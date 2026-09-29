-- Prove2me | solution 1 for syracuse_reaches_one_below_55121
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T05:56:23.430987+00:00
-- url     : https://prove2.me/submissions/6c7307c0-399b-4019-8a63-3a47e9bebe70

import Mathlib
import Definitions.Def_syracuseStep
import Theorems.Thm_syracuse_reaches_one_below_51120

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
theorem B (n : ℕ) (h1 : 0 < n) (h2 : Odd n) (h3 : n ≤ 51119) : Reach n :=
  syracuse_reaches_one_below_51120 n h1 h2 h3
theorem R98309 : Reach 98309 := rs (se 4 (by rfl) ⟨9216, by rfl⟩) (B 18433 (by norm_num) ⟨9216, by rfl⟩ (by norm_num))
theorem R65549 : Reach 65549 := rs (se 3 (by rfl) ⟨12290, by rfl⟩) (B 24581 (by norm_num) ⟨12290, by rfl⟩ (by norm_num))
theorem R65605 : Reach 65605 := rs (se 4 (by rfl) ⟨6150, by rfl⟩) (B 12301 (by norm_num) ⟨6150, by rfl⟩ (by norm_num))
theorem R262277 : Reach 262277 := rs (se 4 (by rfl) ⟨24588, by rfl⟩) (B 49177 (by norm_num) ⟨24588, by rfl⟩ (by norm_num))
theorem R65701 : Reach 65701 := rs (se 4 (by rfl) ⟨6159, by rfl⟩) (B 12319 (by norm_num) ⟨6159, by rfl⟩ (by norm_num))
theorem R65777 : Reach 65777 := rs (se 2 (by rfl) ⟨24666, by rfl⟩) (B 49333 (by norm_num) ⟨24666, by rfl⟩ (by norm_num))
theorem R131341 : Reach 131341 := rs (se 3 (by rfl) ⟨24626, by rfl⟩) (B 49253 (by norm_num) ⟨24626, by rfl⟩ (by norm_num))
theorem R98597 : Reach 98597 := rs (se 4 (by rfl) ⟨9243, by rfl⟩) (B 18487 (by norm_num) ⟨9243, by rfl⟩ (by norm_num))
theorem R327989 : Reach 327989 := rs (se 5 (by rfl) ⟨15374, by rfl⟩) (B 30749 (by norm_num) ⟨15374, by rfl⟩ (by norm_num))
theorem R65873 : Reach 65873 := rs (se 2 (by rfl) ⟨24702, by rfl⟩) (B 49405 (by norm_num) ⟨24702, by rfl⟩ (by norm_num))
theorem R131453 : Reach 131453 := rs (se 3 (by rfl) ⟨24647, by rfl⟩) (B 49295 (by norm_num) ⟨24647, by rfl⟩ (by norm_num))
theorem R65929 : Reach 65929 := rs (se 2 (by rfl) ⟨24723, by rfl⟩) (B 49447 (by norm_num) ⟨24723, by rfl⟩ (by norm_num))
theorem R98749 : Reach 98749 := rs (se 3 (by rfl) ⟨18515, by rfl⟩) (B 37031 (by norm_num) ⟨18515, by rfl⟩ (by norm_num))
theorem R66025 : Reach 66025 := rs (se 2 (by rfl) ⟨24759, by rfl⟩) (B 49519 (by norm_num) ⟨24759, by rfl⟩ (by norm_num))
theorem R131645 : Reach 131645 := rs (se 3 (by rfl) ⟨24683, by rfl⟩) (B 49367 (by norm_num) ⟨24683, by rfl⟩ (by norm_num))
theorem R66197 : Reach 66197 := rs (se 6 (by rfl) ⟨1551, by rfl⟩) (B 3103 (by norm_num) ⟨1551, by rfl⟩ (by norm_num))
theorem R66253 : Reach 66253 := rs (se 3 (by rfl) ⟨12422, by rfl⟩) (B 24845 (by norm_num) ⟨12422, by rfl⟩ (by norm_num))
theorem R99053 : Reach 99053 := rs (se 3 (by rfl) ⟨18572, by rfl⟩) (B 37145 (by norm_num) ⟨18572, by rfl⟩ (by norm_num))
theorem R66349 : Reach 66349 := rs (se 3 (by rfl) ⟨12440, by rfl⟩) (B 24881 (by norm_num) ⟨12440, by rfl⟩ (by norm_num))
theorem R164693 : Reach 164693 := rs (se 9 (by rfl) ⟨482, by rfl⟩) (B 965 (by norm_num) ⟨482, by rfl⟩ (by norm_num))
theorem R426869 : Reach 426869 := rs (se 5 (by rfl) ⟨20009, by rfl⟩) (B 40019 (by norm_num) ⟨20009, by rfl⟩ (by norm_num))
theorem R131989 : Reach 131989 := rs (se 6 (by rfl) ⟨3093, by rfl⟩) (B 6187 (by norm_num) ⟨3093, by rfl⟩ (by norm_num))
theorem R66521 : Reach 66521 := rs (se 2 (by rfl) ⟨24945, by rfl⟩) (B 49891 (by norm_num) ⟨24945, by rfl⟩ (by norm_num))
theorem R132101 : Reach 132101 := rs (se 4 (by rfl) ⟨12384, by rfl⟩) (B 24769 (by norm_num) ⟨12384, by rfl⟩ (by norm_num))
theorem R66577 : Reach 66577 := rs (se 2 (by rfl) ⟨24966, by rfl⟩) (B 49933 (by norm_num) ⟨24966, by rfl⟩ (by norm_num))
theorem R99389 : Reach 99389 := rs (se 3 (by rfl) ⟨18635, by rfl⟩) (B 37271 (by norm_num) ⟨18635, by rfl⟩ (by norm_num))
theorem R66673 : Reach 66673 := rs (se 2 (by rfl) ⟨25002, by rfl⟩) (B 50005 (by norm_num) ⟨25002, by rfl⟩ (by norm_num))
theorem R132293 : Reach 132293 := rs (se 4 (by rfl) ⟨12402, by rfl⟩) (B 24805 (by norm_num) ⟨12402, by rfl⟩ (by norm_num))
theorem R165125 : Reach 165125 := rs (se 4 (by rfl) ⟨15480, by rfl⟩) (B 30961 (by norm_num) ⟨15480, by rfl⟩ (by norm_num))
theorem R197909 : Reach 197909 := rs (se 6 (by rfl) ⟨4638, by rfl⟩) (B 9277 (by norm_num) ⟨4638, by rfl⟩ (by norm_num))
theorem R66845 : Reach 66845 := rs (se 3 (by rfl) ⟨12533, by rfl⟩) (B 25067 (by norm_num) ⟨12533, by rfl⟩ (by norm_num))
theorem R66901 : Reach 66901 := rs (se 12 (by rfl) ⟨24, by rfl⟩) (B 49 (by norm_num) ⟨24, by rfl⟩ (by norm_num))
theorem R263573 : Reach 263573 := rs (se 6 (by rfl) ⟨6177, by rfl⟩) (B 12355 (by norm_num) ⟨6177, by rfl⟩ (by norm_num))
theorem R66997 : Reach 66997 := rs (se 5 (by rfl) ⟨3140, by rfl⟩) (B 6281 (by norm_num) ⟨3140, by rfl⟩ (by norm_num))
theorem R99805 : Reach 99805 := rs (se 3 (by rfl) ⟨18713, by rfl⟩) (B 37427 (by norm_num) ⟨18713, by rfl⟩ (by norm_num))
theorem R132637 : Reach 132637 := rs (se 3 (by rfl) ⟨24869, by rfl⟩) (B 49739 (by norm_num) ⟨24869, by rfl⟩ (by norm_num))
theorem R198197 : Reach 198197 := rs (se 5 (by rfl) ⟨9290, by rfl⟩) (B 18581 (by norm_num) ⟨9290, by rfl⟩ (by norm_num))
theorem R67169 : Reach 67169 := rs (se 2 (by rfl) ⟨25188, by rfl⟩) (B 50377 (by norm_num) ⟨25188, by rfl⟩ (by norm_num))
theorem R99949 : Reach 99949 := rs (se 3 (by rfl) ⟨18740, by rfl⟩) (B 37481 (by norm_num) ⟨18740, by rfl⟩ (by norm_num))
theorem R132749 : Reach 132749 := rs (se 3 (by rfl) ⟨24890, by rfl⟩) (B 49781 (by norm_num) ⟨24890, by rfl⟩ (by norm_num))
theorem R67225 : Reach 67225 := rs (se 2 (by rfl) ⟨25209, by rfl⟩) (B 50419 (by norm_num) ⟨25209, by rfl⟩ (by norm_num))
theorem R362165 : Reach 362165 := rs (se 5 (by rfl) ⟨16976, by rfl⟩) (B 33953 (by norm_num) ⟨16976, by rfl⟩ (by norm_num))
theorem R67321 : Reach 67321 := rs (se 2 (by rfl) ⟨25245, by rfl⟩) (B 50491 (by norm_num) ⟨25245, by rfl⟩ (by norm_num))
theorem R100109 : Reach 100109 := rs (se 3 (by rfl) ⟨18770, by rfl⟩) (B 37541 (by norm_num) ⟨18770, by rfl⟩ (by norm_num))
theorem R132941 : Reach 132941 := rs (se 3 (by rfl) ⟨24926, by rfl⟩) (B 49853 (by norm_num) ⟨24926, by rfl⟩ (by norm_num))
theorem R132949 : Reach 132949 := rs (se 9 (by rfl) ⟨389, by rfl⟩) (B 779 (by norm_num) ⟨389, by rfl⟩ (by norm_num))
theorem R100253 : Reach 100253 := rs (se 3 (by rfl) ⟨18797, by rfl⟩) (B 37595 (by norm_num) ⟨18797, by rfl⟩ (by norm_num))
theorem R67493 : Reach 67493 := rs (se 4 (by rfl) ⟨6327, by rfl⟩) (B 12655 (by norm_num) ⟨6327, by rfl⟩ (by norm_num))
theorem R296885 : Reach 296885 := rs (se 5 (by rfl) ⟨13916, by rfl⟩) (B 27833 (by norm_num) ⟨13916, by rfl⟩ (by norm_num))
theorem R755669 : Reach 755669 := rs (se 7 (by rfl) ⟨8855, by rfl⟩) (B 17711 (by norm_num) ⟨8855, by rfl⟩ (by norm_num))
theorem R67549 : Reach 67549 := rs (se 3 (by rfl) ⟨12665, by rfl⟩) (B 25331 (by norm_num) ⟨12665, by rfl⟩ (by norm_num))
theorem R67573 : Reach 67573 := rs (se 5 (by rfl) ⟨3167, by rfl⟩) (B 6335 (by norm_num) ⟨3167, by rfl⟩ (by norm_num))
theorem R67645 : Reach 67645 := rs (se 3 (by rfl) ⟨12683, by rfl⟩) (B 25367 (by norm_num) ⟨12683, by rfl⟩ (by norm_num))
theorem R133285 : Reach 133285 := rs (se 4 (by rfl) ⟨12495, by rfl⟩) (B 24991 (by norm_num) ⟨12495, by rfl⟩ (by norm_num))
theorem R100541 : Reach 100541 := rs (se 3 (by rfl) ⟨18851, by rfl⟩) (B 37703 (by norm_num) ⟨18851, by rfl⟩ (by norm_num))
theorem R67817 : Reach 67817 := rs (se 2 (by rfl) ⟨25431, by rfl⟩) (B 50863 (by norm_num) ⟨25431, by rfl⟩ (by norm_num))
theorem R133397 : Reach 133397 := rs (se 6 (by rfl) ⟨3126, by rfl⟩) (B 6253 (by norm_num) ⟨3126, by rfl⟩ (by norm_num))
theorem R67873 : Reach 67873 := rs (se 2 (by rfl) ⟨25452, by rfl⟩) (B 50905 (by norm_num) ⟨25452, by rfl⟩ (by norm_num))
theorem R100693 : Reach 100693 := rs (se 10 (by rfl) ⟨147, by rfl⟩) (B 295 (by norm_num) ⟨147, by rfl⟩ (by norm_num))
theorem R330101 : Reach 330101 := rs (se 5 (by rfl) ⟨15473, by rfl⟩) (B 30947 (by norm_num) ⟨15473, by rfl⟩ (by norm_num))
theorem R67969 : Reach 67969 := rs (se 2 (by rfl) ⟨25488, by rfl⟩) (B 50977 (by norm_num) ⟨25488, by rfl⟩ (by norm_num))
theorem R133589 : Reach 133589 := rs (se 7 (by rfl) ⟨1565, by rfl⟩) (B 3131 (by norm_num) ⟨1565, by rfl⟩ (by norm_num))
theorem R68117 : Reach 68117 := rs (se 6 (by rfl) ⟨1596, by rfl⟩) (B 3193 (by norm_num) ⟨1596, by rfl⟩ (by norm_num))
theorem R68141 : Reach 68141 := rs (se 3 (by rfl) ⟨12776, by rfl⟩) (B 25553 (by norm_num) ⟨12776, by rfl⟩ (by norm_num))
theorem R68197 : Reach 68197 := rs (se 4 (by rfl) ⟨6393, by rfl⟩) (B 12787 (by norm_num) ⟨6393, by rfl⟩ (by norm_num))
theorem R133741 : Reach 133741 := rs (se 3 (by rfl) ⟨25076, by rfl⟩) (B 50153 (by norm_num) ⟨25076, by rfl⟩ (by norm_num))
theorem R100997 : Reach 100997 := rs (se 4 (by rfl) ⟨9468, by rfl⟩) (B 18937 (by norm_num) ⟨9468, by rfl⟩ (by norm_num))
theorem R264869 : Reach 264869 := rs (se 4 (by rfl) ⟨24831, by rfl⟩) (B 49663 (by norm_num) ⟨24831, by rfl⟩ (by norm_num))
theorem R68293 : Reach 68293 := rs (se 4 (by rfl) ⟨6402, by rfl⟩) (B 12805 (by norm_num) ⟨6402, by rfl⟩ (by norm_num))
theorem R199381 : Reach 199381 := rs (se 7 (by rfl) ⟨2336, by rfl⟩) (B 4673 (by norm_num) ⟨2336, by rfl⟩ (by norm_num))
theorem R133933 : Reach 133933 := rs (se 3 (by rfl) ⟨25112, by rfl⟩) (B 50225 (by norm_num) ⟨25112, by rfl⟩ (by norm_num))
theorem R134045 : Reach 134045 := rs (se 3 (by rfl) ⟨25133, by rfl⟩) (B 50267 (by norm_num) ⟨25133, by rfl⟩ (by norm_num))
theorem R199685 : Reach 199685 := rs (se 4 (by rfl) ⟨18720, by rfl⟩) (B 37441 (by norm_num) ⟨18720, by rfl⟩ (by norm_num))
theorem R68677 : Reach 68677 := rs (se 4 (by rfl) ⟨6438, by rfl⟩) (B 12877 (by norm_num) ⟨6438, by rfl⟩ (by norm_num))
theorem R134237 : Reach 134237 := rs (se 3 (by rfl) ⟨25169, by rfl⟩) (B 50339 (by norm_num) ⟨25169, by rfl⟩ (by norm_num))
theorem R68789 : Reach 68789 := rs (se 5 (by rfl) ⟨3224, by rfl⟩) (B 6449 (by norm_num) ⟨3224, by rfl⟩ (by norm_num))
theorem R68845 : Reach 68845 := rs (se 3 (by rfl) ⟨12908, by rfl⟩) (B 25817 (by norm_num) ⟨12908, by rfl⟩ (by norm_num))
theorem R68941 : Reach 68941 := rs (se 3 (by rfl) ⟨12926, by rfl⟩) (B 25853 (by norm_num) ⟨12926, by rfl⟩ (by norm_num))
theorem R101749 : Reach 101749 := rs (se 5 (by rfl) ⟨4769, by rfl⟩) (B 9539 (by norm_num) ⟨4769, by rfl⟩ (by norm_num))
theorem R134581 : Reach 134581 := rs (se 5 (by rfl) ⟨6308, by rfl⟩) (B 12617 (by norm_num) ⟨6308, by rfl⟩ (by norm_num))
theorem R232901 : Reach 232901 := rs (se 4 (by rfl) ⟨21834, by rfl⟩) (B 43669 (by norm_num) ⟨21834, by rfl⟩ (by norm_num))
theorem R101893 : Reach 101893 := rs (se 4 (by rfl) ⟨9552, by rfl⟩) (B 19105 (by norm_num) ⟨9552, by rfl⟩ (by norm_num))
theorem R134693 : Reach 134693 := rs (se 4 (by rfl) ⟨12627, by rfl⟩) (B 25255 (by norm_num) ⟨12627, by rfl⟩ (by norm_num))
theorem R102053 : Reach 102053 := rs (se 4 (by rfl) ⟨9567, by rfl⟩) (B 19135 (by norm_num) ⟨9567, by rfl⟩ (by norm_num))
theorem R134885 : Reach 134885 := rs (se 4 (by rfl) ⟨12645, by rfl⟩) (B 25291 (by norm_num) ⟨12645, by rfl⟩ (by norm_num))
theorem R233189 : Reach 233189 := rs (se 4 (by rfl) ⟨21861, by rfl⟩) (B 43723 (by norm_num) ⟨21861, by rfl⟩ (by norm_num))
theorem R102197 : Reach 102197 := rs (se 5 (by rfl) ⟨4790, by rfl⟩) (B 9581 (by norm_num) ⟨4790, by rfl⟩ (by norm_num))
theorem R69437 : Reach 69437 := rs (se 3 (by rfl) ⟨13019, by rfl⟩) (B 26039 (by norm_num) ⟨13019, by rfl⟩ (by norm_num))
theorem R69493 : Reach 69493 := rs (se 5 (by rfl) ⟨3257, by rfl⟩) (B 6515 (by norm_num) ⟨3257, by rfl⟩ (by norm_num))
theorem R167845 : Reach 167845 := rs (se 4 (by rfl) ⟨15735, by rfl⟩) (B 31471 (by norm_num) ⟨15735, by rfl⟩ (by norm_num))
theorem R266165 : Reach 266165 := rs (se 5 (by rfl) ⟨12476, by rfl⟩) (B 24953 (by norm_num) ⟨12476, by rfl⟩ (by norm_num))
theorem R69589 : Reach 69589 := rs (se 7 (by rfl) ⟨815, by rfl⟩) (B 1631 (by norm_num) ⟨815, by rfl⟩ (by norm_num))
theorem R135229 : Reach 135229 := rs (se 3 (by rfl) ⟨25355, by rfl⟩) (B 50711 (by norm_num) ⟨25355, by rfl⟩ (by norm_num))
theorem R102485 : Reach 102485 := rs (se 8 (by rfl) ⟨600, by rfl⟩) (B 1201 (by norm_num) ⟨600, by rfl⟩ (by norm_num))
theorem R135341 : Reach 135341 := rs (se 3 (by rfl) ⟨25376, by rfl⟩) (B 50753 (by norm_num) ⟨25376, by rfl⟩ (by norm_num))
theorem R69869 : Reach 69869 := rs (se 3 (by rfl) ⟨13100, by rfl⟩) (B 26201 (by norm_num) ⟨13100, by rfl⟩ (by norm_num))
theorem R102637 : Reach 102637 := rs (se 3 (by rfl) ⟨19244, by rfl⟩) (B 38489 (by norm_num) ⟨19244, by rfl⟩ (by norm_num))
theorem R69925 : Reach 69925 := rs (se 4 (by rfl) ⟨6555, by rfl⟩) (B 13111 (by norm_num) ⟨6555, by rfl⟩ (by norm_num))
theorem R168293 : Reach 168293 := rs (se 4 (by rfl) ⟨15777, by rfl⟩) (B 31555 (by norm_num) ⟨15777, by rfl⟩ (by norm_num))
theorem R135533 : Reach 135533 := rs (se 3 (by rfl) ⟨25412, by rfl⟩) (B 50825 (by norm_num) ⟨25412, by rfl⟩ (by norm_num))
theorem R233941 : Reach 233941 := rs (se 7 (by rfl) ⟨2741, by rfl⟩) (B 5483 (by norm_num) ⟨2741, by rfl⟩ (by norm_num))
theorem R102941 : Reach 102941 := rs (se 3 (by rfl) ⟨19301, by rfl⟩) (B 38603 (by norm_num) ⟨19301, by rfl⟩ (by norm_num))
theorem R70189 : Reach 70189 := rs (se 3 (by rfl) ⟨13160, by rfl⟩) (B 26321 (by norm_num) ⟨13160, by rfl⟩ (by norm_num))
theorem R168533 : Reach 168533 := rs (se 8 (by rfl) ⟨987, by rfl⟩) (B 1975 (by norm_num) ⟨987, by rfl⟩ (by norm_num))
theorem R135877 : Reach 135877 := rs (se 4 (by rfl) ⟨12738, by rfl⟩) (B 25477 (by norm_num) ⟨12738, by rfl⟩ (by norm_num))
theorem R135989 : Reach 135989 := rs (se 5 (by rfl) ⟨6374, by rfl⟩) (B 12749 (by norm_num) ⟨6374, by rfl⟩ (by norm_num))
theorem R136181 : Reach 136181 := rs (se 5 (by rfl) ⟨6383, by rfl⟩) (B 12767 (by norm_num) ⟨6383, by rfl⟩ (by norm_num))
theorem R201797 : Reach 201797 := rs (se 4 (by rfl) ⟨18918, by rfl⟩) (B 37837 (by norm_num) ⟨18918, by rfl⟩ (by norm_num))
theorem R234677 : Reach 234677 := rs (se 5 (by rfl) ⟨11000, by rfl⟩) (B 22001 (by norm_num) ⟨11000, by rfl⟩ (by norm_num))
theorem R267461 : Reach 267461 := rs (se 4 (by rfl) ⟨25074, by rfl⟩) (B 50149 (by norm_num) ⟨25074, by rfl⟩ (by norm_num))
theorem R103693 : Reach 103693 := rs (se 3 (by rfl) ⟨19442, by rfl⟩) (B 38885 (by norm_num) ⟨19442, by rfl⟩ (by norm_num))
theorem R202085 : Reach 202085 := rs (se 4 (by rfl) ⟨18945, by rfl⟩) (B 37891 (by norm_num) ⟨18945, by rfl⟩ (by norm_num))
theorem R71069 : Reach 71069 := rs (se 3 (by rfl) ⟨13325, by rfl⟩) (B 26651 (by norm_num) ⟨13325, by rfl⟩ (by norm_num))
theorem R103837 : Reach 103837 := rs (se 3 (by rfl) ⟨19469, by rfl⟩) (B 38939 (by norm_num) ⟨19469, by rfl⟩ (by norm_num))
theorem R103997 : Reach 103997 := rs (se 3 (by rfl) ⟨19499, by rfl⟩) (B 38999 (by norm_num) ⟨19499, by rfl⟩ (by norm_num))
theorem R104141 : Reach 104141 := rs (se 3 (by rfl) ⟨19526, by rfl⟩) (B 39053 (by norm_num) ⟨19526, by rfl⟩ (by norm_num))
theorem R137173 : Reach 137173 := rs (se 7 (by rfl) ⟨1607, by rfl⟩) (B 3215 (by norm_num) ⟨1607, by rfl⟩ (by norm_num))
theorem R104429 : Reach 104429 := rs (se 3 (by rfl) ⟨19580, by rfl⟩) (B 39161 (by norm_num) ⟨19580, by rfl⟩ (by norm_num))
theorem R137285 : Reach 137285 := rs (se 4 (by rfl) ⟨12870, by rfl⟩) (B 25741 (by norm_num) ⟨12870, by rfl⟩ (by norm_num))
theorem R104581 : Reach 104581 := rs (se 4 (by rfl) ⟨9804, by rfl⟩) (B 19609 (by norm_num) ⟨9804, by rfl⟩ (by norm_num))
theorem R137477 : Reach 137477 := rs (se 4 (by rfl) ⟨12888, by rfl⟩) (B 25777 (by norm_num) ⟨12888, by rfl⟩ (by norm_num))
theorem R104789 : Reach 104789 := rs (se 10 (by rfl) ⟨153, by rfl⟩) (B 307 (by norm_num) ⟨153, by rfl⟩ (by norm_num))
theorem R268757 : Reach 268757 := rs (se 7 (by rfl) ⟨3149, by rfl⟩) (B 6299 (by norm_num) ⟨3149, by rfl⟩ (by norm_num))
theorem R203269 : Reach 203269 := rs (se 4 (by rfl) ⟨19056, by rfl⟩) (B 38113 (by norm_num) ⟨19056, by rfl⟩ (by norm_num))
theorem R170677 : Reach 170677 := rs (se 5 (by rfl) ⟨8000, by rfl⟩) (B 16001 (by norm_num) ⟨8000, by rfl⟩ (by norm_num))
theorem R170741 : Reach 170741 := rs (se 5 (by rfl) ⟨8003, by rfl⟩) (B 16007 (by norm_num) ⟨8003, by rfl⟩ (by norm_num))
theorem R203573 : Reach 203573 := rs (se 5 (by rfl) ⟨9542, by rfl⟩) (B 19085 (by norm_num) ⟨9542, by rfl⟩ (by norm_num))
theorem R105301 : Reach 105301 := rs (se 9 (by rfl) ⟨308, by rfl⟩) (B 617 (by norm_num) ⟨308, by rfl⟩ (by norm_num))
theorem R105421 : Reach 105421 := rs (se 3 (by rfl) ⟨19766, by rfl⟩) (B 39533 (by norm_num) ⟨19766, by rfl⟩ (by norm_num))
theorem R138469 : Reach 138469 := rs (se 4 (by rfl) ⟨12981, by rfl⟩) (B 25963 (by norm_num) ⟨12981, by rfl⟩ (by norm_num))
theorem R236789 : Reach 236789 := rs (se 5 (by rfl) ⟨11099, by rfl⟩) (B 22199 (by norm_num) ⟨11099, by rfl⟩ (by norm_num))
theorem R138581 : Reach 138581 := rs (se 11 (by rfl) ⟨101, by rfl⟩) (B 203 (by norm_num) ⟨101, by rfl⟩ (by norm_num))
theorem R138773 : Reach 138773 := rs (se 6 (by rfl) ⟨3252, by rfl⟩) (B 6505 (by norm_num) ⟨3252, by rfl⟩ (by norm_num))
theorem R400949 : Reach 400949 := rs (se 5 (by rfl) ⟨18794, by rfl⟩) (B 37589 (by norm_num) ⟨18794, by rfl⟩ (by norm_num))
theorem R73333 : Reach 73333 := rs (se 5 (by rfl) ⟨3437, by rfl⟩) (B 6875 (by norm_num) ⟨3437, by rfl⟩ (by norm_num))
theorem R270053 : Reach 270053 := rs (se 4 (by rfl) ⟨25317, by rfl⟩) (B 50635 (by norm_num) ⟨25317, by rfl⟩ (by norm_num))
theorem R237413 : Reach 237413 := rs (se 4 (by rfl) ⟨22257, by rfl⟩) (B 44515 (by norm_num) ⟨22257, by rfl⟩ (by norm_num))
theorem R434069 : Reach 434069 := rs (se 6 (by rfl) ⟨10173, by rfl⟩) (B 20347 (by norm_num) ⟨10173, by rfl⟩ (by norm_num))
theorem R73837 : Reach 73837 := rs (se 3 (by rfl) ⟨13844, by rfl⟩) (B 27689 (by norm_num) ⟨13844, by rfl⟩ (by norm_num))
theorem R74125 : Reach 74125 := rs (se 3 (by rfl) ⟨13898, by rfl⟩) (B 27797 (by norm_num) ⟨13898, by rfl⟩ (by norm_num))
theorem R139909 : Reach 139909 := rs (se 4 (by rfl) ⟨13116, by rfl⟩) (B 26233 (by norm_num) ⟨13116, by rfl⟩ (by norm_num))
theorem R74461 : Reach 74461 := rs (se 3 (by rfl) ⟨13961, by rfl⟩) (B 27923 (by norm_num) ⟨13961, by rfl⟩ (by norm_num))
theorem R107237 : Reach 107237 := rs (se 4 (by rfl) ⟨10053, by rfl⟩) (B 20107 (by norm_num) ⟨10053, by rfl⟩ (by norm_num))
theorem R172853 : Reach 172853 := rs (se 5 (by rfl) ⟨8102, by rfl⟩) (B 16205 (by norm_num) ⟨8102, by rfl⟩ (by norm_num))
theorem R205685 : Reach 205685 := rs (se 5 (by rfl) ⟨9641, by rfl⟩) (B 19283 (by norm_num) ⟨9641, by rfl⟩ (by norm_num))
theorem R74677 : Reach 74677 := rs (se 5 (by rfl) ⟨3500, by rfl⟩) (B 7001 (by norm_num) ⟨3500, by rfl⟩ (by norm_num))
theorem R271349 : Reach 271349 := rs (se 5 (by rfl) ⟨12719, by rfl⟩) (B 25439 (by norm_num) ⟨12719, by rfl⟩ (by norm_num))
theorem R205861 : Reach 205861 := rs (se 4 (by rfl) ⟨19299, by rfl⟩) (B 38599 (by norm_num) ⟨19299, by rfl⟩ (by norm_num))
theorem R205973 : Reach 205973 := rs (se 6 (by rfl) ⟨4827, by rfl⟩) (B 9655 (by norm_num) ⟨4827, by rfl⟩ (by norm_num))
theorem R173285 : Reach 173285 := rs (se 4 (by rfl) ⟨16245, by rfl⟩) (B 32491 (by norm_num) ⟨16245, by rfl⟩ (by norm_num))
theorem R533749 : Reach 533749 := rs (se 5 (by rfl) ⟨25019, by rfl⟩) (B 50039 (by norm_num) ⟨25019, by rfl⟩ (by norm_num))
theorem R140549 : Reach 140549 := rs (se 4 (by rfl) ⟨13176, by rfl⟩) (B 26353 (by norm_num) ⟨13176, by rfl⟩ (by norm_num))
theorem R75053 : Reach 75053 := rs (se 3 (by rfl) ⟨14072, by rfl⟩) (B 28145 (by norm_num) ⟨14072, by rfl⟩ (by norm_num))
theorem R599381 : Reach 599381 := rs (se 12 (by rfl) ⟨219, by rfl⟩) (B 439 (by norm_num) ⟨219, by rfl⟩ (by norm_num))
theorem R2041301 : Reach 2041301 := rs (se 7 (by rfl) ⟨23921, by rfl⟩) (B 47843 (by norm_num) ⟨23921, by rfl⟩ (by norm_num))
theorem R173717 : Reach 173717 := rs (se 6 (by rfl) ⟨4071, by rfl⟩) (B 8143 (by norm_num) ⟨4071, by rfl⟩ (by norm_num))
theorem R173765 : Reach 173765 := rs (se 4 (by rfl) ⟨16290, by rfl⟩) (B 32581 (by norm_num) ⟨16290, by rfl⟩ (by norm_num))
theorem R108373 : Reach 108373 := rs (se 9 (by rfl) ⟨317, by rfl⟩) (B 635 (by norm_num) ⟨317, by rfl⟩ (by norm_num))
theorem R108445 : Reach 108445 := rs (se 3 (by rfl) ⟨20333, by rfl⟩) (B 40667 (by norm_num) ⟨20333, by rfl⟩ (by norm_num))
theorem R108469 : Reach 108469 := rs (se 5 (by rfl) ⟨5084, by rfl⟩) (B 10169 (by norm_num) ⟨5084, by rfl⟩ (by norm_num))
theorem R567253 : Reach 567253 := rs (se 7 (by rfl) ⟨6647, by rfl⟩) (B 13295 (by norm_num) ⟨6647, by rfl⟩ (by norm_num))
theorem R174149 : Reach 174149 := rs (se 4 (by rfl) ⟨16326, by rfl⟩) (B 32653 (by norm_num) ⟨16326, by rfl⟩ (by norm_num))
theorem R207157 : Reach 207157 := rs (se 5 (by rfl) ⟨9710, by rfl⟩) (B 19421 (by norm_num) ⟨9710, by rfl⟩ (by norm_num))
theorem R665941 : Reach 665941 := rs (se 10 (by rfl) ⟨975, by rfl⟩) (B 1951 (by norm_num) ⟨975, by rfl⟩ (by norm_num))
theorem R174581 : Reach 174581 := rs (se 5 (by rfl) ⟨8183, by rfl⟩) (B 16367 (by norm_num) ⟨8183, by rfl⟩ (by norm_num))
theorem R207461 : Reach 207461 := rs (se 4 (by rfl) ⟨19449, by rfl⟩) (B 38899 (by norm_num) ⟨19449, by rfl⟩ (by norm_num))
theorem R436853 : Reach 436853 := rs (se 5 (by rfl) ⟨20477, by rfl⟩) (B 40955 (by norm_num) ⟨20477, by rfl⟩ (by norm_num))
theorem R76477 : Reach 76477 := rs (se 3 (by rfl) ⟨14339, by rfl⟩) (B 28679 (by norm_num) ⟨14339, by rfl⟩ (by norm_num))
theorem R76685 : Reach 76685 := rs (se 3 (by rfl) ⟨14378, by rfl⟩) (B 28757 (by norm_num) ⟨14378, by rfl⟩ (by norm_num))
theorem R109453 : Reach 109453 := rs (se 3 (by rfl) ⟨20522, by rfl⟩) (B 41045 (by norm_num) ⟨20522, by rfl⟩ (by norm_num))
theorem R76709 : Reach 76709 := rs (se 4 (by rfl) ⟨7191, by rfl⟩) (B 14383 (by norm_num) ⟨7191, by rfl⟩ (by norm_num))
theorem R175013 : Reach 175013 := rs (se 4 (by rfl) ⟨16407, by rfl⟩) (B 32815 (by norm_num) ⟨16407, by rfl⟩ (by norm_num))
theorem R76733 : Reach 76733 := rs (se 3 (by rfl) ⟨14387, by rfl⟩) (B 28775 (by norm_num) ⟨14387, by rfl⟩ (by norm_num))
theorem R76757 : Reach 76757 := rs (se 7 (by rfl) ⟨899, by rfl⟩) (B 1799 (by norm_num) ⟨899, by rfl⟩ (by norm_num))
theorem R76781 : Reach 76781 := rs (se 3 (by rfl) ⟨14396, by rfl⟩) (B 28793 (by norm_num) ⟨14396, by rfl⟩ (by norm_num))
theorem R76805 : Reach 76805 := rs (se 4 (by rfl) ⟨7200, by rfl⟩) (B 14401 (by norm_num) ⟨7200, by rfl⟩ (by norm_num))
theorem R76829 : Reach 76829 := rs (se 3 (by rfl) ⟨14405, by rfl⟩) (B 28811 (by norm_num) ⟨14405, by rfl⟩ (by norm_num))
theorem R76853 : Reach 76853 := rs (se 5 (by rfl) ⟨3602, by rfl⟩) (B 7205 (by norm_num) ⟨3602, by rfl⟩ (by norm_num))
theorem R470069 : Reach 470069 := rs (se 5 (by rfl) ⟨22034, by rfl⟩) (B 44069 (by norm_num) ⟨22034, by rfl⟩ (by norm_num))
theorem R76877 : Reach 76877 := rs (se 3 (by rfl) ⟨14414, by rfl⟩) (B 28829 (by norm_num) ⟨14414, by rfl⟩ (by norm_num))
theorem R76901 : Reach 76901 := rs (se 4 (by rfl) ⟨7209, by rfl⟩) (B 14419 (by norm_num) ⟨7209, by rfl⟩ (by norm_num))
theorem R76925 : Reach 76925 := rs (se 3 (by rfl) ⟨14423, by rfl⟩) (B 28847 (by norm_num) ⟨14423, by rfl⟩ (by norm_num))
theorem R76949 : Reach 76949 := rs (se 6 (by rfl) ⟨1803, by rfl⟩) (B 3607 (by norm_num) ⟨1803, by rfl⟩ (by norm_num))
theorem R76973 : Reach 76973 := rs (se 3 (by rfl) ⟨14432, by rfl⟩) (B 28865 (by norm_num) ⟨14432, by rfl⟩ (by norm_num))
theorem R76997 : Reach 76997 := rs (se 4 (by rfl) ⟨7218, by rfl⟩) (B 14437 (by norm_num) ⟨7218, by rfl⟩ (by norm_num))
theorem R77021 : Reach 77021 := rs (se 3 (by rfl) ⟨14441, by rfl⟩) (B 28883 (by norm_num) ⟨14441, by rfl⟩ (by norm_num))
theorem R77045 : Reach 77045 := rs (se 5 (by rfl) ⟨3611, by rfl⟩) (B 7223 (by norm_num) ⟨3611, by rfl⟩ (by norm_num))
theorem R109829 : Reach 109829 := rs (se 4 (by rfl) ⟨10296, by rfl⟩) (B 20593 (by norm_num) ⟨10296, by rfl⟩ (by norm_num))
theorem R77069 : Reach 77069 := rs (se 3 (by rfl) ⟨14450, by rfl⟩) (B 28901 (by norm_num) ⟨14450, by rfl⟩ (by norm_num))
theorem R77093 : Reach 77093 := rs (se 4 (by rfl) ⟨7227, by rfl⟩) (B 14455 (by norm_num) ⟨7227, by rfl⟩ (by norm_num))
theorem R77117 : Reach 77117 := rs (se 3 (by rfl) ⟨14459, by rfl⟩) (B 28919 (by norm_num) ⟨14459, by rfl⟩ (by norm_num))
theorem R77141 : Reach 77141 := rs (se 11 (by rfl) ⟨56, by rfl⟩) (B 113 (by norm_num) ⟨56, by rfl⟩ (by norm_num))
theorem R175445 : Reach 175445 := rs (se 11 (by rfl) ⟨128, by rfl⟩) (B 257 (by norm_num) ⟨128, by rfl⟩ (by norm_num))
theorem R77149 : Reach 77149 := rs (se 3 (by rfl) ⟨14465, by rfl⟩) (B 28931 (by norm_num) ⟨14465, by rfl⟩ (by norm_num))
theorem R77165 : Reach 77165 := rs (se 3 (by rfl) ⟨14468, by rfl⟩) (B 28937 (by norm_num) ⟨14468, by rfl⟩ (by norm_num))
theorem R77189 : Reach 77189 := rs (se 4 (by rfl) ⟨7236, by rfl⟩) (B 14473 (by norm_num) ⟨7236, by rfl⟩ (by norm_num))
theorem R77213 : Reach 77213 := rs (se 3 (by rfl) ⟨14477, by rfl⟩) (B 28955 (by norm_num) ⟨14477, by rfl⟩ (by norm_num))
theorem R77237 : Reach 77237 := rs (se 5 (by rfl) ⟨3620, by rfl⟩) (B 7241 (by norm_num) ⟨3620, by rfl⟩ (by norm_num))
theorem R77261 : Reach 77261 := rs (se 3 (by rfl) ⟨14486, by rfl⟩) (B 28973 (by norm_num) ⟨14486, by rfl⟩ (by norm_num))
theorem R77269 : Reach 77269 := rs (se 7 (by rfl) ⟨905, by rfl⟩) (B 1811 (by norm_num) ⟨905, by rfl⟩ (by norm_num))
theorem R77285 : Reach 77285 := rs (se 4 (by rfl) ⟨7245, by rfl⟩) (B 14491 (by norm_num) ⟨7245, by rfl⟩ (by norm_num))
theorem R77309 : Reach 77309 := rs (se 3 (by rfl) ⟨14495, by rfl⟩) (B 28991 (by norm_num) ⟨14495, by rfl⟩ (by norm_num))
theorem R77333 : Reach 77333 := rs (se 6 (by rfl) ⟨1812, by rfl⟩) (B 3625 (by norm_num) ⟨1812, by rfl⟩ (by norm_num))
theorem R273941 : Reach 273941 := rs (se 6 (by rfl) ⟨6420, by rfl⟩) (B 12841 (by norm_num) ⟨6420, by rfl⟩ (by norm_num))
theorem R77357 : Reach 77357 := rs (se 3 (by rfl) ⟨14504, by rfl⟩) (B 29009 (by norm_num) ⟨14504, by rfl⟩ (by norm_num))
theorem R77365 : Reach 77365 := rs (se 5 (by rfl) ⟨3626, by rfl⟩) (B 7253 (by norm_num) ⟨3626, by rfl⟩ (by norm_num))
theorem R77381 : Reach 77381 := rs (se 4 (by rfl) ⟨7254, by rfl⟩) (B 14509 (by norm_num) ⟨7254, by rfl⟩ (by norm_num))
theorem R306773 : Reach 306773 := rs (se 8 (by rfl) ⟨1797, by rfl⟩) (B 3595 (by norm_num) ⟨1797, by rfl⟩ (by norm_num))
theorem R77405 : Reach 77405 := rs (se 3 (by rfl) ⟨14513, by rfl⟩) (B 29027 (by norm_num) ⟨14513, by rfl⟩ (by norm_num))
theorem R77429 : Reach 77429 := rs (se 5 (by rfl) ⟨3629, by rfl⟩) (B 7259 (by norm_num) ⟨3629, by rfl⟩ (by norm_num))
theorem R77453 : Reach 77453 := rs (se 3 (by rfl) ⟨14522, by rfl⟩) (B 29045 (by norm_num) ⟨14522, by rfl⟩ (by norm_num))
theorem R77477 : Reach 77477 := rs (se 4 (by rfl) ⟨7263, by rfl⟩) (B 14527 (by norm_num) ⟨7263, by rfl⟩ (by norm_num))
theorem R77501 : Reach 77501 := rs (se 3 (by rfl) ⟨14531, by rfl⟩) (B 29063 (by norm_num) ⟨14531, by rfl⟩ (by norm_num))
theorem R77525 : Reach 77525 := rs (se 7 (by rfl) ⟨908, by rfl⟩) (B 1817 (by norm_num) ⟨908, by rfl⟩ (by norm_num))
theorem R77549 : Reach 77549 := rs (se 3 (by rfl) ⟨14540, by rfl⟩) (B 29081 (by norm_num) ⟨14540, by rfl⟩ (by norm_num))
theorem R77573 : Reach 77573 := rs (se 4 (by rfl) ⟨7272, by rfl⟩) (B 14545 (by norm_num) ⟨7272, by rfl⟩ (by norm_num))
theorem R175877 : Reach 175877 := rs (se 4 (by rfl) ⟨16488, by rfl⟩) (B 32977 (by norm_num) ⟨16488, by rfl⟩ (by norm_num))
theorem R77597 : Reach 77597 := rs (se 3 (by rfl) ⟨14549, by rfl⟩) (B 29099 (by norm_num) ⟨14549, by rfl⟩ (by norm_num))
theorem R77621 : Reach 77621 := rs (se 5 (by rfl) ⟨3638, by rfl⟩) (B 7277 (by norm_num) ⟨3638, by rfl⟩ (by norm_num))
theorem R77645 : Reach 77645 := rs (se 3 (by rfl) ⟨14558, by rfl⟩) (B 29117 (by norm_num) ⟨14558, by rfl⟩ (by norm_num))
theorem R110413 : Reach 110413 := rs (se 3 (by rfl) ⟨20702, by rfl⟩) (B 41405 (by norm_num) ⟨20702, by rfl⟩ (by norm_num))
theorem R77669 : Reach 77669 := rs (se 4 (by rfl) ⟨7281, by rfl⟩) (B 14563 (by norm_num) ⟨7281, by rfl⟩ (by norm_num))
theorem R77693 : Reach 77693 := rs (se 3 (by rfl) ⟨14567, by rfl⟩) (B 29135 (by norm_num) ⟨14567, by rfl⟩ (by norm_num))
theorem R77717 : Reach 77717 := rs (se 6 (by rfl) ⟨1821, by rfl⟩) (B 3643 (by norm_num) ⟨1821, by rfl⟩ (by norm_num))
theorem R77741 : Reach 77741 := rs (se 3 (by rfl) ⟨14576, by rfl⟩) (B 29153 (by norm_num) ⟨14576, by rfl⟩ (by norm_num))
theorem R77765 : Reach 77765 := rs (se 4 (by rfl) ⟨7290, by rfl⟩) (B 14581 (by norm_num) ⟨7290, by rfl⟩ (by norm_num))
theorem R143317 : Reach 143317 := rs (se 7 (by rfl) ⟨1679, by rfl⟩) (B 3359 (by norm_num) ⟨1679, by rfl⟩ (by norm_num))
theorem R77789 : Reach 77789 := rs (se 3 (by rfl) ⟨14585, by rfl⟩) (B 29171 (by norm_num) ⟨14585, by rfl⟩ (by norm_num))
theorem R77813 : Reach 77813 := rs (se 5 (by rfl) ⟨3647, by rfl⟩) (B 7295 (by norm_num) ⟨3647, by rfl⟩ (by norm_num))
theorem R77837 : Reach 77837 := rs (se 3 (by rfl) ⟨14594, by rfl⟩) (B 29189 (by norm_num) ⟨14594, by rfl⟩ (by norm_num))
theorem R77861 : Reach 77861 := rs (se 4 (by rfl) ⟨7299, by rfl⟩) (B 14599 (by norm_num) ⟨7299, by rfl⟩ (by norm_num))
theorem R77885 : Reach 77885 := rs (se 3 (by rfl) ⟨14603, by rfl⟩) (B 29207 (by norm_num) ⟨14603, by rfl⟩ (by norm_num))
theorem R77909 : Reach 77909 := rs (se 8 (by rfl) ⟨456, by rfl⟩) (B 913 (by norm_num) ⟨456, by rfl⟩ (by norm_num))
theorem R77933 : Reach 77933 := rs (se 3 (by rfl) ⟨14612, by rfl⟩) (B 29225 (by norm_num) ⟨14612, by rfl⟩ (by norm_num))
theorem R77957 : Reach 77957 := rs (se 4 (by rfl) ⟨7308, by rfl⟩) (B 14617 (by norm_num) ⟨7308, by rfl⟩ (by norm_num))
theorem R77981 : Reach 77981 := rs (se 3 (by rfl) ⟨14621, by rfl⟩) (B 29243 (by norm_num) ⟨14621, by rfl⟩ (by norm_num))
theorem R78005 : Reach 78005 := rs (se 5 (by rfl) ⟨3656, by rfl⟩) (B 7313 (by norm_num) ⟨3656, by rfl⟩ (by norm_num))
theorem R176309 : Reach 176309 := rs (se 5 (by rfl) ⟨8264, by rfl⟩) (B 16529 (by norm_num) ⟨8264, by rfl⟩ (by norm_num))
theorem R78029 : Reach 78029 := rs (se 3 (by rfl) ⟨14630, by rfl⟩) (B 29261 (by norm_num) ⟨14630, by rfl⟩ (by norm_num))
theorem R78053 : Reach 78053 := rs (se 4 (by rfl) ⟨7317, by rfl⟩) (B 14635 (by norm_num) ⟨7317, by rfl⟩ (by norm_num))
theorem R110837 : Reach 110837 := rs (se 5 (by rfl) ⟨5195, by rfl⟩) (B 10391 (by norm_num) ⟨5195, by rfl⟩ (by norm_num))
theorem R78077 : Reach 78077 := rs (se 3 (by rfl) ⟨14639, by rfl⟩) (B 29279 (by norm_num) ⟨14639, by rfl⟩ (by norm_num))
theorem R78101 : Reach 78101 := rs (se 6 (by rfl) ⟨1830, by rfl⟩) (B 3661 (by norm_num) ⟨1830, by rfl⟩ (by norm_num))
theorem R78125 : Reach 78125 := rs (se 3 (by rfl) ⟨14648, by rfl⟩) (B 29297 (by norm_num) ⟨14648, by rfl⟩ (by norm_num))
theorem R78149 : Reach 78149 := rs (se 4 (by rfl) ⟨7326, by rfl⟩) (B 14653 (by norm_num) ⟨7326, by rfl⟩ (by norm_num))
theorem R78173 : Reach 78173 := rs (se 3 (by rfl) ⟨14657, by rfl⟩) (B 29315 (by norm_num) ⟨14657, by rfl⟩ (by norm_num))
theorem R78197 : Reach 78197 := rs (se 5 (by rfl) ⟨3665, by rfl⟩) (B 7331 (by norm_num) ⟨3665, by rfl⟩ (by norm_num))
theorem R78221 : Reach 78221 := rs (se 3 (by rfl) ⟨14666, by rfl⟩) (B 29333 (by norm_num) ⟨14666, by rfl⟩ (by norm_num))
theorem R78245 : Reach 78245 := rs (se 4 (by rfl) ⟨7335, by rfl⟩) (B 14671 (by norm_num) ⟨7335, by rfl⟩ (by norm_num))
theorem R78269 : Reach 78269 := rs (se 3 (by rfl) ⟨14675, by rfl⟩) (B 29351 (by norm_num) ⟨14675, by rfl⟩ (by norm_num))
theorem R78293 : Reach 78293 := rs (se 7 (by rfl) ⟨917, by rfl⟩) (B 1835 (by norm_num) ⟨917, by rfl⟩ (by norm_num))
theorem R78317 : Reach 78317 := rs (se 3 (by rfl) ⟨14684, by rfl⟩) (B 29369 (by norm_num) ⟨14684, by rfl⟩ (by norm_num))
theorem R78341 : Reach 78341 := rs (se 4 (by rfl) ⟨7344, by rfl⟩) (B 14689 (by norm_num) ⟨7344, by rfl⟩ (by norm_num))
theorem R78365 : Reach 78365 := rs (se 3 (by rfl) ⟨14693, by rfl⟩) (B 29387 (by norm_num) ⟨14693, by rfl⟩ (by norm_num))
theorem R78389 : Reach 78389 := rs (se 5 (by rfl) ⟨3674, by rfl⟩) (B 7349 (by norm_num) ⟨3674, by rfl⟩ (by norm_num))
theorem R78413 : Reach 78413 := rs (se 3 (by rfl) ⟨14702, by rfl⟩) (B 29405 (by norm_num) ⟨14702, by rfl⟩ (by norm_num))
theorem R78437 : Reach 78437 := rs (se 4 (by rfl) ⟨7353, by rfl⟩) (B 14707 (by norm_num) ⟨7353, by rfl⟩ (by norm_num))
theorem R176741 : Reach 176741 := rs (se 4 (by rfl) ⟨16569, by rfl⟩) (B 33139 (by norm_num) ⟨16569, by rfl⟩ (by norm_num))
theorem R78461 : Reach 78461 := rs (se 3 (by rfl) ⟨14711, by rfl⟩) (B 29423 (by norm_num) ⟨14711, by rfl⟩ (by norm_num))
theorem R78485 : Reach 78485 := rs (se 6 (by rfl) ⟨1839, by rfl⟩) (B 3679 (by norm_num) ⟨1839, by rfl⟩ (by norm_num))
theorem R78509 : Reach 78509 := rs (se 3 (by rfl) ⟨14720, by rfl⟩) (B 29441 (by norm_num) ⟨14720, by rfl⟩ (by norm_num))
theorem R78533 : Reach 78533 := rs (se 4 (by rfl) ⟨7362, by rfl⟩) (B 14725 (by norm_num) ⟨7362, by rfl⟩ (by norm_num))
theorem R78557 : Reach 78557 := rs (se 3 (by rfl) ⟨14729, by rfl⟩) (B 29459 (by norm_num) ⟨14729, by rfl⟩ (by norm_num))
theorem R78581 : Reach 78581 := rs (se 5 (by rfl) ⟨3683, by rfl⟩) (B 7367 (by norm_num) ⟨3683, by rfl⟩ (by norm_num))
theorem R78605 : Reach 78605 := rs (se 3 (by rfl) ⟨14738, by rfl⟩) (B 29477 (by norm_num) ⟨14738, by rfl⟩ (by norm_num))
theorem R78629 : Reach 78629 := rs (se 4 (by rfl) ⟨7371, by rfl⟩) (B 14743 (by norm_num) ⟨7371, by rfl⟩ (by norm_num))
theorem R111397 : Reach 111397 := rs (se 4 (by rfl) ⟨10443, by rfl⟩) (B 20887 (by norm_num) ⟨10443, by rfl⟩ (by norm_num))
theorem R78653 : Reach 78653 := rs (se 3 (by rfl) ⟨14747, by rfl⟩) (B 29495 (by norm_num) ⟨14747, by rfl⟩ (by norm_num))
theorem R78677 : Reach 78677 := rs (se 9 (by rfl) ⟨230, by rfl⟩) (B 461 (by norm_num) ⟨230, by rfl⟩ (by norm_num))
theorem R111469 : Reach 111469 := rs (se 3 (by rfl) ⟨20900, by rfl⟩) (B 41801 (by norm_num) ⟨20900, by rfl⟩ (by norm_num))
theorem R78701 : Reach 78701 := rs (se 3 (by rfl) ⟨14756, by rfl⟩) (B 29513 (by norm_num) ⟨14756, by rfl⟩ (by norm_num))
theorem R78725 : Reach 78725 := rs (se 4 (by rfl) ⟨7380, by rfl⟩) (B 14761 (by norm_num) ⟨7380, by rfl⟩ (by norm_num))
theorem R78749 : Reach 78749 := rs (se 3 (by rfl) ⟨14765, by rfl⟩) (B 29531 (by norm_num) ⟨14765, by rfl⟩ (by norm_num))
theorem R78773 : Reach 78773 := rs (se 5 (by rfl) ⟨3692, by rfl⟩) (B 7385 (by norm_num) ⟨3692, by rfl⟩ (by norm_num))
theorem R78797 : Reach 78797 := rs (se 3 (by rfl) ⟨14774, by rfl⟩) (B 29549 (by norm_num) ⟨14774, by rfl⟩ (by norm_num))
theorem R78821 : Reach 78821 := rs (se 4 (by rfl) ⟨7389, by rfl⟩) (B 14779 (by norm_num) ⟨7389, by rfl⟩ (by norm_num))
theorem R78845 : Reach 78845 := rs (se 3 (by rfl) ⟨14783, by rfl⟩) (B 29567 (by norm_num) ⟨14783, by rfl⟩ (by norm_num))
theorem R177173 : Reach 177173 := rs (se 6 (by rfl) ⟨4152, by rfl⟩) (B 8305 (by norm_num) ⟨4152, by rfl⟩ (by norm_num))
theorem R78869 : Reach 78869 := rs (se 6 (by rfl) ⟨1848, by rfl⟩) (B 3697 (by norm_num) ⟨1848, by rfl⟩ (by norm_num))
theorem R78893 : Reach 78893 := rs (se 3 (by rfl) ⟨14792, by rfl⟩) (B 29585 (by norm_num) ⟨14792, by rfl⟩ (by norm_num))
theorem R78917 : Reach 78917 := rs (se 4 (by rfl) ⟨7398, by rfl⟩) (B 14797 (by norm_num) ⟨7398, by rfl⟩ (by norm_num))
theorem R504917 : Reach 504917 := rs (se 8 (by rfl) ⟨2958, by rfl⟩) (B 5917 (by norm_num) ⟨2958, by rfl⟩ (by norm_num))
theorem R78941 : Reach 78941 := rs (se 3 (by rfl) ⟨14801, by rfl⟩) (B 29603 (by norm_num) ⟨14801, by rfl⟩ (by norm_num))
theorem R78965 : Reach 78965 := rs (se 5 (by rfl) ⟨3701, by rfl⟩) (B 7403 (by norm_num) ⟨3701, by rfl⟩ (by norm_num))
theorem R78989 : Reach 78989 := rs (se 3 (by rfl) ⟨14810, by rfl⟩) (B 29621 (by norm_num) ⟨14810, by rfl⟩ (by norm_num))
theorem R79013 : Reach 79013 := rs (se 4 (by rfl) ⟨7407, by rfl⟩) (B 14815 (by norm_num) ⟨7407, by rfl⟩ (by norm_num))
theorem R79037 : Reach 79037 := rs (se 3 (by rfl) ⟨14819, by rfl⟩) (B 29639 (by norm_num) ⟨14819, by rfl⟩ (by norm_num))
theorem R177349 : Reach 177349 := rs (se 4 (by rfl) ⟨16626, by rfl⟩) (B 33253 (by norm_num) ⟨16626, by rfl⟩ (by norm_num))
theorem R79061 : Reach 79061 := rs (se 7 (by rfl) ⟨926, by rfl⟩) (B 1853 (by norm_num) ⟨926, by rfl⟩ (by norm_num))
theorem R79085 : Reach 79085 := rs (se 3 (by rfl) ⟨14828, by rfl⟩) (B 29657 (by norm_num) ⟨14828, by rfl⟩ (by norm_num))
theorem R79109 : Reach 79109 := rs (se 4 (by rfl) ⟨7416, by rfl⟩) (B 14833 (by norm_num) ⟨7416, by rfl⟩ (by norm_num))
theorem R79133 : Reach 79133 := rs (se 3 (by rfl) ⟨14837, by rfl⟩) (B 29675 (by norm_num) ⟨14837, by rfl⟩ (by norm_num))
theorem R79157 : Reach 79157 := rs (se 5 (by rfl) ⟨3710, by rfl⟩) (B 7421 (by norm_num) ⟨3710, by rfl⟩ (by norm_num))
theorem R79181 : Reach 79181 := rs (se 3 (by rfl) ⟨14846, by rfl⟩) (B 29693 (by norm_num) ⟨14846, by rfl⟩ (by norm_num))
theorem R79205 : Reach 79205 := rs (se 4 (by rfl) ⟨7425, by rfl⟩) (B 14851 (by norm_num) ⟨7425, by rfl⟩ (by norm_num))
theorem R79229 : Reach 79229 := rs (se 3 (by rfl) ⟨14855, by rfl⟩) (B 29711 (by norm_num) ⟨14855, by rfl⟩ (by norm_num))
theorem R79253 : Reach 79253 := rs (se 6 (by rfl) ⟨1857, by rfl⟩) (B 3715 (by norm_num) ⟨1857, by rfl⟩ (by norm_num))
theorem R79277 : Reach 79277 := rs (se 3 (by rfl) ⟨14864, by rfl⟩) (B 29729 (by norm_num) ⟨14864, by rfl⟩ (by norm_num))
theorem R144821 : Reach 144821 := rs (se 5 (by rfl) ⟨6788, by rfl⟩) (B 13577 (by norm_num) ⟨6788, by rfl⟩ (by norm_num))
theorem R177605 : Reach 177605 := rs (se 4 (by rfl) ⟨16650, by rfl⟩) (B 33301 (by norm_num) ⟨16650, by rfl⟩ (by norm_num))
theorem R79301 : Reach 79301 := rs (se 4 (by rfl) ⟨7434, by rfl⟩) (B 14869 (by norm_num) ⟨7434, by rfl⟩ (by norm_num))
theorem R79325 : Reach 79325 := rs (se 3 (by rfl) ⟨14873, by rfl⟩) (B 29747 (by norm_num) ⟨14873, by rfl⟩ (by norm_num))
theorem R79349 : Reach 79349 := rs (se 5 (by rfl) ⟨3719, by rfl⟩) (B 7439 (by norm_num) ⟨3719, by rfl⟩ (by norm_num))
theorem R79373 : Reach 79373 := rs (se 3 (by rfl) ⟨14882, by rfl⟩) (B 29765 (by norm_num) ⟨14882, by rfl⟩ (by norm_num))
theorem R439829 : Reach 439829 := rs (se 6 (by rfl) ⟨10308, by rfl⟩) (B 20617 (by norm_num) ⟨10308, by rfl⟩ (by norm_num))
theorem R79397 : Reach 79397 := rs (se 4 (by rfl) ⟨7443, by rfl⟩) (B 14887 (by norm_num) ⟨7443, by rfl⟩ (by norm_num))
theorem R79421 : Reach 79421 := rs (se 3 (by rfl) ⟨14891, by rfl⟩) (B 29783 (by norm_num) ⟨14891, by rfl⟩ (by norm_num))
theorem R79445 : Reach 79445 := rs (se 8 (by rfl) ⟨465, by rfl⟩) (B 931 (by norm_num) ⟨465, by rfl⟩ (by norm_num))
theorem R79469 : Reach 79469 := rs (se 3 (by rfl) ⟨14900, by rfl⟩) (B 29801 (by norm_num) ⟨14900, by rfl⟩ (by norm_num))
theorem R79493 : Reach 79493 := rs (se 4 (by rfl) ⟨7452, by rfl⟩) (B 14905 (by norm_num) ⟨7452, by rfl⟩ (by norm_num))
theorem R79517 : Reach 79517 := rs (se 3 (by rfl) ⟨14909, by rfl⟩) (B 29819 (by norm_num) ⟨14909, by rfl⟩ (by norm_num))
theorem R210613 : Reach 210613 := rs (se 5 (by rfl) ⟨9872, by rfl⟩) (B 19745 (by norm_num) ⟨9872, by rfl⟩ (by norm_num))
theorem R79541 : Reach 79541 := rs (se 5 (by rfl) ⟨3728, by rfl⟩) (B 7457 (by norm_num) ⟨3728, by rfl⟩ (by norm_num))
theorem R79565 : Reach 79565 := rs (se 3 (by rfl) ⟨14918, by rfl⟩) (B 29837 (by norm_num) ⟨14918, by rfl⟩ (by norm_num))
theorem R112357 : Reach 112357 := rs (se 4 (by rfl) ⟨10533, by rfl⟩) (B 21067 (by norm_num) ⟨10533, by rfl⟩ (by norm_num))
theorem R79589 : Reach 79589 := rs (se 4 (by rfl) ⟨7461, by rfl⟩) (B 14923 (by norm_num) ⟨7461, by rfl⟩ (by norm_num))
theorem R79613 : Reach 79613 := rs (se 3 (by rfl) ⟨14927, by rfl⟩) (B 29855 (by norm_num) ⟨14927, by rfl⟩ (by norm_num))
theorem R79637 : Reach 79637 := rs (se 6 (by rfl) ⟨1866, by rfl⟩) (B 3733 (by norm_num) ⟨1866, by rfl⟩ (by norm_num))
theorem R79661 : Reach 79661 := rs (se 3 (by rfl) ⟨14936, by rfl⟩) (B 29873 (by norm_num) ⟨14936, by rfl⟩ (by norm_num))
theorem R79685 : Reach 79685 := rs (se 4 (by rfl) ⟨7470, by rfl⟩) (B 14941 (by norm_num) ⟨7470, by rfl⟩ (by norm_num))
theorem R79709 : Reach 79709 := rs (se 3 (by rfl) ⟨14945, by rfl⟩) (B 29891 (by norm_num) ⟨14945, by rfl⟩ (by norm_num))
theorem R145253 : Reach 145253 := rs (se 4 (by rfl) ⟨13617, by rfl⟩) (B 27235 (by norm_num) ⟨13617, by rfl⟩ (by norm_num))
theorem R178037 : Reach 178037 := rs (se 5 (by rfl) ⟨8345, by rfl⟩) (B 16691 (by norm_num) ⟨8345, by rfl⟩ (by norm_num))
theorem R79733 : Reach 79733 := rs (se 5 (by rfl) ⟨3737, by rfl⟩) (B 7475 (by norm_num) ⟨3737, by rfl⟩ (by norm_num))
theorem R79757 : Reach 79757 := rs (se 3 (by rfl) ⟨14954, by rfl⟩) (B 29909 (by norm_num) ⟨14954, by rfl⟩ (by norm_num))
theorem R79781 : Reach 79781 := rs (se 4 (by rfl) ⟨7479, by rfl⟩) (B 14959 (by norm_num) ⟨7479, by rfl⟩ (by norm_num))
theorem R79805 : Reach 79805 := rs (se 3 (by rfl) ⟨14963, by rfl⟩) (B 29927 (by norm_num) ⟨14963, by rfl⟩ (by norm_num))
theorem R79829 : Reach 79829 := rs (se 7 (by rfl) ⟨935, by rfl⟩) (B 1871 (by norm_num) ⟨935, by rfl⟩ (by norm_num))
theorem R79853 : Reach 79853 := rs (se 3 (by rfl) ⟨14972, by rfl⟩) (B 29945 (by norm_num) ⟨14972, by rfl⟩ (by norm_num))
theorem R538613 : Reach 538613 := rs (se 5 (by rfl) ⟨25247, by rfl⟩) (B 50495 (by norm_num) ⟨25247, by rfl⟩ (by norm_num))
theorem R79877 : Reach 79877 := rs (se 4 (by rfl) ⟨7488, by rfl⟩) (B 14977 (by norm_num) ⟨7488, by rfl⟩ (by norm_num))
theorem R79901 : Reach 79901 := rs (se 3 (by rfl) ⟨14981, by rfl⟩) (B 29963 (by norm_num) ⟨14981, by rfl⟩ (by norm_num))
theorem R79925 : Reach 79925 := rs (se 5 (by rfl) ⟨3746, by rfl⟩) (B 7493 (by norm_num) ⟨3746, by rfl⟩ (by norm_num))
theorem R276533 : Reach 276533 := rs (se 5 (by rfl) ⟨12962, by rfl⟩) (B 25925 (by norm_num) ⟨12962, by rfl⟩ (by norm_num))
theorem R79949 : Reach 79949 := rs (se 3 (by rfl) ⟨14990, by rfl⟩) (B 29981 (by norm_num) ⟨14990, by rfl⟩ (by norm_num))
theorem R79973 : Reach 79973 := rs (se 4 (by rfl) ⟨7497, by rfl⟩) (B 14995 (by norm_num) ⟨7497, by rfl⟩ (by norm_num))
theorem R79997 : Reach 79997 := rs (se 3 (by rfl) ⟨14999, by rfl⟩) (B 29999 (by norm_num) ⟨14999, by rfl⟩ (by norm_num))
theorem R80021 : Reach 80021 := rs (se 6 (by rfl) ⟨1875, by rfl⟩) (B 3751 (by norm_num) ⟨1875, by rfl⟩ (by norm_num))
theorem R80045 : Reach 80045 := rs (se 3 (by rfl) ⟨15008, by rfl⟩) (B 30017 (by norm_num) ⟨15008, by rfl⟩ (by norm_num))
theorem R80069 : Reach 80069 := rs (se 4 (by rfl) ⟨7506, by rfl⟩) (B 15013 (by norm_num) ⟨7506, by rfl⟩ (by norm_num))
theorem R112853 : Reach 112853 := rs (se 7 (by rfl) ⟨1322, by rfl⟩) (B 2645 (by norm_num) ⟨1322, by rfl⟩ (by norm_num))
theorem R80093 : Reach 80093 := rs (se 3 (by rfl) ⟨15017, by rfl⟩) (B 30035 (by norm_num) ⟨15017, by rfl⟩ (by norm_num))
theorem R80117 : Reach 80117 := rs (se 5 (by rfl) ⟨3755, by rfl⟩) (B 7511 (by norm_num) ⟨3755, by rfl⟩ (by norm_num))
theorem R80141 : Reach 80141 := rs (se 3 (by rfl) ⟨15026, by rfl⟩) (B 30053 (by norm_num) ⟨15026, by rfl⟩ (by norm_num))
theorem R112909 : Reach 112909 := rs (se 3 (by rfl) ⟨21170, by rfl⟩) (B 42341 (by norm_num) ⟨21170, by rfl⟩ (by norm_num))
theorem R178469 : Reach 178469 := rs (se 4 (by rfl) ⟨16731, by rfl⟩) (B 33463 (by norm_num) ⟨16731, by rfl⟩ (by norm_num))
theorem R80165 : Reach 80165 := rs (se 4 (by rfl) ⟨7515, by rfl⟩) (B 15031 (by norm_num) ⟨7515, by rfl⟩ (by norm_num))
theorem R80189 : Reach 80189 := rs (se 3 (by rfl) ⟨15035, by rfl⟩) (B 30071 (by norm_num) ⟨15035, by rfl⟩ (by norm_num))
theorem R80213 : Reach 80213 := rs (se 10 (by rfl) ⟨117, by rfl⟩) (B 235 (by norm_num) ⟨117, by rfl⟩ (by norm_num))
theorem R80237 : Reach 80237 := rs (se 3 (by rfl) ⟨15044, by rfl⟩) (B 30089 (by norm_num) ⟨15044, by rfl⟩ (by norm_num))
theorem R80261 : Reach 80261 := rs (se 4 (by rfl) ⟨7524, by rfl⟩) (B 15049 (by norm_num) ⟨7524, by rfl⟩ (by norm_num))
theorem R80285 : Reach 80285 := rs (se 3 (by rfl) ⟨15053, by rfl⟩) (B 30107 (by norm_num) ⟨15053, by rfl⟩ (by norm_num))
theorem R80309 : Reach 80309 := rs (se 5 (by rfl) ⟨3764, by rfl⟩) (B 7529 (by norm_num) ⟨3764, by rfl⟩ (by norm_num))
theorem R80333 : Reach 80333 := rs (se 3 (by rfl) ⟨15062, by rfl⟩) (B 30125 (by norm_num) ⟨15062, by rfl⟩ (by norm_num))
theorem R80357 : Reach 80357 := rs (se 4 (by rfl) ⟨7533, by rfl⟩) (B 15067 (by norm_num) ⟨7533, by rfl⟩ (by norm_num))
theorem R80381 : Reach 80381 := rs (se 3 (by rfl) ⟨15071, by rfl⟩) (B 30143 (by norm_num) ⟨15071, by rfl⟩ (by norm_num))
theorem R80405 : Reach 80405 := rs (se 6 (by rfl) ⟨1884, by rfl⟩) (B 3769 (by norm_num) ⟨1884, by rfl⟩ (by norm_num))
theorem R80429 : Reach 80429 := rs (se 3 (by rfl) ⟨15080, by rfl⟩) (B 30161 (by norm_num) ⟨15080, by rfl⟩ (by norm_num))
theorem R80453 : Reach 80453 := rs (se 4 (by rfl) ⟨7542, by rfl⟩) (B 15085 (by norm_num) ⟨7542, by rfl⟩ (by norm_num))
theorem R80477 : Reach 80477 := rs (se 3 (by rfl) ⟨15089, by rfl⟩) (B 30179 (by norm_num) ⟨15089, by rfl⟩ (by norm_num))
theorem R80501 : Reach 80501 := rs (se 5 (by rfl) ⟨3773, by rfl⟩) (B 7547 (by norm_num) ⟨3773, by rfl⟩ (by norm_num))
theorem R80525 : Reach 80525 := rs (se 3 (by rfl) ⟨15098, by rfl⟩) (B 30197 (by norm_num) ⟨15098, by rfl⟩ (by norm_num))
theorem R277141 : Reach 277141 := rs (se 6 (by rfl) ⟨6495, by rfl⟩) (B 12991 (by norm_num) ⟨6495, by rfl⟩ (by norm_num))
theorem R80549 : Reach 80549 := rs (se 4 (by rfl) ⟨7551, by rfl⟩) (B 15103 (by norm_num) ⟨7551, by rfl⟩ (by norm_num))
theorem R80573 : Reach 80573 := rs (se 3 (by rfl) ⟨15107, by rfl⟩) (B 30215 (by norm_num) ⟨15107, by rfl⟩ (by norm_num))
theorem R178901 : Reach 178901 := rs (se 7 (by rfl) ⟨2096, by rfl⟩) (B 4193 (by norm_num) ⟨2096, by rfl⟩ (by norm_num))
theorem R80597 : Reach 80597 := rs (se 7 (by rfl) ⟨944, by rfl⟩) (B 1889 (by norm_num) ⟨944, by rfl⟩ (by norm_num))
theorem R80621 : Reach 80621 := rs (se 3 (by rfl) ⟨15116, by rfl⟩) (B 30233 (by norm_num) ⟨15116, by rfl⟩ (by norm_num))
theorem R80645 : Reach 80645 := rs (se 4 (by rfl) ⟨7560, by rfl⟩) (B 15121 (by norm_num) ⟨7560, by rfl⟩ (by norm_num))
theorem R80669 : Reach 80669 := rs (se 3 (by rfl) ⟨15125, by rfl⟩) (B 30251 (by norm_num) ⟨15125, by rfl⟩ (by norm_num))
theorem R80693 : Reach 80693 := rs (se 5 (by rfl) ⟨3782, by rfl⟩) (B 7565 (by norm_num) ⟨3782, by rfl⟩ (by norm_num))
theorem R146245 : Reach 146245 := rs (se 4 (by rfl) ⟨13710, by rfl⟩) (B 27421 (by norm_num) ⟨13710, by rfl⟩ (by norm_num))
theorem R80717 : Reach 80717 := rs (se 3 (by rfl) ⟨15134, by rfl⟩) (B 30269 (by norm_num) ⟨15134, by rfl⟩ (by norm_num))
theorem R80741 : Reach 80741 := rs (se 4 (by rfl) ⟨7569, by rfl⟩) (B 15139 (by norm_num) ⟨7569, by rfl⟩ (by norm_num))
theorem R80765 : Reach 80765 := rs (se 3 (by rfl) ⟨15143, by rfl⟩) (B 30287 (by norm_num) ⟨15143, by rfl⟩ (by norm_num))
theorem R80789 : Reach 80789 := rs (se 6 (by rfl) ⟨1893, by rfl⟩) (B 3787 (by norm_num) ⟨1893, by rfl⟩ (by norm_num))
theorem R80813 : Reach 80813 := rs (se 3 (by rfl) ⟨15152, by rfl⟩) (B 30305 (by norm_num) ⟨15152, by rfl⟩ (by norm_num))
theorem R80837 : Reach 80837 := rs (se 4 (by rfl) ⟨7578, by rfl⟩) (B 15157 (by norm_num) ⟨7578, by rfl⟩ (by norm_num))
theorem R506837 : Reach 506837 := rs (se 7 (by rfl) ⟨5939, by rfl⟩) (B 11879 (by norm_num) ⟨5939, by rfl⟩ (by norm_num))
theorem R80861 : Reach 80861 := rs (se 3 (by rfl) ⟨15161, by rfl⟩) (B 30323 (by norm_num) ⟨15161, by rfl⟩ (by norm_num))
theorem R80885 : Reach 80885 := rs (se 5 (by rfl) ⟨3791, by rfl⟩) (B 7583 (by norm_num) ⟨3791, by rfl⟩ (by norm_num))
theorem R80909 : Reach 80909 := rs (se 3 (by rfl) ⟨15170, by rfl⟩) (B 30341 (by norm_num) ⟨15170, by rfl⟩ (by norm_num))
theorem R80933 : Reach 80933 := rs (se 4 (by rfl) ⟨7587, by rfl⟩) (B 15175 (by norm_num) ⟨7587, by rfl⟩ (by norm_num))
theorem R113717 : Reach 113717 := rs (se 5 (by rfl) ⟨5330, by rfl⟩) (B 10661 (by norm_num) ⟨5330, by rfl⟩ (by norm_num))
theorem R80957 : Reach 80957 := rs (se 3 (by rfl) ⟨15179, by rfl⟩) (B 30359 (by norm_num) ⟨15179, by rfl⟩ (by norm_num))
theorem R80981 : Reach 80981 := rs (se 8 (by rfl) ⟨474, by rfl⟩) (B 949 (by norm_num) ⟨474, by rfl⟩ (by norm_num))
theorem R81005 : Reach 81005 := rs (se 3 (by rfl) ⟨15188, by rfl⟩) (B 30377 (by norm_num) ⟨15188, by rfl⟩ (by norm_num))
theorem R179333 : Reach 179333 := rs (se 4 (by rfl) ⟨16812, by rfl⟩) (B 33625 (by norm_num) ⟨16812, by rfl⟩ (by norm_num))
theorem R81029 : Reach 81029 := rs (se 4 (by rfl) ⟨7596, by rfl⟩) (B 15193 (by norm_num) ⟨7596, by rfl⟩ (by norm_num))
theorem R408725 : Reach 408725 := rs (se 6 (by rfl) ⟨9579, by rfl⟩) (B 19159 (by norm_num) ⟨9579, by rfl⟩ (by norm_num))
theorem R81053 : Reach 81053 := rs (se 3 (by rfl) ⟨15197, by rfl⟩) (B 30395 (by norm_num) ⟨15197, by rfl⟩ (by norm_num))
theorem R81077 : Reach 81077 := rs (se 5 (by rfl) ⟨3800, by rfl⟩) (B 7601 (by norm_num) ⟨3800, by rfl⟩ (by norm_num))
theorem R113861 : Reach 113861 := rs (se 4 (by rfl) ⟨10674, by rfl⟩) (B 21349 (by norm_num) ⟨10674, by rfl⟩ (by norm_num))
theorem R81101 : Reach 81101 := rs (se 3 (by rfl) ⟨15206, by rfl⟩) (B 30413 (by norm_num) ⟨15206, by rfl⟩ (by norm_num))
theorem R81125 : Reach 81125 := rs (se 4 (by rfl) ⟨7605, by rfl⟩) (B 15211 (by norm_num) ⟨7605, by rfl⟩ (by norm_num))
theorem R81149 : Reach 81149 := rs (se 3 (by rfl) ⟨15215, by rfl⟩) (B 30431 (by norm_num) ⟨15215, by rfl⟩ (by norm_num))
theorem R81173 : Reach 81173 := rs (se 6 (by rfl) ⟨1902, by rfl⟩) (B 3805 (by norm_num) ⟨1902, by rfl⟩ (by norm_num))
theorem R81197 : Reach 81197 := rs (se 3 (by rfl) ⟨15224, by rfl⟩) (B 30449 (by norm_num) ⟨15224, by rfl⟩ (by norm_num))
theorem R81221 : Reach 81221 := rs (se 4 (by rfl) ⟨7614, by rfl⟩) (B 15229 (by norm_num) ⟨7614, by rfl⟩ (by norm_num))
theorem R81245 : Reach 81245 := rs (se 3 (by rfl) ⟨15233, by rfl⟩) (B 30467 (by norm_num) ⟨15233, by rfl⟩ (by norm_num))
theorem R81269 : Reach 81269 := rs (se 5 (by rfl) ⟨3809, by rfl⟩) (B 7619 (by norm_num) ⟨3809, by rfl⟩ (by norm_num))
theorem R81293 : Reach 81293 := rs (se 3 (by rfl) ⟨15242, by rfl⟩) (B 30485 (by norm_num) ⟨15242, by rfl⟩ (by norm_num))
theorem R81317 : Reach 81317 := rs (se 4 (by rfl) ⟨7623, by rfl⟩) (B 15247 (by norm_num) ⟨7623, by rfl⟩ (by norm_num))
theorem R81341 : Reach 81341 := rs (se 3 (by rfl) ⟨15251, by rfl⟩) (B 30503 (by norm_num) ⟨15251, by rfl⟩ (by norm_num))
theorem R81365 : Reach 81365 := rs (se 7 (by rfl) ⟨953, by rfl⟩) (B 1907 (by norm_num) ⟨953, by rfl⟩ (by norm_num))
theorem R81389 : Reach 81389 := rs (se 3 (by rfl) ⟨15260, by rfl⟩) (B 30521 (by norm_num) ⟨15260, by rfl⟩ (by norm_num))
theorem R81413 : Reach 81413 := rs (se 4 (by rfl) ⟨7632, by rfl⟩) (B 15265 (by norm_num) ⟨7632, by rfl⟩ (by norm_num))
theorem R81437 : Reach 81437 := rs (se 3 (by rfl) ⟨15269, by rfl⟩) (B 30539 (by norm_num) ⟨15269, by rfl⟩ (by norm_num))
theorem R179765 : Reach 179765 := rs (se 5 (by rfl) ⟨8426, by rfl⟩) (B 16853 (by norm_num) ⟨8426, by rfl⟩ (by norm_num))
theorem R81461 : Reach 81461 := rs (se 5 (by rfl) ⟨3818, by rfl⟩) (B 7637 (by norm_num) ⟨3818, by rfl⟩ (by norm_num))
theorem R81485 : Reach 81485 := rs (se 3 (by rfl) ⟨15278, by rfl⟩) (B 30557 (by norm_num) ⟨15278, by rfl⟩ (by norm_num))
theorem R81509 : Reach 81509 := rs (se 4 (by rfl) ⟨7641, by rfl⟩) (B 15283 (by norm_num) ⟨7641, by rfl⟩ (by norm_num))
theorem R81533 : Reach 81533 := rs (se 3 (by rfl) ⟨15287, by rfl⟩) (B 30575 (by norm_num) ⟨15287, by rfl⟩ (by norm_num))
theorem R81557 : Reach 81557 := rs (se 6 (by rfl) ⟨1911, by rfl⟩) (B 3823 (by norm_num) ⟨1911, by rfl⟩ (by norm_num))
theorem R81581 : Reach 81581 := rs (se 3 (by rfl) ⟨15296, by rfl⟩) (B 30593 (by norm_num) ⟨15296, by rfl⟩ (by norm_num))
theorem R81605 : Reach 81605 := rs (se 4 (by rfl) ⟨7650, by rfl⟩) (B 15301 (by norm_num) ⟨7650, by rfl⟩ (by norm_num))
theorem R81629 : Reach 81629 := rs (se 3 (by rfl) ⟨15305, by rfl⟩) (B 30611 (by norm_num) ⟨15305, by rfl⟩ (by norm_num))
theorem R81653 : Reach 81653 := rs (se 5 (by rfl) ⟨3827, by rfl⟩) (B 7655 (by norm_num) ⟨3827, by rfl⟩ (by norm_num))
theorem R81677 : Reach 81677 := rs (se 3 (by rfl) ⟨15314, by rfl⟩) (B 30629 (by norm_num) ⟨15314, by rfl⟩ (by norm_num))
theorem R147221 : Reach 147221 := rs (se 6 (by rfl) ⟨3450, by rfl⟩) (B 6901 (by norm_num) ⟨3450, by rfl⟩ (by norm_num))
theorem R81701 : Reach 81701 := rs (se 4 (by rfl) ⟨7659, by rfl⟩) (B 15319 (by norm_num) ⟨7659, by rfl⟩ (by norm_num))
theorem R81725 : Reach 81725 := rs (se 3 (by rfl) ⟨15323, by rfl⟩) (B 30647 (by norm_num) ⟨15323, by rfl⟩ (by norm_num))
theorem R81749 : Reach 81749 := rs (se 9 (by rfl) ⟨239, by rfl⟩) (B 479 (by norm_num) ⟨239, by rfl⟩ (by norm_num))
theorem R81773 : Reach 81773 := rs (se 3 (by rfl) ⟨15332, by rfl⟩) (B 30665 (by norm_num) ⟨15332, by rfl⟩ (by norm_num))
theorem R81797 : Reach 81797 := rs (se 4 (by rfl) ⟨7668, by rfl⟩) (B 15337 (by norm_num) ⟨7668, by rfl⟩ (by norm_num))
theorem R147349 : Reach 147349 := rs (se 6 (by rfl) ⟨3453, by rfl⟩) (B 6907 (by norm_num) ⟨3453, by rfl⟩ (by norm_num))
theorem R81821 : Reach 81821 := rs (se 3 (by rfl) ⟨15341, by rfl⟩) (B 30683 (by norm_num) ⟨15341, by rfl⟩ (by norm_num))
theorem R114605 : Reach 114605 := rs (se 3 (by rfl) ⟨21488, by rfl⟩) (B 42977 (by norm_num) ⟨21488, by rfl⟩ (by norm_num))
theorem R81845 : Reach 81845 := rs (se 5 (by rfl) ⟨3836, by rfl⟩) (B 7673 (by norm_num) ⟨3836, by rfl⟩ (by norm_num))
theorem R81869 : Reach 81869 := rs (se 3 (by rfl) ⟨15350, by rfl⟩) (B 30701 (by norm_num) ⟨15350, by rfl⟩ (by norm_num))
theorem R180197 : Reach 180197 := rs (se 4 (by rfl) ⟨16893, by rfl⟩) (B 33787 (by norm_num) ⟨16893, by rfl⟩ (by norm_num))
theorem R81893 : Reach 81893 := rs (se 4 (by rfl) ⟨7677, by rfl⟩) (B 15355 (by norm_num) ⟨7677, by rfl⟩ (by norm_num))
theorem R81917 : Reach 81917 := rs (se 3 (by rfl) ⟨15359, by rfl⟩) (B 30719 (by norm_num) ⟨15359, by rfl⟩ (by norm_num))
theorem R81941 : Reach 81941 := rs (se 6 (by rfl) ⟨1920, by rfl⟩) (B 3841 (by norm_num) ⟨1920, by rfl⟩ (by norm_num))
theorem R81965 : Reach 81965 := rs (se 3 (by rfl) ⟨15368, by rfl⟩) (B 30737 (by norm_num) ⟨15368, by rfl⟩ (by norm_num))
theorem R81989 : Reach 81989 := rs (se 4 (by rfl) ⟨7686, by rfl⟩) (B 15373 (by norm_num) ⟨7686, by rfl⟩ (by norm_num))
theorem R82013 : Reach 82013 := rs (se 3 (by rfl) ⟨15377, by rfl⟩) (B 30755 (by norm_num) ⟨15377, by rfl⟩ (by norm_num))
theorem R82037 : Reach 82037 := rs (se 5 (by rfl) ⟨3845, by rfl⟩) (B 7691 (by norm_num) ⟨3845, by rfl⟩ (by norm_num))
theorem R82061 : Reach 82061 := rs (se 3 (by rfl) ⟨15386, by rfl⟩) (B 30773 (by norm_num) ⟨15386, by rfl⟩ (by norm_num))
theorem R82085 : Reach 82085 := rs (se 4 (by rfl) ⟨7695, by rfl⟩) (B 15391 (by norm_num) ⟨7695, by rfl⟩ (by norm_num))
theorem R82109 : Reach 82109 := rs (se 3 (by rfl) ⟨15395, by rfl⟩) (B 30791 (by norm_num) ⟨15395, by rfl⟩ (by norm_num))
theorem R278741 : Reach 278741 := rs (se 7 (by rfl) ⟨3266, by rfl⟩) (B 6533 (by norm_num) ⟨3266, by rfl⟩ (by norm_num))
theorem R82133 : Reach 82133 := rs (se 7 (by rfl) ⟨962, by rfl⟩) (B 1925 (by norm_num) ⟨962, by rfl⟩ (by norm_num))
theorem R82157 : Reach 82157 := rs (se 3 (by rfl) ⟨15404, by rfl⟩) (B 30809 (by norm_num) ⟨15404, by rfl⟩ (by norm_num))
theorem R82181 : Reach 82181 := rs (se 4 (by rfl) ⟨7704, by rfl⟩) (B 15409 (by norm_num) ⟨7704, by rfl⟩ (by norm_num))
theorem R82205 : Reach 82205 := rs (se 3 (by rfl) ⟨15413, by rfl⟩) (B 30827 (by norm_num) ⟨15413, by rfl⟩ (by norm_num))
theorem R82229 : Reach 82229 := rs (se 5 (by rfl) ⟨3854, by rfl⟩) (B 7709 (by norm_num) ⟨3854, by rfl⟩ (by norm_num))
theorem R82253 : Reach 82253 := rs (se 3 (by rfl) ⟨15422, by rfl⟩) (B 30845 (by norm_num) ⟨15422, by rfl⟩ (by norm_num))
theorem R115037 : Reach 115037 := rs (se 3 (by rfl) ⟨21569, by rfl⟩) (B 43139 (by norm_num) ⟨21569, by rfl⟩ (by norm_num))
theorem R82277 : Reach 82277 := rs (se 4 (by rfl) ⟨7713, by rfl⟩) (B 15427 (by norm_num) ⟨7713, by rfl⟩ (by norm_num))
theorem R82301 : Reach 82301 := rs (se 3 (by rfl) ⟨15431, by rfl⟩) (B 30863 (by norm_num) ⟨15431, by rfl⟩ (by norm_num))
theorem R180629 : Reach 180629 := rs (se 6 (by rfl) ⟨4233, by rfl⟩) (B 8467 (by norm_num) ⟨4233, by rfl⟩ (by norm_num))
theorem R82325 : Reach 82325 := rs (se 6 (by rfl) ⟨1929, by rfl⟩) (B 3859 (by norm_num) ⟨1929, by rfl⟩ (by norm_num))
theorem R115109 : Reach 115109 := rs (se 4 (by rfl) ⟨10791, by rfl⟩) (B 21583 (by norm_num) ⟨10791, by rfl⟩ (by norm_num))
theorem R82349 : Reach 82349 := rs (se 3 (by rfl) ⟨15440, by rfl⟩) (B 30881 (by norm_num) ⟨15440, by rfl⟩ (by norm_num))
theorem R82373 : Reach 82373 := rs (se 4 (by rfl) ⟨7722, by rfl⟩) (B 15445 (by norm_num) ⟨7722, by rfl⟩ (by norm_num))
theorem R82397 : Reach 82397 := rs (se 3 (by rfl) ⟨15449, by rfl⟩) (B 30899 (by norm_num) ⟨15449, by rfl⟩ (by norm_num))
theorem R115181 : Reach 115181 := rs (se 3 (by rfl) ⟨21596, by rfl⟩) (B 43193 (by norm_num) ⟨21596, by rfl⟩ (by norm_num))
theorem R82421 : Reach 82421 := rs (se 5 (by rfl) ⟨3863, by rfl⟩) (B 7727 (by norm_num) ⟨3863, by rfl⟩ (by norm_num))
theorem R82445 : Reach 82445 := rs (se 3 (by rfl) ⟨15458, by rfl⟩) (B 30917 (by norm_num) ⟨15458, by rfl⟩ (by norm_num))
theorem R82469 : Reach 82469 := rs (se 4 (by rfl) ⟨7731, by rfl⟩) (B 15463 (by norm_num) ⟨7731, by rfl⟩ (by norm_num))
theorem R115253 : Reach 115253 := rs (se 5 (by rfl) ⟨5402, by rfl⟩) (B 10805 (by norm_num) ⟨5402, by rfl⟩ (by norm_num))
theorem R82493 : Reach 82493 := rs (se 3 (by rfl) ⟨15467, by rfl⟩) (B 30935 (by norm_num) ⟨15467, by rfl⟩ (by norm_num))
theorem R82517 : Reach 82517 := rs (se 8 (by rfl) ⟨483, by rfl⟩) (B 967 (by norm_num) ⟨483, by rfl⟩ (by norm_num))
theorem R82541 : Reach 82541 := rs (se 3 (by rfl) ⟨15476, by rfl⟩) (B 30953 (by norm_num) ⟨15476, by rfl⟩ (by norm_num))
theorem R148085 : Reach 148085 := rs (se 5 (by rfl) ⟨6941, by rfl⟩) (B 13883 (by norm_num) ⟨6941, by rfl⟩ (by norm_num))
theorem R115325 : Reach 115325 := rs (se 3 (by rfl) ⟨21623, by rfl⟩) (B 43247 (by norm_num) ⟨21623, by rfl⟩ (by norm_num))
theorem R82565 : Reach 82565 := rs (se 4 (by rfl) ⟨7740, by rfl⟩) (B 15481 (by norm_num) ⟨7740, by rfl⟩ (by norm_num))
theorem R311957 : Reach 311957 := rs (se 6 (by rfl) ⟨7311, by rfl⟩) (B 14623 (by norm_num) ⟨7311, by rfl⟩ (by norm_num))
theorem R115357 : Reach 115357 := rs (se 3 (by rfl) ⟨21629, by rfl⟩) (B 43259 (by norm_num) ⟨21629, by rfl⟩ (by norm_num))
theorem R82589 : Reach 82589 := rs (se 3 (by rfl) ⟨15485, by rfl⟩) (B 30971 (by norm_num) ⟨15485, by rfl⟩ (by norm_num))
theorem R82613 : Reach 82613 := rs (se 5 (by rfl) ⟨3872, by rfl⟩) (B 7745 (by norm_num) ⟨3872, by rfl⟩ (by norm_num))
theorem R115397 : Reach 115397 := rs (se 4 (by rfl) ⟨10818, by rfl⟩) (B 21637 (by norm_num) ⟨10818, by rfl⟩ (by norm_num))
theorem R82637 : Reach 82637 := rs (se 3 (by rfl) ⟨15494, by rfl⟩) (B 30989 (by norm_num) ⟨15494, by rfl⟩ (by norm_num))
theorem R541397 : Reach 541397 := rs (se 7 (by rfl) ⟨6344, by rfl⟩) (B 12689 (by norm_num) ⟨6344, by rfl⟩ (by norm_num))
theorem R180949 : Reach 180949 := rs (se 7 (by rfl) ⟨2120, by rfl⟩) (B 4241 (by norm_num) ⟨2120, by rfl⟩ (by norm_num))
theorem R82661 : Reach 82661 := rs (se 4 (by rfl) ⟨7749, by rfl⟩) (B 15499 (by norm_num) ⟨7749, by rfl⟩ (by norm_num))
theorem R115469 : Reach 115469 := rs (se 3 (by rfl) ⟨21650, by rfl⟩) (B 43301 (by norm_num) ⟨21650, by rfl⟩ (by norm_num))
theorem R115501 : Reach 115501 := rs (se 3 (by rfl) ⟨21656, by rfl⟩) (B 43313 (by norm_num) ⟨21656, by rfl⟩ (by norm_num))
theorem R148277 : Reach 148277 := rs (se 5 (by rfl) ⟨6950, by rfl⟩) (B 13901 (by norm_num) ⟨6950, by rfl⟩ (by norm_num))
theorem R82757 : Reach 82757 := rs (se 4 (by rfl) ⟨7758, by rfl⟩) (B 15517 (by norm_num) ⟨7758, by rfl⟩ (by norm_num))
theorem R181061 : Reach 181061 := rs (se 4 (by rfl) ⟨16974, by rfl⟩) (B 33949 (by norm_num) ⟨16974, by rfl⟩ (by norm_num))
theorem R115541 : Reach 115541 := rs (se 9 (by rfl) ⟨338, by rfl⟩) (B 677 (by norm_num) ⟨338, by rfl⟩ (by norm_num))
theorem R115613 : Reach 115613 := rs (se 3 (by rfl) ⟨21677, by rfl⟩) (B 43355 (by norm_num) ⟨21677, by rfl⟩ (by norm_num))
theorem R115685 : Reach 115685 := rs (se 4 (by rfl) ⟨10845, by rfl⟩) (B 21691 (by norm_num) ⟨10845, by rfl⟩ (by norm_num))
theorem R181237 : Reach 181237 := rs (se 5 (by rfl) ⟨8495, by rfl⟩) (B 16991 (by norm_num) ⟨8495, by rfl⟩ (by norm_num))
theorem R82981 : Reach 82981 := rs (se 4 (by rfl) ⟨7779, by rfl⟩) (B 15559 (by norm_num) ⟨7779, by rfl⟩ (by norm_num))
theorem R115757 : Reach 115757 := rs (se 3 (by rfl) ⟨21704, by rfl⟩) (B 43409 (by norm_num) ⟨21704, by rfl⟩ (by norm_num))
theorem R115829 : Reach 115829 := rs (se 5 (by rfl) ⟨5429, by rfl⟩) (B 10859 (by norm_num) ⟨5429, by rfl⟩ (by norm_num))
theorem R115877 : Reach 115877 := rs (se 4 (by rfl) ⟨10863, by rfl⟩) (B 21727 (by norm_num) ⟨10863, by rfl⟩ (by norm_num))
theorem R115901 : Reach 115901 := rs (se 3 (by rfl) ⟨21731, by rfl⟩) (B 43463 (by norm_num) ⟨21731, by rfl⟩ (by norm_num))
theorem R181493 : Reach 181493 := rs (se 5 (by rfl) ⟨8507, by rfl⟩) (B 17015 (by norm_num) ⟨8507, by rfl⟩ (by norm_num))
theorem R115973 : Reach 115973 := rs (se 4 (by rfl) ⟨10872, by rfl⟩) (B 21745 (by norm_num) ⟨10872, by rfl⟩ (by norm_num))
theorem R116045 : Reach 116045 := rs (se 3 (by rfl) ⟨21758, by rfl⟩) (B 43517 (by norm_num) ⟨21758, by rfl⟩ (by norm_num))
theorem R148853 : Reach 148853 := rs (se 5 (by rfl) ⟨6977, by rfl⟩) (B 13955 (by norm_num) ⟨6977, by rfl⟩ (by norm_num))
theorem R116117 : Reach 116117 := rs (se 6 (by rfl) ⟨2721, by rfl⟩) (B 5443 (by norm_num) ⟨2721, by rfl⟩ (by norm_num))
theorem R116189 : Reach 116189 := rs (se 3 (by rfl) ⟨21785, by rfl⟩) (B 43571 (by norm_num) ⟨21785, by rfl⟩ (by norm_num))
theorem R116245 : Reach 116245 := rs (se 6 (by rfl) ⟨2724, by rfl⟩) (B 5449 (by norm_num) ⟨2724, by rfl⟩ (by norm_num))
theorem R116261 : Reach 116261 := rs (se 4 (by rfl) ⟨10899, by rfl⟩) (B 21799 (by norm_num) ⟨10899, by rfl⟩ (by norm_num))
theorem R476725 : Reach 476725 := rs (se 5 (by rfl) ⟨22346, by rfl⟩) (B 44693 (by norm_num) ⟨22346, by rfl⟩ (by norm_num))
theorem R116333 : Reach 116333 := rs (se 3 (by rfl) ⟨21812, by rfl⟩) (B 43625 (by norm_num) ⟨21812, by rfl⟩ (by norm_num))
theorem R181925 : Reach 181925 := rs (se 4 (by rfl) ⟨17055, by rfl⟩) (B 34111 (by norm_num) ⟨17055, by rfl⟩ (by norm_num))
theorem R116405 : Reach 116405 := rs (se 5 (by rfl) ⟨5456, by rfl⟩) (B 10913 (by norm_num) ⟨5456, by rfl⟩ (by norm_num))
theorem R116477 : Reach 116477 := rs (se 3 (by rfl) ⟨21839, by rfl⟩) (B 43679 (by norm_num) ⟨21839, by rfl⟩ (by norm_num))
theorem R116549 : Reach 116549 := rs (se 4 (by rfl) ⟨10926, by rfl⟩) (B 21853 (by norm_num) ⟨10926, by rfl⟩ (by norm_num))
theorem R345941 : Reach 345941 := rs (se 9 (by rfl) ⟨1013, by rfl⟩) (B 2027 (by norm_num) ⟨1013, by rfl⟩ (by norm_num))
theorem R116621 : Reach 116621 := rs (se 3 (by rfl) ⟨21866, by rfl⟩) (B 43733 (by norm_num) ⟨21866, by rfl⟩ (by norm_num))
theorem R51121 : Reach 51121 := rs (se 2 (by rfl) ⟨19170, by rfl⟩) (B 38341 (by norm_num) ⟨19170, by rfl⟩ (by norm_num))
theorem R51125 : Reach 51125 := rs (se 5 (by rfl) ⟨2396, by rfl⟩) (B 4793 (by norm_num) ⟨2396, by rfl⟩ (by norm_num))
theorem R51129 : Reach 51129 := rs (se 2 (by rfl) ⟨19173, by rfl⟩) (B 38347 (by norm_num) ⟨19173, by rfl⟩ (by norm_num))
theorem R51133 : Reach 51133 := rs (se 3 (by rfl) ⟨9587, by rfl⟩) (B 19175 (by norm_num) ⟨9587, by rfl⟩ (by norm_num))
theorem R51137 : Reach 51137 := rs (se 2 (by rfl) ⟨19176, by rfl⟩) (B 38353 (by norm_num) ⟨19176, by rfl⟩ (by norm_num))
theorem R51141 : Reach 51141 := rs (se 4 (by rfl) ⟨4794, by rfl⟩) (B 9589 (by norm_num) ⟨4794, by rfl⟩ (by norm_num))
theorem R51145 : Reach 51145 := rs (se 2 (by rfl) ⟨19179, by rfl⟩) (B 38359 (by norm_num) ⟨19179, by rfl⟩ (by norm_num))
theorem R51149 : Reach 51149 := rs (se 3 (by rfl) ⟨9590, by rfl⟩) (B 19181 (by norm_num) ⟨9590, by rfl⟩ (by norm_num))
theorem R51153 : Reach 51153 := rs (se 2 (by rfl) ⟨19182, by rfl⟩) (B 38365 (by norm_num) ⟨19182, by rfl⟩ (by norm_num))
theorem R51157 : Reach 51157 := rs (se 7 (by rfl) ⟨599, by rfl⟩) (B 1199 (by norm_num) ⟨599, by rfl⟩ (by norm_num))
theorem R116693 : Reach 116693 := rs (se 7 (by rfl) ⟨1367, by rfl⟩) (B 2735 (by norm_num) ⟨1367, by rfl⟩ (by norm_num))
theorem R51161 : Reach 51161 := rs (se 2 (by rfl) ⟨19185, by rfl⟩) (B 38371 (by norm_num) ⟨19185, by rfl⟩ (by norm_num))
theorem R51165 : Reach 51165 := rs (se 3 (by rfl) ⟨9593, by rfl⟩) (B 19187 (by norm_num) ⟨9593, by rfl⟩ (by norm_num))
theorem R51169 : Reach 51169 := rs (se 2 (by rfl) ⟨19188, by rfl⟩) (B 38377 (by norm_num) ⟨19188, by rfl⟩ (by norm_num))
theorem R51173 : Reach 51173 := rs (se 4 (by rfl) ⟨4797, by rfl⟩) (B 9595 (by norm_num) ⟨4797, by rfl⟩ (by norm_num))
theorem R51177 : Reach 51177 := rs (se 2 (by rfl) ⟨19191, by rfl⟩) (B 38383 (by norm_num) ⟨19191, by rfl⟩ (by norm_num))
theorem R51181 : Reach 51181 := rs (se 3 (by rfl) ⟨9596, by rfl⟩) (B 19193 (by norm_num) ⟨9596, by rfl⟩ (by norm_num))
theorem R51185 : Reach 51185 := rs (se 2 (by rfl) ⟨19194, by rfl⟩) (B 38389 (by norm_num) ⟨19194, by rfl⟩ (by norm_num))
theorem R51189 : Reach 51189 := rs (se 5 (by rfl) ⟨2399, by rfl⟩) (B 4799 (by norm_num) ⟨2399, by rfl⟩ (by norm_num))
theorem R51193 : Reach 51193 := rs (se 2 (by rfl) ⟨19197, by rfl⟩) (B 38395 (by norm_num) ⟨19197, by rfl⟩ (by norm_num))
theorem R51197 : Reach 51197 := rs (se 3 (by rfl) ⟨9599, by rfl⟩) (B 19199 (by norm_num) ⟨9599, by rfl⟩ (by norm_num))
theorem R51201 : Reach 51201 := rs (se 2 (by rfl) ⟨19200, by rfl⟩) (B 38401 (by norm_num) ⟨19200, by rfl⟩ (by norm_num))
theorem R51205 : Reach 51205 := rs (se 4 (by rfl) ⟨4800, by rfl⟩) (B 9601 (by norm_num) ⟨4800, by rfl⟩ (by norm_num))
theorem R51209 : Reach 51209 := rs (se 2 (by rfl) ⟨19203, by rfl⟩) (B 38407 (by norm_num) ⟨19203, by rfl⟩ (by norm_num))
theorem R51213 : Reach 51213 := rs (se 3 (by rfl) ⟨9602, by rfl⟩) (B 19205 (by norm_num) ⟨9602, by rfl⟩ (by norm_num))
theorem R51217 : Reach 51217 := rs (se 2 (by rfl) ⟨19206, by rfl⟩) (B 38413 (by norm_num) ⟨19206, by rfl⟩ (by norm_num))
theorem R51221 : Reach 51221 := rs (se 6 (by rfl) ⟨1200, by rfl⟩) (B 2401 (by norm_num) ⟨1200, by rfl⟩ (by norm_num))
theorem R51225 : Reach 51225 := rs (se 2 (by rfl) ⟨19209, by rfl⟩) (B 38419 (by norm_num) ⟨19209, by rfl⟩ (by norm_num))
theorem R51229 : Reach 51229 := rs (se 3 (by rfl) ⟨9605, by rfl⟩) (B 19211 (by norm_num) ⟨9605, by rfl⟩ (by norm_num))
theorem R116765 : Reach 116765 := rs (se 3 (by rfl) ⟨21893, by rfl⟩) (B 43787 (by norm_num) ⟨21893, by rfl⟩ (by norm_num))
theorem R51233 : Reach 51233 := rs (se 2 (by rfl) ⟨19212, by rfl⟩) (B 38425 (by norm_num) ⟨19212, by rfl⟩ (by norm_num))
theorem R51237 : Reach 51237 := rs (se 4 (by rfl) ⟨4803, by rfl⟩) (B 9607 (by norm_num) ⟨4803, by rfl⟩ (by norm_num))
theorem R51241 : Reach 51241 := rs (se 2 (by rfl) ⟨19215, by rfl⟩) (B 38431 (by norm_num) ⟨19215, by rfl⟩ (by norm_num))
theorem R51245 : Reach 51245 := rs (se 3 (by rfl) ⟨9608, by rfl⟩) (B 19217 (by norm_num) ⟨9608, by rfl⟩ (by norm_num))
theorem R51249 : Reach 51249 := rs (se 2 (by rfl) ⟨19218, by rfl⟩) (B 38437 (by norm_num) ⟨19218, by rfl⟩ (by norm_num))
theorem R51253 : Reach 51253 := rs (se 5 (by rfl) ⟨2402, by rfl⟩) (B 4805 (by norm_num) ⟨2402, by rfl⟩ (by norm_num))
theorem R51257 : Reach 51257 := rs (se 2 (by rfl) ⟨19221, by rfl⟩) (B 38443 (by norm_num) ⟨19221, by rfl⟩ (by norm_num))
theorem R51261 : Reach 51261 := rs (se 3 (by rfl) ⟨9611, by rfl⟩) (B 19223 (by norm_num) ⟨9611, by rfl⟩ (by norm_num))
theorem R51265 : Reach 51265 := rs (se 2 (by rfl) ⟨19224, by rfl⟩) (B 38449 (by norm_num) ⟨19224, by rfl⟩ (by norm_num))
theorem R51269 : Reach 51269 := rs (se 4 (by rfl) ⟨4806, by rfl⟩) (B 9613 (by norm_num) ⟨4806, by rfl⟩ (by norm_num))
theorem R51273 : Reach 51273 := rs (se 2 (by rfl) ⟨19227, by rfl⟩) (B 38455 (by norm_num) ⟨19227, by rfl⟩ (by norm_num))
theorem R51277 : Reach 51277 := rs (se 3 (by rfl) ⟨9614, by rfl⟩) (B 19229 (by norm_num) ⟨9614, by rfl⟩ (by norm_num))
theorem R51281 : Reach 51281 := rs (se 2 (by rfl) ⟨19230, by rfl⟩) (B 38461 (by norm_num) ⟨19230, by rfl⟩ (by norm_num))
theorem R51285 : Reach 51285 := rs (se 8 (by rfl) ⟨300, by rfl⟩) (B 601 (by norm_num) ⟨300, by rfl⟩ (by norm_num))
theorem R182357 : Reach 182357 := rs (se 8 (by rfl) ⟨1068, by rfl⟩) (B 2137 (by norm_num) ⟨1068, by rfl⟩ (by norm_num))
theorem R51289 : Reach 51289 := rs (se 2 (by rfl) ⟨19233, by rfl⟩) (B 38467 (by norm_num) ⟨19233, by rfl⟩ (by norm_num))
theorem R51293 : Reach 51293 := rs (se 3 (by rfl) ⟨9617, by rfl⟩) (B 19235 (by norm_num) ⟨9617, by rfl⟩ (by norm_num))
theorem R51297 : Reach 51297 := rs (se 2 (by rfl) ⟨19236, by rfl⟩) (B 38473 (by norm_num) ⟨19236, by rfl⟩ (by norm_num))
theorem R51301 : Reach 51301 := rs (se 4 (by rfl) ⟨4809, by rfl⟩) (B 9619 (by norm_num) ⟨4809, by rfl⟩ (by norm_num))
theorem R116837 : Reach 116837 := rs (se 4 (by rfl) ⟨10953, by rfl⟩) (B 21907 (by norm_num) ⟨10953, by rfl⟩ (by norm_num))
theorem R51305 : Reach 51305 := rs (se 2 (by rfl) ⟨19239, by rfl⟩) (B 38479 (by norm_num) ⟨19239, by rfl⟩ (by norm_num))
theorem R51309 : Reach 51309 := rs (se 3 (by rfl) ⟨9620, by rfl⟩) (B 19241 (by norm_num) ⟨9620, by rfl⟩ (by norm_num))
theorem R51313 : Reach 51313 := rs (se 2 (by rfl) ⟨19242, by rfl⟩) (B 38485 (by norm_num) ⟨19242, by rfl⟩ (by norm_num))
theorem R51317 : Reach 51317 := rs (se 5 (by rfl) ⟨2405, by rfl⟩) (B 4811 (by norm_num) ⟨2405, by rfl⟩ (by norm_num))
theorem R51321 : Reach 51321 := rs (se 2 (by rfl) ⟨19245, by rfl⟩) (B 38491 (by norm_num) ⟨19245, by rfl⟩ (by norm_num))
theorem R51325 : Reach 51325 := rs (se 3 (by rfl) ⟨9623, by rfl⟩) (B 19247 (by norm_num) ⟨9623, by rfl⟩ (by norm_num))
theorem R51329 : Reach 51329 := rs (se 2 (by rfl) ⟨19248, by rfl⟩) (B 38497 (by norm_num) ⟨19248, by rfl⟩ (by norm_num))
theorem R51333 : Reach 51333 := rs (se 4 (by rfl) ⟨4812, by rfl⟩) (B 9625 (by norm_num) ⟨4812, by rfl⟩ (by norm_num))
theorem R51337 : Reach 51337 := rs (se 2 (by rfl) ⟨19251, by rfl⟩) (B 38503 (by norm_num) ⟨19251, by rfl⟩ (by norm_num))
theorem R51341 : Reach 51341 := rs (se 3 (by rfl) ⟨9626, by rfl⟩) (B 19253 (by norm_num) ⟨9626, by rfl⟩ (by norm_num))
theorem R51345 : Reach 51345 := rs (se 2 (by rfl) ⟨19254, by rfl⟩) (B 38509 (by norm_num) ⟨19254, by rfl⟩ (by norm_num))
theorem R51349 : Reach 51349 := rs (se 6 (by rfl) ⟨1203, by rfl⟩) (B 2407 (by norm_num) ⟨1203, by rfl⟩ (by norm_num))
theorem R51353 : Reach 51353 := rs (se 2 (by rfl) ⟨19257, by rfl⟩) (B 38515 (by norm_num) ⟨19257, by rfl⟩ (by norm_num))
theorem R51357 : Reach 51357 := rs (se 3 (by rfl) ⟨9629, by rfl⟩) (B 19259 (by norm_num) ⟨9629, by rfl⟩ (by norm_num))
theorem R51361 : Reach 51361 := rs (se 2 (by rfl) ⟨19260, by rfl⟩) (B 38521 (by norm_num) ⟨19260, by rfl⟩ (by norm_num))
theorem R51365 : Reach 51365 := rs (se 4 (by rfl) ⟨4815, by rfl⟩) (B 9631 (by norm_num) ⟨4815, by rfl⟩ (by norm_num))
theorem R51369 : Reach 51369 := rs (se 2 (by rfl) ⟨19263, by rfl⟩) (B 38527 (by norm_num) ⟨19263, by rfl⟩ (by norm_num))
theorem R51373 : Reach 51373 := rs (se 3 (by rfl) ⟨9632, by rfl⟩) (B 19265 (by norm_num) ⟨9632, by rfl⟩ (by norm_num))
theorem R116909 : Reach 116909 := rs (se 3 (by rfl) ⟨21920, by rfl⟩) (B 43841 (by norm_num) ⟨21920, by rfl⟩ (by norm_num))
theorem R51377 : Reach 51377 := rs (se 2 (by rfl) ⟨19266, by rfl⟩) (B 38533 (by norm_num) ⟨19266, by rfl⟩ (by norm_num))
theorem R51381 : Reach 51381 := rs (se 5 (by rfl) ⟨2408, by rfl⟩) (B 4817 (by norm_num) ⟨2408, by rfl⟩ (by norm_num))
theorem R51385 : Reach 51385 := rs (se 2 (by rfl) ⟨19269, by rfl⟩) (B 38539 (by norm_num) ⟨19269, by rfl⟩ (by norm_num))
theorem R51389 : Reach 51389 := rs (se 3 (by rfl) ⟨9635, by rfl⟩) (B 19271 (by norm_num) ⟨9635, by rfl⟩ (by norm_num))
theorem R51393 : Reach 51393 := rs (se 2 (by rfl) ⟨19272, by rfl⟩) (B 38545 (by norm_num) ⟨19272, by rfl⟩ (by norm_num))
theorem R51397 : Reach 51397 := rs (se 4 (by rfl) ⟨4818, by rfl⟩) (B 9637 (by norm_num) ⟨4818, by rfl⟩ (by norm_num))
theorem R215237 : Reach 215237 := rs (se 4 (by rfl) ⟨20178, by rfl⟩) (B 40357 (by norm_num) ⟨20178, by rfl⟩ (by norm_num))
theorem R51401 : Reach 51401 := rs (se 2 (by rfl) ⟨19275, by rfl⟩) (B 38551 (by norm_num) ⟨19275, by rfl⟩ (by norm_num))
theorem R51405 : Reach 51405 := rs (se 3 (by rfl) ⟨9638, by rfl⟩) (B 19277 (by norm_num) ⟨9638, by rfl⟩ (by norm_num))
theorem R51409 : Reach 51409 := rs (se 2 (by rfl) ⟨19278, by rfl⟩) (B 38557 (by norm_num) ⟨19278, by rfl⟩ (by norm_num))
theorem R51413 : Reach 51413 := rs (se 7 (by rfl) ⟨602, by rfl⟩) (B 1205 (by norm_num) ⟨602, by rfl⟩ (by norm_num))
theorem R248021 : Reach 248021 := rs (se 7 (by rfl) ⟨2906, by rfl⟩) (B 5813 (by norm_num) ⟨2906, by rfl⟩ (by norm_num))
theorem R51417 : Reach 51417 := rs (se 2 (by rfl) ⟨19281, by rfl⟩) (B 38563 (by norm_num) ⟨19281, by rfl⟩ (by norm_num))
theorem R51421 : Reach 51421 := rs (se 3 (by rfl) ⟨9641, by rfl⟩) (B 19283 (by norm_num) ⟨9641, by rfl⟩ (by norm_num))
theorem R51425 : Reach 51425 := rs (se 2 (by rfl) ⟨19284, by rfl⟩) (B 38569 (by norm_num) ⟨19284, by rfl⟩ (by norm_num))
theorem R51429 : Reach 51429 := rs (se 4 (by rfl) ⟨4821, by rfl⟩) (B 9643 (by norm_num) ⟨4821, by rfl⟩ (by norm_num))
theorem R51433 : Reach 51433 := rs (se 2 (by rfl) ⟨19287, by rfl⟩) (B 38575 (by norm_num) ⟨19287, by rfl⟩ (by norm_num))
theorem R51437 : Reach 51437 := rs (se 3 (by rfl) ⟨9644, by rfl⟩) (B 19289 (by norm_num) ⟨9644, by rfl⟩ (by norm_num))
theorem R51441 : Reach 51441 := rs (se 2 (by rfl) ⟨19290, by rfl⟩) (B 38581 (by norm_num) ⟨19290, by rfl⟩ (by norm_num))
theorem R51445 : Reach 51445 := rs (se 5 (by rfl) ⟨2411, by rfl⟩) (B 4823 (by norm_num) ⟨2411, by rfl⟩ (by norm_num))
theorem R116981 : Reach 116981 := rs (se 5 (by rfl) ⟨5483, by rfl⟩) (B 10967 (by norm_num) ⟨5483, by rfl⟩ (by norm_num))
theorem R51449 : Reach 51449 := rs (se 2 (by rfl) ⟨19293, by rfl⟩) (B 38587 (by norm_num) ⟨19293, by rfl⟩ (by norm_num))
theorem R51453 : Reach 51453 := rs (se 3 (by rfl) ⟨9647, by rfl⟩) (B 19295 (by norm_num) ⟨9647, by rfl⟩ (by norm_num))
theorem R51457 : Reach 51457 := rs (se 2 (by rfl) ⟨19296, by rfl⟩) (B 38593 (by norm_num) ⟨19296, by rfl⟩ (by norm_num))
theorem R51461 : Reach 51461 := rs (se 4 (by rfl) ⟨4824, by rfl⟩) (B 9649 (by norm_num) ⟨4824, by rfl⟩ (by norm_num))
theorem R51465 : Reach 51465 := rs (se 2 (by rfl) ⟨19299, by rfl⟩) (B 38599 (by norm_num) ⟨19299, by rfl⟩ (by norm_num))
theorem R51469 : Reach 51469 := rs (se 3 (by rfl) ⟨9650, by rfl⟩) (B 19301 (by norm_num) ⟨9650, by rfl⟩ (by norm_num))
theorem R51473 : Reach 51473 := rs (se 2 (by rfl) ⟨19302, by rfl⟩) (B 38605 (by norm_num) ⟨19302, by rfl⟩ (by norm_num))
theorem R51477 : Reach 51477 := rs (se 6 (by rfl) ⟨1206, by rfl⟩) (B 2413 (by norm_num) ⟨1206, by rfl⟩ (by norm_num))
theorem R51481 : Reach 51481 := rs (se 2 (by rfl) ⟨19305, by rfl⟩) (B 38611 (by norm_num) ⟨19305, by rfl⟩ (by norm_num))
theorem R51485 : Reach 51485 := rs (se 3 (by rfl) ⟨9653, by rfl⟩) (B 19307 (by norm_num) ⟨9653, by rfl⟩ (by norm_num))
theorem R51489 : Reach 51489 := rs (se 2 (by rfl) ⟨19308, by rfl⟩) (B 38617 (by norm_num) ⟨19308, by rfl⟩ (by norm_num))
theorem R51493 : Reach 51493 := rs (se 4 (by rfl) ⟨4827, by rfl⟩) (B 9655 (by norm_num) ⟨4827, by rfl⟩ (by norm_num))
theorem R51497 : Reach 51497 := rs (se 2 (by rfl) ⟨19311, by rfl⟩) (B 38623 (by norm_num) ⟨19311, by rfl⟩ (by norm_num))
theorem R51501 : Reach 51501 := rs (se 3 (by rfl) ⟨9656, by rfl⟩) (B 19313 (by norm_num) ⟨9656, by rfl⟩ (by norm_num))
theorem R51505 : Reach 51505 := rs (se 2 (by rfl) ⟨19314, by rfl⟩) (B 38629 (by norm_num) ⟨19314, by rfl⟩ (by norm_num))
theorem R51509 : Reach 51509 := rs (se 5 (by rfl) ⟨2414, by rfl⟩) (B 4829 (by norm_num) ⟨2414, by rfl⟩ (by norm_num))
theorem R51513 : Reach 51513 := rs (se 2 (by rfl) ⟨19317, by rfl⟩) (B 38635 (by norm_num) ⟨19317, by rfl⟩ (by norm_num))
theorem R51517 : Reach 51517 := rs (se 3 (by rfl) ⟨9659, by rfl⟩) (B 19319 (by norm_num) ⟨9659, by rfl⟩ (by norm_num))
theorem R117053 : Reach 117053 := rs (se 3 (by rfl) ⟨21947, by rfl⟩) (B 43895 (by norm_num) ⟨21947, by rfl⟩ (by norm_num))
theorem R51521 : Reach 51521 := rs (se 2 (by rfl) ⟨19320, by rfl⟩) (B 38641 (by norm_num) ⟨19320, by rfl⟩ (by norm_num))
theorem R51525 : Reach 51525 := rs (se 4 (by rfl) ⟨4830, by rfl⟩) (B 9661 (by norm_num) ⟨4830, by rfl⟩ (by norm_num))
theorem R51529 : Reach 51529 := rs (se 2 (by rfl) ⟨19323, by rfl⟩) (B 38647 (by norm_num) ⟨19323, by rfl⟩ (by norm_num))
theorem R51533 : Reach 51533 := rs (se 3 (by rfl) ⟨9662, by rfl⟩) (B 19325 (by norm_num) ⟨9662, by rfl⟩ (by norm_num))
theorem R51537 : Reach 51537 := rs (se 2 (by rfl) ⟨19326, by rfl⟩) (B 38653 (by norm_num) ⟨19326, by rfl⟩ (by norm_num))
theorem R51541 : Reach 51541 := rs (se 10 (by rfl) ⟨75, by rfl⟩) (B 151 (by norm_num) ⟨75, by rfl⟩ (by norm_num))
theorem R51545 : Reach 51545 := rs (se 2 (by rfl) ⟨19329, by rfl⟩) (B 38659 (by norm_num) ⟨19329, by rfl⟩ (by norm_num))
theorem R51549 : Reach 51549 := rs (se 3 (by rfl) ⟨9665, by rfl⟩) (B 19331 (by norm_num) ⟨9665, by rfl⟩ (by norm_num))
theorem R51553 : Reach 51553 := rs (se 2 (by rfl) ⟨19332, by rfl⟩) (B 38665 (by norm_num) ⟨19332, by rfl⟩ (by norm_num))
theorem R51557 : Reach 51557 := rs (se 4 (by rfl) ⟨4833, by rfl⟩) (B 9667 (by norm_num) ⟨4833, by rfl⟩ (by norm_num))
theorem R51561 : Reach 51561 := rs (se 2 (by rfl) ⟨19335, by rfl⟩) (B 38671 (by norm_num) ⟨19335, by rfl⟩ (by norm_num))
theorem R51565 : Reach 51565 := rs (se 3 (by rfl) ⟨9668, by rfl⟩) (B 19337 (by norm_num) ⟨9668, by rfl⟩ (by norm_num))
theorem R51569 : Reach 51569 := rs (se 2 (by rfl) ⟨19338, by rfl⟩) (B 38677 (by norm_num) ⟨19338, by rfl⟩ (by norm_num))
theorem R51573 : Reach 51573 := rs (se 5 (by rfl) ⟨2417, by rfl⟩) (B 4835 (by norm_num) ⟨2417, by rfl⟩ (by norm_num))
theorem R51577 : Reach 51577 := rs (se 2 (by rfl) ⟨19341, by rfl⟩) (B 38683 (by norm_num) ⟨19341, by rfl⟩ (by norm_num))
theorem R51581 : Reach 51581 := rs (se 3 (by rfl) ⟨9671, by rfl⟩) (B 19343 (by norm_num) ⟨9671, by rfl⟩ (by norm_num))
theorem R51585 : Reach 51585 := rs (se 2 (by rfl) ⟨19344, by rfl⟩) (B 38689 (by norm_num) ⟨19344, by rfl⟩ (by norm_num))
theorem R51589 : Reach 51589 := rs (se 4 (by rfl) ⟨4836, by rfl⟩) (B 9673 (by norm_num) ⟨4836, by rfl⟩ (by norm_num))
theorem R117125 : Reach 117125 := rs (se 4 (by rfl) ⟨10980, by rfl⟩) (B 21961 (by norm_num) ⟨10980, by rfl⟩ (by norm_num))
theorem R51593 : Reach 51593 := rs (se 2 (by rfl) ⟨19347, by rfl⟩) (B 38695 (by norm_num) ⟨19347, by rfl⟩ (by norm_num))
theorem R51597 : Reach 51597 := rs (se 3 (by rfl) ⟨9674, by rfl⟩) (B 19349 (by norm_num) ⟨9674, by rfl⟩ (by norm_num))
theorem R51601 : Reach 51601 := rs (se 2 (by rfl) ⟨19350, by rfl⟩) (B 38701 (by norm_num) ⟨19350, by rfl⟩ (by norm_num))
theorem R51605 : Reach 51605 := rs (se 6 (by rfl) ⟨1209, by rfl⟩) (B 2419 (by norm_num) ⟨1209, by rfl⟩ (by norm_num))
theorem R51609 : Reach 51609 := rs (se 2 (by rfl) ⟨19353, by rfl⟩) (B 38707 (by norm_num) ⟨19353, by rfl⟩ (by norm_num))
theorem R51613 : Reach 51613 := rs (se 3 (by rfl) ⟨9677, by rfl⟩) (B 19355 (by norm_num) ⟨9677, by rfl⟩ (by norm_num))
theorem R51617 : Reach 51617 := rs (se 2 (by rfl) ⟨19356, by rfl⟩) (B 38713 (by norm_num) ⟨19356, by rfl⟩ (by norm_num))
theorem R51621 : Reach 51621 := rs (se 4 (by rfl) ⟨4839, by rfl⟩) (B 9679 (by norm_num) ⟨4839, by rfl⟩ (by norm_num))
theorem R51625 : Reach 51625 := rs (se 2 (by rfl) ⟨19359, by rfl⟩) (B 38719 (by norm_num) ⟨19359, by rfl⟩ (by norm_num))
theorem R51629 : Reach 51629 := rs (se 3 (by rfl) ⟨9680, by rfl⟩) (B 19361 (by norm_num) ⟨9680, by rfl⟩ (by norm_num))
theorem R84397 : Reach 84397 := rs (se 3 (by rfl) ⟨15824, by rfl⟩) (B 31649 (by norm_num) ⟨15824, by rfl⟩ (by norm_num))
theorem R51633 : Reach 51633 := rs (se 2 (by rfl) ⟨19362, by rfl⟩) (B 38725 (by norm_num) ⟨19362, by rfl⟩ (by norm_num))
theorem R51637 : Reach 51637 := rs (se 5 (by rfl) ⟨2420, by rfl⟩) (B 4841 (by norm_num) ⟨2420, by rfl⟩ (by norm_num))
theorem R51641 : Reach 51641 := rs (se 2 (by rfl) ⟨19365, by rfl⟩) (B 38731 (by norm_num) ⟨19365, by rfl⟩ (by norm_num))
theorem R51645 : Reach 51645 := rs (se 3 (by rfl) ⟨9683, by rfl⟩) (B 19367 (by norm_num) ⟨9683, by rfl⟩ (by norm_num))
theorem R51649 : Reach 51649 := rs (se 2 (by rfl) ⟨19368, by rfl⟩) (B 38737 (by norm_num) ⟨19368, by rfl⟩ (by norm_num))
theorem R51653 : Reach 51653 := rs (se 4 (by rfl) ⟨4842, by rfl⟩) (B 9685 (by norm_num) ⟨4842, by rfl⟩ (by norm_num))
theorem R51657 : Reach 51657 := rs (se 2 (by rfl) ⟨19371, by rfl⟩) (B 38743 (by norm_num) ⟨19371, by rfl⟩ (by norm_num))
theorem R51661 : Reach 51661 := rs (se 3 (by rfl) ⟨9686, by rfl⟩) (B 19373 (by norm_num) ⟨9686, by rfl⟩ (by norm_num))
theorem R117197 : Reach 117197 := rs (se 3 (by rfl) ⟨21974, by rfl⟩) (B 43949 (by norm_num) ⟨21974, by rfl⟩ (by norm_num))
theorem R51665 : Reach 51665 := rs (se 2 (by rfl) ⟨19374, by rfl⟩) (B 38749 (by norm_num) ⟨19374, by rfl⟩ (by norm_num))
theorem R51669 : Reach 51669 := rs (se 7 (by rfl) ⟨605, by rfl⟩) (B 1211 (by norm_num) ⟨605, by rfl⟩ (by norm_num))
theorem R182741 : Reach 182741 := rs (se 7 (by rfl) ⟨2141, by rfl⟩) (B 4283 (by norm_num) ⟨2141, by rfl⟩ (by norm_num))
theorem R51673 : Reach 51673 := rs (se 2 (by rfl) ⟨19377, by rfl⟩) (B 38755 (by norm_num) ⟨19377, by rfl⟩ (by norm_num))
theorem R51677 : Reach 51677 := rs (se 3 (by rfl) ⟨9689, by rfl⟩) (B 19379 (by norm_num) ⟨9689, by rfl⟩ (by norm_num))
theorem R51681 : Reach 51681 := rs (se 2 (by rfl) ⟨19380, by rfl⟩) (B 38761 (by norm_num) ⟨19380, by rfl⟩ (by norm_num))
theorem R51685 : Reach 51685 := rs (se 4 (by rfl) ⟨4845, by rfl⟩) (B 9691 (by norm_num) ⟨4845, by rfl⟩ (by norm_num))
theorem R51689 : Reach 51689 := rs (se 2 (by rfl) ⟨19383, by rfl⟩) (B 38767 (by norm_num) ⟨19383, by rfl⟩ (by norm_num))
theorem R51693 : Reach 51693 := rs (se 3 (by rfl) ⟨9692, by rfl⟩) (B 19385 (by norm_num) ⟨9692, by rfl⟩ (by norm_num))
theorem R51697 : Reach 51697 := rs (se 2 (by rfl) ⟨19386, by rfl⟩) (B 38773 (by norm_num) ⟨19386, by rfl⟩ (by norm_num))
theorem R51701 : Reach 51701 := rs (se 5 (by rfl) ⟨2423, by rfl⟩) (B 4847 (by norm_num) ⟨2423, by rfl⟩ (by norm_num))
theorem R51705 : Reach 51705 := rs (se 2 (by rfl) ⟨19389, by rfl⟩) (B 38779 (by norm_num) ⟨19389, by rfl⟩ (by norm_num))
theorem R51709 : Reach 51709 := rs (se 3 (by rfl) ⟨9695, by rfl⟩) (B 19391 (by norm_num) ⟨9695, by rfl⟩ (by norm_num))
theorem R51713 : Reach 51713 := rs (se 2 (by rfl) ⟨19392, by rfl⟩) (B 38785 (by norm_num) ⟨19392, by rfl⟩ (by norm_num))
theorem R51717 : Reach 51717 := rs (se 4 (by rfl) ⟨4848, by rfl⟩) (B 9697 (by norm_num) ⟨4848, by rfl⟩ (by norm_num))
theorem R182789 : Reach 182789 := rs (se 4 (by rfl) ⟨17136, by rfl⟩) (B 34273 (by norm_num) ⟨17136, by rfl⟩ (by norm_num))
theorem R51721 : Reach 51721 := rs (se 2 (by rfl) ⟨19395, by rfl⟩) (B 38791 (by norm_num) ⟨19395, by rfl⟩ (by norm_num))
theorem R51725 : Reach 51725 := rs (se 3 (by rfl) ⟨9698, by rfl⟩) (B 19397 (by norm_num) ⟨9698, by rfl⟩ (by norm_num))
theorem R51729 : Reach 51729 := rs (se 2 (by rfl) ⟨19398, by rfl⟩) (B 38797 (by norm_num) ⟨19398, by rfl⟩ (by norm_num))
theorem R51733 : Reach 51733 := rs (se 6 (by rfl) ⟨1212, by rfl⟩) (B 2425 (by norm_num) ⟨1212, by rfl⟩ (by norm_num))
theorem R117269 : Reach 117269 := rs (se 6 (by rfl) ⟨2748, by rfl⟩) (B 5497 (by norm_num) ⟨2748, by rfl⟩ (by norm_num))
theorem R51737 : Reach 51737 := rs (se 2 (by rfl) ⟨19401, by rfl⟩) (B 38803 (by norm_num) ⟨19401, by rfl⟩ (by norm_num))
theorem R51741 : Reach 51741 := rs (se 3 (by rfl) ⟨9701, by rfl⟩) (B 19403 (by norm_num) ⟨9701, by rfl⟩ (by norm_num))
theorem R51745 : Reach 51745 := rs (se 2 (by rfl) ⟨19404, by rfl⟩) (B 38809 (by norm_num) ⟨19404, by rfl⟩ (by norm_num))
theorem R51749 : Reach 51749 := rs (se 4 (by rfl) ⟨4851, by rfl⟩) (B 9703 (by norm_num) ⟨4851, by rfl⟩ (by norm_num))
theorem R51753 : Reach 51753 := rs (se 2 (by rfl) ⟨19407, by rfl⟩) (B 38815 (by norm_num) ⟨19407, by rfl⟩ (by norm_num))
theorem R51757 : Reach 51757 := rs (se 3 (by rfl) ⟨9704, by rfl⟩) (B 19409 (by norm_num) ⟨9704, by rfl⟩ (by norm_num))
theorem R51761 : Reach 51761 := rs (se 2 (by rfl) ⟨19410, by rfl⟩) (B 38821 (by norm_num) ⟨19410, by rfl⟩ (by norm_num))
theorem R51765 : Reach 51765 := rs (se 5 (by rfl) ⟨2426, by rfl⟩) (B 4853 (by norm_num) ⟨2426, by rfl⟩ (by norm_num))
theorem R51769 : Reach 51769 := rs (se 2 (by rfl) ⟨19413, by rfl⟩) (B 38827 (by norm_num) ⟨19413, by rfl⟩ (by norm_num))
theorem R51773 : Reach 51773 := rs (se 3 (by rfl) ⟨9707, by rfl⟩) (B 19415 (by norm_num) ⟨9707, by rfl⟩ (by norm_num))
theorem R51777 : Reach 51777 := rs (se 2 (by rfl) ⟨19416, by rfl⟩) (B 38833 (by norm_num) ⟨19416, by rfl⟩ (by norm_num))
theorem R51781 : Reach 51781 := rs (se 4 (by rfl) ⟨4854, by rfl⟩) (B 9709 (by norm_num) ⟨4854, by rfl⟩ (by norm_num))
theorem R51785 : Reach 51785 := rs (se 2 (by rfl) ⟨19419, by rfl⟩) (B 38839 (by norm_num) ⟨19419, by rfl⟩ (by norm_num))
theorem R51789 : Reach 51789 := rs (se 3 (by rfl) ⟨9710, by rfl⟩) (B 19421 (by norm_num) ⟨9710, by rfl⟩ (by norm_num))
theorem R51793 : Reach 51793 := rs (se 2 (by rfl) ⟨19422, by rfl⟩) (B 38845 (by norm_num) ⟨19422, by rfl⟩ (by norm_num))
theorem R51797 : Reach 51797 := rs (se 8 (by rfl) ⟨303, by rfl⟩) (B 607 (by norm_num) ⟨303, by rfl⟩ (by norm_num))
theorem R51801 : Reach 51801 := rs (se 2 (by rfl) ⟨19425, by rfl⟩) (B 38851 (by norm_num) ⟨19425, by rfl⟩ (by norm_num))
theorem R51805 : Reach 51805 := rs (se 3 (by rfl) ⟨9713, by rfl⟩) (B 19427 (by norm_num) ⟨9713, by rfl⟩ (by norm_num))
theorem R117341 : Reach 117341 := rs (se 3 (by rfl) ⟨22001, by rfl⟩) (B 44003 (by norm_num) ⟨22001, by rfl⟩ (by norm_num))
theorem R51809 : Reach 51809 := rs (se 2 (by rfl) ⟨19428, by rfl⟩) (B 38857 (by norm_num) ⟨19428, by rfl⟩ (by norm_num))
theorem R51813 : Reach 51813 := rs (se 4 (by rfl) ⟨4857, by rfl⟩) (B 9715 (by norm_num) ⟨4857, by rfl⟩ (by norm_num))
theorem R51817 : Reach 51817 := rs (se 2 (by rfl) ⟨19431, by rfl⟩) (B 38863 (by norm_num) ⟨19431, by rfl⟩ (by norm_num))
theorem R51821 : Reach 51821 := rs (se 3 (by rfl) ⟨9716, by rfl⟩) (B 19433 (by norm_num) ⟨9716, by rfl⟩ (by norm_num))
theorem R51825 : Reach 51825 := rs (se 2 (by rfl) ⟨19434, by rfl⟩) (B 38869 (by norm_num) ⟨19434, by rfl⟩ (by norm_num))
theorem R51829 : Reach 51829 := rs (se 5 (by rfl) ⟨2429, by rfl⟩) (B 4859 (by norm_num) ⟨2429, by rfl⟩ (by norm_num))
theorem R51833 : Reach 51833 := rs (se 2 (by rfl) ⟨19437, by rfl⟩) (B 38875 (by norm_num) ⟨19437, by rfl⟩ (by norm_num))
theorem R51837 : Reach 51837 := rs (se 3 (by rfl) ⟨9719, by rfl⟩) (B 19439 (by norm_num) ⟨9719, by rfl⟩ (by norm_num))
theorem R51841 : Reach 51841 := rs (se 2 (by rfl) ⟨19440, by rfl⟩) (B 38881 (by norm_num) ⟨19440, by rfl⟩ (by norm_num))
theorem R51845 : Reach 51845 := rs (se 4 (by rfl) ⟨4860, by rfl⟩) (B 9721 (by norm_num) ⟨4860, by rfl⟩ (by norm_num))
theorem R51849 : Reach 51849 := rs (se 2 (by rfl) ⟨19443, by rfl⟩) (B 38887 (by norm_num) ⟨19443, by rfl⟩ (by norm_num))
theorem R51853 : Reach 51853 := rs (se 3 (by rfl) ⟨9722, by rfl⟩) (B 19445 (by norm_num) ⟨9722, by rfl⟩ (by norm_num))
theorem R51857 : Reach 51857 := rs (se 2 (by rfl) ⟨19446, by rfl⟩) (B 38893 (by norm_num) ⟨19446, by rfl⟩ (by norm_num))
theorem R51861 : Reach 51861 := rs (se 6 (by rfl) ⟨1215, by rfl⟩) (B 2431 (by norm_num) ⟨1215, by rfl⟩ (by norm_num))
theorem R51865 : Reach 51865 := rs (se 2 (by rfl) ⟨19449, by rfl⟩) (B 38899 (by norm_num) ⟨19449, by rfl⟩ (by norm_num))
theorem R51869 : Reach 51869 := rs (se 3 (by rfl) ⟨9725, by rfl⟩) (B 19451 (by norm_num) ⟨9725, by rfl⟩ (by norm_num))
theorem R51873 : Reach 51873 := rs (se 2 (by rfl) ⟨19452, by rfl⟩) (B 38905 (by norm_num) ⟨19452, by rfl⟩ (by norm_num))
theorem R51877 : Reach 51877 := rs (se 4 (by rfl) ⟨4863, by rfl⟩) (B 9727 (by norm_num) ⟨4863, by rfl⟩ (by norm_num))
theorem R117413 : Reach 117413 := rs (se 4 (by rfl) ⟨11007, by rfl⟩) (B 22015 (by norm_num) ⟨11007, by rfl⟩ (by norm_num))
theorem R51881 : Reach 51881 := rs (se 2 (by rfl) ⟨19455, by rfl⟩) (B 38911 (by norm_num) ⟨19455, by rfl⟩ (by norm_num))
theorem R51885 : Reach 51885 := rs (se 3 (by rfl) ⟨9728, by rfl⟩) (B 19457 (by norm_num) ⟨9728, by rfl⟩ (by norm_num))
theorem R84653 : Reach 84653 := rs (se 3 (by rfl) ⟨15872, by rfl⟩) (B 31745 (by norm_num) ⟨15872, by rfl⟩ (by norm_num))
theorem R51889 : Reach 51889 := rs (se 2 (by rfl) ⟨19458, by rfl⟩) (B 38917 (by norm_num) ⟨19458, by rfl⟩ (by norm_num))
theorem R51893 : Reach 51893 := rs (se 5 (by rfl) ⟨2432, by rfl⟩) (B 4865 (by norm_num) ⟨2432, by rfl⟩ (by norm_num))
theorem R51897 : Reach 51897 := rs (se 2 (by rfl) ⟨19461, by rfl⟩) (B 38923 (by norm_num) ⟨19461, by rfl⟩ (by norm_num))
theorem R51901 : Reach 51901 := rs (se 3 (by rfl) ⟨9731, by rfl⟩) (B 19463 (by norm_num) ⟨9731, by rfl⟩ (by norm_num))
theorem R51905 : Reach 51905 := rs (se 2 (by rfl) ⟨19464, by rfl⟩) (B 38929 (by norm_num) ⟨19464, by rfl⟩ (by norm_num))
theorem R51909 : Reach 51909 := rs (se 4 (by rfl) ⟨4866, by rfl⟩) (B 9733 (by norm_num) ⟨4866, by rfl⟩ (by norm_num))
theorem R51913 : Reach 51913 := rs (se 2 (by rfl) ⟨19467, by rfl⟩) (B 38935 (by norm_num) ⟨19467, by rfl⟩ (by norm_num))
theorem R51917 : Reach 51917 := rs (se 3 (by rfl) ⟨9734, by rfl⟩) (B 19469 (by norm_num) ⟨9734, by rfl⟩ (by norm_num))
theorem R51921 : Reach 51921 := rs (se 2 (by rfl) ⟨19470, by rfl⟩) (B 38941 (by norm_num) ⟨19470, by rfl⟩ (by norm_num))
theorem R51925 : Reach 51925 := rs (se 7 (by rfl) ⟨608, by rfl⟩) (B 1217 (by norm_num) ⟨608, by rfl⟩ (by norm_num))
theorem R51929 : Reach 51929 := rs (se 2 (by rfl) ⟨19473, by rfl⟩) (B 38947 (by norm_num) ⟨19473, by rfl⟩ (by norm_num))
theorem R51933 : Reach 51933 := rs (se 3 (by rfl) ⟨9737, by rfl⟩) (B 19475 (by norm_num) ⟨9737, by rfl⟩ (by norm_num))
theorem R51937 : Reach 51937 := rs (se 2 (by rfl) ⟨19476, by rfl⟩) (B 38953 (by norm_num) ⟨19476, by rfl⟩ (by norm_num))
theorem R51941 : Reach 51941 := rs (se 4 (by rfl) ⟨4869, by rfl⟩) (B 9739 (by norm_num) ⟨4869, by rfl⟩ (by norm_num))
theorem R51945 : Reach 51945 := rs (se 2 (by rfl) ⟨19479, by rfl⟩) (B 38959 (by norm_num) ⟨19479, by rfl⟩ (by norm_num))
theorem R51949 : Reach 51949 := rs (se 3 (by rfl) ⟨9740, by rfl⟩) (B 19481 (by norm_num) ⟨9740, by rfl⟩ (by norm_num))
theorem R117485 : Reach 117485 := rs (se 3 (by rfl) ⟨22028, by rfl⟩) (B 44057 (by norm_num) ⟨22028, by rfl⟩ (by norm_num))
theorem R51953 : Reach 51953 := rs (se 2 (by rfl) ⟨19482, by rfl⟩) (B 38965 (by norm_num) ⟨19482, by rfl⟩ (by norm_num))
theorem R51957 : Reach 51957 := rs (se 5 (by rfl) ⟨2435, by rfl⟩) (B 4871 (by norm_num) ⟨2435, by rfl⟩ (by norm_num))
theorem R51961 : Reach 51961 := rs (se 2 (by rfl) ⟨19485, by rfl⟩) (B 38971 (by norm_num) ⟨19485, by rfl⟩ (by norm_num))
theorem R51965 : Reach 51965 := rs (se 3 (by rfl) ⟨9743, by rfl⟩) (B 19487 (by norm_num) ⟨9743, by rfl⟩ (by norm_num))
theorem R51969 : Reach 51969 := rs (se 2 (by rfl) ⟨19488, by rfl⟩) (B 38977 (by norm_num) ⟨19488, by rfl⟩ (by norm_num))
theorem R51973 : Reach 51973 := rs (se 4 (by rfl) ⟨4872, by rfl⟩) (B 9745 (by norm_num) ⟨4872, by rfl⟩ (by norm_num))
theorem R51977 : Reach 51977 := rs (se 2 (by rfl) ⟨19491, by rfl⟩) (B 38983 (by norm_num) ⟨19491, by rfl⟩ (by norm_num))
theorem R51981 : Reach 51981 := rs (se 3 (by rfl) ⟨9746, by rfl⟩) (B 19493 (by norm_num) ⟨9746, by rfl⟩ (by norm_num))
theorem R51985 : Reach 51985 := rs (se 2 (by rfl) ⟨19494, by rfl⟩) (B 38989 (by norm_num) ⟨19494, by rfl⟩ (by norm_num))
theorem R51989 : Reach 51989 := rs (se 6 (by rfl) ⟨1218, by rfl⟩) (B 2437 (by norm_num) ⟨1218, by rfl⟩ (by norm_num))
theorem R51993 : Reach 51993 := rs (se 2 (by rfl) ⟨19497, by rfl⟩) (B 38995 (by norm_num) ⟨19497, by rfl⟩ (by norm_num))
theorem R51997 : Reach 51997 := rs (se 3 (by rfl) ⟨9749, by rfl⟩) (B 19499 (by norm_num) ⟨9749, by rfl⟩ (by norm_num))
theorem R52001 : Reach 52001 := rs (se 2 (by rfl) ⟨19500, by rfl⟩) (B 39001 (by norm_num) ⟨19500, by rfl⟩ (by norm_num))
theorem R52005 : Reach 52005 := rs (se 4 (by rfl) ⟨4875, by rfl⟩) (B 9751 (by norm_num) ⟨4875, by rfl⟩ (by norm_num))
theorem R52009 : Reach 52009 := rs (se 2 (by rfl) ⟨19503, by rfl⟩) (B 39007 (by norm_num) ⟨19503, by rfl⟩ (by norm_num))
theorem R52013 : Reach 52013 := rs (se 3 (by rfl) ⟨9752, by rfl⟩) (B 19505 (by norm_num) ⟨9752, by rfl⟩ (by norm_num))
theorem R52017 : Reach 52017 := rs (se 2 (by rfl) ⟨19506, by rfl⟩) (B 39013 (by norm_num) ⟨19506, by rfl⟩ (by norm_num))
theorem R52021 : Reach 52021 := rs (se 5 (by rfl) ⟨2438, by rfl⟩) (B 4877 (by norm_num) ⟨2438, by rfl⟩ (by norm_num))
theorem R117557 : Reach 117557 := rs (se 5 (by rfl) ⟨5510, by rfl⟩) (B 11021 (by norm_num) ⟨5510, by rfl⟩ (by norm_num))
theorem R52025 : Reach 52025 := rs (se 2 (by rfl) ⟨19509, by rfl⟩) (B 39019 (by norm_num) ⟨19509, by rfl⟩ (by norm_num))
theorem R52029 : Reach 52029 := rs (se 3 (by rfl) ⟨9755, by rfl⟩) (B 19511 (by norm_num) ⟨9755, by rfl⟩ (by norm_num))
theorem R52033 : Reach 52033 := rs (se 2 (by rfl) ⟨19512, by rfl⟩) (B 39025 (by norm_num) ⟨19512, by rfl⟩ (by norm_num))
theorem R52037 : Reach 52037 := rs (se 4 (by rfl) ⟨4878, by rfl⟩) (B 9757 (by norm_num) ⟨4878, by rfl⟩ (by norm_num))
theorem R52041 : Reach 52041 := rs (se 2 (by rfl) ⟨19515, by rfl⟩) (B 39031 (by norm_num) ⟨19515, by rfl⟩ (by norm_num))
theorem R52045 : Reach 52045 := rs (se 3 (by rfl) ⟨9758, by rfl⟩) (B 19517 (by norm_num) ⟨9758, by rfl⟩ (by norm_num))
theorem R52049 : Reach 52049 := rs (se 2 (by rfl) ⟨19518, by rfl⟩) (B 39037 (by norm_num) ⟨19518, by rfl⟩ (by norm_num))
theorem R52053 : Reach 52053 := rs (se 9 (by rfl) ⟨152, by rfl⟩) (B 305 (by norm_num) ⟨152, by rfl⟩ (by norm_num))
theorem R52057 : Reach 52057 := rs (se 2 (by rfl) ⟨19521, by rfl⟩) (B 39043 (by norm_num) ⟨19521, by rfl⟩ (by norm_num))
theorem R52061 : Reach 52061 := rs (se 3 (by rfl) ⟨9761, by rfl⟩) (B 19523 (by norm_num) ⟨9761, by rfl⟩ (by norm_num))
theorem R84829 : Reach 84829 := rs (se 3 (by rfl) ⟨15905, by rfl⟩) (B 31811 (by norm_num) ⟨15905, by rfl⟩ (by norm_num))
theorem R52065 : Reach 52065 := rs (se 2 (by rfl) ⟨19524, by rfl⟩) (B 39049 (by norm_num) ⟨19524, by rfl⟩ (by norm_num))
theorem R52069 : Reach 52069 := rs (se 4 (by rfl) ⟨4881, by rfl⟩) (B 9763 (by norm_num) ⟨4881, by rfl⟩ (by norm_num))
theorem R52073 : Reach 52073 := rs (se 2 (by rfl) ⟨19527, by rfl⟩) (B 39055 (by norm_num) ⟨19527, by rfl⟩ (by norm_num))
theorem R52077 : Reach 52077 := rs (se 3 (by rfl) ⟨9764, by rfl⟩) (B 19529 (by norm_num) ⟨9764, by rfl⟩ (by norm_num))
theorem R84845 : Reach 84845 := rs (se 3 (by rfl) ⟨15908, by rfl⟩) (B 31817 (by norm_num) ⟨15908, by rfl⟩ (by norm_num))
theorem R52081 : Reach 52081 := rs (se 2 (by rfl) ⟨19530, by rfl⟩) (B 39061 (by norm_num) ⟨19530, by rfl⟩ (by norm_num))
theorem R52085 : Reach 52085 := rs (se 5 (by rfl) ⟨2441, by rfl⟩) (B 4883 (by norm_num) ⟨2441, by rfl⟩ (by norm_num))
theorem R52089 : Reach 52089 := rs (se 2 (by rfl) ⟨19533, by rfl⟩) (B 39067 (by norm_num) ⟨19533, by rfl⟩ (by norm_num))
theorem R52093 : Reach 52093 := rs (se 3 (by rfl) ⟨9767, by rfl⟩) (B 19535 (by norm_num) ⟨9767, by rfl⟩ (by norm_num))
theorem R117629 : Reach 117629 := rs (se 3 (by rfl) ⟨22055, by rfl⟩) (B 44111 (by norm_num) ⟨22055, by rfl⟩ (by norm_num))
theorem R52097 : Reach 52097 := rs (se 2 (by rfl) ⟨19536, by rfl⟩) (B 39073 (by norm_num) ⟨19536, by rfl⟩ (by norm_num))
theorem R52101 : Reach 52101 := rs (se 4 (by rfl) ⟨4884, by rfl⟩) (B 9769 (by norm_num) ⟨4884, by rfl⟩ (by norm_num))
theorem R52105 : Reach 52105 := rs (se 2 (by rfl) ⟨19539, by rfl⟩) (B 39079 (by norm_num) ⟨19539, by rfl⟩ (by norm_num))
theorem R52109 : Reach 52109 := rs (se 3 (by rfl) ⟨9770, by rfl⟩) (B 19541 (by norm_num) ⟨9770, by rfl⟩ (by norm_num))
theorem R52113 : Reach 52113 := rs (se 2 (by rfl) ⟨19542, by rfl⟩) (B 39085 (by norm_num) ⟨19542, by rfl⟩ (by norm_num))
theorem R52117 : Reach 52117 := rs (se 6 (by rfl) ⟨1221, by rfl⟩) (B 2443 (by norm_num) ⟨1221, by rfl⟩ (by norm_num))
theorem R52121 : Reach 52121 := rs (se 2 (by rfl) ⟨19545, by rfl⟩) (B 39091 (by norm_num) ⟨19545, by rfl⟩ (by norm_num))
theorem R52125 : Reach 52125 := rs (se 3 (by rfl) ⟨9773, by rfl⟩) (B 19547 (by norm_num) ⟨9773, by rfl⟩ (by norm_num))
theorem R52129 : Reach 52129 := rs (se 2 (by rfl) ⟨19548, by rfl⟩) (B 39097 (by norm_num) ⟨19548, by rfl⟩ (by norm_num))
theorem R52133 : Reach 52133 := rs (se 4 (by rfl) ⟨4887, by rfl⟩) (B 9775 (by norm_num) ⟨4887, by rfl⟩ (by norm_num))
theorem R150437 : Reach 150437 := rs (se 4 (by rfl) ⟨14103, by rfl⟩) (B 28207 (by norm_num) ⟨14103, by rfl⟩ (by norm_num))
theorem R52137 : Reach 52137 := rs (se 2 (by rfl) ⟨19551, by rfl⟩) (B 39103 (by norm_num) ⟨19551, by rfl⟩ (by norm_num))
theorem R52141 : Reach 52141 := rs (se 3 (by rfl) ⟨9776, by rfl⟩) (B 19553 (by norm_num) ⟨9776, by rfl⟩ (by norm_num))
theorem R52145 : Reach 52145 := rs (se 2 (by rfl) ⟨19554, by rfl⟩) (B 39109 (by norm_num) ⟨19554, by rfl⟩ (by norm_num))
theorem R52149 : Reach 52149 := rs (se 5 (by rfl) ⟨2444, by rfl⟩) (B 4889 (by norm_num) ⟨2444, by rfl⟩ (by norm_num))
theorem R183221 : Reach 183221 := rs (se 5 (by rfl) ⟨8588, by rfl⟩) (B 17177 (by norm_num) ⟨8588, by rfl⟩ (by norm_num))
theorem R52153 : Reach 52153 := rs (se 2 (by rfl) ⟨19557, by rfl⟩) (B 39115 (by norm_num) ⟨19557, by rfl⟩ (by norm_num))
theorem R52157 : Reach 52157 := rs (se 3 (by rfl) ⟨9779, by rfl⟩) (B 19559 (by norm_num) ⟨9779, by rfl⟩ (by norm_num))
theorem R52161 : Reach 52161 := rs (se 2 (by rfl) ⟨19560, by rfl⟩) (B 39121 (by norm_num) ⟨19560, by rfl⟩ (by norm_num))
theorem R52165 : Reach 52165 := rs (se 4 (by rfl) ⟨4890, by rfl⟩) (B 9781 (by norm_num) ⟨4890, by rfl⟩ (by norm_num))
theorem R117701 : Reach 117701 := rs (se 4 (by rfl) ⟨11034, by rfl⟩) (B 22069 (by norm_num) ⟨11034, by rfl⟩ (by norm_num))
theorem R52169 : Reach 52169 := rs (se 2 (by rfl) ⟨19563, by rfl⟩) (B 39127 (by norm_num) ⟨19563, by rfl⟩ (by norm_num))
theorem R52173 : Reach 52173 := rs (se 3 (by rfl) ⟨9782, by rfl⟩) (B 19565 (by norm_num) ⟨9782, by rfl⟩ (by norm_num))
theorem R52177 : Reach 52177 := rs (se 2 (by rfl) ⟨19566, by rfl⟩) (B 39133 (by norm_num) ⟨19566, by rfl⟩ (by norm_num))
theorem R52181 : Reach 52181 := rs (se 7 (by rfl) ⟨611, by rfl⟩) (B 1223 (by norm_num) ⟨611, by rfl⟩ (by norm_num))
theorem R52185 : Reach 52185 := rs (se 2 (by rfl) ⟨19569, by rfl⟩) (B 39139 (by norm_num) ⟨19569, by rfl⟩ (by norm_num))
theorem R52189 : Reach 52189 := rs (se 3 (by rfl) ⟨9785, by rfl⟩) (B 19571 (by norm_num) ⟨9785, by rfl⟩ (by norm_num))
theorem R52193 : Reach 52193 := rs (se 2 (by rfl) ⟨19572, by rfl⟩) (B 39145 (by norm_num) ⟨19572, by rfl⟩ (by norm_num))
theorem R52197 : Reach 52197 := rs (se 4 (by rfl) ⟨4893, by rfl⟩) (B 9787 (by norm_num) ⟨4893, by rfl⟩ (by norm_num))
theorem R52201 : Reach 52201 := rs (se 2 (by rfl) ⟨19575, by rfl⟩) (B 39151 (by norm_num) ⟨19575, by rfl⟩ (by norm_num))
theorem R52205 : Reach 52205 := rs (se 3 (by rfl) ⟨9788, by rfl⟩) (B 19577 (by norm_num) ⟨9788, by rfl⟩ (by norm_num))
theorem R52209 : Reach 52209 := rs (se 2 (by rfl) ⟨19578, by rfl⟩) (B 39157 (by norm_num) ⟨19578, by rfl⟩ (by norm_num))
theorem R52213 : Reach 52213 := rs (se 5 (by rfl) ⟨2447, by rfl⟩) (B 4895 (by norm_num) ⟨2447, by rfl⟩ (by norm_num))
theorem R52217 : Reach 52217 := rs (se 2 (by rfl) ⟨19581, by rfl⟩) (B 39163 (by norm_num) ⟨19581, by rfl⟩ (by norm_num))
theorem R52221 : Reach 52221 := rs (se 3 (by rfl) ⟨9791, by rfl⟩) (B 19583 (by norm_num) ⟨9791, by rfl⟩ (by norm_num))
theorem R52225 : Reach 52225 := rs (se 2 (by rfl) ⟨19584, by rfl⟩) (B 39169 (by norm_num) ⟨19584, by rfl⟩ (by norm_num))
theorem R52229 : Reach 52229 := rs (se 4 (by rfl) ⟨4896, by rfl⟩) (B 9793 (by norm_num) ⟨4896, by rfl⟩ (by norm_num))
theorem R52233 : Reach 52233 := rs (se 2 (by rfl) ⟨19587, by rfl⟩) (B 39175 (by norm_num) ⟨19587, by rfl⟩ (by norm_num))
theorem R52237 : Reach 52237 := rs (se 3 (by rfl) ⟨9794, by rfl⟩) (B 19589 (by norm_num) ⟨9794, by rfl⟩ (by norm_num))
theorem R117773 : Reach 117773 := rs (se 3 (by rfl) ⟨22082, by rfl⟩) (B 44165 (by norm_num) ⟨22082, by rfl⟩ (by norm_num))
theorem R52241 : Reach 52241 := rs (se 2 (by rfl) ⟨19590, by rfl⟩) (B 39181 (by norm_num) ⟨19590, by rfl⟩ (by norm_num))
theorem R52245 : Reach 52245 := rs (se 6 (by rfl) ⟨1224, by rfl⟩) (B 2449 (by norm_num) ⟨1224, by rfl⟩ (by norm_num))
theorem R52249 : Reach 52249 := rs (se 2 (by rfl) ⟨19593, by rfl⟩) (B 39187 (by norm_num) ⟨19593, by rfl⟩ (by norm_num))
theorem R52253 : Reach 52253 := rs (se 3 (by rfl) ⟨9797, by rfl⟩) (B 19595 (by norm_num) ⟨9797, by rfl⟩ (by norm_num))
theorem R52257 : Reach 52257 := rs (se 2 (by rfl) ⟨19596, by rfl⟩) (B 39193 (by norm_num) ⟨19596, by rfl⟩ (by norm_num))
theorem R52261 : Reach 52261 := rs (se 4 (by rfl) ⟨4899, by rfl⟩) (B 9799 (by norm_num) ⟨4899, by rfl⟩ (by norm_num))
theorem R52265 : Reach 52265 := rs (se 2 (by rfl) ⟨19599, by rfl⟩) (B 39199 (by norm_num) ⟨19599, by rfl⟩ (by norm_num))
theorem R52269 : Reach 52269 := rs (se 3 (by rfl) ⟨9800, by rfl⟩) (B 19601 (by norm_num) ⟨9800, by rfl⟩ (by norm_num))
theorem R52273 : Reach 52273 := rs (se 2 (by rfl) ⟨19602, by rfl⟩) (B 39205 (by norm_num) ⟨19602, by rfl⟩ (by norm_num))
theorem R52277 : Reach 52277 := rs (se 5 (by rfl) ⟨2450, by rfl⟩) (B 4901 (by norm_num) ⟨2450, by rfl⟩ (by norm_num))
theorem R52281 : Reach 52281 := rs (se 2 (by rfl) ⟨19605, by rfl⟩) (B 39211 (by norm_num) ⟨19605, by rfl⟩ (by norm_num))
theorem R52285 : Reach 52285 := rs (se 3 (by rfl) ⟨9803, by rfl⟩) (B 19607 (by norm_num) ⟨9803, by rfl⟩ (by norm_num))
theorem R52289 : Reach 52289 := rs (se 2 (by rfl) ⟨19608, by rfl⟩) (B 39217 (by norm_num) ⟨19608, by rfl⟩ (by norm_num))
theorem R52293 : Reach 52293 := rs (se 4 (by rfl) ⟨4902, by rfl⟩) (B 9805 (by norm_num) ⟨4902, by rfl⟩ (by norm_num))
theorem R52297 : Reach 52297 := rs (se 2 (by rfl) ⟨19611, by rfl⟩) (B 39223 (by norm_num) ⟨19611, by rfl⟩ (by norm_num))
theorem R52301 : Reach 52301 := rs (se 3 (by rfl) ⟨9806, by rfl⟩) (B 19613 (by norm_num) ⟨9806, by rfl⟩ (by norm_num))
theorem R52305 : Reach 52305 := rs (se 2 (by rfl) ⟨19614, by rfl⟩) (B 39229 (by norm_num) ⟨19614, by rfl⟩ (by norm_num))
theorem R52309 : Reach 52309 := rs (se 8 (by rfl) ⟨306, by rfl⟩) (B 613 (by norm_num) ⟨306, by rfl⟩ (by norm_num))
theorem R117845 : Reach 117845 := rs (se 8 (by rfl) ⟨690, by rfl⟩) (B 1381 (by norm_num) ⟨690, by rfl⟩ (by norm_num))
theorem R52313 : Reach 52313 := rs (se 2 (by rfl) ⟨19617, by rfl⟩) (B 39235 (by norm_num) ⟨19617, by rfl⟩ (by norm_num))
theorem R52317 : Reach 52317 := rs (se 3 (by rfl) ⟨9809, by rfl⟩) (B 19619 (by norm_num) ⟨9809, by rfl⟩ (by norm_num))
theorem R52321 : Reach 52321 := rs (se 2 (by rfl) ⟨19620, by rfl⟩) (B 39241 (by norm_num) ⟨19620, by rfl⟩ (by norm_num))
theorem R52325 : Reach 52325 := rs (se 4 (by rfl) ⟨4905, by rfl⟩) (B 9811 (by norm_num) ⟨4905, by rfl⟩ (by norm_num))
theorem R52329 : Reach 52329 := rs (se 2 (by rfl) ⟨19623, by rfl⟩) (B 39247 (by norm_num) ⟨19623, by rfl⟩ (by norm_num))
theorem R52333 : Reach 52333 := rs (se 3 (by rfl) ⟨9812, by rfl⟩) (B 19625 (by norm_num) ⟨9812, by rfl⟩ (by norm_num))
theorem R52337 : Reach 52337 := rs (se 2 (by rfl) ⟨19626, by rfl⟩) (B 39253 (by norm_num) ⟨19626, by rfl⟩ (by norm_num))
theorem R52341 : Reach 52341 := rs (se 5 (by rfl) ⟨2453, by rfl⟩) (B 4907 (by norm_num) ⟨2453, by rfl⟩ (by norm_num))
theorem R52345 : Reach 52345 := rs (se 2 (by rfl) ⟨19629, by rfl⟩) (B 39259 (by norm_num) ⟨19629, by rfl⟩ (by norm_num))
theorem R52349 : Reach 52349 := rs (se 3 (by rfl) ⟨9815, by rfl⟩) (B 19631 (by norm_num) ⟨9815, by rfl⟩ (by norm_num))
theorem R52353 : Reach 52353 := rs (se 2 (by rfl) ⟨19632, by rfl⟩) (B 39265 (by norm_num) ⟨19632, by rfl⟩ (by norm_num))
theorem R52357 : Reach 52357 := rs (se 4 (by rfl) ⟨4908, by rfl⟩) (B 9817 (by norm_num) ⟨4908, by rfl⟩ (by norm_num))
theorem R52361 : Reach 52361 := rs (se 2 (by rfl) ⟨19635, by rfl⟩) (B 39271 (by norm_num) ⟨19635, by rfl⟩ (by norm_num))
theorem R52365 : Reach 52365 := rs (se 3 (by rfl) ⟨9818, by rfl⟩) (B 19637 (by norm_num) ⟨9818, by rfl⟩ (by norm_num))
theorem R52369 : Reach 52369 := rs (se 2 (by rfl) ⟨19638, by rfl⟩) (B 39277 (by norm_num) ⟨19638, by rfl⟩ (by norm_num))
theorem R52373 : Reach 52373 := rs (se 6 (by rfl) ⟨1227, by rfl⟩) (B 2455 (by norm_num) ⟨1227, by rfl⟩ (by norm_num))
theorem R52377 : Reach 52377 := rs (se 2 (by rfl) ⟨19641, by rfl⟩) (B 39283 (by norm_num) ⟨19641, by rfl⟩ (by norm_num))
theorem R52381 : Reach 52381 := rs (se 3 (by rfl) ⟨9821, by rfl⟩) (B 19643 (by norm_num) ⟨9821, by rfl⟩ (by norm_num))
theorem R117917 : Reach 117917 := rs (se 3 (by rfl) ⟨22109, by rfl⟩) (B 44219 (by norm_num) ⟨22109, by rfl⟩ (by norm_num))
theorem R52385 : Reach 52385 := rs (se 2 (by rfl) ⟨19644, by rfl⟩) (B 39289 (by norm_num) ⟨19644, by rfl⟩ (by norm_num))
theorem R52389 : Reach 52389 := rs (se 4 (by rfl) ⟨4911, by rfl⟩) (B 9823 (by norm_num) ⟨4911, by rfl⟩ (by norm_num))
theorem R52393 : Reach 52393 := rs (se 2 (by rfl) ⟨19647, by rfl⟩) (B 39295 (by norm_num) ⟨19647, by rfl⟩ (by norm_num))
theorem R52397 : Reach 52397 := rs (se 3 (by rfl) ⟨9824, by rfl⟩) (B 19649 (by norm_num) ⟨9824, by rfl⟩ (by norm_num))
theorem R52401 : Reach 52401 := rs (se 2 (by rfl) ⟨19650, by rfl⟩) (B 39301 (by norm_num) ⟨19650, by rfl⟩ (by norm_num))
theorem R52405 : Reach 52405 := rs (se 5 (by rfl) ⟨2456, by rfl⟩) (B 4913 (by norm_num) ⟨2456, by rfl⟩ (by norm_num))
theorem R52409 : Reach 52409 := rs (se 2 (by rfl) ⟨19653, by rfl⟩) (B 39307 (by norm_num) ⟨19653, by rfl⟩ (by norm_num))
theorem R52413 : Reach 52413 := rs (se 3 (by rfl) ⟨9827, by rfl⟩) (B 19655 (by norm_num) ⟨9827, by rfl⟩ (by norm_num))
theorem R52417 : Reach 52417 := rs (se 2 (by rfl) ⟨19656, by rfl⟩) (B 39313 (by norm_num) ⟨19656, by rfl⟩ (by norm_num))
theorem R52421 : Reach 52421 := rs (se 4 (by rfl) ⟨4914, by rfl⟩) (B 9829 (by norm_num) ⟨4914, by rfl⟩ (by norm_num))
theorem R52425 : Reach 52425 := rs (se 2 (by rfl) ⟨19659, by rfl⟩) (B 39319 (by norm_num) ⟨19659, by rfl⟩ (by norm_num))
theorem R52429 : Reach 52429 := rs (se 3 (by rfl) ⟨9830, by rfl⟩) (B 19661 (by norm_num) ⟨9830, by rfl⟩ (by norm_num))
theorem R52433 : Reach 52433 := rs (se 2 (by rfl) ⟨19662, by rfl⟩) (B 39325 (by norm_num) ⟨19662, by rfl⟩ (by norm_num))
theorem R52437 : Reach 52437 := rs (se 7 (by rfl) ⟨614, by rfl⟩) (B 1229 (by norm_num) ⟨614, by rfl⟩ (by norm_num))
theorem R52441 : Reach 52441 := rs (se 2 (by rfl) ⟨19665, by rfl⟩) (B 39331 (by norm_num) ⟨19665, by rfl⟩ (by norm_num))
theorem R52445 : Reach 52445 := rs (se 3 (by rfl) ⟨9833, by rfl⟩) (B 19667 (by norm_num) ⟨9833, by rfl⟩ (by norm_num))
theorem R52449 : Reach 52449 := rs (se 2 (by rfl) ⟨19668, by rfl⟩) (B 39337 (by norm_num) ⟨19668, by rfl⟩ (by norm_num))
theorem R117989 : Reach 117989 := rs (se 4 (by rfl) ⟨11061, by rfl⟩) (B 22123 (by norm_num) ⟨11061, by rfl⟩ (by norm_num))
theorem R52453 : Reach 52453 := rs (se 4 (by rfl) ⟨4917, by rfl⟩) (B 9835 (by norm_num) ⟨4917, by rfl⟩ (by norm_num))
theorem R52457 : Reach 52457 := rs (se 2 (by rfl) ⟨19671, by rfl⟩) (B 39343 (by norm_num) ⟨19671, by rfl⟩ (by norm_num))
theorem R52461 : Reach 52461 := rs (se 3 (by rfl) ⟨9836, by rfl⟩) (B 19673 (by norm_num) ⟨9836, by rfl⟩ (by norm_num))
theorem R52465 : Reach 52465 := rs (se 2 (by rfl) ⟨19674, by rfl⟩) (B 39349 (by norm_num) ⟨19674, by rfl⟩ (by norm_num))
theorem R52469 : Reach 52469 := rs (se 5 (by rfl) ⟨2459, by rfl⟩) (B 4919 (by norm_num) ⟨2459, by rfl⟩ (by norm_num))
theorem R52473 : Reach 52473 := rs (se 2 (by rfl) ⟨19677, by rfl⟩) (B 39355 (by norm_num) ⟨19677, by rfl⟩ (by norm_num))
theorem R52477 : Reach 52477 := rs (se 3 (by rfl) ⟨9839, by rfl⟩) (B 19679 (by norm_num) ⟨9839, by rfl⟩ (by norm_num))
theorem R52481 : Reach 52481 := rs (se 2 (by rfl) ⟨19680, by rfl⟩) (B 39361 (by norm_num) ⟨19680, by rfl⟩ (by norm_num))
theorem R52485 : Reach 52485 := rs (se 4 (by rfl) ⟨4920, by rfl⟩) (B 9841 (by norm_num) ⟨4920, by rfl⟩ (by norm_num))
theorem R52489 : Reach 52489 := rs (se 2 (by rfl) ⟨19683, by rfl⟩) (B 39367 (by norm_num) ⟨19683, by rfl⟩ (by norm_num))
theorem R52493 : Reach 52493 := rs (se 3 (by rfl) ⟨9842, by rfl⟩) (B 19685 (by norm_num) ⟨9842, by rfl⟩ (by norm_num))
theorem R52497 : Reach 52497 := rs (se 2 (by rfl) ⟨19686, by rfl⟩) (B 39373 (by norm_num) ⟨19686, by rfl⟩ (by norm_num))
theorem R52501 : Reach 52501 := rs (se 6 (by rfl) ⟨1230, by rfl⟩) (B 2461 (by norm_num) ⟨1230, by rfl⟩ (by norm_num))
theorem R52505 : Reach 52505 := rs (se 2 (by rfl) ⟨19689, by rfl⟩) (B 39379 (by norm_num) ⟨19689, by rfl⟩ (by norm_num))
theorem R52509 : Reach 52509 := rs (se 3 (by rfl) ⟨9845, by rfl⟩) (B 19691 (by norm_num) ⟨9845, by rfl⟩ (by norm_num))
theorem R52513 : Reach 52513 := rs (se 2 (by rfl) ⟨19692, by rfl⟩) (B 39385 (by norm_num) ⟨19692, by rfl⟩ (by norm_num))
theorem R52517 : Reach 52517 := rs (se 4 (by rfl) ⟨4923, by rfl⟩) (B 9847 (by norm_num) ⟨4923, by rfl⟩ (by norm_num))
theorem R52521 : Reach 52521 := rs (se 2 (by rfl) ⟨19695, by rfl⟩) (B 39391 (by norm_num) ⟨19695, by rfl⟩ (by norm_num))
theorem R118061 : Reach 118061 := rs (se 3 (by rfl) ⟨22136, by rfl⟩) (B 44273 (by norm_num) ⟨22136, by rfl⟩ (by norm_num))
theorem R52525 : Reach 52525 := rs (se 3 (by rfl) ⟨9848, by rfl⟩) (B 19697 (by norm_num) ⟨9848, by rfl⟩ (by norm_num))
theorem R52529 : Reach 52529 := rs (se 2 (by rfl) ⟨19698, by rfl⟩) (B 39397 (by norm_num) ⟨19698, by rfl⟩ (by norm_num))
theorem R52533 : Reach 52533 := rs (se 5 (by rfl) ⟨2462, by rfl⟩) (B 4925 (by norm_num) ⟨2462, by rfl⟩ (by norm_num))
theorem R52537 : Reach 52537 := rs (se 2 (by rfl) ⟨19701, by rfl⟩) (B 39403 (by norm_num) ⟨19701, by rfl⟩ (by norm_num))
theorem R52541 : Reach 52541 := rs (se 3 (by rfl) ⟨9851, by rfl⟩) (B 19703 (by norm_num) ⟨9851, by rfl⟩ (by norm_num))
theorem R52545 : Reach 52545 := rs (se 2 (by rfl) ⟨19704, by rfl⟩) (B 39409 (by norm_num) ⟨19704, by rfl⟩ (by norm_num))
theorem R52549 : Reach 52549 := rs (se 4 (by rfl) ⟨4926, by rfl⟩) (B 9853 (by norm_num) ⟨4926, by rfl⟩ (by norm_num))
theorem R52553 : Reach 52553 := rs (se 2 (by rfl) ⟨19707, by rfl⟩) (B 39415 (by norm_num) ⟨19707, by rfl⟩ (by norm_num))
theorem R52557 : Reach 52557 := rs (se 3 (by rfl) ⟨9854, by rfl⟩) (B 19709 (by norm_num) ⟨9854, by rfl⟩ (by norm_num))
theorem R52561 : Reach 52561 := rs (se 2 (by rfl) ⟨19710, by rfl⟩) (B 39421 (by norm_num) ⟨19710, by rfl⟩ (by norm_num))
theorem R52565 : Reach 52565 := rs (se 11 (by rfl) ⟨38, by rfl⟩) (B 77 (by norm_num) ⟨38, by rfl⟩ (by norm_num))
theorem R52569 : Reach 52569 := rs (se 2 (by rfl) ⟨19713, by rfl⟩) (B 39427 (by norm_num) ⟨19713, by rfl⟩ (by norm_num))
theorem R52573 : Reach 52573 := rs (se 3 (by rfl) ⟨9857, by rfl⟩) (B 19715 (by norm_num) ⟨9857, by rfl⟩ (by norm_num))
theorem R52577 : Reach 52577 := rs (se 2 (by rfl) ⟨19716, by rfl⟩) (B 39433 (by norm_num) ⟨19716, by rfl⟩ (by norm_num))
theorem R52581 : Reach 52581 := rs (se 4 (by rfl) ⟨4929, by rfl⟩) (B 9859 (by norm_num) ⟨4929, by rfl⟩ (by norm_num))
theorem R183653 : Reach 183653 := rs (se 4 (by rfl) ⟨17217, by rfl⟩) (B 34435 (by norm_num) ⟨17217, by rfl⟩ (by norm_num))
theorem R52585 : Reach 52585 := rs (se 2 (by rfl) ⟨19719, by rfl⟩) (B 39439 (by norm_num) ⟨19719, by rfl⟩ (by norm_num))
theorem R52589 : Reach 52589 := rs (se 3 (by rfl) ⟨9860, by rfl⟩) (B 19721 (by norm_num) ⟨9860, by rfl⟩ (by norm_num))
theorem R52593 : Reach 52593 := rs (se 2 (by rfl) ⟨19722, by rfl⟩) (B 39445 (by norm_num) ⟨19722, by rfl⟩ (by norm_num))
theorem R118133 : Reach 118133 := rs (se 5 (by rfl) ⟨5537, by rfl⟩) (B 11075 (by norm_num) ⟨5537, by rfl⟩ (by norm_num))
theorem R52597 : Reach 52597 := rs (se 5 (by rfl) ⟨2465, by rfl⟩) (B 4931 (by norm_num) ⟨2465, by rfl⟩ (by norm_num))
theorem R52601 : Reach 52601 := rs (se 2 (by rfl) ⟨19725, by rfl⟩) (B 39451 (by norm_num) ⟨19725, by rfl⟩ (by norm_num))
theorem R52605 : Reach 52605 := rs (se 3 (by rfl) ⟨9863, by rfl⟩) (B 19727 (by norm_num) ⟨9863, by rfl⟩ (by norm_num))
theorem R52609 : Reach 52609 := rs (se 2 (by rfl) ⟨19728, by rfl⟩) (B 39457 (by norm_num) ⟨19728, by rfl⟩ (by norm_num))
theorem R52613 : Reach 52613 := rs (se 4 (by rfl) ⟨4932, by rfl⟩) (B 9865 (by norm_num) ⟨4932, by rfl⟩ (by norm_num))
theorem R52617 : Reach 52617 := rs (se 2 (by rfl) ⟨19731, by rfl⟩) (B 39463 (by norm_num) ⟨19731, by rfl⟩ (by norm_num))
theorem R52621 : Reach 52621 := rs (se 3 (by rfl) ⟨9866, by rfl⟩) (B 19733 (by norm_num) ⟨9866, by rfl⟩ (by norm_num))
theorem R52625 : Reach 52625 := rs (se 2 (by rfl) ⟨19734, by rfl⟩) (B 39469 (by norm_num) ⟨19734, by rfl⟩ (by norm_num))
theorem R52629 : Reach 52629 := rs (se 6 (by rfl) ⟨1233, by rfl⟩) (B 2467 (by norm_num) ⟨1233, by rfl⟩ (by norm_num))
theorem R52633 : Reach 52633 := rs (se 2 (by rfl) ⟨19737, by rfl⟩) (B 39475 (by norm_num) ⟨19737, by rfl⟩ (by norm_num))
theorem R52637 : Reach 52637 := rs (se 3 (by rfl) ⟨9869, by rfl⟩) (B 19739 (by norm_num) ⟨9869, by rfl⟩ (by norm_num))
theorem R52641 : Reach 52641 := rs (se 2 (by rfl) ⟨19740, by rfl⟩) (B 39481 (by norm_num) ⟨19740, by rfl⟩ (by norm_num))
theorem R52645 : Reach 52645 := rs (se 4 (by rfl) ⟨4935, by rfl⟩) (B 9871 (by norm_num) ⟨4935, by rfl⟩ (by norm_num))
theorem R52649 : Reach 52649 := rs (se 2 (by rfl) ⟨19743, by rfl⟩) (B 39487 (by norm_num) ⟨19743, by rfl⟩ (by norm_num))
theorem R52653 : Reach 52653 := rs (se 3 (by rfl) ⟨9872, by rfl⟩) (B 19745 (by norm_num) ⟨9872, by rfl⟩ (by norm_num))
theorem R52657 : Reach 52657 := rs (se 2 (by rfl) ⟨19746, by rfl⟩) (B 39493 (by norm_num) ⟨19746, by rfl⟩ (by norm_num))
theorem R52661 : Reach 52661 := rs (se 5 (by rfl) ⟨2468, by rfl⟩) (B 4937 (by norm_num) ⟨2468, by rfl⟩ (by norm_num))
theorem R52665 : Reach 52665 := rs (se 2 (by rfl) ⟨19749, by rfl⟩) (B 39499 (by norm_num) ⟨19749, by rfl⟩ (by norm_num))
theorem R118205 : Reach 118205 := rs (se 3 (by rfl) ⟨22163, by rfl⟩) (B 44327 (by norm_num) ⟨22163, by rfl⟩ (by norm_num))
theorem R52669 : Reach 52669 := rs (se 3 (by rfl) ⟨9875, by rfl⟩) (B 19751 (by norm_num) ⟨9875, by rfl⟩ (by norm_num))
theorem R52673 : Reach 52673 := rs (se 2 (by rfl) ⟨19752, by rfl⟩) (B 39505 (by norm_num) ⟨19752, by rfl⟩ (by norm_num))
theorem R52677 : Reach 52677 := rs (se 4 (by rfl) ⟨4938, by rfl⟩) (B 9877 (by norm_num) ⟨4938, by rfl⟩ (by norm_num))
theorem R52681 : Reach 52681 := rs (se 2 (by rfl) ⟨19755, by rfl⟩) (B 39511 (by norm_num) ⟨19755, by rfl⟩ (by norm_num))
theorem R52685 : Reach 52685 := rs (se 3 (by rfl) ⟨9878, by rfl⟩) (B 19757 (by norm_num) ⟨9878, by rfl⟩ (by norm_num))
theorem R52689 : Reach 52689 := rs (se 2 (by rfl) ⟨19758, by rfl⟩) (B 39517 (by norm_num) ⟨19758, by rfl⟩ (by norm_num))
theorem R52693 : Reach 52693 := rs (se 7 (by rfl) ⟨617, by rfl⟩) (B 1235 (by norm_num) ⟨617, by rfl⟩ (by norm_num))
theorem R52697 : Reach 52697 := rs (se 2 (by rfl) ⟨19761, by rfl⟩) (B 39523 (by norm_num) ⟨19761, by rfl⟩ (by norm_num))
theorem R52701 : Reach 52701 := rs (se 3 (by rfl) ⟨9881, by rfl⟩) (B 19763 (by norm_num) ⟨9881, by rfl⟩ (by norm_num))
theorem R52705 : Reach 52705 := rs (se 2 (by rfl) ⟨19764, by rfl⟩) (B 39529 (by norm_num) ⟨19764, by rfl⟩ (by norm_num))
theorem R52709 : Reach 52709 := rs (se 4 (by rfl) ⟨4941, by rfl⟩) (B 9883 (by norm_num) ⟨4941, by rfl⟩ (by norm_num))
theorem R52713 : Reach 52713 := rs (se 2 (by rfl) ⟨19767, by rfl⟩) (B 39535 (by norm_num) ⟨19767, by rfl⟩ (by norm_num))
theorem R52717 : Reach 52717 := rs (se 3 (by rfl) ⟨9884, by rfl⟩) (B 19769 (by norm_num) ⟨9884, by rfl⟩ (by norm_num))
theorem R52721 : Reach 52721 := rs (se 2 (by rfl) ⟨19770, by rfl⟩) (B 39541 (by norm_num) ⟨19770, by rfl⟩ (by norm_num))
theorem R52725 : Reach 52725 := rs (se 5 (by rfl) ⟨2471, by rfl⟩) (B 4943 (by norm_num) ⟨2471, by rfl⟩ (by norm_num))
theorem R52729 : Reach 52729 := rs (se 2 (by rfl) ⟨19773, by rfl⟩) (B 39547 (by norm_num) ⟨19773, by rfl⟩ (by norm_num))
theorem R52733 : Reach 52733 := rs (se 3 (by rfl) ⟨9887, by rfl⟩) (B 19775 (by norm_num) ⟨9887, by rfl⟩ (by norm_num))
theorem R52737 : Reach 52737 := rs (se 2 (by rfl) ⟨19776, by rfl⟩) (B 39553 (by norm_num) ⟨19776, by rfl⟩ (by norm_num))
theorem R118277 : Reach 118277 := rs (se 4 (by rfl) ⟨11088, by rfl⟩) (B 22177 (by norm_num) ⟨11088, by rfl⟩ (by norm_num))
theorem R52741 : Reach 52741 := rs (se 4 (by rfl) ⟨4944, by rfl⟩) (B 9889 (by norm_num) ⟨4944, by rfl⟩ (by norm_num))
theorem R52745 : Reach 52745 := rs (se 2 (by rfl) ⟨19779, by rfl⟩) (B 39559 (by norm_num) ⟨19779, by rfl⟩ (by norm_num))
theorem R52749 : Reach 52749 := rs (se 3 (by rfl) ⟨9890, by rfl⟩) (B 19781 (by norm_num) ⟨9890, by rfl⟩ (by norm_num))
theorem R52753 : Reach 52753 := rs (se 2 (by rfl) ⟨19782, by rfl⟩) (B 39565 (by norm_num) ⟨19782, by rfl⟩ (by norm_num))
theorem R52757 : Reach 52757 := rs (se 6 (by rfl) ⟨1236, by rfl⟩) (B 2473 (by norm_num) ⟨1236, by rfl⟩ (by norm_num))
theorem R52761 : Reach 52761 := rs (se 2 (by rfl) ⟨19785, by rfl⟩) (B 39571 (by norm_num) ⟨19785, by rfl⟩ (by norm_num))
theorem R52765 : Reach 52765 := rs (se 3 (by rfl) ⟨9893, by rfl⟩) (B 19787 (by norm_num) ⟨9893, by rfl⟩ (by norm_num))
theorem R52769 : Reach 52769 := rs (se 2 (by rfl) ⟨19788, by rfl⟩) (B 39577 (by norm_num) ⟨19788, by rfl⟩ (by norm_num))
theorem R52773 : Reach 52773 := rs (se 4 (by rfl) ⟨4947, by rfl⟩) (B 9895 (by norm_num) ⟨4947, by rfl⟩ (by norm_num))
theorem R52777 : Reach 52777 := rs (se 2 (by rfl) ⟨19791, by rfl⟩) (B 39583 (by norm_num) ⟨19791, by rfl⟩ (by norm_num))
theorem R52781 : Reach 52781 := rs (se 3 (by rfl) ⟨9896, by rfl⟩) (B 19793 (by norm_num) ⟨9896, by rfl⟩ (by norm_num))
theorem R52785 : Reach 52785 := rs (se 2 (by rfl) ⟨19794, by rfl⟩) (B 39589 (by norm_num) ⟨19794, by rfl⟩ (by norm_num))
theorem R52789 : Reach 52789 := rs (se 5 (by rfl) ⟨2474, by rfl⟩) (B 4949 (by norm_num) ⟨2474, by rfl⟩ (by norm_num))
theorem R52793 : Reach 52793 := rs (se 2 (by rfl) ⟨19797, by rfl⟩) (B 39595 (by norm_num) ⟨19797, by rfl⟩ (by norm_num))
theorem R52797 : Reach 52797 := rs (se 3 (by rfl) ⟨9899, by rfl⟩) (B 19799 (by norm_num) ⟨9899, by rfl⟩ (by norm_num))
theorem R52801 : Reach 52801 := rs (se 2 (by rfl) ⟨19800, by rfl⟩) (B 39601 (by norm_num) ⟨19800, by rfl⟩ (by norm_num))
theorem R52805 : Reach 52805 := rs (se 4 (by rfl) ⟨4950, by rfl⟩) (B 9901 (by norm_num) ⟨4950, by rfl⟩ (by norm_num))
theorem R151109 : Reach 151109 := rs (se 4 (by rfl) ⟨14166, by rfl⟩) (B 28333 (by norm_num) ⟨14166, by rfl⟩ (by norm_num))
theorem R52809 : Reach 52809 := rs (se 2 (by rfl) ⟨19803, by rfl⟩) (B 39607 (by norm_num) ⟨19803, by rfl⟩ (by norm_num))
theorem R118349 : Reach 118349 := rs (se 3 (by rfl) ⟨22190, by rfl⟩) (B 44381 (by norm_num) ⟨22190, by rfl⟩ (by norm_num))
theorem R52813 : Reach 52813 := rs (se 3 (by rfl) ⟨9902, by rfl⟩) (B 19805 (by norm_num) ⟨9902, by rfl⟩ (by norm_num))
theorem R52817 : Reach 52817 := rs (se 2 (by rfl) ⟨19806, by rfl⟩) (B 39613 (by norm_num) ⟨19806, by rfl⟩ (by norm_num))
theorem R52821 : Reach 52821 := rs (se 8 (by rfl) ⟨309, by rfl⟩) (B 619 (by norm_num) ⟨309, by rfl⟩ (by norm_num))
theorem R52825 : Reach 52825 := rs (se 2 (by rfl) ⟨19809, by rfl⟩) (B 39619 (by norm_num) ⟨19809, by rfl⟩ (by norm_num))
theorem R52829 : Reach 52829 := rs (se 3 (by rfl) ⟨9905, by rfl⟩) (B 19811 (by norm_num) ⟨9905, by rfl⟩ (by norm_num))
theorem R52833 : Reach 52833 := rs (se 2 (by rfl) ⟨19812, by rfl⟩) (B 39625 (by norm_num) ⟨19812, by rfl⟩ (by norm_num))
theorem R216677 : Reach 216677 := rs (se 4 (by rfl) ⟨20313, by rfl⟩) (B 40627 (by norm_num) ⟨20313, by rfl⟩ (by norm_num))
theorem R52837 : Reach 52837 := rs (se 4 (by rfl) ⟨4953, by rfl⟩) (B 9907 (by norm_num) ⟨4953, by rfl⟩ (by norm_num))
theorem R52841 : Reach 52841 := rs (se 2 (by rfl) ⟨19815, by rfl⟩) (B 39631 (by norm_num) ⟨19815, by rfl⟩ (by norm_num))
theorem R52845 : Reach 52845 := rs (se 3 (by rfl) ⟨9908, by rfl⟩) (B 19817 (by norm_num) ⟨9908, by rfl⟩ (by norm_num))
theorem R52849 : Reach 52849 := rs (se 2 (by rfl) ⟨19818, by rfl⟩) (B 39637 (by norm_num) ⟨19818, by rfl⟩ (by norm_num))
theorem R380533 : Reach 380533 := rs (se 5 (by rfl) ⟨17837, by rfl⟩) (B 35675 (by norm_num) ⟨17837, by rfl⟩ (by norm_num))
theorem R52853 : Reach 52853 := rs (se 5 (by rfl) ⟨2477, by rfl⟩) (B 4955 (by norm_num) ⟨2477, by rfl⟩ (by norm_num))
theorem R52857 : Reach 52857 := rs (se 2 (by rfl) ⟨19821, by rfl⟩) (B 39643 (by norm_num) ⟨19821, by rfl⟩ (by norm_num))
theorem R52861 : Reach 52861 := rs (se 3 (by rfl) ⟨9911, by rfl⟩) (B 19823 (by norm_num) ⟨9911, by rfl⟩ (by norm_num))
theorem R52865 : Reach 52865 := rs (se 2 (by rfl) ⟨19824, by rfl⟩) (B 39649 (by norm_num) ⟨19824, by rfl⟩ (by norm_num))
theorem R52869 : Reach 52869 := rs (se 4 (by rfl) ⟨4956, by rfl⟩) (B 9913 (by norm_num) ⟨4956, by rfl⟩ (by norm_num))
theorem R52873 : Reach 52873 := rs (se 2 (by rfl) ⟨19827, by rfl⟩) (B 39655 (by norm_num) ⟨19827, by rfl⟩ (by norm_num))
theorem R52877 : Reach 52877 := rs (se 3 (by rfl) ⟨9914, by rfl⟩) (B 19829 (by norm_num) ⟨9914, by rfl⟩ (by norm_num))
theorem R52881 : Reach 52881 := rs (se 2 (by rfl) ⟨19830, by rfl⟩) (B 39661 (by norm_num) ⟨19830, by rfl⟩ (by norm_num))
theorem R118421 : Reach 118421 := rs (se 6 (by rfl) ⟨2775, by rfl⟩) (B 5551 (by norm_num) ⟨2775, by rfl⟩ (by norm_num))
theorem R52885 : Reach 52885 := rs (se 6 (by rfl) ⟨1239, by rfl⟩) (B 2479 (by norm_num) ⟨1239, by rfl⟩ (by norm_num))
theorem R52889 : Reach 52889 := rs (se 2 (by rfl) ⟨19833, by rfl⟩) (B 39667 (by norm_num) ⟨19833, by rfl⟩ (by norm_num))
theorem R52893 : Reach 52893 := rs (se 3 (by rfl) ⟨9917, by rfl⟩) (B 19835 (by norm_num) ⟨9917, by rfl⟩ (by norm_num))
theorem R52897 : Reach 52897 := rs (se 2 (by rfl) ⟨19836, by rfl⟩) (B 39673 (by norm_num) ⟨19836, by rfl⟩ (by norm_num))
theorem R52901 : Reach 52901 := rs (se 4 (by rfl) ⟨4959, by rfl⟩) (B 9919 (by norm_num) ⟨4959, by rfl⟩ (by norm_num))
theorem R52905 : Reach 52905 := rs (se 2 (by rfl) ⟨19839, by rfl⟩) (B 39679 (by norm_num) ⟨19839, by rfl⟩ (by norm_num))
theorem R52909 : Reach 52909 := rs (se 3 (by rfl) ⟨9920, by rfl⟩) (B 19841 (by norm_num) ⟨9920, by rfl⟩ (by norm_num))
theorem R52913 : Reach 52913 := rs (se 2 (by rfl) ⟨19842, by rfl⟩) (B 39685 (by norm_num) ⟨19842, by rfl⟩ (by norm_num))
theorem R52917 : Reach 52917 := rs (se 5 (by rfl) ⟨2480, by rfl⟩) (B 4961 (by norm_num) ⟨2480, by rfl⟩ (by norm_num))
theorem R52921 : Reach 52921 := rs (se 2 (by rfl) ⟨19845, by rfl⟩) (B 39691 (by norm_num) ⟨19845, by rfl⟩ (by norm_num))
theorem R52925 : Reach 52925 := rs (se 3 (by rfl) ⟨9923, by rfl⟩) (B 19847 (by norm_num) ⟨9923, by rfl⟩ (by norm_num))
theorem R52929 : Reach 52929 := rs (se 2 (by rfl) ⟨19848, by rfl⟩) (B 39697 (by norm_num) ⟨19848, by rfl⟩ (by norm_num))
theorem R52933 : Reach 52933 := rs (se 4 (by rfl) ⟨4962, by rfl⟩) (B 9925 (by norm_num) ⟨4962, by rfl⟩ (by norm_num))
theorem R52937 : Reach 52937 := rs (se 2 (by rfl) ⟨19851, by rfl⟩) (B 39703 (by norm_num) ⟨19851, by rfl⟩ (by norm_num))
theorem R52941 : Reach 52941 := rs (se 3 (by rfl) ⟨9926, by rfl⟩) (B 19853 (by norm_num) ⟨9926, by rfl⟩ (by norm_num))
theorem R52945 : Reach 52945 := rs (se 2 (by rfl) ⟨19854, by rfl⟩) (B 39709 (by norm_num) ⟨19854, by rfl⟩ (by norm_num))
theorem R52949 : Reach 52949 := rs (se 7 (by rfl) ⟨620, by rfl⟩) (B 1241 (by norm_num) ⟨620, by rfl⟩ (by norm_num))
theorem R52953 : Reach 52953 := rs (se 2 (by rfl) ⟨19857, by rfl⟩) (B 39715 (by norm_num) ⟨19857, by rfl⟩ (by norm_num))
theorem R118493 : Reach 118493 := rs (se 3 (by rfl) ⟨22217, by rfl⟩) (B 44435 (by norm_num) ⟨22217, by rfl⟩ (by norm_num))
theorem R52957 : Reach 52957 := rs (se 3 (by rfl) ⟨9929, by rfl⟩) (B 19859 (by norm_num) ⟨9929, by rfl⟩ (by norm_num))
theorem R52961 : Reach 52961 := rs (se 2 (by rfl) ⟨19860, by rfl⟩) (B 39721 (by norm_num) ⟨19860, by rfl⟩ (by norm_num))
theorem R52965 : Reach 52965 := rs (se 4 (by rfl) ⟨4965, by rfl⟩) (B 9931 (by norm_num) ⟨4965, by rfl⟩ (by norm_num))
theorem R52969 : Reach 52969 := rs (se 2 (by rfl) ⟨19863, by rfl⟩) (B 39727 (by norm_num) ⟨19863, by rfl⟩ (by norm_num))
theorem R52973 : Reach 52973 := rs (se 3 (by rfl) ⟨9932, by rfl⟩) (B 19865 (by norm_num) ⟨9932, by rfl⟩ (by norm_num))
theorem R52977 : Reach 52977 := rs (se 2 (by rfl) ⟨19866, by rfl⟩) (B 39733 (by norm_num) ⟨19866, by rfl⟩ (by norm_num))
theorem R52981 : Reach 52981 := rs (se 5 (by rfl) ⟨2483, by rfl⟩) (B 4967 (by norm_num) ⟨2483, by rfl⟩ (by norm_num))
theorem R52985 : Reach 52985 := rs (se 2 (by rfl) ⟨19869, by rfl⟩) (B 39739 (by norm_num) ⟨19869, by rfl⟩ (by norm_num))
theorem R52989 : Reach 52989 := rs (se 3 (by rfl) ⟨9935, by rfl⟩) (B 19871 (by norm_num) ⟨9935, by rfl⟩ (by norm_num))
theorem R52993 : Reach 52993 := rs (se 2 (by rfl) ⟨19872, by rfl⟩) (B 39745 (by norm_num) ⟨19872, by rfl⟩ (by norm_num))
theorem R52997 : Reach 52997 := rs (se 4 (by rfl) ⟨4968, by rfl⟩) (B 9937 (by norm_num) ⟨4968, by rfl⟩ (by norm_num))
theorem R53001 : Reach 53001 := rs (se 2 (by rfl) ⟨19875, by rfl⟩) (B 39751 (by norm_num) ⟨19875, by rfl⟩ (by norm_num))
theorem R53005 : Reach 53005 := rs (se 3 (by rfl) ⟨9938, by rfl⟩) (B 19877 (by norm_num) ⟨9938, by rfl⟩ (by norm_num))
theorem R53009 : Reach 53009 := rs (se 2 (by rfl) ⟨19878, by rfl⟩) (B 39757 (by norm_num) ⟨19878, by rfl⟩ (by norm_num))
theorem R53013 : Reach 53013 := rs (se 6 (by rfl) ⟨1242, by rfl⟩) (B 2485 (by norm_num) ⟨1242, by rfl⟩ (by norm_num))
theorem R85781 : Reach 85781 := rs (se 6 (by rfl) ⟨2010, by rfl⟩) (B 4021 (by norm_num) ⟨2010, by rfl⟩ (by norm_num))
theorem R184085 : Reach 184085 := rs (se 6 (by rfl) ⟨4314, by rfl⟩) (B 8629 (by norm_num) ⟨4314, by rfl⟩ (by norm_num))
theorem R53017 : Reach 53017 := rs (se 2 (by rfl) ⟨19881, by rfl⟩) (B 39763 (by norm_num) ⟨19881, by rfl⟩ (by norm_num))
theorem R53021 : Reach 53021 := rs (se 3 (by rfl) ⟨9941, by rfl⟩) (B 19883 (by norm_num) ⟨9941, by rfl⟩ (by norm_num))
theorem R53025 : Reach 53025 := rs (se 2 (by rfl) ⟨19884, by rfl⟩) (B 39769 (by norm_num) ⟨19884, by rfl⟩ (by norm_num))
theorem R118565 : Reach 118565 := rs (se 4 (by rfl) ⟨11115, by rfl⟩) (B 22231 (by norm_num) ⟨11115, by rfl⟩ (by norm_num))
theorem R53029 : Reach 53029 := rs (se 4 (by rfl) ⟨4971, by rfl⟩) (B 9943 (by norm_num) ⟨4971, by rfl⟩ (by norm_num))
theorem R53033 : Reach 53033 := rs (se 2 (by rfl) ⟨19887, by rfl⟩) (B 39775 (by norm_num) ⟨19887, by rfl⟩ (by norm_num))
theorem R53037 : Reach 53037 := rs (se 3 (by rfl) ⟨9944, by rfl⟩) (B 19889 (by norm_num) ⟨9944, by rfl⟩ (by norm_num))
theorem R53041 : Reach 53041 := rs (se 2 (by rfl) ⟨19890, by rfl⟩) (B 39781 (by norm_num) ⟨19890, by rfl⟩ (by norm_num))
theorem R53045 : Reach 53045 := rs (se 5 (by rfl) ⟨2486, by rfl⟩) (B 4973 (by norm_num) ⟨2486, by rfl⟩ (by norm_num))
theorem R53049 : Reach 53049 := rs (se 2 (by rfl) ⟨19893, by rfl⟩) (B 39787 (by norm_num) ⟨19893, by rfl⟩ (by norm_num))
theorem R53053 : Reach 53053 := rs (se 3 (by rfl) ⟨9947, by rfl⟩) (B 19895 (by norm_num) ⟨9947, by rfl⟩ (by norm_num))
theorem R53057 : Reach 53057 := rs (se 2 (by rfl) ⟨19896, by rfl⟩) (B 39793 (by norm_num) ⟨19896, by rfl⟩ (by norm_num))
theorem R53061 : Reach 53061 := rs (se 4 (by rfl) ⟨4974, by rfl⟩) (B 9949 (by norm_num) ⟨4974, by rfl⟩ (by norm_num))
theorem R53065 : Reach 53065 := rs (se 2 (by rfl) ⟨19899, by rfl⟩) (B 39799 (by norm_num) ⟨19899, by rfl⟩ (by norm_num))
theorem R53069 : Reach 53069 := rs (se 3 (by rfl) ⟨9950, by rfl⟩) (B 19901 (by norm_num) ⟨9950, by rfl⟩ (by norm_num))
theorem R53073 : Reach 53073 := rs (se 2 (by rfl) ⟨19902, by rfl⟩) (B 39805 (by norm_num) ⟨19902, by rfl⟩ (by norm_num))
theorem R53077 : Reach 53077 := rs (se 9 (by rfl) ⟨155, by rfl⟩) (B 311 (by norm_num) ⟨155, by rfl⟩ (by norm_num))
theorem R5820245 : Reach 5820245 := rs (se 9 (by rfl) ⟨17051, by rfl⟩) (B 34103 (by norm_num) ⟨17051, by rfl⟩ (by norm_num))
theorem R53081 : Reach 53081 := rs (se 2 (by rfl) ⟨19905, by rfl⟩) (B 39811 (by norm_num) ⟨19905, by rfl⟩ (by norm_num))
theorem R53085 : Reach 53085 := rs (se 3 (by rfl) ⟨9953, by rfl⟩) (B 19907 (by norm_num) ⟨9953, by rfl⟩ (by norm_num))
theorem R53089 : Reach 53089 := rs (se 2 (by rfl) ⟨19908, by rfl⟩) (B 39817 (by norm_num) ⟨19908, by rfl⟩ (by norm_num))
theorem R53093 : Reach 53093 := rs (se 4 (by rfl) ⟨4977, by rfl⟩) (B 9955 (by norm_num) ⟨4977, by rfl⟩ (by norm_num))
theorem R53097 : Reach 53097 := rs (se 2 (by rfl) ⟨19911, by rfl⟩) (B 39823 (by norm_num) ⟨19911, by rfl⟩ (by norm_num))
theorem R118637 : Reach 118637 := rs (se 3 (by rfl) ⟨22244, by rfl⟩) (B 44489 (by norm_num) ⟨22244, by rfl⟩ (by norm_num))
theorem R53101 : Reach 53101 := rs (se 3 (by rfl) ⟨9956, by rfl⟩) (B 19913 (by norm_num) ⟨9956, by rfl⟩ (by norm_num))
theorem R53105 : Reach 53105 := rs (se 2 (by rfl) ⟨19914, by rfl⟩) (B 39829 (by norm_num) ⟨19914, by rfl⟩ (by norm_num))
theorem R53109 : Reach 53109 := rs (se 5 (by rfl) ⟨2489, by rfl⟩) (B 4979 (by norm_num) ⟨2489, by rfl⟩ (by norm_num))
theorem R53113 : Reach 53113 := rs (se 2 (by rfl) ⟨19917, by rfl⟩) (B 39835 (by norm_num) ⟨19917, by rfl⟩ (by norm_num))
theorem R53117 : Reach 53117 := rs (se 3 (by rfl) ⟨9959, by rfl⟩) (B 19919 (by norm_num) ⟨9959, by rfl⟩ (by norm_num))
theorem R53121 : Reach 53121 := rs (se 2 (by rfl) ⟨19920, by rfl⟩) (B 39841 (by norm_num) ⟨19920, by rfl⟩ (by norm_num))
theorem R53125 : Reach 53125 := rs (se 4 (by rfl) ⟨4980, by rfl⟩) (B 9961 (by norm_num) ⟨4980, by rfl⟩ (by norm_num))
theorem R53129 : Reach 53129 := rs (se 2 (by rfl) ⟨19923, by rfl⟩) (B 39847 (by norm_num) ⟨19923, by rfl⟩ (by norm_num))
theorem R53133 : Reach 53133 := rs (se 3 (by rfl) ⟨9962, by rfl⟩) (B 19925 (by norm_num) ⟨9962, by rfl⟩ (by norm_num))
theorem R53137 : Reach 53137 := rs (se 2 (by rfl) ⟨19926, by rfl⟩) (B 39853 (by norm_num) ⟨19926, by rfl⟩ (by norm_num))
theorem R53141 : Reach 53141 := rs (se 6 (by rfl) ⟨1245, by rfl⟩) (B 2491 (by norm_num) ⟨1245, by rfl⟩ (by norm_num))
theorem R53145 : Reach 53145 := rs (se 2 (by rfl) ⟨19929, by rfl⟩) (B 39859 (by norm_num) ⟨19929, by rfl⟩ (by norm_num))
theorem R53149 : Reach 53149 := rs (se 3 (by rfl) ⟨9965, by rfl⟩) (B 19931 (by norm_num) ⟨9965, by rfl⟩ (by norm_num))
theorem R53153 : Reach 53153 := rs (se 2 (by rfl) ⟨19932, by rfl⟩) (B 39865 (by norm_num) ⟨19932, by rfl⟩ (by norm_num))
theorem R53157 : Reach 53157 := rs (se 4 (by rfl) ⟨4983, by rfl⟩) (B 9967 (by norm_num) ⟨4983, by rfl⟩ (by norm_num))
theorem R53161 : Reach 53161 := rs (se 2 (by rfl) ⟨19935, by rfl⟩) (B 39871 (by norm_num) ⟨19935, by rfl⟩ (by norm_num))
theorem R53165 : Reach 53165 := rs (se 3 (by rfl) ⟨9968, by rfl⟩) (B 19937 (by norm_num) ⟨9968, by rfl⟩ (by norm_num))
theorem R53169 : Reach 53169 := rs (se 2 (by rfl) ⟨19938, by rfl⟩) (B 39877 (by norm_num) ⟨19938, by rfl⟩ (by norm_num))
theorem R53173 : Reach 53173 := rs (se 5 (by rfl) ⟨2492, by rfl⟩) (B 4985 (by norm_num) ⟨2492, by rfl⟩ (by norm_num))
theorem R118709 : Reach 118709 := rs (se 5 (by rfl) ⟨5564, by rfl⟩) (B 11129 (by norm_num) ⟨5564, by rfl⟩ (by norm_num))
theorem R53177 : Reach 53177 := rs (se 2 (by rfl) ⟨19941, by rfl⟩) (B 39883 (by norm_num) ⟨19941, by rfl⟩ (by norm_num))
theorem R53181 : Reach 53181 := rs (se 3 (by rfl) ⟨9971, by rfl⟩) (B 19943 (by norm_num) ⟨9971, by rfl⟩ (by norm_num))
theorem R53185 : Reach 53185 := rs (se 2 (by rfl) ⟨19944, by rfl⟩) (B 39889 (by norm_num) ⟨19944, by rfl⟩ (by norm_num))
theorem R53189 : Reach 53189 := rs (se 4 (by rfl) ⟨4986, by rfl⟩) (B 9973 (by norm_num) ⟨4986, by rfl⟩ (by norm_num))
theorem R53193 : Reach 53193 := rs (se 2 (by rfl) ⟨19947, by rfl⟩) (B 39895 (by norm_num) ⟨19947, by rfl⟩ (by norm_num))
theorem R53197 : Reach 53197 := rs (se 3 (by rfl) ⟨9974, by rfl⟩) (B 19949 (by norm_num) ⟨9974, by rfl⟩ (by norm_num))
theorem R53201 : Reach 53201 := rs (se 2 (by rfl) ⟨19950, by rfl⟩) (B 39901 (by norm_num) ⟨19950, by rfl⟩ (by norm_num))
theorem R53205 : Reach 53205 := rs (se 7 (by rfl) ⟨623, by rfl⟩) (B 1247 (by norm_num) ⟨623, by rfl⟩ (by norm_num))
theorem R53209 : Reach 53209 := rs (se 2 (by rfl) ⟨19953, by rfl⟩) (B 39907 (by norm_num) ⟨19953, by rfl⟩ (by norm_num))
theorem R53213 : Reach 53213 := rs (se 3 (by rfl) ⟨9977, by rfl⟩) (B 19955 (by norm_num) ⟨9977, by rfl⟩ (by norm_num))
theorem R53217 : Reach 53217 := rs (se 2 (by rfl) ⟨19956, by rfl⟩) (B 39913 (by norm_num) ⟨19956, by rfl⟩ (by norm_num))
theorem R53221 : Reach 53221 := rs (se 4 (by rfl) ⟨4989, by rfl⟩) (B 9979 (by norm_num) ⟨4989, by rfl⟩ (by norm_num))
theorem R53225 : Reach 53225 := rs (se 2 (by rfl) ⟨19959, by rfl⟩) (B 39919 (by norm_num) ⟨19959, by rfl⟩ (by norm_num))
theorem R53229 : Reach 53229 := rs (se 3 (by rfl) ⟨9980, by rfl⟩) (B 19961 (by norm_num) ⟨9980, by rfl⟩ (by norm_num))
theorem R53233 : Reach 53233 := rs (se 2 (by rfl) ⟨19962, by rfl⟩) (B 39925 (by norm_num) ⟨19962, by rfl⟩ (by norm_num))
theorem R151541 : Reach 151541 := rs (se 5 (by rfl) ⟨7103, by rfl⟩) (B 14207 (by norm_num) ⟨7103, by rfl⟩ (by norm_num))
theorem R53237 : Reach 53237 := rs (se 5 (by rfl) ⟨2495, by rfl⟩) (B 4991 (by norm_num) ⟨2495, by rfl⟩ (by norm_num))
theorem R53241 : Reach 53241 := rs (se 2 (by rfl) ⟨19965, by rfl⟩) (B 39931 (by norm_num) ⟨19965, by rfl⟩ (by norm_num))
theorem R118781 : Reach 118781 := rs (se 3 (by rfl) ⟨22271, by rfl⟩) (B 44543 (by norm_num) ⟨22271, by rfl⟩ (by norm_num))
theorem R53245 : Reach 53245 := rs (se 3 (by rfl) ⟨9983, by rfl⟩) (B 19967 (by norm_num) ⟨9983, by rfl⟩ (by norm_num))
theorem R53249 : Reach 53249 := rs (se 2 (by rfl) ⟨19968, by rfl⟩) (B 39937 (by norm_num) ⟨19968, by rfl⟩ (by norm_num))
theorem R53253 : Reach 53253 := rs (se 4 (by rfl) ⟨4992, by rfl⟩) (B 9985 (by norm_num) ⟨4992, by rfl⟩ (by norm_num))
theorem R53257 : Reach 53257 := rs (se 2 (by rfl) ⟨19971, by rfl⟩) (B 39943 (by norm_num) ⟨19971, by rfl⟩ (by norm_num))
theorem R53261 : Reach 53261 := rs (se 3 (by rfl) ⟨9986, by rfl⟩) (B 19973 (by norm_num) ⟨9986, by rfl⟩ (by norm_num))
theorem R53265 : Reach 53265 := rs (se 2 (by rfl) ⟨19974, by rfl⟩) (B 39949 (by norm_num) ⟨19974, by rfl⟩ (by norm_num))
theorem R53269 : Reach 53269 := rs (se 6 (by rfl) ⟨1248, by rfl⟩) (B 2497 (by norm_num) ⟨1248, by rfl⟩ (by norm_num))
theorem R53273 : Reach 53273 := rs (se 2 (by rfl) ⟨19977, by rfl⟩) (B 39955 (by norm_num) ⟨19977, by rfl⟩ (by norm_num))
theorem R53277 : Reach 53277 := rs (se 3 (by rfl) ⟨9989, by rfl⟩) (B 19979 (by norm_num) ⟨9989, by rfl⟩ (by norm_num))
theorem R53281 : Reach 53281 := rs (se 2 (by rfl) ⟨19980, by rfl⟩) (B 39961 (by norm_num) ⟨19980, by rfl⟩ (by norm_num))
theorem R53285 : Reach 53285 := rs (se 4 (by rfl) ⟨4995, by rfl⟩) (B 9991 (by norm_num) ⟨4995, by rfl⟩ (by norm_num))
theorem R53289 : Reach 53289 := rs (se 2 (by rfl) ⟨19983, by rfl⟩) (B 39967 (by norm_num) ⟨19983, by rfl⟩ (by norm_num))
theorem R53293 : Reach 53293 := rs (se 3 (by rfl) ⟨9992, by rfl⟩) (B 19985 (by norm_num) ⟨9992, by rfl⟩ (by norm_num))
theorem R53297 : Reach 53297 := rs (se 2 (by rfl) ⟨19986, by rfl⟩) (B 39973 (by norm_num) ⟨19986, by rfl⟩ (by norm_num))
theorem R53301 : Reach 53301 := rs (se 5 (by rfl) ⟨2498, by rfl⟩) (B 4997 (by norm_num) ⟨2498, by rfl⟩ (by norm_num))
theorem R53305 : Reach 53305 := rs (se 2 (by rfl) ⟨19989, by rfl⟩) (B 39979 (by norm_num) ⟨19989, by rfl⟩ (by norm_num))
theorem R53309 : Reach 53309 := rs (se 3 (by rfl) ⟨9995, by rfl⟩) (B 19991 (by norm_num) ⟨9995, by rfl⟩ (by norm_num))
theorem R53313 : Reach 53313 := rs (se 2 (by rfl) ⟨19992, by rfl⟩) (B 39985 (by norm_num) ⟨19992, by rfl⟩ (by norm_num))
theorem R118853 : Reach 118853 := rs (se 4 (by rfl) ⟨11142, by rfl⟩) (B 22285 (by norm_num) ⟨11142, by rfl⟩ (by norm_num))
theorem R53317 : Reach 53317 := rs (se 4 (by rfl) ⟨4998, by rfl⟩) (B 9997 (by norm_num) ⟨4998, by rfl⟩ (by norm_num))
theorem R53321 : Reach 53321 := rs (se 2 (by rfl) ⟨19995, by rfl⟩) (B 39991 (by norm_num) ⟨19995, by rfl⟩ (by norm_num))
theorem R53325 : Reach 53325 := rs (se 3 (by rfl) ⟨9998, by rfl⟩) (B 19997 (by norm_num) ⟨9998, by rfl⟩ (by norm_num))
theorem R53329 : Reach 53329 := rs (se 2 (by rfl) ⟨19998, by rfl⟩) (B 39997 (by norm_num) ⟨19998, by rfl⟩ (by norm_num))
theorem R1527893 : Reach 1527893 := rs (se 8 (by rfl) ⟨8952, by rfl⟩) (B 17905 (by norm_num) ⟨8952, by rfl⟩ (by norm_num))
theorem R53333 : Reach 53333 := rs (se 8 (by rfl) ⟨312, by rfl⟩) (B 625 (by norm_num) ⟨312, by rfl⟩ (by norm_num))
theorem R53337 : Reach 53337 := rs (se 2 (by rfl) ⟨20001, by rfl⟩) (B 40003 (by norm_num) ⟨20001, by rfl⟩ (by norm_num))
theorem R53341 : Reach 53341 := rs (se 3 (by rfl) ⟨10001, by rfl⟩) (B 20003 (by norm_num) ⟨10001, by rfl⟩ (by norm_num))
theorem R53345 : Reach 53345 := rs (se 2 (by rfl) ⟨20004, by rfl⟩) (B 40009 (by norm_num) ⟨20004, by rfl⟩ (by norm_num))
theorem R53349 : Reach 53349 := rs (se 4 (by rfl) ⟨5001, by rfl⟩) (B 10003 (by norm_num) ⟨5001, by rfl⟩ (by norm_num))
theorem R53353 : Reach 53353 := rs (se 2 (by rfl) ⟨20007, by rfl⟩) (B 40015 (by norm_num) ⟨20007, by rfl⟩ (by norm_num))
theorem R53357 : Reach 53357 := rs (se 3 (by rfl) ⟨10004, by rfl⟩) (B 20009 (by norm_num) ⟨10004, by rfl⟩ (by norm_num))
theorem R53361 : Reach 53361 := rs (se 2 (by rfl) ⟨20010, by rfl⟩) (B 40021 (by norm_num) ⟨20010, by rfl⟩ (by norm_num))
theorem R53365 : Reach 53365 := rs (se 5 (by rfl) ⟨2501, by rfl⟩) (B 5003 (by norm_num) ⟨2501, by rfl⟩ (by norm_num))
theorem R53369 : Reach 53369 := rs (se 2 (by rfl) ⟨20013, by rfl⟩) (B 40027 (by norm_num) ⟨20013, by rfl⟩ (by norm_num))
theorem R53373 : Reach 53373 := rs (se 3 (by rfl) ⟨10007, by rfl⟩) (B 20015 (by norm_num) ⟨10007, by rfl⟩ (by norm_num))
theorem R53377 : Reach 53377 := rs (se 2 (by rfl) ⟨20016, by rfl⟩) (B 40033 (by norm_num) ⟨20016, by rfl⟩ (by norm_num))
theorem R53381 : Reach 53381 := rs (se 4 (by rfl) ⟨5004, by rfl⟩) (B 10009 (by norm_num) ⟨5004, by rfl⟩ (by norm_num))
theorem R53385 : Reach 53385 := rs (se 2 (by rfl) ⟨20019, by rfl⟩) (B 40039 (by norm_num) ⟨20019, by rfl⟩ (by norm_num))
theorem R118925 : Reach 118925 := rs (se 3 (by rfl) ⟨22298, by rfl⟩) (B 44597 (by norm_num) ⟨22298, by rfl⟩ (by norm_num))
theorem R53389 : Reach 53389 := rs (se 3 (by rfl) ⟨10010, by rfl⟩) (B 20021 (by norm_num) ⟨10010, by rfl⟩ (by norm_num))
theorem R53393 : Reach 53393 := rs (se 2 (by rfl) ⟨20022, by rfl⟩) (B 40045 (by norm_num) ⟨20022, by rfl⟩ (by norm_num))
theorem R53397 : Reach 53397 := rs (se 6 (by rfl) ⟨1251, by rfl⟩) (B 2503 (by norm_num) ⟨1251, by rfl⟩ (by norm_num))
theorem R86165 : Reach 86165 := rs (se 6 (by rfl) ⟨2019, by rfl⟩) (B 4039 (by norm_num) ⟨2019, by rfl⟩ (by norm_num))
theorem R53401 : Reach 53401 := rs (se 2 (by rfl) ⟨20025, by rfl⟩) (B 40051 (by norm_num) ⟨20025, by rfl⟩ (by norm_num))
theorem R53405 : Reach 53405 := rs (se 3 (by rfl) ⟨10013, by rfl⟩) (B 20027 (by norm_num) ⟨10013, by rfl⟩ (by norm_num))
theorem R53409 : Reach 53409 := rs (se 2 (by rfl) ⟨20028, by rfl⟩) (B 40057 (by norm_num) ⟨20028, by rfl⟩ (by norm_num))
theorem R53413 : Reach 53413 := rs (se 4 (by rfl) ⟨5007, by rfl⟩) (B 10015 (by norm_num) ⟨5007, by rfl⟩ (by norm_num))
theorem R53417 : Reach 53417 := rs (se 2 (by rfl) ⟨20031, by rfl⟩) (B 40063 (by norm_num) ⟨20031, by rfl⟩ (by norm_num))
theorem R53421 : Reach 53421 := rs (se 3 (by rfl) ⟨10016, by rfl⟩) (B 20033 (by norm_num) ⟨10016, by rfl⟩ (by norm_num))
theorem R53425 : Reach 53425 := rs (se 2 (by rfl) ⟨20034, by rfl⟩) (B 40069 (by norm_num) ⟨20034, by rfl⟩ (by norm_num))
theorem R250037 : Reach 250037 := rs (se 5 (by rfl) ⟨11720, by rfl⟩) (B 23441 (by norm_num) ⟨11720, by rfl⟩ (by norm_num))
theorem R53429 : Reach 53429 := rs (se 5 (by rfl) ⟨2504, by rfl⟩) (B 5009 (by norm_num) ⟨2504, by rfl⟩ (by norm_num))
theorem R53433 : Reach 53433 := rs (se 2 (by rfl) ⟨20037, by rfl⟩) (B 40075 (by norm_num) ⟨20037, by rfl⟩ (by norm_num))
theorem R53437 : Reach 53437 := rs (se 3 (by rfl) ⟨10019, by rfl⟩) (B 20039 (by norm_num) ⟨10019, by rfl⟩ (by norm_num))
theorem R53441 : Reach 53441 := rs (se 2 (by rfl) ⟨20040, by rfl⟩) (B 40081 (by norm_num) ⟨20040, by rfl⟩ (by norm_num))
theorem R53445 : Reach 53445 := rs (se 4 (by rfl) ⟨5010, by rfl⟩) (B 10021 (by norm_num) ⟨5010, by rfl⟩ (by norm_num))
theorem R184517 : Reach 184517 := rs (se 4 (by rfl) ⟨17298, by rfl⟩) (B 34597 (by norm_num) ⟨17298, by rfl⟩ (by norm_num))
theorem R53449 : Reach 53449 := rs (se 2 (by rfl) ⟨20043, by rfl⟩) (B 40087 (by norm_num) ⟨20043, by rfl⟩ (by norm_num))
theorem R53453 : Reach 53453 := rs (se 3 (by rfl) ⟨10022, by rfl⟩) (B 20045 (by norm_num) ⟨10022, by rfl⟩ (by norm_num))
theorem R53457 : Reach 53457 := rs (se 2 (by rfl) ⟨20046, by rfl⟩) (B 40093 (by norm_num) ⟨20046, by rfl⟩ (by norm_num))
theorem R118997 : Reach 118997 := rs (se 7 (by rfl) ⟨1394, by rfl⟩) (B 2789 (by norm_num) ⟨1394, by rfl⟩ (by norm_num))
theorem R53461 : Reach 53461 := rs (se 7 (by rfl) ⟨626, by rfl⟩) (B 1253 (by norm_num) ⟨626, by rfl⟩ (by norm_num))
theorem R53465 : Reach 53465 := rs (se 2 (by rfl) ⟨20049, by rfl⟩) (B 40099 (by norm_num) ⟨20049, by rfl⟩ (by norm_num))
theorem R53469 : Reach 53469 := rs (se 3 (by rfl) ⟨10025, by rfl⟩) (B 20051 (by norm_num) ⟨10025, by rfl⟩ (by norm_num))
theorem R53473 : Reach 53473 := rs (se 2 (by rfl) ⟨20052, by rfl⟩) (B 40105 (by norm_num) ⟨20052, by rfl⟩ (by norm_num))
theorem R53477 : Reach 53477 := rs (se 4 (by rfl) ⟨5013, by rfl⟩) (B 10027 (by norm_num) ⟨5013, by rfl⟩ (by norm_num))
theorem R53481 : Reach 53481 := rs (se 2 (by rfl) ⟨20055, by rfl⟩) (B 40111 (by norm_num) ⟨20055, by rfl⟩ (by norm_num))
theorem R53485 : Reach 53485 := rs (se 3 (by rfl) ⟨10028, by rfl⟩) (B 20057 (by norm_num) ⟨10028, by rfl⟩ (by norm_num))
theorem R53489 : Reach 53489 := rs (se 2 (by rfl) ⟨20058, by rfl⟩) (B 40117 (by norm_num) ⟨20058, by rfl⟩ (by norm_num))
theorem R53493 : Reach 53493 := rs (se 5 (by rfl) ⟨2507, by rfl⟩) (B 5015 (by norm_num) ⟨2507, by rfl⟩ (by norm_num))
theorem R53497 : Reach 53497 := rs (se 2 (by rfl) ⟨20061, by rfl⟩) (B 40123 (by norm_num) ⟨20061, by rfl⟩ (by norm_num))
theorem R53501 : Reach 53501 := rs (se 3 (by rfl) ⟨10031, by rfl⟩) (B 20063 (by norm_num) ⟨10031, by rfl⟩ (by norm_num))
theorem R53505 : Reach 53505 := rs (se 2 (by rfl) ⟨20064, by rfl⟩) (B 40129 (by norm_num) ⟨20064, by rfl⟩ (by norm_num))
theorem R53509 : Reach 53509 := rs (se 4 (by rfl) ⟨5016, by rfl⟩) (B 10033 (by norm_num) ⟨5016, by rfl⟩ (by norm_num))
theorem R53513 : Reach 53513 := rs (se 2 (by rfl) ⟨20067, by rfl⟩) (B 40135 (by norm_num) ⟨20067, by rfl⟩ (by norm_num))
theorem R86285 : Reach 86285 := rs (se 3 (by rfl) ⟨16178, by rfl⟩) (B 32357 (by norm_num) ⟨16178, by rfl⟩ (by norm_num))
theorem R53517 : Reach 53517 := rs (se 3 (by rfl) ⟨10034, by rfl⟩) (B 20069 (by norm_num) ⟨10034, by rfl⟩ (by norm_num))
theorem R53521 : Reach 53521 := rs (se 2 (by rfl) ⟨20070, by rfl⟩) (B 40141 (by norm_num) ⟨20070, by rfl⟩ (by norm_num))
theorem R53525 : Reach 53525 := rs (se 6 (by rfl) ⟨1254, by rfl⟩) (B 2509 (by norm_num) ⟨1254, by rfl⟩ (by norm_num))
theorem R86293 : Reach 86293 := rs (se 6 (by rfl) ⟨2022, by rfl⟩) (B 4045 (by norm_num) ⟨2022, by rfl⟩ (by norm_num))
theorem R53529 : Reach 53529 := rs (se 2 (by rfl) ⟨20073, by rfl⟩) (B 40147 (by norm_num) ⟨20073, by rfl⟩ (by norm_num))
theorem R119069 : Reach 119069 := rs (se 3 (by rfl) ⟨22325, by rfl⟩) (B 44651 (by norm_num) ⟨22325, by rfl⟩ (by norm_num))
theorem R53533 : Reach 53533 := rs (se 3 (by rfl) ⟨10037, by rfl⟩) (B 20075 (by norm_num) ⟨10037, by rfl⟩ (by norm_num))
theorem R53537 : Reach 53537 := rs (se 2 (by rfl) ⟨20076, by rfl⟩) (B 40153 (by norm_num) ⟨20076, by rfl⟩ (by norm_num))
theorem R53541 : Reach 53541 := rs (se 4 (by rfl) ⟨5019, by rfl⟩) (B 10039 (by norm_num) ⟨5019, by rfl⟩ (by norm_num))
theorem R53545 : Reach 53545 := rs (se 2 (by rfl) ⟨20079, by rfl⟩) (B 40159 (by norm_num) ⟨20079, by rfl⟩ (by norm_num))
theorem R53549 : Reach 53549 := rs (se 3 (by rfl) ⟨10040, by rfl⟩) (B 20081 (by norm_num) ⟨10040, by rfl⟩ (by norm_num))
theorem R53553 : Reach 53553 := rs (se 2 (by rfl) ⟨20082, by rfl⟩) (B 40165 (by norm_num) ⟨20082, by rfl⟩ (by norm_num))
theorem R53557 : Reach 53557 := rs (se 5 (by rfl) ⟨2510, by rfl⟩) (B 5021 (by norm_num) ⟨2510, by rfl⟩ (by norm_num))
theorem R53561 : Reach 53561 := rs (se 2 (by rfl) ⟨20085, by rfl⟩) (B 40171 (by norm_num) ⟨20085, by rfl⟩ (by norm_num))
theorem R53565 : Reach 53565 := rs (se 3 (by rfl) ⟨10043, by rfl⟩) (B 20087 (by norm_num) ⟨10043, by rfl⟩ (by norm_num))
theorem R53569 : Reach 53569 := rs (se 2 (by rfl) ⟨20088, by rfl⟩) (B 40177 (by norm_num) ⟨20088, by rfl⟩ (by norm_num))
theorem R53573 : Reach 53573 := rs (se 4 (by rfl) ⟨5022, by rfl⟩) (B 10045 (by norm_num) ⟨5022, by rfl⟩ (by norm_num))
theorem R53577 : Reach 53577 := rs (se 2 (by rfl) ⟨20091, by rfl⟩) (B 40183 (by norm_num) ⟨20091, by rfl⟩ (by norm_num))
theorem R53581 : Reach 53581 := rs (se 3 (by rfl) ⟨10046, by rfl⟩) (B 20093 (by norm_num) ⟨10046, by rfl⟩ (by norm_num))
theorem R53585 : Reach 53585 := rs (se 2 (by rfl) ⟨20094, by rfl⟩) (B 40189 (by norm_num) ⟨20094, by rfl⟩ (by norm_num))
theorem R53589 : Reach 53589 := rs (se 10 (by rfl) ⟨78, by rfl⟩) (B 157 (by norm_num) ⟨78, by rfl⟩ (by norm_num))
theorem R53593 : Reach 53593 := rs (se 2 (by rfl) ⟨20097, by rfl⟩) (B 40195 (by norm_num) ⟨20097, by rfl⟩ (by norm_num))
theorem R53597 : Reach 53597 := rs (se 3 (by rfl) ⟨10049, by rfl⟩) (B 20099 (by norm_num) ⟨10049, by rfl⟩ (by norm_num))
theorem R53601 : Reach 53601 := rs (se 2 (by rfl) ⟨20100, by rfl⟩) (B 40201 (by norm_num) ⟨20100, by rfl⟩ (by norm_num))
theorem R119141 : Reach 119141 := rs (se 4 (by rfl) ⟨11169, by rfl⟩) (B 22339 (by norm_num) ⟨11169, by rfl⟩ (by norm_num))
theorem R53605 : Reach 53605 := rs (se 4 (by rfl) ⟨5025, by rfl⟩) (B 10051 (by norm_num) ⟨5025, by rfl⟩ (by norm_num))
theorem R53609 : Reach 53609 := rs (se 2 (by rfl) ⟨20103, by rfl⟩) (B 40207 (by norm_num) ⟨20103, by rfl⟩ (by norm_num))
theorem R53613 : Reach 53613 := rs (se 3 (by rfl) ⟨10052, by rfl⟩) (B 20105 (by norm_num) ⟨10052, by rfl⟩ (by norm_num))
theorem R53617 : Reach 53617 := rs (se 2 (by rfl) ⟨20106, by rfl⟩) (B 40213 (by norm_num) ⟨20106, by rfl⟩ (by norm_num))
theorem R250229 : Reach 250229 := rs (se 5 (by rfl) ⟨11729, by rfl⟩) (B 23459 (by norm_num) ⟨11729, by rfl⟩ (by norm_num))
theorem R53621 : Reach 53621 := rs (se 5 (by rfl) ⟨2513, by rfl⟩) (B 5027 (by norm_num) ⟨2513, by rfl⟩ (by norm_num))
theorem R53625 : Reach 53625 := rs (se 2 (by rfl) ⟨20109, by rfl⟩) (B 40219 (by norm_num) ⟨20109, by rfl⟩ (by norm_num))
theorem R53629 : Reach 53629 := rs (se 3 (by rfl) ⟨10055, by rfl⟩) (B 20111 (by norm_num) ⟨10055, by rfl⟩ (by norm_num))
theorem R53633 : Reach 53633 := rs (se 2 (by rfl) ⟨20112, by rfl⟩) (B 40225 (by norm_num) ⟨20112, by rfl⟩ (by norm_num))
theorem R119173 : Reach 119173 := rs (se 4 (by rfl) ⟨11172, by rfl⟩) (B 22345 (by norm_num) ⟨11172, by rfl⟩ (by norm_num))
theorem R53637 : Reach 53637 := rs (se 4 (by rfl) ⟨5028, by rfl⟩) (B 10057 (by norm_num) ⟨5028, by rfl⟩ (by norm_num))
theorem R53641 : Reach 53641 := rs (se 2 (by rfl) ⟨20115, by rfl⟩) (B 40231 (by norm_num) ⟨20115, by rfl⟩ (by norm_num))
theorem R86413 : Reach 86413 := rs (se 3 (by rfl) ⟨16202, by rfl⟩) (B 32405 (by norm_num) ⟨16202, by rfl⟩ (by norm_num))
theorem R53645 : Reach 53645 := rs (se 3 (by rfl) ⟨10058, by rfl⟩) (B 20117 (by norm_num) ⟨10058, by rfl⟩ (by norm_num))
theorem R53649 : Reach 53649 := rs (se 2 (by rfl) ⟨20118, by rfl⟩) (B 40237 (by norm_num) ⟨20118, by rfl⟩ (by norm_num))
theorem R53653 : Reach 53653 := rs (se 6 (by rfl) ⟨1257, by rfl⟩) (B 2515 (by norm_num) ⟨1257, by rfl⟩ (by norm_num))
theorem R53657 : Reach 53657 := rs (se 2 (by rfl) ⟨20121, by rfl⟩) (B 40243 (by norm_num) ⟨20121, by rfl⟩ (by norm_num))
theorem R53661 : Reach 53661 := rs (se 3 (by rfl) ⟨10061, by rfl⟩) (B 20123 (by norm_num) ⟨10061, by rfl⟩ (by norm_num))
theorem R53665 : Reach 53665 := rs (se 2 (by rfl) ⟨20124, by rfl⟩) (B 40249 (by norm_num) ⟨20124, by rfl⟩ (by norm_num))
theorem R53669 : Reach 53669 := rs (se 4 (by rfl) ⟨5031, by rfl⟩) (B 10063 (by norm_num) ⟨5031, by rfl⟩ (by norm_num))
theorem R53673 : Reach 53673 := rs (se 2 (by rfl) ⟨20127, by rfl⟩) (B 40255 (by norm_num) ⟨20127, by rfl⟩ (by norm_num))
theorem R119213 : Reach 119213 := rs (se 3 (by rfl) ⟨22352, by rfl⟩) (B 44705 (by norm_num) ⟨22352, by rfl⟩ (by norm_num))
theorem R53677 : Reach 53677 := rs (se 3 (by rfl) ⟨10064, by rfl⟩) (B 20129 (by norm_num) ⟨10064, by rfl⟩ (by norm_num))
theorem R53681 : Reach 53681 := rs (se 2 (by rfl) ⟨20130, by rfl⟩) (B 40261 (by norm_num) ⟨20130, by rfl⟩ (by norm_num))
theorem R53685 : Reach 53685 := rs (se 5 (by rfl) ⟨2516, by rfl⟩) (B 5033 (by norm_num) ⟨2516, by rfl⟩ (by norm_num))
theorem R53689 : Reach 53689 := rs (se 2 (by rfl) ⟨20133, by rfl⟩) (B 40267 (by norm_num) ⟨20133, by rfl⟩ (by norm_num))
theorem R53693 : Reach 53693 := rs (se 3 (by rfl) ⟨10067, by rfl⟩) (B 20135 (by norm_num) ⟨10067, by rfl⟩ (by norm_num))
theorem R53697 : Reach 53697 := rs (se 2 (by rfl) ⟨20136, by rfl⟩) (B 40273 (by norm_num) ⟨20136, by rfl⟩ (by norm_num))
theorem R53701 : Reach 53701 := rs (se 4 (by rfl) ⟨5034, by rfl⟩) (B 10069 (by norm_num) ⟨5034, by rfl⟩ (by norm_num))
theorem R53705 : Reach 53705 := rs (se 2 (by rfl) ⟨20139, by rfl⟩) (B 40279 (by norm_num) ⟨20139, by rfl⟩ (by norm_num))
theorem R53709 : Reach 53709 := rs (se 3 (by rfl) ⟨10070, by rfl⟩) (B 20141 (by norm_num) ⟨10070, by rfl⟩ (by norm_num))
theorem R53713 : Reach 53713 := rs (se 2 (by rfl) ⟨20142, by rfl⟩) (B 40285 (by norm_num) ⟨20142, by rfl⟩ (by norm_num))
theorem R53717 : Reach 53717 := rs (se 7 (by rfl) ⟨629, by rfl⟩) (B 1259 (by norm_num) ⟨629, by rfl⟩ (by norm_num))
theorem R53721 : Reach 53721 := rs (se 2 (by rfl) ⟨20145, by rfl⟩) (B 40291 (by norm_num) ⟨20145, by rfl⟩ (by norm_num))
theorem R53725 : Reach 53725 := rs (se 3 (by rfl) ⟨10073, by rfl⟩) (B 20147 (by norm_num) ⟨10073, by rfl⟩ (by norm_num))
theorem R53729 : Reach 53729 := rs (se 2 (by rfl) ⟨20148, by rfl⟩) (B 40297 (by norm_num) ⟨20148, by rfl⟩ (by norm_num))
theorem R86501 : Reach 86501 := rs (se 4 (by rfl) ⟨8109, by rfl⟩) (B 16219 (by norm_num) ⟨8109, by rfl⟩ (by norm_num))
theorem R53733 : Reach 53733 := rs (se 4 (by rfl) ⟨5037, by rfl⟩) (B 10075 (by norm_num) ⟨5037, by rfl⟩ (by norm_num))
theorem R53737 : Reach 53737 := rs (se 2 (by rfl) ⟨20151, by rfl⟩) (B 40303 (by norm_num) ⟨20151, by rfl⟩ (by norm_num))
theorem R53741 : Reach 53741 := rs (se 3 (by rfl) ⟨10076, by rfl⟩) (B 20153 (by norm_num) ⟨10076, by rfl⟩ (by norm_num))
theorem R53745 : Reach 53745 := rs (se 2 (by rfl) ⟨20154, by rfl⟩) (B 40309 (by norm_num) ⟨20154, by rfl⟩ (by norm_num))
theorem R119285 : Reach 119285 := rs (se 5 (by rfl) ⟨5591, by rfl⟩) (B 11183 (by norm_num) ⟨5591, by rfl⟩ (by norm_num))
theorem R53749 : Reach 53749 := rs (se 5 (by rfl) ⟨2519, by rfl⟩) (B 5039 (by norm_num) ⟨2519, by rfl⟩ (by norm_num))
theorem R53753 : Reach 53753 := rs (se 2 (by rfl) ⟨20157, by rfl⟩) (B 40315 (by norm_num) ⟨20157, by rfl⟩ (by norm_num))
theorem R53757 : Reach 53757 := rs (se 3 (by rfl) ⟨10079, by rfl⟩) (B 20159 (by norm_num) ⟨10079, by rfl⟩ (by norm_num))
theorem R53761 : Reach 53761 := rs (se 2 (by rfl) ⟨20160, by rfl⟩) (B 40321 (by norm_num) ⟨20160, by rfl⟩ (by norm_num))
theorem R53765 : Reach 53765 := rs (se 4 (by rfl) ⟨5040, by rfl⟩) (B 10081 (by norm_num) ⟨5040, by rfl⟩ (by norm_num))
theorem R53769 : Reach 53769 := rs (se 2 (by rfl) ⟨20163, by rfl⟩) (B 40327 (by norm_num) ⟨20163, by rfl⟩ (by norm_num))
theorem R53773 : Reach 53773 := rs (se 3 (by rfl) ⟨10082, by rfl⟩) (B 20165 (by norm_num) ⟨10082, by rfl⟩ (by norm_num))
theorem R53777 : Reach 53777 := rs (se 2 (by rfl) ⟨20166, by rfl⟩) (B 40333 (by norm_num) ⟨20166, by rfl⟩ (by norm_num))
theorem R53781 : Reach 53781 := rs (se 6 (by rfl) ⟨1260, by rfl⟩) (B 2521 (by norm_num) ⟨1260, by rfl⟩ (by norm_num))
theorem R53785 : Reach 53785 := rs (se 2 (by rfl) ⟨20169, by rfl⟩) (B 40339 (by norm_num) ⟨20169, by rfl⟩ (by norm_num))
theorem R53789 : Reach 53789 := rs (se 3 (by rfl) ⟨10085, by rfl⟩) (B 20171 (by norm_num) ⟨10085, by rfl⟩ (by norm_num))
theorem R53793 : Reach 53793 := rs (se 2 (by rfl) ⟨20172, by rfl⟩) (B 40345 (by norm_num) ⟨20172, by rfl⟩ (by norm_num))
theorem R53797 : Reach 53797 := rs (se 4 (by rfl) ⟨5043, by rfl⟩) (B 10087 (by norm_num) ⟨5043, by rfl⟩ (by norm_num))
theorem R53801 : Reach 53801 := rs (se 2 (by rfl) ⟨20175, by rfl⟩) (B 40351 (by norm_num) ⟨20175, by rfl⟩ (by norm_num))
theorem R53805 : Reach 53805 := rs (se 3 (by rfl) ⟨10088, by rfl⟩) (B 20177 (by norm_num) ⟨10088, by rfl⟩ (by norm_num))
theorem R53809 : Reach 53809 := rs (se 2 (by rfl) ⟨20178, by rfl⟩) (B 40357 (by norm_num) ⟨20178, by rfl⟩ (by norm_num))
theorem R53813 : Reach 53813 := rs (se 5 (by rfl) ⟨2522, by rfl⟩) (B 5045 (by norm_num) ⟨2522, by rfl⟩ (by norm_num))
theorem R53817 : Reach 53817 := rs (se 2 (by rfl) ⟨20181, by rfl⟩) (B 40363 (by norm_num) ⟨20181, by rfl⟩ (by norm_num))
theorem R119357 : Reach 119357 := rs (se 3 (by rfl) ⟨22379, by rfl⟩) (B 44759 (by norm_num) ⟨22379, by rfl⟩ (by norm_num))
theorem R53821 : Reach 53821 := rs (se 3 (by rfl) ⟨10091, by rfl⟩) (B 20183 (by norm_num) ⟨10091, by rfl⟩ (by norm_num))
theorem R53825 : Reach 53825 := rs (se 2 (by rfl) ⟨20184, by rfl⟩) (B 40369 (by norm_num) ⟨20184, by rfl⟩ (by norm_num))
theorem R53829 : Reach 53829 := rs (se 4 (by rfl) ⟨5046, by rfl⟩) (B 10093 (by norm_num) ⟨5046, by rfl⟩ (by norm_num))
theorem R53833 : Reach 53833 := rs (se 2 (by rfl) ⟨20187, by rfl⟩) (B 40375 (by norm_num) ⟨20187, by rfl⟩ (by norm_num))
theorem R53837 : Reach 53837 := rs (se 3 (by rfl) ⟨10094, by rfl⟩) (B 20189 (by norm_num) ⟨10094, by rfl⟩ (by norm_num))
theorem R53841 : Reach 53841 := rs (se 2 (by rfl) ⟨20190, by rfl⟩) (B 40381 (by norm_num) ⟨20190, by rfl⟩ (by norm_num))
theorem R610901 : Reach 610901 := rs (se 8 (by rfl) ⟨3579, by rfl⟩) (B 7159 (by norm_num) ⟨3579, by rfl⟩ (by norm_num))
theorem R53845 : Reach 53845 := rs (se 8 (by rfl) ⟨315, by rfl⟩) (B 631 (by norm_num) ⟨315, by rfl⟩ (by norm_num))
theorem R53849 : Reach 53849 := rs (se 2 (by rfl) ⟨20193, by rfl⟩) (B 40387 (by norm_num) ⟨20193, by rfl⟩ (by norm_num))
theorem R53853 : Reach 53853 := rs (se 3 (by rfl) ⟨10097, by rfl⟩) (B 20195 (by norm_num) ⟨10097, by rfl⟩ (by norm_num))
theorem R53857 : Reach 53857 := rs (se 2 (by rfl) ⟨20196, by rfl⟩) (B 40393 (by norm_num) ⟨20196, by rfl⟩ (by norm_num))
theorem R184933 : Reach 184933 := rs (se 4 (by rfl) ⟨17337, by rfl⟩) (B 34675 (by norm_num) ⟨17337, by rfl⟩ (by norm_num))
theorem R86629 : Reach 86629 := rs (se 4 (by rfl) ⟨8121, by rfl⟩) (B 16243 (by norm_num) ⟨8121, by rfl⟩ (by norm_num))
theorem R53861 : Reach 53861 := rs (se 4 (by rfl) ⟨5049, by rfl⟩) (B 10099 (by norm_num) ⟨5049, by rfl⟩ (by norm_num))
theorem R53865 : Reach 53865 := rs (se 2 (by rfl) ⟨20199, by rfl⟩) (B 40399 (by norm_num) ⟨20199, by rfl⟩ (by norm_num))
theorem R53869 : Reach 53869 := rs (se 3 (by rfl) ⟨10100, by rfl⟩) (B 20201 (by norm_num) ⟨10100, by rfl⟩ (by norm_num))
theorem R53873 : Reach 53873 := rs (se 2 (by rfl) ⟨20202, by rfl⟩) (B 40405 (by norm_num) ⟨20202, by rfl⟩ (by norm_num))
theorem R53877 : Reach 53877 := rs (se 5 (by rfl) ⟨2525, by rfl⟩) (B 5051 (by norm_num) ⟨2525, by rfl⟩ (by norm_num))
theorem R184949 : Reach 184949 := rs (se 5 (by rfl) ⟨8669, by rfl⟩) (B 17339 (by norm_num) ⟨8669, by rfl⟩ (by norm_num))
theorem R53881 : Reach 53881 := rs (se 2 (by rfl) ⟨20205, by rfl⟩) (B 40411 (by norm_num) ⟨20205, by rfl⟩ (by norm_num))
theorem R53885 : Reach 53885 := rs (se 3 (by rfl) ⟨10103, by rfl⟩) (B 20207 (by norm_num) ⟨10103, by rfl⟩ (by norm_num))
theorem R53889 : Reach 53889 := rs (se 2 (by rfl) ⟨20208, by rfl⟩) (B 40417 (by norm_num) ⟨20208, by rfl⟩ (by norm_num))
theorem R119429 : Reach 119429 := rs (se 4 (by rfl) ⟨11196, by rfl⟩) (B 22393 (by norm_num) ⟨11196, by rfl⟩ (by norm_num))
theorem R53893 : Reach 53893 := rs (se 4 (by rfl) ⟨5052, by rfl⟩) (B 10105 (by norm_num) ⟨5052, by rfl⟩ (by norm_num))
theorem R53897 : Reach 53897 := rs (se 2 (by rfl) ⟨20211, by rfl⟩) (B 40423 (by norm_num) ⟨20211, by rfl⟩ (by norm_num))
theorem R53901 : Reach 53901 := rs (se 3 (by rfl) ⟨10106, by rfl⟩) (B 20213 (by norm_num) ⟨10106, by rfl⟩ (by norm_num))
theorem R53905 : Reach 53905 := rs (se 2 (by rfl) ⟨20214, by rfl⟩) (B 40429 (by norm_num) ⟨20214, by rfl⟩ (by norm_num))
theorem R53909 : Reach 53909 := rs (se 6 (by rfl) ⟨1263, by rfl⟩) (B 2527 (by norm_num) ⟨1263, by rfl⟩ (by norm_num))
theorem R53913 : Reach 53913 := rs (se 2 (by rfl) ⟨20217, by rfl⟩) (B 40435 (by norm_num) ⟨20217, by rfl⟩ (by norm_num))
theorem R53917 : Reach 53917 := rs (se 3 (by rfl) ⟨10109, by rfl⟩) (B 20219 (by norm_num) ⟨10109, by rfl⟩ (by norm_num))
theorem R53921 : Reach 53921 := rs (se 2 (by rfl) ⟨20220, by rfl⟩) (B 40441 (by norm_num) ⟨20220, by rfl⟩ (by norm_num))
theorem R53925 : Reach 53925 := rs (se 4 (by rfl) ⟨5055, by rfl⟩) (B 10111 (by norm_num) ⟨5055, by rfl⟩ (by norm_num))
theorem R53929 : Reach 53929 := rs (se 2 (by rfl) ⟨20223, by rfl⟩) (B 40447 (by norm_num) ⟨20223, by rfl⟩ (by norm_num))
theorem R53933 : Reach 53933 := rs (se 3 (by rfl) ⟨10112, by rfl⟩) (B 20225 (by norm_num) ⟨10112, by rfl⟩ (by norm_num))
theorem R53937 : Reach 53937 := rs (se 2 (by rfl) ⟨20226, by rfl⟩) (B 40453 (by norm_num) ⟨20226, by rfl⟩ (by norm_num))
theorem R53941 : Reach 53941 := rs (se 5 (by rfl) ⟨2528, by rfl⟩) (B 5057 (by norm_num) ⟨2528, by rfl⟩ (by norm_num))
theorem R53945 : Reach 53945 := rs (se 2 (by rfl) ⟨20229, by rfl⟩) (B 40459 (by norm_num) ⟨20229, by rfl⟩ (by norm_num))
theorem R86717 : Reach 86717 := rs (se 3 (by rfl) ⟨16259, by rfl⟩) (B 32519 (by norm_num) ⟨16259, by rfl⟩ (by norm_num))
theorem R53949 : Reach 53949 := rs (se 3 (by rfl) ⟨10115, by rfl⟩) (B 20231 (by norm_num) ⟨10115, by rfl⟩ (by norm_num))
theorem R53953 : Reach 53953 := rs (se 2 (by rfl) ⟨20232, by rfl⟩) (B 40465 (by norm_num) ⟨20232, by rfl⟩ (by norm_num))
theorem R53957 : Reach 53957 := rs (se 4 (by rfl) ⟨5058, by rfl⟩) (B 10117 (by norm_num) ⟨5058, by rfl⟩ (by norm_num))
theorem R53961 : Reach 53961 := rs (se 2 (by rfl) ⟨20235, by rfl⟩) (B 40471 (by norm_num) ⟨20235, by rfl⟩ (by norm_num))
theorem R119501 : Reach 119501 := rs (se 3 (by rfl) ⟨22406, by rfl⟩) (B 44813 (by norm_num) ⟨22406, by rfl⟩ (by norm_num))
theorem R53965 : Reach 53965 := rs (se 3 (by rfl) ⟨10118, by rfl⟩) (B 20237 (by norm_num) ⟨10118, by rfl⟩ (by norm_num))
theorem R53969 : Reach 53969 := rs (se 2 (by rfl) ⟨20238, by rfl⟩) (B 40477 (by norm_num) ⟨20238, by rfl⟩ (by norm_num))
theorem R53973 : Reach 53973 := rs (se 7 (by rfl) ⟨632, by rfl⟩) (B 1265 (by norm_num) ⟨632, by rfl⟩ (by norm_num))
theorem R53977 : Reach 53977 := rs (se 2 (by rfl) ⟨20241, by rfl⟩) (B 40483 (by norm_num) ⟨20241, by rfl⟩ (by norm_num))
theorem R53981 : Reach 53981 := rs (se 3 (by rfl) ⟨10121, by rfl⟩) (B 20243 (by norm_num) ⟨10121, by rfl⟩ (by norm_num))
theorem R53985 : Reach 53985 := rs (se 2 (by rfl) ⟨20244, by rfl⟩) (B 40489 (by norm_num) ⟨20244, by rfl⟩ (by norm_num))
theorem R53989 : Reach 53989 := rs (se 4 (by rfl) ⟨5061, by rfl⟩) (B 10123 (by norm_num) ⟨5061, by rfl⟩ (by norm_num))
theorem R152293 : Reach 152293 := rs (se 4 (by rfl) ⟨14277, by rfl⟩) (B 28555 (by norm_num) ⟨14277, by rfl⟩ (by norm_num))
theorem R53993 : Reach 53993 := rs (se 2 (by rfl) ⟨20247, by rfl⟩) (B 40495 (by norm_num) ⟨20247, by rfl⟩ (by norm_num))
theorem R53997 : Reach 53997 := rs (se 3 (by rfl) ⟨10124, by rfl⟩) (B 20249 (by norm_num) ⟨10124, by rfl⟩ (by norm_num))
theorem R54001 : Reach 54001 := rs (se 2 (by rfl) ⟨20250, by rfl⟩) (B 40501 (by norm_num) ⟨20250, by rfl⟩ (by norm_num))
theorem R54005 : Reach 54005 := rs (se 5 (by rfl) ⟨2531, by rfl⟩) (B 5063 (by norm_num) ⟨2531, by rfl⟩ (by norm_num))
theorem R54009 : Reach 54009 := rs (se 2 (by rfl) ⟨20253, by rfl⟩) (B 40507 (by norm_num) ⟨20253, by rfl⟩ (by norm_num))
theorem R54013 : Reach 54013 := rs (se 3 (by rfl) ⟨10127, by rfl⟩) (B 20255 (by norm_num) ⟨10127, by rfl⟩ (by norm_num))
theorem R54017 : Reach 54017 := rs (se 2 (by rfl) ⟨20256, by rfl⟩) (B 40513 (by norm_num) ⟨20256, by rfl⟩ (by norm_num))
theorem R54021 : Reach 54021 := rs (se 4 (by rfl) ⟨5064, by rfl⟩) (B 10129 (by norm_num) ⟨5064, by rfl⟩ (by norm_num))
theorem R54025 : Reach 54025 := rs (se 2 (by rfl) ⟨20259, by rfl⟩) (B 40519 (by norm_num) ⟨20259, by rfl⟩ (by norm_num))
theorem R54029 : Reach 54029 := rs (se 3 (by rfl) ⟨10130, by rfl⟩) (B 20261 (by norm_num) ⟨10130, by rfl⟩ (by norm_num))
theorem R54033 : Reach 54033 := rs (se 2 (by rfl) ⟨20262, by rfl⟩) (B 40525 (by norm_num) ⟨20262, by rfl⟩ (by norm_num))
theorem R119573 : Reach 119573 := rs (se 6 (by rfl) ⟨2802, by rfl⟩) (B 5605 (by norm_num) ⟨2802, by rfl⟩ (by norm_num))
theorem R54037 : Reach 54037 := rs (se 6 (by rfl) ⟨1266, by rfl⟩) (B 2533 (by norm_num) ⟨1266, by rfl⟩ (by norm_num))
theorem R54041 : Reach 54041 := rs (se 2 (by rfl) ⟨20265, by rfl⟩) (B 40531 (by norm_num) ⟨20265, by rfl⟩ (by norm_num))
theorem R54045 : Reach 54045 := rs (se 3 (by rfl) ⟨10133, by rfl⟩) (B 20267 (by norm_num) ⟨10133, by rfl⟩ (by norm_num))
theorem R54049 : Reach 54049 := rs (se 2 (by rfl) ⟨20268, by rfl⟩) (B 40537 (by norm_num) ⟨20268, by rfl⟩ (by norm_num))
theorem R54053 : Reach 54053 := rs (se 4 (by rfl) ⟨5067, by rfl⟩) (B 10135 (by norm_num) ⟨5067, by rfl⟩ (by norm_num))
theorem R54057 : Reach 54057 := rs (se 2 (by rfl) ⟨20271, by rfl⟩) (B 40543 (by norm_num) ⟨20271, by rfl⟩ (by norm_num))
theorem R54061 : Reach 54061 := rs (se 3 (by rfl) ⟨10136, by rfl⟩) (B 20273 (by norm_num) ⟨10136, by rfl⟩ (by norm_num))
theorem R54065 : Reach 54065 := rs (se 2 (by rfl) ⟨20274, by rfl⟩) (B 40549 (by norm_num) ⟨20274, by rfl⟩ (by norm_num))
theorem R54069 : Reach 54069 := rs (se 5 (by rfl) ⟨2534, by rfl⟩) (B 5069 (by norm_num) ⟨2534, by rfl⟩ (by norm_num))
theorem R54073 : Reach 54073 := rs (se 2 (by rfl) ⟨20277, by rfl⟩) (B 40555 (by norm_num) ⟨20277, by rfl⟩ (by norm_num))
theorem R86845 : Reach 86845 := rs (se 3 (by rfl) ⟨16283, by rfl⟩) (B 32567 (by norm_num) ⟨16283, by rfl⟩ (by norm_num))
theorem R54077 : Reach 54077 := rs (se 3 (by rfl) ⟨10139, by rfl⟩) (B 20279 (by norm_num) ⟨10139, by rfl⟩ (by norm_num))
theorem R54081 : Reach 54081 := rs (se 2 (by rfl) ⟨20280, by rfl⟩) (B 40561 (by norm_num) ⟨20280, by rfl⟩ (by norm_num))
theorem R54085 : Reach 54085 := rs (se 4 (by rfl) ⟨5070, by rfl⟩) (B 10141 (by norm_num) ⟨5070, by rfl⟩ (by norm_num))
theorem R54089 : Reach 54089 := rs (se 2 (by rfl) ⟨20283, by rfl⟩) (B 40567 (by norm_num) ⟨20283, by rfl⟩ (by norm_num))
theorem R54093 : Reach 54093 := rs (se 3 (by rfl) ⟨10142, by rfl⟩) (B 20285 (by norm_num) ⟨10142, by rfl⟩ (by norm_num))
theorem R54097 : Reach 54097 := rs (se 2 (by rfl) ⟨20286, by rfl⟩) (B 40573 (by norm_num) ⟨20286, by rfl⟩ (by norm_num))
theorem R54101 : Reach 54101 := rs (se 9 (by rfl) ⟨158, by rfl⟩) (B 317 (by norm_num) ⟨158, by rfl⟩ (by norm_num))
theorem R54105 : Reach 54105 := rs (se 2 (by rfl) ⟨20289, by rfl⟩) (B 40579 (by norm_num) ⟨20289, by rfl⟩ (by norm_num))
theorem R119645 : Reach 119645 := rs (se 3 (by rfl) ⟨22433, by rfl⟩) (B 44867 (by norm_num) ⟨22433, by rfl⟩ (by norm_num))
theorem R54109 : Reach 54109 := rs (se 3 (by rfl) ⟨10145, by rfl⟩) (B 20291 (by norm_num) ⟨10145, by rfl⟩ (by norm_num))
theorem R54113 : Reach 54113 := rs (se 2 (by rfl) ⟨20292, by rfl⟩) (B 40585 (by norm_num) ⟨20292, by rfl⟩ (by norm_num))
theorem R54117 : Reach 54117 := rs (se 4 (by rfl) ⟨5073, by rfl⟩) (B 10147 (by norm_num) ⟨5073, by rfl⟩ (by norm_num))
theorem R54121 : Reach 54121 := rs (se 2 (by rfl) ⟨20295, by rfl⟩) (B 40591 (by norm_num) ⟨20295, by rfl⟩ (by norm_num))
theorem R54125 : Reach 54125 := rs (se 3 (by rfl) ⟨10148, by rfl⟩) (B 20297 (by norm_num) ⟨10148, by rfl⟩ (by norm_num))
theorem R54129 : Reach 54129 := rs (se 2 (by rfl) ⟨20298, by rfl⟩) (B 40597 (by norm_num) ⟨20298, by rfl⟩ (by norm_num))
theorem R54133 : Reach 54133 := rs (se 5 (by rfl) ⟨2537, by rfl⟩) (B 5075 (by norm_num) ⟨2537, by rfl⟩ (by norm_num))
theorem R54137 : Reach 54137 := rs (se 2 (by rfl) ⟨20301, by rfl⟩) (B 40603 (by norm_num) ⟨20301, by rfl⟩ (by norm_num))
theorem R54141 : Reach 54141 := rs (se 3 (by rfl) ⟨10151, by rfl⟩) (B 20303 (by norm_num) ⟨10151, by rfl⟩ (by norm_num))
theorem R54145 : Reach 54145 := rs (se 2 (by rfl) ⟨20304, by rfl⟩) (B 40609 (by norm_num) ⟨20304, by rfl⟩ (by norm_num))
theorem R54149 : Reach 54149 := rs (se 4 (by rfl) ⟨5076, by rfl⟩) (B 10153 (by norm_num) ⟨5076, by rfl⟩ (by norm_num))
theorem R54153 : Reach 54153 := rs (se 2 (by rfl) ⟨20307, by rfl⟩) (B 40615 (by norm_num) ⟨20307, by rfl⟩ (by norm_num))
theorem R54157 : Reach 54157 := rs (se 3 (by rfl) ⟨10154, by rfl⟩) (B 20309 (by norm_num) ⟨10154, by rfl⟩ (by norm_num))
theorem R54161 : Reach 54161 := rs (se 2 (by rfl) ⟨20310, by rfl⟩) (B 40621 (by norm_num) ⟨20310, by rfl⟩ (by norm_num))
theorem R86933 : Reach 86933 := rs (se 6 (by rfl) ⟨2037, by rfl⟩) (B 4075 (by norm_num) ⟨2037, by rfl⟩ (by norm_num))
theorem R54165 : Reach 54165 := rs (se 6 (by rfl) ⟨1269, by rfl⟩) (B 2539 (by norm_num) ⟨1269, by rfl⟩ (by norm_num))
theorem R54169 : Reach 54169 := rs (se 2 (by rfl) ⟨20313, by rfl⟩) (B 40627 (by norm_num) ⟨20313, by rfl⟩ (by norm_num))
theorem R54173 : Reach 54173 := rs (se 3 (by rfl) ⟨10157, by rfl⟩) (B 20315 (by norm_num) ⟨10157, by rfl⟩ (by norm_num))
theorem R54177 : Reach 54177 := rs (se 2 (by rfl) ⟨20316, by rfl⟩) (B 40633 (by norm_num) ⟨20316, by rfl⟩ (by norm_num))
theorem R119717 : Reach 119717 := rs (se 4 (by rfl) ⟨11223, by rfl⟩) (B 22447 (by norm_num) ⟨11223, by rfl⟩ (by norm_num))
theorem R54181 : Reach 54181 := rs (se 4 (by rfl) ⟨5079, by rfl⟩) (B 10159 (by norm_num) ⟨5079, by rfl⟩ (by norm_num))
theorem R54185 : Reach 54185 := rs (se 2 (by rfl) ⟨20319, by rfl⟩) (B 40639 (by norm_num) ⟨20319, by rfl⟩ (by norm_num))
theorem R54189 : Reach 54189 := rs (se 3 (by rfl) ⟨10160, by rfl⟩) (B 20321 (by norm_num) ⟨10160, by rfl⟩ (by norm_num))
theorem R54193 : Reach 54193 := rs (se 2 (by rfl) ⟨20322, by rfl⟩) (B 40645 (by norm_num) ⟨20322, by rfl⟩ (by norm_num))
theorem R54197 : Reach 54197 := rs (se 5 (by rfl) ⟨2540, by rfl⟩) (B 5081 (by norm_num) ⟨2540, by rfl⟩ (by norm_num))
theorem R54201 : Reach 54201 := rs (se 2 (by rfl) ⟨20325, by rfl⟩) (B 40651 (by norm_num) ⟨20325, by rfl⟩ (by norm_num))
theorem R54205 : Reach 54205 := rs (se 3 (by rfl) ⟨10163, by rfl⟩) (B 20327 (by norm_num) ⟨10163, by rfl⟩ (by norm_num))
theorem R54209 : Reach 54209 := rs (se 2 (by rfl) ⟨20328, by rfl⟩) (B 40657 (by norm_num) ⟨20328, by rfl⟩ (by norm_num))
theorem R54213 : Reach 54213 := rs (se 4 (by rfl) ⟨5082, by rfl⟩) (B 10165 (by norm_num) ⟨5082, by rfl⟩ (by norm_num))
theorem R54217 : Reach 54217 := rs (se 2 (by rfl) ⟨20331, by rfl⟩) (B 40663 (by norm_num) ⟨20331, by rfl⟩ (by norm_num))
theorem R54221 : Reach 54221 := rs (se 3 (by rfl) ⟨10166, by rfl⟩) (B 20333 (by norm_num) ⟨10166, by rfl⟩ (by norm_num))
theorem R54225 : Reach 54225 := rs (se 2 (by rfl) ⟨20334, by rfl⟩) (B 40669 (by norm_num) ⟨20334, by rfl⟩ (by norm_num))
theorem R54229 : Reach 54229 := rs (se 7 (by rfl) ⟨635, by rfl⟩) (B 1271 (by norm_num) ⟨635, by rfl⟩ (by norm_num))
theorem R54233 : Reach 54233 := rs (se 2 (by rfl) ⟨20337, by rfl⟩) (B 40675 (by norm_num) ⟨20337, by rfl⟩ (by norm_num))
theorem R87005 : Reach 87005 := rs (se 3 (by rfl) ⟨16313, by rfl⟩) (B 32627 (by norm_num) ⟨16313, by rfl⟩ (by norm_num))
theorem R54237 : Reach 54237 := rs (se 3 (by rfl) ⟨10169, by rfl⟩) (B 20339 (by norm_num) ⟨10169, by rfl⟩ (by norm_num))
theorem R54241 : Reach 54241 := rs (se 2 (by rfl) ⟨20340, by rfl⟩) (B 40681 (by norm_num) ⟨20340, by rfl⟩ (by norm_num))
theorem R54245 : Reach 54245 := rs (se 4 (by rfl) ⟨5085, by rfl⟩) (B 10171 (by norm_num) ⟨5085, by rfl⟩ (by norm_num))
theorem R54249 : Reach 54249 := rs (se 2 (by rfl) ⟨20343, by rfl⟩) (B 40687 (by norm_num) ⟨20343, by rfl⟩ (by norm_num))
theorem R119789 : Reach 119789 := rs (se 3 (by rfl) ⟨22460, by rfl⟩) (B 44921 (by norm_num) ⟨22460, by rfl⟩ (by norm_num))
theorem R54253 : Reach 54253 := rs (se 3 (by rfl) ⟨10172, by rfl⟩) (B 20345 (by norm_num) ⟨10172, by rfl⟩ (by norm_num))
theorem R54257 : Reach 54257 := rs (se 2 (by rfl) ⟨20346, by rfl⟩) (B 40693 (by norm_num) ⟨20346, by rfl⟩ (by norm_num))
theorem R54261 : Reach 54261 := rs (se 5 (by rfl) ⟨2543, by rfl⟩) (B 5087 (by norm_num) ⟨2543, by rfl⟩ (by norm_num))
theorem R54265 : Reach 54265 := rs (se 2 (by rfl) ⟨20349, by rfl⟩) (B 40699 (by norm_num) ⟨20349, by rfl⟩ (by norm_num))
theorem R54269 : Reach 54269 := rs (se 3 (by rfl) ⟨10175, by rfl⟩) (B 20351 (by norm_num) ⟨10175, by rfl⟩ (by norm_num))
theorem R54273 : Reach 54273 := rs (se 2 (by rfl) ⟨20352, by rfl⟩) (B 40705 (by norm_num) ⟨20352, by rfl⟩ (by norm_num))
theorem R54277 : Reach 54277 := rs (se 4 (by rfl) ⟨5088, by rfl⟩) (B 10177 (by norm_num) ⟨5088, by rfl⟩ (by norm_num))
theorem R54281 : Reach 54281 := rs (se 2 (by rfl) ⟨20355, by rfl⟩) (B 40711 (by norm_num) ⟨20355, by rfl⟩ (by norm_num))
theorem R54285 : Reach 54285 := rs (se 3 (by rfl) ⟨10178, by rfl⟩) (B 20357 (by norm_num) ⟨10178, by rfl⟩ (by norm_num))
theorem R54289 : Reach 54289 := rs (se 2 (by rfl) ⟨20358, by rfl⟩) (B 40717 (by norm_num) ⟨20358, by rfl⟩ (by norm_num))
theorem R87061 : Reach 87061 := rs (se 6 (by rfl) ⟨2040, by rfl⟩) (B 4081 (by norm_num) ⟨2040, by rfl⟩ (by norm_num))
theorem R54293 : Reach 54293 := rs (se 6 (by rfl) ⟨1272, by rfl⟩) (B 2545 (by norm_num) ⟨1272, by rfl⟩ (by norm_num))
theorem R54297 : Reach 54297 := rs (se 2 (by rfl) ⟨20361, by rfl⟩) (B 40723 (by norm_num) ⟨20361, by rfl⟩ (by norm_num))
theorem R54301 : Reach 54301 := rs (se 3 (by rfl) ⟨10181, by rfl⟩) (B 20363 (by norm_num) ⟨10181, by rfl⟩ (by norm_num))
theorem R54305 : Reach 54305 := rs (se 2 (by rfl) ⟨20364, by rfl⟩) (B 40729 (by norm_num) ⟨20364, by rfl⟩ (by norm_num))
theorem R54309 : Reach 54309 := rs (se 4 (by rfl) ⟨5091, by rfl⟩) (B 10183 (by norm_num) ⟨5091, by rfl⟩ (by norm_num))
theorem R185381 : Reach 185381 := rs (se 4 (by rfl) ⟨17379, by rfl⟩) (B 34759 (by norm_num) ⟨17379, by rfl⟩ (by norm_num))
theorem R54313 : Reach 54313 := rs (se 2 (by rfl) ⟨20367, by rfl⟩) (B 40735 (by norm_num) ⟨20367, by rfl⟩ (by norm_num))
theorem R54317 : Reach 54317 := rs (se 3 (by rfl) ⟨10184, by rfl⟩) (B 20369 (by norm_num) ⟨10184, by rfl⟩ (by norm_num))
theorem R54321 : Reach 54321 := rs (se 2 (by rfl) ⟨20370, by rfl⟩) (B 40741 (by norm_num) ⟨20370, by rfl⟩ (by norm_num))
theorem R119861 : Reach 119861 := rs (se 5 (by rfl) ⟨5618, by rfl⟩) (B 11237 (by norm_num) ⟨5618, by rfl⟩ (by norm_num))
theorem R54325 : Reach 54325 := rs (se 5 (by rfl) ⟨2546, by rfl⟩) (B 5093 (by norm_num) ⟨2546, by rfl⟩ (by norm_num))
theorem R54329 : Reach 54329 := rs (se 2 (by rfl) ⟨20373, by rfl⟩) (B 40747 (by norm_num) ⟨20373, by rfl⟩ (by norm_num))
theorem R54333 : Reach 54333 := rs (se 3 (by rfl) ⟨10187, by rfl⟩) (B 20375 (by norm_num) ⟨10187, by rfl⟩ (by norm_num))
theorem R54337 : Reach 54337 := rs (se 2 (by rfl) ⟨20376, by rfl⟩) (B 40753 (by norm_num) ⟨20376, by rfl⟩ (by norm_num))
theorem R54341 : Reach 54341 := rs (se 4 (by rfl) ⟨5094, by rfl⟩) (B 10189 (by norm_num) ⟨5094, by rfl⟩ (by norm_num))
theorem R54345 : Reach 54345 := rs (se 2 (by rfl) ⟨20379, by rfl⟩) (B 40759 (by norm_num) ⟨20379, by rfl⟩ (by norm_num))
theorem R54349 : Reach 54349 := rs (se 3 (by rfl) ⟨10190, by rfl⟩) (B 20381 (by norm_num) ⟨10190, by rfl⟩ (by norm_num))
theorem R54353 : Reach 54353 := rs (se 2 (by rfl) ⟨20382, by rfl⟩) (B 40765 (by norm_num) ⟨20382, by rfl⟩ (by norm_num))
theorem R54357 : Reach 54357 := rs (se 8 (by rfl) ⟨318, by rfl⟩) (B 637 (by norm_num) ⟨318, by rfl⟩ (by norm_num))
theorem R54361 : Reach 54361 := rs (se 2 (by rfl) ⟨20385, by rfl⟩) (B 40771 (by norm_num) ⟨20385, by rfl⟩ (by norm_num))
theorem R54365 : Reach 54365 := rs (se 3 (by rfl) ⟨10193, by rfl⟩) (B 20387 (by norm_num) ⟨10193, by rfl⟩ (by norm_num))
theorem R54369 : Reach 54369 := rs (se 2 (by rfl) ⟨20388, by rfl⟩) (B 40777 (by norm_num) ⟨20388, by rfl⟩ (by norm_num))
theorem R54373 : Reach 54373 := rs (se 4 (by rfl) ⟨5097, by rfl⟩) (B 10195 (by norm_num) ⟨5097, by rfl⟩ (by norm_num))
theorem R54377 : Reach 54377 := rs (se 2 (by rfl) ⟨20391, by rfl⟩) (B 40783 (by norm_num) ⟨20391, by rfl⟩ (by norm_num))
theorem R87149 : Reach 87149 := rs (se 3 (by rfl) ⟨16340, by rfl⟩) (B 32681 (by norm_num) ⟨16340, by rfl⟩ (by norm_num))
theorem R54381 : Reach 54381 := rs (se 3 (by rfl) ⟨10196, by rfl⟩) (B 20393 (by norm_num) ⟨10196, by rfl⟩ (by norm_num))
theorem R54385 : Reach 54385 := rs (se 2 (by rfl) ⟨20394, by rfl⟩) (B 40789 (by norm_num) ⟨20394, by rfl⟩ (by norm_num))
theorem R250997 : Reach 250997 := rs (se 5 (by rfl) ⟨11765, by rfl⟩) (B 23531 (by norm_num) ⟨11765, by rfl⟩ (by norm_num))
theorem R54389 : Reach 54389 := rs (se 5 (by rfl) ⟨2549, by rfl⟩) (B 5099 (by norm_num) ⟨2549, by rfl⟩ (by norm_num))
theorem R54393 : Reach 54393 := rs (se 2 (by rfl) ⟨20397, by rfl⟩) (B 40795 (by norm_num) ⟨20397, by rfl⟩ (by norm_num))
theorem R119933 : Reach 119933 := rs (se 3 (by rfl) ⟨22487, by rfl⟩) (B 44975 (by norm_num) ⟨22487, by rfl⟩ (by norm_num))
theorem R54397 : Reach 54397 := rs (se 3 (by rfl) ⟨10199, by rfl⟩) (B 20399 (by norm_num) ⟨10199, by rfl⟩ (by norm_num))
theorem R54401 : Reach 54401 := rs (se 2 (by rfl) ⟨20400, by rfl⟩) (B 40801 (by norm_num) ⟨20400, by rfl⟩ (by norm_num))
theorem R54405 : Reach 54405 := rs (se 4 (by rfl) ⟨5100, by rfl⟩) (B 10201 (by norm_num) ⟨5100, by rfl⟩ (by norm_num))
theorem R54409 : Reach 54409 := rs (se 2 (by rfl) ⟨20403, by rfl⟩) (B 40807 (by norm_num) ⟨20403, by rfl⟩ (by norm_num))
theorem R54413 : Reach 54413 := rs (se 3 (by rfl) ⟨10202, by rfl⟩) (B 20405 (by norm_num) ⟨10202, by rfl⟩ (by norm_num))
theorem R54417 : Reach 54417 := rs (se 2 (by rfl) ⟨20406, by rfl⟩) (B 40813 (by norm_num) ⟨20406, by rfl⟩ (by norm_num))
theorem R54421 : Reach 54421 := rs (se 6 (by rfl) ⟨1275, by rfl⟩) (B 2551 (by norm_num) ⟨1275, by rfl⟩ (by norm_num))
theorem R54425 : Reach 54425 := rs (se 2 (by rfl) ⟨20409, by rfl⟩) (B 40819 (by norm_num) ⟨20409, by rfl⟩ (by norm_num))
theorem R54429 : Reach 54429 := rs (se 3 (by rfl) ⟨10205, by rfl⟩) (B 20411 (by norm_num) ⟨10205, by rfl⟩ (by norm_num))
theorem R54433 : Reach 54433 := rs (se 2 (by rfl) ⟨20412, by rfl⟩) (B 40825 (by norm_num) ⟨20412, by rfl⟩ (by norm_num))
theorem R54437 : Reach 54437 := rs (se 4 (by rfl) ⟨5103, by rfl⟩) (B 10207 (by norm_num) ⟨5103, by rfl⟩ (by norm_num))
theorem R54441 : Reach 54441 := rs (se 2 (by rfl) ⟨20415, by rfl⟩) (B 40831 (by norm_num) ⟨20415, by rfl⟩ (by norm_num))
theorem R54445 : Reach 54445 := rs (se 3 (by rfl) ⟨10208, by rfl⟩) (B 20417 (by norm_num) ⟨10208, by rfl⟩ (by norm_num))
theorem R54449 : Reach 54449 := rs (se 2 (by rfl) ⟨20418, by rfl⟩) (B 40837 (by norm_num) ⟨20418, by rfl⟩ (by norm_num))
theorem R54453 : Reach 54453 := rs (se 5 (by rfl) ⟨2552, by rfl⟩) (B 5105 (by norm_num) ⟨2552, by rfl⟩ (by norm_num))
theorem R54457 : Reach 54457 := rs (se 2 (by rfl) ⟨20421, by rfl⟩) (B 40843 (by norm_num) ⟨20421, by rfl⟩ (by norm_num))
theorem R54461 : Reach 54461 := rs (se 3 (by rfl) ⟨10211, by rfl⟩) (B 20423 (by norm_num) ⟨10211, by rfl⟩ (by norm_num))
theorem R54465 : Reach 54465 := rs (se 2 (by rfl) ⟨20424, by rfl⟩) (B 40849 (by norm_num) ⟨20424, by rfl⟩ (by norm_num))
theorem R120005 : Reach 120005 := rs (se 4 (by rfl) ⟨11250, by rfl⟩) (B 22501 (by norm_num) ⟨11250, by rfl⟩ (by norm_num))
theorem R54469 : Reach 54469 := rs (se 4 (by rfl) ⟨5106, by rfl⟩) (B 10213 (by norm_num) ⟨5106, by rfl⟩ (by norm_num))
theorem R54473 : Reach 54473 := rs (se 2 (by rfl) ⟨20427, by rfl⟩) (B 40855 (by norm_num) ⟨20427, by rfl⟩ (by norm_num))
theorem R54477 : Reach 54477 := rs (se 3 (by rfl) ⟨10214, by rfl⟩) (B 20429 (by norm_num) ⟨10214, by rfl⟩ (by norm_num))
theorem R54481 : Reach 54481 := rs (se 2 (by rfl) ⟨20430, by rfl⟩) (B 40861 (by norm_num) ⟨20430, by rfl⟩ (by norm_num))
theorem R54485 : Reach 54485 := rs (se 7 (by rfl) ⟨638, by rfl⟩) (B 1277 (by norm_num) ⟨638, by rfl⟩ (by norm_num))
theorem R54489 : Reach 54489 := rs (se 2 (by rfl) ⟨20433, by rfl⟩) (B 40867 (by norm_num) ⟨20433, by rfl⟩ (by norm_num))
theorem R54493 : Reach 54493 := rs (se 3 (by rfl) ⟨10217, by rfl⟩) (B 20435 (by norm_num) ⟨10217, by rfl⟩ (by norm_num))
theorem R54497 : Reach 54497 := rs (se 2 (by rfl) ⟨20436, by rfl⟩) (B 40873 (by norm_num) ⟨20436, by rfl⟩ (by norm_num))
theorem R54501 : Reach 54501 := rs (se 4 (by rfl) ⟨5109, by rfl⟩) (B 10219 (by norm_num) ⟨5109, by rfl⟩ (by norm_num))
theorem R54505 : Reach 54505 := rs (se 2 (by rfl) ⟨20439, by rfl⟩) (B 40879 (by norm_num) ⟨20439, by rfl⟩ (by norm_num))
theorem R87277 : Reach 87277 := rs (se 3 (by rfl) ⟨16364, by rfl⟩) (B 32729 (by norm_num) ⟨16364, by rfl⟩ (by norm_num))
theorem R54509 : Reach 54509 := rs (se 3 (by rfl) ⟨10220, by rfl⟩) (B 20441 (by norm_num) ⟨10220, by rfl⟩ (by norm_num))
theorem R54513 : Reach 54513 := rs (se 2 (by rfl) ⟨20442, by rfl⟩) (B 40885 (by norm_num) ⟨20442, by rfl⟩ (by norm_num))
theorem R54517 : Reach 54517 := rs (se 5 (by rfl) ⟨2555, by rfl⟩) (B 5111 (by norm_num) ⟨2555, by rfl⟩ (by norm_num))
theorem R54521 : Reach 54521 := rs (se 2 (by rfl) ⟨20445, by rfl⟩) (B 40891 (by norm_num) ⟨20445, by rfl⟩ (by norm_num))
theorem R87293 : Reach 87293 := rs (se 3 (by rfl) ⟨16367, by rfl⟩) (B 32735 (by norm_num) ⟨16367, by rfl⟩ (by norm_num))
theorem R54525 : Reach 54525 := rs (se 3 (by rfl) ⟨10223, by rfl⟩) (B 20447 (by norm_num) ⟨10223, by rfl⟩ (by norm_num))
theorem R54529 : Reach 54529 := rs (se 2 (by rfl) ⟨20448, by rfl⟩) (B 40897 (by norm_num) ⟨20448, by rfl⟩ (by norm_num))
theorem R54533 : Reach 54533 := rs (se 4 (by rfl) ⟨5112, by rfl⟩) (B 10225 (by norm_num) ⟨5112, by rfl⟩ (by norm_num))
theorem R54537 : Reach 54537 := rs (se 2 (by rfl) ⟨20451, by rfl⟩) (B 40903 (by norm_num) ⟨20451, by rfl⟩ (by norm_num))
theorem R120077 : Reach 120077 := rs (se 3 (by rfl) ⟨22514, by rfl⟩) (B 45029 (by norm_num) ⟨22514, by rfl⟩ (by norm_num))
theorem R54541 : Reach 54541 := rs (se 3 (by rfl) ⟨10226, by rfl⟩) (B 20453 (by norm_num) ⟨10226, by rfl⟩ (by norm_num))
theorem R54545 : Reach 54545 := rs (se 2 (by rfl) ⟨20454, by rfl⟩) (B 40909 (by norm_num) ⟨20454, by rfl⟩ (by norm_num))
theorem R54549 : Reach 54549 := rs (se 6 (by rfl) ⟨1278, by rfl⟩) (B 2557 (by norm_num) ⟨1278, by rfl⟩ (by norm_num))
theorem R54553 : Reach 54553 := rs (se 2 (by rfl) ⟨20457, by rfl⟩) (B 40915 (by norm_num) ⟨20457, by rfl⟩ (by norm_num))
theorem R54557 : Reach 54557 := rs (se 3 (by rfl) ⟨10229, by rfl⟩) (B 20459 (by norm_num) ⟨10229, by rfl⟩ (by norm_num))
theorem R54561 : Reach 54561 := rs (se 2 (by rfl) ⟨20460, by rfl⟩) (B 40921 (by norm_num) ⟨20460, by rfl⟩ (by norm_num))
theorem R54565 : Reach 54565 := rs (se 4 (by rfl) ⟨5115, by rfl⟩) (B 10231 (by norm_num) ⟨5115, by rfl⟩ (by norm_num))
theorem R54569 : Reach 54569 := rs (se 2 (by rfl) ⟨20463, by rfl⟩) (B 40927 (by norm_num) ⟨20463, by rfl⟩ (by norm_num))
theorem R54573 : Reach 54573 := rs (se 3 (by rfl) ⟨10232, by rfl⟩) (B 20465 (by norm_num) ⟨10232, by rfl⟩ (by norm_num))
theorem R54577 : Reach 54577 := rs (se 2 (by rfl) ⟨20466, by rfl⟩) (B 40933 (by norm_num) ⟨20466, by rfl⟩ (by norm_num))
theorem R54581 : Reach 54581 := rs (se 5 (by rfl) ⟨2558, by rfl⟩) (B 5117 (by norm_num) ⟨2558, by rfl⟩ (by norm_num))
theorem R54585 : Reach 54585 := rs (se 2 (by rfl) ⟨20469, by rfl⟩) (B 40939 (by norm_num) ⟨20469, by rfl⟩ (by norm_num))
theorem R54589 : Reach 54589 := rs (se 3 (by rfl) ⟨10235, by rfl⟩) (B 20471 (by norm_num) ⟨10235, by rfl⟩ (by norm_num))
theorem R54593 : Reach 54593 := rs (se 2 (by rfl) ⟨20472, by rfl⟩) (B 40945 (by norm_num) ⟨20472, by rfl⟩ (by norm_num))
theorem R87365 : Reach 87365 := rs (se 4 (by rfl) ⟨8190, by rfl⟩) (B 16381 (by norm_num) ⟨8190, by rfl⟩ (by norm_num))
theorem R54597 : Reach 54597 := rs (se 4 (by rfl) ⟨5118, by rfl⟩) (B 10237 (by norm_num) ⟨5118, by rfl⟩ (by norm_num))
theorem R54601 : Reach 54601 := rs (se 2 (by rfl) ⟨20475, by rfl⟩) (B 40951 (by norm_num) ⟨20475, by rfl⟩ (by norm_num))
theorem R54605 : Reach 54605 := rs (se 3 (by rfl) ⟨10238, by rfl⟩) (B 20477 (by norm_num) ⟨10238, by rfl⟩ (by norm_num))
theorem R54609 : Reach 54609 := rs (se 2 (by rfl) ⟨20478, by rfl⟩) (B 40957 (by norm_num) ⟨20478, by rfl⟩ (by norm_num))
theorem R120149 : Reach 120149 := rs (se 15 (by rfl) ⟨5, by rfl⟩) (B 11 (by norm_num) ⟨5, by rfl⟩ (by norm_num))
theorem R54613 : Reach 54613 := rs (se 15 (by rfl) ⟨2, by rfl⟩) (B 5 (by norm_num) ⟨2, by rfl⟩ (by norm_num))
theorem R54617 : Reach 54617 := rs (se 2 (by rfl) ⟨20481, by rfl⟩) (B 40963 (by norm_num) ⟨20481, by rfl⟩ (by norm_num))
theorem R54621 : Reach 54621 := rs (se 3 (by rfl) ⟨10241, by rfl⟩) (B 20483 (by norm_num) ⟨10241, by rfl⟩ (by norm_num))
theorem R54625 : Reach 54625 := rs (se 2 (by rfl) ⟨20484, by rfl⟩) (B 40969 (by norm_num) ⟨20484, by rfl⟩ (by norm_num))
theorem R54629 : Reach 54629 := rs (se 4 (by rfl) ⟨5121, by rfl⟩) (B 10243 (by norm_num) ⟨5121, by rfl⟩ (by norm_num))
theorem R54633 : Reach 54633 := rs (se 2 (by rfl) ⟨20487, by rfl⟩) (B 40975 (by norm_num) ⟨20487, by rfl⟩ (by norm_num))
theorem R54637 : Reach 54637 := rs (se 3 (by rfl) ⟨10244, by rfl⟩) (B 20489 (by norm_num) ⟨10244, by rfl⟩ (by norm_num))
theorem R54641 : Reach 54641 := rs (se 2 (by rfl) ⟨20490, by rfl⟩) (B 40981 (by norm_num) ⟨20490, by rfl⟩ (by norm_num))
theorem R54645 : Reach 54645 := rs (se 5 (by rfl) ⟨2561, by rfl⟩) (B 5123 (by norm_num) ⟨2561, by rfl⟩ (by norm_num))
theorem R54649 : Reach 54649 := rs (se 2 (by rfl) ⟨20493, by rfl⟩) (B 40987 (by norm_num) ⟨20493, by rfl⟩ (by norm_num))
theorem R87421 : Reach 87421 := rs (se 3 (by rfl) ⟨16391, by rfl⟩) (B 32783 (by norm_num) ⟨16391, by rfl⟩ (by norm_num))
theorem R54653 : Reach 54653 := rs (se 3 (by rfl) ⟨10247, by rfl⟩) (B 20495 (by norm_num) ⟨10247, by rfl⟩ (by norm_num))
theorem R54657 : Reach 54657 := rs (se 2 (by rfl) ⟨20496, by rfl⟩) (B 40993 (by norm_num) ⟨20496, by rfl⟩ (by norm_num))
theorem R54661 : Reach 54661 := rs (se 4 (by rfl) ⟨5124, by rfl⟩) (B 10249 (by norm_num) ⟨5124, by rfl⟩ (by norm_num))
theorem R54665 : Reach 54665 := rs (se 2 (by rfl) ⟨20499, by rfl⟩) (B 40999 (by norm_num) ⟨20499, by rfl⟩ (by norm_num))
theorem R54669 : Reach 54669 := rs (se 3 (by rfl) ⟨10250, by rfl⟩) (B 20501 (by norm_num) ⟨10250, by rfl⟩ (by norm_num))
theorem R54673 : Reach 54673 := rs (se 2 (by rfl) ⟨20502, by rfl⟩) (B 41005 (by norm_num) ⟨20502, by rfl⟩ (by norm_num))
theorem R54677 : Reach 54677 := rs (se 6 (by rfl) ⟨1281, by rfl⟩) (B 2563 (by norm_num) ⟨1281, by rfl⟩ (by norm_num))
theorem R54681 : Reach 54681 := rs (se 2 (by rfl) ⟨20505, by rfl⟩) (B 41011 (by norm_num) ⟨20505, by rfl⟩ (by norm_num))
theorem R120221 : Reach 120221 := rs (se 3 (by rfl) ⟨22541, by rfl⟩) (B 45083 (by norm_num) ⟨22541, by rfl⟩ (by norm_num))
theorem R54685 : Reach 54685 := rs (se 3 (by rfl) ⟨10253, by rfl⟩) (B 20507 (by norm_num) ⟨10253, by rfl⟩ (by norm_num))
theorem R54689 : Reach 54689 := rs (se 2 (by rfl) ⟨20508, by rfl⟩) (B 41017 (by norm_num) ⟨20508, by rfl⟩ (by norm_num))
theorem R54693 : Reach 54693 := rs (se 4 (by rfl) ⟨5127, by rfl⟩) (B 10255 (by norm_num) ⟨5127, by rfl⟩ (by norm_num))
theorem R54697 : Reach 54697 := rs (se 2 (by rfl) ⟨20511, by rfl⟩) (B 41023 (by norm_num) ⟨20511, by rfl⟩ (by norm_num))
theorem R54701 : Reach 54701 := rs (se 3 (by rfl) ⟨10256, by rfl⟩) (B 20513 (by norm_num) ⟨10256, by rfl⟩ (by norm_num))
theorem R54705 : Reach 54705 := rs (se 2 (by rfl) ⟨20514, by rfl⟩) (B 41029 (by norm_num) ⟨20514, by rfl⟩ (by norm_num))
theorem R54709 : Reach 54709 := rs (se 5 (by rfl) ⟨2564, by rfl⟩) (B 5129 (by norm_num) ⟨2564, by rfl⟩ (by norm_num))
theorem R54713 : Reach 54713 := rs (se 2 (by rfl) ⟨20517, by rfl⟩) (B 41035 (by norm_num) ⟨20517, by rfl⟩ (by norm_num))
theorem R54717 : Reach 54717 := rs (se 3 (by rfl) ⟨10259, by rfl⟩) (B 20519 (by norm_num) ⟨10259, by rfl⟩ (by norm_num))
theorem R54721 : Reach 54721 := rs (se 2 (by rfl) ⟨20520, by rfl⟩) (B 41041 (by norm_num) ⟨20520, by rfl⟩ (by norm_num))
theorem R87493 : Reach 87493 := rs (se 4 (by rfl) ⟨8202, by rfl⟩) (B 16405 (by norm_num) ⟨8202, by rfl⟩ (by norm_num))
theorem R54725 : Reach 54725 := rs (se 4 (by rfl) ⟨5130, by rfl⟩) (B 10261 (by norm_num) ⟨5130, by rfl⟩ (by norm_num))
theorem R54729 : Reach 54729 := rs (se 2 (by rfl) ⟨20523, by rfl⟩) (B 41047 (by norm_num) ⟨20523, by rfl⟩ (by norm_num))
theorem R54733 : Reach 54733 := rs (se 3 (by rfl) ⟨10262, by rfl⟩) (B 20525 (by norm_num) ⟨10262, by rfl⟩ (by norm_num))
theorem R54737 : Reach 54737 := rs (se 2 (by rfl) ⟨20526, by rfl⟩) (B 41053 (by norm_num) ⟨20526, by rfl⟩ (by norm_num))
theorem R54741 : Reach 54741 := rs (se 7 (by rfl) ⟨641, by rfl⟩) (B 1283 (by norm_num) ⟨641, by rfl⟩ (by norm_num))
theorem R185813 : Reach 185813 := rs (se 7 (by rfl) ⟨2177, by rfl⟩) (B 4355 (by norm_num) ⟨2177, by rfl⟩ (by norm_num))
theorem R54745 : Reach 54745 := rs (se 2 (by rfl) ⟨20529, by rfl⟩) (B 41059 (by norm_num) ⟨20529, by rfl⟩ (by norm_num))
theorem R54749 : Reach 54749 := rs (se 3 (by rfl) ⟨10265, by rfl⟩) (B 20531 (by norm_num) ⟨10265, by rfl⟩ (by norm_num))
theorem R54753 : Reach 54753 := rs (se 2 (by rfl) ⟨20532, by rfl⟩) (B 41065 (by norm_num) ⟨20532, by rfl⟩ (by norm_num))
theorem R120293 : Reach 120293 := rs (se 4 (by rfl) ⟨11277, by rfl⟩) (B 22555 (by norm_num) ⟨11277, by rfl⟩ (by norm_num))
theorem R54757 : Reach 54757 := rs (se 4 (by rfl) ⟨5133, by rfl⟩) (B 10267 (by norm_num) ⟨5133, by rfl⟩ (by norm_num))
theorem R54761 : Reach 54761 := rs (se 2 (by rfl) ⟨20535, by rfl⟩) (B 41071 (by norm_num) ⟨20535, by rfl⟩ (by norm_num))
theorem R54765 : Reach 54765 := rs (se 3 (by rfl) ⟨10268, by rfl⟩) (B 20537 (by norm_num) ⟨10268, by rfl⟩ (by norm_num))
theorem R54769 : Reach 54769 := rs (se 2 (by rfl) ⟨20538, by rfl⟩) (B 41077 (by norm_num) ⟨20538, by rfl⟩ (by norm_num))
theorem R54773 : Reach 54773 := rs (se 5 (by rfl) ⟨2567, by rfl⟩) (B 5135 (by norm_num) ⟨2567, by rfl⟩ (by norm_num))
theorem R54777 : Reach 54777 := rs (se 2 (by rfl) ⟨20541, by rfl⟩) (B 41083 (by norm_num) ⟨20541, by rfl⟩ (by norm_num))
theorem R54781 : Reach 54781 := rs (se 3 (by rfl) ⟨10271, by rfl⟩) (B 20543 (by norm_num) ⟨10271, by rfl⟩ (by norm_num))
theorem R54785 : Reach 54785 := rs (se 2 (by rfl) ⟨20544, by rfl⟩) (B 41089 (by norm_num) ⟨20544, by rfl⟩ (by norm_num))
theorem R54789 : Reach 54789 := rs (se 4 (by rfl) ⟨5136, by rfl⟩) (B 10273 (by norm_num) ⟨5136, by rfl⟩ (by norm_num))
theorem R54793 : Reach 54793 := rs (se 2 (by rfl) ⟨20547, by rfl⟩) (B 41095 (by norm_num) ⟨20547, by rfl⟩ (by norm_num))
theorem R54797 : Reach 54797 := rs (se 3 (by rfl) ⟨10274, by rfl⟩) (B 20549 (by norm_num) ⟨10274, by rfl⟩ (by norm_num))
theorem R54801 : Reach 54801 := rs (se 2 (by rfl) ⟨20550, by rfl⟩) (B 41101 (by norm_num) ⟨20550, by rfl⟩ (by norm_num))
theorem R54805 : Reach 54805 := rs (se 6 (by rfl) ⟨1284, by rfl⟩) (B 2569 (by norm_num) ⟨1284, by rfl⟩ (by norm_num))
theorem R54809 : Reach 54809 := rs (se 2 (by rfl) ⟨20553, by rfl⟩) (B 41107 (by norm_num) ⟨20553, by rfl⟩ (by norm_num))
theorem R87581 : Reach 87581 := rs (se 3 (by rfl) ⟨16421, by rfl⟩) (B 32843 (by norm_num) ⟨16421, by rfl⟩ (by norm_num))
theorem R54813 : Reach 54813 := rs (se 3 (by rfl) ⟨10277, by rfl⟩) (B 20555 (by norm_num) ⟨10277, by rfl⟩ (by norm_num))
theorem R54817 : Reach 54817 := rs (se 2 (by rfl) ⟨20556, by rfl⟩) (B 41113 (by norm_num) ⟨20556, by rfl⟩ (by norm_num))
theorem R54821 : Reach 54821 := rs (se 4 (by rfl) ⟨5139, by rfl⟩) (B 10279 (by norm_num) ⟨5139, by rfl⟩ (by norm_num))
theorem R54825 : Reach 54825 := rs (se 2 (by rfl) ⟨20559, by rfl⟩) (B 41119 (by norm_num) ⟨20559, by rfl⟩ (by norm_num))
theorem R120365 : Reach 120365 := rs (se 3 (by rfl) ⟨22568, by rfl⟩) (B 45137 (by norm_num) ⟨22568, by rfl⟩ (by norm_num))
theorem R54829 : Reach 54829 := rs (se 3 (by rfl) ⟨10280, by rfl⟩) (B 20561 (by norm_num) ⟨10280, by rfl⟩ (by norm_num))
theorem R54833 : Reach 54833 := rs (se 2 (by rfl) ⟨20562, by rfl⟩) (B 41125 (by norm_num) ⟨20562, by rfl⟩ (by norm_num))
theorem R54837 : Reach 54837 := rs (se 5 (by rfl) ⟨2570, by rfl⟩) (B 5141 (by norm_num) ⟨2570, by rfl⟩ (by norm_num))
theorem R54841 : Reach 54841 := rs (se 2 (by rfl) ⟨20565, by rfl⟩) (B 41131 (by norm_num) ⟨20565, by rfl⟩ (by norm_num))
theorem R54845 : Reach 54845 := rs (se 3 (by rfl) ⟨10283, by rfl⟩) (B 20567 (by norm_num) ⟨10283, by rfl⟩ (by norm_num))
theorem R54849 : Reach 54849 := rs (se 2 (by rfl) ⟨20568, by rfl⟩) (B 41137 (by norm_num) ⟨20568, by rfl⟩ (by norm_num))
theorem R54853 : Reach 54853 := rs (se 4 (by rfl) ⟨5142, by rfl⟩) (B 10285 (by norm_num) ⟨5142, by rfl⟩ (by norm_num))
theorem R54857 : Reach 54857 := rs (se 2 (by rfl) ⟨20571, by rfl⟩) (B 41143 (by norm_num) ⟨20571, by rfl⟩ (by norm_num))
theorem R54861 : Reach 54861 := rs (se 3 (by rfl) ⟨10286, by rfl⟩) (B 20573 (by norm_num) ⟨10286, by rfl⟩ (by norm_num))
theorem R54865 : Reach 54865 := rs (se 2 (by rfl) ⟨20574, by rfl⟩) (B 41149 (by norm_num) ⟨20574, by rfl⟩ (by norm_num))
theorem R54869 : Reach 54869 := rs (se 8 (by rfl) ⟨321, by rfl⟩) (B 643 (by norm_num) ⟨321, by rfl⟩ (by norm_num))
theorem R54873 : Reach 54873 := rs (se 2 (by rfl) ⟨20577, by rfl⟩) (B 41155 (by norm_num) ⟨20577, by rfl⟩ (by norm_num))
theorem R54877 : Reach 54877 := rs (se 3 (by rfl) ⟨10289, by rfl⟩) (B 20579 (by norm_num) ⟨10289, by rfl⟩ (by norm_num))
theorem R54881 : Reach 54881 := rs (se 2 (by rfl) ⟨20580, by rfl⟩) (B 41161 (by norm_num) ⟨20580, by rfl⟩ (by norm_num))
theorem R54885 : Reach 54885 := rs (se 4 (by rfl) ⟨5145, by rfl⟩) (B 10291 (by norm_num) ⟨5145, by rfl⟩ (by norm_num))
theorem R54889 : Reach 54889 := rs (se 2 (by rfl) ⟨20583, by rfl⟩) (B 41167 (by norm_num) ⟨20583, by rfl⟩ (by norm_num))
theorem R54893 : Reach 54893 := rs (se 3 (by rfl) ⟨10292, by rfl⟩) (B 20585 (by norm_num) ⟨10292, by rfl⟩ (by norm_num))
theorem R54897 : Reach 54897 := rs (se 2 (by rfl) ⟨20586, by rfl⟩) (B 41173 (by norm_num) ⟨20586, by rfl⟩ (by norm_num))
theorem R120437 : Reach 120437 := rs (se 5 (by rfl) ⟨5645, by rfl⟩) (B 11291 (by norm_num) ⟨5645, by rfl⟩ (by norm_num))
theorem R54901 : Reach 54901 := rs (se 5 (by rfl) ⟨2573, by rfl⟩) (B 5147 (by norm_num) ⟨2573, by rfl⟩ (by norm_num))
theorem R54905 : Reach 54905 := rs (se 2 (by rfl) ⟨20589, by rfl⟩) (B 41179 (by norm_num) ⟨20589, by rfl⟩ (by norm_num))
theorem R54909 : Reach 54909 := rs (se 3 (by rfl) ⟨10295, by rfl⟩) (B 20591 (by norm_num) ⟨10295, by rfl⟩ (by norm_num))
theorem R54913 : Reach 54913 := rs (se 2 (by rfl) ⟨20592, by rfl⟩) (B 41185 (by norm_num) ⟨20592, by rfl⟩ (by norm_num))
theorem R54917 : Reach 54917 := rs (se 4 (by rfl) ⟨5148, by rfl⟩) (B 10297 (by norm_num) ⟨5148, by rfl⟩ (by norm_num))
theorem R54921 : Reach 54921 := rs (se 2 (by rfl) ⟨20595, by rfl⟩) (B 41191 (by norm_num) ⟨20595, by rfl⟩ (by norm_num))
theorem R54925 : Reach 54925 := rs (se 3 (by rfl) ⟨10298, by rfl⟩) (B 20597 (by norm_num) ⟨10298, by rfl⟩ (by norm_num))
theorem R54929 : Reach 54929 := rs (se 2 (by rfl) ⟨20598, by rfl⟩) (B 41197 (by norm_num) ⟨20598, by rfl⟩ (by norm_num))
theorem R54933 : Reach 54933 := rs (se 6 (by rfl) ⟨1287, by rfl⟩) (B 2575 (by norm_num) ⟨1287, by rfl⟩ (by norm_num))
theorem R54937 : Reach 54937 := rs (se 2 (by rfl) ⟨20601, by rfl⟩) (B 41203 (by norm_num) ⟨20601, by rfl⟩ (by norm_num))
theorem R87709 : Reach 87709 := rs (se 3 (by rfl) ⟨16445, by rfl⟩) (B 32891 (by norm_num) ⟨16445, by rfl⟩ (by norm_num))
theorem R54941 : Reach 54941 := rs (se 3 (by rfl) ⟨10301, by rfl⟩) (B 20603 (by norm_num) ⟨10301, by rfl⟩ (by norm_num))
theorem R54945 : Reach 54945 := rs (se 2 (by rfl) ⟨20604, by rfl⟩) (B 41209 (by norm_num) ⟨20604, by rfl⟩ (by norm_num))
theorem R54949 : Reach 54949 := rs (se 4 (by rfl) ⟨5151, by rfl⟩) (B 10303 (by norm_num) ⟨5151, by rfl⟩ (by norm_num))
theorem R54953 : Reach 54953 := rs (se 2 (by rfl) ⟨20607, by rfl⟩) (B 41215 (by norm_num) ⟨20607, by rfl⟩ (by norm_num))
theorem R54957 : Reach 54957 := rs (se 3 (by rfl) ⟨10304, by rfl⟩) (B 20609 (by norm_num) ⟨10304, by rfl⟩ (by norm_num))
theorem R54961 : Reach 54961 := rs (se 2 (by rfl) ⟨20610, by rfl⟩) (B 41221 (by norm_num) ⟨20610, by rfl⟩ (by norm_num))
theorem R54965 : Reach 54965 := rs (se 5 (by rfl) ⟨2576, by rfl⟩) (B 5153 (by norm_num) ⟨2576, by rfl⟩ (by norm_num))
theorem R54969 : Reach 54969 := rs (se 2 (by rfl) ⟨20613, by rfl⟩) (B 41227 (by norm_num) ⟨20613, by rfl⟩ (by norm_num))
theorem R120509 : Reach 120509 := rs (se 3 (by rfl) ⟨22595, by rfl⟩) (B 45191 (by norm_num) ⟨22595, by rfl⟩ (by norm_num))
theorem R54973 : Reach 54973 := rs (se 3 (by rfl) ⟨10307, by rfl⟩) (B 20615 (by norm_num) ⟨10307, by rfl⟩ (by norm_num))
theorem R54977 : Reach 54977 := rs (se 2 (by rfl) ⟨20616, by rfl⟩) (B 41233 (by norm_num) ⟨20616, by rfl⟩ (by norm_num))
theorem R218821 : Reach 218821 := rs (se 4 (by rfl) ⟨20514, by rfl⟩) (B 41029 (by norm_num) ⟨20514, by rfl⟩ (by norm_num))
theorem R54981 : Reach 54981 := rs (se 4 (by rfl) ⟨5154, by rfl⟩) (B 10309 (by norm_num) ⟨5154, by rfl⟩ (by norm_num))
theorem R54985 : Reach 54985 := rs (se 2 (by rfl) ⟨20619, by rfl⟩) (B 41239 (by norm_num) ⟨20619, by rfl⟩ (by norm_num))
theorem R54989 : Reach 54989 := rs (se 3 (by rfl) ⟨10310, by rfl⟩) (B 20621 (by norm_num) ⟨10310, by rfl⟩ (by norm_num))
theorem R54993 : Reach 54993 := rs (se 2 (by rfl) ⟨20622, by rfl⟩) (B 41245 (by norm_num) ⟨20622, by rfl⟩ (by norm_num))
theorem R218837 : Reach 218837 := rs (se 7 (by rfl) ⟨2564, by rfl⟩) (B 5129 (by norm_num) ⟨2564, by rfl⟩ (by norm_num))
theorem R54997 : Reach 54997 := rs (se 7 (by rfl) ⟨644, by rfl⟩) (B 1289 (by norm_num) ⟨644, by rfl⟩ (by norm_num))
theorem R55001 : Reach 55001 := rs (se 2 (by rfl) ⟨20625, by rfl⟩) (B 41251 (by norm_num) ⟨20625, by rfl⟩ (by norm_num))
theorem R55005 : Reach 55005 := rs (se 3 (by rfl) ⟨10313, by rfl⟩) (B 20627 (by norm_num) ⟨10313, by rfl⟩ (by norm_num))
theorem R55009 : Reach 55009 := rs (se 2 (by rfl) ⟨20628, by rfl⟩) (B 41257 (by norm_num) ⟨20628, by rfl⟩ (by norm_num))
theorem R55013 : Reach 55013 := rs (se 4 (by rfl) ⟨5157, by rfl⟩) (B 10315 (by norm_num) ⟨5157, by rfl⟩ (by norm_num))
theorem R55017 : Reach 55017 := rs (se 2 (by rfl) ⟨20631, by rfl⟩) (B 41263 (by norm_num) ⟨20631, by rfl⟩ (by norm_num))
theorem R55021 : Reach 55021 := rs (se 3 (by rfl) ⟨10316, by rfl⟩) (B 20633 (by norm_num) ⟨10316, by rfl⟩ (by norm_num))
theorem R55025 : Reach 55025 := rs (se 2 (by rfl) ⟨20634, by rfl⟩) (B 41269 (by norm_num) ⟨20634, by rfl⟩ (by norm_num))
theorem R87797 : Reach 87797 := rs (se 5 (by rfl) ⟨4115, by rfl⟩) (B 8231 (by norm_num) ⟨4115, by rfl⟩ (by norm_num))
theorem R55029 : Reach 55029 := rs (se 5 (by rfl) ⟨2579, by rfl⟩) (B 5159 (by norm_num) ⟨2579, by rfl⟩ (by norm_num))
theorem R55033 : Reach 55033 := rs (se 2 (by rfl) ⟨20637, by rfl⟩) (B 41275 (by norm_num) ⟨20637, by rfl⟩ (by norm_num))
theorem R87805 : Reach 87805 := rs (se 3 (by rfl) ⟨16463, by rfl⟩) (B 32927 (by norm_num) ⟨16463, by rfl⟩ (by norm_num))
theorem R55037 : Reach 55037 := rs (se 3 (by rfl) ⟨10319, by rfl⟩) (B 20639 (by norm_num) ⟨10319, by rfl⟩ (by norm_num))
theorem R55041 : Reach 55041 := rs (se 2 (by rfl) ⟨20640, by rfl⟩) (B 41281 (by norm_num) ⟨20640, by rfl⟩ (by norm_num))
theorem R120581 : Reach 120581 := rs (se 4 (by rfl) ⟨11304, by rfl⟩) (B 22609 (by norm_num) ⟨11304, by rfl⟩ (by norm_num))
theorem R55045 : Reach 55045 := rs (se 4 (by rfl) ⟨5160, by rfl⟩) (B 10321 (by norm_num) ⟨5160, by rfl⟩ (by norm_num))
theorem R55049 : Reach 55049 := rs (se 2 (by rfl) ⟨20643, by rfl⟩) (B 41287 (by norm_num) ⟨20643, by rfl⟩ (by norm_num))
theorem R55053 : Reach 55053 := rs (se 3 (by rfl) ⟨10322, by rfl⟩) (B 20645 (by norm_num) ⟨10322, by rfl⟩ (by norm_num))
theorem R55057 : Reach 55057 := rs (se 2 (by rfl) ⟨20646, by rfl⟩) (B 41293 (by norm_num) ⟨20646, by rfl⟩ (by norm_num))
theorem R55061 : Reach 55061 := rs (se 6 (by rfl) ⟨1290, by rfl⟩) (B 2581 (by norm_num) ⟨1290, by rfl⟩ (by norm_num))
theorem R55065 : Reach 55065 := rs (se 2 (by rfl) ⟨20649, by rfl⟩) (B 41299 (by norm_num) ⟨20649, by rfl⟩ (by norm_num))
theorem R55069 : Reach 55069 := rs (se 3 (by rfl) ⟨10325, by rfl⟩) (B 20651 (by norm_num) ⟨10325, by rfl⟩ (by norm_num))
theorem R55073 : Reach 55073 := rs (se 2 (by rfl) ⟨20652, by rfl⟩) (B 41305 (by norm_num) ⟨20652, by rfl⟩ (by norm_num))
theorem R55077 : Reach 55077 := rs (se 4 (by rfl) ⟨5163, by rfl⟩) (B 10327 (by norm_num) ⟨5163, by rfl⟩ (by norm_num))
theorem R55081 : Reach 55081 := rs (se 2 (by rfl) ⟨20655, by rfl⟩) (B 41311 (by norm_num) ⟨20655, by rfl⟩ (by norm_num))
theorem R55085 : Reach 55085 := rs (se 3 (by rfl) ⟨10328, by rfl⟩) (B 20657 (by norm_num) ⟨10328, by rfl⟩ (by norm_num))
theorem R55089 : Reach 55089 := rs (se 2 (by rfl) ⟨20658, by rfl⟩) (B 41317 (by norm_num) ⟨20658, by rfl⟩ (by norm_num))
theorem R55093 : Reach 55093 := rs (se 5 (by rfl) ⟨2582, by rfl⟩) (B 5165 (by norm_num) ⟨2582, by rfl⟩ (by norm_num))
theorem R55097 : Reach 55097 := rs (se 2 (by rfl) ⟨20661, by rfl⟩) (B 41323 (by norm_num) ⟨20661, by rfl⟩ (by norm_num))
theorem R55101 : Reach 55101 := rs (se 3 (by rfl) ⟨10331, by rfl⟩) (B 20663 (by norm_num) ⟨10331, by rfl⟩ (by norm_num))
theorem R55105 : Reach 55105 := rs (se 2 (by rfl) ⟨20664, by rfl⟩) (B 41329 (by norm_num) ⟨20664, by rfl⟩ (by norm_num))
theorem R55109 : Reach 55109 := rs (se 4 (by rfl) ⟨5166, by rfl⟩) (B 10333 (by norm_num) ⟨5166, by rfl⟩ (by norm_num))
theorem R55113 : Reach 55113 := rs (se 2 (by rfl) ⟨20667, by rfl⟩) (B 41335 (by norm_num) ⟨20667, by rfl⟩ (by norm_num))
theorem R120653 : Reach 120653 := rs (se 3 (by rfl) ⟨22622, by rfl⟩) (B 45245 (by norm_num) ⟨22622, by rfl⟩ (by norm_num))
theorem R55117 : Reach 55117 := rs (se 3 (by rfl) ⟨10334, by rfl⟩) (B 20669 (by norm_num) ⟨10334, by rfl⟩ (by norm_num))
theorem R87925 : Reach 87925 := rs (se 5 (by rfl) ⟨4121, by rfl⟩) (B 8243 (by norm_num) ⟨4121, by rfl⟩ (by norm_num))
theorem R120725 : Reach 120725 := rs (se 6 (by rfl) ⟨2829, by rfl⟩) (B 5659 (by norm_num) ⟨2829, by rfl⟩ (by norm_num))
theorem R88013 : Reach 88013 := rs (se 3 (by rfl) ⟨16502, by rfl⟩) (B 33005 (by norm_num) ⟨16502, by rfl⟩ (by norm_num))
theorem R120797 : Reach 120797 := rs (se 3 (by rfl) ⟨22649, by rfl⟩) (B 45299 (by norm_num) ⟨22649, by rfl⟩ (by norm_num))
theorem R88061 : Reach 88061 := rs (se 3 (by rfl) ⟨16511, by rfl⟩) (B 33023 (by norm_num) ⟨16511, by rfl⟩ (by norm_num))
theorem R55301 : Reach 55301 := rs (se 4 (by rfl) ⟨5184, by rfl⟩) (B 10369 (by norm_num) ⟨5184, by rfl⟩ (by norm_num))
theorem R55333 : Reach 55333 := rs (se 4 (by rfl) ⟨5187, by rfl⟩) (B 10375 (by norm_num) ⟨5187, by rfl⟩ (by norm_num))
theorem R120869 : Reach 120869 := rs (se 4 (by rfl) ⟨11331, by rfl⟩) (B 22663 (by norm_num) ⟨11331, by rfl⟩ (by norm_num))
theorem R88141 : Reach 88141 := rs (se 3 (by rfl) ⟨16526, by rfl⟩) (B 33053 (by norm_num) ⟨16526, by rfl⟩ (by norm_num))
theorem R120941 : Reach 120941 := rs (se 3 (by rfl) ⟨22676, by rfl⟩) (B 45353 (by norm_num) ⟨22676, by rfl⟩ (by norm_num))
theorem R88229 : Reach 88229 := rs (se 4 (by rfl) ⟨8271, by rfl⟩) (B 16543 (by norm_num) ⟨8271, by rfl⟩ (by norm_num))
theorem R121013 : Reach 121013 := rs (se 5 (by rfl) ⟨5672, by rfl⟩) (B 11345 (by norm_num) ⟨5672, by rfl⟩ (by norm_num))
theorem R121085 : Reach 121085 := rs (se 3 (by rfl) ⟨22703, by rfl⟩) (B 45407 (by norm_num) ⟨22703, by rfl⟩ (by norm_num))
theorem R55561 : Reach 55561 := rs (se 2 (by rfl) ⟨20835, by rfl⟩) (B 41671 (by norm_num) ⟨20835, by rfl⟩ (by norm_num))
theorem R121117 : Reach 121117 := rs (se 3 (by rfl) ⟨22709, by rfl⟩) (B 45419 (by norm_num) ⟨22709, by rfl⟩ (by norm_num))
theorem R88357 : Reach 88357 := rs (se 4 (by rfl) ⟨8283, by rfl⟩) (B 16567 (by norm_num) ⟨8283, by rfl⟩ (by norm_num))
theorem R121157 : Reach 121157 := rs (se 4 (by rfl) ⟨11358, by rfl⟩) (B 22717 (by norm_num) ⟨11358, by rfl⟩ (by norm_num))
theorem R88445 : Reach 88445 := rs (se 3 (by rfl) ⟨16583, by rfl⟩) (B 33167 (by norm_num) ⟨16583, by rfl⟩ (by norm_num))
theorem R121229 : Reach 121229 := rs (se 3 (by rfl) ⟨22730, by rfl⟩) (B 45461 (by norm_num) ⟨22730, by rfl⟩ (by norm_num))
theorem R252325 : Reach 252325 := rs (se 4 (by rfl) ⟨23655, by rfl⟩) (B 47311 (by norm_num) ⟨23655, by rfl⟩ (by norm_num))
theorem R55765 : Reach 55765 := rs (se 7 (by rfl) ⟨653, by rfl⟩) (B 1307 (by norm_num) ⟨653, by rfl⟩ (by norm_num))
theorem R121301 : Reach 121301 := rs (se 7 (by rfl) ⟨1421, by rfl⟩) (B 2843 (by norm_num) ⟨1421, by rfl⟩ (by norm_num))
theorem R88573 : Reach 88573 := rs (se 3 (by rfl) ⟨16607, by rfl⟩) (B 33215 (by norm_num) ⟨16607, by rfl⟩ (by norm_num))
theorem R55837 : Reach 55837 := rs (se 3 (by rfl) ⟨10469, by rfl⟩) (B 20939 (by norm_num) ⟨10469, by rfl⟩ (by norm_num))
theorem R121373 : Reach 121373 := rs (se 3 (by rfl) ⟨22757, by rfl⟩) (B 45515 (by norm_num) ⟨22757, by rfl⟩ (by norm_num))
theorem R88661 : Reach 88661 := rs (se 8 (by rfl) ⟨519, by rfl⟩) (B 1039 (by norm_num) ⟨519, by rfl⟩ (by norm_num))
theorem R121445 : Reach 121445 := rs (se 4 (by rfl) ⟨11385, by rfl⟩) (B 22771 (by norm_num) ⟨11385, by rfl⟩ (by norm_num))
theorem R121517 : Reach 121517 := rs (se 3 (by rfl) ⟨22784, by rfl⟩) (B 45569 (by norm_num) ⟨22784, by rfl⟩ (by norm_num))
theorem R88789 : Reach 88789 := rs (se 7 (by rfl) ⟨1040, by rfl⟩) (B 2081 (by norm_num) ⟨1040, by rfl⟩ (by norm_num))
theorem R88813 : Reach 88813 := rs (se 3 (by rfl) ⟨16652, by rfl⟩) (B 33305 (by norm_num) ⟨16652, by rfl⟩ (by norm_num))
theorem R121589 : Reach 121589 := rs (se 5 (by rfl) ⟨5699, by rfl⟩) (B 11399 (by norm_num) ⟨5699, by rfl⟩ (by norm_num))
theorem R416501 : Reach 416501 := rs (se 5 (by rfl) ⟨19523, by rfl⟩) (B 39047 (by norm_num) ⟨19523, by rfl⟩ (by norm_num))
theorem R88877 : Reach 88877 := rs (se 3 (by rfl) ⟨16664, by rfl⟩) (B 33329 (by norm_num) ⟨16664, by rfl⟩ (by norm_num))
theorem R121661 : Reach 121661 := rs (se 3 (by rfl) ⟨22811, by rfl⟩) (B 45623 (by norm_num) ⟨22811, by rfl⟩ (by norm_num))
theorem R121733 : Reach 121733 := rs (se 4 (by rfl) ⟨11412, by rfl⟩) (B 22825 (by norm_num) ⟨11412, by rfl⟩ (by norm_num))
theorem R56209 : Reach 56209 := rs (se 2 (by rfl) ⟨21078, by rfl⟩) (B 42157 (by norm_num) ⟨21078, by rfl⟩ (by norm_num))
theorem R187285 : Reach 187285 := rs (se 6 (by rfl) ⟨4389, by rfl⟩) (B 8779 (by norm_num) ⟨4389, by rfl⟩ (by norm_num))
theorem R89005 : Reach 89005 := rs (se 3 (by rfl) ⟨16688, by rfl⟩) (B 33377 (by norm_num) ⟨16688, by rfl⟩ (by norm_num))
theorem R121805 : Reach 121805 := rs (se 3 (by rfl) ⟨22838, by rfl⟩) (B 45677 (by norm_num) ⟨22838, by rfl⟩ (by norm_num))
theorem R89093 : Reach 89093 := rs (se 4 (by rfl) ⟨8352, by rfl⟩) (B 16705 (by norm_num) ⟨8352, by rfl⟩ (by norm_num))
theorem R121877 : Reach 121877 := rs (se 6 (by rfl) ⟨2856, by rfl⟩) (B 5713 (by norm_num) ⟨2856, by rfl⟩ (by norm_num))
theorem R121949 : Reach 121949 := rs (se 3 (by rfl) ⟨22865, by rfl⟩) (B 45731 (by norm_num) ⟨22865, by rfl⟩ (by norm_num))
theorem R89221 : Reach 89221 := rs (se 4 (by rfl) ⟨8364, by rfl⟩) (B 16729 (by norm_num) ⟨8364, by rfl⟩ (by norm_num))
theorem R122021 : Reach 122021 := rs (se 4 (by rfl) ⟨11439, by rfl⟩) (B 22879 (by norm_num) ⟨11439, by rfl⟩ (by norm_num))
theorem R89309 : Reach 89309 := rs (se 3 (by rfl) ⟨16745, by rfl⟩) (B 33491 (by norm_num) ⟨16745, by rfl⟩ (by norm_num))
theorem R122093 : Reach 122093 := rs (se 3 (by rfl) ⟨22892, by rfl⟩) (B 45785 (by norm_num) ⟨22892, by rfl⟩ (by norm_num))
theorem R56585 : Reach 56585 := rs (se 2 (by rfl) ⟨21219, by rfl⟩) (B 42439 (by norm_num) ⟨21219, by rfl⟩ (by norm_num))
theorem R122165 : Reach 122165 := rs (se 5 (by rfl) ⟨5726, by rfl⟩) (B 11453 (by norm_num) ⟨5726, by rfl⟩ (by norm_num))
theorem R89413 : Reach 89413 := rs (se 4 (by rfl) ⟨8382, by rfl⟩) (B 16765 (by norm_num) ⟨8382, by rfl⟩ (by norm_num))
theorem R56657 : Reach 56657 := rs (se 2 (by rfl) ⟨21246, by rfl⟩) (B 42493 (by norm_num) ⟨21246, by rfl⟩ (by norm_num))
theorem R89437 : Reach 89437 := rs (se 3 (by rfl) ⟨16769, by rfl⟩) (B 33539 (by norm_num) ⟨16769, by rfl⟩ (by norm_num))
theorem R122237 : Reach 122237 := rs (se 3 (by rfl) ⟨22919, by rfl⟩) (B 45839 (by norm_num) ⟨22919, by rfl⟩ (by norm_num))
theorem R89525 : Reach 89525 := rs (se 5 (by rfl) ⟨4196, by rfl⟩) (B 8393 (by norm_num) ⟨4196, by rfl⟩ (by norm_num))
theorem R122309 : Reach 122309 := rs (se 4 (by rfl) ⟨11466, by rfl⟩) (B 22933 (by norm_num) ⟨11466, by rfl⟩ (by norm_num))
theorem R155141 : Reach 155141 := rs (se 4 (by rfl) ⟨14544, by rfl⟩) (B 29089 (by norm_num) ⟨14544, by rfl⟩ (by norm_num))
theorem R56845 : Reach 56845 := rs (se 3 (by rfl) ⟨10658, by rfl⟩) (B 21317 (by norm_num) ⟨10658, by rfl⟩ (by norm_num))
theorem R122381 : Reach 122381 := rs (se 3 (by rfl) ⟨22946, by rfl⟩) (B 45893 (by norm_num) ⟨22946, by rfl⟩ (by norm_num))
theorem R89653 : Reach 89653 := rs (se 5 (by rfl) ⟨4202, by rfl⟩) (B 8405 (by norm_num) ⟨4202, by rfl⟩ (by norm_num))
theorem R122453 : Reach 122453 := rs (se 8 (by rfl) ⟨717, by rfl⟩) (B 1435 (by norm_num) ⟨717, by rfl⟩ (by norm_num))
theorem R89741 : Reach 89741 := rs (se 3 (by rfl) ⟨16826, by rfl⟩) (B 33653 (by norm_num) ⟨16826, by rfl⟩ (by norm_num))
theorem R122525 : Reach 122525 := rs (se 3 (by rfl) ⟨22973, by rfl⟩) (B 45947 (by norm_num) ⟨22973, by rfl⟩ (by norm_num))
theorem R57029 : Reach 57029 := rs (se 4 (by rfl) ⟨5346, by rfl⟩) (B 10693 (by norm_num) ⟨5346, by rfl⟩ (by norm_num))
theorem R122597 : Reach 122597 := rs (se 4 (by rfl) ⟨11493, by rfl⟩) (B 22987 (by norm_num) ⟨11493, by rfl⟩ (by norm_num))
theorem R89869 : Reach 89869 := rs (se 3 (by rfl) ⟨16850, by rfl⟩) (B 33701 (by norm_num) ⟨16850, by rfl⟩ (by norm_num))
theorem R122669 : Reach 122669 := rs (se 3 (by rfl) ⟨23000, by rfl⟩) (B 46001 (by norm_num) ⟨23000, by rfl⟩ (by norm_num))
theorem R384821 : Reach 384821 := rs (se 5 (by rfl) ⟨18038, by rfl⟩) (B 36077 (by norm_num) ⟨18038, by rfl⟩ (by norm_num))
theorem R89957 : Reach 89957 := rs (se 4 (by rfl) ⟨8433, by rfl⟩) (B 16867 (by norm_num) ⟨8433, by rfl⟩ (by norm_num))
theorem R122741 : Reach 122741 := rs (se 5 (by rfl) ⟨5753, by rfl⟩) (B 11507 (by norm_num) ⟨5753, by rfl⟩ (by norm_num))
theorem R221093 : Reach 221093 := rs (se 4 (by rfl) ⟨20727, by rfl⟩) (B 41455 (by norm_num) ⟨20727, by rfl⟩ (by norm_num))
theorem R122813 : Reach 122813 := rs (se 3 (by rfl) ⟨23027, by rfl⟩) (B 46055 (by norm_num) ⟨23027, by rfl⟩ (by norm_num))
theorem R90085 : Reach 90085 := rs (se 4 (by rfl) ⟨8445, by rfl⟩) (B 16891 (by norm_num) ⟨8445, by rfl⟩ (by norm_num))
theorem R122885 : Reach 122885 := rs (se 4 (by rfl) ⟨11520, by rfl⟩) (B 23041 (by norm_num) ⟨11520, by rfl⟩ (by norm_num))
theorem R90173 : Reach 90173 := rs (se 3 (by rfl) ⟨16907, by rfl⟩) (B 33815 (by norm_num) ⟨16907, by rfl⟩ (by norm_num))
theorem R122957 : Reach 122957 := rs (se 3 (by rfl) ⟨23054, by rfl⟩) (B 46109 (by norm_num) ⟨23054, by rfl⟩ (by norm_num))
theorem R680021 : Reach 680021 := rs (se 8 (by rfl) ⟨3984, by rfl⟩) (B 7969 (by norm_num) ⟨3984, by rfl⟩ (by norm_num))
theorem R123029 : Reach 123029 := rs (se 6 (by rfl) ⟨2883, by rfl⟩) (B 5767 (by norm_num) ⟨2883, by rfl⟩ (by norm_num))
theorem R90301 : Reach 90301 := rs (se 3 (by rfl) ⟨16931, by rfl⟩) (B 33863 (by norm_num) ⟨16931, by rfl⟩ (by norm_num))
theorem R57541 : Reach 57541 := rs (se 4 (by rfl) ⟨5394, by rfl⟩) (B 10789 (by norm_num) ⟨5394, by rfl⟩ (by norm_num))
theorem R123101 : Reach 123101 := rs (se 3 (by rfl) ⟨23081, by rfl⟩) (B 46163 (by norm_num) ⟨23081, by rfl⟩ (by norm_num))
theorem R57577 : Reach 57577 := rs (se 2 (by rfl) ⟨21591, by rfl⟩) (B 43183 (by norm_num) ⟨21591, by rfl⟩ (by norm_num))
theorem R57613 : Reach 57613 := rs (se 3 (by rfl) ⟨10802, by rfl⟩) (B 21605 (by norm_num) ⟨10802, by rfl⟩ (by norm_num))
theorem R90389 : Reach 90389 := rs (se 6 (by rfl) ⟨2118, by rfl⟩) (B 4237 (by norm_num) ⟨2118, by rfl⟩ (by norm_num))
theorem R123173 : Reach 123173 := rs (se 4 (by rfl) ⟨11547, by rfl⟩) (B 23095 (by norm_num) ⟨11547, by rfl⟩ (by norm_num))
theorem R57649 : Reach 57649 := rs (se 2 (by rfl) ⟨21618, by rfl⟩) (B 43237 (by norm_num) ⟨21618, by rfl⟩ (by norm_num))
theorem R57685 : Reach 57685 := rs (se 10 (by rfl) ⟨84, by rfl⟩) (B 169 (by norm_num) ⟨84, by rfl⟩ (by norm_num))
theorem R123245 : Reach 123245 := rs (se 3 (by rfl) ⟨23108, by rfl⟩) (B 46217 (by norm_num) ⟨23108, by rfl⟩ (by norm_num))
theorem R57721 : Reach 57721 := rs (se 2 (by rfl) ⟨21645, by rfl⟩) (B 43291 (by norm_num) ⟨21645, by rfl⟩ (by norm_num))
theorem R90517 : Reach 90517 := rs (se 6 (by rfl) ⟨2121, by rfl⟩) (B 4243 (by norm_num) ⟨2121, by rfl⟩ (by norm_num))
theorem R57757 : Reach 57757 := rs (se 3 (by rfl) ⟨10829, by rfl⟩) (B 21659 (by norm_num) ⟨10829, by rfl⟩ (by norm_num))
theorem R57781 : Reach 57781 := rs (se 5 (by rfl) ⟨2708, by rfl⟩) (B 5417 (by norm_num) ⟨2708, by rfl⟩ (by norm_num))
theorem R123317 : Reach 123317 := rs (se 5 (by rfl) ⟨5780, by rfl⟩) (B 11561 (by norm_num) ⟨5780, by rfl⟩ (by norm_num))
theorem R57793 : Reach 57793 := rs (se 2 (by rfl) ⟨21672, by rfl⟩) (B 43345 (by norm_num) ⟨21672, by rfl⟩ (by norm_num))
theorem R778709 : Reach 778709 := rs (se 7 (by rfl) ⟨9125, by rfl⟩) (B 18251 (by norm_num) ⟨9125, by rfl⟩ (by norm_num))
theorem R57829 : Reach 57829 := rs (se 4 (by rfl) ⟨5421, by rfl⟩) (B 10843 (by norm_num) ⟨5421, by rfl⟩ (by norm_num))
theorem R90605 : Reach 90605 := rs (se 3 (by rfl) ⟨16988, by rfl⟩) (B 33977 (by norm_num) ⟨16988, by rfl⟩ (by norm_num))
theorem R57853 : Reach 57853 := rs (se 3 (by rfl) ⟨10847, by rfl⟩) (B 21695 (by norm_num) ⟨10847, by rfl⟩ (by norm_num))
theorem R123389 : Reach 123389 := rs (se 3 (by rfl) ⟨23135, by rfl⟩) (B 46271 (by norm_num) ⟨23135, by rfl⟩ (by norm_num))
theorem R57865 : Reach 57865 := rs (se 2 (by rfl) ⟨21699, by rfl⟩) (B 43399 (by norm_num) ⟨21699, by rfl⟩ (by norm_num))
theorem R57901 : Reach 57901 := rs (se 3 (by rfl) ⟨10856, by rfl⟩) (B 21713 (by norm_num) ⟨10856, by rfl⟩ (by norm_num))
theorem R123461 : Reach 123461 := rs (se 4 (by rfl) ⟨11574, by rfl⟩) (B 23149 (by norm_num) ⟨11574, by rfl⟩ (by norm_num))
theorem R57937 : Reach 57937 := rs (se 2 (by rfl) ⟨21726, by rfl⟩) (B 43453 (by norm_num) ⟨21726, by rfl⟩ (by norm_num))
theorem R90733 : Reach 90733 := rs (se 3 (by rfl) ⟨17012, by rfl⟩) (B 34025 (by norm_num) ⟨17012, by rfl⟩ (by norm_num))
theorem R57973 : Reach 57973 := rs (se 5 (by rfl) ⟨2717, by rfl⟩) (B 5435 (by norm_num) ⟨2717, by rfl⟩ (by norm_num))
theorem R123533 : Reach 123533 := rs (se 3 (by rfl) ⟨23162, by rfl⟩) (B 46325 (by norm_num) ⟨23162, by rfl⟩ (by norm_num))
theorem R58009 : Reach 58009 := rs (se 2 (by rfl) ⟨21753, by rfl⟩) (B 43507 (by norm_num) ⟨21753, by rfl⟩ (by norm_num))
theorem R156325 : Reach 156325 := rs (se 4 (by rfl) ⟨14655, by rfl⟩) (B 29311 (by norm_num) ⟨14655, by rfl⟩ (by norm_num))
theorem R58033 : Reach 58033 := rs (se 2 (by rfl) ⟨21762, by rfl⟩) (B 43525 (by norm_num) ⟨21762, by rfl⟩ (by norm_num))
theorem R58045 : Reach 58045 := rs (se 3 (by rfl) ⟨10883, by rfl⟩) (B 21767 (by norm_num) ⟨10883, by rfl⟩ (by norm_num))
theorem R90821 : Reach 90821 := rs (se 4 (by rfl) ⟨8514, by rfl⟩) (B 17029 (by norm_num) ⟨8514, by rfl⟩ (by norm_num))
theorem R123605 : Reach 123605 := rs (se 7 (by rfl) ⟨1448, by rfl⟩) (B 2897 (by norm_num) ⟨1448, by rfl⟩ (by norm_num))
theorem R58081 : Reach 58081 := rs (se 2 (by rfl) ⟨21780, by rfl⟩) (B 43561 (by norm_num) ⟨21780, by rfl⟩ (by norm_num))
theorem R58117 : Reach 58117 := rs (se 4 (by rfl) ⟨5448, by rfl⟩) (B 10897 (by norm_num) ⟨5448, by rfl⟩ (by norm_num))
theorem R123677 : Reach 123677 := rs (se 3 (by rfl) ⟨23189, by rfl⟩) (B 46379 (by norm_num) ⟨23189, by rfl⟩ (by norm_num))
theorem R58153 : Reach 58153 := rs (se 2 (by rfl) ⟨21807, by rfl⟩) (B 43615 (by norm_num) ⟨21807, by rfl⟩ (by norm_num))
theorem R90949 : Reach 90949 := rs (se 4 (by rfl) ⟨8526, by rfl⟩) (B 17053 (by norm_num) ⟨8526, by rfl⟩ (by norm_num))
theorem R156485 : Reach 156485 := rs (se 4 (by rfl) ⟨14670, by rfl⟩) (B 29341 (by norm_num) ⟨14670, by rfl⟩ (by norm_num))
theorem R58189 : Reach 58189 := rs (se 3 (by rfl) ⟨10910, by rfl⟩) (B 21821 (by norm_num) ⟨10910, by rfl⟩ (by norm_num))
theorem R123749 : Reach 123749 := rs (se 4 (by rfl) ⟨11601, by rfl⟩) (B 23203 (by norm_num) ⟨11601, by rfl⟩ (by norm_num))
theorem R58225 : Reach 58225 := rs (se 2 (by rfl) ⟨21834, by rfl⟩) (B 43669 (by norm_num) ⟨21834, by rfl⟩ (by norm_num))
theorem R189317 : Reach 189317 := rs (se 4 (by rfl) ⟨17748, by rfl⟩) (B 35497 (by norm_num) ⟨17748, by rfl⟩ (by norm_num))
theorem R58261 : Reach 58261 := rs (se 6 (by rfl) ⟨1365, by rfl⟩) (B 2731 (by norm_num) ⟨1365, by rfl⟩ (by norm_num))
theorem R91037 : Reach 91037 := rs (se 3 (by rfl) ⟨17069, by rfl⟩) (B 34139 (by norm_num) ⟨17069, by rfl⟩ (by norm_num))
theorem R123821 : Reach 123821 := rs (se 3 (by rfl) ⟨23216, by rfl⟩) (B 46433 (by norm_num) ⟨23216, by rfl⟩ (by norm_num))
theorem R58297 : Reach 58297 := rs (se 2 (by rfl) ⟨21861, by rfl⟩) (B 43723 (by norm_num) ⟨21861, by rfl⟩ (by norm_num))
theorem R58333 : Reach 58333 := rs (se 3 (by rfl) ⟨10937, by rfl⟩) (B 21875 (by norm_num) ⟨10937, by rfl⟩ (by norm_num))
theorem R123893 : Reach 123893 := rs (se 5 (by rfl) ⟨5807, by rfl⟩) (B 11615 (by norm_num) ⟨5807, by rfl⟩ (by norm_num))
theorem R58369 : Reach 58369 := rs (se 2 (by rfl) ⟨21888, by rfl⟩) (B 43777 (by norm_num) ⟨21888, by rfl⟩ (by norm_num))
theorem R91165 : Reach 91165 := rs (se 3 (by rfl) ⟨17093, by rfl⟩) (B 34187 (by norm_num) ⟨17093, by rfl⟩ (by norm_num))
theorem R58405 : Reach 58405 := rs (se 4 (by rfl) ⟨5475, by rfl⟩) (B 10951 (by norm_num) ⟨5475, by rfl⟩ (by norm_num))
theorem R156725 : Reach 156725 := rs (se 5 (by rfl) ⟨7346, by rfl⟩) (B 14693 (by norm_num) ⟨7346, by rfl⟩ (by norm_num))
theorem R123965 : Reach 123965 := rs (se 3 (by rfl) ⟨23243, by rfl⟩) (B 46487 (by norm_num) ⟨23243, by rfl⟩ (by norm_num))
theorem R58441 : Reach 58441 := rs (se 2 (by rfl) ⟨21915, by rfl⟩) (B 43831 (by norm_num) ⟨21915, by rfl⟩ (by norm_num))
theorem R58477 : Reach 58477 := rs (se 3 (by rfl) ⟨10964, by rfl⟩) (B 21929 (by norm_num) ⟨10964, by rfl⟩ (by norm_num))
theorem R91253 : Reach 91253 := rs (se 5 (by rfl) ⟨4277, by rfl⟩) (B 8555 (by norm_num) ⟨4277, by rfl⟩ (by norm_num))
theorem R124037 : Reach 124037 := rs (se 4 (by rfl) ⟨11628, by rfl⟩) (B 23257 (by norm_num) ⟨11628, by rfl⟩ (by norm_num))
theorem R58513 : Reach 58513 := rs (se 2 (by rfl) ⟨21942, by rfl⟩) (B 43885 (by norm_num) ⟨21942, by rfl⟩ (by norm_num))
theorem R58549 : Reach 58549 := rs (se 5 (by rfl) ⟨2744, by rfl⟩) (B 5489 (by norm_num) ⟨2744, by rfl⟩ (by norm_num))
theorem R58585 : Reach 58585 := rs (se 2 (by rfl) ⟨21969, by rfl⟩) (B 43939 (by norm_num) ⟨21969, by rfl⟩ (by norm_num))
theorem R58601 : Reach 58601 := rs (se 2 (by rfl) ⟨21975, by rfl⟩) (B 43951 (by norm_num) ⟨21975, by rfl⟩ (by norm_num))
theorem R91381 : Reach 91381 := rs (se 5 (by rfl) ⟨4283, by rfl⟩) (B 8567 (by norm_num) ⟨4283, by rfl⟩ (by norm_num))
theorem R156917 : Reach 156917 := rs (se 5 (by rfl) ⟨7355, by rfl⟩) (B 14711 (by norm_num) ⟨7355, by rfl⟩ (by norm_num))
theorem R58621 : Reach 58621 := rs (se 3 (by rfl) ⟨10991, by rfl⟩) (B 21983 (by norm_num) ⟨10991, by rfl⟩ (by norm_num))
theorem R58657 : Reach 58657 := rs (se 2 (by rfl) ⟨21996, by rfl⟩) (B 43993 (by norm_num) ⟨21996, by rfl⟩ (by norm_num))
theorem R58693 : Reach 58693 := rs (se 4 (by rfl) ⟨5502, by rfl⟩) (B 11005 (by norm_num) ⟨5502, by rfl⟩ (by norm_num))
theorem R91469 : Reach 91469 := rs (se 3 (by rfl) ⟨17150, by rfl⟩) (B 34301 (by norm_num) ⟨17150, by rfl⟩ (by norm_num))
theorem R58729 : Reach 58729 := rs (se 2 (by rfl) ⟨22023, by rfl⟩) (B 44047 (by norm_num) ⟨22023, by rfl⟩ (by norm_num))
theorem R58765 : Reach 58765 := rs (se 3 (by rfl) ⟨11018, by rfl⟩) (B 22037 (by norm_num) ⟨11018, by rfl⟩ (by norm_num))
theorem R58801 : Reach 58801 := rs (se 2 (by rfl) ⟨22050, by rfl⟩) (B 44101 (by norm_num) ⟨22050, by rfl⟩ (by norm_num))
theorem R91597 : Reach 91597 := rs (se 3 (by rfl) ⟨17174, by rfl⟩) (B 34349 (by norm_num) ⟨17174, by rfl⟩ (by norm_num))
theorem R58837 : Reach 58837 := rs (se 7 (by rfl) ⟨689, by rfl⟩) (B 1379 (by norm_num) ⟨689, by rfl⟩ (by norm_num))
theorem R157157 : Reach 157157 := rs (se 4 (by rfl) ⟨14733, by rfl⟩) (B 29467 (by norm_num) ⟨14733, by rfl⟩ (by norm_num))
theorem R58853 : Reach 58853 := rs (se 4 (by rfl) ⟨5517, by rfl⟩) (B 11035 (by norm_num) ⟨5517, by rfl⟩ (by norm_num))
theorem R58873 : Reach 58873 := rs (se 2 (by rfl) ⟨22077, by rfl⟩) (B 44155 (by norm_num) ⟨22077, by rfl⟩ (by norm_num))
theorem R222725 : Reach 222725 := rs (se 4 (by rfl) ⟨20880, by rfl⟩) (B 41761 (by norm_num) ⟨20880, by rfl⟩ (by norm_num))
theorem R58909 : Reach 58909 := rs (se 3 (by rfl) ⟨11045, by rfl⟩) (B 22091 (by norm_num) ⟨11045, by rfl⟩ (by norm_num))
theorem R91685 : Reach 91685 := rs (se 4 (by rfl) ⟨8595, by rfl⟩) (B 17191 (by norm_num) ⟨8595, by rfl⟩ (by norm_num))
theorem R58945 : Reach 58945 := rs (se 2 (by rfl) ⟨22104, by rfl⟩) (B 44209 (by norm_num) ⟨22104, by rfl⟩ (by norm_num))
theorem R58981 : Reach 58981 := rs (se 4 (by rfl) ⟨5529, by rfl⟩) (B 11059 (by norm_num) ⟨5529, by rfl⟩ (by norm_num))
theorem R59017 : Reach 59017 := rs (se 2 (by rfl) ⟨22131, by rfl⟩) (B 44263 (by norm_num) ⟨22131, by rfl⟩ (by norm_num))
theorem R91813 : Reach 91813 := rs (se 4 (by rfl) ⟨8607, by rfl⟩) (B 17215 (by norm_num) ⟨8607, by rfl⟩ (by norm_num))
theorem R59053 : Reach 59053 := rs (se 3 (by rfl) ⟨11072, by rfl⟩) (B 22145 (by norm_num) ⟨11072, by rfl⟩ (by norm_num))
theorem R59089 : Reach 59089 := rs (se 2 (by rfl) ⟨22158, by rfl⟩) (B 44317 (by norm_num) ⟨22158, by rfl⟩ (by norm_num))
theorem R190181 : Reach 190181 := rs (se 4 (by rfl) ⟨17829, by rfl⟩) (B 35659 (by norm_num) ⟨17829, by rfl⟩ (by norm_num))
theorem R59125 : Reach 59125 := rs (se 5 (by rfl) ⟨2771, by rfl⟩) (B 5543 (by norm_num) ⟨2771, by rfl⟩ (by norm_num))
theorem R91901 : Reach 91901 := rs (se 3 (by rfl) ⟨17231, by rfl⟩) (B 34463 (by norm_num) ⟨17231, by rfl⟩ (by norm_num))
theorem R517909 : Reach 517909 := rs (se 6 (by rfl) ⟨12138, by rfl⟩) (B 24277 (by norm_num) ⟨12138, by rfl⟩ (by norm_num))
theorem R59161 : Reach 59161 := rs (se 2 (by rfl) ⟨22185, by rfl⟩) (B 44371 (by norm_num) ⟨22185, by rfl⟩ (by norm_num))
theorem R59197 : Reach 59197 := rs (se 3 (by rfl) ⟨11099, by rfl⟩) (B 22199 (by norm_num) ⟨11099, by rfl⟩ (by norm_num))
theorem R59233 : Reach 59233 := rs (se 2 (by rfl) ⟨22212, by rfl⟩) (B 44425 (by norm_num) ⟨22212, by rfl⟩ (by norm_num))
theorem R92029 : Reach 92029 := rs (se 3 (by rfl) ⟨17255, by rfl⟩) (B 34511 (by norm_num) ⟨17255, by rfl⟩ (by norm_num))
theorem R59269 : Reach 59269 := rs (se 4 (by rfl) ⟨5556, by rfl⟩) (B 11113 (by norm_num) ⟨5556, by rfl⟩ (by norm_num))
theorem R59305 : Reach 59305 := rs (se 2 (by rfl) ⟨22239, by rfl⟩) (B 44479 (by norm_num) ⟨22239, by rfl⟩ (by norm_num))
theorem R59341 : Reach 59341 := rs (se 3 (by rfl) ⟨11126, by rfl⟩) (B 22253 (by norm_num) ⟨11126, by rfl⟩ (by norm_num))
theorem R92117 : Reach 92117 := rs (se 7 (by rfl) ⟨1079, by rfl⟩) (B 2159 (by norm_num) ⟨1079, by rfl⟩ (by norm_num))
theorem R59377 : Reach 59377 := rs (se 2 (by rfl) ⟨22266, by rfl⟩) (B 44533 (by norm_num) ⟨22266, by rfl⟩ (by norm_num))
theorem R59413 : Reach 59413 := rs (se 6 (by rfl) ⟨1392, by rfl⟩) (B 2785 (by norm_num) ⟨1392, by rfl⟩ (by norm_num))
theorem R59449 : Reach 59449 := rs (se 2 (by rfl) ⟨22293, by rfl⟩) (B 44587 (by norm_num) ⟨22293, by rfl⟩ (by norm_num))
theorem R92245 : Reach 92245 := rs (se 8 (by rfl) ⟨540, by rfl⟩) (B 1081 (by norm_num) ⟨540, by rfl⟩ (by norm_num))
theorem R59485 : Reach 59485 := rs (se 3 (by rfl) ⟨11153, by rfl⟩) (B 22307 (by norm_num) ⟨11153, by rfl⟩ (by norm_num))
theorem R59521 : Reach 59521 := rs (se 2 (by rfl) ⟨22320, by rfl⟩) (B 44641 (by norm_num) ⟨22320, by rfl⟩ (by norm_num))
theorem R59557 : Reach 59557 := rs (se 4 (by rfl) ⟨5583, by rfl⟩) (B 11167 (by norm_num) ⟨5583, by rfl⟩ (by norm_num))
theorem R92333 : Reach 92333 := rs (se 3 (by rfl) ⟨17312, by rfl⟩) (B 34625 (by norm_num) ⟨17312, by rfl⟩ (by norm_num))
theorem R59593 : Reach 59593 := rs (se 2 (by rfl) ⟨22347, by rfl⟩) (B 44695 (by norm_num) ⟨22347, by rfl⟩ (by norm_num))
theorem R256229 : Reach 256229 := rs (se 4 (by rfl) ⟨24021, by rfl⟩) (B 48043 (by norm_num) ⟨24021, by rfl⟩ (by norm_num))
theorem R59629 : Reach 59629 := rs (se 3 (by rfl) ⟨11180, by rfl⟩) (B 22361 (by norm_num) ⟨11180, by rfl⟩ (by norm_num))
theorem R59665 : Reach 59665 := rs (se 2 (by rfl) ⟨22374, by rfl⟩) (B 44749 (by norm_num) ⟨22374, by rfl⟩ (by norm_num))
theorem R190757 : Reach 190757 := rs (se 4 (by rfl) ⟨17883, by rfl⟩) (B 35767 (by norm_num) ⟨17883, by rfl⟩ (by norm_num))
theorem R92461 : Reach 92461 := rs (se 3 (by rfl) ⟨17336, by rfl⟩) (B 34673 (by norm_num) ⟨17336, by rfl⟩ (by norm_num))
theorem R59701 : Reach 59701 := rs (se 5 (by rfl) ⟨2798, by rfl⟩) (B 5597 (by norm_num) ⟨2798, by rfl⟩ (by norm_num))
theorem R59737 : Reach 59737 := rs (se 2 (by rfl) ⟨22401, by rfl⟩) (B 44803 (by norm_num) ⟨22401, by rfl⟩ (by norm_num))
theorem R59773 : Reach 59773 := rs (se 3 (by rfl) ⟨11207, by rfl⟩) (B 22415 (by norm_num) ⟨11207, by rfl⟩ (by norm_num))
theorem R92549 : Reach 92549 := rs (se 4 (by rfl) ⟨8676, by rfl⟩) (B 17353 (by norm_num) ⟨8676, by rfl⟩ (by norm_num))
theorem R59809 : Reach 59809 := rs (se 2 (by rfl) ⟨22428, by rfl⟩) (B 44857 (by norm_num) ⟨22428, by rfl⟩ (by norm_num))
theorem R387509 : Reach 387509 := rs (se 5 (by rfl) ⟨18164, by rfl⟩) (B 36329 (by norm_num) ⟨18164, by rfl⟩ (by norm_num))
theorem R59845 : Reach 59845 := rs (se 4 (by rfl) ⟨5610, by rfl⟩) (B 11221 (by norm_num) ⟨5610, by rfl⟩ (by norm_num))
theorem R59881 : Reach 59881 := rs (se 2 (by rfl) ⟨22455, by rfl⟩) (B 44911 (by norm_num) ⟨22455, by rfl⟩ (by norm_num))
theorem R92677 : Reach 92677 := rs (se 4 (by rfl) ⟨8688, by rfl⟩) (B 17377 (by norm_num) ⟨8688, by rfl⟩ (by norm_num))
theorem R59917 : Reach 59917 := rs (se 3 (by rfl) ⟨11234, by rfl⟩) (B 22469 (by norm_num) ⟨11234, by rfl⟩ (by norm_num))
theorem R125477 : Reach 125477 := rs (se 4 (by rfl) ⟨11763, by rfl⟩) (B 23527 (by norm_num) ⟨11763, by rfl⟩ (by norm_num))
theorem R59953 : Reach 59953 := rs (se 2 (by rfl) ⟨22482, by rfl⟩) (B 44965 (by norm_num) ⟨22482, by rfl⟩ (by norm_num))
theorem R59989 : Reach 59989 := rs (se 8 (by rfl) ⟨351, by rfl⟩) (B 703 (by norm_num) ⟨351, by rfl⟩ (by norm_num))
theorem R92765 : Reach 92765 := rs (se 3 (by rfl) ⟨17393, by rfl⟩) (B 34787 (by norm_num) ⟨17393, by rfl⟩ (by norm_num))
theorem R60025 : Reach 60025 := rs (se 2 (by rfl) ⟨22509, by rfl⟩) (B 45019 (by norm_num) ⟨22509, by rfl⟩ (by norm_num))
theorem R60061 : Reach 60061 := rs (se 3 (by rfl) ⟨11261, by rfl⟩) (B 22523 (by norm_num) ⟨11261, by rfl⟩ (by norm_num))
theorem R60097 : Reach 60097 := rs (se 2 (by rfl) ⟨22536, by rfl⟩) (B 45073 (by norm_num) ⟨22536, by rfl⟩ (by norm_num))
theorem R92893 : Reach 92893 := rs (se 3 (by rfl) ⟨17417, by rfl⟩) (B 34835 (by norm_num) ⟨17417, by rfl⟩ (by norm_num))
theorem R60133 : Reach 60133 := rs (se 4 (by rfl) ⟨5637, by rfl⟩) (B 11275 (by norm_num) ⟨5637, by rfl⟩ (by norm_num))
theorem R60169 : Reach 60169 := rs (se 2 (by rfl) ⟨22563, by rfl⟩) (B 45127 (by norm_num) ⟨22563, by rfl⟩ (by norm_num))
theorem R60193 : Reach 60193 := rs (se 2 (by rfl) ⟨22572, by rfl⟩) (B 45145 (by norm_num) ⟨22572, by rfl⟩ (by norm_num))
theorem R60205 : Reach 60205 := rs (se 3 (by rfl) ⟨11288, by rfl⟩) (B 22577 (by norm_num) ⟨11288, by rfl⟩ (by norm_num))
theorem R125749 : Reach 125749 := rs (se 5 (by rfl) ⟨5894, by rfl⟩) (B 11789 (by norm_num) ⟨5894, by rfl⟩ (by norm_num))
theorem R92981 : Reach 92981 := rs (se 5 (by rfl) ⟨4358, by rfl⟩) (B 8717 (by norm_num) ⟨4358, by rfl⟩ (by norm_num))
theorem R60241 : Reach 60241 := rs (se 2 (by rfl) ⟨22590, by rfl⟩) (B 45181 (by norm_num) ⟨22590, by rfl⟩ (by norm_num))
theorem R60277 : Reach 60277 := rs (se 5 (by rfl) ⟨2825, by rfl⟩) (B 5651 (by norm_num) ⟨2825, by rfl⟩ (by norm_num))
theorem R93053 : Reach 93053 := rs (se 3 (by rfl) ⟨17447, by rfl⟩) (B 34895 (by norm_num) ⟨17447, by rfl⟩ (by norm_num))
theorem R60313 : Reach 60313 := rs (se 2 (by rfl) ⟨22617, by rfl⟩) (B 45235 (by norm_num) ⟨22617, by rfl⟩ (by norm_num))
theorem R93109 : Reach 93109 := rs (se 5 (by rfl) ⟨4364, by rfl⟩) (B 8729 (by norm_num) ⟨4364, by rfl⟩ (by norm_num))
theorem R60349 : Reach 60349 := rs (se 3 (by rfl) ⟨11315, by rfl⟩) (B 22631 (by norm_num) ⟨11315, by rfl⟩ (by norm_num))
theorem R60385 : Reach 60385 := rs (se 2 (by rfl) ⟨22644, by rfl⟩) (B 45289 (by norm_num) ⟨22644, by rfl⟩ (by norm_num))
theorem R125941 : Reach 125941 := rs (se 5 (by rfl) ⟨5903, by rfl⟩) (B 11807 (by norm_num) ⟨5903, by rfl⟩ (by norm_num))
theorem R60421 : Reach 60421 := rs (se 4 (by rfl) ⟨5664, by rfl⟩) (B 11329 (by norm_num) ⟨5664, by rfl⟩ (by norm_num))
theorem R125981 : Reach 125981 := rs (se 3 (by rfl) ⟨23621, by rfl⟩) (B 47243 (by norm_num) ⟨23621, by rfl⟩ (by norm_num))
theorem R60457 : Reach 60457 := rs (se 2 (by rfl) ⟨22671, by rfl⟩) (B 45343 (by norm_num) ⟨22671, by rfl⟩ (by norm_num))
theorem R60493 : Reach 60493 := rs (se 3 (by rfl) ⟨11342, by rfl⟩) (B 22685 (by norm_num) ⟨11342, by rfl⟩ (by norm_num))
theorem R60529 : Reach 60529 := rs (se 2 (by rfl) ⟨22698, by rfl⟩) (B 45397 (by norm_num) ⟨22698, by rfl⟩ (by norm_num))
theorem R60565 : Reach 60565 := rs (se 6 (by rfl) ⟨1419, by rfl⟩) (B 2839 (by norm_num) ⟨1419, by rfl⟩ (by norm_num))
theorem R60601 : Reach 60601 := rs (se 2 (by rfl) ⟨22725, by rfl⟩) (B 45451 (by norm_num) ⟨22725, by rfl⟩ (by norm_num))
theorem R60637 : Reach 60637 := rs (se 3 (by rfl) ⟨11369, by rfl⟩) (B 22739 (by norm_num) ⟨11369, by rfl⟩ (by norm_num))
theorem R60673 : Reach 60673 := rs (se 2 (by rfl) ⟨22752, by rfl⟩) (B 45505 (by norm_num) ⟨22752, by rfl⟩ (by norm_num))
theorem R93469 : Reach 93469 := rs (se 3 (by rfl) ⟨17525, by rfl⟩) (B 35051 (by norm_num) ⟨17525, by rfl⟩ (by norm_num))
theorem R60709 : Reach 60709 := rs (se 4 (by rfl) ⟨5691, by rfl⟩) (B 11383 (by norm_num) ⟨5691, by rfl⟩ (by norm_num))
theorem R93485 : Reach 93485 := rs (se 3 (by rfl) ⟨17528, by rfl⟩) (B 35057 (by norm_num) ⟨17528, by rfl⟩ (by norm_num))
theorem R126269 : Reach 126269 := rs (se 3 (by rfl) ⟨23675, by rfl⟩) (B 47351 (by norm_num) ⟨23675, by rfl⟩ (by norm_num))
theorem R60745 : Reach 60745 := rs (se 2 (by rfl) ⟨22779, by rfl⟩) (B 45559 (by norm_num) ⟨22779, by rfl⟩ (by norm_num))
theorem R93533 : Reach 93533 := rs (se 3 (by rfl) ⟨17537, by rfl⟩) (B 35075 (by norm_num) ⟨17537, by rfl⟩ (by norm_num))
theorem R60781 : Reach 60781 := rs (se 3 (by rfl) ⟨11396, by rfl⟩) (B 22793 (by norm_num) ⟨11396, by rfl⟩ (by norm_num))
theorem R60817 : Reach 60817 := rs (se 2 (by rfl) ⟨22806, by rfl⟩) (B 45613 (by norm_num) ⟨22806, by rfl⟩ (by norm_num))
theorem R60853 : Reach 60853 := rs (se 5 (by rfl) ⟨2852, by rfl⟩) (B 5705 (by norm_num) ⟨2852, by rfl⟩ (by norm_num))
theorem R60889 : Reach 60889 := rs (se 2 (by rfl) ⟨22833, by rfl⟩) (B 45667 (by norm_num) ⟨22833, by rfl⟩ (by norm_num))
theorem R60925 : Reach 60925 := rs (se 3 (by rfl) ⟨11423, by rfl⟩) (B 22847 (by norm_num) ⟨11423, by rfl⟩ (by norm_num))
theorem R60961 : Reach 60961 := rs (se 2 (by rfl) ⟨22860, by rfl⟩) (B 45721 (by norm_num) ⟨22860, by rfl⟩ (by norm_num))
theorem R60997 : Reach 60997 := rs (se 4 (by rfl) ⟨5718, by rfl⟩) (B 11437 (by norm_num) ⟨5718, by rfl⟩ (by norm_num))
theorem R61033 : Reach 61033 := rs (se 2 (by rfl) ⟨22887, by rfl⟩) (B 45775 (by norm_num) ⟨22887, by rfl⟩ (by norm_num))
theorem R61069 : Reach 61069 := rs (se 3 (by rfl) ⟨11450, by rfl⟩) (B 22901 (by norm_num) ⟨11450, by rfl⟩ (by norm_num))
theorem R61105 : Reach 61105 := rs (se 2 (by rfl) ⟨22914, by rfl⟩) (B 45829 (by norm_num) ⟨22914, by rfl⟩ (by norm_num))
theorem R61141 : Reach 61141 := rs (se 7 (by rfl) ⟨716, by rfl⟩) (B 1433 (by norm_num) ⟨716, by rfl⟩ (by norm_num))
theorem R61177 : Reach 61177 := rs (se 2 (by rfl) ⟨22941, by rfl⟩) (B 45883 (by norm_num) ⟨22941, by rfl⟩ (by norm_num))
theorem R61213 : Reach 61213 := rs (se 3 (by rfl) ⟨11477, by rfl⟩) (B 22955 (by norm_num) ⟨11477, by rfl⟩ (by norm_num))
theorem R61249 : Reach 61249 := rs (se 2 (by rfl) ⟨22968, by rfl⟩) (B 45937 (by norm_num) ⟨22968, by rfl⟩ (by norm_num))
theorem R225125 : Reach 225125 := rs (se 4 (by rfl) ⟨21105, by rfl⟩) (B 42211 (by norm_num) ⟨21105, by rfl⟩ (by norm_num))
theorem R61285 : Reach 61285 := rs (se 4 (by rfl) ⟨5745, by rfl⟩) (B 11491 (by norm_num) ⟨5745, by rfl⟩ (by norm_num))
theorem R61321 : Reach 61321 := rs (se 2 (by rfl) ⟨22995, by rfl⟩) (B 45991 (by norm_num) ⟨22995, by rfl⟩ (by norm_num))
theorem R61357 : Reach 61357 := rs (se 3 (by rfl) ⟨11504, by rfl⟩) (B 23009 (by norm_num) ⟨11504, by rfl⟩ (by norm_num))
theorem R61393 : Reach 61393 := rs (se 2 (by rfl) ⟨23022, by rfl⟩) (B 46045 (by norm_num) ⟨23022, by rfl⟩ (by norm_num))
theorem R61429 : Reach 61429 := rs (se 5 (by rfl) ⟨2879, by rfl⟩) (B 5759 (by norm_num) ⟨2879, by rfl⟩ (by norm_num))
theorem R61441 : Reach 61441 := rs (se 2 (by rfl) ⟨23040, by rfl⟩) (B 46081 (by norm_num) ⟨23040, by rfl⟩ (by norm_num))
theorem R61465 : Reach 61465 := rs (se 2 (by rfl) ⟨23049, by rfl⟩) (B 46099 (by norm_num) ⟨23049, by rfl⟩ (by norm_num))
theorem R127037 : Reach 127037 := rs (se 3 (by rfl) ⟨23819, by rfl⟩) (B 47639 (by norm_num) ⟨23819, by rfl⟩ (by norm_num))
theorem R61501 : Reach 61501 := rs (se 3 (by rfl) ⟨11531, by rfl⟩) (B 23063 (by norm_num) ⟨11531, by rfl⟩ (by norm_num))
theorem R94277 : Reach 94277 := rs (se 4 (by rfl) ⟨8838, by rfl⟩) (B 17677 (by norm_num) ⟨8838, by rfl⟩ (by norm_num))
theorem R61537 : Reach 61537 := rs (se 2 (by rfl) ⟨23076, by rfl⟩) (B 46153 (by norm_num) ⟨23076, by rfl⟩ (by norm_num))
theorem R61573 : Reach 61573 := rs (se 4 (by rfl) ⟨5772, by rfl⟩) (B 11545 (by norm_num) ⟨5772, by rfl⟩ (by norm_num))
theorem R61597 : Reach 61597 := rs (se 3 (by rfl) ⟨11549, by rfl⟩) (B 23099 (by norm_num) ⟨11549, by rfl⟩ (by norm_num))
theorem R61609 : Reach 61609 := rs (se 2 (by rfl) ⟨23103, by rfl⟩) (B 46207 (by norm_num) ⟨23103, by rfl⟩ (by norm_num))
theorem R61645 : Reach 61645 := rs (se 3 (by rfl) ⟨11558, by rfl⟩) (B 23117 (by norm_num) ⟨11558, by rfl⟩ (by norm_num))
theorem R61681 : Reach 61681 := rs (se 2 (by rfl) ⟨23130, by rfl⟩) (B 46261 (by norm_num) ⟨23130, by rfl⟩ (by norm_num))
theorem R61717 : Reach 61717 := rs (se 6 (by rfl) ⟨1446, by rfl⟩) (B 2893 (by norm_num) ⟨1446, by rfl⟩ (by norm_num))
theorem R61753 : Reach 61753 := rs (se 2 (by rfl) ⟨23157, by rfl⟩) (B 46315 (by norm_num) ⟨23157, by rfl⟩ (by norm_num))
theorem R61789 : Reach 61789 := rs (se 3 (by rfl) ⟨11585, by rfl⟩) (B 23171 (by norm_num) ⟨11585, by rfl⟩ (by norm_num))
theorem R94565 : Reach 94565 := rs (se 4 (by rfl) ⟨8865, by rfl⟩) (B 17731 (by norm_num) ⟨8865, by rfl⟩ (by norm_num))
theorem R61813 : Reach 61813 := rs (se 5 (by rfl) ⟨2897, by rfl⟩) (B 5795 (by norm_num) ⟨2897, by rfl⟩ (by norm_num))
theorem R61817 : Reach 61817 := rs (se 2 (by rfl) ⟨23181, by rfl⟩) (B 46363 (by norm_num) ⟨23181, by rfl⟩ (by norm_num))
theorem R61825 : Reach 61825 := rs (se 2 (by rfl) ⟨23184, by rfl⟩) (B 46369 (by norm_num) ⟨23184, by rfl⟩ (by norm_num))
theorem R61861 : Reach 61861 := rs (se 4 (by rfl) ⟨5799, by rfl⟩) (B 11599 (by norm_num) ⟨5799, by rfl⟩ (by norm_num))
theorem R61897 : Reach 61897 := rs (se 2 (by rfl) ⟨23211, by rfl⟩) (B 46423 (by norm_num) ⟨23211, by rfl⟩ (by norm_num))
theorem R61933 : Reach 61933 := rs (se 3 (by rfl) ⟨11612, by rfl⟩) (B 23225 (by norm_num) ⟨11612, by rfl⟩ (by norm_num))
theorem R61969 : Reach 61969 := rs (se 2 (by rfl) ⟨23238, by rfl⟩) (B 46477 (by norm_num) ⟨23238, by rfl⟩ (by norm_num))
theorem R62005 : Reach 62005 := rs (se 5 (by rfl) ⟨2906, by rfl⟩) (B 5813 (by norm_num) ⟨2906, by rfl⟩ (by norm_num))
theorem R291509 : Reach 291509 := rs (se 5 (by rfl) ⟨13664, by rfl⟩) (B 27329 (by norm_num) ⟨13664, by rfl⟩ (by norm_num))
theorem R62317 : Reach 62317 := rs (se 3 (by rfl) ⟨11684, by rfl⟩) (B 23369 (by norm_num) ⟨11684, by rfl⟩ (by norm_num))
theorem R62413 : Reach 62413 := rs (se 3 (by rfl) ⟨11702, by rfl⟩) (B 23405 (by norm_num) ⟨11702, by rfl⟩ (by norm_num))
theorem R259109 : Reach 259109 := rs (se 4 (by rfl) ⟨24291, by rfl⟩) (B 48583 (by norm_num) ⟨24291, by rfl⟩ (by norm_num))
theorem R324821 : Reach 324821 := rs (se 7 (by rfl) ⟨3806, by rfl⟩) (B 7613 (by norm_num) ⟨3806, by rfl⟩ (by norm_num))
theorem R488693 : Reach 488693 := rs (se 5 (by rfl) ⟨22907, by rfl⟩) (B 45815 (by norm_num) ⟨22907, by rfl⟩ (by norm_num))
theorem R455989 : Reach 455989 := rs (se 5 (by rfl) ⟨21374, by rfl⟩) (B 42749 (by norm_num) ⟨21374, by rfl⟩ (by norm_num))
theorem R226901 : Reach 226901 := rs (se 8 (by rfl) ⟨1329, by rfl⟩) (B 2659 (by norm_num) ⟨1329, by rfl⟩ (by norm_num))
theorem R259685 : Reach 259685 := rs (se 4 (by rfl) ⟨24345, by rfl⟩) (B 48691 (by norm_num) ⟨24345, by rfl⟩ (by norm_num))
theorem R358037 : Reach 358037 := rs (se 6 (by rfl) ⟨8391, by rfl⟩) (B 16783 (by norm_num) ⟨8391, by rfl⟩ (by norm_num))
theorem R521909 : Reach 521909 := rs (se 5 (by rfl) ⟨24464, by rfl⟩) (B 48929 (by norm_num) ⟨24464, by rfl⟩ (by norm_num))
theorem R980693 : Reach 980693 := rs (se 7 (by rfl) ⟨11492, by rfl⟩) (B 22985 (by norm_num) ⟨11492, by rfl⟩ (by norm_num))
theorem R194309 : Reach 194309 := rs (se 4 (by rfl) ⟨18216, by rfl⟩) (B 36433 (by norm_num) ⟨18216, by rfl⟩ (by norm_num))
theorem R96013 : Reach 96013 := rs (se 3 (by rfl) ⟨18002, by rfl⟩) (B 36005 (by norm_num) ⟨18002, by rfl⟩ (by norm_num))
theorem R292693 : Reach 292693 := rs (se 9 (by rfl) ⟨857, by rfl⟩) (B 1715 (by norm_num) ⟨857, by rfl⟩ (by norm_num))
theorem R63389 : Reach 63389 := rs (se 3 (by rfl) ⟨11885, by rfl⟩) (B 23771 (by norm_num) ⟨11885, by rfl⟩ (by norm_num))
theorem R96157 : Reach 96157 := rs (se 3 (by rfl) ⟨18029, by rfl⟩) (B 36059 (by norm_num) ⟨18029, by rfl⟩ (by norm_num))
theorem R63865 : Reach 63865 := rs (se 2 (by rfl) ⟨23949, by rfl⟩) (B 47899 (by norm_num) ⟨23949, by rfl⟩ (by norm_num))
theorem R63893 : Reach 63893 := rs (se 6 (by rfl) ⟨1497, by rfl⟩) (B 2995 (by norm_num) ⟨1497, by rfl⟩ (by norm_num))
theorem R1505749 : Reach 1505749 := rs (se 7 (by rfl) ⟨17645, by rfl⟩) (B 35291 (by norm_num) ⟨17645, by rfl⟩ (by norm_num))
theorem R129509 : Reach 129509 := rs (se 4 (by rfl) ⟨12141, by rfl⟩) (B 24283 (by norm_num) ⟨12141, by rfl⟩ (by norm_num))
theorem R227893 : Reach 227893 := rs (se 5 (by rfl) ⟨10682, by rfl⟩) (B 21365 (by norm_num) ⟨10682, by rfl⟩ (by norm_num))
theorem R64081 : Reach 64081 := rs (se 2 (by rfl) ⟨24030, by rfl⟩) (B 48061 (by norm_num) ⟨24030, by rfl⟩ (by norm_num))
theorem R129701 : Reach 129701 := rs (se 4 (by rfl) ⟨12159, by rfl⟩) (B 24319 (by norm_num) ⟨12159, by rfl⟩ (by norm_num))
theorem R96965 : Reach 96965 := rs (se 4 (by rfl) ⟨9090, by rfl⟩) (B 18181 (by norm_num) ⟨9090, by rfl⟩ (by norm_num))
theorem R64201 : Reach 64201 := rs (se 2 (by rfl) ⟨24075, by rfl⟩) (B 48151 (by norm_num) ⟨24075, by rfl⟩ (by norm_num))
theorem R129853 : Reach 129853 := rs (se 3 (by rfl) ⟨24347, by rfl⟩) (B 48695 (by norm_num) ⟨24347, by rfl⟩ (by norm_num))
theorem R97109 : Reach 97109 := rs (se 9 (by rfl) ⟨284, by rfl⟩) (B 569 (by norm_num) ⟨284, by rfl⟩ (by norm_num))
theorem R260981 : Reach 260981 := rs (se 5 (by rfl) ⟨12233, by rfl⟩) (B 24467 (by norm_num) ⟨12233, by rfl⟩ (by norm_num))
theorem R195493 : Reach 195493 := rs (se 4 (by rfl) ⟨18327, by rfl⟩) (B 36655 (by norm_num) ⟨18327, by rfl⟩ (by norm_num))
theorem R130045 : Reach 130045 := rs (se 3 (by rfl) ⟨24383, by rfl⟩) (B 48767 (by norm_num) ⟨24383, by rfl⟩ (by norm_num))
theorem R130157 : Reach 130157 := rs (se 3 (by rfl) ⟨24404, by rfl⟩) (B 48809 (by norm_num) ⟨24404, by rfl⟩ (by norm_num))
theorem R261301 : Reach 261301 := rs (se 5 (by rfl) ⟨12248, by rfl⟩) (B 24497 (by norm_num) ⟨12248, by rfl⟩ (by norm_num))
theorem R195797 : Reach 195797 := rs (se 7 (by rfl) ⟨2294, by rfl⟩) (B 4589 (by norm_num) ⟨2294, by rfl⟩ (by norm_num))
theorem R64729 : Reach 64729 := rs (se 2 (by rfl) ⟨24273, by rfl⟩) (B 48547 (by norm_num) ⟨24273, by rfl⟩ (by norm_num))
theorem R457973 : Reach 457973 := rs (se 5 (by rfl) ⟨21467, by rfl⟩) (B 42935 (by norm_num) ⟨21467, by rfl⟩ (by norm_num))
theorem R130349 : Reach 130349 := rs (se 3 (by rfl) ⟨24440, by rfl⟩) (B 48881 (by norm_num) ⟨24440, by rfl⟩ (by norm_num))
theorem R64901 : Reach 64901 := rs (se 4 (by rfl) ⟨6084, by rfl⟩) (B 12169 (by norm_num) ⟨6084, by rfl⟩ (by norm_num))
theorem R64957 : Reach 64957 := rs (se 3 (by rfl) ⟨12179, by rfl⟩) (B 24359 (by norm_num) ⟨12179, by rfl⟩ (by norm_num))
theorem R130517 : Reach 130517 := rs (se 7 (by rfl) ⟨1529, by rfl⟩) (B 3059 (by norm_num) ⟨1529, by rfl⟩ (by norm_num))
theorem R65053 : Reach 65053 := rs (se 3 (by rfl) ⟨12197, by rfl⟩) (B 24395 (by norm_num) ⟨12197, by rfl⟩ (by norm_num))
theorem R97861 : Reach 97861 := rs (se 4 (by rfl) ⟨9174, by rfl⟩) (B 18349 (by norm_num) ⟨9174, by rfl⟩ (by norm_num))
theorem R65117 : Reach 65117 := rs (se 3 (by rfl) ⟨12209, by rfl⟩) (B 24419 (by norm_num) ⟨12209, by rfl⟩ (by norm_num))
theorem R130693 : Reach 130693 := rs (se 4 (by rfl) ⟨12252, by rfl⟩) (B 24505 (by norm_num) ⟨12252, by rfl⟩ (by norm_num))
theorem R65225 : Reach 65225 := rs (se 2 (by rfl) ⟨24459, by rfl⟩) (B 48919 (by norm_num) ⟨24459, by rfl⟩ (by norm_num))
theorem R98005 : Reach 98005 := rs (se 7 (by rfl) ⟨1148, by rfl⟩) (B 2297 (by norm_num) ⟨1148, by rfl⟩ (by norm_num))
theorem R130805 : Reach 130805 := rs (se 5 (by rfl) ⟨6131, by rfl⟩) (B 12263 (by norm_num) ⟨6131, by rfl⟩ (by norm_num))
theorem R65281 : Reach 65281 := rs (se 2 (by rfl) ⟨24480, by rfl⟩) (B 48961 (by norm_num) ⟨24480, by rfl⟩ (by norm_num))
theorem R294677 : Reach 294677 := rs (se 6 (by rfl) ⟨6906, by rfl⟩) (B 13813 (by norm_num) ⟨6906, by rfl⟩ (by norm_num))
theorem R1408853 : Reach 1408853 := rs (se 9 (by rfl) ⟨4127, by rfl⟩) (B 8255 (by norm_num) ⟨4127, by rfl⟩ (by norm_num))
theorem R65377 : Reach 65377 := rs (se 2 (by rfl) ⟨24516, by rfl⟩) (B 49033 (by norm_num) ⟨24516, by rfl⟩ (by norm_num))
theorem R98165 : Reach 98165 := rs (se 5 (by rfl) ⟨4601, by rfl⟩) (B 9203 (by norm_num) ⟨4601, by rfl⟩ (by norm_num))
theorem R130997 : Reach 130997 := rs (se 5 (by rfl) ⟨6140, by rfl⟩) (B 12281 (by norm_num) ⟨6140, by rfl⟩ (by norm_num))
theorem R393173 : Reach 393173 := rs (se 7 (by rfl) ⟨4607, by rfl⟩) (B 9215 (by norm_num) ⟨4607, by rfl⟩ (by norm_num))
theorem R688085 : Reach 688085 := rs (se 7 (by rfl) ⟨8063, by rfl⟩) (B 16127 (by norm_num) ⟨8063, by rfl⟩ (by norm_num))
theorem R65539 : Reach 65539 := rs (se 1 (by rfl) ⟨49154, by rfl⟩) R98309
theorem R327685 : Reach 327685 := rs (se 4 (by rfl) ⟨30720, by rfl⟩) R61441
theorem R295109 : Reach 295109 := rs (se 4 (by rfl) ⟨27666, by rfl⟩) R55333
theorem R98723 : Reach 98723 := rs (se 1 (by rfl) ⟨74042, by rfl⟩) R148085
theorem R360931 : Reach 360931 := rs (se 1 (by rfl) ⟨270698, by rfl⟩) R541397
theorem R66035 : Reach 66035 := rs (se 1 (by rfl) ⟨49526, by rfl⟩) R99053
theorem R98833 : Reach 98833 := rs (se 2 (by rfl) ⟨37062, by rfl⟩) R74125
theorem R98851 : Reach 98851 := rs (se 1 (by rfl) ⟨74138, by rfl⟩) R148277
theorem R393797 : Reach 393797 := rs (se 4 (by rfl) ⟨36918, by rfl⟩) R73837
theorem R131665 : Reach 131665 := rs (se 2 (by rfl) ⟨49374, by rfl⟩) R98749
theorem R262925 : Reach 262925 := rs (se 3 (by rfl) ⟨49298, by rfl⟩) R98597
theorem R131939 : Reach 131939 := rs (se 1 (by rfl) ⟨98954, by rfl⟩) R197909
theorem R99235 : Reach 99235 := rs (se 1 (by rfl) ⟨74426, by rfl⟩) R148853
theorem R99281 : Reach 99281 := rs (se 2 (by rfl) ⟨37230, by rfl⟩) R74461
theorem R164845 : Reach 164845 := rs (se 3 (by rfl) ⟨30908, by rfl⟩) R61817
theorem R132131 : Reach 132131 := rs (se 1 (by rfl) ⟨99098, by rfl⟩) R198197
theorem R66739 : Reach 66739 := rs (se 1 (by rfl) ⟨50054, by rfl⟩) R100109
theorem R230627 : Reach 230627 := rs (se 1 (by rfl) ⟨172970, by rfl⟩) R345941
theorem R99569 : Reach 99569 := rs (se 2 (by rfl) ⟨37338, by rfl⟩) R74677
theorem R66835 : Reach 66835 := rs (se 1 (by rfl) ⟨50126, by rfl⟩) R100253
theorem R197923 : Reach 197923 := rs (se 1 (by rfl) ⟨148442, by rfl⟩) R296885
theorem R165347 : Reach 165347 := rs (se 1 (by rfl) ⟨124010, by rfl⟩) R248021
theorem R67331 : Reach 67331 := rs (se 1 (by rfl) ⟨50498, by rfl⟩) R100997
theorem R100291 : Reach 100291 := rs (se 1 (by rfl) ⟨75218, by rfl⟩) R150437
theorem R329669 : Reach 329669 := rs (se 4 (by rfl) ⟨30906, by rfl⟩) R61813
theorem R133073 : Reach 133073 := rs (se 2 (by rfl) ⟨49902, by rfl⟩) R99805
theorem R133123 : Reach 133123 := rs (se 1 (by rfl) ⟨99842, by rfl⟩) R199685
theorem R133265 : Reach 133265 := rs (se 2 (by rfl) ⟨49974, by rfl⟩) R99949
theorem R690545 : Reach 690545 := rs (se 2 (by rfl) ⟨258954, by rfl⟩) R517909
theorem R100739 : Reach 100739 := rs (se 1 (by rfl) ⟨75554, by rfl⟩) R151109
theorem R68035 : Reach 68035 := rs (se 1 (by rfl) ⟨51026, by rfl⟩) R102053
theorem R68131 : Reach 68131 := rs (se 1 (by rfl) ⟨51098, by rfl⟩) R102197
theorem R232013 : Reach 232013 := rs (se 3 (by rfl) ⟨43502, by rfl⟩) R87005
theorem R756337 : Reach 756337 := rs (se 2 (by rfl) ⟨283626, by rfl⟩) R567253
theorem R101027 : Reach 101027 := rs (se 1 (by rfl) ⟨75770, by rfl⟩) R151541
theorem R1018595 : Reach 1018595 := rs (se 1 (by rfl) ⟨763946, by rfl⟩) R1527893
theorem R166691 : Reach 166691 := rs (se 1 (by rfl) ⟨125018, by rfl⟩) R250037
theorem R265037 : Reach 265037 := rs (se 3 (by rfl) ⟨49694, by rfl⟩) R99389
theorem R68465 : Reach 68465 := rs (se 2 (by rfl) ⟨25674, by rfl⟩) R51349
theorem R68627 : Reach 68627 := rs (se 1 (by rfl) ⟨51470, by rfl⟩) R102941
theorem R887921 : Reach 887921 := rs (se 2 (by rfl) ⟨332970, by rfl⟩) R665941
theorem R134257 : Reach 134257 := rs (se 2 (by rfl) ⟨50346, by rfl⟩) R100693
theorem R134531 : Reach 134531 := rs (se 1 (by rfl) ⟨100898, by rfl⟩) R201797
theorem R200141 : Reach 200141 := rs (se 3 (by rfl) ⟨37526, by rfl⟩) R75053
theorem R69169 : Reach 69169 := rs (se 2 (by rfl) ⟨25938, by rfl⟩) R51877
theorem R134723 : Reach 134723 := rs (se 1 (by rfl) ⟨101042, by rfl⟩) R202085
theorem R101969 : Reach 101969 := rs (se 2 (by rfl) ⟨38238, by rfl⟩) R76477
theorem R265841 : Reach 265841 := rs (se 2 (by rfl) ⟨99690, by rfl⟩) R199381
theorem R69265 : Reach 69265 := rs (se 2 (by rfl) ⟨25974, by rfl⟩) R51949
theorem R69331 : Reach 69331 := rs (se 1 (by rfl) ⟨51998, by rfl⟩) R103997
theorem R167665 : Reach 167665 := rs (se 2 (by rfl) ⟨62874, by rfl⟩) R125749
theorem R69427 : Reach 69427 := rs (se 1 (by rfl) ⟨52070, by rfl⟩) R104141
theorem R167921 : Reach 167921 := rs (se 2 (by rfl) ⟨62970, by rfl⟩) R125941
theorem R69745 : Reach 69745 := rs (se 2 (by rfl) ⟨26154, by rfl⟩) R52309
theorem R69761 : Reach 69761 := rs (se 2 (by rfl) ⟨26160, by rfl⟩) R52321
theorem R69859 : Reach 69859 := rs (se 1 (by rfl) ⟨52394, by rfl⟩) R104789
theorem R758069 : Reach 758069 := rs (se 5 (by rfl) ⟨35534, by rfl⟩) R71069
theorem R692549 : Reach 692549 := rs (se 4 (by rfl) ⟨64926, by rfl⟩) R129853
theorem R102865 : Reach 102865 := rs (se 2 (by rfl) ⟨38574, by rfl⟩) R77149
theorem R135665 : Reach 135665 := rs (se 2 (by rfl) ⟨50874, by rfl⟩) R101749
theorem R135715 : Reach 135715 := rs (se 1 (by rfl) ⟨101786, by rfl⟩) R203573
theorem R103025 : Reach 103025 := rs (se 2 (by rfl) ⟨38634, by rfl⟩) R77269
theorem R135857 : Reach 135857 := rs (se 2 (by rfl) ⟨50946, by rfl⟩) R101893
theorem R70417 : Reach 70417 := rs (se 2 (by rfl) ⟨26406, by rfl⟩) R52813
theorem R1151765 : Reach 1151765 := rs (se 6 (by rfl) ⟨26994, by rfl⟩) R53989
theorem R70465 : Reach 70465 := rs (se 2 (by rfl) ⟨26424, by rfl⟩) R52849
theorem R70561 : Reach 70561 := rs (se 2 (by rfl) ⟨26460, by rfl⟩) R52921
theorem R103427 : Reach 103427 := rs (se 1 (by rfl) ⟨77570, by rfl⟩) R155141
theorem R267299 : Reach 267299 := rs (se 1 (by rfl) ⟨200474, by rfl⟩) R400949
theorem R332869 : Reach 332869 := rs (se 4 (by rfl) ⟨31206, by rfl⟩) R62413
theorem R169037 : Reach 169037 := rs (se 3 (by rfl) ⟨31694, by rfl⟩) R63389
theorem R70897 : Reach 70897 := rs (se 2 (by rfl) ⟨26586, by rfl⟩) R53173
theorem R136525 : Reach 136525 := rs (se 3 (by rfl) ⟨25598, by rfl⟩) R51197
theorem R234829 : Reach 234829 := rs (se 3 (by rfl) ⟨44030, by rfl⟩) R88061
theorem R136849 : Reach 136849 := rs (se 2 (by rfl) ⟨51318, by rfl⟩) R102637
theorem R366277 : Reach 366277 := rs (se 4 (by rfl) ⟨34338, by rfl⟩) R68677
theorem R71491 : Reach 71491 := rs (se 1 (by rfl) ⟨53618, by rfl⟩) R107237
theorem R268109 : Reach 268109 := rs (se 3 (by rfl) ⟨50270, by rfl⟩) R100541
theorem R104323 : Reach 104323 := rs (se 1 (by rfl) ⟨78242, by rfl⟩) R156485
theorem R300941 : Reach 300941 := rs (se 3 (by rfl) ⟨56426, by rfl⟩) R112853
theorem R137123 : Reach 137123 := rs (se 1 (by rfl) ⟨102842, by rfl⟩) R205685
theorem R104483 : Reach 104483 := rs (se 1 (by rfl) ⟨78362, by rfl⟩) R156725
theorem R137315 : Reach 137315 := rs (se 1 (by rfl) ⟨102986, by rfl⟩) R205973
theorem R399587 : Reach 399587 := rs (se 1 (by rfl) ⟨299690, by rfl⟩) R599381
theorem R203057 : Reach 203057 := rs (se 2 (by rfl) ⟨76146, by rfl⟩) R152293
theorem R104771 : Reach 104771 := rs (se 1 (by rfl) ⟨78578, by rfl⟩) R157157
theorem R170381 : Reach 170381 := rs (se 3 (by rfl) ⟨31946, by rfl⟩) R63893
theorem R137933 : Reach 137933 := rs (se 3 (by rfl) ⟨25862, by rfl⟩) R51725
theorem R170819 : Reach 170819 := rs (se 1 (by rfl) ⟨128114, by rfl⟩) R256229
theorem R138125 : Reach 138125 := rs (se 3 (by rfl) ⟨25898, by rfl⟩) R51797
theorem R236465 : Reach 236465 := rs (se 2 (by rfl) ⟨88674, by rfl⟩) R177349
theorem R138257 : Reach 138257 := rs (se 2 (by rfl) ⟨51846, by rfl⟩) R103693
theorem R138307 : Reach 138307 := rs (se 1 (by rfl) ⟨103730, by rfl⟩) R207461
theorem R138449 : Reach 138449 := rs (se 2 (by rfl) ⟨51918, by rfl⟩) R103837
theorem R73219 : Reach 73219 := rs (se 1 (by rfl) ⟨54914, by rfl⟩) R109829
theorem R204515 : Reach 204515 := rs (se 1 (by rfl) ⟨153386, by rfl⟩) R306773
theorem R139117 : Reach 139117 := rs (se 3 (by rfl) ⟨26084, by rfl⟩) R52169
theorem R1351565 : Reach 1351565 := rs (se 3 (by rfl) ⟨253418, by rfl⟩) R506837
theorem R303173 : Reach 303173 := rs (se 4 (by rfl) ⟨28422, by rfl⟩) R56845
theorem R73891 : Reach 73891 := rs (se 1 (by rfl) ⟨55418, by rfl⟩) R110837
theorem R139441 : Reach 139441 := rs (se 2 (by rfl) ⟨52290, by rfl⟩) R104581
theorem R74081 : Reach 74081 := rs (se 2 (by rfl) ⟨27780, by rfl⟩) R55561
theorem R336433 : Reach 336433 := rs (se 2 (by rfl) ⟨126162, by rfl⟩) R252325
theorem R74353 : Reach 74353 := rs (se 2 (by rfl) ⟨27882, by rfl⟩) R55765
theorem R2007665 : Reach 2007665 := rs (se 2 (by rfl) ⟨752874, by rfl⟩) R1505749
theorem R271025 : Reach 271025 := rs (se 2 (by rfl) ⟨101634, by rfl⟩) R203269
theorem R172739 : Reach 172739 := rs (se 1 (by rfl) ⟨129554, by rfl⟩) R259109
theorem R205517 : Reach 205517 := rs (se 3 (by rfl) ⟨38534, by rfl⟩) R77069
theorem R74449 : Reach 74449 := rs (se 2 (by rfl) ⟨27918, by rfl⟩) R55837
theorem R336611 : Reach 336611 := rs (se 1 (by rfl) ⟨252458, by rfl⟩) R504917
theorem R303857 : Reach 303857 := rs (se 2 (by rfl) ⟨113946, by rfl⟩) R227893
theorem R369521 : Reach 369521 := rs (se 2 (by rfl) ⟨138570, by rfl⟩) R277141
theorem R140237 : Reach 140237 := rs (se 3 (by rfl) ⟨26294, by rfl⟩) R52589
theorem R173069 : Reach 173069 := rs (se 3 (by rfl) ⟨32450, by rfl⟩) R64901
theorem R173123 : Reach 173123 := rs (se 1 (by rfl) ⟨129842, by rfl⟩) R259685
theorem R238691 : Reach 238691 := rs (se 1 (by rfl) ⟨179018, by rfl⟩) R358037
theorem R140401 : Reach 140401 := rs (se 2 (by rfl) ⟨52650, by rfl⟩) R105301
theorem R74945 : Reach 74945 := rs (se 2 (by rfl) ⟨28104, by rfl⟩) R56209
theorem R599237 : Reach 599237 := rs (se 4 (by rfl) ⟨56178, by rfl⟩) R112357
theorem R140561 : Reach 140561 := rs (se 2 (by rfl) ⟨52710, by rfl⟩) R105421
theorem R173393 : Reach 173393 := rs (se 2 (by rfl) ⟨65022, by rfl⟩) R130045
theorem R173645 : Reach 173645 := rs (se 3 (by rfl) ⟨32558, by rfl⟩) R65117
theorem R173933 : Reach 173933 := rs (se 3 (by rfl) ⟨32612, by rfl⟩) R65225
theorem R173987 : Reach 173987 := rs (se 1 (by rfl) ⟨130490, by rfl⟩) R260981
theorem R75811 : Reach 75811 := rs (se 1 (by rfl) ⟨56858, by rfl⟩) R113717
theorem R272483 : Reach 272483 := rs (se 1 (by rfl) ⟨204362, by rfl⟩) R408725
theorem R75907 : Reach 75907 := rs (se 1 (by rfl) ⟨56930, by rfl⟩) R113861
theorem R305315 : Reach 305315 := rs (se 1 (by rfl) ⟨228986, by rfl⟩) R457973
theorem R174257 : Reach 174257 := rs (se 2 (by rfl) ⟨65346, by rfl⟩) R130693
theorem R272645 : Reach 272645 := rs (se 4 (by rfl) ⟨25560, by rfl⟩) R51121
theorem R76403 : Reach 76403 := rs (se 1 (by rfl) ⟨57302, by rfl⟩) R114605
theorem R174797 : Reach 174797 := rs (se 3 (by rfl) ⟨32774, by rfl⟩) R65549
theorem R174851 : Reach 174851 := rs (se 1 (by rfl) ⟨131138, by rfl⟩) R262277
theorem R207629 : Reach 207629 := rs (se 3 (by rfl) ⟨38930, by rfl⟩) R77861
theorem R273293 : Reach 273293 := rs (se 3 (by rfl) ⟨51242, by rfl⟩) R102485
theorem R76691 : Reach 76691 := rs (se 1 (by rfl) ⟨57518, by rfl⟩) R115037
theorem R76721 : Reach 76721 := rs (se 2 (by rfl) ⟨28770, by rfl⟩) R57541
theorem R76739 : Reach 76739 := rs (se 1 (by rfl) ⟨57554, by rfl⟩) R115109
theorem R76769 : Reach 76769 := rs (se 2 (by rfl) ⟨28788, by rfl⟩) R57577
theorem R76787 : Reach 76787 := rs (se 1 (by rfl) ⟨57590, by rfl⟩) R115181
theorem R76817 : Reach 76817 := rs (se 2 (by rfl) ⟨28806, by rfl⟩) R57613
theorem R175121 : Reach 175121 := rs (se 2 (by rfl) ⟨65670, by rfl⟩) R131341
theorem R76835 : Reach 76835 := rs (se 1 (by rfl) ⟨57626, by rfl⟩) R115253
theorem R76865 : Reach 76865 := rs (se 2 (by rfl) ⟨28824, by rfl⟩) R57649
theorem R76883 : Reach 76883 := rs (se 1 (by rfl) ⟨57662, by rfl⟩) R115325
theorem R207971 : Reach 207971 := rs (se 1 (by rfl) ⟨155978, by rfl⟩) R311957
theorem R76913 : Reach 76913 := rs (se 2 (by rfl) ⟨28842, by rfl⟩) R57685
theorem R76931 : Reach 76931 := rs (se 1 (by rfl) ⟨57698, by rfl⟩) R115397
theorem R76961 : Reach 76961 := rs (se 2 (by rfl) ⟨28860, by rfl⟩) R57721
theorem R76979 : Reach 76979 := rs (se 1 (by rfl) ⟨57734, by rfl⟩) R115469
theorem R77009 : Reach 77009 := rs (se 2 (by rfl) ⟨28878, by rfl⟩) R57757
theorem R77027 : Reach 77027 := rs (se 1 (by rfl) ⟨57770, by rfl⟩) R115541
theorem R109795 : Reach 109795 := rs (se 1 (by rfl) ⟨82346, by rfl⟩) R164693
theorem R77041 : Reach 77041 := rs (se 2 (by rfl) ⟨28890, by rfl⟩) R57781
theorem R77057 : Reach 77057 := rs (se 2 (by rfl) ⟨28896, by rfl⟩) R57793
theorem R77075 : Reach 77075 := rs (se 1 (by rfl) ⟨57806, by rfl⟩) R115613
theorem R175405 : Reach 175405 := rs (se 3 (by rfl) ⟨32888, by rfl⟩) R65777
theorem R77105 : Reach 77105 := rs (se 2 (by rfl) ⟨28914, by rfl⟩) R57829
theorem R77123 : Reach 77123 := rs (se 1 (by rfl) ⟨57842, by rfl⟩) R115685
theorem R77153 : Reach 77153 := rs (se 2 (by rfl) ⟨28932, by rfl⟩) R57865
theorem R77171 : Reach 77171 := rs (se 1 (by rfl) ⟨57878, by rfl⟩) R115757
theorem R77201 : Reach 77201 := rs (se 2 (by rfl) ⟨28950, by rfl⟩) R57901
theorem R77219 : Reach 77219 := rs (se 1 (by rfl) ⟨57914, by rfl⟩) R115829
theorem R77249 : Reach 77249 := rs (se 2 (by rfl) ⟨28968, by rfl⟩) R57937
theorem R77267 : Reach 77267 := rs (se 1 (by rfl) ⟨57950, by rfl⟩) R115901
theorem R77297 : Reach 77297 := rs (se 2 (by rfl) ⟨28986, by rfl⟩) R57973
theorem R77315 : Reach 77315 := rs (se 1 (by rfl) ⟨57986, by rfl⟩) R115973
theorem R110083 : Reach 110083 := rs (se 1 (by rfl) ⟨82562, by rfl⟩) R165125
theorem R77345 : Reach 77345 := rs (se 2 (by rfl) ⟨29004, by rfl⟩) R58009
theorem R175661 : Reach 175661 := rs (se 3 (by rfl) ⟨32936, by rfl⟩) R65873
theorem R208433 : Reach 208433 := rs (se 2 (by rfl) ⟨78162, by rfl⟩) R156325
theorem R77363 : Reach 77363 := rs (se 1 (by rfl) ⟨58022, by rfl⟩) R116045
theorem R77377 : Reach 77377 := rs (se 2 (by rfl) ⟨29016, by rfl⟩) R58033
theorem R77393 : Reach 77393 := rs (se 2 (by rfl) ⟨29022, by rfl⟩) R58045
theorem R77411 : Reach 77411 := rs (se 1 (by rfl) ⟨58058, by rfl⟩) R116117
theorem R175715 : Reach 175715 := rs (se 1 (by rfl) ⟨131786, by rfl⟩) R263573
theorem R241265 : Reach 241265 := rs (se 2 (by rfl) ⟨90474, by rfl⟩) R180949
theorem R77441 : Reach 77441 := rs (se 2 (by rfl) ⟨29040, by rfl⟩) R58081
theorem R667277 : Reach 667277 := rs (se 3 (by rfl) ⟨125114, by rfl⟩) R250229
theorem R77459 : Reach 77459 := rs (se 1 (by rfl) ⟨58094, by rfl⟩) R116189
theorem R77489 : Reach 77489 := rs (se 2 (by rfl) ⟨29058, by rfl⟩) R58117
theorem R77507 : Reach 77507 := rs (se 1 (by rfl) ⟨58130, by rfl⟩) R116261
theorem R77537 : Reach 77537 := rs (se 2 (by rfl) ⟨29076, by rfl⟩) R58153
theorem R77555 : Reach 77555 := rs (se 1 (by rfl) ⟨58166, by rfl⟩) R116333
theorem R77585 : Reach 77585 := rs (se 2 (by rfl) ⟨29094, by rfl⟩) R58189
theorem R77603 : Reach 77603 := rs (se 1 (by rfl) ⟨58202, by rfl⟩) R116405
theorem R77633 : Reach 77633 := rs (se 2 (by rfl) ⟨29112, by rfl⟩) R58225
theorem R77651 : Reach 77651 := rs (se 1 (by rfl) ⟨58238, by rfl⟩) R116477
theorem R77681 : Reach 77681 := rs (se 2 (by rfl) ⟨29130, by rfl⟩) R58261
theorem R175985 : Reach 175985 := rs (se 2 (by rfl) ⟨65994, by rfl⟩) R131989
theorem R77699 : Reach 77699 := rs (se 1 (by rfl) ⟨58274, by rfl⟩) R116549
theorem R77729 : Reach 77729 := rs (se 2 (by rfl) ⟨29148, by rfl⟩) R58297
theorem R77747 : Reach 77747 := rs (se 1 (by rfl) ⟨58310, by rfl⟩) R116621
theorem R77777 : Reach 77777 := rs (se 2 (by rfl) ⟨29166, by rfl⟩) R58333
theorem R77795 : Reach 77795 := rs (se 1 (by rfl) ⟨58346, by rfl⟩) R116693
theorem R241649 : Reach 241649 := rs (se 2 (by rfl) ⟨90618, by rfl⟩) R181237
theorem R77825 : Reach 77825 := rs (se 2 (by rfl) ⟨29184, by rfl⟩) R58369
theorem R77843 : Reach 77843 := rs (se 1 (by rfl) ⟨58382, by rfl⟩) R116765
theorem R110641 : Reach 110641 := rs (se 2 (by rfl) ⟨41490, by rfl⟩) R82981
theorem R77873 : Reach 77873 := rs (se 2 (by rfl) ⟨29202, by rfl⟩) R58405
theorem R274481 : Reach 274481 := rs (se 2 (by rfl) ⟨102930, by rfl⟩) R205861
theorem R77891 : Reach 77891 := rs (se 1 (by rfl) ⟨58418, by rfl⟩) R116837
theorem R77921 : Reach 77921 := rs (se 2 (by rfl) ⟨29220, by rfl⟩) R58441
theorem R77939 : Reach 77939 := rs (se 1 (by rfl) ⟨58454, by rfl⟩) R116909
theorem R77969 : Reach 77969 := rs (se 2 (by rfl) ⟨29238, by rfl⟩) R58477
theorem R77987 : Reach 77987 := rs (se 1 (by rfl) ⟨58490, by rfl⟩) R116981
theorem R78017 : Reach 78017 := rs (se 2 (by rfl) ⟨29256, by rfl⟩) R58513
theorem R209101 : Reach 209101 := rs (se 3 (by rfl) ⟨39206, by rfl⟩) R78413
theorem R78035 : Reach 78035 := rs (se 1 (by rfl) ⟨58526, by rfl⟩) R117053
theorem R78065 : Reach 78065 := rs (se 2 (by rfl) ⟨29274, by rfl⟩) R58549
theorem R78083 : Reach 78083 := rs (se 1 (by rfl) ⟨58562, by rfl⟩) R117125
theorem R78113 : Reach 78113 := rs (se 2 (by rfl) ⟨29292, by rfl⟩) R58585
theorem R78131 : Reach 78131 := rs (se 1 (by rfl) ⟨58598, by rfl⟩) R117197
theorem R78161 : Reach 78161 := rs (se 2 (by rfl) ⟨29310, by rfl⟩) R58621
theorem R78179 : Reach 78179 := rs (se 1 (by rfl) ⟨58634, by rfl⟩) R117269
theorem R78209 : Reach 78209 := rs (se 2 (by rfl) ⟨29328, by rfl⟩) R58657
theorem R176525 : Reach 176525 := rs (se 3 (by rfl) ⟨33098, by rfl⟩) R66197
theorem R78227 : Reach 78227 := rs (se 1 (by rfl) ⟨58670, by rfl⟩) R117341
theorem R78257 : Reach 78257 := rs (se 2 (by rfl) ⟨29346, by rfl⟩) R58693
theorem R78275 : Reach 78275 := rs (se 1 (by rfl) ⟨58706, by rfl⟩) R117413
theorem R176579 : Reach 176579 := rs (se 1 (by rfl) ⟨132434, by rfl⟩) R264869
theorem R78305 : Reach 78305 := rs (se 2 (by rfl) ⟨29364, by rfl⟩) R58729
theorem R78323 : Reach 78323 := rs (se 1 (by rfl) ⟨58742, by rfl⟩) R117485
theorem R78353 : Reach 78353 := rs (se 2 (by rfl) ⟨29382, by rfl⟩) R58765
theorem R78371 : Reach 78371 := rs (se 1 (by rfl) ⟨58778, by rfl⟩) R117557
theorem R78401 : Reach 78401 := rs (se 2 (by rfl) ⟨29400, by rfl⟩) R58801
theorem R78419 : Reach 78419 := rs (se 1 (by rfl) ⟨58814, by rfl⟩) R117629
theorem R78449 : Reach 78449 := rs (se 2 (by rfl) ⟨29418, by rfl⟩) R58837
theorem R78467 : Reach 78467 := rs (se 1 (by rfl) ⟨58850, by rfl⟩) R117701
theorem R78497 : Reach 78497 := rs (se 2 (by rfl) ⟨29436, by rfl⟩) R58873
theorem R78515 : Reach 78515 := rs (se 1 (by rfl) ⟨58886, by rfl⟩) R117773
theorem R78545 : Reach 78545 := rs (se 2 (by rfl) ⟨29454, by rfl⟩) R58909
theorem R176849 : Reach 176849 := rs (se 2 (by rfl) ⟨66318, by rfl⟩) R132637
theorem R78563 : Reach 78563 := rs (se 1 (by rfl) ⟨58922, by rfl⟩) R117845
theorem R635633 : Reach 635633 := rs (se 2 (by rfl) ⟨238362, by rfl⟩) R476725
theorem R78593 : Reach 78593 := rs (se 2 (by rfl) ⟨29472, by rfl⟩) R58945
theorem R78611 : Reach 78611 := rs (se 1 (by rfl) ⟨58958, by rfl⟩) R117917
theorem R78641 : Reach 78641 := rs (se 2 (by rfl) ⟨29490, by rfl⟩) R58981
theorem R78659 : Reach 78659 := rs (se 1 (by rfl) ⟨58994, by rfl⟩) R117989
theorem R78689 : Reach 78689 := rs (se 2 (by rfl) ⟨29508, by rfl⟩) R59017
theorem R78707 : Reach 78707 := rs (se 1 (by rfl) ⟨59030, by rfl⟩) R118061
theorem R78737 : Reach 78737 := rs (se 2 (by rfl) ⟨29526, by rfl⟩) R59053
theorem R78755 : Reach 78755 := rs (se 1 (by rfl) ⟨59066, by rfl⟩) R118133
theorem R78785 : Reach 78785 := rs (se 2 (by rfl) ⟨29544, by rfl⟩) R59089
theorem R78803 : Reach 78803 := rs (se 1 (by rfl) ⟨59102, by rfl⟩) R118205
theorem R78833 : Reach 78833 := rs (se 2 (by rfl) ⟨29562, by rfl⟩) R59125
theorem R78851 : Reach 78851 := rs (se 1 (by rfl) ⟨59138, by rfl⟩) R118277
theorem R78881 : Reach 78881 := rs (se 2 (by rfl) ⟨29580, by rfl⟩) R59161
theorem R78899 : Reach 78899 := rs (se 1 (by rfl) ⟨59174, by rfl⟩) R118349
theorem R144451 : Reach 144451 := rs (se 1 (by rfl) ⟨108338, by rfl⟩) R216677
theorem R78929 : Reach 78929 := rs (se 2 (by rfl) ⟨29598, by rfl⟩) R59197
theorem R78947 : Reach 78947 := rs (se 1 (by rfl) ⟨59210, by rfl⟩) R118421
theorem R144497 : Reach 144497 := rs (se 2 (by rfl) ⟨54186, by rfl⟩) R108373
theorem R177265 : Reach 177265 := rs (se 2 (by rfl) ⟨66474, by rfl⟩) R132949
theorem R78977 : Reach 78977 := rs (se 2 (by rfl) ⟨29616, by rfl⟩) R59233
theorem R78995 : Reach 78995 := rs (se 1 (by rfl) ⟨59246, by rfl⟩) R118493
theorem R79025 : Reach 79025 := rs (se 2 (by rfl) ⟨29634, by rfl⟩) R59269
theorem R79043 : Reach 79043 := rs (se 1 (by rfl) ⟨59282, by rfl⟩) R118565
theorem R144593 : Reach 144593 := rs (se 2 (by rfl) ⟨54222, by rfl⟩) R108445
theorem R79073 : Reach 79073 := rs (se 2 (by rfl) ⟨29652, by rfl⟩) R59305
theorem R3880163 : Reach 3880163 := rs (se 1 (by rfl) ⟨2910122, by rfl⟩) R5820245
theorem R177389 : Reach 177389 := rs (se 3 (by rfl) ⟨33260, by rfl⟩) R66521
theorem R144625 : Reach 144625 := rs (se 2 (by rfl) ⟨54234, by rfl⟩) R108469
theorem R79091 : Reach 79091 := rs (se 1 (by rfl) ⟨59318, by rfl⟩) R118637
theorem R79121 : Reach 79121 := rs (se 2 (by rfl) ⟨29670, by rfl⟩) R59341
theorem R177443 : Reach 177443 := rs (se 1 (by rfl) ⟨133082, by rfl⟩) R266165
theorem R79139 : Reach 79139 := rs (se 1 (by rfl) ⟨59354, by rfl⟩) R118709
theorem R79169 : Reach 79169 := rs (se 2 (by rfl) ⟨29688, by rfl⟩) R59377
theorem R308549 : Reach 308549 := rs (se 4 (by rfl) ⟨28926, by rfl⟩) R57853
theorem R79187 : Reach 79187 := rs (se 1 (by rfl) ⟨59390, by rfl⟩) R118781
theorem R79217 : Reach 79217 := rs (se 2 (by rfl) ⟨29706, by rfl⟩) R59413
theorem R79235 : Reach 79235 := rs (se 1 (by rfl) ⟨59426, by rfl⟩) R118853
theorem R79265 : Reach 79265 := rs (se 2 (by rfl) ⟨29724, by rfl⟩) R59449
theorem R79283 : Reach 79283 := rs (se 1 (by rfl) ⟨59462, by rfl⟩) R118925
theorem R79313 : Reach 79313 := rs (se 2 (by rfl) ⟨29742, by rfl⟩) R59485
theorem R79331 : Reach 79331 := rs (se 1 (by rfl) ⟨59498, by rfl⟩) R118997
theorem R79361 : Reach 79361 := rs (se 2 (by rfl) ⟨29760, by rfl⟩) R59521
theorem R79379 : Reach 79379 := rs (se 1 (by rfl) ⟨59534, by rfl⟩) R119069
theorem R177713 : Reach 177713 := rs (se 2 (by rfl) ⟨66642, by rfl⟩) R133285
theorem R79409 : Reach 79409 := rs (se 2 (by rfl) ⟨29778, by rfl⟩) R59557
theorem R112195 : Reach 112195 := rs (se 1 (by rfl) ⟨84146, by rfl⟩) R168293
theorem R79427 : Reach 79427 := rs (se 1 (by rfl) ⟨59570, by rfl⟩) R119141
theorem R374341 : Reach 374341 := rs (se 4 (by rfl) ⟨35094, by rfl⟩) R70189
theorem R79457 : Reach 79457 := rs (se 2 (by rfl) ⟨29796, by rfl⟩) R59593
theorem R79475 : Reach 79475 := rs (se 1 (by rfl) ⟨59606, by rfl⟩) R119213
theorem R669325 : Reach 669325 := rs (se 3 (by rfl) ⟨125498, by rfl⟩) R250997
theorem R79505 : Reach 79505 := rs (se 2 (by rfl) ⟨29814, by rfl⟩) R59629
theorem R79523 : Reach 79523 := rs (se 1 (by rfl) ⟨59642, by rfl⟩) R119285
theorem R79553 : Reach 79553 := rs (se 2 (by rfl) ⟨29832, by rfl⟩) R59665
theorem R79571 : Reach 79571 := rs (se 1 (by rfl) ⟨59678, by rfl⟩) R119357
theorem R112355 : Reach 112355 := rs (se 1 (by rfl) ⟨84266, by rfl⟩) R168533
theorem R407267 : Reach 407267 := rs (se 1 (by rfl) ⟨305450, by rfl⟩) R610901
theorem R79601 : Reach 79601 := rs (se 2 (by rfl) ⟨29850, by rfl⟩) R59701
theorem R276209 : Reach 276209 := rs (se 2 (by rfl) ⟨103578, by rfl⟩) R207157
theorem R79619 : Reach 79619 := rs (se 1 (by rfl) ⟨59714, by rfl⟩) R119429
theorem R341765 : Reach 341765 := rs (se 4 (by rfl) ⟨32040, by rfl⟩) R64081
theorem R309005 : Reach 309005 := rs (se 3 (by rfl) ⟨57938, by rfl⟩) R115877
theorem R79649 : Reach 79649 := rs (se 2 (by rfl) ⟨29868, by rfl⟩) R59737
theorem R79667 : Reach 79667 := rs (se 1 (by rfl) ⟨59750, by rfl⟩) R119501
theorem R79697 : Reach 79697 := rs (se 2 (by rfl) ⟨29886, by rfl⟩) R59773
theorem R79715 : Reach 79715 := rs (se 1 (by rfl) ⟨59786, by rfl⟩) R119573
theorem R79745 : Reach 79745 := rs (se 2 (by rfl) ⟨29904, by rfl⟩) R59809
theorem R866189 : Reach 866189 := rs (se 3 (by rfl) ⟨162410, by rfl⟩) R324821
theorem R112529 : Reach 112529 := rs (se 2 (by rfl) ⟨42198, by rfl⟩) R84397
theorem R79763 : Reach 79763 := rs (se 1 (by rfl) ⟨59822, by rfl⟩) R119645
theorem R79793 : Reach 79793 := rs (se 2 (by rfl) ⟨29922, by rfl⟩) R59845
theorem R79811 : Reach 79811 := rs (se 1 (by rfl) ⟨59858, by rfl⟩) R119717
theorem R79841 : Reach 79841 := rs (se 2 (by rfl) ⟨29940, by rfl⟩) R59881
theorem R79859 : Reach 79859 := rs (se 1 (by rfl) ⟨59894, by rfl⟩) R119789
theorem R374797 : Reach 374797 := rs (se 3 (by rfl) ⟨70274, by rfl⟩) R140549
theorem R79889 : Reach 79889 := rs (se 2 (by rfl) ⟨29958, by rfl⟩) R59917
theorem R79907 : Reach 79907 := rs (se 1 (by rfl) ⟨59930, by rfl⟩) R119861
theorem R79937 : Reach 79937 := rs (se 2 (by rfl) ⟨29976, by rfl⟩) R59953
theorem R178253 : Reach 178253 := rs (se 3 (by rfl) ⟨33422, by rfl⟩) R66845
theorem R79955 : Reach 79955 := rs (se 1 (by rfl) ⟨59966, by rfl⟩) R119933
theorem R79985 : Reach 79985 := rs (se 2 (by rfl) ⟨29994, by rfl⟩) R59989
theorem R178307 : Reach 178307 := rs (se 1 (by rfl) ⟨133730, by rfl⟩) R267461
theorem R80003 : Reach 80003 := rs (se 1 (by rfl) ⟨60002, by rfl⟩) R120005
theorem R178321 : Reach 178321 := rs (se 2 (by rfl) ⟨66870, by rfl⟩) R133741
theorem R80033 : Reach 80033 := rs (se 2 (by rfl) ⟨30012, by rfl⟩) R60025
theorem R80051 : Reach 80051 := rs (se 1 (by rfl) ⟨60038, by rfl⟩) R120077
theorem R80081 : Reach 80081 := rs (se 2 (by rfl) ⟨30030, by rfl⟩) R60061
theorem R80099 : Reach 80099 := rs (se 1 (by rfl) ⟨60074, by rfl⟩) R120149
theorem R80129 : Reach 80129 := rs (se 2 (by rfl) ⟨30048, by rfl⟩) R60097
theorem R80147 : Reach 80147 := rs (se 1 (by rfl) ⟨60110, by rfl⟩) R120221
theorem R145709 : Reach 145709 := rs (se 3 (by rfl) ⟨27320, by rfl⟩) R54641
theorem R80177 : Reach 80177 := rs (se 2 (by rfl) ⟨30066, by rfl⟩) R60133
theorem R80195 : Reach 80195 := rs (se 1 (by rfl) ⟨60146, by rfl⟩) R120293
theorem R80225 : Reach 80225 := rs (se 2 (by rfl) ⟨30084, by rfl⟩) R60169
theorem R80243 : Reach 80243 := rs (se 1 (by rfl) ⟨60182, by rfl⟩) R120365
theorem R178577 : Reach 178577 := rs (se 2 (by rfl) ⟨66966, by rfl⟩) R133933
theorem R80273 : Reach 80273 := rs (se 2 (by rfl) ⟨30102, by rfl⟩) R60205
theorem R80291 : Reach 80291 := rs (se 1 (by rfl) ⟨60218, by rfl⟩) R120437
theorem R80321 : Reach 80321 := rs (se 2 (by rfl) ⟨30120, by rfl⟩) R60241
theorem R113105 : Reach 113105 := rs (se 2 (by rfl) ⟨42414, by rfl⟩) R84829
theorem R80339 : Reach 80339 := rs (se 1 (by rfl) ⟨60254, by rfl⟩) R120509
theorem R145891 : Reach 145891 := rs (se 1 (by rfl) ⟨109418, by rfl⟩) R218837
theorem R80369 : Reach 80369 := rs (se 2 (by rfl) ⟨30138, by rfl⟩) R60277
theorem R80387 : Reach 80387 := rs (se 1 (by rfl) ⟨60290, by rfl⟩) R120581
theorem R145937 : Reach 145937 := rs (se 2 (by rfl) ⟨54726, by rfl⟩) R109453
theorem R80417 : Reach 80417 := rs (se 2 (by rfl) ⟨30156, by rfl⟩) R60313
theorem R80435 : Reach 80435 := rs (se 1 (by rfl) ⟨60326, by rfl⟩) R120653
theorem R80465 : Reach 80465 := rs (se 2 (by rfl) ⟨30174, by rfl⟩) R60349
theorem R80483 : Reach 80483 := rs (se 1 (by rfl) ⟨60362, by rfl⟩) R120725
theorem R80513 : Reach 80513 := rs (se 2 (by rfl) ⟨30192, by rfl⟩) R60385
theorem R80531 : Reach 80531 := rs (se 1 (by rfl) ⟨60398, by rfl⟩) R120797
theorem R80561 : Reach 80561 := rs (se 2 (by rfl) ⟨30210, by rfl⟩) R60421
theorem R80579 : Reach 80579 := rs (se 1 (by rfl) ⟨60434, by rfl⟩) R120869
theorem R80609 : Reach 80609 := rs (se 2 (by rfl) ⟨30228, by rfl⟩) R60457
theorem R80627 : Reach 80627 := rs (se 1 (by rfl) ⟨60470, by rfl⟩) R120941
theorem R80657 : Reach 80657 := rs (se 2 (by rfl) ⟨30246, by rfl⟩) R60493
theorem R80675 : Reach 80675 := rs (se 1 (by rfl) ⟨60506, by rfl⟩) R121013
theorem R80705 : Reach 80705 := rs (se 2 (by rfl) ⟨30264, by rfl⟩) R60529
theorem R80723 : Reach 80723 := rs (se 1 (by rfl) ⟨60542, by rfl⟩) R121085
theorem R80753 : Reach 80753 := rs (se 2 (by rfl) ⟨30282, by rfl⟩) R60565
theorem R80771 : Reach 80771 := rs (se 1 (by rfl) ⟨60578, by rfl⟩) R121157
theorem R605069 : Reach 605069 := rs (se 3 (by rfl) ⟨113450, by rfl⟩) R226901
theorem R80801 : Reach 80801 := rs (se 2 (by rfl) ⟨30300, by rfl⟩) R60601
theorem R179117 : Reach 179117 := rs (se 3 (by rfl) ⟨33584, by rfl⟩) R67169
theorem R80819 : Reach 80819 := rs (se 1 (by rfl) ⟨60614, by rfl⟩) R121229
theorem R80849 : Reach 80849 := rs (se 2 (by rfl) ⟨30318, by rfl⟩) R60637
theorem R179171 : Reach 179171 := rs (se 1 (by rfl) ⟨134378, by rfl⟩) R268757
theorem R80867 : Reach 80867 := rs (se 1 (by rfl) ⟨60650, by rfl⟩) R121301
theorem R80897 : Reach 80897 := rs (se 2 (by rfl) ⟨30336, by rfl⟩) R60673
theorem R80915 : Reach 80915 := rs (se 1 (by rfl) ⟨60686, by rfl⟩) R121373
theorem R80945 : Reach 80945 := rs (se 2 (by rfl) ⟨30354, by rfl⟩) R60709
theorem R80963 : Reach 80963 := rs (se 1 (by rfl) ⟨60722, by rfl⟩) R121445
theorem R80993 : Reach 80993 := rs (se 2 (by rfl) ⟨30372, by rfl⟩) R60745
theorem R81011 : Reach 81011 := rs (se 1 (by rfl) ⟨60758, by rfl⟩) R121517
theorem R965773 : Reach 965773 := rs (se 3 (by rfl) ⟨181082, by rfl⟩) R362165
theorem R81041 : Reach 81041 := rs (se 2 (by rfl) ⟨30390, by rfl⟩) R60781
theorem R113827 : Reach 113827 := rs (se 1 (by rfl) ⟨85370, by rfl⟩) R170741
theorem R81059 : Reach 81059 := rs (se 1 (by rfl) ⟨60794, by rfl⟩) R121589
theorem R277667 : Reach 277667 := rs (se 1 (by rfl) ⟨208250, by rfl⟩) R416501
theorem R81089 : Reach 81089 := rs (se 2 (by rfl) ⟨30408, by rfl⟩) R60817
theorem R81107 : Reach 81107 := rs (se 1 (by rfl) ⟨60830, by rfl⟩) R121661
theorem R179441 : Reach 179441 := rs (se 2 (by rfl) ⟨67290, by rfl⟩) R134581
theorem R81137 : Reach 81137 := rs (se 2 (by rfl) ⟨30426, by rfl⟩) R60853
theorem R81155 : Reach 81155 := rs (se 1 (by rfl) ⟨60866, by rfl⟩) R121733
theorem R81185 : Reach 81185 := rs (se 2 (by rfl) ⟨30444, by rfl⟩) R60889
theorem R81203 : Reach 81203 := rs (se 1 (by rfl) ⟨60902, by rfl⟩) R121805
theorem R277829 : Reach 277829 := rs (se 4 (by rfl) ⟨26046, by rfl⟩) R52093
theorem R81233 : Reach 81233 := rs (se 2 (by rfl) ⟨30462, by rfl⟩) R60925
theorem R81251 : Reach 81251 := rs (se 1 (by rfl) ⟨60938, by rfl⟩) R121877
theorem R81281 : Reach 81281 := rs (se 2 (by rfl) ⟨30480, by rfl⟩) R60961
theorem R81299 : Reach 81299 := rs (se 1 (by rfl) ⟨60974, by rfl⟩) R121949
theorem R81329 : Reach 81329 := rs (se 2 (by rfl) ⟨30498, by rfl⟩) R60997
theorem R81347 : Reach 81347 := rs (se 1 (by rfl) ⟨61010, by rfl⟩) R122021
theorem R81377 : Reach 81377 := rs (se 2 (by rfl) ⟨30516, by rfl⟩) R61033
theorem R507377 : Reach 507377 := rs (se 2 (by rfl) ⟨190266, by rfl⟩) R380533
theorem R81395 : Reach 81395 := rs (se 1 (by rfl) ⟨61046, by rfl⟩) R122093
theorem R81425 : Reach 81425 := rs (se 2 (by rfl) ⟨30534, by rfl⟩) R61069
theorem R81443 : Reach 81443 := rs (se 1 (by rfl) ⟨61082, by rfl⟩) R122165
theorem R81473 : Reach 81473 := rs (se 2 (by rfl) ⟨30552, by rfl⟩) R61105
theorem R81491 : Reach 81491 := rs (se 1 (by rfl) ⟨61118, by rfl⟩) R122237
theorem R81521 : Reach 81521 := rs (se 2 (by rfl) ⟨30570, by rfl⟩) R61141
theorem R81539 : Reach 81539 := rs (se 1 (by rfl) ⟨61154, by rfl⟩) R122309
theorem R81569 : Reach 81569 := rs (se 2 (by rfl) ⟨30588, by rfl⟩) R61177
theorem R81587 : Reach 81587 := rs (se 1 (by rfl) ⟨61190, by rfl⟩) R122381
theorem R81617 : Reach 81617 := rs (se 2 (by rfl) ⟨30606, by rfl⟩) R61213
theorem R81635 : Reach 81635 := rs (se 1 (by rfl) ⟨61226, by rfl⟩) R122453
theorem R81665 : Reach 81665 := rs (se 2 (by rfl) ⟨30624, by rfl⟩) R61249
theorem R179981 : Reach 179981 := rs (se 3 (by rfl) ⟨33746, by rfl⟩) R67493
theorem R147217 : Reach 147217 := rs (se 2 (by rfl) ⟨55206, by rfl⟩) R110413
theorem R81683 : Reach 81683 := rs (se 1 (by rfl) ⟨61262, by rfl⟩) R122525
theorem R81713 : Reach 81713 := rs (se 2 (by rfl) ⟨30642, by rfl⟩) R61285
theorem R180035 : Reach 180035 := rs (se 1 (by rfl) ⟨135026, by rfl⟩) R270053
theorem R81731 : Reach 81731 := rs (se 1 (by rfl) ⟨61298, by rfl⟩) R122597
theorem R81761 : Reach 81761 := rs (se 2 (by rfl) ⟨30660, by rfl⟩) R61321
theorem R81779 : Reach 81779 := rs (se 1 (by rfl) ⟨61334, by rfl⟩) R122669
theorem R2015117 : Reach 2015117 := rs (se 3 (by rfl) ⟨377834, by rfl⟩) R755669
theorem R81809 : Reach 81809 := rs (se 2 (by rfl) ⟨30678, by rfl⟩) R61357
theorem R81827 : Reach 81827 := rs (se 1 (by rfl) ⟨61370, by rfl⟩) R122741
theorem R81857 : Reach 81857 := rs (se 2 (by rfl) ⟨30696, by rfl⟩) R61393
theorem R147395 : Reach 147395 := rs (se 1 (by rfl) ⟨110546, by rfl⟩) R221093
theorem R278477 : Reach 278477 := rs (se 3 (by rfl) ⟨52214, by rfl⟩) R104429
theorem R81875 : Reach 81875 := rs (se 1 (by rfl) ⟨61406, by rfl⟩) R122813
theorem R81905 : Reach 81905 := rs (se 2 (by rfl) ⟨30714, by rfl⟩) R61429
theorem R81923 : Reach 81923 := rs (se 1 (by rfl) ⟨61442, by rfl⟩) R122885
theorem R147469 : Reach 147469 := rs (se 3 (by rfl) ⟨27650, by rfl⟩) R55301
theorem R81953 : Reach 81953 := rs (se 2 (by rfl) ⟨30732, by rfl⟩) R61465
theorem R81971 : Reach 81971 := rs (se 1 (by rfl) ⟨61478, by rfl⟩) R122957
theorem R180305 : Reach 180305 := rs (se 2 (by rfl) ⟨67614, by rfl⟩) R135229
theorem R82001 : Reach 82001 := rs (se 2 (by rfl) ⟨30750, by rfl⟩) R61501
theorem R82019 : Reach 82019 := rs (se 1 (by rfl) ⟨61514, by rfl⟩) R123029
theorem R82049 : Reach 82049 := rs (se 2 (by rfl) ⟨30768, by rfl⟩) R61537
theorem R82067 : Reach 82067 := rs (se 1 (by rfl) ⟨61550, by rfl⟩) R123101
theorem R82097 : Reach 82097 := rs (se 2 (by rfl) ⟨30786, by rfl⟩) R61573
theorem R82115 : Reach 82115 := rs (se 1 (by rfl) ⟨61586, by rfl⟩) R123173
theorem R82129 : Reach 82129 := rs (se 2 (by rfl) ⟨30798, by rfl⟩) R61597
theorem R82145 : Reach 82145 := rs (se 2 (by rfl) ⟨30804, by rfl⟩) R61609
theorem R82163 : Reach 82163 := rs (se 1 (by rfl) ⟨61622, by rfl⟩) R123245
theorem R82193 : Reach 82193 := rs (se 2 (by rfl) ⟨30822, by rfl⟩) R61645
theorem R82211 : Reach 82211 := rs (se 1 (by rfl) ⟨61658, by rfl⟩) R123317
theorem R82241 : Reach 82241 := rs (se 2 (by rfl) ⟨30840, by rfl⟩) R61681
theorem R82259 : Reach 82259 := rs (se 1 (by rfl) ⟨61694, by rfl⟩) R123389
theorem R115057 : Reach 115057 := rs (se 2 (by rfl) ⟨43146, by rfl⟩) R86293
theorem R82289 : Reach 82289 := rs (se 2 (by rfl) ⟨30858, by rfl⟩) R61717
theorem R82307 : Reach 82307 := rs (se 1 (by rfl) ⟨61730, by rfl⟩) R123461
theorem R82337 : Reach 82337 := rs (se 2 (by rfl) ⟨30876, by rfl⟩) R61753
theorem R82355 : Reach 82355 := rs (se 1 (by rfl) ⟨61766, by rfl⟩) R123533
theorem R82385 : Reach 82385 := rs (se 2 (by rfl) ⟨30894, by rfl⟩) R61789
theorem R82403 : Reach 82403 := rs (se 1 (by rfl) ⟨61802, by rfl⟩) R123605
theorem R82433 : Reach 82433 := rs (se 2 (by rfl) ⟨30912, by rfl⟩) R61825
theorem R573965 : Reach 573965 := rs (se 3 (by rfl) ⟨107618, by rfl⟩) R215237
theorem R115217 : Reach 115217 := rs (se 2 (by rfl) ⟨43206, by rfl⟩) R86413
theorem R82451 : Reach 82451 := rs (se 1 (by rfl) ⟨61838, by rfl⟩) R123677
theorem R115235 : Reach 115235 := rs (se 1 (by rfl) ⟨86426, by rfl⟩) R172853
theorem R82481 : Reach 82481 := rs (se 2 (by rfl) ⟨30930, by rfl⟩) R61861
theorem R82499 : Reach 82499 := rs (se 1 (by rfl) ⟨61874, by rfl⟩) R123749
theorem R82529 : Reach 82529 := rs (se 2 (by rfl) ⟨30948, by rfl⟩) R61897
theorem R180845 : Reach 180845 := rs (se 3 (by rfl) ⟨33908, by rfl⟩) R67817
theorem R311921 : Reach 311921 := rs (se 2 (by rfl) ⟨116970, by rfl⟩) R233941
theorem R82547 : Reach 82547 := rs (se 1 (by rfl) ⟨61910, by rfl⟩) R123821
theorem R82577 : Reach 82577 := rs (se 2 (by rfl) ⟨30966, by rfl⟩) R61933
theorem R180899 : Reach 180899 := rs (se 1 (by rfl) ⟨135674, by rfl⟩) R271349
theorem R82595 : Reach 82595 := rs (se 1 (by rfl) ⟨61946, by rfl⟩) R123893
theorem R82625 : Reach 82625 := rs (se 2 (by rfl) ⟨30984, by rfl⟩) R61969
theorem R82643 : Reach 82643 := rs (se 1 (by rfl) ⟨61982, by rfl⟩) R123965
theorem R82673 : Reach 82673 := rs (se 2 (by rfl) ⟨31002, by rfl⟩) R62005
theorem R82691 : Reach 82691 := rs (se 1 (by rfl) ⟨62018, by rfl⟩) R124037
theorem R246577 : Reach 246577 := rs (se 2 (by rfl) ⟨92466, by rfl⟩) R184933
theorem R115505 : Reach 115505 := rs (se 2 (by rfl) ⟨43314, by rfl⟩) R86629
theorem R115523 : Reach 115523 := rs (se 1 (by rfl) ⟨86642, by rfl⟩) R173285
theorem R181169 : Reach 181169 := rs (se 2 (by rfl) ⟨67938, by rfl⟩) R135877
theorem R1360867 : Reach 1360867 := rs (se 1 (by rfl) ⟨1020650, by rfl⟩) R2041301
theorem R148483 : Reach 148483 := rs (se 1 (by rfl) ⟨111362, by rfl⟩) R222725
theorem R148529 : Reach 148529 := rs (se 2 (by rfl) ⟨55698, by rfl⟩) R111397
theorem R115793 : Reach 115793 := rs (se 2 (by rfl) ⟨43422, by rfl⟩) R86845
theorem R115811 : Reach 115811 := rs (se 1 (by rfl) ⟨86858, by rfl⟩) R173717
theorem R115843 : Reach 115843 := rs (se 1 (by rfl) ⟨86882, by rfl⟩) R173765
theorem R1033357 : Reach 1033357 := rs (se 3 (by rfl) ⟨193754, by rfl⟩) R387509
theorem R83089 : Reach 83089 := rs (se 2 (by rfl) ⟨31158, by rfl⟩) R62317
theorem R148625 : Reach 148625 := rs (se 2 (by rfl) ⟨55734, by rfl⟩) R111469
theorem R116081 : Reach 116081 := rs (se 2 (by rfl) ⟨43530, by rfl⟩) R87061
theorem R116099 : Reach 116099 := rs (se 1 (by rfl) ⟨87074, by rfl⟩) R174149
theorem R181645 : Reach 181645 := rs (se 3 (by rfl) ⟨34058, by rfl⟩) R68117
theorem R181709 : Reach 181709 := rs (se 3 (by rfl) ⟨34070, by rfl⟩) R68141
theorem R116369 : Reach 116369 := rs (se 2 (by rfl) ⟨43638, by rfl⟩) R87277
theorem R116387 : Reach 116387 := rs (se 1 (by rfl) ⟨87290, by rfl⟩) R174581
theorem R83651 : Reach 83651 := rs (se 1 (by rfl) ⟨62738, by rfl⟩) R125477
theorem R476869 : Reach 476869 := rs (se 4 (by rfl) ⟨44706, by rfl⟩) R89413
theorem R607985 : Reach 607985 := rs (se 2 (by rfl) ⟨227994, by rfl⟩) R455989
theorem R116561 : Reach 116561 := rs (se 2 (by rfl) ⟨43710, by rfl⟩) R87421
theorem R116657 : Reach 116657 := rs (se 2 (by rfl) ⟨43746, by rfl⟩) R87493
theorem R51123 : Reach 51123 := rs (se 1 (by rfl) ⟨38342, by rfl⟩) R76685
theorem R51139 : Reach 51139 := rs (se 1 (by rfl) ⟨38354, by rfl⟩) R76709
theorem R116675 : Reach 116675 := rs (se 1 (by rfl) ⟨87506, by rfl⟩) R175013
theorem R51155 : Reach 51155 := rs (se 1 (by rfl) ⟨38366, by rfl⟩) R76733
theorem R51171 : Reach 51171 := rs (se 1 (by rfl) ⟨38378, by rfl⟩) R76757
theorem R51187 : Reach 51187 := rs (se 1 (by rfl) ⟨38390, by rfl⟩) R76781
theorem R51203 : Reach 51203 := rs (se 1 (by rfl) ⟨38402, by rfl⟩) R76805
theorem R51219 : Reach 51219 := rs (se 1 (by rfl) ⟨38414, by rfl⟩) R76829
theorem R83987 : Reach 83987 := rs (se 1 (by rfl) ⟨62990, by rfl⟩) R125981
theorem R51235 : Reach 51235 := rs (se 1 (by rfl) ⟨38426, by rfl⟩) R76853
theorem R313379 : Reach 313379 := rs (se 1 (by rfl) ⟨235034, by rfl⟩) R470069
theorem R51251 : Reach 51251 := rs (se 1 (by rfl) ⟨38438, by rfl⟩) R76877
theorem R51267 : Reach 51267 := rs (se 1 (by rfl) ⟨38450, by rfl⟩) R76901
theorem R51283 : Reach 51283 := rs (se 1 (by rfl) ⟨38462, by rfl⟩) R76925
theorem R51299 : Reach 51299 := rs (se 1 (by rfl) ⟨38474, by rfl⟩) R76949
theorem R51315 : Reach 51315 := rs (se 1 (by rfl) ⟨38486, by rfl⟩) R76973
theorem R51331 : Reach 51331 := rs (se 1 (by rfl) ⟨38498, by rfl⟩) R76997
theorem R51347 : Reach 51347 := rs (se 1 (by rfl) ⟨38510, by rfl⟩) R77021
theorem R51363 : Reach 51363 := rs (se 1 (by rfl) ⟨38522, by rfl⟩) R77045
theorem R51379 : Reach 51379 := rs (se 1 (by rfl) ⟨38534, by rfl⟩) R77069
theorem R51395 : Reach 51395 := rs (se 1 (by rfl) ⟨38546, by rfl⟩) R77093
theorem R116945 : Reach 116945 := rs (se 2 (by rfl) ⟨43854, by rfl⟩) R87709
theorem R51411 : Reach 51411 := rs (se 1 (by rfl) ⟨38558, by rfl⟩) R77117
theorem R84179 : Reach 84179 := rs (se 1 (by rfl) ⟨63134, by rfl⟩) R126269
theorem R51427 : Reach 51427 := rs (se 1 (by rfl) ⟨38570, by rfl⟩) R77141
theorem R116963 : Reach 116963 := rs (se 1 (by rfl) ⟨87722, by rfl⟩) R175445
theorem R280817 : Reach 280817 := rs (se 2 (by rfl) ⟨105306, by rfl⟩) R210613
theorem R51443 : Reach 51443 := rs (se 1 (by rfl) ⟨38582, by rfl⟩) R77165
theorem R51459 : Reach 51459 := rs (se 1 (by rfl) ⟨38594, by rfl⟩) R77189
theorem R51475 : Reach 51475 := rs (se 1 (by rfl) ⟨38606, by rfl⟩) R77213
theorem R51491 : Reach 51491 := rs (se 1 (by rfl) ⟨38618, by rfl⟩) R77237
theorem R51507 : Reach 51507 := rs (se 1 (by rfl) ⟨38630, by rfl⟩) R77261
theorem R51523 : Reach 51523 := rs (se 1 (by rfl) ⟨38642, by rfl⟩) R77285
theorem R248141 : Reach 248141 := rs (se 3 (by rfl) ⟨46526, by rfl⟩) R93053
theorem R117073 : Reach 117073 := rs (se 2 (by rfl) ⟨43902, by rfl⟩) R87805
theorem R51539 : Reach 51539 := rs (se 1 (by rfl) ⟨38654, by rfl⟩) R77309
theorem R51555 : Reach 51555 := rs (se 1 (by rfl) ⟨38666, by rfl⟩) R77333
theorem R182627 : Reach 182627 := rs (se 1 (by rfl) ⟨136970, by rfl⟩) R273941
theorem R51571 : Reach 51571 := rs (se 1 (by rfl) ⟨38678, by rfl⟩) R77357
theorem R51587 : Reach 51587 := rs (se 1 (by rfl) ⟨38690, by rfl⟩) R77381
theorem R51603 : Reach 51603 := rs (se 1 (by rfl) ⟨38702, by rfl⟩) R77405
theorem R51619 : Reach 51619 := rs (se 1 (by rfl) ⟨38714, by rfl⟩) R77429
theorem R51635 : Reach 51635 := rs (se 1 (by rfl) ⟨38726, by rfl⟩) R77453
theorem R51651 : Reach 51651 := rs (se 1 (by rfl) ⟨38738, by rfl⟩) R77477
theorem R51667 : Reach 51667 := rs (se 1 (by rfl) ⟨38750, by rfl⟩) R77501
theorem R51683 : Reach 51683 := rs (se 1 (by rfl) ⟨38762, by rfl⟩) R77525
theorem R117233 : Reach 117233 := rs (se 2 (by rfl) ⟨43962, by rfl⟩) R87925
theorem R51699 : Reach 51699 := rs (se 1 (by rfl) ⟨38774, by rfl⟩) R77549
theorem R51715 : Reach 51715 := rs (se 1 (by rfl) ⟨38786, by rfl⟩) R77573
theorem R117251 : Reach 117251 := rs (se 1 (by rfl) ⟨87938, by rfl⟩) R175877
theorem R51731 : Reach 51731 := rs (se 1 (by rfl) ⟨38798, by rfl⟩) R77597
theorem R51747 : Reach 51747 := rs (se 1 (by rfl) ⟨38810, by rfl⟩) R77621
theorem R51763 : Reach 51763 := rs (se 1 (by rfl) ⟨38822, by rfl⟩) R77645
theorem R51779 : Reach 51779 := rs (se 1 (by rfl) ⟨38834, by rfl⟩) R77669
theorem R150083 : Reach 150083 := rs (se 1 (by rfl) ⟨112562, by rfl⟩) R225125
theorem R51795 : Reach 51795 := rs (se 1 (by rfl) ⟨38846, by rfl⟩) R77693
theorem R51811 : Reach 51811 := rs (se 1 (by rfl) ⟨38858, by rfl⟩) R77717
theorem R182897 : Reach 182897 := rs (se 2 (by rfl) ⟨68586, by rfl⟩) R137173
theorem R51827 : Reach 51827 := rs (se 1 (by rfl) ⟨38870, by rfl⟩) R77741
theorem R51843 : Reach 51843 := rs (se 1 (by rfl) ⟨38882, by rfl⟩) R77765
theorem R51859 : Reach 51859 := rs (se 1 (by rfl) ⟨38894, by rfl⟩) R77789
theorem R51875 : Reach 51875 := rs (se 1 (by rfl) ⟨38906, by rfl⟩) R77813
theorem R51891 : Reach 51891 := rs (se 1 (by rfl) ⟨38918, by rfl⟩) R77837
theorem R51907 : Reach 51907 := rs (se 1 (by rfl) ⟨38930, by rfl⟩) R77861
theorem R51923 : Reach 51923 := rs (se 1 (by rfl) ⟨38942, by rfl⟩) R77885
theorem R84691 : Reach 84691 := rs (se 1 (by rfl) ⟨63518, by rfl⟩) R127037
theorem R51939 : Reach 51939 := rs (se 1 (by rfl) ⟨38954, by rfl⟩) R77909
theorem R51955 : Reach 51955 := rs (se 1 (by rfl) ⟨38966, by rfl⟩) R77933
theorem R51971 : Reach 51971 := rs (se 1 (by rfl) ⟨38978, by rfl⟩) R77957
theorem R117521 : Reach 117521 := rs (se 2 (by rfl) ⟨44070, by rfl⟩) R88141
theorem R51987 : Reach 51987 := rs (se 1 (by rfl) ⟨38990, by rfl⟩) R77981
theorem R52003 : Reach 52003 := rs (se 1 (by rfl) ⟨39002, by rfl⟩) R78005
theorem R117539 : Reach 117539 := rs (se 1 (by rfl) ⟨88154, by rfl⟩) R176309
theorem R52019 : Reach 52019 := rs (se 1 (by rfl) ⟨39014, by rfl⟩) R78029
theorem R52035 : Reach 52035 := rs (se 1 (by rfl) ⟨39026, by rfl⟩) R78053
theorem R52051 : Reach 52051 := rs (se 1 (by rfl) ⟨39038, by rfl⟩) R78077
theorem R52067 : Reach 52067 := rs (se 1 (by rfl) ⟨39050, by rfl⟩) R78101
theorem R52083 : Reach 52083 := rs (se 1 (by rfl) ⟨39062, by rfl⟩) R78125
theorem R52099 : Reach 52099 := rs (se 1 (by rfl) ⟨39074, by rfl⟩) R78149
theorem R52115 : Reach 52115 := rs (se 1 (by rfl) ⟨39086, by rfl⟩) R78173
theorem R52131 : Reach 52131 := rs (se 1 (by rfl) ⟨39098, by rfl⟩) R78197
theorem R52147 : Reach 52147 := rs (se 1 (by rfl) ⟨39110, by rfl⟩) R78221
theorem R52163 : Reach 52163 := rs (se 1 (by rfl) ⟨39122, by rfl⟩) R78245
theorem R412613 : Reach 412613 := rs (se 4 (by rfl) ⟨38682, by rfl⟩) R77365
theorem R52179 : Reach 52179 := rs (se 1 (by rfl) ⟨39134, by rfl⟩) R78269
theorem R52195 : Reach 52195 := rs (se 1 (by rfl) ⟨39146, by rfl⟩) R78293
theorem R52211 : Reach 52211 := rs (se 1 (by rfl) ⟨39158, by rfl⟩) R78317
theorem R52227 : Reach 52227 := rs (se 1 (by rfl) ⟨39170, by rfl⟩) R78341
theorem R150545 : Reach 150545 := rs (se 2 (by rfl) ⟨56454, by rfl⟩) R112909
theorem R52243 : Reach 52243 := rs (se 1 (by rfl) ⟨39182, by rfl⟩) R78365
theorem R52259 : Reach 52259 := rs (se 1 (by rfl) ⟨39194, by rfl⟩) R78389
theorem R117809 : Reach 117809 := rs (se 2 (by rfl) ⟨44178, by rfl⟩) R88357
theorem R52275 : Reach 52275 := rs (se 1 (by rfl) ⟨39206, by rfl⟩) R78413
theorem R52291 : Reach 52291 := rs (se 1 (by rfl) ⟨39218, by rfl⟩) R78437
theorem R117827 : Reach 117827 := rs (se 1 (by rfl) ⟨88370, by rfl⟩) R176741
theorem R52307 : Reach 52307 := rs (se 1 (by rfl) ⟨39230, by rfl⟩) R78461
theorem R52323 : Reach 52323 := rs (se 1 (by rfl) ⟨39242, by rfl⟩) R78485
theorem R52339 : Reach 52339 := rs (se 1 (by rfl) ⟨39254, by rfl⟩) R78509
theorem R52355 : Reach 52355 := rs (se 1 (by rfl) ⟨39266, by rfl⟩) R78533
theorem R183437 : Reach 183437 := rs (se 3 (by rfl) ⟨34394, by rfl⟩) R68789
theorem R52371 : Reach 52371 := rs (se 1 (by rfl) ⟨39278, by rfl⟩) R78557
theorem R52387 : Reach 52387 := rs (se 1 (by rfl) ⟨39290, by rfl⟩) R78581
theorem R85153 : Reach 85153 := rs (se 2 (by rfl) ⟨31932, by rfl⟩) R63865
theorem R52403 : Reach 52403 := rs (se 1 (by rfl) ⟨39302, by rfl⟩) R78605
theorem R52419 : Reach 52419 := rs (se 1 (by rfl) ⟨39314, by rfl⟩) R78629
theorem R52435 : Reach 52435 := rs (se 1 (by rfl) ⟨39326, by rfl⟩) R78653
theorem R52451 : Reach 52451 := rs (se 1 (by rfl) ⟨39338, by rfl⟩) R78677
theorem R52467 : Reach 52467 := rs (se 1 (by rfl) ⟨39350, by rfl⟩) R78701
theorem R52483 : Reach 52483 := rs (se 1 (by rfl) ⟨39362, by rfl⟩) R78725
theorem R52499 : Reach 52499 := rs (se 1 (by rfl) ⟨39374, by rfl⟩) R78749
theorem R52515 : Reach 52515 := rs (se 1 (by rfl) ⟨39386, by rfl⟩) R78773
theorem R52531 : Reach 52531 := rs (se 1 (by rfl) ⟨39398, by rfl⟩) R78797
theorem R52547 : Reach 52547 := rs (se 1 (by rfl) ⟨39410, by rfl⟩) R78821
theorem R118097 : Reach 118097 := rs (se 2 (by rfl) ⟨44286, by rfl⟩) R88573
theorem R52563 : Reach 52563 := rs (se 1 (by rfl) ⟨39422, by rfl⟩) R78845
theorem R118115 : Reach 118115 := rs (se 1 (by rfl) ⟨88586, by rfl⟩) R177173
theorem R52579 : Reach 52579 := rs (se 1 (by rfl) ⟨39434, by rfl⟩) R78869
theorem R150893 : Reach 150893 := rs (se 3 (by rfl) ⟨28292, by rfl⟩) R56585
theorem R52595 : Reach 52595 := rs (se 1 (by rfl) ⟨39446, by rfl⟩) R78893
theorem R52611 : Reach 52611 := rs (se 1 (by rfl) ⟨39458, by rfl⟩) R78917
theorem R52627 : Reach 52627 := rs (se 1 (by rfl) ⟨39470, by rfl⟩) R78941
theorem R52643 : Reach 52643 := rs (se 1 (by rfl) ⟨39482, by rfl⟩) R78965
theorem R52659 : Reach 52659 := rs (se 1 (by rfl) ⟨39494, by rfl⟩) R78989
theorem R52675 : Reach 52675 := rs (se 1 (by rfl) ⟨39506, by rfl⟩) R79013
theorem R249293 : Reach 249293 := rs (se 3 (by rfl) ⟨46742, by rfl⟩) R93485
theorem R52691 : Reach 52691 := rs (se 1 (by rfl) ⟨39518, by rfl⟩) R79037
theorem R52707 : Reach 52707 := rs (se 1 (by rfl) ⟨39530, by rfl⟩) R79061
theorem R52723 : Reach 52723 := rs (se 1 (by rfl) ⟨39542, by rfl⟩) R79085
theorem R52739 : Reach 52739 := rs (se 1 (by rfl) ⟨39554, by rfl⟩) R79109
theorem R52755 : Reach 52755 := rs (se 1 (by rfl) ⟨39566, by rfl⟩) R79133
theorem R52771 : Reach 52771 := rs (se 1 (by rfl) ⟨39578, by rfl⟩) R79157
theorem R151085 : Reach 151085 := rs (se 3 (by rfl) ⟨28328, by rfl⟩) R56657
theorem R52787 : Reach 52787 := rs (se 1 (by rfl) ⟨39590, by rfl⟩) R79181
theorem R52803 : Reach 52803 := rs (se 1 (by rfl) ⟨39602, by rfl⟩) R79205
theorem R249421 : Reach 249421 := rs (se 3 (by rfl) ⟨46766, by rfl⟩) R93533
theorem R52819 : Reach 52819 := rs (se 1 (by rfl) ⟨39614, by rfl⟩) R79229
theorem R85601 : Reach 85601 := rs (se 2 (by rfl) ⟨32100, by rfl⟩) R64201
theorem R52835 : Reach 52835 := rs (se 1 (by rfl) ⟨39626, by rfl⟩) R79253
theorem R118385 : Reach 118385 := rs (se 2 (by rfl) ⟨44394, by rfl⟩) R88789
theorem R52851 : Reach 52851 := rs (se 1 (by rfl) ⟨39638, by rfl⟩) R79277
theorem R118403 : Reach 118403 := rs (se 1 (by rfl) ⟨88802, by rfl⟩) R177605
theorem R52867 : Reach 52867 := rs (se 1 (by rfl) ⟨39650, by rfl⟩) R79301
theorem R118417 : Reach 118417 := rs (se 2 (by rfl) ⟨44406, by rfl⟩) R88813
theorem R52883 : Reach 52883 := rs (se 1 (by rfl) ⟨39662, by rfl⟩) R79325
theorem R52899 : Reach 52899 := rs (se 1 (by rfl) ⟨39674, by rfl⟩) R79349
theorem R52915 : Reach 52915 := rs (se 1 (by rfl) ⟨39686, by rfl⟩) R79373
theorem R52931 : Reach 52931 := rs (se 1 (by rfl) ⟨39698, by rfl⟩) R79397
theorem R52947 : Reach 52947 := rs (se 1 (by rfl) ⟨39710, by rfl⟩) R79421
theorem R52963 : Reach 52963 := rs (se 1 (by rfl) ⟨39722, by rfl⟩) R79445
theorem R52979 : Reach 52979 := rs (se 1 (by rfl) ⟨39734, by rfl⟩) R79469
theorem R52995 : Reach 52995 := rs (se 1 (by rfl) ⟨39746, by rfl⟩) R79493
theorem R53011 : Reach 53011 := rs (se 1 (by rfl) ⟨39758, by rfl⟩) R79517
theorem R53027 : Reach 53027 := rs (se 1 (by rfl) ⟨39770, by rfl⟩) R79541
theorem R347939 : Reach 347939 := rs (se 1 (by rfl) ⟨260954, by rfl⟩) R521909
theorem R53043 : Reach 53043 := rs (se 1 (by rfl) ⟨39782, by rfl⟩) R79565
theorem R53059 : Reach 53059 := rs (se 1 (by rfl) ⟨39794, by rfl⟩) R79589
theorem R53075 : Reach 53075 := rs (se 1 (by rfl) ⟨39806, by rfl⟩) R79613
theorem R53091 : Reach 53091 := rs (se 1 (by rfl) ⟨39818, by rfl⟩) R79637
theorem R249713 : Reach 249713 := rs (se 2 (by rfl) ⟨93642, by rfl⟩) R187285
theorem R53107 : Reach 53107 := rs (se 1 (by rfl) ⟨39830, by rfl⟩) R79661
theorem R53123 : Reach 53123 := rs (se 1 (by rfl) ⟨39842, by rfl⟩) R79685
theorem R118673 : Reach 118673 := rs (se 2 (by rfl) ⟨44502, by rfl⟩) R89005
theorem R53139 : Reach 53139 := rs (se 1 (by rfl) ⟨39854, by rfl⟩) R79709
theorem R118691 : Reach 118691 := rs (se 1 (by rfl) ⟨89018, by rfl⟩) R178037
theorem R53155 : Reach 53155 := rs (se 1 (by rfl) ⟨39866, by rfl⟩) R79733
theorem R53171 : Reach 53171 := rs (se 1 (by rfl) ⟨39878, by rfl⟩) R79757
theorem R53187 : Reach 53187 := rs (se 1 (by rfl) ⟨39890, by rfl⟩) R79781
theorem R53203 : Reach 53203 := rs (se 1 (by rfl) ⟨39902, by rfl⟩) R79805
theorem R53219 : Reach 53219 := rs (se 1 (by rfl) ⟨39914, by rfl⟩) R79829
theorem R53235 : Reach 53235 := rs (se 1 (by rfl) ⟨39926, by rfl⟩) R79853
theorem R53251 : Reach 53251 := rs (se 1 (by rfl) ⟨39938, by rfl⟩) R79877
theorem R53267 : Reach 53267 := rs (se 1 (by rfl) ⟨39950, by rfl⟩) R79901
theorem R53283 : Reach 53283 := rs (se 1 (by rfl) ⟨39962, by rfl⟩) R79925
theorem R184355 : Reach 184355 := rs (se 1 (by rfl) ⟨138266, by rfl⟩) R276533
theorem R53299 : Reach 53299 := rs (se 1 (by rfl) ⟨39974, by rfl⟩) R79949
theorem R53315 : Reach 53315 := rs (se 1 (by rfl) ⟨39986, by rfl⟩) R79973
theorem R53331 : Reach 53331 := rs (se 1 (by rfl) ⟨39998, by rfl⟩) R79997
theorem R53347 : Reach 53347 := rs (se 1 (by rfl) ⟨40010, by rfl⟩) R80021
theorem R53363 : Reach 53363 := rs (se 1 (by rfl) ⟨40022, by rfl⟩) R80045
theorem R53379 : Reach 53379 := rs (se 1 (by rfl) ⟨40034, by rfl⟩) R80069
theorem R53395 : Reach 53395 := rs (se 1 (by rfl) ⟨40046, by rfl⟩) R80093
theorem R53411 : Reach 53411 := rs (se 1 (by rfl) ⟨40058, by rfl⟩) R80117
theorem R118961 : Reach 118961 := rs (se 2 (by rfl) ⟨44610, by rfl⟩) R89221
theorem R53427 : Reach 53427 := rs (se 1 (by rfl) ⟨40070, by rfl⟩) R80141
theorem R118979 : Reach 118979 := rs (se 1 (by rfl) ⟨89234, by rfl⟩) R178469
theorem R53443 : Reach 53443 := rs (se 1 (by rfl) ⟨40082, by rfl⟩) R80165
theorem R53459 : Reach 53459 := rs (se 1 (by rfl) ⟨40094, by rfl⟩) R80189
theorem R53475 : Reach 53475 := rs (se 1 (by rfl) ⟨40106, by rfl⟩) R80213
theorem R348401 : Reach 348401 := rs (se 2 (by rfl) ⟨130650, by rfl⟩) R261301
theorem R53491 : Reach 53491 := rs (se 1 (by rfl) ⟨40118, by rfl⟩) R80237
theorem R53507 : Reach 53507 := rs (se 1 (by rfl) ⟨40130, by rfl⟩) R80261
theorem R53523 : Reach 53523 := rs (se 1 (by rfl) ⟨40142, by rfl⟩) R80285
theorem R86305 : Reach 86305 := rs (se 2 (by rfl) ⟨32364, by rfl⟩) R64729
theorem R53539 : Reach 53539 := rs (se 1 (by rfl) ⟨40154, by rfl⟩) R80309
theorem R184625 : Reach 184625 := rs (se 2 (by rfl) ⟨69234, by rfl⟩) R138469
theorem R53555 : Reach 53555 := rs (se 1 (by rfl) ⟨40166, by rfl⟩) R80333
theorem R86339 : Reach 86339 := rs (se 1 (by rfl) ⟨64754, by rfl⟩) R129509
theorem R53571 : Reach 53571 := rs (se 1 (by rfl) ⟨40178, by rfl⟩) R80357
theorem R53587 : Reach 53587 := rs (se 1 (by rfl) ⟨40190, by rfl⟩) R80381
theorem R53603 : Reach 53603 := rs (se 1 (by rfl) ⟨40202, by rfl⟩) R80405
theorem R53619 : Reach 53619 := rs (se 1 (by rfl) ⟨40214, by rfl⟩) R80429
theorem R53635 : Reach 53635 := rs (se 1 (by rfl) ⟨40226, by rfl⟩) R80453
theorem R53651 : Reach 53651 := rs (se 1 (by rfl) ⟨40238, by rfl⟩) R80477
theorem R53667 : Reach 53667 := rs (se 1 (by rfl) ⟨40250, by rfl⟩) R80501
theorem R53683 : Reach 53683 := rs (se 1 (by rfl) ⟨40262, by rfl⟩) R80525
theorem R86467 : Reach 86467 := rs (se 1 (by rfl) ⟨64850, by rfl⟩) R129701
theorem R53699 : Reach 53699 := rs (se 1 (by rfl) ⟨40274, by rfl⟩) R80549
theorem R119249 : Reach 119249 := rs (se 2 (by rfl) ⟨44718, by rfl⟩) R89437
theorem R53715 : Reach 53715 := rs (se 1 (by rfl) ⟨40286, by rfl⟩) R80573
theorem R119267 : Reach 119267 := rs (se 1 (by rfl) ⟨89450, by rfl⟩) R178901
theorem R53731 : Reach 53731 := rs (se 1 (by rfl) ⟨40298, by rfl⟩) R80597
theorem R53747 : Reach 53747 := rs (se 1 (by rfl) ⟨40310, by rfl⟩) R80621
theorem R53763 : Reach 53763 := rs (se 1 (by rfl) ⟨40322, by rfl⟩) R80645
theorem R152077 : Reach 152077 := rs (se 3 (by rfl) ⟨28514, by rfl⟩) R57029
theorem R53779 : Reach 53779 := rs (se 1 (by rfl) ⟨40334, by rfl⟩) R80669
theorem R53795 : Reach 53795 := rs (se 1 (by rfl) ⟨40346, by rfl⟩) R80693
theorem R53811 : Reach 53811 := rs (se 1 (by rfl) ⟨40358, by rfl⟩) R80717
theorem R53827 : Reach 53827 := rs (se 1 (by rfl) ⟨40370, by rfl⟩) R80741
theorem R86609 : Reach 86609 := rs (se 2 (by rfl) ⟨32478, by rfl⟩) R64957
theorem R53843 : Reach 53843 := rs (se 1 (by rfl) ⟨40382, by rfl⟩) R80765
theorem R53859 : Reach 53859 := rs (se 1 (by rfl) ⟨40394, by rfl⟩) R80789
theorem R53875 : Reach 53875 := rs (se 1 (by rfl) ⟨40406, by rfl⟩) R80813
theorem R53891 : Reach 53891 := rs (se 1 (by rfl) ⟨40418, by rfl⟩) R80837
theorem R53907 : Reach 53907 := rs (se 1 (by rfl) ⟨40430, by rfl⟩) R80861
theorem R53923 : Reach 53923 := rs (se 1 (by rfl) ⟨40442, by rfl⟩) R80885
theorem R53939 : Reach 53939 := rs (se 1 (by rfl) ⟨40454, by rfl⟩) R80909
theorem R53955 : Reach 53955 := rs (se 1 (by rfl) ⟨40466, by rfl⟩) R80933
theorem R86737 : Reach 86737 := rs (se 2 (by rfl) ⟨32526, by rfl⟩) R65053
theorem R53971 : Reach 53971 := rs (se 1 (by rfl) ⟨40478, by rfl⟩) R80957
theorem R53987 : Reach 53987 := rs (se 1 (by rfl) ⟨40490, by rfl⟩) R80981
theorem R119537 : Reach 119537 := rs (se 2 (by rfl) ⟨44826, by rfl⟩) R89653
theorem R86771 : Reach 86771 := rs (se 1 (by rfl) ⟨65078, by rfl⟩) R130157
theorem R54003 : Reach 54003 := rs (se 1 (by rfl) ⟨40502, by rfl⟩) R81005
theorem R119555 : Reach 119555 := rs (se 1 (by rfl) ⟨89666, by rfl⟩) R179333
theorem R54019 : Reach 54019 := rs (se 1 (by rfl) ⟨40514, by rfl⟩) R81029
theorem R54035 : Reach 54035 := rs (se 1 (by rfl) ⟨40526, by rfl⟩) R81053
theorem R54051 : Reach 54051 := rs (se 1 (by rfl) ⟨40538, by rfl⟩) R81077
theorem R54067 : Reach 54067 := rs (se 1 (by rfl) ⟨40550, by rfl⟩) R81101
theorem R54083 : Reach 54083 := rs (se 1 (by rfl) ⟨40562, by rfl⟩) R81125
theorem R512837 : Reach 512837 := rs (se 4 (by rfl) ⟨48078, by rfl⟩) R96157
theorem R185165 : Reach 185165 := rs (se 3 (by rfl) ⟨34718, by rfl⟩) R69437
theorem R54099 : Reach 54099 := rs (se 1 (by rfl) ⟨40574, by rfl⟩) R81149
theorem R54115 : Reach 54115 := rs (se 1 (by rfl) ⟨40586, by rfl⟩) R81173
theorem R86899 : Reach 86899 := rs (se 1 (by rfl) ⟨65174, by rfl⟩) R130349
theorem R54131 : Reach 54131 := rs (se 1 (by rfl) ⟨40598, by rfl⟩) R81197
theorem R54147 : Reach 54147 := rs (se 1 (by rfl) ⟨40610, by rfl⟩) R81221
theorem R54163 : Reach 54163 := rs (se 1 (by rfl) ⟨40622, by rfl⟩) R81245
theorem R54179 : Reach 54179 := rs (se 1 (by rfl) ⟨40634, by rfl⟩) R81269
theorem R54195 : Reach 54195 := rs (se 1 (by rfl) ⟨40646, by rfl⟩) R81293
theorem R54211 : Reach 54211 := rs (se 1 (by rfl) ⟨40658, by rfl⟩) R81317
theorem R54227 : Reach 54227 := rs (se 1 (by rfl) ⟨40670, by rfl⟩) R81341
theorem R54243 : Reach 54243 := rs (se 1 (by rfl) ⟨40682, by rfl⟩) R81365
theorem R87011 : Reach 87011 := rs (se 1 (by rfl) ⟨65258, by rfl⟩) R130517
theorem R54259 : Reach 54259 := rs (se 1 (by rfl) ⟨40694, by rfl⟩) R81389
theorem R87041 : Reach 87041 := rs (se 2 (by rfl) ⟨32640, by rfl⟩) R65281
theorem R54275 : Reach 54275 := rs (se 1 (by rfl) ⟨40706, by rfl⟩) R81413
theorem R119825 : Reach 119825 := rs (se 2 (by rfl) ⟨44934, by rfl⟩) R89869
theorem R54291 : Reach 54291 := rs (se 1 (by rfl) ⟨40718, by rfl⟩) R81437
theorem R119843 : Reach 119843 := rs (se 1 (by rfl) ⟨89882, by rfl⟩) R179765
theorem R54307 : Reach 54307 := rs (se 1 (by rfl) ⟨40730, by rfl⟩) R81461
theorem R54323 : Reach 54323 := rs (se 1 (by rfl) ⟨40742, by rfl⟩) R81485
theorem R54339 : Reach 54339 := rs (se 1 (by rfl) ⟨40754, by rfl⟩) R81509
theorem R54355 : Reach 54355 := rs (se 1 (by rfl) ⟨40766, by rfl⟩) R81533
theorem R54371 : Reach 54371 := rs (se 1 (by rfl) ⟨40778, by rfl⟩) R81557
theorem R54387 : Reach 54387 := rs (se 1 (by rfl) ⟨40790, by rfl⟩) R81581
theorem R87169 : Reach 87169 := rs (se 2 (by rfl) ⟨32688, by rfl⟩) R65377
theorem R54403 : Reach 54403 := rs (se 1 (by rfl) ⟨40802, by rfl⟩) R81605
theorem R54419 : Reach 54419 := rs (se 1 (by rfl) ⟨40814, by rfl⟩) R81629
theorem R87203 : Reach 87203 := rs (se 1 (by rfl) ⟨65402, by rfl⟩) R130805
theorem R54435 : Reach 54435 := rs (se 1 (by rfl) ⟨40826, by rfl⟩) R81653
theorem R54451 : Reach 54451 := rs (se 1 (by rfl) ⟨40838, by rfl⟩) R81677
theorem R54467 : Reach 54467 := rs (se 1 (by rfl) ⟨40850, by rfl⟩) R81701
theorem R54483 : Reach 54483 := rs (se 1 (by rfl) ⟨40862, by rfl⟩) R81725
theorem R939235 : Reach 939235 := rs (se 1 (by rfl) ⟨704426, by rfl⟩) R1408853
theorem R54499 : Reach 54499 := rs (se 1 (by rfl) ⟨40874, by rfl⟩) R81749
theorem R54515 : Reach 54515 := rs (se 1 (by rfl) ⟨40886, by rfl⟩) R81773
theorem R54531 : Reach 54531 := rs (se 1 (by rfl) ⟨40898, by rfl⟩) R81797
theorem R54547 : Reach 54547 := rs (se 1 (by rfl) ⟨40910, by rfl⟩) R81821
theorem R87331 : Reach 87331 := rs (se 1 (by rfl) ⟨65498, by rfl⟩) R130997
theorem R54563 : Reach 54563 := rs (se 1 (by rfl) ⟨40922, by rfl⟩) R81845
theorem R120113 : Reach 120113 := rs (se 2 (by rfl) ⟨45042, by rfl⟩) R90085
theorem R54579 : Reach 54579 := rs (se 1 (by rfl) ⟨40934, by rfl⟩) R81869
theorem R120131 : Reach 120131 := rs (se 1 (by rfl) ⟨90098, by rfl⟩) R180197
theorem R54595 : Reach 54595 := rs (se 1 (by rfl) ⟨40946, by rfl⟩) R81893
theorem R54611 : Reach 54611 := rs (se 1 (by rfl) ⟨40958, by rfl⟩) R81917
theorem R54627 : Reach 54627 := rs (se 1 (by rfl) ⟨40970, by rfl⟩) R81941
theorem R54643 : Reach 54643 := rs (se 1 (by rfl) ⟨40982, by rfl⟩) R81965
theorem R54659 : Reach 54659 := rs (se 1 (by rfl) ⟨40994, by rfl⟩) R81989
theorem R54675 : Reach 54675 := rs (se 1 (by rfl) ⟨41006, by rfl⟩) R82013
theorem R54691 : Reach 54691 := rs (se 1 (by rfl) ⟨41018, by rfl⟩) R82037
theorem R87473 : Reach 87473 := rs (se 2 (by rfl) ⟨32802, by rfl⟩) R65605
theorem R54707 : Reach 54707 := rs (se 1 (by rfl) ⟨41030, by rfl⟩) R82061
theorem R54723 : Reach 54723 := rs (se 1 (by rfl) ⟨41042, by rfl⟩) R82085
theorem R54739 : Reach 54739 := rs (se 1 (by rfl) ⟨41054, by rfl⟩) R82109
theorem R185827 : Reach 185827 := rs (se 1 (by rfl) ⟨139370, by rfl⟩) R278741
theorem R54755 : Reach 54755 := rs (se 1 (by rfl) ⟨41066, by rfl⟩) R82133
theorem R54771 : Reach 54771 := rs (se 1 (by rfl) ⟨41078, by rfl⟩) R82157
theorem R54787 : Reach 54787 := rs (se 1 (by rfl) ⟨41090, by rfl⟩) R82181
theorem R54803 : Reach 54803 := rs (se 1 (by rfl) ⟨41102, by rfl⟩) R82205
theorem R218659 : Reach 218659 := rs (se 1 (by rfl) ⟨163994, by rfl⟩) R327989
theorem R54819 : Reach 54819 := rs (se 1 (by rfl) ⟨41114, by rfl⟩) R82229
theorem R87601 : Reach 87601 := rs (se 2 (by rfl) ⟨32850, by rfl⟩) R65701
theorem R54835 : Reach 54835 := rs (se 1 (by rfl) ⟨41126, by rfl⟩) R82253
theorem R54851 : Reach 54851 := rs (se 1 (by rfl) ⟨41138, by rfl⟩) R82277
theorem R120401 : Reach 120401 := rs (se 2 (by rfl) ⟨45150, by rfl⟩) R90301
theorem R87635 : Reach 87635 := rs (se 1 (by rfl) ⟨65726, by rfl⟩) R131453
theorem R54867 : Reach 54867 := rs (se 1 (by rfl) ⟨41150, by rfl⟩) R82301
theorem R120419 : Reach 120419 := rs (se 1 (by rfl) ⟨90314, by rfl⟩) R180629
theorem R54883 : Reach 54883 := rs (se 1 (by rfl) ⟨41162, by rfl⟩) R82325
theorem R54899 : Reach 54899 := rs (se 1 (by rfl) ⟨41174, by rfl⟩) R82349
theorem R54915 : Reach 54915 := rs (se 1 (by rfl) ⟨41186, by rfl⟩) R82373
theorem R54931 : Reach 54931 := rs (se 1 (by rfl) ⟨41198, by rfl⟩) R82397
theorem R54947 : Reach 54947 := rs (se 1 (by rfl) ⟨41210, by rfl⟩) R82421
theorem R54963 : Reach 54963 := rs (se 1 (by rfl) ⟨41222, by rfl⟩) R82445
theorem R54979 : Reach 54979 := rs (se 1 (by rfl) ⟨41234, by rfl⟩) R82469
theorem R87763 : Reach 87763 := rs (se 1 (by rfl) ⟨65822, by rfl⟩) R131645
theorem R54995 : Reach 54995 := rs (se 1 (by rfl) ⟨41246, by rfl⟩) R82493
theorem R55011 : Reach 55011 := rs (se 1 (by rfl) ⟨41258, by rfl⟩) R82517
theorem R55027 : Reach 55027 := rs (se 1 (by rfl) ⟨41270, by rfl⟩) R82541
theorem R55043 : Reach 55043 := rs (se 1 (by rfl) ⟨41282, by rfl⟩) R82565
theorem R55059 : Reach 55059 := rs (se 1 (by rfl) ⟨41294, by rfl⟩) R82589
theorem R55075 : Reach 55075 := rs (se 1 (by rfl) ⟨41306, by rfl⟩) R82613
theorem R55091 : Reach 55091 := rs (se 1 (by rfl) ⟨41318, by rfl⟩) R82637
theorem R55107 : Reach 55107 := rs (se 1 (by rfl) ⟨41330, by rfl⟩) R82661
theorem R87905 : Reach 87905 := rs (se 2 (by rfl) ⟨32964, by rfl⟩) R65929
theorem R120689 : Reach 120689 := rs (se 2 (by rfl) ⟨45258, by rfl⟩) R90517
theorem R55171 : Reach 55171 := rs (se 1 (by rfl) ⟨41378, by rfl⟩) R82757
theorem R120707 : Reach 120707 := rs (se 1 (by rfl) ⟨90530, by rfl⟩) R181061
theorem R284579 : Reach 284579 := rs (se 1 (by rfl) ⟨213434, by rfl⟩) R426869
theorem R186317 : Reach 186317 := rs (se 3 (by rfl) ⟨34934, by rfl⟩) R69869
theorem R88033 : Reach 88033 := rs (se 2 (by rfl) ⟨33012, by rfl⟩) R66025
theorem R88067 : Reach 88067 := rs (se 1 (by rfl) ⟨66050, by rfl⟩) R132101
theorem R88195 : Reach 88195 := rs (se 1 (by rfl) ⟨66146, by rfl⟩) R132293
theorem R120977 : Reach 120977 := rs (se 2 (by rfl) ⟨45366, by rfl⟩) R90733
theorem R120995 : Reach 120995 := rs (se 1 (by rfl) ⟨90746, by rfl⟩) R181493
theorem R186545 : Reach 186545 := rs (se 2 (by rfl) ⟨69954, by rfl⟩) R139909
theorem R153809 : Reach 153809 := rs (se 2 (by rfl) ⟨57678, by rfl⟩) R115357
theorem R252173 : Reach 252173 := rs (se 3 (by rfl) ⟨47282, by rfl⟩) R94565
theorem R88337 : Reach 88337 := rs (se 2 (by rfl) ⟨33126, by rfl⟩) R66253
theorem R88465 : Reach 88465 := rs (se 2 (by rfl) ⟨33174, by rfl⟩) R66349
theorem R154001 : Reach 154001 := rs (se 2 (by rfl) ⟨57750, by rfl⟩) R115501
theorem R121265 : Reach 121265 := rs (se 2 (by rfl) ⟨45474, by rfl⟩) R90949
theorem R88499 : Reach 88499 := rs (se 1 (by rfl) ⟨66374, by rfl⟩) R132749
theorem R121283 : Reach 121283 := rs (se 1 (by rfl) ⟨90962, by rfl⟩) R181925
theorem R88627 : Reach 88627 := rs (se 1 (by rfl) ⟨66470, by rfl⟩) R132941
theorem R88769 : Reach 88769 := rs (se 2 (by rfl) ⟨33288, by rfl⟩) R66577
theorem R121553 : Reach 121553 := rs (se 2 (by rfl) ⟨45582, by rfl⟩) R91165
theorem R121571 : Reach 121571 := rs (se 1 (by rfl) ⟨91178, by rfl⟩) R182357
theorem R88897 : Reach 88897 := rs (se 2 (by rfl) ⟨33336, by rfl⟩) R66673
theorem R88931 : Reach 88931 := rs (se 1 (by rfl) ⟨66698, by rfl⟩) R133397
theorem R220067 : Reach 220067 := rs (se 1 (by rfl) ⟨165050, by rfl⟩) R330101
theorem R89059 : Reach 89059 := rs (se 1 (by rfl) ⟨66794, by rfl⟩) R133589
theorem R711665 : Reach 711665 := rs (se 2 (by rfl) ⟨266874, by rfl⟩) R533749
theorem R121841 : Reach 121841 := rs (se 2 (by rfl) ⟨45690, by rfl⟩) R91381
theorem R121859 : Reach 121859 := rs (se 1 (by rfl) ⟨91394, by rfl⟩) R182789
theorem R89201 : Reach 89201 := rs (se 2 (by rfl) ⟨33450, by rfl⟩) R66901
theorem R56435 : Reach 56435 := rs (se 1 (by rfl) ⟨42326, by rfl⟩) R84653
theorem R89329 : Reach 89329 := rs (se 2 (by rfl) ⟨33498, by rfl⟩) R66997
theorem R122129 : Reach 122129 := rs (se 2 (by rfl) ⟨45798, by rfl⟩) R91597
theorem R89363 : Reach 89363 := rs (se 1 (by rfl) ⟨67022, by rfl⟩) R134045
theorem R122147 : Reach 122147 := rs (se 1 (by rfl) ⟨91610, by rfl⟩) R183221
theorem R154993 : Reach 154993 := rs (se 2 (by rfl) ⟨58122, by rfl⟩) R116245
theorem R89491 : Reach 89491 := rs (se 1 (by rfl) ⟨67118, by rfl⟩) R134237
theorem R89633 : Reach 89633 := rs (se 2 (by rfl) ⟨33612, by rfl⟩) R67225
theorem R122417 : Reach 122417 := rs (se 2 (by rfl) ⟨45906, by rfl⟩) R91813
theorem R122435 : Reach 122435 := rs (se 1 (by rfl) ⟨91826, by rfl⟩) R183653
theorem R155267 : Reach 155267 := rs (se 1 (by rfl) ⟨116450, by rfl⟩) R232901
theorem R89761 : Reach 89761 := rs (se 2 (by rfl) ⟨33660, by rfl⟩) R67321
theorem R89795 : Reach 89795 := rs (se 1 (by rfl) ⟨67346, by rfl⟩) R134693
theorem R89923 : Reach 89923 := rs (se 1 (by rfl) ⟨67442, by rfl⟩) R134885
theorem R155459 : Reach 155459 := rs (se 1 (by rfl) ⟨116594, by rfl⟩) R233189
theorem R122705 : Reach 122705 := rs (se 2 (by rfl) ⟨46014, by rfl⟩) R92029
theorem R57187 : Reach 57187 := rs (se 1 (by rfl) ⟨42890, by rfl⟩) R85781
theorem R122723 : Reach 122723 := rs (se 1 (by rfl) ⟨92042, by rfl⟩) R184085
theorem R90065 : Reach 90065 := rs (se 2 (by rfl) ⟨33774, by rfl⟩) R67549
theorem R90193 : Reach 90193 := rs (se 2 (by rfl) ⟨33822, by rfl⟩) R67645
theorem R57443 : Reach 57443 := rs (se 1 (by rfl) ⟨43082, by rfl⟩) R86165
theorem R122993 : Reach 122993 := rs (se 2 (by rfl) ⟨46122, by rfl⟩) R92245
theorem R90227 : Reach 90227 := rs (se 1 (by rfl) ⟨67670, by rfl⟩) R135341
theorem R123011 : Reach 123011 := rs (se 1 (by rfl) ⟨92258, by rfl⟩) R184517
theorem R57523 : Reach 57523 := rs (se 1 (by rfl) ⟨43142, by rfl⟩) R86285
theorem R90355 : Reach 90355 := rs (se 1 (by rfl) ⟨67766, by rfl⟩) R135533
theorem R57667 : Reach 57667 := rs (se 1 (by rfl) ⟨43250, by rfl⟩) R86501
theorem R90497 : Reach 90497 := rs (se 2 (by rfl) ⟨33936, by rfl⟩) R67873
theorem R123281 : Reach 123281 := rs (se 2 (by rfl) ⟨46230, by rfl⟩) R92461
theorem R123299 : Reach 123299 := rs (se 1 (by rfl) ⟨92474, by rfl⟩) R184949
theorem R57811 : Reach 57811 := rs (se 1 (by rfl) ⟨43358, by rfl⟩) R86717
theorem R90625 : Reach 90625 := rs (se 2 (by rfl) ⟨33984, by rfl⟩) R67969
theorem R90659 : Reach 90659 := rs (se 1 (by rfl) ⟨67994, by rfl⟩) R135989
theorem R57955 : Reach 57955 := rs (se 1 (by rfl) ⟨43466, by rfl⟩) R86933
theorem R156269 : Reach 156269 := rs (se 3 (by rfl) ⟨29300, by rfl⟩) R58601
theorem R418445 : Reach 418445 := rs (se 3 (by rfl) ⟨78458, by rfl⟩) R156917
theorem R90787 : Reach 90787 := rs (se 1 (by rfl) ⟨68090, by rfl⟩) R136181
theorem R123569 : Reach 123569 := rs (se 2 (by rfl) ⟨46338, by rfl⟩) R92677
theorem R123587 : Reach 123587 := rs (se 1 (by rfl) ⟨92690, by rfl⟩) R185381
theorem R58099 : Reach 58099 := rs (se 1 (by rfl) ⟨43574, by rfl⟩) R87149
theorem R156451 : Reach 156451 := rs (se 1 (by rfl) ⟨117338, by rfl⟩) R234677
theorem R90929 : Reach 90929 := rs (se 2 (by rfl) ⟨34098, by rfl⟩) R68197
theorem R58195 : Reach 58195 := rs (se 1 (by rfl) ⟨43646, by rfl⟩) R87293
theorem R58243 : Reach 58243 := rs (se 1 (by rfl) ⟨43682, by rfl⟩) R87365
theorem R91057 : Reach 91057 := rs (se 2 (by rfl) ⟨34146, by rfl⟩) R68293
theorem R123857 : Reach 123857 := rs (se 2 (by rfl) ⟨46446, by rfl⟩) R92893
theorem R123875 : Reach 123875 := rs (se 1 (by rfl) ⟨92906, by rfl⟩) R185813
theorem R58387 : Reach 58387 := rs (se 1 (by rfl) ⟨43790, by rfl⟩) R87581
theorem R58531 : Reach 58531 := rs (se 1 (by rfl) ⟨43898, by rfl⟩) R87797
theorem R124145 : Reach 124145 := rs (se 2 (by rfl) ⟨46554, by rfl⟩) R93109
theorem R156941 : Reach 156941 := rs (se 3 (by rfl) ⟨29426, by rfl⟩) R58853
theorem R58675 : Reach 58675 := rs (se 1 (by rfl) ⟨44006, by rfl⟩) R88013
theorem R91523 : Reach 91523 := rs (se 1 (by rfl) ⟨68642, by rfl⟩) R137285
theorem R58819 : Reach 58819 := rs (se 1 (by rfl) ⟨44114, by rfl⟩) R88229
theorem R91651 : Reach 91651 := rs (se 1 (by rfl) ⟨68738, by rfl⟩) R137477
theorem R321029 : Reach 321029 := rs (se 4 (by rfl) ⟨30096, by rfl⟩) R60193
theorem R58963 : Reach 58963 := rs (se 1 (by rfl) ⟨44222, by rfl⟩) R88445
theorem R91793 : Reach 91793 := rs (se 2 (by rfl) ⟨34422, by rfl⟩) R68845
theorem R124625 : Reach 124625 := rs (se 2 (by rfl) ⟨46734, by rfl⟩) R93469
theorem R59107 : Reach 59107 := rs (se 1 (by rfl) ⟨44330, by rfl⟩) R88661
theorem R91921 : Reach 91921 := rs (se 2 (by rfl) ⟨34470, by rfl⟩) R68941
theorem R59251 : Reach 59251 := rs (se 1 (by rfl) ⟨44438, by rfl⟩) R88877
theorem R59395 : Reach 59395 := rs (se 1 (by rfl) ⟨44546, by rfl⟩) R89093
theorem R59539 : Reach 59539 := rs (se 1 (by rfl) ⟨44654, by rfl⟩) R89309
theorem R157859 : Reach 157859 := rs (se 1 (by rfl) ⟨118394, by rfl⟩) R236789
theorem R583861 : Reach 583861 := rs (se 5 (by rfl) ⟨27368, by rfl⟩) R54737
theorem R92387 : Reach 92387 := rs (se 1 (by rfl) ⟨69290, by rfl⟩) R138581
theorem R387341 : Reach 387341 := rs (se 3 (by rfl) ⟨72626, by rfl⟩) R145253
theorem R59683 : Reach 59683 := rs (se 1 (by rfl) ⟨44762, by rfl⟩) R89525
theorem R92515 : Reach 92515 := rs (se 1 (by rfl) ⟨69386, by rfl⟩) R138773
theorem R59827 : Reach 59827 := rs (se 1 (by rfl) ⟨44870, by rfl⟩) R89741
theorem R92657 : Reach 92657 := rs (se 2 (by rfl) ⟨34746, by rfl⟩) R69493
theorem R256547 : Reach 256547 := rs (se 1 (by rfl) ⟨192410, by rfl⟩) R384821
theorem R223793 : Reach 223793 := rs (se 2 (by rfl) ⟨83922, by rfl⟩) R167845
theorem R59971 : Reach 59971 := rs (se 1 (by rfl) ⟨44978, by rfl⟩) R89957
theorem R158275 : Reach 158275 := rs (se 1 (by rfl) ⟨118706, by rfl⟩) R237413
theorem R289379 : Reach 289379 := rs (se 1 (by rfl) ⟨217034, by rfl⟩) R434069
theorem R191089 : Reach 191089 := rs (se 2 (by rfl) ⟨71658, by rfl⟩) R143317
theorem R92785 : Reach 92785 := rs (se 2 (by rfl) ⟨34794, by rfl⟩) R69589
theorem R60115 : Reach 60115 := rs (se 1 (by rfl) ⟨45086, by rfl⟩) R90173
theorem R453347 : Reach 453347 := rs (se 1 (by rfl) ⟨340010, by rfl⟩) R680021
theorem R60259 : Reach 60259 := rs (se 1 (by rfl) ⟨45194, by rfl⟩) R90389
theorem R519139 : Reach 519139 := rs (se 1 (by rfl) ⟨389354, by rfl⟩) R778709
theorem R60403 : Reach 60403 := rs (se 1 (by rfl) ⟨45302, by rfl⟩) R90605
theorem R93233 : Reach 93233 := rs (se 2 (by rfl) ⟨34962, by rfl⟩) R69925
theorem R60547 : Reach 60547 := rs (se 1 (by rfl) ⟨45410, by rfl⟩) R90821
theorem R158897 : Reach 158897 := rs (se 2 (by rfl) ⟨59586, by rfl⟩) R119173
theorem R126211 : Reach 126211 := rs (se 1 (by rfl) ⟨94658, by rfl⟩) R189317
theorem R60691 : Reach 60691 := rs (se 1 (by rfl) ⟨45518, by rfl⟩) R91037
theorem R60835 : Reach 60835 := rs (se 1 (by rfl) ⟨45626, by rfl⟩) R91253
theorem R60979 : Reach 60979 := rs (se 1 (by rfl) ⟨45734, by rfl⟩) R91469
theorem R61123 : Reach 61123 := rs (se 1 (by rfl) ⟨45842, by rfl⟩) R91685
theorem R126787 : Reach 126787 := rs (se 1 (by rfl) ⟨95090, by rfl⟩) R190181
theorem R61267 : Reach 61267 := rs (se 1 (by rfl) ⟨45950, by rfl⟩) R91901
theorem R487309 : Reach 487309 := rs (se 3 (by rfl) ⟨91370, by rfl⟩) R182741
theorem R61411 : Reach 61411 := rs (se 1 (by rfl) ⟨46058, by rfl⟩) R92117
theorem R61555 : Reach 61555 := rs (se 1 (by rfl) ⟨46166, by rfl⟩) R92333
theorem R127171 : Reach 127171 := rs (se 1 (by rfl) ⟨95378, by rfl⟩) R190757
theorem R61699 : Reach 61699 := rs (se 1 (by rfl) ⟨46274, by rfl⟩) R92549
theorem R61843 : Reach 61843 := rs (se 1 (by rfl) ⟨46382, by rfl⟩) R92765
theorem R291235 : Reach 291235 := rs (se 1 (by rfl) ⟨218426, by rfl⟩) R436853
theorem R61987 : Reach 61987 := rs (se 1 (by rfl) ⟨46490, by rfl⟩) R92981
theorem R291761 : Reach 291761 := rs (se 2 (by rfl) ⟨109410, by rfl⟩) R218821
theorem R226253 : Reach 226253 := rs (se 3 (by rfl) ⟨42422, by rfl⟩) R84845
theorem R128017 : Reach 128017 := rs (se 2 (by rfl) ⟨48006, by rfl⟩) R96013
theorem R390257 : Reach 390257 := rs (se 2 (by rfl) ⟨146346, by rfl⟩) R292693
theorem R62851 : Reach 62851 := rs (se 1 (by rfl) ⟨47138, by rfl⟩) R94277
theorem R161489 : Reach 161489 := rs (se 2 (by rfl) ⟨60558, by rfl⟩) R121117
theorem R194339 : Reach 194339 := rs (se 1 (by rfl) ⟨145754, by rfl⟩) R291509
theorem R587573 : Reach 587573 := rs (se 5 (by rfl) ⟨27542, by rfl⟩) R55085
theorem R325795 : Reach 325795 := rs (se 1 (by rfl) ⟨244346, by rfl⟩) R488693
theorem R227569 : Reach 227569 := rs (se 2 (by rfl) ⟨85338, by rfl⟩) R170677
theorem R96547 : Reach 96547 := rs (se 1 (by rfl) ⟨72410, by rfl⟩) R144821
theorem R293219 : Reach 293219 := rs (se 1 (by rfl) ⟨219914, by rfl⟩) R439829
theorem R194993 : Reach 194993 := rs (se 2 (by rfl) ⟨73122, by rfl⟩) R146245
theorem R653795 : Reach 653795 := rs (se 1 (by rfl) ⟨490346, by rfl⟩) R980693
theorem R129539 : Reach 129539 := rs (se 1 (by rfl) ⟨97154, by rfl⟩) R194309
theorem R260657 : Reach 260657 := rs (se 2 (by rfl) ⟨97746, by rfl⟩) R195493
theorem R359075 : Reach 359075 := rs (se 1 (by rfl) ⟨269306, by rfl⟩) R538613
theorem R64643 : Reach 64643 := rs (se 1 (by rfl) ⟨48482, by rfl⟩) R96965
theorem R64739 : Reach 64739 := rs (se 1 (by rfl) ⟨48554, by rfl⟩) R97109
theorem R130481 : Reach 130481 := rs (se 2 (by rfl) ⟨48930, by rfl⟩) R97861
theorem R130531 : Reach 130531 := rs (se 1 (by rfl) ⟨97898, by rfl⟩) R195797
theorem R97777 : Reach 97777 := rs (se 2 (by rfl) ⟨36666, by rfl⟩) R73333
theorem R130673 : Reach 130673 := rs (se 2 (by rfl) ⟨49002, by rfl⟩) R98005
theorem R196451 : Reach 196451 := rs (se 1 (by rfl) ⟨147338, by rfl⟩) R294677
theorem R98147 : Reach 98147 := rs (se 1 (by rfl) ⟨73610, by rfl⟩) R147221
theorem R196465 : Reach 196465 := rs (se 2 (by rfl) ⟨73674, by rfl⟩) R147349
theorem R65443 : Reach 65443 := rs (se 1 (by rfl) ⟨49082, by rfl⟩) R98165
theorem R360389 : Reach 360389 := rs (se 4 (by rfl) ⟨33786, by rfl⟩) R67573
theorem R262115 : Reach 262115 := rs (se 1 (by rfl) ⟨196586, by rfl⟩) R393173
theorem R458723 : Reach 458723 := rs (se 1 (by rfl) ⟨344042, by rfl⟩) R688085
theorem R196625 : Reach 196625 := rs (se 2 (by rfl) ⟨73734, by rfl⟩) R147469
theorem R196739 : Reach 196739 := rs (se 1 (by rfl) ⟨147554, by rfl⟩) R295109
theorem R65815 : Reach 65815 := rs (se 1 (by rfl) ⟨49361, by rfl⟩) R98723
theorem R262531 : Reach 262531 := rs (se 1 (by rfl) ⟨196898, by rfl⟩) R393797
theorem R66187 : Reach 66187 := rs (se 1 (by rfl) ⟨49640, by rfl⟩) R99281
theorem R131777 : Reach 131777 := rs (se 2 (by rfl) ⟨49416, by rfl⟩) R98833
theorem R99019 : Reach 99019 := rs (se 1 (by rfl) ⟨74264, by rfl⟩) R148529
theorem R131801 : Reach 131801 := rs (se 2 (by rfl) ⟨49425, by rfl⟩) R98851
theorem R99083 : Reach 99083 := rs (se 1 (by rfl) ⟨74312, by rfl⟩) R148625
theorem R99137 : Reach 99137 := rs (se 2 (by rfl) ⟨37176, by rfl⟩) R74353
theorem R394085 : Reach 394085 := rs (se 4 (by rfl) ⟨36945, by rfl⟩) R73891
theorem R197549 : Reach 197549 := rs (se 3 (by rfl) ⟨37040, by rfl⟩) R74081
theorem R328769 : Reach 328769 := rs (se 2 (by rfl) ⟨123288, by rfl⟩) R246577
theorem R132313 : Reach 132313 := rs (se 2 (by rfl) ⟨49617, by rfl⟩) R99235
theorem R1377809 : Reach 1377809 := rs (se 2 (by rfl) ⟨516678, by rfl⟩) R1033357
theorem R460363 : Reach 460363 := rs (se 1 (by rfl) ⟨345272, by rfl⟩) R690545
theorem R67159 : Reach 67159 := rs (se 1 (by rfl) ⟨50369, by rfl⟩) R100739
theorem R100055 : Reach 100055 := rs (se 1 (by rfl) ⟨75041, by rfl⟩) R150083
theorem R263897 : Reach 263897 := rs (se 2 (by rfl) ⟨98961, by rfl⟩) R197923
theorem R460637 : Reach 460637 := rs (se 3 (by rfl) ⟨86369, by rfl⟩) R172739
theorem R100363 : Reach 100363 := rs (se 1 (by rfl) ⟨75272, by rfl⟩) R150545
theorem R591947 : Reach 591947 := rs (se 1 (by rfl) ⟨443960, by rfl⟩) R887921
theorem R100595 : Reach 100595 := rs (se 1 (by rfl) ⟨75446, by rfl⟩) R150893
theorem R133427 : Reach 133427 := rs (se 1 (by rfl) ⟨100070, by rfl⟩) R200141
theorem R166195 : Reach 166195 := rs (se 1 (by rfl) ⟨124646, by rfl⟩) R249293
theorem R67979 : Reach 67979 := rs (se 1 (by rfl) ⟨50984, by rfl⟩) R101969
theorem R231959 : Reach 231959 := rs (se 1 (by rfl) ⟨173969, by rfl⟩) R347939
theorem R166475 : Reach 166475 := rs (se 1 (by rfl) ⟨124856, by rfl⟩) R249713
theorem R133721 : Reach 133721 := rs (se 2 (by rfl) ⟨50145, by rfl⟩) R100291
theorem R101081 : Reach 101081 := rs (se 2 (by rfl) ⟨37905, by rfl⟩) R75811
theorem R232267 : Reach 232267 := rs (se 1 (by rfl) ⟨174200, by rfl⟩) R348401
theorem R461699 : Reach 461699 := rs (se 1 (by rfl) ⟨346274, by rfl⟩) R692549
theorem R68683 : Reach 68683 := rs (se 1 (by rfl) ⟨51512, by rfl⟩) R103025
theorem R232541 : Reach 232541 := rs (se 3 (by rfl) ⟨43601, by rfl⟩) R87203
theorem R199853 : Reach 199853 := rs (se 3 (by rfl) ⟨37472, by rfl⟩) R74945
theorem R1019141 : Reach 1019141 := rs (se 4 (by rfl) ⟨95544, by rfl⟩) R191089
theorem R265517 : Reach 265517 := rs (se 3 (by rfl) ⟨49784, by rfl⟩) R99569
theorem R68951 : Reach 68951 := rs (se 1 (by rfl) ⟨51713, by rfl⟩) R103427
theorem R397061 : Reach 397061 := rs (se 4 (by rfl) ⟨37224, by rfl⟩) R74449
theorem R200627 : Reach 200627 := rs (se 1 (by rfl) ⟨150470, by rfl⟩) R300941
theorem R692185 : Reach 692185 := rs (se 2 (by rfl) ⟨259569, by rfl⟩) R519139
theorem R69655 : Reach 69655 := rs (se 1 (by rfl) ⟨52241, by rfl⟩) R104483
theorem R102539 : Reach 102539 := rs (se 1 (by rfl) ⟨76904, by rfl⟩) R153809
theorem R168115 : Reach 168115 := rs (se 1 (by rfl) ⟨126086, by rfl⟩) R252173
theorem R135371 : Reach 135371 := rs (se 1 (by rfl) ⟨101528, by rfl⟩) R203057
theorem R102721 : Reach 102721 := rs (se 2 (by rfl) ⟨38520, by rfl⟩) R77041
theorem R168281 : Reach 168281 := rs (se 2 (by rfl) ⟨63105, by rfl⟩) R126211
theorem R233873 : Reach 233873 := rs (se 2 (by rfl) ⟨87702, by rfl⟩) R175405
theorem R332333 : Reach 332333 := rs (se 3 (by rfl) ⟨62312, by rfl⟩) R124625
theorem R103169 : Reach 103169 := rs (se 2 (by rfl) ⟨38688, by rfl⟩) R77377
theorem R332561 : Reach 332561 := rs (se 2 (by rfl) ⟨124710, by rfl⟩) R249421
theorem R103511 : Reach 103511 := rs (se 1 (by rfl) ⟨77633, by rfl⟩) R155267
theorem R169049 : Reach 169049 := rs (se 2 (by rfl) ⟨63393, by rfl⟩) R126787
theorem R136343 : Reach 136343 := rs (se 1 (by rfl) ⟨102257, by rfl⟩) R204515
theorem R791909 : Reach 791909 := rs (se 4 (by rfl) ⟨74241, by rfl⟩) R148483
theorem R202115 : Reach 202115 := rs (se 1 (by rfl) ⟨151586, by rfl⟩) R303173
theorem R169561 : Reach 169561 := rs (se 2 (by rfl) ⟨63585, by rfl⟩) R127171
theorem R104179 : Reach 104179 := rs (se 1 (by rfl) ⟨78134, by rfl⟩) R156269
theorem R137011 : Reach 137011 := rs (se 1 (by rfl) ⟨102758, by rfl⟩) R205517
theorem R202571 : Reach 202571 := rs (se 1 (by rfl) ⟨151928, by rfl⟩) R303857
theorem R137153 : Reach 137153 := rs (se 2 (by rfl) ⟨51432, by rfl⟩) R102865
theorem R202769 : Reach 202769 := rs (se 2 (by rfl) ⟨76038, by rfl⟩) R152077
theorem R5150789 : Reach 5150789 := rs (se 4 (by rfl) ⟨482886, by rfl⟩) R965773
theorem R399491 : Reach 399491 := rs (se 1 (by rfl) ⟨299618, by rfl⟩) R599237
theorem R104627 : Reach 104627 := rs (se 1 (by rfl) ⟨78470, by rfl⟩) R156941
theorem R661709 : Reach 661709 := rs (se 3 (by rfl) ⟨124070, by rfl⟩) R248141
theorem R137693 : Reach 137693 := rs (se 3 (by rfl) ⟨25817, by rfl⟩) R51635
theorem R137821 : Reach 137821 := rs (se 3 (by rfl) ⟨25841, by rfl⟩) R51683
theorem R170689 : Reach 170689 := rs (se 2 (by rfl) ⟨64008, by rfl⟩) R128017
theorem R203543 : Reach 203543 := rs (se 1 (by rfl) ⟨152657, by rfl⟩) R305315
theorem R105239 : Reach 105239 := rs (se 1 (by rfl) ⟨78929, by rfl⟩) R157859
theorem R1252313 : Reach 1252313 := rs (se 2 (by rfl) ⟨469617, by rfl⟩) R939235
theorem R203741 : Reach 203741 := rs (se 3 (by rfl) ⟨38201, by rfl⟩) R76403
theorem R171031 : Reach 171031 := rs (se 1 (by rfl) ⟨128273, by rfl⟩) R256547
theorem R269405 : Reach 269405 := rs (se 3 (by rfl) ⟨50513, by rfl⟩) R101027
theorem R302231 : Reach 302231 := rs (se 1 (by rfl) ⟨226673, by rfl⟩) R453347
theorem R138419 : Reach 138419 := rs (se 1 (by rfl) ⟨103814, by rfl⟩) R207629
theorem R138647 : Reach 138647 := rs (se 1 (by rfl) ⟨103985, by rfl⟩) R207971
theorem R499121 : Reach 499121 := rs (se 2 (by rfl) ⟨187170, by rfl⟩) R374341
theorem R105931 : Reach 105931 := rs (se 1 (by rfl) ⟨79448, by rfl⟩) R158897
theorem R892433 : Reach 892433 := rs (se 2 (by rfl) ⟨334662, by rfl⟩) R669325
theorem R138955 : Reach 138955 := rs (se 1 (by rfl) ⟨104216, by rfl⟩) R208433
theorem R73561 : Reach 73561 := rs (se 2 (by rfl) ⟨27585, by rfl⟩) R55171
theorem R139097 : Reach 139097 := rs (se 2 (by rfl) ⟨52161, by rfl⟩) R104323
theorem R139229 : Reach 139229 := rs (se 3 (by rfl) ⟨26105, by rfl⟩) R52211
theorem R499729 : Reach 499729 := rs (se 2 (by rfl) ⟨187398, by rfl⟩) R374797
theorem R237761 : Reach 237761 := rs (se 2 (by rfl) ⟨89160, by rfl⟩) R178321
theorem R434393 : Reach 434393 := rs (se 2 (by rfl) ⟨162897, by rfl⟩) R325795
theorem R303425 : Reach 303425 := rs (se 2 (by rfl) ⟨113784, by rfl⟩) R227569
theorem R172381 : Reach 172381 := rs (se 3 (by rfl) ⟨32321, by rfl⟩) R64643
theorem R598373 : Reach 598373 := rs (se 4 (by rfl) ⟨56097, by rfl⟩) R112195
theorem R172637 : Reach 172637 := rs (se 3 (by rfl) ⟨32369, by rfl⟩) R64739
theorem R205699 : Reach 205699 := rs (se 1 (by rfl) ⟨154274, by rfl⟩) R308549
theorem R107659 : Reach 107659 := rs (se 1 (by rfl) ⟨80744, by rfl⟩) R161489
theorem R271511 : Reach 271511 := rs (se 1 (by rfl) ⟨203633, by rfl⟩) R407267
theorem R206003 : Reach 206003 := rs (se 1 (by rfl) ⟨154502, by rfl⟩) R309005
theorem R75019 : Reach 75019 := rs (se 1 (by rfl) ⟨56264, by rfl⟩) R112529
theorem R402893 : Reach 402893 := rs (se 3 (by rfl) ⟨75542, by rfl⟩) R151085
theorem R4793813 : Reach 4793813 := rs (se 7 (by rfl) ⟨56177, by rfl⟩) R112355
theorem R75403 : Reach 75403 := rs (se 1 (by rfl) ⟨56552, by rfl⟩) R113105
theorem R435863 : Reach 435863 := rs (se 1 (by rfl) ⟨326897, by rfl⟩) R653795
theorem R173771 : Reach 173771 := rs (se 1 (by rfl) ⟨130328, by rfl⟩) R260657
theorem R239383 : Reach 239383 := rs (se 1 (by rfl) ⟨179537, by rfl⟩) R359075
theorem R206657 : Reach 206657 := rs (se 2 (by rfl) ⟨77496, by rfl⟩) R154993
theorem R403379 : Reach 403379 := rs (se 1 (by rfl) ⟨302534, by rfl⟩) R605069
theorem R174041 : Reach 174041 := rs (se 2 (by rfl) ⟨65265, by rfl⟩) R130531
theorem R338251 : Reach 338251 := rs (se 1 (by rfl) ⟨253688, by rfl⟩) R507377
theorem R76249 : Reach 76249 := rs (se 2 (by rfl) ⟨28593, by rfl⟩) R57187
theorem R240259 : Reach 240259 := rs (se 1 (by rfl) ⟨180194, by rfl⟩) R360389
theorem R174743 : Reach 174743 := rs (se 1 (by rfl) ⟨131057, by rfl⟩) R262115
theorem R305815 : Reach 305815 := rs (se 1 (by rfl) ⟨229361, by rfl⟩) R458723
theorem R436913 : Reach 436913 := rs (se 2 (by rfl) ⟨163842, by rfl⟩) R327685
theorem R76697 : Reach 76697 := rs (se 2 (by rfl) ⟨28761, by rfl⟩) R57523
theorem R109505 : Reach 109505 := rs (se 2 (by rfl) ⟨41064, by rfl⟩) R82129
theorem R76811 : Reach 76811 := rs (se 1 (by rfl) ⟨57608, by rfl⟩) R115217
theorem R76823 : Reach 76823 := rs (se 1 (by rfl) ⟨57617, by rfl⟩) R115235
theorem R207917 : Reach 207917 := rs (se 3 (by rfl) ⟨38984, by rfl⟩) R77969
theorem R207947 : Reach 207947 := rs (se 1 (by rfl) ⟨155960, by rfl⟩) R311921
theorem R76889 : Reach 76889 := rs (se 2 (by rfl) ⟨28833, by rfl⟩) R57667
theorem R175283 : Reach 175283 := rs (se 1 (by rfl) ⟨131462, by rfl⟩) R262925
theorem R77003 : Reach 77003 := rs (se 1 (by rfl) ⟨57752, by rfl⟩) R115505
theorem R77015 : Reach 77015 := rs (se 1 (by rfl) ⟨57761, by rfl⟩) R115523
theorem R77081 : Reach 77081 := rs (se 2 (by rfl) ⟨28905, by rfl⟩) R57811
theorem R404837 : Reach 404837 := rs (se 4 (by rfl) ⟨37953, by rfl⟩) R75907
theorem R77195 : Reach 77195 := rs (se 1 (by rfl) ⟨57896, by rfl⟩) R115793
theorem R77207 : Reach 77207 := rs (se 1 (by rfl) ⟨57905, by rfl⟩) R115811
theorem R175553 : Reach 175553 := rs (se 2 (by rfl) ⟨65832, by rfl⟩) R131665
theorem R77273 : Reach 77273 := rs (se 2 (by rfl) ⟨28977, by rfl⟩) R57955
theorem R77387 : Reach 77387 := rs (se 1 (by rfl) ⟨58040, by rfl⟩) R116081
theorem R77399 : Reach 77399 := rs (se 1 (by rfl) ⟨58049, by rfl⟩) R116099
theorem R110231 : Reach 110231 := rs (se 1 (by rfl) ⟨82673, by rfl⟩) R165347
theorem R77465 : Reach 77465 := rs (se 2 (by rfl) ⟨29049, by rfl⟩) R58099
theorem R208601 : Reach 208601 := rs (se 2 (by rfl) ⟨78225, by rfl⟩) R156451
theorem R77579 : Reach 77579 := rs (se 1 (by rfl) ⟨58184, by rfl⟩) R116369
theorem R77591 : Reach 77591 := rs (se 1 (by rfl) ⟨58193, by rfl⟩) R116387
theorem R77593 : Reach 77593 := rs (se 2 (by rfl) ⟨29097, by rfl⟩) R58195
theorem R405323 : Reach 405323 := rs (se 1 (by rfl) ⟨303992, by rfl⟩) R607985
theorem R77657 : Reach 77657 := rs (se 2 (by rfl) ⟨29121, by rfl⟩) R58243
theorem R77707 : Reach 77707 := rs (se 1 (by rfl) ⟨58280, by rfl⟩) R116561
theorem R77771 : Reach 77771 := rs (se 1 (by rfl) ⟨58328, by rfl⟩) R116657
theorem R77783 : Reach 77783 := rs (se 1 (by rfl) ⟨58337, by rfl⟩) R116675
theorem R1814489 : Reach 1814489 := rs (se 2 (by rfl) ⟨680433, by rfl⟩) R1360867
theorem R176093 : Reach 176093 := rs (se 3 (by rfl) ⟨33017, by rfl⟩) R66035
theorem R208919 : Reach 208919 := rs (se 1 (by rfl) ⟨156689, by rfl⟩) R313379
theorem R77849 : Reach 77849 := rs (se 2 (by rfl) ⟨29193, by rfl⟩) R58387
theorem R77963 : Reach 77963 := rs (se 1 (by rfl) ⟨58472, by rfl⟩) R116945
theorem R77975 : Reach 77975 := rs (se 1 (by rfl) ⟨58481, by rfl⟩) R116963
theorem R78041 : Reach 78041 := rs (se 2 (by rfl) ⟨29265, by rfl⟩) R58531
theorem R78155 : Reach 78155 := rs (se 1 (by rfl) ⟨58616, by rfl⟩) R117233
theorem R78167 : Reach 78167 := rs (se 1 (by rfl) ⟨58625, by rfl⟩) R117251
theorem R78233 : Reach 78233 := rs (se 2 (by rfl) ⟨29337, by rfl⟩) R58675
theorem R78347 : Reach 78347 := rs (se 1 (by rfl) ⟨58760, by rfl⟩) R117521
theorem R111127 : Reach 111127 := rs (se 1 (by rfl) ⟨83345, by rfl⟩) R166691
theorem R78359 : Reach 78359 := rs (se 1 (by rfl) ⟨58769, by rfl⟩) R117539
theorem R78425 : Reach 78425 := rs (se 2 (by rfl) ⟨29409, by rfl⟩) R58819
theorem R275075 : Reach 275075 := rs (se 1 (by rfl) ⟨206306, by rfl⟩) R412613
theorem R78539 : Reach 78539 := rs (se 1 (by rfl) ⟨58904, by rfl⟩) R117809
theorem R78551 : Reach 78551 := rs (se 1 (by rfl) ⟨58913, by rfl⟩) R117827
theorem R78617 : Reach 78617 := rs (se 2 (by rfl) ⟨29481, by rfl⟩) R58963
theorem R78731 : Reach 78731 := rs (se 1 (by rfl) ⟨59048, by rfl⟩) R118097
theorem R78743 : Reach 78743 := rs (se 1 (by rfl) ⟨59057, by rfl⟩) R118115
theorem R635825 : Reach 635825 := rs (se 2 (by rfl) ⟨238434, by rfl⟩) R476869
theorem R78809 : Reach 78809 := rs (se 2 (by rfl) ⟨29553, by rfl⟩) R59107
theorem R177227 : Reach 177227 := rs (se 1 (by rfl) ⟨132920, by rfl⟩) R265841
theorem R78923 : Reach 78923 := rs (se 1 (by rfl) ⟨59192, by rfl⟩) R118385
theorem R78935 : Reach 78935 := rs (se 1 (by rfl) ⟨59201, by rfl⟩) R118403
theorem R79001 : Reach 79001 := rs (se 2 (by rfl) ⟨29625, by rfl⟩) R59251
theorem R79115 : Reach 79115 := rs (se 1 (by rfl) ⟨59336, by rfl⟩) R118673
theorem R79127 : Reach 79127 := rs (se 1 (by rfl) ⟨59345, by rfl⟩) R118691
theorem R111947 : Reach 111947 := rs (se 1 (by rfl) ⟨83960, by rfl⟩) R167921
theorem R177497 : Reach 177497 := rs (se 2 (by rfl) ⟨66561, by rfl⟩) R133123
theorem R79193 : Reach 79193 := rs (se 2 (by rfl) ⟨29697, by rfl⟩) R59395
theorem R79307 : Reach 79307 := rs (se 1 (by rfl) ⟨59480, by rfl⟩) R118961
theorem R79319 : Reach 79319 := rs (se 1 (by rfl) ⟨59489, by rfl⟩) R118979
theorem R79385 : Reach 79385 := rs (se 2 (by rfl) ⟨29769, by rfl⟩) R59539
theorem R505379 : Reach 505379 := rs (se 1 (by rfl) ⟨379034, by rfl⟩) R758069
theorem R79499 : Reach 79499 := rs (se 1 (by rfl) ⟨59624, by rfl⟩) R119249
theorem R79511 : Reach 79511 := rs (se 1 (by rfl) ⟨59633, by rfl⟩) R119267
theorem R79577 : Reach 79577 := rs (se 2 (by rfl) ⟨29841, by rfl⟩) R59683
theorem R79691 : Reach 79691 := rs (se 1 (by rfl) ⟨59768, by rfl⟩) R119537
theorem R79703 : Reach 79703 := rs (se 1 (by rfl) ⟨59777, by rfl⟩) R119555
theorem R767843 : Reach 767843 := rs (se 1 (by rfl) ⟨575882, by rfl⟩) R1151765
theorem R341891 : Reach 341891 := rs (se 1 (by rfl) ⟨256418, by rfl⟩) R512837
theorem R79769 : Reach 79769 := rs (se 2 (by rfl) ⟨29913, by rfl⟩) R59827
theorem R79883 : Reach 79883 := rs (se 1 (by rfl) ⟨59912, by rfl⟩) R119825
theorem R178199 : Reach 178199 := rs (se 1 (by rfl) ⟨133649, by rfl⟩) R267299
theorem R79895 : Reach 79895 := rs (se 1 (by rfl) ⟨59921, by rfl⟩) R119843
theorem R112691 : Reach 112691 := rs (se 1 (by rfl) ⟨84518, by rfl⟩) R169037
theorem R79961 : Reach 79961 := rs (se 2 (by rfl) ⟨29985, by rfl⟩) R59971
theorem R211033 : Reach 211033 := rs (se 2 (by rfl) ⟨79137, by rfl⟩) R158275
theorem R80075 : Reach 80075 := rs (se 1 (by rfl) ⟨60056, by rfl⟩) R120113
theorem R80087 : Reach 80087 := rs (se 1 (by rfl) ⟨60065, by rfl⟩) R120131
theorem R112921 : Reach 112921 := rs (se 2 (by rfl) ⟨42345, by rfl⟩) R84691
theorem R80153 : Reach 80153 := rs (se 2 (by rfl) ⟨30057, by rfl⟩) R60115
theorem R80267 : Reach 80267 := rs (se 1 (by rfl) ⟨60200, by rfl⟩) R120401
theorem R80279 : Reach 80279 := rs (se 1 (by rfl) ⟨60209, by rfl⟩) R120419
theorem R80345 : Reach 80345 := rs (se 2 (by rfl) ⟨30129, by rfl⟩) R60259
theorem R178739 : Reach 178739 := rs (se 1 (by rfl) ⟨134054, by rfl⟩) R268109
theorem R80459 : Reach 80459 := rs (se 1 (by rfl) ⟨60344, by rfl⟩) R120689
theorem R80471 : Reach 80471 := rs (se 1 (by rfl) ⟨60353, by rfl⟩) R120707
theorem R80537 : Reach 80537 := rs (se 2 (by rfl) ⟨30201, by rfl⟩) R60403
theorem R80651 : Reach 80651 := rs (se 1 (by rfl) ⟨60488, by rfl⟩) R120977
theorem R80663 : Reach 80663 := rs (se 1 (by rfl) ⟨60497, by rfl⟩) R120995
theorem R179009 : Reach 179009 := rs (se 2 (by rfl) ⟨67128, by rfl⟩) R134257
theorem R80729 : Reach 80729 := rs (se 2 (by rfl) ⟨30273, by rfl⟩) R60547
theorem R113537 : Reach 113537 := rs (se 2 (by rfl) ⟨42576, by rfl⟩) R85153
theorem R80843 : Reach 80843 := rs (se 1 (by rfl) ⟨60632, by rfl⟩) R121265
theorem R80855 : Reach 80855 := rs (se 1 (by rfl) ⟨60641, by rfl⟩) R121283
theorem R146393 : Reach 146393 := rs (se 2 (by rfl) ⟨54897, by rfl⟩) R109795
theorem R80921 : Reach 80921 := rs (se 2 (by rfl) ⟨30345, by rfl⟩) R60691
theorem R81035 : Reach 81035 := rs (se 1 (by rfl) ⟨60776, by rfl⟩) R121553
theorem R81047 : Reach 81047 := rs (se 1 (by rfl) ⟨60785, by rfl⟩) R121571
theorem R113879 : Reach 113879 := rs (se 1 (by rfl) ⟨85409, by rfl⟩) R170819
theorem R81113 : Reach 81113 := rs (se 2 (by rfl) ⟨30417, by rfl⟩) R60835
theorem R146711 : Reach 146711 := rs (se 1 (by rfl) ⟨110033, by rfl⟩) R220067
theorem R474443 : Reach 474443 := rs (se 1 (by rfl) ⟨355832, by rfl⟩) R711665
theorem R81227 : Reach 81227 := rs (se 1 (by rfl) ⟨60920, by rfl⟩) R121841
theorem R81239 : Reach 81239 := rs (se 1 (by rfl) ⟨60929, by rfl⟩) R121859
theorem R146777 : Reach 146777 := rs (se 2 (by rfl) ⟨55041, by rfl⟩) R110083
theorem R179549 : Reach 179549 := rs (se 3 (by rfl) ⟨33665, by rfl⟩) R67331
theorem R81305 : Reach 81305 := rs (se 2 (by rfl) ⟨30489, by rfl⟩) R60979
theorem R376325 : Reach 376325 := rs (se 4 (by rfl) ⟨35280, by rfl⟩) R70561
theorem R81419 : Reach 81419 := rs (se 1 (by rfl) ⟨61064, by rfl⟩) R122129
theorem R81431 : Reach 81431 := rs (se 1 (by rfl) ⟨61073, by rfl⟩) R122147
theorem R81497 : Reach 81497 := rs (se 2 (by rfl) ⟨30561, by rfl⟩) R61123
theorem R81611 : Reach 81611 := rs (se 1 (by rfl) ⟨61208, by rfl⟩) R122417
theorem R81623 : Reach 81623 := rs (se 1 (by rfl) ⟨61217, by rfl⟩) R122435
theorem R81689 : Reach 81689 := rs (se 2 (by rfl) ⟨30633, by rfl⟩) R61267
theorem R81803 : Reach 81803 := rs (se 1 (by rfl) ⟨61352, by rfl⟩) R122705
theorem R81815 : Reach 81815 := rs (se 1 (by rfl) ⟨61361, by rfl⟩) R122723
theorem R901043 : Reach 901043 := rs (se 1 (by rfl) ⟨675782, by rfl⟩) R1351565
theorem R81881 : Reach 81881 := rs (se 2 (by rfl) ⟨30705, by rfl⟩) R61411
theorem R147521 : Reach 147521 := rs (se 2 (by rfl) ⟨55320, by rfl⟩) R110641
theorem R81995 : Reach 81995 := rs (se 1 (by rfl) ⟨61496, by rfl⟩) R122993
theorem R82007 : Reach 82007 := rs (se 1 (by rfl) ⟨61505, by rfl⟩) R123011
theorem R82073 : Reach 82073 := rs (se 2 (by rfl) ⟨30777, by rfl⟩) R61555
theorem R82187 : Reach 82187 := rs (se 1 (by rfl) ⟨61640, by rfl⟩) R123281
theorem R278801 : Reach 278801 := rs (se 2 (by rfl) ⟨104550, by rfl⟩) R209101
theorem R82199 : Reach 82199 := rs (se 1 (by rfl) ⟨61649, by rfl⟩) R123299
theorem R82265 : Reach 82265 := rs (se 2 (by rfl) ⟨30849, by rfl⟩) R61699
theorem R115073 : Reach 115073 := rs (se 2 (by rfl) ⟨43152, by rfl⟩) R86305
theorem R278963 : Reach 278963 := rs (se 1 (by rfl) ⟨209222, by rfl⟩) R418445
theorem R180683 : Reach 180683 := rs (se 1 (by rfl) ⟨135512, by rfl⟩) R271025
theorem R82379 : Reach 82379 := rs (se 1 (by rfl) ⟨61784, by rfl⟩) R123569
theorem R82391 : Reach 82391 := rs (se 1 (by rfl) ⟨61793, by rfl⟩) R123587
theorem R82457 : Reach 82457 := rs (se 2 (by rfl) ⟨30921, by rfl⟩) R61843
theorem R246347 : Reach 246347 := rs (se 1 (by rfl) ⟨184760, by rfl⟩) R369521
theorem R115289 : Reach 115289 := rs (se 2 (by rfl) ⟨43233, by rfl⟩) R86467
theorem R1065565 : Reach 1065565 := rs (se 3 (by rfl) ⟨199793, by rfl⟩) R399587
theorem R82571 : Reach 82571 := rs (se 1 (by rfl) ⟨61928, by rfl⟩) R123857
theorem R82583 : Reach 82583 := rs (se 1 (by rfl) ⟨61937, by rfl⟩) R123875
theorem R115379 : Reach 115379 := rs (se 1 (by rfl) ⟨86534, by rfl⟩) R173069
theorem R115415 : Reach 115415 := rs (se 1 (by rfl) ⟨86561, by rfl⟩) R173123
theorem R180953 : Reach 180953 := rs (se 2 (by rfl) ⟨67857, by rfl⟩) R135715
theorem R82649 : Reach 82649 := rs (se 2 (by rfl) ⟨30993, by rfl⟩) R61987
theorem R443141 : Reach 443141 := rs (se 4 (by rfl) ⟨41544, by rfl⟩) R83089
theorem R82763 : Reach 82763 := rs (se 1 (by rfl) ⟨62072, by rfl⟩) R124145
theorem R279389 : Reach 279389 := rs (se 3 (by rfl) ⟨52385, by rfl⟩) R104771
theorem R115595 : Reach 115595 := rs (se 1 (by rfl) ⟨86696, by rfl⟩) R173393
theorem R115649 : Reach 115649 := rs (se 2 (by rfl) ⟨43368, by rfl⟩) R86737
theorem R214019 : Reach 214019 := rs (se 1 (by rfl) ⟨160514, by rfl⟩) R321029
theorem R410669 : Reach 410669 := rs (se 3 (by rfl) ⟨77000, by rfl⟩) R154001
theorem R115763 : Reach 115763 := rs (se 1 (by rfl) ⟨86822, by rfl⟩) R173645
theorem R115865 : Reach 115865 := rs (se 2 (by rfl) ⟨43449, by rfl⟩) R86899
theorem R115955 : Reach 115955 := rs (se 1 (by rfl) ⟨86966, by rfl⟩) R173933
theorem R115991 : Reach 115991 := rs (se 1 (by rfl) ⟨86993, by rfl⟩) R173987
theorem R181655 : Reach 181655 := rs (se 1 (by rfl) ⟨136241, by rfl⟩) R272483
theorem R443825 : Reach 443825 := rs (se 2 (by rfl) ⟨166434, by rfl⟩) R332869
theorem R116171 : Reach 116171 := rs (se 1 (by rfl) ⟨87128, by rfl⟩) R174257
theorem R116225 : Reach 116225 := rs (se 2 (by rfl) ⟨43584, by rfl⟩) R87169
theorem R181763 : Reach 181763 := rs (se 1 (by rfl) ⟨136322, by rfl⟩) R272645
theorem R771677 : Reach 771677 := rs (se 3 (by rfl) ⟨144689, by rfl⟩) R289379
theorem R149195 : Reach 149195 := rs (se 1 (by rfl) ⟨111896, by rfl⟩) R223793
theorem R116441 : Reach 116441 := rs (se 2 (by rfl) ⟨43665, by rfl⟩) R87331
theorem R182033 : Reach 182033 := rs (se 2 (by rfl) ⟨68262, by rfl⟩) R136525
theorem R313105 : Reach 313105 := rs (se 2 (by rfl) ⟨117414, by rfl⟩) R234829
theorem R116531 : Reach 116531 := rs (se 1 (by rfl) ⟨87398, by rfl⟩) R174797
theorem R116567 : Reach 116567 := rs (se 1 (by rfl) ⟨87425, by rfl⟩) R174851
theorem R83801 : Reach 83801 := rs (se 2 (by rfl) ⟨31425, by rfl⟩) R62851
theorem R182195 : Reach 182195 := rs (se 1 (by rfl) ⟨136646, by rfl⟩) R273293
theorem R51127 : Reach 51127 := rs (se 1 (by rfl) ⟨38345, by rfl⟩) R76691
theorem R51147 : Reach 51147 := rs (se 1 (by rfl) ⟨38360, by rfl⟩) R76721
theorem R51159 : Reach 51159 := rs (se 1 (by rfl) ⟨38369, by rfl⟩) R76739
theorem R247769 : Reach 247769 := rs (se 2 (by rfl) ⟨92913, by rfl⟩) R185827
theorem R51179 : Reach 51179 := rs (se 1 (by rfl) ⟨38384, by rfl⟩) R76769
theorem R51191 : Reach 51191 := rs (se 1 (by rfl) ⟨38393, by rfl⟩) R76787
theorem R51211 : Reach 51211 := rs (se 1 (by rfl) ⟨38408, by rfl⟩) R76817
theorem R116747 : Reach 116747 := rs (se 1 (by rfl) ⟨87560, by rfl⟩) R175121
theorem R51223 : Reach 51223 := rs (se 1 (by rfl) ⟨38417, by rfl⟩) R76835
theorem R51243 : Reach 51243 := rs (se 1 (by rfl) ⟨38432, by rfl⟩) R76865
theorem R51255 : Reach 51255 := rs (se 1 (by rfl) ⟨38441, by rfl⟩) R76883
theorem R116801 : Reach 116801 := rs (se 2 (by rfl) ⟨43800, by rfl⟩) R87601
theorem R968773 : Reach 968773 := rs (se 4 (by rfl) ⟨90822, by rfl⟩) R181645
theorem R51275 : Reach 51275 := rs (se 1 (by rfl) ⟨38456, by rfl⟩) R76913
theorem R51287 : Reach 51287 := rs (se 1 (by rfl) ⟨38465, by rfl⟩) R76931
theorem R51307 : Reach 51307 := rs (se 1 (by rfl) ⟨38480, by rfl⟩) R76961
theorem R51319 : Reach 51319 := rs (se 1 (by rfl) ⟨38489, by rfl⟩) R76979
theorem R51339 : Reach 51339 := rs (se 1 (by rfl) ⟨38504, by rfl⟩) R77009
theorem R51351 : Reach 51351 := rs (se 1 (by rfl) ⟨38513, by rfl⟩) R77027
theorem R51371 : Reach 51371 := rs (se 1 (by rfl) ⟨38528, by rfl⟩) R77057
theorem R51383 : Reach 51383 := rs (se 1 (by rfl) ⟨38537, by rfl⟩) R77075
theorem R182465 : Reach 182465 := rs (se 2 (by rfl) ⟨68424, by rfl⟩) R136849
theorem R51403 : Reach 51403 := rs (se 1 (by rfl) ⟨38552, by rfl⟩) R77105
theorem R706765 : Reach 706765 := rs (se 3 (by rfl) ⟨132518, by rfl⟩) R265037
theorem R51415 : Reach 51415 := rs (se 1 (by rfl) ⟨38561, by rfl⟩) R77123
theorem R51435 : Reach 51435 := rs (se 1 (by rfl) ⟨38576, by rfl⟩) R77153
theorem R51447 : Reach 51447 := rs (se 1 (by rfl) ⟨38585, by rfl⟩) R77171
theorem R51467 : Reach 51467 := rs (se 1 (by rfl) ⟨38600, by rfl⟩) R77201
theorem R51479 : Reach 51479 := rs (se 1 (by rfl) ⟨38609, by rfl⟩) R77219
theorem R117017 : Reach 117017 := rs (se 2 (by rfl) ⟨43881, by rfl⟩) R87763
theorem R51499 : Reach 51499 := rs (se 1 (by rfl) ⟨38624, by rfl⟩) R77249
theorem R182573 : Reach 182573 := rs (se 3 (by rfl) ⟨34232, by rfl⟩) R68465
theorem R51511 : Reach 51511 := rs (se 1 (by rfl) ⟨38633, by rfl⟩) R77267
theorem R51531 : Reach 51531 := rs (se 1 (by rfl) ⟨38648, by rfl⟩) R77297
theorem R51543 : Reach 51543 := rs (se 1 (by rfl) ⟨38657, by rfl⟩) R77315
theorem R51563 : Reach 51563 := rs (se 1 (by rfl) ⟨38672, by rfl⟩) R77345
theorem R117107 : Reach 117107 := rs (se 1 (by rfl) ⟨87830, by rfl⟩) R175661
theorem R51575 : Reach 51575 := rs (se 1 (by rfl) ⟨38681, by rfl⟩) R77363
theorem R51595 : Reach 51595 := rs (se 1 (by rfl) ⟨38696, by rfl⟩) R77393
theorem R51607 : Reach 51607 := rs (se 1 (by rfl) ⟨38705, by rfl⟩) R77411
theorem R117143 : Reach 117143 := rs (se 1 (by rfl) ⟨87857, by rfl⟩) R175715
theorem R51627 : Reach 51627 := rs (se 1 (by rfl) ⟨38720, by rfl⟩) R77441
theorem R444851 : Reach 444851 := rs (se 1 (by rfl) ⟨333638, by rfl⟩) R667277
theorem R51639 : Reach 51639 := rs (se 1 (by rfl) ⟨38729, by rfl⟩) R77459
theorem R51659 : Reach 51659 := rs (se 1 (by rfl) ⟨38744, by rfl⟩) R77489
theorem R51671 : Reach 51671 := rs (se 1 (by rfl) ⟨38753, by rfl⟩) R77507
theorem R51691 : Reach 51691 := rs (se 1 (by rfl) ⟨38768, by rfl⟩) R77537
theorem R51703 : Reach 51703 := rs (se 1 (by rfl) ⟨38777, by rfl⟩) R77555
theorem R51723 : Reach 51723 := rs (se 1 (by rfl) ⟨38792, by rfl⟩) R77585
theorem R51735 : Reach 51735 := rs (se 1 (by rfl) ⟨38801, by rfl⟩) R77603
theorem R51755 : Reach 51755 := rs (se 1 (by rfl) ⟨38816, by rfl⟩) R77633
theorem R51767 : Reach 51767 := rs (se 1 (by rfl) ⟨38825, by rfl⟩) R77651
theorem R51787 : Reach 51787 := rs (se 1 (by rfl) ⟨38840, by rfl⟩) R77681
theorem R117323 : Reach 117323 := rs (se 1 (by rfl) ⟨87992, by rfl⟩) R175985
theorem R51799 : Reach 51799 := rs (se 1 (by rfl) ⟨38849, by rfl⟩) R77699
theorem R51819 : Reach 51819 := rs (se 1 (by rfl) ⟨38864, by rfl⟩) R77729
theorem R51831 : Reach 51831 := rs (se 1 (by rfl) ⟨38873, by rfl⟩) R77747
theorem R117377 : Reach 117377 := rs (se 2 (by rfl) ⟨44016, by rfl⟩) R88033
theorem R51851 : Reach 51851 := rs (se 1 (by rfl) ⟨38888, by rfl⟩) R77777
theorem R51863 : Reach 51863 := rs (se 1 (by rfl) ⟨38897, by rfl⟩) R77795
theorem R51883 : Reach 51883 := rs (se 1 (by rfl) ⟨38912, by rfl⟩) R77825
theorem R51895 : Reach 51895 := rs (se 1 (by rfl) ⟨38921, by rfl⟩) R77843
theorem R51915 : Reach 51915 := rs (se 1 (by rfl) ⟨38936, by rfl⟩) R77873
theorem R182987 : Reach 182987 := rs (se 1 (by rfl) ⟨137240, by rfl⟩) R274481
theorem R51927 : Reach 51927 := rs (se 1 (by rfl) ⟨38945, by rfl⟩) R77891
theorem R183005 : Reach 183005 := rs (se 3 (by rfl) ⟨34313, by rfl⟩) R68627
theorem R51947 : Reach 51947 := rs (se 1 (by rfl) ⟨38960, by rfl⟩) R77921
theorem R51959 : Reach 51959 := rs (se 1 (by rfl) ⟨38969, by rfl⟩) R77939
theorem R51979 : Reach 51979 := rs (se 1 (by rfl) ⟨38984, by rfl⟩) R77969
theorem R51991 : Reach 51991 := rs (se 1 (by rfl) ⟨38993, by rfl⟩) R77987
theorem R52011 : Reach 52011 := rs (se 1 (by rfl) ⟨39008, by rfl⟩) R78017
theorem R52023 : Reach 52023 := rs (se 1 (by rfl) ⟨39017, by rfl⟩) R78035
theorem R52043 : Reach 52043 := rs (se 1 (by rfl) ⟨39032, by rfl⟩) R78065
theorem R52055 : Reach 52055 := rs (se 1 (by rfl) ⟨39041, by rfl⟩) R78083
theorem R117593 : Reach 117593 := rs (se 2 (by rfl) ⟨44097, by rfl⟩) R88195
theorem R52075 : Reach 52075 := rs (se 1 (by rfl) ⟨39056, by rfl⟩) R78113
theorem R52087 : Reach 52087 := rs (se 1 (by rfl) ⟨39065, by rfl⟩) R78131
theorem R52107 : Reach 52107 := rs (se 1 (by rfl) ⟨39080, by rfl⟩) R78161
theorem R52119 : Reach 52119 := rs (se 1 (by rfl) ⟨39089, by rfl⟩) R78179
theorem R52139 : Reach 52139 := rs (se 1 (by rfl) ⟨39104, by rfl⟩) R78209
theorem R117683 : Reach 117683 := rs (se 1 (by rfl) ⟨88262, by rfl⟩) R176525
theorem R52151 : Reach 52151 := rs (se 1 (by rfl) ⟨39113, by rfl⟩) R78227
theorem R52171 : Reach 52171 := rs (se 1 (by rfl) ⟨39128, by rfl⟩) R78257
theorem R52183 : Reach 52183 := rs (se 1 (by rfl) ⟨39137, by rfl⟩) R78275
theorem R117719 : Reach 117719 := rs (se 1 (by rfl) ⟨88289, by rfl⟩) R176579
theorem R150493 : Reach 150493 := rs (se 3 (by rfl) ⟨28217, by rfl⟩) R56435
theorem R52203 : Reach 52203 := rs (se 1 (by rfl) ⟨39152, by rfl⟩) R78305
theorem R52215 : Reach 52215 := rs (se 1 (by rfl) ⟨39161, by rfl⟩) R78323
theorem R52235 : Reach 52235 := rs (se 1 (by rfl) ⟨39176, by rfl⟩) R78353
theorem R52247 : Reach 52247 := rs (se 1 (by rfl) ⟨39185, by rfl⟩) R78371
theorem R52267 : Reach 52267 := rs (se 1 (by rfl) ⟨39200, by rfl⟩) R78401
theorem R52279 : Reach 52279 := rs (se 1 (by rfl) ⟨39209, by rfl⟩) R78419
theorem R52299 : Reach 52299 := rs (se 1 (by rfl) ⟨39224, by rfl⟩) R78449
theorem R52311 : Reach 52311 := rs (se 1 (by rfl) ⟨39233, by rfl⟩) R78467
theorem R52331 : Reach 52331 := rs (se 1 (by rfl) ⟨39248, by rfl⟩) R78497
theorem R52343 : Reach 52343 := rs (se 1 (by rfl) ⟨39257, by rfl⟩) R78515
theorem R52363 : Reach 52363 := rs (se 1 (by rfl) ⟨39272, by rfl⟩) R78545
theorem R117899 : Reach 117899 := rs (se 1 (by rfl) ⟨88424, by rfl⟩) R176849
theorem R52375 : Reach 52375 := rs (se 1 (by rfl) ⟨39281, by rfl⟩) R78563
theorem R52395 : Reach 52395 := rs (se 1 (by rfl) ⟨39296, by rfl⟩) R78593
theorem R52407 : Reach 52407 := rs (se 1 (by rfl) ⟨39305, by rfl⟩) R78611
theorem R117953 : Reach 117953 := rs (se 2 (by rfl) ⟨44232, by rfl⟩) R88465
theorem R52427 : Reach 52427 := rs (se 1 (by rfl) ⟨39320, by rfl⟩) R78641
theorem R52439 : Reach 52439 := rs (se 1 (by rfl) ⟨39329, by rfl⟩) R78659
theorem R52459 : Reach 52459 := rs (se 1 (by rfl) ⟨39344, by rfl⟩) R78689
theorem R52471 : Reach 52471 := rs (se 1 (by rfl) ⟨39353, by rfl⟩) R78707
theorem R52491 : Reach 52491 := rs (se 1 (by rfl) ⟨39368, by rfl⟩) R78737
theorem R52503 : Reach 52503 := rs (se 1 (by rfl) ⟨39377, by rfl⟩) R78755
theorem R52523 : Reach 52523 := rs (se 1 (by rfl) ⟨39392, by rfl⟩) R78785
theorem R150835 : Reach 150835 := rs (se 1 (by rfl) ⟨113126, by rfl⟩) R226253
theorem R52535 : Reach 52535 := rs (se 1 (by rfl) ⟨39401, by rfl⟩) R78803
theorem R52555 : Reach 52555 := rs (se 1 (by rfl) ⟨39416, by rfl⟩) R78833
theorem R52567 : Reach 52567 := rs (se 1 (by rfl) ⟨39425, by rfl⟩) R78851
theorem R52587 : Reach 52587 := rs (se 1 (by rfl) ⟨39440, by rfl⟩) R78881
theorem R52599 : Reach 52599 := rs (se 1 (by rfl) ⟨39449, by rfl⟩) R78899
theorem R52619 : Reach 52619 := rs (se 1 (by rfl) ⟨39464, by rfl⟩) R78929
theorem R52631 : Reach 52631 := rs (se 1 (by rfl) ⟨39473, by rfl⟩) R78947
theorem R118169 : Reach 118169 := rs (se 2 (by rfl) ⟨44313, by rfl⟩) R88627
theorem R52651 : Reach 52651 := rs (se 1 (by rfl) ⟨39488, by rfl⟩) R78977
theorem R52663 : Reach 52663 := rs (se 1 (by rfl) ⟨39497, by rfl⟩) R78995
theorem R52683 : Reach 52683 := rs (se 1 (by rfl) ⟨39512, by rfl⟩) R79025
theorem R52695 : Reach 52695 := rs (se 1 (by rfl) ⟨39521, by rfl⟩) R79043
theorem R52715 : Reach 52715 := rs (se 1 (by rfl) ⟨39536, by rfl⟩) R79073
theorem R118259 : Reach 118259 := rs (se 1 (by rfl) ⟨88694, by rfl⟩) R177389
theorem R52727 : Reach 52727 := rs (se 1 (by rfl) ⟨39545, by rfl⟩) R79091
theorem R52747 : Reach 52747 := rs (se 1 (by rfl) ⟨39560, by rfl⟩) R79121
theorem R118295 : Reach 118295 := rs (se 1 (by rfl) ⟨88721, by rfl⟩) R177443
theorem R52759 : Reach 52759 := rs (se 1 (by rfl) ⟨39569, by rfl⟩) R79139
theorem R52779 : Reach 52779 := rs (se 1 (by rfl) ⟨39584, by rfl⟩) R79169
theorem R52791 : Reach 52791 := rs (se 1 (by rfl) ⟨39593, by rfl⟩) R79187
theorem R52811 : Reach 52811 := rs (se 1 (by rfl) ⟨39608, by rfl⟩) R79217
theorem R52823 : Reach 52823 := rs (se 1 (by rfl) ⟨39617, by rfl⟩) R79235
theorem R52843 : Reach 52843 := rs (se 1 (by rfl) ⟨39632, by rfl⟩) R79265
theorem R52855 : Reach 52855 := rs (se 1 (by rfl) ⟨39641, by rfl⟩) R79283
theorem R52875 : Reach 52875 := rs (se 1 (by rfl) ⟨39656, by rfl⟩) R79313
theorem R52887 : Reach 52887 := rs (se 1 (by rfl) ⟨39665, by rfl⟩) R79331
theorem R52907 : Reach 52907 := rs (se 1 (by rfl) ⟨39680, by rfl⟩) R79361
theorem R52919 : Reach 52919 := rs (se 1 (by rfl) ⟨39689, by rfl⟩) R79379
theorem R118475 : Reach 118475 := rs (se 1 (by rfl) ⟨88856, by rfl⟩) R177713
theorem R52939 : Reach 52939 := rs (se 1 (by rfl) ⟨39704, by rfl⟩) R79409
theorem R52951 : Reach 52951 := rs (se 1 (by rfl) ⟨39713, by rfl⟩) R79427
theorem R52971 : Reach 52971 := rs (se 1 (by rfl) ⟨39728, by rfl⟩) R79457
theorem R52983 : Reach 52983 := rs (se 1 (by rfl) ⟨39737, by rfl⟩) R79475
theorem R118529 : Reach 118529 := rs (se 2 (by rfl) ⟨44448, by rfl⟩) R88897
theorem R53003 : Reach 53003 := rs (se 1 (by rfl) ⟨39752, by rfl⟩) R79505
theorem R53015 : Reach 53015 := rs (se 1 (by rfl) ⟨39761, by rfl⟩) R79523
theorem R53035 : Reach 53035 := rs (se 1 (by rfl) ⟨39776, by rfl⟩) R79553
theorem R53047 : Reach 53047 := rs (se 1 (by rfl) ⟨39785, by rfl⟩) R79571
theorem R53067 : Reach 53067 := rs (se 1 (by rfl) ⟨39800, by rfl⟩) R79601
theorem R184139 : Reach 184139 := rs (se 1 (by rfl) ⟨138104, by rfl⟩) R276209
theorem R53079 : Reach 53079 := rs (se 1 (by rfl) ⟨39809, by rfl⟩) R79619
theorem R53099 : Reach 53099 := rs (se 1 (by rfl) ⟨39824, by rfl⟩) R79649
theorem R53111 : Reach 53111 := rs (se 1 (by rfl) ⟨39833, by rfl⟩) R79667
theorem R53131 : Reach 53131 := rs (se 1 (by rfl) ⟨39848, by rfl⟩) R79697
theorem R53143 : Reach 53143 := rs (se 1 (by rfl) ⟨39857, by rfl⟩) R79715
theorem R53163 : Reach 53163 := rs (se 1 (by rfl) ⟨39872, by rfl⟩) R79745
theorem R577459 : Reach 577459 := rs (se 1 (by rfl) ⟨433094, by rfl⟩) R866189
theorem R53175 : Reach 53175 := rs (se 1 (by rfl) ⟨39881, by rfl⟩) R79763
theorem R53195 : Reach 53195 := rs (se 1 (by rfl) ⟨39896, by rfl⟩) R79793
theorem R53207 : Reach 53207 := rs (se 1 (by rfl) ⟨39905, by rfl⟩) R79811
theorem R118745 : Reach 118745 := rs (se 2 (by rfl) ⟨44529, by rfl⟩) R89059
theorem R53227 : Reach 53227 := rs (se 1 (by rfl) ⟨39920, by rfl⟩) R79841
theorem R53239 : Reach 53239 := rs (se 1 (by rfl) ⟨39929, by rfl⟩) R79859
theorem R53259 : Reach 53259 := rs (se 1 (by rfl) ⟨39944, by rfl⟩) R79889
theorem R53271 : Reach 53271 := rs (se 1 (by rfl) ⟨39953, by rfl⟩) R79907
theorem R53291 : Reach 53291 := rs (se 1 (by rfl) ⟨39968, by rfl⟩) R79937
theorem R118835 : Reach 118835 := rs (se 1 (by rfl) ⟨89126, by rfl⟩) R178253
theorem R53303 : Reach 53303 := rs (se 1 (by rfl) ⟨39977, by rfl⟩) R79955
theorem R53323 : Reach 53323 := rs (se 1 (by rfl) ⟨39992, by rfl⟩) R79985
theorem R118871 : Reach 118871 := rs (se 1 (by rfl) ⟨89153, by rfl⟩) R178307
theorem R53335 : Reach 53335 := rs (se 1 (by rfl) ⟨40001, by rfl⟩) R80003
theorem R184409 : Reach 184409 := rs (se 2 (by rfl) ⟨69153, by rfl⟩) R138307
theorem R53355 : Reach 53355 := rs (se 1 (by rfl) ⟨40016, by rfl⟩) R80033
theorem R53367 : Reach 53367 := rs (se 1 (by rfl) ⟨40025, by rfl⟩) R80051
theorem R53387 : Reach 53387 := rs (se 1 (by rfl) ⟨40040, by rfl⟩) R80081
theorem R53399 : Reach 53399 := rs (se 1 (by rfl) ⟨40049, by rfl⟩) R80099
theorem R53419 : Reach 53419 := rs (se 1 (by rfl) ⟨40064, by rfl⟩) R80129
theorem R53431 : Reach 53431 := rs (se 1 (by rfl) ⟨40073, by rfl⟩) R80147
theorem R53451 : Reach 53451 := rs (se 1 (by rfl) ⟨40088, by rfl⟩) R80177
theorem R53463 : Reach 53463 := rs (se 1 (by rfl) ⟨40097, by rfl⟩) R80195
theorem R151769 : Reach 151769 := rs (se 2 (by rfl) ⟨56913, by rfl⟩) R113827
theorem R53483 : Reach 53483 := rs (se 1 (by rfl) ⟨40112, by rfl⟩) R80225
theorem R53495 : Reach 53495 := rs (se 1 (by rfl) ⟨40121, by rfl⟩) R80243
theorem R119051 : Reach 119051 := rs (se 1 (by rfl) ⟨89288, by rfl⟩) R178577
theorem R53515 : Reach 53515 := rs (se 1 (by rfl) ⟨40136, by rfl⟩) R80273
theorem R53527 : Reach 53527 := rs (se 1 (by rfl) ⟨40145, by rfl⟩) R80291
theorem R53547 : Reach 53547 := rs (se 1 (by rfl) ⟨40160, by rfl⟩) R80321
theorem R643373 : Reach 643373 := rs (se 3 (by rfl) ⟨120632, by rfl⟩) R241265
theorem R53559 : Reach 53559 := rs (se 1 (by rfl) ⟨40169, by rfl⟩) R80339
theorem R119105 : Reach 119105 := rs (se 2 (by rfl) ⟨44664, by rfl⟩) R89329
theorem R53579 : Reach 53579 := rs (se 1 (by rfl) ⟨40184, by rfl⟩) R80369
theorem R86359 : Reach 86359 := rs (se 1 (by rfl) ⟨64769, by rfl⟩) R129539
theorem R53591 : Reach 53591 := rs (se 1 (by rfl) ⟨40193, by rfl⟩) R80387
theorem R53611 : Reach 53611 := rs (se 1 (by rfl) ⟨40208, by rfl⟩) R80417
theorem R53623 : Reach 53623 := rs (se 1 (by rfl) ⟨40217, by rfl⟩) R80435
theorem R53643 : Reach 53643 := rs (se 1 (by rfl) ⟨40232, by rfl⟩) R80465
theorem R53655 : Reach 53655 := rs (se 1 (by rfl) ⟨40241, by rfl⟩) R80483
theorem R53675 : Reach 53675 := rs (se 1 (by rfl) ⟨40256, by rfl⟩) R80513
theorem R53687 : Reach 53687 := rs (se 1 (by rfl) ⟨40265, by rfl⟩) R80531
theorem R53707 : Reach 53707 := rs (se 1 (by rfl) ⟨40280, by rfl⟩) R80561
theorem R53719 : Reach 53719 := rs (se 1 (by rfl) ⟨40289, by rfl⟩) R80579
theorem R53739 : Reach 53739 := rs (se 1 (by rfl) ⟨40304, by rfl⟩) R80609
theorem R53751 : Reach 53751 := rs (se 1 (by rfl) ⟨40313, by rfl⟩) R80627
theorem R53771 : Reach 53771 := rs (se 1 (by rfl) ⟨40328, by rfl⟩) R80657
theorem R53783 : Reach 53783 := rs (se 1 (by rfl) ⟨40337, by rfl⟩) R80675
theorem R119321 : Reach 119321 := rs (se 2 (by rfl) ⟨44745, by rfl⟩) R89491
theorem R53803 : Reach 53803 := rs (se 1 (by rfl) ⟨40352, by rfl⟩) R80705
theorem R53815 : Reach 53815 := rs (se 1 (by rfl) ⟨40361, by rfl⟩) R80723
theorem R53835 : Reach 53835 := rs (se 1 (by rfl) ⟨40376, by rfl⟩) R80753
theorem R53847 : Reach 53847 := rs (se 1 (by rfl) ⟨40385, by rfl⟩) R80771
theorem R53867 : Reach 53867 := rs (se 1 (by rfl) ⟨40400, by rfl⟩) R80801
theorem R119411 : Reach 119411 := rs (se 1 (by rfl) ⟨89558, by rfl⟩) R179117
theorem R53879 : Reach 53879 := rs (se 1 (by rfl) ⟨40409, by rfl⟩) R80819
theorem R53899 : Reach 53899 := rs (se 1 (by rfl) ⟨40424, by rfl⟩) R80849
theorem R119447 : Reach 119447 := rs (se 1 (by rfl) ⟨89585, by rfl⟩) R179171
theorem R53911 : Reach 53911 := rs (se 1 (by rfl) ⟨40433, by rfl⟩) R80867
theorem R53931 : Reach 53931 := rs (se 1 (by rfl) ⟨40448, by rfl⟩) R80897
theorem R53943 : Reach 53943 := rs (se 1 (by rfl) ⟨40457, by rfl⟩) R80915
theorem R53963 : Reach 53963 := rs (se 1 (by rfl) ⟨40472, by rfl⟩) R80945
theorem R53975 : Reach 53975 := rs (se 1 (by rfl) ⟨40481, by rfl⟩) R80963
theorem R53995 : Reach 53995 := rs (se 1 (by rfl) ⟨40496, by rfl⟩) R80993
theorem R54007 : Reach 54007 := rs (se 1 (by rfl) ⟨40505, by rfl⟩) R81011
theorem R54027 : Reach 54027 := rs (se 1 (by rfl) ⟨40520, by rfl⟩) R81041
theorem R54039 : Reach 54039 := rs (se 1 (by rfl) ⟨40529, by rfl⟩) R81059
theorem R185111 : Reach 185111 := rs (se 1 (by rfl) ⟨138833, by rfl⟩) R277667
theorem R54059 : Reach 54059 := rs (se 1 (by rfl) ⟨40544, by rfl⟩) R81089
theorem R54071 : Reach 54071 := rs (se 1 (by rfl) ⟨40553, by rfl⟩) R81107
theorem R119627 : Reach 119627 := rs (se 1 (by rfl) ⟨89720, by rfl⟩) R179441
theorem R54091 : Reach 54091 := rs (se 1 (by rfl) ⟨40568, by rfl⟩) R81137
theorem R54103 : Reach 54103 := rs (se 1 (by rfl) ⟨40577, by rfl⟩) R81155
theorem R414557 : Reach 414557 := rs (se 3 (by rfl) ⟨77729, by rfl⟩) R155459
theorem R54123 : Reach 54123 := rs (se 1 (by rfl) ⟨40592, by rfl⟩) R81185
theorem R54135 : Reach 54135 := rs (se 1 (by rfl) ⟨40601, by rfl⟩) R81203
theorem R119681 : Reach 119681 := rs (se 2 (by rfl) ⟨44880, by rfl⟩) R89761
theorem R185219 : Reach 185219 := rs (se 1 (by rfl) ⟨138914, by rfl⟩) R277829
theorem R54155 : Reach 54155 := rs (se 1 (by rfl) ⟨40616, by rfl⟩) R81233
theorem R54167 : Reach 54167 := rs (se 1 (by rfl) ⟨40625, by rfl⟩) R81251
theorem R54187 : Reach 54187 := rs (se 1 (by rfl) ⟨40640, by rfl⟩) R81281
theorem R54199 : Reach 54199 := rs (se 1 (by rfl) ⟨40649, by rfl⟩) R81299
theorem R86987 : Reach 86987 := rs (se 1 (by rfl) ⟨65240, by rfl⟩) R130481
theorem R54219 : Reach 54219 := rs (se 1 (by rfl) ⟨40664, by rfl⟩) R81329
theorem R54231 : Reach 54231 := rs (se 1 (by rfl) ⟨40673, by rfl⟩) R81347
theorem R54251 : Reach 54251 := rs (se 1 (by rfl) ⟨40688, by rfl⟩) R81377
theorem R54263 : Reach 54263 := rs (se 1 (by rfl) ⟨40697, by rfl⟩) R81395
theorem R54283 : Reach 54283 := rs (se 1 (by rfl) ⟨40712, by rfl⟩) R81425
theorem R54295 : Reach 54295 := rs (se 1 (by rfl) ⟨40721, by rfl⟩) R81443
theorem R54315 : Reach 54315 := rs (se 1 (by rfl) ⟨40736, by rfl⟩) R81473
theorem R54327 : Reach 54327 := rs (se 1 (by rfl) ⟨40745, by rfl⟩) R81491
theorem R87115 : Reach 87115 := rs (se 1 (by rfl) ⟨65336, by rfl⟩) R130673
theorem R54347 : Reach 54347 := rs (se 1 (by rfl) ⟨40760, by rfl⟩) R81521
theorem R54359 : Reach 54359 := rs (se 1 (by rfl) ⟨40769, by rfl⟩) R81539
theorem R119897 : Reach 119897 := rs (se 2 (by rfl) ⟨44961, by rfl⟩) R89923
theorem R54379 : Reach 54379 := rs (se 1 (by rfl) ⟨40784, by rfl⟩) R81569
theorem R54391 : Reach 54391 := rs (se 1 (by rfl) ⟨40793, by rfl⟩) R81587
theorem R54411 : Reach 54411 := rs (se 1 (by rfl) ⟨40808, by rfl⟩) R81617
theorem R185489 : Reach 185489 := rs (se 2 (by rfl) ⟨69558, by rfl⟩) R139117
theorem R54423 : Reach 54423 := rs (se 1 (by rfl) ⟨40817, by rfl⟩) R81635
theorem R54443 : Reach 54443 := rs (se 1 (by rfl) ⟨40832, by rfl⟩) R81665
theorem R119987 : Reach 119987 := rs (se 1 (by rfl) ⟨89990, by rfl⟩) R179981
theorem R54455 : Reach 54455 := rs (se 1 (by rfl) ⟨40841, by rfl⟩) R81683
theorem R54475 : Reach 54475 := rs (se 1 (by rfl) ⟨40856, by rfl⟩) R81713
theorem R120023 : Reach 120023 := rs (se 1 (by rfl) ⟨90017, by rfl⟩) R180035
theorem R87257 : Reach 87257 := rs (se 2 (by rfl) ⟨32721, by rfl⟩) R65443
theorem R54487 : Reach 54487 := rs (se 1 (by rfl) ⟨40865, by rfl⟩) R81731
theorem R54507 : Reach 54507 := rs (se 1 (by rfl) ⟨40880, by rfl⟩) R81761
theorem R54519 : Reach 54519 := rs (se 1 (by rfl) ⟨40889, by rfl⟩) R81779
theorem R54539 : Reach 54539 := rs (se 1 (by rfl) ⟨40904, by rfl⟩) R81809
theorem R54551 : Reach 54551 := rs (se 1 (by rfl) ⟨40913, by rfl⟩) R81827
theorem R54571 : Reach 54571 := rs (se 1 (by rfl) ⟨40928, by rfl⟩) R81857
theorem R185651 : Reach 185651 := rs (se 1 (by rfl) ⟨139238, by rfl⟩) R278477
theorem R54583 : Reach 54583 := rs (se 1 (by rfl) ⟨40937, by rfl⟩) R81875
theorem R54603 : Reach 54603 := rs (se 1 (by rfl) ⟨40952, by rfl⟩) R81905
theorem R54615 : Reach 54615 := rs (se 1 (by rfl) ⟨40961, by rfl⟩) R81923
theorem R87385 : Reach 87385 := rs (se 2 (by rfl) ⟨32769, by rfl⟩) R65539
theorem R54635 : Reach 54635 := rs (se 1 (by rfl) ⟨40976, by rfl⟩) R81953
theorem R54647 : Reach 54647 := rs (se 1 (by rfl) ⟨40985, by rfl⟩) R81971
theorem R120203 : Reach 120203 := rs (se 1 (by rfl) ⟨90152, by rfl⟩) R180305
theorem R54667 : Reach 54667 := rs (se 1 (by rfl) ⟨41000, by rfl⟩) R82001
theorem R54679 : Reach 54679 := rs (se 1 (by rfl) ⟨41009, by rfl⟩) R82019
theorem R54699 : Reach 54699 := rs (se 1 (by rfl) ⟨41024, by rfl⟩) R82049
theorem R54711 : Reach 54711 := rs (se 1 (by rfl) ⟨41033, by rfl⟩) R82067
theorem R120257 : Reach 120257 := rs (se 2 (by rfl) ⟨45096, by rfl⟩) R90193
theorem R54731 : Reach 54731 := rs (se 1 (by rfl) ⟨41048, by rfl⟩) R82097
theorem R54743 : Reach 54743 := rs (se 1 (by rfl) ⟨41057, by rfl⟩) R82115
theorem R54763 : Reach 54763 := rs (se 1 (by rfl) ⟨41072, by rfl⟩) R82145
theorem R54775 : Reach 54775 := rs (se 1 (by rfl) ⟨41081, by rfl⟩) R82163
theorem R54795 : Reach 54795 := rs (se 1 (by rfl) ⟨41096, by rfl⟩) R82193
theorem R54807 : Reach 54807 := rs (se 1 (by rfl) ⟨41105, by rfl⟩) R82211
theorem R54827 : Reach 54827 := rs (se 1 (by rfl) ⟨41120, by rfl⟩) R82241
theorem R54839 : Reach 54839 := rs (se 1 (by rfl) ⟨41129, by rfl⟩) R82259
theorem R185921 : Reach 185921 := rs (se 2 (by rfl) ⟨69720, by rfl⟩) R139441
theorem R54859 : Reach 54859 := rs (se 1 (by rfl) ⟨41144, by rfl⟩) R82289
theorem R54871 : Reach 54871 := rs (se 1 (by rfl) ⟨41153, by rfl⟩) R82307
theorem R153181 : Reach 153181 := rs (se 3 (by rfl) ⟨28721, by rfl⟩) R57443
theorem R54891 : Reach 54891 := rs (se 1 (by rfl) ⟨41168, by rfl⟩) R82337
theorem R54903 : Reach 54903 := rs (se 1 (by rfl) ⟨41177, by rfl⟩) R82355
theorem R54923 : Reach 54923 := rs (se 1 (by rfl) ⟨41192, by rfl⟩) R82385
theorem R54935 : Reach 54935 := rs (se 1 (by rfl) ⟨41201, by rfl⟩) R82403
theorem R120473 : Reach 120473 := rs (se 2 (by rfl) ⟨45177, by rfl⟩) R90355
theorem R54955 : Reach 54955 := rs (se 1 (by rfl) ⟨41216, by rfl⟩) R82433
theorem R186029 : Reach 186029 := rs (se 3 (by rfl) ⟨34880, by rfl⟩) R69761
theorem R382643 : Reach 382643 := rs (se 1 (by rfl) ⟨286982, by rfl⟩) R573965
theorem R54967 : Reach 54967 := rs (se 1 (by rfl) ⟨41225, by rfl⟩) R82451
theorem R54987 : Reach 54987 := rs (se 1 (by rfl) ⟨41240, by rfl⟩) R82481
theorem R54999 : Reach 54999 := rs (se 1 (by rfl) ⟨41249, by rfl⟩) R82499
theorem R55019 : Reach 55019 := rs (se 1 (by rfl) ⟨41264, by rfl⟩) R82529
theorem R120563 : Reach 120563 := rs (se 1 (by rfl) ⟨90422, by rfl⟩) R180845
theorem R55031 : Reach 55031 := rs (se 1 (by rfl) ⟨41273, by rfl⟩) R82547
theorem R55051 : Reach 55051 := rs (se 1 (by rfl) ⟨41288, by rfl⟩) R82577
theorem R120599 : Reach 120599 := rs (se 1 (by rfl) ⟨90449, by rfl⟩) R180899
theorem R55063 : Reach 55063 := rs (se 1 (by rfl) ⟨41297, by rfl⟩) R82595
theorem R55083 : Reach 55083 := rs (se 1 (by rfl) ⟨41312, by rfl⟩) R82625
theorem R55095 : Reach 55095 := rs (se 1 (by rfl) ⟨41321, by rfl⟩) R82643
theorem R153409 : Reach 153409 := rs (se 2 (by rfl) ⟨57528, by rfl⟩) R115057
theorem R55115 : Reach 55115 := rs (se 1 (by rfl) ⟨41336, by rfl⟩) R82673
theorem R55127 : Reach 55127 := rs (se 1 (by rfl) ⟨41345, by rfl⟩) R82691
theorem R87959 : Reach 87959 := rs (se 1 (by rfl) ⟨65969, by rfl⟩) R131939
theorem R120779 : Reach 120779 := rs (se 1 (by rfl) ⟨90584, by rfl⟩) R181169
theorem R481241 : Reach 481241 := rs (se 2 (by rfl) ⟨180465, by rfl⟩) R360931
theorem R120833 : Reach 120833 := rs (se 2 (by rfl) ⟨45312, by rfl⟩) R90625
theorem R88087 : Reach 88087 := rs (se 1 (by rfl) ⟨66065, by rfl⟩) R132131
theorem R448577 : Reach 448577 := rs (se 2 (by rfl) ⟨168216, by rfl⟩) R336433
theorem R153751 : Reach 153751 := rs (se 1 (by rfl) ⟨115313, by rfl⟩) R230627
theorem R121049 : Reach 121049 := rs (se 2 (by rfl) ⟨45393, by rfl⟩) R90787
theorem R121139 : Reach 121139 := rs (se 1 (by rfl) ⟨90854, by rfl⟩) R181709
theorem R121409 : Reach 121409 := rs (se 2 (by rfl) ⟨45528, by rfl⟩) R91057
theorem R219779 : Reach 219779 := rs (se 1 (by rfl) ⟨164834, by rfl⟩) R329669
theorem R88715 : Reach 88715 := rs (se 1 (by rfl) ⟨66536, by rfl⟩) R133073
theorem R55991 : Reach 55991 := rs (se 1 (by rfl) ⟨41993, by rfl⟩) R83987
theorem R88843 : Reach 88843 := rs (se 1 (by rfl) ⟨66632, by rfl⟩) R133265
theorem R187201 : Reach 187201 := rs (se 2 (by rfl) ⟨70200, by rfl⟩) R140401
theorem R187211 : Reach 187211 := rs (se 1 (by rfl) ⟨140408, by rfl⟩) R280817
theorem R154457 : Reach 154457 := rs (se 2 (by rfl) ⟨57921, by rfl⟩) R115843
theorem R121751 : Reach 121751 := rs (se 1 (by rfl) ⟨91313, by rfl⟩) R182627
theorem R88985 : Reach 88985 := rs (se 2 (by rfl) ⟨33369, by rfl⟩) R66739
theorem R89113 : Reach 89113 := rs (se 2 (by rfl) ⟨33417, by rfl⟩) R66835
theorem R154675 : Reach 154675 := rs (se 1 (by rfl) ⟨116006, by rfl⟩) R232013
theorem R121931 : Reach 121931 := rs (se 1 (by rfl) ⟨91448, by rfl⟩) R182897
theorem R679063 : Reach 679063 := rs (se 1 (by rfl) ⟨509297, by rfl⟩) R1018595
theorem R122201 : Reach 122201 := rs (se 2 (by rfl) ⟨45825, by rfl⟩) R91651
theorem R122291 : Reach 122291 := rs (se 1 (by rfl) ⟨91718, by rfl⟩) R183437
theorem R89687 : Reach 89687 := rs (se 1 (by rfl) ⟨67265, by rfl⟩) R134531
theorem R122561 : Reach 122561 := rs (se 2 (by rfl) ⟨45960, by rfl⟩) R91921
theorem R89815 : Reach 89815 := rs (se 1 (by rfl) ⟨67361, by rfl⟩) R134723
theorem R57067 : Reach 57067 := rs (se 1 (by rfl) ⟨42800, by rfl⟩) R85601
theorem R122903 : Reach 122903 := rs (se 1 (by rfl) ⟨92177, by rfl⟩) R184355
theorem R352349 : Reach 352349 := rs (se 3 (by rfl) ⟨66065, by rfl⟩) R132131
theorem R123083 : Reach 123083 := rs (se 1 (by rfl) ⟨92312, by rfl⟩) R184625
theorem R57559 : Reach 57559 := rs (se 1 (by rfl) ⟨43169, by rfl⟩) R86339
theorem R778481 : Reach 778481 := rs (se 2 (by rfl) ⟨291930, by rfl⟩) R583861
theorem R90443 : Reach 90443 := rs (se 1 (by rfl) ⟨67832, by rfl⟩) R135665
theorem R57739 : Reach 57739 := rs (se 1 (by rfl) ⟨43304, by rfl⟩) R86609
theorem R156097 : Reach 156097 := rs (se 2 (by rfl) ⟨58536, by rfl⟩) R117073
theorem R90571 : Reach 90571 := rs (se 1 (by rfl) ⟨67928, by rfl⟩) R135857
theorem R123353 : Reach 123353 := rs (se 2 (by rfl) ⟨46257, by rfl⟩) R92515
theorem R57847 : Reach 57847 := rs (se 1 (by rfl) ⟨43385, by rfl⟩) R86771
theorem R123443 : Reach 123443 := rs (se 1 (by rfl) ⟨92582, by rfl⟩) R185165
theorem R90713 : Reach 90713 := rs (se 2 (by rfl) ⟨34017, by rfl⟩) R68035
theorem R58007 : Reach 58007 := rs (se 1 (by rfl) ⟨43505, by rfl⟩) R87011
theorem R58027 : Reach 58027 := rs (se 1 (by rfl) ⟨43520, by rfl⟩) R87041
theorem R90841 : Reach 90841 := rs (se 2 (by rfl) ⟨34065, by rfl⟩) R68131
theorem R58135 : Reach 58135 := rs (se 1 (by rfl) ⟨43601, by rfl⟩) R87203
theorem R1008449 : Reach 1008449 := rs (se 2 (by rfl) ⟨378168, by rfl⟩) R756337
theorem R123713 : Reach 123713 := rs (se 2 (by rfl) ⟨46392, by rfl⟩) R92785
theorem R58315 : Reach 58315 := rs (se 1 (by rfl) ⟨43736, by rfl⟩) R87473
theorem R58423 : Reach 58423 := rs (se 1 (by rfl) ⟨43817, by rfl⟩) R87635
theorem R58603 : Reach 58603 := rs (se 1 (by rfl) ⟨43952, by rfl⟩) R87905
theorem R189719 : Reach 189719 := rs (se 1 (by rfl) ⟨142289, by rfl⟩) R284579
theorem R91415 : Reach 91415 := rs (se 1 (by rfl) ⟨68561, by rfl⟩) R137123
theorem R124211 : Reach 124211 := rs (se 1 (by rfl) ⟨93158, by rfl⟩) R186317
theorem R58711 : Reach 58711 := rs (se 1 (by rfl) ⟨44033, by rfl⟩) R88067
theorem R91543 : Reach 91543 := rs (se 1 (by rfl) ⟨68657, by rfl⟩) R137315
theorem R124363 : Reach 124363 := rs (se 1 (by rfl) ⟨93272, by rfl⟩) R186545
theorem R58891 : Reach 58891 := rs (se 1 (by rfl) ⟨44168, by rfl⟩) R88337
theorem R58999 : Reach 58999 := rs (se 1 (by rfl) ⟨44249, by rfl⟩) R88499
theorem R59179 : Reach 59179 := rs (se 1 (by rfl) ⟨44384, by rfl⟩) R88769
theorem R91955 : Reach 91955 := rs (se 1 (by rfl) ⟨68966, by rfl⟩) R137933
theorem R223069 : Reach 223069 := rs (se 3 (by rfl) ⟨41825, by rfl⟩) R83651
theorem R59287 : Reach 59287 := rs (se 1 (by rfl) ⟨44465, by rfl⟩) R88931
theorem R92083 : Reach 92083 := rs (se 1 (by rfl) ⟨69062, by rfl⟩) R138125
theorem R157643 : Reach 157643 := rs (se 1 (by rfl) ⟨118232, by rfl⟩) R236465
theorem R92171 : Reach 92171 := rs (se 1 (by rfl) ⟨69128, by rfl⟩) R138257
theorem R92225 : Reach 92225 := rs (se 2 (by rfl) ⟨34584, by rfl⟩) R69169
theorem R59467 : Reach 59467 := rs (se 1 (by rfl) ⟨44600, by rfl⟩) R89201
theorem R92299 : Reach 92299 := rs (se 1 (by rfl) ⟨69224, by rfl⟩) R138449
theorem R59575 : Reach 59575 := rs (se 1 (by rfl) ⟨44681, by rfl⟩) R89363
theorem R157889 : Reach 157889 := rs (se 2 (by rfl) ⟨59208, by rfl⟩) R118417
theorem R92353 : Reach 92353 := rs (se 2 (by rfl) ⟨34632, by rfl⟩) R69265
theorem R92441 : Reach 92441 := rs (se 2 (by rfl) ⟨34665, by rfl⟩) R69331
theorem R223553 : Reach 223553 := rs (se 2 (by rfl) ⟨83832, by rfl⟩) R167665
theorem R59755 : Reach 59755 := rs (se 1 (by rfl) ⟨44816, by rfl⟩) R89633
theorem R92569 : Reach 92569 := rs (se 2 (by rfl) ⟨34713, by rfl⟩) R69427
theorem R59863 : Reach 59863 := rs (se 1 (by rfl) ⟨44897, by rfl⟩) R89795
theorem R649745 : Reach 649745 := rs (se 2 (by rfl) ⟨243654, by rfl⟩) R487309
theorem R879173 : Reach 879173 := rs (se 4 (by rfl) ⟨82422, by rfl⟩) R164845
theorem R60043 : Reach 60043 := rs (se 1 (by rfl) ⟨45032, by rfl⟩) R90065
theorem R60151 : Reach 60151 := rs (se 1 (by rfl) ⟨45113, by rfl⟩) R90227
theorem R92993 : Reach 92993 := rs (se 2 (by rfl) ⟨34872, by rfl⟩) R69745
theorem R60331 : Reach 60331 := rs (se 1 (by rfl) ⟨45248, by rfl⟩) R90497
theorem R93145 : Reach 93145 := rs (se 2 (by rfl) ⟨34929, by rfl⟩) R69859
theorem R60439 : Reach 60439 := rs (se 1 (by rfl) ⟨45329, by rfl⟩) R90659
theorem R1338443 : Reach 1338443 := rs (se 1 (by rfl) ⟨1003832, by rfl⟩) R2007665
theorem R224407 : Reach 224407 := rs (se 1 (by rfl) ⟨168305, by rfl⟩) R336611
theorem R60619 : Reach 60619 := rs (se 1 (by rfl) ⟨45464, by rfl⟩) R90929
theorem R388313 : Reach 388313 := rs (se 2 (by rfl) ⟨145617, by rfl⟩) R291235
theorem R224477 : Reach 224477 := rs (se 3 (by rfl) ⟨42089, by rfl⟩) R84179
theorem R945413 : Reach 945413 := rs (se 4 (by rfl) ⟨88632, by rfl⟩) R177265
theorem R93491 : Reach 93491 := rs (se 1 (by rfl) ⟨70118, by rfl⟩) R140237
theorem R159127 : Reach 159127 := rs (se 1 (by rfl) ⟨119345, by rfl⟩) R238691
theorem R93707 : Reach 93707 := rs (se 1 (by rfl) ⟨70280, by rfl⟩) R140561
theorem R61015 : Reach 61015 := rs (se 1 (by rfl) ⟨45761, by rfl⟩) R91523
theorem R93889 : Reach 93889 := rs (se 2 (by rfl) ⟨35208, by rfl⟩) R70417
theorem R454349 : Reach 454349 := rs (se 3 (by rfl) ⟨85190, by rfl⟩) R170381
theorem R93953 : Reach 93953 := rs (se 2 (by rfl) ⟨35232, by rfl⟩) R70465
theorem R61195 : Reach 61195 := rs (se 1 (by rfl) ⟨45896, by rfl⟩) R91793
theorem R192601 : Reach 192601 := rs (se 2 (by rfl) ⟨72225, by rfl⟩) R144451
theorem R61591 : Reach 61591 := rs (se 1 (by rfl) ⟨46193, by rfl⟩) R92387
theorem R258227 : Reach 258227 := rs (se 1 (by rfl) ⟨193670, by rfl⟩) R387341
theorem R94529 : Reach 94529 := rs (se 2 (by rfl) ⟨35448, by rfl⟩) R70897
theorem R192833 : Reach 192833 := rs (se 2 (by rfl) ⟨72312, by rfl⟩) R144625
theorem R61771 : Reach 61771 := rs (se 1 (by rfl) ⟨46328, by rfl⟩) R92657
theorem R62155 : Reach 62155 := rs (se 1 (by rfl) ⟨46616, by rfl⟩) R93233
theorem R291545 : Reach 291545 := rs (se 2 (by rfl) ⟨109329, by rfl⟩) R218659
theorem R488369 : Reach 488369 := rs (se 2 (by rfl) ⟨183138, by rfl⟩) R366277
theorem R95321 : Reach 95321 := rs (se 2 (by rfl) ⟨35745, by rfl⟩) R71491
theorem R161099 : Reach 161099 := rs (se 1 (by rfl) ⟨120824, by rfl⟩) R241649
theorem R128729 : Reach 128729 := rs (se 2 (by rfl) ⟨48273, by rfl⟩) R96547
theorem R423755 : Reach 423755 := rs (se 1 (by rfl) ⟨317816, by rfl⟩) R635633
theorem R292709 : Reach 292709 := rs (se 4 (by rfl) ⟨27441, by rfl⟩) R54883
theorem R194507 : Reach 194507 := rs (se 1 (by rfl) ⟨145880, by rfl⟩) R291761
theorem R194521 : Reach 194521 := rs (se 2 (by rfl) ⟨72945, by rfl⟩) R145891
theorem R260171 : Reach 260171 := rs (se 1 (by rfl) ⟨195128, by rfl⟩) R390257
theorem R96331 : Reach 96331 := rs (se 1 (by rfl) ⟨72248, by rfl⟩) R144497
theorem R96395 : Reach 96395 := rs (se 1 (by rfl) ⟨72296, by rfl⟩) R144593
theorem R2586775 : Reach 2586775 := rs (se 1 (by rfl) ⟨1940081, by rfl⟩) R3880163
theorem R227843 : Reach 227843 := rs (se 1 (by rfl) ⟨170882, by rfl⟩) R341765
theorem R129559 : Reach 129559 := rs (se 1 (by rfl) ⟨97169, by rfl⟩) R194339
theorem R391715 : Reach 391715 := rs (se 1 (by rfl) ⟨293786, by rfl⟩) R587573
theorem R97139 : Reach 97139 := rs (se 1 (by rfl) ⟨72854, by rfl⟩) R145709
theorem R195479 : Reach 195479 := rs (se 1 (by rfl) ⟨146609, by rfl⟩) R293219
theorem R129995 : Reach 129995 := rs (se 1 (by rfl) ⟨97496, by rfl⟩) R194993
theorem R97291 : Reach 97291 := rs (se 1 (by rfl) ⟨72968, by rfl⟩) R145937
theorem R130369 : Reach 130369 := rs (se 2 (by rfl) ⟨48888, by rfl⟩) R97777
theorem R97625 : Reach 97625 := rs (se 2 (by rfl) ⟨36609, by rfl⟩) R73219
theorem R196289 : Reach 196289 := rs (se 2 (by rfl) ⟨73608, by rfl⟩) R147217
theorem R261953 : Reach 261953 := rs (se 2 (by rfl) ⟨98232, by rfl⟩) R196465
theorem R130967 : Reach 130967 := rs (se 1 (by rfl) ⟨98225, by rfl⟩) R196451
theorem R65431 : Reach 65431 := rs (se 1 (by rfl) ⟨49073, by rfl⟩) R98147
theorem R1343411 : Reach 1343411 := rs (se 1 (by rfl) ⟨1007558, by rfl⟩) R2015117
theorem R98263 : Reach 98263 := rs (se 1 (by rfl) ⟨73697, by rfl⟩) R147395
theorem R98347 : Reach 98347 := rs (se 1 (by rfl) ⟨73760, by rfl⟩) R147521
theorem R524333 : Reach 524333 := rs (se 3 (by rfl) ⟨98312, by rfl⟩) R196625
theorem R131159 : Reach 131159 := rs (se 1 (by rfl) ⟨98369, by rfl⟩) R196739
theorem R40337621 : Reach 40337621 := rs (se 7 (by rfl) ⟨472706, by rfl⟩) R945413
theorem R164231 : Reach 164231 := rs (se 1 (by rfl) ⟨123173, by rfl⟩) R246347
theorem R229841 : Reach 229841 := rs (se 2 (by rfl) ⟨86190, by rfl⟩) R172381
theorem R295427 : Reach 295427 := rs (se 1 (by rfl) ⟨221570, by rfl⟩) R443141
theorem R66091 : Reach 66091 := rs (se 1 (by rfl) ⟨49568, by rfl⟩) R99137
theorem R262723 : Reach 262723 := rs (se 1 (by rfl) ⟨197042, by rfl⟩) R394085
theorem R131699 : Reach 131699 := rs (se 1 (by rfl) ⟨98774, by rfl⟩) R197549
theorem R132025 : Reach 132025 := rs (se 2 (by rfl) ⟨49509, by rfl⟩) R99019
theorem R295883 : Reach 295883 := rs (se 1 (by rfl) ⟨221912, by rfl⟩) R443825
theorem R918539 : Reach 918539 := rs (se 1 (by rfl) ⟨688904, by rfl⟩) R1377809
theorem R99463 : Reach 99463 := rs (se 1 (by rfl) ⟨74597, by rfl⟩) R149195
theorem R165179 : Reach 165179 := rs (se 1 (by rfl) ⟨123884, by rfl⟩) R247769
theorem R394631 : Reach 394631 := rs (se 1 (by rfl) ⟨295973, by rfl⟩) R591947
theorem R67063 : Reach 67063 := rs (se 1 (by rfl) ⟨50297, by rfl⟩) R100595
theorem R886373 : Reach 886373 := rs (se 4 (by rfl) ⟨83097, by rfl⟩) R166195
theorem R296567 : Reach 296567 := rs (se 1 (by rfl) ⟨222425, by rfl⟩) R444851
theorem R100025 : Reach 100025 := rs (se 2 (by rfl) ⟨37509, by rfl⟩) R75019
theorem R67387 : Reach 67387 := rs (se 1 (by rfl) ⟨50540, by rfl⟩) R101081
theorem R165817 : Reach 165817 := rs (se 2 (by rfl) ⟨62181, by rfl⟩) R124363
theorem R264221 : Reach 264221 := rs (se 3 (by rfl) ⟨49541, by rfl⟩) R99083
theorem R133235 : Reach 133235 := rs (se 1 (by rfl) ⟨99926, by rfl⟩) R199853
theorem R297425 : Reach 297425 := rs (se 2 (by rfl) ⟨111534, by rfl⟩) R223069
theorem R264707 : Reach 264707 := rs (se 1 (by rfl) ⟨198530, by rfl⟩) R397061
theorem R133751 : Reach 133751 := rs (se 1 (by rfl) ⟨100313, by rfl⟩) R200627
theorem R133817 : Reach 133817 := rs (se 2 (by rfl) ⟨50181, by rfl⟩) R100363
theorem R68359 : Reach 68359 := rs (se 1 (by rfl) ⟨51269, by rfl⟩) R102539
theorem R101179 : Reach 101179 := rs (se 1 (by rfl) ⟨75884, by rfl⟩) R151769
theorem R428915 : Reach 428915 := rs (se 1 (by rfl) ⟨321686, by rfl⟩) R643373
theorem R68779 : Reach 68779 := rs (se 1 (by rfl) ⟨51584, by rfl⟩) R103169
theorem R101665 : Reach 101665 := rs (se 2 (by rfl) ⟨38124, by rfl⟩) R76249
theorem R69007 : Reach 69007 := rs (se 1 (by rfl) ⟨51755, by rfl⟩) R103511
theorem R331229 : Reach 331229 := rs (se 3 (by rfl) ⟨62105, by rfl⟩) R124211
theorem R298525 : Reach 298525 := rs (se 3 (by rfl) ⟨55973, by rfl⟩) R111947
theorem R527939 : Reach 527939 := rs (se 1 (by rfl) ⟨395954, by rfl⟩) R791909
theorem R134743 : Reach 134743 := rs (se 1 (by rfl) ⟨101057, by rfl⟩) R202115
theorem R135047 : Reach 135047 := rs (se 1 (by rfl) ⟨101285, by rfl⟩) R202571
theorem R200657 : Reach 200657 := rs (se 2 (by rfl) ⟨75246, by rfl⟩) R150493
theorem R135179 : Reach 135179 := rs (se 1 (by rfl) ⟨101384, by rfl⟩) R202769
theorem R299051 : Reach 299051 := rs (se 1 (by rfl) ⟨224288, by rfl⟩) R448577
theorem R266327 : Reach 266327 := rs (se 1 (by rfl) ⟨199745, by rfl⟩) R399491
theorem R69751 : Reach 69751 := rs (se 1 (by rfl) ⟨52313, by rfl⟩) R104627
theorem R299209 : Reach 299209 := rs (se 2 (by rfl) ⟨112203, by rfl⟩) R224407
theorem R201113 : Reach 201113 := rs (se 2 (by rfl) ⟨75417, by rfl⟩) R150835
theorem R135695 : Reach 135695 := rs (se 1 (by rfl) ⟨101771, by rfl⟩) R203543
theorem R102971 : Reach 102971 := rs (se 1 (by rfl) ⟨77228, by rfl⟩) R154457
theorem R266813 : Reach 266813 := rs (se 3 (by rfl) ⟨50027, by rfl⟩) R100055
theorem R135827 : Reach 135827 := rs (se 1 (by rfl) ⟨101870, by rfl⟩) R203741
theorem R332747 : Reach 332747 := rs (se 1 (by rfl) ⟨249560, by rfl⟩) R499121
theorem R594955 : Reach 594955 := rs (se 1 (by rfl) ⟨446216, by rfl⟩) R892433
theorem R103457 : Reach 103457 := rs (se 2 (by rfl) ⟨38796, by rfl⟩) R77593
theorem R103609 : Reach 103609 := rs (se 2 (by rfl) ⟨38853, by rfl⟩) R77707
theorem R1283309 : Reach 1283309 := rs (se 3 (by rfl) ⟨240620, by rfl⟩) R481241
theorem R922913 : Reach 922913 := rs (se 2 (by rfl) ⟨346092, by rfl⟩) R692185
theorem R234899 : Reach 234899 := rs (se 1 (by rfl) ⟨176174, by rfl⟩) R352349
theorem R300509 : Reach 300509 := rs (se 3 (by rfl) ⟨56345, by rfl⟩) R112691
theorem R202283 : Reach 202283 := rs (se 1 (by rfl) ⟨151712, by rfl⟩) R303425
theorem R398915 : Reach 398915 := rs (se 1 (by rfl) ⟨299186, by rfl⟩) R598373
theorem R136961 : Reach 136961 := rs (se 2 (by rfl) ⟨51360, by rfl⟩) R102721
theorem R137335 : Reach 137335 := rs (se 1 (by rfl) ⟨103001, by rfl⟩) R206003
theorem R268595 : Reach 268595 := rs (se 1 (by rfl) ⟨201446, by rfl⟩) R402893
theorem R137771 : Reach 137771 := rs (se 1 (by rfl) ⟨103328, by rfl⟩) R206657
theorem R268919 : Reach 268919 := rs (se 1 (by rfl) ⟨201689, by rfl⟩) R403379
theorem R105095 : Reach 105095 := rs (se 1 (by rfl) ⟨78821, by rfl⟩) R157643
theorem R105259 : Reach 105259 := rs (se 1 (by rfl) ⟨78944, by rfl⟩) R157889
theorem R433163 : Reach 433163 := rs (se 1 (by rfl) ⟨324872, by rfl⟩) R649745
theorem R73003 : Reach 73003 := rs (se 1 (by rfl) ⟨54752, by rfl⟩) R109505
theorem R138611 : Reach 138611 := rs (se 1 (by rfl) ⟨103958, by rfl⟩) R207917
theorem R892295 : Reach 892295 := rs (se 1 (by rfl) ⟨669221, by rfl⟩) R1338443
theorem R138631 : Reach 138631 := rs (se 1 (by rfl) ⟨103973, by rfl⟩) R207947
theorem R73145 : Reach 73145 := rs (se 2 (by rfl) ⟨27429, by rfl⟩) R54859
theorem R204241 : Reach 204241 := rs (se 2 (by rfl) ⟨76590, by rfl⟩) R153181
theorem R499229 : Reach 499229 := rs (se 3 (by rfl) ⟨93605, by rfl⟩) R187211
theorem R138781 : Reach 138781 := rs (se 3 (by rfl) ⟨26021, by rfl⟩) R52043
theorem R269891 : Reach 269891 := rs (se 1 (by rfl) ⟨202418, by rfl⟩) R404837
theorem R138905 : Reach 138905 := rs (se 2 (by rfl) ⟨52089, by rfl⟩) R104179
theorem R564965 : Reach 564965 := rs (se 4 (by rfl) ⟨52965, by rfl⟩) R105931
theorem R204545 : Reach 204545 := rs (se 2 (by rfl) ⟨76704, by rfl⟩) R153409
theorem R73487 : Reach 73487 := rs (se 1 (by rfl) ⟨55115, by rfl⟩) R110231
theorem R302899 : Reach 302899 := rs (se 1 (by rfl) ⟨227174, by rfl⟩) R454349
theorem R139067 : Reach 139067 := rs (se 1 (by rfl) ⟨104300, by rfl⟩) R208601
theorem R270215 : Reach 270215 := rs (se 1 (by rfl) ⟨202661, by rfl⟩) R405323
theorem R139279 : Reach 139279 := rs (se 1 (by rfl) ⟨104459, by rfl⟩) R208919
theorem R172151 : Reach 172151 := rs (se 1 (by rfl) ⟨129113, by rfl⟩) R258227
theorem R205001 : Reach 205001 := rs (se 2 (by rfl) ⟨76875, by rfl⟩) R153751
theorem R3449033 : Reach 3449033 := rs (se 2 (by rfl) ⟨1293387, by rfl⟩) R2586775
theorem R172745 : Reach 172745 := rs (se 2 (by rfl) ⟨64779, by rfl⟩) R129559
theorem R402149 : Reach 402149 := rs (se 4 (by rfl) ⟨37701, by rfl⟩) R75403
theorem R107399 : Reach 107399 := rs (se 1 (by rfl) ⟨80549, by rfl⟩) R161099
theorem R500741 : Reach 500741 := rs (se 4 (by rfl) ⟨46944, by rfl⟩) R93889
theorem R336919 : Reach 336919 := rs (se 1 (by rfl) ⟨252689, by rfl⟩) R505379
theorem R304357 : Reach 304357 := rs (se 4 (by rfl) ⟨28533, by rfl⟩) R57067
theorem R173447 : Reach 173447 := rs (se 1 (by rfl) ⟨130085, by rfl⟩) R260171
theorem R206233 : Reach 206233 := rs (se 2 (by rfl) ⟨77337, by rfl⟩) R154675
theorem R173825 : Reach 173825 := rs (se 2 (by rfl) ⟨65184, by rfl⟩) R130369
theorem R75691 : Reach 75691 := rs (se 1 (by rfl) ⟨56768, by rfl⟩) R113537
theorem R75919 : Reach 75919 := rs (se 1 (by rfl) ⟨56939, by rfl⟩) R113879
theorem R174635 : Reach 174635 := rs (se 1 (by rfl) ⟨130976, by rfl⟩) R261953
theorem R895607 : Reach 895607 := rs (se 1 (by rfl) ⟨671705, by rfl⟩) R1343411
theorem R600695 : Reach 600695 := rs (se 1 (by rfl) ⟨450521, by rfl⟩) R901043
theorem R666305 : Reach 666305 := rs (se 2 (by rfl) ⟨249864, by rfl⟩) R499729
theorem R76715 : Reach 76715 := rs (se 1 (by rfl) ⟨57536, by rfl⟩) R115073
theorem R76745 : Reach 76745 := rs (se 2 (by rfl) ⟨28779, by rfl⟩) R57559
theorem R76859 : Reach 76859 := rs (se 1 (by rfl) ⟨57644, by rfl⟩) R115289
theorem R76919 : Reach 76919 := rs (se 1 (by rfl) ⟨57689, by rfl⟩) R115379
theorem R76943 : Reach 76943 := rs (se 1 (by rfl) ⟨57707, by rfl⟩) R115415
theorem R76985 : Reach 76985 := rs (se 2 (by rfl) ⟨28869, by rfl⟩) R57739
theorem R208129 : Reach 208129 := rs (se 2 (by rfl) ⟨78048, by rfl⟩) R156097
theorem R77063 : Reach 77063 := rs (se 1 (by rfl) ⟨57797, by rfl⟩) R115595
theorem R77099 : Reach 77099 := rs (se 1 (by rfl) ⟨57824, by rfl⟩) R115649
theorem R77129 : Reach 77129 := rs (se 2 (by rfl) ⟨28923, by rfl⟩) R57847
theorem R142679 : Reach 142679 := rs (se 1 (by rfl) ⟨107009, by rfl⟩) R214019
theorem R273779 : Reach 273779 := rs (se 1 (by rfl) ⟨205334, by rfl⟩) R410669
theorem R77243 : Reach 77243 := rs (se 1 (by rfl) ⟨57932, by rfl⟩) R115865
theorem R1420753 : Reach 1420753 := rs (se 2 (by rfl) ⟨532782, by rfl⟩) R1065565
theorem R77303 : Reach 77303 := rs (se 1 (by rfl) ⟨57977, by rfl⟩) R115955
theorem R77327 : Reach 77327 := rs (se 1 (by rfl) ⟨57995, by rfl⟩) R115991
theorem R77369 : Reach 77369 := rs (se 2 (by rfl) ⟨29013, by rfl⟩) R58027
theorem R77447 : Reach 77447 := rs (se 1 (by rfl) ⟨58085, by rfl⟩) R116171
theorem R77483 : Reach 77483 := rs (se 1 (by rfl) ⟨58112, by rfl⟩) R116225
theorem R77513 : Reach 77513 := rs (se 2 (by rfl) ⟨29067, by rfl⟩) R58135
theorem R77627 : Reach 77627 := rs (se 1 (by rfl) ⟨58220, by rfl⟩) R116441
theorem R175931 : Reach 175931 := rs (se 1 (by rfl) ⟨131948, by rfl⟩) R263897
theorem R274265 : Reach 274265 := rs (se 2 (by rfl) ⟨102849, by rfl⟩) R205699
theorem R77687 : Reach 77687 := rs (se 1 (by rfl) ⟨58265, by rfl⟩) R116531
theorem R77711 : Reach 77711 := rs (se 1 (by rfl) ⟨58283, by rfl⟩) R116567
theorem R307091 : Reach 307091 := rs (se 1 (by rfl) ⟨230318, by rfl⟩) R460637
theorem R77753 : Reach 77753 := rs (se 2 (by rfl) ⟨29157, by rfl⟩) R58315
theorem R77831 : Reach 77831 := rs (se 1 (by rfl) ⟨58373, by rfl⟩) R116747
theorem R77867 : Reach 77867 := rs (se 1 (by rfl) ⟨58400, by rfl⟩) R116801
theorem R77897 : Reach 77897 := rs (se 2 (by rfl) ⟨29211, by rfl⟩) R58423
theorem R602245 : Reach 602245 := rs (se 4 (by rfl) ⟨56460, by rfl⟩) R112921
theorem R143545 : Reach 143545 := rs (se 2 (by rfl) ⟨53829, by rfl⟩) R107659
theorem R78011 : Reach 78011 := rs (se 1 (by rfl) ⟨58508, by rfl⟩) R117017
theorem R78071 : Reach 78071 := rs (se 1 (by rfl) ⟨58553, by rfl⟩) R117107
theorem R78095 : Reach 78095 := rs (se 1 (by rfl) ⟨58571, by rfl⟩) R117143
theorem R176417 : Reach 176417 := rs (se 2 (by rfl) ⟨66156, by rfl⟩) R132313
theorem R78137 : Reach 78137 := rs (se 2 (by rfl) ⟨29301, by rfl⟩) R58603
theorem R110983 : Reach 110983 := rs (se 1 (by rfl) ⟨83237, by rfl⟩) R166475
theorem R78215 : Reach 78215 := rs (se 1 (by rfl) ⟨58661, by rfl⟩) R117323
theorem R78251 : Reach 78251 := rs (se 1 (by rfl) ⟨58688, by rfl⟩) R117377
theorem R78281 : Reach 78281 := rs (se 2 (by rfl) ⟨29355, by rfl⟩) R58711
theorem R78395 : Reach 78395 := rs (se 1 (by rfl) ⟨58796, by rfl⟩) R117593
theorem R307799 : Reach 307799 := rs (se 1 (by rfl) ⟨230849, by rfl⟩) R461699
theorem R78455 : Reach 78455 := rs (se 1 (by rfl) ⟨58841, by rfl⟩) R117683
theorem R78479 : Reach 78479 := rs (se 1 (by rfl) ⟨58859, by rfl⟩) R117719
theorem R78521 : Reach 78521 := rs (se 2 (by rfl) ⟨29445, by rfl⟩) R58891
theorem R78599 : Reach 78599 := rs (se 1 (by rfl) ⟨58949, by rfl⟩) R117899
theorem R275237 : Reach 275237 := rs (se 4 (by rfl) ⟨25803, by rfl⟩) R51607
theorem R78635 : Reach 78635 := rs (se 1 (by rfl) ⟨58976, by rfl⟩) R117953
theorem R78665 : Reach 78665 := rs (se 2 (by rfl) ⟨29499, by rfl⟩) R58999
theorem R177011 : Reach 177011 := rs (se 1 (by rfl) ⟨132758, by rfl⟩) R265517
theorem R78779 : Reach 78779 := rs (se 1 (by rfl) ⟨59084, by rfl⟩) R118169
theorem R78839 : Reach 78839 := rs (se 1 (by rfl) ⟨59129, by rfl⟩) R118259
theorem R78863 : Reach 78863 := rs (se 1 (by rfl) ⟨59147, by rfl⟩) R118295
theorem R78905 : Reach 78905 := rs (se 2 (by rfl) ⟨29589, by rfl⟩) R59179
theorem R78983 : Reach 78983 := rs (se 1 (by rfl) ⟨59237, by rfl⟩) R118475
theorem R79019 : Reach 79019 := rs (se 1 (by rfl) ⟨59264, by rfl⟩) R118529
theorem R79049 : Reach 79049 := rs (se 2 (by rfl) ⟨29643, by rfl⟩) R59287
theorem R79163 : Reach 79163 := rs (se 1 (by rfl) ⟨59372, by rfl⟩) R118745
theorem R79223 : Reach 79223 := rs (se 1 (by rfl) ⟨59417, by rfl⟩) R118835
theorem R79247 : Reach 79247 := rs (se 1 (by rfl) ⟨59435, by rfl⟩) R118871
theorem R1291697 : Reach 1291697 := rs (se 2 (by rfl) ⟨484386, by rfl⟩) R968773
theorem R79289 : Reach 79289 := rs (se 2 (by rfl) ⟨29733, by rfl⟩) R59467
theorem R308701 : Reach 308701 := rs (se 3 (by rfl) ⟨57881, by rfl⟩) R115763
theorem R79367 : Reach 79367 := rs (se 1 (by rfl) ⟨59525, by rfl⟩) R119051
theorem R79403 : Reach 79403 := rs (se 1 (by rfl) ⟨59552, by rfl⟩) R119105
theorem R112187 : Reach 112187 := rs (se 1 (by rfl) ⟨84140, by rfl⟩) R168281
theorem R79433 : Reach 79433 := rs (se 2 (by rfl) ⟨29787, by rfl⟩) R59575
theorem R79547 : Reach 79547 := rs (se 1 (by rfl) ⟨59660, by rfl⟩) R119321
theorem R79607 : Reach 79607 := rs (se 1 (by rfl) ⟨59705, by rfl⟩) R119411
theorem R79631 : Reach 79631 := rs (se 1 (by rfl) ⟨59723, by rfl⟩) R119447
theorem R79673 : Reach 79673 := rs (se 2 (by rfl) ⟨29877, by rfl⟩) R59755
theorem R79751 : Reach 79751 := rs (se 1 (by rfl) ⟨59813, by rfl⟩) R119627
theorem R276371 : Reach 276371 := rs (se 1 (by rfl) ⟨207278, by rfl⟩) R414557
theorem R79787 : Reach 79787 := rs (se 1 (by rfl) ⟨59840, by rfl⟩) R119681
theorem R79817 : Reach 79817 := rs (se 2 (by rfl) ⟨29931, by rfl⟩) R59863
theorem R112699 : Reach 112699 := rs (se 1 (by rfl) ⟨84524, by rfl⟩) R169049
theorem R79931 : Reach 79931 := rs (se 1 (by rfl) ⟨59948, by rfl⟩) R119897
theorem R79991 : Reach 79991 := rs (se 1 (by rfl) ⟨59993, by rfl⟩) R119987
theorem R80015 : Reach 80015 := rs (se 1 (by rfl) ⟨60011, by rfl⟩) R120023
theorem R80057 : Reach 80057 := rs (se 2 (by rfl) ⟨30021, by rfl⟩) R60043
theorem R407753 : Reach 407753 := rs (se 2 (by rfl) ⟨152907, by rfl⟩) R305815
theorem R80135 : Reach 80135 := rs (se 1 (by rfl) ⟨60101, by rfl⟩) R120203
theorem R80171 : Reach 80171 := rs (se 1 (by rfl) ⟨60128, by rfl⟩) R120257
theorem R80201 : Reach 80201 := rs (se 2 (by rfl) ⟨30075, by rfl⟩) R60151
theorem R309689 : Reach 309689 := rs (se 2 (by rfl) ⟨116133, by rfl⟩) R232267
theorem R80315 : Reach 80315 := rs (se 1 (by rfl) ⟨60236, by rfl⟩) R120473
theorem R80375 : Reach 80375 := rs (se 1 (by rfl) ⟨60281, by rfl⟩) R120563
theorem R80399 : Reach 80399 := rs (se 1 (by rfl) ⟨60299, by rfl⟩) R120599
theorem R80441 : Reach 80441 := rs (se 2 (by rfl) ⟨30165, by rfl⟩) R60331
theorem R80519 : Reach 80519 := rs (se 1 (by rfl) ⟨60389, by rfl⟩) R120779
theorem R80555 : Reach 80555 := rs (se 1 (by rfl) ⟨60416, by rfl⟩) R120833
theorem R80585 : Reach 80585 := rs (se 2 (by rfl) ⟨30219, by rfl⟩) R60439
theorem R441139 : Reach 441139 := rs (se 1 (by rfl) ⟨330854, by rfl⟩) R661709
theorem R80699 : Reach 80699 := rs (se 1 (by rfl) ⟨60524, by rfl⟩) R121049
theorem R80759 : Reach 80759 := rs (se 1 (by rfl) ⟨60569, by rfl⟩) R121139
theorem R80825 : Reach 80825 := rs (se 2 (by rfl) ⟨30309, by rfl⟩) R60619
theorem R146461 : Reach 146461 := rs (se 3 (by rfl) ⟨27461, by rfl⟩) R54923
theorem R80939 : Reach 80939 := rs (se 1 (by rfl) ⟨60704, by rfl⟩) R121409
theorem R146519 : Reach 146519 := rs (se 1 (by rfl) ⟨109889, by rfl⟩) R219779
theorem R343277 : Reach 343277 := rs (se 3 (by rfl) ⟨64364, by rfl⟩) R128729
theorem R81167 : Reach 81167 := rs (se 1 (by rfl) ⟨60875, by rfl⟩) R121751
theorem R834875 : Reach 834875 := rs (se 1 (by rfl) ⟨626156, by rfl⟩) R1252313
theorem R81287 : Reach 81287 := rs (se 1 (by rfl) ⟨60965, by rfl⟩) R121931
theorem R179603 : Reach 179603 := rs (se 1 (by rfl) ⟨134702, by rfl⟩) R269405
theorem R81353 : Reach 81353 := rs (se 2 (by rfl) ⟨30507, by rfl⟩) R61015
theorem R81467 : Reach 81467 := rs (se 1 (by rfl) ⟨61100, by rfl⟩) R122201
theorem R147005 : Reach 147005 := rs (se 3 (by rfl) ⟨27563, by rfl⟩) R55127
theorem R81527 : Reach 81527 := rs (se 1 (by rfl) ⟨61145, by rfl⟩) R122291
theorem R81593 : Reach 81593 := rs (se 2 (by rfl) ⟨30597, by rfl⟩) R61195
theorem R81707 : Reach 81707 := rs (se 1 (by rfl) ⟨61280, by rfl⟩) R122561
theorem R769945 : Reach 769945 := rs (se 2 (by rfl) ⟨288729, by rfl⟩) R577459
theorem R81935 : Reach 81935 := rs (se 1 (by rfl) ⟨61451, by rfl⟩) R122903
theorem R82055 : Reach 82055 := rs (se 1 (by rfl) ⟨61541, by rfl⟩) R123083
theorem R82121 : Reach 82121 := rs (se 2 (by rfl) ⟨30795, by rfl⟩) R61591
theorem R213229 : Reach 213229 := rs (se 3 (by rfl) ⟨39980, by rfl⟩) R79961
theorem R82235 : Reach 82235 := rs (se 1 (by rfl) ⟨61676, by rfl⟩) R123353
theorem R82295 : Reach 82295 := rs (se 1 (by rfl) ⟨61721, by rfl⟩) R123443
theorem R115091 : Reach 115091 := rs (se 1 (by rfl) ⟨86318, by rfl⟩) R172637
theorem R82361 : Reach 82361 := rs (se 2 (by rfl) ⟨30885, by rfl⟩) R61771
theorem R115145 : Reach 115145 := rs (se 2 (by rfl) ⟨43179, by rfl⟩) R86359
theorem R672299 : Reach 672299 := rs (se 1 (by rfl) ⟨504224, by rfl⟩) R1008449
theorem R82475 : Reach 82475 := rs (se 1 (by rfl) ⟨61856, by rfl⟩) R123713
theorem R148169 : Reach 148169 := rs (se 2 (by rfl) ⟨55563, by rfl⟩) R111127
theorem R181007 : Reach 181007 := rs (se 1 (by rfl) ⟨135755, by rfl⟩) R271511
theorem R82873 : Reach 82873 := rs (se 2 (by rfl) ⟨31077, by rfl⟩) R62155
theorem R3195875 : Reach 3195875 := rs (se 1 (by rfl) ⟨2396906, by rfl⟩) R4793813
theorem R181277 : Reach 181277 := rs (se 3 (by rfl) ⟨33989, by rfl⟩) R67979
theorem R115847 : Reach 115847 := rs (se 1 (by rfl) ⟨86885, by rfl⟩) R173771
theorem R116027 : Reach 116027 := rs (se 1 (by rfl) ⟨87020, by rfl⟩) R174041
theorem R116153 : Reach 116153 := rs (se 2 (by rfl) ⟨43557, by rfl⟩) R87115
theorem R149035 : Reach 149035 := rs (se 1 (by rfl) ⟨111776, by rfl⟩) R223553
theorem R116495 : Reach 116495 := rs (se 1 (by rfl) ⟨87371, by rfl⟩) R174743
theorem R116513 : Reach 116513 := rs (se 2 (by rfl) ⟨43692, by rfl⟩) R87385
theorem R149309 : Reach 149309 := rs (se 3 (by rfl) ⟨27995, by rfl⟩) R55991
theorem R51131 : Reach 51131 := rs (se 1 (by rfl) ⟨38348, by rfl⟩) R76697
theorem R51207 : Reach 51207 := rs (se 1 (by rfl) ⟨38405, by rfl⟩) R76811
theorem R51215 : Reach 51215 := rs (se 1 (by rfl) ⟨38411, by rfl⟩) R76823
theorem R51259 : Reach 51259 := rs (se 1 (by rfl) ⟨38444, by rfl⟩) R76889
theorem R280637 : Reach 280637 := rs (se 3 (by rfl) ⟨52619, by rfl⟩) R105239
theorem R116855 : Reach 116855 := rs (se 1 (by rfl) ⟨87641, by rfl⟩) R175283
theorem R51335 : Reach 51335 := rs (se 1 (by rfl) ⟨38501, by rfl⟩) R77003
theorem R51343 : Reach 51343 := rs (se 1 (by rfl) ⟨38507, by rfl⟩) R77015
theorem R149651 : Reach 149651 := rs (se 1 (by rfl) ⟨112238, by rfl⟩) R224477
theorem R247981 : Reach 247981 := rs (se 3 (by rfl) ⟨46496, by rfl⟩) R92993
theorem R51387 : Reach 51387 := rs (se 1 (by rfl) ⟨38540, by rfl⟩) R77081
theorem R51463 : Reach 51463 := rs (se 1 (by rfl) ⟨38597, by rfl⟩) R77195
theorem R51471 : Reach 51471 := rs (se 1 (by rfl) ⟨38603, by rfl⟩) R77207
theorem R117035 : Reach 117035 := rs (se 1 (by rfl) ⟨87776, by rfl⟩) R175553
theorem R51515 : Reach 51515 := rs (se 1 (by rfl) ⟨38636, by rfl⟩) R77273
theorem R51591 : Reach 51591 := rs (se 1 (by rfl) ⟨38693, by rfl⟩) R77387
theorem R51599 : Reach 51599 := rs (se 1 (by rfl) ⟨38699, by rfl⟩) R77399
theorem R182681 : Reach 182681 := rs (se 2 (by rfl) ⟨68505, by rfl⟩) R137011
theorem R51643 : Reach 51643 := rs (se 1 (by rfl) ⟨38732, by rfl⟩) R77465
theorem R51719 : Reach 51719 := rs (se 1 (by rfl) ⟨38789, by rfl⟩) R77579
theorem R51727 : Reach 51727 := rs (se 1 (by rfl) ⟨38795, by rfl⟩) R77591
theorem R51771 : Reach 51771 := rs (se 1 (by rfl) ⟨38828, by rfl⟩) R77657
theorem R51847 : Reach 51847 := rs (se 1 (by rfl) ⟨38885, by rfl⟩) R77771
theorem R51855 : Reach 51855 := rs (se 1 (by rfl) ⟨38891, by rfl⟩) R77783
theorem R117395 : Reach 117395 := rs (se 1 (by rfl) ⟨88046, by rfl⟩) R176093
theorem R51899 : Reach 51899 := rs (se 1 (by rfl) ⟨38924, by rfl⟩) R77849
theorem R117449 : Reach 117449 := rs (se 2 (by rfl) ⟨44043, by rfl⟩) R88087
theorem R51975 : Reach 51975 := rs (se 1 (by rfl) ⟨38981, by rfl⟩) R77963
theorem R51983 : Reach 51983 := rs (se 1 (by rfl) ⟨38987, by rfl⟩) R77975
theorem R281377 : Reach 281377 := rs (se 2 (by rfl) ⟨105516, by rfl⟩) R211033
theorem R52027 : Reach 52027 := rs (se 1 (by rfl) ⟨39020, by rfl⟩) R78041
theorem R52103 : Reach 52103 := rs (se 1 (by rfl) ⟨39077, by rfl⟩) R78155
theorem R52111 : Reach 52111 := rs (se 1 (by rfl) ⟨39083, by rfl⟩) R78167
theorem R52155 : Reach 52155 := rs (se 1 (by rfl) ⟨39116, by rfl⟩) R78233
theorem R52231 : Reach 52231 := rs (se 1 (by rfl) ⟨39173, by rfl⟩) R78347
theorem R52239 : Reach 52239 := rs (se 1 (by rfl) ⟨39179, by rfl⟩) R78359
theorem R52283 : Reach 52283 := rs (se 1 (by rfl) ⟨39212, by rfl⟩) R78425
theorem R805949 : Reach 805949 := rs (se 3 (by rfl) ⟨151115, by rfl⟩) R302231
theorem R183383 : Reach 183383 := rs (se 1 (by rfl) ⟨137537, by rfl⟩) R275075
theorem R52359 : Reach 52359 := rs (se 1 (by rfl) ⟨39269, by rfl⟩) R78539
theorem R52367 : Reach 52367 := rs (se 1 (by rfl) ⟨39275, by rfl⟩) R78551
theorem R52411 : Reach 52411 := rs (se 1 (by rfl) ⟨39308, by rfl⟩) R78617
theorem R52487 : Reach 52487 := rs (se 1 (by rfl) ⟨39365, by rfl⟩) R78731
theorem R52495 : Reach 52495 := rs (se 1 (by rfl) ⟨39371, by rfl⟩) R78743
theorem R52539 : Reach 52539 := rs (se 1 (by rfl) ⟨39404, by rfl⟩) R78809
theorem R118151 : Reach 118151 := rs (se 1 (by rfl) ⟨88613, by rfl⟩) R177227
theorem R52615 : Reach 52615 := rs (se 1 (by rfl) ⟨39461, by rfl⟩) R78923
theorem R52623 : Reach 52623 := rs (se 1 (by rfl) ⟨39467, by rfl⟩) R78935
theorem R52667 : Reach 52667 := rs (se 1 (by rfl) ⟨39500, by rfl⟩) R79001
theorem R183761 : Reach 183761 := rs (se 2 (by rfl) ⟨68910, by rfl⟩) R137821
theorem R52743 : Reach 52743 := rs (se 1 (by rfl) ⟨39557, by rfl⟩) R79115
theorem R52751 : Reach 52751 := rs (se 1 (by rfl) ⟨39563, by rfl⟩) R79127
theorem R118331 : Reach 118331 := rs (se 1 (by rfl) ⟨88748, by rfl⟩) R177497
theorem R52795 : Reach 52795 := rs (se 1 (by rfl) ⟨39596, by rfl⟩) R79193
theorem R183869 : Reach 183869 := rs (se 3 (by rfl) ⟨34475, by rfl⟩) R68951
theorem R52871 : Reach 52871 := rs (se 1 (by rfl) ⟨39653, by rfl⟩) R79307
theorem R52879 : Reach 52879 := rs (se 1 (by rfl) ⟨39659, by rfl⟩) R79319
theorem R118457 : Reach 118457 := rs (se 2 (by rfl) ⟨44421, by rfl⟩) R88843
theorem R52923 : Reach 52923 := rs (se 1 (by rfl) ⟨39692, by rfl⟩) R79385
theorem R249601 : Reach 249601 := rs (se 2 (by rfl) ⟨93600, by rfl⟩) R187201
theorem R52999 : Reach 52999 := rs (se 1 (by rfl) ⟨39749, by rfl⟩) R79499
theorem R53007 : Reach 53007 := rs (se 1 (by rfl) ⟨39755, by rfl⟩) R79511
theorem R53051 : Reach 53051 := rs (se 1 (by rfl) ⟨39788, by rfl⟩) R79577
theorem R282503 : Reach 282503 := rs (se 1 (by rfl) ⟨211877, by rfl⟩) R423755
theorem R53127 : Reach 53127 := rs (se 1 (by rfl) ⟨39845, by rfl⟩) R79691
theorem R53135 : Reach 53135 := rs (se 1 (by rfl) ⟨39851, by rfl⟩) R79703
theorem R511895 : Reach 511895 := rs (se 1 (by rfl) ⟨383921, by rfl⟩) R767843
theorem R53179 : Reach 53179 := rs (se 1 (by rfl) ⟨39884, by rfl⟩) R79769
theorem R53255 : Reach 53255 := rs (se 1 (by rfl) ⟨39941, by rfl⟩) R79883
theorem R118799 : Reach 118799 := rs (se 1 (by rfl) ⟨89099, by rfl⟩) R178199
theorem R53263 : Reach 53263 := rs (se 1 (by rfl) ⟨39947, by rfl⟩) R79895
theorem R118817 : Reach 118817 := rs (se 2 (by rfl) ⟨44556, by rfl⟩) R89113
theorem R53307 : Reach 53307 := rs (se 1 (by rfl) ⟨39980, by rfl⟩) R79961
theorem R53383 : Reach 53383 := rs (se 1 (by rfl) ⟨40037, by rfl⟩) R80075
theorem R53391 : Reach 53391 := rs (se 1 (by rfl) ⟨40043, by rfl⟩) R80087
theorem R53435 : Reach 53435 := rs (se 1 (by rfl) ⟨40076, by rfl⟩) R80153
theorem R905417 : Reach 905417 := rs (se 2 (by rfl) ⟨339531, by rfl⟩) R679063
theorem R53511 : Reach 53511 := rs (se 1 (by rfl) ⟨40133, by rfl⟩) R80267
theorem R53519 : Reach 53519 := rs (se 1 (by rfl) ⟨40139, by rfl⟩) R80279
theorem R53563 : Reach 53563 := rs (se 1 (by rfl) ⟨40172, by rfl⟩) R80345
theorem R151895 : Reach 151895 := rs (se 1 (by rfl) ⟨113921, by rfl⟩) R227843
theorem R119159 : Reach 119159 := rs (se 1 (by rfl) ⟨89369, by rfl⟩) R178739
theorem R53639 : Reach 53639 := rs (se 1 (by rfl) ⟨40229, by rfl⟩) R80459
theorem R53647 : Reach 53647 := rs (se 1 (by rfl) ⟨40235, by rfl⟩) R80471
theorem R53691 : Reach 53691 := rs (se 1 (by rfl) ⟨40268, by rfl⟩) R80537
theorem R53767 : Reach 53767 := rs (se 1 (by rfl) ⟨40325, by rfl⟩) R80651
theorem R53775 : Reach 53775 := rs (se 1 (by rfl) ⟨40331, by rfl⟩) R80663
theorem R119339 : Reach 119339 := rs (se 1 (by rfl) ⟨89504, by rfl⟩) R179009
theorem R53819 : Reach 53819 := rs (se 1 (by rfl) ⟨40364, by rfl⟩) R80729
theorem R86663 : Reach 86663 := rs (se 1 (by rfl) ⟨64997, by rfl⟩) R129995
theorem R53895 : Reach 53895 := rs (se 1 (by rfl) ⟨40421, by rfl⟩) R80843
theorem R53903 : Reach 53903 := rs (se 1 (by rfl) ⟨40427, by rfl⟩) R80855
theorem R53947 : Reach 53947 := rs (se 1 (by rfl) ⟨40460, by rfl⟩) R80921
theorem R54023 : Reach 54023 := rs (se 1 (by rfl) ⟨40517, by rfl⟩) R81035
theorem R54031 : Reach 54031 := rs (se 1 (by rfl) ⟨40523, by rfl⟩) R81047
theorem R54075 : Reach 54075 := rs (se 1 (by rfl) ⟨40556, by rfl⟩) R81113
theorem R316295 : Reach 316295 := rs (se 1 (by rfl) ⟨237221, by rfl⟩) R474443
theorem R54151 : Reach 54151 := rs (se 1 (by rfl) ⟨40613, by rfl⟩) R81227
theorem R54159 : Reach 54159 := rs (se 1 (by rfl) ⟨40619, by rfl⟩) R81239
theorem R119699 : Reach 119699 := rs (se 1 (by rfl) ⟨89774, by rfl⟩) R179549
theorem R185273 : Reach 185273 := rs (se 2 (by rfl) ⟨69477, by rfl⟩) R138955
theorem R54203 : Reach 54203 := rs (se 1 (by rfl) ⟨40652, by rfl⟩) R81305
theorem R119753 : Reach 119753 := rs (se 2 (by rfl) ⟨44907, by rfl⟩) R89815
theorem R250883 : Reach 250883 := rs (se 1 (by rfl) ⟨188162, by rfl⟩) R376325
theorem R54279 : Reach 54279 := rs (se 1 (by rfl) ⟨40709, by rfl⟩) R81419
theorem R54287 : Reach 54287 := rs (se 1 (by rfl) ⟨40715, by rfl⟩) R81431
theorem R54331 : Reach 54331 := rs (se 1 (by rfl) ⟨40748, by rfl⟩) R81497
theorem R54407 : Reach 54407 := rs (se 1 (by rfl) ⟨40805, by rfl⟩) R81611
theorem R54415 : Reach 54415 := rs (se 1 (by rfl) ⟨40811, by rfl⟩) R81623
theorem R54459 : Reach 54459 := rs (se 1 (by rfl) ⟨40844, by rfl⟩) R81689
theorem R87241 : Reach 87241 := rs (se 2 (by rfl) ⟨32715, by rfl⟩) R65431
theorem R54535 : Reach 54535 := rs (se 1 (by rfl) ⟨40901, by rfl⟩) R81803
theorem R87311 : Reach 87311 := rs (se 1 (by rfl) ⟨65483, by rfl⟩) R130967
theorem R54543 : Reach 54543 := rs (se 1 (by rfl) ⟨40907, by rfl⟩) R81815
theorem R54587 : Reach 54587 := rs (se 1 (by rfl) ⟨40940, by rfl⟩) R81881
theorem R54663 : Reach 54663 := rs (se 1 (by rfl) ⟨40997, by rfl⟩) R81995
theorem R54671 : Reach 54671 := rs (se 1 (by rfl) ⟨41003, by rfl⟩) R82007
theorem R54715 : Reach 54715 := rs (se 1 (by rfl) ⟨41036, by rfl⟩) R82073
theorem R54791 : Reach 54791 := rs (se 1 (by rfl) ⟨41093, by rfl⟩) R82187
theorem R185867 : Reach 185867 := rs (se 1 (by rfl) ⟨139400, by rfl⟩) R278801
theorem R54799 : Reach 54799 := rs (se 1 (by rfl) ⟨41099, by rfl⟩) R82199
theorem R54843 : Reach 54843 := rs (se 1 (by rfl) ⟨41132, by rfl⟩) R82265
theorem R185975 : Reach 185975 := rs (se 1 (by rfl) ⟨139481, by rfl⟩) R278963
theorem R120455 : Reach 120455 := rs (se 1 (by rfl) ⟨90341, by rfl⟩) R180683
theorem R54919 : Reach 54919 := rs (se 1 (by rfl) ⟨41189, by rfl⟩) R82379
theorem R54927 : Reach 54927 := rs (se 1 (by rfl) ⟨41195, by rfl⟩) R82391
theorem R54971 : Reach 54971 := rs (se 1 (by rfl) ⟨41228, by rfl⟩) R82457
theorem R55047 : Reach 55047 := rs (se 1 (by rfl) ⟨41285, by rfl⟩) R82571
theorem R55055 : Reach 55055 := rs (se 1 (by rfl) ⟨41291, by rfl⟩) R82583
theorem R87851 : Reach 87851 := rs (se 1 (by rfl) ⟨65888, by rfl⟩) R131777
theorem R120635 : Reach 120635 := rs (se 1 (by rfl) ⟨90476, by rfl⟩) R180953
theorem R55099 : Reach 55099 := rs (se 1 (by rfl) ⟨41324, by rfl⟩) R82649
theorem R350041 : Reach 350041 := rs (se 2 (by rfl) ⟨131265, by rfl⟩) R262531
theorem R55175 : Reach 55175 := rs (se 1 (by rfl) ⟨41381, by rfl⟩) R82763
theorem R120761 : Reach 120761 := rs (se 2 (by rfl) ⟨45285, by rfl⟩) R90571
theorem R219179 : Reach 219179 := rs (se 1 (by rfl) ⟨164384, by rfl⟩) R328769
theorem R88249 : Reach 88249 := rs (se 2 (by rfl) ⟨33093, by rfl⟩) R66187
theorem R121103 : Reach 121103 := rs (se 1 (by rfl) ⟨90827, by rfl⟩) R181655
theorem R121121 : Reach 121121 := rs (se 2 (by rfl) ⟨45420, by rfl⟩) R90841
theorem R121175 : Reach 121175 := rs (se 1 (by rfl) ⟨90881, by rfl⟩) R181763
theorem R514451 : Reach 514451 := rs (se 1 (by rfl) ⟨385838, by rfl⟩) R771677
theorem R121355 : Reach 121355 := rs (se 1 (by rfl) ⟨91016, by rfl⟩) R182033
theorem R121463 : Reach 121463 := rs (se 1 (by rfl) ⟨91097, by rfl⟩) R182195
theorem R121643 : Reach 121643 := rs (se 1 (by rfl) ⟨91232, by rfl⟩) R182465
theorem R121715 : Reach 121715 := rs (se 1 (by rfl) ⟨91286, by rfl⟩) R182573
theorem R88951 : Reach 88951 := rs (se 1 (by rfl) ⟨66713, by rfl⟩) R133427
theorem R154639 : Reach 154639 := rs (se 1 (by rfl) ⟨115979, by rfl⟩) R231959
theorem R89147 : Reach 89147 := rs (se 1 (by rfl) ⟨66860, by rfl⟩) R133721
theorem R154685 : Reach 154685 := rs (se 3 (by rfl) ⟨29003, by rfl⟩) R58007
theorem R121991 : Reach 121991 := rs (se 1 (by rfl) ⟨91493, by rfl⟩) R182987
theorem R122003 : Reach 122003 := rs (se 1 (by rfl) ⟨91502, by rfl⟩) R183005
theorem R122057 : Reach 122057 := rs (se 2 (by rfl) ⟨45771, by rfl⟩) R91543
theorem R351469 : Reach 351469 := rs (se 3 (by rfl) ⟨65900, by rfl⟩) R131801
theorem R155027 : Reach 155027 := rs (se 1 (by rfl) ⟨116270, by rfl⟩) R232541
theorem R613817 : Reach 613817 := rs (se 2 (by rfl) ⟨230181, by rfl⟩) R460363
theorem R89545 : Reach 89545 := rs (se 2 (by rfl) ⟨33579, by rfl⟩) R67159
theorem R679427 : Reach 679427 := rs (se 1 (by rfl) ⟨509570, by rfl⟩) R1019141
theorem R745037 : Reach 745037 := rs (se 3 (by rfl) ⟨139694, by rfl⟩) R279389
theorem R417473 : Reach 417473 := rs (se 2 (by rfl) ⟨156552, by rfl⟩) R313105
theorem R319177 : Reach 319177 := rs (se 2 (by rfl) ⟨119691, by rfl⟩) R239383
theorem R122759 : Reach 122759 := rs (se 1 (by rfl) ⟨92069, by rfl⟩) R184139
theorem R122777 : Reach 122777 := rs (se 2 (by rfl) ⟨46041, by rfl⟩) R92083
theorem R122939 : Reach 122939 := rs (se 1 (by rfl) ⟨92204, by rfl⟩) R184409
theorem R90247 : Reach 90247 := rs (se 1 (by rfl) ⟨67685, by rfl⟩) R135371
theorem R123065 : Reach 123065 := rs (se 2 (by rfl) ⟨46149, by rfl⟩) R92299
theorem R123137 : Reach 123137 := rs (se 2 (by rfl) ⟨46176, by rfl⟩) R92353
theorem R155915 : Reach 155915 := rs (se 1 (by rfl) ⟨116936, by rfl⟩) R233873
theorem R942353 : Reach 942353 := rs (se 2 (by rfl) ⟨353382, by rfl⟩) R706765
theorem R221555 : Reach 221555 := rs (se 1 (by rfl) ⟨166166, by rfl⟩) R332333
theorem R451001 : Reach 451001 := rs (se 2 (by rfl) ⟨169125, by rfl⟩) R338251
theorem R221707 : Reach 221707 := rs (se 1 (by rfl) ⟨166280, by rfl⟩) R332561
theorem R123407 : Reach 123407 := rs (se 1 (by rfl) ⟨92555, by rfl⟩) R185111
theorem R123425 : Reach 123425 := rs (se 2 (by rfl) ⟨46284, by rfl⟩) R92569
theorem R123479 : Reach 123479 := rs (se 1 (by rfl) ⟨92609, by rfl⟩) R185219
theorem R57991 : Reach 57991 := rs (se 1 (by rfl) ⟨43493, by rfl⟩) R86987
theorem R123659 : Reach 123659 := rs (se 1 (by rfl) ⟨92744, by rfl⟩) R185489
theorem R90895 : Reach 90895 := rs (se 1 (by rfl) ⟨68171, by rfl⟩) R136343
theorem R58171 : Reach 58171 := rs (se 1 (by rfl) ⟨43628, by rfl⟩) R87257
theorem R320345 : Reach 320345 := rs (se 2 (by rfl) ⟨120129, by rfl⟩) R240259
theorem R123767 : Reach 123767 := rs (se 1 (by rfl) ⟨92825, by rfl⟩) R185651
theorem R123947 : Reach 123947 := rs (se 1 (by rfl) ⟨92960, by rfl⟩) R185921
theorem R124019 : Reach 124019 := rs (se 1 (by rfl) ⟨93014, by rfl⟩) R186029
theorem R255095 : Reach 255095 := rs (se 1 (by rfl) ⟨191321, by rfl⟩) R382643
theorem R58639 : Reach 58639 := rs (se 1 (by rfl) ⟨43979, by rfl⟩) R87959
theorem R124193 : Reach 124193 := rs (se 2 (by rfl) ⟨46572, by rfl⟩) R93145
theorem R91435 : Reach 91435 := rs (se 1 (by rfl) ⟨68576, by rfl⟩) R137153
theorem R3433859 : Reach 3433859 := rs (se 1 (by rfl) ⟨2575394, by rfl⟩) R5150789
theorem R91577 : Reach 91577 := rs (se 2 (by rfl) ⟨34341, by rfl⟩) R68683
theorem R91795 : Reach 91795 := rs (se 1 (by rfl) ⟨68846, by rfl⟩) R137693
theorem R59143 : Reach 59143 := rs (se 1 (by rfl) ⟨44357, by rfl⟩) R88715
theorem R59323 : Reach 59323 := rs (se 1 (by rfl) ⟨44492, by rfl⟩) R88985
theorem R92279 : Reach 92279 := rs (se 1 (by rfl) ⟨69209, by rfl⟩) R138419
theorem R223469 : Reach 223469 := rs (se 3 (by rfl) ⟨41900, by rfl⟩) R83801
theorem R92431 : Reach 92431 := rs (se 1 (by rfl) ⟨69323, by rfl⟩) R138647
theorem R59791 : Reach 59791 := rs (se 1 (by rfl) ⟨44843, by rfl⟩) R89687
theorem R92731 : Reach 92731 := rs (se 1 (by rfl) ⟨69548, by rfl⟩) R139097
theorem R92819 : Reach 92819 := rs (se 1 (by rfl) ⟨69614, by rfl⟩) R139229
theorem R92873 : Reach 92873 := rs (se 2 (by rfl) ⟨34827, by rfl⟩) R69655
theorem R256801 : Reach 256801 := rs (se 2 (by rfl) ⟨96300, by rfl⟩) R192601
theorem R158507 : Reach 158507 := rs (se 1 (by rfl) ⟨118880, by rfl⟩) R237761
theorem R289595 : Reach 289595 := rs (se 1 (by rfl) ⟨217196, by rfl⟩) R434393
theorem R518987 : Reach 518987 := rs (se 1 (by rfl) ⟨389240, by rfl⟩) R778481
theorem R60295 : Reach 60295 := rs (se 1 (by rfl) ⟨45221, by rfl⟩) R90443
theorem R224153 : Reach 224153 := rs (se 2 (by rfl) ⟨84057, by rfl⟩) R168115
theorem R257053 : Reach 257053 := rs (se 3 (by rfl) ⟨48197, by rfl⟩) R96395
theorem R60475 : Reach 60475 := rs (se 1 (by rfl) ⟨45356, by rfl⟩) R90713
theorem R1404053 : Reach 1404053 := rs (se 6 (by rfl) ⟨32907, by rfl⟩) R65815
theorem R126479 : Reach 126479 := rs (se 1 (by rfl) ⟨94859, by rfl⟩) R189719
theorem R60943 : Reach 60943 := rs (se 1 (by rfl) ⟨45707, by rfl⟩) R91415
theorem R290575 : Reach 290575 := rs (se 1 (by rfl) ⟨217931, by rfl⟩) R435863
theorem R61303 : Reach 61303 := rs (se 1 (by rfl) ⟨45977, by rfl⟩) R91955
theorem R61447 : Reach 61447 := rs (se 1 (by rfl) ⟨46085, by rfl⟩) R92171
theorem R61483 : Reach 61483 := rs (se 1 (by rfl) ⟨46112, by rfl⟩) R92225
theorem R61627 : Reach 61627 := rs (se 1 (by rfl) ⟨46220, by rfl⟩) R92441
theorem R586115 : Reach 586115 := rs (se 1 (by rfl) ⟨439586, by rfl⟩) R879173
theorem R291275 : Reach 291275 := rs (se 1 (by rfl) ⟨218456, by rfl⟩) R436913
theorem R226081 : Reach 226081 := rs (se 2 (by rfl) ⟨84780, by rfl⟩) R169561
theorem R848677 : Reach 848677 := rs (se 4 (by rfl) ⟨79563, by rfl⟩) R159127
theorem R258875 : Reach 258875 := rs (se 1 (by rfl) ⟨194156, by rfl⟩) R388313
theorem R62327 : Reach 62327 := rs (se 1 (by rfl) ⟨46745, by rfl⟩) R93491
theorem R259037 : Reach 259037 := rs (se 3 (by rfl) ⟨48569, by rfl⟩) R97139
theorem R62471 : Reach 62471 := rs (se 1 (by rfl) ⟨46853, by rfl⟩) R93707
theorem R62635 : Reach 62635 := rs (se 1 (by rfl) ⟨46976, by rfl⟩) R93953
theorem R259361 : Reach 259361 := rs (se 2 (by rfl) ⟨97260, by rfl⟩) R194521
theorem R1209659 : Reach 1209659 := rs (se 1 (by rfl) ⟨907244, by rfl⟩) R1814489
theorem R128441 : Reach 128441 := rs (se 2 (by rfl) ⟨48165, by rfl⟩) R96331
theorem R63019 : Reach 63019 := rs (se 1 (by rfl) ⟨47264, by rfl⟩) R94529
theorem R128555 : Reach 128555 := rs (se 1 (by rfl) ⟨96416, by rfl⟩) R192833
theorem R194363 : Reach 194363 := rs (se 1 (by rfl) ⟨145772, by rfl⟩) R291545
theorem R325579 : Reach 325579 := rs (se 1 (by rfl) ⟨244184, by rfl⟩) R488369
theorem R423883 : Reach 423883 := rs (se 1 (by rfl) ⟨317912, by rfl⟩) R635825
theorem R63547 : Reach 63547 := rs (se 1 (by rfl) ⟨47660, by rfl⟩) R95321
theorem R391229 : Reach 391229 := rs (se 3 (by rfl) ⟨73355, by rfl⟩) R146711
theorem R260333 : Reach 260333 := rs (se 3 (by rfl) ⟨48812, by rfl⟩) R97625
theorem R391405 : Reach 391405 := rs (se 3 (by rfl) ⟨73388, by rfl⟩) R146777
theorem R227585 : Reach 227585 := rs (se 2 (by rfl) ⟨85344, by rfl⟩) R170689
theorem R195139 : Reach 195139 := rs (se 1 (by rfl) ⟨146354, by rfl⟩) R292709
theorem R227927 : Reach 227927 := rs (se 1 (by rfl) ⟨170945, by rfl⟩) R341891
theorem R129671 : Reach 129671 := rs (se 1 (by rfl) ⟨97253, by rfl⟩) R194507
theorem R129721 : Reach 129721 := rs (se 2 (by rfl) ⟨48645, by rfl⟩) R97291
theorem R228041 : Reach 228041 := rs (se 2 (by rfl) ⟨85515, by rfl⟩) R171031
theorem R261143 : Reach 261143 := rs (se 1 (by rfl) ⟨195857, by rfl⟩) R391715
theorem R130319 : Reach 130319 := rs (se 1 (by rfl) ⟨97739, by rfl⟩) R195479
theorem R97595 : Reach 97595 := rs (se 1 (by rfl) ⟨73196, by rfl⟩) R146393
theorem R98081 : Reach 98081 := rs (se 2 (by rfl) ⟨36780, by rfl⟩) R73561
theorem R130859 : Reach 130859 := rs (se 1 (by rfl) ⟨98144, by rfl⟩) R196289
theorem R131017 : Reach 131017 := rs (se 2 (by rfl) ⟨49131, by rfl⟩) R98263
theorem R131129 : Reach 131129 := rs (se 2 (by rfl) ⟨49173, by rfl⟩) R98347
theorem R196951 : Reach 196951 := rs (se 1 (by rfl) ⟨147713, by rfl⟩) R295427
theorem R197255 : Reach 197255 := rs (se 1 (by rfl) ⟨147941, by rfl⟩) R295883
theorem R2130583 : Reach 2130583 := rs (se 1 (by rfl) ⟨1597937, by rfl⟩) R3195875
theorem R295609 : Reach 295609 := rs (se 2 (by rfl) ⟨110853, by rfl⟩) R221707
theorem R3211973 : Reach 3211973 := rs (se 4 (by rfl) ⟨301122, by rfl⟩) R602245
theorem R263087 : Reach 263087 := rs (se 1 (by rfl) ⟨197315, by rfl⟩) R394631
theorem R590915 : Reach 590915 := rs (se 1 (by rfl) ⟨443186, by rfl⟩) R886373
theorem R197711 : Reach 197711 := rs (se 1 (by rfl) ⟨148283, by rfl⟩) R296567
theorem R66683 : Reach 66683 := rs (se 1 (by rfl) ⟨50012, by rfl⟩) R100025
theorem R99539 : Reach 99539 := rs (se 1 (by rfl) ⟨74654, by rfl⟩) R149309
theorem R492965 : Reach 492965 := rs (se 4 (by rfl) ⟨46215, by rfl⟩) R92431
theorem R99767 : Reach 99767 := rs (se 1 (by rfl) ⟨74825, by rfl⟩) R149651
theorem R132617 : Reach 132617 := rs (se 2 (by rfl) ⟨49731, by rfl⟩) R99463
theorem R198283 : Reach 198283 := rs (se 1 (by rfl) ⟨148712, by rfl⟩) R297425
theorem R395117 : Reach 395117 := rs (se 3 (by rfl) ⟨74084, by rfl⟩) R148169
theorem R198713 : Reach 198713 := rs (se 2 (by rfl) ⟨74517, by rfl⟩) R149035
theorem R166205 : Reach 166205 := rs (se 3 (by rfl) ⟨31163, by rfl⟩) R62327
theorem R100921 : Reach 100921 := rs (se 2 (by rfl) ⟨37845, by rfl⟩) R75691
theorem R133771 : Reach 133771 := rs (se 1 (by rfl) ⟨100328, by rfl⟩) R200657
theorem R166589 : Reach 166589 := rs (se 3 (by rfl) ⟨31235, by rfl⟩) R62471
theorem R199367 : Reach 199367 := rs (se 1 (by rfl) ⟨149525, by rfl⟩) R299051
theorem R101225 : Reach 101225 := rs (se 2 (by rfl) ⟨37959, by rfl⟩) R75919
theorem R101263 : Reach 101263 := rs (se 1 (by rfl) ⟨75947, by rfl⟩) R151895
theorem R330641 : Reach 330641 := rs (se 2 (by rfl) ⟨123990, by rfl⟩) R247981
theorem R134075 : Reach 134075 := rs (se 1 (by rfl) ⟨100556, by rfl⟩) R201113
theorem R68617 : Reach 68617 := rs (se 2 (by rfl) ⟨25731, by rfl⟩) R51463
theorem R167255 : Reach 167255 := rs (se 1 (by rfl) ⟨125441, by rfl⟩) R250883
theorem R855539 : Reach 855539 := rs (se 1 (by rfl) ⟨641654, by rfl⟩) R1283309
theorem R200339 : Reach 200339 := rs (se 1 (by rfl) ⟨150254, by rfl⟩) R300509
theorem R134855 : Reach 134855 := rs (se 1 (by rfl) ⟨101141, by rfl⟩) R202283
theorem R265943 : Reach 265943 := rs (se 1 (by rfl) ⟨199457, by rfl⟩) R398915
theorem R134905 : Reach 134905 := rs (se 2 (by rfl) ⟨50589, by rfl⟩) R101179
theorem R135553 : Reach 135553 := rs (se 2 (by rfl) ⟨50832, by rfl⟩) R101665
theorem R398033 : Reach 398033 := rs (se 2 (by rfl) ⟨149262, by rfl⟩) R298525
theorem R103123 : Reach 103123 := rs (se 1 (by rfl) ⟨77342, by rfl⟩) R154685
theorem R594863 : Reach 594863 := rs (se 1 (by rfl) ⟨446147, by rfl⟩) R892295
theorem R103351 : Reach 103351 := rs (se 1 (by rfl) ⟨77513, by rfl⟩) R155027
theorem R332801 : Reach 332801 := rs (se 2 (by rfl) ⟨124800, by rfl⟩) R249601
theorem R332819 : Reach 332819 := rs (se 1 (by rfl) ⟨249614, by rfl⟩) R499229
theorem R496691 : Reach 496691 := rs (se 1 (by rfl) ⟨372518, by rfl⟩) R745037
theorem R136363 : Reach 136363 := rs (se 1 (by rfl) ⟨102272, by rfl⟩) R204545
theorem R136667 : Reach 136667 := rs (se 1 (by rfl) ⟨102500, by rfl⟩) R205001
theorem R2299355 : Reach 2299355 := rs (se 1 (by rfl) ⟨1724516, by rfl⟩) R3449033
theorem R103943 : Reach 103943 := rs (se 1 (by rfl) ⟨77957, by rfl⟩) R155915
theorem R628235 : Reach 628235 := rs (se 1 (by rfl) ⟨471176, by rfl⟩) R942353
theorem R398945 : Reach 398945 := rs (se 2 (by rfl) ⟨149604, by rfl⟩) R299209
theorem R300667 : Reach 300667 := rs (se 1 (by rfl) ⟨225500, by rfl⟩) R451001
theorem R71599 : Reach 71599 := rs (se 1 (by rfl) ⟨53699, by rfl⟩) R107399
theorem R333827 : Reach 333827 := rs (se 1 (by rfl) ⟨250370, by rfl⟩) R500741
theorem R170063 : Reach 170063 := rs (se 1 (by rfl) ⟨127547, by rfl⟩) R255095
theorem R301441 : Reach 301441 := rs (se 2 (by rfl) ⟨113040, by rfl⟩) R226081
theorem R1874501 : Reach 1874501 := rs (se 4 (by rfl) ⟨175734, by rfl⟩) R351469
theorem R793273 : Reach 793273 := rs (se 2 (by rfl) ⟨297477, by rfl⟩) R594955
theorem R138145 : Reach 138145 := rs (se 2 (by rfl) ⟨51804, by rfl⟩) R103609
theorem R597071 : Reach 597071 := rs (se 1 (by rfl) ⟨447803, by rfl⟩) R895607
theorem R400463 : Reach 400463 := rs (se 1 (by rfl) ⟨300347, by rfl⟩) R600695
theorem R105671 : Reach 105671 := rs (se 1 (by rfl) ⟨79253, by rfl⟩) R158507
theorem R466721 : Reach 466721 := rs (se 2 (by rfl) ⟨175020, by rfl⟩) R350041
theorem R204727 : Reach 204727 := rs (se 1 (by rfl) ⟨153545, by rfl⟩) R307091
theorem R434105 : Reach 434105 := rs (se 2 (by rfl) ⟨162789, by rfl⟩) R325579
theorem R565177 : Reach 565177 := rs (se 2 (by rfl) ⟨211941, by rfl⟩) R423883
theorem R139421 : Reach 139421 := rs (se 3 (by rfl) ⟨26141, by rfl⟩) R52283
theorem R205199 : Reach 205199 := rs (se 1 (by rfl) ⟨153899, by rfl⟩) R307799
theorem R172583 : Reach 172583 := rs (se 1 (by rfl) ⟨129437, by rfl⟩) R258875
theorem R172691 : Reach 172691 := rs (se 1 (by rfl) ⟨129518, by rfl⟩) R259037
theorem R172907 : Reach 172907 := rs (se 1 (by rfl) ⟨129680, by rfl⟩) R259361
theorem R172961 : Reach 172961 := rs (se 2 (by rfl) ⟨64860, by rfl⟩) R129721
theorem R861131 : Reach 861131 := rs (se 1 (by rfl) ⟨645848, by rfl⟩) R1291697
theorem R74791 : Reach 74791 := rs (se 1 (by rfl) ⟨56093, by rfl⟩) R112187
theorem R140345 : Reach 140345 := rs (se 2 (by rfl) ⟨52629, by rfl⟩) R105259
theorem R206185 : Reach 206185 := rs (se 2 (by rfl) ⟨77319, by rfl⟩) R154639
theorem R337277 : Reach 337277 := rs (se 3 (by rfl) ⟨63239, by rfl⟩) R126479
theorem R271835 : Reach 271835 := rs (se 1 (by rfl) ⟨203876, by rfl⟩) R407753
theorem R173555 : Reach 173555 := rs (se 1 (by rfl) ⟨130166, by rfl⟩) R260333
theorem R206459 : Reach 206459 := rs (se 1 (by rfl) ⟨154844, by rfl⟩) R309689
theorem R272321 : Reach 272321 := rs (se 2 (by rfl) ⟨102120, by rfl⟩) R204241
theorem R174095 : Reach 174095 := rs (se 1 (by rfl) ⟨130571, by rfl⟩) R261143
theorem R403865 : Reach 403865 := rs (se 2 (by rfl) ⟨151449, by rfl⟩) R302899
theorem R1026593 : Reach 1026593 := rs (se 2 (by rfl) ⟨384972, by rfl⟩) R769945
theorem R174689 : Reach 174689 := rs (se 2 (by rfl) ⟨65508, by rfl⟩) R131017
theorem R109487 : Reach 109487 := rs (se 1 (by rfl) ⟨82115, by rfl⟩) R164231
theorem R76727 : Reach 76727 := rs (se 1 (by rfl) ⟨57545, by rfl⟩) R115091
theorem R76763 : Reach 76763 := rs (se 1 (by rfl) ⟨57572, by rfl⟩) R115145
theorem R338917 : Reach 338917 := rs (se 4 (by rfl) ⟨31773, by rfl⟩) R63547
theorem R77231 : Reach 77231 := rs (se 1 (by rfl) ⟨57923, by rfl⟩) R115847
theorem R77321 : Reach 77321 := rs (se 2 (by rfl) ⟨28995, by rfl⟩) R57991
theorem R77351 : Reach 77351 := rs (se 1 (by rfl) ⟨58013, by rfl⟩) R116027
theorem R77435 : Reach 77435 := rs (se 1 (by rfl) ⟨58076, by rfl⟩) R116153
theorem R77561 : Reach 77561 := rs (se 2 (by rfl) ⟨29085, by rfl⟩) R58171
theorem R77663 : Reach 77663 := rs (se 1 (by rfl) ⟨58247, by rfl⟩) R116495
theorem R77675 : Reach 77675 := rs (se 1 (by rfl) ⟨58256, by rfl⟩) R116513
theorem R176033 : Reach 176033 := rs (se 2 (by rfl) ⟨66012, by rfl⟩) R132025
theorem R110497 : Reach 110497 := rs (se 2 (by rfl) ⟨41436, by rfl⟩) R82873
theorem R176147 : Reach 176147 := rs (se 1 (by rfl) ⟨132110, by rfl⟩) R264221
theorem R77903 : Reach 77903 := rs (se 1 (by rfl) ⟨58427, by rfl⟩) R116855
theorem R274589 : Reach 274589 := rs (se 3 (by rfl) ⟨51485, by rfl⟩) R102971
theorem R78023 : Reach 78023 := rs (se 1 (by rfl) ⟨58517, by rfl⟩) R117035
theorem R405809 : Reach 405809 := rs (se 2 (by rfl) ⟨152178, by rfl⟩) R304357
theorem R176471 : Reach 176471 := rs (se 1 (by rfl) ⟨132353, by rfl⟩) R264707
theorem R78185 : Reach 78185 := rs (se 2 (by rfl) ⟨29319, by rfl⟩) R58639
theorem R78263 : Reach 78263 := rs (se 1 (by rfl) ⟨58697, by rfl⟩) R117395
theorem R78299 : Reach 78299 := rs (se 1 (by rfl) ⟨58724, by rfl⟩) R117449
theorem R537299 : Reach 537299 := rs (se 1 (by rfl) ⟨402974, by rfl⟩) R805949
theorem R78767 : Reach 78767 := rs (se 1 (by rfl) ⟨59075, by rfl⟩) R118151
theorem R78857 : Reach 78857 := rs (se 2 (by rfl) ⟨29571, by rfl⟩) R59143
theorem R78887 : Reach 78887 := rs (se 1 (by rfl) ⟨59165, by rfl⟩) R118331
theorem R78971 : Reach 78971 := rs (se 1 (by rfl) ⟨59228, by rfl⟩) R118457
theorem R79097 : Reach 79097 := rs (se 2 (by rfl) ⟨29661, by rfl⟩) R59323
theorem R341263 : Reach 341263 := rs (se 1 (by rfl) ⟨255947, by rfl⟩) R511895
theorem R79199 : Reach 79199 := rs (se 1 (by rfl) ⟨59399, by rfl⟩) R118799
theorem R79211 : Reach 79211 := rs (se 1 (by rfl) ⟨59408, by rfl⟩) R118817
theorem R177551 : Reach 177551 := rs (se 1 (by rfl) ⟨133163, by rfl⟩) R266327
theorem R275885 : Reach 275885 := rs (se 3 (by rfl) ⟨51728, by rfl⟩) R103457
theorem R603611 : Reach 603611 := rs (se 1 (by rfl) ⟨452708, by rfl⟩) R905417
theorem R79439 : Reach 79439 := rs (se 1 (by rfl) ⟨59579, by rfl⟩) R119159
theorem R79559 : Reach 79559 := rs (se 1 (by rfl) ⟨59669, by rfl⟩) R119339
theorem R177875 : Reach 177875 := rs (se 1 (by rfl) ⟨133406, by rfl⟩) R266813
theorem R79721 : Reach 79721 := rs (se 2 (by rfl) ⟨29895, by rfl⟩) R59791
theorem R210863 : Reach 210863 := rs (se 1 (by rfl) ⟨158147, by rfl⟩) R316295
theorem R79799 : Reach 79799 := rs (se 1 (by rfl) ⟨59849, by rfl⟩) R119699
theorem R79835 : Reach 79835 := rs (se 1 (by rfl) ⟨59876, by rfl⟩) R119753
theorem R440477 : Reach 440477 := rs (se 3 (by rfl) ⟨82589, by rfl⟩) R165179
theorem R3225757 : Reach 3225757 := rs (se 3 (by rfl) ⟨604829, by rfl⟩) R1209659
theorem R342401 : Reach 342401 := rs (se 2 (by rfl) ⟨128400, by rfl⟩) R256801
theorem R80303 : Reach 80303 := rs (se 1 (by rfl) ⟨60227, by rfl⟩) R120455
theorem R80393 : Reach 80393 := rs (se 2 (by rfl) ⟨30147, by rfl⟩) R60295
theorem R80423 : Reach 80423 := rs (se 1 (by rfl) ⟨60317, by rfl⟩) R120635
theorem R80507 : Reach 80507 := rs (se 1 (by rfl) ⟨60380, by rfl⟩) R120761
theorem R146119 : Reach 146119 := rs (se 1 (by rfl) ⟨109589, by rfl⟩) R219179
theorem R342737 : Reach 342737 := rs (se 2 (by rfl) ⟨128526, by rfl⟩) R257053
theorem R80633 : Reach 80633 := rs (se 2 (by rfl) ⟨30237, by rfl⟩) R60475
theorem R80735 : Reach 80735 := rs (se 1 (by rfl) ⟨60551, by rfl⟩) R121103
theorem R80747 : Reach 80747 := rs (se 1 (by rfl) ⟨60560, by rfl⟩) R121121
theorem R179063 : Reach 179063 := rs (se 1 (by rfl) ⟨134297, by rfl⟩) R268595
theorem R80783 : Reach 80783 := rs (se 1 (by rfl) ⟨60587, by rfl⟩) R121175
theorem R342967 : Reach 342967 := rs (se 1 (by rfl) ⟨257225, by rfl⟩) R514451
theorem R277505 : Reach 277505 := rs (se 2 (by rfl) ⟨104064, by rfl⟩) R208129
theorem R80903 : Reach 80903 := rs (se 1 (by rfl) ⟨60677, by rfl⟩) R121355
theorem R179279 : Reach 179279 := rs (se 1 (by rfl) ⟨134459, by rfl⟩) R268919
theorem R80975 : Reach 80975 := rs (se 1 (by rfl) ⟨60731, by rfl⟩) R121463
theorem R81095 : Reach 81095 := rs (se 1 (by rfl) ⟨60821, by rfl⟩) R121643
theorem R81143 : Reach 81143 := rs (se 1 (by rfl) ⟨60857, by rfl⟩) R121715
theorem R81257 : Reach 81257 := rs (se 2 (by rfl) ⟨30471, by rfl⟩) R60943
theorem R81335 : Reach 81335 := rs (se 1 (by rfl) ⟨61001, by rfl⟩) R122003
theorem R179657 : Reach 179657 := rs (se 2 (by rfl) ⟨67371, by rfl⟩) R134743
theorem R81371 : Reach 81371 := rs (se 1 (by rfl) ⟨61028, by rfl⟩) R122057
theorem R409211 : Reach 409211 := rs (se 1 (by rfl) ⟨306908, by rfl⟩) R613817
theorem R147133 : Reach 147133 := rs (se 3 (by rfl) ⟨27587, by rfl⟩) R55175
theorem R179927 : Reach 179927 := rs (se 1 (by rfl) ⟨134945, by rfl⟩) R269891
theorem R278315 : Reach 278315 := rs (se 1 (by rfl) ⟨208736, by rfl⟩) R417473
theorem R376643 : Reach 376643 := rs (se 1 (by rfl) ⟨282482, by rfl⟩) R564965
theorem R81737 : Reach 81737 := rs (se 2 (by rfl) ⟨30651, by rfl⟩) R61303
theorem R180143 : Reach 180143 := rs (se 1 (by rfl) ⟨135107, by rfl⟩) R270215
theorem R81839 : Reach 81839 := rs (se 1 (by rfl) ⟨61379, by rfl⟩) R122759
theorem R81851 : Reach 81851 := rs (se 1 (by rfl) ⟨61388, by rfl⟩) R122777
theorem R81929 : Reach 81929 := rs (se 2 (by rfl) ⟨30723, by rfl⟩) R61447
theorem R81959 : Reach 81959 := rs (se 1 (by rfl) ⟨61469, by rfl⟩) R122939
theorem R81977 : Reach 81977 := rs (se 2 (by rfl) ⟨30741, by rfl⟩) R61483
theorem R114767 : Reach 114767 := rs (se 1 (by rfl) ⟨86075, by rfl⟩) R172151
theorem R82043 : Reach 82043 := rs (se 1 (by rfl) ⟨61532, by rfl⟩) R123065
theorem R82091 : Reach 82091 := rs (se 1 (by rfl) ⟨61568, by rfl⟩) R123137
theorem R147703 : Reach 147703 := rs (se 1 (by rfl) ⟨110777, by rfl⟩) R221555
theorem R82169 : Reach 82169 := rs (se 2 (by rfl) ⟨30813, by rfl⟩) R61627
theorem R82271 : Reach 82271 := rs (se 1 (by rfl) ⟨61703, by rfl⟩) R123407
theorem R82283 : Reach 82283 := rs (se 1 (by rfl) ⟨61712, by rfl⟩) R123425
theorem R82319 : Reach 82319 := rs (se 1 (by rfl) ⟨61739, by rfl⟩) R123479
theorem R115163 : Reach 115163 := rs (se 1 (by rfl) ⟨86372, by rfl⟩) R172745
theorem R82439 : Reach 82439 := rs (se 1 (by rfl) ⟨61829, by rfl⟩) R123659
theorem R147977 : Reach 147977 := rs (se 2 (by rfl) ⟨55491, by rfl⟩) R110983
theorem R213563 : Reach 213563 := rs (se 1 (by rfl) ⟨160172, by rfl⟩) R320345
theorem R82511 : Reach 82511 := rs (se 1 (by rfl) ⟨61883, by rfl⟩) R123767
theorem R82631 : Reach 82631 := rs (se 1 (by rfl) ⟨61973, by rfl⟩) R123947
theorem R82679 : Reach 82679 := rs (se 1 (by rfl) ⟨62009, by rfl⟩) R124019
theorem R82795 : Reach 82795 := rs (se 1 (by rfl) ⟨62096, by rfl⟩) R124193
theorem R115631 : Reach 115631 := rs (se 1 (by rfl) ⟨86723, by rfl⟩) R173447
theorem R1131569 : Reach 1131569 := rs (se 2 (by rfl) ⟨424338, by rfl⟩) R848677
theorem R115883 : Reach 115883 := rs (se 1 (by rfl) ⟨86912, by rfl⟩) R173825
theorem R148979 : Reach 148979 := rs (se 1 (by rfl) ⟨111734, by rfl⟩) R223469
theorem R83513 : Reach 83513 := rs (se 2 (by rfl) ⟨31317, by rfl⟩) R62635
theorem R116321 : Reach 116321 := rs (se 2 (by rfl) ⟨43620, by rfl⟩) R87241
theorem R280253 : Reach 280253 := rs (se 3 (by rfl) ⟨52547, by rfl⟩) R105095
theorem R116423 : Reach 116423 := rs (se 1 (by rfl) ⟨87317, by rfl⟩) R174635
theorem R444203 : Reach 444203 := rs (se 1 (by rfl) ⟨333152, by rfl⟩) R666305
theorem R345991 : Reach 345991 := rs (se 1 (by rfl) ⟨259493, by rfl⟩) R518987
theorem R1427381 : Reach 1427381 := rs (se 5 (by rfl) ⟨66908, by rfl⟩) R133817
theorem R149435 : Reach 149435 := rs (se 1 (by rfl) ⟨112076, by rfl⟩) R224153
theorem R51143 : Reach 51143 := rs (se 1 (by rfl) ⟨38357, by rfl⟩) R76715
theorem R411601 : Reach 411601 := rs (se 2 (by rfl) ⟨154350, by rfl⟩) R308701
theorem R51163 : Reach 51163 := rs (se 1 (by rfl) ⟨38372, by rfl⟩) R76745
theorem R51239 : Reach 51239 := rs (se 1 (by rfl) ⟨38429, by rfl⟩) R76859
theorem R84025 : Reach 84025 := rs (se 2 (by rfl) ⟨31509, by rfl⟩) R63019
theorem R51279 : Reach 51279 := rs (se 1 (by rfl) ⟨38459, by rfl⟩) R76919
theorem R51295 : Reach 51295 := rs (se 1 (by rfl) ⟨38471, by rfl⟩) R76943
theorem R936035 : Reach 936035 := rs (se 1 (by rfl) ⟨702026, by rfl⟩) R1404053
theorem R51323 : Reach 51323 := rs (se 1 (by rfl) ⟨38492, by rfl⟩) R76985
theorem R1099909 : Reach 1099909 := rs (se 4 (by rfl) ⟨103116, by rfl⟩) R206233
theorem R772253 : Reach 772253 := rs (se 3 (by rfl) ⟨144797, by rfl⟩) R289595
theorem R51375 : Reach 51375 := rs (se 1 (by rfl) ⟨38531, by rfl⟩) R77063
theorem R51399 : Reach 51399 := rs (se 1 (by rfl) ⟨38549, by rfl⟩) R77099
theorem R51419 : Reach 51419 := rs (se 1 (by rfl) ⟨38564, by rfl⟩) R77129
theorem R182519 : Reach 182519 := rs (se 1 (by rfl) ⟨136889, by rfl⟩) R273779
theorem R51495 : Reach 51495 := rs (se 1 (by rfl) ⟨38621, by rfl⟩) R77243
theorem R51535 : Reach 51535 := rs (se 1 (by rfl) ⟨38651, by rfl⟩) R77303
theorem R51551 : Reach 51551 := rs (se 1 (by rfl) ⟨38663, by rfl⟩) R77327
theorem R51579 : Reach 51579 := rs (se 1 (by rfl) ⟨38684, by rfl⟩) R77369
theorem R51631 : Reach 51631 := rs (se 1 (by rfl) ⟨38723, by rfl⟩) R77447
theorem R51655 : Reach 51655 := rs (se 1 (by rfl) ⟨38741, by rfl⟩) R77483
theorem R51675 : Reach 51675 := rs (se 1 (by rfl) ⟨38756, by rfl⟩) R77513
theorem R51751 : Reach 51751 := rs (se 1 (by rfl) ⟨38813, by rfl⟩) R77627
theorem R117287 : Reach 117287 := rs (se 1 (by rfl) ⟨87965, by rfl⟩) R175931
theorem R182843 : Reach 182843 := rs (se 1 (by rfl) ⟨137132, by rfl⟩) R274265
theorem R51791 : Reach 51791 := rs (se 1 (by rfl) ⟨38843, by rfl⟩) R77687
theorem R51807 : Reach 51807 := rs (se 1 (by rfl) ⟨38855, by rfl⟩) R77711
theorem R51835 : Reach 51835 := rs (se 1 (by rfl) ⟨38876, by rfl⟩) R77753
theorem R51887 : Reach 51887 := rs (se 1 (by rfl) ⟨38915, by rfl⟩) R77831
theorem R51911 : Reach 51911 := rs (se 1 (by rfl) ⟨38933, by rfl⟩) R77867
theorem R51931 : Reach 51931 := rs (se 1 (by rfl) ⟨38948, by rfl⟩) R77897
theorem R150265 : Reach 150265 := rs (se 2 (by rfl) ⟨56349, by rfl⟩) R112699
theorem R52007 : Reach 52007 := rs (se 1 (by rfl) ⟨39005, by rfl⟩) R78011
theorem R183113 : Reach 183113 := rs (se 2 (by rfl) ⟨68667, by rfl⟩) R137335
theorem R52047 : Reach 52047 := rs (se 1 (by rfl) ⟨39035, by rfl⟩) R78071
theorem R52063 : Reach 52063 := rs (se 1 (by rfl) ⟨39047, by rfl⟩) R78095
theorem R117611 : Reach 117611 := rs (se 1 (by rfl) ⟨88208, by rfl⟩) R176417
theorem R52091 : Reach 52091 := rs (se 1 (by rfl) ⟨39068, by rfl⟩) R78137
theorem R117665 : Reach 117665 := rs (se 2 (by rfl) ⟨44124, by rfl⟩) R88249
theorem R52143 : Reach 52143 := rs (se 1 (by rfl) ⟨39107, by rfl⟩) R78215
theorem R52167 : Reach 52167 := rs (se 1 (by rfl) ⟨39125, by rfl⟩) R78251
theorem R52187 : Reach 52187 := rs (se 1 (by rfl) ⟨39140, by rfl⟩) R78281
theorem R52263 : Reach 52263 := rs (se 1 (by rfl) ⟨39197, by rfl⟩) R78395
theorem R52303 : Reach 52303 := rs (se 1 (by rfl) ⟨39227, by rfl⟩) R78455
theorem R52319 : Reach 52319 := rs (se 1 (by rfl) ⟨39239, by rfl⟩) R78479
theorem R52347 : Reach 52347 := rs (se 1 (by rfl) ⟨39260, by rfl⟩) R78521
theorem R52399 : Reach 52399 := rs (se 1 (by rfl) ⟨39299, by rfl⟩) R78599
theorem R183491 : Reach 183491 := rs (se 1 (by rfl) ⟨137618, by rfl⟩) R275237
theorem R52423 : Reach 52423 := rs (se 1 (by rfl) ⟨39317, by rfl⟩) R78635
theorem R52443 : Reach 52443 := rs (se 1 (by rfl) ⟨39332, by rfl⟩) R78665
theorem R118007 : Reach 118007 := rs (se 1 (by rfl) ⟨88505, by rfl⟩) R177011
theorem R52519 : Reach 52519 := rs (se 1 (by rfl) ⟨39389, by rfl⟩) R78779
theorem R52559 : Reach 52559 := rs (se 1 (by rfl) ⟨39419, by rfl⟩) R78839
theorem R52575 : Reach 52575 := rs (se 1 (by rfl) ⟨39431, by rfl⟩) R78863
theorem R52603 : Reach 52603 := rs (se 1 (by rfl) ⟨39452, by rfl⟩) R78905
theorem R52655 : Reach 52655 := rs (se 1 (by rfl) ⟨39491, by rfl⟩) R78983
theorem R52679 : Reach 52679 := rs (se 1 (by rfl) ⟨39509, by rfl⟩) R79019
theorem R52699 : Reach 52699 := rs (se 1 (by rfl) ⟨39524, by rfl⟩) R79049
theorem R52775 : Reach 52775 := rs (se 1 (by rfl) ⟨39581, by rfl⟩) R79163
theorem R380477 : Reach 380477 := rs (se 3 (by rfl) ⟨71339, by rfl⟩) R142679
theorem R52815 : Reach 52815 := rs (se 1 (by rfl) ⟨39611, by rfl⟩) R79223
theorem R52831 : Reach 52831 := rs (se 1 (by rfl) ⟨39623, by rfl⟩) R79247
theorem R52859 : Reach 52859 := rs (se 1 (by rfl) ⟨39644, by rfl⟩) R79289
theorem R85627 : Reach 85627 := rs (se 1 (by rfl) ⟨64220, by rfl⟩) R128441
theorem R52911 : Reach 52911 := rs (se 1 (by rfl) ⟨39683, by rfl⟩) R79367
theorem R52935 : Reach 52935 := rs (se 1 (by rfl) ⟨39701, by rfl⟩) R79403
theorem R85703 : Reach 85703 := rs (se 1 (by rfl) ⟨64277, by rfl⟩) R128555
theorem R52955 : Reach 52955 := rs (se 1 (by rfl) ⟨39716, by rfl⟩) R79433
theorem R53031 : Reach 53031 := rs (se 1 (by rfl) ⟨39773, by rfl⟩) R79547
theorem R118601 : Reach 118601 := rs (se 2 (by rfl) ⟨44475, by rfl⟩) R88951
theorem R53071 : Reach 53071 := rs (se 1 (by rfl) ⟨39803, by rfl⟩) R79607
theorem R53087 : Reach 53087 := rs (se 1 (by rfl) ⟨39815, by rfl⟩) R79631
theorem R53115 : Reach 53115 := rs (se 1 (by rfl) ⟨39836, by rfl⟩) R79673
theorem R53167 : Reach 53167 := rs (se 1 (by rfl) ⟨39875, by rfl⟩) R79751
theorem R184247 : Reach 184247 := rs (se 1 (by rfl) ⟨138185, by rfl⟩) R276371
theorem R53191 : Reach 53191 := rs (se 1 (by rfl) ⟨39893, by rfl⟩) R79787
theorem R53211 : Reach 53211 := rs (se 1 (by rfl) ⟨39908, by rfl⟩) R79817
theorem R53287 : Reach 53287 := rs (se 1 (by rfl) ⟨39965, by rfl⟩) R79931
theorem R53327 : Reach 53327 := rs (se 1 (by rfl) ⟨39995, by rfl⟩) R79991
theorem R53343 : Reach 53343 := rs (se 1 (by rfl) ⟨40007, by rfl⟩) R80015
theorem R53371 : Reach 53371 := rs (se 1 (by rfl) ⟨40028, by rfl⟩) R80057
theorem R151723 : Reach 151723 := rs (se 1 (by rfl) ⟨113792, by rfl⟩) R227585
theorem R53423 : Reach 53423 := rs (se 1 (by rfl) ⟨40067, by rfl⟩) R80135
theorem R53447 : Reach 53447 := rs (se 1 (by rfl) ⟨40085, by rfl⟩) R80171
theorem R53467 : Reach 53467 := rs (se 1 (by rfl) ⟨40100, by rfl⟩) R80201
theorem R53543 : Reach 53543 := rs (se 1 (by rfl) ⟨40157, by rfl⟩) R80315
theorem R53583 : Reach 53583 := rs (se 1 (by rfl) ⟨40187, by rfl⟩) R80375
theorem R53599 : Reach 53599 := rs (se 1 (by rfl) ⟨40199, by rfl⟩) R80399
theorem R53627 : Reach 53627 := rs (se 1 (by rfl) ⟨40220, by rfl⟩) R80441
theorem R151951 : Reach 151951 := rs (se 1 (by rfl) ⟨113963, by rfl⟩) R227927
theorem R86447 : Reach 86447 := rs (se 1 (by rfl) ⟨64835, by rfl⟩) R129671
theorem R53679 : Reach 53679 := rs (se 1 (by rfl) ⟨40259, by rfl⟩) R80519
theorem R53703 : Reach 53703 := rs (se 1 (by rfl) ⟨40277, by rfl⟩) R80555
theorem R53723 : Reach 53723 := rs (se 1 (by rfl) ⟨40292, by rfl⟩) R80585
theorem R152027 : Reach 152027 := rs (se 1 (by rfl) ⟨114020, by rfl⟩) R228041
theorem R184841 : Reach 184841 := rs (se 2 (by rfl) ⟨69315, by rfl⟩) R138631
theorem R53799 : Reach 53799 := rs (se 1 (by rfl) ⟨40349, by rfl⟩) R80699
theorem R53839 : Reach 53839 := rs (se 1 (by rfl) ⟨40379, by rfl⟩) R80759
theorem R119393 : Reach 119393 := rs (se 2 (by rfl) ⟨44772, by rfl⟩) R89545
theorem R53883 : Reach 53883 := rs (se 1 (by rfl) ⟨40412, by rfl⟩) R80825
theorem R53959 : Reach 53959 := rs (se 1 (by rfl) ⟨40469, by rfl⟩) R80939
theorem R185041 : Reach 185041 := rs (se 2 (by rfl) ⟨69390, by rfl⟩) R138781
theorem R86879 : Reach 86879 := rs (se 1 (by rfl) ⟨65159, by rfl⟩) R130319
theorem R54111 : Reach 54111 := rs (se 1 (by rfl) ⟨40583, by rfl⟩) R81167
theorem R54191 : Reach 54191 := rs (se 1 (by rfl) ⟨40643, by rfl⟩) R81287
theorem R119735 : Reach 119735 := rs (se 1 (by rfl) ⟨89801, by rfl⟩) R179603
theorem R54235 : Reach 54235 := rs (se 1 (by rfl) ⟨40676, by rfl⟩) R81353
theorem R54311 : Reach 54311 := rs (se 1 (by rfl) ⟨40733, by rfl⟩) R81467
theorem R54351 : Reach 54351 := rs (se 1 (by rfl) ⟨40763, by rfl⟩) R81527
theorem R54395 : Reach 54395 := rs (se 1 (by rfl) ⟨40796, by rfl⟩) R81593
theorem R87239 : Reach 87239 := rs (se 1 (by rfl) ⟨65429, by rfl⟩) R130859
theorem R54471 : Reach 54471 := rs (se 1 (by rfl) ⟨40853, by rfl⟩) R81707
theorem R54623 : Reach 54623 := rs (se 1 (by rfl) ⟨40967, by rfl⟩) R81935
theorem R185705 : Reach 185705 := rs (se 2 (by rfl) ⟨69639, by rfl⟩) R139279
theorem R349555 : Reach 349555 := rs (se 1 (by rfl) ⟨262166, by rfl⟩) R524333
theorem R87439 : Reach 87439 := rs (se 1 (by rfl) ⟨65579, by rfl⟩) R131159
theorem R54703 : Reach 54703 := rs (se 1 (by rfl) ⟨41027, by rfl⟩) R82055
theorem R54747 : Reach 54747 := rs (se 1 (by rfl) ⟨41060, by rfl⟩) R82121
theorem R26891747 : Reach 26891747 := rs (se 1 (by rfl) ⟨20168810, by rfl⟩) R40337621
theorem R120329 : Reach 120329 := rs (se 2 (by rfl) ⟨45123, by rfl⟩) R90247
theorem R54823 : Reach 54823 := rs (se 1 (by rfl) ⟨41117, by rfl⟩) R82235
theorem R54863 : Reach 54863 := rs (se 1 (by rfl) ⟨41147, by rfl⟩) R82295
theorem R54907 : Reach 54907 := rs (se 1 (by rfl) ⟨41180, by rfl⟩) R82361
theorem R153227 : Reach 153227 := rs (se 1 (by rfl) ⟨114920, by rfl⟩) R229841
theorem R284305 : Reach 284305 := rs (se 2 (by rfl) ⟨106614, by rfl⟩) R213229
theorem R448199 : Reach 448199 := rs (se 1 (by rfl) ⟨336149, by rfl⟩) R672299
theorem R54983 : Reach 54983 := rs (se 1 (by rfl) ⟨41237, by rfl⟩) R82475
theorem R87799 : Reach 87799 := rs (se 1 (by rfl) ⟨65849, by rfl⟩) R131699
theorem R120671 : Reach 120671 := rs (se 1 (by rfl) ⟨90503, by rfl⟩) R181007
theorem R612359 : Reach 612359 := rs (se 1 (by rfl) ⟨459269, by rfl⟩) R918539
theorem R120851 : Reach 120851 := rs (se 1 (by rfl) ⟨90638, by rfl⟩) R181277
theorem R88121 : Reach 88121 := rs (se 2 (by rfl) ⟨33045, by rfl⟩) R66091
theorem R350297 : Reach 350297 := rs (se 2 (by rfl) ⟨131361, by rfl⟩) R262723
theorem R121193 : Reach 121193 := rs (se 2 (by rfl) ⟨45447, by rfl⟩) R90895
theorem R449225 : Reach 449225 := rs (se 2 (by rfl) ⟨168459, by rfl⟩) R336919
theorem R187091 : Reach 187091 := rs (se 1 (by rfl) ⟨140318, by rfl⟩) R280637
theorem R88823 : Reach 88823 := rs (se 1 (by rfl) ⟨66617, by rfl⟩) R133235
theorem R121787 : Reach 121787 := rs (se 1 (by rfl) ⟨91340, by rfl⟩) R182681
theorem R121913 : Reach 121913 := rs (se 2 (by rfl) ⟨45717, by rfl⟩) R91435
theorem R89167 : Reach 89167 := rs (se 1 (by rfl) ⟨66875, by rfl⟩) R133751
theorem R285943 : Reach 285943 := rs (se 1 (by rfl) ⟨214457, by rfl⟩) R428915
theorem R1072397 : Reach 1072397 := rs (se 3 (by rfl) ⟨201074, by rfl⟩) R402149
theorem R89417 : Reach 89417 := rs (se 2 (by rfl) ⟨33531, by rfl⟩) R67063
theorem R122255 : Reach 122255 := rs (se 1 (by rfl) ⟨91691, by rfl⟩) R183383
theorem R122393 : Reach 122393 := rs (se 2 (by rfl) ⟨45897, by rfl⟩) R91795
theorem R122507 : Reach 122507 := rs (se 1 (by rfl) ⟨91880, by rfl⟩) R183761
theorem R220819 : Reach 220819 := rs (se 1 (by rfl) ⟨165614, by rfl⟩) R331229
theorem R122579 : Reach 122579 := rs (se 1 (by rfl) ⟨91934, by rfl⟩) R183869
theorem R351959 : Reach 351959 := rs (se 1 (by rfl) ⟨263969, by rfl⟩) R527939
theorem R89849 : Reach 89849 := rs (se 2 (by rfl) ⟨33693, by rfl⟩) R67387
theorem R221089 : Reach 221089 := rs (se 2 (by rfl) ⟨82908, by rfl⟩) R165817
theorem R188335 : Reach 188335 := rs (se 1 (by rfl) ⟨141251, by rfl⟩) R282503
theorem R90031 : Reach 90031 := rs (se 1 (by rfl) ⟨67523, by rfl⟩) R135047
theorem R90119 : Reach 90119 := rs (se 1 (by rfl) ⟨67589, by rfl⟩) R135179
theorem R90463 : Reach 90463 := rs (se 1 (by rfl) ⟨67847, by rfl⟩) R135695
theorem R57775 : Reach 57775 := rs (se 1 (by rfl) ⟨43331, by rfl⟩) R86663
theorem R90551 : Reach 90551 := rs (se 1 (by rfl) ⟨67913, by rfl⟩) R135827
theorem R123515 : Reach 123515 := rs (se 1 (by rfl) ⟨92636, by rfl⟩) R185273
theorem R221831 : Reach 221831 := rs (se 1 (by rfl) ⟨166373, by rfl⟩) R332747
theorem R123641 : Reach 123641 := rs (se 2 (by rfl) ⟨46365, by rfl⟩) R92731
theorem R58207 : Reach 58207 := rs (se 1 (by rfl) ⟨43655, by rfl⟩) R87311
theorem R615275 : Reach 615275 := rs (se 1 (by rfl) ⟨461456, by rfl⟩) R922913
theorem R156599 : Reach 156599 := rs (se 1 (by rfl) ⟨117449, by rfl⟩) R234899
theorem R123911 : Reach 123911 := rs (se 1 (by rfl) ⟨92933, by rfl⟩) R185867
theorem R91145 : Reach 91145 := rs (se 2 (by rfl) ⟨34179, by rfl⟩) R68359
theorem R123983 : Reach 123983 := rs (se 1 (by rfl) ⟨92987, by rfl⟩) R185975
theorem R91307 : Reach 91307 := rs (se 1 (by rfl) ⟨68480, by rfl⟩) R136961
theorem R58567 : Reach 58567 := rs (se 1 (by rfl) ⟨43925, by rfl⟩) R87851
theorem R1500677 : Reach 1500677 := rs (se 4 (by rfl) ⟨140688, by rfl⟩) R281377
theorem R91705 : Reach 91705 := rs (se 2 (by rfl) ⟨34389, by rfl⟩) R68779
theorem R91847 : Reach 91847 := rs (se 1 (by rfl) ⟨68885, by rfl⟩) R137771
theorem R92009 : Reach 92009 := rs (se 2 (by rfl) ⟨34503, by rfl⟩) R69007
theorem R1894337 : Reach 1894337 := rs (se 2 (by rfl) ⟨710376, by rfl⟩) R1420753
theorem R288775 : Reach 288775 := rs (se 1 (by rfl) ⟨216581, by rfl⟩) R433163
theorem R59431 : Reach 59431 := rs (se 1 (by rfl) ⟨44573, by rfl⟩) R89147
theorem R92407 : Reach 92407 := rs (se 1 (by rfl) ⟨69305, by rfl⟩) R138611
theorem R452951 : Reach 452951 := rs (se 1 (by rfl) ⟨339713, by rfl⟩) R679427
theorem R387433 : Reach 387433 := rs (se 2 (by rfl) ⟨145287, by rfl⟩) R290575
theorem R92603 : Reach 92603 := rs (se 1 (by rfl) ⟨69452, by rfl⟩) R138905
theorem R92711 : Reach 92711 := rs (se 1 (by rfl) ⟨69533, by rfl⟩) R139067
theorem R93001 : Reach 93001 := rs (se 2 (by rfl) ⟨34875, by rfl⟩) R69751
theorem R191393 : Reach 191393 := rs (se 2 (by rfl) ⟨71772, by rfl⟩) R143545
theorem R2289239 : Reach 2289239 := rs (se 1 (by rfl) ⟨1716929, by rfl⟩) R3433859
theorem R61051 : Reach 61051 := rs (se 1 (by rfl) ⟨45788, by rfl⟩) R91577
theorem R61519 : Reach 61519 := rs (se 1 (by rfl) ⟨46139, by rfl⟩) R92279
theorem R61879 : Reach 61879 := rs (se 1 (by rfl) ⟨46409, by rfl⟩) R92819
theorem R61915 : Reach 61915 := rs (se 1 (by rfl) ⟨46436, by rfl⟩) R92873
theorem R390743 : Reach 390743 := rs (se 1 (by rfl) ⟨293057, by rfl⟩) R586115
theorem R194183 : Reach 194183 := rs (se 1 (by rfl) ⟨145637, by rfl⟩) R291275
theorem R521873 : Reach 521873 := rs (se 2 (by rfl) ⟨195702, by rfl⟩) R391405
theorem R325309 : Reach 325309 := rs (se 3 (by rfl) ⟨60995, by rfl⟩) R121991
theorem R260185 : Reach 260185 := rs (se 2 (by rfl) ⟨97569, by rfl⟩) R195139
theorem R588185 : Reach 588185 := rs (se 2 (by rfl) ⟨220569, by rfl⟩) R441139
theorem R195053 : Reach 195053 := rs (se 3 (by rfl) ⟨36572, by rfl⟩) R73145
theorem R129575 : Reach 129575 := rs (se 1 (by rfl) ⟨97181, by rfl⟩) R194363
theorem R195281 : Reach 195281 := rs (se 2 (by rfl) ⟨73230, by rfl⟩) R146461
theorem R260819 : Reach 260819 := rs (se 1 (by rfl) ⟨195614, by rfl⟩) R391229
theorem R97337 : Reach 97337 := rs (se 2 (by rfl) ⟨36501, by rfl⟩) R73003
theorem R195965 : Reach 195965 := rs (se 3 (by rfl) ⟨36743, by rfl⟩) R73487
theorem R97679 : Reach 97679 := rs (se 1 (by rfl) ⟨73259, by rfl⟩) R146519
theorem R228851 : Reach 228851 := rs (se 1 (by rfl) ⟨171638, by rfl⟩) R343277
theorem R65063 : Reach 65063 := rs (se 1 (by rfl) ⟨48797, by rfl⟩) R97595
theorem R556583 : Reach 556583 := rs (se 1 (by rfl) ⟨417437, by rfl⟩) R834875
theorem R425569 : Reach 425569 := rs (se 2 (by rfl) ⟨159588, by rfl⟩) R319177
theorem R98003 : Reach 98003 := rs (se 1 (by rfl) ⟨73502, by rfl⟩) R147005
theorem R65387 : Reach 65387 := rs (se 1 (by rfl) ⟨49040, by rfl⟩) R98081
theorem R196937 : Reach 196937 := rs (se 2 (by rfl) ⟨73851, by rfl⟩) R147703
theorem R98651 : Reach 98651 := rs (se 1 (by rfl) ⟨73988, by rfl⟩) R147977
theorem R131503 : Reach 131503 := rs (se 1 (by rfl) ⟨98627, by rfl⟩) R197255
theorem R262601 : Reach 262601 := rs (se 2 (by rfl) ⟨98475, by rfl⟩) R196951
theorem R754379 : Reach 754379 := rs (se 1 (by rfl) ⟨565784, by rfl⟩) R1131569
theorem R393943 : Reach 393943 := rs (se 1 (by rfl) ⟨295457, by rfl⟩) R590915
theorem R131807 : Reach 131807 := rs (se 1 (by rfl) ⟨98855, by rfl⟩) R197711
theorem R66359 : Reach 66359 := rs (se 1 (by rfl) ⟨49769, by rfl⟩) R99539
theorem R394145 : Reach 394145 := rs (se 2 (by rfl) ⟨147804, by rfl⟩) R295609
theorem R328643 : Reach 328643 := rs (se 1 (by rfl) ⟨246482, by rfl⟩) R492965
theorem R66511 : Reach 66511 := rs (se 1 (by rfl) ⟨49883, by rfl⟩) R99767
theorem R99319 : Reach 99319 := rs (se 1 (by rfl) ⟨74489, by rfl⟩) R148979
theorem R230525 : Reach 230525 := rs (se 3 (by rfl) ⟨43223, by rfl⟩) R86447
theorem R296135 : Reach 296135 := rs (se 1 (by rfl) ⟨222101, by rfl⟩) R444203
theorem R263411 : Reach 263411 := rs (se 1 (by rfl) ⟨197558, by rfl⟩) R395117
theorem R951587 : Reach 951587 := rs (se 1 (by rfl) ⟨713690, by rfl⟩) R1427381
theorem R99623 : Reach 99623 := rs (se 1 (by rfl) ⟨74717, by rfl⟩) R149435
theorem R132475 : Reach 132475 := rs (se 1 (by rfl) ⟨99356, by rfl⟩) R198713
theorem R99721 : Reach 99721 := rs (se 2 (by rfl) ⟨37395, by rfl⟩) R74791
theorem R624023 : Reach 624023 := rs (se 1 (by rfl) ⟨468017, by rfl⟩) R936035
theorem R132911 : Reach 132911 := rs (se 1 (by rfl) ⟨99683, by rfl⟩) R199367
theorem R67483 : Reach 67483 := rs (se 1 (by rfl) ⟨50612, by rfl⟩) R101225
theorem R264377 : Reach 264377 := rs (se 2 (by rfl) ⟨99141, by rfl⟩) R198283
theorem R133559 : Reach 133559 := rs (se 1 (by rfl) ⟨100169, by rfl⟩) R200339
theorem R461321 : Reach 461321 := rs (se 2 (by rfl) ⟨172995, by rfl⟩) R345991
theorem R2296349 : Reach 2296349 := rs (se 3 (by rfl) ⟨430565, by rfl⟩) R861131
theorem R101351 : Reach 101351 := rs (se 1 (by rfl) ⟨76013, by rfl⟩) R152027
theorem R265355 : Reach 265355 := rs (se 1 (by rfl) ⟨199016, by rfl⟩) R398033
theorem R396575 : Reach 396575 := rs (se 1 (by rfl) ⟨297431, by rfl⟩) R594863
theorem R331127 : Reach 331127 := rs (se 1 (by rfl) ⟨248345, by rfl⟩) R496691
theorem R134561 : Reach 134561 := rs (se 2 (by rfl) ⟨50460, by rfl⟩) R100921
theorem R69113 : Reach 69113 := rs (se 2 (by rfl) ⟨25917, by rfl⟩) R51835
theorem R17927831 : Reach 17927831 := rs (se 1 (by rfl) ⟨13445873, by rfl⟩) R26891747
theorem R200353 : Reach 200353 := rs (se 2 (by rfl) ⟨75132, by rfl⟩) R150265
theorem R265963 : Reach 265963 := rs (se 1 (by rfl) ⟨199472, by rfl⟩) R398945
theorem R102151 : Reach 102151 := rs (se 1 (by rfl) ⟨76613, by rfl⟩) R153227
theorem R298799 : Reach 298799 := rs (se 1 (by rfl) ⟨224099, by rfl⟩) R448199
theorem R135017 : Reach 135017 := rs (se 2 (by rfl) ⟨50631, by rfl⟩) R101263
theorem R233531 : Reach 233531 := rs (se 1 (by rfl) ⟨175148, by rfl⟩) R350297
theorem R1249667 : Reach 1249667 := rs (se 1 (by rfl) ⟨937250, by rfl⟩) R1874501
theorem R299483 : Reach 299483 := rs (se 1 (by rfl) ⟨224612, by rfl⟩) R449225
theorem R398047 : Reach 398047 := rs (se 1 (by rfl) ⟨298535, by rfl⟩) R597071
theorem R266975 : Reach 266975 := rs (se 1 (by rfl) ⟨200231, by rfl⟩) R400463
theorem R562301 : Reach 562301 := rs (se 3 (by rfl) ⟨105431, by rfl⟩) R210863
theorem R136637 : Reach 136637 := rs (se 3 (by rfl) ⟨25619, by rfl⟩) R51239
theorem R202297 : Reach 202297 := rs (se 2 (by rfl) ⟨75861, by rfl⟩) R151723
theorem R136799 : Reach 136799 := rs (se 1 (by rfl) ⟨102599, by rfl⟩) R205199
theorem R5936885 : Reach 5936885 := rs (se 5 (by rfl) ⟨278291, by rfl⟩) R556583
theorem R202601 : Reach 202601 := rs (se 2 (by rfl) ⟨75975, by rfl⟩) R151951
theorem R104399 : Reach 104399 := rs (se 1 (by rfl) ⟨78299, by rfl⟩) R156599
theorem R137497 : Reach 137497 := rs (se 2 (by rfl) ⟨51561, by rfl⟩) R103123
theorem R137639 : Reach 137639 := rs (se 1 (by rfl) ⟨103229, by rfl⟩) R206459
theorem R137801 : Reach 137801 := rs (se 2 (by rfl) ⟨51675, by rfl⟩) R103351
theorem R301967 : Reach 301967 := rs (se 1 (by rfl) ⟨226475, by rfl⟩) R452951
theorem R269243 : Reach 269243 := rs (se 1 (by rfl) ⟨201932, by rfl⟩) R403865
theorem R466073 : Reach 466073 := rs (se 2 (by rfl) ⟨174777, by rfl⟩) R349555
theorem R72991 : Reach 72991 := rs (se 1 (by rfl) ⟨54743, by rfl⟩) R109487
theorem R400889 : Reach 400889 := rs (se 2 (by rfl) ⟨150333, by rfl⟩) R300667
theorem R433745 : Reach 433745 := rs (se 2 (by rfl) ⟨162654, by rfl⟩) R325309
theorem R270539 : Reach 270539 := rs (se 1 (by rfl) ⟨202904, by rfl⟩) R405809
theorem R4301009 : Reach 4301009 := rs (se 2 (by rfl) ⟨1612878, by rfl⟩) R3225757
theorem R401921 : Reach 401921 := rs (se 2 (by rfl) ⟨150720, by rfl⟩) R301441
theorem R2859725 : Reach 2859725 := rs (se 3 (by rfl) ⟨536198, by rfl⟩) R1072397
theorem R1057697 : Reach 1057697 := rs (se 2 (by rfl) ⟨396636, by rfl⟩) R793273
theorem R402407 : Reach 402407 := rs (se 1 (by rfl) ⟨301805, by rfl⟩) R603611
theorem R173501 : Reach 173501 := rs (se 3 (by rfl) ⟨32531, by rfl⟩) R65063
theorem R173879 : Reach 173879 := rs (se 1 (by rfl) ⟨130409, by rfl⟩) R260819
theorem R567425 : Reach 567425 := rs (se 2 (by rfl) ⟨212784, by rfl⟩) R425569
theorem R174365 : Reach 174365 := rs (se 3 (by rfl) ⟨32693, by rfl⟩) R65387
theorem R272807 : Reach 272807 := rs (se 1 (by rfl) ⟨204605, by rfl⟩) R409211
theorem R469421 : Reach 469421 := rs (se 3 (by rfl) ⟨88016, by rfl⟩) R176033
theorem R272969 : Reach 272969 := rs (se 2 (by rfl) ⟨102363, by rfl⟩) R204727
theorem R76511 : Reach 76511 := rs (se 1 (by rfl) ⟨57383, by rfl⟩) R114767
theorem R76775 : Reach 76775 := rs (se 1 (by rfl) ⟨57581, by rfl⟩) R115163
theorem R2141315 : Reach 2141315 := rs (se 1 (by rfl) ⟨1605986, by rfl⟩) R3211973
theorem R77033 : Reach 77033 := rs (se 2 (by rfl) ⟨28887, by rfl⟩) R57775
theorem R77087 : Reach 77087 := rs (se 1 (by rfl) ⟨57815, by rfl⟩) R115631
theorem R175391 : Reach 175391 := rs (se 1 (by rfl) ⟨131543, by rfl⟩) R263087
theorem R77255 : Reach 77255 := rs (se 1 (by rfl) ⟨57941, by rfl⟩) R115883
theorem R143005 : Reach 143005 := rs (se 3 (by rfl) ⟨26813, by rfl⟩) R53627
theorem R77609 : Reach 77609 := rs (se 2 (by rfl) ⟨29103, by rfl⟩) R58207
theorem R77615 : Reach 77615 := rs (se 1 (by rfl) ⟨58211, by rfl⟩) R116423
theorem R110393 : Reach 110393 := rs (se 2 (by rfl) ⟨41397, by rfl⟩) R82795
theorem R569501 : Reach 569501 := rs (se 3 (by rfl) ⟨106781, by rfl⟩) R213563
theorem R110803 : Reach 110803 := rs (se 1 (by rfl) ⟨83102, by rfl⟩) R166205
theorem R78089 : Reach 78089 := rs (se 2 (by rfl) ⟨29283, by rfl⟩) R58567
theorem R78191 : Reach 78191 := rs (se 1 (by rfl) ⟨58643, by rfl⟩) R117287
theorem R111059 : Reach 111059 := rs (se 1 (by rfl) ⟨83294, by rfl⟩) R166589
theorem R274913 : Reach 274913 := rs (se 2 (by rfl) ⟨103092, by rfl⟩) R206185
theorem R78407 : Reach 78407 := rs (se 1 (by rfl) ⟨58805, by rfl⟩) R117611
theorem R78443 : Reach 78443 := rs (se 1 (by rfl) ⟨58832, by rfl⟩) R117665
theorem R78671 : Reach 78671 := rs (se 1 (by rfl) ⟨59003, by rfl⟩) R118007
theorem R111503 : Reach 111503 := rs (se 1 (by rfl) ⟨83627, by rfl⟩) R167255
theorem R570359 : Reach 570359 := rs (se 1 (by rfl) ⟨427769, by rfl⟩) R855539
theorem R79067 : Reach 79067 := rs (se 1 (by rfl) ⟨59300, by rfl⟩) R118601
theorem R79241 : Reach 79241 := rs (se 2 (by rfl) ⟨29715, by rfl⟩) R59431
theorem R112033 : Reach 112033 := rs (se 2 (by rfl) ⟨42012, by rfl⟩) R84025
theorem R177821 : Reach 177821 := rs (se 3 (by rfl) ⟨33341, by rfl⟩) R66683
theorem R79595 : Reach 79595 := rs (se 1 (by rfl) ⟨59696, by rfl⟩) R119393
theorem R79823 : Reach 79823 := rs (se 1 (by rfl) ⟨59867, by rfl⟩) R119735
theorem R178361 : Reach 178361 := rs (se 2 (by rfl) ⟨66885, by rfl⟩) R133771
theorem R80219 : Reach 80219 := rs (se 1 (by rfl) ⟨60164, by rfl⟩) R120329
theorem R80447 : Reach 80447 := rs (se 1 (by rfl) ⟨60335, by rfl⟩) R120671
theorem R408239 : Reach 408239 := rs (se 1 (by rfl) ⟨306179, by rfl⟩) R612359
theorem R80567 : Reach 80567 := rs (se 1 (by rfl) ⟨60425, by rfl⟩) R120851
theorem R277181 : Reach 277181 := rs (se 3 (by rfl) ⟨51971, by rfl⟩) R103943
theorem R113375 : Reach 113375 := rs (se 1 (by rfl) ⟨85031, by rfl⟩) R170063
theorem R80795 : Reach 80795 := rs (se 1 (by rfl) ⟨60596, by rfl⟩) R121193
theorem R310189 : Reach 310189 := rs (se 3 (by rfl) ⟨58160, by rfl⟩) R116321
theorem R81191 : Reach 81191 := rs (se 1 (by rfl) ⟨60893, by rfl⟩) R121787
theorem R81275 : Reach 81275 := rs (se 1 (by rfl) ⟨60956, by rfl⟩) R121913
theorem R114169 : Reach 114169 := rs (se 2 (by rfl) ⟨42813, by rfl⟩) R85627
theorem R81401 : Reach 81401 := rs (se 2 (by rfl) ⟨30525, by rfl⟩) R61051
theorem R81503 : Reach 81503 := rs (se 1 (by rfl) ⟨61127, by rfl⟩) R122255
theorem R179873 : Reach 179873 := rs (se 2 (by rfl) ⟨67452, by rfl⟩) R134905
theorem R81595 : Reach 81595 := rs (se 1 (by rfl) ⟨61196, by rfl⟩) R122393
theorem R81671 : Reach 81671 := rs (se 1 (by rfl) ⟨61253, by rfl⟩) R122507
theorem R81719 : Reach 81719 := rs (se 1 (by rfl) ⟨61289, by rfl⟩) R122579
theorem R311147 : Reach 311147 := rs (se 1 (by rfl) ⟨233360, by rfl⟩) R466721
theorem R147329 : Reach 147329 := rs (se 2 (by rfl) ⟨55248, by rfl⟩) R110497
theorem R82025 : Reach 82025 := rs (se 2 (by rfl) ⟨30759, by rfl⟩) R61519
theorem R115055 : Reach 115055 := rs (se 1 (by rfl) ⟨86291, by rfl⟩) R172583
theorem R82343 : Reach 82343 := rs (se 1 (by rfl) ⟨61757, by rfl⟩) R123515
theorem R147887 : Reach 147887 := rs (se 1 (by rfl) ⟨110915, by rfl⟩) R221831
theorem R115127 : Reach 115127 := rs (se 1 (by rfl) ⟨86345, by rfl⟩) R172691
theorem R82427 : Reach 82427 := rs (se 1 (by rfl) ⟨61820, by rfl⟩) R123641
theorem R180737 : Reach 180737 := rs (se 2 (by rfl) ⟨67776, by rfl⟩) R135553
theorem R115271 : Reach 115271 := rs (se 1 (by rfl) ⟨86453, by rfl⟩) R172907
theorem R410183 : Reach 410183 := rs (se 1 (by rfl) ⟨307637, by rfl⟩) R615275
theorem R82505 : Reach 82505 := rs (se 2 (by rfl) ⟨30939, by rfl⟩) R61879
theorem R115307 : Reach 115307 := rs (se 1 (by rfl) ⟨86480, by rfl⟩) R172961
theorem R82553 : Reach 82553 := rs (se 2 (by rfl) ⟨30957, by rfl⟩) R61915
theorem R574087 : Reach 574087 := rs (se 1 (by rfl) ⟨430565, by rfl⟩) R861131
theorem R82607 : Reach 82607 := rs (se 1 (by rfl) ⟨61955, by rfl⟩) R123911
theorem R82655 : Reach 82655 := rs (se 1 (by rfl) ⟨61991, by rfl⟩) R123983
theorem R246721 : Reach 246721 := rs (se 2 (by rfl) ⟨92520, by rfl⟩) R185041
theorem R181223 : Reach 181223 := rs (se 1 (by rfl) ⟨135917, by rfl⟩) R271835
theorem R115703 : Reach 115703 := rs (se 1 (by rfl) ⟨86777, by rfl⟩) R173555
theorem R1000451 : Reach 1000451 := rs (se 1 (by rfl) ⟨750338, by rfl⟩) R1500677
theorem R181547 : Reach 181547 := rs (se 1 (by rfl) ⟨136160, by rfl⟩) R272321
theorem R1262891 : Reach 1262891 := rs (se 1 (by rfl) ⟨947168, by rfl⟩) R1894337
theorem R116063 : Reach 116063 := rs (se 1 (by rfl) ⟨87047, by rfl⟩) R174095
theorem R181817 : Reach 181817 := rs (se 2 (by rfl) ⟨68181, by rfl⟩) R136363
theorem R116459 : Reach 116459 := rs (se 1 (by rfl) ⟨87344, by rfl⟩) R174689
theorem R116585 : Reach 116585 := rs (se 2 (by rfl) ⟨43719, by rfl⟩) R87439
theorem R51151 : Reach 51151 := rs (se 1 (by rfl) ⟨38363, by rfl⟩) R76727
theorem R51175 : Reach 51175 := rs (se 1 (by rfl) ⟨38381, by rfl⟩) R76763
theorem R379073 : Reach 379073 := rs (se 2 (by rfl) ⟨142152, by rfl⟩) R284305
theorem R51487 : Reach 51487 := rs (se 1 (by rfl) ⟨38615, by rfl⟩) R77231
theorem R117065 : Reach 117065 := rs (se 2 (by rfl) ⟨43899, by rfl⟩) R87799
theorem R51547 : Reach 51547 := rs (se 1 (by rfl) ⟨38660, by rfl⟩) R77321
theorem R51567 : Reach 51567 := rs (se 1 (by rfl) ⟨38675, by rfl⟩) R77351
theorem R1526159 : Reach 1526159 := rs (se 1 (by rfl) ⟨1144619, by rfl⟩) R2289239
theorem R51623 : Reach 51623 := rs (se 1 (by rfl) ⟨38717, by rfl⟩) R77435
theorem R51707 : Reach 51707 := rs (se 1 (by rfl) ⟨38780, by rfl⟩) R77561
theorem R51775 : Reach 51775 := rs (se 1 (by rfl) ⟨38831, by rfl⟩) R77663
theorem R51783 : Reach 51783 := rs (se 1 (by rfl) ⟨38837, by rfl⟩) R77675
theorem R117431 : Reach 117431 := rs (se 1 (by rfl) ⟨88073, by rfl⟩) R176147
theorem R51935 : Reach 51935 := rs (se 1 (by rfl) ⟨38951, by rfl⟩) R77903
theorem R183059 : Reach 183059 := rs (se 1 (by rfl) ⟨137294, by rfl⟩) R274589
theorem R346913 : Reach 346913 := rs (se 2 (by rfl) ⟨130092, by rfl⟩) R260185
theorem R52015 : Reach 52015 := rs (se 1 (by rfl) ⟨39011, by rfl⟩) R78023
theorem R117647 : Reach 117647 := rs (se 1 (by rfl) ⟨88235, by rfl⟩) R176471
theorem R52123 : Reach 52123 := rs (se 1 (by rfl) ⟨39092, by rfl⟩) R78185
theorem R52175 : Reach 52175 := rs (se 1 (by rfl) ⟨39131, by rfl⟩) R78263
theorem R52199 : Reach 52199 := rs (se 1 (by rfl) ⟨39149, by rfl⟩) R78299
theorem R281789 : Reach 281789 := rs (se 3 (by rfl) ⟨52835, by rfl⟩) R105671
theorem R52511 : Reach 52511 := rs (se 1 (by rfl) ⟨39383, by rfl⟩) R78767
theorem R52571 : Reach 52571 := rs (se 1 (by rfl) ⟨39428, by rfl⟩) R78857
theorem R52591 : Reach 52591 := rs (se 1 (by rfl) ⟨39443, by rfl⟩) R78887
theorem R52647 : Reach 52647 := rs (se 1 (by rfl) ⟨39485, by rfl⟩) R78971
theorem R52731 : Reach 52731 := rs (se 1 (by rfl) ⟨39548, by rfl⟩) R79097
theorem R52799 : Reach 52799 := rs (se 1 (by rfl) ⟨39599, by rfl⟩) R79199
theorem R52807 : Reach 52807 := rs (se 1 (by rfl) ⟨39605, by rfl⟩) R79211
theorem R118367 : Reach 118367 := rs (se 1 (by rfl) ⟨88775, by rfl⟩) R177551
theorem R183923 : Reach 183923 := rs (se 1 (by rfl) ⟨137942, by rfl⟩) R275885
theorem R52959 : Reach 52959 := rs (se 1 (by rfl) ⟨39719, by rfl⟩) R79439
theorem R347915 : Reach 347915 := rs (se 1 (by rfl) ⟨260936, by rfl⟩) R521873
theorem R53039 : Reach 53039 := rs (se 1 (by rfl) ⟨39779, by rfl⟩) R79559
theorem R118583 : Reach 118583 := rs (se 1 (by rfl) ⟨88937, by rfl⟩) R177875
theorem R184193 : Reach 184193 := rs (se 2 (by rfl) ⟨69072, by rfl⟩) R138145
theorem R53147 : Reach 53147 := rs (se 1 (by rfl) ⟨39860, by rfl⟩) R79721
theorem R53199 : Reach 53199 := rs (se 1 (by rfl) ⟨39899, by rfl⟩) R79799
theorem R53223 : Reach 53223 := rs (se 1 (by rfl) ⟨39917, by rfl⟩) R79835
theorem R118889 : Reach 118889 := rs (se 2 (by rfl) ⟨44583, by rfl⟩) R89167
theorem R53535 : Reach 53535 := rs (se 1 (by rfl) ⟨40151, by rfl⟩) R80303
theorem R381257 : Reach 381257 := rs (se 2 (by rfl) ⟨142971, by rfl⟩) R285943
theorem R53595 : Reach 53595 := rs (se 1 (by rfl) ⟨40196, by rfl⟩) R80393
theorem R86383 : Reach 86383 := rs (se 1 (by rfl) ⟨64787, by rfl⟩) R129575
theorem R53615 : Reach 53615 := rs (se 1 (by rfl) ⟨40211, by rfl⟩) R80423
theorem R53671 : Reach 53671 := rs (se 1 (by rfl) ⟨40253, by rfl⟩) R80507
theorem R53755 : Reach 53755 := rs (se 1 (by rfl) ⟨40316, by rfl⟩) R80633
theorem R938557 : Reach 938557 := rs (se 3 (by rfl) ⟨175979, by rfl⟩) R351959
theorem R709181 : Reach 709181 := rs (se 3 (by rfl) ⟨132971, by rfl⟩) R265943
theorem R53823 : Reach 53823 := rs (se 1 (by rfl) ⟨40367, by rfl⟩) R80735
theorem R53831 : Reach 53831 := rs (se 1 (by rfl) ⟨40373, by rfl⟩) R80747
theorem R119375 : Reach 119375 := rs (se 1 (by rfl) ⟨89531, by rfl⟩) R179063
theorem R53855 : Reach 53855 := rs (se 1 (by rfl) ⟨40391, by rfl⟩) R80783
theorem R185003 : Reach 185003 := rs (se 1 (by rfl) ⟨138752, by rfl⟩) R277505
theorem R53935 : Reach 53935 := rs (se 1 (by rfl) ⟨40451, by rfl⟩) R80903
theorem R119519 : Reach 119519 := rs (se 1 (by rfl) ⟨89639, by rfl⟩) R179279
theorem R53983 : Reach 53983 := rs (se 1 (by rfl) ⟨40487, by rfl⟩) R80975
theorem R54063 : Reach 54063 := rs (se 1 (by rfl) ⟨40547, by rfl⟩) R81095
theorem R54095 : Reach 54095 := rs (se 1 (by rfl) ⟨40571, by rfl⟩) R81143
theorem R54171 : Reach 54171 := rs (se 1 (by rfl) ⟨40628, by rfl⟩) R81257
theorem R54223 : Reach 54223 := rs (se 1 (by rfl) ⟨40667, by rfl⟩) R81335
theorem R119771 : Reach 119771 := rs (se 1 (by rfl) ⟨89828, by rfl⟩) R179657
theorem R54247 : Reach 54247 := rs (se 1 (by rfl) ⟨40685, by rfl⟩) R81371
theorem R152567 : Reach 152567 := rs (se 1 (by rfl) ⟨114425, by rfl⟩) R228851
theorem R119951 : Reach 119951 := rs (se 1 (by rfl) ⟨89963, by rfl⟩) R179927
theorem R185543 : Reach 185543 := rs (se 1 (by rfl) ⟨139157, by rfl⟩) R278315
theorem R251095 : Reach 251095 := rs (se 1 (by rfl) ⟨188321, by rfl⟩) R376643
theorem R54491 : Reach 54491 := rs (se 1 (by rfl) ⟨40868, by rfl⟩) R81737
theorem R251113 : Reach 251113 := rs (se 2 (by rfl) ⟨94167, by rfl⟩) R188335
theorem R120041 : Reach 120041 := rs (se 2 (by rfl) ⟨45015, by rfl⟩) R90031
theorem R120095 : Reach 120095 := rs (se 1 (by rfl) ⟨90071, by rfl⟩) R180143
theorem R54559 : Reach 54559 := rs (se 1 (by rfl) ⟨40919, by rfl⟩) R81839
theorem R54567 : Reach 54567 := rs (se 1 (by rfl) ⟨40925, by rfl⟩) R81851
theorem R54619 : Reach 54619 := rs (se 1 (by rfl) ⟨40964, by rfl⟩) R81929
theorem R54639 : Reach 54639 := rs (se 1 (by rfl) ⟨40979, by rfl⟩) R81959
theorem R87419 : Reach 87419 := rs (se 1 (by rfl) ⟨65564, by rfl⟩) R131129
theorem R54651 : Reach 54651 := rs (se 1 (by rfl) ⟨40988, by rfl⟩) R81977
theorem R54695 : Reach 54695 := rs (se 1 (by rfl) ⟨41021, by rfl⟩) R82043
theorem R54727 : Reach 54727 := rs (se 1 (by rfl) ⟨41045, by rfl⟩) R82091
theorem R54779 : Reach 54779 := rs (se 1 (by rfl) ⟨41084, by rfl⟩) R82169
theorem R54847 : Reach 54847 := rs (se 1 (by rfl) ⟨41135, by rfl⟩) R82271
theorem R54855 : Reach 54855 := rs (se 1 (by rfl) ⟨41141, by rfl⟩) R82283
theorem R54879 : Reach 54879 := rs (se 1 (by rfl) ⟨41159, by rfl⟩) R82319
theorem R54959 : Reach 54959 := rs (se 1 (by rfl) ⟨41219, by rfl⟩) R82439
theorem R55007 : Reach 55007 := rs (se 1 (by rfl) ⟨41255, by rfl⟩) R82511
theorem R120617 : Reach 120617 := rs (se 2 (by rfl) ⟨45231, by rfl⟩) R90463
theorem R55087 : Reach 55087 := rs (se 1 (by rfl) ⟨41315, by rfl⟩) R82631
theorem R55119 : Reach 55119 := rs (se 1 (by rfl) ⟨41339, by rfl⟩) R82679
theorem R2840777 : Reach 2840777 := rs (se 2 (by rfl) ⟨1065291, by rfl⟩) R2130583
theorem R88411 : Reach 88411 := rs (se 1 (by rfl) ⟨66308, by rfl⟩) R132617
theorem R55675 : Reach 55675 := rs (se 1 (by rfl) ⟨41756, by rfl⟩) R83513
theorem R186835 : Reach 186835 := rs (se 1 (by rfl) ⟨140126, by rfl⟩) R280253
theorem R514835 : Reach 514835 := rs (se 1 (by rfl) ⟨386126, by rfl⟩) R772253
theorem R121679 : Reach 121679 := rs (se 1 (by rfl) ⟨91259, by rfl⟩) R182519
theorem R121895 : Reach 121895 := rs (se 1 (by rfl) ⟨91421, by rfl⟩) R182843
theorem R122075 : Reach 122075 := rs (se 1 (by rfl) ⟨91556, by rfl⟩) R183113
theorem R220427 : Reach 220427 := rs (se 1 (by rfl) ⟨165320, by rfl⟩) R330641
theorem R89383 : Reach 89383 := rs (se 1 (by rfl) ⟨67037, by rfl⟩) R134075
theorem R220477 : Reach 220477 := rs (se 3 (by rfl) ⟨41339, by rfl⟩) R82679
theorem R122273 : Reach 122273 := rs (se 2 (by rfl) ⟨45852, by rfl⟩) R91705
theorem R122327 : Reach 122327 := rs (se 1 (by rfl) ⟨91745, by rfl⟩) R183491
theorem R253651 : Reach 253651 := rs (se 1 (by rfl) ⟨190238, by rfl⟩) R380477
theorem R89903 : Reach 89903 := rs (se 1 (by rfl) ⟨67427, by rfl⟩) R134855
theorem R548801 : Reach 548801 := rs (se 2 (by rfl) ⟨205800, by rfl⟩) R411601
theorem R122831 : Reach 122831 := rs (se 1 (by rfl) ⟨92123, by rfl⟩) R184247
theorem R385033 : Reach 385033 := rs (se 2 (by rfl) ⟨144387, by rfl⟩) R288775
theorem R1466545 : Reach 1466545 := rs (se 2 (by rfl) ⟨549954, by rfl⟩) R1099909
theorem R57631 : Reach 57631 := rs (se 1 (by rfl) ⟨43223, by rfl⟩) R86447
theorem R123209 : Reach 123209 := rs (se 2 (by rfl) ⟨46203, by rfl⟩) R92407
theorem R123227 : Reach 123227 := rs (se 1 (by rfl) ⟨92420, by rfl⟩) R184841
theorem R516577 : Reach 516577 := rs (se 2 (by rfl) ⟨193716, by rfl⟩) R387433
theorem R57919 : Reach 57919 := rs (se 1 (by rfl) ⟨43439, by rfl⟩) R86879
theorem R221867 : Reach 221867 := rs (se 1 (by rfl) ⟨166400, by rfl⟩) R332801
theorem R221879 : Reach 221879 := rs (se 1 (by rfl) ⟨166409, by rfl⟩) R332819
theorem R58159 : Reach 58159 := rs (se 1 (by rfl) ⟨43619, by rfl⟩) R87239
theorem R123803 : Reach 123803 := rs (se 1 (by rfl) ⟨92852, by rfl⟩) R185705
theorem R91111 : Reach 91111 := rs (se 1 (by rfl) ⟨68333, by rfl⟩) R136667
theorem R1532903 : Reach 1532903 := rs (se 1 (by rfl) ⟨1149677, by rfl⟩) R2299355
theorem R418823 : Reach 418823 := rs (se 1 (by rfl) ⟨314117, by rfl⟩) R628235
theorem R124001 : Reach 124001 := rs (se 2 (by rfl) ⟨46500, by rfl⟩) R93001
theorem R451889 : Reach 451889 := rs (se 2 (by rfl) ⟨169458, by rfl⟩) R338917
theorem R222551 : Reach 222551 := rs (se 1 (by rfl) ⟨166913, by rfl⟩) R333827
theorem R91489 : Reach 91489 := rs (se 2 (by rfl) ⟨34308, by rfl⟩) R68617
theorem R58747 : Reach 58747 := rs (se 1 (by rfl) ⟨44060, by rfl⟩) R88121
theorem R59215 : Reach 59215 := rs (se 1 (by rfl) ⟨44411, by rfl⟩) R88823
theorem R59611 : Reach 59611 := rs (se 1 (by rfl) ⟨44708, by rfl⟩) R89417
theorem R59899 : Reach 59899 := rs (se 1 (by rfl) ⟨44924, by rfl⟩) R89849
theorem R289403 : Reach 289403 := rs (se 1 (by rfl) ⟨217052, by rfl⟩) R434105
theorem R60079 : Reach 60079 := rs (se 1 (by rfl) ⟨45059, by rfl⟩) R90119
theorem R92947 : Reach 92947 := rs (se 1 (by rfl) ⟨69710, by rfl⟩) R139421
theorem R60367 : Reach 60367 := rs (se 1 (by rfl) ⟨45275, by rfl⟩) R90551
theorem R60763 : Reach 60763 := rs (se 1 (by rfl) ⟨45572, by rfl⟩) R91145
theorem R93563 : Reach 93563 := rs (se 1 (by rfl) ⟨70172, by rfl⟩) R140345
theorem R60871 : Reach 60871 := rs (se 1 (by rfl) ⟨45653, by rfl⟩) R91307
theorem R224851 : Reach 224851 := rs (se 1 (by rfl) ⟨168638, by rfl⟩) R337277
theorem R913069 : Reach 913069 := rs (se 3 (by rfl) ⟨171200, by rfl⟩) R342401
theorem R61231 : Reach 61231 := rs (se 1 (by rfl) ⟨45923, by rfl⟩) R91847
theorem R61339 : Reach 61339 := rs (se 1 (by rfl) ⟨46004, by rfl⟩) R92009
theorem R520141 : Reach 520141 := rs (se 3 (by rfl) ⟨97526, by rfl⟩) R195053
theorem R61735 : Reach 61735 := rs (se 1 (by rfl) ⟨46301, by rfl⟩) R92603
theorem R455017 : Reach 455017 := rs (se 2 (by rfl) ⟨170631, by rfl⟩) R341263
theorem R684395 : Reach 684395 := rs (se 1 (by rfl) ⟨513296, by rfl⟩) R1026593
theorem R61807 : Reach 61807 := rs (se 1 (by rfl) ⟨46355, by rfl⟩) R92711
theorem R127595 : Reach 127595 := rs (se 1 (by rfl) ⟨95696, by rfl⟩) R191393
theorem R914165 : Reach 914165 := rs (se 5 (by rfl) ⟨42851, by rfl⟩) R85703
theorem R1995637 : Reach 1995637 := rs (se 5 (by rfl) ⟨93545, by rfl⟩) R187091
theorem R95465 : Reach 95465 := rs (se 2 (by rfl) ⟨35799, by rfl⟩) R71599
theorem R358199 : Reach 358199 := rs (se 1 (by rfl) ⟨268649, by rfl⟩) R537299
theorem R194825 : Reach 194825 := rs (se 2 (by rfl) ⟨73059, by rfl⟩) R146119
theorem R260495 : Reach 260495 := rs (se 1 (by rfl) ⟨195371, by rfl⟩) R390743
theorem R129455 : Reach 129455 := rs (se 1 (by rfl) ⟨97091, by rfl⟩) R194183
theorem R457289 : Reach 457289 := rs (se 2 (by rfl) ⟨171483, by rfl⟩) R342967
theorem R293651 : Reach 293651 := rs (se 1 (by rfl) ⟨220238, by rfl⟩) R440477
theorem R392123 : Reach 392123 := rs (se 1 (by rfl) ⟨294092, by rfl⟩) R588185
theorem R228491 : Reach 228491 := rs (se 1 (by rfl) ⟨171368, by rfl⟩) R342737
theorem R130187 : Reach 130187 := rs (se 1 (by rfl) ⟨97640, by rfl⟩) R195281
theorem R64891 : Reach 64891 := rs (se 1 (by rfl) ⟨48668, by rfl⟩) R97337
theorem R294425 : Reach 294425 := rs (se 2 (by rfl) ⟨110409, by rfl⟩) R220819
theorem R196177 : Reach 196177 := rs (se 2 (by rfl) ⟨73566, by rfl⟩) R147133
theorem R130643 : Reach 130643 := rs (se 1 (by rfl) ⟨97982, by rfl⟩) R195965
theorem R65119 : Reach 65119 := rs (se 1 (by rfl) ⟨48839, by rfl⟩) R97679
theorem R65335 : Reach 65335 := rs (se 1 (by rfl) ⟨49001, by rfl⟩) R98003
theorem R294785 : Reach 294785 := rs (se 2 (by rfl) ⟨110544, by rfl⟩) R221089
theorem R753569 : Reach 753569 := rs (se 2 (by rfl) ⟨282588, by rfl⟩) R565177
theorem R131291 : Reach 131291 := rs (se 1 (by rfl) ⟨98468, by rfl⟩) R196937
theorem R65767 : Reach 65767 := rs (se 1 (by rfl) ⟨49325, by rfl⟩) R98651
theorem R98591 : Reach 98591 := rs (se 1 (by rfl) ⟨73943, by rfl⟩) R147887
theorem R262763 : Reach 262763 := rs (se 1 (by rfl) ⟨197072, by rfl⟩) R394145
theorem R688769 : Reach 688769 := rs (se 2 (by rfl) ⟨258288, by rfl⟩) R516577
theorem R197423 : Reach 197423 := rs (se 1 (by rfl) ⟨148067, by rfl⟩) R296135
theorem R66415 : Reach 66415 := rs (se 1 (by rfl) ⟨49811, by rfl⟩) R99623
theorem R525257 : Reach 525257 := rs (se 2 (by rfl) ⟨196971, by rfl⟩) R393943
theorem R328961 : Reach 328961 := rs (se 2 (by rfl) ⟨123360, by rfl⟩) R246721
theorem R132425 : Reach 132425 := rs (se 2 (by rfl) ⟨49659, by rfl⟩) R99319
theorem R132961 : Reach 132961 := rs (se 2 (by rfl) ⟨49860, by rfl⟩) R99721
theorem R231275 : Reach 231275 := rs (se 1 (by rfl) ⟨173456, by rfl⟩) R346913
theorem R67567 : Reach 67567 := rs (se 1 (by rfl) ⟨50675, by rfl⟩) R101351
theorem R264383 : Reach 264383 := rs (se 1 (by rfl) ⟨198287, by rfl⟩) R396575
theorem R297341 : Reach 297341 := rs (se 3 (by rfl) ⟨55751, by rfl⟩) R111503
theorem R231943 : Reach 231943 := rs (se 1 (by rfl) ⟨173957, by rfl⟩) R347915
theorem R199199 : Reach 199199 := rs (se 1 (by rfl) ⟨149399, by rfl⟩) R298799
theorem R199655 : Reach 199655 := rs (se 1 (by rfl) ⟨149741, by rfl⟩) R299483
theorem R101711 : Reach 101711 := rs (se 1 (by rfl) ⟨76283, by rfl⟩) R152567
theorem R135067 : Reach 135067 := rs (se 1 (by rfl) ⟨101300, by rfl⟩) R202601
theorem R69599 : Reach 69599 := rs (se 1 (by rfl) ⟨52199, by rfl⟩) R104399
theorem R201311 : Reach 201311 := rs (se 1 (by rfl) ⟨150983, by rfl⟩) R301967
theorem R299801 : Reach 299801 := rs (se 2 (by rfl) ⟨112425, by rfl⟩) R224851
theorem R267137 : Reach 267137 := rs (se 2 (by rfl) ⟨100176, by rfl⟩) R200353
theorem R1217425 : Reach 1217425 := rs (se 2 (by rfl) ⟨456534, by rfl⟩) R913069
theorem R267259 : Reach 267259 := rs (se 1 (by rfl) ⟨200444, by rfl⟩) R400889
theorem R136201 : Reach 136201 := rs (se 2 (by rfl) ⟨51075, by rfl⟩) R102151
theorem R693521 : Reach 693521 := rs (se 2 (by rfl) ⟨260070, by rfl⟩) R520141
theorem R365867 : Reach 365867 := rs (se 1 (by rfl) ⟨274400, by rfl⟩) R548801
theorem R267947 : Reach 267947 := rs (se 1 (by rfl) ⟨200960, by rfl⟩) R401921
theorem R268271 : Reach 268271 := rs (se 1 (by rfl) ⟨201203, by rfl⟩) R402407
theorem R1251409 : Reach 1251409 := rs (se 2 (by rfl) ⟨469278, by rfl⟩) R938557
theorem R301259 : Reach 301259 := rs (se 1 (by rfl) ⟨225944, by rfl⟩) R451889
theorem R530729 : Reach 530729 := rs (se 2 (by rfl) ⟨199023, by rfl⟩) R398047
theorem R4069757 : Reach 4069757 := rs (se 3 (by rfl) ⟨763079, by rfl⟩) R1526159
theorem R2660849 : Reach 2660849 := rs (se 2 (by rfl) ⟨997818, by rfl⟩) R1995637
theorem R334793 : Reach 334793 := rs (se 2 (by rfl) ⟨125547, by rfl⟩) R251095
theorem R334817 : Reach 334817 := rs (se 2 (by rfl) ⟨125556, by rfl⟩) R251113
theorem R204029 : Reach 204029 := rs (se 3 (by rfl) ⟨38255, by rfl⟩) R76511
theorem R269729 : Reach 269729 := rs (se 2 (by rfl) ⟨101148, by rfl⟩) R202297
theorem R73595 : Reach 73595 := rs (se 1 (by rfl) ⟨55196, by rfl⟩) R110393
theorem R74039 : Reach 74039 := rs (se 1 (by rfl) ⟨55529, by rfl⟩) R111059
theorem R74233 : Reach 74233 := rs (se 2 (by rfl) ⟨27837, by rfl⟩) R55675
theorem R238799 : Reach 238799 := rs (se 1 (by rfl) ⟨179099, by rfl⟩) R358199
theorem R173663 : Reach 173663 := rs (se 1 (by rfl) ⟨130247, by rfl⟩) R260495
theorem R304859 : Reach 304859 := rs (se 1 (by rfl) ⟨228644, by rfl⟩) R457289
theorem R272159 : Reach 272159 := rs (se 1 (by rfl) ⟨204119, by rfl⟩) R408239
theorem R75583 : Reach 75583 := rs (se 1 (by rfl) ⟨56687, by rfl⟩) R113375
theorem R108793 : Reach 108793 := rs (se 2 (by rfl) ⟨40797, by rfl⟩) R81595
theorem R338201 : Reach 338201 := rs (se 2 (by rfl) ⟨126825, by rfl⟩) R253651
theorem R207431 : Reach 207431 := rs (se 1 (by rfl) ⟨155573, by rfl⟩) R311147
theorem R502379 : Reach 502379 := rs (se 1 (by rfl) ⟨376784, by rfl⟩) R753569
theorem R76703 : Reach 76703 := rs (se 1 (by rfl) ⟨57527, by rfl⟩) R115055
theorem R76751 : Reach 76751 := rs (se 1 (by rfl) ⟨57563, by rfl⟩) R115127
theorem R175067 : Reach 175067 := rs (se 1 (by rfl) ⟨131300, by rfl⟩) R262601
theorem R76841 : Reach 76841 := rs (se 2 (by rfl) ⟨28815, by rfl⟩) R57631
theorem R76847 : Reach 76847 := rs (se 1 (by rfl) ⟨57635, by rfl⟩) R115271
theorem R273455 : Reach 273455 := rs (se 1 (by rfl) ⟨205091, by rfl⟩) R410183
theorem R76871 : Reach 76871 := rs (se 1 (by rfl) ⟨57653, by rfl⟩) R115307
theorem R502919 : Reach 502919 := rs (se 1 (by rfl) ⟨377189, by rfl⟩) R754379
theorem R175337 : Reach 175337 := rs (se 2 (by rfl) ⟨65751, by rfl⟩) R131503
theorem R77135 : Reach 77135 := rs (se 1 (by rfl) ⟨57851, by rfl⟩) R115703
theorem R666967 : Reach 666967 := rs (se 1 (by rfl) ⟨500225, by rfl⟩) R1000451
theorem R77225 : Reach 77225 := rs (se 2 (by rfl) ⟨28959, by rfl⟩) R57919
theorem R175607 : Reach 175607 := rs (se 1 (by rfl) ⟨131705, by rfl⟩) R263411
theorem R765449 : Reach 765449 := rs (se 2 (by rfl) ⟨287043, by rfl⟩) R574087
theorem R634391 : Reach 634391 := rs (se 1 (by rfl) ⟨475793, by rfl⟩) R951587
theorem R77375 : Reach 77375 := rs (se 1 (by rfl) ⟨58031, by rfl⟩) R116063
theorem R77545 : Reach 77545 := rs (se 2 (by rfl) ⟨29079, by rfl⟩) R58159
theorem R77639 : Reach 77639 := rs (se 1 (by rfl) ⟨58229, by rfl⟩) R116459
theorem R77723 : Reach 77723 := rs (se 1 (by rfl) ⟨58292, by rfl⟩) R116585
theorem R176251 : Reach 176251 := rs (se 1 (by rfl) ⟨132188, by rfl⟩) R264377
theorem R307547 : Reach 307547 := rs (se 1 (by rfl) ⟨230660, by rfl⟩) R461321
theorem R78287 : Reach 78287 := rs (se 1 (by rfl) ⟨58715, by rfl⟩) R117431
theorem R78329 : Reach 78329 := rs (se 2 (by rfl) ⟨29373, by rfl⟩) R58747
theorem R176633 : Reach 176633 := rs (se 2 (by rfl) ⟨66237, by rfl⟩) R132475
theorem R78431 : Reach 78431 := rs (se 1 (by rfl) ⟨58823, by rfl⟩) R117647
theorem R176903 : Reach 176903 := rs (se 1 (by rfl) ⟨132677, by rfl⟩) R265355
theorem R176957 : Reach 176957 := rs (se 3 (by rfl) ⟨33179, by rfl⟩) R66359
theorem R78911 : Reach 78911 := rs (se 1 (by rfl) ⟨59183, by rfl⟩) R118367
theorem R78953 : Reach 78953 := rs (se 2 (by rfl) ⟨29607, by rfl⟩) R59215
theorem R79055 : Reach 79055 := rs (se 1 (by rfl) ⟨59291, by rfl⟩) R118583
theorem R1520957 : Reach 1520957 := rs (se 3 (by rfl) ⟨285179, by rfl⟩) R570359
theorem R79259 : Reach 79259 := rs (se 1 (by rfl) ⟨59444, by rfl⟩) R118889
theorem R833111 : Reach 833111 := rs (se 1 (by rfl) ⟨624833, by rfl⟩) R1249667
theorem R79481 : Reach 79481 := rs (se 2 (by rfl) ⟨29805, by rfl⟩) R59611
theorem R472787 : Reach 472787 := rs (se 1 (by rfl) ⟨354590, by rfl⟩) R709181
theorem R79583 : Reach 79583 := rs (se 1 (by rfl) ⟨59687, by rfl⟩) R119375
theorem R177983 : Reach 177983 := rs (se 1 (by rfl) ⟨133487, by rfl⟩) R266975
theorem R79679 : Reach 79679 := rs (se 1 (by rfl) ⟨59759, by rfl⟩) R119519
theorem R79847 : Reach 79847 := rs (se 1 (by rfl) ⟨59885, by rfl⟩) R119771
theorem R79865 : Reach 79865 := rs (se 2 (by rfl) ⟨29949, by rfl⟩) R59899
theorem R374867 : Reach 374867 := rs (se 1 (by rfl) ⟨281150, by rfl⟩) R562301
theorem R79967 : Reach 79967 := rs (se 1 (by rfl) ⟨59975, by rfl⟩) R119951
theorem R80027 : Reach 80027 := rs (se 1 (by rfl) ⟨60020, by rfl⟩) R120041
theorem R80063 : Reach 80063 := rs (se 1 (by rfl) ⟨60047, by rfl⟩) R120095
theorem R80105 : Reach 80105 := rs (se 2 (by rfl) ⟨30039, by rfl⟩) R60079
theorem R80411 : Reach 80411 := rs (se 1 (by rfl) ⟨60308, by rfl⟩) R120617
theorem R80489 : Reach 80489 := rs (se 2 (by rfl) ⟨30183, by rfl⟩) R60367
theorem R81017 : Reach 81017 := rs (se 2 (by rfl) ⟨30381, by rfl⟩) R60763
theorem R343223 : Reach 343223 := rs (se 1 (by rfl) ⟨257417, by rfl⟩) R514835
theorem R81119 : Reach 81119 := rs (se 1 (by rfl) ⟨60839, by rfl⟩) R121679
theorem R81161 : Reach 81161 := rs (se 2 (by rfl) ⟨30435, by rfl⟩) R60871
theorem R179495 : Reach 179495 := rs (se 1 (by rfl) ⟨134621, by rfl⟩) R269243
theorem R81263 : Reach 81263 := rs (se 1 (by rfl) ⟨60947, by rfl⟩) R121895
theorem R310715 : Reach 310715 := rs (se 1 (by rfl) ⟨233036, by rfl⟩) R466073
theorem R81383 : Reach 81383 := rs (se 1 (by rfl) ⟨61037, by rfl⟩) R122075
theorem R146951 : Reach 146951 := rs (se 1 (by rfl) ⟨110213, by rfl⟩) R220427
theorem R81515 : Reach 81515 := rs (se 1 (by rfl) ⟨61136, by rfl⟩) R122273
theorem R81551 : Reach 81551 := rs (se 1 (by rfl) ⟨61163, by rfl⟩) R122327
theorem R81641 : Reach 81641 := rs (se 2 (by rfl) ⟨30615, by rfl⟩) R61231
theorem R81785 : Reach 81785 := rs (se 2 (by rfl) ⟨30669, by rfl⟩) R61339
theorem R81887 : Reach 81887 := rs (se 1 (by rfl) ⟨61415, by rfl⟩) R122831
theorem R180359 : Reach 180359 := rs (se 1 (by rfl) ⟨135269, by rfl⟩) R270539
theorem R2867339 : Reach 2867339 := rs (se 1 (by rfl) ⟨2150504, by rfl⟩) R4301009
theorem R82139 : Reach 82139 := rs (se 1 (by rfl) ⟨61604, by rfl⟩) R123209
theorem R82151 : Reach 82151 := rs (se 1 (by rfl) ⟨61613, by rfl⟩) R123227
theorem R147737 : Reach 147737 := rs (se 2 (by rfl) ⟨55401, by rfl⟩) R110803
theorem R82313 : Reach 82313 := rs (se 2 (by rfl) ⟨30867, by rfl⟩) R61735
theorem R147911 : Reach 147911 := rs (se 1 (by rfl) ⟨110933, by rfl⟩) R221867
theorem R147919 : Reach 147919 := rs (se 1 (by rfl) ⟨110939, by rfl⟩) R221879
theorem R606689 : Reach 606689 := rs (se 2 (by rfl) ⟨227508, by rfl⟩) R455017
theorem R115177 : Reach 115177 := rs (se 2 (by rfl) ⟨43191, by rfl⟩) R86383
theorem R82409 : Reach 82409 := rs (se 2 (by rfl) ⟨30903, by rfl⟩) R61807
theorem R82535 : Reach 82535 := rs (se 1 (by rfl) ⟨61901, by rfl⟩) R123803
theorem R705131 : Reach 705131 := rs (se 1 (by rfl) ⟨528848, by rfl⟩) R1057697
theorem R279215 : Reach 279215 := rs (se 1 (by rfl) ⟨209411, by rfl⟩) R418823
theorem R82667 : Reach 82667 := rs (se 1 (by rfl) ⟨62000, by rfl⟩) R124001
theorem R312173 : Reach 312173 := rs (se 3 (by rfl) ⟨58532, by rfl⟩) R117065
theorem R148367 : Reach 148367 := rs (se 1 (by rfl) ⟨111275, by rfl⟩) R222551
theorem R115667 : Reach 115667 := rs (se 1 (by rfl) ⟨86750, by rfl⟩) R173501
theorem R115919 : Reach 115919 := rs (se 1 (by rfl) ⟨86939, by rfl⟩) R173879
theorem R378283 : Reach 378283 := rs (se 1 (by rfl) ⟨283712, by rfl⟩) R567425
theorem R116243 : Reach 116243 := rs (se 1 (by rfl) ⟨87182, by rfl⟩) R174365
theorem R181871 : Reach 181871 := rs (se 1 (by rfl) ⟨136403, by rfl⟩) R272807
theorem R312947 : Reach 312947 := rs (se 1 (by rfl) ⟨234710, by rfl⟩) R469421
theorem R181979 : Reach 181979 := rs (se 1 (by rfl) ⟨136484, by rfl⟩) R272969
theorem R149377 : Reach 149377 := rs (se 2 (by rfl) ⟨56016, by rfl⟩) R112033
theorem R51183 : Reach 51183 := rs (se 1 (by rfl) ⟨38387, by rfl⟩) R76775
theorem R1427543 : Reach 1427543 := rs (se 1 (by rfl) ⟨1070657, by rfl⟩) R2141315
theorem R51355 : Reach 51355 := rs (se 1 (by rfl) ⟨38516, by rfl⟩) R77033
theorem R51391 : Reach 51391 := rs (se 1 (by rfl) ⟨38543, by rfl⟩) R77087
theorem R116927 : Reach 116927 := rs (se 1 (by rfl) ⟨87695, by rfl⟩) R175391
theorem R51503 : Reach 51503 := rs (se 1 (by rfl) ⟨38627, by rfl⟩) R77255
theorem R51739 : Reach 51739 := rs (se 1 (by rfl) ⟨38804, by rfl⟩) R77609
theorem R51743 : Reach 51743 := rs (se 1 (by rfl) ⟨38807, by rfl⟩) R77615
theorem R379667 : Reach 379667 := rs (se 1 (by rfl) ⟨284750, by rfl⟩) R569501
theorem R52059 : Reach 52059 := rs (se 1 (by rfl) ⟨39044, by rfl⟩) R78089
theorem R52127 : Reach 52127 := rs (se 1 (by rfl) ⟨39095, by rfl⟩) R78191
theorem R183275 : Reach 183275 := rs (se 1 (by rfl) ⟨137456, by rfl⟩) R274913
theorem R183329 : Reach 183329 := rs (se 2 (by rfl) ⟨68748, by rfl⟩) R137497
theorem R52271 : Reach 52271 := rs (se 1 (by rfl) ⟨39203, by rfl⟩) R78407
theorem R85063 : Reach 85063 := rs (se 1 (by rfl) ⟨63797, by rfl⟩) R127595
theorem R52295 : Reach 52295 := rs (se 1 (by rfl) ⟨39221, by rfl⟩) R78443
theorem R117881 : Reach 117881 := rs (se 2 (by rfl) ⟨44205, by rfl⟩) R88411
theorem R609443 : Reach 609443 := rs (se 1 (by rfl) ⟨457082, by rfl⟩) R914165
theorem R52447 : Reach 52447 := rs (se 1 (by rfl) ⟨39335, by rfl⟩) R78671
theorem R249113 : Reach 249113 := rs (se 2 (by rfl) ⟨93417, by rfl⟩) R186835
theorem R52711 : Reach 52711 := rs (se 1 (by rfl) ⟨39533, by rfl⟩) R79067
theorem R52827 : Reach 52827 := rs (se 1 (by rfl) ⟨39620, by rfl⟩) R79241
theorem R118547 : Reach 118547 := rs (se 1 (by rfl) ⟨88910, by rfl⟩) R177821
theorem R53063 : Reach 53063 := rs (se 1 (by rfl) ⟨39797, by rfl⟩) R79595
theorem R413585 : Reach 413585 := rs (se 2 (by rfl) ⟨155094, by rfl⟩) R310189
theorem R53215 : Reach 53215 := rs (se 1 (by rfl) ⟨39911, by rfl⟩) R79823
theorem R184301 : Reach 184301 := rs (se 3 (by rfl) ⟨34556, by rfl⟩) R69113
theorem R118907 : Reach 118907 := rs (se 1 (by rfl) ⟨89180, by rfl⟩) R178361
theorem R53479 : Reach 53479 := rs (se 1 (by rfl) ⟨40109, by rfl⟩) R80219
theorem R86303 : Reach 86303 := rs (se 1 (by rfl) ⟨64727, by rfl⟩) R129455
theorem R53631 : Reach 53631 := rs (se 1 (by rfl) ⟨40223, by rfl⟩) R80447
theorem R119177 : Reach 119177 := rs (se 2 (by rfl) ⟨44691, by rfl⟩) R89383
theorem R53711 : Reach 53711 := rs (se 1 (by rfl) ⟨40283, by rfl⟩) R80567
theorem R184787 : Reach 184787 := rs (se 1 (by rfl) ⟨138590, by rfl⟩) R277181
theorem R86521 : Reach 86521 := rs (se 2 (by rfl) ⟨32445, by rfl⟩) R64891
theorem R53863 : Reach 53863 := rs (se 1 (by rfl) ⟨40397, by rfl⟩) R80795
theorem R152225 : Reach 152225 := rs (se 2 (by rfl) ⟨57084, by rfl⟩) R114169
theorem R152327 : Reach 152327 := rs (se 1 (by rfl) ⟨114245, by rfl⟩) R228491
theorem R86791 : Reach 86791 := rs (se 1 (by rfl) ⟨65093, by rfl⟩) R130187
theorem R86825 : Reach 86825 := rs (se 2 (by rfl) ⟨32559, by rfl⟩) R65119
theorem R54127 : Reach 54127 := rs (se 1 (by rfl) ⟨40595, by rfl⟩) R81191
theorem R54183 : Reach 54183 := rs (se 1 (by rfl) ⟨40637, by rfl⟩) R81275
theorem R54267 : Reach 54267 := rs (se 1 (by rfl) ⟨40700, by rfl⟩) R81401
theorem R87095 : Reach 87095 := rs (se 1 (by rfl) ⟨65321, by rfl⟩) R130643
theorem R54335 : Reach 54335 := rs (se 1 (by rfl) ⟨40751, by rfl⟩) R81503
theorem R87113 : Reach 87113 := rs (se 2 (by rfl) ⟨32667, by rfl⟩) R65335
theorem R119915 : Reach 119915 := rs (se 1 (by rfl) ⟨89936, by rfl⟩) R179873
theorem R54447 : Reach 54447 := rs (se 1 (by rfl) ⟨40835, by rfl⟩) R81671
theorem R54479 : Reach 54479 := rs (se 1 (by rfl) ⟨40859, by rfl⟩) R81719
theorem R513377 : Reach 513377 := rs (se 2 (by rfl) ⟨192516, by rfl⟩) R385033
theorem R54683 : Reach 54683 := rs (se 1 (by rfl) ⟨41012, by rfl⟩) R82025
theorem R1955393 : Reach 1955393 := rs (se 2 (by rfl) ⟨733272, by rfl⟩) R1466545
theorem R54895 : Reach 54895 := rs (se 1 (by rfl) ⟨41171, by rfl⟩) R82343
theorem R54951 : Reach 54951 := rs (se 1 (by rfl) ⟨41213, by rfl⟩) R82427
theorem R120491 : Reach 120491 := rs (se 1 (by rfl) ⟨90368, by rfl⟩) R180737
theorem R55003 : Reach 55003 := rs (se 1 (by rfl) ⟨41252, by rfl⟩) R82505
theorem R55035 : Reach 55035 := rs (se 1 (by rfl) ⟨41276, by rfl⟩) R82553
theorem R55071 : Reach 55071 := rs (se 1 (by rfl) ⟨41303, by rfl⟩) R82607
theorem R87871 : Reach 87871 := rs (se 1 (by rfl) ⟨65903, by rfl⟩) R131807
theorem R55103 : Reach 55103 := rs (se 1 (by rfl) ⟨41327, by rfl⟩) R82655
theorem R219095 : Reach 219095 := rs (se 1 (by rfl) ⟨164321, by rfl⟩) R328643
theorem R120815 : Reach 120815 := rs (se 1 (by rfl) ⟨90611, by rfl⟩) R181223
theorem R153683 : Reach 153683 := rs (se 1 (by rfl) ⟨115262, by rfl⟩) R230525
theorem R121031 : Reach 121031 := rs (se 1 (by rfl) ⟨90773, by rfl⟩) R181547
theorem R841927 : Reach 841927 := rs (se 1 (by rfl) ⟨631445, by rfl⟩) R1262891
theorem R416015 : Reach 416015 := rs (se 1 (by rfl) ⟨312011, by rfl⟩) R624023
theorem R121211 : Reach 121211 := rs (se 1 (by rfl) ⟨90908, by rfl⟩) R181817
theorem R88607 : Reach 88607 := rs (se 1 (by rfl) ⟨66455, by rfl⟩) R132911
theorem R88681 : Reach 88681 := rs (se 2 (by rfl) ⟨33255, by rfl⟩) R66511
theorem R121481 : Reach 121481 := rs (se 2 (by rfl) ⟨45555, by rfl⟩) R91111
theorem R252715 : Reach 252715 := rs (se 1 (by rfl) ⟨189536, by rfl⟩) R379073
theorem R89039 : Reach 89039 := rs (se 1 (by rfl) ⟨66779, by rfl⟩) R133559
theorem R1530899 : Reach 1530899 := rs (se 1 (by rfl) ⟨1148174, by rfl⟩) R2296349
theorem R121985 : Reach 121985 := rs (se 2 (by rfl) ⟨45744, by rfl⟩) R91489
theorem R122039 : Reach 122039 := rs (se 1 (by rfl) ⟨91529, by rfl⟩) R183059
theorem R7625933 : Reach 7625933 := rs (se 3 (by rfl) ⟨1429862, by rfl⟩) R2859725
theorem R187859 : Reach 187859 := rs (se 1 (by rfl) ⟨140894, by rfl⟩) R281789
theorem R220751 : Reach 220751 := rs (se 1 (by rfl) ⟨165563, by rfl⟩) R331127
theorem R89707 : Reach 89707 := rs (se 1 (by rfl) ⟨67280, by rfl⟩) R134561
theorem R122615 : Reach 122615 := rs (se 1 (by rfl) ⟨91961, by rfl⟩) R183923
theorem R11951887 : Reach 11951887 := rs (se 1 (by rfl) ⟨8963915, by rfl⟩) R17927831
theorem R89977 : Reach 89977 := rs (se 2 (by rfl) ⟨33741, by rfl⟩) R67483
theorem R90011 : Reach 90011 := rs (se 1 (by rfl) ⟨67508, by rfl⟩) R135017
theorem R122795 : Reach 122795 := rs (se 1 (by rfl) ⟨92096, by rfl⟩) R184193
theorem R4087741 : Reach 4087741 := rs (se 3 (by rfl) ⟨766451, by rfl⟩) R1532903
theorem R155687 : Reach 155687 := rs (se 1 (by rfl) ⟨116765, by rfl⟩) R233531
theorem R254171 : Reach 254171 := rs (se 1 (by rfl) ⟨190628, by rfl⟩) R381257
theorem R123335 : Reach 123335 := rs (se 1 (by rfl) ⟨92501, by rfl⟩) R185003
theorem R254573 : Reach 254573 := rs (se 3 (by rfl) ⟨47732, by rfl⟩) R95465
theorem R123695 : Reach 123695 := rs (se 1 (by rfl) ⟨92771, by rfl⟩) R185543
theorem R58279 : Reach 58279 := rs (se 1 (by rfl) ⟨43709, by rfl⟩) R87419
theorem R91091 : Reach 91091 := rs (se 1 (by rfl) ⟨68318, by rfl⟩) R136637
theorem R123929 : Reach 123929 := rs (se 2 (by rfl) ⟨46473, by rfl⟩) R92947
theorem R91199 : Reach 91199 := rs (se 1 (by rfl) ⟨68399, by rfl⟩) R136799
theorem R3957923 : Reach 3957923 := rs (se 1 (by rfl) ⟨2968442, by rfl⟩) R5936885
theorem R1893851 : Reach 1893851 := rs (se 1 (by rfl) ⟨1420388, by rfl⟩) R2840777
theorem R91759 : Reach 91759 := rs (se 1 (by rfl) ⟨68819, by rfl⟩) R137639
theorem R91867 : Reach 91867 := rs (se 1 (by rfl) ⟨68900, by rfl⟩) R137801
theorem R190673 : Reach 190673 := rs (se 2 (by rfl) ⟨71502, by rfl⟩) R143005
theorem R354617 : Reach 354617 := rs (se 2 (by rfl) ⟨132981, by rfl⟩) R265963
theorem R289163 : Reach 289163 := rs (se 1 (by rfl) ⟨216872, by rfl⟩) R433745
theorem R59935 : Reach 59935 := rs (se 1 (by rfl) ⟨44951, by rfl⟩) R89903
theorem R389285 : Reach 389285 := rs (se 4 (by rfl) ⟨36495, by rfl⟩) R72991
theorem R192935 : Reach 192935 := rs (se 1 (by rfl) ⟨144701, by rfl⟩) R289403
theorem R62375 : Reach 62375 := rs (se 1 (by rfl) ⟨46781, by rfl⟩) R93563
theorem R456263 : Reach 456263 := rs (se 1 (by rfl) ⟨342197, by rfl⟩) R684395
theorem R129883 : Reach 129883 := rs (se 1 (by rfl) ⟨97412, by rfl⟩) R194825
theorem R293969 : Reach 293969 := rs (se 2 (by rfl) ⟨110238, by rfl⟩) R220477
theorem R195767 : Reach 195767 := rs (se 1 (by rfl) ⟨146825, by rfl⟩) R293651
theorem R261415 : Reach 261415 := rs (se 1 (by rfl) ⟨196061, by rfl⟩) R392123
theorem R261569 : Reach 261569 := rs (se 2 (by rfl) ⟨98088, by rfl⟩) R196177
theorem R196283 : Reach 196283 := rs (se 1 (by rfl) ⟨147212, by rfl⟩) R294425
theorem R98219 : Reach 98219 := rs (se 1 (by rfl) ⟨73664, by rfl⟩) R147329
theorem R196523 : Reach 196523 := rs (se 1 (by rfl) ⟨147392, by rfl⟩) R294785
theorem R98491 : Reach 98491 := rs (se 1 (by rfl) ⟨73868, by rfl⟩) R147737
theorem R459179 : Reach 459179 := rs (se 1 (by rfl) ⟨344384, by rfl⟩) R688769
theorem R131615 : Reach 131615 := rs (se 1 (by rfl) ⟨98711, by rfl⟩) R197423
theorem R98911 : Reach 98911 := rs (se 1 (by rfl) ⟨74183, by rfl⟩) R148367
theorem R197225 : Reach 197225 := rs (se 2 (by rfl) ⟨73959, by rfl⟩) R147919
theorem R98977 : Reach 98977 := rs (se 2 (by rfl) ⟨37116, by rfl⟩) R74233
theorem R230141 : Reach 230141 := rs (se 3 (by rfl) ⟨43151, by rfl⟩) R86303
theorem R262909 : Reach 262909 := rs (se 3 (by rfl) ⟨49295, by rfl⟩) R98591
theorem R197437 : Reach 197437 := rs (se 3 (by rfl) ⟨37019, by rfl⟩) R74039
theorem R951695 : Reach 951695 := rs (se 1 (by rfl) ⟨713771, by rfl⟩) R1427543
theorem R198227 : Reach 198227 := rs (se 1 (by rfl) ⟨148670, by rfl⟩) R297341
theorem R132799 : Reach 132799 := rs (se 1 (by rfl) ⟨99599, by rfl⟩) R199199
theorem R133103 : Reach 133103 := rs (se 1 (by rfl) ⟨99827, by rfl⟩) R199655
theorem R67807 : Reach 67807 := rs (se 1 (by rfl) ⟨50855, by rfl⟩) R101711
theorem R100777 : Reach 100777 := rs (se 2 (by rfl) ⟨37791, by rfl⟩) R75583
theorem R166333 : Reach 166333 := rs (se 3 (by rfl) ⟨31187, by rfl⟩) R62375
theorem R199169 : Reach 199169 := rs (se 2 (by rfl) ⟨74688, by rfl⟩) R149377
theorem R232301 : Reach 232301 := rs (se 3 (by rfl) ⟨43556, by rfl⟩) R87113
theorem R68521 : Reach 68521 := rs (se 2 (by rfl) ⟨25695, by rfl⟩) R51391
theorem R134207 : Reach 134207 := rs (se 1 (by rfl) ⟨100655, by rfl⟩) R201311
theorem R101483 : Reach 101483 := rs (se 1 (by rfl) ⟨76112, by rfl⟩) R152225
theorem R199867 : Reach 199867 := rs (se 1 (by rfl) ⟨149900, by rfl⟩) R299801
theorem R462347 : Reach 462347 := rs (se 1 (by rfl) ⟨346760, by rfl⟩) R693521
theorem R102455 : Reach 102455 := rs (se 1 (by rfl) ⟨76841, by rfl⟩) R153683
theorem R200839 : Reach 200839 := rs (se 1 (by rfl) ⟨150629, by rfl⟩) R301259
theorem R1773899 : Reach 1773899 := rs (se 1 (by rfl) ⟨1330424, by rfl⟩) R2660849
theorem R889289 : Reach 889289 := rs (se 2 (by rfl) ⟨333483, by rfl⟩) R666967
theorem R1020599 : Reach 1020599 := rs (se 1 (by rfl) ⟨765449, by rfl⟩) R1530899
theorem R1577717 : Reach 1577717 := rs (se 5 (by rfl) ⟨73955, by rfl⟩) R147911
theorem R5083955 : Reach 5083955 := rs (se 1 (by rfl) ⟨3812966, by rfl⟩) R7625933
theorem R136019 : Reach 136019 := rs (se 1 (by rfl) ⟨102014, by rfl⟩) R204029
theorem R103393 : Reach 103393 := rs (se 2 (by rfl) ⟨38772, by rfl⟩) R77545
theorem R169447 : Reach 169447 := rs (se 1 (by rfl) ⟨127085, by rfl⟩) R254171
theorem R235001 : Reach 235001 := rs (se 2 (by rfl) ⟨88125, by rfl⟩) R176251
theorem R169715 : Reach 169715 := rs (se 1 (by rfl) ⟨127286, by rfl⟩) R254573
theorem R203239 : Reach 203239 := rs (se 1 (by rfl) ⟨152429, by rfl⟩) R304859
theorem R236411 : Reach 236411 := rs (se 1 (by rfl) ⟨177308, by rfl⟩) R354617
theorem R138287 : Reach 138287 := rs (se 1 (by rfl) ⟨103715, by rfl⟩) R207431
theorem R334919 : Reach 334919 := rs (se 1 (by rfl) ⟨251189, by rfl⟩) R502379
theorem R335279 : Reach 335279 := rs (se 1 (by rfl) ⟨251459, by rfl⟩) R502919
theorem R205031 : Reach 205031 := rs (se 1 (by rfl) ⟨153773, by rfl⟩) R307547
theorem R1122569 : Reach 1122569 := rs (se 2 (by rfl) ⟨420963, by rfl⟩) R841927
theorem R664301 : Reach 664301 := rs (se 3 (by rfl) ⟨124556, by rfl⟩) R249113
theorem R304175 : Reach 304175 := rs (se 1 (by rfl) ⟨228131, by rfl⟩) R456263
theorem R336953 : Reach 336953 := rs (se 2 (by rfl) ⟨126357, by rfl⟩) R252715
theorem R173177 : Reach 173177 := rs (se 2 (by rfl) ⟨64941, by rfl⟩) R129883
theorem R697517 : Reach 697517 := rs (se 3 (by rfl) ⟨130784, by rfl⟩) R261569
theorem R207143 : Reach 207143 := rs (se 1 (by rfl) ⟨155357, by rfl⟩) R310715
theorem R15935849 : Reach 15935849 := rs (se 2 (by rfl) ⟨5975943, by rfl⟩) R11951887
theorem R5450321 : Reach 5450321 := rs (se 2 (by rfl) ⟨2043870, by rfl⟩) R4087741
theorem R1911559 : Reach 1911559 := rs (se 1 (by rfl) ⟨1433669, by rfl⟩) R2867339
theorem R404459 : Reach 404459 := rs (se 1 (by rfl) ⟨303344, by rfl⟩) R606689
theorem R470087 : Reach 470087 := rs (se 1 (by rfl) ⟨352565, by rfl⟩) R705131
theorem R175175 : Reach 175175 := rs (se 1 (by rfl) ⟨131381, by rfl⟩) R262763
theorem R208115 : Reach 208115 := rs (se 1 (by rfl) ⟨156086, by rfl⟩) R312173
theorem R77111 : Reach 77111 := rs (se 1 (by rfl) ⟨57833, by rfl⟩) R115667
theorem R77279 : Reach 77279 := rs (se 1 (by rfl) ⟨57959, by rfl⟩) R115919
theorem R77495 : Reach 77495 := rs (se 1 (by rfl) ⟨58121, by rfl⟩) R116243
theorem R208631 : Reach 208631 := rs (se 1 (by rfl) ⟨156473, by rfl⟩) R312947
theorem R77705 : Reach 77705 := rs (se 2 (by rfl) ⟨29139, by rfl⟩) R58279
theorem R77951 : Reach 77951 := rs (se 1 (by rfl) ⟨58463, by rfl⟩) R116927
theorem R176255 : Reach 176255 := rs (se 1 (by rfl) ⟨132191, by rfl⟩) R264383
theorem R504377 : Reach 504377 := rs (se 2 (by rfl) ⟨189141, by rfl⟩) R378283
theorem R406205 : Reach 406205 := rs (se 3 (by rfl) ⟨76163, by rfl⟩) R152327
theorem R78587 : Reach 78587 := rs (se 1 (by rfl) ⟨58940, by rfl⟩) R117881
theorem R406295 : Reach 406295 := rs (se 1 (by rfl) ⟨304721, by rfl⟩) R609443
theorem R177281 : Reach 177281 := rs (se 2 (by rfl) ⟨66480, by rfl⟩) R132961
theorem R79031 : Reach 79031 := rs (se 1 (by rfl) ⟨59273, by rfl⟩) R118547
theorem R275723 : Reach 275723 := rs (se 1 (by rfl) ⟨206792, by rfl⟩) R413585
theorem R79271 : Reach 79271 := rs (se 1 (by rfl) ⟨59453, by rfl⟩) R118907
theorem R79451 : Reach 79451 := rs (se 1 (by rfl) ⟨59588, by rfl⟩) R119177
theorem R636797 : Reach 636797 := rs (se 3 (by rfl) ⟨119399, by rfl⟩) R238799
theorem R178091 : Reach 178091 := rs (se 1 (by rfl) ⟨133568, by rfl⟩) R267137
theorem R309257 : Reach 309257 := rs (se 2 (by rfl) ⟨115971, by rfl⟩) R231943
theorem R79913 : Reach 79913 := rs (se 2 (by rfl) ⟨29967, by rfl⟩) R59935
theorem R79943 : Reach 79943 := rs (se 1 (by rfl) ⟨59957, by rfl⟩) R119915
theorem R243911 : Reach 243911 := rs (se 1 (by rfl) ⟨182933, by rfl⟩) R365867
theorem R342251 : Reach 342251 := rs (se 1 (by rfl) ⟨256688, by rfl⟩) R513377
theorem R178631 : Reach 178631 := rs (se 1 (by rfl) ⟨133973, by rfl⟩) R267947
theorem R80327 : Reach 80327 := rs (se 1 (by rfl) ⟨60245, by rfl⟩) R120491
theorem R146063 : Reach 146063 := rs (se 1 (by rfl) ⟨109547, by rfl⟩) R219095
theorem R178847 : Reach 178847 := rs (se 1 (by rfl) ⟨134135, by rfl⟩) R268271
theorem R80543 : Reach 80543 := rs (se 1 (by rfl) ⟨60407, by rfl⟩) R120815
theorem R113417 : Reach 113417 := rs (se 2 (by rfl) ⟨42531, by rfl⟩) R85063
theorem R80687 : Reach 80687 := rs (se 1 (by rfl) ⟨60515, by rfl⟩) R121031
theorem R277343 : Reach 277343 := rs (se 1 (by rfl) ⟨208007, by rfl⟩) R416015
theorem R80807 : Reach 80807 := rs (se 1 (by rfl) ⟨60605, by rfl⟩) R121211
theorem R80987 : Reach 80987 := rs (se 1 (by rfl) ⟨60740, by rfl⟩) R121481
theorem R81323 : Reach 81323 := rs (se 1 (by rfl) ⟨60992, by rfl⟩) R121985
theorem R81359 : Reach 81359 := rs (se 1 (by rfl) ⟨61019, by rfl⟩) R122039
theorem R179819 : Reach 179819 := rs (se 1 (by rfl) ⟨134864, by rfl⟩) R269729
theorem R147167 : Reach 147167 := rs (se 1 (by rfl) ⟨110375, by rfl⟩) R220751
theorem R81743 : Reach 81743 := rs (se 1 (by rfl) ⟨61307, by rfl⟩) R122615
theorem R180089 : Reach 180089 := rs (se 2 (by rfl) ⟨67533, by rfl⟩) R135067
theorem R81863 : Reach 81863 := rs (se 1 (by rfl) ⟨61397, by rfl⟩) R122795
theorem R82223 : Reach 82223 := rs (se 1 (by rfl) ⟨61667, by rfl⟩) R123335
theorem R82463 : Reach 82463 := rs (se 1 (by rfl) ⟨61847, by rfl⟩) R123695
theorem R115361 : Reach 115361 := rs (se 2 (by rfl) ⟨43260, by rfl⟩) R86521
theorem R82619 : Reach 82619 := rs (se 1 (by rfl) ⟨61964, by rfl⟩) R123929
theorem R2638615 : Reach 2638615 := rs (se 1 (by rfl) ⟨1978961, by rfl⟩) R3957923
theorem R1262567 : Reach 1262567 := rs (se 1 (by rfl) ⟨946925, by rfl⟩) R1893851
theorem R115721 : Reach 115721 := rs (se 2 (by rfl) ⟨43395, by rfl⟩) R86791
theorem R115775 : Reach 115775 := rs (se 1 (by rfl) ⟨86831, by rfl⟩) R173663
theorem R181439 : Reach 181439 := rs (se 1 (by rfl) ⟨136079, by rfl⟩) R272159
theorem R1623233 : Reach 1623233 := rs (se 2 (by rfl) ⟨608712, by rfl⟩) R1217425
theorem R181601 : Reach 181601 := rs (se 2 (by rfl) ⟨68100, by rfl⟩) R136201
theorem R51135 : Reach 51135 := rs (se 1 (by rfl) ⟨38351, by rfl⟩) R76703
theorem R51167 : Reach 51167 := rs (se 1 (by rfl) ⟨38375, by rfl⟩) R76751
theorem R116711 : Reach 116711 := rs (se 1 (by rfl) ⟨87533, by rfl⟩) R175067
theorem R51227 : Reach 51227 := rs (se 1 (by rfl) ⟨38420, by rfl⟩) R76841
theorem R51231 : Reach 51231 := rs (se 1 (by rfl) ⟨38423, by rfl⟩) R76847
theorem R182303 : Reach 182303 := rs (se 1 (by rfl) ⟨136727, by rfl⟩) R273455
theorem R51247 : Reach 51247 := rs (se 1 (by rfl) ⟨38435, by rfl⟩) R76871
theorem R116891 : Reach 116891 := rs (se 1 (by rfl) ⟨87668, by rfl⟩) R175337
theorem R51423 : Reach 51423 := rs (se 1 (by rfl) ⟨38567, by rfl⟩) R77135
theorem R51483 : Reach 51483 := rs (se 1 (by rfl) ⟨38612, by rfl⟩) R77225
theorem R117071 : Reach 117071 := rs (se 1 (by rfl) ⟨87803, by rfl⟩) R175607
theorem R510299 : Reach 510299 := rs (se 1 (by rfl) ⟨382724, by rfl⟩) R765449
theorem R51583 : Reach 51583 := rs (se 1 (by rfl) ⟨38687, by rfl⟩) R77375
theorem R117161 : Reach 117161 := rs (se 2 (by rfl) ⟨43935, by rfl⟩) R87871
theorem R51759 : Reach 51759 := rs (se 1 (by rfl) ⟨38819, by rfl⟩) R77639
theorem R51815 : Reach 51815 := rs (se 1 (by rfl) ⟨38861, by rfl⟩) R77723
theorem R52191 : Reach 52191 := rs (se 1 (by rfl) ⟨39143, by rfl⟩) R78287
theorem R52219 : Reach 52219 := rs (se 1 (by rfl) ⟨39164, by rfl⟩) R78329
theorem R117755 : Reach 117755 := rs (se 1 (by rfl) ⟨88316, by rfl⟩) R176633
theorem R52287 : Reach 52287 := rs (se 1 (by rfl) ⟨39215, by rfl⟩) R78431
theorem R117935 : Reach 117935 := rs (se 1 (by rfl) ⟨88451, by rfl⟩) R176903
theorem R117971 : Reach 117971 := rs (se 1 (by rfl) ⟨88478, by rfl⟩) R176957
theorem R52607 : Reach 52607 := rs (se 1 (by rfl) ⟨39455, by rfl⟩) R78911
theorem R52635 : Reach 52635 := rs (se 1 (by rfl) ⟨39476, by rfl⟩) R78953
theorem R52703 : Reach 52703 := rs (se 1 (by rfl) ⟨39527, by rfl⟩) R79055
theorem R118241 : Reach 118241 := rs (se 2 (by rfl) ⟨44340, by rfl⟩) R88681
theorem R52839 : Reach 52839 := rs (se 1 (by rfl) ⟨39629, by rfl⟩) R79259
theorem R52987 : Reach 52987 := rs (se 1 (by rfl) ⟨39740, by rfl⟩) R79481
theorem R315191 : Reach 315191 := rs (se 1 (by rfl) ⟨236393, by rfl⟩) R472787
theorem R53055 : Reach 53055 := rs (se 1 (by rfl) ⟨39791, by rfl⟩) R79583
theorem R118655 : Reach 118655 := rs (se 1 (by rfl) ⟨88991, by rfl⟩) R177983
theorem R53119 : Reach 53119 := rs (se 1 (by rfl) ⟨39839, by rfl⟩) R79679
theorem R53231 : Reach 53231 := rs (se 1 (by rfl) ⟨39923, by rfl⟩) R79847
theorem R53243 : Reach 53243 := rs (se 1 (by rfl) ⟨39932, by rfl⟩) R79865
theorem R249911 : Reach 249911 := rs (se 1 (by rfl) ⟨187433, by rfl⟩) R374867
theorem R53311 : Reach 53311 := rs (se 1 (by rfl) ⟨39983, by rfl⟩) R79967
theorem R53351 : Reach 53351 := rs (se 1 (by rfl) ⟨40013, by rfl⟩) R80027
theorem R53375 : Reach 53375 := rs (se 1 (by rfl) ⟨40031, by rfl⟩) R80063
theorem R53403 : Reach 53403 := rs (se 1 (by rfl) ⟨40052, by rfl⟩) R80105
theorem R53607 : Reach 53607 := rs (se 1 (by rfl) ⟨40205, by rfl⟩) R80411
theorem R348553 : Reach 348553 := rs (se 2 (by rfl) ⟨130707, by rfl⟩) R261415
theorem R53659 : Reach 53659 := rs (se 1 (by rfl) ⟨40244, by rfl⟩) R80489
theorem R54011 : Reach 54011 := rs (se 1 (by rfl) ⟨40508, by rfl⟩) R81017
theorem R119609 : Reach 119609 := rs (se 2 (by rfl) ⟨44853, by rfl⟩) R89707
theorem R54079 : Reach 54079 := rs (se 1 (by rfl) ⟨40559, by rfl⟩) R81119
theorem R54107 : Reach 54107 := rs (se 1 (by rfl) ⟨40580, by rfl⟩) R81161
theorem R119663 : Reach 119663 := rs (se 1 (by rfl) ⟨89747, by rfl⟩) R179495
theorem R54175 : Reach 54175 := rs (se 1 (by rfl) ⟨40631, by rfl⟩) R81263
theorem R54255 : Reach 54255 := rs (se 1 (by rfl) ⟨40691, by rfl⟩) R81383
theorem R54343 : Reach 54343 := rs (se 1 (by rfl) ⟨40757, by rfl⟩) R81515
theorem R54367 : Reach 54367 := rs (se 1 (by rfl) ⟨40775, by rfl⟩) R81551
theorem R54427 : Reach 54427 := rs (se 1 (by rfl) ⟨40820, by rfl⟩) R81641
theorem R119969 : Reach 119969 := rs (se 2 (by rfl) ⟨44988, by rfl⟩) R89977
theorem R54523 : Reach 54523 := rs (se 1 (by rfl) ⟨40892, by rfl⟩) R81785
theorem R185597 : Reach 185597 := rs (se 3 (by rfl) ⟨34799, by rfl⟩) R69599
theorem R54591 : Reach 54591 := rs (se 1 (by rfl) ⟨40943, by rfl⟩) R81887
theorem R120239 : Reach 120239 := rs (se 1 (by rfl) ⟨90179, by rfl⟩) R180359
theorem R415165 : Reach 415165 := rs (se 3 (by rfl) ⟨77843, by rfl⟩) R155687
theorem R87527 : Reach 87527 := rs (se 1 (by rfl) ⟨65645, by rfl⟩) R131291
theorem R54759 : Reach 54759 := rs (se 1 (by rfl) ⟨41069, by rfl⟩) R82139
theorem R54767 : Reach 54767 := rs (se 1 (by rfl) ⟨41075, by rfl⟩) R82151
theorem R54875 : Reach 54875 := rs (se 1 (by rfl) ⟨41156, by rfl⟩) R82313
theorem R87689 : Reach 87689 := rs (se 2 (by rfl) ⟨32883, by rfl⟩) R65767
theorem R54939 : Reach 54939 := rs (se 1 (by rfl) ⟨41204, by rfl⟩) R82409
theorem R55023 : Reach 55023 := rs (se 1 (by rfl) ⟨41267, by rfl⟩) R82535
theorem R186143 : Reach 186143 := rs (se 1 (by rfl) ⟨139607, by rfl⟩) R279215
theorem R55111 : Reach 55111 := rs (se 1 (by rfl) ⟨41333, by rfl⟩) R82667
theorem R350171 : Reach 350171 := rs (se 1 (by rfl) ⟨262628, by rfl⟩) R525257
theorem R153569 : Reach 153569 := rs (se 2 (by rfl) ⟨57588, by rfl⟩) R115177
theorem R88283 : Reach 88283 := rs (se 1 (by rfl) ⟨66212, by rfl⟩) R132425
theorem R121247 : Reach 121247 := rs (se 1 (by rfl) ⟨90935, by rfl⟩) R181871
theorem R121319 : Reach 121319 := rs (se 1 (by rfl) ⟨90989, by rfl⟩) R181979
theorem R88553 : Reach 88553 := rs (se 2 (by rfl) ⟨33207, by rfl⟩) R66415
theorem R580229 : Reach 580229 := rs (se 4 (by rfl) ⟨54396, by rfl⟩) R108793
theorem R122183 : Reach 122183 := rs (se 1 (by rfl) ⟨91637, by rfl⟩) R183275
theorem R122219 : Reach 122219 := rs (se 1 (by rfl) ⟨91664, by rfl⟩) R183329
theorem R122345 : Reach 122345 := rs (se 2 (by rfl) ⟨45879, by rfl⟩) R91759
theorem R122489 : Reach 122489 := rs (se 2 (by rfl) ⟨45933, by rfl⟩) R91867
theorem R90089 : Reach 90089 := rs (se 2 (by rfl) ⟨33783, by rfl⟩) R67567
theorem R122867 : Reach 122867 := rs (se 1 (by rfl) ⟨92150, by rfl⟩) R184301
theorem R123191 : Reach 123191 := rs (se 1 (by rfl) ⟨92393, by rfl⟩) R184787
theorem R57883 : Reach 57883 := rs (se 1 (by rfl) ⟨43412, by rfl⟩) R86825
theorem R877229 : Reach 877229 := rs (se 3 (by rfl) ⟨164480, by rfl⟩) R328961
theorem R58063 : Reach 58063 := rs (se 1 (by rfl) ⟨43547, by rfl⟩) R87095
theorem R1303595 : Reach 1303595 := rs (se 1 (by rfl) ⟨977696, by rfl⟩) R1955393
theorem R353819 : Reach 353819 := rs (se 1 (by rfl) ⟨265364, by rfl⟩) R530729
theorem R2713171 : Reach 2713171 := rs (se 1 (by rfl) ⟨2034878, by rfl⟩) R4069757
theorem R59071 : Reach 59071 := rs (se 1 (by rfl) ⟨44303, by rfl⟩) R88607
theorem R223195 : Reach 223195 := rs (se 1 (by rfl) ⟨167396, by rfl⟩) R334793
theorem R59359 : Reach 59359 := rs (se 1 (by rfl) ⟨44519, by rfl⟩) R89039
theorem R223211 : Reach 223211 := rs (se 1 (by rfl) ⟨167408, by rfl⟩) R334817
theorem R616733 : Reach 616733 := rs (se 3 (by rfl) ⟨115637, by rfl⟩) R231275
theorem R125239 : Reach 125239 := rs (se 1 (by rfl) ⟨93929, by rfl⟩) R187859
theorem R60007 : Reach 60007 := rs (se 1 (by rfl) ⟨45005, by rfl⟩) R90011
theorem R60727 : Reach 60727 := rs (se 1 (by rfl) ⟨45545, by rfl⟩) R91091
theorem R60799 : Reach 60799 := rs (se 1 (by rfl) ⟨45599, by rfl⟩) R91199
theorem R356345 : Reach 356345 := rs (se 2 (by rfl) ⟨133629, by rfl⟩) R267259
theorem R127115 : Reach 127115 := rs (se 1 (by rfl) ⟨95336, by rfl⟩) R190673
theorem R225467 : Reach 225467 := rs (se 1 (by rfl) ⟨169100, by rfl⟩) R338201
theorem R192775 : Reach 192775 := rs (se 1 (by rfl) ⟨144581, by rfl⟩) R289163
theorem R1012445 : Reach 1012445 := rs (se 3 (by rfl) ⟨189833, by rfl⟩) R379667
theorem R422927 : Reach 422927 := rs (se 1 (by rfl) ⟨317195, by rfl⟩) R634391
theorem R1668545 : Reach 1668545 := rs (se 2 (by rfl) ⟨625704, by rfl⟩) R1251409
theorem R259523 : Reach 259523 := rs (se 1 (by rfl) ⟨194642, by rfl⟩) R389285
theorem R128623 : Reach 128623 := rs (se 1 (by rfl) ⟨96467, by rfl⟩) R192935
theorem R1013971 : Reach 1013971 := rs (se 1 (by rfl) ⟨760478, by rfl⟩) R1520957
theorem R555407 : Reach 555407 := rs (se 1 (by rfl) ⟨416555, by rfl⟩) R833111
theorem R195979 : Reach 195979 := rs (se 1 (by rfl) ⟨146984, by rfl⟩) R293969
theorem R130511 : Reach 130511 := rs (se 1 (by rfl) ⟨97883, by rfl⟩) R195767
theorem R228815 : Reach 228815 := rs (se 1 (by rfl) ⟨171611, by rfl⟩) R343223
theorem R196253 : Reach 196253 := rs (se 3 (by rfl) ⟨36797, by rfl⟩) R73595
theorem R97967 : Reach 97967 := rs (se 1 (by rfl) ⟨73475, by rfl⟩) R146951
theorem R261917 : Reach 261917 := rs (se 3 (by rfl) ⟨49109, by rfl⟩) R98219
theorem R130855 : Reach 130855 := rs (se 1 (by rfl) ⟨98141, by rfl⟩) R196283
theorem R131015 : Reach 131015 := rs (se 1 (by rfl) ⟨98261, by rfl⟩) R196523
theorem R131321 : Reach 131321 := rs (se 2 (by rfl) ⟨49245, by rfl⟩) R98491
theorem R131483 : Reach 131483 := rs (se 1 (by rfl) ⟨98612, by rfl⟩) R197225
theorem R131881 : Reach 131881 := rs (se 2 (by rfl) ⟨49455, by rfl⟩) R98911
theorem R1082155 : Reach 1082155 := rs (se 1 (by rfl) ⟨811616, by rfl⟩) R1623233
theorem R131969 : Reach 131969 := rs (se 2 (by rfl) ⟨49488, by rfl⟩) R98977
theorem R132151 : Reach 132151 := rs (se 1 (by rfl) ⟨99113, by rfl⟩) R198227
theorem R263249 : Reach 263249 := rs (se 2 (by rfl) ⟨98718, by rfl⟩) R197437
theorem R132779 : Reach 132779 := rs (se 1 (by rfl) ⟨99584, by rfl⟩) R199169
theorem R67655 : Reach 67655 := rs (se 1 (by rfl) ⟨50741, by rfl⟩) R101483
theorem R1083941 : Reach 1083941 := rs (se 4 (by rfl) ⟨101619, by rfl⟩) R203239
theorem R297593 : Reach 297593 := rs (se 2 (by rfl) ⟨111597, by rfl⟩) R223195
theorem R166607 : Reach 166607 := rs (se 1 (by rfl) ⟨124955, by rfl⟩) R249911
theorem R68303 : Reach 68303 := rs (se 1 (by rfl) ⟨51227, by rfl⟩) R102455
theorem R1182599 : Reach 1182599 := rs (se 1 (by rfl) ⟨886949, by rfl⟩) R1773899
theorem R592859 : Reach 592859 := rs (se 1 (by rfl) ⟨444644, by rfl⟩) R889289
theorem R166985 : Reach 166985 := rs (se 2 (by rfl) ⟨62619, by rfl⟩) R125239
theorem R1051811 : Reach 1051811 := rs (se 1 (by rfl) ⟨788858, by rfl⟩) R1577717
theorem R134369 : Reach 134369 := rs (se 2 (by rfl) ⟨50388, by rfl⟩) R100777
theorem R233447 : Reach 233447 := rs (se 1 (by rfl) ⟨175085, by rfl⟩) R350171
theorem R102379 : Reach 102379 := rs (se 1 (by rfl) ⟨76784, by rfl⟩) R153569
theorem R266489 : Reach 266489 := rs (se 2 (by rfl) ⟨99933, by rfl⟩) R199867
theorem R496381 : Reach 496381 := rs (se 3 (by rfl) ⟨93071, by rfl⟩) R186143
theorem R136687 : Reach 136687 := rs (se 1 (by rfl) ⟨102515, by rfl⟩) R205031
theorem R267785 : Reach 267785 := rs (se 2 (by rfl) ⟨100419, by rfl⟩) R200839
theorem R464737 : Reach 464737 := rs (se 2 (by rfl) ⟨174276, by rfl⟩) R348553
theorem R202783 : Reach 202783 := rs (se 1 (by rfl) ⟨152087, by rfl⟩) R304175
theorem R465011 : Reach 465011 := rs (se 1 (by rfl) ⟨348758, by rfl⟩) R697517
theorem R235879 : Reach 235879 := rs (se 1 (by rfl) ⟨176909, by rfl⟩) R353819
theorem R137857 : Reach 137857 := rs (se 2 (by rfl) ⟨51696, by rfl⟩) R103393
theorem R138095 : Reach 138095 := rs (se 1 (by rfl) ⟨103571, by rfl⟩) R207143
theorem R10623899 : Reach 10623899 := rs (se 1 (by rfl) ⟨7967924, by rfl⟩) R15935849
theorem R269639 : Reach 269639 := rs (se 1 (by rfl) ⟨202229, by rfl⟩) R404459
theorem R171497 : Reach 171497 := rs (se 2 (by rfl) ⟨64311, by rfl⟩) R128623
theorem R138743 : Reach 138743 := rs (se 1 (by rfl) ⟨104057, by rfl⟩) R208115
theorem R139087 : Reach 139087 := rs (se 1 (by rfl) ⟨104315, by rfl⟩) R208631
theorem R237563 : Reach 237563 := rs (se 1 (by rfl) ⟨178172, by rfl⟩) R356345
theorem R1351961 : Reach 1351961 := rs (se 2 (by rfl) ⟨506985, by rfl⟩) R1013971
theorem R336251 : Reach 336251 := rs (se 1 (by rfl) ⟨252188, by rfl⟩) R504377
theorem R270803 : Reach 270803 := rs (se 1 (by rfl) ⟨203102, by rfl⟩) R406205
theorem R270863 : Reach 270863 := rs (se 1 (by rfl) ⟨203147, by rfl⟩) R406295
theorem R173015 : Reach 173015 := rs (se 1 (by rfl) ⟨129761, by rfl⟩) R259523
theorem R206171 : Reach 206171 := rs (se 1 (by rfl) ⟨154628, by rfl⟩) R309257
theorem R370271 : Reach 370271 := rs (se 1 (by rfl) ⟨277703, by rfl⟩) R555407
theorem R75611 : Reach 75611 := rs (se 1 (by rfl) ⟨56708, by rfl⟩) R113417
theorem R174473 : Reach 174473 := rs (se 2 (by rfl) ⟨65427, by rfl⟩) R130855
theorem R174611 : Reach 174611 := rs (se 1 (by rfl) ⟨130958, by rfl⟩) R261917
theorem R306119 : Reach 306119 := rs (se 1 (by rfl) ⟨229589, by rfl⟩) R459179
theorem R76907 : Reach 76907 := rs (se 1 (by rfl) ⟨57680, by rfl⟩) R115361
theorem R77147 : Reach 77147 := rs (se 1 (by rfl) ⟨57860, by rfl⟩) R115721
theorem R77177 : Reach 77177 := rs (se 2 (by rfl) ⟨28941, by rfl⟩) R57883
theorem R77183 : Reach 77183 := rs (se 1 (by rfl) ⟨57887, by rfl⟩) R115775
theorem R634463 : Reach 634463 := rs (se 1 (by rfl) ⟨475847, by rfl⟩) R951695
theorem R77417 : Reach 77417 := rs (se 2 (by rfl) ⟨29031, by rfl⟩) R58063
theorem R3518153 : Reach 3518153 := rs (se 2 (by rfl) ⟨1319307, by rfl⟩) R2638615
theorem R77807 : Reach 77807 := rs (se 1 (by rfl) ⟨58355, by rfl⟩) R116711
theorem R77927 : Reach 77927 := rs (se 1 (by rfl) ⟨58445, by rfl⟩) R116891
theorem R78047 : Reach 78047 := rs (se 1 (by rfl) ⟨58535, by rfl⟩) R117071
theorem R340199 : Reach 340199 := rs (se 1 (by rfl) ⟨255149, by rfl⟩) R510299
theorem R78107 : Reach 78107 := rs (se 1 (by rfl) ⟨58580, by rfl⟩) R117161
theorem R78503 : Reach 78503 := rs (se 1 (by rfl) ⟨58877, by rfl⟩) R117755
theorem R3617561 : Reach 3617561 := rs (se 2 (by rfl) ⟨1356585, by rfl⟩) R2713171
theorem R78623 : Reach 78623 := rs (se 1 (by rfl) ⟨58967, by rfl⟩) R117935
theorem R78647 : Reach 78647 := rs (se 1 (by rfl) ⟨58985, by rfl⟩) R117971
theorem R177065 : Reach 177065 := rs (se 2 (by rfl) ⟨66399, by rfl⟩) R132799
theorem R78761 : Reach 78761 := rs (se 2 (by rfl) ⟨29535, by rfl⟩) R59071
theorem R78827 : Reach 78827 := rs (se 1 (by rfl) ⟨59120, by rfl⟩) R118241
theorem R308231 : Reach 308231 := rs (se 1 (by rfl) ⟨231173, by rfl⟩) R462347
theorem R210127 : Reach 210127 := rs (se 1 (by rfl) ⟨157595, by rfl⟩) R315191
theorem R79103 : Reach 79103 := rs (se 1 (by rfl) ⟨59327, by rfl⟩) R118655
theorem R79145 : Reach 79145 := rs (se 2 (by rfl) ⟨29679, by rfl⟩) R59359
theorem R3389303 : Reach 3389303 := rs (se 1 (by rfl) ⟨2541977, by rfl⟩) R5083955
theorem R79739 : Reach 79739 := rs (se 1 (by rfl) ⟨59804, by rfl⟩) R119609
theorem R79775 : Reach 79775 := rs (se 1 (by rfl) ⟨59831, by rfl⟩) R119663
theorem R79979 : Reach 79979 := rs (se 1 (by rfl) ⟨59984, by rfl⟩) R119969
theorem R80009 : Reach 80009 := rs (se 2 (by rfl) ⟨30003, by rfl⟩) R60007
theorem R80159 : Reach 80159 := rs (se 1 (by rfl) ⟨60119, by rfl⟩) R120239
theorem R80831 : Reach 80831 := rs (se 1 (by rfl) ⟨60623, by rfl⟩) R121247
theorem R80879 : Reach 80879 := rs (se 1 (by rfl) ⟨60659, by rfl⟩) R121319
theorem R80969 : Reach 80969 := rs (se 2 (by rfl) ⟨30363, by rfl⟩) R60727
theorem R81065 : Reach 81065 := rs (se 2 (by rfl) ⟨30399, by rfl⟩) R60799
theorem R81455 : Reach 81455 := rs (se 1 (by rfl) ⟨61091, by rfl⟩) R122183
theorem R81479 : Reach 81479 := rs (se 1 (by rfl) ⟨61109, by rfl⟩) R122219
theorem R81563 : Reach 81563 := rs (se 1 (by rfl) ⟨61172, by rfl⟩) R122345
theorem R81659 : Reach 81659 := rs (se 1 (by rfl) ⟨61244, by rfl⟩) R122489
theorem R81911 : Reach 81911 := rs (se 1 (by rfl) ⟨61433, by rfl⟩) R122867
theorem R82127 : Reach 82127 := rs (se 1 (by rfl) ⟨61595, by rfl⟩) R123191
theorem R442867 : Reach 442867 := rs (se 1 (by rfl) ⟨332150, by rfl⟩) R664301
theorem R869063 : Reach 869063 := rs (se 1 (by rfl) ⟨651797, by rfl⟩) R1303595
theorem R115451 : Reach 115451 := rs (se 1 (by rfl) ⟨86588, by rfl⟩) R173177
theorem R148807 : Reach 148807 := rs (se 1 (by rfl) ⟨111605, by rfl⟩) R223211
theorem R411155 : Reach 411155 := rs (se 1 (by rfl) ⟨308366, by rfl⟩) R616733
theorem R313391 : Reach 313391 := rs (se 1 (by rfl) ⟨235043, by rfl⟩) R470087
theorem R116783 : Reach 116783 := rs (se 1 (by rfl) ⟨87587, by rfl⟩) R175175
theorem R51407 : Reach 51407 := rs (se 1 (by rfl) ⟨38555, by rfl⟩) R77111
theorem R51519 : Reach 51519 := rs (se 1 (by rfl) ⟨38639, by rfl⟩) R77279
theorem R51663 : Reach 51663 := rs (se 1 (by rfl) ⟨38747, by rfl⟩) R77495
theorem R51803 : Reach 51803 := rs (se 1 (by rfl) ⟨38852, by rfl⟩) R77705
theorem R51967 : Reach 51967 := rs (se 1 (by rfl) ⟨38975, by rfl⟩) R77951
theorem R117503 : Reach 117503 := rs (se 1 (by rfl) ⟨88127, by rfl⟩) R176255
theorem R84743 : Reach 84743 := rs (se 1 (by rfl) ⟨63557, by rfl⟩) R127115
theorem R150311 : Reach 150311 := rs (se 1 (by rfl) ⟨112733, by rfl⟩) R225467
theorem R674963 : Reach 674963 := rs (se 1 (by rfl) ⟨506222, by rfl⟩) R1012445
theorem R52391 : Reach 52391 := rs (se 1 (by rfl) ⟨39293, by rfl⟩) R78587
theorem R281951 : Reach 281951 := rs (se 1 (by rfl) ⟨211463, by rfl⟩) R422927
theorem R118187 : Reach 118187 := rs (se 1 (by rfl) ⟨88640, by rfl⟩) R177281
theorem R52687 : Reach 52687 := rs (se 1 (by rfl) ⟨39515, by rfl⟩) R79031
theorem R183815 : Reach 183815 := rs (se 1 (by rfl) ⟨137861, by rfl⟩) R275723
theorem R52847 : Reach 52847 := rs (se 1 (by rfl) ⟨39635, by rfl⟩) R79271
theorem R52967 : Reach 52967 := rs (se 1 (by rfl) ⟨39725, by rfl⟩) R79451
theorem R118727 : Reach 118727 := rs (se 1 (by rfl) ⟨89045, by rfl⟩) R178091
theorem R53275 : Reach 53275 := rs (se 1 (by rfl) ⟨39956, by rfl⟩) R79913
theorem R53295 : Reach 53295 := rs (se 1 (by rfl) ⟨39971, by rfl⟩) R79943
theorem R119087 : Reach 119087 := rs (se 1 (by rfl) ⟨89315, by rfl⟩) R178631
theorem R53551 : Reach 53551 := rs (se 1 (by rfl) ⟨40163, by rfl⟩) R80327
theorem R119231 : Reach 119231 := rs (se 1 (by rfl) ⟨89423, by rfl⟩) R178847
theorem R53695 : Reach 53695 := rs (se 1 (by rfl) ⟨40271, by rfl⟩) R80543
theorem R53791 : Reach 53791 := rs (se 1 (by rfl) ⟨40343, by rfl⟩) R80687
theorem R184895 : Reach 184895 := rs (se 1 (by rfl) ⟨138671, by rfl⟩) R277343
theorem R53871 : Reach 53871 := rs (se 1 (by rfl) ⟨40403, by rfl⟩) R80807
theorem R53991 : Reach 53991 := rs (se 1 (by rfl) ⟨40493, by rfl⟩) R80987
theorem R54215 : Reach 54215 := rs (se 1 (by rfl) ⟨40661, by rfl⟩) R81323
theorem R87007 : Reach 87007 := rs (se 1 (by rfl) ⟨65255, by rfl⟩) R130511
theorem R152543 : Reach 152543 := rs (se 1 (by rfl) ⟨114407, by rfl⟩) R228815
theorem R54239 : Reach 54239 := rs (se 1 (by rfl) ⟨40679, by rfl⟩) R81359
theorem R119879 : Reach 119879 := rs (se 1 (by rfl) ⟨89909, by rfl⟩) R179819
theorem R349373 : Reach 349373 := rs (se 3 (by rfl) ⟨65507, by rfl⟩) R131015
theorem R54495 : Reach 54495 := rs (se 1 (by rfl) ⟨40871, by rfl⟩) R81743
theorem R120059 : Reach 120059 := rs (se 1 (by rfl) ⟨90044, by rfl⟩) R180089
theorem R54575 : Reach 54575 := rs (se 1 (by rfl) ⟨40931, by rfl⟩) R81863
theorem R54815 : Reach 54815 := rs (se 1 (by rfl) ⟨41111, by rfl⟩) R82223
theorem R87743 : Reach 87743 := rs (se 1 (by rfl) ⟨65807, by rfl⟩) R131615
theorem R54975 : Reach 54975 := rs (se 1 (by rfl) ⟨41231, by rfl⟩) R82463
theorem R55079 : Reach 55079 := rs (se 1 (by rfl) ⟨41309, by rfl⟩) R82619
theorem R153427 : Reach 153427 := rs (se 1 (by rfl) ⟨115070, by rfl⟩) R230141
theorem R841711 : Reach 841711 := rs (se 1 (by rfl) ⟨631283, by rfl⟩) R1262567
theorem R120959 : Reach 120959 := rs (se 1 (by rfl) ⟨90719, by rfl⟩) R181439
theorem R121067 : Reach 121067 := rs (se 1 (by rfl) ⟨90800, by rfl⟩) R181601
theorem R88735 : Reach 88735 := rs (se 1 (by rfl) ⟨66551, by rfl⟩) R133103
theorem R121535 : Reach 121535 := rs (se 1 (by rfl) ⟨91151, by rfl⟩) R182303
theorem R154867 : Reach 154867 := rs (se 1 (by rfl) ⟨116150, by rfl⟩) R232301
theorem R89471 : Reach 89471 := rs (se 1 (by rfl) ⟨67103, by rfl⟩) R134207
theorem R90409 : Reach 90409 := rs (se 2 (by rfl) ⟨33903, by rfl⟩) R67807
theorem R680399 : Reach 680399 := rs (se 1 (by rfl) ⟨510299, by rfl⟩) R1020599
theorem R90679 : Reach 90679 := rs (se 1 (by rfl) ⟨68009, by rfl⟩) R136019
theorem R221777 : Reach 221777 := rs (se 2 (by rfl) ⟨83166, by rfl⟩) R166333
theorem R123731 : Reach 123731 := rs (se 1 (by rfl) ⟨92798, by rfl⟩) R185597
theorem R58351 : Reach 58351 := rs (se 1 (by rfl) ⟨43763, by rfl⟩) R87527
theorem R156667 : Reach 156667 := rs (se 1 (by rfl) ⟨117500, by rfl⟩) R235001
theorem R2548745 : Reach 2548745 := rs (se 2 (by rfl) ⟨955779, by rfl⟩) R1911559
theorem R58459 : Reach 58459 := rs (se 1 (by rfl) ⟨43844, by rfl⟩) R87689
theorem R91361 : Reach 91361 := rs (se 2 (by rfl) ⟨34260, by rfl⟩) R68521
theorem R1402181 : Reach 1402181 := rs (se 4 (by rfl) ⟨131454, by rfl⟩) R262909
theorem R58855 : Reach 58855 := rs (se 1 (by rfl) ⟨44141, by rfl⟩) R88283
theorem R59035 : Reach 59035 := rs (se 1 (by rfl) ⟨44276, by rfl⟩) R88553
theorem R386819 : Reach 386819 := rs (se 1 (by rfl) ⟨290114, by rfl⟩) R580229
theorem R157607 : Reach 157607 := rs (se 1 (by rfl) ⟨118205, by rfl⟩) R236411
theorem R452573 : Reach 452573 := rs (se 3 (by rfl) ⟨84857, by rfl⟩) R169715
theorem R92191 : Reach 92191 := rs (se 1 (by rfl) ⟨69143, by rfl⟩) R138287
theorem R223279 : Reach 223279 := rs (se 1 (by rfl) ⟨167459, by rfl⟩) R334919
theorem R223519 : Reach 223519 := rs (se 1 (by rfl) ⟨167639, by rfl⟩) R335279
theorem R60059 : Reach 60059 := rs (se 1 (by rfl) ⟨45044, by rfl⟩) R90089
theorem R748379 : Reach 748379 := rs (se 1 (by rfl) ⟨561284, by rfl⟩) R1122569
theorem R257033 : Reach 257033 := rs (se 2 (by rfl) ⟨96387, by rfl⟩) R192775
theorem R584819 : Reach 584819 := rs (se 1 (by rfl) ⟨438614, by rfl⟩) R877229
theorem R650429 : Reach 650429 := rs (se 3 (by rfl) ⟨121955, by rfl⟩) R243911
theorem R224635 : Reach 224635 := rs (se 1 (by rfl) ⟨168476, by rfl⟩) R336953
theorem R290789 : Reach 290789 := rs (se 4 (by rfl) ⟨27261, by rfl⟩) R54523
theorem R3633547 : Reach 3633547 := rs (se 1 (by rfl) ⟨2725160, by rfl⟩) R5450321
theorem R553553 : Reach 553553 := rs (se 2 (by rfl) ⟨207582, by rfl⟩) R415165
theorem R225929 : Reach 225929 := rs (se 2 (by rfl) ⟨84723, by rfl⟩) R169447
theorem R1112363 : Reach 1112363 := rs (se 1 (by rfl) ⟨834272, by rfl⟩) R1668545
theorem R424531 : Reach 424531 := rs (se 1 (by rfl) ⟨318398, by rfl⟩) R636797
theorem R228167 : Reach 228167 := rs (se 1 (by rfl) ⟨171125, by rfl⟩) R342251
theorem R97375 : Reach 97375 := rs (se 1 (by rfl) ⟨73031, by rfl⟩) R146063
theorem R261245 : Reach 261245 := rs (se 3 (by rfl) ⟨48983, by rfl⟩) R97967
theorem R261305 : Reach 261305 := rs (se 2 (by rfl) ⟨97989, by rfl⟩) R195979
theorem R130835 : Reach 130835 := rs (se 1 (by rfl) ⟨98126, by rfl⟩) R196253
theorem R98111 : Reach 98111 := rs (se 1 (by rfl) ⟨73583, by rfl⟩) R147167
theorem R590489 : Reach 590489 := rs (se 2 (by rfl) ⟨221433, by rfl⟩) R442867
theorem R1442873 : Reach 1442873 := rs (se 2 (by rfl) ⟨541077, by rfl⟩) R1082155
theorem R722627 : Reach 722627 := rs (se 1 (by rfl) ⟨541970, by rfl⟩) R1083941
theorem R198395 : Reach 198395 := rs (se 1 (by rfl) ⟨148796, by rfl⟩) R297593
theorem R198409 : Reach 198409 := rs (se 2 (by rfl) ⟨74403, by rfl⟩) R148807
theorem R100207 : Reach 100207 := rs (se 1 (by rfl) ⟨75155, by rfl⟩) R150311
theorem R788399 : Reach 788399 := rs (se 1 (by rfl) ⟨591299, by rfl⟩) R1182599
theorem R395239 : Reach 395239 := rs (se 1 (by rfl) ⟨296429, by rfl⟩) R592859
theorem R298025 : Reach 298025 := rs (se 2 (by rfl) ⟨111759, by rfl⟩) R223519
theorem R299513 : Reach 299513 := rs (se 2 (by rfl) ⟨112317, by rfl⟩) R224635
theorem R7082599 : Reach 7082599 := rs (se 1 (by rfl) ⟨5311949, by rfl⟩) R10623899
theorem R201629 : Reach 201629 := rs (se 3 (by rfl) ⟨37805, by rfl⟩) R75611
theorem R136505 : Reach 136505 := rs (se 2 (by rfl) ⟨51189, by rfl⟩) R102379
theorem R137447 : Reach 137447 := rs (se 1 (by rfl) ⟨103085, by rfl⟩) R206171
theorem R661841 : Reach 661841 := rs (se 2 (by rfl) ⟨248190, by rfl⟩) R496381
theorem R105071 : Reach 105071 := rs (se 1 (by rfl) ⟨78803, by rfl⟩) R157607
theorem R301715 : Reach 301715 := rs (se 1 (by rfl) ⟨226286, by rfl⟩) R452573
theorem R498919 : Reach 498919 := rs (se 1 (by rfl) ⟨374189, by rfl⟩) R748379
theorem R204079 : Reach 204079 := rs (se 1 (by rfl) ⟨153059, by rfl⟩) R306119
theorem R433619 : Reach 433619 := rs (se 1 (by rfl) ⟨325214, by rfl⟩) R650429
theorem R204569 : Reach 204569 := rs (se 2 (by rfl) ⟨76713, by rfl⟩) R153427
theorem R1122281 : Reach 1122281 := rs (se 2 (by rfl) ⟨420855, by rfl⟩) R841711
theorem R270377 : Reach 270377 := rs (se 2 (by rfl) ⟨101391, by rfl⟩) R202783
theorem R369035 : Reach 369035 := rs (se 1 (by rfl) ⟨276776, by rfl⟩) R553553
theorem R205487 : Reach 205487 := rs (se 1 (by rfl) ⟨154115, by rfl⟩) R308231
theorem R566041 : Reach 566041 := rs (se 2 (by rfl) ⟨212265, by rfl⟩) R424531
theorem R206489 : Reach 206489 := rs (se 2 (by rfl) ⟨77433, by rfl⟩) R154867
theorem R174163 : Reach 174163 := rs (se 1 (by rfl) ⟨130622, by rfl⟩) R261245
theorem R174203 : Reach 174203 := rs (se 1 (by rfl) ⟨130652, by rfl⟩) R261305
theorem R1190821 : Reach 1190821 := rs (se 4 (by rfl) ⟨111639, by rfl⟩) R223279
theorem R76967 : Reach 76967 := rs (se 1 (by rfl) ⟨57725, by rfl⟩) R115451
theorem R175499 : Reach 175499 := rs (se 1 (by rfl) ⟨131624, by rfl⟩) R263249
theorem R896669 : Reach 896669 := rs (se 3 (by rfl) ⟨168125, by rfl⟩) R336251
theorem R274103 : Reach 274103 := rs (se 1 (by rfl) ⟨205577, by rfl⟩) R411155
theorem R175841 : Reach 175841 := rs (se 2 (by rfl) ⟨65940, by rfl⟩) R131881
theorem R77801 : Reach 77801 := rs (se 2 (by rfl) ⟨29175, by rfl⟩) R58351
theorem R208889 : Reach 208889 := rs (se 2 (by rfl) ⟨78333, by rfl⟩) R156667
theorem R208927 : Reach 208927 := rs (se 1 (by rfl) ⟨156695, by rfl⟩) R313391
theorem R77855 : Reach 77855 := rs (se 1 (by rfl) ⟨58391, by rfl⟩) R116783
theorem R176201 : Reach 176201 := rs (se 2 (by rfl) ⟨66075, by rfl⟩) R132151
theorem R77945 : Reach 77945 := rs (se 2 (by rfl) ⟨29229, by rfl⟩) R58459
theorem R111071 : Reach 111071 := rs (se 1 (by rfl) ⟨83303, by rfl⟩) R166607
theorem R78335 : Reach 78335 := rs (se 1 (by rfl) ⟨58751, by rfl⟩) R117503
theorem R1258021 : Reach 1258021 := rs (se 4 (by rfl) ⟨117939, by rfl⟩) R235879
theorem R78473 : Reach 78473 := rs (se 2 (by rfl) ⟨29427, by rfl⟩) R58855
theorem R111323 : Reach 111323 := rs (se 1 (by rfl) ⟨83492, by rfl⟩) R166985
theorem R701207 : Reach 701207 := rs (se 1 (by rfl) ⟨525905, by rfl⟩) R1051811
theorem R78713 : Reach 78713 := rs (se 2 (by rfl) ⟨29517, by rfl⟩) R59035
theorem R78791 : Reach 78791 := rs (se 1 (by rfl) ⟨59093, by rfl⟩) R118187
theorem R406781 : Reach 406781 := rs (se 3 (by rfl) ⟨76271, by rfl⟩) R152543
theorem R79151 : Reach 79151 := rs (se 1 (by rfl) ⟨59363, by rfl⟩) R118727
theorem R177659 : Reach 177659 := rs (se 1 (by rfl) ⟨133244, by rfl⟩) R266489
theorem R79391 : Reach 79391 := rs (se 1 (by rfl) ⟨59543, by rfl⟩) R119087
theorem R79487 : Reach 79487 := rs (se 1 (by rfl) ⟨59615, by rfl⟩) R119231
theorem R931661 : Reach 931661 := rs (se 3 (by rfl) ⟨174686, by rfl⟩) R349373
theorem R79919 : Reach 79919 := rs (se 1 (by rfl) ⟨59939, by rfl⟩) R119879
theorem R14956597 : Reach 14956597 := rs (se 5 (by rfl) ⟨701090, by rfl⟩) R1402181
theorem R80039 : Reach 80039 := rs (se 1 (by rfl) ⟨60029, by rfl⟩) R120059
theorem R178523 : Reach 178523 := rs (se 1 (by rfl) ⟨133892, by rfl⟩) R267785
theorem R310007 : Reach 310007 := rs (se 1 (by rfl) ⟨232505, by rfl⟩) R465011
theorem R80639 : Reach 80639 := rs (se 1 (by rfl) ⟨60479, by rfl⟩) R120959
theorem R80711 : Reach 80711 := rs (se 1 (by rfl) ⟨60533, by rfl⟩) R121067
theorem R81023 : Reach 81023 := rs (se 1 (by rfl) ⟨60767, by rfl⟩) R121535
theorem R179759 : Reach 179759 := rs (se 1 (by rfl) ⟨134819, by rfl⟩) R269639
theorem R901307 : Reach 901307 := rs (se 1 (by rfl) ⟨675980, by rfl⟩) R1351961
theorem R180413 : Reach 180413 := rs (se 3 (by rfl) ⟨33827, by rfl⟩) R67655
theorem R180535 : Reach 180535 := rs (se 1 (by rfl) ⟨135401, by rfl⟩) R270803
theorem R180575 : Reach 180575 := rs (se 1 (by rfl) ⟨135431, by rfl⟩) R270863
theorem R147851 : Reach 147851 := rs (se 1 (by rfl) ⟨110888, by rfl⟩) R221777
theorem R82487 : Reach 82487 := rs (se 1 (by rfl) ⟨61865, by rfl⟩) R123731
theorem R115343 : Reach 115343 := rs (se 1 (by rfl) ⟨86507, by rfl⟩) R173015
theorem R246847 : Reach 246847 := rs (se 1 (by rfl) ⟨185135, by rfl⟩) R370271
theorem R116009 : Reach 116009 := rs (se 2 (by rfl) ⟨43503, by rfl⟩) R87007
theorem R116315 : Reach 116315 := rs (se 1 (by rfl) ⟨87236, by rfl⟩) R174473
theorem R280169 : Reach 280169 := rs (se 2 (by rfl) ⟨105063, by rfl⟩) R210127
theorem R116407 : Reach 116407 := rs (se 1 (by rfl) ⟨87305, by rfl⟩) R174611
theorem R182141 : Reach 182141 := rs (se 3 (by rfl) ⟨34151, by rfl⟩) R68303
theorem R182249 : Reach 182249 := rs (se 2 (by rfl) ⟨68343, by rfl⟩) R136687
theorem R51271 : Reach 51271 := rs (se 1 (by rfl) ⟨38453, by rfl⟩) R76907
theorem R51431 : Reach 51431 := rs (se 1 (by rfl) ⟨38573, by rfl⟩) R77147
theorem R51451 : Reach 51451 := rs (se 1 (by rfl) ⟨38588, by rfl⟩) R77177
theorem R51455 : Reach 51455 := rs (se 1 (by rfl) ⟨38591, by rfl⟩) R77183
theorem R51611 : Reach 51611 := rs (se 1 (by rfl) ⟨38708, by rfl⟩) R77417
theorem R2345435 : Reach 2345435 := rs (se 1 (by rfl) ⟨1759076, by rfl⟩) R3518153
theorem R51871 : Reach 51871 := rs (se 1 (by rfl) ⟨38903, by rfl⟩) R77807
theorem R51951 : Reach 51951 := rs (se 1 (by rfl) ⟨38963, by rfl⟩) R77927
theorem R52031 : Reach 52031 := rs (se 1 (by rfl) ⟨39023, by rfl⟩) R78047
theorem R52071 : Reach 52071 := rs (se 1 (by rfl) ⟨39053, by rfl⟩) R78107
theorem R150619 : Reach 150619 := rs (se 1 (by rfl) ⟨112964, by rfl⟩) R225929
theorem R52335 : Reach 52335 := rs (se 1 (by rfl) ⟨39251, by rfl⟩) R78503
theorem R2411707 : Reach 2411707 := rs (se 1 (by rfl) ⟨1808780, by rfl⟩) R3617561
theorem R52415 : Reach 52415 := rs (se 1 (by rfl) ⟨39311, by rfl⟩) R78623
theorem R52431 : Reach 52431 := rs (se 1 (by rfl) ⟨39323, by rfl⟩) R78647
theorem R118043 : Reach 118043 := rs (se 1 (by rfl) ⟨88532, by rfl⟩) R177065
theorem R52507 : Reach 52507 := rs (se 1 (by rfl) ⟨39380, by rfl⟩) R78761
theorem R52551 : Reach 52551 := rs (se 1 (by rfl) ⟨39413, by rfl⟩) R78827
theorem R52735 : Reach 52735 := rs (se 1 (by rfl) ⟨39551, by rfl⟩) R79103
theorem R183809 : Reach 183809 := rs (se 2 (by rfl) ⟨68928, by rfl⟩) R137857
theorem R52763 : Reach 52763 := rs (se 1 (by rfl) ⟨39572, by rfl⟩) R79145
theorem R118313 : Reach 118313 := rs (se 2 (by rfl) ⟨44367, by rfl⟩) R88735
theorem R53159 : Reach 53159 := rs (se 1 (by rfl) ⟨39869, by rfl⟩) R79739
theorem R53183 : Reach 53183 := rs (se 1 (by rfl) ⟨39887, by rfl⟩) R79775
theorem R53319 : Reach 53319 := rs (se 1 (by rfl) ⟨39989, by rfl⟩) R79979
theorem R53339 : Reach 53339 := rs (se 1 (by rfl) ⟨40004, by rfl⟩) R80009
theorem R53439 : Reach 53439 := rs (se 1 (by rfl) ⟨40079, by rfl⟩) R80159
theorem R741575 : Reach 741575 := rs (se 1 (by rfl) ⟨556181, by rfl⟩) R1112363
theorem R741797 : Reach 741797 := rs (se 4 (by rfl) ⟨69543, by rfl⟩) R139087
theorem R152111 : Reach 152111 := rs (se 1 (by rfl) ⟨114083, by rfl⟩) R228167
theorem R53887 : Reach 53887 := rs (se 1 (by rfl) ⟨40415, by rfl⟩) R80831
theorem R53919 : Reach 53919 := rs (se 1 (by rfl) ⟨40439, by rfl⟩) R80879
theorem R53979 : Reach 53979 := rs (se 1 (by rfl) ⟨40484, by rfl⟩) R80969
theorem R54043 : Reach 54043 := rs (se 1 (by rfl) ⟨40532, by rfl⟩) R81065
theorem R54303 : Reach 54303 := rs (se 1 (by rfl) ⟨40727, by rfl⟩) R81455
theorem R54319 : Reach 54319 := rs (se 1 (by rfl) ⟨40739, by rfl⟩) R81479
theorem R54375 : Reach 54375 := rs (se 1 (by rfl) ⟨40781, by rfl⟩) R81563
theorem R54439 : Reach 54439 := rs (se 1 (by rfl) ⟨40829, by rfl⟩) R81659
theorem R87223 : Reach 87223 := rs (se 1 (by rfl) ⟨65417, by rfl⟩) R130835
theorem R54607 : Reach 54607 := rs (se 1 (by rfl) ⟨40955, by rfl⟩) R81911
theorem R54751 : Reach 54751 := rs (se 1 (by rfl) ⟨41063, by rfl⟩) R82127
theorem R87547 : Reach 87547 := rs (se 1 (by rfl) ⟨65660, by rfl⟩) R131321
theorem R87655 : Reach 87655 := rs (se 1 (by rfl) ⟨65741, by rfl⟩) R131483
theorem R120545 : Reach 120545 := rs (se 2 (by rfl) ⟨45204, by rfl⟩) R90409
theorem R87979 : Reach 87979 := rs (se 1 (by rfl) ⟨65984, by rfl⟩) R131969
theorem R120905 : Reach 120905 := rs (se 2 (by rfl) ⟨45339, by rfl⟩) R90679
theorem R88519 : Reach 88519 := rs (se 1 (by rfl) ⟨66389, by rfl⟩) R132779
theorem R56495 : Reach 56495 := rs (se 1 (by rfl) ⟨42371, by rfl⟩) R84743
theorem R2317501 : Reach 2317501 := rs (se 3 (by rfl) ⟨434531, by rfl⟩) R869063
theorem R449975 : Reach 449975 := rs (se 1 (by rfl) ⟨337481, by rfl⟩) R674963
theorem R89579 : Reach 89579 := rs (se 1 (by rfl) ⟨67184, by rfl⟩) R134369
theorem R187967 : Reach 187967 := rs (se 1 (by rfl) ⟨140975, by rfl⟩) R281951
theorem R122543 : Reach 122543 := rs (se 1 (by rfl) ⟨91907, by rfl⟩) R183815
theorem R122921 : Reach 122921 := rs (se 2 (by rfl) ⟨46095, by rfl⟩) R92191
theorem R123263 : Reach 123263 := rs (se 1 (by rfl) ⟨92447, by rfl⟩) R184895
theorem R58495 : Reach 58495 := rs (se 1 (by rfl) ⟨43871, by rfl⟩) R87743
theorem R92063 : Reach 92063 := rs (se 1 (by rfl) ⟨69047, by rfl⟩) R138095
theorem R59647 : Reach 59647 := rs (se 1 (by rfl) ⟨44735, by rfl⟩) R89471
theorem R9038141 : Reach 9038141 := rs (se 3 (by rfl) ⟨1694651, by rfl⟩) R3389303
theorem R92495 : Reach 92495 := rs (se 1 (by rfl) ⟨69371, by rfl⟩) R138743
theorem R158375 : Reach 158375 := rs (se 1 (by rfl) ⟨118781, by rfl⟩) R237563
theorem R453599 : Reach 453599 := rs (se 1 (by rfl) ⟨340199, by rfl⟩) R680399
theorem R4844729 : Reach 4844729 := rs (se 2 (by rfl) ⟨1816773, by rfl⟩) R3633547
theorem R1699163 : Reach 1699163 := rs (se 1 (by rfl) ⟨1274372, by rfl⟩) R2548745
theorem R60907 : Reach 60907 := rs (se 1 (by rfl) ⟨45680, by rfl⟩) R91361
theorem R257879 : Reach 257879 := rs (se 1 (by rfl) ⟨193409, by rfl⟩) R386819
theorem R160157 : Reach 160157 := rs (se 3 (by rfl) ⟨30029, by rfl⟩) R60059
theorem R389879 : Reach 389879 := rs (se 1 (by rfl) ⟨292409, by rfl⟩) R584819
theorem R422975 : Reach 422975 := rs (se 1 (by rfl) ⟨317231, by rfl⟩) R634463
theorem R619649 : Reach 619649 := rs (se 2 (by rfl) ⟨232368, by rfl⟩) R464737
theorem R193859 : Reach 193859 := rs (se 1 (by rfl) ⟨145394, by rfl⟩) R290789
theorem R685421 : Reach 685421 := rs (se 3 (by rfl) ⟨128516, by rfl⟩) R257033
theorem R226799 : Reach 226799 := rs (se 1 (by rfl) ⟨170099, by rfl⟩) R340199
theorem R457325 : Reach 457325 := rs (se 3 (by rfl) ⟨85748, by rfl⟩) R171497
theorem R129833 : Reach 129833 := rs (se 2 (by rfl) ⟨48687, by rfl⟩) R97375
theorem R261629 : Reach 261629 := rs (se 3 (by rfl) ⟨49055, by rfl⟩) R98111
theorem R622525 : Reach 622525 := rs (se 3 (by rfl) ⟨116723, by rfl⟩) R233447
theorem R98567 : Reach 98567 := rs (se 1 (by rfl) ⟨73925, by rfl⟩) R147851
theorem R393659 : Reach 393659 := rs (se 1 (by rfl) ⟨295244, by rfl⟩) R590489
theorem R754721 : Reach 754721 := rs (se 2 (by rfl) ⟨283020, by rfl⟩) R566041
theorem R132263 : Reach 132263 := rs (se 1 (by rfl) ⟨99197, by rfl⟩) R198395
theorem R525599 : Reach 525599 := rs (se 1 (by rfl) ⟨394199, by rfl⟩) R788399
theorem R329129 : Reach 329129 := rs (se 2 (by rfl) ⟨123423, by rfl⟩) R246847
theorem R198683 : Reach 198683 := rs (se 1 (by rfl) ⟨149012, by rfl⟩) R298025
theorem R264545 : Reach 264545 := rs (se 2 (by rfl) ⟨99204, by rfl⟩) R198409
theorem R133609 : Reach 133609 := rs (se 2 (by rfl) ⟨50103, by rfl⟩) R100207
theorem R526985 : Reach 526985 := rs (se 2 (by rfl) ⟨197619, by rfl⟩) R395239
theorem R232217 : Reach 232217 := rs (se 2 (by rfl) ⟨87081, by rfl⟩) R174163
theorem R494383 : Reach 494383 := rs (se 1 (by rfl) ⟨370787, by rfl⟩) R741575
theorem R494531 : Reach 494531 := rs (se 1 (by rfl) ⟨370898, by rfl⟩) R741797
theorem R199675 : Reach 199675 := rs (se 1 (by rfl) ⟨149756, by rfl⟩) R299513
theorem R101407 : Reach 101407 := rs (se 1 (by rfl) ⟨76055, by rfl⟩) R152111
theorem R134419 : Reach 134419 := rs (se 1 (by rfl) ⟨100814, by rfl⟩) R201629
theorem R200825 : Reach 200825 := rs (se 2 (by rfl) ⟨75309, by rfl⟩) R150619
theorem R3215609 : Reach 3215609 := rs (se 2 (by rfl) ⟨1205853, by rfl⟩) R2411707
theorem R201143 : Reach 201143 := rs (se 1 (by rfl) ⟨150857, by rfl⟩) R301715
theorem R299983 : Reach 299983 := rs (se 1 (by rfl) ⟨224987, by rfl⟩) R449975
theorem R136379 : Reach 136379 := rs (se 1 (by rfl) ⟨102284, by rfl⟩) R204569
theorem R136991 : Reach 136991 := rs (se 1 (by rfl) ⟨102743, by rfl⟩) R205487
theorem R1677361 : Reach 1677361 := rs (se 2 (by rfl) ⟨629010, by rfl⟩) R1258021
theorem R9443465 : Reach 9443465 := rs (se 2 (by rfl) ⟨3541299, by rfl⟩) R7082599
theorem R137659 : Reach 137659 := rs (se 1 (by rfl) ⟨103244, by rfl⟩) R206489
theorem R302399 : Reach 302399 := rs (se 1 (by rfl) ⟨226799, by rfl⟩) R453599
theorem R597779 : Reach 597779 := rs (se 1 (by rfl) ⟨448334, by rfl⟩) R896669
theorem R171919 : Reach 171919 := rs (se 1 (by rfl) ⟨128939, by rfl⟩) R257879
theorem R139259 : Reach 139259 := rs (se 1 (by rfl) ⟨104444, by rfl⟩) R208889
theorem R106771 : Reach 106771 := rs (se 1 (by rfl) ⟨80078, by rfl⟩) R160157
theorem R74047 : Reach 74047 := rs (se 1 (by rfl) ⟨55535, by rfl⟩) R111071
theorem R74215 : Reach 74215 := rs (se 1 (by rfl) ⟨55661, by rfl⟩) R111323
theorem R12919277 : Reach 12919277 := rs (se 3 (by rfl) ⟨2422364, by rfl⟩) R4844729
theorem R467471 : Reach 467471 := rs (se 1 (by rfl) ⟨350603, by rfl⟩) R701207
theorem R271187 : Reach 271187 := rs (se 1 (by rfl) ⟨203390, by rfl⟩) R406781
theorem R501245 : Reach 501245 := rs (se 3 (by rfl) ⟨93983, by rfl⟩) R187967
theorem R3090001 : Reach 3090001 := rs (se 2 (by rfl) ⟨1158750, by rfl⟩) R2317501
theorem R665225 : Reach 665225 := rs (se 2 (by rfl) ⟨249459, by rfl⟩) R498919
theorem R272105 : Reach 272105 := rs (se 2 (by rfl) ⟨102039, by rfl⟩) R204079
theorem R304883 : Reach 304883 := rs (se 1 (by rfl) ⟨228662, by rfl⟩) R457325
theorem R206671 : Reach 206671 := rs (se 1 (by rfl) ⟨155003, by rfl⟩) R310007
theorem R174419 : Reach 174419 := rs (se 1 (by rfl) ⟨130814, by rfl⟩) R261629
theorem R830033 : Reach 830033 := rs (se 2 (by rfl) ⟨311262, by rfl⟩) R622525
theorem R600871 : Reach 600871 := rs (se 1 (by rfl) ⟨450653, by rfl⟩) R901307
theorem R240713 : Reach 240713 := rs (se 2 (by rfl) ⟨90267, by rfl⟩) R180535
theorem R76895 : Reach 76895 := rs (se 1 (by rfl) ⟨57671, by rfl⟩) R115343
theorem R961915 : Reach 961915 := rs (se 1 (by rfl) ⟨721436, by rfl⟩) R1442873
theorem R77339 : Reach 77339 := rs (se 1 (by rfl) ⟨58004, by rfl⟩) R116009
theorem R77543 : Reach 77543 := rs (se 1 (by rfl) ⟨58157, by rfl⟩) R116315
theorem R77993 : Reach 77993 := rs (se 2 (by rfl) ⟨29247, by rfl⟩) R58495
theorem R78695 : Reach 78695 := rs (se 1 (by rfl) ⟨59021, by rfl⟩) R118043
theorem R78875 : Reach 78875 := rs (se 1 (by rfl) ⟨59156, by rfl⟩) R118313
theorem R79529 : Reach 79529 := rs (se 2 (by rfl) ⟨29823, by rfl⟩) R59647
theorem R80363 : Reach 80363 := rs (se 1 (by rfl) ⟨60272, by rfl⟩) R120545
theorem R1587761 : Reach 1587761 := rs (se 2 (by rfl) ⟨595410, by rfl⟩) R1190821
theorem R80603 : Reach 80603 := rs (se 1 (by rfl) ⟨60452, by rfl⟩) R120905
theorem R441227 : Reach 441227 := rs (se 1 (by rfl) ⟨330920, by rfl⟩) R661841
theorem R81209 : Reach 81209 := rs (se 2 (by rfl) ⟨30453, by rfl⟩) R60907
theorem R81695 : Reach 81695 := rs (se 1 (by rfl) ⟨61271, by rfl⟩) R122543
theorem R180251 : Reach 180251 := rs (se 1 (by rfl) ⟨135188, by rfl⟩) R270377
theorem R81947 : Reach 81947 := rs (se 1 (by rfl) ⟨61460, by rfl⟩) R122921
theorem R278569 : Reach 278569 := rs (se 2 (by rfl) ⟨104463, by rfl⟩) R208927
theorem R82175 : Reach 82175 := rs (se 1 (by rfl) ⟨61631, by rfl⟩) R123263
theorem R246023 : Reach 246023 := rs (se 1 (by rfl) ⟨184517, by rfl⟩) R369035
theorem R246653 : Reach 246653 := rs (se 3 (by rfl) ⟨46247, by rfl⟩) R92495
theorem R116135 : Reach 116135 := rs (se 1 (by rfl) ⟨87101, by rfl⟩) R174203
theorem R116297 : Reach 116297 := rs (se 2 (by rfl) ⟨43611, by rfl⟩) R87223
theorem R280189 : Reach 280189 := rs (se 3 (by rfl) ⟨52535, by rfl⟩) R105071
theorem R116729 : Reach 116729 := rs (se 2 (by rfl) ⟨43773, by rfl⟩) R87547
theorem R51311 : Reach 51311 := rs (se 1 (by rfl) ⟨38483, by rfl⟩) R76967
theorem R116873 : Reach 116873 := rs (se 2 (by rfl) ⟨43827, by rfl⟩) R87655
theorem R1132775 : Reach 1132775 := rs (se 1 (by rfl) ⟨849581, by rfl⟩) R1699163
theorem R116999 : Reach 116999 := rs (se 1 (by rfl) ⟨87749, by rfl⟩) R175499
theorem R182735 : Reach 182735 := rs (se 1 (by rfl) ⟨137051, by rfl⟩) R274103
theorem R117227 : Reach 117227 := rs (se 1 (by rfl) ⟨87920, by rfl⟩) R175841
theorem R117305 : Reach 117305 := rs (se 2 (by rfl) ⟨43989, by rfl⟩) R87979
theorem R51867 : Reach 51867 := rs (se 1 (by rfl) ⟨38900, by rfl⟩) R77801
theorem R51903 : Reach 51903 := rs (se 1 (by rfl) ⟨38927, by rfl⟩) R77855
theorem R117467 : Reach 117467 := rs (se 1 (by rfl) ⟨88100, by rfl⟩) R176201
theorem R19942129 : Reach 19942129 := rs (se 2 (by rfl) ⟨7478298, by rfl⟩) R14956597
theorem R51963 : Reach 51963 := rs (se 1 (by rfl) ⟨38972, by rfl⟩) R77945
theorem R52223 : Reach 52223 := rs (se 1 (by rfl) ⟨39167, by rfl⟩) R78335
theorem R52315 : Reach 52315 := rs (se 1 (by rfl) ⟨39236, by rfl⟩) R78473
theorem R150653 : Reach 150653 := rs (se 3 (by rfl) ⟨28247, by rfl⟩) R56495
theorem R52475 : Reach 52475 := rs (se 1 (by rfl) ⟨39356, by rfl⟩) R78713
theorem R118025 : Reach 118025 := rs (se 2 (by rfl) ⟨44259, by rfl⟩) R88519
theorem R52527 : Reach 52527 := rs (se 1 (by rfl) ⟨39395, by rfl⟩) R78791
theorem R281983 : Reach 281983 := rs (se 1 (by rfl) ⟨211487, by rfl⟩) R422975
theorem R413099 : Reach 413099 := rs (se 1 (by rfl) ⟨309824, by rfl⟩) R619649
theorem R52767 : Reach 52767 := rs (se 1 (by rfl) ⟨39575, by rfl⟩) R79151
theorem R151199 : Reach 151199 := rs (se 1 (by rfl) ⟨113399, by rfl⟩) R226799
theorem R118439 : Reach 118439 := rs (se 1 (by rfl) ⟨88829, by rfl⟩) R177659
theorem R52927 : Reach 52927 := rs (se 1 (by rfl) ⟨39695, by rfl⟩) R79391
theorem R52991 : Reach 52991 := rs (se 1 (by rfl) ⟨39743, by rfl⟩) R79487
theorem R53279 : Reach 53279 := rs (se 1 (by rfl) ⟨39959, by rfl⟩) R79919
theorem R53359 : Reach 53359 := rs (se 1 (by rfl) ⟨40019, by rfl⟩) R80039
theorem R119015 : Reach 119015 := rs (se 1 (by rfl) ⟨89261, by rfl⟩) R178523
theorem R53759 : Reach 53759 := rs (se 1 (by rfl) ⟨40319, by rfl⟩) R80639
theorem R86555 : Reach 86555 := rs (se 1 (by rfl) ⟨64916, by rfl⟩) R129833
theorem R53807 : Reach 53807 := rs (se 1 (by rfl) ⟨40355, by rfl⟩) R80711
theorem R54015 : Reach 54015 := rs (se 1 (by rfl) ⟨40511, by rfl⟩) R81023
theorem R119839 : Reach 119839 := rs (se 1 (by rfl) ⟨89879, by rfl⟩) R179759
theorem R120275 : Reach 120275 := rs (se 1 (by rfl) ⟨90206, by rfl⟩) R180413
theorem R120383 : Reach 120383 := rs (se 1 (by rfl) ⟨90287, by rfl⟩) R180575
theorem R54991 : Reach 54991 := rs (se 1 (by rfl) ⟨41243, by rfl⟩) R82487
theorem R186779 : Reach 186779 := rs (se 1 (by rfl) ⟨140084, by rfl⟩) R280169
theorem R481751 : Reach 481751 := rs (se 1 (by rfl) ⟨361313, by rfl⟩) R722627
theorem R121427 : Reach 121427 := rs (se 1 (by rfl) ⟨91070, by rfl⟩) R182141
theorem R121499 : Reach 121499 := rs (se 1 (by rfl) ⟨91124, by rfl⟩) R182249
theorem R1563623 : Reach 1563623 := rs (se 1 (by rfl) ⟨1172717, by rfl⟩) R2345435
theorem R155209 : Reach 155209 := rs (se 2 (by rfl) ⟨58203, by rfl⟩) R116407
theorem R122539 : Reach 122539 := rs (se 1 (by rfl) ⟨91904, by rfl⟩) R183809
theorem R91003 : Reach 91003 := rs (se 1 (by rfl) ⟨68252, by rfl⟩) R136505
theorem R91631 : Reach 91631 := rs (se 1 (by rfl) ⟨68723, by rfl⟩) R137447
theorem R289079 : Reach 289079 := rs (se 1 (by rfl) ⟨216809, by rfl⟩) R433619
theorem R59719 : Reach 59719 := rs (se 1 (by rfl) ⟨44789, by rfl⟩) R89579
theorem R748187 : Reach 748187 := rs (se 1 (by rfl) ⟨561140, by rfl⟩) R1122281
theorem R61375 : Reach 61375 := rs (se 1 (by rfl) ⟨46031, by rfl⟩) R92063
theorem R6025427 : Reach 6025427 := rs (se 1 (by rfl) ⟨4519070, by rfl⟩) R9038141
theorem R61663 : Reach 61663 := rs (se 1 (by rfl) ⟨46247, by rfl⟩) R92495
theorem R422333 : Reach 422333 := rs (se 3 (by rfl) ⟨79187, by rfl⟩) R158375
theorem R259919 : Reach 259919 := rs (se 1 (by rfl) ⟨194939, by rfl⟩) R389879
theorem R129239 : Reach 129239 := rs (se 1 (by rfl) ⟨96929, by rfl⟩) R193859
theorem R456947 : Reach 456947 := rs (se 1 (by rfl) ⟨342710, by rfl⟩) R685421
theorem R621107 : Reach 621107 := rs (se 1 (by rfl) ⟨465830, by rfl⟩) R931661
theorem R164015 : Reach 164015 := rs (se 1 (by rfl) ⟨123011, by rfl⟩) R246023
theorem R65711 : Reach 65711 := rs (se 1 (by rfl) ⟨49283, by rfl⟩) R98567
theorem R262439 : Reach 262439 := rs (se 1 (by rfl) ⟨196829, by rfl⟩) R393659
theorem R98729 : Reach 98729 := rs (se 2 (by rfl) ⟨37023, by rfl⟩) R74047
theorem R164435 : Reach 164435 := rs (se 1 (by rfl) ⟨123326, by rfl⟩) R246653
theorem R132455 : Reach 132455 := rs (se 1 (by rfl) ⟨99341, by rfl⟩) R198683
theorem R755183 : Reach 755183 := rs (se 1 (by rfl) ⟨566387, by rfl⟩) R1132775
theorem R329687 : Reach 329687 := rs (se 1 (by rfl) ⟨247265, by rfl⟩) R494531
theorem R100435 : Reach 100435 := rs (se 1 (by rfl) ⟨75326, by rfl⟩) R150653
theorem R100799 : Reach 100799 := rs (se 1 (by rfl) ⟨75599, by rfl⟩) R151199
theorem R395813 : Reach 395813 := rs (se 4 (by rfl) ⟨37107, by rfl⟩) R74215
theorem R133883 : Reach 133883 := rs (se 1 (by rfl) ⟨100412, by rfl⟩) R200825
theorem R134095 : Reach 134095 := rs (se 1 (by rfl) ⟨100571, by rfl⟩) R201143
theorem R659177 : Reach 659177 := rs (se 2 (by rfl) ⟨247191, by rfl⟩) R494383
theorem R135209 : Reach 135209 := rs (se 2 (by rfl) ⟨50703, by rfl⟩) R101407
theorem R6295643 : Reach 6295643 := rs (se 1 (by rfl) ⟨4721732, by rfl⟩) R9443465
theorem R1282553 : Reach 1282553 := rs (se 2 (by rfl) ⟨480957, by rfl⟩) R961915
theorem R201599 : Reach 201599 := rs (se 1 (by rfl) ⟨151199, by rfl⟩) R302399
theorem R398519 : Reach 398519 := rs (se 1 (by rfl) ⟨298889, by rfl⟩) R597779
theorem R136829 : Reach 136829 := rs (se 3 (by rfl) ⟨25655, by rfl⟩) R51311
theorem R334163 : Reach 334163 := rs (se 1 (by rfl) ⟨250622, by rfl⟩) R501245
theorem R203255 : Reach 203255 := rs (se 1 (by rfl) ⟨152441, by rfl⟩) R304883
theorem R399977 : Reach 399977 := rs (se 2 (by rfl) ⟨149991, by rfl⟩) R299983
theorem R498791 : Reach 498791 := rs (se 1 (by rfl) ⟨374093, by rfl⟩) R748187
theorem R2236481 : Reach 2236481 := rs (se 2 (by rfl) ⟨838680, by rfl⟩) R1677361
theorem R173279 : Reach 173279 := rs (se 1 (by rfl) ⟨129959, by rfl⟩) R259919
theorem R304631 : Reach 304631 := rs (se 1 (by rfl) ⟨228473, by rfl⟩) R456947
theorem R1058507 : Reach 1058507 := rs (se 1 (by rfl) ⟨793880, by rfl⟩) R1587761
theorem R206945 : Reach 206945 := rs (se 2 (by rfl) ⟨77604, by rfl⟩) R155209
theorem R371425 : Reach 371425 := rs (se 2 (by rfl) ⟨139284, by rfl⟩) R278569
theorem R142361 : Reach 142361 := rs (se 2 (by rfl) ⟨53385, by rfl⟩) R106771
theorem R503147 : Reach 503147 := rs (se 1 (by rfl) ⟨377360, by rfl⟩) R754721
theorem R77423 : Reach 77423 := rs (se 1 (by rfl) ⟨58067, by rfl⟩) R116135
theorem R77531 : Reach 77531 := rs (se 1 (by rfl) ⟨58148, by rfl⟩) R116297
theorem R77819 : Reach 77819 := rs (se 1 (by rfl) ⟨58364, by rfl⟩) R116729
theorem R77915 : Reach 77915 := rs (se 1 (by rfl) ⟨58436, by rfl⟩) R116873
theorem R77999 : Reach 77999 := rs (se 1 (by rfl) ⟨58499, by rfl⟩) R116999
theorem R176363 : Reach 176363 := rs (se 1 (by rfl) ⟨132272, by rfl⟩) R264545
theorem R78203 : Reach 78203 := rs (se 1 (by rfl) ⟨58652, by rfl⟩) R117305
theorem R78311 : Reach 78311 := rs (se 1 (by rfl) ⟨58733, by rfl⟩) R117467
theorem R373585 : Reach 373585 := rs (se 2 (by rfl) ⟨140094, by rfl⟩) R280189
theorem R78683 : Reach 78683 := rs (se 1 (by rfl) ⟨59012, by rfl⟩) R118025
theorem R275399 : Reach 275399 := rs (se 1 (by rfl) ⟨206549, by rfl⟩) R413099
theorem R275561 : Reach 275561 := rs (se 2 (by rfl) ⟨103335, by rfl⟩) R206671
theorem R78959 : Reach 78959 := rs (se 1 (by rfl) ⟨59219, by rfl⟩) R118439
theorem R79343 : Reach 79343 := rs (se 1 (by rfl) ⟨59507, by rfl⟩) R119015
theorem R2143739 : Reach 2143739 := rs (se 1 (by rfl) ⟨1607804, by rfl⟩) R3215609
theorem R79625 : Reach 79625 := rs (se 2 (by rfl) ⟨29859, by rfl⟩) R59719
theorem R178145 : Reach 178145 := rs (se 2 (by rfl) ⟨66804, by rfl⟩) R133609
theorem R80183 : Reach 80183 := rs (se 1 (by rfl) ⟨60137, by rfl⟩) R120275
theorem R26589505 : Reach 26589505 := rs (se 2 (by rfl) ⟨9971064, by rfl⟩) R19942129
theorem R80255 : Reach 80255 := rs (se 1 (by rfl) ⟨60191, by rfl⟩) R120383
theorem R801161 : Reach 801161 := rs (se 2 (by rfl) ⟨300435, by rfl⟩) R600871
theorem R179225 : Reach 179225 := rs (se 2 (by rfl) ⟨67209, by rfl⟩) R134419
theorem R80951 : Reach 80951 := rs (se 1 (by rfl) ⟨60713, by rfl⟩) R121427
theorem R80999 : Reach 80999 := rs (se 1 (by rfl) ⟨60749, by rfl⟩) R121499
theorem R375977 : Reach 375977 := rs (se 2 (by rfl) ⟨140991, by rfl⟩) R281983
theorem R81833 : Reach 81833 := rs (se 2 (by rfl) ⟨30687, by rfl⟩) R61375
theorem R1064933 : Reach 1064933 := rs (se 4 (by rfl) ⟨99837, by rfl⟩) R199675
theorem R82217 : Reach 82217 := rs (se 2 (by rfl) ⟨30831, by rfl⟩) R61663
theorem R311647 : Reach 311647 := rs (se 1 (by rfl) ⟨233735, by rfl⟩) R467471
theorem R180791 : Reach 180791 := rs (se 1 (by rfl) ⟨135593, by rfl⟩) R271187
theorem R443483 : Reach 443483 := rs (se 1 (by rfl) ⟨332612, by rfl⟩) R665225
theorem R181403 : Reach 181403 := rs (se 1 (by rfl) ⟨136052, by rfl⟩) R272105
theorem R312605 : Reach 312605 := rs (se 3 (by rfl) ⟨58613, by rfl⟩) R117227
theorem R116279 : Reach 116279 := rs (se 1 (by rfl) ⟨87209, by rfl⟩) R174419
theorem R51263 : Reach 51263 := rs (se 1 (by rfl) ⟨38447, by rfl⟩) R76895
theorem R51559 : Reach 51559 := rs (se 1 (by rfl) ⟨38669, by rfl⟩) R77339
theorem R51695 : Reach 51695 := rs (se 1 (by rfl) ⟨38771, by rfl⟩) R77543
theorem R51995 : Reach 51995 := rs (se 1 (by rfl) ⟨38996, by rfl⟩) R77993
theorem R4016951 : Reach 4016951 := rs (se 1 (by rfl) ⟨3012713, by rfl⟩) R6025427
theorem R281555 : Reach 281555 := rs (se 1 (by rfl) ⟨211166, by rfl⟩) R422333
theorem R52463 : Reach 52463 := rs (se 1 (by rfl) ⟨39347, by rfl⟩) R78695
theorem R183545 : Reach 183545 := rs (se 2 (by rfl) ⟨68829, by rfl⟩) R137659
theorem R52583 : Reach 52583 := rs (se 1 (by rfl) ⟨39437, by rfl⟩) R78875
theorem R53019 : Reach 53019 := rs (se 1 (by rfl) ⟨39764, by rfl⟩) R79529
theorem R86159 : Reach 86159 := rs (se 1 (by rfl) ⟨64619, by rfl⟩) R129239
theorem R53575 : Reach 53575 := rs (se 1 (by rfl) ⟨40181, by rfl⟩) R80363
theorem R414071 : Reach 414071 := rs (se 1 (by rfl) ⟨310553, by rfl⟩) R621107
theorem R53735 : Reach 53735 := rs (se 1 (by rfl) ⟨40301, by rfl⟩) R80603
theorem R54139 : Reach 54139 := rs (se 1 (by rfl) ⟨40604, by rfl⟩) R81209
theorem R54463 : Reach 54463 := rs (se 1 (by rfl) ⟨40847, by rfl⟩) R81695
theorem R120167 : Reach 120167 := rs (se 1 (by rfl) ⟨90125, by rfl⟩) R180251
theorem R54631 : Reach 54631 := rs (se 1 (by rfl) ⟨40973, by rfl⟩) R81947
theorem R54783 : Reach 54783 := rs (se 1 (by rfl) ⟨41087, by rfl⟩) R82175
theorem R88175 : Reach 88175 := rs (se 1 (by rfl) ⟨66131, by rfl⟩) R132263
theorem R350399 : Reach 350399 := rs (se 1 (by rfl) ⟨262799, by rfl⟩) R525599
theorem R219419 : Reach 219419 := rs (se 1 (by rfl) ⟨164564, by rfl⟩) R329129
theorem R121337 : Reach 121337 := rs (se 2 (by rfl) ⟨45501, by rfl⟩) R91003
theorem R121823 : Reach 121823 := rs (se 1 (by rfl) ⟨91367, by rfl⟩) R182735
theorem R351323 : Reach 351323 := rs (se 1 (by rfl) ⟨263492, by rfl⟩) R526985
theorem R154811 : Reach 154811 := rs (se 1 (by rfl) ⟨116108, by rfl⟩) R232217
theorem R4120001 : Reach 4120001 := rs (se 2 (by rfl) ⟨1545000, by rfl⟩) R3090001
theorem R57703 : Reach 57703 := rs (se 1 (by rfl) ⟨43277, by rfl⟩) R86555
theorem R90919 : Reach 90919 := rs (se 1 (by rfl) ⟨68189, by rfl⟩) R136379
theorem R91327 : Reach 91327 := rs (se 1 (by rfl) ⟨68495, by rfl⟩) R136991
theorem R124519 : Reach 124519 := rs (se 1 (by rfl) ⟨93389, by rfl⟩) R186779
theorem R321167 : Reach 321167 := rs (se 1 (by rfl) ⟨240875, by rfl⟩) R481751
theorem R1042415 : Reach 1042415 := rs (se 1 (by rfl) ⟨781811, by rfl⟩) R1563623
theorem R92839 : Reach 92839 := rs (se 1 (by rfl) ⟨69629, by rfl⟩) R139259
theorem R8612851 : Reach 8612851 := rs (se 1 (by rfl) ⟨6459638, by rfl⟩) R12919277
theorem R61087 : Reach 61087 := rs (se 1 (by rfl) ⟨45815, by rfl⟩) R91631
theorem R159785 : Reach 159785 := rs (se 2 (by rfl) ⟨59919, by rfl⟩) R119839
theorem R192719 : Reach 192719 := rs (se 1 (by rfl) ⟨144539, by rfl⟩) R289079
theorem R553355 : Reach 553355 := rs (se 1 (by rfl) ⟨415016, by rfl⟩) R830033
theorem R160475 : Reach 160475 := rs (se 1 (by rfl) ⟨120356, by rfl⟩) R240713
theorem R294151 : Reach 294151 := rs (se 1 (by rfl) ⟨220613, by rfl⟩) R441227
theorem R163385 : Reach 163385 := rs (se 2 (by rfl) ⟨61269, by rfl⟩) R122539
theorem R229225 : Reach 229225 := rs (se 2 (by rfl) ⟨85959, by rfl⟩) R171919
theorem R65819 : Reach 65819 := rs (se 1 (by rfl) ⟨49364, by rfl⟩) R98729
theorem R295655 : Reach 295655 := rs (se 1 (by rfl) ⟨221741, by rfl⟩) R443483
theorem R67199 : Reach 67199 := rs (se 1 (by rfl) ⟨50399, by rfl⟩) R100799
theorem R427933 : Reach 427933 := rs (se 3 (by rfl) ⟨80237, by rfl⟩) R160475
theorem R166025 : Reach 166025 := rs (se 2 (by rfl) ⟨62259, by rfl⟩) R124519
theorem R4197095 : Reach 4197095 := rs (se 1 (by rfl) ⟨3147821, by rfl⟩) R6295643
theorem R133913 : Reach 133913 := rs (se 2 (by rfl) ⟨50217, by rfl⟩) R100435
theorem R855035 : Reach 855035 := rs (se 1 (by rfl) ⟨641276, by rfl⟩) R1282553
theorem R134399 : Reach 134399 := rs (se 1 (by rfl) ⟨100799, by rfl⟩) R201599
theorem R265679 : Reach 265679 := rs (se 1 (by rfl) ⟨199259, by rfl⟩) R398519
theorem R495233 : Reach 495233 := rs (se 2 (by rfl) ⟨185712, by rfl⟩) R371425
theorem R233599 : Reach 233599 := rs (se 1 (by rfl) ⟨175199, by rfl⟩) R350399
theorem R135503 : Reach 135503 := rs (se 1 (by rfl) ⟨101627, by rfl⟩) R203255
theorem R266651 : Reach 266651 := rs (se 1 (by rfl) ⟨199988, by rfl⟩) R399977
theorem R234215 : Reach 234215 := rs (se 1 (by rfl) ⟨175661, by rfl⟩) R351323
theorem R332527 : Reach 332527 := rs (se 1 (by rfl) ⟨249395, by rfl⟩) R498791
theorem R103207 : Reach 103207 := rs (se 1 (by rfl) ⟨77405, by rfl⟩) R154811
theorem R891101 : Reach 891101 := rs (se 3 (by rfl) ⟨167081, by rfl⟩) R334163
theorem R203087 : Reach 203087 := rs (se 1 (by rfl) ⟨152315, by rfl⟩) R304631
theorem R498113 : Reach 498113 := rs (se 2 (by rfl) ⟨186792, by rfl⟩) R373585
theorem R694943 : Reach 694943 := rs (se 1 (by rfl) ⟨521207, by rfl⟩) R1042415
theorem R137963 : Reach 137963 := rs (se 1 (by rfl) ⟨103472, by rfl⟩) R206945
theorem R1055501 : Reach 1055501 := rs (se 3 (by rfl) ⟨197906, by rfl⟩) R395813
theorem R335431 : Reach 335431 := rs (se 1 (by rfl) ⟨251573, by rfl⟩) R503147
theorem R106523 : Reach 106523 := rs (se 1 (by rfl) ⟨79892, by rfl⟩) R159785
theorem R368903 : Reach 368903 := rs (se 1 (by rfl) ⟨276677, by rfl⟩) R553355
theorem R534107 : Reach 534107 := rs (se 1 (by rfl) ⟨400580, by rfl⟩) R801161
theorem R108923 : Reach 108923 := rs (se 1 (by rfl) ⟨81692, by rfl⟩) R163385
theorem R305633 : Reach 305633 := rs (se 2 (by rfl) ⟨114612, by rfl⟩) R229225
theorem R109343 : Reach 109343 := rs (se 1 (by rfl) ⟨82007, by rfl⟩) R164015
theorem R174959 : Reach 174959 := rs (se 1 (by rfl) ⟨131219, by rfl⟩) R262439
theorem R175229 : Reach 175229 := rs (se 3 (by rfl) ⟨32855, by rfl⟩) R65711
theorem R76937 : Reach 76937 := rs (se 2 (by rfl) ⟨28851, by rfl⟩) R57703
theorem R208403 : Reach 208403 := rs (se 1 (by rfl) ⟨156302, by rfl⟩) R312605
theorem R503455 : Reach 503455 := rs (se 1 (by rfl) ⟨377591, by rfl⟩) R755183
theorem R77519 : Reach 77519 := rs (se 1 (by rfl) ⟨58139, by rfl⟩) R116279
theorem R438493 : Reach 438493 := rs (se 3 (by rfl) ⟨82217, by rfl⟩) R164435
theorem R439451 : Reach 439451 := rs (se 1 (by rfl) ⟨329588, by rfl⟩) R659177
theorem R276047 : Reach 276047 := rs (se 1 (by rfl) ⟨207035, by rfl⟩) R414071
theorem R80111 : Reach 80111 := rs (se 1 (by rfl) ⟨60083, by rfl⟩) R120167
theorem R178793 : Reach 178793 := rs (se 2 (by rfl) ⟨67047, by rfl⟩) R134095
theorem R11483801 : Reach 11483801 := rs (se 2 (by rfl) ⟨4306425, by rfl⟩) R8612851
theorem R146279 : Reach 146279 := rs (se 1 (by rfl) ⟨109709, by rfl⟩) R219419
theorem R80891 : Reach 80891 := rs (se 1 (by rfl) ⟨60668, by rfl⟩) R121337
theorem R81215 : Reach 81215 := rs (se 1 (by rfl) ⟨60911, by rfl⟩) R121823
theorem R81449 : Reach 81449 := rs (se 2 (by rfl) ⟨30543, by rfl⟩) R61087
theorem R1490987 : Reach 1490987 := rs (se 1 (by rfl) ⟨1118240, by rfl⟩) R2236481
theorem R115519 : Reach 115519 := rs (se 1 (by rfl) ⟨86639, by rfl⟩) R173279
theorem R214111 : Reach 214111 := rs (se 1 (by rfl) ⟨160583, by rfl⟩) R321167
theorem R705671 : Reach 705671 := rs (se 1 (by rfl) ⟨529253, by rfl⟩) R1058507
theorem R51615 : Reach 51615 := rs (se 1 (by rfl) ⟨38711, by rfl⟩) R77423
theorem R51687 : Reach 51687 := rs (se 1 (by rfl) ⟨38765, by rfl⟩) R77531
theorem R51879 : Reach 51879 := rs (se 1 (by rfl) ⟨38909, by rfl⟩) R77819
theorem R51943 : Reach 51943 := rs (se 1 (by rfl) ⟨38957, by rfl⟩) R77915
theorem R51999 : Reach 51999 := rs (se 1 (by rfl) ⟨38999, by rfl⟩) R77999
theorem R117575 : Reach 117575 := rs (se 1 (by rfl) ⟨88181, by rfl⟩) R176363
theorem R52135 : Reach 52135 := rs (se 1 (by rfl) ⟨39101, by rfl⟩) R78203
theorem R52207 : Reach 52207 := rs (se 1 (by rfl) ⟨39155, by rfl⟩) R78311
theorem R52455 : Reach 52455 := rs (se 1 (by rfl) ⟨39341, by rfl⟩) R78683
theorem R183599 : Reach 183599 := rs (se 1 (by rfl) ⟨137699, by rfl⟩) R275399
theorem R183707 : Reach 183707 := rs (se 1 (by rfl) ⟨137780, by rfl⟩) R275561
theorem R52639 : Reach 52639 := rs (se 1 (by rfl) ⟨39479, by rfl⟩) R78959
theorem R52895 : Reach 52895 := rs (se 1 (by rfl) ⟨39671, by rfl⟩) R79343
theorem R1429159 : Reach 1429159 := rs (se 1 (by rfl) ⟨1071869, by rfl⟩) R2143739
theorem R53083 : Reach 53083 := rs (se 1 (by rfl) ⟨39812, by rfl⟩) R79625
theorem R118763 : Reach 118763 := rs (se 1 (by rfl) ⟨89072, by rfl⟩) R178145
theorem R53455 : Reach 53455 := rs (se 1 (by rfl) ⟨40091, by rfl⟩) R80183
theorem R53503 : Reach 53503 := rs (se 1 (by rfl) ⟨40127, by rfl⟩) R80255
theorem R119483 : Reach 119483 := rs (se 1 (by rfl) ⟨89612, by rfl⟩) R179225
theorem R53967 : Reach 53967 := rs (se 1 (by rfl) ⟨40475, by rfl⟩) R80951
theorem R53999 : Reach 53999 := rs (se 1 (by rfl) ⟨40499, by rfl⟩) R80999
theorem R250651 : Reach 250651 := rs (se 1 (by rfl) ⟨187988, by rfl⟩) R375977
theorem R54555 : Reach 54555 := rs (se 1 (by rfl) ⟨40916, by rfl⟩) R81833
theorem R709955 : Reach 709955 := rs (se 1 (by rfl) ⟨532466, by rfl⟩) R1064933
theorem R54811 : Reach 54811 := rs (se 1 (by rfl) ⟨41108, by rfl⟩) R82217
theorem R120527 : Reach 120527 := rs (se 1 (by rfl) ⟨90395, by rfl⟩) R180791
theorem R415529 : Reach 415529 := rs (se 2 (by rfl) ⟨155823, by rfl⟩) R311647
theorem R120935 : Reach 120935 := rs (se 1 (by rfl) ⟨90701, by rfl⟩) R181403
theorem R88303 : Reach 88303 := rs (se 1 (by rfl) ⟨66227, by rfl⟩) R132455
theorem R121225 : Reach 121225 := rs (se 2 (by rfl) ⟨45459, by rfl⟩) R90919
theorem R219791 : Reach 219791 := rs (se 1 (by rfl) ⟨164843, by rfl⟩) R329687
theorem R121769 : Reach 121769 := rs (se 2 (by rfl) ⟨45663, by rfl⟩) R91327
theorem R89255 : Reach 89255 := rs (se 1 (by rfl) ⟨66941, by rfl⟩) R133883
theorem R2677967 : Reach 2677967 := rs (se 1 (by rfl) ⟨2008475, by rfl⟩) R4016951
theorem R187703 : Reach 187703 := rs (se 1 (by rfl) ⟨140777, by rfl⟩) R281555
theorem R122363 : Reach 122363 := rs (se 1 (by rfl) ⟨91772, by rfl⟩) R183545
theorem R90139 : Reach 90139 := rs (se 1 (by rfl) ⟨67604, by rfl⟩) R135209
theorem R57439 : Reach 57439 := rs (se 1 (by rfl) ⟨43079, by rfl⟩) R86159
theorem R123785 : Reach 123785 := rs (se 2 (by rfl) ⟨46419, by rfl⟩) R92839
theorem R91219 : Reach 91219 := rs (se 1 (by rfl) ⟨68414, by rfl⟩) R136829
theorem R58783 : Reach 58783 := rs (se 1 (by rfl) ⟨44087, by rfl⟩) R88175
theorem R2746667 : Reach 2746667 := rs (se 1 (by rfl) ⟨2060000, by rfl⟩) R4120001
theorem R94907 : Reach 94907 := rs (se 1 (by rfl) ⟨71180, by rfl⟩) R142361
theorem R128479 : Reach 128479 := rs (se 1 (by rfl) ⟨96359, by rfl⟩) R192719
theorem R35452673 : Reach 35452673 := rs (se 2 (by rfl) ⟨13294752, by rfl⟩) R26589505
theorem R392201 : Reach 392201 := rs (se 2 (by rfl) ⟨147075, by rfl⟩) R294151
theorem R788413 : Reach 788413 := rs (se 3 (by rfl) ⟨147827, by rfl⟩) R295655
theorem R330155 : Reach 330155 := rs (se 1 (by rfl) ⟨247616, by rfl⟩) R495233
theorem R594067 : Reach 594067 := rs (se 1 (by rfl) ⟨445550, by rfl⟩) R891101
theorem R135391 : Reach 135391 := rs (se 1 (by rfl) ⟨101543, by rfl⟩) R203087
theorem R332075 : Reach 332075 := rs (se 1 (by rfl) ⟨249056, by rfl⟩) R498113
theorem R463295 : Reach 463295 := rs (se 1 (by rfl) ⟨347471, by rfl⟩) R694943
theorem R1905545 : Reach 1905545 := rs (se 2 (by rfl) ⟨714579, by rfl⟩) R1429159
theorem R71015 : Reach 71015 := rs (se 1 (by rfl) ⟨53261, by rfl⟩) R106523
theorem R334201 : Reach 334201 := rs (se 2 (by rfl) ⟨125325, by rfl⟩) R250651
theorem R137609 : Reach 137609 := rs (se 2 (by rfl) ⟨51603, by rfl⟩) R103207
theorem R203755 : Reach 203755 := rs (se 1 (by rfl) ⟨152816, by rfl⟩) R305633
theorem R72895 : Reach 72895 := rs (se 1 (by rfl) ⟨54671, by rfl⟩) R109343
theorem R171305 : Reach 171305 := rs (se 2 (by rfl) ⟨64239, by rfl⟩) R128479
theorem R138935 : Reach 138935 := rs (se 1 (by rfl) ⟨104201, by rfl⟩) R208403
theorem R23635115 : Reach 23635115 := rs (se 1 (by rfl) ⟨17726336, by rfl⟩) R35452673
theorem R993991 : Reach 993991 := rs (se 1 (by rfl) ⟨745493, by rfl⟩) R1490987
theorem R3975965 : Reach 3975965 := rs (se 3 (by rfl) ⟨745493, by rfl⟩) R1490987
theorem R306341 : Reach 306341 := rs (se 4 (by rfl) ⟨28719, by rfl⟩) R57439
theorem R175517 : Reach 175517 := rs (se 3 (by rfl) ⟨32909, by rfl⟩) R65819
theorem R470447 : Reach 470447 := rs (se 1 (by rfl) ⟨352835, by rfl⟩) R705671
theorem R110683 : Reach 110683 := rs (se 1 (by rfl) ⟨83012, by rfl⟩) R166025
theorem R2798063 : Reach 2798063 := rs (se 1 (by rfl) ⟨2098547, by rfl⟩) R4197095
theorem R78377 : Reach 78377 := rs (se 2 (by rfl) ⟨29391, by rfl⟩) R58783
theorem R78383 : Reach 78383 := rs (se 1 (by rfl) ⟨58787, by rfl⟩) R117575
theorem R570023 : Reach 570023 := rs (se 1 (by rfl) ⟨427517, by rfl⟩) R855035
theorem R177119 : Reach 177119 := rs (se 1 (by rfl) ⟨132839, by rfl⟩) R265679
theorem R570577 : Reach 570577 := rs (se 2 (by rfl) ⟨213966, by rfl⟩) R427933
theorem R79175 : Reach 79175 := rs (se 1 (by rfl) ⟨59381, by rfl⟩) R118763
theorem R177767 : Reach 177767 := rs (se 1 (by rfl) ⟨133325, by rfl⟩) R266651
theorem R79655 : Reach 79655 := rs (se 1 (by rfl) ⟨59741, by rfl⟩) R119483
theorem R473303 : Reach 473303 := rs (se 1 (by rfl) ⟨354977, by rfl⟩) R709955
theorem R80351 : Reach 80351 := rs (se 1 (by rfl) ⟨60263, by rfl⟩) R120527
theorem R277019 : Reach 277019 := rs (se 1 (by rfl) ⟨207764, by rfl⟩) R415529
theorem R80623 : Reach 80623 := rs (se 1 (by rfl) ⟨60467, by rfl⟩) R120935
theorem R703667 : Reach 703667 := rs (se 1 (by rfl) ⟨527750, by rfl⟩) R1055501
theorem R81179 : Reach 81179 := rs (se 1 (by rfl) ⟨60884, by rfl⟩) R121769
theorem R1785311 : Reach 1785311 := rs (se 1 (by rfl) ⟨1338983, by rfl⟩) R2677967
theorem R671273 : Reach 671273 := rs (se 2 (by rfl) ⟨251727, by rfl⟩) R503455
theorem R81575 : Reach 81575 := rs (se 1 (by rfl) ⟨61181, by rfl⟩) R122363
theorem R311465 : Reach 311465 := rs (se 2 (by rfl) ⟨116799, by rfl⟩) R233599
theorem R245935 : Reach 245935 := rs (se 1 (by rfl) ⟨184451, by rfl⟩) R368903
theorem R82523 : Reach 82523 := rs (se 1 (by rfl) ⟨61892, by rfl⟩) R123785
theorem R7324445 : Reach 7324445 := rs (se 3 (by rfl) ⟨1373333, by rfl⟩) R2746667
theorem R443369 : Reach 443369 := rs (se 2 (by rfl) ⟨166263, by rfl⟩) R332527
theorem R116639 : Reach 116639 := rs (se 1 (by rfl) ⟨87479, by rfl⟩) R174959
theorem R116819 : Reach 116819 := rs (se 1 (by rfl) ⟨87614, by rfl⟩) R175229
theorem R51291 : Reach 51291 := rs (se 1 (by rfl) ⟨38468, by rfl⟩) R76937
theorem R51679 : Reach 51679 := rs (se 1 (by rfl) ⟨38759, by rfl⟩) R77519
theorem R117737 : Reach 117737 := rs (se 2 (by rfl) ⟨44151, by rfl⟩) R88303
theorem R184031 : Reach 184031 := rs (se 1 (by rfl) ⟨138023, by rfl⟩) R276047
theorem R53407 : Reach 53407 := rs (se 1 (by rfl) ⟨40055, by rfl⟩) R80111
theorem R119195 : Reach 119195 := rs (se 1 (by rfl) ⟨89396, by rfl⟩) R178793
theorem R7655867 : Reach 7655867 := rs (se 1 (by rfl) ⟨5741900, by rfl⟩) R11483801
theorem R53927 : Reach 53927 := rs (se 1 (by rfl) ⟨40445, by rfl⟩) R80891
theorem R447241 : Reach 447241 := rs (se 2 (by rfl) ⟨167715, by rfl⟩) R335431
theorem R54143 : Reach 54143 := rs (se 1 (by rfl) ⟨40607, by rfl⟩) R81215
theorem R54299 : Reach 54299 := rs (se 1 (by rfl) ⟨40724, by rfl⟩) R81449
theorem R120185 : Reach 120185 := rs (se 2 (by rfl) ⟨45069, by rfl⟩) R90139
theorem R154025 : Reach 154025 := rs (se 2 (by rfl) ⟨57759, by rfl⟩) R115519
theorem R121625 : Reach 121625 := rs (se 2 (by rfl) ⟨45609, by rfl⟩) R91219
theorem R285481 : Reach 285481 := rs (se 2 (by rfl) ⟨107055, by rfl⟩) R214111
theorem R253085 : Reach 253085 := rs (se 3 (by rfl) ⟨47453, by rfl⟩) R94907
theorem R89275 : Reach 89275 := rs (se 1 (by rfl) ⟨66956, by rfl⟩) R133913
theorem R89599 : Reach 89599 := rs (se 1 (by rfl) ⟨67199, by rfl⟩) R134399
theorem R122399 : Reach 122399 := rs (se 1 (by rfl) ⟨91799, by rfl⟩) R183599
theorem R122471 : Reach 122471 := rs (se 1 (by rfl) ⟨91853, by rfl⟩) R183707
theorem R90335 : Reach 90335 := rs (se 1 (by rfl) ⟨67751, by rfl⟩) R135503
theorem R156143 : Reach 156143 := rs (se 1 (by rfl) ⟨117107, by rfl⟩) R234215
theorem R91975 : Reach 91975 := rs (se 1 (by rfl) ⟨68981, by rfl⟩) R137963
theorem R59503 : Reach 59503 := rs (se 1 (by rfl) ⟨44627, by rfl⟩) R89255
theorem R125135 : Reach 125135 := rs (se 1 (by rfl) ⟨93851, by rfl⟩) R187703
theorem R584657 : Reach 584657 := rs (se 2 (by rfl) ⟨219246, by rfl⟩) R438493
theorem R290461 : Reach 290461 := rs (se 3 (by rfl) ⟨54461, by rfl⟩) R108923
theorem R356071 : Reach 356071 := rs (se 1 (by rfl) ⟨267053, by rfl⟩) R534107
theorem R716789 : Reach 716789 := rs (se 5 (by rfl) ⟨33599, by rfl⟩) R67199
theorem R586109 : Reach 586109 := rs (se 3 (by rfl) ⟨109895, by rfl⟩) R219791
theorem R161633 : Reach 161633 := rs (se 2 (by rfl) ⟨60612, by rfl⟩) R121225
theorem R292967 : Reach 292967 := rs (se 1 (by rfl) ⟨219725, by rfl⟩) R439451
theorem R97519 : Reach 97519 := rs (se 1 (by rfl) ⟨73139, by rfl⟩) R146279
theorem R261467 : Reach 261467 := rs (se 1 (by rfl) ⟨196100, by rfl⟩) R392201
theorem R4882963 : Reach 4882963 := rs (se 1 (by rfl) ⟨3662222, by rfl⟩) R7324445
theorem R295579 : Reach 295579 := rs (se 1 (by rfl) ⟨221684, by rfl⟩) R443369
theorem R1311653 : Reach 1311653 := rs (se 4 (by rfl) ⟨122967, by rfl⟩) R245935
theorem R1051217 : Reach 1051217 := rs (se 2 (by rfl) ⟨394206, by rfl⟩) R788413
theorem R102683 : Reach 102683 := rs (se 1 (by rfl) ⟨77012, by rfl⟩) R154025
theorem R431021 : Reach 431021 := rs (se 3 (by rfl) ⟨80816, by rfl⟩) R161633
theorem R792089 : Reach 792089 := rs (se 2 (by rfl) ⟨297033, by rfl⟩) R594067
theorem R104095 : Reach 104095 := rs (se 1 (by rfl) ⟨78071, by rfl⟩) R156143
theorem R596321 : Reach 596321 := rs (se 2 (by rfl) ⟨223620, by rfl⟩) R447241
theorem R760769 : Reach 760769 := rs (se 2 (by rfl) ⟨285288, by rfl⟩) R570577
theorem R204227 : Reach 204227 := rs (se 1 (by rfl) ⟨153170, by rfl⟩) R306341
theorem R107497 : Reach 107497 := rs (se 2 (by rfl) ⟨40311, by rfl⟩) R80623
theorem R271673 : Reach 271673 := rs (se 2 (by rfl) ⟨101877, by rfl⟩) R203755
theorem R469111 : Reach 469111 := rs (se 1 (by rfl) ⟨351833, by rfl⟩) R703667
theorem R174311 : Reach 174311 := rs (se 1 (by rfl) ⟨130733, by rfl⟩) R261467
theorem R1190207 : Reach 1190207 := rs (se 1 (by rfl) ⟨892655, by rfl⟩) R1785311
theorem R1911437 : Reach 1911437 := rs (se 3 (by rfl) ⟨358394, by rfl⟩) R716789
theorem R207643 : Reach 207643 := rs (se 1 (by rfl) ⟨155732, by rfl⟩) R311465
theorem R77759 : Reach 77759 := rs (se 1 (by rfl) ⟨58319, by rfl⟩) R116639
theorem R77879 : Reach 77879 := rs (se 1 (by rfl) ⟨58409, by rfl⟩) R116819
theorem R78491 : Reach 78491 := rs (se 1 (by rfl) ⟨58868, by rfl⟩) R117737
theorem R79337 : Reach 79337 := rs (se 2 (by rfl) ⟨29751, by rfl⟩) R59503
theorem R79463 : Reach 79463 := rs (se 1 (by rfl) ⟨59597, by rfl⟩) R119195
theorem R308863 : Reach 308863 := rs (se 1 (by rfl) ⟨231647, by rfl⟩) R463295
theorem R80123 : Reach 80123 := rs (se 1 (by rfl) ⟨60092, by rfl⟩) R120185
theorem R1325321 : Reach 1325321 := rs (se 2 (by rfl) ⟨496995, by rfl⟩) R993991
theorem R81083 : Reach 81083 := rs (se 1 (by rfl) ⟨60812, by rfl⟩) R121625
theorem R114203 : Reach 114203 := rs (se 1 (by rfl) ⟨85652, by rfl⟩) R171305
theorem R474761 : Reach 474761 := rs (se 2 (by rfl) ⟨178035, by rfl⟩) R356071
theorem R81599 : Reach 81599 := rs (se 1 (by rfl) ⟨61199, by rfl⟩) R122399
theorem R81647 : Reach 81647 := rs (se 1 (by rfl) ⟨61235, by rfl⟩) R122471
theorem R147577 : Reach 147577 := rs (se 2 (by rfl) ⟨55341, by rfl⟩) R110683
theorem R180521 : Reach 180521 := rs (se 2 (by rfl) ⟨67695, by rfl⟩) R135391
theorem R1262141 : Reach 1262141 := rs (se 3 (by rfl) ⟨236651, by rfl⟩) R473303
theorem R83423 : Reach 83423 := rs (se 1 (by rfl) ⟨62567, by rfl⟩) R125135
theorem R117011 : Reach 117011 := rs (se 1 (by rfl) ⟨87758, by rfl⟩) R175517
theorem R313631 : Reach 313631 := rs (se 1 (by rfl) ⟨235223, by rfl⟩) R470447
theorem R52251 : Reach 52251 := rs (se 1 (by rfl) ⟨39188, by rfl⟩) R78377
theorem R52255 : Reach 52255 := rs (se 1 (by rfl) ⟨39191, by rfl⟩) R78383
theorem R674893 : Reach 674893 := rs (se 3 (by rfl) ⟨126542, by rfl⟩) R253085
theorem R380015 : Reach 380015 := rs (se 1 (by rfl) ⟨285011, by rfl⟩) R570023
theorem R445601 : Reach 445601 := rs (se 2 (by rfl) ⟨167100, by rfl⟩) R334201
theorem R118079 : Reach 118079 := rs (se 1 (by rfl) ⟨88559, by rfl⟩) R177119
theorem R52783 : Reach 52783 := rs (se 1 (by rfl) ⟨39587, by rfl⟩) R79175
theorem R380641 : Reach 380641 := rs (se 2 (by rfl) ⟨142740, by rfl⟩) R285481
theorem R118511 : Reach 118511 := rs (se 1 (by rfl) ⟨88883, by rfl⟩) R177767
theorem R53103 : Reach 53103 := rs (se 1 (by rfl) ⟨39827, by rfl⟩) R79655
theorem R119033 : Reach 119033 := rs (se 2 (by rfl) ⟨44637, by rfl⟩) R89275
theorem R53567 : Reach 53567 := rs (se 1 (by rfl) ⟨40175, by rfl⟩) R80351
theorem R184679 : Reach 184679 := rs (se 1 (by rfl) ⟨138509, by rfl⟩) R277019
theorem R119465 : Reach 119465 := rs (se 2 (by rfl) ⟨44799, by rfl⟩) R89599
theorem R54119 : Reach 54119 := rs (se 1 (by rfl) ⟨40589, by rfl⟩) R81179
theorem R447515 : Reach 447515 := rs (se 1 (by rfl) ⟨335636, by rfl⟩) R671273
theorem R54383 : Reach 54383 := rs (se 1 (by rfl) ⟨40787, by rfl⟩) R81575
theorem R55015 : Reach 55015 := rs (se 1 (by rfl) ⟨41261, by rfl⟩) R82523
theorem R220103 : Reach 220103 := rs (se 1 (by rfl) ⟨165077, by rfl⟩) R330155
theorem R122633 : Reach 122633 := rs (se 2 (by rfl) ⟨45987, by rfl⟩) R91975
theorem R122687 : Reach 122687 := rs (se 1 (by rfl) ⟨92015, by rfl⟩) R184031
theorem R221383 : Reach 221383 := rs (se 1 (by rfl) ⟨166037, by rfl⟩) R332075
theorem R5103911 : Reach 5103911 := rs (se 1 (by rfl) ⟨3827933, by rfl⟩) R7655867
theorem R1270363 : Reach 1270363 := rs (se 1 (by rfl) ⟨952772, by rfl⟩) R1905545
theorem R189373 : Reach 189373 := rs (se 3 (by rfl) ⟨35507, by rfl⟩) R71015
theorem R91739 : Reach 91739 := rs (se 1 (by rfl) ⟨68804, by rfl⟩) R137609
theorem R387281 : Reach 387281 := rs (se 2 (by rfl) ⟨145230, by rfl⟩) R290461
theorem R92623 : Reach 92623 := rs (se 1 (by rfl) ⟨69467, by rfl⟩) R138935
theorem R60223 : Reach 60223 := rs (se 1 (by rfl) ⟨45167, by rfl⟩) R90335
theorem R15756743 : Reach 15756743 := rs (se 1 (by rfl) ⟨11817557, by rfl⟩) R23635115
theorem R2650643 : Reach 2650643 := rs (se 1 (by rfl) ⟨1987982, by rfl⟩) R3975965
theorem R389771 : Reach 389771 := rs (se 1 (by rfl) ⟨292328, by rfl⟩) R584657
theorem R390739 : Reach 390739 := rs (se 1 (by rfl) ⟨293054, by rfl⟩) R586109
theorem R1865375 : Reach 1865375 := rs (se 1 (by rfl) ⟨1399031, by rfl⟩) R2798063
theorem R195311 : Reach 195311 := rs (se 1 (by rfl) ⟨146483, by rfl⟩) R292967
theorem R97193 : Reach 97193 := rs (se 2 (by rfl) ⟨36447, by rfl⟩) R72895
theorem R130025 : Reach 130025 := rs (se 2 (by rfl) ⟨48759, by rfl⟩) R97519
theorem R196769 : Reach 196769 := rs (se 2 (by rfl) ⟨73788, by rfl⟩) R147577
theorem R295177 : Reach 295177 := rs (se 2 (by rfl) ⟨110691, by rfl⟩) R221383
theorem R297067 : Reach 297067 := rs (se 1 (by rfl) ⟨222800, by rfl⟩) R445601
theorem R625481 : Reach 625481 := rs (se 2 (by rfl) ⟨234555, by rfl⟩) R469111
theorem R68455 : Reach 68455 := rs (se 1 (by rfl) ⟨51341, by rfl⟩) R102683
theorem R298343 : Reach 298343 := rs (se 1 (by rfl) ⟨223757, by rfl⟩) R447515
theorem R1576421 : Reach 1576421 := rs (se 4 (by rfl) ⟨147789, by rfl⟩) R295579
theorem R528059 : Reach 528059 := rs (se 1 (by rfl) ⟨396044, by rfl⟩) R792089
theorem R397547 : Reach 397547 := rs (se 1 (by rfl) ⟨298160, by rfl⟩) R596321
theorem R136151 : Reach 136151 := rs (se 1 (by rfl) ⟨102113, by rfl⟩) R204227
theorem R793471 : Reach 793471 := rs (se 1 (by rfl) ⟨595103, by rfl⟩) R1190207
theorem R138793 : Reach 138793 := rs (se 2 (by rfl) ⟨52047, by rfl⟩) R104095
theorem R76135 : Reach 76135 := rs (se 1 (by rfl) ⟨57101, by rfl⟩) R114203
theorem R143329 : Reach 143329 := rs (se 2 (by rfl) ⟨53748, by rfl⟩) R107497
theorem R78007 : Reach 78007 := rs (se 1 (by rfl) ⟨58505, by rfl⟩) R117011
theorem R209087 : Reach 209087 := rs (se 1 (by rfl) ⟨156815, by rfl⟩) R313631
theorem R700811 : Reach 700811 := rs (se 1 (by rfl) ⟨525608, by rfl⟩) R1051217
theorem R78719 : Reach 78719 := rs (se 1 (by rfl) ⟨59039, by rfl⟩) R118079
theorem R79007 : Reach 79007 := rs (se 1 (by rfl) ⟨59255, by rfl⟩) R118511
theorem R79355 : Reach 79355 := rs (se 1 (by rfl) ⟨59516, by rfl⟩) R119033
theorem R79643 : Reach 79643 := rs (se 1 (by rfl) ⟨59732, by rfl⟩) R119465
theorem R276857 : Reach 276857 := rs (se 2 (by rfl) ⟨103821, by rfl⟩) R207643
theorem R80297 : Reach 80297 := rs (se 2 (by rfl) ⟨30111, by rfl⟩) R60223
theorem R899857 : Reach 899857 := rs (se 2 (by rfl) ⟨337446, by rfl⟩) R674893
theorem R507179 : Reach 507179 := rs (se 1 (by rfl) ⟨380384, by rfl⟩) R760769
theorem R146735 : Reach 146735 := rs (se 1 (by rfl) ⟨110051, by rfl⟩) R220103
theorem R507521 : Reach 507521 := rs (se 2 (by rfl) ⟨190320, by rfl⟩) R380641
theorem R81755 : Reach 81755 := rs (se 1 (by rfl) ⟨61316, by rfl⟩) R122633
theorem R81791 : Reach 81791 := rs (se 1 (by rfl) ⟨61343, by rfl⟩) R122687
theorem R181115 : Reach 181115 := rs (se 1 (by rfl) ⟨135836, by rfl⟩) R271673
theorem R116207 : Reach 116207 := rs (se 1 (by rfl) ⟨87155, by rfl⟩) R174311
theorem R870389 : Reach 870389 := rs (se 5 (by rfl) ⟨40799, by rfl⟩) R81599
theorem R411817 : Reach 411817 := rs (se 2 (by rfl) ⟨154431, by rfl⟩) R308863
theorem R10504495 : Reach 10504495 := rs (se 1 (by rfl) ⟨7878371, by rfl⟩) R15756743
theorem R51839 : Reach 51839 := rs (se 1 (by rfl) ⟨38879, by rfl⟩) R77759
theorem R51919 : Reach 51919 := rs (se 1 (by rfl) ⟨38939, by rfl⟩) R77879
theorem R52327 : Reach 52327 := rs (se 1 (by rfl) ⟨39245, by rfl⟩) R78491
theorem R52891 : Reach 52891 := rs (se 1 (by rfl) ⟨39668, by rfl⟩) R79337
theorem R52975 : Reach 52975 := rs (se 1 (by rfl) ⟨39731, by rfl⟩) R79463
theorem R53415 : Reach 53415 := rs (se 1 (by rfl) ⟨40061, by rfl⟩) R80123
theorem R86683 : Reach 86683 := rs (se 1 (by rfl) ⟨65012, by rfl⟩) R130025
theorem R54055 : Reach 54055 := rs (se 1 (by rfl) ⟨40541, by rfl⟩) R81083
theorem R316507 : Reach 316507 := rs (se 1 (by rfl) ⟨237380, by rfl⟩) R474761
theorem R54399 : Reach 54399 := rs (se 1 (by rfl) ⟨40799, by rfl⟩) R81599
theorem R54431 : Reach 54431 := rs (se 1 (by rfl) ⟨40823, by rfl⟩) R81647
theorem R120347 : Reach 120347 := rs (se 1 (by rfl) ⟨90260, by rfl⟩) R180521
theorem R841427 : Reach 841427 := rs (se 1 (by rfl) ⟨631070, by rfl⟩) R1262141
theorem R874435 : Reach 874435 := rs (se 1 (by rfl) ⟨655826, by rfl⟩) R1311653
theorem R6510617 : Reach 6510617 := rs (se 2 (by rfl) ⟨2441481, by rfl⟩) R4882963
theorem R1693817 : Reach 1693817 := rs (se 2 (by rfl) ⟨635181, by rfl⟩) R1270363
theorem R55615 : Reach 55615 := rs (se 1 (by rfl) ⟨41711, by rfl⟩) R83423
theorem R252497 : Reach 252497 := rs (se 2 (by rfl) ⟨94686, by rfl⟩) R189373
theorem R253343 : Reach 253343 := rs (se 1 (by rfl) ⟨190007, by rfl⟩) R380015
theorem R123119 : Reach 123119 := rs (se 1 (by rfl) ⟨92339, by rfl⟩) R184679
theorem R123497 : Reach 123497 := rs (se 2 (by rfl) ⟨46311, by rfl⟩) R92623
theorem R287347 : Reach 287347 := rs (se 1 (by rfl) ⟨215510, by rfl⟩) R431021
theorem R3402607 : Reach 3402607 := rs (se 1 (by rfl) ⟨2551955, by rfl⟩) R5103911
theorem R61159 : Reach 61159 := rs (se 1 (by rfl) ⟨45869, by rfl⟩) R91739
theorem R258187 : Reach 258187 := rs (se 1 (by rfl) ⟨193640, by rfl⟩) R387281
theorem R1274291 : Reach 1274291 := rs (se 1 (by rfl) ⟨955718, by rfl⟩) R1911437
theorem R520985 : Reach 520985 := rs (se 2 (by rfl) ⟨195369, by rfl⟩) R390739
theorem R1767095 : Reach 1767095 := rs (se 1 (by rfl) ⟨1325321, by rfl⟩) R2650643
theorem R259847 : Reach 259847 := rs (se 1 (by rfl) ⟨194885, by rfl⟩) R389771
theorem R1243583 : Reach 1243583 := rs (se 1 (by rfl) ⟨932687, by rfl⟩) R1865375
theorem R883547 : Reach 883547 := rs (se 1 (by rfl) ⟨662660, by rfl⟩) R1325321
theorem R130207 : Reach 130207 := rs (se 1 (by rfl) ⟨97655, by rfl⟩) R195311
theorem R64795 : Reach 64795 := rs (se 1 (by rfl) ⟨48596, by rfl⟩) R97193
theorem R131179 : Reach 131179 := rs (se 1 (by rfl) ⟨98384, by rfl⟩) R196769
theorem R393569 : Reach 393569 := rs (se 2 (by rfl) ⟨147588, by rfl⟩) R295177
theorem R198895 : Reach 198895 := rs (se 1 (by rfl) ⟨149171, by rfl⟩) R298343
theorem R1050947 : Reach 1050947 := rs (se 1 (by rfl) ⟨788210, by rfl⟩) R1576421
theorem R396089 : Reach 396089 := rs (se 2 (by rfl) ⟨148533, by rfl⟩) R297067
theorem R265031 : Reach 265031 := rs (se 1 (by rfl) ⟨198773, by rfl⟩) R397547
theorem R101513 : Reach 101513 := rs (se 2 (by rfl) ⟨38067, by rfl⟩) R76135
theorem R560951 : Reach 560951 := rs (se 1 (by rfl) ⟨420713, by rfl⟩) R841427
theorem R168331 : Reach 168331 := rs (se 1 (by rfl) ⟨126248, by rfl⟩) R252497
theorem R168895 : Reach 168895 := rs (se 1 (by rfl) ⟨126671, by rfl⟩) R253343
theorem R104009 : Reach 104009 := rs (se 2 (by rfl) ⟨39003, by rfl⟩) R78007
theorem R139391 : Reach 139391 := rs (se 1 (by rfl) ⟨104543, by rfl⟩) R209087
theorem R467207 : Reach 467207 := rs (se 1 (by rfl) ⟨350405, by rfl⟩) R700811
theorem R74153 : Reach 74153 := rs (se 2 (by rfl) ⟨27807, by rfl⟩) R55615
theorem R1352477 : Reach 1352477 := rs (se 3 (by rfl) ⟨253589, by rfl⟩) R507179
theorem R1057961 : Reach 1057961 := rs (se 2 (by rfl) ⟨396735, by rfl⟩) R793471
theorem R173231 : Reach 173231 := rs (se 1 (by rfl) ⟨129923, by rfl⟩) R259847
theorem R173609 : Reach 173609 := rs (se 2 (by rfl) ⟨65103, by rfl⟩) R130207
theorem R829055 : Reach 829055 := rs (se 1 (by rfl) ⟨621791, by rfl⟩) R1243583
theorem R338347 : Reach 338347 := rs (se 1 (by rfl) ⟨253760, by rfl⟩) R507521
theorem R77471 : Reach 77471 := rs (se 1 (by rfl) ⟨58103, by rfl⟩) R116207
theorem R14005993 : Reach 14005993 := rs (se 2 (by rfl) ⟨5252247, by rfl⟩) R10504495
theorem R80231 : Reach 80231 := rs (se 1 (by rfl) ⟨60173, by rfl⟩) R120347
theorem R4536809 : Reach 4536809 := rs (se 2 (by rfl) ⟨1701303, by rfl⟩) R3402607
theorem R4340411 : Reach 4340411 := rs (se 1 (by rfl) ⟨3255308, by rfl⟩) R6510617
theorem R1129211 : Reach 1129211 := rs (se 1 (by rfl) ⟨846908, by rfl⟩) R1693817
theorem R81545 : Reach 81545 := rs (se 2 (by rfl) ⟨30579, by rfl⟩) R61159
theorem R82079 : Reach 82079 := rs (se 1 (by rfl) ⟨61559, by rfl⟩) R123119
theorem R344249 : Reach 344249 := rs (se 2 (by rfl) ⟨129093, by rfl⟩) R258187
theorem R82331 : Reach 82331 := rs (se 1 (by rfl) ⟨61748, by rfl⟩) R123497
theorem R115577 : Reach 115577 := rs (se 2 (by rfl) ⟨43341, by rfl⟩) R86683
theorem R1165913 : Reach 1165913 := rs (se 2 (by rfl) ⟨437217, by rfl⟩) R874435
theorem R347323 : Reach 347323 := rs (se 1 (by rfl) ⟨260492, by rfl⟩) R520985
theorem R52479 : Reach 52479 := rs (se 1 (by rfl) ⟨39359, by rfl⟩) R78719
theorem R52671 : Reach 52671 := rs (se 1 (by rfl) ⟨39503, by rfl⟩) R79007
theorem R52903 : Reach 52903 := rs (se 1 (by rfl) ⟨39677, by rfl⟩) R79355
theorem R1199809 : Reach 1199809 := rs (se 2 (by rfl) ⟨449928, by rfl⟩) R899857
theorem R53095 : Reach 53095 := rs (se 1 (by rfl) ⟨39821, by rfl⟩) R79643
theorem R184571 : Reach 184571 := rs (se 1 (by rfl) ⟨138428, by rfl⟩) R276857
theorem R53531 : Reach 53531 := rs (se 1 (by rfl) ⟨40148, by rfl⟩) R80297
theorem R86393 : Reach 86393 := rs (se 2 (by rfl) ⟨32397, by rfl⟩) R64795
theorem R185057 : Reach 185057 := rs (se 2 (by rfl) ⟨69396, by rfl⟩) R138793
theorem R54503 : Reach 54503 := rs (se 1 (by rfl) ⟨40877, by rfl⟩) R81755
theorem R54527 : Reach 54527 := rs (se 1 (by rfl) ⟨40895, by rfl⟩) R81791
theorem R120743 : Reach 120743 := rs (se 1 (by rfl) ⟨90557, by rfl⟩) R181115
theorem R383129 : Reach 383129 := rs (se 2 (by rfl) ⟨143673, by rfl⟩) R287347
theorem R580259 : Reach 580259 := rs (se 1 (by rfl) ⟨435194, by rfl⟩) R870389
theorem R416987 : Reach 416987 := rs (se 1 (by rfl) ⟨312740, by rfl⟩) R625481
theorem R352039 : Reach 352039 := rs (se 1 (by rfl) ⟨264029, by rfl⟩) R528059
theorem R549089 : Reach 549089 := rs (se 2 (by rfl) ⟨205908, by rfl⟩) R411817
theorem R90767 : Reach 90767 := rs (se 1 (by rfl) ⟨68075, by rfl⟩) R136151
theorem R91273 : Reach 91273 := rs (se 2 (by rfl) ⟨34227, by rfl⟩) R68455
theorem R191105 : Reach 191105 := rs (se 2 (by rfl) ⟨71664, by rfl⟩) R143329
theorem R422009 : Reach 422009 := rs (se 2 (by rfl) ⟨158253, by rfl⟩) R316507
theorem R849527 : Reach 849527 := rs (se 1 (by rfl) ⟨637145, by rfl⟩) R1274291
theorem R1178063 : Reach 1178063 := rs (se 1 (by rfl) ⟨883547, by rfl⟩) R1767095
theorem R589031 : Reach 589031 := rs (se 1 (by rfl) ⟨441773, by rfl⟩) R883547
theorem R97823 : Reach 97823 := rs (se 1 (by rfl) ⟨73367, by rfl⟩) R146735
theorem R229499 : Reach 229499 := rs (se 1 (by rfl) ⟨172124, by rfl⟩) R344249
theorem R262379 : Reach 262379 := rs (se 1 (by rfl) ⟨196784, by rfl⟩) R393569
theorem R197741 : Reach 197741 := rs (se 3 (by rfl) ⟨37076, by rfl⟩) R74153
theorem R264059 : Reach 264059 := rs (se 1 (by rfl) ⟨198044, by rfl⟩) R396089
theorem R3606605 : Reach 3606605 := rs (se 3 (by rfl) ⟨676238, by rfl⟩) R1352477
theorem R1804517 : Reach 1804517 := rs (se 4 (by rfl) ⟨169173, by rfl⟩) R338347
theorem R265193 : Reach 265193 := rs (se 2 (by rfl) ⟨99447, by rfl⟩) R198895
theorem R463097 : Reach 463097 := rs (se 2 (by rfl) ⟨173661, by rfl⟩) R347323
theorem R366059 : Reach 366059 := rs (se 1 (by rfl) ⟨274544, by rfl⟩) R549089
theorem R270701 : Reach 270701 := rs (se 3 (by rfl) ⟨50756, by rfl⟩) R101513
theorem R566351 : Reach 566351 := rs (se 1 (by rfl) ⟨424763, by rfl⟩) R849527
theorem R3024539 : Reach 3024539 := rs (se 1 (by rfl) ⟨2268404, by rfl⟩) R4536809
theorem R2893607 : Reach 2893607 := rs (se 1 (by rfl) ⟨2170205, by rfl⟩) R4340411
theorem R469385 : Reach 469385 := rs (se 2 (by rfl) ⟨176019, by rfl⟩) R352039
theorem R174905 : Reach 174905 := rs (se 2 (by rfl) ⟨65589, by rfl⟩) R131179
theorem R77051 : Reach 77051 := rs (se 1 (by rfl) ⟨57788, by rfl⟩) R115577
theorem R700631 : Reach 700631 := rs (se 1 (by rfl) ⟨525473, by rfl⟩) R1050947
theorem R176687 : Reach 176687 := rs (se 1 (by rfl) ⟨132515, by rfl⟩) R265031
theorem R373967 : Reach 373967 := rs (se 1 (by rfl) ⟨280475, by rfl⟩) R560951
theorem R80495 : Reach 80495 := rs (se 1 (by rfl) ⟨60371, by rfl⟩) R120743
theorem R277357 : Reach 277357 := rs (se 3 (by rfl) ⟨52004, by rfl⟩) R104009
theorem R277991 : Reach 277991 := rs (se 1 (by rfl) ⟨208493, by rfl⟩) R416987
theorem R311471 : Reach 311471 := rs (se 1 (by rfl) ⟨233603, by rfl⟩) R467207
theorem R705307 : Reach 705307 := rs (se 1 (by rfl) ⟨528980, by rfl⟩) R1057961
theorem R115487 : Reach 115487 := rs (se 1 (by rfl) ⟨86615, by rfl⟩) R173231
theorem R115739 : Reach 115739 := rs (se 1 (by rfl) ⟨86804, by rfl⟩) R173609
theorem R51647 : Reach 51647 := rs (se 1 (by rfl) ⟨38735, by rfl⟩) R77471
theorem R281339 : Reach 281339 := rs (se 1 (by rfl) ⟨211004, by rfl⟩) R422009
theorem R53487 : Reach 53487 := rs (se 1 (by rfl) ⟨40115, by rfl⟩) R80231
theorem R54363 : Reach 54363 := rs (se 1 (by rfl) ⟨40772, by rfl⟩) R81545
theorem R54719 : Reach 54719 := rs (se 1 (by rfl) ⟨41039, by rfl⟩) R82079
theorem R54887 : Reach 54887 := rs (se 1 (by rfl) ⟨41165, by rfl⟩) R82331
theorem R121697 : Reach 121697 := rs (se 2 (by rfl) ⟨45636, by rfl⟩) R91273
theorem R777275 : Reach 777275 := rs (se 1 (by rfl) ⟨582956, by rfl⟩) R1165913
theorem R123047 : Reach 123047 := rs (se 1 (by rfl) ⟨92285, by rfl⟩) R184571
theorem R57595 : Reach 57595 := rs (se 1 (by rfl) ⟨43196, by rfl⟩) R86393
theorem R123371 : Reach 123371 := rs (se 1 (by rfl) ⟨92528, by rfl⟩) R185057
theorem R255419 : Reach 255419 := rs (se 1 (by rfl) ⟨191564, by rfl⟩) R383129
theorem R386839 : Reach 386839 := rs (se 1 (by rfl) ⟨290129, by rfl⟩) R580259
theorem R1599745 : Reach 1599745 := rs (se 2 (by rfl) ⟨599904, by rfl⟩) R1199809
theorem R92927 : Reach 92927 := rs (se 1 (by rfl) ⟨69695, by rfl⟩) R139391
theorem R60511 : Reach 60511 := rs (se 1 (by rfl) ⟨45383, by rfl⟩) R90767
theorem R224441 : Reach 224441 := rs (se 2 (by rfl) ⟨84165, by rfl⟩) R168331
theorem R552703 : Reach 552703 := rs (se 1 (by rfl) ⟨414527, by rfl⟩) R829055
theorem R225193 : Reach 225193 := rs (se 2 (by rfl) ⟨84447, by rfl⟩) R168895
theorem R127403 : Reach 127403 := rs (se 1 (by rfl) ⟨95552, by rfl⟩) R191105
theorem R18674657 : Reach 18674657 := rs (se 2 (by rfl) ⟨7002996, by rfl⟩) R14005993
theorem R785375 : Reach 785375 := rs (se 1 (by rfl) ⟨589031, by rfl⟩) R1178063
theorem R752807 : Reach 752807 := rs (se 1 (by rfl) ⟨564605, by rfl⟩) R1129211
theorem R392687 : Reach 392687 := rs (se 1 (by rfl) ⟨294515, by rfl⟩) R589031
theorem R65215 : Reach 65215 := rs (se 1 (by rfl) ⟨48911, by rfl⟩) R97823
theorem R131827 : Reach 131827 := rs (se 1 (by rfl) ⟨98870, by rfl⟩) R197741
theorem R2132993 : Reach 2132993 := rs (se 2 (by rfl) ⟨799872, by rfl⟩) R1599745
theorem R300257 : Reach 300257 := rs (se 2 (by rfl) ⟨112596, by rfl⟩) R225193
theorem R170279 : Reach 170279 := rs (se 1 (by rfl) ⟨127709, by rfl⟩) R255419
theorem R467087 : Reach 467087 := rs (se 1 (by rfl) ⟨350315, by rfl⟩) R700631
theorem R369809 : Reach 369809 := rs (se 2 (by rfl) ⟨138678, by rfl⟩) R277357
theorem R501871 : Reach 501871 := rs (se 1 (by rfl) ⟨376403, by rfl⟩) R752807
theorem R207647 : Reach 207647 := rs (se 1 (by rfl) ⟨155735, by rfl⟩) R311471
theorem R174919 : Reach 174919 := rs (se 1 (by rfl) ⟨131189, by rfl⟩) R262379
theorem R76793 : Reach 76793 := rs (se 2 (by rfl) ⟨28797, by rfl⟩) R57595
theorem R76991 : Reach 76991 := rs (se 1 (by rfl) ⟨57743, by rfl⟩) R115487
theorem R77159 : Reach 77159 := rs (se 1 (by rfl) ⟨57869, by rfl⟩) R115739
theorem R176039 : Reach 176039 := rs (se 1 (by rfl) ⟨132029, by rfl⟩) R264059
theorem R2404403 : Reach 2404403 := rs (se 1 (by rfl) ⟨1803302, by rfl⟩) R3606605
theorem R176795 : Reach 176795 := rs (se 1 (by rfl) ⟨132596, by rfl⟩) R265193
theorem R308731 : Reach 308731 := rs (se 1 (by rfl) ⟨231548, by rfl⟩) R463097
theorem R244039 : Reach 244039 := rs (se 1 (by rfl) ⟨183029, by rfl⟩) R366059
theorem R80681 : Reach 80681 := rs (se 2 (by rfl) ⟨30255, by rfl⟩) R60511
theorem R81131 : Reach 81131 := rs (se 1 (by rfl) ⟨60848, by rfl⟩) R121697
theorem R736937 : Reach 736937 := rs (se 2 (by rfl) ⟨276351, by rfl⟩) R552703
theorem R82031 : Reach 82031 := rs (se 1 (by rfl) ⟨61523, by rfl⟩) R123047
theorem R180467 : Reach 180467 := rs (se 1 (by rfl) ⟨135350, by rfl⟩) R270701
theorem R82247 : Reach 82247 := rs (se 1 (by rfl) ⟨61685, by rfl⟩) R123371
theorem R377567 : Reach 377567 := rs (se 1 (by rfl) ⟨283175, by rfl⟩) R566351
theorem R2016359 : Reach 2016359 := rs (se 1 (by rfl) ⟨1512269, by rfl⟩) R3024539
theorem R312923 : Reach 312923 := rs (se 1 (by rfl) ⟨234692, by rfl⟩) R469385
theorem R116603 : Reach 116603 := rs (se 1 (by rfl) ⟨87452, by rfl⟩) R174905
theorem R149627 : Reach 149627 := rs (se 1 (by rfl) ⟨112220, by rfl⟩) R224441
theorem R51367 : Reach 51367 := rs (se 1 (by rfl) ⟨38525, by rfl⟩) R77051
theorem R84935 : Reach 84935 := rs (se 1 (by rfl) ⟨63701, by rfl⟩) R127403
theorem R117791 : Reach 117791 := rs (se 1 (by rfl) ⟨88343, by rfl⟩) R176687
theorem R249311 : Reach 249311 := rs (se 1 (by rfl) ⟨186983, by rfl⟩) R373967
theorem R53663 : Reach 53663 := rs (se 1 (by rfl) ⟨40247, by rfl⟩) R80495
theorem R86953 : Reach 86953 := rs (se 2 (by rfl) ⟨32607, by rfl⟩) R65215
theorem R185327 : Reach 185327 := rs (se 1 (by rfl) ⟨138995, by rfl⟩) R277991
theorem R152999 : Reach 152999 := rs (se 1 (by rfl) ⟨114749, by rfl⟩) R229499
theorem R940409 : Reach 940409 := rs (se 2 (by rfl) ⟨352653, by rfl⟩) R705307
theorem R1203011 : Reach 1203011 := rs (se 1 (by rfl) ⟨902258, by rfl⟩) R1804517
theorem R187559 : Reach 187559 := rs (se 1 (by rfl) ⟨140669, by rfl⟩) R281339
theorem R518183 : Reach 518183 := rs (se 1 (by rfl) ⟨388637, by rfl⟩) R777275
theorem R1929071 : Reach 1929071 := rs (se 1 (by rfl) ⟨1446803, by rfl⟩) R2893607
theorem R61951 : Reach 61951 := rs (se 1 (by rfl) ⟨46463, by rfl⟩) R92927
theorem R12449771 : Reach 12449771 := rs (se 1 (by rfl) ⟨9337328, by rfl⟩) R18674657
theorem R2063141 : Reach 2063141 := rs (se 4 (by rfl) ⟨193419, by rfl⟩) R386839
theorem R523583 : Reach 523583 := rs (se 1 (by rfl) ⟨392687, by rfl⟩) R785375
theorem R261791 : Reach 261791 := rs (se 1 (by rfl) ⟨196343, by rfl⟩) R392687
theorem R1245565 : Reach 1245565 := rs (se 3 (by rfl) ⟨233543, by rfl⟩) R467087
theorem R1344239 : Reach 1344239 := rs (se 1 (by rfl) ⟨1008179, by rfl⟩) R2016359
theorem R166207 : Reach 166207 := rs (se 1 (by rfl) ⟨124655, by rfl⟩) R249311
theorem R200171 : Reach 200171 := rs (se 1 (by rfl) ⟨150128, by rfl⟩) R300257
theorem R101999 : Reach 101999 := rs (se 1 (by rfl) ⟨76499, by rfl⟩) R152999
theorem R233225 : Reach 233225 := rs (se 2 (by rfl) ⟨87459, by rfl⟩) R174919
theorem R626939 : Reach 626939 := rs (se 1 (by rfl) ⟨470204, by rfl⟩) R940409
theorem R399005 : Reach 399005 := rs (se 3 (by rfl) ⟨74813, by rfl⟩) R149627
theorem R138431 : Reach 138431 := rs (se 1 (by rfl) ⟨103823, by rfl⟩) R207647
theorem R1286047 : Reach 1286047 := rs (se 1 (by rfl) ⟨964535, by rfl⟩) R1929071
theorem R8299847 : Reach 8299847 := rs (se 1 (by rfl) ⟨6224885, by rfl⟩) R12449771
theorem R174527 : Reach 174527 := rs (se 1 (by rfl) ⟨130895, by rfl⟩) R261791
theorem R175769 : Reach 175769 := rs (se 2 (by rfl) ⟨65913, by rfl⟩) R131827
theorem R208615 : Reach 208615 := rs (se 1 (by rfl) ⟨156461, by rfl⟩) R312923
theorem R77735 : Reach 77735 := rs (se 1 (by rfl) ⟨58301, by rfl⟩) R116603
theorem R1421995 : Reach 1421995 := rs (se 1 (by rfl) ⟨1066496, by rfl⟩) R2132993
theorem R78527 : Reach 78527 := rs (se 1 (by rfl) ⟨58895, by rfl⟩) R117791
theorem R669161 : Reach 669161 := rs (se 2 (by rfl) ⟨250935, by rfl⟩) R501871
theorem R113519 : Reach 113519 := rs (se 1 (by rfl) ⟨85139, by rfl⟩) R170279
theorem R802007 : Reach 802007 := rs (se 1 (by rfl) ⟨601505, by rfl⟩) R1203011
theorem R82601 : Reach 82601 := rs (se 2 (by rfl) ⟨30975, by rfl⟩) R61951
theorem R246539 : Reach 246539 := rs (se 1 (by rfl) ⟨184904, by rfl⟩) R369809
theorem R115937 : Reach 115937 := rs (se 2 (by rfl) ⟨43476, by rfl⟩) R86953
theorem R345455 : Reach 345455 := rs (se 1 (by rfl) ⟨259091, by rfl⟩) R518183
theorem R51195 : Reach 51195 := rs (se 1 (by rfl) ⟨38396, by rfl⟩) R76793
theorem R411641 : Reach 411641 := rs (se 2 (by rfl) ⟨154365, by rfl⟩) R308731
theorem R51327 : Reach 51327 := rs (se 1 (by rfl) ⟨38495, by rfl⟩) R76991
theorem R51439 : Reach 51439 := rs (se 1 (by rfl) ⟨38579, by rfl⟩) R77159
theorem R117359 : Reach 117359 := rs (se 1 (by rfl) ⟨88019, by rfl⟩) R176039
theorem R117863 : Reach 117863 := rs (se 1 (by rfl) ⟨88397, by rfl⟩) R176795
theorem R53787 : Reach 53787 := rs (se 1 (by rfl) ⟨40340, by rfl⟩) R80681
theorem R54087 : Reach 54087 := rs (se 1 (by rfl) ⟨40565, by rfl⟩) R81131
theorem R349055 : Reach 349055 := rs (se 1 (by rfl) ⟨261791, by rfl⟩) R523583
theorem R54687 : Reach 54687 := rs (se 1 (by rfl) ⟨41015, by rfl⟩) R82031
theorem R120311 : Reach 120311 := rs (se 1 (by rfl) ⟨90233, by rfl⟩) R180467
theorem R54831 : Reach 54831 := rs (se 1 (by rfl) ⟨41123, by rfl⟩) R82247
theorem R251711 : Reach 251711 := rs (se 1 (by rfl) ⟨188783, by rfl⟩) R377567
theorem R56623 : Reach 56623 := rs (se 1 (by rfl) ⟨42467, by rfl⟩) R84935
theorem R123551 : Reach 123551 := rs (se 1 (by rfl) ⟨92663, by rfl⟩) R185327
theorem R125039 : Reach 125039 := rs (se 1 (by rfl) ⟨93779, by rfl⟩) R187559
theorem R1602935 : Reach 1602935 := rs (se 1 (by rfl) ⟨1202201, by rfl⟩) R2404403
theorem R325385 : Reach 325385 := rs (se 2 (by rfl) ⟨122019, by rfl⟩) R244039
theorem R1375427 : Reach 1375427 := rs (se 1 (by rfl) ⟨1031570, by rfl⟩) R2063141
theorem R491291 : Reach 491291 := rs (se 1 (by rfl) ⟨368468, by rfl⟩) R736937
theorem R164359 : Reach 164359 := rs (se 1 (by rfl) ⟨123269, by rfl⟩) R246539
theorem R230303 : Reach 230303 := rs (se 1 (by rfl) ⟨172727, by rfl⟩) R345455
theorem R133447 : Reach 133447 := rs (se 1 (by rfl) ⟨100085, by rfl⟩) R200171
theorem R232703 : Reach 232703 := rs (se 1 (by rfl) ⟨174527, by rfl⟩) R349055
theorem R266003 : Reach 266003 := rs (se 1 (by rfl) ⟨199502, by rfl⟩) R399005
theorem R167807 : Reach 167807 := rs (se 1 (by rfl) ⟨125855, by rfl⟩) R251711
theorem R302717 : Reach 302717 := rs (se 3 (by rfl) ⟨56759, by rfl⟩) R113519
theorem R271997 : Reach 271997 := rs (se 3 (by rfl) ⟨50999, by rfl⟩) R101999
theorem R75497 : Reach 75497 := rs (se 2 (by rfl) ⟨28311, by rfl⟩) R56623
theorem R534671 : Reach 534671 := rs (se 1 (by rfl) ⟨401003, by rfl⟩) R802007
theorem R1714729 : Reach 1714729 := rs (se 2 (by rfl) ⟨643023, by rfl⟩) R1286047
theorem R896159 : Reach 896159 := rs (se 1 (by rfl) ⟨672119, by rfl⟩) R1344239
theorem R77291 : Reach 77291 := rs (se 1 (by rfl) ⟨57968, by rfl⟩) R115937
theorem R274427 : Reach 274427 := rs (se 1 (by rfl) ⟨205820, by rfl⟩) R411641
theorem R78239 : Reach 78239 := rs (se 1 (by rfl) ⟨58679, by rfl⟩) R117359
theorem R78575 : Reach 78575 := rs (se 1 (by rfl) ⟨58931, by rfl⟩) R117863
theorem R80207 : Reach 80207 := rs (se 1 (by rfl) ⟨60155, by rfl⟩) R120311
theorem R278153 : Reach 278153 := rs (se 2 (by rfl) ⟨104307, by rfl⟩) R208615
theorem R82367 : Reach 82367 := rs (se 1 (by rfl) ⟨61775, by rfl⟩) R123551
theorem R83359 : Reach 83359 := rs (se 1 (by rfl) ⟨62519, by rfl⟩) R125039
theorem R116351 : Reach 116351 := rs (se 1 (by rfl) ⟨87263, by rfl⟩) R174527
theorem R117179 : Reach 117179 := rs (se 1 (by rfl) ⟨87884, by rfl⟩) R175769
theorem R51823 : Reach 51823 := rs (se 1 (by rfl) ⟨38867, by rfl⟩) R77735
theorem R52351 : Reach 52351 := rs (se 1 (by rfl) ⟨39263, by rfl⟩) R78527
theorem R1068623 : Reach 1068623 := rs (se 1 (by rfl) ⟨801467, by rfl⟩) R1602935
theorem R446107 : Reach 446107 := rs (se 1 (by rfl) ⟨334580, by rfl⟩) R669161
theorem R216923 : Reach 216923 := rs (se 1 (by rfl) ⟨162692, by rfl⟩) R325385
theorem R55067 : Reach 55067 := rs (se 1 (by rfl) ⟨41300, by rfl⟩) R82601
theorem R1660753 : Reach 1660753 := rs (se 2 (by rfl) ⟨622782, by rfl⟩) R1245565
theorem R155483 : Reach 155483 := rs (se 1 (by rfl) ⟨116612, by rfl⟩) R233225
theorem R417959 : Reach 417959 := rs (se 1 (by rfl) ⟨313469, by rfl⟩) R626939
theorem R221609 : Reach 221609 := rs (se 2 (by rfl) ⟨83103, by rfl⟩) R166207
theorem R92287 : Reach 92287 := rs (se 1 (by rfl) ⟨69215, by rfl⟩) R138431
theorem R5533231 : Reach 5533231 := rs (se 1 (by rfl) ⟨4149923, by rfl⟩) R8299847
theorem R1895993 : Reach 1895993 := rs (se 2 (by rfl) ⟨710997, by rfl⟩) R1421995
theorem R3667805 : Reach 3667805 := rs (se 3 (by rfl) ⟨687713, by rfl⟩) R1375427
theorem R327527 : Reach 327527 := rs (se 1 (by rfl) ⟨245645, by rfl⟩) R491291
theorem R201325 : Reach 201325 := rs (se 3 (by rfl) ⟨37748, by rfl⟩) R75497
theorem R7377641 : Reach 7377641 := rs (se 2 (by rfl) ⟨2766615, by rfl⟩) R5533231
theorem R594809 : Reach 594809 := rs (se 2 (by rfl) ⟨223053, by rfl⟩) R446107
theorem R201811 : Reach 201811 := rs (se 1 (by rfl) ⟨151358, by rfl⟩) R302717
theorem R103655 : Reach 103655 := rs (se 1 (by rfl) ⟨77741, by rfl⟩) R155483
theorem R597439 : Reach 597439 := rs (se 1 (by rfl) ⟨448079, by rfl⟩) R896159
theorem R77567 : Reach 77567 := rs (se 1 (by rfl) ⟨58175, by rfl⟩) R116351
theorem R78119 : Reach 78119 := rs (se 1 (by rfl) ⟨58589, by rfl⟩) R117179
theorem R111145 : Reach 111145 := rs (se 2 (by rfl) ⟨41679, by rfl⟩) R83359
theorem R177335 : Reach 177335 := rs (se 1 (by rfl) ⟨133001, by rfl⟩) R266003
theorem R111871 : Reach 111871 := rs (se 1 (by rfl) ⟨83903, by rfl⟩) R167807
theorem R177929 : Reach 177929 := rs (se 2 (by rfl) ⟨66723, by rfl⟩) R133447
theorem R278639 : Reach 278639 := rs (se 1 (by rfl) ⟨208979, by rfl⟩) R417959
theorem R147739 : Reach 147739 := rs (se 1 (by rfl) ⟨110804, by rfl⟩) R221609
theorem R181331 : Reach 181331 := rs (se 1 (by rfl) ⟨135998, by rfl⟩) R271997
theorem R51527 : Reach 51527 := rs (se 1 (by rfl) ⟨38645, by rfl⟩) R77291
theorem R1263995 : Reach 1263995 := rs (se 1 (by rfl) ⟨947996, by rfl⟩) R1895993
theorem R2214337 : Reach 2214337 := rs (se 2 (by rfl) ⟨830376, by rfl⟩) R1660753
theorem R182951 : Reach 182951 := rs (se 1 (by rfl) ⟨137213, by rfl⟩) R274427
theorem R52159 : Reach 52159 := rs (se 1 (by rfl) ⟨39119, by rfl⟩) R78239
theorem R52383 : Reach 52383 := rs (se 1 (by rfl) ⟨39287, by rfl⟩) R78575
theorem R2445203 : Reach 2445203 := rs (se 1 (by rfl) ⟨1833902, by rfl⟩) R3667805
theorem R53471 : Reach 53471 := rs (se 1 (by rfl) ⟨40103, by rfl⟩) R80207
theorem R578461 : Reach 578461 := rs (se 3 (by rfl) ⟨108461, by rfl⟩) R216923
theorem R185435 : Reach 185435 := rs (se 1 (by rfl) ⟨139076, by rfl⟩) R278153
theorem R218351 : Reach 218351 := rs (se 1 (by rfl) ⟨163763, by rfl⟩) R327527
theorem R54911 : Reach 54911 := rs (se 1 (by rfl) ⟨41183, by rfl⟩) R82367
theorem R153535 : Reach 153535 := rs (se 1 (by rfl) ⟨115151, by rfl⟩) R230303
theorem R219145 : Reach 219145 := rs (se 2 (by rfl) ⟨82179, by rfl⟩) R164359
theorem R155135 : Reach 155135 := rs (se 1 (by rfl) ⟨116351, by rfl⟩) R232703
theorem R712415 : Reach 712415 := rs (se 1 (by rfl) ⟨534311, by rfl⟩) R1068623
theorem R123049 : Reach 123049 := rs (se 2 (by rfl) ⟨46143, by rfl⟩) R92287
theorem R2286305 : Reach 2286305 := rs (se 2 (by rfl) ⟨857364, by rfl⟩) R1714729
theorem R356447 : Reach 356447 := rs (se 1 (by rfl) ⟨267335, by rfl⟩) R534671
theorem R950525 : Reach 950525 := rs (se 3 (by rfl) ⟨178223, by rfl⟩) R356447
theorem R196985 : Reach 196985 := rs (se 2 (by rfl) ⟨73869, by rfl⟩) R147739
theorem R656261 : Reach 656261 := rs (se 4 (by rfl) ⟨61524, by rfl⟩) R123049
theorem R4918427 : Reach 4918427 := rs (se 1 (by rfl) ⟨3688820, by rfl⟩) R7377641
theorem R396539 : Reach 396539 := rs (se 1 (by rfl) ⟨297404, by rfl⟩) R594809
theorem R2952449 : Reach 2952449 := rs (se 2 (by rfl) ⟨1107168, by rfl⟩) R2214337
theorem R69103 : Reach 69103 := rs (se 1 (by rfl) ⟨51827, by rfl⟩) R103655
theorem R103423 : Reach 103423 := rs (se 1 (by rfl) ⟨77567, by rfl⟩) R155135
theorem R268433 : Reach 268433 := rs (se 2 (by rfl) ⟨100662, by rfl⟩) R201325
theorem R269081 : Reach 269081 := rs (se 2 (by rfl) ⟨100905, by rfl⟩) R201811
theorem R3186341 : Reach 3186341 := rs (se 4 (by rfl) ⟨298719, by rfl⟩) R597439
theorem R204713 : Reach 204713 := rs (se 2 (by rfl) ⟨76767, by rfl⟩) R153535
theorem R145567 : Reach 145567 := rs (se 1 (by rfl) ⟨109175, by rfl⟩) R218351
theorem R1524203 : Reach 1524203 := rs (se 1 (by rfl) ⟨1143152, by rfl⟩) R2286305
theorem R148193 : Reach 148193 := rs (se 2 (by rfl) ⟨55572, by rfl⟩) R111145
theorem R771281 : Reach 771281 := rs (se 2 (by rfl) ⟨289230, by rfl⟩) R578461
theorem R149161 : Reach 149161 := rs (se 2 (by rfl) ⟨55935, by rfl⟩) R111871
theorem R51711 : Reach 51711 := rs (se 1 (by rfl) ⟨38783, by rfl⟩) R77567
theorem R52079 : Reach 52079 := rs (se 1 (by rfl) ⟨39059, by rfl⟩) R78119
theorem R118223 : Reach 118223 := rs (se 1 (by rfl) ⟨88667, by rfl⟩) R177335
theorem R118619 : Reach 118619 := rs (se 1 (by rfl) ⟨88964, by rfl⟩) R177929
theorem R185759 : Reach 185759 := rs (se 1 (by rfl) ⟨139319, by rfl⟩) R278639
theorem R120887 : Reach 120887 := rs (se 1 (by rfl) ⟨90665, by rfl⟩) R181331
theorem R842663 : Reach 842663 := rs (se 1 (by rfl) ⟨631997, by rfl⟩) R1263995
theorem R121967 : Reach 121967 := rs (se 1 (by rfl) ⟨91475, by rfl⟩) R182951
theorem R1630135 : Reach 1630135 := rs (se 1 (by rfl) ⟨1222601, by rfl⟩) R2445203
theorem R123623 : Reach 123623 := rs (se 1 (by rfl) ⟨92717, by rfl⟩) R185435
theorem R292193 : Reach 292193 := rs (se 2 (by rfl) ⟨109572, by rfl⟩) R219145
theorem R1899773 : Reach 1899773 := rs (se 3 (by rfl) ⟨356207, by rfl⟩) R712415
theorem R131323 : Reach 131323 := rs (se 1 (by rfl) ⟨98492, by rfl⟩) R196985
theorem R1016135 : Reach 1016135 := rs (se 1 (by rfl) ⟨762101, by rfl⟩) R1524203
theorem R98795 : Reach 98795 := rs (se 1 (by rfl) ⟨74096, by rfl⟩) R148193
theorem R3278951 : Reach 3278951 := rs (se 1 (by rfl) ⟨2459213, by rfl⟩) R4918427
theorem R264359 : Reach 264359 := rs (se 1 (by rfl) ⟨198269, by rfl⟩) R396539
theorem R1968299 : Reach 1968299 := rs (se 1 (by rfl) ⟨1476224, by rfl⟩) R2952449
theorem R198881 : Reach 198881 := rs (se 2 (by rfl) ⟨74580, by rfl⟩) R149161
theorem R561775 : Reach 561775 := rs (se 1 (by rfl) ⟨421331, by rfl⟩) R842663
theorem R136475 : Reach 136475 := rs (se 1 (by rfl) ⟨102356, by rfl⟩) R204713
theorem R137897 : Reach 137897 := rs (se 2 (by rfl) ⟨51711, by rfl⟩) R103423
theorem R2173513 : Reach 2173513 := rs (se 2 (by rfl) ⟨815067, by rfl⟩) R1630135
theorem R633683 : Reach 633683 := rs (se 1 (by rfl) ⟨475262, by rfl⟩) R950525
theorem R437507 : Reach 437507 := rs (se 1 (by rfl) ⟨328130, by rfl⟩) R656261
theorem R78815 : Reach 78815 := rs (se 1 (by rfl) ⟨59111, by rfl⟩) R118223
theorem R79079 : Reach 79079 := rs (se 1 (by rfl) ⟨59309, by rfl⟩) R118619
theorem R80591 : Reach 80591 := rs (se 1 (by rfl) ⟨60443, by rfl⟩) R120887
theorem R178955 : Reach 178955 := rs (se 1 (by rfl) ⟨134216, by rfl⟩) R268433
theorem R179387 : Reach 179387 := rs (se 1 (by rfl) ⟨134540, by rfl⟩) R269081
theorem R81311 : Reach 81311 := rs (se 1 (by rfl) ⟨60983, by rfl⟩) R121967
theorem R82415 : Reach 82415 := rs (se 1 (by rfl) ⟨61811, by rfl⟩) R123623
theorem R1266515 : Reach 1266515 := rs (se 1 (by rfl) ⟨949886, by rfl⟩) R1899773
theorem R514187 : Reach 514187 := rs (se 1 (by rfl) ⟨385640, by rfl⟩) R771281
theorem R123839 : Reach 123839 := rs (se 1 (by rfl) ⟨92879, by rfl⟩) R185759
theorem R92137 : Reach 92137 := rs (se 2 (by rfl) ⟨34551, by rfl⟩) R69103
theorem R2124227 : Reach 2124227 := rs (se 1 (by rfl) ⟨1593170, by rfl⟩) R3186341
theorem R194089 : Reach 194089 := rs (se 2 (by rfl) ⟨72783, by rfl⟩) R145567
theorem R194795 : Reach 194795 := rs (se 1 (by rfl) ⟨146096, by rfl⟩) R292193
theorem R65863 : Reach 65863 := rs (se 1 (by rfl) ⟨49397, by rfl⟩) R98795
theorem R1312199 : Reach 1312199 := rs (se 1 (by rfl) ⟨984149, by rfl⟩) R1968299
theorem R132587 : Reach 132587 := rs (se 1 (by rfl) ⟨99440, by rfl⟩) R198881
theorem R1416151 : Reach 1416151 := rs (se 1 (by rfl) ⟨1062113, by rfl⟩) R2124227
theorem R175097 : Reach 175097 := rs (se 2 (by rfl) ⟨65661, by rfl⟩) R131323
theorem R176239 : Reach 176239 := rs (se 1 (by rfl) ⟨132179, by rfl⟩) R264359
theorem R2898017 : Reach 2898017 := rs (se 2 (by rfl) ⟨1086756, by rfl⟩) R2173513
theorem R342791 : Reach 342791 := rs (se 1 (by rfl) ⟨257093, by rfl⟩) R514187
theorem R82559 : Reach 82559 := rs (se 1 (by rfl) ⟨61919, by rfl⟩) R123839
theorem R1689821 : Reach 1689821 := rs (se 3 (by rfl) ⟨316841, by rfl⟩) R633683
theorem R52543 : Reach 52543 := rs (se 1 (by rfl) ⟨39407, by rfl⟩) R78815
theorem R52719 : Reach 52719 := rs (se 1 (by rfl) ⟨39539, by rfl⟩) R79079
theorem R53727 : Reach 53727 := rs (se 1 (by rfl) ⟨40295, by rfl⟩) R80591
theorem R119303 : Reach 119303 := rs (se 1 (by rfl) ⟨89477, by rfl⟩) R178955
theorem R119591 : Reach 119591 := rs (se 1 (by rfl) ⟨89693, by rfl⟩) R179387
theorem R54207 : Reach 54207 := rs (se 1 (by rfl) ⟨40655, by rfl⟩) R81311
theorem R677423 : Reach 677423 := rs (se 1 (by rfl) ⟨508067, by rfl⟩) R1016135
theorem R54943 : Reach 54943 := rs (se 1 (by rfl) ⟨41207, by rfl⟩) R82415
theorem R2185967 : Reach 2185967 := rs (se 1 (by rfl) ⟨1639475, by rfl⟩) R3278951
theorem R122849 : Reach 122849 := rs (se 2 (by rfl) ⟨46068, by rfl⟩) R92137
theorem R844343 : Reach 844343 := rs (se 1 (by rfl) ⟨633257, by rfl⟩) R1266515
theorem R90983 : Reach 90983 := rs (se 1 (by rfl) ⟨68237, by rfl⟩) R136475
theorem R91931 : Reach 91931 := rs (se 1 (by rfl) ⟨68948, by rfl⟩) R137897
theorem R749033 : Reach 749033 := rs (se 2 (by rfl) ⟨280887, by rfl⟩) R561775
theorem R258785 : Reach 258785 := rs (se 2 (by rfl) ⟨97044, by rfl⟩) R194089
theorem R291671 : Reach 291671 := rs (se 1 (by rfl) ⟨218753, by rfl⟩) R437507
theorem R129863 : Reach 129863 := rs (se 1 (by rfl) ⟨97397, by rfl⟩) R194795
theorem R562895 : Reach 562895 := rs (se 1 (by rfl) ⟨422171, by rfl⟩) R844343
theorem R499355 : Reach 499355 := rs (se 1 (by rfl) ⟨374516, by rfl⟩) R749033
theorem R172523 : Reach 172523 := rs (se 1 (by rfl) ⟨129392, by rfl⟩) R258785
theorem R1126547 : Reach 1126547 := rs (se 1 (by rfl) ⟨844910, by rfl⟩) R1689821
theorem R79535 : Reach 79535 := rs (se 1 (by rfl) ⟨59651, by rfl⟩) R119303
theorem R79727 : Reach 79727 := rs (se 1 (by rfl) ⟨59795, by rfl⟩) R119591
theorem R245149 : Reach 245149 := rs (se 3 (by rfl) ⟨45965, by rfl⟩) R91931
theorem R81899 : Reach 81899 := rs (se 1 (by rfl) ⟨61424, by rfl⟩) R122849
theorem R116731 : Reach 116731 := rs (se 1 (by rfl) ⟨87548, by rfl⟩) R175097
theorem R1888201 : Reach 1888201 := rs (se 2 (by rfl) ⟨708075, by rfl⟩) R1416151
theorem R86575 : Reach 86575 := rs (se 1 (by rfl) ⟨64931, by rfl⟩) R129863
theorem R55039 : Reach 55039 := rs (se 1 (by rfl) ⟨41279, by rfl⟩) R82559
theorem R87817 : Reach 87817 := rs (se 2 (by rfl) ⟨32931, by rfl⟩) R65863
theorem R939941 : Reach 939941 := rs (se 4 (by rfl) ⟨88119, by rfl⟩) R176239
theorem R874799 : Reach 874799 := rs (se 1 (by rfl) ⟨656099, by rfl⟩) R1312199
theorem R88391 : Reach 88391 := rs (se 1 (by rfl) ⟨66293, by rfl⟩) R132587
theorem R451615 : Reach 451615 := rs (se 1 (by rfl) ⟨338711, by rfl⟩) R677423
theorem R60655 : Reach 60655 := rs (se 1 (by rfl) ⟨45491, by rfl⟩) R90983
theorem R5829245 : Reach 5829245 := rs (se 3 (by rfl) ⟨1092983, by rfl⟩) R2185967
theorem R194447 : Reach 194447 := rs (se 1 (by rfl) ⟨145835, by rfl⟩) R291671
theorem R1932011 : Reach 1932011 := rs (se 1 (by rfl) ⟨1449008, by rfl⟩) R2898017
theorem R228527 : Reach 228527 := rs (se 1 (by rfl) ⟨171395, by rfl⟩) R342791
theorem R626627 : Reach 626627 := rs (se 1 (by rfl) ⟨469970, by rfl⟩) R939941
theorem R332903 : Reach 332903 := rs (se 1 (by rfl) ⟨249677, by rfl⟩) R499355
theorem R1288007 : Reach 1288007 := rs (se 1 (by rfl) ⟨966005, by rfl⟩) R1932011
theorem R602153 : Reach 602153 := rs (se 2 (by rfl) ⟨225807, by rfl⟩) R451615
theorem R375263 : Reach 375263 := rs (se 1 (by rfl) ⟨281447, by rfl⟩) R562895
theorem R80873 : Reach 80873 := rs (se 2 (by rfl) ⟨30327, by rfl⟩) R60655
theorem R115015 : Reach 115015 := rs (se 1 (by rfl) ⟨86261, by rfl⟩) R172523
theorem R115433 : Reach 115433 := rs (se 2 (by rfl) ⟨43287, by rfl⟩) R86575
theorem R117089 : Reach 117089 := rs (se 2 (by rfl) ⟨43908, by rfl⟩) R87817
theorem R3886163 : Reach 3886163 := rs (se 1 (by rfl) ⟨2914622, by rfl⟩) R5829245
theorem R53023 : Reach 53023 := rs (se 1 (by rfl) ⟨39767, by rfl⟩) R79535
theorem R53151 : Reach 53151 := rs (se 1 (by rfl) ⟨39863, by rfl⟩) R79727
theorem R152351 : Reach 152351 := rs (se 1 (by rfl) ⟨114263, by rfl⟩) R228527
theorem R54599 : Reach 54599 := rs (se 1 (by rfl) ⟨40949, by rfl⟩) R81899
theorem R583199 : Reach 583199 := rs (se 1 (by rfl) ⟨437399, by rfl⟩) R874799
theorem R58927 : Reach 58927 := rs (se 1 (by rfl) ⟨44195, by rfl⟩) R88391
theorem R518525 : Reach 518525 := rs (se 3 (by rfl) ⟨97223, by rfl⟩) R194447
theorem R2517601 : Reach 2517601 := rs (se 2 (by rfl) ⟨944100, by rfl⟩) R1888201
theorem R1307461 : Reach 1307461 := rs (se 4 (by rfl) ⟨122574, by rfl⟩) R245149
theorem R751031 : Reach 751031 := rs (se 1 (by rfl) ⟨563273, by rfl⟩) R1126547
theorem R622565 : Reach 622565 := rs (se 4 (by rfl) ⟨58365, by rfl⟩) R116731
theorem R2590775 : Reach 2590775 := rs (se 1 (by rfl) ⟨1943081, by rfl⟩) R3886163
theorem R101567 : Reach 101567 := rs (se 1 (by rfl) ⟨76175, by rfl⟩) R152351
theorem R1743281 : Reach 1743281 := rs (se 2 (by rfl) ⟨653730, by rfl⟩) R1307461
theorem R858671 : Reach 858671 := rs (se 1 (by rfl) ⟨644003, by rfl⟩) R1288007
theorem R401435 : Reach 401435 := rs (se 1 (by rfl) ⟨301076, by rfl⟩) R602153
theorem R500687 : Reach 500687 := rs (se 1 (by rfl) ⟨375515, by rfl⟩) R751031
theorem R76955 : Reach 76955 := rs (se 1 (by rfl) ⟨57716, by rfl⟩) R115433
theorem R78059 : Reach 78059 := rs (se 1 (by rfl) ⟨58544, by rfl⟩) R117089
theorem R78569 : Reach 78569 := rs (se 2 (by rfl) ⟨29463, by rfl⟩) R58927
theorem R3356801 : Reach 3356801 := rs (se 2 (by rfl) ⟨1258800, by rfl⟩) R2517601
theorem R345683 : Reach 345683 := rs (se 1 (by rfl) ⟨259262, by rfl⟩) R518525
theorem R250175 : Reach 250175 := rs (se 1 (by rfl) ⟨187631, by rfl⟩) R375263
theorem R53915 : Reach 53915 := rs (se 1 (by rfl) ⟨40436, by rfl⟩) R80873
theorem R415043 : Reach 415043 := rs (se 1 (by rfl) ⟨311282, by rfl⟩) R622565
theorem R153353 : Reach 153353 := rs (se 2 (by rfl) ⟨57507, by rfl⟩) R115015
theorem R221935 : Reach 221935 := rs (se 1 (by rfl) ⟨166451, by rfl⟩) R332903
theorem R388799 : Reach 388799 := rs (se 1 (by rfl) ⟨291599, by rfl⟩) R583199
theorem R1671005 : Reach 1671005 := rs (se 3 (by rfl) ⟨313313, by rfl⟩) R626627
theorem R295913 : Reach 295913 := rs (se 2 (by rfl) ⟨110967, by rfl⟩) R221935
theorem R230455 : Reach 230455 := rs (se 1 (by rfl) ⟨172841, by rfl⟩) R345683
theorem R67711 : Reach 67711 := rs (se 1 (by rfl) ⟨50783, by rfl⟩) R101567
theorem R102235 : Reach 102235 := rs (se 1 (by rfl) ⟨76676, by rfl⟩) R153353
theorem R267623 : Reach 267623 := rs (se 1 (by rfl) ⟨200717, by rfl⟩) R401435
theorem R333791 : Reach 333791 := rs (se 1 (by rfl) ⟨250343, by rfl⟩) R500687
theorem R205213 : Reach 205213 := rs (se 3 (by rfl) ⟨38477, by rfl⟩) R76955
theorem R2237867 : Reach 2237867 := rs (se 1 (by rfl) ⟨1678400, by rfl⟩) R3356801
theorem R667133 : Reach 667133 := rs (se 3 (by rfl) ⟨125087, by rfl⟩) R250175
theorem R276695 : Reach 276695 := rs (se 1 (by rfl) ⟨207521, by rfl⟩) R415043
theorem R1162187 : Reach 1162187 := rs (se 1 (by rfl) ⟨871640, by rfl⟩) R1743281
theorem R572447 : Reach 572447 := rs (se 1 (by rfl) ⟨429335, by rfl⟩) R858671
theorem R51303 : Reach 51303 := rs (se 1 (by rfl) ⟨38477, by rfl⟩) R76955
theorem R52039 : Reach 52039 := rs (se 1 (by rfl) ⟨39029, by rfl⟩) R78059
theorem R52379 : Reach 52379 := rs (se 1 (by rfl) ⟨39284, by rfl⟩) R78569
theorem R1727183 : Reach 1727183 := rs (se 1 (by rfl) ⟨1295387, by rfl⟩) R2590775
theorem R259199 : Reach 259199 := rs (se 1 (by rfl) ⟨194399, by rfl⟩) R388799
theorem R1114003 : Reach 1114003 := rs (se 1 (by rfl) ⟨835502, by rfl⟩) R1671005
theorem R197275 : Reach 197275 := rs (se 1 (by rfl) ⟨147956, by rfl⟩) R295913
theorem R136313 : Reach 136313 := rs (se 2 (by rfl) ⟨51117, by rfl⟩) R102235
theorem R172799 : Reach 172799 := rs (se 1 (by rfl) ⟨129599, by rfl⟩) R259199
theorem R5941349 : Reach 5941349 := rs (se 4 (by rfl) ⟨557001, by rfl⟩) R1114003
theorem R273617 : Reach 273617 := rs (se 2 (by rfl) ⟨102606, by rfl⟩) R205213
theorem R307273 : Reach 307273 := rs (se 2 (by rfl) ⟨115227, by rfl⟩) R230455
theorem R178415 : Reach 178415 := rs (se 1 (by rfl) ⟨133811, by rfl⟩) R267623
theorem R1491911 : Reach 1491911 := rs (se 1 (by rfl) ⟨1118933, by rfl⟩) R2237867
theorem R4605821 : Reach 4605821 := rs (se 3 (by rfl) ⟨863591, by rfl⟩) R1727183
theorem R444755 : Reach 444755 := rs (se 1 (by rfl) ⟨333566, by rfl⟩) R667133
theorem R184463 : Reach 184463 := rs (se 1 (by rfl) ⟨138347, by rfl⟩) R276695
theorem R774791 : Reach 774791 := rs (se 1 (by rfl) ⟨581093, by rfl⟩) R1162187
theorem R381631 : Reach 381631 := rs (se 1 (by rfl) ⟨286223, by rfl⟩) R572447
theorem R90281 : Reach 90281 := rs (se 2 (by rfl) ⟨33855, by rfl⟩) R67711
theorem R222527 : Reach 222527 := rs (se 1 (by rfl) ⟨166895, by rfl⟩) R333791
theorem R263033 : Reach 263033 := rs (se 2 (by rfl) ⟨98637, by rfl⟩) R197275
theorem R296503 : Reach 296503 := rs (se 1 (by rfl) ⟨222377, by rfl⟩) R444755
theorem R593405 : Reach 593405 := rs (se 3 (by rfl) ⟨111263, by rfl⟩) R222527
theorem R994607 : Reach 994607 := rs (se 1 (by rfl) ⟨745955, by rfl⟩) R1491911
theorem R409697 : Reach 409697 := rs (se 2 (by rfl) ⟨153636, by rfl⟩) R307273
theorem R115199 : Reach 115199 := rs (se 1 (by rfl) ⟨86399, by rfl⟩) R172799
theorem R508841 : Reach 508841 := rs (se 2 (by rfl) ⟨190815, by rfl⟩) R381631
theorem R182411 : Reach 182411 := rs (se 1 (by rfl) ⟨136808, by rfl⟩) R273617
theorem R118943 : Reach 118943 := rs (se 1 (by rfl) ⟨89207, by rfl⟩) R178415
theorem R3070547 : Reach 3070547 := rs (se 1 (by rfl) ⟨2302910, by rfl⟩) R4605821
theorem R122975 : Reach 122975 := rs (se 1 (by rfl) ⟨92231, by rfl⟩) R184463
theorem R516527 : Reach 516527 := rs (se 1 (by rfl) ⟨387395, by rfl⟩) R774791
theorem R90875 : Reach 90875 := rs (se 1 (by rfl) ⟨68156, by rfl⟩) R136313
theorem R60187 : Reach 60187 := rs (se 1 (by rfl) ⟨45140, by rfl⟩) R90281
theorem R3960899 : Reach 3960899 := rs (se 1 (by rfl) ⟨2970674, by rfl⟩) R5941349
theorem R6325397 : Reach 6325397 := rs (se 6 (by rfl) ⟨148251, by rfl⟩) R296503
theorem R395603 : Reach 395603 := rs (se 1 (by rfl) ⟨296702, by rfl⟩) R593405
theorem R663071 : Reach 663071 := rs (se 1 (by rfl) ⟨497303, by rfl⟩) R994607
theorem R273131 : Reach 273131 := rs (se 1 (by rfl) ⟨204848, by rfl⟩) R409697
theorem R76799 : Reach 76799 := rs (se 1 (by rfl) ⟨57599, by rfl⟩) R115199
theorem R175355 : Reach 175355 := rs (se 1 (by rfl) ⟨131516, by rfl⟩) R263033
theorem R339227 : Reach 339227 := rs (se 1 (by rfl) ⟨254420, by rfl⟩) R508841
theorem R79295 : Reach 79295 := rs (se 1 (by rfl) ⟨59471, by rfl⟩) R118943
theorem R80249 : Reach 80249 := rs (se 2 (by rfl) ⟨30093, by rfl⟩) R60187
theorem R2047031 : Reach 2047031 := rs (se 1 (by rfl) ⟨1535273, by rfl⟩) R3070547
theorem R81983 : Reach 81983 := rs (se 1 (by rfl) ⟨61487, by rfl⟩) R122975
theorem R344351 : Reach 344351 := rs (se 1 (by rfl) ⟨258263, by rfl⟩) R516527
theorem R2640599 : Reach 2640599 := rs (se 1 (by rfl) ⟨1980449, by rfl⟩) R3960899
theorem R121607 : Reach 121607 := rs (se 1 (by rfl) ⟨91205, by rfl⟩) R182411
theorem R60583 : Reach 60583 := rs (se 1 (by rfl) ⟨45437, by rfl⟩) R90875
theorem R229567 : Reach 229567 := rs (se 1 (by rfl) ⟨172175, by rfl⟩) R344351
theorem R263735 : Reach 263735 := rs (se 1 (by rfl) ⟨197801, by rfl⟩) R395603
theorem R80777 : Reach 80777 := rs (se 2 (by rfl) ⟨30291, by rfl⟩) R60583
theorem R81071 : Reach 81071 := rs (se 1 (by rfl) ⟨60803, by rfl⟩) R121607
theorem R182087 : Reach 182087 := rs (se 1 (by rfl) ⟨136565, by rfl⟩) R273131
theorem R51199 : Reach 51199 := rs (se 1 (by rfl) ⟨38399, by rfl⟩) R76799
theorem R116903 : Reach 116903 := rs (se 1 (by rfl) ⟨87677, by rfl⟩) R175355
theorem R52863 : Reach 52863 := rs (se 1 (by rfl) ⟨39647, by rfl⟩) R79295
theorem R53499 : Reach 53499 := rs (se 1 (by rfl) ⟨40124, by rfl⟩) R80249
theorem R1364687 : Reach 1364687 := rs (se 1 (by rfl) ⟨1023515, by rfl⟩) R2047031
theorem R54655 : Reach 54655 := rs (se 1 (by rfl) ⟨40991, by rfl⟩) R81983
theorem R4216931 : Reach 4216931 := rs (se 1 (by rfl) ⟨3162698, by rfl⟩) R6325397
theorem R1760399 : Reach 1760399 := rs (se 1 (by rfl) ⟨1320299, by rfl⟩) R2640599
theorem R226151 : Reach 226151 := rs (se 1 (by rfl) ⟨169613, by rfl⟩) R339227
theorem R1768189 : Reach 1768189 := rs (se 3 (by rfl) ⟨331535, by rfl⟩) R663071
theorem R306089 : Reach 306089 := rs (se 2 (by rfl) ⟨114783, by rfl⟩) R229567
theorem R175823 : Reach 175823 := rs (se 1 (by rfl) ⟨131867, by rfl⟩) R263735
theorem R77935 : Reach 77935 := rs (se 1 (by rfl) ⟨58451, by rfl⟩) R116903
theorem R150767 : Reach 150767 := rs (se 1 (by rfl) ⟨113075, by rfl⟩) R226151
theorem R53851 : Reach 53851 := rs (se 1 (by rfl) ⟨40388, by rfl⟩) R80777
theorem R54047 : Reach 54047 := rs (se 1 (by rfl) ⟨40535, by rfl⟩) R81071
theorem R121391 : Reach 121391 := rs (se 1 (by rfl) ⟨91043, by rfl⟩) R182087
theorem R909791 : Reach 909791 := rs (se 1 (by rfl) ⟨682343, by rfl⟩) R1364687
theorem R2811287 : Reach 2811287 := rs (se 1 (by rfl) ⟨2108465, by rfl⟩) R4216931
theorem R1173599 : Reach 1173599 := rs (se 1 (by rfl) ⟨880199, by rfl⟩) R1760399
theorem R2357585 : Reach 2357585 := rs (se 2 (by rfl) ⟨884094, by rfl⟩) R1768189
theorem R100511 : Reach 100511 := rs (se 1 (by rfl) ⟨75383, by rfl⟩) R150767
theorem R103913 : Reach 103913 := rs (se 2 (by rfl) ⟨38967, by rfl⟩) R77935
theorem R1874191 : Reach 1874191 := rs (se 1 (by rfl) ⟨1405643, by rfl⟩) R2811287
theorem R204059 : Reach 204059 := rs (se 1 (by rfl) ⟨153044, by rfl⟩) R306089
theorem R80927 : Reach 80927 := rs (se 1 (by rfl) ⟨60695, by rfl⟩) R121391
theorem R606527 : Reach 606527 := rs (se 1 (by rfl) ⟨454895, by rfl⟩) R909791
theorem R117215 : Reach 117215 := rs (se 1 (by rfl) ⟨87911, by rfl⟩) R175823
theorem R782399 : Reach 782399 := rs (se 1 (by rfl) ⟨586799, by rfl⟩) R1173599
theorem R1571723 : Reach 1571723 := rs (se 1 (by rfl) ⟨1178792, by rfl⟩) R2357585
theorem R67007 : Reach 67007 := rs (se 1 (by rfl) ⟨50255, by rfl⟩) R100511
theorem R69275 : Reach 69275 := rs (se 1 (by rfl) ⟨51956, by rfl⟩) R103913
theorem R136039 : Reach 136039 := rs (se 1 (by rfl) ⟨102029, by rfl⟩) R204059
theorem R2498921 : Reach 2498921 := rs (se 2 (by rfl) ⟨937095, by rfl⟩) R1874191
theorem R404351 : Reach 404351 := rs (se 1 (by rfl) ⟨303263, by rfl⟩) R606527
theorem R78143 : Reach 78143 := rs (se 1 (by rfl) ⟨58607, by rfl⟩) R117215
theorem R53951 : Reach 53951 := rs (se 1 (by rfl) ⟨40463, by rfl⟩) R80927
theorem R2086397 : Reach 2086397 := rs (se 3 (by rfl) ⟨391199, by rfl⟩) R782399
theorem R1047815 : Reach 1047815 := rs (se 1 (by rfl) ⟨785861, by rfl⟩) R1571723
theorem R269567 : Reach 269567 := rs (se 1 (by rfl) ⟨202175, by rfl⟩) R404351
theorem R698543 : Reach 698543 := rs (se 1 (by rfl) ⟨523907, by rfl⟩) R1047815
theorem R1390931 : Reach 1390931 := rs (se 1 (by rfl) ⟨1043198, by rfl⟩) R2086397
theorem R178685 : Reach 178685 := rs (se 3 (by rfl) ⟨33503, by rfl⟩) R67007
theorem R181385 : Reach 181385 := rs (se 2 (by rfl) ⟨68019, by rfl⟩) R136039
theorem R52095 : Reach 52095 := rs (se 1 (by rfl) ⟨39071, by rfl⟩) R78143
theorem R184733 : Reach 184733 := rs (se 3 (by rfl) ⟨34637, by rfl⟩) R69275
theorem R1665947 : Reach 1665947 := rs (se 1 (by rfl) ⟨1249460, by rfl⟩) R2498921
theorem R465695 : Reach 465695 := rs (se 1 (by rfl) ⟨349271, by rfl⟩) R698543
theorem R927287 : Reach 927287 := rs (se 1 (by rfl) ⟨695465, by rfl⟩) R1390931
theorem R179711 : Reach 179711 := rs (se 1 (by rfl) ⟨134783, by rfl⟩) R269567
theorem R119123 : Reach 119123 := rs (se 1 (by rfl) ⟨89342, by rfl⟩) R178685
theorem R120923 : Reach 120923 := rs (se 1 (by rfl) ⟨90692, by rfl⟩) R181385
theorem R123155 : Reach 123155 := rs (se 1 (by rfl) ⟨92366, by rfl⟩) R184733
theorem R1110631 : Reach 1110631 := rs (se 1 (by rfl) ⟨832973, by rfl⟩) R1665947
theorem R1480841 : Reach 1480841 := rs (se 2 (by rfl) ⟨555315, by rfl⟩) R1110631
theorem R79415 : Reach 79415 := rs (se 1 (by rfl) ⟨59561, by rfl⟩) R119123
theorem R80615 : Reach 80615 := rs (se 1 (by rfl) ⟨60461, by rfl⟩) R120923
theorem R310463 : Reach 310463 := rs (se 1 (by rfl) ⟨232847, by rfl⟩) R465695
theorem R82103 : Reach 82103 := rs (se 1 (by rfl) ⟨61577, by rfl⟩) R123155
theorem R119807 : Reach 119807 := rs (se 1 (by rfl) ⟨89855, by rfl⟩) R179711
theorem R618191 : Reach 618191 := rs (se 1 (by rfl) ⟨463643, by rfl⟩) R927287
theorem R987227 : Reach 987227 := rs (se 1 (by rfl) ⟨740420, by rfl⟩) R1480841
theorem R206975 : Reach 206975 := rs (se 1 (by rfl) ⟨155231, by rfl⟩) R310463
theorem R79871 : Reach 79871 := rs (se 1 (by rfl) ⟨59903, by rfl⟩) R119807
theorem R412127 : Reach 412127 := rs (se 1 (by rfl) ⟨309095, by rfl⟩) R618191
theorem R52943 : Reach 52943 := rs (se 1 (by rfl) ⟨39707, by rfl⟩) R79415
theorem R53743 : Reach 53743 := rs (se 1 (by rfl) ⟨40307, by rfl⟩) R80615
theorem R54735 : Reach 54735 := rs (se 1 (by rfl) ⟨41051, by rfl⟩) R82103
theorem R658151 : Reach 658151 := rs (se 1 (by rfl) ⟨493613, by rfl⟩) R987227
theorem R137983 : Reach 137983 := rs (se 1 (by rfl) ⟨103487, by rfl⟩) R206975
theorem R274751 : Reach 274751 := rs (se 1 (by rfl) ⟨206063, by rfl⟩) R412127
theorem R53247 : Reach 53247 := rs (se 1 (by rfl) ⟨39935, by rfl⟩) R79871
theorem R438767 : Reach 438767 := rs (se 1 (by rfl) ⟨329075, by rfl⟩) R658151
theorem R183167 : Reach 183167 := rs (se 1 (by rfl) ⟨137375, by rfl⟩) R274751
theorem R183977 : Reach 183977 := rs (se 2 (by rfl) ⟨68991, by rfl⟩) R137983
theorem R122111 : Reach 122111 := rs (se 1 (by rfl) ⟨91583, by rfl⟩) R183167
theorem R122651 : Reach 122651 := rs (se 1 (by rfl) ⟨91988, by rfl⟩) R183977
theorem R292511 : Reach 292511 := rs (se 1 (by rfl) ⟨219383, by rfl⟩) R438767
theorem R81407 : Reach 81407 := rs (se 1 (by rfl) ⟨61055, by rfl⟩) R122111
theorem R81767 : Reach 81767 := rs (se 1 (by rfl) ⟨61325, by rfl⟩) R122651
theorem R195007 : Reach 195007 := rs (se 1 (by rfl) ⟨146255, by rfl⟩) R292511
theorem R54271 : Reach 54271 := rs (se 1 (by rfl) ⟨40703, by rfl⟩) R81407
theorem R54511 : Reach 54511 := rs (se 1 (by rfl) ⟨40883, by rfl⟩) R81767
theorem R260009 : Reach 260009 := rs (se 2 (by rfl) ⟨97503, by rfl⟩) R195007
theorem R173339 : Reach 173339 := rs (se 1 (by rfl) ⟨130004, by rfl⟩) R260009
theorem R115559 : Reach 115559 := rs (se 1 (by rfl) ⟨86669, by rfl⟩) R173339
theorem R77039 : Reach 77039 := rs (se 1 (by rfl) ⟨57779, by rfl⟩) R115559
theorem R51359 : Reach 51359 := rs (se 1 (by rfl) ⟨38519, by rfl⟩) R77039

theorem C0 (j : ℕ) (h1 : 25560 ≤ j) (h2 : j ≤ 26259) : Reach (2 * j + 1) := by
  interval_cases j
  · exact R51121
  · exact R51123
  · exact R51125
  · exact R51127
  · exact R51129
  · exact R51131
  · exact R51133
  · exact R51135
  · exact R51137
  · exact R51139
  · exact R51141
  · exact R51143
  · exact R51145
  · exact R51147
  · exact R51149
  · exact R51151
  · exact R51153
  · exact R51155
  · exact R51157
  · exact R51159
  · exact R51161
  · exact R51163
  · exact R51165
  · exact R51167
  · exact R51169
  · exact R51171
  · exact R51173
  · exact R51175
  · exact R51177
  · exact R51179
  · exact R51181
  · exact R51183
  · exact R51185
  · exact R51187
  · exact R51189
  · exact R51191
  · exact R51193
  · exact R51195
  · exact R51197
  · exact R51199
  · exact R51201
  · exact R51203
  · exact R51205
  · exact R51207
  · exact R51209
  · exact R51211
  · exact R51213
  · exact R51215
  · exact R51217
  · exact R51219
  · exact R51221
  · exact R51223
  · exact R51225
  · exact R51227
  · exact R51229
  · exact R51231
  · exact R51233
  · exact R51235
  · exact R51237
  · exact R51239
  · exact R51241
  · exact R51243
  · exact R51245
  · exact R51247
  · exact R51249
  · exact R51251
  · exact R51253
  · exact R51255
  · exact R51257
  · exact R51259
  · exact R51261
  · exact R51263
  · exact R51265
  · exact R51267
  · exact R51269
  · exact R51271
  · exact R51273
  · exact R51275
  · exact R51277
  · exact R51279
  · exact R51281
  · exact R51283
  · exact R51285
  · exact R51287
  · exact R51289
  · exact R51291
  · exact R51293
  · exact R51295
  · exact R51297
  · exact R51299
  · exact R51301
  · exact R51303
  · exact R51305
  · exact R51307
  · exact R51309
  · exact R51311
  · exact R51313
  · exact R51315
  · exact R51317
  · exact R51319
  · exact R51321
  · exact R51323
  · exact R51325
  · exact R51327
  · exact R51329
  · exact R51331
  · exact R51333
  · exact R51335
  · exact R51337
  · exact R51339
  · exact R51341
  · exact R51343
  · exact R51345
  · exact R51347
  · exact R51349
  · exact R51351
  · exact R51353
  · exact R51355
  · exact R51357
  · exact R51359
  · exact R51361
  · exact R51363
  · exact R51365
  · exact R51367
  · exact R51369
  · exact R51371
  · exact R51373
  · exact R51375
  · exact R51377
  · exact R51379
  · exact R51381
  · exact R51383
  · exact R51385
  · exact R51387
  · exact R51389
  · exact R51391
  · exact R51393
  · exact R51395
  · exact R51397
  · exact R51399
  · exact R51401
  · exact R51403
  · exact R51405
  · exact R51407
  · exact R51409
  · exact R51411
  · exact R51413
  · exact R51415
  · exact R51417
  · exact R51419
  · exact R51421
  · exact R51423
  · exact R51425
  · exact R51427
  · exact R51429
  · exact R51431
  · exact R51433
  · exact R51435
  · exact R51437
  · exact R51439
  · exact R51441
  · exact R51443
  · exact R51445
  · exact R51447
  · exact R51449
  · exact R51451
  · exact R51453
  · exact R51455
  · exact R51457
  · exact R51459
  · exact R51461
  · exact R51463
  · exact R51465
  · exact R51467
  · exact R51469
  · exact R51471
  · exact R51473
  · exact R51475
  · exact R51477
  · exact R51479
  · exact R51481
  · exact R51483
  · exact R51485
  · exact R51487
  · exact R51489
  · exact R51491
  · exact R51493
  · exact R51495
  · exact R51497
  · exact R51499
  · exact R51501
  · exact R51503
  · exact R51505
  · exact R51507
  · exact R51509
  · exact R51511
  · exact R51513
  · exact R51515
  · exact R51517
  · exact R51519
  · exact R51521
  · exact R51523
  · exact R51525
  · exact R51527
  · exact R51529
  · exact R51531
  · exact R51533
  · exact R51535
  · exact R51537
  · exact R51539
  · exact R51541
  · exact R51543
  · exact R51545
  · exact R51547
  · exact R51549
  · exact R51551
  · exact R51553
  · exact R51555
  · exact R51557
  · exact R51559
  · exact R51561
  · exact R51563
  · exact R51565
  · exact R51567
  · exact R51569
  · exact R51571
  · exact R51573
  · exact R51575
  · exact R51577
  · exact R51579
  · exact R51581
  · exact R51583
  · exact R51585
  · exact R51587
  · exact R51589
  · exact R51591
  · exact R51593
  · exact R51595
  · exact R51597
  · exact R51599
  · exact R51601
  · exact R51603
  · exact R51605
  · exact R51607
  · exact R51609
  · exact R51611
  · exact R51613
  · exact R51615
  · exact R51617
  · exact R51619
  · exact R51621
  · exact R51623
  · exact R51625
  · exact R51627
  · exact R51629
  · exact R51631
  · exact R51633
  · exact R51635
  · exact R51637
  · exact R51639
  · exact R51641
  · exact R51643
  · exact R51645
  · exact R51647
  · exact R51649
  · exact R51651
  · exact R51653
  · exact R51655
  · exact R51657
  · exact R51659
  · exact R51661
  · exact R51663
  · exact R51665
  · exact R51667
  · exact R51669
  · exact R51671
  · exact R51673
  · exact R51675
  · exact R51677
  · exact R51679
  · exact R51681
  · exact R51683
  · exact R51685
  · exact R51687
  · exact R51689
  · exact R51691
  · exact R51693
  · exact R51695
  · exact R51697
  · exact R51699
  · exact R51701
  · exact R51703
  · exact R51705
  · exact R51707
  · exact R51709
  · exact R51711
  · exact R51713
  · exact R51715
  · exact R51717
  · exact R51719
  · exact R51721
  · exact R51723
  · exact R51725
  · exact R51727
  · exact R51729
  · exact R51731
  · exact R51733
  · exact R51735
  · exact R51737
  · exact R51739
  · exact R51741
  · exact R51743
  · exact R51745
  · exact R51747
  · exact R51749
  · exact R51751
  · exact R51753
  · exact R51755
  · exact R51757
  · exact R51759
  · exact R51761
  · exact R51763
  · exact R51765
  · exact R51767
  · exact R51769
  · exact R51771
  · exact R51773
  · exact R51775
  · exact R51777
  · exact R51779
  · exact R51781
  · exact R51783
  · exact R51785
  · exact R51787
  · exact R51789
  · exact R51791
  · exact R51793
  · exact R51795
  · exact R51797
  · exact R51799
  · exact R51801
  · exact R51803
  · exact R51805
  · exact R51807
  · exact R51809
  · exact R51811
  · exact R51813
  · exact R51815
  · exact R51817
  · exact R51819
  · exact R51821
  · exact R51823
  · exact R51825
  · exact R51827
  · exact R51829
  · exact R51831
  · exact R51833
  · exact R51835
  · exact R51837
  · exact R51839
  · exact R51841
  · exact R51843
  · exact R51845
  · exact R51847
  · exact R51849
  · exact R51851
  · exact R51853
  · exact R51855
  · exact R51857
  · exact R51859
  · exact R51861
  · exact R51863
  · exact R51865
  · exact R51867
  · exact R51869
  · exact R51871
  · exact R51873
  · exact R51875
  · exact R51877
  · exact R51879
  · exact R51881
  · exact R51883
  · exact R51885
  · exact R51887
  · exact R51889
  · exact R51891
  · exact R51893
  · exact R51895
  · exact R51897
  · exact R51899
  · exact R51901
  · exact R51903
  · exact R51905
  · exact R51907
  · exact R51909
  · exact R51911
  · exact R51913
  · exact R51915
  · exact R51917
  · exact R51919
  · exact R51921
  · exact R51923
  · exact R51925
  · exact R51927
  · exact R51929
  · exact R51931
  · exact R51933
  · exact R51935
  · exact R51937
  · exact R51939
  · exact R51941
  · exact R51943
  · exact R51945
  · exact R51947
  · exact R51949
  · exact R51951
  · exact R51953
  · exact R51955
  · exact R51957
  · exact R51959
  · exact R51961
  · exact R51963
  · exact R51965
  · exact R51967
  · exact R51969
  · exact R51971
  · exact R51973
  · exact R51975
  · exact R51977
  · exact R51979
  · exact R51981
  · exact R51983
  · exact R51985
  · exact R51987
  · exact R51989
  · exact R51991
  · exact R51993
  · exact R51995
  · exact R51997
  · exact R51999
  · exact R52001
  · exact R52003
  · exact R52005
  · exact R52007
  · exact R52009
  · exact R52011
  · exact R52013
  · exact R52015
  · exact R52017
  · exact R52019
  · exact R52021
  · exact R52023
  · exact R52025
  · exact R52027
  · exact R52029
  · exact R52031
  · exact R52033
  · exact R52035
  · exact R52037
  · exact R52039
  · exact R52041
  · exact R52043
  · exact R52045
  · exact R52047
  · exact R52049
  · exact R52051
  · exact R52053
  · exact R52055
  · exact R52057
  · exact R52059
  · exact R52061
  · exact R52063
  · exact R52065
  · exact R52067
  · exact R52069
  · exact R52071
  · exact R52073
  · exact R52075
  · exact R52077
  · exact R52079
  · exact R52081
  · exact R52083
  · exact R52085
  · exact R52087
  · exact R52089
  · exact R52091
  · exact R52093
  · exact R52095
  · exact R52097
  · exact R52099
  · exact R52101
  · exact R52103
  · exact R52105
  · exact R52107
  · exact R52109
  · exact R52111
  · exact R52113
  · exact R52115
  · exact R52117
  · exact R52119
  · exact R52121
  · exact R52123
  · exact R52125
  · exact R52127
  · exact R52129
  · exact R52131
  · exact R52133
  · exact R52135
  · exact R52137
  · exact R52139
  · exact R52141
  · exact R52143
  · exact R52145
  · exact R52147
  · exact R52149
  · exact R52151
  · exact R52153
  · exact R52155
  · exact R52157
  · exact R52159
  · exact R52161
  · exact R52163
  · exact R52165
  · exact R52167
  · exact R52169
  · exact R52171
  · exact R52173
  · exact R52175
  · exact R52177
  · exact R52179
  · exact R52181
  · exact R52183
  · exact R52185
  · exact R52187
  · exact R52189
  · exact R52191
  · exact R52193
  · exact R52195
  · exact R52197
  · exact R52199
  · exact R52201
  · exact R52203
  · exact R52205
  · exact R52207
  · exact R52209
  · exact R52211
  · exact R52213
  · exact R52215
  · exact R52217
  · exact R52219
  · exact R52221
  · exact R52223
  · exact R52225
  · exact R52227
  · exact R52229
  · exact R52231
  · exact R52233
  · exact R52235
  · exact R52237
  · exact R52239
  · exact R52241
  · exact R52243
  · exact R52245
  · exact R52247
  · exact R52249
  · exact R52251
  · exact R52253
  · exact R52255
  · exact R52257
  · exact R52259
  · exact R52261
  · exact R52263
  · exact R52265
  · exact R52267
  · exact R52269
  · exact R52271
  · exact R52273
  · exact R52275
  · exact R52277
  · exact R52279
  · exact R52281
  · exact R52283
  · exact R52285
  · exact R52287
  · exact R52289
  · exact R52291
  · exact R52293
  · exact R52295
  · exact R52297
  · exact R52299
  · exact R52301
  · exact R52303
  · exact R52305
  · exact R52307
  · exact R52309
  · exact R52311
  · exact R52313
  · exact R52315
  · exact R52317
  · exact R52319
  · exact R52321
  · exact R52323
  · exact R52325
  · exact R52327
  · exact R52329
  · exact R52331
  · exact R52333
  · exact R52335
  · exact R52337
  · exact R52339
  · exact R52341
  · exact R52343
  · exact R52345
  · exact R52347
  · exact R52349
  · exact R52351
  · exact R52353
  · exact R52355
  · exact R52357
  · exact R52359
  · exact R52361
  · exact R52363
  · exact R52365
  · exact R52367
  · exact R52369
  · exact R52371
  · exact R52373
  · exact R52375
  · exact R52377
  · exact R52379
  · exact R52381
  · exact R52383
  · exact R52385
  · exact R52387
  · exact R52389
  · exact R52391
  · exact R52393
  · exact R52395
  · exact R52397
  · exact R52399
  · exact R52401
  · exact R52403
  · exact R52405
  · exact R52407
  · exact R52409
  · exact R52411
  · exact R52413
  · exact R52415
  · exact R52417
  · exact R52419
  · exact R52421
  · exact R52423
  · exact R52425
  · exact R52427
  · exact R52429
  · exact R52431
  · exact R52433
  · exact R52435
  · exact R52437
  · exact R52439
  · exact R52441
  · exact R52443
  · exact R52445
  · exact R52447
  · exact R52449
  · exact R52451
  · exact R52453
  · exact R52455
  · exact R52457
  · exact R52459
  · exact R52461
  · exact R52463
  · exact R52465
  · exact R52467
  · exact R52469
  · exact R52471
  · exact R52473
  · exact R52475
  · exact R52477
  · exact R52479
  · exact R52481
  · exact R52483
  · exact R52485
  · exact R52487
  · exact R52489
  · exact R52491
  · exact R52493
  · exact R52495
  · exact R52497
  · exact R52499
  · exact R52501
  · exact R52503
  · exact R52505
  · exact R52507
  · exact R52509
  · exact R52511
  · exact R52513
  · exact R52515
  · exact R52517
  · exact R52519

theorem C1 (j : ℕ) (h1 : 26260 ≤ j) (h2 : j ≤ 26959) : Reach (2 * j + 1) := by
  interval_cases j
  · exact R52521
  · exact R52523
  · exact R52525
  · exact R52527
  · exact R52529
  · exact R52531
  · exact R52533
  · exact R52535
  · exact R52537
  · exact R52539
  · exact R52541
  · exact R52543
  · exact R52545
  · exact R52547
  · exact R52549
  · exact R52551
  · exact R52553
  · exact R52555
  · exact R52557
  · exact R52559
  · exact R52561
  · exact R52563
  · exact R52565
  · exact R52567
  · exact R52569
  · exact R52571
  · exact R52573
  · exact R52575
  · exact R52577
  · exact R52579
  · exact R52581
  · exact R52583
  · exact R52585
  · exact R52587
  · exact R52589
  · exact R52591
  · exact R52593
  · exact R52595
  · exact R52597
  · exact R52599
  · exact R52601
  · exact R52603
  · exact R52605
  · exact R52607
  · exact R52609
  · exact R52611
  · exact R52613
  · exact R52615
  · exact R52617
  · exact R52619
  · exact R52621
  · exact R52623
  · exact R52625
  · exact R52627
  · exact R52629
  · exact R52631
  · exact R52633
  · exact R52635
  · exact R52637
  · exact R52639
  · exact R52641
  · exact R52643
  · exact R52645
  · exact R52647
  · exact R52649
  · exact R52651
  · exact R52653
  · exact R52655
  · exact R52657
  · exact R52659
  · exact R52661
  · exact R52663
  · exact R52665
  · exact R52667
  · exact R52669
  · exact R52671
  · exact R52673
  · exact R52675
  · exact R52677
  · exact R52679
  · exact R52681
  · exact R52683
  · exact R52685
  · exact R52687
  · exact R52689
  · exact R52691
  · exact R52693
  · exact R52695
  · exact R52697
  · exact R52699
  · exact R52701
  · exact R52703
  · exact R52705
  · exact R52707
  · exact R52709
  · exact R52711
  · exact R52713
  · exact R52715
  · exact R52717
  · exact R52719
  · exact R52721
  · exact R52723
  · exact R52725
  · exact R52727
  · exact R52729
  · exact R52731
  · exact R52733
  · exact R52735
  · exact R52737
  · exact R52739
  · exact R52741
  · exact R52743
  · exact R52745
  · exact R52747
  · exact R52749
  · exact R52751
  · exact R52753
  · exact R52755
  · exact R52757
  · exact R52759
  · exact R52761
  · exact R52763
  · exact R52765
  · exact R52767
  · exact R52769
  · exact R52771
  · exact R52773
  · exact R52775
  · exact R52777
  · exact R52779
  · exact R52781
  · exact R52783
  · exact R52785
  · exact R52787
  · exact R52789
  · exact R52791
  · exact R52793
  · exact R52795
  · exact R52797
  · exact R52799
  · exact R52801
  · exact R52803
  · exact R52805
  · exact R52807
  · exact R52809
  · exact R52811
  · exact R52813
  · exact R52815
  · exact R52817
  · exact R52819
  · exact R52821
  · exact R52823
  · exact R52825
  · exact R52827
  · exact R52829
  · exact R52831
  · exact R52833
  · exact R52835
  · exact R52837
  · exact R52839
  · exact R52841
  · exact R52843
  · exact R52845
  · exact R52847
  · exact R52849
  · exact R52851
  · exact R52853
  · exact R52855
  · exact R52857
  · exact R52859
  · exact R52861
  · exact R52863
  · exact R52865
  · exact R52867
  · exact R52869
  · exact R52871
  · exact R52873
  · exact R52875
  · exact R52877
  · exact R52879
  · exact R52881
  · exact R52883
  · exact R52885
  · exact R52887
  · exact R52889
  · exact R52891
  · exact R52893
  · exact R52895
  · exact R52897
  · exact R52899
  · exact R52901
  · exact R52903
  · exact R52905
  · exact R52907
  · exact R52909
  · exact R52911
  · exact R52913
  · exact R52915
  · exact R52917
  · exact R52919
  · exact R52921
  · exact R52923
  · exact R52925
  · exact R52927
  · exact R52929
  · exact R52931
  · exact R52933
  · exact R52935
  · exact R52937
  · exact R52939
  · exact R52941
  · exact R52943
  · exact R52945
  · exact R52947
  · exact R52949
  · exact R52951
  · exact R52953
  · exact R52955
  · exact R52957
  · exact R52959
  · exact R52961
  · exact R52963
  · exact R52965
  · exact R52967
  · exact R52969
  · exact R52971
  · exact R52973
  · exact R52975
  · exact R52977
  · exact R52979
  · exact R52981
  · exact R52983
  · exact R52985
  · exact R52987
  · exact R52989
  · exact R52991
  · exact R52993
  · exact R52995
  · exact R52997
  · exact R52999
  · exact R53001
  · exact R53003
  · exact R53005
  · exact R53007
  · exact R53009
  · exact R53011
  · exact R53013
  · exact R53015
  · exact R53017
  · exact R53019
  · exact R53021
  · exact R53023
  · exact R53025
  · exact R53027
  · exact R53029
  · exact R53031
  · exact R53033
  · exact R53035
  · exact R53037
  · exact R53039
  · exact R53041
  · exact R53043
  · exact R53045
  · exact R53047
  · exact R53049
  · exact R53051
  · exact R53053
  · exact R53055
  · exact R53057
  · exact R53059
  · exact R53061
  · exact R53063
  · exact R53065
  · exact R53067
  · exact R53069
  · exact R53071
  · exact R53073
  · exact R53075
  · exact R53077
  · exact R53079
  · exact R53081
  · exact R53083
  · exact R53085
  · exact R53087
  · exact R53089
  · exact R53091
  · exact R53093
  · exact R53095
  · exact R53097
  · exact R53099
  · exact R53101
  · exact R53103
  · exact R53105
  · exact R53107
  · exact R53109
  · exact R53111
  · exact R53113
  · exact R53115
  · exact R53117
  · exact R53119
  · exact R53121
  · exact R53123
  · exact R53125
  · exact R53127
  · exact R53129
  · exact R53131
  · exact R53133
  · exact R53135
  · exact R53137
  · exact R53139
  · exact R53141
  · exact R53143
  · exact R53145
  · exact R53147
  · exact R53149
  · exact R53151
  · exact R53153
  · exact R53155
  · exact R53157
  · exact R53159
  · exact R53161
  · exact R53163
  · exact R53165
  · exact R53167
  · exact R53169
  · exact R53171
  · exact R53173
  · exact R53175
  · exact R53177
  · exact R53179
  · exact R53181
  · exact R53183
  · exact R53185
  · exact R53187
  · exact R53189
  · exact R53191
  · exact R53193
  · exact R53195
  · exact R53197
  · exact R53199
  · exact R53201
  · exact R53203
  · exact R53205
  · exact R53207
  · exact R53209
  · exact R53211
  · exact R53213
  · exact R53215
  · exact R53217
  · exact R53219
  · exact R53221
  · exact R53223
  · exact R53225
  · exact R53227
  · exact R53229
  · exact R53231
  · exact R53233
  · exact R53235
  · exact R53237
  · exact R53239
  · exact R53241
  · exact R53243
  · exact R53245
  · exact R53247
  · exact R53249
  · exact R53251
  · exact R53253
  · exact R53255
  · exact R53257
  · exact R53259
  · exact R53261
  · exact R53263
  · exact R53265
  · exact R53267
  · exact R53269
  · exact R53271
  · exact R53273
  · exact R53275
  · exact R53277
  · exact R53279
  · exact R53281
  · exact R53283
  · exact R53285
  · exact R53287
  · exact R53289
  · exact R53291
  · exact R53293
  · exact R53295
  · exact R53297
  · exact R53299
  · exact R53301
  · exact R53303
  · exact R53305
  · exact R53307
  · exact R53309
  · exact R53311
  · exact R53313
  · exact R53315
  · exact R53317
  · exact R53319
  · exact R53321
  · exact R53323
  · exact R53325
  · exact R53327
  · exact R53329
  · exact R53331
  · exact R53333
  · exact R53335
  · exact R53337
  · exact R53339
  · exact R53341
  · exact R53343
  · exact R53345
  · exact R53347
  · exact R53349
  · exact R53351
  · exact R53353
  · exact R53355
  · exact R53357
  · exact R53359
  · exact R53361
  · exact R53363
  · exact R53365
  · exact R53367
  · exact R53369
  · exact R53371
  · exact R53373
  · exact R53375
  · exact R53377
  · exact R53379
  · exact R53381
  · exact R53383
  · exact R53385
  · exact R53387
  · exact R53389
  · exact R53391
  · exact R53393
  · exact R53395
  · exact R53397
  · exact R53399
  · exact R53401
  · exact R53403
  · exact R53405
  · exact R53407
  · exact R53409
  · exact R53411
  · exact R53413
  · exact R53415
  · exact R53417
  · exact R53419
  · exact R53421
  · exact R53423
  · exact R53425
  · exact R53427
  · exact R53429
  · exact R53431
  · exact R53433
  · exact R53435
  · exact R53437
  · exact R53439
  · exact R53441
  · exact R53443
  · exact R53445
  · exact R53447
  · exact R53449
  · exact R53451
  · exact R53453
  · exact R53455
  · exact R53457
  · exact R53459
  · exact R53461
  · exact R53463
  · exact R53465
  · exact R53467
  · exact R53469
  · exact R53471
  · exact R53473
  · exact R53475
  · exact R53477
  · exact R53479
  · exact R53481
  · exact R53483
  · exact R53485
  · exact R53487
  · exact R53489
  · exact R53491
  · exact R53493
  · exact R53495
  · exact R53497
  · exact R53499
  · exact R53501
  · exact R53503
  · exact R53505
  · exact R53507
  · exact R53509
  · exact R53511
  · exact R53513
  · exact R53515
  · exact R53517
  · exact R53519
  · exact R53521
  · exact R53523
  · exact R53525
  · exact R53527
  · exact R53529
  · exact R53531
  · exact R53533
  · exact R53535
  · exact R53537
  · exact R53539
  · exact R53541
  · exact R53543
  · exact R53545
  · exact R53547
  · exact R53549
  · exact R53551
  · exact R53553
  · exact R53555
  · exact R53557
  · exact R53559
  · exact R53561
  · exact R53563
  · exact R53565
  · exact R53567
  · exact R53569
  · exact R53571
  · exact R53573
  · exact R53575
  · exact R53577
  · exact R53579
  · exact R53581
  · exact R53583
  · exact R53585
  · exact R53587
  · exact R53589
  · exact R53591
  · exact R53593
  · exact R53595
  · exact R53597
  · exact R53599
  · exact R53601
  · exact R53603
  · exact R53605
  · exact R53607
  · exact R53609
  · exact R53611
  · exact R53613
  · exact R53615
  · exact R53617
  · exact R53619
  · exact R53621
  · exact R53623
  · exact R53625
  · exact R53627
  · exact R53629
  · exact R53631
  · exact R53633
  · exact R53635
  · exact R53637
  · exact R53639
  · exact R53641
  · exact R53643
  · exact R53645
  · exact R53647
  · exact R53649
  · exact R53651
  · exact R53653
  · exact R53655
  · exact R53657
  · exact R53659
  · exact R53661
  · exact R53663
  · exact R53665
  · exact R53667
  · exact R53669
  · exact R53671
  · exact R53673
  · exact R53675
  · exact R53677
  · exact R53679
  · exact R53681
  · exact R53683
  · exact R53685
  · exact R53687
  · exact R53689
  · exact R53691
  · exact R53693
  · exact R53695
  · exact R53697
  · exact R53699
  · exact R53701
  · exact R53703
  · exact R53705
  · exact R53707
  · exact R53709
  · exact R53711
  · exact R53713
  · exact R53715
  · exact R53717
  · exact R53719
  · exact R53721
  · exact R53723
  · exact R53725
  · exact R53727
  · exact R53729
  · exact R53731
  · exact R53733
  · exact R53735
  · exact R53737
  · exact R53739
  · exact R53741
  · exact R53743
  · exact R53745
  · exact R53747
  · exact R53749
  · exact R53751
  · exact R53753
  · exact R53755
  · exact R53757
  · exact R53759
  · exact R53761
  · exact R53763
  · exact R53765
  · exact R53767
  · exact R53769
  · exact R53771
  · exact R53773
  · exact R53775
  · exact R53777
  · exact R53779
  · exact R53781
  · exact R53783
  · exact R53785
  · exact R53787
  · exact R53789
  · exact R53791
  · exact R53793
  · exact R53795
  · exact R53797
  · exact R53799
  · exact R53801
  · exact R53803
  · exact R53805
  · exact R53807
  · exact R53809
  · exact R53811
  · exact R53813
  · exact R53815
  · exact R53817
  · exact R53819
  · exact R53821
  · exact R53823
  · exact R53825
  · exact R53827
  · exact R53829
  · exact R53831
  · exact R53833
  · exact R53835
  · exact R53837
  · exact R53839
  · exact R53841
  · exact R53843
  · exact R53845
  · exact R53847
  · exact R53849
  · exact R53851
  · exact R53853
  · exact R53855
  · exact R53857
  · exact R53859
  · exact R53861
  · exact R53863
  · exact R53865
  · exact R53867
  · exact R53869
  · exact R53871
  · exact R53873
  · exact R53875
  · exact R53877
  · exact R53879
  · exact R53881
  · exact R53883
  · exact R53885
  · exact R53887
  · exact R53889
  · exact R53891
  · exact R53893
  · exact R53895
  · exact R53897
  · exact R53899
  · exact R53901
  · exact R53903
  · exact R53905
  · exact R53907
  · exact R53909
  · exact R53911
  · exact R53913
  · exact R53915
  · exact R53917
  · exact R53919

theorem C2 (j : ℕ) (h1 : 26960 ≤ j) (h2 : j ≤ 27559) : Reach (2 * j + 1) := by
  interval_cases j
  · exact R53921
  · exact R53923
  · exact R53925
  · exact R53927
  · exact R53929
  · exact R53931
  · exact R53933
  · exact R53935
  · exact R53937
  · exact R53939
  · exact R53941
  · exact R53943
  · exact R53945
  · exact R53947
  · exact R53949
  · exact R53951
  · exact R53953
  · exact R53955
  · exact R53957
  · exact R53959
  · exact R53961
  · exact R53963
  · exact R53965
  · exact R53967
  · exact R53969
  · exact R53971
  · exact R53973
  · exact R53975
  · exact R53977
  · exact R53979
  · exact R53981
  · exact R53983
  · exact R53985
  · exact R53987
  · exact R53989
  · exact R53991
  · exact R53993
  · exact R53995
  · exact R53997
  · exact R53999
  · exact R54001
  · exact R54003
  · exact R54005
  · exact R54007
  · exact R54009
  · exact R54011
  · exact R54013
  · exact R54015
  · exact R54017
  · exact R54019
  · exact R54021
  · exact R54023
  · exact R54025
  · exact R54027
  · exact R54029
  · exact R54031
  · exact R54033
  · exact R54035
  · exact R54037
  · exact R54039
  · exact R54041
  · exact R54043
  · exact R54045
  · exact R54047
  · exact R54049
  · exact R54051
  · exact R54053
  · exact R54055
  · exact R54057
  · exact R54059
  · exact R54061
  · exact R54063
  · exact R54065
  · exact R54067
  · exact R54069
  · exact R54071
  · exact R54073
  · exact R54075
  · exact R54077
  · exact R54079
  · exact R54081
  · exact R54083
  · exact R54085
  · exact R54087
  · exact R54089
  · exact R54091
  · exact R54093
  · exact R54095
  · exact R54097
  · exact R54099
  · exact R54101
  · exact R54103
  · exact R54105
  · exact R54107
  · exact R54109
  · exact R54111
  · exact R54113
  · exact R54115
  · exact R54117
  · exact R54119
  · exact R54121
  · exact R54123
  · exact R54125
  · exact R54127
  · exact R54129
  · exact R54131
  · exact R54133
  · exact R54135
  · exact R54137
  · exact R54139
  · exact R54141
  · exact R54143
  · exact R54145
  · exact R54147
  · exact R54149
  · exact R54151
  · exact R54153
  · exact R54155
  · exact R54157
  · exact R54159
  · exact R54161
  · exact R54163
  · exact R54165
  · exact R54167
  · exact R54169
  · exact R54171
  · exact R54173
  · exact R54175
  · exact R54177
  · exact R54179
  · exact R54181
  · exact R54183
  · exact R54185
  · exact R54187
  · exact R54189
  · exact R54191
  · exact R54193
  · exact R54195
  · exact R54197
  · exact R54199
  · exact R54201
  · exact R54203
  · exact R54205
  · exact R54207
  · exact R54209
  · exact R54211
  · exact R54213
  · exact R54215
  · exact R54217
  · exact R54219
  · exact R54221
  · exact R54223
  · exact R54225
  · exact R54227
  · exact R54229
  · exact R54231
  · exact R54233
  · exact R54235
  · exact R54237
  · exact R54239
  · exact R54241
  · exact R54243
  · exact R54245
  · exact R54247
  · exact R54249
  · exact R54251
  · exact R54253
  · exact R54255
  · exact R54257
  · exact R54259
  · exact R54261
  · exact R54263
  · exact R54265
  · exact R54267
  · exact R54269
  · exact R54271
  · exact R54273
  · exact R54275
  · exact R54277
  · exact R54279
  · exact R54281
  · exact R54283
  · exact R54285
  · exact R54287
  · exact R54289
  · exact R54291
  · exact R54293
  · exact R54295
  · exact R54297
  · exact R54299
  · exact R54301
  · exact R54303
  · exact R54305
  · exact R54307
  · exact R54309
  · exact R54311
  · exact R54313
  · exact R54315
  · exact R54317
  · exact R54319
  · exact R54321
  · exact R54323
  · exact R54325
  · exact R54327
  · exact R54329
  · exact R54331
  · exact R54333
  · exact R54335
  · exact R54337
  · exact R54339
  · exact R54341
  · exact R54343
  · exact R54345
  · exact R54347
  · exact R54349
  · exact R54351
  · exact R54353
  · exact R54355
  · exact R54357
  · exact R54359
  · exact R54361
  · exact R54363
  · exact R54365
  · exact R54367
  · exact R54369
  · exact R54371
  · exact R54373
  · exact R54375
  · exact R54377
  · exact R54379
  · exact R54381
  · exact R54383
  · exact R54385
  · exact R54387
  · exact R54389
  · exact R54391
  · exact R54393
  · exact R54395
  · exact R54397
  · exact R54399
  · exact R54401
  · exact R54403
  · exact R54405
  · exact R54407
  · exact R54409
  · exact R54411
  · exact R54413
  · exact R54415
  · exact R54417
  · exact R54419
  · exact R54421
  · exact R54423
  · exact R54425
  · exact R54427
  · exact R54429
  · exact R54431
  · exact R54433
  · exact R54435
  · exact R54437
  · exact R54439
  · exact R54441
  · exact R54443
  · exact R54445
  · exact R54447
  · exact R54449
  · exact R54451
  · exact R54453
  · exact R54455
  · exact R54457
  · exact R54459
  · exact R54461
  · exact R54463
  · exact R54465
  · exact R54467
  · exact R54469
  · exact R54471
  · exact R54473
  · exact R54475
  · exact R54477
  · exact R54479
  · exact R54481
  · exact R54483
  · exact R54485
  · exact R54487
  · exact R54489
  · exact R54491
  · exact R54493
  · exact R54495
  · exact R54497
  · exact R54499
  · exact R54501
  · exact R54503
  · exact R54505
  · exact R54507
  · exact R54509
  · exact R54511
  · exact R54513
  · exact R54515
  · exact R54517
  · exact R54519
  · exact R54521
  · exact R54523
  · exact R54525
  · exact R54527
  · exact R54529
  · exact R54531
  · exact R54533
  · exact R54535
  · exact R54537
  · exact R54539
  · exact R54541
  · exact R54543
  · exact R54545
  · exact R54547
  · exact R54549
  · exact R54551
  · exact R54553
  · exact R54555
  · exact R54557
  · exact R54559
  · exact R54561
  · exact R54563
  · exact R54565
  · exact R54567
  · exact R54569
  · exact R54571
  · exact R54573
  · exact R54575
  · exact R54577
  · exact R54579
  · exact R54581
  · exact R54583
  · exact R54585
  · exact R54587
  · exact R54589
  · exact R54591
  · exact R54593
  · exact R54595
  · exact R54597
  · exact R54599
  · exact R54601
  · exact R54603
  · exact R54605
  · exact R54607
  · exact R54609
  · exact R54611
  · exact R54613
  · exact R54615
  · exact R54617
  · exact R54619
  · exact R54621
  · exact R54623
  · exact R54625
  · exact R54627
  · exact R54629
  · exact R54631
  · exact R54633
  · exact R54635
  · exact R54637
  · exact R54639
  · exact R54641
  · exact R54643
  · exact R54645
  · exact R54647
  · exact R54649
  · exact R54651
  · exact R54653
  · exact R54655
  · exact R54657
  · exact R54659
  · exact R54661
  · exact R54663
  · exact R54665
  · exact R54667
  · exact R54669
  · exact R54671
  · exact R54673
  · exact R54675
  · exact R54677
  · exact R54679
  · exact R54681
  · exact R54683
  · exact R54685
  · exact R54687
  · exact R54689
  · exact R54691
  · exact R54693
  · exact R54695
  · exact R54697
  · exact R54699
  · exact R54701
  · exact R54703
  · exact R54705
  · exact R54707
  · exact R54709
  · exact R54711
  · exact R54713
  · exact R54715
  · exact R54717
  · exact R54719
  · exact R54721
  · exact R54723
  · exact R54725
  · exact R54727
  · exact R54729
  · exact R54731
  · exact R54733
  · exact R54735
  · exact R54737
  · exact R54739
  · exact R54741
  · exact R54743
  · exact R54745
  · exact R54747
  · exact R54749
  · exact R54751
  · exact R54753
  · exact R54755
  · exact R54757
  · exact R54759
  · exact R54761
  · exact R54763
  · exact R54765
  · exact R54767
  · exact R54769
  · exact R54771
  · exact R54773
  · exact R54775
  · exact R54777
  · exact R54779
  · exact R54781
  · exact R54783
  · exact R54785
  · exact R54787
  · exact R54789
  · exact R54791
  · exact R54793
  · exact R54795
  · exact R54797
  · exact R54799
  · exact R54801
  · exact R54803
  · exact R54805
  · exact R54807
  · exact R54809
  · exact R54811
  · exact R54813
  · exact R54815
  · exact R54817
  · exact R54819
  · exact R54821
  · exact R54823
  · exact R54825
  · exact R54827
  · exact R54829
  · exact R54831
  · exact R54833
  · exact R54835
  · exact R54837
  · exact R54839
  · exact R54841
  · exact R54843
  · exact R54845
  · exact R54847
  · exact R54849
  · exact R54851
  · exact R54853
  · exact R54855
  · exact R54857
  · exact R54859
  · exact R54861
  · exact R54863
  · exact R54865
  · exact R54867
  · exact R54869
  · exact R54871
  · exact R54873
  · exact R54875
  · exact R54877
  · exact R54879
  · exact R54881
  · exact R54883
  · exact R54885
  · exact R54887
  · exact R54889
  · exact R54891
  · exact R54893
  · exact R54895
  · exact R54897
  · exact R54899
  · exact R54901
  · exact R54903
  · exact R54905
  · exact R54907
  · exact R54909
  · exact R54911
  · exact R54913
  · exact R54915
  · exact R54917
  · exact R54919
  · exact R54921
  · exact R54923
  · exact R54925
  · exact R54927
  · exact R54929
  · exact R54931
  · exact R54933
  · exact R54935
  · exact R54937
  · exact R54939
  · exact R54941
  · exact R54943
  · exact R54945
  · exact R54947
  · exact R54949
  · exact R54951
  · exact R54953
  · exact R54955
  · exact R54957
  · exact R54959
  · exact R54961
  · exact R54963
  · exact R54965
  · exact R54967
  · exact R54969
  · exact R54971
  · exact R54973
  · exact R54975
  · exact R54977
  · exact R54979
  · exact R54981
  · exact R54983
  · exact R54985
  · exact R54987
  · exact R54989
  · exact R54991
  · exact R54993
  · exact R54995
  · exact R54997
  · exact R54999
  · exact R55001
  · exact R55003
  · exact R55005
  · exact R55007
  · exact R55009
  · exact R55011
  · exact R55013
  · exact R55015
  · exact R55017
  · exact R55019
  · exact R55021
  · exact R55023
  · exact R55025
  · exact R55027
  · exact R55029
  · exact R55031
  · exact R55033
  · exact R55035
  · exact R55037
  · exact R55039
  · exact R55041
  · exact R55043
  · exact R55045
  · exact R55047
  · exact R55049
  · exact R55051
  · exact R55053
  · exact R55055
  · exact R55057
  · exact R55059
  · exact R55061
  · exact R55063
  · exact R55065
  · exact R55067
  · exact R55069
  · exact R55071
  · exact R55073
  · exact R55075
  · exact R55077
  · exact R55079
  · exact R55081
  · exact R55083
  · exact R55085
  · exact R55087
  · exact R55089
  · exact R55091
  · exact R55093
  · exact R55095
  · exact R55097
  · exact R55099
  · exact R55101
  · exact R55103
  · exact R55105
  · exact R55107
  · exact R55109
  · exact R55111
  · exact R55113
  · exact R55115
  · exact R55117
  · exact R55119

theorem solution (m : ℕ) (hm : 0 < m) (hodd : Odd m) (hle : m ≤ 55120) :
    ∃ k : ℕ, syracuseStep^[k] m = 1 := by
  rcases Nat.lt_or_ge m 51120 with hlo | hlo
  · exact syracuse_reaches_one_below_51120 m hm hodd (by omega)
  obtain ⟨j, rfl⟩ : ∃ j, m = 2 * j + 1 := by obtain ⟨t, ht⟩ := hodd; exact ⟨t, by omega⟩
  rcases Nat.lt_or_ge j 26260 with h0 | h0
  · exact C0 j (by omega) (by omega)
  rcases Nat.lt_or_ge j 26960 with h1 | h1
  · exact C1 j (by omega) (by omega)
  exact C2 j (by omega) (by omega)
