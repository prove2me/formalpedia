-- Prove2me | solution 1 for syracuse_reaches_one_below_79127
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T06:28:07.530264+00:00
-- url     : https://prove2.me/submissions/4b88986c-2529-4e84-9db3-cb67cd56636d

import Mathlib
import Definitions.Def_syracuseStep
import Theorems.Thm_syracuse_reaches_one_below_75126

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
theorem B (n : ℕ) (h1 : 0 < n) (h2 : Odd n) (h3 : n ≤ 75125) : Reach n :=
  syracuse_reaches_one_below_75126 n h1 h2 h3
theorem R327685 : Reach 327685 := rs (se 4 (by rfl) ⟨30720, by rfl⟩) (B 61441 (by norm_num) ⟨30720, by rfl⟩ (by norm_num))
theorem R98329 : Reach 98329 := rs (se 2 (by rfl) ⟨36873, by rfl⟩) (B 73747 (by norm_num) ⟨36873, by rfl⟩ (by norm_num))
theorem R131125 : Reach 131125 := rs (se 5 (by rfl) ⟨6146, by rfl⟩) (B 12293 (by norm_num) ⟨6146, by rfl⟩ (by norm_num))
theorem R163957 : Reach 163957 := rs (se 5 (by rfl) ⟨7685, by rfl⟩) (B 15371 (by norm_num) ⟨7685, by rfl⟩ (by norm_num))
theorem R98425 : Reach 98425 := rs (se 2 (by rfl) ⟨36909, by rfl⟩) (B 73819 (by norm_num) ⟨36909, by rfl⟩ (by norm_num))
theorem R262277 : Reach 262277 := rs (se 4 (by rfl) ⟨24588, by rfl⟩) (B 49177 (by norm_num) ⟨24588, by rfl⟩ (by norm_num))
theorem R131213 : Reach 131213 := rs (se 3 (by rfl) ⟨24602, by rfl⟩) (B 49205 (by norm_num) ⟨24602, by rfl⟩ (by norm_num))
theorem R196789 : Reach 196789 := rs (se 5 (by rfl) ⟨9224, by rfl⟩) (B 18449 (by norm_num) ⟨9224, by rfl⟩ (by norm_num))
theorem R295109 : Reach 295109 := rs (se 4 (by rfl) ⟨27666, by rfl⟩) (B 55333 (by norm_num) ⟨27666, by rfl⟩ (by norm_num))
theorem R131341 : Reach 131341 := rs (se 3 (by rfl) ⟨24626, by rfl⟩) (B 49253 (by norm_num) ⟨24626, by rfl⟩ (by norm_num))
theorem R196901 : Reach 196901 := rs (se 4 (by rfl) ⟨18459, by rfl⟩) (B 36919 (by norm_num) ⟨18459, by rfl⟩ (by norm_num))
theorem R98597 : Reach 98597 := rs (se 4 (by rfl) ⟨9243, by rfl⟩) (B 18487 (by norm_num) ⟨9243, by rfl⟩ (by norm_num))
theorem R98653 : Reach 98653 := rs (se 3 (by rfl) ⟨18497, by rfl⟩) (B 36995 (by norm_num) ⟨18497, by rfl⟩ (by norm_num))
theorem R131429 : Reach 131429 := rs (se 4 (by rfl) ⟨12321, by rfl⟩) (B 24643 (by norm_num) ⟨12321, by rfl⟩ (by norm_num))
theorem R98749 : Reach 98749 := rs (se 3 (by rfl) ⟨18515, by rfl⟩) (B 37031 (by norm_num) ⟨18515, by rfl⟩ (by norm_num))
theorem R295397 : Reach 295397 := rs (se 4 (by rfl) ⟨27693, by rfl⟩) (B 55387 (by norm_num) ⟨27693, by rfl⟩ (by norm_num))
theorem R197093 : Reach 197093 := rs (se 4 (by rfl) ⟨18477, by rfl⟩) (B 36955 (by norm_num) ⟨18477, by rfl⟩ (by norm_num))
theorem R131557 : Reach 131557 := rs (se 4 (by rfl) ⟨12333, by rfl⟩) (B 24667 (by norm_num) ⟨12333, by rfl⟩ (by norm_num))
theorem R393781 : Reach 393781 := rs (se 5 (by rfl) ⟨18458, by rfl⟩) (B 36917 (by norm_num) ⟨18458, by rfl⟩ (by norm_num))
theorem R262709 : Reach 262709 := rs (se 5 (by rfl) ⟨12314, by rfl⟩) (B 24629 (by norm_num) ⟨12314, by rfl⟩ (by norm_num))
theorem R131645 : Reach 131645 := rs (se 3 (by rfl) ⟨24683, by rfl⟩) (B 49367 (by norm_num) ⟨24683, by rfl⟩ (by norm_num))
theorem R361061 : Reach 361061 := rs (se 4 (by rfl) ⟨33849, by rfl⟩) (B 67699 (by norm_num) ⟨33849, by rfl⟩ (by norm_num))
theorem R98921 : Reach 98921 := rs (se 2 (by rfl) ⟨37095, by rfl⟩) (B 74191 (by norm_num) ⟨37095, by rfl⟩ (by norm_num))
theorem R98977 : Reach 98977 := rs (se 2 (by rfl) ⟨37116, by rfl⟩) (B 74233 (by norm_num) ⟨37116, by rfl⟩ (by norm_num))
theorem R131773 : Reach 131773 := rs (se 3 (by rfl) ⟨24707, by rfl⟩) (B 49415 (by norm_num) ⟨24707, by rfl⟩ (by norm_num))
theorem R99073 : Reach 99073 := rs (se 2 (by rfl) ⟨37152, by rfl⟩) (B 74305 (by norm_num) ⟨37152, by rfl⟩ (by norm_num))
theorem R131861 : Reach 131861 := rs (se 6 (by rfl) ⟨3090, by rfl⟩) (B 6181 (by norm_num) ⟨3090, by rfl⟩ (by norm_num))
theorem R197437 : Reach 197437 := rs (se 3 (by rfl) ⟨37019, by rfl⟩) (B 74039 (by norm_num) ⟨37019, by rfl⟩ (by norm_num))
theorem R426869 : Reach 426869 := rs (se 5 (by rfl) ⟨20009, by rfl⟩) (B 40019 (by norm_num) ⟨20009, by rfl⟩ (by norm_num))
theorem R131989 : Reach 131989 := rs (se 6 (by rfl) ⟨3093, by rfl⟩) (B 6187 (by norm_num) ⟨3093, by rfl⟩ (by norm_num))
theorem R197549 : Reach 197549 := rs (se 3 (by rfl) ⟨37040, by rfl⟩) (B 74081 (by norm_num) ⟨37040, by rfl⟩ (by norm_num))
theorem R99245 : Reach 99245 := rs (se 3 (by rfl) ⟨18608, by rfl⟩) (B 37217 (by norm_num) ⟨18608, by rfl⟩ (by norm_num))
theorem R263093 : Reach 263093 := rs (se 5 (by rfl) ⟨12332, by rfl⟩) (B 24665 (by norm_num) ⟨12332, by rfl⟩ (by norm_num))
theorem R263141 : Reach 263141 := rs (se 4 (by rfl) ⟨24669, by rfl⟩) (B 49339 (by norm_num) ⟨24669, by rfl⟩ (by norm_num))
theorem R99301 : Reach 99301 := rs (se 4 (by rfl) ⟨9309, by rfl⟩) (B 18619 (by norm_num) ⟨9309, by rfl⟩ (by norm_num))
theorem R164845 : Reach 164845 := rs (se 3 (by rfl) ⟨30908, by rfl⟩) (B 61817 (by norm_num) ⟨30908, by rfl⟩ (by norm_num))
theorem R132077 : Reach 132077 := rs (se 3 (by rfl) ⟨24764, by rfl⟩) (B 49529 (by norm_num) ⟨24764, by rfl⟩ (by norm_num))
theorem R99389 : Reach 99389 := rs (se 3 (by rfl) ⟨18635, by rfl⟩) (B 37271 (by norm_num) ⟨18635, by rfl⟩ (by norm_num))
theorem R99397 : Reach 99397 := rs (se 4 (by rfl) ⟨9318, by rfl⟩) (B 18637 (by norm_num) ⟨9318, by rfl⟩ (by norm_num))
theorem R197741 : Reach 197741 := rs (se 3 (by rfl) ⟨37076, by rfl⟩) (B 74153 (by norm_num) ⟨37076, by rfl⟩ (by norm_num))
theorem R132205 : Reach 132205 := rs (se 3 (by rfl) ⟨24788, by rfl⟩) (B 49577 (by norm_num) ⟨24788, by rfl⟩ (by norm_num))
theorem R132293 : Reach 132293 := rs (se 4 (by rfl) ⟨12402, by rfl⟩) (B 24805 (by norm_num) ⟨12402, by rfl⟩ (by norm_num))
theorem R459989 : Reach 459989 := rs (se 7 (by rfl) ⟨5390, by rfl⟩) (B 10781 (by norm_num) ⟨5390, by rfl⟩ (by norm_num))
theorem R394469 : Reach 394469 := rs (se 4 (by rfl) ⟨36981, by rfl⟩) (B 73963 (by norm_num) ⟨36981, by rfl⟩ (by norm_num))
theorem R99569 : Reach 99569 := rs (se 2 (by rfl) ⟨37338, by rfl⟩) (B 74677 (by norm_num) ⟨37338, by rfl⟩ (by norm_num))
theorem R99625 : Reach 99625 := rs (se 2 (by rfl) ⟨37359, by rfl⟩) (B 74719 (by norm_num) ⟨37359, by rfl⟩ (by norm_num))
theorem R132421 : Reach 132421 := rs (se 4 (by rfl) ⟨12414, by rfl⟩) (B 24829 (by norm_num) ⟨12414, by rfl⟩ (by norm_num))
theorem R99721 : Reach 99721 := rs (se 2 (by rfl) ⟨37395, by rfl⟩) (B 74791 (by norm_num) ⟨37395, by rfl⟩ (by norm_num))
theorem R263573 : Reach 263573 := rs (se 6 (by rfl) ⟨6177, by rfl⟩) (B 12355 (by norm_num) ⟨6177, by rfl⟩ (by norm_num))
theorem R132509 : Reach 132509 := rs (se 3 (by rfl) ⟨24845, by rfl⟩) (B 49691 (by norm_num) ⟨24845, by rfl⟩ (by norm_num))
theorem R198085 : Reach 198085 := rs (se 4 (by rfl) ⟨18570, by rfl⟩) (B 37141 (by norm_num) ⟨18570, by rfl⟩ (by norm_num))
theorem R165341 : Reach 165341 := rs (se 3 (by rfl) ⟨31001, by rfl⟩) (B 62003 (by norm_num) ⟨31001, by rfl⟩ (by norm_num))
theorem R230917 : Reach 230917 := rs (se 4 (by rfl) ⟨21648, by rfl⟩) (B 43297 (by norm_num) ⟨21648, by rfl⟩ (by norm_num))
theorem R132637 : Reach 132637 := rs (se 3 (by rfl) ⟨24869, by rfl⟩) (B 49739 (by norm_num) ⟨24869, by rfl⟩ (by norm_num))
theorem R198197 : Reach 198197 := rs (se 5 (by rfl) ⟨9290, by rfl⟩) (B 18581 (by norm_num) ⟨9290, by rfl⟩ (by norm_num))
theorem R99893 : Reach 99893 := rs (se 5 (by rfl) ⟨4682, by rfl⟩) (B 9365 (by norm_num) ⟨4682, by rfl⟩ (by norm_num))
theorem R99949 : Reach 99949 := rs (se 3 (by rfl) ⟨18740, by rfl⟩) (B 37481 (by norm_num) ⟨18740, by rfl⟩ (by norm_num))
theorem R132725 : Reach 132725 := rs (se 5 (by rfl) ⟨6221, by rfl⟩) (B 12443 (by norm_num) ⟨6221, by rfl⟩ (by norm_num))
theorem R296581 : Reach 296581 := rs (se 4 (by rfl) ⟨27804, by rfl⟩) (B 55609 (by norm_num) ⟨27804, by rfl⟩ (by norm_num))
theorem R100045 : Reach 100045 := rs (se 3 (by rfl) ⟨18758, by rfl⟩) (B 37517 (by norm_num) ⟨18758, by rfl⟩ (by norm_num))
theorem R198389 : Reach 198389 := rs (se 5 (by rfl) ⟨9299, by rfl⟩) (B 18599 (by norm_num) ⟨9299, by rfl⟩ (by norm_num))
theorem R132853 : Reach 132853 := rs (se 5 (by rfl) ⟨6227, by rfl⟩) (B 12455 (by norm_num) ⟨6227, by rfl⟩ (by norm_num))
theorem R264005 : Reach 264005 := rs (se 4 (by rfl) ⟨24750, by rfl⟩) (B 49501 (by norm_num) ⟨24750, by rfl⟩ (by norm_num))
theorem R132941 : Reach 132941 := rs (se 3 (by rfl) ⟨24926, by rfl⟩) (B 49853 (by norm_num) ⟨24926, by rfl⟩ (by norm_num))
theorem R296885 : Reach 296885 := rs (se 5 (by rfl) ⟨13916, by rfl⟩) (B 27833 (by norm_num) ⟨13916, by rfl⟩ (by norm_num))
theorem R133069 : Reach 133069 := rs (se 3 (by rfl) ⟨24950, by rfl⟩) (B 49901 (by norm_num) ⟨24950, by rfl⟩ (by norm_num))
theorem R755669 : Reach 755669 := rs (se 7 (by rfl) ⟨8855, by rfl⟩) (B 17711 (by norm_num) ⟨8855, by rfl⟩ (by norm_num))
theorem R133157 : Reach 133157 := rs (se 4 (by rfl) ⟨12483, by rfl⟩) (B 24967 (by norm_num) ⟨12483, by rfl⟩ (by norm_num))
theorem R198733 : Reach 198733 := rs (se 3 (by rfl) ⟨37262, by rfl⟩) (B 74525 (by norm_num) ⟨37262, by rfl⟩ (by norm_num))
theorem R133285 : Reach 133285 := rs (se 4 (by rfl) ⟨12495, by rfl⟩) (B 24991 (by norm_num) ⟨12495, by rfl⟩ (by norm_num))
theorem R362677 : Reach 362677 := rs (se 5 (by rfl) ⟨17000, by rfl⟩) (B 34001 (by norm_num) ⟨17000, by rfl⟩ (by norm_num))
theorem R198845 : Reach 198845 := rs (se 3 (by rfl) ⟨37283, by rfl⟩) (B 74567 (by norm_num) ⟨37283, by rfl⟩ (by norm_num))
theorem R264437 : Reach 264437 := rs (se 5 (by rfl) ⟨12395, by rfl⟩) (B 24791 (by norm_num) ⟨12395, by rfl⟩ (by norm_num))
theorem R133373 : Reach 133373 := rs (se 3 (by rfl) ⟨25007, by rfl⟩) (B 50015 (by norm_num) ⟨25007, by rfl⟩ (by norm_num))
theorem R166205 : Reach 166205 := rs (se 3 (by rfl) ⟨31163, by rfl⟩) (B 62327 (by norm_num) ⟨31163, by rfl⟩ (by norm_num))
theorem R330101 : Reach 330101 := rs (se 5 (by rfl) ⟨15473, by rfl⟩) (B 30947 (by norm_num) ⟨15473, by rfl⟩ (by norm_num))
theorem R199037 : Reach 199037 := rs (se 3 (by rfl) ⟨37319, by rfl⟩) (B 74639 (by norm_num) ⟨37319, by rfl⟩ (by norm_num))
theorem R133501 : Reach 133501 := rs (se 3 (by rfl) ⟨25031, by rfl⟩) (B 50063 (by norm_num) ⟨25031, by rfl⟩ (by norm_num))
theorem R166349 : Reach 166349 := rs (se 3 (by rfl) ⟨31190, by rfl⟩) (B 62381 (by norm_num) ⟨31190, by rfl⟩ (by norm_num))
theorem R395765 : Reach 395765 := rs (se 5 (by rfl) ⟨18551, by rfl⟩) (B 37103 (by norm_num) ⟨18551, by rfl⟩ (by norm_num))
theorem R264869 : Reach 264869 := rs (se 4 (by rfl) ⟨24831, by rfl⟩) (B 49663 (by norm_num) ⟨24831, by rfl⟩ (by norm_num))
theorem R199381 : Reach 199381 := rs (se 7 (by rfl) ⟨2336, by rfl⟩) (B 4673 (by norm_num) ⟨2336, by rfl⟩ (by norm_num))
theorem R199493 : Reach 199493 := rs (se 4 (by rfl) ⟨18702, by rfl⟩) (B 37405 (by norm_num) ⟨18702, by rfl⟩ (by norm_num))
theorem R199685 : Reach 199685 := rs (se 4 (by rfl) ⟨18720, by rfl⟩) (B 37441 (by norm_num) ⟨18720, by rfl⟩ (by norm_num))
theorem R265301 : Reach 265301 := rs (se 8 (by rfl) ⟨1554, by rfl⟩) (B 3109 (by norm_num) ⟨1554, by rfl⟩ (by norm_num))
theorem R494741 : Reach 494741 := rs (se 6 (by rfl) ⟨11595, by rfl⟩) (B 23191 (by norm_num) ⟨11595, by rfl⟩ (by norm_num))
theorem R167093 : Reach 167093 := rs (se 5 (by rfl) ⟨7832, by rfl⟩) (B 15665 (by norm_num) ⟨7832, by rfl⟩ (by norm_num))
theorem R232757 : Reach 232757 := rs (se 5 (by rfl) ⟨10910, by rfl⟩) (B 21821 (by norm_num) ⟨10910, by rfl⟩ (by norm_num))
theorem R200029 : Reach 200029 := rs (se 3 (by rfl) ⟨37505, by rfl⟩) (B 75011 (by norm_num) ⟨37505, by rfl⟩ (by norm_num))
theorem R200141 : Reach 200141 := rs (se 3 (by rfl) ⟨37526, by rfl⟩) (B 75053 (by norm_num) ⟨37526, by rfl⟩ (by norm_num))
theorem R265733 : Reach 265733 := rs (se 4 (by rfl) ⟨24912, by rfl⟩) (B 49825 (by norm_num) ⟨24912, by rfl⟩ (by norm_num))
theorem R397061 : Reach 397061 := rs (se 4 (by rfl) ⟨37224, by rfl⟩) (B 74449 (by norm_num) ⟨37224, by rfl⟩ (by norm_num))
theorem R167845 : Reach 167845 := rs (se 4 (by rfl) ⟨15735, by rfl⟩) (B 31471 (by norm_num) ⟨15735, by rfl⟩ (by norm_num))
theorem R266165 : Reach 266165 := rs (se 5 (by rfl) ⟨12476, by rfl⟩) (B 24953 (by norm_num) ⟨12476, by rfl⟩ (by norm_num))
theorem R298997 : Reach 298997 := rs (se 5 (by rfl) ⟨14015, by rfl⟩) (B 28031 (by norm_num) ⟨14015, by rfl⟩ (by norm_num))
theorem R167989 : Reach 167989 := rs (se 5 (by rfl) ⟨7874, by rfl⟩) (B 15749 (by norm_num) ⟨7874, by rfl⟩ (by norm_num))
theorem R331877 : Reach 331877 := rs (se 4 (by rfl) ⟨31113, by rfl⟩) (B 62227 (by norm_num) ⟨31113, by rfl⟩ (by norm_num))
theorem R102565 : Reach 102565 := rs (se 4 (by rfl) ⟨9615, by rfl⟩) (B 19231 (by norm_num) ⟨9615, by rfl⟩ (by norm_num))
theorem R299285 : Reach 299285 := rs (se 6 (by rfl) ⟨7014, by rfl⟩) (B 14029 (by norm_num) ⟨7014, by rfl⟩ (by norm_num))
theorem R758069 : Reach 758069 := rs (se 5 (by rfl) ⟨35534, by rfl⟩) (B 71069 (by norm_num) ⟨35534, by rfl⟩ (by norm_num))
theorem R1118549 : Reach 1118549 := rs (se 10 (by rfl) ⟨1638, by rfl⟩) (B 3277 (by norm_num) ⟨1638, by rfl⟩ (by norm_num))
theorem R168293 : Reach 168293 := rs (se 4 (by rfl) ⟨15777, by rfl⟩) (B 31555 (by norm_num) ⟨15777, by rfl⟩ (by norm_num))
theorem R266597 : Reach 266597 := rs (se 4 (by rfl) ⟨24993, by rfl⟩) (B 49987 (by norm_num) ⟨24993, by rfl⟩ (by norm_num))
theorem R233861 : Reach 233861 := rs (se 4 (by rfl) ⟨21924, by rfl⟩) (B 43849 (by norm_num) ⟨21924, by rfl⟩ (by norm_num))
theorem R168365 : Reach 168365 := rs (se 3 (by rfl) ⟨31568, by rfl⟩) (B 63137 (by norm_num) ⟨31568, by rfl⟩ (by norm_num))
theorem R168533 : Reach 168533 := rs (se 8 (by rfl) ⟨987, by rfl⟩) (B 1975 (by norm_num) ⟨987, by rfl⟩ (by norm_num))
theorem R267029 : Reach 267029 := rs (se 6 (by rfl) ⟨6258, by rfl⟩) (B 12517 (by norm_num) ⟨6258, by rfl⟩ (by norm_num))
theorem R168733 : Reach 168733 := rs (se 3 (by rfl) ⟨31637, by rfl⟩) (B 63275 (by norm_num) ⟨31637, by rfl⟩ (by norm_num))
theorem R758645 : Reach 758645 := rs (se 5 (by rfl) ⟨35561, by rfl⟩) (B 71123 (by norm_num) ⟨35561, by rfl⟩ (by norm_num))
theorem R398357 : Reach 398357 := rs (se 6 (by rfl) ⟨9336, by rfl⟩) (B 18673 (by norm_num) ⟨9336, by rfl⟩ (by norm_num))
theorem R332869 : Reach 332869 := rs (se 4 (by rfl) ⟨31206, by rfl⟩) (B 62413 (by norm_num) ⟨31206, by rfl⟩ (by norm_num))
theorem R169037 : Reach 169037 := rs (se 3 (by rfl) ⟨31694, by rfl⟩) (B 63389 (by norm_num) ⟨31694, by rfl⟩ (by norm_num))
theorem R169109 : Reach 169109 := rs (se 6 (by rfl) ⟨3963, by rfl⟩) (B 7927 (by norm_num) ⟨3963, by rfl⟩ (by norm_num))
theorem R169181 : Reach 169181 := rs (se 3 (by rfl) ⟨31721, by rfl⟩) (B 63443 (by norm_num) ⟨31721, by rfl⟩ (by norm_num))
theorem R169253 : Reach 169253 := rs (se 4 (by rfl) ⟨15867, by rfl⟩) (B 31735 (by norm_num) ⟨15867, by rfl⟩ (by norm_num))
theorem R169325 : Reach 169325 := rs (se 3 (by rfl) ⟨31748, by rfl⟩) (B 63497 (by norm_num) ⟨31748, by rfl⟩ (by norm_num))
theorem R431477 : Reach 431477 := rs (se 5 (by rfl) ⟨20225, by rfl⟩) (B 40451 (by norm_num) ⟨20225, by rfl⟩ (by norm_num))
theorem R595349 : Reach 595349 := rs (se 6 (by rfl) ⟨13953, by rfl⟩) (B 27907 (by norm_num) ⟨13953, by rfl⟩ (by norm_num))
theorem R169397 : Reach 169397 := rs (se 5 (by rfl) ⟨7940, by rfl⟩) (B 15881 (by norm_num) ⟨7940, by rfl⟩ (by norm_num))
theorem R169469 : Reach 169469 := rs (se 3 (by rfl) ⟨31775, by rfl⟩) (B 63551 (by norm_num) ⟨31775, by rfl⟩ (by norm_num))
theorem R169541 : Reach 169541 := rs (se 4 (by rfl) ⟨15894, by rfl⟩) (B 31789 (by norm_num) ⟨15894, by rfl⟩ (by norm_num))
theorem R169613 : Reach 169613 := rs (se 3 (by rfl) ⟨31802, by rfl⟩) (B 63605 (by norm_num) ⟨31802, by rfl⟩ (by norm_num))
theorem R169661 : Reach 169661 := rs (se 3 (by rfl) ⟨31811, by rfl⟩) (B 63623 (by norm_num) ⟨31811, by rfl⟩ (by norm_num))
theorem R169685 : Reach 169685 := rs (se 7 (by rfl) ⟨1988, by rfl⟩) (B 3977 (by norm_num) ⟨1988, by rfl⟩ (by norm_num))
theorem R169757 : Reach 169757 := rs (se 3 (by rfl) ⟨31829, by rfl⟩) (B 63659 (by norm_num) ⟨31829, by rfl⟩ (by norm_num))
theorem R169829 : Reach 169829 := rs (se 4 (by rfl) ⟨15921, by rfl⟩) (B 31843 (by norm_num) ⟨15921, by rfl⟩ (by norm_num))
theorem R169901 : Reach 169901 := rs (se 3 (by rfl) ⟨31856, by rfl⟩) (B 63713 (by norm_num) ⟨31856, by rfl⟩ (by norm_num))
theorem R890837 : Reach 890837 := rs (se 7 (by rfl) ⟨10439, by rfl⟩) (B 20879 (by norm_num) ⟨10439, by rfl⟩ (by norm_num))
theorem R169973 : Reach 169973 := rs (se 5 (by rfl) ⟨7967, by rfl⟩) (B 15935 (by norm_num) ⟨7967, by rfl⟩ (by norm_num))
theorem R563221 : Reach 563221 := rs (se 6 (by rfl) ⟨13200, by rfl⟩) (B 26401 (by norm_num) ⟨13200, by rfl⟩ (by norm_num))
theorem R170045 : Reach 170045 := rs (se 3 (by rfl) ⟨31883, by rfl⟩) (B 63767 (by norm_num) ⟨31883, by rfl⟩ (by norm_num))
theorem R170117 : Reach 170117 := rs (se 4 (by rfl) ⟨15948, by rfl⟩) (B 31897 (by norm_num) ⟨15948, by rfl⟩ (by norm_num))
theorem R137389 : Reach 137389 := rs (se 3 (by rfl) ⟨25760, by rfl⟩) (B 51521 (by norm_num) ⟨25760, by rfl⟩ (by norm_num))
theorem R170189 : Reach 170189 := rs (se 3 (by rfl) ⟨31910, by rfl⟩) (B 63821 (by norm_num) ⟨31910, by rfl⟩ (by norm_num))
theorem R104701 : Reach 104701 := rs (se 3 (by rfl) ⟨19631, by rfl⟩) (B 39263 (by norm_num) ⟨19631, by rfl⟩ (by norm_num))
theorem R170261 : Reach 170261 := rs (se 6 (by rfl) ⟨3990, by rfl⟩) (B 7981 (by norm_num) ⟨3990, by rfl⟩ (by norm_num))
theorem R399653 : Reach 399653 := rs (se 4 (by rfl) ⟨37467, by rfl⟩) (B 74935 (by norm_num) ⟨37467, by rfl⟩ (by norm_num))
theorem R170333 : Reach 170333 := rs (se 3 (by rfl) ⟨31937, by rfl⟩) (B 63875 (by norm_num) ⟨31937, by rfl⟩ (by norm_num))
theorem R170405 : Reach 170405 := rs (se 4 (by rfl) ⟨15975, by rfl⟩) (B 31951 (by norm_num) ⟨15975, by rfl⟩ (by norm_num))
theorem R170477 : Reach 170477 := rs (se 3 (by rfl) ⟨31964, by rfl⟩) (B 63929 (by norm_num) ⟨31964, by rfl⟩ (by norm_num))
theorem R432661 : Reach 432661 := rs (se 6 (by rfl) ⟨10140, by rfl⟩) (B 20281 (by norm_num) ⟨10140, by rfl⟩ (by norm_num))
theorem R170549 : Reach 170549 := rs (se 5 (by rfl) ⟨7994, by rfl⟩) (B 15989 (by norm_num) ⟨7994, by rfl⟩ (by norm_num))
theorem R203381 : Reach 203381 := rs (se 5 (by rfl) ⟨9533, by rfl⟩) (B 19067 (by norm_num) ⟨9533, by rfl⟩ (by norm_num))
theorem R170621 : Reach 170621 := rs (se 3 (by rfl) ⟨31991, by rfl⟩) (B 63983 (by norm_num) ⟨31991, by rfl⟩ (by norm_num))
theorem R170693 : Reach 170693 := rs (se 4 (by rfl) ⟨16002, by rfl⟩) (B 32005 (by norm_num) ⟨16002, by rfl⟩ (by norm_num))
theorem R170765 : Reach 170765 := rs (se 3 (by rfl) ⟨32018, by rfl⟩) (B 64037 (by norm_num) ⟨32018, by rfl⟩ (by norm_num))
theorem R170837 : Reach 170837 := rs (se 9 (by rfl) ⟨500, by rfl⟩) (B 1001 (by norm_num) ⟨500, by rfl⟩ (by norm_num))
theorem R170909 : Reach 170909 := rs (se 3 (by rfl) ⟨32045, by rfl⟩) (B 64091 (by norm_num) ⟨32045, by rfl⟩ (by norm_num))
theorem R170981 : Reach 170981 := rs (se 4 (by rfl) ⟨16029, by rfl⟩) (B 32059 (by norm_num) ⟨16029, by rfl⟩ (by norm_num))
theorem R171053 : Reach 171053 := rs (se 3 (by rfl) ⟨32072, by rfl⟩) (B 64145 (by norm_num) ⟨32072, by rfl⟩ (by norm_num))
theorem R171125 : Reach 171125 := rs (se 5 (by rfl) ⟨8021, by rfl⟩) (B 16043 (by norm_num) ⟨8021, by rfl⟩ (by norm_num))
theorem R171197 : Reach 171197 := rs (se 3 (by rfl) ⟨32099, by rfl⟩) (B 64199 (by norm_num) ⟨32099, by rfl⟩ (by norm_num))
theorem R269525 : Reach 269525 := rs (se 7 (by rfl) ⟨3158, by rfl⟩) (B 6317 (by norm_num) ⟨3158, by rfl⟩ (by norm_num))
theorem R466165 : Reach 466165 := rs (se 5 (by rfl) ⟨21851, by rfl⟩) (B 43703 (by norm_num) ⟨21851, by rfl⟩ (by norm_num))
theorem R171269 : Reach 171269 := rs (se 4 (by rfl) ⟨16056, by rfl⟩) (B 32113 (by norm_num) ⟨16056, by rfl⟩ (by norm_num))
theorem R171341 : Reach 171341 := rs (se 3 (by rfl) ⟨32126, by rfl⟩) (B 64253 (by norm_num) ⟨32126, by rfl⟩ (by norm_num))
theorem R171413 : Reach 171413 := rs (se 6 (by rfl) ⟨4017, by rfl⟩) (B 8035 (by norm_num) ⟨4017, by rfl⟩ (by norm_num))
theorem R171485 : Reach 171485 := rs (se 3 (by rfl) ⟨32153, by rfl⟩) (B 64307 (by norm_num) ⟨32153, by rfl⟩ (by norm_num))
theorem R138773 : Reach 138773 := rs (se 6 (by rfl) ⟨3252, by rfl⟩) (B 6505 (by norm_num) ⟨3252, by rfl⟩ (by norm_num))
theorem R171557 : Reach 171557 := rs (se 4 (by rfl) ⟨16083, by rfl⟩) (B 32167 (by norm_num) ⟨16083, by rfl⟩ (by norm_num))
theorem R171629 : Reach 171629 := rs (se 3 (by rfl) ⟨32180, by rfl⟩) (B 64361 (by norm_num) ⟨32180, by rfl⟩ (by norm_num))
theorem R171701 : Reach 171701 := rs (se 5 (by rfl) ⟨8048, by rfl⟩) (B 16097 (by norm_num) ⟨8048, by rfl⟩ (by norm_num))
theorem R138989 : Reach 138989 := rs (se 3 (by rfl) ⟨26060, by rfl⟩) (B 52121 (by norm_num) ⟨26060, by rfl⟩ (by norm_num))
theorem R171773 : Reach 171773 := rs (se 3 (by rfl) ⟨32207, by rfl⟩) (B 64415 (by norm_num) ⟨32207, by rfl⟩ (by norm_num))
theorem R270101 : Reach 270101 := rs (se 6 (by rfl) ⟨6330, by rfl⟩) (B 12661 (by norm_num) ⟨6330, by rfl⟩ (by norm_num))
theorem R171845 : Reach 171845 := rs (se 4 (by rfl) ⟨16110, by rfl⟩) (B 32221 (by norm_num) ⟨16110, by rfl⟩ (by norm_num))
theorem R171917 : Reach 171917 := rs (se 3 (by rfl) ⟨32234, by rfl⟩) (B 64469 (by norm_num) ⟨32234, by rfl⟩ (by norm_num))
theorem R434069 : Reach 434069 := rs (se 6 (by rfl) ⟨10173, by rfl⟩) (B 20347 (by norm_num) ⟨10173, by rfl⟩ (by norm_num))
theorem R171989 : Reach 171989 := rs (se 7 (by rfl) ⟨2015, by rfl⟩) (B 4031 (by norm_num) ⟨2015, by rfl⟩ (by norm_num))
theorem R172061 : Reach 172061 := rs (se 3 (by rfl) ⟨32261, by rfl⟩) (B 64523 (by norm_num) ⟨32261, by rfl⟩ (by norm_num))
theorem R106565 : Reach 106565 := rs (se 4 (by rfl) ⟨9990, by rfl⟩) (B 19981 (by norm_num) ⟨9990, by rfl⟩ (by norm_num))
theorem R172133 : Reach 172133 := rs (se 4 (by rfl) ⟨16137, by rfl⟩) (B 32275 (by norm_num) ⟨16137, by rfl⟩ (by norm_num))
theorem R172205 : Reach 172205 := rs (se 3 (by rfl) ⟨32288, by rfl⟩) (B 64577 (by norm_num) ⟨32288, by rfl⟩ (by norm_num))
theorem R139445 : Reach 139445 := rs (se 5 (by rfl) ⟨6536, by rfl⟩) (B 13073 (by norm_num) ⟨6536, by rfl⟩ (by norm_num))
theorem R106717 : Reach 106717 := rs (se 3 (by rfl) ⟨20009, by rfl⟩) (B 40019 (by norm_num) ⟨20009, by rfl⟩ (by norm_num))
theorem R172277 : Reach 172277 := rs (se 5 (by rfl) ⟨8075, by rfl⟩) (B 16151 (by norm_num) ⟨8075, by rfl⟩ (by norm_num))
theorem R205109 : Reach 205109 := rs (se 5 (by rfl) ⟨9614, by rfl⟩) (B 19229 (by norm_num) ⟨9614, by rfl⟩ (by norm_num))
theorem R172349 : Reach 172349 := rs (se 3 (by rfl) ⟨32315, by rfl⟩) (B 64631 (by norm_num) ⟨32315, by rfl⟩ (by norm_num))
theorem R368981 : Reach 368981 := rs (se 10 (by rfl) ⟨540, by rfl⟩) (B 1081 (by norm_num) ⟨540, by rfl⟩ (by norm_num))
theorem R172421 : Reach 172421 := rs (se 4 (by rfl) ⟨16164, by rfl⟩) (B 32329 (by norm_num) ⟨16164, by rfl⟩ (by norm_num))
theorem R172493 : Reach 172493 := rs (se 3 (by rfl) ⟨32342, by rfl⟩) (B 64685 (by norm_num) ⟨32342, by rfl⟩ (by norm_num))
theorem R434645 : Reach 434645 := rs (se 7 (by rfl) ⟨5093, by rfl⟩) (B 10187 (by norm_num) ⟨5093, by rfl⟩ (by norm_num))
theorem R107021 : Reach 107021 := rs (se 3 (by rfl) ⟨20066, by rfl⟩) (B 40133 (by norm_num) ⟨20066, by rfl⟩ (by norm_num))
theorem R172565 : Reach 172565 := rs (se 6 (by rfl) ⟨4044, by rfl⟩) (B 8089 (by norm_num) ⟨4044, by rfl⟩ (by norm_num))
theorem R172637 : Reach 172637 := rs (se 3 (by rfl) ⟨32369, by rfl⟩) (B 64739 (by norm_num) ⟨32369, by rfl⟩ (by norm_num))
theorem R172709 : Reach 172709 := rs (se 4 (by rfl) ⟨16191, by rfl⟩) (B 32383 (by norm_num) ⟨16191, by rfl⟩ (by norm_num))
theorem R172781 : Reach 172781 := rs (se 3 (by rfl) ⟨32396, by rfl⟩) (B 64793 (by norm_num) ⟨32396, by rfl⟩ (by norm_num))
theorem R140069 : Reach 140069 := rs (se 4 (by rfl) ⟨13131, by rfl⟩) (B 26263 (by norm_num) ⟨13131, by rfl⟩ (by norm_num))
theorem R172853 : Reach 172853 := rs (se 5 (by rfl) ⟨8102, by rfl⟩) (B 16205 (by norm_num) ⟨8102, by rfl⟩ (by norm_num))
theorem R172925 : Reach 172925 := rs (se 3 (by rfl) ⟨32423, by rfl⟩) (B 64847 (by norm_num) ⟨32423, by rfl⟩ (by norm_num))
theorem R172997 : Reach 172997 := rs (se 4 (by rfl) ⟨16218, by rfl⟩) (B 32437 (by norm_num) ⟨16218, by rfl⟩ (by norm_num))
theorem R140293 : Reach 140293 := rs (se 4 (by rfl) ⟨13152, by rfl⟩) (B 26305 (by norm_num) ⟨13152, by rfl⟩ (by norm_num))
theorem R173069 : Reach 173069 := rs (se 3 (by rfl) ⟨32450, by rfl⟩) (B 64901 (by norm_num) ⟨32450, by rfl⟩ (by norm_num))
theorem R926741 : Reach 926741 := rs (se 6 (by rfl) ⟨21720, by rfl⟩) (B 43441 (by norm_num) ⟨21720, by rfl⟩ (by norm_num))
theorem R107573 : Reach 107573 := rs (se 5 (by rfl) ⟨5042, by rfl⟩) (B 10085 (by norm_num) ⟨5042, by rfl⟩ (by norm_num))
theorem R173141 : Reach 173141 := rs (se 8 (by rfl) ⟨1014, by rfl⟩) (B 2029 (by norm_num) ⟨1014, by rfl⟩ (by norm_num))
theorem R173213 : Reach 173213 := rs (se 3 (by rfl) ⟨32477, by rfl⟩) (B 64955 (by norm_num) ⟨32477, by rfl⟩ (by norm_num))
theorem R173285 : Reach 173285 := rs (se 4 (by rfl) ⟨16245, by rfl⟩) (B 32491 (by norm_num) ⟨16245, by rfl⟩ (by norm_num))
theorem R173357 : Reach 173357 := rs (se 3 (by rfl) ⟨32504, by rfl⟩) (B 65009 (by norm_num) ⟨32504, by rfl⟩ (by norm_num))
theorem R173429 : Reach 173429 := rs (se 5 (by rfl) ⟨8129, by rfl⟩) (B 16259 (by norm_num) ⟨8129, by rfl⟩ (by norm_num))
theorem R75129 : Reach 75129 := rs (se 2 (by rfl) ⟨28173, by rfl⟩) (B 56347 (by norm_num) ⟨28173, by rfl⟩ (by norm_num))
theorem R75133 : Reach 75133 := rs (se 3 (by rfl) ⟨14087, by rfl⟩) (B 28175 (by norm_num) ⟨14087, by rfl⟩ (by norm_num))
theorem R75137 : Reach 75137 := rs (se 2 (by rfl) ⟨28176, by rfl⟩) (B 56353 (by norm_num) ⟨28176, by rfl⟩ (by norm_num))
theorem R75141 : Reach 75141 := rs (se 4 (by rfl) ⟨7044, by rfl⟩) (B 14089 (by norm_num) ⟨7044, by rfl⟩ (by norm_num))
theorem R75145 : Reach 75145 := rs (se 2 (by rfl) ⟨28179, by rfl⟩) (B 56359 (by norm_num) ⟨28179, by rfl⟩ (by norm_num))
theorem R75149 : Reach 75149 := rs (se 3 (by rfl) ⟨14090, by rfl⟩) (B 28181 (by norm_num) ⟨14090, by rfl⟩ (by norm_num))
theorem R75153 : Reach 75153 := rs (se 2 (by rfl) ⟨28182, by rfl⟩) (B 56365 (by norm_num) ⟨28182, by rfl⟩ (by norm_num))
theorem R75157 : Reach 75157 := rs (se 6 (by rfl) ⟨1761, by rfl⟩) (B 3523 (by norm_num) ⟨1761, by rfl⟩ (by norm_num))
theorem R75161 : Reach 75161 := rs (se 2 (by rfl) ⟨28185, by rfl⟩) (B 56371 (by norm_num) ⟨28185, by rfl⟩ (by norm_num))
theorem R75165 : Reach 75165 := rs (se 3 (by rfl) ⟨14093, by rfl⟩) (B 28187 (by norm_num) ⟨14093, by rfl⟩ (by norm_num))
theorem R75169 : Reach 75169 := rs (se 2 (by rfl) ⟨28188, by rfl⟩) (B 56377 (by norm_num) ⟨28188, by rfl⟩ (by norm_num))
theorem R75173 : Reach 75173 := rs (se 4 (by rfl) ⟨7047, by rfl⟩) (B 14095 (by norm_num) ⟨7047, by rfl⟩ (by norm_num))
theorem R75177 : Reach 75177 := rs (se 2 (by rfl) ⟨28191, by rfl⟩) (B 56383 (by norm_num) ⟨28191, by rfl⟩ (by norm_num))
theorem R75181 : Reach 75181 := rs (se 3 (by rfl) ⟨14096, by rfl⟩) (B 28193 (by norm_num) ⟨14096, by rfl⟩ (by norm_num))
theorem R75185 : Reach 75185 := rs (se 2 (by rfl) ⟨28194, by rfl⟩) (B 56389 (by norm_num) ⟨28194, by rfl⟩ (by norm_num))
theorem R75189 : Reach 75189 := rs (se 5 (by rfl) ⟨3524, by rfl⟩) (B 7049 (by norm_num) ⟨3524, by rfl⟩ (by norm_num))
theorem R75193 : Reach 75193 := rs (se 2 (by rfl) ⟨28197, by rfl⟩) (B 56395 (by norm_num) ⟨28197, by rfl⟩ (by norm_num))
theorem R75197 : Reach 75197 := rs (se 3 (by rfl) ⟨14099, by rfl⟩) (B 28199 (by norm_num) ⟨14099, by rfl⟩ (by norm_num))
theorem R173501 : Reach 173501 := rs (se 3 (by rfl) ⟨32531, by rfl⟩) (B 65063 (by norm_num) ⟨32531, by rfl⟩ (by norm_num))
theorem R75201 : Reach 75201 := rs (se 2 (by rfl) ⟨28200, by rfl⟩) (B 56401 (by norm_num) ⟨28200, by rfl⟩ (by norm_num))
theorem R75205 : Reach 75205 := rs (se 4 (by rfl) ⟨7050, by rfl⟩) (B 14101 (by norm_num) ⟨7050, by rfl⟩ (by norm_num))
theorem R75209 : Reach 75209 := rs (se 2 (by rfl) ⟨28203, by rfl⟩) (B 56407 (by norm_num) ⟨28203, by rfl⟩ (by norm_num))
theorem R75213 : Reach 75213 := rs (se 3 (by rfl) ⟨14102, by rfl⟩) (B 28205 (by norm_num) ⟨14102, by rfl⟩ (by norm_num))
theorem R75217 : Reach 75217 := rs (se 2 (by rfl) ⟨28206, by rfl⟩) (B 56413 (by norm_num) ⟨28206, by rfl⟩ (by norm_num))
theorem R75221 : Reach 75221 := rs (se 7 (by rfl) ⟨881, by rfl⟩) (B 1763 (by norm_num) ⟨881, by rfl⟩ (by norm_num))
theorem R2041301 : Reach 2041301 := rs (se 7 (by rfl) ⟨23921, by rfl⟩) (B 47843 (by norm_num) ⟨23921, by rfl⟩ (by norm_num))
theorem R75225 : Reach 75225 := rs (se 2 (by rfl) ⟨28209, by rfl⟩) (B 56419 (by norm_num) ⟨28209, by rfl⟩ (by norm_num))
theorem R75229 : Reach 75229 := rs (se 3 (by rfl) ⟨14105, by rfl⟩) (B 28211 (by norm_num) ⟨14105, by rfl⟩ (by norm_num))
theorem R75233 : Reach 75233 := rs (se 2 (by rfl) ⟨28212, by rfl⟩) (B 56425 (by norm_num) ⟨28212, by rfl⟩ (by norm_num))
theorem R75237 : Reach 75237 := rs (se 4 (by rfl) ⟨7053, by rfl⟩) (B 14107 (by norm_num) ⟨7053, by rfl⟩ (by norm_num))
theorem R75241 : Reach 75241 := rs (se 2 (by rfl) ⟨28215, by rfl⟩) (B 56431 (by norm_num) ⟨28215, by rfl⟩ (by norm_num))
theorem R75245 : Reach 75245 := rs (se 3 (by rfl) ⟨14108, by rfl⟩) (B 28217 (by norm_num) ⟨14108, by rfl⟩ (by norm_num))
theorem R75249 : Reach 75249 := rs (se 2 (by rfl) ⟨28218, by rfl⟩) (B 56437 (by norm_num) ⟨28218, by rfl⟩ (by norm_num))
theorem R75253 : Reach 75253 := rs (se 5 (by rfl) ⟨3527, by rfl⟩) (B 7055 (by norm_num) ⟨3527, by rfl⟩ (by norm_num))
theorem R75257 : Reach 75257 := rs (se 2 (by rfl) ⟨28221, by rfl⟩) (B 56443 (by norm_num) ⟨28221, by rfl⟩ (by norm_num))
theorem R75261 : Reach 75261 := rs (se 3 (by rfl) ⟨14111, by rfl⟩) (B 28223 (by norm_num) ⟨14111, by rfl⟩ (by norm_num))
theorem R75265 : Reach 75265 := rs (se 2 (by rfl) ⟨28224, by rfl⟩) (B 56449 (by norm_num) ⟨28224, by rfl⟩ (by norm_num))
theorem R75269 : Reach 75269 := rs (se 4 (by rfl) ⟨7056, by rfl⟩) (B 14113 (by norm_num) ⟨7056, by rfl⟩ (by norm_num))
theorem R173573 : Reach 173573 := rs (se 4 (by rfl) ⟨16272, by rfl⟩) (B 32545 (by norm_num) ⟨16272, by rfl⟩ (by norm_num))
theorem R75273 : Reach 75273 := rs (se 2 (by rfl) ⟨28227, by rfl⟩) (B 56455 (by norm_num) ⟨28227, by rfl⟩ (by norm_num))
theorem R75277 : Reach 75277 := rs (se 3 (by rfl) ⟨14114, by rfl⟩) (B 28229 (by norm_num) ⟨14114, by rfl⟩ (by norm_num))
theorem R75281 : Reach 75281 := rs (se 2 (by rfl) ⟨28230, by rfl⟩) (B 56461 (by norm_num) ⟨28230, by rfl⟩ (by norm_num))
theorem R75285 : Reach 75285 := rs (se 6 (by rfl) ⟨1764, by rfl⟩) (B 3529 (by norm_num) ⟨1764, by rfl⟩ (by norm_num))
theorem R75289 : Reach 75289 := rs (se 2 (by rfl) ⟨28233, by rfl⟩) (B 56467 (by norm_num) ⟨28233, by rfl⟩ (by norm_num))
theorem R75293 : Reach 75293 := rs (se 3 (by rfl) ⟨14117, by rfl⟩) (B 28235 (by norm_num) ⟨14117, by rfl⟩ (by norm_num))
theorem R75297 : Reach 75297 := rs (se 2 (by rfl) ⟨28236, by rfl⟩) (B 56473 (by norm_num) ⟨28236, by rfl⟩ (by norm_num))
theorem R75301 : Reach 75301 := rs (se 4 (by rfl) ⟨7059, by rfl⟩) (B 14119 (by norm_num) ⟨7059, by rfl⟩ (by norm_num))
theorem R75305 : Reach 75305 := rs (se 2 (by rfl) ⟨28239, by rfl⟩) (B 56479 (by norm_num) ⟨28239, by rfl⟩ (by norm_num))
theorem R75309 : Reach 75309 := rs (se 3 (by rfl) ⟨14120, by rfl⟩) (B 28241 (by norm_num) ⟨14120, by rfl⟩ (by norm_num))
theorem R75313 : Reach 75313 := rs (se 2 (by rfl) ⟨28242, by rfl⟩) (B 56485 (by norm_num) ⟨28242, by rfl⟩ (by norm_num))
theorem R75317 : Reach 75317 := rs (se 5 (by rfl) ⟨3530, by rfl⟩) (B 7061 (by norm_num) ⟨3530, by rfl⟩ (by norm_num))
theorem R75321 : Reach 75321 := rs (se 2 (by rfl) ⟨28245, by rfl⟩) (B 56491 (by norm_num) ⟨28245, by rfl⟩ (by norm_num))
theorem R75325 : Reach 75325 := rs (se 3 (by rfl) ⟨14123, by rfl⟩) (B 28247 (by norm_num) ⟨14123, by rfl⟩ (by norm_num))
theorem R75329 : Reach 75329 := rs (se 2 (by rfl) ⟨28248, by rfl⟩) (B 56497 (by norm_num) ⟨28248, by rfl⟩ (by norm_num))
theorem R75333 : Reach 75333 := rs (se 4 (by rfl) ⟨7062, by rfl⟩) (B 14125 (by norm_num) ⟨7062, by rfl⟩ (by norm_num))
theorem R75337 : Reach 75337 := rs (se 2 (by rfl) ⟨28251, by rfl⟩) (B 56503 (by norm_num) ⟨28251, by rfl⟩ (by norm_num))
theorem R75341 : Reach 75341 := rs (se 3 (by rfl) ⟨14126, by rfl⟩) (B 28253 (by norm_num) ⟨14126, by rfl⟩ (by norm_num))
theorem R173645 : Reach 173645 := rs (se 3 (by rfl) ⟨32558, by rfl⟩) (B 65117 (by norm_num) ⟨32558, by rfl⟩ (by norm_num))
theorem R75345 : Reach 75345 := rs (se 2 (by rfl) ⟨28254, by rfl⟩) (B 56509 (by norm_num) ⟨28254, by rfl⟩ (by norm_num))
theorem R75349 : Reach 75349 := rs (se 8 (by rfl) ⟨441, by rfl⟩) (B 883 (by norm_num) ⟨441, by rfl⟩ (by norm_num))
theorem R75353 : Reach 75353 := rs (se 2 (by rfl) ⟨28257, by rfl⟩) (B 56515 (by norm_num) ⟨28257, by rfl⟩ (by norm_num))
theorem R75357 : Reach 75357 := rs (se 3 (by rfl) ⟨14129, by rfl⟩) (B 28259 (by norm_num) ⟨14129, by rfl⟩ (by norm_num))
theorem R75361 : Reach 75361 := rs (se 2 (by rfl) ⟨28260, by rfl⟩) (B 56521 (by norm_num) ⟨28260, by rfl⟩ (by norm_num))
theorem R75365 : Reach 75365 := rs (se 4 (by rfl) ⟨7065, by rfl⟩) (B 14131 (by norm_num) ⟨7065, by rfl⟩ (by norm_num))
theorem R75369 : Reach 75369 := rs (se 2 (by rfl) ⟨28263, by rfl⟩) (B 56527 (by norm_num) ⟨28263, by rfl⟩ (by norm_num))
theorem R75373 : Reach 75373 := rs (se 3 (by rfl) ⟨14132, by rfl⟩) (B 28265 (by norm_num) ⟨14132, by rfl⟩ (by norm_num))
theorem R75377 : Reach 75377 := rs (se 2 (by rfl) ⟨28266, by rfl⟩) (B 56533 (by norm_num) ⟨28266, by rfl⟩ (by norm_num))
theorem R75381 : Reach 75381 := rs (se 5 (by rfl) ⟨3533, by rfl⟩) (B 7067 (by norm_num) ⟨3533, by rfl⟩ (by norm_num))
theorem R75385 : Reach 75385 := rs (se 2 (by rfl) ⟨28269, by rfl⟩) (B 56539 (by norm_num) ⟨28269, by rfl⟩ (by norm_num))
theorem R75389 : Reach 75389 := rs (se 3 (by rfl) ⟨14135, by rfl⟩) (B 28271 (by norm_num) ⟨14135, by rfl⟩ (by norm_num))
theorem R75393 : Reach 75393 := rs (se 2 (by rfl) ⟨28272, by rfl⟩) (B 56545 (by norm_num) ⟨28272, by rfl⟩ (by norm_num))
theorem R75397 : Reach 75397 := rs (se 4 (by rfl) ⟨7068, by rfl⟩) (B 14137 (by norm_num) ⟨7068, by rfl⟩ (by norm_num))
theorem R75401 : Reach 75401 := rs (se 2 (by rfl) ⟨28275, by rfl⟩) (B 56551 (by norm_num) ⟨28275, by rfl⟩ (by norm_num))
theorem R75405 : Reach 75405 := rs (se 3 (by rfl) ⟨14138, by rfl⟩) (B 28277 (by norm_num) ⟨14138, by rfl⟩ (by norm_num))
theorem R75409 : Reach 75409 := rs (se 2 (by rfl) ⟨28278, by rfl⟩) (B 56557 (by norm_num) ⟨28278, by rfl⟩ (by norm_num))
theorem R75413 : Reach 75413 := rs (se 6 (by rfl) ⟨1767, by rfl⟩) (B 3535 (by norm_num) ⟨1767, by rfl⟩ (by norm_num))
theorem R173717 : Reach 173717 := rs (se 6 (by rfl) ⟨4071, by rfl⟩) (B 8143 (by norm_num) ⟨4071, by rfl⟩ (by norm_num))
theorem R75417 : Reach 75417 := rs (se 2 (by rfl) ⟨28281, by rfl⟩) (B 56563 (by norm_num) ⟨28281, by rfl⟩ (by norm_num))
theorem R75421 : Reach 75421 := rs (se 3 (by rfl) ⟨14141, by rfl⟩) (B 28283 (by norm_num) ⟨14141, by rfl⟩ (by norm_num))
theorem R75425 : Reach 75425 := rs (se 2 (by rfl) ⟨28284, by rfl⟩) (B 56569 (by norm_num) ⟨28284, by rfl⟩ (by norm_num))
theorem R75429 : Reach 75429 := rs (se 4 (by rfl) ⟨7071, by rfl⟩) (B 14143 (by norm_num) ⟨7071, by rfl⟩ (by norm_num))
theorem R75433 : Reach 75433 := rs (se 2 (by rfl) ⟨28287, by rfl⟩) (B 56575 (by norm_num) ⟨28287, by rfl⟩ (by norm_num))
theorem R75437 : Reach 75437 := rs (se 3 (by rfl) ⟨14144, by rfl⟩) (B 28289 (by norm_num) ⟨14144, by rfl⟩ (by norm_num))
theorem R75441 : Reach 75441 := rs (se 2 (by rfl) ⟨28290, by rfl⟩) (B 56581 (by norm_num) ⟨28290, by rfl⟩ (by norm_num))
theorem R75445 : Reach 75445 := rs (se 5 (by rfl) ⟨3536, by rfl⟩) (B 7073 (by norm_num) ⟨3536, by rfl⟩ (by norm_num))
theorem R75449 : Reach 75449 := rs (se 2 (by rfl) ⟨28293, by rfl⟩) (B 56587 (by norm_num) ⟨28293, by rfl⟩ (by norm_num))
theorem R75453 : Reach 75453 := rs (se 3 (by rfl) ⟨14147, by rfl⟩) (B 28295 (by norm_num) ⟨14147, by rfl⟩ (by norm_num))
theorem R75457 : Reach 75457 := rs (se 2 (by rfl) ⟨28296, by rfl⟩) (B 56593 (by norm_num) ⟨28296, by rfl⟩ (by norm_num))
theorem R75461 : Reach 75461 := rs (se 4 (by rfl) ⟨7074, by rfl⟩) (B 14149 (by norm_num) ⟨7074, by rfl⟩ (by norm_num))
theorem R75465 : Reach 75465 := rs (se 2 (by rfl) ⟨28299, by rfl⟩) (B 56599 (by norm_num) ⟨28299, by rfl⟩ (by norm_num))
theorem R75469 : Reach 75469 := rs (se 3 (by rfl) ⟨14150, by rfl⟩) (B 28301 (by norm_num) ⟨14150, by rfl⟩ (by norm_num))
theorem R75473 : Reach 75473 := rs (se 2 (by rfl) ⟨28302, by rfl⟩) (B 56605 (by norm_num) ⟨28302, by rfl⟩ (by norm_num))
theorem R75477 : Reach 75477 := rs (se 7 (by rfl) ⟨884, by rfl⟩) (B 1769 (by norm_num) ⟨884, by rfl⟩ (by norm_num))
theorem R75481 : Reach 75481 := rs (se 2 (by rfl) ⟨28305, by rfl⟩) (B 56611 (by norm_num) ⟨28305, by rfl⟩ (by norm_num))
theorem R75485 : Reach 75485 := rs (se 3 (by rfl) ⟨14153, by rfl⟩) (B 28307 (by norm_num) ⟨14153, by rfl⟩ (by norm_num))
theorem R173789 : Reach 173789 := rs (se 3 (by rfl) ⟨32585, by rfl⟩) (B 65171 (by norm_num) ⟨32585, by rfl⟩ (by norm_num))
theorem R108253 : Reach 108253 := rs (se 3 (by rfl) ⟨20297, by rfl⟩) (B 40595 (by norm_num) ⟨20297, by rfl⟩ (by norm_num))
theorem R75489 : Reach 75489 := rs (se 2 (by rfl) ⟨28308, by rfl⟩) (B 56617 (by norm_num) ⟨28308, by rfl⟩ (by norm_num))
theorem R75493 : Reach 75493 := rs (se 4 (by rfl) ⟨7077, by rfl⟩) (B 14155 (by norm_num) ⟨7077, by rfl⟩ (by norm_num))
theorem R75497 : Reach 75497 := rs (se 2 (by rfl) ⟨28311, by rfl⟩) (B 56623 (by norm_num) ⟨28311, by rfl⟩ (by norm_num))
theorem R75501 : Reach 75501 := rs (se 3 (by rfl) ⟨14156, by rfl⟩) (B 28313 (by norm_num) ⟨14156, by rfl⟩ (by norm_num))
theorem R75505 : Reach 75505 := rs (se 2 (by rfl) ⟨28314, by rfl⟩) (B 56629 (by norm_num) ⟨28314, by rfl⟩ (by norm_num))
theorem R75509 : Reach 75509 := rs (se 5 (by rfl) ⟨3539, by rfl⟩) (B 7079 (by norm_num) ⟨3539, by rfl⟩ (by norm_num))
theorem R75513 : Reach 75513 := rs (se 2 (by rfl) ⟨28317, by rfl⟩) (B 56635 (by norm_num) ⟨28317, by rfl⟩ (by norm_num))
theorem R75517 : Reach 75517 := rs (se 3 (by rfl) ⟨14159, by rfl⟩) (B 28319 (by norm_num) ⟨14159, by rfl⟩ (by norm_num))
theorem R75521 : Reach 75521 := rs (se 2 (by rfl) ⟨28320, by rfl⟩) (B 56641 (by norm_num) ⟨28320, by rfl⟩ (by norm_num))
theorem R75525 : Reach 75525 := rs (se 4 (by rfl) ⟨7080, by rfl⟩) (B 14161 (by norm_num) ⟨7080, by rfl⟩ (by norm_num))
theorem R75529 : Reach 75529 := rs (se 2 (by rfl) ⟨28323, by rfl⟩) (B 56647 (by norm_num) ⟨28323, by rfl⟩ (by norm_num))
theorem R75533 : Reach 75533 := rs (se 3 (by rfl) ⟨14162, by rfl⟩) (B 28325 (by norm_num) ⟨14162, by rfl⟩ (by norm_num))
theorem R75537 : Reach 75537 := rs (se 2 (by rfl) ⟨28326, by rfl⟩) (B 56653 (by norm_num) ⟨28326, by rfl⟩ (by norm_num))
theorem R75541 : Reach 75541 := rs (se 6 (by rfl) ⟨1770, by rfl⟩) (B 3541 (by norm_num) ⟨1770, by rfl⟩ (by norm_num))
theorem R75545 : Reach 75545 := rs (se 2 (by rfl) ⟨28329, by rfl⟩) (B 56659 (by norm_num) ⟨28329, by rfl⟩ (by norm_num))
theorem R75549 : Reach 75549 := rs (se 3 (by rfl) ⟨14165, by rfl⟩) (B 28331 (by norm_num) ⟨14165, by rfl⟩ (by norm_num))
theorem R75553 : Reach 75553 := rs (se 2 (by rfl) ⟨28332, by rfl⟩) (B 56665 (by norm_num) ⟨28332, by rfl⟩ (by norm_num))
theorem R75557 : Reach 75557 := rs (se 4 (by rfl) ⟨7083, by rfl⟩) (B 14167 (by norm_num) ⟨7083, by rfl⟩ (by norm_num))
theorem R108325 : Reach 108325 := rs (se 4 (by rfl) ⟨10155, by rfl⟩) (B 20311 (by norm_num) ⟨10155, by rfl⟩ (by norm_num))
theorem R173861 : Reach 173861 := rs (se 4 (by rfl) ⟨16299, by rfl⟩) (B 32599 (by norm_num) ⟨16299, by rfl⟩ (by norm_num))
theorem R75561 : Reach 75561 := rs (se 2 (by rfl) ⟨28335, by rfl⟩) (B 56671 (by norm_num) ⟨28335, by rfl⟩ (by norm_num))
theorem R75565 : Reach 75565 := rs (se 3 (by rfl) ⟨14168, by rfl⟩) (B 28337 (by norm_num) ⟨14168, by rfl⟩ (by norm_num))
theorem R75569 : Reach 75569 := rs (se 2 (by rfl) ⟨28338, by rfl⟩) (B 56677 (by norm_num) ⟨28338, by rfl⟩ (by norm_num))
theorem R75573 : Reach 75573 := rs (se 5 (by rfl) ⟨3542, by rfl⟩) (B 7085 (by norm_num) ⟨3542, by rfl⟩ (by norm_num))
theorem R75577 : Reach 75577 := rs (se 2 (by rfl) ⟨28341, by rfl⟩) (B 56683 (by norm_num) ⟨28341, by rfl⟩ (by norm_num))
theorem R75581 : Reach 75581 := rs (se 3 (by rfl) ⟨14171, by rfl⟩) (B 28343 (by norm_num) ⟨14171, by rfl⟩ (by norm_num))
theorem R75585 : Reach 75585 := rs (se 2 (by rfl) ⟨28344, by rfl⟩) (B 56689 (by norm_num) ⟨28344, by rfl⟩ (by norm_num))
theorem R75589 : Reach 75589 := rs (se 4 (by rfl) ⟨7086, by rfl⟩) (B 14173 (by norm_num) ⟨7086, by rfl⟩ (by norm_num))
theorem R75593 : Reach 75593 := rs (se 2 (by rfl) ⟨28347, by rfl⟩) (B 56695 (by norm_num) ⟨28347, by rfl⟩ (by norm_num))
theorem R75597 : Reach 75597 := rs (se 3 (by rfl) ⟨14174, by rfl⟩) (B 28349 (by norm_num) ⟨14174, by rfl⟩ (by norm_num))
theorem R75601 : Reach 75601 := rs (se 2 (by rfl) ⟨28350, by rfl⟩) (B 56701 (by norm_num) ⟨28350, by rfl⟩ (by norm_num))
theorem R75605 : Reach 75605 := rs (se 9 (by rfl) ⟨221, by rfl⟩) (B 443 (by norm_num) ⟨221, by rfl⟩ (by norm_num))
theorem R75609 : Reach 75609 := rs (se 2 (by rfl) ⟨28353, by rfl⟩) (B 56707 (by norm_num) ⟨28353, by rfl⟩ (by norm_num))
theorem R75613 : Reach 75613 := rs (se 3 (by rfl) ⟨14177, by rfl⟩) (B 28355 (by norm_num) ⟨14177, by rfl⟩ (by norm_num))
theorem R75617 : Reach 75617 := rs (se 2 (by rfl) ⟨28356, by rfl⟩) (B 56713 (by norm_num) ⟨28356, by rfl⟩ (by norm_num))
theorem R75621 : Reach 75621 := rs (se 4 (by rfl) ⟨7089, by rfl⟩) (B 14179 (by norm_num) ⟨7089, by rfl⟩ (by norm_num))
theorem R75625 : Reach 75625 := rs (se 2 (by rfl) ⟨28359, by rfl⟩) (B 56719 (by norm_num) ⟨28359, by rfl⟩ (by norm_num))
theorem R75629 : Reach 75629 := rs (se 3 (by rfl) ⟨14180, by rfl⟩) (B 28361 (by norm_num) ⟨14180, by rfl⟩ (by norm_num))
theorem R173933 : Reach 173933 := rs (se 3 (by rfl) ⟨32612, by rfl⟩) (B 65225 (by norm_num) ⟨32612, by rfl⟩ (by norm_num))
theorem R75633 : Reach 75633 := rs (se 2 (by rfl) ⟨28362, by rfl⟩) (B 56725 (by norm_num) ⟨28362, by rfl⟩ (by norm_num))
theorem R75637 : Reach 75637 := rs (se 5 (by rfl) ⟨3545, by rfl⟩) (B 7091 (by norm_num) ⟨3545, by rfl⟩ (by norm_num))
theorem R75641 : Reach 75641 := rs (se 2 (by rfl) ⟨28365, by rfl⟩) (B 56731 (by norm_num) ⟨28365, by rfl⟩ (by norm_num))
theorem R75645 : Reach 75645 := rs (se 3 (by rfl) ⟨14183, by rfl⟩) (B 28367 (by norm_num) ⟨14183, by rfl⟩ (by norm_num))
theorem R75649 : Reach 75649 := rs (se 2 (by rfl) ⟨28368, by rfl⟩) (B 56737 (by norm_num) ⟨28368, by rfl⟩ (by norm_num))
theorem R75653 : Reach 75653 := rs (se 4 (by rfl) ⟨7092, by rfl⟩) (B 14185 (by norm_num) ⟨7092, by rfl⟩ (by norm_num))
theorem R75657 : Reach 75657 := rs (se 2 (by rfl) ⟨28371, by rfl⟩) (B 56743 (by norm_num) ⟨28371, by rfl⟩ (by norm_num))
theorem R75661 : Reach 75661 := rs (se 3 (by rfl) ⟨14186, by rfl⟩) (B 28373 (by norm_num) ⟨14186, by rfl⟩ (by norm_num))
theorem R75665 : Reach 75665 := rs (se 2 (by rfl) ⟨28374, by rfl⟩) (B 56749 (by norm_num) ⟨28374, by rfl⟩ (by norm_num))
theorem R75669 : Reach 75669 := rs (se 6 (by rfl) ⟨1773, by rfl⟩) (B 3547 (by norm_num) ⟨1773, by rfl⟩ (by norm_num))
theorem R75673 : Reach 75673 := rs (se 2 (by rfl) ⟨28377, by rfl⟩) (B 56755 (by norm_num) ⟨28377, by rfl⟩ (by norm_num))
theorem R75677 : Reach 75677 := rs (se 3 (by rfl) ⟨14189, by rfl⟩) (B 28379 (by norm_num) ⟨14189, by rfl⟩ (by norm_num))
theorem R108445 : Reach 108445 := rs (se 3 (by rfl) ⟨20333, by rfl⟩) (B 40667 (by norm_num) ⟨20333, by rfl⟩ (by norm_num))
theorem R75681 : Reach 75681 := rs (se 2 (by rfl) ⟨28380, by rfl⟩) (B 56761 (by norm_num) ⟨28380, by rfl⟩ (by norm_num))
theorem R75685 : Reach 75685 := rs (se 4 (by rfl) ⟨7095, by rfl⟩) (B 14191 (by norm_num) ⟨7095, by rfl⟩ (by norm_num))
theorem R141221 : Reach 141221 := rs (se 4 (by rfl) ⟨13239, by rfl⟩) (B 26479 (by norm_num) ⟨13239, by rfl⟩ (by norm_num))
theorem R75689 : Reach 75689 := rs (se 2 (by rfl) ⟨28383, by rfl⟩) (B 56767 (by norm_num) ⟨28383, by rfl⟩ (by norm_num))
theorem R75693 : Reach 75693 := rs (se 3 (by rfl) ⟨14192, by rfl⟩) (B 28385 (by norm_num) ⟨14192, by rfl⟩ (by norm_num))
theorem R75697 : Reach 75697 := rs (se 2 (by rfl) ⟨28386, by rfl⟩) (B 56773 (by norm_num) ⟨28386, by rfl⟩ (by norm_num))
theorem R75701 : Reach 75701 := rs (se 5 (by rfl) ⟨3548, by rfl⟩) (B 7097 (by norm_num) ⟨3548, by rfl⟩ (by norm_num))
theorem R174005 : Reach 174005 := rs (se 5 (by rfl) ⟨8156, by rfl⟩) (B 16313 (by norm_num) ⟨8156, by rfl⟩ (by norm_num))
theorem R75705 : Reach 75705 := rs (se 2 (by rfl) ⟨28389, by rfl⟩) (B 56779 (by norm_num) ⟨28389, by rfl⟩ (by norm_num))
theorem R75709 : Reach 75709 := rs (se 3 (by rfl) ⟨14195, by rfl⟩) (B 28391 (by norm_num) ⟨14195, by rfl⟩ (by norm_num))
theorem R75713 : Reach 75713 := rs (se 2 (by rfl) ⟨28392, by rfl⟩) (B 56785 (by norm_num) ⟨28392, by rfl⟩ (by norm_num))
theorem R75717 : Reach 75717 := rs (se 4 (by rfl) ⟨7098, by rfl⟩) (B 14197 (by norm_num) ⟨7098, by rfl⟩ (by norm_num))
theorem R75721 : Reach 75721 := rs (se 2 (by rfl) ⟨28395, by rfl⟩) (B 56791 (by norm_num) ⟨28395, by rfl⟩ (by norm_num))
theorem R75725 : Reach 75725 := rs (se 3 (by rfl) ⟨14198, by rfl⟩) (B 28397 (by norm_num) ⟨14198, by rfl⟩ (by norm_num))
theorem R75729 : Reach 75729 := rs (se 2 (by rfl) ⟨28398, by rfl⟩) (B 56797 (by norm_num) ⟨28398, by rfl⟩ (by norm_num))
theorem R75733 : Reach 75733 := rs (se 7 (by rfl) ⟨887, by rfl⟩) (B 1775 (by norm_num) ⟨887, by rfl⟩ (by norm_num))
theorem R567253 : Reach 567253 := rs (se 7 (by rfl) ⟨6647, by rfl⟩) (B 13295 (by norm_num) ⟨6647, by rfl⟩ (by norm_num))
theorem R337877 : Reach 337877 := rs (se 7 (by rfl) ⟨3959, by rfl⟩) (B 7919 (by norm_num) ⟨3959, by rfl⟩ (by norm_num))
theorem R75737 : Reach 75737 := rs (se 2 (by rfl) ⟨28401, by rfl⟩) (B 56803 (by norm_num) ⟨28401, by rfl⟩ (by norm_num))
theorem R75741 : Reach 75741 := rs (se 3 (by rfl) ⟨14201, by rfl⟩) (B 28403 (by norm_num) ⟨14201, by rfl⟩ (by norm_num))
theorem R75745 : Reach 75745 := rs (se 2 (by rfl) ⟨28404, by rfl⟩) (B 56809 (by norm_num) ⟨28404, by rfl⟩ (by norm_num))
theorem R75749 : Reach 75749 := rs (se 4 (by rfl) ⟨7101, by rfl⟩) (B 14203 (by norm_num) ⟨7101, by rfl⟩ (by norm_num))
theorem R75753 : Reach 75753 := rs (se 2 (by rfl) ⟨28407, by rfl⟩) (B 56815 (by norm_num) ⟨28407, by rfl⟩ (by norm_num))
theorem R75757 : Reach 75757 := rs (se 3 (by rfl) ⟨14204, by rfl⟩) (B 28409 (by norm_num) ⟨14204, by rfl⟩ (by norm_num))
theorem R75761 : Reach 75761 := rs (se 2 (by rfl) ⟨28410, by rfl⟩) (B 56821 (by norm_num) ⟨28410, by rfl⟩ (by norm_num))
theorem R75765 : Reach 75765 := rs (se 5 (by rfl) ⟨3551, by rfl⟩) (B 7103 (by norm_num) ⟨3551, by rfl⟩ (by norm_num))
theorem R75769 : Reach 75769 := rs (se 2 (by rfl) ⟨28413, by rfl⟩) (B 56827 (by norm_num) ⟨28413, by rfl⟩ (by norm_num))
theorem R75773 : Reach 75773 := rs (se 3 (by rfl) ⟨14207, by rfl⟩) (B 28415 (by norm_num) ⟨14207, by rfl⟩ (by norm_num))
theorem R174077 : Reach 174077 := rs (se 3 (by rfl) ⟨32639, by rfl⟩) (B 65279 (by norm_num) ⟨32639, by rfl⟩ (by norm_num))
theorem R75777 : Reach 75777 := rs (se 2 (by rfl) ⟨28416, by rfl⟩) (B 56833 (by norm_num) ⟨28416, by rfl⟩ (by norm_num))
theorem R75781 : Reach 75781 := rs (se 4 (by rfl) ⟨7104, by rfl⟩) (B 14209 (by norm_num) ⟨7104, by rfl⟩ (by norm_num))
theorem R75785 : Reach 75785 := rs (se 2 (by rfl) ⟨28419, by rfl⟩) (B 56839 (by norm_num) ⟨28419, by rfl⟩ (by norm_num))
theorem R75789 : Reach 75789 := rs (se 3 (by rfl) ⟨14210, by rfl⟩) (B 28421 (by norm_num) ⟨14210, by rfl⟩ (by norm_num))
theorem R75793 : Reach 75793 := rs (se 2 (by rfl) ⟨28422, by rfl⟩) (B 56845 (by norm_num) ⟨28422, by rfl⟩ (by norm_num))
theorem R75797 : Reach 75797 := rs (se 6 (by rfl) ⟨1776, by rfl⟩) (B 3553 (by norm_num) ⟨1776, by rfl⟩ (by norm_num))
theorem R75801 : Reach 75801 := rs (se 2 (by rfl) ⟨28425, by rfl⟩) (B 56851 (by norm_num) ⟨28425, by rfl⟩ (by norm_num))
theorem R75805 : Reach 75805 := rs (se 3 (by rfl) ⟨14213, by rfl⟩) (B 28427 (by norm_num) ⟨14213, by rfl⟩ (by norm_num))
theorem R75809 : Reach 75809 := rs (se 2 (by rfl) ⟨28428, by rfl⟩) (B 56857 (by norm_num) ⟨28428, by rfl⟩ (by norm_num))
theorem R75813 : Reach 75813 := rs (se 4 (by rfl) ⟨7107, by rfl⟩) (B 14215 (by norm_num) ⟨7107, by rfl⟩ (by norm_num))
theorem R75817 : Reach 75817 := rs (se 2 (by rfl) ⟨28431, by rfl⟩) (B 56863 (by norm_num) ⟨28431, by rfl⟩ (by norm_num))
theorem R75821 : Reach 75821 := rs (se 3 (by rfl) ⟨14216, by rfl⟩) (B 28433 (by norm_num) ⟨14216, by rfl⟩ (by norm_num))
theorem R75825 : Reach 75825 := rs (se 2 (by rfl) ⟨28434, by rfl⟩) (B 56869 (by norm_num) ⟨28434, by rfl⟩ (by norm_num))
theorem R75829 : Reach 75829 := rs (se 5 (by rfl) ⟨3554, by rfl⟩) (B 7109 (by norm_num) ⟨3554, by rfl⟩ (by norm_num))
theorem R75833 : Reach 75833 := rs (se 2 (by rfl) ⟨28437, by rfl⟩) (B 56875 (by norm_num) ⟨28437, by rfl⟩ (by norm_num))
theorem R75837 : Reach 75837 := rs (se 3 (by rfl) ⟨14219, by rfl⟩) (B 28439 (by norm_num) ⟨14219, by rfl⟩ (by norm_num))
theorem R75841 : Reach 75841 := rs (se 2 (by rfl) ⟨28440, by rfl⟩) (B 56881 (by norm_num) ⟨28440, by rfl⟩ (by norm_num))
theorem R75845 : Reach 75845 := rs (se 4 (by rfl) ⟨7110, by rfl⟩) (B 14221 (by norm_num) ⟨7110, by rfl⟩ (by norm_num))
theorem R174149 : Reach 174149 := rs (se 4 (by rfl) ⟨16326, by rfl⟩) (B 32653 (by norm_num) ⟨16326, by rfl⟩ (by norm_num))
theorem R75849 : Reach 75849 := rs (se 2 (by rfl) ⟨28443, by rfl⟩) (B 56887 (by norm_num) ⟨28443, by rfl⟩ (by norm_num))
theorem R75853 : Reach 75853 := rs (se 3 (by rfl) ⟨14222, by rfl⟩) (B 28445 (by norm_num) ⟨14222, by rfl⟩ (by norm_num))
theorem R75857 : Reach 75857 := rs (se 2 (by rfl) ⟨28446, by rfl⟩) (B 56893 (by norm_num) ⟨28446, by rfl⟩ (by norm_num))
theorem R75861 : Reach 75861 := rs (se 8 (by rfl) ⟨444, by rfl⟩) (B 889 (by norm_num) ⟨444, by rfl⟩ (by norm_num))
theorem R75865 : Reach 75865 := rs (se 2 (by rfl) ⟨28449, by rfl⟩) (B 56899 (by norm_num) ⟨28449, by rfl⟩ (by norm_num))
theorem R75869 : Reach 75869 := rs (se 3 (by rfl) ⟨14225, by rfl⟩) (B 28451 (by norm_num) ⟨14225, by rfl⟩ (by norm_num))
theorem R75873 : Reach 75873 := rs (se 2 (by rfl) ⟨28452, by rfl⟩) (B 56905 (by norm_num) ⟨28452, by rfl⟩ (by norm_num))
theorem R75877 : Reach 75877 := rs (se 4 (by rfl) ⟨7113, by rfl⟩) (B 14227 (by norm_num) ⟨7113, by rfl⟩ (by norm_num))
theorem R75881 : Reach 75881 := rs (se 2 (by rfl) ⟨28455, by rfl⟩) (B 56911 (by norm_num) ⟨28455, by rfl⟩ (by norm_num))
theorem R75885 : Reach 75885 := rs (se 3 (by rfl) ⟨14228, by rfl⟩) (B 28457 (by norm_num) ⟨14228, by rfl⟩ (by norm_num))
theorem R75889 : Reach 75889 := rs (se 2 (by rfl) ⟨28458, by rfl⟩) (B 56917 (by norm_num) ⟨28458, by rfl⟩ (by norm_num))
theorem R75893 : Reach 75893 := rs (se 5 (by rfl) ⟨3557, by rfl⟩) (B 7115 (by norm_num) ⟨3557, by rfl⟩ (by norm_num))
theorem R75897 : Reach 75897 := rs (se 2 (by rfl) ⟨28461, by rfl⟩) (B 56923 (by norm_num) ⟨28461, by rfl⟩ (by norm_num))
theorem R75901 : Reach 75901 := rs (se 3 (by rfl) ⟨14231, by rfl⟩) (B 28463 (by norm_num) ⟨14231, by rfl⟩ (by norm_num))
theorem R75905 : Reach 75905 := rs (se 2 (by rfl) ⟨28464, by rfl⟩) (B 56929 (by norm_num) ⟨28464, by rfl⟩ (by norm_num))
theorem R75909 : Reach 75909 := rs (se 4 (by rfl) ⟨7116, by rfl⟩) (B 14233 (by norm_num) ⟨7116, by rfl⟩ (by norm_num))
theorem R75913 : Reach 75913 := rs (se 2 (by rfl) ⟨28467, by rfl⟩) (B 56935 (by norm_num) ⟨28467, by rfl⟩ (by norm_num))
theorem R75917 : Reach 75917 := rs (se 3 (by rfl) ⟨14234, by rfl⟩) (B 28469 (by norm_num) ⟨14234, by rfl⟩ (by norm_num))
theorem R174221 : Reach 174221 := rs (se 3 (by rfl) ⟨32666, by rfl⟩) (B 65333 (by norm_num) ⟨32666, by rfl⟩ (by norm_num))
theorem R75921 : Reach 75921 := rs (se 2 (by rfl) ⟨28470, by rfl⟩) (B 56941 (by norm_num) ⟨28470, by rfl⟩ (by norm_num))
theorem R75925 : Reach 75925 := rs (se 6 (by rfl) ⟨1779, by rfl⟩) (B 3559 (by norm_num) ⟨1779, by rfl⟩ (by norm_num))
theorem R75929 : Reach 75929 := rs (se 2 (by rfl) ⟨28473, by rfl⟩) (B 56947 (by norm_num) ⟨28473, by rfl⟩ (by norm_num))
theorem R75933 : Reach 75933 := rs (se 3 (by rfl) ⟨14237, by rfl⟩) (B 28475 (by norm_num) ⟨14237, by rfl⟩ (by norm_num))
theorem R75937 : Reach 75937 := rs (se 2 (by rfl) ⟨28476, by rfl⟩) (B 56953 (by norm_num) ⟨28476, by rfl⟩ (by norm_num))
theorem R75941 : Reach 75941 := rs (se 4 (by rfl) ⟨7119, by rfl⟩) (B 14239 (by norm_num) ⟨7119, by rfl⟩ (by norm_num))
theorem R75945 : Reach 75945 := rs (se 2 (by rfl) ⟨28479, by rfl⟩) (B 56959 (by norm_num) ⟨28479, by rfl⟩ (by norm_num))
theorem R75949 : Reach 75949 := rs (se 3 (by rfl) ⟨14240, by rfl⟩) (B 28481 (by norm_num) ⟨14240, by rfl⟩ (by norm_num))
theorem R75953 : Reach 75953 := rs (se 2 (by rfl) ⟨28482, by rfl⟩) (B 56965 (by norm_num) ⟨28482, by rfl⟩ (by norm_num))
theorem R75957 : Reach 75957 := rs (se 5 (by rfl) ⟨3560, by rfl⟩) (B 7121 (by norm_num) ⟨3560, by rfl⟩ (by norm_num))
theorem R75961 : Reach 75961 := rs (se 2 (by rfl) ⟨28485, by rfl⟩) (B 56971 (by norm_num) ⟨28485, by rfl⟩ (by norm_num))
theorem R75965 : Reach 75965 := rs (se 3 (by rfl) ⟨14243, by rfl⟩) (B 28487 (by norm_num) ⟨14243, by rfl⟩ (by norm_num))
theorem R75969 : Reach 75969 := rs (se 2 (by rfl) ⟨28488, by rfl⟩) (B 56977 (by norm_num) ⟨28488, by rfl⟩ (by norm_num))
theorem R75973 : Reach 75973 := rs (se 4 (by rfl) ⟨7122, by rfl⟩) (B 14245 (by norm_num) ⟨7122, by rfl⟩ (by norm_num))
theorem R75977 : Reach 75977 := rs (se 2 (by rfl) ⟨28491, by rfl⟩) (B 56983 (by norm_num) ⟨28491, by rfl⟩ (by norm_num))
theorem R75981 : Reach 75981 := rs (se 3 (by rfl) ⟨14246, by rfl⟩) (B 28493 (by norm_num) ⟨14246, by rfl⟩ (by norm_num))
theorem R75985 : Reach 75985 := rs (se 2 (by rfl) ⟨28494, by rfl⟩) (B 56989 (by norm_num) ⟨28494, by rfl⟩ (by norm_num))
theorem R75989 : Reach 75989 := rs (se 7 (by rfl) ⟨890, by rfl⟩) (B 1781 (by norm_num) ⟨890, by rfl⟩ (by norm_num))
theorem R174293 : Reach 174293 := rs (se 7 (by rfl) ⟨2042, by rfl⟩) (B 4085 (by norm_num) ⟨2042, by rfl⟩ (by norm_num))
theorem R75993 : Reach 75993 := rs (se 2 (by rfl) ⟨28497, by rfl⟩) (B 56995 (by norm_num) ⟨28497, by rfl⟩ (by norm_num))
theorem R75997 : Reach 75997 := rs (se 3 (by rfl) ⟨14249, by rfl⟩) (B 28499 (by norm_num) ⟨14249, by rfl⟩ (by norm_num))
theorem R76001 : Reach 76001 := rs (se 2 (by rfl) ⟨28500, by rfl⟩) (B 57001 (by norm_num) ⟨28500, by rfl⟩ (by norm_num))
theorem R76005 : Reach 76005 := rs (se 4 (by rfl) ⟨7125, by rfl⟩) (B 14251 (by norm_num) ⟨7125, by rfl⟩ (by norm_num))
theorem R76009 : Reach 76009 := rs (se 2 (by rfl) ⟨28503, by rfl⟩) (B 57007 (by norm_num) ⟨28503, by rfl⟩ (by norm_num))
theorem R76013 : Reach 76013 := rs (se 3 (by rfl) ⟨14252, by rfl⟩) (B 28505 (by norm_num) ⟨14252, by rfl⟩ (by norm_num))
theorem R76017 : Reach 76017 := rs (se 2 (by rfl) ⟨28506, by rfl⟩) (B 57013 (by norm_num) ⟨28506, by rfl⟩ (by norm_num))
theorem R76021 : Reach 76021 := rs (se 5 (by rfl) ⟨3563, by rfl⟩) (B 7127 (by norm_num) ⟨3563, by rfl⟩ (by norm_num))
theorem R76025 : Reach 76025 := rs (se 2 (by rfl) ⟨28509, by rfl⟩) (B 57019 (by norm_num) ⟨28509, by rfl⟩ (by norm_num))
theorem R76029 : Reach 76029 := rs (se 3 (by rfl) ⟨14255, by rfl⟩) (B 28511 (by norm_num) ⟨14255, by rfl⟩ (by norm_num))
theorem R76033 : Reach 76033 := rs (se 2 (by rfl) ⟨28512, by rfl⟩) (B 57025 (by norm_num) ⟨28512, by rfl⟩ (by norm_num))
theorem R76037 : Reach 76037 := rs (se 4 (by rfl) ⟨7128, by rfl⟩) (B 14257 (by norm_num) ⟨7128, by rfl⟩ (by norm_num))
theorem R76041 : Reach 76041 := rs (se 2 (by rfl) ⟨28515, by rfl⟩) (B 57031 (by norm_num) ⟨28515, by rfl⟩ (by norm_num))
theorem R76045 : Reach 76045 := rs (se 3 (by rfl) ⟨14258, by rfl⟩) (B 28517 (by norm_num) ⟨14258, by rfl⟩ (by norm_num))
theorem R76049 : Reach 76049 := rs (se 2 (by rfl) ⟨28518, by rfl⟩) (B 57037 (by norm_num) ⟨28518, by rfl⟩ (by norm_num))
theorem R76053 : Reach 76053 := rs (se 6 (by rfl) ⟨1782, by rfl⟩) (B 3565 (by norm_num) ⟨1782, by rfl⟩ (by norm_num))
theorem R76057 : Reach 76057 := rs (se 2 (by rfl) ⟨28521, by rfl⟩) (B 57043 (by norm_num) ⟨28521, by rfl⟩ (by norm_num))
theorem R76061 : Reach 76061 := rs (se 3 (by rfl) ⟨14261, by rfl⟩) (B 28523 (by norm_num) ⟨14261, by rfl⟩ (by norm_num))
theorem R174365 : Reach 174365 := rs (se 3 (by rfl) ⟨32693, by rfl⟩) (B 65387 (by norm_num) ⟨32693, by rfl⟩ (by norm_num))
theorem R76065 : Reach 76065 := rs (se 2 (by rfl) ⟨28524, by rfl⟩) (B 57049 (by norm_num) ⟨28524, by rfl⟩ (by norm_num))
theorem R76069 : Reach 76069 := rs (se 4 (by rfl) ⟨7131, by rfl⟩) (B 14263 (by norm_num) ⟨7131, by rfl⟩ (by norm_num))
theorem R76073 : Reach 76073 := rs (se 2 (by rfl) ⟨28527, by rfl⟩) (B 57055 (by norm_num) ⟨28527, by rfl⟩ (by norm_num))
theorem R76077 : Reach 76077 := rs (se 3 (by rfl) ⟨14264, by rfl⟩) (B 28529 (by norm_num) ⟨14264, by rfl⟩ (by norm_num))
theorem R76081 : Reach 76081 := rs (se 2 (by rfl) ⟨28530, by rfl⟩) (B 57061 (by norm_num) ⟨28530, by rfl⟩ (by norm_num))
theorem R76085 : Reach 76085 := rs (se 5 (by rfl) ⟨3566, by rfl⟩) (B 7133 (by norm_num) ⟨3566, by rfl⟩ (by norm_num))
theorem R76089 : Reach 76089 := rs (se 2 (by rfl) ⟨28533, by rfl⟩) (B 57067 (by norm_num) ⟨28533, by rfl⟩ (by norm_num))
theorem R76093 : Reach 76093 := rs (se 3 (by rfl) ⟨14267, by rfl⟩) (B 28535 (by norm_num) ⟨14267, by rfl⟩ (by norm_num))
theorem R76097 : Reach 76097 := rs (se 2 (by rfl) ⟨28536, by rfl⟩) (B 57073 (by norm_num) ⟨28536, by rfl⟩ (by norm_num))
theorem R76101 : Reach 76101 := rs (se 4 (by rfl) ⟨7134, by rfl⟩) (B 14269 (by norm_num) ⟨7134, by rfl⟩ (by norm_num))
theorem R76105 : Reach 76105 := rs (se 2 (by rfl) ⟨28539, by rfl⟩) (B 57079 (by norm_num) ⟨28539, by rfl⟩ (by norm_num))
theorem R76109 : Reach 76109 := rs (se 3 (by rfl) ⟨14270, by rfl⟩) (B 28541 (by norm_num) ⟨14270, by rfl⟩ (by norm_num))
theorem R76113 : Reach 76113 := rs (se 2 (by rfl) ⟨28542, by rfl⟩) (B 57085 (by norm_num) ⟨28542, by rfl⟩ (by norm_num))
theorem R76117 : Reach 76117 := rs (se 10 (by rfl) ⟨111, by rfl⟩) (B 223 (by norm_num) ⟨111, by rfl⟩ (by norm_num))
theorem R665941 : Reach 665941 := rs (se 10 (by rfl) ⟨975, by rfl⟩) (B 1951 (by norm_num) ⟨975, by rfl⟩ (by norm_num))
theorem R76121 : Reach 76121 := rs (se 2 (by rfl) ⟨28545, by rfl⟩) (B 57091 (by norm_num) ⟨28545, by rfl⟩ (by norm_num))
theorem R76125 : Reach 76125 := rs (se 3 (by rfl) ⟨14273, by rfl⟩) (B 28547 (by norm_num) ⟨14273, by rfl⟩ (by norm_num))
theorem R76129 : Reach 76129 := rs (se 2 (by rfl) ⟨28548, by rfl⟩) (B 57097 (by norm_num) ⟨28548, by rfl⟩ (by norm_num))
theorem R76133 : Reach 76133 := rs (se 4 (by rfl) ⟨7137, by rfl⟩) (B 14275 (by norm_num) ⟨7137, by rfl⟩ (by norm_num))
theorem R174437 : Reach 174437 := rs (se 4 (by rfl) ⟨16353, by rfl⟩) (B 32707 (by norm_num) ⟨16353, by rfl⟩ (by norm_num))
theorem R76137 : Reach 76137 := rs (se 2 (by rfl) ⟨28551, by rfl⟩) (B 57103 (by norm_num) ⟨28551, by rfl⟩ (by norm_num))
theorem R76141 : Reach 76141 := rs (se 3 (by rfl) ⟨14276, by rfl⟩) (B 28553 (by norm_num) ⟨14276, by rfl⟩ (by norm_num))
theorem R141677 : Reach 141677 := rs (se 3 (by rfl) ⟨26564, by rfl⟩) (B 53129 (by norm_num) ⟨26564, by rfl⟩ (by norm_num))
theorem R76145 : Reach 76145 := rs (se 2 (by rfl) ⟨28554, by rfl⟩) (B 57109 (by norm_num) ⟨28554, by rfl⟩ (by norm_num))
theorem R76149 : Reach 76149 := rs (se 5 (by rfl) ⟨3569, by rfl⟩) (B 7139 (by norm_num) ⟨3569, by rfl⟩ (by norm_num))
theorem R76153 : Reach 76153 := rs (se 2 (by rfl) ⟨28557, by rfl⟩) (B 57115 (by norm_num) ⟨28557, by rfl⟩ (by norm_num))
theorem R76157 : Reach 76157 := rs (se 3 (by rfl) ⟨14279, by rfl⟩) (B 28559 (by norm_num) ⟨14279, by rfl⟩ (by norm_num))
theorem R76161 : Reach 76161 := rs (se 2 (by rfl) ⟨28560, by rfl⟩) (B 57121 (by norm_num) ⟨28560, by rfl⟩ (by norm_num))
theorem R76165 : Reach 76165 := rs (se 4 (by rfl) ⟨7140, by rfl⟩) (B 14281 (by norm_num) ⟨7140, by rfl⟩ (by norm_num))
theorem R76169 : Reach 76169 := rs (se 2 (by rfl) ⟨28563, by rfl⟩) (B 57127 (by norm_num) ⟨28563, by rfl⟩ (by norm_num))
theorem R76173 : Reach 76173 := rs (se 3 (by rfl) ⟨14282, by rfl⟩) (B 28565 (by norm_num) ⟨14282, by rfl⟩ (by norm_num))
theorem R76177 : Reach 76177 := rs (se 2 (by rfl) ⟨28566, by rfl⟩) (B 57133 (by norm_num) ⟨28566, by rfl⟩ (by norm_num))
theorem R76181 : Reach 76181 := rs (se 6 (by rfl) ⟨1785, by rfl⟩) (B 3571 (by norm_num) ⟨1785, by rfl⟩ (by norm_num))
theorem R76185 : Reach 76185 := rs (se 2 (by rfl) ⟨28569, by rfl⟩) (B 57139 (by norm_num) ⟨28569, by rfl⟩ (by norm_num))
theorem R76189 : Reach 76189 := rs (se 3 (by rfl) ⟨14285, by rfl⟩) (B 28571 (by norm_num) ⟨14285, by rfl⟩ (by norm_num))
theorem R76193 : Reach 76193 := rs (se 2 (by rfl) ⟨28572, by rfl⟩) (B 57145 (by norm_num) ⟨28572, by rfl⟩ (by norm_num))
theorem R76197 : Reach 76197 := rs (se 4 (by rfl) ⟨7143, by rfl⟩) (B 14287 (by norm_num) ⟨7143, by rfl⟩ (by norm_num))
theorem R76201 : Reach 76201 := rs (se 2 (by rfl) ⟨28575, by rfl⟩) (B 57151 (by norm_num) ⟨28575, by rfl⟩ (by norm_num))
theorem R108973 : Reach 108973 := rs (se 3 (by rfl) ⟨20432, by rfl⟩) (B 40865 (by norm_num) ⟨20432, by rfl⟩ (by norm_num))
theorem R76205 : Reach 76205 := rs (se 3 (by rfl) ⟨14288, by rfl⟩) (B 28577 (by norm_num) ⟨14288, by rfl⟩ (by norm_num))
theorem R174509 : Reach 174509 := rs (se 3 (by rfl) ⟨32720, by rfl⟩) (B 65441 (by norm_num) ⟨32720, by rfl⟩ (by norm_num))
theorem R76209 : Reach 76209 := rs (se 2 (by rfl) ⟨28578, by rfl⟩) (B 57157 (by norm_num) ⟨28578, by rfl⟩ (by norm_num))
theorem R76213 : Reach 76213 := rs (se 5 (by rfl) ⟨3572, by rfl⟩) (B 7145 (by norm_num) ⟨3572, by rfl⟩ (by norm_num))
theorem R76217 : Reach 76217 := rs (se 2 (by rfl) ⟨28581, by rfl⟩) (B 57163 (by norm_num) ⟨28581, by rfl⟩ (by norm_num))
theorem R76221 : Reach 76221 := rs (se 3 (by rfl) ⟨14291, by rfl⟩) (B 28583 (by norm_num) ⟨14291, by rfl⟩ (by norm_num))
theorem R76225 : Reach 76225 := rs (se 2 (by rfl) ⟨28584, by rfl⟩) (B 57169 (by norm_num) ⟨28584, by rfl⟩ (by norm_num))
theorem R76229 : Reach 76229 := rs (se 4 (by rfl) ⟨7146, by rfl⟩) (B 14293 (by norm_num) ⟨7146, by rfl⟩ (by norm_num))
theorem R76233 : Reach 76233 := rs (se 2 (by rfl) ⟨28587, by rfl⟩) (B 57175 (by norm_num) ⟨28587, by rfl⟩ (by norm_num))
theorem R76237 : Reach 76237 := rs (se 3 (by rfl) ⟨14294, by rfl⟩) (B 28589 (by norm_num) ⟨14294, by rfl⟩ (by norm_num))
theorem R76241 : Reach 76241 := rs (se 2 (by rfl) ⟨28590, by rfl⟩) (B 57181 (by norm_num) ⟨28590, by rfl⟩ (by norm_num))
theorem R76245 : Reach 76245 := rs (se 7 (by rfl) ⟨893, by rfl⟩) (B 1787 (by norm_num) ⟨893, by rfl⟩ (by norm_num))
theorem R76249 : Reach 76249 := rs (se 2 (by rfl) ⟨28593, by rfl⟩) (B 57187 (by norm_num) ⟨28593, by rfl⟩ (by norm_num))
theorem R76253 : Reach 76253 := rs (se 3 (by rfl) ⟨14297, by rfl⟩) (B 28595 (by norm_num) ⟨14297, by rfl⟩ (by norm_num))
theorem R76257 : Reach 76257 := rs (se 2 (by rfl) ⟨28596, by rfl⟩) (B 57193 (by norm_num) ⟨28596, by rfl⟩ (by norm_num))
theorem R76261 : Reach 76261 := rs (se 4 (by rfl) ⟨7149, by rfl⟩) (B 14299 (by norm_num) ⟨7149, by rfl⟩ (by norm_num))
theorem R76265 : Reach 76265 := rs (se 2 (by rfl) ⟨28599, by rfl⟩) (B 57199 (by norm_num) ⟨28599, by rfl⟩ (by norm_num))
theorem R76269 : Reach 76269 := rs (se 3 (by rfl) ⟨14300, by rfl⟩) (B 28601 (by norm_num) ⟨14300, by rfl⟩ (by norm_num))
theorem R76273 : Reach 76273 := rs (se 2 (by rfl) ⟨28602, by rfl⟩) (B 57205 (by norm_num) ⟨28602, by rfl⟩ (by norm_num))
theorem R76277 : Reach 76277 := rs (se 5 (by rfl) ⟨3575, by rfl⟩) (B 7151 (by norm_num) ⟨3575, by rfl⟩ (by norm_num))
theorem R174581 : Reach 174581 := rs (se 5 (by rfl) ⟨8183, by rfl⟩) (B 16367 (by norm_num) ⟨8183, by rfl⟩ (by norm_num))
theorem R76281 : Reach 76281 := rs (se 2 (by rfl) ⟨28605, by rfl⟩) (B 57211 (by norm_num) ⟨28605, by rfl⟩ (by norm_num))
theorem R76285 : Reach 76285 := rs (se 3 (by rfl) ⟨14303, by rfl⟩) (B 28607 (by norm_num) ⟨14303, by rfl⟩ (by norm_num))
theorem R76289 : Reach 76289 := rs (se 2 (by rfl) ⟨28608, by rfl⟩) (B 57217 (by norm_num) ⟨28608, by rfl⟩ (by norm_num))
theorem R76293 : Reach 76293 := rs (se 4 (by rfl) ⟨7152, by rfl⟩) (B 14305 (by norm_num) ⟨7152, by rfl⟩ (by norm_num))
theorem R76297 : Reach 76297 := rs (se 2 (by rfl) ⟨28611, by rfl⟩) (B 57223 (by norm_num) ⟨28611, by rfl⟩ (by norm_num))
theorem R76301 : Reach 76301 := rs (se 3 (by rfl) ⟨14306, by rfl⟩) (B 28613 (by norm_num) ⟨14306, by rfl⟩ (by norm_num))
theorem R76305 : Reach 76305 := rs (se 2 (by rfl) ⟨28614, by rfl⟩) (B 57229 (by norm_num) ⟨28614, by rfl⟩ (by norm_num))
theorem R76309 : Reach 76309 := rs (se 6 (by rfl) ⟨1788, by rfl⟩) (B 3577 (by norm_num) ⟨1788, by rfl⟩ (by norm_num))
theorem R76313 : Reach 76313 := rs (se 2 (by rfl) ⟨28617, by rfl⟩) (B 57235 (by norm_num) ⟨28617, by rfl⟩ (by norm_num))
theorem R76317 : Reach 76317 := rs (se 3 (by rfl) ⟨14309, by rfl⟩) (B 28619 (by norm_num) ⟨14309, by rfl⟩ (by norm_num))
theorem R76321 : Reach 76321 := rs (se 2 (by rfl) ⟨28620, by rfl⟩) (B 57241 (by norm_num) ⟨28620, by rfl⟩ (by norm_num))
theorem R76325 : Reach 76325 := rs (se 4 (by rfl) ⟨7155, by rfl⟩) (B 14311 (by norm_num) ⟨7155, by rfl⟩ (by norm_num))
theorem R76329 : Reach 76329 := rs (se 2 (by rfl) ⟨28623, by rfl⟩) (B 57247 (by norm_num) ⟨28623, by rfl⟩ (by norm_num))
theorem R76333 : Reach 76333 := rs (se 3 (by rfl) ⟨14312, by rfl⟩) (B 28625 (by norm_num) ⟨14312, by rfl⟩ (by norm_num))
theorem R76337 : Reach 76337 := rs (se 2 (by rfl) ⟨28626, by rfl⟩) (B 57253 (by norm_num) ⟨28626, by rfl⟩ (by norm_num))
theorem R76341 : Reach 76341 := rs (se 5 (by rfl) ⟨3578, by rfl⟩) (B 7157 (by norm_num) ⟨3578, by rfl⟩ (by norm_num))
theorem R76345 : Reach 76345 := rs (se 2 (by rfl) ⟨28629, by rfl⟩) (B 57259 (by norm_num) ⟨28629, by rfl⟩ (by norm_num))
theorem R76349 : Reach 76349 := rs (se 3 (by rfl) ⟨14315, by rfl⟩) (B 28631 (by norm_num) ⟨14315, by rfl⟩ (by norm_num))
theorem R109117 : Reach 109117 := rs (se 3 (by rfl) ⟨20459, by rfl⟩) (B 40919 (by norm_num) ⟨20459, by rfl⟩ (by norm_num))
theorem R174653 : Reach 174653 := rs (se 3 (by rfl) ⟨32747, by rfl⟩) (B 65495 (by norm_num) ⟨32747, by rfl⟩ (by norm_num))
theorem R76353 : Reach 76353 := rs (se 2 (by rfl) ⟨28632, by rfl⟩) (B 57265 (by norm_num) ⟨28632, by rfl⟩ (by norm_num))
theorem R76357 : Reach 76357 := rs (se 4 (by rfl) ⟨7158, by rfl⟩) (B 14317 (by norm_num) ⟨7158, by rfl⟩ (by norm_num))
theorem R76361 : Reach 76361 := rs (se 2 (by rfl) ⟨28635, by rfl⟩) (B 57271 (by norm_num) ⟨28635, by rfl⟩ (by norm_num))
theorem R76365 : Reach 76365 := rs (se 3 (by rfl) ⟨14318, by rfl⟩) (B 28637 (by norm_num) ⟨14318, by rfl⟩ (by norm_num))
theorem R76369 : Reach 76369 := rs (se 2 (by rfl) ⟨28638, by rfl⟩) (B 57277 (by norm_num) ⟨28638, by rfl⟩ (by norm_num))
theorem R76373 : Reach 76373 := rs (se 8 (by rfl) ⟨447, by rfl⟩) (B 895 (by norm_num) ⟨447, by rfl⟩ (by norm_num))
theorem R76377 : Reach 76377 := rs (se 2 (by rfl) ⟨28641, by rfl⟩) (B 57283 (by norm_num) ⟨28641, by rfl⟩ (by norm_num))
theorem R76381 : Reach 76381 := rs (se 3 (by rfl) ⟨14321, by rfl⟩) (B 28643 (by norm_num) ⟨14321, by rfl⟩ (by norm_num))
theorem R76385 : Reach 76385 := rs (se 2 (by rfl) ⟨28644, by rfl⟩) (B 57289 (by norm_num) ⟨28644, by rfl⟩ (by norm_num))
theorem R76389 : Reach 76389 := rs (se 4 (by rfl) ⟨7161, by rfl⟩) (B 14323 (by norm_num) ⟨7161, by rfl⟩ (by norm_num))
theorem R76393 : Reach 76393 := rs (se 2 (by rfl) ⟨28647, by rfl⟩) (B 57295 (by norm_num) ⟨28647, by rfl⟩ (by norm_num))
theorem R76397 : Reach 76397 := rs (se 3 (by rfl) ⟨14324, by rfl⟩) (B 28649 (by norm_num) ⟨14324, by rfl⟩ (by norm_num))
theorem R76401 : Reach 76401 := rs (se 2 (by rfl) ⟨28650, by rfl⟩) (B 57301 (by norm_num) ⟨28650, by rfl⟩ (by norm_num))
theorem R76405 : Reach 76405 := rs (se 5 (by rfl) ⟨3581, by rfl⟩) (B 7163 (by norm_num) ⟨3581, by rfl⟩ (by norm_num))
theorem R436853 : Reach 436853 := rs (se 5 (by rfl) ⟨20477, by rfl⟩) (B 40955 (by norm_num) ⟨20477, by rfl⟩ (by norm_num))
theorem R76409 : Reach 76409 := rs (se 2 (by rfl) ⟨28653, by rfl⟩) (B 57307 (by norm_num) ⟨28653, by rfl⟩ (by norm_num))
theorem R76413 : Reach 76413 := rs (se 3 (by rfl) ⟨14327, by rfl⟩) (B 28655 (by norm_num) ⟨14327, by rfl⟩ (by norm_num))
theorem R76417 : Reach 76417 := rs (se 2 (by rfl) ⟨28656, by rfl⟩) (B 57313 (by norm_num) ⟨28656, by rfl⟩ (by norm_num))
theorem R76421 : Reach 76421 := rs (se 4 (by rfl) ⟨7164, by rfl⟩) (B 14329 (by norm_num) ⟨7164, by rfl⟩ (by norm_num))
theorem R174725 : Reach 174725 := rs (se 4 (by rfl) ⟨16380, by rfl⟩) (B 32761 (by norm_num) ⟨16380, by rfl⟩ (by norm_num))
theorem R76425 : Reach 76425 := rs (se 2 (by rfl) ⟨28659, by rfl⟩) (B 57319 (by norm_num) ⟨28659, by rfl⟩ (by norm_num))
theorem R76429 : Reach 76429 := rs (se 3 (by rfl) ⟨14330, by rfl⟩) (B 28661 (by norm_num) ⟨14330, by rfl⟩ (by norm_num))
theorem R76433 : Reach 76433 := rs (se 2 (by rfl) ⟨28662, by rfl⟩) (B 57325 (by norm_num) ⟨28662, by rfl⟩ (by norm_num))
theorem R305813 : Reach 305813 := rs (se 6 (by rfl) ⟨7167, by rfl⟩) (B 14335 (by norm_num) ⟨7167, by rfl⟩ (by norm_num))
theorem R76437 : Reach 76437 := rs (se 6 (by rfl) ⟨1791, by rfl⟩) (B 3583 (by norm_num) ⟨1791, by rfl⟩ (by norm_num))
theorem R76441 : Reach 76441 := rs (se 2 (by rfl) ⟨28665, by rfl⟩) (B 57331 (by norm_num) ⟨28665, by rfl⟩ (by norm_num))
theorem R76445 : Reach 76445 := rs (se 3 (by rfl) ⟨14333, by rfl⟩) (B 28667 (by norm_num) ⟨14333, by rfl⟩ (by norm_num))
theorem R76449 : Reach 76449 := rs (se 2 (by rfl) ⟨28668, by rfl⟩) (B 57337 (by norm_num) ⟨28668, by rfl⟩ (by norm_num))
theorem R76453 : Reach 76453 := rs (se 4 (by rfl) ⟨7167, by rfl⟩) (B 14335 (by norm_num) ⟨7167, by rfl⟩ (by norm_num))
theorem R76457 : Reach 76457 := rs (se 2 (by rfl) ⟨28671, by rfl⟩) (B 57343 (by norm_num) ⟨28671, by rfl⟩ (by norm_num))
theorem R76461 : Reach 76461 := rs (se 3 (by rfl) ⟨14336, by rfl⟩) (B 28673 (by norm_num) ⟨14336, by rfl⟩ (by norm_num))
theorem R76465 : Reach 76465 := rs (se 2 (by rfl) ⟨28674, by rfl⟩) (B 57349 (by norm_num) ⟨28674, by rfl⟩ (by norm_num))
theorem R76469 : Reach 76469 := rs (se 5 (by rfl) ⟨3584, by rfl⟩) (B 7169 (by norm_num) ⟨3584, by rfl⟩ (by norm_num))
theorem R76473 : Reach 76473 := rs (se 2 (by rfl) ⟨28677, by rfl⟩) (B 57355 (by norm_num) ⟨28677, by rfl⟩ (by norm_num))
theorem R76477 : Reach 76477 := rs (se 3 (by rfl) ⟨14339, by rfl⟩) (B 28679 (by norm_num) ⟨14339, by rfl⟩ (by norm_num))
theorem R76481 : Reach 76481 := rs (se 2 (by rfl) ⟨28680, by rfl⟩) (B 57361 (by norm_num) ⟨28680, by rfl⟩ (by norm_num))
theorem R76485 : Reach 76485 := rs (se 4 (by rfl) ⟨7170, by rfl⟩) (B 14341 (by norm_num) ⟨7170, by rfl⟩ (by norm_num))
theorem R76489 : Reach 76489 := rs (se 2 (by rfl) ⟨28683, by rfl⟩) (B 57367 (by norm_num) ⟨28683, by rfl⟩ (by norm_num))
theorem R76493 : Reach 76493 := rs (se 3 (by rfl) ⟨14342, by rfl⟩) (B 28685 (by norm_num) ⟨14342, by rfl⟩ (by norm_num))
theorem R174797 : Reach 174797 := rs (se 3 (by rfl) ⟨32774, by rfl⟩) (B 65549 (by norm_num) ⟨32774, by rfl⟩ (by norm_num))
theorem R76497 : Reach 76497 := rs (se 2 (by rfl) ⟨28686, by rfl⟩) (B 57373 (by norm_num) ⟨28686, by rfl⟩ (by norm_num))
theorem R76501 : Reach 76501 := rs (se 7 (by rfl) ⟨896, by rfl⟩) (B 1793 (by norm_num) ⟨896, by rfl⟩ (by norm_num))
theorem R76505 : Reach 76505 := rs (se 2 (by rfl) ⟨28689, by rfl⟩) (B 57379 (by norm_num) ⟨28689, by rfl⟩ (by norm_num))
theorem R76509 : Reach 76509 := rs (se 3 (by rfl) ⟨14345, by rfl⟩) (B 28691 (by norm_num) ⟨14345, by rfl⟩ (by norm_num))
theorem R76513 : Reach 76513 := rs (se 2 (by rfl) ⟨28692, by rfl⟩) (B 57385 (by norm_num) ⟨28692, by rfl⟩ (by norm_num))
theorem R76517 : Reach 76517 := rs (se 4 (by rfl) ⟨7173, by rfl⟩) (B 14347 (by norm_num) ⟨7173, by rfl⟩ (by norm_num))
theorem R76521 : Reach 76521 := rs (se 2 (by rfl) ⟨28695, by rfl⟩) (B 57391 (by norm_num) ⟨28695, by rfl⟩ (by norm_num))
theorem R76525 : Reach 76525 := rs (se 3 (by rfl) ⟨14348, by rfl⟩) (B 28697 (by norm_num) ⟨14348, by rfl⟩ (by norm_num))
theorem R76529 : Reach 76529 := rs (se 2 (by rfl) ⟨28698, by rfl⟩) (B 57397 (by norm_num) ⟨28698, by rfl⟩ (by norm_num))
theorem R76533 : Reach 76533 := rs (se 5 (by rfl) ⟨3587, by rfl⟩) (B 7175 (by norm_num) ⟨3587, by rfl⟩ (by norm_num))
theorem R76537 : Reach 76537 := rs (se 2 (by rfl) ⟨28701, by rfl⟩) (B 57403 (by norm_num) ⟨28701, by rfl⟩ (by norm_num))
theorem R76541 : Reach 76541 := rs (se 3 (by rfl) ⟨14351, by rfl⟩) (B 28703 (by norm_num) ⟨14351, by rfl⟩ (by norm_num))
theorem R76545 : Reach 76545 := rs (se 2 (by rfl) ⟨28704, by rfl⟩) (B 57409 (by norm_num) ⟨28704, by rfl⟩ (by norm_num))
theorem R76549 : Reach 76549 := rs (se 4 (by rfl) ⟨7176, by rfl⟩) (B 14353 (by norm_num) ⟨7176, by rfl⟩ (by norm_num))
theorem R76553 : Reach 76553 := rs (se 2 (by rfl) ⟨28707, by rfl⟩) (B 57415 (by norm_num) ⟨28707, by rfl⟩ (by norm_num))
theorem R76557 : Reach 76557 := rs (se 3 (by rfl) ⟨14354, by rfl⟩) (B 28709 (by norm_num) ⟨14354, by rfl⟩ (by norm_num))
theorem R76561 : Reach 76561 := rs (se 2 (by rfl) ⟨28710, by rfl⟩) (B 57421 (by norm_num) ⟨28710, by rfl⟩ (by norm_num))
theorem R76565 : Reach 76565 := rs (se 6 (by rfl) ⟨1794, by rfl⟩) (B 3589 (by norm_num) ⟨1794, by rfl⟩ (by norm_num))
theorem R174869 : Reach 174869 := rs (se 6 (by rfl) ⟨4098, by rfl⟩) (B 8197 (by norm_num) ⟨4098, by rfl⟩ (by norm_num))
theorem R76569 : Reach 76569 := rs (se 2 (by rfl) ⟨28713, by rfl⟩) (B 57427 (by norm_num) ⟨28713, by rfl⟩ (by norm_num))
theorem R76573 : Reach 76573 := rs (se 3 (by rfl) ⟨14357, by rfl⟩) (B 28715 (by norm_num) ⟨14357, by rfl⟩ (by norm_num))
theorem R76577 : Reach 76577 := rs (se 2 (by rfl) ⟨28716, by rfl⟩) (B 57433 (by norm_num) ⟨28716, by rfl⟩ (by norm_num))
theorem R76581 : Reach 76581 := rs (se 4 (by rfl) ⟨7179, by rfl⟩) (B 14359 (by norm_num) ⟨7179, by rfl⟩ (by norm_num))
theorem R76585 : Reach 76585 := rs (se 2 (by rfl) ⟨28719, by rfl⟩) (B 57439 (by norm_num) ⟨28719, by rfl⟩ (by norm_num))
theorem R76589 : Reach 76589 := rs (se 3 (by rfl) ⟨14360, by rfl⟩) (B 28721 (by norm_num) ⟨14360, by rfl⟩ (by norm_num))
theorem R76593 : Reach 76593 := rs (se 2 (by rfl) ⟨28722, by rfl⟩) (B 57445 (by norm_num) ⟨28722, by rfl⟩ (by norm_num))
theorem R76597 : Reach 76597 := rs (se 5 (by rfl) ⟨3590, by rfl⟩) (B 7181 (by norm_num) ⟨3590, by rfl⟩ (by norm_num))
theorem R469813 : Reach 469813 := rs (se 5 (by rfl) ⟨22022, by rfl⟩) (B 44045 (by norm_num) ⟨22022, by rfl⟩ (by norm_num))
theorem R76601 : Reach 76601 := rs (se 2 (by rfl) ⟨28725, by rfl⟩) (B 57451 (by norm_num) ⟨28725, by rfl⟩ (by norm_num))
theorem R76605 : Reach 76605 := rs (se 3 (by rfl) ⟨14363, by rfl⟩) (B 28727 (by norm_num) ⟨14363, by rfl⟩ (by norm_num))
theorem R76609 : Reach 76609 := rs (se 2 (by rfl) ⟨28728, by rfl⟩) (B 57457 (by norm_num) ⟨28728, by rfl⟩ (by norm_num))
theorem R76613 : Reach 76613 := rs (se 4 (by rfl) ⟨7182, by rfl⟩) (B 14365 (by norm_num) ⟨7182, by rfl⟩ (by norm_num))
theorem R76617 : Reach 76617 := rs (se 2 (by rfl) ⟨28731, by rfl⟩) (B 57463 (by norm_num) ⟨28731, by rfl⟩ (by norm_num))
theorem R76621 : Reach 76621 := rs (se 3 (by rfl) ⟨14366, by rfl⟩) (B 28733 (by norm_num) ⟨14366, by rfl⟩ (by norm_num))
theorem R76625 : Reach 76625 := rs (se 2 (by rfl) ⟨28734, by rfl⟩) (B 57469 (by norm_num) ⟨28734, by rfl⟩ (by norm_num))
theorem R76629 : Reach 76629 := rs (se 9 (by rfl) ⟨224, by rfl⟩) (B 449 (by norm_num) ⟨224, by rfl⟩ (by norm_num))
theorem R76633 : Reach 76633 := rs (se 2 (by rfl) ⟨28737, by rfl⟩) (B 57475 (by norm_num) ⟨28737, by rfl⟩ (by norm_num))
theorem R76637 : Reach 76637 := rs (se 3 (by rfl) ⟨14369, by rfl⟩) (B 28739 (by norm_num) ⟨14369, by rfl⟩ (by norm_num))
theorem R174941 : Reach 174941 := rs (se 3 (by rfl) ⟨32801, by rfl⟩) (B 65603 (by norm_num) ⟨32801, by rfl⟩ (by norm_num))
theorem R76641 : Reach 76641 := rs (se 2 (by rfl) ⟨28740, by rfl⟩) (B 57481 (by norm_num) ⟨28740, by rfl⟩ (by norm_num))
theorem R76645 : Reach 76645 := rs (se 4 (by rfl) ⟨7185, by rfl⟩) (B 14371 (by norm_num) ⟨7185, by rfl⟩ (by norm_num))
theorem R76649 : Reach 76649 := rs (se 2 (by rfl) ⟨28743, by rfl⟩) (B 57487 (by norm_num) ⟨28743, by rfl⟩ (by norm_num))
theorem R76653 : Reach 76653 := rs (se 3 (by rfl) ⟨14372, by rfl⟩) (B 28745 (by norm_num) ⟨14372, by rfl⟩ (by norm_num))
theorem R76657 : Reach 76657 := rs (se 2 (by rfl) ⟨28746, by rfl⟩) (B 57493 (by norm_num) ⟨28746, by rfl⟩ (by norm_num))
theorem R76661 : Reach 76661 := rs (se 5 (by rfl) ⟨3593, by rfl⟩) (B 7187 (by norm_num) ⟨3593, by rfl⟩ (by norm_num))
theorem R76665 : Reach 76665 := rs (se 2 (by rfl) ⟨28749, by rfl⟩) (B 57499 (by norm_num) ⟨28749, by rfl⟩ (by norm_num))
theorem R76669 : Reach 76669 := rs (se 3 (by rfl) ⟨14375, by rfl⟩) (B 28751 (by norm_num) ⟨14375, by rfl⟩ (by norm_num))
theorem R76673 : Reach 76673 := rs (se 2 (by rfl) ⟨28752, by rfl⟩) (B 57505 (by norm_num) ⟨28752, by rfl⟩ (by norm_num))
theorem R76677 : Reach 76677 := rs (se 4 (by rfl) ⟨7188, by rfl⟩) (B 14377 (by norm_num) ⟨7188, by rfl⟩ (by norm_num))
theorem R76681 : Reach 76681 := rs (se 2 (by rfl) ⟨28755, by rfl⟩) (B 57511 (by norm_num) ⟨28755, by rfl⟩ (by norm_num))
theorem R76685 : Reach 76685 := rs (se 3 (by rfl) ⟨14378, by rfl⟩) (B 28757 (by norm_num) ⟨14378, by rfl⟩ (by norm_num))
theorem R109453 : Reach 109453 := rs (se 3 (by rfl) ⟨20522, by rfl⟩) (B 41045 (by norm_num) ⟨20522, by rfl⟩ (by norm_num))
theorem R76689 : Reach 76689 := rs (se 2 (by rfl) ⟨28758, by rfl⟩) (B 57517 (by norm_num) ⟨28758, by rfl⟩ (by norm_num))
theorem R76693 : Reach 76693 := rs (se 6 (by rfl) ⟨1797, by rfl⟩) (B 3595 (by norm_num) ⟨1797, by rfl⟩ (by norm_num))
theorem R76697 : Reach 76697 := rs (se 2 (by rfl) ⟨28761, by rfl⟩) (B 57523 (by norm_num) ⟨28761, by rfl⟩ (by norm_num))
theorem R76701 : Reach 76701 := rs (se 3 (by rfl) ⟨14381, by rfl⟩) (B 28763 (by norm_num) ⟨14381, by rfl⟩ (by norm_num))
theorem R76705 : Reach 76705 := rs (se 2 (by rfl) ⟨28764, by rfl⟩) (B 57529 (by norm_num) ⟨28764, by rfl⟩ (by norm_num))
theorem R76709 : Reach 76709 := rs (se 4 (by rfl) ⟨7191, by rfl⟩) (B 14383 (by norm_num) ⟨7191, by rfl⟩ (by norm_num))
theorem R175013 : Reach 175013 := rs (se 4 (by rfl) ⟨16407, by rfl⟩) (B 32815 (by norm_num) ⟨16407, by rfl⟩ (by norm_num))
theorem R76713 : Reach 76713 := rs (se 2 (by rfl) ⟨28767, by rfl⟩) (B 57535 (by norm_num) ⟨28767, by rfl⟩ (by norm_num))
theorem R76717 : Reach 76717 := rs (se 3 (by rfl) ⟨14384, by rfl⟩) (B 28769 (by norm_num) ⟨14384, by rfl⟩ (by norm_num))
theorem R76721 : Reach 76721 := rs (se 2 (by rfl) ⟨28770, by rfl⟩) (B 57541 (by norm_num) ⟨28770, by rfl⟩ (by norm_num))
theorem R76725 : Reach 76725 := rs (se 5 (by rfl) ⟨3596, by rfl⟩) (B 7193 (by norm_num) ⟨3596, by rfl⟩ (by norm_num))
theorem R76729 : Reach 76729 := rs (se 2 (by rfl) ⟨28773, by rfl⟩) (B 57547 (by norm_num) ⟨28773, by rfl⟩ (by norm_num))
theorem R76733 : Reach 76733 := rs (se 3 (by rfl) ⟨14387, by rfl⟩) (B 28775 (by norm_num) ⟨14387, by rfl⟩ (by norm_num))
theorem R76737 : Reach 76737 := rs (se 2 (by rfl) ⟨28776, by rfl⟩) (B 57553 (by norm_num) ⟨28776, by rfl⟩ (by norm_num))
theorem R76741 : Reach 76741 := rs (se 4 (by rfl) ⟨7194, by rfl⟩) (B 14389 (by norm_num) ⟨7194, by rfl⟩ (by norm_num))
theorem R76745 : Reach 76745 := rs (se 2 (by rfl) ⟨28779, by rfl⟩) (B 57559 (by norm_num) ⟨28779, by rfl⟩ (by norm_num))
theorem R76749 : Reach 76749 := rs (se 3 (by rfl) ⟨14390, by rfl⟩) (B 28781 (by norm_num) ⟨14390, by rfl⟩ (by norm_num))
theorem R76753 : Reach 76753 := rs (se 2 (by rfl) ⟨28782, by rfl⟩) (B 57565 (by norm_num) ⟨28782, by rfl⟩ (by norm_num))
theorem R273365 : Reach 273365 := rs (se 7 (by rfl) ⟨3203, by rfl⟩) (B 6407 (by norm_num) ⟨3203, by rfl⟩ (by norm_num))
theorem R76757 : Reach 76757 := rs (se 7 (by rfl) ⟨899, by rfl⟩) (B 1799 (by norm_num) ⟨899, by rfl⟩ (by norm_num))
theorem R76761 : Reach 76761 := rs (se 2 (by rfl) ⟨28785, by rfl⟩) (B 57571 (by norm_num) ⟨28785, by rfl⟩ (by norm_num))
theorem R76765 : Reach 76765 := rs (se 3 (by rfl) ⟨14393, by rfl⟩) (B 28787 (by norm_num) ⟨14393, by rfl⟩ (by norm_num))
theorem R76769 : Reach 76769 := rs (se 2 (by rfl) ⟨28788, by rfl⟩) (B 57577 (by norm_num) ⟨28788, by rfl⟩ (by norm_num))
theorem R76773 : Reach 76773 := rs (se 4 (by rfl) ⟨7197, by rfl⟩) (B 14395 (by norm_num) ⟨7197, by rfl⟩ (by norm_num))
theorem R76777 : Reach 76777 := rs (se 2 (by rfl) ⟨28791, by rfl⟩) (B 57583 (by norm_num) ⟨28791, by rfl⟩ (by norm_num))
theorem R76781 : Reach 76781 := rs (se 3 (by rfl) ⟨14396, by rfl⟩) (B 28793 (by norm_num) ⟨14396, by rfl⟩ (by norm_num))
theorem R175085 : Reach 175085 := rs (se 3 (by rfl) ⟨32828, by rfl⟩) (B 65657 (by norm_num) ⟨32828, by rfl⟩ (by norm_num))
theorem R76785 : Reach 76785 := rs (se 2 (by rfl) ⟨28794, by rfl⟩) (B 57589 (by norm_num) ⟨28794, by rfl⟩ (by norm_num))
theorem R76789 : Reach 76789 := rs (se 5 (by rfl) ⟨3599, by rfl⟩) (B 7199 (by norm_num) ⟨3599, by rfl⟩ (by norm_num))
theorem R76793 : Reach 76793 := rs (se 2 (by rfl) ⟨28797, by rfl⟩) (B 57595 (by norm_num) ⟨28797, by rfl⟩ (by norm_num))
theorem R76797 : Reach 76797 := rs (se 3 (by rfl) ⟨14399, by rfl⟩) (B 28799 (by norm_num) ⟨14399, by rfl⟩ (by norm_num))
theorem R76801 : Reach 76801 := rs (se 2 (by rfl) ⟨28800, by rfl⟩) (B 57601 (by norm_num) ⟨28800, by rfl⟩ (by norm_num))
theorem R76805 : Reach 76805 := rs (se 4 (by rfl) ⟨7200, by rfl⟩) (B 14401 (by norm_num) ⟨7200, by rfl⟩ (by norm_num))
theorem R76809 : Reach 76809 := rs (se 2 (by rfl) ⟨28803, by rfl⟩) (B 57607 (by norm_num) ⟨28803, by rfl⟩ (by norm_num))
theorem R76813 : Reach 76813 := rs (se 3 (by rfl) ⟨14402, by rfl⟩) (B 28805 (by norm_num) ⟨14402, by rfl⟩ (by norm_num))
theorem R76817 : Reach 76817 := rs (se 2 (by rfl) ⟨28806, by rfl⟩) (B 57613 (by norm_num) ⟨28806, by rfl⟩ (by norm_num))
theorem R76821 : Reach 76821 := rs (se 6 (by rfl) ⟨1800, by rfl⟩) (B 3601 (by norm_num) ⟨1800, by rfl⟩ (by norm_num))
theorem R76825 : Reach 76825 := rs (se 2 (by rfl) ⟨28809, by rfl⟩) (B 57619 (by norm_num) ⟨28809, by rfl⟩ (by norm_num))
theorem R76829 : Reach 76829 := rs (se 3 (by rfl) ⟨14405, by rfl⟩) (B 28811 (by norm_num) ⟨14405, by rfl⟩ (by norm_num))
theorem R76833 : Reach 76833 := rs (se 2 (by rfl) ⟨28812, by rfl⟩) (B 57625 (by norm_num) ⟨28812, by rfl⟩ (by norm_num))
theorem R76837 : Reach 76837 := rs (se 4 (by rfl) ⟨7203, by rfl⟩) (B 14407 (by norm_num) ⟨7203, by rfl⟩ (by norm_num))
theorem R371749 : Reach 371749 := rs (se 4 (by rfl) ⟨34851, by rfl⟩) (B 69703 (by norm_num) ⟨34851, by rfl⟩ (by norm_num))
theorem R76841 : Reach 76841 := rs (se 2 (by rfl) ⟨28815, by rfl⟩) (B 57631 (by norm_num) ⟨28815, by rfl⟩ (by norm_num))
theorem R76845 : Reach 76845 := rs (se 3 (by rfl) ⟨14408, by rfl⟩) (B 28817 (by norm_num) ⟨14408, by rfl⟩ (by norm_num))
theorem R76849 : Reach 76849 := rs (se 2 (by rfl) ⟨28818, by rfl⟩) (B 57637 (by norm_num) ⟨28818, by rfl⟩ (by norm_num))
theorem R76853 : Reach 76853 := rs (se 5 (by rfl) ⟨3602, by rfl⟩) (B 7205 (by norm_num) ⟨3602, by rfl⟩ (by norm_num))
theorem R175157 : Reach 175157 := rs (se 5 (by rfl) ⟨8210, by rfl⟩) (B 16421 (by norm_num) ⟨8210, by rfl⟩ (by norm_num))
theorem R76857 : Reach 76857 := rs (se 2 (by rfl) ⟨28821, by rfl⟩) (B 57643 (by norm_num) ⟨28821, by rfl⟩ (by norm_num))
theorem R76861 : Reach 76861 := rs (se 3 (by rfl) ⟨14411, by rfl⟩) (B 28823 (by norm_num) ⟨14411, by rfl⟩ (by norm_num))
theorem R76865 : Reach 76865 := rs (se 2 (by rfl) ⟨28824, by rfl⟩) (B 57649 (by norm_num) ⟨28824, by rfl⟩ (by norm_num))
theorem R76869 : Reach 76869 := rs (se 4 (by rfl) ⟨7206, by rfl⟩) (B 14413 (by norm_num) ⟨7206, by rfl⟩ (by norm_num))
theorem R76873 : Reach 76873 := rs (se 2 (by rfl) ⟨28827, by rfl⟩) (B 57655 (by norm_num) ⟨28827, by rfl⟩ (by norm_num))
theorem R76877 : Reach 76877 := rs (se 3 (by rfl) ⟨14414, by rfl⟩) (B 28829 (by norm_num) ⟨14414, by rfl⟩ (by norm_num))
theorem R76881 : Reach 76881 := rs (se 2 (by rfl) ⟨28830, by rfl⟩) (B 57661 (by norm_num) ⟨28830, by rfl⟩ (by norm_num))
theorem R76885 : Reach 76885 := rs (se 8 (by rfl) ⟨450, by rfl⟩) (B 901 (by norm_num) ⟨450, by rfl⟩ (by norm_num))
theorem R76889 : Reach 76889 := rs (se 2 (by rfl) ⟨28833, by rfl⟩) (B 57667 (by norm_num) ⟨28833, by rfl⟩ (by norm_num))
theorem R76893 : Reach 76893 := rs (se 3 (by rfl) ⟨14417, by rfl⟩) (B 28835 (by norm_num) ⟨14417, by rfl⟩ (by norm_num))
theorem R76897 : Reach 76897 := rs (se 2 (by rfl) ⟨28836, by rfl⟩) (B 57673 (by norm_num) ⟨28836, by rfl⟩ (by norm_num))
theorem R207973 : Reach 207973 := rs (se 4 (by rfl) ⟨19497, by rfl⟩) (B 38995 (by norm_num) ⟨19497, by rfl⟩ (by norm_num))
theorem R76901 : Reach 76901 := rs (se 4 (by rfl) ⟨7209, by rfl⟩) (B 14419 (by norm_num) ⟨7209, by rfl⟩ (by norm_num))
theorem R109669 : Reach 109669 := rs (se 4 (by rfl) ⟨10281, by rfl⟩) (B 20563 (by norm_num) ⟨10281, by rfl⟩ (by norm_num))
theorem R76905 : Reach 76905 := rs (se 2 (by rfl) ⟨28839, by rfl⟩) (B 57679 (by norm_num) ⟨28839, by rfl⟩ (by norm_num))
theorem R76909 : Reach 76909 := rs (se 3 (by rfl) ⟨14420, by rfl⟩) (B 28841 (by norm_num) ⟨14420, by rfl⟩ (by norm_num))
theorem R76913 : Reach 76913 := rs (se 2 (by rfl) ⟨28842, by rfl⟩) (B 57685 (by norm_num) ⟨28842, by rfl⟩ (by norm_num))
theorem R76917 : Reach 76917 := rs (se 5 (by rfl) ⟨3605, by rfl⟩) (B 7211 (by norm_num) ⟨3605, by rfl⟩ (by norm_num))
theorem R76921 : Reach 76921 := rs (se 2 (by rfl) ⟨28845, by rfl⟩) (B 57691 (by norm_num) ⟨28845, by rfl⟩ (by norm_num))
theorem R76925 : Reach 76925 := rs (se 3 (by rfl) ⟨14423, by rfl⟩) (B 28847 (by norm_num) ⟨14423, by rfl⟩ (by norm_num))
theorem R175229 : Reach 175229 := rs (se 3 (by rfl) ⟨32855, by rfl⟩) (B 65711 (by norm_num) ⟨32855, by rfl⟩ (by norm_num))
theorem R76929 : Reach 76929 := rs (se 2 (by rfl) ⟨28848, by rfl⟩) (B 57697 (by norm_num) ⟨28848, by rfl⟩ (by norm_num))
theorem R76933 : Reach 76933 := rs (se 4 (by rfl) ⟨7212, by rfl⟩) (B 14425 (by norm_num) ⟨7212, by rfl⟩ (by norm_num))
theorem R76937 : Reach 76937 := rs (se 2 (by rfl) ⟨28851, by rfl⟩) (B 57703 (by norm_num) ⟨28851, by rfl⟩ (by norm_num))
theorem R76941 : Reach 76941 := rs (se 3 (by rfl) ⟨14426, by rfl⟩) (B 28853 (by norm_num) ⟨14426, by rfl⟩ (by norm_num))
theorem R76945 : Reach 76945 := rs (se 2 (by rfl) ⟨28854, by rfl⟩) (B 57709 (by norm_num) ⟨28854, by rfl⟩ (by norm_num))
theorem R76949 : Reach 76949 := rs (se 6 (by rfl) ⟨1803, by rfl⟩) (B 3607 (by norm_num) ⟨1803, by rfl⟩ (by norm_num))
theorem R76953 : Reach 76953 := rs (se 2 (by rfl) ⟨28857, by rfl⟩) (B 57715 (by norm_num) ⟨28857, by rfl⟩ (by norm_num))
theorem R76957 : Reach 76957 := rs (se 3 (by rfl) ⟨14429, by rfl⟩) (B 28859 (by norm_num) ⟨14429, by rfl⟩ (by norm_num))
theorem R76961 : Reach 76961 := rs (se 2 (by rfl) ⟨28860, by rfl⟩) (B 57721 (by norm_num) ⟨28860, by rfl⟩ (by norm_num))
theorem R339109 : Reach 339109 := rs (se 4 (by rfl) ⟨31791, by rfl⟩) (B 63583 (by norm_num) ⟨31791, by rfl⟩ (by norm_num))
theorem R76965 : Reach 76965 := rs (se 4 (by rfl) ⟨7215, by rfl⟩) (B 14431 (by norm_num) ⟨7215, by rfl⟩ (by norm_num))
theorem R76969 : Reach 76969 := rs (se 2 (by rfl) ⟨28863, by rfl⟩) (B 57727 (by norm_num) ⟨28863, by rfl⟩ (by norm_num))
theorem R76973 : Reach 76973 := rs (se 3 (by rfl) ⟨14432, by rfl⟩) (B 28865 (by norm_num) ⟨14432, by rfl⟩ (by norm_num))
theorem R76977 : Reach 76977 := rs (se 2 (by rfl) ⟨28866, by rfl⟩) (B 57733 (by norm_num) ⟨28866, by rfl⟩ (by norm_num))
theorem R76981 : Reach 76981 := rs (se 5 (by rfl) ⟨3608, by rfl⟩) (B 7217 (by norm_num) ⟨3608, by rfl⟩ (by norm_num))
theorem R76985 : Reach 76985 := rs (se 2 (by rfl) ⟨28869, by rfl⟩) (B 57739 (by norm_num) ⟨28869, by rfl⟩ (by norm_num))
theorem R76989 : Reach 76989 := rs (se 3 (by rfl) ⟨14435, by rfl⟩) (B 28871 (by norm_num) ⟨14435, by rfl⟩ (by norm_num))
theorem R76993 : Reach 76993 := rs (se 2 (by rfl) ⟨28872, by rfl⟩) (B 57745 (by norm_num) ⟨28872, by rfl⟩ (by norm_num))
theorem R76997 : Reach 76997 := rs (se 4 (by rfl) ⟨7218, by rfl⟩) (B 14437 (by norm_num) ⟨7218, by rfl⟩ (by norm_num))
theorem R175301 : Reach 175301 := rs (se 4 (by rfl) ⟨16434, by rfl⟩) (B 32869 (by norm_num) ⟨16434, by rfl⟩ (by norm_num))
theorem R77001 : Reach 77001 := rs (se 2 (by rfl) ⟨28875, by rfl⟩) (B 57751 (by norm_num) ⟨28875, by rfl⟩ (by norm_num))
theorem R77005 : Reach 77005 := rs (se 3 (by rfl) ⟨14438, by rfl⟩) (B 28877 (by norm_num) ⟨14438, by rfl⟩ (by norm_num))
theorem R77009 : Reach 77009 := rs (se 2 (by rfl) ⟨28878, by rfl⟩) (B 57757 (by norm_num) ⟨28878, by rfl⟩ (by norm_num))
theorem R77013 : Reach 77013 := rs (se 7 (by rfl) ⟨902, by rfl⟩) (B 1805 (by norm_num) ⟨902, by rfl⟩ (by norm_num))
theorem R77017 : Reach 77017 := rs (se 2 (by rfl) ⟨28881, by rfl⟩) (B 57763 (by norm_num) ⟨28881, by rfl⟩ (by norm_num))
theorem R77021 : Reach 77021 := rs (se 3 (by rfl) ⟨14441, by rfl⟩) (B 28883 (by norm_num) ⟨14441, by rfl⟩ (by norm_num))
theorem R77025 : Reach 77025 := rs (se 2 (by rfl) ⟨28884, by rfl⟩) (B 57769 (by norm_num) ⟨28884, by rfl⟩ (by norm_num))
theorem R77029 : Reach 77029 := rs (se 4 (by rfl) ⟨7221, by rfl⟩) (B 14443 (by norm_num) ⟨7221, by rfl⟩ (by norm_num))
theorem R77033 : Reach 77033 := rs (se 2 (by rfl) ⟨28887, by rfl⟩) (B 57775 (by norm_num) ⟨28887, by rfl⟩ (by norm_num))
theorem R77037 : Reach 77037 := rs (se 3 (by rfl) ⟨14444, by rfl⟩) (B 28889 (by norm_num) ⟨14444, by rfl⟩ (by norm_num))
theorem R77041 : Reach 77041 := rs (se 2 (by rfl) ⟨28890, by rfl⟩) (B 57781 (by norm_num) ⟨28890, by rfl⟩ (by norm_num))
theorem R77045 : Reach 77045 := rs (se 5 (by rfl) ⟨3611, by rfl⟩) (B 7223 (by norm_num) ⟨3611, by rfl⟩ (by norm_num))
theorem R77049 : Reach 77049 := rs (se 2 (by rfl) ⟨28893, by rfl⟩) (B 57787 (by norm_num) ⟨28893, by rfl⟩ (by norm_num))
theorem R77053 : Reach 77053 := rs (se 3 (by rfl) ⟨14447, by rfl⟩) (B 28895 (by norm_num) ⟨14447, by rfl⟩ (by norm_num))
theorem R77057 : Reach 77057 := rs (se 2 (by rfl) ⟨28896, by rfl⟩) (B 57793 (by norm_num) ⟨28896, by rfl⟩ (by norm_num))
theorem R77061 : Reach 77061 := rs (se 4 (by rfl) ⟨7224, by rfl⟩) (B 14449 (by norm_num) ⟨7224, by rfl⟩ (by norm_num))
theorem R77065 : Reach 77065 := rs (se 2 (by rfl) ⟨28899, by rfl⟩) (B 57799 (by norm_num) ⟨28899, by rfl⟩ (by norm_num))
theorem R77069 : Reach 77069 := rs (se 3 (by rfl) ⟨14450, by rfl⟩) (B 28901 (by norm_num) ⟨14450, by rfl⟩ (by norm_num))
theorem R175373 : Reach 175373 := rs (se 3 (by rfl) ⟨32882, by rfl⟩) (B 65765 (by norm_num) ⟨32882, by rfl⟩ (by norm_num))
theorem R77073 : Reach 77073 := rs (se 2 (by rfl) ⟨28902, by rfl⟩) (B 57805 (by norm_num) ⟨28902, by rfl⟩ (by norm_num))
theorem R77077 : Reach 77077 := rs (se 6 (by rfl) ⟨1806, by rfl⟩) (B 3613 (by norm_num) ⟨1806, by rfl⟩ (by norm_num))
theorem R77081 : Reach 77081 := rs (se 2 (by rfl) ⟨28905, by rfl⟩) (B 57811 (by norm_num) ⟨28905, by rfl⟩ (by norm_num))
theorem R77085 : Reach 77085 := rs (se 3 (by rfl) ⟨14453, by rfl⟩) (B 28907 (by norm_num) ⟨14453, by rfl⟩ (by norm_num))
theorem R77089 : Reach 77089 := rs (se 2 (by rfl) ⟨28908, by rfl⟩) (B 57817 (by norm_num) ⟨28908, by rfl⟩ (by norm_num))
theorem R77093 : Reach 77093 := rs (se 4 (by rfl) ⟨7227, by rfl⟩) (B 14455 (by norm_num) ⟨7227, by rfl⟩ (by norm_num))
theorem R77097 : Reach 77097 := rs (se 2 (by rfl) ⟨28911, by rfl⟩) (B 57823 (by norm_num) ⟨28911, by rfl⟩ (by norm_num))
theorem R77101 : Reach 77101 := rs (se 3 (by rfl) ⟨14456, by rfl⟩) (B 28913 (by norm_num) ⟨14456, by rfl⟩ (by norm_num))
theorem R77105 : Reach 77105 := rs (se 2 (by rfl) ⟨28914, by rfl⟩) (B 57829 (by norm_num) ⟨28914, by rfl⟩ (by norm_num))
theorem R77109 : Reach 77109 := rs (se 5 (by rfl) ⟨3614, by rfl⟩) (B 7229 (by norm_num) ⟨3614, by rfl⟩ (by norm_num))
theorem R77113 : Reach 77113 := rs (se 2 (by rfl) ⟨28917, by rfl⟩) (B 57835 (by norm_num) ⟨28917, by rfl⟩ (by norm_num))
theorem R77117 : Reach 77117 := rs (se 3 (by rfl) ⟨14459, by rfl⟩) (B 28919 (by norm_num) ⟨14459, by rfl⟩ (by norm_num))
theorem R77121 : Reach 77121 := rs (se 2 (by rfl) ⟨28920, by rfl⟩) (B 57841 (by norm_num) ⟨28920, by rfl⟩ (by norm_num))
theorem R240965 : Reach 240965 := rs (se 4 (by rfl) ⟨22590, by rfl⟩) (B 45181 (by norm_num) ⟨22590, by rfl⟩ (by norm_num))
theorem R77125 : Reach 77125 := rs (se 4 (by rfl) ⟨7230, by rfl⟩) (B 14461 (by norm_num) ⟨7230, by rfl⟩ (by norm_num))
theorem R77129 : Reach 77129 := rs (se 2 (by rfl) ⟨28923, by rfl⟩) (B 57847 (by norm_num) ⟨28923, by rfl⟩ (by norm_num))
theorem R77133 : Reach 77133 := rs (se 3 (by rfl) ⟨14462, by rfl⟩) (B 28925 (by norm_num) ⟨14462, by rfl⟩ (by norm_num))
theorem R77137 : Reach 77137 := rs (se 2 (by rfl) ⟨28926, by rfl⟩) (B 57853 (by norm_num) ⟨28926, by rfl⟩ (by norm_num))
theorem R77141 : Reach 77141 := rs (se 11 (by rfl) ⟨56, by rfl⟩) (B 113 (by norm_num) ⟨56, by rfl⟩ (by norm_num))
theorem R175445 : Reach 175445 := rs (se 11 (by rfl) ⟨128, by rfl⟩) (B 257 (by norm_num) ⟨128, by rfl⟩ (by norm_num))
theorem R77145 : Reach 77145 := rs (se 2 (by rfl) ⟨28929, by rfl⟩) (B 57859 (by norm_num) ⟨28929, by rfl⟩ (by norm_num))
theorem R77149 : Reach 77149 := rs (se 3 (by rfl) ⟨14465, by rfl⟩) (B 28931 (by norm_num) ⟨14465, by rfl⟩ (by norm_num))
theorem R77153 : Reach 77153 := rs (se 2 (by rfl) ⟨28932, by rfl⟩) (B 57865 (by norm_num) ⟨28932, by rfl⟩ (by norm_num))
theorem R77157 : Reach 77157 := rs (se 4 (by rfl) ⟨7233, by rfl⟩) (B 14467 (by norm_num) ⟨7233, by rfl⟩ (by norm_num))
theorem R77161 : Reach 77161 := rs (se 2 (by rfl) ⟨28935, by rfl⟩) (B 57871 (by norm_num) ⟨28935, by rfl⟩ (by norm_num))
theorem R77165 : Reach 77165 := rs (se 3 (by rfl) ⟨14468, by rfl⟩) (B 28937 (by norm_num) ⟨14468, by rfl⟩ (by norm_num))
theorem R77169 : Reach 77169 := rs (se 2 (by rfl) ⟨28938, by rfl⟩) (B 57877 (by norm_num) ⟨28938, by rfl⟩ (by norm_num))
theorem R77173 : Reach 77173 := rs (se 5 (by rfl) ⟨3617, by rfl⟩) (B 7235 (by norm_num) ⟨3617, by rfl⟩ (by norm_num))
theorem R77177 : Reach 77177 := rs (se 2 (by rfl) ⟨28941, by rfl⟩) (B 57883 (by norm_num) ⟨28941, by rfl⟩ (by norm_num))
theorem R142717 : Reach 142717 := rs (se 3 (by rfl) ⟨26759, by rfl⟩) (B 53519 (by norm_num) ⟨26759, by rfl⟩ (by norm_num))
theorem R77181 : Reach 77181 := rs (se 3 (by rfl) ⟨14471, by rfl⟩) (B 28943 (by norm_num) ⟨14471, by rfl⟩ (by norm_num))
theorem R77185 : Reach 77185 := rs (se 2 (by rfl) ⟨28944, by rfl⟩) (B 57889 (by norm_num) ⟨28944, by rfl⟩ (by norm_num))
theorem R77189 : Reach 77189 := rs (se 4 (by rfl) ⟨7236, by rfl⟩) (B 14473 (by norm_num) ⟨7236, by rfl⟩ (by norm_num))
theorem R77193 : Reach 77193 := rs (se 2 (by rfl) ⟨28947, by rfl⟩) (B 57895 (by norm_num) ⟨28947, by rfl⟩ (by norm_num))
theorem R77197 : Reach 77197 := rs (se 3 (by rfl) ⟨14474, by rfl⟩) (B 28949 (by norm_num) ⟨14474, by rfl⟩ (by norm_num))
theorem R77201 : Reach 77201 := rs (se 2 (by rfl) ⟨28950, by rfl⟩) (B 57901 (by norm_num) ⟨28950, by rfl⟩ (by norm_num))
theorem R77205 : Reach 77205 := rs (se 6 (by rfl) ⟨1809, by rfl⟩) (B 3619 (by norm_num) ⟨1809, by rfl⟩ (by norm_num))
theorem R77209 : Reach 77209 := rs (se 2 (by rfl) ⟨28953, by rfl⟩) (B 57907 (by norm_num) ⟨28953, by rfl⟩ (by norm_num))
theorem R175517 : Reach 175517 := rs (se 3 (by rfl) ⟨32909, by rfl⟩) (B 65819 (by norm_num) ⟨32909, by rfl⟩ (by norm_num))
theorem R77213 : Reach 77213 := rs (se 3 (by rfl) ⟨14477, by rfl⟩) (B 28955 (by norm_num) ⟨14477, by rfl⟩ (by norm_num))
theorem R77217 : Reach 77217 := rs (se 2 (by rfl) ⟨28956, by rfl⟩) (B 57913 (by norm_num) ⟨28956, by rfl⟩ (by norm_num))
theorem R77221 : Reach 77221 := rs (se 4 (by rfl) ⟨7239, by rfl⟩) (B 14479 (by norm_num) ⟨7239, by rfl⟩ (by norm_num))
theorem R77225 : Reach 77225 := rs (se 2 (by rfl) ⟨28959, by rfl⟩) (B 57919 (by norm_num) ⟨28959, by rfl⟩ (by norm_num))
theorem R77229 : Reach 77229 := rs (se 3 (by rfl) ⟨14480, by rfl⟩) (B 28961 (by norm_num) ⟨14480, by rfl⟩ (by norm_num))
theorem R77233 : Reach 77233 := rs (se 2 (by rfl) ⟨28962, by rfl⟩) (B 57925 (by norm_num) ⟨28962, by rfl⟩ (by norm_num))
theorem R77237 : Reach 77237 := rs (se 5 (by rfl) ⟨3620, by rfl⟩) (B 7241 (by norm_num) ⟨3620, by rfl⟩ (by norm_num))
theorem R77241 : Reach 77241 := rs (se 2 (by rfl) ⟨28965, by rfl⟩) (B 57931 (by norm_num) ⟨28965, by rfl⟩ (by norm_num))
theorem R77245 : Reach 77245 := rs (se 3 (by rfl) ⟨14483, by rfl⟩) (B 28967 (by norm_num) ⟨14483, by rfl⟩ (by norm_num))
theorem R77249 : Reach 77249 := rs (se 2 (by rfl) ⟨28968, by rfl⟩) (B 57937 (by norm_num) ⟨28968, by rfl⟩ (by norm_num))
theorem R77253 : Reach 77253 := rs (se 4 (by rfl) ⟨7242, by rfl⟩) (B 14485 (by norm_num) ⟨7242, by rfl⟩ (by norm_num))
theorem R77257 : Reach 77257 := rs (se 2 (by rfl) ⟨28971, by rfl⟩) (B 57943 (by norm_num) ⟨28971, by rfl⟩ (by norm_num))
theorem R77261 : Reach 77261 := rs (se 3 (by rfl) ⟨14486, by rfl⟩) (B 28973 (by norm_num) ⟨14486, by rfl⟩ (by norm_num))
theorem R77265 : Reach 77265 := rs (se 2 (by rfl) ⟨28974, by rfl⟩) (B 57949 (by norm_num) ⟨28974, by rfl⟩ (by norm_num))
theorem R77269 : Reach 77269 := rs (se 7 (by rfl) ⟨905, by rfl⟩) (B 1811 (by norm_num) ⟨905, by rfl⟩ (by norm_num))
theorem R77273 : Reach 77273 := rs (se 2 (by rfl) ⟨28977, by rfl⟩) (B 57955 (by norm_num) ⟨28977, by rfl⟩ (by norm_num))
theorem R77277 : Reach 77277 := rs (se 3 (by rfl) ⟨14489, by rfl⟩) (B 28979 (by norm_num) ⟨14489, by rfl⟩ (by norm_num))
theorem R110045 : Reach 110045 := rs (se 3 (by rfl) ⟨20633, by rfl⟩) (B 41267 (by norm_num) ⟨20633, by rfl⟩ (by norm_num))
theorem R77281 : Reach 77281 := rs (se 2 (by rfl) ⟨28980, by rfl⟩) (B 57961 (by norm_num) ⟨28980, by rfl⟩ (by norm_num))
theorem R77285 : Reach 77285 := rs (se 4 (by rfl) ⟨7245, by rfl⟩) (B 14491 (by norm_num) ⟨7245, by rfl⟩ (by norm_num))
theorem R175589 : Reach 175589 := rs (se 4 (by rfl) ⟨16461, by rfl⟩) (B 32923 (by norm_num) ⟨16461, by rfl⟩ (by norm_num))
theorem R77289 : Reach 77289 := rs (se 2 (by rfl) ⟨28983, by rfl⟩) (B 57967 (by norm_num) ⟨28983, by rfl⟩ (by norm_num))
theorem R77293 : Reach 77293 := rs (se 3 (by rfl) ⟨14492, by rfl⟩) (B 28985 (by norm_num) ⟨14492, by rfl⟩ (by norm_num))
theorem R77297 : Reach 77297 := rs (se 2 (by rfl) ⟨28986, by rfl⟩) (B 57973 (by norm_num) ⟨28986, by rfl⟩ (by norm_num))
theorem R77301 : Reach 77301 := rs (se 5 (by rfl) ⟨3623, by rfl⟩) (B 7247 (by norm_num) ⟨3623, by rfl⟩ (by norm_num))
theorem R77305 : Reach 77305 := rs (se 2 (by rfl) ⟨28989, by rfl⟩) (B 57979 (by norm_num) ⟨28989, by rfl⟩ (by norm_num))
theorem R77309 : Reach 77309 := rs (se 3 (by rfl) ⟨14495, by rfl⟩) (B 28991 (by norm_num) ⟨14495, by rfl⟩ (by norm_num))
theorem R77313 : Reach 77313 := rs (se 2 (by rfl) ⟨28992, by rfl⟩) (B 57985 (by norm_num) ⟨28992, by rfl⟩ (by norm_num))
theorem R77317 : Reach 77317 := rs (se 4 (by rfl) ⟨7248, by rfl⟩) (B 14497 (by norm_num) ⟨7248, by rfl⟩ (by norm_num))
theorem R77321 : Reach 77321 := rs (se 2 (by rfl) ⟨28995, by rfl⟩) (B 57991 (by norm_num) ⟨28995, by rfl⟩ (by norm_num))
theorem R77325 : Reach 77325 := rs (se 3 (by rfl) ⟨14498, by rfl⟩) (B 28997 (by norm_num) ⟨14498, by rfl⟩ (by norm_num))
theorem R77329 : Reach 77329 := rs (se 2 (by rfl) ⟨28998, by rfl⟩) (B 57997 (by norm_num) ⟨28998, by rfl⟩ (by norm_num))
theorem R273941 : Reach 273941 := rs (se 6 (by rfl) ⟨6420, by rfl⟩) (B 12841 (by norm_num) ⟨6420, by rfl⟩ (by norm_num))
theorem R77333 : Reach 77333 := rs (se 6 (by rfl) ⟨1812, by rfl⟩) (B 3625 (by norm_num) ⟨1812, by rfl⟩ (by norm_num))
theorem R77337 : Reach 77337 := rs (se 2 (by rfl) ⟨29001, by rfl⟩) (B 58003 (by norm_num) ⟨29001, by rfl⟩ (by norm_num))
theorem R142877 : Reach 142877 := rs (se 3 (by rfl) ⟨26789, by rfl⟩) (B 53579 (by norm_num) ⟨26789, by rfl⟩ (by norm_num))
theorem R77341 : Reach 77341 := rs (se 3 (by rfl) ⟨14501, by rfl⟩) (B 29003 (by norm_num) ⟨14501, by rfl⟩ (by norm_num))
theorem R77345 : Reach 77345 := rs (se 2 (by rfl) ⟨29004, by rfl⟩) (B 58009 (by norm_num) ⟨29004, by rfl⟩ (by norm_num))
theorem R77349 : Reach 77349 := rs (se 4 (by rfl) ⟨7251, by rfl⟩) (B 14503 (by norm_num) ⟨7251, by rfl⟩ (by norm_num))
theorem R77353 : Reach 77353 := rs (se 2 (by rfl) ⟨29007, by rfl⟩) (B 58015 (by norm_num) ⟨29007, by rfl⟩ (by norm_num))
theorem R77357 : Reach 77357 := rs (se 3 (by rfl) ⟨14504, by rfl⟩) (B 29009 (by norm_num) ⟨14504, by rfl⟩ (by norm_num))
theorem R175661 : Reach 175661 := rs (se 3 (by rfl) ⟨32936, by rfl⟩) (B 65873 (by norm_num) ⟨32936, by rfl⟩ (by norm_num))
theorem R77361 : Reach 77361 := rs (se 2 (by rfl) ⟨29010, by rfl⟩) (B 58021 (by norm_num) ⟨29010, by rfl⟩ (by norm_num))
theorem R77365 : Reach 77365 := rs (se 5 (by rfl) ⟨3626, by rfl⟩) (B 7253 (by norm_num) ⟨3626, by rfl⟩ (by norm_num))
theorem R77369 : Reach 77369 := rs (se 2 (by rfl) ⟨29013, by rfl⟩) (B 58027 (by norm_num) ⟨29013, by rfl⟩ (by norm_num))
theorem R77373 : Reach 77373 := rs (se 3 (by rfl) ⟨14507, by rfl⟩) (B 29015 (by norm_num) ⟨14507, by rfl⟩ (by norm_num))
theorem R77377 : Reach 77377 := rs (se 2 (by rfl) ⟨29016, by rfl⟩) (B 58033 (by norm_num) ⟨29016, by rfl⟩ (by norm_num))
theorem R77381 : Reach 77381 := rs (se 4 (by rfl) ⟨7254, by rfl⟩) (B 14509 (by norm_num) ⟨7254, by rfl⟩ (by norm_num))
theorem R77385 : Reach 77385 := rs (se 2 (by rfl) ⟨29019, by rfl⟩) (B 58039 (by norm_num) ⟨29019, by rfl⟩ (by norm_num))
theorem R77389 : Reach 77389 := rs (se 3 (by rfl) ⟨14510, by rfl⟩) (B 29021 (by norm_num) ⟨14510, by rfl⟩ (by norm_num))
theorem R77393 : Reach 77393 := rs (se 2 (by rfl) ⟨29022, by rfl⟩) (B 58045 (by norm_num) ⟨29022, by rfl⟩ (by norm_num))
theorem R77397 : Reach 77397 := rs (se 8 (by rfl) ⟨453, by rfl⟩) (B 907 (by norm_num) ⟨453, by rfl⟩ (by norm_num))
theorem R77401 : Reach 77401 := rs (se 2 (by rfl) ⟨29025, by rfl⟩) (B 58051 (by norm_num) ⟨29025, by rfl⟩ (by norm_num))
theorem R77405 : Reach 77405 := rs (se 3 (by rfl) ⟨14513, by rfl⟩) (B 29027 (by norm_num) ⟨14513, by rfl⟩ (by norm_num))
theorem R77409 : Reach 77409 := rs (se 2 (by rfl) ⟨29028, by rfl⟩) (B 58057 (by norm_num) ⟨29028, by rfl⟩ (by norm_num))
theorem R77413 : Reach 77413 := rs (se 4 (by rfl) ⟨7257, by rfl⟩) (B 14515 (by norm_num) ⟨7257, by rfl⟩ (by norm_num))
theorem R77417 : Reach 77417 := rs (se 2 (by rfl) ⟨29031, by rfl⟩) (B 58063 (by norm_num) ⟨29031, by rfl⟩ (by norm_num))
theorem R77421 : Reach 77421 := rs (se 3 (by rfl) ⟨14516, by rfl⟩) (B 29033 (by norm_num) ⟨14516, by rfl⟩ (by norm_num))
theorem R77425 : Reach 77425 := rs (se 2 (by rfl) ⟨29034, by rfl⟩) (B 58069 (by norm_num) ⟨29034, by rfl⟩ (by norm_num))
theorem R77429 : Reach 77429 := rs (se 5 (by rfl) ⟨3629, by rfl⟩) (B 7259 (by norm_num) ⟨3629, by rfl⟩ (by norm_num))
theorem R175733 : Reach 175733 := rs (se 5 (by rfl) ⟨8237, by rfl⟩) (B 16475 (by norm_num) ⟨8237, by rfl⟩ (by norm_num))
theorem R77433 : Reach 77433 := rs (se 2 (by rfl) ⟨29037, by rfl⟩) (B 58075 (by norm_num) ⟨29037, by rfl⟩ (by norm_num))
theorem R77437 : Reach 77437 := rs (se 3 (by rfl) ⟨14519, by rfl⟩) (B 29039 (by norm_num) ⟨14519, by rfl⟩ (by norm_num))
theorem R77441 : Reach 77441 := rs (se 2 (by rfl) ⟨29040, by rfl⟩) (B 58081 (by norm_num) ⟨29040, by rfl⟩ (by norm_num))
theorem R77445 : Reach 77445 := rs (se 4 (by rfl) ⟨7260, by rfl⟩) (B 14521 (by norm_num) ⟨7260, by rfl⟩ (by norm_num))
theorem R77449 : Reach 77449 := rs (se 2 (by rfl) ⟨29043, by rfl⟩) (B 58087 (by norm_num) ⟨29043, by rfl⟩ (by norm_num))
theorem R77453 : Reach 77453 := rs (se 3 (by rfl) ⟨14522, by rfl⟩) (B 29045 (by norm_num) ⟨14522, by rfl⟩ (by norm_num))
theorem R77457 : Reach 77457 := rs (se 2 (by rfl) ⟨29046, by rfl⟩) (B 58093 (by norm_num) ⟨29046, by rfl⟩ (by norm_num))
theorem R77461 : Reach 77461 := rs (se 6 (by rfl) ⟨1815, by rfl⟩) (B 3631 (by norm_num) ⟨1815, by rfl⟩ (by norm_num))
theorem R77465 : Reach 77465 := rs (se 2 (by rfl) ⟨29049, by rfl⟩) (B 58099 (by norm_num) ⟨29049, by rfl⟩ (by norm_num))
theorem R77469 : Reach 77469 := rs (se 3 (by rfl) ⟨14525, by rfl⟩) (B 29051 (by norm_num) ⟨14525, by rfl⟩ (by norm_num))
theorem R77473 : Reach 77473 := rs (se 2 (by rfl) ⟨29052, by rfl⟩) (B 58105 (by norm_num) ⟨29052, by rfl⟩ (by norm_num))
theorem R77477 : Reach 77477 := rs (se 4 (by rfl) ⟨7263, by rfl⟩) (B 14527 (by norm_num) ⟨7263, by rfl⟩ (by norm_num))
theorem R77481 : Reach 77481 := rs (se 2 (by rfl) ⟨29055, by rfl⟩) (B 58111 (by norm_num) ⟨29055, by rfl⟩ (by norm_num))
theorem R143021 : Reach 143021 := rs (se 3 (by rfl) ⟨26816, by rfl⟩) (B 53633 (by norm_num) ⟨26816, by rfl⟩ (by norm_num))
theorem R77485 : Reach 77485 := rs (se 3 (by rfl) ⟨14528, by rfl⟩) (B 29057 (by norm_num) ⟨14528, by rfl⟩ (by norm_num))
theorem R77489 : Reach 77489 := rs (se 2 (by rfl) ⟨29058, by rfl⟩) (B 58117 (by norm_num) ⟨29058, by rfl⟩ (by norm_num))
theorem R77493 : Reach 77493 := rs (se 5 (by rfl) ⟨3632, by rfl⟩) (B 7265 (by norm_num) ⟨3632, by rfl⟩ (by norm_num))
theorem R77497 : Reach 77497 := rs (se 2 (by rfl) ⟨29061, by rfl⟩) (B 58123 (by norm_num) ⟨29061, by rfl⟩ (by norm_num))
theorem R77501 : Reach 77501 := rs (se 3 (by rfl) ⟨14531, by rfl⟩) (B 29063 (by norm_num) ⟨14531, by rfl⟩ (by norm_num))
theorem R175805 : Reach 175805 := rs (se 3 (by rfl) ⟨32963, by rfl⟩) (B 65927 (by norm_num) ⟨32963, by rfl⟩ (by norm_num))
theorem R77505 : Reach 77505 := rs (se 2 (by rfl) ⟨29064, by rfl⟩) (B 58129 (by norm_num) ⟨29064, by rfl⟩ (by norm_num))
theorem R77509 : Reach 77509 := rs (se 4 (by rfl) ⟨7266, by rfl⟩) (B 14533 (by norm_num) ⟨7266, by rfl⟩ (by norm_num))
theorem R77513 : Reach 77513 := rs (se 2 (by rfl) ⟨29067, by rfl⟩) (B 58135 (by norm_num) ⟨29067, by rfl⟩ (by norm_num))
theorem R77517 : Reach 77517 := rs (se 3 (by rfl) ⟨14534, by rfl⟩) (B 29069 (by norm_num) ⟨14534, by rfl⟩ (by norm_num))
theorem R77521 : Reach 77521 := rs (se 2 (by rfl) ⟨29070, by rfl⟩) (B 58141 (by norm_num) ⟨29070, by rfl⟩ (by norm_num))
theorem R77525 : Reach 77525 := rs (se 7 (by rfl) ⟨908, by rfl⟩) (B 1817 (by norm_num) ⟨908, by rfl⟩ (by norm_num))
theorem R77529 : Reach 77529 := rs (se 2 (by rfl) ⟨29073, by rfl⟩) (B 58147 (by norm_num) ⟨29073, by rfl⟩ (by norm_num))
theorem R77533 : Reach 77533 := rs (se 3 (by rfl) ⟨14537, by rfl⟩) (B 29075 (by norm_num) ⟨14537, by rfl⟩ (by norm_num))
theorem R77537 : Reach 77537 := rs (se 2 (by rfl) ⟨29076, by rfl⟩) (B 58153 (by norm_num) ⟨29076, by rfl⟩ (by norm_num))
theorem R77541 : Reach 77541 := rs (se 4 (by rfl) ⟨7269, by rfl⟩) (B 14539 (by norm_num) ⟨7269, by rfl⟩ (by norm_num))
theorem R77545 : Reach 77545 := rs (se 2 (by rfl) ⟨29079, by rfl⟩) (B 58159 (by norm_num) ⟨29079, by rfl⟩ (by norm_num))
theorem R77549 : Reach 77549 := rs (se 3 (by rfl) ⟨14540, by rfl⟩) (B 29081 (by norm_num) ⟨14540, by rfl⟩ (by norm_num))
theorem R77553 : Reach 77553 := rs (se 2 (by rfl) ⟨29082, by rfl⟩) (B 58165 (by norm_num) ⟨29082, by rfl⟩ (by norm_num))
theorem R77557 : Reach 77557 := rs (se 5 (by rfl) ⟨3635, by rfl⟩) (B 7271 (by norm_num) ⟨3635, by rfl⟩ (by norm_num))
theorem R77561 : Reach 77561 := rs (se 2 (by rfl) ⟨29085, by rfl⟩) (B 58171 (by norm_num) ⟨29085, by rfl⟩ (by norm_num))
theorem R77565 : Reach 77565 := rs (se 3 (by rfl) ⟨14543, by rfl⟩) (B 29087 (by norm_num) ⟨14543, by rfl⟩ (by norm_num))
theorem R77569 : Reach 77569 := rs (se 2 (by rfl) ⟨29088, by rfl⟩) (B 58177 (by norm_num) ⟨29088, by rfl⟩ (by norm_num))
theorem R77573 : Reach 77573 := rs (se 4 (by rfl) ⟨7272, by rfl⟩) (B 14545 (by norm_num) ⟨7272, by rfl⟩ (by norm_num))
theorem R175877 : Reach 175877 := rs (se 4 (by rfl) ⟨16488, by rfl⟩) (B 32977 (by norm_num) ⟨16488, by rfl⟩ (by norm_num))
theorem R77577 : Reach 77577 := rs (se 2 (by rfl) ⟨29091, by rfl⟩) (B 58183 (by norm_num) ⟨29091, by rfl⟩ (by norm_num))
theorem R77581 : Reach 77581 := rs (se 3 (by rfl) ⟨14546, by rfl⟩) (B 29093 (by norm_num) ⟨14546, by rfl⟩ (by norm_num))
theorem R77585 : Reach 77585 := rs (se 2 (by rfl) ⟨29094, by rfl⟩) (B 58189 (by norm_num) ⟨29094, by rfl⟩ (by norm_num))
theorem R77589 : Reach 77589 := rs (se 6 (by rfl) ⟨1818, by rfl⟩) (B 3637 (by norm_num) ⟨1818, by rfl⟩ (by norm_num))
theorem R77593 : Reach 77593 := rs (se 2 (by rfl) ⟨29097, by rfl⟩) (B 58195 (by norm_num) ⟨29097, by rfl⟩ (by norm_num))
theorem R77597 : Reach 77597 := rs (se 3 (by rfl) ⟨14549, by rfl⟩) (B 29099 (by norm_num) ⟨14549, by rfl⟩ (by norm_num))
theorem R77601 : Reach 77601 := rs (se 2 (by rfl) ⟨29100, by rfl⟩) (B 58201 (by norm_num) ⟨29100, by rfl⟩ (by norm_num))
theorem R77605 : Reach 77605 := rs (se 4 (by rfl) ⟨7275, by rfl⟩) (B 14551 (by norm_num) ⟨7275, by rfl⟩ (by norm_num))
theorem R77609 : Reach 77609 := rs (se 2 (by rfl) ⟨29103, by rfl⟩) (B 58207 (by norm_num) ⟨29103, by rfl⟩ (by norm_num))
theorem R77613 : Reach 77613 := rs (se 3 (by rfl) ⟨14552, by rfl⟩) (B 29105 (by norm_num) ⟨14552, by rfl⟩ (by norm_num))
theorem R77617 : Reach 77617 := rs (se 2 (by rfl) ⟨29106, by rfl⟩) (B 58213 (by norm_num) ⟨29106, by rfl⟩ (by norm_num))
theorem R77621 : Reach 77621 := rs (se 5 (by rfl) ⟨3638, by rfl⟩) (B 7277 (by norm_num) ⟨3638, by rfl⟩ (by norm_num))
theorem R77625 : Reach 77625 := rs (se 2 (by rfl) ⟨29109, by rfl⟩) (B 58219 (by norm_num) ⟨29109, by rfl⟩ (by norm_num))
theorem R77629 : Reach 77629 := rs (se 3 (by rfl) ⟨14555, by rfl⟩) (B 29111 (by norm_num) ⟨14555, by rfl⟩ (by norm_num))
theorem R77633 : Reach 77633 := rs (se 2 (by rfl) ⟨29112, by rfl⟩) (B 58225 (by norm_num) ⟨29112, by rfl⟩ (by norm_num))
theorem R77637 : Reach 77637 := rs (se 4 (by rfl) ⟨7278, by rfl⟩) (B 14557 (by norm_num) ⟨7278, by rfl⟩ (by norm_num))
theorem R77641 : Reach 77641 := rs (se 2 (by rfl) ⟨29115, by rfl⟩) (B 58231 (by norm_num) ⟨29115, by rfl⟩ (by norm_num))
theorem R77645 : Reach 77645 := rs (se 3 (by rfl) ⟨14558, by rfl⟩) (B 29117 (by norm_num) ⟨14558, by rfl⟩ (by norm_num))
theorem R175949 : Reach 175949 := rs (se 3 (by rfl) ⟨32990, by rfl⟩) (B 65981 (by norm_num) ⟨32990, by rfl⟩ (by norm_num))
theorem R77649 : Reach 77649 := rs (se 2 (by rfl) ⟨29118, by rfl⟩) (B 58237 (by norm_num) ⟨29118, by rfl⟩ (by norm_num))
theorem R77653 : Reach 77653 := rs (se 9 (by rfl) ⟨227, by rfl⟩) (B 455 (by norm_num) ⟨227, by rfl⟩ (by norm_num))
theorem R77657 : Reach 77657 := rs (se 2 (by rfl) ⟨29121, by rfl⟩) (B 58243 (by norm_num) ⟨29121, by rfl⟩ (by norm_num))
theorem R77661 : Reach 77661 := rs (se 3 (by rfl) ⟨14561, by rfl⟩) (B 29123 (by norm_num) ⟨14561, by rfl⟩ (by norm_num))
theorem R77665 : Reach 77665 := rs (se 2 (by rfl) ⟨29124, by rfl⟩) (B 58249 (by norm_num) ⟨29124, by rfl⟩ (by norm_num))
theorem R77669 : Reach 77669 := rs (se 4 (by rfl) ⟨7281, by rfl⟩) (B 14563 (by norm_num) ⟨7281, by rfl⟩ (by norm_num))
theorem R77673 : Reach 77673 := rs (se 2 (by rfl) ⟨29127, by rfl⟩) (B 58255 (by norm_num) ⟨29127, by rfl⟩ (by norm_num))
theorem R77677 : Reach 77677 := rs (se 3 (by rfl) ⟨14564, by rfl⟩) (B 29129 (by norm_num) ⟨14564, by rfl⟩ (by norm_num))
theorem R77681 : Reach 77681 := rs (se 2 (by rfl) ⟨29130, by rfl⟩) (B 58261 (by norm_num) ⟨29130, by rfl⟩ (by norm_num))
theorem R77685 : Reach 77685 := rs (se 5 (by rfl) ⟨3641, by rfl⟩) (B 7283 (by norm_num) ⟨3641, by rfl⟩ (by norm_num))
theorem R77689 : Reach 77689 := rs (se 2 (by rfl) ⟨29133, by rfl⟩) (B 58267 (by norm_num) ⟨29133, by rfl⟩ (by norm_num))
theorem R77693 : Reach 77693 := rs (se 3 (by rfl) ⟨14567, by rfl⟩) (B 29135 (by norm_num) ⟨14567, by rfl⟩ (by norm_num))
theorem R77697 : Reach 77697 := rs (se 2 (by rfl) ⟨29136, by rfl⟩) (B 58273 (by norm_num) ⟨29136, by rfl⟩ (by norm_num))
theorem R77701 : Reach 77701 := rs (se 4 (by rfl) ⟨7284, by rfl⟩) (B 14569 (by norm_num) ⟨7284, by rfl⟩ (by norm_num))
theorem R77705 : Reach 77705 := rs (se 2 (by rfl) ⟨29139, by rfl⟩) (B 58279 (by norm_num) ⟨29139, by rfl⟩ (by norm_num))
theorem R77709 : Reach 77709 := rs (se 3 (by rfl) ⟨14570, by rfl⟩) (B 29141 (by norm_num) ⟨14570, by rfl⟩ (by norm_num))
theorem R77713 : Reach 77713 := rs (se 2 (by rfl) ⟨29142, by rfl⟩) (B 58285 (by norm_num) ⟨29142, by rfl⟩ (by norm_num))
theorem R77717 : Reach 77717 := rs (se 6 (by rfl) ⟨1821, by rfl⟩) (B 3643 (by norm_num) ⟨1821, by rfl⟩ (by norm_num))
theorem R176021 : Reach 176021 := rs (se 6 (by rfl) ⟨4125, by rfl⟩) (B 8251 (by norm_num) ⟨4125, by rfl⟩ (by norm_num))
theorem R77721 : Reach 77721 := rs (se 2 (by rfl) ⟨29145, by rfl⟩) (B 58291 (by norm_num) ⟨29145, by rfl⟩ (by norm_num))
theorem R77725 : Reach 77725 := rs (se 3 (by rfl) ⟨14573, by rfl⟩) (B 29147 (by norm_num) ⟨14573, by rfl⟩ (by norm_num))
theorem R77729 : Reach 77729 := rs (se 2 (by rfl) ⟨29148, by rfl⟩) (B 58297 (by norm_num) ⟨29148, by rfl⟩ (by norm_num))
theorem R77733 : Reach 77733 := rs (se 4 (by rfl) ⟨7287, by rfl⟩) (B 14575 (by norm_num) ⟨7287, by rfl⟩ (by norm_num))
theorem R77737 : Reach 77737 := rs (se 2 (by rfl) ⟨29151, by rfl⟩) (B 58303 (by norm_num) ⟨29151, by rfl⟩ (by norm_num))
theorem R77741 : Reach 77741 := rs (se 3 (by rfl) ⟨14576, by rfl⟩) (B 29153 (by norm_num) ⟨14576, by rfl⟩ (by norm_num))
theorem R77745 : Reach 77745 := rs (se 2 (by rfl) ⟨29154, by rfl⟩) (B 58309 (by norm_num) ⟨29154, by rfl⟩ (by norm_num))
theorem R77749 : Reach 77749 := rs (se 5 (by rfl) ⟨3644, by rfl⟩) (B 7289 (by norm_num) ⟨3644, by rfl⟩ (by norm_num))
theorem R77753 : Reach 77753 := rs (se 2 (by rfl) ⟨29157, by rfl⟩) (B 58315 (by norm_num) ⟨29157, by rfl⟩ (by norm_num))
theorem R77757 : Reach 77757 := rs (se 3 (by rfl) ⟨14579, by rfl⟩) (B 29159 (by norm_num) ⟨14579, by rfl⟩ (by norm_num))
theorem R77761 : Reach 77761 := rs (se 2 (by rfl) ⟨29160, by rfl⟩) (B 58321 (by norm_num) ⟨29160, by rfl⟩ (by norm_num))
theorem R77765 : Reach 77765 := rs (se 4 (by rfl) ⟨7290, by rfl⟩) (B 14581 (by norm_num) ⟨7290, by rfl⟩ (by norm_num))
theorem R77769 : Reach 77769 := rs (se 2 (by rfl) ⟨29163, by rfl⟩) (B 58327 (by norm_num) ⟨29163, by rfl⟩ (by norm_num))
theorem R143309 : Reach 143309 := rs (se 3 (by rfl) ⟨26870, by rfl⟩) (B 53741 (by norm_num) ⟨26870, by rfl⟩ (by norm_num))
theorem R77773 : Reach 77773 := rs (se 3 (by rfl) ⟨14582, by rfl⟩) (B 29165 (by norm_num) ⟨14582, by rfl⟩ (by norm_num))
theorem R77777 : Reach 77777 := rs (se 2 (by rfl) ⟨29166, by rfl⟩) (B 58333 (by norm_num) ⟨29166, by rfl⟩ (by norm_num))
theorem R77781 : Reach 77781 := rs (se 7 (by rfl) ⟨911, by rfl⟩) (B 1823 (by norm_num) ⟨911, by rfl⟩ (by norm_num))
theorem R77785 : Reach 77785 := rs (se 2 (by rfl) ⟨29169, by rfl⟩) (B 58339 (by norm_num) ⟨29169, by rfl⟩ (by norm_num))
theorem R77789 : Reach 77789 := rs (se 3 (by rfl) ⟨14585, by rfl⟩) (B 29171 (by norm_num) ⟨14585, by rfl⟩ (by norm_num))
theorem R176093 : Reach 176093 := rs (se 3 (by rfl) ⟨33017, by rfl⟩) (B 66035 (by norm_num) ⟨33017, by rfl⟩ (by norm_num))
theorem R77793 : Reach 77793 := rs (se 2 (by rfl) ⟨29172, by rfl⟩) (B 58345 (by norm_num) ⟨29172, by rfl⟩ (by norm_num))
theorem R77797 : Reach 77797 := rs (se 4 (by rfl) ⟨7293, by rfl⟩) (B 14587 (by norm_num) ⟨7293, by rfl⟩ (by norm_num))
theorem R77801 : Reach 77801 := rs (se 2 (by rfl) ⟨29175, by rfl⟩) (B 58351 (by norm_num) ⟨29175, by rfl⟩ (by norm_num))
theorem R77805 : Reach 77805 := rs (se 3 (by rfl) ⟨14588, by rfl⟩) (B 29177 (by norm_num) ⟨14588, by rfl⟩ (by norm_num))
theorem R77809 : Reach 77809 := rs (se 2 (by rfl) ⟨29178, by rfl⟩) (B 58357 (by norm_num) ⟨29178, by rfl⟩ (by norm_num))
theorem R77813 : Reach 77813 := rs (se 5 (by rfl) ⟨3647, by rfl⟩) (B 7295 (by norm_num) ⟨3647, by rfl⟩ (by norm_num))
theorem R77817 : Reach 77817 := rs (se 2 (by rfl) ⟨29181, by rfl⟩) (B 58363 (by norm_num) ⟨29181, by rfl⟩ (by norm_num))
theorem R77821 : Reach 77821 := rs (se 3 (by rfl) ⟨14591, by rfl⟩) (B 29183 (by norm_num) ⟨14591, by rfl⟩ (by norm_num))
theorem R77825 : Reach 77825 := rs (se 2 (by rfl) ⟨29184, by rfl⟩) (B 58369 (by norm_num) ⟨29184, by rfl⟩ (by norm_num))
theorem R77829 : Reach 77829 := rs (se 4 (by rfl) ⟨7296, by rfl⟩) (B 14593 (by norm_num) ⟨7296, by rfl⟩ (by norm_num))
theorem R77833 : Reach 77833 := rs (se 2 (by rfl) ⟨29187, by rfl⟩) (B 58375 (by norm_num) ⟨29187, by rfl⟩ (by norm_num))
theorem R77837 : Reach 77837 := rs (se 3 (by rfl) ⟨14594, by rfl⟩) (B 29189 (by norm_num) ⟨14594, by rfl⟩ (by norm_num))
theorem R77841 : Reach 77841 := rs (se 2 (by rfl) ⟨29190, by rfl⟩) (B 58381 (by norm_num) ⟨29190, by rfl⟩ (by norm_num))
theorem R77845 : Reach 77845 := rs (se 6 (by rfl) ⟨1824, by rfl⟩) (B 3649 (by norm_num) ⟨1824, by rfl⟩ (by norm_num))
theorem R77849 : Reach 77849 := rs (se 2 (by rfl) ⟨29193, by rfl⟩) (B 58387 (by norm_num) ⟨29193, by rfl⟩ (by norm_num))
theorem R77853 : Reach 77853 := rs (se 3 (by rfl) ⟨14597, by rfl⟩) (B 29195 (by norm_num) ⟨14597, by rfl⟩ (by norm_num))
theorem R77857 : Reach 77857 := rs (se 2 (by rfl) ⟨29196, by rfl⟩) (B 58393 (by norm_num) ⟨29196, by rfl⟩ (by norm_num))
theorem R77861 : Reach 77861 := rs (se 4 (by rfl) ⟨7299, by rfl⟩) (B 14599 (by norm_num) ⟨7299, by rfl⟩ (by norm_num))
theorem R176165 : Reach 176165 := rs (se 4 (by rfl) ⟨16515, by rfl⟩) (B 33031 (by norm_num) ⟨16515, by rfl⟩ (by norm_num))
theorem R77865 : Reach 77865 := rs (se 2 (by rfl) ⟨29199, by rfl⟩) (B 58399 (by norm_num) ⟨29199, by rfl⟩ (by norm_num))
theorem R77869 : Reach 77869 := rs (se 3 (by rfl) ⟨14600, by rfl⟩) (B 29201 (by norm_num) ⟨14600, by rfl⟩ (by norm_num))
theorem R77873 : Reach 77873 := rs (se 2 (by rfl) ⟨29202, by rfl⟩) (B 58405 (by norm_num) ⟨29202, by rfl⟩ (by norm_num))
theorem R77877 : Reach 77877 := rs (se 5 (by rfl) ⟨3650, by rfl⟩) (B 7301 (by norm_num) ⟨3650, by rfl⟩ (by norm_num))
theorem R77881 : Reach 77881 := rs (se 2 (by rfl) ⟨29205, by rfl⟩) (B 58411 (by norm_num) ⟨29205, by rfl⟩ (by norm_num))
theorem R77885 : Reach 77885 := rs (se 3 (by rfl) ⟨14603, by rfl⟩) (B 29207 (by norm_num) ⟨14603, by rfl⟩ (by norm_num))
theorem R77889 : Reach 77889 := rs (se 2 (by rfl) ⟨29208, by rfl⟩) (B 58417 (by norm_num) ⟨29208, by rfl⟩ (by norm_num))
theorem R77893 : Reach 77893 := rs (se 4 (by rfl) ⟨7302, by rfl⟩) (B 14605 (by norm_num) ⟨7302, by rfl⟩ (by norm_num))
theorem R77897 : Reach 77897 := rs (se 2 (by rfl) ⟨29211, by rfl⟩) (B 58423 (by norm_num) ⟨29211, by rfl⟩ (by norm_num))
theorem R77901 : Reach 77901 := rs (se 3 (by rfl) ⟨14606, by rfl⟩) (B 29213 (by norm_num) ⟨14606, by rfl⟩ (by norm_num))
theorem R77905 : Reach 77905 := rs (se 2 (by rfl) ⟨29214, by rfl⟩) (B 58429 (by norm_num) ⟨29214, by rfl⟩ (by norm_num))
theorem R77909 : Reach 77909 := rs (se 8 (by rfl) ⟨456, by rfl⟩) (B 913 (by norm_num) ⟨456, by rfl⟩ (by norm_num))
theorem R77913 : Reach 77913 := rs (se 2 (by rfl) ⟨29217, by rfl⟩) (B 58435 (by norm_num) ⟨29217, by rfl⟩ (by norm_num))
theorem R77917 : Reach 77917 := rs (se 3 (by rfl) ⟨14609, by rfl⟩) (B 29219 (by norm_num) ⟨14609, by rfl⟩ (by norm_num))
theorem R77921 : Reach 77921 := rs (se 2 (by rfl) ⟨29220, by rfl⟩) (B 58441 (by norm_num) ⟨29220, by rfl⟩ (by norm_num))
theorem R143461 : Reach 143461 := rs (se 4 (by rfl) ⟨13449, by rfl⟩) (B 26899 (by norm_num) ⟨13449, by rfl⟩ (by norm_num))
theorem R77925 : Reach 77925 := rs (se 4 (by rfl) ⟨7305, by rfl⟩) (B 14611 (by norm_num) ⟨7305, by rfl⟩ (by norm_num))
theorem R77929 : Reach 77929 := rs (se 2 (by rfl) ⟨29223, by rfl⟩) (B 58447 (by norm_num) ⟨29223, by rfl⟩ (by norm_num))
theorem R77933 : Reach 77933 := rs (se 3 (by rfl) ⟨14612, by rfl⟩) (B 29225 (by norm_num) ⟨14612, by rfl⟩ (by norm_num))
theorem R176237 : Reach 176237 := rs (se 3 (by rfl) ⟨33044, by rfl⟩) (B 66089 (by norm_num) ⟨33044, by rfl⟩ (by norm_num))
theorem R77937 : Reach 77937 := rs (se 2 (by rfl) ⟨29226, by rfl⟩) (B 58453 (by norm_num) ⟨29226, by rfl⟩ (by norm_num))
theorem R77941 : Reach 77941 := rs (se 5 (by rfl) ⟨3653, by rfl⟩) (B 7307 (by norm_num) ⟨3653, by rfl⟩ (by norm_num))
theorem R77945 : Reach 77945 := rs (se 2 (by rfl) ⟨29229, by rfl⟩) (B 58459 (by norm_num) ⟨29229, by rfl⟩ (by norm_num))
theorem R77949 : Reach 77949 := rs (se 3 (by rfl) ⟨14615, by rfl⟩) (B 29231 (by norm_num) ⟨14615, by rfl⟩ (by norm_num))
theorem R77953 : Reach 77953 := rs (se 2 (by rfl) ⟨29232, by rfl⟩) (B 58465 (by norm_num) ⟨29232, by rfl⟩ (by norm_num))
theorem R77957 : Reach 77957 := rs (se 4 (by rfl) ⟨7308, by rfl⟩) (B 14617 (by norm_num) ⟨7308, by rfl⟩ (by norm_num))
theorem R77961 : Reach 77961 := rs (se 2 (by rfl) ⟨29235, by rfl⟩) (B 58471 (by norm_num) ⟨29235, by rfl⟩ (by norm_num))
theorem R77965 : Reach 77965 := rs (se 3 (by rfl) ⟨14618, by rfl⟩) (B 29237 (by norm_num) ⟨14618, by rfl⟩ (by norm_num))
theorem R77969 : Reach 77969 := rs (se 2 (by rfl) ⟨29238, by rfl⟩) (B 58477 (by norm_num) ⟨29238, by rfl⟩ (by norm_num))
theorem R77973 : Reach 77973 := rs (se 6 (by rfl) ⟨1827, by rfl⟩) (B 3655 (by norm_num) ⟨1827, by rfl⟩ (by norm_num))
theorem R77977 : Reach 77977 := rs (se 2 (by rfl) ⟨29241, by rfl⟩) (B 58483 (by norm_num) ⟨29241, by rfl⟩ (by norm_num))
theorem R77981 : Reach 77981 := rs (se 3 (by rfl) ⟨14621, by rfl⟩) (B 29243 (by norm_num) ⟨14621, by rfl⟩ (by norm_num))
theorem R77985 : Reach 77985 := rs (se 2 (by rfl) ⟨29244, by rfl⟩) (B 58489 (by norm_num) ⟨29244, by rfl⟩ (by norm_num))
theorem R77989 : Reach 77989 := rs (se 4 (by rfl) ⟨7311, by rfl⟩) (B 14623 (by norm_num) ⟨7311, by rfl⟩ (by norm_num))
theorem R77993 : Reach 77993 := rs (se 2 (by rfl) ⟨29247, by rfl⟩) (B 58495 (by norm_num) ⟨29247, by rfl⟩ (by norm_num))
theorem R77997 : Reach 77997 := rs (se 3 (by rfl) ⟨14624, by rfl⟩) (B 29249 (by norm_num) ⟨14624, by rfl⟩ (by norm_num))
theorem R78001 : Reach 78001 := rs (se 2 (by rfl) ⟨29250, by rfl⟩) (B 58501 (by norm_num) ⟨29250, by rfl⟩ (by norm_num))
theorem R78005 : Reach 78005 := rs (se 5 (by rfl) ⟨3656, by rfl⟩) (B 7313 (by norm_num) ⟨3656, by rfl⟩ (by norm_num))
theorem R176309 : Reach 176309 := rs (se 5 (by rfl) ⟨8264, by rfl⟩) (B 16529 (by norm_num) ⟨8264, by rfl⟩ (by norm_num))
theorem R78009 : Reach 78009 := rs (se 2 (by rfl) ⟨29253, by rfl⟩) (B 58507 (by norm_num) ⟨29253, by rfl⟩ (by norm_num))
theorem R78013 : Reach 78013 := rs (se 3 (by rfl) ⟨14627, by rfl⟩) (B 29255 (by norm_num) ⟨14627, by rfl⟩ (by norm_num))
theorem R78017 : Reach 78017 := rs (se 2 (by rfl) ⟨29256, by rfl⟩) (B 58513 (by norm_num) ⟨29256, by rfl⟩ (by norm_num))
theorem R241861 : Reach 241861 := rs (se 4 (by rfl) ⟨22674, by rfl⟩) (B 45349 (by norm_num) ⟨22674, by rfl⟩ (by norm_num))
theorem R78021 : Reach 78021 := rs (se 4 (by rfl) ⟨7314, by rfl⟩) (B 14629 (by norm_num) ⟨7314, by rfl⟩ (by norm_num))
theorem R78025 : Reach 78025 := rs (se 2 (by rfl) ⟨29259, by rfl⟩) (B 58519 (by norm_num) ⟨29259, by rfl⟩ (by norm_num))
theorem R78029 : Reach 78029 := rs (se 3 (by rfl) ⟨14630, by rfl⟩) (B 29261 (by norm_num) ⟨14630, by rfl⟩ (by norm_num))
theorem R78033 : Reach 78033 := rs (se 2 (by rfl) ⟨29262, by rfl⟩) (B 58525 (by norm_num) ⟨29262, by rfl⟩ (by norm_num))
theorem R78037 : Reach 78037 := rs (se 7 (by rfl) ⟨914, by rfl⟩) (B 1829 (by norm_num) ⟨914, by rfl⟩ (by norm_num))
theorem R78041 : Reach 78041 := rs (se 2 (by rfl) ⟨29265, by rfl⟩) (B 58531 (by norm_num) ⟨29265, by rfl⟩ (by norm_num))
theorem R78045 : Reach 78045 := rs (se 3 (by rfl) ⟨14633, by rfl⟩) (B 29267 (by norm_num) ⟨14633, by rfl⟩ (by norm_num))
theorem R78049 : Reach 78049 := rs (se 2 (by rfl) ⟨29268, by rfl⟩) (B 58537 (by norm_num) ⟨29268, by rfl⟩ (by norm_num))
theorem R78053 : Reach 78053 := rs (se 4 (by rfl) ⟨7317, by rfl⟩) (B 14635 (by norm_num) ⟨7317, by rfl⟩ (by norm_num))
theorem R78057 : Reach 78057 := rs (se 2 (by rfl) ⟨29271, by rfl⟩) (B 58543 (by norm_num) ⟨29271, by rfl⟩ (by norm_num))
theorem R78061 : Reach 78061 := rs (se 3 (by rfl) ⟨14636, by rfl⟩) (B 29273 (by norm_num) ⟨14636, by rfl⟩ (by norm_num))
theorem R78065 : Reach 78065 := rs (se 2 (by rfl) ⟨29274, by rfl⟩) (B 58549 (by norm_num) ⟨29274, by rfl⟩ (by norm_num))
theorem R78069 : Reach 78069 := rs (se 5 (by rfl) ⟨3659, by rfl⟩) (B 7319 (by norm_num) ⟨3659, by rfl⟩ (by norm_num))
theorem R78073 : Reach 78073 := rs (se 2 (by rfl) ⟨29277, by rfl⟩) (B 58555 (by norm_num) ⟨29277, by rfl⟩ (by norm_num))
theorem R78077 : Reach 78077 := rs (se 3 (by rfl) ⟨14639, by rfl⟩) (B 29279 (by norm_num) ⟨14639, by rfl⟩ (by norm_num))
theorem R176381 : Reach 176381 := rs (se 3 (by rfl) ⟨33071, by rfl⟩) (B 66143 (by norm_num) ⟨33071, by rfl⟩ (by norm_num))
theorem R78081 : Reach 78081 := rs (se 2 (by rfl) ⟨29280, by rfl⟩) (B 58561 (by norm_num) ⟨29280, by rfl⟩ (by norm_num))
theorem R78085 : Reach 78085 := rs (se 4 (by rfl) ⟨7320, by rfl⟩) (B 14641 (by norm_num) ⟨7320, by rfl⟩ (by norm_num))
theorem R78089 : Reach 78089 := rs (se 2 (by rfl) ⟨29283, by rfl⟩) (B 58567 (by norm_num) ⟨29283, by rfl⟩ (by norm_num))
theorem R78093 : Reach 78093 := rs (se 3 (by rfl) ⟨14642, by rfl⟩) (B 29285 (by norm_num) ⟨14642, by rfl⟩ (by norm_num))
theorem R78097 : Reach 78097 := rs (se 2 (by rfl) ⟨29286, by rfl⟩) (B 58573 (by norm_num) ⟨29286, by rfl⟩ (by norm_num))
theorem R78101 : Reach 78101 := rs (se 6 (by rfl) ⟨1830, by rfl⟩) (B 3661 (by norm_num) ⟨1830, by rfl⟩ (by norm_num))
theorem R667925 : Reach 667925 := rs (se 6 (by rfl) ⟨15654, by rfl⟩) (B 31309 (by norm_num) ⟨15654, by rfl⟩ (by norm_num))
theorem R78105 : Reach 78105 := rs (se 2 (by rfl) ⟨29289, by rfl⟩) (B 58579 (by norm_num) ⟨29289, by rfl⟩ (by norm_num))
theorem R78109 : Reach 78109 := rs (se 3 (by rfl) ⟨14645, by rfl⟩) (B 29291 (by norm_num) ⟨14645, by rfl⟩ (by norm_num))
theorem R78113 : Reach 78113 := rs (se 2 (by rfl) ⟨29292, by rfl⟩) (B 58585 (by norm_num) ⟨29292, by rfl⟩ (by norm_num))
theorem R78117 : Reach 78117 := rs (se 4 (by rfl) ⟨7323, by rfl⟩) (B 14647 (by norm_num) ⟨7323, by rfl⟩ (by norm_num))
theorem R78121 : Reach 78121 := rs (se 2 (by rfl) ⟨29295, by rfl⟩) (B 58591 (by norm_num) ⟨29295, by rfl⟩ (by norm_num))
theorem R78125 : Reach 78125 := rs (se 3 (by rfl) ⟨14648, by rfl⟩) (B 29297 (by norm_num) ⟨14648, by rfl⟩ (by norm_num))
theorem R78129 : Reach 78129 := rs (se 2 (by rfl) ⟨29298, by rfl⟩) (B 58597 (by norm_num) ⟨29298, by rfl⟩ (by norm_num))
theorem R78133 : Reach 78133 := rs (se 5 (by rfl) ⟨3662, by rfl⟩) (B 7325 (by norm_num) ⟨3662, by rfl⟩ (by norm_num))
theorem R78137 : Reach 78137 := rs (se 2 (by rfl) ⟨29301, by rfl⟩) (B 58603 (by norm_num) ⟨29301, by rfl⟩ (by norm_num))
theorem R78141 : Reach 78141 := rs (se 3 (by rfl) ⟨14651, by rfl⟩) (B 29303 (by norm_num) ⟨14651, by rfl⟩ (by norm_num))
theorem R78145 : Reach 78145 := rs (se 2 (by rfl) ⟨29304, by rfl⟩) (B 58609 (by norm_num) ⟨29304, by rfl⟩ (by norm_num))
theorem R78149 : Reach 78149 := rs (se 4 (by rfl) ⟨7326, by rfl⟩) (B 14653 (by norm_num) ⟨7326, by rfl⟩ (by norm_num))
theorem R176453 : Reach 176453 := rs (se 4 (by rfl) ⟨16542, by rfl⟩) (B 33085 (by norm_num) ⟨16542, by rfl⟩ (by norm_num))
theorem R78153 : Reach 78153 := rs (se 2 (by rfl) ⟨29307, by rfl⟩) (B 58615 (by norm_num) ⟨29307, by rfl⟩ (by norm_num))
theorem R78157 : Reach 78157 := rs (se 3 (by rfl) ⟨14654, by rfl⟩) (B 29309 (by norm_num) ⟨14654, by rfl⟩ (by norm_num))
theorem R78161 : Reach 78161 := rs (se 2 (by rfl) ⟨29310, by rfl⟩) (B 58621 (by norm_num) ⟨29310, by rfl⟩ (by norm_num))
theorem R78165 : Reach 78165 := rs (se 10 (by rfl) ⟨114, by rfl⟩) (B 229 (by norm_num) ⟨114, by rfl⟩ (by norm_num))
theorem R78169 : Reach 78169 := rs (se 2 (by rfl) ⟨29313, by rfl⟩) (B 58627 (by norm_num) ⟨29313, by rfl⟩ (by norm_num))
theorem R78173 : Reach 78173 := rs (se 3 (by rfl) ⟨14657, by rfl⟩) (B 29315 (by norm_num) ⟨14657, by rfl⟩ (by norm_num))
theorem R78177 : Reach 78177 := rs (se 2 (by rfl) ⟨29316, by rfl⟩) (B 58633 (by norm_num) ⟨29316, by rfl⟩ (by norm_num))
theorem R78181 : Reach 78181 := rs (se 4 (by rfl) ⟨7329, by rfl⟩) (B 14659 (by norm_num) ⟨7329, by rfl⟩ (by norm_num))
theorem R78185 : Reach 78185 := rs (se 2 (by rfl) ⟨29319, by rfl⟩) (B 58639 (by norm_num) ⟨29319, by rfl⟩ (by norm_num))
theorem R78189 : Reach 78189 := rs (se 3 (by rfl) ⟨14660, by rfl⟩) (B 29321 (by norm_num) ⟨14660, by rfl⟩ (by norm_num))
theorem R78193 : Reach 78193 := rs (se 2 (by rfl) ⟨29322, by rfl⟩) (B 58645 (by norm_num) ⟨29322, by rfl⟩ (by norm_num))
theorem R78197 : Reach 78197 := rs (se 5 (by rfl) ⟨3665, by rfl⟩) (B 7331 (by norm_num) ⟨3665, by rfl⟩ (by norm_num))
theorem R78201 : Reach 78201 := rs (se 2 (by rfl) ⟨29325, by rfl⟩) (B 58651 (by norm_num) ⟨29325, by rfl⟩ (by norm_num))
theorem R78205 : Reach 78205 := rs (se 3 (by rfl) ⟨14663, by rfl⟩) (B 29327 (by norm_num) ⟨14663, by rfl⟩ (by norm_num))
theorem R78209 : Reach 78209 := rs (se 2 (by rfl) ⟨29328, by rfl⟩) (B 58657 (by norm_num) ⟨29328, by rfl⟩ (by norm_num))
theorem R78213 : Reach 78213 := rs (se 4 (by rfl) ⟨7332, by rfl⟩) (B 14665 (by norm_num) ⟨7332, by rfl⟩ (by norm_num))
theorem R78217 : Reach 78217 := rs (se 2 (by rfl) ⟨29331, by rfl⟩) (B 58663 (by norm_num) ⟨29331, by rfl⟩ (by norm_num))
theorem R78221 : Reach 78221 := rs (se 3 (by rfl) ⟨14666, by rfl⟩) (B 29333 (by norm_num) ⟨14666, by rfl⟩ (by norm_num))
theorem R176525 : Reach 176525 := rs (se 3 (by rfl) ⟨33098, by rfl⟩) (B 66197 (by norm_num) ⟨33098, by rfl⟩ (by norm_num))
theorem R78225 : Reach 78225 := rs (se 2 (by rfl) ⟨29334, by rfl⟩) (B 58669 (by norm_num) ⟨29334, by rfl⟩ (by norm_num))
theorem R143765 : Reach 143765 := rs (se 6 (by rfl) ⟨3369, by rfl⟩) (B 6739 (by norm_num) ⟨3369, by rfl⟩ (by norm_num))
theorem R78229 : Reach 78229 := rs (se 6 (by rfl) ⟨1833, by rfl⟩) (B 3667 (by norm_num) ⟨1833, by rfl⟩ (by norm_num))
theorem R78233 : Reach 78233 := rs (se 2 (by rfl) ⟨29337, by rfl⟩) (B 58675 (by norm_num) ⟨29337, by rfl⟩ (by norm_num))
theorem R78237 : Reach 78237 := rs (se 3 (by rfl) ⟨14669, by rfl⟩) (B 29339 (by norm_num) ⟨14669, by rfl⟩ (by norm_num))
theorem R78241 : Reach 78241 := rs (se 2 (by rfl) ⟨29340, by rfl⟩) (B 58681 (by norm_num) ⟨29340, by rfl⟩ (by norm_num))
theorem R78245 : Reach 78245 := rs (se 4 (by rfl) ⟨7335, by rfl⟩) (B 14671 (by norm_num) ⟨7335, by rfl⟩ (by norm_num))
theorem R78249 : Reach 78249 := rs (se 2 (by rfl) ⟨29343, by rfl⟩) (B 58687 (by norm_num) ⟨29343, by rfl⟩ (by norm_num))
theorem R78253 : Reach 78253 := rs (se 3 (by rfl) ⟨14672, by rfl⟩) (B 29345 (by norm_num) ⟨14672, by rfl⟩ (by norm_num))
theorem R78257 : Reach 78257 := rs (se 2 (by rfl) ⟨29346, by rfl⟩) (B 58693 (by norm_num) ⟨29346, by rfl⟩ (by norm_num))
theorem R78261 : Reach 78261 := rs (se 5 (by rfl) ⟨3668, by rfl⟩) (B 7337 (by norm_num) ⟨3668, by rfl⟩ (by norm_num))
theorem R78265 : Reach 78265 := rs (se 2 (by rfl) ⟨29349, by rfl⟩) (B 58699 (by norm_num) ⟨29349, by rfl⟩ (by norm_num))
theorem R78269 : Reach 78269 := rs (se 3 (by rfl) ⟨14675, by rfl⟩) (B 29351 (by norm_num) ⟨14675, by rfl⟩ (by norm_num))
theorem R78273 : Reach 78273 := rs (se 2 (by rfl) ⟨29352, by rfl⟩) (B 58705 (by norm_num) ⟨29352, by rfl⟩ (by norm_num))
theorem R78277 : Reach 78277 := rs (se 4 (by rfl) ⟨7338, by rfl⟩) (B 14677 (by norm_num) ⟨7338, by rfl⟩ (by norm_num))
theorem R78281 : Reach 78281 := rs (se 2 (by rfl) ⟨29355, by rfl⟩) (B 58711 (by norm_num) ⟨29355, by rfl⟩ (by norm_num))
theorem R78285 : Reach 78285 := rs (se 3 (by rfl) ⟨14678, by rfl⟩) (B 29357 (by norm_num) ⟨14678, by rfl⟩ (by norm_num))
theorem R78289 : Reach 78289 := rs (se 2 (by rfl) ⟨29358, by rfl⟩) (B 58717 (by norm_num) ⟨29358, by rfl⟩ (by norm_num))
theorem R78293 : Reach 78293 := rs (se 7 (by rfl) ⟨917, by rfl⟩) (B 1835 (by norm_num) ⟨917, by rfl⟩ (by norm_num))
theorem R176597 : Reach 176597 := rs (se 7 (by rfl) ⟨2069, by rfl⟩) (B 4139 (by norm_num) ⟨2069, by rfl⟩ (by norm_num))
theorem R78297 : Reach 78297 := rs (se 2 (by rfl) ⟨29361, by rfl⟩) (B 58723 (by norm_num) ⟨29361, by rfl⟩ (by norm_num))
theorem R78301 : Reach 78301 := rs (se 3 (by rfl) ⟨14681, by rfl⟩) (B 29363 (by norm_num) ⟨14681, by rfl⟩ (by norm_num))
theorem R78305 : Reach 78305 := rs (se 2 (by rfl) ⟨29364, by rfl⟩) (B 58729 (by norm_num) ⟨29364, by rfl⟩ (by norm_num))
theorem R78309 : Reach 78309 := rs (se 4 (by rfl) ⟨7341, by rfl⟩) (B 14683 (by norm_num) ⟨7341, by rfl⟩ (by norm_num))
theorem R78313 : Reach 78313 := rs (se 2 (by rfl) ⟨29367, by rfl⟩) (B 58735 (by norm_num) ⟨29367, by rfl⟩ (by norm_num))
theorem R78317 : Reach 78317 := rs (se 3 (by rfl) ⟨14684, by rfl⟩) (B 29369 (by norm_num) ⟨14684, by rfl⟩ (by norm_num))
theorem R78321 : Reach 78321 := rs (se 2 (by rfl) ⟨29370, by rfl⟩) (B 58741 (by norm_num) ⟨29370, by rfl⟩ (by norm_num))
theorem R78325 : Reach 78325 := rs (se 5 (by rfl) ⟨3671, by rfl⟩) (B 7343 (by norm_num) ⟨3671, by rfl⟩ (by norm_num))
theorem R78329 : Reach 78329 := rs (se 2 (by rfl) ⟨29373, by rfl⟩) (B 58747 (by norm_num) ⟨29373, by rfl⟩ (by norm_num))
theorem R78333 : Reach 78333 := rs (se 3 (by rfl) ⟨14687, by rfl⟩) (B 29375 (by norm_num) ⟨14687, by rfl⟩ (by norm_num))
theorem R78337 : Reach 78337 := rs (se 2 (by rfl) ⟨29376, by rfl⟩) (B 58753 (by norm_num) ⟨29376, by rfl⟩ (by norm_num))
theorem R78341 : Reach 78341 := rs (se 4 (by rfl) ⟨7344, by rfl⟩) (B 14689 (by norm_num) ⟨7344, by rfl⟩ (by norm_num))
theorem R78345 : Reach 78345 := rs (se 2 (by rfl) ⟨29379, by rfl⟩) (B 58759 (by norm_num) ⟨29379, by rfl⟩ (by norm_num))
theorem R78349 : Reach 78349 := rs (se 3 (by rfl) ⟨14690, by rfl⟩) (B 29381 (by norm_num) ⟨14690, by rfl⟩ (by norm_num))
theorem R78353 : Reach 78353 := rs (se 2 (by rfl) ⟨29382, by rfl⟩) (B 58765 (by norm_num) ⟨29382, by rfl⟩ (by norm_num))
theorem R78357 : Reach 78357 := rs (se 6 (by rfl) ⟨1836, by rfl⟩) (B 3673 (by norm_num) ⟨1836, by rfl⟩ (by norm_num))
theorem R78361 : Reach 78361 := rs (se 2 (by rfl) ⟨29385, by rfl⟩) (B 58771 (by norm_num) ⟨29385, by rfl⟩ (by norm_num))
theorem R78365 : Reach 78365 := rs (se 3 (by rfl) ⟨14693, by rfl⟩) (B 29387 (by norm_num) ⟨14693, by rfl⟩ (by norm_num))
theorem R176669 : Reach 176669 := rs (se 3 (by rfl) ⟨33125, by rfl⟩) (B 66251 (by norm_num) ⟨33125, by rfl⟩ (by norm_num))
theorem R78369 : Reach 78369 := rs (se 2 (by rfl) ⟨29388, by rfl⟩) (B 58777 (by norm_num) ⟨29388, by rfl⟩ (by norm_num))
theorem R78373 : Reach 78373 := rs (se 4 (by rfl) ⟨7347, by rfl⟩) (B 14695 (by norm_num) ⟨7347, by rfl⟩ (by norm_num))
theorem R78377 : Reach 78377 := rs (se 2 (by rfl) ⟨29391, by rfl⟩) (B 58783 (by norm_num) ⟨29391, by rfl⟩ (by norm_num))
theorem R78381 : Reach 78381 := rs (se 3 (by rfl) ⟨14696, by rfl⟩) (B 29393 (by norm_num) ⟨14696, by rfl⟩ (by norm_num))
theorem R78385 : Reach 78385 := rs (se 2 (by rfl) ⟨29394, by rfl⟩) (B 58789 (by norm_num) ⟨29394, by rfl⟩ (by norm_num))
theorem R78389 : Reach 78389 := rs (se 5 (by rfl) ⟨3674, by rfl⟩) (B 7349 (by norm_num) ⟨3674, by rfl⟩ (by norm_num))
theorem R78393 : Reach 78393 := rs (se 2 (by rfl) ⟨29397, by rfl⟩) (B 58795 (by norm_num) ⟨29397, by rfl⟩ (by norm_num))
theorem R78397 : Reach 78397 := rs (se 3 (by rfl) ⟨14699, by rfl⟩) (B 29399 (by norm_num) ⟨14699, by rfl⟩ (by norm_num))
theorem R78401 : Reach 78401 := rs (se 2 (by rfl) ⟨29400, by rfl⟩) (B 58801 (by norm_num) ⟨29400, by rfl⟩ (by norm_num))
theorem R78405 : Reach 78405 := rs (se 4 (by rfl) ⟨7350, by rfl⟩) (B 14701 (by norm_num) ⟨7350, by rfl⟩ (by norm_num))
theorem R78409 : Reach 78409 := rs (se 2 (by rfl) ⟨29403, by rfl⟩) (B 58807 (by norm_num) ⟨29403, by rfl⟩ (by norm_num))
theorem R78413 : Reach 78413 := rs (se 3 (by rfl) ⟨14702, by rfl⟩) (B 29405 (by norm_num) ⟨14702, by rfl⟩ (by norm_num))
theorem R78417 : Reach 78417 := rs (se 2 (by rfl) ⟨29406, by rfl⟩) (B 58813 (by norm_num) ⟨29406, by rfl⟩ (by norm_num))
theorem R78421 : Reach 78421 := rs (se 8 (by rfl) ⟨459, by rfl⟩) (B 919 (by norm_num) ⟨459, by rfl⟩ (by norm_num))
theorem R78425 : Reach 78425 := rs (se 2 (by rfl) ⟨29409, by rfl⟩) (B 58819 (by norm_num) ⟨29409, by rfl⟩ (by norm_num))
theorem R78429 : Reach 78429 := rs (se 3 (by rfl) ⟨14705, by rfl⟩) (B 29411 (by norm_num) ⟨14705, by rfl⟩ (by norm_num))
theorem R78433 : Reach 78433 := rs (se 2 (by rfl) ⟨29412, by rfl⟩) (B 58825 (by norm_num) ⟨29412, by rfl⟩ (by norm_num))
theorem R78437 : Reach 78437 := rs (se 4 (by rfl) ⟨7353, by rfl⟩) (B 14707 (by norm_num) ⟨7353, by rfl⟩ (by norm_num))
theorem R176741 : Reach 176741 := rs (se 4 (by rfl) ⟨16569, by rfl⟩) (B 33139 (by norm_num) ⟨16569, by rfl⟩ (by norm_num))
theorem R78441 : Reach 78441 := rs (se 2 (by rfl) ⟨29415, by rfl⟩) (B 58831 (by norm_num) ⟨29415, by rfl⟩ (by norm_num))
theorem R78445 : Reach 78445 := rs (se 3 (by rfl) ⟨14708, by rfl⟩) (B 29417 (by norm_num) ⟨14708, by rfl⟩ (by norm_num))
theorem R78449 : Reach 78449 := rs (se 2 (by rfl) ⟨29418, by rfl⟩) (B 58837 (by norm_num) ⟨29418, by rfl⟩ (by norm_num))
theorem R78453 : Reach 78453 := rs (se 5 (by rfl) ⟨3677, by rfl⟩) (B 7355 (by norm_num) ⟨3677, by rfl⟩ (by norm_num))
theorem R78457 : Reach 78457 := rs (se 2 (by rfl) ⟨29421, by rfl⟩) (B 58843 (by norm_num) ⟨29421, by rfl⟩ (by norm_num))
theorem R78461 : Reach 78461 := rs (se 3 (by rfl) ⟨14711, by rfl⟩) (B 29423 (by norm_num) ⟨14711, by rfl⟩ (by norm_num))
theorem R78465 : Reach 78465 := rs (se 2 (by rfl) ⟨29424, by rfl⟩) (B 58849 (by norm_num) ⟨29424, by rfl⟩ (by norm_num))
theorem R78469 : Reach 78469 := rs (se 4 (by rfl) ⟨7356, by rfl⟩) (B 14713 (by norm_num) ⟨7356, by rfl⟩ (by norm_num))
theorem R78473 : Reach 78473 := rs (se 2 (by rfl) ⟨29427, by rfl⟩) (B 58855 (by norm_num) ⟨29427, by rfl⟩ (by norm_num))
theorem R78477 : Reach 78477 := rs (se 3 (by rfl) ⟨14714, by rfl⟩) (B 29429 (by norm_num) ⟨14714, by rfl⟩ (by norm_num))
theorem R78481 : Reach 78481 := rs (se 2 (by rfl) ⟨29430, by rfl⟩) (B 58861 (by norm_num) ⟨29430, by rfl⟩ (by norm_num))
theorem R78485 : Reach 78485 := rs (se 6 (by rfl) ⟨1839, by rfl⟩) (B 3679 (by norm_num) ⟨1839, by rfl⟩ (by norm_num))
theorem R78489 : Reach 78489 := rs (se 2 (by rfl) ⟨29433, by rfl⟩) (B 58867 (by norm_num) ⟨29433, by rfl⟩ (by norm_num))
theorem R78493 : Reach 78493 := rs (se 3 (by rfl) ⟨14717, by rfl⟩) (B 29435 (by norm_num) ⟨14717, by rfl⟩ (by norm_num))
theorem R78497 : Reach 78497 := rs (se 2 (by rfl) ⟨29436, by rfl⟩) (B 58873 (by norm_num) ⟨29436, by rfl⟩ (by norm_num))
theorem R78501 : Reach 78501 := rs (se 4 (by rfl) ⟨7359, by rfl⟩) (B 14719 (by norm_num) ⟨7359, by rfl⟩ (by norm_num))
theorem R78505 : Reach 78505 := rs (se 2 (by rfl) ⟨29439, by rfl⟩) (B 58879 (by norm_num) ⟨29439, by rfl⟩ (by norm_num))
theorem R78509 : Reach 78509 := rs (se 3 (by rfl) ⟨14720, by rfl⟩) (B 29441 (by norm_num) ⟨14720, by rfl⟩ (by norm_num))
theorem R176813 : Reach 176813 := rs (se 3 (by rfl) ⟨33152, by rfl⟩) (B 66305 (by norm_num) ⟨33152, by rfl⟩ (by norm_num))
theorem R78513 : Reach 78513 := rs (se 2 (by rfl) ⟨29442, by rfl⟩) (B 58885 (by norm_num) ⟨29442, by rfl⟩ (by norm_num))
theorem R78517 : Reach 78517 := rs (se 5 (by rfl) ⟨3680, by rfl⟩) (B 7361 (by norm_num) ⟨3680, by rfl⟩ (by norm_num))
theorem R78521 : Reach 78521 := rs (se 2 (by rfl) ⟨29445, by rfl⟩) (B 58891 (by norm_num) ⟨29445, by rfl⟩ (by norm_num))
theorem R78525 : Reach 78525 := rs (se 3 (by rfl) ⟨14723, by rfl⟩) (B 29447 (by norm_num) ⟨14723, by rfl⟩ (by norm_num))
theorem R78529 : Reach 78529 := rs (se 2 (by rfl) ⟨29448, by rfl⟩) (B 58897 (by norm_num) ⟨29448, by rfl⟩ (by norm_num))
theorem R78533 : Reach 78533 := rs (se 4 (by rfl) ⟨7362, by rfl⟩) (B 14725 (by norm_num) ⟨7362, by rfl⟩ (by norm_num))
theorem R78537 : Reach 78537 := rs (se 2 (by rfl) ⟨29451, by rfl⟩) (B 58903 (by norm_num) ⟨29451, by rfl⟩ (by norm_num))
theorem R78541 : Reach 78541 := rs (se 3 (by rfl) ⟨14726, by rfl⟩) (B 29453 (by norm_num) ⟨14726, by rfl⟩ (by norm_num))
theorem R78545 : Reach 78545 := rs (se 2 (by rfl) ⟨29454, by rfl⟩) (B 58909 (by norm_num) ⟨29454, by rfl⟩ (by norm_num))
theorem R78549 : Reach 78549 := rs (se 7 (by rfl) ⟨920, by rfl⟩) (B 1841 (by norm_num) ⟨920, by rfl⟩ (by norm_num))
theorem R78553 : Reach 78553 := rs (se 2 (by rfl) ⟨29457, by rfl⟩) (B 58915 (by norm_num) ⟨29457, by rfl⟩ (by norm_num))
theorem R78557 : Reach 78557 := rs (se 3 (by rfl) ⟨14729, by rfl⟩) (B 29459 (by norm_num) ⟨14729, by rfl⟩ (by norm_num))
theorem R78561 : Reach 78561 := rs (se 2 (by rfl) ⟨29460, by rfl⟩) (B 58921 (by norm_num) ⟨29460, by rfl⟩ (by norm_num))
theorem R78565 : Reach 78565 := rs (se 4 (by rfl) ⟨7365, by rfl⟩) (B 14731 (by norm_num) ⟨7365, by rfl⟩ (by norm_num))
theorem R78569 : Reach 78569 := rs (se 2 (by rfl) ⟨29463, by rfl⟩) (B 58927 (by norm_num) ⟨29463, by rfl⟩ (by norm_num))
theorem R78573 : Reach 78573 := rs (se 3 (by rfl) ⟨14732, by rfl⟩) (B 29465 (by norm_num) ⟨14732, by rfl⟩ (by norm_num))
theorem R78577 : Reach 78577 := rs (se 2 (by rfl) ⟨29466, by rfl⟩) (B 58933 (by norm_num) ⟨29466, by rfl⟩ (by norm_num))
theorem R78581 : Reach 78581 := rs (se 5 (by rfl) ⟨3683, by rfl⟩) (B 7367 (by norm_num) ⟨3683, by rfl⟩ (by norm_num))
theorem R176885 : Reach 176885 := rs (se 5 (by rfl) ⟨8291, by rfl⟩) (B 16583 (by norm_num) ⟨8291, by rfl⟩ (by norm_num))
theorem R78585 : Reach 78585 := rs (se 2 (by rfl) ⟨29469, by rfl⟩) (B 58939 (by norm_num) ⟨29469, by rfl⟩ (by norm_num))
theorem R78589 : Reach 78589 := rs (se 3 (by rfl) ⟨14735, by rfl⟩) (B 29471 (by norm_num) ⟨14735, by rfl⟩ (by norm_num))
theorem R78593 : Reach 78593 := rs (se 2 (by rfl) ⟨29472, by rfl⟩) (B 58945 (by norm_num) ⟨29472, by rfl⟩ (by norm_num))
theorem R78597 : Reach 78597 := rs (se 4 (by rfl) ⟨7368, by rfl⟩) (B 14737 (by norm_num) ⟨7368, by rfl⟩ (by norm_num))
theorem R78601 : Reach 78601 := rs (se 2 (by rfl) ⟨29475, by rfl⟩) (B 58951 (by norm_num) ⟨29475, by rfl⟩ (by norm_num))
theorem R78605 : Reach 78605 := rs (se 3 (by rfl) ⟨14738, by rfl⟩) (B 29477 (by norm_num) ⟨14738, by rfl⟩ (by norm_num))
theorem R78609 : Reach 78609 := rs (se 2 (by rfl) ⟨29478, by rfl⟩) (B 58957 (by norm_num) ⟨29478, by rfl⟩ (by norm_num))
theorem R78613 : Reach 78613 := rs (se 6 (by rfl) ⟨1842, by rfl⟩) (B 3685 (by norm_num) ⟨1842, by rfl⟩ (by norm_num))
theorem R78617 : Reach 78617 := rs (se 2 (by rfl) ⟨29481, by rfl⟩) (B 58963 (by norm_num) ⟨29481, by rfl⟩ (by norm_num))
theorem R78621 : Reach 78621 := rs (se 3 (by rfl) ⟨14741, by rfl⟩) (B 29483 (by norm_num) ⟨14741, by rfl⟩ (by norm_num))
theorem R78625 : Reach 78625 := rs (se 2 (by rfl) ⟨29484, by rfl⟩) (B 58969 (by norm_num) ⟨29484, by rfl⟩ (by norm_num))
theorem R78629 : Reach 78629 := rs (se 4 (by rfl) ⟨7371, by rfl⟩) (B 14743 (by norm_num) ⟨7371, by rfl⟩ (by norm_num))
theorem R78633 : Reach 78633 := rs (se 2 (by rfl) ⟨29487, by rfl⟩) (B 58975 (by norm_num) ⟨29487, by rfl⟩ (by norm_num))
theorem R78637 : Reach 78637 := rs (se 3 (by rfl) ⟨14744, by rfl⟩) (B 29489 (by norm_num) ⟨14744, by rfl⟩ (by norm_num))
theorem R78641 : Reach 78641 := rs (se 2 (by rfl) ⟨29490, by rfl⟩) (B 58981 (by norm_num) ⟨29490, by rfl⟩ (by norm_num))
theorem R78645 : Reach 78645 := rs (se 5 (by rfl) ⟨3686, by rfl⟩) (B 7373 (by norm_num) ⟨3686, by rfl⟩ (by norm_num))
theorem R78649 : Reach 78649 := rs (se 2 (by rfl) ⟨29493, by rfl⟩) (B 58987 (by norm_num) ⟨29493, by rfl⟩ (by norm_num))
theorem R176957 : Reach 176957 := rs (se 3 (by rfl) ⟨33179, by rfl⟩) (B 66359 (by norm_num) ⟨33179, by rfl⟩ (by norm_num))
theorem R78653 : Reach 78653 := rs (se 3 (by rfl) ⟨14747, by rfl⟩) (B 29495 (by norm_num) ⟨14747, by rfl⟩ (by norm_num))
theorem R78657 : Reach 78657 := rs (se 2 (by rfl) ⟨29496, by rfl⟩) (B 58993 (by norm_num) ⟨29496, by rfl⟩ (by norm_num))
theorem R78661 : Reach 78661 := rs (se 4 (by rfl) ⟨7374, by rfl⟩) (B 14749 (by norm_num) ⟨7374, by rfl⟩ (by norm_num))
theorem R78665 : Reach 78665 := rs (se 2 (by rfl) ⟨29499, by rfl⟩) (B 58999 (by norm_num) ⟨29499, by rfl⟩ (by norm_num))
theorem R78669 : Reach 78669 := rs (se 3 (by rfl) ⟨14750, by rfl⟩) (B 29501 (by norm_num) ⟨14750, by rfl⟩ (by norm_num))
theorem R78673 : Reach 78673 := rs (se 2 (by rfl) ⟨29502, by rfl⟩) (B 59005 (by norm_num) ⟨29502, by rfl⟩ (by norm_num))
theorem R78677 : Reach 78677 := rs (se 9 (by rfl) ⟨230, by rfl⟩) (B 461 (by norm_num) ⟨230, by rfl⟩ (by norm_num))
theorem R78681 : Reach 78681 := rs (se 2 (by rfl) ⟨29505, by rfl⟩) (B 59011 (by norm_num) ⟨29505, by rfl⟩ (by norm_num))
theorem R78685 : Reach 78685 := rs (se 3 (by rfl) ⟨14753, by rfl⟩) (B 29507 (by norm_num) ⟨14753, by rfl⟩ (by norm_num))
theorem R78689 : Reach 78689 := rs (se 2 (by rfl) ⟨29508, by rfl⟩) (B 59017 (by norm_num) ⟨29508, by rfl⟩ (by norm_num))
theorem R78693 : Reach 78693 := rs (se 4 (by rfl) ⟨7377, by rfl⟩) (B 14755 (by norm_num) ⟨7377, by rfl⟩ (by norm_num))
theorem R78697 : Reach 78697 := rs (se 2 (by rfl) ⟨29511, by rfl⟩) (B 59023 (by norm_num) ⟨29511, by rfl⟩ (by norm_num))
theorem R111469 : Reach 111469 := rs (se 3 (by rfl) ⟨20900, by rfl⟩) (B 41801 (by norm_num) ⟨20900, by rfl⟩ (by norm_num))
theorem R78701 : Reach 78701 := rs (se 3 (by rfl) ⟨14756, by rfl⟩) (B 29513 (by norm_num) ⟨14756, by rfl⟩ (by norm_num))
theorem R78705 : Reach 78705 := rs (se 2 (by rfl) ⟨29514, by rfl⟩) (B 59029 (by norm_num) ⟨29514, by rfl⟩ (by norm_num))
theorem R78709 : Reach 78709 := rs (se 5 (by rfl) ⟨3689, by rfl⟩) (B 7379 (by norm_num) ⟨3689, by rfl⟩ (by norm_num))
theorem R78713 : Reach 78713 := rs (se 2 (by rfl) ⟨29517, by rfl⟩) (B 59035 (by norm_num) ⟨29517, by rfl⟩ (by norm_num))
theorem R78717 : Reach 78717 := rs (se 3 (by rfl) ⟨14759, by rfl⟩) (B 29519 (by norm_num) ⟨14759, by rfl⟩ (by norm_num))
theorem R78721 : Reach 78721 := rs (se 2 (by rfl) ⟨29520, by rfl⟩) (B 59041 (by norm_num) ⟨29520, by rfl⟩ (by norm_num))
theorem R177029 : Reach 177029 := rs (se 4 (by rfl) ⟨16596, by rfl⟩) (B 33193 (by norm_num) ⟨16596, by rfl⟩ (by norm_num))
theorem R78725 : Reach 78725 := rs (se 4 (by rfl) ⟨7380, by rfl⟩) (B 14761 (by norm_num) ⟨7380, by rfl⟩ (by norm_num))
theorem R78729 : Reach 78729 := rs (se 2 (by rfl) ⟨29523, by rfl⟩) (B 59047 (by norm_num) ⟨29523, by rfl⟩ (by norm_num))
theorem R78733 : Reach 78733 := rs (se 3 (by rfl) ⟨14762, by rfl⟩) (B 29525 (by norm_num) ⟨14762, by rfl⟩ (by norm_num))
theorem R78737 : Reach 78737 := rs (se 2 (by rfl) ⟨29526, by rfl⟩) (B 59053 (by norm_num) ⟨29526, by rfl⟩ (by norm_num))
theorem R78741 : Reach 78741 := rs (se 6 (by rfl) ⟨1845, by rfl⟩) (B 3691 (by norm_num) ⟨1845, by rfl⟩ (by norm_num))
theorem R78745 : Reach 78745 := rs (se 2 (by rfl) ⟨29529, by rfl⟩) (B 59059 (by norm_num) ⟨29529, by rfl⟩ (by norm_num))
theorem R78749 : Reach 78749 := rs (se 3 (by rfl) ⟨14765, by rfl⟩) (B 29531 (by norm_num) ⟨14765, by rfl⟩ (by norm_num))
theorem R78753 : Reach 78753 := rs (se 2 (by rfl) ⟨29532, by rfl⟩) (B 59065 (by norm_num) ⟨29532, by rfl⟩ (by norm_num))
theorem R78757 : Reach 78757 := rs (se 4 (by rfl) ⟨7383, by rfl⟩) (B 14767 (by norm_num) ⟨7383, by rfl⟩ (by norm_num))
theorem R78761 : Reach 78761 := rs (se 2 (by rfl) ⟨29535, by rfl⟩) (B 59071 (by norm_num) ⟨29535, by rfl⟩ (by norm_num))
theorem R78765 : Reach 78765 := rs (se 3 (by rfl) ⟨14768, by rfl⟩) (B 29537 (by norm_num) ⟨14768, by rfl⟩ (by norm_num))
theorem R78769 : Reach 78769 := rs (se 2 (by rfl) ⟨29538, by rfl⟩) (B 59077 (by norm_num) ⟨29538, by rfl⟩ (by norm_num))
theorem R78773 : Reach 78773 := rs (se 5 (by rfl) ⟨3692, by rfl⟩) (B 7385 (by norm_num) ⟨3692, by rfl⟩ (by norm_num))
theorem R78777 : Reach 78777 := rs (se 2 (by rfl) ⟨29541, by rfl⟩) (B 59083 (by norm_num) ⟨29541, by rfl⟩ (by norm_num))
theorem R78781 : Reach 78781 := rs (se 3 (by rfl) ⟨14771, by rfl⟩) (B 29543 (by norm_num) ⟨14771, by rfl⟩ (by norm_num))
theorem R78785 : Reach 78785 := rs (se 2 (by rfl) ⟨29544, by rfl⟩) (B 59089 (by norm_num) ⟨29544, by rfl⟩ (by norm_num))
theorem R78789 : Reach 78789 := rs (se 4 (by rfl) ⟨7386, by rfl⟩) (B 14773 (by norm_num) ⟨7386, by rfl⟩ (by norm_num))
theorem R78793 : Reach 78793 := rs (se 2 (by rfl) ⟨29547, by rfl⟩) (B 59095 (by norm_num) ⟨29547, by rfl⟩ (by norm_num))
theorem R177101 : Reach 177101 := rs (se 3 (by rfl) ⟨33206, by rfl⟩) (B 66413 (by norm_num) ⟨33206, by rfl⟩ (by norm_num))
theorem R78797 : Reach 78797 := rs (se 3 (by rfl) ⟨14774, by rfl⟩) (B 29549 (by norm_num) ⟨14774, by rfl⟩ (by norm_num))
theorem R78801 : Reach 78801 := rs (se 2 (by rfl) ⟨29550, by rfl⟩) (B 59101 (by norm_num) ⟨29550, by rfl⟩ (by norm_num))
theorem R78805 : Reach 78805 := rs (se 7 (by rfl) ⟨923, by rfl⟩) (B 1847 (by norm_num) ⟨923, by rfl⟩ (by norm_num))
theorem R78809 : Reach 78809 := rs (se 2 (by rfl) ⟨29553, by rfl⟩) (B 59107 (by norm_num) ⟨29553, by rfl⟩ (by norm_num))
theorem R78813 : Reach 78813 := rs (se 3 (by rfl) ⟨14777, by rfl⟩) (B 29555 (by norm_num) ⟨14777, by rfl⟩ (by norm_num))
theorem R78817 : Reach 78817 := rs (se 2 (by rfl) ⟨29556, by rfl⟩) (B 59113 (by norm_num) ⟨29556, by rfl⟩ (by norm_num))
theorem R78821 : Reach 78821 := rs (se 4 (by rfl) ⟨7389, by rfl⟩) (B 14779 (by norm_num) ⟨7389, by rfl⟩ (by norm_num))
theorem R78825 : Reach 78825 := rs (se 2 (by rfl) ⟨29559, by rfl⟩) (B 59119 (by norm_num) ⟨29559, by rfl⟩ (by norm_num))
theorem R78829 : Reach 78829 := rs (se 3 (by rfl) ⟨14780, by rfl⟩) (B 29561 (by norm_num) ⟨14780, by rfl⟩ (by norm_num))
theorem R78833 : Reach 78833 := rs (se 2 (by rfl) ⟨29562, by rfl⟩) (B 59125 (by norm_num) ⟨29562, by rfl⟩ (by norm_num))
theorem R78837 : Reach 78837 := rs (se 5 (by rfl) ⟨3695, by rfl⟩) (B 7391 (by norm_num) ⟨3695, by rfl⟩ (by norm_num))
theorem R78841 : Reach 78841 := rs (se 2 (by rfl) ⟨29565, by rfl⟩) (B 59131 (by norm_num) ⟨29565, by rfl⟩ (by norm_num))
theorem R78845 : Reach 78845 := rs (se 3 (by rfl) ⟨14783, by rfl⟩) (B 29567 (by norm_num) ⟨14783, by rfl⟩ (by norm_num))
theorem R78849 : Reach 78849 := rs (se 2 (by rfl) ⟨29568, by rfl⟩) (B 59137 (by norm_num) ⟨29568, by rfl⟩ (by norm_num))
theorem R78853 : Reach 78853 := rs (se 4 (by rfl) ⟨7392, by rfl⟩) (B 14785 (by norm_num) ⟨7392, by rfl⟩ (by norm_num))
theorem R78857 : Reach 78857 := rs (se 2 (by rfl) ⟨29571, by rfl⟩) (B 59143 (by norm_num) ⟨29571, by rfl⟩ (by norm_num))
theorem R78861 : Reach 78861 := rs (se 3 (by rfl) ⟨14786, by rfl⟩) (B 29573 (by norm_num) ⟨14786, by rfl⟩ (by norm_num))
theorem R78865 : Reach 78865 := rs (se 2 (by rfl) ⟨29574, by rfl⟩) (B 59149 (by norm_num) ⟨29574, by rfl⟩ (by norm_num))
theorem R177173 : Reach 177173 := rs (se 6 (by rfl) ⟨4152, by rfl⟩) (B 8305 (by norm_num) ⟨4152, by rfl⟩ (by norm_num))
theorem R78869 : Reach 78869 := rs (se 6 (by rfl) ⟨1848, by rfl⟩) (B 3697 (by norm_num) ⟨1848, by rfl⟩ (by norm_num))
theorem R78873 : Reach 78873 := rs (se 2 (by rfl) ⟨29577, by rfl⟩) (B 59155 (by norm_num) ⟨29577, by rfl⟩ (by norm_num))
theorem R78877 : Reach 78877 := rs (se 3 (by rfl) ⟨14789, by rfl⟩) (B 29579 (by norm_num) ⟨14789, by rfl⟩ (by norm_num))
theorem R78881 : Reach 78881 := rs (se 2 (by rfl) ⟨29580, by rfl⟩) (B 59161 (by norm_num) ⟨29580, by rfl⟩ (by norm_num))
theorem R78885 : Reach 78885 := rs (se 4 (by rfl) ⟨7395, by rfl⟩) (B 14791 (by norm_num) ⟨7395, by rfl⟩ (by norm_num))
theorem R78889 : Reach 78889 := rs (se 2 (by rfl) ⟨29583, by rfl⟩) (B 59167 (by norm_num) ⟨29583, by rfl⟩ (by norm_num))
theorem R78893 : Reach 78893 := rs (se 3 (by rfl) ⟨14792, by rfl⟩) (B 29585 (by norm_num) ⟨14792, by rfl⟩ (by norm_num))
theorem R78897 : Reach 78897 := rs (se 2 (by rfl) ⟨29586, by rfl⟩) (B 59173 (by norm_num) ⟨29586, by rfl⟩ (by norm_num))
theorem R78901 : Reach 78901 := rs (se 5 (by rfl) ⟨3698, by rfl⟩) (B 7397 (by norm_num) ⟨3698, by rfl⟩ (by norm_num))
theorem R78905 : Reach 78905 := rs (se 2 (by rfl) ⟨29589, by rfl⟩) (B 59179 (by norm_num) ⟨29589, by rfl⟩ (by norm_num))
theorem R78909 : Reach 78909 := rs (se 3 (by rfl) ⟨14795, by rfl⟩) (B 29591 (by norm_num) ⟨14795, by rfl⟩ (by norm_num))
theorem R78913 : Reach 78913 := rs (se 2 (by rfl) ⟨29592, by rfl⟩) (B 59185 (by norm_num) ⟨29592, by rfl⟩ (by norm_num))
theorem R275525 : Reach 275525 := rs (se 4 (by rfl) ⟨25830, by rfl⟩) (B 51661 (by norm_num) ⟨25830, by rfl⟩ (by norm_num))
theorem R78917 : Reach 78917 := rs (se 4 (by rfl) ⟨7398, by rfl⟩) (B 14797 (by norm_num) ⟨7398, by rfl⟩ (by norm_num))
theorem R78921 : Reach 78921 := rs (se 2 (by rfl) ⟨29595, by rfl⟩) (B 59191 (by norm_num) ⟨29595, by rfl⟩ (by norm_num))
theorem R78925 : Reach 78925 := rs (se 3 (by rfl) ⟨14798, by rfl⟩) (B 29597 (by norm_num) ⟨14798, by rfl⟩ (by norm_num))
theorem R78929 : Reach 78929 := rs (se 2 (by rfl) ⟨29598, by rfl⟩) (B 59197 (by norm_num) ⟨29598, by rfl⟩ (by norm_num))
theorem R78933 : Reach 78933 := rs (se 8 (by rfl) ⟨462, by rfl⟩) (B 925 (by norm_num) ⟨462, by rfl⟩ (by norm_num))
theorem R78937 : Reach 78937 := rs (se 2 (by rfl) ⟨29601, by rfl⟩) (B 59203 (by norm_num) ⟨29601, by rfl⟩ (by norm_num))
theorem R177245 : Reach 177245 := rs (se 3 (by rfl) ⟨33233, by rfl⟩) (B 66467 (by norm_num) ⟨33233, by rfl⟩ (by norm_num))
theorem R78941 : Reach 78941 := rs (se 3 (by rfl) ⟨14801, by rfl⟩) (B 29603 (by norm_num) ⟨14801, by rfl⟩ (by norm_num))
theorem R78945 : Reach 78945 := rs (se 2 (by rfl) ⟨29604, by rfl⟩) (B 59209 (by norm_num) ⟨29604, by rfl⟩ (by norm_num))
theorem R78949 : Reach 78949 := rs (se 4 (by rfl) ⟨7401, by rfl⟩) (B 14803 (by norm_num) ⟨7401, by rfl⟩ (by norm_num))
theorem R78953 : Reach 78953 := rs (se 2 (by rfl) ⟨29607, by rfl⟩) (B 59215 (by norm_num) ⟨29607, by rfl⟩ (by norm_num))
theorem R78957 : Reach 78957 := rs (se 3 (by rfl) ⟨14804, by rfl⟩) (B 29609 (by norm_num) ⟨14804, by rfl⟩ (by norm_num))
theorem R78961 : Reach 78961 := rs (se 2 (by rfl) ⟨29610, by rfl⟩) (B 59221 (by norm_num) ⟨29610, by rfl⟩ (by norm_num))
theorem R78965 : Reach 78965 := rs (se 5 (by rfl) ⟨3701, by rfl⟩) (B 7403 (by norm_num) ⟨3701, by rfl⟩ (by norm_num))
theorem R78969 : Reach 78969 := rs (se 2 (by rfl) ⟨29613, by rfl⟩) (B 59227 (by norm_num) ⟨29613, by rfl⟩ (by norm_num))
theorem R78973 : Reach 78973 := rs (se 3 (by rfl) ⟨14807, by rfl⟩) (B 29615 (by norm_num) ⟨14807, by rfl⟩ (by norm_num))
theorem R78977 : Reach 78977 := rs (se 2 (by rfl) ⟨29616, by rfl⟩) (B 59233 (by norm_num) ⟨29616, by rfl⟩ (by norm_num))
theorem R144517 : Reach 144517 := rs (se 4 (by rfl) ⟨13548, by rfl⟩) (B 27097 (by norm_num) ⟨13548, by rfl⟩ (by norm_num))
theorem R78981 : Reach 78981 := rs (se 4 (by rfl) ⟨7404, by rfl⟩) (B 14809 (by norm_num) ⟨7404, by rfl⟩ (by norm_num))
theorem R78985 : Reach 78985 := rs (se 2 (by rfl) ⟨29619, by rfl⟩) (B 59239 (by norm_num) ⟨29619, by rfl⟩ (by norm_num))
theorem R78989 : Reach 78989 := rs (se 3 (by rfl) ⟨14810, by rfl⟩) (B 29621 (by norm_num) ⟨14810, by rfl⟩ (by norm_num))
theorem R78993 : Reach 78993 := rs (se 2 (by rfl) ⟨29622, by rfl⟩) (B 59245 (by norm_num) ⟨29622, by rfl⟩ (by norm_num))
theorem R78997 : Reach 78997 := rs (se 6 (by rfl) ⟨1851, by rfl⟩) (B 3703 (by norm_num) ⟨1851, by rfl⟩ (by norm_num))
theorem R79001 : Reach 79001 := rs (se 2 (by rfl) ⟨29625, by rfl⟩) (B 59251 (by norm_num) ⟨29625, by rfl⟩ (by norm_num))
theorem R79005 : Reach 79005 := rs (se 3 (by rfl) ⟨14813, by rfl⟩) (B 29627 (by norm_num) ⟨14813, by rfl⟩ (by norm_num))
theorem R79009 : Reach 79009 := rs (se 2 (by rfl) ⟨29628, by rfl⟩) (B 59257 (by norm_num) ⟨29628, by rfl⟩ (by norm_num))
theorem R177317 : Reach 177317 := rs (se 4 (by rfl) ⟨16623, by rfl⟩) (B 33247 (by norm_num) ⟨16623, by rfl⟩ (by norm_num))
theorem R79013 : Reach 79013 := rs (se 4 (by rfl) ⟨7407, by rfl⟩) (B 14815 (by norm_num) ⟨7407, by rfl⟩ (by norm_num))
theorem R79017 : Reach 79017 := rs (se 2 (by rfl) ⟨29631, by rfl⟩) (B 59263 (by norm_num) ⟨29631, by rfl⟩ (by norm_num))
theorem R79021 : Reach 79021 := rs (se 3 (by rfl) ⟨14816, by rfl⟩) (B 29633 (by norm_num) ⟨14816, by rfl⟩ (by norm_num))
theorem R79025 : Reach 79025 := rs (se 2 (by rfl) ⟨29634, by rfl⟩) (B 59269 (by norm_num) ⟨29634, by rfl⟩ (by norm_num))
theorem R79029 : Reach 79029 := rs (se 5 (by rfl) ⟨3704, by rfl⟩) (B 7409 (by norm_num) ⟨3704, by rfl⟩ (by norm_num))
theorem R79033 : Reach 79033 := rs (se 2 (by rfl) ⟨29637, by rfl⟩) (B 59275 (by norm_num) ⟨29637, by rfl⟩ (by norm_num))
theorem R79037 : Reach 79037 := rs (se 3 (by rfl) ⟨14819, by rfl⟩) (B 29639 (by norm_num) ⟨14819, by rfl⟩ (by norm_num))
theorem R79041 : Reach 79041 := rs (se 2 (by rfl) ⟨29640, by rfl⟩) (B 59281 (by norm_num) ⟨29640, by rfl⟩ (by norm_num))
theorem R177349 : Reach 177349 := rs (se 4 (by rfl) ⟨16626, by rfl⟩) (B 33253 (by norm_num) ⟨16626, by rfl⟩ (by norm_num))
theorem R79045 : Reach 79045 := rs (se 4 (by rfl) ⟨7410, by rfl⟩) (B 14821 (by norm_num) ⟨7410, by rfl⟩ (by norm_num))
theorem R79049 : Reach 79049 := rs (se 2 (by rfl) ⟨29643, by rfl⟩) (B 59287 (by norm_num) ⟨29643, by rfl⟩ (by norm_num))
theorem R79053 : Reach 79053 := rs (se 3 (by rfl) ⟨14822, by rfl⟩) (B 29645 (by norm_num) ⟨14822, by rfl⟩ (by norm_num))
theorem R79057 : Reach 79057 := rs (se 2 (by rfl) ⟨29646, by rfl⟩) (B 59293 (by norm_num) ⟨29646, by rfl⟩ (by norm_num))
theorem R79061 : Reach 79061 := rs (se 7 (by rfl) ⟨926, by rfl⟩) (B 1853 (by norm_num) ⟨926, by rfl⟩ (by norm_num))
theorem R79065 : Reach 79065 := rs (se 2 (by rfl) ⟨29649, by rfl⟩) (B 59299 (by norm_num) ⟨29649, by rfl⟩ (by norm_num))
theorem R79069 : Reach 79069 := rs (se 3 (by rfl) ⟨14825, by rfl⟩) (B 29651 (by norm_num) ⟨14825, by rfl⟩ (by norm_num))
theorem R79073 : Reach 79073 := rs (se 2 (by rfl) ⟨29652, by rfl⟩) (B 59305 (by norm_num) ⟨29652, by rfl⟩ (by norm_num))
theorem R79077 : Reach 79077 := rs (se 4 (by rfl) ⟨7413, by rfl⟩) (B 14827 (by norm_num) ⟨7413, by rfl⟩ (by norm_num))
theorem R79081 : Reach 79081 := rs (se 2 (by rfl) ⟨29655, by rfl⟩) (B 59311 (by norm_num) ⟨29655, by rfl⟩ (by norm_num))
theorem R177389 : Reach 177389 := rs (se 3 (by rfl) ⟨33260, by rfl⟩) (B 66521 (by norm_num) ⟨33260, by rfl⟩ (by norm_num))
theorem R79085 : Reach 79085 := rs (se 3 (by rfl) ⟨14828, by rfl⟩) (B 29657 (by norm_num) ⟨14828, by rfl⟩ (by norm_num))
theorem R79089 : Reach 79089 := rs (se 2 (by rfl) ⟨29658, by rfl⟩) (B 59317 (by norm_num) ⟨29658, by rfl⟩ (by norm_num))
theorem R79093 : Reach 79093 := rs (se 5 (by rfl) ⟨3707, by rfl⟩) (B 7415 (by norm_num) ⟨3707, by rfl⟩ (by norm_num))
theorem R79097 : Reach 79097 := rs (se 2 (by rfl) ⟨29661, by rfl⟩) (B 59323 (by norm_num) ⟨29661, by rfl⟩ (by norm_num))
theorem R79101 : Reach 79101 := rs (se 3 (by rfl) ⟨14831, by rfl⟩) (B 29663 (by norm_num) ⟨14831, by rfl⟩ (by norm_num))
theorem R79105 : Reach 79105 := rs (se 2 (by rfl) ⟨29664, by rfl⟩) (B 59329 (by norm_num) ⟨29664, by rfl⟩ (by norm_num))
theorem R79109 : Reach 79109 := rs (se 4 (by rfl) ⟨7416, by rfl⟩) (B 14833 (by norm_num) ⟨7416, by rfl⟩ (by norm_num))
theorem R79113 : Reach 79113 := rs (se 2 (by rfl) ⟨29667, by rfl⟩) (B 59335 (by norm_num) ⟨29667, by rfl⟩ (by norm_num))
theorem R79117 : Reach 79117 := rs (se 3 (by rfl) ⟨14834, by rfl⟩) (B 29669 (by norm_num) ⟨14834, by rfl⟩ (by norm_num))
theorem R79121 : Reach 79121 := rs (se 2 (by rfl) ⟨29670, by rfl⟩) (B 59341 (by norm_num) ⟨29670, by rfl⟩ (by norm_num))
theorem R144661 : Reach 144661 := rs (se 6 (by rfl) ⟨3390, by rfl⟩) (B 6781 (by norm_num) ⟨3390, by rfl⟩ (by norm_num))
theorem R79125 : Reach 79125 := rs (se 6 (by rfl) ⟨1854, by rfl⟩) (B 3709 (by norm_num) ⟨1854, by rfl⟩ (by norm_num))
theorem R177461 : Reach 177461 := rs (se 5 (by rfl) ⟨8318, by rfl⟩) (B 16637 (by norm_num) ⟨8318, by rfl⟩ (by norm_num))
theorem R177493 : Reach 177493 := rs (se 13 (by rfl) ⟨32, by rfl⟩) (B 65 (by norm_num) ⟨32, by rfl⟩ (by norm_num))
theorem R275813 : Reach 275813 := rs (se 4 (by rfl) ⟨25857, by rfl⟩) (B 51715 (by norm_num) ⟨25857, by rfl⟩ (by norm_num))
theorem R636277 : Reach 636277 := rs (se 5 (by rfl) ⟨29825, by rfl⟩) (B 59651 (by norm_num) ⟨29825, by rfl⟩ (by norm_num))
theorem R177533 : Reach 177533 := rs (se 3 (by rfl) ⟨33287, by rfl⟩) (B 66575 (by norm_num) ⟨33287, by rfl⟩ (by norm_num))
theorem R144821 : Reach 144821 := rs (se 5 (by rfl) ⟨6788, by rfl⟩) (B 13577 (by norm_num) ⟨6788, by rfl⟩ (by norm_num))
theorem R112061 : Reach 112061 := rs (se 3 (by rfl) ⟨21011, by rfl⟩) (B 42023 (by norm_num) ⟨21011, by rfl⟩ (by norm_num))
theorem R177605 : Reach 177605 := rs (se 4 (by rfl) ⟨16650, by rfl⟩) (B 33301 (by norm_num) ⟨16650, by rfl⟩ (by norm_num))
theorem R79373 : Reach 79373 := rs (se 3 (by rfl) ⟨14882, by rfl⟩) (B 29765 (by norm_num) ⟨14882, by rfl⟩ (by norm_num))
theorem R112141 : Reach 112141 := rs (se 3 (by rfl) ⟨21026, by rfl⟩) (B 42053 (by norm_num) ⟨21026, by rfl⟩ (by norm_num))
theorem R177677 : Reach 177677 := rs (se 3 (by rfl) ⟨33314, by rfl⟩) (B 66629 (by norm_num) ⟨33314, by rfl⟩ (by norm_num))
theorem R144965 : Reach 144965 := rs (se 4 (by rfl) ⟨13590, by rfl⟩) (B 27181 (by norm_num) ⟨13590, by rfl⟩ (by norm_num))
theorem R177749 : Reach 177749 := rs (se 8 (by rfl) ⟨1041, by rfl⟩) (B 2083 (by norm_num) ⟨1041, by rfl⟩ (by norm_num))
theorem R112261 : Reach 112261 := rs (se 4 (by rfl) ⟨10524, by rfl⟩) (B 21049 (by norm_num) ⟨10524, by rfl⟩ (by norm_num))
theorem R177821 : Reach 177821 := rs (se 3 (by rfl) ⟨33341, by rfl⟩) (B 66683 (by norm_num) ⟨33341, by rfl⟩ (by norm_num))
theorem R210613 : Reach 210613 := rs (se 5 (by rfl) ⟨9872, by rfl⟩) (B 19745 (by norm_num) ⟨9872, by rfl⟩ (by norm_num))
theorem R112357 : Reach 112357 := rs (se 4 (by rfl) ⟨10533, by rfl⟩) (B 21067 (by norm_num) ⟨10533, by rfl⟩ (by norm_num))
theorem R177893 : Reach 177893 := rs (se 4 (by rfl) ⟨16677, by rfl⟩) (B 33355 (by norm_num) ⟨16677, by rfl⟩ (by norm_num))
theorem R177965 : Reach 177965 := rs (se 3 (by rfl) ⟨33368, by rfl⟩) (B 66737 (by norm_num) ⟨33368, by rfl⟩ (by norm_num))
theorem R145253 : Reach 145253 := rs (se 4 (by rfl) ⟨13617, by rfl⟩) (B 27235 (by norm_num) ⟨13617, by rfl⟩ (by norm_num))
theorem R538613 : Reach 538613 := rs (se 5 (by rfl) ⟨25247, by rfl⟩) (B 50495 (by norm_num) ⟨25247, by rfl⟩ (by norm_num))
theorem R145405 : Reach 145405 := rs (se 3 (by rfl) ⟨27263, by rfl⟩) (B 54527 (by norm_num) ⟨27263, by rfl⟩ (by norm_num))
theorem R79897 : Reach 79897 := rs (se 2 (by rfl) ⟨29961, by rfl⟩) (B 59923 (by norm_num) ⟨29961, by rfl⟩ (by norm_num))
theorem R112685 : Reach 112685 := rs (se 3 (by rfl) ⟨21128, by rfl⟩) (B 42257 (by norm_num) ⟨21128, by rfl⟩ (by norm_num))
theorem R112709 : Reach 112709 := rs (se 4 (by rfl) ⟨10566, by rfl⟩) (B 21133 (by norm_num) ⟨10566, by rfl⟩ (by norm_num))
theorem R112733 : Reach 112733 := rs (se 3 (by rfl) ⟨21137, by rfl⟩) (B 42275 (by norm_num) ⟨21137, by rfl⟩ (by norm_num))
theorem R112757 : Reach 112757 := rs (se 5 (by rfl) ⟨5285, by rfl⟩) (B 10571 (by norm_num) ⟨5285, by rfl⟩ (by norm_num))
theorem R112781 : Reach 112781 := rs (se 3 (by rfl) ⟨21146, by rfl⟩) (B 42293 (by norm_num) ⟨21146, by rfl⟩ (by norm_num))
theorem R112805 : Reach 112805 := rs (se 4 (by rfl) ⟨10575, by rfl⟩) (B 21151 (by norm_num) ⟨10575, by rfl⟩ (by norm_num))
theorem R112829 : Reach 112829 := rs (se 3 (by rfl) ⟨21155, by rfl⟩) (B 42311 (by norm_num) ⟨21155, by rfl⟩ (by norm_num))
theorem R112853 : Reach 112853 := rs (se 7 (by rfl) ⟨1322, by rfl⟩) (B 2645 (by norm_num) ⟨1322, by rfl⟩ (by norm_num))
theorem R112877 : Reach 112877 := rs (se 3 (by rfl) ⟨21164, by rfl⟩) (B 42329 (by norm_num) ⟨21164, by rfl⟩ (by norm_num))
theorem R112901 : Reach 112901 := rs (se 4 (by rfl) ⟨10584, by rfl⟩) (B 21169 (by norm_num) ⟨10584, by rfl⟩ (by norm_num))
theorem R112925 : Reach 112925 := rs (se 3 (by rfl) ⟨21173, by rfl⟩) (B 42347 (by norm_num) ⟨21173, by rfl⟩ (by norm_num))
theorem R145709 : Reach 145709 := rs (se 3 (by rfl) ⟨27320, by rfl⟩) (B 54641 (by norm_num) ⟨27320, by rfl⟩ (by norm_num))
theorem R112949 : Reach 112949 := rs (se 5 (by rfl) ⟨5294, by rfl⟩) (B 10589 (by norm_num) ⟨5294, by rfl⟩ (by norm_num))
theorem R112973 : Reach 112973 := rs (se 3 (by rfl) ⟨21182, by rfl⟩) (B 42365 (by norm_num) ⟨21182, by rfl⟩ (by norm_num))
theorem R178517 : Reach 178517 := rs (se 10 (by rfl) ⟨261, by rfl⟩) (B 523 (by norm_num) ⟨261, by rfl⟩ (by norm_num))
theorem R112997 : Reach 112997 := rs (se 4 (by rfl) ⟨10593, by rfl⟩) (B 21187 (by norm_num) ⟨10593, by rfl⟩ (by norm_num))
theorem R113021 : Reach 113021 := rs (se 3 (by rfl) ⟨21191, by rfl⟩) (B 42383 (by norm_num) ⟨21191, by rfl⟩ (by norm_num))
theorem R113045 : Reach 113045 := rs (se 6 (by rfl) ⟨2649, by rfl⟩) (B 5299 (by norm_num) ⟨2649, by rfl⟩ (by norm_num))
theorem R113069 : Reach 113069 := rs (se 3 (by rfl) ⟨21200, by rfl⟩) (B 42401 (by norm_num) ⟨21200, by rfl⟩ (by norm_num))
theorem R113093 : Reach 113093 := rs (se 4 (by rfl) ⟨10602, by rfl⟩) (B 21205 (by norm_num) ⟨10602, by rfl⟩ (by norm_num))
theorem R113117 : Reach 113117 := rs (se 3 (by rfl) ⟨21209, by rfl⟩) (B 42419 (by norm_num) ⟨21209, by rfl⟩ (by norm_num))
theorem R113141 : Reach 113141 := rs (se 5 (by rfl) ⟨5303, by rfl⟩) (B 10607 (by norm_num) ⟨5303, by rfl⟩ (by norm_num))
theorem R113165 : Reach 113165 := rs (se 3 (by rfl) ⟨21218, by rfl⟩) (B 42437 (by norm_num) ⟨21218, by rfl⟩ (by norm_num))
theorem R113189 : Reach 113189 := rs (se 4 (by rfl) ⟨10611, by rfl⟩) (B 21223 (by norm_num) ⟨10611, by rfl⟩ (by norm_num))
theorem R113213 : Reach 113213 := rs (se 3 (by rfl) ⟨21227, by rfl⟩) (B 42455 (by norm_num) ⟨21227, by rfl⟩ (by norm_num))
theorem R113237 : Reach 113237 := rs (se 8 (by rfl) ⟨663, by rfl⟩) (B 1327 (by norm_num) ⟨663, by rfl⟩ (by norm_num))
theorem R113261 : Reach 113261 := rs (se 3 (by rfl) ⟨21236, by rfl⟩) (B 42473 (by norm_num) ⟨21236, by rfl⟩ (by norm_num))
theorem R572021 : Reach 572021 := rs (se 5 (by rfl) ⟨26813, by rfl⟩) (B 53627 (by norm_num) ⟨26813, by rfl⟩ (by norm_num))
theorem R113285 : Reach 113285 := rs (se 4 (by rfl) ⟨10620, by rfl⟩) (B 21241 (by norm_num) ⟨10620, by rfl⟩ (by norm_num))
theorem R113309 : Reach 113309 := rs (se 3 (by rfl) ⟨21245, by rfl⟩) (B 42491 (by norm_num) ⟨21245, by rfl⟩ (by norm_num))
theorem R113333 : Reach 113333 := rs (se 5 (by rfl) ⟨5312, by rfl⟩) (B 10625 (by norm_num) ⟨5312, by rfl⟩ (by norm_num))
theorem R735925 : Reach 735925 := rs (se 5 (by rfl) ⟨34496, by rfl⟩) (B 68993 (by norm_num) ⟨34496, by rfl⟩ (by norm_num))
theorem R113357 : Reach 113357 := rs (se 3 (by rfl) ⟨21254, by rfl⟩) (B 42509 (by norm_num) ⟨21254, by rfl⟩ (by norm_num))
theorem R113381 : Reach 113381 := rs (se 4 (by rfl) ⟨10629, by rfl⟩) (B 21259 (by norm_num) ⟨10629, by rfl⟩ (by norm_num))
theorem R113405 : Reach 113405 := rs (se 3 (by rfl) ⟨21263, by rfl⟩) (B 42527 (by norm_num) ⟨21263, by rfl⟩ (by norm_num))
theorem R113429 : Reach 113429 := rs (se 6 (by rfl) ⟨2658, by rfl⟩) (B 5317 (by norm_num) ⟨2658, by rfl⟩ (by norm_num))
theorem R113453 : Reach 113453 := rs (se 3 (by rfl) ⟨21272, by rfl⟩) (B 42545 (by norm_num) ⟨21272, by rfl⟩ (by norm_num))
theorem R113477 : Reach 113477 := rs (se 4 (by rfl) ⟨10638, by rfl⟩) (B 21277 (by norm_num) ⟨10638, by rfl⟩ (by norm_num))
theorem R113501 : Reach 113501 := rs (se 3 (by rfl) ⟨21281, by rfl⟩) (B 42563 (by norm_num) ⟨21281, by rfl⟩ (by norm_num))
theorem R113525 : Reach 113525 := rs (se 5 (by rfl) ⟨5321, by rfl⟩) (B 10643 (by norm_num) ⟨5321, by rfl⟩ (by norm_num))
theorem R113549 : Reach 113549 := rs (se 3 (by rfl) ⟨21290, by rfl⟩) (B 42581 (by norm_num) ⟨21290, by rfl⟩ (by norm_num))
theorem R113573 : Reach 113573 := rs (se 4 (by rfl) ⟨10647, by rfl⟩) (B 21295 (by norm_num) ⟨10647, by rfl⟩ (by norm_num))
theorem R113597 : Reach 113597 := rs (se 3 (by rfl) ⟨21299, by rfl⟩) (B 42599 (by norm_num) ⟨21299, by rfl⟩ (by norm_num))
theorem R113621 : Reach 113621 := rs (se 7 (by rfl) ⟨1331, by rfl⟩) (B 2663 (by norm_num) ⟨1331, by rfl⟩ (by norm_num))
theorem R506837 : Reach 506837 := rs (se 7 (by rfl) ⟨5939, by rfl⟩) (B 11879 (by norm_num) ⟨5939, by rfl⟩ (by norm_num))
theorem R113645 : Reach 113645 := rs (se 3 (by rfl) ⟨21308, by rfl⟩) (B 42617 (by norm_num) ⟨21308, by rfl⟩ (by norm_num))
theorem R80885 : Reach 80885 := rs (se 5 (by rfl) ⟨3791, by rfl⟩) (B 7583 (by norm_num) ⟨3791, by rfl⟩ (by norm_num))
theorem R113669 : Reach 113669 := rs (se 4 (by rfl) ⟨10656, by rfl⟩) (B 21313 (by norm_num) ⟨10656, by rfl⟩ (by norm_num))
theorem R244757 : Reach 244757 := rs (se 6 (by rfl) ⟨5736, by rfl⟩) (B 11473 (by norm_num) ⟨5736, by rfl⟩ (by norm_num))
theorem R113693 : Reach 113693 := rs (se 3 (by rfl) ⟨21317, by rfl⟩) (B 42635 (by norm_num) ⟨21317, by rfl⟩ (by norm_num))
theorem R146461 : Reach 146461 := rs (se 3 (by rfl) ⟨27461, by rfl⟩) (B 54923 (by norm_num) ⟨27461, by rfl⟩ (by norm_num))
theorem R179245 : Reach 179245 := rs (se 3 (by rfl) ⟨33608, by rfl⟩) (B 67217 (by norm_num) ⟨33608, by rfl⟩ (by norm_num))
theorem R113717 : Reach 113717 := rs (se 5 (by rfl) ⟨5330, by rfl⟩) (B 10661 (by norm_num) ⟨5330, by rfl⟩ (by norm_num))
theorem R113741 : Reach 113741 := rs (se 3 (by rfl) ⟨21326, by rfl⟩) (B 42653 (by norm_num) ⟨21326, by rfl⟩ (by norm_num))
theorem R113765 : Reach 113765 := rs (se 4 (by rfl) ⟨10665, by rfl⟩) (B 21331 (by norm_num) ⟨10665, by rfl⟩ (by norm_num))
theorem R113789 : Reach 113789 := rs (se 3 (by rfl) ⟨21335, by rfl⟩) (B 42671 (by norm_num) ⟨21335, by rfl⟩ (by norm_num))
theorem R113813 : Reach 113813 := rs (se 6 (by rfl) ⟨2667, by rfl⟩) (B 5335 (by norm_num) ⟨2667, by rfl⟩ (by norm_num))
theorem R113837 : Reach 113837 := rs (se 3 (by rfl) ⟨21344, by rfl⟩) (B 42689 (by norm_num) ⟨21344, by rfl⟩ (by norm_num))
theorem R146605 : Reach 146605 := rs (se 3 (by rfl) ⟨27488, by rfl⟩) (B 54977 (by norm_num) ⟨27488, by rfl⟩ (by norm_num))
theorem R113861 : Reach 113861 := rs (se 4 (by rfl) ⟨10674, by rfl⟩) (B 21349 (by norm_num) ⟨10674, by rfl⟩ (by norm_num))
theorem R113885 : Reach 113885 := rs (se 3 (by rfl) ⟨21353, by rfl⟩) (B 42707 (by norm_num) ⟨21353, by rfl⟩ (by norm_num))
theorem R113909 : Reach 113909 := rs (se 5 (by rfl) ⟨5339, by rfl⟩) (B 10679 (by norm_num) ⟨5339, by rfl⟩ (by norm_num))
theorem R113933 : Reach 113933 := rs (se 3 (by rfl) ⟨21362, by rfl⟩) (B 42725 (by norm_num) ⟨21362, by rfl⟩ (by norm_num))
theorem R113957 : Reach 113957 := rs (se 4 (by rfl) ⟨10683, by rfl⟩) (B 21367 (by norm_num) ⟨10683, by rfl⟩ (by norm_num))
theorem R113981 : Reach 113981 := rs (se 3 (by rfl) ⟨21371, by rfl⟩) (B 42743 (by norm_num) ⟨21371, by rfl⟩ (by norm_num))
theorem R146765 : Reach 146765 := rs (se 3 (by rfl) ⟨27518, by rfl⟩) (B 55037 (by norm_num) ⟨27518, by rfl⟩ (by norm_num))
theorem R114005 : Reach 114005 := rs (se 11 (by rfl) ⟨83, by rfl⟩) (B 167 (by norm_num) ⟨83, by rfl⟩ (by norm_num))
theorem R114029 : Reach 114029 := rs (se 3 (by rfl) ⟨21380, by rfl⟩) (B 42761 (by norm_num) ⟨21380, by rfl⟩ (by norm_num))
theorem R114053 : Reach 114053 := rs (se 4 (by rfl) ⟨10692, by rfl⟩) (B 21385 (by norm_num) ⟨10692, by rfl⟩ (by norm_num))
theorem R114077 : Reach 114077 := rs (se 3 (by rfl) ⟨21389, by rfl⟩) (B 42779 (by norm_num) ⟨21389, by rfl⟩ (by norm_num))
theorem R81329 : Reach 81329 := rs (se 2 (by rfl) ⟨30498, by rfl⟩) (B 60997 (by norm_num) ⟨30498, by rfl⟩ (by norm_num))
theorem R114101 : Reach 114101 := rs (se 5 (by rfl) ⟨5348, by rfl⟩) (B 10697 (by norm_num) ⟨5348, by rfl⟩ (by norm_num))
theorem R114125 : Reach 114125 := rs (se 3 (by rfl) ⟨21398, by rfl⟩) (B 42797 (by norm_num) ⟨21398, by rfl⟩ (by norm_num))
theorem R146909 : Reach 146909 := rs (se 3 (by rfl) ⟨27545, by rfl⟩) (B 55091 (by norm_num) ⟨27545, by rfl⟩ (by norm_num))
theorem R114149 : Reach 114149 := rs (se 4 (by rfl) ⟨10701, by rfl⟩) (B 21403 (by norm_num) ⟨10701, by rfl⟩ (by norm_num))
theorem R114173 : Reach 114173 := rs (se 3 (by rfl) ⟨21407, by rfl⟩) (B 42815 (by norm_num) ⟨21407, by rfl⟩ (by norm_num))
theorem R376325 : Reach 376325 := rs (se 4 (by rfl) ⟨35280, by rfl⟩) (B 70561 (by norm_num) ⟨35280, by rfl⟩ (by norm_num))
theorem R114197 : Reach 114197 := rs (se 6 (by rfl) ⟨2676, by rfl⟩) (B 5353 (by norm_num) ⟨2676, by rfl⟩ (by norm_num))
theorem R114221 : Reach 114221 := rs (se 3 (by rfl) ⟨21416, by rfl⟩) (B 42833 (by norm_num) ⟨21416, by rfl⟩ (by norm_num))
theorem R114245 : Reach 114245 := rs (se 4 (by rfl) ⟨10710, by rfl⟩) (B 21421 (by norm_num) ⟨10710, by rfl⟩ (by norm_num))
theorem R114269 : Reach 114269 := rs (se 3 (by rfl) ⟨21425, by rfl⟩) (B 42851 (by norm_num) ⟨21425, by rfl⟩ (by norm_num))
theorem R114293 : Reach 114293 := rs (se 5 (by rfl) ⟨5357, by rfl⟩) (B 10715 (by norm_num) ⟨5357, by rfl⟩ (by norm_num))
theorem R114317 : Reach 114317 := rs (se 3 (by rfl) ⟨21434, by rfl⟩) (B 42869 (by norm_num) ⟨21434, by rfl⟩ (by norm_num))
theorem R114341 : Reach 114341 := rs (se 4 (by rfl) ⟨10719, by rfl⟩) (B 21439 (by norm_num) ⟨10719, by rfl⟩ (by norm_num))
theorem R81577 : Reach 81577 := rs (se 2 (by rfl) ⟨30591, by rfl⟩) (B 61183 (by norm_num) ⟨30591, by rfl⟩ (by norm_num))
theorem R114365 : Reach 114365 := rs (se 3 (by rfl) ⟨21443, by rfl⟩) (B 42887 (by norm_num) ⟨21443, by rfl⟩ (by norm_num))
theorem R114389 : Reach 114389 := rs (se 7 (by rfl) ⟨1340, by rfl⟩) (B 2681 (by norm_num) ⟨1340, by rfl⟩ (by norm_num))
theorem R114413 : Reach 114413 := rs (se 3 (by rfl) ⟨21452, by rfl⟩) (B 42905 (by norm_num) ⟨21452, by rfl⟩ (by norm_num))
theorem R147197 : Reach 147197 := rs (se 3 (by rfl) ⟨27599, by rfl⟩) (B 55199 (by norm_num) ⟨27599, by rfl⟩ (by norm_num))
theorem R114437 : Reach 114437 := rs (se 4 (by rfl) ⟨10728, by rfl⟩) (B 21457 (by norm_num) ⟨10728, by rfl⟩ (by norm_num))
theorem R114461 : Reach 114461 := rs (se 3 (by rfl) ⟨21461, by rfl⟩) (B 42923 (by norm_num) ⟨21461, by rfl⟩ (by norm_num))
theorem R114485 : Reach 114485 := rs (se 5 (by rfl) ⟨5366, by rfl⟩) (B 10733 (by norm_num) ⟨5366, by rfl⟩ (by norm_num))
theorem R147253 : Reach 147253 := rs (se 5 (by rfl) ⟨6902, by rfl⟩) (B 13805 (by norm_num) ⟨6902, by rfl⟩ (by norm_num))
theorem R114509 : Reach 114509 := rs (se 3 (by rfl) ⟨21470, by rfl⟩) (B 42941 (by norm_num) ⟨21470, by rfl⟩ (by norm_num))
theorem R114533 : Reach 114533 := rs (se 4 (by rfl) ⟨10737, by rfl⟩) (B 21475 (by norm_num) ⟨10737, by rfl⟩ (by norm_num))
theorem R114557 : Reach 114557 := rs (se 3 (by rfl) ⟨21479, by rfl⟩) (B 42959 (by norm_num) ⟨21479, by rfl⟩ (by norm_num))
theorem R114581 : Reach 114581 := rs (se 6 (by rfl) ⟨2685, by rfl⟩) (B 5371 (by norm_num) ⟨2685, by rfl⟩ (by norm_num))
theorem R147349 : Reach 147349 := rs (se 6 (by rfl) ⟨3453, by rfl⟩) (B 6907 (by norm_num) ⟨3453, by rfl⟩ (by norm_num))
theorem R114605 : Reach 114605 := rs (se 3 (by rfl) ⟨21488, by rfl⟩) (B 42977 (by norm_num) ⟨21488, by rfl⟩ (by norm_num))
theorem R114629 : Reach 114629 := rs (se 4 (by rfl) ⟨10746, by rfl⟩) (B 21493 (by norm_num) ⟨10746, by rfl⟩ (by norm_num))
theorem R114653 : Reach 114653 := rs (se 3 (by rfl) ⟨21497, by rfl⟩) (B 42995 (by norm_num) ⟨21497, by rfl⟩ (by norm_num))
theorem R114677 : Reach 114677 := rs (se 5 (by rfl) ⟨5375, by rfl⟩) (B 10751 (by norm_num) ⟨5375, by rfl⟩ (by norm_num))
theorem R114701 : Reach 114701 := rs (se 3 (by rfl) ⟨21506, by rfl⟩) (B 43013 (by norm_num) ⟨21506, by rfl⟩ (by norm_num))
theorem R114725 : Reach 114725 := rs (se 4 (by rfl) ⟨10755, by rfl⟩) (B 21511 (by norm_num) ⟨10755, by rfl⟩ (by norm_num))
theorem R180269 : Reach 180269 := rs (se 3 (by rfl) ⟨33800, by rfl⟩) (B 67601 (by norm_num) ⟨33800, by rfl⟩ (by norm_num))
theorem R278581 : Reach 278581 := rs (se 5 (by rfl) ⟨13058, by rfl⟩) (B 26117 (by norm_num) ⟨13058, by rfl⟩ (by norm_num))
theorem R114749 : Reach 114749 := rs (se 3 (by rfl) ⟨21515, by rfl⟩) (B 43031 (by norm_num) ⟨21515, by rfl⟩ (by norm_num))
theorem R114773 : Reach 114773 := rs (se 8 (by rfl) ⟨672, by rfl⟩) (B 1345 (by norm_num) ⟨672, by rfl⟩ (by norm_num))
theorem R82009 : Reach 82009 := rs (se 2 (by rfl) ⟨30753, by rfl⟩) (B 61507 (by norm_num) ⟨30753, by rfl⟩ (by norm_num))
theorem R114797 : Reach 114797 := rs (se 3 (by rfl) ⟨21524, by rfl⟩) (B 43049 (by norm_num) ⟨21524, by rfl⟩ (by norm_num))
theorem R114821 : Reach 114821 := rs (se 4 (by rfl) ⟨10764, by rfl⟩) (B 21529 (by norm_num) ⟨10764, by rfl⟩ (by norm_num))
theorem R114845 : Reach 114845 := rs (se 3 (by rfl) ⟨21533, by rfl⟩) (B 43067 (by norm_num) ⟨21533, by rfl⟩ (by norm_num))
theorem R82081 : Reach 82081 := rs (se 2 (by rfl) ⟨30780, by rfl⟩) (B 61561 (by norm_num) ⟨30780, by rfl⟩ (by norm_num))
theorem R114869 : Reach 114869 := rs (se 5 (by rfl) ⟨5384, by rfl⟩) (B 10769 (by norm_num) ⟨5384, by rfl⟩ (by norm_num))
theorem R147653 : Reach 147653 := rs (se 4 (by rfl) ⟨13842, by rfl⟩) (B 27685 (by norm_num) ⟨13842, by rfl⟩ (by norm_num))
theorem R114893 : Reach 114893 := rs (se 3 (by rfl) ⟨21542, by rfl⟩) (B 43085 (by norm_num) ⟨21542, by rfl⟩ (by norm_num))
theorem R278741 : Reach 278741 := rs (se 7 (by rfl) ⟨3266, by rfl⟩) (B 6533 (by norm_num) ⟨3266, by rfl⟩ (by norm_num))
theorem R114917 : Reach 114917 := rs (se 4 (by rfl) ⟨10773, by rfl⟩) (B 21547 (by norm_num) ⟨10773, by rfl⟩ (by norm_num))
theorem R114941 : Reach 114941 := rs (se 3 (by rfl) ⟨21551, by rfl⟩) (B 43103 (by norm_num) ⟨21551, by rfl⟩ (by norm_num))
theorem R114965 : Reach 114965 := rs (se 6 (by rfl) ⟨2694, by rfl⟩) (B 5389 (by norm_num) ⟨2694, by rfl⟩ (by norm_num))
theorem R114989 : Reach 114989 := rs (se 3 (by rfl) ⟨21560, by rfl⟩) (B 43121 (by norm_num) ⟨21560, by rfl⟩ (by norm_num))
theorem R115013 : Reach 115013 := rs (se 4 (by rfl) ⟨10782, by rfl⟩) (B 21565 (by norm_num) ⟨10782, by rfl⟩ (by norm_num))
theorem R115021 : Reach 115021 := rs (se 3 (by rfl) ⟨21566, by rfl⟩) (B 43133 (by norm_num) ⟨21566, by rfl⟩ (by norm_num))
theorem R115037 : Reach 115037 := rs (se 3 (by rfl) ⟨21569, by rfl⟩) (B 43139 (by norm_num) ⟨21569, by rfl⟩ (by norm_num))
theorem R115061 : Reach 115061 := rs (se 5 (by rfl) ⟨5393, by rfl⟩) (B 10787 (by norm_num) ⟨5393, by rfl⟩ (by norm_num))
theorem R82301 : Reach 82301 := rs (se 3 (by rfl) ⟨15431, by rfl⟩) (B 30863 (by norm_num) ⟨15431, by rfl⟩ (by norm_num))
theorem R115085 : Reach 115085 := rs (se 3 (by rfl) ⟨21578, by rfl⟩) (B 43157 (by norm_num) ⟨21578, by rfl⟩ (by norm_num))
theorem R115109 : Reach 115109 := rs (se 4 (by rfl) ⟨10791, by rfl⟩) (B 21583 (by norm_num) ⟨10791, by rfl⟩ (by norm_num))
theorem R115133 : Reach 115133 := rs (se 3 (by rfl) ⟨21587, by rfl⟩) (B 43175 (by norm_num) ⟨21587, by rfl⟩ (by norm_num))
theorem R115157 : Reach 115157 := rs (se 7 (by rfl) ⟨1349, by rfl⟩) (B 2699 (by norm_num) ⟨1349, by rfl⟩ (by norm_num))
theorem R115181 : Reach 115181 := rs (se 3 (by rfl) ⟨21596, by rfl⟩) (B 43193 (by norm_num) ⟨21596, by rfl⟩ (by norm_num))
theorem R115205 : Reach 115205 := rs (se 4 (by rfl) ⟨10800, by rfl⟩) (B 21601 (by norm_num) ⟨10800, by rfl⟩ (by norm_num))
theorem R82453 : Reach 82453 := rs (se 6 (by rfl) ⟨1932, by rfl⟩) (B 3865 (by norm_num) ⟨1932, by rfl⟩ (by norm_num))
theorem R115229 : Reach 115229 := rs (se 3 (by rfl) ⟨21605, by rfl⟩) (B 43211 (by norm_num) ⟨21605, by rfl⟩ (by norm_num))
theorem R115253 : Reach 115253 := rs (se 5 (by rfl) ⟨5402, by rfl⟩) (B 10805 (by norm_num) ⟨5402, by rfl⟩ (by norm_num))
theorem R115277 : Reach 115277 := rs (se 3 (by rfl) ⟨21614, by rfl⟩) (B 43229 (by norm_num) ⟨21614, by rfl⟩ (by norm_num))
theorem R115301 : Reach 115301 := rs (se 4 (by rfl) ⟨10809, by rfl⟩) (B 21619 (by norm_num) ⟨10809, by rfl⟩ (by norm_num))
theorem R115325 : Reach 115325 := rs (se 3 (by rfl) ⟨21623, by rfl⟩) (B 43247 (by norm_num) ⟨21623, by rfl⟩ (by norm_num))
theorem R115349 : Reach 115349 := rs (se 6 (by rfl) ⟨2703, by rfl⟩) (B 5407 (by norm_num) ⟨2703, by rfl⟩ (by norm_num))
theorem R115373 : Reach 115373 := rs (se 3 (by rfl) ⟨21632, by rfl⟩) (B 43265 (by norm_num) ⟨21632, by rfl⟩ (by norm_num))
theorem R115397 : Reach 115397 := rs (se 4 (by rfl) ⟨10818, by rfl⟩) (B 21637 (by norm_num) ⟨10818, by rfl⟩ (by norm_num))
theorem R115421 : Reach 115421 := rs (se 3 (by rfl) ⟨21641, by rfl⟩) (B 43283 (by norm_num) ⟨21641, by rfl⟩ (by norm_num))
theorem R115445 : Reach 115445 := rs (se 5 (by rfl) ⟨5411, by rfl⟩) (B 10823 (by norm_num) ⟨5411, by rfl⟩ (by norm_num))
theorem R115469 : Reach 115469 := rs (se 3 (by rfl) ⟨21650, by rfl⟩) (B 43301 (by norm_num) ⟨21650, by rfl⟩ (by norm_num))
theorem R115493 : Reach 115493 := rs (se 4 (by rfl) ⟨10827, by rfl⟩) (B 21655 (by norm_num) ⟨10827, by rfl⟩ (by norm_num))
theorem R148277 : Reach 148277 := rs (se 5 (by rfl) ⟨6950, by rfl⟩) (B 13901 (by norm_num) ⟨6950, by rfl⟩ (by norm_num))
theorem R115517 : Reach 115517 := rs (se 3 (by rfl) ⟨21659, by rfl⟩) (B 43319 (by norm_num) ⟨21659, by rfl⟩ (by norm_num))
theorem R181061 : Reach 181061 := rs (se 4 (by rfl) ⟨16974, by rfl⟩) (B 33949 (by norm_num) ⟨16974, by rfl⟩ (by norm_num))
theorem R115541 : Reach 115541 := rs (se 9 (by rfl) ⟨338, by rfl⟩) (B 677 (by norm_num) ⟨338, by rfl⟩ (by norm_num))
theorem R115565 : Reach 115565 := rs (se 3 (by rfl) ⟨21668, by rfl⟩) (B 43337 (by norm_num) ⟨21668, by rfl⟩ (by norm_num))
theorem R115589 : Reach 115589 := rs (se 4 (by rfl) ⟨10836, by rfl⟩) (B 21673 (by norm_num) ⟨10836, by rfl⟩ (by norm_num))
theorem R82829 : Reach 82829 := rs (se 3 (by rfl) ⟨15530, by rfl⟩) (B 31061 (by norm_num) ⟨15530, by rfl⟩ (by norm_num))
theorem R115613 : Reach 115613 := rs (se 3 (by rfl) ⟨21677, by rfl⟩) (B 43355 (by norm_num) ⟨21677, by rfl⟩ (by norm_num))
theorem R115637 : Reach 115637 := rs (se 5 (by rfl) ⟨5420, by rfl⟩) (B 10841 (by norm_num) ⟨5420, by rfl⟩ (by norm_num))
theorem R148405 : Reach 148405 := rs (se 5 (by rfl) ⟨6956, by rfl⟩) (B 13913 (by norm_num) ⟨6956, by rfl⟩ (by norm_num))
theorem R115661 : Reach 115661 := rs (se 3 (by rfl) ⟨21686, by rfl⟩) (B 43373 (by norm_num) ⟨21686, by rfl⟩ (by norm_num))
theorem R82901 : Reach 82901 := rs (se 7 (by rfl) ⟨971, by rfl⟩) (B 1943 (by norm_num) ⟨971, by rfl⟩ (by norm_num))
theorem R115685 : Reach 115685 := rs (se 4 (by rfl) ⟨10845, by rfl⟩) (B 21691 (by norm_num) ⟨10845, by rfl⟩ (by norm_num))
theorem R115709 : Reach 115709 := rs (se 3 (by rfl) ⟨21695, by rfl⟩) (B 43391 (by norm_num) ⟨21695, by rfl⟩ (by norm_num))
theorem R115733 : Reach 115733 := rs (se 6 (by rfl) ⟨2712, by rfl⟩) (B 5425 (by norm_num) ⟨2712, by rfl⟩ (by norm_num))
theorem R115757 : Reach 115757 := rs (se 3 (by rfl) ⟨21704, by rfl⟩) (B 43409 (by norm_num) ⟨21704, by rfl⟩ (by norm_num))
theorem R115781 : Reach 115781 := rs (se 4 (by rfl) ⟨10854, by rfl⟩) (B 21709 (by norm_num) ⟨10854, by rfl⟩ (by norm_num))
theorem R148549 : Reach 148549 := rs (se 4 (by rfl) ⟨13926, by rfl⟩) (B 27853 (by norm_num) ⟨13926, by rfl⟩ (by norm_num))
theorem R115805 : Reach 115805 := rs (se 3 (by rfl) ⟨21713, by rfl⟩) (B 43427 (by norm_num) ⟨21713, by rfl⟩ (by norm_num))
theorem R115829 : Reach 115829 := rs (se 5 (by rfl) ⟨5429, by rfl⟩) (B 10859 (by norm_num) ⟨5429, by rfl⟩ (by norm_num))
theorem R115853 : Reach 115853 := rs (se 3 (by rfl) ⟨21722, by rfl⟩) (B 43445 (by norm_num) ⟨21722, by rfl⟩ (by norm_num))
theorem R83089 : Reach 83089 := rs (se 2 (by rfl) ⟨31158, by rfl⟩) (B 62317 (by norm_num) ⟨31158, by rfl⟩ (by norm_num))
theorem R115877 : Reach 115877 := rs (se 4 (by rfl) ⟨10863, by rfl⟩) (B 21727 (by norm_num) ⟨10863, by rfl⟩ (by norm_num))
theorem R115901 : Reach 115901 := rs (se 3 (by rfl) ⟨21731, by rfl⟩) (B 43463 (by norm_num) ⟨21731, by rfl⟩ (by norm_num))
theorem R115925 : Reach 115925 := rs (se 7 (by rfl) ⟨1358, by rfl⟩) (B 2717 (by norm_num) ⟨1358, by rfl⟩ (by norm_num))
theorem R247013 : Reach 247013 := rs (se 4 (by rfl) ⟨23157, by rfl⟩) (B 46315 (by norm_num) ⟨23157, by rfl⟩ (by norm_num))
theorem R148709 : Reach 148709 := rs (se 4 (by rfl) ⟨13941, by rfl⟩) (B 27883 (by norm_num) ⟨13941, by rfl⟩ (by norm_num))
theorem R115949 : Reach 115949 := rs (se 3 (by rfl) ⟨21740, by rfl⟩) (B 43481 (by norm_num) ⟨21740, by rfl⟩ (by norm_num))
theorem R115973 : Reach 115973 := rs (se 4 (by rfl) ⟨10872, by rfl⟩) (B 21745 (by norm_num) ⟨10872, by rfl⟩ (by norm_num))
theorem R115997 : Reach 115997 := rs (se 3 (by rfl) ⟨21749, by rfl⟩) (B 43499 (by norm_num) ⟨21749, by rfl⟩ (by norm_num))
theorem R116021 : Reach 116021 := rs (se 5 (by rfl) ⟨5438, by rfl⟩) (B 10877 (by norm_num) ⟨5438, by rfl⟩ (by norm_num))
theorem R83273 : Reach 83273 := rs (se 2 (by rfl) ⟨31227, by rfl⟩) (B 62455 (by norm_num) ⟨31227, by rfl⟩ (by norm_num))
theorem R116045 : Reach 116045 := rs (se 3 (by rfl) ⟨21758, by rfl⟩) (B 43517 (by norm_num) ⟨21758, by rfl⟩ (by norm_num))
theorem R116069 : Reach 116069 := rs (se 4 (by rfl) ⟨10881, by rfl⟩) (B 21763 (by norm_num) ⟨10881, by rfl⟩ (by norm_num))
theorem R148853 : Reach 148853 := rs (se 5 (by rfl) ⟨6977, by rfl⟩) (B 13955 (by norm_num) ⟨6977, by rfl⟩ (by norm_num))
theorem R116093 : Reach 116093 := rs (se 3 (by rfl) ⟨21767, by rfl⟩) (B 43535 (by norm_num) ⟨21767, by rfl⟩ (by norm_num))
theorem R116117 : Reach 116117 := rs (se 6 (by rfl) ⟨2721, by rfl⟩) (B 5443 (by norm_num) ⟨2721, by rfl⟩ (by norm_num))
theorem R607637 : Reach 607637 := rs (se 6 (by rfl) ⟨14241, by rfl⟩) (B 28483 (by norm_num) ⟨14241, by rfl⟩ (by norm_num))
theorem R116141 : Reach 116141 := rs (se 3 (by rfl) ⟨21776, by rfl⟩) (B 43553 (by norm_num) ⟨21776, by rfl⟩ (by norm_num))
theorem R116165 : Reach 116165 := rs (se 4 (by rfl) ⟨10890, by rfl⟩) (B 21781 (by norm_num) ⟨10890, by rfl⟩ (by norm_num))
theorem R116189 : Reach 116189 := rs (se 3 (by rfl) ⟨21785, by rfl⟩) (B 43571 (by norm_num) ⟨21785, by rfl⟩ (by norm_num))
theorem R116213 : Reach 116213 := rs (se 5 (by rfl) ⟨5447, by rfl⟩) (B 10895 (by norm_num) ⟨5447, by rfl⟩ (by norm_num))
theorem R116237 : Reach 116237 := rs (se 3 (by rfl) ⟨21794, by rfl⟩) (B 43589 (by norm_num) ⟨21794, by rfl⟩ (by norm_num))
theorem R149021 : Reach 149021 := rs (se 3 (by rfl) ⟨27941, by rfl⟩) (B 55883 (by norm_num) ⟨27941, by rfl⟩ (by norm_num))
theorem R116261 : Reach 116261 := rs (se 4 (by rfl) ⟨10899, by rfl⟩) (B 21799 (by norm_num) ⟨10899, by rfl⟩ (by norm_num))
theorem R476725 : Reach 476725 := rs (se 5 (by rfl) ⟨22346, by rfl⟩) (B 44693 (by norm_num) ⟨22346, by rfl⟩ (by norm_num))
theorem R116285 : Reach 116285 := rs (se 3 (by rfl) ⟨21803, by rfl⟩) (B 43607 (by norm_num) ⟨21803, by rfl⟩ (by norm_num))
theorem R116309 : Reach 116309 := rs (se 8 (by rfl) ⟨681, by rfl⟩) (B 1363 (by norm_num) ⟨681, by rfl⟩ (by norm_num))
theorem R116333 : Reach 116333 := rs (se 3 (by rfl) ⟨21812, by rfl⟩) (B 43625 (by norm_num) ⟨21812, by rfl⟩ (by norm_num))
theorem R214645 : Reach 214645 := rs (se 5 (by rfl) ⟨10061, by rfl⟩) (B 20123 (by norm_num) ⟨10061, by rfl⟩ (by norm_num))
theorem R116357 : Reach 116357 := rs (se 4 (by rfl) ⟨10908, by rfl⟩) (B 21817 (by norm_num) ⟨10908, by rfl⟩ (by norm_num))
theorem R149141 : Reach 149141 := rs (se 6 (by rfl) ⟨3495, by rfl⟩) (B 6991 (by norm_num) ⟨3495, by rfl⟩ (by norm_num))
theorem R116381 : Reach 116381 := rs (se 3 (by rfl) ⟨21821, by rfl⟩) (B 43643 (by norm_num) ⟨21821, by rfl⟩ (by norm_num))
theorem R116405 : Reach 116405 := rs (se 5 (by rfl) ⟨5456, by rfl⟩) (B 10913 (by norm_num) ⟨5456, by rfl⟩ (by norm_num))
theorem R116429 : Reach 116429 := rs (se 3 (by rfl) ⟨21830, by rfl⟩) (B 43661 (by norm_num) ⟨21830, by rfl⟩ (by norm_num))
theorem R116453 : Reach 116453 := rs (se 4 (by rfl) ⟨10917, by rfl⟩) (B 21835 (by norm_num) ⟨10917, by rfl⟩ (by norm_num))
theorem R116477 : Reach 116477 := rs (se 3 (by rfl) ⟨21839, by rfl⟩) (B 43679 (by norm_num) ⟨21839, by rfl⟩ (by norm_num))
theorem R214805 : Reach 214805 := rs (se 6 (by rfl) ⟨5034, by rfl⟩) (B 10069 (by norm_num) ⟨5034, by rfl⟩ (by norm_num))
theorem R116501 : Reach 116501 := rs (se 6 (by rfl) ⟨2730, by rfl⟩) (B 5461 (by norm_num) ⟨2730, by rfl⟩ (by norm_num))
theorem R116525 : Reach 116525 := rs (se 3 (by rfl) ⟨21848, by rfl⟩) (B 43697 (by norm_num) ⟨21848, by rfl⟩ (by norm_num))
theorem R149293 : Reach 149293 := rs (se 3 (by rfl) ⟨27992, by rfl⟩) (B 55985 (by norm_num) ⟨27992, by rfl⟩ (by norm_num))
theorem R116549 : Reach 116549 := rs (se 4 (by rfl) ⟨10926, by rfl⟩) (B 21853 (by norm_num) ⟨10926, by rfl⟩ (by norm_num))
theorem R345941 : Reach 345941 := rs (se 9 (by rfl) ⟨1013, by rfl⟩) (B 2027 (by norm_num) ⟨1013, by rfl⟩ (by norm_num))
theorem R116573 : Reach 116573 := rs (se 3 (by rfl) ⟨21857, by rfl⟩) (B 43715 (by norm_num) ⟨21857, by rfl⟩ (by norm_num))
theorem R116597 : Reach 116597 := rs (se 5 (by rfl) ⟨5465, by rfl⟩) (B 10931 (by norm_num) ⟨5465, by rfl⟩ (by norm_num))
theorem R509813 : Reach 509813 := rs (se 5 (by rfl) ⟨23897, by rfl⟩) (B 47795 (by norm_num) ⟨23897, by rfl⟩ (by norm_num))
theorem R116621 : Reach 116621 := rs (se 3 (by rfl) ⟨21866, by rfl⟩) (B 43733 (by norm_num) ⟨21866, by rfl⟩ (by norm_num))
theorem R116645 : Reach 116645 := rs (se 4 (by rfl) ⟨10935, by rfl⟩) (B 21871 (by norm_num) ⟨10935, by rfl⟩ (by norm_num))
theorem R116669 : Reach 116669 := rs (se 3 (by rfl) ⟨21875, by rfl⟩) (B 43751 (by norm_num) ⟨21875, by rfl⟩ (by norm_num))
theorem R116693 : Reach 116693 := rs (se 7 (by rfl) ⟨1367, by rfl⟩) (B 2735 (by norm_num) ⟨1367, by rfl⟩ (by norm_num))
theorem R247781 : Reach 247781 := rs (se 4 (by rfl) ⟨23229, by rfl⟩) (B 46459 (by norm_num) ⟨23229, by rfl⟩ (by norm_num))
theorem R116717 : Reach 116717 := rs (se 3 (by rfl) ⟨21884, by rfl⟩) (B 43769 (by norm_num) ⟨21884, by rfl⟩ (by norm_num))
theorem R215045 : Reach 215045 := rs (se 4 (by rfl) ⟨20160, by rfl⟩) (B 40321 (by norm_num) ⟨20160, by rfl⟩ (by norm_num))
theorem R116741 : Reach 116741 := rs (se 4 (by rfl) ⟨10944, by rfl⟩) (B 21889 (by norm_num) ⟨10944, by rfl⟩ (by norm_num))
theorem R116765 : Reach 116765 := rs (se 3 (by rfl) ⟨21893, by rfl⟩) (B 43787 (by norm_num) ⟨21893, by rfl⟩ (by norm_num))
theorem R116789 : Reach 116789 := rs (se 5 (by rfl) ⟨5474, by rfl⟩) (B 10949 (by norm_num) ⟨5474, by rfl⟩ (by norm_num))
theorem R84025 : Reach 84025 := rs (se 2 (by rfl) ⟨31509, by rfl⟩) (B 63019 (by norm_num) ⟨31509, by rfl⟩ (by norm_num))
theorem R116813 : Reach 116813 := rs (se 3 (by rfl) ⟨21902, by rfl⟩) (B 43805 (by norm_num) ⟨21902, by rfl⟩ (by norm_num))
theorem R116821 : Reach 116821 := rs (se 8 (by rfl) ⟨684, by rfl⟩) (B 1369 (by norm_num) ⟨684, by rfl⟩ (by norm_num))
theorem R149597 : Reach 149597 := rs (se 3 (by rfl) ⟨28049, by rfl⟩) (B 56099 (by norm_num) ⟨28049, by rfl⟩ (by norm_num))
theorem R116837 : Reach 116837 := rs (se 4 (by rfl) ⟨10953, by rfl⟩) (B 21907 (by norm_num) ⟨10953, by rfl⟩ (by norm_num))
theorem R116861 : Reach 116861 := rs (se 3 (by rfl) ⟨21911, by rfl⟩) (B 43823 (by norm_num) ⟨21911, by rfl⟩ (by norm_num))
theorem R84097 : Reach 84097 := rs (se 2 (by rfl) ⟨31536, by rfl⟩) (B 63073 (by norm_num) ⟨31536, by rfl⟩ (by norm_num))
theorem R116885 : Reach 116885 := rs (se 6 (by rfl) ⟨2739, by rfl⟩) (B 5479 (by norm_num) ⟨2739, by rfl⟩ (by norm_num))
theorem R116909 : Reach 116909 := rs (se 3 (by rfl) ⟨21920, by rfl⟩) (B 43841 (by norm_num) ⟨21920, by rfl⟩ (by norm_num))
theorem R215237 : Reach 215237 := rs (se 4 (by rfl) ⟨20178, by rfl⟩) (B 40357 (by norm_num) ⟨20178, by rfl⟩ (by norm_num))
theorem R116933 : Reach 116933 := rs (se 4 (by rfl) ⟨10962, by rfl⟩) (B 21925 (by norm_num) ⟨10962, by rfl⟩ (by norm_num))
theorem R116957 : Reach 116957 := rs (se 3 (by rfl) ⟨21929, by rfl⟩) (B 43859 (by norm_num) ⟨21929, by rfl⟩ (by norm_num))
theorem R116981 : Reach 116981 := rs (se 5 (by rfl) ⟨5483, by rfl⟩) (B 10967 (by norm_num) ⟨5483, by rfl⟩ (by norm_num))
theorem R117005 : Reach 117005 := rs (se 3 (by rfl) ⟨21938, by rfl⟩) (B 43877 (by norm_num) ⟨21938, by rfl⟩ (by norm_num))
theorem R117029 : Reach 117029 := rs (se 4 (by rfl) ⟨10971, by rfl⟩) (B 21943 (by norm_num) ⟨10971, by rfl⟩ (by norm_num))
theorem R84277 : Reach 84277 := rs (se 5 (by rfl) ⟨3950, by rfl⟩) (B 7901 (by norm_num) ⟨3950, by rfl⟩ (by norm_num))
theorem R117053 : Reach 117053 := rs (se 3 (by rfl) ⟨21947, by rfl⟩) (B 43895 (by norm_num) ⟨21947, by rfl⟩ (by norm_num))
theorem R117077 : Reach 117077 := rs (se 10 (by rfl) ⟨171, by rfl⟩) (B 343 (by norm_num) ⟨171, by rfl⟩ (by norm_num))
theorem R117101 : Reach 117101 := rs (se 3 (by rfl) ⟨21956, by rfl⟩) (B 43913 (by norm_num) ⟨21956, by rfl⟩ (by norm_num))
theorem R117125 : Reach 117125 := rs (se 4 (by rfl) ⟨10980, by rfl⟩) (B 21961 (by norm_num) ⟨10980, by rfl⟩ (by norm_num))
theorem R117149 : Reach 117149 := rs (se 3 (by rfl) ⟨21965, by rfl⟩) (B 43931 (by norm_num) ⟨21965, by rfl⟩ (by norm_num))
theorem R117173 : Reach 117173 := rs (se 5 (by rfl) ⟨5492, by rfl⟩) (B 10985 (by norm_num) ⟨5492, by rfl⟩ (by norm_num))
theorem R117197 : Reach 117197 := rs (se 3 (by rfl) ⟨21974, by rfl⟩) (B 43949 (by norm_num) ⟨21974, by rfl⟩ (by norm_num))
theorem R248293 : Reach 248293 := rs (se 4 (by rfl) ⟨23277, by rfl⟩) (B 46555 (by norm_num) ⟨23277, by rfl⟩ (by norm_num))
theorem R117221 : Reach 117221 := rs (se 4 (by rfl) ⟨10989, by rfl⟩) (B 21979 (by norm_num) ⟨10989, by rfl⟩ (by norm_num))
theorem R117245 : Reach 117245 := rs (se 3 (by rfl) ⟨21983, by rfl⟩) (B 43967 (by norm_num) ⟨21983, by rfl⟩ (by norm_num))
theorem R117269 : Reach 117269 := rs (se 6 (by rfl) ⟨2748, by rfl⟩) (B 5497 (by norm_num) ⟨2748, by rfl⟩ (by norm_num))
theorem R117293 : Reach 117293 := rs (se 3 (by rfl) ⟨21992, by rfl⟩) (B 43985 (by norm_num) ⟨21992, by rfl⟩ (by norm_num))
theorem R182837 : Reach 182837 := rs (se 5 (by rfl) ⟨8570, by rfl⟩) (B 17141 (by norm_num) ⟨8570, by rfl⟩ (by norm_num))
theorem R84541 : Reach 84541 := rs (se 3 (by rfl) ⟨15851, by rfl⟩) (B 31703 (by norm_num) ⟨15851, by rfl⟩ (by norm_num))
theorem R117317 : Reach 117317 := rs (se 4 (by rfl) ⟨10998, by rfl⟩) (B 21997 (by norm_num) ⟨10998, by rfl⟩ (by norm_num))
theorem R117341 : Reach 117341 := rs (se 3 (by rfl) ⟨22001, by rfl⟩) (B 44003 (by norm_num) ⟨22001, by rfl⟩ (by norm_num))
theorem R84577 : Reach 84577 := rs (se 2 (by rfl) ⟨31716, by rfl⟩) (B 63433 (by norm_num) ⟨31716, by rfl⟩ (by norm_num))
theorem R117365 : Reach 117365 := rs (se 5 (by rfl) ⟨5501, by rfl⟩) (B 11003 (by norm_num) ⟨5501, by rfl⟩ (by norm_num))
theorem R84613 : Reach 84613 := rs (se 4 (by rfl) ⟨7932, by rfl⟩) (B 15865 (by norm_num) ⟨7932, by rfl⟩ (by norm_num))
theorem R117389 : Reach 117389 := rs (se 3 (by rfl) ⟨22010, by rfl⟩) (B 44021 (by norm_num) ⟨22010, by rfl⟩ (by norm_num))
theorem R477845 : Reach 477845 := rs (se 6 (by rfl) ⟨11199, by rfl⟩) (B 22399 (by norm_num) ⟨11199, by rfl⟩ (by norm_num))
theorem R117413 : Reach 117413 := rs (se 4 (by rfl) ⟨11007, by rfl⟩) (B 22015 (by norm_num) ⟨11007, by rfl⟩ (by norm_num))
theorem R84649 : Reach 84649 := rs (se 2 (by rfl) ⟨31743, by rfl⟩) (B 63487 (by norm_num) ⟨31743, by rfl⟩ (by norm_num))
theorem R117437 : Reach 117437 := rs (se 3 (by rfl) ⟨22019, by rfl⟩) (B 44039 (by norm_num) ⟨22019, by rfl⟩ (by norm_num))
theorem R84685 : Reach 84685 := rs (se 3 (by rfl) ⟨15878, by rfl⟩) (B 31757 (by norm_num) ⟨15878, by rfl⟩ (by norm_num))
theorem R117461 : Reach 117461 := rs (se 7 (by rfl) ⟨1376, by rfl⟩) (B 2753 (by norm_num) ⟨1376, by rfl⟩ (by norm_num))
theorem R117485 : Reach 117485 := rs (se 3 (by rfl) ⟨22028, by rfl⟩) (B 44057 (by norm_num) ⟨22028, by rfl⟩ (by norm_num))
theorem R84721 : Reach 84721 := rs (se 2 (by rfl) ⟨31770, by rfl⟩) (B 63541 (by norm_num) ⟨31770, by rfl⟩ (by norm_num))
theorem R117509 : Reach 117509 := rs (se 4 (by rfl) ⟨11016, by rfl⟩) (B 22033 (by norm_num) ⟨11016, by rfl⟩ (by norm_num))
theorem R84757 : Reach 84757 := rs (se 6 (by rfl) ⟨1986, by rfl⟩) (B 3973 (by norm_num) ⟨1986, by rfl⟩ (by norm_num))
theorem R117533 : Reach 117533 := rs (se 3 (by rfl) ⟨22037, by rfl⟩) (B 44075 (by norm_num) ⟨22037, by rfl⟩ (by norm_num))
theorem R117557 : Reach 117557 := rs (se 5 (by rfl) ⟨5510, by rfl⟩) (B 11021 (by norm_num) ⟨5510, by rfl⟩ (by norm_num))
theorem R84793 : Reach 84793 := rs (se 2 (by rfl) ⟨31797, by rfl⟩) (B 63595 (by norm_num) ⟨31797, by rfl⟩ (by norm_num))
theorem R150349 : Reach 150349 := rs (se 3 (by rfl) ⟨28190, by rfl⟩) (B 56381 (by norm_num) ⟨28190, by rfl⟩ (by norm_num))
theorem R117581 : Reach 117581 := rs (se 3 (by rfl) ⟨22046, by rfl⟩) (B 44093 (by norm_num) ⟨22046, by rfl⟩ (by norm_num))
theorem R84829 : Reach 84829 := rs (se 3 (by rfl) ⟨15905, by rfl⟩) (B 31811 (by norm_num) ⟨15905, by rfl⟩ (by norm_num))
theorem R117605 : Reach 117605 := rs (se 4 (by rfl) ⟨11025, by rfl⟩) (B 22051 (by norm_num) ⟨11025, by rfl⟩ (by norm_num))
theorem R117629 : Reach 117629 := rs (se 3 (by rfl) ⟨22055, by rfl⟩) (B 44111 (by norm_num) ⟨22055, by rfl⟩ (by norm_num))
theorem R84865 : Reach 84865 := rs (se 2 (by rfl) ⟨31824, by rfl⟩) (B 63649 (by norm_num) ⟨31824, by rfl⟩ (by norm_num))
theorem R117653 : Reach 117653 := rs (se 6 (by rfl) ⟨2757, by rfl⟩) (B 5515 (by norm_num) ⟨2757, by rfl⟩ (by norm_num))
theorem R84901 : Reach 84901 := rs (se 4 (by rfl) ⟨7959, by rfl⟩) (B 15919 (by norm_num) ⟨7959, by rfl⟩ (by norm_num))
theorem R117677 : Reach 117677 := rs (se 3 (by rfl) ⟨22064, by rfl⟩) (B 44129 (by norm_num) ⟨22064, by rfl⟩ (by norm_num))
theorem R117701 : Reach 117701 := rs (se 4 (by rfl) ⟨11034, by rfl⟩) (B 22069 (by norm_num) ⟨11034, by rfl⟩ (by norm_num))
theorem R84937 : Reach 84937 := rs (se 2 (by rfl) ⟨31851, by rfl⟩) (B 63703 (by norm_num) ⟨31851, by rfl⟩ (by norm_num))
theorem R117725 : Reach 117725 := rs (se 3 (by rfl) ⟨22073, by rfl⟩) (B 44147 (by norm_num) ⟨22073, by rfl⟩ (by norm_num))
theorem R84973 : Reach 84973 := rs (se 3 (by rfl) ⟨15932, by rfl⟩) (B 31865 (by norm_num) ⟨15932, by rfl⟩ (by norm_num))
theorem R117749 : Reach 117749 := rs (se 5 (by rfl) ⟨5519, by rfl⟩) (B 11039 (by norm_num) ⟨5519, by rfl⟩ (by norm_num))
theorem R117773 : Reach 117773 := rs (se 3 (by rfl) ⟨22082, by rfl⟩) (B 44165 (by norm_num) ⟨22082, by rfl⟩ (by norm_num))
theorem R85009 : Reach 85009 := rs (se 2 (by rfl) ⟨31878, by rfl⟩) (B 63757 (by norm_num) ⟨31878, by rfl⟩ (by norm_num))
theorem R117797 : Reach 117797 := rs (se 4 (by rfl) ⟨11043, by rfl⟩) (B 22087 (by norm_num) ⟨11043, by rfl⟩ (by norm_num))
theorem R85045 : Reach 85045 := rs (se 5 (by rfl) ⟨3986, by rfl⟩) (B 7973 (by norm_num) ⟨3986, by rfl⟩ (by norm_num))
theorem R117821 : Reach 117821 := rs (se 3 (by rfl) ⟨22091, by rfl⟩) (B 44183 (by norm_num) ⟨22091, by rfl⟩ (by norm_num))
theorem R117845 : Reach 117845 := rs (se 8 (by rfl) ⟨690, by rfl⟩) (B 1381 (by norm_num) ⟨690, by rfl⟩ (by norm_num))
theorem R85081 : Reach 85081 := rs (se 2 (by rfl) ⟨31905, by rfl⟩) (B 63811 (by norm_num) ⟨31905, by rfl⟩ (by norm_num))
theorem R117869 : Reach 117869 := rs (se 3 (by rfl) ⟨22100, by rfl⟩) (B 44201 (by norm_num) ⟨22100, by rfl⟩ (by norm_num))
theorem R85117 : Reach 85117 := rs (se 3 (by rfl) ⟨15959, by rfl⟩) (B 31919 (by norm_num) ⟨15959, by rfl⟩ (by norm_num))
theorem R117893 : Reach 117893 := rs (se 4 (by rfl) ⟨11052, by rfl⟩) (B 22105 (by norm_num) ⟨11052, by rfl⟩ (by norm_num))
theorem R117917 : Reach 117917 := rs (se 3 (by rfl) ⟨22109, by rfl⟩) (B 44219 (by norm_num) ⟨22109, by rfl⟩ (by norm_num))
theorem R85153 : Reach 85153 := rs (se 2 (by rfl) ⟨31932, by rfl⟩) (B 63865 (by norm_num) ⟨31932, by rfl⟩ (by norm_num))
theorem R216229 : Reach 216229 := rs (se 4 (by rfl) ⟨20271, by rfl⟩) (B 40543 (by norm_num) ⟨20271, by rfl⟩ (by norm_num))
theorem R117941 : Reach 117941 := rs (se 5 (by rfl) ⟨5528, by rfl⟩) (B 11057 (by norm_num) ⟨5528, by rfl⟩ (by norm_num))
theorem R85189 : Reach 85189 := rs (se 4 (by rfl) ⟨7986, by rfl⟩) (B 15973 (by norm_num) ⟨7986, by rfl⟩ (by norm_num))
theorem R117965 : Reach 117965 := rs (se 3 (by rfl) ⟨22118, by rfl⟩) (B 44237 (by norm_num) ⟨22118, by rfl⟩ (by norm_num))
theorem R117989 : Reach 117989 := rs (se 4 (by rfl) ⟨11061, by rfl⟩) (B 22123 (by norm_num) ⟨11061, by rfl⟩ (by norm_num))
theorem R85225 : Reach 85225 := rs (se 2 (by rfl) ⟨31959, by rfl⟩) (B 63919 (by norm_num) ⟨31959, by rfl⟩ (by norm_num))
theorem R347381 : Reach 347381 := rs (se 5 (by rfl) ⟨16283, by rfl⟩) (B 32567 (by norm_num) ⟨16283, by rfl⟩ (by norm_num))
theorem R118013 : Reach 118013 := rs (se 3 (by rfl) ⟨22127, by rfl⟩) (B 44255 (by norm_num) ⟨22127, by rfl⟩ (by norm_num))
theorem R85261 : Reach 85261 := rs (se 3 (by rfl) ⟨15986, by rfl⟩) (B 31973 (by norm_num) ⟨15986, by rfl⟩ (by norm_num))
theorem R118037 : Reach 118037 := rs (se 6 (by rfl) ⟨2766, by rfl⟩) (B 5533 (by norm_num) ⟨2766, by rfl⟩ (by norm_num))
theorem R118061 : Reach 118061 := rs (se 3 (by rfl) ⟨22136, by rfl⟩) (B 44273 (by norm_num) ⟨22136, by rfl⟩ (by norm_num))
theorem R85297 : Reach 85297 := rs (se 2 (by rfl) ⟨31986, by rfl⟩) (B 63973 (by norm_num) ⟨31986, by rfl⟩ (by norm_num))
theorem R118085 : Reach 118085 := rs (se 4 (by rfl) ⟨11070, by rfl⟩) (B 22141 (by norm_num) ⟨11070, by rfl⟩ (by norm_num))
theorem R85333 : Reach 85333 := rs (se 11 (by rfl) ⟨62, by rfl⟩) (B 125 (by norm_num) ⟨62, by rfl⟩ (by norm_num))
theorem R544085 : Reach 544085 := rs (se 11 (by rfl) ⟨398, by rfl⟩) (B 797 (by norm_num) ⟨398, by rfl⟩ (by norm_num))
theorem R118109 : Reach 118109 := rs (se 3 (by rfl) ⟨22145, by rfl⟩) (B 44291 (by norm_num) ⟨22145, by rfl⟩ (by norm_num))
theorem R118133 : Reach 118133 := rs (se 5 (by rfl) ⟨5537, by rfl⟩) (B 11075 (by norm_num) ⟨5537, by rfl⟩ (by norm_num))
theorem R85369 : Reach 85369 := rs (se 2 (by rfl) ⟨32013, by rfl⟩) (B 64027 (by norm_num) ⟨32013, by rfl⟩ (by norm_num))
theorem R118157 : Reach 118157 := rs (se 3 (by rfl) ⟨22154, by rfl⟩) (B 44309 (by norm_num) ⟨22154, by rfl⟩ (by norm_num))
theorem R85405 : Reach 85405 := rs (se 3 (by rfl) ⟨16013, by rfl⟩) (B 32027 (by norm_num) ⟨16013, by rfl⟩ (by norm_num))
theorem R118181 : Reach 118181 := rs (se 4 (by rfl) ⟨11079, by rfl⟩) (B 22159 (by norm_num) ⟨11079, by rfl⟩ (by norm_num))
theorem R118205 : Reach 118205 := rs (se 3 (by rfl) ⟨22163, by rfl⟩) (B 44327 (by norm_num) ⟨22163, by rfl⟩ (by norm_num))
theorem R85441 : Reach 85441 := rs (se 2 (by rfl) ⟨32040, by rfl⟩) (B 64081 (by norm_num) ⟨32040, by rfl⟩ (by norm_num))
theorem R118229 : Reach 118229 := rs (se 7 (by rfl) ⟨1385, by rfl⟩) (B 2771 (by norm_num) ⟨1385, by rfl⟩ (by norm_num))
theorem R85477 : Reach 85477 := rs (se 4 (by rfl) ⟨8013, by rfl⟩) (B 16027 (by norm_num) ⟨8013, by rfl⟩ (by norm_num))
theorem R118253 : Reach 118253 := rs (se 3 (by rfl) ⟨22172, by rfl⟩) (B 44345 (by norm_num) ⟨22172, by rfl⟩ (by norm_num))
theorem R118277 : Reach 118277 := rs (se 4 (by rfl) ⟨11088, by rfl⟩) (B 22177 (by norm_num) ⟨11088, by rfl⟩ (by norm_num))
theorem R85513 : Reach 85513 := rs (se 2 (by rfl) ⟨32067, by rfl⟩) (B 64135 (by norm_num) ⟨32067, by rfl⟩ (by norm_num))
theorem R118301 : Reach 118301 := rs (se 3 (by rfl) ⟨22181, by rfl⟩) (B 44363 (by norm_num) ⟨22181, by rfl⟩ (by norm_num))
theorem R85549 : Reach 85549 := rs (se 3 (by rfl) ⟨16040, by rfl⟩) (B 32081 (by norm_num) ⟨16040, by rfl⟩ (by norm_num))
theorem R118325 : Reach 118325 := rs (se 5 (by rfl) ⟨5546, by rfl⟩) (B 11093 (by norm_num) ⟨5546, by rfl⟩ (by norm_num))
theorem R118349 : Reach 118349 := rs (se 3 (by rfl) ⟨22190, by rfl⟩) (B 44381 (by norm_num) ⟨22190, by rfl⟩ (by norm_num))
theorem R85585 : Reach 85585 := rs (se 2 (by rfl) ⟨32094, by rfl⟩) (B 64189 (by norm_num) ⟨32094, by rfl⟩ (by norm_num))
theorem R118373 : Reach 118373 := rs (se 4 (by rfl) ⟨11097, by rfl⟩) (B 22195 (by norm_num) ⟨11097, by rfl⟩ (by norm_num))
theorem R216677 : Reach 216677 := rs (se 4 (by rfl) ⟨20313, by rfl⟩) (B 40627 (by norm_num) ⟨20313, by rfl⟩ (by norm_num))
theorem R85621 : Reach 85621 := rs (se 5 (by rfl) ⟨4013, by rfl⟩) (B 8027 (by norm_num) ⟨4013, by rfl⟩ (by norm_num))
theorem R118397 : Reach 118397 := rs (se 3 (by rfl) ⟨22199, by rfl⟩) (B 44399 (by norm_num) ⟨22199, by rfl⟩ (by norm_num))
theorem R413333 : Reach 413333 := rs (se 6 (by rfl) ⟨9687, by rfl⟩) (B 19375 (by norm_num) ⟨9687, by rfl⟩ (by norm_num))
theorem R118421 : Reach 118421 := rs (se 6 (by rfl) ⟨2775, by rfl⟩) (B 5551 (by norm_num) ⟨2775, by rfl⟩ (by norm_num))
theorem R85657 : Reach 85657 := rs (se 2 (by rfl) ⟨32121, by rfl⟩) (B 64243 (by norm_num) ⟨32121, by rfl⟩ (by norm_num))
theorem R118445 : Reach 118445 := rs (se 3 (by rfl) ⟨22208, by rfl⟩) (B 44417 (by norm_num) ⟨22208, by rfl⟩ (by norm_num))
theorem R85693 : Reach 85693 := rs (se 3 (by rfl) ⟨16067, by rfl⟩) (B 32135 (by norm_num) ⟨16067, by rfl⟩ (by norm_num))
theorem R118469 : Reach 118469 := rs (se 4 (by rfl) ⟨11106, by rfl⟩) (B 22213 (by norm_num) ⟨11106, by rfl⟩ (by norm_num))
theorem R118493 : Reach 118493 := rs (se 3 (by rfl) ⟨22217, by rfl⟩) (B 44435 (by norm_num) ⟨22217, by rfl⟩ (by norm_num))
theorem R85729 : Reach 85729 := rs (se 2 (by rfl) ⟨32148, by rfl⟩) (B 64297 (by norm_num) ⟨32148, by rfl⟩ (by norm_num))
theorem R118517 : Reach 118517 := rs (se 5 (by rfl) ⟨5555, by rfl⟩) (B 11111 (by norm_num) ⟨5555, by rfl⟩ (by norm_num))
theorem R85765 : Reach 85765 := rs (se 4 (by rfl) ⟨8040, by rfl⟩) (B 16081 (by norm_num) ⟨8040, by rfl⟩ (by norm_num))
theorem R118541 : Reach 118541 := rs (se 3 (by rfl) ⟨22226, by rfl⟩) (B 44453 (by norm_num) ⟨22226, by rfl⟩ (by norm_num))
theorem R118565 : Reach 118565 := rs (se 4 (by rfl) ⟨11115, by rfl⟩) (B 22231 (by norm_num) ⟨11115, by rfl⟩ (by norm_num))
theorem R85801 : Reach 85801 := rs (se 2 (by rfl) ⟨32175, by rfl⟩) (B 64351 (by norm_num) ⟨32175, by rfl⟩ (by norm_num))
theorem R118589 : Reach 118589 := rs (se 3 (by rfl) ⟨22235, by rfl⟩) (B 44471 (by norm_num) ⟨22235, by rfl⟩ (by norm_num))
theorem R85837 : Reach 85837 := rs (se 3 (by rfl) ⟨16094, by rfl⟩) (B 32189 (by norm_num) ⟨16094, by rfl⟩ (by norm_num))
theorem R118613 : Reach 118613 := rs (se 9 (by rfl) ⟨347, by rfl⟩) (B 695 (by norm_num) ⟨347, by rfl⟩ (by norm_num))
theorem R118637 : Reach 118637 := rs (se 3 (by rfl) ⟨22244, by rfl⟩) (B 44489 (by norm_num) ⟨22244, by rfl⟩ (by norm_num))
theorem R85873 : Reach 85873 := rs (se 2 (by rfl) ⟨32202, by rfl⟩) (B 64405 (by norm_num) ⟨32202, by rfl⟩ (by norm_num))
theorem R118661 : Reach 118661 := rs (se 4 (by rfl) ⟨11124, by rfl⟩) (B 22249 (by norm_num) ⟨11124, by rfl⟩ (by norm_num))
theorem R85909 : Reach 85909 := rs (se 6 (by rfl) ⟨2013, by rfl⟩) (B 4027 (by norm_num) ⟨2013, by rfl⟩ (by norm_num))
theorem R118685 : Reach 118685 := rs (se 3 (by rfl) ⟨22253, by rfl⟩) (B 44507 (by norm_num) ⟨22253, by rfl⟩ (by norm_num))
theorem R85945 : Reach 85945 := rs (se 2 (by rfl) ⟨32229, by rfl⟩) (B 64459 (by norm_num) ⟨32229, by rfl⟩ (by norm_num))
theorem R85981 : Reach 85981 := rs (se 3 (by rfl) ⟨16121, by rfl⟩) (B 32243 (by norm_num) ⟨16121, by rfl⟩ (by norm_num))
theorem R86017 : Reach 86017 := rs (se 2 (by rfl) ⟨32256, by rfl⟩) (B 64513 (by norm_num) ⟨32256, by rfl⟩ (by norm_num))
theorem R86053 : Reach 86053 := rs (se 4 (by rfl) ⟨8067, by rfl⟩) (B 16135 (by norm_num) ⟨8067, by rfl⟩ (by norm_num))
theorem R86089 : Reach 86089 := rs (se 2 (by rfl) ⟨32283, by rfl⟩) (B 64567 (by norm_num) ⟨32283, by rfl⟩ (by norm_num))
theorem R86125 : Reach 86125 := rs (se 3 (by rfl) ⟨16148, by rfl⟩) (B 32297 (by norm_num) ⟨16148, by rfl⟩ (by norm_num))
theorem R86161 : Reach 86161 := rs (se 2 (by rfl) ⟨32310, by rfl⟩) (B 64621 (by norm_num) ⟨32310, by rfl⟩ (by norm_num))
theorem R86197 : Reach 86197 := rs (se 5 (by rfl) ⟨4040, by rfl⟩) (B 8081 (by norm_num) ⟨4040, by rfl⟩ (by norm_num))
theorem R250037 : Reach 250037 := rs (se 5 (by rfl) ⟨11720, by rfl⟩) (B 23441 (by norm_num) ⟨11720, by rfl⟩ (by norm_num))
theorem R315589 : Reach 315589 := rs (se 4 (by rfl) ⟨29586, by rfl⟩) (B 59173 (by norm_num) ⟨29586, by rfl⟩ (by norm_num))
theorem R86233 : Reach 86233 := rs (se 2 (by rfl) ⟨32337, by rfl⟩) (B 64675 (by norm_num) ⟨32337, by rfl⟩ (by norm_num))
theorem R217333 : Reach 217333 := rs (se 5 (by rfl) ⟨10187, by rfl⟩) (B 20375 (by norm_num) ⟨10187, by rfl⟩ (by norm_num))
theorem R86269 : Reach 86269 := rs (se 3 (by rfl) ⟨16175, by rfl⟩) (B 32351 (by norm_num) ⟨16175, by rfl⟩ (by norm_num))
theorem R446741 : Reach 446741 := rs (se 6 (by rfl) ⟨10470, by rfl⟩) (B 20941 (by norm_num) ⟨10470, by rfl⟩ (by norm_num))
theorem R86305 : Reach 86305 := rs (se 2 (by rfl) ⟨32364, by rfl⟩) (B 64729 (by norm_num) ⟨32364, by rfl⟩ (by norm_num))
theorem R86341 : Reach 86341 := rs (se 4 (by rfl) ⟨8094, by rfl⟩) (B 16189 (by norm_num) ⟨8094, by rfl⟩ (by norm_num))
theorem R86377 : Reach 86377 := rs (se 2 (by rfl) ⟨32391, by rfl⟩) (B 64783 (by norm_num) ⟨32391, by rfl⟩ (by norm_num))
theorem R250229 : Reach 250229 := rs (se 5 (by rfl) ⟨11729, by rfl⟩) (B 23459 (by norm_num) ⟨11729, by rfl⟩ (by norm_num))
theorem R86413 : Reach 86413 := rs (se 3 (by rfl) ⟨16202, by rfl⟩) (B 32405 (by norm_num) ⟨16202, by rfl⟩ (by norm_num))
theorem R348565 : Reach 348565 := rs (se 6 (by rfl) ⟨8169, by rfl⟩) (B 16339 (by norm_num) ⟨8169, by rfl⟩ (by norm_num))
theorem R86449 : Reach 86449 := rs (se 2 (by rfl) ⟨32418, by rfl⟩) (B 64837 (by norm_num) ⟨32418, by rfl⟩ (by norm_num))
theorem R86485 : Reach 86485 := rs (se 7 (by rfl) ⟨1013, by rfl⟩) (B 2027 (by norm_num) ⟨1013, by rfl⟩ (by norm_num))
theorem R86521 : Reach 86521 := rs (se 2 (by rfl) ⟨32445, by rfl⟩) (B 64891 (by norm_num) ⟨32445, by rfl⟩ (by norm_num))
theorem R152077 : Reach 152077 := rs (se 3 (by rfl) ⟨28514, by rfl⟩) (B 57029 (by norm_num) ⟨28514, by rfl⟩ (by norm_num))
theorem R86557 : Reach 86557 := rs (se 3 (by rfl) ⟨16229, by rfl⟩) (B 32459 (by norm_num) ⟨16229, by rfl⟩ (by norm_num))
theorem R348725 : Reach 348725 := rs (se 5 (by rfl) ⟨16346, by rfl⟩) (B 32693 (by norm_num) ⟨16346, by rfl⟩ (by norm_num))
theorem R86593 : Reach 86593 := rs (se 2 (by rfl) ⟨32472, by rfl⟩) (B 64945 (by norm_num) ⟨32472, by rfl⟩ (by norm_num))
theorem R381509 : Reach 381509 := rs (se 4 (by rfl) ⟨35766, by rfl⟩) (B 71533 (by norm_num) ⟨35766, by rfl⟩ (by norm_num))
theorem R184933 : Reach 184933 := rs (se 4 (by rfl) ⟨17337, by rfl⟩) (B 34675 (by norm_num) ⟨17337, by rfl⟩ (by norm_num))
theorem R86629 : Reach 86629 := rs (se 4 (by rfl) ⟨8121, by rfl⟩) (B 16243 (by norm_num) ⟨8121, by rfl⟩ (by norm_num))
theorem R86665 : Reach 86665 := rs (se 2 (by rfl) ⟨32499, by rfl⟩) (B 64999 (by norm_num) ⟨32499, by rfl⟩ (by norm_num))
theorem R86701 : Reach 86701 := rs (se 3 (by rfl) ⟨16256, by rfl⟩) (B 32513 (by norm_num) ⟨16256, by rfl⟩ (by norm_num))
theorem R86737 : Reach 86737 := rs (se 2 (by rfl) ⟨32526, by rfl⟩) (B 65053 (by norm_num) ⟨32526, by rfl⟩ (by norm_num))
theorem R86773 : Reach 86773 := rs (se 5 (by rfl) ⟨4067, by rfl⟩) (B 8135 (by norm_num) ⟨4067, by rfl⟩ (by norm_num))
theorem R86809 : Reach 86809 := rs (se 2 (by rfl) ⟨32553, by rfl⟩) (B 65107 (by norm_num) ⟨32553, by rfl⟩ (by norm_num))
theorem R86845 : Reach 86845 := rs (se 3 (by rfl) ⟨16283, by rfl⟩) (B 32567 (by norm_num) ⟨16283, by rfl⟩ (by norm_num))
theorem R86881 : Reach 86881 := rs (se 2 (by rfl) ⟨32580, by rfl⟩) (B 65161 (by norm_num) ⟨32580, by rfl⟩ (by norm_num))
theorem R86917 : Reach 86917 := rs (se 4 (by rfl) ⟨8148, by rfl⟩) (B 16297 (by norm_num) ⟨8148, by rfl⟩ (by norm_num))
theorem R316325 : Reach 316325 := rs (se 4 (by rfl) ⟨29655, by rfl⟩) (B 59311 (by norm_num) ⟨29655, by rfl⟩ (by norm_num))
theorem R86953 : Reach 86953 := rs (se 2 (by rfl) ⟨32607, by rfl⟩) (B 65215 (by norm_num) ⟨32607, by rfl⟩ (by norm_num))
theorem R86989 : Reach 86989 := rs (se 3 (by rfl) ⟨16310, by rfl⟩) (B 32621 (by norm_num) ⟨16310, by rfl⟩ (by norm_num))
theorem R87025 : Reach 87025 := rs (se 2 (by rfl) ⟨32634, by rfl⟩) (B 65269 (by norm_num) ⟨32634, by rfl⟩ (by norm_num))
theorem R87061 : Reach 87061 := rs (se 6 (by rfl) ⟨2040, by rfl⟩) (B 4081 (by norm_num) ⟨2040, by rfl⟩ (by norm_num))
theorem R87097 : Reach 87097 := rs (se 2 (by rfl) ⟨32661, by rfl⟩) (B 65323 (by norm_num) ⟨32661, by rfl⟩ (by norm_num))
theorem R87133 : Reach 87133 := rs (se 3 (by rfl) ⟨16337, by rfl⟩) (B 32675 (by norm_num) ⟨16337, by rfl⟩ (by norm_num))
theorem R87169 : Reach 87169 := rs (se 2 (by rfl) ⟨32688, by rfl⟩) (B 65377 (by norm_num) ⟨32688, by rfl⟩ (by norm_num))
theorem R87205 : Reach 87205 := rs (se 4 (by rfl) ⟨8175, by rfl⟩) (B 16351 (by norm_num) ⟨8175, by rfl⟩ (by norm_num))
theorem R87241 : Reach 87241 := rs (se 2 (by rfl) ⟨32715, by rfl⟩) (B 65431 (by norm_num) ⟨32715, by rfl⟩ (by norm_num))
theorem R87277 : Reach 87277 := rs (se 3 (by rfl) ⟨16364, by rfl⟩) (B 32729 (by norm_num) ⟨16364, by rfl⟩ (by norm_num))
theorem R87313 : Reach 87313 := rs (se 2 (by rfl) ⟨32742, by rfl⟩) (B 65485 (by norm_num) ⟨32742, by rfl⟩ (by norm_num))
theorem R185645 : Reach 185645 := rs (se 3 (by rfl) ⟨34808, by rfl⟩) (B 69617 (by norm_num) ⟨34808, by rfl⟩ (by norm_num))
theorem R87349 : Reach 87349 := rs (se 5 (by rfl) ⟨4094, by rfl⟩) (B 8189 (by norm_num) ⟨4094, by rfl⟩ (by norm_num))
theorem R87385 : Reach 87385 := rs (se 2 (by rfl) ⟨32769, by rfl⟩) (B 65539 (by norm_num) ⟨32769, by rfl⟩ (by norm_num))
theorem R87421 : Reach 87421 := rs (se 3 (by rfl) ⟨16391, by rfl⟩) (B 32783 (by norm_num) ⟨16391, by rfl⟩ (by norm_num))
theorem R87457 : Reach 87457 := rs (se 2 (by rfl) ⟨32796, by rfl⟩) (B 65593 (by norm_num) ⟨32796, by rfl⟩ (by norm_num))
theorem R87493 : Reach 87493 := rs (se 4 (by rfl) ⟨8202, by rfl⟩) (B 16405 (by norm_num) ⟨8202, by rfl⟩ (by norm_num))
theorem R87529 : Reach 87529 := rs (se 2 (by rfl) ⟨32823, by rfl⟩) (B 65647 (by norm_num) ⟨32823, by rfl⟩ (by norm_num))
theorem R153101 : Reach 153101 := rs (se 3 (by rfl) ⟨28706, by rfl⟩) (B 57413 (by norm_num) ⟨28706, by rfl⟩ (by norm_num))
theorem R87565 : Reach 87565 := rs (se 3 (by rfl) ⟨16418, by rfl⟩) (B 32837 (by norm_num) ⟨16418, by rfl⟩ (by norm_num))
theorem R349733 : Reach 349733 := rs (se 4 (by rfl) ⟨32787, by rfl⟩) (B 65575 (by norm_num) ⟨32787, by rfl⟩ (by norm_num))
theorem R87601 : Reach 87601 := rs (se 2 (by rfl) ⟨32850, by rfl⟩) (B 65701 (by norm_num) ⟨32850, by rfl⟩ (by norm_num))
theorem R87637 : Reach 87637 := rs (se 8 (by rfl) ⟨513, by rfl⟩) (B 1027 (by norm_num) ⟨513, by rfl⟩ (by norm_num))
theorem R87673 : Reach 87673 := rs (se 2 (by rfl) ⟨32877, by rfl⟩) (B 65755 (by norm_num) ⟨32877, by rfl⟩ (by norm_num))
theorem R87685 : Reach 87685 := rs (se 4 (by rfl) ⟨8220, by rfl⟩) (B 16441 (by norm_num) ⟨8220, by rfl⟩ (by norm_num))
theorem R87709 : Reach 87709 := rs (se 3 (by rfl) ⟨16445, by rfl⟩) (B 32891 (by norm_num) ⟨16445, by rfl⟩ (by norm_num))
theorem R186029 : Reach 186029 := rs (se 3 (by rfl) ⟨34880, by rfl⟩) (B 69761 (by norm_num) ⟨34880, by rfl⟩ (by norm_num))
theorem R87725 : Reach 87725 := rs (se 3 (by rfl) ⟨16448, by rfl⟩) (B 32897 (by norm_num) ⟨16448, by rfl⟩ (by norm_num))
theorem R87745 : Reach 87745 := rs (se 2 (by rfl) ⟨32904, by rfl⟩) (B 65809 (by norm_num) ⟨32904, by rfl⟩ (by norm_num))
theorem R120533 : Reach 120533 := rs (se 7 (by rfl) ⟨1412, by rfl⟩) (B 2825 (by norm_num) ⟨1412, by rfl⟩ (by norm_num))
theorem R218837 : Reach 218837 := rs (se 7 (by rfl) ⟨2564, by rfl⟩) (B 5129 (by norm_num) ⟨2564, by rfl⟩ (by norm_num))
theorem R87781 : Reach 87781 := rs (se 4 (by rfl) ⟨8229, by rfl⟩) (B 16459 (by norm_num) ⟨8229, by rfl⟩ (by norm_num))
theorem R87817 : Reach 87817 := rs (se 2 (by rfl) ⟨32931, by rfl⟩) (B 65863 (by norm_num) ⟨32931, by rfl⟩ (by norm_num))
theorem R87853 : Reach 87853 := rs (se 3 (by rfl) ⟨16472, by rfl⟩) (B 32945 (by norm_num) ⟨16472, by rfl⟩ (by norm_num))
theorem R87889 : Reach 87889 := rs (se 2 (by rfl) ⟨32958, by rfl⟩) (B 65917 (by norm_num) ⟨32958, by rfl⟩ (by norm_num))
theorem R382805 : Reach 382805 := rs (se 9 (by rfl) ⟨1121, by rfl⟩) (B 2243 (by norm_num) ⟨1121, by rfl⟩ (by norm_num))
theorem R87925 : Reach 87925 := rs (se 5 (by rfl) ⟨4121, by rfl⟩) (B 8243 (by norm_num) ⟨4121, by rfl⟩ (by norm_num))
theorem R87961 : Reach 87961 := rs (se 2 (by rfl) ⟨32985, by rfl⟩) (B 65971 (by norm_num) ⟨32985, by rfl⟩ (by norm_num))
theorem R87997 : Reach 87997 := rs (se 3 (by rfl) ⟨16499, by rfl⟩) (B 32999 (by norm_num) ⟨16499, by rfl⟩ (by norm_num))
theorem R186317 : Reach 186317 := rs (se 3 (by rfl) ⟨34934, by rfl⟩) (B 69869 (by norm_num) ⟨34934, by rfl⟩ (by norm_num))
theorem R88033 : Reach 88033 := rs (se 2 (by rfl) ⟨33012, by rfl⟩) (B 66025 (by norm_num) ⟨33012, by rfl⟩ (by norm_num))
theorem R88069 : Reach 88069 := rs (se 4 (by rfl) ⟨8256, by rfl⟩) (B 16513 (by norm_num) ⟨8256, by rfl⟩ (by norm_num))
theorem R88105 : Reach 88105 := rs (se 2 (by rfl) ⟨33039, by rfl⟩) (B 66079 (by norm_num) ⟨33039, by rfl⟩ (by norm_num))
theorem R88141 : Reach 88141 := rs (se 3 (by rfl) ⟨16526, by rfl⟩) (B 33053 (by norm_num) ⟨16526, by rfl⟩ (by norm_num))
theorem R88177 : Reach 88177 := rs (se 2 (by rfl) ⟨33066, by rfl⟩) (B 66133 (by norm_num) ⟨33066, by rfl⟩ (by norm_num))
theorem R88213 : Reach 88213 := rs (se 6 (by rfl) ⟨2067, by rfl⟩) (B 4135 (by norm_num) ⟨2067, by rfl⟩ (by norm_num))
theorem R88249 : Reach 88249 := rs (se 2 (by rfl) ⟨33093, by rfl⟩) (B 66187 (by norm_num) ⟨33093, by rfl⟩ (by norm_num))
theorem R579797 : Reach 579797 := rs (se 7 (by rfl) ⟨6794, by rfl⟩) (B 13589 (by norm_num) ⟨6794, by rfl⟩ (by norm_num))
theorem R88285 : Reach 88285 := rs (se 3 (by rfl) ⟨16553, by rfl⟩) (B 33107 (by norm_num) ⟨16553, by rfl⟩ (by norm_num))
theorem R121085 : Reach 121085 := rs (se 3 (by rfl) ⟨22703, by rfl⟩) (B 45407 (by norm_num) ⟨22703, by rfl⟩ (by norm_num))
theorem R88321 : Reach 88321 := rs (se 2 (by rfl) ⟨33120, by rfl⟩) (B 66241 (by norm_num) ⟨33120, by rfl⟩ (by norm_num))
theorem R121117 : Reach 121117 := rs (se 3 (by rfl) ⟨22709, by rfl⟩) (B 45419 (by norm_num) ⟨22709, by rfl⟩ (by norm_num))
theorem R88357 : Reach 88357 := rs (se 4 (by rfl) ⟨8283, by rfl⟩) (B 16567 (by norm_num) ⟨8283, by rfl⟩ (by norm_num))
theorem R88393 : Reach 88393 := rs (se 2 (by rfl) ⟨33147, by rfl⟩) (B 66295 (by norm_num) ⟨33147, by rfl⟩ (by norm_num))
theorem R88429 : Reach 88429 := rs (se 3 (by rfl) ⟨16580, by rfl⟩) (B 33161 (by norm_num) ⟨16580, by rfl⟩ (by norm_num))
theorem R88465 : Reach 88465 := rs (se 2 (by rfl) ⟨33174, by rfl⟩) (B 66349 (by norm_num) ⟨33174, by rfl⟩ (by norm_num))
theorem R88501 : Reach 88501 := rs (se 5 (by rfl) ⟨4148, by rfl⟩) (B 8297 (by norm_num) ⟨4148, by rfl⟩ (by norm_num))
theorem R88537 : Reach 88537 := rs (se 2 (by rfl) ⟨33201, by rfl⟩) (B 66403 (by norm_num) ⟨33201, by rfl⟩ (by norm_num))
theorem R88561 : Reach 88561 := rs (se 2 (by rfl) ⟨33210, by rfl⟩) (B 66421 (by norm_num) ⟨33210, by rfl⟩ (by norm_num))
theorem R88573 : Reach 88573 := rs (se 3 (by rfl) ⟨16607, by rfl⟩) (B 33215 (by norm_num) ⟨16607, by rfl⟩ (by norm_num))
theorem R154133 : Reach 154133 := rs (se 6 (by rfl) ⟨3612, by rfl⟩) (B 7225 (by norm_num) ⟨3612, by rfl⟩ (by norm_num))
theorem R88609 : Reach 88609 := rs (se 2 (by rfl) ⟨33228, by rfl⟩) (B 66457 (by norm_num) ⟨33228, by rfl⟩ (by norm_num))
theorem R88645 : Reach 88645 := rs (se 4 (by rfl) ⟨8310, by rfl⟩) (B 16621 (by norm_num) ⟨8310, by rfl⟩ (by norm_num))
theorem R88681 : Reach 88681 := rs (se 2 (by rfl) ⟨33255, by rfl⟩) (B 66511 (by norm_num) ⟨33255, by rfl⟩ (by norm_num))
theorem R88717 : Reach 88717 := rs (se 3 (by rfl) ⟨16634, by rfl⟩) (B 33269 (by norm_num) ⟨16634, by rfl⟩ (by norm_num))
theorem R88753 : Reach 88753 := rs (se 2 (by rfl) ⟨33282, by rfl⟩) (B 66565 (by norm_num) ⟨33282, by rfl⟩ (by norm_num))
theorem R88789 : Reach 88789 := rs (se 7 (by rfl) ⟨1040, by rfl⟩) (B 2081 (by norm_num) ⟨1040, by rfl⟩ (by norm_num))
theorem R88825 : Reach 88825 := rs (se 2 (by rfl) ⟨33309, by rfl⟩) (B 66619 (by norm_num) ⟨33309, by rfl⟩ (by norm_num))
theorem R88861 : Reach 88861 := rs (se 3 (by rfl) ⟨16661, by rfl⟩) (B 33323 (by norm_num) ⟨16661, by rfl⟩ (by norm_num))
theorem R88897 : Reach 88897 := rs (se 2 (by rfl) ⟨33336, by rfl⟩) (B 66673 (by norm_num) ⟨33336, by rfl⟩ (by norm_num))
theorem R88933 : Reach 88933 := rs (se 4 (by rfl) ⟨8337, by rfl⟩) (B 16675 (by norm_num) ⟨8337, by rfl⟩ (by norm_num))
theorem R88969 : Reach 88969 := rs (se 2 (by rfl) ⟨33363, by rfl⟩) (B 66727 (by norm_num) ⟨33363, by rfl⟩ (by norm_num))
theorem R89005 : Reach 89005 := rs (se 3 (by rfl) ⟨16688, by rfl⟩) (B 33377 (by norm_num) ⟨16688, by rfl⟩ (by norm_num))
theorem R220117 : Reach 220117 := rs (se 7 (by rfl) ⟨2579, by rfl⟩) (B 5159 (by norm_num) ⟨2579, by rfl⟩ (by norm_num))
theorem R384101 : Reach 384101 := rs (se 4 (by rfl) ⟨36009, by rfl⟩) (B 72019 (by norm_num) ⟨36009, by rfl⟩ (by norm_num))
theorem R122045 : Reach 122045 := rs (se 3 (by rfl) ⟨22883, by rfl⟩) (B 45767 (by norm_num) ⟨22883, by rfl⟩ (by norm_num))
theorem R220421 : Reach 220421 := rs (se 4 (by rfl) ⟨20664, by rfl⟩) (B 41329 (by norm_num) ⟨20664, by rfl⟩ (by norm_num))
theorem R89437 : Reach 89437 := rs (se 3 (by rfl) ⟨16769, by rfl⟩) (B 33539 (by norm_num) ⟨16769, by rfl⟩ (by norm_num))
theorem R122413 : Reach 122413 := rs (se 3 (by rfl) ⟨22952, by rfl⟩) (B 45905 (by norm_num) ⟨22952, by rfl⟩ (by norm_num))
theorem R646805 : Reach 646805 := rs (se 6 (by rfl) ⟨15159, by rfl⟩) (B 30319 (by norm_num) ⟨15159, by rfl⟩ (by norm_num))
theorem R253637 : Reach 253637 := rs (se 4 (by rfl) ⟨23778, by rfl⟩) (B 47557 (by norm_num) ⟨23778, by rfl⟩ (by norm_num))
theorem R122725 : Reach 122725 := rs (se 4 (by rfl) ⟨11505, by rfl⟩) (B 23011 (by norm_num) ⟨11505, by rfl⟩ (by norm_num))
theorem R581525 : Reach 581525 := rs (se 6 (by rfl) ⟨13629, by rfl⟩) (B 27259 (by norm_num) ⟨13629, by rfl⟩ (by norm_num))
theorem R122789 : Reach 122789 := rs (se 4 (by rfl) ⟨11511, by rfl⟩) (B 23023 (by norm_num) ⟨11511, by rfl⟩ (by norm_num))
theorem R221093 : Reach 221093 := rs (se 4 (by rfl) ⟨20727, by rfl⟩) (B 41455 (by norm_num) ⟨20727, by rfl⟩ (by norm_num))
theorem R680021 : Reach 680021 := rs (se 8 (by rfl) ⟨3984, by rfl⟩) (B 7969 (by norm_num) ⟨3984, by rfl⟩ (by norm_num))
theorem R254069 : Reach 254069 := rs (se 5 (by rfl) ⟨11909, by rfl⟩) (B 23819 (by norm_num) ⟨11909, by rfl⟩ (by norm_num))
theorem R221525 : Reach 221525 := rs (se 10 (by rfl) ⟨324, by rfl⟩) (B 649 (by norm_num) ⟨324, by rfl⟩ (by norm_num))
theorem R385397 : Reach 385397 := rs (se 5 (by rfl) ⟨18065, by rfl⟩) (B 36131 (by norm_num) ⟨18065, by rfl⟩ (by norm_num))
theorem R221717 : Reach 221717 := rs (se 6 (by rfl) ⟨5196, by rfl⟩) (B 10393 (by norm_num) ⟨5196, by rfl⟩ (by norm_num))
theorem R254501 : Reach 254501 := rs (se 4 (by rfl) ⟨23859, by rfl⟩) (B 47719 (by norm_num) ⟨23859, by rfl⟩ (by norm_num))
theorem R287333 : Reach 287333 := rs (se 4 (by rfl) ⟨26937, by rfl⟩) (B 53875 (by norm_num) ⟨26937, by rfl⟩ (by norm_num))
theorem R90929 : Reach 90929 := rs (se 2 (by rfl) ⟨34098, by rfl⟩) (B 68197 (by norm_num) ⟨34098, by rfl⟩ (by norm_num))
theorem R287621 : Reach 287621 := rs (se 4 (by rfl) ⟨26964, by rfl⟩) (B 53929 (by norm_num) ⟨26964, by rfl⟩ (by norm_num))
theorem R189373 : Reach 189373 := rs (se 3 (by rfl) ⟨35507, by rfl⟩) (B 71015 (by norm_num) ⟨35507, by rfl⟩ (by norm_num))
theorem R254933 : Reach 254933 := rs (se 7 (by rfl) ⟨2987, by rfl⟩) (B 5975 (by norm_num) ⟨2987, by rfl⟩ (by norm_num))
theorem R1369045 : Reach 1369045 := rs (se 7 (by rfl) ⟨16043, by rfl⟩) (B 32087 (by norm_num) ⟨16043, by rfl⟩ (by norm_num))
theorem R222277 : Reach 222277 := rs (se 4 (by rfl) ⟨20838, by rfl⟩) (B 41677 (by norm_num) ⟨20838, by rfl⟩ (by norm_num))
theorem R124109 : Reach 124109 := rs (se 3 (by rfl) ⟨23270, by rfl⟩) (B 46541 (by norm_num) ⟨23270, by rfl⟩ (by norm_num))
theorem R681205 : Reach 681205 := rs (se 5 (by rfl) ⟨31931, by rfl⟩) (B 63863 (by norm_num) ⟨31931, by rfl⟩ (by norm_num))
theorem R517429 : Reach 517429 := rs (se 5 (by rfl) ⟨24254, by rfl⟩) (B 48509 (by norm_num) ⟨24254, by rfl⟩ (by norm_num))
theorem R255365 : Reach 255365 := rs (se 4 (by rfl) ⟨23940, by rfl⟩) (B 47881 (by norm_num) ⟨23940, by rfl⟩ (by norm_num))
theorem R124301 : Reach 124301 := rs (se 3 (by rfl) ⟨23306, by rfl⟩) (B 46613 (by norm_num) ⟨23306, by rfl⟩ (by norm_num))
theorem R91621 : Reach 91621 := rs (se 4 (by rfl) ⟨8589, by rfl⟩) (B 17179 (by norm_num) ⟨8589, by rfl⟩ (by norm_num))
theorem R157157 : Reach 157157 := rs (se 4 (by rfl) ⟨14733, by rfl⟩) (B 29467 (by norm_num) ⟨14733, by rfl⟩ (by norm_num))
theorem R222725 : Reach 222725 := rs (se 4 (by rfl) ⟨20880, by rfl⟩) (B 41761 (by norm_num) ⟨20880, by rfl⟩ (by norm_num))
theorem R124429 : Reach 124429 := rs (se 3 (by rfl) ⟨23330, by rfl⟩) (B 46661 (by norm_num) ⟨23330, by rfl⟩ (by norm_num))
theorem R189989 : Reach 189989 := rs (se 4 (by rfl) ⟨17811, by rfl⟩) (B 35623 (by norm_num) ⟨17811, by rfl⟩ (by norm_num))
theorem R386693 : Reach 386693 := rs (se 4 (by rfl) ⟨36252, by rfl⟩) (B 72505 (by norm_num) ⟨36252, by rfl⟩ (by norm_num))
theorem R91837 : Reach 91837 := rs (se 3 (by rfl) ⟨17219, by rfl⟩) (B 34439 (by norm_num) ⟨17219, by rfl⟩ (by norm_num))
theorem R255797 : Reach 255797 := rs (se 5 (by rfl) ⟨11990, by rfl⟩) (B 23981 (by norm_num) ⟨11990, by rfl⟩ (by norm_num))
theorem R190309 : Reach 190309 := rs (se 4 (by rfl) ⟨17841, by rfl⟩) (B 35683 (by norm_num) ⟨17841, by rfl⟩ (by norm_num))
theorem R190421 : Reach 190421 := rs (se 7 (by rfl) ⟨2231, by rfl⟩) (B 4463 (by norm_num) ⟨2231, by rfl⟩ (by norm_num))
theorem R288805 : Reach 288805 := rs (se 4 (by rfl) ⟨27075, by rfl⟩) (B 54151 (by norm_num) ⟨27075, by rfl⟩ (by norm_num))
theorem R125069 : Reach 125069 := rs (se 3 (by rfl) ⟨23450, by rfl⟩) (B 46901 (by norm_num) ⟨23450, by rfl⟩ (by norm_num))
theorem R190613 : Reach 190613 := rs (se 6 (by rfl) ⟨4467, by rfl⟩) (B 8935 (by norm_num) ⟨4467, by rfl⟩ (by norm_num))
theorem R256229 : Reach 256229 := rs (se 4 (by rfl) ⟨24021, by rfl⟩) (B 48043 (by norm_num) ⟨24021, by rfl⟩ (by norm_num))
theorem R289109 : Reach 289109 := rs (se 10 (by rfl) ⟨423, by rfl⟩) (B 847 (by norm_num) ⟨423, by rfl⟩ (by norm_num))
theorem R92569 : Reach 92569 := rs (se 2 (by rfl) ⟨34713, by rfl⟩) (B 69427 (by norm_num) ⟨34713, by rfl⟩ (by norm_num))
theorem R190957 : Reach 190957 := rs (se 3 (by rfl) ⟨35804, by rfl⟩) (B 71609 (by norm_num) ⟨35804, by rfl⟩ (by norm_num))
theorem R649781 : Reach 649781 := rs (se 5 (by rfl) ⟨30458, by rfl⟩) (B 60917 (by norm_num) ⟨30458, by rfl⟩ (by norm_num))
theorem R125525 : Reach 125525 := rs (se 8 (by rfl) ⟨735, by rfl⟩) (B 1471 (by norm_num) ⟨735, by rfl⟩ (by norm_num))
theorem R191069 : Reach 191069 := rs (se 3 (by rfl) ⟨35825, by rfl⟩) (B 71651 (by norm_num) ⟨35825, by rfl⟩ (by norm_num))
theorem R256661 : Reach 256661 := rs (se 6 (by rfl) ⟨6015, by rfl⟩) (B 12031 (by norm_num) ⟨6015, by rfl⟩ (by norm_num))
theorem R322309 : Reach 322309 := rs (se 4 (by rfl) ⟨30216, by rfl⟩) (B 60433 (by norm_num) ⟨30216, by rfl⟩ (by norm_num))
theorem R191261 : Reach 191261 := rs (se 3 (by rfl) ⟨35861, by rfl⟩) (B 71723 (by norm_num) ⟨35861, by rfl⟩ (by norm_num))
theorem R125749 : Reach 125749 := rs (se 5 (by rfl) ⟨5894, by rfl⟩) (B 11789 (by norm_num) ⟨5894, by rfl⟩ (by norm_num))
theorem R125813 : Reach 125813 := rs (se 5 (by rfl) ⟨5897, by rfl⟩) (B 11795 (by norm_num) ⟨5897, by rfl⟩ (by norm_num))
theorem R387989 : Reach 387989 := rs (se 6 (by rfl) ⟨9093, by rfl⟩) (B 18187 (by norm_num) ⟨9093, by rfl⟩ (by norm_num))
theorem R125941 : Reach 125941 := rs (se 5 (by rfl) ⟨5903, by rfl⟩) (B 11807 (by norm_num) ⟨5903, by rfl⟩ (by norm_num))
theorem R257093 : Reach 257093 := rs (se 4 (by rfl) ⟨24102, by rfl⟩) (B 48205 (by norm_num) ⟨24102, by rfl⟩ (by norm_num))
theorem R93253 : Reach 93253 := rs (se 4 (by rfl) ⟨8742, by rfl⟩) (B 17485 (by norm_num) ⟨8742, by rfl⟩ (by norm_num))
theorem R191605 : Reach 191605 := rs (se 5 (by rfl) ⟨8981, by rfl⟩) (B 17963 (by norm_num) ⟨8981, by rfl⟩ (by norm_num))
theorem R421013 : Reach 421013 := rs (se 6 (by rfl) ⟨9867, by rfl⟩) (B 19735 (by norm_num) ⟨9867, by rfl⟩ (by norm_num))
theorem R191717 : Reach 191717 := rs (se 4 (by rfl) ⟨17973, by rfl⟩) (B 35947 (by norm_num) ⟨17973, by rfl⟩ (by norm_num))
theorem R93533 : Reach 93533 := rs (se 3 (by rfl) ⟨17537, by rfl⟩) (B 35075 (by norm_num) ⟨17537, by rfl⟩ (by norm_num))
theorem R191909 : Reach 191909 := rs (se 4 (by rfl) ⟨17991, by rfl⟩) (B 35983 (by norm_num) ⟨17991, by rfl⟩ (by norm_num))
theorem R257525 : Reach 257525 := rs (se 5 (by rfl) ⟨12071, by rfl⟩) (B 24143 (by norm_num) ⟨12071, by rfl⟩ (by norm_num))
theorem R93745 : Reach 93745 := rs (se 2 (by rfl) ⟨35154, by rfl⟩) (B 70309 (by norm_num) ⟨35154, by rfl⟩ (by norm_num))
theorem R93889 : Reach 93889 := rs (se 2 (by rfl) ⟨35208, by rfl⟩) (B 70417 (by norm_num) ⟨35208, by rfl⟩ (by norm_num))
theorem R192253 : Reach 192253 := rs (se 3 (by rfl) ⟨36047, by rfl⟩) (B 72095 (by norm_num) ⟨36047, by rfl⟩ (by norm_num))
theorem R126805 : Reach 126805 := rs (se 9 (by rfl) ⟨371, by rfl⟩) (B 743 (by norm_num) ⟨371, by rfl⟩ (by norm_num))
theorem R225125 : Reach 225125 := rs (se 4 (by rfl) ⟨21105, by rfl⟩) (B 42211 (by norm_num) ⟨21105, by rfl⟩ (by norm_num))
theorem R192365 : Reach 192365 := rs (se 3 (by rfl) ⟨36068, by rfl⟩) (B 72137 (by norm_num) ⟨36068, by rfl⟩ (by norm_num))
theorem R257957 : Reach 257957 := rs (se 4 (by rfl) ⟨24183, by rfl⟩) (B 48367 (by norm_num) ⟨24183, by rfl⟩ (by norm_num))
theorem R126893 : Reach 126893 := rs (se 3 (by rfl) ⟨23792, by rfl⟩) (B 47585 (by norm_num) ⟨23792, by rfl⟩ (by norm_num))
theorem R127021 : Reach 127021 := rs (se 3 (by rfl) ⟨23816, by rfl⟩) (B 47633 (by norm_num) ⟨23816, by rfl⟩ (by norm_num))
theorem R192557 : Reach 192557 := rs (se 3 (by rfl) ⟨36104, by rfl⟩) (B 72209 (by norm_num) ⟨36104, by rfl⟩ (by norm_num))
theorem R127037 : Reach 127037 := rs (se 3 (by rfl) ⟨23819, by rfl⟩) (B 47639 (by norm_num) ⟨23819, by rfl⟩ (by norm_num))
theorem R2093141 : Reach 2093141 := rs (se 8 (by rfl) ⟨12264, by rfl⟩) (B 24529 (by norm_num) ⟨12264, by rfl⟩ (by norm_num))
theorem R127109 : Reach 127109 := rs (se 4 (by rfl) ⟨11916, by rfl⟩) (B 23833 (by norm_num) ⟨11916, by rfl⟩ (by norm_num))
theorem R389285 : Reach 389285 := rs (se 4 (by rfl) ⟨36495, by rfl⟩) (B 72991 (by norm_num) ⟨36495, by rfl⟩ (by norm_num))
theorem R749749 : Reach 749749 := rs (se 5 (by rfl) ⟨35144, by rfl⟩) (B 70289 (by norm_num) ⟨35144, by rfl⟩ (by norm_num))
theorem R323797 : Reach 323797 := rs (se 7 (by rfl) ⟨3794, by rfl⟩) (B 7589 (by norm_num) ⟨3794, by rfl⟩ (by norm_num))
theorem R192725 : Reach 192725 := rs (se 7 (by rfl) ⟨2258, by rfl⟩) (B 4517 (by norm_num) ⟨2258, by rfl⟩ (by norm_num))
theorem R323813 : Reach 323813 := rs (se 4 (by rfl) ⟨30357, by rfl⟩) (B 60715 (by norm_num) ⟨30357, by rfl⟩ (by norm_num))
theorem R127237 : Reach 127237 := rs (se 4 (by rfl) ⟨11928, by rfl⟩) (B 23857 (by norm_num) ⟨11928, by rfl⟩ (by norm_num))
theorem R258389 : Reach 258389 := rs (se 10 (by rfl) ⟨378, by rfl⟩) (B 757 (by norm_num) ⟨378, by rfl⟩ (by norm_num))
theorem R127325 : Reach 127325 := rs (se 3 (by rfl) ⟨23873, by rfl⟩) (B 47747 (by norm_num) ⟨23873, by rfl⟩ (by norm_num))
theorem R192901 : Reach 192901 := rs (se 4 (by rfl) ⟨18084, by rfl⟩) (B 36169 (by norm_num) ⟨18084, by rfl⟩ (by norm_num))
theorem R291221 : Reach 291221 := rs (se 6 (by rfl) ⟨6825, by rfl⟩) (B 13651 (by norm_num) ⟨6825, by rfl⟩ (by norm_num))
theorem R160157 : Reach 160157 := rs (se 3 (by rfl) ⟨30029, by rfl⟩) (B 60059 (by norm_num) ⟨30029, by rfl⟩ (by norm_num))
theorem R127453 : Reach 127453 := rs (se 3 (by rfl) ⟨23897, by rfl⟩) (B 47795 (by norm_num) ⟨23897, by rfl⟩ (by norm_num))
theorem R193013 : Reach 193013 := rs (se 5 (by rfl) ⟨9047, by rfl⟩) (B 18095 (by norm_num) ⟨9047, by rfl⟩ (by norm_num))
theorem R127541 : Reach 127541 := rs (se 5 (by rfl) ⟨5978, by rfl⟩) (B 11957 (by norm_num) ⟨5978, by rfl⟩ (by norm_num))
theorem R127637 : Reach 127637 := rs (se 6 (by rfl) ⟨2991, by rfl⟩) (B 5983 (by norm_num) ⟨2991, by rfl⟩ (by norm_num))
theorem R127669 : Reach 127669 := rs (se 5 (by rfl) ⟨5984, by rfl⟩) (B 11969 (by norm_num) ⟨5984, by rfl⟩ (by norm_num))
theorem R193205 : Reach 193205 := rs (se 5 (by rfl) ⟨9056, by rfl⟩) (B 18113 (by norm_num) ⟨9056, by rfl⟩ (by norm_num))
theorem R291509 : Reach 291509 := rs (se 5 (by rfl) ⟨13664, by rfl⟩) (B 27329 (by norm_num) ⟨13664, by rfl⟩ (by norm_num))
theorem R258821 : Reach 258821 := rs (se 4 (by rfl) ⟨24264, by rfl⟩) (B 48529 (by norm_num) ⟨24264, by rfl⟩ (by norm_num))
theorem R127757 : Reach 127757 := rs (se 3 (by rfl) ⟨23954, by rfl⟩) (B 47909 (by norm_num) ⟨23954, by rfl⟩ (by norm_num))
theorem R95089 : Reach 95089 := rs (se 2 (by rfl) ⟨35658, by rfl⟩) (B 71317 (by norm_num) ⟨35658, by rfl⟩ (by norm_num))
theorem R127885 : Reach 127885 := rs (se 3 (by rfl) ⟨23978, by rfl⟩) (B 47957 (by norm_num) ⟨23978, by rfl⟩ (by norm_num))
theorem R95185 : Reach 95185 := rs (se 2 (by rfl) ⟨35694, by rfl⟩) (B 71389 (by norm_num) ⟨35694, by rfl⟩ (by norm_num))
theorem R127973 : Reach 127973 := rs (se 4 (by rfl) ⟨11997, by rfl⟩) (B 23995 (by norm_num) ⟨11997, by rfl⟩ (by norm_num))
theorem R193549 : Reach 193549 := rs (se 3 (by rfl) ⟨36290, by rfl⟩) (B 72581 (by norm_num) ⟨36290, by rfl⟩ (by norm_num))
theorem R160805 : Reach 160805 := rs (se 4 (by rfl) ⟨15075, by rfl⟩) (B 30151 (by norm_num) ⟨15075, by rfl⟩ (by norm_num))
theorem R160813 : Reach 160813 := rs (se 3 (by rfl) ⟨30152, by rfl⟩) (B 60305 (by norm_num) ⟨30152, by rfl⟩ (by norm_num))
theorem R128101 : Reach 128101 := rs (se 4 (by rfl) ⟨12009, by rfl⟩) (B 24019 (by norm_num) ⟨12009, by rfl⟩ (by norm_num))
theorem R95357 : Reach 95357 := rs (se 3 (by rfl) ⟨17879, by rfl⟩) (B 35759 (by norm_num) ⟨17879, by rfl⟩ (by norm_num))
theorem R193661 : Reach 193661 := rs (se 3 (by rfl) ⟨36311, by rfl⟩) (B 72623 (by norm_num) ⟨36311, by rfl⟩ (by norm_num))
theorem R95413 : Reach 95413 := rs (se 5 (by rfl) ⟨4472, by rfl⟩) (B 8945 (by norm_num) ⟨4472, by rfl⟩ (by norm_num))
theorem R259253 : Reach 259253 := rs (se 5 (by rfl) ⟨12152, by rfl⟩) (B 24305 (by norm_num) ⟨12152, by rfl⟩ (by norm_num))
theorem R128189 : Reach 128189 := rs (se 3 (by rfl) ⟨24035, by rfl⟩) (B 48071 (by norm_num) ⟨24035, by rfl⟩ (by norm_num))
theorem R488693 : Reach 488693 := rs (se 5 (by rfl) ⟨22907, by rfl⟩) (B 45815 (by norm_num) ⟨22907, by rfl⟩ (by norm_num))
theorem R95509 : Reach 95509 := rs (se 6 (by rfl) ⟨2238, by rfl⟩) (B 4477 (by norm_num) ⟨2238, by rfl⟩ (by norm_num))
theorem R128317 : Reach 128317 := rs (se 3 (by rfl) ⟨24059, by rfl⟩) (B 48119 (by norm_num) ⟨24059, by rfl⟩ (by norm_num))
theorem R193853 : Reach 193853 := rs (se 3 (by rfl) ⟨36347, by rfl⟩) (B 72695 (by norm_num) ⟨36347, by rfl⟩ (by norm_num))
theorem R128405 : Reach 128405 := rs (se 6 (by rfl) ⟨3009, by rfl⟩) (B 6019 (by norm_num) ⟨3009, by rfl⟩ (by norm_num))
theorem R128413 : Reach 128413 := rs (se 3 (by rfl) ⟨24077, by rfl⟩) (B 48155 (by norm_num) ⟨24077, by rfl⟩ (by norm_num))
theorem R390581 : Reach 390581 := rs (se 5 (by rfl) ⟨18308, by rfl⟩) (B 36617 (by norm_num) ⟨18308, by rfl⟩ (by norm_num))
theorem R95681 : Reach 95681 := rs (se 2 (by rfl) ⟨35880, by rfl⟩) (B 71761 (by norm_num) ⟨35880, by rfl⟩ (by norm_num))
theorem R95737 : Reach 95737 := rs (se 2 (by rfl) ⟨35901, by rfl⟩) (B 71803 (by norm_num) ⟨35901, by rfl⟩ (by norm_num))
theorem R128533 : Reach 128533 := rs (se 6 (by rfl) ⟨3012, by rfl⟩) (B 6025 (by norm_num) ⟨3012, by rfl⟩ (by norm_num))
theorem R95833 : Reach 95833 := rs (se 2 (by rfl) ⟨35937, by rfl⟩) (B 71875 (by norm_num) ⟨35937, by rfl⟩ (by norm_num))
theorem R259685 : Reach 259685 := rs (se 4 (by rfl) ⟨24345, by rfl⟩) (B 48691 (by norm_num) ⟨24345, by rfl⟩ (by norm_num))
theorem R128621 : Reach 128621 := rs (se 3 (by rfl) ⟨24116, by rfl⟩) (B 48233 (by norm_num) ⟨24116, by rfl⟩ (by norm_num))
theorem R194197 : Reach 194197 := rs (se 6 (by rfl) ⟨4551, by rfl⟩) (B 9103 (by norm_num) ⟨4551, by rfl⟩ (by norm_num))
theorem R358037 : Reach 358037 := rs (se 6 (by rfl) ⟨8391, by rfl⟩) (B 16783 (by norm_num) ⟨8391, by rfl⟩ (by norm_num))
theorem R128749 : Reach 128749 := rs (se 3 (by rfl) ⟨24140, by rfl⟩) (B 48281 (by norm_num) ⟨24140, by rfl⟩ (by norm_num))
theorem R96005 : Reach 96005 := rs (se 4 (by rfl) ⟨9000, by rfl⟩) (B 18001 (by norm_num) ⟨9000, by rfl⟩ (by norm_num))
theorem R194309 : Reach 194309 := rs (se 4 (by rfl) ⟨18216, by rfl⟩) (B 36433 (by norm_num) ⟨18216, by rfl⟩ (by norm_num))
theorem R587573 : Reach 587573 := rs (se 5 (by rfl) ⟨27542, by rfl⟩) (B 55085 (by norm_num) ⟨27542, by rfl⟩ (by norm_num))
theorem R96061 : Reach 96061 := rs (se 3 (by rfl) ⟨18011, by rfl⟩) (B 36023 (by norm_num) ⟨18011, by rfl⟩ (by norm_num))
theorem R128837 : Reach 128837 := rs (se 4 (by rfl) ⟨12078, by rfl⟩) (B 24157 (by norm_num) ⟨12078, by rfl⟩ (by norm_num))
theorem R292693 : Reach 292693 := rs (se 9 (by rfl) ⟨857, by rfl⟩) (B 1715 (by norm_num) ⟨857, by rfl⟩ (by norm_num))
theorem R96157 : Reach 96157 := rs (se 3 (by rfl) ⟨18029, by rfl⟩) (B 36059 (by norm_num) ⟨18029, by rfl⟩ (by norm_num))
theorem R128965 : Reach 128965 := rs (se 4 (by rfl) ⟨12090, by rfl⟩) (B 24181 (by norm_num) ⟨12090, by rfl⟩ (by norm_num))
theorem R194501 : Reach 194501 := rs (se 4 (by rfl) ⟨18234, by rfl⟩) (B 36469 (by norm_num) ⟨18234, by rfl⟩ (by norm_num))
theorem R260117 : Reach 260117 := rs (se 6 (by rfl) ⟨6096, by rfl⟩) (B 12193 (by norm_num) ⟨6096, by rfl⟩ (by norm_num))
theorem R129053 : Reach 129053 := rs (se 3 (by rfl) ⟨24197, by rfl⟩) (B 48395 (by norm_num) ⟨24197, by rfl⟩ (by norm_num))
theorem R96329 : Reach 96329 := rs (se 2 (by rfl) ⟨36123, by rfl⟩) (B 72247 (by norm_num) ⟨36123, by rfl⟩ (by norm_num))
theorem R96385 : Reach 96385 := rs (se 2 (by rfl) ⟨36144, by rfl⟩) (B 72289 (by norm_num) ⟨36144, by rfl⟩ (by norm_num))
theorem R292997 : Reach 292997 := rs (se 4 (by rfl) ⟨27468, by rfl⟩) (B 54937 (by norm_num) ⟨27468, by rfl⟩ (by norm_num))
theorem R161941 : Reach 161941 := rs (se 6 (by rfl) ⟨3795, by rfl⟩) (B 7591 (by norm_num) ⟨3795, by rfl⟩ (by norm_num))
theorem R129181 : Reach 129181 := rs (se 3 (by rfl) ⟨24221, by rfl⟩) (B 48443 (by norm_num) ⟨24221, by rfl⟩ (by norm_num))
theorem R96433 : Reach 96433 := rs (se 2 (by rfl) ⟨36162, by rfl⟩) (B 72325 (by norm_num) ⟨36162, by rfl⟩ (by norm_num))
theorem R96481 : Reach 96481 := rs (se 2 (by rfl) ⟨36180, by rfl⟩) (B 72361 (by norm_num) ⟨36180, by rfl⟩ (by norm_num))
theorem R129269 : Reach 129269 := rs (se 5 (by rfl) ⟨6059, by rfl⟩) (B 12119 (by norm_num) ⟨6059, by rfl⟩ (by norm_num))
theorem R194845 : Reach 194845 := rs (se 3 (by rfl) ⟨36533, by rfl⟩) (B 73067 (by norm_num) ⟨36533, by rfl⟩ (by norm_num))
theorem R129397 : Reach 129397 := rs (se 5 (by rfl) ⟨6065, by rfl⟩) (B 12131 (by norm_num) ⟨6065, by rfl⟩ (by norm_num))
theorem R96653 : Reach 96653 := rs (se 3 (by rfl) ⟨18122, by rfl⟩) (B 36245 (by norm_num) ⟨18122, by rfl⟩ (by norm_num))
theorem R194957 : Reach 194957 := rs (se 3 (by rfl) ⟨36554, by rfl⟩) (B 73109 (by norm_num) ⟨36554, by rfl⟩ (by norm_num))
theorem R326069 : Reach 326069 := rs (se 5 (by rfl) ⟨15284, by rfl⟩) (B 30569 (by norm_num) ⟨15284, by rfl⟩ (by norm_num))
theorem R96709 : Reach 96709 := rs (se 4 (by rfl) ⟨9066, by rfl⟩) (B 18133 (by norm_num) ⟨9066, by rfl⟩ (by norm_num))
theorem R260549 : Reach 260549 := rs (se 4 (by rfl) ⟨24426, by rfl⟩) (B 48853 (by norm_num) ⟨24426, by rfl⟩ (by norm_num))
theorem R129485 : Reach 129485 := rs (se 3 (by rfl) ⟨24278, by rfl⟩) (B 48557 (by norm_num) ⟨24278, by rfl⟩ (by norm_num))
theorem R1505749 : Reach 1505749 := rs (se 7 (by rfl) ⟨17645, by rfl⟩) (B 35291 (by norm_num) ⟨17645, by rfl⟩ (by norm_num))
theorem R162317 : Reach 162317 := rs (se 3 (by rfl) ⟨30434, by rfl⟩) (B 60869 (by norm_num) ⟨30434, by rfl⟩ (by norm_num))
theorem R96805 : Reach 96805 := rs (se 4 (by rfl) ⟨9075, by rfl⟩) (B 18151 (by norm_num) ⟨9075, by rfl⟩ (by norm_num))
theorem R129613 : Reach 129613 := rs (se 3 (by rfl) ⟨24302, by rfl⟩) (B 48605 (by norm_num) ⟨24302, by rfl⟩ (by norm_num))
theorem R195149 : Reach 195149 := rs (se 3 (by rfl) ⟨36590, by rfl⟩) (B 73181 (by norm_num) ⟨36590, by rfl⟩ (by norm_num))
theorem R129701 : Reach 129701 := rs (se 4 (by rfl) ⟨12159, by rfl⟩) (B 24319 (by norm_num) ⟨12159, by rfl⟩ (by norm_num))
theorem R391877 : Reach 391877 := rs (se 4 (by rfl) ⟨36738, by rfl⟩) (B 73477 (by norm_num) ⟨36738, by rfl⟩ (by norm_num))
theorem R96977 : Reach 96977 := rs (se 2 (by rfl) ⟨36366, by rfl⟩) (B 72733 (by norm_num) ⟨36366, by rfl⟩ (by norm_num))
theorem R97033 : Reach 97033 := rs (se 2 (by rfl) ⟨36387, by rfl⟩) (B 72775 (by norm_num) ⟨36387, by rfl⟩ (by norm_num))
theorem R129829 : Reach 129829 := rs (se 4 (by rfl) ⟨12171, by rfl⟩) (B 24343 (by norm_num) ⟨12171, by rfl⟩ (by norm_num))
theorem R97129 : Reach 97129 := rs (se 2 (by rfl) ⟨36423, by rfl⟩) (B 72847 (by norm_num) ⟨36423, by rfl⟩ (by norm_num))
theorem R555893 : Reach 555893 := rs (se 5 (by rfl) ⟨26057, by rfl⟩) (B 52115 (by norm_num) ⟨26057, by rfl⟩ (by norm_num))
theorem R260981 : Reach 260981 := rs (se 5 (by rfl) ⟨12233, by rfl⟩) (B 24467 (by norm_num) ⟨12233, by rfl⟩ (by norm_num))
theorem R129917 : Reach 129917 := rs (se 3 (by rfl) ⟨24359, by rfl⟩) (B 48719 (by norm_num) ⟨24359, by rfl⟩ (by norm_num))
theorem R719765 : Reach 719765 := rs (se 6 (by rfl) ⟨16869, by rfl⟩) (B 33739 (by norm_num) ⟨16869, by rfl⟩ (by norm_num))
theorem R195493 : Reach 195493 := rs (se 4 (by rfl) ⟨18327, by rfl⟩) (B 36655 (by norm_num) ⟨18327, by rfl⟩ (by norm_num))
theorem R130045 : Reach 130045 := rs (se 3 (by rfl) ⟨24383, by rfl⟩) (B 48767 (by norm_num) ⟨24383, by rfl⟩ (by norm_num))
theorem R97301 : Reach 97301 := rs (se 6 (by rfl) ⟨2280, by rfl⟩) (B 4561 (by norm_num) ⟨2280, by rfl⟩ (by norm_num))
theorem R195605 : Reach 195605 := rs (se 6 (by rfl) ⟨4584, by rfl⟩) (B 9169 (by norm_num) ⟨4584, by rfl⟩ (by norm_num))
theorem R97357 : Reach 97357 := rs (se 3 (by rfl) ⟨18254, by rfl⟩) (B 36509 (by norm_num) ⟨18254, by rfl⟩ (by norm_num))
theorem R130133 : Reach 130133 := rs (se 8 (by rfl) ⟨762, by rfl⟩) (B 1525 (by norm_num) ⟨762, by rfl⟩ (by norm_num))
theorem R97453 : Reach 97453 := rs (se 3 (by rfl) ⟨18272, by rfl⟩) (B 36545 (by norm_num) ⟨18272, by rfl⟩ (by norm_num))
theorem R97481 : Reach 97481 := rs (se 2 (by rfl) ⟨36555, by rfl⟩) (B 73111 (by norm_num) ⟨36555, by rfl⟩ (by norm_num))
theorem R130261 : Reach 130261 := rs (se 7 (by rfl) ⟨1526, by rfl⟩) (B 3053 (by norm_num) ⟨1526, by rfl⟩ (by norm_num))
theorem R195797 : Reach 195797 := rs (se 7 (by rfl) ⟨2294, by rfl⟩) (B 4589 (by norm_num) ⟨2294, by rfl⟩ (by norm_num))
theorem R261413 : Reach 261413 := rs (se 4 (by rfl) ⟨24507, by rfl⟩) (B 49015 (by norm_num) ⟨24507, by rfl⟩ (by norm_num))
theorem R130349 : Reach 130349 := rs (se 3 (by rfl) ⟨24440, by rfl⟩) (B 48881 (by norm_num) ⟨24440, by rfl⟩ (by norm_num))
theorem R97625 : Reach 97625 := rs (se 2 (by rfl) ⟨36609, by rfl⟩) (B 73219 (by norm_num) ⟨36609, by rfl⟩ (by norm_num))
theorem R97681 : Reach 97681 := rs (se 2 (by rfl) ⟨36630, by rfl⟩) (B 73261 (by norm_num) ⟨36630, by rfl⟩ (by norm_num))
theorem R130477 : Reach 130477 := rs (se 3 (by rfl) ⟨24464, by rfl⟩) (B 48929 (by norm_num) ⟨24464, by rfl⟩ (by norm_num))
theorem R130493 : Reach 130493 := rs (se 3 (by rfl) ⟨24467, by rfl⟩) (B 48935 (by norm_num) ⟨24467, by rfl⟩ (by norm_num))
theorem R97777 : Reach 97777 := rs (se 2 (by rfl) ⟨36666, by rfl⟩) (B 73333 (by norm_num) ⟨36666, by rfl⟩ (by norm_num))
theorem R130565 : Reach 130565 := rs (se 4 (by rfl) ⟨12240, by rfl⟩) (B 24481 (by norm_num) ⟨12240, by rfl⟩ (by norm_num))
theorem R196141 : Reach 196141 := rs (se 3 (by rfl) ⟨36776, by rfl⟩) (B 73553 (by norm_num) ⟨36776, by rfl⟩ (by norm_num))
theorem R261701 : Reach 261701 := rs (se 4 (by rfl) ⟨24534, by rfl⟩) (B 49069 (by norm_num) ⟨24534, by rfl⟩ (by norm_num))
theorem R130693 : Reach 130693 := rs (se 4 (by rfl) ⟨12252, by rfl⟩) (B 24505 (by norm_num) ⟨12252, by rfl⟩ (by norm_num))
theorem R97949 : Reach 97949 := rs (se 3 (by rfl) ⟨18365, by rfl⟩) (B 36731 (by norm_num) ⟨18365, by rfl⟩ (by norm_num))
theorem R196253 : Reach 196253 := rs (se 3 (by rfl) ⟨36797, by rfl⟩) (B 73595 (by norm_num) ⟨36797, by rfl⟩ (by norm_num))
theorem R98005 : Reach 98005 := rs (se 7 (by rfl) ⟨1148, by rfl⟩) (B 2297 (by norm_num) ⟨1148, by rfl⟩ (by norm_num))
theorem R261845 : Reach 261845 := rs (se 7 (by rfl) ⟨3068, by rfl⟩) (B 6137 (by norm_num) ⟨3068, by rfl⟩ (by norm_num))
theorem R130781 : Reach 130781 := rs (se 3 (by rfl) ⟨24521, by rfl⟩) (B 49043 (by norm_num) ⟨24521, by rfl⟩ (by norm_num))
theorem R98101 : Reach 98101 := rs (se 5 (by rfl) ⟨4598, by rfl⟩) (B 9197 (by norm_num) ⟨4598, by rfl⟩ (by norm_num))
theorem R130909 : Reach 130909 := rs (se 3 (by rfl) ⟨24545, by rfl⟩) (B 49091 (by norm_num) ⟨24545, by rfl⟩ (by norm_num))
theorem R196445 : Reach 196445 := rs (se 3 (by rfl) ⟨36833, by rfl⟩) (B 73667 (by norm_num) ⟨36833, by rfl⟩ (by norm_num))
theorem R556949 : Reach 556949 := rs (se 6 (by rfl) ⟨13053, by rfl⟩) (B 26107 (by norm_num) ⟨13053, by rfl⟩ (by norm_num))
theorem R130997 : Reach 130997 := rs (se 5 (by rfl) ⟨6140, by rfl⟩) (B 12281 (by norm_num) ⟨6140, by rfl⟩ (by norm_num))
theorem R360389 : Reach 360389 := rs (se 4 (by rfl) ⟨33786, by rfl⟩) (B 67573 (by norm_num) ⟨33786, by rfl⟩ (by norm_num))
theorem R393173 : Reach 393173 := rs (se 7 (by rfl) ⟨4607, by rfl⟩) (B 9215 (by norm_num) ⟨4607, by rfl⟩ (by norm_num))
theorem R98273 : Reach 98273 := rs (se 2 (by rfl) ⟨36852, by rfl⟩) (B 73705 (by norm_num) ⟨36852, by rfl⟩ (by norm_num))
theorem R98281 : Reach 98281 := rs (se 2 (by rfl) ⟨36855, by rfl⟩) (B 73711 (by norm_num) ⟨36855, by rfl⟩ (by norm_num))
theorem R131105 : Reach 131105 := rs (se 2 (by rfl) ⟨49164, by rfl⟩) R98329
theorem R196739 : Reach 196739 := rs (se 1 (by rfl) ⟨147554, by rfl⟩) R295109
theorem R98435 : Reach 98435 := rs (se 1 (by rfl) ⟨73826, by rfl⟩) R147653
theorem R131233 : Reach 131233 := rs (se 2 (by rfl) ⟨49212, by rfl⟩) R98425
theorem R131267 : Reach 131267 := rs (se 1 (by rfl) ⟨98450, by rfl⟩) R196901
theorem R262385 : Reach 262385 := rs (se 2 (by rfl) ⟨98394, by rfl⟩) R196789
theorem R885005 : Reach 885005 := rs (se 3 (by rfl) ⟨165938, by rfl⟩) R331877
theorem R196931 : Reach 196931 := rs (se 1 (by rfl) ⟨147698, by rfl⟩) R295397
theorem R131395 : Reach 131395 := rs (se 1 (by rfl) ⟨98546, by rfl⟩) R197093
theorem R623045 : Reach 623045 := rs (se 4 (by rfl) ⟨58410, by rfl⟩) R116821
theorem R131537 : Reach 131537 := rs (se 2 (by rfl) ⟨49326, by rfl⟩) R98653
theorem R98851 : Reach 98851 := rs (se 1 (by rfl) ⟨74138, by rfl⟩) R148277
theorem R131665 : Reach 131665 := rs (se 2 (by rfl) ⟨49374, by rfl⟩) R98749
theorem R131699 : Reach 131699 := rs (se 1 (by rfl) ⟨98774, by rfl⟩) R197549
theorem R525041 : Reach 525041 := rs (se 2 (by rfl) ⟨196890, by rfl⟩) R393781
theorem R131827 : Reach 131827 := rs (se 1 (by rfl) ⟨98870, by rfl⟩) R197741
theorem R262925 : Reach 262925 := rs (se 3 (by rfl) ⟨49298, by rfl⟩) R98597
theorem R164675 : Reach 164675 := rs (se 1 (by rfl) ⟨123506, by rfl⟩) R247013
theorem R262979 : Reach 262979 := rs (se 1 (by rfl) ⟨197234, by rfl⟩) R394469
theorem R99139 : Reach 99139 := rs (se 1 (by rfl) ⟨74354, by rfl⟩) R148709
theorem R131969 : Reach 131969 := rs (se 2 (by rfl) ⟨49488, by rfl⟩) R98977
theorem R99235 : Reach 99235 := rs (se 1 (by rfl) ⟨74426, by rfl⟩) R148853
theorem R132097 : Reach 132097 := rs (se 2 (by rfl) ⟨49536, by rfl⟩) R99073
theorem R623629 : Reach 623629 := rs (se 3 (by rfl) ⟨116930, by rfl⟩) R233861
theorem R132131 : Reach 132131 := rs (se 1 (by rfl) ⟨99098, by rfl⟩) R198197
theorem R263249 : Reach 263249 := rs (se 2 (by rfl) ⟨98718, by rfl⟩) R197437
theorem R132259 : Reach 132259 := rs (se 1 (by rfl) ⟨99194, by rfl⟩) R198389
theorem R230627 : Reach 230627 := rs (se 1 (by rfl) ⟨172970, by rfl⟩) R345941
theorem R197873 : Reach 197873 := rs (se 2 (by rfl) ⟨74202, by rfl⟩) R148405
theorem R197923 : Reach 197923 := rs (se 1 (by rfl) ⟨148442, by rfl⟩) R296885
theorem R132401 : Reach 132401 := rs (se 2 (by rfl) ⟨49650, by rfl⟩) R99301
theorem R165187 : Reach 165187 := rs (se 1 (by rfl) ⟨123890, by rfl⟩) R247781
theorem R99731 : Reach 99731 := rs (se 1 (by rfl) ⟨74798, by rfl⟩) R149597
theorem R296369 : Reach 296369 := rs (se 2 (by rfl) ⟨111138, by rfl⟩) R222277
theorem R198065 : Reach 198065 := rs (se 2 (by rfl) ⟨74274, by rfl⟩) R148549
theorem R132529 : Reach 132529 := rs (se 2 (by rfl) ⟨49698, by rfl⟩) R99397
theorem R132563 : Reach 132563 := rs (se 1 (by rfl) ⟨99422, by rfl⟩) R198845
theorem R132691 : Reach 132691 := rs (se 1 (by rfl) ⟨99518, by rfl⟩) R199037
theorem R263789 : Reach 263789 := rs (se 3 (by rfl) ⟨49460, by rfl⟩) R98921
theorem R263843 : Reach 263843 := rs (se 1 (by rfl) ⟨197882, by rfl⟩) R395765
theorem R132833 : Reach 132833 := rs (se 2 (by rfl) ⟨49812, by rfl⟩) R99625
theorem R689905 : Reach 689905 := rs (se 2 (by rfl) ⟨258714, by rfl⟩) R517429
theorem R132961 : Reach 132961 := rs (se 2 (by rfl) ⟨49860, by rfl⟩) R99721
theorem R132995 : Reach 132995 := rs (se 1 (by rfl) ⟨99746, by rfl⟩) R199493
theorem R264113 : Reach 264113 := rs (se 2 (by rfl) ⟨99042, by rfl⟩) R198085
theorem R133123 : Reach 133123 := rs (se 1 (by rfl) ⟨99842, by rfl⟩) R199685
theorem R165905 : Reach 165905 := rs (se 2 (by rfl) ⟨62214, by rfl⟩) R124429
theorem R329827 : Reach 329827 := rs (se 1 (by rfl) ⟨247370, by rfl⟩) R494741
theorem R133265 : Reach 133265 := rs (se 2 (by rfl) ⟨49974, by rfl⟩) R99949
theorem R231587 : Reach 231587 := rs (se 1 (by rfl) ⟨173690, by rfl⟩) R347381
theorem R395441 : Reach 395441 := rs (se 2 (by rfl) ⟨148290, by rfl⟩) R296581
theorem R362723 : Reach 362723 := rs (se 1 (by rfl) ⟨272042, by rfl⟩) R544085
theorem R133393 : Reach 133393 := rs (se 2 (by rfl) ⟨50022, by rfl⟩) R100045
theorem R133427 : Reach 133427 := rs (se 1 (by rfl) ⟨100070, by rfl⟩) R200141
theorem R199057 : Reach 199057 := rs (se 2 (by rfl) ⟨74646, by rfl⟩) R149293
theorem R264653 : Reach 264653 := rs (se 3 (by rfl) ⟨49622, by rfl⟩) R99245
theorem R264707 : Reach 264707 := rs (se 1 (by rfl) ⟨198530, by rfl⟩) R397061
theorem R756337 : Reach 756337 := rs (se 2 (by rfl) ⟨283626, by rfl⟩) R567253
theorem R199331 : Reach 199331 := rs (se 1 (by rfl) ⟨149498, by rfl⟩) R298997
theorem R428813 : Reach 428813 := rs (se 3 (by rfl) ⟨80402, by rfl⟩) R160805
theorem R264977 : Reach 264977 := rs (se 2 (by rfl) ⟨99366, by rfl⟩) R198733
theorem R166691 : Reach 166691 := rs (se 1 (by rfl) ⟨125018, by rfl⟩) R250037
theorem R265037 : Reach 265037 := rs (se 3 (by rfl) ⟨49694, by rfl⟩) R99389
theorem R297827 : Reach 297827 := rs (se 1 (by rfl) ⟨223370, by rfl⟩) R446741
theorem R199523 : Reach 199523 := rs (se 1 (by rfl) ⟨149642, by rfl⟩) R299285
theorem R232483 : Reach 232483 := rs (se 1 (by rfl) ⟨174362, by rfl⟩) R348725
theorem R887921 : Reach 887921 := rs (se 2 (by rfl) ⟨332970, by rfl⟩) R665941
theorem R265517 : Reach 265517 := rs (se 3 (by rfl) ⟨49784, by rfl⟩) R99569
theorem R331057 : Reach 331057 := rs (se 2 (by rfl) ⟨124146, by rfl⟩) R248293
theorem R265571 : Reach 265571 := rs (se 1 (by rfl) ⟨199178, by rfl⟩) R398357
theorem R396899 : Reach 396899 := rs (se 1 (by rfl) ⟨297674, by rfl⟩) R595349
theorem R265841 : Reach 265841 := rs (se 2 (by rfl) ⟨99690, by rfl⟩) R199381
theorem R429745 : Reach 429745 := rs (se 2 (by rfl) ⟨161154, by rfl⟩) R322309
theorem R233155 : Reach 233155 := rs (se 1 (by rfl) ⟨174866, by rfl⟩) R349733
theorem R626417 : Reach 626417 := rs (se 2 (by rfl) ⟨234906, by rfl⟩) R469813
theorem R167665 : Reach 167665 := rs (se 2 (by rfl) ⟨62874, by rfl⟩) R125749
theorem R200465 : Reach 200465 := rs (se 2 (by rfl) ⟨75174, by rfl⟩) R150349
theorem R298829 : Reach 298829 := rs (se 3 (by rfl) ⟨56030, by rfl⟩) R112061
theorem R593891 : Reach 593891 := rs (se 1 (by rfl) ⟨445418, by rfl⟩) R890837
theorem R167921 : Reach 167921 := rs (se 2 (by rfl) ⟨62970, by rfl⟩) R125941
theorem R495665 : Reach 495665 := rs (se 2 (by rfl) ⟨185874, by rfl⟩) R371749
theorem R266381 : Reach 266381 := rs (se 3 (by rfl) ⟨49946, by rfl⟩) R99893
theorem R266435 : Reach 266435 := rs (se 1 (by rfl) ⟨199826, by rfl⟩) R399653
theorem R102641 : Reach 102641 := rs (se 2 (by rfl) ⟨38490, by rfl⟩) R76981
theorem R102755 : Reach 102755 := rs (se 1 (by rfl) ⟨77066, by rfl⟩) R154133
theorem R397709 : Reach 397709 := rs (se 3 (by rfl) ⟨74570, by rfl⟩) R149141
theorem R135587 : Reach 135587 := rs (se 1 (by rfl) ⟨101690, by rfl⟩) R203381
theorem R233933 : Reach 233933 := rs (se 3 (by rfl) ⟨43862, by rfl⟩) R87725
theorem R266705 : Reach 266705 := rs (se 2 (by rfl) ⟨100014, by rfl⟩) R200029
theorem R431203 : Reach 431203 := rs (se 1 (by rfl) ⟨323402, by rfl⟩) R646805
theorem R169073 : Reach 169073 := rs (se 2 (by rfl) ⟨63402, by rfl⟩) R126805
theorem R169091 : Reach 169091 := rs (se 1 (by rfl) ⟨126818, by rfl⟩) R253637
theorem R169361 : Reach 169361 := rs (se 2 (by rfl) ⟨63510, by rfl⟩) R127021
theorem R169379 : Reach 169379 := rs (se 1 (by rfl) ⟨127034, by rfl⟩) R254069
theorem R300493 : Reach 300493 := rs (se 3 (by rfl) ⟨56342, by rfl⟩) R112685
theorem R136739 : Reach 136739 := rs (se 1 (by rfl) ⟨102554, by rfl⟩) R205109
theorem R431729 : Reach 431729 := rs (se 2 (by rfl) ⟨161898, by rfl⟩) R323797
theorem R169649 : Reach 169649 := rs (se 2 (by rfl) ⟨63618, by rfl⟩) R127237
theorem R169667 : Reach 169667 := rs (se 1 (by rfl) ⟨127250, by rfl⟩) R254501
theorem R464753 : Reach 464753 := rs (se 2 (by rfl) ⟨174282, by rfl⟩) R348565
theorem R202637 : Reach 202637 := rs (se 3 (by rfl) ⟨37994, by rfl⟩) R75989
theorem R169937 : Reach 169937 := rs (se 2 (by rfl) ⟨63726, by rfl⟩) R127453
theorem R169955 : Reach 169955 := rs (se 1 (by rfl) ⟨127466, by rfl⟩) R254933
theorem R202769 : Reach 202769 := rs (se 2 (by rfl) ⟨76038, by rfl⟩) R152077
theorem R1808581 : Reach 1808581 := rs (se 4 (by rfl) ⟨169554, by rfl⟩) R339109
theorem R5445845 : Reach 5445845 := rs (se 7 (by rfl) ⟨63818, by rfl⟩) R127637
theorem R170225 : Reach 170225 := rs (se 2 (by rfl) ⟨63834, by rfl⟩) R127669
theorem R170243 : Reach 170243 := rs (se 1 (by rfl) ⟨127682, by rfl⟩) R255365
theorem R104771 : Reach 104771 := rs (se 1 (by rfl) ⟨78578, by rfl⟩) R157157
theorem R170513 : Reach 170513 := rs (se 2 (by rfl) ⟨63942, by rfl⟩) R127885
theorem R170531 : Reach 170531 := rs (se 1 (by rfl) ⟨127898, by rfl⟩) R255797
theorem R170801 : Reach 170801 := rs (se 2 (by rfl) ⟨64050, by rfl⟩) R128101
theorem R170819 : Reach 170819 := rs (se 1 (by rfl) ⟨128114, by rfl⟩) R256229
theorem R236465 : Reach 236465 := rs (se 2 (by rfl) ⟨88674, by rfl⟩) R177349
theorem R105409 : Reach 105409 := rs (se 2 (by rfl) ⟨39528, by rfl⟩) R79057
theorem R203725 : Reach 203725 := rs (se 3 (by rfl) ⟨38198, by rfl⟩) R76397
theorem R433187 : Reach 433187 := rs (se 1 (by rfl) ⟨324890, by rfl⟩) R649781
theorem R171089 : Reach 171089 := rs (se 2 (by rfl) ⟨64158, by rfl⟩) R128317
theorem R171107 : Reach 171107 := rs (se 1 (by rfl) ⟨128330, by rfl⟩) R256661
theorem R171217 : Reach 171217 := rs (se 2 (by rfl) ⟨64206, by rfl⟩) R128413
theorem R171377 : Reach 171377 := rs (se 2 (by rfl) ⟨64266, by rfl⟩) R128533
theorem R171395 : Reach 171395 := rs (se 1 (by rfl) ⟨128546, by rfl⟩) R257093
theorem R335501 : Reach 335501 := rs (se 3 (by rfl) ⟨62906, by rfl⟩) R125813
theorem R171665 : Reach 171665 := rs (se 2 (by rfl) ⟨64374, by rfl⟩) R128749
theorem R171683 : Reach 171683 := rs (se 1 (by rfl) ⟨128762, by rfl⟩) R257525
theorem R1351565 : Reach 1351565 := rs (se 3 (by rfl) ⟨253418, by rfl⟩) R506837
theorem R171953 : Reach 171953 := rs (se 2 (by rfl) ⟨64482, by rfl⟩) R128965
theorem R171971 : Reach 171971 := rs (se 1 (by rfl) ⟨128978, by rfl⟩) R257957
theorem R106529 : Reach 106529 := rs (se 2 (by rfl) ⟨39948, by rfl⟩) R79897
theorem R172241 : Reach 172241 := rs (se 2 (by rfl) ⟨64590, by rfl⟩) R129181
theorem R172259 : Reach 172259 := rs (se 1 (by rfl) ⟨129194, by rfl⟩) R258389
theorem R106771 : Reach 106771 := rs (se 1 (by rfl) ⟨80078, by rfl⟩) R160157
theorem R139601 : Reach 139601 := rs (se 2 (by rfl) ⟨52350, by rfl⟩) R104701
theorem R172529 : Reach 172529 := rs (se 2 (by rfl) ⟨64698, by rfl⟩) R129397
theorem R172547 : Reach 172547 := rs (se 1 (by rfl) ⟨129410, by rfl⟩) R258821
theorem R2007665 : Reach 2007665 := rs (se 2 (by rfl) ⟨752874, by rfl⟩) R1505749
theorem R467653 : Reach 467653 := rs (se 4 (by rfl) ⟨43842, by rfl⟩) R87685
theorem R172817 : Reach 172817 := rs (se 2 (by rfl) ⟨64806, by rfl⟩) R129613
theorem R172835 : Reach 172835 := rs (se 1 (by rfl) ⟨129626, by rfl⟩) R259253
theorem R435077 : Reach 435077 := rs (se 4 (by rfl) ⟨40788, by rfl⟩) R81577
theorem R500741 : Reach 500741 := rs (se 4 (by rfl) ⟨46944, by rfl⟩) R93889
theorem R173105 : Reach 173105 := rs (se 2 (by rfl) ⟨64914, by rfl⟩) R129829
theorem R173123 : Reach 173123 := rs (se 1 (by rfl) ⟨129842, by rfl⟩) R259685
theorem R238691 : Reach 238691 := rs (se 1 (by rfl) ⟨179018, by rfl⟩) R358037
theorem R599237 : Reach 599237 := rs (se 4 (by rfl) ⟨56178, by rfl⟩) R112357
theorem R173393 : Reach 173393 := rs (se 2 (by rfl) ⟨65022, by rfl⟩) R130045
theorem R173411 : Reach 173411 := rs (se 1 (by rfl) ⟨130058, by rfl⟩) R260117
theorem R75139 : Reach 75139 := rs (se 1 (by rfl) ⟨56354, by rfl⟩) R112709
theorem R238993 : Reach 238993 := rs (se 2 (by rfl) ⟨89622, by rfl⟩) R179245
theorem R75155 : Reach 75155 := rs (se 1 (by rfl) ⟨56366, by rfl⟩) R112733
theorem R75171 : Reach 75171 := rs (se 1 (by rfl) ⟨56378, by rfl⟩) R112757
theorem R75187 : Reach 75187 := rs (se 1 (by rfl) ⟨56390, by rfl⟩) R112781
theorem R75203 : Reach 75203 := rs (se 1 (by rfl) ⟨56402, by rfl⟩) R112805
theorem R75219 : Reach 75219 := rs (se 1 (by rfl) ⟨56414, by rfl⟩) R112829
theorem R75235 : Reach 75235 := rs (se 1 (by rfl) ⟨56426, by rfl⟩) R112853
theorem R75251 : Reach 75251 := rs (se 1 (by rfl) ⟨56438, by rfl⟩) R112877
theorem R75267 : Reach 75267 := rs (se 1 (by rfl) ⟨56450, by rfl⟩) R112901
theorem R75283 : Reach 75283 := rs (se 1 (by rfl) ⟨56462, by rfl⟩) R112925
theorem R75299 : Reach 75299 := rs (se 1 (by rfl) ⟨56474, by rfl⟩) R112949
theorem R75315 : Reach 75315 := rs (se 1 (by rfl) ⟨56486, by rfl⟩) R112973
theorem R75331 : Reach 75331 := rs (se 1 (by rfl) ⟨56498, by rfl⟩) R112997
theorem R75347 : Reach 75347 := rs (se 1 (by rfl) ⟨56510, by rfl⟩) R113021
theorem R75363 : Reach 75363 := rs (se 1 (by rfl) ⟨56522, by rfl⟩) R113045
theorem R173681 : Reach 173681 := rs (se 2 (by rfl) ⟨65130, by rfl⟩) R130261
theorem R75379 : Reach 75379 := rs (se 1 (by rfl) ⟨56534, by rfl⟩) R113069
theorem R75395 : Reach 75395 := rs (se 1 (by rfl) ⟨56546, by rfl⟩) R113093
theorem R173699 : Reach 173699 := rs (se 1 (by rfl) ⟨130274, by rfl⟩) R260549
theorem R75411 : Reach 75411 := rs (se 1 (by rfl) ⟨56558, by rfl⟩) R113117
theorem R75427 : Reach 75427 := rs (se 1 (by rfl) ⟨56570, by rfl⟩) R113141
theorem R75443 : Reach 75443 := rs (se 1 (by rfl) ⟨56582, by rfl⟩) R113165
theorem R108211 : Reach 108211 := rs (se 1 (by rfl) ⟨81158, by rfl⟩) R162317
theorem R75459 : Reach 75459 := rs (se 1 (by rfl) ⟨56594, by rfl⟩) R113189
theorem R75475 : Reach 75475 := rs (se 1 (by rfl) ⟨56606, by rfl⟩) R113213
theorem R75491 : Reach 75491 := rs (se 1 (by rfl) ⟨56618, by rfl⟩) R113237
theorem R75507 : Reach 75507 := rs (se 1 (by rfl) ⟨56630, by rfl⟩) R113261
theorem R75523 : Reach 75523 := rs (se 1 (by rfl) ⟨56642, by rfl⟩) R113285
theorem R75539 : Reach 75539 := rs (se 1 (by rfl) ⟨56654, by rfl⟩) R113309
theorem R75555 : Reach 75555 := rs (se 1 (by rfl) ⟨56666, by rfl⟩) R113333
theorem R75571 : Reach 75571 := rs (se 1 (by rfl) ⟨56678, by rfl⟩) R113357
theorem R75587 : Reach 75587 := rs (se 1 (by rfl) ⟨56690, by rfl⟩) R113381
theorem R75603 : Reach 75603 := rs (se 1 (by rfl) ⟨56702, by rfl⟩) R113405
theorem R75619 : Reach 75619 := rs (se 1 (by rfl) ⟨56714, by rfl⟩) R113429
theorem R75635 : Reach 75635 := rs (se 1 (by rfl) ⟨56726, by rfl⟩) R113453
theorem R75651 : Reach 75651 := rs (se 1 (by rfl) ⟨56738, by rfl⟩) R113477
theorem R173969 : Reach 173969 := rs (se 2 (by rfl) ⟨65238, by rfl⟩) R130477
theorem R75667 : Reach 75667 := rs (se 1 (by rfl) ⟨56750, by rfl⟩) R113501
theorem R75683 : Reach 75683 := rs (se 1 (by rfl) ⟨56762, by rfl⟩) R113525
theorem R370595 : Reach 370595 := rs (se 1 (by rfl) ⟨277946, by rfl⟩) R555893
theorem R173987 : Reach 173987 := rs (se 1 (by rfl) ⟨130490, by rfl⟩) R260981
theorem R75699 : Reach 75699 := rs (se 1 (by rfl) ⟨56774, by rfl⟩) R113549
theorem R75715 : Reach 75715 := rs (se 1 (by rfl) ⟨56786, by rfl⟩) R113573
theorem R75731 : Reach 75731 := rs (se 1 (by rfl) ⟨56798, by rfl⟩) R113597
theorem R75747 : Reach 75747 := rs (se 1 (by rfl) ⟨56810, by rfl⟩) R113621
theorem R75763 : Reach 75763 := rs (se 1 (by rfl) ⟨56822, by rfl⟩) R113645
theorem R75779 : Reach 75779 := rs (se 1 (by rfl) ⟨56834, by rfl⟩) R113669
theorem R75795 : Reach 75795 := rs (se 1 (by rfl) ⟨56846, by rfl⟩) R113693
theorem R75811 : Reach 75811 := rs (se 1 (by rfl) ⟨56858, by rfl⟩) R113717
theorem R75827 : Reach 75827 := rs (se 1 (by rfl) ⟨56870, by rfl⟩) R113741
theorem R75843 : Reach 75843 := rs (se 1 (by rfl) ⟨56882, by rfl⟩) R113765
theorem R75859 : Reach 75859 := rs (se 1 (by rfl) ⟨56894, by rfl⟩) R113789
theorem R75875 : Reach 75875 := rs (se 1 (by rfl) ⟨56906, by rfl⟩) R113813
theorem R75891 : Reach 75891 := rs (se 1 (by rfl) ⟨56918, by rfl⟩) R113837
theorem R75907 : Reach 75907 := rs (se 1 (by rfl) ⟨56930, by rfl⟩) R113861
theorem R75923 : Reach 75923 := rs (se 1 (by rfl) ⟨56942, by rfl⟩) R113885
theorem R75939 : Reach 75939 := rs (se 1 (by rfl) ⟨56954, by rfl⟩) R113909
theorem R174257 : Reach 174257 := rs (se 2 (by rfl) ⟨65346, by rfl⟩) R130693
theorem R75955 : Reach 75955 := rs (se 1 (by rfl) ⟨56966, by rfl⟩) R113933
theorem R75971 : Reach 75971 := rs (se 1 (by rfl) ⟨56978, by rfl⟩) R113957
theorem R174275 : Reach 174275 := rs (se 1 (by rfl) ⟨130706, by rfl⟩) R261413
theorem R75987 : Reach 75987 := rs (se 1 (by rfl) ⟨56990, by rfl⟩) R113981
theorem R76003 : Reach 76003 := rs (se 1 (by rfl) ⟨57002, by rfl⟩) R114005
theorem R76019 : Reach 76019 := rs (se 1 (by rfl) ⟨57014, by rfl⟩) R114029
theorem R76035 : Reach 76035 := rs (se 1 (by rfl) ⟨57026, by rfl⟩) R114053
theorem R76051 : Reach 76051 := rs (se 1 (by rfl) ⟨57038, by rfl⟩) R114077
theorem R76067 : Reach 76067 := rs (se 1 (by rfl) ⟨57050, by rfl⟩) R114101
theorem R76083 : Reach 76083 := rs (se 1 (by rfl) ⟨57062, by rfl⟩) R114125
theorem R76099 : Reach 76099 := rs (se 1 (by rfl) ⟨57074, by rfl⟩) R114149
theorem R76115 : Reach 76115 := rs (se 1 (by rfl) ⟨57086, by rfl⟩) R114173
theorem R76131 : Reach 76131 := rs (se 1 (by rfl) ⟨57098, by rfl⟩) R114197
theorem R76147 : Reach 76147 := rs (se 1 (by rfl) ⟨57110, by rfl⟩) R114221
theorem R76163 : Reach 76163 := rs (se 1 (by rfl) ⟨57122, by rfl⟩) R114245
theorem R174467 : Reach 174467 := rs (se 1 (by rfl) ⟨130850, by rfl⟩) R261701
theorem R76179 : Reach 76179 := rs (se 1 (by rfl) ⟨57134, by rfl⟩) R114269
theorem R76195 : Reach 76195 := rs (se 1 (by rfl) ⟨57146, by rfl⟩) R114293
theorem R76211 : Reach 76211 := rs (se 1 (by rfl) ⟨57158, by rfl⟩) R114317
theorem R76227 : Reach 76227 := rs (se 1 (by rfl) ⟨57170, by rfl⟩) R114341
theorem R174545 : Reach 174545 := rs (se 2 (by rfl) ⟨65454, by rfl⟩) R130909
theorem R76243 : Reach 76243 := rs (se 1 (by rfl) ⟨57182, by rfl⟩) R114365
theorem R76259 : Reach 76259 := rs (se 1 (by rfl) ⟨57194, by rfl⟩) R114389
theorem R174563 : Reach 174563 := rs (se 1 (by rfl) ⟨130922, by rfl⟩) R261845
theorem R76275 : Reach 76275 := rs (se 1 (by rfl) ⟨57206, by rfl⟩) R114413
theorem R76291 : Reach 76291 := rs (se 1 (by rfl) ⟨57218, by rfl⟩) R114437
theorem R76307 : Reach 76307 := rs (se 1 (by rfl) ⟨57230, by rfl⟩) R114461
theorem R76323 : Reach 76323 := rs (se 1 (by rfl) ⟨57242, by rfl⟩) R114485
theorem R76339 : Reach 76339 := rs (se 1 (by rfl) ⟨57254, by rfl⟩) R114509
theorem R76355 : Reach 76355 := rs (se 1 (by rfl) ⟨57266, by rfl⟩) R114533
theorem R76371 : Reach 76371 := rs (se 1 (by rfl) ⟨57278, by rfl⟩) R114557
theorem R371299 : Reach 371299 := rs (se 1 (by rfl) ⟨278474, by rfl⟩) R556949
theorem R76387 : Reach 76387 := rs (se 1 (by rfl) ⟨57290, by rfl⟩) R114581
theorem R76403 : Reach 76403 := rs (se 1 (by rfl) ⟨57302, by rfl⟩) R114605
theorem R76419 : Reach 76419 := rs (se 1 (by rfl) ⟨57314, by rfl⟩) R114629
theorem R240259 : Reach 240259 := rs (se 1 (by rfl) ⟨180194, by rfl⟩) R360389
theorem R76435 : Reach 76435 := rs (se 1 (by rfl) ⟨57326, by rfl⟩) R114653
theorem R76451 : Reach 76451 := rs (se 1 (by rfl) ⟨57338, by rfl⟩) R114677
theorem R436913 : Reach 436913 := rs (se 2 (by rfl) ⟨163842, by rfl⟩) R327685
theorem R76467 : Reach 76467 := rs (se 1 (by rfl) ⟨57350, by rfl⟩) R114701
theorem R76483 : Reach 76483 := rs (se 1 (by rfl) ⟨57362, by rfl⟩) R114725
theorem R76499 : Reach 76499 := rs (se 1 (by rfl) ⟨57374, by rfl⟩) R114749
theorem R76515 : Reach 76515 := rs (se 1 (by rfl) ⟨57386, by rfl⟩) R114773
theorem R371441 : Reach 371441 := rs (se 2 (by rfl) ⟨139290, by rfl⟩) R278581
theorem R76531 : Reach 76531 := rs (se 1 (by rfl) ⟨57398, by rfl⟩) R114797
theorem R174833 : Reach 174833 := rs (se 2 (by rfl) ⟨65562, by rfl⟩) R131125
theorem R76547 : Reach 76547 := rs (se 1 (by rfl) ⟨57410, by rfl⟩) R114821
theorem R174851 : Reach 174851 := rs (se 1 (by rfl) ⟨131138, by rfl⟩) R262277
theorem R76563 : Reach 76563 := rs (se 1 (by rfl) ⟨57422, by rfl⟩) R114845
theorem R109345 : Reach 109345 := rs (se 2 (by rfl) ⟨41004, by rfl⟩) R82009
theorem R76579 : Reach 76579 := rs (se 1 (by rfl) ⟨57434, by rfl⟩) R114869
theorem R76595 : Reach 76595 := rs (se 1 (by rfl) ⟨57446, by rfl⟩) R114893
theorem R76611 : Reach 76611 := rs (se 1 (by rfl) ⟨57458, by rfl⟩) R114917
theorem R76627 : Reach 76627 := rs (se 1 (by rfl) ⟨57470, by rfl⟩) R114941
theorem R76643 : Reach 76643 := rs (se 1 (by rfl) ⟨57482, by rfl⟩) R114965
theorem R76659 : Reach 76659 := rs (se 1 (by rfl) ⟨57494, by rfl⟩) R114989
theorem R109441 : Reach 109441 := rs (se 2 (by rfl) ⟨41040, by rfl⟩) R82081
theorem R76675 : Reach 76675 := rs (se 1 (by rfl) ⟨57506, by rfl⟩) R115013
theorem R76691 : Reach 76691 := rs (se 1 (by rfl) ⟨57518, by rfl⟩) R115037
theorem R76707 : Reach 76707 := rs (se 1 (by rfl) ⟨57530, by rfl⟩) R115061
theorem R76723 : Reach 76723 := rs (se 1 (by rfl) ⟨57542, by rfl⟩) R115085
theorem R76739 : Reach 76739 := rs (se 1 (by rfl) ⟨57554, by rfl⟩) R115109
theorem R142289 : Reach 142289 := rs (se 2 (by rfl) ⟨53358, by rfl⟩) R106717
theorem R76755 : Reach 76755 := rs (se 1 (by rfl) ⟨57566, by rfl⟩) R115133
theorem R76771 : Reach 76771 := rs (se 1 (by rfl) ⟨57578, by rfl⟩) R115157
theorem R76787 : Reach 76787 := rs (se 1 (by rfl) ⟨57590, by rfl⟩) R115181
theorem R76803 : Reach 76803 := rs (se 1 (by rfl) ⟨57602, by rfl⟩) R115205
theorem R175121 : Reach 175121 := rs (se 2 (by rfl) ⟨65670, by rfl⟩) R131341
theorem R76819 : Reach 76819 := rs (se 1 (by rfl) ⟨57614, by rfl⟩) R115229
theorem R76835 : Reach 76835 := rs (se 1 (by rfl) ⟨57626, by rfl⟩) R115253
theorem R175139 : Reach 175139 := rs (se 1 (by rfl) ⟨131354, by rfl⟩) R262709
theorem R76851 : Reach 76851 := rs (se 1 (by rfl) ⟨57638, by rfl⟩) R115277
theorem R240707 : Reach 240707 := rs (se 1 (by rfl) ⟨180530, by rfl⟩) R361061
theorem R76867 : Reach 76867 := rs (se 1 (by rfl) ⟨57650, by rfl⟩) R115301
theorem R76883 : Reach 76883 := rs (se 1 (by rfl) ⟨57662, by rfl⟩) R115325
theorem R76899 : Reach 76899 := rs (se 1 (by rfl) ⟨57674, by rfl⟩) R115349
theorem R76915 : Reach 76915 := rs (se 1 (by rfl) ⟨57686, by rfl⟩) R115373
theorem R76931 : Reach 76931 := rs (se 1 (by rfl) ⟨57698, by rfl⟩) R115397
theorem R76947 : Reach 76947 := rs (se 1 (by rfl) ⟨57710, by rfl⟩) R115421
theorem R76963 : Reach 76963 := rs (se 1 (by rfl) ⟨57722, by rfl⟩) R115445
theorem R76979 : Reach 76979 := rs (se 1 (by rfl) ⟨57734, by rfl⟩) R115469
theorem R76995 : Reach 76995 := rs (se 1 (by rfl) ⟨57746, by rfl⟩) R115493
theorem R77011 : Reach 77011 := rs (se 1 (by rfl) ⟨57758, by rfl⟩) R115517
theorem R77027 : Reach 77027 := rs (se 1 (by rfl) ⟨57770, by rfl⟩) R115541
theorem R77043 : Reach 77043 := rs (se 1 (by rfl) ⟨57782, by rfl⟩) R115565
theorem R77059 : Reach 77059 := rs (se 1 (by rfl) ⟨57794, by rfl⟩) R115589
theorem R77075 : Reach 77075 := rs (se 1 (by rfl) ⟨57806, by rfl⟩) R115613
theorem R77091 : Reach 77091 := rs (se 1 (by rfl) ⟨57818, by rfl⟩) R115637
theorem R175409 : Reach 175409 := rs (se 2 (by rfl) ⟨65778, by rfl⟩) R131557
theorem R77107 : Reach 77107 := rs (se 1 (by rfl) ⟨57830, by rfl⟩) R115661
theorem R77123 : Reach 77123 := rs (se 1 (by rfl) ⟨57842, by rfl⟩) R115685
theorem R175427 : Reach 175427 := rs (se 1 (by rfl) ⟨131570, by rfl⟩) R263141
theorem R77139 : Reach 77139 := rs (se 1 (by rfl) ⟨57854, by rfl⟩) R115709
theorem R77155 : Reach 77155 := rs (se 1 (by rfl) ⟨57866, by rfl⟩) R115733
theorem R109937 : Reach 109937 := rs (se 2 (by rfl) ⟨41226, by rfl⟩) R82453
theorem R77171 : Reach 77171 := rs (se 1 (by rfl) ⟨57878, by rfl⟩) R115757
theorem R77187 : Reach 77187 := rs (se 1 (by rfl) ⟨57890, by rfl⟩) R115781
theorem R77203 : Reach 77203 := rs (se 1 (by rfl) ⟨57902, by rfl⟩) R115805
theorem R77219 : Reach 77219 := rs (se 1 (by rfl) ⟨57914, by rfl⟩) R115829
theorem R77235 : Reach 77235 := rs (se 1 (by rfl) ⟨57926, by rfl⟩) R115853
theorem R77251 : Reach 77251 := rs (se 1 (by rfl) ⟨57938, by rfl⟩) R115877
theorem R77267 : Reach 77267 := rs (se 1 (by rfl) ⟨57950, by rfl⟩) R115901
theorem R306659 : Reach 306659 := rs (se 1 (by rfl) ⟨229994, by rfl⟩) R459989
theorem R77283 : Reach 77283 := rs (se 1 (by rfl) ⟨57962, by rfl⟩) R115925
theorem R77299 : Reach 77299 := rs (se 1 (by rfl) ⟨57974, by rfl⟩) R115949
theorem R77315 : Reach 77315 := rs (se 1 (by rfl) ⟨57986, by rfl⟩) R115973
theorem R77331 : Reach 77331 := rs (se 1 (by rfl) ⟨57998, by rfl⟩) R115997
theorem R77347 : Reach 77347 := rs (se 1 (by rfl) ⟨58010, by rfl⟩) R116021
theorem R77363 : Reach 77363 := rs (se 1 (by rfl) ⟨58022, by rfl⟩) R116045
theorem R77379 : Reach 77379 := rs (se 1 (by rfl) ⟨58034, by rfl⟩) R116069
theorem R175697 : Reach 175697 := rs (se 2 (by rfl) ⟨65886, by rfl⟩) R131773
theorem R77395 : Reach 77395 := rs (se 1 (by rfl) ⟨58046, by rfl⟩) R116093
theorem R77411 : Reach 77411 := rs (se 1 (by rfl) ⟨58058, by rfl⟩) R116117
theorem R175715 : Reach 175715 := rs (se 1 (by rfl) ⟨131786, by rfl⟩) R263573
theorem R405091 : Reach 405091 := rs (se 1 (by rfl) ⟨303818, by rfl⟩) R607637
theorem R77427 : Reach 77427 := rs (se 1 (by rfl) ⟨58070, by rfl⟩) R116141
theorem R77443 : Reach 77443 := rs (se 1 (by rfl) ⟨58082, by rfl⟩) R116165
theorem R667277 : Reach 667277 := rs (se 3 (by rfl) ⟨125114, by rfl⟩) R250229
theorem R77459 : Reach 77459 := rs (se 1 (by rfl) ⟨58094, by rfl⟩) R116189
theorem R77475 : Reach 77475 := rs (se 1 (by rfl) ⟨58106, by rfl⟩) R116213
theorem R77491 : Reach 77491 := rs (se 1 (by rfl) ⟨58118, by rfl⟩) R116237
theorem R77507 : Reach 77507 := rs (se 1 (by rfl) ⟨58130, by rfl⟩) R116261
theorem R77523 : Reach 77523 := rs (se 1 (by rfl) ⟨58142, by rfl⟩) R116285
theorem R77539 : Reach 77539 := rs (se 1 (by rfl) ⟨58154, by rfl⟩) R116309
theorem R77555 : Reach 77555 := rs (se 1 (by rfl) ⟨58166, by rfl⟩) R116333
theorem R77571 : Reach 77571 := rs (se 1 (by rfl) ⟨58178, by rfl⟩) R116357
theorem R77587 : Reach 77587 := rs (se 1 (by rfl) ⟨58190, by rfl⟩) R116381
theorem R77603 : Reach 77603 := rs (se 1 (by rfl) ⟨58202, by rfl⟩) R116405
theorem R77619 : Reach 77619 := rs (se 1 (by rfl) ⟨58214, by rfl⟩) R116429
theorem R77635 : Reach 77635 := rs (se 1 (by rfl) ⟨58226, by rfl⟩) R116453
theorem R77651 : Reach 77651 := rs (se 1 (by rfl) ⟨58238, by rfl⟩) R116477
theorem R143203 : Reach 143203 := rs (se 1 (by rfl) ⟨107402, by rfl⟩) R214805
theorem R77667 : Reach 77667 := rs (se 1 (by rfl) ⟨58250, by rfl⟩) R116501
theorem R175985 : Reach 175985 := rs (se 2 (by rfl) ⟨65994, by rfl⟩) R131989
theorem R77683 : Reach 77683 := rs (se 1 (by rfl) ⟨58262, by rfl⟩) R116525
theorem R77699 : Reach 77699 := rs (se 1 (by rfl) ⟨58274, by rfl⟩) R116549
theorem R176003 : Reach 176003 := rs (se 1 (by rfl) ⟨132002, by rfl⟩) R264005
theorem R77715 : Reach 77715 := rs (se 1 (by rfl) ⟨58286, by rfl⟩) R116573
theorem R77731 : Reach 77731 := rs (se 1 (by rfl) ⟨58298, by rfl⟩) R116597
theorem R339875 : Reach 339875 := rs (se 1 (by rfl) ⟨254906, by rfl⟩) R509813
theorem R77747 : Reach 77747 := rs (se 1 (by rfl) ⟨58310, by rfl⟩) R116621
theorem R77763 : Reach 77763 := rs (se 1 (by rfl) ⟨58322, by rfl⟩) R116645
theorem R77779 : Reach 77779 := rs (se 1 (by rfl) ⟨58334, by rfl⟩) R116669
theorem R77795 : Reach 77795 := rs (se 1 (by rfl) ⟨58346, by rfl⟩) R116693
theorem R77811 : Reach 77811 := rs (se 1 (by rfl) ⟨58358, by rfl⟩) R116717
theorem R143363 : Reach 143363 := rs (se 1 (by rfl) ⟨107522, by rfl⟩) R215045
theorem R77827 : Reach 77827 := rs (se 1 (by rfl) ⟨58370, by rfl⟩) R116741
theorem R77843 : Reach 77843 := rs (se 1 (by rfl) ⟨58382, by rfl⟩) R116765
theorem R77859 : Reach 77859 := rs (se 1 (by rfl) ⟨58394, by rfl⟩) R116789
theorem R77875 : Reach 77875 := rs (se 1 (by rfl) ⟨58406, by rfl⟩) R116813
theorem R77891 : Reach 77891 := rs (se 1 (by rfl) ⟨58418, by rfl⟩) R116837
theorem R77907 : Reach 77907 := rs (se 1 (by rfl) ⟨58430, by rfl⟩) R116861
theorem R77923 : Reach 77923 := rs (se 1 (by rfl) ⟨58442, by rfl⟩) R116885
theorem R77939 : Reach 77939 := rs (se 1 (by rfl) ⟨58454, by rfl⟩) R116909
theorem R77955 : Reach 77955 := rs (se 1 (by rfl) ⟨58466, by rfl⟩) R116933
theorem R176273 : Reach 176273 := rs (se 2 (by rfl) ⟨66102, by rfl⟩) R132205
theorem R77971 : Reach 77971 := rs (se 1 (by rfl) ⟨58478, by rfl⟩) R116957
theorem R77987 : Reach 77987 := rs (se 1 (by rfl) ⟨58490, by rfl⟩) R116981
theorem R176291 : Reach 176291 := rs (se 1 (by rfl) ⟨132218, by rfl⟩) R264437
theorem R78003 : Reach 78003 := rs (se 1 (by rfl) ⟨58502, by rfl⟩) R117005
theorem R78019 : Reach 78019 := rs (se 1 (by rfl) ⟨58514, by rfl⟩) R117029
theorem R110803 : Reach 110803 := rs (se 1 (by rfl) ⟨83102, by rfl⟩) R166205
theorem R78035 : Reach 78035 := rs (se 1 (by rfl) ⟨58526, by rfl⟩) R117053
theorem R78051 : Reach 78051 := rs (se 1 (by rfl) ⟨58538, by rfl⟩) R117077
theorem R78067 : Reach 78067 := rs (se 1 (by rfl) ⟨58550, by rfl⟩) R117101
theorem R78083 : Reach 78083 := rs (se 1 (by rfl) ⟨58562, by rfl⟩) R117125
theorem R78099 : Reach 78099 := rs (se 1 (by rfl) ⟨58574, by rfl⟩) R117149
theorem R78115 : Reach 78115 := rs (se 1 (by rfl) ⟨58586, by rfl⟩) R117173
theorem R110899 : Reach 110899 := rs (se 1 (by rfl) ⟨83174, by rfl⟩) R166349
theorem R78131 : Reach 78131 := rs (se 1 (by rfl) ⟨58598, by rfl⟩) R117197
theorem R78147 : Reach 78147 := rs (se 1 (by rfl) ⟨58610, by rfl⟩) R117221
theorem R78163 : Reach 78163 := rs (se 1 (by rfl) ⟨58622, by rfl⟩) R117245
theorem R78179 : Reach 78179 := rs (se 1 (by rfl) ⟨58634, by rfl⟩) R117269
theorem R78195 : Reach 78195 := rs (se 1 (by rfl) ⟨58646, by rfl⟩) R117293
theorem R78211 : Reach 78211 := rs (se 1 (by rfl) ⟨58658, by rfl⟩) R117317
theorem R78227 : Reach 78227 := rs (se 1 (by rfl) ⟨58670, by rfl⟩) R117341
theorem R78243 : Reach 78243 := rs (se 1 (by rfl) ⟨58682, by rfl⟩) R117365
theorem R176561 : Reach 176561 := rs (se 2 (by rfl) ⟨66210, by rfl⟩) R132421
theorem R78259 : Reach 78259 := rs (se 1 (by rfl) ⟨58694, by rfl⟩) R117389
theorem R78275 : Reach 78275 := rs (se 1 (by rfl) ⟨58706, by rfl⟩) R117413
theorem R176579 : Reach 176579 := rs (se 1 (by rfl) ⟨132434, by rfl⟩) R264869
theorem R78291 : Reach 78291 := rs (se 1 (by rfl) ⟨58718, by rfl⟩) R117437
theorem R78307 : Reach 78307 := rs (se 1 (by rfl) ⟨58730, by rfl⟩) R117461
theorem R78323 : Reach 78323 := rs (se 1 (by rfl) ⟨58742, by rfl⟩) R117485
theorem R78339 : Reach 78339 := rs (se 1 (by rfl) ⟨58754, by rfl⟩) R117509
theorem R78355 : Reach 78355 := rs (se 1 (by rfl) ⟨58766, by rfl⟩) R117533
theorem R78371 : Reach 78371 := rs (se 1 (by rfl) ⟨58778, by rfl⟩) R117557
theorem R78387 : Reach 78387 := rs (se 1 (by rfl) ⟨58790, by rfl⟩) R117581
theorem R78403 : Reach 78403 := rs (se 1 (by rfl) ⟨58802, by rfl⟩) R117605
theorem R78419 : Reach 78419 := rs (se 1 (by rfl) ⟨58814, by rfl⟩) R117629
theorem R78435 : Reach 78435 := rs (se 1 (by rfl) ⟨58826, by rfl⟩) R117653
theorem R78451 : Reach 78451 := rs (se 1 (by rfl) ⟨58838, by rfl⟩) R117677
theorem R78467 : Reach 78467 := rs (se 1 (by rfl) ⟨58850, by rfl⟩) R117701
theorem R78483 : Reach 78483 := rs (se 1 (by rfl) ⟨58862, by rfl⟩) R117725
theorem R78499 : Reach 78499 := rs (se 1 (by rfl) ⟨58874, by rfl⟩) R117749
theorem R307889 : Reach 307889 := rs (se 2 (by rfl) ⟨115458, by rfl⟩) R230917
theorem R78515 : Reach 78515 := rs (se 1 (by rfl) ⟨58886, by rfl⟩) R117773
theorem R78531 : Reach 78531 := rs (se 1 (by rfl) ⟨58898, by rfl⟩) R117797
theorem R176849 : Reach 176849 := rs (se 2 (by rfl) ⟨66318, by rfl⟩) R132637
theorem R78547 : Reach 78547 := rs (se 1 (by rfl) ⟨58910, by rfl⟩) R117821
theorem R78563 : Reach 78563 := rs (se 1 (by rfl) ⟨58922, by rfl⟩) R117845
theorem R176867 : Reach 176867 := rs (se 1 (by rfl) ⟨132650, by rfl⟩) R265301
theorem R635633 : Reach 635633 := rs (se 2 (by rfl) ⟨238362, by rfl⟩) R476725
theorem R78579 : Reach 78579 := rs (se 1 (by rfl) ⟨58934, by rfl⟩) R117869
theorem R78595 : Reach 78595 := rs (se 1 (by rfl) ⟨58946, by rfl⟩) R117893
theorem R373517 : Reach 373517 := rs (se 3 (by rfl) ⟨70034, by rfl⟩) R140069
theorem R78611 : Reach 78611 := rs (se 1 (by rfl) ⟨58958, by rfl⟩) R117917
theorem R111395 : Reach 111395 := rs (se 1 (by rfl) ⟨83546, by rfl⟩) R167093
theorem R78627 : Reach 78627 := rs (se 1 (by rfl) ⟨58970, by rfl⟩) R117941
theorem R242477 : Reach 242477 := rs (se 3 (by rfl) ⟨45464, by rfl⟩) R90929
theorem R78643 : Reach 78643 := rs (se 1 (by rfl) ⟨58982, by rfl⟩) R117965
theorem R78659 : Reach 78659 := rs (se 1 (by rfl) ⟨58994, by rfl⟩) R117989
theorem R78675 : Reach 78675 := rs (se 1 (by rfl) ⟨59006, by rfl⟩) R118013
theorem R78691 : Reach 78691 := rs (se 1 (by rfl) ⟨59018, by rfl⟩) R118037
theorem R78707 : Reach 78707 := rs (se 1 (by rfl) ⟨59030, by rfl⟩) R118061
theorem R78723 : Reach 78723 := rs (se 1 (by rfl) ⟨59042, by rfl⟩) R118085
theorem R78739 : Reach 78739 := rs (se 1 (by rfl) ⟨59054, by rfl⟩) R118109
theorem R78755 : Reach 78755 := rs (se 1 (by rfl) ⟨59066, by rfl⟩) R118133
theorem R78771 : Reach 78771 := rs (se 1 (by rfl) ⟨59078, by rfl⟩) R118157
theorem R78787 : Reach 78787 := rs (se 1 (by rfl) ⟨59090, by rfl⟩) R118181
theorem R144337 : Reach 144337 := rs (se 2 (by rfl) ⟨54126, by rfl⟩) R108253
theorem R78803 : Reach 78803 := rs (se 1 (by rfl) ⟨59102, by rfl⟩) R118205
theorem R78819 : Reach 78819 := rs (se 1 (by rfl) ⟨59114, by rfl⟩) R118229
theorem R177137 : Reach 177137 := rs (se 2 (by rfl) ⟨66426, by rfl⟩) R132853
theorem R78835 : Reach 78835 := rs (se 1 (by rfl) ⟨59126, by rfl⟩) R118253
theorem R177155 : Reach 177155 := rs (se 1 (by rfl) ⟨132866, by rfl⟩) R265733
theorem R78851 : Reach 78851 := rs (se 1 (by rfl) ⟨59138, by rfl⟩) R118277
theorem R78867 : Reach 78867 := rs (se 1 (by rfl) ⟨59150, by rfl⟩) R118301
theorem R78883 : Reach 78883 := rs (se 1 (by rfl) ⟨59162, by rfl⟩) R118325
theorem R144433 : Reach 144433 := rs (se 2 (by rfl) ⟨54162, by rfl⟩) R108325
theorem R78899 : Reach 78899 := rs (se 1 (by rfl) ⟨59174, by rfl⟩) R118349
theorem R78915 : Reach 78915 := rs (se 1 (by rfl) ⟨59186, by rfl⟩) R118373
theorem R144451 : Reach 144451 := rs (se 1 (by rfl) ⟨108338, by rfl⟩) R216677
theorem R78931 : Reach 78931 := rs (se 1 (by rfl) ⟨59198, by rfl⟩) R118397
theorem R275555 : Reach 275555 := rs (se 1 (by rfl) ⟨206666, by rfl⟩) R413333
theorem R78947 : Reach 78947 := rs (se 1 (by rfl) ⟨59210, by rfl⟩) R118421
theorem R78963 : Reach 78963 := rs (se 1 (by rfl) ⟨59222, by rfl⟩) R118445
theorem R78979 : Reach 78979 := rs (se 1 (by rfl) ⟨59234, by rfl⟩) R118469
theorem R701581 : Reach 701581 := rs (se 3 (by rfl) ⟨131546, by rfl⟩) R263093
theorem R78995 : Reach 78995 := rs (se 1 (by rfl) ⟨59246, by rfl⟩) R118493
theorem R79011 : Reach 79011 := rs (se 1 (by rfl) ⟨59258, by rfl⟩) R118517
theorem R79027 : Reach 79027 := rs (se 1 (by rfl) ⟨59270, by rfl⟩) R118541
theorem R79043 : Reach 79043 := rs (se 1 (by rfl) ⟨59282, by rfl⟩) R118565
theorem R144593 : Reach 144593 := rs (se 2 (by rfl) ⟨54222, by rfl⟩) R108445
theorem R79059 : Reach 79059 := rs (se 1 (by rfl) ⟨59294, by rfl⟩) R118589
theorem R79075 : Reach 79075 := rs (se 1 (by rfl) ⟨59306, by rfl⟩) R118613
theorem R79091 : Reach 79091 := rs (se 1 (by rfl) ⟨59318, by rfl⟩) R118637
theorem R79107 : Reach 79107 := rs (se 1 (by rfl) ⟨59330, by rfl⟩) R118661
theorem R177425 : Reach 177425 := rs (se 2 (by rfl) ⟨66534, by rfl⟩) R133069
theorem R79123 : Reach 79123 := rs (se 1 (by rfl) ⟨59342, by rfl⟩) R118685
theorem R177443 : Reach 177443 := rs (se 1 (by rfl) ⟨133082, by rfl⟩) R266165
theorem R112033 : Reach 112033 := rs (se 2 (by rfl) ⟨42012, by rfl⟩) R84025
theorem R505379 : Reach 505379 := rs (se 1 (by rfl) ⟨379034, by rfl⟩) R758069
theorem R177713 : Reach 177713 := rs (se 2 (by rfl) ⟨66642, by rfl⟩) R133285
theorem R112195 : Reach 112195 := rs (se 1 (by rfl) ⟨84146, by rfl⟩) R168293
theorem R177731 : Reach 177731 := rs (se 1 (by rfl) ⟨133298, by rfl⟩) R266597
theorem R112355 : Reach 112355 := rs (se 1 (by rfl) ⟨84266, by rfl⟩) R168533
theorem R112369 : Reach 112369 := rs (se 2 (by rfl) ⟨42138, by rfl⟩) R84277
theorem R178001 : Reach 178001 := rs (se 2 (by rfl) ⟨66750, by rfl⟩) R133501
theorem R178019 : Reach 178019 := rs (se 1 (by rfl) ⟨133514, by rfl⟩) R267029
theorem R145297 : Reach 145297 := rs (se 2 (by rfl) ⟨54486, by rfl⟩) R108973
theorem R505763 : Reach 505763 := rs (se 1 (by rfl) ⟨379322, by rfl⟩) R758645
theorem R210883 : Reach 210883 := rs (se 1 (by rfl) ⟨158162, by rfl⟩) R316325
theorem R112691 : Reach 112691 := rs (se 1 (by rfl) ⟨84518, by rfl⟩) R169037
theorem R112721 : Reach 112721 := rs (se 2 (by rfl) ⟨42270, by rfl⟩) R84541
theorem R145489 : Reach 145489 := rs (se 2 (by rfl) ⟨54558, by rfl⟩) R109117
theorem R112739 : Reach 112739 := rs (se 1 (by rfl) ⟨84554, by rfl⟩) R169109
theorem R112769 : Reach 112769 := rs (se 2 (by rfl) ⟨42288, by rfl⟩) R84577
theorem R112787 : Reach 112787 := rs (se 1 (by rfl) ⟨84590, by rfl⟩) R169181
theorem R112817 : Reach 112817 := rs (se 2 (by rfl) ⟨42306, by rfl⟩) R84613
theorem R112835 : Reach 112835 := rs (se 1 (by rfl) ⟨84626, by rfl⟩) R169253
theorem R112865 : Reach 112865 := rs (se 2 (by rfl) ⟨42324, by rfl⟩) R84649
theorem R112883 : Reach 112883 := rs (se 1 (by rfl) ⟨84662, by rfl⟩) R169325
theorem R112913 : Reach 112913 := rs (se 2 (by rfl) ⟨42342, by rfl⟩) R84685
theorem R112931 : Reach 112931 := rs (se 1 (by rfl) ⟨84698, by rfl⟩) R169397
theorem R112961 : Reach 112961 := rs (se 2 (by rfl) ⟨42360, by rfl⟩) R84721
theorem R112979 : Reach 112979 := rs (se 1 (by rfl) ⟨84734, by rfl⟩) R169469
theorem R113009 : Reach 113009 := rs (se 2 (by rfl) ⟨42378, by rfl⟩) R84757
theorem R113027 : Reach 113027 := rs (se 1 (by rfl) ⟨84770, by rfl⟩) R169541
theorem R113057 : Reach 113057 := rs (se 2 (by rfl) ⟨42396, by rfl⟩) R84793
theorem R113075 : Reach 113075 := rs (se 1 (by rfl) ⟨84806, by rfl⟩) R169613
theorem R113105 : Reach 113105 := rs (se 2 (by rfl) ⟨42414, by rfl⟩) R84829
theorem R113123 : Reach 113123 := rs (se 1 (by rfl) ⟨84842, by rfl⟩) R169685
theorem R145891 : Reach 145891 := rs (se 1 (by rfl) ⟨109418, by rfl⟩) R218837
theorem R113153 : Reach 113153 := rs (se 2 (by rfl) ⟨42432, by rfl⟩) R84865
theorem R145937 : Reach 145937 := rs (se 2 (by rfl) ⟨54726, by rfl⟩) R109453
theorem R113171 : Reach 113171 := rs (se 1 (by rfl) ⟨84878, by rfl⟩) R169757
theorem R113201 : Reach 113201 := rs (se 2 (by rfl) ⟨42450, by rfl⟩) R84901
theorem R113219 : Reach 113219 := rs (se 1 (by rfl) ⟨84914, by rfl⟩) R169829
theorem R440909 : Reach 440909 := rs (se 3 (by rfl) ⟨82670, by rfl⟩) R165341
theorem R113249 : Reach 113249 := rs (se 2 (by rfl) ⟨42468, by rfl⟩) R84937
theorem R113267 : Reach 113267 := rs (se 1 (by rfl) ⟨84950, by rfl⟩) R169901
theorem R113297 : Reach 113297 := rs (se 2 (by rfl) ⟨42486, by rfl⟩) R84973
theorem R113315 : Reach 113315 := rs (se 1 (by rfl) ⟨84986, by rfl⟩) R169973
theorem R113345 : Reach 113345 := rs (se 2 (by rfl) ⟨42504, by rfl⟩) R85009
theorem R408269 : Reach 408269 := rs (se 3 (by rfl) ⟨76550, by rfl⟩) R153101
theorem R211661 : Reach 211661 := rs (se 3 (by rfl) ⟨39686, by rfl⟩) R79373
theorem R113363 : Reach 113363 := rs (se 1 (by rfl) ⟨85022, by rfl⟩) R170045
theorem R113393 : Reach 113393 := rs (se 2 (by rfl) ⟨42522, by rfl⟩) R85045
theorem R113411 : Reach 113411 := rs (se 1 (by rfl) ⟨85058, by rfl⟩) R170117
theorem R113441 : Reach 113441 := rs (se 2 (by rfl) ⟨42540, by rfl⟩) R85081
theorem R146225 : Reach 146225 := rs (se 2 (by rfl) ⟨54834, by rfl⟩) R109669
theorem R113459 : Reach 113459 := rs (se 1 (by rfl) ⟨85094, by rfl⟩) R170189
theorem R113489 : Reach 113489 := rs (se 2 (by rfl) ⟨42558, by rfl⟩) R85117
theorem R80723 : Reach 80723 := rs (se 1 (by rfl) ⟨60542, by rfl⟩) R121085
theorem R113507 : Reach 113507 := rs (se 1 (by rfl) ⟨85130, by rfl⟩) R170261
theorem R113537 : Reach 113537 := rs (se 2 (by rfl) ⟨42576, by rfl⟩) R85153
theorem R113555 : Reach 113555 := rs (se 1 (by rfl) ⟨85166, by rfl⟩) R170333
theorem R113585 : Reach 113585 := rs (se 2 (by rfl) ⟨42594, by rfl⟩) R85189
theorem R113603 : Reach 113603 := rs (se 1 (by rfl) ⟨85202, by rfl⟩) R170405
theorem R113633 : Reach 113633 := rs (se 2 (by rfl) ⟨42612, by rfl⟩) R85225
theorem R113651 : Reach 113651 := rs (se 1 (by rfl) ⟨85238, by rfl⟩) R170477
theorem R113681 : Reach 113681 := rs (se 2 (by rfl) ⟨42630, by rfl⟩) R85261
theorem R113699 : Reach 113699 := rs (se 1 (by rfl) ⟨85274, by rfl⟩) R170549
theorem R113729 : Reach 113729 := rs (se 2 (by rfl) ⟨42648, by rfl⟩) R85297
theorem R113747 : Reach 113747 := rs (se 1 (by rfl) ⟨85310, by rfl⟩) R170621
theorem R113777 : Reach 113777 := rs (se 2 (by rfl) ⟨42666, by rfl⟩) R85333
theorem R113795 : Reach 113795 := rs (se 1 (by rfl) ⟨85346, by rfl⟩) R170693
theorem R113825 : Reach 113825 := rs (se 2 (by rfl) ⟨42684, by rfl⟩) R85369
theorem R113843 : Reach 113843 := rs (se 1 (by rfl) ⟨85382, by rfl⟩) R170765
theorem R867509 : Reach 867509 := rs (se 5 (by rfl) ⟨40664, by rfl⟩) R81329
theorem R113873 : Reach 113873 := rs (se 2 (by rfl) ⟨42702, by rfl⟩) R85405
theorem R113891 : Reach 113891 := rs (se 1 (by rfl) ⟨85418, by rfl⟩) R170837
theorem R113921 : Reach 113921 := rs (se 2 (by rfl) ⟨42720, by rfl⟩) R85441
theorem R113939 : Reach 113939 := rs (se 1 (by rfl) ⟨85454, by rfl⟩) R170909
theorem R113969 : Reach 113969 := rs (se 2 (by rfl) ⟨42738, by rfl⟩) R85477
theorem R113987 : Reach 113987 := rs (se 1 (by rfl) ⟨85490, by rfl⟩) R170981
theorem R114017 : Reach 114017 := rs (se 2 (by rfl) ⟨42756, by rfl⟩) R85513
theorem R114035 : Reach 114035 := rs (se 1 (by rfl) ⟨85526, by rfl⟩) R171053
theorem R114065 : Reach 114065 := rs (se 2 (by rfl) ⟨42774, by rfl⟩) R85549
theorem R114083 : Reach 114083 := rs (se 1 (by rfl) ⟨85562, by rfl⟩) R171125
theorem R114113 : Reach 114113 := rs (se 2 (by rfl) ⟨42792, by rfl⟩) R85585
theorem R114131 : Reach 114131 := rs (se 1 (by rfl) ⟨85598, by rfl⟩) R171197
theorem R114161 : Reach 114161 := rs (se 2 (by rfl) ⟨42810, by rfl⟩) R85621
theorem R114179 : Reach 114179 := rs (se 1 (by rfl) ⟨85634, by rfl⟩) R171269
theorem R146947 : Reach 146947 := rs (se 1 (by rfl) ⟨110210, by rfl⟩) R220421
theorem R114209 : Reach 114209 := rs (se 2 (by rfl) ⟨42828, by rfl⟩) R85657
theorem R114227 : Reach 114227 := rs (se 1 (by rfl) ⟨85670, by rfl⟩) R171341
theorem R114257 : Reach 114257 := rs (se 2 (by rfl) ⟨42846, by rfl⟩) R85693
theorem R114275 : Reach 114275 := rs (se 1 (by rfl) ⟨85706, by rfl⟩) R171413
theorem R114305 : Reach 114305 := rs (se 2 (by rfl) ⟨42864, by rfl⟩) R85729
theorem R114323 : Reach 114323 := rs (se 1 (by rfl) ⟨85742, by rfl⟩) R171485
theorem R114353 : Reach 114353 := rs (se 2 (by rfl) ⟨42882, by rfl⟩) R85765
theorem R114371 : Reach 114371 := rs (se 1 (by rfl) ⟨85778, by rfl⟩) R171557
theorem R114401 : Reach 114401 := rs (se 2 (by rfl) ⟨42900, by rfl⟩) R85801
theorem R114419 : Reach 114419 := rs (se 1 (by rfl) ⟨85814, by rfl⟩) R171629
theorem R376589 : Reach 376589 := rs (se 3 (by rfl) ⟨70610, by rfl⟩) R141221
theorem R114449 : Reach 114449 := rs (se 2 (by rfl) ⟨42918, by rfl⟩) R85837
theorem R114467 : Reach 114467 := rs (se 1 (by rfl) ⟨85850, by rfl⟩) R171701
theorem R114497 : Reach 114497 := rs (se 2 (by rfl) ⟨42936, by rfl⟩) R85873
theorem R114515 : Reach 114515 := rs (se 1 (by rfl) ⟨85886, by rfl⟩) R171773
theorem R180067 : Reach 180067 := rs (se 1 (by rfl) ⟨135050, by rfl⟩) R270101
theorem R114545 : Reach 114545 := rs (se 2 (by rfl) ⟨42954, by rfl⟩) R85909
theorem R114563 : Reach 114563 := rs (se 1 (by rfl) ⟨85922, by rfl⟩) R171845
theorem R2015117 : Reach 2015117 := rs (se 3 (by rfl) ⟨377834, by rfl⟩) R755669
theorem R114593 : Reach 114593 := rs (se 2 (by rfl) ⟨42972, by rfl⟩) R85945
theorem R114611 : Reach 114611 := rs (se 1 (by rfl) ⟨85958, by rfl⟩) R171917
theorem R81859 : Reach 81859 := rs (se 1 (by rfl) ⟨61394, by rfl⟩) R122789
theorem R147395 : Reach 147395 := rs (se 1 (by rfl) ⟨110546, by rfl⟩) R221093
theorem R114641 : Reach 114641 := rs (se 2 (by rfl) ⟨42990, by rfl⟩) R85981
theorem R114659 : Reach 114659 := rs (se 1 (by rfl) ⟨85994, by rfl⟩) R171989
theorem R114689 : Reach 114689 := rs (se 2 (by rfl) ⟨43008, by rfl⟩) R86017
theorem R114707 : Reach 114707 := rs (se 1 (by rfl) ⟨86030, by rfl⟩) R172061
theorem R114737 : Reach 114737 := rs (se 2 (by rfl) ⟨43026, by rfl⟩) R86053
theorem R114755 : Reach 114755 := rs (se 1 (by rfl) ⟨86066, by rfl⟩) R172133
theorem R114785 : Reach 114785 := rs (se 2 (by rfl) ⟨43044, by rfl⟩) R86089
theorem R114803 : Reach 114803 := rs (se 1 (by rfl) ⟨86102, by rfl⟩) R172205
theorem R114833 : Reach 114833 := rs (se 2 (by rfl) ⟨43062, by rfl⟩) R86125
theorem R114851 : Reach 114851 := rs (se 1 (by rfl) ⟨86138, by rfl⟩) R172277
theorem R114881 : Reach 114881 := rs (se 2 (by rfl) ⟨43080, by rfl⟩) R86161
theorem R114899 : Reach 114899 := rs (se 1 (by rfl) ⟨86174, by rfl⟩) R172349
theorem R245987 : Reach 245987 := rs (se 1 (by rfl) ⟨184490, by rfl⟩) R368981
theorem R147683 : Reach 147683 := rs (se 1 (by rfl) ⟨110762, by rfl⟩) R221525
theorem R114929 : Reach 114929 := rs (se 2 (by rfl) ⟨43098, by rfl⟩) R86197
theorem R999665 : Reach 999665 := rs (se 2 (by rfl) ⟨374874, by rfl⟩) R749749
theorem R114947 : Reach 114947 := rs (se 1 (by rfl) ⟨86210, by rfl⟩) R172421
theorem R114977 : Reach 114977 := rs (se 2 (by rfl) ⟨43116, by rfl⟩) R86233
theorem R114995 : Reach 114995 := rs (se 1 (by rfl) ⟨86246, by rfl⟩) R172493
theorem R1589557 : Reach 1589557 := rs (se 5 (by rfl) ⟨74510, by rfl⟩) R149021
theorem R115025 : Reach 115025 := rs (se 2 (by rfl) ⟨43134, by rfl⟩) R86269
theorem R147811 : Reach 147811 := rs (se 1 (by rfl) ⟨110858, by rfl⟩) R221717
theorem R115043 : Reach 115043 := rs (se 1 (by rfl) ⟨86282, by rfl⟩) R172565
theorem R115073 : Reach 115073 := rs (se 2 (by rfl) ⟨43152, by rfl⟩) R86305
theorem R115091 : Reach 115091 := rs (se 1 (by rfl) ⟨86318, by rfl⟩) R172637
theorem R115121 : Reach 115121 := rs (se 2 (by rfl) ⟨43170, by rfl⟩) R86341
theorem R115139 : Reach 115139 := rs (se 1 (by rfl) ⟨86354, by rfl⟩) R172709
theorem R115169 : Reach 115169 := rs (se 2 (by rfl) ⟨43188, by rfl⟩) R86377
theorem R115187 : Reach 115187 := rs (se 1 (by rfl) ⟨86390, by rfl⟩) R172781
theorem R573965 : Reach 573965 := rs (se 3 (by rfl) ⟨107618, by rfl⟩) R215237
theorem R115217 : Reach 115217 := rs (se 2 (by rfl) ⟨43206, by rfl⟩) R86413
theorem R115235 : Reach 115235 := rs (se 1 (by rfl) ⟨86426, by rfl⟩) R172853
theorem R115265 : Reach 115265 := rs (se 2 (by rfl) ⟨43224, by rfl⟩) R86449
theorem R115283 : Reach 115283 := rs (se 1 (by rfl) ⟨86462, by rfl⟩) R172925
theorem R115313 : Reach 115313 := rs (se 2 (by rfl) ⟨43242, by rfl⟩) R86485
theorem R115331 : Reach 115331 := rs (se 1 (by rfl) ⟨86498, by rfl⟩) R172997
theorem R115361 : Reach 115361 := rs (se 2 (by rfl) ⟨43260, by rfl⟩) R86521
theorem R115379 : Reach 115379 := rs (se 1 (by rfl) ⟨86534, by rfl⟩) R173069
theorem R410309 : Reach 410309 := rs (se 4 (by rfl) ⟨38466, by rfl⟩) R76933
theorem R115409 : Reach 115409 := rs (se 2 (by rfl) ⟨43278, by rfl⟩) R86557
theorem R115427 : Reach 115427 := rs (se 1 (by rfl) ⟨86570, by rfl⟩) R173141
theorem R115457 : Reach 115457 := rs (se 2 (by rfl) ⟨43296, by rfl⟩) R86593
theorem R443141 : Reach 443141 := rs (se 4 (by rfl) ⟨41544, by rfl⟩) R83089
theorem R115475 : Reach 115475 := rs (se 1 (by rfl) ⟨86606, by rfl⟩) R173213
theorem R246577 : Reach 246577 := rs (se 2 (by rfl) ⟨92466, by rfl⟩) R184933
theorem R115505 : Reach 115505 := rs (se 2 (by rfl) ⟨43314, by rfl⟩) R86629
theorem R82739 : Reach 82739 := rs (se 1 (by rfl) ⟨62054, by rfl⟩) R124109
theorem R115523 : Reach 115523 := rs (se 1 (by rfl) ⟨86642, by rfl⟩) R173285
theorem R115553 : Reach 115553 := rs (se 2 (by rfl) ⟨43332, by rfl⟩) R86665
theorem R115571 : Reach 115571 := rs (se 1 (by rfl) ⟨86678, by rfl⟩) R173357
theorem R115601 : Reach 115601 := rs (se 2 (by rfl) ⟨43350, by rfl⟩) R86701
theorem R115619 : Reach 115619 := rs (se 1 (by rfl) ⟨86714, by rfl⟩) R173429
theorem R82867 : Reach 82867 := rs (se 1 (by rfl) ⟨62150, by rfl⟩) R124301
theorem R115649 : Reach 115649 := rs (se 2 (by rfl) ⟨43368, by rfl⟩) R86737
theorem R115667 : Reach 115667 := rs (se 1 (by rfl) ⟨86750, by rfl⟩) R173501
theorem R1360867 : Reach 1360867 := rs (se 1 (by rfl) ⟨1020650, by rfl⟩) R2041301
theorem R115697 : Reach 115697 := rs (se 2 (by rfl) ⟨43386, by rfl⟩) R86773
theorem R115715 : Reach 115715 := rs (se 1 (by rfl) ⟨86786, by rfl⟩) R173573
theorem R148483 : Reach 148483 := rs (se 1 (by rfl) ⟨111362, by rfl⟩) R222725
theorem R115745 : Reach 115745 := rs (se 2 (by rfl) ⟨43404, by rfl⟩) R86809
theorem R115763 : Reach 115763 := rs (se 1 (by rfl) ⟨86822, by rfl⟩) R173645
theorem R115793 : Reach 115793 := rs (se 2 (by rfl) ⟨43422, by rfl⟩) R86845
theorem R115811 : Reach 115811 := rs (se 1 (by rfl) ⟨86858, by rfl⟩) R173717
theorem R115841 : Reach 115841 := rs (se 2 (by rfl) ⟨43440, by rfl⟩) R86881
theorem R148625 : Reach 148625 := rs (se 2 (by rfl) ⟨55734, by rfl⟩) R111469
theorem R115859 : Reach 115859 := rs (se 1 (by rfl) ⟨86894, by rfl⟩) R173789
theorem R115889 : Reach 115889 := rs (se 2 (by rfl) ⟨43458, by rfl⟩) R86917
theorem R115907 : Reach 115907 := rs (se 1 (by rfl) ⟨86930, by rfl⟩) R173861
theorem R115937 : Reach 115937 := rs (se 2 (by rfl) ⟨43476, by rfl⟩) R86953
theorem R115955 : Reach 115955 := rs (se 1 (by rfl) ⟨86966, by rfl⟩) R173933
theorem R115985 : Reach 115985 := rs (se 2 (by rfl) ⟨43494, by rfl⟩) R86989
theorem R116003 : Reach 116003 := rs (se 1 (by rfl) ⟨87002, by rfl⟩) R174005
theorem R116033 : Reach 116033 := rs (se 2 (by rfl) ⟨43512, by rfl⟩) R87025
theorem R116051 : Reach 116051 := rs (se 1 (by rfl) ⟨87038, by rfl⟩) R174077
theorem R116081 : Reach 116081 := rs (se 2 (by rfl) ⟨43530, by rfl⟩) R87061
theorem R116099 : Reach 116099 := rs (se 1 (by rfl) ⟨87074, by rfl⟩) R174149
theorem R214417 : Reach 214417 := rs (se 2 (by rfl) ⟨80406, by rfl⟩) R160813
theorem R116129 : Reach 116129 := rs (se 2 (by rfl) ⟨43548, by rfl⟩) R87097
theorem R443825 : Reach 443825 := rs (se 2 (by rfl) ⟨166434, by rfl⟩) R332869
theorem R116147 : Reach 116147 := rs (se 1 (by rfl) ⟨87110, by rfl⟩) R174221
theorem R116177 : Reach 116177 := rs (se 2 (by rfl) ⟨43566, by rfl⟩) R87133
theorem R116195 : Reach 116195 := rs (se 1 (by rfl) ⟨87146, by rfl⟩) R174293
theorem R116225 : Reach 116225 := rs (se 2 (by rfl) ⟨43584, by rfl⟩) R87169
theorem R116243 : Reach 116243 := rs (se 1 (by rfl) ⟨87182, by rfl⟩) R174365
theorem R116273 : Reach 116273 := rs (se 2 (by rfl) ⟨43602, by rfl⟩) R87205
theorem R116291 : Reach 116291 := rs (se 1 (by rfl) ⟨87218, by rfl⟩) R174437
theorem R116321 : Reach 116321 := rs (se 2 (by rfl) ⟨43620, by rfl⟩) R87241
theorem R116339 : Reach 116339 := rs (se 1 (by rfl) ⟨87254, by rfl⟩) R174509
theorem R116369 : Reach 116369 := rs (se 2 (by rfl) ⟨43638, by rfl⟩) R87277
theorem R116387 : Reach 116387 := rs (se 1 (by rfl) ⟨87290, by rfl⟩) R174581
theorem R116417 : Reach 116417 := rs (se 2 (by rfl) ⟨43656, by rfl⟩) R87313
theorem R116435 : Reach 116435 := rs (se 1 (by rfl) ⟨87326, by rfl⟩) R174653
theorem R83683 : Reach 83683 := rs (se 1 (by rfl) ⟨62762, by rfl⟩) R125525
theorem R116465 : Reach 116465 := rs (se 2 (by rfl) ⟨43674, by rfl⟩) R87349
theorem R116483 : Reach 116483 := rs (se 1 (by rfl) ⟨87362, by rfl⟩) R174725
theorem R3786517 : Reach 3786517 := rs (se 6 (by rfl) ⟨88746, by rfl⟩) R177493
theorem R116513 : Reach 116513 := rs (se 2 (by rfl) ⟨43692, by rfl⟩) R87385
theorem R116531 : Reach 116531 := rs (se 1 (by rfl) ⟨87398, by rfl⟩) R174797
theorem R116561 : Reach 116561 := rs (se 2 (by rfl) ⟨43710, by rfl⟩) R87421
theorem R116579 : Reach 116579 := rs (se 1 (by rfl) ⟨87434, by rfl⟩) R174869
theorem R116609 : Reach 116609 := rs (se 2 (by rfl) ⟨43728, by rfl⟩) R87457
theorem R116627 : Reach 116627 := rs (se 1 (by rfl) ⟨87470, by rfl⟩) R174941
theorem R116657 : Reach 116657 := rs (se 2 (by rfl) ⟨43746, by rfl⟩) R87493
theorem R116675 : Reach 116675 := rs (se 1 (by rfl) ⟨87506, by rfl⟩) R175013
theorem R116705 : Reach 116705 := rs (se 2 (by rfl) ⟨43764, by rfl⟩) R87529
theorem R182243 : Reach 182243 := rs (se 1 (by rfl) ⟨136682, by rfl⟩) R273365
theorem R116723 : Reach 116723 := rs (se 1 (by rfl) ⟨87542, by rfl⟩) R175085
theorem R116753 : Reach 116753 := rs (se 2 (by rfl) ⟨43782, by rfl⟩) R87565
theorem R149521 : Reach 149521 := rs (se 2 (by rfl) ⟨56070, by rfl⟩) R112141
theorem R116771 : Reach 116771 := rs (se 1 (by rfl) ⟨87578, by rfl⟩) R175157
theorem R116801 : Reach 116801 := rs (se 2 (by rfl) ⟨43800, by rfl⟩) R87601
theorem R116819 : Reach 116819 := rs (se 1 (by rfl) ⟨87614, by rfl⟩) R175229
theorem R280675 : Reach 280675 := rs (se 1 (by rfl) ⟨210506, by rfl⟩) R421013
theorem R116849 : Reach 116849 := rs (se 2 (by rfl) ⟨43818, by rfl⟩) R87637
theorem R116867 : Reach 116867 := rs (se 1 (by rfl) ⟨87650, by rfl⟩) R175301
theorem R116897 : Reach 116897 := rs (se 2 (by rfl) ⟨43836, by rfl⟩) R87673
theorem R149681 : Reach 149681 := rs (se 2 (by rfl) ⟨56130, by rfl⟩) R112261
theorem R116915 : Reach 116915 := rs (se 1 (by rfl) ⟨87686, by rfl⟩) R175373
theorem R116945 : Reach 116945 := rs (se 2 (by rfl) ⟨43854, by rfl⟩) R87709
theorem R116963 : Reach 116963 := rs (se 1 (by rfl) ⟨87722, by rfl⟩) R175445
theorem R280817 : Reach 280817 := rs (se 2 (by rfl) ⟨105306, by rfl⟩) R210613
theorem R116993 : Reach 116993 := rs (se 2 (by rfl) ⟨43872, by rfl⟩) R87745
theorem R117011 : Reach 117011 := rs (se 1 (by rfl) ⟨87758, by rfl⟩) R175517
theorem R117041 : Reach 117041 := rs (se 2 (by rfl) ⟨43890, by rfl⟩) R87781
theorem R117059 : Reach 117059 := rs (se 1 (by rfl) ⟨87794, by rfl⟩) R175589
theorem R117089 : Reach 117089 := rs (se 2 (by rfl) ⟨43908, by rfl⟩) R87817
theorem R182627 : Reach 182627 := rs (se 1 (by rfl) ⟨136970, by rfl⟩) R273941
theorem R117107 : Reach 117107 := rs (se 1 (by rfl) ⟨87830, by rfl⟩) R175661
theorem R117137 : Reach 117137 := rs (se 2 (by rfl) ⟨43926, by rfl⟩) R87853
theorem R117155 : Reach 117155 := rs (se 1 (by rfl) ⟨87866, by rfl⟩) R175733
theorem R117185 : Reach 117185 := rs (se 2 (by rfl) ⟨43944, by rfl⟩) R87889
theorem R117203 : Reach 117203 := rs (se 1 (by rfl) ⟨87902, by rfl⟩) R175805
theorem R117233 : Reach 117233 := rs (se 2 (by rfl) ⟨43962, by rfl⟩) R87925
theorem R117251 : Reach 117251 := rs (se 1 (by rfl) ⟨87938, by rfl⟩) R175877
theorem R117281 : Reach 117281 := rs (se 2 (by rfl) ⟨43980, by rfl⟩) R87961
theorem R117299 : Reach 117299 := rs (se 1 (by rfl) ⟨87974, by rfl⟩) R175949
theorem R150083 : Reach 150083 := rs (se 1 (by rfl) ⟨112562, by rfl⟩) R225125
theorem R117329 : Reach 117329 := rs (se 2 (by rfl) ⟨43998, by rfl⟩) R87997
theorem R117347 : Reach 117347 := rs (se 1 (by rfl) ⟨88010, by rfl⟩) R176021
theorem R84595 : Reach 84595 := rs (se 1 (by rfl) ⟨63446, by rfl⟩) R126893
theorem R117377 : Reach 117377 := rs (se 2 (by rfl) ⟨44016, by rfl⟩) R88033
theorem R215693 : Reach 215693 := rs (se 3 (by rfl) ⟨40442, by rfl⟩) R80885
theorem R117395 : Reach 117395 := rs (se 1 (by rfl) ⟨88046, by rfl⟩) R176093
theorem R117425 : Reach 117425 := rs (se 2 (by rfl) ⟨44034, by rfl⟩) R88069
theorem R117443 : Reach 117443 := rs (se 1 (by rfl) ⟨88082, by rfl⟩) R176165
theorem R84691 : Reach 84691 := rs (se 1 (by rfl) ⟨63518, by rfl⟩) R127037
theorem R117473 : Reach 117473 := rs (se 2 (by rfl) ⟨44052, by rfl⟩) R88105
theorem R1395427 : Reach 1395427 := rs (se 1 (by rfl) ⟨1046570, by rfl⟩) R2093141
theorem R117491 : Reach 117491 := rs (se 1 (by rfl) ⟨88118, by rfl⟩) R176237
theorem R84739 : Reach 84739 := rs (se 1 (by rfl) ⟨63554, by rfl⟩) R127109
theorem R117521 : Reach 117521 := rs (se 2 (by rfl) ⟨44070, by rfl⟩) R88141
theorem R117539 : Reach 117539 := rs (se 1 (by rfl) ⟨88154, by rfl⟩) R176309
theorem R117569 : Reach 117569 := rs (se 2 (by rfl) ⟨44088, by rfl⟩) R88177
theorem R215875 : Reach 215875 := rs (se 1 (by rfl) ⟨161906, by rfl⟩) R323813
theorem R117587 : Reach 117587 := rs (se 1 (by rfl) ⟨88190, by rfl⟩) R176381
theorem R445283 : Reach 445283 := rs (se 1 (by rfl) ⟨333962, by rfl⟩) R667925
theorem R215921 : Reach 215921 := rs (se 2 (by rfl) ⟨80970, by rfl⟩) R161941
theorem R117617 : Reach 117617 := rs (se 2 (by rfl) ⟨44106, by rfl⟩) R88213
theorem R117635 : Reach 117635 := rs (se 1 (by rfl) ⟨88226, by rfl⟩) R176453
theorem R183185 : Reach 183185 := rs (se 2 (by rfl) ⟨68694, by rfl⟩) R137389
theorem R84883 : Reach 84883 := rs (se 1 (by rfl) ⟨63662, by rfl⟩) R127325
theorem R117665 : Reach 117665 := rs (se 2 (by rfl) ⟨44124, by rfl⟩) R88249
theorem R117683 : Reach 117683 := rs (se 1 (by rfl) ⟨88262, by rfl⟩) R176525
theorem R117713 : Reach 117713 := rs (se 2 (by rfl) ⟨44142, by rfl⟩) R88285
theorem R117731 : Reach 117731 := rs (se 1 (by rfl) ⟨88298, by rfl⟩) R176597
theorem R117761 : Reach 117761 := rs (se 2 (by rfl) ⟨44160, by rfl⟩) R88321
theorem R117779 : Reach 117779 := rs (se 1 (by rfl) ⟨88334, by rfl⟩) R176669
theorem R85027 : Reach 85027 := rs (se 1 (by rfl) ⟨63770, by rfl⟩) R127541
theorem R117809 : Reach 117809 := rs (se 2 (by rfl) ⟨44178, by rfl⟩) R88357
theorem R117827 : Reach 117827 := rs (se 1 (by rfl) ⟨88370, by rfl⟩) R176741
theorem R117857 : Reach 117857 := rs (se 2 (by rfl) ⟨44196, by rfl⟩) R88393
theorem R117875 : Reach 117875 := rs (se 1 (by rfl) ⟨88406, by rfl⟩) R176813
theorem R117905 : Reach 117905 := rs (se 2 (by rfl) ⟨44214, by rfl⟩) R88429
theorem R117923 : Reach 117923 := rs (se 1 (by rfl) ⟨88442, by rfl⟩) R176885
theorem R85171 : Reach 85171 := rs (se 1 (by rfl) ⟨63878, by rfl⟩) R127757
theorem R117953 : Reach 117953 := rs (se 2 (by rfl) ⟨44232, by rfl⟩) R88465
theorem R117971 : Reach 117971 := rs (se 1 (by rfl) ⟨88478, by rfl⟩) R176957
theorem R118001 : Reach 118001 := rs (se 2 (by rfl) ⟨44250, by rfl⟩) R88501
theorem R118019 : Reach 118019 := rs (se 1 (by rfl) ⟨88514, by rfl⟩) R177029
theorem R118049 : Reach 118049 := rs (se 2 (by rfl) ⟨44268, by rfl⟩) R88537
theorem R118067 : Reach 118067 := rs (se 1 (by rfl) ⟨88550, by rfl⟩) R177101
theorem R118081 : Reach 118081 := rs (se 2 (by rfl) ⟨44280, by rfl⟩) R88561
theorem R85315 : Reach 85315 := rs (se 1 (by rfl) ⟨63986, by rfl⟩) R127973
theorem R118097 : Reach 118097 := rs (se 2 (by rfl) ⟨44286, by rfl⟩) R88573
theorem R118115 : Reach 118115 := rs (se 1 (by rfl) ⟨88586, by rfl⟩) R177173
theorem R576881 : Reach 576881 := rs (se 2 (by rfl) ⟨216330, by rfl⟩) R432661
theorem R118145 : Reach 118145 := rs (se 2 (by rfl) ⟨44304, by rfl⟩) R88609
theorem R183683 : Reach 183683 := rs (se 1 (by rfl) ⟨137762, by rfl⟩) R275525
theorem R118163 : Reach 118163 := rs (se 1 (by rfl) ⟨88622, by rfl⟩) R177245
theorem R118193 : Reach 118193 := rs (se 2 (by rfl) ⟨44322, by rfl⟩) R88645
theorem R118211 : Reach 118211 := rs (se 1 (by rfl) ⟨88658, by rfl⟩) R177317
theorem R85459 : Reach 85459 := rs (se 1 (by rfl) ⟨64094, by rfl⟩) R128189
theorem R118241 : Reach 118241 := rs (se 2 (by rfl) ⟨44340, by rfl⟩) R88681
theorem R118259 : Reach 118259 := rs (se 1 (by rfl) ⟨88694, by rfl⟩) R177389
theorem R118289 : Reach 118289 := rs (se 2 (by rfl) ⟨44358, by rfl⟩) R88717
theorem R118307 : Reach 118307 := rs (se 1 (by rfl) ⟨88730, by rfl⟩) R177461
theorem R118337 : Reach 118337 := rs (se 2 (by rfl) ⟨44376, by rfl⟩) R88753
theorem R183875 : Reach 183875 := rs (se 1 (by rfl) ⟨137906, by rfl⟩) R275813
theorem R249421 : Reach 249421 := rs (se 3 (by rfl) ⟨46766, by rfl⟩) R93533
theorem R118355 : Reach 118355 := rs (se 1 (by rfl) ⟨88766, by rfl⟩) R177533
theorem R85603 : Reach 85603 := rs (se 1 (by rfl) ⟨64202, by rfl⟩) R128405
theorem R118385 : Reach 118385 := rs (se 2 (by rfl) ⟨44394, by rfl⟩) R88789
theorem R118403 : Reach 118403 := rs (se 1 (by rfl) ⟨88802, by rfl⟩) R177605
theorem R118433 : Reach 118433 := rs (se 2 (by rfl) ⟨44412, by rfl⟩) R88825
theorem R118451 : Reach 118451 := rs (se 1 (by rfl) ⟨88838, by rfl⟩) R177677
theorem R118481 : Reach 118481 := rs (se 2 (by rfl) ⟨44430, by rfl⟩) R88861
theorem R118499 : Reach 118499 := rs (se 1 (by rfl) ⟨88874, by rfl⟩) R177749
theorem R85747 : Reach 85747 := rs (se 1 (by rfl) ⟨64310, by rfl⟩) R128621
theorem R118529 : Reach 118529 := rs (se 2 (by rfl) ⟨44448, by rfl⟩) R88897
theorem R118547 : Reach 118547 := rs (se 1 (by rfl) ⟨88910, by rfl⟩) R177821
theorem R118577 : Reach 118577 := rs (se 2 (by rfl) ⟨44466, by rfl⟩) R88933
theorem R118595 : Reach 118595 := rs (se 1 (by rfl) ⟨88946, by rfl⟩) R177893
theorem R118625 : Reach 118625 := rs (se 2 (by rfl) ⟨44484, by rfl⟩) R88969
theorem R118643 : Reach 118643 := rs (se 1 (by rfl) ⟨88982, by rfl⟩) R177965
theorem R85891 : Reach 85891 := rs (se 1 (by rfl) ⟨64418, by rfl⟩) R128837
theorem R118673 : Reach 118673 := rs (se 2 (by rfl) ⟨44502, by rfl⟩) R89005
theorem R86035 : Reach 86035 := rs (se 1 (by rfl) ⟨64526, by rfl⟩) R129053
theorem R86179 : Reach 86179 := rs (se 1 (by rfl) ⟨64634, by rfl⟩) R129269
theorem R119011 : Reach 119011 := rs (se 1 (by rfl) ⟨89258, by rfl⟩) R178517
theorem R217379 : Reach 217379 := rs (se 1 (by rfl) ⟨163034, by rfl⟩) R326069
theorem R86323 : Reach 86323 := rs (se 1 (by rfl) ⟨64742, by rfl⟩) R129485
theorem R381347 : Reach 381347 := rs (se 1 (by rfl) ⟨286010, by rfl⟩) R572021
theorem R86467 : Reach 86467 := rs (se 1 (by rfl) ⟨64850, by rfl⟩) R129701
theorem R119249 : Reach 119249 := rs (se 2 (by rfl) ⟨44718, by rfl⟩) R89437
theorem R86611 : Reach 86611 := rs (se 1 (by rfl) ⟨64958, by rfl⟩) R129917
theorem R479843 : Reach 479843 := rs (se 1 (by rfl) ⟨359882, by rfl⟩) R719765
theorem R86755 : Reach 86755 := rs (se 1 (by rfl) ⟨65066, by rfl⟩) R130133
theorem R86899 : Reach 86899 := rs (se 1 (by rfl) ⟨65174, by rfl⟩) R130349
theorem R86995 : Reach 86995 := rs (se 1 (by rfl) ⟨65246, by rfl⟩) R130493
theorem R87043 : Reach 87043 := rs (se 1 (by rfl) ⟨65282, by rfl⟩) R130565
theorem R250883 : Reach 250883 := rs (se 1 (by rfl) ⟨188162, by rfl⟩) R376325
theorem R87187 : Reach 87187 := rs (se 1 (by rfl) ⟨65390, by rfl⟩) R130781
theorem R382157 : Reach 382157 := rs (se 3 (by rfl) ⟨71654, by rfl⟩) R143309
theorem R87331 : Reach 87331 := rs (se 1 (by rfl) ⟨65498, by rfl⟩) R130997
theorem R120179 : Reach 120179 := rs (se 1 (by rfl) ⟨90134, by rfl⟩) R180269
theorem R87475 : Reach 87475 := rs (se 1 (by rfl) ⟨65606, by rfl⟩) R131213
theorem R185827 : Reach 185827 := rs (se 1 (by rfl) ⟨139370, by rfl⟩) R278741
theorem R218609 : Reach 218609 := rs (se 2 (by rfl) ⟨81978, by rfl⟩) R163957
theorem R87619 : Reach 87619 := rs (se 1 (by rfl) ⟨65714, by rfl⟩) R131429
theorem R87763 : Reach 87763 := rs (se 1 (by rfl) ⟨65822, by rfl⟩) R131645
theorem R153361 : Reach 153361 := rs (se 2 (by rfl) ⟨57510, by rfl⟩) R115021
theorem R87907 : Reach 87907 := rs (se 1 (by rfl) ⟨65930, by rfl⟩) R131861
theorem R120707 : Reach 120707 := rs (se 1 (by rfl) ⟨90530, by rfl⟩) R181061
theorem R284579 : Reach 284579 := rs (se 1 (by rfl) ⟨213434, by rfl⟩) R426869
theorem R88051 : Reach 88051 := rs (se 1 (by rfl) ⟨66038, by rfl⟩) R132077
theorem R448517 : Reach 448517 := rs (se 4 (by rfl) ⟨42048, by rfl⟩) R84097
theorem R1136693 : Reach 1136693 := rs (se 5 (by rfl) ⟨53282, by rfl⟩) R106565
theorem R88195 : Reach 88195 := rs (se 1 (by rfl) ⟨66146, by rfl⟩) R132293
theorem R547013 : Reach 547013 := rs (se 4 (by rfl) ⟨51282, by rfl⟩) R102565
theorem R88339 : Reach 88339 := rs (se 1 (by rfl) ⟨66254, by rfl⟩) R132509
theorem R88483 : Reach 88483 := rs (se 1 (by rfl) ⟨66362, by rfl⟩) R132725
theorem R448973 : Reach 448973 := rs (se 3 (by rfl) ⟨84182, by rfl⟩) R168365
theorem R88627 : Reach 88627 := rs (se 1 (by rfl) ⟨66470, by rfl⟩) R132941
theorem R252497 : Reach 252497 := rs (se 2 (by rfl) ⟨94686, by rfl⟩) R189373
theorem R187057 : Reach 187057 := rs (se 2 (by rfl) ⟨70146, by rfl⟩) R140293
theorem R88771 : Reach 88771 := rs (se 1 (by rfl) ⟨66578, by rfl⟩) R133157
theorem R285389 : Reach 285389 := rs (se 3 (by rfl) ⟨53510, by rfl⟩) R107021
theorem R1334069 : Reach 1334069 := rs (se 5 (by rfl) ⟨62534, by rfl⟩) R125069
theorem R88915 : Reach 88915 := rs (se 1 (by rfl) ⟨66686, by rfl⟩) R133373
theorem R220067 : Reach 220067 := rs (se 1 (by rfl) ⟨165050, by rfl⟩) R330101
theorem R908273 : Reach 908273 := rs (se 2 (by rfl) ⟨340602, by rfl⟩) R681205
theorem R318563 : Reach 318563 := rs (se 1 (by rfl) ⟨238922, by rfl⟩) R477845
theorem R122161 : Reach 122161 := rs (se 2 (by rfl) ⟨45810, by rfl⟩) R91621
theorem R286193 : Reach 286193 := rs (se 2 (by rfl) ⟨107322, by rfl⟩) R214645
theorem R155171 : Reach 155171 := rs (se 1 (by rfl) ⟨116378, by rfl⟩) R232757
theorem R220877 : Reach 220877 := rs (se 3 (by rfl) ⟨41414, by rfl⟩) R82829
theorem R253745 : Reach 253745 := rs (se 2 (by rfl) ⟨95154, by rfl⟩) R190309
theorem R221069 : Reach 221069 := rs (se 3 (by rfl) ⟨41450, by rfl⟩) R82901
theorem R385073 : Reach 385073 := rs (se 2 (by rfl) ⟨144402, by rfl⟩) R288805
theorem R286861 : Reach 286861 := rs (se 3 (by rfl) ⟨53786, by rfl⟩) R107573
theorem R745699 : Reach 745699 := rs (se 1 (by rfl) ⟨559274, by rfl⟩) R1118549
theorem R483569 : Reach 483569 := rs (se 2 (by rfl) ⟨181338, by rfl⟩) R362677
theorem R254285 : Reach 254285 := rs (se 3 (by rfl) ⟨47678, by rfl⟩) R95357
theorem R254339 : Reach 254339 := rs (se 1 (by rfl) ⟨190754, by rfl⟩) R381509
theorem R123425 : Reach 123425 := rs (se 2 (by rfl) ⟨46284, by rfl⟩) R92569
theorem R254609 : Reach 254609 := rs (se 2 (by rfl) ⟨95478, by rfl⟩) R190957
theorem R222061 : Reach 222061 := rs (se 3 (by rfl) ⟨41636, by rfl⟩) R83273
theorem R123763 : Reach 123763 := rs (se 1 (by rfl) ⟨92822, by rfl⟩) R185645
theorem R287651 : Reach 287651 := rs (se 1 (by rfl) ⟨215738, by rfl⟩) R431477
theorem R2057237 : Reach 2057237 := rs (se 6 (by rfl) ⟨48216, by rfl⟩) R96433
theorem R124019 : Reach 124019 := rs (se 1 (by rfl) ⟨93014, by rfl⟩) R186029
theorem R255149 : Reach 255149 := rs (se 3 (by rfl) ⟨47840, by rfl⟩) R95681
theorem R255203 : Reach 255203 := rs (se 1 (by rfl) ⟨191402, by rfl⟩) R382805
theorem R124211 : Reach 124211 := rs (se 1 (by rfl) ⟨93158, by rfl⟩) R186317
theorem R877877 : Reach 877877 := rs (se 5 (by rfl) ⟨41150, by rfl⟩) R82301
theorem R124337 : Reach 124337 := rs (se 2 (by rfl) ⟨46626, by rfl⟩) R93253
theorem R386531 : Reach 386531 := rs (se 1 (by rfl) ⟨289898, by rfl⟩) R579797
theorem R255473 : Reach 255473 := rs (se 2 (by rfl) ⟨95802, by rfl⟩) R191605
theorem R288305 : Reach 288305 := rs (se 2 (by rfl) ⟨108114, by rfl⟩) R216229
theorem R452429 : Reach 452429 := rs (se 3 (by rfl) ⟨84830, by rfl⟩) R169661
theorem R190289 : Reach 190289 := rs (se 2 (by rfl) ⟨71358, by rfl⟩) R142717
theorem R321421 : Reach 321421 := rs (se 3 (by rfl) ⟨60266, by rfl⟩) R120533
theorem R256013 : Reach 256013 := rs (se 3 (by rfl) ⟨48002, by rfl⟩) R96005
theorem R124993 : Reach 124993 := rs (se 2 (by rfl) ⟨46872, by rfl⟩) R93745
theorem R256067 : Reach 256067 := rs (se 1 (by rfl) ⟨192050, by rfl⟩) R384101
theorem R387341 : Reach 387341 := rs (se 3 (by rfl) ⟨72626, by rfl⟩) R145253
theorem R256337 : Reach 256337 := rs (se 2 (by rfl) ⟨96126, by rfl⟩) R192253
theorem R92515 : Reach 92515 := rs (se 1 (by rfl) ⟨69386, by rfl⟩) R138773
theorem R7301573 : Reach 7301573 := rs (se 4 (by rfl) ⟨684522, by rfl⟩) R1369045
theorem R92659 : Reach 92659 := rs (se 1 (by rfl) ⟨69494, by rfl⟩) R138989
theorem R223793 : Reach 223793 := rs (se 2 (by rfl) ⟨83922, by rfl⟩) R167845
theorem R879173 : Reach 879173 := rs (se 4 (by rfl) ⟨82422, by rfl⟩) R164845
theorem R387683 : Reach 387683 := rs (se 1 (by rfl) ⟨290762, by rfl⟩) R581525
theorem R289379 : Reach 289379 := rs (se 1 (by rfl) ⟨217034, by rfl⟩) R434069
theorem R453347 : Reach 453347 := rs (se 1 (by rfl) ⟨340010, by rfl⟩) R680021
theorem R223985 : Reach 223985 := rs (se 2 (by rfl) ⟨83994, by rfl⟩) R167989
theorem R92963 : Reach 92963 := rs (se 1 (by rfl) ⟨69722, by rfl⟩) R139445
theorem R191281 : Reach 191281 := rs (se 2 (by rfl) ⟨71730, by rfl⟩) R143461
theorem R256877 : Reach 256877 := rs (se 3 (by rfl) ⟨48164, by rfl⟩) R96329
theorem R256931 : Reach 256931 := rs (se 1 (by rfl) ⟨192698, by rfl⟩) R385397
theorem R322481 : Reach 322481 := rs (se 2 (by rfl) ⟨120930, by rfl⟩) R241861
theorem R420785 : Reach 420785 := rs (se 2 (by rfl) ⟨157794, by rfl⟩) R315589
theorem R289763 : Reach 289763 := rs (se 1 (by rfl) ⟨217322, by rfl⟩) R434645
theorem R289777 : Reach 289777 := rs (se 2 (by rfl) ⟨108666, by rfl⟩) R217333
theorem R191555 : Reach 191555 := rs (se 1 (by rfl) ⟨143666, by rfl⟩) R287333
theorem R257201 : Reach 257201 := rs (se 2 (by rfl) ⟨96450, by rfl⟩) R192901
theorem R1109189 : Reach 1109189 := rs (se 4 (by rfl) ⟨103986, by rfl⟩) R207973
theorem R191747 : Reach 191747 := rs (se 1 (by rfl) ⟨143810, by rfl⟩) R287621
theorem R617827 : Reach 617827 := rs (se 1 (by rfl) ⟨463370, by rfl⟩) R926741
theorem R126659 : Reach 126659 := rs (se 1 (by rfl) ⟨94994, by rfl⟩) R189989
theorem R257741 : Reach 257741 := rs (se 3 (by rfl) ⟨48326, by rfl⟩) R96653
theorem R224977 : Reach 224977 := rs (se 2 (by rfl) ⟨84366, by rfl⟩) R168733
theorem R257795 : Reach 257795 := rs (se 1 (by rfl) ⟨193346, by rfl⟩) R386693
theorem R126785 : Reach 126785 := rs (se 2 (by rfl) ⟨47544, by rfl⟩) R95089
theorem R126913 : Reach 126913 := rs (se 2 (by rfl) ⟨47592, by rfl⟩) R95185
theorem R126947 : Reach 126947 := rs (se 1 (by rfl) ⟨95210, by rfl⟩) R190421
theorem R225251 : Reach 225251 := rs (se 1 (by rfl) ⟨168938, by rfl⟩) R337877
theorem R258065 : Reach 258065 := rs (se 2 (by rfl) ⟨96774, by rfl⟩) R193549
theorem R127075 : Reach 127075 := rs (se 1 (by rfl) ⟨95306, by rfl⟩) R190613
theorem R487565 : Reach 487565 := rs (se 3 (by rfl) ⟨91418, by rfl⟩) R182837
theorem R192689 : Reach 192689 := rs (se 2 (by rfl) ⟨72258, by rfl⟩) R144517
theorem R192739 : Reach 192739 := rs (se 1 (by rfl) ⟨144554, by rfl⟩) R289109
theorem R127217 : Reach 127217 := rs (se 2 (by rfl) ⟨47706, by rfl⟩) R95413
theorem R94451 : Reach 94451 := rs (se 1 (by rfl) ⟨70838, by rfl⟩) R141677
theorem R127345 : Reach 127345 := rs (se 2 (by rfl) ⟨47754, by rfl⟩) R95509
theorem R192881 : Reach 192881 := rs (se 2 (by rfl) ⟨72330, by rfl⟩) R144661
theorem R815501 : Reach 815501 := rs (se 3 (by rfl) ⟨152906, by rfl⟩) R305813
theorem R127379 : Reach 127379 := rs (se 1 (by rfl) ⟨95534, by rfl⟩) R191069
theorem R291235 : Reach 291235 := rs (se 1 (by rfl) ⟨218426, by rfl⟩) R436853
theorem R848369 : Reach 848369 := rs (se 2 (by rfl) ⟨318138, by rfl⟩) R636277
theorem R127507 : Reach 127507 := rs (se 1 (by rfl) ⟨95630, by rfl⟩) R191261
theorem R258605 : Reach 258605 := rs (se 3 (by rfl) ⟨48488, by rfl⟩) R96977
theorem R258659 : Reach 258659 := rs (se 1 (by rfl) ⟨193994, by rfl⟩) R387989
theorem R127649 : Reach 127649 := rs (se 2 (by rfl) ⟨47868, by rfl⟩) R95737
theorem R127777 : Reach 127777 := rs (se 2 (by rfl) ⟨47916, by rfl⟩) R95833
theorem R127811 : Reach 127811 := rs (se 1 (by rfl) ⟨95858, by rfl⟩) R191717
theorem R258929 : Reach 258929 := rs (se 2 (by rfl) ⟨97098, by rfl⟩) R194197
theorem R160643 : Reach 160643 := rs (se 1 (by rfl) ⟨120482, by rfl⟩) R240965
theorem R127939 : Reach 127939 := rs (se 1 (by rfl) ⟨95954, by rfl⟩) R191909
theorem R95251 : Reach 95251 := rs (se 1 (by rfl) ⟨71438, by rfl⟩) R142877
theorem R128081 : Reach 128081 := rs (se 2 (by rfl) ⟨48030, by rfl⟩) R96061
theorem R390257 : Reach 390257 := rs (se 2 (by rfl) ⟨146346, by rfl⟩) R292693
theorem R95347 : Reach 95347 := rs (se 1 (by rfl) ⟨71510, by rfl⟩) R143021
theorem R128209 : Reach 128209 := rs (se 2 (by rfl) ⟨48078, by rfl⟩) R96157
theorem R128243 : Reach 128243 := rs (se 1 (by rfl) ⟨96182, by rfl⟩) R192365
theorem R193873 : Reach 193873 := rs (se 2 (by rfl) ⟨72702, by rfl⟩) R145405
theorem R750961 : Reach 750961 := rs (se 2 (by rfl) ⟨281610, by rfl⟩) R563221
theorem R128371 : Reach 128371 := rs (se 1 (by rfl) ⟨96278, by rfl⟩) R192557
theorem R259469 : Reach 259469 := rs (se 3 (by rfl) ⟨48650, by rfl⟩) R97301
theorem R259523 : Reach 259523 := rs (se 1 (by rfl) ⟨194642, by rfl⟩) R389285
theorem R128483 : Reach 128483 := rs (se 1 (by rfl) ⟨96362, by rfl⟩) R192725
theorem R128513 : Reach 128513 := rs (se 2 (by rfl) ⟨48192, by rfl⟩) R96385
theorem R95843 : Reach 95843 := rs (se 1 (by rfl) ⟨71882, by rfl⟩) R143765
theorem R194147 : Reach 194147 := rs (se 1 (by rfl) ⟨145610, by rfl⟩) R291221
theorem R128641 : Reach 128641 := rs (se 2 (by rfl) ⟨48240, by rfl⟩) R96481
theorem R128675 : Reach 128675 := rs (se 1 (by rfl) ⟨96506, by rfl⟩) R193013
theorem R161489 : Reach 161489 := rs (se 2 (by rfl) ⟨60558, by rfl⟩) R121117
theorem R259793 : Reach 259793 := rs (se 2 (by rfl) ⟨97422, by rfl⟩) R194845
theorem R128803 : Reach 128803 := rs (se 1 (by rfl) ⟨96602, by rfl⟩) R193205
theorem R194339 : Reach 194339 := rs (se 1 (by rfl) ⟨145754, by rfl⟩) R291509
theorem R325453 : Reach 325453 := rs (se 3 (by rfl) ⟨61022, by rfl⟩) R122045
theorem R259949 : Reach 259949 := rs (se 3 (by rfl) ⟨48740, by rfl⟩) R97481
theorem R718733 : Reach 718733 := rs (se 3 (by rfl) ⟨134762, by rfl⟩) R269525
theorem R128945 : Reach 128945 := rs (se 2 (by rfl) ⟨48354, by rfl⟩) R96709
theorem R129073 : Reach 129073 := rs (se 2 (by rfl) ⟨48402, by rfl⟩) R96805
theorem R129107 : Reach 129107 := rs (se 1 (by rfl) ⟨96830, by rfl⟩) R193661
theorem R325795 : Reach 325795 := rs (se 1 (by rfl) ⟨244346, by rfl⟩) R488693
theorem R129235 : Reach 129235 := rs (se 1 (by rfl) ⟨96926, by rfl⟩) R193853
theorem R260333 : Reach 260333 := rs (se 3 (by rfl) ⟨48812, by rfl⟩) R97625
theorem R981233 : Reach 981233 := rs (se 2 (by rfl) ⟨367962, by rfl⟩) R735925
theorem R96547 : Reach 96547 := rs (se 1 (by rfl) ⟨72410, by rfl⟩) R144821
theorem R260387 : Reach 260387 := rs (se 1 (by rfl) ⟨195290, by rfl⟩) R390581
theorem R489797 : Reach 489797 := rs (se 4 (by rfl) ⟨45918, by rfl⟩) R91837
theorem R129377 : Reach 129377 := rs (se 2 (by rfl) ⟨48516, by rfl⟩) R97033
theorem R96643 : Reach 96643 := rs (se 1 (by rfl) ⟨72482, by rfl⟩) R144965
theorem R129505 : Reach 129505 := rs (se 2 (by rfl) ⟨48564, by rfl⟩) R97129
theorem R129539 : Reach 129539 := rs (se 1 (by rfl) ⟨97154, by rfl⟩) R194309
theorem R391715 : Reach 391715 := rs (se 1 (by rfl) ⟨293786, by rfl⟩) R587573
theorem R260657 : Reach 260657 := rs (se 2 (by rfl) ⟨97746, by rfl⟩) R195493
theorem R293453 : Reach 293453 := rs (se 3 (by rfl) ⟨55022, by rfl⟩) R110045
theorem R293489 : Reach 293489 := rs (se 2 (by rfl) ⟨110058, by rfl⟩) R220117
theorem R129667 : Reach 129667 := rs (se 1 (by rfl) ⟨97250, by rfl⟩) R194501
theorem R359075 : Reach 359075 := rs (se 1 (by rfl) ⟨269306, by rfl⟩) R538613
theorem R195281 : Reach 195281 := rs (se 2 (by rfl) ⟨73230, by rfl⟩) R146461
theorem R195331 : Reach 195331 := rs (se 1 (by rfl) ⟨146498, by rfl⟩) R292997
theorem R129809 : Reach 129809 := rs (se 2 (by rfl) ⟨48678, by rfl⟩) R97357
theorem R97139 : Reach 97139 := rs (se 1 (by rfl) ⟨72854, by rfl⟩) R145709
theorem R129937 : Reach 129937 := rs (se 2 (by rfl) ⟨48726, by rfl⟩) R97453
theorem R195473 : Reach 195473 := rs (se 2 (by rfl) ⟨73302, by rfl⟩) R146605
theorem R129971 : Reach 129971 := rs (se 1 (by rfl) ⟨97478, by rfl⟩) R194957
theorem R621553 : Reach 621553 := rs (se 2 (by rfl) ⟨233082, by rfl⟩) R466165
theorem R130099 : Reach 130099 := rs (se 1 (by rfl) ⟨97574, by rfl⟩) R195149
theorem R261197 : Reach 261197 := rs (se 3 (by rfl) ⟨48974, by rfl⟩) R97949
theorem R261251 : Reach 261251 := rs (se 1 (by rfl) ⟨195938, by rfl⟩) R391877
theorem R130241 : Reach 130241 := rs (se 2 (by rfl) ⟨48840, by rfl⟩) R97681
theorem R130369 : Reach 130369 := rs (se 2 (by rfl) ⟨48888, by rfl⟩) R97777
theorem R392525 : Reach 392525 := rs (se 3 (by rfl) ⟨73598, by rfl⟩) R147197
theorem R163171 : Reach 163171 := rs (se 1 (by rfl) ⟨122378, by rfl⟩) R244757
theorem R130403 : Reach 130403 := rs (se 1 (by rfl) ⟨97802, by rfl⟩) R195605
theorem R163217 : Reach 163217 := rs (se 2 (by rfl) ⟨61206, by rfl⟩) R122413
theorem R261521 : Reach 261521 := rs (se 2 (by rfl) ⟨98070, by rfl⟩) R196141
theorem R130531 : Reach 130531 := rs (se 1 (by rfl) ⟨97898, by rfl⟩) R195797
theorem R97843 : Reach 97843 := rs (se 1 (by rfl) ⟨73382, by rfl⟩) R146765
theorem R130673 : Reach 130673 := rs (se 2 (by rfl) ⟨49002, by rfl⟩) R98005
theorem R97939 : Reach 97939 := rs (se 1 (by rfl) ⟨73454, by rfl⟩) R146909
theorem R196337 : Reach 196337 := rs (se 2 (by rfl) ⟨73626, by rfl⟩) R147253
theorem R130801 : Reach 130801 := rs (se 2 (by rfl) ⟨49050, by rfl⟩) R98101
theorem R130835 : Reach 130835 := rs (se 1 (by rfl) ⟨98126, by rfl⟩) R196253
theorem R163633 : Reach 163633 := rs (se 2 (by rfl) ⟨61362, by rfl⟩) R122725
theorem R196465 : Reach 196465 := rs (se 2 (by rfl) ⟨73674, by rfl⟩) R147349
theorem R130963 : Reach 130963 := rs (se 1 (by rfl) ⟨98222, by rfl⟩) R196445
theorem R262061 : Reach 262061 := rs (se 3 (by rfl) ⟨49136, by rfl⟩) R98273
theorem R131041 : Reach 131041 := rs (se 2 (by rfl) ⟨49140, by rfl⟩) R98281
theorem R262115 : Reach 262115 := rs (se 1 (by rfl) ⟨196586, by rfl⟩) R393173
theorem R131159 : Reach 131159 := rs (se 1 (by rfl) ⟨98369, by rfl⟩) R196739
theorem R163991 : Reach 163991 := rs (se 1 (by rfl) ⟨122993, by rfl⟩) R245987
theorem R590003 : Reach 590003 := rs (se 1 (by rfl) ⟨442502, by rfl⟩) R885005
theorem R131287 : Reach 131287 := rs (se 1 (by rfl) ⟨98465, by rfl⟩) R196931
theorem R262493 : Reach 262493 := rs (se 3 (by rfl) ⟨49217, by rfl⟩) R98435
theorem R197081 : Reach 197081 := rs (se 2 (by rfl) ⟨73905, by rfl⟩) R147811
theorem R295427 : Reach 295427 := rs (se 1 (by rfl) ⟨221570, by rfl⟩) R443141
theorem R393821 : Reach 393821 := rs (se 3 (by rfl) ⟨73841, by rfl⟩) R147683
theorem R131801 : Reach 131801 := rs (se 2 (by rfl) ⟨49425, by rfl⟩) R98851
theorem R99083 : Reach 99083 := rs (se 1 (by rfl) ⟨74312, by rfl⟩) R148625
theorem R131915 : Reach 131915 := rs (se 1 (by rfl) ⟨98936, by rfl⟩) R197873
theorem R623537 : Reach 623537 := rs (se 2 (by rfl) ⟨233826, by rfl⟩) R467653
theorem R295883 : Reach 295883 := rs (se 1 (by rfl) ⟨221912, by rfl⟩) R443825
theorem R197579 : Reach 197579 := rs (se 1 (by rfl) ⟨148184, by rfl⟩) R296369
theorem R132043 : Reach 132043 := rs (se 1 (by rfl) ⟨99032, by rfl⟩) R198065
theorem R328769 : Reach 328769 := rs (se 2 (by rfl) ⟨123288, by rfl⟩) R246577
theorem R132185 : Reach 132185 := rs (se 2 (by rfl) ⟨49569, by rfl⟩) R99139
theorem R296081 : Reach 296081 := rs (se 2 (by rfl) ⟨111030, by rfl⟩) R222061
theorem R165017 : Reach 165017 := rs (se 2 (by rfl) ⟨61881, by rfl⟩) R123763
theorem R132313 : Reach 132313 := rs (se 2 (by rfl) ⟨49617, by rfl⟩) R99235
theorem R263627 : Reach 263627 := rs (se 1 (by rfl) ⟨197720, by rfl⟩) R395441
theorem R99787 : Reach 99787 := rs (se 1 (by rfl) ⟨74840, by rfl⟩) R149681
theorem R591461 : Reach 591461 := rs (se 4 (by rfl) ⟨55449, by rfl⟩) R110899
theorem R100055 : Reach 100055 := rs (se 1 (by rfl) ⟨75041, by rfl⟩) R150083
theorem R263897 : Reach 263897 := rs (se 2 (by rfl) ⟨98961, by rfl⟩) R197923
theorem R132887 : Reach 132887 := rs (se 1 (by rfl) ⟨99665, by rfl⟩) R199331
theorem R296855 : Reach 296855 := rs (se 1 (by rfl) ⟨222641, by rfl⟩) R445283
theorem R198551 : Reach 198551 := rs (se 1 (by rfl) ⟨148913, by rfl⟩) R297827
theorem R133015 : Reach 133015 := rs (se 1 (by rfl) ⟨99761, by rfl⟩) R199523
theorem R591947 : Reach 591947 := rs (se 1 (by rfl) ⟨443960, by rfl⟩) R887921
theorem R297053 : Reach 297053 := rs (se 3 (by rfl) ⟨55697, by rfl⟩) R111395
theorem R919873 : Reach 919873 := rs (se 2 (by rfl) ⟨344952, by rfl⟩) R689905
theorem R5048689 : Reach 5048689 := rs (se 2 (by rfl) ⟨1893258, by rfl⟩) R3786517
theorem R3869045 : Reach 3869045 := rs (se 5 (by rfl) ⟨181361, by rfl⟩) R362723
theorem R264599 : Reach 264599 := rs (se 1 (by rfl) ⟨198449, by rfl⟩) R396899
theorem R133643 : Reach 133643 := rs (se 1 (by rfl) ⟨100232, by rfl⟩) R200465
theorem R428561 : Reach 428561 := rs (se 2 (by rfl) ⟨160710, by rfl⟩) R321421
theorem R199219 : Reach 199219 := rs (se 1 (by rfl) ⟨149414, by rfl⟩) R298829
theorem R395927 : Reach 395927 := rs (se 1 (by rfl) ⟨296945, by rfl⟩) R593891
theorem R199361 : Reach 199361 := rs (se 2 (by rfl) ⟨74760, by rfl⟩) R149521
theorem R330443 : Reach 330443 := rs (se 1 (by rfl) ⟨247832, by rfl⟩) R495665
theorem R166657 : Reach 166657 := rs (se 2 (by rfl) ⟨62496, by rfl⟩) R124993
theorem R265139 : Reach 265139 := rs (se 1 (by rfl) ⟨198854, by rfl⟩) R397709
theorem R265409 : Reach 265409 := rs (se 2 (by rfl) ⟨99528, by rfl⟩) R199057
theorem R167255 : Reach 167255 := rs (se 1 (by rfl) ⟨125441, by rfl⟩) R250883
theorem R495065 : Reach 495065 := rs (se 2 (by rfl) ⟨185649, by rfl⟩) R371299
theorem R331229 : Reach 331229 := rs (se 3 (by rfl) ⟨62105, by rfl⟩) R124211
theorem R265949 : Reach 265949 := rs (se 3 (by rfl) ⟨49865, by rfl⟩) R99731
theorem R135091 : Reach 135091 := rs (se 1 (by rfl) ⟨101318, by rfl⟩) R202637
theorem R299011 : Reach 299011 := rs (se 1 (by rfl) ⟨224258, by rfl⟩) R448517
theorem R135179 : Reach 135179 := rs (se 1 (by rfl) ⟨101384, by rfl⟩) R202769
theorem R364637 : Reach 364637 := rs (se 3 (by rfl) ⟨68369, by rfl⟩) R136739
theorem R364675 : Reach 364675 := rs (se 1 (by rfl) ⟨273506, by rfl⟩) R547013
theorem R299315 : Reach 299315 := rs (se 1 (by rfl) ⟨224486, by rfl⟩) R448973
theorem R168331 : Reach 168331 := rs (se 1 (by rfl) ⟨126248, by rfl⟩) R252497
theorem R823769 : Reach 823769 := rs (se 2 (by rfl) ⟨308913, by rfl⟩) R617827
theorem R889379 : Reach 889379 := rs (se 1 (by rfl) ⟨667034, by rfl⟩) R1334069
theorem R332561 : Reach 332561 := rs (se 2 (by rfl) ⟨124710, by rfl⟩) R249421
theorem R2495285 : Reach 2495285 := rs (se 5 (by rfl) ⟨116966, by rfl⟩) R233933
theorem R299969 : Reach 299969 := rs (se 2 (by rfl) ⟨112488, by rfl⟩) R224977
theorem R693197 : Reach 693197 := rs (se 3 (by rfl) ⟨129974, by rfl⟩) R259949
theorem R103447 : Reach 103447 := rs (se 1 (by rfl) ⟨77585, by rfl⟩) R155171
theorem R463973 : Reach 463973 := rs (se 4 (by rfl) ⟨43497, by rfl⟩) R86995
theorem R169163 : Reach 169163 := rs (se 1 (by rfl) ⟨126872, by rfl⟩) R253745
theorem R169217 : Reach 169217 := rs (se 2 (by rfl) ⟨63456, by rfl⟩) R126913
theorem R791909 : Reach 791909 := rs (se 4 (by rfl) ⟨74241, by rfl⟩) R148483
theorem R169433 : Reach 169433 := rs (se 2 (by rfl) ⟨63537, by rfl⟩) R127075
theorem R169523 : Reach 169523 := rs (se 1 (by rfl) ⟨127142, by rfl⟩) R254285
theorem R169559 : Reach 169559 := rs (se 1 (by rfl) ⟨127169, by rfl⟩) R254339
theorem R1316533 : Reach 1316533 := rs (se 5 (by rfl) ⟨61712, by rfl⟩) R123425
theorem R169739 : Reach 169739 := rs (se 1 (by rfl) ⟨127304, by rfl⟩) R254609
theorem R169793 : Reach 169793 := rs (se 2 (by rfl) ⟨63672, by rfl⟩) R127345
theorem R333827 : Reach 333827 := rs (se 1 (by rfl) ⟨250370, by rfl⟩) R500741
theorem R170009 : Reach 170009 := rs (se 2 (by rfl) ⟨63753, by rfl⟩) R127507
theorem R170099 : Reach 170099 := rs (se 1 (by rfl) ⟨127574, by rfl⟩) R255149
theorem R399491 : Reach 399491 := rs (se 1 (by rfl) ⟨299618, by rfl⟩) R599237
theorem R170135 : Reach 170135 := rs (se 1 (by rfl) ⟨127601, by rfl⟩) R255203
theorem R170315 : Reach 170315 := rs (se 1 (by rfl) ⟨127736, by rfl⟩) R255473
theorem R170369 : Reach 170369 := rs (se 2 (by rfl) ⟨63888, by rfl⟩) R127777
theorem R301619 : Reach 301619 := rs (se 1 (by rfl) ⟨226214, by rfl⟩) R452429
theorem R170585 : Reach 170585 := rs (se 2 (by rfl) ⟨63969, by rfl⟩) R127939
theorem R203357 : Reach 203357 := rs (se 3 (by rfl) ⟨38129, by rfl⟩) R76259
theorem R170675 : Reach 170675 := rs (se 1 (by rfl) ⟨128006, by rfl⟩) R256013
theorem R170711 : Reach 170711 := rs (se 1 (by rfl) ⟨128033, by rfl⟩) R256067
theorem R170891 : Reach 170891 := rs (se 1 (by rfl) ⟨128168, by rfl⟩) R256337
theorem R170945 : Reach 170945 := rs (se 2 (by rfl) ⟨64104, by rfl⟩) R128209
theorem R629765 : Reach 629765 := rs (se 4 (by rfl) ⟨59040, by rfl⟩) R118081
theorem R302231 : Reach 302231 := rs (se 1 (by rfl) ⟨226673, by rfl⟩) R453347
theorem R171161 : Reach 171161 := rs (se 2 (by rfl) ⟨64185, by rfl⟩) R128371
theorem R171251 : Reach 171251 := rs (se 1 (by rfl) ⟨128438, by rfl⟩) R256877
theorem R400657 : Reach 400657 := rs (se 2 (by rfl) ⟨150246, by rfl⟩) R300493
theorem R171287 : Reach 171287 := rs (se 1 (by rfl) ⟨128465, by rfl⟩) R256931
theorem R597293 : Reach 597293 := rs (se 3 (by rfl) ⟨111992, by rfl⟩) R223985
theorem R171467 : Reach 171467 := rs (se 1 (by rfl) ⟨128600, by rfl⟩) R257201
theorem R171521 : Reach 171521 := rs (se 2 (by rfl) ⟨64320, by rfl⟩) R128641
theorem R204439 : Reach 204439 := rs (se 1 (by rfl) ⟨153329, by rfl⟩) R306659
theorem R204481 : Reach 204481 := rs (se 2 (by rfl) ⟨76680, by rfl⟩) R153361
theorem R171737 : Reach 171737 := rs (se 2 (by rfl) ⟨64401, by rfl⟩) R128803
theorem R433937 : Reach 433937 := rs (se 2 (by rfl) ⟨162726, by rfl⟩) R325453
theorem R171827 : Reach 171827 := rs (se 1 (by rfl) ⟨128870, by rfl⟩) R257741
theorem R171863 : Reach 171863 := rs (se 1 (by rfl) ⟨128897, by rfl⟩) R257795
theorem R172043 : Reach 172043 := rs (se 1 (by rfl) ⟨129032, by rfl⟩) R258065
theorem R172097 : Reach 172097 := rs (se 2 (by rfl) ⟨64536, by rfl⟩) R129073
theorem R434393 : Reach 434393 := rs (se 2 (by rfl) ⟨162897, by rfl⟩) R325795
theorem R172313 : Reach 172313 := rs (se 2 (by rfl) ⟨64617, by rfl⟩) R129235
theorem R565579 : Reach 565579 := rs (se 1 (by rfl) ⟨424184, by rfl⟩) R848369
theorem R598373 : Reach 598373 := rs (se 4 (by rfl) ⟨56097, by rfl⟩) R112195
theorem R172403 : Reach 172403 := rs (se 1 (by rfl) ⟨129302, by rfl⟩) R258605
theorem R172439 : Reach 172439 := rs (se 1 (by rfl) ⟨129329, by rfl⟩) R258659
theorem R205259 : Reach 205259 := rs (se 1 (by rfl) ⟨153944, by rfl⟩) R307889
theorem R172619 : Reach 172619 := rs (se 1 (by rfl) ⟨129464, by rfl⟩) R258929
theorem R107095 : Reach 107095 := rs (se 1 (by rfl) ⟨80321, by rfl⟩) R160643
theorem R172673 : Reach 172673 := rs (se 2 (by rfl) ⟨64752, by rfl⟩) R129505
theorem R172889 : Reach 172889 := rs (se 2 (by rfl) ⟨64833, by rfl⟩) R129667
theorem R172979 : Reach 172979 := rs (se 1 (by rfl) ⟨129734, by rfl⟩) R259469
theorem R173015 : Reach 173015 := rs (se 1 (by rfl) ⟨129761, by rfl⟩) R259523
theorem R336919 : Reach 336919 := rs (se 1 (by rfl) ⟨252689, by rfl⟩) R505379
theorem R107659 : Reach 107659 := rs (se 1 (by rfl) ⟨80744, by rfl⟩) R161489
theorem R173195 : Reach 173195 := rs (se 1 (by rfl) ⟨129896, by rfl⟩) R259793
theorem R173249 : Reach 173249 := rs (se 2 (by rfl) ⟨64968, by rfl⟩) R129937
theorem R140545 : Reach 140545 := rs (se 2 (by rfl) ⟨52704, by rfl⟩) R105409
theorem R271633 : Reach 271633 := rs (se 2 (by rfl) ⟨101862, by rfl⟩) R203725
theorem R337175 : Reach 337175 := rs (se 1 (by rfl) ⟨252881, by rfl⟩) R505763
theorem R828737 : Reach 828737 := rs (se 2 (by rfl) ⟨310776, by rfl⟩) R621553
theorem R75127 : Reach 75127 := rs (se 1 (by rfl) ⟨56345, by rfl⟩) R112691
theorem R75147 : Reach 75147 := rs (se 1 (by rfl) ⟨56360, by rfl⟩) R112721
theorem R75159 : Reach 75159 := rs (se 1 (by rfl) ⟨56369, by rfl⟩) R112739
theorem R173465 : Reach 173465 := rs (se 2 (by rfl) ⟨65049, by rfl⟩) R130099
theorem R75179 : Reach 75179 := rs (se 1 (by rfl) ⟨56384, by rfl⟩) R112769
theorem R75191 : Reach 75191 := rs (se 1 (by rfl) ⟨56393, by rfl⟩) R112787
theorem R75211 : Reach 75211 := rs (se 1 (by rfl) ⟨56408, by rfl⟩) R112817
theorem R4793813 : Reach 4793813 := rs (se 7 (by rfl) ⟨56177, by rfl⟩) R112355
theorem R75223 : Reach 75223 := rs (se 1 (by rfl) ⟨56417, by rfl⟩) R112835
theorem R75243 : Reach 75243 := rs (se 1 (by rfl) ⟨56432, by rfl⟩) R112865
theorem R173555 : Reach 173555 := rs (se 1 (by rfl) ⟨130166, by rfl⟩) R260333
theorem R75255 : Reach 75255 := rs (se 1 (by rfl) ⟨56441, by rfl⟩) R112883
theorem R75275 : Reach 75275 := rs (se 1 (by rfl) ⟨56456, by rfl⟩) R112913
theorem R75287 : Reach 75287 := rs (se 1 (by rfl) ⟨56465, by rfl⟩) R112931
theorem R173591 : Reach 173591 := rs (se 1 (by rfl) ⟨130193, by rfl⟩) R260387
theorem R75307 : Reach 75307 := rs (se 1 (by rfl) ⟨56480, by rfl⟩) R112961
theorem R75319 : Reach 75319 := rs (se 1 (by rfl) ⟨56489, by rfl⟩) R112979
theorem R75339 : Reach 75339 := rs (se 1 (by rfl) ⟨56504, by rfl⟩) R113009
theorem R75351 : Reach 75351 := rs (se 1 (by rfl) ⟨56513, by rfl⟩) R113027
theorem R75371 : Reach 75371 := rs (se 1 (by rfl) ⟨56528, by rfl⟩) R113057
theorem R75383 : Reach 75383 := rs (se 1 (by rfl) ⟨56537, by rfl⟩) R113075
theorem R75403 : Reach 75403 := rs (se 1 (by rfl) ⟨56552, by rfl⟩) R113105
theorem R75415 : Reach 75415 := rs (se 1 (by rfl) ⟨56561, by rfl⟩) R113123
theorem R75435 : Reach 75435 := rs (se 1 (by rfl) ⟨56576, by rfl⟩) R113153
theorem R75447 : Reach 75447 := rs (se 1 (by rfl) ⟨56585, by rfl⟩) R113171
theorem R75467 : Reach 75467 := rs (se 1 (by rfl) ⟨56600, by rfl⟩) R113201
theorem R173771 : Reach 173771 := rs (se 1 (by rfl) ⟨130328, by rfl⟩) R260657
theorem R75479 : Reach 75479 := rs (se 1 (by rfl) ⟨56609, by rfl⟩) R113219
theorem R75499 : Reach 75499 := rs (se 1 (by rfl) ⟨56624, by rfl⟩) R113249
theorem R75511 : Reach 75511 := rs (se 1 (by rfl) ⟨56633, by rfl⟩) R113267
theorem R173825 : Reach 173825 := rs (se 2 (by rfl) ⟨65184, by rfl⟩) R130369
theorem R75531 : Reach 75531 := rs (se 1 (by rfl) ⟨56648, by rfl⟩) R113297
theorem R75543 : Reach 75543 := rs (se 1 (by rfl) ⟨56657, by rfl⟩) R113315
theorem R239383 : Reach 239383 := rs (se 1 (by rfl) ⟨179537, by rfl⟩) R359075
theorem R75563 : Reach 75563 := rs (se 1 (by rfl) ⟨56672, by rfl⟩) R113345
theorem R272179 : Reach 272179 := rs (se 1 (by rfl) ⟨204134, by rfl⟩) R408269
theorem R141107 : Reach 141107 := rs (se 1 (by rfl) ⟨105830, by rfl⟩) R211661
theorem R75575 : Reach 75575 := rs (se 1 (by rfl) ⟨56681, by rfl⟩) R113363
theorem R75595 : Reach 75595 := rs (se 1 (by rfl) ⟨56696, by rfl⟩) R113393
theorem R75607 : Reach 75607 := rs (se 1 (by rfl) ⟨56705, by rfl⟩) R113411
theorem R75627 : Reach 75627 := rs (se 1 (by rfl) ⟨56720, by rfl⟩) R113441
theorem R75639 : Reach 75639 := rs (se 1 (by rfl) ⟨56729, by rfl⟩) R113459
theorem R75659 : Reach 75659 := rs (se 1 (by rfl) ⟨56744, by rfl⟩) R113489
theorem R75671 : Reach 75671 := rs (se 1 (by rfl) ⟨56753, by rfl⟩) R113507
theorem R75691 : Reach 75691 := rs (se 1 (by rfl) ⟨56768, by rfl⟩) R113537
theorem R75703 : Reach 75703 := rs (se 1 (by rfl) ⟨56777, by rfl⟩) R113555
theorem R75723 : Reach 75723 := rs (se 1 (by rfl) ⟨56792, by rfl⟩) R113585
theorem R75735 : Reach 75735 := rs (se 1 (by rfl) ⟨56801, by rfl⟩) R113603
theorem R174041 : Reach 174041 := rs (se 2 (by rfl) ⟨65265, by rfl⟩) R130531
theorem R75755 : Reach 75755 := rs (se 1 (by rfl) ⟨56816, by rfl⟩) R113633
theorem R75767 : Reach 75767 := rs (se 1 (by rfl) ⟨56825, by rfl⟩) R113651
theorem R75787 : Reach 75787 := rs (se 1 (by rfl) ⟨56840, by rfl⟩) R113681
theorem R75799 : Reach 75799 := rs (se 1 (by rfl) ⟨56849, by rfl⟩) R113699
theorem R75819 : Reach 75819 := rs (se 1 (by rfl) ⟨56864, by rfl⟩) R113729
theorem R174131 : Reach 174131 := rs (se 1 (by rfl) ⟨130598, by rfl⟩) R261197
theorem R75831 : Reach 75831 := rs (se 1 (by rfl) ⟨56873, by rfl⟩) R113747
theorem R75851 : Reach 75851 := rs (se 1 (by rfl) ⟨56888, by rfl⟩) R113777
theorem R75863 : Reach 75863 := rs (se 1 (by rfl) ⟨56897, by rfl⟩) R113795
theorem R174167 : Reach 174167 := rs (se 1 (by rfl) ⟨130625, by rfl⟩) R261251
theorem R75883 : Reach 75883 := rs (se 1 (by rfl) ⟨56912, by rfl⟩) R113825
theorem R75895 : Reach 75895 := rs (se 1 (by rfl) ⟨56921, by rfl⟩) R113843
theorem R75915 : Reach 75915 := rs (se 1 (by rfl) ⟨56936, by rfl⟩) R113873
theorem R75927 : Reach 75927 := rs (se 1 (by rfl) ⟨56945, by rfl⟩) R113891
theorem R75947 : Reach 75947 := rs (se 1 (by rfl) ⟨56960, by rfl⟩) R113921
theorem R75959 : Reach 75959 := rs (se 1 (by rfl) ⟨56969, by rfl⟩) R113939
theorem R75979 : Reach 75979 := rs (se 1 (by rfl) ⟨56984, by rfl⟩) R113969
theorem R75991 : Reach 75991 := rs (se 1 (by rfl) ⟨56993, by rfl⟩) R113987
theorem R76011 : Reach 76011 := rs (se 1 (by rfl) ⟨57008, by rfl⟩) R114017
theorem R76023 : Reach 76023 := rs (se 1 (by rfl) ⟨57017, by rfl⟩) R114035
theorem R108811 : Reach 108811 := rs (se 1 (by rfl) ⟨81608, by rfl⟩) R163217
theorem R76043 : Reach 76043 := rs (se 1 (by rfl) ⟨57032, by rfl⟩) R114065
theorem R174347 : Reach 174347 := rs (se 1 (by rfl) ⟨130760, by rfl⟩) R261521
theorem R76055 : Reach 76055 := rs (se 1 (by rfl) ⟨57041, by rfl⟩) R114083
theorem R76075 : Reach 76075 := rs (se 1 (by rfl) ⟨57056, by rfl⟩) R114113
theorem R76087 : Reach 76087 := rs (se 1 (by rfl) ⟨57065, by rfl⟩) R114131
theorem R174401 : Reach 174401 := rs (se 2 (by rfl) ⟨65400, by rfl⟩) R130801
theorem R76107 : Reach 76107 := rs (se 1 (by rfl) ⟨57080, by rfl⟩) R114161
theorem R76119 : Reach 76119 := rs (se 1 (by rfl) ⟨57089, by rfl⟩) R114179
theorem R76139 : Reach 76139 := rs (se 1 (by rfl) ⟨57104, by rfl⟩) R114209
theorem R76151 : Reach 76151 := rs (se 1 (by rfl) ⟨57113, by rfl⟩) R114227
theorem R76171 : Reach 76171 := rs (se 1 (by rfl) ⟨57128, by rfl⟩) R114257
theorem R76183 : Reach 76183 := rs (se 1 (by rfl) ⟨57137, by rfl⟩) R114275
theorem R76203 : Reach 76203 := rs (se 1 (by rfl) ⟨57152, by rfl⟩) R114305
theorem R76215 : Reach 76215 := rs (se 1 (by rfl) ⟨57161, by rfl⟩) R114323
theorem R76235 : Reach 76235 := rs (se 1 (by rfl) ⟨57176, by rfl⟩) R114353
theorem R76247 : Reach 76247 := rs (se 1 (by rfl) ⟨57185, by rfl⟩) R114371
theorem R240089 : Reach 240089 := rs (se 2 (by rfl) ⟨90033, by rfl⟩) R180067
theorem R76267 : Reach 76267 := rs (se 1 (by rfl) ⟨57200, by rfl⟩) R114401
theorem R76279 : Reach 76279 := rs (se 1 (by rfl) ⟨57209, by rfl⟩) R114419
theorem R76299 : Reach 76299 := rs (se 1 (by rfl) ⟨57224, by rfl⟩) R114449
theorem R76311 : Reach 76311 := rs (se 1 (by rfl) ⟨57233, by rfl⟩) R114467
theorem R174617 : Reach 174617 := rs (se 2 (by rfl) ⟨65481, by rfl⟩) R130963
theorem R76331 : Reach 76331 := rs (se 1 (by rfl) ⟨57248, by rfl⟩) R114497
theorem R76343 : Reach 76343 := rs (se 1 (by rfl) ⟨57257, by rfl⟩) R114515
theorem R76363 : Reach 76363 := rs (se 1 (by rfl) ⟨57272, by rfl⟩) R114545
theorem R76375 : Reach 76375 := rs (se 1 (by rfl) ⟨57281, by rfl⟩) R114563
theorem R109145 : Reach 109145 := rs (se 2 (by rfl) ⟨40929, by rfl⟩) R81859
theorem R76395 : Reach 76395 := rs (se 1 (by rfl) ⟨57296, by rfl⟩) R114593
theorem R174707 : Reach 174707 := rs (se 1 (by rfl) ⟨131030, by rfl⟩) R262061
theorem R76407 : Reach 76407 := rs (se 1 (by rfl) ⟨57305, by rfl⟩) R114611
theorem R174721 : Reach 174721 := rs (se 2 (by rfl) ⟨65520, by rfl⟩) R131041
theorem R76427 : Reach 76427 := rs (se 1 (by rfl) ⟨57320, by rfl⟩) R114641
theorem R76439 : Reach 76439 := rs (se 1 (by rfl) ⟨57329, by rfl⟩) R114659
theorem R174743 : Reach 174743 := rs (se 1 (by rfl) ⟨131057, by rfl⟩) R262115
theorem R76459 : Reach 76459 := rs (se 1 (by rfl) ⟨57344, by rfl⟩) R114689
theorem R76471 : Reach 76471 := rs (se 1 (by rfl) ⟨57353, by rfl⟩) R114707
theorem R76491 : Reach 76491 := rs (se 1 (by rfl) ⟨57368, by rfl⟩) R114737
theorem R76503 : Reach 76503 := rs (se 1 (by rfl) ⟨57377, by rfl⟩) R114755
theorem R76523 : Reach 76523 := rs (se 1 (by rfl) ⟨57392, by rfl⟩) R114785
theorem R76535 : Reach 76535 := rs (se 1 (by rfl) ⟨57401, by rfl⟩) R114803
theorem R76555 : Reach 76555 := rs (se 1 (by rfl) ⟨57416, by rfl⟩) R114833
theorem R76567 : Reach 76567 := rs (se 1 (by rfl) ⟨57425, by rfl⟩) R114851
theorem R76587 : Reach 76587 := rs (se 1 (by rfl) ⟨57440, by rfl⟩) R114881
theorem R76599 : Reach 76599 := rs (se 1 (by rfl) ⟨57449, by rfl⟩) R114899
theorem R76619 : Reach 76619 := rs (se 1 (by rfl) ⟨57464, by rfl⟩) R114929
theorem R666443 : Reach 666443 := rs (se 1 (by rfl) ⟨499832, by rfl⟩) R999665
theorem R174923 : Reach 174923 := rs (se 1 (by rfl) ⟨131192, by rfl⟩) R262385
theorem R76631 : Reach 76631 := rs (se 1 (by rfl) ⟨57473, by rfl⟩) R114947
theorem R76651 : Reach 76651 := rs (se 1 (by rfl) ⟨57488, by rfl⟩) R114977
theorem R76663 : Reach 76663 := rs (se 1 (by rfl) ⟨57497, by rfl⟩) R114995
theorem R174977 : Reach 174977 := rs (se 2 (by rfl) ⟨65616, by rfl⟩) R131233
theorem R76683 : Reach 76683 := rs (se 1 (by rfl) ⟨57512, by rfl⟩) R115025
theorem R76695 : Reach 76695 := rs (se 1 (by rfl) ⟨57521, by rfl⟩) R115043
theorem R76715 : Reach 76715 := rs (se 1 (by rfl) ⟨57536, by rfl⟩) R115073
theorem R76727 : Reach 76727 := rs (se 1 (by rfl) ⟨57545, by rfl⟩) R115091
theorem R76747 : Reach 76747 := rs (se 1 (by rfl) ⟨57560, by rfl⟩) R115121
theorem R76759 : Reach 76759 := rs (se 1 (by rfl) ⟨57569, by rfl⟩) R115139
theorem R994265 : Reach 994265 := rs (se 2 (by rfl) ⟨372849, by rfl⟩) R745699
theorem R76779 : Reach 76779 := rs (se 1 (by rfl) ⟨57584, by rfl⟩) R115169
theorem R76791 : Reach 76791 := rs (se 1 (by rfl) ⟨57593, by rfl⟩) R115187
theorem R76811 : Reach 76811 := rs (se 1 (by rfl) ⟨57608, by rfl⟩) R115217
theorem R76823 : Reach 76823 := rs (se 1 (by rfl) ⟨57617, by rfl⟩) R115235
theorem R142361 : Reach 142361 := rs (se 2 (by rfl) ⟨53385, by rfl⟩) R106771
theorem R76843 : Reach 76843 := rs (se 1 (by rfl) ⟨57632, by rfl⟩) R115265
theorem R76855 : Reach 76855 := rs (se 1 (by rfl) ⟨57641, by rfl⟩) R115283
theorem R76875 : Reach 76875 := rs (se 1 (by rfl) ⟨57656, by rfl⟩) R115313
theorem R76887 : Reach 76887 := rs (se 1 (by rfl) ⟨57665, by rfl⟩) R115331
theorem R175193 : Reach 175193 := rs (se 2 (by rfl) ⟨65697, by rfl⟩) R131395
theorem R76907 : Reach 76907 := rs (se 1 (by rfl) ⟨57680, by rfl⟩) R115361
theorem R76919 : Reach 76919 := rs (se 1 (by rfl) ⟨57689, by rfl⟩) R115379
theorem R273539 : Reach 273539 := rs (se 1 (by rfl) ⟨205154, by rfl⟩) R410309
theorem R76939 : Reach 76939 := rs (se 1 (by rfl) ⟨57704, by rfl⟩) R115409
theorem R76951 : Reach 76951 := rs (se 1 (by rfl) ⟨57713, by rfl⟩) R115427
theorem R76971 : Reach 76971 := rs (se 1 (by rfl) ⟨57728, by rfl⟩) R115457
theorem R175283 : Reach 175283 := rs (se 1 (by rfl) ⟨131462, by rfl⟩) R262925
theorem R76983 : Reach 76983 := rs (se 1 (by rfl) ⟨57737, by rfl⟩) R115475
theorem R77003 : Reach 77003 := rs (se 1 (by rfl) ⟨57752, by rfl⟩) R115505
theorem R77015 : Reach 77015 := rs (se 1 (by rfl) ⟨57761, by rfl⟩) R115523
theorem R109783 : Reach 109783 := rs (se 1 (by rfl) ⟨82337, by rfl⟩) R164675
theorem R175319 : Reach 175319 := rs (se 1 (by rfl) ⟨131489, by rfl⟩) R262979
theorem R77035 : Reach 77035 := rs (se 1 (by rfl) ⟨57776, by rfl⟩) R115553
theorem R77047 : Reach 77047 := rs (se 1 (by rfl) ⟨57785, by rfl⟩) R115571
theorem R77067 : Reach 77067 := rs (se 1 (by rfl) ⟨57800, by rfl⟩) R115601
theorem R77079 : Reach 77079 := rs (se 1 (by rfl) ⟨57809, by rfl⟩) R115619
theorem R77099 : Reach 77099 := rs (se 1 (by rfl) ⟨57824, by rfl⟩) R115649
theorem R273709 : Reach 273709 := rs (se 3 (by rfl) ⟨51320, by rfl⟩) R102641
theorem R77111 : Reach 77111 := rs (se 1 (by rfl) ⟨57833, by rfl⟩) R115667
theorem R77131 : Reach 77131 := rs (se 1 (by rfl) ⟨57848, by rfl⟩) R115697
theorem R77143 : Reach 77143 := rs (se 1 (by rfl) ⟨57857, by rfl⟩) R115715
theorem R77163 : Reach 77163 := rs (se 1 (by rfl) ⟨57872, by rfl⟩) R115745
theorem R77175 : Reach 77175 := rs (se 1 (by rfl) ⟨57881, by rfl⟩) R115763
theorem R77195 : Reach 77195 := rs (se 1 (by rfl) ⟨57896, by rfl⟩) R115793
theorem R175499 : Reach 175499 := rs (se 1 (by rfl) ⟨131624, by rfl⟩) R263249
theorem R77207 : Reach 77207 := rs (se 1 (by rfl) ⟨57905, by rfl⟩) R115811
theorem R77227 : Reach 77227 := rs (se 1 (by rfl) ⟨57920, by rfl⟩) R115841
theorem R77239 : Reach 77239 := rs (se 1 (by rfl) ⟨57929, by rfl⟩) R115859
theorem R175553 : Reach 175553 := rs (se 2 (by rfl) ⟨65832, by rfl⟩) R131665
theorem R77259 : Reach 77259 := rs (se 1 (by rfl) ⟨57944, by rfl⟩) R115889
theorem R77271 : Reach 77271 := rs (se 1 (by rfl) ⟨57953, by rfl⟩) R115907
theorem R77291 : Reach 77291 := rs (se 1 (by rfl) ⟨57968, by rfl⟩) R115937
theorem R77303 : Reach 77303 := rs (se 1 (by rfl) ⟨57977, by rfl⟩) R115955
theorem R77323 : Reach 77323 := rs (se 1 (by rfl) ⟨57992, by rfl⟩) R115985
theorem R77335 : Reach 77335 := rs (se 1 (by rfl) ⟨58001, by rfl⟩) R116003
theorem R77355 : Reach 77355 := rs (se 1 (by rfl) ⟨58016, by rfl⟩) R116033
theorem R372269 : Reach 372269 := rs (se 3 (by rfl) ⟨69800, by rfl⟩) R139601
theorem R77367 : Reach 77367 := rs (se 1 (by rfl) ⟨58025, by rfl⟩) R116051
theorem R77387 : Reach 77387 := rs (se 1 (by rfl) ⟨58040, by rfl⟩) R116081
theorem R77399 : Reach 77399 := rs (se 1 (by rfl) ⟨58049, by rfl⟩) R116099
theorem R274013 : Reach 274013 := rs (se 3 (by rfl) ⟨51377, by rfl⟩) R102755
theorem R77419 : Reach 77419 := rs (se 1 (by rfl) ⟨58064, by rfl⟩) R116129
theorem R77431 : Reach 77431 := rs (se 1 (by rfl) ⟨58073, by rfl⟩) R116147
theorem R77451 : Reach 77451 := rs (se 1 (by rfl) ⟨58088, by rfl⟩) R116177
theorem R77463 : Reach 77463 := rs (se 1 (by rfl) ⟨58097, by rfl⟩) R116195
theorem R175769 : Reach 175769 := rs (se 2 (by rfl) ⟨65913, by rfl⟩) R131827
theorem R77483 : Reach 77483 := rs (se 1 (by rfl) ⟨58112, by rfl⟩) R116225
theorem R77495 : Reach 77495 := rs (se 1 (by rfl) ⟨58121, by rfl⟩) R116243
theorem R77515 : Reach 77515 := rs (se 1 (by rfl) ⟨58136, by rfl⟩) R116273
theorem R77527 : Reach 77527 := rs (se 1 (by rfl) ⟨58145, by rfl⟩) R116291
theorem R77547 : Reach 77547 := rs (se 1 (by rfl) ⟨58160, by rfl⟩) R116321
theorem R175859 : Reach 175859 := rs (se 1 (by rfl) ⟨131894, by rfl⟩) R263789
theorem R77559 : Reach 77559 := rs (se 1 (by rfl) ⟨58169, by rfl⟩) R116339
theorem R77579 : Reach 77579 := rs (se 1 (by rfl) ⟨58184, by rfl⟩) R116369
theorem R77591 : Reach 77591 := rs (se 1 (by rfl) ⟨58193, by rfl⟩) R116387
theorem R175895 : Reach 175895 := rs (se 1 (by rfl) ⟨131921, by rfl⟩) R263843
theorem R77611 : Reach 77611 := rs (se 1 (by rfl) ⟨58208, by rfl⟩) R116417
theorem R77623 : Reach 77623 := rs (se 1 (by rfl) ⟨58217, by rfl⟩) R116435
theorem R77643 : Reach 77643 := rs (se 1 (by rfl) ⟨58232, by rfl⟩) R116465
theorem R77655 : Reach 77655 := rs (se 1 (by rfl) ⟨58241, by rfl⟩) R116483
theorem R77675 : Reach 77675 := rs (se 1 (by rfl) ⟨58256, by rfl⟩) R116513
theorem R77687 : Reach 77687 := rs (se 1 (by rfl) ⟨58265, by rfl⟩) R116531
theorem R77707 : Reach 77707 := rs (se 1 (by rfl) ⟨58280, by rfl⟩) R116561
theorem R77719 : Reach 77719 := rs (se 1 (by rfl) ⟨58289, by rfl⟩) R116579
theorem R110489 : Reach 110489 := rs (se 2 (by rfl) ⟨41433, by rfl⟩) R82867
theorem R77739 : Reach 77739 := rs (se 1 (by rfl) ⟨58304, by rfl⟩) R116609
theorem R77751 : Reach 77751 := rs (se 1 (by rfl) ⟨58313, by rfl⟩) R116627
theorem R77771 : Reach 77771 := rs (se 1 (by rfl) ⟨58328, by rfl⟩) R116657
theorem R176075 : Reach 176075 := rs (se 1 (by rfl) ⟨132056, by rfl⟩) R264113
theorem R77783 : Reach 77783 := rs (se 1 (by rfl) ⟨58337, by rfl⟩) R116675
theorem R1814489 : Reach 1814489 := rs (se 2 (by rfl) ⟨680433, by rfl⟩) R1360867
theorem R77803 : Reach 77803 := rs (se 1 (by rfl) ⟨58352, by rfl⟩) R116705
theorem R77815 : Reach 77815 := rs (se 1 (by rfl) ⟨58361, by rfl⟩) R116723
theorem R176129 : Reach 176129 := rs (se 2 (by rfl) ⟨66048, by rfl⟩) R132097
theorem R110603 : Reach 110603 := rs (se 1 (by rfl) ⟨82952, by rfl⟩) R165905
theorem R77835 : Reach 77835 := rs (se 1 (by rfl) ⟨58376, by rfl⟩) R116753
theorem R831505 : Reach 831505 := rs (se 2 (by rfl) ⟨311814, by rfl⟩) R623629
theorem R77847 : Reach 77847 := rs (se 1 (by rfl) ⟨58385, by rfl⟩) R116771
theorem R77867 : Reach 77867 := rs (se 1 (by rfl) ⟨58400, by rfl⟩) R116801
theorem R77879 : Reach 77879 := rs (se 1 (by rfl) ⟨58409, by rfl⟩) R116819
theorem R77899 : Reach 77899 := rs (se 1 (by rfl) ⟨58424, by rfl⟩) R116849
theorem R77911 : Reach 77911 := rs (se 1 (by rfl) ⟨58433, by rfl⟩) R116867
theorem R77931 : Reach 77931 := rs (se 1 (by rfl) ⟨58448, by rfl⟩) R116897
theorem R77943 : Reach 77943 := rs (se 1 (by rfl) ⟨58457, by rfl⟩) R116915
theorem R77963 : Reach 77963 := rs (se 1 (by rfl) ⟨58472, by rfl⟩) R116945
theorem R77975 : Reach 77975 := rs (se 1 (by rfl) ⟨58481, by rfl⟩) R116963
theorem R77995 : Reach 77995 := rs (se 1 (by rfl) ⟨58496, by rfl⟩) R116993
theorem R78007 : Reach 78007 := rs (se 1 (by rfl) ⟨58505, by rfl⟩) R117011
theorem R78027 : Reach 78027 := rs (se 1 (by rfl) ⟨58520, by rfl⟩) R117041
theorem R78039 : Reach 78039 := rs (se 1 (by rfl) ⟨58529, by rfl⟩) R117059
theorem R176345 : Reach 176345 := rs (se 2 (by rfl) ⟨66129, by rfl⟩) R132259
theorem R78059 : Reach 78059 := rs (se 1 (by rfl) ⟨58544, by rfl⟩) R117089
theorem R78071 : Reach 78071 := rs (se 1 (by rfl) ⟨58553, by rfl⟩) R117107
theorem R78091 : Reach 78091 := rs (se 1 (by rfl) ⟨58568, by rfl⟩) R117137
theorem R78103 : Reach 78103 := rs (se 1 (by rfl) ⟨58577, by rfl⟩) R117155
theorem R78123 : Reach 78123 := rs (se 1 (by rfl) ⟨58592, by rfl⟩) R117185
theorem R176435 : Reach 176435 := rs (se 1 (by rfl) ⟨132326, by rfl⟩) R264653
theorem R78135 : Reach 78135 := rs (se 1 (by rfl) ⟨58601, by rfl⟩) R117203
theorem R78155 : Reach 78155 := rs (se 1 (by rfl) ⟨58616, by rfl⟩) R117233
theorem R78167 : Reach 78167 := rs (se 1 (by rfl) ⟨58625, by rfl⟩) R117251
theorem R176471 : Reach 176471 := rs (se 1 (by rfl) ⟨132353, by rfl⟩) R264707
theorem R78187 : Reach 78187 := rs (se 1 (by rfl) ⟨58640, by rfl⟩) R117281
theorem R78199 : Reach 78199 := rs (se 1 (by rfl) ⟨58649, by rfl⟩) R117299
theorem R78219 : Reach 78219 := rs (se 1 (by rfl) ⟨58664, by rfl⟩) R117329
theorem R78231 : Reach 78231 := rs (se 1 (by rfl) ⟨58673, by rfl⟩) R117347
theorem R78251 : Reach 78251 := rs (se 1 (by rfl) ⟨58688, by rfl⟩) R117377
theorem R143795 : Reach 143795 := rs (se 1 (by rfl) ⟨107846, by rfl⟩) R215693
theorem R78263 : Reach 78263 := rs (se 1 (by rfl) ⟨58697, by rfl⟩) R117395
theorem R78283 : Reach 78283 := rs (se 1 (by rfl) ⟨58712, by rfl⟩) R117425
theorem R78295 : Reach 78295 := rs (se 1 (by rfl) ⟨58721, by rfl⟩) R117443
theorem R78315 : Reach 78315 := rs (se 1 (by rfl) ⟨58736, by rfl⟩) R117473
theorem R78327 : Reach 78327 := rs (se 1 (by rfl) ⟨58745, by rfl⟩) R117491
theorem R78347 : Reach 78347 := rs (se 1 (by rfl) ⟨58760, by rfl⟩) R117521
theorem R176651 : Reach 176651 := rs (se 1 (by rfl) ⟨132488, by rfl⟩) R264977
theorem R111127 : Reach 111127 := rs (se 1 (by rfl) ⟨83345, by rfl⟩) R166691
theorem R78359 : Reach 78359 := rs (se 1 (by rfl) ⟨58769, by rfl⟩) R117539
theorem R78379 : Reach 78379 := rs (se 1 (by rfl) ⟨58784, by rfl⟩) R117569
theorem R78391 : Reach 78391 := rs (se 1 (by rfl) ⟨58793, by rfl⟩) R117587
theorem R176705 : Reach 176705 := rs (se 2 (by rfl) ⟨66264, by rfl⟩) R132529
theorem R143947 : Reach 143947 := rs (se 1 (by rfl) ⟨107960, by rfl⟩) R215921
theorem R78411 : Reach 78411 := rs (se 1 (by rfl) ⟨58808, by rfl⟩) R117617
theorem R78423 : Reach 78423 := rs (se 1 (by rfl) ⟨58817, by rfl⟩) R117635
theorem R78443 : Reach 78443 := rs (se 1 (by rfl) ⟨58832, by rfl⟩) R117665
theorem R78455 : Reach 78455 := rs (se 1 (by rfl) ⟨58841, by rfl⟩) R117683
theorem R78475 : Reach 78475 := rs (se 1 (by rfl) ⟨58856, by rfl⟩) R117713
theorem R78487 : Reach 78487 := rs (se 1 (by rfl) ⟨58865, by rfl⟩) R117731
theorem R78507 : Reach 78507 := rs (se 1 (by rfl) ⟨58880, by rfl⟩) R117761
theorem R78519 : Reach 78519 := rs (se 1 (by rfl) ⟨58889, by rfl⟩) R117779
theorem R78539 : Reach 78539 := rs (se 1 (by rfl) ⟨58904, by rfl⟩) R117809
theorem R78551 : Reach 78551 := rs (se 1 (by rfl) ⟨58913, by rfl⟩) R117827
theorem R78571 : Reach 78571 := rs (se 1 (by rfl) ⟨58928, by rfl⟩) R117857
theorem R78583 : Reach 78583 := rs (se 1 (by rfl) ⟨58937, by rfl⟩) R117875
theorem R78603 : Reach 78603 := rs (se 1 (by rfl) ⟨58952, by rfl⟩) R117905
theorem R78615 : Reach 78615 := rs (se 1 (by rfl) ⟨58961, by rfl⟩) R117923
theorem R176921 : Reach 176921 := rs (se 2 (by rfl) ⟨66345, by rfl⟩) R132691
theorem R78635 : Reach 78635 := rs (se 1 (by rfl) ⟨58976, by rfl⟩) R117953
theorem R78647 : Reach 78647 := rs (se 1 (by rfl) ⟨58985, by rfl⟩) R117971
theorem R78667 : Reach 78667 := rs (se 1 (by rfl) ⟨59000, by rfl⟩) R118001
theorem R78679 : Reach 78679 := rs (se 1 (by rfl) ⟨59009, by rfl⟩) R118019
theorem R78699 : Reach 78699 := rs (se 1 (by rfl) ⟨59024, by rfl⟩) R118049
theorem R177011 : Reach 177011 := rs (se 1 (by rfl) ⟨132758, by rfl⟩) R265517
theorem R78711 : Reach 78711 := rs (se 1 (by rfl) ⟨59033, by rfl⟩) R118067
theorem R78731 : Reach 78731 := rs (se 1 (by rfl) ⟨59048, by rfl⟩) R118097
theorem R177047 : Reach 177047 := rs (se 1 (by rfl) ⟨132785, by rfl⟩) R265571
theorem R78743 : Reach 78743 := rs (se 1 (by rfl) ⟨59057, by rfl⟩) R118115
theorem R144281 : Reach 144281 := rs (se 2 (by rfl) ⟨54105, by rfl⟩) R108211
theorem R78763 : Reach 78763 := rs (se 1 (by rfl) ⟨59072, by rfl⟩) R118145
theorem R78775 : Reach 78775 := rs (se 1 (by rfl) ⟨59081, by rfl⟩) R118163
theorem R78795 : Reach 78795 := rs (se 1 (by rfl) ⟨59096, by rfl⟩) R118193
theorem R78807 : Reach 78807 := rs (se 1 (by rfl) ⟨59105, by rfl⟩) R118211
theorem R78827 : Reach 78827 := rs (se 1 (by rfl) ⟨59120, by rfl⟩) R118241
theorem R78839 : Reach 78839 := rs (se 1 (by rfl) ⟨59129, by rfl⟩) R118259
theorem R78859 : Reach 78859 := rs (se 1 (by rfl) ⟨59144, by rfl⟩) R118289
theorem R78871 : Reach 78871 := rs (se 1 (by rfl) ⟨59153, by rfl⟩) R118307
theorem R78891 : Reach 78891 := rs (se 1 (by rfl) ⟨59168, by rfl⟩) R118337
theorem R78903 : Reach 78903 := rs (se 1 (by rfl) ⟨59177, by rfl⟩) R118355
theorem R177227 : Reach 177227 := rs (se 1 (by rfl) ⟨132920, by rfl⟩) R265841
theorem R78923 : Reach 78923 := rs (se 1 (by rfl) ⟨59192, by rfl⟩) R118385
theorem R78935 : Reach 78935 := rs (se 1 (by rfl) ⟨59201, by rfl⟩) R118403
theorem R78955 : Reach 78955 := rs (se 1 (by rfl) ⟨59216, by rfl⟩) R118433
theorem R78967 : Reach 78967 := rs (se 1 (by rfl) ⟨59225, by rfl⟩) R118451
theorem R177281 : Reach 177281 := rs (se 2 (by rfl) ⟨66480, by rfl⟩) R132961
theorem R78987 : Reach 78987 := rs (se 1 (by rfl) ⟨59240, by rfl⟩) R118481
theorem R78999 : Reach 78999 := rs (se 1 (by rfl) ⟨59249, by rfl⟩) R118499
theorem R79019 : Reach 79019 := rs (se 1 (by rfl) ⟨59264, by rfl⟩) R118529
theorem R79031 : Reach 79031 := rs (se 1 (by rfl) ⟨59273, by rfl⟩) R118547
theorem R79051 : Reach 79051 := rs (se 1 (by rfl) ⟨59288, by rfl⟩) R118577
theorem R79063 : Reach 79063 := rs (se 1 (by rfl) ⟨59297, by rfl⟩) R118595
theorem R79083 : Reach 79083 := rs (se 1 (by rfl) ⟨59312, by rfl⟩) R118625
theorem R79095 : Reach 79095 := rs (se 1 (by rfl) ⟨59321, by rfl⟩) R118643
theorem R79115 : Reach 79115 := rs (se 1 (by rfl) ⟨59336, by rfl⟩) R118673
theorem R111947 : Reach 111947 := rs (se 1 (by rfl) ⟨83960, by rfl⟩) R167921
theorem R177497 : Reach 177497 := rs (se 2 (by rfl) ⟨66561, by rfl⟩) R133123
theorem R308573 : Reach 308573 := rs (se 3 (by rfl) ⟨57857, by rfl⟩) R115715
theorem R406885 : Reach 406885 := rs (se 4 (by rfl) ⟨38145, by rfl⟩) R76291
theorem R177587 : Reach 177587 := rs (se 1 (by rfl) ⟨133190, by rfl⟩) R266381
theorem R177623 : Reach 177623 := rs (se 1 (by rfl) ⟨133217, by rfl⟩) R266435
theorem R374233 : Reach 374233 := rs (se 2 (by rfl) ⟨140337, by rfl⟩) R280675
theorem R439769 : Reach 439769 := rs (se 2 (by rfl) ⟨164913, by rfl⟩) R329827
theorem R308701 : Reach 308701 := rs (se 3 (by rfl) ⟨57881, by rfl⟩) R115763
theorem R144919 : Reach 144919 := rs (se 1 (by rfl) ⟨108689, by rfl⟩) R217379
theorem R79499 : Reach 79499 := rs (se 1 (by rfl) ⟨59624, by rfl⟩) R119249
theorem R177803 : Reach 177803 := rs (se 1 (by rfl) ⟨133352, by rfl⟩) R266705
theorem R177857 : Reach 177857 := rs (se 2 (by rfl) ⟨66696, by rfl⟩) R133393
theorem R112715 : Reach 112715 := rs (se 1 (by rfl) ⟨84536, by rfl⟩) R169073
theorem R112727 : Reach 112727 := rs (se 1 (by rfl) ⟨84545, by rfl⟩) R169091
theorem R112793 : Reach 112793 := rs (se 2 (by rfl) ⟨42297, by rfl⟩) R84595
theorem R80119 : Reach 80119 := rs (se 1 (by rfl) ⟨60089, by rfl⟩) R120179
theorem R112907 : Reach 112907 := rs (se 1 (by rfl) ⟨84680, by rfl⟩) R169361
theorem R112919 : Reach 112919 := rs (se 1 (by rfl) ⟨84689, by rfl⟩) R169379
theorem R112921 : Reach 112921 := rs (se 2 (by rfl) ⟨42345, by rfl⟩) R84691
theorem R145739 : Reach 145739 := rs (se 1 (by rfl) ⟨109304, by rfl⟩) R218609
theorem R112985 : Reach 112985 := rs (se 2 (by rfl) ⟨42369, by rfl⟩) R84739
theorem R145793 : Reach 145793 := rs (se 2 (by rfl) ⟨54672, by rfl⟩) R109345
theorem R113099 : Reach 113099 := rs (se 1 (by rfl) ⟨84824, by rfl⟩) R169649
theorem R113111 : Reach 113111 := rs (se 1 (by rfl) ⟨84833, by rfl⟩) R169667
theorem R113177 : Reach 113177 := rs (se 2 (by rfl) ⟨42441, by rfl⟩) R84883
theorem R309835 : Reach 309835 := rs (se 1 (by rfl) ⟨232376, by rfl⟩) R464753
theorem R80471 : Reach 80471 := rs (se 1 (by rfl) ⟨60353, by rfl⟩) R120707
theorem R113291 : Reach 113291 := rs (se 1 (by rfl) ⟨84968, by rfl⟩) R169937
theorem R113303 : Reach 113303 := rs (se 1 (by rfl) ⟨84977, by rfl⟩) R169955
theorem R309977 : Reach 309977 := rs (se 2 (by rfl) ⟨116241, by rfl⟩) R232483
theorem R113369 : Reach 113369 := rs (se 2 (by rfl) ⟨42513, by rfl⟩) R85027
theorem R113483 : Reach 113483 := rs (se 1 (by rfl) ⟨85112, by rfl⟩) R170225
theorem R113495 : Reach 113495 := rs (se 1 (by rfl) ⟨85121, by rfl⟩) R170243
theorem R113561 : Reach 113561 := rs (se 2 (by rfl) ⟨42585, by rfl⟩) R85171
theorem R113675 : Reach 113675 := rs (se 1 (by rfl) ⟨85256, by rfl⟩) R170513
theorem R113687 : Reach 113687 := rs (se 1 (by rfl) ⟨85265, by rfl⟩) R170531
theorem R441409 : Reach 441409 := rs (se 2 (by rfl) ⟨165528, by rfl⟩) R331057
theorem R113753 : Reach 113753 := rs (se 2 (by rfl) ⟨42657, by rfl⟩) R85315
theorem R113867 : Reach 113867 := rs (se 1 (by rfl) ⟨85400, by rfl⟩) R170801
theorem R113879 : Reach 113879 := rs (se 1 (by rfl) ⟨85409, by rfl⟩) R170819
theorem R146711 : Reach 146711 := rs (se 1 (by rfl) ⟨110033, by rfl⟩) R220067
theorem R113945 : Reach 113945 := rs (se 2 (by rfl) ⟨42729, by rfl⟩) R85459
theorem R605515 : Reach 605515 := rs (se 1 (by rfl) ⟨454136, by rfl⟩) R908273
theorem R114059 : Reach 114059 := rs (se 1 (by rfl) ⟨85544, by rfl⟩) R171089
theorem R114071 : Reach 114071 := rs (se 1 (by rfl) ⟨85553, by rfl⟩) R171107
theorem R212375 : Reach 212375 := rs (se 1 (by rfl) ⟨159281, by rfl⟩) R318563
theorem R114137 : Reach 114137 := rs (se 2 (by rfl) ⟨42801, by rfl⟩) R85603
theorem R540121 : Reach 540121 := rs (se 2 (by rfl) ⟨202545, by rfl⟩) R405091
theorem R572993 : Reach 572993 := rs (se 2 (by rfl) ⟨214872, by rfl⟩) R429745
theorem R114251 : Reach 114251 := rs (se 1 (by rfl) ⟨85688, by rfl⟩) R171377
theorem R114263 : Reach 114263 := rs (se 1 (by rfl) ⟨85697, by rfl⟩) R171395
theorem R310873 : Reach 310873 := rs (se 2 (by rfl) ⟨116577, by rfl⟩) R233155
theorem R114329 : Reach 114329 := rs (se 2 (by rfl) ⟨42873, by rfl⟩) R85747
theorem R114443 : Reach 114443 := rs (se 1 (by rfl) ⟨85832, by rfl⟩) R171665
theorem R114455 : Reach 114455 := rs (se 1 (by rfl) ⟨85841, by rfl⟩) R171683
theorem R147251 : Reach 147251 := rs (se 1 (by rfl) ⟨110438, by rfl⟩) R220877
theorem R114521 : Reach 114521 := rs (se 2 (by rfl) ⟨42945, by rfl⟩) R85891
theorem R901043 : Reach 901043 := rs (se 1 (by rfl) ⟨675782, by rfl⟩) R1351565
theorem R114635 : Reach 114635 := rs (se 1 (by rfl) ⟨85976, by rfl⟩) R171953
theorem R114647 : Reach 114647 := rs (se 1 (by rfl) ⟨85985, by rfl⟩) R171971
theorem R114713 : Reach 114713 := rs (se 2 (by rfl) ⟨43017, by rfl⟩) R86035
theorem R114827 : Reach 114827 := rs (se 1 (by rfl) ⟨86120, by rfl⟩) R172241
theorem R3031181 : Reach 3031181 := rs (se 3 (by rfl) ⟨568346, by rfl⟩) R1136693
theorem R114839 : Reach 114839 := rs (se 1 (by rfl) ⟨86129, by rfl⟩) R172259
theorem R114905 : Reach 114905 := rs (se 2 (by rfl) ⟨43089, by rfl⟩) R86179
theorem R147737 : Reach 147737 := rs (se 2 (by rfl) ⟨55401, by rfl⟩) R110803
theorem R115019 : Reach 115019 := rs (se 1 (by rfl) ⟨86264, by rfl⟩) R172529
theorem R115031 : Reach 115031 := rs (se 1 (by rfl) ⟨86273, by rfl⟩) R172547
theorem R115097 : Reach 115097 := rs (se 2 (by rfl) ⟨43161, by rfl⟩) R86323
theorem R115211 : Reach 115211 := rs (se 1 (by rfl) ⟨86408, by rfl⟩) R172817
theorem R115223 : Reach 115223 := rs (se 1 (by rfl) ⟨86417, by rfl⟩) R172835
theorem R115289 : Reach 115289 := rs (se 2 (by rfl) ⟨43233, by rfl⟩) R86467
theorem R115403 : Reach 115403 := rs (se 1 (by rfl) ⟨86552, by rfl⟩) R173105
theorem R115415 : Reach 115415 := rs (se 1 (by rfl) ⟨86561, by rfl⟩) R173123
theorem R82679 : Reach 82679 := rs (se 1 (by rfl) ⟨62009, by rfl⟩) R124019
theorem R115481 : Reach 115481 := rs (se 2 (by rfl) ⟨43305, by rfl⟩) R86611
theorem R279389 : Reach 279389 := rs (se 3 (by rfl) ⟨52385, by rfl⟩) R104771
theorem R115595 : Reach 115595 := rs (se 1 (by rfl) ⟨86696, by rfl⟩) R173393
theorem R115607 : Reach 115607 := rs (se 1 (by rfl) ⟨86705, by rfl⟩) R173411
theorem R82891 : Reach 82891 := rs (se 1 (by rfl) ⟨62168, by rfl⟩) R124337
theorem R115673 : Reach 115673 := rs (se 2 (by rfl) ⟨43377, by rfl⟩) R86755
theorem R115787 : Reach 115787 := rs (se 1 (by rfl) ⟨86840, by rfl⟩) R173681
theorem R115799 : Reach 115799 := rs (se 1 (by rfl) ⟨86849, by rfl⟩) R173699
theorem R115865 : Reach 115865 := rs (se 2 (by rfl) ⟨43449, by rfl⟩) R86899
theorem R115979 : Reach 115979 := rs (se 1 (by rfl) ⟨86984, by rfl⟩) R173969
theorem R247063 : Reach 247063 := rs (se 1 (by rfl) ⟨185297, by rfl⟩) R370595
theorem R115991 : Reach 115991 := rs (se 1 (by rfl) ⟨86993, by rfl⟩) R173987
theorem R116057 : Reach 116057 := rs (se 2 (by rfl) ⟨43521, by rfl⟩) R87043
theorem R116171 : Reach 116171 := rs (se 1 (by rfl) ⟨87128, by rfl⟩) R174257
theorem R116183 : Reach 116183 := rs (se 1 (by rfl) ⟨87137, by rfl⟩) R174275
theorem R574937 : Reach 574937 := rs (se 2 (by rfl) ⟨215601, by rfl⟩) R431203
theorem R935441 : Reach 935441 := rs (se 2 (by rfl) ⟨350790, by rfl⟩) R701581
theorem R116249 : Reach 116249 := rs (se 2 (by rfl) ⟨43593, by rfl⟩) R87187
theorem R116311 : Reach 116311 := rs (se 1 (by rfl) ⟨87233, by rfl⟩) R174467
theorem R771677 : Reach 771677 := rs (se 3 (by rfl) ⟨144689, by rfl⟩) R289379
theorem R4867715 : Reach 4867715 := rs (se 1 (by rfl) ⟨3650786, by rfl⟩) R7301573
theorem R116363 : Reach 116363 := rs (se 1 (by rfl) ⟨87272, by rfl⟩) R174545
theorem R116375 : Reach 116375 := rs (se 1 (by rfl) ⟨87281, by rfl⟩) R174563
theorem R149195 : Reach 149195 := rs (se 1 (by rfl) ⟨111896, by rfl⟩) R223793
theorem R116441 : Reach 116441 := rs (se 2 (by rfl) ⟨43665, by rfl⟩) R87331
theorem R1001281 : Reach 1001281 := rs (se 2 (by rfl) ⟨375480, by rfl⟩) R750961
theorem R247627 : Reach 247627 := rs (se 1 (by rfl) ⟨185720, by rfl⟩) R371441
theorem R116555 : Reach 116555 := rs (se 1 (by rfl) ⟨87416, by rfl⟩) R174833
theorem R116567 : Reach 116567 := rs (se 1 (by rfl) ⟨87425, by rfl⟩) R174851
theorem R149377 : Reach 149377 := rs (se 2 (by rfl) ⟨56016, by rfl⟩) R112033
theorem R116633 : Reach 116633 := rs (se 2 (by rfl) ⟨43737, by rfl⟩) R87475
theorem R214987 : Reach 214987 := rs (se 1 (by rfl) ⟨161240, by rfl⟩) R322481
theorem R280523 : Reach 280523 := rs (se 1 (by rfl) ⟨210392, by rfl⟩) R420785
theorem R247769 : Reach 247769 := rs (se 2 (by rfl) ⟨92913, by rfl⟩) R185827
theorem R116747 : Reach 116747 := rs (se 1 (by rfl) ⟨87560, by rfl⟩) R175121
theorem R116759 : Reach 116759 := rs (se 1 (by rfl) ⟨87569, by rfl⟩) R175139
theorem R116825 : Reach 116825 := rs (se 2 (by rfl) ⟨43809, by rfl⟩) R87619
theorem R247901 : Reach 247901 := rs (se 3 (by rfl) ⟨46481, by rfl⟩) R92963
theorem R739459 : Reach 739459 := rs (se 1 (by rfl) ⟨554594, by rfl⟩) R1109189
theorem R116939 : Reach 116939 := rs (se 1 (by rfl) ⟨87704, by rfl⟩) R175409
theorem R706765 : Reach 706765 := rs (se 3 (by rfl) ⟨132518, by rfl⟩) R265037
theorem R116951 : Reach 116951 := rs (se 1 (by rfl) ⟨87713, by rfl⟩) R175427
theorem R215261 : Reach 215261 := rs (se 3 (by rfl) ⟨40361, by rfl⟩) R80723
theorem R117017 : Reach 117017 := rs (se 2 (by rfl) ⟨43881, by rfl⟩) R87763
theorem R149825 : Reach 149825 := rs (se 2 (by rfl) ⟨56184, by rfl⟩) R112369
theorem R117131 : Reach 117131 := rs (se 1 (by rfl) ⟨87848, by rfl⟩) R175697
theorem R117143 : Reach 117143 := rs (se 1 (by rfl) ⟨87857, by rfl⟩) R175715
theorem R444851 : Reach 444851 := rs (se 1 (by rfl) ⟨333638, by rfl⟩) R667277
theorem R84439 : Reach 84439 := rs (se 1 (by rfl) ⟨63329, by rfl⟩) R126659
theorem R117209 : Reach 117209 := rs (se 2 (by rfl) ⟨43953, by rfl⟩) R87907
theorem R84523 : Reach 84523 := rs (se 1 (by rfl) ⟨63392, by rfl⟩) R126785
theorem R117323 : Reach 117323 := rs (se 1 (by rfl) ⟨87992, by rfl⟩) R175985
theorem R117335 : Reach 117335 := rs (se 1 (by rfl) ⟨88001, by rfl⟩) R176003
theorem R281177 : Reach 281177 := rs (se 2 (by rfl) ⟨105441, by rfl⟩) R210883
theorem R84631 : Reach 84631 := rs (se 1 (by rfl) ⟨63473, by rfl⟩) R126947
theorem R150167 : Reach 150167 := rs (se 1 (by rfl) ⟨112625, by rfl⟩) R225251
theorem R117401 : Reach 117401 := rs (se 2 (by rfl) ⟨44025, by rfl⟩) R88051
theorem R117515 : Reach 117515 := rs (se 1 (by rfl) ⟨88136, by rfl⟩) R176273
theorem R117527 : Reach 117527 := rs (se 1 (by rfl) ⟨88145, by rfl⟩) R176291
theorem R84811 : Reach 84811 := rs (se 1 (by rfl) ⟨63608, by rfl⟩) R127217
theorem R117593 : Reach 117593 := rs (se 2 (by rfl) ⟨44097, by rfl⟩) R88195
theorem R2411441 : Reach 2411441 := rs (se 2 (by rfl) ⟨904290, by rfl⟩) R1808581
theorem R543667 : Reach 543667 := rs (se 1 (by rfl) ⟨407750, by rfl⟩) R815501
theorem R84919 : Reach 84919 := rs (se 1 (by rfl) ⟨63689, by rfl⟩) R127379
theorem R117707 : Reach 117707 := rs (se 1 (by rfl) ⟨88280, by rfl⟩) R176561
theorem R117719 : Reach 117719 := rs (se 1 (by rfl) ⟨88289, by rfl⟩) R176579
theorem R117785 : Reach 117785 := rs (se 2 (by rfl) ⟨44169, by rfl⟩) R88339
theorem R85099 : Reach 85099 := rs (se 1 (by rfl) ⟨63824, by rfl⟩) R127649
theorem R117899 : Reach 117899 := rs (se 1 (by rfl) ⟨88424, by rfl⟩) R176849
theorem R117911 : Reach 117911 := rs (se 1 (by rfl) ⟨88433, by rfl⟩) R176867
theorem R249011 : Reach 249011 := rs (se 1 (by rfl) ⟨186758, by rfl⟩) R373517
theorem R85207 : Reach 85207 := rs (se 1 (by rfl) ⟨63905, by rfl⟩) R127811
theorem R117977 : Reach 117977 := rs (se 2 (by rfl) ⟨44241, by rfl⟩) R88483
theorem R118091 : Reach 118091 := rs (se 1 (by rfl) ⟨88568, by rfl⟩) R177137
theorem R118103 : Reach 118103 := rs (se 1 (by rfl) ⟨88577, by rfl⟩) R177155
theorem R85387 : Reach 85387 := rs (se 1 (by rfl) ⟨64040, by rfl⟩) R128081
theorem R183703 : Reach 183703 := rs (se 1 (by rfl) ⟨137777, by rfl⟩) R275555
theorem R118169 : Reach 118169 := rs (se 2 (by rfl) ⟨44313, by rfl⟩) R88627
theorem R85495 : Reach 85495 := rs (se 1 (by rfl) ⟨64121, by rfl⟩) R128243
theorem R118283 : Reach 118283 := rs (se 1 (by rfl) ⟨88712, by rfl⟩) R177425
theorem R118295 : Reach 118295 := rs (se 1 (by rfl) ⟨88721, by rfl⟩) R177443
theorem R249409 : Reach 249409 := rs (se 2 (by rfl) ⟨93528, by rfl⟩) R187057
theorem R118361 : Reach 118361 := rs (se 2 (by rfl) ⟨44385, by rfl⟩) R88771
theorem R85655 : Reach 85655 := rs (se 1 (by rfl) ⟨64241, by rfl⟩) R128483
theorem R85675 : Reach 85675 := rs (se 1 (by rfl) ⟨64256, by rfl⟩) R128513
theorem R118475 : Reach 118475 := rs (se 1 (by rfl) ⟨88856, by rfl⟩) R177713
theorem R118487 : Reach 118487 := rs (se 1 (by rfl) ⟨88865, by rfl⟩) R177731
theorem R85783 : Reach 85783 := rs (se 1 (by rfl) ⟨64337, by rfl⟩) R128675
theorem R118553 : Reach 118553 := rs (se 2 (by rfl) ⟨44457, by rfl⟩) R88915
theorem R446309 : Reach 446309 := rs (se 4 (by rfl) ⟨41841, by rfl⟩) R83683
theorem R118667 : Reach 118667 := rs (se 1 (by rfl) ⟨89000, by rfl⟩) R178001
theorem R118679 : Reach 118679 := rs (se 1 (by rfl) ⟨89009, by rfl⟩) R178019
theorem R479155 : Reach 479155 := rs (se 1 (by rfl) ⟨359366, by rfl⟩) R718733
theorem R85963 : Reach 85963 := rs (se 1 (by rfl) ⟨64472, by rfl⟩) R128945
theorem R86071 : Reach 86071 := rs (se 1 (by rfl) ⟨64553, by rfl⟩) R129107
theorem R86251 : Reach 86251 := rs (se 1 (by rfl) ⟨64688, by rfl⟩) R129377
theorem R86359 : Reach 86359 := rs (se 1 (by rfl) ⟨64769, by rfl⟩) R129539
theorem R217561 : Reach 217561 := rs (se 2 (by rfl) ⟨81585, by rfl⟩) R163171
theorem R86539 : Reach 86539 := rs (se 1 (by rfl) ⟨64904, by rfl⟩) R129809
theorem R86647 : Reach 86647 := rs (se 1 (by rfl) ⟨64985, by rfl⟩) R129971
theorem R774917 : Reach 774917 := rs (se 4 (by rfl) ⟨72648, by rfl⟩) R145297
theorem R578339 : Reach 578339 := rs (se 1 (by rfl) ⟨433754, by rfl⟩) R867509
theorem R86827 : Reach 86827 := rs (se 1 (by rfl) ⟨65120, by rfl⟩) R130241
theorem R86935 : Reach 86935 := rs (se 1 (by rfl) ⟨65201, by rfl⟩) R130403
theorem R218177 : Reach 218177 := rs (se 2 (by rfl) ⟨81816, by rfl⟩) R163633
theorem R87115 : Reach 87115 := rs (se 1 (by rfl) ⟨65336, by rfl⟩) R130673
theorem R251059 : Reach 251059 := rs (se 1 (by rfl) ⟨188294, by rfl⟩) R376589
theorem R87223 : Reach 87223 := rs (se 1 (by rfl) ⟨65417, by rfl⟩) R130835
theorem R87403 : Reach 87403 := rs (se 1 (by rfl) ⟨65552, by rfl⟩) R131105
theorem R284077 : Reach 284077 := rs (se 3 (by rfl) ⟨53264, by rfl⟩) R106529
theorem R87511 : Reach 87511 := rs (se 1 (by rfl) ⟨65633, by rfl⟩) R131267
theorem R382481 : Reach 382481 := rs (se 2 (by rfl) ⟨143430, by rfl⟩) R286861
theorem R415363 : Reach 415363 := rs (se 1 (by rfl) ⟨311522, by rfl⟩) R623045
theorem R87691 : Reach 87691 := rs (se 1 (by rfl) ⟨65768, by rfl⟩) R131537
theorem R382643 : Reach 382643 := rs (se 1 (by rfl) ⟨286982, by rfl⟩) R573965
theorem R2119409 : Reach 2119409 := rs (se 2 (by rfl) ⟨794778, by rfl⟩) R1589557
theorem R87799 : Reach 87799 := rs (se 1 (by rfl) ⟨65849, by rfl⟩) R131699
theorem R350027 : Reach 350027 := rs (se 1 (by rfl) ⟨262520, by rfl⟩) R525041
theorem R87979 : Reach 87979 := rs (se 1 (by rfl) ⟨65984, by rfl⟩) R131969
theorem R88087 : Reach 88087 := rs (se 1 (by rfl) ⟨66065, by rfl⟩) R132131
theorem R153751 : Reach 153751 := rs (se 1 (by rfl) ⟨115313, by rfl⟩) R230627
theorem R88267 : Reach 88267 := rs (se 1 (by rfl) ⟨66200, by rfl⟩) R132401
theorem R88375 : Reach 88375 := rs (se 1 (by rfl) ⟨66281, by rfl⟩) R132563
theorem R88555 : Reach 88555 := rs (se 1 (by rfl) ⟨66416, by rfl⟩) R132833
theorem R88663 : Reach 88663 := rs (se 1 (by rfl) ⟨66497, by rfl⟩) R132995
theorem R121495 : Reach 121495 := rs (se 1 (by rfl) ⟨91121, by rfl⟩) R182243
theorem R88843 : Reach 88843 := rs (se 1 (by rfl) ⟨66632, by rfl⟩) R133265
theorem R154391 : Reach 154391 := rs (se 1 (by rfl) ⟨115793, by rfl⟩) R231587
theorem R187211 : Reach 187211 := rs (se 1 (by rfl) ⟨140408, by rfl⟩) R280817
theorem R88951 : Reach 88951 := rs (se 1 (by rfl) ⟨66713, by rfl⟩) R133427
theorem R121751 : Reach 121751 := rs (se 1 (by rfl) ⟨91313, by rfl⟩) R182627
theorem R220249 : Reach 220249 := rs (se 2 (by rfl) ⟨82593, by rfl⟩) R165187
theorem R285875 : Reach 285875 := rs (se 1 (by rfl) ⟨214406, by rfl⟩) R428813
theorem R285889 : Reach 285889 := rs (se 2 (by rfl) ⟨107208, by rfl⟩) R214417
theorem R122123 : Reach 122123 := rs (se 1 (by rfl) ⟨91592, by rfl⟩) R183185
theorem R220637 : Reach 220637 := rs (se 3 (by rfl) ⟨41369, by rfl⟩) R82739
theorem R384587 : Reach 384587 := rs (se 1 (by rfl) ⟨288440, by rfl⟩) R576881
theorem R122455 : Reach 122455 := rs (se 1 (by rfl) ⟨91841, by rfl⟩) R183683
theorem R417611 : Reach 417611 := rs (se 1 (by rfl) ⟨313208, by rfl⟩) R626417
theorem R1007477 : Reach 1007477 := rs (se 5 (by rfl) ⟨47225, by rfl⟩) R94451
theorem R90391 : Reach 90391 := rs (se 1 (by rfl) ⟨67793, by rfl⟩) R135587
theorem R254231 : Reach 254231 := rs (se 1 (by rfl) ⟨190673, by rfl⟩) R381347
theorem R319895 : Reach 319895 := rs (se 1 (by rfl) ⟨239921, by rfl⟩) R479843
theorem R123353 : Reach 123353 := rs (se 2 (by rfl) ⟨46257, by rfl⟩) R92515
theorem R123545 : Reach 123545 := rs (se 2 (by rfl) ⟨46329, by rfl⟩) R92659
theorem R254771 : Reach 254771 := rs (se 1 (by rfl) ⟨191078, by rfl⟩) R382157
theorem R1008449 : Reach 1008449 := rs (se 2 (by rfl) ⟨378168, by rfl⟩) R756337
theorem R320345 : Reach 320345 := rs (se 2 (by rfl) ⟨120129, by rfl⟩) R240259
theorem R1860569 : Reach 1860569 := rs (se 2 (by rfl) ⟨697713, by rfl⟩) R1395427
theorem R255041 : Reach 255041 := rs (se 2 (by rfl) ⟨95640, by rfl⟩) R191281
theorem R287819 : Reach 287819 := rs (se 1 (by rfl) ⟨215864, by rfl⟩) R431729
theorem R287833 : Reach 287833 := rs (se 2 (by rfl) ⟨107937, by rfl⟩) R215875
theorem R189719 : Reach 189719 := rs (se 1 (by rfl) ⟨142289, by rfl⟩) R284579
theorem R386369 : Reach 386369 := rs (se 2 (by rfl) ⟨144888, by rfl⟩) R289777
theorem R3630563 : Reach 3630563 := rs (se 1 (by rfl) ⟨2722922, by rfl⟩) R5445845
theorem R255581 : Reach 255581 := rs (se 3 (by rfl) ⟨47921, by rfl⟩) R95843
theorem R190259 : Reach 190259 := rs (se 1 (by rfl) ⟨142694, by rfl⟩) R285389
theorem R157643 : Reach 157643 := rs (se 1 (by rfl) ⟨118232, by rfl⟩) R236465
theorem R583685 : Reach 583685 := rs (se 4 (by rfl) ⟨54720, by rfl⟩) R109441
theorem R288791 : Reach 288791 := rs (se 1 (by rfl) ⟨216593, by rfl⟩) R433187
theorem R223553 : Reach 223553 := rs (se 2 (by rfl) ⟨83832, by rfl⟩) R167665
theorem R190795 : Reach 190795 := rs (se 1 (by rfl) ⟨143096, by rfl⟩) R286193
theorem R223667 : Reach 223667 := rs (se 1 (by rfl) ⟨167750, by rfl⟩) R335501
theorem R190937 : Reach 190937 := rs (se 2 (by rfl) ⟨71601, by rfl⟩) R143203
theorem R256715 : Reach 256715 := rs (se 1 (by rfl) ⟨192536, by rfl⟩) R385073
theorem R322379 : Reach 322379 := rs (se 1 (by rfl) ⟨241784, by rfl⟩) R483569
theorem R256985 : Reach 256985 := rs (se 2 (by rfl) ⟨96369, by rfl⟩) R192739
theorem R158681 : Reach 158681 := rs (se 2 (by rfl) ⟨59505, by rfl⟩) R119011
theorem R1338443 : Reach 1338443 := rs (se 1 (by rfl) ⟨1003832, by rfl⟩) R2007665
theorem R388313 : Reach 388313 := rs (se 2 (by rfl) ⟨145617, by rfl⟩) R291235
theorem R290051 : Reach 290051 := rs (se 1 (by rfl) ⟨217538, by rfl⟩) R435077
theorem R191767 : Reach 191767 := rs (se 1 (by rfl) ⟨143825, by rfl⟩) R287651
theorem R1371491 : Reach 1371491 := rs (se 1 (by rfl) ⟨1028618, by rfl⟩) R2057237
theorem R159127 : Reach 159127 := rs (se 1 (by rfl) ⟨119345, by rfl⟩) R238691
theorem R585251 : Reach 585251 := rs (se 1 (by rfl) ⟨438938, by rfl⟩) R877877
theorem R257687 : Reach 257687 := rs (se 1 (by rfl) ⟨193265, by rfl⟩) R386531
theorem R192203 : Reach 192203 := rs (se 1 (by rfl) ⟨144152, by rfl⟩) R288305
theorem R913157 : Reach 913157 := rs (se 4 (by rfl) ⟨85608, by rfl⟩) R171217
theorem R126859 : Reach 126859 := rs (se 1 (by rfl) ⟨95144, by rfl⟩) R190289
theorem R192449 : Reach 192449 := rs (se 2 (by rfl) ⟨72168, by rfl⟩) R144337
theorem R127001 : Reach 127001 := rs (se 2 (by rfl) ⟨47625, by rfl⟩) R95251
theorem R192577 : Reach 192577 := rs (se 2 (by rfl) ⟨72216, by rfl⟩) R144433
theorem R192601 : Reach 192601 := rs (se 2 (by rfl) ⟨72225, by rfl⟩) R144451
theorem R127129 : Reach 127129 := rs (se 2 (by rfl) ⟨47673, by rfl⟩) R95347
theorem R258227 : Reach 258227 := rs (se 1 (by rfl) ⟨193670, by rfl⟩) R387341
theorem R586115 : Reach 586115 := rs (se 1 (by rfl) ⟨439586, by rfl⟩) R879173
theorem R258455 : Reach 258455 := rs (se 1 (by rfl) ⟨193841, by rfl⟩) R387683
theorem R258497 : Reach 258497 := rs (se 2 (by rfl) ⟨96936, by rfl⟩) R193873
theorem R291275 : Reach 291275 := rs (se 1 (by rfl) ⟨218456, by rfl⟩) R436913
theorem R94859 : Reach 94859 := rs (se 1 (by rfl) ⟨71144, by rfl⟩) R142289
theorem R193175 : Reach 193175 := rs (se 1 (by rfl) ⟨144881, by rfl⟩) R289763
theorem R160471 : Reach 160471 := rs (se 1 (by rfl) ⟨120353, by rfl⟩) R240707
theorem R127703 : Reach 127703 := rs (se 1 (by rfl) ⟨95777, by rfl⟩) R191555
theorem R1274629 : Reach 1274629 := rs (se 4 (by rfl) ⟨119496, by rfl⟩) R238993
theorem R389933 : Reach 389933 := rs (se 3 (by rfl) ⟨73112, by rfl⟩) R146225
theorem R127831 : Reach 127831 := rs (se 1 (by rfl) ⟨95873, by rfl⟩) R191747
theorem R259037 : Reach 259037 := rs (se 3 (by rfl) ⟨48569, by rfl⟩) R97139
theorem R226583 : Reach 226583 := rs (se 1 (by rfl) ⟨169937, by rfl⟩) R339875
theorem R95575 : Reach 95575 := rs (se 1 (by rfl) ⟨71681, by rfl⟩) R143363
theorem R325043 : Reach 325043 := rs (se 1 (by rfl) ⟨243782, by rfl⟩) R487565
theorem R193985 : Reach 193985 := rs (se 2 (by rfl) ⟨72744, by rfl⟩) R145489
theorem R128459 : Reach 128459 := rs (se 1 (by rfl) ⟨96344, by rfl⟩) R192689
theorem R128587 : Reach 128587 := rs (se 1 (by rfl) ⟨96440, by rfl⟩) R192881
theorem R128729 : Reach 128729 := rs (se 2 (by rfl) ⟨48273, by rfl⟩) R96547
theorem R423755 : Reach 423755 := rs (se 1 (by rfl) ⟨317816, by rfl⟩) R635633
theorem R128857 : Reach 128857 := rs (se 2 (by rfl) ⟨48321, by rfl⟩) R96643
theorem R161651 : Reach 161651 := rs (se 1 (by rfl) ⟨121238, by rfl⟩) R242477
theorem R194521 : Reach 194521 := rs (se 2 (by rfl) ⟨72945, by rfl⟩) R145891
theorem R260171 : Reach 260171 := rs (se 1 (by rfl) ⟨195128, by rfl⟩) R390257
theorem R96395 : Reach 96395 := rs (se 1 (by rfl) ⟨72296, by rfl⟩) R144593
theorem R293165 : Reach 293165 := rs (se 3 (by rfl) ⟨54968, by rfl⟩) R109937
theorem R260441 : Reach 260441 := rs (se 2 (by rfl) ⟨97665, by rfl⟩) R195331
theorem R129431 : Reach 129431 := rs (se 1 (by rfl) ⟨97073, by rfl⟩) R194147
theorem R129559 : Reach 129559 := rs (se 1 (by rfl) ⟨97169, by rfl⟩) R194339
theorem R654155 : Reach 654155 := rs (se 1 (by rfl) ⟨490616, by rfl⟩) R981233
theorem R490333 : Reach 490333 := rs (se 3 (by rfl) ⟨91937, by rfl⟩) R183875
theorem R326531 : Reach 326531 := rs (se 1 (by rfl) ⟨244898, by rfl⟩) R489797
theorem R97291 : Reach 97291 := rs (se 1 (by rfl) ⟨72968, by rfl⟩) R145937
theorem R261143 : Reach 261143 := rs (se 1 (by rfl) ⟨195857, by rfl⟩) R391715
theorem R195635 : Reach 195635 := rs (se 1 (by rfl) ⟨146726, by rfl⟩) R293453
theorem R293939 : Reach 293939 := rs (se 1 (by rfl) ⟨220454, by rfl⟩) R440909
theorem R162881 : Reach 162881 := rs (se 2 (by rfl) ⟨61080, by rfl⟩) R122161
theorem R195659 : Reach 195659 := rs (se 1 (by rfl) ⟨146744, by rfl⟩) R293489
theorem R130187 : Reach 130187 := rs (se 1 (by rfl) ⟨97640, by rfl⟩) R195281
theorem R130315 : Reach 130315 := rs (se 1 (by rfl) ⟨97736, by rfl⟩) R195473
theorem R195929 : Reach 195929 := rs (se 2 (by rfl) ⟨73473, by rfl⟩) R146947
theorem R130457 : Reach 130457 := rs (se 2 (by rfl) ⟨48921, by rfl⟩) R97843
theorem R130585 : Reach 130585 := rs (se 2 (by rfl) ⟨48969, by rfl⟩) R97939
theorem R261683 : Reach 261683 := rs (se 1 (by rfl) ⟨196262, by rfl⟩) R392525
theorem R589517 : Reach 589517 := rs (se 3 (by rfl) ⟨110534, by rfl⟩) R221069
theorem R261953 : Reach 261953 := rs (se 2 (by rfl) ⟨98232, by rfl⟩) R196465
theorem R130891 : Reach 130891 := rs (se 1 (by rfl) ⟨98168, by rfl⟩) R196337
theorem R1343411 : Reach 1343411 := rs (se 1 (by rfl) ⟨1007558, by rfl⟩) R2015117
theorem R98263 : Reach 98263 := rs (se 1 (by rfl) ⟨73697, by rfl⟩) R147395
theorem R294941 : Reach 294941 := rs (se 3 (by rfl) ⟨55301, by rfl⟩) R110603
theorem R393335 : Reach 393335 := rs (se 1 (by rfl) ⟨295001, by rfl⟩) R590003
theorem R98491 : Reach 98491 := rs (se 1 (by rfl) ⟨73868, by rfl⟩) R147737
theorem R131387 : Reach 131387 := rs (se 1 (by rfl) ⟨98540, by rfl⟩) R197081
theorem R196951 : Reach 196951 := rs (se 1 (by rfl) ⟨147713, by rfl⟩) R295427
theorem R262547 : Reach 262547 := rs (se 1 (by rfl) ⟨196910, by rfl⟩) R393821
theorem R754105 : Reach 754105 := rs (se 2 (by rfl) ⟨282789, by rfl⟩) R565579
theorem R197255 : Reach 197255 := rs (se 1 (by rfl) ⟨147941, by rfl⟩) R295883
theorem R131719 : Reach 131719 := rs (se 1 (by rfl) ⟨98789, by rfl⟩) R197579
theorem R197387 : Reach 197387 := rs (se 1 (by rfl) ⟨148040, by rfl⟩) R296081
theorem R623627 : Reach 623627 := rs (se 1 (by rfl) ⟨467720, by rfl⟩) R935441
theorem R4949045 : Reach 4949045 := rs (se 5 (by rfl) ⟨231986, by rfl⟩) R463973
theorem R689213 : Reach 689213 := rs (se 3 (by rfl) ⟨129227, by rfl⟩) R258455
theorem R394307 : Reach 394307 := rs (se 1 (by rfl) ⟨295730, by rfl⟩) R591461
theorem R3245143 : Reach 3245143 := rs (se 1 (by rfl) ⟨2433857, by rfl⟩) R4867715
theorem R99463 : Reach 99463 := rs (se 1 (by rfl) ⟨74597, by rfl⟩) R149195
theorem R197903 : Reach 197903 := rs (se 1 (by rfl) ⟨148427, by rfl⟩) R296855
theorem R132367 : Reach 132367 := rs (se 1 (by rfl) ⟨99275, by rfl⟩) R198551
theorem R427301 : Reach 427301 := rs (se 4 (by rfl) ⟨40059, by rfl⟩) R80119
theorem R165179 : Reach 165179 := rs (se 1 (by rfl) ⟨123884, by rfl⟩) R247769
theorem R394631 : Reach 394631 := rs (se 1 (by rfl) ⟨295973, by rfl⟩) R591947
theorem R198035 : Reach 198035 := rs (se 1 (by rfl) ⟨148526, by rfl⟩) R297053
theorem R99883 : Reach 99883 := rs (se 1 (by rfl) ⟨74912, by rfl⟩) R149825
theorem R296567 : Reach 296567 := rs (se 1 (by rfl) ⟨222425, by rfl⟩) R444851
theorem R362177 : Reach 362177 := rs (se 2 (by rfl) ⟨135816, by rfl⟩) R271633
theorem R329417 : Reach 329417 := rs (se 2 (by rfl) ⟨123531, by rfl⟩) R247063
theorem R329453 : Reach 329453 := rs (se 3 (by rfl) ⟨61772, by rfl⟩) R123545
theorem R263951 : Reach 263951 := rs (se 1 (by rfl) ⟨197963, by rfl⟩) R395927
theorem R100111 : Reach 100111 := rs (se 1 (by rfl) ⟨75083, by rfl⟩) R150167
theorem R132907 : Reach 132907 := rs (se 1 (by rfl) ⟨99680, by rfl⟩) R199361
theorem R133049 : Reach 133049 := rs (se 2 (by rfl) ⟨49893, by rfl⟩) R99787
theorem R1607627 : Reach 1607627 := rs (se 1 (by rfl) ⟨1205720, by rfl⟩) R2411441
theorem R264221 : Reach 264221 := rs (se 3 (by rfl) ⟨49541, by rfl⟩) R99083
theorem R166007 : Reach 166007 := rs (se 1 (by rfl) ⟨124505, by rfl⟩) R249011
theorem R330043 : Reach 330043 := rs (se 1 (by rfl) ⟨247532, by rfl⟩) R495065
theorem R330169 : Reach 330169 := rs (se 2 (by rfl) ⟨123813, by rfl⟩) R247627
theorem R199169 : Reach 199169 := rs (se 2 (by rfl) ⟨74688, by rfl⟩) R149377
theorem R297539 : Reach 297539 := rs (se 1 (by rfl) ⟨223154, by rfl⟩) R446309
theorem R985945 : Reach 985945 := rs (se 2 (by rfl) ⟨369729, by rfl⟩) R739459
theorem R199543 : Reach 199543 := rs (se 1 (by rfl) ⟨149657, by rfl⟩) R299315
theorem R592919 : Reach 592919 := rs (se 1 (by rfl) ⟨444689, by rfl⟩) R889379
theorem R199979 : Reach 199979 := rs (se 1 (by rfl) ⟨149984, by rfl⟩) R299969
theorem R462131 : Reach 462131 := rs (se 1 (by rfl) ⟨346598, by rfl⟩) R693197
theorem R265625 : Reach 265625 := rs (se 2 (by rfl) ⟨99609, by rfl⟩) R199219
theorem R232961 : Reach 232961 := rs (se 2 (by rfl) ⟨87360, by rfl⟩) R174721
theorem R298525 : Reach 298525 := rs (se 3 (by rfl) ⟨55973, by rfl⟩) R111947
theorem R527939 : Reach 527939 := rs (se 1 (by rfl) ⟨395954, by rfl⟩) R791909
theorem R855845 : Reach 855845 := rs (se 4 (by rfl) ⟨80235, by rfl⟩) R160471
theorem R1412939 : Reach 1412939 := rs (se 1 (by rfl) ⟨1059704, by rfl⟩) R2119409
theorem R233351 : Reach 233351 := rs (se 1 (by rfl) ⟨175013, by rfl⟩) R350027
theorem R724889 : Reach 724889 := rs (se 2 (by rfl) ⟨271833, by rfl⟩) R543667
theorem R266327 : Reach 266327 := rs (se 1 (by rfl) ⟨199745, by rfl⟩) R399491
theorem R201079 : Reach 201079 := rs (se 1 (by rfl) ⟨150809, by rfl⟩) R301619
theorem R364945 : Reach 364945 := rs (se 2 (by rfl) ⟨136854, by rfl⟩) R273709
theorem R266813 : Reach 266813 := rs (se 3 (by rfl) ⟨50027, by rfl⟩) R100055
theorem R332545 : Reach 332545 := rs (se 2 (by rfl) ⟨124704, by rfl⟩) R249409
theorem R398195 : Reach 398195 := rs (se 1 (by rfl) ⟨298646, by rfl⟩) R597293
theorem R169145 : Reach 169145 := rs (se 2 (by rfl) ⟨63429, by rfl⟩) R126859
theorem R398681 : Reach 398681 := rs (se 2 (by rfl) ⟨149505, by rfl⟩) R299011
theorem R169487 : Reach 169487 := rs (se 1 (by rfl) ⟨127115, by rfl⟩) R254231
theorem R169505 : Reach 169505 := rs (se 2 (by rfl) ⟨63564, by rfl⟩) R127129
theorem R398915 : Reach 398915 := rs (se 1 (by rfl) ⟨299186, by rfl⟩) R598373
theorem R104009 : Reach 104009 := rs (se 2 (by rfl) ⟨39003, by rfl⟩) R78007
theorem R661069 : Reach 661069 := rs (se 3 (by rfl) ⟨123950, by rfl⟩) R247901
theorem R169847 : Reach 169847 := rs (se 1 (by rfl) ⟨127385, by rfl⟩) R254771
theorem R170027 : Reach 170027 := rs (se 1 (by rfl) ⟨127520, by rfl⟩) R255041
theorem R170387 : Reach 170387 := rs (se 1 (by rfl) ⟨127790, by rfl⟩) R255581
theorem R170441 : Reach 170441 := rs (se 2 (by rfl) ⟨63915, by rfl⟩) R127831
theorem R105095 : Reach 105095 := rs (se 1 (by rfl) ⟨78821, by rfl⟩) R157643
theorem R334745 : Reach 334745 := rs (se 2 (by rfl) ⟨125529, by rfl⟩) R251059
theorem R171143 : Reach 171143 := rs (se 1 (by rfl) ⟨128357, by rfl⟩) R256715
theorem R498977 : Reach 498977 := rs (se 2 (by rfl) ⟨187116, by rfl⟩) R374233
theorem R171323 : Reach 171323 := rs (se 1 (by rfl) ⟨128492, by rfl⟩) R256985
theorem R662843 : Reach 662843 := rs (se 1 (by rfl) ⟨497132, by rfl⟩) R994265
theorem R105787 : Reach 105787 := rs (se 1 (by rfl) ⟨79340, by rfl⟩) R158681
theorem R892295 : Reach 892295 := rs (se 1 (by rfl) ⟨669221, by rfl⟩) R1338443
theorem R171449 : Reach 171449 := rs (se 2 (by rfl) ⟨64293, by rfl⟩) R128587
theorem R499229 : Reach 499229 := rs (se 3 (by rfl) ⟨93605, by rfl⟩) R187211
theorem R171791 : Reach 171791 := rs (se 1 (by rfl) ⟨128843, by rfl⟩) R257687
theorem R171809 : Reach 171809 := rs (se 2 (by rfl) ⟨64428, by rfl⟩) R128857
theorem R172151 : Reach 172151 := rs (se 1 (by rfl) ⟨129113, by rfl⟩) R258227
theorem R205001 : Reach 205001 := rs (se 2 (by rfl) ⟨76875, by rfl⟩) R153751
theorem R1646837 : Reach 1646837 := rs (se 5 (by rfl) ⟨77195, by rfl⟩) R154391
theorem R172331 : Reach 172331 := rs (se 1 (by rfl) ⟨129248, by rfl⟩) R258497
theorem R172691 : Reach 172691 := rs (se 1 (by rfl) ⟨129518, by rfl⟩) R259037
theorem R172745 : Reach 172745 := rs (se 2 (by rfl) ⟨64779, by rfl⟩) R129559
theorem R205715 : Reach 205715 := rs (se 1 (by rfl) ⟨154286, by rfl⟩) R308573
theorem R107767 : Reach 107767 := rs (se 1 (by rfl) ⟨80825, by rfl⟩) R161651
theorem R75143 : Reach 75143 := rs (se 1 (by rfl) ⟨56357, by rfl⟩) R112715
theorem R173447 : Reach 173447 := rs (se 1 (by rfl) ⟨130085, by rfl⟩) R260171
theorem R75151 : Reach 75151 := rs (se 1 (by rfl) ⟨56363, by rfl⟩) R112727
theorem R75195 : Reach 75195 := rs (se 1 (by rfl) ⟨56396, by rfl⟩) R112793
theorem R75271 : Reach 75271 := rs (se 1 (by rfl) ⟨56453, by rfl⟩) R112907
theorem R75279 : Reach 75279 := rs (se 1 (by rfl) ⟨56459, by rfl⟩) R112919
theorem R75323 : Reach 75323 := rs (se 1 (by rfl) ⟨56492, by rfl⟩) R112985
theorem R173627 : Reach 173627 := rs (se 1 (by rfl) ⟨130220, by rfl⟩) R260441
theorem R1451621 : Reach 1451621 := rs (se 4 (by rfl) ⟨136089, by rfl⟩) R272179
theorem R75399 : Reach 75399 := rs (se 1 (by rfl) ⟨56549, by rfl⟩) R113099
theorem R75407 : Reach 75407 := rs (se 1 (by rfl) ⟨56555, by rfl⟩) R113111
theorem R173753 : Reach 173753 := rs (se 2 (by rfl) ⟨65157, by rfl⟩) R130315
theorem R75451 : Reach 75451 := rs (se 1 (by rfl) ⟨56588, by rfl⟩) R113177
theorem R534209 : Reach 534209 := rs (se 2 (by rfl) ⟨200328, by rfl⟩) R400657
theorem R75527 : Reach 75527 := rs (se 1 (by rfl) ⟨56645, by rfl⟩) R113291
theorem R75535 : Reach 75535 := rs (se 1 (by rfl) ⟨56651, by rfl⟩) R113303
theorem R206651 : Reach 206651 := rs (se 1 (by rfl) ⟨154988, by rfl⟩) R309977
theorem R75579 : Reach 75579 := rs (se 1 (by rfl) ⟨56684, by rfl⟩) R113369
theorem R75655 : Reach 75655 := rs (se 1 (by rfl) ⟨56741, by rfl⟩) R113483
theorem R436103 : Reach 436103 := rs (se 1 (by rfl) ⟨327077, by rfl⟩) R654155
theorem R75663 : Reach 75663 := rs (se 1 (by rfl) ⟨56747, by rfl⟩) R113495
theorem R75707 : Reach 75707 := rs (se 1 (by rfl) ⟨56780, by rfl⟩) R113561
theorem R75783 : Reach 75783 := rs (se 1 (by rfl) ⟨56837, by rfl⟩) R113675
theorem R75791 : Reach 75791 := rs (se 1 (by rfl) ⟨56843, by rfl⟩) R113687
theorem R174095 : Reach 174095 := rs (se 1 (by rfl) ⟨130571, by rfl⟩) R261143
theorem R174113 : Reach 174113 := rs (se 2 (by rfl) ⟨65292, by rfl⟩) R130585
theorem R108587 : Reach 108587 := rs (se 1 (by rfl) ⟨81440, by rfl⟩) R162881
theorem R75835 : Reach 75835 := rs (se 1 (by rfl) ⟨56876, by rfl⟩) R113753
theorem R75911 : Reach 75911 := rs (se 1 (by rfl) ⟨56933, by rfl⟩) R113867
theorem R75919 : Reach 75919 := rs (se 1 (by rfl) ⟨56939, by rfl⟩) R113879
theorem R75963 : Reach 75963 := rs (se 1 (by rfl) ⟨56972, by rfl⟩) R113945
theorem R272585 : Reach 272585 := rs (se 2 (by rfl) ⟨102219, by rfl⟩) R204439
theorem R272641 : Reach 272641 := rs (se 2 (by rfl) ⟨102240, by rfl⟩) R204481
theorem R76039 : Reach 76039 := rs (se 1 (by rfl) ⟨57029, by rfl⟩) R114059
theorem R76047 : Reach 76047 := rs (se 1 (by rfl) ⟨57035, by rfl⟩) R114071
theorem R141583 : Reach 141583 := rs (se 1 (by rfl) ⟨106187, by rfl⟩) R212375
theorem R76091 : Reach 76091 := rs (se 1 (by rfl) ⟨57068, by rfl⟩) R114137
theorem R174455 : Reach 174455 := rs (se 1 (by rfl) ⟨130841, by rfl⟩) R261683
theorem R76167 : Reach 76167 := rs (se 1 (by rfl) ⟨57125, by rfl⟩) R114251
theorem R76175 : Reach 76175 := rs (se 1 (by rfl) ⟨57131, by rfl⟩) R114263
theorem R174521 : Reach 174521 := rs (se 2 (by rfl) ⟨65445, by rfl⟩) R130891
theorem R76219 : Reach 76219 := rs (se 1 (by rfl) ⟨57164, by rfl⟩) R114329
theorem R76295 : Reach 76295 := rs (se 1 (by rfl) ⟨57221, by rfl⟩) R114443
theorem R76303 : Reach 76303 := rs (se 1 (by rfl) ⟨57227, by rfl⟩) R114455
theorem R174635 : Reach 174635 := rs (se 1 (by rfl) ⟨130976, by rfl⟩) R261953
theorem R76347 : Reach 76347 := rs (se 1 (by rfl) ⟨57260, by rfl⟩) R114521
theorem R895607 : Reach 895607 := rs (se 1 (by rfl) ⟨671705, by rfl⟩) R1343411
theorem R600695 : Reach 600695 := rs (se 1 (by rfl) ⟨450521, by rfl⟩) R901043
theorem R76423 : Reach 76423 := rs (se 1 (by rfl) ⟨57317, by rfl⟩) R114635
theorem R76431 : Reach 76431 := rs (se 1 (by rfl) ⟨57323, by rfl⟩) R114647
theorem R76475 : Reach 76475 := rs (se 1 (by rfl) ⟨57356, by rfl⟩) R114713
theorem R76551 : Reach 76551 := rs (se 1 (by rfl) ⟨57413, by rfl⟩) R114827
theorem R76559 : Reach 76559 := rs (se 1 (by rfl) ⟨57419, by rfl⟩) R114839
theorem R76603 : Reach 76603 := rs (se 1 (by rfl) ⟨57452, by rfl⟩) R114905
theorem R76679 : Reach 76679 := rs (se 1 (by rfl) ⟨57509, by rfl⟩) R115019
theorem R76687 : Reach 76687 := rs (se 1 (by rfl) ⟨57515, by rfl⟩) R115031
theorem R174995 : Reach 174995 := rs (se 1 (by rfl) ⟨131246, by rfl⟩) R262493
theorem R76731 : Reach 76731 := rs (se 1 (by rfl) ⟨57548, by rfl⟩) R115097
theorem R175049 : Reach 175049 := rs (se 2 (by rfl) ⟨65643, by rfl⟩) R131287
theorem R76807 : Reach 76807 := rs (se 1 (by rfl) ⟨57605, by rfl⟩) R115211
theorem R76815 : Reach 76815 := rs (se 1 (by rfl) ⟨57611, by rfl⟩) R115223
theorem R76859 : Reach 76859 := rs (se 1 (by rfl) ⟨57644, by rfl⟩) R115289
theorem R437309 : Reach 437309 := rs (se 3 (by rfl) ⟨81995, by rfl⟩) R163991
theorem R76935 : Reach 76935 := rs (se 1 (by rfl) ⟨57701, by rfl⟩) R115403
theorem R76943 : Reach 76943 := rs (se 1 (by rfl) ⟨57707, by rfl⟩) R115415
theorem R76987 : Reach 76987 := rs (se 1 (by rfl) ⟨57740, by rfl⟩) R115481
theorem R77063 : Reach 77063 := rs (se 1 (by rfl) ⟨57797, by rfl⟩) R115595
theorem R77071 : Reach 77071 := rs (se 1 (by rfl) ⟨57803, by rfl⟩) R115607
theorem R77115 : Reach 77115 := rs (se 1 (by rfl) ⟨57836, by rfl⟩) R115673
theorem R77191 : Reach 77191 := rs (se 1 (by rfl) ⟨57893, by rfl⟩) R115787
theorem R77199 : Reach 77199 := rs (se 1 (by rfl) ⟨57899, by rfl⟩) R115799
theorem R77243 : Reach 77243 := rs (se 1 (by rfl) ⟨57932, by rfl⟩) R115865
theorem R110011 : Reach 110011 := rs (se 1 (by rfl) ⟨82508, by rfl⟩) R165017
theorem R142793 : Reach 142793 := rs (se 2 (by rfl) ⟨53547, by rfl⟩) R107095
theorem R77319 : Reach 77319 := rs (se 1 (by rfl) ⟨57989, by rfl⟩) R115979
theorem R77327 : Reach 77327 := rs (se 1 (by rfl) ⟨57995, by rfl⟩) R115991
theorem R77371 : Reach 77371 := rs (se 1 (by rfl) ⟨58028, by rfl⟩) R116057
theorem R77447 : Reach 77447 := rs (se 1 (by rfl) ⟨58085, by rfl⟩) R116171
theorem R175751 : Reach 175751 := rs (se 1 (by rfl) ⟨131813, by rfl⟩) R263627
theorem R77455 : Reach 77455 := rs (se 1 (by rfl) ⟨58091, by rfl⟩) R116183
theorem R77499 : Reach 77499 := rs (se 1 (by rfl) ⟨58124, by rfl⟩) R116249
theorem R77575 : Reach 77575 := rs (se 1 (by rfl) ⟨58181, by rfl⟩) R116363
theorem R77583 : Reach 77583 := rs (se 1 (by rfl) ⟨58187, by rfl⟩) R116375
theorem R77627 : Reach 77627 := rs (se 1 (by rfl) ⟨58220, by rfl⟩) R116441
theorem R175931 : Reach 175931 := rs (se 1 (by rfl) ⟨131948, by rfl⟩) R263897
theorem R77703 : Reach 77703 := rs (se 1 (by rfl) ⟨58277, by rfl⟩) R116555
theorem R77711 : Reach 77711 := rs (se 1 (by rfl) ⟨58283, by rfl⟩) R116567
theorem R110521 : Reach 110521 := rs (se 2 (by rfl) ⟨41445, by rfl⟩) R82891
theorem R77755 : Reach 77755 := rs (se 1 (by rfl) ⟨58316, by rfl⟩) R116633
theorem R176057 : Reach 176057 := rs (se 2 (by rfl) ⟨66021, by rfl⟩) R132043
theorem R77831 : Reach 77831 := rs (se 1 (by rfl) ⟨58373, by rfl⟩) R116747
theorem R77839 : Reach 77839 := rs (se 1 (by rfl) ⟨58379, by rfl⟩) R116759
theorem R77883 : Reach 77883 := rs (se 1 (by rfl) ⟨58412, by rfl⟩) R116825
theorem R602245 : Reach 602245 := rs (se 4 (by rfl) ⟨56460, by rfl⟩) R112921
theorem R77959 : Reach 77959 := rs (se 1 (by rfl) ⟨58469, by rfl⟩) R116939
theorem R77967 : Reach 77967 := rs (se 1 (by rfl) ⟨58475, by rfl⟩) R116951
theorem R143507 : Reach 143507 := rs (se 1 (by rfl) ⟨107630, by rfl⟩) R215261
theorem R143545 : Reach 143545 := rs (se 2 (by rfl) ⟨53829, by rfl⟩) R107659
theorem R78011 : Reach 78011 := rs (se 1 (by rfl) ⟨58508, by rfl⟩) R117017
theorem R78087 : Reach 78087 := rs (se 1 (by rfl) ⟨58565, by rfl⟩) R117131
theorem R78095 : Reach 78095 := rs (se 1 (by rfl) ⟨58571, by rfl⟩) R117143
theorem R176399 : Reach 176399 := rs (se 1 (by rfl) ⟨132299, by rfl⟩) R264599
theorem R176417 : Reach 176417 := rs (se 2 (by rfl) ⟨66156, by rfl⟩) R132313
theorem R78139 : Reach 78139 := rs (se 1 (by rfl) ⟨58604, by rfl⟩) R117209
theorem R78215 : Reach 78215 := rs (se 1 (by rfl) ⟨58661, by rfl⟩) R117323
theorem R78223 : Reach 78223 := rs (se 1 (by rfl) ⟨58667, by rfl⟩) R117335
theorem R78267 : Reach 78267 := rs (se 1 (by rfl) ⟨58700, by rfl⟩) R117401
theorem R78343 : Reach 78343 := rs (se 1 (by rfl) ⟨58757, by rfl⟩) R117515
theorem R78351 : Reach 78351 := rs (se 1 (by rfl) ⟨58763, by rfl⟩) R117527
theorem R78395 : Reach 78395 := rs (se 1 (by rfl) ⟨58796, by rfl⟩) R117593
theorem R176759 : Reach 176759 := rs (se 1 (by rfl) ⟨132569, by rfl⟩) R265139
theorem R78471 : Reach 78471 := rs (se 1 (by rfl) ⟨58853, by rfl⟩) R117707
theorem R78479 : Reach 78479 := rs (se 1 (by rfl) ⟨58859, by rfl⟩) R117719
theorem R78523 : Reach 78523 := rs (se 1 (by rfl) ⟨58892, by rfl⟩) R117785
theorem R78599 : Reach 78599 := rs (se 1 (by rfl) ⟨58949, by rfl⟩) R117899
theorem R78607 : Reach 78607 := rs (se 1 (by rfl) ⟨58955, by rfl⟩) R117911
theorem R176939 : Reach 176939 := rs (se 1 (by rfl) ⟨132704, by rfl⟩) R265409
theorem R78651 : Reach 78651 := rs (se 1 (by rfl) ⟨58988, by rfl⟩) R117977
theorem R78727 : Reach 78727 := rs (se 1 (by rfl) ⟨59045, by rfl⟩) R118091
theorem R111503 : Reach 111503 := rs (se 1 (by rfl) ⟨83627, by rfl⟩) R167255
theorem R78735 : Reach 78735 := rs (se 1 (by rfl) ⟨59051, by rfl⟩) R118103
theorem R78779 : Reach 78779 := rs (se 1 (by rfl) ⟨59084, by rfl⟩) R118169
theorem R78855 : Reach 78855 := rs (se 1 (by rfl) ⟨59141, by rfl⟩) R118283
theorem R78863 : Reach 78863 := rs (se 1 (by rfl) ⟨59147, by rfl⟩) R118295
theorem R78907 : Reach 78907 := rs (se 1 (by rfl) ⟨59180, by rfl⟩) R118361
theorem R78983 : Reach 78983 := rs (se 1 (by rfl) ⟨59237, by rfl⟩) R118475
theorem R78991 : Reach 78991 := rs (se 1 (by rfl) ⟨59243, by rfl⟩) R118487
theorem R177299 : Reach 177299 := rs (se 1 (by rfl) ⟨132974, by rfl⟩) R265949
theorem R79035 : Reach 79035 := rs (se 1 (by rfl) ⟨59276, by rfl⟩) R118553
theorem R177353 : Reach 177353 := rs (se 2 (by rfl) ⟨66507, by rfl⟩) R133015
theorem R79111 : Reach 79111 := rs (se 1 (by rfl) ⟨59333, by rfl⟩) R118667
theorem R79119 : Reach 79119 := rs (se 1 (by rfl) ⟨59339, by rfl⟩) R118679
theorem R243091 : Reach 243091 := rs (se 1 (by rfl) ⟨182318, by rfl⟩) R364637
theorem R145081 : Reach 145081 := rs (se 2 (by rfl) ⟨54405, by rfl⟩) R108811
theorem R1226497 : Reach 1226497 := rs (se 2 (by rfl) ⟨459936, by rfl⟩) R919873
theorem R6731585 : Reach 6731585 := rs (se 2 (by rfl) ⟨2524344, by rfl⟩) R5048689
theorem R112585 : Reach 112585 := rs (se 2 (by rfl) ⟨42219, by rfl⟩) R84439
theorem R145451 : Reach 145451 := rs (se 1 (by rfl) ⟨109088, by rfl⟩) R218177
theorem R112697 : Reach 112697 := rs (se 2 (by rfl) ⟨42261, by rfl⟩) R84523
theorem R112775 : Reach 112775 := rs (se 1 (by rfl) ⟨84581, by rfl⟩) R169163
theorem R112811 : Reach 112811 := rs (se 1 (by rfl) ⟨84608, by rfl⟩) R169217
theorem R112841 : Reach 112841 := rs (se 2 (by rfl) ⟨42315, by rfl⟩) R84631
theorem R112955 : Reach 112955 := rs (se 1 (by rfl) ⟨84716, by rfl⟩) R169433
theorem R113015 : Reach 113015 := rs (se 1 (by rfl) ⟨84761, by rfl⟩) R169523
theorem R113039 : Reach 113039 := rs (se 1 (by rfl) ⟨84779, by rfl⟩) R169559
theorem R113081 : Reach 113081 := rs (se 2 (by rfl) ⟨42405, by rfl⟩) R84811
theorem R113159 : Reach 113159 := rs (se 1 (by rfl) ⟨84869, by rfl⟩) R169739
theorem R113195 : Reach 113195 := rs (se 1 (by rfl) ⟨84896, by rfl⟩) R169793
theorem R113225 : Reach 113225 := rs (se 2 (by rfl) ⟨42459, by rfl⟩) R84919
theorem R113339 : Reach 113339 := rs (se 1 (by rfl) ⟨85004, by rfl⟩) R170009
theorem R113399 : Reach 113399 := rs (se 1 (by rfl) ⟨85049, by rfl⟩) R170099
theorem R113423 : Reach 113423 := rs (se 1 (by rfl) ⟨85067, by rfl⟩) R170135
theorem R113465 : Reach 113465 := rs (se 2 (by rfl) ⟨42549, by rfl⟩) R85099
theorem R113543 : Reach 113543 := rs (se 1 (by rfl) ⟨85157, by rfl⟩) R170315
theorem R113579 : Reach 113579 := rs (se 1 (by rfl) ⟨85184, by rfl⟩) R170369
theorem R113609 : Reach 113609 := rs (se 2 (by rfl) ⟨42603, by rfl⟩) R85207
theorem R146377 : Reach 146377 := rs (se 2 (by rfl) ⟨54891, by rfl⟩) R109783
theorem R211997 : Reach 211997 := rs (se 3 (by rfl) ⟨39749, by rfl⟩) R79499
theorem R113723 : Reach 113723 := rs (se 1 (by rfl) ⟨85292, by rfl⟩) R170585
theorem R113783 : Reach 113783 := rs (se 1 (by rfl) ⟨85337, by rfl⟩) R170675
theorem R113807 : Reach 113807 := rs (se 1 (by rfl) ⟨85355, by rfl⟩) R170711
theorem R113849 : Reach 113849 := rs (se 2 (by rfl) ⟨42693, by rfl⟩) R85387
theorem R244937 : Reach 244937 := rs (se 2 (by rfl) ⟨91851, by rfl⟩) R183703
theorem R113927 : Reach 113927 := rs (se 1 (by rfl) ⟨85445, by rfl⟩) R170891
theorem R81167 : Reach 81167 := rs (se 1 (by rfl) ⟨60875, by rfl⟩) R121751
theorem R113963 : Reach 113963 := rs (se 1 (by rfl) ⟨85472, by rfl⟩) R170945
theorem R113993 : Reach 113993 := rs (se 2 (by rfl) ⟨42747, by rfl⟩) R85495
theorem R114107 : Reach 114107 := rs (se 1 (by rfl) ⟨85580, by rfl⟩) R171161
theorem R376285 : Reach 376285 := rs (se 3 (by rfl) ⟨70553, by rfl⟩) R141107
theorem R114167 : Reach 114167 := rs (se 1 (by rfl) ⟨85625, by rfl⟩) R171251
theorem R81415 : Reach 81415 := rs (se 1 (by rfl) ⟨61061, by rfl⟩) R122123
theorem R114191 : Reach 114191 := rs (se 1 (by rfl) ⟨85643, by rfl⟩) R171287
theorem R114233 : Reach 114233 := rs (se 2 (by rfl) ⟨42837, by rfl⟩) R85675
theorem R114311 : Reach 114311 := rs (se 1 (by rfl) ⟨85733, by rfl⟩) R171467
theorem R147091 : Reach 147091 := rs (se 1 (by rfl) ⟨110318, by rfl⟩) R220637
theorem R114347 : Reach 114347 := rs (se 1 (by rfl) ⟨85760, by rfl⟩) R171521
theorem R114377 : Reach 114377 := rs (se 2 (by rfl) ⟨42891, by rfl⟩) R85783
theorem R114491 : Reach 114491 := rs (se 1 (by rfl) ⟨85868, by rfl⟩) R171737
theorem R114551 : Reach 114551 := rs (se 1 (by rfl) ⟨85913, by rfl⟩) R171827
theorem R278407 : Reach 278407 := rs (se 1 (by rfl) ⟨208805, by rfl⟩) R417611
theorem R114575 : Reach 114575 := rs (se 1 (by rfl) ⟨85931, by rfl⟩) R171863
theorem R638873 : Reach 638873 := rs (se 2 (by rfl) ⟨239577, by rfl⟩) R479155
theorem R671651 : Reach 671651 := rs (se 1 (by rfl) ⟨503738, by rfl⟩) R1007477
theorem R114617 : Reach 114617 := rs (se 2 (by rfl) ⟨42981, by rfl⟩) R85963
theorem R114695 : Reach 114695 := rs (se 1 (by rfl) ⟨86021, by rfl⟩) R172043
theorem R114731 : Reach 114731 := rs (se 1 (by rfl) ⟨86048, by rfl⟩) R172097
theorem R114761 : Reach 114761 := rs (se 2 (by rfl) ⟨43035, by rfl⟩) R86071
theorem R114875 : Reach 114875 := rs (se 1 (by rfl) ⟨86156, by rfl⟩) R172313
theorem R114935 : Reach 114935 := rs (se 1 (by rfl) ⟨86201, by rfl⟩) R172403
theorem R114959 : Reach 114959 := rs (se 1 (by rfl) ⟨86219, by rfl⟩) R172439
theorem R213263 : Reach 213263 := rs (se 1 (by rfl) ⟨159947, by rfl⟩) R319895
theorem R115001 : Reach 115001 := rs (se 2 (by rfl) ⟨43125, by rfl⟩) R86251
theorem R82235 : Reach 82235 := rs (se 1 (by rfl) ⟨61676, by rfl⟩) R123353
theorem R115079 : Reach 115079 := rs (se 1 (by rfl) ⟨86309, by rfl⟩) R172619
theorem R115115 : Reach 115115 := rs (se 1 (by rfl) ⟨86336, by rfl⟩) R172673
theorem R115145 : Reach 115145 := rs (se 2 (by rfl) ⟨43179, by rfl⟩) R86359
theorem R4047317 : Reach 4047317 := rs (se 7 (by rfl) ⟨47429, by rfl⟩) R94859
theorem R672299 : Reach 672299 := rs (se 1 (by rfl) ⟨504224, by rfl⟩) R1008449
theorem R115259 : Reach 115259 := rs (se 1 (by rfl) ⟨86444, by rfl⟩) R172889
theorem R213563 : Reach 213563 := rs (se 1 (by rfl) ⟨160172, by rfl⟩) R320345
theorem R115319 : Reach 115319 := rs (se 1 (by rfl) ⟨86489, by rfl⟩) R172979
theorem R115343 : Reach 115343 := rs (se 1 (by rfl) ⟨86507, by rfl⟩) R173015
theorem R115385 : Reach 115385 := rs (se 2 (by rfl) ⟨43269, by rfl⟩) R86539
theorem R148169 : Reach 148169 := rs (se 2 (by rfl) ⟨55563, by rfl⟩) R111127
theorem R115463 : Reach 115463 := rs (se 1 (by rfl) ⟨86597, by rfl⟩) R173195
theorem R115499 : Reach 115499 := rs (se 1 (by rfl) ⟨86624, by rfl⟩) R173249
theorem R115529 : Reach 115529 := rs (se 2 (by rfl) ⟨43323, by rfl⟩) R86647
theorem R115643 : Reach 115643 := rs (se 1 (by rfl) ⟨86732, by rfl⟩) R173465
theorem R3195875 : Reach 3195875 := rs (se 1 (by rfl) ⟨2396906, by rfl⟩) R4793813
theorem R115703 : Reach 115703 := rs (se 1 (by rfl) ⟨86777, by rfl⟩) R173555
theorem R115727 : Reach 115727 := rs (se 1 (by rfl) ⟨86795, by rfl⟩) R173591
theorem R115769 : Reach 115769 := rs (se 2 (by rfl) ⟨43413, by rfl⟩) R86827
theorem R115847 : Reach 115847 := rs (se 1 (by rfl) ⟨86885, by rfl⟩) R173771
theorem R115883 : Reach 115883 := rs (se 1 (by rfl) ⟨86912, by rfl⟩) R173825
theorem R115913 : Reach 115913 := rs (se 2 (by rfl) ⟨43467, by rfl⟩) R86935
theorem R640237 : Reach 640237 := rs (se 3 (by rfl) ⟨120044, by rfl⟩) R240089
theorem R116027 : Reach 116027 := rs (se 1 (by rfl) ⟨87020, by rfl⟩) R174041
theorem R116087 : Reach 116087 := rs (se 1 (by rfl) ⟨87065, by rfl⟩) R174131
theorem R116111 : Reach 116111 := rs (se 1 (by rfl) ⟨87083, by rfl⟩) R174167
theorem R116153 : Reach 116153 := rs (se 2 (by rfl) ⟨43557, by rfl⟩) R87115
theorem R116231 : Reach 116231 := rs (se 1 (by rfl) ⟨87173, by rfl⟩) R174347
theorem R116267 : Reach 116267 := rs (se 1 (by rfl) ⟨87200, by rfl⟩) R174401
theorem R149035 : Reach 149035 := rs (se 1 (by rfl) ⟨111776, by rfl⟩) R223553
theorem R214589 : Reach 214589 := rs (se 3 (by rfl) ⟨40235, by rfl⟩) R80471
theorem R116297 : Reach 116297 := rs (se 2 (by rfl) ⟨43611, by rfl⟩) R87223
theorem R542285 : Reach 542285 := rs (se 3 (by rfl) ⟨101678, by rfl⟩) R203357
theorem R149111 : Reach 149111 := rs (se 1 (by rfl) ⟨111833, by rfl⟩) R223667
theorem R116411 : Reach 116411 := rs (se 1 (by rfl) ⟨87308, by rfl⟩) R174617
theorem R116471 : Reach 116471 := rs (se 1 (by rfl) ⟨87353, by rfl⟩) R174707
theorem R116495 : Reach 116495 := rs (se 1 (by rfl) ⟨87371, by rfl⟩) R174743
theorem R542513 : Reach 542513 := rs (se 2 (by rfl) ⟨203442, by rfl⟩) R406885
theorem R116537 : Reach 116537 := rs (se 2 (by rfl) ⟨43701, by rfl⟩) R87403
theorem R214919 : Reach 214919 := rs (se 1 (by rfl) ⟨161189, by rfl⟩) R322379
theorem R444295 : Reach 444295 := rs (se 1 (by rfl) ⟨333221, by rfl⟩) R666443
theorem R116615 : Reach 116615 := rs (se 1 (by rfl) ⟨87461, by rfl⟩) R174923
theorem R378769 : Reach 378769 := rs (se 2 (by rfl) ⟨142038, by rfl⟩) R284077
theorem R116651 : Reach 116651 := rs (se 1 (by rfl) ⟨87488, by rfl⟩) R174977
theorem R116681 : Reach 116681 := rs (se 2 (by rfl) ⟨43755, by rfl⟩) R87511
theorem R411601 : Reach 411601 := rs (se 2 (by rfl) ⟨154350, by rfl⟩) R308701
theorem R116795 : Reach 116795 := rs (se 1 (by rfl) ⟨87596, by rfl⟩) R175193
theorem R182359 : Reach 182359 := rs (se 1 (by rfl) ⟨136769, by rfl⟩) R273539
theorem R116855 : Reach 116855 := rs (se 1 (by rfl) ⟨87641, by rfl⟩) R175283
theorem R116879 : Reach 116879 := rs (se 1 (by rfl) ⟨87659, by rfl⟩) R175319
theorem R116921 : Reach 116921 := rs (se 2 (by rfl) ⟨43845, by rfl⟩) R87691
theorem R1755377 : Reach 1755377 := rs (se 2 (by rfl) ⟨658266, by rfl⟩) R1316533
theorem R116999 : Reach 116999 := rs (se 1 (by rfl) ⟨87749, by rfl⟩) R175499
theorem R117035 : Reach 117035 := rs (se 1 (by rfl) ⟨87776, by rfl⟩) R175553
theorem R117065 : Reach 117065 := rs (se 2 (by rfl) ⟨43899, by rfl⟩) R87799
theorem R248179 : Reach 248179 := rs (se 1 (by rfl) ⟨186134, by rfl⟩) R372269
theorem R182675 : Reach 182675 := rs (se 1 (by rfl) ⟨137006, by rfl⟩) R274013
theorem R117179 : Reach 117179 := rs (se 1 (by rfl) ⟨87884, by rfl⟩) R175769
theorem R117239 : Reach 117239 := rs (se 1 (by rfl) ⟨87929, by rfl⟩) R175859
theorem R608771 : Reach 608771 := rs (se 1 (by rfl) ⟨456578, by rfl⟩) R913157
theorem R117263 : Reach 117263 := rs (se 1 (by rfl) ⟨87947, by rfl⟩) R175895
theorem R117305 : Reach 117305 := rs (se 2 (by rfl) ⟨43989, by rfl⟩) R87979
theorem R117383 : Reach 117383 := rs (se 1 (by rfl) ⟨88037, by rfl⟩) R176075
theorem R117419 : Reach 117419 := rs (se 1 (by rfl) ⟨88064, by rfl⟩) R176129
theorem R84667 : Reach 84667 := rs (se 1 (by rfl) ⟨63500, by rfl⟩) R127001
theorem R117449 : Reach 117449 := rs (se 2 (by rfl) ⟨44043, by rfl⟩) R88087
theorem R117563 : Reach 117563 := rs (se 1 (by rfl) ⟨88172, by rfl⟩) R176345
theorem R117623 : Reach 117623 := rs (se 1 (by rfl) ⟨88217, by rfl⟩) R176435
theorem R117647 : Reach 117647 := rs (se 1 (by rfl) ⟨88235, by rfl⟩) R176471
theorem R117689 : Reach 117689 := rs (se 2 (by rfl) ⟨44133, by rfl⟩) R88267
theorem R117767 : Reach 117767 := rs (se 1 (by rfl) ⟨88325, by rfl⟩) R176651
theorem R117803 : Reach 117803 := rs (se 1 (by rfl) ⟨88352, by rfl⟩) R176705
theorem R805949 : Reach 805949 := rs (se 3 (by rfl) ⟨151115, by rfl⟩) R302231
theorem R117833 : Reach 117833 := rs (se 2 (by rfl) ⟨44187, by rfl⟩) R88375
theorem R85135 : Reach 85135 := rs (se 1 (by rfl) ⟨63851, by rfl⟩) R127703
theorem R117947 : Reach 117947 := rs (se 1 (by rfl) ⟨88460, by rfl⟩) R176921
theorem R118007 : Reach 118007 := rs (se 1 (by rfl) ⟨88505, by rfl⟩) R177011
theorem R118031 : Reach 118031 := rs (se 1 (by rfl) ⟨88523, by rfl⟩) R177047
theorem R118073 : Reach 118073 := rs (se 2 (by rfl) ⟨44277, by rfl⟩) R88555
theorem R118151 : Reach 118151 := rs (se 1 (by rfl) ⟨88613, by rfl⟩) R177227
theorem R118187 : Reach 118187 := rs (se 1 (by rfl) ⟨88640, by rfl⟩) R177281
theorem R413113 : Reach 413113 := rs (se 2 (by rfl) ⟨154917, by rfl⟩) R309835
theorem R118217 : Reach 118217 := rs (se 2 (by rfl) ⟨44331, by rfl⟩) R88663
theorem R151055 : Reach 151055 := rs (se 1 (by rfl) ⟨113291, by rfl⟩) R226583
theorem R118331 : Reach 118331 := rs (se 1 (by rfl) ⟨88748, by rfl⟩) R177497
theorem R216695 : Reach 216695 := rs (se 1 (by rfl) ⟨162521, by rfl⟩) R325043
theorem R118391 : Reach 118391 := rs (se 1 (by rfl) ⟨88793, by rfl⟩) R177587
theorem R85639 : Reach 85639 := rs (se 1 (by rfl) ⟨64229, by rfl⟩) R128459
theorem R118415 : Reach 118415 := rs (se 1 (by rfl) ⟨88811, by rfl⟩) R177623
theorem R118457 : Reach 118457 := rs (se 2 (by rfl) ⟨44421, by rfl⟩) R88843
theorem R118535 : Reach 118535 := rs (se 1 (by rfl) ⟨88901, by rfl⟩) R177803
theorem R118571 : Reach 118571 := rs (se 1 (by rfl) ⟨88928, by rfl⟩) R177857
theorem R85819 : Reach 85819 := rs (se 1 (by rfl) ⟨64364, by rfl⟩) R128729
theorem R118601 : Reach 118601 := rs (se 2 (by rfl) ⟨44475, by rfl⟩) R88951
theorem R282503 : Reach 282503 := rs (se 1 (by rfl) ⟨211877, by rfl⟩) R423755
theorem R381185 : Reach 381185 := rs (se 2 (by rfl) ⟨142944, by rfl⟩) R285889
theorem R86287 : Reach 86287 := rs (se 1 (by rfl) ⟨64715, by rfl⟩) R129431
theorem R807353 : Reach 807353 := rs (se 2 (by rfl) ⟨302757, by rfl⟩) R605515
theorem R217687 : Reach 217687 := rs (se 1 (by rfl) ⟨163265, by rfl⟩) R326531
theorem R86791 : Reach 86791 := rs (se 1 (by rfl) ⟨65093, by rfl⟩) R130187
theorem R414497 : Reach 414497 := rs (se 2 (by rfl) ⟨155436, by rfl⟩) R310873
theorem R86971 : Reach 86971 := rs (se 1 (by rfl) ⟨65228, by rfl⟩) R130457
theorem R381995 : Reach 381995 := rs (se 1 (by rfl) ⟨286496, by rfl⟩) R572993
theorem R87439 : Reach 87439 := rs (se 1 (by rfl) ⟨65579, by rfl⟩) R131159
theorem R2020787 : Reach 2020787 := rs (se 1 (by rfl) ⟨1515590, by rfl⟩) R3031181
theorem R120521 : Reach 120521 := rs (se 2 (by rfl) ⟨45195, by rfl⟩) R90391
theorem R87943 : Reach 87943 := rs (se 1 (by rfl) ⟨65957, by rfl⟩) R131915
theorem R415691 : Reach 415691 := rs (se 1 (by rfl) ⟨311768, by rfl⟩) R623537
theorem R219179 : Reach 219179 := rs (se 1 (by rfl) ⟨164384, by rfl⟩) R328769
theorem R88123 : Reach 88123 := rs (se 1 (by rfl) ⟨66092, by rfl⟩) R132185
theorem R383291 : Reach 383291 := rs (se 1 (by rfl) ⟨287468, by rfl⟩) R574937
theorem R514451 : Reach 514451 := rs (se 1 (by rfl) ⟨385838, by rfl⟩) R771677
theorem R383453 : Reach 383453 := rs (se 3 (by rfl) ⟨71897, by rfl⟩) R143795
theorem R88591 : Reach 88591 := rs (se 1 (by rfl) ⟨66443, by rfl⟩) R132887
theorem R449225 : Reach 449225 := rs (se 2 (by rfl) ⟨168459, by rfl⟩) R336919
theorem R383777 : Reach 383777 := rs (se 2 (by rfl) ⟨143916, by rfl⟩) R287833
theorem R2579363 : Reach 2579363 := rs (se 1 (by rfl) ⟨1934522, by rfl⟩) R3869045
theorem R89095 : Reach 89095 := rs (se 1 (by rfl) ⟨66821, by rfl⟩) R133643
theorem R285707 : Reach 285707 := rs (se 1 (by rfl) ⟨214280, by rfl⟩) R428561
theorem R187451 : Reach 187451 := rs (se 1 (by rfl) ⟨140588, by rfl⟩) R281177
theorem R220295 : Reach 220295 := rs (se 1 (by rfl) ⟨165221, by rfl⟩) R330443
theorem R351469 : Reach 351469 := rs (se 3 (by rfl) ⟨65900, by rfl⟩) R131801
theorem R220477 : Reach 220477 := rs (se 3 (by rfl) ⟨41339, by rfl⟩) R82679
theorem R155081 : Reach 155081 := rs (se 2 (by rfl) ⟨58155, by rfl⟩) R116311
theorem R745037 : Reach 745037 := rs (se 3 (by rfl) ⟨139694, by rfl⟩) R279389
theorem R220819 : Reach 220819 := rs (se 1 (by rfl) ⟨165614, by rfl⟩) R331229
theorem R319177 : Reach 319177 := rs (se 2 (by rfl) ⟨119691, by rfl⟩) R239383
theorem R384749 : Reach 384749 := rs (se 3 (by rfl) ⟨72140, by rfl⟩) R144281
theorem R1335041 : Reach 1335041 := rs (se 2 (by rfl) ⟨500640, by rfl⟩) R1001281
theorem R286649 : Reach 286649 := rs (se 2 (by rfl) ⟨107493, by rfl⟩) R214987
theorem R90119 : Reach 90119 := rs (se 1 (by rfl) ⟨67589, by rfl⟩) R135179
theorem R942353 : Reach 942353 := rs (se 2 (by rfl) ⟨353382, by rfl⟩) R706765
theorem R549179 : Reach 549179 := rs (se 1 (by rfl) ⟨411884, by rfl⟩) R823769
theorem R254393 : Reach 254393 := rs (se 2 (by rfl) ⟨95397, by rfl⟩) R190795
theorem R516611 : Reach 516611 := rs (se 1 (by rfl) ⟨387458, by rfl⟩) R774917
theorem R221707 : Reach 221707 := rs (se 1 (by rfl) ⟨166280, by rfl⟩) R332561
theorem R385559 : Reach 385559 := rs (se 1 (by rfl) ⟨289169, by rfl⟩) R578339
theorem R1663523 : Reach 1663523 := rs (se 1 (by rfl) ⟨1247642, by rfl⟩) R2495285
theorem R222209 : Reach 222209 := rs (se 2 (by rfl) ⟨83328, by rfl⟩) R166657
theorem R254987 : Reach 254987 := rs (se 1 (by rfl) ⟨191240, by rfl⟩) R382481
theorem R255095 : Reach 255095 := rs (se 1 (by rfl) ⟨191321, by rfl⟩) R382643
theorem R222551 : Reach 222551 := rs (se 1 (by rfl) ⟨166913, by rfl⟩) R333827
theorem R255689 : Reach 255689 := rs (se 2 (by rfl) ⟨95883, by rfl⟩) R191767
theorem R419843 : Reach 419843 := rs (se 1 (by rfl) ⟨314882, by rfl⟩) R629765
theorem R2189429 : Reach 2189429 := rs (se 5 (by rfl) ⟨102629, by rfl⟩) R205259
theorem R190583 : Reach 190583 := rs (se 1 (by rfl) ⟨142937, by rfl⟩) R285875
theorem R256391 : Reach 256391 := rs (se 1 (by rfl) ⟨192293, by rfl⟩) R384587
theorem R289291 : Reach 289291 := rs (se 1 (by rfl) ⟨216968, by rfl⟩) R433937
theorem R748061 : Reach 748061 := rs (se 3 (by rfl) ⟨140261, by rfl⟩) R280523
theorem R1108673 : Reach 1108673 := rs (se 2 (by rfl) ⟨415752, by rfl⟩) R831505
theorem R256769 : Reach 256769 := rs (se 2 (by rfl) ⟨96288, by rfl⟩) R192577
theorem R256801 : Reach 256801 := rs (se 2 (by rfl) ⟨96300, by rfl⟩) R192601
theorem R551717 : Reach 551717 := rs (se 4 (by rfl) ⟨51723, by rfl⟩) R103447
theorem R289595 : Reach 289595 := rs (se 1 (by rfl) ⟨217196, by rfl⟩) R434393
theorem R486233 : Reach 486233 := rs (se 2 (by rfl) ⟨182337, by rfl⟩) R364675
theorem R257053 : Reach 257053 := rs (se 3 (by rfl) ⟨48197, by rfl⟩) R96395
theorem R224441 : Reach 224441 := rs (se 2 (by rfl) ⟨84165, by rfl⟩) R168331
theorem R290081 : Reach 290081 := rs (se 2 (by rfl) ⟨108780, by rfl⟩) R217561
theorem R1240379 : Reach 1240379 := rs (se 1 (by rfl) ⟨930284, by rfl⟩) R1860569
theorem R191879 : Reach 191879 := rs (se 1 (by rfl) ⟨143909, by rfl⟩) R287819
theorem R191929 : Reach 191929 := rs (se 2 (by rfl) ⟨71973, by rfl⟩) R143947
theorem R224783 : Reach 224783 := rs (se 1 (by rfl) ⟨168587, by rfl⟩) R337175
theorem R126479 : Reach 126479 := rs (se 1 (by rfl) ⟨94859, by rfl⟩) R189719
theorem R388637 : Reach 388637 := rs (se 3 (by rfl) ⟨72869, by rfl⟩) R145739
theorem R257579 : Reach 257579 := rs (se 1 (by rfl) ⟨193184, by rfl⟩) R386369
theorem R552491 : Reach 552491 := rs (se 1 (by rfl) ⟨414368, by rfl⟩) R828737
theorem R2420375 : Reach 2420375 := rs (se 1 (by rfl) ⟨1815281, by rfl⟩) R3630563
theorem R1699505 : Reach 1699505 := rs (se 2 (by rfl) ⟨637314, by rfl⟩) R1274629
theorem R126839 : Reach 126839 := rs (se 1 (by rfl) ⟨95129, by rfl⟩) R190259
theorem R389123 : Reach 389123 := rs (se 1 (by rfl) ⟨291842, by rfl⟩) R583685
theorem R749573 : Reach 749573 := rs (se 4 (by rfl) ⟨70272, by rfl⟩) R140545
theorem R192527 : Reach 192527 := rs (se 1 (by rfl) ⟨144395, by rfl⟩) R288791
theorem R291053 : Reach 291053 := rs (se 3 (by rfl) ⟨54572, by rfl⟩) R109145
theorem R127291 : Reach 127291 := rs (se 1 (by rfl) ⟨95468, by rfl⟩) R190937
theorem R127433 : Reach 127433 := rs (se 2 (by rfl) ⟨47787, by rfl⟩) R95575
theorem R94907 : Reach 94907 := rs (se 1 (by rfl) ⟨71180, by rfl⟩) R142361
theorem R193225 : Reach 193225 := rs (se 2 (by rfl) ⟨72459, by rfl⟩) R144919
theorem R848677 : Reach 848677 := rs (se 4 (by rfl) ⟨79563, by rfl⟩) R159127
theorem R258875 : Reach 258875 := rs (se 1 (by rfl) ⟨194156, by rfl⟩) R388313
theorem R193367 : Reach 193367 := rs (se 1 (by rfl) ⟨145025, by rfl⟩) R290051
theorem R553817 : Reach 553817 := rs (se 2 (by rfl) ⟨207681, by rfl⟩) R415363
theorem R914327 : Reach 914327 := rs (se 1 (by rfl) ⟨685745, by rfl⟩) R1371491
theorem R390167 : Reach 390167 := rs (se 1 (by rfl) ⟨292625, by rfl⟩) R585251
theorem R128135 : Reach 128135 := rs (se 1 (by rfl) ⟨96101, by rfl⟩) R192203
theorem R259361 : Reach 259361 := rs (se 2 (by rfl) ⟨97260, by rfl⟩) R194521
theorem R128299 : Reach 128299 := rs (se 1 (by rfl) ⟨96224, by rfl⟩) R192449
theorem R1209659 : Reach 1209659 := rs (se 1 (by rfl) ⟨907244, by rfl⟩) R1814489
theorem R390743 : Reach 390743 := rs (se 1 (by rfl) ⟨293057, by rfl⟩) R586115
theorem R194183 : Reach 194183 := rs (se 1 (by rfl) ⟨145637, by rfl⟩) R291275
theorem R128783 : Reach 128783 := rs (se 1 (by rfl) ⟨96587, by rfl⟩) R193175
theorem R653093 : Reach 653093 := rs (se 4 (by rfl) ⟨61227, by rfl⟩) R122455
theorem R259955 : Reach 259955 := rs (se 1 (by rfl) ⟨194966, by rfl⟩) R389933
theorem R391229 : Reach 391229 := rs (se 3 (by rfl) ⟨73355, by rfl⟩) R146711
theorem R161993 : Reach 161993 := rs (se 2 (by rfl) ⟨60747, by rfl⟩) R121495
theorem R129323 : Reach 129323 := rs (se 1 (by rfl) ⟨96992, by rfl⟩) R193985
theorem R293179 : Reach 293179 := rs (se 1 (by rfl) ⟨219884, by rfl⟩) R439769
theorem R653777 : Reach 653777 := rs (se 2 (by rfl) ⟨245166, by rfl⟩) R490333
theorem R129721 : Reach 129721 := rs (se 2 (by rfl) ⟨48645, by rfl⟩) R97291
theorem R588545 : Reach 588545 := rs (se 2 (by rfl) ⟨220704, by rfl⟩) R441409
theorem R293665 : Reach 293665 := rs (se 2 (by rfl) ⟨110124, by rfl⟩) R220249
theorem R195443 : Reach 195443 := rs (se 1 (by rfl) ⟨146582, by rfl⟩) R293165
theorem R97195 : Reach 97195 := rs (se 1 (by rfl) ⟨72896, by rfl⟩) R145793
theorem R228413 : Reach 228413 := rs (se 3 (by rfl) ⟨42827, by rfl⟩) R85655
theorem R720161 : Reach 720161 := rs (se 2 (by rfl) ⟨270060, by rfl⟩) R540121
theorem R130423 : Reach 130423 := rs (se 1 (by rfl) ⟨97817, by rfl⟩) R195635
theorem R195959 : Reach 195959 := rs (se 1 (by rfl) ⟨146969, by rfl⟩) R293939
theorem R130439 : Reach 130439 := rs (se 1 (by rfl) ⟨97829, by rfl⟩) R195659
theorem R130619 : Reach 130619 := rs (se 1 (by rfl) ⟨97964, by rfl⟩) R195929
theorem R720485 : Reach 720485 := rs (se 4 (by rfl) ⟨67545, by rfl⟩) R135091
theorem R294637 : Reach 294637 := rs (se 3 (by rfl) ⟨55244, by rfl⟩) R110489
theorem R393011 : Reach 393011 := rs (se 1 (by rfl) ⟨294758, by rfl⟩) R589517
theorem R98167 : Reach 98167 := rs (se 1 (by rfl) ⟨73625, by rfl⟩) R147251
theorem R131017 : Reach 131017 := rs (se 2 (by rfl) ⟨49131, by rfl⟩) R98263
theorem R196627 : Reach 196627 := rs (se 1 (by rfl) ⟨147470, by rfl⟩) R294941
theorem R262223 : Reach 262223 := rs (se 1 (by rfl) ⟨196667, by rfl⟩) R393335
theorem R131321 : Reach 131321 := rs (se 2 (by rfl) ⟨49245, by rfl⟩) R98491
theorem R131503 : Reach 131503 := rs (se 1 (by rfl) ⟨98627, by rfl⟩) R197255
theorem R262601 : Reach 262601 := rs (se 2 (by rfl) ⟨98475, by rfl⟩) R196951
theorem R131591 : Reach 131591 := rs (se 1 (by rfl) ⟨98693, by rfl⟩) R197387
theorem R2130583 : Reach 2130583 := rs (se 1 (by rfl) ⟨1597937, by rfl⟩) R3195875
theorem R295609 : Reach 295609 := rs (se 2 (by rfl) ⟨110853, by rfl⟩) R221707
theorem R3211973 : Reach 3211973 := rs (se 4 (by rfl) ⟨301122, by rfl⟩) R602245
theorem R459475 : Reach 459475 := rs (se 1 (by rfl) ⟨344606, by rfl⟩) R689213
theorem R262871 : Reach 262871 := rs (se 1 (by rfl) ⟨197153, by rfl⟩) R394307
theorem R131935 : Reach 131935 := rs (se 1 (by rfl) ⟨98951, by rfl⟩) R197903
theorem R263087 : Reach 263087 := rs (se 1 (by rfl) ⟨197315, by rfl⟩) R394631
theorem R132023 : Reach 132023 := rs (se 1 (by rfl) ⟨99017, by rfl⟩) R198035
theorem R361523 : Reach 361523 := rs (se 1 (by rfl) ⟨271142, by rfl⟩) R542285
theorem R197711 : Reach 197711 := rs (se 1 (by rfl) ⟨148283, by rfl⟩) R296567
theorem R99407 : Reach 99407 := rs (se 1 (by rfl) ⟨74555, by rfl⟩) R149111
theorem R361675 : Reach 361675 := rs (se 1 (by rfl) ⟨271256, by rfl⟩) R542513
theorem R4326857 : Reach 4326857 := rs (se 2 (by rfl) ⟨1622571, by rfl⟩) R3245143
theorem R132617 : Reach 132617 := rs (se 2 (by rfl) ⟨49731, by rfl⟩) R99463
theorem R853649 : Reach 853649 := rs (se 2 (by rfl) ⟨320118, by rfl⟩) R640237
theorem R132779 : Reach 132779 := rs (se 1 (by rfl) ⟨99584, by rfl⟩) R199169
theorem R198359 : Reach 198359 := rs (se 1 (by rfl) ⟨148769, by rfl⟩) R297539
theorem R395117 : Reach 395117 := rs (se 3 (by rfl) ⟨74084, by rfl⟩) R148169
theorem R395279 : Reach 395279 := rs (se 1 (by rfl) ⟨296459, by rfl⟩) R592919
theorem R198713 : Reach 198713 := rs (se 2 (by rfl) ⟨74517, by rfl⟩) R149035
theorem R133177 : Reach 133177 := rs (se 2 (by rfl) ⟨49941, by rfl⟩) R99883
theorem R133319 : Reach 133319 := rs (se 1 (by rfl) ⟨99989, by rfl⟩) R199979
theorem R100703 : Reach 100703 := rs (se 1 (by rfl) ⟨75527, by rfl⟩) R151055
theorem R133481 : Reach 133481 := rs (se 2 (by rfl) ⟨50055, by rfl⟩) R100111
theorem R297341 : Reach 297341 := rs (se 3 (by rfl) ⟨55751, by rfl⟩) R111503
theorem R592393 : Reach 592393 := rs (se 2 (by rfl) ⟨222147, by rfl⟩) R444295
theorem R363521 : Reach 363521 := rs (se 2 (by rfl) ⟨136320, by rfl⟩) R272641
theorem R330905 : Reach 330905 := rs (se 2 (by rfl) ⟨124089, by rfl⟩) R248179
theorem R265463 : Reach 265463 := rs (se 1 (by rfl) ⟨199097, by rfl⟩) R398195
theorem R265787 : Reach 265787 := rs (se 1 (by rfl) ⟨199340, by rfl⟩) R398681
theorem R1347191 : Reach 1347191 := rs (se 1 (by rfl) ⟨1010393, by rfl⟩) R2020787
theorem R265943 : Reach 265943 := rs (se 1 (by rfl) ⟨199457, by rfl⟩) R398915
theorem R1314593 : Reach 1314593 := rs (se 2 (by rfl) ⟨492972, by rfl⟩) R985945
theorem R266057 : Reach 266057 := rs (se 2 (by rfl) ⟨99771, by rfl⟩) R199543
theorem R299483 : Reach 299483 := rs (se 1 (by rfl) ⟨224612, by rfl⟩) R449225
theorem R398033 : Reach 398033 := rs (se 2 (by rfl) ⟨149262, by rfl⟩) R298525
theorem R332651 : Reach 332651 := rs (se 1 (by rfl) ⟨249488, by rfl⟩) R498977
theorem R594863 : Reach 594863 := rs (se 1 (by rfl) ⟨446147, by rfl⟩) R892295
theorem R332819 : Reach 332819 := rs (se 1 (by rfl) ⟨249614, by rfl⟩) R499229
theorem R496691 : Reach 496691 := rs (se 1 (by rfl) ⟨372518, by rfl⟩) R745037
theorem R890027 : Reach 890027 := rs (se 1 (by rfl) ⟨667520, by rfl⟩) R1335041
theorem R136667 : Reach 136667 := rs (se 1 (by rfl) ⟨102500, by rfl⟩) R205001
theorem R628235 : Reach 628235 := rs (se 1 (by rfl) ⟨471176, by rfl⟩) R942353
theorem R366119 : Reach 366119 := rs (se 1 (by rfl) ⟨274589, by rfl⟩) R549179
theorem R169595 : Reach 169595 := rs (se 1 (by rfl) ⟨127196, by rfl⟩) R254393
theorem R169721 : Reach 169721 := rs (se 2 (by rfl) ⟨63645, by rfl⟩) R127291
theorem R268105 : Reach 268105 := rs (se 2 (by rfl) ⟨100539, by rfl⟩) R201079
theorem R137143 : Reach 137143 := rs (se 1 (by rfl) ⟨102857, by rfl⟩) R205715
theorem R169991 : Reach 169991 := rs (se 1 (by rfl) ⟨127493, by rfl⟩) R254987
theorem R170063 : Reach 170063 := rs (se 1 (by rfl) ⟨127547, by rfl⟩) R255095
theorem R170459 : Reach 170459 := rs (se 1 (by rfl) ⟨127844, by rfl⟩) R255689
theorem R1874501 : Reach 1874501 := rs (se 4 (by rfl) ⟨175734, by rfl⟩) R351469
theorem R170927 : Reach 170927 := rs (se 1 (by rfl) ⟨128195, by rfl⟩) R256391
theorem R498707 : Reach 498707 := rs (se 1 (by rfl) ⟨374030, by rfl⟩) R748061
theorem R171065 : Reach 171065 := rs (se 2 (by rfl) ⟨64149, by rfl⟩) R128299
theorem R597071 : Reach 597071 := rs (se 1 (by rfl) ⟨447803, by rfl⟩) R895607
theorem R400463 : Reach 400463 := rs (se 1 (by rfl) ⟨300347, by rfl⟩) R600695
theorem R171179 : Reach 171179 := rs (se 1 (by rfl) ⟨128384, by rfl⟩) R256769
theorem R367811 : Reach 367811 := rs (se 1 (by rfl) ⟨275858, by rfl⟩) R551717
theorem R826919 : Reach 826919 := rs (se 1 (by rfl) ⟨620189, by rfl⟩) R1240379
theorem R171719 : Reach 171719 := rs (se 1 (by rfl) ⟨128789, by rfl⟩) R257579
theorem R368327 : Reach 368327 := rs (se 1 (by rfl) ⟨276245, by rfl⟩) R552491
theorem R499715 : Reach 499715 := rs (se 1 (by rfl) ⟨374786, by rfl⟩) R749573
theorem R565325 : Reach 565325 := rs (se 3 (by rfl) ⟨105998, by rfl⟩) R211997
theorem R172583 : Reach 172583 := rs (se 1 (by rfl) ⟨129437, by rfl⟩) R258875
theorem R369211 : Reach 369211 := rs (se 1 (by rfl) ⟨276908, by rfl⟩) R553817
theorem R172907 : Reach 172907 := rs (se 1 (by rfl) ⟨129680, by rfl⟩) R259361
theorem R172961 : Reach 172961 := rs (se 2 (by rfl) ⟨64860, by rfl⟩) R129721
theorem R435395 : Reach 435395 := rs (se 1 (by rfl) ⟨326546, by rfl⟩) R653093
theorem R173303 : Reach 173303 := rs (se 1 (by rfl) ⟨129977, by rfl⟩) R259955
theorem R75131 : Reach 75131 := rs (se 1 (by rfl) ⟨56348, by rfl⟩) R112697
theorem R337277 : Reach 337277 := rs (se 3 (by rfl) ⟨63239, by rfl⟩) R126479
theorem R75183 : Reach 75183 := rs (se 1 (by rfl) ⟨56387, by rfl⟩) R112775
theorem R75207 : Reach 75207 := rs (se 1 (by rfl) ⟨56405, by rfl⟩) R112811
theorem R107995 : Reach 107995 := rs (se 1 (by rfl) ⟨80996, by rfl⟩) R161993
theorem R75227 : Reach 75227 := rs (se 1 (by rfl) ⟨56420, by rfl⟩) R112841
theorem R75303 : Reach 75303 := rs (se 1 (by rfl) ⟨56477, by rfl⟩) R112955
theorem R75343 : Reach 75343 := rs (se 1 (by rfl) ⟨56507, by rfl⟩) R113015
theorem R75359 : Reach 75359 := rs (se 1 (by rfl) ⟨56519, by rfl⟩) R113039
theorem R75387 : Reach 75387 := rs (se 1 (by rfl) ⟨56540, by rfl⟩) R113081
theorem R435851 : Reach 435851 := rs (se 1 (by rfl) ⟨326888, by rfl⟩) R653777
theorem R75439 : Reach 75439 := rs (se 1 (by rfl) ⟨56579, by rfl⟩) R113159
theorem R75463 : Reach 75463 := rs (se 1 (by rfl) ⟨56597, by rfl⟩) R113195
theorem R75483 : Reach 75483 := rs (se 1 (by rfl) ⟨56612, by rfl⟩) R113225
theorem R141049 : Reach 141049 := rs (se 2 (by rfl) ⟨52893, by rfl⟩) R105787
theorem R75559 : Reach 75559 := rs (se 1 (by rfl) ⟨56669, by rfl⟩) R113339
theorem R173897 : Reach 173897 := rs (se 2 (by rfl) ⟨65211, by rfl⟩) R130423
theorem R75599 : Reach 75599 := rs (se 1 (by rfl) ⟨56699, by rfl⟩) R113399
theorem R75615 : Reach 75615 := rs (se 1 (by rfl) ⟨56711, by rfl⟩) R113423
theorem R75643 : Reach 75643 := rs (se 1 (by rfl) ⟨56732, by rfl⟩) R113465
theorem R75695 : Reach 75695 := rs (se 1 (by rfl) ⟨56771, by rfl⟩) R113543
theorem R75719 : Reach 75719 := rs (se 1 (by rfl) ⟨56789, by rfl⟩) R113579
theorem R501713 : Reach 501713 := rs (se 2 (by rfl) ⟨188142, by rfl⟩) R376285
theorem R75739 : Reach 75739 := rs (se 1 (by rfl) ⟨56804, by rfl⟩) R113609
theorem R108553 : Reach 108553 := rs (se 2 (by rfl) ⟨40707, by rfl⟩) R81415
theorem R1484837 : Reach 1484837 := rs (se 4 (by rfl) ⟨139203, by rfl⟩) R278407
theorem R75815 : Reach 75815 := rs (se 1 (by rfl) ⟨56861, by rfl⟩) R113723
theorem R75855 : Reach 75855 := rs (se 1 (by rfl) ⟨56891, by rfl⟩) R113783
theorem R75871 : Reach 75871 := rs (se 1 (by rfl) ⟨56903, by rfl⟩) R113807
theorem R75899 : Reach 75899 := rs (se 1 (by rfl) ⟨56924, by rfl⟩) R113849
theorem R75951 : Reach 75951 := rs (se 1 (by rfl) ⟨56963, by rfl⟩) R113927
theorem R75975 : Reach 75975 := rs (se 1 (by rfl) ⟨56981, by rfl⟩) R113963
theorem R75995 : Reach 75995 := rs (se 1 (by rfl) ⟨56996, by rfl⟩) R113993
theorem R76071 : Reach 76071 := rs (se 1 (by rfl) ⟨57053, by rfl⟩) R114107
theorem R76111 : Reach 76111 := rs (se 1 (by rfl) ⟨57083, by rfl⟩) R114167
theorem R76127 : Reach 76127 := rs (se 1 (by rfl) ⟨57095, by rfl⟩) R114191
theorem R76155 : Reach 76155 := rs (se 1 (by rfl) ⟨57116, by rfl⟩) R114233
theorem R76207 : Reach 76207 := rs (se 1 (by rfl) ⟨57155, by rfl⟩) R114311
theorem R76231 : Reach 76231 := rs (se 1 (by rfl) ⟨57173, by rfl⟩) R114347
theorem R76251 : Reach 76251 := rs (se 1 (by rfl) ⟨57188, by rfl⟩) R114377
theorem R76327 : Reach 76327 := rs (se 1 (by rfl) ⟨57245, by rfl⟩) R114491
theorem R76367 : Reach 76367 := rs (se 1 (by rfl) ⟨57275, by rfl⟩) R114551
theorem R76383 : Reach 76383 := rs (se 1 (by rfl) ⟨57287, by rfl⟩) R114575
theorem R174689 : Reach 174689 := rs (se 2 (by rfl) ⟨65508, by rfl⟩) R131017
theorem R76411 : Reach 76411 := rs (se 1 (by rfl) ⟨57308, by rfl⟩) R114617
theorem R76463 : Reach 76463 := rs (se 1 (by rfl) ⟨57347, by rfl⟩) R114695
theorem R240317 : Reach 240317 := rs (se 3 (by rfl) ⟨45059, by rfl⟩) R90119
theorem R76487 : Reach 76487 := rs (se 1 (by rfl) ⟨57365, by rfl⟩) R114731
theorem R76507 : Reach 76507 := rs (se 1 (by rfl) ⟨57380, by rfl⟩) R114761
theorem R76583 : Reach 76583 := rs (se 1 (by rfl) ⟨57437, by rfl⟩) R114875
theorem R76623 : Reach 76623 := rs (se 1 (by rfl) ⟨57467, by rfl⟩) R114935
theorem R76639 : Reach 76639 := rs (se 1 (by rfl) ⟨57479, by rfl⟩) R114959
theorem R142175 : Reach 142175 := rs (se 1 (by rfl) ⟨106631, by rfl⟩) R213263
theorem R76667 : Reach 76667 := rs (se 1 (by rfl) ⟨57500, by rfl⟩) R115001
theorem R76719 : Reach 76719 := rs (se 1 (by rfl) ⟨57539, by rfl⟩) R115079
theorem R175031 : Reach 175031 := rs (se 1 (by rfl) ⟨131273, by rfl⟩) R262547
theorem R76743 : Reach 76743 := rs (se 1 (by rfl) ⟨57557, by rfl⟩) R115115
theorem R76763 : Reach 76763 := rs (se 1 (by rfl) ⟨57572, by rfl⟩) R115145
theorem R2698211 : Reach 2698211 := rs (se 1 (by rfl) ⟨2023658, by rfl⟩) R4047317
theorem R76839 : Reach 76839 := rs (se 1 (by rfl) ⟨57629, by rfl⟩) R115259
theorem R76879 : Reach 76879 := rs (se 1 (by rfl) ⟨57659, by rfl⟩) R115319
theorem R76895 : Reach 76895 := rs (se 1 (by rfl) ⟨57671, by rfl⟩) R115343
theorem R76923 : Reach 76923 := rs (se 1 (by rfl) ⟨57692, by rfl⟩) R115385
theorem R76975 : Reach 76975 := rs (se 1 (by rfl) ⟨57731, by rfl⟩) R115463
theorem R76999 : Reach 76999 := rs (se 1 (by rfl) ⟨57749, by rfl⟩) R115499
theorem R77019 : Reach 77019 := rs (se 1 (by rfl) ⟨57764, by rfl⟩) R115529
theorem R77095 : Reach 77095 := rs (se 1 (by rfl) ⟨57821, by rfl⟩) R115643
theorem R77135 : Reach 77135 := rs (se 1 (by rfl) ⟨57851, by rfl⟩) R115703
theorem R77151 : Reach 77151 := rs (se 1 (by rfl) ⟨57863, by rfl⟩) R115727
theorem R77179 : Reach 77179 := rs (se 1 (by rfl) ⟨57884, by rfl⟩) R115769
theorem R77231 : Reach 77231 := rs (se 1 (by rfl) ⟨57923, by rfl⟩) R115847
theorem R77255 : Reach 77255 := rs (se 1 (by rfl) ⟨57941, by rfl⟩) R115883
theorem R77275 : Reach 77275 := rs (se 1 (by rfl) ⟨57956, by rfl⟩) R115913
theorem R175625 : Reach 175625 := rs (se 2 (by rfl) ⟨65859, by rfl⟩) R131719
theorem R77351 : Reach 77351 := rs (se 1 (by rfl) ⟨58013, by rfl⟩) R116027
theorem R77391 : Reach 77391 := rs (se 1 (by rfl) ⟨58043, by rfl⟩) R116087
theorem R77407 : Reach 77407 := rs (se 1 (by rfl) ⟨58055, by rfl⟩) R116111
theorem R77435 : Reach 77435 := rs (se 1 (by rfl) ⟨58076, by rfl⟩) R116153
theorem R77487 : Reach 77487 := rs (se 1 (by rfl) ⟨58115, by rfl⟩) R116231
theorem R77511 : Reach 77511 := rs (se 1 (by rfl) ⟨58133, by rfl⟩) R116267
theorem R143059 : Reach 143059 := rs (se 1 (by rfl) ⟨107294, by rfl⟩) R214589
theorem R77531 : Reach 77531 := rs (se 1 (by rfl) ⟨58148, by rfl⟩) R116297
theorem R77607 : Reach 77607 := rs (se 1 (by rfl) ⟨58205, by rfl⟩) R116411
theorem R241451 : Reach 241451 := rs (se 1 (by rfl) ⟨181088, by rfl⟩) R362177
theorem R77647 : Reach 77647 := rs (se 1 (by rfl) ⟨58235, by rfl⟩) R116471
theorem R77663 : Reach 77663 := rs (se 1 (by rfl) ⟨58247, by rfl⟩) R116495
theorem R175967 : Reach 175967 := rs (se 1 (by rfl) ⟨131975, by rfl⟩) R263951
theorem R77691 : Reach 77691 := rs (se 1 (by rfl) ⟨58268, by rfl⟩) R116537
theorem R143279 : Reach 143279 := rs (se 1 (by rfl) ⟨107459, by rfl⟩) R214919
theorem R77743 : Reach 77743 := rs (se 1 (by rfl) ⟨58307, by rfl⟩) R116615
theorem R77767 : Reach 77767 := rs (se 1 (by rfl) ⟨58325, by rfl⟩) R116651
theorem R77787 : Reach 77787 := rs (se 1 (by rfl) ⟨58340, by rfl⟩) R116681
theorem R176147 : Reach 176147 := rs (se 1 (by rfl) ⟨132110, by rfl⟩) R264221
theorem R77863 : Reach 77863 := rs (se 1 (by rfl) ⟨58397, by rfl⟩) R116795
theorem R77903 : Reach 77903 := rs (se 1 (by rfl) ⟨58427, by rfl⟩) R116855
theorem R77919 : Reach 77919 := rs (se 1 (by rfl) ⟨58439, by rfl⟩) R116879
theorem R77947 : Reach 77947 := rs (se 1 (by rfl) ⟨58460, by rfl⟩) R116921
theorem R569501 : Reach 569501 := rs (se 3 (by rfl) ⟨106781, by rfl⟩) R213563
theorem R77999 : Reach 77999 := rs (se 1 (by rfl) ⟨58499, by rfl⟩) R116999
theorem R78023 : Reach 78023 := rs (se 1 (by rfl) ⟨58517, by rfl⟩) R117035
theorem R78043 : Reach 78043 := rs (se 1 (by rfl) ⟨58532, by rfl⟩) R117065
theorem R78119 : Reach 78119 := rs (se 1 (by rfl) ⟨58589, by rfl⟩) R117179
theorem R143689 : Reach 143689 := rs (se 2 (by rfl) ⟨53883, by rfl⟩) R107767
theorem R78159 : Reach 78159 := rs (se 1 (by rfl) ⟨58619, by rfl⟩) R117239
theorem R405847 : Reach 405847 := rs (se 1 (by rfl) ⟨304385, by rfl⟩) R608771
theorem R78175 : Reach 78175 := rs (se 1 (by rfl) ⟨58631, by rfl⟩) R117263
theorem R176489 : Reach 176489 := rs (se 2 (by rfl) ⟨66183, by rfl⟩) R132367
theorem R78203 : Reach 78203 := rs (se 1 (by rfl) ⟨58652, by rfl⟩) R117305
theorem R78255 : Reach 78255 := rs (se 1 (by rfl) ⟨58691, by rfl⟩) R117383
theorem R78279 : Reach 78279 := rs (se 1 (by rfl) ⟨58709, by rfl⟩) R117419
theorem R78299 : Reach 78299 := rs (se 1 (by rfl) ⟨58724, by rfl⟩) R117449
theorem R78375 : Reach 78375 := rs (se 1 (by rfl) ⟨58781, by rfl⟩) R117563
theorem R78415 : Reach 78415 := rs (se 1 (by rfl) ⟨58811, by rfl⟩) R117623
theorem R78431 : Reach 78431 := rs (se 1 (by rfl) ⟨58823, by rfl⟩) R117647
theorem R78459 : Reach 78459 := rs (se 1 (by rfl) ⟨58844, by rfl⟩) R117689
theorem R78511 : Reach 78511 := rs (se 1 (by rfl) ⟨58883, by rfl⟩) R117767
theorem R78535 : Reach 78535 := rs (se 1 (by rfl) ⟨58901, by rfl⟩) R117803
theorem R537299 : Reach 537299 := rs (se 1 (by rfl) ⟨402974, by rfl⟩) R805949
theorem R78555 : Reach 78555 := rs (se 1 (by rfl) ⟨58916, by rfl⟩) R117833
theorem R78631 : Reach 78631 := rs (se 1 (by rfl) ⟨58973, by rfl⟩) R117947
theorem R78671 : Reach 78671 := rs (se 1 (by rfl) ⟨59003, by rfl⟩) R118007
theorem R78687 : Reach 78687 := rs (se 1 (by rfl) ⟨59015, by rfl⟩) R118031
theorem R308087 : Reach 308087 := rs (se 1 (by rfl) ⟨231065, by rfl⟩) R462131
theorem R78715 : Reach 78715 := rs (se 1 (by rfl) ⟨59036, by rfl⟩) R118073
theorem R78767 : Reach 78767 := rs (se 1 (by rfl) ⟨59075, by rfl⟩) R118151
theorem R177083 : Reach 177083 := rs (se 1 (by rfl) ⟨132812, by rfl⟩) R265625
theorem R78791 : Reach 78791 := rs (se 1 (by rfl) ⟨59093, by rfl⟩) R118187
theorem R78811 : Reach 78811 := rs (se 1 (by rfl) ⟨59108, by rfl⟩) R118217
theorem R78887 : Reach 78887 := rs (se 1 (by rfl) ⟨59165, by rfl⟩) R118331
theorem R177209 : Reach 177209 := rs (se 2 (by rfl) ⟨66453, by rfl⟩) R132907
theorem R78927 : Reach 78927 := rs (se 1 (by rfl) ⟨59195, by rfl⟩) R118391
theorem R78943 : Reach 78943 := rs (se 1 (by rfl) ⟨59207, by rfl⟩) R118415
theorem R78971 : Reach 78971 := rs (se 1 (by rfl) ⟨59228, by rfl⟩) R118457
theorem R79023 : Reach 79023 := rs (se 1 (by rfl) ⟨59267, by rfl⟩) R118535
theorem R505025 : Reach 505025 := rs (se 2 (by rfl) ⟨189384, by rfl⟩) R378769
theorem R570563 : Reach 570563 := rs (se 1 (by rfl) ⟨427922, by rfl⟩) R855845
theorem R79047 : Reach 79047 := rs (se 1 (by rfl) ⟨59285, by rfl⟩) R118571
theorem R79067 : Reach 79067 := rs (se 1 (by rfl) ⟨59300, by rfl⟩) R118601
theorem R177551 : Reach 177551 := rs (se 1 (by rfl) ⟨133163, by rfl⟩) R266327
theorem R243145 : Reach 243145 := rs (se 2 (by rfl) ⟨91179, by rfl⟩) R182359
theorem R538235 : Reach 538235 := rs (se 1 (by rfl) ⟨403676, by rfl⟩) R807353
theorem R177875 : Reach 177875 := rs (se 1 (by rfl) ⟨133406, by rfl⟩) R266813
theorem R440057 : Reach 440057 := rs (se 2 (by rfl) ⟨165021, by rfl⟩) R330043
theorem R440225 : Reach 440225 := rs (se 2 (by rfl) ⟨165084, by rfl⟩) R330169
theorem R112763 : Reach 112763 := rs (se 1 (by rfl) ⟨84572, by rfl⟩) R169145
theorem R440477 : Reach 440477 := rs (se 3 (by rfl) ⟨82589, by rfl⟩) R165179
theorem R3225757 : Reach 3225757 := rs (se 3 (by rfl) ⟨604829, by rfl⟩) R1209659
theorem R112889 : Reach 112889 := rs (se 2 (by rfl) ⟨42333, by rfl⟩) R84667
theorem R112991 : Reach 112991 := rs (se 1 (by rfl) ⟨84743, by rfl⟩) R169487
theorem R113003 : Reach 113003 := rs (se 1 (by rfl) ⟨84752, by rfl⟩) R169505
theorem R342401 : Reach 342401 := rs (se 2 (by rfl) ⟨128400, by rfl⟩) R256801
theorem R80347 : Reach 80347 := rs (se 1 (by rfl) ⟨60260, by rfl⟩) R120521
theorem R113231 : Reach 113231 := rs (se 1 (by rfl) ⟨84923, by rfl⟩) R169847
theorem R277127 : Reach 277127 := rs (se 1 (by rfl) ⟨207845, by rfl⟩) R415691
theorem R113351 : Reach 113351 := rs (se 1 (by rfl) ⟨85013, by rfl⟩) R170027
theorem R146119 : Reach 146119 := rs (se 1 (by rfl) ⟨109589, by rfl⟩) R219179
theorem R342737 : Reach 342737 := rs (se 2 (by rfl) ⟨128526, by rfl⟩) R257053
theorem R113513 : Reach 113513 := rs (se 2 (by rfl) ⟨42567, by rfl⟩) R85135
theorem R277357 : Reach 277357 := rs (se 3 (by rfl) ⟨52004, by rfl⟩) R104009
theorem R113591 : Reach 113591 := rs (se 1 (by rfl) ⟨85193, by rfl⟩) R170387
theorem R342967 : Reach 342967 := rs (se 1 (by rfl) ⟨257225, by rfl⟩) R514451
theorem R113627 : Reach 113627 := rs (se 1 (by rfl) ⟨85220, by rfl⟩) R170441
theorem R1424557 : Reach 1424557 := rs (se 3 (by rfl) ⟨267104, by rfl⟩) R534209
theorem R146681 : Reach 146681 := rs (se 2 (by rfl) ⟨55005, by rfl⟩) R110011
theorem R1719575 : Reach 1719575 := rs (se 1 (by rfl) ⟨1289681, by rfl⟩) R2579363
theorem R114095 : Reach 114095 := rs (se 1 (by rfl) ⟨85571, by rfl⟩) R171143
theorem R146863 : Reach 146863 := rs (se 1 (by rfl) ⟨110147, by rfl⟩) R220295
theorem R114185 : Reach 114185 := rs (se 2 (by rfl) ⟨42819, by rfl⟩) R85639
theorem R114215 : Reach 114215 := rs (se 1 (by rfl) ⟨85661, by rfl⟩) R171323
theorem R441895 : Reach 441895 := rs (se 1 (by rfl) ⟨331421, by rfl⟩) R662843
theorem R114299 : Reach 114299 := rs (se 1 (by rfl) ⟨85724, by rfl⟩) R171449
theorem R114425 : Reach 114425 := rs (se 2 (by rfl) ⟨42909, by rfl⟩) R85819
theorem R114527 : Reach 114527 := rs (se 1 (by rfl) ⟨85895, by rfl⟩) R171791
theorem R114539 : Reach 114539 := rs (se 1 (by rfl) ⟨85904, by rfl⟩) R171809
theorem R147361 : Reach 147361 := rs (se 2 (by rfl) ⟨55260, by rfl⟩) R110521
theorem R409637 : Reach 409637 := rs (se 4 (by rfl) ⟨38403, by rfl⟩) R76807
theorem R114767 : Reach 114767 := rs (se 1 (by rfl) ⟨86075, by rfl⟩) R172151
theorem R1097891 : Reach 1097891 := rs (se 1 (by rfl) ⟨823418, by rfl⟩) R1646837
theorem R114887 : Reach 114887 := rs (se 1 (by rfl) ⟨86165, by rfl⟩) R172331
theorem R442685 : Reach 442685 := rs (se 3 (by rfl) ⟨83003, by rfl⟩) R166007
theorem R344407 : Reach 344407 := rs (se 1 (by rfl) ⟨258305, by rfl⟩) R516611
theorem R115049 : Reach 115049 := rs (se 2 (by rfl) ⟨43143, by rfl⟩) R86287
theorem R115127 : Reach 115127 := rs (se 1 (by rfl) ⟨86345, by rfl⟩) R172691
theorem R115163 : Reach 115163 := rs (se 1 (by rfl) ⟨86372, by rfl⟩) R172745
theorem R148139 : Reach 148139 := rs (se 1 (by rfl) ⟨111104, by rfl⟩) R222209
theorem R312173 : Reach 312173 := rs (se 3 (by rfl) ⟨58532, by rfl⟩) R117065
theorem R148367 : Reach 148367 := rs (se 1 (by rfl) ⟨111275, by rfl⟩) R222551
theorem R115631 : Reach 115631 := rs (se 1 (by rfl) ⟨86723, by rfl⟩) R173447
theorem R443393 : Reach 443393 := rs (se 2 (by rfl) ⟨166272, by rfl⟩) R332545
theorem R115721 : Reach 115721 := rs (se 2 (by rfl) ⟨43395, by rfl⟩) R86791
theorem R115751 : Reach 115751 := rs (se 1 (by rfl) ⟨86813, by rfl⟩) R173627
theorem R1131569 : Reach 1131569 := rs (se 2 (by rfl) ⟨424338, by rfl⟩) R848677
theorem R967747 : Reach 967747 := rs (se 1 (by rfl) ⟨725810, by rfl⟩) R1451621
theorem R115835 : Reach 115835 := rs (se 1 (by rfl) ⟨86876, by rfl⟩) R173753
theorem R115961 : Reach 115961 := rs (se 2 (by rfl) ⟨43485, by rfl⟩) R86971
theorem R279895 : Reach 279895 := rs (se 1 (by rfl) ⟨209921, by rfl⟩) R419843
theorem R116063 : Reach 116063 := rs (se 1 (by rfl) ⟨87047, by rfl⟩) R174095
theorem R116075 : Reach 116075 := rs (se 1 (by rfl) ⟨87056, by rfl⟩) R174113
theorem R1459619 : Reach 1459619 := rs (se 1 (by rfl) ⟨1094714, by rfl⟩) R2189429
theorem R181723 : Reach 181723 := rs (se 1 (by rfl) ⟨136292, by rfl⟩) R272585
theorem R116303 : Reach 116303 := rs (se 1 (by rfl) ⟨87227, by rfl⟩) R174455
theorem R116347 : Reach 116347 := rs (se 1 (by rfl) ⟨87260, by rfl⟩) R174521
theorem R280253 : Reach 280253 := rs (se 3 (by rfl) ⟨52547, by rfl⟩) R105095
theorem R116423 : Reach 116423 := rs (se 1 (by rfl) ⟨87317, by rfl⟩) R174635
theorem R739115 : Reach 739115 := rs (se 1 (by rfl) ⟨554336, by rfl⟩) R1108673
theorem R116585 : Reach 116585 := rs (se 2 (by rfl) ⟨43719, by rfl⟩) R87439
theorem R116663 : Reach 116663 := rs (se 1 (by rfl) ⟨87497, by rfl⟩) R174995
theorem R116699 : Reach 116699 := rs (se 1 (by rfl) ⟨87524, by rfl⟩) R175049
theorem R149627 : Reach 149627 := rs (se 1 (by rfl) ⟨112220, by rfl⟩) R224441
theorem R149855 : Reach 149855 := rs (se 1 (by rfl) ⟨112391, by rfl⟩) R224783
theorem R117167 : Reach 117167 := rs (se 1 (by rfl) ⟨87875, by rfl⟩) R175751
theorem R1133003 : Reach 1133003 := rs (se 1 (by rfl) ⟨849752, by rfl⟩) R1699505
theorem R117257 : Reach 117257 := rs (se 2 (by rfl) ⟨43971, by rfl⟩) R87943
theorem R117287 : Reach 117287 := rs (se 1 (by rfl) ⟨87965, by rfl⟩) R175931
theorem R84559 : Reach 84559 := rs (se 1 (by rfl) ⟨63419, by rfl⟩) R126839
theorem R150113 : Reach 150113 := rs (se 2 (by rfl) ⟨56292, by rfl⟩) R112585
theorem R117371 : Reach 117371 := rs (se 1 (by rfl) ⟨88028, by rfl⟩) R176057
theorem R117497 : Reach 117497 := rs (se 2 (by rfl) ⟨44061, by rfl⟩) R88123
theorem R117599 : Reach 117599 := rs (se 1 (by rfl) ⟨88199, by rfl⟩) R176399
theorem R117611 : Reach 117611 := rs (se 1 (by rfl) ⟨88208, by rfl⟩) R176417
theorem R84955 : Reach 84955 := rs (se 1 (by rfl) ⟨63716, by rfl⟩) R127433
theorem R117839 : Reach 117839 := rs (se 1 (by rfl) ⟨88379, by rfl⟩) R176759
theorem R117959 : Reach 117959 := rs (se 1 (by rfl) ⟨88469, by rfl⟩) R176939
theorem R609551 : Reach 609551 := rs (se 1 (by rfl) ⟨457163, by rfl⟩) R914327
theorem R118121 : Reach 118121 := rs (se 2 (by rfl) ⟨44295, by rfl⟩) R88591
theorem R216445 : Reach 216445 := rs (se 3 (by rfl) ⟨40583, by rfl⟩) R81167
theorem R85423 : Reach 85423 := rs (se 1 (by rfl) ⟨64067, by rfl⟩) R128135
theorem R118199 : Reach 118199 := rs (se 1 (by rfl) ⟨88649, by rfl⟩) R177299
theorem R118235 : Reach 118235 := rs (se 1 (by rfl) ⟨88676, by rfl⟩) R177353
theorem R85855 : Reach 85855 := rs (se 1 (by rfl) ⟨64391, by rfl⟩) R128783
theorem R413549 : Reach 413549 := rs (se 3 (by rfl) ⟨77540, by rfl⟩) R155081
theorem R118793 : Reach 118793 := rs (se 2 (by rfl) ⟨44547, by rfl⟩) R89095
theorem R86215 : Reach 86215 := rs (se 1 (by rfl) ⟨64661, by rfl⟩) R129323
theorem R577853 : Reach 577853 := rs (se 3 (by rfl) ⟨108347, by rfl⟩) R216695
theorem R152275 : Reach 152275 := rs (se 1 (by rfl) ⟨114206, by rfl⟩) R228413
theorem R480107 : Reach 480107 := rs (se 1 (by rfl) ⟨360080, by rfl⟩) R720161
theorem R86959 : Reach 86959 := rs (se 1 (by rfl) ⟨65219, by rfl⟩) R130439
theorem R87079 : Reach 87079 := rs (se 1 (by rfl) ⟨65309, by rfl⟩) R130619
theorem R480323 : Reach 480323 := rs (se 1 (by rfl) ⟨360242, by rfl⟩) R720485
theorem R447767 : Reach 447767 := rs (se 1 (by rfl) ⟨335825, by rfl⟩) R671651
theorem R448199 : Reach 448199 := rs (se 1 (by rfl) ⟨336149, by rfl⟩) R672299
theorem R1005473 : Reach 1005473 := rs (se 2 (by rfl) ⟨377052, by rfl⟩) R754105
theorem R415751 : Reach 415751 := rs (se 1 (by rfl) ⟨311813, by rfl⟩) R623627
theorem R3299363 : Reach 3299363 := rs (se 1 (by rfl) ⟨2474522, by rfl⟩) R4949045
theorem R350365 : Reach 350365 := rs (se 3 (by rfl) ⟨65693, by rfl⟩) R131387
theorem R219293 : Reach 219293 := rs (se 3 (by rfl) ⟨41117, by rfl⟩) R82235
theorem R284867 : Reach 284867 := rs (se 1 (by rfl) ⟨213650, by rfl⟩) R427301
theorem R219611 : Reach 219611 := rs (se 1 (by rfl) ⟨164708, by rfl⟩) R329417
theorem R219635 : Reach 219635 := rs (se 1 (by rfl) ⟨164726, by rfl⟩) R329453
theorem R88699 : Reach 88699 := rs (se 1 (by rfl) ⟨66524, by rfl⟩) R133049
theorem R1071751 : Reach 1071751 := rs (se 1 (by rfl) ⟨803813, by rfl⟩) R1607627
theorem R1170251 : Reach 1170251 := rs (se 1 (by rfl) ⟨877688, by rfl⟩) R1755377
theorem R253085 : Reach 253085 := rs (se 3 (by rfl) ⟨47453, by rfl⟩) R94907
theorem R1105325 : Reach 1105325 := rs (se 3 (by rfl) ⟨207248, by rfl⟩) R414497
theorem R351959 : Reach 351959 := rs (se 1 (by rfl) ⟨263969, by rfl⟩) R527939
theorem R941959 : Reach 941959 := rs (se 1 (by rfl) ⟨706469, by rfl⟩) R1412939
theorem R155567 : Reach 155567 := rs (se 1 (by rfl) ⟨116675, by rfl⟩) R233351
theorem R188335 : Reach 188335 := rs (se 1 (by rfl) ⟨141251, by rfl⟩) R282503
theorem R483259 : Reach 483259 := rs (se 1 (by rfl) ⟨362444, by rfl⟩) R724889
theorem R548801 : Reach 548801 := rs (se 2 (by rfl) ⟨205800, by rfl⟩) R411601
theorem R254123 : Reach 254123 := rs (se 1 (by rfl) ⟨190592, by rfl⟩) R381185
theorem R188777 : Reach 188777 := rs (se 2 (by rfl) ⟨70791, by rfl⟩) R141583
theorem R385721 : Reach 385721 := rs (se 2 (by rfl) ⟨144645, by rfl⟩) R289291
theorem R254663 : Reach 254663 := rs (se 1 (by rfl) ⟨190997, by rfl⟩) R381995
theorem R255527 : Reach 255527 := rs (se 1 (by rfl) ⟨191645, by rfl⟩) R383291
theorem R255635 : Reach 255635 := rs (se 1 (by rfl) ⟨191726, by rfl⟩) R383453
theorem R255851 : Reach 255851 := rs (se 1 (by rfl) ⟨191888, by rfl⟩) R383777
theorem R255905 : Reach 255905 := rs (se 2 (by rfl) ⟨95964, by rfl⟩) R191929
theorem R550817 : Reach 550817 := rs (se 2 (by rfl) ⟨206556, by rfl⟩) R413113
theorem R223163 : Reach 223163 := rs (se 1 (by rfl) ⟨167372, by rfl⟩) R334745
theorem R190471 : Reach 190471 := rs (se 1 (by rfl) ⟨142853, by rfl⟩) R285707
theorem R124967 : Reach 124967 := rs (se 1 (by rfl) ⟨93725, by rfl⟩) R187451
theorem R551069 : Reach 551069 := rs (se 3 (by rfl) ⟨103325, by rfl⟩) R206651
theorem R256499 : Reach 256499 := rs (se 1 (by rfl) ⟨192374, by rfl⟩) R384749
theorem R191099 : Reach 191099 := rs (se 1 (by rfl) ⟨143324, by rfl⟩) R286649
theorem R289565 : Reach 289565 := rs (se 3 (by rfl) ⟨54293, by rfl⟩) R108587
theorem R191393 : Reach 191393 := rs (se 2 (by rfl) ⟨71772, by rfl⟩) R143545
theorem R257039 : Reach 257039 := rs (se 1 (by rfl) ⟨192779, by rfl⟩) R385559
theorem R1109015 : Reach 1109015 := rs (se 1 (by rfl) ⟨831761, by rfl⟩) R1663523
theorem R486593 : Reach 486593 := rs (se 2 (by rfl) ⟨182472, by rfl⟩) R364945
theorem R290249 : Reach 290249 := rs (se 2 (by rfl) ⟨108843, by rfl⟩) R217687
theorem R257633 : Reach 257633 := rs (se 2 (by rfl) ⟨96612, by rfl⟩) R193225
theorem R487133 : Reach 487133 := rs (se 3 (by rfl) ⟨91337, by rfl⟩) R182675
theorem R290735 : Reach 290735 := rs (se 1 (by rfl) ⟨218051, by rfl⟩) R436103
theorem R127055 : Reach 127055 := rs (se 1 (by rfl) ⟨95291, by rfl⟩) R190583
theorem R324121 : Reach 324121 := rs (se 2 (by rfl) ⟨121545, by rfl⟩) R243091
theorem R193063 : Reach 193063 := rs (se 1 (by rfl) ⟨144797, by rfl⟩) R289595
theorem R324155 : Reach 324155 := rs (se 1 (by rfl) ⟨243116, by rfl⟩) R486233
theorem R291539 : Reach 291539 := rs (se 1 (by rfl) ⟨218654, by rfl⟩) R437309
theorem R881425 : Reach 881425 := rs (se 2 (by rfl) ⟨330534, by rfl⟩) R661069
theorem R193387 : Reach 193387 := rs (se 1 (by rfl) ⟨145040, by rfl⟩) R290081
theorem R193441 : Reach 193441 := rs (se 2 (by rfl) ⟨72540, by rfl⟩) R145081
theorem R127919 : Reach 127919 := rs (se 1 (by rfl) ⟨95939, by rfl⟩) R191879
theorem R95195 : Reach 95195 := rs (se 1 (by rfl) ⟨71396, by rfl⟩) R142793
theorem R1635329 : Reach 1635329 := rs (se 2 (by rfl) ⟨613248, by rfl⟩) R1226497
theorem R259091 : Reach 259091 := rs (se 1 (by rfl) ⟨194318, by rfl⟩) R388637
theorem R259415 : Reach 259415 := rs (se 1 (by rfl) ⟨194561, by rfl⟩) R389123
theorem R128351 : Reach 128351 := rs (se 1 (by rfl) ⟨96263, by rfl⟩) R192527
theorem R95671 : Reach 95671 := rs (se 1 (by rfl) ⟨71753, by rfl⟩) R143507
theorem R194035 : Reach 194035 := rs (se 1 (by rfl) ⟨145526, by rfl⟩) R291053
theorem R390905 : Reach 390905 := rs (se 2 (by rfl) ⟨146589, by rfl⟩) R293179
theorem R128911 : Reach 128911 := rs (se 1 (by rfl) ⟨96683, by rfl⟩) R193367
theorem R260111 : Reach 260111 := rs (se 1 (by rfl) ⟨195083, by rfl⟩) R390167
theorem R391553 : Reach 391553 := rs (se 2 (by rfl) ⟨146832, by rfl⟩) R293665
theorem R260495 : Reach 260495 := rs (se 1 (by rfl) ⟨195371, by rfl⟩) R390743
theorem R129455 : Reach 129455 := rs (se 1 (by rfl) ⟨97091, by rfl⟩) R194183
theorem R4487723 : Reach 4487723 := rs (se 1 (by rfl) ⟨3365792, by rfl⟩) R6731585
theorem R129593 : Reach 129593 := rs (se 2 (by rfl) ⟨48597, by rfl⟩) R97195
theorem R195169 : Reach 195169 := rs (se 2 (by rfl) ⟨73188, by rfl⟩) R146377
theorem R621229 : Reach 621229 := rs (se 3 (by rfl) ⟨116480, by rfl⟩) R232961
theorem R96967 : Reach 96967 := rs (se 1 (by rfl) ⟨72725, by rfl⟩) R145451
theorem R260819 : Reach 260819 := rs (se 1 (by rfl) ⟨195614, by rfl⟩) R391229
theorem R6454333 : Reach 6454333 := rs (se 3 (by rfl) ⟨1210187, by rfl⟩) R2420375
theorem R293969 : Reach 293969 := rs (se 2 (by rfl) ⟨110238, by rfl⟩) R220477
theorem R392363 : Reach 392363 := rs (se 1 (by rfl) ⟨294272, by rfl⟩) R588545
theorem R130295 : Reach 130295 := rs (se 1 (by rfl) ⟨97721, by rfl⟩) R195443
theorem R163291 : Reach 163291 := rs (se 1 (by rfl) ⟨122468, by rfl⟩) R244937
theorem R196121 : Reach 196121 := rs (se 2 (by rfl) ⟨73545, by rfl⟩) R147091
theorem R294425 : Reach 294425 := rs (se 2 (by rfl) ⟨110409, by rfl⟩) R220819
theorem R130639 : Reach 130639 := rs (se 1 (by rfl) ⟨97979, by rfl⟩) R195959
theorem R425569 : Reach 425569 := rs (se 2 (by rfl) ⟨159588, by rfl⟩) R319177
theorem R392849 : Reach 392849 := rs (se 2 (by rfl) ⟨147318, by rfl⟩) R294637
theorem R130889 : Reach 130889 := rs (se 2 (by rfl) ⟨49083, by rfl⟩) R98167
theorem R262007 : Reach 262007 := rs (se 1 (by rfl) ⟨196505, by rfl⟩) R393011
theorem R425915 : Reach 425915 := rs (se 1 (by rfl) ⟨319436, by rfl⟩) R638873
theorem R262169 : Reach 262169 := rs (se 2 (by rfl) ⟨98313, by rfl⟩) R196627
theorem R295123 : Reach 295123 := rs (se 1 (by rfl) ⟨221342, by rfl⟩) R442685
theorem R98759 : Reach 98759 := rs (se 1 (by rfl) ⟨74069, by rfl⟩) R148139
theorem R459209 : Reach 459209 := rs (se 2 (by rfl) ⟨172203, by rfl⟩) R344407
theorem R98911 : Reach 98911 := rs (se 1 (by rfl) ⟨74183, by rfl⟩) R148367
theorem R295595 : Reach 295595 := rs (se 1 (by rfl) ⟨221696, by rfl⟩) R443393
theorem R754379 : Reach 754379 := rs (se 1 (by rfl) ⟨565784, by rfl⟩) R1131569
theorem R131807 : Reach 131807 := rs (se 1 (by rfl) ⟨98855, by rfl⟩) R197711
theorem R492281 : Reach 492281 := rs (se 2 (by rfl) ⟨184605, by rfl⟩) R369211
theorem R394145 : Reach 394145 := rs (se 2 (by rfl) ⟨147804, by rfl⟩) R295609
theorem R2884571 : Reach 2884571 := rs (se 1 (by rfl) ⟨2163428, by rfl⟩) R4326857
theorem R132239 : Reach 132239 := rs (se 1 (by rfl) ⟨99179, by rfl⟩) R198359
theorem R492743 : Reach 492743 := rs (se 1 (by rfl) ⟨369557, by rfl⟩) R739115
theorem R263411 : Reach 263411 := rs (se 1 (by rfl) ⟨197558, by rfl⟩) R395117
theorem R263519 : Reach 263519 := rs (se 1 (by rfl) ⟨197639, by rfl⟩) R395279
theorem R132475 : Reach 132475 := rs (se 1 (by rfl) ⟨99356, by rfl⟩) R198713
theorem R198227 : Reach 198227 := rs (se 1 (by rfl) ⟨148670, by rfl⟩) R297341
theorem R755335 : Reach 755335 := rs (se 1 (by rfl) ⟨566501, by rfl⟩) R1133003
theorem R1280285 : Reach 1280285 := rs (se 3 (by rfl) ⟨240053, by rfl⟩) R480107
theorem R265085 : Reach 265085 := rs (se 3 (by rfl) ⟨49703, by rfl⟩) R99407
theorem R199655 : Reach 199655 := rs (se 1 (by rfl) ⟨149741, by rfl⟩) R299483
theorem R265355 : Reach 265355 := rs (se 1 (by rfl) ⟨199016, by rfl⟩) R398033
theorem R396575 : Reach 396575 := rs (se 1 (by rfl) ⟨297431, by rfl⟩) R594863
theorem R789857 : Reach 789857 := rs (se 2 (by rfl) ⟨296196, by rfl⟩) R592393
theorem R331127 : Reach 331127 := rs (se 1 (by rfl) ⟨248345, by rfl⟩) R496691
theorem R593351 : Reach 593351 := rs (se 1 (by rfl) ⟨445013, by rfl⟩) R890027
theorem R298511 : Reach 298511 := rs (se 1 (by rfl) ⟨223883, by rfl⟩) R447767
theorem R298799 : Reach 298799 := rs (se 1 (by rfl) ⟨224099, by rfl⟩) R448199
theorem R364445 : Reach 364445 := rs (se 3 (by rfl) ⟨68333, by rfl⟩) R136667
theorem R2199575 : Reach 2199575 := rs (se 1 (by rfl) ⟨1649681, by rfl⟩) R3299363
theorem R1249667 : Reach 1249667 := rs (se 1 (by rfl) ⟨937250, by rfl⟩) R1874501
theorem R332471 : Reach 332471 := rs (se 1 (by rfl) ⟨249353, by rfl⟩) R498707
theorem R398047 : Reach 398047 := rs (se 1 (by rfl) ⟨298535, by rfl⟩) R597071
theorem R266975 : Reach 266975 := rs (se 1 (by rfl) ⟨200231, by rfl⟩) R400463
theorem R463781 : Reach 463781 := rs (se 4 (by rfl) ⟨43479, by rfl⟩) R86959
theorem R103711 : Reach 103711 := rs (se 1 (by rfl) ⟨77783, by rfl⟩) R155567
theorem R365867 : Reach 365867 := rs (se 1 (by rfl) ⟨274400, by rfl⟩) R548801
theorem R333143 : Reach 333143 := rs (se 1 (by rfl) ⟨249857, by rfl⟩) R499715
theorem R693629 : Reach 693629 := rs (se 3 (by rfl) ⟨130055, by rfl⟩) R260111
theorem R169415 : Reach 169415 := rs (se 1 (by rfl) ⟨127061, by rfl⟩) R254123
theorem R399005 : Reach 399005 := rs (se 3 (by rfl) ⟨74813, by rfl⟩) R149627
theorem R169775 : Reach 169775 := rs (se 1 (by rfl) ⟨127331, by rfl⟩) R254663
theorem R432161 : Reach 432161 := rs (se 2 (by rfl) ⟨162060, by rfl⟩) R324121
theorem R399613 : Reach 399613 := rs (se 3 (by rfl) ⟨74927, by rfl⟩) R149855
theorem R268541 : Reach 268541 := rs (se 3 (by rfl) ⟨50351, by rfl⟩) R100703
theorem R203033 : Reach 203033 := rs (se 2 (by rfl) ⟨76137, by rfl⟩) R152275
theorem R170351 : Reach 170351 := rs (se 1 (by rfl) ⟨127763, by rfl⟩) R255527
theorem R170423 : Reach 170423 := rs (se 1 (by rfl) ⟨127817, by rfl⟩) R255635
theorem R170567 : Reach 170567 := rs (se 1 (by rfl) ⟨127925, by rfl⟩) R255851
theorem R170603 : Reach 170603 := rs (se 1 (by rfl) ⟨127952, by rfl⟩) R255905
theorem R367211 : Reach 367211 := rs (se 1 (by rfl) ⟨275408, by rfl⟩) R550817
theorem R334475 : Reach 334475 := rs (se 1 (by rfl) ⟨250856, by rfl⟩) R501713
theorem R989891 : Reach 989891 := rs (se 1 (by rfl) ⟨742418, by rfl⟩) R1484837
theorem R367379 : Reach 367379 := rs (se 1 (by rfl) ⟨275534, by rfl⟩) R551069
theorem R400301 : Reach 400301 := rs (se 3 (by rfl) ⟨75056, by rfl⟩) R150113
theorem R170999 : Reach 170999 := rs (se 1 (by rfl) ⟨128249, by rfl⟩) R256499
theorem R171359 : Reach 171359 := rs (se 1 (by rfl) ⟨128519, by rfl⟩) R257039
theorem R171755 : Reach 171755 := rs (se 1 (by rfl) ⟨128816, by rfl⟩) R257633
theorem R171881 : Reach 171881 := rs (se 2 (by rfl) ⟨64455, by rfl⟩) R128911
theorem R467153 : Reach 467153 := rs (se 2 (by rfl) ⟨175182, by rfl⟩) R350365
theorem R4301009 : Reach 4301009 := rs (se 2 (by rfl) ⟨1612878, by rfl⟩) R3225757
theorem R205391 : Reach 205391 := rs (se 1 (by rfl) ⟨154043, by rfl⟩) R308087
theorem R107129 : Reach 107129 := rs (se 2 (by rfl) ⟨40173, by rfl⟩) R80347
theorem R1090219 : Reach 1090219 := rs (se 1 (by rfl) ⟨817664, by rfl⟩) R1635329
theorem R172727 : Reach 172727 := rs (se 1 (by rfl) ⟨129545, by rfl⟩) R259091
theorem R336683 : Reach 336683 := rs (se 1 (by rfl) ⟨252512, by rfl⟩) R505025
theorem R172943 : Reach 172943 := rs (se 1 (by rfl) ⟨129707, by rfl⟩) R259415
theorem R828305 : Reach 828305 := rs (se 2 (by rfl) ⟨310614, by rfl⟩) R621229
theorem R369809 : Reach 369809 := rs (se 2 (by rfl) ⟨138678, by rfl⟩) R277357
theorem R75175 : Reach 75175 := rs (se 1 (by rfl) ⟨56381, by rfl⟩) R112763
theorem R75259 : Reach 75259 := rs (se 1 (by rfl) ⟨56444, by rfl⟩) R112889
theorem R75327 : Reach 75327 := rs (se 1 (by rfl) ⟨56495, by rfl⟩) R112991
theorem R75335 : Reach 75335 := rs (se 1 (by rfl) ⟨56501, by rfl⟩) R113003
theorem R173663 : Reach 173663 := rs (se 1 (by rfl) ⟨130247, by rfl⟩) R260495
theorem R2991815 : Reach 2991815 := rs (se 1 (by rfl) ⟨2243861, by rfl⟩) R4487723
theorem R75487 : Reach 75487 := rs (se 1 (by rfl) ⟨56615, by rfl⟩) R113231
theorem R75567 : Reach 75567 := rs (se 1 (by rfl) ⟨56675, by rfl⟩) R113351
theorem R173879 : Reach 173879 := rs (se 1 (by rfl) ⟨130409, by rfl⟩) R260819
theorem R75675 : Reach 75675 := rs (se 1 (by rfl) ⟨56756, by rfl⟩) R113513
theorem R75727 : Reach 75727 := rs (se 1 (by rfl) ⟨56795, by rfl⟩) R113591
theorem R75751 : Reach 75751 := rs (se 1 (by rfl) ⟨56813, by rfl⟩) R113627
theorem R5023781 : Reach 5023781 := rs (se 4 (by rfl) ⟨470979, by rfl⟩) R941959
theorem R174185 : Reach 174185 := rs (se 2 (by rfl) ⟨65319, by rfl⟩) R130639
theorem R567425 : Reach 567425 := rs (se 2 (by rfl) ⟨212784, by rfl⟩) R425569
theorem R76063 : Reach 76063 := rs (se 1 (by rfl) ⟨57047, by rfl⟩) R114095
theorem R731429 : Reach 731429 := rs (se 4 (by rfl) ⟨68571, by rfl⟩) R137143
theorem R76123 : Reach 76123 := rs (se 1 (by rfl) ⟨57092, by rfl⟩) R114185
theorem R76143 : Reach 76143 := rs (se 1 (by rfl) ⟨57107, by rfl⟩) R114215
theorem R76199 : Reach 76199 := rs (se 1 (by rfl) ⟨57149, by rfl⟩) R114299
theorem R76283 : Reach 76283 := rs (se 1 (by rfl) ⟨57212, by rfl⟩) R114425
theorem R76351 : Reach 76351 := rs (se 1 (by rfl) ⟨57263, by rfl⟩) R114527
theorem R76359 : Reach 76359 := rs (se 1 (by rfl) ⟨57269, by rfl⟩) R114539
theorem R174671 : Reach 174671 := rs (se 1 (by rfl) ⟨131003, by rfl⟩) R262007
theorem R273091 : Reach 273091 := rs (se 1 (by rfl) ⟨204818, by rfl⟩) R409637
theorem R76511 : Reach 76511 := rs (se 1 (by rfl) ⟨57383, by rfl⟩) R114767
theorem R174815 : Reach 174815 := rs (se 1 (by rfl) ⟨131111, by rfl⟩) R262223
theorem R731927 : Reach 731927 := rs (se 1 (by rfl) ⟨548945, by rfl⟩) R1097891
theorem R76591 : Reach 76591 := rs (se 1 (by rfl) ⟨57443, by rfl⟩) R114887
theorem R76699 : Reach 76699 := rs (se 1 (by rfl) ⟨57524, by rfl⟩) R115049
theorem R76751 : Reach 76751 := rs (se 1 (by rfl) ⟨57563, by rfl⟩) R115127
theorem R175067 : Reach 175067 := rs (se 1 (by rfl) ⟨131300, by rfl⟩) R262601
theorem R76775 : Reach 76775 := rs (se 1 (by rfl) ⟨57581, by rfl⟩) R115163
theorem R2141315 : Reach 2141315 := rs (se 1 (by rfl) ⟨1605986, by rfl⟩) R3211973
theorem R175247 : Reach 175247 := rs (se 1 (by rfl) ⟨131435, by rfl⟩) R262871
theorem R175337 : Reach 175337 := rs (se 2 (by rfl) ⟨65751, by rfl⟩) R131503
theorem R208115 : Reach 208115 := rs (se 1 (by rfl) ⟨156086, by rfl⟩) R312173
theorem R77087 : Reach 77087 := rs (se 1 (by rfl) ⟨57815, by rfl⟩) R115631
theorem R175391 : Reach 175391 := rs (se 1 (by rfl) ⟨131543, by rfl⟩) R263087
theorem R77147 : Reach 77147 := rs (se 1 (by rfl) ⟨57860, by rfl⟩) R115721
theorem R77167 : Reach 77167 := rs (se 1 (by rfl) ⟨57875, by rfl⟩) R115751
theorem R241015 : Reach 241015 := rs (se 1 (by rfl) ⟨180761, by rfl⟩) R361523
theorem R77223 : Reach 77223 := rs (se 1 (by rfl) ⟨57917, by rfl⟩) R115835
theorem R77307 : Reach 77307 := rs (se 1 (by rfl) ⟨57980, by rfl⟩) R115961
theorem R77375 : Reach 77375 := rs (se 1 (by rfl) ⟨58031, by rfl⟩) R116063
theorem R77383 : Reach 77383 := rs (se 1 (by rfl) ⟨58037, by rfl⟩) R116075
theorem R503405 : Reach 503405 := rs (se 3 (by rfl) ⟨94388, by rfl⟩) R188777
theorem R77535 : Reach 77535 := rs (se 1 (by rfl) ⟨58151, by rfl⟩) R116303
theorem R569099 : Reach 569099 := rs (se 1 (by rfl) ⟨426824, by rfl⟩) R853649
theorem R175913 : Reach 175913 := rs (se 2 (by rfl) ⟨65967, by rfl⟩) R131935
theorem R77615 : Reach 77615 := rs (se 1 (by rfl) ⟨58211, by rfl⟩) R116423
theorem R77723 : Reach 77723 := rs (se 1 (by rfl) ⟨58292, by rfl⟩) R116585
theorem R77775 : Reach 77775 := rs (se 1 (by rfl) ⟨58331, by rfl⟩) R116663
theorem R77799 : Reach 77799 := rs (se 1 (by rfl) ⟨58349, by rfl⟩) R116699
theorem R1290329 : Reach 1290329 := rs (se 2 (by rfl) ⟨483873, by rfl⟩) R967747
theorem R78111 : Reach 78111 := rs (se 1 (by rfl) ⟨58583, by rfl⟩) R117167
theorem R78171 : Reach 78171 := rs (se 1 (by rfl) ⟨58628, by rfl⟩) R117257
theorem R78191 : Reach 78191 := rs (se 1 (by rfl) ⟨58643, by rfl⟩) R117287
theorem R78247 : Reach 78247 := rs (se 1 (by rfl) ⟨58685, by rfl⟩) R117371
theorem R373193 : Reach 373193 := rs (se 2 (by rfl) ⟨139947, by rfl⟩) R279895
theorem R78331 : Reach 78331 := rs (se 1 (by rfl) ⟨58748, by rfl⟩) R117497
theorem R78399 : Reach 78399 := rs (se 1 (by rfl) ⟨58799, by rfl⟩) R117599
theorem R78407 : Reach 78407 := rs (se 1 (by rfl) ⟨58805, by rfl⟩) R117611
theorem R242297 : Reach 242297 := rs (se 2 (by rfl) ⟨90861, by rfl⟩) R181723
theorem R143993 : Reach 143993 := rs (se 2 (by rfl) ⟨53997, by rfl⟩) R107995
theorem R242347 : Reach 242347 := rs (se 1 (by rfl) ⟨181760, by rfl⟩) R363521
theorem R78559 : Reach 78559 := rs (se 1 (by rfl) ⟨58919, by rfl⟩) R117839
theorem R78639 : Reach 78639 := rs (se 1 (by rfl) ⟨58979, by rfl⟩) R117959
theorem R176975 : Reach 176975 := rs (se 1 (by rfl) ⟨132731, by rfl⟩) R265463
theorem R406367 : Reach 406367 := rs (se 1 (by rfl) ⟨304775, by rfl⟩) R609551
theorem R78747 : Reach 78747 := rs (se 1 (by rfl) ⟨59060, by rfl⟩) R118121
theorem R78799 : Reach 78799 := rs (se 1 (by rfl) ⟨59099, by rfl⟩) R118199
theorem R78823 : Reach 78823 := rs (se 1 (by rfl) ⟨59117, by rfl⟩) R118235
theorem R177191 : Reach 177191 := rs (se 1 (by rfl) ⟨132893, by rfl⟩) R265787
theorem R898127 : Reach 898127 := rs (se 1 (by rfl) ⟨673595, by rfl⟩) R1347191
theorem R177371 : Reach 177371 := rs (se 1 (by rfl) ⟨133028, by rfl⟩) R266057
theorem R275699 : Reach 275699 := rs (se 1 (by rfl) ⟨206774, by rfl⟩) R413549
theorem R144737 : Reach 144737 := rs (se 2 (by rfl) ⟨54276, by rfl⟩) R108553
theorem R177569 : Reach 177569 := rs (se 2 (by rfl) ⟨66588, by rfl⟩) R133177
theorem R112745 : Reach 112745 := rs (se 2 (by rfl) ⟨42279, by rfl⟩) R84559
theorem R244079 : Reach 244079 := rs (se 1 (by rfl) ⟨183059, by rfl⟩) R366119
theorem R113063 : Reach 113063 := rs (se 1 (by rfl) ⟨84797, by rfl⟩) R169595
theorem R113147 : Reach 113147 := rs (se 1 (by rfl) ⟨84860, by rfl⟩) R169721
theorem R670315 : Reach 670315 := rs (se 1 (by rfl) ⟨502736, by rfl⟩) R1005473
theorem R113273 : Reach 113273 := rs (se 2 (by rfl) ⟨42477, by rfl⟩) R84955
theorem R113327 : Reach 113327 := rs (se 1 (by rfl) ⟨84995, by rfl⟩) R169991
theorem R113375 : Reach 113375 := rs (se 1 (by rfl) ⟨85031, by rfl⟩) R170063
theorem R146195 : Reach 146195 := rs (se 1 (by rfl) ⟨109646, by rfl⟩) R219293
theorem R113639 : Reach 113639 := rs (se 1 (by rfl) ⟨85229, by rfl⟩) R170459
theorem R146423 : Reach 146423 := rs (se 1 (by rfl) ⟨109817, by rfl⟩) R219635
theorem R113897 : Reach 113897 := rs (se 2 (by rfl) ⟨42711, by rfl⟩) R85423
theorem R113951 : Reach 113951 := rs (se 1 (by rfl) ⟨85463, by rfl⟩) R170927
theorem R114043 : Reach 114043 := rs (se 1 (by rfl) ⟨85532, by rfl⟩) R171065
theorem R114119 : Reach 114119 := rs (se 1 (by rfl) ⟨85589, by rfl⟩) R171179
theorem R245207 : Reach 245207 := rs (se 1 (by rfl) ⟨183905, by rfl⟩) R367811
theorem R736883 : Reach 736883 := rs (se 1 (by rfl) ⟨552662, by rfl⟩) R1105325
theorem R114473 : Reach 114473 := rs (se 2 (by rfl) ⟨42927, by rfl⟩) R85855
theorem R114479 : Reach 114479 := rs (se 1 (by rfl) ⟨85859, by rfl⟩) R171719
theorem R376883 : Reach 376883 := rs (se 1 (by rfl) ⟨282662, by rfl⟩) R565325
theorem R114953 : Reach 114953 := rs (se 2 (by rfl) ⟨43107, by rfl⟩) R86215
theorem R115055 : Reach 115055 := rs (se 1 (by rfl) ⟨86291, by rfl⟩) R172583
theorem R541129 : Reach 541129 := rs (se 2 (by rfl) ⟨202923, by rfl⟩) R405847
theorem R115271 : Reach 115271 := rs (se 1 (by rfl) ⟨86453, by rfl⟩) R172907
theorem R115307 : Reach 115307 := rs (se 1 (by rfl) ⟨86480, by rfl⟩) R172961
theorem R115535 : Reach 115535 := rs (se 1 (by rfl) ⟨86651, by rfl⟩) R173303
theorem R115931 : Reach 115931 := rs (se 1 (by rfl) ⟨86948, by rfl⟩) R173897
theorem R148775 : Reach 148775 := rs (se 1 (by rfl) ⟨111581, by rfl⟩) R223163
theorem R83311 : Reach 83311 := rs (se 1 (by rfl) ⟨62483, by rfl⟩) R124967
theorem R116105 : Reach 116105 := rs (se 2 (by rfl) ⟨43539, by rfl⟩) R87079
theorem R116459 : Reach 116459 := rs (se 1 (by rfl) ⟨87344, by rfl⟩) R174689
theorem R116687 : Reach 116687 := rs (se 1 (by rfl) ⟨87515, by rfl⟩) R175031
theorem R739343 : Reach 739343 := rs (se 1 (by rfl) ⟨554507, by rfl⟩) R1109015
theorem R117083 : Reach 117083 := rs (se 1 (by rfl) ⟨87812, by rfl⟩) R175625
theorem R1296773 : Reach 1296773 := rs (se 4 (by rfl) ⟨121572, by rfl⟩) R243145
theorem R117311 : Reach 117311 := rs (se 1 (by rfl) ⟨87983, by rfl⟩) R175967
theorem R117431 : Reach 117431 := rs (se 1 (by rfl) ⟨88073, by rfl⟩) R176147
theorem R84703 : Reach 84703 := rs (se 1 (by rfl) ⟨63527, by rfl⟩) R127055
theorem R379667 : Reach 379667 := rs (se 1 (by rfl) ⟨284750, by rfl⟩) R569501
theorem R117659 : Reach 117659 := rs (se 1 (by rfl) ⟨88244, by rfl⟩) R176489
theorem R216103 : Reach 216103 := rs (se 1 (by rfl) ⟨162077, by rfl⟩) R324155
theorem R674893 : Reach 674893 := rs (se 3 (by rfl) ⟨126542, by rfl⟩) R253085
theorem R85279 : Reach 85279 := rs (se 1 (by rfl) ⟨63959, by rfl⟩) R127919
theorem R118055 : Reach 118055 := rs (se 1 (by rfl) ⟨88541, by rfl⟩) R177083
theorem R118139 : Reach 118139 := rs (se 1 (by rfl) ⟨88604, by rfl⟩) R177209
theorem R380375 : Reach 380375 := rs (se 1 (by rfl) ⟨285281, by rfl⟩) R570563
theorem R118265 : Reach 118265 := rs (se 2 (by rfl) ⟨44349, by rfl⟩) R88699
theorem R1429001 : Reach 1429001 := rs (se 2 (by rfl) ⟨535875, by rfl⟩) R1071751
theorem R85567 : Reach 85567 := rs (se 1 (by rfl) ⟨64175, by rfl⟩) R128351
theorem R118367 : Reach 118367 := rs (se 1 (by rfl) ⟨88775, by rfl⟩) R177551
theorem R118583 : Reach 118583 := rs (se 1 (by rfl) ⟨88937, by rfl⟩) R177875
theorem R8605777 : Reach 8605777 := rs (se 2 (by rfl) ⟨3227166, by rfl⟩) R6454333
theorem R86303 : Reach 86303 := rs (se 1 (by rfl) ⟨64727, by rfl⟩) R129455
theorem R86395 : Reach 86395 := rs (se 1 (by rfl) ⟨64796, by rfl⟩) R129593
theorem R184751 : Reach 184751 := rs (se 1 (by rfl) ⟨138563, by rfl⟩) R277127
theorem R938557 : Reach 938557 := rs (se 3 (by rfl) ⟨175979, by rfl⟩) R351959
theorem R709181 : Reach 709181 := rs (se 3 (by rfl) ⟨132971, by rfl⟩) R265943
theorem R217721 : Reach 217721 := rs (se 2 (by rfl) ⟨81645, by rfl⟩) R163291
theorem R86863 : Reach 86863 := rs (se 1 (by rfl) ⟨65147, by rfl⟩) R130295
theorem R87259 : Reach 87259 := rs (se 1 (by rfl) ⟨65444, by rfl⟩) R130889
theorem R251113 : Reach 251113 := rs (se 2 (by rfl) ⟨94167, by rfl⟩) R188335
theorem R644345 : Reach 644345 := rs (se 2 (by rfl) ⟨241629, by rfl⟩) R483259
theorem R283943 : Reach 283943 := rs (se 1 (by rfl) ⟨212957, by rfl⟩) R425915
theorem R316781 : Reach 316781 := rs (se 3 (by rfl) ⟨59396, by rfl⟩) R118793
theorem R87547 : Reach 87547 := rs (se 1 (by rfl) ⟨65660, by rfl⟩) R131321
theorem R87727 : Reach 87727 := rs (se 1 (by rfl) ⟨65795, by rfl⟩) R131591
theorem R88015 : Reach 88015 := rs (se 1 (by rfl) ⟨66011, by rfl⟩) R132023
theorem R2840777 : Reach 2840777 := rs (se 2 (by rfl) ⟨1065291, by rfl⟩) R2130583
theorem R973079 : Reach 973079 := rs (se 1 (by rfl) ⟨729809, by rfl⟩) R1459619
theorem R88411 : Reach 88411 := rs (se 1 (by rfl) ⟨66308, by rfl⟩) R132617
theorem R88519 : Reach 88519 := rs (se 1 (by rfl) ⟨66389, by rfl⟩) R132779
theorem R186835 : Reach 186835 := rs (se 1 (by rfl) ⟨140126, by rfl⟩) R280253
theorem R88879 : Reach 88879 := rs (se 1 (by rfl) ⟨66659, by rfl⟩) R133319
theorem R88987 : Reach 88987 := rs (se 1 (by rfl) ⟨66740, by rfl⟩) R133481
theorem R220603 : Reach 220603 := rs (se 1 (by rfl) ⟨165452, by rfl⟩) R330905
theorem R155129 : Reach 155129 := rs (se 2 (by rfl) ⟨58173, by rfl⟩) R116347
theorem R188065 : Reach 188065 := rs (se 2 (by rfl) ⟨70524, by rfl⟩) R141049
theorem R876395 : Reach 876395 := rs (se 1 (by rfl) ⟨657296, by rfl⟩) R1314593
theorem R253853 : Reach 253853 := rs (se 3 (by rfl) ⟨47597, by rfl⟩) R95195
theorem R253961 : Reach 253961 := rs (se 2 (by rfl) ⟨95235, by rfl⟩) R190471
theorem R385235 : Reach 385235 := rs (se 1 (by rfl) ⟨288926, by rfl⟩) R577853
theorem R221767 : Reach 221767 := rs (se 1 (by rfl) ⟨166325, by rfl⟩) R332651
theorem R221879 : Reach 221879 := rs (se 1 (by rfl) ⟨166409, by rfl⟩) R332819
theorem R320215 : Reach 320215 := rs (se 1 (by rfl) ⟨240161, by rfl⟩) R480323
theorem R418823 : Reach 418823 := rs (se 1 (by rfl) ⟨314117, by rfl⟩) R628235
theorem R2450533 : Reach 2450533 := rs (se 4 (by rfl) ⟨229737, by rfl⟩) R459475
theorem R189911 : Reach 189911 := rs (se 1 (by rfl) ⟨142433, by rfl⟩) R284867
theorem R288593 : Reach 288593 := rs (se 2 (by rfl) ⟨108222, by rfl⟩) R216445
theorem R780167 : Reach 780167 := rs (se 1 (by rfl) ⟨585125, by rfl⟩) R1170251
theorem R190745 : Reach 190745 := rs (se 2 (by rfl) ⟨71529, by rfl⟩) R143059
theorem R551279 : Reach 551279 := rs (se 1 (by rfl) ⟨413459, by rfl⟩) R826919
theorem R1108669 : Reach 1108669 := rs (se 3 (by rfl) ⟨207875, by rfl⟩) R415751
theorem R191585 : Reach 191585 := rs (se 2 (by rfl) ⟨71844, by rfl⟩) R143689
theorem R257147 : Reach 257147 := rs (se 1 (by rfl) ⟨192860, by rfl⟩) R385721
theorem R257417 : Reach 257417 := rs (se 2 (by rfl) ⟨96531, by rfl⟩) R193063
theorem R290263 : Reach 290263 := rs (se 1 (by rfl) ⟨217697, by rfl⟩) R435395
theorem R224851 : Reach 224851 := rs (se 1 (by rfl) ⟨168638, by rfl⟩) R337277
theorem R913069 : Reach 913069 := rs (se 3 (by rfl) ⟨171200, by rfl⟩) R342401
theorem R1175233 : Reach 1175233 := rs (se 2 (by rfl) ⟨440712, by rfl⟩) R881425
theorem R1928933 : Reach 1928933 := rs (se 4 (by rfl) ⟨180837, by rfl⟩) R361675
theorem R290567 : Reach 290567 := rs (se 1 (by rfl) ⟨217925, by rfl⟩) R435851
theorem R257849 : Reach 257849 := rs (se 2 (by rfl) ⟨96693, by rfl⟩) R193387
theorem R257921 : Reach 257921 := rs (se 2 (by rfl) ⟨96720, by rfl⟩) R193441
theorem R585629 : Reach 585629 := rs (se 3 (by rfl) ⟨109805, by rfl⟩) R219611
theorem R127399 : Reach 127399 := rs (se 1 (by rfl) ⟨95549, by rfl⟩) R191099
theorem R160211 : Reach 160211 := rs (se 1 (by rfl) ⟨120158, by rfl⟩) R240317
theorem R193043 : Reach 193043 := rs (se 1 (by rfl) ⟨144782, by rfl⟩) R289565
theorem R94783 : Reach 94783 := rs (se 1 (by rfl) ⟨71087, by rfl⟩) R142175
theorem R127561 : Reach 127561 := rs (se 2 (by rfl) ⟨47835, by rfl⟩) R95671
theorem R127595 : Reach 127595 := rs (se 1 (by rfl) ⟨95696, by rfl⟩) R191393
theorem R1798807 : Reach 1798807 := rs (se 1 (by rfl) ⟨1349105, by rfl⟩) R2698211
theorem R258713 : Reach 258713 := rs (se 2 (by rfl) ⟨97017, by rfl⟩) R194035
theorem R324395 : Reach 324395 := rs (se 1 (by rfl) ⟨243296, by rfl⟩) R486593
theorem R193499 : Reach 193499 := rs (se 1 (by rfl) ⟨145124, by rfl⟩) R290249
theorem R357473 : Reach 357473 := rs (se 2 (by rfl) ⟨134052, by rfl⟩) R268105
theorem R324755 : Reach 324755 := rs (se 1 (by rfl) ⟨243566, by rfl⟩) R487133
theorem R160967 : Reach 160967 := rs (se 1 (by rfl) ⟨120725, by rfl⟩) R241451
theorem R95519 : Reach 95519 := rs (se 1 (by rfl) ⟨71639, by rfl⟩) R143279
theorem R193823 : Reach 193823 := rs (se 1 (by rfl) ⟨145367, by rfl⟩) R290735
theorem R783917 : Reach 783917 := rs (se 3 (by rfl) ⟨146984, by rfl⟩) R293969
theorem R194359 : Reach 194359 := rs (se 1 (by rfl) ⟨145769, by rfl⟩) R291539
theorem R358199 : Reach 358199 := rs (se 1 (by rfl) ⟨268649, by rfl⟩) R537299
theorem R260225 : Reach 260225 := rs (se 2 (by rfl) ⟨97584, by rfl⟩) R195169
theorem R129289 : Reach 129289 := rs (se 2 (by rfl) ⟨48483, by rfl⟩) R96967
theorem R194825 : Reach 194825 := rs (se 2 (by rfl) ⟨73059, by rfl⟩) R146119
theorem R358823 : Reach 358823 := rs (se 1 (by rfl) ⟨269117, by rfl⟩) R538235
theorem R293371 : Reach 293371 := rs (se 1 (by rfl) ⟨220028, by rfl⟩) R440057
theorem R260603 : Reach 260603 := rs (se 1 (by rfl) ⟨195452, by rfl⟩) R390905
theorem R457289 : Reach 457289 := rs (se 2 (by rfl) ⟨171483, by rfl⟩) R342967
theorem R293483 : Reach 293483 := rs (se 1 (by rfl) ⟨220112, by rfl⟩) R440225
theorem R293651 : Reach 293651 := rs (se 1 (by rfl) ⟨220238, by rfl⟩) R440477
theorem R1899409 : Reach 1899409 := rs (se 2 (by rfl) ⟨712278, by rfl⟩) R1424557
theorem R261035 : Reach 261035 := rs (se 1 (by rfl) ⟨195776, by rfl⟩) R391553
theorem R228491 : Reach 228491 := rs (se 1 (by rfl) ⟨171368, by rfl⟩) R342737
theorem R982205 : Reach 982205 := rs (se 3 (by rfl) ⟨184163, by rfl⟩) R368327
theorem R195817 : Reach 195817 := rs (se 2 (by rfl) ⟨73431, by rfl⟩) R146863
theorem R589193 : Reach 589193 := rs (se 2 (by rfl) ⟨220947, by rfl⟩) R441895
theorem R195979 : Reach 195979 := rs (se 1 (by rfl) ⟨146984, by rfl⟩) R293969
theorem R261575 : Reach 261575 := rs (se 1 (by rfl) ⟨196181, by rfl⟩) R392363
theorem R97787 : Reach 97787 := rs (se 1 (by rfl) ⟨73340, by rfl⟩) R146681
theorem R1146383 : Reach 1146383 := rs (se 1 (by rfl) ⟨859787, by rfl⟩) R1719575
theorem R130747 : Reach 130747 := rs (se 1 (by rfl) ⟨98060, by rfl⟩) R196121
theorem R196283 : Reach 196283 := rs (se 1 (by rfl) ⟨147212, by rfl⟩) R294425
theorem R261899 : Reach 261899 := rs (se 1 (by rfl) ⟨196424, by rfl⟩) R392849
theorem R196481 : Reach 196481 := rs (se 2 (by rfl) ⟨73680, by rfl⟩) R147361
theorem R393497 : Reach 393497 := rs (se 2 (by rfl) ⟨147561, by rfl⟩) R295123
theorem R197063 : Reach 197063 := rs (se 1 (by rfl) ⟨147797, by rfl⟩) R295595
theorem R328187 : Reach 328187 := rs (se 1 (by rfl) ⟨246140, by rfl⟩) R492281
theorem R721505 : Reach 721505 := rs (se 2 (by rfl) ⟨270564, by rfl⟩) R541129
theorem R262763 : Reach 262763 := rs (se 1 (by rfl) ⟨197072, by rfl⟩) R394145
theorem R230141 : Reach 230141 := rs (se 3 (by rfl) ⟨43151, by rfl⟩) R86303
theorem R131881 : Reach 131881 := rs (se 2 (by rfl) ⟨49455, by rfl⟩) R98911
theorem R328495 : Reach 328495 := rs (se 1 (by rfl) ⟨246371, by rfl⟩) R492743
theorem R426953 : Reach 426953 := rs (se 2 (by rfl) ⟨160107, by rfl⟩) R320215
theorem R132151 : Reach 132151 := rs (se 1 (by rfl) ⟨99113, by rfl⟩) R198227
theorem R263357 : Reach 263357 := rs (se 3 (by rfl) ⟨49379, by rfl⟩) R98759
theorem R492895 : Reach 492895 := rs (se 1 (by rfl) ⟨369671, by rfl⟩) R739343
theorem R853523 : Reach 853523 := rs (se 1 (by rfl) ⟨640142, by rfl⟩) R1280285
theorem R133103 : Reach 133103 := rs (se 1 (by rfl) ⟨99827, by rfl⟩) R199655
theorem R264383 : Reach 264383 := rs (se 1 (by rfl) ⟨198287, by rfl⟩) R396575
theorem R526571 : Reach 526571 := rs (se 1 (by rfl) ⟨394928, by rfl⟩) R789857
theorem R395567 : Reach 395567 := rs (se 1 (by rfl) ⟨296675, by rfl⟩) R593351
theorem R952667 : Reach 952667 := rs (se 1 (by rfl) ⟨714500, by rfl⟩) R1429001
theorem R199007 : Reach 199007 := rs (se 1 (by rfl) ⟨149255, by rfl⟩) R298511
theorem R199199 : Reach 199199 := rs (se 1 (by rfl) ⟨149399, by rfl⟩) R298799
theorem R1182757 : Reach 1182757 := rs (se 4 (by rfl) ⟨110883, by rfl⟩) R221767
theorem R429245 : Reach 429245 := rs (se 3 (by rfl) ⟨80483, by rfl⟩) R160967
theorem R396733 : Reach 396733 := rs (se 3 (by rfl) ⟨74387, by rfl⟩) R148775
theorem R757181 : Reach 757181 := rs (se 3 (by rfl) ⟨141971, by rfl⟩) R283943
theorem R429563 : Reach 429563 := rs (se 1 (by rfl) ⟨322172, by rfl⟩) R644345
theorem R1478225 : Reach 1478225 := rs (se 2 (by rfl) ⟨554334, by rfl⟩) R1108669
theorem R462419 : Reach 462419 := rs (se 1 (by rfl) ⟨346814, by rfl⟩) R693629
theorem R364121 : Reach 364121 := rs (se 2 (by rfl) ⟨136545, by rfl⟩) R273091
theorem R266003 : Reach 266003 := rs (se 1 (by rfl) ⟨199502, by rfl⟩) R399005
theorem R135355 : Reach 135355 := rs (se 1 (by rfl) ⟨101516, by rfl⟩) R203033
theorem R659927 : Reach 659927 := rs (se 1 (by rfl) ⟨494945, by rfl⟩) R989891
theorem R266867 : Reach 266867 := rs (se 1 (by rfl) ⟨200150, by rfl⟩) R400301
theorem R299801 : Reach 299801 := rs (se 2 (by rfl) ⟨112425, by rfl⟩) R224851
theorem R1217425 : Reach 1217425 := rs (se 2 (by rfl) ⟨456534, by rfl⟩) R913069
theorem R169235 : Reach 169235 := rs (se 1 (by rfl) ⟨126926, by rfl⟩) R253853
theorem R169307 : Reach 169307 := rs (se 1 (by rfl) ⟨126980, by rfl⟩) R253961
theorem R11474369 : Reach 11474369 := rs (se 2 (by rfl) ⟨4302888, by rfl⟩) R8605777
theorem R136927 : Reach 136927 := rs (se 1 (by rfl) ⟨102695, by rfl⟩) R205391
theorem R169865 : Reach 169865 := rs (se 2 (by rfl) ⟨63699, by rfl⟩) R127399
theorem R1251409 : Reach 1251409 := rs (se 2 (by rfl) ⟨469278, by rfl⟩) R938557
theorem R170081 : Reach 170081 := rs (se 2 (by rfl) ⟨63780, by rfl⟩) R127561
theorem R2398409 : Reach 2398409 := rs (se 2 (by rfl) ⟨899403, by rfl⟩) R1798807
theorem R530729 : Reach 530729 := rs (se 2 (by rfl) ⟨199023, by rfl⟩) R398047
theorem R3349187 : Reach 3349187 := rs (se 1 (by rfl) ⟨2511890, by rfl⟩) R5023781
theorem R367519 : Reach 367519 := rs (se 1 (by rfl) ⟨275639, by rfl⟩) R551279
theorem R334817 : Reach 334817 := rs (se 2 (by rfl) ⟨125556, by rfl⟩) R251113
theorem R138281 : Reach 138281 := rs (se 2 (by rfl) ⟨51855, by rfl⟩) R103711
theorem R171431 : Reach 171431 := rs (se 1 (by rfl) ⟨128573, by rfl⟩) R257147
theorem R138743 : Reach 138743 := rs (se 1 (by rfl) ⟨104057, by rfl⟩) R208115
theorem R171611 : Reach 171611 := rs (se 1 (by rfl) ⟨128708, by rfl⟩) R257417
theorem R335603 : Reach 335603 := rs (se 1 (by rfl) ⟨251702, by rfl⟩) R503405
theorem R1285955 : Reach 1285955 := rs (se 1 (by rfl) ⟨964466, by rfl⟩) R1928933
theorem R171899 : Reach 171899 := rs (se 1 (by rfl) ⟨128924, by rfl⟩) R257849
theorem R171947 : Reach 171947 := rs (se 1 (by rfl) ⟨128960, by rfl⟩) R257921
theorem R860219 : Reach 860219 := rs (se 1 (by rfl) ⟨645164, by rfl⟩) R1290329
theorem R106807 : Reach 106807 := rs (se 1 (by rfl) ⟨80105, by rfl⟩) R160211
theorem R532817 : Reach 532817 := rs (se 2 (by rfl) ⟨199806, by rfl⟩) R399613
theorem R172385 : Reach 172385 := rs (se 2 (by rfl) ⟨64644, by rfl⟩) R129289
theorem R172475 : Reach 172475 := rs (se 1 (by rfl) ⟨129356, by rfl⟩) R258713
theorem R270911 : Reach 270911 := rs (se 1 (by rfl) ⟨203183, by rfl⟩) R406367
theorem R598751 : Reach 598751 := rs (se 1 (by rfl) ⟨449063, by rfl⟩) R898127
theorem R238315 : Reach 238315 := rs (se 1 (by rfl) ⟨178736, by rfl⟩) R357473
theorem R893753 : Reach 893753 := rs (se 2 (by rfl) ⟨335157, by rfl⟩) R670315
theorem R2532545 : Reach 2532545 := rs (se 2 (by rfl) ⟨949704, by rfl⟩) R1899409
theorem R238799 : Reach 238799 := rs (se 1 (by rfl) ⟨179099, by rfl⟩) R358199
theorem R75163 : Reach 75163 := rs (se 1 (by rfl) ⟨56372, by rfl⟩) R112745
theorem R173483 : Reach 173483 := rs (se 1 (by rfl) ⟨130112, by rfl⟩) R260225
theorem R75375 : Reach 75375 := rs (se 1 (by rfl) ⟨56531, by rfl⟩) R113063
theorem R239215 : Reach 239215 := rs (se 1 (by rfl) ⟨179411, by rfl⟩) R358823
theorem R75431 : Reach 75431 := rs (se 1 (by rfl) ⟨56573, by rfl⟩) R113147
theorem R173735 : Reach 173735 := rs (se 1 (by rfl) ⟨130301, by rfl⟩) R260603
theorem R304859 : Reach 304859 := rs (se 1 (by rfl) ⟨228644, by rfl⟩) R457289
theorem R75515 : Reach 75515 := rs (se 1 (by rfl) ⟨56636, by rfl⟩) R113273
theorem R75551 : Reach 75551 := rs (se 1 (by rfl) ⟨56663, by rfl⟩) R113327
theorem R75583 : Reach 75583 := rs (se 1 (by rfl) ⟨56687, by rfl⟩) R113375
theorem R174023 : Reach 174023 := rs (se 1 (by rfl) ⟨130517, by rfl⟩) R261035
theorem R75759 : Reach 75759 := rs (se 1 (by rfl) ⟨56819, by rfl⟩) R113639
theorem R75931 : Reach 75931 := rs (se 1 (by rfl) ⟨56948, by rfl⟩) R113897
theorem R75967 : Reach 75967 := rs (se 1 (by rfl) ⟨56975, by rfl⟩) R113951
theorem R174329 : Reach 174329 := rs (se 2 (by rfl) ⟨65373, by rfl⟩) R130747
theorem R76079 : Reach 76079 := rs (se 1 (by rfl) ⟨57059, by rfl⟩) R114119
theorem R174383 : Reach 174383 := rs (se 1 (by rfl) ⟨130787, by rfl⟩) R261575
theorem R764255 : Reach 764255 := rs (se 1 (by rfl) ⟨573191, by rfl⟩) R1146383
theorem R174599 : Reach 174599 := rs (se 1 (by rfl) ⟨130949, by rfl⟩) R261899
theorem R76315 : Reach 76315 := rs (se 1 (by rfl) ⟨57236, by rfl⟩) R114473
theorem R76319 : Reach 76319 := rs (se 1 (by rfl) ⟨57239, by rfl⟩) R114479
theorem R174779 : Reach 174779 := rs (se 1 (by rfl) ⟨131084, by rfl⟩) R262169
theorem R76635 : Reach 76635 := rs (se 1 (by rfl) ⟨57476, by rfl⟩) R114953
theorem R76703 : Reach 76703 := rs (se 1 (by rfl) ⟨57527, by rfl⟩) R115055
theorem R306139 : Reach 306139 := rs (se 1 (by rfl) ⟨229604, by rfl⟩) R459209
theorem R76847 : Reach 76847 := rs (se 1 (by rfl) ⟨57635, by rfl⟩) R115271
theorem R76871 : Reach 76871 := rs (se 1 (by rfl) ⟨57653, by rfl⟩) R115307
theorem R502919 : Reach 502919 := rs (se 1 (by rfl) ⟨377189, by rfl⟩) R754379
theorem R77023 : Reach 77023 := rs (se 1 (by rfl) ⟨57767, by rfl⟩) R115535
theorem R77287 : Reach 77287 := rs (se 1 (by rfl) ⟨57965, by rfl⟩) R115931
theorem R175607 : Reach 175607 := rs (se 1 (by rfl) ⟨131705, by rfl⟩) R263411
theorem R1453625 : Reach 1453625 := rs (se 2 (by rfl) ⟨545109, by rfl⟩) R1090219
theorem R175679 : Reach 175679 := rs (se 1 (by rfl) ⟨131759, by rfl⟩) R263519
theorem R77403 : Reach 77403 := rs (se 1 (by rfl) ⟨58052, by rfl⟩) R116105
theorem R77639 : Reach 77639 := rs (se 1 (by rfl) ⟨58229, by rfl⟩) R116459
theorem R77791 : Reach 77791 := rs (se 1 (by rfl) ⟨58343, by rfl⟩) R116687
theorem R78055 : Reach 78055 := rs (se 1 (by rfl) ⟨58541, by rfl⟩) R117083
theorem R864515 : Reach 864515 := rs (se 1 (by rfl) ⟨648386, by rfl⟩) R1296773
theorem R78207 : Reach 78207 := rs (se 1 (by rfl) ⟨58655, by rfl⟩) R117311
theorem R78287 : Reach 78287 := rs (se 1 (by rfl) ⟨58715, by rfl⟩) R117431
theorem R176633 : Reach 176633 := rs (se 2 (by rfl) ⟨66237, by rfl⟩) R132475
theorem R176723 : Reach 176723 := rs (se 1 (by rfl) ⟨132542, by rfl⟩) R265085
theorem R78439 : Reach 78439 := rs (se 1 (by rfl) ⟨58829, by rfl⟩) R117659
theorem R176903 : Reach 176903 := rs (se 1 (by rfl) ⟨132677, by rfl⟩) R265355
theorem R897821 : Reach 897821 := rs (se 3 (by rfl) ⟨168341, by rfl⟩) R336683
theorem R78703 : Reach 78703 := rs (se 1 (by rfl) ⟨59027, by rfl⟩) R118055
theorem R78759 : Reach 78759 := rs (se 1 (by rfl) ⟨59069, by rfl⟩) R118139
theorem R78843 : Reach 78843 := rs (se 1 (by rfl) ⟨59132, by rfl⟩) R118265
theorem R78911 : Reach 78911 := rs (se 1 (by rfl) ⟨59183, by rfl⟩) R118367
theorem R79055 : Reach 79055 := rs (se 1 (by rfl) ⟨59291, by rfl⟩) R118583
theorem R242963 : Reach 242963 := rs (se 1 (by rfl) ⟨182222, by rfl⟩) R364445
theorem R833111 : Reach 833111 := rs (se 1 (by rfl) ⟨624833, by rfl⟩) R1249667
theorem R472787 : Reach 472787 := rs (se 1 (by rfl) ⟨354590, by rfl⟩) R709181
theorem R145147 : Reach 145147 := rs (se 1 (by rfl) ⟨108860, by rfl⟩) R217721
theorem R177983 : Reach 177983 := rs (se 1 (by rfl) ⟨133487, by rfl⟩) R266975
theorem R309187 : Reach 309187 := rs (se 1 (by rfl) ⟨231890, by rfl⟩) R463781
theorem R243911 : Reach 243911 := rs (se 1 (by rfl) ⟨182933, by rfl⟩) R365867
theorem R211187 : Reach 211187 := rs (se 1 (by rfl) ⟨158390, by rfl⟩) R316781
theorem R112937 : Reach 112937 := rs (se 2 (by rfl) ⟨42351, by rfl⟩) R84703
theorem R112943 : Reach 112943 := rs (se 1 (by rfl) ⟨84707, by rfl⟩) R169415
theorem R113183 : Reach 113183 := rs (se 1 (by rfl) ⟨84887, by rfl⟩) R169775
theorem R899857 : Reach 899857 := rs (se 2 (by rfl) ⟨337446, by rfl⟩) R674893
theorem R179027 : Reach 179027 := rs (se 1 (by rfl) ⟨134270, by rfl⟩) R268541
theorem R113567 : Reach 113567 := rs (se 1 (by rfl) ⟨85175, by rfl⟩) R170351
theorem R113615 : Reach 113615 := rs (se 1 (by rfl) ⟨85211, by rfl⟩) R170423
theorem R113705 : Reach 113705 := rs (se 2 (by rfl) ⟨42639, by rfl⟩) R85279
theorem R113711 : Reach 113711 := rs (se 1 (by rfl) ⟨85283, by rfl⟩) R170567
theorem R113735 : Reach 113735 := rs (se 1 (by rfl) ⟨85301, by rfl⟩) R170603
theorem R244919 : Reach 244919 := rs (se 1 (by rfl) ⟨183689, by rfl⟩) R367379
theorem R113999 : Reach 113999 := rs (se 1 (by rfl) ⟨85499, by rfl⟩) R170999
theorem R114089 : Reach 114089 := rs (se 2 (by rfl) ⟨42783, by rfl⟩) R85567
theorem R114239 : Reach 114239 := rs (se 1 (by rfl) ⟨85679, by rfl⟩) R171359
theorem R114503 : Reach 114503 := rs (se 1 (by rfl) ⟨85877, by rfl⟩) R171755
theorem R114587 : Reach 114587 := rs (se 1 (by rfl) ⟨85940, by rfl⟩) R171881
theorem R311435 : Reach 311435 := rs (se 1 (by rfl) ⟨233576, by rfl⟩) R467153
theorem R2867339 : Reach 2867339 := rs (se 1 (by rfl) ⟨2150504, by rfl⟩) R4301009
theorem R115151 : Reach 115151 := rs (se 1 (by rfl) ⟨86363, by rfl⟩) R172727
theorem R147919 : Reach 147919 := rs (se 1 (by rfl) ⟨110939, by rfl⟩) R221879
theorem R115193 : Reach 115193 := rs (se 2 (by rfl) ⟨43197, by rfl⟩) R86395
theorem R115295 : Reach 115295 := rs (se 1 (by rfl) ⟨86471, by rfl⟩) R172943
theorem R279215 : Reach 279215 := rs (se 1 (by rfl) ⟨209411, by rfl⟩) R418823
theorem R246539 : Reach 246539 := rs (se 1 (by rfl) ⟨184904, by rfl⟩) R369809
theorem R115775 : Reach 115775 := rs (se 1 (by rfl) ⟨86831, by rfl⟩) R173663
theorem R115817 : Reach 115817 := rs (se 2 (by rfl) ⟨43431, by rfl⟩) R86863
theorem R115919 : Reach 115919 := rs (se 1 (by rfl) ⟨86939, by rfl⟩) R173879
theorem R116123 : Reach 116123 := rs (se 1 (by rfl) ⟨87092, by rfl⟩) R174185
theorem R378283 : Reach 378283 := rs (se 1 (by rfl) ⟨283712, by rfl⟩) R567425
theorem R116345 : Reach 116345 := rs (se 2 (by rfl) ⟨43629, by rfl⟩) R87259
theorem R116447 : Reach 116447 := rs (se 1 (by rfl) ⟨87335, by rfl⟩) R174671
theorem R116543 : Reach 116543 := rs (se 1 (by rfl) ⟨87407, by rfl⟩) R174815
theorem R444325 : Reach 444325 := rs (se 4 (by rfl) ⟨41655, by rfl⟩) R83311
theorem R116711 : Reach 116711 := rs (se 1 (by rfl) ⟨87533, by rfl⟩) R175067
theorem R116729 : Reach 116729 := rs (se 2 (by rfl) ⟨43773, by rfl⟩) R87547
theorem R1427543 : Reach 1427543 := rs (se 1 (by rfl) ⟨1070657, by rfl⟩) R2141315
theorem R116831 : Reach 116831 := rs (se 1 (by rfl) ⟨87623, by rfl⟩) R175247
theorem R116891 : Reach 116891 := rs (se 1 (by rfl) ⟨87668, by rfl⟩) R175337
theorem R116927 : Reach 116927 := rs (se 1 (by rfl) ⟨87695, by rfl⟩) R175391
theorem R116969 : Reach 116969 := rs (se 2 (by rfl) ⟨43863, by rfl⟩) R87727
theorem R379399 : Reach 379399 := rs (se 1 (by rfl) ⟨284549, by rfl⟩) R569099
theorem R117275 : Reach 117275 := rs (se 1 (by rfl) ⟨87956, by rfl⟩) R175913
theorem R117353 : Reach 117353 := rs (se 2 (by rfl) ⟨44007, by rfl⟩) R88015
theorem R248795 : Reach 248795 := rs (se 1 (by rfl) ⟨186596, by rfl⟩) R373193
theorem R85063 : Reach 85063 := rs (se 1 (by rfl) ⟨63797, by rfl⟩) R127595
theorem R117881 : Reach 117881 := rs (se 2 (by rfl) ⟨44205, by rfl⟩) R88411
theorem R216263 : Reach 216263 := rs (se 1 (by rfl) ⟨162197, by rfl⟩) R324395
theorem R117983 : Reach 117983 := rs (se 1 (by rfl) ⟨88487, by rfl⟩) R176975
theorem R118025 : Reach 118025 := rs (se 2 (by rfl) ⟨44259, by rfl⟩) R88519
theorem R249113 : Reach 249113 := rs (se 2 (by rfl) ⟨93417, by rfl⟩) R186835
theorem R118127 : Reach 118127 := rs (se 1 (by rfl) ⟨88595, by rfl⟩) R177191
theorem R216503 : Reach 216503 := rs (se 1 (by rfl) ⟨162377, by rfl⟩) R324755
theorem R118247 : Reach 118247 := rs (se 1 (by rfl) ⟨88685, by rfl⟩) R177371
theorem R183799 : Reach 183799 := rs (se 1 (by rfl) ⟨137849, by rfl⟩) R275699
theorem R1003013 : Reach 1003013 := rs (se 4 (by rfl) ⟨94032, by rfl⟩) R188065
theorem R118379 : Reach 118379 := rs (se 1 (by rfl) ⟨88784, by rfl⟩) R177569
theorem R118505 : Reach 118505 := rs (se 2 (by rfl) ⟨44439, by rfl⟩) R88879
theorem R118649 : Reach 118649 := rs (se 2 (by rfl) ⟨44493, by rfl⟩) R88987
theorem R413677 : Reach 413677 := rs (se 3 (by rfl) ⟨77564, by rfl⟩) R155129
theorem R152057 : Reach 152057 := rs (se 2 (by rfl) ⟨57021, by rfl⟩) R114043
theorem R152327 : Reach 152327 := rs (se 1 (by rfl) ⟨114245, by rfl⟩) R228491
theorem R251255 : Reach 251255 := rs (se 1 (by rfl) ⟨188441, by rfl⟩) R376883
theorem R87871 : Reach 87871 := rs (se 1 (by rfl) ⟨65903, by rfl⟩) R131807
theorem R1923047 : Reach 1923047 := rs (se 1 (by rfl) ⟨1442285, by rfl⟩) R2884571
theorem R88159 : Reach 88159 := rs (se 1 (by rfl) ⟨66119, by rfl⟩) R132239
theorem R3267377 : Reach 3267377 := rs (se 2 (by rfl) ⟨1225266, by rfl⟩) R2450533
theorem R285677 : Reach 285677 := rs (se 3 (by rfl) ⟨53564, by rfl⟩) R107129
theorem R351485 : Reach 351485 := rs (se 3 (by rfl) ⟨65903, by rfl⟩) R131807
theorem R1007113 : Reach 1007113 := rs (se 2 (by rfl) ⟨377667, by rfl⟩) R755335
theorem R220751 : Reach 220751 := rs (se 1 (by rfl) ⟨165563, by rfl⟩) R331127
theorem R253583 : Reach 253583 := rs (se 1 (by rfl) ⟨190187, by rfl⟩) R380375
theorem R1564645 : Reach 1564645 := rs (se 4 (by rfl) ⟨146685, by rfl⟩) R293371
theorem R1466383 : Reach 1466383 := rs (se 1 (by rfl) ⟨1099787, by rfl⟩) R2199575
theorem R123167 : Reach 123167 := rs (se 1 (by rfl) ⟨92375, by rfl⟩) R184751
theorem R221647 : Reach 221647 := rs (se 1 (by rfl) ⟨166235, by rfl⟩) R332471
theorem R254717 : Reach 254717 := rs (se 3 (by rfl) ⟨47759, by rfl⟩) R95519
theorem R222095 : Reach 222095 := rs (se 1 (by rfl) ⟨166571, by rfl⟩) R333143
theorem R288107 : Reach 288107 := rs (se 1 (by rfl) ⟨216080, by rfl⟩) R432161
theorem R288137 : Reach 288137 := rs (se 2 (by rfl) ⟨108051, by rfl⟩) R216103
theorem R1893851 : Reach 1893851 := rs (se 1 (by rfl) ⟨1420388, by rfl⟩) R2840777
theorem R648719 : Reach 648719 := rs (se 1 (by rfl) ⟨486539, by rfl⟩) R973079
theorem R222983 : Reach 222983 := rs (se 1 (by rfl) ⟨167237, by rfl⟩) R334475
theorem R321353 : Reach 321353 := rs (se 2 (by rfl) ⟨120507, by rfl⟩) R241015
theorem R387017 : Reach 387017 := rs (se 2 (by rfl) ⟨145131, by rfl⟩) R290263
theorem R1566977 : Reach 1566977 := rs (se 2 (by rfl) ⟨587616, by rfl⟩) R1175233
theorem R584263 : Reach 584263 := rs (se 1 (by rfl) ⟨438197, by rfl⟩) R876395
theorem R256823 : Reach 256823 := rs (se 1 (by rfl) ⟨192617, by rfl⟩) R385235
theorem R552203 : Reach 552203 := rs (se 1 (by rfl) ⟨414152, by rfl⟩) R828305
theorem R126377 : Reach 126377 := rs (se 2 (by rfl) ⟨47391, by rfl⟩) R94783
theorem R323129 : Reach 323129 := rs (se 2 (by rfl) ⟨121173, by rfl⟩) R242347
theorem R126607 : Reach 126607 := rs (se 1 (by rfl) ⟨94955, by rfl⟩) R189911
theorem R1994543 : Reach 1994543 := rs (se 1 (by rfl) ⟨1495907, by rfl⟩) R2991815
theorem R192395 : Reach 192395 := rs (se 1 (by rfl) ⟨144296, by rfl⟩) R288593
theorem R520111 : Reach 520111 := rs (se 1 (by rfl) ⟨390083, by rfl⟩) R780167
theorem R127163 : Reach 127163 := rs (se 1 (by rfl) ⟨95372, by rfl⟩) R190745
theorem R487619 : Reach 487619 := rs (se 1 (by rfl) ⟨365714, by rfl⟩) R731429
theorem R979229 : Reach 979229 := rs (se 3 (by rfl) ⟨183605, by rfl⟩) R367211
theorem R487951 : Reach 487951 := rs (se 1 (by rfl) ⟨365963, by rfl⟩) R731927
theorem R1012445 : Reach 1012445 := rs (se 3 (by rfl) ⟨189833, by rfl⟩) R379667
theorem R127723 : Reach 127723 := rs (se 1 (by rfl) ⟨95792, by rfl⟩) R191585
theorem R259145 : Reach 259145 := rs (se 2 (by rfl) ⟨97179, by rfl⟩) R194359
theorem R193711 : Reach 193711 := rs (se 1 (by rfl) ⟨145283, by rfl⟩) R290567
theorem R390419 : Reach 390419 := rs (se 1 (by rfl) ⟨292814, by rfl⟩) R585629
theorem R128695 : Reach 128695 := rs (se 1 (by rfl) ⟨96521, by rfl⟩) R193043
theorem R95995 : Reach 95995 := rs (se 1 (by rfl) ⟨71996, by rfl⟩) R143993
theorem R161531 : Reach 161531 := rs (se 1 (by rfl) ⟨121148, by rfl⟩) R242297
theorem R128999 : Reach 128999 := rs (se 1 (by rfl) ⟨96749, by rfl⟩) R193499
theorem R129215 : Reach 129215 := rs (se 1 (by rfl) ⟨96911, by rfl⟩) R193823
theorem R96491 : Reach 96491 := rs (se 1 (by rfl) ⟨72368, by rfl⟩) R144737
theorem R522611 : Reach 522611 := rs (se 1 (by rfl) ⟨391958, by rfl⟩) R783917
theorem R260765 : Reach 260765 := rs (se 3 (by rfl) ⟨48893, by rfl⟩) R97787
theorem R129883 : Reach 129883 := rs (se 1 (by rfl) ⟨97412, by rfl⟩) R194825
theorem R162719 : Reach 162719 := rs (se 1 (by rfl) ⟨122039, by rfl⟩) R244079
theorem R261089 : Reach 261089 := rs (se 2 (by rfl) ⟨97908, by rfl⟩) R195817
theorem R195655 : Reach 195655 := rs (se 1 (by rfl) ⟨146741, by rfl⟩) R293483
theorem R97463 : Reach 97463 := rs (se 1 (by rfl) ⟨73097, by rfl⟩) R146195
theorem R195767 : Reach 195767 := rs (se 1 (by rfl) ⟨146825, by rfl⟩) R293651
theorem R261305 : Reach 261305 := rs (se 2 (by rfl) ⟨97989, by rfl⟩) R195979
theorem R294137 : Reach 294137 := rs (se 2 (by rfl) ⟨110301, by rfl⟩) R220603
theorem R97615 : Reach 97615 := rs (se 1 (by rfl) ⟨73211, by rfl⟩) R146423
theorem R654803 : Reach 654803 := rs (se 1 (by rfl) ⟨491102, by rfl⟩) R982205
theorem R392795 : Reach 392795 := rs (se 1 (by rfl) ⟨294596, by rfl⟩) R589193
theorem R163471 : Reach 163471 := rs (se 1 (by rfl) ⟨122603, by rfl⟩) R245207
theorem R491255 : Reach 491255 := rs (se 1 (by rfl) ⟨368441, by rfl⟩) R736883
theorem R130855 : Reach 130855 := rs (se 1 (by rfl) ⟨98141, by rfl⟩) R196283
theorem R130987 : Reach 130987 := rs (se 1 (by rfl) ⟨98240, by rfl⟩) R196481
theorem R262331 : Reach 262331 := rs (se 1 (by rfl) ⟨196748, by rfl⟩) R393497
theorem R131375 : Reach 131375 := rs (se 1 (by rfl) ⟨98531, by rfl⟩) R197063
theorem R164359 : Reach 164359 := rs (se 1 (by rfl) ⟨123269, by rfl⟩) R246539
theorem R295529 : Reach 295529 := rs (se 2 (by rfl) ⟨110823, by rfl⟩) R221647
theorem R197225 : Reach 197225 := rs (se 2 (by rfl) ⟨73959, by rfl⟩) R147919
theorem R328445 : Reach 328445 := rs (se 3 (by rfl) ⟨61583, by rfl⟩) R123167
theorem R951695 : Reach 951695 := rs (se 1 (by rfl) ⟨713771, by rfl⟩) R1427543
theorem R722429 : Reach 722429 := rs (se 3 (by rfl) ⟨135455, by rfl⟩) R270911
theorem R263711 : Reach 263711 := rs (se 1 (by rfl) ⟨197783, by rfl⟩) R395567
theorem R132671 : Reach 132671 := rs (se 1 (by rfl) ⟨99503, by rfl⟩) R199007
theorem R132799 : Reach 132799 := rs (se 1 (by rfl) ⟨99599, by rfl⟩) R199199
theorem R657193 : Reach 657193 := rs (se 2 (by rfl) ⟨246447, by rfl⟩) R492895
theorem R165863 : Reach 165863 := rs (se 1 (by rfl) ⟨124397, by rfl⟩) R248795
theorem R985483 : Reach 985483 := rs (se 1 (by rfl) ⟨739112, by rfl⟩) R1478225
theorem R592433 : Reach 592433 := rs (se 2 (by rfl) ⟨222162, by rfl⟩) R444325
theorem R16714421 : Reach 16714421 := rs (se 5 (by rfl) ⟨783488, by rfl⟩) R1566977
theorem R199867 : Reach 199867 := rs (se 1 (by rfl) ⟨149900, by rfl⟩) R299801
theorem R167503 : Reach 167503 := rs (se 1 (by rfl) ⟨125627, by rfl⟩) R251255
theorem R1282031 : Reach 1282031 := rs (se 1 (by rfl) ⟨961523, by rfl⟩) R1923047
theorem R1577009 : Reach 1577009 := rs (se 2 (by rfl) ⟨591378, by rfl⟩) R1182757
theorem R2232791 : Reach 2232791 := rs (se 1 (by rfl) ⟨1674593, by rfl⟩) R3349187
theorem R528977 : Reach 528977 := rs (se 2 (by rfl) ⟨198366, by rfl⟩) R396733
theorem R234323 : Reach 234323 := rs (se 1 (by rfl) ⟨175742, by rfl⟩) R351485
theorem R168809 : Reach 168809 := rs (se 2 (by rfl) ⟨63303, by rfl⟩) R126607
theorem R169055 : Reach 169055 := rs (se 1 (by rfl) ⟨126791, by rfl⟩) R253583
theorem R857303 : Reach 857303 := rs (se 1 (by rfl) ⟨642977, by rfl⟩) R1285955
theorem R693481 : Reach 693481 := rs (se 2 (by rfl) ⟨260055, by rfl⟩) R520111
theorem R399167 : Reach 399167 := rs (se 1 (by rfl) ⟨299375, by rfl⟩) R598751
theorem R169811 : Reach 169811 := rs (se 1 (by rfl) ⟨127358, by rfl⟩) R254717
theorem R595835 : Reach 595835 := rs (se 1 (by rfl) ⟨446876, by rfl⟩) R893753
theorem R170297 : Reach 170297 := rs (se 2 (by rfl) ⟨63861, by rfl⟩) R127723
theorem R432479 : Reach 432479 := rs (se 1 (by rfl) ⟨324359, by rfl⟩) R648719
theorem R203239 : Reach 203239 := rs (se 1 (by rfl) ⟨152429, by rfl⟩) R304859
theorem R171215 : Reach 171215 := rs (se 1 (by rfl) ⟨128411, by rfl⟩) R256823
theorem R335279 : Reach 335279 := rs (se 1 (by rfl) ⟨251459, by rfl⟩) R502919
theorem R368135 : Reach 368135 := rs (se 1 (by rfl) ⟨276101, by rfl⟩) R552203
theorem R171593 : Reach 171593 := rs (se 2 (by rfl) ⟨64347, by rfl⟩) R128695
theorem R368749 : Reach 368749 := rs (se 3 (by rfl) ⟨69140, by rfl⟩) R138281
theorem R598547 : Reach 598547 := rs (se 1 (by rfl) ⟨448910, by rfl⟩) R897821
theorem R172763 : Reach 172763 := rs (se 1 (by rfl) ⟨129572, by rfl⟩) R259145
theorem R664301 : Reach 664301 := rs (se 3 (by rfl) ⟨124556, by rfl⟩) R249113
theorem R173177 : Reach 173177 := rs (se 2 (by rfl) ⟨64941, by rfl⟩) R129883
theorem R107687 : Reach 107687 := rs (se 1 (by rfl) ⟨80765, by rfl⟩) R161531
theorem R861677 : Reach 861677 := rs (se 3 (by rfl) ⟨161564, by rfl⟩) R323129
theorem R140791 : Reach 140791 := rs (se 1 (by rfl) ⟨105593, by rfl⟩) R211187
theorem R75291 : Reach 75291 := rs (se 1 (by rfl) ⟨56468, by rfl⟩) R112937
theorem R75295 : Reach 75295 := rs (se 1 (by rfl) ⟨56471, by rfl⟩) R112943
theorem R75455 : Reach 75455 := rs (se 1 (by rfl) ⟨56591, by rfl⟩) R113183
theorem R173843 : Reach 173843 := rs (se 1 (by rfl) ⟨130382, by rfl⟩) R260765
theorem R75711 : Reach 75711 := rs (se 1 (by rfl) ⟨56783, by rfl⟩) R113567
theorem R108479 : Reach 108479 := rs (se 1 (by rfl) ⟨81359, by rfl⟩) R162719
theorem R75743 : Reach 75743 := rs (se 1 (by rfl) ⟨56807, by rfl⟩) R113615
theorem R174059 : Reach 174059 := rs (se 1 (by rfl) ⟨130544, by rfl⟩) R261089
theorem R75803 : Reach 75803 := rs (se 1 (by rfl) ⟨56852, by rfl⟩) R113705
theorem R75807 : Reach 75807 := rs (se 1 (by rfl) ⟨56855, by rfl⟩) R113711
theorem R75823 : Reach 75823 := rs (se 1 (by rfl) ⟨56867, by rfl⟩) R113735
theorem R174203 : Reach 174203 := rs (se 1 (by rfl) ⟨130652, by rfl⟩) R261305
theorem R75999 : Reach 75999 := rs (se 1 (by rfl) ⟨56999, by rfl⟩) R113999
theorem R76059 : Reach 76059 := rs (se 1 (by rfl) ⟨57044, by rfl⟩) R114089
theorem R436535 : Reach 436535 := rs (se 1 (by rfl) ⟨327401, by rfl⟩) R654803
theorem R1648997 : Reach 1648997 := rs (se 4 (by rfl) ⟨154593, by rfl⟩) R309187
theorem R76159 : Reach 76159 := rs (se 1 (by rfl) ⟨57119, by rfl⟩) R114239
theorem R174473 : Reach 174473 := rs (se 2 (by rfl) ⟨65427, by rfl⟩) R130855
theorem R76335 : Reach 76335 := rs (se 1 (by rfl) ⟨57251, by rfl⟩) R114503
theorem R174649 : Reach 174649 := rs (se 2 (by rfl) ⟨65493, by rfl⟩) R130987
theorem R76391 : Reach 76391 := rs (se 1 (by rfl) ⟨57293, by rfl⟩) R114587
theorem R207623 : Reach 207623 := rs (se 1 (by rfl) ⟨155717, by rfl⟩) R311435
theorem R1911559 : Reach 1911559 := rs (se 1 (by rfl) ⟨1433669, by rfl⟩) R2867339
theorem R76767 : Reach 76767 := rs (se 1 (by rfl) ⟨57575, by rfl⟩) R115151
theorem R76795 : Reach 76795 := rs (se 1 (by rfl) ⟨57596, by rfl⟩) R115193
theorem R76863 : Reach 76863 := rs (se 1 (by rfl) ⟨57647, by rfl⟩) R115295
theorem R175175 : Reach 175175 := rs (se 1 (by rfl) ⟨131381, by rfl⟩) R262763
theorem R142409 : Reach 142409 := rs (se 2 (by rfl) ⟨53403, by rfl⟩) R106807
theorem R77183 : Reach 77183 := rs (se 1 (by rfl) ⟨57887, by rfl⟩) R115775
theorem R77211 : Reach 77211 := rs (se 1 (by rfl) ⟨57908, by rfl⟩) R115817
theorem R175571 : Reach 175571 := rs (se 1 (by rfl) ⟨131678, by rfl⟩) R263357
theorem R77279 : Reach 77279 := rs (se 1 (by rfl) ⟨57959, by rfl⟩) R115919
theorem R77415 : Reach 77415 := rs (se 1 (by rfl) ⟨58061, by rfl⟩) R116123
theorem R569015 : Reach 569015 := rs (se 1 (by rfl) ⟨426761, by rfl⟩) R853523
theorem R175841 : Reach 175841 := rs (se 2 (by rfl) ⟨65940, by rfl⟩) R131881
theorem R437993 : Reach 437993 := rs (se 2 (by rfl) ⟨164247, by rfl⟩) R328495
theorem R77563 : Reach 77563 := rs (se 1 (by rfl) ⟨58172, by rfl⟩) R116345
theorem R77631 : Reach 77631 := rs (se 1 (by rfl) ⟨58223, by rfl⟩) R116447
theorem R77695 : Reach 77695 := rs (se 1 (by rfl) ⟨58271, by rfl⟩) R116543
theorem R405485 : Reach 405485 := rs (se 3 (by rfl) ⟨76028, by rfl⟩) R152057
theorem R77807 : Reach 77807 := rs (se 1 (by rfl) ⟨58355, by rfl⟩) R116711
theorem R77819 : Reach 77819 := rs (se 1 (by rfl) ⟨58364, by rfl⟩) R116729
theorem R77887 : Reach 77887 := rs (se 1 (by rfl) ⟨58415, by rfl⟩) R116831
theorem R176201 : Reach 176201 := rs (se 2 (by rfl) ⟨66075, by rfl⟩) R132151
theorem R77927 : Reach 77927 := rs (se 1 (by rfl) ⟨58445, by rfl⟩) R116891
theorem R77951 : Reach 77951 := rs (se 1 (by rfl) ⟨58463, by rfl⟩) R116927
theorem R176255 : Reach 176255 := rs (se 1 (by rfl) ⟨132191, by rfl⟩) R264383
theorem R77979 : Reach 77979 := rs (se 1 (by rfl) ⟨58484, by rfl⟩) R116969
theorem R635111 : Reach 635111 := rs (se 1 (by rfl) ⟨476333, by rfl⟩) R952667
theorem R78183 : Reach 78183 := rs (se 1 (by rfl) ⟨58637, by rfl⟩) R117275
theorem R78235 : Reach 78235 := rs (se 1 (by rfl) ⟨58676, by rfl⟩) R117353
theorem R504377 : Reach 504377 := rs (se 2 (by rfl) ⟨189141, by rfl⟩) R378283
theorem R406205 : Reach 406205 := rs (se 3 (by rfl) ⟨76163, by rfl⟩) R152327
theorem R78587 : Reach 78587 := rs (se 1 (by rfl) ⟨58940, by rfl⟩) R117881
theorem R144175 : Reach 144175 := rs (se 1 (by rfl) ⟨108131, by rfl⟩) R216263
theorem R78655 : Reach 78655 := rs (se 1 (by rfl) ⟨58991, by rfl⟩) R117983
theorem R78683 : Reach 78683 := rs (se 1 (by rfl) ⟨59012, by rfl⟩) R118025
theorem R78751 : Reach 78751 := rs (se 1 (by rfl) ⟨59063, by rfl⟩) R118127
theorem R144335 : Reach 144335 := rs (se 1 (by rfl) ⟨108251, by rfl⟩) R216503
theorem R504787 : Reach 504787 := rs (se 1 (by rfl) ⟨378590, by rfl⟩) R757181
theorem R78831 : Reach 78831 := rs (se 1 (by rfl) ⟨59123, by rfl⟩) R118247
theorem R668675 : Reach 668675 := rs (se 1 (by rfl) ⟨501506, by rfl⟩) R1003013
theorem R308279 : Reach 308279 := rs (se 1 (by rfl) ⟨231209, by rfl⟩) R462419
theorem R242747 : Reach 242747 := rs (se 1 (by rfl) ⟨182060, by rfl⟩) R364121
theorem R78919 : Reach 78919 := rs (se 1 (by rfl) ⟨59189, by rfl⟩) R118379
theorem R79003 : Reach 79003 := rs (se 1 (by rfl) ⟨59252, by rfl⟩) R118505
theorem R177335 : Reach 177335 := rs (se 1 (by rfl) ⟨133001, by rfl⟩) R266003
theorem R79099 : Reach 79099 := rs (se 1 (by rfl) ⟨59324, by rfl⟩) R118649
theorem R2602405 : Reach 2602405 := rs (se 4 (by rfl) ⟨243975, by rfl⟩) R487951
theorem R439951 : Reach 439951 := rs (se 1 (by rfl) ⟨329963, by rfl⟩) R659927
theorem R177911 : Reach 177911 := rs (se 1 (by rfl) ⟨133433, by rfl⟩) R266867
theorem R636797 : Reach 636797 := rs (se 3 (by rfl) ⟨119399, by rfl⟩) R238799
theorem R505865 : Reach 505865 := rs (se 2 (by rfl) ⟨189699, by rfl⟩) R379399
theorem R112823 : Reach 112823 := rs (se 1 (by rfl) ⟨84617, by rfl⟩) R169235
theorem R112871 : Reach 112871 := rs (se 1 (by rfl) ⟨84653, by rfl⟩) R169307
theorem R7649579 : Reach 7649579 := rs (se 1 (by rfl) ⟨5737184, by rfl⟩) R11474369
theorem R113243 : Reach 113243 := rs (se 1 (by rfl) ⟨84932, by rfl⟩) R169865
theorem R408185 : Reach 408185 := rs (se 2 (by rfl) ⟨153069, by rfl⟩) R306139
theorem R113387 : Reach 113387 := rs (se 1 (by rfl) ⟨85040, by rfl⟩) R170081
theorem R113417 : Reach 113417 := rs (se 2 (by rfl) ⟨42531, by rfl⟩) R85063
theorem R2178251 : Reach 2178251 := rs (se 1 (by rfl) ⟨1633688, by rfl⟩) R3267377
theorem R245065 : Reach 245065 := rs (se 2 (by rfl) ⟨91899, by rfl⟩) R183799
theorem R114287 : Reach 114287 := rs (se 1 (by rfl) ⟨85715, by rfl⟩) R171431
theorem R147167 : Reach 147167 := rs (se 1 (by rfl) ⟨110375, by rfl⟩) R220751
theorem R114407 : Reach 114407 := rs (se 1 (by rfl) ⟨85805, by rfl⟩) R171611
theorem R114599 : Reach 114599 := rs (se 1 (by rfl) ⟨85949, by rfl⟩) R171899
theorem R114631 : Reach 114631 := rs (se 1 (by rfl) ⟨85973, by rfl⟩) R171947
theorem R573479 : Reach 573479 := rs (se 1 (by rfl) ⟨430109, by rfl⟩) R860219
theorem R114923 : Reach 114923 := rs (se 1 (by rfl) ⟨86192, by rfl⟩) R172385
theorem R180473 : Reach 180473 := rs (se 2 (by rfl) ⟨67677, by rfl⟩) R135355
theorem R114983 : Reach 114983 := rs (se 1 (by rfl) ⟨86237, by rfl⟩) R172475
theorem R148063 : Reach 148063 := rs (se 1 (by rfl) ⟨111047, by rfl⟩) R222095
theorem R1688363 : Reach 1688363 := rs (se 1 (by rfl) ⟨1266272, by rfl⟩) R2532545
theorem R115655 : Reach 115655 := rs (se 1 (by rfl) ⟨86741, by rfl⟩) R173483
theorem R1262567 : Reach 1262567 := rs (se 1 (by rfl) ⟨946925, by rfl⟩) R1893851
theorem R115823 : Reach 115823 := rs (se 1 (by rfl) ⟨86867, by rfl⟩) R173735
theorem R148655 : Reach 148655 := rs (se 1 (by rfl) ⟨111491, by rfl⟩) R222983
theorem R1623233 : Reach 1623233 := rs (se 2 (by rfl) ⟨608712, by rfl⟩) R1217425
theorem R214235 : Reach 214235 := rs (se 1 (by rfl) ⟨160676, by rfl⟩) R321353
theorem R116015 : Reach 116015 := rs (se 1 (by rfl) ⟨87011, by rfl⟩) R174023
theorem R116219 : Reach 116219 := rs (se 1 (by rfl) ⟨87164, by rfl⟩) R174329
theorem R116255 : Reach 116255 := rs (se 1 (by rfl) ⟨87191, by rfl⟩) R174383
theorem R509503 : Reach 509503 := rs (se 1 (by rfl) ⟨382127, by rfl⟩) R764255
theorem R116399 : Reach 116399 := rs (se 1 (by rfl) ⟨87299, by rfl⟩) R174599
theorem R116519 : Reach 116519 := rs (se 1 (by rfl) ⟨87389, by rfl⟩) R174779
theorem R84251 : Reach 84251 := rs (se 1 (by rfl) ⟨63188, by rfl⟩) R126377
theorem R182569 : Reach 182569 := rs (se 2 (by rfl) ⟨68463, by rfl⟩) R136927
theorem R117071 : Reach 117071 := rs (se 1 (by rfl) ⟨87803, by rfl⟩) R175607
theorem R969083 : Reach 969083 := rs (se 1 (by rfl) ⟨726812, by rfl⟩) R1453625
theorem R117119 : Reach 117119 := rs (se 1 (by rfl) ⟨87839, by rfl⟩) R175679
theorem R117161 : Reach 117161 := rs (se 2 (by rfl) ⟨43935, by rfl⟩) R87871
theorem R1329695 : Reach 1329695 := rs (se 1 (by rfl) ⟨997271, by rfl⟩) R1994543
theorem R84775 : Reach 84775 := rs (se 1 (by rfl) ⟨63581, by rfl⟩) R127163
theorem R117545 : Reach 117545 := rs (se 2 (by rfl) ⟨44079, by rfl⟩) R88159
theorem R576343 : Reach 576343 := rs (se 1 (by rfl) ⟨432257, by rfl⟩) R864515
theorem R117755 : Reach 117755 := rs (se 1 (by rfl) ⟨88316, by rfl⟩) R176633
theorem R117815 : Reach 117815 := rs (se 1 (by rfl) ⟨88361, by rfl⟩) R176723
theorem R674963 : Reach 674963 := rs (se 1 (by rfl) ⟨506222, by rfl⟩) R1012445
theorem R117935 : Reach 117935 := rs (se 1 (by rfl) ⟨88451, by rfl⟩) R176903
theorem R314621 : Reach 314621 := rs (se 3 (by rfl) ⟨58991, by rfl⟩) R117983
theorem R1199809 : Reach 1199809 := rs (se 2 (by rfl) ⟨449928, by rfl⟩) R899857
theorem R315191 : Reach 315191 := rs (se 1 (by rfl) ⟨236393, by rfl⟩) R472787
theorem R118655 : Reach 118655 := rs (se 1 (by rfl) ⟨88991, by rfl⟩) R177983
theorem R85999 : Reach 85999 := rs (se 1 (by rfl) ⟨64499, by rfl⟩) R128999
theorem R86143 : Reach 86143 := rs (se 1 (by rfl) ⟨64607, by rfl⟩) R129215
theorem R348407 : Reach 348407 := rs (se 1 (by rfl) ⟨261305, by rfl⟩) R522611
theorem R119351 : Reach 119351 := rs (se 1 (by rfl) ⟨89513, by rfl⟩) R179027
theorem R217961 : Reach 217961 := rs (se 2 (by rfl) ⟨81735, by rfl⟩) R163471
theorem R2086193 : Reach 2086193 := rs (se 2 (by rfl) ⟨782322, by rfl⟩) R1564645
theorem R1955177 : Reach 1955177 := rs (se 2 (by rfl) ⟨733191, by rfl⟩) R1466383
theorem R218791 : Reach 218791 := rs (se 1 (by rfl) ⟨164093, by rfl⟩) R328187
theorem R186143 : Reach 186143 := rs (se 1 (by rfl) ⟨139607, by rfl⟩) R279215
theorem R153427 : Reach 153427 := rs (se 1 (by rfl) ⟨115070, by rfl⟩) R230141
theorem R284635 : Reach 284635 := rs (se 1 (by rfl) ⟨213476, by rfl⟩) R426953
theorem R317753 : Reach 317753 := rs (se 2 (by rfl) ⟨119157, by rfl⟩) R238315
theorem R88735 : Reach 88735 := rs (se 1 (by rfl) ⟨66551, by rfl⟩) R133103
theorem R351047 : Reach 351047 := rs (se 1 (by rfl) ⟨263285, by rfl⟩) R526571
theorem R1924013 : Reach 1924013 := rs (se 3 (by rfl) ⟨360752, by rfl⟩) R721505
theorem R286163 : Reach 286163 := rs (se 1 (by rfl) ⟨214622, by rfl⟩) R429245
theorem R318953 : Reach 318953 := rs (se 2 (by rfl) ⟨119607, by rfl⟩) R239215
theorem R286375 : Reach 286375 := rs (se 1 (by rfl) ⟨214781, by rfl⟩) R429563
theorem R779017 : Reach 779017 := rs (se 2 (by rfl) ⟨292131, by rfl⟩) R584263
theorem R1598939 : Reach 1598939 := rs (se 1 (by rfl) ⟨1199204, by rfl⟩) R2398409
theorem R353819 : Reach 353819 := rs (se 1 (by rfl) ⟨265364, by rfl⟩) R530729
theorem R223211 : Reach 223211 := rs (se 1 (by rfl) ⟨167408, by rfl⟩) R334817
theorem R190451 : Reach 190451 := rs (se 1 (by rfl) ⟨142838, by rfl⟩) R285677
theorem R92495 : Reach 92495 := rs (se 1 (by rfl) ⟨69371, by rfl⟩) R138743
theorem R223735 : Reach 223735 := rs (se 1 (by rfl) ⟨167801, by rfl⟩) R335603
theorem R551569 : Reach 551569 := rs (se 2 (by rfl) ⟨206838, by rfl⟩) R413677
theorem R355211 : Reach 355211 := rs (se 1 (by rfl) ⟨266408, by rfl⟩) R532817
theorem R650429 : Reach 650429 := rs (se 3 (by rfl) ⟨121955, by rfl⟩) R243911
theorem R257309 : Reach 257309 := rs (se 3 (by rfl) ⟨48245, by rfl⟩) R96491
theorem R192071 : Reach 192071 := rs (se 1 (by rfl) ⟨144053, by rfl⟩) R288107
theorem R192091 : Reach 192091 := rs (se 1 (by rfl) ⟨144068, by rfl⟩) R288137
theorem R258011 : Reach 258011 := rs (se 1 (by rfl) ⟨193508, by rfl⟩) R387017
theorem R258281 : Reach 258281 := rs (se 2 (by rfl) ⟨96855, by rfl⟩) R193711
theorem R127993 : Reach 127993 := rs (se 2 (by rfl) ⟨47997, by rfl⟩) R95995
theorem R193529 : Reach 193529 := rs (se 2 (by rfl) ⟨72573, by rfl⟩) R145147
theorem R128263 : Reach 128263 := rs (se 1 (by rfl) ⟨96197, by rfl⟩) R192395
theorem R1668545 : Reach 1668545 := rs (se 2 (by rfl) ⟨625704, by rfl⟩) R1251409
theorem R325079 : Reach 325079 := rs (se 1 (by rfl) ⟨243809, by rfl⟩) R487619
theorem R652819 : Reach 652819 := rs (se 1 (by rfl) ⟨489614, by rfl⟩) R979229
theorem R259901 : Reach 259901 := rs (se 3 (by rfl) ⟨48731, by rfl⟩) R97463
theorem R161975 : Reach 161975 := rs (se 1 (by rfl) ⟨121481, by rfl⟩) R242963
theorem R260279 : Reach 260279 := rs (se 1 (by rfl) ⟨195209, by rfl⟩) R390419
theorem R555407 : Reach 555407 := rs (se 1 (by rfl) ⟨416555, by rfl⟩) R833111
theorem R490025 : Reach 490025 := rs (se 2 (by rfl) ⟨183759, by rfl⟩) R367519
theorem R260873 : Reach 260873 := rs (se 2 (by rfl) ⟨97827, by rfl⟩) R195655
theorem R130153 : Reach 130153 := rs (se 2 (by rfl) ⟨48807, by rfl⟩) R97615
theorem R1342817 : Reach 1342817 := rs (se 2 (by rfl) ⟨503556, by rfl⟩) R1007113
theorem R163279 : Reach 163279 := rs (se 1 (by rfl) ⟨122459, by rfl⟩) R244919
theorem R130511 : Reach 130511 := rs (se 1 (by rfl) ⟨97883, by rfl⟩) R195767
theorem R196091 : Reach 196091 := rs (se 1 (by rfl) ⟨147068, by rfl⟩) R294137
theorem R261863 : Reach 261863 := rs (se 1 (by rfl) ⟨196397, by rfl⟩) R392795
theorem R327503 : Reach 327503 := rs (se 1 (by rfl) ⟨245627, by rfl⟩) R491255
theorem R491665 : Reach 491665 := rs (se 2 (by rfl) ⟨184374, by rfl⟩) R368749
theorem R131483 : Reach 131483 := rs (se 1 (by rfl) ⟨98612, by rfl⟩) R197225
theorem R197417 : Reach 197417 := rs (se 2 (by rfl) ⟨74031, by rfl⟩) R148063
theorem R1082155 : Reach 1082155 := rs (se 1 (by rfl) ⟨811616, by rfl⟩) R1623233
theorem R1410605 : Reach 1410605 := rs (se 3 (by rfl) ⟨264488, by rfl⟩) R528977
theorem R788077 : Reach 788077 := rs (se 3 (by rfl) ⟨147764, by rfl⟩) R295529
theorem R886463 : Reach 886463 := rs (se 1 (by rfl) ⟨664847, by rfl⟩) R1329695
theorem R394955 : Reach 394955 := rs (se 1 (by rfl) ⟨296216, by rfl⟩) R592433
theorem R11142947 : Reach 11142947 := rs (se 1 (by rfl) ⟨8357210, by rfl⟩) R16714421
theorem R1083941 : Reach 1083941 := rs (se 4 (by rfl) ⟨101619, by rfl⟩) R203239
theorem R854687 : Reach 854687 := rs (se 1 (by rfl) ⟨641015, by rfl⟩) R1282031
theorem R1051339 : Reach 1051339 := rs (se 1 (by rfl) ⟨788504, by rfl⟩) R1577009
theorem R232271 : Reach 232271 := rs (se 1 (by rfl) ⟨174203, by rfl⟩) R348407
theorem R396413 : Reach 396413 := rs (se 3 (by rfl) ⟨74327, by rfl⟩) R148655
theorem R1313977 : Reach 1313977 := rs (se 2 (by rfl) ⟨492741, by rfl⟩) R985483
theorem R298313 : Reach 298313 := rs (se 2 (by rfl) ⟨111867, by rfl⟩) R223735
theorem R232865 : Reach 232865 := rs (se 2 (by rfl) ⟨87324, by rfl⟩) R174649
theorem R266111 : Reach 266111 := rs (se 1 (by rfl) ⟨199583, by rfl⟩) R399167
theorem R397223 : Reach 397223 := rs (se 1 (by rfl) ⟨297917, by rfl⟩) R595835
theorem R266489 : Reach 266489 := rs (se 2 (by rfl) ⟨99933, by rfl⟩) R199867
theorem R234031 : Reach 234031 := rs (se 1 (by rfl) ⟨175523, by rfl⟩) R351047
theorem R496381 : Reach 496381 := rs (se 3 (by rfl) ⟨93071, by rfl⟩) R186143
theorem R235879 : Reach 235879 := rs (se 1 (by rfl) ⟨176909, by rfl⟩) R353819
theorem R170657 : Reach 170657 := rs (se 2 (by rfl) ⟨63996, by rfl⟩) R127993
theorem R924641 : Reach 924641 := rs (se 2 (by rfl) ⟨346740, by rfl⟩) R693481
theorem R171017 : Reach 171017 := rs (se 2 (by rfl) ⟨64131, by rfl⟩) R128263
theorem R236807 : Reach 236807 := rs (se 1 (by rfl) ⟨177605, by rfl⟩) R355211
theorem R433619 : Reach 433619 := rs (se 1 (by rfl) ⟨325214, by rfl⟩) R650429
theorem R171539 : Reach 171539 := rs (se 1 (by rfl) ⟨128654, by rfl⟩) R257309
theorem R204569 : Reach 204569 := rs (se 2 (by rfl) ⟨76713, by rfl⟩) R153427
theorem R172007 : Reach 172007 := rs (se 1 (by rfl) ⟨129005, by rfl⟩) R258011
theorem R270323 : Reach 270323 := rs (se 1 (by rfl) ⟨202742, by rfl⟩) R405485
theorem R172187 : Reach 172187 := rs (se 1 (by rfl) ⟨129140, by rfl⟩) R258281
theorem R336251 : Reach 336251 := rs (se 1 (by rfl) ⟨252188, by rfl⟩) R504377
theorem R270803 : Reach 270803 := rs (se 1 (by rfl) ⟨203102, by rfl⟩) R406205
theorem R205519 : Reach 205519 := rs (se 1 (by rfl) ⟨154139, by rfl⟩) R308279
theorem R173267 : Reach 173267 := rs (se 1 (by rfl) ⟨129950, by rfl⟩) R259901
theorem R337243 : Reach 337243 := rs (se 1 (by rfl) ⟨252932, by rfl⟩) R505865
theorem R75215 : Reach 75215 := rs (se 1 (by rfl) ⟨56411, by rfl⟩) R112823
theorem R107983 : Reach 107983 := rs (se 1 (by rfl) ⟨80987, by rfl⟩) R161975
theorem R173519 : Reach 173519 := rs (se 1 (by rfl) ⟨130139, by rfl⟩) R260279
theorem R173537 : Reach 173537 := rs (se 2 (by rfl) ⟨65076, by rfl⟩) R130153
theorem R75247 : Reach 75247 := rs (se 1 (by rfl) ⟨56435, by rfl⟩) R112871
theorem R370271 : Reach 370271 := rs (se 1 (by rfl) ⟨277703, by rfl⟩) R555407
theorem R75495 : Reach 75495 := rs (se 1 (by rfl) ⟨56621, by rfl⟩) R113243
theorem R272123 : Reach 272123 := rs (se 1 (by rfl) ⟨204092, by rfl⟩) R408185
theorem R75591 : Reach 75591 := rs (se 1 (by rfl) ⟨56693, by rfl⟩) R113387
theorem R75611 : Reach 75611 := rs (se 1 (by rfl) ⟨56708, by rfl⟩) R113417
theorem R173915 : Reach 173915 := rs (se 1 (by rfl) ⟨130436, by rfl⟩) R260873
theorem R1452167 : Reach 1452167 := rs (se 1 (by rfl) ⟨1089125, by rfl⟩) R2178251
theorem R895211 : Reach 895211 := rs (se 1 (by rfl) ⟨671408, by rfl⟩) R1342817
theorem R76191 : Reach 76191 := rs (se 1 (by rfl) ⟨57143, by rfl⟩) R114287
theorem R76271 : Reach 76271 := rs (se 1 (by rfl) ⟨57203, by rfl⟩) R114407
theorem R174575 : Reach 174575 := rs (se 1 (by rfl) ⟨130931, by rfl⟩) R261863
theorem R76399 : Reach 76399 := rs (se 1 (by rfl) ⟨57299, by rfl⟩) R114599
theorem R174887 : Reach 174887 := rs (se 1 (by rfl) ⟨131165, by rfl⟩) R262331
theorem R76615 : Reach 76615 := rs (se 1 (by rfl) ⟨57461, by rfl⟩) R114923
theorem R76655 : Reach 76655 := rs (se 1 (by rfl) ⟨57491, by rfl⟩) R114983
theorem R1125575 : Reach 1125575 := rs (se 1 (by rfl) ⟨844181, by rfl⟩) R1688363
theorem R77103 : Reach 77103 := rs (se 1 (by rfl) ⟨57827, by rfl⟩) R115655
theorem R77215 : Reach 77215 := rs (se 1 (by rfl) ⟨57911, by rfl⟩) R115823
theorem R142823 : Reach 142823 := rs (se 1 (by rfl) ⟨107117, by rfl⟩) R214235
theorem R77343 : Reach 77343 := rs (se 1 (by rfl) ⟨58007, by rfl⟩) R116015
theorem R634463 : Reach 634463 := rs (se 1 (by rfl) ⟨475847, by rfl⟩) R951695
theorem R77479 : Reach 77479 := rs (se 1 (by rfl) ⟨58109, by rfl⟩) R116219
theorem R175807 : Reach 175807 := rs (se 1 (by rfl) ⟨131855, by rfl⟩) R263711
theorem R77503 : Reach 77503 := rs (se 1 (by rfl) ⟨58127, by rfl⟩) R116255
theorem R77599 : Reach 77599 := rs (se 1 (by rfl) ⟨58199, by rfl⟩) R116399
theorem R77679 : Reach 77679 := rs (se 1 (by rfl) ⟨58259, by rfl⟩) R116519
theorem R110575 : Reach 110575 := rs (se 1 (by rfl) ⟨82931, by rfl⟩) R165863
theorem R78047 : Reach 78047 := rs (se 1 (by rfl) ⟨58535, by rfl⟩) R117071
theorem R78079 : Reach 78079 := rs (se 1 (by rfl) ⟨58559, by rfl⟩) R117119
theorem R78107 : Reach 78107 := rs (se 1 (by rfl) ⟨58580, by rfl⟩) R117161
theorem R78363 : Reach 78363 := rs (se 1 (by rfl) ⟨58772, by rfl⟩) R117545
theorem R78503 : Reach 78503 := rs (se 1 (by rfl) ⟨58877, by rfl⟩) R117755
theorem R78543 : Reach 78543 := rs (se 1 (by rfl) ⟨58907, by rfl⟩) R117815
theorem R78623 : Reach 78623 := rs (se 1 (by rfl) ⟨58967, by rfl⟩) R117935
theorem R209747 : Reach 209747 := rs (se 1 (by rfl) ⟨157310, by rfl⟩) R314621
theorem R177065 : Reach 177065 := rs (se 2 (by rfl) ⟨66399, by rfl⟩) R132799
theorem R210127 : Reach 210127 := rs (se 1 (by rfl) ⟨157595, by rfl⟩) R315191
theorem R79103 : Reach 79103 := rs (se 1 (by rfl) ⟨59327, by rfl⟩) R118655
theorem R1488527 : Reach 1488527 := rs (se 1 (by rfl) ⟨1116395, by rfl⟩) R2232791
theorem R243425 : Reach 243425 := rs (se 2 (by rfl) ⟨91284, by rfl⟩) R182569
theorem R145307 : Reach 145307 := rs (se 1 (by rfl) ⟨108980, by rfl⟩) R217961
theorem R112703 : Reach 112703 := rs (se 1 (by rfl) ⟨84527, by rfl⟩) R169055
theorem R571535 : Reach 571535 := rs (se 1 (by rfl) ⟨428651, by rfl⟩) R857303
theorem R735425 : Reach 735425 := rs (se 2 (by rfl) ⟨275784, by rfl⟩) R551569
theorem R113033 : Reach 113033 := rs (se 2 (by rfl) ⟨42387, by rfl⟩) R84775
theorem R768457 : Reach 768457 := rs (se 2 (by rfl) ⟨288171, by rfl⟩) R576343
theorem R113207 : Reach 113207 := rs (se 1 (by rfl) ⟨84905, by rfl⟩) R169811
theorem R113531 : Reach 113531 := rs (se 1 (by rfl) ⟨85148, by rfl⟩) R170297
theorem R211835 : Reach 211835 := rs (se 1 (by rfl) ⟨158876, by rfl⟩) R317753
theorem R114143 : Reach 114143 := rs (se 1 (by rfl) ⟨85607, by rfl⟩) R171215
theorem R212635 : Reach 212635 := rs (se 1 (by rfl) ⟨159476, by rfl⟩) R318953
theorem R245423 : Reach 245423 := rs (se 1 (by rfl) ⟨184067, by rfl⟩) R368135
theorem R114395 : Reach 114395 := rs (se 1 (by rfl) ⟨85796, by rfl⟩) R171593
theorem R114665 : Reach 114665 := rs (se 2 (by rfl) ⟨42999, by rfl⟩) R85999
theorem R114857 : Reach 114857 := rs (se 2 (by rfl) ⟨43071, by rfl⟩) R86143
theorem R115175 : Reach 115175 := rs (se 1 (by rfl) ⟨86381, by rfl⟩) R172763
theorem R442867 : Reach 442867 := rs (se 1 (by rfl) ⟨332150, by rfl⟩) R664301
theorem R115451 : Reach 115451 := rs (se 1 (by rfl) ⟨86588, by rfl⟩) R173177
theorem R246653 : Reach 246653 := rs (se 3 (by rfl) ⟨46247, by rfl⟩) R92495
theorem R1065959 : Reach 1065959 := rs (se 1 (by rfl) ⟨799469, by rfl⟩) R1598939
theorem R574451 : Reach 574451 := rs (se 1 (by rfl) ⟨430838, by rfl⟩) R861677
theorem R115895 : Reach 115895 := rs (se 1 (by rfl) ⟨86921, by rfl⟩) R173843
theorem R673049 : Reach 673049 := rs (se 2 (by rfl) ⟨252393, by rfl⟩) R504787
theorem R116039 : Reach 116039 := rs (se 1 (by rfl) ⟨87029, by rfl⟩) R174059
theorem R148807 : Reach 148807 := rs (se 1 (by rfl) ⟨111605, by rfl⟩) R223211
theorem R116135 : Reach 116135 := rs (se 1 (by rfl) ⟨87101, by rfl⟩) R174203
theorem R1099331 : Reach 1099331 := rs (se 1 (by rfl) ⟨824498, by rfl⟩) R1648997
theorem R116315 : Reach 116315 := rs (se 1 (by rfl) ⟨87236, by rfl⟩) R174473
theorem R870425 : Reach 870425 := rs (se 2 (by rfl) ⟨326409, by rfl⟩) R652819
theorem R116783 : Reach 116783 := rs (se 1 (by rfl) ⟨87587, by rfl⟩) R175175
theorem R117047 : Reach 117047 := rs (se 1 (by rfl) ⟨87785, by rfl⟩) R175571
theorem R870821 : Reach 870821 := rs (se 4 (by rfl) ⟨81639, by rfl⟩) R163279
theorem R5130701 : Reach 5130701 := rs (se 3 (by rfl) ⟨962006, by rfl⟩) R1924013
theorem R379343 : Reach 379343 := rs (se 1 (by rfl) ⟨284507, by rfl⟩) R569015
theorem R117227 : Reach 117227 := rs (se 1 (by rfl) ⟨87920, by rfl⟩) R175841
theorem R379513 : Reach 379513 := rs (se 2 (by rfl) ⟨142317, by rfl⟩) R284635
theorem R117467 : Reach 117467 := rs (se 1 (by rfl) ⟨88100, by rfl⟩) R176201
theorem R117503 : Reach 117503 := rs (se 1 (by rfl) ⟨88127, by rfl⟩) R176255
theorem R445783 : Reach 445783 := rs (se 1 (by rfl) ⟨334337, by rfl⟩) R668675
theorem R118223 : Reach 118223 := rs (se 1 (by rfl) ⟨88667, by rfl⟩) R177335
theorem R118313 : Reach 118313 := rs (se 2 (by rfl) ⟨44367, by rfl⟩) R88735
theorem R216719 : Reach 216719 := rs (se 1 (by rfl) ⟨162539, by rfl⟩) R325079
theorem R118607 : Reach 118607 := rs (se 1 (by rfl) ⟨88955, by rfl⟩) R177911
theorem R2445461 : Reach 2445461 := rs (se 6 (by rfl) ⟨57315, by rfl⟩) R114631
theorem R5099719 : Reach 5099719 := rs (se 1 (by rfl) ⟨3824789, by rfl⟩) R7649579
theorem R873341 : Reach 873341 := rs (se 3 (by rfl) ⟨163751, by rfl⟩) R327503
theorem R381833 : Reach 381833 := rs (se 2 (by rfl) ⟨143187, by rfl⟩) R286375
theorem R87007 : Reach 87007 := rs (se 1 (by rfl) ⟨65255, by rfl⟩) R130511
theorem R382319 : Reach 382319 := rs (se 1 (by rfl) ⟨286739, by rfl⟩) R573479
theorem R87583 : Reach 87583 := rs (se 1 (by rfl) ⟨65687, by rfl⟩) R131375
theorem R218963 : Reach 218963 := rs (se 1 (by rfl) ⟨164222, by rfl⟩) R328445
theorem R481261 : Reach 481261 := rs (se 3 (by rfl) ⟨90236, by rfl⟩) R180473
theorem R841711 : Reach 841711 := rs (se 1 (by rfl) ⟨631283, by rfl⟩) R1262567
theorem R219145 : Reach 219145 := rs (se 2 (by rfl) ⟨82179, by rfl⟩) R164359
theorem R481619 : Reach 481619 := rs (se 1 (by rfl) ⟨361214, by rfl⟩) R722429
theorem R1038689 : Reach 1038689 := rs (se 2 (by rfl) ⟨389508, by rfl⟩) R779017
theorem R88447 : Reach 88447 := rs (se 1 (by rfl) ⟨66335, by rfl⟩) R132671
theorem R1596125 : Reach 1596125 := rs (se 3 (by rfl) ⟨299273, by rfl⟩) R598547
theorem R318269 : Reach 318269 := rs (se 3 (by rfl) ⟨59675, by rfl⟩) R119351
theorem R646055 : Reach 646055 := rs (se 1 (by rfl) ⟨484541, by rfl⟩) R969083
theorem R187721 : Reach 187721 := rs (se 2 (by rfl) ⟨70395, by rfl⟩) R140791
theorem R679337 : Reach 679337 := rs (se 2 (by rfl) ⟨254751, by rfl⟩) R509503
theorem R449975 : Reach 449975 := rs (se 1 (by rfl) ⟨337481, by rfl⟩) R674963
theorem R450157 : Reach 450157 := rs (se 3 (by rfl) ⟨84404, by rfl⟩) R168809
theorem R876257 : Reach 876257 := rs (se 2 (by rfl) ⟨328596, by rfl⟩) R657193
theorem R287165 : Reach 287165 := rs (se 3 (by rfl) ⟨53843, by rfl⟩) R107687
theorem R156215 : Reach 156215 := rs (se 1 (by rfl) ⟨117161, by rfl⟩) R234323
theorem R5563181 : Reach 5563181 := rs (se 3 (by rfl) ⟨1043096, by rfl⟩) R2086193
theorem R1303451 : Reach 1303451 := rs (se 1 (by rfl) ⟨977588, by rfl⟩) R1955177
theorem R2548745 : Reach 2548745 := rs (se 2 (by rfl) ⟨955779, by rfl⟩) R1911559
theorem R288319 : Reach 288319 := rs (se 1 (by rfl) ⟨216239, by rfl⟩) R432479
theorem R223337 : Reach 223337 := rs (se 2 (by rfl) ⟨83751, by rfl⟩) R167503
theorem R256121 : Reach 256121 := rs (se 2 (by rfl) ⟨96045, by rfl⟩) R192091
theorem R1599745 : Reach 1599745 := rs (se 2 (by rfl) ⟨599904, by rfl⟩) R1199809
theorem R223519 : Reach 223519 := rs (se 1 (by rfl) ⟨167639, by rfl⟩) R335279
theorem R190775 : Reach 190775 := rs (se 1 (by rfl) ⟨143081, by rfl⟩) R286163
theorem R289277 : Reach 289277 := rs (se 3 (by rfl) ⟨54239, by rfl⟩) R108479
theorem R224669 : Reach 224669 := rs (se 3 (by rfl) ⟨42125, by rfl⟩) R84251
theorem R192233 : Reach 192233 := rs (se 2 (by rfl) ⟨72087, by rfl⟩) R144175
theorem R126967 : Reach 126967 := rs (se 1 (by rfl) ⟨95225, by rfl⟩) R190451
theorem R291023 : Reach 291023 := rs (se 1 (by rfl) ⟨218267, by rfl⟩) R436535
theorem R3469873 : Reach 3469873 := rs (se 2 (by rfl) ⟨1301202, by rfl⟩) R2602405
theorem R553661 : Reach 553661 := rs (se 3 (by rfl) ⟨103811, by rfl⟩) R207623
theorem R94939 : Reach 94939 := rs (se 1 (by rfl) ⟨71204, by rfl⟩) R142409
theorem R586601 : Reach 586601 := rs (se 2 (by rfl) ⟨219975, by rfl⟩) R439951
theorem R291721 : Reach 291721 := rs (se 2 (by rfl) ⟨109395, by rfl⟩) R218791
theorem R128047 : Reach 128047 := rs (se 1 (by rfl) ⟨96035, by rfl⟩) R192071
theorem R291995 : Reach 291995 := rs (se 1 (by rfl) ⟨218996, by rfl⟩) R437993
theorem R423407 : Reach 423407 := rs (se 1 (by rfl) ⟨317555, by rfl⟩) R635111
theorem R96223 : Reach 96223 := rs (se 1 (by rfl) ⟨72167, by rfl⟩) R144335
theorem R129019 : Reach 129019 := rs (se 1 (by rfl) ⟨96764, by rfl⟩) R193529
theorem R161831 : Reach 161831 := rs (se 1 (by rfl) ⟨121373, by rfl⟩) R242747
theorem R1112363 : Reach 1112363 := rs (se 1 (by rfl) ⟨834272, by rfl⟩) R1668545
theorem R424531 : Reach 424531 := rs (se 1 (by rfl) ⟨318398, by rfl⟩) R636797
theorem R326683 : Reach 326683 := rs (se 1 (by rfl) ⟨245012, by rfl⟩) R490025
theorem R326753 : Reach 326753 := rs (se 2 (by rfl) ⟨122532, by rfl⟩) R245065
theorem R130727 : Reach 130727 := rs (se 1 (by rfl) ⟨98045, by rfl⟩) R196091
theorem R98111 : Reach 98111 := rs (se 1 (by rfl) ⟨73583, by rfl⟩) R147167
theorem R655553 : Reach 655553 := rs (se 2 (by rfl) ⟨245832, by rfl⟩) R491665
theorem R131611 : Reach 131611 := rs (se 1 (by rfl) ⟨98708, by rfl⟩) R197417
theorem R164435 : Reach 164435 := rs (se 1 (by rfl) ⟨123326, by rfl⟩) R246653
theorem R590489 : Reach 590489 := rs (se 2 (by rfl) ⟨221433, by rfl⟩) R442867
theorem R1442873 : Reach 1442873 := rs (se 2 (by rfl) ⟨541077, by rfl⟩) R1082155
theorem R590975 : Reach 590975 := rs (se 1 (by rfl) ⟨443231, by rfl⟩) R886463
theorem R263303 : Reach 263303 := rs (se 1 (by rfl) ⟨197477, by rfl⟩) R394955
theorem R722627 : Reach 722627 := rs (se 1 (by rfl) ⟨541970, by rfl⟩) R1083941
theorem R198409 : Reach 198409 := rs (se 2 (by rfl) ⟨74403, by rfl⟩) R148807
theorem R264275 : Reach 264275 := rs (se 1 (by rfl) ⟨198206, by rfl⟩) R396413
theorem R1050769 : Reach 1050769 := rs (se 2 (by rfl) ⟨394038, by rfl⟩) R788077
theorem R198875 : Reach 198875 := rs (se 1 (by rfl) ⟨149156, by rfl⟩) R298313
theorem R559325 : Reach 559325 := rs (se 3 (by rfl) ⟨104873, by rfl⟩) R209747
theorem R264815 : Reach 264815 := rs (se 1 (by rfl) ⟨198611, by rfl⟩) R397223
theorem R2132993 : Reach 2132993 := rs (se 2 (by rfl) ⟨799872, by rfl⟩) R1599745
theorem R298025 : Reach 298025 := rs (se 2 (by rfl) ⟨111759, by rfl⟩) R223519
theorem R692459 : Reach 692459 := rs (se 1 (by rfl) ⟨519344, by rfl⟩) R1038689
theorem R594377 : Reach 594377 := rs (se 2 (by rfl) ⟨222891, by rfl⟩) R445783
theorem R430703 : Reach 430703 := rs (se 1 (by rfl) ⟨323027, by rfl⟩) R646055
theorem R234409 : Reach 234409 := rs (se 2 (by rfl) ⟨87903, by rfl⟩) R175807
theorem R299983 : Reach 299983 := rs (se 1 (by rfl) ⟨224987, by rfl⟩) R449975
theorem R136379 : Reach 136379 := rs (se 1 (by rfl) ⟨102284, by rfl⟩) R204569
theorem R169289 : Reach 169289 := rs (se 2 (by rfl) ⟨63483, by rfl⟩) R126967
theorem R3708787 : Reach 3708787 := rs (se 1 (by rfl) ⟨2781590, by rfl⟩) R5563181
theorem R4626497 : Reach 4626497 := rs (se 2 (by rfl) ⟨1734936, by rfl⟩) R3469873
theorem R661841 : Reach 661841 := rs (se 2 (by rfl) ⟨248190, by rfl⟩) R496381
theorem R465533 : Reach 465533 := rs (se 3 (by rfl) ⟨87287, by rfl⟩) R174575
theorem R170729 : Reach 170729 := rs (se 2 (by rfl) ⟨64023, by rfl⟩) R128047
theorem R170747 : Reach 170747 := rs (se 1 (by rfl) ⟨128060, by rfl⟩) R256121
theorem R596807 : Reach 596807 := rs (se 1 (by rfl) ⟨447605, by rfl⟩) R895211
theorem R1122281 : Reach 1122281 := rs (se 2 (by rfl) ⟨420855, by rfl⟩) R841711
theorem R172025 : Reach 172025 := rs (se 2 (by rfl) ⟨64509, by rfl⟩) R129019
theorem R369107 : Reach 369107 := rs (se 1 (by rfl) ⟨276830, by rfl⟩) R553661
theorem R1024609 : Reach 1024609 := rs (se 2 (by rfl) ⟨384228, by rfl⟩) R768457
theorem R566041 : Reach 566041 := rs (se 2 (by rfl) ⟨212265, by rfl⟩) R424531
theorem R992351 : Reach 992351 := rs (se 1 (by rfl) ⟨744263, by rfl⟩) R1488527
theorem R107887 : Reach 107887 := rs (se 1 (by rfl) ⟨80915, by rfl⟩) R161831
theorem R435577 : Reach 435577 := rs (se 2 (by rfl) ⟨163341, by rfl⟩) R326683
theorem R75135 : Reach 75135 := rs (se 1 (by rfl) ⟨56351, by rfl⟩) R112703
theorem R75355 : Reach 75355 := rs (se 1 (by rfl) ⟨56516, by rfl⟩) R113033
theorem R75471 : Reach 75471 := rs (se 1 (by rfl) ⟨56603, by rfl⟩) R113207
theorem R75687 : Reach 75687 := rs (se 1 (by rfl) ⟨56765, by rfl⟩) R113531
theorem R141223 : Reach 141223 := rs (se 1 (by rfl) ⟨105917, by rfl⟩) R211835
theorem R600209 : Reach 600209 := rs (se 2 (by rfl) ⟨225078, by rfl⟩) R450157
theorem R76095 : Reach 76095 := rs (se 1 (by rfl) ⟨57071, by rfl⟩) R114143
theorem R76263 : Reach 76263 := rs (se 1 (by rfl) ⟨57197, by rfl⟩) R114395
theorem R76443 : Reach 76443 := rs (se 1 (by rfl) ⟨57332, by rfl⟩) R114665
theorem R76571 : Reach 76571 := rs (se 1 (by rfl) ⟨57428, by rfl⟩) R114857
theorem R76783 : Reach 76783 := rs (se 1 (by rfl) ⟨57587, by rfl⟩) R115175
theorem R76967 : Reach 76967 := rs (se 1 (by rfl) ⟨57725, by rfl⟩) R115451
theorem R77263 : Reach 77263 := rs (se 1 (by rfl) ⟨57947, by rfl⟩) R115895
theorem R77359 : Reach 77359 := rs (se 1 (by rfl) ⟨58019, by rfl⟩) R116039
theorem R274025 : Reach 274025 := rs (se 2 (by rfl) ⟨102759, by rfl⟩) R205519
theorem R77423 : Reach 77423 := rs (se 1 (by rfl) ⟨58067, by rfl⟩) R116135
theorem R896669 : Reach 896669 := rs (se 3 (by rfl) ⟨168125, by rfl⟩) R336251
theorem R732887 : Reach 732887 := rs (se 1 (by rfl) ⟨549665, by rfl⟩) R1099331
theorem R77543 : Reach 77543 := rs (se 1 (by rfl) ⟨58157, by rfl⟩) R116315
theorem R77855 : Reach 77855 := rs (se 1 (by rfl) ⟨58391, by rfl⟩) R116783
theorem R78031 : Reach 78031 := rs (se 1 (by rfl) ⟨58523, by rfl⟩) R117047
theorem R3420467 : Reach 3420467 := rs (se 1 (by rfl) ⟨2565350, by rfl⟩) R5130701
theorem R78151 : Reach 78151 := rs (se 1 (by rfl) ⟨58613, by rfl⟩) R117227
theorem R569791 : Reach 569791 := rs (se 1 (by rfl) ⟨427343, by rfl⟩) R854687
theorem R78311 : Reach 78311 := rs (se 1 (by rfl) ⟨58733, by rfl⟩) R117467
theorem R78335 : Reach 78335 := rs (se 1 (by rfl) ⟨58751, by rfl⟩) R117503
theorem R1258021 : Reach 1258021 := rs (se 4 (by rfl) ⟨117939, by rfl⟩) R235879
theorem R78815 : Reach 78815 := rs (se 1 (by rfl) ⟨59111, by rfl⟩) R118223
theorem R78875 : Reach 78875 := rs (se 1 (by rfl) ⟨59156, by rfl⟩) R118313
theorem R144479 : Reach 144479 := rs (se 1 (by rfl) ⟨108359, by rfl⟩) R216719
theorem R79071 : Reach 79071 := rs (se 1 (by rfl) ⟨59303, by rfl⟩) R118607
theorem R177407 : Reach 177407 := rs (se 1 (by rfl) ⟨133055, by rfl⟩) R266111
theorem R177659 : Reach 177659 := rs (se 1 (by rfl) ⟨133244, by rfl⟩) R266489
theorem R506017 : Reach 506017 := rs (se 2 (by rfl) ⟨189756, by rfl⟩) R379513
theorem R506341 : Reach 506341 := rs (se 4 (by rfl) ⟨47469, by rfl⟩) R94939
theorem R145975 : Reach 145975 := rs (se 1 (by rfl) ⟨109481, by rfl⟩) R218963
theorem R1129085 : Reach 1129085 := rs (se 3 (by rfl) ⟨211703, by rfl⟩) R423407
theorem R1751969 : Reach 1751969 := rs (se 2 (by rfl) ⟨656988, by rfl⟩) R1313977
theorem R113771 : Reach 113771 := rs (se 1 (by rfl) ⟨85328, by rfl⟩) R170657
theorem R1064083 : Reach 1064083 := rs (se 1 (by rfl) ⟨798062, by rfl⟩) R1596125
theorem R114011 : Reach 114011 := rs (se 1 (by rfl) ⟨85508, by rfl⟩) R171017
theorem R114359 : Reach 114359 := rs (se 1 (by rfl) ⟨85769, by rfl⟩) R171539
theorem R147433 : Reach 147433 := rs (se 2 (by rfl) ⟨55287, by rfl⟩) R110575
theorem R114671 : Reach 114671 := rs (se 1 (by rfl) ⟨86003, by rfl⟩) R172007
theorem R180215 : Reach 180215 := rs (se 1 (by rfl) ⟨135161, by rfl⟩) R270323
theorem R114791 : Reach 114791 := rs (se 1 (by rfl) ⟨86093, by rfl⟩) R172187
theorem R6799625 : Reach 6799625 := rs (se 2 (by rfl) ⟨2549859, by rfl⟩) R5099719
theorem R180535 : Reach 180535 := rs (se 1 (by rfl) ⟨135401, by rfl⟩) R270803
theorem R868967 : Reach 868967 := rs (se 1 (by rfl) ⟨651725, by rfl⟩) R1303451
theorem R312041 : Reach 312041 := rs (se 2 (by rfl) ⟨117015, by rfl⟩) R234031
theorem R115511 : Reach 115511 := rs (se 1 (by rfl) ⟨86633, by rfl⟩) R173267
theorem R115679 : Reach 115679 := rs (se 1 (by rfl) ⟨86759, by rfl⟩) R173519
theorem R115691 : Reach 115691 := rs (se 1 (by rfl) ⟨86768, by rfl⟩) R173537
theorem R246847 : Reach 246847 := rs (se 1 (by rfl) ⟨185135, by rfl⟩) R370271
theorem R181415 : Reach 181415 := rs (se 1 (by rfl) ⟨136061, by rfl⟩) R272123
theorem R115943 : Reach 115943 := rs (se 1 (by rfl) ⟨86957, by rfl⟩) R173915
theorem R116009 : Reach 116009 := rs (se 2 (by rfl) ⟨43503, by rfl⟩) R87007
theorem R148891 : Reach 148891 := rs (se 1 (by rfl) ⟨111668, by rfl⟩) R223337
theorem R968111 : Reach 968111 := rs (se 1 (by rfl) ⟨726083, by rfl⟩) R1452167
theorem R280169 : Reach 280169 := rs (se 2 (by rfl) ⟨105063, by rfl⟩) R210127
theorem R116591 : Reach 116591 := rs (se 1 (by rfl) ⟨87443, by rfl⟩) R174887
theorem R116777 : Reach 116777 := rs (se 2 (by rfl) ⟨43791, by rfl⟩) R87583
theorem R149779 : Reach 149779 := rs (se 1 (by rfl) ⟨112334, by rfl⟩) R224669
theorem R575909 : Reach 575909 := rs (se 4 (by rfl) ⟨53991, by rfl⟩) R107983
theorem R641681 : Reach 641681 := rs (se 2 (by rfl) ⟨240630, by rfl⟩) R481261
theorem R117929 : Reach 117929 := rs (se 2 (by rfl) ⟨44223, by rfl⟩) R88447
theorem R118043 : Reach 118043 := rs (se 1 (by rfl) ⟨88532, by rfl⟩) R177065
theorem R380861 : Reach 380861 := rs (se 3 (by rfl) ⟨71411, by rfl⟩) R142823
theorem R381023 : Reach 381023 := rs (se 1 (by rfl) ⟨285767, by rfl⟩) R571535
theorem R741575 : Reach 741575 := rs (se 1 (by rfl) ⟨556181, by rfl⟩) R1112363
theorem R217835 : Reach 217835 := rs (se 1 (by rfl) ⟨163376, by rfl⟩) R326753
theorem R283513 : Reach 283513 := rs (se 2 (by rfl) ⟨106317, by rfl⟩) R212635
theorem R87151 : Reach 87151 := rs (se 1 (by rfl) ⟨65363, by rfl⟩) R130727
theorem R87655 : Reach 87655 := rs (se 1 (by rfl) ⟨65741, by rfl⟩) R131483
theorem R710639 : Reach 710639 := rs (se 1 (by rfl) ⟨532979, by rfl⟩) R1065959
theorem R382967 : Reach 382967 := rs (se 1 (by rfl) ⟨287225, by rfl⟩) R574451
theorem R448699 : Reach 448699 := rs (se 1 (by rfl) ⟨336524, by rfl⟩) R673049
theorem R940403 : Reach 940403 := rs (se 1 (by rfl) ⟨705302, by rfl⟩) R1410605
theorem R7428631 : Reach 7428631 := rs (se 1 (by rfl) ⟨5571473, by rfl⟩) R11142947
theorem R580283 : Reach 580283 := rs (se 1 (by rfl) ⟨435212, by rfl⟩) R870425
theorem R416573 : Reach 416573 := rs (se 3 (by rfl) ⟨78107, by rfl⟩) R156215
theorem R580547 : Reach 580547 := rs (se 1 (by rfl) ⟨435410, by rfl⟩) R870821
theorem R252895 : Reach 252895 := rs (se 1 (by rfl) ⟨189671, by rfl⟩) R379343
theorem R449657 : Reach 449657 := rs (se 2 (by rfl) ⟨168621, by rfl⟩) R337243
theorem R154847 : Reach 154847 := rs (se 1 (by rfl) ⟨116135, by rfl⟩) R232271
theorem R384425 : Reach 384425 := rs (se 2 (by rfl) ⟨144159, by rfl⟩) R288319
theorem R155243 : Reach 155243 := rs (se 1 (by rfl) ⟨116432, by rfl⟩) R232865
theorem R1630307 : Reach 1630307 := rs (se 1 (by rfl) ⟨1222730, by rfl⟩) R2445461
theorem R582227 : Reach 582227 := rs (se 1 (by rfl) ⟨436670, by rfl⟩) R873341
theorem R254555 : Reach 254555 := rs (se 1 (by rfl) ⟨190916, by rfl⟩) R381833
theorem R254879 : Reach 254879 := rs (se 1 (by rfl) ⟨191159, by rfl⟩) R382319
theorem R1401785 : Reach 1401785 := rs (se 2 (by rfl) ⟨525669, by rfl⟩) R1051339
theorem R321079 : Reach 321079 := rs (se 1 (by rfl) ⟨240809, by rfl⟩) R481619
theorem R616427 : Reach 616427 := rs (se 1 (by rfl) ⟨462320, by rfl⟩) R924641
theorem R157871 : Reach 157871 := rs (se 1 (by rfl) ⟨118403, by rfl⟩) R236807
theorem R125147 : Reach 125147 := rs (se 1 (by rfl) ⟨93860, by rfl⟩) R187721
theorem R452891 : Reach 452891 := rs (se 1 (by rfl) ⟨339668, by rfl⟩) R679337
theorem R289079 : Reach 289079 := rs (se 1 (by rfl) ⟨216809, by rfl⟩) R433619
theorem R584171 : Reach 584171 := rs (se 1 (by rfl) ⟨438128, by rfl⟩) R876257
theorem R191443 : Reach 191443 := rs (se 1 (by rfl) ⟨143582, by rfl⟩) R287165
theorem R1699163 : Reach 1699163 := rs (se 1 (by rfl) ⟨1274372, by rfl⟩) R2548745
theorem R388961 : Reach 388961 := rs (se 2 (by rfl) ⟨145860, by rfl⟩) R291721
theorem R127183 : Reach 127183 := rs (se 1 (by rfl) ⟨95387, by rfl⟩) R190775
theorem R192851 : Reach 192851 := rs (se 1 (by rfl) ⟨144638, by rfl⟩) R289277
theorem R750383 : Reach 750383 := rs (se 1 (by rfl) ⟨562787, by rfl⟩) R1125575
theorem R848717 : Reach 848717 := rs (se 3 (by rfl) ⟨159134, by rfl⟩) R318269
theorem R422975 : Reach 422975 := rs (se 1 (by rfl) ⟨317231, by rfl⟩) R634463
theorem R128155 : Reach 128155 := rs (se 1 (by rfl) ⟨96116, by rfl⟩) R192233
theorem R128297 : Reach 128297 := rs (se 2 (by rfl) ⟨48111, by rfl⟩) R96223
theorem R292193 : Reach 292193 := rs (se 2 (by rfl) ⟨109572, by rfl⟩) R219145
theorem R194015 : Reach 194015 := rs (se 1 (by rfl) ⟨145511, by rfl⟩) R291023
theorem R391067 : Reach 391067 := rs (se 1 (by rfl) ⟨293300, by rfl⟩) R586601
theorem R194663 : Reach 194663 := rs (se 1 (by rfl) ⟨145997, by rfl⟩) R291995
theorem R162283 : Reach 162283 := rs (se 1 (by rfl) ⟨121712, by rfl⟩) R243425
theorem R96871 : Reach 96871 := rs (se 1 (by rfl) ⟨72653, by rfl⟩) R145307
theorem R490283 : Reach 490283 := rs (se 1 (by rfl) ⟨367712, by rfl⟩) R735425
theorem R261629 : Reach 261629 := rs (se 3 (by rfl) ⟨49055, by rfl⟩) R98111
theorem R163615 : Reach 163615 := rs (se 1 (by rfl) ⟨122711, by rfl⟩) R245423
theorem R393659 : Reach 393659 := rs (se 1 (by rfl) ⟨295244, by rfl⟩) R590489
theorem R393983 : Reach 393983 := rs (se 1 (by rfl) ⟨295487, by rfl⟩) R590975
theorem R754721 : Reach 754721 := rs (se 2 (by rfl) ⟨283020, by rfl⟩) R566041
theorem R329129 : Reach 329129 := rs (se 2 (by rfl) ⟨123423, by rfl⟩) R246847
theorem R132583 : Reach 132583 := rs (se 1 (by rfl) ⟨99437, by rfl⟩) R198875
theorem R427787 : Reach 427787 := rs (se 1 (by rfl) ⟨320840, by rfl⟩) R641681
theorem R198521 : Reach 198521 := rs (se 2 (by rfl) ⟨74445, by rfl⟩) R148891
theorem R198683 : Reach 198683 := rs (se 1 (by rfl) ⟨149012, by rfl⟩) R298025
theorem R428105 : Reach 428105 := rs (se 2 (by rfl) ⟨160539, by rfl⟩) R321079
theorem R264545 : Reach 264545 := rs (se 2 (by rfl) ⟨99204, by rfl⟩) R198409
theorem R494383 : Reach 494383 := rs (se 1 (by rfl) ⟨370787, by rfl⟩) R741575
theorem R461639 : Reach 461639 := rs (se 1 (by rfl) ⟨346229, by rfl⟩) R692459
theorem R396251 : Reach 396251 := rs (se 1 (by rfl) ⟨297188, by rfl⟩) R594377
theorem R199705 : Reach 199705 := rs (se 2 (by rfl) ⟨74889, by rfl⟩) R149779
theorem R3084331 : Reach 3084331 := rs (se 1 (by rfl) ⟨2313248, by rfl⟩) R4626497
theorem R626935 : Reach 626935 := rs (se 1 (by rfl) ⟨470201, by rfl⟩) R940403
theorem R397871 : Reach 397871 := rs (se 1 (by rfl) ⟨298403, by rfl⟩) R596807
theorem R299771 : Reach 299771 := rs (se 1 (by rfl) ⟨224828, by rfl⟩) R449657
theorem R103231 : Reach 103231 := rs (se 1 (by rfl) ⟨77423, by rfl⟩) R154847
theorem R1086871 : Reach 1086871 := rs (se 1 (by rfl) ⟨815153, by rfl⟩) R1630307
theorem R169577 : Reach 169577 := rs (se 2 (by rfl) ⟨63591, by rfl⟩) R127183
theorem R169703 : Reach 169703 := rs (se 1 (by rfl) ⟨127277, by rfl⟩) R254555
theorem R759721 : Reach 759721 := rs (se 2 (by rfl) ⟨284895, by rfl⟩) R569791
theorem R169919 : Reach 169919 := rs (se 1 (by rfl) ⟨127439, by rfl⟩) R254879
theorem R1677361 : Reach 1677361 := rs (se 2 (by rfl) ⟨629010, by rfl⟩) R1258021
theorem R661567 : Reach 661567 := rs (se 1 (by rfl) ⟨496175, by rfl⟩) R992351
theorem R399977 : Reach 399977 := rs (se 2 (by rfl) ⟨149991, by rfl⟩) R299983
theorem R400139 : Reach 400139 := rs (se 1 (by rfl) ⟨300104, by rfl⟩) R600209
theorem R105247 : Reach 105247 := rs (se 1 (by rfl) ⟨78935, by rfl⟩) R157871
theorem R301927 : Reach 301927 := rs (se 1 (by rfl) ⟨226445, by rfl⟩) R452891
theorem R170873 : Reach 170873 := rs (se 2 (by rfl) ⟨64077, by rfl⟩) R128155
theorem R597779 : Reach 597779 := rs (se 1 (by rfl) ⟨448334, by rfl⟩) R896669
theorem R598265 : Reach 598265 := rs (se 2 (by rfl) ⟨224349, by rfl⟩) R448699
theorem R500255 : Reach 500255 := rs (se 1 (by rfl) ⟨375191, by rfl⟩) R750383
theorem R565811 : Reach 565811 := rs (se 1 (by rfl) ⟨424358, by rfl⟩) R848717
theorem R9904841 : Reach 9904841 := rs (se 2 (by rfl) ⟨3714315, by rfl⟩) R7428631
theorem R337193 : Reach 337193 := rs (se 2 (by rfl) ⟨126447, by rfl⟩) R252895
theorem R1418777 : Reach 1418777 := rs (se 2 (by rfl) ⟨532041, by rfl⟩) R1064083
theorem R75847 : Reach 75847 := rs (se 1 (by rfl) ⟨56885, by rfl⟩) R113771
theorem R76007 : Reach 76007 := rs (se 1 (by rfl) ⟨57005, by rfl⟩) R114011
theorem R174419 : Reach 174419 := rs (se 1 (by rfl) ⟨130814, by rfl⟩) R261629
theorem R76239 : Reach 76239 := rs (se 1 (by rfl) ⟨57179, by rfl⟩) R114359
theorem R76447 : Reach 76447 := rs (se 1 (by rfl) ⟨57335, by rfl⟩) R114671
theorem R76527 : Reach 76527 := rs (se 1 (by rfl) ⟨57395, by rfl⟩) R114791
theorem R437035 : Reach 437035 := rs (se 1 (by rfl) ⟨327776, by rfl⟩) R655553
theorem R4533083 : Reach 4533083 := rs (se 1 (by rfl) ⟨3399812, by rfl⟩) R6799625
theorem R240713 : Reach 240713 := rs (se 2 (by rfl) ⟨90267, by rfl⟩) R180535
theorem R208027 : Reach 208027 := rs (se 1 (by rfl) ⟨156020, by rfl⟩) R312041
theorem R77007 : Reach 77007 := rs (se 1 (by rfl) ⟨57755, by rfl⟩) R115511
theorem R77119 : Reach 77119 := rs (se 1 (by rfl) ⟨57839, by rfl⟩) R115679
theorem R77127 : Reach 77127 := rs (se 1 (by rfl) ⟨57845, by rfl⟩) R115691
theorem R175481 : Reach 175481 := rs (se 2 (by rfl) ⟨65805, by rfl⟩) R131611
theorem R961915 : Reach 961915 := rs (se 1 (by rfl) ⟨721436, by rfl⟩) R1442873
theorem R175535 : Reach 175535 := rs (se 1 (by rfl) ⟨131651, by rfl⟩) R263303
theorem R77295 : Reach 77295 := rs (se 1 (by rfl) ⟨57971, by rfl⟩) R115943
theorem R77339 : Reach 77339 := rs (se 1 (by rfl) ⟨58004, by rfl⟩) R116009
theorem R77727 : Reach 77727 := rs (se 1 (by rfl) ⟨58295, by rfl⟩) R116591
theorem R77851 : Reach 77851 := rs (se 1 (by rfl) ⟨58388, by rfl⟩) R116777
theorem R176183 : Reach 176183 := rs (se 1 (by rfl) ⟨132137, by rfl⟩) R264275
theorem R438493 : Reach 438493 := rs (se 3 (by rfl) ⟨82217, by rfl⟩) R164435
theorem R176543 : Reach 176543 := rs (se 1 (by rfl) ⟨132407, by rfl⟩) R264815
theorem R143849 : Reach 143849 := rs (se 2 (by rfl) ⟨53943, by rfl⟩) R107887
theorem R1421995 : Reach 1421995 := rs (se 1 (by rfl) ⟨1066496, by rfl⟩) R2132993
theorem R78619 : Reach 78619 := rs (se 1 (by rfl) ⟨58964, by rfl⟩) R117929
theorem R78695 : Reach 78695 := rs (se 1 (by rfl) ⟨59021, by rfl⟩) R118043
theorem R2700485 : Reach 2700485 := rs (se 4 (by rfl) ⟨253170, by rfl⟩) R506341
theorem R145223 : Reach 145223 := rs (se 1 (by rfl) ⟨108917, by rfl⟩) R217835
theorem R112859 : Reach 112859 := rs (se 1 (by rfl) ⟨84644, by rfl⟩) R169289
theorem R473759 : Reach 473759 := rs (se 1 (by rfl) ⟨355319, by rfl⟩) R710639
theorem R441227 : Reach 441227 := rs (se 1 (by rfl) ⟨330920, by rfl⟩) R661841
theorem R310355 : Reach 310355 := rs (se 1 (by rfl) ⟨232766, by rfl⟩) R465533
theorem R113819 : Reach 113819 := rs (se 1 (by rfl) ⟨85364, by rfl⟩) R170729
theorem R113831 : Reach 113831 := rs (se 1 (by rfl) ⟨85373, by rfl⟩) R170747
theorem R277715 : Reach 277715 := rs (se 1 (by rfl) ⟨208286, by rfl⟩) R416573
theorem R114683 : Reach 114683 := rs (se 1 (by rfl) ⟨86012, by rfl⟩) R172025
theorem R246071 : Reach 246071 := rs (se 1 (by rfl) ⟨184553, by rfl⟩) R369107
theorem R1491533 : Reach 1491533 := rs (se 3 (by rfl) ⟨279662, by rfl⟩) R559325
theorem R934523 : Reach 934523 := rs (se 1 (by rfl) ⟨700892, by rfl⟩) R1401785
theorem R378017 : Reach 378017 := rs (se 2 (by rfl) ⟨141756, by rfl⟩) R283513
theorem R312545 : Reach 312545 := rs (se 2 (by rfl) ⟨117204, by rfl⟩) R234409
theorem R410951 : Reach 410951 := rs (se 1 (by rfl) ⟨308213, by rfl⟩) R616427
theorem R83431 : Reach 83431 := rs (se 1 (by rfl) ⟨62573, by rfl⟩) R125147
theorem R116201 : Reach 116201 := rs (se 2 (by rfl) ⟨43575, by rfl⟩) R87151
theorem R116873 : Reach 116873 := rs (se 2 (by rfl) ⟨43827, by rfl⟩) R87655
theorem R1132775 : Reach 1132775 := rs (se 1 (by rfl) ⟨849581, by rfl⟩) R1699163
theorem R182683 : Reach 182683 := rs (se 1 (by rfl) ⟨137012, by rfl⟩) R274025
theorem R2280311 : Reach 2280311 := rs (se 1 (by rfl) ⟨1710233, by rfl⟩) R3420467
theorem R674689 : Reach 674689 := rs (se 2 (by rfl) ⟨253008, by rfl⟩) R506017
theorem R216377 : Reach 216377 := rs (se 2 (by rfl) ⟨81141, by rfl⟩) R162283
theorem R281983 : Reach 281983 := rs (se 1 (by rfl) ⟨211487, by rfl⟩) R422975
theorem R118271 : Reach 118271 := rs (se 1 (by rfl) ⟨88703, by rfl⟩) R177407
theorem R85531 : Reach 85531 := rs (se 1 (by rfl) ⟨64148, by rfl⟩) R128297
theorem R118439 : Reach 118439 := rs (se 1 (by rfl) ⟨88829, by rfl⟩) R177659
theorem R413981 : Reach 413981 := rs (se 3 (by rfl) ⟨77621, by rfl⟩) R155243
theorem R1167979 : Reach 1167979 := rs (se 1 (by rfl) ⟨875984, by rfl⟩) R1751969
theorem R218153 : Reach 218153 := rs (se 2 (by rfl) ⟨81807, by rfl⟩) R163615
theorem R120143 : Reach 120143 := rs (se 1 (by rfl) ⟨90107, by rfl⟩) R180215
theorem R579311 : Reach 579311 := rs (se 1 (by rfl) ⟨434483, by rfl⟩) R868967
theorem R120943 : Reach 120943 := rs (se 1 (by rfl) ⟨90707, by rfl⟩) R181415
theorem R1366145 : Reach 1366145 := rs (se 2 (by rfl) ⟨512304, by rfl⟩) R1024609
theorem R645407 : Reach 645407 := rs (se 1 (by rfl) ⟨484055, by rfl⟩) R968111
theorem R186779 : Reach 186779 := rs (se 1 (by rfl) ⟨140084, by rfl⟩) R280169
theorem R481751 : Reach 481751 := rs (se 1 (by rfl) ⟨361313, by rfl⟩) R722627
theorem R383939 : Reach 383939 := rs (se 1 (by rfl) ⟨287954, by rfl⟩) R575909
theorem R580769 : Reach 580769 := rs (se 2 (by rfl) ⟨217788, by rfl⟩) R435577
theorem R188297 : Reach 188297 := rs (se 2 (by rfl) ⟨70611, by rfl⟩) R141223
theorem R253907 : Reach 253907 := rs (se 1 (by rfl) ⟨190430, by rfl⟩) R380861
theorem R254015 : Reach 254015 := rs (se 1 (by rfl) ⟨190511, by rfl⟩) R381023
theorem R1401025 : Reach 1401025 := rs (se 2 (by rfl) ⟨525384, by rfl⟩) R1050769
theorem R287135 : Reach 287135 := rs (se 1 (by rfl) ⟨215351, by rfl⟩) R430703
theorem R90919 : Reach 90919 := rs (se 1 (by rfl) ⟨68189, by rfl⟩) R136379
theorem R255257 : Reach 255257 := rs (se 2 (by rfl) ⟨95721, by rfl⟩) R191443
theorem R255311 : Reach 255311 := rs (se 1 (by rfl) ⟨191483, by rfl⟩) R382967
theorem R386855 : Reach 386855 := rs (se 1 (by rfl) ⟨290141, by rfl⟩) R580283
theorem R387031 : Reach 387031 := rs (se 1 (by rfl) ⟨290273, by rfl⟩) R580547
theorem R256283 : Reach 256283 := rs (se 1 (by rfl) ⟨192212, by rfl⟩) R384425
theorem R748187 : Reach 748187 := rs (se 1 (by rfl) ⟨561140, by rfl⟩) R1122281
theorem R388151 : Reach 388151 := rs (se 1 (by rfl) ⟨291113, by rfl⟩) R582227
theorem R192719 : Reach 192719 := rs (se 1 (by rfl) ⟨144539, by rfl⟩) R289079
theorem R389447 : Reach 389447 := rs (se 1 (by rfl) ⟨292085, by rfl⟩) R584171
theorem R488591 : Reach 488591 := rs (se 1 (by rfl) ⟨366443, by rfl⟩) R732887
theorem R4945049 : Reach 4945049 := rs (se 2 (by rfl) ⟨1854393, by rfl⟩) R3708787
theorem R259307 : Reach 259307 := rs (se 1 (by rfl) ⟨194480, by rfl⟩) R388961
theorem R128567 : Reach 128567 := rs (se 1 (by rfl) ⟨96425, by rfl⟩) R192851
theorem R96319 : Reach 96319 := rs (se 1 (by rfl) ⟨72239, by rfl⟩) R144479
theorem R194633 : Reach 194633 := rs (se 2 (by rfl) ⟨72987, by rfl⟩) R145975
theorem R129161 : Reach 129161 := rs (se 2 (by rfl) ⟨48435, by rfl⟩) R96871
theorem R194795 : Reach 194795 := rs (se 1 (by rfl) ⟨146096, by rfl⟩) R292193
theorem R129343 : Reach 129343 := rs (se 1 (by rfl) ⟨97007, by rfl⟩) R194015
theorem R260711 : Reach 260711 := rs (se 1 (by rfl) ⟨195533, by rfl⟩) R391067
theorem R129775 : Reach 129775 := rs (se 1 (by rfl) ⟨97331, by rfl⟩) R194663
theorem R752723 : Reach 752723 := rs (se 1 (by rfl) ⟨564542, by rfl⟩) R1129085
theorem R326855 : Reach 326855 := rs (se 1 (by rfl) ⟨245141, by rfl⟩) R490283
theorem R196577 : Reach 196577 := rs (se 2 (by rfl) ⟨73716, by rfl⟩) R147433
theorem R164047 : Reach 164047 := rs (se 1 (by rfl) ⟨123035, by rfl⟩) R246071
theorem R1868033 : Reach 1868033 := rs (se 2 (by rfl) ⟨700512, by rfl⟩) R1401025
theorem R262439 : Reach 262439 := rs (se 1 (by rfl) ⟨196829, by rfl⟩) R393659
theorem R623015 : Reach 623015 := rs (se 1 (by rfl) ⟨467261, by rfl⟩) R934523
theorem R262655 : Reach 262655 := rs (se 1 (by rfl) ⟨196991, by rfl⟩) R393983
theorem R132347 : Reach 132347 := rs (se 1 (by rfl) ⟨99260, by rfl⟩) R198521
theorem R132455 : Reach 132455 := rs (se 1 (by rfl) ⟨99341, by rfl⟩) R198683
theorem R755183 : Reach 755183 := rs (se 1 (by rfl) ⟨566387, by rfl⟩) R1132775
theorem R264167 : Reach 264167 := rs (se 1 (by rfl) ⟨198125, by rfl⟩) R396251
theorem R265247 : Reach 265247 := rs (se 1 (by rfl) ⟨198935, by rfl⟩) R397871
theorem R199847 : Reach 199847 := rs (se 1 (by rfl) ⟨149885, by rfl⟩) R299771
theorem R659177 : Reach 659177 := rs (se 2 (by rfl) ⟨247191, by rfl⟩) R494383
theorem R266273 : Reach 266273 := rs (se 2 (by rfl) ⟨99852, by rfl⟩) R199705
theorem R430271 : Reach 430271 := rs (se 1 (by rfl) ⟨322703, by rfl⟩) R645407
theorem R266651 : Reach 266651 := rs (se 1 (by rfl) ⟨199988, by rfl⟩) R399977
theorem R1282553 : Reach 1282553 := rs (se 2 (by rfl) ⟨480957, by rfl⟩) R961915
theorem R266759 : Reach 266759 := rs (se 1 (by rfl) ⟨200069, by rfl⟩) R400139
theorem R398519 : Reach 398519 := rs (se 1 (by rfl) ⟨298889, by rfl⟩) R597779
theorem R169271 : Reach 169271 := rs (se 1 (by rfl) ⟨126953, by rfl⟩) R253907
theorem R169343 : Reach 169343 := rs (se 1 (by rfl) ⟨127007, by rfl⟩) R254015
theorem R398843 : Reach 398843 := rs (se 1 (by rfl) ⟨299132, by rfl⟩) R598265
theorem R333503 : Reach 333503 := rs (se 1 (by rfl) ⟨250127, by rfl⟩) R500255
theorem R170171 : Reach 170171 := rs (se 1 (by rfl) ⟨127628, by rfl⟩) R255257
theorem R170207 : Reach 170207 := rs (se 1 (by rfl) ⟨127655, by rfl⟩) R255311
theorem R137641 : Reach 137641 := rs (se 2 (by rfl) ⟨51615, by rfl⟩) R103231
theorem R170855 : Reach 170855 := rs (se 1 (by rfl) ⟨128141, by rfl⟩) R256283
theorem R498791 : Reach 498791 := rs (se 1 (by rfl) ⟨374093, by rfl⟩) R748187
theorem R1449161 : Reach 1449161 := rs (se 2 (by rfl) ⟨543435, by rfl⟩) R1086871
theorem R3022055 : Reach 3022055 := rs (se 1 (by rfl) ⟨2266541, by rfl⟩) R4533083
theorem R2236481 : Reach 2236481 := rs (se 2 (by rfl) ⟨838680, by rfl⟩) R1677361
theorem R172457 : Reach 172457 := rs (se 2 (by rfl) ⟨64671, by rfl⟩) R129343
theorem R172871 : Reach 172871 := rs (se 1 (by rfl) ⟨129653, by rfl⟩) R259307
theorem R173033 : Reach 173033 := rs (se 2 (by rfl) ⟨64887, by rfl⟩) R129775
theorem R140329 : Reach 140329 := rs (se 2 (by rfl) ⟨52623, by rfl⟩) R105247
theorem R402569 : Reach 402569 := rs (se 2 (by rfl) ⟨150963, by rfl⟩) R301927
theorem R75239 : Reach 75239 := rs (se 1 (by rfl) ⟨56429, by rfl⟩) R112859
theorem R173807 : Reach 173807 := rs (se 1 (by rfl) ⟨130355, by rfl⟩) R260711
theorem R501815 : Reach 501815 := rs (se 1 (by rfl) ⟨376361, by rfl⟩) R752723
theorem R206903 : Reach 206903 := rs (se 1 (by rfl) ⟨155177, by rfl⟩) R310355
theorem R75879 : Reach 75879 := rs (se 1 (by rfl) ⟨56909, by rfl⟩) R113819
theorem R75887 : Reach 75887 := rs (se 1 (by rfl) ⟨56915, by rfl⟩) R113831
theorem R76455 : Reach 76455 := rs (se 1 (by rfl) ⟨57341, by rfl⟩) R114683
theorem R994355 : Reach 994355 := rs (se 1 (by rfl) ⟨745766, by rfl⟩) R1491533
theorem R503147 : Reach 503147 := rs (se 1 (by rfl) ⟨377360, by rfl⟩) R754721
theorem R77467 : Reach 77467 := rs (se 1 (by rfl) ⟨58100, by rfl⟩) R116201
theorem R77915 : Reach 77915 := rs (se 1 (by rfl) ⟨58436, by rfl⟩) R116873
theorem R176363 : Reach 176363 := rs (se 1 (by rfl) ⟨132272, by rfl⟩) R264545
theorem R1520207 : Reach 1520207 := rs (se 1 (by rfl) ⟨1140155, by rfl⟩) R2280311
theorem R111241 : Reach 111241 := rs (se 2 (by rfl) ⟨41715, by rfl⟩) R83431
theorem R176777 : Reach 176777 := rs (se 2 (by rfl) ⟨66291, by rfl⟩) R132583
theorem R144251 : Reach 144251 := rs (se 1 (by rfl) ⟨108188, by rfl⟩) R216377
theorem R78847 : Reach 78847 := rs (se 1 (by rfl) ⟨59135, by rfl⟩) R118271
theorem R78959 : Reach 78959 := rs (se 1 (by rfl) ⟨59219, by rfl⟩) R118439
theorem R275987 : Reach 275987 := rs (se 1 (by rfl) ⟨206990, by rfl⟩) R413981
theorem R243577 : Reach 243577 := rs (se 2 (by rfl) ⟨91341, by rfl⟩) R182683
theorem R833453 : Reach 833453 := rs (se 3 (by rfl) ⟨156272, by rfl⟩) R312545
theorem R1095869 : Reach 1095869 := rs (se 3 (by rfl) ⟨205475, by rfl⟩) R410951
theorem R113051 : Reach 113051 := rs (se 1 (by rfl) ⟨84788, by rfl⟩) R169577
theorem R113135 : Reach 113135 := rs (se 1 (by rfl) ⟨84851, by rfl⟩) R169703
theorem R899585 : Reach 899585 := rs (se 2 (by rfl) ⟨337344, by rfl⟩) R674689
theorem R113279 : Reach 113279 := rs (se 1 (by rfl) ⟨84959, by rfl⟩) R169919
theorem R375977 : Reach 375977 := rs (se 2 (by rfl) ⟨140991, by rfl⟩) R281983
theorem R113915 : Reach 113915 := rs (se 1 (by rfl) ⟨85436, by rfl⟩) R170873
theorem R114041 : Reach 114041 := rs (se 2 (by rfl) ⟨42765, by rfl⟩) R85531
theorem R4112441 : Reach 4112441 := rs (se 2 (by rfl) ⟨1542165, by rfl⟩) R3084331
theorem R835913 : Reach 835913 := rs (se 2 (by rfl) ⟨313467, by rfl⟩) R626935
theorem R377207 : Reach 377207 := rs (se 1 (by rfl) ⟨282905, by rfl⟩) R565811
theorem R6603227 : Reach 6603227 := rs (se 1 (by rfl) ⟨4952420, by rfl⟩) R9904841
theorem R1557305 : Reach 1557305 := rs (se 2 (by rfl) ⟨583989, by rfl⟩) R1167979
theorem R116279 : Reach 116279 := rs (se 1 (by rfl) ⟨87209, by rfl⟩) R174419
theorem R1231037 : Reach 1231037 := rs (se 3 (by rfl) ⟨230819, by rfl⟩) R461639
theorem R116987 : Reach 116987 := rs (se 1 (by rfl) ⟨87740, by rfl⟩) R175481
theorem R117023 : Reach 117023 := rs (se 1 (by rfl) ⟨87767, by rfl⟩) R175535
theorem R117455 : Reach 117455 := rs (se 1 (by rfl) ⟨88091, by rfl⟩) R176183
theorem R117695 : Reach 117695 := rs (se 1 (by rfl) ⟨88271, by rfl⟩) R176543
theorem R740573 : Reach 740573 := rs (se 3 (by rfl) ⟨138857, by rfl⟩) R277715
theorem R3296699 : Reach 3296699 := rs (se 1 (by rfl) ⟨2472524, by rfl⟩) R4945049
theorem R85711 : Reach 85711 := rs (se 1 (by rfl) ⟨64283, by rfl⟩) R128567
theorem R86107 : Reach 86107 := rs (se 1 (by rfl) ⟨64580, by rfl⟩) R129161
theorem R315839 : Reach 315839 := rs (se 1 (by rfl) ⟨236879, by rfl⟩) R473759
theorem R217903 : Reach 217903 := rs (se 1 (by rfl) ⟨163427, by rfl⟩) R326855
theorem R645029 : Reach 645029 := rs (se 4 (by rfl) ⟨60471, by rfl⟩) R120943
theorem R252011 : Reach 252011 := rs (se 1 (by rfl) ⟨189008, by rfl⟩) R378017
theorem R219419 : Reach 219419 := rs (se 1 (by rfl) ⟨164564, by rfl⟩) R329129
theorem R121225 : Reach 121225 := rs (se 2 (by rfl) ⟨45459, by rfl⟩) R90919
theorem R285191 : Reach 285191 := rs (se 1 (by rfl) ⟨213893, by rfl⟩) R427787
theorem R285403 : Reach 285403 := rs (se 1 (by rfl) ⟨214052, by rfl⟩) R428105
theorem R516041 : Reach 516041 := rs (se 2 (by rfl) ⟨193515, by rfl⟩) R387031
theorem R581741 : Reach 581741 := rs (se 3 (by rfl) ⟨109076, by rfl⟩) R218153
theorem R320381 : Reach 320381 := rs (se 3 (by rfl) ⟨60071, by rfl⟩) R120143
theorem R582713 : Reach 582713 := rs (se 2 (by rfl) ⟨218517, by rfl⟩) R437035
theorem R386207 : Reach 386207 := rs (se 1 (by rfl) ⟨289655, by rfl⟩) R579311
theorem R910763 : Reach 910763 := rs (se 1 (by rfl) ⟨683072, by rfl⟩) R1366145
theorem R124519 : Reach 124519 := rs (se 1 (by rfl) ⟨93389, by rfl⟩) R186779
theorem R321167 : Reach 321167 := rs (se 1 (by rfl) ⟨240875, by rfl⟩) R481751
theorem R255959 : Reach 255959 := rs (se 1 (by rfl) ⟨191969, by rfl⟩) R383939
theorem R387179 : Reach 387179 := rs (se 1 (by rfl) ⟨290384, by rfl⟩) R580769
theorem R125531 : Reach 125531 := rs (se 1 (by rfl) ⟨94148, by rfl⟩) R188297
theorem R191423 : Reach 191423 := rs (se 1 (by rfl) ⟨143567, by rfl⟩) R287135
theorem R584657 : Reach 584657 := rs (se 2 (by rfl) ⟨219246, by rfl⟩) R438493
theorem R1109477 : Reach 1109477 := rs (se 4 (by rfl) ⟨104013, by rfl⟩) R208027
theorem R224795 : Reach 224795 := rs (se 1 (by rfl) ⟨168596, by rfl⟩) R337193
theorem R1895993 : Reach 1895993 := rs (se 2 (by rfl) ⟨710997, by rfl⟩) R1421995
theorem R945851 : Reach 945851 := rs (se 1 (by rfl) ⟨709388, by rfl⟩) R1418777
theorem R257903 : Reach 257903 := rs (se 1 (by rfl) ⟨193427, by rfl⟩) R386855
theorem R258767 : Reach 258767 := rs (se 1 (by rfl) ⟨194075, by rfl⟩) R388151
theorem R160475 : Reach 160475 := rs (se 1 (by rfl) ⟨120356, by rfl⟩) R240713
theorem R1012961 : Reach 1012961 := rs (se 2 (by rfl) ⟨379860, by rfl⟩) R759721
theorem R128425 : Reach 128425 := rs (se 2 (by rfl) ⟨48159, by rfl⟩) R96319
theorem R882089 : Reach 882089 := rs (se 2 (by rfl) ⟨330783, by rfl⟩) R661567
theorem R128479 : Reach 128479 := rs (se 1 (by rfl) ⟨96359, by rfl⟩) R192719
theorem R259631 : Reach 259631 := rs (se 1 (by rfl) ⟨194723, by rfl⟩) R389447
theorem R95899 : Reach 95899 := rs (se 1 (by rfl) ⟨71924, by rfl⟩) R143849
theorem R325727 : Reach 325727 := rs (se 1 (by rfl) ⟨244295, by rfl⟩) R488591
theorem R1800323 : Reach 1800323 := rs (se 1 (by rfl) ⟨1350242, by rfl⟩) R2700485
theorem R96815 : Reach 96815 := rs (se 1 (by rfl) ⟨72611, by rfl⟩) R145223
theorem R129755 : Reach 129755 := rs (se 1 (by rfl) ⟨97316, by rfl⟩) R194633
theorem R129863 : Reach 129863 := rs (se 1 (by rfl) ⟨97397, by rfl⟩) R194795
theorem R294151 : Reach 294151 := rs (se 1 (by rfl) ⟨220613, by rfl⟩) R441227
theorem R131051 : Reach 131051 := rs (se 1 (by rfl) ⟨98288, by rfl⟩) R196577
theorem R557275 : Reach 557275 := rs (se 1 (by rfl) ⟨417956, by rfl⟩) R835913
theorem R4981421 : Reach 4981421 := rs (se 3 (by rfl) ⟨934016, by rfl⟩) R1868033
theorem R820691 : Reach 820691 := rs (se 1 (by rfl) ⟨615518, by rfl⟩) R1231037
theorem R427933 : Reach 427933 := rs (se 3 (by rfl) ⟨80237, by rfl⟩) R160475
theorem R133231 : Reach 133231 := rs (se 1 (by rfl) ⟨99923, by rfl⟩) R199847
theorem R166025 : Reach 166025 := rs (se 2 (by rfl) ⟨62259, by rfl⟩) R124519
theorem R493715 : Reach 493715 := rs (se 1 (by rfl) ⟨370286, by rfl⟩) R740573
theorem R2197799 : Reach 2197799 := rs (se 1 (by rfl) ⟨1648349, by rfl⟩) R3296699
theorem R855035 : Reach 855035 := rs (se 1 (by rfl) ⟨641276, by rfl⟩) R1282553
theorem R265679 : Reach 265679 := rs (se 1 (by rfl) ⟨199259, by rfl⟩) R398519
theorem R265895 : Reach 265895 := rs (se 1 (by rfl) ⟨199421, by rfl⟩) R398843
theorem R430019 : Reach 430019 := rs (se 1 (by rfl) ⟨322514, by rfl⟩) R645029
theorem R168007 : Reach 168007 := rs (se 1 (by rfl) ⟨126005, by rfl⟩) R252011
theorem R332527 : Reach 332527 := rs (se 1 (by rfl) ⟨249395, by rfl⟩) R498791
theorem R268379 : Reach 268379 := rs (se 1 (by rfl) ⟨201284, by rfl⟩) R402569
theorem R170639 : Reach 170639 := rs (se 1 (by rfl) ⟨127979, by rfl⟩) R255959
theorem R334543 : Reach 334543 := rs (se 1 (by rfl) ⟨250907, by rfl⟩) R501815
theorem R137935 : Reach 137935 := rs (se 1 (by rfl) ⟨103451, by rfl⟩) R206903
theorem R171233 : Reach 171233 := rs (se 2 (by rfl) ⟨64212, by rfl⟩) R128425
theorem R171305 : Reach 171305 := rs (se 2 (by rfl) ⟨64239, by rfl⟩) R128479
theorem R662903 : Reach 662903 := rs (se 1 (by rfl) ⟨497177, by rfl⟩) R994355
theorem R335431 : Reach 335431 := rs (se 1 (by rfl) ⟨251573, by rfl⟩) R503147
theorem R171935 : Reach 171935 := rs (se 1 (by rfl) ⟨128951, by rfl⟩) R257903
theorem R172511 : Reach 172511 := rs (se 1 (by rfl) ⟨129383, by rfl⟩) R258767
theorem R173087 : Reach 173087 := rs (se 1 (by rfl) ⟨129815, by rfl⟩) R259631
theorem R730579 : Reach 730579 := rs (se 1 (by rfl) ⟨547934, by rfl⟩) R1095869
theorem R75367 : Reach 75367 := rs (se 1 (by rfl) ⟨56525, by rfl⟩) R113051
theorem R75423 : Reach 75423 := rs (se 1 (by rfl) ⟨56567, by rfl⟩) R113135
theorem R599723 : Reach 599723 := rs (se 1 (by rfl) ⟨449792, by rfl⟩) R899585
theorem R75519 : Reach 75519 := rs (se 1 (by rfl) ⟨56639, by rfl⟩) R113279
theorem R75943 : Reach 75943 := rs (se 1 (by rfl) ⟨56957, by rfl⟩) R113915
theorem R76027 : Reach 76027 := rs (se 1 (by rfl) ⟨57020, by rfl⟩) R114041
theorem R174959 : Reach 174959 := rs (se 1 (by rfl) ⟨131219, by rfl⟩) R262439
theorem R4402151 : Reach 4402151 := rs (se 1 (by rfl) ⟨3301613, by rfl⟩) R6603227
theorem R175103 : Reach 175103 := rs (se 1 (by rfl) ⟨131327, by rfl⟩) R262655
theorem R503455 : Reach 503455 := rs (se 1 (by rfl) ⟨377591, by rfl⟩) R755183
theorem R77519 : Reach 77519 := rs (se 1 (by rfl) ⟨58139, by rfl⟩) R116279
theorem R176111 : Reach 176111 := rs (se 1 (by rfl) ⟨132083, by rfl⟩) R264167
theorem R77991 : Reach 77991 := rs (se 1 (by rfl) ⟨58493, by rfl⟩) R116987
theorem R78015 : Reach 78015 := rs (se 1 (by rfl) ⟨58511, by rfl⟩) R117023
theorem R78303 : Reach 78303 := rs (se 1 (by rfl) ⟨58727, by rfl⟩) R117455
theorem R78463 : Reach 78463 := rs (se 1 (by rfl) ⟨58847, by rfl⟩) R117695
theorem R176831 : Reach 176831 := rs (se 1 (by rfl) ⟨132623, by rfl⟩) R265247
theorem R439451 : Reach 439451 := rs (se 1 (by rfl) ⟨329588, by rfl⟩) R659177
theorem R177515 : Reach 177515 := rs (se 1 (by rfl) ⟨133136, by rfl⟩) R266273
theorem R177767 : Reach 177767 := rs (se 1 (by rfl) ⟨133325, by rfl⟩) R266651
theorem R177839 : Reach 177839 := rs (se 1 (by rfl) ⟨133379, by rfl⟩) R266759
theorem R112847 : Reach 112847 := rs (se 1 (by rfl) ⟨84635, by rfl⟩) R169271
theorem R112895 : Reach 112895 := rs (se 1 (by rfl) ⟨84671, by rfl⟩) R169343
theorem R113447 : Reach 113447 := rs (se 1 (by rfl) ⟨85085, by rfl⟩) R170171
theorem R113471 : Reach 113471 := rs (se 1 (by rfl) ⟨85103, by rfl⟩) R170207
theorem R146279 : Reach 146279 := rs (se 1 (by rfl) ⟨109709, by rfl⟩) R219419
theorem R113903 : Reach 113903 := rs (se 1 (by rfl) ⟨85427, by rfl⟩) R170855
theorem R966107 : Reach 966107 := rs (se 1 (by rfl) ⟨724580, by rfl⟩) R1449161
theorem R2014703 : Reach 2014703 := rs (se 1 (by rfl) ⟨1511027, by rfl⟩) R3022055
theorem R114281 : Reach 114281 := rs (se 2 (by rfl) ⟨42855, by rfl⟩) R85711
theorem R344027 : Reach 344027 := rs (se 1 (by rfl) ⟨258020, by rfl⟩) R516041
theorem R1490987 : Reach 1490987 := rs (se 1 (by rfl) ⟨1118240, by rfl⟩) R2236481
theorem R114809 : Reach 114809 := rs (se 2 (by rfl) ⟨43053, by rfl⟩) R86107
theorem R114971 : Reach 114971 := rs (se 1 (by rfl) ⟨86228, by rfl⟩) R172457
theorem R115247 : Reach 115247 := rs (se 1 (by rfl) ⟨86435, by rfl⟩) R172871
theorem R213587 : Reach 213587 := rs (se 1 (by rfl) ⟨160190, by rfl⟩) R320381
theorem R115355 : Reach 115355 := rs (se 1 (by rfl) ⟨86516, by rfl⟩) R173033
theorem R148321 : Reach 148321 := rs (se 2 (by rfl) ⟨55620, by rfl⟩) R111241
theorem R607175 : Reach 607175 := rs (se 1 (by rfl) ⟨455381, by rfl⟩) R910763
theorem R214111 : Reach 214111 := rs (se 1 (by rfl) ⟨160583, by rfl⟩) R321167
theorem R115871 : Reach 115871 := rs (se 1 (by rfl) ⟨86903, by rfl⟩) R173807
theorem R83687 : Reach 83687 := rs (se 1 (by rfl) ⟨62765, by rfl⟩) R125531
theorem R739651 : Reach 739651 := rs (se 1 (by rfl) ⟨554738, by rfl⟩) R1109477
theorem R149863 : Reach 149863 := rs (se 1 (by rfl) ⟨112397, by rfl⟩) R224795
theorem R1263995 : Reach 1263995 := rs (se 1 (by rfl) ⟨947996, by rfl⟩) R1895993
theorem R117575 : Reach 117575 := rs (se 1 (by rfl) ⟨88181, by rfl⟩) R176363
theorem R117851 : Reach 117851 := rs (se 1 (by rfl) ⟨88388, by rfl⟩) R176777
theorem R183521 : Reach 183521 := rs (se 2 (by rfl) ⟨68820, by rfl⟩) R137641
theorem R675307 : Reach 675307 := rs (se 1 (by rfl) ⟨506480, by rfl⟩) R1012961
theorem R380537 : Reach 380537 := rs (se 2 (by rfl) ⟨142701, by rfl⟩) R285403
theorem R183991 : Reach 183991 := rs (se 1 (by rfl) ⟨137993, by rfl⟩) R275987
theorem R217151 : Reach 217151 := rs (se 1 (by rfl) ⟨162863, by rfl⟩) R325727
theorem R1200215 : Reach 1200215 := rs (se 1 (by rfl) ⟨900161, by rfl⟩) R1800323
theorem R86503 : Reach 86503 := rs (se 1 (by rfl) ⟨64877, by rfl⟩) R129755
theorem R86575 : Reach 86575 := rs (se 1 (by rfl) ⟨64931, by rfl⟩) R129863
theorem R1299077 : Reach 1299077 := rs (se 4 (by rfl) ⟨121788, by rfl⟩) R243577
theorem R250651 : Reach 250651 := rs (se 1 (by rfl) ⟨187988, by rfl⟩) R375977
theorem R87367 : Reach 87367 := rs (se 1 (by rfl) ⟨65525, by rfl⟩) R131051
theorem R2741627 : Reach 2741627 := rs (se 1 (by rfl) ⟨2056220, by rfl⟩) R4112441
theorem R251471 : Reach 251471 := rs (se 1 (by rfl) ⟨188603, by rfl⟩) R377207
theorem R218729 : Reach 218729 := rs (se 2 (by rfl) ⟨82023, by rfl⟩) R164047
theorem R415343 : Reach 415343 := rs (se 1 (by rfl) ⟨311507, by rfl⟩) R623015
theorem R1038203 : Reach 1038203 := rs (se 1 (by rfl) ⟨778652, by rfl⟩) R1557305
theorem R88231 : Reach 88231 := rs (se 1 (by rfl) ⟨66173, by rfl⟩) R132347
theorem R88303 : Reach 88303 := rs (se 1 (by rfl) ⟨66227, by rfl⟩) R132455
theorem R842237 : Reach 842237 := rs (se 3 (by rfl) ⟨157919, by rfl⟩) R315839
theorem R187105 : Reach 187105 := rs (se 2 (by rfl) ⟨70164, by rfl⟩) R140329
theorem R286847 : Reach 286847 := rs (se 1 (by rfl) ⟨215135, by rfl⟩) R430271
theorem R222335 : Reach 222335 := rs (se 1 (by rfl) ⟨166751, by rfl⟩) R333503
theorem R190127 : Reach 190127 := rs (se 1 (by rfl) ⟨142595, by rfl⟩) R285191
theorem R387827 : Reach 387827 := rs (se 1 (by rfl) ⟨290870, by rfl⟩) R581741
theorem R388475 : Reach 388475 := rs (se 1 (by rfl) ⟨291356, by rfl⟩) R582713
theorem R257471 : Reach 257471 := rs (se 1 (by rfl) ⟨193103, by rfl⟩) R386207
theorem R290537 : Reach 290537 := rs (se 2 (by rfl) ⟨108951, by rfl⟩) R217903
theorem R258119 : Reach 258119 := rs (se 1 (by rfl) ⟨193589, by rfl⟩) R387179
theorem R258173 : Reach 258173 := rs (se 3 (by rfl) ⟨48407, by rfl⟩) R96815
theorem R127615 : Reach 127615 := rs (se 1 (by rfl) ⟨95711, by rfl⟩) R191423
theorem R389771 : Reach 389771 := rs (se 1 (by rfl) ⟨292328, by rfl⟩) R584657
theorem R127865 : Reach 127865 := rs (se 2 (by rfl) ⟨47949, by rfl⟩) R95899
theorem R1013471 : Reach 1013471 := rs (se 1 (by rfl) ⟨760103, by rfl⟩) R1520207
theorem R161633 : Reach 161633 := rs (se 2 (by rfl) ⟨60612, by rfl⟩) R121225
theorem R96167 : Reach 96167 := rs (se 1 (by rfl) ⟨72125, by rfl⟩) R144251
theorem R588059 : Reach 588059 := rs (se 1 (by rfl) ⟨441044, by rfl⟩) R882089
theorem R555635 : Reach 555635 := rs (se 1 (by rfl) ⟨416726, by rfl⟩) R833453
theorem R392201 : Reach 392201 := rs (se 2 (by rfl) ⟨147075, by rfl⟩) R294151
theorem R2522269 : Reach 2522269 := rs (se 3 (by rfl) ⟨472925, by rfl⟩) R945851
theorem R197761 : Reach 197761 := rs (se 2 (by rfl) ⟨74160, by rfl⟩) R148321
theorem R986201 : Reach 986201 := rs (se 2 (by rfl) ⟨369825, by rfl⟩) R739651
theorem R199817 : Reach 199817 := rs (se 2 (by rfl) ⟨74931, by rfl⟩) R149863
theorem R7311005 : Reach 7311005 := rs (se 3 (by rfl) ⟨1370813, by rfl⟩) R2741627
theorem R692135 : Reach 692135 := rs (se 1 (by rfl) ⟨519101, by rfl⟩) R1038203
theorem R561491 : Reach 561491 := rs (se 1 (by rfl) ⟨421118, by rfl⟩) R842237
theorem R431021 : Reach 431021 := rs (se 3 (by rfl) ⟨80816, by rfl⟩) R161633
theorem R1316573 : Reach 1316573 := rs (se 3 (by rfl) ⟨246857, by rfl⟩) R493715
theorem R170153 : Reach 170153 := rs (se 2 (by rfl) ⟨63807, by rfl⟩) R127615
theorem R334201 : Reach 334201 := rs (se 2 (by rfl) ⟨125325, by rfl⟩) R250651
theorem R399815 : Reach 399815 := rs (se 1 (by rfl) ⟨299861, by rfl⟩) R599723
theorem R171647 : Reach 171647 := rs (se 1 (by rfl) ⟨128735, by rfl⟩) R257471
theorem R172079 : Reach 172079 := rs (se 1 (by rfl) ⟨129059, by rfl⟩) R258119
theorem R172115 : Reach 172115 := rs (se 1 (by rfl) ⟨129086, by rfl⟩) R258173
theorem R75231 : Reach 75231 := rs (se 1 (by rfl) ⟨56423, by rfl⟩) R112847
theorem R75263 : Reach 75263 := rs (se 1 (by rfl) ⟨56447, by rfl⟩) R112895
theorem R370423 : Reach 370423 := rs (se 1 (by rfl) ⟨277817, by rfl⟩) R555635
theorem R75631 : Reach 75631 := rs (se 1 (by rfl) ⟨56723, by rfl⟩) R113447
theorem R75647 : Reach 75647 := rs (se 1 (by rfl) ⟨56735, by rfl⟩) R113471
theorem R75935 : Reach 75935 := rs (se 1 (by rfl) ⟨56951, by rfl⟩) R113903
theorem R76187 : Reach 76187 := rs (se 1 (by rfl) ⟨57140, by rfl⟩) R114281
theorem R993991 : Reach 993991 := rs (se 1 (by rfl) ⟨745493, by rfl⟩) R1490987
theorem R76539 : Reach 76539 := rs (se 1 (by rfl) ⟨57404, by rfl⟩) R114809
theorem R76647 : Reach 76647 := rs (se 1 (by rfl) ⟨57485, by rfl⟩) R114971
theorem R76831 : Reach 76831 := rs (se 1 (by rfl) ⟨57623, by rfl⟩) R115247
theorem R142391 : Reach 142391 := rs (se 1 (by rfl) ⟨106793, by rfl⟩) R213587
theorem R76903 : Reach 76903 := rs (se 1 (by rfl) ⟨57677, by rfl⟩) R115355
theorem R3320947 : Reach 3320947 := rs (se 1 (by rfl) ⟨2490710, by rfl⟩) R4981421
theorem R404783 : Reach 404783 := rs (se 1 (by rfl) ⟨303587, by rfl⟩) R607175
theorem R77247 : Reach 77247 := rs (se 1 (by rfl) ⟨57935, by rfl⟩) R115871
theorem R110683 : Reach 110683 := rs (se 1 (by rfl) ⟨83012, by rfl⟩) R166025
theorem R78383 : Reach 78383 := rs (se 1 (by rfl) ⟨58787, by rfl⟩) R117575
theorem R570023 : Reach 570023 := rs (se 1 (by rfl) ⟨427517, by rfl⟩) R855035
theorem R78567 : Reach 78567 := rs (se 1 (by rfl) ⟨58925, by rfl⟩) R117851
theorem R177119 : Reach 177119 := rs (se 1 (by rfl) ⟨132839, by rfl⟩) R265679
theorem R177263 : Reach 177263 := rs (se 1 (by rfl) ⟨132947, by rfl⟩) R265895
theorem R570577 : Reach 570577 := rs (se 2 (by rfl) ⟨213966, by rfl⟩) R427933
theorem R144767 : Reach 144767 := rs (se 1 (by rfl) ⟨108575, by rfl⟩) R217151
theorem R177641 : Reach 177641 := rs (se 2 (by rfl) ⟨66615, by rfl⟩) R133231
theorem R866051 : Reach 866051 := rs (se 1 (by rfl) ⟨649538, by rfl⟩) R1299077
theorem R145819 : Reach 145819 := rs (se 1 (by rfl) ⟨109364, by rfl⟩) R218729
theorem R276895 : Reach 276895 := rs (se 1 (by rfl) ⟨207671, by rfl⟩) R415343
theorem R178919 : Reach 178919 := rs (se 1 (by rfl) ⟨134189, by rfl⟩) R268379
theorem R670589 : Reach 670589 := rs (se 3 (by rfl) ⟨125735, by rfl⟩) R251471
theorem R113759 : Reach 113759 := rs (se 1 (by rfl) ⟨85319, by rfl⟩) R170639
theorem R507005 : Reach 507005 := rs (se 3 (by rfl) ⟨95063, by rfl⟩) R190127
theorem R900409 : Reach 900409 := rs (se 2 (by rfl) ⟨337653, by rfl⟩) R675307
theorem R114155 : Reach 114155 := rs (se 1 (by rfl) ⟨85616, by rfl⟩) R171233
theorem R114203 : Reach 114203 := rs (se 1 (by rfl) ⟨85652, by rfl⟩) R171305
theorem R671273 : Reach 671273 := rs (se 2 (by rfl) ⟨251727, by rfl⟩) R503455
theorem R245321 : Reach 245321 := rs (se 2 (by rfl) ⟨91995, by rfl⟩) R183991
theorem R441935 : Reach 441935 := rs (se 1 (by rfl) ⟨331451, by rfl⟩) R662903
theorem R114623 : Reach 114623 := rs (se 1 (by rfl) ⟨85967, by rfl⟩) R171935
theorem R115007 : Reach 115007 := rs (se 1 (by rfl) ⟨86255, by rfl⟩) R172511
theorem R115337 : Reach 115337 := rs (se 2 (by rfl) ⟨43251, by rfl⟩) R86503
theorem R115391 : Reach 115391 := rs (se 1 (by rfl) ⟨86543, by rfl⟩) R173087
theorem R115433 : Reach 115433 := rs (se 2 (by rfl) ⟨43287, by rfl⟩) R86575
theorem R148223 : Reach 148223 := rs (se 1 (by rfl) ⟨111167, by rfl⟩) R222335
theorem R13452101 : Reach 13452101 := rs (se 4 (by rfl) ⟨1261134, by rfl⟩) R2522269
theorem R443369 : Reach 443369 := rs (se 2 (by rfl) ⟨166263, by rfl⟩) R332527
theorem R116489 : Reach 116489 := rs (se 2 (by rfl) ⟨43683, by rfl⟩) R87367
theorem R116639 : Reach 116639 := rs (se 1 (by rfl) ⟨87479, by rfl⟩) R174959
theorem R2934767 : Reach 2934767 := rs (se 1 (by rfl) ⟨2201075, by rfl⟩) R4402151
theorem R116735 : Reach 116735 := rs (se 1 (by rfl) ⟨87551, by rfl⟩) R175103
theorem R117407 : Reach 117407 := rs (se 1 (by rfl) ⟨88055, by rfl⟩) R176111
theorem R117641 : Reach 117641 := rs (se 2 (by rfl) ⟨44115, by rfl⟩) R88231
theorem R117737 : Reach 117737 := rs (se 2 (by rfl) ⟨44151, by rfl⟩) R88303
theorem R117887 : Reach 117887 := rs (se 1 (by rfl) ⟨88415, by rfl⟩) R176831
theorem R85243 : Reach 85243 := rs (se 1 (by rfl) ⟨63932, by rfl⟩) R127865
theorem R118343 : Reach 118343 := rs (se 1 (by rfl) ⟨88757, by rfl⟩) R177515
theorem R446057 : Reach 446057 := rs (se 2 (by rfl) ⟨167271, by rfl⟩) R334543
theorem R183913 : Reach 183913 := rs (se 2 (by rfl) ⟨68967, by rfl⟩) R137935
theorem R249473 : Reach 249473 := rs (se 2 (by rfl) ⟨93552, by rfl⟩) R187105
theorem R118511 : Reach 118511 := rs (se 1 (by rfl) ⟨88883, by rfl⟩) R177767
theorem R118559 : Reach 118559 := rs (se 1 (by rfl) ⟨88919, by rfl⟩) R177839
theorem R675647 : Reach 675647 := rs (se 1 (by rfl) ⟨506735, by rfl⟩) R1013471
theorem R447241 : Reach 447241 := rs (se 2 (by rfl) ⟨167715, by rfl⟩) R335431
theorem R644071 : Reach 644071 := rs (se 1 (by rfl) ⟨483053, by rfl⟩) R966107
theorem R3200573 : Reach 3200573 := rs (se 3 (by rfl) ⟨600107, by rfl⟩) R1200215
theorem R743033 : Reach 743033 := rs (se 2 (by rfl) ⟨278637, by rfl⟩) R557275
theorem R547127 : Reach 547127 := rs (se 1 (by rfl) ⟨410345, by rfl⟩) R820691
theorem R285481 : Reach 285481 := rs (se 2 (by rfl) ⟨107055, by rfl⟩) R214111
theorem R1465199 : Reach 1465199 := rs (se 1 (by rfl) ⟨1098899, by rfl⟩) R2197799
theorem R842663 : Reach 842663 := rs (se 1 (by rfl) ⟨631997, by rfl⟩) R1263995
theorem R974105 : Reach 974105 := rs (se 2 (by rfl) ⟨365289, by rfl⟩) R730579
theorem R122347 : Reach 122347 := rs (se 1 (by rfl) ⟨91760, by rfl⟩) R183521
theorem R253691 : Reach 253691 := rs (se 1 (by rfl) ⟨190268, by rfl⟩) R380537
theorem R286679 : Reach 286679 := rs (se 1 (by rfl) ⟨215009, by rfl⟩) R430019
theorem R223165 : Reach 223165 := rs (se 3 (by rfl) ⟨41843, by rfl⟩) R83687
theorem R256445 : Reach 256445 := rs (se 3 (by rfl) ⟨48083, by rfl⟩) R96167
theorem R191231 : Reach 191231 := rs (se 1 (by rfl) ⟨143423, by rfl⟩) R286847
theorem R224009 : Reach 224009 := rs (se 2 (by rfl) ⟨84003, by rfl⟩) R168007
theorem R258551 : Reach 258551 := rs (se 1 (by rfl) ⟨193913, by rfl⟩) R387827
theorem R258983 : Reach 258983 := rs (se 1 (by rfl) ⟨194237, by rfl⟩) R388475
theorem R193691 : Reach 193691 := rs (se 1 (by rfl) ⟨145268, by rfl⟩) R290537
theorem R259847 : Reach 259847 := rs (se 1 (by rfl) ⟨194885, by rfl⟩) R389771
theorem R292967 : Reach 292967 := rs (se 1 (by rfl) ⟨219725, by rfl⟩) R439451
theorem R392039 : Reach 392039 := rs (se 1 (by rfl) ⟨294029, by rfl⟩) R588059
theorem R97519 : Reach 97519 := rs (se 1 (by rfl) ⟨73139, by rfl⟩) R146279
theorem R261467 : Reach 261467 := rs (se 1 (by rfl) ⟨196100, by rfl⟩) R392201
theorem R1343135 : Reach 1343135 := rs (se 1 (by rfl) ⟨1007351, by rfl⟩) R2014703
theorem R229351 : Reach 229351 := rs (se 1 (by rfl) ⟨172013, by rfl⟩) R344027
theorem R98815 : Reach 98815 := rs (se 1 (by rfl) ⟨74111, by rfl⟩) R148223
theorem R295579 : Reach 295579 := rs (se 1 (by rfl) ⟨221684, by rfl⟩) R443369
theorem R263681 : Reach 263681 := rs (se 2 (by rfl) ⟨98880, by rfl⟩) R197761
theorem R657467 : Reach 657467 := rs (se 1 (by rfl) ⟨493100, by rfl⟩) R986201
theorem R133211 : Reach 133211 := rs (se 1 (by rfl) ⟨99908, by rfl⟩) R199817
theorem R493897 : Reach 493897 := rs (se 2 (by rfl) ⟨185211, by rfl⟩) R370423
theorem R297371 : Reach 297371 := rs (se 1 (by rfl) ⟨223028, by rfl⟩) R446057
theorem R166315 : Reach 166315 := rs (se 1 (by rfl) ⟨124736, by rfl⟩) R249473
theorem R297553 : Reach 297553 := rs (se 2 (by rfl) ⟨111582, by rfl⟩) R223165
theorem R461423 : Reach 461423 := rs (se 1 (by rfl) ⟨346067, by rfl⟩) R692135
theorem R2133715 : Reach 2133715 := rs (se 1 (by rfl) ⟨1600286, by rfl⟩) R3200573
theorem R4427929 : Reach 4427929 := rs (se 2 (by rfl) ⟨1660473, by rfl⟩) R3320947
theorem R364751 : Reach 364751 := rs (se 1 (by rfl) ⟨273563, by rfl⟩) R547127
theorem R266543 : Reach 266543 := rs (se 1 (by rfl) ⟨199907, by rfl⟩) R399815
theorem R561775 : Reach 561775 := rs (se 1 (by rfl) ⟨421331, by rfl⟩) R842663
theorem R169127 : Reach 169127 := rs (se 1 (by rfl) ⟨126845, by rfl⟩) R253691
theorem R596321 : Reach 596321 := rs (se 2 (by rfl) ⟨223620, by rfl⟩) R447241
theorem R858761 : Reach 858761 := rs (se 2 (by rfl) ⟨322035, by rfl⟩) R644071
theorem R760769 : Reach 760769 := rs (se 2 (by rfl) ⟨285288, by rfl⟩) R570577
theorem R170963 : Reach 170963 := rs (se 1 (by rfl) ⟨128222, by rfl⟩) R256445
theorem R269855 : Reach 269855 := rs (se 1 (by rfl) ⟨202391, by rfl⟩) R404783
theorem R172367 : Reach 172367 := rs (se 1 (by rfl) ⟨129275, by rfl⟩) R258551
theorem R369193 : Reach 369193 := rs (se 2 (by rfl) ⟨138447, by rfl⟩) R276895
theorem R172655 : Reach 172655 := rs (se 1 (by rfl) ⟨129491, by rfl⟩) R258983
theorem R173231 : Reach 173231 := rs (se 1 (by rfl) ⟨129923, by rfl⟩) R259847
theorem R75839 : Reach 75839 := rs (se 1 (by rfl) ⟨56879, by rfl⟩) R113759
theorem R338003 : Reach 338003 := rs (se 1 (by rfl) ⟨253502, by rfl⟩) R507005
theorem R174311 : Reach 174311 := rs (se 1 (by rfl) ⟨130733, by rfl⟩) R261467
theorem R76103 : Reach 76103 := rs (se 1 (by rfl) ⟨57077, by rfl⟩) R114155
theorem R76135 : Reach 76135 := rs (se 1 (by rfl) ⟨57101, by rfl⟩) R114203
theorem R895423 : Reach 895423 := rs (se 1 (by rfl) ⟨671567, by rfl⟩) R1343135
theorem R76415 : Reach 76415 := rs (se 1 (by rfl) ⟨57311, by rfl⟩) R114623
theorem R305801 : Reach 305801 := rs (se 2 (by rfl) ⟨114675, by rfl⟩) R229351
theorem R76671 : Reach 76671 := rs (se 1 (by rfl) ⟨57503, by rfl⟩) R115007
theorem R76891 : Reach 76891 := rs (se 1 (by rfl) ⟨57668, by rfl⟩) R115337
theorem R76927 : Reach 76927 := rs (se 1 (by rfl) ⟨57695, by rfl⟩) R115391
theorem R76955 : Reach 76955 := rs (se 1 (by rfl) ⟨57716, by rfl⟩) R115433
theorem R77659 : Reach 77659 := rs (se 1 (by rfl) ⟨58244, by rfl⟩) R116489
theorem R77759 : Reach 77759 := rs (se 1 (by rfl) ⟨58319, by rfl⟩) R116639
theorem R77823 : Reach 77823 := rs (se 1 (by rfl) ⟨58367, by rfl⟩) R116735
theorem R78271 : Reach 78271 := rs (se 1 (by rfl) ⟨58703, by rfl⟩) R117407
theorem R78427 : Reach 78427 := rs (se 1 (by rfl) ⟨58820, by rfl⟩) R117641
theorem R78491 : Reach 78491 := rs (se 1 (by rfl) ⟨58868, by rfl⟩) R117737
theorem R78591 : Reach 78591 := rs (se 1 (by rfl) ⟨58943, by rfl⟩) R117887
theorem R78895 : Reach 78895 := rs (se 1 (by rfl) ⟨59171, by rfl⟩) R118343
theorem R79007 : Reach 79007 := rs (se 1 (by rfl) ⟨59255, by rfl⟩) R118511
theorem R79039 : Reach 79039 := rs (se 1 (by rfl) ⟨59279, by rfl⟩) R118559
theorem R374327 : Reach 374327 := rs (se 1 (by rfl) ⟨280745, by rfl⟩) R561491
theorem R1325321 : Reach 1325321 := rs (se 2 (by rfl) ⟨496995, by rfl⟩) R993991
theorem R113435 : Reach 113435 := rs (se 1 (by rfl) ⟨85076, by rfl⟩) R170153
theorem R1981421 : Reach 1981421 := rs (se 3 (by rfl) ⟨371516, by rfl⟩) R743033
theorem R113657 : Reach 113657 := rs (se 2 (by rfl) ⟨42621, by rfl⟩) R85243
theorem R114431 : Reach 114431 := rs (se 1 (by rfl) ⟨85823, by rfl⟩) R171647
theorem R114719 : Reach 114719 := rs (se 1 (by rfl) ⟨86039, by rfl⟩) R172079
theorem R114743 : Reach 114743 := rs (se 1 (by rfl) ⟨86057, by rfl⟩) R172115
theorem R147577 : Reach 147577 := rs (se 2 (by rfl) ⟨55341, by rfl⟩) R110683
theorem R149339 : Reach 149339 := rs (se 1 (by rfl) ⟨112004, by rfl⟩) R224009
theorem R380015 : Reach 380015 := rs (se 1 (by rfl) ⟨285011, by rfl⟩) R570023
theorem R445601 : Reach 445601 := rs (se 2 (by rfl) ⟨167100, by rfl⟩) R334201
theorem R118079 : Reach 118079 := rs (se 1 (by rfl) ⟨88559, by rfl⟩) R177119
theorem R118175 : Reach 118175 := rs (se 1 (by rfl) ⟨88631, by rfl⟩) R177263
theorem R118427 : Reach 118427 := rs (se 1 (by rfl) ⟨88820, by rfl⟩) R177641
theorem R380641 : Reach 380641 := rs (se 2 (by rfl) ⟨142740, by rfl⟩) R285481
theorem R577367 : Reach 577367 := rs (se 1 (by rfl) ⟨433025, by rfl⟩) R866051
theorem R1200545 : Reach 1200545 := rs (se 2 (by rfl) ⟨450204, by rfl⟩) R900409
theorem R119279 : Reach 119279 := rs (se 1 (by rfl) ⟨89459, by rfl⟩) R178919
theorem R447059 : Reach 447059 := rs (se 1 (by rfl) ⟨335294, by rfl⟩) R670589
theorem R447515 : Reach 447515 := rs (se 1 (by rfl) ⟨335636, by rfl⟩) R671273
theorem R8968067 : Reach 8968067 := rs (se 1 (by rfl) ⟨6726050, by rfl⟩) R13452101
theorem R1956511 : Reach 1956511 := rs (se 1 (by rfl) ⟨1467383, by rfl⟩) R2934767
theorem R777701 : Reach 777701 := rs (se 4 (by rfl) ⟨72909, by rfl⟩) R145819
theorem R4874003 : Reach 4874003 := rs (se 1 (by rfl) ⟨3655502, by rfl⟩) R7311005
theorem R450431 : Reach 450431 := rs (se 1 (by rfl) ⟨337823, by rfl⟩) R675647
theorem R287347 : Reach 287347 := rs (se 1 (by rfl) ⟨215510, by rfl⟩) R431021
theorem R386045 : Reach 386045 := rs (se 3 (by rfl) ⟨72383, by rfl⟩) R144767
theorem R877715 : Reach 877715 := rs (se 1 (by rfl) ⟨658286, by rfl⟩) R1316573
theorem R976799 : Reach 976799 := rs (se 1 (by rfl) ⟨732599, by rfl⟩) R1465199
theorem R649403 : Reach 649403 := rs (se 1 (by rfl) ⟨487052, by rfl⟩) R974105
theorem R191119 : Reach 191119 := rs (se 1 (by rfl) ⟨143339, by rfl⟩) R286679
theorem R127487 : Reach 127487 := rs (se 1 (by rfl) ⟨95615, by rfl⟩) R191231
theorem R94927 : Reach 94927 := rs (se 1 (by rfl) ⟨71195, by rfl⟩) R142391
theorem R980869 : Reach 980869 := rs (se 4 (by rfl) ⟨91956, by rfl⟩) R183913
theorem R129127 : Reach 129127 := rs (se 1 (by rfl) ⟨96845, by rfl⟩) R193691
theorem R195311 : Reach 195311 := rs (se 1 (by rfl) ⟨146483, by rfl⟩) R292967
theorem R130025 : Reach 130025 := rs (se 2 (by rfl) ⟨48759, by rfl⟩) R97519
theorem R261359 : Reach 261359 := rs (se 1 (by rfl) ⟨196019, by rfl⟩) R392039
theorem R163129 : Reach 163129 := rs (se 2 (by rfl) ⟨61173, by rfl⟩) R122347
theorem R163547 : Reach 163547 := rs (se 1 (by rfl) ⟨122660, by rfl⟩) R245321
theorem R294623 : Reach 294623 := rs (se 1 (by rfl) ⟨220967, by rfl⟩) R441935
theorem R196769 : Reach 196769 := rs (se 2 (by rfl) ⟨73788, by rfl⟩) R147577
theorem R131753 : Reach 131753 := rs (se 2 (by rfl) ⟨49407, by rfl⟩) R98815
theorem R492257 : Reach 492257 := rs (se 2 (by rfl) ⟨184596, by rfl⟩) R369193
theorem R99559 : Reach 99559 := rs (se 1 (by rfl) ⟨74669, by rfl⟩) R149339
theorem R198247 : Reach 198247 := rs (se 1 (by rfl) ⟨148685, by rfl⟩) R297371
theorem R297067 : Reach 297067 := rs (se 1 (by rfl) ⟨222800, by rfl⟩) R445601
theorem R298039 : Reach 298039 := rs (se 1 (by rfl) ⟨223529, by rfl⟩) R447059
theorem R658529 : Reach 658529 := rs (se 2 (by rfl) ⟨246948, by rfl⟩) R493897
theorem R298343 : Reach 298343 := rs (se 1 (by rfl) ⟨223757, by rfl⟩) R447515
theorem R396737 : Reach 396737 := rs (se 2 (by rfl) ⟨148776, by rfl⟩) R297553
theorem R1576421 : Reach 1576421 := rs (se 4 (by rfl) ⟨147789, by rfl⟩) R295579
theorem R397547 : Reach 397547 := rs (se 1 (by rfl) ⟨298160, by rfl⟩) R596321
theorem R3249335 : Reach 3249335 := rs (se 1 (by rfl) ⟨2437001, by rfl⟩) R4874003
theorem R300287 : Reach 300287 := rs (se 1 (by rfl) ⟨225215, by rfl⟩) R450431
theorem R432935 : Reach 432935 := rs (se 1 (by rfl) ⟨324701, by rfl⟩) R649403
theorem R203867 : Reach 203867 := rs (se 1 (by rfl) ⟨152900, by rfl⟩) R305801
theorem R172169 : Reach 172169 := rs (se 2 (by rfl) ⟨64563, by rfl⟩) R129127
theorem R75623 : Reach 75623 := rs (se 1 (by rfl) ⟨56717, by rfl⟩) R113435
theorem R1320947 : Reach 1320947 := rs (se 1 (by rfl) ⟨990710, by rfl⟩) R1981421
theorem R75771 : Reach 75771 := rs (se 1 (by rfl) ⟨56828, by rfl⟩) R113657
theorem R174239 : Reach 174239 := rs (se 1 (by rfl) ⟨130679, by rfl⟩) R261359
theorem R109031 : Reach 109031 := rs (se 1 (by rfl) ⟨81773, by rfl⟩) R163547
theorem R76287 : Reach 76287 := rs (se 1 (by rfl) ⟨57215, by rfl⟩) R114431
theorem R76479 : Reach 76479 := rs (se 1 (by rfl) ⟨57359, by rfl⟩) R114719
theorem R76495 : Reach 76495 := rs (se 1 (by rfl) ⟨57371, by rfl⟩) R114743
theorem R175787 : Reach 175787 := rs (se 1 (by rfl) ⟨131840, by rfl⟩) R263681
theorem R438311 : Reach 438311 := rs (se 1 (by rfl) ⟨328733, by rfl⟩) R657467
theorem R78719 : Reach 78719 := rs (se 1 (by rfl) ⟨59039, by rfl⟩) R118079
theorem R78783 : Reach 78783 := rs (se 1 (by rfl) ⟨59087, by rfl⟩) R118175
theorem R78951 : Reach 78951 := rs (se 1 (by rfl) ⟨59213, by rfl⟩) R118427
theorem R243167 : Reach 243167 := rs (se 1 (by rfl) ⟨182375, by rfl⟩) R364751
theorem R177695 : Reach 177695 := rs (se 1 (by rfl) ⟨133271, by rfl⟩) R266543
theorem R800363 : Reach 800363 := rs (se 1 (by rfl) ⟨600272, by rfl⟩) R1200545
theorem R1193897 : Reach 1193897 := rs (se 2 (by rfl) ⟨447711, by rfl⟩) R895423
theorem R112751 : Reach 112751 := rs (se 1 (by rfl) ⟨84563, by rfl⟩) R169127
theorem R5978711 : Reach 5978711 := rs (se 1 (by rfl) ⟨4484033, by rfl⟩) R8968067
theorem R572507 : Reach 572507 := rs (se 1 (by rfl) ⟨429380, by rfl⟩) R858761
theorem R507179 : Reach 507179 := rs (se 1 (by rfl) ⟨380384, by rfl⟩) R760769
theorem R113975 : Reach 113975 := rs (se 1 (by rfl) ⟨85481, by rfl⟩) R170963
theorem R507521 : Reach 507521 := rs (se 2 (by rfl) ⟨190320, by rfl⟩) R380641
theorem R179903 : Reach 179903 := rs (se 1 (by rfl) ⟨134927, by rfl⟩) R269855
theorem R114911 : Reach 114911 := rs (se 1 (by rfl) ⟨86183, by rfl⟩) R172367
theorem R115103 : Reach 115103 := rs (se 1 (by rfl) ⟨86327, by rfl⟩) R172655
theorem R115487 : Reach 115487 := rs (se 1 (by rfl) ⟨86615, by rfl⟩) R173231
theorem R116207 : Reach 116207 := rs (se 1 (by rfl) ⟨87155, by rfl⟩) R174311
theorem R1230461 : Reach 1230461 := rs (se 3 (by rfl) ⟨230711, by rfl⟩) R461423
theorem R84991 : Reach 84991 := rs (se 1 (by rfl) ⟨63743, by rfl⟩) R127487
theorem R2608681 : Reach 2608681 := rs (se 2 (by rfl) ⟨978255, by rfl⟩) R1956511
theorem R249551 : Reach 249551 := rs (se 1 (by rfl) ⟨187163, by rfl⟩) R374327
theorem R217505 : Reach 217505 := rs (se 2 (by rfl) ⟨81564, by rfl⟩) R163129
theorem R86683 : Reach 86683 := rs (se 1 (by rfl) ⟨65012, by rfl⟩) R130025
theorem R23615621 : Reach 23615621 := rs (se 4 (by rfl) ⟨2213964, by rfl⟩) R4427929
theorem R383129 : Reach 383129 := rs (se 2 (by rfl) ⟨143673, by rfl⟩) R287347
theorem R318077 : Reach 318077 := rs (se 3 (by rfl) ⟨59639, by rfl⟩) R119279
theorem R88807 : Reach 88807 := rs (se 1 (by rfl) ⟨66605, by rfl⟩) R133211
theorem R253343 : Reach 253343 := rs (se 1 (by rfl) ⟨190007, by rfl⟩) R380015
theorem R384911 : Reach 384911 := rs (se 1 (by rfl) ⟨288683, by rfl⟩) R577367
theorem R221753 : Reach 221753 := rs (se 2 (by rfl) ⟨83157, by rfl⟩) R166315
theorem R254825 : Reach 254825 := rs (se 2 (by rfl) ⟨95559, by rfl⟩) R191119
theorem R2844953 : Reach 2844953 := rs (se 2 (by rfl) ⟨1066857, by rfl⟩) R2133715
theorem R518467 : Reach 518467 := rs (se 1 (by rfl) ⟨388850, by rfl⟩) R777701
theorem R257363 : Reach 257363 := rs (se 1 (by rfl) ⟨193022, by rfl⟩) R386045
theorem R585143 : Reach 585143 := rs (se 1 (by rfl) ⟨438857, by rfl⟩) R877715
theorem R749033 : Reach 749033 := rs (se 2 (by rfl) ⟨280887, by rfl⟩) R561775
theorem R126569 : Reach 126569 := rs (se 2 (by rfl) ⟨47463, by rfl⟩) R94927
theorem R651199 : Reach 651199 := rs (se 1 (by rfl) ⟨488399, by rfl⟩) R976799
theorem R225335 : Reach 225335 := rs (se 1 (by rfl) ⟨169001, by rfl⟩) R338003
theorem R1307825 : Reach 1307825 := rs (se 2 (by rfl) ⟨490434, by rfl⟩) R980869
theorem R883547 : Reach 883547 := rs (se 1 (by rfl) ⟨662660, by rfl⟩) R1325321
theorem R130207 : Reach 130207 := rs (se 1 (by rfl) ⟨97655, by rfl⟩) R195311
theorem R196415 : Reach 196415 := rs (se 1 (by rfl) ⟨147311, by rfl⟩) R294623
theorem R131179 : Reach 131179 := rs (se 1 (by rfl) ⟨98384, by rfl⟩) R196769
theorem R328171 : Reach 328171 := rs (se 1 (by rfl) ⟨246128, by rfl⟩) R492257
theorem R820307 : Reach 820307 := rs (se 1 (by rfl) ⟨615230, by rfl⟩) R1230461
theorem R132745 : Reach 132745 := rs (se 2 (by rfl) ⟨49779, by rfl⟩) R99559
theorem R264329 : Reach 264329 := rs (se 2 (by rfl) ⟨99123, by rfl⟩) R198247
theorem R198895 : Reach 198895 := rs (se 1 (by rfl) ⟨149171, by rfl⟩) R298343
theorem R264491 : Reach 264491 := rs (se 1 (by rfl) ⟨198368, by rfl⟩) R396737
theorem R1050947 : Reach 1050947 := rs (se 1 (by rfl) ⟨788210, by rfl⟩) R1576421
theorem R166367 : Reach 166367 := rs (se 1 (by rfl) ⟨124775, by rfl⟩) R249551
theorem R396089 : Reach 396089 := rs (se 2 (by rfl) ⟨148533, by rfl⟩) R297067
theorem R265031 : Reach 265031 := rs (se 1 (by rfl) ⟨198773, by rfl⟩) R397547
theorem R691289 : Reach 691289 := rs (se 2 (by rfl) ⟨259233, by rfl⟩) R518467
theorem R2166223 : Reach 2166223 := rs (se 1 (by rfl) ⟨1624667, by rfl⟩) R3249335
theorem R200191 : Reach 200191 := rs (se 1 (by rfl) ⟨150143, by rfl⟩) R300287
theorem R397385 : Reach 397385 := rs (se 2 (by rfl) ⟨149019, by rfl⟩) R298039
theorem R3478241 : Reach 3478241 := rs (se 2 (by rfl) ⟨1304340, by rfl⟩) R2608681
theorem R135911 : Reach 135911 := rs (se 1 (by rfl) ⟨101933, by rfl⟩) R203867
theorem R168895 : Reach 168895 := rs (se 1 (by rfl) ⟨126671, by rfl⟩) R253343
theorem R3183725 : Reach 3183725 := rs (se 3 (by rfl) ⟨596948, by rfl⟩) R1193897
theorem R169883 : Reach 169883 := rs (se 1 (by rfl) ⟨127412, by rfl⟩) R254825
theorem R171575 : Reach 171575 := rs (se 1 (by rfl) ⟨128681, by rfl⟩) R257363
theorem R499355 : Reach 499355 := rs (se 1 (by rfl) ⟨374516, by rfl⟩) R749033
theorem R1352477 : Reach 1352477 := rs (se 3 (by rfl) ⟨253589, by rfl⟩) R507179
theorem R533575 : Reach 533575 := rs (se 1 (by rfl) ⟨400181, by rfl⟩) R800363
theorem R75167 : Reach 75167 := rs (se 1 (by rfl) ⟨56375, by rfl⟩) R112751
theorem R173609 : Reach 173609 := rs (se 2 (by rfl) ⟨65103, by rfl⟩) R130207
theorem R337517 : Reach 337517 := rs (se 3 (by rfl) ⟨63284, by rfl⟩) R126569
theorem R75983 : Reach 75983 := rs (se 1 (by rfl) ⟨56987, by rfl⟩) R113975
theorem R338347 : Reach 338347 := rs (se 1 (by rfl) ⟨253760, by rfl⟩) R507521
theorem R76607 : Reach 76607 := rs (se 1 (by rfl) ⟨57455, by rfl⟩) R114911
theorem R76735 : Reach 76735 := rs (se 1 (by rfl) ⟨57551, by rfl⟩) R115103
theorem R76991 : Reach 76991 := rs (se 1 (by rfl) ⟨57743, by rfl⟩) R115487
theorem R77471 : Reach 77471 := rs (se 1 (by rfl) ⟨58103, by rfl⟩) R116207
theorem R439019 : Reach 439019 := rs (se 1 (by rfl) ⟨329264, by rfl⟩) R658529
theorem R145003 : Reach 145003 := rs (se 1 (by rfl) ⟨108752, by rfl⟩) R217505
theorem R113321 : Reach 113321 := rs (se 2 (by rfl) ⟨42495, by rfl⟩) R84991
theorem R15743747 : Reach 15743747 := rs (se 1 (by rfl) ⟨11807810, by rfl⟩) R23615621
theorem R212051 : Reach 212051 := rs (se 1 (by rfl) ⟨159038, by rfl⟩) R318077
theorem R868265 : Reach 868265 := rs (se 2 (by rfl) ⟨325599, by rfl⟩) R651199
theorem R114779 : Reach 114779 := rs (se 1 (by rfl) ⟨86084, by rfl⟩) R172169
theorem R147835 : Reach 147835 := rs (se 1 (by rfl) ⟨110876, by rfl⟩) R221753
theorem R115577 : Reach 115577 := rs (se 2 (by rfl) ⟨43341, by rfl⟩) R86683
theorem R116159 : Reach 116159 := rs (se 1 (by rfl) ⟨87119, by rfl⟩) R174239
theorem R15943229 : Reach 15943229 := rs (se 3 (by rfl) ⟨2989355, by rfl⟩) R5978711
theorem R117191 : Reach 117191 := rs (se 1 (by rfl) ⟨87893, by rfl⟩) R175787
theorem R150223 : Reach 150223 := rs (se 1 (by rfl) ⟨112667, by rfl⟩) R225335
theorem R871883 : Reach 871883 := rs (se 1 (by rfl) ⟨653912, by rfl⟩) R1307825
theorem R118409 : Reach 118409 := rs (se 2 (by rfl) ⟨44403, by rfl⟩) R88807
theorem R118463 : Reach 118463 := rs (se 1 (by rfl) ⟨88847, by rfl⟩) R177695
theorem R381671 : Reach 381671 := rs (se 1 (by rfl) ⟨286253, by rfl⟩) R572507
theorem R119935 : Reach 119935 := rs (se 1 (by rfl) ⟨89951, by rfl⟩) R179903
theorem R87835 : Reach 87835 := rs (se 1 (by rfl) ⟨65876, by rfl⟩) R131753
theorem R648445 : Reach 648445 := rs (se 3 (by rfl) ⟨121583, by rfl⟩) R243167
theorem R255419 : Reach 255419 := rs (se 1 (by rfl) ⟨191564, by rfl⟩) R383129
theorem R288623 : Reach 288623 := rs (se 1 (by rfl) ⟨216467, by rfl⟩) R432935
theorem R256607 : Reach 256607 := rs (se 1 (by rfl) ⟨192455, by rfl⟩) R384911
theorem R290749 : Reach 290749 := rs (se 3 (by rfl) ⟨54515, by rfl⟩) R109031
theorem R880631 : Reach 880631 := rs (se 1 (by rfl) ⟨660473, by rfl⟩) R1320947
theorem R1896635 : Reach 1896635 := rs (se 1 (by rfl) ⟨1422476, by rfl⟩) R2844953
theorem R390095 : Reach 390095 := rs (se 1 (by rfl) ⟨292571, by rfl⟩) R585143
theorem R292207 : Reach 292207 := rs (se 1 (by rfl) ⟨219155, by rfl⟩) R438311
theorem R589031 : Reach 589031 := rs (se 1 (by rfl) ⟨441773, by rfl⟩) R883547
theorem R130943 : Reach 130943 := rs (se 1 (by rfl) ⟨98207, by rfl⟩) R196415
theorem R197113 : Reach 197113 := rs (se 2 (by rfl) ⟨73917, by rfl⟩) R147835
theorem R264059 : Reach 264059 := rs (se 1 (by rfl) ⟨198044, by rfl⟩) R396089
theorem R9275309 : Reach 9275309 := rs (se 3 (by rfl) ⟨1739120, by rfl⟩) R3478241
theorem R460859 : Reach 460859 := rs (se 1 (by rfl) ⟨345644, by rfl⟩) R691289
theorem R3606605 : Reach 3606605 := rs (se 3 (by rfl) ⟨676238, by rfl⟩) R1352477
theorem R1804517 : Reach 1804517 := rs (se 4 (by rfl) ⟨169173, by rfl⟩) R338347
theorem R264923 : Reach 264923 := rs (se 1 (by rfl) ⟨198692, by rfl⟩) R397385
theorem R265193 : Reach 265193 := rs (se 2 (by rfl) ⟨99447, by rfl⟩) R198895
theorem R200297 : Reach 200297 := rs (se 2 (by rfl) ⟨75111, by rfl⟩) R150223
theorem R2888297 : Reach 2888297 := rs (se 2 (by rfl) ⟨1083111, by rfl⟩) R2166223
theorem R266921 : Reach 266921 := rs (se 2 (by rfl) ⟨100095, by rfl⟩) R200191
theorem R332903 : Reach 332903 := rs (se 1 (by rfl) ⟨249677, by rfl⟩) R499355
theorem R170279 : Reach 170279 := rs (se 1 (by rfl) ⟨127709, by rfl⟩) R255419
theorem R171071 : Reach 171071 := rs (se 1 (by rfl) ⟨128303, by rfl⟩) R256607
theorem R75547 : Reach 75547 := rs (se 1 (by rfl) ⟨56660, by rfl⟩) R113321
theorem R10495831 : Reach 10495831 := rs (se 1 (by rfl) ⟨7871873, by rfl⟩) R15743747
theorem R141367 : Reach 141367 := rs (se 1 (by rfl) ⟨106025, by rfl⟩) R212051
theorem R76519 : Reach 76519 := rs (se 1 (by rfl) ⟨57389, by rfl⟩) R114779
theorem R174905 : Reach 174905 := rs (se 2 (by rfl) ⟨65589, by rfl⟩) R131179
theorem R77051 : Reach 77051 := rs (se 1 (by rfl) ⟨57788, by rfl⟩) R115577
theorem R437561 : Reach 437561 := rs (se 2 (by rfl) ⟨164085, by rfl⟩) R328171
theorem R77439 : Reach 77439 := rs (se 1 (by rfl) ⟨58079, by rfl⟩) R116159
theorem R10628819 : Reach 10628819 := rs (se 1 (by rfl) ⟨7971614, by rfl⟩) R15943229
theorem R176219 : Reach 176219 := rs (se 1 (by rfl) ⟨132164, by rfl⟩) R264329
theorem R176327 : Reach 176327 := rs (se 1 (by rfl) ⟨132245, by rfl⟩) R264491
theorem R700631 : Reach 700631 := rs (se 1 (by rfl) ⟨525473, by rfl⟩) R1050947
theorem R78127 : Reach 78127 := rs (se 1 (by rfl) ⟨58595, by rfl⟩) R117191
theorem R110911 : Reach 110911 := rs (se 1 (by rfl) ⟨83183, by rfl⟩) R166367
theorem R864593 : Reach 864593 := rs (se 2 (by rfl) ⟨324222, by rfl⟩) R648445
theorem R176687 : Reach 176687 := rs (se 1 (by rfl) ⟨132515, by rfl⟩) R265031
theorem R176993 : Reach 176993 := rs (se 2 (by rfl) ⟨66372, by rfl⟩) R132745
theorem R78939 : Reach 78939 := rs (se 1 (by rfl) ⟨59204, by rfl⟩) R118409
theorem R78975 : Reach 78975 := rs (se 1 (by rfl) ⟨59231, by rfl⟩) R118463
theorem R113255 : Reach 113255 := rs (se 1 (by rfl) ⟨84941, by rfl⟩) R169883
theorem R114383 : Reach 114383 := rs (se 1 (by rfl) ⟨85787, by rfl⟩) R171575
theorem R115739 : Reach 115739 := rs (se 1 (by rfl) ⟨86804, by rfl⟩) R173609
theorem R117113 : Reach 117113 := rs (se 2 (by rfl) ⟨43917, by rfl⟩) R87835
theorem R1264423 : Reach 1264423 := rs (se 1 (by rfl) ⟨948317, by rfl⟩) R1896635
theorem R87295 : Reach 87295 := rs (se 1 (by rfl) ⟨65471, by rfl⟩) R130943
theorem R578843 : Reach 578843 := rs (se 1 (by rfl) ⟨434132, by rfl⟩) R868265
theorem R546871 : Reach 546871 := rs (se 1 (by rfl) ⟨410153, by rfl⟩) R820307
theorem R711433 : Reach 711433 := rs (se 2 (by rfl) ⟨266787, by rfl⟩) R533575
theorem R581255 : Reach 581255 := rs (se 1 (by rfl) ⟨435941, by rfl⟩) R871883
theorem R254447 : Reach 254447 := rs (se 1 (by rfl) ⟨190835, by rfl⟩) R381671
theorem R90607 : Reach 90607 := rs (se 1 (by rfl) ⟨67955, by rfl⟩) R135911
theorem R2122483 : Reach 2122483 := rs (se 1 (by rfl) ⟨1591862, by rfl⟩) R3183725
theorem R387665 : Reach 387665 := rs (se 2 (by rfl) ⟨145374, by rfl⟩) R290749
theorem R225011 : Reach 225011 := rs (se 1 (by rfl) ⟨168758, by rfl⟩) R337517
theorem R192415 : Reach 192415 := rs (se 1 (by rfl) ⟨144311, by rfl⟩) R288623
theorem R225193 : Reach 225193 := rs (se 2 (by rfl) ⟨84447, by rfl⟩) R168895
theorem R159913 : Reach 159913 := rs (se 2 (by rfl) ⟨59967, by rfl⟩) R119935
theorem R389609 : Reach 389609 := rs (se 2 (by rfl) ⟨146103, by rfl⟩) R292207
theorem R193337 : Reach 193337 := rs (se 2 (by rfl) ⟨72501, by rfl⟩) R145003
theorem R587087 : Reach 587087 := rs (se 1 (by rfl) ⟨440315, by rfl⟩) R880631
theorem R292679 : Reach 292679 := rs (se 1 (by rfl) ⟨219509, by rfl⟩) R439019
theorem R260063 : Reach 260063 := rs (se 1 (by rfl) ⟨195047, by rfl⟩) R390095
theorem R392687 : Reach 392687 := rs (se 1 (by rfl) ⟨294515, by rfl⟩) R589031
theorem R4915829 : Reach 4915829 := rs (se 5 (by rfl) ⟨230429, by rfl⟩) R460859
theorem R262817 : Reach 262817 := rs (se 2 (by rfl) ⟨98556, by rfl⟩) R197113
theorem R852869 : Reach 852869 := rs (se 4 (by rfl) ⟨79956, by rfl⟩) R159913
theorem R133531 : Reach 133531 := rs (se 1 (by rfl) ⟨100148, by rfl⟩) R200297
theorem R13994441 : Reach 13994441 := rs (se 2 (by rfl) ⟨5247915, by rfl⟩) R10495831
theorem R300257 : Reach 300257 := rs (se 2 (by rfl) ⟨112596, by rfl⟩) R225193
theorem R169631 : Reach 169631 := rs (se 1 (by rfl) ⟨127223, by rfl⟩) R254447
theorem R7085879 : Reach 7085879 := rs (se 1 (by rfl) ⟨5314409, by rfl⟩) R10628819
theorem R729161 : Reach 729161 := rs (se 2 (by rfl) ⟨273435, by rfl⟩) R546871
theorem R467087 : Reach 467087 := rs (se 1 (by rfl) ⟨350315, by rfl⟩) R700631
theorem R173375 : Reach 173375 := rs (se 1 (by rfl) ⟨130031, by rfl⟩) R260063
theorem R75503 : Reach 75503 := rs (se 1 (by rfl) ⟨56627, by rfl⟩) R113255
theorem R76255 : Reach 76255 := rs (se 1 (by rfl) ⟨57191, by rfl⟩) R114383
theorem R77159 : Reach 77159 := rs (se 1 (by rfl) ⟨57869, by rfl⟩) R115739
theorem R2829977 : Reach 2829977 := rs (se 2 (by rfl) ⟨1061241, by rfl⟩) R2122483
theorem R176039 : Reach 176039 := rs (se 1 (by rfl) ⟨132029, by rfl⟩) R264059
theorem R2404403 : Reach 2404403 := rs (se 1 (by rfl) ⟨1803302, by rfl⟩) R3606605
theorem R78075 : Reach 78075 := rs (se 1 (by rfl) ⟨58556, by rfl⟩) R117113
theorem R176615 : Reach 176615 := rs (se 1 (by rfl) ⟨132461, by rfl⟩) R264923
theorem R176795 : Reach 176795 := rs (se 1 (by rfl) ⟨132596, by rfl⟩) R265193
theorem R177947 : Reach 177947 := rs (se 1 (by rfl) ⟨133460, by rfl⟩) R266921
theorem R1685897 : Reach 1685897 := rs (se 2 (by rfl) ⟨632211, by rfl⟩) R1264423
theorem R113519 : Reach 113519 := rs (se 1 (by rfl) ⟨85139, by rfl⟩) R170279
theorem R114047 : Reach 114047 := rs (se 1 (by rfl) ⟨85535, by rfl⟩) R171071
theorem R147881 : Reach 147881 := rs (se 2 (by rfl) ⟨55455, by rfl⟩) R110911
theorem R116393 : Reach 116393 := rs (se 2 (by rfl) ⟨43647, by rfl⟩) R87295
theorem R116603 : Reach 116603 := rs (se 1 (by rfl) ⟨87452, by rfl⟩) R174905
theorem R150007 : Reach 150007 := rs (se 1 (by rfl) ⟨112505, by rfl⟩) R225011
theorem R117479 : Reach 117479 := rs (se 1 (by rfl) ⟨88109, by rfl⟩) R176219
theorem R117551 : Reach 117551 := rs (se 1 (by rfl) ⟨88163, by rfl⟩) R176327
theorem R576395 : Reach 576395 := rs (se 1 (by rfl) ⟨432296, by rfl⟩) R864593
theorem R117791 : Reach 117791 := rs (se 1 (by rfl) ⟨88343, by rfl⟩) R176687
theorem R117995 : Reach 117995 := rs (se 1 (by rfl) ⟨88496, by rfl⟩) R176993
theorem R120809 : Reach 120809 := rs (se 2 (by rfl) ⟨45303, by rfl⟩) R90607
theorem R6183539 : Reach 6183539 := rs (se 1 (by rfl) ⟨4637654, by rfl⟩) R9275309
theorem R1203011 : Reach 1203011 := rs (se 1 (by rfl) ⟨902258, by rfl⟩) R1804517
theorem R188489 : Reach 188489 := rs (se 2 (by rfl) ⟨70683, by rfl⟩) R141367
theorem R1925531 : Reach 1925531 := rs (se 1 (by rfl) ⟨1444148, by rfl⟩) R2888297
theorem R221935 : Reach 221935 := rs (se 1 (by rfl) ⟨166451, by rfl⟩) R332903
theorem R385895 : Reach 385895 := rs (se 1 (by rfl) ⟨289421, by rfl⟩) R578843
theorem R3794309 : Reach 3794309 := rs (se 4 (by rfl) ⟨355716, by rfl⟩) R711433
theorem R387503 : Reach 387503 := rs (se 1 (by rfl) ⟨290627, by rfl⟩) R581255
theorem R256553 : Reach 256553 := rs (se 2 (by rfl) ⟨96207, by rfl⟩) R192415
theorem R258443 : Reach 258443 := rs (se 1 (by rfl) ⟨193832, by rfl⟩) R387665
theorem R291707 : Reach 291707 := rs (se 1 (by rfl) ⟨218780, by rfl⟩) R437561
theorem R259739 : Reach 259739 := rs (se 1 (by rfl) ⟨194804, by rfl⟩) R389609
theorem R128891 : Reach 128891 := rs (se 1 (by rfl) ⟨96668, by rfl⟩) R193337
theorem R391391 : Reach 391391 := rs (se 1 (by rfl) ⟨293543, by rfl⟩) R587087
theorem R195119 : Reach 195119 := rs (se 1 (by rfl) ⟨146339, by rfl⟩) R292679
theorem R261791 : Reach 261791 := rs (se 1 (by rfl) ⟨196343, by rfl⟩) R392687
theorem R98587 : Reach 98587 := rs (se 1 (by rfl) ⟨73940, by rfl⟩) R147881
theorem R1245565 : Reach 1245565 := rs (se 3 (by rfl) ⟨233543, by rfl⟩) R467087
theorem R3277219 : Reach 3277219 := rs (se 1 (by rfl) ⟨2457914, by rfl⟩) R4915829
theorem R295913 : Reach 295913 := rs (se 2 (by rfl) ⟨110967, by rfl⟩) R221935
theorem R200009 : Reach 200009 := rs (se 2 (by rfl) ⟨75003, by rfl⟩) R150007
theorem R200171 : Reach 200171 := rs (se 1 (by rfl) ⟨150128, by rfl⟩) R300257
theorem R4723919 : Reach 4723919 := rs (se 1 (by rfl) ⟨3542939, by rfl⟩) R7085879
theorem R1283687 : Reach 1283687 := rs (se 1 (by rfl) ⟨962765, by rfl⟩) R1925531
theorem R2529539 : Reach 2529539 := rs (se 1 (by rfl) ⟨1897154, by rfl⟩) R3794309
theorem R171035 : Reach 171035 := rs (se 1 (by rfl) ⟨128276, by rfl⟩) R256553
theorem R172295 : Reach 172295 := rs (se 1 (by rfl) ⟨129221, by rfl⟩) R258443
theorem R173159 : Reach 173159 := rs (se 1 (by rfl) ⟨129869, by rfl⟩) R259739
theorem R1123931 : Reach 1123931 := rs (se 1 (by rfl) ⟨842948, by rfl⟩) R1685897
theorem R75679 : Reach 75679 := rs (se 1 (by rfl) ⟨56759, by rfl⟩) R113519
theorem R76031 : Reach 76031 := rs (se 1 (by rfl) ⟨57023, by rfl⟩) R114047
theorem R174527 : Reach 174527 := rs (se 1 (by rfl) ⟨130895, by rfl⟩) R261791
theorem R175211 : Reach 175211 := rs (se 1 (by rfl) ⟨131408, by rfl⟩) R262817
theorem R568579 : Reach 568579 := rs (se 1 (by rfl) ⟨426434, by rfl⟩) R852869
theorem R77595 : Reach 77595 := rs (se 1 (by rfl) ⟨58196, by rfl⟩) R116393
theorem R77735 : Reach 77735 := rs (se 1 (by rfl) ⟨58301, by rfl⟩) R116603
theorem R78319 : Reach 78319 := rs (se 1 (by rfl) ⟨58739, by rfl⟩) R117479
theorem R78367 : Reach 78367 := rs (se 1 (by rfl) ⟨58775, by rfl⟩) R117551
theorem R78527 : Reach 78527 := rs (se 1 (by rfl) ⟨58895, by rfl⟩) R117791
theorem R78663 : Reach 78663 := rs (se 1 (by rfl) ⟨58997, by rfl⟩) R117995
theorem R113087 : Reach 113087 := rs (se 1 (by rfl) ⟨84815, by rfl⟩) R169631
theorem R802007 : Reach 802007 := rs (se 1 (by rfl) ⟨601505, by rfl⟩) R1203011
theorem R115583 : Reach 115583 := rs (se 1 (by rfl) ⟨86687, by rfl⟩) R173375
theorem R1886651 : Reach 1886651 := rs (se 1 (by rfl) ⟨1414988, by rfl⟩) R2829977
theorem R117359 : Reach 117359 := rs (se 1 (by rfl) ⟨88019, by rfl⟩) R176039
theorem R117743 : Reach 117743 := rs (se 1 (by rfl) ⟨88307, by rfl⟩) R176615
theorem R117863 : Reach 117863 := rs (se 1 (by rfl) ⟨88397, by rfl⟩) R176795
theorem R118631 : Reach 118631 := rs (se 1 (by rfl) ⟨88973, by rfl⟩) R177947
theorem R85927 : Reach 85927 := rs (se 1 (by rfl) ⟨64445, by rfl⟩) R128891
theorem R9329627 : Reach 9329627 := rs (se 1 (by rfl) ⟨6997220, by rfl⟩) R13994441
theorem R384263 : Reach 384263 := rs (se 1 (by rfl) ⟨288197, by rfl⟩) R576395
theorem R712165 : Reach 712165 := rs (se 4 (by rfl) ⟨66765, by rfl⟩) R133531
theorem R4122359 : Reach 4122359 := rs (se 1 (by rfl) ⟨3091769, by rfl⟩) R6183539
theorem R322157 : Reach 322157 := rs (se 3 (by rfl) ⟨60404, by rfl⟩) R120809
theorem R486107 : Reach 486107 := rs (se 1 (by rfl) ⟨364580, by rfl⟩) R729161
theorem R125659 : Reach 125659 := rs (se 1 (by rfl) ⟨94244, by rfl⟩) R188489
theorem R257263 : Reach 257263 := rs (se 1 (by rfl) ⟨192947, by rfl⟩) R385895
theorem R258335 : Reach 258335 := rs (se 1 (by rfl) ⟨193751, by rfl⟩) R387503
theorem R1602935 : Reach 1602935 := rs (se 1 (by rfl) ⟨1202201, by rfl⟩) R2404403
theorem R194471 : Reach 194471 := rs (se 1 (by rfl) ⟨145853, by rfl⟩) R291707
theorem R260927 : Reach 260927 := rs (se 1 (by rfl) ⟨195695, by rfl⟩) R391391
theorem R130079 : Reach 130079 := rs (se 1 (by rfl) ⟨97559, by rfl⟩) R195119
theorem R131449 : Reach 131449 := rs (se 2 (by rfl) ⟨49293, by rfl⟩) R98587
theorem R197275 : Reach 197275 := rs (se 1 (by rfl) ⟨147956, by rfl⟩) R295913
theorem R133339 : Reach 133339 := rs (se 1 (by rfl) ⟨100004, by rfl⟩) R200009
theorem R133447 : Reach 133447 := rs (se 1 (by rfl) ⟨100085, by rfl⟩) R200171
theorem R3149279 : Reach 3149279 := rs (se 1 (by rfl) ⟨2361959, by rfl⟩) R4723919
theorem R167545 : Reach 167545 := rs (se 2 (by rfl) ⟨62829, by rfl⟩) R125659
theorem R855791 : Reach 855791 := rs (se 1 (by rfl) ⟨641843, by rfl⟩) R1283687
theorem R758105 : Reach 758105 := rs (se 2 (by rfl) ⟨284289, by rfl⟩) R568579
theorem R104425 : Reach 104425 := rs (se 2 (by rfl) ⟨39159, by rfl⟩) R78319
theorem R24879005 : Reach 24879005 := rs (se 3 (by rfl) ⟨4664813, by rfl⟩) R9329627
theorem R172223 : Reach 172223 := rs (se 1 (by rfl) ⟨129167, by rfl⟩) R258335
theorem R75391 : Reach 75391 := rs (se 1 (by rfl) ⟨56543, by rfl⟩) R113087
theorem R173951 : Reach 173951 := rs (se 1 (by rfl) ⟨130463, by rfl⟩) R260927
theorem R534671 : Reach 534671 := rs (se 1 (by rfl) ⟨401003, by rfl⟩) R802007
theorem R4369625 : Reach 4369625 := rs (se 2 (by rfl) ⟨1638609, by rfl⟩) R3277219
theorem R77055 : Reach 77055 := rs (se 1 (by rfl) ⟨57791, by rfl⟩) R115583
theorem R1257767 : Reach 1257767 := rs (se 1 (by rfl) ⟨943325, by rfl⟩) R1886651
theorem R78239 : Reach 78239 := rs (se 1 (by rfl) ⟨58679, by rfl⟩) R117359
theorem R78495 : Reach 78495 := rs (se 1 (by rfl) ⟨58871, by rfl⟩) R117743
theorem R78575 : Reach 78575 := rs (se 1 (by rfl) ⟨58931, by rfl⟩) R117863
theorem R79087 : Reach 79087 := rs (se 1 (by rfl) ⟨59315, by rfl⟩) R118631
theorem R1686359 : Reach 1686359 := rs (se 1 (by rfl) ⟨1264769, by rfl⟩) R2529539
theorem R114023 : Reach 114023 := rs (se 1 (by rfl) ⟨85517, by rfl⟩) R171035
theorem R114569 : Reach 114569 := rs (se 2 (by rfl) ⟨42963, by rfl⟩) R85927
theorem R114863 : Reach 114863 := rs (se 1 (by rfl) ⟨86147, by rfl⟩) R172295
theorem R115439 : Reach 115439 := rs (se 1 (by rfl) ⟨86579, by rfl⟩) R173159
theorem R116351 : Reach 116351 := rs (se 1 (by rfl) ⟨87263, by rfl⟩) R174527
theorem R214771 : Reach 214771 := rs (se 1 (by rfl) ⟨161078, by rfl⟩) R322157
theorem R116807 : Reach 116807 := rs (se 1 (by rfl) ⟨87605, by rfl⟩) R175211
theorem R1068623 : Reach 1068623 := rs (se 1 (by rfl) ⟨801467, by rfl⟩) R1602935
theorem R86719 : Reach 86719 := rs (se 1 (by rfl) ⟨65039, by rfl⟩) R130079
theorem R1660753 : Reach 1660753 := rs (se 2 (by rfl) ⟨622782, by rfl⟩) R1245565
theorem R256175 : Reach 256175 := rs (se 1 (by rfl) ⟨192131, by rfl⟩) R384263
theorem R749287 : Reach 749287 := rs (se 1 (by rfl) ⟨561965, by rfl⟩) R1123931
theorem R2748239 : Reach 2748239 := rs (se 1 (by rfl) ⟨2061179, by rfl⟩) R4122359
theorem R1372069 : Reach 1372069 := rs (se 4 (by rfl) ⟨128631, by rfl⟩) R257263
theorem R324071 : Reach 324071 := rs (se 1 (by rfl) ⟨243053, by rfl⟩) R486107
theorem R129647 : Reach 129647 := rs (se 1 (by rfl) ⟨97235, by rfl⟩) R194471
theorem R949553 : Reach 949553 := rs (se 2 (by rfl) ⟨356082, by rfl⟩) R712165
theorem R263033 : Reach 263033 := rs (se 2 (by rfl) ⟨98637, by rfl⟩) R197275
theorem R2099519 : Reach 2099519 := rs (se 1 (by rfl) ⟨1574639, by rfl⟩) R3149279
theorem R16586003 : Reach 16586003 := rs (se 1 (by rfl) ⟨12439502, by rfl⟩) R24879005
theorem R170783 : Reach 170783 := rs (se 1 (by rfl) ⟨128087, by rfl⟩) R256175
theorem R1124239 : Reach 1124239 := rs (se 1 (by rfl) ⟨843179, by rfl⟩) R1686359
theorem R7317701 : Reach 7317701 := rs (se 4 (by rfl) ⟨686034, by rfl⟩) R1372069
theorem R633035 : Reach 633035 := rs (se 1 (by rfl) ⟨474776, by rfl⟩) R949553
theorem R76015 : Reach 76015 := rs (se 1 (by rfl) ⟨57011, by rfl⟩) R114023
theorem R76379 : Reach 76379 := rs (se 1 (by rfl) ⟨57284, by rfl⟩) R114569
theorem R76575 : Reach 76575 := rs (se 1 (by rfl) ⟨57431, by rfl⟩) R114863
theorem R76959 : Reach 76959 := rs (se 1 (by rfl) ⟨57719, by rfl⟩) R115439
theorem R175265 : Reach 175265 := rs (se 2 (by rfl) ⟨65724, by rfl⟩) R131449
theorem R77567 : Reach 77567 := rs (se 1 (by rfl) ⟨58175, by rfl⟩) R116351
theorem R77871 : Reach 77871 := rs (se 1 (by rfl) ⟨58403, by rfl⟩) R116807
theorem R570527 : Reach 570527 := rs (se 1 (by rfl) ⟨427895, by rfl⟩) R855791
theorem R505403 : Reach 505403 := rs (se 1 (by rfl) ⟨379052, by rfl⟩) R758105
theorem R177785 : Reach 177785 := rs (se 2 (by rfl) ⟨66669, by rfl⟩) R133339
theorem R177929 : Reach 177929 := rs (se 2 (by rfl) ⟨66723, by rfl⟩) R133447
theorem R999049 : Reach 999049 := rs (se 2 (by rfl) ⟨374643, by rfl⟩) R749287
theorem R114815 : Reach 114815 := rs (se 1 (by rfl) ⟨86111, by rfl⟩) R172223
theorem R115625 : Reach 115625 := rs (se 2 (by rfl) ⟨43359, by rfl⟩) R86719
theorem R115967 : Reach 115967 := rs (se 1 (by rfl) ⟨86975, by rfl⟩) R173951
theorem R2214337 : Reach 2214337 := rs (se 2 (by rfl) ⟨830376, by rfl⟩) R1660753
theorem R838511 : Reach 838511 := rs (se 1 (by rfl) ⟨628883, by rfl⟩) R1257767
theorem R216047 : Reach 216047 := rs (se 1 (by rfl) ⟨162035, by rfl⟩) R324071
theorem R86431 : Reach 86431 := rs (se 1 (by rfl) ⟨64823, by rfl⟩) R129647
theorem R286361 : Reach 286361 := rs (se 2 (by rfl) ⟨107385, by rfl⟩) R214771
theorem R712415 : Reach 712415 := rs (se 1 (by rfl) ⟨534311, by rfl⟩) R1068623
theorem R223393 : Reach 223393 := rs (se 2 (by rfl) ⟨83772, by rfl⟩) R167545
theorem R356447 : Reach 356447 := rs (se 1 (by rfl) ⟨267335, by rfl⟩) R534671
theorem R2913083 : Reach 2913083 := rs (se 1 (by rfl) ⟨2184812, by rfl⟩) R4369625
theorem R1832159 : Reach 1832159 := rs (se 1 (by rfl) ⟨1374119, by rfl⟩) R2748239
theorem R2227733 : Reach 2227733 := rs (se 6 (by rfl) ⟨52212, by rfl⟩) R104425
theorem R950525 : Reach 950525 := rs (se 3 (by rfl) ⟨178223, by rfl⟩) R356447
theorem R559007 : Reach 559007 := rs (se 1 (by rfl) ⟨419255, by rfl⟩) R838511
theorem R297857 : Reach 297857 := rs (se 2 (by rfl) ⟨111696, by rfl⟩) R223393
theorem R2952449 : Reach 2952449 := rs (se 2 (by rfl) ⟨1107168, by rfl⟩) R2214337
theorem R1942055 : Reach 1942055 := rs (se 1 (by rfl) ⟨1456541, by rfl⟩) R2913083
theorem R1221439 : Reach 1221439 := rs (se 1 (by rfl) ⟨916079, by rfl⟩) R1832159
theorem R336935 : Reach 336935 := rs (se 1 (by rfl) ⟨252701, by rfl⟩) R505403
theorem R1485155 : Reach 1485155 := rs (se 1 (by rfl) ⟨1113866, by rfl⟩) R2227733
theorem R76543 : Reach 76543 := rs (se 1 (by rfl) ⟨57407, by rfl⟩) R114815
theorem R175355 : Reach 175355 := rs (se 1 (by rfl) ⟨131516, by rfl⟩) R263033
theorem R77083 : Reach 77083 := rs (se 1 (by rfl) ⟨57812, by rfl⟩) R115625
theorem R77311 : Reach 77311 := rs (se 1 (by rfl) ⟨57983, by rfl⟩) R115967
theorem R144031 : Reach 144031 := rs (se 1 (by rfl) ⟨108023, by rfl⟩) R216047
theorem R113855 : Reach 113855 := rs (se 1 (by rfl) ⟨85391, by rfl⟩) R170783
theorem R115241 : Reach 115241 := rs (se 2 (by rfl) ⟨43215, by rfl⟩) R86431
theorem R116843 : Reach 116843 := rs (se 1 (by rfl) ⟨87632, by rfl⟩) R175265
theorem R380351 : Reach 380351 := rs (se 1 (by rfl) ⟨285263, by rfl⟩) R570527
theorem R118523 : Reach 118523 := rs (se 1 (by rfl) ⟨88892, by rfl⟩) R177785
theorem R118619 : Reach 118619 := rs (se 1 (by rfl) ⟨88964, by rfl⟩) R177929
theorem R1332065 : Reach 1332065 := rs (se 2 (by rfl) ⟨499524, by rfl⟩) R999049
theorem R1399679 : Reach 1399679 := rs (se 1 (by rfl) ⟨1049759, by rfl⟩) R2099519
theorem R1498985 : Reach 1498985 := rs (se 2 (by rfl) ⟨562119, by rfl⟩) R1124239
theorem R44229341 : Reach 44229341 := rs (se 3 (by rfl) ⟨8293001, by rfl⟩) R16586003
theorem R190907 : Reach 190907 := rs (se 1 (by rfl) ⟨143180, by rfl⟩) R286361
theorem R4878467 : Reach 4878467 := rs (se 1 (by rfl) ⟨3658850, by rfl⟩) R7317701
theorem R422023 : Reach 422023 := rs (se 1 (by rfl) ⟨316517, by rfl⟩) R633035
theorem R1899773 : Reach 1899773 := rs (se 3 (by rfl) ⟨356207, by rfl⟩) R712415
theorem R198571 : Reach 198571 := rs (se 1 (by rfl) ⟨148928, by rfl⟩) R297857
theorem R1968299 : Reach 1968299 := rs (se 1 (by rfl) ⟨1476224, by rfl⟩) R2952449
theorem R888043 : Reach 888043 := rs (se 1 (by rfl) ⟨666032, by rfl⟩) R1332065
theorem R562697 : Reach 562697 := rs (se 2 (by rfl) ⟨211011, by rfl⟩) R422023
theorem R990103 : Reach 990103 := rs (se 1 (by rfl) ⟨742577, by rfl⟩) R1485155
theorem R3252311 : Reach 3252311 := rs (se 1 (by rfl) ⟨2439233, by rfl⟩) R4878467
theorem R75903 : Reach 75903 := rs (se 1 (by rfl) ⟨56927, by rfl⟩) R113855
theorem R633683 : Reach 633683 := rs (se 1 (by rfl) ⟨475262, by rfl⟩) R950525
theorem R76827 : Reach 76827 := rs (se 1 (by rfl) ⟨57620, by rfl⟩) R115241
theorem R372671 : Reach 372671 := rs (se 1 (by rfl) ⟨279503, by rfl⟩) R559007
theorem R77895 : Reach 77895 := rs (se 1 (by rfl) ⟨58421, by rfl⟩) R116843
theorem R79015 : Reach 79015 := rs (se 1 (by rfl) ⟨59261, by rfl⟩) R118523
theorem R79079 : Reach 79079 := rs (se 1 (by rfl) ⟨59309, by rfl⟩) R118619
theorem R933119 : Reach 933119 := rs (se 1 (by rfl) ⟨699839, by rfl⟩) R1399679
theorem R999323 : Reach 999323 := rs (se 1 (by rfl) ⟨749492, by rfl⟩) R1498985
theorem R1294703 : Reach 1294703 := rs (se 1 (by rfl) ⟨971027, by rfl⟩) R1942055
theorem R116903 : Reach 116903 := rs (se 1 (by rfl) ⟨87677, by rfl⟩) R175355
theorem R1266515 : Reach 1266515 := rs (se 1 (by rfl) ⟨949886, by rfl⟩) R1899773
theorem R1628585 : Reach 1628585 := rs (se 2 (by rfl) ⟨610719, by rfl⟩) R1221439
theorem R253567 : Reach 253567 := rs (se 1 (by rfl) ⟨190175, by rfl⟩) R380351
theorem R29486227 : Reach 29486227 := rs (se 1 (by rfl) ⟨22114670, by rfl⟩) R44229341
theorem R224623 : Reach 224623 := rs (se 1 (by rfl) ⟨168467, by rfl⟩) R336935
theorem R192041 : Reach 192041 := rs (se 2 (by rfl) ⟨72015, by rfl⟩) R144031
theorem R127271 : Reach 127271 := rs (se 1 (by rfl) ⟨95453, by rfl⟩) R190907
theorem R1312199 : Reach 1312199 := rs (se 1 (by rfl) ⟨984149, by rfl⟩) R1968299
theorem R264761 : Reach 264761 := rs (se 2 (by rfl) ⟨99285, by rfl⟩) R198571
theorem R1085723 : Reach 1085723 := rs (se 1 (by rfl) ⟨814292, by rfl⟩) R1628585
theorem R1184057 : Reach 1184057 := rs (se 2 (by rfl) ⟨444021, by rfl⟩) R888043
theorem R299497 : Reach 299497 := rs (se 2 (by rfl) ⟨112311, by rfl⟩) R224623
theorem R2168207 : Reach 2168207 := rs (se 1 (by rfl) ⟨1626155, by rfl⟩) R3252311
theorem R1320137 : Reach 1320137 := rs (se 2 (by rfl) ⟨495051, by rfl⟩) R990103
theorem R338089 : Reach 338089 := rs (se 2 (by rfl) ⟨126783, by rfl⟩) R253567
theorem R666215 : Reach 666215 := rs (se 1 (by rfl) ⟨499661, by rfl⟩) R999323
theorem R863135 : Reach 863135 := rs (se 1 (by rfl) ⟨647351, by rfl⟩) R1294703
theorem R77935 : Reach 77935 := rs (se 1 (by rfl) ⟨58451, by rfl⟩) R116903
theorem R375131 : Reach 375131 := rs (se 1 (by rfl) ⟨281348, by rfl⟩) R562697
theorem R1689821 : Reach 1689821 := rs (se 3 (by rfl) ⟨316841, by rfl⟩) R633683
theorem R248447 : Reach 248447 := rs (se 1 (by rfl) ⟨186335, by rfl⟩) R372671
theorem R84847 : Reach 84847 := rs (se 1 (by rfl) ⟨63635, by rfl⟩) R127271
theorem R844343 : Reach 844343 := rs (se 1 (by rfl) ⟨633257, by rfl⟩) R1266515
theorem R39314969 : Reach 39314969 := rs (se 2 (by rfl) ⟨14743113, by rfl⟩) R29486227
theorem R128027 : Reach 128027 := rs (se 1 (by rfl) ⟨96020, by rfl⟩) R192041
theorem R622079 : Reach 622079 := rs (se 1 (by rfl) ⟨466559, by rfl⟩) R933119
theorem R723815 : Reach 723815 := rs (se 1 (by rfl) ⟨542861, by rfl⟩) R1085723
theorem R789371 : Reach 789371 := rs (se 1 (by rfl) ⟨592028, by rfl⟩) R1184057
theorem R1445471 : Reach 1445471 := rs (se 1 (by rfl) ⟨1084103, by rfl⟩) R2168207
theorem R562895 : Reach 562895 := rs (se 1 (by rfl) ⟨422171, by rfl⟩) R844343
theorem R399329 : Reach 399329 := rs (se 2 (by rfl) ⟨149748, by rfl⟩) R299497
theorem R662525 : Reach 662525 := rs (se 3 (by rfl) ⟨124223, by rfl⟩) R248447
theorem R1126547 : Reach 1126547 := rs (se 1 (by rfl) ⟨844910, by rfl⟩) R1689821
theorem R176507 : Reach 176507 := rs (se 1 (by rfl) ⟨132380, by rfl⟩) R264761
theorem R113129 : Reach 113129 := rs (se 2 (by rfl) ⟨42423, by rfl⟩) R84847
theorem R1000349 : Reach 1000349 := rs (se 3 (by rfl) ⟨187565, by rfl⟩) R375131
theorem R444143 : Reach 444143 := rs (se 1 (by rfl) ⟨333107, by rfl⟩) R666215
theorem R575423 : Reach 575423 := rs (se 1 (by rfl) ⟨431567, by rfl⟩) R863135
theorem R85351 : Reach 85351 := rs (se 1 (by rfl) ⟨64013, by rfl⟩) R128027
theorem R414719 : Reach 414719 := rs (se 1 (by rfl) ⟨311039, by rfl⟩) R622079
theorem R874799 : Reach 874799 := rs (se 1 (by rfl) ⟨656099, by rfl⟩) R1312199
theorem R450785 : Reach 450785 := rs (se 2 (by rfl) ⟨169044, by rfl⟩) R338089
theorem R880091 : Reach 880091 := rs (se 1 (by rfl) ⟨660068, by rfl⟩) R1320137
theorem R26209979 : Reach 26209979 := rs (se 1 (by rfl) ⟨19657484, by rfl⟩) R39314969
theorem R296095 : Reach 296095 := rs (se 1 (by rfl) ⟨222071, by rfl⟩) R444143
theorem R526247 : Reach 526247 := rs (se 1 (by rfl) ⟨394685, by rfl⟩) R789371
theorem R266219 : Reach 266219 := rs (se 1 (by rfl) ⟨199664, by rfl⟩) R399329
theorem R300523 : Reach 300523 := rs (se 1 (by rfl) ⟨225392, by rfl⟩) R450785
theorem R17473319 : Reach 17473319 := rs (se 1 (by rfl) ⟨13104989, by rfl⟩) R26209979
theorem R75419 : Reach 75419 := rs (se 1 (by rfl) ⟨56564, by rfl⟩) R113129
theorem R666899 : Reach 666899 := rs (se 1 (by rfl) ⟨500174, by rfl⟩) R1000349
theorem R963647 : Reach 963647 := rs (se 1 (by rfl) ⟨722735, by rfl⟩) R1445471
theorem R276479 : Reach 276479 := rs (se 1 (by rfl) ⟨207359, by rfl⟩) R414719
theorem R375263 : Reach 375263 := rs (se 1 (by rfl) ⟨281447, by rfl⟩) R562895
theorem R113801 : Reach 113801 := rs (se 2 (by rfl) ⟨42675, by rfl⟩) R85351
theorem R441683 : Reach 441683 := rs (se 1 (by rfl) ⟨331262, by rfl⟩) R662525
theorem R117671 : Reach 117671 := rs (se 1 (by rfl) ⟨88253, by rfl⟩) R176507
theorem R383615 : Reach 383615 := rs (se 1 (by rfl) ⟨287711, by rfl⟩) R575423
theorem R482543 : Reach 482543 := rs (se 1 (by rfl) ⟨361907, by rfl⟩) R723815
theorem R583199 : Reach 583199 := rs (se 1 (by rfl) ⟨437399, by rfl⟩) R874799
theorem R586727 : Reach 586727 := rs (se 1 (by rfl) ⟨440045, by rfl⟩) R880091
theorem R751031 : Reach 751031 := rs (se 1 (by rfl) ⟨563273, by rfl⟩) R1126547
theorem R394793 : Reach 394793 := rs (se 2 (by rfl) ⟨148047, by rfl⟩) R296095
theorem R400697 : Reach 400697 := rs (se 2 (by rfl) ⟨150261, by rfl⟩) R300523
theorem R500687 : Reach 500687 := rs (se 1 (by rfl) ⟨375515, by rfl⟩) R751031
theorem R75867 : Reach 75867 := rs (se 1 (by rfl) ⟨56900, by rfl⟩) R113801
theorem R78447 : Reach 78447 := rs (se 1 (by rfl) ⟨58835, by rfl⟩) R117671
theorem R177479 : Reach 177479 := rs (se 1 (by rfl) ⟨133109, by rfl⟩) R266219
theorem R11648879 : Reach 11648879 := rs (se 1 (by rfl) ⟨8736659, by rfl⟩) R17473319
theorem R444599 : Reach 444599 := rs (se 1 (by rfl) ⟨333449, by rfl⟩) R666899
theorem R642431 : Reach 642431 := rs (se 1 (by rfl) ⟨481823, by rfl⟩) R963647
theorem R184319 : Reach 184319 := rs (se 1 (by rfl) ⟨138239, by rfl⟩) R276479
theorem R250175 : Reach 250175 := rs (se 1 (by rfl) ⟨187631, by rfl⟩) R375263
theorem R350831 : Reach 350831 := rs (se 1 (by rfl) ⟨263123, by rfl⟩) R526247
theorem R255743 : Reach 255743 := rs (se 1 (by rfl) ⟨191807, by rfl⟩) R383615
theorem R321695 : Reach 321695 := rs (se 1 (by rfl) ⟨241271, by rfl⟩) R482543
theorem R388799 : Reach 388799 := rs (se 1 (by rfl) ⟨291599, by rfl⟩) R583199
theorem R391151 : Reach 391151 := rs (se 1 (by rfl) ⟨293363, by rfl⟩) R586727
theorem R294455 : Reach 294455 := rs (se 1 (by rfl) ⟨220841, by rfl⟩) R441683
theorem R263195 : Reach 263195 := rs (se 1 (by rfl) ⟨197396, by rfl⟩) R394793
theorem R296399 : Reach 296399 := rs (se 1 (by rfl) ⟨222299, by rfl⟩) R444599
theorem R428287 : Reach 428287 := rs (se 1 (by rfl) ⟨321215, by rfl⟩) R642431
theorem R233887 : Reach 233887 := rs (se 1 (by rfl) ⟨175415, by rfl⟩) R350831
theorem R267131 : Reach 267131 := rs (se 1 (by rfl) ⟨200348, by rfl⟩) R400697
theorem R333791 : Reach 333791 := rs (se 1 (by rfl) ⟨250343, by rfl⟩) R500687
theorem R170495 : Reach 170495 := rs (se 1 (by rfl) ⟨127871, by rfl⟩) R255743
theorem R667133 : Reach 667133 := rs (se 3 (by rfl) ⟨125087, by rfl⟩) R250175
theorem R214463 : Reach 214463 := rs (se 1 (by rfl) ⟨160847, by rfl⟩) R321695
theorem R118319 : Reach 118319 := rs (se 1 (by rfl) ⟨88739, by rfl⟩) R177479
theorem R122879 : Reach 122879 := rs (se 1 (by rfl) ⟨92159, by rfl⟩) R184319
theorem R259199 : Reach 259199 := rs (se 1 (by rfl) ⟨194399, by rfl⟩) R388799
theorem R260767 : Reach 260767 := rs (se 1 (by rfl) ⟨195575, by rfl⟩) R391151
theorem R196303 : Reach 196303 := rs (se 1 (by rfl) ⟨147227, by rfl⟩) R294455
theorem R7765919 : Reach 7765919 := rs (se 1 (by rfl) ⟨5824439, by rfl⟩) R11648879
theorem R197599 : Reach 197599 := rs (se 1 (by rfl) ⟨148199, by rfl⟩) R296399
theorem R172799 : Reach 172799 := rs (se 1 (by rfl) ⟨129599, by rfl⟩) R259199
theorem R175463 : Reach 175463 := rs (se 1 (by rfl) ⟨131597, by rfl⟩) R263195
theorem R142975 : Reach 142975 := rs (se 1 (by rfl) ⟨107231, by rfl⟩) R214463
theorem R78879 : Reach 78879 := rs (se 1 (by rfl) ⟨59159, by rfl⟩) R118319
theorem R571049 : Reach 571049 := rs (se 2 (by rfl) ⟨214143, by rfl⟩) R428287
theorem R178087 : Reach 178087 := rs (se 1 (by rfl) ⟨133565, by rfl⟩) R267131
theorem R113663 : Reach 113663 := rs (se 1 (by rfl) ⟨85247, by rfl⟩) R170495
theorem R81919 : Reach 81919 := rs (se 1 (by rfl) ⟨61439, by rfl⟩) R122879
theorem R311849 : Reach 311849 := rs (se 2 (by rfl) ⟨116943, by rfl⟩) R233887
theorem R444755 : Reach 444755 := rs (se 1 (by rfl) ⟨333566, by rfl⟩) R667133
theorem R347689 : Reach 347689 := rs (se 2 (by rfl) ⟨130383, by rfl⟩) R260767
theorem R222527 : Reach 222527 := rs (se 1 (by rfl) ⟨166895, by rfl⟩) R333791
theorem R261737 : Reach 261737 := rs (se 2 (by rfl) ⟨98151, by rfl⟩) R196303
theorem R5177279 : Reach 5177279 := rs (se 1 (by rfl) ⟨3882959, by rfl⟩) R7765919
theorem R263465 : Reach 263465 := rs (se 2 (by rfl) ⟨98799, by rfl⟩) R197599
theorem R296503 : Reach 296503 := rs (se 1 (by rfl) ⟨222377, by rfl⟩) R444755
theorem R593405 : Reach 593405 := rs (se 3 (by rfl) ⟨111263, by rfl⟩) R222527
theorem R463585 : Reach 463585 := rs (se 2 (by rfl) ⟨173844, by rfl⟩) R347689
theorem R237449 : Reach 237449 := rs (se 2 (by rfl) ⟨89043, by rfl⟩) R178087
theorem R75775 : Reach 75775 := rs (se 1 (by rfl) ⟨56831, by rfl⟩) R113663
theorem R174491 : Reach 174491 := rs (se 1 (by rfl) ⟨130868, by rfl⟩) R261737
theorem R13806077 : Reach 13806077 := rs (se 3 (by rfl) ⟨2588639, by rfl⟩) R5177279
theorem R109225 : Reach 109225 := rs (se 2 (by rfl) ⟨40959, by rfl⟩) R81919
theorem R207899 : Reach 207899 := rs (se 1 (by rfl) ⟨155924, by rfl⟩) R311849
theorem R115199 : Reach 115199 := rs (se 1 (by rfl) ⟨86399, by rfl⟩) R172799
theorem R116975 : Reach 116975 := rs (se 1 (by rfl) ⟨87731, by rfl⟩) R175463
theorem R380699 : Reach 380699 := rs (se 1 (by rfl) ⟨285524, by rfl⟩) R571049
theorem R190633 : Reach 190633 := rs (se 2 (by rfl) ⟨71487, by rfl⟩) R142975
theorem R6325397 : Reach 6325397 := rs (se 6 (by rfl) ⟨148251, by rfl⟩) R296503
theorem R395603 : Reach 395603 := rs (se 1 (by rfl) ⟨296702, by rfl⟩) R593405
theorem R138599 : Reach 138599 := rs (se 1 (by rfl) ⟨103949, by rfl⟩) R207899
theorem R633197 : Reach 633197 := rs (se 3 (by rfl) ⟨118724, by rfl⟩) R237449
theorem R76799 : Reach 76799 := rs (se 1 (by rfl) ⟨57599, by rfl⟩) R115199
theorem R175643 : Reach 175643 := rs (se 1 (by rfl) ⟨131732, by rfl⟩) R263465
theorem R77983 : Reach 77983 := rs (se 1 (by rfl) ⟨58487, by rfl⟩) R116975
theorem R145633 : Reach 145633 := rs (se 2 (by rfl) ⟨54612, by rfl⟩) R109225
theorem R36816205 : Reach 36816205 := rs (se 3 (by rfl) ⟨6903038, by rfl⟩) R13806077
theorem R116327 : Reach 116327 := rs (se 1 (by rfl) ⟨87245, by rfl⟩) R174491
theorem R253799 : Reach 253799 := rs (se 1 (by rfl) ⟨190349, by rfl⟩) R380699
theorem R254177 : Reach 254177 := rs (se 2 (by rfl) ⟨95316, by rfl⟩) R190633
theorem R618113 : Reach 618113 := rs (se 2 (by rfl) ⟨231792, by rfl⟩) R463585
theorem R263735 : Reach 263735 := rs (se 1 (by rfl) ⟨197801, by rfl⟩) R395603
theorem R49088273 : Reach 49088273 := rs (se 2 (by rfl) ⟨18408102, by rfl⟩) R36816205
theorem R169199 : Reach 169199 := rs (se 1 (by rfl) ⟨126899, by rfl⟩) R253799
theorem R169451 : Reach 169451 := rs (se 1 (by rfl) ⟨127088, by rfl⟩) R254177
theorem R77551 : Reach 77551 := rs (se 1 (by rfl) ⟨58163, by rfl⟩) R116327
theorem R117095 : Reach 117095 := rs (se 1 (by rfl) ⟨87821, by rfl⟩) R175643
theorem R412075 : Reach 412075 := rs (se 1 (by rfl) ⟨309056, by rfl⟩) R618113
theorem R4216931 : Reach 4216931 := rs (se 1 (by rfl) ⟨3162698, by rfl⟩) R6325397
theorem R92399 : Reach 92399 := rs (se 1 (by rfl) ⟨69299, by rfl⟩) R138599
theorem R422131 : Reach 422131 := rs (se 1 (by rfl) ⟨316598, by rfl⟩) R633197
theorem R194177 : Reach 194177 := rs (se 2 (by rfl) ⟨72816, by rfl⟩) R145633
theorem R562841 : Reach 562841 := rs (se 2 (by rfl) ⟨211065, by rfl⟩) R422131
theorem R523608245 : Reach 523608245 := rs (se 5 (by rfl) ⟨24544136, by rfl⟩) R49088273
theorem R175823 : Reach 175823 := rs (se 1 (by rfl) ⟨131867, by rfl⟩) R263735
theorem R78063 : Reach 78063 := rs (se 1 (by rfl) ⟨58547, by rfl⟩) R117095
theorem R112799 : Reach 112799 := rs (se 1 (by rfl) ⟨84599, by rfl⟩) R169199
theorem R112967 : Reach 112967 := rs (se 1 (by rfl) ⟨84725, by rfl⟩) R169451
theorem R246397 : Reach 246397 := rs (se 3 (by rfl) ⟨46199, by rfl⟩) R92399
theorem R549433 : Reach 549433 := rs (se 2 (by rfl) ⟨206037, by rfl⟩) R412075
theorem R2811287 : Reach 2811287 := rs (se 1 (by rfl) ⟨2108465, by rfl⟩) R4216931
theorem R129451 : Reach 129451 := rs (se 1 (by rfl) ⟨97088, by rfl⟩) R194177
theorem R328529 : Reach 328529 := rs (se 2 (by rfl) ⟨123198, by rfl⟩) R246397
theorem R1874191 : Reach 1874191 := rs (se 1 (by rfl) ⟨1405643, by rfl⟩) R2811287
theorem R172601 : Reach 172601 := rs (se 2 (by rfl) ⟨64725, by rfl⟩) R129451
theorem R75199 : Reach 75199 := rs (se 1 (by rfl) ⟨56399, by rfl⟩) R112799
theorem R75311 : Reach 75311 := rs (se 1 (by rfl) ⟨56483, by rfl⟩) R112967
theorem R732577 : Reach 732577 := rs (se 2 (by rfl) ⟨274716, by rfl⟩) R549433
theorem R375227 : Reach 375227 := rs (se 1 (by rfl) ⟨281420, by rfl⟩) R562841
theorem R117215 : Reach 117215 := rs (se 1 (by rfl) ⟨87911, by rfl⟩) R175823
theorem R349072163 : Reach 349072163 := rs (se 1 (by rfl) ⟨261804122, by rfl⟩) R523608245
theorem R2498921 : Reach 2498921 := rs (se 2 (by rfl) ⟨937095, by rfl⟩) R1874191
theorem R78143 : Reach 78143 := rs (se 1 (by rfl) ⟨58607, by rfl⟩) R117215
theorem R115067 : Reach 115067 := rs (se 1 (by rfl) ⟨86300, by rfl⟩) R172601
theorem R250151 : Reach 250151 := rs (se 1 (by rfl) ⟨187613, by rfl⟩) R375227
theorem R219019 : Reach 219019 := rs (se 1 (by rfl) ⟨164264, by rfl⟩) R328529
theorem R976769 : Reach 976769 := rs (se 2 (by rfl) ⟨366288, by rfl⟩) R732577
theorem R232714775 : Reach 232714775 := rs (se 1 (by rfl) ⟨174536081, by rfl⟩) R349072163
theorem R76711 : Reach 76711 := rs (se 1 (by rfl) ⟨57533, by rfl⟩) R115067
theorem R2668277 : Reach 2668277 := rs (se 5 (by rfl) ⟨125075, by rfl⟩) R250151
theorem R155143183 : Reach 155143183 := rs (se 1 (by rfl) ⟨116357387, by rfl⟩) R232714775
theorem R1665947 : Reach 1665947 := rs (se 1 (by rfl) ⟨1249460, by rfl⟩) R2498921
theorem R651179 : Reach 651179 := rs (se 1 (by rfl) ⟨488384, by rfl⟩) R976769
theorem R292025 : Reach 292025 := rs (se 2 (by rfl) ⟨109509, by rfl⟩) R219019
theorem R434119 : Reach 434119 := rs (se 1 (by rfl) ⟨325589, by rfl⟩) R651179
theorem R1778851 : Reach 1778851 := rs (se 1 (by rfl) ⟨1334138, by rfl⟩) R2668277
theorem R206857577 : Reach 206857577 := rs (se 2 (by rfl) ⟨77571591, by rfl⟩) R155143183
theorem R1110631 : Reach 1110631 := rs (se 1 (by rfl) ⟨832973, by rfl⟩) R1665947
theorem R194683 : Reach 194683 := rs (se 1 (by rfl) ⟨146012, by rfl⟩) R292025
theorem R1480841 : Reach 1480841 := rs (se 2 (by rfl) ⟨555315, by rfl⟩) R1110631
theorem R2371801 : Reach 2371801 := rs (se 2 (by rfl) ⟨889425, by rfl⟩) R1778851
theorem R137905051 : Reach 137905051 := rs (se 1 (by rfl) ⟨103428788, by rfl⟩) R206857577
theorem R578825 : Reach 578825 := rs (se 2 (by rfl) ⟨217059, by rfl⟩) R434119
theorem R259577 : Reach 259577 := rs (se 2 (by rfl) ⟨97341, by rfl⟩) R194683
theorem R987227 : Reach 987227 := rs (se 1 (by rfl) ⟨740420, by rfl⟩) R1480841
theorem R173051 : Reach 173051 := rs (se 1 (by rfl) ⟨129788, by rfl⟩) R259577
theorem R183873401 : Reach 183873401 := rs (se 2 (by rfl) ⟨68952525, by rfl⟩) R137905051
theorem R3162401 : Reach 3162401 := rs (se 2 (by rfl) ⟨1185900, by rfl⟩) R2371801
theorem R385883 : Reach 385883 := rs (se 1 (by rfl) ⟨289412, by rfl⟩) R578825
theorem R658151 : Reach 658151 := rs (se 1 (by rfl) ⟨493613, by rfl⟩) R987227
theorem R2108267 : Reach 2108267 := rs (se 1 (by rfl) ⟨1581200, by rfl⟩) R3162401
theorem R115367 : Reach 115367 := rs (se 1 (by rfl) ⟨86525, by rfl⟩) R173051
theorem R257255 : Reach 257255 := rs (se 1 (by rfl) ⟨192941, by rfl⟩) R385883
theorem R122582267 : Reach 122582267 := rs (se 1 (by rfl) ⟨91936700, by rfl⟩) R183873401
theorem R171503 : Reach 171503 := rs (se 1 (by rfl) ⟨128627, by rfl⟩) R257255
theorem R76911 : Reach 76911 := rs (se 1 (by rfl) ⟨57683, by rfl⟩) R115367
theorem R438767 : Reach 438767 := rs (se 1 (by rfl) ⟨329075, by rfl⟩) R658151
theorem R1405511 : Reach 1405511 := rs (se 1 (by rfl) ⟨1054133, by rfl⟩) R2108267
theorem R81721511 : Reach 81721511 := rs (se 1 (by rfl) ⟨61291133, by rfl⟩) R122582267
theorem R114335 : Reach 114335 := rs (se 1 (by rfl) ⟨85751, by rfl⟩) R171503
theorem R937007 : Reach 937007 := rs (se 1 (by rfl) ⟨702755, by rfl⟩) R1405511
theorem R54481007 : Reach 54481007 := rs (se 1 (by rfl) ⟨40860755, by rfl⟩) R81721511
theorem R292511 : Reach 292511 := rs (se 1 (by rfl) ⟨219383, by rfl⟩) R438767
theorem R624671 : Reach 624671 := rs (se 1 (by rfl) ⟨468503, by rfl⟩) R937007
theorem R76223 : Reach 76223 := rs (se 1 (by rfl) ⟨57167, by rfl⟩) R114335
theorem R36320671 : Reach 36320671 := rs (se 1 (by rfl) ⟨27240503, by rfl⟩) R54481007
theorem R195007 : Reach 195007 := rs (se 1 (by rfl) ⟨146255, by rfl⟩) R292511
theorem R416447 : Reach 416447 := rs (se 1 (by rfl) ⟨312335, by rfl⟩) R624671
theorem R48427561 : Reach 48427561 := rs (se 2 (by rfl) ⟨18160335, by rfl⟩) R36320671
theorem R260009 : Reach 260009 := rs (se 2 (by rfl) ⟨97503, by rfl⟩) R195007
theorem R173339 : Reach 173339 := rs (se 1 (by rfl) ⟨130004, by rfl⟩) R260009
theorem R277631 : Reach 277631 := rs (se 1 (by rfl) ⟨208223, by rfl⟩) R416447
theorem R64570081 : Reach 64570081 := rs (se 2 (by rfl) ⟨24213780, by rfl⟩) R48427561
theorem R86093441 : Reach 86093441 := rs (se 2 (by rfl) ⟨32285040, by rfl⟩) R64570081
theorem R115559 : Reach 115559 := rs (se 1 (by rfl) ⟨86669, by rfl⟩) R173339
theorem R185087 : Reach 185087 := rs (se 1 (by rfl) ⟨138815, by rfl⟩) R277631
theorem R77039 : Reach 77039 := rs (se 1 (by rfl) ⟨57779, by rfl⟩) R115559
theorem R57395627 : Reach 57395627 := rs (se 1 (by rfl) ⟨43046720, by rfl⟩) R86093441
theorem R123391 : Reach 123391 := rs (se 1 (by rfl) ⟨92543, by rfl⟩) R185087
theorem R164521 : Reach 164521 := rs (se 2 (by rfl) ⟨61695, by rfl⟩) R123391
theorem R38263751 : Reach 38263751 := rs (se 1 (by rfl) ⟨28697813, by rfl⟩) R57395627
theorem R25509167 : Reach 25509167 := rs (se 1 (by rfl) ⟨19131875, by rfl⟩) R38263751
theorem R219361 : Reach 219361 := rs (se 2 (by rfl) ⟨82260, by rfl⟩) R164521
theorem R292481 : Reach 292481 := rs (se 2 (by rfl) ⟨109680, by rfl⟩) R219361
theorem R17006111 : Reach 17006111 := rs (se 1 (by rfl) ⟨12754583, by rfl⟩) R25509167
theorem R194987 : Reach 194987 := rs (se 1 (by rfl) ⟨146240, by rfl⟩) R292481
theorem R11337407 : Reach 11337407 := rs (se 1 (by rfl) ⟨8503055, by rfl⟩) R17006111
theorem R7558271 : Reach 7558271 := rs (se 1 (by rfl) ⟨5668703, by rfl⟩) R11337407
theorem R129991 : Reach 129991 := rs (se 1 (by rfl) ⟨97493, by rfl⟩) R194987
theorem R173321 : Reach 173321 := rs (se 2 (by rfl) ⟨64995, by rfl⟩) R129991
theorem R5038847 : Reach 5038847 := rs (se 1 (by rfl) ⟨3779135, by rfl⟩) R7558271
theorem R3359231 : Reach 3359231 := rs (se 1 (by rfl) ⟨2519423, by rfl⟩) R5038847
theorem R115547 : Reach 115547 := rs (se 1 (by rfl) ⟨86660, by rfl⟩) R173321
theorem R2239487 : Reach 2239487 := rs (se 1 (by rfl) ⟨1679615, by rfl⟩) R3359231
theorem R77031 : Reach 77031 := rs (se 1 (by rfl) ⟨57773, by rfl⟩) R115547
theorem R1492991 : Reach 1492991 := rs (se 1 (by rfl) ⟨1119743, by rfl⟩) R2239487
theorem R995327 : Reach 995327 := rs (se 1 (by rfl) ⟨746495, by rfl⟩) R1492991
theorem R663551 : Reach 663551 := rs (se 1 (by rfl) ⟨497663, by rfl⟩) R995327
theorem R442367 : Reach 442367 := rs (se 1 (by rfl) ⟨331775, by rfl⟩) R663551
theorem R294911 : Reach 294911 := rs (se 1 (by rfl) ⟨221183, by rfl⟩) R442367
theorem R196607 : Reach 196607 := rs (se 1 (by rfl) ⟨147455, by rfl⟩) R294911
theorem R131071 : Reach 131071 := rs (se 1 (by rfl) ⟨98303, by rfl⟩) R196607
theorem R174761 : Reach 174761 := rs (se 2 (by rfl) ⟨65535, by rfl⟩) R131071
theorem R116507 : Reach 116507 := rs (se 1 (by rfl) ⟨87380, by rfl⟩) R174761
theorem R77671 : Reach 77671 := rs (se 1 (by rfl) ⟨58253, by rfl⟩) R116507

theorem C0 (j : ℕ) (h1 : 37563 ≤ j) (h2 : j ≤ 38262) : Reach (2 * j + 1) := by
  interval_cases j
  · exact R75127
  · exact R75129
  · exact R75131
  · exact R75133
  · exact R75135
  · exact R75137
  · exact R75139
  · exact R75141
  · exact R75143
  · exact R75145
  · exact R75147
  · exact R75149
  · exact R75151
  · exact R75153
  · exact R75155
  · exact R75157
  · exact R75159
  · exact R75161
  · exact R75163
  · exact R75165
  · exact R75167
  · exact R75169
  · exact R75171
  · exact R75173
  · exact R75175
  · exact R75177
  · exact R75179
  · exact R75181
  · exact R75183
  · exact R75185
  · exact R75187
  · exact R75189
  · exact R75191
  · exact R75193
  · exact R75195
  · exact R75197
  · exact R75199
  · exact R75201
  · exact R75203
  · exact R75205
  · exact R75207
  · exact R75209
  · exact R75211
  · exact R75213
  · exact R75215
  · exact R75217
  · exact R75219
  · exact R75221
  · exact R75223
  · exact R75225
  · exact R75227
  · exact R75229
  · exact R75231
  · exact R75233
  · exact R75235
  · exact R75237
  · exact R75239
  · exact R75241
  · exact R75243
  · exact R75245
  · exact R75247
  · exact R75249
  · exact R75251
  · exact R75253
  · exact R75255
  · exact R75257
  · exact R75259
  · exact R75261
  · exact R75263
  · exact R75265
  · exact R75267
  · exact R75269
  · exact R75271
  · exact R75273
  · exact R75275
  · exact R75277
  · exact R75279
  · exact R75281
  · exact R75283
  · exact R75285
  · exact R75287
  · exact R75289
  · exact R75291
  · exact R75293
  · exact R75295
  · exact R75297
  · exact R75299
  · exact R75301
  · exact R75303
  · exact R75305
  · exact R75307
  · exact R75309
  · exact R75311
  · exact R75313
  · exact R75315
  · exact R75317
  · exact R75319
  · exact R75321
  · exact R75323
  · exact R75325
  · exact R75327
  · exact R75329
  · exact R75331
  · exact R75333
  · exact R75335
  · exact R75337
  · exact R75339
  · exact R75341
  · exact R75343
  · exact R75345
  · exact R75347
  · exact R75349
  · exact R75351
  · exact R75353
  · exact R75355
  · exact R75357
  · exact R75359
  · exact R75361
  · exact R75363
  · exact R75365
  · exact R75367
  · exact R75369
  · exact R75371
  · exact R75373
  · exact R75375
  · exact R75377
  · exact R75379
  · exact R75381
  · exact R75383
  · exact R75385
  · exact R75387
  · exact R75389
  · exact R75391
  · exact R75393
  · exact R75395
  · exact R75397
  · exact R75399
  · exact R75401
  · exact R75403
  · exact R75405
  · exact R75407
  · exact R75409
  · exact R75411
  · exact R75413
  · exact R75415
  · exact R75417
  · exact R75419
  · exact R75421
  · exact R75423
  · exact R75425
  · exact R75427
  · exact R75429
  · exact R75431
  · exact R75433
  · exact R75435
  · exact R75437
  · exact R75439
  · exact R75441
  · exact R75443
  · exact R75445
  · exact R75447
  · exact R75449
  · exact R75451
  · exact R75453
  · exact R75455
  · exact R75457
  · exact R75459
  · exact R75461
  · exact R75463
  · exact R75465
  · exact R75467
  · exact R75469
  · exact R75471
  · exact R75473
  · exact R75475
  · exact R75477
  · exact R75479
  · exact R75481
  · exact R75483
  · exact R75485
  · exact R75487
  · exact R75489
  · exact R75491
  · exact R75493
  · exact R75495
  · exact R75497
  · exact R75499
  · exact R75501
  · exact R75503
  · exact R75505
  · exact R75507
  · exact R75509
  · exact R75511
  · exact R75513
  · exact R75515
  · exact R75517
  · exact R75519
  · exact R75521
  · exact R75523
  · exact R75525
  · exact R75527
  · exact R75529
  · exact R75531
  · exact R75533
  · exact R75535
  · exact R75537
  · exact R75539
  · exact R75541
  · exact R75543
  · exact R75545
  · exact R75547
  · exact R75549
  · exact R75551
  · exact R75553
  · exact R75555
  · exact R75557
  · exact R75559
  · exact R75561
  · exact R75563
  · exact R75565
  · exact R75567
  · exact R75569
  · exact R75571
  · exact R75573
  · exact R75575
  · exact R75577
  · exact R75579
  · exact R75581
  · exact R75583
  · exact R75585
  · exact R75587
  · exact R75589
  · exact R75591
  · exact R75593
  · exact R75595
  · exact R75597
  · exact R75599
  · exact R75601
  · exact R75603
  · exact R75605
  · exact R75607
  · exact R75609
  · exact R75611
  · exact R75613
  · exact R75615
  · exact R75617
  · exact R75619
  · exact R75621
  · exact R75623
  · exact R75625
  · exact R75627
  · exact R75629
  · exact R75631
  · exact R75633
  · exact R75635
  · exact R75637
  · exact R75639
  · exact R75641
  · exact R75643
  · exact R75645
  · exact R75647
  · exact R75649
  · exact R75651
  · exact R75653
  · exact R75655
  · exact R75657
  · exact R75659
  · exact R75661
  · exact R75663
  · exact R75665
  · exact R75667
  · exact R75669
  · exact R75671
  · exact R75673
  · exact R75675
  · exact R75677
  · exact R75679
  · exact R75681
  · exact R75683
  · exact R75685
  · exact R75687
  · exact R75689
  · exact R75691
  · exact R75693
  · exact R75695
  · exact R75697
  · exact R75699
  · exact R75701
  · exact R75703
  · exact R75705
  · exact R75707
  · exact R75709
  · exact R75711
  · exact R75713
  · exact R75715
  · exact R75717
  · exact R75719
  · exact R75721
  · exact R75723
  · exact R75725
  · exact R75727
  · exact R75729
  · exact R75731
  · exact R75733
  · exact R75735
  · exact R75737
  · exact R75739
  · exact R75741
  · exact R75743
  · exact R75745
  · exact R75747
  · exact R75749
  · exact R75751
  · exact R75753
  · exact R75755
  · exact R75757
  · exact R75759
  · exact R75761
  · exact R75763
  · exact R75765
  · exact R75767
  · exact R75769
  · exact R75771
  · exact R75773
  · exact R75775
  · exact R75777
  · exact R75779
  · exact R75781
  · exact R75783
  · exact R75785
  · exact R75787
  · exact R75789
  · exact R75791
  · exact R75793
  · exact R75795
  · exact R75797
  · exact R75799
  · exact R75801
  · exact R75803
  · exact R75805
  · exact R75807
  · exact R75809
  · exact R75811
  · exact R75813
  · exact R75815
  · exact R75817
  · exact R75819
  · exact R75821
  · exact R75823
  · exact R75825
  · exact R75827
  · exact R75829
  · exact R75831
  · exact R75833
  · exact R75835
  · exact R75837
  · exact R75839
  · exact R75841
  · exact R75843
  · exact R75845
  · exact R75847
  · exact R75849
  · exact R75851
  · exact R75853
  · exact R75855
  · exact R75857
  · exact R75859
  · exact R75861
  · exact R75863
  · exact R75865
  · exact R75867
  · exact R75869
  · exact R75871
  · exact R75873
  · exact R75875
  · exact R75877
  · exact R75879
  · exact R75881
  · exact R75883
  · exact R75885
  · exact R75887
  · exact R75889
  · exact R75891
  · exact R75893
  · exact R75895
  · exact R75897
  · exact R75899
  · exact R75901
  · exact R75903
  · exact R75905
  · exact R75907
  · exact R75909
  · exact R75911
  · exact R75913
  · exact R75915
  · exact R75917
  · exact R75919
  · exact R75921
  · exact R75923
  · exact R75925
  · exact R75927
  · exact R75929
  · exact R75931
  · exact R75933
  · exact R75935
  · exact R75937
  · exact R75939
  · exact R75941
  · exact R75943
  · exact R75945
  · exact R75947
  · exact R75949
  · exact R75951
  · exact R75953
  · exact R75955
  · exact R75957
  · exact R75959
  · exact R75961
  · exact R75963
  · exact R75965
  · exact R75967
  · exact R75969
  · exact R75971
  · exact R75973
  · exact R75975
  · exact R75977
  · exact R75979
  · exact R75981
  · exact R75983
  · exact R75985
  · exact R75987
  · exact R75989
  · exact R75991
  · exact R75993
  · exact R75995
  · exact R75997
  · exact R75999
  · exact R76001
  · exact R76003
  · exact R76005
  · exact R76007
  · exact R76009
  · exact R76011
  · exact R76013
  · exact R76015
  · exact R76017
  · exact R76019
  · exact R76021
  · exact R76023
  · exact R76025
  · exact R76027
  · exact R76029
  · exact R76031
  · exact R76033
  · exact R76035
  · exact R76037
  · exact R76039
  · exact R76041
  · exact R76043
  · exact R76045
  · exact R76047
  · exact R76049
  · exact R76051
  · exact R76053
  · exact R76055
  · exact R76057
  · exact R76059
  · exact R76061
  · exact R76063
  · exact R76065
  · exact R76067
  · exact R76069
  · exact R76071
  · exact R76073
  · exact R76075
  · exact R76077
  · exact R76079
  · exact R76081
  · exact R76083
  · exact R76085
  · exact R76087
  · exact R76089
  · exact R76091
  · exact R76093
  · exact R76095
  · exact R76097
  · exact R76099
  · exact R76101
  · exact R76103
  · exact R76105
  · exact R76107
  · exact R76109
  · exact R76111
  · exact R76113
  · exact R76115
  · exact R76117
  · exact R76119
  · exact R76121
  · exact R76123
  · exact R76125
  · exact R76127
  · exact R76129
  · exact R76131
  · exact R76133
  · exact R76135
  · exact R76137
  · exact R76139
  · exact R76141
  · exact R76143
  · exact R76145
  · exact R76147
  · exact R76149
  · exact R76151
  · exact R76153
  · exact R76155
  · exact R76157
  · exact R76159
  · exact R76161
  · exact R76163
  · exact R76165
  · exact R76167
  · exact R76169
  · exact R76171
  · exact R76173
  · exact R76175
  · exact R76177
  · exact R76179
  · exact R76181
  · exact R76183
  · exact R76185
  · exact R76187
  · exact R76189
  · exact R76191
  · exact R76193
  · exact R76195
  · exact R76197
  · exact R76199
  · exact R76201
  · exact R76203
  · exact R76205
  · exact R76207
  · exact R76209
  · exact R76211
  · exact R76213
  · exact R76215
  · exact R76217
  · exact R76219
  · exact R76221
  · exact R76223
  · exact R76225
  · exact R76227
  · exact R76229
  · exact R76231
  · exact R76233
  · exact R76235
  · exact R76237
  · exact R76239
  · exact R76241
  · exact R76243
  · exact R76245
  · exact R76247
  · exact R76249
  · exact R76251
  · exact R76253
  · exact R76255
  · exact R76257
  · exact R76259
  · exact R76261
  · exact R76263
  · exact R76265
  · exact R76267
  · exact R76269
  · exact R76271
  · exact R76273
  · exact R76275
  · exact R76277
  · exact R76279
  · exact R76281
  · exact R76283
  · exact R76285
  · exact R76287
  · exact R76289
  · exact R76291
  · exact R76293
  · exact R76295
  · exact R76297
  · exact R76299
  · exact R76301
  · exact R76303
  · exact R76305
  · exact R76307
  · exact R76309
  · exact R76311
  · exact R76313
  · exact R76315
  · exact R76317
  · exact R76319
  · exact R76321
  · exact R76323
  · exact R76325
  · exact R76327
  · exact R76329
  · exact R76331
  · exact R76333
  · exact R76335
  · exact R76337
  · exact R76339
  · exact R76341
  · exact R76343
  · exact R76345
  · exact R76347
  · exact R76349
  · exact R76351
  · exact R76353
  · exact R76355
  · exact R76357
  · exact R76359
  · exact R76361
  · exact R76363
  · exact R76365
  · exact R76367
  · exact R76369
  · exact R76371
  · exact R76373
  · exact R76375
  · exact R76377
  · exact R76379
  · exact R76381
  · exact R76383
  · exact R76385
  · exact R76387
  · exact R76389
  · exact R76391
  · exact R76393
  · exact R76395
  · exact R76397
  · exact R76399
  · exact R76401
  · exact R76403
  · exact R76405
  · exact R76407
  · exact R76409
  · exact R76411
  · exact R76413
  · exact R76415
  · exact R76417
  · exact R76419
  · exact R76421
  · exact R76423
  · exact R76425
  · exact R76427
  · exact R76429
  · exact R76431
  · exact R76433
  · exact R76435
  · exact R76437
  · exact R76439
  · exact R76441
  · exact R76443
  · exact R76445
  · exact R76447
  · exact R76449
  · exact R76451
  · exact R76453
  · exact R76455
  · exact R76457
  · exact R76459
  · exact R76461
  · exact R76463
  · exact R76465
  · exact R76467
  · exact R76469
  · exact R76471
  · exact R76473
  · exact R76475
  · exact R76477
  · exact R76479
  · exact R76481
  · exact R76483
  · exact R76485
  · exact R76487
  · exact R76489
  · exact R76491
  · exact R76493
  · exact R76495
  · exact R76497
  · exact R76499
  · exact R76501
  · exact R76503
  · exact R76505
  · exact R76507
  · exact R76509
  · exact R76511
  · exact R76513
  · exact R76515
  · exact R76517
  · exact R76519
  · exact R76521
  · exact R76523
  · exact R76525

theorem C1 (j : ℕ) (h1 : 38263 ≤ j) (h2 : j ≤ 38962) : Reach (2 * j + 1) := by
  interval_cases j
  · exact R76527
  · exact R76529
  · exact R76531
  · exact R76533
  · exact R76535
  · exact R76537
  · exact R76539
  · exact R76541
  · exact R76543
  · exact R76545
  · exact R76547
  · exact R76549
  · exact R76551
  · exact R76553
  · exact R76555
  · exact R76557
  · exact R76559
  · exact R76561
  · exact R76563
  · exact R76565
  · exact R76567
  · exact R76569
  · exact R76571
  · exact R76573
  · exact R76575
  · exact R76577
  · exact R76579
  · exact R76581
  · exact R76583
  · exact R76585
  · exact R76587
  · exact R76589
  · exact R76591
  · exact R76593
  · exact R76595
  · exact R76597
  · exact R76599
  · exact R76601
  · exact R76603
  · exact R76605
  · exact R76607
  · exact R76609
  · exact R76611
  · exact R76613
  · exact R76615
  · exact R76617
  · exact R76619
  · exact R76621
  · exact R76623
  · exact R76625
  · exact R76627
  · exact R76629
  · exact R76631
  · exact R76633
  · exact R76635
  · exact R76637
  · exact R76639
  · exact R76641
  · exact R76643
  · exact R76645
  · exact R76647
  · exact R76649
  · exact R76651
  · exact R76653
  · exact R76655
  · exact R76657
  · exact R76659
  · exact R76661
  · exact R76663
  · exact R76665
  · exact R76667
  · exact R76669
  · exact R76671
  · exact R76673
  · exact R76675
  · exact R76677
  · exact R76679
  · exact R76681
  · exact R76683
  · exact R76685
  · exact R76687
  · exact R76689
  · exact R76691
  · exact R76693
  · exact R76695
  · exact R76697
  · exact R76699
  · exact R76701
  · exact R76703
  · exact R76705
  · exact R76707
  · exact R76709
  · exact R76711
  · exact R76713
  · exact R76715
  · exact R76717
  · exact R76719
  · exact R76721
  · exact R76723
  · exact R76725
  · exact R76727
  · exact R76729
  · exact R76731
  · exact R76733
  · exact R76735
  · exact R76737
  · exact R76739
  · exact R76741
  · exact R76743
  · exact R76745
  · exact R76747
  · exact R76749
  · exact R76751
  · exact R76753
  · exact R76755
  · exact R76757
  · exact R76759
  · exact R76761
  · exact R76763
  · exact R76765
  · exact R76767
  · exact R76769
  · exact R76771
  · exact R76773
  · exact R76775
  · exact R76777
  · exact R76779
  · exact R76781
  · exact R76783
  · exact R76785
  · exact R76787
  · exact R76789
  · exact R76791
  · exact R76793
  · exact R76795
  · exact R76797
  · exact R76799
  · exact R76801
  · exact R76803
  · exact R76805
  · exact R76807
  · exact R76809
  · exact R76811
  · exact R76813
  · exact R76815
  · exact R76817
  · exact R76819
  · exact R76821
  · exact R76823
  · exact R76825
  · exact R76827
  · exact R76829
  · exact R76831
  · exact R76833
  · exact R76835
  · exact R76837
  · exact R76839
  · exact R76841
  · exact R76843
  · exact R76845
  · exact R76847
  · exact R76849
  · exact R76851
  · exact R76853
  · exact R76855
  · exact R76857
  · exact R76859
  · exact R76861
  · exact R76863
  · exact R76865
  · exact R76867
  · exact R76869
  · exact R76871
  · exact R76873
  · exact R76875
  · exact R76877
  · exact R76879
  · exact R76881
  · exact R76883
  · exact R76885
  · exact R76887
  · exact R76889
  · exact R76891
  · exact R76893
  · exact R76895
  · exact R76897
  · exact R76899
  · exact R76901
  · exact R76903
  · exact R76905
  · exact R76907
  · exact R76909
  · exact R76911
  · exact R76913
  · exact R76915
  · exact R76917
  · exact R76919
  · exact R76921
  · exact R76923
  · exact R76925
  · exact R76927
  · exact R76929
  · exact R76931
  · exact R76933
  · exact R76935
  · exact R76937
  · exact R76939
  · exact R76941
  · exact R76943
  · exact R76945
  · exact R76947
  · exact R76949
  · exact R76951
  · exact R76953
  · exact R76955
  · exact R76957
  · exact R76959
  · exact R76961
  · exact R76963
  · exact R76965
  · exact R76967
  · exact R76969
  · exact R76971
  · exact R76973
  · exact R76975
  · exact R76977
  · exact R76979
  · exact R76981
  · exact R76983
  · exact R76985
  · exact R76987
  · exact R76989
  · exact R76991
  · exact R76993
  · exact R76995
  · exact R76997
  · exact R76999
  · exact R77001
  · exact R77003
  · exact R77005
  · exact R77007
  · exact R77009
  · exact R77011
  · exact R77013
  · exact R77015
  · exact R77017
  · exact R77019
  · exact R77021
  · exact R77023
  · exact R77025
  · exact R77027
  · exact R77029
  · exact R77031
  · exact R77033
  · exact R77035
  · exact R77037
  · exact R77039
  · exact R77041
  · exact R77043
  · exact R77045
  · exact R77047
  · exact R77049
  · exact R77051
  · exact R77053
  · exact R77055
  · exact R77057
  · exact R77059
  · exact R77061
  · exact R77063
  · exact R77065
  · exact R77067
  · exact R77069
  · exact R77071
  · exact R77073
  · exact R77075
  · exact R77077
  · exact R77079
  · exact R77081
  · exact R77083
  · exact R77085
  · exact R77087
  · exact R77089
  · exact R77091
  · exact R77093
  · exact R77095
  · exact R77097
  · exact R77099
  · exact R77101
  · exact R77103
  · exact R77105
  · exact R77107
  · exact R77109
  · exact R77111
  · exact R77113
  · exact R77115
  · exact R77117
  · exact R77119
  · exact R77121
  · exact R77123
  · exact R77125
  · exact R77127
  · exact R77129
  · exact R77131
  · exact R77133
  · exact R77135
  · exact R77137
  · exact R77139
  · exact R77141
  · exact R77143
  · exact R77145
  · exact R77147
  · exact R77149
  · exact R77151
  · exact R77153
  · exact R77155
  · exact R77157
  · exact R77159
  · exact R77161
  · exact R77163
  · exact R77165
  · exact R77167
  · exact R77169
  · exact R77171
  · exact R77173
  · exact R77175
  · exact R77177
  · exact R77179
  · exact R77181
  · exact R77183
  · exact R77185
  · exact R77187
  · exact R77189
  · exact R77191
  · exact R77193
  · exact R77195
  · exact R77197
  · exact R77199
  · exact R77201
  · exact R77203
  · exact R77205
  · exact R77207
  · exact R77209
  · exact R77211
  · exact R77213
  · exact R77215
  · exact R77217
  · exact R77219
  · exact R77221
  · exact R77223
  · exact R77225
  · exact R77227
  · exact R77229
  · exact R77231
  · exact R77233
  · exact R77235
  · exact R77237
  · exact R77239
  · exact R77241
  · exact R77243
  · exact R77245
  · exact R77247
  · exact R77249
  · exact R77251
  · exact R77253
  · exact R77255
  · exact R77257
  · exact R77259
  · exact R77261
  · exact R77263
  · exact R77265
  · exact R77267
  · exact R77269
  · exact R77271
  · exact R77273
  · exact R77275
  · exact R77277
  · exact R77279
  · exact R77281
  · exact R77283
  · exact R77285
  · exact R77287
  · exact R77289
  · exact R77291
  · exact R77293
  · exact R77295
  · exact R77297
  · exact R77299
  · exact R77301
  · exact R77303
  · exact R77305
  · exact R77307
  · exact R77309
  · exact R77311
  · exact R77313
  · exact R77315
  · exact R77317
  · exact R77319
  · exact R77321
  · exact R77323
  · exact R77325
  · exact R77327
  · exact R77329
  · exact R77331
  · exact R77333
  · exact R77335
  · exact R77337
  · exact R77339
  · exact R77341
  · exact R77343
  · exact R77345
  · exact R77347
  · exact R77349
  · exact R77351
  · exact R77353
  · exact R77355
  · exact R77357
  · exact R77359
  · exact R77361
  · exact R77363
  · exact R77365
  · exact R77367
  · exact R77369
  · exact R77371
  · exact R77373
  · exact R77375
  · exact R77377
  · exact R77379
  · exact R77381
  · exact R77383
  · exact R77385
  · exact R77387
  · exact R77389
  · exact R77391
  · exact R77393
  · exact R77395
  · exact R77397
  · exact R77399
  · exact R77401
  · exact R77403
  · exact R77405
  · exact R77407
  · exact R77409
  · exact R77411
  · exact R77413
  · exact R77415
  · exact R77417
  · exact R77419
  · exact R77421
  · exact R77423
  · exact R77425
  · exact R77427
  · exact R77429
  · exact R77431
  · exact R77433
  · exact R77435
  · exact R77437
  · exact R77439
  · exact R77441
  · exact R77443
  · exact R77445
  · exact R77447
  · exact R77449
  · exact R77451
  · exact R77453
  · exact R77455
  · exact R77457
  · exact R77459
  · exact R77461
  · exact R77463
  · exact R77465
  · exact R77467
  · exact R77469
  · exact R77471
  · exact R77473
  · exact R77475
  · exact R77477
  · exact R77479
  · exact R77481
  · exact R77483
  · exact R77485
  · exact R77487
  · exact R77489
  · exact R77491
  · exact R77493
  · exact R77495
  · exact R77497
  · exact R77499
  · exact R77501
  · exact R77503
  · exact R77505
  · exact R77507
  · exact R77509
  · exact R77511
  · exact R77513
  · exact R77515
  · exact R77517
  · exact R77519
  · exact R77521
  · exact R77523
  · exact R77525
  · exact R77527
  · exact R77529
  · exact R77531
  · exact R77533
  · exact R77535
  · exact R77537
  · exact R77539
  · exact R77541
  · exact R77543
  · exact R77545
  · exact R77547
  · exact R77549
  · exact R77551
  · exact R77553
  · exact R77555
  · exact R77557
  · exact R77559
  · exact R77561
  · exact R77563
  · exact R77565
  · exact R77567
  · exact R77569
  · exact R77571
  · exact R77573
  · exact R77575
  · exact R77577
  · exact R77579
  · exact R77581
  · exact R77583
  · exact R77585
  · exact R77587
  · exact R77589
  · exact R77591
  · exact R77593
  · exact R77595
  · exact R77597
  · exact R77599
  · exact R77601
  · exact R77603
  · exact R77605
  · exact R77607
  · exact R77609
  · exact R77611
  · exact R77613
  · exact R77615
  · exact R77617
  · exact R77619
  · exact R77621
  · exact R77623
  · exact R77625
  · exact R77627
  · exact R77629
  · exact R77631
  · exact R77633
  · exact R77635
  · exact R77637
  · exact R77639
  · exact R77641
  · exact R77643
  · exact R77645
  · exact R77647
  · exact R77649
  · exact R77651
  · exact R77653
  · exact R77655
  · exact R77657
  · exact R77659
  · exact R77661
  · exact R77663
  · exact R77665
  · exact R77667
  · exact R77669
  · exact R77671
  · exact R77673
  · exact R77675
  · exact R77677
  · exact R77679
  · exact R77681
  · exact R77683
  · exact R77685
  · exact R77687
  · exact R77689
  · exact R77691
  · exact R77693
  · exact R77695
  · exact R77697
  · exact R77699
  · exact R77701
  · exact R77703
  · exact R77705
  · exact R77707
  · exact R77709
  · exact R77711
  · exact R77713
  · exact R77715
  · exact R77717
  · exact R77719
  · exact R77721
  · exact R77723
  · exact R77725
  · exact R77727
  · exact R77729
  · exact R77731
  · exact R77733
  · exact R77735
  · exact R77737
  · exact R77739
  · exact R77741
  · exact R77743
  · exact R77745
  · exact R77747
  · exact R77749
  · exact R77751
  · exact R77753
  · exact R77755
  · exact R77757
  · exact R77759
  · exact R77761
  · exact R77763
  · exact R77765
  · exact R77767
  · exact R77769
  · exact R77771
  · exact R77773
  · exact R77775
  · exact R77777
  · exact R77779
  · exact R77781
  · exact R77783
  · exact R77785
  · exact R77787
  · exact R77789
  · exact R77791
  · exact R77793
  · exact R77795
  · exact R77797
  · exact R77799
  · exact R77801
  · exact R77803
  · exact R77805
  · exact R77807
  · exact R77809
  · exact R77811
  · exact R77813
  · exact R77815
  · exact R77817
  · exact R77819
  · exact R77821
  · exact R77823
  · exact R77825
  · exact R77827
  · exact R77829
  · exact R77831
  · exact R77833
  · exact R77835
  · exact R77837
  · exact R77839
  · exact R77841
  · exact R77843
  · exact R77845
  · exact R77847
  · exact R77849
  · exact R77851
  · exact R77853
  · exact R77855
  · exact R77857
  · exact R77859
  · exact R77861
  · exact R77863
  · exact R77865
  · exact R77867
  · exact R77869
  · exact R77871
  · exact R77873
  · exact R77875
  · exact R77877
  · exact R77879
  · exact R77881
  · exact R77883
  · exact R77885
  · exact R77887
  · exact R77889
  · exact R77891
  · exact R77893
  · exact R77895
  · exact R77897
  · exact R77899
  · exact R77901
  · exact R77903
  · exact R77905
  · exact R77907
  · exact R77909
  · exact R77911
  · exact R77913
  · exact R77915
  · exact R77917
  · exact R77919
  · exact R77921
  · exact R77923
  · exact R77925

theorem C2 (j : ℕ) (h1 : 38963 ≤ j) (h2 : j ≤ 39562) : Reach (2 * j + 1) := by
  interval_cases j
  · exact R77927
  · exact R77929
  · exact R77931
  · exact R77933
  · exact R77935
  · exact R77937
  · exact R77939
  · exact R77941
  · exact R77943
  · exact R77945
  · exact R77947
  · exact R77949
  · exact R77951
  · exact R77953
  · exact R77955
  · exact R77957
  · exact R77959
  · exact R77961
  · exact R77963
  · exact R77965
  · exact R77967
  · exact R77969
  · exact R77971
  · exact R77973
  · exact R77975
  · exact R77977
  · exact R77979
  · exact R77981
  · exact R77983
  · exact R77985
  · exact R77987
  · exact R77989
  · exact R77991
  · exact R77993
  · exact R77995
  · exact R77997
  · exact R77999
  · exact R78001
  · exact R78003
  · exact R78005
  · exact R78007
  · exact R78009
  · exact R78011
  · exact R78013
  · exact R78015
  · exact R78017
  · exact R78019
  · exact R78021
  · exact R78023
  · exact R78025
  · exact R78027
  · exact R78029
  · exact R78031
  · exact R78033
  · exact R78035
  · exact R78037
  · exact R78039
  · exact R78041
  · exact R78043
  · exact R78045
  · exact R78047
  · exact R78049
  · exact R78051
  · exact R78053
  · exact R78055
  · exact R78057
  · exact R78059
  · exact R78061
  · exact R78063
  · exact R78065
  · exact R78067
  · exact R78069
  · exact R78071
  · exact R78073
  · exact R78075
  · exact R78077
  · exact R78079
  · exact R78081
  · exact R78083
  · exact R78085
  · exact R78087
  · exact R78089
  · exact R78091
  · exact R78093
  · exact R78095
  · exact R78097
  · exact R78099
  · exact R78101
  · exact R78103
  · exact R78105
  · exact R78107
  · exact R78109
  · exact R78111
  · exact R78113
  · exact R78115
  · exact R78117
  · exact R78119
  · exact R78121
  · exact R78123
  · exact R78125
  · exact R78127
  · exact R78129
  · exact R78131
  · exact R78133
  · exact R78135
  · exact R78137
  · exact R78139
  · exact R78141
  · exact R78143
  · exact R78145
  · exact R78147
  · exact R78149
  · exact R78151
  · exact R78153
  · exact R78155
  · exact R78157
  · exact R78159
  · exact R78161
  · exact R78163
  · exact R78165
  · exact R78167
  · exact R78169
  · exact R78171
  · exact R78173
  · exact R78175
  · exact R78177
  · exact R78179
  · exact R78181
  · exact R78183
  · exact R78185
  · exact R78187
  · exact R78189
  · exact R78191
  · exact R78193
  · exact R78195
  · exact R78197
  · exact R78199
  · exact R78201
  · exact R78203
  · exact R78205
  · exact R78207
  · exact R78209
  · exact R78211
  · exact R78213
  · exact R78215
  · exact R78217
  · exact R78219
  · exact R78221
  · exact R78223
  · exact R78225
  · exact R78227
  · exact R78229
  · exact R78231
  · exact R78233
  · exact R78235
  · exact R78237
  · exact R78239
  · exact R78241
  · exact R78243
  · exact R78245
  · exact R78247
  · exact R78249
  · exact R78251
  · exact R78253
  · exact R78255
  · exact R78257
  · exact R78259
  · exact R78261
  · exact R78263
  · exact R78265
  · exact R78267
  · exact R78269
  · exact R78271
  · exact R78273
  · exact R78275
  · exact R78277
  · exact R78279
  · exact R78281
  · exact R78283
  · exact R78285
  · exact R78287
  · exact R78289
  · exact R78291
  · exact R78293
  · exact R78295
  · exact R78297
  · exact R78299
  · exact R78301
  · exact R78303
  · exact R78305
  · exact R78307
  · exact R78309
  · exact R78311
  · exact R78313
  · exact R78315
  · exact R78317
  · exact R78319
  · exact R78321
  · exact R78323
  · exact R78325
  · exact R78327
  · exact R78329
  · exact R78331
  · exact R78333
  · exact R78335
  · exact R78337
  · exact R78339
  · exact R78341
  · exact R78343
  · exact R78345
  · exact R78347
  · exact R78349
  · exact R78351
  · exact R78353
  · exact R78355
  · exact R78357
  · exact R78359
  · exact R78361
  · exact R78363
  · exact R78365
  · exact R78367
  · exact R78369
  · exact R78371
  · exact R78373
  · exact R78375
  · exact R78377
  · exact R78379
  · exact R78381
  · exact R78383
  · exact R78385
  · exact R78387
  · exact R78389
  · exact R78391
  · exact R78393
  · exact R78395
  · exact R78397
  · exact R78399
  · exact R78401
  · exact R78403
  · exact R78405
  · exact R78407
  · exact R78409
  · exact R78411
  · exact R78413
  · exact R78415
  · exact R78417
  · exact R78419
  · exact R78421
  · exact R78423
  · exact R78425
  · exact R78427
  · exact R78429
  · exact R78431
  · exact R78433
  · exact R78435
  · exact R78437
  · exact R78439
  · exact R78441
  · exact R78443
  · exact R78445
  · exact R78447
  · exact R78449
  · exact R78451
  · exact R78453
  · exact R78455
  · exact R78457
  · exact R78459
  · exact R78461
  · exact R78463
  · exact R78465
  · exact R78467
  · exact R78469
  · exact R78471
  · exact R78473
  · exact R78475
  · exact R78477
  · exact R78479
  · exact R78481
  · exact R78483
  · exact R78485
  · exact R78487
  · exact R78489
  · exact R78491
  · exact R78493
  · exact R78495
  · exact R78497
  · exact R78499
  · exact R78501
  · exact R78503
  · exact R78505
  · exact R78507
  · exact R78509
  · exact R78511
  · exact R78513
  · exact R78515
  · exact R78517
  · exact R78519
  · exact R78521
  · exact R78523
  · exact R78525
  · exact R78527
  · exact R78529
  · exact R78531
  · exact R78533
  · exact R78535
  · exact R78537
  · exact R78539
  · exact R78541
  · exact R78543
  · exact R78545
  · exact R78547
  · exact R78549
  · exact R78551
  · exact R78553
  · exact R78555
  · exact R78557
  · exact R78559
  · exact R78561
  · exact R78563
  · exact R78565
  · exact R78567
  · exact R78569
  · exact R78571
  · exact R78573
  · exact R78575
  · exact R78577
  · exact R78579
  · exact R78581
  · exact R78583
  · exact R78585
  · exact R78587
  · exact R78589
  · exact R78591
  · exact R78593
  · exact R78595
  · exact R78597
  · exact R78599
  · exact R78601
  · exact R78603
  · exact R78605
  · exact R78607
  · exact R78609
  · exact R78611
  · exact R78613
  · exact R78615
  · exact R78617
  · exact R78619
  · exact R78621
  · exact R78623
  · exact R78625
  · exact R78627
  · exact R78629
  · exact R78631
  · exact R78633
  · exact R78635
  · exact R78637
  · exact R78639
  · exact R78641
  · exact R78643
  · exact R78645
  · exact R78647
  · exact R78649
  · exact R78651
  · exact R78653
  · exact R78655
  · exact R78657
  · exact R78659
  · exact R78661
  · exact R78663
  · exact R78665
  · exact R78667
  · exact R78669
  · exact R78671
  · exact R78673
  · exact R78675
  · exact R78677
  · exact R78679
  · exact R78681
  · exact R78683
  · exact R78685
  · exact R78687
  · exact R78689
  · exact R78691
  · exact R78693
  · exact R78695
  · exact R78697
  · exact R78699
  · exact R78701
  · exact R78703
  · exact R78705
  · exact R78707
  · exact R78709
  · exact R78711
  · exact R78713
  · exact R78715
  · exact R78717
  · exact R78719
  · exact R78721
  · exact R78723
  · exact R78725
  · exact R78727
  · exact R78729
  · exact R78731
  · exact R78733
  · exact R78735
  · exact R78737
  · exact R78739
  · exact R78741
  · exact R78743
  · exact R78745
  · exact R78747
  · exact R78749
  · exact R78751
  · exact R78753
  · exact R78755
  · exact R78757
  · exact R78759
  · exact R78761
  · exact R78763
  · exact R78765
  · exact R78767
  · exact R78769
  · exact R78771
  · exact R78773
  · exact R78775
  · exact R78777
  · exact R78779
  · exact R78781
  · exact R78783
  · exact R78785
  · exact R78787
  · exact R78789
  · exact R78791
  · exact R78793
  · exact R78795
  · exact R78797
  · exact R78799
  · exact R78801
  · exact R78803
  · exact R78805
  · exact R78807
  · exact R78809
  · exact R78811
  · exact R78813
  · exact R78815
  · exact R78817
  · exact R78819
  · exact R78821
  · exact R78823
  · exact R78825
  · exact R78827
  · exact R78829
  · exact R78831
  · exact R78833
  · exact R78835
  · exact R78837
  · exact R78839
  · exact R78841
  · exact R78843
  · exact R78845
  · exact R78847
  · exact R78849
  · exact R78851
  · exact R78853
  · exact R78855
  · exact R78857
  · exact R78859
  · exact R78861
  · exact R78863
  · exact R78865
  · exact R78867
  · exact R78869
  · exact R78871
  · exact R78873
  · exact R78875
  · exact R78877
  · exact R78879
  · exact R78881
  · exact R78883
  · exact R78885
  · exact R78887
  · exact R78889
  · exact R78891
  · exact R78893
  · exact R78895
  · exact R78897
  · exact R78899
  · exact R78901
  · exact R78903
  · exact R78905
  · exact R78907
  · exact R78909
  · exact R78911
  · exact R78913
  · exact R78915
  · exact R78917
  · exact R78919
  · exact R78921
  · exact R78923
  · exact R78925
  · exact R78927
  · exact R78929
  · exact R78931
  · exact R78933
  · exact R78935
  · exact R78937
  · exact R78939
  · exact R78941
  · exact R78943
  · exact R78945
  · exact R78947
  · exact R78949
  · exact R78951
  · exact R78953
  · exact R78955
  · exact R78957
  · exact R78959
  · exact R78961
  · exact R78963
  · exact R78965
  · exact R78967
  · exact R78969
  · exact R78971
  · exact R78973
  · exact R78975
  · exact R78977
  · exact R78979
  · exact R78981
  · exact R78983
  · exact R78985
  · exact R78987
  · exact R78989
  · exact R78991
  · exact R78993
  · exact R78995
  · exact R78997
  · exact R78999
  · exact R79001
  · exact R79003
  · exact R79005
  · exact R79007
  · exact R79009
  · exact R79011
  · exact R79013
  · exact R79015
  · exact R79017
  · exact R79019
  · exact R79021
  · exact R79023
  · exact R79025
  · exact R79027
  · exact R79029
  · exact R79031
  · exact R79033
  · exact R79035
  · exact R79037
  · exact R79039
  · exact R79041
  · exact R79043
  · exact R79045
  · exact R79047
  · exact R79049
  · exact R79051
  · exact R79053
  · exact R79055
  · exact R79057
  · exact R79059
  · exact R79061
  · exact R79063
  · exact R79065
  · exact R79067
  · exact R79069
  · exact R79071
  · exact R79073
  · exact R79075
  · exact R79077
  · exact R79079
  · exact R79081
  · exact R79083
  · exact R79085
  · exact R79087
  · exact R79089
  · exact R79091
  · exact R79093
  · exact R79095
  · exact R79097
  · exact R79099
  · exact R79101
  · exact R79103
  · exact R79105
  · exact R79107
  · exact R79109
  · exact R79111
  · exact R79113
  · exact R79115
  · exact R79117
  · exact R79119
  · exact R79121
  · exact R79123
  · exact R79125

theorem solution (m : ℕ) (hm : 0 < m) (hodd : Odd m) (hle : m ≤ 79126) :
    ∃ k : ℕ, syracuseStep^[k] m = 1 := by
  rcases Nat.lt_or_ge m 75126 with hlo | hlo
  · exact syracuse_reaches_one_below_75126 m hm hodd (by omega)
  obtain ⟨j, rfl⟩ : ∃ j, m = 2 * j + 1 := by obtain ⟨t, ht⟩ := hodd; exact ⟨t, by omega⟩
  rcases Nat.lt_or_ge j 38263 with h0 | h0
  · exact C0 j (by omega) (by omega)
  rcases Nat.lt_or_ge j 38963 with h1 | h1
  · exact C1 j (by omega) (by omega)
  exact C2 j (by omega) (by omega)
