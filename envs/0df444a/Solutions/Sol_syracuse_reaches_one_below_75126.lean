-- Prove2me | solution 1 for syracuse_reaches_one_below_75126
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T06:22:59.122703+00:00
-- url     : https://prove2.me/submissions/a63fb8cb-9589-4af1-a3cc-af4802e9e516

import Mathlib
import Definitions.Def_syracuseStep
import Theorems.Thm_syracuse_reaches_one_below_71125

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
theorem B (n : ℕ) (h1 : 0 < n) (h2 : Odd n) (h3 : n ≤ 71124) : Reach n :=
  syracuse_reaches_one_below_71125 n h1 h2 h3
theorem R163853 : Reach 163853 := rs (se 3 (by rfl) ⟨30722, by rfl⟩) (B 61445 (by norm_num) ⟨30722, by rfl⟩ (by norm_num))
theorem R163925 : Reach 163925 := rs (se 8 (by rfl) ⟨960, by rfl⟩) (B 1921 (by norm_num) ⟨960, by rfl⟩ (by norm_num))
theorem R163997 : Reach 163997 := rs (se 3 (by rfl) ⟨30749, by rfl⟩) (B 61499 (by norm_num) ⟨30749, by rfl⟩ (by norm_num))
theorem R196805 : Reach 196805 := rs (se 4 (by rfl) ⟨18450, by rfl⟩) (B 36901 (by norm_num) ⟨18450, by rfl⟩ (by norm_num))
theorem R164069 : Reach 164069 := rs (se 4 (by rfl) ⟨15381, by rfl⟩) (B 30763 (by norm_num) ⟨15381, by rfl⟩ (by norm_num))
theorem R164101 : Reach 164101 := rs (se 4 (by rfl) ⟨15384, by rfl⟩) (B 30769 (by norm_num) ⟨15384, by rfl⟩ (by norm_num))
theorem R164141 : Reach 164141 := rs (se 3 (by rfl) ⟨30776, by rfl⟩) (B 61553 (by norm_num) ⟨30776, by rfl⟩ (by norm_num))
theorem R327989 : Reach 327989 := rs (se 5 (by rfl) ⟨15374, by rfl⟩) (B 30749 (by norm_num) ⟨15374, by rfl⟩ (by norm_num))
theorem R360773 : Reach 360773 := rs (se 4 (by rfl) ⟨33822, by rfl⟩) (B 67645 (by norm_num) ⟨33822, by rfl⟩ (by norm_num))
theorem R164213 : Reach 164213 := rs (se 5 (by rfl) ⟨7697, by rfl⟩) (B 15395 (by norm_num) ⟨7697, by rfl⟩ (by norm_num))
theorem R393653 : Reach 393653 := rs (se 5 (by rfl) ⟨18452, by rfl⟩) (B 36905 (by norm_num) ⟨18452, by rfl⟩ (by norm_num))
theorem R164285 : Reach 164285 := rs (se 3 (by rfl) ⟨30803, by rfl⟩) (B 61607 (by norm_num) ⟨30803, by rfl⟩ (by norm_num))
theorem R164357 : Reach 164357 := rs (se 4 (by rfl) ⟨15408, by rfl⟩) (B 30817 (by norm_num) ⟨15408, by rfl⟩ (by norm_num))
theorem R164429 : Reach 164429 := rs (se 3 (by rfl) ⟨30830, by rfl⟩) (B 61661 (by norm_num) ⟨30830, by rfl⟩ (by norm_num))
theorem R164501 : Reach 164501 := rs (se 6 (by rfl) ⟨3855, by rfl⟩) (B 7711 (by norm_num) ⟨3855, by rfl⟩ (by norm_num))
theorem R131765 : Reach 131765 := rs (se 5 (by rfl) ⟨6176, by rfl⟩) (B 12353 (by norm_num) ⟨6176, by rfl⟩ (by norm_num))
theorem R164573 : Reach 164573 := rs (se 3 (by rfl) ⟨30857, by rfl⟩) (B 61715 (by norm_num) ⟨30857, by rfl⟩ (by norm_num))
theorem R164645 : Reach 164645 := rs (se 4 (by rfl) ⟨15435, by rfl⟩) (B 30871 (by norm_num) ⟨15435, by rfl⟩ (by norm_num))
theorem R164717 : Reach 164717 := rs (se 3 (by rfl) ⟨30884, by rfl⟩) (B 61769 (by norm_num) ⟨30884, by rfl⟩ (by norm_num))
theorem R164789 : Reach 164789 := rs (se 5 (by rfl) ⟨7724, by rfl⟩) (B 15449 (by norm_num) ⟨7724, by rfl⟩ (by norm_num))
theorem R164861 : Reach 164861 := rs (se 3 (by rfl) ⟨30911, by rfl⟩) (B 61823 (by norm_num) ⟨30911, by rfl⟩ (by norm_num))
theorem R164933 : Reach 164933 := rs (se 4 (by rfl) ⟨15462, by rfl⟩) (B 30925 (by norm_num) ⟨15462, by rfl⟩ (by norm_num))
theorem R165005 : Reach 165005 := rs (se 3 (by rfl) ⟨30938, by rfl⟩) (B 61877 (by norm_num) ⟨30938, by rfl⟩ (by norm_num))
theorem R132293 : Reach 132293 := rs (se 4 (by rfl) ⟨12402, by rfl⟩) (B 24805 (by norm_num) ⟨12402, by rfl⟩ (by norm_num))
theorem R459989 : Reach 459989 := rs (se 7 (by rfl) ⟨5390, by rfl⟩) (B 10781 (by norm_num) ⟨5390, by rfl⟩ (by norm_num))
theorem R165077 : Reach 165077 := rs (se 7 (by rfl) ⟨1934, by rfl⟩) (B 3869 (by norm_num) ⟨1934, by rfl⟩ (by norm_num))
theorem R165125 : Reach 165125 := rs (se 4 (by rfl) ⟨15480, by rfl⟩) (B 30961 (by norm_num) ⟨15480, by rfl⟩ (by norm_num))
theorem R165149 : Reach 165149 := rs (se 3 (by rfl) ⟨30965, by rfl⟩) (B 61931 (by norm_num) ⟨30965, by rfl⟩ (by norm_num))
theorem R296245 : Reach 296245 := rs (se 5 (by rfl) ⟨13886, by rfl⟩) (B 27773 (by norm_num) ⟨13886, by rfl⟩ (by norm_num))
theorem R165221 : Reach 165221 := rs (se 4 (by rfl) ⟨15489, by rfl⟩) (B 30979 (by norm_num) ⟨15489, by rfl⟩ (by norm_num))
theorem R230789 : Reach 230789 := rs (se 4 (by rfl) ⟨21636, by rfl⟩) (B 43273 (by norm_num) ⟨21636, by rfl⟩ (by norm_num))
theorem R99733 : Reach 99733 := rs (se 6 (by rfl) ⟨2337, by rfl⟩) (B 4675 (by norm_num) ⟨2337, by rfl⟩ (by norm_num))
theorem R165293 : Reach 165293 := rs (se 3 (by rfl) ⟨30992, by rfl⟩) (B 61985 (by norm_num) ⟨30992, by rfl⟩ (by norm_num))
theorem R99797 : Reach 99797 := rs (se 7 (by rfl) ⟨1169, by rfl⟩) (B 2339 (by norm_num) ⟨1169, by rfl⟩ (by norm_num))
theorem R165365 : Reach 165365 := rs (se 5 (by rfl) ⟨7751, by rfl⟩) (B 15503 (by norm_num) ⟨7751, by rfl⟩ (by norm_num))
theorem R165437 : Reach 165437 := rs (se 3 (by rfl) ⟨31019, by rfl⟩) (B 62039 (by norm_num) ⟨31019, by rfl⟩ (by norm_num))
theorem R362069 : Reach 362069 := rs (se 8 (by rfl) ⟨2121, by rfl⟩) (B 4243 (by norm_num) ⟨2121, by rfl⟩ (by norm_num))
theorem R99949 : Reach 99949 := rs (se 3 (by rfl) ⟨18740, by rfl⟩) (B 37481 (by norm_num) ⟨18740, by rfl⟩ (by norm_num))
theorem R165509 : Reach 165509 := rs (se 4 (by rfl) ⟨15516, by rfl⟩) (B 31033 (by norm_num) ⟨15516, by rfl⟩ (by norm_num))
theorem R165581 : Reach 165581 := rs (se 3 (by rfl) ⟨31046, by rfl⟩) (B 62093 (by norm_num) ⟨31046, by rfl⟩ (by norm_num))
theorem R165653 : Reach 165653 := rs (se 6 (by rfl) ⟨3882, by rfl⟩) (B 7765 (by norm_num) ⟨3882, by rfl⟩ (by norm_num))
theorem R165725 : Reach 165725 := rs (se 3 (by rfl) ⟨31073, by rfl⟩) (B 62147 (by norm_num) ⟨31073, by rfl⟩ (by norm_num))
theorem R165797 : Reach 165797 := rs (se 4 (by rfl) ⟨15543, by rfl⟩) (B 31087 (by norm_num) ⟨15543, by rfl⟩ (by norm_num))
theorem R165869 : Reach 165869 := rs (se 3 (by rfl) ⟨31100, by rfl⟩) (B 62201 (by norm_num) ⟨31100, by rfl⟩ (by norm_num))
theorem R165941 : Reach 165941 := rs (se 5 (by rfl) ⟨7778, by rfl⟩) (B 15557 (by norm_num) ⟨7778, by rfl⟩ (by norm_num))
theorem R166013 : Reach 166013 := rs (se 3 (by rfl) ⟨31127, by rfl⟩) (B 62255 (by norm_num) ⟨31127, by rfl⟩ (by norm_num))
theorem R166085 : Reach 166085 := rs (se 4 (by rfl) ⟨15570, by rfl⟩) (B 31141 (by norm_num) ⟨15570, by rfl⟩ (by norm_num))
theorem R100549 : Reach 100549 := rs (se 4 (by rfl) ⟨9426, by rfl⟩) (B 18853 (by norm_num) ⟨9426, by rfl⟩ (by norm_num))
theorem R133373 : Reach 133373 := rs (se 3 (by rfl) ⟨25007, by rfl⟩) (B 50015 (by norm_num) ⟨25007, by rfl⟩ (by norm_num))
theorem R166157 : Reach 166157 := rs (se 3 (by rfl) ⟨31154, by rfl⟩) (B 62309 (by norm_num) ⟨31154, by rfl⟩ (by norm_num))
theorem R166229 : Reach 166229 := rs (se 10 (by rfl) ⟨243, by rfl⟩) (B 487 (by norm_num) ⟨243, by rfl⟩ (by norm_num))
theorem R166301 : Reach 166301 := rs (se 3 (by rfl) ⟨31181, by rfl⟩) (B 62363 (by norm_num) ⟨31181, by rfl⟩ (by norm_num))
theorem R166373 : Reach 166373 := rs (se 4 (by rfl) ⟨15597, by rfl⟩) (B 31195 (by norm_num) ⟨15597, by rfl⟩ (by norm_num))
theorem R199205 : Reach 199205 := rs (se 4 (by rfl) ⟨18675, by rfl⟩) (B 37351 (by norm_num) ⟨18675, by rfl⟩ (by norm_num))
theorem R166445 : Reach 166445 := rs (se 3 (by rfl) ⟨31208, by rfl⟩) (B 62417 (by norm_num) ⟨31208, by rfl⟩ (by norm_num))
theorem R133741 : Reach 133741 := rs (se 3 (by rfl) ⟨25076, by rfl⟩) (B 50153 (by norm_num) ⟨25076, by rfl⟩ (by norm_num))
theorem R166517 : Reach 166517 := rs (se 5 (by rfl) ⟨7805, by rfl⟩) (B 15611 (by norm_num) ⟨7805, by rfl⟩ (by norm_num))
theorem R232085 : Reach 232085 := rs (se 6 (by rfl) ⟨5439, by rfl⟩) (B 10879 (by norm_num) ⟨5439, by rfl⟩ (by norm_num))
theorem R166589 : Reach 166589 := rs (se 3 (by rfl) ⟨31235, by rfl⟩) (B 62471 (by norm_num) ⟨31235, by rfl⟩ (by norm_num))
theorem R166661 : Reach 166661 := rs (se 4 (by rfl) ⟨15624, by rfl⟩) (B 31249 (by norm_num) ⟨15624, by rfl⟩ (by norm_num))
theorem R166733 : Reach 166733 := rs (se 3 (by rfl) ⟨31262, by rfl⟩) (B 62525 (by norm_num) ⟨31262, by rfl⟩ (by norm_num))
theorem R363365 : Reach 363365 := rs (se 4 (by rfl) ⟨34065, by rfl⟩) (B 68131 (by norm_num) ⟨34065, by rfl⟩ (by norm_num))
theorem R199541 : Reach 199541 := rs (se 5 (by rfl) ⟨9353, by rfl⟩) (B 18707 (by norm_num) ⟨9353, by rfl⟩ (by norm_num))
theorem R166805 : Reach 166805 := rs (se 6 (by rfl) ⟨3909, by rfl⟩) (B 7819 (by norm_num) ⟨3909, by rfl⟩ (by norm_num))
theorem R166877 : Reach 166877 := rs (se 3 (by rfl) ⟨31289, by rfl⟩) (B 62579 (by norm_num) ⟨31289, by rfl⟩ (by norm_num))
theorem R330725 : Reach 330725 := rs (se 4 (by rfl) ⟨31005, by rfl⟩) (B 62011 (by norm_num) ⟨31005, by rfl⟩ (by norm_num))
theorem R166949 : Reach 166949 := rs (se 4 (by rfl) ⟨15651, by rfl⟩) (B 31303 (by norm_num) ⟨15651, by rfl⟩ (by norm_num))
theorem R167021 : Reach 167021 := rs (se 3 (by rfl) ⟨31316, by rfl⟩) (B 62633 (by norm_num) ⟨31316, by rfl⟩ (by norm_num))
theorem R167093 : Reach 167093 := rs (se 5 (by rfl) ⟨7832, by rfl⟩) (B 15665 (by norm_num) ⟨7832, by rfl⟩ (by norm_num))
theorem R167165 : Reach 167165 := rs (se 3 (by rfl) ⟨31343, by rfl⟩) (B 62687 (by norm_num) ⟨31343, by rfl⟩ (by norm_num))
theorem R167237 : Reach 167237 := rs (se 4 (by rfl) ⟨15678, by rfl⟩) (B 31357 (by norm_num) ⟨15678, by rfl⟩ (by norm_num))
theorem R101741 : Reach 101741 := rs (se 3 (by rfl) ⟨19076, by rfl⟩) (B 38153 (by norm_num) ⟨19076, by rfl⟩ (by norm_num))
theorem R167309 : Reach 167309 := rs (se 3 (by rfl) ⟨31370, by rfl⟩) (B 62741 (by norm_num) ⟨31370, by rfl⟩ (by norm_num))
theorem R167381 : Reach 167381 := rs (se 7 (by rfl) ⟨1961, by rfl⟩) (B 3923 (by norm_num) ⟨1961, by rfl⟩ (by norm_num))
theorem R167453 : Reach 167453 := rs (se 3 (by rfl) ⟨31397, by rfl⟩) (B 62795 (by norm_num) ⟨31397, by rfl⟩ (by norm_num))
theorem R527957 : Reach 527957 := rs (se 8 (by rfl) ⟨3093, by rfl⟩) (B 6187 (by norm_num) ⟨3093, by rfl⟩ (by norm_num))
theorem R167525 : Reach 167525 := rs (se 4 (by rfl) ⟨15705, by rfl⟩) (B 31411 (by norm_num) ⟨15705, by rfl⟩ (by norm_num))
theorem R167597 : Reach 167597 := rs (se 3 (by rfl) ⟨31424, by rfl⟩) (B 62849 (by norm_num) ⟨31424, by rfl⟩ (by norm_num))
theorem R167669 : Reach 167669 := rs (se 5 (by rfl) ⟨7859, by rfl⟩) (B 15719 (by norm_num) ⟨7859, by rfl⟩ (by norm_num))
theorem R167741 : Reach 167741 := rs (se 3 (by rfl) ⟨31451, by rfl⟩) (B 62903 (by norm_num) ⟨31451, by rfl⟩ (by norm_num))
theorem R167813 : Reach 167813 := rs (se 4 (by rfl) ⟨15732, by rfl⟩) (B 31465 (by norm_num) ⟨15732, by rfl⟩ (by norm_num))
theorem R135101 : Reach 135101 := rs (se 3 (by rfl) ⟨25331, by rfl⟩) (B 50663 (by norm_num) ⟨25331, by rfl⟩ (by norm_num))
theorem R167885 : Reach 167885 := rs (se 3 (by rfl) ⟨31478, by rfl⟩) (B 62957 (by norm_num) ⟨31478, by rfl⟩ (by norm_num))
theorem R135125 : Reach 135125 := rs (se 7 (by rfl) ⟨1583, by rfl⟩) (B 3167 (by norm_num) ⟨1583, by rfl⟩ (by norm_num))
theorem R167957 : Reach 167957 := rs (se 6 (by rfl) ⟨3936, by rfl⟩) (B 7873 (by norm_num) ⟨3936, by rfl⟩ (by norm_num))
theorem R135245 : Reach 135245 := rs (se 3 (by rfl) ⟨25358, by rfl⟩) (B 50717 (by norm_num) ⟨25358, by rfl⟩ (by norm_num))
theorem R102493 : Reach 102493 := rs (se 3 (by rfl) ⟨19217, by rfl⟩) (B 38435 (by norm_num) ⟨19217, by rfl⟩ (by norm_num))
theorem R168029 : Reach 168029 := rs (se 3 (by rfl) ⟨31505, by rfl⟩) (B 63011 (by norm_num) ⟨31505, by rfl⟩ (by norm_num))
theorem R364661 : Reach 364661 := rs (se 5 (by rfl) ⟨17093, by rfl⟩) (B 34187 (by norm_num) ⟨17093, by rfl⟩ (by norm_num))
theorem R168101 : Reach 168101 := rs (se 4 (by rfl) ⟨15759, by rfl⟩) (B 31519 (by norm_num) ⟨15759, by rfl⟩ (by norm_num))
theorem R168173 : Reach 168173 := rs (se 3 (by rfl) ⟨31532, by rfl⟩) (B 63065 (by norm_num) ⟨31532, by rfl⟩ (by norm_num))
theorem R168245 : Reach 168245 := rs (se 5 (by rfl) ⟨7886, by rfl⟩) (B 15773 (by norm_num) ⟨7886, by rfl⟩ (by norm_num))
theorem R135533 : Reach 135533 := rs (se 3 (by rfl) ⟨25412, by rfl⟩) (B 50825 (by norm_num) ⟨25412, by rfl⟩ (by norm_num))
theorem R168317 : Reach 168317 := rs (se 3 (by rfl) ⟨31559, by rfl⟩) (B 63119 (by norm_num) ⟨31559, by rfl⟩ (by norm_num))
theorem R168389 : Reach 168389 := rs (se 4 (by rfl) ⟨15786, by rfl⟩) (B 31573 (by norm_num) ⟨15786, by rfl⟩ (by norm_num))
theorem R233941 : Reach 233941 := rs (se 7 (by rfl) ⟨2741, by rfl⟩) (B 5483 (by norm_num) ⟨2741, by rfl⟩ (by norm_num))
theorem R135685 : Reach 135685 := rs (se 4 (by rfl) ⟨12720, by rfl⟩) (B 25441 (by norm_num) ⟨12720, by rfl⟩ (by norm_num))
theorem R168461 : Reach 168461 := rs (se 3 (by rfl) ⟨31586, by rfl⟩) (B 63173 (by norm_num) ⟨31586, by rfl⟩ (by norm_num))
theorem R168517 : Reach 168517 := rs (se 4 (by rfl) ⟨15798, by rfl⟩) (B 31597 (by norm_num) ⟨15798, by rfl⟩ (by norm_num))
theorem R168533 : Reach 168533 := rs (se 8 (by rfl) ⟨987, by rfl⟩) (B 1975 (by norm_num) ⟨987, by rfl⟩ (by norm_num))
theorem R168605 : Reach 168605 := rs (se 3 (by rfl) ⟨31613, by rfl⟩) (B 63227 (by norm_num) ⟨31613, by rfl⟩ (by norm_num))
theorem R168677 : Reach 168677 := rs (se 4 (by rfl) ⟨15813, by rfl⟩) (B 31627 (by norm_num) ⟨15813, by rfl⟩ (by norm_num))
theorem R168749 : Reach 168749 := rs (se 3 (by rfl) ⟨31640, by rfl⟩) (B 63281 (by norm_num) ⟨31640, by rfl⟩ (by norm_num))
theorem R135989 : Reach 135989 := rs (se 5 (by rfl) ⟨6374, by rfl⟩) (B 12749 (by norm_num) ⟨6374, by rfl⟩ (by norm_num))
theorem R201541 : Reach 201541 := rs (se 4 (by rfl) ⟨18894, by rfl⟩) (B 37789 (by norm_num) ⟨18894, by rfl⟩ (by norm_num))
theorem R136037 : Reach 136037 := rs (se 4 (by rfl) ⟨12753, by rfl⟩) (B 25507 (by norm_num) ⟨12753, by rfl⟩ (by norm_num))
theorem R103285 : Reach 103285 := rs (se 5 (by rfl) ⟨4841, by rfl⟩) (B 9683 (by norm_num) ⟨4841, by rfl⟩ (by norm_num))
theorem R168821 : Reach 168821 := rs (se 5 (by rfl) ⟨7913, by rfl⟩) (B 15827 (by norm_num) ⟨7913, by rfl⟩ (by norm_num))
theorem R168893 : Reach 168893 := rs (se 3 (by rfl) ⟨31667, by rfl⟩) (B 63335 (by norm_num) ⟨31667, by rfl⟩ (by norm_num))
theorem R267221 : Reach 267221 := rs (se 7 (by rfl) ⟨3131, by rfl⟩) (B 6263 (by norm_num) ⟨3131, by rfl⟩ (by norm_num))
theorem R168965 : Reach 168965 := rs (se 4 (by rfl) ⟨15840, by rfl⟩) (B 31681 (by norm_num) ⟨15840, by rfl⟩ (by norm_num))
theorem R103621 : Reach 103621 := rs (se 4 (by rfl) ⟨9714, by rfl⟩) (B 19429 (by norm_num) ⟨9714, by rfl⟩ (by norm_num))
theorem R267509 : Reach 267509 := rs (se 5 (by rfl) ⟨12539, by rfl⟩) (B 25079 (by norm_num) ⟨12539, by rfl⟩ (by norm_num))
theorem R365957 : Reach 365957 := rs (se 4 (by rfl) ⟨34308, by rfl⟩) (B 68617 (by norm_num) ⟨34308, by rfl⟩ (by norm_num))
theorem R103837 : Reach 103837 := rs (se 3 (by rfl) ⟨19469, by rfl⟩) (B 38939 (by norm_num) ⟨19469, by rfl⟩ (by norm_num))
theorem R71125 : Reach 71125 := rs (se 7 (by rfl) ⟨833, by rfl⟩) (B 1667 (by norm_num) ⟨833, by rfl⟩ (by norm_num))
theorem R71129 : Reach 71129 := rs (se 2 (by rfl) ⟨26673, by rfl⟩) (B 53347 (by norm_num) ⟨26673, by rfl⟩ (by norm_num))
theorem R71133 : Reach 71133 := rs (se 3 (by rfl) ⟨13337, by rfl⟩) (B 26675 (by norm_num) ⟨13337, by rfl⟩ (by norm_num))
theorem R71137 : Reach 71137 := rs (se 2 (by rfl) ⟨26676, by rfl⟩) (B 53353 (by norm_num) ⟨26676, by rfl⟩ (by norm_num))
theorem R71141 : Reach 71141 := rs (se 4 (by rfl) ⟨6669, by rfl⟩) (B 13339 (by norm_num) ⟨6669, by rfl⟩ (by norm_num))
theorem R71145 : Reach 71145 := rs (se 2 (by rfl) ⟨26679, by rfl⟩) (B 53359 (by norm_num) ⟨26679, by rfl⟩ (by norm_num))
theorem R71149 : Reach 71149 := rs (se 3 (by rfl) ⟨13340, by rfl⟩) (B 26681 (by norm_num) ⟨13340, by rfl⟩ (by norm_num))
theorem R71153 : Reach 71153 := rs (se 2 (by rfl) ⟨26682, by rfl⟩) (B 53365 (by norm_num) ⟨26682, by rfl⟩ (by norm_num))
theorem R71157 : Reach 71157 := rs (se 5 (by rfl) ⟨3335, by rfl⟩) (B 6671 (by norm_num) ⟨3335, by rfl⟩ (by norm_num))
theorem R71161 : Reach 71161 := rs (se 2 (by rfl) ⟨26685, by rfl⟩) (B 53371 (by norm_num) ⟨26685, by rfl⟩ (by norm_num))
theorem R71165 : Reach 71165 := rs (se 3 (by rfl) ⟨13343, by rfl⟩) (B 26687 (by norm_num) ⟨13343, by rfl⟩ (by norm_num))
theorem R71169 : Reach 71169 := rs (se 2 (by rfl) ⟨26688, by rfl⟩) (B 53377 (by norm_num) ⟨26688, by rfl⟩ (by norm_num))
theorem R71173 : Reach 71173 := rs (se 4 (by rfl) ⟨6672, by rfl⟩) (B 13345 (by norm_num) ⟨6672, by rfl⟩ (by norm_num))
theorem R71177 : Reach 71177 := rs (se 2 (by rfl) ⟨26691, by rfl⟩) (B 53383 (by norm_num) ⟨26691, by rfl⟩ (by norm_num))
theorem R71181 : Reach 71181 := rs (se 3 (by rfl) ⟨13346, by rfl⟩) (B 26693 (by norm_num) ⟨13346, by rfl⟩ (by norm_num))
theorem R71185 : Reach 71185 := rs (se 2 (by rfl) ⟨26694, by rfl⟩) (B 53389 (by norm_num) ⟨26694, by rfl⟩ (by norm_num))
theorem R71189 : Reach 71189 := rs (se 6 (by rfl) ⟨1668, by rfl⟩) (B 3337 (by norm_num) ⟨1668, by rfl⟩ (by norm_num))
theorem R71193 : Reach 71193 := rs (se 2 (by rfl) ⟨26697, by rfl⟩) (B 53395 (by norm_num) ⟨26697, by rfl⟩ (by norm_num))
theorem R71197 : Reach 71197 := rs (se 3 (by rfl) ⟨13349, by rfl⟩) (B 26699 (by norm_num) ⟨13349, by rfl⟩ (by norm_num))
theorem R71201 : Reach 71201 := rs (se 2 (by rfl) ⟨26700, by rfl⟩) (B 53401 (by norm_num) ⟨26700, by rfl⟩ (by norm_num))
theorem R71205 : Reach 71205 := rs (se 4 (by rfl) ⟨6675, by rfl⟩) (B 13351 (by norm_num) ⟨6675, by rfl⟩ (by norm_num))
theorem R136741 : Reach 136741 := rs (se 4 (by rfl) ⟨12819, by rfl⟩) (B 25639 (by norm_num) ⟨12819, by rfl⟩ (by norm_num))
theorem R71209 : Reach 71209 := rs (se 2 (by rfl) ⟨26703, by rfl⟩) (B 53407 (by norm_num) ⟨26703, by rfl⟩ (by norm_num))
theorem R71213 : Reach 71213 := rs (se 3 (by rfl) ⟨13352, by rfl⟩) (B 26705 (by norm_num) ⟨13352, by rfl⟩ (by norm_num))
theorem R71217 : Reach 71217 := rs (se 2 (by rfl) ⟨26706, by rfl⟩) (B 53413 (by norm_num) ⟨26706, by rfl⟩ (by norm_num))
theorem R71221 : Reach 71221 := rs (se 5 (by rfl) ⟨3338, by rfl⟩) (B 6677 (by norm_num) ⟨3338, by rfl⟩ (by norm_num))
theorem R71225 : Reach 71225 := rs (se 2 (by rfl) ⟨26709, by rfl⟩) (B 53419 (by norm_num) ⟨26709, by rfl⟩ (by norm_num))
theorem R71229 : Reach 71229 := rs (se 3 (by rfl) ⟨13355, by rfl⟩) (B 26711 (by norm_num) ⟨13355, by rfl⟩ (by norm_num))
theorem R71233 : Reach 71233 := rs (se 2 (by rfl) ⟨26712, by rfl⟩) (B 53425 (by norm_num) ⟨26712, by rfl⟩ (by norm_num))
theorem R71237 : Reach 71237 := rs (se 4 (by rfl) ⟨6678, by rfl⟩) (B 13357 (by norm_num) ⟨6678, by rfl⟩ (by norm_num))
theorem R71241 : Reach 71241 := rs (se 2 (by rfl) ⟨26715, by rfl⟩) (B 53431 (by norm_num) ⟨26715, by rfl⟩ (by norm_num))
theorem R71245 : Reach 71245 := rs (se 3 (by rfl) ⟨13358, by rfl⟩) (B 26717 (by norm_num) ⟨13358, by rfl⟩ (by norm_num))
theorem R71249 : Reach 71249 := rs (se 2 (by rfl) ⟨26718, by rfl⟩) (B 53437 (by norm_num) ⟨26718, by rfl⟩ (by norm_num))
theorem R71253 : Reach 71253 := rs (se 8 (by rfl) ⟨417, by rfl⟩) (B 835 (by norm_num) ⟨417, by rfl⟩ (by norm_num))
theorem R71257 : Reach 71257 := rs (se 2 (by rfl) ⟨26721, by rfl⟩) (B 53443 (by norm_num) ⟨26721, by rfl⟩ (by norm_num))
theorem R71261 : Reach 71261 := rs (se 3 (by rfl) ⟨13361, by rfl⟩) (B 26723 (by norm_num) ⟨13361, by rfl⟩ (by norm_num))
theorem R71265 : Reach 71265 := rs (se 2 (by rfl) ⟨26724, by rfl⟩) (B 53449 (by norm_num) ⟨26724, by rfl⟩ (by norm_num))
theorem R71269 : Reach 71269 := rs (se 4 (by rfl) ⟨6681, by rfl⟩) (B 13363 (by norm_num) ⟨6681, by rfl⟩ (by norm_num))
theorem R71273 : Reach 71273 := rs (se 2 (by rfl) ⟨26727, by rfl⟩) (B 53455 (by norm_num) ⟨26727, by rfl⟩ (by norm_num))
theorem R71277 : Reach 71277 := rs (se 3 (by rfl) ⟨13364, by rfl⟩) (B 26729 (by norm_num) ⟨13364, by rfl⟩ (by norm_num))
theorem R71281 : Reach 71281 := rs (se 2 (by rfl) ⟨26730, by rfl⟩) (B 53461 (by norm_num) ⟨26730, by rfl⟩ (by norm_num))
theorem R71285 : Reach 71285 := rs (se 5 (by rfl) ⟨3341, by rfl⟩) (B 6683 (by norm_num) ⟨3341, by rfl⟩ (by norm_num))
theorem R71289 : Reach 71289 := rs (se 2 (by rfl) ⟨26733, by rfl⟩) (B 53467 (by norm_num) ⟨26733, by rfl⟩ (by norm_num))
theorem R71293 : Reach 71293 := rs (se 3 (by rfl) ⟨13367, by rfl⟩) (B 26735 (by norm_num) ⟨13367, by rfl⟩ (by norm_num))
theorem R71297 : Reach 71297 := rs (se 2 (by rfl) ⟨26736, by rfl⟩) (B 53473 (by norm_num) ⟨26736, by rfl⟩ (by norm_num))
theorem R71301 : Reach 71301 := rs (se 4 (by rfl) ⟨6684, by rfl⟩) (B 13369 (by norm_num) ⟨6684, by rfl⟩ (by norm_num))
theorem R71305 : Reach 71305 := rs (se 2 (by rfl) ⟨26739, by rfl⟩) (B 53479 (by norm_num) ⟨26739, by rfl⟩ (by norm_num))
theorem R71309 : Reach 71309 := rs (se 3 (by rfl) ⟨13370, by rfl⟩) (B 26741 (by norm_num) ⟨13370, by rfl⟩ (by norm_num))
theorem R71313 : Reach 71313 := rs (se 2 (by rfl) ⟨26742, by rfl⟩) (B 53485 (by norm_num) ⟨26742, by rfl⟩ (by norm_num))
theorem R71317 : Reach 71317 := rs (se 6 (by rfl) ⟨1671, by rfl⟩) (B 3343 (by norm_num) ⟨1671, by rfl⟩ (by norm_num))
theorem R71321 : Reach 71321 := rs (se 2 (by rfl) ⟨26745, by rfl⟩) (B 53491 (by norm_num) ⟨26745, by rfl⟩ (by norm_num))
theorem R71325 : Reach 71325 := rs (se 3 (by rfl) ⟨13373, by rfl⟩) (B 26747 (by norm_num) ⟨13373, by rfl⟩ (by norm_num))
theorem R71329 : Reach 71329 := rs (se 2 (by rfl) ⟨26748, by rfl⟩) (B 53497 (by norm_num) ⟨26748, by rfl⟩ (by norm_num))
theorem R71333 : Reach 71333 := rs (se 4 (by rfl) ⟨6687, by rfl⟩) (B 13375 (by norm_num) ⟨6687, by rfl⟩ (by norm_num))
theorem R202405 : Reach 202405 := rs (se 4 (by rfl) ⟨18975, by rfl⟩) (B 37951 (by norm_num) ⟨18975, by rfl⟩ (by norm_num))
theorem R71337 : Reach 71337 := rs (se 2 (by rfl) ⟨26751, by rfl⟩) (B 53503 (by norm_num) ⟨26751, by rfl⟩ (by norm_num))
theorem R71341 : Reach 71341 := rs (se 3 (by rfl) ⟨13376, by rfl⟩) (B 26753 (by norm_num) ⟨13376, by rfl⟩ (by norm_num))
theorem R71345 : Reach 71345 := rs (se 2 (by rfl) ⟨26754, by rfl⟩) (B 53509 (by norm_num) ⟨26754, by rfl⟩ (by norm_num))
theorem R71349 : Reach 71349 := rs (se 5 (by rfl) ⟨3344, by rfl⟩) (B 6689 (by norm_num) ⟨3344, by rfl⟩ (by norm_num))
theorem R136885 : Reach 136885 := rs (se 5 (by rfl) ⟨6416, by rfl⟩) (B 12833 (by norm_num) ⟨6416, by rfl⟩ (by norm_num))
theorem R71353 : Reach 71353 := rs (se 2 (by rfl) ⟨26757, by rfl⟩) (B 53515 (by norm_num) ⟨26757, by rfl⟩ (by norm_num))
theorem R71357 : Reach 71357 := rs (se 3 (by rfl) ⟨13379, by rfl⟩) (B 26759 (by norm_num) ⟨13379, by rfl⟩ (by norm_num))
theorem R71361 : Reach 71361 := rs (se 2 (by rfl) ⟨26760, by rfl⟩) (B 53521 (by norm_num) ⟨26760, by rfl⟩ (by norm_num))
theorem R71365 : Reach 71365 := rs (se 4 (by rfl) ⟨6690, by rfl⟩) (B 13381 (by norm_num) ⟨6690, by rfl⟩ (by norm_num))
theorem R366277 : Reach 366277 := rs (se 4 (by rfl) ⟨34338, by rfl⟩) (B 68677 (by norm_num) ⟨34338, by rfl⟩ (by norm_num))
theorem R71369 : Reach 71369 := rs (se 2 (by rfl) ⟨26763, by rfl⟩) (B 53527 (by norm_num) ⟨26763, by rfl⟩ (by norm_num))
theorem R71373 : Reach 71373 := rs (se 3 (by rfl) ⟨13382, by rfl⟩) (B 26765 (by norm_num) ⟨13382, by rfl⟩ (by norm_num))
theorem R71377 : Reach 71377 := rs (se 2 (by rfl) ⟨26766, by rfl⟩) (B 53533 (by norm_num) ⟨26766, by rfl⟩ (by norm_num))
theorem R71381 : Reach 71381 := rs (se 7 (by rfl) ⟨836, by rfl⟩) (B 1673 (by norm_num) ⟨836, by rfl⟩ (by norm_num))
theorem R71385 : Reach 71385 := rs (se 2 (by rfl) ⟨26769, by rfl⟩) (B 53539 (by norm_num) ⟨26769, by rfl⟩ (by norm_num))
theorem R71389 : Reach 71389 := rs (se 3 (by rfl) ⟨13385, by rfl⟩) (B 26771 (by norm_num) ⟨13385, by rfl⟩ (by norm_num))
theorem R71393 : Reach 71393 := rs (se 2 (by rfl) ⟨26772, by rfl⟩) (B 53545 (by norm_num) ⟨26772, by rfl⟩ (by norm_num))
theorem R71397 : Reach 71397 := rs (se 4 (by rfl) ⟨6693, by rfl⟩) (B 13387 (by norm_num) ⟨6693, by rfl⟩ (by norm_num))
theorem R71401 : Reach 71401 := rs (se 2 (by rfl) ⟨26775, by rfl⟩) (B 53551 (by norm_num) ⟨26775, by rfl⟩ (by norm_num))
theorem R71405 : Reach 71405 := rs (se 3 (by rfl) ⟨13388, by rfl⟩) (B 26777 (by norm_num) ⟨13388, by rfl⟩ (by norm_num))
theorem R71409 : Reach 71409 := rs (se 2 (by rfl) ⟨26778, by rfl⟩) (B 53557 (by norm_num) ⟨26778, by rfl⟩ (by norm_num))
theorem R71413 : Reach 71413 := rs (se 5 (by rfl) ⟨3347, by rfl⟩) (B 6695 (by norm_num) ⟨3347, by rfl⟩ (by norm_num))
theorem R71417 : Reach 71417 := rs (se 2 (by rfl) ⟨26781, by rfl⟩) (B 53563 (by norm_num) ⟨26781, by rfl⟩ (by norm_num))
theorem R71421 : Reach 71421 := rs (se 3 (by rfl) ⟨13391, by rfl⟩) (B 26783 (by norm_num) ⟨13391, by rfl⟩ (by norm_num))
theorem R71425 : Reach 71425 := rs (se 2 (by rfl) ⟨26784, by rfl⟩) (B 53569 (by norm_num) ⟨26784, by rfl⟩ (by norm_num))
theorem R71429 : Reach 71429 := rs (se 4 (by rfl) ⟨6696, by rfl⟩) (B 13393 (by norm_num) ⟨6696, by rfl⟩ (by norm_num))
theorem R71433 : Reach 71433 := rs (se 2 (by rfl) ⟨26787, by rfl⟩) (B 53575 (by norm_num) ⟨26787, by rfl⟩ (by norm_num))
theorem R71437 : Reach 71437 := rs (se 3 (by rfl) ⟨13394, by rfl⟩) (B 26789 (by norm_num) ⟨13394, by rfl⟩ (by norm_num))
theorem R71441 : Reach 71441 := rs (se 2 (by rfl) ⟨26790, by rfl⟩) (B 53581 (by norm_num) ⟨26790, by rfl⟩ (by norm_num))
theorem R71445 : Reach 71445 := rs (se 6 (by rfl) ⟨1674, by rfl⟩) (B 3349 (by norm_num) ⟨1674, by rfl⟩ (by norm_num))
theorem R104213 : Reach 104213 := rs (se 6 (by rfl) ⟨2442, by rfl⟩) (B 4885 (by norm_num) ⟨2442, by rfl⟩ (by norm_num))
theorem R71449 : Reach 71449 := rs (se 2 (by rfl) ⟨26793, by rfl⟩) (B 53587 (by norm_num) ⟨26793, by rfl⟩ (by norm_num))
theorem R71453 : Reach 71453 := rs (se 3 (by rfl) ⟨13397, by rfl⟩) (B 26795 (by norm_num) ⟨13397, by rfl⟩ (by norm_num))
theorem R71457 : Reach 71457 := rs (se 2 (by rfl) ⟨26796, by rfl⟩) (B 53593 (by norm_num) ⟨26796, by rfl⟩ (by norm_num))
theorem R71461 : Reach 71461 := rs (se 4 (by rfl) ⟨6699, by rfl⟩) (B 13399 (by norm_num) ⟨6699, by rfl⟩ (by norm_num))
theorem R71465 : Reach 71465 := rs (se 2 (by rfl) ⟨26799, by rfl⟩) (B 53599 (by norm_num) ⟨26799, by rfl⟩ (by norm_num))
theorem R71469 : Reach 71469 := rs (se 3 (by rfl) ⟨13400, by rfl⟩) (B 26801 (by norm_num) ⟨13400, by rfl⟩ (by norm_num))
theorem R71473 : Reach 71473 := rs (se 2 (by rfl) ⟨26802, by rfl⟩) (B 53605 (by norm_num) ⟨26802, by rfl⟩ (by norm_num))
theorem R71477 : Reach 71477 := rs (se 5 (by rfl) ⟨3350, by rfl⟩) (B 6701 (by norm_num) ⟨3350, by rfl⟩ (by norm_num))
theorem R71481 : Reach 71481 := rs (se 2 (by rfl) ⟨26805, by rfl⟩) (B 53611 (by norm_num) ⟨26805, by rfl⟩ (by norm_num))
theorem R71485 : Reach 71485 := rs (se 3 (by rfl) ⟨13403, by rfl⟩) (B 26807 (by norm_num) ⟨13403, by rfl⟩ (by norm_num))
theorem R71489 : Reach 71489 := rs (se 2 (by rfl) ⟨26808, by rfl⟩) (B 53617 (by norm_num) ⟨26808, by rfl⟩ (by norm_num))
theorem R71493 : Reach 71493 := rs (se 4 (by rfl) ⟨6702, by rfl⟩) (B 13405 (by norm_num) ⟨6702, by rfl⟩ (by norm_num))
theorem R71497 : Reach 71497 := rs (se 2 (by rfl) ⟨26811, by rfl⟩) (B 53623 (by norm_num) ⟨26811, by rfl⟩ (by norm_num))
theorem R71501 : Reach 71501 := rs (se 3 (by rfl) ⟨13406, by rfl⟩) (B 26813 (by norm_num) ⟨13406, by rfl⟩ (by norm_num))
theorem R71505 : Reach 71505 := rs (se 2 (by rfl) ⟨26814, by rfl⟩) (B 53629 (by norm_num) ⟨26814, by rfl⟩ (by norm_num))
theorem R71509 : Reach 71509 := rs (se 9 (by rfl) ⟨209, by rfl⟩) (B 419 (by norm_num) ⟨209, by rfl⟩ (by norm_num))
theorem R137045 : Reach 137045 := rs (se 9 (by rfl) ⟨401, by rfl⟩) (B 803 (by norm_num) ⟨401, by rfl⟩ (by norm_num))
theorem R71513 : Reach 71513 := rs (se 2 (by rfl) ⟨26817, by rfl⟩) (B 53635 (by norm_num) ⟨26817, by rfl⟩ (by norm_num))
theorem R71517 : Reach 71517 := rs (se 3 (by rfl) ⟨13409, by rfl⟩) (B 26819 (by norm_num) ⟨13409, by rfl⟩ (by norm_num))
theorem R71521 : Reach 71521 := rs (se 2 (by rfl) ⟨26820, by rfl⟩) (B 53641 (by norm_num) ⟨26820, by rfl⟩ (by norm_num))
theorem R71525 : Reach 71525 := rs (se 4 (by rfl) ⟨6705, by rfl⟩) (B 13411 (by norm_num) ⟨6705, by rfl⟩ (by norm_num))
theorem R71529 : Reach 71529 := rs (se 2 (by rfl) ⟨26823, by rfl⟩) (B 53647 (by norm_num) ⟨26823, by rfl⟩ (by norm_num))
theorem R71533 : Reach 71533 := rs (se 3 (by rfl) ⟨13412, by rfl⟩) (B 26825 (by norm_num) ⟨13412, by rfl⟩ (by norm_num))
theorem R71537 : Reach 71537 := rs (se 2 (by rfl) ⟨26826, by rfl⟩) (B 53653 (by norm_num) ⟨26826, by rfl⟩ (by norm_num))
theorem R71541 : Reach 71541 := rs (se 5 (by rfl) ⟨3353, by rfl⟩) (B 6707 (by norm_num) ⟨3353, by rfl⟩ (by norm_num))
theorem R71545 : Reach 71545 := rs (se 2 (by rfl) ⟨26829, by rfl⟩) (B 53659 (by norm_num) ⟨26829, by rfl⟩ (by norm_num))
theorem R71549 : Reach 71549 := rs (se 3 (by rfl) ⟨13415, by rfl⟩) (B 26831 (by norm_num) ⟨13415, by rfl⟩ (by norm_num))
theorem R71553 : Reach 71553 := rs (se 2 (by rfl) ⟨26832, by rfl⟩) (B 53665 (by norm_num) ⟨26832, by rfl⟩ (by norm_num))
theorem R71557 : Reach 71557 := rs (se 4 (by rfl) ⟨6708, by rfl⟩) (B 13417 (by norm_num) ⟨6708, by rfl⟩ (by norm_num))
theorem R71561 : Reach 71561 := rs (se 2 (by rfl) ⟨26835, by rfl⟩) (B 53671 (by norm_num) ⟨26835, by rfl⟩ (by norm_num))
theorem R71565 : Reach 71565 := rs (se 3 (by rfl) ⟨13418, by rfl⟩) (B 26837 (by norm_num) ⟨13418, by rfl⟩ (by norm_num))
theorem R71569 : Reach 71569 := rs (se 2 (by rfl) ⟨26838, by rfl⟩) (B 53677 (by norm_num) ⟨26838, by rfl⟩ (by norm_num))
theorem R71573 : Reach 71573 := rs (se 6 (by rfl) ⟨1677, by rfl⟩) (B 3355 (by norm_num) ⟨1677, by rfl⟩ (by norm_num))
theorem R71577 : Reach 71577 := rs (se 2 (by rfl) ⟨26841, by rfl⟩) (B 53683 (by norm_num) ⟨26841, by rfl⟩ (by norm_num))
theorem R71581 : Reach 71581 := rs (se 3 (by rfl) ⟨13421, by rfl⟩) (B 26843 (by norm_num) ⟨13421, by rfl⟩ (by norm_num))
theorem R71585 : Reach 71585 := rs (se 2 (by rfl) ⟨26844, by rfl⟩) (B 53689 (by norm_num) ⟨26844, by rfl⟩ (by norm_num))
theorem R71589 : Reach 71589 := rs (se 4 (by rfl) ⟨6711, by rfl⟩) (B 13423 (by norm_num) ⟨6711, by rfl⟩ (by norm_num))
theorem R71593 : Reach 71593 := rs (se 2 (by rfl) ⟨26847, by rfl⟩) (B 53695 (by norm_num) ⟨26847, by rfl⟩ (by norm_num))
theorem R71597 : Reach 71597 := rs (se 3 (by rfl) ⟨13424, by rfl⟩) (B 26849 (by norm_num) ⟨13424, by rfl⟩ (by norm_num))
theorem R71601 : Reach 71601 := rs (se 2 (by rfl) ⟨26850, by rfl⟩) (B 53701 (by norm_num) ⟨26850, by rfl⟩ (by norm_num))
theorem R71605 : Reach 71605 := rs (se 5 (by rfl) ⟨3356, by rfl⟩) (B 6713 (by norm_num) ⟨3356, by rfl⟩ (by norm_num))
theorem R71609 : Reach 71609 := rs (se 2 (by rfl) ⟨26853, by rfl⟩) (B 53707 (by norm_num) ⟨26853, by rfl⟩ (by norm_num))
theorem R71613 : Reach 71613 := rs (se 3 (by rfl) ⟨13427, by rfl⟩) (B 26855 (by norm_num) ⟨13427, by rfl⟩ (by norm_num))
theorem R71617 : Reach 71617 := rs (se 2 (by rfl) ⟨26856, by rfl⟩) (B 53713 (by norm_num) ⟨26856, by rfl⟩ (by norm_num))
theorem R71621 : Reach 71621 := rs (se 4 (by rfl) ⟨6714, by rfl⟩) (B 13429 (by norm_num) ⟨6714, by rfl⟩ (by norm_num))
theorem R71625 : Reach 71625 := rs (se 2 (by rfl) ⟨26859, by rfl⟩) (B 53719 (by norm_num) ⟨26859, by rfl⟩ (by norm_num))
theorem R71629 : Reach 71629 := rs (se 3 (by rfl) ⟨13430, by rfl⟩) (B 26861 (by norm_num) ⟨13430, by rfl⟩ (by norm_num))
theorem R71633 : Reach 71633 := rs (se 2 (by rfl) ⟨26862, by rfl⟩) (B 53725 (by norm_num) ⟨26862, by rfl⟩ (by norm_num))
theorem R71637 : Reach 71637 := rs (se 7 (by rfl) ⟨839, by rfl⟩) (B 1679 (by norm_num) ⟨839, by rfl⟩ (by norm_num))
theorem R71641 : Reach 71641 := rs (se 2 (by rfl) ⟨26865, by rfl⟩) (B 53731 (by norm_num) ⟨26865, by rfl⟩ (by norm_num))
theorem R71645 : Reach 71645 := rs (se 3 (by rfl) ⟨13433, by rfl⟩) (B 26867 (by norm_num) ⟨13433, by rfl⟩ (by norm_num))
theorem R71649 : Reach 71649 := rs (se 2 (by rfl) ⟨26868, by rfl⟩) (B 53737 (by norm_num) ⟨26868, by rfl⟩ (by norm_num))
theorem R71653 : Reach 71653 := rs (se 4 (by rfl) ⟨6717, by rfl⟩) (B 13435 (by norm_num) ⟨6717, by rfl⟩ (by norm_num))
theorem R137189 : Reach 137189 := rs (se 4 (by rfl) ⟨12861, by rfl⟩) (B 25723 (by norm_num) ⟨12861, by rfl⟩ (by norm_num))
theorem R71657 : Reach 71657 := rs (se 2 (by rfl) ⟨26871, by rfl⟩) (B 53743 (by norm_num) ⟨26871, by rfl⟩ (by norm_num))
theorem R71661 : Reach 71661 := rs (se 3 (by rfl) ⟨13436, by rfl⟩) (B 26873 (by norm_num) ⟨13436, by rfl⟩ (by norm_num))
theorem R71665 : Reach 71665 := rs (se 2 (by rfl) ⟨26874, by rfl⟩) (B 53749 (by norm_num) ⟨26874, by rfl⟩ (by norm_num))
theorem R71669 : Reach 71669 := rs (se 5 (by rfl) ⟨3359, by rfl⟩) (B 6719 (by norm_num) ⟨3359, by rfl⟩ (by norm_num))
theorem R71673 : Reach 71673 := rs (se 2 (by rfl) ⟨26877, by rfl⟩) (B 53755 (by norm_num) ⟨26877, by rfl⟩ (by norm_num))
theorem R71677 : Reach 71677 := rs (se 3 (by rfl) ⟨13439, by rfl⟩) (B 26879 (by norm_num) ⟨13439, by rfl⟩ (by norm_num))
theorem R71681 : Reach 71681 := rs (se 2 (by rfl) ⟨26880, by rfl⟩) (B 53761 (by norm_num) ⟨26880, by rfl⟩ (by norm_num))
theorem R71685 : Reach 71685 := rs (se 4 (by rfl) ⟨6720, by rfl⟩) (B 13441 (by norm_num) ⟨6720, by rfl⟩ (by norm_num))
theorem R71689 : Reach 71689 := rs (se 2 (by rfl) ⟨26883, by rfl⟩) (B 53767 (by norm_num) ⟨26883, by rfl⟩ (by norm_num))
theorem R71693 : Reach 71693 := rs (se 3 (by rfl) ⟨13442, by rfl⟩) (B 26885 (by norm_num) ⟨13442, by rfl⟩ (by norm_num))
theorem R71697 : Reach 71697 := rs (se 2 (by rfl) ⟨26886, by rfl⟩) (B 53773 (by norm_num) ⟨26886, by rfl⟩ (by norm_num))
theorem R71701 : Reach 71701 := rs (se 6 (by rfl) ⟨1680, by rfl⟩) (B 3361 (by norm_num) ⟨1680, by rfl⟩ (by norm_num))
theorem R71705 : Reach 71705 := rs (se 2 (by rfl) ⟨26889, by rfl⟩) (B 53779 (by norm_num) ⟨26889, by rfl⟩ (by norm_num))
theorem R71709 : Reach 71709 := rs (se 3 (by rfl) ⟨13445, by rfl⟩) (B 26891 (by norm_num) ⟨13445, by rfl⟩ (by norm_num))
theorem R71713 : Reach 71713 := rs (se 2 (by rfl) ⟨26892, by rfl⟩) (B 53785 (by norm_num) ⟨26892, by rfl⟩ (by norm_num))
theorem R71717 : Reach 71717 := rs (se 4 (by rfl) ⟨6723, by rfl⟩) (B 13447 (by norm_num) ⟨6723, by rfl⟩ (by norm_num))
theorem R71721 : Reach 71721 := rs (se 2 (by rfl) ⟨26895, by rfl⟩) (B 53791 (by norm_num) ⟨26895, by rfl⟩ (by norm_num))
theorem R71725 : Reach 71725 := rs (se 3 (by rfl) ⟨13448, by rfl⟩) (B 26897 (by norm_num) ⟨13448, by rfl⟩ (by norm_num))
theorem R71729 : Reach 71729 := rs (se 2 (by rfl) ⟨26898, by rfl⟩) (B 53797 (by norm_num) ⟨26898, by rfl⟩ (by norm_num))
theorem R71733 : Reach 71733 := rs (se 5 (by rfl) ⟨3362, by rfl⟩) (B 6725 (by norm_num) ⟨3362, by rfl⟩ (by norm_num))
theorem R71737 : Reach 71737 := rs (se 2 (by rfl) ⟨26901, by rfl⟩) (B 53803 (by norm_num) ⟨26901, by rfl⟩ (by norm_num))
theorem R71741 : Reach 71741 := rs (se 3 (by rfl) ⟨13451, by rfl⟩) (B 26903 (by norm_num) ⟨13451, by rfl⟩ (by norm_num))
theorem R71745 : Reach 71745 := rs (se 2 (by rfl) ⟨26904, by rfl⟩) (B 53809 (by norm_num) ⟨26904, by rfl⟩ (by norm_num))
theorem R71749 : Reach 71749 := rs (se 4 (by rfl) ⟨6726, by rfl⟩) (B 13453 (by norm_num) ⟨6726, by rfl⟩ (by norm_num))
theorem R71753 : Reach 71753 := rs (se 2 (by rfl) ⟨26907, by rfl⟩) (B 53815 (by norm_num) ⟨26907, by rfl⟩ (by norm_num))
theorem R71757 : Reach 71757 := rs (se 3 (by rfl) ⟨13454, by rfl⟩) (B 26909 (by norm_num) ⟨13454, by rfl⟩ (by norm_num))
theorem R71761 : Reach 71761 := rs (se 2 (by rfl) ⟨26910, by rfl⟩) (B 53821 (by norm_num) ⟨26910, by rfl⟩ (by norm_num))
theorem R71765 : Reach 71765 := rs (se 8 (by rfl) ⟨420, by rfl⟩) (B 841 (by norm_num) ⟨420, by rfl⟩ (by norm_num))
theorem R71769 : Reach 71769 := rs (se 2 (by rfl) ⟨26913, by rfl⟩) (B 53827 (by norm_num) ⟨26913, by rfl⟩ (by norm_num))
theorem R71773 : Reach 71773 := rs (se 3 (by rfl) ⟨13457, by rfl⟩) (B 26915 (by norm_num) ⟨13457, by rfl⟩ (by norm_num))
theorem R71777 : Reach 71777 := rs (se 2 (by rfl) ⟨26916, by rfl⟩) (B 53833 (by norm_num) ⟨26916, by rfl⟩ (by norm_num))
theorem R71781 : Reach 71781 := rs (se 4 (by rfl) ⟨6729, by rfl⟩) (B 13459 (by norm_num) ⟨6729, by rfl⟩ (by norm_num))
theorem R71785 : Reach 71785 := rs (se 2 (by rfl) ⟨26919, by rfl⟩) (B 53839 (by norm_num) ⟨26919, by rfl⟩ (by norm_num))
theorem R71789 : Reach 71789 := rs (se 3 (by rfl) ⟨13460, by rfl⟩) (B 26921 (by norm_num) ⟨13460, by rfl⟩ (by norm_num))
theorem R71793 : Reach 71793 := rs (se 2 (by rfl) ⟨26922, by rfl⟩) (B 53845 (by norm_num) ⟨26922, by rfl⟩ (by norm_num))
theorem R71797 : Reach 71797 := rs (se 5 (by rfl) ⟨3365, by rfl⟩) (B 6731 (by norm_num) ⟨3365, by rfl⟩ (by norm_num))
theorem R71801 : Reach 71801 := rs (se 2 (by rfl) ⟨26925, by rfl⟩) (B 53851 (by norm_num) ⟨26925, by rfl⟩ (by norm_num))
theorem R71805 : Reach 71805 := rs (se 3 (by rfl) ⟨13463, by rfl⟩) (B 26927 (by norm_num) ⟨13463, by rfl⟩ (by norm_num))
theorem R71809 : Reach 71809 := rs (se 2 (by rfl) ⟨26928, by rfl⟩) (B 53857 (by norm_num) ⟨26928, by rfl⟩ (by norm_num))
theorem R71813 : Reach 71813 := rs (se 4 (by rfl) ⟨6732, by rfl⟩) (B 13465 (by norm_num) ⟨6732, by rfl⟩ (by norm_num))
theorem R71817 : Reach 71817 := rs (se 2 (by rfl) ⟨26931, by rfl⟩) (B 53863 (by norm_num) ⟨26931, by rfl⟩ (by norm_num))
theorem R71821 : Reach 71821 := rs (se 3 (by rfl) ⟨13466, by rfl⟩) (B 26933 (by norm_num) ⟨13466, by rfl⟩ (by norm_num))
theorem R71825 : Reach 71825 := rs (se 2 (by rfl) ⟨26934, by rfl⟩) (B 53869 (by norm_num) ⟨26934, by rfl⟩ (by norm_num))
theorem R71829 : Reach 71829 := rs (se 6 (by rfl) ⟨1683, by rfl⟩) (B 3367 (by norm_num) ⟨1683, by rfl⟩ (by norm_num))
theorem R71833 : Reach 71833 := rs (se 2 (by rfl) ⟨26937, by rfl⟩) (B 53875 (by norm_num) ⟨26937, by rfl⟩ (by norm_num))
theorem R71837 : Reach 71837 := rs (se 3 (by rfl) ⟨13469, by rfl⟩) (B 26939 (by norm_num) ⟨13469, by rfl⟩ (by norm_num))
theorem R170141 : Reach 170141 := rs (se 3 (by rfl) ⟨31901, by rfl⟩) (B 63803 (by norm_num) ⟨31901, by rfl⟩ (by norm_num))
theorem R71841 : Reach 71841 := rs (se 2 (by rfl) ⟨26940, by rfl⟩) (B 53881 (by norm_num) ⟨26940, by rfl⟩ (by norm_num))
theorem R71845 : Reach 71845 := rs (se 4 (by rfl) ⟨6735, by rfl⟩) (B 13471 (by norm_num) ⟨6735, by rfl⟩ (by norm_num))
theorem R71849 : Reach 71849 := rs (se 2 (by rfl) ⟨26943, by rfl⟩) (B 53887 (by norm_num) ⟨26943, by rfl⟩ (by norm_num))
theorem R71853 : Reach 71853 := rs (se 3 (by rfl) ⟨13472, by rfl⟩) (B 26945 (by norm_num) ⟨13472, by rfl⟩ (by norm_num))
theorem R71857 : Reach 71857 := rs (se 2 (by rfl) ⟨26946, by rfl⟩) (B 53893 (by norm_num) ⟨26946, by rfl⟩ (by norm_num))
theorem R71861 : Reach 71861 := rs (se 5 (by rfl) ⟨3368, by rfl⟩) (B 6737 (by norm_num) ⟨3368, by rfl⟩ (by norm_num))
theorem R71865 : Reach 71865 := rs (se 2 (by rfl) ⟨26949, by rfl⟩) (B 53899 (by norm_num) ⟨26949, by rfl⟩ (by norm_num))
theorem R71869 : Reach 71869 := rs (se 3 (by rfl) ⟨13475, by rfl⟩) (B 26951 (by norm_num) ⟨13475, by rfl⟩ (by norm_num))
theorem R71873 : Reach 71873 := rs (se 2 (by rfl) ⟨26952, by rfl⟩) (B 53905 (by norm_num) ⟨26952, by rfl⟩ (by norm_num))
theorem R71877 : Reach 71877 := rs (se 4 (by rfl) ⟨6738, by rfl⟩) (B 13477 (by norm_num) ⟨6738, by rfl⟩ (by norm_num))
theorem R71881 : Reach 71881 := rs (se 2 (by rfl) ⟨26955, by rfl⟩) (B 53911 (by norm_num) ⟨26955, by rfl⟩ (by norm_num))
theorem R71885 : Reach 71885 := rs (se 3 (by rfl) ⟨13478, by rfl⟩) (B 26957 (by norm_num) ⟨13478, by rfl⟩ (by norm_num))
theorem R71889 : Reach 71889 := rs (se 2 (by rfl) ⟨26958, by rfl⟩) (B 53917 (by norm_num) ⟨26958, by rfl⟩ (by norm_num))
theorem R71893 : Reach 71893 := rs (se 7 (by rfl) ⟨842, by rfl⟩) (B 1685 (by norm_num) ⟨842, by rfl⟩ (by norm_num))
theorem R71897 : Reach 71897 := rs (se 2 (by rfl) ⟨26961, by rfl⟩) (B 53923 (by norm_num) ⟨26961, by rfl⟩ (by norm_num))
theorem R71901 : Reach 71901 := rs (se 3 (by rfl) ⟨13481, by rfl⟩) (B 26963 (by norm_num) ⟨13481, by rfl⟩ (by norm_num))
theorem R71905 : Reach 71905 := rs (se 2 (by rfl) ⟨26964, by rfl⟩) (B 53929 (by norm_num) ⟨26964, by rfl⟩ (by norm_num))
theorem R202981 : Reach 202981 := rs (se 4 (by rfl) ⟨19029, by rfl⟩) (B 38059 (by norm_num) ⟨19029, by rfl⟩ (by norm_num))
theorem R71909 : Reach 71909 := rs (se 4 (by rfl) ⟨6741, by rfl⟩) (B 13483 (by norm_num) ⟨6741, by rfl⟩ (by norm_num))
theorem R71913 : Reach 71913 := rs (se 2 (by rfl) ⟨26967, by rfl⟩) (B 53935 (by norm_num) ⟨26967, by rfl⟩ (by norm_num))
theorem R71917 : Reach 71917 := rs (se 3 (by rfl) ⟨13484, by rfl⟩) (B 26969 (by norm_num) ⟨13484, by rfl⟩ (by norm_num))
theorem R71921 : Reach 71921 := rs (se 2 (by rfl) ⟨26970, by rfl⟩) (B 53941 (by norm_num) ⟨26970, by rfl⟩ (by norm_num))
theorem R71925 : Reach 71925 := rs (se 5 (by rfl) ⟨3371, by rfl⟩) (B 6743 (by norm_num) ⟨3371, by rfl⟩ (by norm_num))
theorem R71929 : Reach 71929 := rs (se 2 (by rfl) ⟨26973, by rfl⟩) (B 53947 (by norm_num) ⟨26973, by rfl⟩ (by norm_num))
theorem R71933 : Reach 71933 := rs (se 3 (by rfl) ⟨13487, by rfl⟩) (B 26975 (by norm_num) ⟨13487, by rfl⟩ (by norm_num))
theorem R71937 : Reach 71937 := rs (se 2 (by rfl) ⟨26976, by rfl⟩) (B 53953 (by norm_num) ⟨26976, by rfl⟩ (by norm_num))
theorem R71941 : Reach 71941 := rs (se 4 (by rfl) ⟨6744, by rfl⟩) (B 13489 (by norm_num) ⟨6744, by rfl⟩ (by norm_num))
theorem R137477 : Reach 137477 := rs (se 4 (by rfl) ⟨12888, by rfl⟩) (B 25777 (by norm_num) ⟨12888, by rfl⟩ (by norm_num))
theorem R71945 : Reach 71945 := rs (se 2 (by rfl) ⟨26979, by rfl⟩) (B 53959 (by norm_num) ⟨26979, by rfl⟩ (by norm_num))
theorem R71949 : Reach 71949 := rs (se 3 (by rfl) ⟨13490, by rfl⟩) (B 26981 (by norm_num) ⟨13490, by rfl⟩ (by norm_num))
theorem R71953 : Reach 71953 := rs (se 2 (by rfl) ⟨26982, by rfl⟩) (B 53965 (by norm_num) ⟨26982, by rfl⟩ (by norm_num))
theorem R71957 : Reach 71957 := rs (se 6 (by rfl) ⟨1686, by rfl⟩) (B 3373 (by norm_num) ⟨1686, by rfl⟩ (by norm_num))
theorem R71961 : Reach 71961 := rs (se 2 (by rfl) ⟨26985, by rfl⟩) (B 53971 (by norm_num) ⟨26985, by rfl⟩ (by norm_num))
theorem R71965 : Reach 71965 := rs (se 3 (by rfl) ⟨13493, by rfl⟩) (B 26987 (by norm_num) ⟨13493, by rfl⟩ (by norm_num))
theorem R71969 : Reach 71969 := rs (se 2 (by rfl) ⟨26988, by rfl⟩) (B 53977 (by norm_num) ⟨26988, by rfl⟩ (by norm_num))
theorem R71973 : Reach 71973 := rs (se 4 (by rfl) ⟨6747, by rfl⟩) (B 13495 (by norm_num) ⟨6747, by rfl⟩ (by norm_num))
theorem R71977 : Reach 71977 := rs (se 2 (by rfl) ⟨26991, by rfl⟩) (B 53983 (by norm_num) ⟨26991, by rfl⟩ (by norm_num))
theorem R71981 : Reach 71981 := rs (se 3 (by rfl) ⟨13496, by rfl⟩) (B 26993 (by norm_num) ⟨13496, by rfl⟩ (by norm_num))
theorem R71985 : Reach 71985 := rs (se 2 (by rfl) ⟨26994, by rfl⟩) (B 53989 (by norm_num) ⟨26994, by rfl⟩ (by norm_num))
theorem R71989 : Reach 71989 := rs (se 5 (by rfl) ⟨3374, by rfl⟩) (B 6749 (by norm_num) ⟨3374, by rfl⟩ (by norm_num))
theorem R71993 : Reach 71993 := rs (se 2 (by rfl) ⟨26997, by rfl⟩) (B 53995 (by norm_num) ⟨26997, by rfl⟩ (by norm_num))
theorem R71997 : Reach 71997 := rs (se 3 (by rfl) ⟨13499, by rfl⟩) (B 26999 (by norm_num) ⟨13499, by rfl⟩ (by norm_num))
theorem R72001 : Reach 72001 := rs (se 2 (by rfl) ⟨27000, by rfl⟩) (B 54001 (by norm_num) ⟨27000, by rfl⟩ (by norm_num))
theorem R72005 : Reach 72005 := rs (se 4 (by rfl) ⟨6750, by rfl⟩) (B 13501 (by norm_num) ⟨6750, by rfl⟩ (by norm_num))
theorem R72009 : Reach 72009 := rs (se 2 (by rfl) ⟨27003, by rfl⟩) (B 54007 (by norm_num) ⟨27003, by rfl⟩ (by norm_num))
theorem R72013 : Reach 72013 := rs (se 3 (by rfl) ⟨13502, by rfl⟩) (B 27005 (by norm_num) ⟨13502, by rfl⟩ (by norm_num))
theorem R72017 : Reach 72017 := rs (se 2 (by rfl) ⟨27006, by rfl⟩) (B 54013 (by norm_num) ⟨27006, by rfl⟩ (by norm_num))
theorem R72021 : Reach 72021 := rs (se 10 (by rfl) ⟨105, by rfl⟩) (B 211 (by norm_num) ⟨105, by rfl⟩ (by norm_num))
theorem R72025 : Reach 72025 := rs (se 2 (by rfl) ⟨27009, by rfl⟩) (B 54019 (by norm_num) ⟨27009, by rfl⟩ (by norm_num))
theorem R72029 : Reach 72029 := rs (se 3 (by rfl) ⟨13505, by rfl⟩) (B 27011 (by norm_num) ⟨13505, by rfl⟩ (by norm_num))
theorem R72033 : Reach 72033 := rs (se 2 (by rfl) ⟨27012, by rfl⟩) (B 54025 (by norm_num) ⟨27012, by rfl⟩ (by norm_num))
theorem R72037 : Reach 72037 := rs (se 4 (by rfl) ⟨6753, by rfl⟩) (B 13507 (by norm_num) ⟨6753, by rfl⟩ (by norm_num))
theorem R72041 : Reach 72041 := rs (se 2 (by rfl) ⟨27015, by rfl⟩) (B 54031 (by norm_num) ⟨27015, by rfl⟩ (by norm_num))
theorem R72045 : Reach 72045 := rs (se 3 (by rfl) ⟨13508, by rfl⟩) (B 27017 (by norm_num) ⟨13508, by rfl⟩ (by norm_num))
theorem R72049 : Reach 72049 := rs (se 2 (by rfl) ⟨27018, by rfl⟩) (B 54037 (by norm_num) ⟨27018, by rfl⟩ (by norm_num))
theorem R72053 : Reach 72053 := rs (se 5 (by rfl) ⟨3377, by rfl⟩) (B 6755 (by norm_num) ⟨3377, by rfl⟩ (by norm_num))
theorem R72057 : Reach 72057 := rs (se 2 (by rfl) ⟨27021, by rfl⟩) (B 54043 (by norm_num) ⟨27021, by rfl⟩ (by norm_num))
theorem R72061 : Reach 72061 := rs (se 3 (by rfl) ⟨13511, by rfl⟩) (B 27023 (by norm_num) ⟨13511, by rfl⟩ (by norm_num))
theorem R72065 : Reach 72065 := rs (se 2 (by rfl) ⟨27024, by rfl⟩) (B 54049 (by norm_num) ⟨27024, by rfl⟩ (by norm_num))
theorem R203141 : Reach 203141 := rs (se 4 (by rfl) ⟨19044, by rfl⟩) (B 38089 (by norm_num) ⟨19044, by rfl⟩ (by norm_num))
theorem R72069 : Reach 72069 := rs (se 4 (by rfl) ⟨6756, by rfl⟩) (B 13513 (by norm_num) ⟨6756, by rfl⟩ (by norm_num))
theorem R72073 : Reach 72073 := rs (se 2 (by rfl) ⟨27027, by rfl⟩) (B 54055 (by norm_num) ⟨27027, by rfl⟩ (by norm_num))
theorem R72077 : Reach 72077 := rs (se 3 (by rfl) ⟨13514, by rfl⟩) (B 27029 (by norm_num) ⟨13514, by rfl⟩ (by norm_num))
theorem R72081 : Reach 72081 := rs (se 2 (by rfl) ⟨27030, by rfl⟩) (B 54061 (by norm_num) ⟨27030, by rfl⟩ (by norm_num))
theorem R72085 : Reach 72085 := rs (se 6 (by rfl) ⟨1689, by rfl⟩) (B 3379 (by norm_num) ⟨1689, by rfl⟩ (by norm_num))
theorem R72089 : Reach 72089 := rs (se 2 (by rfl) ⟨27033, by rfl⟩) (B 54067 (by norm_num) ⟨27033, by rfl⟩ (by norm_num))
theorem R72093 : Reach 72093 := rs (se 3 (by rfl) ⟨13517, by rfl⟩) (B 27035 (by norm_num) ⟨13517, by rfl⟩ (by norm_num))
theorem R137629 : Reach 137629 := rs (se 3 (by rfl) ⟨25805, by rfl⟩) (B 51611 (by norm_num) ⟨25805, by rfl⟩ (by norm_num))
theorem R72097 : Reach 72097 := rs (se 2 (by rfl) ⟨27036, by rfl⟩) (B 54073 (by norm_num) ⟨27036, by rfl⟩ (by norm_num))
theorem R72101 : Reach 72101 := rs (se 4 (by rfl) ⟨6759, by rfl⟩) (B 13519 (by norm_num) ⟨6759, by rfl⟩ (by norm_num))
theorem R72105 : Reach 72105 := rs (se 2 (by rfl) ⟨27039, by rfl⟩) (B 54079 (by norm_num) ⟨27039, by rfl⟩ (by norm_num))
theorem R72109 : Reach 72109 := rs (se 3 (by rfl) ⟨13520, by rfl⟩) (B 27041 (by norm_num) ⟨13520, by rfl⟩ (by norm_num))
theorem R72113 : Reach 72113 := rs (se 2 (by rfl) ⟨27042, by rfl⟩) (B 54085 (by norm_num) ⟨27042, by rfl⟩ (by norm_num))
theorem R72117 : Reach 72117 := rs (se 5 (by rfl) ⟨3380, by rfl⟩) (B 6761 (by norm_num) ⟨3380, by rfl⟩ (by norm_num))
theorem R72121 : Reach 72121 := rs (se 2 (by rfl) ⟨27045, by rfl⟩) (B 54091 (by norm_num) ⟨27045, by rfl⟩ (by norm_num))
theorem R72125 : Reach 72125 := rs (se 3 (by rfl) ⟨13523, by rfl⟩) (B 27047 (by norm_num) ⟨13523, by rfl⟩ (by norm_num))
theorem R72129 : Reach 72129 := rs (se 2 (by rfl) ⟨27048, by rfl⟩) (B 54097 (by norm_num) ⟨27048, by rfl⟩ (by norm_num))
theorem R72133 : Reach 72133 := rs (se 4 (by rfl) ⟨6762, by rfl⟩) (B 13525 (by norm_num) ⟨6762, by rfl⟩ (by norm_num))
theorem R72137 : Reach 72137 := rs (se 2 (by rfl) ⟨27051, by rfl⟩) (B 54103 (by norm_num) ⟨27051, by rfl⟩ (by norm_num))
theorem R72141 : Reach 72141 := rs (se 3 (by rfl) ⟨13526, by rfl⟩) (B 27053 (by norm_num) ⟨13526, by rfl⟩ (by norm_num))
theorem R72145 : Reach 72145 := rs (se 2 (by rfl) ⟨27054, by rfl⟩) (B 54109 (by norm_num) ⟨27054, by rfl⟩ (by norm_num))
theorem R72149 : Reach 72149 := rs (se 7 (by rfl) ⟨845, by rfl⟩) (B 1691 (by norm_num) ⟨845, by rfl⟩ (by norm_num))
theorem R72153 : Reach 72153 := rs (se 2 (by rfl) ⟨27057, by rfl⟩) (B 54115 (by norm_num) ⟨27057, by rfl⟩ (by norm_num))
theorem R137693 : Reach 137693 := rs (se 3 (by rfl) ⟨25817, by rfl⟩) (B 51635 (by norm_num) ⟨25817, by rfl⟩ (by norm_num))
theorem R72157 : Reach 72157 := rs (se 3 (by rfl) ⟨13529, by rfl⟩) (B 27059 (by norm_num) ⟨13529, by rfl⟩ (by norm_num))
theorem R72161 : Reach 72161 := rs (se 2 (by rfl) ⟨27060, by rfl⟩) (B 54121 (by norm_num) ⟨27060, by rfl⟩ (by norm_num))
theorem R72165 : Reach 72165 := rs (se 4 (by rfl) ⟨6765, by rfl⟩) (B 13531 (by norm_num) ⟨6765, by rfl⟩ (by norm_num))
theorem R72169 : Reach 72169 := rs (se 2 (by rfl) ⟨27063, by rfl⟩) (B 54127 (by norm_num) ⟨27063, by rfl⟩ (by norm_num))
theorem R72173 : Reach 72173 := rs (se 3 (by rfl) ⟨13532, by rfl⟩) (B 27065 (by norm_num) ⟨13532, by rfl⟩ (by norm_num))
theorem R72177 : Reach 72177 := rs (se 2 (by rfl) ⟨27066, by rfl⟩) (B 54133 (by norm_num) ⟨27066, by rfl⟩ (by norm_num))
theorem R72181 : Reach 72181 := rs (se 5 (by rfl) ⟨3383, by rfl⟩) (B 6767 (by norm_num) ⟨3383, by rfl⟩ (by norm_num))
theorem R72185 : Reach 72185 := rs (se 2 (by rfl) ⟨27069, by rfl⟩) (B 54139 (by norm_num) ⟨27069, by rfl⟩ (by norm_num))
theorem R72189 : Reach 72189 := rs (se 3 (by rfl) ⟨13535, by rfl⟩) (B 27071 (by norm_num) ⟨13535, by rfl⟩ (by norm_num))
theorem R72193 : Reach 72193 := rs (se 2 (by rfl) ⟨27072, by rfl⟩) (B 54145 (by norm_num) ⟨27072, by rfl⟩ (by norm_num))
theorem R72197 : Reach 72197 := rs (se 4 (by rfl) ⟨6768, by rfl⟩) (B 13537 (by norm_num) ⟨6768, by rfl⟩ (by norm_num))
theorem R72201 : Reach 72201 := rs (se 2 (by rfl) ⟨27075, by rfl⟩) (B 54151 (by norm_num) ⟨27075, by rfl⟩ (by norm_num))
theorem R72205 : Reach 72205 := rs (se 3 (by rfl) ⟨13538, by rfl⟩) (B 27077 (by norm_num) ⟨13538, by rfl⟩ (by norm_num))
theorem R72209 : Reach 72209 := rs (se 2 (by rfl) ⟨27078, by rfl⟩) (B 54157 (by norm_num) ⟨27078, by rfl⟩ (by norm_num))
theorem R72213 : Reach 72213 := rs (se 6 (by rfl) ⟨1692, by rfl⟩) (B 3385 (by norm_num) ⟨1692, by rfl⟩ (by norm_num))
theorem R72217 : Reach 72217 := rs (se 2 (by rfl) ⟨27081, by rfl⟩) (B 54163 (by norm_num) ⟨27081, by rfl⟩ (by norm_num))
theorem R72221 : Reach 72221 := rs (se 3 (by rfl) ⟨13541, by rfl⟩) (B 27083 (by norm_num) ⟨13541, by rfl⟩ (by norm_num))
theorem R72225 : Reach 72225 := rs (se 2 (by rfl) ⟨27084, by rfl⟩) (B 54169 (by norm_num) ⟨27084, by rfl⟩ (by norm_num))
theorem R72229 : Reach 72229 := rs (se 4 (by rfl) ⟨6771, by rfl⟩) (B 13543 (by norm_num) ⟨6771, by rfl⟩ (by norm_num))
theorem R72233 : Reach 72233 := rs (se 2 (by rfl) ⟨27087, by rfl⟩) (B 54175 (by norm_num) ⟨27087, by rfl⟩ (by norm_num))
theorem R72237 : Reach 72237 := rs (se 3 (by rfl) ⟨13544, by rfl⟩) (B 27089 (by norm_num) ⟨13544, by rfl⟩ (by norm_num))
theorem R72241 : Reach 72241 := rs (se 2 (by rfl) ⟨27090, by rfl⟩) (B 54181 (by norm_num) ⟨27090, by rfl⟩ (by norm_num))
theorem R72245 : Reach 72245 := rs (se 5 (by rfl) ⟨3386, by rfl⟩) (B 6773 (by norm_num) ⟨3386, by rfl⟩ (by norm_num))
theorem R72249 : Reach 72249 := rs (se 2 (by rfl) ⟨27093, by rfl⟩) (B 54187 (by norm_num) ⟨27093, by rfl⟩ (by norm_num))
theorem R72253 : Reach 72253 := rs (se 3 (by rfl) ⟨13547, by rfl⟩) (B 27095 (by norm_num) ⟨13547, by rfl⟩ (by norm_num))
theorem R72257 : Reach 72257 := rs (se 2 (by rfl) ⟨27096, by rfl⟩) (B 54193 (by norm_num) ⟨27096, by rfl⟩ (by norm_num))
theorem R72261 : Reach 72261 := rs (se 4 (by rfl) ⟨6774, by rfl⟩) (B 13549 (by norm_num) ⟨6774, by rfl⟩ (by norm_num))
theorem R72265 : Reach 72265 := rs (se 2 (by rfl) ⟨27099, by rfl⟩) (B 54199 (by norm_num) ⟨27099, by rfl⟩ (by norm_num))
theorem R72269 : Reach 72269 := rs (se 3 (by rfl) ⟨13550, by rfl⟩) (B 27101 (by norm_num) ⟨13550, by rfl⟩ (by norm_num))
theorem R72273 : Reach 72273 := rs (se 2 (by rfl) ⟨27102, by rfl⟩) (B 54205 (by norm_num) ⟨27102, by rfl⟩ (by norm_num))
theorem R72277 : Reach 72277 := rs (se 8 (by rfl) ⟨423, by rfl⟩) (B 847 (by norm_num) ⟨423, by rfl⟩ (by norm_num))
theorem R72281 : Reach 72281 := rs (se 2 (by rfl) ⟨27105, by rfl⟩) (B 54211 (by norm_num) ⟨27105, by rfl⟩ (by norm_num))
theorem R72285 : Reach 72285 := rs (se 3 (by rfl) ⟨13553, by rfl⟩) (B 27107 (by norm_num) ⟨13553, by rfl⟩ (by norm_num))
theorem R72289 : Reach 72289 := rs (se 2 (by rfl) ⟨27108, by rfl⟩) (B 54217 (by norm_num) ⟨27108, by rfl⟩ (by norm_num))
theorem R72293 : Reach 72293 := rs (se 4 (by rfl) ⟨6777, by rfl⟩) (B 13555 (by norm_num) ⟨6777, by rfl⟩ (by norm_num))
theorem R72297 : Reach 72297 := rs (se 2 (by rfl) ⟨27111, by rfl⟩) (B 54223 (by norm_num) ⟨27111, by rfl⟩ (by norm_num))
theorem R72301 : Reach 72301 := rs (se 3 (by rfl) ⟨13556, by rfl⟩) (B 27113 (by norm_num) ⟨13556, by rfl⟩ (by norm_num))
theorem R72305 : Reach 72305 := rs (se 2 (by rfl) ⟨27114, by rfl⟩) (B 54229 (by norm_num) ⟨27114, by rfl⟩ (by norm_num))
theorem R203381 : Reach 203381 := rs (se 5 (by rfl) ⟨9533, by rfl⟩) (B 19067 (by norm_num) ⟨9533, by rfl⟩ (by norm_num))
theorem R72309 : Reach 72309 := rs (se 5 (by rfl) ⟨3389, by rfl⟩) (B 6779 (by norm_num) ⟨3389, by rfl⟩ (by norm_num))
theorem R72313 : Reach 72313 := rs (se 2 (by rfl) ⟨27117, by rfl⟩) (B 54235 (by norm_num) ⟨27117, by rfl⟩ (by norm_num))
theorem R72317 : Reach 72317 := rs (se 3 (by rfl) ⟨13559, by rfl⟩) (B 27119 (by norm_num) ⟨13559, by rfl⟩ (by norm_num))
theorem R72321 : Reach 72321 := rs (se 2 (by rfl) ⟨27120, by rfl⟩) (B 54241 (by norm_num) ⟨27120, by rfl⟩ (by norm_num))
theorem R72325 : Reach 72325 := rs (se 4 (by rfl) ⟨6780, by rfl⟩) (B 13561 (by norm_num) ⟨6780, by rfl⟩ (by norm_num))
theorem R72329 : Reach 72329 := rs (se 2 (by rfl) ⟨27123, by rfl⟩) (B 54247 (by norm_num) ⟨27123, by rfl⟩ (by norm_num))
theorem R72333 : Reach 72333 := rs (se 3 (by rfl) ⟨13562, by rfl⟩) (B 27125 (by norm_num) ⟨13562, by rfl⟩ (by norm_num))
theorem R72337 : Reach 72337 := rs (se 2 (by rfl) ⟨27126, by rfl⟩) (B 54253 (by norm_num) ⟨27126, by rfl⟩ (by norm_num))
theorem R72341 : Reach 72341 := rs (se 6 (by rfl) ⟨1695, by rfl⟩) (B 3391 (by norm_num) ⟨1695, by rfl⟩ (by norm_num))
theorem R367253 : Reach 367253 := rs (se 6 (by rfl) ⟨8607, by rfl⟩) (B 17215 (by norm_num) ⟨8607, by rfl⟩ (by norm_num))
theorem R498325 : Reach 498325 := rs (se 6 (by rfl) ⟨11679, by rfl⟩) (B 23359 (by norm_num) ⟨11679, by rfl⟩ (by norm_num))
theorem R72345 : Reach 72345 := rs (se 2 (by rfl) ⟨27129, by rfl⟩) (B 54259 (by norm_num) ⟨27129, by rfl⟩ (by norm_num))
theorem R72349 : Reach 72349 := rs (se 3 (by rfl) ⟨13565, by rfl⟩) (B 27131 (by norm_num) ⟨13565, by rfl⟩ (by norm_num))
theorem R72353 : Reach 72353 := rs (se 2 (by rfl) ⟨27132, by rfl⟩) (B 54265 (by norm_num) ⟨27132, by rfl⟩ (by norm_num))
theorem R72357 : Reach 72357 := rs (se 4 (by rfl) ⟨6783, by rfl⟩) (B 13567 (by norm_num) ⟨6783, by rfl⟩ (by norm_num))
theorem R72361 : Reach 72361 := rs (se 2 (by rfl) ⟨27135, by rfl⟩) (B 54271 (by norm_num) ⟨27135, by rfl⟩ (by norm_num))
theorem R72365 : Reach 72365 := rs (se 3 (by rfl) ⟨13568, by rfl⟩) (B 27137 (by norm_num) ⟨13568, by rfl⟩ (by norm_num))
theorem R72369 : Reach 72369 := rs (se 2 (by rfl) ⟨27138, by rfl⟩) (B 54277 (by norm_num) ⟨27138, by rfl⟩ (by norm_num))
theorem R72373 : Reach 72373 := rs (se 5 (by rfl) ⟨3392, by rfl⟩) (B 6785 (by norm_num) ⟨3392, by rfl⟩ (by norm_num))
theorem R72377 : Reach 72377 := rs (se 2 (by rfl) ⟨27141, by rfl⟩) (B 54283 (by norm_num) ⟨27141, by rfl⟩ (by norm_num))
theorem R72381 : Reach 72381 := rs (se 3 (by rfl) ⟨13571, by rfl⟩) (B 27143 (by norm_num) ⟨13571, by rfl⟩ (by norm_num))
theorem R72385 : Reach 72385 := rs (se 2 (by rfl) ⟨27144, by rfl⟩) (B 54289 (by norm_num) ⟨27144, by rfl⟩ (by norm_num))
theorem R72389 : Reach 72389 := rs (se 4 (by rfl) ⟨6786, by rfl⟩) (B 13573 (by norm_num) ⟨6786, by rfl⟩ (by norm_num))
theorem R72393 : Reach 72393 := rs (se 2 (by rfl) ⟨27147, by rfl⟩) (B 54295 (by norm_num) ⟨27147, by rfl⟩ (by norm_num))
theorem R137933 : Reach 137933 := rs (se 3 (by rfl) ⟨25862, by rfl⟩) (B 51725 (by norm_num) ⟨25862, by rfl⟩ (by norm_num))
theorem R72397 : Reach 72397 := rs (se 3 (by rfl) ⟨13574, by rfl⟩) (B 27149 (by norm_num) ⟨13574, by rfl⟩ (by norm_num))
theorem R72401 : Reach 72401 := rs (se 2 (by rfl) ⟨27150, by rfl⟩) (B 54301 (by norm_num) ⟨27150, by rfl⟩ (by norm_num))
theorem R72405 : Reach 72405 := rs (se 7 (by rfl) ⟨848, by rfl⟩) (B 1697 (by norm_num) ⟨848, by rfl⟩ (by norm_num))
theorem R72409 : Reach 72409 := rs (se 2 (by rfl) ⟨27153, by rfl⟩) (B 54307 (by norm_num) ⟨27153, by rfl⟩ (by norm_num))
theorem R72413 : Reach 72413 := rs (se 3 (by rfl) ⟨13577, by rfl⟩) (B 27155 (by norm_num) ⟨13577, by rfl⟩ (by norm_num))
theorem R72417 : Reach 72417 := rs (se 2 (by rfl) ⟨27156, by rfl⟩) (B 54313 (by norm_num) ⟨27156, by rfl⟩ (by norm_num))
theorem R72421 : Reach 72421 := rs (se 4 (by rfl) ⟨6789, by rfl⟩) (B 13579 (by norm_num) ⟨6789, by rfl⟩ (by norm_num))
theorem R72425 : Reach 72425 := rs (se 2 (by rfl) ⟨27159, by rfl⟩) (B 54319 (by norm_num) ⟨27159, by rfl⟩ (by norm_num))
theorem R72429 : Reach 72429 := rs (se 3 (by rfl) ⟨13580, by rfl⟩) (B 27161 (by norm_num) ⟨13580, by rfl⟩ (by norm_num))
theorem R72433 : Reach 72433 := rs (se 2 (by rfl) ⟨27162, by rfl⟩) (B 54325 (by norm_num) ⟨27162, by rfl⟩ (by norm_num))
theorem R72437 : Reach 72437 := rs (se 5 (by rfl) ⟨3395, by rfl⟩) (B 6791 (by norm_num) ⟨3395, by rfl⟩ (by norm_num))
theorem R72441 : Reach 72441 := rs (se 2 (by rfl) ⟨27165, by rfl⟩) (B 54331 (by norm_num) ⟨27165, by rfl⟩ (by norm_num))
theorem R72445 : Reach 72445 := rs (se 3 (by rfl) ⟨13583, by rfl⟩) (B 27167 (by norm_num) ⟨13583, by rfl⟩ (by norm_num))
theorem R72449 : Reach 72449 := rs (se 2 (by rfl) ⟨27168, by rfl⟩) (B 54337 (by norm_num) ⟨27168, by rfl⟩ (by norm_num))
theorem R72453 : Reach 72453 := rs (se 4 (by rfl) ⟨6792, by rfl⟩) (B 13585 (by norm_num) ⟨6792, by rfl⟩ (by norm_num))
theorem R72457 : Reach 72457 := rs (se 2 (by rfl) ⟨27171, by rfl⟩) (B 54343 (by norm_num) ⟨27171, by rfl⟩ (by norm_num))
theorem R72461 : Reach 72461 := rs (se 3 (by rfl) ⟨13586, by rfl⟩) (B 27173 (by norm_num) ⟨13586, by rfl⟩ (by norm_num))
theorem R72465 : Reach 72465 := rs (se 2 (by rfl) ⟨27174, by rfl⟩) (B 54349 (by norm_num) ⟨27174, by rfl⟩ (by norm_num))
theorem R72469 : Reach 72469 := rs (se 6 (by rfl) ⟨1698, by rfl⟩) (B 3397 (by norm_num) ⟨1698, by rfl⟩ (by norm_num))
theorem R72473 : Reach 72473 := rs (se 2 (by rfl) ⟨27177, by rfl⟩) (B 54355 (by norm_num) ⟨27177, by rfl⟩ (by norm_num))
theorem R72477 : Reach 72477 := rs (se 3 (by rfl) ⟨13589, by rfl⟩) (B 27179 (by norm_num) ⟨13589, by rfl⟩ (by norm_num))
theorem R72481 : Reach 72481 := rs (se 2 (by rfl) ⟨27180, by rfl⟩) (B 54361 (by norm_num) ⟨27180, by rfl⟩ (by norm_num))
theorem R72485 : Reach 72485 := rs (se 4 (by rfl) ⟨6795, by rfl⟩) (B 13591 (by norm_num) ⟨6795, by rfl⟩ (by norm_num))
theorem R72489 : Reach 72489 := rs (se 2 (by rfl) ⟨27183, by rfl⟩) (B 54367 (by norm_num) ⟨27183, by rfl⟩ (by norm_num))
theorem R72493 : Reach 72493 := rs (se 3 (by rfl) ⟨13592, by rfl⟩) (B 27185 (by norm_num) ⟨13592, by rfl⟩ (by norm_num))
theorem R72497 : Reach 72497 := rs (se 2 (by rfl) ⟨27186, by rfl⟩) (B 54373 (by norm_num) ⟨27186, by rfl⟩ (by norm_num))
theorem R203573 : Reach 203573 := rs (se 5 (by rfl) ⟨9542, by rfl⟩) (B 19085 (by norm_num) ⟨9542, by rfl⟩ (by norm_num))
theorem R72501 : Reach 72501 := rs (se 5 (by rfl) ⟨3398, by rfl⟩) (B 6797 (by norm_num) ⟨3398, by rfl⟩ (by norm_num))
theorem R72505 : Reach 72505 := rs (se 2 (by rfl) ⟨27189, by rfl⟩) (B 54379 (by norm_num) ⟨27189, by rfl⟩ (by norm_num))
theorem R72509 : Reach 72509 := rs (se 3 (by rfl) ⟨13595, by rfl⟩) (B 27191 (by norm_num) ⟨13595, by rfl⟩ (by norm_num))
theorem R72513 : Reach 72513 := rs (se 2 (by rfl) ⟨27192, by rfl⟩) (B 54385 (by norm_num) ⟨27192, by rfl⟩ (by norm_num))
theorem R72517 : Reach 72517 := rs (se 4 (by rfl) ⟨6798, by rfl⟩) (B 13597 (by norm_num) ⟨6798, by rfl⟩ (by norm_num))
theorem R72521 : Reach 72521 := rs (se 2 (by rfl) ⟨27195, by rfl⟩) (B 54391 (by norm_num) ⟨27195, by rfl⟩ (by norm_num))
theorem R72525 : Reach 72525 := rs (se 3 (by rfl) ⟨13598, by rfl⟩) (B 27197 (by norm_num) ⟨13598, by rfl⟩ (by norm_num))
theorem R72529 : Reach 72529 := rs (se 2 (by rfl) ⟨27198, by rfl⟩) (B 54397 (by norm_num) ⟨27198, by rfl⟩ (by norm_num))
theorem R170837 : Reach 170837 := rs (se 9 (by rfl) ⟨500, by rfl⟩) (B 1001 (by norm_num) ⟨500, by rfl⟩ (by norm_num))
theorem R105301 : Reach 105301 := rs (se 9 (by rfl) ⟨308, by rfl⟩) (B 617 (by norm_num) ⟨308, by rfl⟩ (by norm_num))
theorem R72533 : Reach 72533 := rs (se 9 (by rfl) ⟨212, by rfl⟩) (B 425 (by norm_num) ⟨212, by rfl⟩ (by norm_num))
theorem R72537 : Reach 72537 := rs (se 2 (by rfl) ⟨27201, by rfl⟩) (B 54403 (by norm_num) ⟨27201, by rfl⟩ (by norm_num))
theorem R72541 : Reach 72541 := rs (se 3 (by rfl) ⟨13601, by rfl⟩) (B 27203 (by norm_num) ⟨13601, by rfl⟩ (by norm_num))
theorem R72545 : Reach 72545 := rs (se 2 (by rfl) ⟨27204, by rfl⟩) (B 54409 (by norm_num) ⟨27204, by rfl⟩ (by norm_num))
theorem R72549 : Reach 72549 := rs (se 4 (by rfl) ⟨6801, by rfl⟩) (B 13603 (by norm_num) ⟨6801, by rfl⟩ (by norm_num))
theorem R72553 : Reach 72553 := rs (se 2 (by rfl) ⟨27207, by rfl⟩) (B 54415 (by norm_num) ⟨27207, by rfl⟩ (by norm_num))
theorem R72557 : Reach 72557 := rs (se 3 (by rfl) ⟨13604, by rfl⟩) (B 27209 (by norm_num) ⟨13604, by rfl⟩ (by norm_num))
theorem R72561 : Reach 72561 := rs (se 2 (by rfl) ⟨27210, by rfl⟩) (B 54421 (by norm_num) ⟨27210, by rfl⟩ (by norm_num))
theorem R72565 : Reach 72565 := rs (se 5 (by rfl) ⟨3401, by rfl⟩) (B 6803 (by norm_num) ⟨3401, by rfl⟩ (by norm_num))
theorem R72569 : Reach 72569 := rs (se 2 (by rfl) ⟨27213, by rfl⟩) (B 54427 (by norm_num) ⟨27213, by rfl⟩ (by norm_num))
theorem R72573 : Reach 72573 := rs (se 3 (by rfl) ⟨13607, by rfl⟩) (B 27215 (by norm_num) ⟨13607, by rfl⟩ (by norm_num))
theorem R72577 : Reach 72577 := rs (se 2 (by rfl) ⟨27216, by rfl⟩) (B 54433 (by norm_num) ⟨27216, by rfl⟩ (by norm_num))
theorem R72581 : Reach 72581 := rs (se 4 (by rfl) ⟨6804, by rfl⟩) (B 13609 (by norm_num) ⟨6804, by rfl⟩ (by norm_num))
theorem R72585 : Reach 72585 := rs (se 2 (by rfl) ⟨27219, by rfl⟩) (B 54439 (by norm_num) ⟨27219, by rfl⟩ (by norm_num))
theorem R72589 : Reach 72589 := rs (se 3 (by rfl) ⟨13610, by rfl⟩) (B 27221 (by norm_num) ⟨13610, by rfl⟩ (by norm_num))
theorem R72593 : Reach 72593 := rs (se 2 (by rfl) ⟨27222, by rfl⟩) (B 54445 (by norm_num) ⟨27222, by rfl⟩ (by norm_num))
theorem R72597 : Reach 72597 := rs (se 6 (by rfl) ⟨1701, by rfl⟩) (B 3403 (by norm_num) ⟨1701, by rfl⟩ (by norm_num))
theorem R72601 : Reach 72601 := rs (se 2 (by rfl) ⟨27225, by rfl⟩) (B 54451 (by norm_num) ⟨27225, by rfl⟩ (by norm_num))
theorem R72605 : Reach 72605 := rs (se 3 (by rfl) ⟨13613, by rfl⟩) (B 27227 (by norm_num) ⟨13613, by rfl⟩ (by norm_num))
theorem R72609 : Reach 72609 := rs (se 2 (by rfl) ⟨27228, by rfl⟩) (B 54457 (by norm_num) ⟨27228, by rfl⟩ (by norm_num))
theorem R72613 : Reach 72613 := rs (se 4 (by rfl) ⟨6807, by rfl⟩) (B 13615 (by norm_num) ⟨6807, by rfl⟩ (by norm_num))
theorem R72617 : Reach 72617 := rs (se 2 (by rfl) ⟨27231, by rfl⟩) (B 54463 (by norm_num) ⟨27231, by rfl⟩ (by norm_num))
theorem R72621 : Reach 72621 := rs (se 3 (by rfl) ⟨13616, by rfl⟩) (B 27233 (by norm_num) ⟨13616, by rfl⟩ (by norm_num))
theorem R72625 : Reach 72625 := rs (se 2 (by rfl) ⟨27234, by rfl⟩) (B 54469 (by norm_num) ⟨27234, by rfl⟩ (by norm_num))
theorem R72629 : Reach 72629 := rs (se 5 (by rfl) ⟨3404, by rfl⟩) (B 6809 (by norm_num) ⟨3404, by rfl⟩ (by norm_num))
theorem R72633 : Reach 72633 := rs (se 2 (by rfl) ⟨27237, by rfl⟩) (B 54475 (by norm_num) ⟨27237, by rfl⟩ (by norm_num))
theorem R72637 : Reach 72637 := rs (se 3 (by rfl) ⟨13619, by rfl⟩) (B 27239 (by norm_num) ⟨13619, by rfl⟩ (by norm_num))
theorem R72641 : Reach 72641 := rs (se 2 (by rfl) ⟨27240, by rfl⟩) (B 54481 (by norm_num) ⟨27240, by rfl⟩ (by norm_num))
theorem R72645 : Reach 72645 := rs (se 4 (by rfl) ⟨6810, by rfl⟩) (B 13621 (by norm_num) ⟨6810, by rfl⟩ (by norm_num))
theorem R72649 : Reach 72649 := rs (se 2 (by rfl) ⟨27243, by rfl⟩) (B 54487 (by norm_num) ⟨27243, by rfl⟩ (by norm_num))
theorem R72653 : Reach 72653 := rs (se 3 (by rfl) ⟨13622, by rfl⟩) (B 27245 (by norm_num) ⟨13622, by rfl⟩ (by norm_num))
theorem R72657 : Reach 72657 := rs (se 2 (by rfl) ⟨27246, by rfl⟩) (B 54493 (by norm_num) ⟨27246, by rfl⟩ (by norm_num))
theorem R72661 : Reach 72661 := rs (se 7 (by rfl) ⟨851, by rfl⟩) (B 1703 (by norm_num) ⟨851, by rfl⟩ (by norm_num))
theorem R72665 : Reach 72665 := rs (se 2 (by rfl) ⟨27249, by rfl⟩) (B 54499 (by norm_num) ⟨27249, by rfl⟩ (by norm_num))
theorem R72669 : Reach 72669 := rs (se 3 (by rfl) ⟨13625, by rfl⟩) (B 27251 (by norm_num) ⟨13625, by rfl⟩ (by norm_num))
theorem R72673 : Reach 72673 := rs (se 2 (by rfl) ⟨27252, by rfl⟩) (B 54505 (by norm_num) ⟨27252, by rfl⟩ (by norm_num))
theorem R72677 : Reach 72677 := rs (se 4 (by rfl) ⟨6813, by rfl⟩) (B 13627 (by norm_num) ⟨6813, by rfl⟩ (by norm_num))
theorem R72681 : Reach 72681 := rs (se 2 (by rfl) ⟨27255, by rfl⟩) (B 54511 (by norm_num) ⟨27255, by rfl⟩ (by norm_num))
theorem R72685 : Reach 72685 := rs (se 3 (by rfl) ⟨13628, by rfl⟩) (B 27257 (by norm_num) ⟨13628, by rfl⟩ (by norm_num))
theorem R72689 : Reach 72689 := rs (se 2 (by rfl) ⟨27258, by rfl⟩) (B 54517 (by norm_num) ⟨27258, by rfl⟩ (by norm_num))
theorem R72693 : Reach 72693 := rs (se 5 (by rfl) ⟨3407, by rfl⟩) (B 6815 (by norm_num) ⟨3407, by rfl⟩ (by norm_num))
theorem R72697 : Reach 72697 := rs (se 2 (by rfl) ⟨27261, by rfl⟩) (B 54523 (by norm_num) ⟨27261, by rfl⟩ (by norm_num))
theorem R72701 : Reach 72701 := rs (se 3 (by rfl) ⟨13631, by rfl⟩) (B 27263 (by norm_num) ⟨13631, by rfl⟩ (by norm_num))
theorem R72705 : Reach 72705 := rs (se 2 (by rfl) ⟨27264, by rfl⟩) (B 54529 (by norm_num) ⟨27264, by rfl⟩ (by norm_num))
theorem R72709 : Reach 72709 := rs (se 4 (by rfl) ⟨6816, by rfl⟩) (B 13633 (by norm_num) ⟨6816, by rfl⟩ (by norm_num))
theorem R72713 : Reach 72713 := rs (se 2 (by rfl) ⟨27267, by rfl⟩) (B 54535 (by norm_num) ⟨27267, by rfl⟩ (by norm_num))
theorem R72717 : Reach 72717 := rs (se 3 (by rfl) ⟨13634, by rfl⟩) (B 27269 (by norm_num) ⟨13634, by rfl⟩ (by norm_num))
theorem R72721 : Reach 72721 := rs (se 2 (by rfl) ⟨27270, by rfl⟩) (B 54541 (by norm_num) ⟨27270, by rfl⟩ (by norm_num))
theorem R72725 : Reach 72725 := rs (se 6 (by rfl) ⟨1704, by rfl⟩) (B 3409 (by norm_num) ⟨1704, by rfl⟩ (by norm_num))
theorem R564245 : Reach 564245 := rs (se 6 (by rfl) ⟨13224, by rfl⟩) (B 26449 (by norm_num) ⟨13224, by rfl⟩ (by norm_num))
theorem R72729 : Reach 72729 := rs (se 2 (by rfl) ⟨27273, by rfl⟩) (B 54547 (by norm_num) ⟨27273, by rfl⟩ (by norm_num))
theorem R72733 : Reach 72733 := rs (se 3 (by rfl) ⟨13637, by rfl⟩) (B 27275 (by norm_num) ⟨13637, by rfl⟩ (by norm_num))
theorem R72737 : Reach 72737 := rs (se 2 (by rfl) ⟨27276, by rfl⟩) (B 54553 (by norm_num) ⟨27276, by rfl⟩ (by norm_num))
theorem R72741 : Reach 72741 := rs (se 4 (by rfl) ⟨6819, by rfl⟩) (B 13639 (by norm_num) ⟨6819, by rfl⟩ (by norm_num))
theorem R72745 : Reach 72745 := rs (se 2 (by rfl) ⟨27279, by rfl⟩) (B 54559 (by norm_num) ⟨27279, by rfl⟩ (by norm_num))
theorem R72749 : Reach 72749 := rs (se 3 (by rfl) ⟨13640, by rfl⟩) (B 27281 (by norm_num) ⟨13640, by rfl⟩ (by norm_num))
theorem R72753 : Reach 72753 := rs (se 2 (by rfl) ⟨27282, by rfl⟩) (B 54565 (by norm_num) ⟨27282, by rfl⟩ (by norm_num))
theorem R72757 : Reach 72757 := rs (se 5 (by rfl) ⟨3410, by rfl⟩) (B 6821 (by norm_num) ⟨3410, by rfl⟩ (by norm_num))
theorem R72761 : Reach 72761 := rs (se 2 (by rfl) ⟨27285, by rfl⟩) (B 54571 (by norm_num) ⟨27285, by rfl⟩ (by norm_num))
theorem R72765 : Reach 72765 := rs (se 3 (by rfl) ⟨13643, by rfl⟩) (B 27287 (by norm_num) ⟨13643, by rfl⟩ (by norm_num))
theorem R72769 : Reach 72769 := rs (se 2 (by rfl) ⟨27288, by rfl⟩) (B 54577 (by norm_num) ⟨27288, by rfl⟩ (by norm_num))
theorem R72773 : Reach 72773 := rs (se 4 (by rfl) ⟨6822, by rfl⟩) (B 13645 (by norm_num) ⟨6822, by rfl⟩ (by norm_num))
theorem R72777 : Reach 72777 := rs (se 2 (by rfl) ⟨27291, by rfl⟩) (B 54583 (by norm_num) ⟨27291, by rfl⟩ (by norm_num))
theorem R72781 : Reach 72781 := rs (se 3 (by rfl) ⟨13646, by rfl⟩) (B 27293 (by norm_num) ⟨13646, by rfl⟩ (by norm_num))
theorem R72785 : Reach 72785 := rs (se 2 (by rfl) ⟨27294, by rfl⟩) (B 54589 (by norm_num) ⟨27294, by rfl⟩ (by norm_num))
theorem R72789 : Reach 72789 := rs (se 8 (by rfl) ⟨426, by rfl⟩) (B 853 (by norm_num) ⟨426, by rfl⟩ (by norm_num))
theorem R72793 : Reach 72793 := rs (se 2 (by rfl) ⟨27297, by rfl⟩) (B 54595 (by norm_num) ⟨27297, by rfl⟩ (by norm_num))
theorem R72797 : Reach 72797 := rs (se 3 (by rfl) ⟨13649, by rfl⟩) (B 27299 (by norm_num) ⟨13649, by rfl⟩ (by norm_num))
theorem R72801 : Reach 72801 := rs (se 2 (by rfl) ⟨27300, by rfl⟩) (B 54601 (by norm_num) ⟨27300, by rfl⟩ (by norm_num))
theorem R72805 : Reach 72805 := rs (se 4 (by rfl) ⟨6825, by rfl⟩) (B 13651 (by norm_num) ⟨6825, by rfl⟩ (by norm_num))
theorem R72809 : Reach 72809 := rs (se 2 (by rfl) ⟨27303, by rfl⟩) (B 54607 (by norm_num) ⟨27303, by rfl⟩ (by norm_num))
theorem R72813 : Reach 72813 := rs (se 3 (by rfl) ⟨13652, by rfl⟩) (B 27305 (by norm_num) ⟨13652, by rfl⟩ (by norm_num))
theorem R72817 : Reach 72817 := rs (se 2 (by rfl) ⟨27306, by rfl⟩) (B 54613 (by norm_num) ⟨27306, by rfl⟩ (by norm_num))
theorem R466037 : Reach 466037 := rs (se 5 (by rfl) ⟨21845, by rfl⟩) (B 43691 (by norm_num) ⟨21845, by rfl⟩ (by norm_num))
theorem R72821 : Reach 72821 := rs (se 5 (by rfl) ⟨3413, by rfl⟩) (B 6827 (by norm_num) ⟨3413, by rfl⟩ (by norm_num))
theorem R72825 : Reach 72825 := rs (se 2 (by rfl) ⟨27309, by rfl⟩) (B 54619 (by norm_num) ⟨27309, by rfl⟩ (by norm_num))
theorem R72829 : Reach 72829 := rs (se 3 (by rfl) ⟨13655, by rfl⟩) (B 27311 (by norm_num) ⟨13655, by rfl⟩ (by norm_num))
theorem R72833 : Reach 72833 := rs (se 2 (by rfl) ⟨27312, by rfl⟩) (B 54625 (by norm_num) ⟨27312, by rfl⟩ (by norm_num))
theorem R72837 : Reach 72837 := rs (se 4 (by rfl) ⟨6828, by rfl⟩) (B 13657 (by norm_num) ⟨6828, by rfl⟩ (by norm_num))
theorem R72841 : Reach 72841 := rs (se 2 (by rfl) ⟨27315, by rfl⟩) (B 54631 (by norm_num) ⟨27315, by rfl⟩ (by norm_num))
theorem R72845 : Reach 72845 := rs (se 3 (by rfl) ⟨13658, by rfl⟩) (B 27317 (by norm_num) ⟨13658, by rfl⟩ (by norm_num))
theorem R72849 : Reach 72849 := rs (se 2 (by rfl) ⟨27318, by rfl⟩) (B 54637 (by norm_num) ⟨27318, by rfl⟩ (by norm_num))
theorem R72853 : Reach 72853 := rs (se 6 (by rfl) ⟨1707, by rfl⟩) (B 3415 (by norm_num) ⟨1707, by rfl⟩ (by norm_num))
theorem R72857 : Reach 72857 := rs (se 2 (by rfl) ⟨27321, by rfl⟩) (B 54643 (by norm_num) ⟨27321, by rfl⟩ (by norm_num))
theorem R72861 : Reach 72861 := rs (se 3 (by rfl) ⟨13661, by rfl⟩) (B 27323 (by norm_num) ⟨13661, by rfl⟩ (by norm_num))
theorem R72865 : Reach 72865 := rs (se 2 (by rfl) ⟨27324, by rfl⟩) (B 54649 (by norm_num) ⟨27324, by rfl⟩ (by norm_num))
theorem R72869 : Reach 72869 := rs (se 4 (by rfl) ⟨6831, by rfl⟩) (B 13663 (by norm_num) ⟨6831, by rfl⟩ (by norm_num))
theorem R105637 : Reach 105637 := rs (se 4 (by rfl) ⟨9903, by rfl⟩) (B 19807 (by norm_num) ⟨9903, by rfl⟩ (by norm_num))
theorem R72873 : Reach 72873 := rs (se 2 (by rfl) ⟨27327, by rfl⟩) (B 54655 (by norm_num) ⟨27327, by rfl⟩ (by norm_num))
theorem R72877 : Reach 72877 := rs (se 3 (by rfl) ⟨13664, by rfl⟩) (B 27329 (by norm_num) ⟨13664, by rfl⟩ (by norm_num))
theorem R72881 : Reach 72881 := rs (se 2 (by rfl) ⟨27330, by rfl⟩) (B 54661 (by norm_num) ⟨27330, by rfl⟩ (by norm_num))
theorem R72885 : Reach 72885 := rs (se 5 (by rfl) ⟨3416, by rfl⟩) (B 6833 (by norm_num) ⟨3416, by rfl⟩ (by norm_num))
theorem R72889 : Reach 72889 := rs (se 2 (by rfl) ⟨27333, by rfl⟩) (B 54667 (by norm_num) ⟨27333, by rfl⟩ (by norm_num))
theorem R72893 : Reach 72893 := rs (se 3 (by rfl) ⟨13667, by rfl⟩) (B 27335 (by norm_num) ⟨13667, by rfl⟩ (by norm_num))
theorem R72897 : Reach 72897 := rs (se 2 (by rfl) ⟨27336, by rfl⟩) (B 54673 (by norm_num) ⟨27336, by rfl⟩ (by norm_num))
theorem R72901 : Reach 72901 := rs (se 4 (by rfl) ⟨6834, by rfl⟩) (B 13669 (by norm_num) ⟨6834, by rfl⟩ (by norm_num))
theorem R72905 : Reach 72905 := rs (se 2 (by rfl) ⟨27339, by rfl⟩) (B 54679 (by norm_num) ⟨27339, by rfl⟩ (by norm_num))
theorem R72909 : Reach 72909 := rs (se 3 (by rfl) ⟨13670, by rfl⟩) (B 27341 (by norm_num) ⟨13670, by rfl⟩ (by norm_num))
theorem R72913 : Reach 72913 := rs (se 2 (by rfl) ⟨27342, by rfl⟩) (B 54685 (by norm_num) ⟨27342, by rfl⟩ (by norm_num))
theorem R72917 : Reach 72917 := rs (se 7 (by rfl) ⟨854, by rfl⟩) (B 1709 (by norm_num) ⟨854, by rfl⟩ (by norm_num))
theorem R269525 : Reach 269525 := rs (se 7 (by rfl) ⟨3158, by rfl⟩) (B 6317 (by norm_num) ⟨3158, by rfl⟩ (by norm_num))
theorem R72921 : Reach 72921 := rs (se 2 (by rfl) ⟨27345, by rfl⟩) (B 54691 (by norm_num) ⟨27345, by rfl⟩ (by norm_num))
theorem R72925 : Reach 72925 := rs (se 3 (by rfl) ⟨13673, by rfl⟩) (B 27347 (by norm_num) ⟨13673, by rfl⟩ (by norm_num))
theorem R72929 : Reach 72929 := rs (se 2 (by rfl) ⟨27348, by rfl⟩) (B 54697 (by norm_num) ⟨27348, by rfl⟩ (by norm_num))
theorem R72933 : Reach 72933 := rs (se 4 (by rfl) ⟨6837, by rfl⟩) (B 13675 (by norm_num) ⟨6837, by rfl⟩ (by norm_num))
theorem R72937 : Reach 72937 := rs (se 2 (by rfl) ⟨27351, by rfl⟩) (B 54703 (by norm_num) ⟨27351, by rfl⟩ (by norm_num))
theorem R72941 : Reach 72941 := rs (se 3 (by rfl) ⟨13676, by rfl⟩) (B 27353 (by norm_num) ⟨13676, by rfl⟩ (by norm_num))
theorem R72945 : Reach 72945 := rs (se 2 (by rfl) ⟨27354, by rfl⟩) (B 54709 (by norm_num) ⟨27354, by rfl⟩ (by norm_num))
theorem R72949 : Reach 72949 := rs (se 5 (by rfl) ⟨3419, by rfl⟩) (B 6839 (by norm_num) ⟨3419, by rfl⟩ (by norm_num))
theorem R72953 : Reach 72953 := rs (se 2 (by rfl) ⟨27357, by rfl⟩) (B 54715 (by norm_num) ⟨27357, by rfl⟩ (by norm_num))
theorem R72957 : Reach 72957 := rs (se 3 (by rfl) ⟨13679, by rfl⟩) (B 27359 (by norm_num) ⟨13679, by rfl⟩ (by norm_num))
theorem R72961 : Reach 72961 := rs (se 2 (by rfl) ⟨27360, by rfl⟩) (B 54721 (by norm_num) ⟨27360, by rfl⟩ (by norm_num))
theorem R72965 : Reach 72965 := rs (se 4 (by rfl) ⟨6840, by rfl⟩) (B 13681 (by norm_num) ⟨6840, by rfl⟩ (by norm_num))
theorem R72969 : Reach 72969 := rs (se 2 (by rfl) ⟨27363, by rfl⟩) (B 54727 (by norm_num) ⟨27363, by rfl⟩ (by norm_num))
theorem R72973 : Reach 72973 := rs (se 3 (by rfl) ⟨13682, by rfl⟩) (B 27365 (by norm_num) ⟨13682, by rfl⟩ (by norm_num))
theorem R72977 : Reach 72977 := rs (se 2 (by rfl) ⟨27366, by rfl⟩) (B 54733 (by norm_num) ⟨27366, by rfl⟩ (by norm_num))
theorem R72981 : Reach 72981 := rs (se 6 (by rfl) ⟨1710, by rfl⟩) (B 3421 (by norm_num) ⟨1710, by rfl⟩ (by norm_num))
theorem R72985 : Reach 72985 := rs (se 2 (by rfl) ⟨27369, by rfl⟩) (B 54739 (by norm_num) ⟨27369, by rfl⟩ (by norm_num))
theorem R72989 : Reach 72989 := rs (se 3 (by rfl) ⟨13685, by rfl⟩) (B 27371 (by norm_num) ⟨13685, by rfl⟩ (by norm_num))
theorem R72993 : Reach 72993 := rs (se 2 (by rfl) ⟨27372, by rfl⟩) (B 54745 (by norm_num) ⟨27372, by rfl⟩ (by norm_num))
theorem R72997 : Reach 72997 := rs (se 4 (by rfl) ⟨6843, by rfl⟩) (B 13687 (by norm_num) ⟨6843, by rfl⟩ (by norm_num))
theorem R73001 : Reach 73001 := rs (se 2 (by rfl) ⟨27375, by rfl⟩) (B 54751 (by norm_num) ⟨27375, by rfl⟩ (by norm_num))
theorem R73005 : Reach 73005 := rs (se 3 (by rfl) ⟨13688, by rfl⟩) (B 27377 (by norm_num) ⟨13688, by rfl⟩ (by norm_num))
theorem R73009 : Reach 73009 := rs (se 2 (by rfl) ⟨27378, by rfl⟩) (B 54757 (by norm_num) ⟨27378, by rfl⟩ (by norm_num))
theorem R73013 : Reach 73013 := rs (se 5 (by rfl) ⟨3422, by rfl⟩) (B 6845 (by norm_num) ⟨3422, by rfl⟩ (by norm_num))
theorem R73017 : Reach 73017 := rs (se 2 (by rfl) ⟨27381, by rfl⟩) (B 54763 (by norm_num) ⟨27381, by rfl⟩ (by norm_num))
theorem R73021 : Reach 73021 := rs (se 3 (by rfl) ⟨13691, by rfl⟩) (B 27383 (by norm_num) ⟨13691, by rfl⟩ (by norm_num))
theorem R73025 : Reach 73025 := rs (se 2 (by rfl) ⟨27384, by rfl⟩) (B 54769 (by norm_num) ⟨27384, by rfl⟩ (by norm_num))
theorem R73029 : Reach 73029 := rs (se 4 (by rfl) ⟨6846, by rfl⟩) (B 13693 (by norm_num) ⟨6846, by rfl⟩ (by norm_num))
theorem R73033 : Reach 73033 := rs (se 2 (by rfl) ⟨27387, by rfl⟩) (B 54775 (by norm_num) ⟨27387, by rfl⟩ (by norm_num))
theorem R73037 : Reach 73037 := rs (se 3 (by rfl) ⟨13694, by rfl⟩) (B 27389 (by norm_num) ⟨13694, by rfl⟩ (by norm_num))
theorem R73041 : Reach 73041 := rs (se 2 (by rfl) ⟨27390, by rfl⟩) (B 54781 (by norm_num) ⟨27390, by rfl⟩ (by norm_num))
theorem R73045 : Reach 73045 := rs (se 11 (by rfl) ⟨53, by rfl⟩) (B 107 (by norm_num) ⟨53, by rfl⟩ (by norm_num))
theorem R73049 : Reach 73049 := rs (se 2 (by rfl) ⟨27393, by rfl⟩) (B 54787 (by norm_num) ⟨27393, by rfl⟩ (by norm_num))
theorem R73053 : Reach 73053 := rs (se 3 (by rfl) ⟨13697, by rfl⟩) (B 27395 (by norm_num) ⟨13697, by rfl⟩ (by norm_num))
theorem R73057 : Reach 73057 := rs (se 2 (by rfl) ⟨27396, by rfl⟩) (B 54793 (by norm_num) ⟨27396, by rfl⟩ (by norm_num))
theorem R73061 : Reach 73061 := rs (se 4 (by rfl) ⟨6849, by rfl⟩) (B 13699 (by norm_num) ⟨6849, by rfl⟩ (by norm_num))
theorem R73065 : Reach 73065 := rs (se 2 (by rfl) ⟨27399, by rfl⟩) (B 54799 (by norm_num) ⟨27399, by rfl⟩ (by norm_num))
theorem R73069 : Reach 73069 := rs (se 3 (by rfl) ⟨13700, by rfl⟩) (B 27401 (by norm_num) ⟨13700, by rfl⟩ (by norm_num))
theorem R73073 : Reach 73073 := rs (se 2 (by rfl) ⟨27402, by rfl⟩) (B 54805 (by norm_num) ⟨27402, by rfl⟩ (by norm_num))
theorem R73077 : Reach 73077 := rs (se 5 (by rfl) ⟨3425, by rfl⟩) (B 6851 (by norm_num) ⟨3425, by rfl⟩ (by norm_num))
theorem R73081 : Reach 73081 := rs (se 2 (by rfl) ⟨27405, by rfl⟩) (B 54811 (by norm_num) ⟨27405, by rfl⟩ (by norm_num))
theorem R73085 : Reach 73085 := rs (se 3 (by rfl) ⟨13703, by rfl⟩) (B 27407 (by norm_num) ⟨13703, by rfl⟩ (by norm_num))
theorem R73089 : Reach 73089 := rs (se 2 (by rfl) ⟨27408, by rfl⟩) (B 54817 (by norm_num) ⟨27408, by rfl⟩ (by norm_num))
theorem R73093 : Reach 73093 := rs (se 4 (by rfl) ⟨6852, by rfl⟩) (B 13705 (by norm_num) ⟨6852, by rfl⟩ (by norm_num))
theorem R73097 : Reach 73097 := rs (se 2 (by rfl) ⟨27411, by rfl⟩) (B 54823 (by norm_num) ⟨27411, by rfl⟩ (by norm_num))
theorem R73101 : Reach 73101 := rs (se 3 (by rfl) ⟨13706, by rfl⟩) (B 27413 (by norm_num) ⟨13706, by rfl⟩ (by norm_num))
theorem R73105 : Reach 73105 := rs (se 2 (by rfl) ⟨27414, by rfl⟩) (B 54829 (by norm_num) ⟨27414, by rfl⟩ (by norm_num))
theorem R73109 : Reach 73109 := rs (se 6 (by rfl) ⟨1713, by rfl⟩) (B 3427 (by norm_num) ⟨1713, by rfl⟩ (by norm_num))
theorem R73113 : Reach 73113 := rs (se 2 (by rfl) ⟨27417, by rfl⟩) (B 54835 (by norm_num) ⟨27417, by rfl⟩ (by norm_num))
theorem R73117 : Reach 73117 := rs (se 3 (by rfl) ⟨13709, by rfl⟩) (B 27419 (by norm_num) ⟨13709, by rfl⟩ (by norm_num))
theorem R73121 : Reach 73121 := rs (se 2 (by rfl) ⟨27420, by rfl⟩) (B 54841 (by norm_num) ⟨27420, by rfl⟩ (by norm_num))
theorem R73125 : Reach 73125 := rs (se 4 (by rfl) ⟨6855, by rfl⟩) (B 13711 (by norm_num) ⟨6855, by rfl⟩ (by norm_num))
theorem R73129 : Reach 73129 := rs (se 2 (by rfl) ⟨27423, by rfl⟩) (B 54847 (by norm_num) ⟨27423, by rfl⟩ (by norm_num))
theorem R73133 : Reach 73133 := rs (se 3 (by rfl) ⟨13712, by rfl⟩) (B 27425 (by norm_num) ⟨13712, by rfl⟩ (by norm_num))
theorem R73137 : Reach 73137 := rs (se 2 (by rfl) ⟨27426, by rfl⟩) (B 54853 (by norm_num) ⟨27426, by rfl⟩ (by norm_num))
theorem R73141 : Reach 73141 := rs (se 5 (by rfl) ⟨3428, by rfl⟩) (B 6857 (by norm_num) ⟨3428, by rfl⟩ (by norm_num))
theorem R73145 : Reach 73145 := rs (se 2 (by rfl) ⟨27429, by rfl⟩) (B 54859 (by norm_num) ⟨27429, by rfl⟩ (by norm_num))
theorem R138685 : Reach 138685 := rs (se 3 (by rfl) ⟨26003, by rfl⟩) (B 52007 (by norm_num) ⟨26003, by rfl⟩ (by norm_num))
theorem R73149 : Reach 73149 := rs (se 3 (by rfl) ⟨13715, by rfl⟩) (B 27431 (by norm_num) ⟨13715, by rfl⟩ (by norm_num))
theorem R73153 : Reach 73153 := rs (se 2 (by rfl) ⟨27432, by rfl⟩) (B 54865 (by norm_num) ⟨27432, by rfl⟩ (by norm_num))
theorem R73157 : Reach 73157 := rs (se 4 (by rfl) ⟨6858, by rfl⟩) (B 13717 (by norm_num) ⟨6858, by rfl⟩ (by norm_num))
theorem R73161 : Reach 73161 := rs (se 2 (by rfl) ⟨27435, by rfl⟩) (B 54871 (by norm_num) ⟨27435, by rfl⟩ (by norm_num))
theorem R73165 : Reach 73165 := rs (se 3 (by rfl) ⟨13718, by rfl⟩) (B 27437 (by norm_num) ⟨13718, by rfl⟩ (by norm_num))
theorem R73169 : Reach 73169 := rs (se 2 (by rfl) ⟨27438, by rfl⟩) (B 54877 (by norm_num) ⟨27438, by rfl⟩ (by norm_num))
theorem R73173 : Reach 73173 := rs (se 7 (by rfl) ⟨857, by rfl⟩) (B 1715 (by norm_num) ⟨857, by rfl⟩ (by norm_num))
theorem R73177 : Reach 73177 := rs (se 2 (by rfl) ⟨27441, by rfl⟩) (B 54883 (by norm_num) ⟨27441, by rfl⟩ (by norm_num))
theorem R73181 : Reach 73181 := rs (se 3 (by rfl) ⟨13721, by rfl⟩) (B 27443 (by norm_num) ⟨13721, by rfl⟩ (by norm_num))
theorem R73185 : Reach 73185 := rs (se 2 (by rfl) ⟨27444, by rfl⟩) (B 54889 (by norm_num) ⟨27444, by rfl⟩ (by norm_num))
theorem R73189 : Reach 73189 := rs (se 4 (by rfl) ⟨6861, by rfl⟩) (B 13723 (by norm_num) ⟨6861, by rfl⟩ (by norm_num))
theorem R73193 : Reach 73193 := rs (se 2 (by rfl) ⟨27447, by rfl⟩) (B 54895 (by norm_num) ⟨27447, by rfl⟩ (by norm_num))
theorem R73197 : Reach 73197 := rs (se 3 (by rfl) ⟨13724, by rfl⟩) (B 27449 (by norm_num) ⟨13724, by rfl⟩ (by norm_num))
theorem R73201 : Reach 73201 := rs (se 2 (by rfl) ⟨27450, by rfl⟩) (B 54901 (by norm_num) ⟨27450, by rfl⟩ (by norm_num))
theorem R73205 : Reach 73205 := rs (se 5 (by rfl) ⟨3431, by rfl⟩) (B 6863 (by norm_num) ⟨3431, by rfl⟩ (by norm_num))
theorem R73209 : Reach 73209 := rs (se 2 (by rfl) ⟨27453, by rfl⟩) (B 54907 (by norm_num) ⟨27453, by rfl⟩ (by norm_num))
theorem R73213 : Reach 73213 := rs (se 3 (by rfl) ⟨13727, by rfl⟩) (B 27455 (by norm_num) ⟨13727, by rfl⟩ (by norm_num))
theorem R73217 : Reach 73217 := rs (se 2 (by rfl) ⟨27456, by rfl⟩) (B 54913 (by norm_num) ⟨27456, by rfl⟩ (by norm_num))
theorem R73221 : Reach 73221 := rs (se 4 (by rfl) ⟨6864, by rfl⟩) (B 13729 (by norm_num) ⟨6864, by rfl⟩ (by norm_num))
theorem R73225 : Reach 73225 := rs (se 2 (by rfl) ⟨27459, by rfl⟩) (B 54919 (by norm_num) ⟨27459, by rfl⟩ (by norm_num))
theorem R73229 : Reach 73229 := rs (se 3 (by rfl) ⟨13730, by rfl⟩) (B 27461 (by norm_num) ⟨13730, by rfl⟩ (by norm_num))
theorem R73233 : Reach 73233 := rs (se 2 (by rfl) ⟨27462, by rfl⟩) (B 54925 (by norm_num) ⟨27462, by rfl⟩ (by norm_num))
theorem R73237 : Reach 73237 := rs (se 6 (by rfl) ⟨1716, by rfl⟩) (B 3433 (by norm_num) ⟨1716, by rfl⟩ (by norm_num))
theorem R73241 : Reach 73241 := rs (se 2 (by rfl) ⟨27465, by rfl⟩) (B 54931 (by norm_num) ⟨27465, by rfl⟩ (by norm_num))
theorem R73245 : Reach 73245 := rs (se 3 (by rfl) ⟨13733, by rfl⟩) (B 27467 (by norm_num) ⟨13733, by rfl⟩ (by norm_num))
theorem R73249 : Reach 73249 := rs (se 2 (by rfl) ⟨27468, by rfl⟩) (B 54937 (by norm_num) ⟨27468, by rfl⟩ (by norm_num))
theorem R73253 : Reach 73253 := rs (se 4 (by rfl) ⟨6867, by rfl⟩) (B 13735 (by norm_num) ⟨6867, by rfl⟩ (by norm_num))
theorem R73257 : Reach 73257 := rs (se 2 (by rfl) ⟨27471, by rfl⟩) (B 54943 (by norm_num) ⟨27471, by rfl⟩ (by norm_num))
theorem R73261 : Reach 73261 := rs (se 3 (by rfl) ⟨13736, by rfl⟩) (B 27473 (by norm_num) ⟨13736, by rfl⟩ (by norm_num))
theorem R73265 : Reach 73265 := rs (se 2 (by rfl) ⟨27474, by rfl⟩) (B 54949 (by norm_num) ⟨27474, by rfl⟩ (by norm_num))
theorem R73269 : Reach 73269 := rs (se 5 (by rfl) ⟨3434, by rfl⟩) (B 6869 (by norm_num) ⟨3434, by rfl⟩ (by norm_num))
theorem R73273 : Reach 73273 := rs (se 2 (by rfl) ⟨27477, by rfl⟩) (B 54955 (by norm_num) ⟨27477, by rfl⟩ (by norm_num))
theorem R73277 : Reach 73277 := rs (se 3 (by rfl) ⟨13739, by rfl⟩) (B 27479 (by norm_num) ⟨13739, by rfl⟩ (by norm_num))
theorem R73281 : Reach 73281 := rs (se 2 (by rfl) ⟨27480, by rfl⟩) (B 54961 (by norm_num) ⟨27480, by rfl⟩ (by norm_num))
theorem R73285 : Reach 73285 := rs (se 4 (by rfl) ⟨6870, by rfl⟩) (B 13741 (by norm_num) ⟨6870, by rfl⟩ (by norm_num))
theorem R73289 : Reach 73289 := rs (se 2 (by rfl) ⟨27483, by rfl⟩) (B 54967 (by norm_num) ⟨27483, by rfl⟩ (by norm_num))
theorem R138829 : Reach 138829 := rs (se 3 (by rfl) ⟨26030, by rfl⟩) (B 52061 (by norm_num) ⟨26030, by rfl⟩ (by norm_num))
theorem R73293 : Reach 73293 := rs (se 3 (by rfl) ⟨13742, by rfl⟩) (B 27485 (by norm_num) ⟨13742, by rfl⟩ (by norm_num))
theorem R73297 : Reach 73297 := rs (se 2 (by rfl) ⟨27486, by rfl⟩) (B 54973 (by norm_num) ⟨27486, by rfl⟩ (by norm_num))
theorem R73301 : Reach 73301 := rs (se 8 (by rfl) ⟨429, by rfl⟩) (B 859 (by norm_num) ⟨429, by rfl⟩ (by norm_num))
theorem R73305 : Reach 73305 := rs (se 2 (by rfl) ⟨27489, by rfl⟩) (B 54979 (by norm_num) ⟨27489, by rfl⟩ (by norm_num))
theorem R73309 : Reach 73309 := rs (se 3 (by rfl) ⟨13745, by rfl⟩) (B 27491 (by norm_num) ⟨13745, by rfl⟩ (by norm_num))
theorem R73313 : Reach 73313 := rs (se 2 (by rfl) ⟨27492, by rfl⟩) (B 54985 (by norm_num) ⟨27492, by rfl⟩ (by norm_num))
theorem R73317 : Reach 73317 := rs (se 4 (by rfl) ⟨6873, by rfl⟩) (B 13747 (by norm_num) ⟨6873, by rfl⟩ (by norm_num))
theorem R73321 : Reach 73321 := rs (se 2 (by rfl) ⟨27495, by rfl⟩) (B 54991 (by norm_num) ⟨27495, by rfl⟩ (by norm_num))
theorem R73325 : Reach 73325 := rs (se 3 (by rfl) ⟨13748, by rfl⟩) (B 27497 (by norm_num) ⟨13748, by rfl⟩ (by norm_num))
theorem R73329 : Reach 73329 := rs (se 2 (by rfl) ⟨27498, by rfl⟩) (B 54997 (by norm_num) ⟨27498, by rfl⟩ (by norm_num))
theorem R73333 : Reach 73333 := rs (se 5 (by rfl) ⟨3437, by rfl⟩) (B 6875 (by norm_num) ⟨3437, by rfl⟩ (by norm_num))
theorem R73337 : Reach 73337 := rs (se 2 (by rfl) ⟨27501, by rfl⟩) (B 55003 (by norm_num) ⟨27501, by rfl⟩ (by norm_num))
theorem R73341 : Reach 73341 := rs (se 3 (by rfl) ⟨13751, by rfl⟩) (B 27503 (by norm_num) ⟨13751, by rfl⟩ (by norm_num))
theorem R73345 : Reach 73345 := rs (se 2 (by rfl) ⟨27504, by rfl⟩) (B 55009 (by norm_num) ⟨27504, by rfl⟩ (by norm_num))
theorem R73349 : Reach 73349 := rs (se 4 (by rfl) ⟨6876, by rfl⟩) (B 13753 (by norm_num) ⟨6876, by rfl⟩ (by norm_num))
theorem R73353 : Reach 73353 := rs (se 2 (by rfl) ⟨27507, by rfl⟩) (B 55015 (by norm_num) ⟨27507, by rfl⟩ (by norm_num))
theorem R73357 : Reach 73357 := rs (se 3 (by rfl) ⟨13754, by rfl⟩) (B 27509 (by norm_num) ⟨13754, by rfl⟩ (by norm_num))
theorem R73361 : Reach 73361 := rs (se 2 (by rfl) ⟨27510, by rfl⟩) (B 55021 (by norm_num) ⟨27510, by rfl⟩ (by norm_num))
theorem R73365 : Reach 73365 := rs (se 6 (by rfl) ⟨1719, by rfl⟩) (B 3439 (by norm_num) ⟨1719, by rfl⟩ (by norm_num))
theorem R73369 : Reach 73369 := rs (se 2 (by rfl) ⟨27513, by rfl⟩) (B 55027 (by norm_num) ⟨27513, by rfl⟩ (by norm_num))
theorem R73373 : Reach 73373 := rs (se 3 (by rfl) ⟨13757, by rfl⟩) (B 27515 (by norm_num) ⟨13757, by rfl⟩ (by norm_num))
theorem R73377 : Reach 73377 := rs (se 2 (by rfl) ⟨27516, by rfl⟩) (B 55033 (by norm_num) ⟨27516, by rfl⟩ (by norm_num))
theorem R73381 : Reach 73381 := rs (se 4 (by rfl) ⟨6879, by rfl⟩) (B 13759 (by norm_num) ⟨6879, by rfl⟩ (by norm_num))
theorem R73385 : Reach 73385 := rs (se 2 (by rfl) ⟨27519, by rfl⟩) (B 55039 (by norm_num) ⟨27519, by rfl⟩ (by norm_num))
theorem R73389 : Reach 73389 := rs (se 3 (by rfl) ⟨13760, by rfl⟩) (B 27521 (by norm_num) ⟨13760, by rfl⟩ (by norm_num))
theorem R73393 : Reach 73393 := rs (se 2 (by rfl) ⟨27522, by rfl⟩) (B 55045 (by norm_num) ⟨27522, by rfl⟩ (by norm_num))
theorem R73397 : Reach 73397 := rs (se 5 (by rfl) ⟨3440, by rfl⟩) (B 6881 (by norm_num) ⟨3440, by rfl⟩ (by norm_num))
theorem R73401 : Reach 73401 := rs (se 2 (by rfl) ⟨27525, by rfl⟩) (B 55051 (by norm_num) ⟨27525, by rfl⟩ (by norm_num))
theorem R73405 : Reach 73405 := rs (se 3 (by rfl) ⟨13763, by rfl⟩) (B 27527 (by norm_num) ⟨13763, by rfl⟩ (by norm_num))
theorem R73409 : Reach 73409 := rs (se 2 (by rfl) ⟨27528, by rfl⟩) (B 55057 (by norm_num) ⟨27528, by rfl⟩ (by norm_num))
theorem R73413 : Reach 73413 := rs (se 4 (by rfl) ⟨6882, by rfl⟩) (B 13765 (by norm_num) ⟨6882, by rfl⟩ (by norm_num))
theorem R73417 : Reach 73417 := rs (se 2 (by rfl) ⟨27531, by rfl⟩) (B 55063 (by norm_num) ⟨27531, by rfl⟩ (by norm_num))
theorem R73421 : Reach 73421 := rs (se 3 (by rfl) ⟨13766, by rfl⟩) (B 27533 (by norm_num) ⟨13766, by rfl⟩ (by norm_num))
theorem R73425 : Reach 73425 := rs (se 2 (by rfl) ⟨27534, by rfl⟩) (B 55069 (by norm_num) ⟨27534, by rfl⟩ (by norm_num))
theorem R73429 : Reach 73429 := rs (se 7 (by rfl) ⟨860, by rfl⟩) (B 1721 (by norm_num) ⟨860, by rfl⟩ (by norm_num))
theorem R73433 : Reach 73433 := rs (se 2 (by rfl) ⟨27537, by rfl⟩) (B 55075 (by norm_num) ⟨27537, by rfl⟩ (by norm_num))
theorem R73437 : Reach 73437 := rs (se 3 (by rfl) ⟨13769, by rfl⟩) (B 27539 (by norm_num) ⟨13769, by rfl⟩ (by norm_num))
theorem R73441 : Reach 73441 := rs (se 2 (by rfl) ⟨27540, by rfl⟩) (B 55081 (by norm_num) ⟨27540, by rfl⟩ (by norm_num))
theorem R73445 : Reach 73445 := rs (se 4 (by rfl) ⟨6885, by rfl⟩) (B 13771 (by norm_num) ⟨6885, by rfl⟩ (by norm_num))
theorem R73449 : Reach 73449 := rs (se 2 (by rfl) ⟨27543, by rfl⟩) (B 55087 (by norm_num) ⟨27543, by rfl⟩ (by norm_num))
theorem R138989 : Reach 138989 := rs (se 3 (by rfl) ⟨26060, by rfl⟩) (B 52121 (by norm_num) ⟨26060, by rfl⟩ (by norm_num))
theorem R73453 : Reach 73453 := rs (se 3 (by rfl) ⟨13772, by rfl⟩) (B 27545 (by norm_num) ⟨13772, by rfl⟩ (by norm_num))
theorem R73457 : Reach 73457 := rs (se 2 (by rfl) ⟨27546, by rfl⟩) (B 55093 (by norm_num) ⟨27546, by rfl⟩ (by norm_num))
theorem R73461 : Reach 73461 := rs (se 5 (by rfl) ⟨3443, by rfl⟩) (B 6887 (by norm_num) ⟨3443, by rfl⟩ (by norm_num))
theorem R106229 : Reach 106229 := rs (se 5 (by rfl) ⟨4979, by rfl⟩) (B 9959 (by norm_num) ⟨4979, by rfl⟩ (by norm_num))
theorem R73465 : Reach 73465 := rs (se 2 (by rfl) ⟨27549, by rfl⟩) (B 55099 (by norm_num) ⟨27549, by rfl⟩ (by norm_num))
theorem R73469 : Reach 73469 := rs (se 3 (by rfl) ⟨13775, by rfl⟩) (B 27551 (by norm_num) ⟨13775, by rfl⟩ (by norm_num))
theorem R73473 : Reach 73473 := rs (se 2 (by rfl) ⟨27552, by rfl⟩) (B 55105 (by norm_num) ⟨27552, by rfl⟩ (by norm_num))
theorem R73477 : Reach 73477 := rs (se 4 (by rfl) ⟨6888, by rfl⟩) (B 13777 (by norm_num) ⟨6888, by rfl⟩ (by norm_num))
theorem R73481 : Reach 73481 := rs (se 2 (by rfl) ⟨27555, by rfl⟩) (B 55111 (by norm_num) ⟨27555, by rfl⟩ (by norm_num))
theorem R73485 : Reach 73485 := rs (se 3 (by rfl) ⟨13778, by rfl⟩) (B 27557 (by norm_num) ⟨13778, by rfl⟩ (by norm_num))
theorem R73489 : Reach 73489 := rs (se 2 (by rfl) ⟨27558, by rfl⟩) (B 55117 (by norm_num) ⟨27558, by rfl⟩ (by norm_num))
theorem R204565 : Reach 204565 := rs (se 6 (by rfl) ⟨4794, by rfl⟩) (B 9589 (by norm_num) ⟨4794, by rfl⟩ (by norm_num))
theorem R73493 : Reach 73493 := rs (se 6 (by rfl) ⟨1722, by rfl⟩) (B 3445 (by norm_num) ⟨1722, by rfl⟩ (by norm_num))
theorem R73497 : Reach 73497 := rs (se 2 (by rfl) ⟨27561, by rfl⟩) (B 55123 (by norm_num) ⟨27561, by rfl⟩ (by norm_num))
theorem R73501 : Reach 73501 := rs (se 3 (by rfl) ⟨13781, by rfl⟩) (B 27563 (by norm_num) ⟨13781, by rfl⟩ (by norm_num))
theorem R73505 : Reach 73505 := rs (se 2 (by rfl) ⟨27564, by rfl⟩) (B 55129 (by norm_num) ⟨27564, by rfl⟩ (by norm_num))
theorem R73509 : Reach 73509 := rs (se 4 (by rfl) ⟨6891, by rfl⟩) (B 13783 (by norm_num) ⟨6891, by rfl⟩ (by norm_num))
theorem R73513 : Reach 73513 := rs (se 2 (by rfl) ⟨27567, by rfl⟩) (B 55135 (by norm_num) ⟨27567, by rfl⟩ (by norm_num))
theorem R73517 : Reach 73517 := rs (se 3 (by rfl) ⟨13784, by rfl⟩) (B 27569 (by norm_num) ⟨13784, by rfl⟩ (by norm_num))
theorem R73521 : Reach 73521 := rs (se 2 (by rfl) ⟨27570, by rfl⟩) (B 55141 (by norm_num) ⟨27570, by rfl⟩ (by norm_num))
theorem R73525 : Reach 73525 := rs (se 5 (by rfl) ⟨3446, by rfl⟩) (B 6893 (by norm_num) ⟨3446, by rfl⟩ (by norm_num))
theorem R73529 : Reach 73529 := rs (se 2 (by rfl) ⟨27573, by rfl⟩) (B 55147 (by norm_num) ⟨27573, by rfl⟩ (by norm_num))
theorem R73533 : Reach 73533 := rs (se 3 (by rfl) ⟨13787, by rfl⟩) (B 27575 (by norm_num) ⟨13787, by rfl⟩ (by norm_num))
theorem R73537 : Reach 73537 := rs (se 2 (by rfl) ⟨27576, by rfl⟩) (B 55153 (by norm_num) ⟨27576, by rfl⟩ (by norm_num))
theorem R73541 : Reach 73541 := rs (se 4 (by rfl) ⟨6894, by rfl⟩) (B 13789 (by norm_num) ⟨6894, by rfl⟩ (by norm_num))
theorem R106309 : Reach 106309 := rs (se 4 (by rfl) ⟨9966, by rfl⟩) (B 19933 (by norm_num) ⟨9966, by rfl⟩ (by norm_num))
theorem R73545 : Reach 73545 := rs (se 2 (by rfl) ⟨27579, by rfl⟩) (B 55159 (by norm_num) ⟨27579, by rfl⟩ (by norm_num))
theorem R73549 : Reach 73549 := rs (se 3 (by rfl) ⟨13790, by rfl⟩) (B 27581 (by norm_num) ⟨13790, by rfl⟩ (by norm_num))
theorem R73553 : Reach 73553 := rs (se 2 (by rfl) ⟨27582, by rfl⟩) (B 55165 (by norm_num) ⟨27582, by rfl⟩ (by norm_num))
theorem R73557 : Reach 73557 := rs (se 9 (by rfl) ⟨215, by rfl⟩) (B 431 (by norm_num) ⟨215, by rfl⟩ (by norm_num))
theorem R73561 : Reach 73561 := rs (se 2 (by rfl) ⟨27585, by rfl⟩) (B 55171 (by norm_num) ⟨27585, by rfl⟩ (by norm_num))
theorem R73565 : Reach 73565 := rs (se 3 (by rfl) ⟨13793, by rfl⟩) (B 27587 (by norm_num) ⟨13793, by rfl⟩ (by norm_num))
theorem R73569 : Reach 73569 := rs (se 2 (by rfl) ⟨27588, by rfl⟩) (B 55177 (by norm_num) ⟨27588, by rfl⟩ (by norm_num))
theorem R73573 : Reach 73573 := rs (se 4 (by rfl) ⟨6897, by rfl⟩) (B 13795 (by norm_num) ⟨6897, by rfl⟩ (by norm_num))
theorem R73577 : Reach 73577 := rs (se 2 (by rfl) ⟨27591, by rfl⟩) (B 55183 (by norm_num) ⟨27591, by rfl⟩ (by norm_num))
theorem R73581 : Reach 73581 := rs (se 3 (by rfl) ⟨13796, by rfl⟩) (B 27593 (by norm_num) ⟨13796, by rfl⟩ (by norm_num))
theorem R73585 : Reach 73585 := rs (se 2 (by rfl) ⟨27594, by rfl⟩) (B 55189 (by norm_num) ⟨27594, by rfl⟩ (by norm_num))
theorem R73589 : Reach 73589 := rs (se 5 (by rfl) ⟨3449, by rfl⟩) (B 6899 (by norm_num) ⟨3449, by rfl⟩ (by norm_num))
theorem R73593 : Reach 73593 := rs (se 2 (by rfl) ⟨27597, by rfl⟩) (B 55195 (by norm_num) ⟨27597, by rfl⟩ (by norm_num))
theorem R139133 : Reach 139133 := rs (se 3 (by rfl) ⟨26087, by rfl⟩) (B 52175 (by norm_num) ⟨26087, by rfl⟩ (by norm_num))
theorem R73597 : Reach 73597 := rs (se 3 (by rfl) ⟨13799, by rfl⟩) (B 27599 (by norm_num) ⟨13799, by rfl⟩ (by norm_num))
theorem R73601 : Reach 73601 := rs (se 2 (by rfl) ⟨27600, by rfl⟩) (B 55201 (by norm_num) ⟨27600, by rfl⟩ (by norm_num))
theorem R73605 : Reach 73605 := rs (se 4 (by rfl) ⟨6900, by rfl⟩) (B 13801 (by norm_num) ⟨6900, by rfl⟩ (by norm_num))
theorem R73609 : Reach 73609 := rs (se 2 (by rfl) ⟨27603, by rfl⟩) (B 55207 (by norm_num) ⟨27603, by rfl⟩ (by norm_num))
theorem R73613 : Reach 73613 := rs (se 3 (by rfl) ⟨13802, by rfl⟩) (B 27605 (by norm_num) ⟨13802, by rfl⟩ (by norm_num))
theorem R73617 : Reach 73617 := rs (se 2 (by rfl) ⟨27606, by rfl⟩) (B 55213 (by norm_num) ⟨27606, by rfl⟩ (by norm_num))
theorem R73621 : Reach 73621 := rs (se 6 (by rfl) ⟨1725, by rfl⟩) (B 3451 (by norm_num) ⟨1725, by rfl⟩ (by norm_num))
theorem R434069 : Reach 434069 := rs (se 6 (by rfl) ⟨10173, by rfl⟩) (B 20347 (by norm_num) ⟨10173, by rfl⟩ (by norm_num))
theorem R73625 : Reach 73625 := rs (se 2 (by rfl) ⟨27609, by rfl⟩) (B 55219 (by norm_num) ⟨27609, by rfl⟩ (by norm_num))
theorem R73629 : Reach 73629 := rs (se 3 (by rfl) ⟨13805, by rfl⟩) (B 27611 (by norm_num) ⟨13805, by rfl⟩ (by norm_num))
theorem R73633 : Reach 73633 := rs (se 2 (by rfl) ⟨27612, by rfl⟩) (B 55225 (by norm_num) ⟨27612, by rfl⟩ (by norm_num))
theorem R368549 : Reach 368549 := rs (se 4 (by rfl) ⟨34551, by rfl⟩) (B 69103 (by norm_num) ⟨34551, by rfl⟩ (by norm_num))
theorem R73637 : Reach 73637 := rs (se 4 (by rfl) ⟨6903, by rfl⟩) (B 13807 (by norm_num) ⟨6903, by rfl⟩ (by norm_num))
theorem R73641 : Reach 73641 := rs (se 2 (by rfl) ⟨27615, by rfl⟩) (B 55231 (by norm_num) ⟨27615, by rfl⟩ (by norm_num))
theorem R73645 : Reach 73645 := rs (se 3 (by rfl) ⟨13808, by rfl⟩) (B 27617 (by norm_num) ⟨13808, by rfl⟩ (by norm_num))
theorem R73649 : Reach 73649 := rs (se 2 (by rfl) ⟨27618, by rfl⟩) (B 55237 (by norm_num) ⟨27618, by rfl⟩ (by norm_num))
theorem R73653 : Reach 73653 := rs (se 5 (by rfl) ⟨3452, by rfl⟩) (B 6905 (by norm_num) ⟨3452, by rfl⟩ (by norm_num))
theorem R73657 : Reach 73657 := rs (se 2 (by rfl) ⟨27621, by rfl⟩) (B 55243 (by norm_num) ⟨27621, by rfl⟩ (by norm_num))
theorem R73661 : Reach 73661 := rs (se 3 (by rfl) ⟨13811, by rfl⟩) (B 27623 (by norm_num) ⟨13811, by rfl⟩ (by norm_num))
theorem R106429 : Reach 106429 := rs (se 3 (by rfl) ⟨19955, by rfl⟩) (B 39911 (by norm_num) ⟨19955, by rfl⟩ (by norm_num))
theorem R73665 : Reach 73665 := rs (se 2 (by rfl) ⟨27624, by rfl⟩) (B 55249 (by norm_num) ⟨27624, by rfl⟩ (by norm_num))
theorem R73669 : Reach 73669 := rs (se 4 (by rfl) ⟨6906, by rfl⟩) (B 13813 (by norm_num) ⟨6906, by rfl⟩ (by norm_num))
theorem R73673 : Reach 73673 := rs (se 2 (by rfl) ⟨27627, by rfl⟩) (B 55255 (by norm_num) ⟨27627, by rfl⟩ (by norm_num))
theorem R73677 : Reach 73677 := rs (se 3 (by rfl) ⟨13814, by rfl⟩) (B 27629 (by norm_num) ⟨13814, by rfl⟩ (by norm_num))
theorem R73681 : Reach 73681 := rs (se 2 (by rfl) ⟨27630, by rfl⟩) (B 55261 (by norm_num) ⟨27630, by rfl⟩ (by norm_num))
theorem R73685 : Reach 73685 := rs (se 7 (by rfl) ⟨863, by rfl⟩) (B 1727 (by norm_num) ⟨863, by rfl⟩ (by norm_num))
theorem R73689 : Reach 73689 := rs (se 2 (by rfl) ⟨27633, by rfl⟩) (B 55267 (by norm_num) ⟨27633, by rfl⟩ (by norm_num))
theorem R73693 : Reach 73693 := rs (se 3 (by rfl) ⟨13817, by rfl⟩) (B 27635 (by norm_num) ⟨13817, by rfl⟩ (by norm_num))
theorem R73697 : Reach 73697 := rs (se 2 (by rfl) ⟨27636, by rfl⟩) (B 55273 (by norm_num) ⟨27636, by rfl⟩ (by norm_num))
theorem R73701 : Reach 73701 := rs (se 4 (by rfl) ⟨6909, by rfl⟩) (B 13819 (by norm_num) ⟨6909, by rfl⟩ (by norm_num))
theorem R73705 : Reach 73705 := rs (se 2 (by rfl) ⟨27639, by rfl⟩) (B 55279 (by norm_num) ⟨27639, by rfl⟩ (by norm_num))
theorem R73709 : Reach 73709 := rs (se 3 (by rfl) ⟨13820, by rfl⟩) (B 27641 (by norm_num) ⟨13820, by rfl⟩ (by norm_num))
theorem R73713 : Reach 73713 := rs (se 2 (by rfl) ⟨27642, by rfl⟩) (B 55285 (by norm_num) ⟨27642, by rfl⟩ (by norm_num))
theorem R73717 : Reach 73717 := rs (se 5 (by rfl) ⟨3455, by rfl⟩) (B 6911 (by norm_num) ⟨3455, by rfl⟩ (by norm_num))
theorem R73721 : Reach 73721 := rs (se 2 (by rfl) ⟨27645, by rfl⟩) (B 55291 (by norm_num) ⟨27645, by rfl⟩ (by norm_num))
theorem R73725 : Reach 73725 := rs (se 3 (by rfl) ⟨13823, by rfl⟩) (B 27647 (by norm_num) ⟨13823, by rfl⟩ (by norm_num))
theorem R73729 : Reach 73729 := rs (se 2 (by rfl) ⟨27648, by rfl⟩) (B 55297 (by norm_num) ⟨27648, by rfl⟩ (by norm_num))
theorem R73733 : Reach 73733 := rs (se 4 (by rfl) ⟨6912, by rfl⟩) (B 13825 (by norm_num) ⟨6912, by rfl⟩ (by norm_num))
theorem R73737 : Reach 73737 := rs (se 2 (by rfl) ⟨27651, by rfl⟩) (B 55303 (by norm_num) ⟨27651, by rfl⟩ (by norm_num))
theorem R73741 : Reach 73741 := rs (se 3 (by rfl) ⟨13826, by rfl⟩) (B 27653 (by norm_num) ⟨13826, by rfl⟩ (by norm_num))
theorem R73745 : Reach 73745 := rs (se 2 (by rfl) ⟨27654, by rfl⟩) (B 55309 (by norm_num) ⟨27654, by rfl⟩ (by norm_num))
theorem R73749 : Reach 73749 := rs (se 6 (by rfl) ⟨1728, by rfl⟩) (B 3457 (by norm_num) ⟨1728, by rfl⟩ (by norm_num))
theorem R73753 : Reach 73753 := rs (se 2 (by rfl) ⟨27657, by rfl⟩) (B 55315 (by norm_num) ⟨27657, by rfl⟩ (by norm_num))
theorem R73757 : Reach 73757 := rs (se 3 (by rfl) ⟨13829, by rfl⟩) (B 27659 (by norm_num) ⟨13829, by rfl⟩ (by norm_num))
theorem R106525 : Reach 106525 := rs (se 3 (by rfl) ⟨19973, by rfl⟩) (B 39947 (by norm_num) ⟨19973, by rfl⟩ (by norm_num))
theorem R73761 : Reach 73761 := rs (se 2 (by rfl) ⟨27660, by rfl⟩) (B 55321 (by norm_num) ⟨27660, by rfl⟩ (by norm_num))
theorem R73765 : Reach 73765 := rs (se 4 (by rfl) ⟨6915, by rfl⟩) (B 13831 (by norm_num) ⟨6915, by rfl⟩ (by norm_num))
theorem R73769 : Reach 73769 := rs (se 2 (by rfl) ⟨27663, by rfl⟩) (B 55327 (by norm_num) ⟨27663, by rfl⟩ (by norm_num))
theorem R73773 : Reach 73773 := rs (se 3 (by rfl) ⟨13832, by rfl⟩) (B 27665 (by norm_num) ⟨13832, by rfl⟩ (by norm_num))
theorem R73777 : Reach 73777 := rs (se 2 (by rfl) ⟨27666, by rfl⟩) (B 55333 (by norm_num) ⟨27666, by rfl⟩ (by norm_num))
theorem R73781 : Reach 73781 := rs (se 5 (by rfl) ⟨3458, by rfl⟩) (B 6917 (by norm_num) ⟨3458, by rfl⟩ (by norm_num))
theorem R73785 : Reach 73785 := rs (se 2 (by rfl) ⟨27669, by rfl⟩) (B 55339 (by norm_num) ⟨27669, by rfl⟩ (by norm_num))
theorem R73789 : Reach 73789 := rs (se 3 (by rfl) ⟨13835, by rfl⟩) (B 27671 (by norm_num) ⟨13835, by rfl⟩ (by norm_num))
theorem R73793 : Reach 73793 := rs (se 2 (by rfl) ⟨27672, by rfl⟩) (B 55345 (by norm_num) ⟨27672, by rfl⟩ (by norm_num))
theorem R73797 : Reach 73797 := rs (se 4 (by rfl) ⟨6918, by rfl⟩) (B 13837 (by norm_num) ⟨6918, by rfl⟩ (by norm_num))
theorem R73801 : Reach 73801 := rs (se 2 (by rfl) ⟨27675, by rfl⟩) (B 55351 (by norm_num) ⟨27675, by rfl⟩ (by norm_num))
theorem R73805 : Reach 73805 := rs (se 3 (by rfl) ⟨13838, by rfl⟩) (B 27677 (by norm_num) ⟨13838, by rfl⟩ (by norm_num))
theorem R73809 : Reach 73809 := rs (se 2 (by rfl) ⟨27678, by rfl⟩) (B 55357 (by norm_num) ⟨27678, by rfl⟩ (by norm_num))
theorem R73813 : Reach 73813 := rs (se 8 (by rfl) ⟨432, by rfl⟩) (B 865 (by norm_num) ⟨432, by rfl⟩ (by norm_num))
theorem R73817 : Reach 73817 := rs (se 2 (by rfl) ⟨27681, by rfl⟩) (B 55363 (by norm_num) ⟨27681, by rfl⟩ (by norm_num))
theorem R73821 : Reach 73821 := rs (se 3 (by rfl) ⟨13841, by rfl⟩) (B 27683 (by norm_num) ⟨13841, by rfl⟩ (by norm_num))
theorem R73825 : Reach 73825 := rs (se 2 (by rfl) ⟨27684, by rfl⟩) (B 55369 (by norm_num) ⟨27684, by rfl⟩ (by norm_num))
theorem R73829 : Reach 73829 := rs (se 4 (by rfl) ⟨6921, by rfl⟩) (B 13843 (by norm_num) ⟨6921, by rfl⟩ (by norm_num))
theorem R73833 : Reach 73833 := rs (se 2 (by rfl) ⟨27687, by rfl⟩) (B 55375 (by norm_num) ⟨27687, by rfl⟩ (by norm_num))
theorem R73837 : Reach 73837 := rs (se 3 (by rfl) ⟨13844, by rfl⟩) (B 27689 (by norm_num) ⟨13844, by rfl⟩ (by norm_num))
theorem R73841 : Reach 73841 := rs (se 2 (by rfl) ⟨27690, by rfl⟩) (B 55381 (by norm_num) ⟨27690, by rfl⟩ (by norm_num))
theorem R73845 : Reach 73845 := rs (se 5 (by rfl) ⟨3461, by rfl⟩) (B 6923 (by norm_num) ⟨3461, by rfl⟩ (by norm_num))
theorem R73849 : Reach 73849 := rs (se 2 (by rfl) ⟨27693, by rfl⟩) (B 55387 (by norm_num) ⟨27693, by rfl⟩ (by norm_num))
theorem R73853 : Reach 73853 := rs (se 3 (by rfl) ⟨13847, by rfl⟩) (B 27695 (by norm_num) ⟨13847, by rfl⟩ (by norm_num))
theorem R73857 : Reach 73857 := rs (se 2 (by rfl) ⟨27696, by rfl⟩) (B 55393 (by norm_num) ⟨27696, by rfl⟩ (by norm_num))
theorem R73861 : Reach 73861 := rs (se 4 (by rfl) ⟨6924, by rfl⟩) (B 13849 (by norm_num) ⟨6924, by rfl⟩ (by norm_num))
theorem R73865 : Reach 73865 := rs (se 2 (by rfl) ⟨27699, by rfl⟩) (B 55399 (by norm_num) ⟨27699, by rfl⟩ (by norm_num))
theorem R73869 : Reach 73869 := rs (se 3 (by rfl) ⟨13850, by rfl⟩) (B 27701 (by norm_num) ⟨13850, by rfl⟩ (by norm_num))
theorem R73873 : Reach 73873 := rs (se 2 (by rfl) ⟨27702, by rfl⟩) (B 55405 (by norm_num) ⟨27702, by rfl⟩ (by norm_num))
theorem R73877 : Reach 73877 := rs (se 6 (by rfl) ⟨1731, by rfl⟩) (B 3463 (by norm_num) ⟨1731, by rfl⟩ (by norm_num))
theorem R73881 : Reach 73881 := rs (se 2 (by rfl) ⟨27705, by rfl⟩) (B 55411 (by norm_num) ⟨27705, by rfl⟩ (by norm_num))
theorem R139421 : Reach 139421 := rs (se 3 (by rfl) ⟨26141, by rfl⟩) (B 52283 (by norm_num) ⟨26141, by rfl⟩ (by norm_num))
theorem R73885 : Reach 73885 := rs (se 3 (by rfl) ⟨13853, by rfl⟩) (B 27707 (by norm_num) ⟨13853, by rfl⟩ (by norm_num))
theorem R73889 : Reach 73889 := rs (se 2 (by rfl) ⟨27708, by rfl⟩) (B 55417 (by norm_num) ⟨27708, by rfl⟩ (by norm_num))
theorem R73893 : Reach 73893 := rs (se 4 (by rfl) ⟨6927, by rfl⟩) (B 13855 (by norm_num) ⟨6927, by rfl⟩ (by norm_num))
theorem R73897 : Reach 73897 := rs (se 2 (by rfl) ⟨27711, by rfl⟩) (B 55423 (by norm_num) ⟨27711, by rfl⟩ (by norm_num))
theorem R73901 : Reach 73901 := rs (se 3 (by rfl) ⟨13856, by rfl⟩) (B 27713 (by norm_num) ⟨13856, by rfl⟩ (by norm_num))
theorem R73905 : Reach 73905 := rs (se 2 (by rfl) ⟨27714, by rfl⟩) (B 55429 (by norm_num) ⟨27714, by rfl⟩ (by norm_num))
theorem R73909 : Reach 73909 := rs (se 5 (by rfl) ⟨3464, by rfl⟩) (B 6929 (by norm_num) ⟨3464, by rfl⟩ (by norm_num))
theorem R73913 : Reach 73913 := rs (se 2 (by rfl) ⟨27717, by rfl⟩) (B 55435 (by norm_num) ⟨27717, by rfl⟩ (by norm_num))
theorem R73917 : Reach 73917 := rs (se 3 (by rfl) ⟨13859, by rfl⟩) (B 27719 (by norm_num) ⟨13859, by rfl⟩ (by norm_num))
theorem R73921 : Reach 73921 := rs (se 2 (by rfl) ⟨27720, by rfl⟩) (B 55441 (by norm_num) ⟨27720, by rfl⟩ (by norm_num))
theorem R73925 : Reach 73925 := rs (se 4 (by rfl) ⟨6930, by rfl⟩) (B 13861 (by norm_num) ⟨6930, by rfl⟩ (by norm_num))
theorem R73929 : Reach 73929 := rs (se 2 (by rfl) ⟨27723, by rfl⟩) (B 55447 (by norm_num) ⟨27723, by rfl⟩ (by norm_num))
theorem R73933 : Reach 73933 := rs (se 3 (by rfl) ⟨13862, by rfl⟩) (B 27725 (by norm_num) ⟨13862, by rfl⟩ (by norm_num))
theorem R73937 : Reach 73937 := rs (se 2 (by rfl) ⟨27726, by rfl⟩) (B 55453 (by norm_num) ⟨27726, by rfl⟩ (by norm_num))
theorem R106709 : Reach 106709 := rs (se 7 (by rfl) ⟨1250, by rfl⟩) (B 2501 (by norm_num) ⟨1250, by rfl⟩ (by norm_num))
theorem R73941 : Reach 73941 := rs (se 7 (by rfl) ⟨866, by rfl⟩) (B 1733 (by norm_num) ⟨866, by rfl⟩ (by norm_num))
theorem R73945 : Reach 73945 := rs (se 2 (by rfl) ⟨27729, by rfl⟩) (B 55459 (by norm_num) ⟨27729, by rfl⟩ (by norm_num))
theorem R73949 : Reach 73949 := rs (se 3 (by rfl) ⟨13865, by rfl⟩) (B 27731 (by norm_num) ⟨13865, by rfl⟩ (by norm_num))
theorem R73953 : Reach 73953 := rs (se 2 (by rfl) ⟨27732, by rfl⟩) (B 55465 (by norm_num) ⟨27732, by rfl⟩ (by norm_num))
theorem R73957 : Reach 73957 := rs (se 4 (by rfl) ⟨6933, by rfl⟩) (B 13867 (by norm_num) ⟨6933, by rfl⟩ (by norm_num))
theorem R73961 : Reach 73961 := rs (se 2 (by rfl) ⟨27735, by rfl⟩) (B 55471 (by norm_num) ⟨27735, by rfl⟩ (by norm_num))
theorem R106733 : Reach 106733 := rs (se 3 (by rfl) ⟨20012, by rfl⟩) (B 40025 (by norm_num) ⟨20012, by rfl⟩ (by norm_num))
theorem R73965 : Reach 73965 := rs (se 3 (by rfl) ⟨13868, by rfl⟩) (B 27737 (by norm_num) ⟨13868, by rfl⟩ (by norm_num))
theorem R73969 : Reach 73969 := rs (se 2 (by rfl) ⟨27738, by rfl⟩) (B 55477 (by norm_num) ⟨27738, by rfl⟩ (by norm_num))
theorem R73973 : Reach 73973 := rs (se 5 (by rfl) ⟨3467, by rfl⟩) (B 6935 (by norm_num) ⟨3467, by rfl⟩ (by norm_num))
theorem R73977 : Reach 73977 := rs (se 2 (by rfl) ⟨27741, by rfl⟩) (B 55483 (by norm_num) ⟨27741, by rfl⟩ (by norm_num))
theorem R73981 : Reach 73981 := rs (se 3 (by rfl) ⟨13871, by rfl⟩) (B 27743 (by norm_num) ⟨13871, by rfl⟩ (by norm_num))
theorem R73985 : Reach 73985 := rs (se 2 (by rfl) ⟨27744, by rfl⟩) (B 55489 (by norm_num) ⟨27744, by rfl⟩ (by norm_num))
theorem R106757 : Reach 106757 := rs (se 4 (by rfl) ⟨10008, by rfl⟩) (B 20017 (by norm_num) ⟨10008, by rfl⟩ (by norm_num))
theorem R73989 : Reach 73989 := rs (se 4 (by rfl) ⟨6936, by rfl⟩) (B 13873 (by norm_num) ⟨6936, by rfl⟩ (by norm_num))
theorem R73993 : Reach 73993 := rs (se 2 (by rfl) ⟨27747, by rfl⟩) (B 55495 (by norm_num) ⟨27747, by rfl⟩ (by norm_num))
theorem R73997 : Reach 73997 := rs (se 3 (by rfl) ⟨13874, by rfl⟩) (B 27749 (by norm_num) ⟨13874, by rfl⟩ (by norm_num))
theorem R74001 : Reach 74001 := rs (se 2 (by rfl) ⟨27750, by rfl⟩) (B 55501 (by norm_num) ⟨27750, by rfl⟩ (by norm_num))
theorem R74005 : Reach 74005 := rs (se 6 (by rfl) ⟨1734, by rfl⟩) (B 3469 (by norm_num) ⟨1734, by rfl⟩ (by norm_num))
theorem R74009 : Reach 74009 := rs (se 2 (by rfl) ⟨27753, by rfl⟩) (B 55507 (by norm_num) ⟨27753, by rfl⟩ (by norm_num))
theorem R106781 : Reach 106781 := rs (se 3 (by rfl) ⟨20021, by rfl⟩) (B 40043 (by norm_num) ⟨20021, by rfl⟩ (by norm_num))
theorem R74013 : Reach 74013 := rs (se 3 (by rfl) ⟨13877, by rfl⟩) (B 27755 (by norm_num) ⟨13877, by rfl⟩ (by norm_num))
theorem R74017 : Reach 74017 := rs (se 2 (by rfl) ⟨27756, by rfl⟩) (B 55513 (by norm_num) ⟨27756, by rfl⟩ (by norm_num))
theorem R74021 : Reach 74021 := rs (se 4 (by rfl) ⟨6939, by rfl⟩) (B 13879 (by norm_num) ⟨6939, by rfl⟩ (by norm_num))
theorem R74025 : Reach 74025 := rs (se 2 (by rfl) ⟨27759, by rfl⟩) (B 55519 (by norm_num) ⟨27759, by rfl⟩ (by norm_num))
theorem R74029 : Reach 74029 := rs (se 3 (by rfl) ⟨13880, by rfl⟩) (B 27761 (by norm_num) ⟨13880, by rfl⟩ (by norm_num))
theorem R74033 : Reach 74033 := rs (se 2 (by rfl) ⟨27762, by rfl⟩) (B 55525 (by norm_num) ⟨27762, by rfl⟩ (by norm_num))
theorem R106805 : Reach 106805 := rs (se 5 (by rfl) ⟨5006, by rfl⟩) (B 10013 (by norm_num) ⟨5006, by rfl⟩ (by norm_num))
theorem R139573 : Reach 139573 := rs (se 5 (by rfl) ⟨6542, by rfl⟩) (B 13085 (by norm_num) ⟨6542, by rfl⟩ (by norm_num))
theorem R74037 : Reach 74037 := rs (se 5 (by rfl) ⟨3470, by rfl⟩) (B 6941 (by norm_num) ⟨3470, by rfl⟩ (by norm_num))
theorem R74041 : Reach 74041 := rs (se 2 (by rfl) ⟨27765, by rfl⟩) (B 55531 (by norm_num) ⟨27765, by rfl⟩ (by norm_num))
theorem R74045 : Reach 74045 := rs (se 3 (by rfl) ⟨13883, by rfl⟩) (B 27767 (by norm_num) ⟨13883, by rfl⟩ (by norm_num))
theorem R74049 : Reach 74049 := rs (se 2 (by rfl) ⟨27768, by rfl⟩) (B 55537 (by norm_num) ⟨27768, by rfl⟩ (by norm_num))
theorem R74053 : Reach 74053 := rs (se 4 (by rfl) ⟨6942, by rfl⟩) (B 13885 (by norm_num) ⟨6942, by rfl⟩ (by norm_num))
theorem R74057 : Reach 74057 := rs (se 2 (by rfl) ⟨27771, by rfl⟩) (B 55543 (by norm_num) ⟨27771, by rfl⟩ (by norm_num))
theorem R106829 : Reach 106829 := rs (se 3 (by rfl) ⟨20030, by rfl⟩) (B 40061 (by norm_num) ⟨20030, by rfl⟩ (by norm_num))
theorem R74061 : Reach 74061 := rs (se 3 (by rfl) ⟨13886, by rfl⟩) (B 27773 (by norm_num) ⟨13886, by rfl⟩ (by norm_num))
theorem R74065 : Reach 74065 := rs (se 2 (by rfl) ⟨27774, by rfl⟩) (B 55549 (by norm_num) ⟨27774, by rfl⟩ (by norm_num))
theorem R74069 : Reach 74069 := rs (se 10 (by rfl) ⟨108, by rfl⟩) (B 217 (by norm_num) ⟨108, by rfl⟩ (by norm_num))
theorem R74073 : Reach 74073 := rs (se 2 (by rfl) ⟨27777, by rfl⟩) (B 55555 (by norm_num) ⟨27777, by rfl⟩ (by norm_num))
theorem R172381 : Reach 172381 := rs (se 3 (by rfl) ⟨32321, by rfl⟩) (B 64643 (by norm_num) ⟨32321, by rfl⟩ (by norm_num))
theorem R74077 : Reach 74077 := rs (se 3 (by rfl) ⟨13889, by rfl⟩) (B 27779 (by norm_num) ⟨13889, by rfl⟩ (by norm_num))
theorem R74081 : Reach 74081 := rs (se 2 (by rfl) ⟨27780, by rfl⟩) (B 55561 (by norm_num) ⟨27780, by rfl⟩ (by norm_num))
theorem R106853 : Reach 106853 := rs (se 4 (by rfl) ⟨10017, by rfl⟩) (B 20035 (by norm_num) ⟨10017, by rfl⟩ (by norm_num))
theorem R74085 : Reach 74085 := rs (se 4 (by rfl) ⟨6945, by rfl⟩) (B 13891 (by norm_num) ⟨6945, by rfl⟩ (by norm_num))
theorem R74089 : Reach 74089 := rs (se 2 (by rfl) ⟨27783, by rfl⟩) (B 55567 (by norm_num) ⟨27783, by rfl⟩ (by norm_num))
theorem R74093 : Reach 74093 := rs (se 3 (by rfl) ⟨13892, by rfl⟩) (B 27785 (by norm_num) ⟨13892, by rfl⟩ (by norm_num))
theorem R74097 : Reach 74097 := rs (se 2 (by rfl) ⟨27786, by rfl⟩) (B 55573 (by norm_num) ⟨27786, by rfl⟩ (by norm_num))
theorem R74101 : Reach 74101 := rs (se 5 (by rfl) ⟨3473, by rfl⟩) (B 6947 (by norm_num) ⟨3473, by rfl⟩ (by norm_num))
theorem R74105 : Reach 74105 := rs (se 2 (by rfl) ⟨27789, by rfl⟩) (B 55579 (by norm_num) ⟨27789, by rfl⟩ (by norm_num))
theorem R106877 : Reach 106877 := rs (se 3 (by rfl) ⟨20039, by rfl⟩) (B 40079 (by norm_num) ⟨20039, by rfl⟩ (by norm_num))
theorem R74109 : Reach 74109 := rs (se 3 (by rfl) ⟨13895, by rfl⟩) (B 27791 (by norm_num) ⟨13895, by rfl⟩ (by norm_num))
theorem R74113 : Reach 74113 := rs (se 2 (by rfl) ⟨27792, by rfl⟩) (B 55585 (by norm_num) ⟨27792, by rfl⟩ (by norm_num))
theorem R74117 : Reach 74117 := rs (se 4 (by rfl) ⟨6948, by rfl⟩) (B 13897 (by norm_num) ⟨6948, by rfl⟩ (by norm_num))
theorem R74121 : Reach 74121 := rs (se 2 (by rfl) ⟨27795, by rfl⟩) (B 55591 (by norm_num) ⟨27795, by rfl⟩ (by norm_num))
theorem R74125 : Reach 74125 := rs (se 3 (by rfl) ⟨13898, by rfl⟩) (B 27797 (by norm_num) ⟨13898, by rfl⟩ (by norm_num))
theorem R74129 : Reach 74129 := rs (se 2 (by rfl) ⟨27798, by rfl⟩) (B 55597 (by norm_num) ⟨27798, by rfl⟩ (by norm_num))
theorem R106901 : Reach 106901 := rs (se 6 (by rfl) ⟨2505, by rfl⟩) (B 5011 (by norm_num) ⟨2505, by rfl⟩ (by norm_num))
theorem R74133 : Reach 74133 := rs (se 6 (by rfl) ⟨1737, by rfl⟩) (B 3475 (by norm_num) ⟨1737, by rfl⟩ (by norm_num))
theorem R74137 : Reach 74137 := rs (se 2 (by rfl) ⟨27801, by rfl⟩) (B 55603 (by norm_num) ⟨27801, by rfl⟩ (by norm_num))
theorem R74141 : Reach 74141 := rs (se 3 (by rfl) ⟨13901, by rfl⟩) (B 27803 (by norm_num) ⟨13901, by rfl⟩ (by norm_num))
theorem R74145 : Reach 74145 := rs (se 2 (by rfl) ⟨27804, by rfl⟩) (B 55609 (by norm_num) ⟨27804, by rfl⟩ (by norm_num))
theorem R74149 : Reach 74149 := rs (se 4 (by rfl) ⟨6951, by rfl⟩) (B 13903 (by norm_num) ⟨6951, by rfl⟩ (by norm_num))
theorem R74153 : Reach 74153 := rs (se 2 (by rfl) ⟨27807, by rfl⟩) (B 55615 (by norm_num) ⟨27807, by rfl⟩ (by norm_num))
theorem R106925 : Reach 106925 := rs (se 3 (by rfl) ⟨20048, by rfl⟩) (B 40097 (by norm_num) ⟨20048, by rfl⟩ (by norm_num))
theorem R74157 : Reach 74157 := rs (se 3 (by rfl) ⟨13904, by rfl⟩) (B 27809 (by norm_num) ⟨13904, by rfl⟩ (by norm_num))
theorem R74161 : Reach 74161 := rs (se 2 (by rfl) ⟨27810, by rfl⟩) (B 55621 (by norm_num) ⟨27810, by rfl⟩ (by norm_num))
theorem R74165 : Reach 74165 := rs (se 5 (by rfl) ⟨3476, by rfl⟩) (B 6953 (by norm_num) ⟨3476, by rfl⟩ (by norm_num))
theorem R74169 : Reach 74169 := rs (se 2 (by rfl) ⟨27813, by rfl⟩) (B 55627 (by norm_num) ⟨27813, by rfl⟩ (by norm_num))
theorem R172477 : Reach 172477 := rs (se 3 (by rfl) ⟨32339, by rfl⟩) (B 64679 (by norm_num) ⟨32339, by rfl⟩ (by norm_num))
theorem R74173 : Reach 74173 := rs (se 3 (by rfl) ⟨13907, by rfl⟩) (B 27815 (by norm_num) ⟨13907, by rfl⟩ (by norm_num))
theorem R74177 : Reach 74177 := rs (se 2 (by rfl) ⟨27816, by rfl⟩) (B 55633 (by norm_num) ⟨27816, by rfl⟩ (by norm_num))
theorem R106949 : Reach 106949 := rs (se 4 (by rfl) ⟨10026, by rfl⟩) (B 20053 (by norm_num) ⟨10026, by rfl⟩ (by norm_num))
theorem R74181 : Reach 74181 := rs (se 4 (by rfl) ⟨6954, by rfl⟩) (B 13909 (by norm_num) ⟨6954, by rfl⟩ (by norm_num))
theorem R74185 : Reach 74185 := rs (se 2 (by rfl) ⟨27819, by rfl⟩) (B 55639 (by norm_num) ⟨27819, by rfl⟩ (by norm_num))
theorem R74189 : Reach 74189 := rs (se 3 (by rfl) ⟨13910, by rfl⟩) (B 27821 (by norm_num) ⟨13910, by rfl⟩ (by norm_num))
theorem R74193 : Reach 74193 := rs (se 2 (by rfl) ⟨27822, by rfl⟩) (B 55645 (by norm_num) ⟨27822, by rfl⟩ (by norm_num))
theorem R74197 : Reach 74197 := rs (se 7 (by rfl) ⟨869, by rfl⟩) (B 1739 (by norm_num) ⟨869, by rfl⟩ (by norm_num))
theorem R74201 : Reach 74201 := rs (se 2 (by rfl) ⟨27825, by rfl⟩) (B 55651 (by norm_num) ⟨27825, by rfl⟩ (by norm_num))
theorem R106973 : Reach 106973 := rs (se 3 (by rfl) ⟨20057, by rfl⟩) (B 40115 (by norm_num) ⟨20057, by rfl⟩ (by norm_num))
theorem R74205 : Reach 74205 := rs (se 3 (by rfl) ⟨13913, by rfl⟩) (B 27827 (by norm_num) ⟨13913, by rfl⟩ (by norm_num))
theorem R74209 : Reach 74209 := rs (se 2 (by rfl) ⟨27828, by rfl⟩) (B 55657 (by norm_num) ⟨27828, by rfl⟩ (by norm_num))
theorem R74213 : Reach 74213 := rs (se 4 (by rfl) ⟨6957, by rfl⟩) (B 13915 (by norm_num) ⟨6957, by rfl⟩ (by norm_num))
theorem R74217 : Reach 74217 := rs (se 2 (by rfl) ⟨27831, by rfl⟩) (B 55663 (by norm_num) ⟨27831, by rfl⟩ (by norm_num))
theorem R74221 : Reach 74221 := rs (se 3 (by rfl) ⟨13916, by rfl⟩) (B 27833 (by norm_num) ⟨13916, by rfl⟩ (by norm_num))
theorem R74225 : Reach 74225 := rs (se 2 (by rfl) ⟨27834, by rfl⟩) (B 55669 (by norm_num) ⟨27834, by rfl⟩ (by norm_num))
theorem R106997 : Reach 106997 := rs (se 5 (by rfl) ⟨5015, by rfl⟩) (B 10031 (by norm_num) ⟨5015, by rfl⟩ (by norm_num))
theorem R74229 : Reach 74229 := rs (se 5 (by rfl) ⟨3479, by rfl⟩) (B 6959 (by norm_num) ⟨3479, by rfl⟩ (by norm_num))
theorem R74233 : Reach 74233 := rs (se 2 (by rfl) ⟨27837, by rfl⟩) (B 55675 (by norm_num) ⟨27837, by rfl⟩ (by norm_num))
theorem R74237 : Reach 74237 := rs (se 3 (by rfl) ⟨13919, by rfl⟩) (B 27839 (by norm_num) ⟨13919, by rfl⟩ (by norm_num))
theorem R74241 : Reach 74241 := rs (se 2 (by rfl) ⟨27840, by rfl⟩) (B 55681 (by norm_num) ⟨27840, by rfl⟩ (by norm_num))
theorem R74245 : Reach 74245 := rs (se 4 (by rfl) ⟨6960, by rfl⟩) (B 13921 (by norm_num) ⟨6960, by rfl⟩ (by norm_num))
theorem R74249 : Reach 74249 := rs (se 2 (by rfl) ⟨27843, by rfl⟩) (B 55687 (by norm_num) ⟨27843, by rfl⟩ (by norm_num))
theorem R107021 : Reach 107021 := rs (se 3 (by rfl) ⟨20066, by rfl⟩) (B 40133 (by norm_num) ⟨20066, by rfl⟩ (by norm_num))
theorem R74253 : Reach 74253 := rs (se 3 (by rfl) ⟨13922, by rfl⟩) (B 27845 (by norm_num) ⟨13922, by rfl⟩ (by norm_num))
theorem R74257 : Reach 74257 := rs (se 2 (by rfl) ⟨27846, by rfl⟩) (B 55693 (by norm_num) ⟨27846, by rfl⟩ (by norm_num))
theorem R74261 : Reach 74261 := rs (se 6 (by rfl) ⟨1740, by rfl⟩) (B 3481 (by norm_num) ⟨1740, by rfl⟩ (by norm_num))
theorem R74265 : Reach 74265 := rs (se 2 (by rfl) ⟨27849, by rfl⟩) (B 55699 (by norm_num) ⟨27849, by rfl⟩ (by norm_num))
theorem R74269 : Reach 74269 := rs (se 3 (by rfl) ⟨13925, by rfl⟩) (B 27851 (by norm_num) ⟨13925, by rfl⟩ (by norm_num))
theorem R74273 : Reach 74273 := rs (se 2 (by rfl) ⟨27852, by rfl⟩) (B 55705 (by norm_num) ⟨27852, by rfl⟩ (by norm_num))
theorem R107045 : Reach 107045 := rs (se 4 (by rfl) ⟨10035, by rfl⟩) (B 20071 (by norm_num) ⟨10035, by rfl⟩ (by norm_num))
theorem R74277 : Reach 74277 := rs (se 4 (by rfl) ⟨6963, by rfl⟩) (B 13927 (by norm_num) ⟨6963, by rfl⟩ (by norm_num))
theorem R74281 : Reach 74281 := rs (se 2 (by rfl) ⟨27855, by rfl⟩) (B 55711 (by norm_num) ⟨27855, by rfl⟩ (by norm_num))
theorem R74285 : Reach 74285 := rs (se 3 (by rfl) ⟨13928, by rfl⟩) (B 27857 (by norm_num) ⟨13928, by rfl⟩ (by norm_num))
theorem R74289 : Reach 74289 := rs (se 2 (by rfl) ⟨27858, by rfl⟩) (B 55717 (by norm_num) ⟨27858, by rfl⟩ (by norm_num))
theorem R74293 : Reach 74293 := rs (se 5 (by rfl) ⟨3482, by rfl⟩) (B 6965 (by norm_num) ⟨3482, by rfl⟩ (by norm_num))
theorem R238133 : Reach 238133 := rs (se 5 (by rfl) ⟨11162, by rfl⟩) (B 22325 (by norm_num) ⟨11162, by rfl⟩ (by norm_num))
theorem R74297 : Reach 74297 := rs (se 2 (by rfl) ⟨27861, by rfl⟩) (B 55723 (by norm_num) ⟨27861, by rfl⟩ (by norm_num))
theorem R107069 : Reach 107069 := rs (se 3 (by rfl) ⟨20075, by rfl⟩) (B 40151 (by norm_num) ⟨20075, by rfl⟩ (by norm_num))
theorem R74301 : Reach 74301 := rs (se 3 (by rfl) ⟨13931, by rfl⟩) (B 27863 (by norm_num) ⟨13931, by rfl⟩ (by norm_num))
theorem R74305 : Reach 74305 := rs (se 2 (by rfl) ⟨27864, by rfl⟩) (B 55729 (by norm_num) ⟨27864, by rfl⟩ (by norm_num))
theorem R74309 : Reach 74309 := rs (se 4 (by rfl) ⟨6966, by rfl⟩) (B 13933 (by norm_num) ⟨6966, by rfl⟩ (by norm_num))
theorem R74313 : Reach 74313 := rs (se 2 (by rfl) ⟨27867, by rfl⟩) (B 55735 (by norm_num) ⟨27867, by rfl⟩ (by norm_num))
theorem R74317 : Reach 74317 := rs (se 3 (by rfl) ⟨13934, by rfl⟩) (B 27869 (by norm_num) ⟨13934, by rfl⟩ (by norm_num))
theorem R74321 : Reach 74321 := rs (se 2 (by rfl) ⟨27870, by rfl⟩) (B 55741 (by norm_num) ⟨27870, by rfl⟩ (by norm_num))
theorem R107093 : Reach 107093 := rs (se 8 (by rfl) ⟨627, by rfl⟩) (B 1255 (by norm_num) ⟨627, by rfl⟩ (by norm_num))
theorem R74325 : Reach 74325 := rs (se 8 (by rfl) ⟨435, by rfl⟩) (B 871 (by norm_num) ⟨435, by rfl⟩ (by norm_num))
theorem R74329 : Reach 74329 := rs (se 2 (by rfl) ⟨27873, by rfl⟩) (B 55747 (by norm_num) ⟨27873, by rfl⟩ (by norm_num))
theorem R74333 : Reach 74333 := rs (se 3 (by rfl) ⟨13937, by rfl⟩) (B 27875 (by norm_num) ⟨13937, by rfl⟩ (by norm_num))
theorem R74337 : Reach 74337 := rs (se 2 (by rfl) ⟨27876, by rfl⟩) (B 55753 (by norm_num) ⟨27876, by rfl⟩ (by norm_num))
theorem R139877 : Reach 139877 := rs (se 4 (by rfl) ⟨13113, by rfl⟩) (B 26227 (by norm_num) ⟨13113, by rfl⟩ (by norm_num))
theorem R74341 : Reach 74341 := rs (se 4 (by rfl) ⟨6969, by rfl⟩) (B 13939 (by norm_num) ⟨6969, by rfl⟩ (by norm_num))
theorem R74345 : Reach 74345 := rs (se 2 (by rfl) ⟨27879, by rfl⟩) (B 55759 (by norm_num) ⟨27879, by rfl⟩ (by norm_num))
theorem R107117 : Reach 107117 := rs (se 3 (by rfl) ⟨20084, by rfl⟩) (B 40169 (by norm_num) ⟨20084, by rfl⟩ (by norm_num))
theorem R74349 : Reach 74349 := rs (se 3 (by rfl) ⟨13940, by rfl⟩) (B 27881 (by norm_num) ⟨13940, by rfl⟩ (by norm_num))
theorem R74353 : Reach 74353 := rs (se 2 (by rfl) ⟨27882, by rfl⟩) (B 55765 (by norm_num) ⟨27882, by rfl⟩ (by norm_num))
theorem R74357 : Reach 74357 := rs (se 5 (by rfl) ⟨3485, by rfl⟩) (B 6971 (by norm_num) ⟨3485, by rfl⟩ (by norm_num))
theorem R74361 : Reach 74361 := rs (se 2 (by rfl) ⟨27885, by rfl⟩) (B 55771 (by norm_num) ⟨27885, by rfl⟩ (by norm_num))
theorem R74365 : Reach 74365 := rs (se 3 (by rfl) ⟨13943, by rfl⟩) (B 27887 (by norm_num) ⟨13943, by rfl⟩ (by norm_num))
theorem R74369 : Reach 74369 := rs (se 2 (by rfl) ⟨27888, by rfl⟩) (B 55777 (by norm_num) ⟨27888, by rfl⟩ (by norm_num))
theorem R107141 : Reach 107141 := rs (se 4 (by rfl) ⟨10044, by rfl⟩) (B 20089 (by norm_num) ⟨10044, by rfl⟩ (by norm_num))
theorem R74373 : Reach 74373 := rs (se 4 (by rfl) ⟨6972, by rfl⟩) (B 13945 (by norm_num) ⟨6972, by rfl⟩ (by norm_num))
theorem R74377 : Reach 74377 := rs (se 2 (by rfl) ⟨27891, by rfl⟩) (B 55783 (by norm_num) ⟨27891, by rfl⟩ (by norm_num))
theorem R74381 : Reach 74381 := rs (se 3 (by rfl) ⟨13946, by rfl⟩) (B 27893 (by norm_num) ⟨13946, by rfl⟩ (by norm_num))
theorem R74385 : Reach 74385 := rs (se 2 (by rfl) ⟨27894, by rfl⟩) (B 55789 (by norm_num) ⟨27894, by rfl⟩ (by norm_num))
theorem R74389 : Reach 74389 := rs (se 6 (by rfl) ⟨1743, by rfl⟩) (B 3487 (by norm_num) ⟨1743, by rfl⟩ (by norm_num))
theorem R74393 : Reach 74393 := rs (se 2 (by rfl) ⟨27897, by rfl⟩) (B 55795 (by norm_num) ⟨27897, by rfl⟩ (by norm_num))
theorem R107165 : Reach 107165 := rs (se 3 (by rfl) ⟨20093, by rfl⟩) (B 40187 (by norm_num) ⟨20093, by rfl⟩ (by norm_num))
theorem R74397 : Reach 74397 := rs (se 3 (by rfl) ⟨13949, by rfl⟩) (B 27899 (by norm_num) ⟨13949, by rfl⟩ (by norm_num))
theorem R74401 : Reach 74401 := rs (se 2 (by rfl) ⟨27900, by rfl⟩) (B 55801 (by norm_num) ⟨27900, by rfl⟩ (by norm_num))
theorem R74405 : Reach 74405 := rs (se 4 (by rfl) ⟨6975, by rfl⟩) (B 13951 (by norm_num) ⟨6975, by rfl⟩ (by norm_num))
theorem R74409 : Reach 74409 := rs (se 2 (by rfl) ⟨27903, by rfl⟩) (B 55807 (by norm_num) ⟨27903, by rfl⟩ (by norm_num))
theorem R74413 : Reach 74413 := rs (se 3 (by rfl) ⟨13952, by rfl⟩) (B 27905 (by norm_num) ⟨13952, by rfl⟩ (by norm_num))
theorem R74417 : Reach 74417 := rs (se 2 (by rfl) ⟨27906, by rfl⟩) (B 55813 (by norm_num) ⟨27906, by rfl⟩ (by norm_num))
theorem R107189 : Reach 107189 := rs (se 5 (by rfl) ⟨5024, by rfl⟩) (B 10049 (by norm_num) ⟨5024, by rfl⟩ (by norm_num))
theorem R74421 : Reach 74421 := rs (se 5 (by rfl) ⟨3488, by rfl⟩) (B 6977 (by norm_num) ⟨3488, by rfl⟩ (by norm_num))
theorem R74425 : Reach 74425 := rs (se 2 (by rfl) ⟨27909, by rfl⟩) (B 55819 (by norm_num) ⟨27909, by rfl⟩ (by norm_num))
theorem R74429 : Reach 74429 := rs (se 3 (by rfl) ⟨13955, by rfl⟩) (B 27911 (by norm_num) ⟨13955, by rfl⟩ (by norm_num))
theorem R74433 : Reach 74433 := rs (se 2 (by rfl) ⟨27912, by rfl⟩) (B 55825 (by norm_num) ⟨27912, by rfl⟩ (by norm_num))
theorem R74437 : Reach 74437 := rs (se 4 (by rfl) ⟨6978, by rfl⟩) (B 13957 (by norm_num) ⟨6978, by rfl⟩ (by norm_num))
theorem R74441 : Reach 74441 := rs (se 2 (by rfl) ⟨27915, by rfl⟩) (B 55831 (by norm_num) ⟨27915, by rfl⟩ (by norm_num))
theorem R107213 : Reach 107213 := rs (se 3 (by rfl) ⟨20102, by rfl⟩) (B 40205 (by norm_num) ⟨20102, by rfl⟩ (by norm_num))
theorem R74445 : Reach 74445 := rs (se 3 (by rfl) ⟨13958, by rfl⟩) (B 27917 (by norm_num) ⟨13958, by rfl⟩ (by norm_num))
theorem R74449 : Reach 74449 := rs (se 2 (by rfl) ⟨27918, by rfl⟩) (B 55837 (by norm_num) ⟨27918, by rfl⟩ (by norm_num))
theorem R74453 : Reach 74453 := rs (se 7 (by rfl) ⟨872, by rfl⟩) (B 1745 (by norm_num) ⟨872, by rfl⟩ (by norm_num))
theorem R74457 : Reach 74457 := rs (se 2 (by rfl) ⟨27921, by rfl⟩) (B 55843 (by norm_num) ⟨27921, by rfl⟩ (by norm_num))
theorem R74461 : Reach 74461 := rs (se 3 (by rfl) ⟨13961, by rfl⟩) (B 27923 (by norm_num) ⟨13961, by rfl⟩ (by norm_num))
theorem R74465 : Reach 74465 := rs (se 2 (by rfl) ⟨27924, by rfl⟩) (B 55849 (by norm_num) ⟨27924, by rfl⟩ (by norm_num))
theorem R107237 : Reach 107237 := rs (se 4 (by rfl) ⟨10053, by rfl⟩) (B 20107 (by norm_num) ⟨10053, by rfl⟩ (by norm_num))
theorem R74469 : Reach 74469 := rs (se 4 (by rfl) ⟨6981, by rfl⟩) (B 13963 (by norm_num) ⟨6981, by rfl⟩ (by norm_num))
theorem R74473 : Reach 74473 := rs (se 2 (by rfl) ⟨27927, by rfl⟩) (B 55855 (by norm_num) ⟨27927, by rfl⟩ (by norm_num))
theorem R74477 : Reach 74477 := rs (se 3 (by rfl) ⟨13964, by rfl⟩) (B 27929 (by norm_num) ⟨13964, by rfl⟩ (by norm_num))
theorem R74481 : Reach 74481 := rs (se 2 (by rfl) ⟨27930, by rfl⟩) (B 55861 (by norm_num) ⟨27930, by rfl⟩ (by norm_num))
theorem R74485 : Reach 74485 := rs (se 5 (by rfl) ⟨3491, by rfl⟩) (B 6983 (by norm_num) ⟨3491, by rfl⟩ (by norm_num))
theorem R74489 : Reach 74489 := rs (se 2 (by rfl) ⟨27933, by rfl⟩) (B 55867 (by norm_num) ⟨27933, by rfl⟩ (by norm_num))
theorem R107261 : Reach 107261 := rs (se 3 (by rfl) ⟨20111, by rfl⟩) (B 40223 (by norm_num) ⟨20111, by rfl⟩ (by norm_num))
theorem R74493 : Reach 74493 := rs (se 3 (by rfl) ⟨13967, by rfl⟩) (B 27935 (by norm_num) ⟨13967, by rfl⟩ (by norm_num))
theorem R74497 : Reach 74497 := rs (se 2 (by rfl) ⟨27936, by rfl⟩) (B 55873 (by norm_num) ⟨27936, by rfl⟩ (by norm_num))
theorem R74501 : Reach 74501 := rs (se 4 (by rfl) ⟨6984, by rfl⟩) (B 13969 (by norm_num) ⟨6984, by rfl⟩ (by norm_num))
theorem R74505 : Reach 74505 := rs (se 2 (by rfl) ⟨27939, by rfl⟩) (B 55879 (by norm_num) ⟨27939, by rfl⟩ (by norm_num))
theorem R74509 : Reach 74509 := rs (se 3 (by rfl) ⟨13970, by rfl⟩) (B 27941 (by norm_num) ⟨13970, by rfl⟩ (by norm_num))
theorem R74513 : Reach 74513 := rs (se 2 (by rfl) ⟨27942, by rfl⟩) (B 55885 (by norm_num) ⟨27942, by rfl⟩ (by norm_num))
theorem R107285 : Reach 107285 := rs (se 6 (by rfl) ⟨2514, by rfl⟩) (B 5029 (by norm_num) ⟨2514, by rfl⟩ (by norm_num))
theorem R74517 : Reach 74517 := rs (se 6 (by rfl) ⟨1746, by rfl⟩) (B 3493 (by norm_num) ⟨1746, by rfl⟩ (by norm_num))
theorem R74521 : Reach 74521 := rs (se 2 (by rfl) ⟨27945, by rfl⟩) (B 55891 (by norm_num) ⟨27945, by rfl⟩ (by norm_num))
theorem R74525 : Reach 74525 := rs (se 3 (by rfl) ⟨13973, by rfl⟩) (B 27947 (by norm_num) ⟨13973, by rfl⟩ (by norm_num))
theorem R74529 : Reach 74529 := rs (se 2 (by rfl) ⟨27948, by rfl⟩) (B 55897 (by norm_num) ⟨27948, by rfl⟩ (by norm_num))
theorem R74533 : Reach 74533 := rs (se 4 (by rfl) ⟨6987, by rfl⟩) (B 13975 (by norm_num) ⟨6987, by rfl⟩ (by norm_num))
theorem R74537 : Reach 74537 := rs (se 2 (by rfl) ⟨27951, by rfl⟩) (B 55903 (by norm_num) ⟨27951, by rfl⟩ (by norm_num))
theorem R107309 : Reach 107309 := rs (se 3 (by rfl) ⟨20120, by rfl⟩) (B 40241 (by norm_num) ⟨20120, by rfl⟩ (by norm_num))
theorem R74541 : Reach 74541 := rs (se 3 (by rfl) ⟨13976, by rfl⟩) (B 27953 (by norm_num) ⟨13976, by rfl⟩ (by norm_num))
theorem R74545 : Reach 74545 := rs (se 2 (by rfl) ⟨27954, by rfl⟩) (B 55909 (by norm_num) ⟨27954, by rfl⟩ (by norm_num))
theorem R303925 : Reach 303925 := rs (se 5 (by rfl) ⟨14246, by rfl⟩) (B 28493 (by norm_num) ⟨14246, by rfl⟩ (by norm_num))
theorem R74549 : Reach 74549 := rs (se 5 (by rfl) ⟨3494, by rfl⟩) (B 6989 (by norm_num) ⟨3494, by rfl⟩ (by norm_num))
theorem R74553 : Reach 74553 := rs (se 2 (by rfl) ⟨27957, by rfl⟩) (B 55915 (by norm_num) ⟨27957, by rfl⟩ (by norm_num))
theorem R74557 : Reach 74557 := rs (se 3 (by rfl) ⟨13979, by rfl⟩) (B 27959 (by norm_num) ⟨13979, by rfl⟩ (by norm_num))
theorem R74561 : Reach 74561 := rs (se 2 (by rfl) ⟨27960, by rfl⟩) (B 55921 (by norm_num) ⟨27960, by rfl⟩ (by norm_num))
theorem R107333 : Reach 107333 := rs (se 4 (by rfl) ⟨10062, by rfl⟩) (B 20125 (by norm_num) ⟨10062, by rfl⟩ (by norm_num))
theorem R74565 : Reach 74565 := rs (se 4 (by rfl) ⟨6990, by rfl⟩) (B 13981 (by norm_num) ⟨6990, by rfl⟩ (by norm_num))
theorem R74569 : Reach 74569 := rs (se 2 (by rfl) ⟨27963, by rfl⟩) (B 55927 (by norm_num) ⟨27963, by rfl⟩ (by norm_num))
theorem R74573 : Reach 74573 := rs (se 3 (by rfl) ⟨13982, by rfl⟩) (B 27965 (by norm_num) ⟨13982, by rfl⟩ (by norm_num))
theorem R74577 : Reach 74577 := rs (se 2 (by rfl) ⟨27966, by rfl⟩) (B 55933 (by norm_num) ⟨27966, by rfl⟩ (by norm_num))
theorem R74581 : Reach 74581 := rs (se 9 (by rfl) ⟨218, by rfl⟩) (B 437 (by norm_num) ⟨218, by rfl⟩ (by norm_num))
theorem R74585 : Reach 74585 := rs (se 2 (by rfl) ⟨27969, by rfl⟩) (B 55939 (by norm_num) ⟨27969, by rfl⟩ (by norm_num))
theorem R107357 : Reach 107357 := rs (se 3 (by rfl) ⟨20129, by rfl⟩) (B 40259 (by norm_num) ⟨20129, by rfl⟩ (by norm_num))
theorem R74589 : Reach 74589 := rs (se 3 (by rfl) ⟨13985, by rfl⟩) (B 27971 (by norm_num) ⟨13985, by rfl⟩ (by norm_num))
theorem R74593 : Reach 74593 := rs (se 2 (by rfl) ⟨27972, by rfl⟩) (B 55945 (by norm_num) ⟨27972, by rfl⟩ (by norm_num))
theorem R205669 : Reach 205669 := rs (se 4 (by rfl) ⟨19281, by rfl⟩) (B 38563 (by norm_num) ⟨19281, by rfl⟩ (by norm_num))
theorem R74597 : Reach 74597 := rs (se 4 (by rfl) ⟨6993, by rfl⟩) (B 13987 (by norm_num) ⟨6993, by rfl⟩ (by norm_num))
theorem R74601 : Reach 74601 := rs (se 2 (by rfl) ⟨27975, by rfl⟩) (B 55951 (by norm_num) ⟨27975, by rfl⟩ (by norm_num))
theorem R74605 : Reach 74605 := rs (se 3 (by rfl) ⟨13988, by rfl⟩) (B 27977 (by norm_num) ⟨13988, by rfl⟩ (by norm_num))
theorem R74609 : Reach 74609 := rs (se 2 (by rfl) ⟨27978, by rfl⟩) (B 55957 (by norm_num) ⟨27978, by rfl⟩ (by norm_num))
theorem R107381 : Reach 107381 := rs (se 5 (by rfl) ⟨5033, by rfl⟩) (B 10067 (by norm_num) ⟨5033, by rfl⟩ (by norm_num))
theorem R74613 : Reach 74613 := rs (se 5 (by rfl) ⟨3497, by rfl⟩) (B 6995 (by norm_num) ⟨3497, by rfl⟩ (by norm_num))
theorem R74617 : Reach 74617 := rs (se 2 (by rfl) ⟨27981, by rfl⟩) (B 55963 (by norm_num) ⟨27981, by rfl⟩ (by norm_num))
theorem R74621 : Reach 74621 := rs (se 3 (by rfl) ⟨13991, by rfl⟩) (B 27983 (by norm_num) ⟨13991, by rfl⟩ (by norm_num))
theorem R74625 : Reach 74625 := rs (se 2 (by rfl) ⟨27984, by rfl⟩) (B 55969 (by norm_num) ⟨27984, by rfl⟩ (by norm_num))
theorem R74629 : Reach 74629 := rs (se 4 (by rfl) ⟨6996, by rfl⟩) (B 13993 (by norm_num) ⟨6996, by rfl⟩ (by norm_num))
theorem R74633 : Reach 74633 := rs (se 2 (by rfl) ⟨27987, by rfl⟩) (B 55975 (by norm_num) ⟨27987, by rfl⟩ (by norm_num))
theorem R107405 : Reach 107405 := rs (se 3 (by rfl) ⟨20138, by rfl⟩) (B 40277 (by norm_num) ⟨20138, by rfl⟩ (by norm_num))
theorem R74637 : Reach 74637 := rs (se 3 (by rfl) ⟨13994, by rfl⟩) (B 27989 (by norm_num) ⟨13994, by rfl⟩ (by norm_num))
theorem R74641 : Reach 74641 := rs (se 2 (by rfl) ⟨27990, by rfl⟩) (B 55981 (by norm_num) ⟨27990, by rfl⟩ (by norm_num))
theorem R74645 : Reach 74645 := rs (se 6 (by rfl) ⟨1749, by rfl⟩) (B 3499 (by norm_num) ⟨1749, by rfl⟩ (by norm_num))
theorem R74649 : Reach 74649 := rs (se 2 (by rfl) ⟨27993, by rfl⟩) (B 55987 (by norm_num) ⟨27993, by rfl⟩ (by norm_num))
theorem R74653 : Reach 74653 := rs (se 3 (by rfl) ⟨13997, by rfl⟩) (B 27995 (by norm_num) ⟨13997, by rfl⟩ (by norm_num))
theorem R74657 : Reach 74657 := rs (se 2 (by rfl) ⟨27996, by rfl⟩) (B 55993 (by norm_num) ⟨27996, by rfl⟩ (by norm_num))
theorem R107429 : Reach 107429 := rs (se 4 (by rfl) ⟨10071, by rfl⟩) (B 20143 (by norm_num) ⟨10071, by rfl⟩ (by norm_num))
theorem R74661 : Reach 74661 := rs (se 4 (by rfl) ⟨6999, by rfl⟩) (B 13999 (by norm_num) ⟨6999, by rfl⟩ (by norm_num))
theorem R74665 : Reach 74665 := rs (se 2 (by rfl) ⟨27999, by rfl⟩) (B 55999 (by norm_num) ⟨27999, by rfl⟩ (by norm_num))
theorem R74669 : Reach 74669 := rs (se 3 (by rfl) ⟨14000, by rfl⟩) (B 28001 (by norm_num) ⟨14000, by rfl⟩ (by norm_num))
theorem R74673 : Reach 74673 := rs (se 2 (by rfl) ⟨28002, by rfl⟩) (B 56005 (by norm_num) ⟨28002, by rfl⟩ (by norm_num))
theorem R74677 : Reach 74677 := rs (se 5 (by rfl) ⟨3500, by rfl⟩) (B 7001 (by norm_num) ⟨3500, by rfl⟩ (by norm_num))
theorem R74681 : Reach 74681 := rs (se 2 (by rfl) ⟨28005, by rfl⟩) (B 56011 (by norm_num) ⟨28005, by rfl⟩ (by norm_num))
theorem R107453 : Reach 107453 := rs (se 3 (by rfl) ⟨20147, by rfl⟩) (B 40295 (by norm_num) ⟨20147, by rfl⟩ (by norm_num))
theorem R74685 : Reach 74685 := rs (se 3 (by rfl) ⟨14003, by rfl⟩) (B 28007 (by norm_num) ⟨14003, by rfl⟩ (by norm_num))
theorem R74689 : Reach 74689 := rs (se 2 (by rfl) ⟨28008, by rfl⟩) (B 56017 (by norm_num) ⟨28008, by rfl⟩ (by norm_num))
theorem R74693 : Reach 74693 := rs (se 4 (by rfl) ⟨7002, by rfl⟩) (B 14005 (by norm_num) ⟨7002, by rfl⟩ (by norm_num))
theorem R74697 : Reach 74697 := rs (se 2 (by rfl) ⟨28011, by rfl⟩) (B 56023 (by norm_num) ⟨28011, by rfl⟩ (by norm_num))
theorem R74701 : Reach 74701 := rs (se 3 (by rfl) ⟨14006, by rfl⟩) (B 28013 (by norm_num) ⟨14006, by rfl⟩ (by norm_num))
theorem R74705 : Reach 74705 := rs (se 2 (by rfl) ⟨28014, by rfl⟩) (B 56029 (by norm_num) ⟨28014, by rfl⟩ (by norm_num))
theorem R107477 : Reach 107477 := rs (se 7 (by rfl) ⟨1259, by rfl⟩) (B 2519 (by norm_num) ⟨1259, by rfl⟩ (by norm_num))
theorem R74709 : Reach 74709 := rs (se 7 (by rfl) ⟨875, by rfl⟩) (B 1751 (by norm_num) ⟨875, by rfl⟩ (by norm_num))
theorem R74713 : Reach 74713 := rs (se 2 (by rfl) ⟨28017, by rfl⟩) (B 56035 (by norm_num) ⟨28017, by rfl⟩ (by norm_num))
theorem R74717 : Reach 74717 := rs (se 3 (by rfl) ⟨14009, by rfl⟩) (B 28019 (by norm_num) ⟨14009, by rfl⟩ (by norm_num))
theorem R74721 : Reach 74721 := rs (se 2 (by rfl) ⟨28020, by rfl⟩) (B 56041 (by norm_num) ⟨28020, by rfl⟩ (by norm_num))
theorem R74725 : Reach 74725 := rs (se 4 (by rfl) ⟨7005, by rfl⟩) (B 14011 (by norm_num) ⟨7005, by rfl⟩ (by norm_num))
theorem R74729 : Reach 74729 := rs (se 2 (by rfl) ⟨28023, by rfl⟩) (B 56047 (by norm_num) ⟨28023, by rfl⟩ (by norm_num))
theorem R107501 : Reach 107501 := rs (se 3 (by rfl) ⟨20156, by rfl⟩) (B 40313 (by norm_num) ⟨20156, by rfl⟩ (by norm_num))
theorem R74733 : Reach 74733 := rs (se 3 (by rfl) ⟨14012, by rfl⟩) (B 28025 (by norm_num) ⟨14012, by rfl⟩ (by norm_num))
theorem R74737 : Reach 74737 := rs (se 2 (by rfl) ⟨28026, by rfl⟩) (B 56053 (by norm_num) ⟨28026, by rfl⟩ (by norm_num))
theorem R74741 : Reach 74741 := rs (se 5 (by rfl) ⟨3503, by rfl⟩) (B 7007 (by norm_num) ⟨3503, by rfl⟩ (by norm_num))
theorem R74745 : Reach 74745 := rs (se 2 (by rfl) ⟨28029, by rfl⟩) (B 56059 (by norm_num) ⟨28029, by rfl⟩ (by norm_num))
theorem R74749 : Reach 74749 := rs (se 3 (by rfl) ⟨14015, by rfl⟩) (B 28031 (by norm_num) ⟨14015, by rfl⟩ (by norm_num))
theorem R74753 : Reach 74753 := rs (se 2 (by rfl) ⟨28032, by rfl⟩) (B 56065 (by norm_num) ⟨28032, by rfl⟩ (by norm_num))
theorem R107525 : Reach 107525 := rs (se 4 (by rfl) ⟨10080, by rfl⟩) (B 20161 (by norm_num) ⟨10080, by rfl⟩ (by norm_num))
theorem R74757 : Reach 74757 := rs (se 4 (by rfl) ⟨7008, by rfl⟩) (B 14017 (by norm_num) ⟨7008, by rfl⟩ (by norm_num))
theorem R74761 : Reach 74761 := rs (se 2 (by rfl) ⟨28035, by rfl⟩) (B 56071 (by norm_num) ⟨28035, by rfl⟩ (by norm_num))
theorem R74765 : Reach 74765 := rs (se 3 (by rfl) ⟨14018, by rfl⟩) (B 28037 (by norm_num) ⟨14018, by rfl⟩ (by norm_num))
theorem R74769 : Reach 74769 := rs (se 2 (by rfl) ⟨28038, by rfl⟩) (B 56077 (by norm_num) ⟨28038, by rfl⟩ (by norm_num))
theorem R926741 : Reach 926741 := rs (se 6 (by rfl) ⟨21720, by rfl⟩) (B 43441 (by norm_num) ⟨21720, by rfl⟩ (by norm_num))
theorem R74773 : Reach 74773 := rs (se 6 (by rfl) ⟨1752, by rfl⟩) (B 3505 (by norm_num) ⟨1752, by rfl⟩ (by norm_num))
theorem R74777 : Reach 74777 := rs (se 2 (by rfl) ⟨28041, by rfl⟩) (B 56083 (by norm_num) ⟨28041, by rfl⟩ (by norm_num))
theorem R107549 : Reach 107549 := rs (se 3 (by rfl) ⟨20165, by rfl⟩) (B 40331 (by norm_num) ⟨20165, by rfl⟩ (by norm_num))
theorem R74781 : Reach 74781 := rs (se 3 (by rfl) ⟨14021, by rfl⟩) (B 28043 (by norm_num) ⟨14021, by rfl⟩ (by norm_num))
theorem R74785 : Reach 74785 := rs (se 2 (by rfl) ⟨28044, by rfl⟩) (B 56089 (by norm_num) ⟨28044, by rfl⟩ (by norm_num))
theorem R74789 : Reach 74789 := rs (se 4 (by rfl) ⟨7011, by rfl⟩) (B 14023 (by norm_num) ⟨7011, by rfl⟩ (by norm_num))
theorem R74793 : Reach 74793 := rs (se 2 (by rfl) ⟨28047, by rfl⟩) (B 56095 (by norm_num) ⟨28047, by rfl⟩ (by norm_num))
theorem R74797 : Reach 74797 := rs (se 3 (by rfl) ⟨14024, by rfl⟩) (B 28049 (by norm_num) ⟨14024, by rfl⟩ (by norm_num))
theorem R74801 : Reach 74801 := rs (se 2 (by rfl) ⟨28050, by rfl⟩) (B 56101 (by norm_num) ⟨28050, by rfl⟩ (by norm_num))
theorem R107573 : Reach 107573 := rs (se 5 (by rfl) ⟨5042, by rfl⟩) (B 10085 (by norm_num) ⟨5042, by rfl⟩ (by norm_num))
theorem R74805 : Reach 74805 := rs (se 5 (by rfl) ⟨3506, by rfl⟩) (B 7013 (by norm_num) ⟨3506, by rfl⟩ (by norm_num))
theorem R74809 : Reach 74809 := rs (se 2 (by rfl) ⟨28053, by rfl⟩) (B 56107 (by norm_num) ⟨28053, by rfl⟩ (by norm_num))
theorem R74813 : Reach 74813 := rs (se 3 (by rfl) ⟨14027, by rfl⟩) (B 28055 (by norm_num) ⟨14027, by rfl⟩ (by norm_num))
theorem R74817 : Reach 74817 := rs (se 2 (by rfl) ⟨28056, by rfl⟩) (B 56113 (by norm_num) ⟨28056, by rfl⟩ (by norm_num))
theorem R74821 : Reach 74821 := rs (se 4 (by rfl) ⟨7014, by rfl⟩) (B 14029 (by norm_num) ⟨7014, by rfl⟩ (by norm_num))
theorem R107597 : Reach 107597 := rs (se 3 (by rfl) ⟨20174, by rfl⟩) (B 40349 (by norm_num) ⟨20174, by rfl⟩ (by norm_num))
theorem R74825 : Reach 74825 := rs (se 2 (by rfl) ⟨28059, by rfl⟩) (B 56119 (by norm_num) ⟨28059, by rfl⟩ (by norm_num))
theorem R74829 : Reach 74829 := rs (se 3 (by rfl) ⟨14030, by rfl⟩) (B 28061 (by norm_num) ⟨14030, by rfl⟩ (by norm_num))
theorem R74833 : Reach 74833 := rs (se 2 (by rfl) ⟨28062, by rfl⟩) (B 56125 (by norm_num) ⟨28062, by rfl⟩ (by norm_num))
theorem R74837 : Reach 74837 := rs (se 8 (by rfl) ⟨438, by rfl⟩) (B 877 (by norm_num) ⟨438, by rfl⟩ (by norm_num))
theorem R74841 : Reach 74841 := rs (se 2 (by rfl) ⟨28065, by rfl⟩) (B 56131 (by norm_num) ⟨28065, by rfl⟩ (by norm_num))
theorem R74845 : Reach 74845 := rs (se 3 (by rfl) ⟨14033, by rfl⟩) (B 28067 (by norm_num) ⟨14033, by rfl⟩ (by norm_num))
theorem R74849 : Reach 74849 := rs (se 2 (by rfl) ⟨28068, by rfl⟩) (B 56137 (by norm_num) ⟨28068, by rfl⟩ (by norm_num))
theorem R107621 : Reach 107621 := rs (se 4 (by rfl) ⟨10089, by rfl⟩) (B 20179 (by norm_num) ⟨10089, by rfl⟩ (by norm_num))
theorem R74853 : Reach 74853 := rs (se 4 (by rfl) ⟨7017, by rfl⟩) (B 14035 (by norm_num) ⟨7017, by rfl⟩ (by norm_num))
theorem R74857 : Reach 74857 := rs (se 2 (by rfl) ⟨28071, by rfl⟩) (B 56143 (by norm_num) ⟨28071, by rfl⟩ (by norm_num))
theorem R74861 : Reach 74861 := rs (se 3 (by rfl) ⟨14036, by rfl⟩) (B 28073 (by norm_num) ⟨14036, by rfl⟩ (by norm_num))
theorem R74865 : Reach 74865 := rs (se 2 (by rfl) ⟨28074, by rfl⟩) (B 56149 (by norm_num) ⟨28074, by rfl⟩ (by norm_num))
theorem R74869 : Reach 74869 := rs (se 5 (by rfl) ⟨3509, by rfl⟩) (B 7019 (by norm_num) ⟨3509, by rfl⟩ (by norm_num))
theorem R74873 : Reach 74873 := rs (se 2 (by rfl) ⟨28077, by rfl⟩) (B 56155 (by norm_num) ⟨28077, by rfl⟩ (by norm_num))
theorem R107645 : Reach 107645 := rs (se 3 (by rfl) ⟨20183, by rfl⟩) (B 40367 (by norm_num) ⟨20183, by rfl⟩ (by norm_num))
theorem R74877 : Reach 74877 := rs (se 3 (by rfl) ⟨14039, by rfl⟩) (B 28079 (by norm_num) ⟨14039, by rfl⟩ (by norm_num))
theorem R74881 : Reach 74881 := rs (se 2 (by rfl) ⟨28080, by rfl⟩) (B 56161 (by norm_num) ⟨28080, by rfl⟩ (by norm_num))
theorem R74885 : Reach 74885 := rs (se 4 (by rfl) ⟨7020, by rfl⟩) (B 14041 (by norm_num) ⟨7020, by rfl⟩ (by norm_num))
theorem R74889 : Reach 74889 := rs (se 2 (by rfl) ⟨28083, by rfl⟩) (B 56167 (by norm_num) ⟨28083, by rfl⟩ (by norm_num))
theorem R74893 : Reach 74893 := rs (se 3 (by rfl) ⟨14042, by rfl⟩) (B 28085 (by norm_num) ⟨14042, by rfl⟩ (by norm_num))
theorem R74897 : Reach 74897 := rs (se 2 (by rfl) ⟨28086, by rfl⟩) (B 56173 (by norm_num) ⟨28086, by rfl⟩ (by norm_num))
theorem R107669 : Reach 107669 := rs (se 6 (by rfl) ⟨2523, by rfl⟩) (B 5047 (by norm_num) ⟨2523, by rfl⟩ (by norm_num))
theorem R74901 : Reach 74901 := rs (se 6 (by rfl) ⟨1755, by rfl⟩) (B 3511 (by norm_num) ⟨1755, by rfl⟩ (by norm_num))
theorem R74905 : Reach 74905 := rs (se 2 (by rfl) ⟨28089, by rfl⟩) (B 56179 (by norm_num) ⟨28089, by rfl⟩ (by norm_num))
theorem R74909 : Reach 74909 := rs (se 3 (by rfl) ⟨14045, by rfl⟩) (B 28091 (by norm_num) ⟨14045, by rfl⟩ (by norm_num))
theorem R74913 : Reach 74913 := rs (se 2 (by rfl) ⟨28092, by rfl⟩) (B 56185 (by norm_num) ⟨28092, by rfl⟩ (by norm_num))
theorem R74917 : Reach 74917 := rs (se 4 (by rfl) ⟨7023, by rfl⟩) (B 14047 (by norm_num) ⟨7023, by rfl⟩ (by norm_num))
theorem R74921 : Reach 74921 := rs (se 2 (by rfl) ⟨28095, by rfl⟩) (B 56191 (by norm_num) ⟨28095, by rfl⟩ (by norm_num))
theorem R107693 : Reach 107693 := rs (se 3 (by rfl) ⟨20192, by rfl⟩) (B 40385 (by norm_num) ⟨20192, by rfl⟩ (by norm_num))
theorem R74925 : Reach 74925 := rs (se 3 (by rfl) ⟨14048, by rfl⟩) (B 28097 (by norm_num) ⟨14048, by rfl⟩ (by norm_num))
theorem R74929 : Reach 74929 := rs (se 2 (by rfl) ⟨28098, by rfl⟩) (B 56197 (by norm_num) ⟨28098, by rfl⟩ (by norm_num))
theorem R369845 : Reach 369845 := rs (se 5 (by rfl) ⟨17336, by rfl⟩) (B 34673 (by norm_num) ⟨17336, by rfl⟩ (by norm_num))
theorem R74933 : Reach 74933 := rs (se 5 (by rfl) ⟨3512, by rfl⟩) (B 7025 (by norm_num) ⟨3512, by rfl⟩ (by norm_num))
theorem R74937 : Reach 74937 := rs (se 2 (by rfl) ⟨28101, by rfl⟩) (B 56203 (by norm_num) ⟨28101, by rfl⟩ (by norm_num))
theorem R74941 : Reach 74941 := rs (se 3 (by rfl) ⟨14051, by rfl⟩) (B 28103 (by norm_num) ⟨14051, by rfl⟩ (by norm_num))
theorem R74945 : Reach 74945 := rs (se 2 (by rfl) ⟨28104, by rfl⟩) (B 56209 (by norm_num) ⟨28104, by rfl⟩ (by norm_num))
theorem R107717 : Reach 107717 := rs (se 4 (by rfl) ⟨10098, by rfl⟩) (B 20197 (by norm_num) ⟨10098, by rfl⟩ (by norm_num))
theorem R74949 : Reach 74949 := rs (se 4 (by rfl) ⟨7026, by rfl⟩) (B 14053 (by norm_num) ⟨7026, by rfl⟩ (by norm_num))
theorem R74953 : Reach 74953 := rs (se 2 (by rfl) ⟨28107, by rfl⟩) (B 56215 (by norm_num) ⟨28107, by rfl⟩ (by norm_num))
theorem R74957 : Reach 74957 := rs (se 3 (by rfl) ⟨14054, by rfl⟩) (B 28109 (by norm_num) ⟨14054, by rfl⟩ (by norm_num))
theorem R74961 : Reach 74961 := rs (se 2 (by rfl) ⟨28110, by rfl⟩) (B 56221 (by norm_num) ⟨28110, by rfl⟩ (by norm_num))
theorem R74965 : Reach 74965 := rs (se 7 (by rfl) ⟨878, by rfl⟩) (B 1757 (by norm_num) ⟨878, by rfl⟩ (by norm_num))
theorem R74969 : Reach 74969 := rs (se 2 (by rfl) ⟨28113, by rfl⟩) (B 56227 (by norm_num) ⟨28113, by rfl⟩ (by norm_num))
theorem R107741 : Reach 107741 := rs (se 3 (by rfl) ⟨20201, by rfl⟩) (B 40403 (by norm_num) ⟨20201, by rfl⟩ (by norm_num))
theorem R74973 : Reach 74973 := rs (se 3 (by rfl) ⟨14057, by rfl⟩) (B 28115 (by norm_num) ⟨14057, by rfl⟩ (by norm_num))
theorem R74977 : Reach 74977 := rs (se 2 (by rfl) ⟨28116, by rfl⟩) (B 56233 (by norm_num) ⟨28116, by rfl⟩ (by norm_num))
theorem R74981 : Reach 74981 := rs (se 4 (by rfl) ⟨7029, by rfl⟩) (B 14059 (by norm_num) ⟨7029, by rfl⟩ (by norm_num))
theorem R74985 : Reach 74985 := rs (se 2 (by rfl) ⟨28119, by rfl⟩) (B 56239 (by norm_num) ⟨28119, by rfl⟩ (by norm_num))
theorem R74989 : Reach 74989 := rs (se 3 (by rfl) ⟨14060, by rfl⟩) (B 28121 (by norm_num) ⟨14060, by rfl⟩ (by norm_num))
theorem R74993 : Reach 74993 := rs (se 2 (by rfl) ⟨28122, by rfl⟩) (B 56245 (by norm_num) ⟨28122, by rfl⟩ (by norm_num))
theorem R107765 : Reach 107765 := rs (se 5 (by rfl) ⟨5051, by rfl⟩) (B 10103 (by norm_num) ⟨5051, by rfl⟩ (by norm_num))
theorem R533749 : Reach 533749 := rs (se 5 (by rfl) ⟨25019, by rfl⟩) (B 50039 (by norm_num) ⟨25019, by rfl⟩ (by norm_num))
theorem R74997 : Reach 74997 := rs (se 5 (by rfl) ⟨3515, by rfl⟩) (B 7031 (by norm_num) ⟨3515, by rfl⟩ (by norm_num))
theorem R75001 : Reach 75001 := rs (se 2 (by rfl) ⟨28125, by rfl⟩) (B 56251 (by norm_num) ⟨28125, by rfl⟩ (by norm_num))
theorem R75005 : Reach 75005 := rs (se 3 (by rfl) ⟨14063, by rfl⟩) (B 28127 (by norm_num) ⟨14063, by rfl⟩ (by norm_num))
theorem R75009 : Reach 75009 := rs (se 2 (by rfl) ⟨28128, by rfl⟩) (B 56257 (by norm_num) ⟨28128, by rfl⟩ (by norm_num))
theorem R75013 : Reach 75013 := rs (se 4 (by rfl) ⟨7032, by rfl⟩) (B 14065 (by norm_num) ⟨7032, by rfl⟩ (by norm_num))
theorem R75017 : Reach 75017 := rs (se 2 (by rfl) ⟨28131, by rfl⟩) (B 56263 (by norm_num) ⟨28131, by rfl⟩ (by norm_num))
theorem R107789 : Reach 107789 := rs (se 3 (by rfl) ⟨20210, by rfl⟩) (B 40421 (by norm_num) ⟨20210, by rfl⟩ (by norm_num))
theorem R75021 : Reach 75021 := rs (se 3 (by rfl) ⟨14066, by rfl⟩) (B 28133 (by norm_num) ⟨14066, by rfl⟩ (by norm_num))
theorem R75025 : Reach 75025 := rs (se 2 (by rfl) ⟨28134, by rfl⟩) (B 56269 (by norm_num) ⟨28134, by rfl⟩ (by norm_num))
theorem R75029 : Reach 75029 := rs (se 6 (by rfl) ⟨1758, by rfl⟩) (B 3517 (by norm_num) ⟨1758, by rfl⟩ (by norm_num))
theorem R75033 : Reach 75033 := rs (se 2 (by rfl) ⟨28137, by rfl⟩) (B 56275 (by norm_num) ⟨28137, by rfl⟩ (by norm_num))
theorem R75037 : Reach 75037 := rs (se 3 (by rfl) ⟨14069, by rfl⟩) (B 28139 (by norm_num) ⟨14069, by rfl⟩ (by norm_num))
theorem R75041 : Reach 75041 := rs (se 2 (by rfl) ⟨28140, by rfl⟩) (B 56281 (by norm_num) ⟨28140, by rfl⟩ (by norm_num))
theorem R107813 : Reach 107813 := rs (se 4 (by rfl) ⟨10107, by rfl⟩) (B 20215 (by norm_num) ⟨10107, by rfl⟩ (by norm_num))
theorem R75045 : Reach 75045 := rs (se 4 (by rfl) ⟨7035, by rfl⟩) (B 14071 (by norm_num) ⟨7035, by rfl⟩ (by norm_num))
theorem R75049 : Reach 75049 := rs (se 2 (by rfl) ⟨28143, by rfl⟩) (B 56287 (by norm_num) ⟨28143, by rfl⟩ (by norm_num))
theorem R75053 : Reach 75053 := rs (se 3 (by rfl) ⟨14072, by rfl⟩) (B 28145 (by norm_num) ⟨14072, by rfl⟩ (by norm_num))
theorem R75057 : Reach 75057 := rs (se 2 (by rfl) ⟨28146, by rfl⟩) (B 56293 (by norm_num) ⟨28146, by rfl⟩ (by norm_num))
theorem R75061 : Reach 75061 := rs (se 5 (by rfl) ⟨3518, by rfl⟩) (B 7037 (by norm_num) ⟨3518, by rfl⟩ (by norm_num))
theorem R75065 : Reach 75065 := rs (se 2 (by rfl) ⟨28149, by rfl⟩) (B 56299 (by norm_num) ⟨28149, by rfl⟩ (by norm_num))
theorem R107837 : Reach 107837 := rs (se 3 (by rfl) ⟨20219, by rfl⟩) (B 40439 (by norm_num) ⟨20219, by rfl⟩ (by norm_num))
theorem R75069 : Reach 75069 := rs (se 3 (by rfl) ⟨14075, by rfl⟩) (B 28151 (by norm_num) ⟨14075, by rfl⟩ (by norm_num))
theorem R75073 : Reach 75073 := rs (se 2 (by rfl) ⟨28152, by rfl⟩) (B 56305 (by norm_num) ⟨28152, by rfl⟩ (by norm_num))
theorem R75077 : Reach 75077 := rs (se 4 (by rfl) ⟨7038, by rfl⟩) (B 14077 (by norm_num) ⟨7038, by rfl⟩ (by norm_num))
theorem R75081 : Reach 75081 := rs (se 2 (by rfl) ⟨28155, by rfl⟩) (B 56311 (by norm_num) ⟨28155, by rfl⟩ (by norm_num))
theorem R75085 : Reach 75085 := rs (se 3 (by rfl) ⟨14078, by rfl⟩) (B 28157 (by norm_num) ⟨14078, by rfl⟩ (by norm_num))
theorem R75089 : Reach 75089 := rs (se 2 (by rfl) ⟨28158, by rfl⟩) (B 56317 (by norm_num) ⟨28158, by rfl⟩ (by norm_num))
theorem R107861 : Reach 107861 := rs (se 12 (by rfl) ⟨39, by rfl⟩) (B 79 (by norm_num) ⟨39, by rfl⟩ (by norm_num))
theorem R599381 : Reach 599381 := rs (se 12 (by rfl) ⟨219, by rfl⟩) (B 439 (by norm_num) ⟨219, by rfl⟩ (by norm_num))
theorem R140629 : Reach 140629 := rs (se 12 (by rfl) ⟨51, by rfl⟩) (B 103 (by norm_num) ⟨51, by rfl⟩ (by norm_num))
theorem R75093 : Reach 75093 := rs (se 12 (by rfl) ⟨27, by rfl⟩) (B 55 (by norm_num) ⟨27, by rfl⟩ (by norm_num))
theorem R75097 : Reach 75097 := rs (se 2 (by rfl) ⟨28161, by rfl⟩) (B 56323 (by norm_num) ⟨28161, by rfl⟩ (by norm_num))
theorem R75101 : Reach 75101 := rs (se 3 (by rfl) ⟨14081, by rfl⟩) (B 28163 (by norm_num) ⟨14081, by rfl⟩ (by norm_num))
theorem R75105 : Reach 75105 := rs (se 2 (by rfl) ⟨28164, by rfl⟩) (B 56329 (by norm_num) ⟨28164, by rfl⟩ (by norm_num))
theorem R75109 : Reach 75109 := rs (se 4 (by rfl) ⟨7041, by rfl⟩) (B 14083 (by norm_num) ⟨7041, by rfl⟩ (by norm_num))
theorem R75113 : Reach 75113 := rs (se 2 (by rfl) ⟨28167, by rfl⟩) (B 56335 (by norm_num) ⟨28167, by rfl⟩ (by norm_num))
theorem R107885 : Reach 107885 := rs (se 3 (by rfl) ⟨20228, by rfl⟩) (B 40457 (by norm_num) ⟨20228, by rfl⟩ (by norm_num))
theorem R75117 : Reach 75117 := rs (se 3 (by rfl) ⟨14084, by rfl⟩) (B 28169 (by norm_num) ⟨14084, by rfl⟩ (by norm_num))
theorem R75121 : Reach 75121 := rs (se 2 (by rfl) ⟨28170, by rfl⟩) (B 56341 (by norm_num) ⟨28170, by rfl⟩ (by norm_num))
theorem R75125 : Reach 75125 := rs (se 5 (by rfl) ⟨3521, by rfl⟩) (B 7043 (by norm_num) ⟨3521, by rfl⟩ (by norm_num))
theorem R107909 : Reach 107909 := rs (se 4 (by rfl) ⟨10116, by rfl⟩) (B 20233 (by norm_num) ⟨10116, by rfl⟩ (by norm_num))
theorem R107933 : Reach 107933 := rs (se 3 (by rfl) ⟨20237, by rfl⟩) (B 40475 (by norm_num) ⟨20237, by rfl⟩ (by norm_num))
theorem R271781 : Reach 271781 := rs (se 4 (by rfl) ⟨25479, by rfl⟩) (B 50959 (by norm_num) ⟨25479, by rfl⟩ (by norm_num))
theorem R107957 : Reach 107957 := rs (se 5 (by rfl) ⟨5060, by rfl⟩) (B 10121 (by norm_num) ⟨5060, by rfl⟩ (by norm_num))
theorem R107981 : Reach 107981 := rs (se 3 (by rfl) ⟨20246, by rfl⟩) (B 40493 (by norm_num) ⟨20246, by rfl⟩ (by norm_num))
theorem R959957 : Reach 959957 := rs (se 7 (by rfl) ⟨11249, by rfl⟩) (B 22499 (by norm_num) ⟨11249, by rfl⟩ (by norm_num))
theorem R108005 : Reach 108005 := rs (se 4 (by rfl) ⟨10125, by rfl⟩) (B 20251 (by norm_num) ⟨10125, by rfl⟩ (by norm_num))
theorem R140773 : Reach 140773 := rs (se 4 (by rfl) ⟨13197, by rfl⟩) (B 26395 (by norm_num) ⟨13197, by rfl⟩ (by norm_num))
theorem R108029 : Reach 108029 := rs (se 3 (by rfl) ⟨20255, by rfl⟩) (B 40511 (by norm_num) ⟨20255, by rfl⟩ (by norm_num))
theorem R173573 : Reach 173573 := rs (se 4 (by rfl) ⟨16272, by rfl⟩) (B 32545 (by norm_num) ⟨16272, by rfl⟩ (by norm_num))
theorem R304661 : Reach 304661 := rs (se 6 (by rfl) ⟨7140, by rfl⟩) (B 14281 (by norm_num) ⟨7140, by rfl⟩ (by norm_num))
theorem R108053 : Reach 108053 := rs (se 6 (by rfl) ⟨2532, by rfl⟩) (B 5065 (by norm_num) ⟨2532, by rfl⟩ (by norm_num))
theorem R108077 : Reach 108077 := rs (se 3 (by rfl) ⟨20264, by rfl⟩) (B 40529 (by norm_num) ⟨20264, by rfl⟩ (by norm_num))
theorem R108101 : Reach 108101 := rs (se 4 (by rfl) ⟨10134, by rfl⟩) (B 20269 (by norm_num) ⟨10134, by rfl⟩ (by norm_num))
theorem R108125 : Reach 108125 := rs (se 3 (by rfl) ⟨20273, by rfl⟩) (B 40547 (by norm_num) ⟨20273, by rfl⟩ (by norm_num))
theorem R108149 : Reach 108149 := rs (se 5 (by rfl) ⟨5069, by rfl⟩) (B 10139 (by norm_num) ⟨5069, by rfl⟩ (by norm_num))
theorem R140933 : Reach 140933 := rs (se 4 (by rfl) ⟨13212, by rfl⟩) (B 26425 (by norm_num) ⟨13212, by rfl⟩ (by norm_num))
theorem R108173 : Reach 108173 := rs (se 3 (by rfl) ⟨20282, by rfl⟩) (B 40565 (by norm_num) ⟨20282, by rfl⟩ (by norm_num))
theorem R468629 : Reach 468629 := rs (se 6 (by rfl) ⟨10983, by rfl⟩) (B 21967 (by norm_num) ⟨10983, by rfl⟩ (by norm_num))
theorem R108197 : Reach 108197 := rs (se 4 (by rfl) ⟨10143, by rfl⟩) (B 20287 (by norm_num) ⟨10143, by rfl⟩ (by norm_num))
theorem R108221 : Reach 108221 := rs (se 3 (by rfl) ⟨20291, by rfl⟩) (B 40583 (by norm_num) ⟨20291, by rfl⟩ (by norm_num))
theorem R272069 : Reach 272069 := rs (se 4 (by rfl) ⟨25506, by rfl⟩) (B 51013 (by norm_num) ⟨25506, by rfl⟩ (by norm_num))
theorem R108245 : Reach 108245 := rs (se 7 (by rfl) ⟨1268, by rfl⟩) (B 2537 (by norm_num) ⟨1268, by rfl⟩ (by norm_num))
theorem R108253 : Reach 108253 := rs (se 3 (by rfl) ⟨20297, by rfl⟩) (B 40595 (by norm_num) ⟨20297, by rfl⟩ (by norm_num))
theorem R108269 : Reach 108269 := rs (se 3 (by rfl) ⟨20300, by rfl⟩) (B 40601 (by norm_num) ⟨20300, by rfl⟩ (by norm_num))
theorem R108293 : Reach 108293 := rs (se 4 (by rfl) ⟨10152, by rfl⟩) (B 20305 (by norm_num) ⟨10152, by rfl⟩ (by norm_num))
theorem R141077 : Reach 141077 := rs (se 6 (by rfl) ⟨3306, by rfl⟩) (B 6613 (by norm_num) ⟨3306, by rfl⟩ (by norm_num))
theorem R108317 : Reach 108317 := rs (se 3 (by rfl) ⟨20309, by rfl⟩) (B 40619 (by norm_num) ⟨20309, by rfl⟩ (by norm_num))
theorem R108341 : Reach 108341 := rs (se 5 (by rfl) ⟨5078, by rfl⟩) (B 10157 (by norm_num) ⟨5078, by rfl⟩ (by norm_num))
theorem R108365 : Reach 108365 := rs (se 3 (by rfl) ⟨20318, by rfl⟩) (B 40637 (by norm_num) ⟨20318, by rfl⟩ (by norm_num))
theorem R108389 : Reach 108389 := rs (se 4 (by rfl) ⟨10161, by rfl⟩) (B 20323 (by norm_num) ⟨10161, by rfl⟩ (by norm_num))
theorem R108413 : Reach 108413 := rs (se 3 (by rfl) ⟨20327, by rfl⟩) (B 40655 (by norm_num) ⟨20327, by rfl⟩ (by norm_num))
theorem R108437 : Reach 108437 := rs (se 6 (by rfl) ⟨2541, by rfl⟩) (B 5083 (by norm_num) ⟨2541, by rfl⟩ (by norm_num))
theorem R108461 : Reach 108461 := rs (se 3 (by rfl) ⟨20336, by rfl⟩) (B 40673 (by norm_num) ⟨20336, by rfl⟩ (by norm_num))
theorem R108485 : Reach 108485 := rs (se 4 (by rfl) ⟨10170, by rfl⟩) (B 20341 (by norm_num) ⟨10170, by rfl⟩ (by norm_num))
theorem R108509 : Reach 108509 := rs (se 3 (by rfl) ⟨20345, by rfl⟩) (B 40691 (by norm_num) ⟨20345, by rfl⟩ (by norm_num))
theorem R108533 : Reach 108533 := rs (se 5 (by rfl) ⟨5087, by rfl⟩) (B 10175 (by norm_num) ⟨5087, by rfl⟩ (by norm_num))
theorem R108557 : Reach 108557 := rs (se 3 (by rfl) ⟨20354, by rfl⟩) (B 40709 (by norm_num) ⟨20354, by rfl⟩ (by norm_num))
theorem R108581 : Reach 108581 := rs (se 4 (by rfl) ⟨10179, by rfl⟩) (B 20359 (by norm_num) ⟨10179, by rfl⟩ (by norm_num))
theorem R141365 : Reach 141365 := rs (se 5 (by rfl) ⟨6626, by rfl⟩) (B 13253 (by norm_num) ⟨6626, by rfl⟩ (by norm_num))
theorem R108605 : Reach 108605 := rs (se 3 (by rfl) ⟨20363, by rfl⟩) (B 40727 (by norm_num) ⟨20363, by rfl⟩ (by norm_num))
theorem R108629 : Reach 108629 := rs (se 8 (by rfl) ⟨636, by rfl⟩) (B 1273 (by norm_num) ⟨636, by rfl⟩ (by norm_num))
theorem R108653 : Reach 108653 := rs (se 3 (by rfl) ⟨20372, by rfl⟩) (B 40745 (by norm_num) ⟨20372, by rfl⟩ (by norm_num))
theorem R108677 : Reach 108677 := rs (se 4 (by rfl) ⟨10188, by rfl⟩) (B 20377 (by norm_num) ⟨10188, by rfl⟩ (by norm_num))
theorem R108701 : Reach 108701 := rs (se 3 (by rfl) ⟨20381, by rfl⟩) (B 40763 (by norm_num) ⟨20381, by rfl⟩ (by norm_num))
theorem R108725 : Reach 108725 := rs (se 5 (by rfl) ⟨5096, by rfl⟩) (B 10193 (by norm_num) ⟨5096, by rfl⟩ (by norm_num))
theorem R75973 : Reach 75973 := rs (se 4 (by rfl) ⟨7122, by rfl⟩) (B 14245 (by norm_num) ⟨7122, by rfl⟩ (by norm_num))
theorem R108749 : Reach 108749 := rs (se 3 (by rfl) ⟨20390, by rfl⟩) (B 40781 (by norm_num) ⟨20390, by rfl⟩ (by norm_num))
theorem R141517 : Reach 141517 := rs (se 3 (by rfl) ⟨26534, by rfl⟩) (B 53069 (by norm_num) ⟨26534, by rfl⟩ (by norm_num))
theorem R108773 : Reach 108773 := rs (se 4 (by rfl) ⟨10197, by rfl⟩) (B 20395 (by norm_num) ⟨10197, by rfl⟩ (by norm_num))
theorem R108797 : Reach 108797 := rs (se 3 (by rfl) ⟨20399, by rfl⟩) (B 40799 (by norm_num) ⟨20399, by rfl⟩ (by norm_num))
theorem R108821 : Reach 108821 := rs (se 6 (by rfl) ⟨2550, by rfl⟩) (B 5101 (by norm_num) ⟨2550, by rfl⟩ (by norm_num))
theorem R108845 : Reach 108845 := rs (se 3 (by rfl) ⟨20408, by rfl⟩) (B 40817 (by norm_num) ⟨20408, by rfl⟩ (by norm_num))
theorem R76097 : Reach 76097 := rs (se 2 (by rfl) ⟨28536, by rfl⟩) (B 57073 (by norm_num) ⟨28536, by rfl⟩ (by norm_num))
theorem R108869 : Reach 108869 := rs (se 4 (by rfl) ⟨10206, by rfl⟩) (B 20413 (by norm_num) ⟨10206, by rfl⟩ (by norm_num))
theorem R207173 : Reach 207173 := rs (se 4 (by rfl) ⟨19422, by rfl⟩) (B 38845 (by norm_num) ⟨19422, by rfl⟩ (by norm_num))
theorem R108893 : Reach 108893 := rs (se 3 (by rfl) ⟨20417, by rfl⟩) (B 40835 (by norm_num) ⟨20417, by rfl⟩ (by norm_num))
theorem R108917 : Reach 108917 := rs (se 5 (by rfl) ⟨5105, by rfl⟩) (B 10211 (by norm_num) ⟨5105, by rfl⟩ (by norm_num))
theorem R108941 : Reach 108941 := rs (se 3 (by rfl) ⟨20426, by rfl⟩) (B 40853 (by norm_num) ⟨20426, by rfl⟩ (by norm_num))
theorem R108965 : Reach 108965 := rs (se 4 (by rfl) ⟨10215, by rfl⟩) (B 20431 (by norm_num) ⟨10215, by rfl⟩ (by norm_num))
theorem R108989 : Reach 108989 := rs (se 3 (by rfl) ⟨20435, by rfl⟩) (B 40871 (by norm_num) ⟨20435, by rfl⟩ (by norm_num))
theorem R174533 : Reach 174533 := rs (se 4 (by rfl) ⟨16362, by rfl⟩) (B 32725 (by norm_num) ⟨16362, by rfl⟩ (by norm_num))
theorem R371141 : Reach 371141 := rs (se 4 (by rfl) ⟨34794, by rfl⟩) (B 69589 (by norm_num) ⟨34794, by rfl⟩ (by norm_num))
theorem R109013 : Reach 109013 := rs (se 7 (by rfl) ⟨1277, by rfl⟩) (B 2555 (by norm_num) ⟨1277, by rfl⟩ (by norm_num))
theorem R109037 : Reach 109037 := rs (se 3 (by rfl) ⟨20444, by rfl⟩) (B 40889 (by norm_num) ⟨20444, by rfl⟩ (by norm_num))
theorem R141821 : Reach 141821 := rs (se 3 (by rfl) ⟨26591, by rfl⟩) (B 53183 (by norm_num) ⟨26591, by rfl⟩ (by norm_num))
theorem R109061 : Reach 109061 := rs (se 4 (by rfl) ⟨10224, by rfl⟩) (B 20449 (by norm_num) ⟨10224, by rfl⟩ (by norm_num))
theorem R109085 : Reach 109085 := rs (se 3 (by rfl) ⟨20453, by rfl⟩) (B 40907 (by norm_num) ⟨20453, by rfl⟩ (by norm_num))
theorem R109109 : Reach 109109 := rs (se 5 (by rfl) ⟨5114, by rfl⟩) (B 10229 (by norm_num) ⟨5114, by rfl⟩ (by norm_num))
theorem R76349 : Reach 76349 := rs (se 3 (by rfl) ⟨14315, by rfl⟩) (B 28631 (by norm_num) ⟨14315, by rfl⟩ (by norm_num))
theorem R109133 : Reach 109133 := rs (se 3 (by rfl) ⟨20462, by rfl⟩) (B 40925 (by norm_num) ⟨20462, by rfl⟩ (by norm_num))
theorem R109157 : Reach 109157 := rs (se 4 (by rfl) ⟨10233, by rfl⟩) (B 20467 (by norm_num) ⟨10233, by rfl⟩ (by norm_num))
theorem R240245 : Reach 240245 := rs (se 5 (by rfl) ⟨11261, by rfl⟩) (B 22523 (by norm_num) ⟨11261, by rfl⟩ (by norm_num))
theorem R109181 : Reach 109181 := rs (se 3 (by rfl) ⟨20471, by rfl⟩) (B 40943 (by norm_num) ⟨20471, by rfl⟩ (by norm_num))
theorem R109205 : Reach 109205 := rs (se 6 (by rfl) ⟨2559, by rfl⟩) (B 5119 (by norm_num) ⟨2559, by rfl⟩ (by norm_num))
theorem R404117 : Reach 404117 := rs (se 6 (by rfl) ⟨9471, by rfl⟩) (B 18943 (by norm_num) ⟨9471, by rfl⟩ (by norm_num))
theorem R109229 : Reach 109229 := rs (se 3 (by rfl) ⟨20480, by rfl⟩) (B 40961 (by norm_num) ⟨20480, by rfl⟩ (by norm_num))
theorem R109253 : Reach 109253 := rs (se 4 (by rfl) ⟨10242, by rfl⟩) (B 20485 (by norm_num) ⟨10242, by rfl⟩ (by norm_num))
theorem R109277 : Reach 109277 := rs (se 3 (by rfl) ⟨20489, by rfl⟩) (B 40979 (by norm_num) ⟨20489, by rfl⟩ (by norm_num))
theorem R109301 : Reach 109301 := rs (se 5 (by rfl) ⟨5123, by rfl⟩) (B 10247 (by norm_num) ⟨5123, by rfl⟩ (by norm_num))
theorem R109325 : Reach 109325 := rs (se 3 (by rfl) ⟨20498, by rfl⟩) (B 40997 (by norm_num) ⟨20498, by rfl⟩ (by norm_num))
theorem R109349 : Reach 109349 := rs (se 4 (by rfl) ⟨10251, by rfl⟩) (B 20503 (by norm_num) ⟨10251, by rfl⟩ (by norm_num))
theorem R109373 : Reach 109373 := rs (se 3 (by rfl) ⟨20507, by rfl⟩) (B 41015 (by norm_num) ⟨20507, by rfl⟩ (by norm_num))
theorem R109397 : Reach 109397 := rs (se 9 (by rfl) ⟨320, by rfl⟩) (B 641 (by norm_num) ⟨320, by rfl⟩ (by norm_num))
theorem R273253 : Reach 273253 := rs (se 4 (by rfl) ⟨25617, by rfl⟩) (B 51235 (by norm_num) ⟨25617, by rfl⟩ (by norm_num))
theorem R109421 : Reach 109421 := rs (se 3 (by rfl) ⟨20516, by rfl⟩) (B 41033 (by norm_num) ⟨20516, by rfl⟩ (by norm_num))
theorem R109445 : Reach 109445 := rs (se 4 (by rfl) ⟨10260, by rfl⟩) (B 20521 (by norm_num) ⟨10260, by rfl⟩ (by norm_num))
theorem R732053 : Reach 732053 := rs (se 6 (by rfl) ⟨17157, by rfl⟩) (B 34315 (by norm_num) ⟨17157, by rfl⟩ (by norm_num))
theorem R109469 : Reach 109469 := rs (se 3 (by rfl) ⟨20525, by rfl⟩) (B 41051 (by norm_num) ⟨20525, by rfl⟩ (by norm_num))
theorem R109493 : Reach 109493 := rs (se 5 (by rfl) ⟨5132, by rfl⟩) (B 10265 (by norm_num) ⟨5132, by rfl⟩ (by norm_num))
theorem R109517 : Reach 109517 := rs (se 3 (by rfl) ⟨20534, by rfl⟩) (B 41069 (by norm_num) ⟨20534, by rfl⟩ (by norm_num))
theorem R109541 : Reach 109541 := rs (se 4 (by rfl) ⟨10269, by rfl⟩) (B 20539 (by norm_num) ⟨10269, by rfl⟩ (by norm_num))
theorem R76793 : Reach 76793 := rs (se 2 (by rfl) ⟨28797, by rfl⟩) (B 57595 (by norm_num) ⟨28797, by rfl⟩ (by norm_num))
theorem R109565 : Reach 109565 := rs (se 3 (by rfl) ⟨20543, by rfl⟩) (B 41087 (by norm_num) ⟨20543, by rfl⟩ (by norm_num))
theorem R109589 : Reach 109589 := rs (se 6 (by rfl) ⟨2568, by rfl⟩) (B 5137 (by norm_num) ⟨2568, by rfl⟩ (by norm_num))
theorem R240677 : Reach 240677 := rs (se 4 (by rfl) ⟨22563, by rfl⟩) (B 45127 (by norm_num) ⟨22563, by rfl⟩ (by norm_num))
theorem R109613 : Reach 109613 := rs (se 3 (by rfl) ⟨20552, by rfl⟩) (B 41105 (by norm_num) ⟨20552, by rfl⟩ (by norm_num))
theorem R109637 : Reach 109637 := rs (se 4 (by rfl) ⟨10278, by rfl⟩) (B 20557 (by norm_num) ⟨10278, by rfl⟩ (by norm_num))
theorem R109661 : Reach 109661 := rs (se 3 (by rfl) ⟨20561, by rfl⟩) (B 41123 (by norm_num) ⟨20561, by rfl⟩ (by norm_num))
theorem R109685 : Reach 109685 := rs (se 5 (by rfl) ⟨5141, by rfl⟩) (B 10283 (by norm_num) ⟨5141, by rfl⟩ (by norm_num))
theorem R109709 : Reach 109709 := rs (se 3 (by rfl) ⟨20570, by rfl⟩) (B 41141 (by norm_num) ⟨20570, by rfl⟩ (by norm_num))
theorem R273557 : Reach 273557 := rs (se 6 (by rfl) ⟨6411, by rfl⟩) (B 12823 (by norm_num) ⟨6411, by rfl⟩ (by norm_num))
theorem R109733 : Reach 109733 := rs (se 4 (by rfl) ⟨10287, by rfl⟩) (B 20575 (by norm_num) ⟨10287, by rfl⟩ (by norm_num))
theorem R109757 : Reach 109757 := rs (se 3 (by rfl) ⟨20579, by rfl⟩) (B 41159 (by norm_num) ⟨20579, by rfl⟩ (by norm_num))
theorem R109781 : Reach 109781 := rs (se 7 (by rfl) ⟨1286, by rfl⟩) (B 2573 (by norm_num) ⟨1286, by rfl⟩ (by norm_num))
theorem R109805 : Reach 109805 := rs (se 3 (by rfl) ⟨20588, by rfl⟩) (B 41177 (by norm_num) ⟨20588, by rfl⟩ (by norm_num))
theorem R142573 : Reach 142573 := rs (se 3 (by rfl) ⟨26732, by rfl⟩) (B 53465 (by norm_num) ⟨26732, by rfl⟩ (by norm_num))
theorem R77041 : Reach 77041 := rs (se 2 (by rfl) ⟨28890, by rfl⟩) (B 57781 (by norm_num) ⟨28890, by rfl⟩ (by norm_num))
theorem R109829 : Reach 109829 := rs (se 4 (by rfl) ⟨10296, by rfl⟩) (B 20593 (by norm_num) ⟨10296, by rfl⟩ (by norm_num))
theorem R109853 : Reach 109853 := rs (se 3 (by rfl) ⟨20597, by rfl⟩) (B 41195 (by norm_num) ⟨20597, by rfl⟩ (by norm_num))
theorem R109877 : Reach 109877 := rs (se 5 (by rfl) ⟨5150, by rfl⟩) (B 10301 (by norm_num) ⟨5150, by rfl⟩ (by norm_num))
theorem R109901 : Reach 109901 := rs (se 3 (by rfl) ⟨20606, by rfl⟩) (B 41213 (by norm_num) ⟨20606, by rfl⟩ (by norm_num))
theorem R109925 : Reach 109925 := rs (se 4 (by rfl) ⟨10305, by rfl⟩) (B 20611 (by norm_num) ⟨10305, by rfl⟩ (by norm_num))
theorem R109949 : Reach 109949 := rs (se 3 (by rfl) ⟨20615, by rfl⟩) (B 41231 (by norm_num) ⟨20615, by rfl⟩ (by norm_num))
theorem R109973 : Reach 109973 := rs (se 6 (by rfl) ⟨2577, by rfl⟩) (B 5155 (by norm_num) ⟨2577, by rfl⟩ (by norm_num))
theorem R175517 : Reach 175517 := rs (se 3 (by rfl) ⟨32909, by rfl⟩) (B 65819 (by norm_num) ⟨32909, by rfl⟩ (by norm_num))
theorem R109997 : Reach 109997 := rs (se 3 (by rfl) ⟨20624, by rfl⟩) (B 41249 (by norm_num) ⟨20624, by rfl⟩ (by norm_num))
theorem R110021 : Reach 110021 := rs (se 4 (by rfl) ⟨10314, by rfl⟩) (B 20629 (by norm_num) ⟨10314, by rfl⟩ (by norm_num))
theorem R241109 : Reach 241109 := rs (se 7 (by rfl) ⟨2825, by rfl⟩) (B 5651 (by norm_num) ⟨2825, by rfl⟩ (by norm_num))
theorem R110045 : Reach 110045 := rs (se 3 (by rfl) ⟨20633, by rfl⟩) (B 41267 (by norm_num) ⟨20633, by rfl⟩ (by norm_num))
theorem R110069 : Reach 110069 := rs (se 5 (by rfl) ⟨5159, by rfl⟩) (B 10319 (by norm_num) ⟨5159, by rfl⟩ (by norm_num))
theorem R77321 : Reach 77321 := rs (se 2 (by rfl) ⟨28995, by rfl⟩) (B 57991 (by norm_num) ⟨28995, by rfl⟩ (by norm_num))
theorem R110093 : Reach 110093 := rs (se 3 (by rfl) ⟨20642, by rfl⟩) (B 41285 (by norm_num) ⟨20642, by rfl⟩ (by norm_num))
theorem R110117 : Reach 110117 := rs (se 4 (by rfl) ⟨10323, by rfl⟩) (B 20647 (by norm_num) ⟨10323, by rfl⟩ (by norm_num))
theorem R110141 : Reach 110141 := rs (se 3 (by rfl) ⟨20651, by rfl⟩) (B 41303 (by norm_num) ⟨20651, by rfl⟩ (by norm_num))
theorem R110165 : Reach 110165 := rs (se 8 (by rfl) ⟨645, by rfl⟩) (B 1291 (by norm_num) ⟨645, by rfl⟩ (by norm_num))
theorem R110189 : Reach 110189 := rs (se 3 (by rfl) ⟨20660, by rfl⟩) (B 41321 (by norm_num) ⟨20660, by rfl⟩ (by norm_num))
theorem R110213 : Reach 110213 := rs (se 4 (by rfl) ⟨10332, by rfl⟩) (B 20665 (by norm_num) ⟨10332, by rfl⟩ (by norm_num))
theorem R110237 : Reach 110237 := rs (se 3 (by rfl) ⟨20669, by rfl⟩) (B 41339 (by norm_num) ⟨20669, by rfl⟩ (by norm_num))
theorem R77485 : Reach 77485 := rs (se 3 (by rfl) ⟨14528, by rfl⟩) (B 29057 (by norm_num) ⟨14528, by rfl⟩ (by norm_num))
theorem R110261 : Reach 110261 := rs (se 5 (by rfl) ⟨5168, by rfl⟩) (B 10337 (by norm_num) ⟨5168, by rfl⟩ (by norm_num))
theorem R110285 : Reach 110285 := rs (se 3 (by rfl) ⟨20678, by rfl⟩) (B 41357 (by norm_num) ⟨20678, by rfl⟩ (by norm_num))
theorem R372437 : Reach 372437 := rs (se 7 (by rfl) ⟨4364, by rfl⟩) (B 8729 (by norm_num) ⟨4364, by rfl⟩ (by norm_num))
theorem R110309 : Reach 110309 := rs (se 4 (by rfl) ⟨10341, by rfl⟩) (B 20683 (by norm_num) ⟨10341, by rfl⟩ (by norm_num))
theorem R77545 : Reach 77545 := rs (se 2 (by rfl) ⟨29079, by rfl⟩) (B 58159 (by norm_num) ⟨29079, by rfl⟩ (by norm_num))
theorem R110333 : Reach 110333 := rs (se 3 (by rfl) ⟨20687, by rfl⟩) (B 41375 (by norm_num) ⟨20687, by rfl⟩ (by norm_num))
theorem R110341 : Reach 110341 := rs (se 4 (by rfl) ⟨10344, by rfl⟩) (B 20689 (by norm_num) ⟨10344, by rfl⟩ (by norm_num))
theorem R110357 : Reach 110357 := rs (se 6 (by rfl) ⟨2586, by rfl⟩) (B 5173 (by norm_num) ⟨2586, by rfl⟩ (by norm_num))
theorem R110381 : Reach 110381 := rs (se 3 (by rfl) ⟨20696, by rfl⟩) (B 41393 (by norm_num) ⟨20696, by rfl⟩ (by norm_num))
theorem R110405 : Reach 110405 := rs (se 4 (by rfl) ⟨10350, by rfl⟩) (B 20701 (by norm_num) ⟨10350, by rfl⟩ (by norm_num))
theorem R110429 : Reach 110429 := rs (se 3 (by rfl) ⟨20705, by rfl⟩) (B 41411 (by norm_num) ⟨20705, by rfl⟩ (by norm_num))
theorem R208757 : Reach 208757 := rs (se 5 (by rfl) ⟨9785, by rfl⟩) (B 19571 (by norm_num) ⟨9785, by rfl⟩ (by norm_num))
theorem R110453 : Reach 110453 := rs (se 5 (by rfl) ⟨5177, by rfl⟩) (B 10355 (by norm_num) ⟨5177, by rfl⟩ (by norm_num))
theorem R241541 : Reach 241541 := rs (se 4 (by rfl) ⟨22644, by rfl⟩) (B 45289 (by norm_num) ⟨22644, by rfl⟩ (by norm_num))
theorem R110477 : Reach 110477 := rs (se 3 (by rfl) ⟨20714, by rfl⟩) (B 41429 (by norm_num) ⟨20714, by rfl⟩ (by norm_num))
theorem R110501 : Reach 110501 := rs (se 4 (by rfl) ⟨10359, by rfl⟩) (B 20719 (by norm_num) ⟨10359, by rfl⟩ (by norm_num))
theorem R110525 : Reach 110525 := rs (se 3 (by rfl) ⟨20723, by rfl⟩) (B 41447 (by norm_num) ⟨20723, by rfl⟩ (by norm_num))
theorem R110549 : Reach 110549 := rs (se 7 (by rfl) ⟨1295, by rfl⟩) (B 2591 (by norm_num) ⟨1295, by rfl⟩ (by norm_num))
theorem R110573 : Reach 110573 := rs (se 3 (by rfl) ⟨20732, by rfl⟩) (B 41465 (by norm_num) ⟨20732, by rfl⟩ (by norm_num))
theorem R110597 : Reach 110597 := rs (se 4 (by rfl) ⟨10368, by rfl⟩) (B 20737 (by norm_num) ⟨10368, by rfl⟩ (by norm_num))
theorem R110621 : Reach 110621 := rs (se 3 (by rfl) ⟨20741, by rfl⟩) (B 41483 (by norm_num) ⟨20741, by rfl⟩ (by norm_num))
theorem R77861 : Reach 77861 := rs (se 4 (by rfl) ⟨7299, by rfl⟩) (B 14599 (by norm_num) ⟨7299, by rfl⟩ (by norm_num))
theorem R110645 : Reach 110645 := rs (se 5 (by rfl) ⟨5186, by rfl⟩) (B 10373 (by norm_num) ⟨5186, by rfl⟩ (by norm_num))
theorem R110669 : Reach 110669 := rs (se 3 (by rfl) ⟨20750, by rfl⟩) (B 41501 (by norm_num) ⟨20750, by rfl⟩ (by norm_num))
theorem R110693 : Reach 110693 := rs (se 4 (by rfl) ⟨10377, by rfl⟩) (B 20755 (by norm_num) ⟨10377, by rfl⟩ (by norm_num))
theorem R110717 : Reach 110717 := rs (se 3 (by rfl) ⟨20759, by rfl⟩) (B 41519 (by norm_num) ⟨20759, by rfl⟩ (by norm_num))
theorem R110741 : Reach 110741 := rs (se 6 (by rfl) ⟨2595, by rfl⟩) (B 5191 (by norm_num) ⟨2595, by rfl⟩ (by norm_num))
theorem R176293 : Reach 176293 := rs (se 4 (by rfl) ⟨16527, by rfl⟩) (B 33055 (by norm_num) ⟨16527, by rfl⟩ (by norm_num))
theorem R110765 : Reach 110765 := rs (se 3 (by rfl) ⟨20768, by rfl⟩) (B 41537 (by norm_num) ⟨20768, by rfl⟩ (by norm_num))
theorem R110789 : Reach 110789 := rs (se 4 (by rfl) ⟨10386, by rfl⟩) (B 20773 (by norm_num) ⟨10386, by rfl⟩ (by norm_num))
theorem R110813 : Reach 110813 := rs (se 3 (by rfl) ⟨20777, by rfl⟩) (B 41555 (by norm_num) ⟨20777, by rfl⟩ (by norm_num))
theorem R110837 : Reach 110837 := rs (se 5 (by rfl) ⟨5195, by rfl⟩) (B 10391 (by norm_num) ⟨5195, by rfl⟩ (by norm_num))
theorem R110861 : Reach 110861 := rs (se 3 (by rfl) ⟨20786, by rfl⟩) (B 41573 (by norm_num) ⟨20786, by rfl⟩ (by norm_num))
theorem R110885 : Reach 110885 := rs (se 4 (by rfl) ⟨10395, by rfl⟩) (B 20791 (by norm_num) ⟨10395, by rfl⟩ (by norm_num))
theorem R241973 : Reach 241973 := rs (se 5 (by rfl) ⟨11342, by rfl⟩) (B 22685 (by norm_num) ⟨11342, by rfl⟩ (by norm_num))
theorem R110909 : Reach 110909 := rs (se 3 (by rfl) ⟨20795, by rfl⟩) (B 41591 (by norm_num) ⟨20795, by rfl⟩ (by norm_num))
theorem R110933 : Reach 110933 := rs (se 10 (by rfl) ⟨162, by rfl⟩) (B 325 (by norm_num) ⟨162, by rfl⟩ (by norm_num))
theorem R110957 : Reach 110957 := rs (se 3 (by rfl) ⟨20804, by rfl⟩) (B 41609 (by norm_num) ⟨20804, by rfl⟩ (by norm_num))
theorem R110981 : Reach 110981 := rs (se 4 (by rfl) ⟨10404, by rfl⟩) (B 20809 (by norm_num) ⟨10404, by rfl⟩ (by norm_num))
theorem R176525 : Reach 176525 := rs (se 3 (by rfl) ⟨33098, by rfl⟩) (B 66197 (by norm_num) ⟨33098, by rfl⟩ (by norm_num))
theorem R111005 : Reach 111005 := rs (se 3 (by rfl) ⟨20813, by rfl⟩) (B 41627 (by norm_num) ⟨20813, by rfl⟩ (by norm_num))
theorem R111029 : Reach 111029 := rs (se 5 (by rfl) ⟨5204, by rfl⟩) (B 10409 (by norm_num) ⟨5204, by rfl⟩ (by norm_num))
theorem R111053 : Reach 111053 := rs (se 3 (by rfl) ⟨20822, by rfl⟩) (B 41645 (by norm_num) ⟨20822, by rfl⟩ (by norm_num))
theorem R78305 : Reach 78305 := rs (se 2 (by rfl) ⟨29364, by rfl⟩) (B 58729 (by norm_num) ⟨29364, by rfl⟩ (by norm_num))
theorem R111077 : Reach 111077 := rs (se 4 (by rfl) ⟨10413, by rfl⟩) (B 20827 (by norm_num) ⟨10413, by rfl⟩ (by norm_num))
theorem R111101 : Reach 111101 := rs (se 3 (by rfl) ⟨20831, by rfl⟩) (B 41663 (by norm_num) ⟨20831, by rfl⟩ (by norm_num))
theorem R209429 : Reach 209429 := rs (se 6 (by rfl) ⟨4908, by rfl⟩) (B 9817 (by norm_num) ⟨4908, by rfl⟩ (by norm_num))
theorem R111125 : Reach 111125 := rs (se 6 (by rfl) ⟨2604, by rfl⟩) (B 5209 (by norm_num) ⟨2604, by rfl⟩ (by norm_num))
theorem R78365 : Reach 78365 := rs (se 3 (by rfl) ⟨14693, by rfl⟩) (B 29387 (by norm_num) ⟨14693, by rfl⟩ (by norm_num))
theorem R111149 : Reach 111149 := rs (se 3 (by rfl) ⟨20840, by rfl⟩) (B 41681 (by norm_num) ⟨20840, by rfl⟩ (by norm_num))
theorem R111173 : Reach 111173 := rs (se 4 (by rfl) ⟨10422, by rfl⟩) (B 20845 (by norm_num) ⟨10422, by rfl⟩ (by norm_num))
theorem R111197 : Reach 111197 := rs (se 3 (by rfl) ⟨20849, by rfl⟩) (B 41699 (by norm_num) ⟨20849, by rfl⟩ (by norm_num))
theorem R111221 : Reach 111221 := rs (se 5 (by rfl) ⟨5213, by rfl⟩) (B 10427 (by norm_num) ⟨5213, by rfl⟩ (by norm_num))
theorem R78457 : Reach 78457 := rs (se 2 (by rfl) ⟨29421, by rfl⟩) (B 58843 (by norm_num) ⟨29421, by rfl⟩ (by norm_num))
theorem R111245 : Reach 111245 := rs (se 3 (by rfl) ⟨20858, by rfl⟩) (B 41717 (by norm_num) ⟨20858, by rfl⟩ (by norm_num))
theorem R78493 : Reach 78493 := rs (se 3 (by rfl) ⟨14717, by rfl⟩) (B 29435 (by norm_num) ⟨14717, by rfl⟩ (by norm_num))
theorem R111269 : Reach 111269 := rs (se 4 (by rfl) ⟨10431, by rfl⟩) (B 20863 (by norm_num) ⟨10431, by rfl⟩ (by norm_num))
theorem R111293 : Reach 111293 := rs (se 3 (by rfl) ⟨20867, by rfl⟩) (B 41735 (by norm_num) ⟨20867, by rfl⟩ (by norm_num))
theorem R111317 : Reach 111317 := rs (se 7 (by rfl) ⟨1304, by rfl⟩) (B 2609 (by norm_num) ⟨1304, by rfl⟩ (by norm_num))
theorem R242405 : Reach 242405 := rs (se 4 (by rfl) ⟨22725, by rfl⟩) (B 45451 (by norm_num) ⟨22725, by rfl⟩ (by norm_num))
theorem R111341 : Reach 111341 := rs (se 3 (by rfl) ⟨20876, by rfl⟩) (B 41753 (by norm_num) ⟨20876, by rfl⟩ (by norm_num))
theorem R307957 : Reach 307957 := rs (se 5 (by rfl) ⟨14435, by rfl⟩) (B 28871 (by norm_num) ⟨14435, by rfl⟩ (by norm_num))
theorem R111365 : Reach 111365 := rs (se 4 (by rfl) ⟨10440, by rfl⟩) (B 20881 (by norm_num) ⟨10440, by rfl⟩ (by norm_num))
theorem R176917 : Reach 176917 := rs (se 6 (by rfl) ⟨4146, by rfl⟩) (B 8293 (by norm_num) ⟨4146, by rfl⟩ (by norm_num))
theorem R111389 : Reach 111389 := rs (se 3 (by rfl) ⟨20885, by rfl⟩) (B 41771 (by norm_num) ⟨20885, by rfl⟩ (by norm_num))
theorem R111397 : Reach 111397 := rs (se 4 (by rfl) ⟨10443, by rfl⟩) (B 20887 (by norm_num) ⟨10443, by rfl⟩ (by norm_num))
theorem R111413 : Reach 111413 := rs (se 5 (by rfl) ⟨5222, by rfl⟩) (B 10445 (by norm_num) ⟨5222, by rfl⟩ (by norm_num))
theorem R111437 : Reach 111437 := rs (se 3 (by rfl) ⟨20894, by rfl⟩) (B 41789 (by norm_num) ⟨20894, by rfl⟩ (by norm_num))
theorem R8926037 : Reach 8926037 := rs (se 9 (by rfl) ⟨26150, by rfl⟩) (B 52301 (by norm_num) ⟨26150, by rfl⟩ (by norm_num))
theorem R111461 : Reach 111461 := rs (se 4 (by rfl) ⟨10449, by rfl⟩) (B 20899 (by norm_num) ⟨10449, by rfl⟩ (by norm_num))
theorem R111485 : Reach 111485 := rs (se 3 (by rfl) ⟨20903, by rfl⟩) (B 41807 (by norm_num) ⟨20903, by rfl⟩ (by norm_num))
theorem R111509 : Reach 111509 := rs (se 6 (by rfl) ⟨2613, by rfl⟩) (B 5227 (by norm_num) ⟨2613, by rfl⟩ (by norm_num))
theorem R111533 : Reach 111533 := rs (se 3 (by rfl) ⟨20912, by rfl⟩) (B 41825 (by norm_num) ⟨20912, by rfl⟩ (by norm_num))
theorem R209861 : Reach 209861 := rs (se 4 (by rfl) ⟨19674, by rfl⟩) (B 39349 (by norm_num) ⟨19674, by rfl⟩ (by norm_num))
theorem R111557 : Reach 111557 := rs (se 4 (by rfl) ⟨10458, by rfl⟩) (B 20917 (by norm_num) ⟨10458, by rfl⟩ (by norm_num))
theorem R111581 : Reach 111581 := rs (se 3 (by rfl) ⟨20921, by rfl⟩) (B 41843 (by norm_num) ⟨20921, by rfl⟩ (by norm_num))
theorem R373733 : Reach 373733 := rs (se 4 (by rfl) ⟨35037, by rfl⟩) (B 70075 (by norm_num) ⟨35037, by rfl⟩ (by norm_num))
theorem R111605 : Reach 111605 := rs (se 5 (by rfl) ⟨5231, by rfl⟩) (B 10463 (by norm_num) ⟨5231, by rfl⟩ (by norm_num))
theorem R111629 : Reach 111629 := rs (se 3 (by rfl) ⟨20930, by rfl⟩) (B 41861 (by norm_num) ⟨20930, by rfl⟩ (by norm_num))
theorem R111653 : Reach 111653 := rs (se 4 (by rfl) ⟨10467, by rfl⟩) (B 20935 (by norm_num) ⟨10467, by rfl⟩ (by norm_num))
theorem R111677 : Reach 111677 := rs (se 3 (by rfl) ⟨20939, by rfl⟩) (B 41879 (by norm_num) ⟨20939, by rfl⟩ (by norm_num))
theorem R111701 : Reach 111701 := rs (se 8 (by rfl) ⟨654, by rfl⟩) (B 1309 (by norm_num) ⟨654, by rfl⟩ (by norm_num))
theorem R78937 : Reach 78937 := rs (se 2 (by rfl) ⟨29601, by rfl⟩) (B 59203 (by norm_num) ⟨29601, by rfl⟩ (by norm_num))
theorem R111725 : Reach 111725 := rs (se 3 (by rfl) ⟨20948, by rfl⟩) (B 41897 (by norm_num) ⟨20948, by rfl⟩ (by norm_num))
theorem R111749 : Reach 111749 := rs (se 4 (by rfl) ⟨10476, by rfl⟩) (B 20953 (by norm_num) ⟨10476, by rfl⟩ (by norm_num))
theorem R242837 : Reach 242837 := rs (se 6 (by rfl) ⟨5691, by rfl⟩) (B 11383 (by norm_num) ⟨5691, by rfl⟩ (by norm_num))
theorem R373909 : Reach 373909 := rs (se 6 (by rfl) ⟨8763, by rfl⟩) (B 17527 (by norm_num) ⟨8763, by rfl⟩ (by norm_num))
theorem R111773 : Reach 111773 := rs (se 3 (by rfl) ⟨20957, by rfl⟩) (B 41915 (by norm_num) ⟨20957, by rfl⟩ (by norm_num))
theorem R111797 : Reach 111797 := rs (se 5 (by rfl) ⟨5240, by rfl⟩) (B 10481 (by norm_num) ⟨5240, by rfl⟩ (by norm_num))
theorem R111821 : Reach 111821 := rs (se 3 (by rfl) ⟨20966, by rfl⟩) (B 41933 (by norm_num) ⟨20966, by rfl⟩ (by norm_num))
theorem R79057 : Reach 79057 := rs (se 2 (by rfl) ⟨29646, by rfl⟩) (B 59293 (by norm_num) ⟨29646, by rfl⟩ (by norm_num))
theorem R275669 : Reach 275669 := rs (se 7 (by rfl) ⟨3230, by rfl⟩) (B 6461 (by norm_num) ⟨3230, by rfl⟩ (by norm_num))
theorem R111845 : Reach 111845 := rs (se 4 (by rfl) ⟨10485, by rfl⟩) (B 20971 (by norm_num) ⟨10485, by rfl⟩ (by norm_num))
theorem R111869 : Reach 111869 := rs (se 3 (by rfl) ⟨20975, by rfl⟩) (B 41951 (by norm_num) ⟨20975, by rfl⟩ (by norm_num))
theorem R111893 : Reach 111893 := rs (se 6 (by rfl) ⟨2622, by rfl⟩) (B 5245 (by norm_num) ⟨2622, by rfl⟩ (by norm_num))
theorem R111917 : Reach 111917 := rs (se 3 (by rfl) ⟨20984, by rfl⟩) (B 41969 (by norm_num) ⟨20984, by rfl⟩ (by norm_num))
theorem R111941 : Reach 111941 := rs (se 4 (by rfl) ⟨10494, by rfl⟩) (B 20989 (by norm_num) ⟨10494, by rfl⟩ (by norm_num))
theorem R111965 : Reach 111965 := rs (se 3 (by rfl) ⟨20993, by rfl⟩) (B 41987 (by norm_num) ⟨20993, by rfl⟩ (by norm_num))
theorem R111989 : Reach 111989 := rs (se 5 (by rfl) ⟨5249, by rfl⟩) (B 10499 (by norm_num) ⟨5249, by rfl⟩ (by norm_num))
theorem R112013 : Reach 112013 := rs (se 3 (by rfl) ⟨21002, by rfl⟩) (B 42005 (by norm_num) ⟨21002, by rfl⟩ (by norm_num))
theorem R144797 : Reach 144797 := rs (se 3 (by rfl) ⟨27149, by rfl⟩) (B 54299 (by norm_num) ⟨27149, by rfl⟩ (by norm_num))
theorem R112037 : Reach 112037 := rs (se 4 (by rfl) ⟨10503, by rfl⟩) (B 21007 (by norm_num) ⟨10503, by rfl⟩ (by norm_num))
theorem R112061 : Reach 112061 := rs (se 3 (by rfl) ⟨21011, by rfl⟩) (B 42023 (by norm_num) ⟨21011, by rfl⟩ (by norm_num))
theorem R79309 : Reach 79309 := rs (se 3 (by rfl) ⟨14870, by rfl⟩) (B 29741 (by norm_num) ⟨14870, by rfl⟩ (by norm_num))
theorem R79313 : Reach 79313 := rs (se 2 (by rfl) ⟨29742, by rfl⟩) (B 59485 (by norm_num) ⟨29742, by rfl⟩ (by norm_num))
theorem R112085 : Reach 112085 := rs (se 7 (by rfl) ⟨1313, by rfl⟩) (B 2627 (by norm_num) ⟨1313, by rfl⟩ (by norm_num))
theorem R112109 : Reach 112109 := rs (se 3 (by rfl) ⟨21020, by rfl⟩) (B 42041 (by norm_num) ⟨21020, by rfl⟩ (by norm_num))
theorem R275957 : Reach 275957 := rs (se 5 (by rfl) ⟨12935, by rfl⟩) (B 25871 (by norm_num) ⟨12935, by rfl⟩ (by norm_num))
theorem R112133 : Reach 112133 := rs (se 4 (by rfl) ⟨10512, by rfl⟩) (B 21025 (by norm_num) ⟨10512, by rfl⟩ (by norm_num))
theorem R112157 : Reach 112157 := rs (se 3 (by rfl) ⟨21029, by rfl⟩) (B 42059 (by norm_num) ⟨21029, by rfl⟩ (by norm_num))
theorem R112181 : Reach 112181 := rs (se 5 (by rfl) ⟨5258, by rfl⟩) (B 10517 (by norm_num) ⟨5258, by rfl⟩ (by norm_num))
theorem R243269 : Reach 243269 := rs (se 4 (by rfl) ⟨22806, by rfl⟩) (B 45613 (by norm_num) ⟨22806, by rfl⟩ (by norm_num))
theorem R112205 : Reach 112205 := rs (se 3 (by rfl) ⟨21038, by rfl⟩) (B 42077 (by norm_num) ⟨21038, by rfl⟩ (by norm_num))
theorem R112229 : Reach 112229 := rs (se 4 (by rfl) ⟨10521, by rfl⟩) (B 21043 (by norm_num) ⟨10521, by rfl⟩ (by norm_num))
theorem R112253 : Reach 112253 := rs (se 3 (by rfl) ⟨21047, by rfl⟩) (B 42095 (by norm_num) ⟨21047, by rfl⟩ (by norm_num))
theorem R112261 : Reach 112261 := rs (se 4 (by rfl) ⟨10524, by rfl⟩) (B 21049 (by norm_num) ⟨10524, by rfl⟩ (by norm_num))
theorem R112277 : Reach 112277 := rs (se 6 (by rfl) ⟨2631, by rfl⟩) (B 5263 (by norm_num) ⟨2631, by rfl⟩ (by norm_num))
theorem R112301 : Reach 112301 := rs (se 3 (by rfl) ⟨21056, by rfl⟩) (B 42113 (by norm_num) ⟨21056, by rfl⟩ (by norm_num))
theorem R210613 : Reach 210613 := rs (se 5 (by rfl) ⟨9872, by rfl⟩) (B 19745 (by norm_num) ⟨9872, by rfl⟩ (by norm_num))
theorem R112325 : Reach 112325 := rs (se 4 (by rfl) ⟨10530, by rfl⟩) (B 21061 (by norm_num) ⟨10530, by rfl⟩ (by norm_num))
theorem R308933 : Reach 308933 := rs (se 4 (by rfl) ⟨28962, by rfl⟩) (B 57925 (by norm_num) ⟨28962, by rfl⟩ (by norm_num))
theorem R669397 : Reach 669397 := rs (se 7 (by rfl) ⟨7844, by rfl⟩) (B 15689 (by norm_num) ⟨7844, by rfl⟩ (by norm_num))
theorem R112349 : Reach 112349 := rs (se 3 (by rfl) ⟨21065, by rfl⟩) (B 42131 (by norm_num) ⟨21065, by rfl⟩ (by norm_num))
theorem R112373 : Reach 112373 := rs (se 5 (by rfl) ⟨5267, by rfl⟩) (B 10535 (by norm_num) ⟨5267, by rfl⟩ (by norm_num))
theorem R112397 : Reach 112397 := rs (se 3 (by rfl) ⟨21074, by rfl⟩) (B 42149 (by norm_num) ⟨21074, by rfl⟩ (by norm_num))
theorem R112421 : Reach 112421 := rs (se 4 (by rfl) ⟨10539, by rfl⟩) (B 21079 (by norm_num) ⟨10539, by rfl⟩ (by norm_num))
theorem R112445 : Reach 112445 := rs (se 3 (by rfl) ⟨21083, by rfl⟩) (B 42167 (by norm_num) ⟨21083, by rfl⟩ (by norm_num))
theorem R112469 : Reach 112469 := rs (se 9 (by rfl) ⟨329, by rfl⟩) (B 659 (by norm_num) ⟨329, by rfl⟩ (by norm_num))
theorem R178013 : Reach 178013 := rs (se 3 (by rfl) ⟨33377, by rfl⟩) (B 66755 (by norm_num) ⟨33377, by rfl⟩ (by norm_num))
theorem R145253 : Reach 145253 := rs (se 4 (by rfl) ⟨13617, by rfl⟩) (B 27235 (by norm_num) ⟨13617, by rfl⟩ (by norm_num))
theorem R112493 : Reach 112493 := rs (se 3 (by rfl) ⟨21092, by rfl⟩) (B 42185 (by norm_num) ⟨21092, by rfl⟩ (by norm_num))
theorem R112517 : Reach 112517 := rs (se 4 (by rfl) ⟨10548, by rfl⟩) (B 21097 (by norm_num) ⟨10548, by rfl⟩ (by norm_num))
theorem R145309 : Reach 145309 := rs (se 3 (by rfl) ⟨27245, by rfl⟩) (B 54491 (by norm_num) ⟨27245, by rfl⟩ (by norm_num))
theorem R112541 : Reach 112541 := rs (se 3 (by rfl) ⟨21101, by rfl⟩) (B 42203 (by norm_num) ⟨21101, by rfl⟩ (by norm_num))
theorem R112565 : Reach 112565 := rs (se 5 (by rfl) ⟨5276, by rfl⟩) (B 10553 (by norm_num) ⟨5276, by rfl⟩ (by norm_num))
theorem R112589 : Reach 112589 := rs (se 3 (by rfl) ⟨21110, by rfl⟩) (B 42221 (by norm_num) ⟨21110, by rfl⟩ (by norm_num))
theorem R112613 : Reach 112613 := rs (se 4 (by rfl) ⟨10557, by rfl⟩) (B 21115 (by norm_num) ⟨10557, by rfl⟩ (by norm_num))
theorem R243701 : Reach 243701 := rs (se 5 (by rfl) ⟨11423, by rfl⟩) (B 22847 (by norm_num) ⟨11423, by rfl⟩ (by norm_num))
theorem R112637 : Reach 112637 := rs (se 3 (by rfl) ⟨21119, by rfl⟩) (B 42239 (by norm_num) ⟨21119, by rfl⟩ (by norm_num))
theorem R79877 : Reach 79877 := rs (se 4 (by rfl) ⟨7488, by rfl⟩) (B 14977 (by norm_num) ⟨7488, by rfl⟩ (by norm_num))
theorem R112661 : Reach 112661 := rs (se 6 (by rfl) ⟨2640, by rfl⟩) (B 5281 (by norm_num) ⟨2640, by rfl⟩ (by norm_num))
theorem R112685 : Reach 112685 := rs (se 3 (by rfl) ⟨21128, by rfl⟩) (B 42257 (by norm_num) ⟨21128, by rfl⟩ (by norm_num))
theorem R178301 : Reach 178301 := rs (se 3 (by rfl) ⟨33431, by rfl⟩) (B 66863 (by norm_num) ⟨33431, by rfl⟩ (by norm_num))
theorem R80041 : Reach 80041 := rs (se 2 (by rfl) ⟨30015, by rfl⟩) (B 60031 (by norm_num) ⟨30015, by rfl⟩ (by norm_num))
theorem R80065 : Reach 80065 := rs (se 2 (by rfl) ⟨30024, by rfl⟩) (B 60049 (by norm_num) ⟨30024, by rfl⟩ (by norm_num))
theorem R80077 : Reach 80077 := rs (se 3 (by rfl) ⟨15014, by rfl⟩) (B 30029 (by norm_num) ⟨15014, by rfl⟩ (by norm_num))
theorem R211157 : Reach 211157 := rs (se 7 (by rfl) ⟨2474, by rfl⟩) (B 4949 (by norm_num) ⟨2474, by rfl⟩ (by norm_num))
theorem R80113 : Reach 80113 := rs (se 2 (by rfl) ⟨30042, by rfl⟩) (B 60085 (by norm_num) ⟨30042, by rfl⟩ (by norm_num))
theorem R375029 : Reach 375029 := rs (se 5 (by rfl) ⟨17579, by rfl⟩) (B 35159 (by norm_num) ⟨17579, by rfl⟩ (by norm_num))
theorem R80149 : Reach 80149 := rs (se 6 (by rfl) ⟨1878, by rfl⟩) (B 3757 (by norm_num) ⟨1878, by rfl⟩ (by norm_num))
theorem R80185 : Reach 80185 := rs (se 2 (by rfl) ⟨30069, by rfl⟩) (B 60139 (by norm_num) ⟨30069, by rfl⟩ (by norm_num))
theorem R80221 : Reach 80221 := rs (se 3 (by rfl) ⟨15041, by rfl⟩) (B 30083 (by norm_num) ⟨15041, by rfl⟩ (by norm_num))
theorem R80257 : Reach 80257 := rs (se 2 (by rfl) ⟨30096, by rfl⟩) (B 60193 (by norm_num) ⟨30096, by rfl⟩ (by norm_num))
theorem R80293 : Reach 80293 := rs (se 4 (by rfl) ⟨7527, by rfl⟩) (B 15055 (by norm_num) ⟨7527, by rfl⟩ (by norm_num))
theorem R145829 : Reach 145829 := rs (se 4 (by rfl) ⟨13671, by rfl⟩) (B 27343 (by norm_num) ⟨13671, by rfl⟩ (by norm_num))
theorem R244133 : Reach 244133 := rs (se 4 (by rfl) ⟨22887, by rfl⟩) (B 45775 (by norm_num) ⟨22887, by rfl⟩ (by norm_num))
theorem R80329 : Reach 80329 := rs (se 2 (by rfl) ⟨30123, by rfl⟩) (B 60247 (by norm_num) ⟨30123, by rfl⟩ (by norm_num))
theorem R80365 : Reach 80365 := rs (se 3 (by rfl) ⟨15068, by rfl⟩) (B 30137 (by norm_num) ⟨15068, by rfl⟩ (by norm_num))
theorem R80401 : Reach 80401 := rs (se 2 (by rfl) ⟨30150, by rfl⟩) (B 60301 (by norm_num) ⟨30150, by rfl⟩ (by norm_num))
theorem R80437 : Reach 80437 := rs (se 5 (by rfl) ⟨3770, by rfl⟩) (B 7541 (by norm_num) ⟨3770, by rfl⟩ (by norm_num))
theorem R408149 : Reach 408149 := rs (se 8 (by rfl) ⟨2391, by rfl⟩) (B 4783 (by norm_num) ⟨2391, by rfl⟩ (by norm_num))
theorem R80473 : Reach 80473 := rs (se 2 (by rfl) ⟨30177, by rfl⟩) (B 60355 (by norm_num) ⟨30177, by rfl⟩ (by norm_num))
theorem R113269 : Reach 113269 := rs (se 5 (by rfl) ⟨5309, by rfl⟩) (B 10619 (by norm_num) ⟨5309, by rfl⟩ (by norm_num))
theorem R80509 : Reach 80509 := rs (se 3 (by rfl) ⟨15095, by rfl⟩) (B 30191 (by norm_num) ⟨15095, by rfl⟩ (by norm_num))
theorem R277141 : Reach 277141 := rs (se 6 (by rfl) ⟨6495, by rfl⟩) (B 12991 (by norm_num) ⟨6495, by rfl⟩ (by norm_num))
theorem R80545 : Reach 80545 := rs (se 2 (by rfl) ⟨30204, by rfl⟩) (B 60409 (by norm_num) ⟨30204, by rfl⟩ (by norm_num))
theorem R80581 : Reach 80581 := rs (se 4 (by rfl) ⟨7554, by rfl⟩) (B 15109 (by norm_num) ⟨7554, by rfl⟩ (by norm_num))
theorem R80617 : Reach 80617 := rs (se 2 (by rfl) ⟨30231, by rfl⟩) (B 60463 (by norm_num) ⟨30231, by rfl⟩ (by norm_num))
theorem R80653 : Reach 80653 := rs (se 3 (by rfl) ⟨15122, by rfl⟩) (B 30245 (by norm_num) ⟨15122, by rfl⟩ (by norm_num))
theorem R80669 : Reach 80669 := rs (se 3 (by rfl) ⟨15125, by rfl⟩) (B 30251 (by norm_num) ⟨15125, by rfl⟩ (by norm_num))
theorem R80689 : Reach 80689 := rs (se 2 (by rfl) ⟨30258, by rfl⟩) (B 60517 (by norm_num) ⟨30258, by rfl⟩ (by norm_num))
theorem R310085 : Reach 310085 := rs (se 4 (by rfl) ⟨29070, by rfl⟩) (B 58141 (by norm_num) ⟨29070, by rfl⟩ (by norm_num))
theorem R80717 : Reach 80717 := rs (se 3 (by rfl) ⟨15134, by rfl⟩) (B 30269 (by norm_num) ⟨15134, by rfl⟩ (by norm_num))
theorem R80725 : Reach 80725 := rs (se 9 (by rfl) ⟨236, by rfl⟩) (B 473 (by norm_num) ⟨236, by rfl⟩ (by norm_num))
theorem R244565 : Reach 244565 := rs (se 9 (by rfl) ⟨716, by rfl⟩) (B 1433 (by norm_num) ⟨716, by rfl⟩ (by norm_num))
theorem R80761 : Reach 80761 := rs (se 2 (by rfl) ⟨30285, by rfl⟩) (B 60571 (by norm_num) ⟨30285, by rfl⟩ (by norm_num))
theorem R80797 : Reach 80797 := rs (se 3 (by rfl) ⟨15149, by rfl⟩) (B 30299 (by norm_num) ⟨15149, by rfl⟩ (by norm_num))
theorem R80833 : Reach 80833 := rs (se 2 (by rfl) ⟨30312, by rfl⟩) (B 60625 (by norm_num) ⟨30312, by rfl⟩ (by norm_num))
theorem R277445 : Reach 277445 := rs (se 4 (by rfl) ⟨26010, by rfl⟩) (B 52021 (by norm_num) ⟨26010, by rfl⟩ (by norm_num))
theorem R80869 : Reach 80869 := rs (se 4 (by rfl) ⟨7581, by rfl⟩) (B 15163 (by norm_num) ⟨7581, by rfl⟩ (by norm_num))
theorem R80905 : Reach 80905 := rs (se 2 (by rfl) ⟨30339, by rfl⟩) (B 60679 (by norm_num) ⟨30339, by rfl⟩ (by norm_num))
theorem R80941 : Reach 80941 := rs (se 3 (by rfl) ⟨15176, by rfl⟩) (B 30353 (by norm_num) ⟨15176, by rfl⟩ (by norm_num))
theorem R343109 : Reach 343109 := rs (se 4 (by rfl) ⟨32166, by rfl⟩) (B 64333 (by norm_num) ⟨32166, by rfl⟩ (by norm_num))
theorem R80977 : Reach 80977 := rs (se 2 (by rfl) ⟨30366, by rfl⟩) (B 60733 (by norm_num) ⟨30366, by rfl⟩ (by norm_num))
theorem R81013 : Reach 81013 := rs (se 5 (by rfl) ⟨3797, by rfl⟩) (B 7595 (by norm_num) ⟨3797, by rfl⟩ (by norm_num))
theorem R81049 : Reach 81049 := rs (se 2 (by rfl) ⟨30393, by rfl⟩) (B 60787 (by norm_num) ⟨30393, by rfl⟩ (by norm_num))
theorem R81085 : Reach 81085 := rs (se 3 (by rfl) ⟨15203, by rfl⟩) (B 30407 (by norm_num) ⟨15203, by rfl⟩ (by norm_num))
theorem R81121 : Reach 81121 := rs (se 2 (by rfl) ⟨30420, by rfl⟩) (B 60841 (by norm_num) ⟨30420, by rfl⟩ (by norm_num))
theorem R81157 : Reach 81157 := rs (se 4 (by rfl) ⟨7608, by rfl⟩) (B 15217 (by norm_num) ⟨7608, by rfl⟩ (by norm_num))
theorem R244997 : Reach 244997 := rs (se 4 (by rfl) ⟨22968, by rfl⟩) (B 45937 (by norm_num) ⟨22968, by rfl⟩ (by norm_num))
theorem R81193 : Reach 81193 := rs (se 2 (by rfl) ⟨30447, by rfl⟩) (B 60895 (by norm_num) ⟨30447, by rfl⟩ (by norm_num))
theorem R81229 : Reach 81229 := rs (se 3 (by rfl) ⟨15230, by rfl⟩) (B 30461 (by norm_num) ⟨15230, by rfl⟩ (by norm_num))
theorem R81265 : Reach 81265 := rs (se 2 (by rfl) ⟨30474, by rfl⟩) (B 60949 (by norm_num) ⟨30474, by rfl⟩ (by norm_num))
theorem R81301 : Reach 81301 := rs (se 6 (by rfl) ⟨1905, by rfl⟩) (B 3811 (by norm_num) ⟨1905, by rfl⟩ (by norm_num))
theorem R81337 : Reach 81337 := rs (se 2 (by rfl) ⟨30501, by rfl⟩) (B 61003 (by norm_num) ⟨30501, by rfl⟩ (by norm_num))
theorem R81373 : Reach 81373 := rs (se 3 (by rfl) ⟨15257, by rfl⟩) (B 30515 (by norm_num) ⟨15257, by rfl⟩ (by norm_num))
theorem R81409 : Reach 81409 := rs (se 2 (by rfl) ⟨30528, by rfl⟩) (B 61057 (by norm_num) ⟨30528, by rfl⟩ (by norm_num))
theorem R376325 : Reach 376325 := rs (se 4 (by rfl) ⟨35280, by rfl⟩) (B 70561 (by norm_num) ⟨35280, by rfl⟩ (by norm_num))
theorem R81445 : Reach 81445 := rs (se 4 (by rfl) ⟨7635, by rfl⟩) (B 15271 (by norm_num) ⟨7635, by rfl⟩ (by norm_num))
theorem R81481 : Reach 81481 := rs (se 2 (by rfl) ⟨30555, by rfl⟩) (B 61111 (by norm_num) ⟨30555, by rfl⟩ (by norm_num))
theorem R81517 : Reach 81517 := rs (se 3 (by rfl) ⟨15284, by rfl⟩) (B 30569 (by norm_num) ⟨15284, by rfl⟩ (by norm_num))
theorem R81553 : Reach 81553 := rs (se 2 (by rfl) ⟨30582, by rfl⟩) (B 61165 (by norm_num) ⟨30582, by rfl⟩ (by norm_num))
theorem R310949 : Reach 310949 := rs (se 4 (by rfl) ⟨29151, by rfl⟩) (B 58303 (by norm_num) ⟨29151, by rfl⟩ (by norm_num))
theorem R81577 : Reach 81577 := rs (se 2 (by rfl) ⟨30591, by rfl⟩) (B 61183 (by norm_num) ⟨30591, by rfl⟩ (by norm_num))
theorem R81589 : Reach 81589 := rs (se 5 (by rfl) ⟨3824, by rfl⟩) (B 7649 (by norm_num) ⟨3824, by rfl⟩ (by norm_num))
theorem R245429 : Reach 245429 := rs (se 5 (by rfl) ⟨11504, by rfl⟩) (B 23009 (by norm_num) ⟨11504, by rfl⟩ (by norm_num))
theorem R147133 : Reach 147133 := rs (se 3 (by rfl) ⟨27587, by rfl⟩) (B 55175 (by norm_num) ⟨27587, by rfl⟩ (by norm_num))
theorem R81625 : Reach 81625 := rs (se 2 (by rfl) ⟨30609, by rfl⟩) (B 61219 (by norm_num) ⟨30609, by rfl⟩ (by norm_num))
theorem R409333 : Reach 409333 := rs (se 5 (by rfl) ⟨19187, by rfl⟩) (B 38375 (by norm_num) ⟨19187, by rfl⟩ (by norm_num))
theorem R81661 : Reach 81661 := rs (se 3 (by rfl) ⟨15311, by rfl⟩) (B 30623 (by norm_num) ⟨15311, by rfl⟩ (by norm_num))
theorem R81697 : Reach 81697 := rs (se 2 (by rfl) ⟨30636, by rfl⟩) (B 61273 (by norm_num) ⟨30636, by rfl⟩ (by norm_num))
theorem R81733 : Reach 81733 := rs (se 4 (by rfl) ⟨7662, by rfl⟩) (B 15325 (by norm_num) ⟨7662, by rfl⟩ (by norm_num))
theorem R180053 : Reach 180053 := rs (se 9 (by rfl) ⟨527, by rfl⟩) (B 1055 (by norm_num) ⟨527, by rfl⟩ (by norm_num))
theorem R81769 : Reach 81769 := rs (se 2 (by rfl) ⟨30663, by rfl⟩) (B 61327 (by norm_num) ⟨30663, by rfl⟩ (by norm_num))
theorem R81805 : Reach 81805 := rs (se 3 (by rfl) ⟨15338, by rfl⟩) (B 30677 (by norm_num) ⟨15338, by rfl⟩ (by norm_num))
theorem R376741 : Reach 376741 := rs (se 4 (by rfl) ⟨35319, by rfl⟩) (B 70639 (by norm_num) ⟨35319, by rfl⟩ (by norm_num))
theorem R81841 : Reach 81841 := rs (se 2 (by rfl) ⟨30690, by rfl⟩) (B 61381 (by norm_num) ⟨30690, by rfl⟩ (by norm_num))
theorem R81877 : Reach 81877 := rs (se 7 (by rfl) ⟨959, by rfl⟩) (B 1919 (by norm_num) ⟨959, by rfl⟩ (by norm_num))
theorem R81913 : Reach 81913 := rs (se 2 (by rfl) ⟨30717, by rfl⟩) (B 61435 (by norm_num) ⟨30717, by rfl⟩ (by norm_num))
theorem R180245 : Reach 180245 := rs (se 6 (by rfl) ⟨4224, by rfl⟩) (B 8449 (by norm_num) ⟨4224, by rfl⟩ (by norm_num))
theorem R81949 : Reach 81949 := rs (se 3 (by rfl) ⟨15365, by rfl⟩) (B 30731 (by norm_num) ⟨15365, by rfl⟩ (by norm_num))
theorem R81985 : Reach 81985 := rs (se 2 (by rfl) ⟨30744, by rfl⟩) (B 61489 (by norm_num) ⟨30744, by rfl⟩ (by norm_num))
theorem R245861 : Reach 245861 := rs (se 4 (by rfl) ⟨23049, by rfl⟩) (B 46099 (by norm_num) ⟨23049, by rfl⟩ (by norm_num))
theorem R82021 : Reach 82021 := rs (se 4 (by rfl) ⟨7689, by rfl⟩) (B 15379 (by norm_num) ⟨7689, by rfl⟩ (by norm_num))
theorem R147565 : Reach 147565 := rs (se 3 (by rfl) ⟨27668, by rfl⟩) (B 55337 (by norm_num) ⟨27668, by rfl⟩ (by norm_num))
theorem R82057 : Reach 82057 := rs (se 2 (by rfl) ⟨30771, by rfl⟩) (B 61543 (by norm_num) ⟨30771, by rfl⟩ (by norm_num))
theorem R82093 : Reach 82093 := rs (se 3 (by rfl) ⟨15392, by rfl⟩) (B 30785 (by norm_num) ⟨15392, by rfl⟩ (by norm_num))
theorem R180397 : Reach 180397 := rs (se 3 (by rfl) ⟨33824, by rfl⟩) (B 67649 (by norm_num) ⟨33824, by rfl⟩ (by norm_num))
theorem R114869 : Reach 114869 := rs (se 5 (by rfl) ⟨5384, by rfl⟩) (B 10769 (by norm_num) ⟨5384, by rfl⟩ (by norm_num))
theorem R82129 : Reach 82129 := rs (se 2 (by rfl) ⟨30798, by rfl⟩) (B 61597 (by norm_num) ⟨30798, by rfl⟩ (by norm_num))
theorem R540917 : Reach 540917 := rs (se 5 (by rfl) ⟨25355, by rfl⟩) (B 50711 (by norm_num) ⟨25355, by rfl⟩ (by norm_num))
theorem R82165 : Reach 82165 := rs (se 5 (by rfl) ⟨3851, by rfl⟩) (B 7703 (by norm_num) ⟨3851, by rfl⟩ (by norm_num))
theorem R82201 : Reach 82201 := rs (se 2 (by rfl) ⟨30825, by rfl⟩) (B 61651 (by norm_num) ⟨30825, by rfl⟩ (by norm_num))
theorem R82237 : Reach 82237 := rs (se 3 (by rfl) ⟨15419, by rfl⟩) (B 30839 (by norm_num) ⟨15419, by rfl⟩ (by norm_num))
theorem R82273 : Reach 82273 := rs (se 2 (by rfl) ⟨30852, by rfl⟩) (B 61705 (by norm_num) ⟨30852, by rfl⟩ (by norm_num))
theorem R180589 : Reach 180589 := rs (se 3 (by rfl) ⟨33860, by rfl⟩) (B 67721 (by norm_num) ⟨33860, by rfl⟩ (by norm_num))
theorem R82309 : Reach 82309 := rs (se 4 (by rfl) ⟨7716, by rfl⟩) (B 15433 (by norm_num) ⟨7716, by rfl⟩ (by norm_num))
theorem R82345 : Reach 82345 := rs (se 2 (by rfl) ⟨30879, by rfl⟩) (B 61759 (by norm_num) ⟨30879, by rfl⟩ (by norm_num))
theorem R82381 : Reach 82381 := rs (se 3 (by rfl) ⟨15446, by rfl⟩) (B 30893 (by norm_num) ⟨15446, by rfl⟩ (by norm_num))
theorem R213461 : Reach 213461 := rs (se 7 (by rfl) ⟨2501, by rfl⟩) (B 5003 (by norm_num) ⟨2501, by rfl⟩ (by norm_num))
theorem R180701 : Reach 180701 := rs (se 3 (by rfl) ⟨33881, by rfl⟩) (B 67763 (by norm_num) ⟨33881, by rfl⟩ (by norm_num))
theorem R82417 : Reach 82417 := rs (se 2 (by rfl) ⟨30906, by rfl⟩) (B 61813 (by norm_num) ⟨30906, by rfl⟩ (by norm_num))
theorem R82453 : Reach 82453 := rs (se 6 (by rfl) ⟨1932, by rfl⟩) (B 3865 (by norm_num) ⟨1932, by rfl⟩ (by norm_num))
theorem R246293 : Reach 246293 := rs (se 6 (by rfl) ⟨5772, by rfl⟩) (B 11545 (by norm_num) ⟨5772, by rfl⟩ (by norm_num))
theorem R82489 : Reach 82489 := rs (se 2 (by rfl) ⟨30933, by rfl⟩) (B 61867 (by norm_num) ⟨30933, by rfl⟩ (by norm_num))
theorem R82525 : Reach 82525 := rs (se 3 (by rfl) ⟨15473, by rfl⟩) (B 30947 (by norm_num) ⟨15473, by rfl⟩ (by norm_num))
theorem R82561 : Reach 82561 := rs (se 2 (by rfl) ⟨30960, by rfl⟩) (B 61921 (by norm_num) ⟨30960, by rfl⟩ (by norm_num))
theorem R311957 : Reach 311957 := rs (se 6 (by rfl) ⟨7311, by rfl⟩) (B 14623 (by norm_num) ⟨7311, by rfl⟩ (by norm_num))
theorem R180893 : Reach 180893 := rs (se 3 (by rfl) ⟨33917, by rfl⟩) (B 67835 (by norm_num) ⟨33917, by rfl⟩ (by norm_num))
theorem R82597 : Reach 82597 := rs (se 4 (by rfl) ⟨7743, by rfl⟩) (B 15487 (by norm_num) ⟨7743, by rfl⟩ (by norm_num))
theorem R82633 : Reach 82633 := rs (se 2 (by rfl) ⟨30987, by rfl⟩) (B 61975 (by norm_num) ⟨30987, by rfl⟩ (by norm_num))
theorem R82669 : Reach 82669 := rs (se 3 (by rfl) ⟨15500, by rfl⟩) (B 31001 (by norm_num) ⟨15500, by rfl⟩ (by norm_num))
theorem R82705 : Reach 82705 := rs (se 2 (by rfl) ⟨31014, by rfl⟩) (B 62029 (by norm_num) ⟨31014, by rfl⟩ (by norm_num))
theorem R377621 : Reach 377621 := rs (se 6 (by rfl) ⟨8850, by rfl⟩) (B 17701 (by norm_num) ⟨8850, by rfl⟩ (by norm_num))
theorem R82741 : Reach 82741 := rs (se 5 (by rfl) ⟨3878, by rfl⟩) (B 7757 (by norm_num) ⟨3878, by rfl⟩ (by norm_num))
theorem R82777 : Reach 82777 := rs (se 2 (by rfl) ⟨31041, by rfl⟩) (B 62083 (by norm_num) ⟨31041, by rfl⟩ (by norm_num))
theorem R82813 : Reach 82813 := rs (se 3 (by rfl) ⟨15527, by rfl⟩) (B 31055 (by norm_num) ⟨15527, by rfl⟩ (by norm_num))
theorem R82849 : Reach 82849 := rs (se 2 (by rfl) ⟨31068, by rfl⟩) (B 62137 (by norm_num) ⟨31068, by rfl⟩ (by norm_num))
theorem R82873 : Reach 82873 := rs (se 2 (by rfl) ⟨31077, by rfl⟩) (B 62155 (by norm_num) ⟨31077, by rfl⟩ (by norm_num))
theorem R246725 : Reach 246725 := rs (se 4 (by rfl) ⟨23130, by rfl⟩) (B 46261 (by norm_num) ⟨23130, by rfl⟩ (by norm_num))
theorem R82885 : Reach 82885 := rs (se 4 (by rfl) ⟨7770, by rfl⟩) (B 15541 (by norm_num) ⟨7770, by rfl⟩ (by norm_num))
theorem R82921 : Reach 82921 := rs (se 2 (by rfl) ⟨31095, by rfl⟩) (B 62191 (by norm_num) ⟨31095, by rfl⟩ (by norm_num))
theorem R181237 : Reach 181237 := rs (se 5 (by rfl) ⟨8495, by rfl⟩) (B 16991 (by norm_num) ⟨8495, by rfl⟩ (by norm_num))
theorem R279557 : Reach 279557 := rs (se 4 (by rfl) ⟨26208, by rfl⟩) (B 52417 (by norm_num) ⟨26208, by rfl⟩ (by norm_num))
theorem R82957 : Reach 82957 := rs (se 3 (by rfl) ⟨15554, by rfl⟩) (B 31109 (by norm_num) ⟨15554, by rfl⟩ (by norm_num))
theorem R82993 : Reach 82993 := rs (se 2 (by rfl) ⟨31122, by rfl⟩) (B 62245 (by norm_num) ⟨31122, by rfl⟩ (by norm_num))
theorem R83029 : Reach 83029 := rs (se 8 (by rfl) ⟨486, by rfl⟩) (B 973 (by norm_num) ⟨486, by rfl⟩ (by norm_num))
theorem R115805 : Reach 115805 := rs (se 3 (by rfl) ⟨21713, by rfl⟩) (B 43427 (by norm_num) ⟨21713, by rfl⟩ (by norm_num))
theorem R181349 : Reach 181349 := rs (se 4 (by rfl) ⟨17001, by rfl⟩) (B 34003 (by norm_num) ⟨17001, by rfl⟩ (by norm_num))
theorem R83065 : Reach 83065 := rs (se 2 (by rfl) ⟨31149, by rfl⟩) (B 62299 (by norm_num) ⟨31149, by rfl⟩ (by norm_num))
theorem R181397 : Reach 181397 := rs (se 6 (by rfl) ⟨4251, by rfl⟩) (B 8503 (by norm_num) ⟨4251, by rfl⟩ (by norm_num))
theorem R83101 : Reach 83101 := rs (se 3 (by rfl) ⟨15581, by rfl⟩) (B 31163 (by norm_num) ⟨15581, by rfl⟩ (by norm_num))
theorem R83137 : Reach 83137 := rs (se 2 (by rfl) ⟨31176, by rfl⟩) (B 62353 (by norm_num) ⟨31176, by rfl⟩ (by norm_num))
theorem R83173 : Reach 83173 := rs (se 4 (by rfl) ⟨7797, by rfl⟩) (B 15595 (by norm_num) ⟨7797, by rfl⟩ (by norm_num))
theorem R83197 : Reach 83197 := rs (se 3 (by rfl) ⟨15599, by rfl⟩) (B 31199 (by norm_num) ⟨15599, by rfl⟩ (by norm_num))
theorem R83209 : Reach 83209 := rs (se 2 (by rfl) ⟨31203, by rfl⟩) (B 62407 (by norm_num) ⟨31203, by rfl⟩ (by norm_num))
theorem R181541 : Reach 181541 := rs (se 4 (by rfl) ⟨17019, by rfl⟩) (B 34039 (by norm_num) ⟨17019, by rfl⟩ (by norm_num))
theorem R279845 : Reach 279845 := rs (se 4 (by rfl) ⟨26235, by rfl⟩) (B 52471 (by norm_num) ⟨26235, by rfl⟩ (by norm_num))
theorem R83245 : Reach 83245 := rs (se 3 (by rfl) ⟨15608, by rfl⟩) (B 31217 (by norm_num) ⟨15608, by rfl⟩ (by norm_num))
theorem R83281 : Reach 83281 := rs (se 2 (by rfl) ⟨31230, by rfl⟩) (B 62461 (by norm_num) ⟨31230, by rfl⟩ (by norm_num))
theorem R247157 : Reach 247157 := rs (se 5 (by rfl) ⟨11585, by rfl⟩) (B 23171 (by norm_num) ⟨11585, by rfl⟩ (by norm_num))
theorem R83317 : Reach 83317 := rs (se 5 (by rfl) ⟨3905, by rfl⟩) (B 7811 (by norm_num) ⟨3905, by rfl⟩ (by norm_num))
theorem R83353 : Reach 83353 := rs (se 2 (by rfl) ⟨31257, by rfl⟩) (B 62515 (by norm_num) ⟨31257, by rfl⟩ (by norm_num))
theorem R83389 : Reach 83389 := rs (se 3 (by rfl) ⟨15635, by rfl⟩) (B 31271 (by norm_num) ⟨15635, by rfl⟩ (by norm_num))
theorem R2803157 : Reach 2803157 := rs (se 7 (by rfl) ⟨32849, by rfl⟩) (B 65699 (by norm_num) ⟨32849, by rfl⟩ (by norm_num))
theorem R83425 : Reach 83425 := rs (se 2 (by rfl) ⟨31284, by rfl⟩) (B 62569 (by norm_num) ⟨31284, by rfl⟩ (by norm_num))
theorem R378341 : Reach 378341 := rs (se 4 (by rfl) ⟨35469, by rfl⟩) (B 70939 (by norm_num) ⟨35469, by rfl⟩ (by norm_num))
theorem R83461 : Reach 83461 := rs (se 4 (by rfl) ⟨7824, by rfl⟩) (B 15649 (by norm_num) ⟨7824, by rfl⟩ (by norm_num))
theorem R83497 : Reach 83497 := rs (se 2 (by rfl) ⟨31311, by rfl⟩) (B 62623 (by norm_num) ⟨31311, by rfl⟩ (by norm_num))
theorem R83533 : Reach 83533 := rs (se 3 (by rfl) ⟨15662, by rfl⟩) (B 31325 (by norm_num) ⟨15662, by rfl⟩ (by norm_num))
theorem R83569 : Reach 83569 := rs (se 2 (by rfl) ⟨31338, by rfl⟩) (B 62677 (by norm_num) ⟨31338, by rfl⟩ (by norm_num))
theorem R181885 : Reach 181885 := rs (se 3 (by rfl) ⟨34103, by rfl⟩) (B 68207 (by norm_num) ⟨34103, by rfl⟩ (by norm_num))
theorem R83605 : Reach 83605 := rs (se 6 (by rfl) ⟨1959, by rfl⟩) (B 3919 (by norm_num) ⟨1959, by rfl⟩ (by norm_num))
theorem R411317 : Reach 411317 := rs (se 5 (by rfl) ⟨19280, by rfl⟩) (B 38561 (by norm_num) ⟨19280, by rfl⟩ (by norm_num))
theorem R83641 : Reach 83641 := rs (se 2 (by rfl) ⟨31365, by rfl⟩) (B 62731 (by norm_num) ⟨31365, by rfl⟩ (by norm_num))
theorem R83677 : Reach 83677 := rs (se 3 (by rfl) ⟨15689, by rfl⟩) (B 31379 (by norm_num) ⟨15689, by rfl⟩ (by norm_num))
theorem R116453 : Reach 116453 := rs (se 4 (by rfl) ⟨10917, by rfl⟩) (B 21835 (by norm_num) ⟨10917, by rfl⟩ (by norm_num))
theorem R181997 : Reach 181997 := rs (se 3 (by rfl) ⟨34124, by rfl⟩) (B 68249 (by norm_num) ⟨34124, by rfl⟩ (by norm_num))
theorem R83713 : Reach 83713 := rs (se 2 (by rfl) ⟨31392, by rfl⟩) (B 62785 (by norm_num) ⟨31392, by rfl⟩ (by norm_num))
theorem R247589 : Reach 247589 := rs (se 4 (by rfl) ⟨23211, by rfl⟩) (B 46423 (by norm_num) ⟨23211, by rfl⟩ (by norm_num))
theorem R83749 : Reach 83749 := rs (se 4 (by rfl) ⟨7851, by rfl⟩) (B 15703 (by norm_num) ⟨7851, by rfl⟩ (by norm_num))
theorem R83785 : Reach 83785 := rs (se 2 (by rfl) ⟨31419, by rfl⟩) (B 62839 (by norm_num) ⟨31419, by rfl⟩ (by norm_num))
theorem R83821 : Reach 83821 := rs (se 3 (by rfl) ⟨15716, by rfl⟩) (B 31433 (by norm_num) ⟨15716, by rfl⟩ (by norm_num))
theorem R83857 : Reach 83857 := rs (se 2 (by rfl) ⟨31446, by rfl⟩) (B 62893 (by norm_num) ⟨31446, by rfl⟩ (by norm_num))
theorem R182189 : Reach 182189 := rs (se 3 (by rfl) ⟨34160, by rfl⟩) (B 68321 (by norm_num) ⟨34160, by rfl⟩ (by norm_num))
theorem R83893 : Reach 83893 := rs (se 5 (by rfl) ⟨3932, by rfl⟩) (B 7865 (by norm_num) ⟨3932, by rfl⟩ (by norm_num))
theorem R83929 : Reach 83929 := rs (se 2 (by rfl) ⟨31473, by rfl⟩) (B 62947 (by norm_num) ⟨31473, by rfl⟩ (by norm_num))
theorem R83965 : Reach 83965 := rs (se 3 (by rfl) ⟨15743, by rfl⟩) (B 31487 (by norm_num) ⟨15743, by rfl⟩ (by norm_num))
theorem R84001 : Reach 84001 := rs (se 2 (by rfl) ⟨31500, by rfl⟩) (B 63001 (by norm_num) ⟨31500, by rfl⟩ (by norm_num))
theorem R378917 : Reach 378917 := rs (se 4 (by rfl) ⟨35523, by rfl⟩) (B 71047 (by norm_num) ⟨35523, by rfl⟩ (by norm_num))
theorem R84037 : Reach 84037 := rs (se 4 (by rfl) ⟨7878, by rfl⟩) (B 15757 (by norm_num) ⟨7878, by rfl⟩ (by norm_num))
theorem R84073 : Reach 84073 := rs (se 2 (by rfl) ⟨31527, by rfl⟩) (B 63055 (by norm_num) ⟨31527, by rfl⟩ (by norm_num))
theorem R84109 : Reach 84109 := rs (se 3 (by rfl) ⟨15770, by rfl⟩) (B 31541 (by norm_num) ⟨15770, by rfl⟩ (by norm_num))
theorem R84145 : Reach 84145 := rs (se 2 (by rfl) ⟨31554, by rfl⟩) (B 63109 (by norm_num) ⟨31554, by rfl⟩ (by norm_num))
theorem R248021 : Reach 248021 := rs (se 7 (by rfl) ⟨2906, by rfl⟩) (B 5813 (by norm_num) ⟨2906, by rfl⟩ (by norm_num))
theorem R84181 : Reach 84181 := rs (se 7 (by rfl) ⟨986, by rfl⟩) (B 1973 (by norm_num) ⟨986, by rfl⟩ (by norm_num))
theorem R84217 : Reach 84217 := rs (se 2 (by rfl) ⟨31581, by rfl⟩) (B 63163 (by norm_num) ⟨31581, by rfl⟩ (by norm_num))
theorem R182533 : Reach 182533 := rs (se 4 (by rfl) ⟨17112, by rfl⟩) (B 34225 (by norm_num) ⟨17112, by rfl⟩ (by norm_num))
theorem R84253 : Reach 84253 := rs (se 3 (by rfl) ⟨15797, by rfl⟩) (B 31595 (by norm_num) ⟨15797, by rfl⟩ (by norm_num))
theorem R84289 : Reach 84289 := rs (se 2 (by rfl) ⟨31608, by rfl⟩) (B 63217 (by norm_num) ⟨31608, by rfl⟩ (by norm_num))
theorem R313685 : Reach 313685 := rs (se 10 (by rfl) ⟨459, by rfl⟩) (B 919 (by norm_num) ⟨459, by rfl⟩ (by norm_num))
theorem R84317 : Reach 84317 := rs (se 3 (by rfl) ⟨15809, by rfl⟩) (B 31619 (by norm_num) ⟨15809, by rfl⟩ (by norm_num))
theorem R84325 : Reach 84325 := rs (se 4 (by rfl) ⟨7905, by rfl⟩) (B 15811 (by norm_num) ⟨7905, by rfl⟩ (by norm_num))
theorem R182645 : Reach 182645 := rs (se 5 (by rfl) ⟨8561, by rfl⟩) (B 17123 (by norm_num) ⟨8561, by rfl⟩ (by norm_num))
theorem R313733 : Reach 313733 := rs (se 4 (by rfl) ⟨29412, by rfl⟩) (B 58825 (by norm_num) ⟨29412, by rfl⟩ (by norm_num))
theorem R84361 : Reach 84361 := rs (se 2 (by rfl) ⟨31635, by rfl⟩) (B 63271 (by norm_num) ⟨31635, by rfl⟩ (by norm_num))
theorem R84397 : Reach 84397 := rs (se 3 (by rfl) ⟨15824, by rfl⟩) (B 31649 (by norm_num) ⟨15824, by rfl⟩ (by norm_num))
theorem R281029 : Reach 281029 := rs (se 4 (by rfl) ⟨26346, by rfl⟩) (B 52693 (by norm_num) ⟨26346, by rfl⟩ (by norm_num))
theorem R84433 : Reach 84433 := rs (se 2 (by rfl) ⟨31662, by rfl⟩) (B 63325 (by norm_num) ⟨31662, by rfl⟩ (by norm_num))
theorem R1264085 : Reach 1264085 := rs (se 7 (by rfl) ⟨14813, by rfl⟩) (B 29627 (by norm_num) ⟨14813, by rfl⟩ (by norm_num))
theorem R84469 : Reach 84469 := rs (se 5 (by rfl) ⟨3959, by rfl⟩) (B 7919 (by norm_num) ⟨3959, by rfl⟩ (by norm_num))
theorem R84505 : Reach 84505 := rs (se 2 (by rfl) ⟨31689, by rfl⟩) (B 63379 (by norm_num) ⟨31689, by rfl⟩ (by norm_num))
theorem R182837 : Reach 182837 := rs (se 5 (by rfl) ⟨8570, by rfl⟩) (B 17141 (by norm_num) ⟨8570, by rfl⟩ (by norm_num))
theorem R248453 : Reach 248453 := rs (se 4 (by rfl) ⟨23292, by rfl⟩) (B 46585 (by norm_num) ⟨23292, by rfl⟩ (by norm_num))
theorem R117445 : Reach 117445 := rs (se 4 (by rfl) ⟨11010, by rfl⟩) (B 22021 (by norm_num) ⟨11010, by rfl⟩ (by norm_num))
theorem R346837 : Reach 346837 := rs (se 7 (by rfl) ⟨4064, by rfl⟩) (B 8129 (by norm_num) ⟨4064, by rfl⟩ (by norm_num))
theorem R281333 : Reach 281333 := rs (se 5 (by rfl) ⟨13187, by rfl⟩) (B 26375 (by norm_num) ⟨13187, by rfl⟩ (by norm_num))
theorem R183181 : Reach 183181 := rs (se 3 (by rfl) ⟨34346, by rfl⟩) (B 68693 (by norm_num) ⟨34346, by rfl⟩ (by norm_num))
theorem R478133 : Reach 478133 := rs (se 5 (by rfl) ⟨22412, by rfl⟩) (B 44825 (by norm_num) ⟨22412, by rfl⟩ (by norm_num))
theorem R183293 : Reach 183293 := rs (se 3 (by rfl) ⟨34367, by rfl⟩) (B 68735 (by norm_num) ⟨34367, by rfl⟩ (by norm_num))
theorem R248885 : Reach 248885 := rs (se 5 (by rfl) ⟨11666, by rfl⟩) (B 23333 (by norm_num) ⟨11666, by rfl⟩ (by norm_num))
theorem R117893 : Reach 117893 := rs (se 4 (by rfl) ⟨11052, by rfl⟩) (B 22105 (by norm_num) ⟨11052, by rfl⟩ (by norm_num))
theorem R183485 : Reach 183485 := rs (se 3 (by rfl) ⟨34403, by rfl⟩) (B 68807 (by norm_num) ⟨34403, by rfl⟩ (by norm_num))
theorem R380213 : Reach 380213 := rs (se 5 (by rfl) ⟨17822, by rfl⟩) (B 35645 (by norm_num) ⟨17822, by rfl⟩ (by norm_num))
theorem R118093 : Reach 118093 := rs (se 3 (by rfl) ⟨22142, by rfl⟩) (B 44285 (by norm_num) ⟨22142, by rfl⟩ (by norm_num))
theorem R249301 : Reach 249301 := rs (se 7 (by rfl) ⟨2921, by rfl⟩) (B 5843 (by norm_num) ⟨2921, by rfl⟩ (by norm_num))
theorem R249317 : Reach 249317 := rs (se 4 (by rfl) ⟨23373, by rfl⟩) (B 46747 (by norm_num) ⟨23373, by rfl⟩ (by norm_num))
theorem R183829 : Reach 183829 := rs (se 6 (by rfl) ⟨4308, by rfl⟩) (B 8617 (by norm_num) ⟨4308, by rfl⟩ (by norm_num))
theorem R85537 : Reach 85537 := rs (se 2 (by rfl) ⟨32076, by rfl⟩) (B 64153 (by norm_num) ⟨32076, by rfl⟩ (by norm_num))
theorem R118349 : Reach 118349 := rs (se 3 (by rfl) ⟨22190, by rfl⟩) (B 44381 (by norm_num) ⟨22190, by rfl⟩ (by norm_num))
theorem R446069 : Reach 446069 := rs (se 5 (by rfl) ⟨20909, by rfl⟩) (B 41819 (by norm_num) ⟨20909, by rfl⟩ (by norm_num))
theorem R183941 : Reach 183941 := rs (se 4 (by rfl) ⟨17244, by rfl⟩) (B 34489 (by norm_num) ⟨17244, by rfl⟩ (by norm_num))
theorem R85729 : Reach 85729 := rs (se 2 (by rfl) ⟨32148, by rfl⟩) (B 64297 (by norm_num) ⟨32148, by rfl⟩ (by norm_num))
theorem R610037 : Reach 610037 := rs (se 5 (by rfl) ⟨28595, by rfl⟩) (B 57191 (by norm_num) ⟨28595, by rfl⟩ (by norm_num))
theorem R184133 : Reach 184133 := rs (se 4 (by rfl) ⟨17262, by rfl⟩) (B 34525 (by norm_num) ⟨17262, by rfl⟩ (by norm_num))
theorem R413525 : Reach 413525 := rs (se 9 (by rfl) ⟨1211, by rfl⟩) (B 2423 (by norm_num) ⟨1211, by rfl⟩ (by norm_num))
theorem R249749 : Reach 249749 := rs (se 6 (by rfl) ⟨5853, by rfl⟩) (B 11707 (by norm_num) ⟨5853, by rfl⟩ (by norm_num))
theorem R184477 : Reach 184477 := rs (se 3 (by rfl) ⟨34589, by rfl⟩) (B 69179 (by norm_num) ⟨34589, by rfl⟩ (by norm_num))
theorem R151733 : Reach 151733 := rs (se 5 (by rfl) ⟨7112, by rfl⟩) (B 14225 (by norm_num) ⟨7112, by rfl⟩ (by norm_num))
theorem R184589 : Reach 184589 := rs (se 3 (by rfl) ⟨34610, by rfl⟩) (B 69221 (by norm_num) ⟨34610, by rfl⟩ (by norm_num))
theorem R250181 : Reach 250181 := rs (se 4 (by rfl) ⟨23454, by rfl⟩) (B 46909 (by norm_num) ⟨23454, by rfl⟩ (by norm_num))
theorem R184781 : Reach 184781 := rs (se 3 (by rfl) ⟨34646, by rfl⟩) (B 69293 (by norm_num) ⟨34646, by rfl⟩ (by norm_num))
theorem R86609 : Reach 86609 := rs (se 2 (by rfl) ⟨32478, by rfl⟩) (B 64957 (by norm_num) ⟨32478, by rfl⟩ (by norm_num))
theorem R119477 : Reach 119477 := rs (se 5 (by rfl) ⟨5600, by rfl⟩) (B 11201 (by norm_num) ⟨5600, by rfl⟩ (by norm_num))
theorem R250613 : Reach 250613 := rs (se 5 (by rfl) ⟨11747, by rfl⟩) (B 23495 (by norm_num) ⟨11747, by rfl⟩ (by norm_num))
theorem R185125 : Reach 185125 := rs (se 4 (by rfl) ⟨17355, by rfl⟩) (B 34711 (by norm_num) ⟨17355, by rfl⟩ (by norm_num))
theorem R283445 : Reach 283445 := rs (se 5 (by rfl) ⟨13286, by rfl⟩) (B 26573 (by norm_num) ⟨13286, by rfl⟩ (by norm_num))
theorem R185237 : Reach 185237 := rs (se 6 (by rfl) ⟨4341, by rfl⟩) (B 8683 (by norm_num) ⟨4341, by rfl⟩ (by norm_num))
theorem R807893 : Reach 807893 := rs (se 7 (by rfl) ⟨9467, by rfl⟩) (B 18935 (by norm_num) ⟨9467, by rfl⟩ (by norm_num))
theorem R87113 : Reach 87113 := rs (se 2 (by rfl) ⟨32667, by rfl⟩) (B 65335 (by norm_num) ⟨32667, by rfl⟩ (by norm_num))
theorem R185429 : Reach 185429 := rs (se 8 (by rfl) ⟨1086, by rfl⟩) (B 2173 (by norm_num) ⟨1086, by rfl⟩ (by norm_num))
theorem R283733 : Reach 283733 := rs (se 8 (by rfl) ⟨1662, by rfl⟩) (B 3325 (by norm_num) ⟨1662, by rfl⟩ (by norm_num))
theorem R87161 : Reach 87161 := rs (se 2 (by rfl) ⟨32685, by rfl⟩) (B 65371 (by norm_num) ⟨32685, by rfl⟩ (by norm_num))
theorem R152741 : Reach 152741 := rs (se 4 (by rfl) ⟨14319, by rfl⟩) (B 28639 (by norm_num) ⟨14319, by rfl⟩ (by norm_num))
theorem R251045 : Reach 251045 := rs (se 4 (by rfl) ⟨23535, by rfl⟩) (B 47071 (by norm_num) ⟨23535, by rfl⟩ (by norm_num))
theorem R119989 : Reach 119989 := rs (se 5 (by rfl) ⟨5624, by rfl⟩) (B 11249 (by norm_num) ⟨5624, by rfl⟩ (by norm_num))
theorem R1823957 : Reach 1823957 := rs (se 7 (by rfl) ⟨21374, by rfl⟩) (B 42749 (by norm_num) ⟨21374, by rfl⟩ (by norm_num))
theorem R120109 : Reach 120109 := rs (se 3 (by rfl) ⟨22520, by rfl⟩) (B 45041 (by norm_num) ⟨22520, by rfl⟩ (by norm_num))
theorem R152885 : Reach 152885 := rs (se 5 (by rfl) ⟨7166, by rfl⟩) (B 14333 (by norm_num) ⟨7166, by rfl⟩ (by norm_num))
theorem R87421 : Reach 87421 := rs (se 3 (by rfl) ⟨16391, by rfl⟩) (B 32783 (by norm_num) ⟨16391, by rfl⟩ (by norm_num))
theorem R120197 : Reach 120197 := rs (se 4 (by rfl) ⟨11268, by rfl⟩) (B 22537 (by norm_num) ⟨11268, by rfl⟩ (by norm_num))
theorem R185773 : Reach 185773 := rs (se 3 (by rfl) ⟨34832, by rfl⟩) (B 69665 (by norm_num) ⟨34832, by rfl⟩ (by norm_num))
theorem R120325 : Reach 120325 := rs (se 4 (by rfl) ⟨11280, by rfl⟩) (B 22561 (by norm_num) ⟨11280, by rfl⟩ (by norm_num))
theorem R185885 : Reach 185885 := rs (se 3 (by rfl) ⟨34853, by rfl⟩) (B 69707 (by norm_num) ⟨34853, by rfl⟩ (by norm_num))
theorem R251477 : Reach 251477 := rs (se 8 (by rfl) ⟨1473, by rfl⟩) (B 2947 (by norm_num) ⟨1473, by rfl⟩ (by norm_num))
theorem R120413 : Reach 120413 := rs (se 3 (by rfl) ⟨22577, by rfl⟩) (B 45155 (by norm_num) ⟨22577, by rfl⟩ (by norm_num))
theorem R87685 : Reach 87685 := rs (se 4 (by rfl) ⟨8220, by rfl⟩) (B 16441 (by norm_num) ⟨8220, by rfl⟩ (by norm_num))
theorem R153245 : Reach 153245 := rs (se 3 (by rfl) ⟨28733, by rfl⟩) (B 57467 (by norm_num) ⟨28733, by rfl⟩ (by norm_num))
theorem R120541 : Reach 120541 := rs (se 3 (by rfl) ⟨22601, by rfl⟩) (B 45203 (by norm_num) ⟨22601, by rfl⟩ (by norm_num))
theorem R186077 : Reach 186077 := rs (se 3 (by rfl) ⟨34889, by rfl⟩) (B 69779 (by norm_num) ⟨34889, by rfl⟩ (by norm_num))
theorem R87805 : Reach 87805 := rs (se 3 (by rfl) ⟨16463, by rfl⟩) (B 32927 (by norm_num) ⟨16463, by rfl⟩ (by norm_num))
theorem R120629 : Reach 120629 := rs (se 5 (by rfl) ⟨5654, by rfl⟩) (B 11309 (by norm_num) ⟨5654, by rfl⟩ (by norm_num))
theorem R120757 : Reach 120757 := rs (se 5 (by rfl) ⟨5660, by rfl⟩) (B 11321 (by norm_num) ⟨5660, by rfl⟩ (by norm_num))
theorem R251909 : Reach 251909 := rs (se 4 (by rfl) ⟨23616, by rfl⟩) (B 47233 (by norm_num) ⟨23616, by rfl⟩ (by norm_num))
theorem R120845 : Reach 120845 := rs (se 3 (by rfl) ⟨22658, by rfl⟩) (B 45317 (by norm_num) ⟨22658, by rfl⟩ (by norm_num))
theorem R186421 : Reach 186421 := rs (se 5 (by rfl) ⟨8738, by rfl⟩) (B 17477 (by norm_num) ⟨8738, by rfl⟩ (by norm_num))
theorem R120973 : Reach 120973 := rs (se 3 (by rfl) ⟨22682, by rfl⟩) (B 45365 (by norm_num) ⟨22682, by rfl⟩ (by norm_num))
theorem R186533 : Reach 186533 := rs (se 4 (by rfl) ⟨17487, by rfl⟩) (B 34975 (by norm_num) ⟨17487, by rfl⟩ (by norm_num))
theorem R121061 : Reach 121061 := rs (se 4 (by rfl) ⟨11349, by rfl⟩) (B 22699 (by norm_num) ⟨11349, by rfl⟩ (by norm_num))
theorem R284917 : Reach 284917 := rs (se 5 (by rfl) ⟨13355, by rfl⟩) (B 26711 (by norm_num) ⟨13355, by rfl⟩ (by norm_num))
theorem R121189 : Reach 121189 := rs (se 4 (by rfl) ⟨11361, by rfl⟩) (B 22723 (by norm_num) ⟨11361, by rfl⟩ (by norm_num))
theorem R186725 : Reach 186725 := rs (se 4 (by rfl) ⟨17505, by rfl⟩) (B 35011 (by norm_num) ⟨17505, by rfl⟩ (by norm_num))
theorem R252341 : Reach 252341 := rs (se 5 (by rfl) ⟨11828, by rfl⟩) (B 23657 (by norm_num) ⟨11828, by rfl⟩ (by norm_num))
theorem R121277 : Reach 121277 := rs (se 3 (by rfl) ⟨22739, by rfl⟩) (B 45479 (by norm_num) ⟨22739, by rfl⟩ (by norm_num))
theorem R154133 : Reach 154133 := rs (se 6 (by rfl) ⟨3612, by rfl⟩) (B 7225 (by norm_num) ⟨3612, by rfl⟩ (by norm_num))
theorem R285221 : Reach 285221 := rs (se 4 (by rfl) ⟨26739, by rfl⟩) (B 53479 (by norm_num) ⟨26739, by rfl⟩ (by norm_num))
theorem R318005 : Reach 318005 := rs (se 5 (by rfl) ⟨14906, by rfl⟩) (B 29813 (by norm_num) ⟨14906, by rfl⟩ (by norm_num))
theorem R121405 : Reach 121405 := rs (se 3 (by rfl) ⟨22763, by rfl⟩) (B 45527 (by norm_num) ⟨22763, by rfl⟩ (by norm_num))
theorem R88661 : Reach 88661 := rs (se 8 (by rfl) ⟨519, by rfl⟩) (B 1039 (by norm_num) ⟨519, by rfl⟩ (by norm_num))
theorem R350837 : Reach 350837 := rs (se 5 (by rfl) ⟨16445, by rfl⟩) (B 32891 (by norm_num) ⟨16445, by rfl⟩ (by norm_num))
theorem R121493 : Reach 121493 := rs (se 6 (by rfl) ⟨2847, by rfl⟩) (B 5695 (by norm_num) ⟨2847, by rfl⟩ (by norm_num))
theorem R187069 : Reach 187069 := rs (se 3 (by rfl) ⟨35075, by rfl⟩) (B 70151 (by norm_num) ⟨35075, by rfl⟩ (by norm_num))
theorem R154381 : Reach 154381 := rs (se 3 (by rfl) ⟨28946, by rfl⟩) (B 57893 (by norm_num) ⟨28946, by rfl⟩ (by norm_num))
theorem R121621 : Reach 121621 := rs (se 6 (by rfl) ⟨2850, by rfl⟩) (B 5701 (by norm_num) ⟨2850, by rfl⟩ (by norm_num))
theorem R187181 : Reach 187181 := rs (se 3 (by rfl) ⟨35096, by rfl⟩) (B 70193 (by norm_num) ⟨35096, by rfl⟩ (by norm_num))
theorem R252773 : Reach 252773 := rs (se 4 (by rfl) ⟨23697, by rfl⟩) (B 47395 (by norm_num) ⟨23697, by rfl⟩ (by norm_num))
theorem R121709 : Reach 121709 := rs (se 3 (by rfl) ⟨22820, by rfl⟩) (B 45641 (by norm_num) ⟨22820, by rfl⟩ (by norm_num))
theorem R220117 : Reach 220117 := rs (se 7 (by rfl) ⟨2579, by rfl⟩) (B 5159 (by norm_num) ⟨2579, by rfl⟩ (by norm_num))
theorem R121837 : Reach 121837 := rs (se 3 (by rfl) ⟨22844, by rfl⟩) (B 45689 (by norm_num) ⟨22844, by rfl⟩ (by norm_num))
theorem R187373 : Reach 187373 := rs (se 3 (by rfl) ⟨35132, by rfl⟩) (B 70265 (by norm_num) ⟨35132, by rfl⟩ (by norm_num))
theorem R121925 : Reach 121925 := rs (se 4 (by rfl) ⟨11430, by rfl⟩) (B 22861 (by norm_num) ⟨11430, by rfl⟩ (by norm_num))
theorem R122053 : Reach 122053 := rs (se 4 (by rfl) ⟨11442, by rfl⟩) (B 22885 (by norm_num) ⟨11442, by rfl⟩ (by norm_num))
theorem R154885 : Reach 154885 := rs (se 4 (by rfl) ⟨14520, by rfl⟩) (B 29041 (by norm_num) ⟨14520, by rfl⟩ (by norm_num))
theorem R253205 : Reach 253205 := rs (se 6 (by rfl) ⟨5934, by rfl⟩) (B 11869 (by norm_num) ⟨5934, by rfl⟩ (by norm_num))
theorem R122141 : Reach 122141 := rs (se 3 (by rfl) ⟨22901, by rfl⟩) (B 45803 (by norm_num) ⟨22901, by rfl⟩ (by norm_num))
theorem R89381 : Reach 89381 := rs (se 4 (by rfl) ⟨8379, by rfl⟩) (B 16759 (by norm_num) ⟨8379, by rfl⟩ (by norm_num))
theorem R89413 : Reach 89413 := rs (se 4 (by rfl) ⟨8382, by rfl⟩) (B 16765 (by norm_num) ⟨8382, by rfl⟩ (by norm_num))
theorem R187717 : Reach 187717 := rs (se 4 (by rfl) ⟨17598, by rfl⟩) (B 35197 (by norm_num) ⟨17598, by rfl⟩ (by norm_num))
theorem R122269 : Reach 122269 := rs (se 3 (by rfl) ⟨22925, by rfl⟩) (B 45851 (by norm_num) ⟨22925, by rfl⟩ (by norm_num))
theorem R187829 : Reach 187829 := rs (se 5 (by rfl) ⟨8804, by rfl⟩) (B 17609 (by norm_num) ⟨8804, by rfl⟩ (by norm_num))
theorem R122357 : Reach 122357 := rs (se 5 (by rfl) ⟨5735, by rfl⟩) (B 11471 (by norm_num) ⟨5735, by rfl⟩ (by norm_num))
theorem R89689 : Reach 89689 := rs (se 2 (by rfl) ⟨33633, by rfl⟩) (B 67267 (by norm_num) ⟨33633, by rfl⟩ (by norm_num))
theorem R122485 : Reach 122485 := rs (se 5 (by rfl) ⟨5741, by rfl⟩) (B 11483 (by norm_num) ⟨5741, by rfl⟩ (by norm_num))
theorem R188021 : Reach 188021 := rs (se 5 (by rfl) ⟨8813, by rfl⟩) (B 17627 (by norm_num) ⟨8813, by rfl⟩ (by norm_num))
theorem R89785 : Reach 89785 := rs (se 2 (by rfl) ⟨33669, by rfl⟩) (B 67339 (by norm_num) ⟨33669, by rfl⟩ (by norm_num))
theorem R122573 : Reach 122573 := rs (se 3 (by rfl) ⟨22982, by rfl⟩) (B 45965 (by norm_num) ⟨22982, by rfl⟩ (by norm_num))
theorem R351989 : Reach 351989 := rs (se 5 (by rfl) ⟨16499, by rfl⟩) (B 32999 (by norm_num) ⟨16499, by rfl⟩ (by norm_num))
theorem R89929 : Reach 89929 := rs (se 2 (by rfl) ⟨33723, by rfl⟩) (B 67447 (by norm_num) ⟨33723, by rfl⟩ (by norm_num))
theorem R122701 : Reach 122701 := rs (se 3 (by rfl) ⟨23006, by rfl⟩) (B 46013 (by norm_num) ⟨23006, by rfl⟩ (by norm_num))
theorem R548693 : Reach 548693 := rs (se 9 (by rfl) ⟨1607, by rfl⟩) (B 3215 (by norm_num) ⟨1607, by rfl⟩ (by norm_num))
theorem R122789 : Reach 122789 := rs (se 4 (by rfl) ⟨11511, by rfl⟩) (B 23023 (by norm_num) ⟨11511, by rfl⟩ (by norm_num))
theorem R188365 : Reach 188365 := rs (se 3 (by rfl) ⟨35318, by rfl⟩) (B 70637 (by norm_num) ⟨35318, by rfl⟩ (by norm_num))
theorem R122885 : Reach 122885 := rs (se 4 (by rfl) ⟨11520, by rfl⟩) (B 23041 (by norm_num) ⟨11520, by rfl⟩ (by norm_num))
theorem R122917 : Reach 122917 := rs (se 4 (by rfl) ⟨11523, by rfl⟩) (B 23047 (by norm_num) ⟨11523, by rfl⟩ (by norm_num))
theorem R90173 : Reach 90173 := rs (se 3 (by rfl) ⟨16907, by rfl⟩) (B 33815 (by norm_num) ⟨16907, by rfl⟩ (by norm_num))
theorem R188477 : Reach 188477 := rs (se 3 (by rfl) ⟨35339, by rfl⟩) (B 70679 (by norm_num) ⟨35339, by rfl⟩ (by norm_num))
theorem R680021 : Reach 680021 := rs (se 8 (by rfl) ⟨3984, by rfl⟩) (B 7969 (by norm_num) ⟨3984, by rfl⟩ (by norm_num))
theorem R90229 : Reach 90229 := rs (se 5 (by rfl) ⟨4229, by rfl⟩) (B 8459 (by norm_num) ⟨4229, by rfl⟩ (by norm_num))
theorem R123005 : Reach 123005 := rs (se 3 (by rfl) ⟨23063, by rfl⟩) (B 46127 (by norm_num) ⟨23063, by rfl⟩ (by norm_num))
theorem R155773 : Reach 155773 := rs (se 3 (by rfl) ⟨29207, by rfl⟩) (B 58415 (by norm_num) ⟨29207, by rfl⟩ (by norm_num))
theorem R90325 : Reach 90325 := rs (se 7 (by rfl) ⟨1058, by rfl⟩) (B 2117 (by norm_num) ⟨1058, by rfl⟩ (by norm_num))
theorem R123133 : Reach 123133 := rs (se 3 (by rfl) ⟨23087, by rfl⟩) (B 46175 (by norm_num) ⟨23087, by rfl⟩ (by norm_num))
theorem R188669 : Reach 188669 := rs (se 3 (by rfl) ⟨35375, by rfl⟩) (B 70751 (by norm_num) ⟨35375, by rfl⟩ (by norm_num))
theorem R123173 : Reach 123173 := rs (se 4 (by rfl) ⟨11547, by rfl⟩) (B 23095 (by norm_num) ⟨11547, by rfl⟩ (by norm_num))
theorem R319781 : Reach 319781 := rs (se 4 (by rfl) ⟨29979, by rfl⟩) (B 59959 (by norm_num) ⟨29979, by rfl⟩ (by norm_num))
theorem R123221 : Reach 123221 := rs (se 10 (by rfl) ⟨180, by rfl⟩) (B 361 (by norm_num) ⟨180, by rfl⟩ (by norm_num))
theorem R90497 : Reach 90497 := rs (se 2 (by rfl) ⟨33936, by rfl⟩) (B 67873 (by norm_num) ⟨33936, by rfl⟩ (by norm_num))
theorem R844181 : Reach 844181 := rs (se 6 (by rfl) ⟨19785, by rfl⟩) (B 39571 (by norm_num) ⟨19785, by rfl⟩ (by norm_num))
theorem R90553 : Reach 90553 := rs (se 2 (by rfl) ⟨33957, by rfl⟩) (B 67915 (by norm_num) ⟨33957, by rfl⟩ (by norm_num))
theorem R123349 : Reach 123349 := rs (se 7 (by rfl) ⟨1445, by rfl⟩) (B 2891 (by norm_num) ⟨1445, by rfl⟩ (by norm_num))
theorem R352757 : Reach 352757 := rs (se 5 (by rfl) ⟨16535, by rfl⟩) (B 33071 (by norm_num) ⟨16535, by rfl⟩ (by norm_num))
theorem R320021 : Reach 320021 := rs (se 6 (by rfl) ⟨7500, by rfl⟩) (B 15001 (by norm_num) ⟨7500, by rfl⟩ (by norm_num))
theorem R90649 : Reach 90649 := rs (se 2 (by rfl) ⟨33993, by rfl⟩) (B 67987 (by norm_num) ⟨33993, by rfl⟩ (by norm_num))
theorem R123437 : Reach 123437 := rs (se 3 (by rfl) ⟨23144, by rfl⟩) (B 46289 (by norm_num) ⟨23144, by rfl⟩ (by norm_num))
theorem R189013 : Reach 189013 := rs (se 8 (by rfl) ⟨1107, by rfl⟩) (B 2215 (by norm_num) ⟨1107, by rfl⟩ (by norm_num))
theorem R156269 : Reach 156269 := rs (se 3 (by rfl) ⟨29300, by rfl⟩) (B 58601 (by norm_num) ⟨29300, by rfl⟩ (by norm_num))
theorem R123565 : Reach 123565 := rs (se 3 (by rfl) ⟨23168, by rfl⟩) (B 46337 (by norm_num) ⟨23168, by rfl⟩ (by norm_num))
theorem R90821 : Reach 90821 := rs (se 4 (by rfl) ⟨8514, by rfl⟩) (B 17029 (by norm_num) ⟨8514, by rfl⟩ (by norm_num))
theorem R189125 : Reach 189125 := rs (se 4 (by rfl) ⟨17730, by rfl⟩) (B 35461 (by norm_num) ⟨17730, by rfl⟩ (by norm_num))
theorem R90877 : Reach 90877 := rs (se 3 (by rfl) ⟨17039, by rfl⟩) (B 34079 (by norm_num) ⟨17039, by rfl⟩ (by norm_num))
theorem R123653 : Reach 123653 := rs (se 4 (by rfl) ⟨11592, by rfl⟩) (B 23185 (by norm_num) ⟨11592, by rfl⟩ (by norm_num))
theorem R90973 : Reach 90973 := rs (se 3 (by rfl) ⟨17057, by rfl⟩) (B 34115 (by norm_num) ⟨17057, by rfl⟩ (by norm_num))
theorem R123781 : Reach 123781 := rs (se 4 (by rfl) ⟨11604, by rfl⟩) (B 23209 (by norm_num) ⟨11604, by rfl⟩ (by norm_num))
theorem R189317 : Reach 189317 := rs (se 4 (by rfl) ⟨17748, by rfl⟩) (B 35497 (by norm_num) ⟨17748, by rfl⟩ (by norm_num))
theorem R123869 : Reach 123869 := rs (se 3 (by rfl) ⟨23225, by rfl⟩) (B 46451 (by norm_num) ⟨23225, by rfl⟩ (by norm_num))
theorem R91145 : Reach 91145 := rs (se 2 (by rfl) ⟨34179, by rfl⟩) (B 68359 (by norm_num) ⟨34179, by rfl⟩ (by norm_num))
theorem R91201 : Reach 91201 := rs (se 2 (by rfl) ⟨34200, by rfl⟩) (B 68401 (by norm_num) ⟨34200, by rfl⟩ (by norm_num))
theorem R123997 : Reach 123997 := rs (se 3 (by rfl) ⟨23249, by rfl⟩) (B 46499 (by norm_num) ⟨23249, by rfl⟩ (by norm_num))
theorem R91297 : Reach 91297 := rs (se 2 (by rfl) ⟨34236, by rfl⟩) (B 68473 (by norm_num) ⟨34236, by rfl⟩ (by norm_num))
theorem R124085 : Reach 124085 := rs (se 5 (by rfl) ⟨5816, by rfl⟩) (B 11633 (by norm_num) ⟨5816, by rfl⟩ (by norm_num))
theorem R189661 : Reach 189661 := rs (se 3 (by rfl) ⟨35561, by rfl⟩) (B 71123 (by norm_num) ⟨35561, by rfl⟩ (by norm_num))
theorem R681205 : Reach 681205 := rs (se 5 (by rfl) ⟨31931, by rfl⟩) (B 63863 (by norm_num) ⟨31931, by rfl⟩ (by norm_num))
theorem R124213 : Reach 124213 := rs (se 5 (by rfl) ⟨5822, by rfl⟩) (B 11645 (by norm_num) ⟨5822, by rfl⟩ (by norm_num))
theorem R91469 : Reach 91469 := rs (se 3 (by rfl) ⟨17150, by rfl⟩) (B 34301 (by norm_num) ⟨17150, by rfl⟩ (by norm_num))
theorem R91525 : Reach 91525 := rs (se 4 (by rfl) ⟨8580, by rfl⟩) (B 17161 (by norm_num) ⟨8580, by rfl⟩ (by norm_num))
theorem R124301 : Reach 124301 := rs (se 3 (by rfl) ⟨23306, by rfl⟩) (B 46613 (by norm_num) ⟨23306, by rfl⟩ (by norm_num))
theorem R681365 : Reach 681365 := rs (se 6 (by rfl) ⟨15969, by rfl⟩) (B 31939 (by norm_num) ⟨15969, by rfl⟩ (by norm_num))
theorem R91621 : Reach 91621 := rs (se 4 (by rfl) ⟨8589, by rfl⟩) (B 17179 (by norm_num) ⟨8589, by rfl⟩ (by norm_num))
theorem R157157 : Reach 157157 := rs (se 4 (by rfl) ⟨14733, by rfl⟩) (B 29467 (by norm_num) ⟨14733, by rfl⟩ (by norm_num))
theorem R124429 : Reach 124429 := rs (se 3 (by rfl) ⟨23330, by rfl⟩) (B 46661 (by norm_num) ⟨23330, by rfl⟩ (by norm_num))
theorem R157277 : Reach 157277 := rs (se 3 (by rfl) ⟨29489, by rfl⟩) (B 58979 (by norm_num) ⟨29489, by rfl⟩ (by norm_num))
theorem R124517 : Reach 124517 := rs (se 4 (by rfl) ⟨11673, by rfl⟩) (B 23347 (by norm_num) ⟨11673, by rfl⟩ (by norm_num))
theorem R91793 : Reach 91793 := rs (se 2 (by rfl) ⟨34422, by rfl⟩) (B 68845 (by norm_num) ⟨34422, by rfl⟩ (by norm_num))
theorem R91849 : Reach 91849 := rs (se 2 (by rfl) ⟨34443, by rfl⟩) (B 68887 (by norm_num) ⟨34443, by rfl⟩ (by norm_num))
theorem R124645 : Reach 124645 := rs (se 4 (by rfl) ⟨11685, by rfl⟩) (B 23371 (by norm_num) ⟨11685, by rfl⟩ (by norm_num))
theorem R91945 : Reach 91945 := rs (se 2 (by rfl) ⟨34479, by rfl⟩) (B 68959 (by norm_num) ⟨34479, by rfl⟩ (by norm_num))
theorem R124733 : Reach 124733 := rs (se 3 (by rfl) ⟨23387, by rfl⟩) (B 46775 (by norm_num) ⟨23387, by rfl⟩ (by norm_num))
theorem R92021 : Reach 92021 := rs (se 5 (by rfl) ⟨4313, by rfl⟩) (B 8627 (by norm_num) ⟨4313, by rfl⟩ (by norm_num))
theorem R124861 : Reach 124861 := rs (se 3 (by rfl) ⟨23411, by rfl⟩) (B 46823 (by norm_num) ⟨23411, by rfl⟩ (by norm_num))
theorem R92117 : Reach 92117 := rs (se 7 (by rfl) ⟨1079, by rfl⟩) (B 2159 (by norm_num) ⟨1079, by rfl⟩ (by norm_num))
theorem R92173 : Reach 92173 := rs (se 3 (by rfl) ⟨17282, by rfl⟩) (B 34565 (by norm_num) ⟨17282, by rfl⟩ (by norm_num))
theorem R124949 : Reach 124949 := rs (se 6 (by rfl) ⟨2928, by rfl⟩) (B 5857 (by norm_num) ⟨2928, by rfl⟩ (by norm_num))
theorem R92269 : Reach 92269 := rs (se 3 (by rfl) ⟨17300, by rfl⟩) (B 34601 (by norm_num) ⟨17300, by rfl⟩ (by norm_num))
theorem R256117 : Reach 256117 := rs (se 5 (by rfl) ⟨12005, by rfl⟩) (B 24011 (by norm_num) ⟨12005, by rfl⟩ (by norm_num))
theorem R125069 : Reach 125069 := rs (se 3 (by rfl) ⟨23450, by rfl⟩) (B 46901 (by norm_num) ⟨23450, by rfl⟩ (by norm_num))
theorem R125077 : Reach 125077 := rs (se 6 (by rfl) ⟨2931, by rfl⟩) (B 5863 (by norm_num) ⟨2931, by rfl⟩ (by norm_num))
theorem R583861 : Reach 583861 := rs (se 5 (by rfl) ⟨27368, by rfl⟩) (B 54737 (by norm_num) ⟨27368, by rfl⟩ (by norm_num))
theorem R157909 : Reach 157909 := rs (se 7 (by rfl) ⟨1850, by rfl⟩) (B 3701 (by norm_num) ⟨1850, by rfl⟩ (by norm_num))
theorem R125165 : Reach 125165 := rs (se 3 (by rfl) ⟨23468, by rfl⟩) (B 46937 (by norm_num) ⟨23468, by rfl⟩ (by norm_num))
theorem R92441 : Reach 92441 := rs (se 2 (by rfl) ⟨34665, by rfl⟩) (B 69331 (by norm_num) ⟨34665, by rfl⟩ (by norm_num))
theorem R92497 : Reach 92497 := rs (se 2 (by rfl) ⟨34686, by rfl⟩) (B 69373 (by norm_num) ⟨34686, by rfl⟩ (by norm_num))
theorem R125293 : Reach 125293 := rs (se 3 (by rfl) ⟨23492, by rfl⟩) (B 46985 (by norm_num) ⟨23492, by rfl⟩ (by norm_num))
theorem R92533 : Reach 92533 := rs (se 5 (by rfl) ⟨4337, by rfl⟩) (B 8675 (by norm_num) ⟨4337, by rfl⟩ (by norm_num))
theorem R92593 : Reach 92593 := rs (se 2 (by rfl) ⟨34722, by rfl⟩) (B 69445 (by norm_num) ⟨34722, by rfl⟩ (by norm_num))
theorem R387509 : Reach 387509 := rs (se 5 (by rfl) ⟨18164, by rfl⟩) (B 36329 (by norm_num) ⟨18164, by rfl⟩ (by norm_num))
theorem R125381 : Reach 125381 := rs (se 4 (by rfl) ⟨11754, by rfl⟩) (B 23509 (by norm_num) ⟨11754, by rfl⟩ (by norm_num))
theorem R125509 : Reach 125509 := rs (se 4 (by rfl) ⟨11766, by rfl⟩) (B 23533 (by norm_num) ⟨11766, by rfl⟩ (by norm_num))
theorem R92765 : Reach 92765 := rs (se 3 (by rfl) ⟨17393, by rfl⟩) (B 34787 (by norm_num) ⟨17393, by rfl⟩ (by norm_num))
theorem R92821 : Reach 92821 := rs (se 6 (by rfl) ⟨2175, by rfl⟩) (B 4351 (by norm_num) ⟨2175, by rfl⟩ (by norm_num))
theorem R125597 : Reach 125597 := rs (se 3 (by rfl) ⟨23549, by rfl⟩) (B 47099 (by norm_num) ⟨23549, by rfl⟩ (by norm_num))
theorem R92917 : Reach 92917 := rs (se 5 (by rfl) ⟨4355, by rfl⟩) (B 8711 (by norm_num) ⟨4355, by rfl⟩ (by norm_num))
theorem R125725 : Reach 125725 := rs (se 3 (by rfl) ⟨23573, by rfl⟩) (B 47147 (by norm_num) ⟨23573, by rfl⟩ (by norm_num))
theorem R125813 : Reach 125813 := rs (se 5 (by rfl) ⟨5897, by rfl⟩) (B 11795 (by norm_num) ⟨5897, by rfl⟩ (by norm_num))
theorem R93089 : Reach 93089 := rs (se 2 (by rfl) ⟨34908, by rfl⟩) (B 69817 (by norm_num) ⟨34908, by rfl⟩ (by norm_num))
theorem R93145 : Reach 93145 := rs (se 2 (by rfl) ⟨34929, by rfl⟩) (B 69859 (by norm_num) ⟨34929, by rfl⟩ (by norm_num))
theorem R125941 : Reach 125941 := rs (se 5 (by rfl) ⟨5903, by rfl⟩) (B 11807 (by norm_num) ⟨5903, by rfl⟩ (by norm_num))
theorem R93241 : Reach 93241 := rs (se 2 (by rfl) ⟨34965, by rfl⟩) (B 69931 (by norm_num) ⟨34965, by rfl⟩ (by norm_num))
theorem R93253 : Reach 93253 := rs (se 4 (by rfl) ⟨8742, by rfl⟩) (B 17485 (by norm_num) ⟨8742, by rfl⟩ (by norm_num))
theorem R158797 : Reach 158797 := rs (se 3 (by rfl) ⟨29774, by rfl⟩) (B 59549 (by norm_num) ⟨29774, by rfl⟩ (by norm_num))
theorem R126029 : Reach 126029 := rs (se 3 (by rfl) ⟨23630, by rfl⟩) (B 47261 (by norm_num) ⟨23630, by rfl⟩ (by norm_num))
theorem R93317 : Reach 93317 := rs (se 4 (by rfl) ⟨8748, by rfl⟩) (B 17497 (by norm_num) ⟨8748, by rfl⟩ (by norm_num))
theorem R158917 : Reach 158917 := rs (se 4 (by rfl) ⟨14898, by rfl⟩) (B 29797 (by norm_num) ⟨14898, by rfl⟩ (by norm_num))
theorem R126157 : Reach 126157 := rs (se 3 (by rfl) ⟨23654, by rfl⟩) (B 47309 (by norm_num) ⟨23654, by rfl⟩ (by norm_num))
theorem R93413 : Reach 93413 := rs (se 4 (by rfl) ⟨8757, by rfl⟩) (B 17515 (by norm_num) ⟨8757, by rfl⟩ (by norm_num))
theorem R93469 : Reach 93469 := rs (se 3 (by rfl) ⟨17525, by rfl⟩) (B 35051 (by norm_num) ⟨17525, by rfl⟩ (by norm_num))
theorem R126245 : Reach 126245 := rs (se 4 (by rfl) ⟨11835, by rfl⟩) (B 23671 (by norm_num) ⟨11835, by rfl⟩ (by norm_num))
theorem R93485 : Reach 93485 := rs (se 3 (by rfl) ⟨17528, by rfl⟩) (B 35057 (by norm_num) ⟨17528, by rfl⟩ (by norm_num))
theorem R93565 : Reach 93565 := rs (se 3 (by rfl) ⟨17543, by rfl⟩) (B 35087 (by norm_num) ⟨17543, by rfl⟩ (by norm_num))
theorem R126373 : Reach 126373 := rs (se 4 (by rfl) ⟨11847, by rfl⟩) (B 23695 (by norm_num) ⟨11847, by rfl⟩ (by norm_num))
theorem R159173 : Reach 159173 := rs (se 4 (by rfl) ⟨14922, by rfl⟩) (B 29845 (by norm_num) ⟨14922, by rfl⟩ (by norm_num))
theorem R126461 : Reach 126461 := rs (se 3 (by rfl) ⟨23711, by rfl⟩) (B 47423 (by norm_num) ⟨23711, by rfl⟩ (by norm_num))
theorem R93737 : Reach 93737 := rs (se 2 (by rfl) ⟨35151, by rfl⟩) (B 70303 (by norm_num) ⟨35151, by rfl⟩ (by norm_num))
theorem R93793 : Reach 93793 := rs (se 2 (by rfl) ⟨35172, by rfl⟩) (B 70345 (by norm_num) ⟨35172, by rfl⟩ (by norm_num))
theorem R618101 : Reach 618101 := rs (se 5 (by rfl) ⟨28973, by rfl⟩) (B 57947 (by norm_num) ⟨28973, by rfl⟩ (by norm_num))
theorem R126589 : Reach 126589 := rs (se 3 (by rfl) ⟨23735, by rfl⟩) (B 47471 (by norm_num) ⟨23735, by rfl⟩ (by norm_num))
theorem R93889 : Reach 93889 := rs (se 2 (by rfl) ⟨35208, by rfl⟩) (B 70417 (by norm_num) ⟨35208, by rfl⟩ (by norm_num))
theorem R126677 : Reach 126677 := rs (se 7 (by rfl) ⟨1484, by rfl⟩) (B 2969 (by norm_num) ⟨1484, by rfl⟩ (by norm_num))
theorem R126821 : Reach 126821 := rs (se 4 (by rfl) ⟨11889, by rfl⟩) (B 23779 (by norm_num) ⟨11889, by rfl⟩ (by norm_num))
theorem R94061 : Reach 94061 := rs (se 3 (by rfl) ⟨17636, by rfl⟩) (B 35273 (by norm_num) ⟨17636, by rfl⟩ (by norm_num))
theorem R94117 : Reach 94117 := rs (se 4 (by rfl) ⟨8823, by rfl⟩) (B 17647 (by norm_num) ⟨8823, by rfl⟩ (by norm_num))
theorem R94213 : Reach 94213 := rs (se 4 (by rfl) ⟨8832, by rfl⟩) (B 17665 (by norm_num) ⟨8832, by rfl⟩ (by norm_num))
theorem R94385 : Reach 94385 := rs (se 2 (by rfl) ⟨35394, by rfl⟩) (B 70789 (by norm_num) ⟨35394, by rfl⟩ (by norm_num))
theorem R192725 : Reach 192725 := rs (se 7 (by rfl) ⟨2258, by rfl⟩) (B 4517 (by norm_num) ⟨2258, by rfl⟩ (by norm_num))
theorem R94441 : Reach 94441 := rs (se 2 (by rfl) ⟨35415, by rfl⟩) (B 70831 (by norm_num) ⟨35415, by rfl⟩ (by norm_num))
theorem R160037 : Reach 160037 := rs (se 4 (by rfl) ⟨15003, by rfl⟩) (B 30007 (by norm_num) ⟨15003, by rfl⟩ (by norm_num))
theorem R160061 : Reach 160061 := rs (se 3 (by rfl) ⟨30011, by rfl⟩) (B 60023 (by norm_num) ⟨30011, by rfl⟩ (by norm_num))
theorem R94537 : Reach 94537 := rs (se 2 (by rfl) ⟨35451, by rfl⟩) (B 70903 (by norm_num) ⟨35451, by rfl⟩ (by norm_num))
theorem R160109 : Reach 160109 := rs (se 3 (by rfl) ⟨30020, by rfl⟩) (B 60041 (by norm_num) ⟨30020, by rfl⟩ (by norm_num))
theorem R160181 : Reach 160181 := rs (se 5 (by rfl) ⟨7508, by rfl⟩) (B 15017 (by norm_num) ⟨7508, by rfl⟩ (by norm_num))
theorem R94709 : Reach 94709 := rs (se 5 (by rfl) ⟨4439, by rfl⟩) (B 8879 (by norm_num) ⟨4439, by rfl⟩ (by norm_num))
theorem R160253 : Reach 160253 := rs (se 3 (by rfl) ⟨30047, by rfl⟩) (B 60095 (by norm_num) ⟨30047, by rfl⟩ (by norm_num))
theorem R94765 : Reach 94765 := rs (se 3 (by rfl) ⟨17768, by rfl⟩) (B 35537 (by norm_num) ⟨17768, by rfl⟩ (by norm_num))
theorem R160301 : Reach 160301 := rs (se 3 (by rfl) ⟨30056, by rfl⟩) (B 60113 (by norm_num) ⟨30056, by rfl⟩ (by norm_num))
theorem R160325 : Reach 160325 := rs (se 4 (by rfl) ⟨15030, by rfl⟩) (B 30061 (by norm_num) ⟨15030, by rfl⟩ (by norm_num))
theorem R160397 : Reach 160397 := rs (se 3 (by rfl) ⟨30074, by rfl⟩) (B 60149 (by norm_num) ⟨30074, by rfl⟩ (by norm_num))
theorem R94861 : Reach 94861 := rs (se 3 (by rfl) ⟨17786, by rfl⟩) (B 35573 (by norm_num) ⟨17786, by rfl⟩ (by norm_num))
theorem R160469 : Reach 160469 := rs (se 7 (by rfl) ⟨1880, by rfl⟩) (B 3761 (by norm_num) ⟨1880, by rfl⟩ (by norm_num))
theorem R160541 : Reach 160541 := rs (se 3 (by rfl) ⟨30101, by rfl⟩) (B 60203 (by norm_num) ⟨30101, by rfl⟩ (by norm_num))
theorem R160613 : Reach 160613 := rs (se 4 (by rfl) ⟨15057, by rfl⟩) (B 30115 (by norm_num) ⟨15057, by rfl⟩ (by norm_num))
theorem R160685 : Reach 160685 := rs (se 3 (by rfl) ⟨30128, by rfl⟩) (B 60257 (by norm_num) ⟨30128, by rfl⟩ (by norm_num))
theorem R160757 : Reach 160757 := rs (se 5 (by rfl) ⟨7535, by rfl⟩) (B 15071 (by norm_num) ⟨7535, by rfl⟩ (by norm_num))
theorem R160829 : Reach 160829 := rs (se 3 (by rfl) ⟨30155, by rfl⟩) (B 60311 (by norm_num) ⟨30155, by rfl⟩ (by norm_num))
theorem R160901 : Reach 160901 := rs (se 4 (by rfl) ⟨15084, by rfl⟩) (B 30169 (by norm_num) ⟨15084, by rfl⟩ (by norm_num))
theorem R259205 : Reach 259205 := rs (se 4 (by rfl) ⟨24300, by rfl⟩) (B 48601 (by norm_num) ⟨24300, by rfl⟩ (by norm_num))
theorem R160973 : Reach 160973 := rs (se 3 (by rfl) ⟨30182, by rfl⟩) (B 60365 (by norm_num) ⟨30182, by rfl⟩ (by norm_num))
theorem R161045 : Reach 161045 := rs (se 6 (by rfl) ⟨3774, by rfl⟩) (B 7549 (by norm_num) ⟨3774, by rfl⟩ (by norm_num))
theorem R161117 : Reach 161117 := rs (se 3 (by rfl) ⟨30209, by rfl⟩) (B 60419 (by norm_num) ⟨30209, by rfl⟩ (by norm_num))
theorem R161189 : Reach 161189 := rs (se 4 (by rfl) ⟨15111, by rfl⟩) (B 30223 (by norm_num) ⟨15111, by rfl⟩ (by norm_num))
theorem R194005 : Reach 194005 := rs (se 7 (by rfl) ⟨2273, by rfl⟩) (B 4547 (by norm_num) ⟨2273, by rfl⟩ (by norm_num))
theorem R161261 : Reach 161261 := rs (se 3 (by rfl) ⟨30236, by rfl⟩) (B 60473 (by norm_num) ⟨30236, by rfl⟩ (by norm_num))
theorem R423413 : Reach 423413 := rs (se 5 (by rfl) ⟨19847, by rfl⟩) (B 39695 (by norm_num) ⟨19847, by rfl⟩ (by norm_num))
theorem R161333 : Reach 161333 := rs (se 5 (by rfl) ⟨7562, by rfl⟩) (B 15125 (by norm_num) ⟨7562, by rfl⟩ (by norm_num))
theorem R1799765 : Reach 1799765 := rs (se 8 (by rfl) ⟨10545, by rfl⟩) (B 21091 (by norm_num) ⟨10545, by rfl⟩ (by norm_num))
theorem R161405 : Reach 161405 := rs (se 3 (by rfl) ⟨30263, by rfl⟩) (B 60527 (by norm_num) ⟨30263, by rfl⟩ (by norm_num))
theorem R947861 : Reach 947861 := rs (se 6 (by rfl) ⟨22215, by rfl⟩) (B 44431 (by norm_num) ⟨22215, by rfl⟩ (by norm_num))
theorem R161477 : Reach 161477 := rs (se 4 (by rfl) ⟨15138, by rfl⟩) (B 30277 (by norm_num) ⟨15138, by rfl⟩ (by norm_num))
theorem R95941 : Reach 95941 := rs (se 4 (by rfl) ⟨8994, by rfl⟩) (B 17989 (by norm_num) ⟨8994, by rfl⟩ (by norm_num))
theorem R161549 : Reach 161549 := rs (se 3 (by rfl) ⟨30290, by rfl⟩) (B 60581 (by norm_num) ⟨30290, by rfl⟩ (by norm_num))
theorem R161621 : Reach 161621 := rs (se 9 (by rfl) ⟨473, by rfl⟩) (B 947 (by norm_num) ⟨473, by rfl⟩ (by norm_num))
theorem R522101 : Reach 522101 := rs (se 5 (by rfl) ⟨24473, by rfl⟩) (B 48947 (by norm_num) ⟨24473, by rfl⟩ (by norm_num))
theorem R161693 : Reach 161693 := rs (se 3 (by rfl) ⟨30317, by rfl⟩) (B 60635 (by norm_num) ⟨30317, by rfl⟩ (by norm_num))
theorem R161765 : Reach 161765 := rs (se 4 (by rfl) ⟨15165, by rfl⟩) (B 30331 (by norm_num) ⟨15165, by rfl⟩ (by norm_num))
theorem R391189 : Reach 391189 := rs (se 6 (by rfl) ⟨9168, by rfl⟩) (B 18337 (by norm_num) ⟨9168, by rfl⟩ (by norm_num))
theorem R161837 : Reach 161837 := rs (se 3 (by rfl) ⟨30344, by rfl⟩) (B 60689 (by norm_num) ⟨30344, by rfl⟩ (by norm_num))
theorem R161909 : Reach 161909 := rs (se 5 (by rfl) ⟨7589, by rfl⟩) (B 15179 (by norm_num) ⟨7589, by rfl⟩ (by norm_num))
theorem R161981 : Reach 161981 := rs (se 3 (by rfl) ⟨30371, by rfl⟩) (B 60743 (by norm_num) ⟨30371, by rfl⟩ (by norm_num))
theorem R162053 : Reach 162053 := rs (se 4 (by rfl) ⟨15192, by rfl⟩) (B 30385 (by norm_num) ⟨15192, by rfl⟩ (by norm_num))
theorem R162125 : Reach 162125 := rs (se 3 (by rfl) ⟨30398, by rfl⟩) (B 60797 (by norm_num) ⟨30398, by rfl⟩ (by norm_num))
theorem R1603925 : Reach 1603925 := rs (se 10 (by rfl) ⟨2349, by rfl⟩) (B 4699 (by norm_num) ⟨2349, by rfl⟩ (by norm_num))
theorem R162197 : Reach 162197 := rs (se 6 (by rfl) ⟨3801, by rfl⟩) (B 7603 (by norm_num) ⟨3801, by rfl⟩ (by norm_num))
theorem R162269 : Reach 162269 := rs (se 3 (by rfl) ⟨30425, by rfl⟩) (B 60851 (by norm_num) ⟨30425, by rfl⟩ (by norm_num))
theorem R162341 : Reach 162341 := rs (se 4 (by rfl) ⟨15219, by rfl⟩) (B 30439 (by norm_num) ⟨15219, by rfl⟩ (by norm_num))
theorem R227893 : Reach 227893 := rs (se 5 (by rfl) ⟨10682, by rfl⟩) (B 21365 (by norm_num) ⟨10682, by rfl⟩ (by norm_num))
theorem R162413 : Reach 162413 := rs (se 3 (by rfl) ⟨30452, by rfl⟩) (B 60905 (by norm_num) ⟨30452, by rfl⟩ (by norm_num))
theorem R162485 : Reach 162485 := rs (se 5 (by rfl) ⟨7616, by rfl⟩) (B 15233 (by norm_num) ⟨7616, by rfl⟩ (by norm_num))
theorem R162557 : Reach 162557 := rs (se 3 (by rfl) ⟨30479, by rfl⟩) (B 60959 (by norm_num) ⟨30479, by rfl⟩ (by norm_num))
theorem R162605 : Reach 162605 := rs (se 3 (by rfl) ⟨30488, by rfl⟩) (B 60977 (by norm_num) ⟨30488, by rfl⟩ (by norm_num))
theorem R162629 : Reach 162629 := rs (se 4 (by rfl) ⟨15246, by rfl⟩) (B 30493 (by norm_num) ⟨15246, by rfl⟩ (by norm_num))
theorem R228181 : Reach 228181 := rs (se 9 (by rfl) ⟨668, by rfl⟩) (B 1337 (by norm_num) ⟨668, by rfl⟩ (by norm_num))
theorem R162701 : Reach 162701 := rs (se 3 (by rfl) ⟨30506, by rfl⟩) (B 61013 (by norm_num) ⟨30506, by rfl⟩ (by norm_num))
theorem R162773 : Reach 162773 := rs (se 7 (by rfl) ⟨1907, by rfl⟩) (B 3815 (by norm_num) ⟨1907, by rfl⟩ (by norm_num))
theorem R162845 : Reach 162845 := rs (se 3 (by rfl) ⟨30533, by rfl⟩) (B 61067 (by norm_num) ⟨30533, by rfl⟩ (by norm_num))
theorem R162917 : Reach 162917 := rs (se 4 (by rfl) ⟨15273, by rfl⟩) (B 30547 (by norm_num) ⟨15273, by rfl⟩ (by norm_num))
theorem R162989 : Reach 162989 := rs (se 3 (by rfl) ⟨30560, by rfl⟩) (B 61121 (by norm_num) ⟨30560, by rfl⟩ (by norm_num))
theorem R163061 : Reach 163061 := rs (se 5 (by rfl) ⟨7643, by rfl⟩) (B 15287 (by norm_num) ⟨7643, by rfl⟩ (by norm_num))
theorem R163133 : Reach 163133 := rs (se 3 (by rfl) ⟨30587, by rfl⟩) (B 61175 (by norm_num) ⟨30587, by rfl⟩ (by norm_num))
theorem R163205 : Reach 163205 := rs (se 4 (by rfl) ⟨15300, by rfl⟩) (B 30601 (by norm_num) ⟨15300, by rfl⟩ (by norm_num))
theorem R556469 : Reach 556469 := rs (se 5 (by rfl) ⟨26084, by rfl⟩) (B 52169 (by norm_num) ⟨26084, by rfl⟩ (by norm_num))
theorem R163277 : Reach 163277 := rs (se 3 (by rfl) ⟨30614, by rfl⟩) (B 61229 (by norm_num) ⟨30614, by rfl⟩ (by norm_num))
theorem R97781 : Reach 97781 := rs (se 5 (by rfl) ⟨4583, by rfl⟩) (B 9167 (by norm_num) ⟨4583, by rfl⟩ (by norm_num))
theorem R163349 : Reach 163349 := rs (se 6 (by rfl) ⟨3828, by rfl⟩) (B 7657 (by norm_num) ⟨3828, by rfl⟩ (by norm_num))
theorem R163421 : Reach 163421 := rs (se 3 (by rfl) ⟨30641, by rfl⟩) (B 61283 (by norm_num) ⟨30641, by rfl⟩ (by norm_num))
theorem R163493 : Reach 163493 := rs (se 4 (by rfl) ⟨15327, by rfl⟩) (B 30655 (by norm_num) ⟨15327, by rfl⟩ (by norm_num))
theorem R163565 : Reach 163565 := rs (se 3 (by rfl) ⟨30668, by rfl⟩) (B 61337 (by norm_num) ⟨30668, by rfl⟩ (by norm_num))
theorem R163637 : Reach 163637 := rs (se 5 (by rfl) ⟨7670, by rfl⟩) (B 15341 (by norm_num) ⟨7670, by rfl⟩ (by norm_num))
theorem R163709 : Reach 163709 := rs (se 3 (by rfl) ⟨30695, by rfl⟩) (B 61391 (by norm_num) ⟨30695, by rfl⟩ (by norm_num))
theorem R163781 : Reach 163781 := rs (se 4 (by rfl) ⟨15354, by rfl⟩) (B 30709 (by norm_num) ⟨15354, by rfl⟩ (by norm_num))
theorem R262133 : Reach 262133 := rs (se 5 (by rfl) ⟨12287, by rfl⟩) (B 24575 (by norm_num) ⟨12287, by rfl⟩ (by norm_num))
theorem R163889 : Reach 163889 := rs (se 2 (by rfl) ⟨61458, by rfl⟩) R122917
theorem R163907 : Reach 163907 := rs (se 1 (by rfl) ⟨122930, by rfl⟩) R245861
theorem R131203 : Reach 131203 := rs (se 1 (by rfl) ⟨98402, by rfl⟩) R196805
theorem R360611 : Reach 360611 := rs (se 1 (by rfl) ⟨270458, by rfl⟩) R540917
theorem R262435 : Reach 262435 := rs (se 1 (by rfl) ⟨196826, by rfl⟩) R393653
theorem R164177 : Reach 164177 := rs (se 2 (by rfl) ⟨61566, by rfl⟩) R123133
theorem R164195 : Reach 164195 := rs (se 1 (by rfl) ⟨123146, by rfl⟩) R246293
theorem R229841 : Reach 229841 := rs (se 2 (by rfl) ⟨86190, by rfl⟩) R172381
theorem R787013 : Reach 787013 := rs (se 4 (by rfl) ⟨73782, by rfl⟩) R147565
theorem R229969 : Reach 229969 := rs (se 2 (by rfl) ⟨86238, by rfl⟩) R172477
theorem R164465 : Reach 164465 := rs (se 2 (by rfl) ⟨61674, by rfl⟩) R123349
theorem R164483 : Reach 164483 := rs (se 1 (by rfl) ⟨123362, by rfl⟩) R246725
theorem R426829 : Reach 426829 := rs (se 3 (by rfl) ⟨80030, by rfl⟩) R160061
theorem R164753 : Reach 164753 := rs (se 2 (by rfl) ⟨61782, by rfl⟩) R123565
theorem R164771 : Reach 164771 := rs (se 1 (by rfl) ⟨123578, by rfl⟩) R247157
theorem R361421 : Reach 361421 := rs (se 3 (by rfl) ⟨67766, by rfl⟩) R135533
theorem R1868771 : Reach 1868771 := rs (se 1 (by rfl) ⟨1401578, by rfl⟩) R2803157
theorem R99425 : Reach 99425 := rs (se 2 (by rfl) ⟨37284, by rfl⟩) R74569
theorem R165041 : Reach 165041 := rs (se 2 (by rfl) ⟨61890, by rfl⟩) R123781
theorem R165059 : Reach 165059 := rs (se 1 (by rfl) ⟨123794, by rfl⟩) R247589
theorem R165329 : Reach 165329 := rs (se 2 (by rfl) ⟨61998, by rfl⟩) R123997
theorem R165347 : Reach 165347 := rs (se 1 (by rfl) ⟨124010, by rfl⟩) R248021
theorem R230957 : Reach 230957 := rs (se 3 (by rfl) ⟨43304, by rfl⟩) R86609
theorem R132803 : Reach 132803 := rs (se 1 (by rfl) ⟨99602, by rfl⟩) R199205
theorem R394993 : Reach 394993 := rs (se 2 (by rfl) ⟨148122, by rfl⟩) R296245
theorem R165617 : Reach 165617 := rs (se 2 (by rfl) ⟨62106, by rfl⟩) R124213
theorem R165635 : Reach 165635 := rs (se 1 (by rfl) ⟨124226, by rfl⟩) R248453
theorem R132977 : Reach 132977 := rs (se 2 (by rfl) ⟨49866, by rfl⟩) R99733
theorem R165905 : Reach 165905 := rs (se 2 (by rfl) ⟨62214, by rfl⟩) R124429
theorem R165923 : Reach 165923 := rs (se 1 (by rfl) ⟨124442, by rfl⟩) R248885
theorem R133265 : Reach 133265 := rs (se 2 (by rfl) ⟨49974, by rfl⟩) R99949
theorem R166193 : Reach 166193 := rs (se 2 (by rfl) ⟨62322, by rfl⟩) R124645
theorem R166211 : Reach 166211 := rs (se 1 (by rfl) ⟨124658, by rfl⟩) R249317
theorem R297379 : Reach 297379 := rs (se 1 (by rfl) ⟨223034, by rfl⟩) R446069
theorem R166481 : Reach 166481 := rs (se 2 (by rfl) ⟨62430, by rfl⟩) R124861
theorem R166499 : Reach 166499 := rs (se 1 (by rfl) ⟨124874, by rfl⟩) R249749
theorem R101155 : Reach 101155 := rs (se 1 (by rfl) ⟨75866, by rfl⟩) R151733
theorem R232301 : Reach 232301 := rs (se 3 (by rfl) ⟨43556, by rfl⟩) R87113
theorem R166769 : Reach 166769 := rs (se 2 (by rfl) ⟨62538, by rfl⟩) R125077
theorem R166787 : Reach 166787 := rs (se 1 (by rfl) ⟨125090, by rfl⟩) R250181
theorem R101297 : Reach 101297 := rs (se 2 (by rfl) ⟨37986, by rfl⟩) R75973
theorem R134065 : Reach 134065 := rs (se 2 (by rfl) ⟨50274, by rfl⟩) R100549
theorem R691213 : Reach 691213 := rs (se 3 (by rfl) ⟨129602, by rfl⟩) R259205
theorem R167057 : Reach 167057 := rs (se 2 (by rfl) ⟨62646, by rfl⟩) R125293
theorem R167075 : Reach 167075 := rs (se 1 (by rfl) ⟨125306, by rfl⟩) R250613
theorem R167345 : Reach 167345 := rs (se 2 (by rfl) ⟨62754, by rfl⟩) R125509
theorem R101827 : Reach 101827 := rs (se 1 (by rfl) ⟨76370, by rfl⟩) R152741
theorem R167363 : Reach 167363 := rs (se 1 (by rfl) ⟨125522, by rfl⟩) R251045
theorem R1215971 : Reach 1215971 := rs (se 1 (by rfl) ⟨911978, by rfl⟩) R1823957
theorem R462449 : Reach 462449 := rs (se 2 (by rfl) ⟨173418, by rfl⟩) R346837
theorem R167633 : Reach 167633 := rs (se 2 (by rfl) ⟨62862, by rfl⟩) R125725
theorem R167651 : Reach 167651 := rs (se 1 (by rfl) ⟨125738, by rfl⟩) R251477
theorem R102163 : Reach 102163 := rs (se 1 (by rfl) ⟨76622, by rfl⟩) R153245
theorem R364337 : Reach 364337 := rs (se 2 (by rfl) ⟨136626, by rfl⟩) R273253
theorem R167921 : Reach 167921 := rs (se 2 (by rfl) ⟨62970, by rfl⟩) R125941
theorem R167939 : Reach 167939 := rs (se 1 (by rfl) ⟨125954, by rfl⟩) R251909
theorem R135427 : Reach 135427 := rs (se 1 (by rfl) ⟨101570, by rfl⟩) R203141
theorem R168209 : Reach 168209 := rs (se 2 (by rfl) ⟨63078, by rfl⟩) R126157
theorem R168227 : Reach 168227 := rs (se 1 (by rfl) ⟨126170, by rfl⟩) R252341
theorem R1544501 : Reach 1544501 := rs (se 5 (by rfl) ⟨72398, by rfl⟩) R144797
theorem R102721 : Reach 102721 := rs (se 2 (by rfl) ⟨38520, by rfl⟩) R77041
theorem R102755 : Reach 102755 := rs (se 1 (by rfl) ⟨77066, by rfl⟩) R154133
theorem R135587 : Reach 135587 := rs (se 1 (by rfl) ⟨101690, by rfl⟩) R203381
theorem R233891 : Reach 233891 := rs (se 1 (by rfl) ⟨175418, by rfl⟩) R350837
theorem R168497 : Reach 168497 := rs (se 2 (by rfl) ⟨63186, by rfl⟩) R126373
theorem R4133429 : Reach 4133429 := rs (se 5 (by rfl) ⟨193754, by rfl⟩) R387509
theorem R168515 : Reach 168515 := rs (se 1 (by rfl) ⟨126386, by rfl⟩) R252773
theorem R168785 : Reach 168785 := rs (se 2 (by rfl) ⟨63294, by rfl⟩) R126589
theorem R168803 : Reach 168803 := rs (se 1 (by rfl) ⟨126602, by rfl⟩) R253205
theorem R103313 : Reach 103313 := rs (se 2 (by rfl) ⟨38742, by rfl⟩) R77485
theorem R103393 : Reach 103393 := rs (se 2 (by rfl) ⟨38772, by rfl⟩) R77545
theorem R234659 : Reach 234659 := rs (se 1 (by rfl) ⟨175994, by rfl⟩) R351989
theorem R365795 : Reach 365795 := rs (se 1 (by rfl) ⟨274346, by rfl⟩) R548693
theorem R136657 : Reach 136657 := rs (se 2 (by rfl) ⟨51246, by rfl⟩) R102493
theorem R71139 : Reach 71139 := rs (se 1 (by rfl) ⟨53354, by rfl⟩) R106709
theorem R71155 : Reach 71155 := rs (se 1 (by rfl) ⟨53366, by rfl⟩) R106733
theorem R71171 : Reach 71171 := rs (se 1 (by rfl) ⟨53378, by rfl⟩) R106757
theorem R71187 : Reach 71187 := rs (se 1 (by rfl) ⟨53390, by rfl⟩) R106781
theorem R71203 : Reach 71203 := rs (se 1 (by rfl) ⟨53402, by rfl⟩) R106805
theorem R235057 : Reach 235057 := rs (se 2 (by rfl) ⟨88146, by rfl⟩) R176293
theorem R71219 : Reach 71219 := rs (se 1 (by rfl) ⟨53414, by rfl⟩) R106829
theorem R71235 : Reach 71235 := rs (se 1 (by rfl) ⟨53426, by rfl⟩) R106853
theorem R71251 : Reach 71251 := rs (se 1 (by rfl) ⟨53438, by rfl⟩) R106877
theorem R71267 : Reach 71267 := rs (se 1 (by rfl) ⟨53450, by rfl⟩) R106901
theorem R562787 : Reach 562787 := rs (se 1 (by rfl) ⟨422090, by rfl⟩) R844181
theorem R71283 : Reach 71283 := rs (se 1 (by rfl) ⟨53462, by rfl⟩) R106925
theorem R71299 : Reach 71299 := rs (se 1 (by rfl) ⟨53474, by rfl⟩) R106949
theorem R71315 : Reach 71315 := rs (se 1 (by rfl) ⟨53486, by rfl⟩) R106973
theorem R71331 : Reach 71331 := rs (se 1 (by rfl) ⟨53498, by rfl⟩) R106997
theorem R235171 : Reach 235171 := rs (se 1 (by rfl) ⟨176378, by rfl⟩) R352757
theorem R71347 : Reach 71347 := rs (se 1 (by rfl) ⟨53510, by rfl⟩) R107021
theorem R71363 : Reach 71363 := rs (se 1 (by rfl) ⟨53522, by rfl⟩) R107045
theorem R71379 : Reach 71379 := rs (se 1 (by rfl) ⟨53534, by rfl⟩) R107069
theorem R71395 : Reach 71395 := rs (se 1 (by rfl) ⟨53546, by rfl⟩) R107093
theorem R71411 : Reach 71411 := rs (se 1 (by rfl) ⟨53558, by rfl⟩) R107117
theorem R104179 : Reach 104179 := rs (se 1 (by rfl) ⟨78134, by rfl⟩) R156269
theorem R71427 : Reach 71427 := rs (se 1 (by rfl) ⟨53570, by rfl⟩) R107141
theorem R71443 : Reach 71443 := rs (se 1 (by rfl) ⟨53582, by rfl⟩) R107165
theorem R71459 : Reach 71459 := rs (se 1 (by rfl) ⟨53594, by rfl⟩) R107189
theorem R71475 : Reach 71475 := rs (se 1 (by rfl) ⟨53606, by rfl⟩) R107213
theorem R71491 : Reach 71491 := rs (se 1 (by rfl) ⟨53618, by rfl⟩) R107237
theorem R71507 : Reach 71507 := rs (se 1 (by rfl) ⟨53630, by rfl⟩) R107261
theorem R71523 : Reach 71523 := rs (se 1 (by rfl) ⟨53642, by rfl⟩) R107285
theorem R71539 : Reach 71539 := rs (se 1 (by rfl) ⟨53654, by rfl⟩) R107309
theorem R71555 : Reach 71555 := rs (se 1 (by rfl) ⟨53666, by rfl⟩) R107333
theorem R71571 : Reach 71571 := rs (se 1 (by rfl) ⟨53678, by rfl⟩) R107357
theorem R71587 : Reach 71587 := rs (se 1 (by rfl) ⟨53690, by rfl⟩) R107381
theorem R71603 : Reach 71603 := rs (se 1 (by rfl) ⟨53702, by rfl⟩) R107405
theorem R71619 : Reach 71619 := rs (se 1 (by rfl) ⟨53714, by rfl⟩) R107429
theorem R71635 : Reach 71635 := rs (se 1 (by rfl) ⟨53726, by rfl⟩) R107453
theorem R71651 : Reach 71651 := rs (se 1 (by rfl) ⟨53738, by rfl⟩) R107477
theorem R71667 : Reach 71667 := rs (se 1 (by rfl) ⟨53750, by rfl⟩) R107501
theorem R71683 : Reach 71683 := rs (se 1 (by rfl) ⟨53762, by rfl⟩) R107525
theorem R366605 : Reach 366605 := rs (se 3 (by rfl) ⟨68738, by rfl⟩) R137477
theorem R71699 : Reach 71699 := rs (se 1 (by rfl) ⟨53774, by rfl⟩) R107549
theorem R71715 : Reach 71715 := rs (se 1 (by rfl) ⟨53786, by rfl⟩) R107573
theorem R71731 : Reach 71731 := rs (se 1 (by rfl) ⟨53798, by rfl⟩) R107597
theorem R71747 : Reach 71747 := rs (se 1 (by rfl) ⟨53810, by rfl⟩) R107621
theorem R71763 : Reach 71763 := rs (se 1 (by rfl) ⟨53822, by rfl⟩) R107645
theorem R71779 : Reach 71779 := rs (se 1 (by rfl) ⟨53834, by rfl⟩) R107669
theorem R71795 : Reach 71795 := rs (se 1 (by rfl) ⟨53846, by rfl⟩) R107693
theorem R71811 : Reach 71811 := rs (se 1 (by rfl) ⟨53858, by rfl⟩) R107717
theorem R71827 : Reach 71827 := rs (se 1 (by rfl) ⟨53870, by rfl⟩) R107741
theorem R104609 : Reach 104609 := rs (se 2 (by rfl) ⟨39228, by rfl⟩) R78457
theorem R71843 : Reach 71843 := rs (se 1 (by rfl) ⟨53882, by rfl⟩) R107765
theorem R202925 : Reach 202925 := rs (se 3 (by rfl) ⟨38048, by rfl⟩) R76097
theorem R71859 : Reach 71859 := rs (se 1 (by rfl) ⟨53894, by rfl⟩) R107789
theorem R71875 : Reach 71875 := rs (se 1 (by rfl) ⟨53906, by rfl⟩) R107813
theorem R104657 : Reach 104657 := rs (se 2 (by rfl) ⟨39246, by rfl⟩) R78493
theorem R71891 : Reach 71891 := rs (se 1 (by rfl) ⟨53918, by rfl⟩) R107837
theorem R71907 : Reach 71907 := rs (se 1 (by rfl) ⟨53930, by rfl⟩) R107861
theorem R399587 : Reach 399587 := rs (se 1 (by rfl) ⟨299690, by rfl⟩) R599381
theorem R71923 : Reach 71923 := rs (se 1 (by rfl) ⟨53942, by rfl⟩) R107885
theorem R71939 : Reach 71939 := rs (se 1 (by rfl) ⟨53954, by rfl⟩) R107909
theorem R71955 : Reach 71955 := rs (se 1 (by rfl) ⟨53966, by rfl⟩) R107933
theorem R71971 : Reach 71971 := rs (se 1 (by rfl) ⟨53978, by rfl⟩) R107957
theorem R71987 : Reach 71987 := rs (se 1 (by rfl) ⟨53990, by rfl⟩) R107981
theorem R72003 : Reach 72003 := rs (se 1 (by rfl) ⟨54002, by rfl⟩) R108005
theorem R104771 : Reach 104771 := rs (se 1 (by rfl) ⟨78578, by rfl⟩) R157157
theorem R72019 : Reach 72019 := rs (se 1 (by rfl) ⟨54014, by rfl⟩) R108029
theorem R203107 : Reach 203107 := rs (se 1 (by rfl) ⟨152330, by rfl⟩) R304661
theorem R72035 : Reach 72035 := rs (se 1 (by rfl) ⟨54026, by rfl⟩) R108053
theorem R235889 : Reach 235889 := rs (se 2 (by rfl) ⟨88458, by rfl⟩) R176917
theorem R72051 : Reach 72051 := rs (se 1 (by rfl) ⟨54038, by rfl⟩) R108077
theorem R72067 : Reach 72067 := rs (se 1 (by rfl) ⟨54050, by rfl⟩) R108101
theorem R72083 : Reach 72083 := rs (se 1 (by rfl) ⟨54062, by rfl⟩) R108125
theorem R104851 : Reach 104851 := rs (se 1 (by rfl) ⟨78638, by rfl⟩) R157277
theorem R72099 : Reach 72099 := rs (se 1 (by rfl) ⟨54074, by rfl⟩) R108149
theorem R72115 : Reach 72115 := rs (se 1 (by rfl) ⟨54086, by rfl⟩) R108173
theorem R268721 : Reach 268721 := rs (se 2 (by rfl) ⟨100770, by rfl⟩) R201541
theorem R72131 : Reach 72131 := rs (se 1 (by rfl) ⟨54098, by rfl⟩) R108197
theorem R72147 : Reach 72147 := rs (se 1 (by rfl) ⟨54110, by rfl⟩) R108221
theorem R72163 : Reach 72163 := rs (se 1 (by rfl) ⟨54122, by rfl⟩) R108245
theorem R137713 : Reach 137713 := rs (se 2 (by rfl) ⟨51642, by rfl⟩) R103285
theorem R72179 : Reach 72179 := rs (se 1 (by rfl) ⟨54134, by rfl⟩) R108269
theorem R72195 : Reach 72195 := rs (se 1 (by rfl) ⟨54146, by rfl⟩) R108293
theorem R465421 : Reach 465421 := rs (se 3 (by rfl) ⟨87266, by rfl⟩) R174533
theorem R72211 : Reach 72211 := rs (se 1 (by rfl) ⟨54158, by rfl⟩) R108317
theorem R72227 : Reach 72227 := rs (se 1 (by rfl) ⟨54170, by rfl⟩) R108341
theorem R72243 : Reach 72243 := rs (se 1 (by rfl) ⟨54182, by rfl⟩) R108365
theorem R72259 : Reach 72259 := rs (se 1 (by rfl) ⟨54194, by rfl⟩) R108389
theorem R72275 : Reach 72275 := rs (se 1 (by rfl) ⟨54206, by rfl⟩) R108413
theorem R72291 : Reach 72291 := rs (se 1 (by rfl) ⟨54218, by rfl⟩) R108437
theorem R72307 : Reach 72307 := rs (se 1 (by rfl) ⟨54230, by rfl⟩) R108461
theorem R72323 : Reach 72323 := rs (se 1 (by rfl) ⟨54242, by rfl⟩) R108485
theorem R72339 : Reach 72339 := rs (se 1 (by rfl) ⟨54254, by rfl⟩) R108509
theorem R72355 : Reach 72355 := rs (se 1 (by rfl) ⟨54266, by rfl⟩) R108533
theorem R72371 : Reach 72371 := rs (se 1 (by rfl) ⟨54278, by rfl⟩) R108557
theorem R72387 : Reach 72387 := rs (se 1 (by rfl) ⟨54290, by rfl⟩) R108581
theorem R72403 : Reach 72403 := rs (se 1 (by rfl) ⟨54302, by rfl⟩) R108605
theorem R72419 : Reach 72419 := rs (se 1 (by rfl) ⟨54314, by rfl⟩) R108629
theorem R72435 : Reach 72435 := rs (se 1 (by rfl) ⟨54326, by rfl⟩) R108653
theorem R72451 : Reach 72451 := rs (se 1 (by rfl) ⟨54338, by rfl⟩) R108677
theorem R72467 : Reach 72467 := rs (se 1 (by rfl) ⟨54350, by rfl⟩) R108701
theorem R72483 : Reach 72483 := rs (se 1 (by rfl) ⟨54362, by rfl⟩) R108725
theorem R72499 : Reach 72499 := rs (se 1 (by rfl) ⟨54374, by rfl⟩) R108749
theorem R72515 : Reach 72515 := rs (se 1 (by rfl) ⟨54386, by rfl⟩) R108773
theorem R203597 : Reach 203597 := rs (se 3 (by rfl) ⟨38174, by rfl⟩) R76349
theorem R72531 : Reach 72531 := rs (se 1 (by rfl) ⟨54398, by rfl⟩) R108797
theorem R72547 : Reach 72547 := rs (se 1 (by rfl) ⟨54410, by rfl⟩) R108821
theorem R498545 : Reach 498545 := rs (se 2 (by rfl) ⟨186954, by rfl⟩) R373909
theorem R72563 : Reach 72563 := rs (se 1 (by rfl) ⟨54422, by rfl⟩) R108845
theorem R72579 : Reach 72579 := rs (se 1 (by rfl) ⟨54434, by rfl⟩) R108869
theorem R138115 : Reach 138115 := rs (se 1 (by rfl) ⟨103586, by rfl⟩) R207173
theorem R236429 : Reach 236429 := rs (se 3 (by rfl) ⟨44330, by rfl⟩) R88661
theorem R72595 : Reach 72595 := rs (se 1 (by rfl) ⟨54446, by rfl⟩) R108893
theorem R72611 : Reach 72611 := rs (se 1 (by rfl) ⟨54458, by rfl⟩) R108917
theorem R138161 : Reach 138161 := rs (se 2 (by rfl) ⟨51810, by rfl⟩) R103621
theorem R72627 : Reach 72627 := rs (se 1 (by rfl) ⟨54470, by rfl⟩) R108941
theorem R105409 : Reach 105409 := rs (se 2 (by rfl) ⟨39528, by rfl⟩) R79057
theorem R72643 : Reach 72643 := rs (se 1 (by rfl) ⟨54482, by rfl⟩) R108965
theorem R72659 : Reach 72659 := rs (se 1 (by rfl) ⟨54494, by rfl⟩) R108989
theorem R72675 : Reach 72675 := rs (se 1 (by rfl) ⟨54506, by rfl⟩) R109013
theorem R72691 : Reach 72691 := rs (se 1 (by rfl) ⟨54518, by rfl⟩) R109037
theorem R72707 : Reach 72707 := rs (se 1 (by rfl) ⟨54530, by rfl⟩) R109061
theorem R72723 : Reach 72723 := rs (se 1 (by rfl) ⟨54542, by rfl⟩) R109085
theorem R72739 : Reach 72739 := rs (se 1 (by rfl) ⟨54554, by rfl⟩) R109109
theorem R72755 : Reach 72755 := rs (se 1 (by rfl) ⟨54566, by rfl⟩) R109133
theorem R72771 : Reach 72771 := rs (se 1 (by rfl) ⟨54578, by rfl⟩) R109157
theorem R72787 : Reach 72787 := rs (se 1 (by rfl) ⟨54590, by rfl⟩) R109181
theorem R72803 : Reach 72803 := rs (se 1 (by rfl) ⟨54602, by rfl⟩) R109205
theorem R269411 : Reach 269411 := rs (se 1 (by rfl) ⟨202058, by rfl⟩) R404117
theorem R72819 : Reach 72819 := rs (se 1 (by rfl) ⟨54614, by rfl⟩) R109229
theorem R72835 : Reach 72835 := rs (se 1 (by rfl) ⟨54626, by rfl⟩) R109253
theorem R72851 : Reach 72851 := rs (se 1 (by rfl) ⟨54638, by rfl⟩) R109277
theorem R72867 : Reach 72867 := rs (se 1 (by rfl) ⟨54650, by rfl⟩) R109301
theorem R72883 : Reach 72883 := rs (se 1 (by rfl) ⟨54662, by rfl⟩) R109325
theorem R72899 : Reach 72899 := rs (se 1 (by rfl) ⟨54674, by rfl⟩) R109349
theorem R138449 : Reach 138449 := rs (se 2 (by rfl) ⟨51918, by rfl⟩) R103837
theorem R72915 : Reach 72915 := rs (se 1 (by rfl) ⟨54686, by rfl⟩) R109373
theorem R72931 : Reach 72931 := rs (se 1 (by rfl) ⟨54698, by rfl⟩) R109397
theorem R72947 : Reach 72947 := rs (se 1 (by rfl) ⟨54710, by rfl⟩) R109421
theorem R72963 : Reach 72963 := rs (se 1 (by rfl) ⟨54722, by rfl⟩) R109445
theorem R72979 : Reach 72979 := rs (se 1 (by rfl) ⟨54734, by rfl⟩) R109469
theorem R72995 : Reach 72995 := rs (se 1 (by rfl) ⟨54746, by rfl⟩) R109493
theorem R73011 : Reach 73011 := rs (se 1 (by rfl) ⟨54758, by rfl⟩) R109517
theorem R73027 : Reach 73027 := rs (se 1 (by rfl) ⟨54770, by rfl⟩) R109541
theorem R73043 : Reach 73043 := rs (se 1 (by rfl) ⟨54782, by rfl⟩) R109565
theorem R73059 : Reach 73059 := rs (se 1 (by rfl) ⟨54794, by rfl⟩) R109589
theorem R73075 : Reach 73075 := rs (se 1 (by rfl) ⟨54806, by rfl⟩) R109613
theorem R73091 : Reach 73091 := rs (se 1 (by rfl) ⟨54818, by rfl⟩) R109637
theorem R73107 : Reach 73107 := rs (se 1 (by rfl) ⟨54830, by rfl⟩) R109661
theorem R73123 : Reach 73123 := rs (se 1 (by rfl) ⟨54842, by rfl⟩) R109685
theorem R73139 : Reach 73139 := rs (se 1 (by rfl) ⟨54854, by rfl⟩) R109709
theorem R73155 : Reach 73155 := rs (se 1 (by rfl) ⟨54866, by rfl⟩) R109733
theorem R433613 : Reach 433613 := rs (se 3 (by rfl) ⟨81302, by rfl⟩) R162605
theorem R73171 : Reach 73171 := rs (se 1 (by rfl) ⟨54878, by rfl⟩) R109757
theorem R73187 : Reach 73187 := rs (se 1 (by rfl) ⟨54890, by rfl⟩) R109781
theorem R73203 : Reach 73203 := rs (se 1 (by rfl) ⟨54902, by rfl⟩) R109805
theorem R73219 : Reach 73219 := rs (se 1 (by rfl) ⟨54914, by rfl⟩) R109829
theorem R73235 : Reach 73235 := rs (se 1 (by rfl) ⟨54926, by rfl⟩) R109853
theorem R73251 : Reach 73251 := rs (se 1 (by rfl) ⟨54938, by rfl⟩) R109877
theorem R269873 : Reach 269873 := rs (se 2 (by rfl) ⟨101202, by rfl⟩) R202405
theorem R73267 : Reach 73267 := rs (se 1 (by rfl) ⟨54950, by rfl⟩) R109901
theorem R73283 : Reach 73283 := rs (se 1 (by rfl) ⟨54962, by rfl⟩) R109925
theorem R73299 : Reach 73299 := rs (se 1 (by rfl) ⟨54974, by rfl⟩) R109949
theorem R73315 : Reach 73315 := rs (se 1 (by rfl) ⟨54986, by rfl⟩) R109973
theorem R892529 : Reach 892529 := rs (se 2 (by rfl) ⟨334698, by rfl⟩) R669397
theorem R73331 : Reach 73331 := rs (se 1 (by rfl) ⟨54998, by rfl⟩) R109997
theorem R73347 : Reach 73347 := rs (se 1 (by rfl) ⟨55010, by rfl⟩) R110021
theorem R106115 : Reach 106115 := rs (se 1 (by rfl) ⟨79586, by rfl⟩) R159173
theorem R532109 : Reach 532109 := rs (se 3 (by rfl) ⟨99770, by rfl⟩) R199541
theorem R73363 : Reach 73363 := rs (se 1 (by rfl) ⟨55022, by rfl⟩) R110045
theorem R73379 : Reach 73379 := rs (se 1 (by rfl) ⟨55034, by rfl⟩) R110069
theorem R73395 : Reach 73395 := rs (se 1 (by rfl) ⟨55046, by rfl⟩) R110093
theorem R73411 : Reach 73411 := rs (se 1 (by rfl) ⟨55058, by rfl⟩) R110117
theorem R73427 : Reach 73427 := rs (se 1 (by rfl) ⟨55070, by rfl⟩) R110141
theorem R73443 : Reach 73443 := rs (se 1 (by rfl) ⟨55082, by rfl⟩) R110165
theorem R73459 : Reach 73459 := rs (se 1 (by rfl) ⟨55094, by rfl⟩) R110189
theorem R73475 : Reach 73475 := rs (se 1 (by rfl) ⟨55106, by rfl⟩) R110213
theorem R73491 : Reach 73491 := rs (se 1 (by rfl) ⟨55118, by rfl⟩) R110237
theorem R73507 : Reach 73507 := rs (se 1 (by rfl) ⟨55130, by rfl⟩) R110261
theorem R73523 : Reach 73523 := rs (se 1 (by rfl) ⟨55142, by rfl⟩) R110285
theorem R73539 : Reach 73539 := rs (se 1 (by rfl) ⟨55154, by rfl⟩) R110309
theorem R73555 : Reach 73555 := rs (se 1 (by rfl) ⟨55166, by rfl⟩) R110333
theorem R73571 : Reach 73571 := rs (se 1 (by rfl) ⟨55178, by rfl⟩) R110357
theorem R73587 : Reach 73587 := rs (se 1 (by rfl) ⟨55190, by rfl⟩) R110381
theorem R73603 : Reach 73603 := rs (se 1 (by rfl) ⟨55202, by rfl⟩) R110405
theorem R73619 : Reach 73619 := rs (se 1 (by rfl) ⟨55214, by rfl⟩) R110429
theorem R73635 : Reach 73635 := rs (se 1 (by rfl) ⟨55226, by rfl⟩) R110453
theorem R139171 : Reach 139171 := rs (se 1 (by rfl) ⟨104378, by rfl⟩) R208757
theorem R73651 : Reach 73651 := rs (se 1 (by rfl) ⟨55238, by rfl⟩) R110477
theorem R73667 : Reach 73667 := rs (se 1 (by rfl) ⟨55250, by rfl⟩) R110501
theorem R73683 : Reach 73683 := rs (se 1 (by rfl) ⟨55262, by rfl⟩) R110525
theorem R73699 : Reach 73699 := rs (se 1 (by rfl) ⟨55274, by rfl⟩) R110549
theorem R204781 : Reach 204781 := rs (se 3 (by rfl) ⟨38396, by rfl⟩) R76793
theorem R73715 : Reach 73715 := rs (se 1 (by rfl) ⟨55286, by rfl⟩) R110573
theorem R73731 : Reach 73731 := rs (se 1 (by rfl) ⟨55298, by rfl⟩) R110597
theorem R73747 : Reach 73747 := rs (se 1 (by rfl) ⟨55310, by rfl⟩) R110621
theorem R73763 : Reach 73763 := rs (se 1 (by rfl) ⟨55322, by rfl⟩) R110645
theorem R73779 : Reach 73779 := rs (se 1 (by rfl) ⟨55334, by rfl⟩) R110669
theorem R73795 : Reach 73795 := rs (se 1 (by rfl) ⟨55346, by rfl⟩) R110693
theorem R73811 : Reach 73811 := rs (se 1 (by rfl) ⟨55358, by rfl⟩) R110717
theorem R73827 : Reach 73827 := rs (se 1 (by rfl) ⟨55370, by rfl⟩) R110741
theorem R73843 : Reach 73843 := rs (se 1 (by rfl) ⟨55382, by rfl⟩) R110765
theorem R73859 : Reach 73859 := rs (se 1 (by rfl) ⟨55394, by rfl⟩) R110789
theorem R73875 : Reach 73875 := rs (se 1 (by rfl) ⟨55406, by rfl⟩) R110813
theorem R73891 : Reach 73891 := rs (se 1 (by rfl) ⟨55418, by rfl⟩) R110837
theorem R73907 : Reach 73907 := rs (se 1 (by rfl) ⟨55430, by rfl⟩) R110861
theorem R106691 : Reach 106691 := rs (se 1 (by rfl) ⟨80018, by rfl⟩) R160037
theorem R73923 : Reach 73923 := rs (se 1 (by rfl) ⟨55442, by rfl⟩) R110885
theorem R73939 : Reach 73939 := rs (se 1 (by rfl) ⟨55454, by rfl⟩) R110909
theorem R106721 : Reach 106721 := rs (se 2 (by rfl) ⟨40020, by rfl⟩) R80041
theorem R73955 : Reach 73955 := rs (se 1 (by rfl) ⟨55466, by rfl⟩) R110933
theorem R106739 : Reach 106739 := rs (se 1 (by rfl) ⟨80054, by rfl⟩) R160109
theorem R73971 : Reach 73971 := rs (se 1 (by rfl) ⟨55478, by rfl⟩) R110957
theorem R73987 : Reach 73987 := rs (se 1 (by rfl) ⟨55490, by rfl⟩) R110981
theorem R106753 : Reach 106753 := rs (se 2 (by rfl) ⟨40032, by rfl⟩) R80065
theorem R106769 : Reach 106769 := rs (se 2 (by rfl) ⟨40038, by rfl⟩) R80077
theorem R74003 : Reach 74003 := rs (se 1 (by rfl) ⟨55502, by rfl⟩) R111005
theorem R106787 : Reach 106787 := rs (se 1 (by rfl) ⟨80090, by rfl⟩) R160181
theorem R74019 : Reach 74019 := rs (se 1 (by rfl) ⟨55514, by rfl⟩) R111029
theorem R270641 : Reach 270641 := rs (se 2 (by rfl) ⟨101490, by rfl⟩) R202981
theorem R74035 : Reach 74035 := rs (se 1 (by rfl) ⟨55526, by rfl⟩) R111053
theorem R106817 : Reach 106817 := rs (se 2 (by rfl) ⟨40056, by rfl⟩) R80113
theorem R74051 : Reach 74051 := rs (se 1 (by rfl) ⟨55538, by rfl⟩) R111077
theorem R106835 : Reach 106835 := rs (se 1 (by rfl) ⟨80126, by rfl⟩) R160253
theorem R74067 : Reach 74067 := rs (se 1 (by rfl) ⟨55550, by rfl⟩) R111101
theorem R139619 : Reach 139619 := rs (se 1 (by rfl) ⟨104714, by rfl⟩) R209429
theorem R74083 : Reach 74083 := rs (se 1 (by rfl) ⟨55562, by rfl⟩) R111125
theorem R106865 : Reach 106865 := rs (se 2 (by rfl) ⟨40074, by rfl⟩) R80149
theorem R74099 : Reach 74099 := rs (se 1 (by rfl) ⟨55574, by rfl⟩) R111149
theorem R106867 : Reach 106867 := rs (se 1 (by rfl) ⟨80150, by rfl⟩) R160301
theorem R106883 : Reach 106883 := rs (se 1 (by rfl) ⟨80162, by rfl⟩) R160325
theorem R74115 : Reach 74115 := rs (se 1 (by rfl) ⟨55586, by rfl⟩) R111173
theorem R74131 : Reach 74131 := rs (se 1 (by rfl) ⟨55598, by rfl⟩) R111197
theorem R106913 : Reach 106913 := rs (se 2 (by rfl) ⟨40092, by rfl⟩) R80185
theorem R74147 : Reach 74147 := rs (se 1 (by rfl) ⟨55610, by rfl⟩) R111221
theorem R106931 : Reach 106931 := rs (se 1 (by rfl) ⟨80198, by rfl⟩) R160397
theorem R74163 : Reach 74163 := rs (se 1 (by rfl) ⟨55622, by rfl⟩) R111245
theorem R74179 : Reach 74179 := rs (se 1 (by rfl) ⟨55634, by rfl⟩) R111269
theorem R106961 : Reach 106961 := rs (se 2 (by rfl) ⟨40110, by rfl⟩) R80221
theorem R74195 : Reach 74195 := rs (se 1 (by rfl) ⟨55646, by rfl⟩) R111293
theorem R106979 : Reach 106979 := rs (se 1 (by rfl) ⟨80234, by rfl⟩) R160469
theorem R74211 : Reach 74211 := rs (se 1 (by rfl) ⟨55658, by rfl⟩) R111317
theorem R74227 : Reach 74227 := rs (se 1 (by rfl) ⟨55670, by rfl⟩) R111341
theorem R107009 : Reach 107009 := rs (se 2 (by rfl) ⟨40128, by rfl⟩) R80257
theorem R74243 : Reach 74243 := rs (se 1 (by rfl) ⟨55682, by rfl⟩) R111365
theorem R107027 : Reach 107027 := rs (se 1 (by rfl) ⟨80270, by rfl⟩) R160541
theorem R74259 : Reach 74259 := rs (se 1 (by rfl) ⟨55694, by rfl⟩) R111389
theorem R74275 : Reach 74275 := rs (se 1 (by rfl) ⟨55706, by rfl⟩) R111413
theorem R107057 : Reach 107057 := rs (se 2 (by rfl) ⟨40146, by rfl⟩) R80293
theorem R74291 : Reach 74291 := rs (se 1 (by rfl) ⟨55718, by rfl⟩) R111437
theorem R107075 : Reach 107075 := rs (se 1 (by rfl) ⟨80306, by rfl⟩) R160613
theorem R74307 : Reach 74307 := rs (se 1 (by rfl) ⟨55730, by rfl⟩) R111461
theorem R74323 : Reach 74323 := rs (se 1 (by rfl) ⟨55742, by rfl⟩) R111485
theorem R107105 : Reach 107105 := rs (se 2 (by rfl) ⟨40164, by rfl⟩) R80329
theorem R74339 : Reach 74339 := rs (se 1 (by rfl) ⟨55754, by rfl⟩) R111509
theorem R107123 : Reach 107123 := rs (se 1 (by rfl) ⟨80342, by rfl⟩) R160685
theorem R74355 : Reach 74355 := rs (se 1 (by rfl) ⟨55766, by rfl⟩) R111533
theorem R139907 : Reach 139907 := rs (se 1 (by rfl) ⟨104930, by rfl⟩) R209861
theorem R74371 : Reach 74371 := rs (se 1 (by rfl) ⟨55778, by rfl⟩) R111557
theorem R107153 : Reach 107153 := rs (se 2 (by rfl) ⟨40182, by rfl⟩) R80365
theorem R74387 : Reach 74387 := rs (se 1 (by rfl) ⟨55790, by rfl⟩) R111581
theorem R107171 : Reach 107171 := rs (se 1 (by rfl) ⟨80378, by rfl⟩) R160757
theorem R74403 : Reach 74403 := rs (se 1 (by rfl) ⟨55802, by rfl⟩) R111605
theorem R74419 : Reach 74419 := rs (se 1 (by rfl) ⟨55814, by rfl⟩) R111629
theorem R107201 : Reach 107201 := rs (se 2 (by rfl) ⟨40200, by rfl⟩) R80401
theorem R74435 : Reach 74435 := rs (se 1 (by rfl) ⟨55826, by rfl⟩) R111653
theorem R467653 : Reach 467653 := rs (se 4 (by rfl) ⟨43842, by rfl⟩) R87685
theorem R107219 : Reach 107219 := rs (se 1 (by rfl) ⟨80414, by rfl⟩) R160829
theorem R74451 : Reach 74451 := rs (se 1 (by rfl) ⟨55838, by rfl⟩) R111677
theorem R74467 : Reach 74467 := rs (se 1 (by rfl) ⟨55850, by rfl⟩) R111701
theorem R303857 : Reach 303857 := rs (se 2 (by rfl) ⟨113946, by rfl⟩) R227893
theorem R107249 : Reach 107249 := rs (se 2 (by rfl) ⟨40218, by rfl⟩) R80437
theorem R74483 : Reach 74483 := rs (se 1 (by rfl) ⟨55862, by rfl⟩) R111725
theorem R107267 : Reach 107267 := rs (se 1 (by rfl) ⟨80450, by rfl⟩) R160901
theorem R74499 : Reach 74499 := rs (se 1 (by rfl) ⟨55874, by rfl⟩) R111749
theorem R238349 : Reach 238349 := rs (se 3 (by rfl) ⟨44690, by rfl⟩) R89381
theorem R74515 : Reach 74515 := rs (se 1 (by rfl) ⟨55886, by rfl⟩) R111773
theorem R107297 : Reach 107297 := rs (se 2 (by rfl) ⟨40236, by rfl⟩) R80473
theorem R74531 : Reach 74531 := rs (se 1 (by rfl) ⟨55898, by rfl⟩) R111797
theorem R107315 : Reach 107315 := rs (se 1 (by rfl) ⟨80486, by rfl⟩) R160973
theorem R74547 : Reach 74547 := rs (se 1 (by rfl) ⟨55910, by rfl⟩) R111821
theorem R74563 : Reach 74563 := rs (se 1 (by rfl) ⟨55922, by rfl⟩) R111845
theorem R107345 : Reach 107345 := rs (se 2 (by rfl) ⟨40254, by rfl⟩) R80509
theorem R74579 : Reach 74579 := rs (se 1 (by rfl) ⟨55934, by rfl⟩) R111869
theorem R107363 : Reach 107363 := rs (se 1 (by rfl) ⟨80522, by rfl⟩) R161045
theorem R74595 : Reach 74595 := rs (se 1 (by rfl) ⟨55946, by rfl⟩) R111893
theorem R664433 : Reach 664433 := rs (se 2 (by rfl) ⟨249162, by rfl⟩) R498325
theorem R369521 : Reach 369521 := rs (se 2 (by rfl) ⟨138570, by rfl⟩) R277141
theorem R74611 : Reach 74611 := rs (se 1 (by rfl) ⟨55958, by rfl⟩) R111917
theorem R107393 : Reach 107393 := rs (se 2 (by rfl) ⟨40272, by rfl⟩) R80545
theorem R435077 : Reach 435077 := rs (se 4 (by rfl) ⟨40788, by rfl⟩) R81577
theorem R74627 : Reach 74627 := rs (se 1 (by rfl) ⟨55970, by rfl⟩) R111941
theorem R107411 : Reach 107411 := rs (se 1 (by rfl) ⟨80558, by rfl⟩) R161117
theorem R74643 : Reach 74643 := rs (se 1 (by rfl) ⟨55982, by rfl⟩) R111965
theorem R74659 : Reach 74659 := rs (se 1 (by rfl) ⟨55994, by rfl⟩) R111989
theorem R107441 : Reach 107441 := rs (se 2 (by rfl) ⟨40290, by rfl⟩) R80581
theorem R74675 : Reach 74675 := rs (se 1 (by rfl) ⟨56006, by rfl⟩) R112013
theorem R107459 : Reach 107459 := rs (se 1 (by rfl) ⟨80594, by rfl⟩) R161189
theorem R74691 : Reach 74691 := rs (se 1 (by rfl) ⟨56018, by rfl⟩) R112037
theorem R271309 : Reach 271309 := rs (se 3 (by rfl) ⟨50870, by rfl⟩) R101741
theorem R74707 : Reach 74707 := rs (se 1 (by rfl) ⟨56030, by rfl⟩) R112061
theorem R107489 : Reach 107489 := rs (se 2 (by rfl) ⟨40308, by rfl⟩) R80617
theorem R74723 : Reach 74723 := rs (se 1 (by rfl) ⟨56042, by rfl⟩) R112085
theorem R107507 : Reach 107507 := rs (se 1 (by rfl) ⟨80630, by rfl⟩) R161261
theorem R74739 : Reach 74739 := rs (se 1 (by rfl) ⟨56054, by rfl⟩) R112109
theorem R74755 : Reach 74755 := rs (se 1 (by rfl) ⟨56066, by rfl⟩) R112133
theorem R500741 : Reach 500741 := rs (se 4 (by rfl) ⟨46944, by rfl⟩) R93889
theorem R107537 : Reach 107537 := rs (se 2 (by rfl) ⟨40326, by rfl⟩) R80653
theorem R205841 : Reach 205841 := rs (se 2 (by rfl) ⟨77190, by rfl⟩) R154381
theorem R74771 : Reach 74771 := rs (se 1 (by rfl) ⟨56078, by rfl⟩) R112157
theorem R107555 : Reach 107555 := rs (se 1 (by rfl) ⟨80666, by rfl⟩) R161333
theorem R74787 : Reach 74787 := rs (se 1 (by rfl) ⟨56090, by rfl⟩) R112181
theorem R74803 : Reach 74803 := rs (se 1 (by rfl) ⟨56102, by rfl⟩) R112205
theorem R107585 : Reach 107585 := rs (se 2 (by rfl) ⟨40344, by rfl⟩) R80689
theorem R74819 : Reach 74819 := rs (se 1 (by rfl) ⟨56114, by rfl⟩) R112229
theorem R107603 : Reach 107603 := rs (se 1 (by rfl) ⟨80702, by rfl⟩) R161405
theorem R74835 : Reach 74835 := rs (se 1 (by rfl) ⟨56126, by rfl⟩) R112253
theorem R631907 : Reach 631907 := rs (se 1 (by rfl) ⟨473930, by rfl⟩) R947861
theorem R74851 : Reach 74851 := rs (se 1 (by rfl) ⟨56138, by rfl⟩) R112277
theorem R107633 : Reach 107633 := rs (se 2 (by rfl) ⟨40362, by rfl⟩) R80725
theorem R140401 : Reach 140401 := rs (se 2 (by rfl) ⟨52650, by rfl⟩) R105301
theorem R74867 : Reach 74867 := rs (se 1 (by rfl) ⟨56150, by rfl⟩) R112301
theorem R304241 : Reach 304241 := rs (se 2 (by rfl) ⟨114090, by rfl⟩) R228181
theorem R107651 : Reach 107651 := rs (se 1 (by rfl) ⟨80738, by rfl⟩) R161477
theorem R74883 : Reach 74883 := rs (se 1 (by rfl) ⟨56162, by rfl⟩) R112325
theorem R205955 : Reach 205955 := rs (se 1 (by rfl) ⟨154466, by rfl⟩) R308933
theorem R74899 : Reach 74899 := rs (se 1 (by rfl) ⟨56174, by rfl⟩) R112349
theorem R107681 : Reach 107681 := rs (se 2 (by rfl) ⟨40380, by rfl⟩) R80761
theorem R74915 : Reach 74915 := rs (se 1 (by rfl) ⟨56186, by rfl⟩) R112373
theorem R107699 : Reach 107699 := rs (se 1 (by rfl) ⟨80774, by rfl⟩) R161549
theorem R74931 : Reach 74931 := rs (se 1 (by rfl) ⟨56198, by rfl⟩) R112397
theorem R74947 : Reach 74947 := rs (se 1 (by rfl) ⟨56210, by rfl⟩) R112421
theorem R107729 : Reach 107729 := rs (se 2 (by rfl) ⟨40398, by rfl⟩) R80797
theorem R74963 : Reach 74963 := rs (se 1 (by rfl) ⟨56222, by rfl⟩) R112445
theorem R107747 : Reach 107747 := rs (se 1 (by rfl) ⟨80810, by rfl⟩) R161621
theorem R74979 : Reach 74979 := rs (se 1 (by rfl) ⟨56234, by rfl⟩) R112469
theorem R74995 : Reach 74995 := rs (se 1 (by rfl) ⟨56246, by rfl⟩) R112493
theorem R107777 : Reach 107777 := rs (se 2 (by rfl) ⟨40416, by rfl⟩) R80833
theorem R75011 : Reach 75011 := rs (se 1 (by rfl) ⟨56258, by rfl⟩) R112517
theorem R107795 : Reach 107795 := rs (se 1 (by rfl) ⟨80846, by rfl⟩) R161693
theorem R75027 : Reach 75027 := rs (se 1 (by rfl) ⟨56270, by rfl⟩) R112541
theorem R75043 : Reach 75043 := rs (se 1 (by rfl) ⟨56282, by rfl⟩) R112565
theorem R107825 : Reach 107825 := rs (se 2 (by rfl) ⟨40434, by rfl⟩) R80869
theorem R75059 : Reach 75059 := rs (se 1 (by rfl) ⟨56294, by rfl⟩) R112589
theorem R107843 : Reach 107843 := rs (se 1 (by rfl) ⟨80882, by rfl⟩) R161765
theorem R75075 : Reach 75075 := rs (se 1 (by rfl) ⟨56306, by rfl⟩) R112613
theorem R75091 : Reach 75091 := rs (se 1 (by rfl) ⟨56318, by rfl⟩) R112637
theorem R107873 : Reach 107873 := rs (se 2 (by rfl) ⟨40452, by rfl⟩) R80905
theorem R75107 : Reach 75107 := rs (se 1 (by rfl) ⟨56330, by rfl⟩) R112661
theorem R206189 : Reach 206189 := rs (se 3 (by rfl) ⟨38660, by rfl⟩) R77321
theorem R107891 : Reach 107891 := rs (se 1 (by rfl) ⟨80918, by rfl⟩) R161837
theorem R75123 : Reach 75123 := rs (se 1 (by rfl) ⟨56342, by rfl⟩) R112685
theorem R107921 : Reach 107921 := rs (se 2 (by rfl) ⟨40470, by rfl⟩) R80941
theorem R107939 : Reach 107939 := rs (se 1 (by rfl) ⟨80954, by rfl⟩) R161909
theorem R107969 : Reach 107969 := rs (se 2 (by rfl) ⟨40488, by rfl⟩) R80977
theorem R107987 : Reach 107987 := rs (se 1 (by rfl) ⟨80990, by rfl⟩) R161981
theorem R140771 : Reach 140771 := rs (se 1 (by rfl) ⟨105578, by rfl⟩) R211157
theorem R108017 : Reach 108017 := rs (se 2 (by rfl) ⟨40506, by rfl⟩) R81013
theorem R108035 : Reach 108035 := rs (se 1 (by rfl) ⟨81026, by rfl⟩) R162053
theorem R108065 : Reach 108065 := rs (se 2 (by rfl) ⟨40524, by rfl⟩) R81049
theorem R140849 : Reach 140849 := rs (se 2 (by rfl) ⟨52818, by rfl⟩) R105637
theorem R108083 : Reach 108083 := rs (se 1 (by rfl) ⟨81062, by rfl⟩) R162125
theorem R108113 : Reach 108113 := rs (se 2 (by rfl) ⟨40542, by rfl⟩) R81085
theorem R108131 : Reach 108131 := rs (se 1 (by rfl) ⟨81098, by rfl⟩) R162197
theorem R108161 : Reach 108161 := rs (se 2 (by rfl) ⟨40560, by rfl⟩) R81121
theorem R108179 : Reach 108179 := rs (se 1 (by rfl) ⟨81134, by rfl⟩) R162269
theorem R108209 : Reach 108209 := rs (se 2 (by rfl) ⟨40578, by rfl⟩) R81157
theorem R206513 : Reach 206513 := rs (se 2 (by rfl) ⟨77442, by rfl⟩) R154885
theorem R108227 : Reach 108227 := rs (se 1 (by rfl) ⟨81170, by rfl⟩) R162341
theorem R108257 : Reach 108257 := rs (se 2 (by rfl) ⟨40596, by rfl⟩) R81193
theorem R272099 : Reach 272099 := rs (se 1 (by rfl) ⟨204074, by rfl⟩) R408149
theorem R108275 : Reach 108275 := rs (se 1 (by rfl) ⟨81206, by rfl⟩) R162413
theorem R108305 : Reach 108305 := rs (se 2 (by rfl) ⟨40614, by rfl⟩) R81229
theorem R108323 : Reach 108323 := rs (se 1 (by rfl) ⟨81242, by rfl⟩) R162485
theorem R108353 : Reach 108353 := rs (se 2 (by rfl) ⟨40632, by rfl⟩) R81265
theorem R108371 : Reach 108371 := rs (se 1 (by rfl) ⟨81278, by rfl⟩) R162557
theorem R108401 : Reach 108401 := rs (se 2 (by rfl) ⟨40650, by rfl⟩) R81301
theorem R206723 : Reach 206723 := rs (se 1 (by rfl) ⟨155042, by rfl⟩) R310085
theorem R108419 : Reach 108419 := rs (se 1 (by rfl) ⟨81314, by rfl⟩) R162629
theorem R108449 : Reach 108449 := rs (se 2 (by rfl) ⟨40668, by rfl⟩) R81337
theorem R108467 : Reach 108467 := rs (se 1 (by rfl) ⟨81350, by rfl⟩) R162701
theorem R108497 : Reach 108497 := rs (se 2 (by rfl) ⟨40686, by rfl⟩) R81373
theorem R108515 : Reach 108515 := rs (se 1 (by rfl) ⟨81386, by rfl⟩) R162773
theorem R108545 : Reach 108545 := rs (se 2 (by rfl) ⟨40704, by rfl⟩) R81409
theorem R108563 : Reach 108563 := rs (se 1 (by rfl) ⟨81422, by rfl⟩) R162845
theorem R108593 : Reach 108593 := rs (se 2 (by rfl) ⟨40722, by rfl⟩) R81445
theorem R108611 : Reach 108611 := rs (se 1 (by rfl) ⟨81458, by rfl⟩) R162917
theorem R108641 : Reach 108641 := rs (se 2 (by rfl) ⟨40740, by rfl⟩) R81481
theorem R108659 : Reach 108659 := rs (se 1 (by rfl) ⟨81494, by rfl⟩) R162989
theorem R108689 : Reach 108689 := rs (se 2 (by rfl) ⟨40758, by rfl⟩) R81517
theorem R108707 : Reach 108707 := rs (se 1 (by rfl) ⟨81530, by rfl⟩) R163061
theorem R108737 : Reach 108737 := rs (se 2 (by rfl) ⟨40776, by rfl⟩) R81553
theorem R2009285 : Reach 2009285 := rs (se 4 (by rfl) ⟨188370, by rfl⟩) R376741
theorem R108755 : Reach 108755 := rs (se 1 (by rfl) ⟨81566, by rfl⟩) R163133
theorem R108785 : Reach 108785 := rs (se 2 (by rfl) ⟨40794, by rfl⟩) R81589
theorem R108803 : Reach 108803 := rs (se 1 (by rfl) ⟨81602, by rfl⟩) R163205
theorem R108833 : Reach 108833 := rs (se 2 (by rfl) ⟨40812, by rfl⟩) R81625
theorem R370979 : Reach 370979 := rs (se 1 (by rfl) ⟨278234, by rfl⟩) R556469
theorem R108851 : Reach 108851 := rs (se 1 (by rfl) ⟨81638, by rfl⟩) R163277
theorem R108881 : Reach 108881 := rs (se 2 (by rfl) ⟨40830, by rfl⟩) R81661
theorem R108899 : Reach 108899 := rs (se 1 (by rfl) ⟨81674, by rfl⟩) R163349
theorem R272753 : Reach 272753 := rs (se 2 (by rfl) ⟨102282, by rfl⟩) R204565
theorem R108929 : Reach 108929 := rs (se 2 (by rfl) ⟨40848, by rfl⟩) R81697
theorem R108947 : Reach 108947 := rs (se 1 (by rfl) ⟨81710, by rfl⟩) R163421
theorem R108977 : Reach 108977 := rs (se 2 (by rfl) ⟨40866, by rfl⟩) R81733
theorem R141745 : Reach 141745 := rs (se 2 (by rfl) ⟨53154, by rfl⟩) R106309
theorem R108995 : Reach 108995 := rs (se 1 (by rfl) ⟨81746, by rfl⟩) R163493
theorem R207299 : Reach 207299 := rs (se 1 (by rfl) ⟨155474, by rfl⟩) R310949
theorem R109025 : Reach 109025 := rs (se 2 (by rfl) ⟨40884, by rfl⟩) R81769
theorem R109043 : Reach 109043 := rs (se 1 (by rfl) ⟨81782, by rfl⟩) R163565
theorem R109073 : Reach 109073 := rs (se 2 (by rfl) ⟨40902, by rfl⟩) R81805
theorem R109091 : Reach 109091 := rs (se 1 (by rfl) ⟨81818, by rfl⟩) R163637
theorem R109121 : Reach 109121 := rs (se 2 (by rfl) ⟨40920, by rfl⟩) R81841
theorem R141905 : Reach 141905 := rs (se 2 (by rfl) ⟨53214, by rfl⟩) R106429
theorem R109139 : Reach 109139 := rs (se 1 (by rfl) ⟨81854, by rfl⟩) R163709
theorem R109169 : Reach 109169 := rs (se 2 (by rfl) ⟨40938, by rfl⟩) R81877
theorem R109187 : Reach 109187 := rs (se 1 (by rfl) ⟨81890, by rfl⟩) R163781
theorem R109217 : Reach 109217 := rs (se 2 (by rfl) ⟨40956, by rfl⟩) R81913
theorem R174755 : Reach 174755 := rs (se 1 (by rfl) ⟨131066, by rfl⟩) R262133
theorem R109235 : Reach 109235 := rs (se 1 (by rfl) ⟨81926, by rfl⟩) R163853
theorem R109265 : Reach 109265 := rs (se 2 (by rfl) ⟨40974, by rfl⟩) R81949
theorem R109283 : Reach 109283 := rs (se 1 (by rfl) ⟨81962, by rfl⟩) R163925
theorem R109313 : Reach 109313 := rs (se 2 (by rfl) ⟨40992, by rfl⟩) R81985
theorem R207629 : Reach 207629 := rs (se 3 (by rfl) ⟨38930, by rfl⟩) R77861
theorem R109331 : Reach 109331 := rs (se 1 (by rfl) ⟨81998, by rfl⟩) R163997
theorem R109361 : Reach 109361 := rs (se 2 (by rfl) ⟨41010, by rfl⟩) R82021
theorem R109379 : Reach 109379 := rs (se 1 (by rfl) ⟨82034, by rfl⟩) R164069
theorem R568133 : Reach 568133 := rs (se 4 (by rfl) ⟨53262, by rfl⟩) R106525
theorem R240461 : Reach 240461 := rs (se 3 (by rfl) ⟨45086, by rfl⟩) R90173
theorem R207697 : Reach 207697 := rs (se 2 (by rfl) ⟨77886, by rfl⟩) R155773
theorem R109409 : Reach 109409 := rs (se 2 (by rfl) ⟨41028, by rfl⟩) R82057
theorem R109427 : Reach 109427 := rs (se 1 (by rfl) ⟨82070, by rfl⟩) R164141
theorem R240515 : Reach 240515 := rs (se 1 (by rfl) ⟨180386, by rfl⟩) R360773
theorem R109457 : Reach 109457 := rs (se 2 (by rfl) ⟨41046, by rfl⟩) R82093
theorem R240529 : Reach 240529 := rs (se 2 (by rfl) ⟨90198, by rfl⟩) R180397
theorem R109475 : Reach 109475 := rs (se 1 (by rfl) ⟨82106, by rfl⟩) R164213
theorem R109505 : Reach 109505 := rs (se 2 (by rfl) ⟨41064, by rfl⟩) R82129
theorem R109523 : Reach 109523 := rs (se 1 (by rfl) ⟨82142, by rfl⟩) R164285
theorem R142307 : Reach 142307 := rs (se 1 (by rfl) ⟨106730, by rfl⟩) R213461
theorem R109553 : Reach 109553 := rs (se 2 (by rfl) ⟨41082, by rfl⟩) R82165
theorem R109571 : Reach 109571 := rs (se 1 (by rfl) ⟨82178, by rfl⟩) R164357
theorem R109601 : Reach 109601 := rs (se 2 (by rfl) ⟨41100, by rfl⟩) R82201
theorem R109619 : Reach 109619 := rs (se 1 (by rfl) ⟨82214, by rfl⟩) R164429
theorem R371789 : Reach 371789 := rs (se 3 (by rfl) ⟨69710, by rfl⟩) R139421
theorem R109649 : Reach 109649 := rs (se 2 (by rfl) ⟨41118, by rfl⟩) R82237
theorem R207971 : Reach 207971 := rs (se 1 (by rfl) ⟨155978, by rfl⟩) R311957
theorem R109667 : Reach 109667 := rs (se 1 (by rfl) ⟨82250, by rfl⟩) R164501
theorem R109697 : Reach 109697 := rs (se 2 (by rfl) ⟨41136, by rfl⟩) R82273
theorem R306317 : Reach 306317 := rs (se 3 (by rfl) ⟨57434, by rfl⟩) R114869
theorem R240785 : Reach 240785 := rs (se 2 (by rfl) ⟨90294, by rfl⟩) R180589
theorem R109715 : Reach 109715 := rs (se 1 (by rfl) ⟨82286, by rfl⟩) R164573
theorem R109745 : Reach 109745 := rs (se 2 (by rfl) ⟨41154, by rfl⟩) R82309
theorem R109763 : Reach 109763 := rs (se 1 (by rfl) ⟨82322, by rfl⟩) R164645
theorem R109793 : Reach 109793 := rs (se 2 (by rfl) ⟨41172, by rfl⟩) R82345
theorem R109811 : Reach 109811 := rs (se 1 (by rfl) ⟨82358, by rfl⟩) R164717
theorem R109841 : Reach 109841 := rs (se 2 (by rfl) ⟨41190, by rfl⟩) R82381
theorem R109859 : Reach 109859 := rs (se 1 (by rfl) ⟨82394, by rfl⟩) R164789
theorem R109889 : Reach 109889 := rs (se 2 (by rfl) ⟨41208, by rfl⟩) R82417
theorem R109907 : Reach 109907 := rs (se 1 (by rfl) ⟨82430, by rfl⟩) R164861
theorem R109937 : Reach 109937 := rs (se 2 (by rfl) ⟨41226, by rfl⟩) R82453
theorem R109955 : Reach 109955 := rs (se 1 (by rfl) ⟨82466, by rfl⟩) R164933
theorem R77203 : Reach 77203 := rs (se 1 (by rfl) ⟨57902, by rfl⟩) R115805
theorem R109985 : Reach 109985 := rs (se 2 (by rfl) ⟨41244, by rfl⟩) R82489
theorem R110003 : Reach 110003 := rs (se 1 (by rfl) ⟨82502, by rfl⟩) R165005
theorem R110033 : Reach 110033 := rs (se 2 (by rfl) ⟨41262, by rfl⟩) R82525
theorem R306659 : Reach 306659 := rs (se 1 (by rfl) ⟨229994, by rfl⟩) R459989
theorem R110051 : Reach 110051 := rs (se 1 (by rfl) ⟨82538, by rfl⟩) R165077
theorem R110081 : Reach 110081 := rs (se 2 (by rfl) ⟨41280, by rfl⟩) R82561
theorem R110083 : Reach 110083 := rs (se 1 (by rfl) ⟨82562, by rfl⟩) R165125
theorem R110099 : Reach 110099 := rs (se 1 (by rfl) ⟨82574, by rfl⟩) R165149
theorem R110129 : Reach 110129 := rs (se 2 (by rfl) ⟨41298, by rfl⟩) R82597
theorem R110147 : Reach 110147 := rs (se 1 (by rfl) ⟨82610, by rfl⟩) R165221
theorem R110177 : Reach 110177 := rs (se 2 (by rfl) ⟨41316, by rfl⟩) R82633
theorem R110195 : Reach 110195 := rs (se 1 (by rfl) ⟨82646, by rfl⟩) R165293
theorem R110225 : Reach 110225 := rs (se 2 (by rfl) ⟨41334, by rfl⟩) R82669
theorem R110243 : Reach 110243 := rs (se 1 (by rfl) ⟨82682, by rfl⟩) R165365
theorem R241325 : Reach 241325 := rs (se 3 (by rfl) ⟨45248, by rfl⟩) R90497
theorem R110273 : Reach 110273 := rs (se 2 (by rfl) ⟨41352, by rfl⟩) R82705
theorem R110291 : Reach 110291 := rs (se 1 (by rfl) ⟨82718, by rfl⟩) R165437
theorem R241379 : Reach 241379 := rs (se 1 (by rfl) ⟨181034, by rfl⟩) R362069
theorem R405233 : Reach 405233 := rs (se 2 (by rfl) ⟨151962, by rfl⟩) R303925
theorem R110321 : Reach 110321 := rs (se 2 (by rfl) ⟨41370, by rfl⟩) R82741
theorem R110339 : Reach 110339 := rs (se 1 (by rfl) ⟨82754, by rfl⟩) R165509
theorem R110369 : Reach 110369 := rs (se 2 (by rfl) ⟨41388, by rfl⟩) R82777
theorem R274211 : Reach 274211 := rs (se 1 (by rfl) ⟨205658, by rfl⟩) R411317
theorem R274225 : Reach 274225 := rs (se 2 (by rfl) ⟨102834, by rfl⟩) R205669
theorem R110387 : Reach 110387 := rs (se 1 (by rfl) ⟨82790, by rfl⟩) R165581
theorem R77635 : Reach 77635 := rs (se 1 (by rfl) ⟨58226, by rfl⟩) R116453
theorem R110417 : Reach 110417 := rs (se 2 (by rfl) ⟨41406, by rfl⟩) R82813
theorem R110435 : Reach 110435 := rs (se 1 (by rfl) ⟨82826, by rfl⟩) R165653
theorem R110465 : Reach 110465 := rs (se 2 (by rfl) ⟨41424, by rfl⟩) R82849
theorem R110483 : Reach 110483 := rs (se 1 (by rfl) ⟨82862, by rfl⟩) R165725
theorem R110497 : Reach 110497 := rs (se 2 (by rfl) ⟨41436, by rfl⟩) R82873
theorem R208813 : Reach 208813 := rs (se 3 (by rfl) ⟨39152, by rfl⟩) R78305
theorem R110513 : Reach 110513 := rs (se 2 (by rfl) ⟨41442, by rfl⟩) R82885
theorem R929717 : Reach 929717 := rs (se 5 (by rfl) ⟨43580, by rfl⟩) R87161
theorem R110531 : Reach 110531 := rs (se 1 (by rfl) ⟨82898, by rfl⟩) R165797
theorem R110561 : Reach 110561 := rs (se 2 (by rfl) ⟨41460, by rfl⟩) R82921
theorem R241649 : Reach 241649 := rs (se 2 (by rfl) ⟨90618, by rfl⟩) R181237
theorem R110579 : Reach 110579 := rs (se 1 (by rfl) ⟨82934, by rfl⟩) R165869
theorem R110609 : Reach 110609 := rs (se 2 (by rfl) ⟨41478, by rfl⟩) R82957
theorem R110627 : Reach 110627 := rs (se 1 (by rfl) ⟨82970, by rfl⟩) R165941
theorem R110657 : Reach 110657 := rs (se 2 (by rfl) ⟨41496, by rfl⟩) R82993
theorem R208973 : Reach 208973 := rs (se 3 (by rfl) ⟨39182, by rfl⟩) R78365
theorem R110675 : Reach 110675 := rs (se 1 (by rfl) ⟨83006, by rfl⟩) R166013
theorem R110705 : Reach 110705 := rs (se 2 (by rfl) ⟨41514, by rfl⟩) R83029
theorem R110723 : Reach 110723 := rs (se 1 (by rfl) ⟨83042, by rfl⟩) R166085
theorem R110753 : Reach 110753 := rs (se 2 (by rfl) ⟨41532, by rfl⟩) R83065
theorem R110771 : Reach 110771 := rs (se 1 (by rfl) ⟨83078, by rfl⟩) R166157
theorem R110801 : Reach 110801 := rs (se 2 (by rfl) ⟨41550, by rfl⟩) R83101
theorem R209123 : Reach 209123 := rs (se 1 (by rfl) ⟨156842, by rfl⟩) R313685
theorem R110819 : Reach 110819 := rs (se 1 (by rfl) ⟨83114, by rfl⟩) R166229
theorem R110849 : Reach 110849 := rs (se 2 (by rfl) ⟨41568, by rfl⟩) R83137
theorem R209155 : Reach 209155 := rs (se 1 (by rfl) ⟨156866, by rfl⟩) R313733
theorem R110867 : Reach 110867 := rs (se 1 (by rfl) ⟨83150, by rfl⟩) R166301
theorem R110897 : Reach 110897 := rs (se 2 (by rfl) ⟨41586, by rfl⟩) R83173
theorem R110915 : Reach 110915 := rs (se 1 (by rfl) ⟨83186, by rfl⟩) R166373
theorem R110945 : Reach 110945 := rs (se 2 (by rfl) ⟨41604, by rfl⟩) R83209
theorem R110963 : Reach 110963 := rs (se 1 (by rfl) ⟨83222, by rfl⟩) R166445
theorem R110993 : Reach 110993 := rs (se 2 (by rfl) ⟨41622, by rfl⟩) R83245
theorem R111011 : Reach 111011 := rs (se 1 (by rfl) ⟨83258, by rfl⟩) R166517
theorem R111041 : Reach 111041 := rs (se 2 (by rfl) ⟨41640, by rfl⟩) R83281
theorem R111059 : Reach 111059 := rs (se 1 (by rfl) ⟨83294, by rfl⟩) R166589
theorem R111089 : Reach 111089 := rs (se 2 (by rfl) ⟨41658, by rfl⟩) R83317
theorem R111107 : Reach 111107 := rs (se 1 (by rfl) ⟨83330, by rfl⟩) R166661
theorem R242189 : Reach 242189 := rs (se 3 (by rfl) ⟨45410, by rfl⟩) R90821
theorem R111137 : Reach 111137 := rs (se 2 (by rfl) ⟨41676, by rfl⟩) R83353
theorem R111155 : Reach 111155 := rs (se 1 (by rfl) ⟨83366, by rfl⟩) R166733
theorem R242243 : Reach 242243 := rs (se 1 (by rfl) ⟨181682, by rfl⟩) R363365
theorem R111185 : Reach 111185 := rs (se 2 (by rfl) ⟨41694, by rfl⟩) R83389
theorem R111203 : Reach 111203 := rs (se 1 (by rfl) ⟨83402, by rfl⟩) R166805
theorem R111233 : Reach 111233 := rs (se 2 (by rfl) ⟨41712, by rfl⟩) R83425
theorem R111251 : Reach 111251 := rs (se 1 (by rfl) ⟨83438, by rfl⟩) R166877
theorem R111281 : Reach 111281 := rs (se 2 (by rfl) ⟨41730, by rfl⟩) R83461
theorem R111299 : Reach 111299 := rs (se 1 (by rfl) ⟨83474, by rfl⟩) R166949
theorem R111329 : Reach 111329 := rs (se 2 (by rfl) ⟨41748, by rfl⟩) R83497
theorem R111347 : Reach 111347 := rs (se 1 (by rfl) ⟨83510, by rfl⟩) R167021
theorem R111377 : Reach 111377 := rs (se 2 (by rfl) ⟨41766, by rfl⟩) R83533
theorem R111395 : Reach 111395 := rs (se 1 (by rfl) ⟨83546, by rfl⟩) R167093
theorem R111425 : Reach 111425 := rs (se 2 (by rfl) ⟨41784, by rfl⟩) R83569
theorem R242513 : Reach 242513 := rs (se 2 (by rfl) ⟨90942, by rfl⟩) R181885
theorem R111443 : Reach 111443 := rs (se 1 (by rfl) ⟨83582, by rfl⟩) R167165
theorem R111473 : Reach 111473 := rs (se 2 (by rfl) ⟨41802, by rfl⟩) R83605
theorem R111491 : Reach 111491 := rs (se 1 (by rfl) ⟨83618, by rfl⟩) R167237
theorem R111521 : Reach 111521 := rs (se 2 (by rfl) ⟨41820, by rfl⟩) R83641
theorem R111539 : Reach 111539 := rs (se 1 (by rfl) ⟨83654, by rfl⟩) R167309
theorem R144337 : Reach 144337 := rs (se 2 (by rfl) ⟨54126, by rfl⟩) R108253
theorem R111569 : Reach 111569 := rs (se 2 (by rfl) ⟨41838, by rfl⟩) R83677
theorem R111587 : Reach 111587 := rs (se 1 (by rfl) ⟨83690, by rfl⟩) R167381
theorem R111617 : Reach 111617 := rs (se 2 (by rfl) ⟨41856, by rfl⟩) R83713
theorem R111635 : Reach 111635 := rs (se 1 (by rfl) ⟨83726, by rfl⟩) R167453
theorem R111665 : Reach 111665 := rs (se 2 (by rfl) ⟨41874, by rfl⟩) R83749
theorem R78899 : Reach 78899 := rs (se 1 (by rfl) ⟨59174, by rfl⟩) R118349
theorem R111683 : Reach 111683 := rs (se 1 (by rfl) ⟨83762, by rfl⟩) R167525
theorem R111713 : Reach 111713 := rs (se 2 (by rfl) ⟨41892, by rfl⟩) R83785
theorem R111731 : Reach 111731 := rs (se 1 (by rfl) ⟨83798, by rfl⟩) R167597
theorem R111761 : Reach 111761 := rs (se 2 (by rfl) ⟨41910, by rfl⟩) R83821
theorem R406691 : Reach 406691 := rs (se 1 (by rfl) ⟨305018, by rfl⟩) R610037
theorem R111779 : Reach 111779 := rs (se 1 (by rfl) ⟨83834, by rfl⟩) R167669
theorem R111809 : Reach 111809 := rs (se 2 (by rfl) ⟨41928, by rfl⟩) R83857
theorem R111827 : Reach 111827 := rs (se 1 (by rfl) ⟨83870, by rfl⟩) R167741
theorem R275683 : Reach 275683 := rs (se 1 (by rfl) ⟨206762, by rfl⟩) R413525
theorem R111857 : Reach 111857 := rs (se 2 (by rfl) ⟨41946, by rfl⟩) R83893
theorem R111875 : Reach 111875 := rs (se 1 (by rfl) ⟨83906, by rfl⟩) R167813
theorem R111905 : Reach 111905 := rs (se 2 (by rfl) ⟨41964, by rfl⟩) R83929
theorem R111923 : Reach 111923 := rs (se 1 (by rfl) ⟨83942, by rfl⟩) R167885
theorem R111953 : Reach 111953 := rs (se 2 (by rfl) ⟨41982, by rfl⟩) R83965
theorem R111971 : Reach 111971 := rs (se 1 (by rfl) ⟨83978, by rfl⟩) R167957
theorem R243053 : Reach 243053 := rs (se 3 (by rfl) ⟨45572, by rfl⟩) R91145
theorem R112001 : Reach 112001 := rs (se 2 (by rfl) ⟨42000, by rfl⟩) R84001
theorem R112019 : Reach 112019 := rs (se 1 (by rfl) ⟨84014, by rfl⟩) R168029
theorem R243107 : Reach 243107 := rs (se 1 (by rfl) ⟨182330, by rfl⟩) R364661
theorem R112049 : Reach 112049 := rs (se 2 (by rfl) ⟨42018, by rfl⟩) R84037
theorem R112067 : Reach 112067 := rs (se 1 (by rfl) ⟨84050, by rfl⟩) R168101
theorem R112097 : Reach 112097 := rs (se 2 (by rfl) ⟨42036, by rfl⟩) R84073
theorem R341489 : Reach 341489 := rs (se 2 (by rfl) ⟨128058, by rfl⟩) R256117
theorem R112115 : Reach 112115 := rs (se 1 (by rfl) ⟨84086, by rfl⟩) R168173
theorem R112145 : Reach 112145 := rs (se 2 (by rfl) ⟨42054, by rfl⟩) R84109
theorem R112163 : Reach 112163 := rs (se 1 (by rfl) ⟨84122, by rfl⟩) R168245
theorem R112193 : Reach 112193 := rs (se 2 (by rfl) ⟨42072, by rfl⟩) R84145
theorem R112211 : Reach 112211 := rs (se 1 (by rfl) ⟨84158, by rfl⟩) R168317
theorem R210545 : Reach 210545 := rs (se 2 (by rfl) ⟨78954, by rfl⟩) R157909
theorem R112241 : Reach 112241 := rs (se 2 (by rfl) ⟨42090, by rfl⟩) R84181
theorem R112259 : Reach 112259 := rs (se 1 (by rfl) ⟨84194, by rfl⟩) R168389
theorem R112289 : Reach 112289 := rs (se 2 (by rfl) ⟨42108, by rfl⟩) R84217
theorem R243377 : Reach 243377 := rs (se 2 (by rfl) ⟨91266, by rfl⟩) R182533
theorem R112307 : Reach 112307 := rs (se 1 (by rfl) ⟨84230, by rfl⟩) R168461
theorem R112337 : Reach 112337 := rs (se 2 (by rfl) ⟨42126, by rfl⟩) R84253
theorem R112355 : Reach 112355 := rs (se 1 (by rfl) ⟨84266, by rfl⟩) R168533
theorem R112385 : Reach 112385 := rs (se 2 (by rfl) ⟨42144, by rfl⟩) R84289
theorem R112403 : Reach 112403 := rs (se 1 (by rfl) ⟨84302, by rfl⟩) R168605
theorem R79651 : Reach 79651 := rs (se 1 (by rfl) ⟨59738, by rfl⟩) R119477
theorem R112433 : Reach 112433 := rs (se 2 (by rfl) ⟨42162, by rfl⟩) R84325
theorem R112451 : Reach 112451 := rs (se 1 (by rfl) ⟨84338, by rfl⟩) R168677
theorem R112481 : Reach 112481 := rs (se 2 (by rfl) ⟨42180, by rfl⟩) R84361
theorem R112499 : Reach 112499 := rs (se 1 (by rfl) ⟨84374, by rfl⟩) R168749
theorem R112529 : Reach 112529 := rs (se 2 (by rfl) ⟨42198, by rfl⟩) R84397
theorem R112547 : Reach 112547 := rs (se 1 (by rfl) ⟨84410, by rfl⟩) R168821
theorem R374705 : Reach 374705 := rs (se 2 (by rfl) ⟨140514, by rfl⟩) R281029
theorem R112577 : Reach 112577 := rs (se 2 (by rfl) ⟨42216, by rfl⟩) R84433
theorem R112595 : Reach 112595 := rs (se 1 (by rfl) ⟨84446, by rfl⟩) R168893
theorem R538595 : Reach 538595 := rs (se 1 (by rfl) ⟨403946, by rfl⟩) R807893
theorem R178147 : Reach 178147 := rs (se 1 (by rfl) ⟨133610, by rfl⟩) R267221
theorem R112625 : Reach 112625 := rs (se 2 (by rfl) ⟨42234, by rfl⟩) R84469
theorem R112643 : Reach 112643 := rs (se 1 (by rfl) ⟨84482, by rfl⟩) R168965
theorem R112673 : Reach 112673 := rs (se 2 (by rfl) ⟨42252, by rfl⟩) R84505
theorem R407693 : Reach 407693 := rs (se 3 (by rfl) ⟨76442, by rfl⟩) R152885
theorem R178321 : Reach 178321 := rs (se 2 (by rfl) ⟨66870, by rfl⟩) R133741
theorem R243917 : Reach 243917 := rs (se 3 (by rfl) ⟨45734, by rfl⟩) R91469
theorem R80131 : Reach 80131 := rs (se 1 (by rfl) ⟨60098, by rfl⟩) R120197
theorem R243971 : Reach 243971 := rs (se 1 (by rfl) ⟨182978, by rfl⟩) R365957
theorem R899381 : Reach 899381 := rs (se 5 (by rfl) ⟨42158, by rfl⟩) R84317
theorem R80275 : Reach 80275 := rs (se 1 (by rfl) ⟨60206, by rfl⟩) R120413
theorem R244241 : Reach 244241 := rs (se 2 (by rfl) ⟨91590, by rfl⟩) R183181
theorem R80419 : Reach 80419 := rs (se 1 (by rfl) ⟨60314, by rfl⟩) R120629
theorem R211501 : Reach 211501 := rs (se 3 (by rfl) ⟨39656, by rfl⟩) R79313
theorem R80563 : Reach 80563 := rs (se 1 (by rfl) ⟨60422, by rfl⟩) R120845
theorem R211729 : Reach 211729 := rs (se 2 (by rfl) ⟨79398, by rfl⟩) R158797
theorem R80707 : Reach 80707 := rs (se 1 (by rfl) ⟨60530, by rfl⟩) R121061
theorem R211889 : Reach 211889 := rs (se 2 (by rfl) ⟨79458, by rfl⟩) R158917
theorem R80851 : Reach 80851 := rs (se 1 (by rfl) ⟨60638, by rfl⟩) R121277
theorem R212003 : Reach 212003 := rs (se 1 (by rfl) ⟨159002, by rfl⟩) R318005
theorem R244781 : Reach 244781 := rs (se 3 (by rfl) ⟨45896, by rfl⟩) R91793
theorem R80995 : Reach 80995 := rs (se 1 (by rfl) ⟨60746, by rfl⟩) R121493
theorem R244835 : Reach 244835 := rs (se 1 (by rfl) ⟨183626, by rfl⟩) R367253
theorem R113891 : Reach 113891 := rs (se 1 (by rfl) ⟨85418, by rfl⟩) R170837
theorem R81139 : Reach 81139 := rs (se 1 (by rfl) ⟨60854, by rfl⟩) R121709
theorem R376163 : Reach 376163 := rs (se 1 (by rfl) ⟨282122, by rfl⟩) R564245
theorem R245105 : Reach 245105 := rs (se 2 (by rfl) ⟨91914, by rfl⟩) R183829
theorem R114049 : Reach 114049 := rs (se 2 (by rfl) ⟨42768, by rfl⟩) R85537
theorem R81283 : Reach 81283 := rs (se 1 (by rfl) ⟨60962, by rfl⟩) R121925
theorem R277901 : Reach 277901 := rs (se 3 (by rfl) ⟨52106, by rfl⟩) R104213
theorem R310691 : Reach 310691 := rs (se 1 (by rfl) ⟨233018, by rfl⟩) R466037
theorem R81427 : Reach 81427 := rs (se 1 (by rfl) ⟨61070, by rfl⟩) R122141
theorem R1064501 : Reach 1064501 := rs (se 5 (by rfl) ⟨49898, by rfl⟩) R99797
theorem R114305 : Reach 114305 := rs (se 2 (by rfl) ⟨42864, by rfl⟩) R85729
theorem R245389 : Reach 245389 := rs (se 3 (by rfl) ⟨46010, by rfl⟩) R92021
theorem R81571 : Reach 81571 := rs (se 1 (by rfl) ⟨61178, by rfl⟩) R122357
theorem R81715 : Reach 81715 := rs (se 1 (by rfl) ⟨61286, by rfl⟩) R122573
theorem R245645 : Reach 245645 := rs (se 3 (by rfl) ⟨46058, by rfl⟩) R92117
theorem R81859 : Reach 81859 := rs (se 1 (by rfl) ⟨61394, by rfl⟩) R122789
theorem R245699 : Reach 245699 := rs (se 1 (by rfl) ⟨184274, by rfl⟩) R368549
theorem R81923 : Reach 81923 := rs (se 1 (by rfl) ⟨61442, by rfl⟩) R122885
theorem R213005 : Reach 213005 := rs (se 3 (by rfl) ⟨39938, by rfl⟩) R79877
theorem R82003 : Reach 82003 := rs (se 1 (by rfl) ⟨61502, by rfl⟩) R123005
theorem R376973 : Reach 376973 := rs (se 3 (by rfl) ⟨70682, by rfl⟩) R141365
theorem R82115 : Reach 82115 := rs (se 1 (by rfl) ⟨61586, by rfl⟩) R123173
theorem R213187 : Reach 213187 := rs (se 1 (by rfl) ⟨159890, by rfl⟩) R319781
theorem R245969 : Reach 245969 := rs (se 2 (by rfl) ⟨92238, by rfl⟩) R184477
theorem R82147 : Reach 82147 := rs (se 1 (by rfl) ⟨61610, by rfl⟩) R123221
theorem R475469 : Reach 475469 := rs (se 3 (by rfl) ⟨89150, by rfl⟩) R178301
theorem R213347 : Reach 213347 := rs (se 1 (by rfl) ⟨160010, by rfl⟩) R320021
theorem R82291 : Reach 82291 := rs (se 1 (by rfl) ⟨61718, by rfl⟩) R123437
theorem R82435 : Reach 82435 := rs (se 1 (by rfl) ⟨61826, by rfl⟩) R123653
theorem R311921 : Reach 311921 := rs (se 2 (by rfl) ⟨116970, by rfl⟩) R233941
theorem R82579 : Reach 82579 := rs (se 1 (by rfl) ⟨61934, by rfl⟩) R123869
theorem R180913 : Reach 180913 := rs (se 2 (by rfl) ⟨67842, by rfl⟩) R135685
theorem R246509 : Reach 246509 := rs (se 3 (by rfl) ⟨46220, by rfl⟩) R92441
theorem R246563 : Reach 246563 := rs (se 1 (by rfl) ⟨184922, by rfl⟩) R369845
theorem R82723 : Reach 82723 := rs (se 1 (by rfl) ⟨62042, by rfl⟩) R124085
theorem R82867 : Reach 82867 := rs (se 1 (by rfl) ⟨62150, by rfl⟩) R124301
theorem R181187 : Reach 181187 := rs (se 1 (by rfl) ⟨135890, by rfl⟩) R271781
theorem R639971 : Reach 639971 := rs (se 1 (by rfl) ⟨479978, by rfl⟩) R959957
theorem R410609 : Reach 410609 := rs (se 2 (by rfl) ⟨153978, by rfl⟩) R307957
theorem R115715 : Reach 115715 := rs (se 1 (by rfl) ⟨86786, by rfl⟩) R173573
theorem R246833 : Reach 246833 := rs (se 2 (by rfl) ⟨92562, by rfl⟩) R185125
theorem R148529 : Reach 148529 := rs (se 2 (by rfl) ⟨55698, by rfl⟩) R111397
theorem R83011 : Reach 83011 := rs (se 1 (by rfl) ⟨62258, by rfl⟩) R124517
theorem R312419 : Reach 312419 := rs (se 1 (by rfl) ⟨234314, by rfl⟩) R468629
theorem R181379 : Reach 181379 := rs (se 1 (by rfl) ⟨136034, by rfl⟩) R272069
theorem R83155 : Reach 83155 := rs (se 1 (by rfl) ⟨62366, by rfl⟩) R124733
theorem R443717 : Reach 443717 := rs (se 4 (by rfl) ⟨41598, by rfl⟩) R83197
theorem R83299 : Reach 83299 := rs (se 1 (by rfl) ⟨62474, by rfl⟩) R124949
theorem R83443 : Reach 83443 := rs (se 1 (by rfl) ⟨62582, by rfl⟩) R125165
theorem R247373 : Reach 247373 := rs (se 3 (by rfl) ⟨46382, by rfl⟩) R92765
theorem R247427 : Reach 247427 := rs (se 1 (by rfl) ⟨185570, by rfl⟩) R371141
theorem R83587 : Reach 83587 := rs (se 1 (by rfl) ⟨62690, by rfl⟩) R125381
theorem R476869 : Reach 476869 := rs (se 4 (by rfl) ⟨44706, by rfl⟩) R89413
theorem R83731 : Reach 83731 := rs (se 1 (by rfl) ⟨62798, by rfl⟩) R125597
theorem R116561 : Reach 116561 := rs (se 2 (by rfl) ⟨43710, by rfl⟩) R87421
theorem R247697 : Reach 247697 := rs (se 2 (by rfl) ⟨92886, by rfl⟩) R185773
theorem R83875 : Reach 83875 := rs (se 1 (by rfl) ⟨62906, by rfl⟩) R125813
theorem R182321 : Reach 182321 := rs (se 2 (by rfl) ⟨68370, by rfl⟩) R136741
theorem R84019 : Reach 84019 := rs (se 1 (by rfl) ⟨63014, by rfl⟩) R126029
theorem R215117 : Reach 215117 := rs (se 3 (by rfl) ⟨40334, by rfl⟩) R80669
theorem R182371 : Reach 182371 := rs (se 1 (by rfl) ⟨136778, by rfl⟩) R273557
theorem R542861 : Reach 542861 := rs (se 3 (by rfl) ⟨101786, by rfl⟩) R203573
theorem R149681 : Reach 149681 := rs (se 2 (by rfl) ⟨56130, by rfl⟩) R112261
theorem R84163 : Reach 84163 := rs (se 1 (by rfl) ⟨63122, by rfl⟩) R126245
theorem R215245 : Reach 215245 := rs (se 3 (by rfl) ⟨40358, by rfl⟩) R80717
theorem R182513 : Reach 182513 := rs (se 2 (by rfl) ⟨68442, by rfl⟩) R136885
theorem R280817 : Reach 280817 := rs (se 2 (by rfl) ⟨105306, by rfl⟩) R210613
theorem R117011 : Reach 117011 := rs (se 1 (by rfl) ⟨87758, by rfl⟩) R175517
theorem R117073 : Reach 117073 := rs (se 2 (by rfl) ⟨43902, by rfl⟩) R87805
theorem R84307 : Reach 84307 := rs (se 1 (by rfl) ⟨63230, by rfl⟩) R126461
theorem R412067 : Reach 412067 := rs (se 1 (by rfl) ⟨309050, by rfl⟩) R618101
theorem R248237 : Reach 248237 := rs (se 3 (by rfl) ⟨46544, by rfl⟩) R93089
theorem R1034693 : Reach 1034693 := rs (se 4 (by rfl) ⟨97002, by rfl⟩) R194005
theorem R1329605 : Reach 1329605 := rs (se 4 (by rfl) ⟨124650, by rfl⟩) R249301
theorem R248291 : Reach 248291 := rs (se 1 (by rfl) ⟨186218, by rfl⟩) R372437
theorem R84451 : Reach 84451 := rs (se 1 (by rfl) ⟨63338, by rfl⟩) R126677
theorem R84547 : Reach 84547 := rs (se 1 (by rfl) ⟨63410, by rfl⟩) R126821
theorem R248561 : Reach 248561 := rs (se 2 (by rfl) ⟨93210, by rfl⟩) R186421
theorem R117683 : Reach 117683 := rs (se 1 (by rfl) ⟨88262, by rfl⟩) R176525
theorem R379889 : Reach 379889 := rs (se 2 (by rfl) ⟨142458, by rfl⟩) R284917
theorem R248845 : Reach 248845 := rs (se 3 (by rfl) ⟨46658, by rfl⟩) R93317
theorem R314381 : Reach 314381 := rs (se 3 (by rfl) ⟨58946, by rfl⟩) R117893
theorem R183505 : Reach 183505 := rs (se 2 (by rfl) ⟨68814, by rfl⟩) R137629
theorem R5950691 : Reach 5950691 := rs (se 1 (by rfl) ⟨4463018, by rfl⟩) R8926037
theorem R249101 : Reach 249101 := rs (se 3 (by rfl) ⟨46706, by rfl⟩) R93413
theorem R249155 : Reach 249155 := rs (se 1 (by rfl) ⟨186866, by rfl⟩) R373733
theorem R249293 : Reach 249293 := rs (se 3 (by rfl) ⟨46742, by rfl⟩) R93485
theorem R183779 : Reach 183779 := rs (se 1 (by rfl) ⟨137834, by rfl⟩) R275669
theorem R151025 : Reach 151025 := rs (se 2 (by rfl) ⟨56634, by rfl⟩) R113269
theorem R249425 : Reach 249425 := rs (se 2 (by rfl) ⟨93534, by rfl⟩) R187069
theorem R183971 : Reach 183971 := rs (se 1 (by rfl) ⟨137978, by rfl⟩) R275957
theorem R282275 : Reach 282275 := rs (se 1 (by rfl) ⟨211706, by rfl⟩) R423413
theorem R1199843 : Reach 1199843 := rs (se 1 (by rfl) ⟨899882, by rfl⟩) R1799765
theorem R118675 : Reach 118675 := rs (se 1 (by rfl) ⟨89006, by rfl⟩) R178013
theorem R348067 : Reach 348067 := rs (se 1 (by rfl) ⟨261050, by rfl⟩) R522101
theorem R249965 : Reach 249965 := rs (se 3 (by rfl) ⟨46868, by rfl⟩) R93737
theorem R250019 : Reach 250019 := rs (se 1 (by rfl) ⟨187514, by rfl⟩) R375029
theorem R1069283 : Reach 1069283 := rs (se 1 (by rfl) ⟨801962, by rfl⟩) R1603925
theorem R479621 : Reach 479621 := rs (se 4 (by rfl) ⟨44964, by rfl⟩) R89929
theorem R250289 : Reach 250289 := rs (se 2 (by rfl) ⟨93858, by rfl⟩) R187717
theorem R184913 : Reach 184913 := rs (se 2 (by rfl) ⟨69342, by rfl⟩) R138685
theorem R184963 : Reach 184963 := rs (se 1 (by rfl) ⟨138722, by rfl⟩) R277445
theorem R283277 : Reach 283277 := rs (se 3 (by rfl) ⟨53114, by rfl⟩) R106229
theorem R185105 : Reach 185105 := rs (se 2 (by rfl) ⟨69414, by rfl⟩) R138829
theorem R119585 : Reach 119585 := rs (se 2 (by rfl) ⟨44844, by rfl⟩) R89689
theorem R119713 : Reach 119713 := rs (se 2 (by rfl) ⟨44892, by rfl⟩) R89785
theorem R250829 : Reach 250829 := rs (se 3 (by rfl) ⟨47030, by rfl⟩) R94061
theorem R545777 : Reach 545777 := rs (se 2 (by rfl) ⟨204666, by rfl⟩) R409333
theorem R250883 : Reach 250883 := rs (se 1 (by rfl) ⟨188162, by rfl⟩) R376325
theorem R120035 : Reach 120035 := rs (se 1 (by rfl) ⟨90026, by rfl⟩) R180053
theorem R251153 : Reach 251153 := rs (se 2 (by rfl) ⟨94182, by rfl⟩) R188365
theorem R120163 : Reach 120163 := rs (se 1 (by rfl) ⟨90122, by rfl⟩) R180245
theorem R120305 : Reach 120305 := rs (se 2 (by rfl) ⟨45114, by rfl⟩) R90229
theorem R218659 : Reach 218659 := rs (se 1 (by rfl) ⟨163994, by rfl⟩) R327989
theorem R120433 : Reach 120433 := rs (se 2 (by rfl) ⟨45162, by rfl⟩) R90325
theorem R120467 : Reach 120467 := rs (se 1 (by rfl) ⟨90350, by rfl⟩) R180701
theorem R218801 : Reach 218801 := rs (se 2 (by rfl) ⟨82050, by rfl⟩) R164101
theorem R186097 : Reach 186097 := rs (se 2 (by rfl) ⟨69786, by rfl⟩) R139573
theorem R120595 : Reach 120595 := rs (se 1 (by rfl) ⟨90446, by rfl⟩) R180893
theorem R251693 : Reach 251693 := rs (se 3 (by rfl) ⟨47192, by rfl⟩) R94385
theorem R251747 : Reach 251747 := rs (se 1 (by rfl) ⟨188810, by rfl⟩) R377621
theorem R120737 : Reach 120737 := rs (se 2 (by rfl) ⟨45276, by rfl⟩) R90553
theorem R186371 : Reach 186371 := rs (se 1 (by rfl) ⟨139778, by rfl⟩) R279557
theorem R120865 : Reach 120865 := rs (se 2 (by rfl) ⟨45324, by rfl⟩) R90649
theorem R120899 : Reach 120899 := rs (se 1 (by rfl) ⟨90674, by rfl⟩) R181349
theorem R252017 : Reach 252017 := rs (se 2 (by rfl) ⟨94506, by rfl⟩) R189013
theorem R88195 : Reach 88195 := rs (se 1 (by rfl) ⟨66146, by rfl⟩) R132293
theorem R121027 : Reach 121027 := rs (se 1 (by rfl) ⟨90770, by rfl⟩) R181541
theorem R186563 : Reach 186563 := rs (se 1 (by rfl) ⟨139922, by rfl⟩) R279845
theorem R252227 : Reach 252227 := rs (se 1 (by rfl) ⟨189170, by rfl⟩) R378341
theorem R121169 : Reach 121169 := rs (se 2 (by rfl) ⟨45438, by rfl⟩) R90877
theorem R121297 : Reach 121297 := rs (se 2 (by rfl) ⟨45486, by rfl⟩) R90973
theorem R121331 : Reach 121331 := rs (se 1 (by rfl) ⟨90998, by rfl⟩) R181997
theorem R121459 : Reach 121459 := rs (se 1 (by rfl) ⟨91094, by rfl⟩) R182189
theorem R252557 : Reach 252557 := rs (se 3 (by rfl) ⟨47354, by rfl⟩) R94709
theorem R252611 : Reach 252611 := rs (se 1 (by rfl) ⟨189458, by rfl⟩) R378917
theorem R121601 : Reach 121601 := rs (se 2 (by rfl) ⟨45600, by rfl⟩) R91201
theorem R1334069 : Reach 1334069 := rs (se 5 (by rfl) ⟨62534, by rfl⟩) R125069
theorem R121729 : Reach 121729 := rs (se 2 (by rfl) ⟨45648, by rfl⟩) R91297
theorem R121763 : Reach 121763 := rs (se 1 (by rfl) ⟨91322, by rfl⟩) R182645
theorem R252881 : Reach 252881 := rs (se 2 (by rfl) ⟨94830, by rfl⟩) R189661
theorem R842723 : Reach 842723 := rs (se 1 (by rfl) ⟨632042, by rfl⟩) R1264085
theorem R908273 : Reach 908273 := rs (se 2 (by rfl) ⟨340602, by rfl⟩) R681205
theorem R711665 : Reach 711665 := rs (se 2 (by rfl) ⟨266874, by rfl⟩) R533749
theorem R121891 : Reach 121891 := rs (se 1 (by rfl) ⟨91418, by rfl⟩) R182837
theorem R154723 : Reach 154723 := rs (se 1 (by rfl) ⟨116042, by rfl⟩) R232085
theorem R187505 : Reach 187505 := rs (se 2 (by rfl) ⟨70314, by rfl⟩) R140629
theorem R351373 : Reach 351373 := rs (se 3 (by rfl) ⟨65882, by rfl⟩) R131765
theorem R187555 : Reach 187555 := rs (se 1 (by rfl) ⟨140666, by rfl⟩) R281333
theorem R122033 : Reach 122033 := rs (se 2 (by rfl) ⟨45762, by rfl⟩) R91525
theorem R318755 : Reach 318755 := rs (se 1 (by rfl) ⟨239066, by rfl⟩) R478133
theorem R122161 : Reach 122161 := rs (se 2 (by rfl) ⟨45810, by rfl⟩) R91621
theorem R187697 : Reach 187697 := rs (se 2 (by rfl) ⟨70386, by rfl⟩) R140773
theorem R220483 : Reach 220483 := rs (se 1 (by rfl) ⟨165362, by rfl⟩) R330725
theorem R122195 : Reach 122195 := rs (se 1 (by rfl) ⟨91646, by rfl⟩) R183293
theorem R122323 : Reach 122323 := rs (se 1 (by rfl) ⟨91742, by rfl⟩) R183485
theorem R253475 : Reach 253475 := rs (se 1 (by rfl) ⟨190106, by rfl⟩) R380213
theorem R122465 : Reach 122465 := rs (se 2 (by rfl) ⟨45924, by rfl⟩) R91849
theorem R122593 : Reach 122593 := rs (se 2 (by rfl) ⟨45972, by rfl⟩) R91945
theorem R351971 : Reach 351971 := rs (se 1 (by rfl) ⟨263978, by rfl⟩) R527957
theorem R122627 : Reach 122627 := rs (se 1 (by rfl) ⟨91970, by rfl⟩) R183941
theorem R122755 : Reach 122755 := rs (se 1 (by rfl) ⟨92066, by rfl⟩) R184133
theorem R90067 : Reach 90067 := rs (se 1 (by rfl) ⟨67550, by rfl⟩) R135101
theorem R90083 : Reach 90083 := rs (se 1 (by rfl) ⟨67562, by rfl⟩) R135125
theorem R122897 : Reach 122897 := rs (se 2 (by rfl) ⟨46086, by rfl⟩) R92173
theorem R90163 : Reach 90163 := rs (se 1 (by rfl) ⟨67622, by rfl⟩) R135245
theorem R123025 : Reach 123025 := rs (se 2 (by rfl) ⟨46134, by rfl⟩) R92269
theorem R123059 : Reach 123059 := rs (se 1 (by rfl) ⟨92294, by rfl⟩) R184589
theorem R778481 : Reach 778481 := rs (se 2 (by rfl) ⟨291930, by rfl⟩) R583861
theorem R188689 : Reach 188689 := rs (se 2 (by rfl) ⟨70758, by rfl⟩) R141517
theorem R123187 : Reach 123187 := rs (se 1 (by rfl) ⟨92390, by rfl⟩) R184781
theorem R483725 : Reach 483725 := rs (se 3 (by rfl) ⟨90698, by rfl⟩) R181397
theorem R123329 : Reach 123329 := rs (se 2 (by rfl) ⟨46248, by rfl⟩) R92497
theorem R123377 : Reach 123377 := rs (se 2 (by rfl) ⟨46266, by rfl⟩) R92533
theorem R90659 : Reach 90659 := rs (se 1 (by rfl) ⟨67994, by rfl⟩) R135989
theorem R188963 : Reach 188963 := rs (se 1 (by rfl) ⟨141722, by rfl⟩) R283445
theorem R123457 : Reach 123457 := rs (se 2 (by rfl) ⟨46296, by rfl⟩) R92593
theorem R90691 : Reach 90691 := rs (se 1 (by rfl) ⟨68018, by rfl⟩) R136037
theorem R123491 : Reach 123491 := rs (se 1 (by rfl) ⟨92618, by rfl⟩) R185237
theorem R713357 : Reach 713357 := rs (se 3 (by rfl) ⟨133754, by rfl⟩) R267509
theorem R123619 : Reach 123619 := rs (se 1 (by rfl) ⟨92714, by rfl⟩) R185429
theorem R189155 : Reach 189155 := rs (se 1 (by rfl) ⟨141866, by rfl⟩) R283733
theorem R123761 : Reach 123761 := rs (se 2 (by rfl) ⟨46410, by rfl⟩) R92821
theorem R156593 : Reach 156593 := rs (se 2 (by rfl) ⟨58722, by rfl⟩) R117445
theorem R123889 : Reach 123889 := rs (se 2 (by rfl) ⟨46458, by rfl⟩) R92917
theorem R615437 : Reach 615437 := rs (se 3 (by rfl) ⟨115394, by rfl⟩) R230789
theorem R123923 : Reach 123923 := rs (se 1 (by rfl) ⟨92942, by rfl⟩) R185885
theorem R124051 : Reach 124051 := rs (se 1 (by rfl) ⟨93038, by rfl⟩) R186077
theorem R91363 : Reach 91363 := rs (se 1 (by rfl) ⟨68522, by rfl⟩) R137045
theorem R124193 : Reach 124193 := rs (se 2 (by rfl) ⟨46572, by rfl⟩) R93145
theorem R91459 : Reach 91459 := rs (se 1 (by rfl) ⟨68594, by rfl⟩) R137189
theorem R189773 : Reach 189773 := rs (se 3 (by rfl) ⟨35582, by rfl⟩) R71165
theorem R124321 : Reach 124321 := rs (se 2 (by rfl) ⟨46620, by rfl⟩) R93241
theorem R124337 : Reach 124337 := rs (se 2 (by rfl) ⟨46626, by rfl⟩) R93253
theorem R124355 : Reach 124355 := rs (se 1 (by rfl) ⟨93266, by rfl⟩) R186533
theorem R189965 : Reach 189965 := rs (se 3 (by rfl) ⟨35618, by rfl⟩) R71237
theorem R124483 : Reach 124483 := rs (se 1 (by rfl) ⟨93362, by rfl⟩) R186725
theorem R190097 : Reach 190097 := rs (se 2 (by rfl) ⟨71286, by rfl⟩) R142573
theorem R91795 : Reach 91795 := rs (se 1 (by rfl) ⟨68846, by rfl⟩) R137693
theorem R190147 : Reach 190147 := rs (se 1 (by rfl) ⟨142610, by rfl⟩) R285221
theorem R124625 : Reach 124625 := rs (se 2 (by rfl) ⟨46734, by rfl⟩) R93469
theorem R157457 : Reach 157457 := rs (se 2 (by rfl) ⟨59046, by rfl⟩) R118093
theorem R91955 : Reach 91955 := rs (se 1 (by rfl) ⟨68966, by rfl⟩) R137933
theorem R124753 : Reach 124753 := rs (se 2 (by rfl) ⟨46782, by rfl⟩) R93565
theorem R124787 : Reach 124787 := rs (se 1 (by rfl) ⟨93590, by rfl⟩) R187181
theorem R124915 : Reach 124915 := rs (se 1 (by rfl) ⟨93686, by rfl⟩) R187373
theorem R125057 : Reach 125057 := rs (se 2 (by rfl) ⟨46896, by rfl⟩) R93793
theorem R125185 : Reach 125185 := rs (se 2 (by rfl) ⟨46944, by rfl⟩) R93889
theorem R387341 : Reach 387341 := rs (se 3 (by rfl) ⟨72626, by rfl⟩) R145253
theorem R125219 : Reach 125219 := rs (se 1 (by rfl) ⟨93914, by rfl⟩) R187829
theorem R125347 : Reach 125347 := rs (se 1 (by rfl) ⟨94010, by rfl⟩) R188021
theorem R92659 : Reach 92659 := rs (se 1 (by rfl) ⟨69494, by rfl⟩) R138989
theorem R125489 : Reach 125489 := rs (se 2 (by rfl) ⟨47058, by rfl⟩) R94117
theorem R92755 : Reach 92755 := rs (se 1 (by rfl) ⟨69566, by rfl⟩) R139133
theorem R289379 : Reach 289379 := rs (se 1 (by rfl) ⟨217034, by rfl⟩) R434069
theorem R125617 : Reach 125617 := rs (se 2 (by rfl) ⟨47106, by rfl⟩) R94213
theorem R125651 : Reach 125651 := rs (se 1 (by rfl) ⟨94238, by rfl⟩) R188477
theorem R453347 : Reach 453347 := rs (se 1 (by rfl) ⟨340010, by rfl⟩) R680021
theorem R125779 : Reach 125779 := rs (se 1 (by rfl) ⟨94334, by rfl⟩) R188669
theorem R125921 : Reach 125921 := rs (se 2 (by rfl) ⟨47220, by rfl⟩) R94441
theorem R158755 : Reach 158755 := rs (se 1 (by rfl) ⟨119066, by rfl⟩) R238133
theorem R93251 : Reach 93251 := rs (se 1 (by rfl) ⟨69938, by rfl⟩) R139877
theorem R453709 : Reach 453709 := rs (se 3 (by rfl) ⟨85070, by rfl⟩) R170141
theorem R126049 : Reach 126049 := rs (se 2 (by rfl) ⟨47268, by rfl⟩) R94537
theorem R126083 : Reach 126083 := rs (se 1 (by rfl) ⟨94562, by rfl⟩) R189125
theorem R420997 : Reach 420997 := rs (se 4 (by rfl) ⟨39468, by rfl⟩) R78937
theorem R126211 : Reach 126211 := rs (se 1 (by rfl) ⟨94658, by rfl⟩) R189317
theorem R388421 : Reach 388421 := rs (se 4 (by rfl) ⟨36414, by rfl⟩) R72829
theorem R355661 : Reach 355661 := rs (se 3 (by rfl) ⟨66686, by rfl⟩) R133373
theorem R617827 : Reach 617827 := rs (se 1 (by rfl) ⟨463370, by rfl⟩) R926741
theorem R126353 : Reach 126353 := rs (se 2 (by rfl) ⟨47382, by rfl⟩) R94765
theorem R224689 : Reach 224689 := rs (se 2 (by rfl) ⟨84258, by rfl⟩) R168517
theorem R126481 : Reach 126481 := rs (se 2 (by rfl) ⟨47430, by rfl⟩) R94861
theorem R454243 : Reach 454243 := rs (se 1 (by rfl) ⟨340682, by rfl⟩) R681365
theorem R93955 : Reach 93955 := rs (se 1 (by rfl) ⟨70466, by rfl⟩) R140933
theorem R94051 : Reach 94051 := rs (se 1 (by rfl) ⟨70538, by rfl⟩) R141077
theorem R159985 : Reach 159985 := rs (se 2 (by rfl) ⟨59994, by rfl⟩) R119989
theorem R94547 : Reach 94547 := rs (se 1 (by rfl) ⟨70910, by rfl⟩) R141821
theorem R160145 : Reach 160145 := rs (se 2 (by rfl) ⟨60054, by rfl⟩) R120109
theorem R160163 : Reach 160163 := rs (se 1 (by rfl) ⟨120122, by rfl⟩) R240245
theorem R488035 : Reach 488035 := rs (se 1 (by rfl) ⟨366026, by rfl⟩) R732053
theorem R160433 : Reach 160433 := rs (se 2 (by rfl) ⟨60162, by rfl⟩) R120325
theorem R160451 : Reach 160451 := rs (se 1 (by rfl) ⟨120338, by rfl⟩) R240677
theorem R488369 : Reach 488369 := rs (se 2 (by rfl) ⟨183138, by rfl⟩) R366277
theorem R127921 : Reach 127921 := rs (se 2 (by rfl) ⟨47970, by rfl⟩) R95941
theorem R160721 : Reach 160721 := rs (se 2 (by rfl) ⟨60270, by rfl⟩) R120541
theorem R160739 : Reach 160739 := rs (se 1 (by rfl) ⟨120554, by rfl⟩) R241109
theorem R422981 : Reach 422981 := rs (se 4 (by rfl) ⟨39654, by rfl⟩) R79309
theorem R390277 : Reach 390277 := rs (se 4 (by rfl) ⟨36588, by rfl⟩) R73177
theorem R193745 : Reach 193745 := rs (se 2 (by rfl) ⟨72654, by rfl⟩) R145309
theorem R161009 : Reach 161009 := rs (se 2 (by rfl) ⟨60378, by rfl⟩) R120757
theorem R161027 : Reach 161027 := rs (se 1 (by rfl) ⟨120770, by rfl⟩) R241541
theorem R521585 : Reach 521585 := rs (se 2 (by rfl) ⟨195594, by rfl⟩) R391189
theorem R128483 : Reach 128483 := rs (se 1 (by rfl) ⟨96362, by rfl⟩) R192725
theorem R161297 : Reach 161297 := rs (se 2 (by rfl) ⟨60486, by rfl⟩) R120973
theorem R161315 : Reach 161315 := rs (se 1 (by rfl) ⟨120986, by rfl⟩) R241973
theorem R161585 : Reach 161585 := rs (se 2 (by rfl) ⟨60594, by rfl⟩) R121189
theorem R161603 : Reach 161603 := rs (se 1 (by rfl) ⟨121202, by rfl⟩) R242405
theorem R718733 : Reach 718733 := rs (se 3 (by rfl) ⟨134762, by rfl⟩) R269525
theorem R161873 : Reach 161873 := rs (se 2 (by rfl) ⟨60702, by rfl⟩) R121405
theorem R161891 : Reach 161891 := rs (se 1 (by rfl) ⟨121418, by rfl⟩) R242837
theorem R162161 : Reach 162161 := rs (se 2 (by rfl) ⟨60810, by rfl⟩) R121621
theorem R162179 : Reach 162179 := rs (se 1 (by rfl) ⟨121634, by rfl⟩) R243269
theorem R195053 : Reach 195053 := rs (se 3 (by rfl) ⟨36572, by rfl⟩) R73145
theorem R293489 : Reach 293489 := rs (se 2 (by rfl) ⟨110058, by rfl⟩) R220117
theorem R260749 : Reach 260749 := rs (se 3 (by rfl) ⟨48890, by rfl⟩) R97781
theorem R162449 : Reach 162449 := rs (se 2 (by rfl) ⟨60918, by rfl⟩) R121837
theorem R162467 : Reach 162467 := rs (se 1 (by rfl) ⟨121850, by rfl⟩) R243701
theorem R588485 : Reach 588485 := rs (se 4 (by rfl) ⟨55170, by rfl⟩) R110341
theorem R162737 : Reach 162737 := rs (se 2 (by rfl) ⟨61026, by rfl⟩) R122053
theorem R97219 : Reach 97219 := rs (se 1 (by rfl) ⟨72914, by rfl⟩) R145829
theorem R162755 : Reach 162755 := rs (se 1 (by rfl) ⟨122066, by rfl⟩) R244133
theorem R163025 : Reach 163025 := rs (se 2 (by rfl) ⟨61134, by rfl⟩) R122269
theorem R163043 : Reach 163043 := rs (se 1 (by rfl) ⟨122282, by rfl⟩) R244565
theorem R228739 : Reach 228739 := rs (se 1 (by rfl) ⟨171554, by rfl⟩) R343109
theorem R163313 : Reach 163313 := rs (se 2 (by rfl) ⟨61242, by rfl⟩) R122485
theorem R163331 : Reach 163331 := rs (se 1 (by rfl) ⟨122498, by rfl⟩) R244997
theorem R196177 : Reach 196177 := rs (se 2 (by rfl) ⟨73566, by rfl⟩) R147133
theorem R163601 : Reach 163601 := rs (se 2 (by rfl) ⟨61350, by rfl⟩) R122701
theorem R163619 : Reach 163619 := rs (se 1 (by rfl) ⟨122714, by rfl⟩) R245429
theorem R98113 : Reach 98113 := rs (se 2 (by rfl) ⟨36792, by rfl⟩) R73585
theorem R163979 : Reach 163979 := rs (se 1 (by rfl) ⟨122984, by rfl⟩) R245969
theorem R164033 : Reach 164033 := rs (se 2 (by rfl) ⟨61512, by rfl⟩) R123025
theorem R524675 : Reach 524675 := rs (se 1 (by rfl) ⟨393506, by rfl⟩) R787013
theorem R164249 : Reach 164249 := rs (se 2 (by rfl) ⟨61593, by rfl⟩) R123187
theorem R164339 : Reach 164339 := rs (se 1 (by rfl) ⟨123254, by rfl⟩) R246509
theorem R164375 : Reach 164375 := rs (se 1 (by rfl) ⟨123281, by rfl⟩) R246563
theorem R2851421 : Reach 2851421 := rs (se 3 (by rfl) ⟨534641, by rfl⟩) R1069283
theorem R426647 : Reach 426647 := rs (se 1 (by rfl) ⟨319985, by rfl⟩) R639971
theorem R164555 : Reach 164555 := rs (se 1 (by rfl) ⟨123416, by rfl⟩) R246833
theorem R99019 : Reach 99019 := rs (se 1 (by rfl) ⟨74264, by rfl⟩) R148529
theorem R164609 : Reach 164609 := rs (se 2 (by rfl) ⟨61728, by rfl⟩) R123457
theorem R394085 : Reach 394085 := rs (se 4 (by rfl) ⟨36945, by rfl⟩) R73891
theorem R295811 : Reach 295811 := rs (se 1 (by rfl) ⟨221858, by rfl⟩) R443717
theorem R623537 : Reach 623537 := rs (se 2 (by rfl) ⟨233826, by rfl⟩) R467653
theorem R164825 : Reach 164825 := rs (se 2 (by rfl) ⟨61809, by rfl⟩) R123619
theorem R164915 : Reach 164915 := rs (se 1 (by rfl) ⟨123686, by rfl⟩) R247373
theorem R164951 : Reach 164951 := rs (se 1 (by rfl) ⟨123713, by rfl⟩) R247427
theorem R165131 : Reach 165131 := rs (se 1 (by rfl) ⟨123848, by rfl⟩) R247697
theorem R361745 : Reach 361745 := rs (se 2 (by rfl) ⟨135654, by rfl⟩) R271309
theorem R329005 : Reach 329005 := rs (se 3 (by rfl) ⟨61688, by rfl⟩) R123377
theorem R165185 : Reach 165185 := rs (se 2 (by rfl) ⟨61944, by rfl⟩) R123889
theorem R361907 : Reach 361907 := rs (se 1 (by rfl) ⟨271430, by rfl⟩) R542861
theorem R99787 : Reach 99787 := rs (se 1 (by rfl) ⟨74840, by rfl⟩) R149681
theorem R165401 : Reach 165401 := rs (se 2 (by rfl) ⟨62025, by rfl⟩) R124051
theorem R165491 : Reach 165491 := rs (se 1 (by rfl) ⟨124118, by rfl⟩) R248237
theorem R689795 : Reach 689795 := rs (se 1 (by rfl) ⟨517346, by rfl⟩) R1034693
theorem R886403 : Reach 886403 := rs (se 1 (by rfl) ⟨664802, by rfl⟩) R1329605
theorem R165527 : Reach 165527 := rs (se 1 (by rfl) ⟨124145, by rfl⟩) R248291
theorem R165707 : Reach 165707 := rs (se 1 (by rfl) ⟨124280, by rfl⟩) R248561
theorem R296797 : Reach 296797 := rs (se 3 (by rfl) ⟨55649, by rfl⟩) R111299
theorem R165761 : Reach 165761 := rs (se 2 (by rfl) ⟨62160, by rfl⟩) R124321
theorem R165977 : Reach 165977 := rs (se 2 (by rfl) ⟨62241, by rfl⟩) R124483
theorem R3967127 : Reach 3967127 := rs (se 1 (by rfl) ⟨2975345, by rfl⟩) R5950691
theorem R166067 : Reach 166067 := rs (se 1 (by rfl) ⟨124550, by rfl⟩) R249101
theorem R166103 : Reach 166103 := rs (se 1 (by rfl) ⟨124577, by rfl⟩) R249155
theorem R166195 : Reach 166195 := rs (se 1 (by rfl) ⟨124646, by rfl⟩) R249293
theorem R526657 : Reach 526657 := rs (se 2 (by rfl) ⟨197496, by rfl⟩) R394993
theorem R166283 : Reach 166283 := rs (se 1 (by rfl) ⟨124712, by rfl⟩) R249425
theorem R166337 : Reach 166337 := rs (se 2 (by rfl) ⟨62376, by rfl⟩) R124753
theorem R4983389 : Reach 4983389 := rs (se 3 (by rfl) ⟨934385, by rfl⟩) R1868771
theorem R166553 : Reach 166553 := rs (se 2 (by rfl) ⟨62457, by rfl⟩) R124915
theorem R166643 : Reach 166643 := rs (se 1 (by rfl) ⟨124982, by rfl⟩) R249965
theorem R166679 : Reach 166679 := rs (se 1 (by rfl) ⟨125009, by rfl⟩) R250019
theorem R265133 : Reach 265133 := rs (se 3 (by rfl) ⟨49712, by rfl⟩) R99425
theorem R166859 : Reach 166859 := rs (se 1 (by rfl) ⟨125144, by rfl⟩) R250289
theorem R166913 : Reach 166913 := rs (se 2 (by rfl) ⟨62592, by rfl⟩) R125185
theorem R2755619 : Reach 2755619 := rs (se 1 (by rfl) ⟨2066714, by rfl⟩) R4133429
theorem R396505 : Reach 396505 := rs (se 2 (by rfl) ⟨148689, by rfl⟩) R297379
theorem R167129 : Reach 167129 := rs (se 2 (by rfl) ⟨62673, by rfl⟩) R125347
theorem R167219 : Reach 167219 := rs (se 1 (by rfl) ⟨125414, by rfl⟩) R250829
theorem R363851 : Reach 363851 := rs (se 1 (by rfl) ⟨272888, by rfl⟩) R545777
theorem R167255 : Reach 167255 := rs (se 1 (by rfl) ⟨125441, by rfl⟩) R250883
theorem R167435 : Reach 167435 := rs (se 1 (by rfl) ⟨125576, by rfl⟩) R251153
theorem R167489 : Reach 167489 := rs (se 2 (by rfl) ⟨62808, by rfl⟩) R125617
theorem R134873 : Reach 134873 := rs (se 2 (by rfl) ⟨50577, by rfl⟩) R101155
theorem R167705 : Reach 167705 := rs (se 2 (by rfl) ⟨62889, by rfl⟩) R125779
theorem R167795 : Reach 167795 := rs (se 1 (by rfl) ⟨125846, by rfl⟩) R251693
theorem R167831 : Reach 167831 := rs (se 1 (by rfl) ⟨125873, by rfl⟩) R251747
theorem R921617 : Reach 921617 := rs (se 2 (by rfl) ⟨345606, by rfl⟩) R691213
theorem R331793 : Reach 331793 := rs (se 2 (by rfl) ⟨124422, by rfl⟩) R248845
theorem R168011 : Reach 168011 := rs (se 1 (by rfl) ⟨126008, by rfl⟩) R252017
theorem R135283 : Reach 135283 := rs (se 1 (by rfl) ⟨101462, by rfl⟩) R202925
theorem R168065 : Reach 168065 := rs (se 2 (by rfl) ⟨63024, by rfl⟩) R126049
theorem R561329 : Reach 561329 := rs (se 2 (by rfl) ⟨210498, by rfl⟩) R420997
theorem R168281 : Reach 168281 := rs (se 2 (by rfl) ⟨63105, by rfl⟩) R126211
theorem R168371 : Reach 168371 := rs (se 1 (by rfl) ⟨126278, by rfl⟩) R252557
theorem R168407 : Reach 168407 := rs (se 1 (by rfl) ⟨126305, by rfl⟩) R252611
theorem R823769 : Reach 823769 := rs (se 2 (by rfl) ⟨308913, by rfl⟩) R617827
theorem R889379 : Reach 889379 := rs (se 1 (by rfl) ⟨667034, by rfl⟩) R1334069
theorem R135731 : Reach 135731 := rs (se 1 (by rfl) ⟨101798, by rfl⟩) R203597
theorem R299585 : Reach 299585 := rs (se 2 (by rfl) ⟨112344, by rfl⟩) R224689
theorem R332363 : Reach 332363 := rs (se 1 (by rfl) ⟨249272, by rfl⟩) R498545
theorem R135769 : Reach 135769 := rs (se 2 (by rfl) ⟨50913, by rfl⟩) R101827
theorem R168587 : Reach 168587 := rs (se 1 (by rfl) ⟨126440, by rfl⟩) R252881
theorem R561815 : Reach 561815 := rs (se 1 (by rfl) ⟨421361, by rfl⟩) R842723
theorem R168641 : Reach 168641 := rs (se 2 (by rfl) ⟨63240, by rfl⟩) R126481
theorem R168983 : Reach 168983 := rs (se 1 (by rfl) ⟨126737, by rfl⟩) R253475
theorem R136217 : Reach 136217 := rs (se 2 (by rfl) ⟨51081, by rfl⟩) R102163
theorem R365633 : Reach 365633 := rs (se 2 (by rfl) ⟨137112, by rfl⟩) R274225
theorem R595019 : Reach 595019 := rs (se 1 (by rfl) ⟨446264, by rfl⟩) R892529
theorem R103513 : Reach 103513 := rs (se 2 (by rfl) ⟨38817, by rfl⟩) R77635
theorem R234647 : Reach 234647 := rs (se 1 (by rfl) ⟨175985, by rfl⟩) R351971
theorem R464089 : Reach 464089 := rs (se 2 (by rfl) ⟨174033, by rfl⟩) R348067
theorem R71127 : Reach 71127 := rs (se 1 (by rfl) ⟨53345, by rfl⟩) R106691
theorem R71147 : Reach 71147 := rs (se 1 (by rfl) ⟨53360, by rfl⟩) R106721
theorem R71159 : Reach 71159 := rs (se 1 (by rfl) ⟨53369, by rfl⟩) R106739
theorem R71179 : Reach 71179 := rs (se 1 (by rfl) ⟨53384, by rfl⟩) R106769
theorem R71191 : Reach 71191 := rs (se 1 (by rfl) ⟨53393, by rfl⟩) R106787
theorem R71211 : Reach 71211 := rs (se 1 (by rfl) ⟨53408, by rfl⟩) R106817
theorem R71223 : Reach 71223 := rs (se 1 (by rfl) ⟨53417, by rfl⟩) R106835
theorem R71243 : Reach 71243 := rs (se 1 (by rfl) ⟨53432, by rfl⟩) R106865
theorem R71255 : Reach 71255 := rs (se 1 (by rfl) ⟨53441, by rfl⟩) R106883
theorem R71275 : Reach 71275 := rs (se 1 (by rfl) ⟨53456, by rfl⟩) R106913
theorem R71287 : Reach 71287 := rs (se 1 (by rfl) ⟨53465, by rfl⟩) R106931
theorem R71307 : Reach 71307 := rs (se 1 (by rfl) ⟨53480, by rfl⟩) R106961
theorem R71319 : Reach 71319 := rs (se 1 (by rfl) ⟨53489, by rfl⟩) R106979
theorem R71339 : Reach 71339 := rs (se 1 (by rfl) ⟨53504, by rfl⟩) R107009
theorem R71351 : Reach 71351 := rs (se 1 (by rfl) ⟨53513, by rfl⟩) R107027
theorem R71371 : Reach 71371 := rs (se 1 (by rfl) ⟨53528, by rfl⟩) R107057
theorem R71383 : Reach 71383 := rs (se 1 (by rfl) ⟨53537, by rfl⟩) R107075
theorem R71403 : Reach 71403 := rs (se 1 (by rfl) ⟨53552, by rfl⟩) R107105
theorem R71415 : Reach 71415 := rs (se 1 (by rfl) ⟨53561, by rfl⟩) R107123
theorem R136961 : Reach 136961 := rs (se 2 (by rfl) ⟨51360, by rfl⟩) R102721
theorem R71435 : Reach 71435 := rs (se 1 (by rfl) ⟨53576, by rfl⟩) R107153
theorem R71447 : Reach 71447 := rs (se 1 (by rfl) ⟨53585, by rfl⟩) R107171
theorem R71467 : Reach 71467 := rs (se 1 (by rfl) ⟨53600, by rfl⟩) R107201
theorem R71479 : Reach 71479 := rs (se 1 (by rfl) ⟨53609, by rfl⟩) R107219
theorem R202571 : Reach 202571 := rs (se 1 (by rfl) ⟨151928, by rfl⟩) R303857
theorem R71499 : Reach 71499 := rs (se 1 (by rfl) ⟨53624, by rfl⟩) R107249
theorem R71511 : Reach 71511 := rs (se 1 (by rfl) ⟨53633, by rfl⟩) R107267
theorem R71531 : Reach 71531 := rs (se 1 (by rfl) ⟨53648, by rfl⟩) R107297
theorem R71543 : Reach 71543 := rs (se 1 (by rfl) ⟨53657, by rfl⟩) R107315
theorem R71563 : Reach 71563 := rs (se 1 (by rfl) ⟨53672, by rfl⟩) R107345
theorem R71575 : Reach 71575 := rs (se 1 (by rfl) ⟨53681, by rfl⟩) R107363
theorem R71595 : Reach 71595 := rs (se 1 (by rfl) ⟨53696, by rfl⟩) R107393
theorem R71607 : Reach 71607 := rs (se 1 (by rfl) ⟨53705, by rfl⟩) R107411
theorem R71627 : Reach 71627 := rs (se 1 (by rfl) ⟨53720, by rfl⟩) R107441
theorem R71639 : Reach 71639 := rs (se 1 (by rfl) ⟨53729, by rfl⟩) R107459
theorem R71659 : Reach 71659 := rs (se 1 (by rfl) ⟨53744, by rfl⟩) R107489
theorem R71671 : Reach 71671 := rs (se 1 (by rfl) ⟨53753, by rfl⟩) R107507
theorem R333827 : Reach 333827 := rs (se 1 (by rfl) ⟨250370, by rfl⟩) R500741
theorem R71691 : Reach 71691 := rs (se 1 (by rfl) ⟨53768, by rfl⟩) R107537
theorem R137227 : Reach 137227 := rs (se 1 (by rfl) ⟨102920, by rfl⟩) R205841
theorem R71703 : Reach 71703 := rs (se 1 (by rfl) ⟨53777, by rfl⟩) R107555
theorem R71723 : Reach 71723 := rs (se 1 (by rfl) ⟨53792, by rfl⟩) R107585
theorem R71735 : Reach 71735 := rs (se 1 (by rfl) ⟨53801, by rfl⟩) R107603
theorem R71755 : Reach 71755 := rs (se 1 (by rfl) ⟨53816, by rfl⟩) R107633
theorem R71767 : Reach 71767 := rs (se 1 (by rfl) ⟨53825, by rfl⟩) R107651
theorem R137303 : Reach 137303 := rs (se 1 (by rfl) ⟨102977, by rfl⟩) R205955
theorem R71787 : Reach 71787 := rs (se 1 (by rfl) ⟨53840, by rfl⟩) R107681
theorem R71799 : Reach 71799 := rs (se 1 (by rfl) ⟨53849, by rfl⟩) R107699
theorem R71819 : Reach 71819 := rs (se 1 (by rfl) ⟨53864, by rfl⟩) R107729
theorem R2398349 : Reach 2398349 := rs (se 3 (by rfl) ⟨449690, by rfl⟩) R899381
theorem R71831 : Reach 71831 := rs (se 1 (by rfl) ⟨53873, by rfl⟩) R107747
theorem R71851 : Reach 71851 := rs (se 1 (by rfl) ⟨53888, by rfl⟩) R107777
theorem R71863 : Reach 71863 := rs (se 1 (by rfl) ⟨53897, by rfl⟩) R107795
theorem R71883 : Reach 71883 := rs (se 1 (by rfl) ⟨53912, by rfl⟩) R107825
theorem R71895 : Reach 71895 := rs (se 1 (by rfl) ⟨53921, by rfl⟩) R107843
theorem R71915 : Reach 71915 := rs (se 1 (by rfl) ⟨53936, by rfl⟩) R107873
theorem R137459 : Reach 137459 := rs (se 1 (by rfl) ⟨103094, by rfl⟩) R206189
theorem R71927 : Reach 71927 := rs (se 1 (by rfl) ⟨53945, by rfl⟩) R107891
theorem R71947 : Reach 71947 := rs (se 1 (by rfl) ⟨53960, by rfl⟩) R107921
theorem R71959 : Reach 71959 := rs (se 1 (by rfl) ⟨53969, by rfl⟩) R107939
theorem R71979 : Reach 71979 := rs (se 1 (by rfl) ⟨53984, by rfl⟩) R107969
theorem R71991 : Reach 71991 := rs (se 1 (by rfl) ⟨53993, by rfl⟩) R107987
theorem R72011 : Reach 72011 := rs (se 1 (by rfl) ⟨54008, by rfl⟩) R108017
theorem R72023 : Reach 72023 := rs (se 1 (by rfl) ⟨54017, by rfl⟩) R108035
theorem R72043 : Reach 72043 := rs (se 1 (by rfl) ⟨54032, by rfl⟩) R108065
theorem R72055 : Reach 72055 := rs (se 1 (by rfl) ⟨54041, by rfl⟩) R108083
theorem R72075 : Reach 72075 := rs (se 1 (by rfl) ⟨54056, by rfl⟩) R108113
theorem R72087 : Reach 72087 := rs (se 1 (by rfl) ⟨54065, by rfl⟩) R108131
theorem R72107 : Reach 72107 := rs (se 1 (by rfl) ⟨54080, by rfl⟩) R108161
theorem R72119 : Reach 72119 := rs (se 1 (by rfl) ⟨54089, by rfl⟩) R108179
theorem R72139 : Reach 72139 := rs (se 1 (by rfl) ⟨54104, by rfl⟩) R108209
theorem R137675 : Reach 137675 := rs (se 1 (by rfl) ⟨103256, by rfl⟩) R206513
theorem R72151 : Reach 72151 := rs (se 1 (by rfl) ⟨54113, by rfl⟩) R108227
theorem R72171 : Reach 72171 := rs (se 1 (by rfl) ⟨54128, by rfl⟩) R108257
theorem R72183 : Reach 72183 := rs (se 1 (by rfl) ⟨54137, by rfl⟩) R108275
theorem R72203 : Reach 72203 := rs (se 1 (by rfl) ⟨54152, by rfl⟩) R108305
theorem R104971 : Reach 104971 := rs (se 1 (by rfl) ⟨78728, by rfl⟩) R157457
theorem R72215 : Reach 72215 := rs (se 1 (by rfl) ⟨54161, by rfl⟩) R108323
theorem R72235 : Reach 72235 := rs (se 1 (by rfl) ⟨54176, by rfl⟩) R108353
theorem R72247 : Reach 72247 := rs (se 1 (by rfl) ⟨54185, by rfl⟩) R108371
theorem R170561 : Reach 170561 := rs (se 2 (by rfl) ⟨63960, by rfl⟩) R127921
theorem R72267 : Reach 72267 := rs (se 1 (by rfl) ⟨54200, by rfl⟩) R108401
theorem R72279 : Reach 72279 := rs (se 1 (by rfl) ⟨54209, by rfl⟩) R108419
theorem R72299 : Reach 72299 := rs (se 1 (by rfl) ⟨54224, by rfl⟩) R108449
theorem R72311 : Reach 72311 := rs (se 1 (by rfl) ⟨54233, by rfl⟩) R108467
theorem R137857 : Reach 137857 := rs (se 2 (by rfl) ⟨51696, by rfl⟩) R103393
theorem R72331 : Reach 72331 := rs (se 1 (by rfl) ⟨54248, by rfl⟩) R108497
theorem R72343 : Reach 72343 := rs (se 1 (by rfl) ⟨54257, by rfl⟩) R108515
theorem R72363 : Reach 72363 := rs (se 1 (by rfl) ⟨54272, by rfl⟩) R108545
theorem R72375 : Reach 72375 := rs (se 1 (by rfl) ⟨54281, by rfl⟩) R108563
theorem R72395 : Reach 72395 := rs (se 1 (by rfl) ⟨54296, by rfl⟩) R108593
theorem R72407 : Reach 72407 := rs (se 1 (by rfl) ⟨54305, by rfl⟩) R108611
theorem R72427 : Reach 72427 := rs (se 1 (by rfl) ⟨54320, by rfl⟩) R108641
theorem R72439 : Reach 72439 := rs (se 1 (by rfl) ⟨54329, by rfl⟩) R108659
theorem R72459 : Reach 72459 := rs (se 1 (by rfl) ⟨54344, by rfl⟩) R108689
theorem R72471 : Reach 72471 := rs (se 1 (by rfl) ⟨54353, by rfl⟩) R108707
theorem R72491 : Reach 72491 := rs (se 1 (by rfl) ⟨54368, by rfl⟩) R108737
theorem R72503 : Reach 72503 := rs (se 1 (by rfl) ⟨54377, by rfl⟩) R108755
theorem R72523 : Reach 72523 := rs (se 1 (by rfl) ⟨54392, by rfl⟩) R108785
theorem R72535 : Reach 72535 := rs (se 1 (by rfl) ⟨54401, by rfl⟩) R108803
theorem R72555 : Reach 72555 := rs (se 1 (by rfl) ⟨54416, by rfl⟩) R108833
theorem R72567 : Reach 72567 := rs (se 1 (by rfl) ⟨54425, by rfl⟩) R108851
theorem R72587 : Reach 72587 := rs (se 1 (by rfl) ⟨54440, by rfl⟩) R108881
theorem R72599 : Reach 72599 := rs (se 1 (by rfl) ⟨54449, by rfl⟩) R108899
theorem R72619 : Reach 72619 := rs (se 1 (by rfl) ⟨54464, by rfl⟩) R108929
theorem R72631 : Reach 72631 := rs (se 1 (by rfl) ⟨54473, by rfl⟩) R108947
theorem R72651 : Reach 72651 := rs (se 1 (by rfl) ⟨54488, by rfl⟩) R108977
theorem R72663 : Reach 72663 := rs (se 1 (by rfl) ⟨54497, by rfl⟩) R108995
theorem R138199 : Reach 138199 := rs (se 1 (by rfl) ⟨103649, by rfl⟩) R207299
theorem R367577 : Reach 367577 := rs (se 2 (by rfl) ⟨137841, by rfl⟩) R275683
theorem R72683 : Reach 72683 := rs (se 1 (by rfl) ⟨54512, by rfl⟩) R109025
theorem R72695 : Reach 72695 := rs (se 1 (by rfl) ⟨54521, by rfl⟩) R109043
theorem R72715 : Reach 72715 := rs (se 1 (by rfl) ⟨54536, by rfl⟩) R109073
theorem R72727 : Reach 72727 := rs (se 1 (by rfl) ⟨54545, by rfl⟩) R109091
theorem R72747 : Reach 72747 := rs (se 1 (by rfl) ⟨54560, by rfl⟩) R109121
theorem R72759 : Reach 72759 := rs (se 1 (by rfl) ⟨54569, by rfl⟩) R109139
theorem R72779 : Reach 72779 := rs (se 1 (by rfl) ⟨54584, by rfl⟩) R109169
theorem R72791 : Reach 72791 := rs (se 1 (by rfl) ⟨54593, by rfl⟩) R109187
theorem R466013 : Reach 466013 := rs (se 3 (by rfl) ⟨87377, by rfl⟩) R174755
theorem R72811 : Reach 72811 := rs (se 1 (by rfl) ⟨54608, by rfl⟩) R109217
theorem R72823 : Reach 72823 := rs (se 1 (by rfl) ⟨54617, by rfl⟩) R109235
theorem R72843 : Reach 72843 := rs (se 1 (by rfl) ⟨54632, by rfl⟩) R109265
theorem R72855 : Reach 72855 := rs (se 1 (by rfl) ⟨54641, by rfl⟩) R109283
theorem R302231 : Reach 302231 := rs (se 1 (by rfl) ⟨226673, by rfl⟩) R453347
theorem R72875 : Reach 72875 := rs (se 1 (by rfl) ⟨54656, by rfl⟩) R109313
theorem R138419 : Reach 138419 := rs (se 1 (by rfl) ⟨103814, by rfl⟩) R207629
theorem R72887 : Reach 72887 := rs (se 1 (by rfl) ⟨54665, by rfl⟩) R109331
theorem R72907 : Reach 72907 := rs (se 1 (by rfl) ⟨54680, by rfl⟩) R109361
theorem R72919 : Reach 72919 := rs (se 1 (by rfl) ⟨54689, by rfl⟩) R109379
theorem R72939 : Reach 72939 := rs (se 1 (by rfl) ⟨54704, by rfl⟩) R109409
theorem R72951 : Reach 72951 := rs (se 1 (by rfl) ⟨54713, by rfl⟩) R109427
theorem R72971 : Reach 72971 := rs (se 1 (by rfl) ⟨54728, by rfl⟩) R109457
theorem R72983 : Reach 72983 := rs (se 1 (by rfl) ⟨54737, by rfl⟩) R109475
theorem R73003 : Reach 73003 := rs (se 1 (by rfl) ⟨54752, by rfl⟩) R109505
theorem R73015 : Reach 73015 := rs (se 1 (by rfl) ⟨54761, by rfl⟩) R109523
theorem R73035 : Reach 73035 := rs (se 1 (by rfl) ⟨54776, by rfl⟩) R109553
theorem R73047 : Reach 73047 := rs (se 1 (by rfl) ⟨54785, by rfl⟩) R109571
theorem R73067 : Reach 73067 := rs (se 1 (by rfl) ⟨54800, by rfl⟩) R109601
theorem R73079 : Reach 73079 := rs (se 1 (by rfl) ⟨54809, by rfl⟩) R109619
theorem R73099 : Reach 73099 := rs (se 1 (by rfl) ⟨54824, by rfl⟩) R109649
theorem R138647 : Reach 138647 := rs (se 1 (by rfl) ⟨103985, by rfl⟩) R207971
theorem R73111 : Reach 73111 := rs (se 1 (by rfl) ⟨54833, by rfl⟩) R109667
theorem R73131 : Reach 73131 := rs (se 1 (by rfl) ⟨54848, by rfl⟩) R109697
theorem R204211 : Reach 204211 := rs (se 1 (by rfl) ⟨153158, by rfl⟩) R306317
theorem R73143 : Reach 73143 := rs (se 1 (by rfl) ⟨54857, by rfl⟩) R109715
theorem R73163 : Reach 73163 := rs (se 1 (by rfl) ⟨54872, by rfl⟩) R109745
theorem R73175 : Reach 73175 := rs (se 1 (by rfl) ⟨54881, by rfl⟩) R109763
theorem R73195 : Reach 73195 := rs (se 1 (by rfl) ⟨54896, by rfl⟩) R109793
theorem R73207 : Reach 73207 := rs (se 1 (by rfl) ⟨54905, by rfl⟩) R109811
theorem R73227 : Reach 73227 := rs (se 1 (by rfl) ⟨54920, by rfl⟩) R109841
theorem R73239 : Reach 73239 := rs (se 1 (by rfl) ⟨54929, by rfl⟩) R109859
theorem R73259 : Reach 73259 := rs (se 1 (by rfl) ⟨54944, by rfl⟩) R109889
theorem R237107 : Reach 237107 := rs (se 1 (by rfl) ⟨177830, by rfl⟩) R355661
theorem R73271 : Reach 73271 := rs (se 1 (by rfl) ⟨54953, by rfl⟩) R109907
theorem R73291 : Reach 73291 := rs (se 1 (by rfl) ⟨54968, by rfl⟩) R109937
theorem R73303 : Reach 73303 := rs (se 1 (by rfl) ⟨54977, by rfl⟩) R109955
theorem R73323 : Reach 73323 := rs (se 1 (by rfl) ⟨54992, by rfl⟩) R109985
theorem R73335 : Reach 73335 := rs (se 1 (by rfl) ⟨55001, by rfl⟩) R110003
theorem R73355 : Reach 73355 := rs (se 1 (by rfl) ⟨55016, by rfl⟩) R110033
theorem R204439 : Reach 204439 := rs (se 1 (by rfl) ⟨153329, by rfl⟩) R306659
theorem R138905 : Reach 138905 := rs (se 2 (by rfl) ⟨52089, by rfl⟩) R104179
theorem R73367 : Reach 73367 := rs (se 1 (by rfl) ⟨55025, by rfl⟩) R110051
theorem R73387 : Reach 73387 := rs (se 1 (by rfl) ⟨55040, by rfl⟩) R110081
theorem R73399 : Reach 73399 := rs (se 1 (by rfl) ⟨55049, by rfl⟩) R110099
theorem R73419 : Reach 73419 := rs (se 1 (by rfl) ⟨55064, by rfl⟩) R110129
theorem R73431 : Reach 73431 := rs (se 1 (by rfl) ⟨55073, by rfl⟩) R110147
theorem R106201 : Reach 106201 := rs (se 2 (by rfl) ⟨39825, by rfl⟩) R79651
theorem R73451 : Reach 73451 := rs (se 1 (by rfl) ⟨55088, by rfl⟩) R110177
theorem R73463 : Reach 73463 := rs (se 1 (by rfl) ⟨55097, by rfl⟩) R110195
theorem R73483 : Reach 73483 := rs (se 1 (by rfl) ⟨55112, by rfl⟩) R110225
theorem R73495 : Reach 73495 := rs (se 1 (by rfl) ⟨55121, by rfl⟩) R110243
theorem R73515 : Reach 73515 := rs (se 1 (by rfl) ⟨55136, by rfl⟩) R110273
theorem R270125 : Reach 270125 := rs (se 3 (by rfl) ⟨50648, by rfl⟩) R101297
theorem R73527 : Reach 73527 := rs (se 1 (by rfl) ⟨55145, by rfl⟩) R110291
theorem R270155 : Reach 270155 := rs (se 1 (by rfl) ⟨202616, by rfl⟩) R405233
theorem R73547 : Reach 73547 := rs (se 1 (by rfl) ⟨55160, by rfl⟩) R110321
theorem R73559 : Reach 73559 := rs (se 1 (by rfl) ⟨55169, by rfl⟩) R110339
theorem R73579 : Reach 73579 := rs (se 1 (by rfl) ⟨55184, by rfl⟩) R110369
theorem R73591 : Reach 73591 := rs (se 1 (by rfl) ⟨55193, by rfl⟩) R110387
theorem R73611 : Reach 73611 := rs (se 1 (by rfl) ⟨55208, by rfl⟩) R110417
theorem R73623 : Reach 73623 := rs (se 1 (by rfl) ⟨55217, by rfl⟩) R110435
theorem R73643 : Reach 73643 := rs (se 1 (by rfl) ⟨55232, by rfl⟩) R110465
theorem R73655 : Reach 73655 := rs (se 1 (by rfl) ⟨55241, by rfl⟩) R110483
theorem R73675 : Reach 73675 := rs (se 1 (by rfl) ⟨55256, by rfl⟩) R110513
theorem R73687 : Reach 73687 := rs (se 1 (by rfl) ⟨55265, by rfl⟩) R110531
theorem R237529 : Reach 237529 := rs (se 2 (by rfl) ⟨89073, by rfl⟩) R178147
theorem R73707 : Reach 73707 := rs (se 1 (by rfl) ⟨55280, by rfl⟩) R110561
theorem R73719 : Reach 73719 := rs (se 1 (by rfl) ⟨55289, by rfl⟩) R110579
theorem R73739 : Reach 73739 := rs (se 1 (by rfl) ⟨55304, by rfl⟩) R110609
theorem R73751 : Reach 73751 := rs (se 1 (by rfl) ⟨55313, by rfl⟩) R110627
theorem R73771 : Reach 73771 := rs (se 1 (by rfl) ⟨55328, by rfl⟩) R110657
theorem R139315 : Reach 139315 := rs (se 1 (by rfl) ⟨104486, by rfl⟩) R208973
theorem R73783 : Reach 73783 := rs (se 1 (by rfl) ⟨55337, by rfl⟩) R110675
theorem R73803 : Reach 73803 := rs (se 1 (by rfl) ⟨55352, by rfl⟩) R110705
theorem R73815 : Reach 73815 := rs (se 1 (by rfl) ⟨55361, by rfl⟩) R110723
theorem R73835 : Reach 73835 := rs (se 1 (by rfl) ⟨55376, by rfl⟩) R110753
theorem R73847 : Reach 73847 := rs (se 1 (by rfl) ⟨55385, by rfl⟩) R110771
theorem R73867 : Reach 73867 := rs (se 1 (by rfl) ⟨55400, by rfl⟩) R110801
theorem R139415 : Reach 139415 := rs (se 1 (by rfl) ⟨104561, by rfl⟩) R209123
theorem R73879 : Reach 73879 := rs (se 1 (by rfl) ⟨55409, by rfl⟩) R110819
theorem R73899 : Reach 73899 := rs (se 1 (by rfl) ⟨55424, by rfl⟩) R110849
theorem R73911 : Reach 73911 := rs (se 1 (by rfl) ⟨55433, by rfl⟩) R110867
theorem R237761 : Reach 237761 := rs (se 2 (by rfl) ⟨89160, by rfl⟩) R178321
theorem R73931 : Reach 73931 := rs (se 1 (by rfl) ⟨55448, by rfl⟩) R110897
theorem R73943 : Reach 73943 := rs (se 1 (by rfl) ⟨55457, by rfl⟩) R110915
theorem R73963 : Reach 73963 := rs (se 1 (by rfl) ⟨55472, by rfl⟩) R110945
theorem R73975 : Reach 73975 := rs (se 1 (by rfl) ⟨55481, by rfl⟩) R110963
theorem R106763 : Reach 106763 := rs (se 1 (by rfl) ⟨80072, by rfl⟩) R160145
theorem R73995 : Reach 73995 := rs (se 1 (by rfl) ⟨55496, by rfl⟩) R110993
theorem R106775 : Reach 106775 := rs (se 1 (by rfl) ⟨80081, by rfl⟩) R160163
theorem R74007 : Reach 74007 := rs (se 1 (by rfl) ⟨55505, by rfl⟩) R111011
theorem R74027 : Reach 74027 := rs (se 1 (by rfl) ⟨55520, by rfl⟩) R111041
theorem R74039 : Reach 74039 := rs (se 1 (by rfl) ⟨55529, by rfl⟩) R111059
theorem R74059 : Reach 74059 := rs (se 1 (by rfl) ⟨55544, by rfl⟩) R111089
theorem R74071 : Reach 74071 := rs (se 1 (by rfl) ⟨55553, by rfl⟩) R111107
theorem R106841 : Reach 106841 := rs (se 2 (by rfl) ⟨40065, by rfl⟩) R80131
theorem R74091 : Reach 74091 := rs (se 1 (by rfl) ⟨55568, by rfl⟩) R111137
theorem R74103 : Reach 74103 := rs (se 1 (by rfl) ⟨55577, by rfl⟩) R111155
theorem R74123 : Reach 74123 := rs (se 1 (by rfl) ⟨55592, by rfl⟩) R111185
theorem R74135 : Reach 74135 := rs (se 1 (by rfl) ⟨55601, by rfl⟩) R111203
theorem R74155 : Reach 74155 := rs (se 1 (by rfl) ⟨55616, by rfl⟩) R111233
theorem R74167 : Reach 74167 := rs (se 1 (by rfl) ⟨55625, by rfl⟩) R111251
theorem R106955 : Reach 106955 := rs (se 1 (by rfl) ⟨80216, by rfl⟩) R160433
theorem R74187 : Reach 74187 := rs (se 1 (by rfl) ⟨55640, by rfl⟩) R111281
theorem R106967 : Reach 106967 := rs (se 1 (by rfl) ⟨80225, by rfl⟩) R160451
theorem R74199 : Reach 74199 := rs (se 1 (by rfl) ⟨55649, by rfl⟩) R111299
theorem R270809 : Reach 270809 := rs (se 2 (by rfl) ⟨101553, by rfl⟩) R203107
theorem R74219 : Reach 74219 := rs (se 1 (by rfl) ⟨55664, by rfl⟩) R111329
theorem R74231 : Reach 74231 := rs (se 1 (by rfl) ⟨55673, by rfl⟩) R111347
theorem R74251 : Reach 74251 := rs (se 1 (by rfl) ⟨55688, by rfl⟩) R111377
theorem R74263 : Reach 74263 := rs (se 1 (by rfl) ⟨55697, by rfl⟩) R111395
theorem R107033 : Reach 107033 := rs (se 2 (by rfl) ⟨40137, by rfl⟩) R80275
theorem R139801 : Reach 139801 := rs (se 2 (by rfl) ⟨52425, by rfl⟩) R104851
theorem R74283 : Reach 74283 := rs (se 1 (by rfl) ⟨55712, by rfl⟩) R111425
theorem R369197 : Reach 369197 := rs (se 3 (by rfl) ⟨69224, by rfl⟩) R138449
theorem R74295 : Reach 74295 := rs (se 1 (by rfl) ⟨55721, by rfl⟩) R111443
theorem R74315 : Reach 74315 := rs (se 1 (by rfl) ⟨55736, by rfl⟩) R111473
theorem R74327 : Reach 74327 := rs (se 1 (by rfl) ⟨55745, by rfl⟩) R111491
theorem R303709 : Reach 303709 := rs (se 3 (by rfl) ⟨56945, by rfl⟩) R113891
theorem R74347 : Reach 74347 := rs (se 1 (by rfl) ⟨55760, by rfl⟩) R111521
theorem R74359 : Reach 74359 := rs (se 1 (by rfl) ⟨55769, by rfl⟩) R111539
theorem R107147 : Reach 107147 := rs (se 1 (by rfl) ⟨80360, by rfl⟩) R160721
theorem R74379 : Reach 74379 := rs (se 1 (by rfl) ⟨55784, by rfl⟩) R111569
theorem R107159 : Reach 107159 := rs (se 1 (by rfl) ⟨80369, by rfl⟩) R160739
theorem R74391 : Reach 74391 := rs (se 1 (by rfl) ⟨55793, by rfl⟩) R111587
theorem R74411 : Reach 74411 := rs (se 1 (by rfl) ⟨55808, by rfl⟩) R111617
theorem R74423 : Reach 74423 := rs (se 1 (by rfl) ⟨55817, by rfl⟩) R111635
theorem R74443 : Reach 74443 := rs (se 1 (by rfl) ⟨55832, by rfl⟩) R111665
theorem R74455 : Reach 74455 := rs (se 1 (by rfl) ⟨55841, by rfl⟩) R111683
theorem R107225 : Reach 107225 := rs (se 2 (by rfl) ⟨40209, by rfl⟩) R80419
theorem R74475 : Reach 74475 := rs (se 1 (by rfl) ⟨55856, by rfl⟩) R111713
theorem R74487 : Reach 74487 := rs (se 1 (by rfl) ⟨55865, by rfl⟩) R111731
theorem R74507 : Reach 74507 := rs (se 1 (by rfl) ⟨55880, by rfl⟩) R111761
theorem R271127 : Reach 271127 := rs (se 1 (by rfl) ⟨203345, by rfl⟩) R406691
theorem R74519 : Reach 74519 := rs (se 1 (by rfl) ⟨55889, by rfl⟩) R111779
theorem R74539 : Reach 74539 := rs (se 1 (by rfl) ⟨55904, by rfl⟩) R111809
theorem R74551 : Reach 74551 := rs (se 1 (by rfl) ⟨55913, by rfl⟩) R111827
theorem R107339 : Reach 107339 := rs (se 1 (by rfl) ⟨80504, by rfl⟩) R161009
theorem R74571 : Reach 74571 := rs (se 1 (by rfl) ⟨55928, by rfl⟩) R111857
theorem R107351 : Reach 107351 := rs (se 1 (by rfl) ⟨80513, by rfl⟩) R161027
theorem R74583 : Reach 74583 := rs (se 1 (by rfl) ⟨55937, by rfl⟩) R111875
theorem R74603 : Reach 74603 := rs (se 1 (by rfl) ⟨55952, by rfl⟩) R111905
theorem R74615 : Reach 74615 := rs (se 1 (by rfl) ⟨55961, by rfl⟩) R111923
theorem R74635 : Reach 74635 := rs (se 1 (by rfl) ⟨55976, by rfl⟩) R111953
theorem R74647 : Reach 74647 := rs (se 1 (by rfl) ⟨55985, by rfl⟩) R111971
theorem R107417 : Reach 107417 := rs (se 2 (by rfl) ⟨40281, by rfl⟩) R80563
theorem R74667 : Reach 74667 := rs (se 1 (by rfl) ⟨56000, by rfl⟩) R112001
theorem R74679 : Reach 74679 := rs (se 1 (by rfl) ⟨56009, by rfl⟩) R112019
theorem R74699 : Reach 74699 := rs (se 1 (by rfl) ⟨56024, by rfl⟩) R112049
theorem R74711 : Reach 74711 := rs (se 1 (by rfl) ⟨56033, by rfl⟩) R112067
theorem R74731 : Reach 74731 := rs (se 1 (by rfl) ⟨56048, by rfl⟩) R112097
theorem R74743 : Reach 74743 := rs (se 1 (by rfl) ⟨56057, by rfl⟩) R112115
theorem R107531 : Reach 107531 := rs (se 1 (by rfl) ⟨80648, by rfl⟩) R161297
theorem R74763 : Reach 74763 := rs (se 1 (by rfl) ⟨56072, by rfl⟩) R112145
theorem R107543 : Reach 107543 := rs (se 1 (by rfl) ⟨80657, by rfl⟩) R161315
theorem R74775 : Reach 74775 := rs (se 1 (by rfl) ⟨56081, by rfl⟩) R112163
theorem R74795 : Reach 74795 := rs (se 1 (by rfl) ⟨56096, by rfl⟩) R112193
theorem R74807 : Reach 74807 := rs (se 1 (by rfl) ⟨56105, by rfl⟩) R112211
theorem R140363 : Reach 140363 := rs (se 1 (by rfl) ⟨105272, by rfl⟩) R210545
theorem R74827 : Reach 74827 := rs (se 1 (by rfl) ⟨56120, by rfl⟩) R112241
theorem R74839 : Reach 74839 := rs (se 1 (by rfl) ⟨56129, by rfl⟩) R112259
theorem R107609 : Reach 107609 := rs (se 2 (by rfl) ⟨40353, by rfl⟩) R80707
theorem R74859 : Reach 74859 := rs (se 1 (by rfl) ⟨56144, by rfl⟩) R112289
theorem R74871 : Reach 74871 := rs (se 1 (by rfl) ⟨56153, by rfl⟩) R112307
theorem R74891 : Reach 74891 := rs (se 1 (by rfl) ⟨56168, by rfl⟩) R112337
theorem R74903 : Reach 74903 := rs (se 1 (by rfl) ⟨56177, by rfl⟩) R112355
theorem R74923 : Reach 74923 := rs (se 1 (by rfl) ⟨56192, by rfl⟩) R112385
theorem R74935 : Reach 74935 := rs (se 1 (by rfl) ⟨56201, by rfl⟩) R112403
theorem R107723 : Reach 107723 := rs (se 1 (by rfl) ⟨80792, by rfl⟩) R161585
theorem R74955 : Reach 74955 := rs (se 1 (by rfl) ⟨56216, by rfl⟩) R112433
theorem R1156301 : Reach 1156301 := rs (se 3 (by rfl) ⟨216806, by rfl⟩) R433613
theorem R107735 : Reach 107735 := rs (se 1 (by rfl) ⟨80801, by rfl⟩) R161603
theorem R74967 : Reach 74967 := rs (se 1 (by rfl) ⟨56225, by rfl⟩) R112451
theorem R74987 : Reach 74987 := rs (se 1 (by rfl) ⟨56240, by rfl⟩) R112481
theorem R74999 : Reach 74999 := rs (se 1 (by rfl) ⟨56249, by rfl⟩) R112499
theorem R140545 : Reach 140545 := rs (se 2 (by rfl) ⟨52704, by rfl⟩) R105409
theorem R75019 : Reach 75019 := rs (se 1 (by rfl) ⟨56264, by rfl⟩) R112529
theorem R75031 : Reach 75031 := rs (se 1 (by rfl) ⟨56273, by rfl⟩) R112547
theorem R107801 : Reach 107801 := rs (se 2 (by rfl) ⟨40425, by rfl⟩) R80851
theorem R75051 : Reach 75051 := rs (se 1 (by rfl) ⟨56288, by rfl⟩) R112577
theorem R402733 : Reach 402733 := rs (se 3 (by rfl) ⟨75512, by rfl⟩) R151025
theorem R75063 : Reach 75063 := rs (se 1 (by rfl) ⟨56297, by rfl⟩) R112595
theorem R75083 : Reach 75083 := rs (se 1 (by rfl) ⟨56312, by rfl⟩) R112625
theorem R75095 : Reach 75095 := rs (se 1 (by rfl) ⟨56321, by rfl⟩) R112643
theorem R75115 : Reach 75115 := rs (se 1 (by rfl) ⟨56336, by rfl⟩) R112673
theorem R763253 : Reach 763253 := rs (se 5 (by rfl) ⟨35777, by rfl⟩) R71555
theorem R107915 : Reach 107915 := rs (se 1 (by rfl) ⟨80936, by rfl⟩) R161873
theorem R107927 : Reach 107927 := rs (se 1 (by rfl) ⟨80945, by rfl⟩) R161891
theorem R271795 : Reach 271795 := rs (se 1 (by rfl) ⟨203846, by rfl⟩) R407693
theorem R107993 : Reach 107993 := rs (se 2 (by rfl) ⟨40497, by rfl⟩) R80995
theorem R206297 : Reach 206297 := rs (se 2 (by rfl) ⟨77361, by rfl⟩) R154723
theorem R468497 : Reach 468497 := rs (se 2 (by rfl) ⟨175686, by rfl⟩) R351373
theorem R108107 : Reach 108107 := rs (se 1 (by rfl) ⟨81080, by rfl⟩) R162161
theorem R108119 : Reach 108119 := rs (se 1 (by rfl) ⟨81089, by rfl⟩) R162179
theorem R108185 : Reach 108185 := rs (se 2 (by rfl) ⟨40569, by rfl⟩) R81139
theorem R304813 : Reach 304813 := rs (se 3 (by rfl) ⟨57152, by rfl⟩) R114305
theorem R108299 : Reach 108299 := rs (se 1 (by rfl) ⟨81224, by rfl⟩) R162449
theorem R108311 : Reach 108311 := rs (se 1 (by rfl) ⟨81233, by rfl⟩) R162467
theorem R304985 : Reach 304985 := rs (se 2 (by rfl) ⟨114369, by rfl⟩) R228739
theorem R108377 : Reach 108377 := rs (se 2 (by rfl) ⟨40641, by rfl⟩) R81283
theorem R108491 : Reach 108491 := rs (se 1 (by rfl) ⟨81368, by rfl⟩) R162737
theorem R141259 : Reach 141259 := rs (se 1 (by rfl) ⟨105944, by rfl⟩) R211889
theorem R108503 : Reach 108503 := rs (se 1 (by rfl) ⟨81377, by rfl⟩) R162755
theorem R141335 : Reach 141335 := rs (se 1 (by rfl) ⟨106001, by rfl⟩) R212003
theorem R108569 : Reach 108569 := rs (se 2 (by rfl) ⟨40713, by rfl⟩) R81427
theorem R632933 : Reach 632933 := rs (se 4 (by rfl) ⟨59337, by rfl⟩) R118675
theorem R108683 : Reach 108683 := rs (se 1 (by rfl) ⟨81512, by rfl⟩) R163025
theorem R108695 : Reach 108695 := rs (se 1 (by rfl) ⟨81521, by rfl⟩) R163043
theorem R108761 : Reach 108761 := rs (se 2 (by rfl) ⟨40785, by rfl⟩) R81571
theorem R207127 : Reach 207127 := rs (se 1 (by rfl) ⟨155345, by rfl⟩) R310691
theorem R108875 : Reach 108875 := rs (se 1 (by rfl) ⟨81656, by rfl⟩) R163313
theorem R108887 : Reach 108887 := rs (se 1 (by rfl) ⟨81665, by rfl⟩) R163331
theorem R108953 : Reach 108953 := rs (se 2 (by rfl) ⟨40857, by rfl⟩) R81715
theorem R109067 : Reach 109067 := rs (se 1 (by rfl) ⟨81800, by rfl⟩) R163601
theorem R109079 : Reach 109079 := rs (se 1 (by rfl) ⟨81809, by rfl⟩) R163619
theorem R109145 : Reach 109145 := rs (se 2 (by rfl) ⟨40929, by rfl⟩) R81859
theorem R240221 : Reach 240221 := rs (se 3 (by rfl) ⟨45041, by rfl⟩) R90083
theorem R273041 : Reach 273041 := rs (se 2 (by rfl) ⟨102390, by rfl⟩) R204781
theorem R142003 : Reach 142003 := rs (se 1 (by rfl) ⟨106502, by rfl⟩) R213005
theorem R109259 : Reach 109259 := rs (se 1 (by rfl) ⟨81944, by rfl⟩) R163889
theorem R109271 : Reach 109271 := rs (se 1 (by rfl) ⟨81953, by rfl⟩) R163907
theorem R240407 : Reach 240407 := rs (se 1 (by rfl) ⟨180305, by rfl⟩) R360611
theorem R109337 : Reach 109337 := rs (se 2 (by rfl) ⟨41001, by rfl⟩) R82003
theorem R109451 : Reach 109451 := rs (se 1 (by rfl) ⟨82088, by rfl⟩) R164177
theorem R109463 : Reach 109463 := rs (se 1 (by rfl) ⟨82097, by rfl⟩) R164195
theorem R142231 : Reach 142231 := rs (se 1 (by rfl) ⟨106673, by rfl⟩) R213347
theorem R109529 : Reach 109529 := rs (se 2 (by rfl) ⟨41073, by rfl⟩) R82147
theorem R142337 : Reach 142337 := rs (se 2 (by rfl) ⟨53376, by rfl⟩) R106753
theorem R207947 : Reach 207947 := rs (se 1 (by rfl) ⟨155960, by rfl⟩) R311921
theorem R109643 : Reach 109643 := rs (se 1 (by rfl) ⟨82232, by rfl⟩) R164465
theorem R109655 : Reach 109655 := rs (se 1 (by rfl) ⟨82241, by rfl⟩) R164483
theorem R109721 : Reach 109721 := rs (se 2 (by rfl) ⟨41145, by rfl⟩) R82291
theorem R142489 : Reach 142489 := rs (se 2 (by rfl) ⟨53433, by rfl⟩) R106867
theorem R109835 : Reach 109835 := rs (se 1 (by rfl) ⟨82376, by rfl⟩) R164753
theorem R109847 : Reach 109847 := rs (se 1 (by rfl) ⟨82385, by rfl⟩) R164771
theorem R240947 : Reach 240947 := rs (se 1 (by rfl) ⟨180710, by rfl⟩) R361421
theorem R273739 : Reach 273739 := rs (se 1 (by rfl) ⟨205304, by rfl⟩) R410609
theorem R109913 : Reach 109913 := rs (se 2 (by rfl) ⟨41217, by rfl⟩) R82435
theorem R699749 : Reach 699749 := rs (se 4 (by rfl) ⟨65601, by rfl⟩) R131203
theorem R208279 : Reach 208279 := rs (se 1 (by rfl) ⟨156209, by rfl⟩) R312419
theorem R306625 : Reach 306625 := rs (se 2 (by rfl) ⟨114984, by rfl⟩) R229969
theorem R110027 : Reach 110027 := rs (se 1 (by rfl) ⟨82520, by rfl⟩) R165041
theorem R110039 : Reach 110039 := rs (se 1 (by rfl) ⟨82529, by rfl⟩) R165059
theorem R110105 : Reach 110105 := rs (se 2 (by rfl) ⟨41289, by rfl⟩) R82579
theorem R241217 : Reach 241217 := rs (se 2 (by rfl) ⟨90456, by rfl⟩) R180913
theorem R274013 : Reach 274013 := rs (se 3 (by rfl) ⟨51377, by rfl⟩) R102755
theorem R110219 : Reach 110219 := rs (se 1 (by rfl) ⟨82664, by rfl⟩) R165329
theorem R110231 : Reach 110231 := rs (se 1 (by rfl) ⟨82673, by rfl⟩) R165347
theorem R110297 : Reach 110297 := rs (se 2 (by rfl) ⟨41361, by rfl⟩) R82723
theorem R569105 : Reach 569105 := rs (se 2 (by rfl) ⟨213414, by rfl⟩) R426829
theorem R110411 : Reach 110411 := rs (se 1 (by rfl) ⟨82808, by rfl⟩) R165617
theorem R110423 : Reach 110423 := rs (se 1 (by rfl) ⟨82817, by rfl⟩) R165635
theorem R77707 : Reach 77707 := rs (se 1 (by rfl) ⟨58280, by rfl⟩) R116561
theorem R110489 : Reach 110489 := rs (se 2 (by rfl) ⟨41433, by rfl⟩) R82867
theorem R110603 : Reach 110603 := rs (se 1 (by rfl) ⟨82952, by rfl⟩) R165905
theorem R110615 : Reach 110615 := rs (se 1 (by rfl) ⟨82961, by rfl⟩) R165923
theorem R143411 : Reach 143411 := rs (se 1 (by rfl) ⟨107558, by rfl⟩) R215117
theorem R110681 : Reach 110681 := rs (se 2 (by rfl) ⟨41505, by rfl⟩) R83011
theorem R241757 : Reach 241757 := rs (se 3 (by rfl) ⟨45329, by rfl⟩) R90659
theorem R78007 : Reach 78007 := rs (se 1 (by rfl) ⟨58505, by rfl⟩) R117011
theorem R110795 : Reach 110795 := rs (se 1 (by rfl) ⟨83096, by rfl⟩) R166193
theorem R110807 : Reach 110807 := rs (se 1 (by rfl) ⟨83105, by rfl⟩) R166211
theorem R274711 : Reach 274711 := rs (se 1 (by rfl) ⟨206033, by rfl⟩) R412067
theorem R110873 : Reach 110873 := rs (se 2 (by rfl) ⟨41577, by rfl⟩) R83155
theorem R373085 : Reach 373085 := rs (se 3 (by rfl) ⟨69953, by rfl⟩) R139907
theorem R110987 : Reach 110987 := rs (se 1 (by rfl) ⟨83240, by rfl⟩) R166481
theorem R110999 : Reach 110999 := rs (se 1 (by rfl) ⟨83249, by rfl⟩) R166499
theorem R111065 : Reach 111065 := rs (se 2 (by rfl) ⟨41649, by rfl⟩) R83299
theorem R111179 : Reach 111179 := rs (se 1 (by rfl) ⟨83384, by rfl⟩) R166769
theorem R111191 : Reach 111191 := rs (se 1 (by rfl) ⟨83393, by rfl⟩) R166787
theorem R78455 : Reach 78455 := rs (se 1 (by rfl) ⟨58841, by rfl⟩) R117683
theorem R111257 : Reach 111257 := rs (se 2 (by rfl) ⟨41721, by rfl⟩) R83443
theorem R635597 : Reach 635597 := rs (se 3 (by rfl) ⟨119174, by rfl⟩) R238349
theorem R111371 : Reach 111371 := rs (se 1 (by rfl) ⟨83528, by rfl⟩) R167057
theorem R111383 : Reach 111383 := rs (se 1 (by rfl) ⟨83537, by rfl⟩) R167075
theorem R111449 : Reach 111449 := rs (se 2 (by rfl) ⟨41793, by rfl⟩) R83587
theorem R635825 : Reach 635825 := rs (se 2 (by rfl) ⟨238434, by rfl⟩) R476869
theorem R111563 : Reach 111563 := rs (se 1 (by rfl) ⟨83672, by rfl⟩) R167345
theorem R111575 : Reach 111575 := rs (se 1 (by rfl) ⟨83681, by rfl⟩) R167363
theorem R111641 : Reach 111641 := rs (se 2 (by rfl) ⟨41865, by rfl⟩) R83731
theorem R275501 : Reach 275501 := rs (se 3 (by rfl) ⟨51656, by rfl⟩) R103313
theorem R308299 : Reach 308299 := rs (se 1 (by rfl) ⟨231224, by rfl⟩) R462449
theorem R111755 : Reach 111755 := rs (se 1 (by rfl) ⟨83816, by rfl⟩) R167633
theorem R799895 : Reach 799895 := rs (se 1 (by rfl) ⟨599921, by rfl⟩) R1199843
theorem R111767 : Reach 111767 := rs (se 1 (by rfl) ⟨83825, by rfl⟩) R167651
theorem R242891 : Reach 242891 := rs (se 1 (by rfl) ⟨182168, by rfl⟩) R364337
theorem R111833 : Reach 111833 := rs (se 2 (by rfl) ⟨41937, by rfl⟩) R83875
theorem R111947 : Reach 111947 := rs (se 1 (by rfl) ⟨83960, by rfl⟩) R167921
theorem R111959 : Reach 111959 := rs (se 1 (by rfl) ⟨83969, by rfl⟩) R167939
theorem R308573 : Reach 308573 := rs (se 3 (by rfl) ⟨57857, by rfl⟩) R115715
theorem R112025 : Reach 112025 := rs (se 2 (by rfl) ⟨42009, by rfl⟩) R84019
theorem R243161 : Reach 243161 := rs (se 2 (by rfl) ⟨91185, by rfl⟩) R182371
theorem R210397 : Reach 210397 := rs (se 3 (by rfl) ⟨39449, by rfl⟩) R78899
theorem R112139 : Reach 112139 := rs (se 1 (by rfl) ⟨84104, by rfl⟩) R168209
theorem R112151 : Reach 112151 := rs (se 1 (by rfl) ⟨84113, by rfl⟩) R168227
theorem R1029667 : Reach 1029667 := rs (se 1 (by rfl) ⟨772250, by rfl⟩) R1544501
theorem R112217 : Reach 112217 := rs (se 2 (by rfl) ⟨42081, by rfl⟩) R84163
theorem R112331 : Reach 112331 := rs (se 1 (by rfl) ⟨84248, by rfl⟩) R168497
theorem R112343 : Reach 112343 := rs (se 1 (by rfl) ⟨84257, by rfl⟩) R168515
theorem R112409 : Reach 112409 := rs (se 2 (by rfl) ⟨42153, by rfl⟩) R84307
theorem R79723 : Reach 79723 := rs (se 1 (by rfl) ⟨59792, by rfl⟩) R119585
theorem R112523 : Reach 112523 := rs (se 1 (by rfl) ⟨84392, by rfl⟩) R168785
theorem R112535 : Reach 112535 := rs (se 1 (by rfl) ⟨84401, by rfl⟩) R168803
theorem R112601 : Reach 112601 := rs (se 2 (by rfl) ⟨42225, by rfl⟩) R84451
theorem R80023 : Reach 80023 := rs (se 1 (by rfl) ⟨60017, by rfl⟩) R120035
theorem R243863 : Reach 243863 := rs (se 1 (by rfl) ⟨182897, by rfl⟩) R365795
theorem R80203 : Reach 80203 := rs (se 1 (by rfl) ⟨60152, by rfl⟩) R120305
theorem R375191 : Reach 375191 := rs (se 1 (by rfl) ⟨281393, by rfl⟩) R562787
theorem R80311 : Reach 80311 := rs (se 1 (by rfl) ⟨60233, by rfl⟩) R120467
theorem R276929 : Reach 276929 := rs (se 2 (by rfl) ⟨103848, by rfl⟩) R207697
theorem R80491 : Reach 80491 := rs (se 1 (by rfl) ⟨60368, by rfl⟩) R120737
theorem R244403 : Reach 244403 := rs (se 1 (by rfl) ⟨183302, by rfl⟩) R366605
theorem R80599 : Reach 80599 := rs (se 1 (by rfl) ⟨60449, by rfl⟩) R120899
theorem R211673 : Reach 211673 := rs (se 2 (by rfl) ⟨79377, by rfl⟩) R158755
theorem R604945 : Reach 604945 := rs (se 2 (by rfl) ⟨226854, by rfl⟩) R453709
theorem R80779 : Reach 80779 := rs (se 1 (by rfl) ⟨60584, by rfl⟩) R121169
theorem R244673 : Reach 244673 := rs (se 2 (by rfl) ⟨91752, by rfl⟩) R183505
theorem R179147 : Reach 179147 := rs (se 1 (by rfl) ⟨134360, by rfl⟩) R268721
theorem R80887 : Reach 80887 := rs (se 1 (by rfl) ⟨60665, by rfl⟩) R121331
theorem R81067 : Reach 81067 := rs (se 1 (by rfl) ⟨60800, by rfl⟩) R121601
theorem R81175 : Reach 81175 := rs (se 1 (by rfl) ⟨60881, by rfl⟩) R121763
theorem R605515 : Reach 605515 := rs (se 1 (by rfl) ⟨454136, by rfl⟩) R908273
theorem R474443 : Reach 474443 := rs (se 1 (by rfl) ⟨355832, by rfl⟩) R711665
theorem R146777 : Reach 146777 := rs (se 2 (by rfl) ⟨55041, by rfl⟩) R110083
theorem R81355 : Reach 81355 := rs (se 1 (by rfl) ⟨61016, by rfl⟩) R122033
theorem R605657 : Reach 605657 := rs (se 2 (by rfl) ⟨227121, by rfl⟩) R454243
theorem R245213 : Reach 245213 := rs (se 3 (by rfl) ⟨45977, by rfl⟩) R91955
theorem R81463 : Reach 81463 := rs (se 1 (by rfl) ⟨61097, by rfl⟩) R122195
theorem R179915 : Reach 179915 := rs (se 1 (by rfl) ⟨134936, by rfl⟩) R269873
theorem R81643 : Reach 81643 := rs (se 1 (by rfl) ⟨61232, by rfl⟩) R122465
theorem R81751 : Reach 81751 := rs (se 1 (by rfl) ⟨61313, by rfl⟩) R122627
theorem R147329 : Reach 147329 := rs (se 2 (by rfl) ⟨55248, by rfl⟩) R110497
theorem R278417 : Reach 278417 := rs (se 2 (by rfl) ⟨104406, by rfl⟩) R208813
theorem R81931 : Reach 81931 := rs (se 1 (by rfl) ⟨61448, by rfl⟩) R122897
theorem R82039 : Reach 82039 := rs (se 1 (by rfl) ⟨61529, by rfl⟩) R123059
theorem R180427 : Reach 180427 := rs (se 1 (by rfl) ⟨135320, by rfl⟩) R270641
theorem R82219 : Reach 82219 := rs (se 1 (by rfl) ⟨61664, by rfl⟩) R123329
theorem R213313 : Reach 213313 := rs (se 2 (by rfl) ⟨79992, by rfl⟩) R159985
theorem R180569 : Reach 180569 := rs (se 2 (by rfl) ⟨67713, by rfl⟩) R135427
theorem R278873 : Reach 278873 := rs (se 2 (by rfl) ⟨104577, by rfl⟩) R209155
theorem R82327 : Reach 82327 := rs (se 1 (by rfl) ⟨61745, by rfl⟩) R123491
theorem R278957 : Reach 278957 := rs (se 3 (by rfl) ⟨52304, by rfl⟩) R104609
theorem R475571 : Reach 475571 := rs (se 1 (by rfl) ⟨356678, by rfl⟩) R713357
theorem R279085 : Reach 279085 := rs (se 3 (by rfl) ⟨52328, by rfl⟩) R104657
theorem R442955 : Reach 442955 := rs (se 1 (by rfl) ⟨332216, by rfl⟩) R664433
theorem R246347 : Reach 246347 := rs (se 1 (by rfl) ⟨184760, by rfl⟩) R369521
theorem R82507 : Reach 82507 := rs (se 1 (by rfl) ⟨61880, by rfl⟩) R123761
theorem R1065565 : Reach 1065565 := rs (se 3 (by rfl) ⟨199793, by rfl⟩) R399587
theorem R410291 : Reach 410291 := rs (se 1 (by rfl) ⟨307718, by rfl⟩) R615437
theorem R82615 : Reach 82615 := rs (se 1 (by rfl) ⟨61961, by rfl⟩) R123923
theorem R2081477 : Reach 2081477 := rs (se 4 (by rfl) ⟨195138, by rfl⟩) R390277
theorem R246617 : Reach 246617 := rs (se 2 (by rfl) ⟨92481, by rfl⟩) R184963
theorem R279389 : Reach 279389 := rs (se 3 (by rfl) ⟨52385, by rfl⟩) R104771
theorem R672605 : Reach 672605 := rs (se 3 (by rfl) ⟨126113, by rfl⟩) R252227
theorem R82795 : Reach 82795 := rs (se 1 (by rfl) ⟨62096, by rfl⟩) R124193
theorem R82891 : Reach 82891 := rs (se 1 (by rfl) ⟨62168, by rfl⟩) R124337
theorem R82903 : Reach 82903 := rs (se 1 (by rfl) ⟨62177, by rfl⟩) R124355
theorem R83083 : Reach 83083 := rs (se 1 (by rfl) ⟨62312, by rfl⟩) R124625
theorem R181399 : Reach 181399 := rs (se 1 (by rfl) ⟨136049, by rfl⟩) R272099
theorem R83191 : Reach 83191 := rs (se 1 (by rfl) ⟨62393, by rfl⟩) R124787
theorem R83371 : Reach 83371 := rs (se 1 (by rfl) ⟨62528, by rfl⟩) R125057
theorem R247319 : Reach 247319 := rs (se 1 (by rfl) ⟨185489, by rfl⟩) R370979
theorem R83479 : Reach 83479 := rs (se 1 (by rfl) ⟨62609, by rfl⟩) R125219
theorem R181835 : Reach 181835 := rs (se 1 (by rfl) ⟨136376, by rfl⟩) R272753
theorem R771677 : Reach 771677 := rs (se 3 (by rfl) ⟨144689, by rfl⟩) R289379
theorem R83659 : Reach 83659 := rs (se 1 (by rfl) ⟨62744, by rfl⟩) R125489
theorem R83767 : Reach 83767 := rs (se 1 (by rfl) ⟨62825, by rfl⟩) R125651
theorem R378755 : Reach 378755 := rs (se 1 (by rfl) ⟨284066, by rfl⟩) R568133
theorem R182209 : Reach 182209 := rs (se 2 (by rfl) ⟨68328, by rfl⟩) R136657
theorem R83947 : Reach 83947 := rs (se 1 (by rfl) ⟨62960, by rfl⟩) R125921
theorem R247859 : Reach 247859 := rs (se 1 (by rfl) ⟨185894, by rfl⟩) R371789
theorem R313409 : Reach 313409 := rs (se 2 (by rfl) ⟨117528, by rfl⟩) R235057
theorem R84055 : Reach 84055 := rs (se 1 (by rfl) ⟨63041, by rfl⟩) R126083
theorem R411749 : Reach 411749 := rs (se 4 (by rfl) ⟨38601, by rfl⟩) R77203
theorem R313561 : Reach 313561 := rs (se 2 (by rfl) ⟨117585, by rfl⟩) R235171
theorem R84235 : Reach 84235 := rs (se 1 (by rfl) ⟨63176, by rfl⟩) R126353
theorem R248129 : Reach 248129 := rs (se 2 (by rfl) ⟨93048, by rfl⟩) R186097
theorem R182807 : Reach 182807 := rs (se 1 (by rfl) ⟨137105, by rfl⟩) R274211
theorem R838349 : Reach 838349 := rs (se 3 (by rfl) ⟨157190, by rfl⟩) R314381
theorem R117593 : Reach 117593 := rs (se 2 (by rfl) ⟨44097, by rfl⟩) R88195
theorem R248669 : Reach 248669 := rs (se 3 (by rfl) ⟨46625, by rfl⟩) R93251
theorem R183617 : Reach 183617 := rs (se 2 (by rfl) ⟨68856, by rfl⟩) R137713
theorem R281987 : Reach 281987 := rs (se 1 (by rfl) ⟨211490, by rfl⟩) R422981
theorem R282001 : Reach 282001 := rs (se 2 (by rfl) ⟨105750, by rfl⟩) R211501
theorem R347665 : Reach 347665 := rs (se 2 (by rfl) ⟨130374, by rfl⟩) R260749
theorem R347723 : Reach 347723 := rs (se 1 (by rfl) ⟨260792, by rfl⟩) R521585
theorem R85655 : Reach 85655 := rs (se 1 (by rfl) ⟨64241, by rfl⟩) R128483
theorem R282305 : Reach 282305 := rs (se 2 (by rfl) ⟨105864, by rfl⟩) R211729
theorem R184153 : Reach 184153 := rs (se 2 (by rfl) ⟨69057, by rfl⟩) R138115
theorem R479155 : Reach 479155 := rs (se 1 (by rfl) ⟨359366, by rfl⟩) R718733
theorem R249803 : Reach 249803 := rs (se 1 (by rfl) ⟨187352, by rfl⟩) R374705
theorem R250073 : Reach 250073 := rs (se 2 (by rfl) ⟨93777, by rfl⟩) R187555
theorem R282973 : Reach 282973 := rs (se 3 (by rfl) ⟨53057, by rfl⟩) R106115
theorem R152065 : Reach 152065 := rs (se 2 (by rfl) ⟨57024, by rfl⟩) R114049
theorem R250775 : Reach 250775 := rs (se 1 (by rfl) ⟨188081, by rfl⟩) R376163
theorem R185267 : Reach 185267 := rs (se 1 (by rfl) ⟨138950, by rfl⟩) R277901
theorem R709667 : Reach 709667 := rs (se 1 (by rfl) ⟨532250, by rfl⟩) R1064501
theorem R185561 : Reach 185561 := rs (se 2 (by rfl) ⟨69585, by rfl⟩) R139171
theorem R120089 : Reach 120089 := rs (se 2 (by rfl) ⟨45033, by rfl⟩) R90067
theorem R218461 : Reach 218461 := rs (se 3 (by rfl) ⟨40961, by rfl⟩) R81923
theorem R120217 : Reach 120217 := rs (se 2 (by rfl) ⟨45081, by rfl⟩) R90163
theorem R251315 : Reach 251315 := rs (se 1 (by rfl) ⟨188486, by rfl⟩) R376973
theorem R316979 : Reach 316979 := rs (se 1 (by rfl) ⟨237734, by rfl⟩) R475469
theorem R284249 : Reach 284249 := rs (se 2 (by rfl) ⟨106593, by rfl⟩) R213187
theorem R153227 : Reach 153227 := rs (se 1 (by rfl) ⟨114920, by rfl⟩) R229841
theorem R251585 : Reach 251585 := rs (se 2 (by rfl) ⟨94344, by rfl⟩) R188689
theorem R349913 : Reach 349913 := rs (se 2 (by rfl) ⟨131217, by rfl⟩) R262435
theorem R120791 : Reach 120791 := rs (se 1 (by rfl) ⟨90593, by rfl⟩) R181187
theorem R120919 : Reach 120919 := rs (se 1 (by rfl) ⟨90689, by rfl⟩) R181379
theorem R252125 : Reach 252125 := rs (se 3 (by rfl) ⟨47273, by rfl⟩) R94547
theorem R153971 : Reach 153971 := rs (se 1 (by rfl) ⟨115478, by rfl⟩) R230957
theorem R2873717 : Reach 2873717 := rs (se 5 (by rfl) ⟨134705, by rfl⟩) R269411
theorem R88535 : Reach 88535 := rs (se 1 (by rfl) ⟨66401, by rfl⟩) R132803
theorem R88651 : Reach 88651 := rs (se 1 (by rfl) ⟨66488, by rfl⟩) R132977
theorem R121547 : Reach 121547 := rs (se 1 (by rfl) ⟨91160, by rfl⟩) R182321
theorem R187201 : Reach 187201 := rs (se 2 (by rfl) ⟨70200, by rfl⟩) R140401
theorem R121675 : Reach 121675 := rs (se 1 (by rfl) ⟨91256, by rfl⟩) R182513
theorem R187211 : Reach 187211 := rs (se 1 (by rfl) ⟨140408, by rfl⟩) R280817
theorem R121817 : Reach 121817 := rs (se 2 (by rfl) ⟨45681, by rfl⟩) R91363
theorem R121945 : Reach 121945 := rs (se 2 (by rfl) ⟨45729, by rfl⟩) R91459
theorem R154867 : Reach 154867 := rs (se 1 (by rfl) ⟨116150, by rfl⟩) R232301
theorem R253259 : Reach 253259 := rs (se 1 (by rfl) ⟨189944, by rfl⟩) R379889
theorem R122393 : Reach 122393 := rs (se 2 (by rfl) ⟨45897, by rfl⟩) R91795
theorem R253529 : Reach 253529 := rs (se 2 (by rfl) ⟨95073, by rfl⟩) R190147
theorem R810647 : Reach 810647 := rs (se 1 (by rfl) ⟨607985, by rfl⟩) R1215971
theorem R122519 : Reach 122519 := rs (se 1 (by rfl) ⟨91889, by rfl⟩) R183779
theorem R122647 : Reach 122647 := rs (se 1 (by rfl) ⟨91985, by rfl⟩) R183971
theorem R188183 : Reach 188183 := rs (se 1 (by rfl) ⟨141137, by rfl⟩) R282275
theorem R417581 : Reach 417581 := rs (se 3 (by rfl) ⟨78296, by rfl⟩) R156593
theorem R319747 : Reach 319747 := rs (se 1 (by rfl) ⟨239810, by rfl⟩) R479621
theorem R286993 : Reach 286993 := rs (se 2 (by rfl) ⟨107622, by rfl⟩) R215245
theorem R90391 : Reach 90391 := rs (se 1 (by rfl) ⟨67793, by rfl⟩) R135587
theorem R155927 : Reach 155927 := rs (se 1 (by rfl) ⟨116945, by rfl⟩) R233891
theorem R811309 : Reach 811309 := rs (se 3 (by rfl) ⟨152120, by rfl⟩) R304241
theorem R483685 : Reach 483685 := rs (se 4 (by rfl) ⟨45345, by rfl⟩) R90691
theorem R450917 : Reach 450917 := rs (se 4 (by rfl) ⟨42273, by rfl⟩) R84547
theorem R123275 : Reach 123275 := rs (se 1 (by rfl) ⟨92456, by rfl⟩) R184913
theorem R188851 : Reach 188851 := rs (se 1 (by rfl) ⟨141638, by rfl⟩) R283277
theorem R156097 : Reach 156097 := rs (se 2 (by rfl) ⟨58536, by rfl⟩) R117073
theorem R123403 : Reach 123403 := rs (se 1 (by rfl) ⟨92552, by rfl⟩) R185105
theorem R188993 : Reach 188993 := rs (se 2 (by rfl) ⟨70872, by rfl⟩) R141745
theorem R123545 : Reach 123545 := rs (se 2 (by rfl) ⟨46329, by rfl⟩) R92659
theorem R156439 : Reach 156439 := rs (se 1 (by rfl) ⟨117329, by rfl⟩) R234659
theorem R123673 : Reach 123673 := rs (se 2 (by rfl) ⟨46377, by rfl⟩) R92755
theorem R320705 : Reach 320705 := rs (se 2 (by rfl) ⟨120264, by rfl⟩) R240529
theorem R124247 : Reach 124247 := rs (se 1 (by rfl) ⟨93185, by rfl⟩) R186371
theorem R124375 : Reach 124375 := rs (se 1 (by rfl) ⟨93281, by rfl⟩) R186563
theorem R157259 : Reach 157259 := rs (se 1 (by rfl) ⟨117944, by rfl⟩) R235889
theorem R583469 : Reach 583469 := rs (se 3 (by rfl) ⟨109400, by rfl⟩) R218801
theorem R157619 : Reach 157619 := rs (se 1 (by rfl) ⟨118214, by rfl⟩) R236429
theorem R92107 : Reach 92107 := rs (se 1 (by rfl) ⟨69080, by rfl⟩) R138161
theorem R125003 : Reach 125003 := rs (se 1 (by rfl) ⟨93752, by rfl⟩) R187505
theorem R125131 : Reach 125131 := rs (se 1 (by rfl) ⟨93848, by rfl⟩) R187697
theorem R715013 : Reach 715013 := rs (se 4 (by rfl) ⟨67032, by rfl⟩) R134065
theorem R125273 : Reach 125273 := rs (se 2 (by rfl) ⟨46977, by rfl⟩) R93955
theorem R551261 : Reach 551261 := rs (se 3 (by rfl) ⟨103361, by rfl⟩) R206723
theorem R518501 : Reach 518501 := rs (se 4 (by rfl) ⟨48609, by rfl⟩) R97219
theorem R354739 : Reach 354739 := rs (se 1 (by rfl) ⟨266054, by rfl⟩) R532109
theorem R125401 : Reach 125401 := rs (se 2 (by rfl) ⟨47025, by rfl⟩) R94051
theorem R518987 : Reach 518987 := rs (se 1 (by rfl) ⟨389240, by rfl⟩) R778481
theorem R93079 : Reach 93079 := rs (se 1 (by rfl) ⟨69809, by rfl⟩) R139619
theorem R322483 : Reach 322483 := rs (se 1 (by rfl) ⟨241862, by rfl⟩) R483725
theorem R125975 : Reach 125975 := rs (se 1 (by rfl) ⟨94481, by rfl⟩) R188963
theorem R355373 : Reach 355373 := rs (se 3 (by rfl) ⟨66632, by rfl⟩) R133265
theorem R126103 : Reach 126103 := rs (se 1 (by rfl) ⟨94577, by rfl⟩) R189155
theorem R290051 : Reach 290051 := rs (se 1 (by rfl) ⟨217538, by rfl⟩) R435077
theorem R421271 : Reach 421271 := rs (se 1 (by rfl) ⟨315953, by rfl⟩) R631907
theorem R650713 : Reach 650713 := rs (se 2 (by rfl) ⟨244017, by rfl⟩) R488035
theorem R126515 : Reach 126515 := rs (se 1 (by rfl) ⟨94886, by rfl⟩) R189773
theorem R93847 : Reach 93847 := rs (se 1 (by rfl) ⟨70385, by rfl⟩) R140771
theorem R126643 : Reach 126643 := rs (se 1 (by rfl) ⟨94982, by rfl⟩) R189965
theorem R93899 : Reach 93899 := rs (se 1 (by rfl) ⟨70424, by rfl⟩) R140849
theorem R126731 : Reach 126731 := rs (se 1 (by rfl) ⟨95048, by rfl⟩) R190097
theorem R159617 : Reach 159617 := rs (se 2 (by rfl) ⟨59856, by rfl⟩) R119713
theorem R192449 : Reach 192449 := rs (se 2 (by rfl) ⟨72168, by rfl⟩) R144337
theorem R520141 : Reach 520141 := rs (se 3 (by rfl) ⟨97526, by rfl⟩) R195053
theorem R1339523 : Reach 1339523 := rs (se 1 (by rfl) ⟨1004642, by rfl⟩) R2009285
theorem R258227 : Reach 258227 := rs (se 1 (by rfl) ⟨193670, by rfl⟩) R387341
theorem R94603 : Reach 94603 := rs (se 1 (by rfl) ⟨70952, by rfl⟩) R141905
theorem R160217 : Reach 160217 := rs (se 2 (by rfl) ⟨60081, by rfl⟩) R120163
theorem R160307 : Reach 160307 := rs (se 1 (by rfl) ⟨120230, by rfl⟩) R240461
theorem R160343 : Reach 160343 := rs (se 1 (by rfl) ⟨120257, by rfl⟩) R240515
theorem R94871 : Reach 94871 := rs (se 1 (by rfl) ⟨71153, by rfl⟩) R142307
theorem R291545 : Reach 291545 := rs (se 2 (by rfl) ⟨109329, by rfl⟩) R218659
theorem R160523 : Reach 160523 := rs (se 1 (by rfl) ⟨120392, by rfl⟩) R240785
theorem R160577 : Reach 160577 := rs (se 2 (by rfl) ⟨60216, by rfl⟩) R120433
theorem R258947 : Reach 258947 := rs (se 1 (by rfl) ⟨194210, by rfl⟩) R388421
theorem R160793 : Reach 160793 := rs (se 2 (by rfl) ⟨60297, by rfl⟩) R120595
theorem R160883 : Reach 160883 := rs (se 1 (by rfl) ⟨120662, by rfl⟩) R241325
theorem R160919 : Reach 160919 := rs (se 1 (by rfl) ⟨120689, by rfl⟩) R241379
theorem R619811 : Reach 619811 := rs (se 1 (by rfl) ⟨464858, by rfl⟩) R929717
theorem R161099 : Reach 161099 := rs (se 1 (by rfl) ⟨120824, by rfl⟩) R241649
theorem R161153 : Reach 161153 := rs (se 2 (by rfl) ⟨60432, by rfl⟩) R120865
theorem R3503573 : Reach 3503573 := rs (se 7 (by rfl) ⟨41057, by rfl⟩) R82115
theorem R161369 : Reach 161369 := rs (se 2 (by rfl) ⟨60513, by rfl⟩) R121027
theorem R161459 : Reach 161459 := rs (se 1 (by rfl) ⟨121094, by rfl⟩) R242189
theorem R161495 : Reach 161495 := rs (se 1 (by rfl) ⟨121121, by rfl⟩) R242243
theorem R161675 : Reach 161675 := rs (se 1 (by rfl) ⟨121256, by rfl⟩) R242513
theorem R161729 : Reach 161729 := rs (se 2 (by rfl) ⟨60648, by rfl⟩) R121297
theorem R325579 : Reach 325579 := rs (se 1 (by rfl) ⟨244184, by rfl⟩) R488369
theorem R194525 : Reach 194525 := rs (se 3 (by rfl) ⟨36473, by rfl⟩) R72947
theorem R620561 : Reach 620561 := rs (se 2 (by rfl) ⟨232710, by rfl⟩) R465421
theorem R850013 : Reach 850013 := rs (se 3 (by rfl) ⟨159377, by rfl⟩) R318755
theorem R129163 : Reach 129163 := rs (se 1 (by rfl) ⟨96872, by rfl⟩) R193745
theorem R161945 : Reach 161945 := rs (se 2 (by rfl) ⟨60729, by rfl⟩) R121459
theorem R162035 : Reach 162035 := rs (se 1 (by rfl) ⟨121526, by rfl⟩) R243053
theorem R162071 : Reach 162071 := rs (se 1 (by rfl) ⟨121553, by rfl⟩) R243107
theorem R293165 : Reach 293165 := rs (se 3 (by rfl) ⟨54968, by rfl⟩) R109937
theorem R227659 : Reach 227659 := rs (se 1 (by rfl) ⟨170744, by rfl⟩) R341489
theorem R162251 : Reach 162251 := rs (se 1 (by rfl) ⟨121688, by rfl⟩) R243377
theorem R162305 : Reach 162305 := rs (se 2 (by rfl) ⟨60864, by rfl⟩) R121729
theorem R359063 : Reach 359063 := rs (se 1 (by rfl) ⟨269297, by rfl⟩) R538595
theorem R162521 : Reach 162521 := rs (se 2 (by rfl) ⟨60945, by rfl⟩) R121891
theorem R162611 : Reach 162611 := rs (se 1 (by rfl) ⟨121958, by rfl⟩) R243917
theorem R162647 : Reach 162647 := rs (se 1 (by rfl) ⟨121985, by rfl⟩) R243971
theorem R162827 : Reach 162827 := rs (se 1 (by rfl) ⟨122120, by rfl⟩) R244241
theorem R162881 : Reach 162881 := rs (se 2 (by rfl) ⟨61080, by rfl⟩) R122161
theorem R195659 : Reach 195659 := rs (se 1 (by rfl) ⟨146744, by rfl⟩) R293489
theorem R293977 : Reach 293977 := rs (se 2 (by rfl) ⟨110241, by rfl⟩) R220483
theorem R392323 : Reach 392323 := rs (se 1 (by rfl) ⟨294242, by rfl⟩) R588485
theorem R163097 : Reach 163097 := rs (se 2 (by rfl) ⟨61161, by rfl⟩) R122323
theorem R163187 : Reach 163187 := rs (se 1 (by rfl) ⟨122390, by rfl⟩) R244781
theorem R163223 : Reach 163223 := rs (se 1 (by rfl) ⟨122417, by rfl⟩) R244835
theorem R261569 : Reach 261569 := rs (se 2 (by rfl) ⟨98088, by rfl⟩) R196177
theorem R327185 : Reach 327185 := rs (se 2 (by rfl) ⟨122694, by rfl⟩) R245389
theorem R163403 : Reach 163403 := rs (se 1 (by rfl) ⟨122552, by rfl⟩) R245105
theorem R163457 : Reach 163457 := rs (se 2 (by rfl) ⟨61296, by rfl⟩) R122593
theorem R130817 : Reach 130817 := rs (se 2 (by rfl) ⟨49056, by rfl⟩) R98113
theorem R163673 : Reach 163673 := rs (se 2 (by rfl) ⟨61377, by rfl⟩) R122755
theorem R163763 : Reach 163763 := rs (se 1 (by rfl) ⟨122822, by rfl⟩) R245645
theorem R163799 : Reach 163799 := rs (se 1 (by rfl) ⟨122849, by rfl⟩) R245699
theorem R426329 : Reach 426329 := rs (se 2 (by rfl) ⟨159873, by rfl⟩) R319747
theorem R164231 : Reach 164231 := rs (se 1 (by rfl) ⟨123173, by rfl⟩) R246347
theorem R1081745 : Reach 1081745 := rs (se 2 (by rfl) ⟨405654, by rfl⟩) R811309
theorem R164411 : Reach 164411 := rs (se 1 (by rfl) ⟨123308, by rfl⟩) R246617
theorem R262723 : Reach 262723 := rs (se 1 (by rfl) ⟨197042, by rfl⟩) R394085
theorem R197207 : Reach 197207 := rs (se 1 (by rfl) ⟨147905, by rfl⟩) R295811
theorem R164537 : Reach 164537 := rs (se 2 (by rfl) ⟨61701, by rfl⟩) R123403
theorem R132025 : Reach 132025 := rs (se 2 (by rfl) ⟨49509, by rfl⟩) R99019
theorem R164879 : Reach 164879 := rs (se 1 (by rfl) ⟨123659, by rfl⟩) R247319
theorem R164897 : Reach 164897 := rs (se 2 (by rfl) ⟨61836, by rfl⟩) R123673
theorem R459863 : Reach 459863 := rs (se 1 (by rfl) ⟨344897, by rfl⟩) R689795
theorem R590935 : Reach 590935 := rs (se 1 (by rfl) ⟨443201, by rfl⟩) R886403
theorem R165239 : Reach 165239 := rs (se 1 (by rfl) ⟨123929, by rfl⟩) R247859
theorem R1181213 : Reach 1181213 := rs (se 3 (by rfl) ⟨221477, by rfl⟩) R442955
theorem R886301 : Reach 886301 := rs (se 3 (by rfl) ⟨166181, by rfl⟩) R332363
theorem R165419 : Reach 165419 := rs (se 1 (by rfl) ⟨124064, by rfl⟩) R248129
theorem R7603789 : Reach 7603789 := rs (se 3 (by rfl) ⟨1425710, by rfl⟩) R2851421
theorem R886373 : Reach 886373 := rs (se 4 (by rfl) ⟨83097, by rfl⟩) R166195
theorem R558899 : Reach 558899 := rs (se 1 (by rfl) ⟨419174, by rfl⟩) R838349
theorem R165779 : Reach 165779 := rs (se 1 (by rfl) ⟨124334, by rfl⟩) R248669
theorem R362393 : Reach 362393 := rs (se 2 (by rfl) ⟨135897, by rfl⟩) R271795
theorem R133049 : Reach 133049 := rs (se 2 (by rfl) ⟨49893, by rfl⟩) R99787
theorem R165833 : Reach 165833 := rs (se 2 (by rfl) ⟨62187, by rfl⟩) R124375
theorem R1837079 : Reach 1837079 := rs (se 1 (by rfl) ⟨1377809, by rfl⟩) R2755619
theorem R231815 : Reach 231815 := rs (se 1 (by rfl) ⟨173861, by rfl⟩) R347723
theorem R395729 : Reach 395729 := rs (se 2 (by rfl) ⟨148398, by rfl⟩) R296797
theorem R166535 : Reach 166535 := rs (se 1 (by rfl) ⟨124901, by rfl⟩) R249803
theorem R166715 : Reach 166715 := rs (se 1 (by rfl) ⟨125036, by rfl⟩) R250073
theorem R166841 : Reach 166841 := rs (se 2 (by rfl) ⟨62565, by rfl⟩) R125131
theorem R592919 : Reach 592919 := rs (se 1 (by rfl) ⟨444689, by rfl⟩) R889379
theorem R298013 : Reach 298013 := rs (se 3 (by rfl) ⟨55877, by rfl⟩) R111755
theorem R167183 : Reach 167183 := rs (se 1 (by rfl) ⟨125387, by rfl⟩) R250775
theorem R167201 : Reach 167201 := rs (se 2 (by rfl) ⟨62700, by rfl⟩) R125401
theorem R396679 : Reach 396679 := rs (se 1 (by rfl) ⟨297509, by rfl⟩) R595019
theorem R167543 : Reach 167543 := rs (se 1 (by rfl) ⟨125657, by rfl⟩) R251315
theorem R102151 : Reach 102151 := rs (se 1 (by rfl) ⟨76613, by rfl⟩) R153227
theorem R167723 : Reach 167723 := rs (se 1 (by rfl) ⟨125792, by rfl⟩) R251585
theorem R233275 : Reach 233275 := rs (se 1 (by rfl) ⟨174956, by rfl⟩) R349913
theorem R15109973 : Reach 15109973 := rs (se 9 (by rfl) ⟨44267, by rfl⟩) R88535
theorem R135047 : Reach 135047 := rs (se 1 (by rfl) ⟨101285, by rfl⟩) R202571
theorem R429977 : Reach 429977 := rs (se 2 (by rfl) ⟨161241, by rfl⟩) R322483
theorem R168083 : Reach 168083 := rs (se 1 (by rfl) ⟨126062, by rfl⟩) R252125
theorem R168137 : Reach 168137 := rs (se 2 (by rfl) ⟨63051, by rfl⟩) R126103
theorem R102647 : Reach 102647 := rs (se 1 (by rfl) ⟨76985, by rfl⟩) R153971
theorem R364985 : Reach 364985 := rs (se 2 (by rfl) ⟨136869, by rfl⟩) R273739
theorem R463553 : Reach 463553 := rs (se 2 (by rfl) ⟨173832, by rfl⟩) R347665
theorem R168839 : Reach 168839 := rs (se 1 (by rfl) ⟨126629, by rfl⟩) R253259
theorem R168857 : Reach 168857 := rs (se 2 (by rfl) ⟨63321, by rfl⟩) R126643
theorem R169019 : Reach 169019 := rs (se 1 (by rfl) ⟨126764, by rfl⟩) R253529
theorem R103609 : Reach 103609 := rs (se 2 (by rfl) ⟨38853, by rfl⟩) R77707
theorem R300269 : Reach 300269 := rs (se 3 (by rfl) ⟨56300, by rfl⟩) R112601
theorem R693521 : Reach 693521 := rs (se 2 (by rfl) ⟨260070, by rfl⟩) R520141
theorem R71175 : Reach 71175 := rs (se 1 (by rfl) ⟨53381, by rfl⟩) R106763
theorem R71183 : Reach 71183 := rs (se 1 (by rfl) ⟨53387, by rfl⟩) R106775
theorem R103951 : Reach 103951 := rs (se 1 (by rfl) ⟨77963, by rfl⟩) R155927
theorem R71227 : Reach 71227 := rs (se 1 (by rfl) ⟨53420, by rfl⟩) R106841
theorem R300611 : Reach 300611 := rs (se 1 (by rfl) ⟨225458, by rfl⟩) R450917
theorem R104009 : Reach 104009 := rs (se 2 (by rfl) ⟨39003, by rfl⟩) R78007
theorem R71303 : Reach 71303 := rs (se 1 (by rfl) ⟨53477, by rfl⟩) R106955
theorem R71311 : Reach 71311 := rs (se 1 (by rfl) ⟨53483, by rfl⟩) R106967
theorem R71355 : Reach 71355 := rs (se 1 (by rfl) ⟨53516, by rfl⟩) R107033
theorem R366281 : Reach 366281 := rs (se 2 (by rfl) ⟨137355, by rfl⟩) R274711
theorem R71431 : Reach 71431 := rs (se 1 (by rfl) ⟨53573, by rfl⟩) R107147
theorem R71439 : Reach 71439 := rs (se 1 (by rfl) ⟨53579, by rfl⟩) R107159
theorem R71483 : Reach 71483 := rs (se 1 (by rfl) ⟨53612, by rfl⟩) R107225
theorem R71559 : Reach 71559 := rs (se 1 (by rfl) ⟨53669, by rfl⟩) R107339
theorem R71567 : Reach 71567 := rs (se 1 (by rfl) ⟨53675, by rfl⟩) R107351
theorem R71611 : Reach 71611 := rs (se 1 (by rfl) ⟨53708, by rfl⟩) R107417
theorem R366557 : Reach 366557 := rs (se 3 (by rfl) ⟨68729, by rfl⟩) R137459
theorem R202753 : Reach 202753 := rs (se 2 (by rfl) ⟨76032, by rfl⟩) R152065
theorem R71687 : Reach 71687 := rs (se 1 (by rfl) ⟨53765, by rfl⟩) R107531
theorem R71695 : Reach 71695 := rs (se 1 (by rfl) ⟨53771, by rfl⟩) R107543
theorem R71739 : Reach 71739 := rs (se 1 (by rfl) ⟨53804, by rfl⟩) R107609
theorem R71815 : Reach 71815 := rs (se 1 (by rfl) ⟨53861, by rfl⟩) R107723
theorem R71823 : Reach 71823 := rs (se 1 (by rfl) ⟨53867, by rfl⟩) R107735
theorem R71867 : Reach 71867 := rs (se 1 (by rfl) ⟨53900, by rfl⟩) R107801
theorem R71943 : Reach 71943 := rs (se 1 (by rfl) ⟨53957, by rfl⟩) R107915
theorem R71951 : Reach 71951 := rs (se 1 (by rfl) ⟨53963, by rfl⟩) R107927
theorem R71995 : Reach 71995 := rs (se 1 (by rfl) ⟨53996, by rfl⟩) R107993
theorem R137531 : Reach 137531 := rs (se 1 (by rfl) ⟨103148, by rfl⟩) R206297
theorem R72071 : Reach 72071 := rs (se 1 (by rfl) ⟨54053, by rfl⟩) R108107
theorem R72079 : Reach 72079 := rs (se 1 (by rfl) ⟨54059, by rfl⟩) R108119
theorem R72123 : Reach 72123 := rs (se 1 (by rfl) ⟨54092, by rfl⟩) R108185
theorem R72199 : Reach 72199 := rs (se 1 (by rfl) ⟨54149, by rfl⟩) R108299
theorem R72207 : Reach 72207 := rs (se 1 (by rfl) ⟨54155, by rfl⟩) R108311
theorem R203323 : Reach 203323 := rs (se 1 (by rfl) ⟨152492, by rfl⟩) R304985
theorem R72251 : Reach 72251 := rs (se 1 (by rfl) ⟨54188, by rfl⟩) R108377
theorem R105079 : Reach 105079 := rs (se 1 (by rfl) ⟨78809, by rfl⟩) R157619
theorem R72327 : Reach 72327 := rs (se 1 (by rfl) ⟨54245, by rfl⟩) R108491
theorem R72335 : Reach 72335 := rs (se 1 (by rfl) ⟨54251, by rfl⟩) R108503
theorem R72379 : Reach 72379 := rs (se 1 (by rfl) ⟨54284, by rfl⟩) R108569
theorem R72455 : Reach 72455 := rs (se 1 (by rfl) ⟨54341, by rfl⟩) R108683
theorem R72463 : Reach 72463 := rs (se 1 (by rfl) ⟨54347, by rfl⟩) R108695
theorem R138017 : Reach 138017 := rs (se 2 (by rfl) ⟨51756, by rfl⟩) R103513
theorem R72507 : Reach 72507 := rs (se 1 (by rfl) ⟨54380, by rfl⟩) R108761
theorem R72583 : Reach 72583 := rs (se 1 (by rfl) ⟨54437, by rfl⟩) R108875
theorem R72591 : Reach 72591 := rs (se 1 (by rfl) ⟨54443, by rfl⟩) R108887
theorem R367507 : Reach 367507 := rs (se 1 (by rfl) ⟨275630, by rfl⟩) R551261
theorem R72635 : Reach 72635 := rs (se 1 (by rfl) ⟨54476, by rfl⟩) R108953
theorem R72711 : Reach 72711 := rs (se 1 (by rfl) ⟨54533, by rfl⟩) R109067
theorem R72719 : Reach 72719 := rs (se 1 (by rfl) ⟨54539, by rfl⟩) R109079
theorem R72763 : Reach 72763 := rs (se 1 (by rfl) ⟨54572, by rfl⟩) R109145
theorem R72839 : Reach 72839 := rs (se 1 (by rfl) ⟨54629, by rfl⟩) R109259
theorem R72847 : Reach 72847 := rs (se 1 (by rfl) ⟨54635, by rfl⟩) R109271
theorem R72891 : Reach 72891 := rs (se 1 (by rfl) ⟨54668, by rfl⟩) R109337
theorem R72967 : Reach 72967 := rs (se 1 (by rfl) ⟨54725, by rfl⟩) R109451
theorem R72975 : Reach 72975 := rs (se 1 (by rfl) ⟨54731, by rfl⟩) R109463
theorem R73019 : Reach 73019 := rs (se 1 (by rfl) ⟨54764, by rfl⟩) R109529
theorem R236915 : Reach 236915 := rs (se 1 (by rfl) ⟨177686, by rfl⟩) R355373
theorem R73095 : Reach 73095 := rs (se 1 (by rfl) ⟨54821, by rfl⟩) R109643
theorem R73103 : Reach 73103 := rs (se 1 (by rfl) ⟨54827, by rfl⟩) R109655
theorem R73147 : Reach 73147 := rs (se 1 (by rfl) ⟨54860, by rfl⟩) R109721
theorem R73223 : Reach 73223 := rs (se 1 (by rfl) ⟨54917, by rfl⟩) R109835
theorem R73231 : Reach 73231 := rs (se 1 (by rfl) ⟨54923, by rfl⟩) R109847
theorem R73275 : Reach 73275 := rs (se 1 (by rfl) ⟨54956, by rfl⟩) R109913
theorem R466499 : Reach 466499 := rs (se 1 (by rfl) ⟨349874, by rfl⟩) R699749
theorem R73351 : Reach 73351 := rs (se 1 (by rfl) ⟨55013, by rfl⟩) R110027
theorem R73359 : Reach 73359 := rs (se 1 (by rfl) ⟨55019, by rfl⟩) R110039
theorem R73403 : Reach 73403 := rs (se 1 (by rfl) ⟨55052, by rfl⟩) R110105
theorem R73479 : Reach 73479 := rs (se 1 (by rfl) ⟨55109, by rfl⟩) R110219
theorem R73487 : Reach 73487 := rs (se 1 (by rfl) ⟨55115, by rfl⟩) R110231
theorem R73531 : Reach 73531 := rs (se 1 (by rfl) ⟨55148, by rfl⟩) R110297
theorem R73607 : Reach 73607 := rs (se 1 (by rfl) ⟨55205, by rfl⟩) R110411
theorem R73615 : Reach 73615 := rs (se 1 (by rfl) ⟨55211, by rfl⟩) R110423
theorem R434105 : Reach 434105 := rs (se 2 (by rfl) ⟨162789, by rfl⟩) R325579
theorem R73659 : Reach 73659 := rs (se 1 (by rfl) ⟨55244, by rfl⟩) R110489
theorem R73735 : Reach 73735 := rs (se 1 (by rfl) ⟨55301, by rfl⟩) R110603
theorem R73743 : Reach 73743 := rs (se 1 (by rfl) ⟨55307, by rfl⟩) R110615
theorem R73787 : Reach 73787 := rs (se 1 (by rfl) ⟨55340, by rfl⟩) R110681
theorem R893015 : Reach 893015 := rs (se 1 (by rfl) ⟨669761, by rfl⟩) R1339523
theorem R172151 : Reach 172151 := rs (se 1 (by rfl) ⟨129113, by rfl⟩) R258227
theorem R73863 : Reach 73863 := rs (se 1 (by rfl) ⟨55397, by rfl⟩) R110795
theorem R73871 : Reach 73871 := rs (se 1 (by rfl) ⟨55403, by rfl⟩) R110807
theorem R172217 : Reach 172217 := rs (se 2 (by rfl) ⟨64581, by rfl⟩) R129163
theorem R73915 : Reach 73915 := rs (se 1 (by rfl) ⟨55436, by rfl⟩) R110873
theorem R106697 : Reach 106697 := rs (se 2 (by rfl) ⟨40011, by rfl⟩) R80023
theorem R73991 : Reach 73991 := rs (se 1 (by rfl) ⟨55493, by rfl⟩) R110987
theorem R73999 : Reach 73999 := rs (se 1 (by rfl) ⟨55499, by rfl⟩) R110999
theorem R106811 : Reach 106811 := rs (se 1 (by rfl) ⟨80108, by rfl⟩) R160217
theorem R74043 : Reach 74043 := rs (se 1 (by rfl) ⟨55532, by rfl⟩) R111065
theorem R106871 : Reach 106871 := rs (se 1 (by rfl) ⟨80153, by rfl⟩) R160307
theorem R74119 : Reach 74119 := rs (se 1 (by rfl) ⟨55589, by rfl⟩) R111179
theorem R106895 : Reach 106895 := rs (se 1 (by rfl) ⟨80171, by rfl⟩) R160343
theorem R74127 : Reach 74127 := rs (se 1 (by rfl) ⟨55595, by rfl⟩) R111191
theorem R106937 : Reach 106937 := rs (se 2 (by rfl) ⟨40101, by rfl⟩) R80203
theorem R303545 : Reach 303545 := rs (se 2 (by rfl) ⟨113829, by rfl⟩) R227659
theorem R74171 : Reach 74171 := rs (se 1 (by rfl) ⟨55628, by rfl⟩) R111257
theorem R107015 : Reach 107015 := rs (se 1 (by rfl) ⟨80261, by rfl⟩) R160523
theorem R74247 : Reach 74247 := rs (se 1 (by rfl) ⟨55685, by rfl⟩) R111371
theorem R74255 : Reach 74255 := rs (se 1 (by rfl) ⟨55691, by rfl⟩) R111383
theorem R107051 : Reach 107051 := rs (se 1 (by rfl) ⟨80288, by rfl⟩) R160577
theorem R74299 : Reach 74299 := rs (se 1 (by rfl) ⟨55724, by rfl⟩) R111449
theorem R107081 : Reach 107081 := rs (se 2 (by rfl) ⟨40155, by rfl⟩) R80311
theorem R172631 : Reach 172631 := rs (se 1 (by rfl) ⟨129473, by rfl⟩) R258947
theorem R74375 : Reach 74375 := rs (se 1 (by rfl) ⟨55781, by rfl⟩) R111563
theorem R74383 : Reach 74383 := rs (se 1 (by rfl) ⟨55787, by rfl⟩) R111575
theorem R139961 : Reach 139961 := rs (se 2 (by rfl) ⟨52485, by rfl⟩) R104971
theorem R107195 : Reach 107195 := rs (se 1 (by rfl) ⟨80396, by rfl⟩) R160793
theorem R74427 : Reach 74427 := rs (se 1 (by rfl) ⟨55820, by rfl⟩) R111641
theorem R107255 : Reach 107255 := rs (se 1 (by rfl) ⟨80441, by rfl⟩) R160883
theorem R74503 : Reach 74503 := rs (se 1 (by rfl) ⟨55877, by rfl⟩) R111755
theorem R107279 : Reach 107279 := rs (se 1 (by rfl) ⟨80459, by rfl⟩) R160919
theorem R533263 : Reach 533263 := rs (se 1 (by rfl) ⟨399947, by rfl⟩) R799895
theorem R74511 : Reach 74511 := rs (se 1 (by rfl) ⟨55883, by rfl⟩) R111767
theorem R107321 : Reach 107321 := rs (se 2 (by rfl) ⟨40245, by rfl⟩) R80491
theorem R74555 : Reach 74555 := rs (se 1 (by rfl) ⟨55916, by rfl⟩) R111833
theorem R107399 : Reach 107399 := rs (se 1 (by rfl) ⟨80549, by rfl⟩) R161099
theorem R74631 : Reach 74631 := rs (se 1 (by rfl) ⟨55973, by rfl⟩) R111947
theorem R74639 : Reach 74639 := rs (se 1 (by rfl) ⟨55979, by rfl⟩) R111959
theorem R205715 : Reach 205715 := rs (se 1 (by rfl) ⟨154286, by rfl⟩) R308573
theorem R107435 : Reach 107435 := rs (se 1 (by rfl) ⟨80576, by rfl⟩) R161153
theorem R1254325 : Reach 1254325 := rs (se 5 (by rfl) ⟨58796, by rfl⟩) R117593
theorem R74683 : Reach 74683 := rs (se 1 (by rfl) ⟨56012, by rfl⟩) R112025
theorem R107465 : Reach 107465 := rs (se 2 (by rfl) ⟨40299, by rfl⟩) R80599
theorem R2335715 : Reach 2335715 := rs (se 1 (by rfl) ⟨1751786, by rfl⟩) R3503573
theorem R74759 : Reach 74759 := rs (se 1 (by rfl) ⟨56069, by rfl⟩) R112139
theorem R74767 : Reach 74767 := rs (se 1 (by rfl) ⟨56075, by rfl⟩) R112151
theorem R107579 : Reach 107579 := rs (se 1 (by rfl) ⟨80684, by rfl⟩) R161369
theorem R74811 : Reach 74811 := rs (se 1 (by rfl) ⟨56108, by rfl⟩) R112217
theorem R107639 : Reach 107639 := rs (se 1 (by rfl) ⟨80729, by rfl⟩) R161459
theorem R74887 : Reach 74887 := rs (se 1 (by rfl) ⟨56165, by rfl⟩) R112331
theorem R107663 : Reach 107663 := rs (se 1 (by rfl) ⟨80747, by rfl⟩) R161495
theorem R74895 : Reach 74895 := rs (se 1 (by rfl) ⟨56171, by rfl⟩) R112343
theorem R697517 : Reach 697517 := rs (se 3 (by rfl) ⟨130784, by rfl⟩) R261569
theorem R107705 : Reach 107705 := rs (se 2 (by rfl) ⟨40389, by rfl⟩) R80779
theorem R74939 : Reach 74939 := rs (se 1 (by rfl) ⟨56204, by rfl⟩) R112409
theorem R1615085 : Reach 1615085 := rs (se 3 (by rfl) ⟨302828, by rfl⟩) R605657
theorem R107783 : Reach 107783 := rs (se 1 (by rfl) ⟨80837, by rfl⟩) R161675
theorem R75015 : Reach 75015 := rs (se 1 (by rfl) ⟨56261, by rfl⟩) R112523
theorem R75023 : Reach 75023 := rs (se 1 (by rfl) ⟨56267, by rfl⟩) R112535
theorem R107819 : Reach 107819 := rs (se 1 (by rfl) ⟨80864, by rfl⟩) R161729
theorem R75067 : Reach 75067 := rs (se 1 (by rfl) ⟨56300, by rfl⟩) R112601
theorem R107849 : Reach 107849 := rs (se 2 (by rfl) ⟨40443, by rfl⟩) R80887
theorem R566675 : Reach 566675 := rs (se 1 (by rfl) ⟨425006, by rfl⟩) R850013
theorem R107963 : Reach 107963 := rs (se 1 (by rfl) ⟨80972, by rfl⟩) R161945
theorem R632285 : Reach 632285 := rs (se 3 (by rfl) ⟨118553, by rfl⟩) R237107
theorem R108023 : Reach 108023 := rs (se 1 (by rfl) ⟨81017, by rfl⟩) R162035
theorem R108047 : Reach 108047 := rs (se 1 (by rfl) ⟨81035, by rfl⟩) R162071
theorem R108089 : Reach 108089 := rs (se 2 (by rfl) ⟨40533, by rfl⟩) R81067
theorem R108167 : Reach 108167 := rs (se 1 (by rfl) ⟨81125, by rfl⟩) R162251
theorem R206489 : Reach 206489 := rs (se 2 (by rfl) ⟨77433, by rfl⟩) R154867
theorem R108203 : Reach 108203 := rs (se 1 (by rfl) ⟨81152, by rfl⟩) R162305
theorem R108233 : Reach 108233 := rs (se 2 (by rfl) ⟨40587, by rfl⟩) R81175
theorem R239375 : Reach 239375 := rs (se 1 (by rfl) ⟨179531, by rfl⟩) R359063
theorem R108347 : Reach 108347 := rs (se 1 (by rfl) ⟨81260, by rfl⟩) R162521
theorem R141115 : Reach 141115 := rs (se 1 (by rfl) ⟨105836, by rfl⟩) R211673
theorem R108407 : Reach 108407 := rs (se 1 (by rfl) ⟨81305, by rfl⟩) R162611
theorem R108431 : Reach 108431 := rs (se 1 (by rfl) ⟨81323, by rfl⟩) R162647
theorem R272281 : Reach 272281 := rs (se 2 (by rfl) ⟨102105, by rfl⟩) R204211
theorem R108473 : Reach 108473 := rs (se 2 (by rfl) ⟨40677, by rfl⟩) R81355
theorem R108551 : Reach 108551 := rs (se 1 (by rfl) ⟨81413, by rfl⟩) R162827
theorem R108587 : Reach 108587 := rs (se 1 (by rfl) ⟨81440, by rfl⟩) R162881
theorem R108617 : Reach 108617 := rs (se 2 (by rfl) ⟨40731, by rfl⟩) R81463
theorem R108731 : Reach 108731 := rs (se 1 (by rfl) ⟨81548, by rfl⟩) R163097
theorem R272585 : Reach 272585 := rs (se 2 (by rfl) ⟨102219, by rfl⟩) R204439
theorem R108791 : Reach 108791 := rs (se 1 (by rfl) ⟨81593, by rfl⟩) R163187
theorem R108815 : Reach 108815 := rs (se 1 (by rfl) ⟨81611, by rfl⟩) R163223
theorem R141601 : Reach 141601 := rs (se 2 (by rfl) ⟨53100, by rfl⟩) R106201
theorem R108857 : Reach 108857 := rs (se 2 (by rfl) ⟨40821, by rfl⟩) R81643
theorem R108935 : Reach 108935 := rs (se 1 (by rfl) ⟨81701, by rfl⟩) R163403
theorem R108971 : Reach 108971 := rs (se 1 (by rfl) ⟨81728, by rfl⟩) R163457
theorem R109001 : Reach 109001 := rs (se 2 (by rfl) ⟨40875, by rfl⟩) R81751
theorem R109115 : Reach 109115 := rs (se 1 (by rfl) ⟨81836, by rfl⟩) R163673
theorem R109175 : Reach 109175 := rs (se 1 (by rfl) ⟨81881, by rfl⟩) R163763
theorem R109199 : Reach 109199 := rs (se 1 (by rfl) ⟨81899, by rfl⟩) R163799
theorem R109241 : Reach 109241 := rs (se 2 (by rfl) ⟨40965, by rfl⟩) R81931
theorem R109319 : Reach 109319 := rs (se 1 (by rfl) ⟨81989, by rfl⟩) R163979
theorem R109355 : Reach 109355 := rs (se 1 (by rfl) ⟨82016, by rfl⟩) R164033
theorem R109385 : Reach 109385 := rs (se 2 (by rfl) ⟨41019, by rfl⟩) R82039
theorem R240569 : Reach 240569 := rs (se 2 (by rfl) ⟨90213, by rfl⟩) R180427
theorem R109499 : Reach 109499 := rs (se 1 (by rfl) ⟨82124, by rfl⟩) R164249
theorem R109559 : Reach 109559 := rs (se 1 (by rfl) ⟨82169, by rfl⟩) R164339
theorem R109583 : Reach 109583 := rs (se 1 (by rfl) ⟨82187, by rfl⟩) R164375
theorem R109625 : Reach 109625 := rs (se 2 (by rfl) ⟨41109, by rfl⟩) R82219
theorem R371773 : Reach 371773 := rs (se 3 (by rfl) ⟨69707, by rfl⟩) R139415
theorem R273527 : Reach 273527 := rs (se 1 (by rfl) ⟨205145, by rfl⟩) R410291
theorem R1387651 : Reach 1387651 := rs (se 1 (by rfl) ⟨1040738, by rfl⟩) R2081477
theorem R109703 : Reach 109703 := rs (se 1 (by rfl) ⟨82277, by rfl⟩) R164555
theorem R109739 : Reach 109739 := rs (se 1 (by rfl) ⟨82304, by rfl⟩) R164609
theorem R109769 : Reach 109769 := rs (se 2 (by rfl) ⟨41163, by rfl⟩) R82327
theorem R109883 : Reach 109883 := rs (se 1 (by rfl) ⟨82412, by rfl⟩) R164825
theorem R109943 : Reach 109943 := rs (se 1 (by rfl) ⟨82457, by rfl⟩) R164915
theorem R109967 : Reach 109967 := rs (se 1 (by rfl) ⟨82475, by rfl⟩) R164951
theorem R372113 : Reach 372113 := rs (se 2 (by rfl) ⟨139542, by rfl⟩) R279085
theorem R110009 : Reach 110009 := rs (se 2 (by rfl) ⟨41253, by rfl⟩) R82507
theorem R1420753 : Reach 1420753 := rs (se 2 (by rfl) ⟨532782, by rfl⟩) R1065565
theorem R404945 : Reach 404945 := rs (se 2 (by rfl) ⟨151854, by rfl⟩) R303709
theorem R110087 : Reach 110087 := rs (se 1 (by rfl) ⟨82565, by rfl⟩) R165131
theorem R241163 : Reach 241163 := rs (se 1 (by rfl) ⟨180872, by rfl⟩) R361745
theorem R110123 : Reach 110123 := rs (se 1 (by rfl) ⟨82592, by rfl⟩) R165185
theorem R110153 : Reach 110153 := rs (se 2 (by rfl) ⟨41307, by rfl⟩) R82615
theorem R241271 : Reach 241271 := rs (se 1 (by rfl) ⟨180953, by rfl⟩) R361907
theorem R110267 : Reach 110267 := rs (se 1 (by rfl) ⟨82700, by rfl⟩) R165401
theorem R208585 : Reach 208585 := rs (se 2 (by rfl) ⟨78219, by rfl⟩) R156439
theorem R110327 : Reach 110327 := rs (se 1 (by rfl) ⟨82745, by rfl⟩) R165491
theorem R110351 : Reach 110351 := rs (se 1 (by rfl) ⟨82763, by rfl⟩) R165527
theorem R110393 : Reach 110393 := rs (se 2 (by rfl) ⟨41397, by rfl⟩) R82795
theorem R110471 : Reach 110471 := rs (se 1 (by rfl) ⟨82853, by rfl⟩) R165707
theorem R110507 : Reach 110507 := rs (se 1 (by rfl) ⟨82880, by rfl⟩) R165761
theorem R110521 : Reach 110521 := rs (se 2 (by rfl) ⟨41445, by rfl⟩) R82891
theorem R110537 : Reach 110537 := rs (se 2 (by rfl) ⟨41451, by rfl⟩) R82903
theorem R208939 : Reach 208939 := rs (se 1 (by rfl) ⟨156704, by rfl⟩) R313409
theorem R110651 : Reach 110651 := rs (se 1 (by rfl) ⟨82988, by rfl⟩) R165977
theorem R274499 : Reach 274499 := rs (se 1 (by rfl) ⟨205874, by rfl⟩) R411749
theorem R110711 : Reach 110711 := rs (se 1 (by rfl) ⟨83033, by rfl⟩) R166067
theorem R110735 : Reach 110735 := rs (se 1 (by rfl) ⟨83051, by rfl⟩) R166103
theorem R798893 : Reach 798893 := rs (se 3 (by rfl) ⟨149792, by rfl⟩) R299585
theorem R110777 : Reach 110777 := rs (se 2 (by rfl) ⟨41541, by rfl⟩) R83083
theorem R241865 : Reach 241865 := rs (se 2 (by rfl) ⟨90699, by rfl⟩) R181399
theorem R110855 : Reach 110855 := rs (se 1 (by rfl) ⟨83141, by rfl⟩) R166283
theorem R110891 : Reach 110891 := rs (se 1 (by rfl) ⟨83168, by rfl⟩) R166337
theorem R209213 : Reach 209213 := rs (se 3 (by rfl) ⟨39227, by rfl⟩) R78455
theorem R110921 : Reach 110921 := rs (se 2 (by rfl) ⟨41595, by rfl⟩) R83191
theorem R536977 : Reach 536977 := rs (se 2 (by rfl) ⟨201366, by rfl⟩) R402733
theorem R3322259 : Reach 3322259 := rs (se 1 (by rfl) ⟨2491694, by rfl⟩) R4983389
theorem R111035 : Reach 111035 := rs (se 1 (by rfl) ⟨83276, by rfl⟩) R166553
theorem R111095 : Reach 111095 := rs (se 1 (by rfl) ⟨83321, by rfl⟩) R166643
theorem R111119 : Reach 111119 := rs (se 1 (by rfl) ⟨83339, by rfl⟩) R166679
theorem R111161 : Reach 111161 := rs (se 2 (by rfl) ⟨41685, by rfl⟩) R83371
theorem R176755 : Reach 176755 := rs (se 1 (by rfl) ⟨132566, by rfl⟩) R265133
theorem R111239 : Reach 111239 := rs (se 1 (by rfl) ⟨83429, by rfl⟩) R166859
theorem R111275 : Reach 111275 := rs (se 1 (by rfl) ⟨83456, by rfl⟩) R166913
theorem R111305 : Reach 111305 := rs (se 2 (by rfl) ⟨41739, by rfl⟩) R83479
theorem R111419 : Reach 111419 := rs (se 1 (by rfl) ⟨83564, by rfl⟩) R167129
theorem R111479 : Reach 111479 := rs (se 1 (by rfl) ⟨83609, by rfl⟩) R167219
theorem R242567 : Reach 242567 := rs (se 1 (by rfl) ⟨181925, by rfl⟩) R363851
theorem R111503 : Reach 111503 := rs (se 1 (by rfl) ⟨83627, by rfl⟩) R167255
theorem R406417 : Reach 406417 := rs (se 2 (by rfl) ⟨152406, by rfl⟩) R304813
theorem R111545 : Reach 111545 := rs (se 2 (by rfl) ⟨41829, by rfl⟩) R83659
theorem R832517 : Reach 832517 := rs (se 4 (by rfl) ⟨78048, by rfl⟩) R156097
theorem R111623 : Reach 111623 := rs (se 1 (by rfl) ⟨83717, by rfl⟩) R167435
theorem R111659 : Reach 111659 := rs (se 1 (by rfl) ⟨83744, by rfl⟩) R167489
theorem R111689 : Reach 111689 := rs (se 2 (by rfl) ⟨41883, by rfl⟩) R83767
theorem R111803 : Reach 111803 := rs (se 1 (by rfl) ⟨83852, by rfl⟩) R167705
theorem R111863 : Reach 111863 := rs (se 1 (by rfl) ⟨83897, by rfl⟩) R167795
theorem R242945 : Reach 242945 := rs (se 2 (by rfl) ⟨91104, by rfl⟩) R182209
theorem R111887 : Reach 111887 := rs (se 1 (by rfl) ⟨83915, by rfl⟩) R167831
theorem R111929 : Reach 111929 := rs (se 2 (by rfl) ⟨41973, by rfl⟩) R83947
theorem R112007 : Reach 112007 := rs (se 1 (by rfl) ⟨84005, by rfl⟩) R168011
theorem R112043 : Reach 112043 := rs (se 1 (by rfl) ⟨84032, by rfl⟩) R168065
theorem R112073 : Reach 112073 := rs (se 2 (by rfl) ⟨42027, by rfl⟩) R84055
theorem R374219 : Reach 374219 := rs (se 1 (by rfl) ⟨280664, by rfl⟩) R561329
theorem R112187 : Reach 112187 := rs (se 1 (by rfl) ⟨84140, by rfl⟩) R168281
theorem R112247 : Reach 112247 := rs (se 1 (by rfl) ⟨84185, by rfl⟩) R168371
theorem R112271 : Reach 112271 := rs (se 1 (by rfl) ⟨84203, by rfl⟩) R168407
theorem R112313 : Reach 112313 := rs (se 2 (by rfl) ⟨42117, by rfl⟩) R84235
theorem R276169 : Reach 276169 := rs (se 2 (by rfl) ⟨103563, by rfl⟩) R207127
theorem R702209 : Reach 702209 := rs (se 2 (by rfl) ⟨263328, by rfl⟩) R526657
theorem R112391 : Reach 112391 := rs (se 1 (by rfl) ⟨84293, by rfl⟩) R168587
theorem R374543 : Reach 374543 := rs (se 1 (by rfl) ⟨280907, by rfl⟩) R561815
theorem R112427 : Reach 112427 := rs (se 1 (by rfl) ⟨84320, by rfl⟩) R168641
theorem R472985 : Reach 472985 := rs (se 2 (by rfl) ⟨177369, by rfl⟩) R354739
theorem R112655 : Reach 112655 := rs (se 1 (by rfl) ⟨84491, by rfl⟩) R168983
theorem R473111 : Reach 473111 := rs (se 1 (by rfl) ⟨354833, by rfl⟩) R709667
theorem R243755 : Reach 243755 := rs (se 1 (by rfl) ⟨182816, by rfl⟩) R365633
theorem R80059 : Reach 80059 := rs (se 1 (by rfl) ⟨60044, by rfl⟩) R120089
theorem R211319 : Reach 211319 := rs (se 1 (by rfl) ⟨158489, by rfl⟩) R316979
theorem R80527 : Reach 80527 := rs (se 1 (by rfl) ⟨60395, by rfl⟩) R120791
theorem R1915811 : Reach 1915811 := rs (se 1 (by rfl) ⟨1436858, by rfl⟩) R2873717
theorem R113707 : Reach 113707 := rs (se 1 (by rfl) ⟨85280, by rfl⟩) R170561
theorem R81031 : Reach 81031 := rs (se 1 (by rfl) ⟨60773, by rfl⟩) R121547
theorem R376001 : Reach 376001 := rs (se 2 (by rfl) ⟨141000, by rfl⟩) R282001
theorem R277705 : Reach 277705 := rs (se 2 (by rfl) ⟨104139, by rfl⟩) R208279
theorem R408833 : Reach 408833 := rs (se 2 (by rfl) ⟨153312, by rfl⟩) R306625
theorem R867617 : Reach 867617 := rs (se 2 (by rfl) ⟨325356, by rfl⟩) R650713
theorem R81211 : Reach 81211 := rs (se 1 (by rfl) ⟨60908, by rfl⟩) R121817
theorem R245051 : Reach 245051 := rs (se 1 (by rfl) ⟨183788, by rfl⟩) R367577
theorem R310675 : Reach 310675 := rs (se 1 (by rfl) ⟨233006, by rfl⟩) R466013
theorem R81595 : Reach 81595 := rs (se 1 (by rfl) ⟨61196, by rfl⟩) R122393
theorem R540431 : Reach 540431 := rs (se 1 (by rfl) ⟨405323, by rfl⟩) R810647
theorem R81679 : Reach 81679 := rs (se 1 (by rfl) ⟨61259, by rfl⟩) R122519
theorem R245537 : Reach 245537 := rs (se 2 (by rfl) ⟨92076, by rfl⟩) R184153
theorem R180083 : Reach 180083 := rs (se 1 (by rfl) ⟨135062, by rfl⟩) R270125
theorem R278387 : Reach 278387 := rs (se 1 (by rfl) ⟨208790, by rfl⟩) R417581
theorem R180103 : Reach 180103 := rs (se 1 (by rfl) ⟨135077, by rfl⟩) R270155
theorem R638873 : Reach 638873 := rs (se 2 (by rfl) ⟨239577, by rfl⟩) R479155
theorem R180377 : Reach 180377 := rs (se 2 (by rfl) ⟨67641, by rfl⟩) R135283
theorem R82183 : Reach 82183 := rs (se 1 (by rfl) ⟨61637, by rfl⟩) R123275
theorem R180539 : Reach 180539 := rs (se 1 (by rfl) ⟨135404, by rfl⟩) R270809
theorem R246131 : Reach 246131 := rs (se 1 (by rfl) ⟨184598, by rfl⟩) R369197
theorem R82363 : Reach 82363 := rs (se 1 (by rfl) ⟨61772, by rfl⟩) R123545
theorem R377297 : Reach 377297 := rs (se 2 (by rfl) ⟨141486, by rfl⟩) R282973
theorem R180751 : Reach 180751 := rs (se 1 (by rfl) ⟨135563, by rfl⟩) R271127
theorem R181025 : Reach 181025 := rs (se 2 (by rfl) ⟨67884, by rfl⟩) R135769
theorem R213803 : Reach 213803 := rs (se 1 (by rfl) ⟨160352, by rfl⟩) R320705
theorem R770867 : Reach 770867 := rs (se 1 (by rfl) ⟨578150, by rfl⟩) R1156301
theorem R82831 : Reach 82831 := rs (se 1 (by rfl) ⟨62123, by rfl⟩) R124247
theorem R508835 : Reach 508835 := rs (se 1 (by rfl) ⟨381626, by rfl⟩) R763253
theorem R312331 : Reach 312331 := rs (se 1 (by rfl) ⟨234248, by rfl⟩) R468497
theorem R2114693 : Reach 2114693 := rs (se 4 (by rfl) ⟨198252, by rfl⟩) R396505
theorem R83335 : Reach 83335 := rs (se 1 (by rfl) ⟨62501, by rfl⟩) R125003
theorem R411065 : Reach 411065 := rs (se 2 (by rfl) ⟨154149, by rfl⟩) R308299
theorem R476675 : Reach 476675 := rs (se 1 (by rfl) ⟨357506, by rfl⟩) R715013
theorem R83515 : Reach 83515 := rs (se 1 (by rfl) ⟨62636, by rfl⟩) R125273
theorem R345667 : Reach 345667 := rs (se 1 (by rfl) ⟨259250, by rfl⟩) R518501
theorem R1754693 : Reach 1754693 := rs (se 4 (by rfl) ⟨164502, by rfl⟩) R329005
theorem R182027 : Reach 182027 := rs (se 1 (by rfl) ⟨136520, by rfl⟩) R273041
theorem R345991 : Reach 345991 := rs (se 1 (by rfl) ⟨259493, by rfl⟩) R518987
theorem R280529 : Reach 280529 := rs (se 2 (by rfl) ⟨105198, by rfl⟩) R210397
theorem R83983 : Reach 83983 := rs (se 1 (by rfl) ⟨62987, by rfl⟩) R125975
theorem R280847 : Reach 280847 := rs (se 1 (by rfl) ⟨210635, by rfl⟩) R421271
theorem R84343 : Reach 84343 := rs (se 1 (by rfl) ⟨63257, by rfl⟩) R126515
theorem R182675 : Reach 182675 := rs (se 1 (by rfl) ⟨137006, by rfl⟩) R274013
theorem R84487 : Reach 84487 := rs (se 1 (by rfl) ⟨63365, by rfl⟩) R126731
theorem R379403 : Reach 379403 := rs (se 1 (by rfl) ⟨284552, by rfl⟩) R569105
theorem R379565 : Reach 379565 := rs (se 3 (by rfl) ⟨71168, by rfl⟩) R142337
theorem R182969 : Reach 182969 := rs (se 2 (by rfl) ⟨68613, by rfl⟩) R137227
theorem R248723 : Reach 248723 := rs (se 1 (by rfl) ⟨186542, by rfl⟩) R373085
theorem R805949 : Reach 805949 := rs (se 3 (by rfl) ⟨151115, by rfl⟩) R302231
theorem R183667 : Reach 183667 := rs (se 1 (by rfl) ⟨137750, by rfl⟩) R275501
theorem R118201 : Reach 118201 := rs (se 2 (by rfl) ⟨44325, by rfl⟩) R88651
theorem R183809 : Reach 183809 := rs (se 2 (by rfl) ⟨68928, by rfl⟩) R137857
theorem R413207 : Reach 413207 := rs (se 1 (by rfl) ⟨309905, by rfl⟩) R619811
theorem R806593 : Reach 806593 := rs (se 2 (by rfl) ⟨302472, by rfl⟩) R604945
theorem R249601 : Reach 249601 := rs (se 2 (by rfl) ⟨93600, by rfl⟩) R187201
theorem R184265 : Reach 184265 := rs (se 2 (by rfl) ⟨69099, by rfl⟩) R138199
theorem R413707 : Reach 413707 := rs (se 1 (by rfl) ⟨310280, by rfl⟩) R620561
theorem R250127 : Reach 250127 := rs (se 1 (by rfl) ⟨187595, by rfl⟩) R375191
theorem R184619 : Reach 184619 := rs (se 1 (by rfl) ⟨138464, by rfl⟩) R276929
theorem R807353 : Reach 807353 := rs (se 2 (by rfl) ⟨302757, by rfl⟩) R605515
theorem R250397 : Reach 250397 := rs (se 3 (by rfl) ⟨46949, by rfl⟩) R93899
theorem R479773 : Reach 479773 := rs (se 3 (by rfl) ⟨89957, by rfl⟩) R179915
theorem R119431 : Reach 119431 := rs (se 1 (by rfl) ⟨89573, by rfl⟩) R179147
theorem R348845 : Reach 348845 := rs (se 3 (by rfl) ⟨65408, by rfl⟩) R130817
theorem R316295 : Reach 316295 := rs (se 1 (by rfl) ⟨237221, by rfl⟩) R474443
theorem R218123 : Reach 218123 := rs (se 1 (by rfl) ⟨163592, by rfl⟩) R327185
theorem R185611 : Reach 185611 := rs (se 1 (by rfl) ⟨139208, by rfl⟩) R278417
theorem R316705 : Reach 316705 := rs (se 2 (by rfl) ⟨118764, by rfl⟩) R237529
theorem R185753 : Reach 185753 := rs (se 2 (by rfl) ⟨69657, by rfl⟩) R139315
theorem R382429 : Reach 382429 := rs (se 3 (by rfl) ⟨71705, by rfl⟩) R143411
theorem R120379 : Reach 120379 := rs (se 1 (by rfl) ⟨90284, by rfl⟩) R180569
theorem R185915 : Reach 185915 := rs (se 1 (by rfl) ⟨139436, by rfl⟩) R278873
theorem R185971 : Reach 185971 := rs (se 1 (by rfl) ⟨139478, by rfl⟩) R278957
theorem R317047 : Reach 317047 := rs (se 1 (by rfl) ⟨237785, by rfl⟩) R475571
theorem R382657 : Reach 382657 := rs (se 2 (by rfl) ⟨143496, by rfl⟩) R286993
theorem R120521 : Reach 120521 := rs (se 2 (by rfl) ⟨45195, by rfl⟩) R90391
theorem R284417 : Reach 284417 := rs (se 2 (by rfl) ⟨106656, by rfl⟩) R213313
theorem R284431 : Reach 284431 := rs (se 1 (by rfl) ⟨213323, by rfl⟩) R426647
theorem R186259 : Reach 186259 := rs (se 1 (by rfl) ⟨139694, by rfl⟩) R279389
theorem R251801 : Reach 251801 := rs (se 2 (by rfl) ⟨94425, by rfl⟩) R188851
theorem R415691 : Reach 415691 := rs (se 1 (by rfl) ⟨311768, by rfl⟩) R623537
theorem R186401 : Reach 186401 := rs (se 2 (by rfl) ⟨69900, by rfl⟩) R139801
theorem R1399133 : Reach 1399133 := rs (se 3 (by rfl) ⟨262337, by rfl⟩) R524675
theorem R121223 : Reach 121223 := rs (se 1 (by rfl) ⟨90917, by rfl⟩) R181835
theorem R514451 : Reach 514451 := rs (se 1 (by rfl) ⟨385838, by rfl⟩) R771677
theorem R252503 : Reach 252503 := rs (se 1 (by rfl) ⟨189377, by rfl⟩) R378755
theorem R2644751 : Reach 2644751 := rs (se 1 (by rfl) ⟨1983563, by rfl⟩) R3967127
theorem R187393 : Reach 187393 := rs (se 2 (by rfl) ⟨70272, by rfl⟩) R140545
theorem R121871 : Reach 121871 := rs (se 1 (by rfl) ⟨91403, by rfl⟩) R182807
theorem R252989 : Reach 252989 := rs (se 3 (by rfl) ⟨47435, by rfl⟩) R94871
theorem R2579653 : Reach 2579653 := rs (se 4 (by rfl) ⟨241842, by rfl⟩) R483685
theorem R122411 : Reach 122411 := rs (se 1 (by rfl) ⟨91808, by rfl⟩) R183617
theorem R187991 : Reach 187991 := rs (se 1 (by rfl) ⟨140993, by rfl⟩) R281987
theorem R188203 : Reach 188203 := rs (se 1 (by rfl) ⟨141152, by rfl⟩) R282305
theorem R89915 : Reach 89915 := rs (se 1 (by rfl) ⟨67436, by rfl⟩) R134873
theorem R122809 : Reach 122809 := rs (se 2 (by rfl) ⟨46053, by rfl⟩) R92107
theorem R188345 : Reach 188345 := rs (se 2 (by rfl) ⟨70629, by rfl⟩) R141259
theorem R614411 : Reach 614411 := rs (se 1 (by rfl) ⟨460808, by rfl⟩) R921617
theorem R221195 : Reach 221195 := rs (se 1 (by rfl) ⟨165896, by rfl⟩) R331793
theorem R418081 : Reach 418081 := rs (se 2 (by rfl) ⟨156780, by rfl⟩) R313561
theorem R549179 : Reach 549179 := rs (se 1 (by rfl) ⟨411884, by rfl⟩) R823769
theorem R90487 : Reach 90487 := rs (se 1 (by rfl) ⟨67865, by rfl⟩) R135731
theorem R123511 : Reach 123511 := rs (se 1 (by rfl) ⟨92633, by rfl⟩) R185267
theorem R90811 : Reach 90811 := rs (se 1 (by rfl) ⟨68108, by rfl⟩) R136217
theorem R156431 : Reach 156431 := rs (se 1 (by rfl) ⟨117323, by rfl⟩) R234647
theorem R123707 : Reach 123707 := rs (se 1 (by rfl) ⟨92780, by rfl⟩) R185561
theorem R189337 : Reach 189337 := rs (se 2 (by rfl) ⟨71001, by rfl⟩) R142003
theorem R189499 : Reach 189499 := rs (se 1 (by rfl) ⟨142124, by rfl⟩) R284249
theorem R91307 : Reach 91307 := rs (se 1 (by rfl) ⟨68480, by rfl⟩) R136961
theorem R124105 : Reach 124105 := rs (se 2 (by rfl) ⟨46539, by rfl⟩) R93079
theorem R189641 : Reach 189641 := rs (se 2 (by rfl) ⟨71115, by rfl⟩) R142231
theorem R287981 : Reach 287981 := rs (se 3 (by rfl) ⟨53996, by rfl⟩) R107993
theorem R222551 : Reach 222551 := rs (se 1 (by rfl) ⟨166913, by rfl⟩) R333827
theorem R91535 : Reach 91535 := rs (se 1 (by rfl) ⟨68651, by rfl⟩) R137303
theorem R1598899 : Reach 1598899 := rs (se 1 (by rfl) ⟨1199174, by rfl⟩) R2398349
theorem R419357 : Reach 419357 := rs (se 3 (by rfl) ⟨78629, by rfl⟩) R157259
theorem R189985 : Reach 189985 := rs (se 2 (by rfl) ⟨71244, by rfl⟩) R142489
theorem R91783 : Reach 91783 := rs (se 1 (by rfl) ⟨68837, by rfl⟩) R137675
theorem R124807 : Reach 124807 := rs (se 1 (by rfl) ⟨93605, by rfl⟩) R187211
theorem R92279 : Reach 92279 := rs (se 1 (by rfl) ⟨69209, by rfl⟩) R138419
theorem R125129 : Reach 125129 := rs (se 2 (by rfl) ⟨46923, by rfl⟩) R93847
theorem R92431 : Reach 92431 := rs (se 1 (by rfl) ⟨69323, by rfl⟩) R138647
theorem R92603 : Reach 92603 := rs (se 1 (by rfl) ⟨69452, by rfl⟩) R138905
theorem R125455 : Reach 125455 := rs (se 1 (by rfl) ⟨94091, by rfl⟩) R188183
theorem R158507 : Reach 158507 := rs (se 1 (by rfl) ⟨118880, by rfl⟩) R237761
theorem R125995 : Reach 125995 := rs (se 1 (by rfl) ⟨94496, by rfl⟩) R188993
theorem R126137 : Reach 126137 := rs (se 2 (by rfl) ⟨47301, by rfl⟩) R94603
theorem R93575 : Reach 93575 := rs (se 1 (by rfl) ⟨70181, by rfl⟩) R140363
theorem R388979 : Reach 388979 := rs (se 1 (by rfl) ⟨291734, by rfl⟩) R583469
theorem R94223 : Reach 94223 := rs (se 1 (by rfl) ⟨70667, by rfl⟩) R141335
theorem R421955 : Reach 421955 := rs (se 1 (by rfl) ⟨316466, by rfl⟩) R632933
theorem R618785 : Reach 618785 := rs (se 2 (by rfl) ⟨232044, by rfl⟩) R464089
theorem R160147 : Reach 160147 := rs (se 1 (by rfl) ⟨120110, by rfl⟩) R240221
theorem R291281 : Reach 291281 := rs (se 2 (by rfl) ⟨109230, by rfl⟩) R218461
theorem R160271 : Reach 160271 := rs (se 1 (by rfl) ⟨120203, by rfl⟩) R240407
theorem R160289 : Reach 160289 := rs (se 2 (by rfl) ⟨60108, by rfl⟩) R120217
theorem R1372889 : Reach 1372889 := rs (se 2 (by rfl) ⟨514833, by rfl⟩) R1029667
theorem R95033 : Reach 95033 := rs (se 2 (by rfl) ⟨35637, by rfl⟩) R71275
theorem R193367 : Reach 193367 := rs (se 1 (by rfl) ⟨145025, by rfl⟩) R290051
theorem R160631 : Reach 160631 := rs (se 1 (by rfl) ⟨120473, by rfl⟩) R240947
theorem R160811 : Reach 160811 := rs (se 1 (by rfl) ⟨120608, by rfl⟩) R241217
theorem R95305 : Reach 95305 := rs (se 2 (by rfl) ⟨35739, by rfl⟩) R71479
theorem R128299 : Reach 128299 := rs (se 1 (by rfl) ⟨96224, by rfl⟩) R192449
theorem R161171 : Reach 161171 := rs (se 1 (by rfl) ⟨120878, by rfl⟩) R241757
theorem R161225 : Reach 161225 := rs (se 2 (by rfl) ⟨60459, by rfl⟩) R120919
theorem R554525 : Reach 554525 := rs (se 3 (by rfl) ⟨103973, by rfl⟩) R207947
theorem R423731 : Reach 423731 := rs (se 1 (by rfl) ⟨317798, by rfl⟩) R635597
theorem R194363 : Reach 194363 := rs (se 1 (by rfl) ⟨145772, by rfl⟩) R291545
theorem R423883 : Reach 423883 := rs (se 1 (by rfl) ⟨317912, by rfl⟩) R635825
theorem R292925 : Reach 292925 := rs (se 3 (by rfl) ⟨54923, by rfl⟩) R109847
theorem R161927 : Reach 161927 := rs (se 1 (by rfl) ⟨121445, by rfl⟩) R242891
theorem R391405 : Reach 391405 := rs (se 3 (by rfl) ⟨73388, by rfl⟩) R146777
theorem R7174453 : Reach 7174453 := rs (se 5 (by rfl) ⟨336302, by rfl⟩) R672605
theorem R162107 : Reach 162107 := rs (se 1 (by rfl) ⟨121580, by rfl⟩) R243161
theorem R162233 : Reach 162233 := rs (se 2 (by rfl) ⟨60837, by rfl⟩) R121675
theorem R129683 : Reach 129683 := rs (se 1 (by rfl) ⟨97262, by rfl⟩) R194525
theorem R162575 : Reach 162575 := rs (se 1 (by rfl) ⟨121931, by rfl⟩) R243863
theorem R391969 : Reach 391969 := rs (se 2 (by rfl) ⟨146988, by rfl⟩) R293977
theorem R162593 : Reach 162593 := rs (se 2 (by rfl) ⟨60972, by rfl⟩) R121945
theorem R523097 : Reach 523097 := rs (se 2 (by rfl) ⟨196161, by rfl⟩) R392323
theorem R195443 : Reach 195443 := rs (se 1 (by rfl) ⟨146582, by rfl⟩) R293165
theorem R228413 : Reach 228413 := rs (se 3 (by rfl) ⟨42827, by rfl⟩) R85655
theorem R162935 : Reach 162935 := rs (se 1 (by rfl) ⟨122201, by rfl⟩) R244403
theorem R425189 : Reach 425189 := rs (se 4 (by rfl) ⟨39861, by rfl⟩) R79723
theorem R163115 : Reach 163115 := rs (se 1 (by rfl) ⟨122336, by rfl⟩) R244673
theorem R130439 : Reach 130439 := rs (se 1 (by rfl) ⟨97829, by rfl⟩) R195659
theorem R163475 : Reach 163475 := rs (se 1 (by rfl) ⟨122606, by rfl⟩) R245213
theorem R425645 : Reach 425645 := rs (se 3 (by rfl) ⟨79808, by rfl⟩) R159617
theorem R163529 : Reach 163529 := rs (se 2 (by rfl) ⟨61323, by rfl⟩) R122647
theorem R98219 : Reach 98219 := rs (se 1 (by rfl) ⟨73664, by rfl⟩) R147329
theorem R589853 : Reach 589853 := rs (se 3 (by rfl) ⟨110597, by rfl⟩) R221195
theorem R164087 : Reach 164087 := rs (se 1 (by rfl) ⟨123065, by rfl⟩) R246131
theorem R721163 : Reach 721163 := rs (se 1 (by rfl) ⟨540872, by rfl⟩) R1081745
theorem R557441 : Reach 557441 := rs (se 2 (by rfl) ⟨209040, by rfl⟩) R418081
theorem R131471 : Reach 131471 := rs (se 1 (by rfl) ⟨98603, by rfl⟩) R197207
theorem R459245 : Reach 459245 := rs (se 3 (by rfl) ⟨86108, by rfl⟩) R172217
theorem R1409795 : Reach 1409795 := rs (se 1 (by rfl) ⟨1057346, by rfl⟩) R2114693
theorem R164681 : Reach 164681 := rs (se 2 (by rfl) ⟨61755, by rfl⟩) R123511
theorem R787475 : Reach 787475 := rs (se 1 (by rfl) ⟨590606, by rfl⟩) R1181213
theorem R590867 : Reach 590867 := rs (se 1 (by rfl) ⟨443150, by rfl⟩) R886301
theorem R590915 : Reach 590915 := rs (se 1 (by rfl) ⟨443186, by rfl⟩) R886373
theorem R1672433 : Reach 1672433 := rs (se 2 (by rfl) ⟨627162, by rfl⟩) R1254325
theorem R99689 : Reach 99689 := rs (se 2 (by rfl) ⟨37383, by rfl⟩) R74767
theorem R787913 : Reach 787913 := rs (se 2 (by rfl) ⟨295467, by rfl⟩) R590935
theorem R460349 : Reach 460349 := rs (se 3 (by rfl) ⟨86315, by rfl⟩) R172631
theorem R165473 : Reach 165473 := rs (se 2 (by rfl) ⟨62052, by rfl⟩) R124105
theorem R263819 : Reach 263819 := rs (se 1 (by rfl) ⟨197864, by rfl⟩) R395729
theorem R2131865 : Reach 2131865 := rs (se 2 (by rfl) ⟨799449, by rfl⟩) R1598899
theorem R165815 : Reach 165815 := rs (se 1 (by rfl) ⟨124361, by rfl⟩) R248723
theorem R395279 : Reach 395279 := rs (se 1 (by rfl) ⟨296459, by rfl⟩) R592919
theorem R460889 : Reach 460889 := rs (se 2 (by rfl) ⟨172833, by rfl⟩) R345667
theorem R461321 : Reach 461321 := rs (se 2 (by rfl) ⟨172995, by rfl⟩) R345991
theorem R166409 : Reach 166409 := rs (se 2 (by rfl) ⟨62403, by rfl⟩) R124807
theorem R363041 : Reach 363041 := rs (se 2 (by rfl) ⟨136140, by rfl⟩) R272281
theorem R166751 : Reach 166751 := rs (se 1 (by rfl) ⟨125063, by rfl⟩) R250127
theorem R166931 : Reach 166931 := rs (se 1 (by rfl) ⟨125198, by rfl⟩) R250397
theorem R167273 : Reach 167273 := rs (se 2 (by rfl) ⟨62727, by rfl⟩) R125455
theorem R200179 : Reach 200179 := rs (se 1 (by rfl) ⟨150134, by rfl⟩) R300269
theorem R462347 : Reach 462347 := rs (se 1 (by rfl) ⟨346760, by rfl⟩) R693521
theorem R200407 : Reach 200407 := rs (se 1 (by rfl) ⟨150305, by rfl⟩) R300611
theorem R167867 : Reach 167867 := rs (se 1 (by rfl) ⟨125900, by rfl⟩) R251801
theorem R167993 : Reach 167993 := rs (se 2 (by rfl) ⟨62997, by rfl⟩) R125995
theorem R168335 : Reach 168335 := rs (se 1 (by rfl) ⟨126251, by rfl⟩) R252503
theorem R528905 : Reach 528905 := rs (se 2 (by rfl) ⟨198339, by rfl⟩) R396679
theorem R168659 : Reach 168659 := rs (se 1 (by rfl) ⟨126494, by rfl⟩) R252989
theorem R332801 : Reach 332801 := rs (se 2 (by rfl) ⟨124800, by rfl⟩) R249601
theorem R595343 : Reach 595343 := rs (se 1 (by rfl) ⟨446507, by rfl⟩) R893015
theorem R71131 : Reach 71131 := rs (se 1 (by rfl) ⟨53348, by rfl⟩) R106697
theorem R71207 : Reach 71207 := rs (se 1 (by rfl) ⟨53405, by rfl⟩) R106811
theorem R366119 : Reach 366119 := rs (se 1 (by rfl) ⟨274589, by rfl⟩) R549179
theorem R71247 : Reach 71247 := rs (se 1 (by rfl) ⟨53435, by rfl⟩) R106871
theorem R71263 : Reach 71263 := rs (se 1 (by rfl) ⟨53447, by rfl⟩) R106895
theorem R71291 : Reach 71291 := rs (se 1 (by rfl) ⟨53468, by rfl⟩) R106937
theorem R71343 : Reach 71343 := rs (se 1 (by rfl) ⟨53507, by rfl⟩) R107015
theorem R71367 : Reach 71367 := rs (se 1 (by rfl) ⟨53525, by rfl⟩) R107051
theorem R71387 : Reach 71387 := rs (se 1 (by rfl) ⟨53540, by rfl⟩) R107081
theorem R71463 : Reach 71463 := rs (se 1 (by rfl) ⟨53597, by rfl⟩) R107195
theorem R71503 : Reach 71503 := rs (se 1 (by rfl) ⟨53627, by rfl⟩) R107255
theorem R71519 : Reach 71519 := rs (se 1 (by rfl) ⟨53639, by rfl⟩) R107279
theorem R71547 : Reach 71547 := rs (se 1 (by rfl) ⟨53660, by rfl⟩) R107321
theorem R71599 : Reach 71599 := rs (se 1 (by rfl) ⟨53699, by rfl⟩) R107399
theorem R137143 : Reach 137143 := rs (se 1 (by rfl) ⟨102857, by rfl⟩) R205715
theorem R71623 : Reach 71623 := rs (se 1 (by rfl) ⟨53717, by rfl⟩) R107435
theorem R71643 : Reach 71643 := rs (se 1 (by rfl) ⟨53732, by rfl⟩) R107465
theorem R71719 : Reach 71719 := rs (se 1 (by rfl) ⟨53789, by rfl⟩) R107579
theorem R71759 : Reach 71759 := rs (se 1 (by rfl) ⟨53819, by rfl⟩) R107639
theorem R71775 : Reach 71775 := rs (se 1 (by rfl) ⟨53831, by rfl⟩) R107663
theorem R465011 : Reach 465011 := rs (se 1 (by rfl) ⟨348758, by rfl⟩) R697517
theorem R71803 : Reach 71803 := rs (se 1 (by rfl) ⟨53852, by rfl⟩) R107705
theorem R235673 : Reach 235673 := rs (se 2 (by rfl) ⟨88377, by rfl⟩) R176755
theorem R71855 : Reach 71855 := rs (se 1 (by rfl) ⟨53891, by rfl⟩) R107783
theorem R71879 : Reach 71879 := rs (se 1 (by rfl) ⟨53909, by rfl⟩) R107819
theorem R71899 : Reach 71899 := rs (se 1 (by rfl) ⟨53924, by rfl⟩) R107849
theorem R71975 : Reach 71975 := rs (se 1 (by rfl) ⟨53981, by rfl⟩) R107963
theorem R72015 : Reach 72015 := rs (se 1 (by rfl) ⟨54011, by rfl⟩) R108023
theorem R72031 : Reach 72031 := rs (se 1 (by rfl) ⟨54023, by rfl⟩) R108047
theorem R72059 : Reach 72059 := rs (se 1 (by rfl) ⟨54044, by rfl⟩) R108089
theorem R72111 : Reach 72111 := rs (se 1 (by rfl) ⟨54083, by rfl⟩) R108167
theorem R72135 : Reach 72135 := rs (se 1 (by rfl) ⟨54101, by rfl⟩) R108203
theorem R72155 : Reach 72155 := rs (se 1 (by rfl) ⟨54116, by rfl⟩) R108233
theorem R72231 : Reach 72231 := rs (se 1 (by rfl) ⟨54173, by rfl⟩) R108347
theorem R72271 : Reach 72271 := rs (se 1 (by rfl) ⟨54203, by rfl⟩) R108407
theorem R72287 : Reach 72287 := rs (se 1 (by rfl) ⟨54215, by rfl⟩) R108431
theorem R72315 : Reach 72315 := rs (se 1 (by rfl) ⟨54236, by rfl⟩) R108473
theorem R72367 : Reach 72367 := rs (se 1 (by rfl) ⟨54275, by rfl⟩) R108551
theorem R72391 : Reach 72391 := rs (se 1 (by rfl) ⟨54293, by rfl⟩) R108587
theorem R72411 : Reach 72411 := rs (se 1 (by rfl) ⟨54308, by rfl⟩) R108617
theorem R72487 : Reach 72487 := rs (se 1 (by rfl) ⟨54365, by rfl⟩) R108731
theorem R72527 : Reach 72527 := rs (se 1 (by rfl) ⟨54395, by rfl⟩) R108791
theorem R72543 : Reach 72543 := rs (se 1 (by rfl) ⟨54407, by rfl⟩) R108815
theorem R72571 : Reach 72571 := rs (se 1 (by rfl) ⟨54428, by rfl⟩) R108857
theorem R72623 : Reach 72623 := rs (se 1 (by rfl) ⟨54467, by rfl⟩) R108935
theorem R72647 : Reach 72647 := rs (se 1 (by rfl) ⟨54485, by rfl⟩) R108971
theorem R72667 : Reach 72667 := rs (se 1 (by rfl) ⟨54500, by rfl⟩) R109001
theorem R72743 : Reach 72743 := rs (se 1 (by rfl) ⟨54557, by rfl⟩) R109115
theorem R171065 : Reach 171065 := rs (se 2 (by rfl) ⟨64149, by rfl⟩) R128299
theorem R72783 : Reach 72783 := rs (se 1 (by rfl) ⟨54587, by rfl⟩) R109175
theorem R72799 : Reach 72799 := rs (se 1 (by rfl) ⟨54599, by rfl⟩) R109199
theorem R72827 : Reach 72827 := rs (se 1 (by rfl) ⟨54620, by rfl⟩) R109241
theorem R72879 : Reach 72879 := rs (se 1 (by rfl) ⟨54659, by rfl⟩) R109319
theorem R72903 : Reach 72903 := rs (se 1 (by rfl) ⟨54677, by rfl⟩) R109355
theorem R105671 : Reach 105671 := rs (se 1 (by rfl) ⟨79253, by rfl⟩) R158507
theorem R72923 : Reach 72923 := rs (se 1 (by rfl) ⟨54692, by rfl⟩) R109385
theorem R72999 : Reach 72999 := rs (se 1 (by rfl) ⟨54749, by rfl⟩) R109499
theorem R73039 : Reach 73039 := rs (se 1 (by rfl) ⟨54779, by rfl⟩) R109559
theorem R73055 : Reach 73055 := rs (se 1 (by rfl) ⟨54791, by rfl⟩) R109583
theorem R138601 : Reach 138601 := rs (se 2 (by rfl) ⟨51975, by rfl⟩) R103951
theorem R73083 : Reach 73083 := rs (se 1 (by rfl) ⟨54812, by rfl⟩) R109625
theorem R73135 : Reach 73135 := rs (se 1 (by rfl) ⟨54851, by rfl⟩) R109703
theorem R73159 : Reach 73159 := rs (se 1 (by rfl) ⟨54869, by rfl⟩) R109739
theorem R73179 : Reach 73179 := rs (se 1 (by rfl) ⟨54884, by rfl⟩) R109769
theorem R73255 : Reach 73255 := rs (se 1 (by rfl) ⟨54941, by rfl⟩) R109883
theorem R73295 : Reach 73295 := rs (se 1 (by rfl) ⟨54971, by rfl⟩) R109943
theorem R73311 : Reach 73311 := rs (se 1 (by rfl) ⟨54983, by rfl⟩) R109967
theorem R368225 : Reach 368225 := rs (se 2 (by rfl) ⟨138084, by rfl⟩) R276169
theorem R73339 : Reach 73339 := rs (se 1 (by rfl) ⟨55004, by rfl⟩) R110009
theorem R269963 : Reach 269963 := rs (se 1 (by rfl) ⟨202472, by rfl⟩) R404945
theorem R73391 : Reach 73391 := rs (se 1 (by rfl) ⟨55043, by rfl⟩) R110087
theorem R73415 : Reach 73415 := rs (se 1 (by rfl) ⟨55061, by rfl⟩) R110123
theorem R73435 : Reach 73435 := rs (se 1 (by rfl) ⟨55076, by rfl⟩) R110153
theorem R73511 : Reach 73511 := rs (se 1 (by rfl) ⟨55133, by rfl⟩) R110267
theorem R73551 : Reach 73551 := rs (se 1 (by rfl) ⟨55163, by rfl⟩) R110327
theorem R73567 : Reach 73567 := rs (se 1 (by rfl) ⟨55175, by rfl⟩) R110351
theorem R73595 : Reach 73595 := rs (se 1 (by rfl) ⟨55196, by rfl⟩) R110393
theorem R73647 : Reach 73647 := rs (se 1 (by rfl) ⟨55235, by rfl⟩) R110471
theorem R565177 : Reach 565177 := rs (se 2 (by rfl) ⟨211941, by rfl⟩) R423883
theorem R73671 : Reach 73671 := rs (se 1 (by rfl) ⟨55253, by rfl⟩) R110507
theorem R73691 : Reach 73691 := rs (se 1 (by rfl) ⟨55268, by rfl⟩) R110537
theorem R270337 : Reach 270337 := rs (se 2 (by rfl) ⟨101376, by rfl⟩) R202753
theorem R73767 : Reach 73767 := rs (se 1 (by rfl) ⟨55325, by rfl⟩) R110651
theorem R794701 : Reach 794701 := rs (se 3 (by rfl) ⟨149006, by rfl⟩) R298013
theorem R73807 : Reach 73807 := rs (se 1 (by rfl) ⟨55355, by rfl⟩) R110711
theorem R73823 : Reach 73823 := rs (se 1 (by rfl) ⟨55367, by rfl⟩) R110735
theorem R532595 : Reach 532595 := rs (se 1 (by rfl) ⟨399446, by rfl⟩) R798893
theorem R73851 : Reach 73851 := rs (se 1 (by rfl) ⟨55388, by rfl⟩) R110777
theorem R73903 : Reach 73903 := rs (se 1 (by rfl) ⟨55427, by rfl⟩) R110855
theorem R73927 : Reach 73927 := rs (se 1 (by rfl) ⟨55445, by rfl⟩) R110891
theorem R139475 : Reach 139475 := rs (se 1 (by rfl) ⟨104606, by rfl⟩) R209213
theorem R73947 : Reach 73947 := rs (se 1 (by rfl) ⟨55460, by rfl⟩) R110921
theorem R106745 : Reach 106745 := rs (se 2 (by rfl) ⟨40029, by rfl⟩) R80059
theorem R74023 : Reach 74023 := rs (se 1 (by rfl) ⟨55517, by rfl⟩) R111035
theorem R74063 : Reach 74063 := rs (se 1 (by rfl) ⟨55547, by rfl⟩) R111095
theorem R106847 : Reach 106847 := rs (se 1 (by rfl) ⟨80135, by rfl⟩) R160271
theorem R74079 : Reach 74079 := rs (se 1 (by rfl) ⟨55559, by rfl⟩) R111119
theorem R106859 : Reach 106859 := rs (se 1 (by rfl) ⟨80144, by rfl⟩) R160289
theorem R74107 : Reach 74107 := rs (se 1 (by rfl) ⟨55580, by rfl⟩) R111161
theorem R74159 : Reach 74159 := rs (se 1 (by rfl) ⟨55619, by rfl⟩) R111239
theorem R74183 : Reach 74183 := rs (se 1 (by rfl) ⟨55637, by rfl⟩) R111275
theorem R74203 : Reach 74203 := rs (se 1 (by rfl) ⟨55652, by rfl⟩) R111305
theorem R74279 : Reach 74279 := rs (se 1 (by rfl) ⟨55709, by rfl⟩) R111419
theorem R107087 : Reach 107087 := rs (se 1 (by rfl) ⟨80315, by rfl⟩) R160631
theorem R74319 : Reach 74319 := rs (se 1 (by rfl) ⟨55739, by rfl⟩) R111479
theorem R74335 : Reach 74335 := rs (se 1 (by rfl) ⟨55751, by rfl⟩) R111503
theorem R74363 : Reach 74363 := rs (se 1 (by rfl) ⟨55772, by rfl⟩) R111545
theorem R74415 : Reach 74415 := rs (se 1 (by rfl) ⟨55811, by rfl⟩) R111623
theorem R107207 : Reach 107207 := rs (se 1 (by rfl) ⟨80405, by rfl⟩) R160811
theorem R74439 : Reach 74439 := rs (se 1 (by rfl) ⟨55829, by rfl⟩) R111659
theorem R74459 : Reach 74459 := rs (se 1 (by rfl) ⟨55844, by rfl⟩) R111689
theorem R271097 : Reach 271097 := rs (se 2 (by rfl) ⟨101661, by rfl⟩) R203323
theorem R74535 : Reach 74535 := rs (se 1 (by rfl) ⟨55901, by rfl⟩) R111803
theorem R140105 : Reach 140105 := rs (se 2 (by rfl) ⟨52539, by rfl⟩) R105079
theorem R74575 : Reach 74575 := rs (se 1 (by rfl) ⟨55931, by rfl⟩) R111863
theorem R74591 : Reach 74591 := rs (se 1 (by rfl) ⟨55943, by rfl⟩) R111887
theorem R107369 : Reach 107369 := rs (se 2 (by rfl) ⟨40263, by rfl⟩) R80527
theorem R74619 : Reach 74619 := rs (se 1 (by rfl) ⟨55964, by rfl⟩) R111929
theorem R74671 : Reach 74671 := rs (se 1 (by rfl) ⟨56003, by rfl⟩) R112007
theorem R107447 : Reach 107447 := rs (se 1 (by rfl) ⟨80585, by rfl⟩) R161171
theorem R74695 : Reach 74695 := rs (se 1 (by rfl) ⟨56021, by rfl⟩) R112043
theorem R107483 : Reach 107483 := rs (se 1 (by rfl) ⟨80612, by rfl⟩) R161225
theorem R74715 : Reach 74715 := rs (se 1 (by rfl) ⟨56036, by rfl⟩) R112073
theorem R369683 : Reach 369683 := rs (se 1 (by rfl) ⟨277262, by rfl⟩) R554525
theorem R74791 : Reach 74791 := rs (se 1 (by rfl) ⟨56093, by rfl⟩) R112187
theorem R74831 : Reach 74831 := rs (se 1 (by rfl) ⟨56123, by rfl⟩) R112247
theorem R74847 : Reach 74847 := rs (se 1 (by rfl) ⟨56135, by rfl⟩) R112271
theorem R74875 : Reach 74875 := rs (se 1 (by rfl) ⟨56156, by rfl⟩) R112313
theorem R468139 : Reach 468139 := rs (se 1 (by rfl) ⟨351104, by rfl⟩) R702209
theorem R74927 : Reach 74927 := rs (se 1 (by rfl) ⟨56195, by rfl⟩) R112391
theorem R74951 : Reach 74951 := rs (se 1 (by rfl) ⟨56213, by rfl⟩) R112427
theorem R75103 : Reach 75103 := rs (se 1 (by rfl) ⟨56327, by rfl⟩) R112655
theorem R107951 : Reach 107951 := rs (se 1 (by rfl) ⟨80963, by rfl⟩) R161927
theorem R108041 : Reach 108041 := rs (se 2 (by rfl) ⟨40515, by rfl⟩) R81031
theorem R108071 : Reach 108071 := rs (se 1 (by rfl) ⟨81053, by rfl⟩) R162107
theorem R140879 : Reach 140879 := rs (se 1 (by rfl) ⟨105659, by rfl⟩) R211319
theorem R370273 : Reach 370273 := rs (se 2 (by rfl) ⟨138852, by rfl⟩) R277705
theorem R108155 : Reach 108155 := rs (se 1 (by rfl) ⟨81116, by rfl⟩) R162233
theorem R108281 : Reach 108281 := rs (se 2 (by rfl) ⟨40605, by rfl⟩) R81211
theorem R108383 : Reach 108383 := rs (se 1 (by rfl) ⟨81287, by rfl⟩) R162575
theorem R108395 : Reach 108395 := rs (se 1 (by rfl) ⟨81296, by rfl⟩) R162593
theorem R108623 : Reach 108623 := rs (se 1 (by rfl) ⟨81467, by rfl⟩) R162935
theorem R239773 : Reach 239773 := rs (se 3 (by rfl) ⟨44957, by rfl⟩) R89915
theorem R272555 : Reach 272555 := rs (se 1 (by rfl) ⟨204416, by rfl⟩) R408833
theorem R108743 : Reach 108743 := rs (se 1 (by rfl) ⟨81557, by rfl⟩) R163115
theorem R108793 : Reach 108793 := rs (se 2 (by rfl) ⟨40797, by rfl⟩) R81595
theorem R3909941 : Reach 3909941 := rs (se 5 (by rfl) ⟨183278, by rfl⟩) R366557
theorem R108905 : Reach 108905 := rs (se 2 (by rfl) ⟨40839, by rfl⟩) R81679
theorem R108983 : Reach 108983 := rs (se 1 (by rfl) ⟨81737, by rfl⟩) R163475
theorem R109019 : Reach 109019 := rs (se 1 (by rfl) ⟨81764, by rfl⟩) R163529
theorem R240137 : Reach 240137 := rs (se 2 (by rfl) ⟨90051, by rfl⟩) R180103
theorem R109487 : Reach 109487 := rs (se 1 (by rfl) ⟨82115, by rfl⟩) R164231
theorem R109577 : Reach 109577 := rs (se 2 (by rfl) ⟨41091, by rfl⟩) R82183
theorem R109607 : Reach 109607 := rs (se 1 (by rfl) ⟨82205, by rfl⟩) R164411
theorem R109691 : Reach 109691 := rs (se 1 (by rfl) ⟨82268, by rfl⟩) R164537
theorem R142535 : Reach 142535 := rs (se 1 (by rfl) ⟨106901, by rfl⟩) R213803
theorem R109817 : Reach 109817 := rs (se 2 (by rfl) ⟨41181, by rfl⟩) R82363
theorem R339223 : Reach 339223 := rs (se 1 (by rfl) ⟨254417, by rfl⟩) R508835
theorem R273725 : Reach 273725 := rs (se 3 (by rfl) ⟨51323, by rfl⟩) R102647
theorem R109919 : Reach 109919 := rs (se 1 (by rfl) ⟨82439, by rfl⟩) R164879
theorem R241001 : Reach 241001 := rs (se 2 (by rfl) ⟨90375, by rfl⟩) R180751
theorem R109931 : Reach 109931 := rs (se 1 (by rfl) ⟨82448, by rfl⟩) R164897
theorem R306575 : Reach 306575 := rs (se 1 (by rfl) ⟨229931, by rfl⟩) R459863
theorem R110159 : Reach 110159 := rs (se 1 (by rfl) ⟨82619, by rfl⟩) R165239
theorem R274043 : Reach 274043 := rs (se 1 (by rfl) ⟨205532, by rfl⟩) R411065
theorem R110279 : Reach 110279 := rs (se 1 (by rfl) ⟨82709, by rfl⟩) R165419
theorem R110441 : Reach 110441 := rs (se 2 (by rfl) ⟨41415, by rfl⟩) R82831
theorem R372599 : Reach 372599 := rs (se 1 (by rfl) ⟨279449, by rfl⟩) R558899
theorem R176033 : Reach 176033 := rs (se 2 (by rfl) ⟨66012, by rfl⟩) R132025
theorem R110519 : Reach 110519 := rs (se 1 (by rfl) ⟨82889, by rfl⟩) R165779
theorem R241595 : Reach 241595 := rs (se 1 (by rfl) ⟨181196, by rfl⟩) R362393
theorem R110555 : Reach 110555 := rs (se 1 (by rfl) ⟨82916, by rfl⟩) R165833
theorem R1224719 : Reach 1224719 := rs (se 1 (by rfl) ⟨918539, by rfl⟩) R1837079
theorem R111023 : Reach 111023 := rs (se 1 (by rfl) ⟨83267, by rfl⟩) R166535
theorem R930253 : Reach 930253 := rs (se 3 (by rfl) ⟨174422, by rfl⟩) R348845
theorem R111113 : Reach 111113 := rs (se 2 (by rfl) ⟨41667, by rfl⟩) R83335
theorem R111143 : Reach 111143 := rs (se 1 (by rfl) ⟨83357, by rfl⟩) R166715
theorem R111227 : Reach 111227 := rs (se 1 (by rfl) ⟨83420, by rfl⟩) R166841
theorem R537299 : Reach 537299 := rs (se 1 (by rfl) ⟨402974, by rfl⟩) R805949
theorem R111353 : Reach 111353 := rs (se 2 (by rfl) ⟨41757, by rfl⟩) R83515
theorem R10138385 : Reach 10138385 := rs (se 2 (by rfl) ⟨3801894, by rfl⟩) R7603789
theorem R111455 : Reach 111455 := rs (se 1 (by rfl) ⟨83591, by rfl⟩) R167183
theorem R111467 : Reach 111467 := rs (se 1 (by rfl) ⟨83600, by rfl⟩) R167201
theorem R275471 : Reach 275471 := rs (se 1 (by rfl) ⟨206603, by rfl⟩) R413207
theorem R111695 : Reach 111695 := rs (se 1 (by rfl) ⟨83771, by rfl⟩) R167543
theorem R111815 : Reach 111815 := rs (se 1 (by rfl) ⟨83861, by rfl⟩) R167723
theorem R10073315 : Reach 10073315 := rs (se 1 (by rfl) ⟨7554986, by rfl⟩) R15109973
theorem R111977 : Reach 111977 := rs (se 2 (by rfl) ⟨41991, by rfl⟩) R83983
theorem R112055 : Reach 112055 := rs (se 1 (by rfl) ⟨84041, by rfl⟩) R168083
theorem R112091 : Reach 112091 := rs (se 1 (by rfl) ⟨84068, by rfl⟩) R168137
theorem R243323 : Reach 243323 := rs (se 1 (by rfl) ⟨182492, by rfl⟩) R364985
theorem R538235 : Reach 538235 := rs (se 1 (by rfl) ⟨403676, by rfl⟩) R807353
theorem R243485 : Reach 243485 := rs (se 3 (by rfl) ⟨45653, by rfl⟩) R91307
theorem R309035 : Reach 309035 := rs (se 1 (by rfl) ⟨231776, by rfl⟩) R463553
theorem R112457 : Reach 112457 := rs (se 2 (by rfl) ⟨42171, by rfl⟩) R84343
theorem R210863 : Reach 210863 := rs (se 1 (by rfl) ⟨158147, by rfl⟩) R316295
theorem R112559 : Reach 112559 := rs (se 1 (by rfl) ⟨84419, by rfl⟩) R168839
theorem R112571 : Reach 112571 := rs (se 1 (by rfl) ⟨84428, by rfl⟩) R168857
theorem R145415 : Reach 145415 := rs (se 1 (by rfl) ⟨109061, by rfl⟩) R218123
theorem R112649 : Reach 112649 := rs (se 2 (by rfl) ⟨42243, by rfl⟩) R84487
theorem R112679 : Reach 112679 := rs (se 1 (by rfl) ⟨84509, by rfl⟩) R169019
theorem R80347 : Reach 80347 := rs (se 1 (by rfl) ⟨60260, by rfl⟩) R120521
theorem R244187 : Reach 244187 := rs (se 1 (by rfl) ⟨183140, by rfl⟩) R366281
theorem R277127 : Reach 277127 := rs (se 1 (by rfl) ⟨207845, by rfl⟩) R415691
theorem R1850201 : Reach 1850201 := rs (se 2 (by rfl) ⟨693825, by rfl⟩) R1387651
theorem R277357 : Reach 277357 := rs (se 3 (by rfl) ⟨52004, by rfl⟩) R104009
theorem R932755 : Reach 932755 := rs (se 1 (by rfl) ⟨699566, by rfl⟩) R1399133
theorem R80815 : Reach 80815 := rs (se 1 (by rfl) ⟨60611, by rfl⟩) R121223
theorem R342967 : Reach 342967 := rs (se 1 (by rfl) ⟨257225, by rfl⟩) R514451
theorem R244889 : Reach 244889 := rs (se 2 (by rfl) ⟨91833, by rfl⟩) R183667
theorem R81247 : Reach 81247 := rs (se 1 (by rfl) ⟨60935, by rfl⟩) R121871
theorem R278113 : Reach 278113 := rs (se 2 (by rfl) ⟨104292, by rfl⟩) R208585
theorem R81607 : Reach 81607 := rs (se 1 (by rfl) ⟨61205, by rfl⟩) R122411
theorem R310999 : Reach 310999 := rs (se 1 (by rfl) ⟨233249, by rfl⟩) R466499
theorem R311033 : Reach 311033 := rs (se 2 (by rfl) ⟨116637, by rfl⟩) R233275
theorem R147361 : Reach 147361 := rs (se 2 (by rfl) ⟨55260, by rfl⟩) R110521
theorem R409607 : Reach 409607 := rs (se 1 (by rfl) ⟨307205, by rfl⟩) R614411
theorem R278585 : Reach 278585 := rs (se 2 (by rfl) ⟨104469, by rfl⟩) R208939
theorem R114767 : Reach 114767 := rs (se 1 (by rfl) ⟨86075, by rfl⟩) R172151
theorem R606437 : Reach 606437 := rs (se 4 (by rfl) ⟨56853, by rfl⟩) R113707
theorem R246077 : Reach 246077 := rs (se 3 (by rfl) ⟨46139, by rfl⟩) R92279
theorem R1982789 : Reach 1982789 := rs (se 4 (by rfl) ⟨185886, by rfl⟩) R371773
theorem R213529 : Reach 213529 := rs (se 2 (by rfl) ⟨80073, by rfl⟩) R160147
theorem R82471 : Reach 82471 := rs (se 1 (by rfl) ⟨61853, by rfl⟩) R123707
theorem R1557143 : Reach 1557143 := rs (se 1 (by rfl) ⟨1167857, by rfl⟩) R2335715
theorem R639697 : Reach 639697 := rs (se 2 (by rfl) ⟨239886, by rfl⟩) R479773
theorem R148367 : Reach 148367 := rs (se 1 (by rfl) ⟨111275, by rfl⟩) R222551
theorem R377783 : Reach 377783 := rs (se 1 (by rfl) ⟨283337, by rfl⟩) R566675
theorem R279571 : Reach 279571 := rs (se 1 (by rfl) ⟨209678, by rfl⟩) R419357
theorem R246941 : Reach 246941 := rs (se 3 (by rfl) ⟨46301, by rfl⟩) R92603
theorem R541889 : Reach 541889 := rs (se 2 (by rfl) ⟨203208, by rfl⟩) R406417
theorem R181723 : Reach 181723 := rs (se 1 (by rfl) ⟨136292, by rfl⟩) R272585
theorem R83419 : Reach 83419 := rs (se 1 (by rfl) ⟨62564, by rfl⟩) R125129
theorem R247481 : Reach 247481 := rs (se 2 (by rfl) ⟨92805, by rfl⟩) R185611
theorem R509905 : Reach 509905 := rs (se 2 (by rfl) ⟨191214, by rfl⟩) R382429
theorem R182351 : Reach 182351 := rs (se 1 (by rfl) ⟨136763, by rfl⟩) R273527
theorem R84091 : Reach 84091 := rs (se 1 (by rfl) ⟨63068, by rfl⟩) R126137
theorem R247961 : Reach 247961 := rs (se 2 (by rfl) ⟨92985, by rfl⟩) R185971
theorem R510209 : Reach 510209 := rs (se 2 (by rfl) ⟨191328, by rfl⟩) R382657
theorem R248075 : Reach 248075 := rs (se 1 (by rfl) ⟨186056, by rfl⟩) R372113
theorem R379241 : Reach 379241 := rs (se 2 (by rfl) ⟨142215, by rfl⟩) R284431
theorem R248345 : Reach 248345 := rs (se 2 (by rfl) ⟨93129, by rfl⟩) R186259
theorem R182999 : Reach 182999 := rs (se 1 (by rfl) ⟨137249, by rfl⟩) R274499
theorem R281303 : Reach 281303 := rs (se 1 (by rfl) ⟨210977, by rfl⟩) R421955
theorem R412523 : Reach 412523 := rs (se 1 (by rfl) ⟨309392, by rfl⟩) R618785
theorem R2214839 : Reach 2214839 := rs (se 1 (by rfl) ⟨1661129, by rfl⟩) R3322259
theorem R249479 : Reach 249479 := rs (se 1 (by rfl) ⟨187109, by rfl⟩) R374219
theorem R249533 : Reach 249533 := rs (se 3 (by rfl) ⟨46787, by rfl⟩) R93575
theorem R249695 : Reach 249695 := rs (se 1 (by rfl) ⟨187271, by rfl⟩) R374543
theorem R282487 : Reach 282487 := rs (se 1 (by rfl) ⟨211865, by rfl⟩) R423731
theorem R315323 : Reach 315323 := rs (se 1 (by rfl) ⟨236492, by rfl⟩) R472985
theorem R249857 : Reach 249857 := rs (se 2 (by rfl) ⟨93696, by rfl⟩) R187393
theorem R315407 : Reach 315407 := rs (se 1 (by rfl) ⟨236555, by rfl⟩) R473111
theorem R544805 : Reach 544805 := rs (se 4 (by rfl) ⟨51075, by rfl⟩) R102151
theorem R86455 : Reach 86455 := rs (se 1 (by rfl) ⟨64841, by rfl⟩) R129683
theorem R414233 : Reach 414233 := rs (se 2 (by rfl) ⟨155337, by rfl⟩) R310675
theorem R348731 : Reach 348731 := rs (se 1 (by rfl) ⟨261548, by rfl⟩) R523097
theorem R152275 : Reach 152275 := rs (se 1 (by rfl) ⟨114206, by rfl⟩) R228413
theorem R250667 : Reach 250667 := rs (se 1 (by rfl) ⟨188000, by rfl⟩) R376001
theorem R283459 : Reach 283459 := rs (se 1 (by rfl) ⟨212594, by rfl⟩) R425189
theorem R578411 : Reach 578411 := rs (se 1 (by rfl) ⟨433808, by rfl⟩) R867617
theorem R86959 : Reach 86959 := rs (se 1 (by rfl) ⟨65219, by rfl⟩) R130439
theorem R250937 : Reach 250937 := rs (se 2 (by rfl) ⟨94101, by rfl⟩) R188203
theorem R283763 : Reach 283763 := rs (se 1 (by rfl) ⟨212822, by rfl⟩) R425645
theorem R120055 : Reach 120055 := rs (se 1 (by rfl) ⟨90041, by rfl⟩) R180083
theorem R185591 : Reach 185591 := rs (se 1 (by rfl) ⟨139193, by rfl⟩) R278387
theorem R251261 : Reach 251261 := rs (se 3 (by rfl) ⟨47111, by rfl⟩) R94223
theorem R120251 : Reach 120251 := rs (se 1 (by rfl) ⟨90188, by rfl⟩) R180377
theorem R120359 : Reach 120359 := rs (se 1 (by rfl) ⟨90269, by rfl⟩) R180539
theorem R284219 : Reach 284219 := rs (se 1 (by rfl) ⟨213164, by rfl⟩) R426329
theorem R251531 : Reach 251531 := rs (se 1 (by rfl) ⟨188648, by rfl⟩) R377297
theorem R120649 : Reach 120649 := rs (se 2 (by rfl) ⟨45243, by rfl⟩) R90487
theorem R120683 : Reach 120683 := rs (se 1 (by rfl) ⟨90512, by rfl⟩) R181025
theorem R513911 : Reach 513911 := rs (se 1 (by rfl) ⟨385433, by rfl⟩) R770867
theorem R350297 : Reach 350297 := rs (se 2 (by rfl) ⟨131361, by rfl⟩) R262723
theorem R121081 : Reach 121081 := rs (se 2 (by rfl) ⟨45405, by rfl⟩) R90811
theorem R317783 : Reach 317783 := rs (se 1 (by rfl) ⟨238337, by rfl⟩) R476675
theorem R711017 : Reach 711017 := rs (se 2 (by rfl) ⟨266631, by rfl⟩) R533263
theorem R1169795 : Reach 1169795 := rs (se 1 (by rfl) ⟨877346, by rfl⟩) R1754693
theorem R809453 : Reach 809453 := rs (se 3 (by rfl) ⟨151772, by rfl⟩) R303545
theorem R121351 : Reach 121351 := rs (se 1 (by rfl) ⟨91013, by rfl⟩) R182027
theorem R252449 : Reach 252449 := rs (se 2 (by rfl) ⟨94668, by rfl⟩) R189337
theorem R88699 : Reach 88699 := rs (se 1 (by rfl) ⟨66524, by rfl⟩) R133049
theorem R187019 : Reach 187019 := rs (se 1 (by rfl) ⟨140264, by rfl⟩) R280529
theorem R416441 : Reach 416441 := rs (se 2 (by rfl) ⟨156165, by rfl⟩) R312331
theorem R252665 : Reach 252665 := rs (se 2 (by rfl) ⟨94749, by rfl⟩) R189499
theorem R187231 : Reach 187231 := rs (se 1 (by rfl) ⟨140423, by rfl⟩) R280847
theorem R154543 : Reach 154543 := rs (se 1 (by rfl) ⟨115907, by rfl⟩) R231815
theorem R121783 : Reach 121783 := rs (se 1 (by rfl) ⟨91337, by rfl⟩) R182675
theorem R252935 : Reach 252935 := rs (se 1 (by rfl) ⟨189701, by rfl⟩) R379403
theorem R253043 : Reach 253043 := rs (se 1 (by rfl) ⟨189782, by rfl⟩) R379565
theorem R121979 : Reach 121979 := rs (se 1 (by rfl) ⟨91484, by rfl⟩) R182969
theorem R417149 : Reach 417149 := rs (se 3 (by rfl) ⟨78215, by rfl⟩) R156431
theorem R253313 : Reach 253313 := rs (se 2 (by rfl) ⟨94992, by rfl⟩) R189985
theorem R253421 : Reach 253421 := rs (se 3 (by rfl) ⟨47516, by rfl⟩) R95033
theorem R122377 : Reach 122377 := rs (se 2 (by rfl) ⟨45891, by rfl⟩) R91783
theorem R515645 : Reach 515645 := rs (se 3 (by rfl) ⟨96683, by rfl⟩) R193367
theorem R122539 : Reach 122539 := rs (se 1 (by rfl) ⟨91904, by rfl⟩) R183809
theorem R188153 : Reach 188153 := rs (se 2 (by rfl) ⟨70557, by rfl⟩) R141115
theorem R286651 : Reach 286651 := rs (se 1 (by rfl) ⟨214988, by rfl⟩) R429977
theorem R122843 : Reach 122843 := rs (se 1 (by rfl) ⟨92132, by rfl⟩) R184265
theorem R123079 : Reach 123079 := rs (se 1 (by rfl) ⟨92309, by rfl⟩) R184619
theorem R123241 : Reach 123241 := rs (se 2 (by rfl) ⟨46215, by rfl⟩) R92431
theorem R188801 : Reach 188801 := rs (se 2 (by rfl) ⟨70800, by rfl⟩) R141601
theorem R123835 : Reach 123835 := rs (se 1 (by rfl) ⟨92876, by rfl⟩) R185753
theorem R123943 : Reach 123943 := rs (se 1 (by rfl) ⟨92957, by rfl⟩) R185915
theorem R189611 : Reach 189611 := rs (se 1 (by rfl) ⟨142208, by rfl⟩) R284417
theorem R124267 : Reach 124267 := rs (se 1 (by rfl) ⟨93200, by rfl⟩) R186401
theorem R976373 : Reach 976373 := rs (se 5 (by rfl) ⟨45767, by rfl⟩) R91535
theorem R91687 : Reach 91687 := rs (se 1 (by rfl) ⟨68765, by rfl⟩) R137531
theorem R550637 : Reach 550637 := rs (se 3 (by rfl) ⟨103244, by rfl⟩) R206489
theorem R1763167 : Reach 1763167 := rs (se 1 (by rfl) ⟨1322375, by rfl⟩) R2644751
theorem R92011 : Reach 92011 := rs (se 1 (by rfl) ⟨69008, by rfl⟩) R138017
theorem R157601 : Reach 157601 := rs (se 2 (by rfl) ⟨59100, by rfl⟩) R118201
theorem R1894337 : Reach 1894337 := rs (se 2 (by rfl) ⟨710376, by rfl⟩) R1420753
theorem R3106997 : Reach 3106997 := rs (se 5 (by rfl) ⟨145640, by rfl⟩) R291281
theorem R157943 : Reach 157943 := rs (se 1 (by rfl) ⟨118457, by rfl⟩) R236915
theorem R1075457 : Reach 1075457 := rs (se 2 (by rfl) ⟨403296, by rfl⟩) R806593
theorem R125327 : Reach 125327 := rs (se 1 (by rfl) ⟨93995, by rfl⟩) R187991
theorem R289403 : Reach 289403 := rs (se 1 (by rfl) ⟨217052, by rfl⟩) R434105
theorem R125563 : Reach 125563 := rs (se 1 (by rfl) ⟨94172, by rfl⟩) R188345
theorem R551609 : Reach 551609 := rs (se 2 (by rfl) ⟨206853, by rfl⟩) R413707
theorem R93307 : Reach 93307 := rs (se 1 (by rfl) ⟨69980, by rfl⟩) R139961
theorem R715969 : Reach 715969 := rs (se 2 (by rfl) ⟨268488, by rfl⟩) R536977
theorem R126427 : Reach 126427 := rs (se 1 (by rfl) ⟨94820, by rfl⟩) R189641
theorem R1076723 : Reach 1076723 := rs (se 1 (by rfl) ⟨807542, by rfl⟩) R1615085
theorem R191987 : Reach 191987 := rs (se 1 (by rfl) ⟨143990, by rfl⟩) R287981
theorem R159241 : Reach 159241 := rs (se 2 (by rfl) ⟨59715, by rfl⟩) R119431
theorem R552581 : Reach 552581 := rs (se 4 (by rfl) ⟨51804, by rfl⟩) R103609
theorem R421523 : Reach 421523 := rs (se 1 (by rfl) ⟨316142, by rfl⟩) R632285
theorem R13758149 : Reach 13758149 := rs (se 4 (by rfl) ⟨1289826, by rfl⟩) R2579653
theorem R159583 : Reach 159583 := rs (se 1 (by rfl) ⟨119687, by rfl⟩) R239375
theorem R127073 : Reach 127073 := rs (se 2 (by rfl) ⟨47652, by rfl⟩) R95305
theorem R422273 : Reach 422273 := rs (se 2 (by rfl) ⟨158352, by rfl⟩) R316705
theorem R160379 : Reach 160379 := rs (se 1 (by rfl) ⟨120284, by rfl⟩) R240569
theorem R160505 : Reach 160505 := rs (se 2 (by rfl) ⟨60189, by rfl⟩) R120379
theorem R422729 : Reach 422729 := rs (se 2 (by rfl) ⟨158523, by rfl⟩) R317047
theorem R160775 : Reach 160775 := rs (se 1 (by rfl) ⟨120581, by rfl⟩) R241163
theorem R160847 : Reach 160847 := rs (se 1 (by rfl) ⟨120635, by rfl⟩) R241271
theorem R259319 : Reach 259319 := rs (se 1 (by rfl) ⟨194489, by rfl⟩) R388979
theorem R161243 : Reach 161243 := rs (se 1 (by rfl) ⟨120932, by rfl⟩) R241865
theorem R521873 : Reach 521873 := rs (se 2 (by rfl) ⟨195702, by rfl⟩) R391405
theorem R9565937 : Reach 9565937 := rs (se 2 (by rfl) ⟨3587226, by rfl⟩) R7174453
theorem R915259 : Reach 915259 := rs (se 1 (by rfl) ⟨686444, by rfl⟩) R1372889
theorem R161711 : Reach 161711 := rs (se 1 (by rfl) ⟨121283, by rfl⟩) R242567
theorem R555011 : Reach 555011 := rs (se 1 (by rfl) ⟨416258, by rfl⟩) R832517
theorem R161963 : Reach 161963 := rs (se 1 (by rfl) ⟨121472, by rfl⟩) R242945
theorem R522625 : Reach 522625 := rs (se 2 (by rfl) ⟨195984, by rfl⟩) R391969
theorem R490009 : Reach 490009 := rs (se 2 (by rfl) ⟨183753, by rfl⟩) R367507
theorem R129575 : Reach 129575 := rs (se 1 (by rfl) ⟨97181, by rfl⟩) R194363
theorem R162503 : Reach 162503 := rs (se 1 (by rfl) ⟨121877, by rfl⟩) R243755
theorem R195283 : Reach 195283 := rs (se 1 (by rfl) ⟨146462, by rfl⟩) R292925
theorem R130295 : Reach 130295 := rs (se 1 (by rfl) ⟨97721, by rfl⟩) R195443
theorem R1277207 : Reach 1277207 := rs (se 1 (by rfl) ⟨957905, by rfl⟩) R1915811
theorem R163367 : Reach 163367 := rs (se 1 (by rfl) ⟨122525, by rfl⟩) R245051
theorem R360125 : Reach 360125 := rs (se 3 (by rfl) ⟨67523, by rfl⟩) R135047
theorem R261917 : Reach 261917 := rs (se 3 (by rfl) ⟨49109, by rfl⟩) R98219
theorem R360287 : Reach 360287 := rs (se 1 (by rfl) ⟨270215, by rfl⟩) R540431
theorem R163691 : Reach 163691 := rs (se 1 (by rfl) ⟨122768, by rfl⟩) R245537
theorem R163745 : Reach 163745 := rs (se 2 (by rfl) ⟨61404, by rfl⟩) R122809
theorem R425915 : Reach 425915 := rs (se 1 (by rfl) ⟨319436, by rfl⟩) R638873
theorem R360449 : Reach 360449 := rs (se 2 (by rfl) ⟨135168, by rfl⟩) R270337
theorem R1572941 : Reach 1572941 := rs (se 3 (by rfl) ⟨294926, by rfl⟩) R589853
theorem R164051 : Reach 164051 := rs (se 1 (by rfl) ⟨123038, by rfl⟩) R246077
theorem R164105 : Reach 164105 := rs (se 2 (by rfl) ⟨61539, by rfl⟩) R123079
theorem R164321 : Reach 164321 := rs (se 2 (by rfl) ⟨61620, by rfl⟩) R123241
theorem R98911 : Reach 98911 := rs (se 1 (by rfl) ⟨74183, by rfl⟩) R148367
theorem R524983 : Reach 524983 := rs (se 1 (by rfl) ⟨393737, by rfl⟩) R787475
theorem R393911 : Reach 393911 := rs (se 1 (by rfl) ⟨295433, by rfl⟩) R590867
theorem R393943 : Reach 393943 := rs (se 1 (by rfl) ⟨295457, by rfl⟩) R590915
theorem R164627 : Reach 164627 := rs (se 1 (by rfl) ⟨123470, by rfl⟩) R246941
theorem R361259 : Reach 361259 := rs (se 1 (by rfl) ⟨270944, by rfl⟩) R541889
theorem R1114955 : Reach 1114955 := rs (se 1 (by rfl) ⟨836216, by rfl⟩) R1672433
theorem R852929 : Reach 852929 := rs (se 2 (by rfl) ⟨319848, by rfl⟩) R639697
theorem R525275 : Reach 525275 := rs (se 1 (by rfl) ⟨393956, by rfl⟩) R787913
theorem R164987 : Reach 164987 := rs (se 1 (by rfl) ⟨123740, by rfl⟩) R247481
theorem R165113 : Reach 165113 := rs (se 2 (by rfl) ⟨61917, by rfl⟩) R123835
theorem R263519 : Reach 263519 := rs (se 1 (by rfl) ⟨197639, by rfl⟩) R395279
theorem R165257 : Reach 165257 := rs (se 2 (by rfl) ⟨61971, by rfl⟩) R123943
theorem R165307 : Reach 165307 := rs (se 1 (by rfl) ⟨123980, by rfl⟩) R247961
theorem R165383 : Reach 165383 := rs (se 1 (by rfl) ⟨124037, by rfl⟩) R248075
theorem R624185 : Reach 624185 := rs (se 2 (by rfl) ⟨234069, by rfl⟩) R468139
theorem R165563 : Reach 165563 := rs (se 1 (by rfl) ⟨124172, by rfl⟩) R248345
theorem R165689 : Reach 165689 := rs (se 2 (by rfl) ⟨62133, by rfl⟩) R124267
theorem R198557 : Reach 198557 := rs (se 3 (by rfl) ⟨37229, by rfl⟩) R74459
theorem R1476559 : Reach 1476559 := rs (se 1 (by rfl) ⟨1107419, by rfl⟩) R2214839
theorem R493697 : Reach 493697 := rs (se 2 (by rfl) ⟨185136, by rfl⟩) R370273
theorem R166319 : Reach 166319 := rs (se 1 (by rfl) ⟨124739, by rfl⟩) R249479
theorem R166355 : Reach 166355 := rs (se 1 (by rfl) ⟨124766, by rfl⟩) R249533
theorem R166463 : Reach 166463 := rs (se 1 (by rfl) ⟨124847, by rfl⟩) R249695
theorem R166571 : Reach 166571 := rs (se 1 (by rfl) ⟨124928, by rfl⟩) R249857
theorem R363203 : Reach 363203 := rs (se 1 (by rfl) ⟨272402, by rfl⟩) R544805
theorem R232487 : Reach 232487 := rs (se 1 (by rfl) ⟨174365, by rfl⟩) R348731
theorem R167111 : Reach 167111 := rs (se 1 (by rfl) ⟨125333, by rfl⟩) R250667
theorem R691517 : Reach 691517 := rs (se 3 (by rfl) ⟨129659, by rfl⟩) R259319
theorem R167291 : Reach 167291 := rs (se 1 (by rfl) ⟨125468, by rfl⟩) R250937
theorem R167417 : Reach 167417 := rs (se 2 (by rfl) ⟨62781, by rfl⟩) R125563
theorem R167507 : Reach 167507 := rs (se 1 (by rfl) ⟨125630, by rfl⟩) R251261
theorem R396895 : Reach 396895 := rs (se 1 (by rfl) ⟨297671, by rfl⟩) R595343
theorem R265837 : Reach 265837 := rs (se 3 (by rfl) ⟨49844, by rfl⟩) R99689
theorem R167687 : Reach 167687 := rs (se 1 (by rfl) ⟨125765, by rfl⟩) R251531
theorem R233531 : Reach 233531 := rs (se 1 (by rfl) ⟨175148, by rfl⟩) R350297
theorem R954625 : Reach 954625 := rs (se 2 (by rfl) ⟨357984, by rfl⟩) R715969
theorem R168299 : Reach 168299 := rs (se 1 (by rfl) ⟨126224, by rfl⟩) R252449
theorem R168443 : Reach 168443 := rs (se 1 (by rfl) ⟨126332, by rfl⟩) R252665
theorem R168569 : Reach 168569 := rs (se 2 (by rfl) ⟨63213, by rfl⟩) R126427
theorem R266905 : Reach 266905 := rs (se 2 (by rfl) ⟨100089, by rfl⟩) R200179
theorem R168623 : Reach 168623 := rs (se 1 (by rfl) ⟨126467, by rfl⟩) R252935
theorem R168695 : Reach 168695 := rs (se 1 (by rfl) ⟨126521, by rfl⟩) R253043
theorem R463781 : Reach 463781 := rs (se 4 (by rfl) ⟨43479, by rfl⟩) R86959
theorem R168875 : Reach 168875 := rs (se 1 (by rfl) ⟨126656, by rfl⟩) R253313
theorem R267209 : Reach 267209 := rs (se 2 (by rfl) ⟨100203, by rfl⟩) R200407
theorem R168947 : Reach 168947 := rs (se 1 (by rfl) ⟨126710, by rfl⟩) R253421
theorem R562301 : Reach 562301 := rs (se 3 (by rfl) ⟨105431, by rfl⟩) R210863
theorem R71163 : Reach 71163 := rs (se 1 (by rfl) ⟨53372, by rfl⟩) R106745
theorem R71231 : Reach 71231 := rs (se 1 (by rfl) ⟨53423, by rfl⟩) R106847
theorem R71239 : Reach 71239 := rs (se 1 (by rfl) ⟨53429, by rfl⟩) R106859
theorem R71391 : Reach 71391 := rs (se 1 (by rfl) ⟨53543, by rfl⟩) R107087
theorem R71471 : Reach 71471 := rs (se 1 (by rfl) ⟨53603, by rfl⟩) R107207
theorem R71579 : Reach 71579 := rs (se 1 (by rfl) ⟨53684, by rfl⟩) R107369
theorem R71631 : Reach 71631 := rs (se 1 (by rfl) ⟨53723, by rfl⟩) R107447
theorem R71655 : Reach 71655 := rs (se 1 (by rfl) ⟨53741, by rfl⟩) R107483
theorem R203033 : Reach 203033 := rs (se 2 (by rfl) ⟨76137, by rfl⟩) R152275
theorem R71967 : Reach 71967 := rs (se 1 (by rfl) ⟨53975, by rfl⟩) R107951
theorem R72027 : Reach 72027 := rs (se 1 (by rfl) ⟨54020, by rfl⟩) R108041
theorem R72047 : Reach 72047 := rs (se 1 (by rfl) ⟨54035, by rfl⟩) R108071
theorem R72103 : Reach 72103 := rs (se 1 (by rfl) ⟨54077, by rfl⟩) R108155
theorem R367091 : Reach 367091 := rs (se 1 (by rfl) ⟨275318, by rfl⟩) R550637
theorem R72187 : Reach 72187 := rs (se 1 (by rfl) ⟨54140, by rfl⟩) R108281
theorem R72255 : Reach 72255 := rs (se 1 (by rfl) ⟨54191, by rfl⟩) R108383
theorem R72263 : Reach 72263 := rs (se 1 (by rfl) ⟨54197, by rfl⟩) R108395
theorem R105067 : Reach 105067 := rs (se 1 (by rfl) ⟨78800, by rfl⟩) R157601
theorem R72415 : Reach 72415 := rs (se 1 (by rfl) ⟨54311, by rfl⟩) R108623
theorem R2071331 : Reach 2071331 := rs (se 1 (by rfl) ⟨1553498, by rfl⟩) R3106997
theorem R72495 : Reach 72495 := rs (se 1 (by rfl) ⟨54371, by rfl⟩) R108743
theorem R105295 : Reach 105295 := rs (se 1 (by rfl) ⟨78971, by rfl⟩) R157943
theorem R72603 : Reach 72603 := rs (se 1 (by rfl) ⟨54452, by rfl⟩) R108905
theorem R72655 : Reach 72655 := rs (se 1 (by rfl) ⟨54491, by rfl⟩) R108983
theorem R72679 : Reach 72679 := rs (se 1 (by rfl) ⟨54509, by rfl⟩) R109019
theorem R367739 : Reach 367739 := rs (se 1 (by rfl) ⟨275804, by rfl⟩) R551609
theorem R72991 : Reach 72991 := rs (se 1 (by rfl) ⟨54743, by rfl⟩) R109487
theorem R73051 : Reach 73051 := rs (se 1 (by rfl) ⟨54788, by rfl⟩) R109577
theorem R73071 : Reach 73071 := rs (se 1 (by rfl) ⟨54803, by rfl⟩) R109607
theorem R73127 : Reach 73127 := rs (se 1 (by rfl) ⟨54845, by rfl⟩) R109691
theorem R73211 : Reach 73211 := rs (se 1 (by rfl) ⟨54908, by rfl⟩) R109817
theorem R73279 : Reach 73279 := rs (se 1 (by rfl) ⟨54959, by rfl⟩) R109919
theorem R73287 : Reach 73287 := rs (se 1 (by rfl) ⟨54965, by rfl⟩) R109931
theorem R204383 : Reach 204383 := rs (se 1 (by rfl) ⟨153287, by rfl⟩) R306575
theorem R73439 : Reach 73439 := rs (se 1 (by rfl) ⟨55079, by rfl⟩) R110159
theorem R1220345 : Reach 1220345 := rs (se 2 (by rfl) ⟨457629, by rfl⟩) R915259
theorem R368387 : Reach 368387 := rs (se 1 (by rfl) ⟨276290, by rfl⟩) R552581
theorem R73519 : Reach 73519 := rs (se 1 (by rfl) ⟨55139, by rfl⟩) R110279
theorem R73627 : Reach 73627 := rs (se 1 (by rfl) ⟨55220, by rfl⟩) R110441
theorem R73679 : Reach 73679 := rs (se 1 (by rfl) ⟨55259, by rfl⟩) R110519
theorem R73703 : Reach 73703 := rs (se 1 (by rfl) ⟨55277, by rfl⟩) R110555
theorem R74015 : Reach 74015 := rs (se 1 (by rfl) ⟨55511, by rfl⟩) R111023
theorem R74075 : Reach 74075 := rs (se 1 (by rfl) ⟨55556, by rfl⟩) R111113
theorem R74095 : Reach 74095 := rs (se 1 (by rfl) ⟨55571, by rfl⟩) R111143
theorem R106919 : Reach 106919 := rs (se 1 (by rfl) ⟨80189, by rfl⟩) R160379
theorem R74151 : Reach 74151 := rs (se 1 (by rfl) ⟨55613, by rfl⟩) R111227
theorem R107003 : Reach 107003 := rs (se 1 (by rfl) ⟨80252, by rfl⟩) R160505
theorem R74235 : Reach 74235 := rs (se 1 (by rfl) ⟨55676, by rfl⟩) R111353
theorem R696833 : Reach 696833 := rs (se 2 (by rfl) ⟨261312, by rfl⟩) R522625
theorem R6758923 : Reach 6758923 := rs (se 1 (by rfl) ⟨5069192, by rfl⟩) R10138385
theorem R74303 : Reach 74303 := rs (se 1 (by rfl) ⟨55727, by rfl⟩) R111455
theorem R74311 : Reach 74311 := rs (se 1 (by rfl) ⟨55733, by rfl⟩) R111467
theorem R107129 : Reach 107129 := rs (se 2 (by rfl) ⟨40173, by rfl⟩) R80347
theorem R107183 : Reach 107183 := rs (se 1 (by rfl) ⟨80387, by rfl⟩) R160775
theorem R107231 : Reach 107231 := rs (se 1 (by rfl) ⟨80423, by rfl⟩) R160847
theorem R74463 : Reach 74463 := rs (se 1 (by rfl) ⟨55847, by rfl⟩) R111695
theorem R74543 : Reach 74543 := rs (se 1 (by rfl) ⟨55907, by rfl⟩) R111815
theorem R74651 : Reach 74651 := rs (se 1 (by rfl) ⟨55988, by rfl⟩) R111977
theorem R74703 : Reach 74703 := rs (se 1 (by rfl) ⟨56027, by rfl⟩) R112055
theorem R107495 : Reach 107495 := rs (se 1 (by rfl) ⟨80621, by rfl⟩) R161243
theorem R74727 : Reach 74727 := rs (se 1 (by rfl) ⟨56045, by rfl⟩) R112091
theorem R369809 : Reach 369809 := rs (se 2 (by rfl) ⟨138678, by rfl⟩) R277357
theorem R206023 : Reach 206023 := rs (se 1 (by rfl) ⟨154517, by rfl⟩) R309035
theorem R74971 : Reach 74971 := rs (se 1 (by rfl) ⟨56228, by rfl⟩) R112457
theorem R107753 : Reach 107753 := rs (se 2 (by rfl) ⟨40407, by rfl⟩) R80815
theorem R206057 : Reach 206057 := rs (se 2 (by rfl) ⟨77271, by rfl⟩) R154543
theorem R107807 : Reach 107807 := rs (se 1 (by rfl) ⟨80855, by rfl⟩) R161711
theorem R75039 : Reach 75039 := rs (se 1 (by rfl) ⟨56279, by rfl⟩) R112559
theorem R75047 : Reach 75047 := rs (se 1 (by rfl) ⟨56285, by rfl⟩) R112571
theorem R370007 : Reach 370007 := rs (se 1 (by rfl) ⟨277505, by rfl⟩) R555011
theorem R75099 : Reach 75099 := rs (se 1 (by rfl) ⟨56324, by rfl⟩) R112649
theorem R75119 : Reach 75119 := rs (se 1 (by rfl) ⟨56339, by rfl⟩) R112679
theorem R107975 : Reach 107975 := rs (se 1 (by rfl) ⟨80981, by rfl⟩) R161963
theorem R108329 : Reach 108329 := rs (se 2 (by rfl) ⟨40623, by rfl⟩) R81247
theorem R108335 : Reach 108335 := rs (se 1 (by rfl) ⟨81251, by rfl⟩) R162503
theorem R370817 : Reach 370817 := rs (se 2 (by rfl) ⟨139056, by rfl⟩) R278113
theorem R108809 : Reach 108809 := rs (se 2 (by rfl) ⟨40803, by rfl⟩) R81607
theorem R108911 : Reach 108911 := rs (se 1 (by rfl) ⟨81683, by rfl⟩) R163367
theorem R469421 : Reach 469421 := rs (se 3 (by rfl) ⟨88016, by rfl⟩) R176033
theorem R240083 : Reach 240083 := rs (se 1 (by rfl) ⟨180062, by rfl⟩) R360125
theorem R207355 : Reach 207355 := rs (se 1 (by rfl) ⟨155516, by rfl⟩) R311033
theorem R174611 : Reach 174611 := rs (se 1 (by rfl) ⟨130958, by rfl⟩) R261917
theorem R240191 : Reach 240191 := rs (se 1 (by rfl) ⟨180143, by rfl⟩) R360287
theorem R109127 : Reach 109127 := rs (se 1 (by rfl) ⟨81845, by rfl⟩) R163691
theorem R109163 : Reach 109163 := rs (se 1 (by rfl) ⟨81872, by rfl⟩) R163745
theorem R273071 : Reach 273071 := rs (se 1 (by rfl) ⟨204803, by rfl⟩) R409607
theorem R76511 : Reach 76511 := rs (se 1 (by rfl) ⟨57383, by rfl⟩) R114767
theorem R1059601 : Reach 1059601 := rs (se 2 (by rfl) ⟨397350, by rfl⟩) R794701
theorem R404291 : Reach 404291 := rs (se 1 (by rfl) ⟨303218, by rfl⟩) R606437
theorem R109391 : Reach 109391 := rs (se 1 (by rfl) ⟨82043, by rfl⟩) R164087
theorem R1321859 : Reach 1321859 := rs (se 1 (by rfl) ⟨991394, by rfl⟩) R1982789
theorem R371627 : Reach 371627 := rs (se 1 (by rfl) ⟨278720, by rfl⟩) R557441
theorem R1420253 : Reach 1420253 := rs (se 3 (by rfl) ⟨266297, by rfl⟩) R532595
theorem R306163 : Reach 306163 := rs (se 1 (by rfl) ⟨229622, by rfl⟩) R459245
theorem R109787 : Reach 109787 := rs (se 1 (by rfl) ⟨82340, by rfl⟩) R164681
theorem R109961 : Reach 109961 := rs (se 2 (by rfl) ⟨41235, by rfl⟩) R82471
theorem R306899 : Reach 306899 := rs (se 1 (by rfl) ⟨230174, by rfl⟩) R460349
theorem R110315 : Reach 110315 := rs (se 1 (by rfl) ⟨82736, by rfl⟩) R165473
theorem R175879 : Reach 175879 := rs (se 1 (by rfl) ⟨131909, by rfl⟩) R263819
theorem R1421243 : Reach 1421243 := rs (se 1 (by rfl) ⟨1065932, by rfl⟩) R2131865
theorem R110543 : Reach 110543 := rs (se 1 (by rfl) ⟨82907, by rfl⟩) R165815
theorem R372761 : Reach 372761 := rs (se 2 (by rfl) ⟨139785, by rfl⟩) R279571
theorem R307259 : Reach 307259 := rs (se 1 (by rfl) ⟨230444, by rfl⟩) R460889
theorem R340139 : Reach 340139 := rs (se 1 (by rfl) ⟨255104, by rfl⟩) R510209
theorem R307547 : Reach 307547 := rs (se 1 (by rfl) ⟨230660, by rfl⟩) R461321
theorem R110939 : Reach 110939 := rs (se 1 (by rfl) ⟨83204, by rfl⟩) R166409
theorem R242027 : Reach 242027 := rs (se 1 (by rfl) ⟨181520, by rfl⟩) R363041
theorem R111167 : Reach 111167 := rs (se 1 (by rfl) ⟨83375, by rfl⟩) R166751
theorem R275015 : Reach 275015 := rs (se 1 (by rfl) ⟨206261, by rfl⟩) R412523
theorem R242297 : Reach 242297 := rs (se 2 (by rfl) ⟨90861, by rfl⟩) R181723
theorem R111287 : Reach 111287 := rs (se 1 (by rfl) ⟨83465, by rfl⟩) R166931
theorem R111515 : Reach 111515 := rs (se 1 (by rfl) ⟨83636, by rfl⟩) R167273
theorem R308231 : Reach 308231 := rs (se 1 (by rfl) ⟨231173, by rfl⟩) R462347
theorem R210215 : Reach 210215 := rs (se 1 (by rfl) ⟨157661, by rfl⟩) R315323
theorem R111911 : Reach 111911 := rs (se 1 (by rfl) ⟨83933, by rfl⟩) R167867
theorem R210271 : Reach 210271 := rs (se 1 (by rfl) ⟨157703, by rfl⟩) R315407
theorem R111995 : Reach 111995 := rs (se 1 (by rfl) ⟨83996, by rfl⟩) R167993
theorem R112121 : Reach 112121 := rs (se 2 (by rfl) ⟨42045, by rfl⟩) R84091
theorem R112223 : Reach 112223 := rs (se 1 (by rfl) ⟨84167, by rfl⟩) R168335
theorem R276155 : Reach 276155 := rs (se 1 (by rfl) ⟨207116, by rfl⟩) R414233
theorem R112439 : Reach 112439 := rs (se 1 (by rfl) ⟨84329, by rfl⟩) R168659
theorem R80167 : Reach 80167 := rs (se 1 (by rfl) ⟨60125, by rfl⟩) R120251
theorem R80239 : Reach 80239 := rs (se 1 (by rfl) ⟨60179, by rfl⟩) R120359
theorem R244079 : Reach 244079 := rs (se 1 (by rfl) ⟨183059, by rfl⟩) R366119
theorem R80455 : Reach 80455 := rs (se 1 (by rfl) ⟨60341, by rfl⟩) R120683
theorem R310007 : Reach 310007 := rs (se 1 (by rfl) ⟨232505, by rfl⟩) R465011
theorem R375677 : Reach 375677 := rs (se 3 (by rfl) ⟨70439, by rfl⟩) R140879
theorem R211855 : Reach 211855 := rs (se 1 (by rfl) ⟨158891, by rfl⟩) R317783
theorem R474011 : Reach 474011 := rs (se 1 (by rfl) ⟨355508, by rfl⟩) R711017
theorem R539635 : Reach 539635 := rs (se 1 (by rfl) ⟨404726, by rfl⟩) R809453
theorem R277627 : Reach 277627 := rs (se 1 (by rfl) ⟨208220, by rfl⟩) R416441
theorem R212321 : Reach 212321 := rs (se 2 (by rfl) ⟨79620, by rfl⟩) R159241
theorem R114043 : Reach 114043 := rs (se 1 (by rfl) ⟨85532, by rfl⟩) R171065
theorem R81319 : Reach 81319 := rs (se 1 (by rfl) ⟨60989, by rfl⟩) R121979
theorem R278099 : Reach 278099 := rs (se 1 (by rfl) ⟨208574, by rfl⟩) R417149
theorem R343763 : Reach 343763 := rs (se 1 (by rfl) ⟨257822, by rfl⟩) R515645
theorem R245483 : Reach 245483 := rs (se 1 (by rfl) ⟨184112, by rfl⟩) R368225
theorem R179975 : Reach 179975 := rs (se 1 (by rfl) ⟨134981, by rfl⟩) R269963
theorem R212777 : Reach 212777 := rs (se 2 (by rfl) ⟨79791, by rfl⟩) R159583
theorem R376649 : Reach 376649 := rs (se 2 (by rfl) ⟨141243, by rfl⟩) R282487
theorem R81895 : Reach 81895 := rs (se 1 (by rfl) ⟨61421, by rfl⟩) R122843
theorem R180731 : Reach 180731 := rs (se 1 (by rfl) ⟨135548, by rfl⟩) R271097
theorem R115273 : Reach 115273 := rs (se 2 (by rfl) ⟨43227, by rfl⟩) R86455
theorem R246455 : Reach 246455 := rs (se 1 (by rfl) ⟨184841, by rfl⟩) R369683
theorem R377945 : Reach 377945 := rs (se 2 (by rfl) ⟨141729, by rfl⟩) R283459
theorem R1262891 : Reach 1262891 := rs (se 1 (by rfl) ⟨947168, by rfl⟩) R1894337
theorem R181703 : Reach 181703 := rs (se 1 (by rfl) ⟨136277, by rfl⟩) R272555
theorem R2606627 : Reach 2606627 := rs (se 1 (by rfl) ⟨1954970, by rfl⟩) R3909941
theorem R83551 : Reach 83551 := rs (se 1 (by rfl) ⟨62663, by rfl⟩) R125327
theorem R182483 : Reach 182483 := rs (se 1 (by rfl) ⟨136862, by rfl⟩) R273725
theorem R182695 : Reach 182695 := rs (se 1 (by rfl) ⟨137021, by rfl⟩) R274043
theorem R281015 : Reach 281015 := rs (se 1 (by rfl) ⟨210761, by rfl⟩) R421523
theorem R444901 : Reach 444901 := rs (se 4 (by rfl) ⟨41709, by rfl⟩) R83419
theorem R182857 : Reach 182857 := rs (se 2 (by rfl) ⟨68571, by rfl⟩) R137143
theorem R248399 : Reach 248399 := rs (se 1 (by rfl) ⟨186299, by rfl⟩) R372599
theorem R84715 : Reach 84715 := rs (se 1 (by rfl) ⟨63536, by rfl⟩) R127073
theorem R281515 : Reach 281515 := rs (se 1 (by rfl) ⟨211136, by rfl⟩) R422273
theorem R281789 : Reach 281789 := rs (se 3 (by rfl) ⟨52835, by rfl⟩) R105671
theorem R281819 : Reach 281819 := rs (se 1 (by rfl) ⟨211364, by rfl⟩) R422729
theorem R347453 : Reach 347453 := rs (se 3 (by rfl) ⟨65147, by rfl⟩) R130295
theorem R183647 : Reach 183647 := rs (se 1 (by rfl) ⟨137735, by rfl⟩) R275471
theorem R118265 : Reach 118265 := rs (se 2 (by rfl) ⟨44349, by rfl⟩) R88699
theorem R347915 : Reach 347915 := rs (se 1 (by rfl) ⟨260936, by rfl⟩) R521873
theorem R249641 : Reach 249641 := rs (se 2 (by rfl) ⟨93615, by rfl⟩) R187231
theorem R6377291 : Reach 6377291 := rs (se 1 (by rfl) ⟨4782968, by rfl⟩) R9565937
theorem R86383 : Reach 86383 := rs (se 1 (by rfl) ⟨64787, by rfl⟩) R129575
theorem R184751 : Reach 184751 := rs (se 1 (by rfl) ⟨138563, by rfl⟩) R277127
theorem R184801 : Reach 184801 := rs (se 2 (by rfl) ⟨69300, by rfl⟩) R138601
theorem R1233467 : Reach 1233467 := rs (se 1 (by rfl) ⟨925100, by rfl⟩) R1850201
theorem R414665 : Reach 414665 := rs (se 2 (by rfl) ⟨155499, by rfl⟩) R310999
theorem R382201 : Reach 382201 := rs (se 2 (by rfl) ⟨143325, by rfl⟩) R286651
theorem R283943 : Reach 283943 := rs (se 1 (by rfl) ⟨212957, by rfl⟩) R425915
theorem R185723 : Reach 185723 := rs (se 1 (by rfl) ⟨139292, by rfl⟩) R278585
theorem R480775 : Reach 480775 := rs (se 1 (by rfl) ⟨360581, by rfl⟩) R721163
theorem R87647 : Reach 87647 := rs (se 1 (by rfl) ⟨65735, by rfl⟩) R131471
theorem R1038095 : Reach 1038095 := rs (se 1 (by rfl) ⟨778571, by rfl⟩) R1557143
theorem R939863 : Reach 939863 := rs (se 1 (by rfl) ⟨704897, by rfl⟩) R1409795
theorem R251855 : Reach 251855 := rs (se 1 (by rfl) ⟨188891, by rfl⟩) R377783
theorem R284705 : Reach 284705 := rs (se 2 (by rfl) ⟨106764, by rfl⟩) R213529
theorem R580229 : Reach 580229 := rs (se 4 (by rfl) ⟨54396, by rfl⟩) R108793
theorem R121567 : Reach 121567 := rs (se 1 (by rfl) ⟨91175, by rfl⟩) R182351
theorem R252827 : Reach 252827 := rs (se 1 (by rfl) ⟨189620, by rfl⟩) R379241
theorem R121999 : Reach 121999 := rs (se 1 (by rfl) ⟨91499, by rfl⟩) R182999
theorem R187535 : Reach 187535 := rs (se 1 (by rfl) ⟨140651, by rfl⟩) R281303
theorem R122249 : Reach 122249 := rs (se 2 (by rfl) ⟨45843, by rfl⟩) R91687
theorem R2350889 : Reach 2350889 := rs (se 2 (by rfl) ⟨881583, by rfl⟩) R1763167
theorem R122681 : Reach 122681 := rs (se 2 (by rfl) ⟨46005, by rfl⟩) R92011
theorem R286621 : Reach 286621 := rs (se 3 (by rfl) ⟨53741, by rfl⟩) R107483
theorem R679873 : Reach 679873 := rs (se 2 (by rfl) ⟨254952, by rfl⟩) R509905
theorem R319697 : Reach 319697 := rs (se 2 (by rfl) ⟨119886, by rfl⟩) R239773
theorem R352603 : Reach 352603 := rs (se 1 (by rfl) ⟨264452, by rfl⟩) R528905
theorem R385607 : Reach 385607 := rs (se 1 (by rfl) ⟨289205, by rfl⟩) R578411
theorem R221867 : Reach 221867 := rs (se 1 (by rfl) ⟨166400, by rfl⟩) R332801
theorem R189175 : Reach 189175 := rs (se 1 (by rfl) ⟨141881, by rfl⟩) R283763
theorem R123727 : Reach 123727 := rs (se 1 (by rfl) ⟨92795, by rfl⟩) R185591
theorem R189479 : Reach 189479 := rs (se 1 (by rfl) ⟨142109, by rfl⟩) R284219
theorem R320669 : Reach 320669 := rs (se 3 (by rfl) ⟨60125, by rfl⟩) R120251
theorem R157115 : Reach 157115 := rs (se 1 (by rfl) ⟨117836, by rfl⟩) R235673
theorem R124409 : Reach 124409 := rs (se 2 (by rfl) ⟨46653, by rfl⟩) R93307
theorem R779863 : Reach 779863 := rs (se 1 (by rfl) ⟨584897, by rfl⟩) R1169795
theorem R452297 : Reach 452297 := rs (se 2 (by rfl) ⟨169611, by rfl⟩) R339223
theorem R124679 : Reach 124679 := rs (se 1 (by rfl) ⟨93509, by rfl⟩) R187019
theorem R1370429 : Reach 1370429 := rs (se 3 (by rfl) ⟨256955, by rfl⟩) R513911
theorem R125435 : Reach 125435 := rs (se 1 (by rfl) ⟨94076, by rfl⟩) R188153
theorem R387773 : Reach 387773 := rs (se 3 (by rfl) ⟨72707, by rfl⟩) R145415
theorem R92983 : Reach 92983 := rs (se 1 (by rfl) ⟨69737, by rfl⟩) R139475
theorem R125867 : Reach 125867 := rs (se 1 (by rfl) ⟨94400, by rfl⟩) R188801
theorem R93403 : Reach 93403 := rs (se 1 (by rfl) ⟨70052, by rfl⟩) R140105
theorem R1240337 : Reach 1240337 := rs (se 2 (by rfl) ⟨465126, by rfl⟩) R930253
theorem R126407 : Reach 126407 := rs (se 1 (by rfl) ⟨94805, by rfl⟩) R189611
theorem R650915 : Reach 650915 := rs (se 1 (by rfl) ⟨488186, by rfl⟩) R976373
theorem R290621 : Reach 290621 := rs (se 3 (by rfl) ⟨54491, by rfl⟩) R108983
theorem R716971 : Reach 716971 := rs (se 1 (by rfl) ⟨537728, by rfl⟩) R1075457
theorem R160073 : Reach 160073 := rs (se 2 (by rfl) ⟨60027, by rfl⟩) R120055
theorem R160091 : Reach 160091 := rs (se 1 (by rfl) ⟨120068, by rfl⟩) R240137
theorem R192935 : Reach 192935 := rs (se 1 (by rfl) ⟨144701, by rfl⟩) R289403
theorem R95023 : Reach 95023 := rs (se 1 (by rfl) ⟨71267, by rfl⟩) R142535
theorem R160667 : Reach 160667 := rs (se 1 (by rfl) ⟨120500, by rfl⟩) R241001
theorem R717815 : Reach 717815 := rs (se 1 (by rfl) ⟨538361, by rfl⟩) R1076723
theorem R127991 : Reach 127991 := rs (se 1 (by rfl) ⟨95993, by rfl⟩) R191987
theorem R160865 : Reach 160865 := rs (se 2 (by rfl) ⟨60324, by rfl⟩) R120649
theorem R9172099 : Reach 9172099 := rs (se 1 (by rfl) ⟨6879074, by rfl⟩) R13758149
theorem R161063 : Reach 161063 := rs (se 1 (by rfl) ⟨120797, by rfl⟩) R241595
theorem R816479 : Reach 816479 := rs (se 1 (by rfl) ⟨612359, by rfl⟩) R1224719
theorem R161441 : Reach 161441 := rs (se 2 (by rfl) ⟨60540, by rfl⟩) R121081
theorem R358199 : Reach 358199 := rs (se 1 (by rfl) ⟨268649, by rfl⟩) R537299
theorem R161801 : Reach 161801 := rs (se 2 (by rfl) ⟨60675, by rfl⟩) R121351
theorem R653345 : Reach 653345 := rs (se 2 (by rfl) ⟨245004, by rfl⟩) R490009
theorem R6715543 : Reach 6715543 := rs (se 1 (by rfl) ⟨5036657, by rfl⟩) R10073315
theorem R260377 : Reach 260377 := rs (se 2 (by rfl) ⟨97641, by rfl⟩) R195283
theorem R162215 : Reach 162215 := rs (se 1 (by rfl) ⟨121661, by rfl⟩) R243323
theorem R358823 : Reach 358823 := rs (se 1 (by rfl) ⟨269117, by rfl⟩) R538235
theorem R162323 : Reach 162323 := rs (se 1 (by rfl) ⟨121742, by rfl⟩) R243485
theorem R1243673 : Reach 1243673 := rs (se 2 (by rfl) ⟨466377, by rfl⟩) R932755
theorem R162377 : Reach 162377 := rs (se 2 (by rfl) ⟨60891, by rfl⟩) R121783
theorem R457289 : Reach 457289 := rs (se 2 (by rfl) ⟨171483, by rfl⟩) R342967
theorem R162791 : Reach 162791 := rs (se 1 (by rfl) ⟨122093, by rfl⟩) R244187
theorem R163169 : Reach 163169 := rs (se 2 (by rfl) ⟨61188, by rfl⟩) R122377
theorem R163259 : Reach 163259 := rs (se 1 (by rfl) ⟨122444, by rfl⟩) R244889
theorem R851471 : Reach 851471 := rs (se 1 (by rfl) ⟨638603, by rfl⟩) R1277207
theorem R163385 : Reach 163385 := rs (se 2 (by rfl) ⟨61269, by rfl⟩) R122539
theorem R196481 : Reach 196481 := rs (se 2 (by rfl) ⟨73680, by rfl⟩) R147361
theorem R753569 : Reach 753569 := rs (se 2 (by rfl) ⟨282588, by rfl⟩) R565177
theorem R1048627 : Reach 1048627 := rs (se 1 (by rfl) ⟨786470, by rfl⟩) R1572941
theorem R262607 : Reach 262607 := rs (se 1 (by rfl) ⟨196955, by rfl⟩) R393911
theorem R164303 : Reach 164303 := rs (se 1 (by rfl) ⟨123227, by rfl⟩) R246455
theorem R9011897 : Reach 9011897 := rs (se 2 (by rfl) ⟨3379461, by rfl⟩) R6758923
theorem R131881 : Reach 131881 := rs (se 2 (by rfl) ⟨49455, by rfl⟩) R98911
theorem R525257 : Reach 525257 := rs (se 2 (by rfl) ⟨196971, by rfl⟩) R393943
theorem R164969 : Reach 164969 := rs (se 2 (by rfl) ⟨61863, by rfl⟩) R123727
theorem R132371 : Reach 132371 := rs (se 1 (by rfl) ⟨99278, by rfl⟩) R198557
theorem R329131 : Reach 329131 := rs (se 1 (by rfl) ⟨246848, by rfl⟩) R493697
theorem R165599 : Reach 165599 := rs (se 1 (by rfl) ⟨124199, by rfl⟩) R248399
theorem R231635 : Reach 231635 := rs (se 1 (by rfl) ⟨173726, by rfl⟩) R347453
theorem R231943 : Reach 231943 := rs (se 1 (by rfl) ⟨173957, by rfl⟩) R347915
theorem R166427 : Reach 166427 := rs (se 1 (by rfl) ⟨124820, by rfl⟩) R249641
theorem R1968745 : Reach 1968745 := rs (se 2 (by rfl) ⟨738279, by rfl⟩) R1476559
theorem R822311 : Reach 822311 := rs (se 1 (by rfl) ⟨616733, by rfl⟩) R1233467
theorem R560357 : Reach 560357 := rs (se 4 (by rfl) ⟨52533, by rfl⟩) R105067
theorem R593201 : Reach 593201 := rs (se 2 (by rfl) ⟨222450, by rfl⟩) R444901
theorem R757181 : Reach 757181 := rs (se 3 (by rfl) ⟨141971, by rfl⟩) R283943
theorem R1412801 : Reach 1412801 := rs (se 2 (by rfl) ⟨529800, by rfl⟩) R1059601
theorem R692063 : Reach 692063 := rs (se 1 (by rfl) ⟨519047, by rfl⟩) R1038095
theorem R626575 : Reach 626575 := rs (se 1 (by rfl) ⟨469931, by rfl⟩) R939863
theorem R167903 : Reach 167903 := rs (se 1 (by rfl) ⟨125927, by rfl⟩) R251855
theorem R6951005 : Reach 6951005 := rs (se 3 (by rfl) ⟨1303313, by rfl⟩) R2606627
theorem R135355 : Reach 135355 := rs (se 1 (by rfl) ⟨101516, by rfl⟩) R203033
theorem R233725 : Reach 233725 := rs (se 3 (by rfl) ⟨43823, by rfl⟩) R87647
theorem R1380887 : Reach 1380887 := rs (se 1 (by rfl) ⟨1035665, by rfl⟩) R2071331
theorem R168551 : Reach 168551 := rs (se 1 (by rfl) ⟨126413, by rfl⟩) R252827
theorem R529193 : Reach 529193 := rs (se 2 (by rfl) ⟨198447, by rfl⟩) R396895
theorem R234505 : Reach 234505 := rs (se 2 (by rfl) ⟨87939, by rfl⟩) R175879
theorem R136255 : Reach 136255 := rs (se 1 (by rfl) ⟨102191, by rfl⟩) R204383
theorem R955961 : Reach 955961 := rs (se 2 (by rfl) ⟨358485, by rfl⟩) R716971
theorem R71279 : Reach 71279 := rs (se 1 (by rfl) ⟨53459, by rfl⟩) R106919
theorem R71335 : Reach 71335 := rs (se 1 (by rfl) ⟨53501, by rfl⟩) R107003
theorem R464555 : Reach 464555 := rs (se 1 (by rfl) ⟨348416, by rfl⟩) R696833
theorem R71419 : Reach 71419 := rs (se 1 (by rfl) ⟨53564, by rfl⟩) R107129
theorem R71455 : Reach 71455 := rs (se 1 (by rfl) ⟨53591, by rfl⟩) R107183
theorem R71487 : Reach 71487 := rs (se 1 (by rfl) ⟨53615, by rfl⟩) R107231
theorem R71663 : Reach 71663 := rs (se 1 (by rfl) ⟨53747, by rfl⟩) R107495
theorem R71835 : Reach 71835 := rs (se 1 (by rfl) ⟨53876, by rfl⟩) R107753
theorem R137371 : Reach 137371 := rs (se 1 (by rfl) ⟨103028, by rfl⟩) R206057
theorem R71871 : Reach 71871 := rs (se 1 (by rfl) ⟨53903, by rfl⟩) R107807
theorem R104743 : Reach 104743 := rs (se 1 (by rfl) ⟨78557, by rfl⟩) R157115
theorem R71983 : Reach 71983 := rs (se 1 (by rfl) ⟨53987, by rfl⟩) R107975
theorem R301531 : Reach 301531 := rs (se 1 (by rfl) ⟨226148, by rfl⟩) R452297
theorem R72219 : Reach 72219 := rs (se 1 (by rfl) ⟨54164, by rfl⟩) R108329
theorem R72223 : Reach 72223 := rs (se 1 (by rfl) ⟨54167, by rfl⟩) R108335
theorem R2038405 : Reach 2038405 := rs (se 4 (by rfl) ⟨191100, by rfl⟩) R382201
theorem R12229465 : Reach 12229465 := rs (se 2 (by rfl) ⟨4586049, by rfl⟩) R9172099
theorem R72539 : Reach 72539 := rs (se 1 (by rfl) ⟨54404, by rfl⟩) R108809
theorem R72607 : Reach 72607 := rs (se 1 (by rfl) ⟨54455, by rfl⟩) R108911
theorem R72751 : Reach 72751 := rs (se 1 (by rfl) ⟨54563, by rfl⟩) R109127
theorem R72775 : Reach 72775 := rs (se 1 (by rfl) ⟨54581, by rfl⟩) R109163
theorem R72927 : Reach 72927 := rs (se 1 (by rfl) ⟨54695, by rfl⟩) R109391
theorem R204029 : Reach 204029 := rs (se 3 (by rfl) ⟨38255, by rfl⟩) R76511
theorem R826685 : Reach 826685 := rs (se 3 (by rfl) ⟨155003, by rfl⟩) R310007
theorem R73191 : Reach 73191 := rs (se 1 (by rfl) ⟨54893, by rfl⟩) R109787
theorem R826891 : Reach 826891 := rs (se 1 (by rfl) ⟨620168, by rfl⟩) R1240337
theorem R73307 : Reach 73307 := rs (se 1 (by rfl) ⟨54980, by rfl⟩) R109961
theorem R433943 : Reach 433943 := rs (se 1 (by rfl) ⟨325457, by rfl⟩) R650915
theorem R204599 : Reach 204599 := rs (se 1 (by rfl) ⟨153449, by rfl⟩) R306899
theorem R73543 : Reach 73543 := rs (se 1 (by rfl) ⟨55157, by rfl⟩) R110315
theorem R73695 : Reach 73695 := rs (se 1 (by rfl) ⟨55271, by rfl⟩) R110543
theorem R204839 : Reach 204839 := rs (se 1 (by rfl) ⟨153629, by rfl⟩) R307259
theorem R8954057 : Reach 8954057 := rs (se 2 (by rfl) ⟨3357771, by rfl⟩) R6715543
theorem R106715 : Reach 106715 := rs (se 1 (by rfl) ⟨80036, by rfl⟩) R160073
theorem R106727 : Reach 106727 := rs (se 1 (by rfl) ⟨80045, by rfl⟩) R160091
theorem R205031 : Reach 205031 := rs (se 1 (by rfl) ⟨153773, by rfl⟩) R307547
theorem R73959 : Reach 73959 := rs (se 1 (by rfl) ⟨55469, by rfl⟩) R110939
theorem R74111 : Reach 74111 := rs (se 1 (by rfl) ⟨55583, by rfl⟩) R111167
theorem R106889 : Reach 106889 := rs (se 2 (by rfl) ⟨40083, by rfl⟩) R80167
theorem R74191 : Reach 74191 := rs (se 1 (by rfl) ⟨55643, by rfl⟩) R111287
theorem R106985 : Reach 106985 := rs (se 2 (by rfl) ⟨40119, by rfl⟩) R80239
theorem R107111 : Reach 107111 := rs (se 1 (by rfl) ⟨80333, by rfl⟩) R160667
theorem R74343 : Reach 74343 := rs (se 1 (by rfl) ⟨55757, by rfl⟩) R111515
theorem R205487 : Reach 205487 := rs (se 1 (by rfl) ⟨154115, by rfl⟩) R308231
theorem R107243 : Reach 107243 := rs (se 1 (by rfl) ⟨80432, by rfl⟩) R160865
theorem R107273 : Reach 107273 := rs (se 2 (by rfl) ⟨40227, by rfl⟩) R80455
theorem R1844045 : Reach 1844045 := rs (se 3 (by rfl) ⟨345758, by rfl⟩) R691517
theorem R107375 : Reach 107375 := rs (se 1 (by rfl) ⟨80531, by rfl⟩) R161063
theorem R140143 : Reach 140143 := rs (se 1 (by rfl) ⟨105107, by rfl⟩) R210215
theorem R74607 : Reach 74607 := rs (se 1 (by rfl) ⟨55955, by rfl⟩) R111911
theorem R74663 : Reach 74663 := rs (se 1 (by rfl) ⟨55997, by rfl⟩) R111995
theorem R566189 : Reach 566189 := rs (se 3 (by rfl) ⟨106160, by rfl⟩) R212321
theorem R74747 : Reach 74747 := rs (se 1 (by rfl) ⟨56060, by rfl⟩) R112121
theorem R74815 : Reach 74815 := rs (se 1 (by rfl) ⟨56111, by rfl⟩) R112223
theorem R140393 : Reach 140393 := rs (se 2 (by rfl) ⟨52647, by rfl⟩) R105295
theorem R107627 : Reach 107627 := rs (se 1 (by rfl) ⟨80720, by rfl⟩) R161441
theorem R238799 : Reach 238799 := rs (se 1 (by rfl) ⟨179099, by rfl⟩) R358199
theorem R74959 : Reach 74959 := rs (se 1 (by rfl) ⟨56219, by rfl⟩) R112439
theorem R107867 : Reach 107867 := rs (se 1 (by rfl) ⟨80900, by rfl⟩) R161801
theorem R435563 : Reach 435563 := rs (se 1 (by rfl) ⟨326672, by rfl⟩) R653345
theorem R370169 : Reach 370169 := rs (se 2 (by rfl) ⟨138813, by rfl⟩) R277627
theorem R108143 : Reach 108143 := rs (se 1 (by rfl) ⟨81107, by rfl⟩) R162215
theorem R239215 : Reach 239215 := rs (se 1 (by rfl) ⟨179411, by rfl⟩) R358823
theorem R108215 : Reach 108215 := rs (se 1 (by rfl) ⟨81161, by rfl⟩) R162323
theorem R829115 : Reach 829115 := rs (se 1 (by rfl) ⟨621836, by rfl⟩) R1243673
theorem R108251 : Reach 108251 := rs (se 1 (by rfl) ⟨81188, by rfl⟩) R162377
theorem R304859 : Reach 304859 := rs (se 1 (by rfl) ⟨228644, by rfl⟩) R457289
theorem R108425 : Reach 108425 := rs (se 2 (by rfl) ⟨40659, by rfl⟩) R81319
theorem R108527 : Reach 108527 := rs (se 1 (by rfl) ⟨81395, by rfl⟩) R162791
theorem R108779 : Reach 108779 := rs (se 1 (by rfl) ⟨81584, by rfl⟩) R163169
theorem R108839 : Reach 108839 := rs (se 1 (by rfl) ⟨81629, by rfl⟩) R163259
theorem R567647 : Reach 567647 := rs (se 1 (by rfl) ⟨425735, by rfl⟩) R851471
theorem R108923 : Reach 108923 := rs (se 1 (by rfl) ⟨81692, by rfl⟩) R163385
theorem R141851 : Reach 141851 := rs (se 1 (by rfl) ⟨106388, by rfl⟩) R212777
theorem R502379 : Reach 502379 := rs (se 1 (by rfl) ⟨376784, by rfl⟩) R753569
theorem R109193 : Reach 109193 := rs (se 2 (by rfl) ⟨40947, by rfl⟩) R81895
theorem R240299 : Reach 240299 := rs (se 1 (by rfl) ⟨180224, by rfl⟩) R360449
theorem R109367 : Reach 109367 := rs (se 1 (by rfl) ⟨82025, by rfl⟩) R164051
theorem R109403 : Reach 109403 := rs (se 1 (by rfl) ⟨82052, by rfl⟩) R164105
theorem R109547 : Reach 109547 := rs (se 1 (by rfl) ⟨82160, by rfl⟩) R164321
theorem R470137 : Reach 470137 := rs (se 2 (by rfl) ⟨176301, by rfl⟩) R352603
theorem R109751 : Reach 109751 := rs (se 1 (by rfl) ⟨82313, by rfl⟩) R164627
theorem R240839 : Reach 240839 := rs (se 1 (by rfl) ⟨180629, by rfl⟩) R361259
theorem R568619 : Reach 568619 := rs (se 1 (by rfl) ⟨426464, by rfl⟩) R852929
theorem R109991 : Reach 109991 := rs (se 1 (by rfl) ⟨82493, by rfl⟩) R164987
theorem R110075 : Reach 110075 := rs (se 1 (by rfl) ⟨82556, by rfl⟩) R165113
theorem R175679 : Reach 175679 := rs (se 1 (by rfl) ⟨131759, by rfl⟩) R263519
theorem R699977 : Reach 699977 := rs (se 2 (by rfl) ⟨262491, by rfl⟩) R524983
theorem R110171 : Reach 110171 := rs (se 1 (by rfl) ⟨82628, by rfl⟩) R165257
theorem R110255 : Reach 110255 := rs (se 1 (by rfl) ⟨82691, by rfl⟩) R165383
theorem R110375 : Reach 110375 := rs (se 1 (by rfl) ⟨82781, by rfl⟩) R165563
theorem R110459 : Reach 110459 := rs (se 1 (by rfl) ⟨82844, by rfl⟩) R165689
theorem R1388677 : Reach 1388677 := rs (se 4 (by rfl) ⟨130188, by rfl⟩) R260377
theorem R1028285 : Reach 1028285 := rs (se 3 (by rfl) ⟨192803, by rfl⟩) R385607
theorem R274697 : Reach 274697 := rs (se 2 (by rfl) ⟨103011, by rfl⟩) R206023
theorem R110879 : Reach 110879 := rs (se 1 (by rfl) ⟨83159, by rfl⟩) R166319
theorem R110903 : Reach 110903 := rs (se 1 (by rfl) ⟨83177, by rfl⟩) R166355
theorem R110975 : Reach 110975 := rs (se 1 (by rfl) ⟨83231, by rfl⟩) R166463
theorem R111047 : Reach 111047 := rs (se 1 (by rfl) ⟨83285, by rfl⟩) R166571
theorem R242135 : Reach 242135 := rs (se 1 (by rfl) ⟨181601, by rfl⟩) R363203
theorem R111401 : Reach 111401 := rs (se 2 (by rfl) ⟨41775, by rfl⟩) R83551
theorem R111407 : Reach 111407 := rs (se 1 (by rfl) ⟨83555, by rfl⟩) R167111
theorem R111527 : Reach 111527 := rs (se 1 (by rfl) ⟨83645, by rfl⟩) R167291
theorem R111611 : Reach 111611 := rs (se 1 (by rfl) ⟨83708, by rfl⟩) R167417
theorem R111671 : Reach 111671 := rs (se 1 (by rfl) ⟨83753, by rfl⟩) R167507
theorem R111791 : Reach 111791 := rs (se 1 (by rfl) ⟨83843, by rfl⟩) R167687
theorem R341309 : Reach 341309 := rs (se 3 (by rfl) ⟨63995, by rfl⟩) R127991
theorem R112199 : Reach 112199 := rs (se 1 (by rfl) ⟨84149, by rfl⟩) R168299
theorem R112295 : Reach 112295 := rs (se 1 (by rfl) ⟨84221, by rfl⟩) R168443
theorem R112379 : Reach 112379 := rs (se 1 (by rfl) ⟨84284, by rfl⟩) R168569
theorem R112415 : Reach 112415 := rs (se 1 (by rfl) ⟨84311, by rfl⟩) R168623
theorem R112463 : Reach 112463 := rs (se 1 (by rfl) ⟨84347, by rfl⟩) R168695
theorem R243593 : Reach 243593 := rs (se 2 (by rfl) ⟨91347, by rfl⟩) R182695
theorem R309187 : Reach 309187 := rs (se 1 (by rfl) ⟨231890, by rfl⟩) R463781
theorem R112583 : Reach 112583 := rs (se 1 (by rfl) ⟨84437, by rfl⟩) R168875
theorem R276443 : Reach 276443 := rs (se 1 (by rfl) ⟨207332, by rfl⟩) R414665
theorem R178139 : Reach 178139 := rs (se 1 (by rfl) ⟨133604, by rfl⟩) R267209
theorem R112631 : Reach 112631 := rs (se 1 (by rfl) ⟨84473, by rfl⟩) R168947
theorem R276473 : Reach 276473 := rs (se 2 (by rfl) ⟨103677, by rfl⟩) R207355
theorem R374867 : Reach 374867 := rs (se 1 (by rfl) ⟨281150, by rfl⟩) R562301
theorem R243809 : Reach 243809 := rs (se 2 (by rfl) ⟨91428, by rfl⟩) R182857
theorem R375353 : Reach 375353 := rs (se 2 (by rfl) ⟨140757, by rfl⟩) R281515
theorem R244727 : Reach 244727 := rs (se 1 (by rfl) ⟨183545, by rfl⟩) R367091
theorem R245159 : Reach 245159 := rs (se 1 (by rfl) ⟨183869, by rfl⟩) R367739
theorem R81499 : Reach 81499 := rs (se 1 (by rfl) ⟨61124, by rfl⟩) R122249
theorem R245591 : Reach 245591 := rs (se 1 (by rfl) ⟨184193, by rfl⟩) R368387
theorem R81787 : Reach 81787 := rs (se 1 (by rfl) ⟨61340, by rfl⟩) R122681
theorem R213131 : Reach 213131 := rs (se 1 (by rfl) ⟨159848, by rfl⟩) R319697
theorem R147911 : Reach 147911 := rs (se 1 (by rfl) ⟨110933, by rfl⟩) R221867
theorem R115177 : Reach 115177 := rs (se 2 (by rfl) ⟨43191, by rfl⟩) R86383
theorem R246401 : Reach 246401 := rs (se 2 (by rfl) ⟨92400, by rfl⟩) R184801
theorem R246539 : Reach 246539 := rs (se 1 (by rfl) ⟨184904, by rfl⟩) R369809
theorem R213779 : Reach 213779 := rs (se 1 (by rfl) ⟨160334, by rfl⟩) R320669
theorem R246671 : Reach 246671 := rs (se 1 (by rfl) ⟨185003, by rfl⟩) R370007
theorem R82939 : Reach 82939 := rs (se 1 (by rfl) ⟨62204, by rfl⟩) R124409
theorem R83119 : Reach 83119 := rs (se 1 (by rfl) ⟨62339, by rfl⟩) R124679
theorem R247211 : Reach 247211 := rs (se 1 (by rfl) ⟨185408, by rfl⟩) R370817
theorem R312947 : Reach 312947 := rs (se 1 (by rfl) ⟨234710, by rfl⟩) R469421
theorem R83623 : Reach 83623 := rs (se 1 (by rfl) ⟨62717, by rfl⟩) R125435
theorem R116407 : Reach 116407 := rs (se 1 (by rfl) ⟨87305, by rfl⟩) R174611
theorem R182047 : Reach 182047 := rs (se 1 (by rfl) ⟨136535, by rfl⟩) R273071
theorem R280361 : Reach 280361 := rs (se 2 (by rfl) ⟨105135, by rfl⟩) R210271
theorem R247751 : Reach 247751 := rs (se 1 (by rfl) ⟨185813, by rfl⟩) R371627
theorem R83911 : Reach 83911 := rs (se 1 (by rfl) ⟨62933, by rfl⟩) R125867
theorem R641033 : Reach 641033 := rs (se 2 (by rfl) ⟨240387, by rfl⟩) R480775
theorem R84271 : Reach 84271 := rs (se 1 (by rfl) ⟨63203, by rfl⟩) R126407
theorem R248507 : Reach 248507 := rs (se 1 (by rfl) ⟨186380, by rfl⟩) R372761
theorem R183343 : Reach 183343 := rs (se 1 (by rfl) ⟨137507, by rfl⟩) R275015
theorem R478543 : Reach 478543 := rs (se 1 (by rfl) ⟨358907, by rfl⟩) R717815
theorem R544319 : Reach 544319 := rs (se 1 (by rfl) ⟨408239, by rfl⟩) R816479
theorem R184103 : Reach 184103 := rs (se 1 (by rfl) ⟨138077, by rfl⟩) R276155
theorem R282473 : Reach 282473 := rs (se 2 (by rfl) ⟨105927, by rfl⟩) R211855
theorem R315373 : Reach 315373 := rs (se 3 (by rfl) ⟨59132, by rfl⟩) R118265
theorem R152057 : Reach 152057 := rs (se 2 (by rfl) ⟨57021, by rfl⟩) R114043
theorem R250451 : Reach 250451 := rs (se 1 (by rfl) ⟨187838, by rfl⟩) R375677
theorem R316007 : Reach 316007 := rs (se 1 (by rfl) ⟨237005, by rfl⟩) R474011
theorem R479933 : Reach 479933 := rs (se 3 (by rfl) ⟨89987, by rfl⟩) R179975
theorem R1528645 : Reach 1528645 := rs (se 4 (by rfl) ⟨143310, by rfl⟩) R286621
theorem R185399 : Reach 185399 := rs (se 1 (by rfl) ⟨139049, by rfl⟩) R278099
theorem R251099 : Reach 251099 := rs (se 1 (by rfl) ⟨188324, by rfl⟩) R376649
theorem R906497 : Reach 906497 := rs (se 2 (by rfl) ⟨339936, by rfl⟩) R679873
theorem R120487 : Reach 120487 := rs (se 1 (by rfl) ⟨90365, by rfl⟩) R180731
theorem R907037 : Reach 907037 := rs (se 3 (by rfl) ⟨170069, by rfl⟩) R340139
theorem R743303 : Reach 743303 := rs (se 1 (by rfl) ⟨557477, by rfl⟩) R1114955
theorem R350183 : Reach 350183 := rs (se 1 (by rfl) ⟨262637, by rfl⟩) R525275
theorem R251963 : Reach 251963 := rs (se 1 (by rfl) ⟨188972, by rfl⟩) R377945
theorem R841927 : Reach 841927 := rs (se 1 (by rfl) ⟨631445, by rfl⟩) R1262891
theorem R121135 : Reach 121135 := rs (se 1 (by rfl) ⟨90851, by rfl⟩) R181703
theorem R252233 : Reach 252233 := rs (se 2 (by rfl) ⟨94587, by rfl⟩) R189175
theorem R416123 : Reach 416123 := rs (se 1 (by rfl) ⟨312092, by rfl⟩) R624185
theorem R121655 : Reach 121655 := rs (se 1 (by rfl) ⟨91241, by rfl⟩) R182483
theorem R187343 : Reach 187343 := rs (se 1 (by rfl) ⟨140507, by rfl⟩) R281015
theorem R220409 : Reach 220409 := rs (se 2 (by rfl) ⟨82653, by rfl⟩) R165307
theorem R154991 : Reach 154991 := rs (se 1 (by rfl) ⟨116243, by rfl⟩) R232487
theorem R1039817 : Reach 1039817 := rs (se 2 (by rfl) ⟨389931, by rfl⟩) R779863
theorem R187859 : Reach 187859 := rs (se 1 (by rfl) ⟨140894, by rfl⟩) R281789
theorem R187879 : Reach 187879 := rs (se 1 (by rfl) ⟨140909, by rfl⟩) R281819
theorem R122431 : Reach 122431 := rs (se 1 (by rfl) ⟨91823, by rfl⟩) R183647
theorem R4251527 : Reach 4251527 := rs (se 1 (by rfl) ⟨3188645, by rfl⟩) R6377291
theorem R155687 : Reach 155687 := rs (se 1 (by rfl) ⟨116765, by rfl⟩) R233531
theorem R123167 : Reach 123167 := rs (se 1 (by rfl) ⟨92375, by rfl⟩) R184751
theorem R614789 : Reach 614789 := rs (se 4 (by rfl) ⟨57636, by rfl⟩) R115273
theorem R123815 : Reach 123815 := rs (se 1 (by rfl) ⟨92861, by rfl⟩) R185723
theorem R123977 : Reach 123977 := rs (se 2 (by rfl) ⟨46491, by rfl⟩) R92983
theorem R451813 : Reach 451813 := rs (se 4 (by rfl) ⟨42357, by rfl⟩) R84715
theorem R189803 : Reach 189803 := rs (se 1 (by rfl) ⟨142352, by rfl⟩) R284705
theorem R124537 : Reach 124537 := rs (se 2 (by rfl) ⟨46701, by rfl⟩) R93403
theorem R386819 : Reach 386819 := rs (se 1 (by rfl) ⟨290114, by rfl⟩) R580229
theorem R125023 : Reach 125023 := rs (se 1 (by rfl) ⟨93767, by rfl⟩) R187535
theorem R354449 : Reach 354449 := rs (se 2 (by rfl) ⟨132918, by rfl⟩) R265837
theorem R813563 : Reach 813563 := rs (se 1 (by rfl) ⟨610172, by rfl⟩) R1220345
theorem R1567259 : Reach 1567259 := rs (se 1 (by rfl) ⟨1175444, by rfl⟩) R2350889
theorem R1632869 : Reach 1632869 := rs (se 4 (by rfl) ⟨153081, by rfl⟩) R306163
theorem R1272833 : Reach 1272833 := rs (se 2 (by rfl) ⟨477312, by rfl⟩) R954625
theorem R126319 : Reach 126319 := rs (se 1 (by rfl) ⟨94739, by rfl⟩) R189479
theorem R355873 : Reach 355873 := rs (se 2 (by rfl) ⟨133452, by rfl⟩) R266905
theorem R126697 : Reach 126697 := rs (se 2 (by rfl) ⟨47511, by rfl⟩) R95023
theorem R913619 : Reach 913619 := rs (se 1 (by rfl) ⟨685214, by rfl⟩) R1370429
theorem R160055 : Reach 160055 := rs (se 1 (by rfl) ⟨120041, by rfl⟩) R240083
theorem R160127 : Reach 160127 := rs (se 1 (by rfl) ⟨120095, by rfl⟩) R240191
theorem R258515 : Reach 258515 := rs (se 1 (by rfl) ⟨193886, by rfl⟩) R387773
theorem R881239 : Reach 881239 := rs (se 1 (by rfl) ⟨660929, by rfl⟩) R1321859
theorem R946835 : Reach 946835 := rs (se 1 (by rfl) ⟨710126, by rfl⟩) R1420253
theorem R1078109 : Reach 1078109 := rs (se 3 (by rfl) ⟨202145, by rfl⟩) R404291
theorem R193747 : Reach 193747 := rs (se 1 (by rfl) ⟨145310, by rfl⟩) R290621
theorem R947495 : Reach 947495 := rs (se 1 (by rfl) ⟨710621, by rfl⟩) R1421243
theorem R161351 : Reach 161351 := rs (se 1 (by rfl) ⟨121013, by rfl⟩) R242027
theorem R128623 : Reach 128623 := rs (se 1 (by rfl) ⟨96467, by rfl⟩) R192935
theorem R161531 : Reach 161531 := rs (se 1 (by rfl) ⟨121148, by rfl⟩) R242297
theorem R162089 : Reach 162089 := rs (se 2 (by rfl) ⟨60783, by rfl⟩) R121567
theorem R719513 : Reach 719513 := rs (se 2 (by rfl) ⟨269817, by rfl⟩) R539635
theorem R162665 : Reach 162665 := rs (se 2 (by rfl) ⟨60999, by rfl⟩) R121999
theorem R162719 : Reach 162719 := rs (se 1 (by rfl) ⟨122039, by rfl⟩) R244079
theorem R229175 : Reach 229175 := rs (se 1 (by rfl) ⟨171881, by rfl⟩) R343763
theorem R163655 : Reach 163655 := rs (se 1 (by rfl) ⟨122741, by rfl⟩) R245483
theorem R130987 : Reach 130987 := rs (se 1 (by rfl) ⟨98240, by rfl⟩) R196481
theorem R164267 : Reach 164267 := rs (se 1 (by rfl) ⟨123200, by rfl⟩) R246401
theorem R164359 : Reach 164359 := rs (se 1 (by rfl) ⟨123269, by rfl⟩) R246539
theorem R164447 : Reach 164447 := rs (se 1 (by rfl) ⟨123335, by rfl⟩) R246671
theorem R164807 : Reach 164807 := rs (se 1 (by rfl) ⟨123605, by rfl⟩) R247211
theorem R165167 : Reach 165167 := rs (se 1 (by rfl) ⟨123875, by rfl⟩) R247751
theorem R427355 : Reach 427355 := rs (se 1 (by rfl) ⟨320516, by rfl⟩) R641033
theorem R165671 : Reach 165671 := rs (se 1 (by rfl) ⟨124253, by rfl⟩) R248507
theorem R1411181 : Reach 1411181 := rs (se 3 (by rfl) ⟨264596, by rfl⟩) R529193
theorem R166049 : Reach 166049 := rs (se 2 (by rfl) ⟨62268, by rfl⟩) R124537
theorem R362879 : Reach 362879 := rs (se 1 (by rfl) ⟨272159, by rfl⟩) R544319
theorem R461375 : Reach 461375 := rs (se 1 (by rfl) ⟨346031, by rfl⟩) R692063
theorem R166697 : Reach 166697 := rs (se 2 (by rfl) ⟨62511, by rfl⟩) R125023
theorem R920591 : Reach 920591 := rs (se 1 (by rfl) ⟨690443, by rfl⟩) R1380887
theorem R166967 : Reach 166967 := rs (se 1 (by rfl) ⟨125225, by rfl⟩) R250451
theorem R2526653 : Reach 2526653 := rs (se 3 (by rfl) ⟨473747, by rfl⟩) R947495
theorem R2624993 : Reach 2624993 := rs (se 2 (by rfl) ⟨984372, by rfl⟩) R1968745
theorem R167399 : Reach 167399 := rs (se 1 (by rfl) ⟨125549, by rfl⟩) R251099
theorem R233455 : Reach 233455 := rs (se 1 (by rfl) ⟨175091, by rfl⟩) R350183
theorem R167975 : Reach 167975 := rs (se 1 (by rfl) ⟨125981, by rfl⟩) R251963
theorem R626849 : Reach 626849 := rs (se 2 (by rfl) ⟨235068, by rfl⟩) R470137
theorem R168155 : Reach 168155 := rs (se 1 (by rfl) ⟨126116, by rfl⟩) R252233
theorem R168425 : Reach 168425 := rs (se 2 (by rfl) ⟨63159, by rfl⟩) R126319
theorem R1577717 : Reach 1577717 := rs (se 5 (by rfl) ⟨73955, by rfl⟩) R147911
theorem R136019 : Reach 136019 := rs (se 1 (by rfl) ⟨102014, by rfl⟩) R204029
theorem R693211 : Reach 693211 := rs (se 1 (by rfl) ⟨519908, by rfl⟩) R1039817
theorem R168929 : Reach 168929 := rs (se 2 (by rfl) ⟨63348, by rfl⟩) R126697
theorem R136399 : Reach 136399 := rs (se 1 (by rfl) ⟨102299, by rfl⟩) R204599
theorem R136559 : Reach 136559 := rs (se 1 (by rfl) ⟨102419, by rfl⟩) R204839
theorem R5969371 : Reach 5969371 := rs (se 1 (by rfl) ⟨4477028, by rfl⟩) R8954057
theorem R71143 : Reach 71143 := rs (se 1 (by rfl) ⟨53357, by rfl⟩) R106715
theorem R71151 : Reach 71151 := rs (se 1 (by rfl) ⟨53363, by rfl⟩) R106727
theorem R71259 : Reach 71259 := rs (se 1 (by rfl) ⟨53444, by rfl⟩) R106889
theorem R71323 : Reach 71323 := rs (se 1 (by rfl) ⟨53492, by rfl⟩) R106985
theorem R71407 : Reach 71407 := rs (se 1 (by rfl) ⟨53555, by rfl⟩) R107111
theorem R136991 : Reach 136991 := rs (se 1 (by rfl) ⟨102743, by rfl⟩) R205487
theorem R71495 : Reach 71495 := rs (se 1 (by rfl) ⟨53621, by rfl⟩) R107243
theorem R71515 : Reach 71515 := rs (se 1 (by rfl) ⟨53636, by rfl⟩) R107273
theorem R71583 : Reach 71583 := rs (se 1 (by rfl) ⟨53687, by rfl⟩) R107375
theorem R71751 : Reach 71751 := rs (se 1 (by rfl) ⟨53813, by rfl⟩) R107627
theorem R71911 : Reach 71911 := rs (se 1 (by rfl) ⟨53933, by rfl⟩) R107867
theorem R72095 : Reach 72095 := rs (se 1 (by rfl) ⟨54071, by rfl⟩) R108143
theorem R2038193 : Reach 2038193 := rs (se 2 (by rfl) ⟨764322, by rfl⟩) R1528645
theorem R72143 : Reach 72143 := rs (se 1 (by rfl) ⟨54107, by rfl⟩) R108215
theorem R72167 : Reach 72167 := rs (se 1 (by rfl) ⟨54125, by rfl⟩) R108251
theorem R203239 : Reach 203239 := rs (se 1 (by rfl) ⟨152429, by rfl⟩) R304859
theorem R72283 : Reach 72283 := rs (se 1 (by rfl) ⟨54212, by rfl⟩) R108425
theorem R72351 : Reach 72351 := rs (se 1 (by rfl) ⟨54263, by rfl⟩) R108527
theorem R236299 : Reach 236299 := rs (se 1 (by rfl) ⟨177224, by rfl⟩) R354449
theorem R72519 : Reach 72519 := rs (se 1 (by rfl) ⟨54389, by rfl⟩) R108779
theorem R72559 : Reach 72559 := rs (se 1 (by rfl) ⟨54419, by rfl⟩) R108839
theorem R72615 : Reach 72615 := rs (se 1 (by rfl) ⟨54461, by rfl⟩) R108923
theorem R1088579 : Reach 1088579 := rs (se 1 (by rfl) ⟨816434, by rfl⟩) R1632869
theorem R334919 : Reach 334919 := rs (se 1 (by rfl) ⟨251189, by rfl⟩) R502379
theorem R72795 : Reach 72795 := rs (se 1 (by rfl) ⟨54596, by rfl⟩) R109193
theorem R72911 : Reach 72911 := rs (se 1 (by rfl) ⟨54683, by rfl⟩) R109367
theorem R72935 : Reach 72935 := rs (se 1 (by rfl) ⟨54701, by rfl⟩) R109403
theorem R73031 : Reach 73031 := rs (se 1 (by rfl) ⟨54773, by rfl⟩) R109547
theorem R73167 : Reach 73167 := rs (se 1 (by rfl) ⟨54875, by rfl⟩) R109751
theorem R171497 : Reach 171497 := rs (se 2 (by rfl) ⟨64311, by rfl⟩) R128623
theorem R73327 : Reach 73327 := rs (se 1 (by rfl) ⟨54995, by rfl⟩) R109991
theorem R73383 : Reach 73383 := rs (se 1 (by rfl) ⟨55037, by rfl⟩) R110075
theorem R466651 : Reach 466651 := rs (se 1 (by rfl) ⟨349988, by rfl⟩) R699977
theorem R73447 : Reach 73447 := rs (se 1 (by rfl) ⟨55085, by rfl⟩) R110171
theorem R73503 : Reach 73503 := rs (se 1 (by rfl) ⟨55127, by rfl⟩) R110255
theorem R73583 : Reach 73583 := rs (se 1 (by rfl) ⟨55187, by rfl⟩) R110375
theorem R73639 : Reach 73639 := rs (se 1 (by rfl) ⟨55229, by rfl⟩) R110459
theorem R73919 : Reach 73919 := rs (se 1 (by rfl) ⟨55439, by rfl⟩) R110879
theorem R106703 : Reach 106703 := rs (se 1 (by rfl) ⟨80027, by rfl⟩) R160055
theorem R73935 : Reach 73935 := rs (se 1 (by rfl) ⟨55451, by rfl⟩) R110903
theorem R106751 : Reach 106751 := rs (se 1 (by rfl) ⟨80063, by rfl⟩) R160127
theorem R73983 : Reach 73983 := rs (se 1 (by rfl) ⟨55487, by rfl⟩) R110975
theorem R1122569 : Reach 1122569 := rs (se 2 (by rfl) ⟨420963, by rfl⟩) R841927
theorem R74031 : Reach 74031 := rs (se 1 (by rfl) ⟨55523, by rfl⟩) R111047
theorem R172343 : Reach 172343 := rs (se 1 (by rfl) ⟨129257, by rfl⟩) R258515
theorem R139657 : Reach 139657 := rs (se 2 (by rfl) ⟨52371, by rfl⟩) R104743
theorem R631223 : Reach 631223 := rs (se 1 (by rfl) ⟨473417, by rfl⟩) R946835
theorem R74267 : Reach 74267 := rs (se 1 (by rfl) ⟨55700, by rfl⟩) R111401
theorem R74271 : Reach 74271 := rs (se 1 (by rfl) ⟨55703, by rfl⟩) R111407
theorem R74351 : Reach 74351 := rs (se 1 (by rfl) ⟨55763, by rfl⟩) R111527
theorem R402041 : Reach 402041 := rs (se 2 (by rfl) ⟨150765, by rfl⟩) R301531
theorem R74407 : Reach 74407 := rs (se 1 (by rfl) ⟨55805, by rfl⟩) R111611
theorem R74447 : Reach 74447 := rs (se 1 (by rfl) ⟨55835, by rfl⟩) R111671
theorem R74527 : Reach 74527 := rs (se 1 (by rfl) ⟨55895, by rfl⟩) R111791
theorem R1581869 : Reach 1581869 := rs (se 3 (by rfl) ⟨296600, by rfl⟩) R593201
theorem R107567 : Reach 107567 := rs (se 1 (by rfl) ⟨80675, by rfl⟩) R161351
theorem R74799 : Reach 74799 := rs (se 1 (by rfl) ⟨56099, by rfl⟩) R112199
theorem R74863 : Reach 74863 := rs (se 1 (by rfl) ⟨56147, by rfl⟩) R112295
theorem R107687 : Reach 107687 := rs (se 1 (by rfl) ⟨80765, by rfl⟩) R161531
theorem R74919 : Reach 74919 := rs (se 1 (by rfl) ⟨56189, by rfl⟩) R112379
theorem R74943 : Reach 74943 := rs (se 1 (by rfl) ⟨56207, by rfl⟩) R112415
theorem R74975 : Reach 74975 := rs (se 1 (by rfl) ⟨56231, by rfl⟩) R112463
theorem R75055 : Reach 75055 := rs (se 1 (by rfl) ⟨56291, by rfl⟩) R112583
theorem R75087 : Reach 75087 := rs (se 1 (by rfl) ⟨56315, by rfl⟩) R112631
theorem R108059 : Reach 108059 := rs (se 1 (by rfl) ⟨81044, by rfl⟩) R162089
theorem R108443 : Reach 108443 := rs (se 1 (by rfl) ⟨81332, by rfl⟩) R162665
theorem R108479 : Reach 108479 := rs (se 1 (by rfl) ⟨81359, by rfl⟩) R162719
theorem R108665 : Reach 108665 := rs (se 2 (by rfl) ⟨40749, by rfl⟩) R81499
theorem R109049 : Reach 109049 := rs (se 2 (by rfl) ⟨40893, by rfl⟩) R81787
theorem R109103 : Reach 109103 := rs (se 1 (by rfl) ⟨81827, by rfl⟩) R163655
theorem R174649 : Reach 174649 := rs (se 2 (by rfl) ⟨65493, by rfl⟩) R130987
theorem R142087 : Reach 142087 := rs (se 1 (by rfl) ⟨106565, by rfl⟩) R213131
theorem R109535 : Reach 109535 := rs (se 1 (by rfl) ⟨82151, by rfl⟩) R164303
theorem R6007931 : Reach 6007931 := rs (se 1 (by rfl) ⟨4505948, by rfl⟩) R9011897
theorem R109979 : Reach 109979 := rs (se 1 (by rfl) ⟨82484, by rfl⟩) R164969
theorem R175841 : Reach 175841 := rs (se 2 (by rfl) ⟨65940, by rfl⟩) R131881
theorem R208631 : Reach 208631 := rs (se 1 (by rfl) ⟨156473, by rfl⟩) R312947
theorem R110399 : Reach 110399 := rs (se 1 (by rfl) ⟨82799, by rfl⟩) R165599
theorem R700285 : Reach 700285 := rs (se 3 (by rfl) ⟨131303, by rfl⟩) R262607
theorem R405485 : Reach 405485 := rs (se 3 (by rfl) ⟨76028, by rfl⟩) R152057
theorem R110585 : Reach 110585 := rs (se 2 (by rfl) ⟨41469, by rfl⟩) R82939
theorem R110825 : Reach 110825 := rs (se 2 (by rfl) ⟨41559, by rfl⟩) R83119
theorem R602417 : Reach 602417 := rs (se 2 (by rfl) ⟨225906, by rfl⟩) R451813
theorem R110951 : Reach 110951 := rs (se 1 (by rfl) ⟨83213, by rfl⟩) R166427
theorem R438841 : Reach 438841 := rs (se 2 (by rfl) ⟨164565, by rfl⟩) R329131
theorem R570077 : Reach 570077 := rs (se 3 (by rfl) ⟨106889, by rfl⟩) R213779
theorem R373571 : Reach 373571 := rs (se 1 (by rfl) ⟨280178, by rfl⟩) R560357
theorem R111497 : Reach 111497 := rs (se 2 (by rfl) ⟨41811, by rfl⟩) R83623
theorem R504787 : Reach 504787 := rs (se 1 (by rfl) ⟨378590, by rfl⟩) R757181
theorem R242729 : Reach 242729 := rs (se 2 (by rfl) ⟨91023, by rfl⟩) R182047
theorem R111881 : Reach 111881 := rs (se 2 (by rfl) ⟨41955, by rfl⟩) R83911
theorem R111935 : Reach 111935 := rs (se 1 (by rfl) ⟨83951, by rfl⟩) R167903
theorem R4634003 : Reach 4634003 := rs (se 1 (by rfl) ⟨3475502, by rfl⟩) R6951005
theorem R374381 : Reach 374381 := rs (se 3 (by rfl) ⟨70196, by rfl⟩) R140393
theorem R112361 : Reach 112361 := rs (se 2 (by rfl) ⟨42135, by rfl⟩) R84271
theorem R210671 : Reach 210671 := rs (se 1 (by rfl) ⟨158003, by rfl⟩) R316007
theorem R112367 : Reach 112367 := rs (se 1 (by rfl) ⟨84275, by rfl⟩) R168551
theorem R636797 : Reach 636797 := rs (se 3 (by rfl) ⟨119399, by rfl⟩) R238799
theorem R309257 : Reach 309257 := rs (se 2 (by rfl) ⟨115971, by rfl⟩) R231943
theorem R604331 : Reach 604331 := rs (se 1 (by rfl) ⟨453248, by rfl⟩) R906497
theorem R637307 : Reach 637307 := rs (se 1 (by rfl) ⟨477980, by rfl⟩) R955961
theorem R604691 : Reach 604691 := rs (se 1 (by rfl) ⟨453518, by rfl⟩) R907037
theorem R244457 : Reach 244457 := rs (se 2 (by rfl) ⟨91671, by rfl⟩) R183343
theorem R277415 : Reach 277415 := rs (se 1 (by rfl) ⟨208061, by rfl⟩) R416123
theorem R638057 : Reach 638057 := rs (se 2 (by rfl) ⟨239271, by rfl⟩) R478543
theorem R81103 : Reach 81103 := rs (se 1 (by rfl) ⟨60827, by rfl⟩) R121655
theorem R474497 : Reach 474497 := rs (se 2 (by rfl) ⟨177936, by rfl⟩) R355873
theorem R146939 : Reach 146939 := rs (se 1 (by rfl) ⟨110204, by rfl⟩) R220409
theorem R1982141 : Reach 1982141 := rs (se 3 (by rfl) ⟨371651, by rfl⟩) R743303
theorem R835433 : Reach 835433 := rs (se 2 (by rfl) ⟨313287, by rfl⟩) R626575
theorem R2834351 : Reach 2834351 := rs (se 1 (by rfl) ⟨2125763, by rfl⟩) R4251527
theorem R1851569 : Reach 1851569 := rs (se 2 (by rfl) ⟨694338, by rfl⟩) R1388677
theorem R82111 : Reach 82111 := rs (se 1 (by rfl) ⟨61583, by rfl⟩) R123167
theorem R180473 : Reach 180473 := rs (se 2 (by rfl) ⟨67677, by rfl⟩) R135355
theorem R409859 : Reach 409859 := rs (se 1 (by rfl) ⟨307394, by rfl⟩) R614789
theorem R311633 : Reach 311633 := rs (se 2 (by rfl) ⟨116862, by rfl⟩) R233725
theorem R1229363 : Reach 1229363 := rs (se 1 (by rfl) ⟨922022, by rfl⟩) R1844045
theorem R82543 : Reach 82543 := rs (se 1 (by rfl) ⟨61907, by rfl⟩) R123815
theorem R377459 : Reach 377459 := rs (se 1 (by rfl) ⟨283094, by rfl⟩) R566189
theorem R82651 : Reach 82651 := rs (se 1 (by rfl) ⟨61988, by rfl⟩) R123977
theorem R246779 : Reach 246779 := rs (se 1 (by rfl) ⟨185084, by rfl⟩) R370169
theorem R312673 : Reach 312673 := rs (se 2 (by rfl) ⟨117252, by rfl⟩) R234505
theorem R378269 : Reach 378269 := rs (se 3 (by rfl) ⟨70925, by rfl⟩) R141851
theorem R181673 : Reach 181673 := rs (se 2 (by rfl) ⟨68127, by rfl⟩) R136255
theorem R378431 : Reach 378431 := rs (se 1 (by rfl) ⟨283823, by rfl⟩) R567647
theorem R542375 : Reach 542375 := rs (se 1 (by rfl) ⟨406781, by rfl⟩) R813563
theorem R379079 : Reach 379079 := rs (se 1 (by rfl) ⟨284309, by rfl⟩) R568619
theorem R117119 : Reach 117119 := rs (se 1 (by rfl) ⟨87839, by rfl⟩) R175679
theorem R412249 : Reach 412249 := rs (se 2 (by rfl) ⟨154593, by rfl⟩) R309187
theorem R4410085 : Reach 4410085 := rs (se 4 (by rfl) ⟨413445, by rfl⟩) R826891
theorem R609079 : Reach 609079 := rs (se 1 (by rfl) ⟨456809, by rfl⟩) R913619
theorem R183131 : Reach 183131 := rs (se 1 (by rfl) ⟨137348, by rfl⟩) R274697
theorem R183161 : Reach 183161 := rs (se 2 (by rfl) ⟨68685, by rfl⟩) R137371
theorem R413309 : Reach 413309 := rs (se 3 (by rfl) ⟨77495, by rfl⟩) R154991
theorem R16305953 : Reach 16305953 := rs (se 2 (by rfl) ⟨6114732, by rfl⟩) R12229465
theorem R184295 : Reach 184295 := rs (se 1 (by rfl) ⟨138221, by rfl⟩) R276443
theorem R118759 : Reach 118759 := rs (se 1 (by rfl) ⟨89069, by rfl⟩) R178139
theorem R184315 : Reach 184315 := rs (se 1 (by rfl) ⟨138236, by rfl⟩) R276473
theorem R249911 : Reach 249911 := rs (se 1 (by rfl) ⟨187433, by rfl⟩) R374867
theorem R250235 : Reach 250235 := rs (se 1 (by rfl) ⟨187676, by rfl⟩) R375353
theorem R479675 : Reach 479675 := rs (se 1 (by rfl) ⟨359756, by rfl⟩) R719513
theorem R250505 : Reach 250505 := rs (se 2 (by rfl) ⟨93939, by rfl⟩) R187879
theorem R152783 : Reach 152783 := rs (se 1 (by rfl) ⟨114587, by rfl⟩) R229175
theorem R1398169 : Reach 1398169 := rs (se 2 (by rfl) ⟨524313, by rfl⟩) R1048627
theorem R415165 : Reach 415165 := rs (se 3 (by rfl) ⟨77843, by rfl⟩) R155687
theorem R546749 : Reach 546749 := rs (se 3 (by rfl) ⟨102515, by rfl⟩) R205031
theorem R350171 : Reach 350171 := rs (se 1 (by rfl) ⟨262628, by rfl⟩) R525257
theorem R153569 : Reach 153569 := rs (se 2 (by rfl) ⟨57588, by rfl⟩) R115177
theorem R88247 : Reach 88247 := rs (se 1 (by rfl) ⟨66185, by rfl⟩) R132371
theorem R186857 : Reach 186857 := rs (se 2 (by rfl) ⟨70071, by rfl⟩) R140143
theorem R186907 : Reach 186907 := rs (se 1 (by rfl) ⟨140180, by rfl⟩) R280361
theorem R154423 : Reach 154423 := rs (se 1 (by rfl) ⟨115817, by rfl⟩) R231635
theorem R548207 : Reach 548207 := rs (se 1 (by rfl) ⟨411155, by rfl⟩) R822311
theorem R318953 : Reach 318953 := rs (se 2 (by rfl) ⟨119607, by rfl⟩) R239215
theorem R155209 : Reach 155209 := rs (se 2 (by rfl) ⟨58203, by rfl⟩) R116407
theorem R941867 : Reach 941867 := rs (se 1 (by rfl) ⟨706400, by rfl⟩) R1412801
theorem R122735 : Reach 122735 := rs (se 1 (by rfl) ⟨92051, by rfl⟩) R184103
theorem R188315 : Reach 188315 := rs (se 1 (by rfl) ⟨141236, by rfl⟩) R282473
theorem R319955 : Reach 319955 := rs (se 1 (by rfl) ⟨239966, by rfl⟩) R479933
theorem R123599 : Reach 123599 := rs (se 1 (by rfl) ⟨92699, by rfl⟩) R185399
theorem R1238813 : Reach 1238813 := rs (se 3 (by rfl) ⟨232277, by rfl⟩) R464555
theorem R124895 : Reach 124895 := rs (se 1 (by rfl) ⟨93671, by rfl⟩) R187343
theorem R551123 : Reach 551123 := rs (se 1 (by rfl) ⟨413342, by rfl⟩) R826685
theorem R125239 : Reach 125239 := rs (se 1 (by rfl) ⟨93929, by rfl⟩) R187859
theorem R289295 : Reach 289295 := rs (se 1 (by rfl) ⟨216971, by rfl⟩) R433943
theorem R420497 : Reach 420497 := rs (se 2 (by rfl) ⟨157686, by rfl⟩) R315373
theorem R1174985 : Reach 1174985 := rs (se 2 (by rfl) ⟨440619, by rfl⟩) R881239
theorem R290375 : Reach 290375 := rs (se 1 (by rfl) ⟨217781, by rfl⟩) R435563
theorem R126535 : Reach 126535 := rs (se 1 (by rfl) ⟨94901, by rfl⟩) R189803
theorem R552743 : Reach 552743 := rs (se 1 (by rfl) ⟨414557, by rfl⟩) R829115
theorem R257879 : Reach 257879 := rs (se 1 (by rfl) ⟨193409, by rfl⟩) R386819
theorem R258329 : Reach 258329 := rs (se 2 (by rfl) ⟨96873, by rfl⟩) R193747
theorem R1044839 : Reach 1044839 := rs (se 1 (by rfl) ⟨783629, by rfl⟩) R1567259
theorem R160199 : Reach 160199 := rs (se 1 (by rfl) ⟨120149, by rfl⟩) R240299
theorem R848555 : Reach 848555 := rs (se 1 (by rfl) ⟨636416, by rfl⟩) R1272833
theorem R160559 : Reach 160559 := rs (se 1 (by rfl) ⟨120419, by rfl⟩) R240839
theorem R160649 : Reach 160649 := rs (se 2 (by rfl) ⟨60243, by rfl⟩) R120487
theorem R685523 : Reach 685523 := rs (se 1 (by rfl) ⟨514142, by rfl⟩) R1028285
theorem R161423 : Reach 161423 := rs (se 1 (by rfl) ⟨121067, by rfl⟩) R242135
theorem R161513 : Reach 161513 := rs (se 2 (by rfl) ⟨60567, by rfl⟩) R121135
theorem R718739 : Reach 718739 := rs (se 1 (by rfl) ⟨539054, by rfl⟩) R1078109
theorem R2717873 : Reach 2717873 := rs (se 2 (by rfl) ⟨1019202, by rfl⟩) R2038405
theorem R227539 : Reach 227539 := rs (se 1 (by rfl) ⟨170654, by rfl⟩) R341309
theorem R162395 : Reach 162395 := rs (se 1 (by rfl) ⟨121796, by rfl⟩) R243593
theorem R162539 : Reach 162539 := rs (se 1 (by rfl) ⟨121904, by rfl⟩) R243809
theorem R163151 : Reach 163151 := rs (se 1 (by rfl) ⟨122363, by rfl⟩) R244727
theorem R163241 : Reach 163241 := rs (se 2 (by rfl) ⟨61215, by rfl⟩) R122431
theorem R163439 : Reach 163439 := rs (se 1 (by rfl) ⟨122579, by rfl⟩) R245159
theorem R163727 : Reach 163727 := rs (se 1 (by rfl) ⟨122795, by rfl⟩) R245591
theorem R819575 : Reach 819575 := rs (se 1 (by rfl) ⟨614681, by rfl⟩) R1229363
theorem R164519 : Reach 164519 := rs (se 1 (by rfl) ⟨123389, by rfl⟩) R246779
theorem R361583 : Reach 361583 := rs (se 1 (by rfl) ⟨271187, by rfl⟩) R542375
theorem R853213 : Reach 853213 := rs (se 3 (by rfl) ⟨159977, by rfl⟩) R319955
theorem R362717 : Reach 362717 := rs (se 3 (by rfl) ⟨68009, by rfl⟩) R136019
theorem R1083941 : Reach 1083941 := rs (se 4 (by rfl) ⟨101619, by rfl⟩) R203239
theorem R166607 : Reach 166607 := rs (se 1 (by rfl) ⟨124955, by rfl⟩) R249911
theorem R166823 : Reach 166823 := rs (se 1 (by rfl) ⟨125117, by rfl⟩) R250235
theorem R166985 : Reach 166985 := rs (se 2 (by rfl) ⟨62619, by rfl⟩) R125239
theorem R167003 : Reach 167003 := rs (se 1 (by rfl) ⟨125252, by rfl⟩) R250505
theorem R1051811 : Reach 1051811 := rs (se 1 (by rfl) ⟨788858, by rfl⟩) R1577717
theorem R232865 : Reach 232865 := rs (se 2 (by rfl) ⟨87324, by rfl⟩) R174649
theorem R101855 : Reach 101855 := rs (se 1 (by rfl) ⟨76391, by rfl⟩) R152783
theorem R364499 : Reach 364499 := rs (se 1 (by rfl) ⟨273374, by rfl⟩) R546749
theorem R233447 : Reach 233447 := rs (se 1 (by rfl) ⟨175085, by rfl⟩) R350171
theorem R102379 : Reach 102379 := rs (se 1 (by rfl) ⟨76784, by rfl⟩) R153569
theorem R725719 : Reach 725719 := rs (se 1 (by rfl) ⟨544289, by rfl⟩) R1088579
theorem R365309 : Reach 365309 := rs (se 3 (by rfl) ⟨68495, by rfl⟩) R136991
theorem R168713 : Reach 168713 := rs (se 2 (by rfl) ⟨63267, by rfl⟩) R126535
theorem R365471 : Reach 365471 := rs (se 1 (by rfl) ⟨274103, by rfl⟩) R548207
theorem R627911 : Reach 627911 := rs (se 1 (by rfl) ⟨470933, by rfl⟩) R941867
theorem R71135 : Reach 71135 := rs (se 1 (by rfl) ⟨53351, by rfl⟩) R106703
theorem R71167 : Reach 71167 := rs (se 1 (by rfl) ⟨53375, by rfl⟩) R106751
theorem R235325 : Reach 235325 := rs (se 3 (by rfl) ⟨44123, by rfl⟩) R88247
theorem R1054579 : Reach 1054579 := rs (se 1 (by rfl) ⟨790934, by rfl⟩) R1581869
theorem R71711 : Reach 71711 := rs (se 1 (by rfl) ⟨53783, by rfl⟩) R107567
theorem R71791 : Reach 71791 := rs (se 1 (by rfl) ⟨53843, by rfl⟩) R107687
theorem R72039 : Reach 72039 := rs (se 1 (by rfl) ⟨54029, by rfl⟩) R108059
theorem R825875 : Reach 825875 := rs (se 1 (by rfl) ⟨619406, by rfl⟩) R1238813
theorem R72295 : Reach 72295 := rs (se 1 (by rfl) ⟨54221, by rfl⟩) R108443
theorem R924281 : Reach 924281 := rs (se 2 (by rfl) ⟨346605, by rfl⟩) R693211
theorem R72319 : Reach 72319 := rs (se 1 (by rfl) ⟨54239, by rfl⟩) R108479
theorem R72443 : Reach 72443 := rs (se 1 (by rfl) ⟨54332, by rfl⟩) R108665
theorem R367415 : Reach 367415 := rs (se 1 (by rfl) ⟨275561, by rfl⟩) R551123
theorem R72699 : Reach 72699 := rs (se 1 (by rfl) ⟨54524, by rfl⟩) R109049
theorem R72735 : Reach 72735 := rs (se 1 (by rfl) ⟨54551, by rfl⟩) R109103
theorem R73023 : Reach 73023 := rs (se 1 (by rfl) ⟨54767, by rfl⟩) R109535
theorem R4005287 : Reach 4005287 := rs (se 1 (by rfl) ⟨3003965, by rfl⟩) R6007931
theorem R73319 : Reach 73319 := rs (se 1 (by rfl) ⟨54989, by rfl⟩) R109979
theorem R139087 : Reach 139087 := rs (se 1 (by rfl) ⟨104315, by rfl⟩) R208631
theorem R368495 : Reach 368495 := rs (se 1 (by rfl) ⟨276371, by rfl⟩) R552743
theorem R73599 : Reach 73599 := rs (se 1 (by rfl) ⟨55199, by rfl⟩) R110399
theorem R171919 : Reach 171919 := rs (se 1 (by rfl) ⟨128939, by rfl⟩) R257879
theorem R270323 : Reach 270323 := rs (se 1 (by rfl) ⟨202742, by rfl⟩) R405485
theorem R73723 : Reach 73723 := rs (se 1 (by rfl) ⟨55292, by rfl⟩) R110585
theorem R73883 : Reach 73883 := rs (se 1 (by rfl) ⟨55412, by rfl⟩) R110825
theorem R172219 : Reach 172219 := rs (se 1 (by rfl) ⟨129164, by rfl⟩) R258329
theorem R401611 : Reach 401611 := rs (se 1 (by rfl) ⟨301208, by rfl⟩) R602417
theorem R696559 : Reach 696559 := rs (se 1 (by rfl) ⟨522419, by rfl⟩) R1044839
theorem R73967 : Reach 73967 := rs (se 1 (by rfl) ⟨55475, by rfl⟩) R110951
theorem R303385 : Reach 303385 := rs (se 2 (by rfl) ⟨113769, by rfl⟩) R227539
theorem R106799 : Reach 106799 := rs (se 1 (by rfl) ⟨80099, by rfl⟩) R160199
theorem R565703 : Reach 565703 := rs (se 1 (by rfl) ⟨424277, by rfl⟩) R848555
theorem R107039 : Reach 107039 := rs (se 1 (by rfl) ⟨80279, by rfl⟩) R160559
theorem R107099 : Reach 107099 := rs (se 1 (by rfl) ⟨80324, by rfl⟩) R160649
theorem R74331 : Reach 74331 := rs (se 1 (by rfl) ⟨55748, by rfl⟩) R111497
theorem R74587 : Reach 74587 := rs (se 1 (by rfl) ⟨55940, by rfl⟩) R111881
theorem R74623 : Reach 74623 := rs (se 1 (by rfl) ⟨55967, by rfl⟩) R111935
theorem R3089335 : Reach 3089335 := rs (se 1 (by rfl) ⟨2317001, by rfl⟩) R4634003
theorem R205897 : Reach 205897 := rs (se 2 (by rfl) ⟨77211, by rfl⟩) R154423
theorem R107615 : Reach 107615 := rs (se 1 (by rfl) ⟨80711, by rfl⟩) R161423
theorem R107675 : Reach 107675 := rs (se 1 (by rfl) ⟨80756, by rfl⟩) R161513
theorem R74907 : Reach 74907 := rs (se 1 (by rfl) ⟨56180, by rfl⟩) R112361
theorem R140447 : Reach 140447 := rs (se 1 (by rfl) ⟨105335, by rfl⟩) R210671
theorem R74911 : Reach 74911 := rs (se 1 (by rfl) ⟨56183, by rfl⟩) R112367
theorem R206171 : Reach 206171 := rs (se 1 (by rfl) ⟨154628, by rfl⟩) R309257
theorem R402887 : Reach 402887 := rs (se 1 (by rfl) ⟨302165, by rfl⟩) R604331
theorem R1811915 : Reach 1811915 := rs (se 1 (by rfl) ⟨1358936, by rfl⟩) R2717873
theorem R108137 : Reach 108137 := rs (se 2 (by rfl) ⟨40551, by rfl⟩) R81103
theorem R403127 : Reach 403127 := rs (se 1 (by rfl) ⟨302345, by rfl⟩) R604691
theorem R108263 : Reach 108263 := rs (se 1 (by rfl) ⟨81197, by rfl⟩) R162395
theorem R108359 : Reach 108359 := rs (se 1 (by rfl) ⟨81269, by rfl⟩) R162539
theorem R206945 : Reach 206945 := rs (se 2 (by rfl) ⟨77604, by rfl⟩) R155209
theorem R108767 : Reach 108767 := rs (se 1 (by rfl) ⟨81575, by rfl⟩) R163151
theorem R108827 : Reach 108827 := rs (se 1 (by rfl) ⟨81620, by rfl⟩) R163241
theorem R108959 : Reach 108959 := rs (se 1 (by rfl) ⟨81719, by rfl⟩) R163439
theorem R1321427 : Reach 1321427 := rs (se 1 (by rfl) ⟨991070, by rfl⟩) R1982141
theorem R109151 : Reach 109151 := rs (se 1 (by rfl) ⟨81863, by rfl⟩) R163727
theorem R273239 : Reach 273239 := rs (se 1 (by rfl) ⟨204929, by rfl⟩) R409859
theorem R207755 : Reach 207755 := rs (se 1 (by rfl) ⟨155816, by rfl⟩) R311633
theorem R109481 : Reach 109481 := rs (se 2 (by rfl) ⟨41055, by rfl⟩) R82111
theorem R109511 : Reach 109511 := rs (se 1 (by rfl) ⟨82133, by rfl⟩) R164267
theorem R109631 : Reach 109631 := rs (se 1 (by rfl) ⟨82223, by rfl⟩) R164447
theorem R109871 : Reach 109871 := rs (se 1 (by rfl) ⟨82403, by rfl⟩) R164807
theorem R110057 : Reach 110057 := rs (se 2 (by rfl) ⟨41271, by rfl⟩) R82543
theorem R110111 : Reach 110111 := rs (se 1 (by rfl) ⟨82583, by rfl⟩) R165167
theorem R110201 : Reach 110201 := rs (se 2 (by rfl) ⟨41325, by rfl⟩) R82651
theorem R110447 : Reach 110447 := rs (se 1 (by rfl) ⟨82835, by rfl⟩) R165671
theorem R110699 : Reach 110699 := rs (se 1 (by rfl) ⟨83024, by rfl⟩) R166049
theorem R241919 : Reach 241919 := rs (se 1 (by rfl) ⟨181439, by rfl⟩) R362879
theorem R78079 : Reach 78079 := rs (se 1 (by rfl) ⟨58559, by rfl⟩) R117119
theorem R307583 : Reach 307583 := rs (se 1 (by rfl) ⟨230687, by rfl⟩) R461375
theorem R111131 : Reach 111131 := rs (se 1 (by rfl) ⟨83348, by rfl⟩) R166697
theorem R111311 : Reach 111311 := rs (se 1 (by rfl) ⟨83483, by rfl⟩) R166967
theorem R1684435 : Reach 1684435 := rs (se 1 (by rfl) ⟨1263326, by rfl⟩) R2526653
theorem R1749995 : Reach 1749995 := rs (se 1 (by rfl) ⟨1312496, by rfl⟩) R2624993
theorem R111599 : Reach 111599 := rs (se 1 (by rfl) ⟨83699, by rfl⟩) R167399
theorem R111983 : Reach 111983 := rs (se 1 (by rfl) ⟨83987, by rfl⟩) R167975
theorem R112103 : Reach 112103 := rs (se 1 (by rfl) ⟨84077, by rfl⟩) R168155
theorem R2340485 : Reach 2340485 := rs (se 4 (by rfl) ⟨219420, by rfl⟩) R438841
theorem R112283 : Reach 112283 := rs (se 1 (by rfl) ⟨84212, by rfl⟩) R168425
theorem R112619 : Reach 112619 := rs (se 1 (by rfl) ⟨84464, by rfl⟩) R168929
theorem R5880113 : Reach 5880113 := rs (se 2 (by rfl) ⟨2205042, by rfl⟩) R4410085
theorem R1358795 : Reach 1358795 := rs (se 1 (by rfl) ⟨1019096, by rfl⟩) R2038193
theorem R212635 : Reach 212635 := rs (se 1 (by rfl) ⟨159476, by rfl⟩) R318953
theorem R933713 : Reach 933713 := rs (se 2 (by rfl) ⟨350142, by rfl⟩) R700285
theorem R81823 : Reach 81823 := rs (se 1 (by rfl) ⟨61367, by rfl⟩) R122735
theorem R311273 : Reach 311273 := rs (se 2 (by rfl) ⟨116727, by rfl⟩) R233455
theorem R245753 : Reach 245753 := rs (se 2 (by rfl) ⟨92157, by rfl⟩) R184315
theorem R114895 : Reach 114895 := rs (se 1 (by rfl) ⟨86171, by rfl⟩) R172343
theorem R82399 : Reach 82399 := rs (se 1 (by rfl) ⟨61799, by rfl⟩) R123599
theorem R673049 : Reach 673049 := rs (se 2 (by rfl) ⟨252393, by rfl⟩) R504787
theorem R83263 : Reach 83263 := rs (se 1 (by rfl) ⟨62447, by rfl⟩) R124895
theorem R181865 : Reach 181865 := rs (se 2 (by rfl) ⟨68199, by rfl⟩) R136399
theorem R280331 : Reach 280331 := rs (se 1 (by rfl) ⟨210248, by rfl⟩) R420497
theorem R117227 : Reach 117227 := rs (se 1 (by rfl) ⟨87920, by rfl⟩) R175841
theorem R380051 : Reach 380051 := rs (se 1 (by rfl) ⟨285038, by rfl⟩) R570077
theorem R249047 : Reach 249047 := rs (se 1 (by rfl) ⟨186785, by rfl⟩) R373571
theorem R249209 : Reach 249209 := rs (se 2 (by rfl) ⟨93453, by rfl⟩) R186907
theorem R315065 : Reach 315065 := rs (se 2 (by rfl) ⟨118149, by rfl⟩) R236299
theorem R249587 : Reach 249587 := rs (se 1 (by rfl) ⟨187190, by rfl⟩) R374381
theorem R479159 : Reach 479159 := rs (se 1 (by rfl) ⟨359369, by rfl⟩) R718739
theorem R1102157 : Reach 1102157 := rs (se 3 (by rfl) ⟨206654, by rfl⟩) R413309
theorem R184943 : Reach 184943 := rs (se 1 (by rfl) ⟨138707, by rfl⟩) R277415
theorem R316331 : Reach 316331 := rs (se 1 (by rfl) ⟨237248, by rfl⟩) R474497
theorem R1889567 : Reach 1889567 := rs (se 1 (by rfl) ⟨1417175, by rfl⟩) R2834351
theorem R1234379 : Reach 1234379 := rs (se 1 (by rfl) ⟨925784, by rfl⟩) R1851569
theorem R251639 : Reach 251639 := rs (se 1 (by rfl) ⟨188729, by rfl⟩) R377459
theorem R186209 : Reach 186209 := rs (se 2 (by rfl) ⟨69828, by rfl⟩) R139657
theorem R481261 : Reach 481261 := rs (se 3 (by rfl) ⟨90236, by rfl⟩) R180473
theorem R219145 : Reach 219145 := rs (se 2 (by rfl) ⟨82179, by rfl⟩) R164359
theorem R284903 : Reach 284903 := rs (se 1 (by rfl) ⟨213677, by rfl⟩) R427355
theorem R252179 : Reach 252179 := rs (se 1 (by rfl) ⟨189134, by rfl⟩) R378269
theorem R121115 : Reach 121115 := rs (se 1 (by rfl) ⟨90836, by rfl⟩) R181673
theorem R252287 : Reach 252287 := rs (se 1 (by rfl) ⟨189215, by rfl⟩) R378431
theorem R940787 : Reach 940787 := rs (se 1 (by rfl) ⟨705590, by rfl⟩) R1411181
theorem R252719 : Reach 252719 := rs (se 1 (by rfl) ⟨189539, by rfl⟩) R379079
theorem R1072109 : Reach 1072109 := rs (se 3 (by rfl) ⟨201020, by rfl⟩) R402041
theorem R416897 : Reach 416897 := rs (se 2 (by rfl) ⟨156336, by rfl⟩) R312673
theorem R122087 : Reach 122087 := rs (se 1 (by rfl) ⟨91565, by rfl⟩) R183131
theorem R122107 : Reach 122107 := rs (se 1 (by rfl) ⟨91580, by rfl⟩) R183161
theorem R613727 : Reach 613727 := rs (se 1 (by rfl) ⟨460295, by rfl⟩) R920591
theorem R122863 : Reach 122863 := rs (se 1 (by rfl) ⟨92147, by rfl⟩) R184295
theorem R417899 : Reach 417899 := rs (se 1 (by rfl) ⟨313424, by rfl⟩) R626849
theorem R319783 : Reach 319783 := rs (se 1 (by rfl) ⟨239837, by rfl⟩) R479675
theorem R549665 : Reach 549665 := rs (se 2 (by rfl) ⟨206124, by rfl⟩) R412249
theorem R91039 : Reach 91039 := rs (se 1 (by rfl) ⟨68279, by rfl⟩) R136559
theorem R189449 : Reach 189449 := rs (se 2 (by rfl) ⟨71043, by rfl⟩) R142087
theorem R812105 : Reach 812105 := rs (se 2 (by rfl) ⟨304539, by rfl⟩) R609079
theorem R124571 : Reach 124571 := rs (se 1 (by rfl) ⟨93428, by rfl⟩) R186857
theorem R223279 : Reach 223279 := rs (se 1 (by rfl) ⟨167459, by rfl⟩) R334919
theorem R125543 : Reach 125543 := rs (se 1 (by rfl) ⟨94157, by rfl⟩) R188315
theorem R158345 : Reach 158345 := rs (se 2 (by rfl) ⟨59379, by rfl⟩) R118759
theorem R748379 : Reach 748379 := rs (se 1 (by rfl) ⟨561284, by rfl⟩) R1122569
theorem R420815 : Reach 420815 := rs (se 1 (by rfl) ⟨315611, by rfl⟩) R631223
theorem R192863 : Reach 192863 := rs (se 1 (by rfl) ⟨144647, by rfl⟩) R289295
theorem R1864225 : Reach 1864225 := rs (se 2 (by rfl) ⟨699084, by rfl⟩) R1398169
theorem R553553 : Reach 553553 := rs (se 2 (by rfl) ⟨207582, by rfl⟩) R415165
theorem R7959161 : Reach 7959161 := rs (se 2 (by rfl) ⟨2984685, by rfl⟩) R5969371
theorem R783323 : Reach 783323 := rs (se 1 (by rfl) ⟨587492, by rfl⟩) R1174985
theorem R193583 : Reach 193583 := rs (se 1 (by rfl) ⟨145187, by rfl⟩) R290375
theorem R173930165 : Reach 173930165 := rs (se 5 (by rfl) ⟨8152976, by rfl⟩) R16305953
theorem R161819 : Reach 161819 := rs (se 1 (by rfl) ⟨121364, by rfl⟩) R242729
theorem R457015 : Reach 457015 := rs (se 1 (by rfl) ⟨342761, by rfl⟩) R685523
theorem R424531 : Reach 424531 := rs (se 1 (by rfl) ⟨318398, by rfl⟩) R636797
theorem R457325 : Reach 457325 := rs (se 3 (by rfl) ⟨85748, by rfl⟩) R171497
theorem R391837 : Reach 391837 := rs (se 3 (by rfl) ⟨73469, by rfl⟩) R146939
theorem R424871 : Reach 424871 := rs (se 1 (by rfl) ⟨318653, by rfl⟩) R637307
theorem R162971 : Reach 162971 := rs (se 1 (by rfl) ⟨122228, by rfl⟩) R244457
theorem R425371 : Reach 425371 := rs (se 1 (by rfl) ⟨319028, by rfl⟩) R638057
theorem R622201 : Reach 622201 := rs (se 2 (by rfl) ⟨233325, by rfl⟩) R466651
theorem R556955 : Reach 556955 := rs (se 1 (by rfl) ⟨417716, by rfl⟩) R835433
theorem R229625 : Reach 229625 := rs (se 2 (by rfl) ⟨86109, by rfl⟩) R172219
theorem R426377 : Reach 426377 := rs (se 2 (by rfl) ⟨159891, by rfl⟩) R319783
theorem R722627 : Reach 722627 := rs (se 1 (by rfl) ⟨541970, by rfl⟩) R1083941
theorem R166031 : Reach 166031 := rs (se 1 (by rfl) ⟨124523, by rfl⟩) R249047
theorem R166139 : Reach 166139 := rs (se 1 (by rfl) ⟨124604, by rfl⟩) R249209
theorem R166391 : Reach 166391 := rs (se 1 (by rfl) ⟨124793, by rfl⟩) R249587
theorem R167759 : Reach 167759 := rs (se 1 (by rfl) ⟨125819, by rfl⟩) R251639
theorem R168119 : Reach 168119 := rs (se 1 (by rfl) ⟨126089, by rfl⟩) R252179
theorem R168191 : Reach 168191 := rs (se 1 (by rfl) ⟨126143, by rfl⟩) R252287
theorem R627191 : Reach 627191 := rs (se 1 (by rfl) ⟨470393, by rfl⟩) R940787
theorem R168479 : Reach 168479 := rs (se 1 (by rfl) ⟨126359, by rfl⟩) R252719
theorem R627533 : Reach 627533 := rs (se 3 (by rfl) ⟨117662, by rfl⟩) R235325
theorem R136505 : Reach 136505 := rs (se 2 (by rfl) ⟨51189, by rfl⟩) R102379
theorem R71199 : Reach 71199 := rs (se 1 (by rfl) ⟨53399, by rfl⟩) R106799
theorem R104105 : Reach 104105 := rs (se 2 (by rfl) ⟨39039, by rfl⟩) R78079
theorem R71359 : Reach 71359 := rs (se 1 (by rfl) ⟨53519, by rfl⟩) R107039
theorem R71399 : Reach 71399 := rs (se 1 (by rfl) ⟨53549, by rfl⟩) R107099
theorem R366443 : Reach 366443 := rs (se 1 (by rfl) ⟨274832, by rfl⟩) R549665
theorem R71743 : Reach 71743 := rs (se 1 (by rfl) ⟨53807, by rfl⟩) R107615
theorem R71783 : Reach 71783 := rs (se 1 (by rfl) ⟨53837, by rfl⟩) R107675
theorem R137447 : Reach 137447 := rs (se 1 (by rfl) ⟨103085, by rfl⟩) R206171
theorem R268591 : Reach 268591 := rs (se 1 (by rfl) ⟨201443, by rfl⟩) R402887
theorem R72091 : Reach 72091 := rs (se 1 (by rfl) ⟨54068, by rfl⟩) R108137
theorem R268751 : Reach 268751 := rs (se 1 (by rfl) ⟨201563, by rfl⟩) R403127
theorem R72175 : Reach 72175 := rs (se 1 (by rfl) ⟨54131, by rfl⟩) R108263
theorem R72239 : Reach 72239 := rs (se 1 (by rfl) ⟨54179, by rfl⟩) R108359
theorem R137963 : Reach 137963 := rs (se 1 (by rfl) ⟨103472, by rfl⟩) R206945
theorem R72511 : Reach 72511 := rs (se 1 (by rfl) ⟨54383, by rfl⟩) R108767
theorem R72551 : Reach 72551 := rs (se 1 (by rfl) ⟨54413, by rfl⟩) R108827
theorem R72639 : Reach 72639 := rs (se 1 (by rfl) ⟨54479, by rfl⟩) R108959
theorem R72767 : Reach 72767 := rs (se 1 (by rfl) ⟨54575, by rfl⟩) R109151
theorem R105563 : Reach 105563 := rs (se 1 (by rfl) ⟨79172, by rfl⟩) R158345
theorem R498919 : Reach 498919 := rs (se 1 (by rfl) ⟨374189, by rfl⟩) R748379
theorem R138503 : Reach 138503 := rs (se 1 (by rfl) ⟨103877, by rfl⟩) R207755
theorem R72987 : Reach 72987 := rs (se 1 (by rfl) ⟨54740, by rfl⟩) R109481
theorem R73007 : Reach 73007 := rs (se 1 (by rfl) ⟨54755, by rfl⟩) R109511
theorem R73087 : Reach 73087 := rs (se 1 (by rfl) ⟨54815, by rfl⟩) R109631
theorem R73247 : Reach 73247 := rs (se 1 (by rfl) ⟨54935, by rfl⟩) R109871
theorem R73371 : Reach 73371 := rs (se 1 (by rfl) ⟨55028, by rfl⟩) R110057
theorem R73407 : Reach 73407 := rs (se 1 (by rfl) ⟨55055, by rfl⟩) R110111
theorem R73467 : Reach 73467 := rs (se 1 (by rfl) ⟨55100, by rfl⟩) R110201
theorem R73631 : Reach 73631 := rs (se 1 (by rfl) ⟨55223, by rfl⟩) R110447
theorem R73799 : Reach 73799 := rs (se 1 (by rfl) ⟨55349, by rfl⟩) R110699
theorem R205055 : Reach 205055 := rs (se 1 (by rfl) ⟨153791, by rfl⟩) R307583
theorem R74087 : Reach 74087 := rs (se 1 (by rfl) ⟨55565, by rfl⟩) R111131
theorem R369035 : Reach 369035 := rs (se 1 (by rfl) ⟨276776, by rfl⟩) R553553
theorem R74207 : Reach 74207 := rs (se 1 (by rfl) ⟨55655, by rfl⟩) R111311
theorem R74399 : Reach 74399 := rs (se 1 (by rfl) ⟨55799, by rfl⟩) R111599
theorem R566041 : Reach 566041 := rs (se 2 (by rfl) ⟨212265, by rfl⟩) R424531
theorem R74655 : Reach 74655 := rs (se 1 (by rfl) ⟨55991, by rfl⟩) R111983
theorem R74735 : Reach 74735 := rs (se 1 (by rfl) ⟨56051, by rfl⟩) R112103
theorem R74855 : Reach 74855 := rs (se 1 (by rfl) ⟨56141, by rfl⟩) R112283
theorem R271613 : Reach 271613 := rs (se 3 (by rfl) ⟨50927, by rfl⟩) R101855
theorem R75079 : Reach 75079 := rs (se 1 (by rfl) ⟨56309, by rfl⟩) R112619
theorem R107879 : Reach 107879 := rs (se 1 (by rfl) ⟨80909, by rfl⟩) R161819
theorem R304883 : Reach 304883 := rs (se 1 (by rfl) ⟨228662, by rfl⟩) R457325
theorem R567161 : Reach 567161 := rs (se 2 (by rfl) ⟨212685, by rfl⟩) R425371
theorem R108647 : Reach 108647 := rs (se 1 (by rfl) ⟨81485, by rfl⟩) R162971
theorem R829601 : Reach 829601 := rs (se 2 (by rfl) ⟨311100, by rfl⟩) R622201
theorem R109097 : Reach 109097 := rs (se 2 (by rfl) ⟨40911, by rfl⟩) R81823
theorem R371303 : Reach 371303 := rs (se 1 (by rfl) ⟨278477, by rfl⟩) R556955
theorem R207515 : Reach 207515 := rs (se 1 (by rfl) ⟨155636, by rfl⟩) R311273
theorem R1190821 : Reach 1190821 := rs (se 4 (by rfl) ⟨111639, by rfl⟩) R223279
theorem R535481 : Reach 535481 := rs (se 2 (by rfl) ⟨200805, by rfl⟩) R401611
theorem R928745 : Reach 928745 := rs (se 2 (by rfl) ⟨348279, by rfl⟩) R696559
theorem R404513 : Reach 404513 := rs (se 2 (by rfl) ⟨151692, by rfl⟩) R303385
theorem R109679 : Reach 109679 := rs (se 1 (by rfl) ⟨82259, by rfl⟩) R164519
theorem R109865 : Reach 109865 := rs (se 2 (by rfl) ⟨41199, by rfl⟩) R82399
theorem R241055 : Reach 241055 := rs (se 1 (by rfl) ⟨180791, by rfl⟩) R361583
theorem R274529 : Reach 274529 := rs (se 2 (by rfl) ⟨102948, by rfl⟩) R205897
theorem R241811 : Reach 241811 := rs (se 1 (by rfl) ⟨181358, by rfl⟩) R362717
theorem R111017 : Reach 111017 := rs (se 2 (by rfl) ⟨41631, by rfl⟩) R83263
theorem R111071 : Reach 111071 := rs (se 1 (by rfl) ⟨83303, by rfl⟩) R166607
theorem R111215 : Reach 111215 := rs (se 1 (by rfl) ⟨83411, by rfl⟩) R166823
theorem R111323 : Reach 111323 := rs (se 1 (by rfl) ⟨83492, by rfl⟩) R166985
theorem R111335 : Reach 111335 := rs (se 1 (by rfl) ⟨83501, by rfl⟩) R167003
theorem R701207 : Reach 701207 := rs (se 1 (by rfl) ⟨525905, by rfl⟩) R1051811
theorem R210043 : Reach 210043 := rs (se 1 (by rfl) ⟨157532, by rfl⟩) R315065
theorem R242999 : Reach 242999 := rs (se 1 (by rfl) ⟨182249, by rfl⟩) R364499
theorem R734771 : Reach 734771 := rs (se 1 (by rfl) ⟨551078, by rfl⟩) R1102157
theorem R243539 : Reach 243539 := rs (se 1 (by rfl) ⟨182654, by rfl⟩) R365309
theorem R112475 : Reach 112475 := rs (se 1 (by rfl) ⟨84356, by rfl⟩) R168713
theorem R243647 : Reach 243647 := rs (se 1 (by rfl) ⟨182735, by rfl⟩) R365471
theorem R210887 : Reach 210887 := rs (se 1 (by rfl) ⟨158165, by rfl⟩) R316331
theorem R1259711 : Reach 1259711 := rs (se 1 (by rfl) ⟨944783, by rfl⟩) R1889567
theorem R3291677 : Reach 3291677 := rs (se 3 (by rfl) ⟨617189, by rfl⟩) R1234379
theorem R80743 : Reach 80743 := rs (se 1 (by rfl) ⟨60557, by rfl⟩) R121115
theorem R244943 : Reach 244943 := rs (se 1 (by rfl) ⟨183707, by rfl⟩) R367415
theorem R277931 : Reach 277931 := rs (se 1 (by rfl) ⟨208448, by rfl⟩) R416897
theorem R81391 : Reach 81391 := rs (se 1 (by rfl) ⟨61043, by rfl⟩) R122087
theorem R409151 : Reach 409151 := rs (se 1 (by rfl) ⟨306863, by rfl⟩) R613727
theorem R2670191 : Reach 2670191 := rs (se 1 (by rfl) ⟨2002643, by rfl⟩) R4005287
theorem R245663 : Reach 245663 := rs (se 1 (by rfl) ⟨184247, by rfl⟩) R368495
theorem R180215 : Reach 180215 := rs (se 1 (by rfl) ⟨135161, by rfl⟩) R270323
theorem R278599 : Reach 278599 := rs (se 1 (by rfl) ⟨208949, by rfl⟩) R417899
theorem R377135 : Reach 377135 := rs (se 1 (by rfl) ⟨282851, by rfl⟩) R565703
theorem R541403 : Reach 541403 := rs (se 1 (by rfl) ⟨406052, by rfl⟩) R812105
theorem R967625 : Reach 967625 := rs (se 2 (by rfl) ⟨362859, by rfl⟩) R725719
theorem R83047 : Reach 83047 := rs (se 1 (by rfl) ⟨62285, by rfl⟩) R124571
theorem R2245913 : Reach 2245913 := rs (se 2 (by rfl) ⟨842217, by rfl⟩) R1684435
theorem R312605 : Reach 312605 := rs (se 3 (by rfl) ⟨58613, by rfl⟩) R117227
theorem R83695 : Reach 83695 := rs (se 1 (by rfl) ⟨62771, by rfl⟩) R125543
theorem R182159 : Reach 182159 := rs (se 1 (by rfl) ⟨136619, by rfl⟩) R273239
theorem R280543 : Reach 280543 := rs (se 1 (by rfl) ⟨210407, by rfl⟩) R420815
theorem R641681 : Reach 641681 := rs (se 2 (by rfl) ⟨240630, by rfl⟩) R481261
theorem R609353 : Reach 609353 := rs (se 2 (by rfl) ⟨228507, by rfl⟩) R457015
theorem R1166663 : Reach 1166663 := rs (se 1 (by rfl) ⟨874997, by rfl⟩) R1749995
theorem R1560323 : Reach 1560323 := rs (se 1 (by rfl) ⟨1170242, by rfl⟩) R2340485
theorem R115953443 : Reach 115953443 := rs (se 1 (by rfl) ⟨86965082, by rfl⟩) R173930165
theorem R3920075 : Reach 3920075 := rs (se 1 (by rfl) ⟨2940056, by rfl⟩) R5880113
theorem R283247 : Reach 283247 := rs (se 1 (by rfl) ⟨212435, by rfl⟩) R424871
theorem R905863 : Reach 905863 := rs (se 1 (by rfl) ⟨679397, by rfl⟩) R1358795
theorem R283513 : Reach 283513 := rs (se 2 (by rfl) ⟨106317, by rfl⟩) R212635
theorem R185449 : Reach 185449 := rs (se 2 (by rfl) ⟨69543, by rfl⟩) R139087
theorem R546383 : Reach 546383 := rs (se 1 (by rfl) ⟨409787, by rfl⟩) R819575
theorem R153193 : Reach 153193 := rs (se 2 (by rfl) ⟨57447, by rfl⟩) R114895
theorem R121243 : Reach 121243 := rs (se 1 (by rfl) ⟨90932, by rfl⟩) R181865
theorem R186887 : Reach 186887 := rs (se 1 (by rfl) ⟨140165, by rfl⟩) R280331
theorem R121385 : Reach 121385 := rs (se 2 (by rfl) ⟨45519, by rfl⟩) R91039
theorem R4119113 : Reach 4119113 := rs (se 2 (by rfl) ⟨1544667, by rfl⟩) R3089335
theorem R1137617 : Reach 1137617 := rs (se 2 (by rfl) ⟨426606, by rfl⟩) R853213
theorem R253367 : Reach 253367 := rs (se 1 (by rfl) ⟨190025, by rfl⟩) R380051
theorem R155243 : Reach 155243 := rs (se 1 (by rfl) ⟨116432, by rfl⟩) R232865
theorem R319439 : Reach 319439 := rs (se 1 (by rfl) ⟨239579, by rfl⟩) R479159
theorem R123295 : Reach 123295 := rs (se 1 (by rfl) ⟨92471, by rfl⟩) R184943
theorem R1794797 : Reach 1794797 := rs (se 3 (by rfl) ⟨336524, by rfl⟩) R673049
theorem R418607 : Reach 418607 := rs (se 1 (by rfl) ⟨313955, by rfl⟩) R627911
theorem R124139 : Reach 124139 := rs (se 1 (by rfl) ⟨93104, by rfl⟩) R186209
theorem R189935 : Reach 189935 := rs (se 1 (by rfl) ⟨142451, by rfl⟩) R284903
theorem R550583 : Reach 550583 := rs (se 1 (by rfl) ⟨412937, by rfl⟩) R825875
theorem R616187 : Reach 616187 := rs (se 1 (by rfl) ⟨462140, by rfl⟩) R924281
theorem R714739 : Reach 714739 := rs (se 1 (by rfl) ⟨536054, by rfl⟩) R1072109
theorem R126299 : Reach 126299 := rs (se 1 (by rfl) ⟨94724, by rfl⟩) R189449
theorem R2485633 : Reach 2485633 := rs (se 2 (by rfl) ⟨932112, by rfl⟩) R1864225
theorem R93631 : Reach 93631 := rs (se 1 (by rfl) ⟨70223, by rfl⟩) R140447
theorem R1207943 : Reach 1207943 := rs (se 1 (by rfl) ⟨905957, by rfl⟩) R1811915
theorem R880951 : Reach 880951 := rs (se 1 (by rfl) ⟨660713, by rfl⟩) R1321427
theorem R1406105 : Reach 1406105 := rs (se 2 (by rfl) ⟨527289, by rfl⟩) R1054579
theorem R292193 : Reach 292193 := rs (se 2 (by rfl) ⟨109572, by rfl⟩) R219145
theorem R161279 : Reach 161279 := rs (se 1 (by rfl) ⟨120959, by rfl⟩) R241919
theorem R128575 : Reach 128575 := rs (se 1 (by rfl) ⟨96431, by rfl⟩) R192863
theorem R5306107 : Reach 5306107 := rs (se 1 (by rfl) ⟨3979580, by rfl⟩) R7959161
theorem R522215 : Reach 522215 := rs (se 1 (by rfl) ⟨391661, by rfl⟩) R783323
theorem R129055 : Reach 129055 := rs (se 1 (by rfl) ⟨96791, by rfl⟩) R193583
theorem R522449 : Reach 522449 := rs (se 2 (by rfl) ⟨195918, by rfl⟩) R391837
theorem R162809 : Reach 162809 := rs (se 2 (by rfl) ⟨61053, by rfl⟩) R122107
theorem R229225 : Reach 229225 := rs (se 2 (by rfl) ⟨85959, by rfl⟩) R171919
theorem R622475 : Reach 622475 := rs (se 1 (by rfl) ⟨466856, by rfl⟩) R933713
theorem R622525 : Reach 622525 := rs (se 3 (by rfl) ⟨116723, by rfl⟩) R233447
theorem R163817 : Reach 163817 := rs (se 2 (by rfl) ⟨61431, by rfl⟩) R122863
theorem R163835 : Reach 163835 := rs (se 1 (by rfl) ⟨122876, by rfl⟩) R245753
theorem R360935 : Reach 360935 := rs (se 1 (by rfl) ⟨270701, by rfl⟩) R541403
theorem R164393 : Reach 164393 := rs (se 2 (by rfl) ⟨61647, by rfl⟩) R123295
theorem R754721 : Reach 754721 := rs (se 2 (by rfl) ⟨283020, by rfl⟩) R566041
theorem R427787 : Reach 427787 := rs (se 1 (by rfl) ⟨320840, by rfl⟩) R641681
theorem R77302295 : Reach 77302295 := rs (se 1 (by rfl) ⟨57976721, by rfl⟩) R115953443
theorem R952985 : Reach 952985 := rs (se 2 (by rfl) ⟨357369, by rfl⟩) R714739
theorem R364013 : Reach 364013 := rs (se 3 (by rfl) ⟨68252, by rfl⟩) R136505
theorem R3314177 : Reach 3314177 := rs (se 2 (by rfl) ⟨1242816, by rfl⟩) R2485633
theorem R758411 : Reach 758411 := rs (se 1 (by rfl) ⟨568808, by rfl⟩) R1137617
theorem R168911 : Reach 168911 := rs (se 1 (by rfl) ⟨126683, by rfl⟩) R253367
theorem R136703 : Reach 136703 := rs (se 1 (by rfl) ⟨102527, by rfl⟩) R205055
theorem R71919 : Reach 71919 := rs (se 1 (by rfl) ⟨53939, by rfl⟩) R107879
theorem R367055 : Reach 367055 := rs (se 1 (by rfl) ⟨275291, by rfl⟩) R550583
theorem R203255 : Reach 203255 := rs (se 1 (by rfl) ⟨152441, by rfl⟩) R304883
theorem R72431 : Reach 72431 := rs (se 1 (by rfl) ⟨54323, by rfl⟩) R108647
theorem R72731 : Reach 72731 := rs (se 1 (by rfl) ⟨54548, by rfl⟩) R109097
theorem R138343 : Reach 138343 := rs (se 1 (by rfl) ⟨103757, by rfl⟩) R207515
theorem R367901 : Reach 367901 := rs (se 3 (by rfl) ⟨68981, by rfl⟩) R137963
theorem R269675 : Reach 269675 := rs (se 1 (by rfl) ⟨202256, by rfl⟩) R404513
theorem R73119 : Reach 73119 := rs (se 1 (by rfl) ⟨54839, by rfl⟩) R109679
theorem R171433 : Reach 171433 := rs (se 2 (by rfl) ⟨64287, by rfl⟩) R128575
theorem R204257 : Reach 204257 := rs (se 2 (by rfl) ⟨76596, by rfl⟩) R153193
theorem R73243 : Reach 73243 := rs (se 1 (by rfl) ⟨54932, by rfl⟩) R109865
theorem R172073 : Reach 172073 := rs (se 2 (by rfl) ⟨64527, by rfl⟩) R129055
theorem R74011 : Reach 74011 := rs (se 1 (by rfl) ⟨55508, by rfl⟩) R111017
theorem R74047 : Reach 74047 := rs (se 1 (by rfl) ⟨55535, by rfl⟩) R111071
theorem R74143 : Reach 74143 := rs (se 1 (by rfl) ⟨55607, by rfl⟩) R111215
theorem R74215 : Reach 74215 := rs (se 1 (by rfl) ⟨55661, by rfl⟩) R111323
theorem R74223 : Reach 74223 := rs (se 1 (by rfl) ⟨55667, by rfl⟩) R111335
theorem R467471 : Reach 467471 := rs (se 1 (by rfl) ⟨350603, by rfl⟩) R701207
theorem R107519 : Reach 107519 := rs (se 1 (by rfl) ⟨80639, by rfl⟩) R161279
theorem R107657 : Reach 107657 := rs (se 2 (by rfl) ⟨40371, by rfl⟩) R80743
theorem R74983 : Reach 74983 := rs (se 1 (by rfl) ⟨56237, by rfl⟩) R112475
theorem R140591 : Reach 140591 := rs (se 1 (by rfl) ⟨105443, by rfl⟩) R210887
theorem R665225 : Reach 665225 := rs (se 2 (by rfl) ⟨249459, by rfl⟩) R498919
theorem R108521 : Reach 108521 := rs (se 2 (by rfl) ⟨40695, by rfl⟩) R81391
theorem R108539 : Reach 108539 := rs (se 1 (by rfl) ⟨81404, by rfl⟩) R162809
theorem R272767 : Reach 272767 := rs (se 1 (by rfl) ⟨204575, by rfl⟩) R409151
theorem R1780127 : Reach 1780127 := rs (se 1 (by rfl) ⟨1335095, by rfl⟩) R2670191
theorem R305633 : Reach 305633 := rs (se 2 (by rfl) ⟨114612, by rfl⟩) R229225
theorem R830033 : Reach 830033 := rs (se 2 (by rfl) ⟨311262, by rfl⟩) R622525
theorem R109211 : Reach 109211 := rs (se 1 (by rfl) ⟨81908, by rfl⟩) R163817
theorem R109223 : Reach 109223 := rs (se 1 (by rfl) ⟨81917, by rfl⟩) R163835
theorem R371465 : Reach 371465 := rs (se 2 (by rfl) ⟨139299, by rfl⟩) R278599
theorem R208403 : Reach 208403 := rs (se 1 (by rfl) ⟨156302, by rfl⟩) R312605
theorem R110687 : Reach 110687 := rs (se 1 (by rfl) ⟨83015, by rfl⟩) R166031
theorem R110729 : Reach 110729 := rs (se 2 (by rfl) ⟨41523, by rfl⟩) R83047
theorem R110759 : Reach 110759 := rs (se 1 (by rfl) ⟨83069, by rfl⟩) R166139
theorem R110927 : Reach 110927 := rs (se 1 (by rfl) ⟨83195, by rfl⟩) R166391
theorem R406235 : Reach 406235 := rs (se 1 (by rfl) ⟨304676, by rfl⟩) R609353
theorem R111593 : Reach 111593 := rs (se 2 (by rfl) ⟨41847, by rfl⟩) R83695
theorem R111839 : Reach 111839 := rs (se 1 (by rfl) ⟨83879, by rfl⟩) R167759
theorem R374057 : Reach 374057 := rs (se 2 (by rfl) ⟨140271, by rfl⟩) R280543
theorem R112079 : Reach 112079 := rs (se 1 (by rfl) ⟨84059, by rfl⟩) R168119
theorem R112127 : Reach 112127 := rs (se 1 (by rfl) ⟨84095, by rfl⟩) R168191
theorem R112319 : Reach 112319 := rs (se 1 (by rfl) ⟨84239, by rfl⟩) R168479
theorem R1587761 : Reach 1587761 := rs (se 2 (by rfl) ⟨595410, by rfl⟩) R1190821
theorem R244295 : Reach 244295 := rs (se 1 (by rfl) ⟨183221, by rfl⟩) R366443
theorem R1457021 : Reach 1457021 := rs (se 3 (by rfl) ⟨273191, by rfl⟩) R546383
theorem R179167 : Reach 179167 := rs (se 1 (by rfl) ⟨134375, by rfl⟩) R268751
theorem R80923 : Reach 80923 := rs (se 1 (by rfl) ⟨60692, by rfl⟩) R121385
theorem R277613 : Reach 277613 := rs (se 3 (by rfl) ⟨52052, by rfl⟩) R104105
theorem R212959 : Reach 212959 := rs (se 1 (by rfl) ⟨159719, by rfl⟩) R319439
theorem R246023 : Reach 246023 := rs (se 1 (by rfl) ⟨184517, by rfl⟩) R369035
theorem R1196531 : Reach 1196531 := rs (se 1 (by rfl) ⟨897398, by rfl⟩) R1794797
theorem R279071 : Reach 279071 := rs (se 1 (by rfl) ⟨209303, by rfl⟩) R418607
theorem R82759 : Reach 82759 := rs (se 1 (by rfl) ⟨62069, by rfl⟩) R124139
theorem R181075 : Reach 181075 := rs (se 1 (by rfl) ⟨135806, by rfl⟩) R271613
theorem R378017 : Reach 378017 := rs (se 2 (by rfl) ⟨141756, by rfl⟩) R283513
theorem R410791 : Reach 410791 := rs (se 1 (by rfl) ⟨308093, by rfl⟩) R616187
theorem R378107 : Reach 378107 := rs (se 1 (by rfl) ⟨283580, by rfl⟩) R567161
theorem R247265 : Reach 247265 := rs (se 2 (by rfl) ⟨92724, by rfl⟩) R185449
theorem R280057 : Reach 280057 := rs (se 2 (by rfl) ⟨105021, by rfl⟩) R210043
theorem R247535 : Reach 247535 := rs (se 1 (by rfl) ⟨185651, by rfl⟩) R371303
theorem R84199 : Reach 84199 := rs (se 1 (by rfl) ⟨63149, by rfl⟩) R126299
theorem R805295 : Reach 805295 := rs (se 1 (by rfl) ⟨603971, by rfl⟩) R1207943
theorem R183019 : Reach 183019 := rs (se 1 (by rfl) ⟨137264, by rfl⟩) R274529
theorem R281501 : Reach 281501 := rs (se 3 (by rfl) ⟨52781, by rfl⟩) R105563
theorem R937403 : Reach 937403 := rs (se 1 (by rfl) ⟨703052, by rfl⟩) R1406105
theorem R348143 : Reach 348143 := rs (se 1 (by rfl) ⟨261107, by rfl⟩) R522215
theorem R839807 : Reach 839807 := rs (se 1 (by rfl) ⟨629855, by rfl⟩) R1259711
theorem R348299 : Reach 348299 := rs (se 1 (by rfl) ⟨261224, by rfl⟩) R522449
theorem R413981 : Reach 413981 := rs (se 3 (by rfl) ⟨77621, by rfl⟩) R155243
theorem R185287 : Reach 185287 := rs (se 1 (by rfl) ⟨138965, by rfl⟩) R277931
theorem R414983 : Reach 414983 := rs (se 1 (by rfl) ⟨311237, by rfl⟩) R622475
theorem R120143 : Reach 120143 := rs (se 1 (by rfl) ⟨90107, by rfl⟩) R180215
theorem R153083 : Reach 153083 := rs (se 1 (by rfl) ⟨114812, by rfl⟩) R229625
theorem R251423 : Reach 251423 := rs (se 1 (by rfl) ⟨188567, by rfl⟩) R377135
theorem R284251 : Reach 284251 := rs (se 1 (by rfl) ⟨213188, by rfl⟩) R426377
theorem R645083 : Reach 645083 := rs (se 1 (by rfl) ⟨483812, by rfl⟩) R967625
theorem R1497275 : Reach 1497275 := rs (se 1 (by rfl) ⟨1122956, by rfl⟩) R2245913
theorem R481751 : Reach 481751 := rs (se 1 (by rfl) ⟨361313, by rfl⟩) R722627
theorem R121439 : Reach 121439 := rs (se 1 (by rfl) ⟨91079, by rfl⟩) R182159
theorem R777775 : Reach 777775 := rs (se 1 (by rfl) ⟨583331, by rfl⟩) R1166663
theorem R1040215 : Reach 1040215 := rs (se 1 (by rfl) ⟨780161, by rfl⟩) R1560323
theorem R2613383 : Reach 2613383 := rs (se 1 (by rfl) ⟨1960037, by rfl⟩) R3920075
theorem R418127 : Reach 418127 := rs (se 1 (by rfl) ⟨313595, by rfl⟩) R627191
theorem R188831 : Reach 188831 := rs (se 1 (by rfl) ⟨141623, by rfl⟩) R283247
theorem R418355 : Reach 418355 := rs (se 1 (by rfl) ⟨313766, by rfl⟩) R627533
theorem R91631 : Reach 91631 := rs (se 1 (by rfl) ⟨68723, by rfl⟩) R137447
theorem R124591 : Reach 124591 := rs (se 1 (by rfl) ⟨93443, by rfl⟩) R186887
theorem R2746075 : Reach 2746075 := rs (se 1 (by rfl) ⟨2059556, by rfl⟩) R4119113
theorem R124841 : Reach 124841 := rs (se 2 (by rfl) ⟨46815, by rfl⟩) R93631
theorem R92335 : Reach 92335 := rs (se 1 (by rfl) ⟨69251, by rfl⟩) R138503
theorem R1174601 : Reach 1174601 := rs (se 2 (by rfl) ⟨440475, by rfl⟩) R880951
theorem R1207817 : Reach 1207817 := rs (se 2 (by rfl) ⟨452931, by rfl⟩) R905863
theorem R126623 : Reach 126623 := rs (se 1 (by rfl) ⟨94967, by rfl⟩) R189935
theorem R553067 : Reach 553067 := rs (se 1 (by rfl) ⟨414800, by rfl⟩) R829601
theorem R356987 : Reach 356987 := rs (se 1 (by rfl) ⟨267740, by rfl⟩) R535481
theorem R619163 : Reach 619163 := rs (se 1 (by rfl) ⟨464372, by rfl⟩) R928745
theorem R160703 : Reach 160703 := rs (se 1 (by rfl) ⟨120527, by rfl⟩) R241055
theorem R7074809 : Reach 7074809 := rs (se 2 (by rfl) ⟨2653053, by rfl⟩) R5306107
theorem R161207 : Reach 161207 := rs (se 1 (by rfl) ⟨120905, by rfl⟩) R241811
theorem R358121 : Reach 358121 := rs (se 2 (by rfl) ⟨134295, by rfl⟩) R268591
theorem R161657 : Reach 161657 := rs (se 2 (by rfl) ⟨60621, by rfl⟩) R121243
theorem R161999 : Reach 161999 := rs (se 1 (by rfl) ⟨121499, by rfl⟩) R242999
theorem R194795 : Reach 194795 := rs (se 1 (by rfl) ⟨146096, by rfl⟩) R292193
theorem R489847 : Reach 489847 := rs (se 1 (by rfl) ⟨367385, by rfl⟩) R734771
theorem R162359 : Reach 162359 := rs (se 1 (by rfl) ⟨121769, by rfl⟩) R243539
theorem R162431 : Reach 162431 := rs (se 1 (by rfl) ⟨121823, by rfl⟩) R243647
theorem R2194451 : Reach 2194451 := rs (se 1 (by rfl) ⟨1645838, by rfl⟩) R3291677
theorem R163295 : Reach 163295 := rs (se 1 (by rfl) ⟨122471, by rfl⟩) R244943
theorem R163775 : Reach 163775 := rs (se 1 (by rfl) ⟨122831, by rfl⟩) R245663
theorem R164015 : Reach 164015 := rs (se 1 (by rfl) ⟨123011, by rfl⟩) R246023
theorem R1115005 : Reach 1115005 := rs (se 3 (by rfl) ⟨209063, by rfl⟩) R418127
theorem R164843 : Reach 164843 := rs (se 1 (by rfl) ⟨123632, by rfl⟩) R247265
theorem R165023 : Reach 165023 := rs (se 1 (by rfl) ⟨123767, by rfl⟩) R247535
theorem R1246589 : Reach 1246589 := rs (se 3 (by rfl) ⟨233735, by rfl⟩) R467471
theorem R166121 : Reach 166121 := rs (se 2 (by rfl) ⟨62295, by rfl⟩) R124591
theorem R624935 : Reach 624935 := rs (se 1 (by rfl) ⟨468701, by rfl⟩) R937403
theorem R395813 : Reach 395813 := rs (se 4 (by rfl) ⟨37107, by rfl⟩) R74215
theorem R559871 : Reach 559871 := rs (se 1 (by rfl) ⟨419903, by rfl⟩) R839807
theorem R232199 : Reach 232199 := rs (se 1 (by rfl) ⟨174149, by rfl⟩) R348299
theorem R363689 : Reach 363689 := rs (se 2 (by rfl) ⟨136383, by rfl⟩) R272767
theorem R102055 : Reach 102055 := rs (se 1 (by rfl) ⟨76541, by rfl⟩) R153083
theorem R167615 : Reach 167615 := rs (se 1 (by rfl) ⟨125711, by rfl⟩) R251423
theorem R430055 : Reach 430055 := rs (se 1 (by rfl) ⟨322541, by rfl⟩) R645083
theorem R135503 : Reach 135503 := rs (se 1 (by rfl) ⟨101627, by rfl⟩) R203255
theorem R954989 : Reach 954989 := rs (se 3 (by rfl) ⟨179060, by rfl⟩) R358121
theorem R136171 : Reach 136171 := rs (se 1 (by rfl) ⟨102128, by rfl⟩) R204257
theorem R1742255 : Reach 1742255 := rs (se 1 (by rfl) ⟨1306691, by rfl⟩) R2613383
theorem R71679 : Reach 71679 := rs (se 1 (by rfl) ⟨53759, by rfl⟩) R107519
theorem R71771 : Reach 71771 := rs (se 1 (by rfl) ⟨53828, by rfl⟩) R107657
theorem R72347 : Reach 72347 := rs (se 1 (by rfl) ⟨54260, by rfl⟩) R108521
theorem R72359 : Reach 72359 := rs (se 1 (by rfl) ⟨54269, by rfl⟩) R108539
theorem R1186751 : Reach 1186751 := rs (se 1 (by rfl) ⟨890063, by rfl⟩) R1780127
theorem R72807 : Reach 72807 := rs (se 1 (by rfl) ⟨54605, by rfl⟩) R109211
theorem R72815 : Reach 72815 := rs (se 1 (by rfl) ⟨54611, by rfl⟩) R109223
theorem R138935 : Reach 138935 := rs (se 1 (by rfl) ⟨104201, by rfl⟩) R208403
theorem R73791 : Reach 73791 := rs (se 1 (by rfl) ⟨55343, by rfl⟩) R110687
theorem R368711 : Reach 368711 := rs (se 1 (by rfl) ⟨276533, by rfl⟩) R553067
theorem R73819 : Reach 73819 := rs (se 1 (by rfl) ⟨55364, by rfl⟩) R110729
theorem R73839 : Reach 73839 := rs (se 1 (by rfl) ⟨55379, by rfl⟩) R110759
theorem R73951 : Reach 73951 := rs (se 1 (by rfl) ⟨55463, by rfl⟩) R110927
theorem R237991 : Reach 237991 := rs (se 1 (by rfl) ⟨178493, by rfl⟩) R356987
theorem R270823 : Reach 270823 := rs (se 1 (by rfl) ⟨203117, by rfl⟩) R406235
theorem R107135 : Reach 107135 := rs (se 1 (by rfl) ⟨80351, by rfl⟩) R160703
theorem R74395 : Reach 74395 := rs (se 1 (by rfl) ⟨55796, by rfl⟩) R111593
theorem R74559 : Reach 74559 := rs (se 1 (by rfl) ⟨55919, by rfl⟩) R111839
theorem R107471 : Reach 107471 := rs (se 1 (by rfl) ⟨80603, by rfl⟩) R161207
theorem R74719 : Reach 74719 := rs (se 1 (by rfl) ⟨56039, by rfl⟩) R112079
theorem R74751 : Reach 74751 := rs (se 1 (by rfl) ⟨56063, by rfl⟩) R112127
theorem R74879 : Reach 74879 := rs (se 1 (by rfl) ⟨56159, by rfl⟩) R112319
theorem R107771 : Reach 107771 := rs (se 1 (by rfl) ⟨80828, by rfl⟩) R161657
theorem R238889 : Reach 238889 := rs (se 2 (by rfl) ⟨89583, by rfl⟩) R179167
theorem R107897 : Reach 107897 := rs (se 2 (by rfl) ⟨40461, by rfl⟩) R80923
theorem R107999 : Reach 107999 := rs (se 1 (by rfl) ⟨80999, by rfl⟩) R161999
theorem R1058507 : Reach 1058507 := rs (se 1 (by rfl) ⟨793880, by rfl⟩) R1587761
theorem R108239 : Reach 108239 := rs (se 1 (by rfl) ⟨81179, by rfl⟩) R162359
theorem R108287 : Reach 108287 := rs (se 1 (by rfl) ⟨81215, by rfl⟩) R162431
theorem R108863 : Reach 108863 := rs (se 1 (by rfl) ⟨81647, by rfl⟩) R163295
theorem R1386953 : Reach 1386953 := rs (se 2 (by rfl) ⟨520107, by rfl⟩) R1040215
theorem R928381 : Reach 928381 := rs (se 3 (by rfl) ⟨174071, by rfl⟩) R348143
theorem R109183 : Reach 109183 := rs (se 1 (by rfl) ⟨81887, by rfl⟩) R163775
theorem R240623 : Reach 240623 := rs (se 1 (by rfl) ⟨180467, by rfl⟩) R360935
theorem R797687 : Reach 797687 := rs (se 1 (by rfl) ⟨598265, by rfl⟩) R1196531
theorem R109595 : Reach 109595 := rs (se 1 (by rfl) ⟨82196, by rfl⟩) R164393
theorem R503147 : Reach 503147 := rs (se 1 (by rfl) ⟨377360, by rfl⟩) R754721
theorem R110345 : Reach 110345 := rs (se 2 (by rfl) ⟨41379, by rfl⟩) R82759
theorem R241433 : Reach 241433 := rs (se 2 (by rfl) ⟨90537, by rfl⟩) R181075
theorem R536863 : Reach 536863 := rs (se 1 (by rfl) ⟨402647, by rfl⟩) R805295
theorem R635323 : Reach 635323 := rs (se 1 (by rfl) ⟨476492, by rfl⟩) R952985
theorem R373409 : Reach 373409 := rs (se 2 (by rfl) ⟨140028, by rfl⟩) R280057
theorem R242675 : Reach 242675 := rs (se 1 (by rfl) ⟨182006, by rfl⟩) R364013
theorem R275987 : Reach 275987 := rs (se 1 (by rfl) ⟨206990, by rfl⟩) R413981
theorem R112265 : Reach 112265 := rs (se 2 (by rfl) ⟨42099, by rfl⟩) R84199
theorem R2209451 : Reach 2209451 := rs (se 1 (by rfl) ⟨1657088, by rfl⟩) R3314177
theorem R505607 : Reach 505607 := rs (se 1 (by rfl) ⟨379205, by rfl⟩) R758411
theorem R112607 : Reach 112607 := rs (se 1 (by rfl) ⟨84455, by rfl⟩) R168911
theorem R276655 : Reach 276655 := rs (se 1 (by rfl) ⟨207491, by rfl⟩) R414983
theorem R80095 : Reach 80095 := rs (se 1 (by rfl) ⟨60071, by rfl⟩) R120143
theorem R244025 : Reach 244025 := rs (se 2 (by rfl) ⟨91509, by rfl⟩) R183019
theorem R244349 : Reach 244349 := rs (se 3 (by rfl) ⟨45815, by rfl⟩) R91631
theorem R998183 : Reach 998183 := rs (se 1 (by rfl) ⟨748637, by rfl⟩) R1497275
theorem R244703 : Reach 244703 := rs (se 1 (by rfl) ⟨183527, by rfl⟩) R367055
theorem R80959 : Reach 80959 := rs (se 1 (by rfl) ⟨60719, by rfl⟩) R121439
theorem R245267 : Reach 245267 := rs (se 1 (by rfl) ⟨183950, by rfl⟩) R367901
theorem R179783 : Reach 179783 := rs (se 1 (by rfl) ⟨134837, by rfl⟩) R269675
theorem R114715 : Reach 114715 := rs (se 1 (by rfl) ⟨86036, by rfl⟩) R172073
theorem R278903 : Reach 278903 := rs (se 1 (by rfl) ⟨209177, by rfl⟩) R418355
theorem R443483 : Reach 443483 := rs (se 1 (by rfl) ⟨332612, by rfl⟩) R665225
theorem R247049 : Reach 247049 := rs (se 2 (by rfl) ⟨92643, by rfl⟩) R185287
theorem R83227 : Reach 83227 := rs (se 1 (by rfl) ⟨62420, by rfl⟩) R124841
theorem R247643 : Reach 247643 := rs (se 1 (by rfl) ⟨185732, by rfl⟩) R371465
theorem R379001 : Reach 379001 := rs (se 2 (by rfl) ⟨142125, by rfl⟩) R284251
theorem R805211 : Reach 805211 := rs (se 1 (by rfl) ⟨603908, by rfl⟩) R1207817
theorem R84415 : Reach 84415 := rs (se 1 (by rfl) ⟨63311, by rfl⟩) R126623
theorem R412775 : Reach 412775 := rs (se 1 (by rfl) ⟨309581, by rfl⟩) R619163
theorem R249371 : Reach 249371 := rs (se 1 (by rfl) ⟨187028, by rfl⟩) R374057
theorem R184457 : Reach 184457 := rs (se 2 (by rfl) ⟨69171, by rfl⟩) R138343
theorem R971347 : Reach 971347 := rs (se 1 (by rfl) ⟨728510, by rfl⟩) R1457021
theorem R1462967 : Reach 1462967 := rs (se 1 (by rfl) ⟨1097225, by rfl⟩) R2194451
theorem R1037033 : Reach 1037033 := rs (se 2 (by rfl) ⟨388887, by rfl⟩) R777775
theorem R185075 : Reach 185075 := rs (se 1 (by rfl) ⟨138806, by rfl⟩) R277613
theorem R283945 : Reach 283945 := rs (se 2 (by rfl) ⟨106479, by rfl⟩) R212959
theorem R186047 : Reach 186047 := rs (se 1 (by rfl) ⟨139535, by rfl⟩) R279071
theorem R252011 : Reach 252011 := rs (se 1 (by rfl) ⟨189008, by rfl⟩) R378017
theorem R252071 : Reach 252071 := rs (se 1 (by rfl) ⟨189053, by rfl⟩) R378107
theorem R285191 : Reach 285191 := rs (se 1 (by rfl) ⟨213893, by rfl⟩) R427787
theorem R547721 : Reach 547721 := rs (se 2 (by rfl) ⟨205395, by rfl⟩) R410791
theorem R51534863 : Reach 51534863 := rs (se 1 (by rfl) ⟨38651147, by rfl⟩) R77302295
theorem R187667 : Reach 187667 := rs (se 1 (by rfl) ⟨140750, by rfl⟩) R281501
theorem R3661433 : Reach 3661433 := rs (se 2 (by rfl) ⟨1373037, by rfl⟩) R2746075
theorem R123113 : Reach 123113 := rs (se 2 (by rfl) ⟨46167, by rfl⟩) R92335
theorem R320381 : Reach 320381 := rs (se 3 (by rfl) ⟨60071, by rfl⟩) R120143
theorem R91135 : Reach 91135 := rs (se 1 (by rfl) ⟨68351, by rfl⟩) R136703
theorem R321167 : Reach 321167 := rs (se 1 (by rfl) ⟨240875, by rfl⟩) R481751
theorem R125887 : Reach 125887 := rs (se 1 (by rfl) ⟨94415, by rfl⟩) R188831
theorem R93727 : Reach 93727 := rs (se 1 (by rfl) ⟨70295, by rfl⟩) R140591
theorem R815021 : Reach 815021 := rs (se 3 (by rfl) ⟨152816, by rfl⟩) R305633
theorem R553355 : Reach 553355 := rs (se 1 (by rfl) ⟨415016, by rfl⟩) R830033
theorem R783067 : Reach 783067 := rs (se 1 (by rfl) ⟨587300, by rfl⟩) R1174601
theorem R653129 : Reach 653129 := rs (se 2 (by rfl) ⟨244923, by rfl⟩) R489847
theorem R4716539 : Reach 4716539 := rs (se 1 (by rfl) ⟨3537404, by rfl⟩) R7074809
theorem R129863 : Reach 129863 := rs (se 1 (by rfl) ⟨97397, by rfl⟩) R194795
theorem R162863 : Reach 162863 := rs (se 1 (by rfl) ⟨122147, by rfl⟩) R244295
theorem R228577 : Reach 228577 := rs (se 2 (by rfl) ⟨85716, by rfl⟩) R171433
theorem R361097 : Reach 361097 := rs (se 2 (by rfl) ⟨135411, by rfl⟩) R270823
theorem R295655 : Reach 295655 := rs (se 1 (by rfl) ⟨221741, by rfl⟩) R443483
theorem R164699 : Reach 164699 := rs (se 1 (by rfl) ⟨123524, by rfl⟩) R247049
theorem R165095 : Reach 165095 := rs (se 1 (by rfl) ⟨123821, by rfl⟩) R247643
theorem R99625 : Reach 99625 := rs (se 2 (by rfl) ⟨37359, by rfl⟩) R74719
theorem R166247 : Reach 166247 := rs (se 1 (by rfl) ⟨124685, by rfl⟩) R249371
theorem R691355 : Reach 691355 := rs (se 1 (by rfl) ⟨518516, by rfl⟩) R1037033
theorem R167849 : Reach 167849 := rs (se 2 (by rfl) ⟨62943, by rfl⟩) R125887
theorem R168007 : Reach 168007 := rs (se 1 (by rfl) ⟨126005, by rfl⟩) R252011
theorem R168047 : Reach 168047 := rs (se 1 (by rfl) ⟨126035, by rfl⟩) R252071
theorem R365147 : Reach 365147 := rs (se 1 (by rfl) ⟨273860, by rfl⟩) R547721
theorem R791167 : Reach 791167 := rs (se 1 (by rfl) ⟨593375, by rfl⟩) R1186751
theorem R136073 : Reach 136073 := rs (se 2 (by rfl) ⟨51027, by rfl⟩) R102055
theorem R71423 : Reach 71423 := rs (se 1 (by rfl) ⟨53567, by rfl⟩) R107135
theorem R71647 : Reach 71647 := rs (se 1 (by rfl) ⟨53735, by rfl⟩) R107471
theorem R71847 : Reach 71847 := rs (se 1 (by rfl) ⟨53885, by rfl⟩) R107771
theorem R71931 : Reach 71931 := rs (se 1 (by rfl) ⟨53948, by rfl⟩) R107897
theorem R71999 : Reach 71999 := rs (se 1 (by rfl) ⟨53999, by rfl⟩) R107999
theorem R72159 : Reach 72159 := rs (se 1 (by rfl) ⟨54119, by rfl⟩) R108239
theorem R72191 : Reach 72191 := rs (se 1 (by rfl) ⟨54143, by rfl⟩) R108287
theorem R1055501 : Reach 1055501 := rs (se 3 (by rfl) ⟨197906, by rfl⟩) R395813
theorem R72575 : Reach 72575 := rs (se 1 (by rfl) ⟨54431, by rfl⟩) R108863
theorem R924635 : Reach 924635 := rs (se 1 (by rfl) ⟨693476, by rfl⟩) R1386953
theorem R531791 : Reach 531791 := rs (se 1 (by rfl) ⟨398843, by rfl⟩) R797687
theorem R73063 : Reach 73063 := rs (se 1 (by rfl) ⟨54797, by rfl⟩) R109595
theorem R2661821 : Reach 2661821 := rs (se 3 (by rfl) ⟨499091, by rfl⟩) R998183
theorem R335431 : Reach 335431 := rs (se 1 (by rfl) ⟨251573, by rfl⟩) R503147
theorem R73563 : Reach 73563 := rs (se 1 (by rfl) ⟨55172, by rfl⟩) R110345
theorem R368873 : Reach 368873 := rs (se 2 (by rfl) ⟨138327, by rfl⟩) R276655
theorem R368903 : Reach 368903 := rs (se 1 (by rfl) ⟨276677, by rfl⟩) R553355
theorem R106793 : Reach 106793 := rs (se 2 (by rfl) ⟨40047, by rfl⟩) R80095
theorem R74843 : Reach 74843 := rs (se 1 (by rfl) ⟨56132, by rfl⟩) R112265
theorem R435419 : Reach 435419 := rs (se 1 (by rfl) ⟨326564, by rfl⟩) R653129
theorem R75071 : Reach 75071 := rs (se 1 (by rfl) ⟨56303, by rfl⟩) R112607
theorem R107945 : Reach 107945 := rs (se 2 (by rfl) ⟨40479, by rfl⟩) R80959
theorem R304769 : Reach 304769 := rs (se 2 (by rfl) ⟨114288, by rfl⟩) R228577
theorem R370493 : Reach 370493 := rs (se 3 (by rfl) ⟨69467, by rfl⟩) R138935
theorem R108575 : Reach 108575 := rs (se 1 (by rfl) ⟨81431, by rfl⟩) R162863
theorem R109343 : Reach 109343 := rs (se 1 (by rfl) ⟨82007, by rfl⟩) R164015
theorem R109895 : Reach 109895 := rs (se 1 (by rfl) ⟨82421, by rfl⟩) R164843
theorem R110015 : Reach 110015 := rs (se 1 (by rfl) ⟨82511, by rfl⟩) R165023
theorem R831059 : Reach 831059 := rs (se 1 (by rfl) ⟨623294, by rfl⟩) R1246589
theorem R1486673 : Reach 1486673 := rs (se 2 (by rfl) ⟨557502, by rfl⟩) R1115005
theorem R110747 : Reach 110747 := rs (se 1 (by rfl) ⟨83060, by rfl⟩) R166121
theorem R536807 : Reach 536807 := rs (se 1 (by rfl) ⟨402605, by rfl⟩) R805211
theorem R110969 : Reach 110969 := rs (se 2 (by rfl) ⟨41613, by rfl⟩) R83227
theorem R373247 : Reach 373247 := rs (se 1 (by rfl) ⟨279935, by rfl⟩) R559871
theorem R275183 : Reach 275183 := rs (se 1 (by rfl) ⟨206387, by rfl⟩) R412775
theorem R242459 : Reach 242459 := rs (se 1 (by rfl) ⟨181844, by rfl⟩) R363689
theorem R111743 : Reach 111743 := rs (se 1 (by rfl) ⟨83807, by rfl⟩) R167615
theorem R636659 : Reach 636659 := rs (se 1 (by rfl) ⟨477494, by rfl⟩) R954989
theorem R112553 : Reach 112553 := rs (se 2 (by rfl) ⟨42207, by rfl⟩) R84415
theorem R145577 : Reach 145577 := rs (se 2 (by rfl) ⟨54591, by rfl⟩) R109183
theorem R1161503 : Reach 1161503 := rs (se 1 (by rfl) ⟨871127, by rfl⟩) R1742255
theorem R34356575 : Reach 34356575 := rs (se 1 (by rfl) ⟨25767431, by rfl⟩) R51534863
theorem R2440955 : Reach 2440955 := rs (se 1 (by rfl) ⟨1830716, by rfl⟩) R3661433
theorem R245807 : Reach 245807 := rs (se 1 (by rfl) ⟨184355, by rfl⟩) R368711
theorem R82075 : Reach 82075 := rs (se 1 (by rfl) ⟨61556, by rfl⟩) R123113
theorem R213587 : Reach 213587 := rs (se 1 (by rfl) ⟨160190, by rfl⟩) R320381
theorem R1295129 : Reach 1295129 := rs (se 2 (by rfl) ⟨485673, by rfl⟩) R971347
theorem R214111 : Reach 214111 := rs (se 1 (by rfl) ⟨160583, by rfl⟩) R321167
theorem R705671 : Reach 705671 := rs (se 1 (by rfl) ⟨529253, by rfl⟩) R1058507
theorem R181561 : Reach 181561 := rs (se 2 (by rfl) ⟨68085, by rfl⟩) R136171
theorem R378593 : Reach 378593 := rs (se 2 (by rfl) ⟨141972, by rfl⟩) R283945
theorem R543347 : Reach 543347 := rs (se 1 (by rfl) ⟨407510, by rfl⟩) R815021
theorem R5393141 : Reach 5393141 := rs (se 5 (by rfl) ⟨252803, by rfl⟩) R505607
theorem R248939 : Reach 248939 := rs (se 1 (by rfl) ⟨186704, by rfl⟩) R373409
theorem R183991 : Reach 183991 := rs (se 1 (by rfl) ⟨137993, by rfl⟩) R275987
theorem R86575 : Reach 86575 := rs (se 1 (by rfl) ⟨64931, by rfl⟩) R129863
theorem R119855 : Reach 119855 := rs (se 1 (by rfl) ⟨89891, by rfl⟩) R179783
theorem R611813 : Reach 611813 := rs (se 4 (by rfl) ⟨57357, by rfl⟩) R114715
theorem R185935 : Reach 185935 := rs (se 1 (by rfl) ⟨139451, by rfl⟩) R278903
theorem R317321 : Reach 317321 := rs (se 2 (by rfl) ⟨118995, by rfl⟩) R237991
theorem R121513 : Reach 121513 := rs (se 2 (by rfl) ⟨45567, by rfl⟩) R91135
theorem R252667 : Reach 252667 := rs (se 1 (by rfl) ⟨189500, by rfl⟩) R379001
theorem R416623 : Reach 416623 := rs (se 1 (by rfl) ⟨312467, by rfl⟩) R624935
theorem R154799 : Reach 154799 := rs (se 1 (by rfl) ⟨116099, by rfl⟩) R232199
theorem R286703 : Reach 286703 := rs (se 1 (by rfl) ⟨215027, by rfl⟩) R430055
theorem R122971 : Reach 122971 := rs (se 1 (by rfl) ⟨92228, by rfl⟩) R184457
theorem R90335 : Reach 90335 := rs (se 1 (by rfl) ⟨67751, by rfl⟩) R135503
theorem R975311 : Reach 975311 := rs (se 1 (by rfl) ⟨731483, by rfl⟩) R1462967
theorem R123383 : Reach 123383 := rs (se 1 (by rfl) ⟨92537, by rfl⟩) R185075
theorem R1237841 : Reach 1237841 := rs (se 2 (by rfl) ⟨464190, by rfl⟩) R928381
theorem R124031 : Reach 124031 := rs (se 1 (by rfl) ⟨93023, by rfl⟩) R186047
theorem R190127 : Reach 190127 := rs (se 1 (by rfl) ⟨142595, by rfl⟩) R285191
theorem R5891869 : Reach 5891869 := rs (se 3 (by rfl) ⟨1104725, by rfl⟩) R2209451
theorem R124969 : Reach 124969 := rs (se 2 (by rfl) ⟨46863, by rfl⟩) R93727
theorem R125111 : Reach 125111 := rs (se 1 (by rfl) ⟨93833, by rfl⟩) R187667
theorem R715817 : Reach 715817 := rs (se 2 (by rfl) ⟨268431, by rfl⟩) R536863
theorem R847097 : Reach 847097 := rs (se 2 (by rfl) ⟨317661, by rfl⟩) R635323
theorem R159259 : Reach 159259 := rs (se 1 (by rfl) ⟨119444, by rfl⟩) R238889
theorem R1044089 : Reach 1044089 := rs (se 2 (by rfl) ⟨391533, by rfl⟩) R783067
theorem R160415 : Reach 160415 := rs (se 1 (by rfl) ⟨120311, by rfl⟩) R240623
theorem R160955 : Reach 160955 := rs (se 1 (by rfl) ⟨120716, by rfl⟩) R241433
theorem R161783 : Reach 161783 := rs (se 1 (by rfl) ⟨121337, by rfl⟩) R242675
theorem R3144359 : Reach 3144359 := rs (se 1 (by rfl) ⟨2358269, by rfl⟩) R4716539
theorem R162683 : Reach 162683 := rs (se 1 (by rfl) ⟨122012, by rfl⟩) R244025
theorem R162899 : Reach 162899 := rs (se 1 (by rfl) ⟨122174, by rfl⟩) R244349
theorem R163135 : Reach 163135 := rs (se 1 (by rfl) ⟨122351, by rfl⟩) R244703
theorem R163511 : Reach 163511 := rs (se 1 (by rfl) ⟨122633, by rfl⟩) R245267
theorem R163871 : Reach 163871 := rs (se 1 (by rfl) ⟨122903, by rfl⟩) R245807
theorem R163961 : Reach 163961 := rs (se 2 (by rfl) ⟨61485, by rfl⟩) R122971
theorem R132833 : Reach 132833 := rs (se 2 (by rfl) ⟨49812, by rfl⟩) R99625
theorem R362231 : Reach 362231 := rs (se 1 (by rfl) ⟨271673, by rfl⟩) R543347
theorem R788413 : Reach 788413 := rs (se 3 (by rfl) ⟨147827, by rfl⟩) R295655
theorem R165959 : Reach 165959 := rs (se 1 (by rfl) ⟨124469, by rfl⟩) R248939
theorem R460903 : Reach 460903 := rs (se 1 (by rfl) ⟨345677, by rfl⟩) R691355
theorem R166625 : Reach 166625 := rs (se 2 (by rfl) ⟨62484, by rfl⟩) R124969
theorem R103199 : Reach 103199 := rs (se 1 (by rfl) ⟨77399, by rfl⟩) R154799
theorem R1774547 : Reach 1774547 := rs (se 1 (by rfl) ⟨1330910, by rfl⟩) R2661821
theorem R71195 : Reach 71195 := rs (se 1 (by rfl) ⟨53396, by rfl⟩) R106793
theorem R825227 : Reach 825227 := rs (se 1 (by rfl) ⟨618920, by rfl⟩) R1237841
theorem R1054889 : Reach 1054889 := rs (se 2 (by rfl) ⟨395583, by rfl⟩) R791167
theorem R71963 : Reach 71963 := rs (se 1 (by rfl) ⟨53972, by rfl⟩) R107945
theorem R72383 : Reach 72383 := rs (se 1 (by rfl) ⟨54287, by rfl⟩) R108575
theorem R72895 : Reach 72895 := rs (se 1 (by rfl) ⟨54671, by rfl⟩) R109343
theorem R564731 : Reach 564731 := rs (se 1 (by rfl) ⟨423548, by rfl⟩) R847097
theorem R73263 : Reach 73263 := rs (se 1 (by rfl) ⟨54947, by rfl⟩) R109895
theorem R73343 : Reach 73343 := rs (se 1 (by rfl) ⟨55007, by rfl⟩) R110015
theorem R696059 : Reach 696059 := rs (se 1 (by rfl) ⟨522044, by rfl⟩) R1044089
theorem R991115 : Reach 991115 := rs (se 1 (by rfl) ⟨743336, by rfl⟩) R1486673
theorem R73831 : Reach 73831 := rs (se 1 (by rfl) ⟨55373, by rfl⟩) R110747
theorem R73979 : Reach 73979 := rs (se 1 (by rfl) ⟨55484, by rfl⟩) R110969
theorem R106943 : Reach 106943 := rs (se 1 (by rfl) ⟨80207, by rfl⟩) R160415
theorem R74495 : Reach 74495 := rs (se 1 (by rfl) ⟨55871, by rfl⟩) R111743
theorem R107303 : Reach 107303 := rs (se 1 (by rfl) ⟨80477, by rfl⟩) R160955
theorem R336889 : Reach 336889 := rs (se 2 (by rfl) ⟨126333, by rfl⟩) R252667
theorem R75035 : Reach 75035 := rs (se 1 (by rfl) ⟨56276, by rfl⟩) R112553
theorem R107855 : Reach 107855 := rs (se 1 (by rfl) ⟨80891, by rfl⟩) R161783
theorem R108455 : Reach 108455 := rs (se 1 (by rfl) ⟨81341, by rfl⟩) R162683
theorem R108599 : Reach 108599 := rs (se 1 (by rfl) ⟨81449, by rfl⟩) R162899
theorem R109007 : Reach 109007 := rs (se 1 (by rfl) ⟨81755, by rfl⟩) R163511
theorem R109433 : Reach 109433 := rs (se 2 (by rfl) ⟨41037, by rfl⟩) R82075
theorem R142391 : Reach 142391 := rs (se 1 (by rfl) ⟨106793, by rfl⟩) R213587
theorem R240731 : Reach 240731 := rs (se 1 (by rfl) ⟨180548, by rfl⟩) R361097
theorem R109799 : Reach 109799 := rs (se 1 (by rfl) ⟨82349, by rfl⟩) R164699
theorem R240893 : Reach 240893 := rs (se 3 (by rfl) ⟨45167, by rfl⟩) R90335
theorem R470447 : Reach 470447 := rs (se 1 (by rfl) ⟨352835, by rfl⟩) R705671
theorem R110063 : Reach 110063 := rs (se 1 (by rfl) ⟨82547, by rfl⟩) R165095
theorem R110831 : Reach 110831 := rs (se 1 (by rfl) ⟨83123, by rfl⟩) R166247
theorem R242081 : Reach 242081 := rs (se 2 (by rfl) ⟨90780, by rfl⟩) R181561
theorem R3453677 : Reach 3453677 := rs (se 3 (by rfl) ⟨647564, by rfl⟩) R1295129
theorem R111899 : Reach 111899 := rs (se 1 (by rfl) ⟨83924, by rfl⟩) R167849
theorem R112031 : Reach 112031 := rs (se 1 (by rfl) ⟨84023, by rfl⟩) R168047
theorem R243431 : Reach 243431 := rs (se 1 (by rfl) ⟨182573, by rfl⟩) R365147
theorem R79903 : Reach 79903 := rs (se 1 (by rfl) ⟨59927, by rfl⟩) R119855
theorem R407875 : Reach 407875 := rs (se 1 (by rfl) ⟨305906, by rfl⟩) R611813
theorem R211547 : Reach 211547 := rs (se 1 (by rfl) ⟨158660, by rfl⟩) R317321
theorem R703667 : Reach 703667 := rs (se 1 (by rfl) ⟨527750, by rfl⟩) R1055501
theorem R212345 : Reach 212345 := rs (se 2 (by rfl) ⟨79629, by rfl⟩) R159259
theorem R245321 : Reach 245321 := rs (se 2 (by rfl) ⟨91995, by rfl⟩) R183991
theorem R245915 : Reach 245915 := rs (se 1 (by rfl) ⟨184436, by rfl⟩) R368873
theorem R245935 : Reach 245935 := rs (se 1 (by rfl) ⟨184451, by rfl⟩) R368903
theorem R82255 : Reach 82255 := rs (se 1 (by rfl) ⟨61691, by rfl⟩) R123383
theorem R115433 : Reach 115433 := rs (se 2 (by rfl) ⟨43287, by rfl⟩) R86575
theorem R82687 : Reach 82687 := rs (se 1 (by rfl) ⟨62015, by rfl⟩) R124031
theorem R246995 : Reach 246995 := rs (se 1 (by rfl) ⟨185246, by rfl⟩) R370493
theorem R83407 : Reach 83407 := rs (se 1 (by rfl) ⟨62555, by rfl⟩) R125111
theorem R477211 : Reach 477211 := rs (se 1 (by rfl) ⟨357908, by rfl⟩) R715817
theorem R247913 : Reach 247913 := rs (se 2 (by rfl) ⟨92967, by rfl⟩) R185935
theorem R248831 : Reach 248831 := rs (se 1 (by rfl) ⟨186623, by rfl⟩) R373247
theorem R183455 : Reach 183455 := rs (se 1 (by rfl) ⟨137591, by rfl⟩) R275183
theorem R774335 : Reach 774335 := rs (se 1 (by rfl) ⟨580751, by rfl⟩) R1161503
theorem R217513 : Reach 217513 := rs (se 2 (by rfl) ⟨81567, by rfl⟩) R163135
theorem R447241 : Reach 447241 := rs (se 2 (by rfl) ⟨167715, by rfl⟩) R335431
theorem R1627303 : Reach 1627303 := rs (se 1 (by rfl) ⟨1220477, by rfl⟩) R2440955
theorem R252395 : Reach 252395 := rs (se 1 (by rfl) ⟨189296, by rfl⟩) R378593
theorem R285481 : Reach 285481 := rs (se 2 (by rfl) ⟨107055, by rfl⟩) R214111
theorem R3595427 : Reach 3595427 := rs (se 1 (by rfl) ⟨2696570, by rfl⟩) R5393141
theorem R7855825 : Reach 7855825 := rs (se 2 (by rfl) ⟨2945934, by rfl⟩) R5891869
theorem R90715 : Reach 90715 := rs (se 1 (by rfl) ⟨68036, by rfl⟩) R136073
theorem R812717 : Reach 812717 := rs (se 3 (by rfl) ⟨152384, by rfl⟩) R304769
theorem R616423 : Reach 616423 := rs (se 1 (by rfl) ⟨462317, by rfl⟩) R924635
theorem R354527 : Reach 354527 := rs (se 1 (by rfl) ⟨265895, by rfl⟩) R531791
theorem R191135 : Reach 191135 := rs (se 1 (by rfl) ⟨143351, by rfl⟩) R286703
theorem R224009 : Reach 224009 := rs (se 2 (by rfl) ⟨84003, by rfl⟩) R168007
theorem R650207 : Reach 650207 := rs (se 1 (by rfl) ⟨487655, by rfl⟩) R975311
theorem R290279 : Reach 290279 := rs (se 1 (by rfl) ⟨217709, by rfl⟩) R435419
theorem R126751 : Reach 126751 := rs (se 1 (by rfl) ⟨95063, by rfl⟩) R190127
theorem R554039 : Reach 554039 := rs (se 1 (by rfl) ⟨415529, by rfl⟩) R831059
theorem R357871 : Reach 357871 := rs (se 1 (by rfl) ⟨268403, by rfl⟩) R536807
theorem R161639 : Reach 161639 := rs (se 1 (by rfl) ⟨121229, by rfl⟩) R242459
theorem R162017 : Reach 162017 := rs (se 2 (by rfl) ⟨60756, by rfl⟩) R121513
theorem R555497 : Reach 555497 := rs (se 2 (by rfl) ⟨208311, by rfl⟩) R416623
theorem R424439 : Reach 424439 := rs (se 1 (by rfl) ⟨318329, by rfl⟩) R636659
theorem R97051 : Reach 97051 := rs (se 1 (by rfl) ⟨72788, by rfl⟩) R145577
theorem R2096239 : Reach 2096239 := rs (se 1 (by rfl) ⟨1572179, by rfl⟩) R3144359
theorem R22904383 : Reach 22904383 := rs (se 1 (by rfl) ⟨17178287, by rfl⟩) R34356575
theorem R163943 : Reach 163943 := rs (se 1 (by rfl) ⟨122957, by rfl⟩) R245915
theorem R164663 : Reach 164663 := rs (se 1 (by rfl) ⟨123497, by rfl⟩) R246995
theorem R1311653 : Reach 1311653 := rs (se 4 (by rfl) ⟨122967, by rfl⟩) R245935
theorem R165275 : Reach 165275 := rs (se 1 (by rfl) ⟨123956, by rfl⟩) R247913
theorem R165887 : Reach 165887 := rs (se 1 (by rfl) ⟨124415, by rfl⟩) R248831
theorem R1051217 : Reach 1051217 := rs (se 2 (by rfl) ⟨394206, by rfl⟩) R788413
theorem R821897 : Reach 821897 := rs (se 2 (by rfl) ⟨308211, by rfl⟩) R616423
theorem R1183031 : Reach 1183031 := rs (se 1 (by rfl) ⟨887273, by rfl⟩) R1774547
theorem R168263 : Reach 168263 := rs (se 1 (by rfl) ⟨126197, by rfl⟩) R252395
theorem R2396951 : Reach 2396951 := rs (se 1 (by rfl) ⟨1797713, by rfl⟩) R3595427
theorem R169001 : Reach 169001 := rs (se 2 (by rfl) ⟨63375, by rfl⟩) R126751
theorem R464039 : Reach 464039 := rs (se 1 (by rfl) ⟨348029, by rfl⟩) R696059
theorem R660743 : Reach 660743 := rs (se 1 (by rfl) ⟨495557, by rfl⟩) R991115
theorem R71295 : Reach 71295 := rs (se 1 (by rfl) ⟨53471, by rfl⟩) R106943
theorem R71535 : Reach 71535 := rs (se 1 (by rfl) ⟨53651, by rfl⟩) R107303
theorem R71903 : Reach 71903 := rs (se 1 (by rfl) ⟨53927, by rfl⟩) R107855
theorem R596321 : Reach 596321 := rs (se 2 (by rfl) ⟨223620, by rfl⟩) R447241
theorem R72303 : Reach 72303 := rs (se 1 (by rfl) ⟨54227, by rfl⟩) R108455
theorem R72399 : Reach 72399 := rs (se 1 (by rfl) ⟨54299, by rfl⟩) R108599
theorem R236351 : Reach 236351 := rs (se 1 (by rfl) ⟨177263, by rfl⟩) R354527
theorem R2169737 : Reach 2169737 := rs (se 2 (by rfl) ⟨813651, by rfl⟩) R1627303
theorem R72671 : Reach 72671 := rs (se 1 (by rfl) ⟨54503, by rfl⟩) R109007
theorem R72955 : Reach 72955 := rs (se 1 (by rfl) ⟨54716, by rfl⟩) R109433
theorem R433471 : Reach 433471 := rs (se 1 (by rfl) ⟨325103, by rfl⟩) R650207
theorem R73199 : Reach 73199 := rs (se 1 (by rfl) ⟨54899, by rfl⟩) R109799
theorem R73375 : Reach 73375 := rs (se 1 (by rfl) ⟨55031, by rfl⟩) R110063
theorem R106537 : Reach 106537 := rs (se 2 (by rfl) ⟨39951, by rfl⟩) R79903
theorem R73887 : Reach 73887 := rs (se 1 (by rfl) ⟨55415, by rfl⟩) R110831
theorem R1876445 : Reach 1876445 := rs (se 3 (by rfl) ⟨351833, by rfl⟩) R703667
theorem R2302451 : Reach 2302451 := rs (se 1 (by rfl) ⟨1726838, by rfl⟩) R3453677
theorem R369359 : Reach 369359 := rs (se 1 (by rfl) ⟨277019, by rfl⟩) R554039
theorem R74599 : Reach 74599 := rs (se 1 (by rfl) ⟨55949, by rfl⟩) R111899
theorem R74687 : Reach 74687 := rs (se 1 (by rfl) ⟨56015, by rfl⟩) R112031
theorem R107759 : Reach 107759 := rs (se 1 (by rfl) ⟨80819, by rfl⟩) R161639
theorem R2794985 : Reach 2794985 := rs (se 2 (by rfl) ⟨1048119, by rfl⟩) R2096239
theorem R108011 : Reach 108011 := rs (se 1 (by rfl) ⟨81008, by rfl⟩) R162017
theorem R370331 : Reach 370331 := rs (se 1 (by rfl) ⟨277748, by rfl⟩) R555497
theorem R141031 : Reach 141031 := rs (se 1 (by rfl) ⟨105773, by rfl⟩) R211547
theorem R141563 : Reach 141563 := rs (se 1 (by rfl) ⟨106172, by rfl⟩) R212345
theorem R109247 : Reach 109247 := rs (se 1 (by rfl) ⟨81935, by rfl⟩) R163871
theorem R109307 : Reach 109307 := rs (se 1 (by rfl) ⟨81980, by rfl⟩) R163961
theorem R109673 : Reach 109673 := rs (se 2 (by rfl) ⟨41127, by rfl⟩) R82255
theorem R76955 : Reach 76955 := rs (se 1 (by rfl) ⟨57716, by rfl⟩) R115433
theorem R110249 : Reach 110249 := rs (se 2 (by rfl) ⟨41343, by rfl⟩) R82687
theorem R241487 : Reach 241487 := rs (se 1 (by rfl) ⟨181115, by rfl⟩) R362231
theorem R110639 : Reach 110639 := rs (se 1 (by rfl) ⟨82979, by rfl⟩) R165959
theorem R111083 : Reach 111083 := rs (se 1 (by rfl) ⟨83312, by rfl⟩) R166625
theorem R111209 : Reach 111209 := rs (se 2 (by rfl) ⟨41703, by rfl⟩) R83407
theorem R275197 : Reach 275197 := rs (se 3 (by rfl) ⟨51599, by rfl⟩) R103199
theorem R636281 : Reach 636281 := rs (se 2 (by rfl) ⟨238605, by rfl⟩) R477211
theorem R703259 : Reach 703259 := rs (se 1 (by rfl) ⟨527444, by rfl⟩) R1054889
theorem R376487 : Reach 376487 := rs (se 1 (by rfl) ⟨282365, by rfl⟩) R564731
theorem R541811 : Reach 541811 := rs (se 1 (by rfl) ⟨406358, by rfl⟩) R812717
theorem R149339 : Reach 149339 := rs (se 1 (by rfl) ⟨112004, by rfl⟩) R224009
theorem R477161 : Reach 477161 := rs (se 2 (by rfl) ⟨178935, by rfl⟩) R357871
theorem R313631 : Reach 313631 := rs (se 1 (by rfl) ⟨235223, by rfl⟩) R470447
theorem R543833 : Reach 543833 := rs (se 2 (by rfl) ⟨203937, by rfl⟩) R407875
theorem R380641 : Reach 380641 := rs (se 2 (by rfl) ⟨142740, by rfl⟩) R285481
theorem R282959 : Reach 282959 := rs (se 1 (by rfl) ⟨212219, by rfl⟩) R424439
theorem R10474433 : Reach 10474433 := rs (se 2 (by rfl) ⟨3927912, by rfl⟩) R7855825
theorem R120953 : Reach 120953 := rs (se 2 (by rfl) ⟨45357, by rfl⟩) R90715
theorem R88555 : Reach 88555 := rs (se 1 (by rfl) ⟨66416, by rfl⟩) R132833
theorem R449185 : Reach 449185 := rs (se 2 (by rfl) ⟨168444, by rfl⟩) R336889
theorem R122303 : Reach 122303 := rs (se 1 (by rfl) ⟨91727, by rfl⟩) R183455
theorem R516223 : Reach 516223 := rs (se 1 (by rfl) ⟨387167, by rfl⟩) R774335
theorem R614537 : Reach 614537 := rs (se 2 (by rfl) ⟨230451, by rfl⟩) R460903
theorem R550151 : Reach 550151 := rs (se 1 (by rfl) ⟨412613, by rfl⟩) R825227
theorem R290017 : Reach 290017 := rs (se 2 (by rfl) ⟨108756, by rfl⟩) R217513
theorem R127423 : Reach 127423 := rs (se 1 (by rfl) ⟨95567, by rfl⟩) R191135
theorem R94927 : Reach 94927 := rs (se 1 (by rfl) ⟨71195, by rfl⟩) R142391
theorem R160487 : Reach 160487 := rs (se 1 (by rfl) ⟨120365, by rfl⟩) R240731
theorem R160595 : Reach 160595 := rs (se 1 (by rfl) ⟨120446, by rfl⟩) R240893
theorem R193519 : Reach 193519 := rs (se 1 (by rfl) ⟨145139, by rfl⟩) R290279
theorem R161387 : Reach 161387 := rs (se 1 (by rfl) ⟨121040, by rfl⟩) R242081
theorem R129401 : Reach 129401 := rs (se 2 (by rfl) ⟨48525, by rfl⟩) R97051
theorem R162287 : Reach 162287 := rs (se 1 (by rfl) ⟨121715, by rfl⟩) R243431
theorem R30539177 : Reach 30539177 := rs (se 2 (by rfl) ⟨11452191, by rfl⟩) R22904383
theorem R163547 : Reach 163547 := rs (se 1 (by rfl) ⟨122660, by rfl⟩) R245321
theorem R688297 : Reach 688297 := rs (se 2 (by rfl) ⟨258111, by rfl⟩) R516223
theorem R361207 : Reach 361207 := rs (se 1 (by rfl) ⟨270905, by rfl⟩) R541811
theorem R99559 : Reach 99559 := rs (se 1 (by rfl) ⟨74669, by rfl⟩) R149339
theorem R820853 : Reach 820853 := rs (se 5 (by rfl) ⟨38477, by rfl⟩) R76955
theorem R362555 : Reach 362555 := rs (se 1 (by rfl) ⟨271916, by rfl⟩) R543833
theorem R788687 : Reach 788687 := rs (se 1 (by rfl) ⟨591515, by rfl⟩) R1183031
theorem R6982955 : Reach 6982955 := rs (se 1 (by rfl) ⟨5237216, by rfl⟩) R10474433
theorem R397547 : Reach 397547 := rs (se 1 (by rfl) ⟨298160, by rfl⟩) R596321
theorem R1446491 : Reach 1446491 := rs (se 1 (by rfl) ⟨1084868, by rfl⟩) R2169737
theorem R1250963 : Reach 1250963 := rs (se 1 (by rfl) ⟨938222, by rfl⟩) R1876445
theorem R71839 : Reach 71839 := rs (se 1 (by rfl) ⟨53879, by rfl⟩) R107759
theorem R366767 : Reach 366767 := rs (se 1 (by rfl) ⟨275075, by rfl⟩) R550151
theorem R72007 : Reach 72007 := rs (se 1 (by rfl) ⟨54005, by rfl⟩) R108011
theorem R366929 : Reach 366929 := rs (se 2 (by rfl) ⟨137598, by rfl⟩) R275197
theorem R72831 : Reach 72831 := rs (se 1 (by rfl) ⟨54623, by rfl⟩) R109247
theorem R72871 : Reach 72871 := rs (se 1 (by rfl) ⟨54653, by rfl⟩) R109307
theorem R73115 : Reach 73115 := rs (se 1 (by rfl) ⟨54836, by rfl⟩) R109673
theorem R73499 : Reach 73499 := rs (se 1 (by rfl) ⟨55124, by rfl⟩) R110249
theorem R73759 : Reach 73759 := rs (se 1 (by rfl) ⟨55319, by rfl⟩) R110639
theorem R74055 : Reach 74055 := rs (se 1 (by rfl) ⟨55541, by rfl⟩) R111083
theorem R74139 : Reach 74139 := rs (se 1 (by rfl) ⟨55604, by rfl⟩) R111209
theorem R106991 : Reach 106991 := rs (se 1 (by rfl) ⟨80243, by rfl⟩) R160487
theorem R107063 : Reach 107063 := rs (se 1 (by rfl) ⟨80297, by rfl⟩) R160595
theorem R598913 : Reach 598913 := rs (se 2 (by rfl) ⟨224592, by rfl⟩) R449185
theorem R107591 : Reach 107591 := rs (se 1 (by rfl) ⟨80693, by rfl⟩) R161387
theorem R108191 : Reach 108191 := rs (se 1 (by rfl) ⟨81143, by rfl⟩) R162287
theorem R468839 : Reach 468839 := rs (se 1 (by rfl) ⟨351629, by rfl⟩) R703259
theorem R20359451 : Reach 20359451 := rs (se 1 (by rfl) ⟨15269588, by rfl⟩) R30539177
theorem R109031 : Reach 109031 := rs (se 1 (by rfl) ⟨81773, by rfl⟩) R163547
theorem R142049 : Reach 142049 := rs (se 2 (by rfl) ⟨53268, by rfl⟩) R106537
theorem R109295 : Reach 109295 := rs (se 1 (by rfl) ⟨81971, by rfl⟩) R163943
theorem R109775 : Reach 109775 := rs (se 1 (by rfl) ⟨82331, by rfl⟩) R164663
theorem R110183 : Reach 110183 := rs (se 1 (by rfl) ⟨82637, by rfl⟩) R165275
theorem R110591 : Reach 110591 := rs (se 1 (by rfl) ⟨82943, by rfl⟩) R165887
theorem R209087 : Reach 209087 := rs (se 1 (by rfl) ⟨156815, by rfl⟩) R313631
theorem R700811 : Reach 700811 := rs (se 1 (by rfl) ⟨525608, by rfl⟩) R1051217
theorem R112175 : Reach 112175 := rs (se 1 (by rfl) ⟨84131, by rfl⟩) R168263
theorem R112667 : Reach 112667 := rs (se 1 (by rfl) ⟨84500, by rfl⟩) R169001
theorem R309359 : Reach 309359 := rs (se 1 (by rfl) ⟨232019, by rfl⟩) R464039
theorem R440495 : Reach 440495 := rs (se 1 (by rfl) ⟨330371, by rfl⟩) R660743
theorem R80635 : Reach 80635 := rs (se 1 (by rfl) ⟨60476, by rfl⟩) R120953
theorem R81535 : Reach 81535 := rs (se 1 (by rfl) ⟨61151, by rfl⟩) R122303
theorem R507521 : Reach 507521 := rs (se 2 (by rfl) ⟨190320, by rfl⟩) R380641
theorem R409691 : Reach 409691 := rs (se 1 (by rfl) ⟨307268, by rfl⟩) R614537
theorem R246239 : Reach 246239 := rs (se 1 (by rfl) ⟨184679, by rfl⟩) R369359
theorem R246887 : Reach 246887 := rs (se 1 (by rfl) ⟨185165, by rfl⟩) R370331
theorem R118073 : Reach 118073 := rs (se 2 (by rfl) ⟨44277, by rfl⟩) R88555
theorem R86267 : Reach 86267 := rs (se 1 (by rfl) ⟨64700, by rfl⟩) R129401
theorem R577961 : Reach 577961 := rs (se 2 (by rfl) ⟨216735, by rfl⟩) R433471
theorem R250991 : Reach 250991 := rs (se 1 (by rfl) ⟨188243, by rfl⟩) R376487
theorem R874435 : Reach 874435 := rs (se 1 (by rfl) ⟨655826, by rfl⟩) R1311653
theorem R318107 : Reach 318107 := rs (se 1 (by rfl) ⟨238580, by rfl⟩) R477161
theorem R547931 : Reach 547931 := rs (se 1 (by rfl) ⟨410948, by rfl⟩) R821897
theorem R188041 : Reach 188041 := rs (se 2 (by rfl) ⟨70515, by rfl⟩) R141031
theorem R679589 : Reach 679589 := rs (se 4 (by rfl) ⟨63711, by rfl⟩) R127423
theorem R188639 : Reach 188639 := rs (se 1 (by rfl) ⟨141479, by rfl⟩) R282959
theorem R1597967 : Reach 1597967 := rs (se 1 (by rfl) ⟨1198475, by rfl⟩) R2396951
theorem R386689 : Reach 386689 := rs (se 2 (by rfl) ⟨145008, by rfl⟩) R290017
theorem R157567 : Reach 157567 := rs (se 1 (by rfl) ⟨118175, by rfl⟩) R236351
theorem R1534967 : Reach 1534967 := rs (se 1 (by rfl) ⟨1151225, by rfl⟩) R2302451
theorem R126569 : Reach 126569 := rs (se 2 (by rfl) ⟨47463, by rfl⟩) R94927
theorem R1863323 : Reach 1863323 := rs (se 1 (by rfl) ⟨1397492, by rfl⟩) R2794985
theorem R258025 : Reach 258025 := rs (se 2 (by rfl) ⟨96759, by rfl⟩) R193519
theorem R94375 : Reach 94375 := rs (se 1 (by rfl) ⟨70781, by rfl⟩) R141563
theorem R160991 : Reach 160991 := rs (se 1 (by rfl) ⟨120743, by rfl⟩) R241487
theorem R424187 : Reach 424187 := rs (se 1 (by rfl) ⟨318140, by rfl⟩) R636281
theorem R917729 : Reach 917729 := rs (se 2 (by rfl) ⟨344148, by rfl⟩) R688297
theorem R164159 : Reach 164159 := rs (se 1 (by rfl) ⟨123119, by rfl⟩) R246239
theorem R230045 : Reach 230045 := rs (se 3 (by rfl) ⟨43133, by rfl⟩) R86267
theorem R164591 : Reach 164591 := rs (se 1 (by rfl) ⟨123443, by rfl⟩) R246887
theorem R525791 : Reach 525791 := rs (se 1 (by rfl) ⟨394343, by rfl⟩) R788687
theorem R4655303 : Reach 4655303 := rs (se 1 (by rfl) ⟨3491477, by rfl⟩) R6982955
theorem R265031 : Reach 265031 := rs (se 1 (by rfl) ⟨198773, by rfl⟩) R397547
theorem R167327 : Reach 167327 := rs (se 1 (by rfl) ⟨125495, by rfl⟩) R250991
theorem R71327 : Reach 71327 := rs (se 1 (by rfl) ⟨53495, by rfl⟩) R106991
theorem R71375 : Reach 71375 := rs (se 1 (by rfl) ⟨53531, by rfl⟩) R107063
theorem R399275 : Reach 399275 := rs (se 1 (by rfl) ⟨299456, by rfl⟩) R598913
theorem R71727 : Reach 71727 := rs (se 1 (by rfl) ⟨53795, by rfl⟩) R107591
theorem R72127 : Reach 72127 := rs (se 1 (by rfl) ⟨54095, by rfl⟩) R108191
theorem R530981 : Reach 530981 := rs (se 4 (by rfl) ⟨49779, by rfl⟩) R99559
theorem R13572967 : Reach 13572967 := rs (se 1 (by rfl) ⟨10179725, by rfl⟩) R20359451
theorem R72687 : Reach 72687 := rs (se 1 (by rfl) ⟨54515, by rfl⟩) R109031
theorem R72863 : Reach 72863 := rs (se 1 (by rfl) ⟨54647, by rfl⟩) R109295
theorem R1023311 : Reach 1023311 := rs (se 1 (by rfl) ⟨767483, by rfl⟩) R1534967
theorem R73183 : Reach 73183 := rs (se 1 (by rfl) ⟨54887, by rfl⟩) R109775
theorem R73455 : Reach 73455 := rs (se 1 (by rfl) ⟨55091, by rfl⟩) R110183
theorem R73727 : Reach 73727 := rs (se 1 (by rfl) ⟨55295, by rfl⟩) R110591
theorem R139391 : Reach 139391 := rs (se 1 (by rfl) ⟨104543, by rfl⟩) R209087
theorem R467207 : Reach 467207 := rs (se 1 (by rfl) ⟨350405, by rfl⟩) R700811
theorem R107327 : Reach 107327 := rs (se 1 (by rfl) ⟨80495, by rfl⟩) R160991
theorem R107513 : Reach 107513 := rs (se 2 (by rfl) ⟨40317, by rfl⟩) R80635
theorem R74783 : Reach 74783 := rs (se 1 (by rfl) ⟨56087, by rfl⟩) R112175
theorem R75111 : Reach 75111 := rs (se 1 (by rfl) ⟨56333, by rfl⟩) R112667
theorem R206239 : Reach 206239 := rs (se 1 (by rfl) ⟨154679, by rfl⟩) R309359
theorem R108713 : Reach 108713 := rs (se 2 (by rfl) ⟨40767, by rfl⟩) R81535
theorem R338347 : Reach 338347 := rs (se 1 (by rfl) ⟨253760, by rfl⟩) R507521
theorem R1092509 : Reach 1092509 := rs (se 3 (by rfl) ⟨204845, by rfl⟩) R409691
theorem R241703 : Reach 241703 := rs (se 1 (by rfl) ⟨181277, by rfl⟩) R362555
theorem R78715 : Reach 78715 := rs (se 1 (by rfl) ⟨59036, by rfl⟩) R118073
theorem R210089 : Reach 210089 := rs (se 2 (by rfl) ⟨78783, by rfl⟩) R157567
theorem R964327 : Reach 964327 := rs (se 1 (by rfl) ⟨723245, by rfl⟩) R1446491
theorem R833975 : Reach 833975 := rs (se 1 (by rfl) ⟨625481, by rfl⟩) R1250963
theorem R244511 : Reach 244511 := rs (se 1 (by rfl) ⟨183383, by rfl⟩) R366767
theorem R244619 : Reach 244619 := rs (se 1 (by rfl) ⟨183464, by rfl⟩) R366929
theorem R212071 : Reach 212071 := rs (se 1 (by rfl) ⟨159053, by rfl⟩) R318107
theorem R344033 : Reach 344033 := rs (se 2 (by rfl) ⟨129012, by rfl⟩) R258025
theorem R1065311 : Reach 1065311 := rs (se 1 (by rfl) ⟨798983, by rfl⟩) R1597967
theorem R312559 : Reach 312559 := rs (se 1 (by rfl) ⟨234419, by rfl⟩) R468839
theorem R84379 : Reach 84379 := rs (se 1 (by rfl) ⟨63284, by rfl⟩) R126569
theorem R1165913 : Reach 1165913 := rs (se 2 (by rfl) ⟨437217, by rfl⟩) R874435
theorem R1461149 : Reach 1461149 := rs (se 3 (by rfl) ⟨273965, by rfl⟩) R547931
theorem R282791 : Reach 282791 := rs (se 1 (by rfl) ⟨212093, by rfl⟩) R424187
theorem R250721 : Reach 250721 := rs (se 2 (by rfl) ⟨94020, by rfl⟩) R188041
theorem R481609 : Reach 481609 := rs (se 2 (by rfl) ⟨180603, by rfl⟩) R361207
theorem R547235 : Reach 547235 := rs (se 1 (by rfl) ⟨410426, by rfl⟩) R820853
theorem R515585 : Reach 515585 := rs (se 2 (by rfl) ⟨193344, by rfl⟩) R386689
theorem R385307 : Reach 385307 := rs (se 1 (by rfl) ⟨288980, by rfl⟩) R577961
theorem R453059 : Reach 453059 := rs (se 1 (by rfl) ⟨339794, by rfl⟩) R679589
theorem R125759 : Reach 125759 := rs (se 1 (by rfl) ⟨94319, by rfl⟩) R188639
theorem R125833 : Reach 125833 := rs (se 2 (by rfl) ⟨47187, by rfl⟩) R94375
theorem R290749 : Reach 290749 := rs (se 3 (by rfl) ⟨54515, by rfl⟩) R109031
theorem R94699 : Reach 94699 := rs (se 1 (by rfl) ⟨71024, by rfl⟩) R142049
theorem R1242215 : Reach 1242215 := rs (se 1 (by rfl) ⟨931661, by rfl⟩) R1863323
theorem R293663 : Reach 293663 := rs (se 1 (by rfl) ⟨220247, by rfl⟩) R440495
theorem R1804517 : Reach 1804517 := rs (se 4 (by rfl) ⟨169173, by rfl⟩) R338347
theorem R167147 : Reach 167147 := rs (se 1 (by rfl) ⟨125360, by rfl⟩) R250721
theorem R167777 : Reach 167777 := rs (se 2 (by rfl) ⟨62916, by rfl⟩) R125833
theorem R266183 : Reach 266183 := rs (se 1 (by rfl) ⟨199637, by rfl⟩) R399275
theorem R364823 : Reach 364823 := rs (se 1 (by rfl) ⟨273617, by rfl⟩) R547235
theorem R71551 : Reach 71551 := rs (se 1 (by rfl) ⟨53663, by rfl⟩) R107327
theorem R71675 : Reach 71675 := rs (se 1 (by rfl) ⟨53756, by rfl⟩) R107513
theorem R72475 : Reach 72475 := rs (se 1 (by rfl) ⟨54356, by rfl⟩) R108713
theorem R302039 : Reach 302039 := rs (se 1 (by rfl) ⟨226529, by rfl⟩) R453059
theorem R1285769 : Reach 1285769 := rs (se 2 (by rfl) ⟨482163, by rfl⟩) R964327
theorem R828143 : Reach 828143 := rs (se 1 (by rfl) ⟨621107, by rfl⟩) R1242215
theorem R140059 : Reach 140059 := rs (se 1 (by rfl) ⟨105044, by rfl⟩) R210089
theorem R2728829 : Reach 2728829 := rs (se 3 (by rfl) ⟨511655, by rfl⟩) R1023311
theorem R18097289 : Reach 18097289 := rs (se 2 (by rfl) ⟨6786483, by rfl⟩) R13572967
theorem R109439 : Reach 109439 := rs (se 1 (by rfl) ⟨82079, by rfl⟩) R164159
theorem R109727 : Reach 109727 := rs (se 1 (by rfl) ⟨82295, by rfl⟩) R164591
theorem R2568581 : Reach 2568581 := rs (se 4 (by rfl) ⟨240804, by rfl⟩) R481609
theorem R274985 : Reach 274985 := rs (se 2 (by rfl) ⟨103119, by rfl⟩) R206239
theorem R176687 : Reach 176687 := rs (se 1 (by rfl) ⟨132515, by rfl⟩) R265031
theorem R111551 : Reach 111551 := rs (se 1 (by rfl) ⟨83663, by rfl⟩) R167327
theorem R112505 : Reach 112505 := rs (se 2 (by rfl) ⟨42189, by rfl⟩) R84379
theorem R311471 : Reach 311471 := rs (se 1 (by rfl) ⟨233603, by rfl⟩) R467207
theorem R46613717 : Reach 46613717 := rs (se 7 (by rfl) ⟨546254, by rfl⟩) R1092509
theorem R83839 : Reach 83839 := rs (se 1 (by rfl) ⟨62879, by rfl⟩) R125759
theorem R282761 : Reach 282761 := rs (se 2 (by rfl) ⟨106035, by rfl⟩) R212071
theorem R611819 : Reach 611819 := rs (se 1 (by rfl) ⟨458864, by rfl⟩) R917729
theorem R710207 : Reach 710207 := rs (se 1 (by rfl) ⟨532655, by rfl⟩) R1065311
theorem R3103535 : Reach 3103535 := rs (se 1 (by rfl) ⟨2327651, by rfl⟩) R4655303
theorem R777275 : Reach 777275 := rs (se 1 (by rfl) ⟨582956, by rfl⟩) R1165913
theorem R613453 : Reach 613453 := rs (se 3 (by rfl) ⟨115022, by rfl⟩) R230045
theorem R974099 : Reach 974099 := rs (se 1 (by rfl) ⟨730574, by rfl⟩) R1461149
theorem R188527 : Reach 188527 := rs (se 1 (by rfl) ⟨141395, by rfl⟩) R282791
theorem R1402109 : Reach 1402109 := rs (se 3 (by rfl) ⟨262895, by rfl⟩) R525791
theorem R353987 : Reach 353987 := rs (se 1 (by rfl) ⟨265490, by rfl⟩) R530981
theorem R419813 : Reach 419813 := rs (se 4 (by rfl) ⟨39357, by rfl⟩) R78715
theorem R387665 : Reach 387665 := rs (se 2 (by rfl) ⟨145374, by rfl⟩) R290749
theorem R92927 : Reach 92927 := rs (se 1 (by rfl) ⟨69695, by rfl⟩) R139391
theorem R256871 : Reach 256871 := rs (se 1 (by rfl) ⟨192653, by rfl⟩) R385307
theorem R126265 : Reach 126265 := rs (se 2 (by rfl) ⟨47349, by rfl⟩) R94699
theorem R1666981 : Reach 1666981 := rs (se 4 (by rfl) ⟨156279, by rfl⟩) R312559
theorem R783101 : Reach 783101 := rs (se 3 (by rfl) ⟨146831, by rfl⟩) R293663
theorem R161135 : Reach 161135 := rs (se 1 (by rfl) ⟨120851, by rfl⟩) R241703
theorem R1374893 : Reach 1374893 := rs (se 3 (by rfl) ⟨257792, by rfl⟩) R515585
theorem R555983 : Reach 555983 := rs (se 1 (by rfl) ⟨416987, by rfl⟩) R833975
theorem R163007 : Reach 163007 := rs (se 1 (by rfl) ⟨122255, by rfl⟩) R244511
theorem R163079 : Reach 163079 := rs (se 1 (by rfl) ⟨122309, by rfl⟩) R244619
theorem R229355 : Reach 229355 := rs (se 1 (by rfl) ⟨172016, by rfl⟩) R344033
theorem R168353 : Reach 168353 := rs (se 2 (by rfl) ⟨63132, by rfl⟩) R126265
theorem R2069023 : Reach 2069023 := rs (se 1 (by rfl) ⟨1551767, by rfl⟩) R3103535
theorem R201359 : Reach 201359 := rs (se 1 (by rfl) ⟨151019, by rfl⟩) R302039
theorem R857179 : Reach 857179 := rs (se 1 (by rfl) ⟨642884, by rfl⟩) R1285769
theorem R12064859 : Reach 12064859 := rs (se 1 (by rfl) ⟨9048644, by rfl⟩) R18097289
theorem R235991 : Reach 235991 := rs (se 1 (by rfl) ⟨176993, by rfl⟩) R353987
theorem R171247 : Reach 171247 := rs (se 1 (by rfl) ⟨128435, by rfl⟩) R256871
theorem R72959 : Reach 72959 := rs (se 1 (by rfl) ⟨54719, by rfl⟩) R109439
theorem R73151 : Reach 73151 := rs (se 1 (by rfl) ⟨54863, by rfl⟩) R109727
theorem R74367 : Reach 74367 := rs (se 1 (by rfl) ⟨55775, by rfl⟩) R111551
theorem R107423 : Reach 107423 := rs (se 1 (by rfl) ⟨80567, by rfl⟩) R161135
theorem R75003 : Reach 75003 := rs (se 1 (by rfl) ⟨56252, by rfl⟩) R112505
theorem R370655 : Reach 370655 := rs (se 1 (by rfl) ⟨277991, by rfl⟩) R555983
theorem R108671 : Reach 108671 := rs (se 1 (by rfl) ⟨81503, by rfl⟩) R163007
theorem R108719 : Reach 108719 := rs (se 1 (by rfl) ⟨81539, by rfl⟩) R163079
theorem R8890565 : Reach 8890565 := rs (se 4 (by rfl) ⟨833490, by rfl⟩) R1666981
theorem R207647 : Reach 207647 := rs (se 1 (by rfl) ⟨155735, by rfl⟩) R311471
theorem R31075811 : Reach 31075811 := rs (se 1 (by rfl) ⟨23306858, by rfl⟩) R46613717
theorem R111431 : Reach 111431 := rs (se 1 (by rfl) ⟨83573, by rfl⟩) R167147
theorem R111785 : Reach 111785 := rs (se 2 (by rfl) ⟨41919, by rfl⟩) R83839
theorem R111851 : Reach 111851 := rs (se 1 (by rfl) ⟨83888, by rfl⟩) R167777
theorem R177455 : Reach 177455 := rs (se 1 (by rfl) ⟨133091, by rfl⟩) R266183
theorem R243215 : Reach 243215 := rs (se 1 (by rfl) ⟨182411, by rfl⟩) R364823
theorem R407879 : Reach 407879 := rs (se 1 (by rfl) ⟨305909, by rfl⟩) R611819
theorem R473471 : Reach 473471 := rs (se 1 (by rfl) ⟨355103, by rfl⟩) R710207
theorem R1819219 : Reach 1819219 := rs (se 1 (by rfl) ⟨1364414, by rfl⟩) R2728829
theorem R934739 : Reach 934739 := rs (se 1 (by rfl) ⟨701054, by rfl⟩) R1402109
theorem R279875 : Reach 279875 := rs (se 1 (by rfl) ⟨209906, by rfl⟩) R419813
theorem R247805 : Reach 247805 := rs (se 3 (by rfl) ⟨46463, by rfl⟩) R92927
theorem R183323 : Reach 183323 := rs (se 1 (by rfl) ⟨137492, by rfl⟩) R274985
theorem R117791 : Reach 117791 := rs (se 1 (by rfl) ⟨88343, by rfl⟩) R176687
theorem R152903 : Reach 152903 := rs (se 1 (by rfl) ⟨114677, by rfl⟩) R229355
theorem R251369 : Reach 251369 := rs (se 2 (by rfl) ⟨94263, by rfl⟩) R188527
theorem R186745 : Reach 186745 := rs (se 2 (by rfl) ⟨70029, by rfl⟩) R140059
theorem R1203011 : Reach 1203011 := rs (se 1 (by rfl) ⟨902258, by rfl⟩) R1804517
theorem R188507 : Reach 188507 := rs (se 1 (by rfl) ⟨141380, by rfl⟩) R282761
theorem R518183 : Reach 518183 := rs (se 1 (by rfl) ⟨388637, by rfl⟩) R777275
theorem R649399 : Reach 649399 := rs (se 1 (by rfl) ⟨487049, by rfl⟩) R974099
theorem R552095 : Reach 552095 := rs (se 1 (by rfl) ⟨414071, by rfl⟩) R828143
theorem R258443 : Reach 258443 := rs (se 1 (by rfl) ⟨193832, by rfl⟩) R387665
theorem R1712387 : Reach 1712387 := rs (se 1 (by rfl) ⟨1284290, by rfl⟩) R2568581
theorem R522067 : Reach 522067 := rs (se 1 (by rfl) ⟨391550, by rfl⟩) R783101
theorem R817937 : Reach 817937 := rs (se 2 (by rfl) ⟨306726, by rfl⟩) R613453
theorem R916595 : Reach 916595 := rs (se 1 (by rfl) ⟨687446, by rfl⟩) R1374893
theorem R623159 : Reach 623159 := rs (se 1 (by rfl) ⟨467369, by rfl⟩) R934739
theorem R2425625 : Reach 2425625 := rs (se 2 (by rfl) ⟨909609, by rfl⟩) R1819219
theorem R165203 : Reach 165203 := rs (se 1 (by rfl) ⟨123902, by rfl⟩) R247805
theorem R134239 : Reach 134239 := rs (se 1 (by rfl) ⟨100679, by rfl⟩) R201359
theorem R101935 : Reach 101935 := rs (se 1 (by rfl) ⟨76451, by rfl⟩) R152903
theorem R167579 : Reach 167579 := rs (se 1 (by rfl) ⟨125684, by rfl⟩) R251369
theorem R71615 : Reach 71615 := rs (se 1 (by rfl) ⟨53711, by rfl⟩) R107423
theorem R2758697 : Reach 2758697 := rs (se 2 (by rfl) ⟨1034511, by rfl⟩) R2069023
theorem R629309 : Reach 629309 := rs (se 3 (by rfl) ⟨117995, by rfl⟩) R235991
theorem R72447 : Reach 72447 := rs (se 1 (by rfl) ⟨54335, by rfl⟩) R108671
theorem R72479 : Reach 72479 := rs (se 1 (by rfl) ⟨54359, by rfl⟩) R108719
theorem R138431 : Reach 138431 := rs (se 1 (by rfl) ⟨103823, by rfl⟩) R207647
theorem R368063 : Reach 368063 := rs (se 1 (by rfl) ⟨276047, by rfl⟩) R552095
theorem R20717207 : Reach 20717207 := rs (se 1 (by rfl) ⟨15537905, by rfl⟩) R31075811
theorem R696089 : Reach 696089 := rs (se 2 (by rfl) ⟨261033, by rfl⟩) R522067
theorem R172295 : Reach 172295 := rs (se 1 (by rfl) ⟨129221, by rfl⟩) R258443
theorem R74287 : Reach 74287 := rs (se 1 (by rfl) ⟨55715, by rfl⟩) R111431
theorem R74523 : Reach 74523 := rs (se 1 (by rfl) ⟨55892, by rfl⟩) R111785
theorem R74567 : Reach 74567 := rs (se 1 (by rfl) ⟨55925, by rfl⟩) R111851
theorem R271919 : Reach 271919 := rs (se 1 (by rfl) ⟨203939, by rfl⟩) R407879
theorem R4566365 : Reach 4566365 := rs (se 3 (by rfl) ⟨856193, by rfl⟩) R1712387
theorem R78527 : Reach 78527 := rs (se 1 (by rfl) ⟨58895, by rfl⟩) R117791
theorem R865865 : Reach 865865 := rs (se 2 (by rfl) ⟨324699, by rfl⟩) R649399
theorem R112235 : Reach 112235 := rs (se 1 (by rfl) ⟨84176, by rfl⟩) R168353
theorem R8043239 : Reach 8043239 := rs (se 1 (by rfl) ⟨6032429, by rfl⟩) R12064859
theorem R802007 : Reach 802007 := rs (se 1 (by rfl) ⟨601505, by rfl⟩) R1203011
theorem R23708173 : Reach 23708173 := rs (se 3 (by rfl) ⟨4445282, by rfl⟩) R8890565
theorem R247103 : Reach 247103 := rs (se 1 (by rfl) ⟨185327, by rfl⟩) R370655
theorem R345455 : Reach 345455 := rs (se 1 (by rfl) ⟨259091, by rfl⟩) R518183
theorem R248993 : Reach 248993 := rs (se 2 (by rfl) ⟨93372, by rfl⟩) R186745
theorem R118303 : Reach 118303 := rs (se 1 (by rfl) ⟨88727, by rfl⟩) R177455
theorem R315647 : Reach 315647 := rs (se 1 (by rfl) ⟨236735, by rfl⟩) R473471
theorem R545291 : Reach 545291 := rs (se 1 (by rfl) ⟨408968, by rfl⟩) R817937
theorem R611063 : Reach 611063 := rs (se 1 (by rfl) ⟨458297, by rfl⟩) R916595
theorem R186583 : Reach 186583 := rs (se 1 (by rfl) ⟨139937, by rfl⟩) R279875
theorem R122215 : Reach 122215 := rs (se 1 (by rfl) ⟨91661, by rfl⟩) R183323
theorem R125671 : Reach 125671 := rs (se 1 (by rfl) ⟨94253, by rfl⟩) R188507
theorem R1142905 : Reach 1142905 := rs (se 2 (by rfl) ⟨428589, by rfl⟩) R857179
theorem R162143 : Reach 162143 := rs (se 1 (by rfl) ⟨121607, by rfl⟩) R243215
theorem R228329 : Reach 228329 := rs (se 2 (by rfl) ⟨85623, by rfl⟩) R171247
theorem R164735 : Reach 164735 := rs (se 1 (by rfl) ⟨123551, by rfl⟩) R247103
theorem R230303 : Reach 230303 := rs (se 1 (by rfl) ⟨172727, by rfl⟩) R345455
theorem R165995 : Reach 165995 := rs (se 1 (by rfl) ⟨124496, by rfl⟩) R248993
theorem R363527 : Reach 363527 := rs (se 1 (by rfl) ⟨272645, by rfl⟩) R545291
theorem R167561 : Reach 167561 := rs (se 2 (by rfl) ⟨62835, by rfl⟩) R125671
theorem R1839131 : Reach 1839131 := rs (se 1 (by rfl) ⟨1379348, by rfl⟩) R2758697
theorem R725117 : Reach 725117 := rs (se 3 (by rfl) ⟨135959, by rfl⟩) R271919
theorem R135913 : Reach 135913 := rs (se 2 (by rfl) ⟨50967, by rfl⟩) R101935
theorem R464059 : Reach 464059 := rs (se 1 (by rfl) ⟨348044, by rfl⟩) R696089
theorem R630949 : Reach 630949 := rs (se 4 (by rfl) ⟨59151, by rfl⟩) R118303
theorem R74823 : Reach 74823 := rs (se 1 (by rfl) ⟨56117, by rfl⟩) R112235
theorem R108095 : Reach 108095 := rs (se 1 (by rfl) ⟨81071, by rfl⟩) R162143
theorem R534671 : Reach 534671 := rs (se 1 (by rfl) ⟨401003, by rfl⟩) R802007
theorem R1617083 : Reach 1617083 := rs (se 1 (by rfl) ⟨1212812, by rfl⟩) R2425625
theorem R110135 : Reach 110135 := rs (se 1 (by rfl) ⟨82601, by rfl⟩) R165203
theorem R209405 : Reach 209405 := rs (se 3 (by rfl) ⟨39263, by rfl⟩) R78527
theorem R111719 : Reach 111719 := rs (se 1 (by rfl) ⟨83789, by rfl⟩) R167579
theorem R210431 : Reach 210431 := rs (se 1 (by rfl) ⟨157823, by rfl⟩) R315647
theorem R407375 : Reach 407375 := rs (se 1 (by rfl) ⟨305531, by rfl⟩) R611063
theorem R178985 : Reach 178985 := rs (se 2 (by rfl) ⟨67119, by rfl⟩) R134239
theorem R245375 : Reach 245375 := rs (se 1 (by rfl) ⟨184031, by rfl⟩) R368063
theorem R13811471 : Reach 13811471 := rs (se 1 (by rfl) ⟨10358603, by rfl⟩) R20717207
theorem R1523873 : Reach 1523873 := rs (se 2 (by rfl) ⟨571452, by rfl⟩) R1142905
theorem R114863 : Reach 114863 := rs (se 1 (by rfl) ⟨86147, by rfl⟩) R172295
theorem R248777 : Reach 248777 := rs (se 2 (by rfl) ⟨93291, by rfl⟩) R186583
theorem R577243 : Reach 577243 := rs (se 1 (by rfl) ⟨432932, by rfl⟩) R865865
theorem R5362159 : Reach 5362159 := rs (se 1 (by rfl) ⟨4021619, by rfl⟩) R8043239
theorem R152219 : Reach 152219 := rs (se 1 (by rfl) ⟨114164, by rfl⟩) R228329
theorem R415439 : Reach 415439 := rs (se 1 (by rfl) ⟨311579, by rfl⟩) R623159
theorem R31610897 : Reach 31610897 := rs (se 2 (by rfl) ⟨11854086, by rfl⟩) R23708173
theorem R419539 : Reach 419539 := rs (se 1 (by rfl) ⟨314654, by rfl⟩) R629309
theorem R92287 : Reach 92287 := rs (se 1 (by rfl) ⟨69215, by rfl⟩) R138431
theorem R3044243 : Reach 3044243 := rs (se 1 (by rfl) ⟨2283182, by rfl⟩) R4566365
theorem R162953 : Reach 162953 := rs (se 2 (by rfl) ⟨61107, by rfl⟩) R122215
theorem R1015915 : Reach 1015915 := rs (se 1 (by rfl) ⟨761936, by rfl⟩) R1523873
theorem R1933645 : Reach 1933645 := rs (se 3 (by rfl) ⟨362558, by rfl⟩) R725117
theorem R558413 : Reach 558413 := rs (se 3 (by rfl) ⟨104702, by rfl⟩) R209405
theorem R165851 : Reach 165851 := rs (se 1 (by rfl) ⟨124388, by rfl⟩) R248777
theorem R559385 : Reach 559385 := rs (se 2 (by rfl) ⟨209769, by rfl⟩) R419539
theorem R21073931 : Reach 21073931 := rs (se 1 (by rfl) ⟨15805448, by rfl⟩) R31610897
theorem R7149545 : Reach 7149545 := rs (se 2 (by rfl) ⟨2681079, by rfl⟩) R5362159
theorem R72063 : Reach 72063 := rs (se 1 (by rfl) ⟨54047, by rfl⟩) R108095
theorem R73423 : Reach 73423 := rs (se 1 (by rfl) ⟨55067, by rfl⟩) R110135
theorem R74479 : Reach 74479 := rs (se 1 (by rfl) ⟨55859, by rfl⟩) R111719
theorem R140287 : Reach 140287 := rs (se 1 (by rfl) ⟨105215, by rfl⟩) R210431
theorem R271583 : Reach 271583 := rs (se 1 (by rfl) ⟨203687, by rfl⟩) R407375
theorem R108635 : Reach 108635 := rs (se 1 (by rfl) ⟨81476, by rfl⟩) R162953
theorem R306301 : Reach 306301 := rs (se 3 (by rfl) ⟨57431, by rfl⟩) R114863
theorem R109823 : Reach 109823 := rs (se 1 (by rfl) ⟨82367, by rfl⟩) R164735
theorem R110663 : Reach 110663 := rs (se 1 (by rfl) ⟨82997, by rfl⟩) R165995
theorem R405917 : Reach 405917 := rs (se 3 (by rfl) ⟨76109, by rfl⟩) R152219
theorem R242351 : Reach 242351 := rs (se 1 (by rfl) ⟨181763, by rfl⟩) R363527
theorem R111707 : Reach 111707 := rs (se 1 (by rfl) ⟨83780, by rfl⟩) R167561
theorem R1226087 : Reach 1226087 := rs (se 1 (by rfl) ⟨919565, by rfl⟩) R1839131
theorem R276959 : Reach 276959 := rs (se 1 (by rfl) ⟨207719, by rfl⟩) R415439
theorem R769657 : Reach 769657 := rs (se 2 (by rfl) ⟨288621, by rfl⟩) R577243
theorem R181217 : Reach 181217 := rs (se 2 (by rfl) ⟨67956, by rfl⟩) R135913
theorem R119323 : Reach 119323 := rs (se 1 (by rfl) ⟨89492, by rfl⟩) R178985
theorem R841265 : Reach 841265 := rs (se 2 (by rfl) ⟨315474, by rfl⟩) R630949
theorem R153535 : Reach 153535 := rs (se 1 (by rfl) ⟨115151, by rfl⟩) R230303
theorem R123049 : Reach 123049 := rs (se 2 (by rfl) ⟨46143, by rfl⟩) R92287
theorem R356447 : Reach 356447 := rs (se 1 (by rfl) ⟨267335, by rfl⟩) R534671
theorem R618745 : Reach 618745 := rs (se 2 (by rfl) ⟨232029, by rfl⟩) R464059
theorem R1078055 : Reach 1078055 := rs (se 1 (by rfl) ⟨808541, by rfl⟩) R1617083
theorem R2029495 : Reach 2029495 := rs (se 1 (by rfl) ⟨1522121, by rfl⟩) R3044243
theorem R163583 : Reach 163583 := rs (se 1 (by rfl) ⟨122687, by rfl⟩) R245375
theorem R9207647 : Reach 9207647 := rs (se 1 (by rfl) ⟨6905735, by rfl⟩) R13811471
theorem R950525 : Reach 950525 := rs (se 3 (by rfl) ⟨178223, by rfl⟩) R356447
theorem R656261 : Reach 656261 := rs (se 4 (by rfl) ⟨61524, by rfl⟩) R123049
theorem R560843 : Reach 560843 := rs (se 1 (by rfl) ⟨420632, by rfl⟩) R841265
theorem R824993 : Reach 824993 := rs (se 2 (by rfl) ⟨309372, by rfl⟩) R618745
theorem R72423 : Reach 72423 := rs (se 1 (by rfl) ⟨54317, by rfl⟩) R108635
theorem R73215 : Reach 73215 := rs (se 1 (by rfl) ⟨54911, by rfl⟩) R109823
theorem R204713 : Reach 204713 := rs (se 2 (by rfl) ⟨76767, by rfl⟩) R153535
theorem R73775 : Reach 73775 := rs (se 1 (by rfl) ⟨55331, by rfl⟩) R110663
theorem R270611 : Reach 270611 := rs (se 1 (by rfl) ⟨202958, by rfl⟩) R405917
theorem R74471 : Reach 74471 := rs (se 1 (by rfl) ⟨55853, by rfl⟩) R111707
theorem R1026209 : Reach 1026209 := rs (se 2 (by rfl) ⟨384828, by rfl⟩) R769657
theorem R109055 : Reach 109055 := rs (se 1 (by rfl) ⟨81791, by rfl⟩) R163583
theorem R6138431 : Reach 6138431 := rs (se 1 (by rfl) ⟨4603823, by rfl⟩) R9207647
theorem R1354553 : Reach 1354553 := rs (se 2 (by rfl) ⟨507957, by rfl⟩) R1015915
theorem R372275 : Reach 372275 := rs (se 1 (by rfl) ⟨279206, by rfl⟩) R558413
theorem R110567 : Reach 110567 := rs (se 1 (by rfl) ⟨82925, by rfl⟩) R165851
theorem R372923 : Reach 372923 := rs (se 1 (by rfl) ⟨279692, by rfl⟩) R559385
theorem R4766363 : Reach 4766363 := rs (se 1 (by rfl) ⟨3574772, by rfl⟩) R7149545
theorem R408401 : Reach 408401 := rs (se 2 (by rfl) ⟨153150, by rfl⟩) R306301
theorem R181055 : Reach 181055 := rs (se 1 (by rfl) ⟨135791, by rfl⟩) R271583
theorem R2705993 : Reach 2705993 := rs (se 2 (by rfl) ⟨1014747, by rfl⟩) R2029495
theorem R184639 : Reach 184639 := rs (se 1 (by rfl) ⟨138479, by rfl⟩) R276959
theorem R2578193 : Reach 2578193 := rs (se 2 (by rfl) ⟨966822, by rfl⟩) R1933645
theorem R120811 : Reach 120811 := rs (se 1 (by rfl) ⟨90608, by rfl⟩) R181217
theorem R187049 : Reach 187049 := rs (se 2 (by rfl) ⟨70143, by rfl⟩) R140287
theorem R14049287 : Reach 14049287 := rs (se 1 (by rfl) ⟨10536965, by rfl⟩) R21073931
theorem R159097 : Reach 159097 := rs (se 2 (by rfl) ⟨59661, by rfl⟩) R119323
theorem R161567 : Reach 161567 := rs (se 1 (by rfl) ⟨121175, by rfl⟩) R242351
theorem R718703 : Reach 718703 := rs (se 1 (by rfl) ⟨539027, by rfl⟩) R1078055
theorem R817391 : Reach 817391 := rs (se 1 (by rfl) ⟨613043, by rfl⟩) R1226087
theorem R1803995 : Reach 1803995 := rs (se 1 (by rfl) ⟨1352996, by rfl⟩) R2705993
theorem R136475 : Reach 136475 := rs (se 1 (by rfl) ⟨102356, by rfl⟩) R204713
theorem R72703 : Reach 72703 := rs (se 1 (by rfl) ⟨54527, by rfl⟩) R109055
theorem R73711 : Reach 73711 := rs (se 1 (by rfl) ⟨55283, by rfl⟩) R110567
theorem R107711 : Reach 107711 := rs (se 1 (by rfl) ⟨80783, by rfl⟩) R161567
theorem R272267 : Reach 272267 := rs (se 1 (by rfl) ⟨204200, by rfl⟩) R408401
theorem R633683 : Reach 633683 := rs (se 1 (by rfl) ⟨475262, by rfl⟩) R950525
theorem R437507 : Reach 437507 := rs (se 1 (by rfl) ⟨328130, by rfl⟩) R656261
theorem R373895 : Reach 373895 := rs (se 1 (by rfl) ⟨280421, by rfl⟩) R560843
theorem R1718795 : Reach 1718795 := rs (se 1 (by rfl) ⟨1289096, by rfl⟩) R2578193
theorem R212129 : Reach 212129 := rs (se 2 (by rfl) ⟨79548, by rfl⟩) R159097
theorem R180407 : Reach 180407 := rs (se 1 (by rfl) ⟨135305, by rfl⟩) R270611
theorem R246185 : Reach 246185 := rs (se 2 (by rfl) ⟨92319, by rfl⟩) R184639
theorem R2179709 : Reach 2179709 := rs (se 3 (by rfl) ⟨408695, by rfl⟩) R817391
theorem R903035 : Reach 903035 := rs (se 1 (by rfl) ⟨677276, by rfl⟩) R1354553
theorem R248183 : Reach 248183 := rs (se 1 (by rfl) ⟨186137, by rfl⟩) R372275
theorem R248615 : Reach 248615 := rs (se 1 (by rfl) ⟨186461, by rfl⟩) R372923
theorem R479135 : Reach 479135 := rs (se 1 (by rfl) ⟨359351, by rfl⟩) R718703
theorem R120703 : Reach 120703 := rs (se 1 (by rfl) ⟨90527, by rfl⟩) R181055
theorem R549995 : Reach 549995 := rs (se 1 (by rfl) ⟨412496, by rfl⟩) R824993
theorem R124699 : Reach 124699 := rs (se 1 (by rfl) ⟨93524, by rfl⟩) R187049
theorem R9366191 : Reach 9366191 := rs (se 1 (by rfl) ⟨7024643, by rfl⟩) R14049287
theorem R684139 : Reach 684139 := rs (se 1 (by rfl) ⟨513104, by rfl⟩) R1026209
theorem R4092287 : Reach 4092287 := rs (se 1 (by rfl) ⟨3069215, by rfl⟩) R6138431
theorem R161081 : Reach 161081 := rs (se 2 (by rfl) ⟨60405, by rfl⟩) R120811
theorem R3177575 : Reach 3177575 := rs (se 1 (by rfl) ⟨2383181, by rfl⟩) R4766363
theorem R164123 : Reach 164123 := rs (se 1 (by rfl) ⟨123092, by rfl⟩) R246185
theorem R10912765 : Reach 10912765 := rs (se 3 (by rfl) ⟨2046143, by rfl⟩) R4092287
theorem R5866613 : Reach 5866613 := rs (se 5 (by rfl) ⟨274997, by rfl⟩) R549995
theorem R165455 : Reach 165455 := rs (se 1 (by rfl) ⟨124091, by rfl⟩) R248183
theorem R165743 : Reach 165743 := rs (se 1 (by rfl) ⟨124307, by rfl⟩) R248615
theorem R166265 : Reach 166265 := rs (se 2 (by rfl) ⟨62349, by rfl⟩) R124699
theorem R71807 : Reach 71807 := rs (se 1 (by rfl) ⟨53855, by rfl⟩) R107711
theorem R107387 : Reach 107387 := rs (se 1 (by rfl) ⟨80540, by rfl⟩) R161081
theorem R141419 : Reach 141419 := rs (se 1 (by rfl) ⟨106064, by rfl⟩) R212129
theorem R1453139 : Reach 1453139 := rs (se 1 (by rfl) ⟨1089854, by rfl⟩) R2179709
theorem R2408093 : Reach 2408093 := rs (se 3 (by rfl) ⟨451517, by rfl⟩) R903035
theorem R181511 : Reach 181511 := rs (se 1 (by rfl) ⟨136133, by rfl⟩) R272267
theorem R6244127 : Reach 6244127 := rs (se 1 (by rfl) ⟨4683095, by rfl⟩) R9366191
theorem R249263 : Reach 249263 := rs (se 1 (by rfl) ⟨186947, by rfl⟩) R373895
theorem R2118383 : Reach 2118383 := rs (se 1 (by rfl) ⟨1588787, by rfl⟩) R3177575
theorem R120271 : Reach 120271 := rs (se 1 (by rfl) ⟨90203, by rfl⟩) R180407
theorem R1202663 : Reach 1202663 := rs (se 1 (by rfl) ⟨901997, by rfl⟩) R1803995
theorem R319423 : Reach 319423 := rs (se 1 (by rfl) ⟨239567, by rfl⟩) R479135
theorem R90983 : Reach 90983 := rs (se 1 (by rfl) ⟨68237, by rfl⟩) R136475
theorem R912185 : Reach 912185 := rs (se 2 (by rfl) ⟨342069, by rfl⟩) R684139
theorem R422455 : Reach 422455 := rs (se 1 (by rfl) ⟨316841, by rfl⟩) R633683
theorem R291671 : Reach 291671 := rs (se 1 (by rfl) ⟨218753, by rfl⟩) R437507
theorem R160937 : Reach 160937 := rs (se 2 (by rfl) ⟨60351, by rfl⟩) R120703
theorem R1145863 : Reach 1145863 := rs (se 1 (by rfl) ⟨859397, by rfl⟩) R1718795
theorem R4162751 : Reach 4162751 := rs (se 1 (by rfl) ⟨3122063, by rfl⟩) R6244127
theorem R14550353 : Reach 14550353 := rs (se 2 (by rfl) ⟨5456382, by rfl⟩) R10912765
theorem R166175 : Reach 166175 := rs (se 1 (by rfl) ⟨124631, by rfl⟩) R249263
theorem R1412255 : Reach 1412255 := rs (se 1 (by rfl) ⟨1059191, by rfl⟩) R2118383
theorem R71591 : Reach 71591 := rs (se 1 (by rfl) ⟨53693, by rfl⟩) R107387
theorem R563273 : Reach 563273 := rs (se 2 (by rfl) ⟨211227, by rfl⟩) R422455
theorem R107291 : Reach 107291 := rs (se 1 (by rfl) ⟨80468, by rfl⟩) R160937
theorem R109415 : Reach 109415 := rs (se 1 (by rfl) ⟨82061, by rfl⟩) R164123
theorem R3911075 : Reach 3911075 := rs (se 1 (by rfl) ⟨2933306, by rfl⟩) R5866613
theorem R110303 : Reach 110303 := rs (se 1 (by rfl) ⟨82727, by rfl⟩) R165455
theorem R110495 : Reach 110495 := rs (se 1 (by rfl) ⟨82871, by rfl⟩) R165743
theorem R110843 : Reach 110843 := rs (se 1 (by rfl) ⟨83132, by rfl⟩) R166265
theorem R242621 : Reach 242621 := rs (se 3 (by rfl) ⟨45491, by rfl⟩) R90983
theorem R801775 : Reach 801775 := rs (se 1 (by rfl) ⟨601331, by rfl⟩) R1202663
theorem R608123 : Reach 608123 := rs (se 1 (by rfl) ⟨456092, by rfl⟩) R912185
theorem R968759 : Reach 968759 := rs (se 1 (by rfl) ⟨726569, by rfl⟩) R1453139
theorem R1527817 : Reach 1527817 := rs (se 2 (by rfl) ⟨572931, by rfl⟩) R1145863
theorem R121007 : Reach 121007 := rs (se 1 (by rfl) ⟨90755, by rfl⟩) R181511
theorem R94279 : Reach 94279 := rs (se 1 (by rfl) ⟨70709, by rfl⟩) R141419
theorem R160361 : Reach 160361 := rs (se 2 (by rfl) ⟨60135, by rfl⟩) R120271
theorem R194447 : Reach 194447 := rs (se 1 (by rfl) ⟨145835, by rfl⟩) R291671
theorem R1605395 : Reach 1605395 := rs (se 1 (by rfl) ⟨1204046, by rfl⟩) R2408093
theorem R425897 : Reach 425897 := rs (se 2 (by rfl) ⟨159711, by rfl⟩) R319423
theorem R9700235 : Reach 9700235 := rs (se 1 (by rfl) ⟨7275176, by rfl⟩) R14550353
theorem R2037089 : Reach 2037089 := rs (se 2 (by rfl) ⟨763908, by rfl⟩) R1527817
theorem R71527 : Reach 71527 := rs (se 1 (by rfl) ⟨53645, by rfl⟩) R107291
theorem R72943 : Reach 72943 := rs (se 1 (by rfl) ⟨54707, by rfl⟩) R109415
theorem R73535 : Reach 73535 := rs (se 1 (by rfl) ⟨55151, by rfl⟩) R110303
theorem R73663 : Reach 73663 := rs (se 1 (by rfl) ⟨55247, by rfl⟩) R110495
theorem R73895 : Reach 73895 := rs (se 1 (by rfl) ⟨55421, by rfl⟩) R110843
theorem R106907 : Reach 106907 := rs (se 1 (by rfl) ⟨80180, by rfl⟩) R160361
theorem R405415 : Reach 405415 := rs (se 1 (by rfl) ⟨304061, by rfl⟩) R608123
theorem R110783 : Reach 110783 := rs (se 1 (by rfl) ⟨83087, by rfl⟩) R166175
theorem R375515 : Reach 375515 := rs (se 1 (by rfl) ⟨281636, by rfl⟩) R563273
theorem R80671 : Reach 80671 := rs (se 1 (by rfl) ⟨60503, by rfl⟩) R121007
theorem R2607383 : Reach 2607383 := rs (se 1 (by rfl) ⟨1955537, by rfl⟩) R3911075
theorem R1069033 : Reach 1069033 := rs (se 2 (by rfl) ⟨400887, by rfl⟩) R801775
theorem R1070263 : Reach 1070263 := rs (se 1 (by rfl) ⟨802697, by rfl⟩) R1605395
theorem R283931 : Reach 283931 := rs (se 1 (by rfl) ⟨212948, by rfl⟩) R425897
theorem R2775167 : Reach 2775167 := rs (se 1 (by rfl) ⟨2081375, by rfl⟩) R4162751
theorem R645839 : Reach 645839 := rs (se 1 (by rfl) ⟨484379, by rfl⟩) R968759
theorem R941503 : Reach 941503 := rs (se 1 (by rfl) ⟨706127, by rfl⟩) R1412255
theorem R518525 : Reach 518525 := rs (se 3 (by rfl) ⟨97223, by rfl⟩) R194447
theorem R125705 : Reach 125705 := rs (se 2 (by rfl) ⟨47139, by rfl⟩) R94279
theorem R161747 : Reach 161747 := rs (se 1 (by rfl) ⟨121310, by rfl⟩) R242621
theorem R1738255 : Reach 1738255 := rs (se 1 (by rfl) ⟨1303691, by rfl⟩) R2607383
theorem R430559 : Reach 430559 := rs (se 1 (by rfl) ⟨322919, by rfl⟩) R645839
theorem R71271 : Reach 71271 := rs (se 1 (by rfl) ⟨53453, by rfl⟩) R106907
theorem R73855 : Reach 73855 := rs (se 1 (by rfl) ⟨55391, by rfl⟩) R110783
theorem R107561 : Reach 107561 := rs (se 2 (by rfl) ⟨40335, by rfl⟩) R80671
theorem R107831 : Reach 107831 := rs (se 1 (by rfl) ⟨80873, by rfl⟩) R161747
theorem R1255337 : Reach 1255337 := rs (se 2 (by rfl) ⟨470751, by rfl⟩) R941503
theorem R6466823 : Reach 6466823 := rs (se 1 (by rfl) ⟨4850117, by rfl⟩) R9700235
theorem R1358059 : Reach 1358059 := rs (se 1 (by rfl) ⟨1018544, by rfl⟩) R2037089
theorem R1850111 : Reach 1850111 := rs (se 1 (by rfl) ⟨1387583, by rfl⟩) R2775167
theorem R1425377 : Reach 1425377 := rs (se 2 (by rfl) ⟨534516, by rfl⟩) R1069033
theorem R1427017 : Reach 1427017 := rs (se 2 (by rfl) ⟨535131, by rfl⟩) R1070263
theorem R345683 : Reach 345683 := rs (se 1 (by rfl) ⟨259262, by rfl⟩) R518525
theorem R83803 : Reach 83803 := rs (se 1 (by rfl) ⟨62852, by rfl⟩) R125705
theorem R250343 : Reach 250343 := rs (se 1 (by rfl) ⟨187757, by rfl⟩) R375515
theorem R189287 : Reach 189287 := rs (se 1 (by rfl) ⟨141965, by rfl⟩) R283931
theorem R2162213 : Reach 2162213 := rs (se 4 (by rfl) ⟨202707, by rfl⟩) R405415
theorem R393893 : Reach 393893 := rs (se 4 (by rfl) ⟨36927, by rfl⟩) R73855
theorem R230455 : Reach 230455 := rs (se 1 (by rfl) ⟨172841, by rfl⟩) R345683
theorem R1902689 : Reach 1902689 := rs (se 2 (by rfl) ⟨713508, by rfl⟩) R1427017
theorem R166895 : Reach 166895 := rs (se 1 (by rfl) ⟨125171, by rfl⟩) R250343
theorem R71707 : Reach 71707 := rs (se 1 (by rfl) ⟨53780, by rfl⟩) R107561
theorem R71887 : Reach 71887 := rs (se 1 (by rfl) ⟨53915, by rfl⟩) R107831
theorem R1810745 : Reach 1810745 := rs (se 2 (by rfl) ⟨679029, by rfl⟩) R1358059
theorem R111737 : Reach 111737 := rs (se 2 (by rfl) ⟨41901, by rfl⟩) R83803
theorem R836891 : Reach 836891 := rs (se 1 (by rfl) ⟨627668, by rfl⟩) R1255337
theorem R4311215 : Reach 4311215 := rs (se 1 (by rfl) ⟨3233411, by rfl⟩) R6466823
theorem R1233407 : Reach 1233407 := rs (se 1 (by rfl) ⟨925055, by rfl⟩) R1850111
theorem R2317673 : Reach 2317673 := rs (se 2 (by rfl) ⟨869127, by rfl⟩) R1738255
theorem R287039 : Reach 287039 := rs (se 1 (by rfl) ⟨215279, by rfl⟩) R430559
theorem R126191 : Reach 126191 := rs (se 1 (by rfl) ⟨94643, by rfl⟩) R189287
theorem R1441475 : Reach 1441475 := rs (se 1 (by rfl) ⟨1081106, by rfl⟩) R2162213
theorem R3801005 : Reach 3801005 := rs (se 3 (by rfl) ⟨712688, by rfl⟩) R1425377
theorem R262595 : Reach 262595 := rs (se 1 (by rfl) ⟨196946, by rfl⟩) R393893
theorem R557927 : Reach 557927 := rs (se 1 (by rfl) ⟨418445, by rfl⟩) R836891
theorem R822271 : Reach 822271 := rs (se 1 (by rfl) ⟨616703, by rfl⟩) R1233407
theorem R1545115 : Reach 1545115 := rs (se 1 (by rfl) ⟨1158836, by rfl⟩) R2317673
theorem R74491 : Reach 74491 := rs (se 1 (by rfl) ⟨55868, by rfl⟩) R111737
theorem R960983 : Reach 960983 := rs (se 1 (by rfl) ⟨720737, by rfl⟩) R1441475
theorem R2534003 : Reach 2534003 := rs (se 1 (by rfl) ⟨1900502, by rfl⟩) R3801005
theorem R111263 : Reach 111263 := rs (se 1 (by rfl) ⟨83447, by rfl⟩) R166895
theorem R1229093 : Reach 1229093 := rs (se 4 (by rfl) ⟨115227, by rfl⟩) R230455
theorem R84127 : Reach 84127 := rs (se 1 (by rfl) ⟨63095, by rfl⟩) R126191
theorem R1268459 : Reach 1268459 := rs (se 1 (by rfl) ⟨951344, by rfl⟩) R1902689
theorem R2874143 : Reach 2874143 := rs (se 1 (by rfl) ⟨2155607, by rfl⟩) R4311215
theorem R1207163 : Reach 1207163 := rs (se 1 (by rfl) ⟨905372, by rfl⟩) R1810745
theorem R191359 : Reach 191359 := rs (se 1 (by rfl) ⟨143519, by rfl⟩) R287039
theorem R819395 : Reach 819395 := rs (se 1 (by rfl) ⟨614546, by rfl⟩) R1229093
theorem R74175 : Reach 74175 := rs (se 1 (by rfl) ⟨55631, by rfl⟩) R111263
theorem R175063 : Reach 175063 := rs (se 1 (by rfl) ⟨131297, by rfl⟩) R262595
theorem R371951 : Reach 371951 := rs (se 1 (by rfl) ⟨278963, by rfl⟩) R557927
theorem R112169 : Reach 112169 := rs (se 2 (by rfl) ⟨42063, by rfl⟩) R84127
theorem R1096361 : Reach 1096361 := rs (se 2 (by rfl) ⟨411135, by rfl⟩) R822271
theorem R1916095 : Reach 1916095 := rs (se 1 (by rfl) ⟨1437071, by rfl⟩) R2874143
theorem R640655 : Reach 640655 := rs (se 1 (by rfl) ⟨480491, by rfl⟩) R960983
theorem R1689335 : Reach 1689335 := rs (se 1 (by rfl) ⟨1267001, by rfl⟩) R2534003
theorem R804775 : Reach 804775 := rs (se 1 (by rfl) ⟨603581, by rfl⟩) R1207163
theorem R255145 : Reach 255145 := rs (se 2 (by rfl) ⟨95679, by rfl⟩) R191359
theorem R845639 : Reach 845639 := rs (se 1 (by rfl) ⟨634229, by rfl⟩) R1268459
theorem R2060153 : Reach 2060153 := rs (se 2 (by rfl) ⟨772557, by rfl⟩) R1545115
theorem R427103 : Reach 427103 := rs (se 1 (by rfl) ⟨320327, by rfl⟩) R640655
theorem R233417 : Reach 233417 := rs (se 2 (by rfl) ⟨87531, by rfl⟩) R175063
theorem R563759 : Reach 563759 := rs (se 1 (by rfl) ⟨422819, by rfl⟩) R845639
theorem R74779 : Reach 74779 := rs (se 1 (by rfl) ⟨56084, by rfl⟩) R112169
theorem R730907 : Reach 730907 := rs (se 1 (by rfl) ⟨548180, by rfl⟩) R1096361
theorem R1126223 : Reach 1126223 := rs (se 1 (by rfl) ⟨844667, by rfl⟩) R1689335
theorem R340193 : Reach 340193 := rs (se 2 (by rfl) ⟨127572, by rfl⟩) R255145
theorem R247967 : Reach 247967 := rs (se 1 (by rfl) ⟨185975, by rfl⟩) R371951
theorem R546263 : Reach 546263 := rs (se 1 (by rfl) ⟨409697, by rfl⟩) R819395
theorem R1073033 : Reach 1073033 := rs (se 2 (by rfl) ⟨402387, by rfl⟩) R804775
theorem R1373435 : Reach 1373435 := rs (se 1 (by rfl) ⟨1030076, by rfl⟩) R2060153
theorem R2554793 : Reach 2554793 := rs (se 2 (by rfl) ⟨958047, by rfl⟩) R1916095
theorem R165311 : Reach 165311 := rs (se 1 (by rfl) ⟨123983, by rfl⟩) R247967
theorem R364175 : Reach 364175 := rs (se 1 (by rfl) ⟨273131, by rfl⟩) R546263
theorem R375839 : Reach 375839 := rs (se 1 (by rfl) ⟨281879, by rfl⟩) R563759
theorem R284735 : Reach 284735 := rs (se 1 (by rfl) ⟨213551, by rfl⟩) R427103
theorem R155611 : Reach 155611 := rs (se 1 (by rfl) ⟨116708, by rfl⟩) R233417
theorem R715355 : Reach 715355 := rs (se 1 (by rfl) ⟨536516, by rfl⟩) R1073033
theorem R487271 : Reach 487271 := rs (se 1 (by rfl) ⟨365453, by rfl⟩) R730907
theorem R750815 : Reach 750815 := rs (se 1 (by rfl) ⟨563111, by rfl⟩) R1126223
theorem R226795 : Reach 226795 := rs (se 1 (by rfl) ⟨170096, by rfl⟩) R340193
theorem R915623 : Reach 915623 := rs (se 1 (by rfl) ⟨686717, by rfl⟩) R1373435
theorem R1703195 : Reach 1703195 := rs (se 1 (by rfl) ⟨1277396, by rfl⟩) R2554793
theorem R302393 : Reach 302393 := rs (se 2 (by rfl) ⟨113397, by rfl⟩) R226795
theorem R500543 : Reach 500543 := rs (se 1 (by rfl) ⟨375407, by rfl⟩) R750815
theorem R207481 : Reach 207481 := rs (se 2 (by rfl) ⟨77805, by rfl⟩) R155611
theorem R110207 : Reach 110207 := rs (se 1 (by rfl) ⟨82655, by rfl⟩) R165311
theorem R242783 : Reach 242783 := rs (se 1 (by rfl) ⟨182087, by rfl⟩) R364175
theorem R476903 : Reach 476903 := rs (se 1 (by rfl) ⟨357677, by rfl⟩) R715355
theorem R610415 : Reach 610415 := rs (se 1 (by rfl) ⟨457811, by rfl⟩) R915623
theorem R250559 : Reach 250559 := rs (se 1 (by rfl) ⟨187919, by rfl⟩) R375839
theorem R1135463 : Reach 1135463 := rs (se 1 (by rfl) ⟨851597, by rfl⟩) R1703195
theorem R189823 : Reach 189823 := rs (se 1 (by rfl) ⟨142367, by rfl⟩) R284735
theorem R324847 : Reach 324847 := rs (se 1 (by rfl) ⟨243635, by rfl⟩) R487271
theorem R167039 : Reach 167039 := rs (se 1 (by rfl) ⟨125279, by rfl⟩) R250559
theorem R333695 : Reach 333695 := rs (se 1 (by rfl) ⟨250271, by rfl⟩) R500543
theorem R433129 : Reach 433129 := rs (se 2 (by rfl) ⟨162423, by rfl⟩) R324847
theorem R73471 : Reach 73471 := rs (se 1 (by rfl) ⟨55103, by rfl⟩) R110207
theorem R3027901 : Reach 3027901 := rs (se 3 (by rfl) ⟨567731, by rfl⟩) R1135463
theorem R406943 : Reach 406943 := rs (se 1 (by rfl) ⟨305207, by rfl⟩) R610415
theorem R276641 : Reach 276641 := rs (se 2 (by rfl) ⟨103740, by rfl⟩) R207481
theorem R806381 : Reach 806381 := rs (se 3 (by rfl) ⟨151196, by rfl⟩) R302393
theorem R317935 : Reach 317935 := rs (se 1 (by rfl) ⟨238451, by rfl⟩) R476903
theorem R253097 : Reach 253097 := rs (se 2 (by rfl) ⟨94911, by rfl⟩) R189823
theorem R161855 : Reach 161855 := rs (se 1 (by rfl) ⟨121391, by rfl⟩) R242783
theorem R168731 : Reach 168731 := rs (se 1 (by rfl) ⟨126548, by rfl⟩) R253097
theorem R4037201 : Reach 4037201 := rs (se 2 (by rfl) ⟨1513950, by rfl⟩) R3027901
theorem R271295 : Reach 271295 := rs (se 1 (by rfl) ⟨203471, by rfl⟩) R406943
theorem R107903 : Reach 107903 := rs (se 1 (by rfl) ⟨80927, by rfl⟩) R161855
theorem R111359 : Reach 111359 := rs (se 1 (by rfl) ⟨83519, by rfl⟩) R167039
theorem R537587 : Reach 537587 := rs (se 1 (by rfl) ⟨403190, by rfl⟩) R806381
theorem R577505 : Reach 577505 := rs (se 2 (by rfl) ⟨216564, by rfl⟩) R433129
theorem R184427 : Reach 184427 := rs (se 1 (by rfl) ⟨138320, by rfl⟩) R276641
theorem R222463 : Reach 222463 := rs (se 1 (by rfl) ⟨166847, by rfl⟩) R333695
theorem R423913 : Reach 423913 := rs (se 2 (by rfl) ⟨158967, by rfl⟩) R317935
theorem R296617 : Reach 296617 := rs (se 2 (by rfl) ⟨111231, by rfl⟩) R222463
theorem R2691467 : Reach 2691467 := rs (se 1 (by rfl) ⟨2018600, by rfl⟩) R4037201
theorem R71935 : Reach 71935 := rs (se 1 (by rfl) ⟨53951, by rfl⟩) R107903
theorem R565217 : Reach 565217 := rs (se 2 (by rfl) ⟨211956, by rfl⟩) R423913
theorem R74239 : Reach 74239 := rs (se 1 (by rfl) ⟨55679, by rfl⟩) R111359
theorem R112487 : Reach 112487 := rs (se 1 (by rfl) ⟨84365, by rfl⟩) R168731
theorem R180863 : Reach 180863 := rs (se 1 (by rfl) ⟨135647, by rfl⟩) R271295
theorem R385003 : Reach 385003 := rs (se 1 (by rfl) ⟨288752, by rfl⟩) R577505
theorem R122951 : Reach 122951 := rs (se 1 (by rfl) ⟨92213, by rfl⟩) R184427
theorem R358391 : Reach 358391 := rs (se 1 (by rfl) ⟨268793, by rfl⟩) R537587
theorem R395489 : Reach 395489 := rs (se 2 (by rfl) ⟨148308, by rfl⟩) R296617
theorem R955709 : Reach 955709 := rs (se 3 (by rfl) ⟨179195, by rfl⟩) R358391
theorem R74991 : Reach 74991 := rs (se 1 (by rfl) ⟨56243, by rfl⟩) R112487
theorem R376811 : Reach 376811 := rs (se 1 (by rfl) ⟨282608, by rfl⟩) R565217
theorem R81967 : Reach 81967 := rs (se 1 (by rfl) ⟨61475, by rfl⟩) R122951
theorem R513337 : Reach 513337 := rs (se 2 (by rfl) ⟨192501, by rfl⟩) R385003
theorem R120575 : Reach 120575 := rs (se 1 (by rfl) ⟨90431, by rfl⟩) R180863
theorem R1794311 : Reach 1794311 := rs (se 1 (by rfl) ⟨1345733, by rfl⟩) R2691467
theorem R1054637 : Reach 1054637 := rs (se 3 (by rfl) ⟨197744, by rfl⟩) R395489
theorem R109289 : Reach 109289 := rs (se 2 (by rfl) ⟨40983, by rfl⟩) R81967
theorem R637139 : Reach 637139 := rs (se 1 (by rfl) ⟨477854, by rfl⟩) R955709
theorem R80383 : Reach 80383 := rs (se 1 (by rfl) ⟨60287, by rfl⟩) R120575
theorem R1196207 : Reach 1196207 := rs (se 1 (by rfl) ⟨897155, by rfl⟩) R1794311
theorem R251207 : Reach 251207 := rs (se 1 (by rfl) ⟨188405, by rfl⟩) R376811
theorem R684449 : Reach 684449 := rs (se 2 (by rfl) ⟨256668, by rfl⟩) R513337
theorem R167471 : Reach 167471 := rs (se 1 (by rfl) ⟨125603, by rfl⟩) R251207
theorem R72859 : Reach 72859 := rs (se 1 (by rfl) ⟨54644, by rfl⟩) R109289
theorem R107177 : Reach 107177 := rs (se 2 (by rfl) ⟨40191, by rfl⟩) R80383
theorem R797471 : Reach 797471 := rs (se 1 (by rfl) ⟨598103, by rfl⟩) R1196207
theorem R703091 : Reach 703091 := rs (se 1 (by rfl) ⟨527318, by rfl⟩) R1054637
theorem R456299 : Reach 456299 := rs (se 1 (by rfl) ⟨342224, by rfl⟩) R684449
theorem R424759 : Reach 424759 := rs (se 1 (by rfl) ⟨318569, by rfl⟩) R637139
theorem R71451 : Reach 71451 := rs (se 1 (by rfl) ⟨53588, by rfl⟩) R107177
theorem R1874909 : Reach 1874909 := rs (se 3 (by rfl) ⟨351545, by rfl⟩) R703091
theorem R531647 : Reach 531647 := rs (se 1 (by rfl) ⟨398735, by rfl⟩) R797471
theorem R304199 : Reach 304199 := rs (se 1 (by rfl) ⟨228149, by rfl⟩) R456299
theorem R566345 : Reach 566345 := rs (se 2 (by rfl) ⟨212379, by rfl⟩) R424759
theorem R111647 : Reach 111647 := rs (se 1 (by rfl) ⟨83735, by rfl⟩) R167471
theorem R1249939 : Reach 1249939 := rs (se 1 (by rfl) ⟨937454, by rfl⟩) R1874909
theorem R202799 : Reach 202799 := rs (se 1 (by rfl) ⟨152099, by rfl⟩) R304199
theorem R74431 : Reach 74431 := rs (se 1 (by rfl) ⟨55823, by rfl⟩) R111647
theorem R377563 : Reach 377563 := rs (se 1 (by rfl) ⟨283172, by rfl⟩) R566345
theorem R354431 : Reach 354431 := rs (se 1 (by rfl) ⟨265823, by rfl⟩) R531647
theorem R135199 : Reach 135199 := rs (se 1 (by rfl) ⟨101399, by rfl⟩) R202799
theorem R236287 : Reach 236287 := rs (se 1 (by rfl) ⟨177215, by rfl⟩) R354431
theorem R503417 : Reach 503417 := rs (se 2 (by rfl) ⟨188781, by rfl⟩) R377563
theorem R1666585 : Reach 1666585 := rs (se 2 (by rfl) ⟨624969, by rfl⟩) R1249939
theorem R335611 : Reach 335611 := rs (se 1 (by rfl) ⟨251708, by rfl⟩) R503417
theorem R180265 : Reach 180265 := rs (se 2 (by rfl) ⟨67599, by rfl⟩) R135199
theorem R315049 : Reach 315049 := rs (se 2 (by rfl) ⟨118143, by rfl⟩) R236287
theorem R2222113 : Reach 2222113 := rs (se 2 (by rfl) ⟨833292, by rfl⟩) R1666585
theorem R240353 : Reach 240353 := rs (se 2 (by rfl) ⟨90132, by rfl⟩) R180265
theorem R2962817 : Reach 2962817 := rs (se 2 (by rfl) ⟨1111056, by rfl⟩) R2222113
theorem R447481 : Reach 447481 := rs (se 2 (by rfl) ⟨167805, by rfl⟩) R335611
theorem R420065 : Reach 420065 := rs (se 2 (by rfl) ⟨157524, by rfl⟩) R315049
theorem R596641 : Reach 596641 := rs (se 2 (by rfl) ⟨223740, by rfl⟩) R447481
theorem R1975211 : Reach 1975211 := rs (se 1 (by rfl) ⟨1481408, by rfl⟩) R2962817
theorem R280043 : Reach 280043 := rs (se 1 (by rfl) ⟨210032, by rfl⟩) R420065
theorem R160235 : Reach 160235 := rs (se 1 (by rfl) ⟨120176, by rfl⟩) R240353
theorem R1316807 : Reach 1316807 := rs (se 1 (by rfl) ⟨987605, by rfl⟩) R1975211
theorem R106823 : Reach 106823 := rs (se 1 (by rfl) ⟨80117, by rfl⟩) R160235
theorem R795521 : Reach 795521 := rs (se 2 (by rfl) ⟨298320, by rfl⟩) R596641
theorem R186695 : Reach 186695 := rs (se 1 (by rfl) ⟨140021, by rfl⟩) R280043
theorem R71215 : Reach 71215 := rs (se 1 (by rfl) ⟨53411, by rfl⟩) R106823
theorem R2121389 : Reach 2121389 := rs (se 3 (by rfl) ⟨397760, by rfl⟩) R795521
theorem R877871 : Reach 877871 := rs (se 1 (by rfl) ⟨658403, by rfl⟩) R1316807
theorem R124463 : Reach 124463 := rs (se 1 (by rfl) ⟨93347, by rfl⟩) R186695
theorem R1414259 : Reach 1414259 := rs (se 1 (by rfl) ⟨1060694, by rfl⟩) R2121389
theorem R82975 : Reach 82975 := rs (se 1 (by rfl) ⟨62231, by rfl⟩) R124463
theorem R585247 : Reach 585247 := rs (se 1 (by rfl) ⟨438935, by rfl⟩) R877871
theorem R110633 : Reach 110633 := rs (se 2 (by rfl) ⟨41487, by rfl⟩) R82975
theorem R942839 : Reach 942839 := rs (se 1 (by rfl) ⟨707129, by rfl⟩) R1414259
theorem R780329 : Reach 780329 := rs (se 2 (by rfl) ⟨292623, by rfl⟩) R585247
theorem R628559 : Reach 628559 := rs (se 1 (by rfl) ⟨471419, by rfl⟩) R942839
theorem R73755 : Reach 73755 := rs (se 1 (by rfl) ⟨55316, by rfl⟩) R110633
theorem R520219 : Reach 520219 := rs (se 1 (by rfl) ⟨390164, by rfl⟩) R780329
theorem R693625 : Reach 693625 := rs (se 2 (by rfl) ⟨260109, by rfl⟩) R520219
theorem R419039 : Reach 419039 := rs (se 1 (by rfl) ⟨314279, by rfl⟩) R628559
theorem R924833 : Reach 924833 := rs (se 2 (by rfl) ⟨346812, by rfl⟩) R693625
theorem R279359 : Reach 279359 := rs (se 1 (by rfl) ⟨209519, by rfl⟩) R419039
theorem R186239 : Reach 186239 := rs (se 1 (by rfl) ⟨139679, by rfl⟩) R279359
theorem R616555 : Reach 616555 := rs (se 1 (by rfl) ⟨462416, by rfl⟩) R924833
theorem R822073 : Reach 822073 := rs (se 2 (by rfl) ⟨308277, by rfl⟩) R616555
theorem R124159 : Reach 124159 := rs (se 1 (by rfl) ⟨93119, by rfl⟩) R186239
theorem R165545 : Reach 165545 := rs (se 2 (by rfl) ⟨62079, by rfl⟩) R124159
theorem R1096097 : Reach 1096097 := rs (se 2 (by rfl) ⟨411036, by rfl⟩) R822073
theorem R110363 : Reach 110363 := rs (se 1 (by rfl) ⟨82772, by rfl⟩) R165545
theorem R11691701 : Reach 11691701 := rs (se 5 (by rfl) ⟨548048, by rfl⟩) R1096097
theorem R73575 : Reach 73575 := rs (se 1 (by rfl) ⟨55181, by rfl⟩) R110363
theorem R7794467 : Reach 7794467 := rs (se 1 (by rfl) ⟨5845850, by rfl⟩) R11691701
theorem R5196311 : Reach 5196311 := rs (se 1 (by rfl) ⟨3897233, by rfl⟩) R7794467
theorem R3464207 : Reach 3464207 := rs (se 1 (by rfl) ⟨2598155, by rfl⟩) R5196311
theorem R2309471 : Reach 2309471 := rs (se 1 (by rfl) ⟨1732103, by rfl⟩) R3464207
theorem R1539647 : Reach 1539647 := rs (se 1 (by rfl) ⟨1154735, by rfl⟩) R2309471
theorem R1026431 : Reach 1026431 := rs (se 1 (by rfl) ⟨769823, by rfl⟩) R1539647
theorem R684287 : Reach 684287 := rs (se 1 (by rfl) ⟨513215, by rfl⟩) R1026431
theorem R456191 : Reach 456191 := rs (se 1 (by rfl) ⟨342143, by rfl⟩) R684287
theorem R304127 : Reach 304127 := rs (se 1 (by rfl) ⟨228095, by rfl⟩) R456191
theorem R202751 : Reach 202751 := rs (se 1 (by rfl) ⟨152063, by rfl⟩) R304127
theorem R135167 : Reach 135167 := rs (se 1 (by rfl) ⟨101375, by rfl⟩) R202751
theorem R360445 : Reach 360445 := rs (se 3 (by rfl) ⟨67583, by rfl⟩) R135167
theorem R480593 : Reach 480593 := rs (se 2 (by rfl) ⟨180222, by rfl⟩) R360445
theorem R1281581 : Reach 1281581 := rs (se 3 (by rfl) ⟨240296, by rfl⟩) R480593
theorem R854387 : Reach 854387 := rs (se 1 (by rfl) ⟨640790, by rfl⟩) R1281581
theorem R569591 : Reach 569591 := rs (se 1 (by rfl) ⟨427193, by rfl⟩) R854387
theorem R379727 : Reach 379727 := rs (se 1 (by rfl) ⟨284795, by rfl⟩) R569591
theorem R253151 : Reach 253151 := rs (se 1 (by rfl) ⟨189863, by rfl⟩) R379727
theorem R168767 : Reach 168767 := rs (se 1 (by rfl) ⟨126575, by rfl⟩) R253151
theorem R112511 : Reach 112511 := rs (se 1 (by rfl) ⟨84383, by rfl⟩) R168767
theorem R75007 : Reach 75007 := rs (se 1 (by rfl) ⟨56255, by rfl⟩) R112511

theorem C0 (j : ℕ) (h1 : 35562 ≤ j) (h2 : j ≤ 36261) : Reach (2 * j + 1) := by
  interval_cases j
  · exact R71125
  · exact R71127
  · exact R71129
  · exact R71131
  · exact R71133
  · exact R71135
  · exact R71137
  · exact R71139
  · exact R71141
  · exact R71143
  · exact R71145
  · exact R71147
  · exact R71149
  · exact R71151
  · exact R71153
  · exact R71155
  · exact R71157
  · exact R71159
  · exact R71161
  · exact R71163
  · exact R71165
  · exact R71167
  · exact R71169
  · exact R71171
  · exact R71173
  · exact R71175
  · exact R71177
  · exact R71179
  · exact R71181
  · exact R71183
  · exact R71185
  · exact R71187
  · exact R71189
  · exact R71191
  · exact R71193
  · exact R71195
  · exact R71197
  · exact R71199
  · exact R71201
  · exact R71203
  · exact R71205
  · exact R71207
  · exact R71209
  · exact R71211
  · exact R71213
  · exact R71215
  · exact R71217
  · exact R71219
  · exact R71221
  · exact R71223
  · exact R71225
  · exact R71227
  · exact R71229
  · exact R71231
  · exact R71233
  · exact R71235
  · exact R71237
  · exact R71239
  · exact R71241
  · exact R71243
  · exact R71245
  · exact R71247
  · exact R71249
  · exact R71251
  · exact R71253
  · exact R71255
  · exact R71257
  · exact R71259
  · exact R71261
  · exact R71263
  · exact R71265
  · exact R71267
  · exact R71269
  · exact R71271
  · exact R71273
  · exact R71275
  · exact R71277
  · exact R71279
  · exact R71281
  · exact R71283
  · exact R71285
  · exact R71287
  · exact R71289
  · exact R71291
  · exact R71293
  · exact R71295
  · exact R71297
  · exact R71299
  · exact R71301
  · exact R71303
  · exact R71305
  · exact R71307
  · exact R71309
  · exact R71311
  · exact R71313
  · exact R71315
  · exact R71317
  · exact R71319
  · exact R71321
  · exact R71323
  · exact R71325
  · exact R71327
  · exact R71329
  · exact R71331
  · exact R71333
  · exact R71335
  · exact R71337
  · exact R71339
  · exact R71341
  · exact R71343
  · exact R71345
  · exact R71347
  · exact R71349
  · exact R71351
  · exact R71353
  · exact R71355
  · exact R71357
  · exact R71359
  · exact R71361
  · exact R71363
  · exact R71365
  · exact R71367
  · exact R71369
  · exact R71371
  · exact R71373
  · exact R71375
  · exact R71377
  · exact R71379
  · exact R71381
  · exact R71383
  · exact R71385
  · exact R71387
  · exact R71389
  · exact R71391
  · exact R71393
  · exact R71395
  · exact R71397
  · exact R71399
  · exact R71401
  · exact R71403
  · exact R71405
  · exact R71407
  · exact R71409
  · exact R71411
  · exact R71413
  · exact R71415
  · exact R71417
  · exact R71419
  · exact R71421
  · exact R71423
  · exact R71425
  · exact R71427
  · exact R71429
  · exact R71431
  · exact R71433
  · exact R71435
  · exact R71437
  · exact R71439
  · exact R71441
  · exact R71443
  · exact R71445
  · exact R71447
  · exact R71449
  · exact R71451
  · exact R71453
  · exact R71455
  · exact R71457
  · exact R71459
  · exact R71461
  · exact R71463
  · exact R71465
  · exact R71467
  · exact R71469
  · exact R71471
  · exact R71473
  · exact R71475
  · exact R71477
  · exact R71479
  · exact R71481
  · exact R71483
  · exact R71485
  · exact R71487
  · exact R71489
  · exact R71491
  · exact R71493
  · exact R71495
  · exact R71497
  · exact R71499
  · exact R71501
  · exact R71503
  · exact R71505
  · exact R71507
  · exact R71509
  · exact R71511
  · exact R71513
  · exact R71515
  · exact R71517
  · exact R71519
  · exact R71521
  · exact R71523
  · exact R71525
  · exact R71527
  · exact R71529
  · exact R71531
  · exact R71533
  · exact R71535
  · exact R71537
  · exact R71539
  · exact R71541
  · exact R71543
  · exact R71545
  · exact R71547
  · exact R71549
  · exact R71551
  · exact R71553
  · exact R71555
  · exact R71557
  · exact R71559
  · exact R71561
  · exact R71563
  · exact R71565
  · exact R71567
  · exact R71569
  · exact R71571
  · exact R71573
  · exact R71575
  · exact R71577
  · exact R71579
  · exact R71581
  · exact R71583
  · exact R71585
  · exact R71587
  · exact R71589
  · exact R71591
  · exact R71593
  · exact R71595
  · exact R71597
  · exact R71599
  · exact R71601
  · exact R71603
  · exact R71605
  · exact R71607
  · exact R71609
  · exact R71611
  · exact R71613
  · exact R71615
  · exact R71617
  · exact R71619
  · exact R71621
  · exact R71623
  · exact R71625
  · exact R71627
  · exact R71629
  · exact R71631
  · exact R71633
  · exact R71635
  · exact R71637
  · exact R71639
  · exact R71641
  · exact R71643
  · exact R71645
  · exact R71647
  · exact R71649
  · exact R71651
  · exact R71653
  · exact R71655
  · exact R71657
  · exact R71659
  · exact R71661
  · exact R71663
  · exact R71665
  · exact R71667
  · exact R71669
  · exact R71671
  · exact R71673
  · exact R71675
  · exact R71677
  · exact R71679
  · exact R71681
  · exact R71683
  · exact R71685
  · exact R71687
  · exact R71689
  · exact R71691
  · exact R71693
  · exact R71695
  · exact R71697
  · exact R71699
  · exact R71701
  · exact R71703
  · exact R71705
  · exact R71707
  · exact R71709
  · exact R71711
  · exact R71713
  · exact R71715
  · exact R71717
  · exact R71719
  · exact R71721
  · exact R71723
  · exact R71725
  · exact R71727
  · exact R71729
  · exact R71731
  · exact R71733
  · exact R71735
  · exact R71737
  · exact R71739
  · exact R71741
  · exact R71743
  · exact R71745
  · exact R71747
  · exact R71749
  · exact R71751
  · exact R71753
  · exact R71755
  · exact R71757
  · exact R71759
  · exact R71761
  · exact R71763
  · exact R71765
  · exact R71767
  · exact R71769
  · exact R71771
  · exact R71773
  · exact R71775
  · exact R71777
  · exact R71779
  · exact R71781
  · exact R71783
  · exact R71785
  · exact R71787
  · exact R71789
  · exact R71791
  · exact R71793
  · exact R71795
  · exact R71797
  · exact R71799
  · exact R71801
  · exact R71803
  · exact R71805
  · exact R71807
  · exact R71809
  · exact R71811
  · exact R71813
  · exact R71815
  · exact R71817
  · exact R71819
  · exact R71821
  · exact R71823
  · exact R71825
  · exact R71827
  · exact R71829
  · exact R71831
  · exact R71833
  · exact R71835
  · exact R71837
  · exact R71839
  · exact R71841
  · exact R71843
  · exact R71845
  · exact R71847
  · exact R71849
  · exact R71851
  · exact R71853
  · exact R71855
  · exact R71857
  · exact R71859
  · exact R71861
  · exact R71863
  · exact R71865
  · exact R71867
  · exact R71869
  · exact R71871
  · exact R71873
  · exact R71875
  · exact R71877
  · exact R71879
  · exact R71881
  · exact R71883
  · exact R71885
  · exact R71887
  · exact R71889
  · exact R71891
  · exact R71893
  · exact R71895
  · exact R71897
  · exact R71899
  · exact R71901
  · exact R71903
  · exact R71905
  · exact R71907
  · exact R71909
  · exact R71911
  · exact R71913
  · exact R71915
  · exact R71917
  · exact R71919
  · exact R71921
  · exact R71923
  · exact R71925
  · exact R71927
  · exact R71929
  · exact R71931
  · exact R71933
  · exact R71935
  · exact R71937
  · exact R71939
  · exact R71941
  · exact R71943
  · exact R71945
  · exact R71947
  · exact R71949
  · exact R71951
  · exact R71953
  · exact R71955
  · exact R71957
  · exact R71959
  · exact R71961
  · exact R71963
  · exact R71965
  · exact R71967
  · exact R71969
  · exact R71971
  · exact R71973
  · exact R71975
  · exact R71977
  · exact R71979
  · exact R71981
  · exact R71983
  · exact R71985
  · exact R71987
  · exact R71989
  · exact R71991
  · exact R71993
  · exact R71995
  · exact R71997
  · exact R71999
  · exact R72001
  · exact R72003
  · exact R72005
  · exact R72007
  · exact R72009
  · exact R72011
  · exact R72013
  · exact R72015
  · exact R72017
  · exact R72019
  · exact R72021
  · exact R72023
  · exact R72025
  · exact R72027
  · exact R72029
  · exact R72031
  · exact R72033
  · exact R72035
  · exact R72037
  · exact R72039
  · exact R72041
  · exact R72043
  · exact R72045
  · exact R72047
  · exact R72049
  · exact R72051
  · exact R72053
  · exact R72055
  · exact R72057
  · exact R72059
  · exact R72061
  · exact R72063
  · exact R72065
  · exact R72067
  · exact R72069
  · exact R72071
  · exact R72073
  · exact R72075
  · exact R72077
  · exact R72079
  · exact R72081
  · exact R72083
  · exact R72085
  · exact R72087
  · exact R72089
  · exact R72091
  · exact R72093
  · exact R72095
  · exact R72097
  · exact R72099
  · exact R72101
  · exact R72103
  · exact R72105
  · exact R72107
  · exact R72109
  · exact R72111
  · exact R72113
  · exact R72115
  · exact R72117
  · exact R72119
  · exact R72121
  · exact R72123
  · exact R72125
  · exact R72127
  · exact R72129
  · exact R72131
  · exact R72133
  · exact R72135
  · exact R72137
  · exact R72139
  · exact R72141
  · exact R72143
  · exact R72145
  · exact R72147
  · exact R72149
  · exact R72151
  · exact R72153
  · exact R72155
  · exact R72157
  · exact R72159
  · exact R72161
  · exact R72163
  · exact R72165
  · exact R72167
  · exact R72169
  · exact R72171
  · exact R72173
  · exact R72175
  · exact R72177
  · exact R72179
  · exact R72181
  · exact R72183
  · exact R72185
  · exact R72187
  · exact R72189
  · exact R72191
  · exact R72193
  · exact R72195
  · exact R72197
  · exact R72199
  · exact R72201
  · exact R72203
  · exact R72205
  · exact R72207
  · exact R72209
  · exact R72211
  · exact R72213
  · exact R72215
  · exact R72217
  · exact R72219
  · exact R72221
  · exact R72223
  · exact R72225
  · exact R72227
  · exact R72229
  · exact R72231
  · exact R72233
  · exact R72235
  · exact R72237
  · exact R72239
  · exact R72241
  · exact R72243
  · exact R72245
  · exact R72247
  · exact R72249
  · exact R72251
  · exact R72253
  · exact R72255
  · exact R72257
  · exact R72259
  · exact R72261
  · exact R72263
  · exact R72265
  · exact R72267
  · exact R72269
  · exact R72271
  · exact R72273
  · exact R72275
  · exact R72277
  · exact R72279
  · exact R72281
  · exact R72283
  · exact R72285
  · exact R72287
  · exact R72289
  · exact R72291
  · exact R72293
  · exact R72295
  · exact R72297
  · exact R72299
  · exact R72301
  · exact R72303
  · exact R72305
  · exact R72307
  · exact R72309
  · exact R72311
  · exact R72313
  · exact R72315
  · exact R72317
  · exact R72319
  · exact R72321
  · exact R72323
  · exact R72325
  · exact R72327
  · exact R72329
  · exact R72331
  · exact R72333
  · exact R72335
  · exact R72337
  · exact R72339
  · exact R72341
  · exact R72343
  · exact R72345
  · exact R72347
  · exact R72349
  · exact R72351
  · exact R72353
  · exact R72355
  · exact R72357
  · exact R72359
  · exact R72361
  · exact R72363
  · exact R72365
  · exact R72367
  · exact R72369
  · exact R72371
  · exact R72373
  · exact R72375
  · exact R72377
  · exact R72379
  · exact R72381
  · exact R72383
  · exact R72385
  · exact R72387
  · exact R72389
  · exact R72391
  · exact R72393
  · exact R72395
  · exact R72397
  · exact R72399
  · exact R72401
  · exact R72403
  · exact R72405
  · exact R72407
  · exact R72409
  · exact R72411
  · exact R72413
  · exact R72415
  · exact R72417
  · exact R72419
  · exact R72421
  · exact R72423
  · exact R72425
  · exact R72427
  · exact R72429
  · exact R72431
  · exact R72433
  · exact R72435
  · exact R72437
  · exact R72439
  · exact R72441
  · exact R72443
  · exact R72445
  · exact R72447
  · exact R72449
  · exact R72451
  · exact R72453
  · exact R72455
  · exact R72457
  · exact R72459
  · exact R72461
  · exact R72463
  · exact R72465
  · exact R72467
  · exact R72469
  · exact R72471
  · exact R72473
  · exact R72475
  · exact R72477
  · exact R72479
  · exact R72481
  · exact R72483
  · exact R72485
  · exact R72487
  · exact R72489
  · exact R72491
  · exact R72493
  · exact R72495
  · exact R72497
  · exact R72499
  · exact R72501
  · exact R72503
  · exact R72505
  · exact R72507
  · exact R72509
  · exact R72511
  · exact R72513
  · exact R72515
  · exact R72517
  · exact R72519
  · exact R72521
  · exact R72523

theorem C1 (j : ℕ) (h1 : 36262 ≤ j) (h2 : j ≤ 36961) : Reach (2 * j + 1) := by
  interval_cases j
  · exact R72525
  · exact R72527
  · exact R72529
  · exact R72531
  · exact R72533
  · exact R72535
  · exact R72537
  · exact R72539
  · exact R72541
  · exact R72543
  · exact R72545
  · exact R72547
  · exact R72549
  · exact R72551
  · exact R72553
  · exact R72555
  · exact R72557
  · exact R72559
  · exact R72561
  · exact R72563
  · exact R72565
  · exact R72567
  · exact R72569
  · exact R72571
  · exact R72573
  · exact R72575
  · exact R72577
  · exact R72579
  · exact R72581
  · exact R72583
  · exact R72585
  · exact R72587
  · exact R72589
  · exact R72591
  · exact R72593
  · exact R72595
  · exact R72597
  · exact R72599
  · exact R72601
  · exact R72603
  · exact R72605
  · exact R72607
  · exact R72609
  · exact R72611
  · exact R72613
  · exact R72615
  · exact R72617
  · exact R72619
  · exact R72621
  · exact R72623
  · exact R72625
  · exact R72627
  · exact R72629
  · exact R72631
  · exact R72633
  · exact R72635
  · exact R72637
  · exact R72639
  · exact R72641
  · exact R72643
  · exact R72645
  · exact R72647
  · exact R72649
  · exact R72651
  · exact R72653
  · exact R72655
  · exact R72657
  · exact R72659
  · exact R72661
  · exact R72663
  · exact R72665
  · exact R72667
  · exact R72669
  · exact R72671
  · exact R72673
  · exact R72675
  · exact R72677
  · exact R72679
  · exact R72681
  · exact R72683
  · exact R72685
  · exact R72687
  · exact R72689
  · exact R72691
  · exact R72693
  · exact R72695
  · exact R72697
  · exact R72699
  · exact R72701
  · exact R72703
  · exact R72705
  · exact R72707
  · exact R72709
  · exact R72711
  · exact R72713
  · exact R72715
  · exact R72717
  · exact R72719
  · exact R72721
  · exact R72723
  · exact R72725
  · exact R72727
  · exact R72729
  · exact R72731
  · exact R72733
  · exact R72735
  · exact R72737
  · exact R72739
  · exact R72741
  · exact R72743
  · exact R72745
  · exact R72747
  · exact R72749
  · exact R72751
  · exact R72753
  · exact R72755
  · exact R72757
  · exact R72759
  · exact R72761
  · exact R72763
  · exact R72765
  · exact R72767
  · exact R72769
  · exact R72771
  · exact R72773
  · exact R72775
  · exact R72777
  · exact R72779
  · exact R72781
  · exact R72783
  · exact R72785
  · exact R72787
  · exact R72789
  · exact R72791
  · exact R72793
  · exact R72795
  · exact R72797
  · exact R72799
  · exact R72801
  · exact R72803
  · exact R72805
  · exact R72807
  · exact R72809
  · exact R72811
  · exact R72813
  · exact R72815
  · exact R72817
  · exact R72819
  · exact R72821
  · exact R72823
  · exact R72825
  · exact R72827
  · exact R72829
  · exact R72831
  · exact R72833
  · exact R72835
  · exact R72837
  · exact R72839
  · exact R72841
  · exact R72843
  · exact R72845
  · exact R72847
  · exact R72849
  · exact R72851
  · exact R72853
  · exact R72855
  · exact R72857
  · exact R72859
  · exact R72861
  · exact R72863
  · exact R72865
  · exact R72867
  · exact R72869
  · exact R72871
  · exact R72873
  · exact R72875
  · exact R72877
  · exact R72879
  · exact R72881
  · exact R72883
  · exact R72885
  · exact R72887
  · exact R72889
  · exact R72891
  · exact R72893
  · exact R72895
  · exact R72897
  · exact R72899
  · exact R72901
  · exact R72903
  · exact R72905
  · exact R72907
  · exact R72909
  · exact R72911
  · exact R72913
  · exact R72915
  · exact R72917
  · exact R72919
  · exact R72921
  · exact R72923
  · exact R72925
  · exact R72927
  · exact R72929
  · exact R72931
  · exact R72933
  · exact R72935
  · exact R72937
  · exact R72939
  · exact R72941
  · exact R72943
  · exact R72945
  · exact R72947
  · exact R72949
  · exact R72951
  · exact R72953
  · exact R72955
  · exact R72957
  · exact R72959
  · exact R72961
  · exact R72963
  · exact R72965
  · exact R72967
  · exact R72969
  · exact R72971
  · exact R72973
  · exact R72975
  · exact R72977
  · exact R72979
  · exact R72981
  · exact R72983
  · exact R72985
  · exact R72987
  · exact R72989
  · exact R72991
  · exact R72993
  · exact R72995
  · exact R72997
  · exact R72999
  · exact R73001
  · exact R73003
  · exact R73005
  · exact R73007
  · exact R73009
  · exact R73011
  · exact R73013
  · exact R73015
  · exact R73017
  · exact R73019
  · exact R73021
  · exact R73023
  · exact R73025
  · exact R73027
  · exact R73029
  · exact R73031
  · exact R73033
  · exact R73035
  · exact R73037
  · exact R73039
  · exact R73041
  · exact R73043
  · exact R73045
  · exact R73047
  · exact R73049
  · exact R73051
  · exact R73053
  · exact R73055
  · exact R73057
  · exact R73059
  · exact R73061
  · exact R73063
  · exact R73065
  · exact R73067
  · exact R73069
  · exact R73071
  · exact R73073
  · exact R73075
  · exact R73077
  · exact R73079
  · exact R73081
  · exact R73083
  · exact R73085
  · exact R73087
  · exact R73089
  · exact R73091
  · exact R73093
  · exact R73095
  · exact R73097
  · exact R73099
  · exact R73101
  · exact R73103
  · exact R73105
  · exact R73107
  · exact R73109
  · exact R73111
  · exact R73113
  · exact R73115
  · exact R73117
  · exact R73119
  · exact R73121
  · exact R73123
  · exact R73125
  · exact R73127
  · exact R73129
  · exact R73131
  · exact R73133
  · exact R73135
  · exact R73137
  · exact R73139
  · exact R73141
  · exact R73143
  · exact R73145
  · exact R73147
  · exact R73149
  · exact R73151
  · exact R73153
  · exact R73155
  · exact R73157
  · exact R73159
  · exact R73161
  · exact R73163
  · exact R73165
  · exact R73167
  · exact R73169
  · exact R73171
  · exact R73173
  · exact R73175
  · exact R73177
  · exact R73179
  · exact R73181
  · exact R73183
  · exact R73185
  · exact R73187
  · exact R73189
  · exact R73191
  · exact R73193
  · exact R73195
  · exact R73197
  · exact R73199
  · exact R73201
  · exact R73203
  · exact R73205
  · exact R73207
  · exact R73209
  · exact R73211
  · exact R73213
  · exact R73215
  · exact R73217
  · exact R73219
  · exact R73221
  · exact R73223
  · exact R73225
  · exact R73227
  · exact R73229
  · exact R73231
  · exact R73233
  · exact R73235
  · exact R73237
  · exact R73239
  · exact R73241
  · exact R73243
  · exact R73245
  · exact R73247
  · exact R73249
  · exact R73251
  · exact R73253
  · exact R73255
  · exact R73257
  · exact R73259
  · exact R73261
  · exact R73263
  · exact R73265
  · exact R73267
  · exact R73269
  · exact R73271
  · exact R73273
  · exact R73275
  · exact R73277
  · exact R73279
  · exact R73281
  · exact R73283
  · exact R73285
  · exact R73287
  · exact R73289
  · exact R73291
  · exact R73293
  · exact R73295
  · exact R73297
  · exact R73299
  · exact R73301
  · exact R73303
  · exact R73305
  · exact R73307
  · exact R73309
  · exact R73311
  · exact R73313
  · exact R73315
  · exact R73317
  · exact R73319
  · exact R73321
  · exact R73323
  · exact R73325
  · exact R73327
  · exact R73329
  · exact R73331
  · exact R73333
  · exact R73335
  · exact R73337
  · exact R73339
  · exact R73341
  · exact R73343
  · exact R73345
  · exact R73347
  · exact R73349
  · exact R73351
  · exact R73353
  · exact R73355
  · exact R73357
  · exact R73359
  · exact R73361
  · exact R73363
  · exact R73365
  · exact R73367
  · exact R73369
  · exact R73371
  · exact R73373
  · exact R73375
  · exact R73377
  · exact R73379
  · exact R73381
  · exact R73383
  · exact R73385
  · exact R73387
  · exact R73389
  · exact R73391
  · exact R73393
  · exact R73395
  · exact R73397
  · exact R73399
  · exact R73401
  · exact R73403
  · exact R73405
  · exact R73407
  · exact R73409
  · exact R73411
  · exact R73413
  · exact R73415
  · exact R73417
  · exact R73419
  · exact R73421
  · exact R73423
  · exact R73425
  · exact R73427
  · exact R73429
  · exact R73431
  · exact R73433
  · exact R73435
  · exact R73437
  · exact R73439
  · exact R73441
  · exact R73443
  · exact R73445
  · exact R73447
  · exact R73449
  · exact R73451
  · exact R73453
  · exact R73455
  · exact R73457
  · exact R73459
  · exact R73461
  · exact R73463
  · exact R73465
  · exact R73467
  · exact R73469
  · exact R73471
  · exact R73473
  · exact R73475
  · exact R73477
  · exact R73479
  · exact R73481
  · exact R73483
  · exact R73485
  · exact R73487
  · exact R73489
  · exact R73491
  · exact R73493
  · exact R73495
  · exact R73497
  · exact R73499
  · exact R73501
  · exact R73503
  · exact R73505
  · exact R73507
  · exact R73509
  · exact R73511
  · exact R73513
  · exact R73515
  · exact R73517
  · exact R73519
  · exact R73521
  · exact R73523
  · exact R73525
  · exact R73527
  · exact R73529
  · exact R73531
  · exact R73533
  · exact R73535
  · exact R73537
  · exact R73539
  · exact R73541
  · exact R73543
  · exact R73545
  · exact R73547
  · exact R73549
  · exact R73551
  · exact R73553
  · exact R73555
  · exact R73557
  · exact R73559
  · exact R73561
  · exact R73563
  · exact R73565
  · exact R73567
  · exact R73569
  · exact R73571
  · exact R73573
  · exact R73575
  · exact R73577
  · exact R73579
  · exact R73581
  · exact R73583
  · exact R73585
  · exact R73587
  · exact R73589
  · exact R73591
  · exact R73593
  · exact R73595
  · exact R73597
  · exact R73599
  · exact R73601
  · exact R73603
  · exact R73605
  · exact R73607
  · exact R73609
  · exact R73611
  · exact R73613
  · exact R73615
  · exact R73617
  · exact R73619
  · exact R73621
  · exact R73623
  · exact R73625
  · exact R73627
  · exact R73629
  · exact R73631
  · exact R73633
  · exact R73635
  · exact R73637
  · exact R73639
  · exact R73641
  · exact R73643
  · exact R73645
  · exact R73647
  · exact R73649
  · exact R73651
  · exact R73653
  · exact R73655
  · exact R73657
  · exact R73659
  · exact R73661
  · exact R73663
  · exact R73665
  · exact R73667
  · exact R73669
  · exact R73671
  · exact R73673
  · exact R73675
  · exact R73677
  · exact R73679
  · exact R73681
  · exact R73683
  · exact R73685
  · exact R73687
  · exact R73689
  · exact R73691
  · exact R73693
  · exact R73695
  · exact R73697
  · exact R73699
  · exact R73701
  · exact R73703
  · exact R73705
  · exact R73707
  · exact R73709
  · exact R73711
  · exact R73713
  · exact R73715
  · exact R73717
  · exact R73719
  · exact R73721
  · exact R73723
  · exact R73725
  · exact R73727
  · exact R73729
  · exact R73731
  · exact R73733
  · exact R73735
  · exact R73737
  · exact R73739
  · exact R73741
  · exact R73743
  · exact R73745
  · exact R73747
  · exact R73749
  · exact R73751
  · exact R73753
  · exact R73755
  · exact R73757
  · exact R73759
  · exact R73761
  · exact R73763
  · exact R73765
  · exact R73767
  · exact R73769
  · exact R73771
  · exact R73773
  · exact R73775
  · exact R73777
  · exact R73779
  · exact R73781
  · exact R73783
  · exact R73785
  · exact R73787
  · exact R73789
  · exact R73791
  · exact R73793
  · exact R73795
  · exact R73797
  · exact R73799
  · exact R73801
  · exact R73803
  · exact R73805
  · exact R73807
  · exact R73809
  · exact R73811
  · exact R73813
  · exact R73815
  · exact R73817
  · exact R73819
  · exact R73821
  · exact R73823
  · exact R73825
  · exact R73827
  · exact R73829
  · exact R73831
  · exact R73833
  · exact R73835
  · exact R73837
  · exact R73839
  · exact R73841
  · exact R73843
  · exact R73845
  · exact R73847
  · exact R73849
  · exact R73851
  · exact R73853
  · exact R73855
  · exact R73857
  · exact R73859
  · exact R73861
  · exact R73863
  · exact R73865
  · exact R73867
  · exact R73869
  · exact R73871
  · exact R73873
  · exact R73875
  · exact R73877
  · exact R73879
  · exact R73881
  · exact R73883
  · exact R73885
  · exact R73887
  · exact R73889
  · exact R73891
  · exact R73893
  · exact R73895
  · exact R73897
  · exact R73899
  · exact R73901
  · exact R73903
  · exact R73905
  · exact R73907
  · exact R73909
  · exact R73911
  · exact R73913
  · exact R73915
  · exact R73917
  · exact R73919
  · exact R73921
  · exact R73923

theorem C2 (j : ℕ) (h1 : 36962 ≤ j) (h2 : j ≤ 37562) : Reach (2 * j + 1) := by
  interval_cases j
  · exact R73925
  · exact R73927
  · exact R73929
  · exact R73931
  · exact R73933
  · exact R73935
  · exact R73937
  · exact R73939
  · exact R73941
  · exact R73943
  · exact R73945
  · exact R73947
  · exact R73949
  · exact R73951
  · exact R73953
  · exact R73955
  · exact R73957
  · exact R73959
  · exact R73961
  · exact R73963
  · exact R73965
  · exact R73967
  · exact R73969
  · exact R73971
  · exact R73973
  · exact R73975
  · exact R73977
  · exact R73979
  · exact R73981
  · exact R73983
  · exact R73985
  · exact R73987
  · exact R73989
  · exact R73991
  · exact R73993
  · exact R73995
  · exact R73997
  · exact R73999
  · exact R74001
  · exact R74003
  · exact R74005
  · exact R74007
  · exact R74009
  · exact R74011
  · exact R74013
  · exact R74015
  · exact R74017
  · exact R74019
  · exact R74021
  · exact R74023
  · exact R74025
  · exact R74027
  · exact R74029
  · exact R74031
  · exact R74033
  · exact R74035
  · exact R74037
  · exact R74039
  · exact R74041
  · exact R74043
  · exact R74045
  · exact R74047
  · exact R74049
  · exact R74051
  · exact R74053
  · exact R74055
  · exact R74057
  · exact R74059
  · exact R74061
  · exact R74063
  · exact R74065
  · exact R74067
  · exact R74069
  · exact R74071
  · exact R74073
  · exact R74075
  · exact R74077
  · exact R74079
  · exact R74081
  · exact R74083
  · exact R74085
  · exact R74087
  · exact R74089
  · exact R74091
  · exact R74093
  · exact R74095
  · exact R74097
  · exact R74099
  · exact R74101
  · exact R74103
  · exact R74105
  · exact R74107
  · exact R74109
  · exact R74111
  · exact R74113
  · exact R74115
  · exact R74117
  · exact R74119
  · exact R74121
  · exact R74123
  · exact R74125
  · exact R74127
  · exact R74129
  · exact R74131
  · exact R74133
  · exact R74135
  · exact R74137
  · exact R74139
  · exact R74141
  · exact R74143
  · exact R74145
  · exact R74147
  · exact R74149
  · exact R74151
  · exact R74153
  · exact R74155
  · exact R74157
  · exact R74159
  · exact R74161
  · exact R74163
  · exact R74165
  · exact R74167
  · exact R74169
  · exact R74171
  · exact R74173
  · exact R74175
  · exact R74177
  · exact R74179
  · exact R74181
  · exact R74183
  · exact R74185
  · exact R74187
  · exact R74189
  · exact R74191
  · exact R74193
  · exact R74195
  · exact R74197
  · exact R74199
  · exact R74201
  · exact R74203
  · exact R74205
  · exact R74207
  · exact R74209
  · exact R74211
  · exact R74213
  · exact R74215
  · exact R74217
  · exact R74219
  · exact R74221
  · exact R74223
  · exact R74225
  · exact R74227
  · exact R74229
  · exact R74231
  · exact R74233
  · exact R74235
  · exact R74237
  · exact R74239
  · exact R74241
  · exact R74243
  · exact R74245
  · exact R74247
  · exact R74249
  · exact R74251
  · exact R74253
  · exact R74255
  · exact R74257
  · exact R74259
  · exact R74261
  · exact R74263
  · exact R74265
  · exact R74267
  · exact R74269
  · exact R74271
  · exact R74273
  · exact R74275
  · exact R74277
  · exact R74279
  · exact R74281
  · exact R74283
  · exact R74285
  · exact R74287
  · exact R74289
  · exact R74291
  · exact R74293
  · exact R74295
  · exact R74297
  · exact R74299
  · exact R74301
  · exact R74303
  · exact R74305
  · exact R74307
  · exact R74309
  · exact R74311
  · exact R74313
  · exact R74315
  · exact R74317
  · exact R74319
  · exact R74321
  · exact R74323
  · exact R74325
  · exact R74327
  · exact R74329
  · exact R74331
  · exact R74333
  · exact R74335
  · exact R74337
  · exact R74339
  · exact R74341
  · exact R74343
  · exact R74345
  · exact R74347
  · exact R74349
  · exact R74351
  · exact R74353
  · exact R74355
  · exact R74357
  · exact R74359
  · exact R74361
  · exact R74363
  · exact R74365
  · exact R74367
  · exact R74369
  · exact R74371
  · exact R74373
  · exact R74375
  · exact R74377
  · exact R74379
  · exact R74381
  · exact R74383
  · exact R74385
  · exact R74387
  · exact R74389
  · exact R74391
  · exact R74393
  · exact R74395
  · exact R74397
  · exact R74399
  · exact R74401
  · exact R74403
  · exact R74405
  · exact R74407
  · exact R74409
  · exact R74411
  · exact R74413
  · exact R74415
  · exact R74417
  · exact R74419
  · exact R74421
  · exact R74423
  · exact R74425
  · exact R74427
  · exact R74429
  · exact R74431
  · exact R74433
  · exact R74435
  · exact R74437
  · exact R74439
  · exact R74441
  · exact R74443
  · exact R74445
  · exact R74447
  · exact R74449
  · exact R74451
  · exact R74453
  · exact R74455
  · exact R74457
  · exact R74459
  · exact R74461
  · exact R74463
  · exact R74465
  · exact R74467
  · exact R74469
  · exact R74471
  · exact R74473
  · exact R74475
  · exact R74477
  · exact R74479
  · exact R74481
  · exact R74483
  · exact R74485
  · exact R74487
  · exact R74489
  · exact R74491
  · exact R74493
  · exact R74495
  · exact R74497
  · exact R74499
  · exact R74501
  · exact R74503
  · exact R74505
  · exact R74507
  · exact R74509
  · exact R74511
  · exact R74513
  · exact R74515
  · exact R74517
  · exact R74519
  · exact R74521
  · exact R74523
  · exact R74525
  · exact R74527
  · exact R74529
  · exact R74531
  · exact R74533
  · exact R74535
  · exact R74537
  · exact R74539
  · exact R74541
  · exact R74543
  · exact R74545
  · exact R74547
  · exact R74549
  · exact R74551
  · exact R74553
  · exact R74555
  · exact R74557
  · exact R74559
  · exact R74561
  · exact R74563
  · exact R74565
  · exact R74567
  · exact R74569
  · exact R74571
  · exact R74573
  · exact R74575
  · exact R74577
  · exact R74579
  · exact R74581
  · exact R74583
  · exact R74585
  · exact R74587
  · exact R74589
  · exact R74591
  · exact R74593
  · exact R74595
  · exact R74597
  · exact R74599
  · exact R74601
  · exact R74603
  · exact R74605
  · exact R74607
  · exact R74609
  · exact R74611
  · exact R74613
  · exact R74615
  · exact R74617
  · exact R74619
  · exact R74621
  · exact R74623
  · exact R74625
  · exact R74627
  · exact R74629
  · exact R74631
  · exact R74633
  · exact R74635
  · exact R74637
  · exact R74639
  · exact R74641
  · exact R74643
  · exact R74645
  · exact R74647
  · exact R74649
  · exact R74651
  · exact R74653
  · exact R74655
  · exact R74657
  · exact R74659
  · exact R74661
  · exact R74663
  · exact R74665
  · exact R74667
  · exact R74669
  · exact R74671
  · exact R74673
  · exact R74675
  · exact R74677
  · exact R74679
  · exact R74681
  · exact R74683
  · exact R74685
  · exact R74687
  · exact R74689
  · exact R74691
  · exact R74693
  · exact R74695
  · exact R74697
  · exact R74699
  · exact R74701
  · exact R74703
  · exact R74705
  · exact R74707
  · exact R74709
  · exact R74711
  · exact R74713
  · exact R74715
  · exact R74717
  · exact R74719
  · exact R74721
  · exact R74723
  · exact R74725
  · exact R74727
  · exact R74729
  · exact R74731
  · exact R74733
  · exact R74735
  · exact R74737
  · exact R74739
  · exact R74741
  · exact R74743
  · exact R74745
  · exact R74747
  · exact R74749
  · exact R74751
  · exact R74753
  · exact R74755
  · exact R74757
  · exact R74759
  · exact R74761
  · exact R74763
  · exact R74765
  · exact R74767
  · exact R74769
  · exact R74771
  · exact R74773
  · exact R74775
  · exact R74777
  · exact R74779
  · exact R74781
  · exact R74783
  · exact R74785
  · exact R74787
  · exact R74789
  · exact R74791
  · exact R74793
  · exact R74795
  · exact R74797
  · exact R74799
  · exact R74801
  · exact R74803
  · exact R74805
  · exact R74807
  · exact R74809
  · exact R74811
  · exact R74813
  · exact R74815
  · exact R74817
  · exact R74819
  · exact R74821
  · exact R74823
  · exact R74825
  · exact R74827
  · exact R74829
  · exact R74831
  · exact R74833
  · exact R74835
  · exact R74837
  · exact R74839
  · exact R74841
  · exact R74843
  · exact R74845
  · exact R74847
  · exact R74849
  · exact R74851
  · exact R74853
  · exact R74855
  · exact R74857
  · exact R74859
  · exact R74861
  · exact R74863
  · exact R74865
  · exact R74867
  · exact R74869
  · exact R74871
  · exact R74873
  · exact R74875
  · exact R74877
  · exact R74879
  · exact R74881
  · exact R74883
  · exact R74885
  · exact R74887
  · exact R74889
  · exact R74891
  · exact R74893
  · exact R74895
  · exact R74897
  · exact R74899
  · exact R74901
  · exact R74903
  · exact R74905
  · exact R74907
  · exact R74909
  · exact R74911
  · exact R74913
  · exact R74915
  · exact R74917
  · exact R74919
  · exact R74921
  · exact R74923
  · exact R74925
  · exact R74927
  · exact R74929
  · exact R74931
  · exact R74933
  · exact R74935
  · exact R74937
  · exact R74939
  · exact R74941
  · exact R74943
  · exact R74945
  · exact R74947
  · exact R74949
  · exact R74951
  · exact R74953
  · exact R74955
  · exact R74957
  · exact R74959
  · exact R74961
  · exact R74963
  · exact R74965
  · exact R74967
  · exact R74969
  · exact R74971
  · exact R74973
  · exact R74975
  · exact R74977
  · exact R74979
  · exact R74981
  · exact R74983
  · exact R74985
  · exact R74987
  · exact R74989
  · exact R74991
  · exact R74993
  · exact R74995
  · exact R74997
  · exact R74999
  · exact R75001
  · exact R75003
  · exact R75005
  · exact R75007
  · exact R75009
  · exact R75011
  · exact R75013
  · exact R75015
  · exact R75017
  · exact R75019
  · exact R75021
  · exact R75023
  · exact R75025
  · exact R75027
  · exact R75029
  · exact R75031
  · exact R75033
  · exact R75035
  · exact R75037
  · exact R75039
  · exact R75041
  · exact R75043
  · exact R75045
  · exact R75047
  · exact R75049
  · exact R75051
  · exact R75053
  · exact R75055
  · exact R75057
  · exact R75059
  · exact R75061
  · exact R75063
  · exact R75065
  · exact R75067
  · exact R75069
  · exact R75071
  · exact R75073
  · exact R75075
  · exact R75077
  · exact R75079
  · exact R75081
  · exact R75083
  · exact R75085
  · exact R75087
  · exact R75089
  · exact R75091
  · exact R75093
  · exact R75095
  · exact R75097
  · exact R75099
  · exact R75101
  · exact R75103
  · exact R75105
  · exact R75107
  · exact R75109
  · exact R75111
  · exact R75113
  · exact R75115
  · exact R75117
  · exact R75119
  · exact R75121
  · exact R75123
  · exact R75125

theorem solution (m : ℕ) (hm : 0 < m) (hodd : Odd m) (hle : m ≤ 75125) :
    ∃ k : ℕ, syracuseStep^[k] m = 1 := by
  rcases Nat.lt_or_ge m 71125 with hlo | hlo
  · exact syracuse_reaches_one_below_71125 m hm hodd (by omega)
  obtain ⟨j, rfl⟩ : ∃ j, m = 2 * j + 1 := by obtain ⟨t, ht⟩ := hodd; exact ⟨t, by omega⟩
  rcases Nat.lt_or_ge j 36262 with h0 | h0
  · exact C0 j (by omega) (by omega)
  rcases Nat.lt_or_ge j 36962 with h1 | h1
  · exact C1 j (by omega) (by omega)
  exact C2 j (by omega) (by omega)
