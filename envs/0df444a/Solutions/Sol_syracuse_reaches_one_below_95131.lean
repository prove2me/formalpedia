-- Prove2me | solution 1 for syracuse_reaches_one_below_95131
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T06:50:10.440544+00:00
-- url     : https://prove2.me/submissions/7787da11-8179-4c90-894e-ce999c1a74b4

import Mathlib
import Definitions.Def_syracuseStep
import Theorems.Thm_syracuse_reaches_one_below_91130

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
theorem B (n : ℕ) (h1 : 0 < n) (h2 : Odd n) (h3 : n ≤ 91129) : Reach n :=
  syracuse_reaches_one_below_91130 n h1 h2 h3
theorem R294965 : Reach 294965 := rs (se 5 (by rfl) ⟨13826, by rfl⟩) (B 27653 (by norm_num) ⟨13826, by rfl⟩ (by norm_num))
theorem R98381 : Reach 98381 := rs (se 3 (by rfl) ⟨18446, by rfl⟩) (B 36893 (by norm_num) ⟨18446, by rfl⟩ (by norm_num))
theorem R950453 : Reach 950453 := rs (se 5 (by rfl) ⟨44552, by rfl⟩) (B 89105 (by norm_num) ⟨44552, by rfl⟩ (by norm_num))
theorem R196933 : Reach 196933 := rs (se 4 (by rfl) ⟨18462, by rfl⟩) (B 36925 (by norm_num) ⟨18462, by rfl⟩ (by norm_num))
theorem R786773 : Reach 786773 := rs (se 10 (by rfl) ⟨1152, by rfl⟩) (B 2305 (by norm_num) ⟨1152, by rfl⟩ (by norm_num))
theorem R164197 : Reach 164197 := rs (se 4 (by rfl) ⟨15393, by rfl⟩) (B 30787 (by norm_num) ⟨15393, by rfl⟩ (by norm_num))
theorem R524789 : Reach 524789 := rs (se 5 (by rfl) ⟨24599, by rfl⟩) (B 49199 (by norm_num) ⟨24599, by rfl⟩ (by norm_num))
theorem R98825 : Reach 98825 := rs (se 2 (by rfl) ⟨37059, by rfl⟩) (B 74119 (by norm_num) ⟨37059, by rfl⟩ (by norm_num))
theorem R393781 : Reach 393781 := rs (se 5 (by rfl) ⟨18458, by rfl⟩) (B 36917 (by norm_num) ⟨18458, by rfl⟩ (by norm_num))
theorem R393797 : Reach 393797 := rs (se 4 (by rfl) ⟨36918, by rfl⟩) (B 73837 (by norm_num) ⟨36918, by rfl⟩ (by norm_num))
theorem R131653 : Reach 131653 := rs (se 4 (by rfl) ⟨12342, by rfl⟩) (B 24685 (by norm_num) ⟨12342, by rfl⟩ (by norm_num))
theorem R164461 : Reach 164461 := rs (se 3 (by rfl) ⟨30836, by rfl⟩) (B 61673 (by norm_num) ⟨30836, by rfl⟩ (by norm_num))
theorem R131765 : Reach 131765 := rs (se 5 (by rfl) ⟨6176, by rfl⟩) (B 12353 (by norm_num) ⟨6176, by rfl⟩ (by norm_num))
theorem R197309 : Reach 197309 := rs (se 3 (by rfl) ⟨36995, by rfl⟩) (B 73991 (by norm_num) ⟨36995, by rfl⟩ (by norm_num))
theorem R262885 : Reach 262885 := rs (se 4 (by rfl) ⟨24645, by rfl⟩) (B 49291 (by norm_num) ⟨24645, by rfl⟩ (by norm_num))
theorem R99073 : Reach 99073 := rs (se 2 (by rfl) ⟨37152, by rfl⟩) (B 74305 (by norm_num) ⟨37152, by rfl⟩ (by norm_num))
theorem R132053 : Reach 132053 := rs (se 7 (by rfl) ⟨1547, by rfl⟩) (B 3095 (by norm_num) ⟨1547, by rfl⟩ (by norm_num))
theorem R99505 : Reach 99505 := rs (se 2 (by rfl) ⟨37314, by rfl⟩) (B 74629 (by norm_num) ⟨37314, by rfl⟩ (by norm_num))
theorem R459989 : Reach 459989 := rs (se 7 (by rfl) ⟨5390, by rfl⟩) (B 10781 (by norm_num) ⟨5390, by rfl⟩ (by norm_num))
theorem R99577 : Reach 99577 := rs (se 2 (by rfl) ⟨37341, by rfl⟩) (B 74683 (by norm_num) ⟨37341, by rfl⟩ (by norm_num))
theorem R165125 : Reach 165125 := rs (se 4 (by rfl) ⟨15480, by rfl⟩) (B 30961 (by norm_num) ⟨15480, by rfl⟩ (by norm_num))
theorem R722197 : Reach 722197 := rs (se 6 (by rfl) ⟨16926, by rfl⟩) (B 33853 (by norm_num) ⟨16926, by rfl⟩ (by norm_num))
theorem R132445 : Reach 132445 := rs (se 3 (by rfl) ⟨24833, by rfl⟩) (B 49667 (by norm_num) ⟨24833, by rfl⟩ (by norm_num))
theorem R230789 : Reach 230789 := rs (se 4 (by rfl) ⟨21636, by rfl⟩) (B 43273 (by norm_num) ⟨21636, by rfl⟩ (by norm_num))
theorem R165341 : Reach 165341 := rs (se 3 (by rfl) ⟨31001, by rfl⟩) (B 62003 (by norm_num) ⟨31001, by rfl⟩ (by norm_num))
theorem R231005 : Reach 231005 := rs (se 3 (by rfl) ⟨43313, by rfl⟩) (B 86627 (by norm_num) ⟨43313, by rfl⟩ (by norm_num))
theorem R99949 : Reach 99949 := rs (se 3 (by rfl) ⟨18740, by rfl⟩) (B 37481 (by norm_num) ⟨18740, by rfl⟩ (by norm_num))
theorem R525973 : Reach 525973 := rs (se 6 (by rfl) ⟨12327, by rfl⟩) (B 24655 (by norm_num) ⟨12327, by rfl⟩ (by norm_num))
theorem R132781 : Reach 132781 := rs (se 3 (by rfl) ⟨24896, by rfl⟩) (B 49793 (by norm_num) ⟨24896, by rfl⟩ (by norm_num))
theorem R362165 : Reach 362165 := rs (se 5 (by rfl) ⟨16976, by rfl⟩) (B 33953 (by norm_num) ⟨16976, by rfl⟩ (by norm_num))
theorem R231133 : Reach 231133 := rs (se 3 (by rfl) ⟨43337, by rfl⟩) (B 86675 (by norm_num) ⟨43337, by rfl⟩ (by norm_num))
theorem R362245 : Reach 362245 := rs (se 4 (by rfl) ⟨33960, by rfl⟩) (B 67921 (by norm_num) ⟨33960, by rfl⟩ (by norm_num))
theorem R263989 : Reach 263989 := rs (se 5 (by rfl) ⟨12374, by rfl⟩) (B 24749 (by norm_num) ⟨12374, by rfl⟩ (by norm_num))
theorem R231245 : Reach 231245 := rs (se 3 (by rfl) ⟨43358, by rfl⟩) (B 86717 (by norm_num) ⟨43358, by rfl⟩ (by norm_num))
theorem R132997 : Reach 132997 := rs (se 4 (by rfl) ⟨12468, by rfl⟩) (B 24937 (by norm_num) ⟨12468, by rfl⟩ (by norm_num))
theorem R755669 : Reach 755669 := rs (se 7 (by rfl) ⟨8855, by rfl⟩) (B 17711 (by norm_num) ⟨8855, by rfl⟩ (by norm_num))
theorem R165845 : Reach 165845 := rs (se 7 (by rfl) ⟨1943, by rfl⟩) (B 3887 (by norm_num) ⟨1943, by rfl⟩ (by norm_num))
theorem R100325 : Reach 100325 := rs (se 4 (by rfl) ⟨9405, by rfl⟩) (B 18811 (by norm_num) ⟨9405, by rfl⟩ (by norm_num))
theorem R231437 : Reach 231437 := rs (se 3 (by rfl) ⟨43394, by rfl⟩) (B 86789 (by norm_num) ⟨43394, by rfl⟩ (by norm_num))
theorem R100397 : Reach 100397 := rs (se 3 (by rfl) ⟨18824, by rfl⟩) (B 37649 (by norm_num) ⟨18824, by rfl⟩ (by norm_num))
theorem R329845 : Reach 329845 := rs (se 5 (by rfl) ⟨15461, by rfl⟩) (B 30923 (by norm_num) ⟨15461, by rfl⟩ (by norm_num))
theorem R592085 : Reach 592085 := rs (se 7 (by rfl) ⟨6938, by rfl⟩) (B 13877 (by norm_num) ⟨6938, by rfl⟩ (by norm_num))
theorem R100585 : Reach 100585 := rs (se 2 (by rfl) ⟨37719, by rfl⟩) (B 75439 (by norm_num) ⟨37719, by rfl⟩ (by norm_num))
theorem R133373 : Reach 133373 := rs (se 3 (by rfl) ⟨25007, by rfl⟩) (B 50015 (by norm_num) ⟨25007, by rfl⟩ (by norm_num))
theorem R198949 : Reach 198949 := rs (se 4 (by rfl) ⟨18651, by rfl⟩) (B 37303 (by norm_num) ⟨18651, by rfl⟩ (by norm_num))
theorem R231781 : Reach 231781 := rs (se 4 (by rfl) ⟨21729, by rfl⟩) (B 43459 (by norm_num) ⟨21729, by rfl⟩ (by norm_num))
theorem R100769 : Reach 100769 := rs (se 2 (by rfl) ⟨37788, by rfl⟩) (B 75577 (by norm_num) ⟨37788, by rfl⟩ (by norm_num))
theorem R428485 : Reach 428485 := rs (se 4 (by rfl) ⟨40170, by rfl⟩) (B 80341 (by norm_num) ⟨40170, by rfl⟩ (by norm_num))
theorem R231893 : Reach 231893 := rs (se 7 (by rfl) ⟨2717, by rfl⟩) (B 5435 (by norm_num) ⟨2717, by rfl⟩ (by norm_num))
theorem R625205 : Reach 625205 := rs (se 5 (by rfl) ⟨29306, by rfl⟩) (B 58613 (by norm_num) ⟨29306, by rfl⟩ (by norm_num))
theorem R232013 : Reach 232013 := rs (se 3 (by rfl) ⟨43502, by rfl⟩) (B 87005 (by norm_num) ⟨43502, by rfl⟩ (by norm_num))
theorem R232085 : Reach 232085 := rs (se 6 (by rfl) ⟨5439, by rfl⟩) (B 10879 (by norm_num) ⟨5439, by rfl⟩ (by norm_num))
theorem R396053 : Reach 396053 := rs (se 6 (by rfl) ⟨9282, by rfl⟩) (B 18565 (by norm_num) ⟨9282, by rfl⟩ (by norm_num))
theorem R232429 : Reach 232429 := rs (se 3 (by rfl) ⟨43580, by rfl⟩) (B 87161 (by norm_num) ⟨43580, by rfl⟩ (by norm_num))
theorem R461861 : Reach 461861 := rs (se 4 (by rfl) ⟨43299, by rfl⟩) (B 86599 (by norm_num) ⟨43299, by rfl⟩ (by norm_num))
theorem R232541 : Reach 232541 := rs (se 3 (by rfl) ⟨43601, by rfl⟩) (B 87203 (by norm_num) ⟨43601, by rfl⟩ (by norm_num))
theorem R101521 : Reach 101521 := rs (se 2 (by rfl) ⟨38070, by rfl⟩) (B 76141 (by norm_num) ⟨38070, by rfl⟩ (by norm_num))
theorem R199837 : Reach 199837 := rs (se 3 (by rfl) ⟨37469, by rfl⟩) (B 74939 (by norm_num) ⟨37469, by rfl⟩ (by norm_num))
theorem R789749 : Reach 789749 := rs (se 5 (by rfl) ⟨37019, by rfl⟩) (B 74039 (by norm_num) ⟨37019, by rfl⟩ (by norm_num))
theorem R265493 : Reach 265493 := rs (se 6 (by rfl) ⟨6222, by rfl⟩) (B 12445 (by norm_num) ⟨6222, by rfl⟩ (by norm_num))
theorem R232733 : Reach 232733 := rs (se 3 (by rfl) ⟨43637, by rfl⟩) (B 87275 (by norm_num) ⟨43637, by rfl⟩ (by norm_num))
theorem R527957 : Reach 527957 := rs (se 8 (by rfl) ⟨3093, by rfl⟩) (B 6187 (by norm_num) ⟨3093, by rfl⟩ (by norm_num))
theorem R233077 : Reach 233077 := rs (se 5 (by rfl) ⟨10925, by rfl⟩) (B 21851 (by norm_num) ⟨10925, by rfl⟩ (by norm_num))
theorem R200333 : Reach 200333 := rs (se 3 (by rfl) ⟨37562, by rfl⟩) (B 75125 (by norm_num) ⟨37562, by rfl⟩ (by norm_num))
theorem R134797 : Reach 134797 := rs (se 3 (by rfl) ⟨25274, by rfl⟩) (B 50549 (by norm_num) ⟨25274, by rfl⟩ (by norm_num))
theorem R233189 : Reach 233189 := rs (se 4 (by rfl) ⟨21861, by rfl⟩) (B 43723 (by norm_num) ⟨21861, by rfl⟩ (by norm_num))
theorem R298885 : Reach 298885 := rs (se 4 (by rfl) ⟨28020, by rfl⟩) (B 56041 (by norm_num) ⟨28020, by rfl⟩ (by norm_num))
theorem R233381 : Reach 233381 := rs (se 4 (by rfl) ⟨21879, by rfl⟩) (B 43759 (by norm_num) ⟨21879, by rfl⟩ (by norm_num))
theorem R299141 : Reach 299141 := rs (se 4 (by rfl) ⟨28044, by rfl⟩) (B 56089 (by norm_num) ⟨28044, by rfl⟩ (by norm_num))
theorem R102541 : Reach 102541 := rs (se 3 (by rfl) ⟨19226, by rfl⟩) (B 38453 (by norm_num) ⟨19226, by rfl⟩ (by norm_num))
theorem R102565 : Reach 102565 := rs (se 4 (by rfl) ⟨9615, by rfl⟩) (B 19231 (by norm_num) ⟨9615, by rfl⟩ (by norm_num))
theorem R102577 : Reach 102577 := rs (se 2 (by rfl) ⟨38466, by rfl⟩) (B 76933 (by norm_num) ⟨38466, by rfl⟩ (by norm_num))
theorem R102613 : Reach 102613 := rs (se 7 (by rfl) ⟨1202, by rfl⟩) (B 2405 (by norm_num) ⟨1202, by rfl⟩ (by norm_num))
theorem R135389 : Reach 135389 := rs (se 3 (by rfl) ⟨25385, by rfl⟩) (B 50771 (by norm_num) ⟨25385, by rfl⟩ (by norm_num))
theorem R102649 : Reach 102649 := rs (se 2 (by rfl) ⟨38493, by rfl⟩) (B 76987 (by norm_num) ⟨38493, by rfl⟩ (by norm_num))
theorem R233725 : Reach 233725 := rs (se 3 (by rfl) ⟨43823, by rfl⟩) (B 87647 (by norm_num) ⟨43823, by rfl⟩ (by norm_num))
theorem R102685 : Reach 102685 := rs (se 3 (by rfl) ⟨19253, by rfl⟩) (B 38507 (by norm_num) ⟨19253, by rfl⟩ (by norm_num))
theorem R463157 : Reach 463157 := rs (se 5 (by rfl) ⟨21710, by rfl⟩) (B 43421 (by norm_num) ⟨21710, by rfl⟩ (by norm_num))
theorem R102721 : Reach 102721 := rs (se 2 (by rfl) ⟨38520, by rfl⟩) (B 77041 (by norm_num) ⟨38520, by rfl⟩ (by norm_num))
theorem R102757 : Reach 102757 := rs (se 4 (by rfl) ⟨9633, by rfl⟩) (B 19267 (by norm_num) ⟨9633, by rfl⟩ (by norm_num))
theorem R233837 : Reach 233837 := rs (se 3 (by rfl) ⟨43844, by rfl⟩) (B 87689 (by norm_num) ⟨43844, by rfl⟩ (by norm_num))
theorem R102793 : Reach 102793 := rs (se 2 (by rfl) ⟨38547, by rfl⟩) (B 77095 (by norm_num) ⟨38547, by rfl⟩ (by norm_num))
theorem R102829 : Reach 102829 := rs (se 3 (by rfl) ⟨19280, by rfl⟩) (B 38561 (by norm_num) ⟨19280, by rfl⟩ (by norm_num))
theorem R102865 : Reach 102865 := rs (se 2 (by rfl) ⟨38574, by rfl⟩) (B 77149 (by norm_num) ⟨38574, by rfl⟩ (by norm_num))
theorem R201197 : Reach 201197 := rs (se 3 (by rfl) ⟨37724, by rfl⟩) (B 75449 (by norm_num) ⟨37724, by rfl⟩ (by norm_num))
theorem R102901 : Reach 102901 := rs (se 5 (by rfl) ⟨4823, by rfl⟩) (B 9647 (by norm_num) ⟨4823, by rfl⟩ (by norm_num))
theorem R102937 : Reach 102937 := rs (se 2 (by rfl) ⟨38601, by rfl⟩) (B 77203 (by norm_num) ⟨38601, by rfl⟩ (by norm_num))
theorem R234029 : Reach 234029 := rs (se 3 (by rfl) ⟨43880, by rfl⟩) (B 87761 (by norm_num) ⟨43880, by rfl⟩ (by norm_num))
theorem R102973 : Reach 102973 := rs (se 3 (by rfl) ⟨19307, by rfl⟩) (B 38615 (by norm_num) ⟨19307, by rfl⟩ (by norm_num))
theorem R168533 : Reach 168533 := rs (se 8 (by rfl) ⟨987, by rfl⟩) (B 1975 (by norm_num) ⟨987, by rfl⟩ (by norm_num))
theorem R103009 : Reach 103009 := rs (se 2 (by rfl) ⟨38628, by rfl⟩) (B 77257 (by norm_num) ⟨38628, by rfl⟩ (by norm_num))
theorem R201341 : Reach 201341 := rs (se 3 (by rfl) ⟨37751, by rfl⟩) (B 75503 (by norm_num) ⟨37751, by rfl⟩ (by norm_num))
theorem R103045 : Reach 103045 := rs (se 4 (by rfl) ⟨9660, by rfl⟩) (B 19321 (by norm_num) ⟨9660, by rfl⟩ (by norm_num))
theorem R103081 : Reach 103081 := rs (se 2 (by rfl) ⟨38655, by rfl⟩) (B 77311 (by norm_num) ⟨38655, by rfl⟩ (by norm_num))
theorem R103117 : Reach 103117 := rs (se 3 (by rfl) ⟨19334, by rfl⟩) (B 38669 (by norm_num) ⟨19334, by rfl⟩ (by norm_num))
theorem R103153 : Reach 103153 := rs (se 2 (by rfl) ⟨38682, by rfl⟩) (B 77365 (by norm_num) ⟨38682, by rfl⟩ (by norm_num))
theorem R103189 : Reach 103189 := rs (se 6 (by rfl) ⟨2418, by rfl⟩) (B 4837 (by norm_num) ⟨2418, by rfl⟩ (by norm_num))
theorem R1151765 : Reach 1151765 := rs (se 6 (by rfl) ⟨26994, by rfl⟩) (B 53989 (by norm_num) ⟨26994, by rfl⟩ (by norm_num))
theorem R103225 : Reach 103225 := rs (se 2 (by rfl) ⟨38709, by rfl⟩) (B 77419 (by norm_num) ⟨38709, by rfl⟩ (by norm_num))
theorem R267077 : Reach 267077 := rs (se 4 (by rfl) ⟨25038, by rfl⟩) (B 50077 (by norm_num) ⟨25038, by rfl⟩ (by norm_num))
theorem R594773 : Reach 594773 := rs (se 9 (by rfl) ⟨1742, by rfl⟩) (B 3485 (by norm_num) ⟨1742, by rfl⟩ (by norm_num))
theorem R103261 : Reach 103261 := rs (se 3 (by rfl) ⟨19361, by rfl⟩) (B 38723 (by norm_num) ⟨19361, by rfl⟩ (by norm_num))
theorem R136037 : Reach 136037 := rs (se 4 (by rfl) ⟨12753, by rfl⟩) (B 25507 (by norm_num) ⟨12753, by rfl⟩ (by norm_num))
theorem R103297 : Reach 103297 := rs (se 2 (by rfl) ⟨38736, by rfl⟩) (B 77473 (by norm_num) ⟨38736, by rfl⟩ (by norm_num))
theorem R234373 : Reach 234373 := rs (se 4 (by rfl) ⟨21972, by rfl⟩) (B 43945 (by norm_num) ⟨21972, by rfl⟩ (by norm_num))
theorem R1217429 : Reach 1217429 := rs (se 6 (by rfl) ⟨28533, by rfl⟩) (B 57067 (by norm_num) ⟨28533, by rfl⟩ (by norm_num))
theorem R103333 : Reach 103333 := rs (se 4 (by rfl) ⟨9687, by rfl⟩) (B 19375 (by norm_num) ⟨9687, by rfl⟩ (by norm_num))
theorem R103369 : Reach 103369 := rs (se 2 (by rfl) ⟨38763, by rfl⟩) (B 77527 (by norm_num) ⟨38763, by rfl⟩ (by norm_num))
theorem R1151957 : Reach 1151957 := rs (se 7 (by rfl) ⟨13499, by rfl⟩) (B 26999 (by norm_num) ⟨13499, by rfl⟩ (by norm_num))
theorem R103405 : Reach 103405 := rs (se 3 (by rfl) ⟨19388, by rfl⟩) (B 38777 (by norm_num) ⟨19388, by rfl⟩ (by norm_num))
theorem R234485 : Reach 234485 := rs (se 5 (by rfl) ⟨10991, by rfl⟩) (B 21983 (by norm_num) ⟨10991, by rfl⟩ (by norm_num))
theorem R103441 : Reach 103441 := rs (se 2 (by rfl) ⟨38790, by rfl⟩) (B 77581 (by norm_num) ⟨38790, by rfl⟩ (by norm_num))
theorem R103477 : Reach 103477 := rs (se 5 (by rfl) ⟨4850, by rfl⟩) (B 9701 (by norm_num) ⟨4850, by rfl⟩ (by norm_num))
theorem R103513 : Reach 103513 := rs (se 2 (by rfl) ⟨38817, by rfl⟩) (B 77635 (by norm_num) ⟨38817, by rfl⟩ (by norm_num))
theorem R103549 : Reach 103549 := rs (se 3 (by rfl) ⟨19415, by rfl⟩) (B 38831 (by norm_num) ⟨19415, by rfl⟩ (by norm_num))
theorem R103585 : Reach 103585 := rs (se 2 (by rfl) ⟨38844, by rfl⟩) (B 77689 (by norm_num) ⟨38844, by rfl⟩ (by norm_num))
theorem R234677 : Reach 234677 := rs (se 5 (by rfl) ⟨11000, by rfl⟩) (B 22001 (by norm_num) ⟨11000, by rfl⟩ (by norm_num))
theorem R103621 : Reach 103621 := rs (se 4 (by rfl) ⟨9714, by rfl⟩) (B 19429 (by norm_num) ⟨9714, by rfl⟩ (by norm_num))
theorem R103657 : Reach 103657 := rs (se 2 (by rfl) ⟨38871, by rfl⟩) (B 77743 (by norm_num) ⟨38871, by rfl⟩ (by norm_num))
theorem R103693 : Reach 103693 := rs (se 3 (by rfl) ⟨19442, by rfl⟩) (B 38885 (by norm_num) ⟨19442, by rfl⟩ (by norm_num))
theorem R103729 : Reach 103729 := rs (se 2 (by rfl) ⟨38898, by rfl⟩) (B 77797 (by norm_num) ⟨38898, by rfl⟩ (by norm_num))
theorem R103765 : Reach 103765 := rs (se 14 (by rfl) ⟨9, by rfl⟩) (B 19 (by norm_num) ⟨9, by rfl⟩ (by norm_num))
theorem R202085 : Reach 202085 := rs (se 4 (by rfl) ⟨18945, by rfl⟩) (B 37891 (by norm_num) ⟨18945, by rfl⟩ (by norm_num))
theorem R103801 : Reach 103801 := rs (se 2 (by rfl) ⟨38925, by rfl⟩) (B 77851 (by norm_num) ⟨38925, by rfl⟩ (by norm_num))
theorem R103837 : Reach 103837 := rs (se 3 (by rfl) ⟨19469, by rfl⟩) (B 38939 (by norm_num) ⟨19469, by rfl⟩ (by norm_num))
theorem R103873 : Reach 103873 := rs (se 2 (by rfl) ⟨38952, by rfl⟩) (B 77905 (by norm_num) ⟨38952, by rfl⟩ (by norm_num))
theorem R103909 : Reach 103909 := rs (se 4 (by rfl) ⟨9741, by rfl⟩) (B 19483 (by norm_num) ⟨9741, by rfl⟩ (by norm_num))
theorem R267749 : Reach 267749 := rs (se 4 (by rfl) ⟨25101, by rfl⟩) (B 50203 (by norm_num) ⟨25101, by rfl⟩ (by norm_num))
theorem R136709 : Reach 136709 := rs (se 4 (by rfl) ⟨12816, by rfl⟩) (B 25633 (by norm_num) ⟨12816, by rfl⟩ (by norm_num))
theorem R103945 : Reach 103945 := rs (se 2 (by rfl) ⟨38979, by rfl⟩) (B 77959 (by norm_num) ⟨38979, by rfl⟩ (by norm_num))
theorem R235021 : Reach 235021 := rs (se 3 (by rfl) ⟨44066, by rfl⟩) (B 88133 (by norm_num) ⟨44066, by rfl⟩ (by norm_num))
theorem R136733 : Reach 136733 := rs (se 3 (by rfl) ⟨25637, by rfl⟩) (B 51275 (by norm_num) ⟨25637, by rfl⟩ (by norm_num))
theorem R103981 : Reach 103981 := rs (se 3 (by rfl) ⟨19496, by rfl⟩) (B 38993 (by norm_num) ⟨19496, by rfl⟩ (by norm_num))
theorem R136757 : Reach 136757 := rs (se 5 (by rfl) ⟨6410, by rfl⟩) (B 12821 (by norm_num) ⟨6410, by rfl⟩ (by norm_num))
theorem R464453 : Reach 464453 := rs (se 4 (by rfl) ⟨43542, by rfl⟩) (B 87085 (by norm_num) ⟨43542, by rfl⟩ (by norm_num))
theorem R136781 : Reach 136781 := rs (se 3 (by rfl) ⟨25646, by rfl⟩) (B 51293 (by norm_num) ⟨25646, by rfl⟩ (by norm_num))
theorem R104017 : Reach 104017 := rs (se 2 (by rfl) ⟨39006, by rfl⟩) (B 78013 (by norm_num) ⟨39006, by rfl⟩ (by norm_num))
theorem R136805 : Reach 136805 := rs (se 4 (by rfl) ⟨12825, by rfl⟩) (B 25651 (by norm_num) ⟨12825, by rfl⟩ (by norm_num))
theorem R104053 : Reach 104053 := rs (se 5 (by rfl) ⟨4877, by rfl⟩) (B 9755 (by norm_num) ⟨4877, by rfl⟩ (by norm_num))
theorem R136829 : Reach 136829 := rs (se 3 (by rfl) ⟨25655, by rfl⟩) (B 51311 (by norm_num) ⟨25655, by rfl⟩ (by norm_num))
theorem R235133 : Reach 235133 := rs (se 3 (by rfl) ⟨44087, by rfl⟩) (B 88175 (by norm_num) ⟨44087, by rfl⟩ (by norm_num))
theorem R136853 : Reach 136853 := rs (se 6 (by rfl) ⟨3207, by rfl⟩) (B 6415 (by norm_num) ⟨3207, by rfl⟩ (by norm_num))
theorem R104089 : Reach 104089 := rs (se 2 (by rfl) ⟨39033, by rfl⟩) (B 78067 (by norm_num) ⟨39033, by rfl⟩ (by norm_num))
theorem R136877 : Reach 136877 := rs (se 3 (by rfl) ⟨25664, by rfl⟩) (B 51329 (by norm_num) ⟨25664, by rfl⟩ (by norm_num))
theorem R104125 : Reach 104125 := rs (se 3 (by rfl) ⟨19523, by rfl⟩) (B 39047 (by norm_num) ⟨19523, by rfl⟩ (by norm_num))
theorem R136901 : Reach 136901 := rs (se 4 (by rfl) ⟨12834, by rfl⟩) (B 25669 (by norm_num) ⟨12834, by rfl⟩ (by norm_num))
theorem R136925 : Reach 136925 := rs (se 3 (by rfl) ⟨25673, by rfl⟩) (B 51347 (by norm_num) ⟨25673, by rfl⟩ (by norm_num))
theorem R104161 : Reach 104161 := rs (se 2 (by rfl) ⟨39060, by rfl⟩) (B 78121 (by norm_num) ⟨39060, by rfl⟩ (by norm_num))
theorem R136949 : Reach 136949 := rs (se 5 (by rfl) ⟨6419, by rfl⟩) (B 12839 (by norm_num) ⟨6419, by rfl⟩ (by norm_num))
theorem R530165 : Reach 530165 := rs (se 5 (by rfl) ⟨24851, by rfl⟩) (B 49703 (by norm_num) ⟨24851, by rfl⟩ (by norm_num))
theorem R104197 : Reach 104197 := rs (se 4 (by rfl) ⟨9768, by rfl⟩) (B 19537 (by norm_num) ⟨9768, by rfl⟩ (by norm_num))
theorem R136973 : Reach 136973 := rs (se 3 (by rfl) ⟨25682, by rfl⟩) (B 51365 (by norm_num) ⟨25682, by rfl⟩ (by norm_num))
theorem R136997 : Reach 136997 := rs (se 4 (by rfl) ⟨12843, by rfl⟩) (B 25687 (by norm_num) ⟨12843, by rfl⟩ (by norm_num))
theorem R104233 : Reach 104233 := rs (se 2 (by rfl) ⟨39087, by rfl⟩) (B 78175 (by norm_num) ⟨39087, by rfl⟩ (by norm_num))
theorem R137021 : Reach 137021 := rs (se 3 (by rfl) ⟨25691, by rfl⟩) (B 51383 (by norm_num) ⟨25691, by rfl⟩ (by norm_num))
theorem R235325 : Reach 235325 := rs (se 3 (by rfl) ⟨44123, by rfl⟩) (B 88247 (by norm_num) ⟨44123, by rfl⟩ (by norm_num))
theorem R104269 : Reach 104269 := rs (se 3 (by rfl) ⟨19550, by rfl⟩) (B 39101 (by norm_num) ⟨19550, by rfl⟩ (by norm_num))
theorem R137045 : Reach 137045 := rs (se 9 (by rfl) ⟨401, by rfl⟩) (B 803 (by norm_num) ⟨401, by rfl⟩ (by norm_num))
theorem R137069 : Reach 137069 := rs (se 3 (by rfl) ⟨25700, by rfl⟩) (B 51401 (by norm_num) ⟨25700, by rfl⟩ (by norm_num))
theorem R104305 : Reach 104305 := rs (se 2 (by rfl) ⟨39114, by rfl⟩) (B 78229 (by norm_num) ⟨39114, by rfl⟩ (by norm_num))
theorem R137093 : Reach 137093 := rs (se 4 (by rfl) ⟨12852, by rfl⟩) (B 25705 (by norm_num) ⟨12852, by rfl⟩ (by norm_num))
theorem R104341 : Reach 104341 := rs (se 6 (by rfl) ⟨2445, by rfl⟩) (B 4891 (by norm_num) ⟨2445, by rfl⟩ (by norm_num))
theorem R268181 : Reach 268181 := rs (se 6 (by rfl) ⟨6285, by rfl⟩) (B 12571 (by norm_num) ⟨6285, by rfl⟩ (by norm_num))
theorem R137117 : Reach 137117 := rs (se 3 (by rfl) ⟨25709, by rfl⟩) (B 51419 (by norm_num) ⟨25709, by rfl⟩ (by norm_num))
theorem R137141 : Reach 137141 := rs (se 5 (by rfl) ⟨6428, by rfl⟩) (B 12857 (by norm_num) ⟨6428, by rfl⟩ (by norm_num))
theorem R104377 : Reach 104377 := rs (se 2 (by rfl) ⟨39141, by rfl⟩) (B 78283 (by norm_num) ⟨39141, by rfl⟩ (by norm_num))
theorem R137165 : Reach 137165 := rs (se 3 (by rfl) ⟨25718, by rfl⟩) (B 51437 (by norm_num) ⟨25718, by rfl⟩ (by norm_num))
theorem R169933 : Reach 169933 := rs (se 3 (by rfl) ⟨31862, by rfl⟩) (B 63725 (by norm_num) ⟨31862, by rfl⟩ (by norm_num))
theorem R104413 : Reach 104413 := rs (se 3 (by rfl) ⟨19577, by rfl⟩) (B 39155 (by norm_num) ⟨19577, by rfl⟩ (by norm_num))
theorem R137189 : Reach 137189 := rs (se 4 (by rfl) ⟨12861, by rfl⟩) (B 25723 (by norm_num) ⟨12861, by rfl⟩ (by norm_num))
theorem R137213 : Reach 137213 := rs (se 3 (by rfl) ⟨25727, by rfl⟩) (B 51455 (by norm_num) ⟨25727, by rfl⟩ (by norm_num))
theorem R104449 : Reach 104449 := rs (se 2 (by rfl) ⟨39168, by rfl⟩) (B 78337 (by norm_num) ⟨39168, by rfl⟩ (by norm_num))
theorem R137237 : Reach 137237 := rs (se 6 (by rfl) ⟨3216, by rfl⟩) (B 6433 (by norm_num) ⟨3216, by rfl⟩ (by norm_num))
theorem R104485 : Reach 104485 := rs (se 4 (by rfl) ⟨9795, by rfl⟩) (B 19591 (by norm_num) ⟨9795, by rfl⟩ (by norm_num))
theorem R137261 : Reach 137261 := rs (se 3 (by rfl) ⟨25736, by rfl⟩) (B 51473 (by norm_num) ⟨25736, by rfl⟩ (by norm_num))
theorem R137285 : Reach 137285 := rs (se 4 (by rfl) ⟨12870, by rfl⟩) (B 25741 (by norm_num) ⟨12870, by rfl⟩ (by norm_num))
theorem R104521 : Reach 104521 := rs (se 2 (by rfl) ⟨39195, by rfl⟩) (B 78391 (by norm_num) ⟨39195, by rfl⟩ (by norm_num))
theorem R202837 : Reach 202837 := rs (se 8 (by rfl) ⟨1188, by rfl⟩) (B 2377 (by norm_num) ⟨1188, by rfl⟩ (by norm_num))
theorem R137309 : Reach 137309 := rs (se 3 (by rfl) ⟨25745, by rfl⟩) (B 51491 (by norm_num) ⟨25745, by rfl⟩ (by norm_num))
theorem R104557 : Reach 104557 := rs (se 3 (by rfl) ⟨19604, by rfl⟩) (B 39209 (by norm_num) ⟨19604, by rfl⟩ (by norm_num))
theorem R137333 : Reach 137333 := rs (se 5 (by rfl) ⟨6437, by rfl⟩) (B 12875 (by norm_num) ⟨6437, by rfl⟩ (by norm_num))
theorem R137357 : Reach 137357 := rs (se 3 (by rfl) ⟨25754, by rfl⟩) (B 51509 (by norm_num) ⟨25754, by rfl⟩ (by norm_num))
theorem R104593 : Reach 104593 := rs (se 2 (by rfl) ⟨39222, by rfl⟩) (B 78445 (by norm_num) ⟨39222, by rfl⟩ (by norm_num))
theorem R235669 : Reach 235669 := rs (se 6 (by rfl) ⟨5523, by rfl⟩) (B 11047 (by norm_num) ⟨5523, by rfl⟩ (by norm_num))
theorem R137381 : Reach 137381 := rs (se 4 (by rfl) ⟨12879, by rfl⟩) (B 25759 (by norm_num) ⟨12879, by rfl⟩ (by norm_num))
theorem R104629 : Reach 104629 := rs (se 5 (by rfl) ⟨4904, by rfl⟩) (B 9809 (by norm_num) ⟨4904, by rfl⟩ (by norm_num))
theorem R137405 : Reach 137405 := rs (se 3 (by rfl) ⟨25763, by rfl⟩) (B 51527 (by norm_num) ⟨25763, by rfl⟩ (by norm_num))
theorem R137429 : Reach 137429 := rs (se 7 (by rfl) ⟨1610, by rfl⟩) (B 3221 (by norm_num) ⟨1610, by rfl⟩ (by norm_num))
theorem R104665 : Reach 104665 := rs (se 2 (by rfl) ⟨39249, by rfl⟩) (B 78499 (by norm_num) ⟨39249, by rfl⟩ (by norm_num))
theorem R202981 : Reach 202981 := rs (se 4 (by rfl) ⟨19029, by rfl⟩) (B 38059 (by norm_num) ⟨19029, by rfl⟩ (by norm_num))
theorem R137453 : Reach 137453 := rs (se 3 (by rfl) ⟨25772, by rfl⟩) (B 51545 (by norm_num) ⟨25772, by rfl⟩ (by norm_num))
theorem R104701 : Reach 104701 := rs (se 3 (by rfl) ⟨19631, by rfl⟩) (B 39263 (by norm_num) ⟨19631, by rfl⟩ (by norm_num))
theorem R137477 : Reach 137477 := rs (se 4 (by rfl) ⟨12888, by rfl⟩) (B 25777 (by norm_num) ⟨12888, by rfl⟩ (by norm_num))
theorem R235781 : Reach 235781 := rs (se 4 (by rfl) ⟨22104, by rfl⟩) (B 44209 (by norm_num) ⟨22104, by rfl⟩ (by norm_num))
theorem R137501 : Reach 137501 := rs (se 3 (by rfl) ⟨25781, by rfl⟩) (B 51563 (by norm_num) ⟨25781, by rfl⟩ (by norm_num))
theorem R104737 : Reach 104737 := rs (se 2 (by rfl) ⟨39276, by rfl⟩) (B 78553 (by norm_num) ⟨39276, by rfl⟩ (by norm_num))
theorem R137525 : Reach 137525 := rs (se 5 (by rfl) ⟨6446, by rfl⟩) (B 12893 (by norm_num) ⟨6446, by rfl⟩ (by norm_num))
theorem R104773 : Reach 104773 := rs (se 4 (by rfl) ⟨9822, by rfl⟩) (B 19645 (by norm_num) ⟨9822, by rfl⟩ (by norm_num))
theorem R137549 : Reach 137549 := rs (se 3 (by rfl) ⟨25790, by rfl⟩) (B 51581 (by norm_num) ⟨25790, by rfl⟩ (by norm_num))
theorem R137573 : Reach 137573 := rs (se 4 (by rfl) ⟨12897, by rfl⟩) (B 25795 (by norm_num) ⟨12897, by rfl⟩ (by norm_num))
theorem R104809 : Reach 104809 := rs (se 2 (by rfl) ⟨39303, by rfl⟩) (B 78607 (by norm_num) ⟨39303, by rfl⟩ (by norm_num))
theorem R137597 : Reach 137597 := rs (se 3 (by rfl) ⟨25799, by rfl⟩) (B 51599 (by norm_num) ⟨25799, by rfl⟩ (by norm_num))
theorem R104845 : Reach 104845 := rs (se 3 (by rfl) ⟨19658, by rfl⟩) (B 39317 (by norm_num) ⟨19658, by rfl⟩ (by norm_num))
theorem R137621 : Reach 137621 := rs (se 6 (by rfl) ⟨3225, by rfl⟩) (B 6451 (by norm_num) ⟨3225, by rfl⟩ (by norm_num))
theorem R137645 : Reach 137645 := rs (se 3 (by rfl) ⟨25808, by rfl⟩) (B 51617 (by norm_num) ⟨25808, by rfl⟩ (by norm_num))
theorem R104881 : Reach 104881 := rs (se 2 (by rfl) ⟨39330, by rfl⟩) (B 78661 (by norm_num) ⟨39330, by rfl⟩ (by norm_num))
theorem R137669 : Reach 137669 := rs (se 4 (by rfl) ⟨12906, by rfl⟩) (B 25813 (by norm_num) ⟨12906, by rfl⟩ (by norm_num))
theorem R235973 : Reach 235973 := rs (se 4 (by rfl) ⟨22122, by rfl⟩) (B 44245 (by norm_num) ⟨22122, by rfl⟩ (by norm_num))
theorem R104917 : Reach 104917 := rs (se 7 (by rfl) ⟨1229, by rfl⟩) (B 2459 (by norm_num) ⟨1229, by rfl⟩ (by norm_num))
theorem R137693 : Reach 137693 := rs (se 3 (by rfl) ⟨25817, by rfl⟩) (B 51635 (by norm_num) ⟨25817, by rfl⟩ (by norm_num))
theorem R137717 : Reach 137717 := rs (se 5 (by rfl) ⟨6455, by rfl⟩) (B 12911 (by norm_num) ⟨6455, by rfl⟩ (by norm_num))
theorem R104953 : Reach 104953 := rs (se 2 (by rfl) ⟨39357, by rfl⟩) (B 78715 (by norm_num) ⟨39357, by rfl⟩ (by norm_num))
theorem R137741 : Reach 137741 := rs (se 3 (by rfl) ⟨25826, by rfl⟩) (B 51653 (by norm_num) ⟨25826, by rfl⟩ (by norm_num))
theorem R203293 : Reach 203293 := rs (se 3 (by rfl) ⟨38117, by rfl⟩) (B 76235 (by norm_num) ⟨38117, by rfl⟩ (by norm_num))
theorem R104989 : Reach 104989 := rs (se 3 (by rfl) ⟨19685, by rfl⟩) (B 39371 (by norm_num) ⟨19685, by rfl⟩ (by norm_num))
theorem R137765 : Reach 137765 := rs (se 4 (by rfl) ⟨12915, by rfl⟩) (B 25831 (by norm_num) ⟨12915, by rfl⟩ (by norm_num))
theorem R137789 : Reach 137789 := rs (se 3 (by rfl) ⟨25835, by rfl⟩) (B 51671 (by norm_num) ⟨25835, by rfl⟩ (by norm_num))
theorem R105025 : Reach 105025 := rs (se 2 (by rfl) ⟨39384, by rfl⟩) (B 78769 (by norm_num) ⟨39384, by rfl⟩ (by norm_num))
theorem R137813 : Reach 137813 := rs (se 8 (by rfl) ⟨807, by rfl⟩) (B 1615 (by norm_num) ⟨807, by rfl⟩ (by norm_num))
theorem R105061 : Reach 105061 := rs (se 4 (by rfl) ⟨9849, by rfl⟩) (B 19699 (by norm_num) ⟨9849, by rfl⟩ (by norm_num))
theorem R137837 : Reach 137837 := rs (se 3 (by rfl) ⟨25844, by rfl⟩) (B 51689 (by norm_num) ⟨25844, by rfl⟩ (by norm_num))
theorem R137861 : Reach 137861 := rs (se 4 (by rfl) ⟨12924, by rfl⟩) (B 25849 (by norm_num) ⟨12924, by rfl⟩ (by norm_num))
theorem R268933 : Reach 268933 := rs (se 4 (by rfl) ⟨25212, by rfl⟩) (B 50425 (by norm_num) ⟨25212, by rfl⟩ (by norm_num))
theorem R105097 : Reach 105097 := rs (se 2 (by rfl) ⟨39411, by rfl⟩) (B 78823 (by norm_num) ⟨39411, by rfl⟩ (by norm_num))
theorem R137885 : Reach 137885 := rs (se 3 (by rfl) ⟨25853, by rfl⟩) (B 51707 (by norm_num) ⟨25853, by rfl⟩ (by norm_num))
theorem R105133 : Reach 105133 := rs (se 3 (by rfl) ⟨19712, by rfl⟩) (B 39425 (by norm_num) ⟨19712, by rfl⟩ (by norm_num))
theorem R137909 : Reach 137909 := rs (se 5 (by rfl) ⟨6464, by rfl⟩) (B 12929 (by norm_num) ⟨6464, by rfl⟩ (by norm_num))
theorem R137933 : Reach 137933 := rs (se 3 (by rfl) ⟨25862, by rfl⟩) (B 51725 (by norm_num) ⟨25862, by rfl⟩ (by norm_num))
theorem R105169 : Reach 105169 := rs (se 2 (by rfl) ⟨39438, by rfl⟩) (B 78877 (by norm_num) ⟨39438, by rfl⟩ (by norm_num))
theorem R400085 : Reach 400085 := rs (se 7 (by rfl) ⟨4688, by rfl⟩) (B 9377 (by norm_num) ⟨4688, by rfl⟩ (by norm_num))
theorem R137957 : Reach 137957 := rs (se 4 (by rfl) ⟨12933, by rfl⟩) (B 25867 (by norm_num) ⟨12933, by rfl⟩ (by norm_num))
theorem R105205 : Reach 105205 := rs (se 5 (by rfl) ⟨4931, by rfl⟩) (B 9863 (by norm_num) ⟨4931, by rfl⟩ (by norm_num))
theorem R170741 : Reach 170741 := rs (se 5 (by rfl) ⟨8003, by rfl⟩) (B 16007 (by norm_num) ⟨8003, by rfl⟩ (by norm_num))
theorem R137981 : Reach 137981 := rs (se 3 (by rfl) ⟨25871, by rfl⟩) (B 51743 (by norm_num) ⟨25871, by rfl⟩ (by norm_num))
theorem R138005 : Reach 138005 := rs (se 6 (by rfl) ⟨3234, by rfl⟩) (B 6469 (by norm_num) ⟨3234, by rfl⟩ (by norm_num))
theorem R105241 : Reach 105241 := rs (se 2 (by rfl) ⟨39465, by rfl⟩) (B 78931 (by norm_num) ⟨39465, by rfl⟩ (by norm_num))
theorem R236317 : Reach 236317 := rs (se 3 (by rfl) ⟨44309, by rfl⟩) (B 88619 (by norm_num) ⟨44309, by rfl⟩ (by norm_num))
theorem R138029 : Reach 138029 := rs (se 3 (by rfl) ⟨25880, by rfl⟩) (B 51761 (by norm_num) ⟨25880, by rfl⟩ (by norm_num))
theorem R105277 : Reach 105277 := rs (se 3 (by rfl) ⟨19739, by rfl⟩) (B 39479 (by norm_num) ⟨19739, by rfl⟩ (by norm_num))
theorem R138053 : Reach 138053 := rs (se 4 (by rfl) ⟨12942, by rfl⟩) (B 25885 (by norm_num) ⟨12942, by rfl⟩ (by norm_num))
theorem R465749 : Reach 465749 := rs (se 9 (by rfl) ⟨1364, by rfl⟩) (B 2729 (by norm_num) ⟨1364, by rfl⟩ (by norm_num))
theorem R301909 : Reach 301909 := rs (se 9 (by rfl) ⟨884, by rfl⟩) (B 1769 (by norm_num) ⟨884, by rfl⟩ (by norm_num))
theorem R138077 : Reach 138077 := rs (se 3 (by rfl) ⟨25889, by rfl⟩) (B 51779 (by norm_num) ⟨25889, by rfl⟩ (by norm_num))
theorem R105313 : Reach 105313 := rs (se 2 (by rfl) ⟨39492, by rfl⟩) (B 78985 (by norm_num) ⟨39492, by rfl⟩ (by norm_num))
theorem R138101 : Reach 138101 := rs (se 5 (by rfl) ⟨6473, by rfl⟩) (B 12947 (by norm_num) ⟨6473, by rfl⟩ (by norm_num))
theorem R105349 : Reach 105349 := rs (se 4 (by rfl) ⟨9876, by rfl⟩) (B 19753 (by norm_num) ⟨9876, by rfl⟩ (by norm_num))
theorem R138125 : Reach 138125 := rs (se 3 (by rfl) ⟨25898, by rfl⟩) (B 51797 (by norm_num) ⟨25898, by rfl⟩ (by norm_num))
theorem R236429 : Reach 236429 := rs (se 3 (by rfl) ⟨44330, by rfl⟩) (B 88661 (by norm_num) ⟨44330, by rfl⟩ (by norm_num))
theorem R138149 : Reach 138149 := rs (se 4 (by rfl) ⟨12951, by rfl⟩) (B 25903 (by norm_num) ⟨12951, by rfl⟩ (by norm_num))
theorem R105385 : Reach 105385 := rs (se 2 (by rfl) ⟨39519, by rfl⟩) (B 79039 (by norm_num) ⟨39519, by rfl⟩ (by norm_num))
theorem R138173 : Reach 138173 := rs (se 3 (by rfl) ⟨25907, by rfl⟩) (B 51815 (by norm_num) ⟨25907, by rfl⟩ (by norm_num))
theorem R105421 : Reach 105421 := rs (se 3 (by rfl) ⟨19766, by rfl⟩) (B 39533 (by norm_num) ⟨19766, by rfl⟩ (by norm_num))
theorem R138197 : Reach 138197 := rs (se 7 (by rfl) ⟨1619, by rfl⟩) (B 3239 (by norm_num) ⟨1619, by rfl⟩ (by norm_num))
theorem R138221 : Reach 138221 := rs (se 3 (by rfl) ⟨25916, by rfl⟩) (B 51833 (by norm_num) ⟨25916, by rfl⟩ (by norm_num))
theorem R105457 : Reach 105457 := rs (se 2 (by rfl) ⟨39546, by rfl⟩) (B 79093 (by norm_num) ⟨39546, by rfl⟩ (by norm_num))
theorem R138245 : Reach 138245 := rs (se 4 (by rfl) ⟨12960, by rfl⟩) (B 25921 (by norm_num) ⟨12960, by rfl⟩ (by norm_num))
theorem R105493 : Reach 105493 := rs (se 6 (by rfl) ⟨2472, by rfl⟩) (B 4945 (by norm_num) ⟨2472, by rfl⟩ (by norm_num))
theorem R138269 : Reach 138269 := rs (se 3 (by rfl) ⟨25925, by rfl⟩) (B 51851 (by norm_num) ⟨25925, by rfl⟩ (by norm_num))
theorem R138293 : Reach 138293 := rs (se 5 (by rfl) ⟨6482, by rfl⟩) (B 12965 (by norm_num) ⟨6482, by rfl⟩ (by norm_num))
theorem R105529 : Reach 105529 := rs (se 2 (by rfl) ⟨39573, by rfl⟩) (B 79147 (by norm_num) ⟨39573, by rfl⟩ (by norm_num))
theorem R138317 : Reach 138317 := rs (se 3 (by rfl) ⟨25934, by rfl⟩) (B 51869 (by norm_num) ⟨25934, by rfl⟩ (by norm_num))
theorem R236621 : Reach 236621 := rs (se 3 (by rfl) ⟨44366, by rfl⟩) (B 88733 (by norm_num) ⟨44366, by rfl⟩ (by norm_num))
theorem R236629 : Reach 236629 := rs (se 8 (by rfl) ⟨1386, by rfl⟩) (B 2773 (by norm_num) ⟨1386, by rfl⟩ (by norm_num))
theorem R105565 : Reach 105565 := rs (se 3 (by rfl) ⟨19793, by rfl⟩) (B 39587 (by norm_num) ⟨19793, by rfl⟩ (by norm_num))
theorem R138341 : Reach 138341 := rs (se 4 (by rfl) ⟨12969, by rfl⟩) (B 25939 (by norm_num) ⟨12969, by rfl⟩ (by norm_num))
theorem R138365 : Reach 138365 := rs (se 3 (by rfl) ⟨25943, by rfl⟩) (B 51887 (by norm_num) ⟨25943, by rfl⟩ (by norm_num))
theorem R105601 : Reach 105601 := rs (se 2 (by rfl) ⟨39600, by rfl⟩) (B 79201 (by norm_num) ⟨39600, by rfl⟩ (by norm_num))
theorem R138389 : Reach 138389 := rs (se 6 (by rfl) ⟨3243, by rfl⟩) (B 6487 (by norm_num) ⟨3243, by rfl⟩ (by norm_num))
theorem R236701 : Reach 236701 := rs (se 3 (by rfl) ⟨44381, by rfl⟩) (B 88763 (by norm_num) ⟨44381, by rfl⟩ (by norm_num))
theorem R105637 : Reach 105637 := rs (se 4 (by rfl) ⟨9903, by rfl⟩) (B 19807 (by norm_num) ⟨9903, by rfl⟩ (by norm_num))
theorem R138413 : Reach 138413 := rs (se 3 (by rfl) ⟨25952, by rfl⟩) (B 51905 (by norm_num) ⟨25952, by rfl⟩ (by norm_num))
theorem R138437 : Reach 138437 := rs (se 4 (by rfl) ⟨12978, by rfl⟩) (B 25957 (by norm_num) ⟨12978, by rfl⟩ (by norm_num))
theorem R105673 : Reach 105673 := rs (se 2 (by rfl) ⟨39627, by rfl⟩) (B 79255 (by norm_num) ⟨39627, by rfl⟩ (by norm_num))
theorem R138461 : Reach 138461 := rs (se 3 (by rfl) ⟨25961, by rfl⟩) (B 51923 (by norm_num) ⟨25961, by rfl⟩ (by norm_num))
theorem R105709 : Reach 105709 := rs (se 3 (by rfl) ⟨19820, by rfl⟩) (B 39641 (by norm_num) ⟨19820, by rfl⟩ (by norm_num))
theorem R138485 : Reach 138485 := rs (se 5 (by rfl) ⟨6491, by rfl⟩) (B 12983 (by norm_num) ⟨6491, by rfl⟩ (by norm_num))
theorem R138509 : Reach 138509 := rs (se 3 (by rfl) ⟨25970, by rfl⟩) (B 51941 (by norm_num) ⟨25970, by rfl⟩ (by norm_num))
theorem R105745 : Reach 105745 := rs (se 2 (by rfl) ⟨39654, by rfl⟩) (B 79309 (by norm_num) ⟨39654, by rfl⟩ (by norm_num))
theorem R138533 : Reach 138533 := rs (se 4 (by rfl) ⟨12987, by rfl⟩) (B 25975 (by norm_num) ⟨12987, by rfl⟩ (by norm_num))
theorem R105781 : Reach 105781 := rs (se 5 (by rfl) ⟨4958, by rfl⟩) (B 9917 (by norm_num) ⟨4958, by rfl⟩ (by norm_num))
theorem R138557 : Reach 138557 := rs (se 3 (by rfl) ⟨25979, by rfl⟩) (B 51959 (by norm_num) ⟨25979, by rfl⟩ (by norm_num))
theorem R138581 : Reach 138581 := rs (se 11 (by rfl) ⟨101, by rfl⟩) (B 203 (by norm_num) ⟨101, by rfl⟩ (by norm_num))
theorem R105817 : Reach 105817 := rs (se 2 (by rfl) ⟨39681, by rfl⟩) (B 79363 (by norm_num) ⟨39681, by rfl⟩ (by norm_num))
theorem R138605 : Reach 138605 := rs (se 3 (by rfl) ⟨25988, by rfl⟩) (B 51977 (by norm_num) ⟨25988, by rfl⟩ (by norm_num))
theorem R105853 : Reach 105853 := rs (se 3 (by rfl) ⟨19847, by rfl⟩) (B 39695 (by norm_num) ⟨19847, by rfl⟩ (by norm_num))
theorem R138629 : Reach 138629 := rs (se 4 (by rfl) ⟨12996, by rfl⟩) (B 25993 (by norm_num) ⟨12996, by rfl⟩ (by norm_num))
theorem R138653 : Reach 138653 := rs (se 3 (by rfl) ⟨25997, by rfl⟩) (B 51995 (by norm_num) ⟨25997, by rfl⟩ (by norm_num))
theorem R105889 : Reach 105889 := rs (se 2 (by rfl) ⟨39708, by rfl⟩) (B 79417 (by norm_num) ⟨39708, by rfl⟩ (by norm_num))
theorem R236965 : Reach 236965 := rs (se 4 (by rfl) ⟨22215, by rfl⟩) (B 44431 (by norm_num) ⟨22215, by rfl⟩ (by norm_num))
theorem R335285 : Reach 335285 := rs (se 5 (by rfl) ⟨15716, by rfl⟩) (B 31433 (by norm_num) ⟨15716, by rfl⟩ (by norm_num))
theorem R138677 : Reach 138677 := rs (se 5 (by rfl) ⟨6500, by rfl⟩) (B 13001 (by norm_num) ⟨6500, by rfl⟩ (by norm_num))
theorem R105925 : Reach 105925 := rs (se 4 (by rfl) ⟨9930, by rfl⟩) (B 19861 (by norm_num) ⟨9930, by rfl⟩ (by norm_num))
theorem R138701 : Reach 138701 := rs (se 3 (by rfl) ⟨26006, by rfl⟩) (B 52013 (by norm_num) ⟨26006, by rfl⟩ (by norm_num))
theorem R105953 : Reach 105953 := rs (se 2 (by rfl) ⟨39732, by rfl⟩) (B 79465 (by norm_num) ⟨39732, by rfl⟩ (by norm_num))
theorem R138725 : Reach 138725 := rs (se 4 (by rfl) ⟨13005, by rfl⟩) (B 26011 (by norm_num) ⟨13005, by rfl⟩ (by norm_num))
theorem R105961 : Reach 105961 := rs (se 2 (by rfl) ⟨39735, by rfl⟩) (B 79471 (by norm_num) ⟨39735, by rfl⟩ (by norm_num))
theorem R138749 : Reach 138749 := rs (se 3 (by rfl) ⟨26015, by rfl⟩) (B 52031 (by norm_num) ⟨26015, by rfl⟩ (by norm_num))
theorem R105997 : Reach 105997 := rs (se 3 (by rfl) ⟨19874, by rfl⟩) (B 39749 (by norm_num) ⟨19874, by rfl⟩ (by norm_num))
theorem R138773 : Reach 138773 := rs (se 6 (by rfl) ⟨3252, by rfl⟩) (B 6505 (by norm_num) ⟨3252, by rfl⟩ (by norm_num))
theorem R237077 : Reach 237077 := rs (se 6 (by rfl) ⟨5556, by rfl⟩) (B 11113 (by norm_num) ⟨5556, by rfl⟩ (by norm_num))
theorem R138797 : Reach 138797 := rs (se 3 (by rfl) ⟨26024, by rfl⟩) (B 52049 (by norm_num) ⟨26024, by rfl⟩ (by norm_num))
theorem R106033 : Reach 106033 := rs (se 2 (by rfl) ⟨39762, by rfl⟩) (B 79525 (by norm_num) ⟨39762, by rfl⟩ (by norm_num))
theorem R138821 : Reach 138821 := rs (se 4 (by rfl) ⟨13014, by rfl⟩) (B 26029 (by norm_num) ⟨13014, by rfl⟩ (by norm_num))
theorem R106069 : Reach 106069 := rs (se 8 (by rfl) ⟨621, by rfl⟩) (B 1243 (by norm_num) ⟨621, by rfl⟩ (by norm_num))
theorem R138845 : Reach 138845 := rs (se 3 (by rfl) ⟨26033, by rfl⟩) (B 52067 (by norm_num) ⟨26033, by rfl⟩ (by norm_num))
theorem R138869 : Reach 138869 := rs (se 5 (by rfl) ⟨6509, by rfl⟩) (B 13019 (by norm_num) ⟨6509, by rfl⟩ (by norm_num))
theorem R106105 : Reach 106105 := rs (se 2 (by rfl) ⟨39789, by rfl⟩) (B 79579 (by norm_num) ⟨39789, by rfl⟩ (by norm_num))
theorem R138893 : Reach 138893 := rs (se 3 (by rfl) ⟨26042, by rfl⟩) (B 52085 (by norm_num) ⟨26042, by rfl⟩ (by norm_num))
theorem R106141 : Reach 106141 := rs (se 3 (by rfl) ⟨19901, by rfl⟩) (B 39803 (by norm_num) ⟨19901, by rfl⟩ (by norm_num))
theorem R138917 : Reach 138917 := rs (se 4 (by rfl) ⟨13023, by rfl⟩) (B 26047 (by norm_num) ⟨13023, by rfl⟩ (by norm_num))
theorem R138941 : Reach 138941 := rs (se 3 (by rfl) ⟨26051, by rfl⟩) (B 52103 (by norm_num) ⟨26051, by rfl⟩ (by norm_num))
theorem R106177 : Reach 106177 := rs (se 2 (by rfl) ⟨39816, by rfl⟩) (B 79633 (by norm_num) ⟨39816, by rfl⟩ (by norm_num))
theorem R138965 : Reach 138965 := rs (se 7 (by rfl) ⟨1628, by rfl⟩) (B 3257 (by norm_num) ⟨1628, by rfl⟩ (by norm_num))
theorem R237269 : Reach 237269 := rs (se 7 (by rfl) ⟨2780, by rfl⟩) (B 5561 (by norm_num) ⟨2780, by rfl⟩ (by norm_num))
theorem R106213 : Reach 106213 := rs (se 4 (by rfl) ⟨9957, by rfl⟩) (B 19915 (by norm_num) ⟨9957, by rfl⟩ (by norm_num))
theorem R138989 : Reach 138989 := rs (se 3 (by rfl) ⟨26060, by rfl⟩) (B 52121 (by norm_num) ⟨26060, by rfl⟩ (by norm_num))
theorem R139013 : Reach 139013 := rs (se 4 (by rfl) ⟨13032, by rfl⟩) (B 26065 (by norm_num) ⟨13032, by rfl⟩ (by norm_num))
theorem R106249 : Reach 106249 := rs (se 2 (by rfl) ⟨39843, by rfl⟩) (B 79687 (by norm_num) ⟨39843, by rfl⟩ (by norm_num))
theorem R139037 : Reach 139037 := rs (se 3 (by rfl) ⟨26069, by rfl⟩) (B 52139 (by norm_num) ⟨26069, by rfl⟩ (by norm_num))
theorem R171805 : Reach 171805 := rs (se 3 (by rfl) ⟨32213, by rfl⟩) (B 64427 (by norm_num) ⟨32213, by rfl⟩ (by norm_num))
theorem R106285 : Reach 106285 := rs (se 3 (by rfl) ⟨19928, by rfl⟩) (B 39857 (by norm_num) ⟨19928, by rfl⟩ (by norm_num))
theorem R139061 : Reach 139061 := rs (se 5 (by rfl) ⟨6518, by rfl⟩) (B 13037 (by norm_num) ⟨6518, by rfl⟩ (by norm_num))
theorem R139085 : Reach 139085 := rs (se 3 (by rfl) ⟨26078, by rfl⟩) (B 52157 (by norm_num) ⟨26078, by rfl⟩ (by norm_num))
theorem R106321 : Reach 106321 := rs (se 2 (by rfl) ⟨39870, by rfl⟩) (B 79741 (by norm_num) ⟨39870, by rfl⟩ (by norm_num))
theorem R139109 : Reach 139109 := rs (se 4 (by rfl) ⟨13041, by rfl⟩) (B 26083 (by norm_num) ⟨13041, by rfl⟩ (by norm_num))
theorem R106357 : Reach 106357 := rs (se 5 (by rfl) ⟨4985, by rfl⟩) (B 9971 (by norm_num) ⟨4985, by rfl⟩ (by norm_num))
theorem R139133 : Reach 139133 := rs (se 3 (by rfl) ⟨26087, by rfl⟩) (B 52175 (by norm_num) ⟨26087, by rfl⟩ (by norm_num))
theorem R139157 : Reach 139157 := rs (se 6 (by rfl) ⟨3261, by rfl⟩) (B 6523 (by norm_num) ⟨3261, by rfl⟩ (by norm_num))
theorem R106393 : Reach 106393 := rs (se 2 (by rfl) ⟨39897, by rfl⟩) (B 79795 (by norm_num) ⟨39897, by rfl⟩ (by norm_num))
theorem R139181 : Reach 139181 := rs (se 3 (by rfl) ⟨26096, by rfl⟩) (B 52193 (by norm_num) ⟨26096, by rfl⟩ (by norm_num))
theorem R106429 : Reach 106429 := rs (se 3 (by rfl) ⟨19955, by rfl⟩) (B 39911 (by norm_num) ⟨19955, by rfl⟩ (by norm_num))
theorem R139205 : Reach 139205 := rs (se 4 (by rfl) ⟨13050, by rfl⟩) (B 26101 (by norm_num) ⟨13050, by rfl⟩ (by norm_num))
theorem R139229 : Reach 139229 := rs (se 3 (by rfl) ⟨26105, by rfl⟩) (B 52211 (by norm_num) ⟨26105, by rfl⟩ (by norm_num))
theorem R106465 : Reach 106465 := rs (se 2 (by rfl) ⟨39924, by rfl⟩) (B 79849 (by norm_num) ⟨39924, by rfl⟩ (by norm_num))
theorem R139253 : Reach 139253 := rs (se 5 (by rfl) ⟨6527, by rfl⟩) (B 13055 (by norm_num) ⟨6527, by rfl⟩ (by norm_num))
theorem R106501 : Reach 106501 := rs (se 4 (by rfl) ⟨9984, by rfl⟩) (B 19969 (by norm_num) ⟨9984, by rfl⟩ (by norm_num))
theorem R139277 : Reach 139277 := rs (se 3 (by rfl) ⟨26114, by rfl⟩) (B 52229 (by norm_num) ⟨26114, by rfl⟩ (by norm_num))
theorem R106529 : Reach 106529 := rs (se 2 (by rfl) ⟨39948, by rfl⟩) (B 79897 (by norm_num) ⟨39948, by rfl⟩ (by norm_num))
theorem R139301 : Reach 139301 := rs (se 4 (by rfl) ⟨13059, by rfl⟩) (B 26119 (by norm_num) ⟨13059, by rfl⟩ (by norm_num))
theorem R106537 : Reach 106537 := rs (se 2 (by rfl) ⟨39951, by rfl⟩) (B 79903 (by norm_num) ⟨39951, by rfl⟩ (by norm_num))
theorem R237613 : Reach 237613 := rs (se 3 (by rfl) ⟨44552, by rfl⟩) (B 89105 (by norm_num) ⟨44552, by rfl⟩ (by norm_num))
theorem R139325 : Reach 139325 := rs (se 3 (by rfl) ⟨26123, by rfl⟩) (B 52247 (by norm_num) ⟨26123, by rfl⟩ (by norm_num))
theorem R106573 : Reach 106573 := rs (se 3 (by rfl) ⟨19982, by rfl⟩) (B 39965 (by norm_num) ⟨19982, by rfl⟩ (by norm_num))
theorem R139349 : Reach 139349 := rs (se 8 (by rfl) ⟨816, by rfl⟩) (B 1633 (by norm_num) ⟨816, by rfl⟩ (by norm_num))
theorem R467045 : Reach 467045 := rs (se 4 (by rfl) ⟨43785, by rfl⟩) (B 87571 (by norm_num) ⟨43785, by rfl⟩ (by norm_num))
theorem R139373 : Reach 139373 := rs (se 3 (by rfl) ⟨26132, by rfl⟩) (B 52265 (by norm_num) ⟨26132, by rfl⟩ (by norm_num))
theorem R106609 : Reach 106609 := rs (se 2 (by rfl) ⟨39978, by rfl⟩) (B 79957 (by norm_num) ⟨39978, by rfl⟩ (by norm_num))
theorem R696437 : Reach 696437 := rs (se 5 (by rfl) ⟨32645, by rfl⟩) (B 65291 (by norm_num) ⟨32645, by rfl⟩ (by norm_num))
theorem R139397 : Reach 139397 := rs (se 4 (by rfl) ⟨13068, by rfl⟩) (B 26137 (by norm_num) ⟨13068, by rfl⟩ (by norm_num))
theorem R106645 : Reach 106645 := rs (se 6 (by rfl) ⟨2499, by rfl⟩) (B 4999 (by norm_num) ⟨2499, by rfl⟩ (by norm_num))
theorem R139421 : Reach 139421 := rs (se 3 (by rfl) ⟨26141, by rfl⟩) (B 52283 (by norm_num) ⟨26141, by rfl⟩ (by norm_num))
theorem R237725 : Reach 237725 := rs (se 3 (by rfl) ⟨44573, by rfl⟩) (B 89147 (by norm_num) ⟨44573, by rfl⟩ (by norm_num))
theorem R139445 : Reach 139445 := rs (se 5 (by rfl) ⟨6536, by rfl⟩) (B 13073 (by norm_num) ⟨6536, by rfl⟩ (by norm_num))
theorem R106681 : Reach 106681 := rs (se 2 (by rfl) ⟨40005, by rfl⟩) (B 80011 (by norm_num) ⟨40005, by rfl⟩ (by norm_num))
theorem R139469 : Reach 139469 := rs (se 3 (by rfl) ⟨26150, by rfl⟩) (B 52301 (by norm_num) ⟨26150, by rfl⟩ (by norm_num))
theorem R106717 : Reach 106717 := rs (se 3 (by rfl) ⟨20009, by rfl⟩) (B 40019 (by norm_num) ⟨20009, by rfl⟩ (by norm_num))
theorem R139493 : Reach 139493 := rs (se 4 (by rfl) ⟨13077, by rfl⟩) (B 26155 (by norm_num) ⟨13077, by rfl⟩ (by norm_num))
theorem R139517 : Reach 139517 := rs (se 3 (by rfl) ⟨26159, by rfl⟩) (B 52319 (by norm_num) ⟨26159, by rfl⟩ (by norm_num))
theorem R106753 : Reach 106753 := rs (se 2 (by rfl) ⟨40032, by rfl⟩) (B 80065 (by norm_num) ⟨40032, by rfl⟩ (by norm_num))
theorem R139541 : Reach 139541 := rs (se 6 (by rfl) ⟨3270, by rfl⟩) (B 6541 (by norm_num) ⟨3270, by rfl⟩ (by norm_num))
theorem R106789 : Reach 106789 := rs (se 4 (by rfl) ⟨10011, by rfl⟩) (B 20023 (by norm_num) ⟨10011, by rfl⟩ (by norm_num))
theorem R139565 : Reach 139565 := rs (se 3 (by rfl) ⟨26168, by rfl⟩) (B 52337 (by norm_num) ⟨26168, by rfl⟩ (by norm_num))
theorem R205109 : Reach 205109 := rs (se 5 (by rfl) ⟨9614, by rfl⟩) (B 19229 (by norm_num) ⟨9614, by rfl⟩ (by norm_num))
theorem R139589 : Reach 139589 := rs (se 4 (by rfl) ⟨13086, by rfl⟩) (B 26173 (by norm_num) ⟨13086, by rfl⟩ (by norm_num))
theorem R106825 : Reach 106825 := rs (se 2 (by rfl) ⟨40059, by rfl⟩) (B 80119 (by norm_num) ⟨40059, by rfl⟩ (by norm_num))
theorem R139613 : Reach 139613 := rs (se 3 (by rfl) ⟨26177, by rfl⟩) (B 52355 (by norm_num) ⟨26177, by rfl⟩ (by norm_num))
theorem R237917 : Reach 237917 := rs (se 3 (by rfl) ⟨44609, by rfl⟩) (B 89219 (by norm_num) ⟨44609, by rfl⟩ (by norm_num))
theorem R106861 : Reach 106861 := rs (se 3 (by rfl) ⟨20036, by rfl⟩) (B 40073 (by norm_num) ⟨20036, by rfl⟩ (by norm_num))
theorem R139637 : Reach 139637 := rs (se 5 (by rfl) ⟨6545, by rfl⟩) (B 13091 (by norm_num) ⟨6545, by rfl⟩ (by norm_num))
theorem R205181 : Reach 205181 := rs (se 3 (by rfl) ⟨38471, by rfl⟩) (B 76943 (by norm_num) ⟨38471, by rfl⟩ (by norm_num))
theorem R139661 : Reach 139661 := rs (se 3 (by rfl) ⟨26186, by rfl⟩) (B 52373 (by norm_num) ⟨26186, by rfl⟩ (by norm_num))
theorem R106897 : Reach 106897 := rs (se 2 (by rfl) ⟨40086, by rfl⟩) (B 80173 (by norm_num) ⟨40086, by rfl⟩ (by norm_num))
theorem R139685 : Reach 139685 := rs (se 4 (by rfl) ⟨13095, by rfl⟩) (B 26191 (by norm_num) ⟨13095, by rfl⟩ (by norm_num))
theorem R106933 : Reach 106933 := rs (se 5 (by rfl) ⟨5012, by rfl⟩) (B 10025 (by norm_num) ⟨5012, by rfl⟩ (by norm_num))
theorem R139709 : Reach 139709 := rs (se 3 (by rfl) ⟨26195, by rfl⟩) (B 52391 (by norm_num) ⟨26195, by rfl⟩ (by norm_num))
theorem R205253 : Reach 205253 := rs (se 4 (by rfl) ⟨19242, by rfl⟩) (B 38485 (by norm_num) ⟨19242, by rfl⟩ (by norm_num))
theorem R401861 : Reach 401861 := rs (se 4 (by rfl) ⟨37674, by rfl⟩) (B 75349 (by norm_num) ⟨37674, by rfl⟩ (by norm_num))
theorem R139733 : Reach 139733 := rs (se 7 (by rfl) ⟨1637, by rfl⟩) (B 3275 (by norm_num) ⟨1637, by rfl⟩ (by norm_num))
theorem R106969 : Reach 106969 := rs (se 2 (by rfl) ⟨40113, by rfl⟩) (B 80227 (by norm_num) ⟨40113, by rfl⟩ (by norm_num))
theorem R139757 : Reach 139757 := rs (se 3 (by rfl) ⟨26204, by rfl⟩) (B 52409 (by norm_num) ⟨26204, by rfl⟩ (by norm_num))
theorem R107005 : Reach 107005 := rs (se 3 (by rfl) ⟨20063, by rfl⟩) (B 40127 (by norm_num) ⟨20063, by rfl⟩ (by norm_num))
theorem R139781 : Reach 139781 := rs (se 4 (by rfl) ⟨13104, by rfl⟩) (B 26209 (by norm_num) ⟨13104, by rfl⟩ (by norm_num))
theorem R205325 : Reach 205325 := rs (se 3 (by rfl) ⟨38498, by rfl⟩) (B 76997 (by norm_num) ⟨38498, by rfl⟩ (by norm_num))
theorem R139805 : Reach 139805 := rs (se 3 (by rfl) ⟨26213, by rfl⟩) (B 52427 (by norm_num) ⟨26213, by rfl⟩ (by norm_num))
theorem R139829 : Reach 139829 := rs (se 5 (by rfl) ⟨6554, by rfl⟩) (B 13109 (by norm_num) ⟨6554, by rfl⟩ (by norm_num))
theorem R139853 : Reach 139853 := rs (se 3 (by rfl) ⟨26222, by rfl⟩) (B 52445 (by norm_num) ⟨26222, by rfl⟩ (by norm_num))
theorem R205397 : Reach 205397 := rs (se 8 (by rfl) ⟨1203, by rfl⟩) (B 2407 (by norm_num) ⟨1203, by rfl⟩ (by norm_num))
theorem R139877 : Reach 139877 := rs (se 4 (by rfl) ⟨13113, by rfl⟩) (B 26227 (by norm_num) ⟨13113, by rfl⟩ (by norm_num))
theorem R139901 : Reach 139901 := rs (se 3 (by rfl) ⟨26231, by rfl⟩) (B 52463 (by norm_num) ⟨26231, by rfl⟩ (by norm_num))
theorem R139909 : Reach 139909 := rs (se 4 (by rfl) ⟨13116, by rfl⟩) (B 26233 (by norm_num) ⟨13116, by rfl⟩ (by norm_num))
theorem R139925 : Reach 139925 := rs (se 6 (by rfl) ⟨3279, by rfl⟩) (B 6559 (by norm_num) ⟨3279, by rfl⟩ (by norm_num))
theorem R205469 : Reach 205469 := rs (se 3 (by rfl) ⟨38525, by rfl⟩) (B 77051 (by norm_num) ⟨38525, by rfl⟩ (by norm_num))
theorem R139949 : Reach 139949 := rs (se 3 (by rfl) ⟨26240, by rfl⟩) (B 52481 (by norm_num) ⟨26240, by rfl⟩ (by norm_num))
theorem R238261 : Reach 238261 := rs (se 5 (by rfl) ⟨11168, by rfl⟩) (B 22337 (by norm_num) ⟨11168, by rfl⟩ (by norm_num))
theorem R139973 : Reach 139973 := rs (se 4 (by rfl) ⟨13122, by rfl⟩) (B 26245 (by norm_num) ⟨13122, by rfl⟩ (by norm_num))
theorem R139997 : Reach 139997 := rs (se 3 (by rfl) ⟨26249, by rfl⟩) (B 52499 (by norm_num) ⟨26249, by rfl⟩ (by norm_num))
theorem R205541 : Reach 205541 := rs (se 4 (by rfl) ⟨19269, by rfl⟩) (B 38539 (by norm_num) ⟨19269, by rfl⟩ (by norm_num))
theorem R140021 : Reach 140021 := rs (se 5 (by rfl) ⟨6563, by rfl⟩) (B 13127 (by norm_num) ⟨6563, by rfl⟩ (by norm_num))
theorem R140045 : Reach 140045 := rs (se 3 (by rfl) ⟨26258, by rfl⟩) (B 52517 (by norm_num) ⟨26258, by rfl⟩ (by norm_num))
theorem R140069 : Reach 140069 := rs (se 4 (by rfl) ⟨13131, by rfl⟩) (B 26263 (by norm_num) ⟨13131, by rfl⟩ (by norm_num))
theorem R238373 : Reach 238373 := rs (se 4 (by rfl) ⟨22347, by rfl⟩) (B 44695 (by norm_num) ⟨22347, by rfl⟩ (by norm_num))
theorem R205613 : Reach 205613 := rs (se 3 (by rfl) ⟨38552, by rfl⟩) (B 77105 (by norm_num) ⟨38552, by rfl⟩ (by norm_num))
theorem R140093 : Reach 140093 := rs (se 3 (by rfl) ⟨26267, by rfl⟩) (B 52535 (by norm_num) ⟨26267, by rfl⟩ (by norm_num))
theorem R140117 : Reach 140117 := rs (se 9 (by rfl) ⟨410, by rfl⟩) (B 821 (by norm_num) ⟨410, by rfl⟩ (by norm_num))
theorem R140141 : Reach 140141 := rs (se 3 (by rfl) ⟨26276, by rfl⟩) (B 52553 (by norm_num) ⟨26276, by rfl⟩ (by norm_num))
theorem R205685 : Reach 205685 := rs (se 5 (by rfl) ⟨9641, by rfl⟩) (B 19283 (by norm_num) ⟨9641, by rfl⟩ (by norm_num))
theorem R140165 : Reach 140165 := rs (se 4 (by rfl) ⟨13140, by rfl⟩) (B 26281 (by norm_num) ⟨13140, by rfl⟩ (by norm_num))
theorem R140189 : Reach 140189 := rs (se 3 (by rfl) ⟨26285, by rfl⟩) (B 52571 (by norm_num) ⟨26285, by rfl⟩ (by norm_num))
theorem R140213 : Reach 140213 := rs (se 5 (by rfl) ⟨6572, by rfl⟩) (B 13145 (by norm_num) ⟨6572, by rfl⟩ (by norm_num))
theorem R205757 : Reach 205757 := rs (se 3 (by rfl) ⟨38579, by rfl⟩) (B 77159 (by norm_num) ⟨38579, by rfl⟩ (by norm_num))
theorem R140237 : Reach 140237 := rs (se 3 (by rfl) ⟨26294, by rfl⟩) (B 52589 (by norm_num) ⟨26294, by rfl⟩ (by norm_num))
theorem R140261 : Reach 140261 := rs (se 4 (by rfl) ⟨13149, by rfl⟩) (B 26299 (by norm_num) ⟨13149, by rfl⟩ (by norm_num))
theorem R238565 : Reach 238565 := rs (se 4 (by rfl) ⟨22365, by rfl⟩) (B 44731 (by norm_num) ⟨22365, by rfl⟩ (by norm_num))
theorem R140285 : Reach 140285 := rs (se 3 (by rfl) ⟨26303, by rfl⟩) (B 52607 (by norm_num) ⟨26303, by rfl⟩ (by norm_num))
theorem R205829 : Reach 205829 := rs (se 4 (by rfl) ⟨19296, by rfl⟩) (B 38593 (by norm_num) ⟨19296, by rfl⟩ (by norm_num))
theorem R140309 : Reach 140309 := rs (se 6 (by rfl) ⟨3288, by rfl⟩) (B 6577 (by norm_num) ⟨3288, by rfl⟩ (by norm_num))
theorem R140333 : Reach 140333 := rs (se 3 (by rfl) ⟨26312, by rfl⟩) (B 52625 (by norm_num) ⟨26312, by rfl⟩ (by norm_num))
theorem R140357 : Reach 140357 := rs (se 4 (by rfl) ⟨13158, by rfl⟩) (B 26317 (by norm_num) ⟨13158, by rfl⟩ (by norm_num))
theorem R205901 : Reach 205901 := rs (se 3 (by rfl) ⟨38606, by rfl⟩) (B 77213 (by norm_num) ⟨38606, by rfl⟩ (by norm_num))
theorem R140381 : Reach 140381 := rs (se 3 (by rfl) ⟨26321, by rfl⟩) (B 52643 (by norm_num) ⟨26321, by rfl⟩ (by norm_num))
theorem R140405 : Reach 140405 := rs (se 5 (by rfl) ⟨6581, by rfl⟩) (B 13163 (by norm_num) ⟨6581, by rfl⟩ (by norm_num))
theorem R140429 : Reach 140429 := rs (se 3 (by rfl) ⟨26330, by rfl⟩) (B 52661 (by norm_num) ⟨26330, by rfl⟩ (by norm_num))
theorem R205973 : Reach 205973 := rs (se 6 (by rfl) ⟨4827, by rfl⟩) (B 9655 (by norm_num) ⟨4827, by rfl⟩ (by norm_num))
theorem R140453 : Reach 140453 := rs (se 4 (by rfl) ⟨13167, by rfl⟩) (B 26335 (by norm_num) ⟨13167, by rfl⟩ (by norm_num))
theorem R140477 : Reach 140477 := rs (se 3 (by rfl) ⟨26339, by rfl⟩) (B 52679 (by norm_num) ⟨26339, by rfl⟩ (by norm_num))
theorem R107713 : Reach 107713 := rs (se 2 (by rfl) ⟨40392, by rfl⟩) (B 80785 (by norm_num) ⟨40392, by rfl⟩ (by norm_num))
theorem R140501 : Reach 140501 := rs (se 7 (by rfl) ⟨1646, by rfl⟩) (B 3293 (by norm_num) ⟨1646, by rfl⟩ (by norm_num))
theorem R206045 : Reach 206045 := rs (se 3 (by rfl) ⟨38633, by rfl⟩) (B 77267 (by norm_num) ⟨38633, by rfl⟩ (by norm_num))
theorem R140525 : Reach 140525 := rs (se 3 (by rfl) ⟨26348, by rfl⟩) (B 52697 (by norm_num) ⟨26348, by rfl⟩ (by norm_num))
theorem R402677 : Reach 402677 := rs (se 5 (by rfl) ⟨18875, by rfl⟩) (B 37751 (by norm_num) ⟨18875, by rfl⟩ (by norm_num))
theorem R140549 : Reach 140549 := rs (se 4 (by rfl) ⟨13176, by rfl⟩) (B 26353 (by norm_num) ⟨13176, by rfl⟩ (by norm_num))
theorem R140573 : Reach 140573 := rs (se 3 (by rfl) ⟨26357, by rfl⟩) (B 52715 (by norm_num) ⟨26357, by rfl⟩ (by norm_num))
theorem R206117 : Reach 206117 := rs (se 4 (by rfl) ⟨19323, by rfl⟩) (B 38647 (by norm_num) ⟨19323, by rfl⟩ (by norm_num))
theorem R140597 : Reach 140597 := rs (se 5 (by rfl) ⟨6590, by rfl⟩) (B 13181 (by norm_num) ⟨6590, by rfl⟩ (by norm_num))
theorem R238909 : Reach 238909 := rs (se 3 (by rfl) ⟨44795, by rfl⟩) (B 89591 (by norm_num) ⟨44795, by rfl⟩ (by norm_num))
theorem R140621 : Reach 140621 := rs (se 3 (by rfl) ⟨26366, by rfl⟩) (B 52733 (by norm_num) ⟨26366, by rfl⟩ (by norm_num))
theorem R599381 : Reach 599381 := rs (se 12 (by rfl) ⟨219, by rfl⟩) (B 439 (by norm_num) ⟨219, by rfl⟩ (by norm_num))
theorem R140645 : Reach 140645 := rs (se 4 (by rfl) ⟨13185, by rfl⟩) (B 26371 (by norm_num) ⟨13185, by rfl⟩ (by norm_num))
theorem R206189 : Reach 206189 := rs (se 3 (by rfl) ⟨38660, by rfl⟩) (B 77321 (by norm_num) ⟨38660, by rfl⟩ (by norm_num))
theorem R468341 : Reach 468341 := rs (se 5 (by rfl) ⟨21953, by rfl⟩) (B 43907 (by norm_num) ⟨21953, by rfl⟩ (by norm_num))
theorem R140669 : Reach 140669 := rs (se 3 (by rfl) ⟨26375, by rfl⟩) (B 52751 (by norm_num) ⟨26375, by rfl⟩ (by norm_num))
theorem R140693 : Reach 140693 := rs (se 6 (by rfl) ⟨3297, by rfl⟩) (B 6595 (by norm_num) ⟨3297, by rfl⟩ (by norm_num))
theorem R402853 : Reach 402853 := rs (se 4 (by rfl) ⟨37767, by rfl⟩) (B 75535 (by norm_num) ⟨37767, by rfl⟩ (by norm_num))
theorem R140717 : Reach 140717 := rs (se 3 (by rfl) ⟨26384, by rfl⟩) (B 52769 (by norm_num) ⟨26384, by rfl⟩ (by norm_num))
theorem R239021 : Reach 239021 := rs (se 3 (by rfl) ⟨44816, by rfl⟩) (B 89633 (by norm_num) ⟨44816, by rfl⟩ (by norm_num))
theorem R206261 : Reach 206261 := rs (se 5 (by rfl) ⟨9668, by rfl⟩) (B 19337 (by norm_num) ⟨9668, by rfl⟩ (by norm_num))
theorem R140741 : Reach 140741 := rs (se 4 (by rfl) ⟨13194, by rfl⟩) (B 26389 (by norm_num) ⟨13194, by rfl⟩ (by norm_num))
theorem R140765 : Reach 140765 := rs (se 3 (by rfl) ⟨26393, by rfl⟩) (B 52787 (by norm_num) ⟨26393, by rfl⟩ (by norm_num))
theorem R140789 : Reach 140789 := rs (se 5 (by rfl) ⟨6599, by rfl⟩) (B 13199 (by norm_num) ⟨6599, by rfl⟩ (by norm_num))
theorem R206333 : Reach 206333 := rs (se 3 (by rfl) ⟨38687, by rfl⟩) (B 77375 (by norm_num) ⟨38687, by rfl⟩ (by norm_num))
theorem R140813 : Reach 140813 := rs (se 3 (by rfl) ⟨26402, by rfl⟩) (B 52805 (by norm_num) ⟨26402, by rfl⟩ (by norm_num))
theorem R140837 : Reach 140837 := rs (se 4 (by rfl) ⟨13203, by rfl⟩) (B 26407 (by norm_num) ⟨13203, by rfl⟩ (by norm_num))
theorem R140861 : Reach 140861 := rs (se 3 (by rfl) ⟨26411, by rfl⟩) (B 52823 (by norm_num) ⟨26411, by rfl⟩ (by norm_num))
theorem R206405 : Reach 206405 := rs (se 4 (by rfl) ⟨19350, by rfl⟩) (B 38701 (by norm_num) ⟨19350, by rfl⟩ (by norm_num))
theorem R140885 : Reach 140885 := rs (se 8 (by rfl) ⟨825, by rfl⟩) (B 1651 (by norm_num) ⟨825, by rfl⟩ (by norm_num))
theorem R173677 : Reach 173677 := rs (se 3 (by rfl) ⟨32564, by rfl⟩) (B 65129 (by norm_num) ⟨32564, by rfl⟩ (by norm_num))
theorem R140909 : Reach 140909 := rs (se 3 (by rfl) ⟨26420, by rfl⟩) (B 52841 (by norm_num) ⟨26420, by rfl⟩ (by norm_num))
theorem R239213 : Reach 239213 := rs (se 3 (by rfl) ⟨44852, by rfl⟩) (B 89705 (by norm_num) ⟨44852, by rfl⟩ (by norm_num))
theorem R140933 : Reach 140933 := rs (se 4 (by rfl) ⟨13212, by rfl⟩) (B 26425 (by norm_num) ⟨13212, by rfl⟩ (by norm_num))
theorem R206477 : Reach 206477 := rs (se 3 (by rfl) ⟨38714, by rfl⟩) (B 77429 (by norm_num) ⟨38714, by rfl⟩ (by norm_num))
theorem R468629 : Reach 468629 := rs (se 6 (by rfl) ⟨10983, by rfl⟩) (B 21967 (by norm_num) ⟨10983, by rfl⟩ (by norm_num))
theorem R140957 : Reach 140957 := rs (se 3 (by rfl) ⟨26429, by rfl⟩) (B 52859 (by norm_num) ⟨26429, by rfl⟩ (by norm_num))
theorem R140981 : Reach 140981 := rs (se 5 (by rfl) ⟨6608, by rfl⟩) (B 13217 (by norm_num) ⟨6608, by rfl⟩ (by norm_num))
theorem R141005 : Reach 141005 := rs (se 3 (by rfl) ⟨26438, by rfl⟩) (B 52877 (by norm_num) ⟨26438, by rfl⟩ (by norm_num))
theorem R206549 : Reach 206549 := rs (se 7 (by rfl) ⟨2420, by rfl⟩) (B 4841 (by norm_num) ⟨2420, by rfl⟩ (by norm_num))
theorem R108253 : Reach 108253 := rs (se 3 (by rfl) ⟨20297, by rfl⟩) (B 40595 (by norm_num) ⟨20297, by rfl⟩ (by norm_num))
theorem R141029 : Reach 141029 := rs (se 4 (by rfl) ⟨13221, by rfl⟩) (B 26443 (by norm_num) ⟨13221, by rfl⟩ (by norm_num))
theorem R173821 : Reach 173821 := rs (se 3 (by rfl) ⟨32591, by rfl⟩) (B 65183 (by norm_num) ⟨32591, by rfl⟩ (by norm_num))
theorem R141053 : Reach 141053 := rs (se 3 (by rfl) ⟨26447, by rfl⟩) (B 52895 (by norm_num) ⟨26447, by rfl⟩ (by norm_num))
theorem R141077 : Reach 141077 := rs (se 6 (by rfl) ⟨3306, by rfl⟩) (B 6613 (by norm_num) ⟨3306, by rfl⟩ (by norm_num))
theorem R206621 : Reach 206621 := rs (se 3 (by rfl) ⟨38741, by rfl⟩) (B 77483 (by norm_num) ⟨38741, by rfl⟩ (by norm_num))
theorem R141101 : Reach 141101 := rs (se 3 (by rfl) ⟨26456, by rfl⟩) (B 52913 (by norm_num) ⟨26456, by rfl⟩ (by norm_num))
theorem R141125 : Reach 141125 := rs (se 4 (by rfl) ⟨13230, by rfl⟩) (B 26461 (by norm_num) ⟨13230, by rfl⟩ (by norm_num))
theorem R141149 : Reach 141149 := rs (se 3 (by rfl) ⟨26465, by rfl⟩) (B 52931 (by norm_num) ⟨26465, by rfl⟩ (by norm_num))
theorem R206693 : Reach 206693 := rs (se 4 (by rfl) ⟨19377, by rfl⟩) (B 38755 (by norm_num) ⟨19377, by rfl⟩ (by norm_num))
theorem R141173 : Reach 141173 := rs (se 5 (by rfl) ⟨6617, by rfl⟩) (B 13235 (by norm_num) ⟨6617, by rfl⟩ (by norm_num))
theorem R141197 : Reach 141197 := rs (se 3 (by rfl) ⟨26474, by rfl⟩) (B 52949 (by norm_num) ⟨26474, by rfl⟩ (by norm_num))
theorem R173981 : Reach 173981 := rs (se 3 (by rfl) ⟨32621, by rfl⟩) (B 65243 (by norm_num) ⟨32621, by rfl⟩ (by norm_num))
theorem R141221 : Reach 141221 := rs (se 4 (by rfl) ⟨13239, by rfl⟩) (B 26479 (by norm_num) ⟨13239, by rfl⟩ (by norm_num))
theorem R206765 : Reach 206765 := rs (se 3 (by rfl) ⟨38768, by rfl⟩) (B 77537 (by norm_num) ⟨38768, by rfl⟩ (by norm_num))
theorem R141245 : Reach 141245 := rs (se 3 (by rfl) ⟨26483, by rfl⟩) (B 52967 (by norm_num) ⟨26483, by rfl⟩ (by norm_num))
theorem R337861 : Reach 337861 := rs (se 4 (by rfl) ⟨31674, by rfl⟩) (B 63349 (by norm_num) ⟨31674, by rfl⟩ (by norm_num))
theorem R305093 : Reach 305093 := rs (se 4 (by rfl) ⟨28602, by rfl⟩) (B 57205 (by norm_num) ⟨28602, by rfl⟩ (by norm_num))
theorem R239557 : Reach 239557 := rs (se 4 (by rfl) ⟨22458, by rfl⟩) (B 44917 (by norm_num) ⟨22458, by rfl⟩ (by norm_num))
theorem R141269 : Reach 141269 := rs (se 7 (by rfl) ⟨1655, by rfl⟩) (B 3311 (by norm_num) ⟨1655, by rfl⟩ (by norm_num))
theorem R141293 : Reach 141293 := rs (se 3 (by rfl) ⟨26492, by rfl⟩) (B 52985 (by norm_num) ⟨26492, by rfl⟩ (by norm_num))
theorem R206837 : Reach 206837 := rs (se 5 (by rfl) ⟨9695, by rfl⟩) (B 19391 (by norm_num) ⟨9695, by rfl⟩ (by norm_num))
theorem R141317 : Reach 141317 := rs (se 4 (by rfl) ⟨13248, by rfl⟩) (B 26497 (by norm_num) ⟨13248, by rfl⟩ (by norm_num))
theorem R141341 : Reach 141341 := rs (se 3 (by rfl) ⟨26501, by rfl⟩) (B 53003 (by norm_num) ⟨26501, by rfl⟩ (by norm_num))
theorem R174125 : Reach 174125 := rs (se 3 (by rfl) ⟨32648, by rfl⟩) (B 65297 (by norm_num) ⟨32648, by rfl⟩ (by norm_num))
theorem R141365 : Reach 141365 := rs (se 5 (by rfl) ⟨6626, by rfl⟩) (B 13253 (by norm_num) ⟨6626, by rfl⟩ (by norm_num))
theorem R239669 : Reach 239669 := rs (se 5 (by rfl) ⟨11234, by rfl⟩) (B 22469 (by norm_num) ⟨11234, by rfl⟩ (by norm_num))
theorem R206909 : Reach 206909 := rs (se 3 (by rfl) ⟨38795, by rfl⟩) (B 77591 (by norm_num) ⟨38795, by rfl⟩ (by norm_num))
theorem R141389 : Reach 141389 := rs (se 3 (by rfl) ⟨26510, by rfl⟩) (B 53021 (by norm_num) ⟨26510, by rfl⟩ (by norm_num))
theorem R141413 : Reach 141413 := rs (se 4 (by rfl) ⟨13257, by rfl⟩) (B 26515 (by norm_num) ⟨13257, by rfl⟩ (by norm_num))
theorem R141437 : Reach 141437 := rs (se 3 (by rfl) ⟨26519, by rfl⟩) (B 53039 (by norm_num) ⟨26519, by rfl⟩ (by norm_num))
theorem R206981 : Reach 206981 := rs (se 4 (by rfl) ⟨19404, by rfl⟩) (B 38809 (by norm_num) ⟨19404, by rfl⟩ (by norm_num))
theorem R141461 : Reach 141461 := rs (se 6 (by rfl) ⟨3315, by rfl⟩) (B 6631 (by norm_num) ⟨3315, by rfl⟩ (by norm_num))
theorem R141485 : Reach 141485 := rs (se 3 (by rfl) ⟨26528, by rfl⟩) (B 53057 (by norm_num) ⟨26528, by rfl⟩ (by norm_num))
theorem R141509 : Reach 141509 := rs (se 4 (by rfl) ⟨13266, by rfl⟩) (B 26533 (by norm_num) ⟨13266, by rfl⟩ (by norm_num))
theorem R207053 : Reach 207053 := rs (se 3 (by rfl) ⟨38822, by rfl⟩) (B 77645 (by norm_num) ⟨38822, by rfl⟩ (by norm_num))
theorem R141533 : Reach 141533 := rs (se 3 (by rfl) ⟨26537, by rfl⟩) (B 53075 (by norm_num) ⟨26537, by rfl⟩ (by norm_num))
theorem R141557 : Reach 141557 := rs (se 5 (by rfl) ⟨6635, by rfl⟩) (B 13271 (by norm_num) ⟨6635, by rfl⟩ (by norm_num))
theorem R239861 : Reach 239861 := rs (se 5 (by rfl) ⟨11243, by rfl⟩) (B 22487 (by norm_num) ⟨11243, by rfl⟩ (by norm_num))
theorem R141581 : Reach 141581 := rs (se 3 (by rfl) ⟨26546, by rfl⟩) (B 53093 (by norm_num) ⟨26546, by rfl⟩ (by norm_num))
theorem R207125 : Reach 207125 := rs (se 6 (by rfl) ⟨4854, by rfl⟩) (B 9709 (by norm_num) ⟨4854, by rfl⟩ (by norm_num))
theorem R141605 : Reach 141605 := rs (se 4 (by rfl) ⟨13275, by rfl⟩) (B 26551 (by norm_num) ⟨13275, by rfl⟩ (by norm_num))
theorem R141629 : Reach 141629 := rs (se 3 (by rfl) ⟨26555, by rfl⟩) (B 53111 (by norm_num) ⟨26555, by rfl⟩ (by norm_num))
theorem R174413 : Reach 174413 := rs (se 3 (by rfl) ⟨32702, by rfl⟩) (B 65405 (by norm_num) ⟨32702, by rfl⟩ (by norm_num))
theorem R141653 : Reach 141653 := rs (se 10 (by rfl) ⟨207, by rfl⟩) (B 415 (by norm_num) ⟨207, by rfl⟩ (by norm_num))
theorem R207197 : Reach 207197 := rs (se 3 (by rfl) ⟨38849, by rfl⟩) (B 77699 (by norm_num) ⟨38849, by rfl⟩ (by norm_num))
theorem R141677 : Reach 141677 := rs (se 3 (by rfl) ⟨26564, by rfl⟩) (B 53129 (by norm_num) ⟨26564, by rfl⟩ (by norm_num))
theorem R141701 : Reach 141701 := rs (se 4 (by rfl) ⟨13284, by rfl⟩) (B 26569 (by norm_num) ⟨13284, by rfl⟩ (by norm_num))
theorem R141725 : Reach 141725 := rs (se 3 (by rfl) ⟨26573, by rfl⟩) (B 53147 (by norm_num) ⟨26573, by rfl⟩ (by norm_num))
theorem R207269 : Reach 207269 := rs (se 4 (by rfl) ⟨19431, by rfl⟩) (B 38863 (by norm_num) ⟨19431, by rfl⟩ (by norm_num))
theorem R141749 : Reach 141749 := rs (se 5 (by rfl) ⟨6644, by rfl⟩) (B 13289 (by norm_num) ⟨6644, by rfl⟩ (by norm_num))
theorem R141773 : Reach 141773 := rs (se 3 (by rfl) ⟨26582, by rfl⟩) (B 53165 (by norm_num) ⟨26582, by rfl⟩ (by norm_num))
theorem R174565 : Reach 174565 := rs (se 4 (by rfl) ⟨16365, by rfl⟩) (B 32731 (by norm_num) ⟨16365, by rfl⟩ (by norm_num))
theorem R141797 : Reach 141797 := rs (se 4 (by rfl) ⟨13293, by rfl⟩) (B 26587 (by norm_num) ⟨13293, by rfl⟩ (by norm_num))
theorem R141805 : Reach 141805 := rs (se 3 (by rfl) ⟨26588, by rfl⟩) (B 53177 (by norm_num) ⟨26588, by rfl⟩ (by norm_num))
theorem R207341 : Reach 207341 := rs (se 3 (by rfl) ⟨38876, by rfl⟩) (B 77753 (by norm_num) ⟨38876, by rfl⟩ (by norm_num))
theorem R141821 : Reach 141821 := rs (se 3 (by rfl) ⟨26591, by rfl⟩) (B 53183 (by norm_num) ⟨26591, by rfl⟩ (by norm_num))
theorem R141845 : Reach 141845 := rs (se 6 (by rfl) ⟨3324, by rfl⟩) (B 6649 (by norm_num) ⟨3324, by rfl⟩ (by norm_num))
theorem R141869 : Reach 141869 := rs (se 3 (by rfl) ⟨26600, by rfl⟩) (B 53201 (by norm_num) ⟨26600, by rfl⟩ (by norm_num))
theorem R404021 : Reach 404021 := rs (se 5 (by rfl) ⟨18938, by rfl⟩) (B 37877 (by norm_num) ⟨18938, by rfl⟩ (by norm_num))
theorem R207413 : Reach 207413 := rs (se 5 (by rfl) ⟨9722, by rfl⟩) (B 19445 (by norm_num) ⟨9722, by rfl⟩ (by norm_num))
theorem R141893 : Reach 141893 := rs (se 4 (by rfl) ⟨13302, by rfl⟩) (B 26605 (by norm_num) ⟨13302, by rfl⟩ (by norm_num))
theorem R240205 : Reach 240205 := rs (se 3 (by rfl) ⟨45038, by rfl⟩) (B 90077 (by norm_num) ⟨45038, by rfl⟩ (by norm_num))
theorem R141917 : Reach 141917 := rs (se 3 (by rfl) ⟨26609, by rfl⟩) (B 53219 (by norm_num) ⟨26609, by rfl⟩ (by norm_num))
theorem R141941 : Reach 141941 := rs (se 5 (by rfl) ⟨6653, by rfl⟩) (B 13307 (by norm_num) ⟨6653, by rfl⟩ (by norm_num))
theorem R207485 : Reach 207485 := rs (se 3 (by rfl) ⟨38903, by rfl⟩) (B 77807 (by norm_num) ⟨38903, by rfl⟩ (by norm_num))
theorem R469637 : Reach 469637 := rs (se 4 (by rfl) ⟨44028, by rfl⟩) (B 88057 (by norm_num) ⟨44028, by rfl⟩ (by norm_num))
theorem R141965 : Reach 141965 := rs (se 3 (by rfl) ⟨26618, by rfl⟩) (B 53237 (by norm_num) ⟨26618, by rfl⟩ (by norm_num))
theorem R141989 : Reach 141989 := rs (se 4 (by rfl) ⟨13311, by rfl⟩) (B 26623 (by norm_num) ⟨13311, by rfl⟩ (by norm_num))
theorem R240317 : Reach 240317 := rs (se 3 (by rfl) ⟨45059, by rfl⟩) (B 90119 (by norm_num) ⟨45059, by rfl⟩ (by norm_num))
theorem R142013 : Reach 142013 := rs (se 3 (by rfl) ⟨26627, by rfl⟩) (B 53255 (by norm_num) ⟨26627, by rfl⟩ (by norm_num))
theorem R207557 : Reach 207557 := rs (se 4 (by rfl) ⟨19458, by rfl⟩) (B 38917 (by norm_num) ⟨19458, by rfl⟩ (by norm_num))
theorem R142037 : Reach 142037 := rs (se 7 (by rfl) ⟨1664, by rfl⟩) (B 3329 (by norm_num) ⟨1664, by rfl⟩ (by norm_num))
theorem R240365 : Reach 240365 := rs (se 3 (by rfl) ⟨45068, by rfl⟩) (B 90137 (by norm_num) ⟨45068, by rfl⟩ (by norm_num))
theorem R142061 : Reach 142061 := rs (se 3 (by rfl) ⟨26636, by rfl⟩) (B 53273 (by norm_num) ⟨26636, by rfl⟩ (by norm_num))
theorem R142085 : Reach 142085 := rs (se 4 (by rfl) ⟨13320, by rfl⟩) (B 26641 (by norm_num) ⟨13320, by rfl⟩ (by norm_num))
theorem R207629 : Reach 207629 := rs (se 3 (by rfl) ⟨38930, by rfl⟩) (B 77861 (by norm_num) ⟨38930, by rfl⟩ (by norm_num))
theorem R174869 : Reach 174869 := rs (se 6 (by rfl) ⟨4098, by rfl⟩) (B 8197 (by norm_num) ⟨4098, by rfl⟩ (by norm_num))
theorem R142109 : Reach 142109 := rs (se 3 (by rfl) ⟨26645, by rfl⟩) (B 53291 (by norm_num) ⟨26645, by rfl⟩ (by norm_num))
theorem R142133 : Reach 142133 := rs (se 5 (by rfl) ⟨6662, by rfl⟩) (B 13325 (by norm_num) ⟨6662, by rfl⟩ (by norm_num))
theorem R142157 : Reach 142157 := rs (se 3 (by rfl) ⟨26654, by rfl⟩) (B 53309 (by norm_num) ⟨26654, by rfl⟩ (by norm_num))
theorem R207701 : Reach 207701 := rs (se 9 (by rfl) ⟨608, by rfl⟩) (B 1217 (by norm_num) ⟨608, by rfl⟩ (by norm_num))
theorem R142181 : Reach 142181 := rs (se 4 (by rfl) ⟨13329, by rfl⟩) (B 26659 (by norm_num) ⟨13329, by rfl⟩ (by norm_num))
theorem R142205 : Reach 142205 := rs (se 3 (by rfl) ⟨26663, by rfl⟩) (B 53327 (by norm_num) ⟨26663, by rfl⟩ (by norm_num))
theorem R240509 : Reach 240509 := rs (se 3 (by rfl) ⟨45095, by rfl⟩) (B 90191 (by norm_num) ⟨45095, by rfl⟩ (by norm_num))
theorem R142229 : Reach 142229 := rs (se 6 (by rfl) ⟨3333, by rfl⟩) (B 6667 (by norm_num) ⟨3333, by rfl⟩ (by norm_num))
theorem R732053 : Reach 732053 := rs (se 6 (by rfl) ⟨17157, by rfl⟩) (B 34315 (by norm_num) ⟨17157, by rfl⟩ (by norm_num))
theorem R207773 : Reach 207773 := rs (se 3 (by rfl) ⟨38957, by rfl⟩) (B 77915 (by norm_num) ⟨38957, by rfl⟩ (by norm_num))
theorem R142253 : Reach 142253 := rs (se 3 (by rfl) ⟨26672, by rfl⟩) (B 53345 (by norm_num) ⟨26672, by rfl⟩ (by norm_num))
theorem R142277 : Reach 142277 := rs (se 4 (by rfl) ⟨13338, by rfl⟩) (B 26677 (by norm_num) ⟨13338, by rfl⟩ (by norm_num))
theorem R142301 : Reach 142301 := rs (se 3 (by rfl) ⟨26681, by rfl⟩) (B 53363 (by norm_num) ⟨26681, by rfl⟩ (by norm_num))
theorem R207845 : Reach 207845 := rs (se 4 (by rfl) ⟨19485, by rfl⟩) (B 38971 (by norm_num) ⟨19485, by rfl⟩ (by norm_num))
theorem R142325 : Reach 142325 := rs (se 5 (by rfl) ⟨6671, by rfl⟩) (B 13343 (by norm_num) ⟨6671, by rfl⟩ (by norm_num))
theorem R142349 : Reach 142349 := rs (se 3 (by rfl) ⟨26690, by rfl⟩) (B 53381 (by norm_num) ⟨26690, by rfl⟩ (by norm_num))
theorem R142373 : Reach 142373 := rs (se 4 (by rfl) ⟨13347, by rfl⟩) (B 26695 (by norm_num) ⟨13347, by rfl⟩ (by norm_num))
theorem R207917 : Reach 207917 := rs (se 3 (by rfl) ⟨38984, by rfl⟩) (B 77969 (by norm_num) ⟨38984, by rfl⟩ (by norm_num))
theorem R142397 : Reach 142397 := rs (se 3 (by rfl) ⟨26699, by rfl⟩) (B 53399 (by norm_num) ⟨26699, by rfl⟩ (by norm_num))
theorem R142421 : Reach 142421 := rs (se 8 (by rfl) ⟨834, by rfl⟩) (B 1669 (by norm_num) ⟨834, by rfl⟩ (by norm_num))
theorem R142445 : Reach 142445 := rs (se 3 (by rfl) ⟨26708, by rfl⟩) (B 53417 (by norm_num) ⟨26708, by rfl⟩ (by norm_num))
theorem R207989 : Reach 207989 := rs (se 5 (by rfl) ⟨9749, by rfl⟩) (B 19499 (by norm_num) ⟨9749, by rfl⟩ (by norm_num))
theorem R142469 : Reach 142469 := rs (se 4 (by rfl) ⟨13356, by rfl⟩) (B 26713 (by norm_num) ⟨13356, by rfl⟩ (by norm_num))
theorem R142493 : Reach 142493 := rs (se 3 (by rfl) ⟨26717, by rfl⟩) (B 53435 (by norm_num) ⟨26717, by rfl⟩ (by norm_num))
theorem R142517 : Reach 142517 := rs (se 5 (by rfl) ⟨6680, by rfl⟩) (B 13361 (by norm_num) ⟨6680, by rfl⟩ (by norm_num))
theorem R208061 : Reach 208061 := rs (se 3 (by rfl) ⟨39011, by rfl⟩) (B 78023 (by norm_num) ⟨39011, by rfl⟩ (by norm_num))
theorem R142541 : Reach 142541 := rs (se 3 (by rfl) ⟨26726, by rfl⟩) (B 53453 (by norm_num) ⟨26726, by rfl⟩ (by norm_num))
theorem R142565 : Reach 142565 := rs (se 4 (by rfl) ⟨13365, by rfl⟩) (B 26731 (by norm_num) ⟨13365, by rfl⟩ (by norm_num))
theorem R142589 : Reach 142589 := rs (se 3 (by rfl) ⟨26735, by rfl⟩) (B 53471 (by norm_num) ⟨26735, by rfl⟩ (by norm_num))
theorem R208133 : Reach 208133 := rs (se 4 (by rfl) ⟨19512, by rfl⟩) (B 39025 (by norm_num) ⟨19512, by rfl⟩ (by norm_num))
theorem R142613 : Reach 142613 := rs (se 6 (by rfl) ⟨3342, by rfl⟩) (B 6685 (by norm_num) ⟨3342, by rfl⟩ (by norm_num))
theorem R142637 : Reach 142637 := rs (se 3 (by rfl) ⟨26744, by rfl⟩) (B 53489 (by norm_num) ⟨26744, by rfl⟩ (by norm_num))
theorem R142661 : Reach 142661 := rs (se 4 (by rfl) ⟨13374, by rfl⟩) (B 26749 (by norm_num) ⟨13374, by rfl⟩ (by norm_num))
theorem R208205 : Reach 208205 := rs (se 3 (by rfl) ⟨39038, by rfl⟩) (B 78077 (by norm_num) ⟨39038, by rfl⟩ (by norm_num))
theorem R142685 : Reach 142685 := rs (se 3 (by rfl) ⟨26753, by rfl⟩) (B 53507 (by norm_num) ⟨26753, by rfl⟩ (by norm_num))
theorem R208277 : Reach 208277 := rs (se 6 (by rfl) ⟨4881, by rfl⟩) (B 9763 (by norm_num) ⟨4881, by rfl⟩ (by norm_num))
theorem R110045 : Reach 110045 := rs (se 3 (by rfl) ⟨20633, by rfl⟩) (B 41267 (by norm_num) ⟨20633, by rfl⟩ (by norm_num))
theorem R208349 : Reach 208349 := rs (se 3 (by rfl) ⟨39065, by rfl⟩) (B 78131 (by norm_num) ⟨39065, by rfl⟩ (by norm_num))
theorem R175621 : Reach 175621 := rs (se 4 (by rfl) ⟨16464, by rfl⟩) (B 32929 (by norm_num) ⟨16464, by rfl⟩ (by norm_num))
theorem R208421 : Reach 208421 := rs (se 4 (by rfl) ⟨19539, by rfl⟩) (B 39079 (by norm_num) ⟨19539, by rfl⟩ (by norm_num))
theorem R208493 : Reach 208493 := rs (se 3 (by rfl) ⟨39092, by rfl⟩) (B 78185 (by norm_num) ⟨39092, by rfl⟩ (by norm_num))
theorem R175765 : Reach 175765 := rs (se 6 (by rfl) ⟨4119, by rfl⟩) (B 8239 (by norm_num) ⟨4119, by rfl⟩ (by norm_num))
theorem R208565 : Reach 208565 := rs (se 5 (by rfl) ⟨9776, by rfl⟩) (B 19553 (by norm_num) ⟨9776, by rfl⟩ (by norm_num))
theorem R208637 : Reach 208637 := rs (se 3 (by rfl) ⟨39119, by rfl⟩) (B 78239 (by norm_num) ⟨39119, by rfl⟩ (by norm_num))
theorem R306965 : Reach 306965 := rs (se 6 (by rfl) ⟨7194, by rfl⟩) (B 14389 (by norm_num) ⟨7194, by rfl⟩ (by norm_num))
theorem R110381 : Reach 110381 := rs (se 3 (by rfl) ⟨20696, by rfl⟩) (B 41393 (by norm_num) ⟨20696, by rfl⟩ (by norm_num))
theorem R175925 : Reach 175925 := rs (se 5 (by rfl) ⟨8246, by rfl⟩) (B 16493 (by norm_num) ⟨8246, by rfl⟩ (by norm_num))
theorem R208709 : Reach 208709 := rs (se 4 (by rfl) ⟨19566, by rfl⟩) (B 39133 (by norm_num) ⟨19566, by rfl⟩ (by norm_num))
theorem R634709 : Reach 634709 := rs (se 9 (by rfl) ⟨1859, by rfl⟩) (B 3719 (by norm_num) ⟨1859, by rfl⟩ (by norm_num))
theorem R208781 : Reach 208781 := rs (se 3 (by rfl) ⟨39146, by rfl⟩) (B 78293 (by norm_num) ⟨39146, by rfl⟩ (by norm_num))
theorem R470933 : Reach 470933 := rs (se 6 (by rfl) ⟨11037, by rfl⟩) (B 22075 (by norm_num) ⟨11037, by rfl⟩ (by norm_num))
theorem R110497 : Reach 110497 := rs (se 2 (by rfl) ⟨41436, by rfl⟩) (B 82873 (by norm_num) ⟨41436, by rfl⟩ (by norm_num))
theorem R110521 : Reach 110521 := rs (se 2 (by rfl) ⟨41445, by rfl⟩) (B 82891 (by norm_num) ⟨41445, by rfl⟩ (by norm_num))
theorem R176069 : Reach 176069 := rs (se 4 (by rfl) ⟨16506, by rfl⟩) (B 33013 (by norm_num) ⟨16506, by rfl⟩ (by norm_num))
theorem R208853 : Reach 208853 := rs (se 7 (by rfl) ⟨2447, by rfl⟩) (B 4895 (by norm_num) ⟨2447, by rfl⟩ (by norm_num))
theorem R208925 : Reach 208925 := rs (se 3 (by rfl) ⟨39173, by rfl⟩) (B 78347 (by norm_num) ⟨39173, by rfl⟩ (by norm_num))
theorem R208997 : Reach 208997 := rs (se 4 (by rfl) ⟨19593, by rfl⟩) (B 39187 (by norm_num) ⟨19593, by rfl⟩ (by norm_num))
theorem R209069 : Reach 209069 := rs (se 3 (by rfl) ⟨39200, by rfl⟩) (B 78401 (by norm_num) ⟨39200, by rfl⟩ (by norm_num))
theorem R307381 : Reach 307381 := rs (se 5 (by rfl) ⟨14408, by rfl⟩) (B 28817 (by norm_num) ⟨14408, by rfl⟩ (by norm_num))
theorem R176357 : Reach 176357 := rs (se 4 (by rfl) ⟨16533, by rfl⟩) (B 33067 (by norm_num) ⟨16533, by rfl⟩ (by norm_num))
theorem R209141 : Reach 209141 := rs (se 5 (by rfl) ⟨9803, by rfl⟩) (B 19607 (by norm_num) ⟨9803, by rfl⟩ (by norm_num))
theorem R209213 : Reach 209213 := rs (se 3 (by rfl) ⟨39227, by rfl⟩) (B 78455 (by norm_num) ⟨39227, by rfl⟩ (by norm_num))
theorem R176509 : Reach 176509 := rs (se 3 (by rfl) ⟨33095, by rfl⟩) (B 66191 (by norm_num) ⟨33095, by rfl⟩ (by norm_num))
theorem R209285 : Reach 209285 := rs (se 4 (by rfl) ⟨19620, by rfl⟩) (B 39241 (by norm_num) ⟨19620, by rfl⟩ (by norm_num))
theorem R307637 : Reach 307637 := rs (se 5 (by rfl) ⟨14420, by rfl⟩) (B 28841 (by norm_num) ⟨14420, by rfl⟩ (by norm_num))
theorem R209357 : Reach 209357 := rs (se 3 (by rfl) ⟨39254, by rfl⟩) (B 78509 (by norm_num) ⟨39254, by rfl⟩ (by norm_num))
theorem R766421 : Reach 766421 := rs (se 7 (by rfl) ⟨8981, by rfl⟩) (B 17963 (by norm_num) ⟨8981, by rfl⟩ (by norm_num))
theorem R209429 : Reach 209429 := rs (se 6 (by rfl) ⟨4908, by rfl⟩) (B 9817 (by norm_num) ⟨4908, by rfl⟩ (by norm_num))
theorem R209501 : Reach 209501 := rs (se 3 (by rfl) ⟨39281, by rfl⟩) (B 78563 (by norm_num) ⟨39281, by rfl⟩ (by norm_num))
theorem R111217 : Reach 111217 := rs (se 2 (by rfl) ⟨41706, by rfl⟩) (B 83413 (by norm_num) ⟨41706, by rfl⟩ (by norm_num))
theorem R209573 : Reach 209573 := rs (se 4 (by rfl) ⟨19647, by rfl⟩) (B 39295 (by norm_num) ⟨19647, by rfl⟩ (by norm_num))
theorem R176813 : Reach 176813 := rs (se 3 (by rfl) ⟨33152, by rfl⟩) (B 66305 (by norm_num) ⟨33152, by rfl⟩ (by norm_num))
theorem R111313 : Reach 111313 := rs (se 2 (by rfl) ⟨41742, by rfl⟩) (B 83485 (by norm_num) ⟨41742, by rfl⟩ (by norm_num))
theorem R209645 : Reach 209645 := rs (se 3 (by rfl) ⟨39308, by rfl⟩) (B 78617 (by norm_num) ⟨39308, by rfl⟩ (by norm_num))
theorem R144173 : Reach 144173 := rs (se 3 (by rfl) ⟨27032, by rfl⟩) (B 54065 (by norm_num) ⟨27032, by rfl⟩ (by norm_num))
theorem R209717 : Reach 209717 := rs (se 5 (by rfl) ⟨9830, by rfl⟩) (B 19661 (by norm_num) ⟨9830, by rfl⟩ (by norm_num))
theorem R308069 : Reach 308069 := rs (se 4 (by rfl) ⟨28881, by rfl⟩) (B 57763 (by norm_num) ⟨28881, by rfl⟩ (by norm_num))
theorem R209789 : Reach 209789 := rs (se 3 (by rfl) ⟨39335, by rfl⟩) (B 78671 (by norm_num) ⟨39335, by rfl⟩ (by norm_num))
theorem R209861 : Reach 209861 := rs (se 4 (by rfl) ⟨19674, by rfl⟩) (B 39349 (by norm_num) ⟨19674, by rfl⟩ (by norm_num))
theorem R898037 : Reach 898037 := rs (se 5 (by rfl) ⟨42095, by rfl⟩) (B 84191 (by norm_num) ⟨42095, by rfl⟩ (by norm_num))
theorem R209933 : Reach 209933 := rs (se 3 (by rfl) ⟨39362, by rfl⟩) (B 78725 (by norm_num) ⟨39362, by rfl⟩ (by norm_num))
theorem R210005 : Reach 210005 := rs (se 8 (by rfl) ⟨1230, by rfl⟩) (B 2461 (by norm_num) ⟨1230, by rfl⟩ (by norm_num))
theorem R210077 : Reach 210077 := rs (se 3 (by rfl) ⟨39389, by rfl⟩) (B 78779 (by norm_num) ⟨39389, by rfl⟩ (by norm_num))
theorem R472229 : Reach 472229 := rs (se 4 (by rfl) ⟨44271, by rfl⟩) (B 88543 (by norm_num) ⟨44271, by rfl⟩ (by norm_num))
theorem R210149 : Reach 210149 := rs (se 4 (by rfl) ⟨19701, by rfl⟩) (B 39403 (by norm_num) ⟨19701, by rfl⟩ (by norm_num))
theorem R308501 : Reach 308501 := rs (se 6 (by rfl) ⟨7230, by rfl⟩) (B 14461 (by norm_num) ⟨7230, by rfl⟩ (by norm_num))
theorem R210221 : Reach 210221 := rs (se 3 (by rfl) ⟨39416, by rfl⟩) (B 78833 (by norm_num) ⟨39416, by rfl⟩ (by norm_num))
theorem R210293 : Reach 210293 := rs (se 5 (by rfl) ⟨9857, by rfl⟩) (B 19715 (by norm_num) ⟨9857, by rfl⟩ (by norm_num))
theorem R177565 : Reach 177565 := rs (se 3 (by rfl) ⟨33293, by rfl⟩) (B 66587 (by norm_num) ⟨33293, by rfl⟩ (by norm_num))
theorem R210365 : Reach 210365 := rs (se 3 (by rfl) ⟨39443, by rfl⟩) (B 78887 (by norm_num) ⟨39443, by rfl⟩ (by norm_num))
theorem R210437 : Reach 210437 := rs (se 4 (by rfl) ⟨19728, by rfl⟩) (B 39457 (by norm_num) ⟨19728, by rfl⟩ (by norm_num))
theorem R177709 : Reach 177709 := rs (se 3 (by rfl) ⟨33320, by rfl⟩) (B 66641 (by norm_num) ⟨33320, by rfl⟩ (by norm_num))
theorem R210509 : Reach 210509 := rs (se 3 (by rfl) ⟨39470, by rfl⟩) (B 78941 (by norm_num) ⟨39470, by rfl⟩ (by norm_num))
theorem R177797 : Reach 177797 := rs (se 4 (by rfl) ⟨16668, by rfl⟩) (B 33337 (by norm_num) ⟨16668, by rfl⟩ (by norm_num))
theorem R210581 : Reach 210581 := rs (se 6 (by rfl) ⟨4935, by rfl⟩) (B 9871 (by norm_num) ⟨4935, by rfl⟩ (by norm_num))
theorem R112313 : Reach 112313 := rs (se 2 (by rfl) ⟨42117, by rfl⟩) (B 84235 (by norm_num) ⟨42117, by rfl⟩ (by norm_num))
theorem R308933 : Reach 308933 := rs (se 4 (by rfl) ⟨28962, by rfl⟩) (B 57925 (by norm_num) ⟨28962, by rfl⟩ (by norm_num))
theorem R177869 : Reach 177869 := rs (se 3 (by rfl) ⟨33350, by rfl⟩) (B 66701 (by norm_num) ⟨33350, by rfl⟩ (by norm_num))
theorem R210653 : Reach 210653 := rs (se 3 (by rfl) ⟨39497, by rfl⟩) (B 78995 (by norm_num) ⟨39497, by rfl⟩ (by norm_num))
theorem R243445 : Reach 243445 := rs (se 5 (by rfl) ⟨11411, by rfl⟩) (B 22823 (by norm_num) ⟨11411, by rfl⟩ (by norm_num))
theorem R210725 : Reach 210725 := rs (se 4 (by rfl) ⟨19755, by rfl⟩) (B 39511 (by norm_num) ⟨19755, by rfl⟩ (by norm_num))
theorem R177965 : Reach 177965 := rs (se 3 (by rfl) ⟨33368, by rfl⟩) (B 66737 (by norm_num) ⟨33368, by rfl⟩ (by norm_num))
theorem R178013 : Reach 178013 := rs (se 3 (by rfl) ⟨33377, by rfl⟩) (B 66755 (by norm_num) ⟨33377, by rfl⟩ (by norm_num))
theorem R210797 : Reach 210797 := rs (se 3 (by rfl) ⟨39524, by rfl⟩) (B 79049 (by norm_num) ⟨39524, by rfl⟩ (by norm_num))
theorem R145309 : Reach 145309 := rs (se 3 (by rfl) ⟨27245, by rfl⟩) (B 54491 (by norm_num) ⟨27245, by rfl⟩ (by norm_num))
theorem R210869 : Reach 210869 := rs (se 5 (by rfl) ⟨9884, by rfl⟩) (B 19769 (by norm_num) ⟨9884, by rfl⟩ (by norm_num))
theorem R112601 : Reach 112601 := rs (se 2 (by rfl) ⟨42225, by rfl⟩) (B 84451 (by norm_num) ⟨42225, by rfl⟩ (by norm_num))
theorem R210941 : Reach 210941 := rs (se 3 (by rfl) ⟨39551, by rfl⟩) (B 79103 (by norm_num) ⟨39551, by rfl⟩ (by norm_num))
theorem R211013 : Reach 211013 := rs (se 4 (by rfl) ⟨19782, by rfl⟩) (B 39565 (by norm_num) ⟨19782, by rfl⟩ (by norm_num))
theorem R309365 : Reach 309365 := rs (se 5 (by rfl) ⟨14501, by rfl⟩) (B 29003 (by norm_num) ⟨14501, by rfl⟩ (by norm_num))
theorem R112765 : Reach 112765 := rs (se 3 (by rfl) ⟨21143, by rfl⟩) (B 42287 (by norm_num) ⟨21143, by rfl⟩ (by norm_num))
theorem R178301 : Reach 178301 := rs (se 3 (by rfl) ⟨33431, by rfl⟩) (B 66863 (by norm_num) ⟨33431, by rfl⟩ (by norm_num))
theorem R211085 : Reach 211085 := rs (se 3 (by rfl) ⟨39578, by rfl⟩) (B 79157 (by norm_num) ⟨39578, by rfl⟩ (by norm_num))
theorem R112793 : Reach 112793 := rs (se 2 (by rfl) ⟨42297, by rfl⟩) (B 84595 (by norm_num) ⟨42297, by rfl⟩ (by norm_num))
theorem R211157 : Reach 211157 := rs (se 7 (by rfl) ⟨2474, by rfl⟩) (B 4949 (by norm_num) ⟨2474, by rfl⟩ (by norm_num))
theorem R112909 : Reach 112909 := rs (se 3 (by rfl) ⟨21170, by rfl⟩) (B 42341 (by norm_num) ⟨21170, by rfl⟩ (by norm_num))
theorem R178453 : Reach 178453 := rs (se 6 (by rfl) ⟨4182, by rfl⟩) (B 8365 (by norm_num) ⟨4182, by rfl⟩ (by norm_num))
theorem R211229 : Reach 211229 := rs (se 3 (by rfl) ⟨39605, by rfl⟩) (B 79211 (by norm_num) ⟨39605, by rfl⟩ (by norm_num))
theorem R899381 : Reach 899381 := rs (se 5 (by rfl) ⟨42158, by rfl⟩) (B 84317 (by norm_num) ⟨42158, by rfl⟩ (by norm_num))
theorem R211301 : Reach 211301 := rs (se 4 (by rfl) ⟨19809, by rfl⟩) (B 39619 (by norm_num) ⟨19809, by rfl⟩ (by norm_num))
theorem R113005 : Reach 113005 := rs (se 3 (by rfl) ⟨21188, by rfl⟩) (B 42377 (by norm_num) ⟨21188, by rfl⟩ (by norm_num))
theorem R211373 : Reach 211373 := rs (se 3 (by rfl) ⟨39632, by rfl⟩) (B 79265 (by norm_num) ⟨39632, by rfl⟩ (by norm_num))
theorem R473525 : Reach 473525 := rs (se 5 (by rfl) ⟨22196, by rfl⟩) (B 44393 (by norm_num) ⟨22196, by rfl⟩ (by norm_num))
theorem R211445 : Reach 211445 := rs (se 5 (by rfl) ⟨9911, by rfl⟩) (B 19823 (by norm_num) ⟨9911, by rfl⟩ (by norm_num))
theorem R309797 : Reach 309797 := rs (se 4 (by rfl) ⟨29043, by rfl⟩) (B 58087 (by norm_num) ⟨29043, by rfl⟩ (by norm_num))
theorem R211517 : Reach 211517 := rs (se 3 (by rfl) ⟨39659, by rfl⟩) (B 79319 (by norm_num) ⟨39659, by rfl⟩ (by norm_num))
theorem R178757 : Reach 178757 := rs (se 4 (by rfl) ⟨16758, by rfl⟩) (B 33517 (by norm_num) ⟨16758, by rfl⟩ (by norm_num))
theorem R211589 : Reach 211589 := rs (se 4 (by rfl) ⟨19836, by rfl⟩) (B 39673 (by norm_num) ⟨19836, by rfl⟩ (by norm_num))
theorem R211661 : Reach 211661 := rs (se 3 (by rfl) ⟨39686, by rfl⟩) (B 79373 (by norm_num) ⟨39686, by rfl⟩ (by norm_num))
theorem R211733 : Reach 211733 := rs (se 6 (by rfl) ⟨4962, by rfl⟩) (B 9925 (by norm_num) ⟨4962, by rfl⟩ (by norm_num))
theorem R113485 : Reach 113485 := rs (se 3 (by rfl) ⟨21278, by rfl⟩) (B 42557 (by norm_num) ⟨21278, by rfl⟩ (by norm_num))
theorem R211805 : Reach 211805 := rs (se 3 (by rfl) ⟨39713, by rfl⟩) (B 79427 (by norm_num) ⟨39713, by rfl⟩ (by norm_num))
theorem R1096597 : Reach 1096597 := rs (se 6 (by rfl) ⟨25701, by rfl⟩) (B 51403 (by norm_num) ⟨25701, by rfl⟩ (by norm_num))
theorem R211877 : Reach 211877 := rs (se 4 (by rfl) ⟨19863, by rfl⟩) (B 39727 (by norm_num) ⟨19863, by rfl⟩ (by norm_num))
theorem R310229 : Reach 310229 := rs (se 7 (by rfl) ⟨3635, by rfl⟩) (B 7271 (by norm_num) ⟨3635, by rfl⟩ (by norm_num))
theorem R211949 : Reach 211949 := rs (se 3 (by rfl) ⟨39740, by rfl⟩) (B 79481 (by norm_num) ⟨39740, by rfl⟩ (by norm_num))
theorem R769013 : Reach 769013 := rs (se 5 (by rfl) ⟨36047, by rfl⟩) (B 72095 (by norm_num) ⟨36047, by rfl⟩ (by norm_num))
theorem R212021 : Reach 212021 := rs (se 5 (by rfl) ⟨9938, by rfl⟩) (B 19877 (by norm_num) ⟨9938, by rfl⟩ (by norm_num))
theorem R212093 : Reach 212093 := rs (se 3 (by rfl) ⟨39767, by rfl⟩) (B 79535 (by norm_num) ⟨39767, by rfl⟩ (by norm_num))
theorem R474245 : Reach 474245 := rs (se 4 (by rfl) ⟨44460, by rfl⟩) (B 88921 (by norm_num) ⟨44460, by rfl⟩ (by norm_num))
theorem R179381 : Reach 179381 := rs (se 5 (by rfl) ⟨8408, by rfl⟩) (B 16817 (by norm_num) ⟨8408, by rfl⟩ (by norm_num))
theorem R212165 : Reach 212165 := rs (se 4 (by rfl) ⟨19890, by rfl⟩) (B 39781 (by norm_num) ⟨19890, by rfl⟩ (by norm_num))
theorem R212237 : Reach 212237 := rs (se 3 (by rfl) ⟨39794, by rfl⟩) (B 79589 (by norm_num) ⟨39794, by rfl⟩ (by norm_num))
theorem R179509 : Reach 179509 := rs (se 5 (by rfl) ⟨8414, by rfl⟩) (B 16829 (by norm_num) ⟨8414, by rfl⟩ (by norm_num))
theorem R146765 : Reach 146765 := rs (se 3 (by rfl) ⟨27518, by rfl⟩) (B 55037 (by norm_num) ⟨27518, by rfl⟩ (by norm_num))
theorem R212309 : Reach 212309 := rs (se 11 (by rfl) ⟨155, by rfl⟩) (B 311 (by norm_num) ⟨155, by rfl⟩ (by norm_num))
theorem R310661 : Reach 310661 := rs (se 4 (by rfl) ⟨29124, by rfl⟩) (B 58249 (by norm_num) ⟨29124, by rfl⟩ (by norm_num))
theorem R540053 : Reach 540053 := rs (se 6 (by rfl) ⟨12657, by rfl⟩) (B 25315 (by norm_num) ⟨12657, by rfl⟩ (by norm_num))
theorem R212381 : Reach 212381 := rs (se 3 (by rfl) ⟨39821, by rfl⟩) (B 79643 (by norm_num) ⟨39821, by rfl⟩ (by norm_num))
theorem R179653 : Reach 179653 := rs (se 4 (by rfl) ⟨16842, by rfl⟩) (B 33685 (by norm_num) ⟨16842, by rfl⟩ (by norm_num))
theorem R212453 : Reach 212453 := rs (se 4 (by rfl) ⟨19917, by rfl⟩) (B 39835 (by norm_num) ⟨19917, by rfl⟩ (by norm_num))
theorem R605717 : Reach 605717 := rs (se 6 (by rfl) ⟨14196, by rfl⟩) (B 28393 (by norm_num) ⟨14196, by rfl⟩ (by norm_num))
theorem R212525 : Reach 212525 := rs (se 3 (by rfl) ⟨39848, by rfl⟩) (B 79697 (by norm_num) ⟨39848, by rfl⟩ (by norm_num))
theorem R179813 : Reach 179813 := rs (se 4 (by rfl) ⟨16857, by rfl⟩) (B 33715 (by norm_num) ⟨16857, by rfl⟩ (by norm_num))
theorem R147053 : Reach 147053 := rs (se 3 (by rfl) ⟨27572, by rfl⟩) (B 55145 (by norm_num) ⟨27572, by rfl⟩ (by norm_num))
theorem R212597 : Reach 212597 := rs (se 5 (by rfl) ⟨9965, by rfl⟩) (B 19931 (by norm_num) ⟨9965, by rfl⟩ (by norm_num))
theorem R212669 : Reach 212669 := rs (se 3 (by rfl) ⟨39875, by rfl⟩) (B 79751 (by norm_num) ⟨39875, by rfl⟩ (by norm_num))
theorem R474821 : Reach 474821 := rs (se 4 (by rfl) ⟨44514, by rfl⟩) (B 89029 (by norm_num) ⟨44514, by rfl⟩ (by norm_num))
theorem R704213 : Reach 704213 := rs (se 7 (by rfl) ⟨8252, by rfl⟩) (B 16505 (by norm_num) ⟨8252, by rfl⟩ (by norm_num))
theorem R179957 : Reach 179957 := rs (se 5 (by rfl) ⟨8435, by rfl⟩) (B 16871 (by norm_num) ⟨8435, by rfl⟩ (by norm_num))
theorem R212741 : Reach 212741 := rs (se 4 (by rfl) ⟨19944, by rfl⟩) (B 39889 (by norm_num) ⟨19944, by rfl⟩ (by norm_num))
theorem R311093 : Reach 311093 := rs (se 5 (by rfl) ⟨14582, by rfl⟩) (B 29165 (by norm_num) ⟨14582, by rfl⟩ (by norm_num))
theorem R212813 : Reach 212813 := rs (se 3 (by rfl) ⟨39902, by rfl⟩) (B 79805 (by norm_num) ⟨39902, by rfl⟩ (by norm_num))
theorem R212885 : Reach 212885 := rs (se 6 (by rfl) ⟨4989, by rfl⟩) (B 9979 (by norm_num) ⟨4989, by rfl⟩ (by norm_num))
theorem R507829 : Reach 507829 := rs (se 5 (by rfl) ⟨23804, by rfl⟩) (B 47609 (by norm_num) ⟨23804, by rfl⟩ (by norm_num))
theorem R212957 : Reach 212957 := rs (se 3 (by rfl) ⟨39929, by rfl⟩) (B 79859 (by norm_num) ⟨39929, by rfl⟩ (by norm_num))
theorem R147469 : Reach 147469 := rs (se 3 (by rfl) ⟨27650, by rfl⟩) (B 55301 (by norm_num) ⟨27650, by rfl⟩ (by norm_num))
theorem R180245 : Reach 180245 := rs (se 6 (by rfl) ⟨4224, by rfl⟩) (B 8449 (by norm_num) ⟨4224, by rfl⟩ (by norm_num))
theorem R213029 : Reach 213029 := rs (se 4 (by rfl) ⟨19971, by rfl⟩) (B 39943 (by norm_num) ⟨19971, by rfl⟩ (by norm_num))
theorem R213101 : Reach 213101 := rs (se 3 (by rfl) ⟨39956, by rfl⟩) (B 79913 (by norm_num) ⟨39956, by rfl⟩ (by norm_num))
theorem R180397 : Reach 180397 := rs (se 3 (by rfl) ⟨33824, by rfl⟩) (B 67649 (by norm_num) ⟨33824, by rfl⟩ (by norm_num))
theorem R213173 : Reach 213173 := rs (se 5 (by rfl) ⟨9992, by rfl⟩) (B 19985 (by norm_num) ⟨9992, by rfl⟩ (by norm_num))
theorem R377045 : Reach 377045 := rs (se 7 (by rfl) ⟨4418, by rfl⟩) (B 8837 (by norm_num) ⟨4418, by rfl⟩ (by norm_num))
theorem R311525 : Reach 311525 := rs (se 4 (by rfl) ⟨29205, by rfl⟩) (B 58411 (by norm_num) ⟨29205, by rfl⟩ (by norm_num))
theorem R213229 : Reach 213229 := rs (se 3 (by rfl) ⟨39980, by rfl⟩) (B 79961 (by norm_num) ⟨39980, by rfl⟩ (by norm_num))
theorem R213245 : Reach 213245 := rs (se 3 (by rfl) ⟨39983, by rfl⟩) (B 79967 (by norm_num) ⟨39983, by rfl⟩ (by norm_num))
theorem R213317 : Reach 213317 := rs (se 4 (by rfl) ⟨19998, by rfl⟩) (B 39997 (by norm_num) ⟨19998, by rfl⟩ (by norm_num))
theorem R213389 : Reach 213389 := rs (se 3 (by rfl) ⟨40010, by rfl⟩) (B 80021 (by norm_num) ⟨40010, by rfl⟩ (by norm_num))
theorem R213461 : Reach 213461 := rs (se 7 (by rfl) ⟨2501, by rfl⟩) (B 5003 (by norm_num) ⟨2501, by rfl⟩ (by norm_num))
theorem R442853 : Reach 442853 := rs (se 4 (by rfl) ⟨41517, by rfl⟩) (B 83035 (by norm_num) ⟨41517, by rfl⟩ (by norm_num))
theorem R213533 : Reach 213533 := rs (se 3 (by rfl) ⟨40037, by rfl⟩) (B 80075 (by norm_num) ⟨40037, by rfl⟩ (by norm_num))
theorem R213605 : Reach 213605 := rs (se 4 (by rfl) ⟨20025, by rfl⟩) (B 40051 (by norm_num) ⟨20025, by rfl⟩ (by norm_num))
theorem R311957 : Reach 311957 := rs (se 6 (by rfl) ⟨7311, by rfl⟩) (B 14623 (by norm_num) ⟨7311, by rfl⟩ (by norm_num))
theorem R213677 : Reach 213677 := rs (se 3 (by rfl) ⟨40064, by rfl⟩) (B 80129 (by norm_num) ⟨40064, by rfl⟩ (by norm_num))
theorem R705205 : Reach 705205 := rs (se 5 (by rfl) ⟨33056, by rfl⟩) (B 66113 (by norm_num) ⟨33056, by rfl⟩ (by norm_num))
theorem R115445 : Reach 115445 := rs (se 5 (by rfl) ⟨5411, by rfl⟩) (B 10823 (by norm_num) ⟨5411, by rfl⟩ (by norm_num))
theorem R213749 : Reach 213749 := rs (se 5 (by rfl) ⟨10019, by rfl⟩) (B 20039 (by norm_num) ⟨10019, by rfl⟩ (by norm_num))
theorem R115501 : Reach 115501 := rs (se 3 (by rfl) ⟨21656, by rfl⟩) (B 43313 (by norm_num) ⟨21656, by rfl⟩ (by norm_num))
theorem R213821 : Reach 213821 := rs (se 3 (by rfl) ⟨40091, by rfl⟩) (B 80183 (by norm_num) ⟨40091, by rfl⟩ (by norm_num))
theorem R213893 : Reach 213893 := rs (se 4 (by rfl) ⟨20052, by rfl⟩) (B 40105 (by norm_num) ⟨20052, by rfl⟩ (by norm_num))
theorem R115597 : Reach 115597 := rs (se 3 (by rfl) ⟨21674, by rfl⟩) (B 43349 (by norm_num) ⟨21674, by rfl⟩ (by norm_num))
theorem R148405 : Reach 148405 := rs (se 5 (by rfl) ⟨6956, by rfl⟩) (B 13913 (by norm_num) ⟨6956, by rfl⟩ (by norm_num))
theorem R213965 : Reach 213965 := rs (se 3 (by rfl) ⟨40118, by rfl⟩) (B 80237 (by norm_num) ⟨40118, by rfl⟩ (by norm_num))
theorem R476117 : Reach 476117 := rs (se 7 (by rfl) ⟨5579, by rfl⟩) (B 11159 (by norm_num) ⟨5579, by rfl⟩ (by norm_num))
theorem R214037 : Reach 214037 := rs (se 6 (by rfl) ⟨5016, by rfl⟩) (B 10033 (by norm_num) ⟨5016, by rfl⟩ (by norm_num))
theorem R115769 : Reach 115769 := rs (se 2 (by rfl) ⟨43413, by rfl⟩) (B 86827 (by norm_num) ⟨43413, by rfl⟩ (by norm_num))
theorem R312389 : Reach 312389 := rs (se 4 (by rfl) ⟨29286, by rfl⟩) (B 58573 (by norm_num) ⟨29286, by rfl⟩ (by norm_num))
theorem R115825 : Reach 115825 := rs (se 2 (by rfl) ⟨43434, by rfl⟩) (B 86869 (by norm_num) ⟨43434, by rfl⟩ (by norm_num))
theorem R115921 : Reach 115921 := rs (se 2 (by rfl) ⟨43470, by rfl⟩) (B 86941 (by norm_num) ⟨43470, by rfl⟩ (by norm_num))
theorem R181597 : Reach 181597 := rs (se 3 (by rfl) ⟨34049, by rfl⟩) (B 68099 (by norm_num) ⟨34049, by rfl⟩ (by norm_num))
theorem R116093 : Reach 116093 := rs (se 3 (by rfl) ⟨21767, by rfl⟩) (B 43535 (by norm_num) ⟨21767, by rfl⟩ (by norm_num))
theorem R378245 : Reach 378245 := rs (se 4 (by rfl) ⟨35460, by rfl⟩) (B 70921 (by norm_num) ⟨35460, by rfl⟩ (by norm_num))
theorem R116149 : Reach 116149 := rs (se 5 (by rfl) ⟨5444, by rfl⟩) (B 10889 (by norm_num) ⟨5444, by rfl⟩ (by norm_num))
theorem R312821 : Reach 312821 := rs (se 5 (by rfl) ⟨14663, by rfl⟩) (B 29327 (by norm_num) ⟨14663, by rfl⟩ (by norm_num))
theorem R116245 : Reach 116245 := rs (se 6 (by rfl) ⟨2724, by rfl⟩) (B 5449 (by norm_num) ⟨2724, by rfl⟩ (by norm_num))
theorem R116417 : Reach 116417 := rs (se 2 (by rfl) ⟨43656, by rfl⟩) (B 87313 (by norm_num) ⟨43656, by rfl⟩ (by norm_num))
theorem R476869 : Reach 476869 := rs (se 4 (by rfl) ⟨44706, by rfl⟩) (B 89413 (by norm_num) ⟨44706, by rfl⟩ (by norm_num))
theorem R116473 : Reach 116473 := rs (se 2 (by rfl) ⟨43677, by rfl⟩) (B 87355 (by norm_num) ⟨43677, by rfl⟩ (by norm_num))
theorem R214829 : Reach 214829 := rs (se 3 (by rfl) ⟨40280, by rfl⟩) (B 80561 (by norm_num) ⟨40280, by rfl⟩ (by norm_num))
theorem R116569 : Reach 116569 := rs (se 2 (by rfl) ⟨43713, by rfl⟩) (B 87427 (by norm_num) ⟨43713, by rfl⟩ (by norm_num))
theorem R509813 : Reach 509813 := rs (se 5 (by rfl) ⟨23897, by rfl⟩) (B 47795 (by norm_num) ⟨23897, by rfl⟩ (by norm_num))
theorem R313253 : Reach 313253 := rs (se 4 (by rfl) ⟨29367, by rfl⟩) (B 58735 (by norm_num) ⟨29367, by rfl⟩ (by norm_num))
theorem R116741 : Reach 116741 := rs (se 4 (by rfl) ⟨10944, by rfl⟩) (B 21889 (by norm_num) ⟨10944, by rfl⟩ (by norm_num))
theorem R116797 : Reach 116797 := rs (se 3 (by rfl) ⟨21899, by rfl⟩) (B 43799 (by norm_num) ⟨21899, by rfl⟩ (by norm_num))
theorem R215117 : Reach 215117 := rs (se 3 (by rfl) ⟨40334, by rfl⟩) (B 80669 (by norm_num) ⟨40334, by rfl⟩ (by norm_num))
theorem R149597 : Reach 149597 := rs (se 3 (by rfl) ⟨28049, by rfl⟩) (B 56099 (by norm_num) ⟨28049, by rfl⟩ (by norm_num))
theorem R116893 : Reach 116893 := rs (se 3 (by rfl) ⟨21917, by rfl⟩) (B 43835 (by norm_num) ⟨21917, by rfl⟩ (by norm_num))
theorem R215245 : Reach 215245 := rs (se 3 (by rfl) ⟨40358, by rfl⟩) (B 80717 (by norm_num) ⟨40358, by rfl⟩ (by norm_num))
theorem R477413 : Reach 477413 := rs (se 4 (by rfl) ⟨44757, by rfl⟩) (B 89515 (by norm_num) ⟨44757, by rfl⟩ (by norm_num))
theorem R149789 : Reach 149789 := rs (se 3 (by rfl) ⟨28085, by rfl⟩) (B 56171 (by norm_num) ⟨28085, by rfl⟩ (by norm_num))
theorem R117065 : Reach 117065 := rs (se 2 (by rfl) ⟨43899, by rfl⟩) (B 87799 (by norm_num) ⟨43899, by rfl⟩ (by norm_num))
theorem R313685 : Reach 313685 := rs (se 10 (by rfl) ⟨459, by rfl⟩) (B 919 (by norm_num) ⟨459, by rfl⟩ (by norm_num))
theorem R117121 : Reach 117121 := rs (se 2 (by rfl) ⟨43920, by rfl⟩) (B 87841 (by norm_num) ⟨43920, by rfl⟩ (by norm_num))
theorem R117217 : Reach 117217 := rs (se 2 (by rfl) ⟨43956, by rfl⟩) (B 87913 (by norm_num) ⟨43956, by rfl⟩ (by norm_num))
theorem R248293 : Reach 248293 := rs (se 4 (by rfl) ⟨23277, by rfl⟩) (B 46555 (by norm_num) ⟨23277, by rfl⟩ (by norm_num))
theorem R117389 : Reach 117389 := rs (se 3 (by rfl) ⟨22010, by rfl⟩) (B 44021 (by norm_num) ⟨22010, by rfl⟩ (by norm_num))
theorem R117445 : Reach 117445 := rs (se 4 (by rfl) ⟨11010, by rfl⟩) (B 22021 (by norm_num) ⟨11010, by rfl⟩ (by norm_num))
theorem R314117 : Reach 314117 := rs (se 4 (by rfl) ⟨29448, by rfl⟩) (B 58897 (by norm_num) ⟨29448, by rfl⟩ (by norm_num))
theorem R117541 : Reach 117541 := rs (se 4 (by rfl) ⟨11019, by rfl⟩) (B 22039 (by norm_num) ⟨11019, by rfl⟩ (by norm_num))
theorem R117713 : Reach 117713 := rs (se 2 (by rfl) ⟨44142, by rfl⟩) (B 88285 (by norm_num) ⟨44142, by rfl⟩ (by norm_num))
theorem R216029 : Reach 216029 := rs (se 3 (by rfl) ⟨40505, by rfl⟩) (B 81011 (by norm_num) ⟨40505, by rfl⟩ (by norm_num))
theorem R347125 : Reach 347125 := rs (se 5 (by rfl) ⟨16271, by rfl⟩) (B 32543 (by norm_num) ⟨16271, by rfl⟩ (by norm_num))
theorem R117769 : Reach 117769 := rs (se 2 (by rfl) ⟨44163, by rfl⟩) (B 88327 (by norm_num) ⟨44163, by rfl⟩ (by norm_num))
theorem R805909 : Reach 805909 := rs (se 6 (by rfl) ⟨18888, by rfl⟩) (B 37777 (by norm_num) ⟨18888, by rfl⟩ (by norm_num))
theorem R117865 : Reach 117865 := rs (se 2 (by rfl) ⟨44199, by rfl⟩) (B 88399 (by norm_num) ⟨44199, by rfl⟩ (by norm_num))
theorem R314549 : Reach 314549 := rs (se 5 (by rfl) ⟨14744, by rfl⟩) (B 29489 (by norm_num) ⟨14744, by rfl⟩ (by norm_num))
theorem R118037 : Reach 118037 := rs (se 6 (by rfl) ⟨2766, by rfl⟩) (B 5533 (by norm_num) ⟨2766, by rfl⟩ (by norm_num))
theorem R642325 : Reach 642325 := rs (se 6 (by rfl) ⟨15054, by rfl⟩) (B 30109 (by norm_num) ⟨15054, by rfl⟩ (by norm_num))
theorem R347429 : Reach 347429 := rs (se 4 (by rfl) ⟨32571, by rfl⟩) (B 65143 (by norm_num) ⟨32571, by rfl⟩ (by norm_num))
theorem R118093 : Reach 118093 := rs (se 3 (by rfl) ⟨22142, by rfl⟩) (B 44285 (by norm_num) ⟨22142, by rfl⟩ (by norm_num))
theorem R118189 : Reach 118189 := rs (se 3 (by rfl) ⟨22160, by rfl⟩) (B 44321 (by norm_num) ⟨22160, by rfl⟩ (by norm_num))
theorem R478709 : Reach 478709 := rs (se 5 (by rfl) ⟨22439, by rfl⟩) (B 44879 (by norm_num) ⟨22439, by rfl⟩ (by norm_num))
theorem R151093 : Reach 151093 := rs (se 5 (by rfl) ⟨7082, by rfl⟩) (B 14165 (by norm_num) ⟨7082, by rfl⟩ (by norm_num))
theorem R118361 : Reach 118361 := rs (se 2 (by rfl) ⟨44385, by rfl⟩) (B 88771 (by norm_num) ⟨44385, by rfl⟩ (by norm_num))
theorem R314981 : Reach 314981 := rs (se 4 (by rfl) ⟨29529, by rfl⟩) (B 59059 (by norm_num) ⟨29529, by rfl⟩ (by norm_num))
theorem R216677 : Reach 216677 := rs (se 4 (by rfl) ⟨20313, by rfl⟩) (B 40627 (by norm_num) ⟨20313, by rfl⟩ (by norm_num))
theorem R380533 : Reach 380533 := rs (se 5 (by rfl) ⟨17837, by rfl⟩) (B 35675 (by norm_num) ⟨17837, by rfl⟩ (by norm_num))
theorem R118417 : Reach 118417 := rs (se 2 (by rfl) ⟨44406, by rfl⟩) (B 88813 (by norm_num) ⟨44406, by rfl⟩ (by norm_num))
theorem R151237 : Reach 151237 := rs (se 4 (by rfl) ⟨14178, by rfl⟩) (B 28357 (by norm_num) ⟨14178, by rfl⟩ (by norm_num))
theorem R118513 : Reach 118513 := rs (se 2 (by rfl) ⟨44442, by rfl⟩) (B 88885 (by norm_num) ⟨44442, by rfl⟩ (by norm_num))
theorem R118685 : Reach 118685 := rs (se 3 (by rfl) ⟨22253, by rfl⟩) (B 44507 (by norm_num) ⟨22253, by rfl⟩ (by norm_num))
theorem R249797 : Reach 249797 := rs (se 4 (by rfl) ⟨23418, by rfl⟩) (B 46837 (by norm_num) ⟨23418, by rfl⟩ (by norm_num))
theorem R118741 : Reach 118741 := rs (se 7 (by rfl) ⟨1391, by rfl⟩) (B 2783 (by norm_num) ⟨1391, by rfl⟩ (by norm_num))
theorem R937973 : Reach 937973 := rs (se 5 (by rfl) ⟨43967, by rfl⟩) (B 87935 (by norm_num) ⟨43967, by rfl⟩ (by norm_num))
theorem R315413 : Reach 315413 := rs (se 6 (by rfl) ⟨7392, by rfl⟩) (B 14785 (by norm_num) ⟨7392, by rfl⟩ (by norm_num))
theorem R118837 : Reach 118837 := rs (se 5 (by rfl) ⟨5570, by rfl⟩) (B 11141 (by norm_num) ⟨5570, by rfl⟩ (by norm_num))
theorem R119009 : Reach 119009 := rs (se 2 (by rfl) ⟨44628, by rfl⟩) (B 89257 (by norm_num) ⟨44628, by rfl⟩ (by norm_num))
theorem R119053 : Reach 119053 := rs (se 3 (by rfl) ⟨22322, by rfl⟩) (B 44645 (by norm_num) ⟨22322, by rfl⟩ (by norm_num))
theorem R119065 : Reach 119065 := rs (se 2 (by rfl) ⟨44649, by rfl⟩) (B 89299 (by norm_num) ⟨44649, by rfl⟩ (by norm_num))
theorem R250229 : Reach 250229 := rs (se 5 (by rfl) ⟨11729, by rfl⟩) (B 23459 (by norm_num) ⟨11729, by rfl⟩ (by norm_num))
theorem R119161 : Reach 119161 := rs (se 2 (by rfl) ⟨44685, by rfl⟩) (B 89371 (by norm_num) ⟨44685, by rfl⟩ (by norm_num))
theorem R315845 : Reach 315845 := rs (se 4 (by rfl) ⟨29610, by rfl⟩) (B 59221 (by norm_num) ⟨29610, by rfl⟩ (by norm_num))
theorem R119333 : Reach 119333 := rs (se 4 (by rfl) ⟨11187, by rfl⟩) (B 22375 (by norm_num) ⟨11187, by rfl⟩ (by norm_num))
theorem R119389 : Reach 119389 := rs (se 3 (by rfl) ⟨22385, by rfl⟩) (B 44771 (by norm_num) ⟨22385, by rfl⟩ (by norm_num))
theorem R119485 : Reach 119485 := rs (se 3 (by rfl) ⟨22403, by rfl⟩) (B 44807 (by norm_num) ⟨22403, by rfl⟩ (by norm_num))
theorem R480005 : Reach 480005 := rs (se 4 (by rfl) ⟨45000, by rfl⟩) (B 90001 (by norm_num) ⟨45000, by rfl⟩ (by norm_num))
theorem R119657 : Reach 119657 := rs (se 2 (by rfl) ⟨44871, by rfl⟩) (B 89743 (by norm_num) ⟨44871, by rfl⟩ (by norm_num))
theorem R316277 : Reach 316277 := rs (se 5 (by rfl) ⟨14825, by rfl⟩) (B 29651 (by norm_num) ⟨14825, by rfl⟩ (by norm_num))
theorem R119713 : Reach 119713 := rs (se 2 (by rfl) ⟨44892, by rfl⟩) (B 89785 (by norm_num) ⟨44892, by rfl⟩ (by norm_num))
theorem R1004501 : Reach 1004501 := rs (se 7 (by rfl) ⟨11771, by rfl⟩) (B 23543 (by norm_num) ⟨11771, by rfl⟩ (by norm_num))
theorem R807893 : Reach 807893 := rs (se 7 (by rfl) ⟨9467, by rfl⟩) (B 18935 (by norm_num) ⟨9467, by rfl⟩ (by norm_num))
theorem R119809 : Reach 119809 := rs (se 2 (by rfl) ⟨44928, by rfl⟩) (B 89857 (by norm_num) ⟨44928, by rfl⟩ (by norm_num))
theorem R119981 : Reach 119981 := rs (se 3 (by rfl) ⟨22496, by rfl⟩) (B 44993 (by norm_num) ⟨22496, by rfl⟩ (by norm_num))
theorem R120037 : Reach 120037 := rs (se 4 (by rfl) ⟨11253, by rfl⟩) (B 22507 (by norm_num) ⟨11253, by rfl⟩ (by norm_num))
theorem R316709 : Reach 316709 := rs (se 4 (by rfl) ⟨29691, by rfl⟩) (B 59383 (by norm_num) ⟨29691, by rfl⟩ (by norm_num))
theorem R120133 : Reach 120133 := rs (se 4 (by rfl) ⟨11262, by rfl⟩) (B 22525 (by norm_num) ⟨11262, by rfl⟩ (by norm_num))
theorem R349541 : Reach 349541 := rs (se 4 (by rfl) ⟨32769, by rfl⟩) (B 65539 (by norm_num) ⟨32769, by rfl⟩ (by norm_num))
theorem R447925 : Reach 447925 := rs (se 5 (by rfl) ⟨20996, by rfl⟩) (B 41993 (by norm_num) ⟨20996, by rfl⟩ (by norm_num))
theorem R185797 : Reach 185797 := rs (se 4 (by rfl) ⟨17418, by rfl⟩) (B 34837 (by norm_num) ⟨17418, by rfl⟩ (by norm_num))
theorem R120305 : Reach 120305 := rs (se 2 (by rfl) ⟨45114, by rfl⟩) (B 90229 (by norm_num) ⟨45114, by rfl⟩ (by norm_num))
theorem R120361 : Reach 120361 := rs (se 2 (by rfl) ⟨45135, by rfl⟩) (B 90271 (by norm_num) ⟨45135, by rfl⟩ (by norm_num))
theorem R349829 : Reach 349829 := rs (se 4 (by rfl) ⟨32796, by rfl⟩) (B 65593 (by norm_num) ⟨32796, by rfl⟩ (by norm_num))
theorem R317141 : Reach 317141 := rs (se 7 (by rfl) ⟨3716, by rfl⟩) (B 7433 (by norm_num) ⟨3716, by rfl⟩ (by norm_num))
theorem R153341 : Reach 153341 := rs (se 3 (by rfl) ⟨28751, by rfl⟩) (B 57503 (by norm_num) ⟨28751, by rfl⟩ (by norm_num))
theorem R120737 : Reach 120737 := rs (se 2 (by rfl) ⟨45276, by rfl⟩) (B 90553 (by norm_num) ⟨45276, by rfl⟩ (by norm_num))
theorem R219149 : Reach 219149 := rs (se 3 (by rfl) ⟨41090, by rfl⟩) (B 82181 (by norm_num) ⟨41090, by rfl⟩ (by norm_num))
theorem R481301 : Reach 481301 := rs (se 6 (by rfl) ⟨11280, by rfl⟩) (B 22561 (by norm_num) ⟨11280, by rfl⟩ (by norm_num))
theorem R317573 : Reach 317573 := rs (se 4 (by rfl) ⟨29772, by rfl⟩) (B 59545 (by norm_num) ⟨29772, by rfl⟩ (by norm_num))
theorem R153805 : Reach 153805 := rs (se 3 (by rfl) ⟨28838, by rfl⟩) (B 57677 (by norm_num) ⟨28838, by rfl⟩ (by norm_num))
theorem R153893 : Reach 153893 := rs (se 4 (by rfl) ⟨14427, by rfl⟩) (B 28855 (by norm_num) ⟨14427, by rfl⟩ (by norm_num))
theorem R121225 : Reach 121225 := rs (se 2 (by rfl) ⟨45459, by rfl⟩) (B 90919 (by norm_num) ⟨45459, by rfl⟩ (by norm_num))
theorem R154021 : Reach 154021 := rs (se 4 (by rfl) ⟨14439, by rfl⟩) (B 28879 (by norm_num) ⟨14439, by rfl⟩ (by norm_num))
theorem R219581 : Reach 219581 := rs (se 3 (by rfl) ⟨41171, by rfl⟩) (B 82343 (by norm_num) ⟨41171, by rfl⟩ (by norm_num))
theorem R154109 : Reach 154109 := rs (se 3 (by rfl) ⟨28895, by rfl⟩) (B 57791 (by norm_num) ⟨28895, by rfl⟩ (by norm_num))
theorem R121385 : Reach 121385 := rs (se 2 (by rfl) ⟨45519, by rfl⟩) (B 91039 (by norm_num) ⟨45519, by rfl⟩ (by norm_num))
theorem R318005 : Reach 318005 := rs (se 5 (by rfl) ⟨14906, by rfl⟩) (B 29813 (by norm_num) ⟨14906, by rfl⟩ (by norm_num))
theorem R154237 : Reach 154237 := rs (se 3 (by rfl) ⟨28919, by rfl⟩) (B 57839 (by norm_num) ⟨28919, by rfl⟩ (by norm_num))
theorem R154325 : Reach 154325 := rs (se 7 (by rfl) ⟨1808, by rfl⟩) (B 3617 (by norm_num) ⟨1808, by rfl⟩ (by norm_num))
theorem R351013 : Reach 351013 := rs (se 4 (by rfl) ⟨32907, by rfl⟩) (B 65815 (by norm_num) ⟨32907, by rfl⟩ (by norm_num))
theorem R154453 : Reach 154453 := rs (se 9 (by rfl) ⟨452, by rfl⟩) (B 905 (by norm_num) ⟨452, by rfl⟩ (by norm_num))
theorem R154541 : Reach 154541 := rs (se 3 (by rfl) ⟨28976, by rfl⟩) (B 57953 (by norm_num) ⟨28976, by rfl⟩ (by norm_num))
theorem R318437 : Reach 318437 := rs (se 4 (by rfl) ⟨29853, by rfl⟩) (B 59707 (by norm_num) ⟨29853, by rfl⟩ (by norm_num))
theorem R154669 : Reach 154669 := rs (se 3 (by rfl) ⟨29000, by rfl⟩) (B 58001 (by norm_num) ⟨29000, by rfl⟩ (by norm_num))
theorem R351317 : Reach 351317 := rs (se 8 (by rfl) ⟨2058, by rfl⟩) (B 4117 (by norm_num) ⟨2058, by rfl⟩ (by norm_num))
theorem R613493 : Reach 613493 := rs (se 5 (by rfl) ⟨28757, by rfl⟩) (B 57515 (by norm_num) ⟨28757, by rfl⟩ (by norm_num))
theorem R154757 : Reach 154757 := rs (se 4 (by rfl) ⟨14508, by rfl⟩) (B 29017 (by norm_num) ⟨14508, by rfl⟩ (by norm_num))
theorem R154885 : Reach 154885 := rs (se 4 (by rfl) ⟨14520, by rfl⟩) (B 29041 (by norm_num) ⟨14520, by rfl⟩ (by norm_num))
theorem R843061 : Reach 843061 := rs (se 5 (by rfl) ⟨39518, by rfl⟩) (B 79037 (by norm_num) ⟨39518, by rfl⟩ (by norm_num))
theorem R711989 : Reach 711989 := rs (se 5 (by rfl) ⟨33374, by rfl⟩) (B 66749 (by norm_num) ⟨33374, by rfl⟩ (by norm_num))
theorem R154973 : Reach 154973 := rs (se 3 (by rfl) ⟨29057, by rfl⟩) (B 58115 (by norm_num) ⟨29057, by rfl⟩ (by norm_num))
theorem R318869 : Reach 318869 := rs (se 6 (by rfl) ⟨7473, by rfl⟩) (B 14947 (by norm_num) ⟨7473, by rfl⟩ (by norm_num))
theorem R155101 : Reach 155101 := rs (se 3 (by rfl) ⟨29081, by rfl⟩) (B 58163 (by norm_num) ⟨29081, by rfl⟩ (by norm_num))
theorem R155189 : Reach 155189 := rs (se 5 (by rfl) ⟨7274, by rfl⟩) (B 14549 (by norm_num) ⟨7274, by rfl⟩ (by norm_num))
theorem R220781 : Reach 220781 := rs (se 3 (by rfl) ⟨41396, by rfl⟩) (B 82793 (by norm_num) ⟨41396, by rfl⟩ (by norm_num))
theorem R155317 : Reach 155317 := rs (se 5 (by rfl) ⟨7280, by rfl⟩) (B 14561 (by norm_num) ⟨7280, by rfl⟩ (by norm_num))
theorem R1367765 : Reach 1367765 := rs (se 7 (by rfl) ⟨16028, by rfl⟩) (B 32057 (by norm_num) ⟨16028, by rfl⟩ (by norm_num))
theorem R351989 : Reach 351989 := rs (se 5 (by rfl) ⟨16499, by rfl⟩) (B 32999 (by norm_num) ⟨16499, by rfl⟩ (by norm_num))
theorem R155405 : Reach 155405 := rs (se 3 (by rfl) ⟨29138, by rfl⟩) (B 58277 (by norm_num) ⟨29138, by rfl⟩ (by norm_num))
theorem R319301 : Reach 319301 := rs (se 4 (by rfl) ⟨29934, by rfl⟩) (B 59869 (by norm_num) ⟨29934, by rfl⟩ (by norm_num))
theorem R253829 : Reach 253829 := rs (se 4 (by rfl) ⟨23796, by rfl⟩) (B 47593 (by norm_num) ⟨23796, by rfl⟩ (by norm_num))
theorem R155533 : Reach 155533 := rs (se 3 (by rfl) ⟨29162, by rfl⟩) (B 58325 (by norm_num) ⟨29162, by rfl⟩ (by norm_num))
theorem R155621 : Reach 155621 := rs (se 4 (by rfl) ⟨14589, by rfl⟩) (B 29179 (by norm_num) ⟨14589, by rfl⟩ (by norm_num))
theorem R155749 : Reach 155749 := rs (se 4 (by rfl) ⟨14601, by rfl⟩) (B 29203 (by norm_num) ⟨14601, by rfl⟩ (by norm_num))
theorem R155837 : Reach 155837 := rs (se 3 (by rfl) ⟨29219, by rfl⟩) (B 58439 (by norm_num) ⟨29219, by rfl⟩ (by norm_num))
theorem R319733 : Reach 319733 := rs (se 5 (by rfl) ⟨14987, by rfl⟩) (B 29975 (by norm_num) ⟨14987, by rfl⟩ (by norm_num))
theorem R155965 : Reach 155965 := rs (se 3 (by rfl) ⟨29243, by rfl⟩) (B 58487 (by norm_num) ⟨29243, by rfl⟩ (by norm_num))
theorem R156053 : Reach 156053 := rs (se 6 (by rfl) ⟨3657, by rfl⟩) (B 7315 (by norm_num) ⟨3657, by rfl⟩ (by norm_num))
theorem R156181 : Reach 156181 := rs (se 6 (by rfl) ⟨3660, by rfl⟩) (B 7321 (by norm_num) ⟨3660, by rfl⟩ (by norm_num))
theorem R156269 : Reach 156269 := rs (se 3 (by rfl) ⟨29300, by rfl⟩) (B 58601 (by norm_num) ⟨29300, by rfl⟩ (by norm_num))
theorem R123557 : Reach 123557 := rs (se 4 (by rfl) ⟨11583, by rfl⟩) (B 23167 (by norm_num) ⟨11583, by rfl⟩ (by norm_num))
theorem R320165 : Reach 320165 := rs (se 4 (by rfl) ⟨30015, by rfl⟩) (B 60031 (by norm_num) ⟨30015, by rfl⟩ (by norm_num))
theorem R320213 : Reach 320213 := rs (se 7 (by rfl) ⟨3752, by rfl⟩) (B 7505 (by norm_num) ⟨3752, by rfl⟩ (by norm_num))
theorem R156397 : Reach 156397 := rs (se 3 (by rfl) ⟨29324, by rfl⟩) (B 58649 (by norm_num) ⟨29324, by rfl⟩ (by norm_num))
theorem R189229 : Reach 189229 := rs (se 3 (by rfl) ⟨35480, by rfl⟩) (B 70961 (by norm_num) ⟨35480, by rfl⟩ (by norm_num))
theorem R156485 : Reach 156485 := rs (se 4 (by rfl) ⟨14670, by rfl⟩) (B 29341 (by norm_num) ⟨14670, by rfl⟩ (by norm_num))
theorem R189253 : Reach 189253 := rs (se 4 (by rfl) ⟨17742, by rfl⟩) (B 35485 (by norm_num) ⟨17742, by rfl⟩ (by norm_num))
theorem R156613 : Reach 156613 := rs (se 4 (by rfl) ⟨14682, by rfl⟩) (B 29365 (by norm_num) ⟨14682, by rfl⟩ (by norm_num))
theorem R91133 : Reach 91133 := rs (se 3 (by rfl) ⟨17087, by rfl⟩) (B 34175 (by norm_num) ⟨17087, by rfl⟩ (by norm_num))
theorem R91137 : Reach 91137 := rs (se 2 (by rfl) ⟨34176, by rfl⟩) (B 68353 (by norm_num) ⟨34176, by rfl⟩ (by norm_num))
theorem R91141 : Reach 91141 := rs (se 4 (by rfl) ⟨8544, by rfl⟩) (B 17089 (by norm_num) ⟨8544, by rfl⟩ (by norm_num))
theorem R91145 : Reach 91145 := rs (se 2 (by rfl) ⟨34179, by rfl⟩) (B 68359 (by norm_num) ⟨34179, by rfl⟩ (by norm_num))
theorem R91149 : Reach 91149 := rs (se 3 (by rfl) ⟨17090, by rfl⟩) (B 34181 (by norm_num) ⟨17090, by rfl⟩ (by norm_num))
theorem R91153 : Reach 91153 := rs (se 2 (by rfl) ⟨34182, by rfl⟩) (B 68365 (by norm_num) ⟨34182, by rfl⟩ (by norm_num))
theorem R91157 : Reach 91157 := rs (se 6 (by rfl) ⟨2136, by rfl⟩) (B 4273 (by norm_num) ⟨2136, by rfl⟩ (by norm_num))
theorem R91161 : Reach 91161 := rs (se 2 (by rfl) ⟨34185, by rfl⟩) (B 68371 (by norm_num) ⟨34185, by rfl⟩ (by norm_num))
theorem R91165 : Reach 91165 := rs (se 3 (by rfl) ⟨17093, by rfl⟩) (B 34187 (by norm_num) ⟨17093, by rfl⟩ (by norm_num))
theorem R156701 : Reach 156701 := rs (se 3 (by rfl) ⟨29381, by rfl⟩) (B 58763 (by norm_num) ⟨29381, by rfl⟩ (by norm_num))
theorem R91169 : Reach 91169 := rs (se 2 (by rfl) ⟨34188, by rfl⟩) (B 68377 (by norm_num) ⟨34188, by rfl⟩ (by norm_num))
theorem R91173 : Reach 91173 := rs (se 4 (by rfl) ⟨8547, by rfl⟩) (B 17095 (by norm_num) ⟨8547, by rfl⟩ (by norm_num))
theorem R91177 : Reach 91177 := rs (se 2 (by rfl) ⟨34191, by rfl⟩) (B 68383 (by norm_num) ⟨34191, by rfl⟩ (by norm_num))
theorem R91181 : Reach 91181 := rs (se 3 (by rfl) ⟨17096, by rfl⟩) (B 34193 (by norm_num) ⟨17096, by rfl⟩ (by norm_num))
theorem R91185 : Reach 91185 := rs (se 2 (by rfl) ⟨34194, by rfl⟩) (B 68389 (by norm_num) ⟨34194, by rfl⟩ (by norm_num))
theorem R91189 : Reach 91189 := rs (se 5 (by rfl) ⟨4274, by rfl⟩) (B 8549 (by norm_num) ⟨4274, by rfl⟩ (by norm_num))
theorem R91193 : Reach 91193 := rs (se 2 (by rfl) ⟨34197, by rfl⟩) (B 68395 (by norm_num) ⟨34197, by rfl⟩ (by norm_num))
theorem R91197 : Reach 91197 := rs (se 3 (by rfl) ⟨17099, by rfl⟩) (B 34199 (by norm_num) ⟨17099, by rfl⟩ (by norm_num))
theorem R91201 : Reach 91201 := rs (se 2 (by rfl) ⟨34200, by rfl⟩) (B 68401 (by norm_num) ⟨34200, by rfl⟩ (by norm_num))
theorem R91205 : Reach 91205 := rs (se 4 (by rfl) ⟨8550, by rfl⟩) (B 17101 (by norm_num) ⟨8550, by rfl⟩ (by norm_num))
theorem R91209 : Reach 91209 := rs (se 2 (by rfl) ⟨34203, by rfl⟩) (B 68407 (by norm_num) ⟨34203, by rfl⟩ (by norm_num))
theorem R91213 : Reach 91213 := rs (se 3 (by rfl) ⟨17102, by rfl⟩) (B 34205 (by norm_num) ⟨17102, by rfl⟩ (by norm_num))
theorem R91217 : Reach 91217 := rs (se 2 (by rfl) ⟨34206, by rfl⟩) (B 68413 (by norm_num) ⟨34206, by rfl⟩ (by norm_num))
theorem R91221 : Reach 91221 := rs (se 8 (by rfl) ⟨534, by rfl⟩) (B 1069 (by norm_num) ⟨534, by rfl⟩ (by norm_num))
theorem R320597 : Reach 320597 := rs (se 8 (by rfl) ⟨1878, by rfl⟩) (B 3757 (by norm_num) ⟨1878, by rfl⟩ (by norm_num))
theorem R91225 : Reach 91225 := rs (se 2 (by rfl) ⟨34209, by rfl⟩) (B 68419 (by norm_num) ⟨34209, by rfl⟩ (by norm_num))
theorem R91229 : Reach 91229 := rs (se 3 (by rfl) ⟨17105, by rfl⟩) (B 34211 (by norm_num) ⟨17105, by rfl⟩ (by norm_num))
theorem R91233 : Reach 91233 := rs (se 2 (by rfl) ⟨34212, by rfl⟩) (B 68425 (by norm_num) ⟨34212, by rfl⟩ (by norm_num))
theorem R91237 : Reach 91237 := rs (se 4 (by rfl) ⟨8553, by rfl⟩) (B 17107 (by norm_num) ⟨8553, by rfl⟩ (by norm_num))
theorem R91241 : Reach 91241 := rs (se 2 (by rfl) ⟨34215, by rfl⟩) (B 68431 (by norm_num) ⟨34215, by rfl⟩ (by norm_num))
theorem R91245 : Reach 91245 := rs (se 3 (by rfl) ⟨17108, by rfl⟩) (B 34217 (by norm_num) ⟨17108, by rfl⟩ (by norm_num))
theorem R91249 : Reach 91249 := rs (se 2 (by rfl) ⟨34218, by rfl⟩) (B 68437 (by norm_num) ⟨34218, by rfl⟩ (by norm_num))
theorem R91253 : Reach 91253 := rs (se 5 (by rfl) ⟨4277, by rfl⟩) (B 8555 (by norm_num) ⟨4277, by rfl⟩ (by norm_num))
theorem R91257 : Reach 91257 := rs (se 2 (by rfl) ⟨34221, by rfl⟩) (B 68443 (by norm_num) ⟨34221, by rfl⟩ (by norm_num))
theorem R91261 : Reach 91261 := rs (se 3 (by rfl) ⟨17111, by rfl⟩) (B 34223 (by norm_num) ⟨17111, by rfl⟩ (by norm_num))
theorem R91265 : Reach 91265 := rs (se 2 (by rfl) ⟨34224, by rfl⟩) (B 68449 (by norm_num) ⟨34224, by rfl⟩ (by norm_num))
theorem R91269 : Reach 91269 := rs (se 4 (by rfl) ⟨8556, by rfl⟩) (B 17113 (by norm_num) ⟨8556, by rfl⟩ (by norm_num))
theorem R91273 : Reach 91273 := rs (se 2 (by rfl) ⟨34227, by rfl⟩) (B 68455 (by norm_num) ⟨34227, by rfl⟩ (by norm_num))
theorem R91277 : Reach 91277 := rs (se 3 (by rfl) ⟨17114, by rfl⟩) (B 34229 (by norm_num) ⟨17114, by rfl⟩ (by norm_num))
theorem R91281 : Reach 91281 := rs (se 2 (by rfl) ⟨34230, by rfl⟩) (B 68461 (by norm_num) ⟨34230, by rfl⟩ (by norm_num))
theorem R91285 : Reach 91285 := rs (se 6 (by rfl) ⟨2139, by rfl⟩) (B 4279 (by norm_num) ⟨2139, by rfl⟩ (by norm_num))
theorem R353429 : Reach 353429 := rs (se 6 (by rfl) ⟨8283, by rfl⟩) (B 16567 (by norm_num) ⟨8283, by rfl⟩ (by norm_num))
theorem R91289 : Reach 91289 := rs (se 2 (by rfl) ⟨34233, by rfl⟩) (B 68467 (by norm_num) ⟨34233, by rfl⟩ (by norm_num))
theorem R91293 : Reach 91293 := rs (se 3 (by rfl) ⟨17117, by rfl⟩) (B 34235 (by norm_num) ⟨17117, by rfl⟩ (by norm_num))
theorem R156829 : Reach 156829 := rs (se 3 (by rfl) ⟨29405, by rfl⟩) (B 58811 (by norm_num) ⟨29405, by rfl⟩ (by norm_num))
theorem R91297 : Reach 91297 := rs (se 2 (by rfl) ⟨34236, by rfl⟩) (B 68473 (by norm_num) ⟨34236, by rfl⟩ (by norm_num))
theorem R91301 : Reach 91301 := rs (se 4 (by rfl) ⟨8559, by rfl⟩) (B 17119 (by norm_num) ⟨8559, by rfl⟩ (by norm_num))
theorem R91305 : Reach 91305 := rs (se 2 (by rfl) ⟨34239, by rfl⟩) (B 68479 (by norm_num) ⟨34239, by rfl⟩ (by norm_num))
theorem R91309 : Reach 91309 := rs (se 3 (by rfl) ⟨17120, by rfl⟩) (B 34241 (by norm_num) ⟨17120, by rfl⟩ (by norm_num))
theorem R91313 : Reach 91313 := rs (se 2 (by rfl) ⟨34242, by rfl⟩) (B 68485 (by norm_num) ⟨34242, by rfl⟩ (by norm_num))
theorem R91317 : Reach 91317 := rs (se 5 (by rfl) ⟨4280, by rfl⟩) (B 8561 (by norm_num) ⟨4280, by rfl⟩ (by norm_num))
theorem R91321 : Reach 91321 := rs (se 2 (by rfl) ⟨34245, by rfl⟩) (B 68491 (by norm_num) ⟨34245, by rfl⟩ (by norm_num))
theorem R91325 : Reach 91325 := rs (se 3 (by rfl) ⟨17123, by rfl⟩) (B 34247 (by norm_num) ⟨17123, by rfl⟩ (by norm_num))
theorem R91329 : Reach 91329 := rs (se 2 (by rfl) ⟨34248, by rfl⟩) (B 68497 (by norm_num) ⟨34248, by rfl⟩ (by norm_num))
theorem R91333 : Reach 91333 := rs (se 4 (by rfl) ⟨8562, by rfl⟩) (B 17125 (by norm_num) ⟨8562, by rfl⟩ (by norm_num))
theorem R91337 : Reach 91337 := rs (se 2 (by rfl) ⟨34251, by rfl⟩) (B 68503 (by norm_num) ⟨34251, by rfl⟩ (by norm_num))
theorem R91341 : Reach 91341 := rs (se 3 (by rfl) ⟨17126, by rfl⟩) (B 34253 (by norm_num) ⟨17126, by rfl⟩ (by norm_num))
theorem R91345 : Reach 91345 := rs (se 2 (by rfl) ⟨34254, by rfl⟩) (B 68509 (by norm_num) ⟨34254, by rfl⟩ (by norm_num))
theorem R91349 : Reach 91349 := rs (se 7 (by rfl) ⟨1070, by rfl⟩) (B 2141 (by norm_num) ⟨1070, by rfl⟩ (by norm_num))
theorem R91353 : Reach 91353 := rs (se 2 (by rfl) ⟨34257, by rfl⟩) (B 68515 (by norm_num) ⟨34257, by rfl⟩ (by norm_num))
theorem R91357 : Reach 91357 := rs (se 3 (by rfl) ⟨17129, by rfl⟩) (B 34259 (by norm_num) ⟨17129, by rfl⟩ (by norm_num))
theorem R91361 : Reach 91361 := rs (se 2 (by rfl) ⟨34260, by rfl⟩) (B 68521 (by norm_num) ⟨34260, by rfl⟩ (by norm_num))
theorem R91365 : Reach 91365 := rs (se 4 (by rfl) ⟨8565, by rfl⟩) (B 17131 (by norm_num) ⟨8565, by rfl⟩ (by norm_num))
theorem R91369 : Reach 91369 := rs (se 2 (by rfl) ⟨34263, by rfl⟩) (B 68527 (by norm_num) ⟨34263, by rfl⟩ (by norm_num))
theorem R91373 : Reach 91373 := rs (se 3 (by rfl) ⟨17132, by rfl⟩) (B 34265 (by norm_num) ⟨17132, by rfl⟩ (by norm_num))
theorem R91377 : Reach 91377 := rs (se 2 (by rfl) ⟨34266, by rfl⟩) (B 68533 (by norm_num) ⟨34266, by rfl⟩ (by norm_num))
theorem R91381 : Reach 91381 := rs (se 5 (by rfl) ⟨4283, by rfl⟩) (B 8567 (by norm_num) ⟨4283, by rfl⟩ (by norm_num))
theorem R156917 : Reach 156917 := rs (se 5 (by rfl) ⟨7355, by rfl⟩) (B 14711 (by norm_num) ⟨7355, by rfl⟩ (by norm_num))
theorem R91385 : Reach 91385 := rs (se 2 (by rfl) ⟨34269, by rfl⟩) (B 68539 (by norm_num) ⟨34269, by rfl⟩ (by norm_num))
theorem R91389 : Reach 91389 := rs (se 3 (by rfl) ⟨17135, by rfl⟩) (B 34271 (by norm_num) ⟨17135, by rfl⟩ (by norm_num))
theorem R91393 : Reach 91393 := rs (se 2 (by rfl) ⟨34272, by rfl⟩) (B 68545 (by norm_num) ⟨34272, by rfl⟩ (by norm_num))
theorem R91397 : Reach 91397 := rs (se 4 (by rfl) ⟨8568, by rfl⟩) (B 17137 (by norm_num) ⟨8568, by rfl⟩ (by norm_num))
theorem R91401 : Reach 91401 := rs (se 2 (by rfl) ⟨34275, by rfl⟩) (B 68551 (by norm_num) ⟨34275, by rfl⟩ (by norm_num))
theorem R91405 : Reach 91405 := rs (se 3 (by rfl) ⟨17138, by rfl⟩) (B 34277 (by norm_num) ⟨17138, by rfl⟩ (by norm_num))
theorem R91409 : Reach 91409 := rs (se 2 (by rfl) ⟨34278, by rfl⟩) (B 68557 (by norm_num) ⟨34278, by rfl⟩ (by norm_num))
theorem R91413 : Reach 91413 := rs (se 6 (by rfl) ⟨2142, by rfl⟩) (B 4285 (by norm_num) ⟨2142, by rfl⟩ (by norm_num))
theorem R91417 : Reach 91417 := rs (se 2 (by rfl) ⟨34281, by rfl⟩) (B 68563 (by norm_num) ⟨34281, by rfl⟩ (by norm_num))
theorem R91421 : Reach 91421 := rs (se 3 (by rfl) ⟨17141, by rfl⟩) (B 34283 (by norm_num) ⟨17141, by rfl⟩ (by norm_num))
theorem R91425 : Reach 91425 := rs (se 2 (by rfl) ⟨34284, by rfl⟩) (B 68569 (by norm_num) ⟨34284, by rfl⟩ (by norm_num))
theorem R91429 : Reach 91429 := rs (se 4 (by rfl) ⟨8571, by rfl⟩) (B 17143 (by norm_num) ⟨8571, by rfl⟩ (by norm_num))
theorem R91433 : Reach 91433 := rs (se 2 (by rfl) ⟨34287, by rfl⟩) (B 68575 (by norm_num) ⟨34287, by rfl⟩ (by norm_num))
theorem R91437 : Reach 91437 := rs (se 3 (by rfl) ⟨17144, by rfl⟩) (B 34289 (by norm_num) ⟨17144, by rfl⟩ (by norm_num))
theorem R91441 : Reach 91441 := rs (se 2 (by rfl) ⟨34290, by rfl⟩) (B 68581 (by norm_num) ⟨34290, by rfl⟩ (by norm_num))
theorem R91445 : Reach 91445 := rs (se 5 (by rfl) ⟨4286, by rfl⟩) (B 8573 (by norm_num) ⟨4286, by rfl⟩ (by norm_num))
theorem R91449 : Reach 91449 := rs (se 2 (by rfl) ⟨34293, by rfl⟩) (B 68587 (by norm_num) ⟨34293, by rfl⟩ (by norm_num))
theorem R91453 : Reach 91453 := rs (se 3 (by rfl) ⟨17147, by rfl⟩) (B 34295 (by norm_num) ⟨17147, by rfl⟩ (by norm_num))
theorem R91457 : Reach 91457 := rs (se 2 (by rfl) ⟨34296, by rfl⟩) (B 68593 (by norm_num) ⟨34296, by rfl⟩ (by norm_num))
theorem R91461 : Reach 91461 := rs (se 4 (by rfl) ⟨8574, by rfl⟩) (B 17149 (by norm_num) ⟨8574, by rfl⟩ (by norm_num))
theorem R91465 : Reach 91465 := rs (se 2 (by rfl) ⟨34299, by rfl⟩) (B 68599 (by norm_num) ⟨34299, by rfl⟩ (by norm_num))
theorem R91469 : Reach 91469 := rs (se 3 (by rfl) ⟨17150, by rfl⟩) (B 34301 (by norm_num) ⟨17150, by rfl⟩ (by norm_num))
theorem R91473 : Reach 91473 := rs (se 2 (by rfl) ⟨34302, by rfl⟩) (B 68605 (by norm_num) ⟨34302, by rfl⟩ (by norm_num))
theorem R91477 : Reach 91477 := rs (se 12 (by rfl) ⟨33, by rfl⟩) (B 67 (by norm_num) ⟨33, by rfl⟩ (by norm_num))
theorem R451925 : Reach 451925 := rs (se 12 (by rfl) ⟨165, by rfl⟩) (B 331 (by norm_num) ⟨165, by rfl⟩ (by norm_num))
theorem R91481 : Reach 91481 := rs (se 2 (by rfl) ⟨34305, by rfl⟩) (B 68611 (by norm_num) ⟨34305, by rfl⟩ (by norm_num))
theorem R91485 : Reach 91485 := rs (se 3 (by rfl) ⟨17153, by rfl⟩) (B 34307 (by norm_num) ⟨17153, by rfl⟩ (by norm_num))
theorem R91489 : Reach 91489 := rs (se 2 (by rfl) ⟨34308, by rfl⟩) (B 68617 (by norm_num) ⟨34308, by rfl⟩ (by norm_num))
theorem R91493 : Reach 91493 := rs (se 4 (by rfl) ⟨8577, by rfl⟩) (B 17155 (by norm_num) ⟨8577, by rfl⟩ (by norm_num))
theorem R91497 : Reach 91497 := rs (se 2 (by rfl) ⟨34311, by rfl⟩) (B 68623 (by norm_num) ⟨34311, by rfl⟩ (by norm_num))
theorem R91501 : Reach 91501 := rs (se 3 (by rfl) ⟨17156, by rfl⟩) (B 34313 (by norm_num) ⟨17156, by rfl⟩ (by norm_num))
theorem R91505 : Reach 91505 := rs (se 2 (by rfl) ⟨34314, by rfl⟩) (B 68629 (by norm_num) ⟨34314, by rfl⟩ (by norm_num))
theorem R91509 : Reach 91509 := rs (se 5 (by rfl) ⟨4289, by rfl⟩) (B 8579 (by norm_num) ⟨4289, by rfl⟩ (by norm_num))
theorem R157045 : Reach 157045 := rs (se 5 (by rfl) ⟨7361, by rfl⟩) (B 14723 (by norm_num) ⟨7361, by rfl⟩ (by norm_num))
theorem R91513 : Reach 91513 := rs (se 2 (by rfl) ⟨34317, by rfl⟩) (B 68635 (by norm_num) ⟨34317, by rfl⟩ (by norm_num))
theorem R91517 : Reach 91517 := rs (se 3 (by rfl) ⟨17159, by rfl⟩) (B 34319 (by norm_num) ⟨17159, by rfl⟩ (by norm_num))
theorem R91521 : Reach 91521 := rs (se 2 (by rfl) ⟨34320, by rfl⟩) (B 68641 (by norm_num) ⟨34320, by rfl⟩ (by norm_num))
theorem R91525 : Reach 91525 := rs (se 4 (by rfl) ⟨8580, by rfl⟩) (B 17161 (by norm_num) ⟨8580, by rfl⟩ (by norm_num))
theorem R91529 : Reach 91529 := rs (se 2 (by rfl) ⟨34323, by rfl⟩) (B 68647 (by norm_num) ⟨34323, by rfl⟩ (by norm_num))
theorem R91533 : Reach 91533 := rs (se 3 (by rfl) ⟨17162, by rfl⟩) (B 34325 (by norm_num) ⟨17162, by rfl⟩ (by norm_num))
theorem R91537 : Reach 91537 := rs (se 2 (by rfl) ⟨34326, by rfl⟩) (B 68653 (by norm_num) ⟨34326, by rfl⟩ (by norm_num))
theorem R91541 : Reach 91541 := rs (se 6 (by rfl) ⟨2145, by rfl⟩) (B 4291 (by norm_num) ⟨2145, by rfl⟩ (by norm_num))
theorem R91545 : Reach 91545 := rs (se 2 (by rfl) ⟨34329, by rfl⟩) (B 68659 (by norm_num) ⟨34329, by rfl⟩ (by norm_num))
theorem R91549 : Reach 91549 := rs (se 3 (by rfl) ⟨17165, by rfl⟩) (B 34331 (by norm_num) ⟨17165, by rfl⟩ (by norm_num))
theorem R91553 : Reach 91553 := rs (se 2 (by rfl) ⟨34332, by rfl⟩) (B 68665 (by norm_num) ⟨34332, by rfl⟩ (by norm_num))
theorem R91557 : Reach 91557 := rs (se 4 (by rfl) ⟨8583, by rfl⟩) (B 17167 (by norm_num) ⟨8583, by rfl⟩ (by norm_num))
theorem R91561 : Reach 91561 := rs (se 2 (by rfl) ⟨34335, by rfl⟩) (B 68671 (by norm_num) ⟨34335, by rfl⟩ (by norm_num))
theorem R91565 : Reach 91565 := rs (se 3 (by rfl) ⟨17168, by rfl⟩) (B 34337 (by norm_num) ⟨17168, by rfl⟩ (by norm_num))
theorem R91569 : Reach 91569 := rs (se 2 (by rfl) ⟨34338, by rfl⟩) (B 68677 (by norm_num) ⟨34338, by rfl⟩ (by norm_num))
theorem R91573 : Reach 91573 := rs (se 5 (by rfl) ⟨4292, by rfl⟩) (B 8585 (by norm_num) ⟨4292, by rfl⟩ (by norm_num))
theorem R353717 : Reach 353717 := rs (se 5 (by rfl) ⟨16580, by rfl⟩) (B 33161 (by norm_num) ⟨16580, by rfl⟩ (by norm_num))
theorem R91577 : Reach 91577 := rs (se 2 (by rfl) ⟨34341, by rfl⟩) (B 68683 (by norm_num) ⟨34341, by rfl⟩ (by norm_num))
theorem R91581 : Reach 91581 := rs (se 3 (by rfl) ⟨17171, by rfl⟩) (B 34343 (by norm_num) ⟨17171, by rfl⟩ (by norm_num))
theorem R91585 : Reach 91585 := rs (se 2 (by rfl) ⟨34344, by rfl⟩) (B 68689 (by norm_num) ⟨34344, by rfl⟩ (by norm_num))
theorem R91589 : Reach 91589 := rs (se 4 (by rfl) ⟨8586, by rfl⟩) (B 17173 (by norm_num) ⟨8586, by rfl⟩ (by norm_num))
theorem R91593 : Reach 91593 := rs (se 2 (by rfl) ⟨34347, by rfl⟩) (B 68695 (by norm_num) ⟨34347, by rfl⟩ (by norm_num))
theorem R91597 : Reach 91597 := rs (se 3 (by rfl) ⟨17174, by rfl⟩) (B 34349 (by norm_num) ⟨17174, by rfl⟩ (by norm_num))
theorem R157133 : Reach 157133 := rs (se 3 (by rfl) ⟨29462, by rfl⟩) (B 58925 (by norm_num) ⟨29462, by rfl⟩ (by norm_num))
theorem R91601 : Reach 91601 := rs (se 2 (by rfl) ⟨34350, by rfl⟩) (B 68701 (by norm_num) ⟨34350, by rfl⟩ (by norm_num))
theorem R91605 : Reach 91605 := rs (se 7 (by rfl) ⟨1073, by rfl⟩) (B 2147 (by norm_num) ⟨1073, by rfl⟩ (by norm_num))
theorem R91609 : Reach 91609 := rs (se 2 (by rfl) ⟨34353, by rfl⟩) (B 68707 (by norm_num) ⟨34353, by rfl⟩ (by norm_num))
theorem R91613 : Reach 91613 := rs (se 3 (by rfl) ⟨17177, by rfl⟩) (B 34355 (by norm_num) ⟨17177, by rfl⟩ (by norm_num))
theorem R91617 : Reach 91617 := rs (se 2 (by rfl) ⟨34356, by rfl⟩) (B 68713 (by norm_num) ⟨34356, by rfl⟩ (by norm_num))
theorem R91621 : Reach 91621 := rs (se 4 (by rfl) ⟨8589, by rfl⟩) (B 17179 (by norm_num) ⟨8589, by rfl⟩ (by norm_num))
theorem R91625 : Reach 91625 := rs (se 2 (by rfl) ⟨34359, by rfl⟩) (B 68719 (by norm_num) ⟨34359, by rfl⟩ (by norm_num))
theorem R91629 : Reach 91629 := rs (se 3 (by rfl) ⟨17180, by rfl⟩) (B 34361 (by norm_num) ⟨17180, by rfl⟩ (by norm_num))
theorem R157165 : Reach 157165 := rs (se 3 (by rfl) ⟨29468, by rfl⟩) (B 58937 (by norm_num) ⟨29468, by rfl⟩ (by norm_num))
theorem R91633 : Reach 91633 := rs (se 2 (by rfl) ⟨34362, by rfl⟩) (B 68725 (by norm_num) ⟨34362, by rfl⟩ (by norm_num))
theorem R91637 : Reach 91637 := rs (se 5 (by rfl) ⟨4295, by rfl⟩) (B 8591 (by norm_num) ⟨4295, by rfl⟩ (by norm_num))
theorem R91641 : Reach 91641 := rs (se 2 (by rfl) ⟨34365, by rfl⟩) (B 68731 (by norm_num) ⟨34365, by rfl⟩ (by norm_num))
theorem R91645 : Reach 91645 := rs (se 3 (by rfl) ⟨17183, by rfl⟩) (B 34367 (by norm_num) ⟨17183, by rfl⟩ (by norm_num))
theorem R189949 : Reach 189949 := rs (se 3 (by rfl) ⟨35615, by rfl⟩) (B 71231 (by norm_num) ⟨35615, by rfl⟩ (by norm_num))
theorem R91649 : Reach 91649 := rs (se 2 (by rfl) ⟨34368, by rfl⟩) (B 68737 (by norm_num) ⟨34368, by rfl⟩ (by norm_num))
theorem R91653 : Reach 91653 := rs (se 4 (by rfl) ⟨8592, by rfl⟩) (B 17185 (by norm_num) ⟨8592, by rfl⟩ (by norm_num))
theorem R321029 : Reach 321029 := rs (se 4 (by rfl) ⟨30096, by rfl⟩) (B 60193 (by norm_num) ⟨30096, by rfl⟩ (by norm_num))
theorem R91657 : Reach 91657 := rs (se 2 (by rfl) ⟨34371, by rfl⟩) (B 68743 (by norm_num) ⟨34371, by rfl⟩ (by norm_num))
theorem R91661 : Reach 91661 := rs (se 3 (by rfl) ⟨17186, by rfl⟩) (B 34373 (by norm_num) ⟨17186, by rfl⟩ (by norm_num))
theorem R91665 : Reach 91665 := rs (se 2 (by rfl) ⟨34374, by rfl⟩) (B 68749 (by norm_num) ⟨34374, by rfl⟩ (by norm_num))
theorem R91669 : Reach 91669 := rs (se 6 (by rfl) ⟨2148, by rfl⟩) (B 4297 (by norm_num) ⟨2148, by rfl⟩ (by norm_num))
theorem R91673 : Reach 91673 := rs (se 2 (by rfl) ⟨34377, by rfl⟩) (B 68755 (by norm_num) ⟨34377, by rfl⟩ (by norm_num))
theorem R91677 : Reach 91677 := rs (se 3 (by rfl) ⟨17189, by rfl⟩) (B 34379 (by norm_num) ⟨17189, by rfl⟩ (by norm_num))
theorem R91681 : Reach 91681 := rs (se 2 (by rfl) ⟨34380, by rfl⟩) (B 68761 (by norm_num) ⟨34380, by rfl⟩ (by norm_num))
theorem R91685 : Reach 91685 := rs (se 4 (by rfl) ⟨8595, by rfl⟩) (B 17191 (by norm_num) ⟨8595, by rfl⟩ (by norm_num))
theorem R91689 : Reach 91689 := rs (se 2 (by rfl) ⟨34383, by rfl⟩) (B 68767 (by norm_num) ⟨34383, by rfl⟩ (by norm_num))
theorem R91693 : Reach 91693 := rs (se 3 (by rfl) ⟨17192, by rfl⟩) (B 34385 (by norm_num) ⟨17192, by rfl⟩ (by norm_num))
theorem R91697 : Reach 91697 := rs (se 2 (by rfl) ⟨34386, by rfl⟩) (B 68773 (by norm_num) ⟨34386, by rfl⟩ (by norm_num))
theorem R91701 : Reach 91701 := rs (se 5 (by rfl) ⟨4298, by rfl⟩) (B 8597 (by norm_num) ⟨4298, by rfl⟩ (by norm_num))
theorem R91705 : Reach 91705 := rs (se 2 (by rfl) ⟨34389, by rfl⟩) (B 68779 (by norm_num) ⟨34389, by rfl⟩ (by norm_num))
theorem R91709 : Reach 91709 := rs (se 3 (by rfl) ⟨17195, by rfl⟩) (B 34391 (by norm_num) ⟨17195, by rfl⟩ (by norm_num))
theorem R91713 : Reach 91713 := rs (se 2 (by rfl) ⟨34392, by rfl⟩) (B 68785 (by norm_num) ⟨34392, by rfl⟩ (by norm_num))
theorem R91717 : Reach 91717 := rs (se 4 (by rfl) ⟨8598, by rfl⟩) (B 17197 (by norm_num) ⟨8598, by rfl⟩ (by norm_num))
theorem R91721 : Reach 91721 := rs (se 2 (by rfl) ⟨34395, by rfl⟩) (B 68791 (by norm_num) ⟨34395, by rfl⟩ (by norm_num))
theorem R91725 : Reach 91725 := rs (se 3 (by rfl) ⟨17198, by rfl⟩) (B 34397 (by norm_num) ⟨17198, by rfl⟩ (by norm_num))
theorem R157261 : Reach 157261 := rs (se 3 (by rfl) ⟨29486, by rfl⟩) (B 58973 (by norm_num) ⟨29486, by rfl⟩ (by norm_num))
theorem R91729 : Reach 91729 := rs (se 2 (by rfl) ⟨34398, by rfl⟩) (B 68797 (by norm_num) ⟨34398, by rfl⟩ (by norm_num))
theorem R91733 : Reach 91733 := rs (se 8 (by rfl) ⟨537, by rfl⟩) (B 1075 (by norm_num) ⟨537, by rfl⟩ (by norm_num))
theorem R91737 : Reach 91737 := rs (se 2 (by rfl) ⟨34401, by rfl⟩) (B 68803 (by norm_num) ⟨34401, by rfl⟩ (by norm_num))
theorem R91741 : Reach 91741 := rs (se 3 (by rfl) ⟨17201, by rfl⟩) (B 34403 (by norm_num) ⟨17201, by rfl⟩ (by norm_num))
theorem R91745 : Reach 91745 := rs (se 2 (by rfl) ⟨34404, by rfl⟩) (B 68809 (by norm_num) ⟨34404, by rfl⟩ (by norm_num))
theorem R91749 : Reach 91749 := rs (se 4 (by rfl) ⟨8601, by rfl⟩) (B 17203 (by norm_num) ⟨8601, by rfl⟩ (by norm_num))
theorem R91753 : Reach 91753 := rs (se 2 (by rfl) ⟨34407, by rfl⟩) (B 68815 (by norm_num) ⟨34407, by rfl⟩ (by norm_num))
theorem R91757 : Reach 91757 := rs (se 3 (by rfl) ⟨17204, by rfl⟩) (B 34409 (by norm_num) ⟨17204, by rfl⟩ (by norm_num))
theorem R91761 : Reach 91761 := rs (se 2 (by rfl) ⟨34410, by rfl⟩) (B 68821 (by norm_num) ⟨34410, by rfl⟩ (by norm_num))
theorem R91765 : Reach 91765 := rs (se 5 (by rfl) ⟨4301, by rfl⟩) (B 8603 (by norm_num) ⟨4301, by rfl⟩ (by norm_num))
theorem R91769 : Reach 91769 := rs (se 2 (by rfl) ⟨34413, by rfl⟩) (B 68827 (by norm_num) ⟨34413, by rfl⟩ (by norm_num))
theorem R91773 : Reach 91773 := rs (se 3 (by rfl) ⟨17207, by rfl⟩) (B 34415 (by norm_num) ⟨17207, by rfl⟩ (by norm_num))
theorem R91777 : Reach 91777 := rs (se 2 (by rfl) ⟨34416, by rfl⟩) (B 68833 (by norm_num) ⟨34416, by rfl⟩ (by norm_num))
theorem R91781 : Reach 91781 := rs (se 4 (by rfl) ⟨8604, by rfl⟩) (B 17209 (by norm_num) ⟨8604, by rfl⟩ (by norm_num))
theorem R91785 : Reach 91785 := rs (se 2 (by rfl) ⟨34419, by rfl⟩) (B 68839 (by norm_num) ⟨34419, by rfl⟩ (by norm_num))
theorem R91789 : Reach 91789 := rs (se 3 (by rfl) ⟨17210, by rfl⟩) (B 34421 (by norm_num) ⟨17210, by rfl⟩ (by norm_num))
theorem R91793 : Reach 91793 := rs (se 2 (by rfl) ⟨34422, by rfl⟩) (B 68845 (by norm_num) ⟨34422, by rfl⟩ (by norm_num))
theorem R91797 : Reach 91797 := rs (se 6 (by rfl) ⟨2151, by rfl⟩) (B 4303 (by norm_num) ⟨2151, by rfl⟩ (by norm_num))
theorem R91801 : Reach 91801 := rs (se 2 (by rfl) ⟨34425, by rfl⟩) (B 68851 (by norm_num) ⟨34425, by rfl⟩ (by norm_num))
theorem R91805 : Reach 91805 := rs (se 3 (by rfl) ⟨17213, by rfl⟩) (B 34427 (by norm_num) ⟨17213, by rfl⟩ (by norm_num))
theorem R91809 : Reach 91809 := rs (se 2 (by rfl) ⟨34428, by rfl⟩) (B 68857 (by norm_num) ⟨34428, by rfl⟩ (by norm_num))
theorem R91813 : Reach 91813 := rs (se 4 (by rfl) ⟨8607, by rfl⟩) (B 17215 (by norm_num) ⟨8607, by rfl⟩ (by norm_num))
theorem R157349 : Reach 157349 := rs (se 4 (by rfl) ⟨14751, by rfl⟩) (B 29503 (by norm_num) ⟨14751, by rfl⟩ (by norm_num))
theorem R91817 : Reach 91817 := rs (se 2 (by rfl) ⟨34431, by rfl⟩) (B 68863 (by norm_num) ⟨34431, by rfl⟩ (by norm_num))
theorem R91821 : Reach 91821 := rs (se 3 (by rfl) ⟨17216, by rfl⟩) (B 34433 (by norm_num) ⟨17216, by rfl⟩ (by norm_num))
theorem R91825 : Reach 91825 := rs (se 2 (by rfl) ⟨34434, by rfl⟩) (B 68869 (by norm_num) ⟨34434, by rfl⟩ (by norm_num))
theorem R91829 : Reach 91829 := rs (se 5 (by rfl) ⟨4304, by rfl⟩) (B 8609 (by norm_num) ⟨4304, by rfl⟩ (by norm_num))
theorem R91833 : Reach 91833 := rs (se 2 (by rfl) ⟨34437, by rfl⟩) (B 68875 (by norm_num) ⟨34437, by rfl⟩ (by norm_num))
theorem R91837 : Reach 91837 := rs (se 3 (by rfl) ⟨17219, by rfl⟩) (B 34439 (by norm_num) ⟨17219, by rfl⟩ (by norm_num))
theorem R91841 : Reach 91841 := rs (se 2 (by rfl) ⟨34440, by rfl⟩) (B 68881 (by norm_num) ⟨34440, by rfl⟩ (by norm_num))
theorem R91845 : Reach 91845 := rs (se 4 (by rfl) ⟨8610, by rfl⟩) (B 17221 (by norm_num) ⟨8610, by rfl⟩ (by norm_num))
theorem R91849 : Reach 91849 := rs (se 2 (by rfl) ⟨34443, by rfl⟩) (B 68887 (by norm_num) ⟨34443, by rfl⟩ (by norm_num))
theorem R91853 : Reach 91853 := rs (se 3 (by rfl) ⟨17222, by rfl⟩) (B 34445 (by norm_num) ⟨17222, by rfl⟩ (by norm_num))
theorem R91857 : Reach 91857 := rs (se 2 (by rfl) ⟨34446, by rfl⟩) (B 68893 (by norm_num) ⟨34446, by rfl⟩ (by norm_num))
theorem R91861 : Reach 91861 := rs (se 7 (by rfl) ⟨1076, by rfl⟩) (B 2153 (by norm_num) ⟨1076, by rfl⟩ (by norm_num))
theorem R91865 : Reach 91865 := rs (se 2 (by rfl) ⟨34449, by rfl⟩) (B 68899 (by norm_num) ⟨34449, by rfl⟩ (by norm_num))
theorem R91869 : Reach 91869 := rs (se 3 (by rfl) ⟨17225, by rfl⟩) (B 34451 (by norm_num) ⟨17225, by rfl⟩ (by norm_num))
theorem R91873 : Reach 91873 := rs (se 2 (by rfl) ⟨34452, by rfl⟩) (B 68905 (by norm_num) ⟨34452, by rfl⟩ (by norm_num))
theorem R91877 : Reach 91877 := rs (se 4 (by rfl) ⟨8613, by rfl⟩) (B 17227 (by norm_num) ⟨8613, by rfl⟩ (by norm_num))
theorem R91881 : Reach 91881 := rs (se 2 (by rfl) ⟨34455, by rfl⟩) (B 68911 (by norm_num) ⟨34455, by rfl⟩ (by norm_num))
theorem R91885 : Reach 91885 := rs (se 3 (by rfl) ⟨17228, by rfl⟩) (B 34457 (by norm_num) ⟨17228, by rfl⟩ (by norm_num))
theorem R91889 : Reach 91889 := rs (se 2 (by rfl) ⟨34458, by rfl⟩) (B 68917 (by norm_num) ⟨34458, by rfl⟩ (by norm_num))
theorem R91893 : Reach 91893 := rs (se 5 (by rfl) ⟨4307, by rfl⟩) (B 8615 (by norm_num) ⟨4307, by rfl⟩ (by norm_num))
theorem R91897 : Reach 91897 := rs (se 2 (by rfl) ⟨34461, by rfl⟩) (B 68923 (by norm_num) ⟨34461, by rfl⟩ (by norm_num))
theorem R91901 : Reach 91901 := rs (se 3 (by rfl) ⟨17231, by rfl⟩) (B 34463 (by norm_num) ⟨17231, by rfl⟩ (by norm_num))
theorem R91905 : Reach 91905 := rs (se 2 (by rfl) ⟨34464, by rfl⟩) (B 68929 (by norm_num) ⟨34464, by rfl⟩ (by norm_num))
theorem R91909 : Reach 91909 := rs (se 4 (by rfl) ⟨8616, by rfl⟩) (B 17233 (by norm_num) ⟨8616, by rfl⟩ (by norm_num))
theorem R91913 : Reach 91913 := rs (se 2 (by rfl) ⟨34467, by rfl⟩) (B 68935 (by norm_num) ⟨34467, by rfl⟩ (by norm_num))
theorem R91917 : Reach 91917 := rs (se 3 (by rfl) ⟨17234, by rfl⟩) (B 34469 (by norm_num) ⟨17234, by rfl⟩ (by norm_num))
theorem R91921 : Reach 91921 := rs (se 2 (by rfl) ⟨34470, by rfl⟩) (B 68941 (by norm_num) ⟨34470, by rfl⟩ (by norm_num))
theorem R91925 : Reach 91925 := rs (se 6 (by rfl) ⟨2154, by rfl⟩) (B 4309 (by norm_num) ⟨2154, by rfl⟩ (by norm_num))
theorem R91929 : Reach 91929 := rs (se 2 (by rfl) ⟨34473, by rfl⟩) (B 68947 (by norm_num) ⟨34473, by rfl⟩ (by norm_num))
theorem R91933 : Reach 91933 := rs (se 3 (by rfl) ⟨17237, by rfl⟩) (B 34475 (by norm_num) ⟨17237, by rfl⟩ (by norm_num))
theorem R91937 : Reach 91937 := rs (se 2 (by rfl) ⟨34476, by rfl⟩) (B 68953 (by norm_num) ⟨34476, by rfl⟩ (by norm_num))
theorem R91941 : Reach 91941 := rs (se 4 (by rfl) ⟨8619, by rfl⟩) (B 17239 (by norm_num) ⟨8619, by rfl⟩ (by norm_num))
theorem R157477 : Reach 157477 := rs (se 4 (by rfl) ⟨14763, by rfl⟩) (B 29527 (by norm_num) ⟨14763, by rfl⟩ (by norm_num))
theorem R91945 : Reach 91945 := rs (se 2 (by rfl) ⟨34479, by rfl⟩) (B 68959 (by norm_num) ⟨34479, by rfl⟩ (by norm_num))
theorem R91949 : Reach 91949 := rs (se 3 (by rfl) ⟨17240, by rfl⟩) (B 34481 (by norm_num) ⟨17240, by rfl⟩ (by norm_num))
theorem R91953 : Reach 91953 := rs (se 2 (by rfl) ⟨34482, by rfl⟩) (B 68965 (by norm_num) ⟨34482, by rfl⟩ (by norm_num))
theorem R91957 : Reach 91957 := rs (se 5 (by rfl) ⟨4310, by rfl⟩) (B 8621 (by norm_num) ⟨4310, by rfl⟩ (by norm_num))
theorem R91961 : Reach 91961 := rs (se 2 (by rfl) ⟨34485, by rfl⟩) (B 68971 (by norm_num) ⟨34485, by rfl⟩ (by norm_num))
theorem R91965 : Reach 91965 := rs (se 3 (by rfl) ⟨17243, by rfl⟩) (B 34487 (by norm_num) ⟨17243, by rfl⟩ (by norm_num))
theorem R91969 : Reach 91969 := rs (se 2 (by rfl) ⟨34488, by rfl⟩) (B 68977 (by norm_num) ⟨34488, by rfl⟩ (by norm_num))
theorem R91973 : Reach 91973 := rs (se 4 (by rfl) ⟨8622, by rfl⟩) (B 17245 (by norm_num) ⟨8622, by rfl⟩ (by norm_num))
theorem R91977 : Reach 91977 := rs (se 2 (by rfl) ⟨34491, by rfl⟩) (B 68983 (by norm_num) ⟨34491, by rfl⟩ (by norm_num))
theorem R91981 : Reach 91981 := rs (se 3 (by rfl) ⟨17246, by rfl⟩) (B 34493 (by norm_num) ⟨17246, by rfl⟩ (by norm_num))
theorem R91985 : Reach 91985 := rs (se 2 (by rfl) ⟨34494, by rfl⟩) (B 68989 (by norm_num) ⟨34494, by rfl⟩ (by norm_num))
theorem R91989 : Reach 91989 := rs (se 9 (by rfl) ⟨269, by rfl⟩) (B 539 (by norm_num) ⟨269, by rfl⟩ (by norm_num))
theorem R91993 : Reach 91993 := rs (se 2 (by rfl) ⟨34497, by rfl⟩) (B 68995 (by norm_num) ⟨34497, by rfl⟩ (by norm_num))
theorem R91997 : Reach 91997 := rs (se 3 (by rfl) ⟨17249, by rfl⟩) (B 34499 (by norm_num) ⟨17249, by rfl⟩ (by norm_num))
theorem R223069 : Reach 223069 := rs (se 3 (by rfl) ⟨41825, by rfl⟩) (B 83651 (by norm_num) ⟨41825, by rfl⟩ (by norm_num))
theorem R92001 : Reach 92001 := rs (se 2 (by rfl) ⟨34500, by rfl⟩) (B 69001 (by norm_num) ⟨34500, by rfl⟩ (by norm_num))
theorem R92005 : Reach 92005 := rs (se 4 (by rfl) ⟨8625, by rfl⟩) (B 17251 (by norm_num) ⟨8625, by rfl⟩ (by norm_num))
theorem R92009 : Reach 92009 := rs (se 2 (by rfl) ⟨34503, by rfl⟩) (B 69007 (by norm_num) ⟨34503, by rfl⟩ (by norm_num))
theorem R92013 : Reach 92013 := rs (se 3 (by rfl) ⟨17252, by rfl⟩) (B 34505 (by norm_num) ⟨17252, by rfl⟩ (by norm_num))
theorem R92017 : Reach 92017 := rs (se 2 (by rfl) ⟨34506, by rfl⟩) (B 69013 (by norm_num) ⟨34506, by rfl⟩ (by norm_num))
theorem R92021 : Reach 92021 := rs (se 5 (by rfl) ⟨4313, by rfl⟩) (B 8627 (by norm_num) ⟨4313, by rfl⟩ (by norm_num))
theorem R92025 : Reach 92025 := rs (se 2 (by rfl) ⟨34509, by rfl⟩) (B 69019 (by norm_num) ⟨34509, by rfl⟩ (by norm_num))
theorem R92029 : Reach 92029 := rs (se 3 (by rfl) ⟨17255, by rfl⟩) (B 34511 (by norm_num) ⟨17255, by rfl⟩ (by norm_num))
theorem R157565 : Reach 157565 := rs (se 3 (by rfl) ⟨29543, by rfl⟩) (B 59087 (by norm_num) ⟨29543, by rfl⟩ (by norm_num))
theorem R92033 : Reach 92033 := rs (se 2 (by rfl) ⟨34512, by rfl⟩) (B 69025 (by norm_num) ⟨34512, by rfl⟩ (by norm_num))
theorem R92037 : Reach 92037 := rs (se 4 (by rfl) ⟨8628, by rfl⟩) (B 17257 (by norm_num) ⟨8628, by rfl⟩ (by norm_num))
theorem R92041 : Reach 92041 := rs (se 2 (by rfl) ⟨34515, by rfl⟩) (B 69031 (by norm_num) ⟨34515, by rfl⟩ (by norm_num))
theorem R92045 : Reach 92045 := rs (se 3 (by rfl) ⟨17258, by rfl⟩) (B 34517 (by norm_num) ⟨17258, by rfl⟩ (by norm_num))
theorem R92049 : Reach 92049 := rs (se 2 (by rfl) ⟨34518, by rfl⟩) (B 69037 (by norm_num) ⟨34518, by rfl⟩ (by norm_num))
theorem R92053 : Reach 92053 := rs (se 6 (by rfl) ⟨2157, by rfl⟩) (B 4315 (by norm_num) ⟨2157, by rfl⟩ (by norm_num))
theorem R92057 : Reach 92057 := rs (se 2 (by rfl) ⟨34521, by rfl⟩) (B 69043 (by norm_num) ⟨34521, by rfl⟩ (by norm_num))
theorem R92061 : Reach 92061 := rs (se 3 (by rfl) ⟨17261, by rfl⟩) (B 34523 (by norm_num) ⟨17261, by rfl⟩ (by norm_num))
theorem R92065 : Reach 92065 := rs (se 2 (by rfl) ⟨34524, by rfl⟩) (B 69049 (by norm_num) ⟨34524, by rfl⟩ (by norm_num))
theorem R92069 : Reach 92069 := rs (se 4 (by rfl) ⟨8631, by rfl⟩) (B 17263 (by norm_num) ⟨8631, by rfl⟩ (by norm_num))
theorem R92073 : Reach 92073 := rs (se 2 (by rfl) ⟨34527, by rfl⟩) (B 69055 (by norm_num) ⟨34527, by rfl⟩ (by norm_num))
theorem R92077 : Reach 92077 := rs (se 3 (by rfl) ⟨17264, by rfl⟩) (B 34529 (by norm_num) ⟨17264, by rfl⟩ (by norm_num))
theorem R92081 : Reach 92081 := rs (se 2 (by rfl) ⟨34530, by rfl⟩) (B 69061 (by norm_num) ⟨34530, by rfl⟩ (by norm_num))
theorem R92085 : Reach 92085 := rs (se 5 (by rfl) ⟨4316, by rfl⟩) (B 8633 (by norm_num) ⟨4316, by rfl⟩ (by norm_num))
theorem R92089 : Reach 92089 := rs (se 2 (by rfl) ⟨34533, by rfl⟩) (B 69067 (by norm_num) ⟨34533, by rfl⟩ (by norm_num))
theorem R92093 : Reach 92093 := rs (se 3 (by rfl) ⟨17267, by rfl⟩) (B 34535 (by norm_num) ⟨17267, by rfl⟩ (by norm_num))
theorem R223165 : Reach 223165 := rs (se 3 (by rfl) ⟨41843, by rfl⟩) (B 83687 (by norm_num) ⟨41843, by rfl⟩ (by norm_num))
theorem R92097 : Reach 92097 := rs (se 2 (by rfl) ⟨34536, by rfl⟩) (B 69073 (by norm_num) ⟨34536, by rfl⟩ (by norm_num))
theorem R92101 : Reach 92101 := rs (se 4 (by rfl) ⟨8634, by rfl⟩) (B 17269 (by norm_num) ⟨8634, by rfl⟩ (by norm_num))
theorem R92105 : Reach 92105 := rs (se 2 (by rfl) ⟨34539, by rfl⟩) (B 69079 (by norm_num) ⟨34539, by rfl⟩ (by norm_num))
theorem R92109 : Reach 92109 := rs (se 3 (by rfl) ⟨17270, by rfl⟩) (B 34541 (by norm_num) ⟨17270, by rfl⟩ (by norm_num))
theorem R92113 : Reach 92113 := rs (se 2 (by rfl) ⟨34542, by rfl⟩) (B 69085 (by norm_num) ⟨34542, by rfl⟩ (by norm_num))
theorem R92117 : Reach 92117 := rs (se 7 (by rfl) ⟨1079, by rfl⟩) (B 2159 (by norm_num) ⟨1079, by rfl⟩ (by norm_num))
theorem R190421 : Reach 190421 := rs (se 7 (by rfl) ⟨2231, by rfl⟩) (B 4463 (by norm_num) ⟨2231, by rfl⟩ (by norm_num))
theorem R92121 : Reach 92121 := rs (se 2 (by rfl) ⟨34545, by rfl⟩) (B 69091 (by norm_num) ⟨34545, by rfl⟩ (by norm_num))
theorem R92125 : Reach 92125 := rs (se 3 (by rfl) ⟨17273, by rfl⟩) (B 34547 (by norm_num) ⟨17273, by rfl⟩ (by norm_num))
theorem R92129 : Reach 92129 := rs (se 2 (by rfl) ⟨34548, by rfl⟩) (B 69097 (by norm_num) ⟨34548, by rfl⟩ (by norm_num))
theorem R92133 : Reach 92133 := rs (se 4 (by rfl) ⟨8637, by rfl⟩) (B 17275 (by norm_num) ⟨8637, by rfl⟩ (by norm_num))
theorem R92137 : Reach 92137 := rs (se 2 (by rfl) ⟨34551, by rfl⟩) (B 69103 (by norm_num) ⟨34551, by rfl⟩ (by norm_num))
theorem R92141 : Reach 92141 := rs (se 3 (by rfl) ⟨17276, by rfl⟩) (B 34553 (by norm_num) ⟨17276, by rfl⟩ (by norm_num))
theorem R92145 : Reach 92145 := rs (se 2 (by rfl) ⟨34554, by rfl⟩) (B 69109 (by norm_num) ⟨34554, by rfl⟩ (by norm_num))
theorem R92149 : Reach 92149 := rs (se 5 (by rfl) ⟨4319, by rfl⟩) (B 8639 (by norm_num) ⟨4319, by rfl⟩ (by norm_num))
theorem R92153 : Reach 92153 := rs (se 2 (by rfl) ⟨34557, by rfl⟩) (B 69115 (by norm_num) ⟨34557, by rfl⟩ (by norm_num))
theorem R92157 : Reach 92157 := rs (se 3 (by rfl) ⟨17279, by rfl⟩) (B 34559 (by norm_num) ⟨17279, by rfl⟩ (by norm_num))
theorem R157693 : Reach 157693 := rs (se 3 (by rfl) ⟨29567, by rfl⟩) (B 59135 (by norm_num) ⟨29567, by rfl⟩ (by norm_num))
theorem R92161 : Reach 92161 := rs (se 2 (by rfl) ⟨34560, by rfl⟩) (B 69121 (by norm_num) ⟨34560, by rfl⟩ (by norm_num))
theorem R92165 : Reach 92165 := rs (se 4 (by rfl) ⟨8640, by rfl⟩) (B 17281 (by norm_num) ⟨8640, by rfl⟩ (by norm_num))
theorem R92169 : Reach 92169 := rs (se 2 (by rfl) ⟨34563, by rfl⟩) (B 69127 (by norm_num) ⟨34563, by rfl⟩ (by norm_num))
theorem R92173 : Reach 92173 := rs (se 3 (by rfl) ⟨17282, by rfl⟩) (B 34565 (by norm_num) ⟨17282, by rfl⟩ (by norm_num))
theorem R92177 : Reach 92177 := rs (se 2 (by rfl) ⟨34566, by rfl⟩) (B 69133 (by norm_num) ⟨34566, by rfl⟩ (by norm_num))
theorem R92181 : Reach 92181 := rs (se 6 (by rfl) ⟨2160, by rfl⟩) (B 4321 (by norm_num) ⟨2160, by rfl⟩ (by norm_num))
theorem R92185 : Reach 92185 := rs (se 2 (by rfl) ⟨34569, by rfl⟩) (B 69139 (by norm_num) ⟨34569, by rfl⟩ (by norm_num))
theorem R92189 : Reach 92189 := rs (se 3 (by rfl) ⟨17285, by rfl⟩) (B 34571 (by norm_num) ⟨17285, by rfl⟩ (by norm_num))
theorem R92193 : Reach 92193 := rs (se 2 (by rfl) ⟨34572, by rfl⟩) (B 69145 (by norm_num) ⟨34572, by rfl⟩ (by norm_num))
theorem R92197 : Reach 92197 := rs (se 4 (by rfl) ⟨8643, by rfl⟩) (B 17287 (by norm_num) ⟨8643, by rfl⟩ (by norm_num))
theorem R92201 : Reach 92201 := rs (se 2 (by rfl) ⟨34575, by rfl⟩) (B 69151 (by norm_num) ⟨34575, by rfl⟩ (by norm_num))
theorem R92205 : Reach 92205 := rs (se 3 (by rfl) ⟨17288, by rfl⟩) (B 34577 (by norm_num) ⟨17288, by rfl⟩ (by norm_num))
theorem R92209 : Reach 92209 := rs (se 2 (by rfl) ⟨34578, by rfl⟩) (B 69157 (by norm_num) ⟨34578, by rfl⟩ (by norm_num))
theorem R92213 : Reach 92213 := rs (se 5 (by rfl) ⟨4322, by rfl⟩) (B 8645 (by norm_num) ⟨4322, by rfl⟩ (by norm_num))
theorem R92217 : Reach 92217 := rs (se 2 (by rfl) ⟨34581, by rfl⟩) (B 69163 (by norm_num) ⟨34581, by rfl⟩ (by norm_num))
theorem R92221 : Reach 92221 := rs (se 3 (by rfl) ⟨17291, by rfl⟩) (B 34583 (by norm_num) ⟨17291, by rfl⟩ (by norm_num))
theorem R92225 : Reach 92225 := rs (se 2 (by rfl) ⟨34584, by rfl⟩) (B 69169 (by norm_num) ⟨34584, by rfl⟩ (by norm_num))
theorem R92229 : Reach 92229 := rs (se 4 (by rfl) ⟨8646, by rfl⟩) (B 17293 (by norm_num) ⟨8646, by rfl⟩ (by norm_num))
theorem R92233 : Reach 92233 := rs (se 2 (by rfl) ⟨34587, by rfl⟩) (B 69175 (by norm_num) ⟨34587, by rfl⟩ (by norm_num))
theorem R92237 : Reach 92237 := rs (se 3 (by rfl) ⟨17294, by rfl⟩) (B 34589 (by norm_num) ⟨17294, by rfl⟩ (by norm_num))
theorem R92241 : Reach 92241 := rs (se 2 (by rfl) ⟨34590, by rfl⟩) (B 69181 (by norm_num) ⟨34590, by rfl⟩ (by norm_num))
theorem R92245 : Reach 92245 := rs (se 8 (by rfl) ⟨540, by rfl⟩) (B 1081 (by norm_num) ⟨540, by rfl⟩ (by norm_num))
theorem R157781 : Reach 157781 := rs (se 8 (by rfl) ⟨924, by rfl⟩) (B 1849 (by norm_num) ⟨924, by rfl⟩ (by norm_num))
theorem R92249 : Reach 92249 := rs (se 2 (by rfl) ⟨34593, by rfl⟩) (B 69187 (by norm_num) ⟨34593, by rfl⟩ (by norm_num))
theorem R92253 : Reach 92253 := rs (se 3 (by rfl) ⟨17297, by rfl⟩) (B 34595 (by norm_num) ⟨17297, by rfl⟩ (by norm_num))
theorem R92257 : Reach 92257 := rs (se 2 (by rfl) ⟨34596, by rfl⟩) (B 69193 (by norm_num) ⟨34596, by rfl⟩ (by norm_num))
theorem R92261 : Reach 92261 := rs (se 4 (by rfl) ⟨8649, by rfl⟩) (B 17299 (by norm_num) ⟨8649, by rfl⟩ (by norm_num))
theorem R92265 : Reach 92265 := rs (se 2 (by rfl) ⟨34599, by rfl⟩) (B 69199 (by norm_num) ⟨34599, by rfl⟩ (by norm_num))
theorem R92269 : Reach 92269 := rs (se 3 (by rfl) ⟨17300, by rfl⟩) (B 34601 (by norm_num) ⟨17300, by rfl⟩ (by norm_num))
theorem R92273 : Reach 92273 := rs (se 2 (by rfl) ⟨34602, by rfl⟩) (B 69205 (by norm_num) ⟨34602, by rfl⟩ (by norm_num))
theorem R92277 : Reach 92277 := rs (se 5 (by rfl) ⟨4325, by rfl⟩) (B 8651 (by norm_num) ⟨4325, by rfl⟩ (by norm_num))
theorem R92281 : Reach 92281 := rs (se 2 (by rfl) ⟨34605, by rfl⟩) (B 69211 (by norm_num) ⟨34605, by rfl⟩ (by norm_num))
theorem R92285 : Reach 92285 := rs (se 3 (by rfl) ⟨17303, by rfl⟩) (B 34607 (by norm_num) ⟨17303, by rfl⟩ (by norm_num))
theorem R223357 : Reach 223357 := rs (se 3 (by rfl) ⟨41879, by rfl⟩) (B 83759 (by norm_num) ⟨41879, by rfl⟩ (by norm_num))
theorem R92289 : Reach 92289 := rs (se 2 (by rfl) ⟨34608, by rfl⟩) (B 69217 (by norm_num) ⟨34608, by rfl⟩ (by norm_num))
theorem R92293 : Reach 92293 := rs (se 4 (by rfl) ⟨8652, by rfl⟩) (B 17305 (by norm_num) ⟨8652, by rfl⟩ (by norm_num))
theorem R92297 : Reach 92297 := rs (se 2 (by rfl) ⟨34611, by rfl⟩) (B 69223 (by norm_num) ⟨34611, by rfl⟩ (by norm_num))
theorem R92301 : Reach 92301 := rs (se 3 (by rfl) ⟨17306, by rfl⟩) (B 34613 (by norm_num) ⟨17306, by rfl⟩ (by norm_num))
theorem R92305 : Reach 92305 := rs (se 2 (by rfl) ⟨34614, by rfl⟩) (B 69229 (by norm_num) ⟨34614, by rfl⟩ (by norm_num))
theorem R92309 : Reach 92309 := rs (se 6 (by rfl) ⟨2163, by rfl⟩) (B 4327 (by norm_num) ⟨2163, by rfl⟩ (by norm_num))
theorem R288917 : Reach 288917 := rs (se 6 (by rfl) ⟨6771, by rfl⟩) (B 13543 (by norm_num) ⟨6771, by rfl⟩ (by norm_num))
theorem R92313 : Reach 92313 := rs (se 2 (by rfl) ⟨34617, by rfl⟩) (B 69235 (by norm_num) ⟨34617, by rfl⟩ (by norm_num))
theorem R92317 : Reach 92317 := rs (se 3 (by rfl) ⟨17309, by rfl⟩) (B 34619 (by norm_num) ⟨17309, by rfl⟩ (by norm_num))
theorem R92321 : Reach 92321 := rs (se 2 (by rfl) ⟨34620, by rfl⟩) (B 69241 (by norm_num) ⟨34620, by rfl⟩ (by norm_num))
theorem R92325 : Reach 92325 := rs (se 4 (by rfl) ⟨8655, by rfl⟩) (B 17311 (by norm_num) ⟨8655, by rfl⟩ (by norm_num))
theorem R92329 : Reach 92329 := rs (se 2 (by rfl) ⟨34623, by rfl⟩) (B 69247 (by norm_num) ⟨34623, by rfl⟩ (by norm_num))
theorem R92333 : Reach 92333 := rs (se 3 (by rfl) ⟨17312, by rfl⟩) (B 34625 (by norm_num) ⟨17312, by rfl⟩ (by norm_num))
theorem R92337 : Reach 92337 := rs (se 2 (by rfl) ⟨34626, by rfl⟩) (B 69253 (by norm_num) ⟨34626, by rfl⟩ (by norm_num))
theorem R92341 : Reach 92341 := rs (se 5 (by rfl) ⟨4328, by rfl⟩) (B 8657 (by norm_num) ⟨4328, by rfl⟩ (by norm_num))
theorem R92345 : Reach 92345 := rs (se 2 (by rfl) ⟨34629, by rfl⟩) (B 69259 (by norm_num) ⟨34629, by rfl⟩ (by norm_num))
theorem R92349 : Reach 92349 := rs (se 3 (by rfl) ⟨17315, by rfl⟩) (B 34631 (by norm_num) ⟨17315, by rfl⟩ (by norm_num))
theorem R92353 : Reach 92353 := rs (se 2 (by rfl) ⟨34632, by rfl⟩) (B 69265 (by norm_num) ⟨34632, by rfl⟩ (by norm_num))
theorem R92357 : Reach 92357 := rs (se 4 (by rfl) ⟨8658, by rfl⟩) (B 17317 (by norm_num) ⟨8658, by rfl⟩ (by norm_num))
theorem R92361 : Reach 92361 := rs (se 2 (by rfl) ⟨34635, by rfl⟩) (B 69271 (by norm_num) ⟨34635, by rfl⟩ (by norm_num))
theorem R92365 : Reach 92365 := rs (se 3 (by rfl) ⟨17318, by rfl⟩) (B 34637 (by norm_num) ⟨17318, by rfl⟩ (by norm_num))
theorem R92369 : Reach 92369 := rs (se 2 (by rfl) ⟨34638, by rfl⟩) (B 69277 (by norm_num) ⟨34638, by rfl⟩ (by norm_num))
theorem R92373 : Reach 92373 := rs (se 7 (by rfl) ⟨1082, by rfl⟩) (B 2165 (by norm_num) ⟨1082, by rfl⟩ (by norm_num))
theorem R157909 : Reach 157909 := rs (se 7 (by rfl) ⟨1850, by rfl⟩) (B 3701 (by norm_num) ⟨1850, by rfl⟩ (by norm_num))
theorem R92377 : Reach 92377 := rs (se 2 (by rfl) ⟨34641, by rfl⟩) (B 69283 (by norm_num) ⟨34641, by rfl⟩ (by norm_num))
theorem R92381 : Reach 92381 := rs (se 3 (by rfl) ⟨17321, by rfl⟩) (B 34643 (by norm_num) ⟨17321, by rfl⟩ (by norm_num))
theorem R92385 : Reach 92385 := rs (se 2 (by rfl) ⟨34644, by rfl⟩) (B 69289 (by norm_num) ⟨34644, by rfl⟩ (by norm_num))
theorem R92389 : Reach 92389 := rs (se 4 (by rfl) ⟨8661, by rfl⟩) (B 17323 (by norm_num) ⟨8661, by rfl⟩ (by norm_num))
theorem R92393 : Reach 92393 := rs (se 2 (by rfl) ⟨34647, by rfl⟩) (B 69295 (by norm_num) ⟨34647, by rfl⟩ (by norm_num))
theorem R92397 : Reach 92397 := rs (se 3 (by rfl) ⟨17324, by rfl⟩) (B 34649 (by norm_num) ⟨17324, by rfl⟩ (by norm_num))
theorem R92401 : Reach 92401 := rs (se 2 (by rfl) ⟨34650, by rfl⟩) (B 69301 (by norm_num) ⟨34650, by rfl⟩ (by norm_num))
theorem R92405 : Reach 92405 := rs (se 5 (by rfl) ⟨4331, by rfl⟩) (B 8663 (by norm_num) ⟨4331, by rfl⟩ (by norm_num))
theorem R92409 : Reach 92409 := rs (se 2 (by rfl) ⟨34653, by rfl⟩) (B 69307 (by norm_num) ⟨34653, by rfl⟩ (by norm_num))
theorem R92413 : Reach 92413 := rs (se 3 (by rfl) ⟨17327, by rfl⟩) (B 34655 (by norm_num) ⟨17327, by rfl⟩ (by norm_num))
theorem R92417 : Reach 92417 := rs (se 2 (by rfl) ⟨34656, by rfl⟩) (B 69313 (by norm_num) ⟨34656, by rfl⟩ (by norm_num))
theorem R92421 : Reach 92421 := rs (se 4 (by rfl) ⟨8664, by rfl⟩) (B 17329 (by norm_num) ⟨8664, by rfl⟩ (by norm_num))
theorem R92425 : Reach 92425 := rs (se 2 (by rfl) ⟨34659, by rfl⟩) (B 69319 (by norm_num) ⟨34659, by rfl⟩ (by norm_num))
theorem R92429 : Reach 92429 := rs (se 3 (by rfl) ⟨17330, by rfl⟩) (B 34661 (by norm_num) ⟨17330, by rfl⟩ (by norm_num))
theorem R92433 : Reach 92433 := rs (se 2 (by rfl) ⟨34662, by rfl⟩) (B 69325 (by norm_num) ⟨34662, by rfl⟩ (by norm_num))
theorem R92437 : Reach 92437 := rs (se 6 (by rfl) ⟨2166, by rfl⟩) (B 4333 (by norm_num) ⟨2166, by rfl⟩ (by norm_num))
theorem R92441 : Reach 92441 := rs (se 2 (by rfl) ⟨34665, by rfl⟩) (B 69331 (by norm_num) ⟨34665, by rfl⟩ (by norm_num))
theorem R92445 : Reach 92445 := rs (se 3 (by rfl) ⟨17333, by rfl⟩) (B 34667 (by norm_num) ⟨17333, by rfl⟩ (by norm_num))
theorem R92449 : Reach 92449 := rs (se 2 (by rfl) ⟨34668, by rfl⟩) (B 69337 (by norm_num) ⟨34668, by rfl⟩ (by norm_num))
theorem R92453 : Reach 92453 := rs (se 4 (by rfl) ⟨8667, by rfl⟩) (B 17335 (by norm_num) ⟨8667, by rfl⟩ (by norm_num))
theorem R92457 : Reach 92457 := rs (se 2 (by rfl) ⟨34671, by rfl⟩) (B 69343 (by norm_num) ⟨34671, by rfl⟩ (by norm_num))
theorem R92461 : Reach 92461 := rs (se 3 (by rfl) ⟨17336, by rfl⟩) (B 34673 (by norm_num) ⟨17336, by rfl⟩ (by norm_num))
theorem R157997 : Reach 157997 := rs (se 3 (by rfl) ⟨29624, by rfl⟩) (B 59249 (by norm_num) ⟨29624, by rfl⟩ (by norm_num))
theorem R92465 : Reach 92465 := rs (se 2 (by rfl) ⟨34674, by rfl⟩) (B 69349 (by norm_num) ⟨34674, by rfl⟩ (by norm_num))
theorem R92469 : Reach 92469 := rs (se 5 (by rfl) ⟨4334, by rfl⟩) (B 8669 (by norm_num) ⟨4334, by rfl⟩ (by norm_num))
theorem R92473 : Reach 92473 := rs (se 2 (by rfl) ⟨34677, by rfl⟩) (B 69355 (by norm_num) ⟨34677, by rfl⟩ (by norm_num))
theorem R92477 : Reach 92477 := rs (se 3 (by rfl) ⟨17339, by rfl⟩) (B 34679 (by norm_num) ⟨17339, by rfl⟩ (by norm_num))
theorem R92481 : Reach 92481 := rs (se 2 (by rfl) ⟨34680, by rfl⟩) (B 69361 (by norm_num) ⟨34680, by rfl⟩ (by norm_num))
theorem R92485 : Reach 92485 := rs (se 4 (by rfl) ⟨8670, by rfl⟩) (B 17341 (by norm_num) ⟨8670, by rfl⟩ (by norm_num))
theorem R92489 : Reach 92489 := rs (se 2 (by rfl) ⟨34683, by rfl⟩) (B 69367 (by norm_num) ⟨34683, by rfl⟩ (by norm_num))
theorem R92493 : Reach 92493 := rs (se 3 (by rfl) ⟨17342, by rfl⟩) (B 34685 (by norm_num) ⟨17342, by rfl⟩ (by norm_num))
theorem R92497 : Reach 92497 := rs (se 2 (by rfl) ⟨34686, by rfl⟩) (B 69373 (by norm_num) ⟨34686, by rfl⟩ (by norm_num))
theorem R92501 : Reach 92501 := rs (se 10 (by rfl) ⟨135, by rfl⟩) (B 271 (by norm_num) ⟨135, by rfl⟩ (by norm_num))
theorem R92505 : Reach 92505 := rs (se 2 (by rfl) ⟨34689, by rfl⟩) (B 69379 (by norm_num) ⟨34689, by rfl⟩ (by norm_num))
theorem R92509 : Reach 92509 := rs (se 3 (by rfl) ⟨17345, by rfl⟩) (B 34691 (by norm_num) ⟨17345, by rfl⟩ (by norm_num))
theorem R92513 : Reach 92513 := rs (se 2 (by rfl) ⟨34692, by rfl⟩) (B 69385 (by norm_num) ⟨34692, by rfl⟩ (by norm_num))
theorem R92517 : Reach 92517 := rs (se 4 (by rfl) ⟨8673, by rfl⟩) (B 17347 (by norm_num) ⟨8673, by rfl⟩ (by norm_num))
theorem R92521 : Reach 92521 := rs (se 2 (by rfl) ⟨34695, by rfl⟩) (B 69391 (by norm_num) ⟨34695, by rfl⟩ (by norm_num))
theorem R92525 : Reach 92525 := rs (se 3 (by rfl) ⟨17348, by rfl⟩) (B 34697 (by norm_num) ⟨17348, by rfl⟩ (by norm_num))
theorem R92529 : Reach 92529 := rs (se 2 (by rfl) ⟨34698, by rfl⟩) (B 69397 (by norm_num) ⟨34698, by rfl⟩ (by norm_num))
theorem R92533 : Reach 92533 := rs (se 5 (by rfl) ⟨4337, by rfl⟩) (B 8675 (by norm_num) ⟨4337, by rfl⟩ (by norm_num))
theorem R92537 : Reach 92537 := rs (se 2 (by rfl) ⟨34701, by rfl⟩) (B 69403 (by norm_num) ⟨34701, by rfl⟩ (by norm_num))
theorem R92541 : Reach 92541 := rs (se 3 (by rfl) ⟨17351, by rfl⟩) (B 34703 (by norm_num) ⟨17351, by rfl⟩ (by norm_num))
theorem R92545 : Reach 92545 := rs (se 2 (by rfl) ⟨34704, by rfl⟩) (B 69409 (by norm_num) ⟨34704, by rfl⟩ (by norm_num))
theorem R92549 : Reach 92549 := rs (se 4 (by rfl) ⟨8676, by rfl⟩) (B 17353 (by norm_num) ⟨8676, by rfl⟩ (by norm_num))
theorem R92553 : Reach 92553 := rs (se 2 (by rfl) ⟨34707, by rfl⟩) (B 69415 (by norm_num) ⟨34707, by rfl⟩ (by norm_num))
theorem R92557 : Reach 92557 := rs (se 3 (by rfl) ⟨17354, by rfl⟩) (B 34709 (by norm_num) ⟨17354, by rfl⟩ (by norm_num))
theorem R92561 : Reach 92561 := rs (se 2 (by rfl) ⟨34710, by rfl⟩) (B 69421 (by norm_num) ⟨34710, by rfl⟩ (by norm_num))
theorem R92565 : Reach 92565 := rs (se 6 (by rfl) ⟨2169, by rfl⟩) (B 4339 (by norm_num) ⟨2169, by rfl⟩ (by norm_num))
theorem R92569 : Reach 92569 := rs (se 2 (by rfl) ⟨34713, by rfl⟩) (B 69427 (by norm_num) ⟨34713, by rfl⟩ (by norm_num))
theorem R92573 : Reach 92573 := rs (se 3 (by rfl) ⟨17357, by rfl⟩) (B 34715 (by norm_num) ⟨17357, by rfl⟩ (by norm_num))
theorem R92577 : Reach 92577 := rs (se 2 (by rfl) ⟨34716, by rfl⟩) (B 69433 (by norm_num) ⟨34716, by rfl⟩ (by norm_num))
theorem R92581 : Reach 92581 := rs (se 4 (by rfl) ⟨8679, by rfl⟩) (B 17359 (by norm_num) ⟨8679, by rfl⟩ (by norm_num))
theorem R92585 : Reach 92585 := rs (se 2 (by rfl) ⟨34719, by rfl⟩) (B 69439 (by norm_num) ⟨34719, by rfl⟩ (by norm_num))
theorem R92589 : Reach 92589 := rs (se 3 (by rfl) ⟨17360, by rfl⟩) (B 34721 (by norm_num) ⟨17360, by rfl⟩ (by norm_num))
theorem R158125 : Reach 158125 := rs (se 3 (by rfl) ⟨29648, by rfl⟩) (B 59297 (by norm_num) ⟨29648, by rfl⟩ (by norm_num))
theorem R92593 : Reach 92593 := rs (se 2 (by rfl) ⟨34722, by rfl⟩) (B 69445 (by norm_num) ⟨34722, by rfl⟩ (by norm_num))
theorem R92597 : Reach 92597 := rs (se 5 (by rfl) ⟨4340, by rfl⟩) (B 8681 (by norm_num) ⟨4340, by rfl⟩ (by norm_num))
theorem R92601 : Reach 92601 := rs (se 2 (by rfl) ⟨34725, by rfl⟩) (B 69451 (by norm_num) ⟨34725, by rfl⟩ (by norm_num))
theorem R92605 : Reach 92605 := rs (se 3 (by rfl) ⟨17363, by rfl⟩) (B 34727 (by norm_num) ⟨17363, by rfl⟩ (by norm_num))
theorem R92609 : Reach 92609 := rs (se 2 (by rfl) ⟨34728, by rfl⟩) (B 69457 (by norm_num) ⟨34728, by rfl⟩ (by norm_num))
theorem R92613 : Reach 92613 := rs (se 4 (by rfl) ⟨8682, by rfl⟩) (B 17365 (by norm_num) ⟨8682, by rfl⟩ (by norm_num))
theorem R223685 : Reach 223685 := rs (se 4 (by rfl) ⟨20970, by rfl⟩) (B 41941 (by norm_num) ⟨20970, by rfl⟩ (by norm_num))
theorem R92617 : Reach 92617 := rs (se 2 (by rfl) ⟨34731, by rfl⟩) (B 69463 (by norm_num) ⟨34731, by rfl⟩ (by norm_num))
theorem R92621 : Reach 92621 := rs (se 3 (by rfl) ⟨17366, by rfl⟩) (B 34733 (by norm_num) ⟨17366, by rfl⟩ (by norm_num))
theorem R92625 : Reach 92625 := rs (se 2 (by rfl) ⟨34734, by rfl⟩) (B 69469 (by norm_num) ⟨34734, by rfl⟩ (by norm_num))
theorem R92629 : Reach 92629 := rs (se 7 (by rfl) ⟨1085, by rfl⟩) (B 2171 (by norm_num) ⟨1085, by rfl⟩ (by norm_num))
theorem R92633 : Reach 92633 := rs (se 2 (by rfl) ⟨34737, by rfl⟩) (B 69475 (by norm_num) ⟨34737, by rfl⟩ (by norm_num))
theorem R92637 : Reach 92637 := rs (se 3 (by rfl) ⟨17369, by rfl⟩) (B 34739 (by norm_num) ⟨17369, by rfl⟩ (by norm_num))
theorem R92641 : Reach 92641 := rs (se 2 (by rfl) ⟨34740, by rfl⟩) (B 69481 (by norm_num) ⟨34740, by rfl⟩ (by norm_num))
theorem R92645 : Reach 92645 := rs (se 4 (by rfl) ⟨8685, by rfl⟩) (B 17371 (by norm_num) ⟨8685, by rfl⟩ (by norm_num))
theorem R92649 : Reach 92649 := rs (se 2 (by rfl) ⟨34743, by rfl⟩) (B 69487 (by norm_num) ⟨34743, by rfl⟩ (by norm_num))
theorem R92653 : Reach 92653 := rs (se 3 (by rfl) ⟨17372, by rfl⟩) (B 34745 (by norm_num) ⟨17372, by rfl⟩ (by norm_num))
theorem R92657 : Reach 92657 := rs (se 2 (by rfl) ⟨34746, by rfl⟩) (B 69493 (by norm_num) ⟨34746, by rfl⟩ (by norm_num))
theorem R92661 : Reach 92661 := rs (se 5 (by rfl) ⟨4343, by rfl⟩) (B 8687 (by norm_num) ⟨4343, by rfl⟩ (by norm_num))
theorem R92665 : Reach 92665 := rs (se 2 (by rfl) ⟨34749, by rfl⟩) (B 69499 (by norm_num) ⟨34749, by rfl⟩ (by norm_num))
theorem R92669 : Reach 92669 := rs (se 3 (by rfl) ⟨17375, by rfl⟩) (B 34751 (by norm_num) ⟨17375, by rfl⟩ (by norm_num))
theorem R92673 : Reach 92673 := rs (se 2 (by rfl) ⟨34752, by rfl⟩) (B 69505 (by norm_num) ⟨34752, by rfl⟩ (by norm_num))
theorem R92677 : Reach 92677 := rs (se 4 (by rfl) ⟨8688, by rfl⟩) (B 17377 (by norm_num) ⟨8688, by rfl⟩ (by norm_num))
theorem R158213 : Reach 158213 := rs (se 4 (by rfl) ⟨14832, by rfl⟩) (B 29665 (by norm_num) ⟨14832, by rfl⟩ (by norm_num))
theorem R92681 : Reach 92681 := rs (se 2 (by rfl) ⟨34755, by rfl⟩) (B 69511 (by norm_num) ⟨34755, by rfl⟩ (by norm_num))
theorem R92685 : Reach 92685 := rs (se 3 (by rfl) ⟨17378, by rfl⟩) (B 34757 (by norm_num) ⟨17378, by rfl⟩ (by norm_num))
theorem R92689 : Reach 92689 := rs (se 2 (by rfl) ⟨34758, by rfl⟩) (B 69517 (by norm_num) ⟨34758, by rfl⟩ (by norm_num))
theorem R92693 : Reach 92693 := rs (se 6 (by rfl) ⟨2172, by rfl⟩) (B 4345 (by norm_num) ⟨2172, by rfl⟩ (by norm_num))
theorem R92697 : Reach 92697 := rs (se 2 (by rfl) ⟨34761, by rfl⟩) (B 69523 (by norm_num) ⟨34761, by rfl⟩ (by norm_num))
theorem R92701 : Reach 92701 := rs (se 3 (by rfl) ⟨17381, by rfl⟩) (B 34763 (by norm_num) ⟨17381, by rfl⟩ (by norm_num))
theorem R92705 : Reach 92705 := rs (se 2 (by rfl) ⟨34764, by rfl⟩) (B 69529 (by norm_num) ⟨34764, by rfl⟩ (by norm_num))
theorem R92709 : Reach 92709 := rs (se 4 (by rfl) ⟨8691, by rfl⟩) (B 17383 (by norm_num) ⟨8691, by rfl⟩ (by norm_num))
theorem R92713 : Reach 92713 := rs (se 2 (by rfl) ⟨34767, by rfl⟩) (B 69535 (by norm_num) ⟨34767, by rfl⟩ (by norm_num))
theorem R92717 : Reach 92717 := rs (se 3 (by rfl) ⟨17384, by rfl⟩) (B 34769 (by norm_num) ⟨17384, by rfl⟩ (by norm_num))
theorem R92721 : Reach 92721 := rs (se 2 (by rfl) ⟨34770, by rfl⟩) (B 69541 (by norm_num) ⟨34770, by rfl⟩ (by norm_num))
theorem R92725 : Reach 92725 := rs (se 5 (by rfl) ⟨4346, by rfl⟩) (B 8693 (by norm_num) ⟨4346, by rfl⟩ (by norm_num))
theorem R92729 : Reach 92729 := rs (se 2 (by rfl) ⟨34773, by rfl⟩) (B 69547 (by norm_num) ⟨34773, by rfl⟩ (by norm_num))
theorem R92733 : Reach 92733 := rs (se 3 (by rfl) ⟨17387, by rfl⟩) (B 34775 (by norm_num) ⟨17387, by rfl⟩ (by norm_num))
theorem R92737 : Reach 92737 := rs (se 2 (by rfl) ⟨34776, by rfl⟩) (B 69553 (by norm_num) ⟨34776, by rfl⟩ (by norm_num))
theorem R92741 : Reach 92741 := rs (se 4 (by rfl) ⟨8694, by rfl⟩) (B 17389 (by norm_num) ⟨8694, by rfl⟩ (by norm_num))
theorem R191045 : Reach 191045 := rs (se 4 (by rfl) ⟨17910, by rfl⟩) (B 35821 (by norm_num) ⟨17910, by rfl⟩ (by norm_num))
theorem R92745 : Reach 92745 := rs (se 2 (by rfl) ⟨34779, by rfl⟩) (B 69559 (by norm_num) ⟨34779, by rfl⟩ (by norm_num))
theorem R92749 : Reach 92749 := rs (se 3 (by rfl) ⟨17390, by rfl⟩) (B 34781 (by norm_num) ⟨17390, by rfl⟩ (by norm_num))
theorem R92753 : Reach 92753 := rs (se 2 (by rfl) ⟨34782, by rfl⟩) (B 69565 (by norm_num) ⟨34782, by rfl⟩ (by norm_num))
theorem R92757 : Reach 92757 := rs (se 8 (by rfl) ⟨543, by rfl⟩) (B 1087 (by norm_num) ⟨543, by rfl⟩ (by norm_num))
theorem R453205 : Reach 453205 := rs (se 8 (by rfl) ⟨2655, by rfl⟩) (B 5311 (by norm_num) ⟨2655, by rfl⟩ (by norm_num))
theorem R354901 : Reach 354901 := rs (se 8 (by rfl) ⟨2079, by rfl⟩) (B 4159 (by norm_num) ⟨2079, by rfl⟩ (by norm_num))
theorem R92761 : Reach 92761 := rs (se 2 (by rfl) ⟨34785, by rfl⟩) (B 69571 (by norm_num) ⟨34785, by rfl⟩ (by norm_num))
theorem R92765 : Reach 92765 := rs (se 3 (by rfl) ⟨17393, by rfl⟩) (B 34787 (by norm_num) ⟨17393, by rfl⟩ (by norm_num))
theorem R92769 : Reach 92769 := rs (se 2 (by rfl) ⟨34788, by rfl⟩) (B 69577 (by norm_num) ⟨34788, by rfl⟩ (by norm_num))
theorem R92773 : Reach 92773 := rs (se 4 (by rfl) ⟨8697, by rfl⟩) (B 17395 (by norm_num) ⟨8697, by rfl⟩ (by norm_num))
theorem R92777 : Reach 92777 := rs (se 2 (by rfl) ⟨34791, by rfl⟩) (B 69583 (by norm_num) ⟨34791, by rfl⟩ (by norm_num))
theorem R92781 : Reach 92781 := rs (se 3 (by rfl) ⟨17396, by rfl⟩) (B 34793 (by norm_num) ⟨17396, by rfl⟩ (by norm_num))
theorem R92785 : Reach 92785 := rs (se 2 (by rfl) ⟨34794, by rfl⟩) (B 69589 (by norm_num) ⟨34794, by rfl⟩ (by norm_num))
theorem R92789 : Reach 92789 := rs (se 5 (by rfl) ⟨4349, by rfl⟩) (B 8699 (by norm_num) ⟨4349, by rfl⟩ (by norm_num))
theorem R92793 : Reach 92793 := rs (se 2 (by rfl) ⟨34797, by rfl⟩) (B 69595 (by norm_num) ⟨34797, by rfl⟩ (by norm_num))
theorem R92797 : Reach 92797 := rs (se 3 (by rfl) ⟨17399, by rfl⟩) (B 34799 (by norm_num) ⟨17399, by rfl⟩ (by norm_num))
theorem R92801 : Reach 92801 := rs (se 2 (by rfl) ⟨34800, by rfl⟩) (B 69601 (by norm_num) ⟨34800, by rfl⟩ (by norm_num))
theorem R158341 : Reach 158341 := rs (se 4 (by rfl) ⟨14844, by rfl⟩) (B 29689 (by norm_num) ⟨14844, by rfl⟩ (by norm_num))
theorem R92805 : Reach 92805 := rs (se 4 (by rfl) ⟨8700, by rfl⟩) (B 17401 (by norm_num) ⟨8700, by rfl⟩ (by norm_num))
theorem R92809 : Reach 92809 := rs (se 2 (by rfl) ⟨34803, by rfl⟩) (B 69607 (by norm_num) ⟨34803, by rfl⟩ (by norm_num))
theorem R92813 : Reach 92813 := rs (se 3 (by rfl) ⟨17402, by rfl⟩) (B 34805 (by norm_num) ⟨17402, by rfl⟩ (by norm_num))
theorem R92817 : Reach 92817 := rs (se 2 (by rfl) ⟨34806, by rfl⟩) (B 69613 (by norm_num) ⟨34806, by rfl⟩ (by norm_num))
theorem R92821 : Reach 92821 := rs (se 6 (by rfl) ⟨2175, by rfl⟩) (B 4351 (by norm_num) ⟨2175, by rfl⟩ (by norm_num))
theorem R92825 : Reach 92825 := rs (se 2 (by rfl) ⟨34809, by rfl⟩) (B 69619 (by norm_num) ⟨34809, by rfl⟩ (by norm_num))
theorem R92829 : Reach 92829 := rs (se 3 (by rfl) ⟨17405, by rfl⟩) (B 34811 (by norm_num) ⟨17405, by rfl⟩ (by norm_num))
theorem R92833 : Reach 92833 := rs (se 2 (by rfl) ⟨34812, by rfl⟩) (B 69625 (by norm_num) ⟨34812, by rfl⟩ (by norm_num))
theorem R92837 : Reach 92837 := rs (se 4 (by rfl) ⟨8703, by rfl⟩) (B 17407 (by norm_num) ⟨8703, by rfl⟩ (by norm_num))
theorem R92841 : Reach 92841 := rs (se 2 (by rfl) ⟨34815, by rfl⟩) (B 69631 (by norm_num) ⟨34815, by rfl⟩ (by norm_num))
theorem R92845 : Reach 92845 := rs (se 3 (by rfl) ⟨17408, by rfl⟩) (B 34817 (by norm_num) ⟨17408, by rfl⟩ (by norm_num))
theorem R92849 : Reach 92849 := rs (se 2 (by rfl) ⟨34818, by rfl⟩) (B 69637 (by norm_num) ⟨34818, by rfl⟩ (by norm_num))
theorem R92853 : Reach 92853 := rs (se 5 (by rfl) ⟨4352, by rfl⟩) (B 8705 (by norm_num) ⟨4352, by rfl⟩ (by norm_num))
theorem R92857 : Reach 92857 := rs (se 2 (by rfl) ⟨34821, by rfl⟩) (B 69643 (by norm_num) ⟨34821, by rfl⟩ (by norm_num))
theorem R92861 : Reach 92861 := rs (se 3 (by rfl) ⟨17411, by rfl⟩) (B 34823 (by norm_num) ⟨17411, by rfl⟩ (by norm_num))
theorem R92865 : Reach 92865 := rs (se 2 (by rfl) ⟨34824, by rfl⟩) (B 69649 (by norm_num) ⟨34824, by rfl⟩ (by norm_num))
theorem R92869 : Reach 92869 := rs (se 4 (by rfl) ⟨8706, by rfl⟩) (B 17413 (by norm_num) ⟨8706, by rfl⟩ (by norm_num))
theorem R92873 : Reach 92873 := rs (se 2 (by rfl) ⟨34827, by rfl⟩) (B 69655 (by norm_num) ⟨34827, by rfl⟩ (by norm_num))
theorem R92877 : Reach 92877 := rs (se 3 (by rfl) ⟨17414, by rfl⟩) (B 34829 (by norm_num) ⟨17414, by rfl⟩ (by norm_num))
theorem R92881 : Reach 92881 := rs (se 2 (by rfl) ⟨34830, by rfl⟩) (B 69661 (by norm_num) ⟨34830, by rfl⟩ (by norm_num))
theorem R92885 : Reach 92885 := rs (se 7 (by rfl) ⟨1088, by rfl⟩) (B 2177 (by norm_num) ⟨1088, by rfl⟩ (by norm_num))
theorem R92889 : Reach 92889 := rs (se 2 (by rfl) ⟨34833, by rfl⟩) (B 69667 (by norm_num) ⟨34833, by rfl⟩ (by norm_num))
theorem R92893 : Reach 92893 := rs (se 3 (by rfl) ⟨17417, by rfl⟩) (B 34835 (by norm_num) ⟨17417, by rfl⟩ (by norm_num))
theorem R158429 : Reach 158429 := rs (se 3 (by rfl) ⟨29705, by rfl⟩) (B 59411 (by norm_num) ⟨29705, by rfl⟩ (by norm_num))
theorem R92897 : Reach 92897 := rs (se 2 (by rfl) ⟨34836, by rfl⟩) (B 69673 (by norm_num) ⟨34836, by rfl⟩ (by norm_num))
theorem R92901 : Reach 92901 := rs (se 4 (by rfl) ⟨8709, by rfl⟩) (B 17419 (by norm_num) ⟨8709, by rfl⟩ (by norm_num))
theorem R92905 : Reach 92905 := rs (se 2 (by rfl) ⟨34839, by rfl⟩) (B 69679 (by norm_num) ⟨34839, by rfl⟩ (by norm_num))
theorem R92909 : Reach 92909 := rs (se 3 (by rfl) ⟨17420, by rfl⟩) (B 34841 (by norm_num) ⟨17420, by rfl⟩ (by norm_num))
theorem R92913 : Reach 92913 := rs (se 2 (by rfl) ⟨34842, by rfl⟩) (B 69685 (by norm_num) ⟨34842, by rfl⟩ (by norm_num))
theorem R92917 : Reach 92917 := rs (se 5 (by rfl) ⟨4355, by rfl⟩) (B 8711 (by norm_num) ⟨4355, by rfl⟩ (by norm_num))
theorem R92921 : Reach 92921 := rs (se 2 (by rfl) ⟨34845, by rfl⟩) (B 69691 (by norm_num) ⟨34845, by rfl⟩ (by norm_num))
theorem R92925 : Reach 92925 := rs (se 3 (by rfl) ⟨17423, by rfl⟩) (B 34847 (by norm_num) ⟨17423, by rfl⟩ (by norm_num))
theorem R92929 : Reach 92929 := rs (se 2 (by rfl) ⟨34848, by rfl⟩) (B 69697 (by norm_num) ⟨34848, by rfl⟩ (by norm_num))
theorem R92933 : Reach 92933 := rs (se 4 (by rfl) ⟨8712, by rfl⟩) (B 17425 (by norm_num) ⟨8712, by rfl⟩ (by norm_num))
theorem R92937 : Reach 92937 := rs (se 2 (by rfl) ⟨34851, by rfl⟩) (B 69703 (by norm_num) ⟨34851, by rfl⟩ (by norm_num))
theorem R92941 : Reach 92941 := rs (se 3 (by rfl) ⟨17426, by rfl⟩) (B 34853 (by norm_num) ⟨17426, by rfl⟩ (by norm_num))
theorem R92945 : Reach 92945 := rs (se 2 (by rfl) ⟨34854, by rfl⟩) (B 69709 (by norm_num) ⟨34854, by rfl⟩ (by norm_num))
theorem R92949 : Reach 92949 := rs (se 6 (by rfl) ⟨2178, by rfl⟩) (B 4357 (by norm_num) ⟨2178, by rfl⟩ (by norm_num))
theorem R92953 : Reach 92953 := rs (se 2 (by rfl) ⟨34857, by rfl⟩) (B 69715 (by norm_num) ⟨34857, by rfl⟩ (by norm_num))
theorem R92957 : Reach 92957 := rs (se 3 (by rfl) ⟨17429, by rfl⟩) (B 34859 (by norm_num) ⟨17429, by rfl⟩ (by norm_num))
theorem R92961 : Reach 92961 := rs (se 2 (by rfl) ⟨34860, by rfl⟩) (B 69721 (by norm_num) ⟨34860, by rfl⟩ (by norm_num))
theorem R92965 : Reach 92965 := rs (se 4 (by rfl) ⟨8715, by rfl⟩) (B 17431 (by norm_num) ⟨8715, by rfl⟩ (by norm_num))
theorem R92969 : Reach 92969 := rs (se 2 (by rfl) ⟨34863, by rfl⟩) (B 69727 (by norm_num) ⟨34863, by rfl⟩ (by norm_num))
theorem R92973 : Reach 92973 := rs (se 3 (by rfl) ⟨17432, by rfl⟩) (B 34865 (by norm_num) ⟨17432, by rfl⟩ (by norm_num))
theorem R92977 : Reach 92977 := rs (se 2 (by rfl) ⟨34866, by rfl⟩) (B 69733 (by norm_num) ⟨34866, by rfl⟩ (by norm_num))
theorem R92981 : Reach 92981 := rs (se 5 (by rfl) ⟨4358, by rfl⟩) (B 8717 (by norm_num) ⟨4358, by rfl⟩ (by norm_num))
theorem R92985 : Reach 92985 := rs (se 2 (by rfl) ⟨34869, by rfl⟩) (B 69739 (by norm_num) ⟨34869, by rfl⟩ (by norm_num))
theorem R92989 : Reach 92989 := rs (se 3 (by rfl) ⟨17435, by rfl⟩) (B 34871 (by norm_num) ⟨17435, by rfl⟩ (by norm_num))
theorem R92993 : Reach 92993 := rs (se 2 (by rfl) ⟨34872, by rfl⟩) (B 69745 (by norm_num) ⟨34872, by rfl⟩ (by norm_num))
theorem R92997 : Reach 92997 := rs (se 4 (by rfl) ⟨8718, by rfl⟩) (B 17437 (by norm_num) ⟨8718, by rfl⟩ (by norm_num))
theorem R93001 : Reach 93001 := rs (se 2 (by rfl) ⟨34875, by rfl⟩) (B 69751 (by norm_num) ⟨34875, by rfl⟩ (by norm_num))
theorem R93005 : Reach 93005 := rs (se 3 (by rfl) ⟨17438, by rfl⟩) (B 34877 (by norm_num) ⟨17438, by rfl⟩ (by norm_num))
theorem R93009 : Reach 93009 := rs (se 2 (by rfl) ⟨34878, by rfl⟩) (B 69757 (by norm_num) ⟨34878, by rfl⟩ (by norm_num))
theorem R93013 : Reach 93013 := rs (se 9 (by rfl) ⟨272, by rfl⟩) (B 545 (by norm_num) ⟨272, by rfl⟩ (by norm_num))
theorem R93017 : Reach 93017 := rs (se 2 (by rfl) ⟨34881, by rfl⟩) (B 69763 (by norm_num) ⟨34881, by rfl⟩ (by norm_num))
theorem R93021 : Reach 93021 := rs (se 3 (by rfl) ⟨17441, by rfl⟩) (B 34883 (by norm_num) ⟨17441, by rfl⟩ (by norm_num))
theorem R158557 : Reach 158557 := rs (se 3 (by rfl) ⟨29729, by rfl⟩) (B 59459 (by norm_num) ⟨29729, by rfl⟩ (by norm_num))
theorem R93025 : Reach 93025 := rs (se 2 (by rfl) ⟨34884, by rfl⟩) (B 69769 (by norm_num) ⟨34884, by rfl⟩ (by norm_num))
theorem R93029 : Reach 93029 := rs (se 4 (by rfl) ⟨8721, by rfl⟩) (B 17443 (by norm_num) ⟨8721, by rfl⟩ (by norm_num))
theorem R93033 : Reach 93033 := rs (se 2 (by rfl) ⟨34887, by rfl⟩) (B 69775 (by norm_num) ⟨34887, by rfl⟩ (by norm_num))
theorem R93037 : Reach 93037 := rs (se 3 (by rfl) ⟨17444, by rfl⟩) (B 34889 (by norm_num) ⟨17444, by rfl⟩ (by norm_num))
theorem R93041 : Reach 93041 := rs (se 2 (by rfl) ⟨34890, by rfl⟩) (B 69781 (by norm_num) ⟨34890, by rfl⟩ (by norm_num))
theorem R93045 : Reach 93045 := rs (se 5 (by rfl) ⟨4361, by rfl⟩) (B 8723 (by norm_num) ⟨4361, by rfl⟩ (by norm_num))
theorem R224117 : Reach 224117 := rs (se 5 (by rfl) ⟨10505, by rfl⟩) (B 21011 (by norm_num) ⟨10505, by rfl⟩ (by norm_num))
theorem R93049 : Reach 93049 := rs (se 2 (by rfl) ⟨34893, by rfl⟩) (B 69787 (by norm_num) ⟨34893, by rfl⟩ (by norm_num))
theorem R93053 : Reach 93053 := rs (se 3 (by rfl) ⟨17447, by rfl⟩) (B 34895 (by norm_num) ⟨17447, by rfl⟩ (by norm_num))
theorem R93057 : Reach 93057 := rs (se 2 (by rfl) ⟨34896, by rfl⟩) (B 69793 (by norm_num) ⟨34896, by rfl⟩ (by norm_num))
theorem R93061 : Reach 93061 := rs (se 4 (by rfl) ⟨8724, by rfl⟩) (B 17449 (by norm_num) ⟨8724, by rfl⟩ (by norm_num))
theorem R355205 : Reach 355205 := rs (se 4 (by rfl) ⟨33300, by rfl⟩) (B 66601 (by norm_num) ⟨33300, by rfl⟩ (by norm_num))
theorem R93065 : Reach 93065 := rs (se 2 (by rfl) ⟨34899, by rfl⟩) (B 69799 (by norm_num) ⟨34899, by rfl⟩ (by norm_num))
theorem R93069 : Reach 93069 := rs (se 3 (by rfl) ⟨17450, by rfl⟩) (B 34901 (by norm_num) ⟨17450, by rfl⟩ (by norm_num))
theorem R93073 : Reach 93073 := rs (se 2 (by rfl) ⟨34902, by rfl⟩) (B 69805 (by norm_num) ⟨34902, by rfl⟩ (by norm_num))
theorem R584597 : Reach 584597 := rs (se 6 (by rfl) ⟨13701, by rfl⟩) (B 27403 (by norm_num) ⟨13701, by rfl⟩ (by norm_num))
theorem R93077 : Reach 93077 := rs (se 6 (by rfl) ⟨2181, by rfl⟩) (B 4363 (by norm_num) ⟨2181, by rfl⟩ (by norm_num))
theorem R93081 : Reach 93081 := rs (se 2 (by rfl) ⟨34905, by rfl⟩) (B 69811 (by norm_num) ⟨34905, by rfl⟩ (by norm_num))
theorem R93085 : Reach 93085 := rs (se 3 (by rfl) ⟨17453, by rfl⟩) (B 34907 (by norm_num) ⟨17453, by rfl⟩ (by norm_num))
theorem R93089 : Reach 93089 := rs (se 2 (by rfl) ⟨34908, by rfl⟩) (B 69817 (by norm_num) ⟨34908, by rfl⟩ (by norm_num))
theorem R93093 : Reach 93093 := rs (se 4 (by rfl) ⟨8727, by rfl⟩) (B 17455 (by norm_num) ⟨8727, by rfl⟩ (by norm_num))
theorem R93097 : Reach 93097 := rs (se 2 (by rfl) ⟨34911, by rfl⟩) (B 69823 (by norm_num) ⟨34911, by rfl⟩ (by norm_num))
theorem R93101 : Reach 93101 := rs (se 3 (by rfl) ⟨17456, by rfl⟩) (B 34913 (by norm_num) ⟨17456, by rfl⟩ (by norm_num))
theorem R93105 : Reach 93105 := rs (se 2 (by rfl) ⟨34914, by rfl⟩) (B 69829 (by norm_num) ⟨34914, by rfl⟩ (by norm_num))
theorem R93109 : Reach 93109 := rs (se 5 (by rfl) ⟨4364, by rfl⟩) (B 8729 (by norm_num) ⟨4364, by rfl⟩ (by norm_num))
theorem R158645 : Reach 158645 := rs (se 5 (by rfl) ⟨7436, by rfl⟩) (B 14873 (by norm_num) ⟨7436, by rfl⟩ (by norm_num))
theorem R93113 : Reach 93113 := rs (se 2 (by rfl) ⟨34917, by rfl⟩) (B 69835 (by norm_num) ⟨34917, by rfl⟩ (by norm_num))
theorem R93117 : Reach 93117 := rs (se 3 (by rfl) ⟨17459, by rfl⟩) (B 34919 (by norm_num) ⟨17459, by rfl⟩ (by norm_num))
theorem R93121 : Reach 93121 := rs (se 2 (by rfl) ⟨34920, by rfl⟩) (B 69841 (by norm_num) ⟨34920, by rfl⟩ (by norm_num))
theorem R93125 : Reach 93125 := rs (se 4 (by rfl) ⟨8730, by rfl⟩) (B 17461 (by norm_num) ⟨8730, by rfl⟩ (by norm_num))
theorem R93129 : Reach 93129 := rs (se 2 (by rfl) ⟨34923, by rfl⟩) (B 69847 (by norm_num) ⟨34923, by rfl⟩ (by norm_num))
theorem R93133 : Reach 93133 := rs (se 3 (by rfl) ⟨17462, by rfl⟩) (B 34925 (by norm_num) ⟨17462, by rfl⟩ (by norm_num))
theorem R93137 : Reach 93137 := rs (se 2 (by rfl) ⟨34926, by rfl⟩) (B 69853 (by norm_num) ⟨34926, by rfl⟩ (by norm_num))
theorem R93141 : Reach 93141 := rs (se 7 (by rfl) ⟨1091, by rfl⟩) (B 2183 (by norm_num) ⟨1091, by rfl⟩ (by norm_num))
theorem R93145 : Reach 93145 := rs (se 2 (by rfl) ⟨34929, by rfl⟩) (B 69859 (by norm_num) ⟨34929, by rfl⟩ (by norm_num))
theorem R93149 : Reach 93149 := rs (se 3 (by rfl) ⟨17465, by rfl⟩) (B 34931 (by norm_num) ⟨17465, by rfl⟩ (by norm_num))
theorem R93153 : Reach 93153 := rs (se 2 (by rfl) ⟨34932, by rfl⟩) (B 69865 (by norm_num) ⟨34932, by rfl⟩ (by norm_num))
theorem R93157 : Reach 93157 := rs (se 4 (by rfl) ⟨8733, by rfl⟩) (B 17467 (by norm_num) ⟨8733, by rfl⟩ (by norm_num))
theorem R93161 : Reach 93161 := rs (se 2 (by rfl) ⟨34935, by rfl⟩) (B 69871 (by norm_num) ⟨34935, by rfl⟩ (by norm_num))
theorem R93165 : Reach 93165 := rs (se 3 (by rfl) ⟨17468, by rfl⟩) (B 34937 (by norm_num) ⟨17468, by rfl⟩ (by norm_num))
theorem R93169 : Reach 93169 := rs (se 2 (by rfl) ⟨34938, by rfl⟩) (B 69877 (by norm_num) ⟨34938, by rfl⟩ (by norm_num))
theorem R93173 : Reach 93173 := rs (se 5 (by rfl) ⟨4367, by rfl⟩) (B 8735 (by norm_num) ⟨4367, by rfl⟩ (by norm_num))
theorem R93177 : Reach 93177 := rs (se 2 (by rfl) ⟨34941, by rfl⟩) (B 69883 (by norm_num) ⟨34941, by rfl⟩ (by norm_num))
theorem R93181 : Reach 93181 := rs (se 3 (by rfl) ⟨17471, by rfl⟩) (B 34943 (by norm_num) ⟨17471, by rfl⟩ (by norm_num))
theorem R93185 : Reach 93185 := rs (se 2 (by rfl) ⟨34944, by rfl⟩) (B 69889 (by norm_num) ⟨34944, by rfl⟩ (by norm_num))
theorem R93189 : Reach 93189 := rs (se 4 (by rfl) ⟨8736, by rfl⟩) (B 17473 (by norm_num) ⟨8736, by rfl⟩ (by norm_num))
theorem R93193 : Reach 93193 := rs (se 2 (by rfl) ⟨34947, by rfl⟩) (B 69895 (by norm_num) ⟨34947, by rfl⟩ (by norm_num))
theorem R93197 : Reach 93197 := rs (se 3 (by rfl) ⟨17474, by rfl⟩) (B 34949 (by norm_num) ⟨17474, by rfl⟩ (by norm_num))
theorem R93201 : Reach 93201 := rs (se 2 (by rfl) ⟨34950, by rfl⟩) (B 69901 (by norm_num) ⟨34950, by rfl⟩ (by norm_num))
theorem R93205 : Reach 93205 := rs (se 6 (by rfl) ⟨2184, by rfl⟩) (B 4369 (by norm_num) ⟨2184, by rfl⟩ (by norm_num))
theorem R93209 : Reach 93209 := rs (se 2 (by rfl) ⟨34953, by rfl⟩) (B 69907 (by norm_num) ⟨34953, by rfl⟩ (by norm_num))
theorem R93213 : Reach 93213 := rs (se 3 (by rfl) ⟨17477, by rfl⟩) (B 34955 (by norm_num) ⟨17477, by rfl⟩ (by norm_num))
theorem R93217 : Reach 93217 := rs (se 2 (by rfl) ⟨34956, by rfl⟩) (B 69913 (by norm_num) ⟨34956, by rfl⟩ (by norm_num))
theorem R93221 : Reach 93221 := rs (se 4 (by rfl) ⟨8739, by rfl⟩) (B 17479 (by norm_num) ⟨8739, by rfl⟩ (by norm_num))
theorem R93225 : Reach 93225 := rs (se 2 (by rfl) ⟨34959, by rfl⟩) (B 69919 (by norm_num) ⟨34959, by rfl⟩ (by norm_num))
theorem R93229 : Reach 93229 := rs (se 3 (by rfl) ⟨17480, by rfl⟩) (B 34961 (by norm_num) ⟨17480, by rfl⟩ (by norm_num))
theorem R93233 : Reach 93233 := rs (se 2 (by rfl) ⟨34962, by rfl⟩) (B 69925 (by norm_num) ⟨34962, by rfl⟩ (by norm_num))
theorem R93237 : Reach 93237 := rs (se 5 (by rfl) ⟨4370, by rfl⟩) (B 8741 (by norm_num) ⟨4370, by rfl⟩ (by norm_num))
theorem R158773 : Reach 158773 := rs (se 5 (by rfl) ⟨7442, by rfl⟩) (B 14885 (by norm_num) ⟨7442, by rfl⟩ (by norm_num))
theorem R93241 : Reach 93241 := rs (se 2 (by rfl) ⟨34965, by rfl⟩) (B 69931 (by norm_num) ⟨34965, by rfl⟩ (by norm_num))
theorem R93245 : Reach 93245 := rs (se 3 (by rfl) ⟨17483, by rfl⟩) (B 34967 (by norm_num) ⟨17483, by rfl⟩ (by norm_num))
theorem R93249 : Reach 93249 := rs (se 2 (by rfl) ⟨34968, by rfl⟩) (B 69937 (by norm_num) ⟨34968, by rfl⟩ (by norm_num))
theorem R93253 : Reach 93253 := rs (se 4 (by rfl) ⟨8742, by rfl⟩) (B 17485 (by norm_num) ⟨8742, by rfl⟩ (by norm_num))
theorem R93257 : Reach 93257 := rs (se 2 (by rfl) ⟨34971, by rfl⟩) (B 69943 (by norm_num) ⟨34971, by rfl⟩ (by norm_num))
theorem R93261 : Reach 93261 := rs (se 3 (by rfl) ⟨17486, by rfl⟩) (B 34973 (by norm_num) ⟨17486, by rfl⟩ (by norm_num))
theorem R93265 : Reach 93265 := rs (se 2 (by rfl) ⟨34974, by rfl⟩) (B 69949 (by norm_num) ⟨34974, by rfl⟩ (by norm_num))
theorem R93269 : Reach 93269 := rs (se 8 (by rfl) ⟨546, by rfl⟩) (B 1093 (by norm_num) ⟨546, by rfl⟩ (by norm_num))
theorem R93273 : Reach 93273 := rs (se 2 (by rfl) ⟨34977, by rfl⟩) (B 69955 (by norm_num) ⟨34977, by rfl⟩ (by norm_num))
theorem R93277 : Reach 93277 := rs (se 3 (by rfl) ⟨17489, by rfl⟩) (B 34979 (by norm_num) ⟨17489, by rfl⟩ (by norm_num))
theorem R93281 : Reach 93281 := rs (se 2 (by rfl) ⟨34980, by rfl⟩) (B 69961 (by norm_num) ⟨34980, by rfl⟩ (by norm_num))
theorem R93285 : Reach 93285 := rs (se 4 (by rfl) ⟨8745, by rfl⟩) (B 17491 (by norm_num) ⟨8745, by rfl⟩ (by norm_num))
theorem R93289 : Reach 93289 := rs (se 2 (by rfl) ⟨34983, by rfl⟩) (B 69967 (by norm_num) ⟨34983, by rfl⟩ (by norm_num))
theorem R93293 : Reach 93293 := rs (se 3 (by rfl) ⟨17492, by rfl⟩) (B 34985 (by norm_num) ⟨17492, by rfl⟩ (by norm_num))
theorem R93297 : Reach 93297 := rs (se 2 (by rfl) ⟨34986, by rfl⟩) (B 69973 (by norm_num) ⟨34986, by rfl⟩ (by norm_num))
theorem R93301 : Reach 93301 := rs (se 5 (by rfl) ⟨4373, by rfl⟩) (B 8747 (by norm_num) ⟨4373, by rfl⟩ (by norm_num))
theorem R93305 : Reach 93305 := rs (se 2 (by rfl) ⟨34989, by rfl⟩) (B 69979 (by norm_num) ⟨34989, by rfl⟩ (by norm_num))
theorem R93309 : Reach 93309 := rs (se 3 (by rfl) ⟨17495, by rfl⟩) (B 34991 (by norm_num) ⟨17495, by rfl⟩ (by norm_num))
theorem R93313 : Reach 93313 := rs (se 2 (by rfl) ⟨34992, by rfl⟩) (B 69985 (by norm_num) ⟨34992, by rfl⟩ (by norm_num))
theorem R93317 : Reach 93317 := rs (se 4 (by rfl) ⟨8748, by rfl⟩) (B 17497 (by norm_num) ⟨8748, by rfl⟩ (by norm_num))
theorem R93321 : Reach 93321 := rs (se 2 (by rfl) ⟨34995, by rfl⟩) (B 69991 (by norm_num) ⟨34995, by rfl⟩ (by norm_num))
theorem R93325 : Reach 93325 := rs (se 3 (by rfl) ⟨17498, by rfl⟩) (B 34997 (by norm_num) ⟨17498, by rfl⟩ (by norm_num))
theorem R158861 : Reach 158861 := rs (se 3 (by rfl) ⟨29786, by rfl⟩) (B 59573 (by norm_num) ⟨29786, by rfl⟩ (by norm_num))
theorem R93329 : Reach 93329 := rs (se 2 (by rfl) ⟨34998, by rfl⟩) (B 69997 (by norm_num) ⟨34998, by rfl⟩ (by norm_num))
theorem R93333 : Reach 93333 := rs (se 6 (by rfl) ⟨2187, by rfl⟩) (B 4375 (by norm_num) ⟨2187, by rfl⟩ (by norm_num))
theorem R93337 : Reach 93337 := rs (se 2 (by rfl) ⟨35001, by rfl⟩) (B 70003 (by norm_num) ⟨35001, by rfl⟩ (by norm_num))
theorem R93341 : Reach 93341 := rs (se 3 (by rfl) ⟨17501, by rfl⟩) (B 35003 (by norm_num) ⟨17501, by rfl⟩ (by norm_num))
theorem R93345 : Reach 93345 := rs (se 2 (by rfl) ⟨35004, by rfl⟩) (B 70009 (by norm_num) ⟨35004, by rfl⟩ (by norm_num))
theorem R93349 : Reach 93349 := rs (se 4 (by rfl) ⟨8751, by rfl⟩) (B 17503 (by norm_num) ⟨8751, by rfl⟩ (by norm_num))
theorem R93353 : Reach 93353 := rs (se 2 (by rfl) ⟨35007, by rfl⟩) (B 70015 (by norm_num) ⟨35007, by rfl⟩ (by norm_num))
theorem R93357 : Reach 93357 := rs (se 3 (by rfl) ⟨17504, by rfl⟩) (B 35009 (by norm_num) ⟨17504, by rfl⟩ (by norm_num))
theorem R93361 : Reach 93361 := rs (se 2 (by rfl) ⟨35010, by rfl⟩) (B 70021 (by norm_num) ⟨35010, by rfl⟩ (by norm_num))
theorem R93365 : Reach 93365 := rs (se 5 (by rfl) ⟨4376, by rfl⟩) (B 8753 (by norm_num) ⟨4376, by rfl⟩ (by norm_num))
theorem R93369 : Reach 93369 := rs (se 2 (by rfl) ⟨35013, by rfl⟩) (B 70027 (by norm_num) ⟨35013, by rfl⟩ (by norm_num))
theorem R93373 : Reach 93373 := rs (se 3 (by rfl) ⟨17507, by rfl⟩) (B 35015 (by norm_num) ⟨17507, by rfl⟩ (by norm_num))
theorem R93377 : Reach 93377 := rs (se 2 (by rfl) ⟨35016, by rfl⟩) (B 70033 (by norm_num) ⟨35016, by rfl⟩ (by norm_num))
theorem R93381 : Reach 93381 := rs (se 4 (by rfl) ⟨8754, by rfl⟩) (B 17509 (by norm_num) ⟨8754, by rfl⟩ (by norm_num))
theorem R224453 : Reach 224453 := rs (se 4 (by rfl) ⟨21042, by rfl⟩) (B 42085 (by norm_num) ⟨21042, by rfl⟩ (by norm_num))
theorem R93385 : Reach 93385 := rs (se 2 (by rfl) ⟨35019, by rfl⟩) (B 70039 (by norm_num) ⟨35019, by rfl⟩ (by norm_num))
theorem R93389 : Reach 93389 := rs (se 3 (by rfl) ⟨17510, by rfl⟩) (B 35021 (by norm_num) ⟨17510, by rfl⟩ (by norm_num))
theorem R93393 : Reach 93393 := rs (se 2 (by rfl) ⟨35022, by rfl⟩) (B 70045 (by norm_num) ⟨35022, by rfl⟩ (by norm_num))
theorem R93397 : Reach 93397 := rs (se 7 (by rfl) ⟨1094, by rfl⟩) (B 2189 (by norm_num) ⟨1094, by rfl⟩ (by norm_num))
theorem R93401 : Reach 93401 := rs (se 2 (by rfl) ⟨35025, by rfl⟩) (B 70051 (by norm_num) ⟨35025, by rfl⟩ (by norm_num))
theorem R93405 : Reach 93405 := rs (se 3 (by rfl) ⟨17513, by rfl⟩) (B 35027 (by norm_num) ⟨17513, by rfl⟩ (by norm_num))
theorem R93409 : Reach 93409 := rs (se 2 (by rfl) ⟨35028, by rfl⟩) (B 70057 (by norm_num) ⟨35028, by rfl⟩ (by norm_num))
theorem R93413 : Reach 93413 := rs (se 4 (by rfl) ⟨8757, by rfl⟩) (B 17515 (by norm_num) ⟨8757, by rfl⟩ (by norm_num))
theorem R93417 : Reach 93417 := rs (se 2 (by rfl) ⟨35031, by rfl⟩) (B 70063 (by norm_num) ⟨35031, by rfl⟩ (by norm_num))
theorem R93421 : Reach 93421 := rs (se 3 (by rfl) ⟨17516, by rfl⟩) (B 35033 (by norm_num) ⟨17516, by rfl⟩ (by norm_num))
theorem R93425 : Reach 93425 := rs (se 2 (by rfl) ⟨35034, by rfl⟩) (B 70069 (by norm_num) ⟨35034, by rfl⟩ (by norm_num))
theorem R93429 : Reach 93429 := rs (se 5 (by rfl) ⟨4379, by rfl⟩) (B 8759 (by norm_num) ⟨4379, by rfl⟩ (by norm_num))
theorem R93433 : Reach 93433 := rs (se 2 (by rfl) ⟨35037, by rfl⟩) (B 70075 (by norm_num) ⟨35037, by rfl⟩ (by norm_num))
theorem R93437 : Reach 93437 := rs (se 3 (by rfl) ⟨17519, by rfl⟩) (B 35039 (by norm_num) ⟨17519, by rfl⟩ (by norm_num))
theorem R93441 : Reach 93441 := rs (se 2 (by rfl) ⟨35040, by rfl⟩) (B 70081 (by norm_num) ⟨35040, by rfl⟩ (by norm_num))
theorem R93445 : Reach 93445 := rs (se 4 (by rfl) ⟨8760, by rfl⟩) (B 17521 (by norm_num) ⟨8760, by rfl⟩ (by norm_num))
theorem R93449 : Reach 93449 := rs (se 2 (by rfl) ⟨35043, by rfl⟩) (B 70087 (by norm_num) ⟨35043, by rfl⟩ (by norm_num))
theorem R93453 : Reach 93453 := rs (se 3 (by rfl) ⟨17522, by rfl⟩) (B 35045 (by norm_num) ⟨17522, by rfl⟩ (by norm_num))
theorem R158989 : Reach 158989 := rs (se 3 (by rfl) ⟨29810, by rfl⟩) (B 59621 (by norm_num) ⟨29810, by rfl⟩ (by norm_num))
theorem R93457 : Reach 93457 := rs (se 2 (by rfl) ⟨35046, by rfl⟩) (B 70093 (by norm_num) ⟨35046, by rfl⟩ (by norm_num))
theorem R879893 : Reach 879893 := rs (se 6 (by rfl) ⟨20622, by rfl⟩) (B 41245 (by norm_num) ⟨20622, by rfl⟩ (by norm_num))
theorem R93461 : Reach 93461 := rs (se 6 (by rfl) ⟨2190, by rfl⟩) (B 4381 (by norm_num) ⟨2190, by rfl⟩ (by norm_num))
theorem R93465 : Reach 93465 := rs (se 2 (by rfl) ⟨35049, by rfl⟩) (B 70099 (by norm_num) ⟨35049, by rfl⟩ (by norm_num))
theorem R93469 : Reach 93469 := rs (se 3 (by rfl) ⟨17525, by rfl⟩) (B 35051 (by norm_num) ⟨17525, by rfl⟩ (by norm_num))
theorem R93473 : Reach 93473 := rs (se 2 (by rfl) ⟨35052, by rfl⟩) (B 70105 (by norm_num) ⟨35052, by rfl⟩ (by norm_num))
theorem R93477 : Reach 93477 := rs (se 4 (by rfl) ⟨8763, by rfl⟩) (B 17527 (by norm_num) ⟨8763, by rfl⟩ (by norm_num))
theorem R93481 : Reach 93481 := rs (se 2 (by rfl) ⟨35055, by rfl⟩) (B 70111 (by norm_num) ⟨35055, by rfl⟩ (by norm_num))
theorem R93485 : Reach 93485 := rs (se 3 (by rfl) ⟨17528, by rfl⟩) (B 35057 (by norm_num) ⟨17528, by rfl⟩ (by norm_num))
theorem R93489 : Reach 93489 := rs (se 2 (by rfl) ⟨35058, by rfl⟩) (B 70117 (by norm_num) ⟨35058, by rfl⟩ (by norm_num))
theorem R93493 : Reach 93493 := rs (se 5 (by rfl) ⟨4382, by rfl⟩) (B 8765 (by norm_num) ⟨4382, by rfl⟩ (by norm_num))
theorem R650549 : Reach 650549 := rs (se 5 (by rfl) ⟨30494, by rfl⟩) (B 60989 (by norm_num) ⟨30494, by rfl⟩ (by norm_num))
theorem R93497 : Reach 93497 := rs (se 2 (by rfl) ⟨35061, by rfl⟩) (B 70123 (by norm_num) ⟨35061, by rfl⟩ (by norm_num))
theorem R93501 : Reach 93501 := rs (se 3 (by rfl) ⟨17531, by rfl⟩) (B 35063 (by norm_num) ⟨17531, by rfl⟩ (by norm_num))
theorem R93505 : Reach 93505 := rs (se 2 (by rfl) ⟨35064, by rfl⟩) (B 70129 (by norm_num) ⟨35064, by rfl⟩ (by norm_num))
theorem R93509 : Reach 93509 := rs (se 4 (by rfl) ⟨8766, by rfl⟩) (B 17533 (by norm_num) ⟨8766, by rfl⟩ (by norm_num))
theorem R93513 : Reach 93513 := rs (se 2 (by rfl) ⟨35067, by rfl⟩) (B 70135 (by norm_num) ⟨35067, by rfl⟩ (by norm_num))
theorem R93517 : Reach 93517 := rs (se 3 (by rfl) ⟨17534, by rfl⟩) (B 35069 (by norm_num) ⟨17534, by rfl⟩ (by norm_num))
theorem R93521 : Reach 93521 := rs (se 2 (by rfl) ⟨35070, by rfl⟩) (B 70141 (by norm_num) ⟨35070, by rfl⟩ (by norm_num))
theorem R93525 : Reach 93525 := rs (se 11 (by rfl) ⟨68, by rfl⟩) (B 137 (by norm_num) ⟨68, by rfl⟩ (by norm_num))
theorem R93529 : Reach 93529 := rs (se 2 (by rfl) ⟨35073, by rfl⟩) (B 70147 (by norm_num) ⟨35073, by rfl⟩ (by norm_num))
theorem R93533 : Reach 93533 := rs (se 3 (by rfl) ⟨17537, by rfl⟩) (B 35075 (by norm_num) ⟨17537, by rfl⟩ (by norm_num))
theorem R93537 : Reach 93537 := rs (se 2 (by rfl) ⟨35076, by rfl⟩) (B 70153 (by norm_num) ⟨35076, by rfl⟩ (by norm_num))
theorem R93541 : Reach 93541 := rs (se 4 (by rfl) ⟨8769, by rfl⟩) (B 17539 (by norm_num) ⟨8769, by rfl⟩ (by norm_num))
theorem R159077 : Reach 159077 := rs (se 4 (by rfl) ⟨14913, by rfl⟩) (B 29827 (by norm_num) ⟨14913, by rfl⟩ (by norm_num))
theorem R93545 : Reach 93545 := rs (se 2 (by rfl) ⟨35079, by rfl⟩) (B 70159 (by norm_num) ⟨35079, by rfl⟩ (by norm_num))
theorem R93549 : Reach 93549 := rs (se 3 (by rfl) ⟨17540, by rfl⟩) (B 35081 (by norm_num) ⟨17540, by rfl⟩ (by norm_num))
theorem R93553 : Reach 93553 := rs (se 2 (by rfl) ⟨35082, by rfl⟩) (B 70165 (by norm_num) ⟨35082, by rfl⟩ (by norm_num))
theorem R126325 : Reach 126325 := rs (se 5 (by rfl) ⟨5921, by rfl⟩) (B 11843 (by norm_num) ⟨5921, by rfl⟩ (by norm_num))
theorem R93557 : Reach 93557 := rs (se 5 (by rfl) ⟨4385, by rfl⟩) (B 8771 (by norm_num) ⟨4385, by rfl⟩ (by norm_num))
theorem R93561 : Reach 93561 := rs (se 2 (by rfl) ⟨35085, by rfl⟩) (B 70171 (by norm_num) ⟨35085, by rfl⟩ (by norm_num))
theorem R93565 : Reach 93565 := rs (se 3 (by rfl) ⟨17543, by rfl⟩) (B 35087 (by norm_num) ⟨17543, by rfl⟩ (by norm_num))
theorem R93569 : Reach 93569 := rs (se 2 (by rfl) ⟨35088, by rfl⟩) (B 70177 (by norm_num) ⟨35088, by rfl⟩ (by norm_num))
theorem R93573 : Reach 93573 := rs (se 4 (by rfl) ⟨8772, by rfl⟩) (B 17545 (by norm_num) ⟨8772, by rfl⟩ (by norm_num))
theorem R93577 : Reach 93577 := rs (se 2 (by rfl) ⟨35091, by rfl⟩) (B 70183 (by norm_num) ⟨35091, by rfl⟩ (by norm_num))
theorem R93581 : Reach 93581 := rs (se 3 (by rfl) ⟨17546, by rfl⟩) (B 35093 (by norm_num) ⟨17546, by rfl⟩ (by norm_num))
theorem R93585 : Reach 93585 := rs (se 2 (by rfl) ⟨35094, by rfl⟩) (B 70189 (by norm_num) ⟨35094, by rfl⟩ (by norm_num))
theorem R93589 : Reach 93589 := rs (se 6 (by rfl) ⟨2193, by rfl⟩) (B 4387 (by norm_num) ⟨2193, by rfl⟩ (by norm_num))
theorem R93593 : Reach 93593 := rs (se 2 (by rfl) ⟨35097, by rfl⟩) (B 70195 (by norm_num) ⟨35097, by rfl⟩ (by norm_num))
theorem R93597 : Reach 93597 := rs (se 3 (by rfl) ⟨17549, by rfl⟩) (B 35099 (by norm_num) ⟨17549, by rfl⟩ (by norm_num))
theorem R93601 : Reach 93601 := rs (se 2 (by rfl) ⟨35100, by rfl⟩) (B 70201 (by norm_num) ⟨35100, by rfl⟩ (by norm_num))
theorem R93605 : Reach 93605 := rs (se 4 (by rfl) ⟨8775, by rfl⟩) (B 17551 (by norm_num) ⟨8775, by rfl⟩ (by norm_num))
theorem R93609 : Reach 93609 := rs (se 2 (by rfl) ⟨35103, by rfl⟩) (B 70207 (by norm_num) ⟨35103, by rfl⟩ (by norm_num))
theorem R93613 : Reach 93613 := rs (se 3 (by rfl) ⟨17552, by rfl⟩) (B 35105 (by norm_num) ⟨17552, by rfl⟩ (by norm_num))
theorem R93617 : Reach 93617 := rs (se 2 (by rfl) ⟨35106, by rfl⟩) (B 70213 (by norm_num) ⟨35106, by rfl⟩ (by norm_num))
theorem R93621 : Reach 93621 := rs (se 5 (by rfl) ⟨4388, by rfl⟩) (B 8777 (by norm_num) ⟨4388, by rfl⟩ (by norm_num))
theorem R93625 : Reach 93625 := rs (se 2 (by rfl) ⟨35109, by rfl⟩) (B 70219 (by norm_num) ⟨35109, by rfl⟩ (by norm_num))
theorem R93629 : Reach 93629 := rs (se 3 (by rfl) ⟨17555, by rfl⟩) (B 35111 (by norm_num) ⟨17555, by rfl⟩ (by norm_num))
theorem R93633 : Reach 93633 := rs (se 2 (by rfl) ⟨35112, by rfl⟩) (B 70225 (by norm_num) ⟨35112, by rfl⟩ (by norm_num))
theorem R93637 : Reach 93637 := rs (se 4 (by rfl) ⟨8778, by rfl⟩) (B 17557 (by norm_num) ⟨8778, by rfl⟩ (by norm_num))
theorem R93641 : Reach 93641 := rs (se 2 (by rfl) ⟨35115, by rfl⟩) (B 70231 (by norm_num) ⟨35115, by rfl⟩ (by norm_num))
theorem R93645 : Reach 93645 := rs (se 3 (by rfl) ⟨17558, by rfl⟩) (B 35117 (by norm_num) ⟨17558, by rfl⟩ (by norm_num))
theorem R93649 : Reach 93649 := rs (se 2 (by rfl) ⟨35118, by rfl⟩) (B 70237 (by norm_num) ⟨35118, by rfl⟩ (by norm_num))
theorem R93653 : Reach 93653 := rs (se 7 (by rfl) ⟨1097, by rfl⟩) (B 2195 (by norm_num) ⟨1097, by rfl⟩ (by norm_num))
theorem R93657 : Reach 93657 := rs (se 2 (by rfl) ⟨35121, by rfl⟩) (B 70243 (by norm_num) ⟨35121, by rfl⟩ (by norm_num))
theorem R93661 : Reach 93661 := rs (se 3 (by rfl) ⟨17561, by rfl⟩) (B 35123 (by norm_num) ⟨17561, by rfl⟩ (by norm_num))
theorem R93665 : Reach 93665 := rs (se 2 (by rfl) ⟨35124, by rfl⟩) (B 70249 (by norm_num) ⟨35124, by rfl⟩ (by norm_num))
theorem R93669 : Reach 93669 := rs (se 4 (by rfl) ⟨8781, by rfl⟩) (B 17563 (by norm_num) ⟨8781, by rfl⟩ (by norm_num))
theorem R159205 : Reach 159205 := rs (se 4 (by rfl) ⟨14925, by rfl⟩) (B 29851 (by norm_num) ⟨14925, by rfl⟩ (by norm_num))
theorem R93673 : Reach 93673 := rs (se 2 (by rfl) ⟨35127, by rfl⟩) (B 70255 (by norm_num) ⟨35127, by rfl⟩ (by norm_num))
theorem R93677 : Reach 93677 := rs (se 3 (by rfl) ⟨17564, by rfl⟩) (B 35129 (by norm_num) ⟨17564, by rfl⟩ (by norm_num))
theorem R93681 : Reach 93681 := rs (se 2 (by rfl) ⟨35130, by rfl⟩) (B 70261 (by norm_num) ⟨35130, by rfl⟩ (by norm_num))
theorem R93685 : Reach 93685 := rs (se 5 (by rfl) ⟨4391, by rfl⟩) (B 8783 (by norm_num) ⟨4391, by rfl⟩ (by norm_num))
theorem R93689 : Reach 93689 := rs (se 2 (by rfl) ⟨35133, by rfl⟩) (B 70267 (by norm_num) ⟨35133, by rfl⟩ (by norm_num))
theorem R93693 : Reach 93693 := rs (se 3 (by rfl) ⟨17567, by rfl⟩) (B 35135 (by norm_num) ⟨17567, by rfl⟩ (by norm_num))
theorem R93697 : Reach 93697 := rs (se 2 (by rfl) ⟨35136, by rfl⟩) (B 70273 (by norm_num) ⟨35136, by rfl⟩ (by norm_num))
theorem R93701 : Reach 93701 := rs (se 4 (by rfl) ⟨8784, by rfl⟩) (B 17569 (by norm_num) ⟨8784, by rfl⟩ (by norm_num))
theorem R93705 : Reach 93705 := rs (se 2 (by rfl) ⟨35139, by rfl⟩) (B 70279 (by norm_num) ⟨35139, by rfl⟩ (by norm_num))
theorem R93709 : Reach 93709 := rs (se 3 (by rfl) ⟨17570, by rfl⟩) (B 35141 (by norm_num) ⟨17570, by rfl⟩ (by norm_num))
theorem R93713 : Reach 93713 := rs (se 2 (by rfl) ⟨35142, by rfl⟩) (B 70285 (by norm_num) ⟨35142, by rfl⟩ (by norm_num))
theorem R93717 : Reach 93717 := rs (se 6 (by rfl) ⟨2196, by rfl⟩) (B 4393 (by norm_num) ⟨2196, by rfl⟩ (by norm_num))
theorem R93721 : Reach 93721 := rs (se 2 (by rfl) ⟨35145, by rfl⟩) (B 70291 (by norm_num) ⟨35145, by rfl⟩ (by norm_num))
theorem R93725 : Reach 93725 := rs (se 3 (by rfl) ⟨17573, by rfl⟩) (B 35147 (by norm_num) ⟨17573, by rfl⟩ (by norm_num))
theorem R93729 : Reach 93729 := rs (se 2 (by rfl) ⟨35148, by rfl⟩) (B 70297 (by norm_num) ⟨35148, by rfl⟩ (by norm_num))
theorem R93733 : Reach 93733 := rs (se 4 (by rfl) ⟨8787, by rfl⟩) (B 17575 (by norm_num) ⟨8787, by rfl⟩ (by norm_num))
theorem R93737 : Reach 93737 := rs (se 2 (by rfl) ⟨35151, by rfl⟩) (B 70303 (by norm_num) ⟨35151, by rfl⟩ (by norm_num))
theorem R93741 : Reach 93741 := rs (se 3 (by rfl) ⟨17576, by rfl⟩) (B 35153 (by norm_num) ⟨17576, by rfl⟩ (by norm_num))
theorem R93745 : Reach 93745 := rs (se 2 (by rfl) ⟨35154, by rfl⟩) (B 70309 (by norm_num) ⟨35154, by rfl⟩ (by norm_num))
theorem R93749 : Reach 93749 := rs (se 5 (by rfl) ⟨4394, by rfl⟩) (B 8789 (by norm_num) ⟨4394, by rfl⟩ (by norm_num))
theorem R93753 : Reach 93753 := rs (se 2 (by rfl) ⟨35157, by rfl⟩) (B 70315 (by norm_num) ⟨35157, by rfl⟩ (by norm_num))
theorem R93757 : Reach 93757 := rs (se 3 (by rfl) ⟨17579, by rfl⟩) (B 35159 (by norm_num) ⟨17579, by rfl⟩ (by norm_num))
theorem R159293 : Reach 159293 := rs (se 3 (by rfl) ⟨29867, by rfl⟩) (B 59735 (by norm_num) ⟨29867, by rfl⟩ (by norm_num))
theorem R93761 : Reach 93761 := rs (se 2 (by rfl) ⟨35160, by rfl⟩) (B 70321 (by norm_num) ⟨35160, by rfl⟩ (by norm_num))
theorem R93765 : Reach 93765 := rs (se 4 (by rfl) ⟨8790, by rfl⟩) (B 17581 (by norm_num) ⟨8790, by rfl⟩ (by norm_num))
theorem R93769 : Reach 93769 := rs (se 2 (by rfl) ⟨35163, by rfl⟩) (B 70327 (by norm_num) ⟨35163, by rfl⟩ (by norm_num))
theorem R93773 : Reach 93773 := rs (se 3 (by rfl) ⟨17582, by rfl⟩) (B 35165 (by norm_num) ⟨17582, by rfl⟩ (by norm_num))
theorem R93777 : Reach 93777 := rs (se 2 (by rfl) ⟨35166, by rfl⟩) (B 70333 (by norm_num) ⟨35166, by rfl⟩ (by norm_num))
theorem R93781 : Reach 93781 := rs (se 8 (by rfl) ⟨549, by rfl⟩) (B 1099 (by norm_num) ⟨549, by rfl⟩ (by norm_num))
theorem R93785 : Reach 93785 := rs (se 2 (by rfl) ⟨35169, by rfl⟩) (B 70339 (by norm_num) ⟨35169, by rfl⟩ (by norm_num))
theorem R93789 : Reach 93789 := rs (se 3 (by rfl) ⟨17585, by rfl⟩) (B 35171 (by norm_num) ⟨17585, by rfl⟩ (by norm_num))
theorem R93793 : Reach 93793 := rs (se 2 (by rfl) ⟨35172, by rfl⟩) (B 70345 (by norm_num) ⟨35172, by rfl⟩ (by norm_num))
theorem R224869 : Reach 224869 := rs (se 4 (by rfl) ⟨21081, by rfl⟩) (B 42163 (by norm_num) ⟨21081, by rfl⟩ (by norm_num))
theorem R93797 : Reach 93797 := rs (se 4 (by rfl) ⟨8793, by rfl⟩) (B 17587 (by norm_num) ⟨8793, by rfl⟩ (by norm_num))
theorem R93801 : Reach 93801 := rs (se 2 (by rfl) ⟨35175, by rfl⟩) (B 70351 (by norm_num) ⟨35175, by rfl⟩ (by norm_num))
theorem R93805 : Reach 93805 := rs (se 3 (by rfl) ⟨17588, by rfl⟩) (B 35177 (by norm_num) ⟨17588, by rfl⟩ (by norm_num))
theorem R93809 : Reach 93809 := rs (se 2 (by rfl) ⟨35178, by rfl⟩) (B 70357 (by norm_num) ⟨35178, by rfl⟩ (by norm_num))
theorem R93813 : Reach 93813 := rs (se 5 (by rfl) ⟨4397, by rfl⟩) (B 8795 (by norm_num) ⟨4397, by rfl⟩ (by norm_num))
theorem R93817 : Reach 93817 := rs (se 2 (by rfl) ⟨35181, by rfl⟩) (B 70363 (by norm_num) ⟨35181, by rfl⟩ (by norm_num))
theorem R93821 : Reach 93821 := rs (se 3 (by rfl) ⟨17591, by rfl⟩) (B 35183 (by norm_num) ⟨17591, by rfl⟩ (by norm_num))
theorem R93825 : Reach 93825 := rs (se 2 (by rfl) ⟨35184, by rfl⟩) (B 70369 (by norm_num) ⟨35184, by rfl⟩ (by norm_num))
theorem R93829 : Reach 93829 := rs (se 4 (by rfl) ⟨8796, by rfl⟩) (B 17593 (by norm_num) ⟨8796, by rfl⟩ (by norm_num))
theorem R93833 : Reach 93833 := rs (se 2 (by rfl) ⟨35187, by rfl⟩) (B 70375 (by norm_num) ⟨35187, by rfl⟩ (by norm_num))
theorem R93837 : Reach 93837 := rs (se 3 (by rfl) ⟨17594, by rfl⟩) (B 35189 (by norm_num) ⟨17594, by rfl⟩ (by norm_num))
theorem R93841 : Reach 93841 := rs (se 2 (by rfl) ⟨35190, by rfl⟩) (B 70381 (by norm_num) ⟨35190, by rfl⟩ (by norm_num))
theorem R192149 : Reach 192149 := rs (se 6 (by rfl) ⟨4503, by rfl⟩) (B 9007 (by norm_num) ⟨4503, by rfl⟩ (by norm_num))
theorem R93845 : Reach 93845 := rs (se 6 (by rfl) ⟨2199, by rfl⟩) (B 4399 (by norm_num) ⟨2199, by rfl⟩ (by norm_num))
theorem R93849 : Reach 93849 := rs (se 2 (by rfl) ⟨35193, by rfl⟩) (B 70387 (by norm_num) ⟨35193, by rfl⟩ (by norm_num))
theorem R93853 : Reach 93853 := rs (se 3 (by rfl) ⟨17597, by rfl⟩) (B 35195 (by norm_num) ⟨17597, by rfl⟩ (by norm_num))
theorem R93857 : Reach 93857 := rs (se 2 (by rfl) ⟨35196, by rfl⟩) (B 70393 (by norm_num) ⟨35196, by rfl⟩ (by norm_num))
theorem R93861 : Reach 93861 := rs (se 4 (by rfl) ⟨8799, by rfl⟩) (B 17599 (by norm_num) ⟨8799, by rfl⟩ (by norm_num))
theorem R93865 : Reach 93865 := rs (se 2 (by rfl) ⟨35199, by rfl⟩) (B 70399 (by norm_num) ⟨35199, by rfl⟩ (by norm_num))
theorem R93869 : Reach 93869 := rs (se 3 (by rfl) ⟨17600, by rfl⟩) (B 35201 (by norm_num) ⟨17600, by rfl⟩ (by norm_num))
theorem R93873 : Reach 93873 := rs (se 2 (by rfl) ⟨35202, by rfl⟩) (B 70405 (by norm_num) ⟨35202, by rfl⟩ (by norm_num))
theorem R93877 : Reach 93877 := rs (se 5 (by rfl) ⟨4400, by rfl⟩) (B 8801 (by norm_num) ⟨4400, by rfl⟩ (by norm_num))
theorem R93881 : Reach 93881 := rs (se 2 (by rfl) ⟨35205, by rfl⟩) (B 70411 (by norm_num) ⟨35205, by rfl⟩ (by norm_num))
theorem R93885 : Reach 93885 := rs (se 3 (by rfl) ⟨17603, by rfl⟩) (B 35207 (by norm_num) ⟨17603, by rfl⟩ (by norm_num))
theorem R159421 : Reach 159421 := rs (se 3 (by rfl) ⟨29891, by rfl⟩) (B 59783 (by norm_num) ⟨29891, by rfl⟩ (by norm_num))
theorem R93889 : Reach 93889 := rs (se 2 (by rfl) ⟨35208, by rfl⟩) (B 70417 (by norm_num) ⟨35208, by rfl⟩ (by norm_num))
theorem R93893 : Reach 93893 := rs (se 4 (by rfl) ⟨8802, by rfl⟩) (B 17605 (by norm_num) ⟨8802, by rfl⟩ (by norm_num))
theorem R93897 : Reach 93897 := rs (se 2 (by rfl) ⟨35211, by rfl⟩) (B 70423 (by norm_num) ⟨35211, by rfl⟩ (by norm_num))
theorem R93901 : Reach 93901 := rs (se 3 (by rfl) ⟨17606, by rfl⟩) (B 35213 (by norm_num) ⟨17606, by rfl⟩ (by norm_num))
theorem R93905 : Reach 93905 := rs (se 2 (by rfl) ⟨35214, by rfl⟩) (B 70429 (by norm_num) ⟨35214, by rfl⟩ (by norm_num))
theorem R93909 : Reach 93909 := rs (se 7 (by rfl) ⟨1100, by rfl⟩) (B 2201 (by norm_num) ⟨1100, by rfl⟩ (by norm_num))
theorem R93913 : Reach 93913 := rs (se 2 (by rfl) ⟨35217, by rfl⟩) (B 70435 (by norm_num) ⟨35217, by rfl⟩ (by norm_num))
theorem R93917 : Reach 93917 := rs (se 3 (by rfl) ⟨17609, by rfl⟩) (B 35219 (by norm_num) ⟨17609, by rfl⟩ (by norm_num))
theorem R93921 : Reach 93921 := rs (se 2 (by rfl) ⟨35220, by rfl⟩) (B 70441 (by norm_num) ⟨35220, by rfl⟩ (by norm_num))
theorem R93925 : Reach 93925 := rs (se 4 (by rfl) ⟨8805, by rfl⟩) (B 17611 (by norm_num) ⟨8805, by rfl⟩ (by norm_num))
theorem R93929 : Reach 93929 := rs (se 2 (by rfl) ⟨35223, by rfl⟩) (B 70447 (by norm_num) ⟨35223, by rfl⟩ (by norm_num))
theorem R93933 : Reach 93933 := rs (se 3 (by rfl) ⟨17612, by rfl⟩) (B 35225 (by norm_num) ⟨17612, by rfl⟩ (by norm_num))
theorem R93937 : Reach 93937 := rs (se 2 (by rfl) ⟨35226, by rfl⟩) (B 70453 (by norm_num) ⟨35226, by rfl⟩ (by norm_num))
theorem R93941 : Reach 93941 := rs (se 5 (by rfl) ⟨4403, by rfl⟩) (B 8807 (by norm_num) ⟨4403, by rfl⟩ (by norm_num))
theorem R93945 : Reach 93945 := rs (se 2 (by rfl) ⟨35229, by rfl⟩) (B 70459 (by norm_num) ⟨35229, by rfl⟩ (by norm_num))
theorem R93949 : Reach 93949 := rs (se 3 (by rfl) ⟨17615, by rfl⟩) (B 35231 (by norm_num) ⟨17615, by rfl⟩ (by norm_num))
theorem R93953 : Reach 93953 := rs (se 2 (by rfl) ⟨35232, by rfl⟩) (B 70465 (by norm_num) ⟨35232, by rfl⟩ (by norm_num))
theorem R93957 : Reach 93957 := rs (se 4 (by rfl) ⟨8808, by rfl⟩) (B 17617 (by norm_num) ⟨8808, by rfl⟩ (by norm_num))
theorem R93961 : Reach 93961 := rs (se 2 (by rfl) ⟨35235, by rfl⟩) (B 70471 (by norm_num) ⟨35235, by rfl⟩ (by norm_num))
theorem R93965 : Reach 93965 := rs (se 3 (by rfl) ⟨17618, by rfl⟩) (B 35237 (by norm_num) ⟨17618, by rfl⟩ (by norm_num))
theorem R93969 : Reach 93969 := rs (se 2 (by rfl) ⟨35238, by rfl⟩) (B 70477 (by norm_num) ⟨35238, by rfl⟩ (by norm_num))
theorem R93973 : Reach 93973 := rs (se 6 (by rfl) ⟨2202, by rfl⟩) (B 4405 (by norm_num) ⟨2202, by rfl⟩ (by norm_num))
theorem R159509 : Reach 159509 := rs (se 6 (by rfl) ⟨3738, by rfl⟩) (B 7477 (by norm_num) ⟨3738, by rfl⟩ (by norm_num))
theorem R93977 : Reach 93977 := rs (se 2 (by rfl) ⟨35241, by rfl⟩) (B 70483 (by norm_num) ⟨35241, by rfl⟩ (by norm_num))
theorem R93981 : Reach 93981 := rs (se 3 (by rfl) ⟨17621, by rfl⟩) (B 35243 (by norm_num) ⟨17621, by rfl⟩ (by norm_num))
theorem R93985 : Reach 93985 := rs (se 2 (by rfl) ⟨35244, by rfl⟩) (B 70489 (by norm_num) ⟨35244, by rfl⟩ (by norm_num))
theorem R93989 : Reach 93989 := rs (se 4 (by rfl) ⟨8811, by rfl⟩) (B 17623 (by norm_num) ⟨8811, by rfl⟩ (by norm_num))
theorem R93993 : Reach 93993 := rs (se 2 (by rfl) ⟨35247, by rfl⟩) (B 70495 (by norm_num) ⟨35247, by rfl⟩ (by norm_num))
theorem R93997 : Reach 93997 := rs (se 3 (by rfl) ⟨17624, by rfl⟩) (B 35249 (by norm_num) ⟨17624, by rfl⟩ (by norm_num))
theorem R94001 : Reach 94001 := rs (se 2 (by rfl) ⟨35250, by rfl⟩) (B 70501 (by norm_num) ⟨35250, by rfl⟩ (by norm_num))
theorem R94005 : Reach 94005 := rs (se 5 (by rfl) ⟨4406, by rfl⟩) (B 8813 (by norm_num) ⟨4406, by rfl⟩ (by norm_num))
theorem R94009 : Reach 94009 := rs (se 2 (by rfl) ⟨35253, by rfl⟩) (B 70507 (by norm_num) ⟨35253, by rfl⟩ (by norm_num))
theorem R94013 : Reach 94013 := rs (se 3 (by rfl) ⟨17627, by rfl⟩) (B 35255 (by norm_num) ⟨17627, by rfl⟩ (by norm_num))
theorem R94017 : Reach 94017 := rs (se 2 (by rfl) ⟨35256, by rfl⟩) (B 70513 (by norm_num) ⟨35256, by rfl⟩ (by norm_num))
theorem R94021 : Reach 94021 := rs (se 4 (by rfl) ⟨8814, by rfl⟩) (B 17629 (by norm_num) ⟨8814, by rfl⟩ (by norm_num))
theorem R94025 : Reach 94025 := rs (se 2 (by rfl) ⟨35259, by rfl⟩) (B 70519 (by norm_num) ⟨35259, by rfl⟩ (by norm_num))
theorem R94029 : Reach 94029 := rs (se 3 (by rfl) ⟨17630, by rfl⟩) (B 35261 (by norm_num) ⟨17630, by rfl⟩ (by norm_num))
theorem R94033 : Reach 94033 := rs (se 2 (by rfl) ⟨35262, by rfl⟩) (B 70525 (by norm_num) ⟨35262, by rfl⟩ (by norm_num))
theorem R94037 : Reach 94037 := rs (se 9 (by rfl) ⟨275, by rfl⟩) (B 551 (by norm_num) ⟨275, by rfl⟩ (by norm_num))
theorem R94041 : Reach 94041 := rs (se 2 (by rfl) ⟨35265, by rfl⟩) (B 70531 (by norm_num) ⟨35265, by rfl⟩ (by norm_num))
theorem R94045 : Reach 94045 := rs (se 3 (by rfl) ⟨17633, by rfl⟩) (B 35267 (by norm_num) ⟨17633, by rfl⟩ (by norm_num))
theorem R94049 : Reach 94049 := rs (se 2 (by rfl) ⟨35268, by rfl⟩) (B 70537 (by norm_num) ⟨35268, by rfl⟩ (by norm_num))
theorem R94053 : Reach 94053 := rs (se 4 (by rfl) ⟨8817, by rfl⟩) (B 17635 (by norm_num) ⟨8817, by rfl⟩ (by norm_num))
theorem R94057 : Reach 94057 := rs (se 2 (by rfl) ⟨35271, by rfl⟩) (B 70543 (by norm_num) ⟨35271, by rfl⟩ (by norm_num))
theorem R94061 : Reach 94061 := rs (se 3 (by rfl) ⟨17636, by rfl⟩) (B 35273 (by norm_num) ⟨17636, by rfl⟩ (by norm_num))
theorem R94065 : Reach 94065 := rs (se 2 (by rfl) ⟨35274, by rfl⟩) (B 70549 (by norm_num) ⟨35274, by rfl⟩ (by norm_num))
theorem R94069 : Reach 94069 := rs (se 5 (by rfl) ⟨4409, by rfl⟩) (B 8819 (by norm_num) ⟨4409, by rfl⟩ (by norm_num))
theorem R94073 : Reach 94073 := rs (se 2 (by rfl) ⟨35277, by rfl⟩) (B 70555 (by norm_num) ⟨35277, by rfl⟩ (by norm_num))
theorem R94077 : Reach 94077 := rs (se 3 (by rfl) ⟨17639, by rfl⟩) (B 35279 (by norm_num) ⟨17639, by rfl⟩ (by norm_num))
theorem R94081 : Reach 94081 := rs (se 2 (by rfl) ⟨35280, by rfl⟩) (B 70561 (by norm_num) ⟨35280, by rfl⟩ (by norm_num))
theorem R94085 : Reach 94085 := rs (se 4 (by rfl) ⟨8820, by rfl⟩) (B 17641 (by norm_num) ⟨8820, by rfl⟩ (by norm_num))
theorem R94089 : Reach 94089 := rs (se 2 (by rfl) ⟨35283, by rfl⟩) (B 70567 (by norm_num) ⟨35283, by rfl⟩ (by norm_num))
theorem R94093 : Reach 94093 := rs (se 3 (by rfl) ⟨17642, by rfl⟩) (B 35285 (by norm_num) ⟨17642, by rfl⟩ (by norm_num))
theorem R94097 : Reach 94097 := rs (se 2 (by rfl) ⟨35286, by rfl⟩) (B 70573 (by norm_num) ⟨35286, by rfl⟩ (by norm_num))
theorem R94101 : Reach 94101 := rs (se 6 (by rfl) ⟨2205, by rfl⟩) (B 4411 (by norm_num) ⟨2205, by rfl⟩ (by norm_num))
theorem R159637 : Reach 159637 := rs (se 6 (by rfl) ⟨3741, by rfl⟩) (B 7483 (by norm_num) ⟨3741, by rfl⟩ (by norm_num))
theorem R94105 : Reach 94105 := rs (se 2 (by rfl) ⟨35289, by rfl⟩) (B 70579 (by norm_num) ⟨35289, by rfl⟩ (by norm_num))
theorem R94109 : Reach 94109 := rs (se 3 (by rfl) ⟨17645, by rfl⟩) (B 35291 (by norm_num) ⟨17645, by rfl⟩ (by norm_num))
theorem R94113 : Reach 94113 := rs (se 2 (by rfl) ⟨35292, by rfl⟩) (B 70585 (by norm_num) ⟨35292, by rfl⟩ (by norm_num))
theorem R94117 : Reach 94117 := rs (se 4 (by rfl) ⟨8823, by rfl⟩) (B 17647 (by norm_num) ⟨8823, by rfl⟩ (by norm_num))
theorem R94121 : Reach 94121 := rs (se 2 (by rfl) ⟨35295, by rfl⟩) (B 70591 (by norm_num) ⟨35295, by rfl⟩ (by norm_num))
theorem R94125 : Reach 94125 := rs (se 3 (by rfl) ⟨17648, by rfl⟩) (B 35297 (by norm_num) ⟨17648, by rfl⟩ (by norm_num))
theorem R94129 : Reach 94129 := rs (se 2 (by rfl) ⟨35298, by rfl⟩) (B 70597 (by norm_num) ⟨35298, by rfl⟩ (by norm_num))
theorem R94133 : Reach 94133 := rs (se 5 (by rfl) ⟨4412, by rfl⟩) (B 8825 (by norm_num) ⟨4412, by rfl⟩ (by norm_num))
theorem R94137 : Reach 94137 := rs (se 2 (by rfl) ⟨35301, by rfl⟩) (B 70603 (by norm_num) ⟨35301, by rfl⟩ (by norm_num))
theorem R94141 : Reach 94141 := rs (se 3 (by rfl) ⟨17651, by rfl⟩) (B 35303 (by norm_num) ⟨17651, by rfl⟩ (by norm_num))
theorem R94145 : Reach 94145 := rs (se 2 (by rfl) ⟨35304, by rfl⟩) (B 70609 (by norm_num) ⟨35304, by rfl⟩ (by norm_num))
theorem R94149 : Reach 94149 := rs (se 4 (by rfl) ⟨8826, by rfl⟩) (B 17653 (by norm_num) ⟨8826, by rfl⟩ (by norm_num))
theorem R94153 : Reach 94153 := rs (se 2 (by rfl) ⟨35307, by rfl⟩) (B 70615 (by norm_num) ⟨35307, by rfl⟩ (by norm_num))
theorem R94157 : Reach 94157 := rs (se 3 (by rfl) ⟨17654, by rfl⟩) (B 35309 (by norm_num) ⟨17654, by rfl⟩ (by norm_num))
theorem R94161 : Reach 94161 := rs (se 2 (by rfl) ⟨35310, by rfl⟩) (B 70621 (by norm_num) ⟨35310, by rfl⟩ (by norm_num))
theorem R94165 : Reach 94165 := rs (se 7 (by rfl) ⟨1103, by rfl⟩) (B 2207 (by norm_num) ⟨1103, by rfl⟩ (by norm_num))
theorem R94169 : Reach 94169 := rs (se 2 (by rfl) ⟨35313, by rfl⟩) (B 70627 (by norm_num) ⟨35313, by rfl⟩ (by norm_num))
theorem R94173 : Reach 94173 := rs (se 3 (by rfl) ⟨17657, by rfl⟩) (B 35315 (by norm_num) ⟨17657, by rfl⟩ (by norm_num))
theorem R94177 : Reach 94177 := rs (se 2 (by rfl) ⟨35316, by rfl⟩) (B 70633 (by norm_num) ⟨35316, by rfl⟩ (by norm_num))
theorem R94181 : Reach 94181 := rs (se 4 (by rfl) ⟨8829, by rfl⟩) (B 17659 (by norm_num) ⟨8829, by rfl⟩ (by norm_num))
theorem R94185 : Reach 94185 := rs (se 2 (by rfl) ⟨35319, by rfl⟩) (B 70639 (by norm_num) ⟨35319, by rfl⟩ (by norm_num))
theorem R94189 : Reach 94189 := rs (se 3 (by rfl) ⟨17660, by rfl⟩) (B 35321 (by norm_num) ⟨17660, by rfl⟩ (by norm_num))
theorem R159725 : Reach 159725 := rs (se 3 (by rfl) ⟨29948, by rfl⟩) (B 59897 (by norm_num) ⟨29948, by rfl⟩ (by norm_num))
theorem R94193 : Reach 94193 := rs (se 2 (by rfl) ⟨35322, by rfl⟩) (B 70645 (by norm_num) ⟨35322, by rfl⟩ (by norm_num))
theorem R94197 : Reach 94197 := rs (se 5 (by rfl) ⟨4415, by rfl⟩) (B 8831 (by norm_num) ⟨4415, by rfl⟩ (by norm_num))
theorem R94201 : Reach 94201 := rs (se 2 (by rfl) ⟨35325, by rfl⟩) (B 70651 (by norm_num) ⟨35325, by rfl⟩ (by norm_num))
theorem R94205 : Reach 94205 := rs (se 3 (by rfl) ⟨17663, by rfl⟩) (B 35327 (by norm_num) ⟨17663, by rfl⟩ (by norm_num))
theorem R94209 : Reach 94209 := rs (se 2 (by rfl) ⟨35328, by rfl⟩) (B 70657 (by norm_num) ⟨35328, by rfl⟩ (by norm_num))
theorem R94213 : Reach 94213 := rs (se 4 (by rfl) ⟨8832, by rfl⟩) (B 17665 (by norm_num) ⟨8832, by rfl⟩ (by norm_num))
theorem R94217 : Reach 94217 := rs (se 2 (by rfl) ⟨35331, by rfl⟩) (B 70663 (by norm_num) ⟨35331, by rfl⟩ (by norm_num))
theorem R94221 : Reach 94221 := rs (se 3 (by rfl) ⟨17666, by rfl⟩) (B 35333 (by norm_num) ⟨17666, by rfl⟩ (by norm_num))
theorem R94225 : Reach 94225 := rs (se 2 (by rfl) ⟨35334, by rfl⟩) (B 70669 (by norm_num) ⟨35334, by rfl⟩ (by norm_num))
theorem R94229 : Reach 94229 := rs (se 6 (by rfl) ⟨2208, by rfl⟩) (B 4417 (by norm_num) ⟨2208, by rfl⟩ (by norm_num))
theorem R94233 : Reach 94233 := rs (se 2 (by rfl) ⟨35337, by rfl⟩) (B 70675 (by norm_num) ⟨35337, by rfl⟩ (by norm_num))
theorem R94237 : Reach 94237 := rs (se 3 (by rfl) ⟨17669, by rfl⟩) (B 35339 (by norm_num) ⟨17669, by rfl⟩ (by norm_num))
theorem R94241 : Reach 94241 := rs (se 2 (by rfl) ⟨35340, by rfl⟩) (B 70681 (by norm_num) ⟨35340, by rfl⟩ (by norm_num))
theorem R94245 : Reach 94245 := rs (se 4 (by rfl) ⟨8835, by rfl⟩) (B 17671 (by norm_num) ⟨8835, by rfl⟩ (by norm_num))
theorem R94249 : Reach 94249 := rs (se 2 (by rfl) ⟨35343, by rfl⟩) (B 70687 (by norm_num) ⟨35343, by rfl⟩ (by norm_num))
theorem R94253 : Reach 94253 := rs (se 3 (by rfl) ⟨17672, by rfl⟩) (B 35345 (by norm_num) ⟨17672, by rfl⟩ (by norm_num))
theorem R94257 : Reach 94257 := rs (se 2 (by rfl) ⟨35346, by rfl⟩) (B 70693 (by norm_num) ⟨35346, by rfl⟩ (by norm_num))
theorem R94261 : Reach 94261 := rs (se 5 (by rfl) ⟨4418, by rfl⟩) (B 8837 (by norm_num) ⟨4418, by rfl⟩ (by norm_num))
theorem R454709 : Reach 454709 := rs (se 5 (by rfl) ⟨21314, by rfl⟩) (B 42629 (by norm_num) ⟨21314, by rfl⟩ (by norm_num))
theorem R94265 : Reach 94265 := rs (se 2 (by rfl) ⟨35349, by rfl⟩) (B 70699 (by norm_num) ⟨35349, by rfl⟩ (by norm_num))
theorem R94269 : Reach 94269 := rs (se 3 (by rfl) ⟨17675, by rfl⟩) (B 35351 (by norm_num) ⟨17675, by rfl⟩ (by norm_num))
theorem R94273 : Reach 94273 := rs (se 2 (by rfl) ⟨35352, by rfl⟩) (B 70705 (by norm_num) ⟨35352, by rfl⟩ (by norm_num))
theorem R94277 : Reach 94277 := rs (se 4 (by rfl) ⟨8838, by rfl⟩) (B 17677 (by norm_num) ⟨8838, by rfl⟩ (by norm_num))
theorem R94281 : Reach 94281 := rs (se 2 (by rfl) ⟨35355, by rfl⟩) (B 70711 (by norm_num) ⟨35355, by rfl⟩ (by norm_num))
theorem R94285 : Reach 94285 := rs (se 3 (by rfl) ⟨17678, by rfl⟩) (B 35357 (by norm_num) ⟨17678, by rfl⟩ (by norm_num))
theorem R94289 : Reach 94289 := rs (se 2 (by rfl) ⟨35358, by rfl⟩) (B 70717 (by norm_num) ⟨35358, by rfl⟩ (by norm_num))
theorem R94293 : Reach 94293 := rs (se 8 (by rfl) ⟨552, by rfl⟩) (B 1105 (by norm_num) ⟨552, by rfl⟩ (by norm_num))
theorem R94297 : Reach 94297 := rs (se 2 (by rfl) ⟨35361, by rfl⟩) (B 70723 (by norm_num) ⟨35361, by rfl⟩ (by norm_num))
theorem R94301 : Reach 94301 := rs (se 3 (by rfl) ⟨17681, by rfl⟩) (B 35363 (by norm_num) ⟨17681, by rfl⟩ (by norm_num))
theorem R94305 : Reach 94305 := rs (se 2 (by rfl) ⟨35364, by rfl⟩) (B 70729 (by norm_num) ⟨35364, by rfl⟩ (by norm_num))
theorem R94309 : Reach 94309 := rs (se 4 (by rfl) ⟨8841, by rfl⟩) (B 17683 (by norm_num) ⟨8841, by rfl⟩ (by norm_num))
theorem R94313 : Reach 94313 := rs (se 2 (by rfl) ⟨35367, by rfl⟩) (B 70735 (by norm_num) ⟨35367, by rfl⟩ (by norm_num))
theorem R94317 : Reach 94317 := rs (se 3 (by rfl) ⟨17684, by rfl⟩) (B 35369 (by norm_num) ⟨17684, by rfl⟩ (by norm_num))
theorem R94321 : Reach 94321 := rs (se 2 (by rfl) ⟨35370, by rfl⟩) (B 70741 (by norm_num) ⟨35370, by rfl⟩ (by norm_num))
theorem R159853 : Reach 159853 := rs (se 3 (by rfl) ⟨29972, by rfl⟩) (B 59945 (by norm_num) ⟨29972, by rfl⟩ (by norm_num))
theorem R94325 : Reach 94325 := rs (se 5 (by rfl) ⟨4421, by rfl⟩) (B 8843 (by norm_num) ⟨4421, by rfl⟩ (by norm_num))
theorem R94329 : Reach 94329 := rs (se 2 (by rfl) ⟨35373, by rfl⟩) (B 70747 (by norm_num) ⟨35373, by rfl⟩ (by norm_num))
theorem R94333 : Reach 94333 := rs (se 3 (by rfl) ⟨17687, by rfl⟩) (B 35375 (by norm_num) ⟨17687, by rfl⟩ (by norm_num))
theorem R94337 : Reach 94337 := rs (se 2 (by rfl) ⟨35376, by rfl⟩) (B 70753 (by norm_num) ⟨35376, by rfl⟩ (by norm_num))
theorem R94341 : Reach 94341 := rs (se 4 (by rfl) ⟨8844, by rfl⟩) (B 17689 (by norm_num) ⟨8844, by rfl⟩ (by norm_num))
theorem R94345 : Reach 94345 := rs (se 2 (by rfl) ⟨35379, by rfl⟩) (B 70759 (by norm_num) ⟨35379, by rfl⟩ (by norm_num))
theorem R94349 : Reach 94349 := rs (se 3 (by rfl) ⟨17690, by rfl⟩) (B 35381 (by norm_num) ⟨17690, by rfl⟩ (by norm_num))
theorem R94353 : Reach 94353 := rs (se 2 (by rfl) ⟨35382, by rfl⟩) (B 70765 (by norm_num) ⟨35382, by rfl⟩ (by norm_num))
theorem R94357 : Reach 94357 := rs (se 6 (by rfl) ⟨2211, by rfl⟩) (B 4423 (by norm_num) ⟨2211, by rfl⟩ (by norm_num))
theorem R94361 : Reach 94361 := rs (se 2 (by rfl) ⟨35385, by rfl⟩) (B 70771 (by norm_num) ⟨35385, by rfl⟩ (by norm_num))
theorem R94365 : Reach 94365 := rs (se 3 (by rfl) ⟨17693, by rfl⟩) (B 35387 (by norm_num) ⟨17693, by rfl⟩ (by norm_num))
theorem R94369 : Reach 94369 := rs (se 2 (by rfl) ⟨35388, by rfl⟩) (B 70777 (by norm_num) ⟨35388, by rfl⟩ (by norm_num))
theorem R94373 : Reach 94373 := rs (se 4 (by rfl) ⟨8847, by rfl⟩) (B 17695 (by norm_num) ⟨8847, by rfl⟩ (by norm_num))
theorem R94377 : Reach 94377 := rs (se 2 (by rfl) ⟨35391, by rfl⟩) (B 70783 (by norm_num) ⟨35391, by rfl⟩ (by norm_num))
theorem R94381 : Reach 94381 := rs (se 3 (by rfl) ⟨17696, by rfl⟩) (B 35393 (by norm_num) ⟨17696, by rfl⟩ (by norm_num))
theorem R94385 : Reach 94385 := rs (se 2 (by rfl) ⟨35394, by rfl⟩) (B 70789 (by norm_num) ⟨35394, by rfl⟩ (by norm_num))
theorem R94389 : Reach 94389 := rs (se 5 (by rfl) ⟨4424, by rfl⟩) (B 8849 (by norm_num) ⟨4424, by rfl⟩ (by norm_num))
theorem R94393 : Reach 94393 := rs (se 2 (by rfl) ⟨35397, by rfl⟩) (B 70795 (by norm_num) ⟨35397, by rfl⟩ (by norm_num))
theorem R94397 : Reach 94397 := rs (se 3 (by rfl) ⟨17699, by rfl⟩) (B 35399 (by norm_num) ⟨17699, by rfl⟩ (by norm_num))
theorem R94401 : Reach 94401 := rs (se 2 (by rfl) ⟨35400, by rfl⟩) (B 70801 (by norm_num) ⟨35400, by rfl⟩ (by norm_num))
theorem R94405 : Reach 94405 := rs (se 4 (by rfl) ⟨8850, by rfl⟩) (B 17701 (by norm_num) ⟨8850, by rfl⟩ (by norm_num))
theorem R159941 : Reach 159941 := rs (se 4 (by rfl) ⟨14994, by rfl⟩) (B 29989 (by norm_num) ⟨14994, by rfl⟩ (by norm_num))
theorem R94409 : Reach 94409 := rs (se 2 (by rfl) ⟨35403, by rfl⟩) (B 70807 (by norm_num) ⟨35403, by rfl⟩ (by norm_num))
theorem R94413 : Reach 94413 := rs (se 3 (by rfl) ⟨17702, by rfl⟩) (B 35405 (by norm_num) ⟨17702, by rfl⟩ (by norm_num))
theorem R94417 : Reach 94417 := rs (se 2 (by rfl) ⟨35406, by rfl⟩) (B 70813 (by norm_num) ⟨35406, by rfl⟩ (by norm_num))
theorem R94421 : Reach 94421 := rs (se 7 (by rfl) ⟨1106, by rfl⟩) (B 2213 (by norm_num) ⟨1106, by rfl⟩ (by norm_num))
theorem R1077461 : Reach 1077461 := rs (se 7 (by rfl) ⟨12626, by rfl⟩) (B 25253 (by norm_num) ⟨12626, by rfl⟩ (by norm_num))
theorem R94425 : Reach 94425 := rs (se 2 (by rfl) ⟨35409, by rfl⟩) (B 70819 (by norm_num) ⟨35409, by rfl⟩ (by norm_num))
theorem R94429 : Reach 94429 := rs (se 3 (by rfl) ⟨17705, by rfl⟩) (B 35411 (by norm_num) ⟨17705, by rfl⟩ (by norm_num))
theorem R94433 : Reach 94433 := rs (se 2 (by rfl) ⟨35412, by rfl⟩) (B 70825 (by norm_num) ⟨35412, by rfl⟩ (by norm_num))
theorem R225509 : Reach 225509 := rs (se 4 (by rfl) ⟨21141, by rfl⟩) (B 42283 (by norm_num) ⟨21141, by rfl⟩ (by norm_num))
theorem R94437 : Reach 94437 := rs (se 4 (by rfl) ⟨8853, by rfl⟩) (B 17707 (by norm_num) ⟨8853, by rfl⟩ (by norm_num))
theorem R94441 : Reach 94441 := rs (se 2 (by rfl) ⟨35415, by rfl⟩) (B 70831 (by norm_num) ⟨35415, by rfl⟩ (by norm_num))
theorem R94445 : Reach 94445 := rs (se 3 (by rfl) ⟨17708, by rfl⟩) (B 35417 (by norm_num) ⟨17708, by rfl⟩ (by norm_num))
theorem R94449 : Reach 94449 := rs (se 2 (by rfl) ⟨35418, by rfl⟩) (B 70837 (by norm_num) ⟨35418, by rfl⟩ (by norm_num))
theorem R94453 : Reach 94453 := rs (se 5 (by rfl) ⟨4427, by rfl⟩) (B 8855 (by norm_num) ⟨4427, by rfl⟩ (by norm_num))
theorem R94457 : Reach 94457 := rs (se 2 (by rfl) ⟨35421, by rfl⟩) (B 70843 (by norm_num) ⟨35421, by rfl⟩ (by norm_num))
theorem R94461 : Reach 94461 := rs (se 3 (by rfl) ⟨17711, by rfl⟩) (B 35423 (by norm_num) ⟨17711, by rfl⟩ (by norm_num))
theorem R94465 : Reach 94465 := rs (se 2 (by rfl) ⟨35424, by rfl⟩) (B 70849 (by norm_num) ⟨35424, by rfl⟩ (by norm_num))
theorem R94469 : Reach 94469 := rs (se 4 (by rfl) ⟨8856, by rfl⟩) (B 17713 (by norm_num) ⟨8856, by rfl⟩ (by norm_num))
theorem R94473 : Reach 94473 := rs (se 2 (by rfl) ⟨35427, by rfl⟩) (B 70855 (by norm_num) ⟨35427, by rfl⟩ (by norm_num))
theorem R94477 : Reach 94477 := rs (se 3 (by rfl) ⟨17714, by rfl⟩) (B 35429 (by norm_num) ⟨17714, by rfl⟩ (by norm_num))
theorem R94481 : Reach 94481 := rs (se 2 (by rfl) ⟨35430, by rfl⟩) (B 70861 (by norm_num) ⟨35430, by rfl⟩ (by norm_num))
theorem R94485 : Reach 94485 := rs (se 6 (by rfl) ⟨2214, by rfl⟩) (B 4429 (by norm_num) ⟨2214, by rfl⟩ (by norm_num))
theorem R94489 : Reach 94489 := rs (se 2 (by rfl) ⟨35433, by rfl⟩) (B 70867 (by norm_num) ⟨35433, by rfl⟩ (by norm_num))
theorem R94493 : Reach 94493 := rs (se 3 (by rfl) ⟨17717, by rfl⟩) (B 35435 (by norm_num) ⟨17717, by rfl⟩ (by norm_num))
theorem R94497 : Reach 94497 := rs (se 2 (by rfl) ⟨35436, by rfl⟩) (B 70873 (by norm_num) ⟨35436, by rfl⟩ (by norm_num))
theorem R94501 : Reach 94501 := rs (se 4 (by rfl) ⟨8859, by rfl⟩) (B 17719 (by norm_num) ⟨8859, by rfl⟩ (by norm_num))
theorem R94505 : Reach 94505 := rs (se 2 (by rfl) ⟨35439, by rfl⟩) (B 70879 (by norm_num) ⟨35439, by rfl⟩ (by norm_num))
theorem R94509 : Reach 94509 := rs (se 3 (by rfl) ⟨17720, by rfl⟩) (B 35441 (by norm_num) ⟨17720, by rfl⟩ (by norm_num))
theorem R94513 : Reach 94513 := rs (se 2 (by rfl) ⟨35442, by rfl⟩) (B 70885 (by norm_num) ⟨35442, by rfl⟩ (by norm_num))
theorem R94517 : Reach 94517 := rs (se 5 (by rfl) ⟨4430, by rfl⟩) (B 8861 (by norm_num) ⟨4430, by rfl⟩ (by norm_num))
theorem R94521 : Reach 94521 := rs (se 2 (by rfl) ⟨35445, by rfl⟩) (B 70891 (by norm_num) ⟨35445, by rfl⟩ (by norm_num))
theorem R94525 : Reach 94525 := rs (se 3 (by rfl) ⟨17723, by rfl⟩) (B 35447 (by norm_num) ⟨17723, by rfl⟩ (by norm_num))
theorem R94529 : Reach 94529 := rs (se 2 (by rfl) ⟨35448, by rfl⟩) (B 70897 (by norm_num) ⟨35448, by rfl⟩ (by norm_num))
theorem R94533 : Reach 94533 := rs (se 4 (by rfl) ⟨8862, by rfl⟩) (B 17725 (by norm_num) ⟨8862, by rfl⟩ (by norm_num))
theorem R160069 : Reach 160069 := rs (se 4 (by rfl) ⟨15006, by rfl⟩) (B 30013 (by norm_num) ⟨15006, by rfl⟩ (by norm_num))
theorem R94537 : Reach 94537 := rs (se 2 (by rfl) ⟨35451, by rfl⟩) (B 70903 (by norm_num) ⟨35451, by rfl⟩ (by norm_num))
theorem R94541 : Reach 94541 := rs (se 3 (by rfl) ⟨17726, by rfl⟩) (B 35453 (by norm_num) ⟨17726, by rfl⟩ (by norm_num))
theorem R94545 : Reach 94545 := rs (se 2 (by rfl) ⟨35454, by rfl⟩) (B 70909 (by norm_num) ⟨35454, by rfl⟩ (by norm_num))
theorem R94549 : Reach 94549 := rs (se 10 (by rfl) ⟨138, by rfl⟩) (B 277 (by norm_num) ⟨138, by rfl⟩ (by norm_num))
theorem R94553 : Reach 94553 := rs (se 2 (by rfl) ⟨35457, by rfl⟩) (B 70915 (by norm_num) ⟨35457, by rfl⟩ (by norm_num))
theorem R94557 : Reach 94557 := rs (se 3 (by rfl) ⟨17729, by rfl⟩) (B 35459 (by norm_num) ⟨17729, by rfl⟩ (by norm_num))
theorem R94561 : Reach 94561 := rs (se 2 (by rfl) ⟨35460, by rfl⟩) (B 70921 (by norm_num) ⟨35460, by rfl⟩ (by norm_num))
theorem R94565 : Reach 94565 := rs (se 4 (by rfl) ⟨8865, by rfl⟩) (B 17731 (by norm_num) ⟨8865, by rfl⟩ (by norm_num))
theorem R94569 : Reach 94569 := rs (se 2 (by rfl) ⟨35463, by rfl⟩) (B 70927 (by norm_num) ⟨35463, by rfl⟩ (by norm_num))
theorem R94573 : Reach 94573 := rs (se 3 (by rfl) ⟨17732, by rfl⟩) (B 35465 (by norm_num) ⟨17732, by rfl⟩ (by norm_num))
theorem R94577 : Reach 94577 := rs (se 2 (by rfl) ⟨35466, by rfl⟩) (B 70933 (by norm_num) ⟨35466, by rfl⟩ (by norm_num))
theorem R94581 : Reach 94581 := rs (se 5 (by rfl) ⟨4433, by rfl⟩) (B 8867 (by norm_num) ⟨4433, by rfl⟩ (by norm_num))
theorem R94585 : Reach 94585 := rs (se 2 (by rfl) ⟨35469, by rfl⟩) (B 70939 (by norm_num) ⟨35469, by rfl⟩ (by norm_num))
theorem R94589 : Reach 94589 := rs (se 3 (by rfl) ⟨17735, by rfl⟩) (B 35471 (by norm_num) ⟨17735, by rfl⟩ (by norm_num))
theorem R94593 : Reach 94593 := rs (se 2 (by rfl) ⟨35472, by rfl⟩) (B 70945 (by norm_num) ⟨35472, by rfl⟩ (by norm_num))
theorem R94597 : Reach 94597 := rs (se 4 (by rfl) ⟨8868, by rfl⟩) (B 17737 (by norm_num) ⟨8868, by rfl⟩ (by norm_num))
theorem R94601 : Reach 94601 := rs (se 2 (by rfl) ⟨35475, by rfl⟩) (B 70951 (by norm_num) ⟨35475, by rfl⟩ (by norm_num))
theorem R94605 : Reach 94605 := rs (se 3 (by rfl) ⟨17738, by rfl⟩) (B 35477 (by norm_num) ⟨17738, by rfl⟩ (by norm_num))
theorem R94609 : Reach 94609 := rs (se 2 (by rfl) ⟨35478, by rfl⟩) (B 70957 (by norm_num) ⟨35478, by rfl⟩ (by norm_num))
theorem R94613 : Reach 94613 := rs (se 6 (by rfl) ⟨2217, by rfl⟩) (B 4435 (by norm_num) ⟨2217, by rfl⟩ (by norm_num))
theorem R94617 : Reach 94617 := rs (se 2 (by rfl) ⟨35481, by rfl⟩) (B 70963 (by norm_num) ⟨35481, by rfl⟩ (by norm_num))
theorem R160157 : Reach 160157 := rs (se 3 (by rfl) ⟨30029, by rfl⟩) (B 60059 (by norm_num) ⟨30029, by rfl⟩ (by norm_num))
theorem R94621 : Reach 94621 := rs (se 3 (by rfl) ⟨17741, by rfl⟩) (B 35483 (by norm_num) ⟨17741, by rfl⟩ (by norm_num))
theorem R94625 : Reach 94625 := rs (se 2 (by rfl) ⟨35484, by rfl⟩) (B 70969 (by norm_num) ⟨35484, by rfl⟩ (by norm_num))
theorem R94629 : Reach 94629 := rs (se 4 (by rfl) ⟨8871, by rfl⟩) (B 17743 (by norm_num) ⟨8871, by rfl⟩ (by norm_num))
theorem R94633 : Reach 94633 := rs (se 2 (by rfl) ⟨35487, by rfl⟩) (B 70975 (by norm_num) ⟨35487, by rfl⟩ (by norm_num))
theorem R94637 : Reach 94637 := rs (se 3 (by rfl) ⟨17744, by rfl⟩) (B 35489 (by norm_num) ⟨17744, by rfl⟩ (by norm_num))
theorem R94641 : Reach 94641 := rs (se 2 (by rfl) ⟨35490, by rfl⟩) (B 70981 (by norm_num) ⟨35490, by rfl⟩ (by norm_num))
theorem R750005 : Reach 750005 := rs (se 5 (by rfl) ⟨35156, by rfl⟩) (B 70313 (by norm_num) ⟨35156, by rfl⟩ (by norm_num))
theorem R94645 : Reach 94645 := rs (se 5 (by rfl) ⟨4436, by rfl⟩) (B 8873 (by norm_num) ⟨4436, by rfl⟩ (by norm_num))
theorem R94649 : Reach 94649 := rs (se 2 (by rfl) ⟨35493, by rfl⟩) (B 70987 (by norm_num) ⟨35493, by rfl⟩ (by norm_num))
theorem R94653 : Reach 94653 := rs (se 3 (by rfl) ⟨17747, by rfl⟩) (B 35495 (by norm_num) ⟨17747, by rfl⟩ (by norm_num))
theorem R94657 : Reach 94657 := rs (se 2 (by rfl) ⟨35496, by rfl⟩) (B 70993 (by norm_num) ⟨35496, by rfl⟩ (by norm_num))
theorem R94661 : Reach 94661 := rs (se 4 (by rfl) ⟨8874, by rfl⟩) (B 17749 (by norm_num) ⟨8874, by rfl⟩ (by norm_num))
theorem R94665 : Reach 94665 := rs (se 2 (by rfl) ⟨35499, by rfl⟩) (B 70999 (by norm_num) ⟨35499, by rfl⟩ (by norm_num))
theorem R94669 : Reach 94669 := rs (se 3 (by rfl) ⟨17750, by rfl⟩) (B 35501 (by norm_num) ⟨17750, by rfl⟩ (by norm_num))
theorem R94673 : Reach 94673 := rs (se 2 (by rfl) ⟨35502, by rfl⟩) (B 71005 (by norm_num) ⟨35502, by rfl⟩ (by norm_num))
theorem R94677 : Reach 94677 := rs (se 7 (by rfl) ⟨1109, by rfl⟩) (B 2219 (by norm_num) ⟨1109, by rfl⟩ (by norm_num))
theorem R94681 : Reach 94681 := rs (se 2 (by rfl) ⟨35505, by rfl⟩) (B 71011 (by norm_num) ⟨35505, by rfl⟩ (by norm_num))
theorem R94685 : Reach 94685 := rs (se 3 (by rfl) ⟨17753, by rfl⟩) (B 35507 (by norm_num) ⟨17753, by rfl⟩ (by norm_num))
theorem R94689 : Reach 94689 := rs (se 2 (by rfl) ⟨35508, by rfl⟩) (B 71017 (by norm_num) ⟨35508, by rfl⟩ (by norm_num))
theorem R94693 : Reach 94693 := rs (se 4 (by rfl) ⟨8877, by rfl⟩) (B 17755 (by norm_num) ⟨8877, by rfl⟩ (by norm_num))
theorem R94697 : Reach 94697 := rs (se 2 (by rfl) ⟨35511, by rfl⟩) (B 71023 (by norm_num) ⟨35511, by rfl⟩ (by norm_num))
theorem R94701 : Reach 94701 := rs (se 3 (by rfl) ⟨17756, by rfl⟩) (B 35513 (by norm_num) ⟨17756, by rfl⟩ (by norm_num))
theorem R94705 : Reach 94705 := rs (se 2 (by rfl) ⟨35514, by rfl⟩) (B 71029 (by norm_num) ⟨35514, by rfl⟩ (by norm_num))
theorem R94709 : Reach 94709 := rs (se 5 (by rfl) ⟨4439, by rfl⟩) (B 8879 (by norm_num) ⟨4439, by rfl⟩ (by norm_num))
theorem R94713 : Reach 94713 := rs (se 2 (by rfl) ⟨35517, by rfl⟩) (B 71035 (by norm_num) ⟨35517, by rfl⟩ (by norm_num))
theorem R94717 : Reach 94717 := rs (se 3 (by rfl) ⟨17759, by rfl⟩) (B 35519 (by norm_num) ⟨17759, by rfl⟩ (by norm_num))
theorem R94721 : Reach 94721 := rs (se 2 (by rfl) ⟨35520, by rfl⟩) (B 71041 (by norm_num) ⟨35520, by rfl⟩ (by norm_num))
theorem R94725 : Reach 94725 := rs (se 4 (by rfl) ⟨8880, by rfl⟩) (B 17761 (by norm_num) ⟨8880, by rfl⟩ (by norm_num))
theorem R94729 : Reach 94729 := rs (se 2 (by rfl) ⟨35523, by rfl⟩) (B 71047 (by norm_num) ⟨35523, by rfl⟩ (by norm_num))
theorem R94733 : Reach 94733 := rs (se 3 (by rfl) ⟨17762, by rfl⟩) (B 35525 (by norm_num) ⟨17762, by rfl⟩ (by norm_num))
theorem R94737 : Reach 94737 := rs (se 2 (by rfl) ⟨35526, by rfl⟩) (B 71053 (by norm_num) ⟨35526, by rfl⟩ (by norm_num))
theorem R94741 : Reach 94741 := rs (se 6 (by rfl) ⟨2220, by rfl⟩) (B 4441 (by norm_num) ⟨2220, by rfl⟩ (by norm_num))
theorem R94745 : Reach 94745 := rs (se 2 (by rfl) ⟨35529, by rfl⟩) (B 71059 (by norm_num) ⟨35529, by rfl⟩ (by norm_num))
theorem R94749 : Reach 94749 := rs (se 3 (by rfl) ⟨17765, by rfl⟩) (B 35531 (by norm_num) ⟨17765, by rfl⟩ (by norm_num))
theorem R160285 : Reach 160285 := rs (se 3 (by rfl) ⟨30053, by rfl⟩) (B 60107 (by norm_num) ⟨30053, by rfl⟩ (by norm_num))
theorem R94753 : Reach 94753 := rs (se 2 (by rfl) ⟨35532, by rfl⟩) (B 71065 (by norm_num) ⟨35532, by rfl⟩ (by norm_num))
theorem R94757 : Reach 94757 := rs (se 4 (by rfl) ⟨8883, by rfl⟩) (B 17767 (by norm_num) ⟨8883, by rfl⟩ (by norm_num))
theorem R94761 : Reach 94761 := rs (se 2 (by rfl) ⟨35535, by rfl⟩) (B 71071 (by norm_num) ⟨35535, by rfl⟩ (by norm_num))
theorem R94765 : Reach 94765 := rs (se 3 (by rfl) ⟨17768, by rfl⟩) (B 35537 (by norm_num) ⟨17768, by rfl⟩ (by norm_num))
theorem R94769 : Reach 94769 := rs (se 2 (by rfl) ⟨35538, by rfl⟩) (B 71077 (by norm_num) ⟨35538, by rfl⟩ (by norm_num))
theorem R94773 : Reach 94773 := rs (se 5 (by rfl) ⟨4442, by rfl⟩) (B 8885 (by norm_num) ⟨4442, by rfl⟩ (by norm_num))
theorem R94777 : Reach 94777 := rs (se 2 (by rfl) ⟨35541, by rfl⟩) (B 71083 (by norm_num) ⟨35541, by rfl⟩ (by norm_num))
theorem R94781 : Reach 94781 := rs (se 3 (by rfl) ⟨17771, by rfl⟩) (B 35543 (by norm_num) ⟨17771, by rfl⟩ (by norm_num))
theorem R94785 : Reach 94785 := rs (se 2 (by rfl) ⟨35544, by rfl⟩) (B 71089 (by norm_num) ⟨35544, by rfl⟩ (by norm_num))
theorem R94789 : Reach 94789 := rs (se 4 (by rfl) ⟨8886, by rfl⟩) (B 17773 (by norm_num) ⟨8886, by rfl⟩ (by norm_num))
theorem R94793 : Reach 94793 := rs (se 2 (by rfl) ⟨35547, by rfl⟩) (B 71095 (by norm_num) ⟨35547, by rfl⟩ (by norm_num))
theorem R94797 : Reach 94797 := rs (se 3 (by rfl) ⟨17774, by rfl⟩) (B 35549 (by norm_num) ⟨17774, by rfl⟩ (by norm_num))
theorem R94801 : Reach 94801 := rs (se 2 (by rfl) ⟨35550, by rfl⟩) (B 71101 (by norm_num) ⟨35550, by rfl⟩ (by norm_num))
theorem R94805 : Reach 94805 := rs (se 8 (by rfl) ⟨555, by rfl⟩) (B 1111 (by norm_num) ⟨555, by rfl⟩ (by norm_num))
theorem R94809 : Reach 94809 := rs (se 2 (by rfl) ⟨35553, by rfl⟩) (B 71107 (by norm_num) ⟨35553, by rfl⟩ (by norm_num))
theorem R94813 : Reach 94813 := rs (se 3 (by rfl) ⟨17777, by rfl⟩) (B 35555 (by norm_num) ⟨17777, by rfl⟩ (by norm_num))
theorem R94817 : Reach 94817 := rs (se 2 (by rfl) ⟨35556, by rfl⟩) (B 71113 (by norm_num) ⟨35556, by rfl⟩ (by norm_num))
theorem R94821 : Reach 94821 := rs (se 4 (by rfl) ⟨8889, by rfl⟩) (B 17779 (by norm_num) ⟨8889, by rfl⟩ (by norm_num))
theorem R94825 : Reach 94825 := rs (se 2 (by rfl) ⟨35559, by rfl⟩) (B 71119 (by norm_num) ⟨35559, by rfl⟩ (by norm_num))
theorem R94829 : Reach 94829 := rs (se 3 (by rfl) ⟨17780, by rfl⟩) (B 35561 (by norm_num) ⟨17780, by rfl⟩ (by norm_num))
theorem R94833 : Reach 94833 := rs (se 2 (by rfl) ⟨35562, by rfl⟩) (B 71125 (by norm_num) ⟨35562, by rfl⟩ (by norm_num))
theorem R94837 : Reach 94837 := rs (se 5 (by rfl) ⟨4445, by rfl⟩) (B 8891 (by norm_num) ⟨4445, by rfl⟩ (by norm_num))
theorem R160373 : Reach 160373 := rs (se 5 (by rfl) ⟨7517, by rfl⟩) (B 15035 (by norm_num) ⟨7517, by rfl⟩ (by norm_num))
theorem R94841 : Reach 94841 := rs (se 2 (by rfl) ⟨35565, by rfl⟩) (B 71131 (by norm_num) ⟨35565, by rfl⟩ (by norm_num))
theorem R94845 : Reach 94845 := rs (se 3 (by rfl) ⟨17783, by rfl⟩) (B 35567 (by norm_num) ⟨17783, by rfl⟩ (by norm_num))
theorem R94849 : Reach 94849 := rs (se 2 (by rfl) ⟨35568, by rfl⟩) (B 71137 (by norm_num) ⟨35568, by rfl⟩ (by norm_num))
theorem R389765 : Reach 389765 := rs (se 4 (by rfl) ⟨36540, by rfl⟩) (B 73081 (by norm_num) ⟨36540, by rfl⟩ (by norm_num))
theorem R94853 : Reach 94853 := rs (se 4 (by rfl) ⟨8892, by rfl⟩) (B 17785 (by norm_num) ⟨8892, by rfl⟩ (by norm_num))
theorem R94857 : Reach 94857 := rs (se 2 (by rfl) ⟨35571, by rfl⟩) (B 71143 (by norm_num) ⟨35571, by rfl⟩ (by norm_num))
theorem R94861 : Reach 94861 := rs (se 3 (by rfl) ⟨17786, by rfl⟩) (B 35573 (by norm_num) ⟨17786, by rfl⟩ (by norm_num))
theorem R94865 : Reach 94865 := rs (se 2 (by rfl) ⟨35574, by rfl⟩) (B 71149 (by norm_num) ⟨35574, by rfl⟩ (by norm_num))
theorem R94869 : Reach 94869 := rs (se 6 (by rfl) ⟨2223, by rfl⟩) (B 4447 (by norm_num) ⟨2223, by rfl⟩ (by norm_num))
theorem R94873 : Reach 94873 := rs (se 2 (by rfl) ⟨35577, by rfl⟩) (B 71155 (by norm_num) ⟨35577, by rfl⟩ (by norm_num))
theorem R94877 : Reach 94877 := rs (se 3 (by rfl) ⟨17789, by rfl⟩) (B 35579 (by norm_num) ⟨17789, by rfl⟩ (by norm_num))
theorem R94881 : Reach 94881 := rs (se 2 (by rfl) ⟨35580, by rfl⟩) (B 71161 (by norm_num) ⟨35580, by rfl⟩ (by norm_num))
theorem R94885 : Reach 94885 := rs (se 4 (by rfl) ⟨8895, by rfl⟩) (B 17791 (by norm_num) ⟨8895, by rfl⟩ (by norm_num))
theorem R94889 : Reach 94889 := rs (se 2 (by rfl) ⟨35583, by rfl⟩) (B 71167 (by norm_num) ⟨35583, by rfl⟩ (by norm_num))
theorem R94893 : Reach 94893 := rs (se 3 (by rfl) ⟨17792, by rfl⟩) (B 35585 (by norm_num) ⟨17792, by rfl⟩ (by norm_num))
theorem R94897 : Reach 94897 := rs (se 2 (by rfl) ⟨35586, by rfl⟩) (B 71173 (by norm_num) ⟨35586, by rfl⟩ (by norm_num))
theorem R94901 : Reach 94901 := rs (se 5 (by rfl) ⟨4448, by rfl⟩) (B 8897 (by norm_num) ⟨4448, by rfl⟩ (by norm_num))
theorem R94905 : Reach 94905 := rs (se 2 (by rfl) ⟨35589, by rfl⟩) (B 71179 (by norm_num) ⟨35589, by rfl⟩ (by norm_num))
theorem R94909 : Reach 94909 := rs (se 3 (by rfl) ⟨17795, by rfl⟩) (B 35591 (by norm_num) ⟨17795, by rfl⟩ (by norm_num))
theorem R94913 : Reach 94913 := rs (se 2 (by rfl) ⟨35592, by rfl⟩) (B 71185 (by norm_num) ⟨35592, by rfl⟩ (by norm_num))
theorem R94917 : Reach 94917 := rs (se 4 (by rfl) ⟨8898, by rfl⟩) (B 17797 (by norm_num) ⟨8898, by rfl⟩ (by norm_num))
theorem R94921 : Reach 94921 := rs (se 2 (by rfl) ⟨35595, by rfl⟩) (B 71191 (by norm_num) ⟨35595, by rfl⟩ (by norm_num))
theorem R94925 : Reach 94925 := rs (se 3 (by rfl) ⟨17798, by rfl⟩) (B 35597 (by norm_num) ⟨17798, by rfl⟩ (by norm_num))
theorem R94929 : Reach 94929 := rs (se 2 (by rfl) ⟨35598, by rfl⟩) (B 71197 (by norm_num) ⟨35598, by rfl⟩ (by norm_num))
theorem R94933 : Reach 94933 := rs (se 7 (by rfl) ⟨1112, by rfl⟩) (B 2225 (by norm_num) ⟨1112, by rfl⟩ (by norm_num))
theorem R94937 : Reach 94937 := rs (se 2 (by rfl) ⟨35601, by rfl⟩) (B 71203 (by norm_num) ⟨35601, by rfl⟩ (by norm_num))
theorem R94941 : Reach 94941 := rs (se 3 (by rfl) ⟨17801, by rfl⟩) (B 35603 (by norm_num) ⟨17801, by rfl⟩ (by norm_num))
theorem R94945 : Reach 94945 := rs (se 2 (by rfl) ⟨35604, by rfl⟩) (B 71209 (by norm_num) ⟨35604, by rfl⟩ (by norm_num))
theorem R94949 : Reach 94949 := rs (se 4 (by rfl) ⟨8901, by rfl⟩) (B 17803 (by norm_num) ⟨8901, by rfl⟩ (by norm_num))
theorem R94953 : Reach 94953 := rs (se 2 (by rfl) ⟨35607, by rfl⟩) (B 71215 (by norm_num) ⟨35607, by rfl⟩ (by norm_num))
theorem R94957 : Reach 94957 := rs (se 3 (by rfl) ⟨17804, by rfl⟩) (B 35609 (by norm_num) ⟨17804, by rfl⟩ (by norm_num))
theorem R94961 : Reach 94961 := rs (se 2 (by rfl) ⟨35610, by rfl⟩) (B 71221 (by norm_num) ⟨35610, by rfl⟩ (by norm_num))
theorem R94965 : Reach 94965 := rs (se 5 (by rfl) ⟨4451, by rfl⟩) (B 8903 (by norm_num) ⟨4451, by rfl⟩ (by norm_num))
theorem R160501 : Reach 160501 := rs (se 5 (by rfl) ⟨7523, by rfl⟩) (B 15047 (by norm_num) ⟨7523, by rfl⟩ (by norm_num))
theorem R94969 : Reach 94969 := rs (se 2 (by rfl) ⟨35613, by rfl⟩) (B 71227 (by norm_num) ⟨35613, by rfl⟩ (by norm_num))
theorem R94973 : Reach 94973 := rs (se 3 (by rfl) ⟨17807, by rfl⟩) (B 35615 (by norm_num) ⟨17807, by rfl⟩ (by norm_num))
theorem R94977 : Reach 94977 := rs (se 2 (by rfl) ⟨35616, by rfl⟩) (B 71233 (by norm_num) ⟨35616, by rfl⟩ (by norm_num))
theorem R94981 : Reach 94981 := rs (se 4 (by rfl) ⟨8904, by rfl⟩) (B 17809 (by norm_num) ⟨8904, by rfl⟩ (by norm_num))
theorem R94985 : Reach 94985 := rs (se 2 (by rfl) ⟨35619, by rfl⟩) (B 71239 (by norm_num) ⟨35619, by rfl⟩ (by norm_num))
theorem R94989 : Reach 94989 := rs (se 3 (by rfl) ⟨17810, by rfl⟩) (B 35621 (by norm_num) ⟨17810, by rfl⟩ (by norm_num))
theorem R94993 : Reach 94993 := rs (se 2 (by rfl) ⟨35622, by rfl⟩) (B 71245 (by norm_num) ⟨35622, by rfl⟩ (by norm_num))
theorem R94997 : Reach 94997 := rs (se 6 (by rfl) ⟨2226, by rfl⟩) (B 4453 (by norm_num) ⟨2226, by rfl⟩ (by norm_num))
theorem R95001 : Reach 95001 := rs (se 2 (by rfl) ⟨35625, by rfl⟩) (B 71251 (by norm_num) ⟨35625, by rfl⟩ (by norm_num))
theorem R95005 : Reach 95005 := rs (se 3 (by rfl) ⟨17813, by rfl⟩) (B 35627 (by norm_num) ⟨17813, by rfl⟩ (by norm_num))
theorem R95009 : Reach 95009 := rs (se 2 (by rfl) ⟨35628, by rfl⟩) (B 71257 (by norm_num) ⟨35628, by rfl⟩ (by norm_num))
theorem R95013 : Reach 95013 := rs (se 4 (by rfl) ⟨8907, by rfl⟩) (B 17815 (by norm_num) ⟨8907, by rfl⟩ (by norm_num))
theorem R95017 : Reach 95017 := rs (se 2 (by rfl) ⟨35631, by rfl⟩) (B 71263 (by norm_num) ⟨35631, by rfl⟩ (by norm_num))
theorem R95021 : Reach 95021 := rs (se 3 (by rfl) ⟨17816, by rfl⟩) (B 35633 (by norm_num) ⟨17816, by rfl⟩ (by norm_num))
theorem R95025 : Reach 95025 := rs (se 2 (by rfl) ⟨35634, by rfl⟩) (B 71269 (by norm_num) ⟨35634, by rfl⟩ (by norm_num))
theorem R95029 : Reach 95029 := rs (se 5 (by rfl) ⟨4454, by rfl⟩) (B 8909 (by norm_num) ⟨4454, by rfl⟩ (by norm_num))
theorem R95033 : Reach 95033 := rs (se 2 (by rfl) ⟨35637, by rfl⟩) (B 71275 (by norm_num) ⟨35637, by rfl⟩ (by norm_num))
theorem R95037 : Reach 95037 := rs (se 3 (by rfl) ⟨17819, by rfl⟩) (B 35639 (by norm_num) ⟨17819, by rfl⟩ (by norm_num))
theorem R95041 : Reach 95041 := rs (se 2 (by rfl) ⟨35640, by rfl⟩) (B 71281 (by norm_num) ⟨35640, by rfl⟩ (by norm_num))
theorem R95045 : Reach 95045 := rs (se 4 (by rfl) ⟨8910, by rfl⟩) (B 17821 (by norm_num) ⟨8910, by rfl⟩ (by norm_num))
theorem R95049 : Reach 95049 := rs (se 2 (by rfl) ⟨35643, by rfl⟩) (B 71287 (by norm_num) ⟨35643, by rfl⟩ (by norm_num))
theorem R95053 : Reach 95053 := rs (se 3 (by rfl) ⟨17822, by rfl⟩) (B 35645 (by norm_num) ⟨17822, by rfl⟩ (by norm_num))
theorem R95057 : Reach 95057 := rs (se 2 (by rfl) ⟨35646, by rfl⟩) (B 71293 (by norm_num) ⟨35646, by rfl⟩ (by norm_num))
theorem R95061 : Reach 95061 := rs (se 9 (by rfl) ⟨278, by rfl⟩) (B 557 (by norm_num) ⟨278, by rfl⟩ (by norm_num))
theorem R95065 : Reach 95065 := rs (se 2 (by rfl) ⟨35649, by rfl⟩) (B 71299 (by norm_num) ⟨35649, by rfl⟩ (by norm_num))
theorem R95069 : Reach 95069 := rs (se 3 (by rfl) ⟨17825, by rfl⟩) (B 35651 (by norm_num) ⟨17825, by rfl⟩ (by norm_num))
theorem R95073 : Reach 95073 := rs (se 2 (by rfl) ⟨35652, by rfl⟩) (B 71305 (by norm_num) ⟨35652, by rfl⟩ (by norm_num))
theorem R95077 : Reach 95077 := rs (se 4 (by rfl) ⟨8913, by rfl⟩) (B 17827 (by norm_num) ⟨8913, by rfl⟩ (by norm_num))
theorem R95081 : Reach 95081 := rs (se 2 (by rfl) ⟨35655, by rfl⟩) (B 71311 (by norm_num) ⟨35655, by rfl⟩ (by norm_num))
theorem R95085 : Reach 95085 := rs (se 3 (by rfl) ⟨17828, by rfl⟩) (B 35657 (by norm_num) ⟨17828, by rfl⟩ (by norm_num))
theorem R95089 : Reach 95089 := rs (se 2 (by rfl) ⟨35658, by rfl⟩) (B 71317 (by norm_num) ⟨35658, by rfl⟩ (by norm_num))
theorem R390005 : Reach 390005 := rs (se 5 (by rfl) ⟨18281, by rfl⟩) (B 36563 (by norm_num) ⟨18281, by rfl⟩ (by norm_num))
theorem R95093 : Reach 95093 := rs (se 5 (by rfl) ⟨4457, by rfl⟩) (B 8915 (by norm_num) ⟨4457, by rfl⟩ (by norm_num))
theorem R95097 : Reach 95097 := rs (se 2 (by rfl) ⟨35661, by rfl⟩) (B 71323 (by norm_num) ⟨35661, by rfl⟩ (by norm_num))
theorem R95101 : Reach 95101 := rs (se 3 (by rfl) ⟨17831, by rfl⟩) (B 35663 (by norm_num) ⟨17831, by rfl⟩ (by norm_num))
theorem R95105 : Reach 95105 := rs (se 2 (by rfl) ⟨35664, by rfl⟩) (B 71329 (by norm_num) ⟨35664, by rfl⟩ (by norm_num))
theorem R95109 : Reach 95109 := rs (se 4 (by rfl) ⟨8916, by rfl⟩) (B 17833 (by norm_num) ⟨8916, by rfl⟩ (by norm_num))
theorem R95113 : Reach 95113 := rs (se 2 (by rfl) ⟨35667, by rfl⟩) (B 71335 (by norm_num) ⟨35667, by rfl⟩ (by norm_num))
theorem R95117 : Reach 95117 := rs (se 3 (by rfl) ⟨17834, by rfl⟩) (B 35669 (by norm_num) ⟨17834, by rfl⟩ (by norm_num))
theorem R95121 : Reach 95121 := rs (se 2 (by rfl) ⟨35670, by rfl⟩) (B 71341 (by norm_num) ⟨35670, by rfl⟩ (by norm_num))
theorem R95125 : Reach 95125 := rs (se 6 (by rfl) ⟨2229, by rfl⟩) (B 4459 (by norm_num) ⟨2229, by rfl⟩ (by norm_num))
theorem R95129 : Reach 95129 := rs (se 2 (by rfl) ⟨35673, by rfl⟩) (B 71347 (by norm_num) ⟨35673, by rfl⟩ (by norm_num))
theorem R357317 : Reach 357317 := rs (se 4 (by rfl) ⟨33498, by rfl⟩) (B 66997 (by norm_num) ⟨33498, by rfl⟩ (by norm_num))
theorem R226373 : Reach 226373 := rs (se 4 (by rfl) ⟨21222, by rfl⟩) (B 42445 (by norm_num) ⟨21222, by rfl⟩ (by norm_num))
theorem R1766549 : Reach 1766549 := rs (se 6 (by rfl) ⟨41403, by rfl⟩) (B 82807 (by norm_num) ⟨41403, by rfl⟩ (by norm_num))
theorem R95429 : Reach 95429 := rs (se 4 (by rfl) ⟨8946, by rfl⟩) (B 17893 (by norm_num) ⟨8946, by rfl⟩ (by norm_num))
theorem R357605 : Reach 357605 := rs (se 4 (by rfl) ⟨33525, by rfl⟩) (B 67051 (by norm_num) ⟨33525, by rfl⟩ (by norm_num))
theorem R128245 : Reach 128245 := rs (se 5 (by rfl) ⟨6011, by rfl⟩) (B 12023 (by norm_num) ⟨6011, by rfl⟩ (by norm_num))
theorem R292261 : Reach 292261 := rs (se 4 (by rfl) ⟨27399, by rfl⟩) (B 54799 (by norm_num) ⟨27399, by rfl⟩ (by norm_num))
theorem R95689 : Reach 95689 := rs (se 2 (by rfl) ⟨35883, by rfl⟩) (B 71767 (by norm_num) ⟨35883, by rfl⟩ (by norm_num))
theorem R128461 : Reach 128461 := rs (se 3 (by rfl) ⟨24086, by rfl⟩) (B 48173 (by norm_num) ⟨24086, by rfl⟩ (by norm_num))
theorem R3503573 : Reach 3503573 := rs (se 7 (by rfl) ⟨41057, by rfl⟩) (B 82115 (by norm_num) ⟨41057, by rfl⟩ (by norm_num))
theorem R1799765 : Reach 1799765 := rs (se 8 (by rfl) ⟨10545, by rfl⟩) (B 21091 (by norm_num) ⟨10545, by rfl⟩ (by norm_num))
theorem R259781 : Reach 259781 := rs (se 4 (by rfl) ⟨24354, by rfl⟩) (B 48709 (by norm_num) ⟨24354, by rfl⟩ (by norm_num))
theorem R95989 : Reach 95989 := rs (se 5 (by rfl) ⟨4499, by rfl⟩) (B 8999 (by norm_num) ⟨4499, by rfl⟩ (by norm_num))
theorem R96005 : Reach 96005 := rs (se 4 (by rfl) ⟨9000, by rfl⟩) (B 18001 (by norm_num) ⟨9000, by rfl⟩ (by norm_num))
theorem R292709 : Reach 292709 := rs (se 4 (by rfl) ⟨27441, by rfl⟩) (B 54883 (by norm_num) ⟨27441, by rfl⟩ (by norm_num))
theorem R260117 : Reach 260117 := rs (se 6 (by rfl) ⟨6096, by rfl⟩) (B 12193 (by norm_num) ⟨6096, by rfl⟩ (by norm_num))
theorem R227701 : Reach 227701 := rs (se 5 (by rfl) ⟨10673, by rfl⟩) (B 21347 (by norm_num) ⟨10673, by rfl⟩ (by norm_num))
theorem R358789 : Reach 358789 := rs (se 4 (by rfl) ⟨33636, by rfl⟩) (B 67273 (by norm_num) ⟨33636, by rfl⟩ (by norm_num))
theorem R195053 : Reach 195053 := rs (se 3 (by rfl) ⟨36572, by rfl⟩) (B 73145 (by norm_num) ⟨36572, by rfl⟩ (by norm_num))
theorem R359093 : Reach 359093 := rs (se 5 (by rfl) ⟨16832, by rfl⟩) (B 33665 (by norm_num) ⟨16832, by rfl⟩ (by norm_num))
theorem R129757 : Reach 129757 := rs (se 3 (by rfl) ⟨24329, by rfl⟩) (B 48659 (by norm_num) ⟨24329, by rfl⟩ (by norm_num))
theorem R195293 : Reach 195293 := rs (se 3 (by rfl) ⟨36617, by rfl⟩) (B 73235 (by norm_num) ⟨36617, by rfl⟩ (by norm_num))
theorem R129853 : Reach 129853 := rs (se 3 (by rfl) ⟨24347, by rfl⟩) (B 48695 (by norm_num) ⟨24347, by rfl⟩ (by norm_num))
theorem R719765 : Reach 719765 := rs (se 6 (by rfl) ⟨16869, by rfl⟩) (B 33739 (by norm_num) ⟨16869, by rfl⟩ (by norm_num))
theorem R228413 : Reach 228413 := rs (se 3 (by rfl) ⟨42827, by rfl⟩) (B 85655 (by norm_num) ⟨42827, by rfl⟩ (by norm_num))
theorem R97373 : Reach 97373 := rs (se 3 (by rfl) ⟨18257, by rfl⟩) (B 36515 (by norm_num) ⟨18257, by rfl⟩ (by norm_num))
theorem R392293 : Reach 392293 := rs (se 4 (by rfl) ⟨36777, by rfl⟩) (B 73555 (by norm_num) ⟨36777, by rfl⟩ (by norm_num))
theorem R261301 : Reach 261301 := rs (se 5 (by rfl) ⟨12248, by rfl⟩) (B 24497 (by norm_num) ⟨12248, by rfl⟩ (by norm_num))
theorem R195797 : Reach 195797 := rs (se 7 (by rfl) ⟨2294, by rfl⟩) (B 4589 (by norm_num) ⟨2294, by rfl⟩ (by norm_num))
theorem R195805 : Reach 195805 := rs (se 3 (by rfl) ⟨36713, by rfl⟩) (B 73427 (by norm_num) ⟨36713, by rfl⟩ (by norm_num))
theorem R97561 : Reach 97561 := rs (se 2 (by rfl) ⟨36585, by rfl⟩) (B 73171 (by norm_num) ⟨36585, by rfl⟩ (by norm_num))
theorem R130349 : Reach 130349 := rs (se 3 (by rfl) ⟨24440, by rfl⟩) (B 48881 (by norm_num) ⟨24440, by rfl⟩ (by norm_num))
theorem R261461 : Reach 261461 := rs (se 11 (by rfl) ⟨191, by rfl⟩) (B 383 (by norm_num) ⟨191, by rfl⟩ (by norm_num))
theorem R261701 : Reach 261701 := rs (se 4 (by rfl) ⟨24534, by rfl⟩) (B 49069 (by norm_num) ⟨24534, by rfl⟩ (by norm_num))
theorem R261893 : Reach 261893 := rs (se 4 (by rfl) ⟨24552, by rfl⟩) (B 49105 (by norm_num) ⟨24552, by rfl⟩ (by norm_num))
theorem R491285 : Reach 491285 := rs (se 6 (by rfl) ⟨11514, by rfl⟩) (B 23029 (by norm_num) ⟨11514, by rfl⟩ (by norm_num))
theorem R130901 : Reach 130901 := rs (se 9 (by rfl) ⟨383, by rfl⟩) (B 767 (by norm_num) ⟨383, by rfl⟩ (by norm_num))
theorem R196625 : Reach 196625 := rs (se 2 (by rfl) ⟨73734, by rfl⟩) R147469
theorem R196643 : Reach 196643 := rs (se 1 (by rfl) ⟨147482, by rfl⟩) R294965
theorem R262349 : Reach 262349 := rs (se 3 (by rfl) ⟨49190, by rfl⟩) R98381
theorem R524515 : Reach 524515 := rs (se 1 (by rfl) ⟨393386, by rfl⟩) R786773
theorem R295235 : Reach 295235 := rs (se 1 (by rfl) ⟨221426, by rfl⟩) R442853
theorem R262531 : Reach 262531 := rs (se 1 (by rfl) ⟨196898, by rfl⟩) R393797
theorem R262577 : Reach 262577 := rs (se 2 (by rfl) ⟨98466, by rfl⟩) R196933
theorem R131539 : Reach 131539 := rs (se 1 (by rfl) ⟨98654, by rfl⟩) R197309
theorem R361037 : Reach 361037 := rs (se 3 (by rfl) ⟨67694, by rfl⟩) R135389
theorem R525041 : Reach 525041 := rs (se 2 (by rfl) ⟨196890, by rfl⟩) R393781
theorem R197873 : Reach 197873 := rs (se 2 (by rfl) ⟨74202, by rfl⟩) R148405
theorem R99731 : Reach 99731 := rs (se 1 (by rfl) ⟨74798, by rfl⟩) R149597
theorem R394723 : Reach 394723 := rs (se 1 (by rfl) ⟨296042, by rfl⟩) R592085
theorem R132673 : Reach 132673 := rs (se 2 (by rfl) ⟨49752, by rfl⟩) R99505
theorem R132769 : Reach 132769 := rs (se 2 (by rfl) ⟨49788, by rfl⟩) R99577
theorem R264035 : Reach 264035 := rs (se 1 (by rfl) ⟨198026, by rfl⟩) R396053
theorem R853901 : Reach 853901 := rs (se 3 (by rfl) ⟨160106, by rfl⟩) R320213
theorem R231569 : Reach 231569 := rs (se 2 (by rfl) ⟨86838, by rfl⟩) R173677
theorem R133265 : Reach 133265 := rs (se 2 (by rfl) ⟨49974, by rfl⟩) R99949
theorem R526499 : Reach 526499 := rs (se 1 (by rfl) ⟨394874, by rfl⟩) R789749
theorem R231619 : Reach 231619 := rs (se 1 (by rfl) ⟨173714, by rfl⟩) R347429
theorem R362765 : Reach 362765 := rs (se 3 (by rfl) ⟨68018, by rfl⟩) R136037
theorem R231761 : Reach 231761 := rs (se 2 (by rfl) ⟨86910, by rfl⟩) R173821
theorem R297425 : Reach 297425 := rs (se 2 (by rfl) ⟨111534, by rfl⟩) R223069
theorem R297553 : Reach 297553 := rs (se 2 (by rfl) ⟨111582, by rfl⟩) R223165
theorem R166531 : Reach 166531 := rs (se 1 (by rfl) ⟨124898, by rfl⟩) R249797
theorem R625315 : Reach 625315 := rs (se 1 (by rfl) ⟨468986, by rfl⟩) R937973
theorem R199427 : Reach 199427 := rs (se 1 (by rfl) ⟨149570, by rfl⟩) R299141
theorem R1084229 : Reach 1084229 := rs (se 4 (by rfl) ⟨101646, by rfl⟩) R203293
theorem R297809 : Reach 297809 := rs (se 2 (by rfl) ⟨111678, by rfl⟩) R223357
theorem R134131 : Reach 134131 := rs (se 1 (by rfl) ⟨100598, by rfl⟩) R201197
theorem R265265 : Reach 265265 := rs (se 2 (by rfl) ⟨99474, by rfl⟩) R198949
theorem R134227 : Reach 134227 := rs (se 1 (by rfl) ⟨100670, by rfl⟩) R201341
theorem R396515 : Reach 396515 := rs (se 1 (by rfl) ⟨297386, by rfl⟩) R594773
theorem R331057 : Reach 331057 := rs (se 2 (by rfl) ⟨124146, by rfl⟩) R248293
theorem R232753 : Reach 232753 := rs (se 2 (by rfl) ⟨87282, by rfl⟩) R174565
theorem R233027 : Reach 233027 := rs (se 1 (by rfl) ⟨174770, by rfl⟩) R349541
theorem R134723 : Reach 134723 := rs (se 1 (by rfl) ⟨101042, by rfl⟩) R202085
theorem R233219 : Reach 233219 := rs (se 1 (by rfl) ⟨174914, by rfl⟩) R349829
theorem R593669 : Reach 593669 := rs (se 4 (by rfl) ⟨55656, by rfl⟩) R111313
theorem R102227 : Reach 102227 := rs (se 1 (by rfl) ⟨76670, by rfl⟩) R153341
theorem R462833 : Reach 462833 := rs (se 2 (by rfl) ⟨173562, by rfl⟩) R347125
theorem R528389 : Reach 528389 := rs (se 4 (by rfl) ⟨49536, by rfl⟩) R99073
theorem R135361 : Reach 135361 := rs (se 2 (by rfl) ⟨50760, by rfl⟩) R101521
theorem R102595 : Reach 102595 := rs (se 1 (by rfl) ⟨76946, by rfl⟩) R153893
theorem R692549 : Reach 692549 := rs (se 4 (by rfl) ⟨64926, by rfl⟩) R129853
theorem R102739 : Reach 102739 := rs (se 1 (by rfl) ⟨77054, by rfl⟩) R154109
theorem R856433 : Reach 856433 := rs (se 2 (by rfl) ⟨321162, by rfl⟩) R642325
theorem R102883 : Reach 102883 := rs (se 1 (by rfl) ⟨77162, by rfl⟩) R154325
theorem R266723 : Reach 266723 := rs (se 1 (by rfl) ⟨200042, by rfl⟩) R400085
theorem R299501 : Reach 299501 := rs (se 3 (by rfl) ⟨56156, by rfl⟩) R112313
theorem R692749 : Reach 692749 := rs (se 3 (by rfl) ⟨129890, by rfl⟩) R259781
theorem R103027 : Reach 103027 := rs (se 1 (by rfl) ⟨77270, by rfl⟩) R154541
theorem R234161 : Reach 234161 := rs (se 2 (by rfl) ⟨87810, by rfl⟩) R175621
theorem R234211 : Reach 234211 := rs (se 1 (by rfl) ⟨175658, by rfl⟩) R351317
theorem R201457 : Reach 201457 := rs (se 2 (by rfl) ⟨75546, by rfl⟩) R151093
theorem R103171 : Reach 103171 := rs (se 1 (by rfl) ⟨77378, by rfl⟩) R154757
theorem R299825 : Reach 299825 := rs (se 2 (by rfl) ⟨112434, by rfl⟩) R224869
theorem R234353 : Reach 234353 := rs (se 2 (by rfl) ⟨87882, by rfl⟩) R175765
theorem R103315 : Reach 103315 := rs (se 1 (by rfl) ⟨77486, by rfl⟩) R154973
theorem R201649 : Reach 201649 := rs (se 2 (by rfl) ⟨75618, by rfl⟩) R151237
theorem R103459 : Reach 103459 := rs (se 1 (by rfl) ⟨77594, by rfl⟩) R155189
theorem R234659 : Reach 234659 := rs (se 1 (by rfl) ⟨175994, by rfl⟩) R351989
theorem R398513 : Reach 398513 := rs (se 2 (by rfl) ⟨149442, by rfl⟩) R298885
theorem R103603 : Reach 103603 := rs (se 1 (by rfl) ⟨77702, by rfl⟩) R155405
theorem R300269 : Reach 300269 := rs (se 3 (by rfl) ⟨56300, by rfl⟩) R112601
theorem R169219 : Reach 169219 := rs (se 1 (by rfl) ⟨126914, by rfl⟩) R253829
theorem R267533 : Reach 267533 := rs (se 3 (by rfl) ⟨50162, by rfl⟩) R100325
theorem R103747 : Reach 103747 := rs (se 1 (by rfl) ⟨77810, by rfl⟩) R155621
theorem R464291 : Reach 464291 := rs (se 1 (by rfl) ⟨348218, by rfl⟩) R696437
theorem R1054133 : Reach 1054133 := rs (se 5 (by rfl) ⟨49412, by rfl⟩) R98825
theorem R267725 : Reach 267725 := rs (se 3 (by rfl) ⟨50198, by rfl⟩) R100397
theorem R103891 : Reach 103891 := rs (se 1 (by rfl) ⟨77918, by rfl⟩) R155837
theorem R136721 : Reach 136721 := rs (se 2 (by rfl) ⟨51270, by rfl⟩) R102541
theorem R136739 : Reach 136739 := rs (se 1 (by rfl) ⟨102554, by rfl⟩) R205109
theorem R136769 : Reach 136769 := rs (se 2 (by rfl) ⟨51288, by rfl⟩) R102577
theorem R136787 : Reach 136787 := rs (se 1 (by rfl) ⟨102590, by rfl⟩) R205181
theorem R104035 : Reach 104035 := rs (se 1 (by rfl) ⟨78026, by rfl⟩) R156053
theorem R136817 : Reach 136817 := rs (se 2 (by rfl) ⟨51306, by rfl⟩) R102613
theorem R136835 : Reach 136835 := rs (se 1 (by rfl) ⟨102626, by rfl⟩) R205253
theorem R136865 : Reach 136865 := rs (se 2 (by rfl) ⟨51324, by rfl⟩) R102649
theorem R136883 : Reach 136883 := rs (se 1 (by rfl) ⟨102662, by rfl⟩) R205325
theorem R136913 : Reach 136913 := rs (se 2 (by rfl) ⟨51342, by rfl⟩) R102685
theorem R136931 : Reach 136931 := rs (se 1 (by rfl) ⟨102698, by rfl⟩) R205397
theorem R300781 : Reach 300781 := rs (se 3 (by rfl) ⟨56396, by rfl⟩) R112793
theorem R104179 : Reach 104179 := rs (se 1 (by rfl) ⟨78134, by rfl⟩) R156269
theorem R136961 : Reach 136961 := rs (se 2 (by rfl) ⟨51360, by rfl⟩) R102721
theorem R136979 : Reach 136979 := rs (se 1 (by rfl) ⟨102734, by rfl⟩) R205469
theorem R137009 : Reach 137009 := rs (se 2 (by rfl) ⟨51378, by rfl⟩) R102757
theorem R137027 : Reach 137027 := rs (se 1 (by rfl) ⟨102770, by rfl⟩) R205541
theorem R235345 : Reach 235345 := rs (se 2 (by rfl) ⟨88254, by rfl⟩) R176509
theorem R137057 : Reach 137057 := rs (se 2 (by rfl) ⟨51396, by rfl⟩) R102793
theorem R137075 : Reach 137075 := rs (se 1 (by rfl) ⟨102806, by rfl⟩) R205613
theorem R104323 : Reach 104323 := rs (se 1 (by rfl) ⟨78242, by rfl⟩) R156485
theorem R137105 : Reach 137105 := rs (se 2 (by rfl) ⟨51414, by rfl⟩) R102829
theorem R137123 : Reach 137123 := rs (se 1 (by rfl) ⟨102842, by rfl⟩) R205685
theorem R137153 : Reach 137153 := rs (se 2 (by rfl) ⟨51432, by rfl⟩) R102865
theorem R137171 : Reach 137171 := rs (se 1 (by rfl) ⟨102878, by rfl⟩) R205757
theorem R137201 : Reach 137201 := rs (se 2 (by rfl) ⟨51450, by rfl⟩) R102901
theorem R137219 : Reach 137219 := rs (se 1 (by rfl) ⟨102914, by rfl⟩) R205829
theorem R104467 : Reach 104467 := rs (se 1 (by rfl) ⟨78350, by rfl⟩) R156701
theorem R137249 : Reach 137249 := rs (se 2 (by rfl) ⟨51468, by rfl⟩) R102937
theorem R137267 : Reach 137267 := rs (se 1 (by rfl) ⟨102950, by rfl⟩) R205901
theorem R399437 : Reach 399437 := rs (se 3 (by rfl) ⟨74894, by rfl⟩) R149789
theorem R137297 : Reach 137297 := rs (se 2 (by rfl) ⟨51486, by rfl⟩) R102973
theorem R137315 : Reach 137315 := rs (se 1 (by rfl) ⟨102986, by rfl⟩) R205973
theorem R235619 : Reach 235619 := rs (se 1 (by rfl) ⟨176714, by rfl⟩) R353429
theorem R137345 : Reach 137345 := rs (se 2 (by rfl) ⟨51504, by rfl⟩) R103009
theorem R2398349 : Reach 2398349 := rs (se 3 (by rfl) ⟨449690, by rfl⟩) R899381
theorem R137363 : Reach 137363 := rs (se 1 (by rfl) ⟨103022, by rfl⟩) R206045
theorem R104611 : Reach 104611 := rs (se 1 (by rfl) ⟨78458, by rfl⟩) R156917
theorem R268451 : Reach 268451 := rs (se 1 (by rfl) ⟨201338, by rfl⟩) R402677
theorem R137393 : Reach 137393 := rs (se 2 (by rfl) ⟨51522, by rfl⟩) R103045
theorem R137411 : Reach 137411 := rs (se 1 (by rfl) ⟨103058, by rfl⟩) R206117
theorem R465101 : Reach 465101 := rs (se 3 (by rfl) ⟨87206, by rfl⟩) R174413
theorem R137441 : Reach 137441 := rs (se 2 (by rfl) ⟨51540, by rfl⟩) R103081
theorem R399587 : Reach 399587 := rs (se 1 (by rfl) ⟨299690, by rfl⟩) R599381
theorem R301283 : Reach 301283 := rs (se 1 (by rfl) ⟨225962, by rfl⟩) R451925
theorem R137459 : Reach 137459 := rs (se 1 (by rfl) ⟨103094, by rfl⟩) R206189
theorem R137489 : Reach 137489 := rs (se 2 (by rfl) ⟨51558, by rfl⟩) R103117
theorem R137507 : Reach 137507 := rs (se 1 (by rfl) ⟨103130, by rfl⟩) R206261
theorem R235811 : Reach 235811 := rs (se 1 (by rfl) ⟨176858, by rfl⟩) R353717
theorem R104755 : Reach 104755 := rs (se 1 (by rfl) ⟨78566, by rfl⟩) R157133
theorem R137537 : Reach 137537 := rs (se 2 (by rfl) ⟨51576, by rfl⟩) R103153
theorem R137555 : Reach 137555 := rs (se 1 (by rfl) ⟨103166, by rfl⟩) R206333
theorem R137585 : Reach 137585 := rs (se 2 (by rfl) ⟨51594, by rfl⟩) R103189
theorem R137603 : Reach 137603 := rs (se 1 (by rfl) ⟨103202, by rfl⟩) R206405
theorem R137633 : Reach 137633 := rs (se 2 (by rfl) ⟨51612, by rfl⟩) R103225
theorem R268717 : Reach 268717 := rs (se 3 (by rfl) ⟨50384, by rfl⟩) R100769
theorem R137651 : Reach 137651 := rs (se 1 (by rfl) ⟨103238, by rfl⟩) R206477
theorem R104899 : Reach 104899 := rs (se 1 (by rfl) ⟨78674, by rfl⟩) R157349
theorem R137681 : Reach 137681 := rs (se 2 (by rfl) ⟨51630, by rfl⟩) R103261
theorem R137699 : Reach 137699 := rs (se 1 (by rfl) ⟨103274, by rfl⟩) R206549
theorem R137729 : Reach 137729 := rs (se 2 (by rfl) ⟨51648, by rfl⟩) R103297
theorem R137747 : Reach 137747 := rs (se 1 (by rfl) ⟨103310, by rfl⟩) R206621
theorem R137777 : Reach 137777 := rs (se 2 (by rfl) ⟨51666, by rfl⟩) R103333
theorem R137795 : Reach 137795 := rs (se 1 (by rfl) ⟨103346, by rfl⟩) R206693
theorem R105043 : Reach 105043 := rs (se 1 (by rfl) ⟨78782, by rfl⟩) R157565
theorem R137825 : Reach 137825 := rs (se 2 (by rfl) ⟨51684, by rfl⟩) R103369
theorem R137843 : Reach 137843 := rs (se 1 (by rfl) ⟨103382, by rfl⟩) R206765
theorem R137873 : Reach 137873 := rs (se 2 (by rfl) ⟨51702, by rfl⟩) R103405
theorem R137891 : Reach 137891 := rs (se 1 (by rfl) ⟨103418, by rfl⟩) R206837
theorem R137921 : Reach 137921 := rs (se 2 (by rfl) ⟨51720, by rfl⟩) R103441
theorem R137939 : Reach 137939 := rs (se 1 (by rfl) ⟨103454, by rfl⟩) R206909
theorem R105187 : Reach 105187 := rs (se 1 (by rfl) ⟨78890, by rfl⟩) R157781
theorem R137969 : Reach 137969 := rs (se 2 (by rfl) ⟨51738, by rfl⟩) R103477
theorem R137987 : Reach 137987 := rs (se 1 (by rfl) ⟨103490, by rfl⟩) R206981
theorem R138017 : Reach 138017 := rs (se 2 (by rfl) ⟨51756, by rfl⟩) R103513
theorem R138035 : Reach 138035 := rs (se 1 (by rfl) ⟨103526, by rfl⟩) R207053
theorem R138065 : Reach 138065 := rs (se 2 (by rfl) ⟨51774, by rfl⟩) R103549
theorem R138083 : Reach 138083 := rs (se 1 (by rfl) ⟨103562, by rfl⟩) R207125
theorem R105331 : Reach 105331 := rs (se 1 (by rfl) ⟨78998, by rfl⟩) R157997
theorem R138113 : Reach 138113 := rs (se 2 (by rfl) ⟨51792, by rfl⟩) R103585
theorem R138131 : Reach 138131 := rs (se 1 (by rfl) ⟨103598, by rfl⟩) R207197
theorem R138161 : Reach 138161 := rs (se 2 (by rfl) ⟨51810, by rfl⟩) R103621
theorem R138179 : Reach 138179 := rs (se 1 (by rfl) ⟨103634, by rfl⟩) R207269
theorem R138209 : Reach 138209 := rs (se 2 (by rfl) ⟨51828, by rfl⟩) R103657
theorem R170993 : Reach 170993 := rs (se 2 (by rfl) ⟨64122, by rfl⟩) R128245
theorem R138227 : Reach 138227 := rs (se 1 (by rfl) ⟨103670, by rfl⟩) R207341
theorem R105475 : Reach 105475 := rs (se 1 (by rfl) ⟨79106, by rfl⟩) R158213
theorem R138257 : Reach 138257 := rs (se 2 (by rfl) ⟨51846, by rfl⟩) R103693
theorem R138275 : Reach 138275 := rs (se 1 (by rfl) ⟨103706, by rfl⟩) R207413
theorem R269347 : Reach 269347 := rs (se 1 (by rfl) ⟨202010, by rfl⟩) R404021
theorem R1317941 : Reach 1317941 := rs (se 5 (by rfl) ⟨61778, by rfl⟩) R123557
theorem R138305 : Reach 138305 := rs (se 2 (by rfl) ⟨51864, by rfl⟩) R103729
theorem R138323 : Reach 138323 := rs (se 1 (by rfl) ⟨103742, by rfl⟩) R207485
theorem R138353 : Reach 138353 := rs (se 2 (by rfl) ⟨51882, by rfl⟩) R103765
theorem R138371 : Reach 138371 := rs (se 1 (by rfl) ⟨103778, by rfl⟩) R207557
theorem R105619 : Reach 105619 := rs (se 1 (by rfl) ⟨79214, by rfl⟩) R158429
theorem R138401 : Reach 138401 := rs (se 2 (by rfl) ⟨51900, by rfl⟩) R103801
theorem R138419 : Reach 138419 := rs (se 1 (by rfl) ⟨103814, by rfl⟩) R207629
theorem R236753 : Reach 236753 := rs (se 2 (by rfl) ⟨88782, by rfl⟩) R177565
theorem R138449 : Reach 138449 := rs (se 2 (by rfl) ⟨51918, by rfl⟩) R103837
theorem R138467 : Reach 138467 := rs (se 1 (by rfl) ⟨103850, by rfl⟩) R207701
theorem R597233 : Reach 597233 := rs (se 2 (by rfl) ⟨223962, by rfl⟩) R447925
theorem R138497 : Reach 138497 := rs (se 2 (by rfl) ⟨51936, by rfl⟩) R103873
theorem R236803 : Reach 236803 := rs (se 1 (by rfl) ⟨177602, by rfl⟩) R355205
theorem R171281 : Reach 171281 := rs (se 2 (by rfl) ⟨64230, by rfl⟩) R128461
theorem R138515 : Reach 138515 := rs (se 1 (by rfl) ⟨103886, by rfl⟩) R207773
theorem R105763 : Reach 105763 := rs (se 1 (by rfl) ⟨79322, by rfl⟩) R158645
theorem R138545 : Reach 138545 := rs (se 2 (by rfl) ⟨51954, by rfl⟩) R103909
theorem R138563 : Reach 138563 := rs (se 1 (by rfl) ⟨103922, by rfl⟩) R207845
theorem R138593 : Reach 138593 := rs (se 2 (by rfl) ⟨51972, by rfl⟩) R103945
theorem R138611 : Reach 138611 := rs (se 1 (by rfl) ⟨103958, by rfl⟩) R207917
theorem R138641 : Reach 138641 := rs (se 2 (by rfl) ⟨51990, by rfl⟩) R103981
theorem R236945 : Reach 236945 := rs (se 2 (by rfl) ⟨88854, by rfl⟩) R177709
theorem R138659 : Reach 138659 := rs (se 1 (by rfl) ⟨103994, by rfl⟩) R207989
theorem R105907 : Reach 105907 := rs (se 1 (by rfl) ⟨79430, by rfl⟩) R158861
theorem R138689 : Reach 138689 := rs (se 2 (by rfl) ⟨52008, by rfl⟩) R104017
theorem R138707 : Reach 138707 := rs (se 1 (by rfl) ⟨104030, by rfl⟩) R208061
theorem R138737 : Reach 138737 := rs (se 2 (by rfl) ⟨52026, by rfl⟩) R104053
theorem R138755 : Reach 138755 := rs (se 1 (by rfl) ⟨104066, by rfl⟩) R208133
theorem R138785 : Reach 138785 := rs (se 2 (by rfl) ⟨52044, by rfl⟩) R104089
theorem R138803 : Reach 138803 := rs (se 1 (by rfl) ⟨104102, by rfl⟩) R208205
theorem R106051 : Reach 106051 := rs (se 1 (by rfl) ⟨79538, by rfl⟩) R159077
theorem R138833 : Reach 138833 := rs (se 2 (by rfl) ⟨52062, by rfl⟩) R104125
theorem R138851 : Reach 138851 := rs (se 1 (by rfl) ⟨104138, by rfl⟩) R208277
theorem R138881 : Reach 138881 := rs (se 2 (by rfl) ⟨52080, by rfl⟩) R104161
theorem R138899 : Reach 138899 := rs (se 1 (by rfl) ⟨104174, by rfl⟩) R208349
theorem R138929 : Reach 138929 := rs (se 2 (by rfl) ⟨52098, by rfl⟩) R104197
theorem R138947 : Reach 138947 := rs (se 1 (by rfl) ⟨104210, by rfl⟩) R208421
theorem R990917 : Reach 990917 := rs (se 4 (by rfl) ⟨92898, by rfl⟩) R185797
theorem R106195 : Reach 106195 := rs (se 1 (by rfl) ⟨79646, by rfl⟩) R159293
theorem R138977 : Reach 138977 := rs (se 2 (by rfl) ⟨52116, by rfl⟩) R104233
theorem R138995 : Reach 138995 := rs (se 1 (by rfl) ⟨104246, by rfl⟩) R208493
theorem R139025 : Reach 139025 := rs (se 2 (by rfl) ⟨52134, by rfl⟩) R104269
theorem R139043 : Reach 139043 := rs (se 1 (by rfl) ⟨104282, by rfl⟩) R208565
theorem R139073 : Reach 139073 := rs (se 2 (by rfl) ⟨52152, by rfl⟩) R104305
theorem R139091 : Reach 139091 := rs (se 1 (by rfl) ⟨104318, by rfl⟩) R208637
theorem R106339 : Reach 106339 := rs (se 1 (by rfl) ⟨79754, by rfl⟩) R159509
theorem R204643 : Reach 204643 := rs (se 1 (by rfl) ⟨153482, by rfl⟩) R306965
theorem R139121 : Reach 139121 := rs (se 2 (by rfl) ⟨52170, by rfl⟩) R104341
theorem R139139 : Reach 139139 := rs (se 1 (by rfl) ⟨104354, by rfl⟩) R208709
theorem R139169 : Reach 139169 := rs (se 2 (by rfl) ⟨52188, by rfl⟩) R104377
theorem R139187 : Reach 139187 := rs (se 1 (by rfl) ⟨104390, by rfl⟩) R208781
theorem R139217 : Reach 139217 := rs (se 2 (by rfl) ⟨52206, by rfl⟩) R104413
theorem R139235 : Reach 139235 := rs (se 1 (by rfl) ⟨104426, by rfl⟩) R208853
theorem R106483 : Reach 106483 := rs (se 1 (by rfl) ⟨79862, by rfl⟩) R159725
theorem R139265 : Reach 139265 := rs (se 2 (by rfl) ⟨52224, by rfl⟩) R104449
theorem R139283 : Reach 139283 := rs (se 1 (by rfl) ⟨104462, by rfl⟩) R208925
theorem R303139 : Reach 303139 := rs (se 1 (by rfl) ⟨227354, by rfl⟩) R454709
theorem R139313 : Reach 139313 := rs (se 2 (by rfl) ⟨52242, by rfl⟩) R104485
theorem R139331 : Reach 139331 := rs (se 1 (by rfl) ⟨104498, by rfl⟩) R208997
theorem R139361 : Reach 139361 := rs (se 2 (by rfl) ⟨52260, by rfl⟩) R104521
theorem R270449 : Reach 270449 := rs (se 2 (by rfl) ⟨101418, by rfl⟩) R202837
theorem R139379 : Reach 139379 := rs (se 1 (by rfl) ⟨104534, by rfl⟩) R209069
theorem R106627 : Reach 106627 := rs (se 1 (by rfl) ⟨79970, by rfl⟩) R159941
theorem R139409 : Reach 139409 := rs (se 2 (by rfl) ⟨52278, by rfl⟩) R104557
theorem R139427 : Reach 139427 := rs (se 1 (by rfl) ⟨104570, by rfl⟩) R209141
theorem R139457 : Reach 139457 := rs (se 2 (by rfl) ⟨52296, by rfl⟩) R104593
theorem R139475 : Reach 139475 := rs (se 1 (by rfl) ⟨104606, by rfl⟩) R209213
theorem R139505 : Reach 139505 := rs (se 2 (by rfl) ⟨52314, by rfl⟩) R104629
theorem R139523 : Reach 139523 := rs (se 1 (by rfl) ⟨104642, by rfl⟩) R209285
theorem R205073 : Reach 205073 := rs (se 2 (by rfl) ⟨76902, by rfl⟩) R153805
theorem R106771 : Reach 106771 := rs (se 1 (by rfl) ⟨80078, by rfl⟩) R160157
theorem R139553 : Reach 139553 := rs (se 2 (by rfl) ⟨52332, by rfl⟩) R104665
theorem R205091 : Reach 205091 := rs (se 1 (by rfl) ⟨153818, by rfl⟩) R307637
theorem R500003 : Reach 500003 := rs (se 1 (by rfl) ⟨375002, by rfl⟩) R750005
theorem R270641 : Reach 270641 := rs (se 2 (by rfl) ⟨101490, by rfl⟩) R202981
theorem R139571 : Reach 139571 := rs (se 1 (by rfl) ⟨104678, by rfl⟩) R209357
theorem R139601 : Reach 139601 := rs (se 2 (by rfl) ⟨52350, by rfl⟩) R104701
theorem R139619 : Reach 139619 := rs (se 1 (by rfl) ⟨104714, by rfl⟩) R209429
theorem R237937 : Reach 237937 := rs (se 2 (by rfl) ⟨89226, by rfl⟩) R178453
theorem R139649 : Reach 139649 := rs (se 2 (by rfl) ⟨52368, by rfl⟩) R104737
theorem R139667 : Reach 139667 := rs (se 1 (by rfl) ⟨104750, by rfl⟩) R209501
theorem R106915 : Reach 106915 := rs (se 1 (by rfl) ⟨80186, by rfl⟩) R160373
theorem R139697 : Reach 139697 := rs (se 2 (by rfl) ⟨52386, by rfl⟩) R104773
theorem R139715 : Reach 139715 := rs (se 1 (by rfl) ⟨104786, by rfl⟩) R209573
theorem R139745 : Reach 139745 := rs (se 2 (by rfl) ⟨52404, by rfl⟩) R104809
theorem R303601 : Reach 303601 := rs (se 2 (by rfl) ⟨113850, by rfl⟩) R227701
theorem R139763 : Reach 139763 := rs (se 1 (by rfl) ⟨104822, by rfl⟩) R209645
theorem R139793 : Reach 139793 := rs (se 2 (by rfl) ⟨52422, by rfl⟩) R104845
theorem R139811 : Reach 139811 := rs (se 1 (by rfl) ⟨104858, by rfl⟩) R209717
theorem R205361 : Reach 205361 := rs (se 2 (by rfl) ⟨77010, by rfl⟩) R154021
theorem R139841 : Reach 139841 := rs (se 2 (by rfl) ⟨52440, by rfl⟩) R104881
theorem R205379 : Reach 205379 := rs (se 1 (by rfl) ⟨154034, by rfl⟩) R308069
theorem R139859 : Reach 139859 := rs (se 1 (by rfl) ⟨104894, by rfl⟩) R209789
theorem R139889 : Reach 139889 := rs (se 2 (by rfl) ⟨52458, by rfl⟩) R104917
theorem R139907 : Reach 139907 := rs (se 1 (by rfl) ⟨104930, by rfl⟩) R209861
theorem R238211 : Reach 238211 := rs (se 1 (by rfl) ⟨178658, by rfl⟩) R357317
theorem R139937 : Reach 139937 := rs (se 2 (by rfl) ⟨52476, by rfl⟩) R104953
theorem R598691 : Reach 598691 := rs (se 1 (by rfl) ⟨449018, by rfl⟩) R898037
theorem R139955 : Reach 139955 := rs (se 1 (by rfl) ⟨104966, by rfl⟩) R209933
theorem R139985 : Reach 139985 := rs (se 2 (by rfl) ⟨52494, by rfl⟩) R104989
theorem R140003 : Reach 140003 := rs (se 1 (by rfl) ⟨105002, by rfl⟩) R210005
theorem R140033 : Reach 140033 := rs (se 2 (by rfl) ⟨52512, by rfl⟩) R105025
theorem R140051 : Reach 140051 := rs (se 1 (by rfl) ⟨105038, by rfl⟩) R210077
theorem R140081 : Reach 140081 := rs (se 2 (by rfl) ⟨52530, by rfl⟩) R105061
theorem R140099 : Reach 140099 := rs (se 1 (by rfl) ⟨105074, by rfl⟩) R210149
theorem R238403 : Reach 238403 := rs (se 1 (by rfl) ⟨178802, by rfl⟩) R357605
theorem R205649 : Reach 205649 := rs (se 2 (by rfl) ⟨77118, by rfl⟩) R154237
theorem R140129 : Reach 140129 := rs (se 2 (by rfl) ⟨52548, by rfl⟩) R105097
theorem R205667 : Reach 205667 := rs (se 1 (by rfl) ⟨154250, by rfl⟩) R308501
theorem R140147 : Reach 140147 := rs (se 1 (by rfl) ⟨105110, by rfl⟩) R210221
theorem R140177 : Reach 140177 := rs (se 2 (by rfl) ⟨52566, by rfl⟩) R105133
theorem R140195 : Reach 140195 := rs (se 1 (by rfl) ⟨105146, by rfl⟩) R210293
theorem R140225 : Reach 140225 := rs (se 2 (by rfl) ⟨52584, by rfl⟩) R105169
theorem R173009 : Reach 173009 := rs (se 2 (by rfl) ⟨64878, by rfl⟩) R129757
theorem R140243 : Reach 140243 := rs (se 1 (by rfl) ⟨105182, by rfl⟩) R210365
theorem R2335715 : Reach 2335715 := rs (se 1 (by rfl) ⟨1751786, by rfl⟩) R3503573
theorem R140273 : Reach 140273 := rs (se 2 (by rfl) ⟨52602, by rfl⟩) R105205
theorem R140291 : Reach 140291 := rs (se 1 (by rfl) ⟨105218, by rfl⟩) R210437
theorem R500741 : Reach 500741 := rs (se 4 (by rfl) ⟨46944, by rfl⟩) R93889
theorem R140321 : Reach 140321 := rs (se 2 (by rfl) ⟨52620, by rfl⟩) R105241
theorem R468017 : Reach 468017 := rs (se 2 (by rfl) ⟨175506, by rfl⟩) R351013
theorem R140339 : Reach 140339 := rs (se 1 (by rfl) ⟨105254, by rfl⟩) R210509
theorem R140369 : Reach 140369 := rs (se 2 (by rfl) ⟨52638, by rfl⟩) R105277
theorem R140387 : Reach 140387 := rs (se 1 (by rfl) ⟨105290, by rfl⟩) R210581
theorem R205937 : Reach 205937 := rs (se 2 (by rfl) ⟨77226, by rfl⟩) R154453
theorem R402545 : Reach 402545 := rs (se 2 (by rfl) ⟨150954, by rfl⟩) R301909
theorem R140417 : Reach 140417 := rs (se 2 (by rfl) ⟨52656, by rfl⟩) R105313
theorem R205955 : Reach 205955 := rs (se 1 (by rfl) ⟨154466, by rfl⟩) R308933
theorem R140435 : Reach 140435 := rs (se 1 (by rfl) ⟨105326, by rfl⟩) R210653
theorem R140465 : Reach 140465 := rs (se 2 (by rfl) ⟨52674, by rfl⟩) R105349
theorem R140483 : Reach 140483 := rs (se 1 (by rfl) ⟨105362, by rfl⟩) R210725
theorem R140513 : Reach 140513 := rs (se 2 (by rfl) ⟨52692, by rfl⟩) R105385
theorem R140531 : Reach 140531 := rs (se 1 (by rfl) ⟨105398, by rfl⟩) R210797
theorem R140561 : Reach 140561 := rs (se 2 (by rfl) ⟨52710, by rfl⟩) R105421
theorem R140579 : Reach 140579 := rs (se 1 (by rfl) ⟨105434, by rfl⟩) R210869
theorem R140609 : Reach 140609 := rs (se 2 (by rfl) ⟨52728, by rfl⟩) R105457
theorem R140627 : Reach 140627 := rs (se 1 (by rfl) ⟨105470, by rfl⟩) R210941
theorem R173411 : Reach 173411 := rs (se 1 (by rfl) ⟨130058, by rfl⟩) R260117
theorem R140657 : Reach 140657 := rs (se 2 (by rfl) ⟨52746, by rfl⟩) R105493
theorem R140675 : Reach 140675 := rs (se 1 (by rfl) ⟨105506, by rfl⟩) R211013
theorem R206225 : Reach 206225 := rs (se 2 (by rfl) ⟨77334, by rfl⟩) R154669
theorem R140705 : Reach 140705 := rs (se 2 (by rfl) ⟨52764, by rfl⟩) R105529
theorem R206243 : Reach 206243 := rs (se 1 (by rfl) ⟨154682, by rfl⟩) R309365
theorem R140723 : Reach 140723 := rs (se 1 (by rfl) ⟨105542, by rfl⟩) R211085
theorem R140753 : Reach 140753 := rs (se 2 (by rfl) ⟨52782, by rfl⟩) R105565
theorem R140771 : Reach 140771 := rs (se 1 (by rfl) ⟨105578, by rfl⟩) R211157
theorem R140801 : Reach 140801 := rs (se 2 (by rfl) ⟨52800, by rfl⟩) R105601
theorem R140819 : Reach 140819 := rs (se 1 (by rfl) ⟨105614, by rfl⟩) R211229
theorem R140849 : Reach 140849 := rs (se 2 (by rfl) ⟨52818, by rfl⟩) R105637
theorem R140867 : Reach 140867 := rs (se 1 (by rfl) ⟨105650, by rfl⟩) R211301
theorem R140897 : Reach 140897 := rs (se 2 (by rfl) ⟨52836, by rfl⟩) R105673
theorem R140915 : Reach 140915 := rs (se 1 (by rfl) ⟨105686, by rfl⟩) R211373
theorem R140945 : Reach 140945 := rs (se 2 (by rfl) ⟨52854, by rfl⟩) R105709
theorem R140963 : Reach 140963 := rs (se 1 (by rfl) ⟨105722, by rfl⟩) R211445
theorem R206513 : Reach 206513 := rs (se 2 (by rfl) ⟨77442, by rfl⟩) R154885
theorem R140993 : Reach 140993 := rs (se 2 (by rfl) ⟨52872, by rfl⟩) R105745
theorem R206531 : Reach 206531 := rs (se 1 (by rfl) ⟨154898, by rfl⟩) R309797
theorem R534221 : Reach 534221 := rs (se 3 (by rfl) ⟨100166, by rfl⟩) R200333
theorem R141011 : Reach 141011 := rs (se 1 (by rfl) ⟨105758, by rfl⟩) R211517
theorem R1124081 : Reach 1124081 := rs (se 2 (by rfl) ⟨421530, by rfl⟩) R843061
theorem R141041 : Reach 141041 := rs (se 2 (by rfl) ⟨52890, by rfl⟩) R105781
theorem R239345 : Reach 239345 := rs (se 2 (by rfl) ⟨89754, by rfl⟩) R179509
theorem R141059 : Reach 141059 := rs (se 1 (by rfl) ⟨105794, by rfl⟩) R211589
theorem R141089 : Reach 141089 := rs (se 2 (by rfl) ⟨52908, by rfl⟩) R105817
theorem R239395 : Reach 239395 := rs (se 1 (by rfl) ⟨179546, by rfl⟩) R359093
theorem R141107 : Reach 141107 := rs (se 1 (by rfl) ⟨105830, by rfl⟩) R211661
theorem R141137 : Reach 141137 := rs (se 2 (by rfl) ⟨52926, by rfl⟩) R105853
theorem R141155 : Reach 141155 := rs (se 1 (by rfl) ⟨105866, by rfl⟩) R211733
theorem R141185 : Reach 141185 := rs (se 2 (by rfl) ⟨52944, by rfl⟩) R105889
theorem R141203 : Reach 141203 := rs (se 1 (by rfl) ⟨105902, by rfl⟩) R211805
theorem R141233 : Reach 141233 := rs (se 2 (by rfl) ⟨52962, by rfl⟩) R105925
theorem R239537 : Reach 239537 := rs (se 2 (by rfl) ⟨89826, by rfl⟩) R179653
theorem R141251 : Reach 141251 := rs (se 1 (by rfl) ⟨105938, by rfl⟩) R211877
theorem R206801 : Reach 206801 := rs (se 2 (by rfl) ⟨77550, by rfl⟩) R155101
theorem R141281 : Reach 141281 := rs (se 2 (by rfl) ⟨52980, by rfl⟩) R105961
theorem R206819 : Reach 206819 := rs (se 1 (by rfl) ⟨155114, by rfl⟩) R310229
theorem R141299 : Reach 141299 := rs (se 1 (by rfl) ⟨105974, by rfl⟩) R211949
theorem R698381 : Reach 698381 := rs (se 3 (by rfl) ⟨130946, by rfl⟩) R261893
theorem R141329 : Reach 141329 := rs (se 2 (by rfl) ⟨52998, by rfl⟩) R105997
theorem R141347 : Reach 141347 := rs (se 1 (by rfl) ⟨106010, by rfl⟩) R212021
theorem R141377 : Reach 141377 := rs (se 2 (by rfl) ⟨53016, by rfl⟩) R106033
theorem R141395 : Reach 141395 := rs (se 1 (by rfl) ⟨106046, by rfl⟩) R212093
theorem R141425 : Reach 141425 := rs (se 2 (by rfl) ⟨53034, by rfl⟩) R106069
theorem R141443 : Reach 141443 := rs (se 1 (by rfl) ⟨106082, by rfl⟩) R212165
theorem R141473 : Reach 141473 := rs (se 2 (by rfl) ⟨53052, by rfl⟩) R106105
theorem R141491 : Reach 141491 := rs (se 1 (by rfl) ⟨106118, by rfl⟩) R212237
theorem R141521 : Reach 141521 := rs (se 2 (by rfl) ⟨53070, by rfl⟩) R106141
theorem R174307 : Reach 174307 := rs (se 1 (by rfl) ⟨130730, by rfl⟩) R261461
theorem R141539 : Reach 141539 := rs (se 1 (by rfl) ⟨106154, by rfl⟩) R212309
theorem R207089 : Reach 207089 := rs (se 2 (by rfl) ⟨77658, by rfl⟩) R155317
theorem R141569 : Reach 141569 := rs (se 2 (by rfl) ⟨53088, by rfl⟩) R106177
theorem R207107 : Reach 207107 := rs (se 1 (by rfl) ⟨155330, by rfl⟩) R310661
theorem R141587 : Reach 141587 := rs (se 1 (by rfl) ⟨106190, by rfl⟩) R212381
theorem R3352853 : Reach 3352853 := rs (se 6 (by rfl) ⟨78582, by rfl⟩) R157165
theorem R141617 : Reach 141617 := rs (se 2 (by rfl) ⟨53106, by rfl⟩) R106213
theorem R141635 : Reach 141635 := rs (se 1 (by rfl) ⟨106226, by rfl⟩) R212453
theorem R141665 : Reach 141665 := rs (se 2 (by rfl) ⟨53124, by rfl⟩) R106249
theorem R403811 : Reach 403811 := rs (se 1 (by rfl) ⟨302858, by rfl⟩) R605717
theorem R141683 : Reach 141683 := rs (se 1 (by rfl) ⟨106262, by rfl⟩) R212525
theorem R174467 : Reach 174467 := rs (se 1 (by rfl) ⟨130850, by rfl⟩) R261701
theorem R141713 : Reach 141713 := rs (se 2 (by rfl) ⟨53142, by rfl⟩) R106285
theorem R141731 : Reach 141731 := rs (se 1 (by rfl) ⟨106298, by rfl⟩) R212597
theorem R141761 : Reach 141761 := rs (se 2 (by rfl) ⟨53160, by rfl⟩) R106321
theorem R141779 : Reach 141779 := rs (se 1 (by rfl) ⟨106334, by rfl⟩) R212669
theorem R469475 : Reach 469475 := rs (se 1 (by rfl) ⟨352106, by rfl⟩) R704213
theorem R141809 : Reach 141809 := rs (se 2 (by rfl) ⟨53178, by rfl⟩) R106357
theorem R141827 : Reach 141827 := rs (se 1 (by rfl) ⟨106370, by rfl⟩) R212741
theorem R207377 : Reach 207377 := rs (se 2 (by rfl) ⟨77766, by rfl⟩) R155533
theorem R141857 : Reach 141857 := rs (se 2 (by rfl) ⟨53196, by rfl⟩) R106393
theorem R207395 : Reach 207395 := rs (se 1 (by rfl) ⟨155546, by rfl⟩) R311093
theorem R141875 : Reach 141875 := rs (se 1 (by rfl) ⟨106406, by rfl⟩) R212813
theorem R141905 : Reach 141905 := rs (se 2 (by rfl) ⟨53214, by rfl⟩) R106429
theorem R141923 : Reach 141923 := rs (se 1 (by rfl) ⟨106442, by rfl⟩) R212885
theorem R141953 : Reach 141953 := rs (se 2 (by rfl) ⟨53232, by rfl⟩) R106465
theorem R141971 : Reach 141971 := rs (se 1 (by rfl) ⟨106478, by rfl⟩) R212957
theorem R142001 : Reach 142001 := rs (se 2 (by rfl) ⟨53250, by rfl⟩) R106501
theorem R142019 : Reach 142019 := rs (se 1 (by rfl) ⟨106514, by rfl⟩) R213029
theorem R142049 : Reach 142049 := rs (se 2 (by rfl) ⟨53268, by rfl⟩) R106537
theorem R142067 : Reach 142067 := rs (se 1 (by rfl) ⟨106550, by rfl⟩) R213101
theorem R142097 : Reach 142097 := rs (se 2 (by rfl) ⟨53286, by rfl⟩) R106573
theorem R633635 : Reach 633635 := rs (se 1 (by rfl) ⟨475226, by rfl⟩) R950453
theorem R142115 : Reach 142115 := rs (se 1 (by rfl) ⟨106586, by rfl⟩) R213173
theorem R207665 : Reach 207665 := rs (se 2 (by rfl) ⟨77874, by rfl⟩) R155749
theorem R142145 : Reach 142145 := rs (se 2 (by rfl) ⟨53304, by rfl⟩) R106609
theorem R207683 : Reach 207683 := rs (se 1 (by rfl) ⟨155762, by rfl⟩) R311525
theorem R142163 : Reach 142163 := rs (se 1 (by rfl) ⟨106622, by rfl⟩) R213245
theorem R142193 : Reach 142193 := rs (se 2 (by rfl) ⟨53322, by rfl⟩) R106645
theorem R142211 : Reach 142211 := rs (se 1 (by rfl) ⟨106658, by rfl⟩) R213317
theorem R240529 : Reach 240529 := rs (se 2 (by rfl) ⟨90198, by rfl⟩) R180397
theorem R142241 : Reach 142241 := rs (se 2 (by rfl) ⟨53340, by rfl⟩) R106681
theorem R142259 : Reach 142259 := rs (se 1 (by rfl) ⟨106694, by rfl⟩) R213389
theorem R142289 : Reach 142289 := rs (se 2 (by rfl) ⟨53358, by rfl⟩) R106717
theorem R142307 : Reach 142307 := rs (se 1 (by rfl) ⟨106730, by rfl⟩) R213461
theorem R142337 : Reach 142337 := rs (se 2 (by rfl) ⟨53376, by rfl⟩) R106753
theorem R142355 : Reach 142355 := rs (se 1 (by rfl) ⟨106766, by rfl⟩) R213533
theorem R142385 : Reach 142385 := rs (se 2 (by rfl) ⟨53394, by rfl⟩) R106789
theorem R142403 : Reach 142403 := rs (se 1 (by rfl) ⟨106802, by rfl⟩) R213605
theorem R207953 : Reach 207953 := rs (se 2 (by rfl) ⟨77982, by rfl⟩) R155965
theorem R142433 : Reach 142433 := rs (se 2 (by rfl) ⟨53412, by rfl⟩) R106825
theorem R207971 : Reach 207971 := rs (se 1 (by rfl) ⟨155978, by rfl⟩) R311957
theorem R142451 : Reach 142451 := rs (se 1 (by rfl) ⟨106838, by rfl⟩) R213677
theorem R142481 : Reach 142481 := rs (se 2 (by rfl) ⟨53430, by rfl⟩) R106861
theorem R142499 : Reach 142499 := rs (se 1 (by rfl) ⟨106874, by rfl⟩) R213749
theorem R142529 : Reach 142529 := rs (se 2 (by rfl) ⟨53448, by rfl⟩) R106897
theorem R142547 : Reach 142547 := rs (se 1 (by rfl) ⟨106910, by rfl⟩) R213821
theorem R142577 : Reach 142577 := rs (se 2 (by rfl) ⟨53466, by rfl⟩) R106933
theorem R142595 : Reach 142595 := rs (se 1 (by rfl) ⟨106946, by rfl⟩) R213893
theorem R601357 : Reach 601357 := rs (se 3 (by rfl) ⟨112754, by rfl⟩) R225509
theorem R470285 : Reach 470285 := rs (se 3 (by rfl) ⟨88178, by rfl⟩) R176357
theorem R142625 : Reach 142625 := rs (se 2 (by rfl) ⟨53484, by rfl⟩) R106969
theorem R142643 : Reach 142643 := rs (se 1 (by rfl) ⟨106982, by rfl⟩) R213965
theorem R142673 : Reach 142673 := rs (se 2 (by rfl) ⟨53502, by rfl⟩) R107005
theorem R142691 : Reach 142691 := rs (se 1 (by rfl) ⟨107018, by rfl⟩) R214037
theorem R208241 : Reach 208241 := rs (se 2 (by rfl) ⟨78090, by rfl⟩) R156181
theorem R208259 : Reach 208259 := rs (se 1 (by rfl) ⟨156194, by rfl⟩) R312389
theorem R175537 : Reach 175537 := rs (se 2 (by rfl) ⟨65826, by rfl⟩) R131653
theorem R306659 : Reach 306659 := rs (se 1 (by rfl) ⟨229994, by rfl⟩) R459989
theorem R110083 : Reach 110083 := rs (se 1 (by rfl) ⟨82562, by rfl⟩) R165125
theorem R667277 : Reach 667277 := rs (se 3 (by rfl) ⟨125114, by rfl⟩) R250229
theorem R208529 : Reach 208529 := rs (se 2 (by rfl) ⟨78198, by rfl⟩) R156397
theorem R208547 : Reach 208547 := rs (se 1 (by rfl) ⟨156410, by rfl⟩) R312821
theorem R143219 : Reach 143219 := rs (se 1 (by rfl) ⟨107414, by rfl⟩) R214829
theorem R536453 : Reach 536453 := rs (se 4 (by rfl) ⟨50292, by rfl⟩) R100585
theorem R339875 : Reach 339875 := rs (se 1 (by rfl) ⟨254906, by rfl⟩) R509813
theorem R208817 : Reach 208817 := rs (se 2 (by rfl) ⟨78306, by rfl⟩) R156613
theorem R208835 : Reach 208835 := rs (se 1 (by rfl) ⟨156626, by rfl⟩) R313253
theorem R143411 : Reach 143411 := rs (se 1 (by rfl) ⟨107558, by rfl⟩) R215117
theorem R634949 : Reach 634949 := rs (se 4 (by rfl) ⟨59526, by rfl⟩) R119053
theorem R209105 : Reach 209105 := rs (se 2 (by rfl) ⟨78414, by rfl⟩) R156829
theorem R209123 : Reach 209123 := rs (se 1 (by rfl) ⟨156842, by rfl⟩) R313685
theorem R143617 : Reach 143617 := rs (se 2 (by rfl) ⟨53856, by rfl⟩) R107713
theorem R176593 : Reach 176593 := rs (se 2 (by rfl) ⟨66222, by rfl⟩) R132445
theorem R242129 : Reach 242129 := rs (se 2 (by rfl) ⟨90798, by rfl⟩) R181597
theorem R209393 : Reach 209393 := rs (se 2 (by rfl) ⟨78522, by rfl⟩) R157045
theorem R209411 : Reach 209411 := rs (se 1 (by rfl) ⟨157058, by rfl⟩) R314117
theorem R537137 : Reach 537137 := rs (se 2 (by rfl) ⟨201426, by rfl⟩) R402853
theorem R307853 : Reach 307853 := rs (se 3 (by rfl) ⟨57722, by rfl⟩) R115445
theorem R144019 : Reach 144019 := rs (se 1 (by rfl) ⟨108014, by rfl⟩) R216029
theorem R307907 : Reach 307907 := rs (se 1 (by rfl) ⟨230930, by rfl⟩) R461861
theorem R209681 : Reach 209681 := rs (se 2 (by rfl) ⟨78630, by rfl⟩) R157261
theorem R209699 : Reach 209699 := rs (se 1 (by rfl) ⟨157274, by rfl⟩) R314549
theorem R176995 : Reach 176995 := rs (se 1 (by rfl) ⟨132746, by rfl⟩) R265493
theorem R701297 : Reach 701297 := rs (se 2 (by rfl) ⟨262986, by rfl⟩) R525973
theorem R177041 : Reach 177041 := rs (se 2 (by rfl) ⟨66390, by rfl⟩) R132781
theorem R635825 : Reach 635825 := rs (se 2 (by rfl) ⟨238434, by rfl⟩) R476869
theorem R308177 : Reach 308177 := rs (se 2 (by rfl) ⟨115566, by rfl⟩) R231133
theorem R144337 : Reach 144337 := rs (se 2 (by rfl) ⟨54126, by rfl⟩) R108253
theorem R209969 : Reach 209969 := rs (se 2 (by rfl) ⟨78738, by rfl⟩) R157477
theorem R209987 : Reach 209987 := rs (se 1 (by rfl) ⟨157490, by rfl⟩) R314981
theorem R144451 : Reach 144451 := rs (se 1 (by rfl) ⟨108338, by rfl⟩) R216677
theorem R177329 : Reach 177329 := rs (se 2 (by rfl) ⟨66498, by rfl⟩) R132997
theorem R210257 : Reach 210257 := rs (se 2 (by rfl) ⟨78846, by rfl⟩) R157693
theorem R210275 : Reach 210275 := rs (se 1 (by rfl) ⟨157706, by rfl⟩) R315413
theorem R308717 : Reach 308717 := rs (se 3 (by rfl) ⟨57884, by rfl⟩) R115769
theorem R439793 : Reach 439793 := rs (se 2 (by rfl) ⟨164922, by rfl⟩) R329845
theorem R308771 : Reach 308771 := rs (se 1 (by rfl) ⟨231578, by rfl⟩) R463157
theorem R210545 : Reach 210545 := rs (se 2 (by rfl) ⟨78954, by rfl⟩) R157909
theorem R210563 : Reach 210563 := rs (se 1 (by rfl) ⟨157922, by rfl⟩) R315845
theorem R112355 : Reach 112355 := rs (se 1 (by rfl) ⟨84266, by rfl⟩) R168533
theorem R309041 : Reach 309041 := rs (se 2 (by rfl) ⟨115890, by rfl⟩) R231781
theorem R767843 : Reach 767843 := rs (se 1 (by rfl) ⟨575882, by rfl⟩) R1151765
theorem R178051 : Reach 178051 := rs (se 1 (by rfl) ⟨133538, by rfl⟩) R267077
theorem R210833 : Reach 210833 := rs (se 2 (by rfl) ⟨79062, by rfl⟩) R158125
theorem R210851 : Reach 210851 := rs (se 1 (by rfl) ⟨158138, by rfl⟩) R316277
theorem R243629 : Reach 243629 := rs (se 3 (by rfl) ⟨45680, by rfl⟩) R91361
theorem R571313 : Reach 571313 := rs (se 2 (by rfl) ⟨214242, by rfl⟩) R428485
theorem R669667 : Reach 669667 := rs (se 1 (by rfl) ⟨502250, by rfl⟩) R1004501
theorem R538595 : Reach 538595 := rs (se 1 (by rfl) ⟨403946, by rfl⟩) R807893
theorem R767971 : Reach 767971 := rs (se 1 (by rfl) ⟨575978, by rfl⟩) R1151957
theorem R604273 : Reach 604273 := rs (se 2 (by rfl) ⟨226602, by rfl⟩) R453205
theorem R473201 : Reach 473201 := rs (se 2 (by rfl) ⟨177450, by rfl⟩) R354901
theorem R211121 : Reach 211121 := rs (se 2 (by rfl) ⟨79170, by rfl⟩) R158341
theorem R211139 : Reach 211139 := rs (se 1 (by rfl) ⟨158354, by rfl⟩) R316709
theorem R178499 : Reach 178499 := rs (se 1 (by rfl) ⟨133874, by rfl⟩) R267749
theorem R309581 : Reach 309581 := rs (se 3 (by rfl) ⟨58046, by rfl⟩) R116093
theorem R309635 : Reach 309635 := rs (se 1 (by rfl) ⟨232226, by rfl⟩) R464453
theorem R211409 : Reach 211409 := rs (se 2 (by rfl) ⟨79278, by rfl⟩) R158557
theorem R211427 : Reach 211427 := rs (se 1 (by rfl) ⟨158570, by rfl⟩) R317141
theorem R440909 : Reach 440909 := rs (se 3 (by rfl) ⟨82670, by rfl⟩) R165341
theorem R178787 : Reach 178787 := rs (se 1 (by rfl) ⟨134090, by rfl⟩) R268181
theorem R309905 : Reach 309905 := rs (se 2 (by rfl) ⟨116214, by rfl⟩) R232429
theorem R146099 : Reach 146099 := rs (se 1 (by rfl) ⟨109574, by rfl⟩) R219149
theorem R211697 : Reach 211697 := rs (se 2 (by rfl) ⟨79386, by rfl⟩) R158773
theorem R211715 : Reach 211715 := rs (se 1 (by rfl) ⟨158786, by rfl⟩) R317573
theorem R146387 : Reach 146387 := rs (se 1 (by rfl) ⟨109790, by rfl⟩) R219581
theorem R211985 : Reach 211985 := rs (se 2 (by rfl) ⟨79494, by rfl⟩) R158989
theorem R212003 : Reach 212003 := rs (se 1 (by rfl) ⟨159002, by rfl⟩) R318005
theorem R965773 : Reach 965773 := rs (se 3 (by rfl) ⟨181082, by rfl⟩) R362165
theorem R113827 : Reach 113827 := rs (se 1 (by rfl) ⟨85370, by rfl⟩) R170741
theorem R310445 : Reach 310445 := rs (se 3 (by rfl) ⟨58208, by rfl⟩) R116417
theorem R310499 : Reach 310499 := rs (se 1 (by rfl) ⟨232874, by rfl⟩) R465749
theorem R212273 : Reach 212273 := rs (se 2 (by rfl) ⟨79602, by rfl⟩) R159205
theorem R212291 : Reach 212291 := rs (se 1 (by rfl) ⟨159218, by rfl⟩) R318437
theorem R408995 : Reach 408995 := rs (se 1 (by rfl) ⟨306746, by rfl⟩) R613493
theorem R5848517 : Reach 5848517 := rs (se 4 (by rfl) ⟨548298, by rfl⟩) R1096597
theorem R310769 : Reach 310769 := rs (se 2 (by rfl) ⟨116538, by rfl⟩) R233077
theorem R507377 : Reach 507377 := rs (se 2 (by rfl) ⟨190266, by rfl⟩) R380533
theorem R179729 : Reach 179729 := rs (se 2 (by rfl) ⟨67398, by rfl⟩) R134797
theorem R474659 : Reach 474659 := rs (se 1 (by rfl) ⟨355994, by rfl⟩) R711989
theorem R376397 : Reach 376397 := rs (se 3 (by rfl) ⟨70574, by rfl⟩) R141149
theorem R212561 : Reach 212561 := rs (se 2 (by rfl) ⟨79710, by rfl⟩) R159421
theorem R212579 : Reach 212579 := rs (se 1 (by rfl) ⟨159434, by rfl⟩) R318869
theorem R376525 : Reach 376525 := rs (se 3 (by rfl) ⟨70598, by rfl⟩) R141197
theorem R147187 : Reach 147187 := rs (se 1 (by rfl) ⟨110390, by rfl⟩) R220781
theorem R212849 : Reach 212849 := rs (se 2 (by rfl) ⟨79818, by rfl⟩) R159637
theorem R147329 : Reach 147329 := rs (se 2 (by rfl) ⟨55248, by rfl⟩) R110497
theorem R212867 : Reach 212867 := rs (se 1 (by rfl) ⟨159650, by rfl⟩) R319301
theorem R2015117 : Reach 2015117 := rs (se 3 (by rfl) ⟨377834, by rfl⟩) R755669
theorem R442253 : Reach 442253 := rs (se 3 (by rfl) ⟨82922, by rfl⟩) R165845
theorem R147361 : Reach 147361 := rs (se 2 (by rfl) ⟨55260, by rfl⟩) R110521
theorem R311309 : Reach 311309 := rs (se 3 (by rfl) ⟨58370, by rfl⟩) R116741
theorem R311363 : Reach 311363 := rs (se 1 (by rfl) ⟨233522, by rfl⟩) R467045
theorem R213137 : Reach 213137 := rs (se 2 (by rfl) ⟨79926, by rfl⟩) R159853
theorem R213155 : Reach 213155 := rs (se 1 (by rfl) ⟨159866, by rfl⟩) R319733
theorem R409841 : Reach 409841 := rs (se 2 (by rfl) ⟨153690, by rfl⟩) R307381
theorem R475469 : Reach 475469 := rs (se 3 (by rfl) ⟨89150, by rfl⟩) R178301
theorem R311633 : Reach 311633 := rs (se 2 (by rfl) ⟨116862, by rfl⟩) R233725
theorem R213425 : Reach 213425 := rs (se 2 (by rfl) ⟨80034, by rfl⟩) R160069
theorem R213443 : Reach 213443 := rs (se 1 (by rfl) ⟨160082, by rfl⟩) R320165
theorem R213713 : Reach 213713 := rs (se 2 (by rfl) ⟨80142, by rfl⟩) R160285
theorem R213731 : Reach 213731 := rs (se 1 (by rfl) ⟨160298, by rfl⟩) R320597
theorem R148289 : Reach 148289 := rs (se 2 (by rfl) ⟨55608, by rfl⟩) R111217
theorem R1262405 : Reach 1262405 := rs (se 4 (by rfl) ⟨118350, by rfl⟩) R236701
theorem R1065797 : Reach 1065797 := rs (se 4 (by rfl) ⟨99918, by rfl⟩) R199837
theorem R312173 : Reach 312173 := rs (se 3 (by rfl) ⟨58532, by rfl⟩) R117065
theorem R312227 : Reach 312227 := rs (se 1 (by rfl) ⟨234170, by rfl⟩) R468341
theorem R214001 : Reach 214001 := rs (se 2 (by rfl) ⟨80250, by rfl⟩) R160501
theorem R214019 : Reach 214019 := rs (se 1 (by rfl) ⟨160514, by rfl⟩) R321029
theorem R312419 : Reach 312419 := rs (se 1 (by rfl) ⟨234314, by rfl⟩) R468629
theorem R312497 : Reach 312497 := rs (se 2 (by rfl) ⟨117186, by rfl⟩) R234373
theorem R115987 : Reach 115987 := rs (se 1 (by rfl) ⟨86990, by rfl⟩) R173981
theorem R116083 : Reach 116083 := rs (se 1 (by rfl) ⟨87062, by rfl⟩) R174125
theorem R3851717 : Reach 3851717 := rs (se 4 (by rfl) ⟨361098, by rfl⟩) R722197
theorem R509453 : Reach 509453 := rs (se 3 (by rfl) ⟨95522, by rfl⟩) R191045
theorem R149123 : Reach 149123 := rs (se 1 (by rfl) ⟨111842, by rfl⟩) R223685
theorem R313037 : Reach 313037 := rs (se 3 (by rfl) ⟨58694, by rfl⟩) R117389
theorem R313091 : Reach 313091 := rs (se 1 (by rfl) ⟨234818, by rfl⟩) R469637
theorem R116579 : Reach 116579 := rs (se 1 (by rfl) ⟨87434, by rfl⟩) R174869
theorem R149411 : Reach 149411 := rs (se 1 (by rfl) ⟨112058, by rfl⟩) R224117
theorem R673733 : Reach 673733 := rs (se 4 (by rfl) ⟨63162, by rfl⟩) R126325
theorem R640973 : Reach 640973 := rs (se 3 (by rfl) ⟨120182, by rfl⟩) R240365
theorem R313361 : Reach 313361 := rs (se 2 (by rfl) ⟨117510, by rfl⟩) R235021
theorem R149635 : Reach 149635 := rs (se 1 (by rfl) ⟨112226, by rfl⟩) R224453
theorem R247981 : Reach 247981 := rs (se 3 (by rfl) ⟨46496, by rfl⟩) R92993
theorem R117283 : Reach 117283 := rs (se 1 (by rfl) ⟨87962, by rfl⟩) R175925
theorem R313901 : Reach 313901 := rs (se 3 (by rfl) ⟨58856, by rfl⟩) R117713
theorem R313955 : Reach 313955 := rs (se 1 (by rfl) ⟨235466, by rfl⟩) R470933
theorem R117379 : Reach 117379 := rs (se 1 (by rfl) ⟨88034, by rfl⟩) R176069
theorem R150353 : Reach 150353 := rs (se 2 (by rfl) ⟨56382, by rfl⟩) R112765
theorem R314225 : Reach 314225 := rs (se 2 (by rfl) ⟨117834, by rfl⟩) R235669
theorem R510947 : Reach 510947 := rs (se 1 (by rfl) ⟨383210, by rfl⟩) R766421
theorem R248845 : Reach 248845 := rs (se 3 (by rfl) ⟨46658, by rfl⟩) R93317
theorem R150545 : Reach 150545 := rs (se 2 (by rfl) ⟨56454, by rfl⟩) R112909
theorem R117875 : Reach 117875 := rs (se 1 (by rfl) ⟨88406, by rfl⟩) R176813
theorem R150673 : Reach 150673 := rs (se 2 (by rfl) ⟨56502, by rfl⟩) R113005
theorem R478385 : Reach 478385 := rs (se 2 (by rfl) ⟨179394, by rfl⟩) R358789
theorem R314765 : Reach 314765 := rs (se 3 (by rfl) ⟨59018, by rfl⟩) R118037
theorem R314819 : Reach 314819 := rs (se 1 (by rfl) ⟨236114, by rfl⟩) R472229
theorem R347597 : Reach 347597 := rs (se 3 (by rfl) ⟨65174, by rfl⟩) R130349
theorem R315089 : Reach 315089 := rs (se 2 (by rfl) ⟨118158, by rfl⟩) R236317
theorem R1199843 : Reach 1199843 := rs (se 1 (by rfl) ⟨899882, by rfl⟩) R1799765
theorem R118531 : Reach 118531 := rs (se 1 (by rfl) ⟨88898, by rfl⟩) R177797
theorem R151313 : Reach 151313 := rs (se 2 (by rfl) ⟨56742, by rfl⟩) R113485
theorem R118579 : Reach 118579 := rs (se 1 (by rfl) ⟨88934, by rfl⟩) R177869
theorem R118643 : Reach 118643 := rs (se 1 (by rfl) ⟨88982, by rfl⟩) R177965
theorem R118675 : Reach 118675 := rs (se 1 (by rfl) ⟨89006, by rfl⟩) R178013
theorem R282541 : Reach 282541 := rs (se 3 (by rfl) ⟨52976, by rfl⟩) R105953
theorem R315505 : Reach 315505 := rs (se 2 (by rfl) ⟨118314, by rfl⟩) R236629
theorem R315629 : Reach 315629 := rs (se 3 (by rfl) ⟨59180, by rfl⟩) R118361
theorem R348401 : Reach 348401 := rs (se 2 (by rfl) ⟨130650, by rfl⟩) R261301
theorem R315683 : Reach 315683 := rs (se 1 (by rfl) ⟨236762, by rfl⟩) R473525
theorem R119171 : Reach 119171 := rs (se 1 (by rfl) ⟨89378, by rfl⟩) R178757
theorem R315953 : Reach 315953 := rs (se 2 (by rfl) ⟨118482, by rfl⟩) R236965
theorem R479843 : Reach 479843 := rs (se 1 (by rfl) ⟨359882, by rfl⟩) R719765
theorem R512675 : Reach 512675 := rs (se 1 (by rfl) ⟨384506, by rfl⟩) R769013
theorem R152275 : Reach 152275 := rs (se 1 (by rfl) ⟨114206, by rfl⟩) R228413
theorem R316163 : Reach 316163 := rs (se 1 (by rfl) ⟨237122, by rfl⟩) R474245
theorem R119587 : Reach 119587 := rs (se 1 (by rfl) ⟨89690, by rfl⟩) R179381
theorem R349069 : Reach 349069 := rs (se 3 (by rfl) ⟨65450, by rfl⟩) R130901
theorem R119875 : Reach 119875 := rs (se 1 (by rfl) ⟨89906, by rfl⟩) R179813
theorem R316493 : Reach 316493 := rs (se 3 (by rfl) ⟨59342, by rfl⟩) R118685
theorem R316547 : Reach 316547 := rs (se 1 (by rfl) ⟨237410, by rfl⟩) R474821
theorem R119971 : Reach 119971 := rs (se 1 (by rfl) ⟨89978, by rfl⟩) R179957
theorem R677105 : Reach 677105 := rs (se 2 (by rfl) ⟨253914, by rfl⟩) R507829
theorem R480653 : Reach 480653 := rs (se 3 (by rfl) ⟨90122, by rfl⟩) R180245
theorem R316817 : Reach 316817 := rs (se 2 (by rfl) ⟨118806, by rfl⟩) R237613
theorem R284077 : Reach 284077 := rs (se 3 (by rfl) ⟨53264, by rfl⟩) R106529
theorem R251363 : Reach 251363 := rs (se 1 (by rfl) ⟨188522, by rfl⟩) R377045
theorem R284305 : Reach 284305 := rs (se 2 (by rfl) ⟨106614, by rfl⟩) R213229
theorem R349859 : Reach 349859 := rs (se 1 (by rfl) ⟨262394, by rfl⟩) R524789
theorem R317357 : Reach 317357 := rs (se 3 (by rfl) ⟨59504, by rfl⟩) R119009
theorem R317411 : Reach 317411 := rs (se 1 (by rfl) ⟨238058, by rfl⟩) R476117
theorem R2414645 : Reach 2414645 := rs (se 5 (by rfl) ⟨113186, by rfl⟩) R226373
theorem R219281 : Reach 219281 := rs (se 2 (by rfl) ⟨82230, by rfl⟩) R164461
theorem R186545 : Reach 186545 := rs (se 2 (by rfl) ⟨69954, by rfl⟩) R139909
theorem R547013 : Reach 547013 := rs (se 4 (by rfl) ⟨51282, by rfl⟩) R102565
theorem R317681 : Reach 317681 := rs (se 2 (by rfl) ⟨119130, by rfl⟩) R238261
theorem R153859 : Reach 153859 := rs (se 1 (by rfl) ⟨115394, by rfl⟩) R230789
theorem R252163 : Reach 252163 := rs (se 1 (by rfl) ⟨189122, by rfl⟩) R378245
theorem R350513 : Reach 350513 := rs (se 2 (by rfl) ⟨131442, by rfl⟩) R262885
theorem R154001 : Reach 154001 := rs (se 2 (by rfl) ⟨57750, by rfl⟩) R115501
theorem R252305 : Reach 252305 := rs (se 2 (by rfl) ⟨94614, by rfl⟩) R189229
theorem R154003 : Reach 154003 := rs (se 1 (by rfl) ⟨115502, by rfl⟩) R231005
theorem R252337 : Reach 252337 := rs (se 2 (by rfl) ⟨94626, by rfl⟩) R189253
theorem R1071629 : Reach 1071629 := rs (se 3 (by rfl) ⟨200930, by rfl⟩) R401861
theorem R154129 : Reach 154129 := rs (se 2 (by rfl) ⟨57798, by rfl⟩) R115597
theorem R154163 : Reach 154163 := rs (se 1 (by rfl) ⟨115622, by rfl⟩) R231245
theorem R154291 : Reach 154291 := rs (se 1 (by rfl) ⟨115718, by rfl⟩) R231437
theorem R318221 : Reach 318221 := rs (se 3 (by rfl) ⟨59666, by rfl⟩) R119333
theorem R154433 : Reach 154433 := rs (se 2 (by rfl) ⟨57912, by rfl⟩) R115825
theorem R318275 : Reach 318275 := rs (se 1 (by rfl) ⟨238706, by rfl⟩) R477413
theorem R154561 : Reach 154561 := rs (se 2 (by rfl) ⟨57960, by rfl⟩) R115921
theorem R154595 : Reach 154595 := rs (se 1 (by rfl) ⟨115946, by rfl⟩) R231893
theorem R154675 : Reach 154675 := rs (se 1 (by rfl) ⟨116006, by rfl⟩) R232013
theorem R318545 : Reach 318545 := rs (se 2 (by rfl) ⟨119454, by rfl⟩) R238909
theorem R154723 : Reach 154723 := rs (se 1 (by rfl) ⟨116042, by rfl⟩) R232085
theorem R351373 : Reach 351373 := rs (se 3 (by rfl) ⟨65882, by rfl⟩) R131765
theorem R875717 : Reach 875717 := rs (se 4 (by rfl) ⟨82098, by rfl⟩) R164197
theorem R154865 : Reach 154865 := rs (se 2 (by rfl) ⟨58074, by rfl⟩) R116149
theorem R253265 : Reach 253265 := rs (se 2 (by rfl) ⟨94974, by rfl⟩) R189949
theorem R154993 : Reach 154993 := rs (se 2 (by rfl) ⟨58122, by rfl⟩) R116245
theorem R155027 : Reach 155027 := rs (se 1 (by rfl) ⟨116270, by rfl⟩) R232541
theorem R155155 : Reach 155155 := rs (se 1 (by rfl) ⟨116366, by rfl⟩) R232733
theorem R319085 : Reach 319085 := rs (se 3 (by rfl) ⟨59828, by rfl⟩) R119657
theorem R155297 : Reach 155297 := rs (se 2 (by rfl) ⟨58236, by rfl⟩) R116473
theorem R319139 : Reach 319139 := rs (se 1 (by rfl) ⟨239354, by rfl⟩) R478709
theorem R482993 : Reach 482993 := rs (se 2 (by rfl) ⟨181122, by rfl⟩) R362245
theorem R351971 : Reach 351971 := rs (se 1 (by rfl) ⟨263978, by rfl⟩) R527957
theorem R351985 : Reach 351985 := rs (se 2 (by rfl) ⟨131994, by rfl⟩) R263989
theorem R155425 : Reach 155425 := rs (se 2 (by rfl) ⟨58284, by rfl⟩) R116569
theorem R155459 : Reach 155459 := rs (se 1 (by rfl) ⟨116594, by rfl⟩) R233189
theorem R450481 : Reach 450481 := rs (se 2 (by rfl) ⟨168930, by rfl⟩) R337861
theorem R319409 : Reach 319409 := rs (se 2 (by rfl) ⟨119778, by rfl⟩) R239557
theorem R155587 : Reach 155587 := rs (se 1 (by rfl) ⟨116690, by rfl⟩) R233381
theorem R155729 : Reach 155729 := rs (se 2 (by rfl) ⟨58398, by rfl⟩) R116797
theorem R155857 : Reach 155857 := rs (se 2 (by rfl) ⟨58446, by rfl⟩) R116893
theorem R155891 : Reach 155891 := rs (se 1 (by rfl) ⟨116918, by rfl⟩) R233837
theorem R286993 : Reach 286993 := rs (se 2 (by rfl) ⟨107622, by rfl⟩) R215245
theorem R156019 : Reach 156019 := rs (se 1 (by rfl) ⟨117014, by rfl⟩) R234029
theorem R319949 : Reach 319949 := rs (se 3 (by rfl) ⟨59990, by rfl⟩) R119981
theorem R156161 : Reach 156161 := rs (se 2 (by rfl) ⟨58560, by rfl⟩) R117121
theorem R320003 : Reach 320003 := rs (se 1 (by rfl) ⟨240002, by rfl⟩) R480005
theorem R254477 : Reach 254477 := rs (se 3 (by rfl) ⟨47714, by rfl⟩) R95429
theorem R811619 : Reach 811619 := rs (se 1 (by rfl) ⟨608714, by rfl⟩) R1217429
theorem R156289 : Reach 156289 := rs (se 2 (by rfl) ⟨58608, by rfl⟩) R117217
theorem R189073 : Reach 189073 := rs (se 2 (by rfl) ⟨70902, by rfl⟩) R141805
theorem R156323 : Reach 156323 := rs (se 1 (by rfl) ⟨117242, by rfl⟩) R234485
theorem R123617 : Reach 123617 := rs (se 2 (by rfl) ⟨46356, by rfl⟩) R92713
theorem R320273 : Reach 320273 := rs (se 2 (by rfl) ⟨120102, by rfl⟩) R240205
theorem R156451 : Reach 156451 := rs (se 1 (by rfl) ⟨117338, by rfl⟩) R234677
theorem R156593 : Reach 156593 := rs (se 2 (by rfl) ⟨58722, by rfl⟩) R117445
theorem R3761093 : Reach 3761093 := rs (se 4 (by rfl) ⟨352602, by rfl⟩) R705205
theorem R91139 : Reach 91139 := rs (se 1 (by rfl) ⟨68354, by rfl⟩) R136709
theorem R91155 : Reach 91155 := rs (se 1 (by rfl) ⟨68366, by rfl⟩) R136733
theorem R91171 : Reach 91171 := rs (se 1 (by rfl) ⟨68378, by rfl⟩) R136757
theorem R156721 : Reach 156721 := rs (se 2 (by rfl) ⟨58770, by rfl⟩) R117541
theorem R91187 : Reach 91187 := rs (se 1 (by rfl) ⟨68390, by rfl⟩) R136781
theorem R91203 : Reach 91203 := rs (se 1 (by rfl) ⟨68402, by rfl⟩) R136805
theorem R91219 : Reach 91219 := rs (se 1 (by rfl) ⟨68414, by rfl⟩) R136829
theorem R156755 : Reach 156755 := rs (se 1 (by rfl) ⟨117566, by rfl⟩) R235133
theorem R91235 : Reach 91235 := rs (se 1 (by rfl) ⟨68426, by rfl⟩) R136853
theorem R91251 : Reach 91251 := rs (se 1 (by rfl) ⟨68438, by rfl⟩) R136877
theorem R91267 : Reach 91267 := rs (se 1 (by rfl) ⟨68450, by rfl⟩) R136901
theorem R91283 : Reach 91283 := rs (se 1 (by rfl) ⟨68462, by rfl⟩) R136925
theorem R91299 : Reach 91299 := rs (se 1 (by rfl) ⟨68474, by rfl⟩) R136949
theorem R353443 : Reach 353443 := rs (se 1 (by rfl) ⟨265082, by rfl⟩) R530165
theorem R124081 : Reach 124081 := rs (se 2 (by rfl) ⟨46530, by rfl⟩) R93061
theorem R91315 : Reach 91315 := rs (se 1 (by rfl) ⟨68486, by rfl⟩) R136973
theorem R91331 : Reach 91331 := rs (se 1 (by rfl) ⟨68498, by rfl⟩) R136997
theorem R91347 : Reach 91347 := rs (se 1 (by rfl) ⟨68510, by rfl⟩) R137021
theorem R156883 : Reach 156883 := rs (se 1 (by rfl) ⟨117662, by rfl⟩) R235325
theorem R91363 : Reach 91363 := rs (se 1 (by rfl) ⟨68522, by rfl⟩) R137045
theorem R91379 : Reach 91379 := rs (se 1 (by rfl) ⟨68534, by rfl⟩) R137069
theorem R91395 : Reach 91395 := rs (se 1 (by rfl) ⟨68546, by rfl⟩) R137093
theorem R91411 : Reach 91411 := rs (se 1 (by rfl) ⟨68558, by rfl⟩) R137117
theorem R91427 : Reach 91427 := rs (se 1 (by rfl) ⟨68570, by rfl⟩) R137141
theorem R320813 : Reach 320813 := rs (se 3 (by rfl) ⟨60152, by rfl⟩) R120305
theorem R91443 : Reach 91443 := rs (se 1 (by rfl) ⟨68582, by rfl⟩) R137165
theorem R91459 : Reach 91459 := rs (se 1 (by rfl) ⟨68594, by rfl⟩) R137189
theorem R91475 : Reach 91475 := rs (se 1 (by rfl) ⟨68606, by rfl⟩) R137213
theorem R157025 : Reach 157025 := rs (se 2 (by rfl) ⟨58884, by rfl⟩) R117769
theorem R91491 : Reach 91491 := rs (se 1 (by rfl) ⟨68618, by rfl⟩) R137237
theorem R320867 : Reach 320867 := rs (se 1 (by rfl) ⟨240650, by rfl⟩) R481301
theorem R1074545 : Reach 1074545 := rs (se 2 (by rfl) ⟨402954, by rfl⟩) R805909
theorem R91507 : Reach 91507 := rs (se 1 (by rfl) ⟨68630, by rfl⟩) R137261
theorem R91523 : Reach 91523 := rs (se 1 (by rfl) ⟨68642, by rfl⟩) R137285
theorem R91539 : Reach 91539 := rs (se 1 (by rfl) ⟨68654, by rfl⟩) R137309
theorem R91555 : Reach 91555 := rs (se 1 (by rfl) ⟨68666, by rfl⟩) R137333
theorem R91571 : Reach 91571 := rs (se 1 (by rfl) ⟨68678, by rfl⟩) R137357
theorem R91587 : Reach 91587 := rs (se 1 (by rfl) ⟨68690, by rfl⟩) R137381
theorem R91603 : Reach 91603 := rs (se 1 (by rfl) ⟨68702, by rfl⟩) R137405
theorem R157153 : Reach 157153 := rs (se 2 (by rfl) ⟨58932, by rfl⟩) R117865
theorem R91619 : Reach 91619 := rs (se 1 (by rfl) ⟨68714, by rfl⟩) R137429
theorem R91635 : Reach 91635 := rs (se 1 (by rfl) ⟨68726, by rfl⟩) R137453
theorem R91651 : Reach 91651 := rs (se 1 (by rfl) ⟨68738, by rfl⟩) R137477
theorem R157187 : Reach 157187 := rs (se 1 (by rfl) ⟨117890, by rfl⟩) R235781
theorem R91667 : Reach 91667 := rs (se 1 (by rfl) ⟨68750, by rfl⟩) R137501
theorem R91683 : Reach 91683 := rs (se 1 (by rfl) ⟨68762, by rfl⟩) R137525
theorem R91699 : Reach 91699 := rs (se 1 (by rfl) ⟨68774, by rfl⟩) R137549
theorem R91715 : Reach 91715 := rs (se 1 (by rfl) ⟨68786, by rfl⟩) R137573
theorem R91731 : Reach 91731 := rs (se 1 (by rfl) ⟨68798, by rfl⟩) R137597
theorem R91747 : Reach 91747 := rs (se 1 (by rfl) ⟨68810, by rfl⟩) R137621
theorem R91763 : Reach 91763 := rs (se 1 (by rfl) ⟨68822, by rfl⟩) R137645
theorem R91779 : Reach 91779 := rs (se 1 (by rfl) ⟨68834, by rfl⟩) R137669
theorem R157315 : Reach 157315 := rs (se 1 (by rfl) ⟨117986, by rfl⟩) R235973
theorem R91795 : Reach 91795 := rs (se 1 (by rfl) ⟨68846, by rfl⟩) R137693
theorem R91811 : Reach 91811 := rs (se 1 (by rfl) ⟨68858, by rfl⟩) R137717
theorem R91827 : Reach 91827 := rs (se 1 (by rfl) ⟨68870, by rfl⟩) R137741
theorem R91843 : Reach 91843 := rs (se 1 (by rfl) ⟨68882, by rfl⟩) R137765
theorem R91859 : Reach 91859 := rs (se 1 (by rfl) ⟨68894, by rfl⟩) R137789
theorem R91875 : Reach 91875 := rs (se 1 (by rfl) ⟨68906, by rfl⟩) R137813
theorem R91891 : Reach 91891 := rs (se 1 (by rfl) ⟨68918, by rfl⟩) R137837
theorem R91907 : Reach 91907 := rs (se 1 (by rfl) ⟨68930, by rfl⟩) R137861
theorem R157457 : Reach 157457 := rs (se 2 (by rfl) ⟨59046, by rfl⟩) R118093
theorem R91923 : Reach 91923 := rs (se 1 (by rfl) ⟨68942, by rfl⟩) R137885
theorem R91939 : Reach 91939 := rs (se 1 (by rfl) ⟨68954, by rfl⟩) R137909
theorem R91955 : Reach 91955 := rs (se 1 (by rfl) ⟨68966, by rfl⟩) R137933
theorem R91971 : Reach 91971 := rs (se 1 (by rfl) ⟨68978, by rfl⟩) R137957
theorem R91987 : Reach 91987 := rs (se 1 (by rfl) ⟨68990, by rfl⟩) R137981
theorem R92003 : Reach 92003 := rs (se 1 (by rfl) ⟨69002, by rfl⟩) R138005
theorem R92019 : Reach 92019 := rs (se 1 (by rfl) ⟨69014, by rfl⟩) R138029
theorem R92035 : Reach 92035 := rs (se 1 (by rfl) ⟨69026, by rfl⟩) R138053
theorem R157585 : Reach 157585 := rs (se 2 (by rfl) ⟨59094, by rfl⟩) R118189
theorem R92051 : Reach 92051 := rs (se 1 (by rfl) ⟨69038, by rfl⟩) R138077
theorem R92067 : Reach 92067 := rs (se 1 (by rfl) ⟨69050, by rfl⟩) R138101
theorem R92083 : Reach 92083 := rs (se 1 (by rfl) ⟨69062, by rfl⟩) R138125
theorem R157619 : Reach 157619 := rs (se 1 (by rfl) ⟨118214, by rfl⟩) R236429
theorem R92099 : Reach 92099 := rs (se 1 (by rfl) ⟨69074, by rfl⟩) R138149
theorem R92115 : Reach 92115 := rs (se 1 (by rfl) ⟨69086, by rfl⟩) R138173
theorem R92131 : Reach 92131 := rs (se 1 (by rfl) ⟨69098, by rfl⟩) R138197
theorem R92147 : Reach 92147 := rs (se 1 (by rfl) ⟨69110, by rfl⟩) R138221
theorem R92163 : Reach 92163 := rs (se 1 (by rfl) ⟨69122, by rfl⟩) R138245
theorem R256013 : Reach 256013 := rs (se 3 (by rfl) ⟨48002, by rfl⟩) R96005
theorem R92179 : Reach 92179 := rs (se 1 (by rfl) ⟨69134, by rfl⟩) R138269
theorem R92195 : Reach 92195 := rs (se 1 (by rfl) ⟨69146, by rfl⟩) R138293
theorem R92211 : Reach 92211 := rs (se 1 (by rfl) ⟨69158, by rfl⟩) R138317
theorem R157747 : Reach 157747 := rs (se 1 (by rfl) ⟨118310, by rfl⟩) R236621
theorem R92227 : Reach 92227 := rs (se 1 (by rfl) ⟨69170, by rfl⟩) R138341
theorem R92243 : Reach 92243 := rs (se 1 (by rfl) ⟨69182, by rfl⟩) R138365
theorem R92259 : Reach 92259 := rs (se 1 (by rfl) ⟨69194, by rfl⟩) R138389
theorem R92275 : Reach 92275 := rs (se 1 (by rfl) ⟨69206, by rfl⟩) R138413
theorem R92291 : Reach 92291 := rs (se 1 (by rfl) ⟨69218, by rfl⟩) R138437
theorem R92307 : Reach 92307 := rs (se 1 (by rfl) ⟨69230, by rfl⟩) R138461
theorem R92323 : Reach 92323 := rs (se 1 (by rfl) ⟨69242, by rfl⟩) R138485
theorem R92339 : Reach 92339 := rs (se 1 (by rfl) ⟨69254, by rfl⟩) R138509
theorem R157889 : Reach 157889 := rs (se 2 (by rfl) ⟨59208, by rfl⟩) R118417
theorem R92355 : Reach 92355 := rs (se 1 (by rfl) ⟨69266, by rfl⟩) R138533
theorem R92371 : Reach 92371 := rs (se 1 (by rfl) ⟨69278, by rfl⟩) R138557
theorem R92387 : Reach 92387 := rs (se 1 (by rfl) ⟨69290, by rfl⟩) R138581
theorem R92403 : Reach 92403 := rs (se 1 (by rfl) ⟨69302, by rfl⟩) R138605
theorem R92419 : Reach 92419 := rs (se 1 (by rfl) ⟨69314, by rfl⟩) R138629
theorem R92435 : Reach 92435 := rs (se 1 (by rfl) ⟨69326, by rfl⟩) R138653
theorem R223523 : Reach 223523 := rs (se 1 (by rfl) ⟨167642, by rfl⟩) R335285
theorem R92451 : Reach 92451 := rs (se 1 (by rfl) ⟨69338, by rfl⟩) R138677
theorem R92467 : Reach 92467 := rs (se 1 (by rfl) ⟨69350, by rfl⟩) R138701
theorem R158017 : Reach 158017 := rs (se 2 (by rfl) ⟨59256, by rfl⟩) R118513
theorem R92483 : Reach 92483 := rs (se 1 (by rfl) ⟨69362, by rfl⟩) R138725
theorem R92499 : Reach 92499 := rs (se 1 (by rfl) ⟨69374, by rfl⟩) R138749
theorem R92515 : Reach 92515 := rs (se 1 (by rfl) ⟨69386, by rfl⟩) R138773
theorem R158051 : Reach 158051 := rs (se 1 (by rfl) ⟨118538, by rfl⟩) R237077
theorem R92531 : Reach 92531 := rs (se 1 (by rfl) ⟨69398, by rfl⟩) R138797
theorem R92547 : Reach 92547 := rs (se 1 (by rfl) ⟨69410, by rfl⟩) R138821
theorem R92563 : Reach 92563 := rs (se 1 (by rfl) ⟨69422, by rfl⟩) R138845
theorem R92579 : Reach 92579 := rs (se 1 (by rfl) ⟨69434, by rfl⟩) R138869
theorem R321965 : Reach 321965 := rs (se 3 (by rfl) ⟨60368, by rfl⟩) R120737
theorem R92595 : Reach 92595 := rs (se 1 (by rfl) ⟨69446, by rfl⟩) R138893
theorem R92611 : Reach 92611 := rs (se 1 (by rfl) ⟨69458, by rfl⟩) R138917
theorem R92627 : Reach 92627 := rs (se 1 (by rfl) ⟨69470, by rfl⟩) R138941
theorem R92643 : Reach 92643 := rs (se 1 (by rfl) ⟨69482, by rfl⟩) R138965
theorem R158179 : Reach 158179 := rs (se 1 (by rfl) ⟨118634, by rfl⟩) R237269
theorem R911843 : Reach 911843 := rs (se 1 (by rfl) ⟨683882, by rfl⟩) R1367765
theorem R92659 : Reach 92659 := rs (se 1 (by rfl) ⟨69494, by rfl⟩) R138989
theorem R92675 : Reach 92675 := rs (se 1 (by rfl) ⟨69506, by rfl⟩) R139013
theorem R813581 : Reach 813581 := rs (se 3 (by rfl) ⟨152546, by rfl⟩) R305093
theorem R92691 : Reach 92691 := rs (se 1 (by rfl) ⟨69518, by rfl⟩) R139037
theorem R92707 : Reach 92707 := rs (se 1 (by rfl) ⟨69530, by rfl⟩) R139061
theorem R92723 : Reach 92723 := rs (se 1 (by rfl) ⟨69542, by rfl⟩) R139085
theorem R92739 : Reach 92739 := rs (se 1 (by rfl) ⟨69554, by rfl⟩) R139109
theorem R92755 : Reach 92755 := rs (se 1 (by rfl) ⟨69566, by rfl⟩) R139133
theorem R92771 : Reach 92771 := rs (se 1 (by rfl) ⟨69578, by rfl⟩) R139157
theorem R158321 : Reach 158321 := rs (se 2 (by rfl) ⟨59370, by rfl⟩) R118741
theorem R92787 : Reach 92787 := rs (se 1 (by rfl) ⟨69590, by rfl⟩) R139181
theorem R92803 : Reach 92803 := rs (se 1 (by rfl) ⟨69602, by rfl⟩) R139205
theorem R92819 : Reach 92819 := rs (se 1 (by rfl) ⟨69614, by rfl⟩) R139229
theorem R92835 : Reach 92835 := rs (se 1 (by rfl) ⟨69626, by rfl⟩) R139253
theorem R92851 : Reach 92851 := rs (se 1 (by rfl) ⟨69638, by rfl⟩) R139277
theorem R125633 : Reach 125633 := rs (se 2 (by rfl) ⟨47112, by rfl⟩) R94225
theorem R92867 : Reach 92867 := rs (se 1 (by rfl) ⟨69650, by rfl⟩) R139301
theorem R92883 : Reach 92883 := rs (se 1 (by rfl) ⟨69662, by rfl⟩) R139325
theorem R92899 : Reach 92899 := rs (se 1 (by rfl) ⟨69674, by rfl⟩) R139349
theorem R158449 : Reach 158449 := rs (se 2 (by rfl) ⟨59418, by rfl⟩) R118837
theorem R92915 : Reach 92915 := rs (se 1 (by rfl) ⟨69686, by rfl⟩) R139373
theorem R92931 : Reach 92931 := rs (se 1 (by rfl) ⟨69698, by rfl⟩) R139397
theorem R92947 : Reach 92947 := rs (se 1 (by rfl) ⟨69710, by rfl⟩) R139421
theorem R158483 : Reach 158483 := rs (se 1 (by rfl) ⟨118862, by rfl⟩) R237725
theorem R92963 : Reach 92963 := rs (se 1 (by rfl) ⟨69722, by rfl⟩) R139445
theorem R92979 : Reach 92979 := rs (se 1 (by rfl) ⟨69734, by rfl⟩) R139469
theorem R92995 : Reach 92995 := rs (se 1 (by rfl) ⟨69746, by rfl⟩) R139493
theorem R93011 : Reach 93011 := rs (se 1 (by rfl) ⟨69758, by rfl⟩) R139517
theorem R93027 : Reach 93027 := rs (se 1 (by rfl) ⟨69770, by rfl⟩) R139541
theorem R93043 : Reach 93043 := rs (se 1 (by rfl) ⟨69782, by rfl⟩) R139565
theorem R93059 : Reach 93059 := rs (se 1 (by rfl) ⟨69794, by rfl⟩) R139589
theorem R93075 : Reach 93075 := rs (se 1 (by rfl) ⟨69806, by rfl⟩) R139613
theorem R158611 : Reach 158611 := rs (se 1 (by rfl) ⟨118958, by rfl⟩) R237917
theorem R93091 : Reach 93091 := rs (se 1 (by rfl) ⟨69818, by rfl⟩) R139637
theorem R93107 : Reach 93107 := rs (se 1 (by rfl) ⟨69830, by rfl⟩) R139661
theorem R93123 : Reach 93123 := rs (se 1 (by rfl) ⟨69842, by rfl⟩) R139685
theorem R93139 : Reach 93139 := rs (se 1 (by rfl) ⟨69854, by rfl⟩) R139709
theorem R93155 : Reach 93155 := rs (se 1 (by rfl) ⟨69866, by rfl⟩) R139733
theorem R93171 : Reach 93171 := rs (se 1 (by rfl) ⟨69878, by rfl⟩) R139757
theorem R93187 : Reach 93187 := rs (se 1 (by rfl) ⟨69890, by rfl⟩) R139781
theorem R93203 : Reach 93203 := rs (se 1 (by rfl) ⟨69902, by rfl⟩) R139805
theorem R158753 : Reach 158753 := rs (se 2 (by rfl) ⟨59532, by rfl⟩) R119065
theorem R93219 : Reach 93219 := rs (se 1 (by rfl) ⟨69914, by rfl⟩) R139829
theorem R93235 : Reach 93235 := rs (se 1 (by rfl) ⟨69926, by rfl⟩) R139853
theorem R93251 : Reach 93251 := rs (se 1 (by rfl) ⟨69938, by rfl⟩) R139877
theorem R93267 : Reach 93267 := rs (se 1 (by rfl) ⟨69950, by rfl⟩) R139901
theorem R93283 : Reach 93283 := rs (se 1 (by rfl) ⟨69962, by rfl⟩) R139925
theorem R93299 : Reach 93299 := rs (se 1 (by rfl) ⟨69974, by rfl⟩) R139949
theorem R93315 : Reach 93315 := rs (se 1 (by rfl) ⟨69986, by rfl⟩) R139973
theorem R93331 : Reach 93331 := rs (se 1 (by rfl) ⟨69998, by rfl⟩) R139997
theorem R158881 : Reach 158881 := rs (se 2 (by rfl) ⟨59580, by rfl⟩) R119161
theorem R93347 : Reach 93347 := rs (se 1 (by rfl) ⟨70010, by rfl⟩) R140021
theorem R93363 : Reach 93363 := rs (se 1 (by rfl) ⟨70022, by rfl⟩) R140045
theorem R93379 : Reach 93379 := rs (se 1 (by rfl) ⟨70034, by rfl⟩) R140069
theorem R158915 : Reach 158915 := rs (se 1 (by rfl) ⟨119186, by rfl⟩) R238373
theorem R93395 : Reach 93395 := rs (se 1 (by rfl) ⟨70046, by rfl⟩) R140093
theorem R93411 : Reach 93411 := rs (se 1 (by rfl) ⟨70058, by rfl⟩) R140117
theorem R93427 : Reach 93427 := rs (se 1 (by rfl) ⟨70070, by rfl⟩) R140141
theorem R93443 : Reach 93443 := rs (se 1 (by rfl) ⟨70082, by rfl⟩) R140165
theorem R93459 : Reach 93459 := rs (se 1 (by rfl) ⟨70094, by rfl⟩) R140189
theorem R3665173 : Reach 3665173 := rs (se 6 (by rfl) ⟨85902, by rfl⟩) R171805
theorem R93475 : Reach 93475 := rs (se 1 (by rfl) ⟨70106, by rfl⟩) R140213
theorem R93491 : Reach 93491 := rs (se 1 (by rfl) ⟨70118, by rfl⟩) R140237
theorem R93507 : Reach 93507 := rs (se 1 (by rfl) ⟨70130, by rfl⟩) R140261
theorem R159043 : Reach 159043 := rs (se 1 (by rfl) ⟨119282, by rfl⟩) R238565
theorem R355661 : Reach 355661 := rs (se 3 (by rfl) ⟨66686, by rfl⟩) R133373
theorem R93523 : Reach 93523 := rs (se 1 (by rfl) ⟨70142, by rfl⟩) R140285
theorem R93539 : Reach 93539 := rs (se 1 (by rfl) ⟨70154, by rfl⟩) R140309
theorem R93555 : Reach 93555 := rs (se 1 (by rfl) ⟨70166, by rfl⟩) R140333
theorem R93571 : Reach 93571 := rs (se 1 (by rfl) ⟨70178, by rfl⟩) R140357
theorem R93587 : Reach 93587 := rs (se 1 (by rfl) ⟨70190, by rfl⟩) R140381
theorem R93603 : Reach 93603 := rs (se 1 (by rfl) ⟨70202, by rfl⟩) R140405
theorem R93619 : Reach 93619 := rs (se 1 (by rfl) ⟨70214, by rfl⟩) R140429
theorem R93635 : Reach 93635 := rs (se 1 (by rfl) ⟨70226, by rfl⟩) R140453
theorem R159185 : Reach 159185 := rs (se 2 (by rfl) ⟨59694, by rfl⟩) R119389
theorem R93651 : Reach 93651 := rs (se 1 (by rfl) ⟨70238, by rfl⟩) R140477
theorem R93667 : Reach 93667 := rs (se 1 (by rfl) ⟨70250, by rfl⟩) R140501
theorem R93683 : Reach 93683 := rs (se 1 (by rfl) ⟨70262, by rfl⟩) R140525
theorem R93699 : Reach 93699 := rs (se 1 (by rfl) ⟨70274, by rfl⟩) R140549
theorem R93715 : Reach 93715 := rs (se 1 (by rfl) ⟨70286, by rfl⟩) R140573
theorem R93731 : Reach 93731 := rs (se 1 (by rfl) ⟨70298, by rfl⟩) R140597
theorem R93747 : Reach 93747 := rs (se 1 (by rfl) ⟨70310, by rfl⟩) R140621
theorem R93763 : Reach 93763 := rs (se 1 (by rfl) ⟨70322, by rfl⟩) R140645
theorem R159313 : Reach 159313 := rs (se 2 (by rfl) ⟨59742, by rfl⟩) R119485
theorem R93779 : Reach 93779 := rs (se 1 (by rfl) ⟨70334, by rfl⟩) R140669
theorem R93795 : Reach 93795 := rs (se 1 (by rfl) ⟨70346, by rfl⟩) R140693
theorem R93811 : Reach 93811 := rs (se 1 (by rfl) ⟨70358, by rfl⟩) R140717
theorem R159347 : Reach 159347 := rs (se 1 (by rfl) ⟨119510, by rfl⟩) R239021
theorem R93827 : Reach 93827 := rs (se 1 (by rfl) ⟨70370, by rfl⟩) R140741
theorem R93843 : Reach 93843 := rs (se 1 (by rfl) ⟨70382, by rfl⟩) R140765
theorem R93859 : Reach 93859 := rs (se 1 (by rfl) ⟨70394, by rfl⟩) R140789
theorem R93875 : Reach 93875 := rs (se 1 (by rfl) ⟨70406, by rfl⟩) R140813
theorem R93891 : Reach 93891 := rs (se 1 (by rfl) ⟨70418, by rfl⟩) R140837
theorem R93907 : Reach 93907 := rs (se 1 (by rfl) ⟨70430, by rfl⟩) R140861
theorem R93923 : Reach 93923 := rs (se 1 (by rfl) ⟨70442, by rfl⟩) R140885
theorem R93939 : Reach 93939 := rs (se 1 (by rfl) ⟨70454, by rfl⟩) R140909
theorem R159475 : Reach 159475 := rs (se 1 (by rfl) ⟨119606, by rfl⟩) R239213
theorem R93955 : Reach 93955 := rs (se 1 (by rfl) ⟨70466, by rfl⟩) R140933
theorem R93971 : Reach 93971 := rs (se 1 (by rfl) ⟨70478, by rfl⟩) R140957
theorem R93987 : Reach 93987 := rs (se 1 (by rfl) ⟨70490, by rfl⟩) R140981
theorem R94003 : Reach 94003 := rs (se 1 (by rfl) ⟨70502, by rfl⟩) R141005
theorem R126785 : Reach 126785 := rs (se 2 (by rfl) ⟨47544, by rfl⟩) R95089
theorem R94019 : Reach 94019 := rs (se 1 (by rfl) ⟨70514, by rfl⟩) R141029
theorem R94035 : Reach 94035 := rs (se 1 (by rfl) ⟨70526, by rfl⟩) R141053
theorem R94051 : Reach 94051 := rs (se 1 (by rfl) ⟨70538, by rfl⟩) R141077
theorem R94067 : Reach 94067 := rs (se 1 (by rfl) ⟨70550, by rfl⟩) R141101
theorem R159617 : Reach 159617 := rs (se 2 (by rfl) ⟨59856, by rfl⟩) R119713
theorem R94083 : Reach 94083 := rs (se 1 (by rfl) ⟨70562, by rfl⟩) R141125
theorem R94099 : Reach 94099 := rs (se 1 (by rfl) ⟨70574, by rfl⟩) R141149
theorem R94115 : Reach 94115 := rs (se 1 (by rfl) ⟨70586, by rfl⟩) R141173
theorem R94131 : Reach 94131 := rs (se 1 (by rfl) ⟨70598, by rfl⟩) R141197
theorem R94147 : Reach 94147 := rs (se 1 (by rfl) ⟨70610, by rfl⟩) R141221
theorem R520141 : Reach 520141 := rs (se 3 (by rfl) ⟨97526, by rfl⟩) R195053
theorem R94163 : Reach 94163 := rs (se 1 (by rfl) ⟨70622, by rfl⟩) R141245
theorem R126947 : Reach 126947 := rs (se 1 (by rfl) ⟨95210, by rfl⟩) R190421
theorem R94179 : Reach 94179 := rs (se 1 (by rfl) ⟨70634, by rfl⟩) R141269
theorem R94195 : Reach 94195 := rs (se 1 (by rfl) ⟨70646, by rfl⟩) R141293
theorem R159745 : Reach 159745 := rs (se 2 (by rfl) ⟨59904, by rfl⟩) R119809
theorem R94211 : Reach 94211 := rs (se 1 (by rfl) ⟨70658, by rfl⟩) R141317
theorem R94227 : Reach 94227 := rs (se 1 (by rfl) ⟨70670, by rfl⟩) R141341
theorem R94243 : Reach 94243 := rs (se 1 (by rfl) ⟨70682, by rfl⟩) R141365
theorem R159779 : Reach 159779 := rs (se 1 (by rfl) ⟨119834, by rfl⟩) R239669
theorem R94259 : Reach 94259 := rs (se 1 (by rfl) ⟨70694, by rfl⟩) R141389
theorem R94275 : Reach 94275 := rs (se 1 (by rfl) ⟨70706, by rfl⟩) R141413
theorem R94291 : Reach 94291 := rs (se 1 (by rfl) ⟨70718, by rfl⟩) R141437
theorem R94307 : Reach 94307 := rs (se 1 (by rfl) ⟨70730, by rfl⟩) R141461
theorem R192611 : Reach 192611 := rs (se 1 (by rfl) ⟨144458, by rfl⟩) R288917
theorem R323693 : Reach 323693 := rs (se 3 (by rfl) ⟨60692, by rfl⟩) R121385
theorem R94323 : Reach 94323 := rs (se 1 (by rfl) ⟨70742, by rfl⟩) R141485
theorem R94339 : Reach 94339 := rs (se 1 (by rfl) ⟨70754, by rfl⟩) R141509
theorem R1667213 : Reach 1667213 := rs (se 3 (by rfl) ⟨312602, by rfl⟩) R625205
theorem R94355 : Reach 94355 := rs (se 1 (by rfl) ⟨70766, by rfl⟩) R141533
theorem R94371 : Reach 94371 := rs (se 1 (by rfl) ⟨70778, by rfl⟩) R141557
theorem R159907 : Reach 159907 := rs (se 1 (by rfl) ⟨119930, by rfl⟩) R239861
theorem R94387 : Reach 94387 := rs (se 1 (by rfl) ⟨70790, by rfl⟩) R141581
theorem R94403 : Reach 94403 := rs (se 1 (by rfl) ⟨70802, by rfl⟩) R141605
theorem R94419 : Reach 94419 := rs (se 1 (by rfl) ⟨70814, by rfl⟩) R141629
theorem R94435 : Reach 94435 := rs (se 1 (by rfl) ⟨70826, by rfl⟩) R141653
theorem R94451 : Reach 94451 := rs (se 1 (by rfl) ⟨70838, by rfl⟩) R141677
theorem R94467 : Reach 94467 := rs (se 1 (by rfl) ⟨70850, by rfl⟩) R141701
theorem R94483 : Reach 94483 := rs (se 1 (by rfl) ⟨70862, by rfl⟩) R141725
theorem R94499 : Reach 94499 := rs (se 1 (by rfl) ⟨70874, by rfl⟩) R141749
theorem R160049 : Reach 160049 := rs (se 2 (by rfl) ⟨60018, by rfl⟩) R120037
theorem R94515 : Reach 94515 := rs (se 1 (by rfl) ⟨70886, by rfl⟩) R141773
theorem R94531 : Reach 94531 := rs (se 1 (by rfl) ⟨70898, by rfl⟩) R141797
theorem R94547 : Reach 94547 := rs (se 1 (by rfl) ⟨70910, by rfl⟩) R141821
theorem R94563 : Reach 94563 := rs (se 1 (by rfl) ⟨70922, by rfl⟩) R141845
theorem R94579 : Reach 94579 := rs (se 1 (by rfl) ⟨70934, by rfl⟩) R141869
theorem R94595 : Reach 94595 := rs (se 1 (by rfl) ⟨70946, by rfl⟩) R141893
theorem R94611 : Reach 94611 := rs (se 1 (by rfl) ⟨70958, by rfl⟩) R141917
theorem R94627 : Reach 94627 := rs (se 1 (by rfl) ⟨70970, by rfl⟩) R141941
theorem R160177 : Reach 160177 := rs (se 2 (by rfl) ⟨60066, by rfl⟩) R120133
theorem R94643 : Reach 94643 := rs (se 1 (by rfl) ⟨70982, by rfl⟩) R141965
theorem R94659 : Reach 94659 := rs (se 1 (by rfl) ⟨70994, by rfl⟩) R141989
theorem R160211 : Reach 160211 := rs (se 1 (by rfl) ⟨120158, by rfl⟩) R240317
theorem R94675 : Reach 94675 := rs (se 1 (by rfl) ⟨71006, by rfl⟩) R142013
theorem R94691 : Reach 94691 := rs (se 1 (by rfl) ⟨71018, by rfl⟩) R142037
theorem R94707 : Reach 94707 := rs (se 1 (by rfl) ⟨71030, by rfl⟩) R142061
theorem R94723 : Reach 94723 := rs (se 1 (by rfl) ⟨71042, by rfl⟩) R142085
theorem R94739 : Reach 94739 := rs (se 1 (by rfl) ⟨71054, by rfl⟩) R142109
theorem R94755 : Reach 94755 := rs (se 1 (by rfl) ⟨71066, by rfl⟩) R142133
theorem R389681 : Reach 389681 := rs (se 2 (by rfl) ⟨146130, by rfl⟩) R292261
theorem R94771 : Reach 94771 := rs (se 1 (by rfl) ⟨71078, by rfl⟩) R142157
theorem R94787 : Reach 94787 := rs (se 1 (by rfl) ⟨71090, by rfl⟩) R142181
theorem R94803 : Reach 94803 := rs (se 1 (by rfl) ⟨71102, by rfl⟩) R142205
theorem R160339 : Reach 160339 := rs (se 1 (by rfl) ⟨120254, by rfl⟩) R240509
theorem R127585 : Reach 127585 := rs (se 2 (by rfl) ⟨47844, by rfl⟩) R95689
theorem R389731 : Reach 389731 := rs (se 1 (by rfl) ⟨292298, by rfl⟩) R584597
theorem R94819 : Reach 94819 := rs (se 1 (by rfl) ⟨71114, by rfl⟩) R142229
theorem R488035 : Reach 488035 := rs (se 1 (by rfl) ⟨366026, by rfl⟩) R732053
theorem R94835 : Reach 94835 := rs (se 1 (by rfl) ⟨71126, by rfl⟩) R142253
theorem R94851 : Reach 94851 := rs (se 1 (by rfl) ⟨71138, by rfl⟩) R142277
theorem R94867 : Reach 94867 := rs (se 1 (by rfl) ⟨71150, by rfl⟩) R142301
theorem R94883 : Reach 94883 := rs (se 1 (by rfl) ⟨71162, by rfl⟩) R142325
theorem R94899 : Reach 94899 := rs (se 1 (by rfl) ⟨71174, by rfl⟩) R142349
theorem R94915 : Reach 94915 := rs (se 1 (by rfl) ⟨71186, by rfl⟩) R142373
theorem R94931 : Reach 94931 := rs (se 1 (by rfl) ⟨71198, by rfl⟩) R142397
theorem R160481 : Reach 160481 := rs (se 2 (by rfl) ⟨60180, by rfl⟩) R120361
theorem R94947 : Reach 94947 := rs (se 1 (by rfl) ⟨71210, by rfl⟩) R142421
theorem R94963 : Reach 94963 := rs (se 1 (by rfl) ⟨71222, by rfl⟩) R142445
theorem R94979 : Reach 94979 := rs (se 1 (by rfl) ⟨71234, by rfl⟩) R142469
theorem R94995 : Reach 94995 := rs (se 1 (by rfl) ⟨71246, by rfl⟩) R142493
theorem R95011 : Reach 95011 := rs (se 1 (by rfl) ⟨71258, by rfl⟩) R142517
theorem R95027 : Reach 95027 := rs (se 1 (by rfl) ⟨71270, by rfl⟩) R142541
theorem R95043 : Reach 95043 := rs (se 1 (by rfl) ⟨71282, by rfl⟩) R142565
theorem R95059 : Reach 95059 := rs (se 1 (by rfl) ⟨71294, by rfl⟩) R142589
theorem R586595 : Reach 586595 := rs (se 1 (by rfl) ⟨439946, by rfl⟩) R879893
theorem R95075 : Reach 95075 := rs (se 1 (by rfl) ⟨71306, by rfl⟩) R142613
theorem R95091 : Reach 95091 := rs (se 1 (by rfl) ⟨71318, by rfl⟩) R142637
theorem R95107 : Reach 95107 := rs (se 1 (by rfl) ⟨71330, by rfl⟩) R142661
theorem R95123 : Reach 95123 := rs (se 1 (by rfl) ⟨71342, by rfl⟩) R142685
theorem R127985 : Reach 127985 := rs (se 2 (by rfl) ⟨47994, by rfl⟩) R95989
theorem R324593 : Reach 324593 := rs (se 2 (by rfl) ⟨121722, by rfl⟩) R243445
theorem R128099 : Reach 128099 := rs (se 1 (by rfl) ⟨96074, by rfl⟩) R192149
theorem R193745 : Reach 193745 := rs (se 2 (by rfl) ⟨72654, by rfl⟩) R145309
theorem R423139 : Reach 423139 := rs (se 1 (by rfl) ⟨317354, by rfl⟩) R634709
theorem R226577 : Reach 226577 := rs (se 2 (by rfl) ⟨84966, by rfl⟩) R169933
theorem R718307 : Reach 718307 := rs (se 1 (by rfl) ⟨538730, by rfl⟩) R1077461
theorem R259661 : Reach 259661 := rs (se 3 (by rfl) ⟨48686, by rfl⟩) R97373
theorem R259843 : Reach 259843 := rs (se 1 (by rfl) ⟨194882, by rfl⟩) R389765
theorem R161633 : Reach 161633 := rs (se 2 (by rfl) ⟨60612, by rfl⟩) R121225
theorem R96115 : Reach 96115 := rs (se 1 (by rfl) ⟨72086, by rfl⟩) R144173
theorem R522125 : Reach 522125 := rs (se 3 (by rfl) ⟨97898, by rfl⟩) R195797
theorem R260003 : Reach 260003 := rs (se 1 (by rfl) ⟨195002, by rfl⟩) R390005
theorem R1177699 : Reach 1177699 := rs (se 1 (by rfl) ⟨883274, by rfl⟩) R1766549
theorem R1734797 : Reach 1734797 := rs (se 3 (by rfl) ⟨325274, by rfl⟩) R650549
theorem R358577 : Reach 358577 := rs (se 2 (by rfl) ⟨134466, by rfl⟩) R268933
theorem R195139 : Reach 195139 := rs (se 1 (by rfl) ⟨146354, by rfl⟩) R292709
theorem R293453 : Reach 293453 := rs (se 3 (by rfl) ⟨55022, by rfl⟩) R110045
theorem R523057 : Reach 523057 := rs (se 2 (by rfl) ⟨196146, by rfl⟩) R392293
theorem R392141 : Reach 392141 := rs (se 3 (by rfl) ⟨73526, by rfl⟩) R147053
theorem R261073 : Reach 261073 := rs (se 2 (by rfl) ⟨97902, by rfl⟩) R195805
theorem R130081 : Reach 130081 := rs (se 2 (by rfl) ⟨48780, by rfl⟩) R97561
theorem R130195 : Reach 130195 := rs (se 1 (by rfl) ⟨97646, by rfl⟩) R195293
theorem R294349 : Reach 294349 := rs (se 3 (by rfl) ⟨55190, by rfl⟩) R110381
theorem R97843 : Reach 97843 := rs (se 1 (by rfl) ⟨73382, by rfl⟩) R146765
theorem R1408565 : Reach 1408565 := rs (se 5 (by rfl) ⟨66026, by rfl⟩) R132053
theorem R360035 : Reach 360035 := rs (se 1 (by rfl) ⟨270026, by rfl⟩) R540053
theorem R327523 : Reach 327523 := rs (se 1 (by rfl) ⟨245642, by rfl⟩) R491285
theorem R131095 : Reach 131095 := rs (se 1 (by rfl) ⟨98321, by rfl⟩) R196643
theorem R524333 : Reach 524333 := rs (se 3 (by rfl) ⟨98312, by rfl⟩) R196625
theorem R196823 : Reach 196823 := rs (se 1 (by rfl) ⟨147617, by rfl⟩) R295235
theorem R721709 : Reach 721709 := rs (se 3 (by rfl) ⟨135320, by rfl⟩) R270641
theorem R131915 : Reach 131915 := rs (se 1 (by rfl) ⟨98936, by rfl⟩) R197873
theorem R99415 : Reach 99415 := rs (se 1 (by rfl) ⟨74561, by rfl⟩) R149123
theorem R427315 : Reach 427315 := rs (se 1 (by rfl) ⟨320486, by rfl⟩) R640973
theorem R1344869 : Reach 1344869 := rs (se 4 (by rfl) ⟨126081, by rfl⟩) R252163
theorem R198283 : Reach 198283 := rs (se 1 (by rfl) ⟨148712, by rfl⟩) R297425
theorem R722819 : Reach 722819 := rs (se 1 (by rfl) ⟨542114, by rfl⟩) R1084229
theorem R198539 : Reach 198539 := rs (se 1 (by rfl) ⟨148904, by rfl⟩) R297809
theorem R100235 : Reach 100235 := rs (se 1 (by rfl) ⟨75176, by rfl⟩) R150353
theorem R329645 : Reach 329645 := rs (se 3 (by rfl) ⟨61808, by rfl⟩) R123617
theorem R526297 : Reach 526297 := rs (se 2 (by rfl) ⟨197361, by rfl⟩) R394723
theorem R100363 : Reach 100363 := rs (se 1 (by rfl) ⟨75272, by rfl⟩) R150545
theorem R264343 : Reach 264343 := rs (se 1 (by rfl) ⟨198257, by rfl⟩) R396515
theorem R395437 : Reach 395437 := rs (se 3 (by rfl) ⟨74144, by rfl⟩) R148289
theorem R231731 : Reach 231731 := rs (se 1 (by rfl) ⟨173798, by rfl⟩) R347597
theorem R395779 : Reach 395779 := rs (se 1 (by rfl) ⟨296834, by rfl⟩) R593669
theorem R232267 : Reach 232267 := rs (se 1 (by rfl) ⟨174200, by rfl⟩) R348401
theorem R199513 : Reach 199513 := rs (se 2 (by rfl) ⟨74817, by rfl⟩) R149635
theorem R461699 : Reach 461699 := rs (se 1 (by rfl) ⟨346274, by rfl⟩) R692549
theorem R330641 : Reach 330641 := rs (se 2 (by rfl) ⟨123990, by rfl⟩) R247981
theorem R232409 : Reach 232409 := rs (se 2 (by rfl) ⟨87153, by rfl⟩) R174307
theorem R199667 : Reach 199667 := rs (se 1 (by rfl) ⟨149750, by rfl⟩) R299501
theorem R199883 : Reach 199883 := rs (se 1 (by rfl) ⟨149912, by rfl⟩) R299825
theorem R396737 : Reach 396737 := rs (se 2 (by rfl) ⟨148776, by rfl⟩) R297553
theorem R265675 : Reach 265675 := rs (se 1 (by rfl) ⟨199256, by rfl⟩) R398513
theorem R200179 : Reach 200179 := rs (se 1 (by rfl) ⟨150134, by rfl⟩) R300269
theorem R265949 : Reach 265949 := rs (se 3 (by rfl) ⟨49865, by rfl⟩) R99731
theorem R233239 : Reach 233239 := rs (se 1 (by rfl) ⟨174929, by rfl⟩) R349859
theorem R331793 : Reach 331793 := rs (se 2 (by rfl) ⟨124422, by rfl⟩) R248845
theorem R1609763 : Reach 1609763 := rs (se 1 (by rfl) ⟨1207322, by rfl⟩) R2414645
theorem R266291 : Reach 266291 := rs (se 1 (by rfl) ⟨199718, by rfl⟩) R399437
theorem R364675 : Reach 364675 := rs (se 1 (by rfl) ⟨273506, by rfl⟩) R547013
theorem R200855 : Reach 200855 := rs (se 1 (by rfl) ⟨150641, by rfl⟩) R301283
theorem R200897 : Reach 200897 := rs (se 2 (by rfl) ⟨75336, by rfl⟩) R150673
theorem R233675 : Reach 233675 := rs (se 1 (by rfl) ⟨175256, by rfl⟩) R350513
theorem R102667 : Reach 102667 := rs (se 1 (by rfl) ⟨77000, by rfl⟩) R154001
theorem R168203 : Reach 168203 := rs (se 1 (by rfl) ⟨126152, by rfl⟩) R252305
theorem R4886897 : Reach 4886897 := rs (se 2 (by rfl) ⟨1832586, by rfl⟩) R3665173
theorem R102775 : Reach 102775 := rs (se 1 (by rfl) ⟨77081, by rfl⟩) R154163
theorem R102955 : Reach 102955 := rs (se 1 (by rfl) ⟨77216, by rfl⟩) R154433
theorem R234049 : Reach 234049 := rs (se 2 (by rfl) ⟨87768, by rfl⟩) R175537
theorem R103063 : Reach 103063 := rs (se 1 (by rfl) ⟨77297, by rfl⟩) R154595
theorem R103243 : Reach 103243 := rs (se 1 (by rfl) ⟨77432, by rfl⟩) R154865
theorem R398155 : Reach 398155 := rs (se 1 (by rfl) ⟨298616, by rfl⟩) R597233
theorem R431021 : Reach 431021 := rs (se 3 (by rfl) ⟨80816, by rfl⟩) R161633
theorem R103351 : Reach 103351 := rs (se 1 (by rfl) ⟨77513, by rfl⟩) R155027
theorem R398429 : Reach 398429 := rs (se 3 (by rfl) ⟨74705, by rfl⟩) R149411
theorem R103531 : Reach 103531 := rs (se 1 (by rfl) ⟨77648, by rfl⟩) R155297
theorem R660611 : Reach 660611 := rs (se 1 (by rfl) ⟨495458, by rfl⟩) R990917
theorem R234647 : Reach 234647 := rs (se 1 (by rfl) ⟨175985, by rfl⟩) R351971
theorem R103639 : Reach 103639 := rs (se 1 (by rfl) ⟨77729, by rfl⟩) R155459
theorem R693521 : Reach 693521 := rs (se 2 (by rfl) ⟨260070, by rfl⟩) R520141
theorem R103819 : Reach 103819 := rs (se 1 (by rfl) ⟨77864, by rfl⟩) R155729
theorem R103927 : Reach 103927 := rs (se 1 (by rfl) ⟨77945, by rfl⟩) R155891
theorem R136715 : Reach 136715 := rs (se 1 (by rfl) ⟨102536, by rfl⟩) R205073
theorem R136727 : Reach 136727 := rs (se 1 (by rfl) ⟨102545, by rfl⟩) R205091
theorem R333335 : Reach 333335 := rs (se 1 (by rfl) ⟨250001, by rfl⟩) R500003
theorem R136793 : Reach 136793 := rs (se 2 (by rfl) ⟨51297, by rfl⟩) R102595
theorem R104107 : Reach 104107 := rs (se 1 (by rfl) ⟨78080, by rfl⟩) R156161
theorem R169651 : Reach 169651 := rs (se 1 (by rfl) ⟨127238, by rfl⟩) R254477
theorem R136907 : Reach 136907 := rs (se 1 (by rfl) ⟨102680, by rfl⟩) R205361
theorem R136919 : Reach 136919 := rs (se 1 (by rfl) ⟨102689, by rfl⟩) R205379
theorem R104215 : Reach 104215 := rs (se 1 (by rfl) ⟨78161, by rfl⟩) R156323
theorem R136985 : Reach 136985 := rs (se 2 (by rfl) ⟨51369, by rfl⟩) R102739
theorem R137099 : Reach 137099 := rs (se 1 (by rfl) ⟨102824, by rfl⟩) R205649
theorem R137111 : Reach 137111 := rs (se 1 (by rfl) ⟨102833, by rfl⟩) R205667
theorem R235457 : Reach 235457 := rs (se 2 (by rfl) ⟨88296, by rfl⟩) R176593
theorem R104395 : Reach 104395 := rs (se 1 (by rfl) ⟨78296, by rfl⟩) R156593
theorem R137177 : Reach 137177 := rs (se 2 (by rfl) ⟨51441, by rfl⟩) R102883
theorem R333827 : Reach 333827 := rs (se 1 (by rfl) ⟨250370, by rfl⟩) R500741
theorem R923665 : Reach 923665 := rs (se 2 (by rfl) ⟨346374, by rfl⟩) R692749
theorem R104503 : Reach 104503 := rs (se 1 (by rfl) ⟨78377, by rfl⟩) R156755
theorem R5150789 : Reach 5150789 := rs (se 4 (by rfl) ⟨482886, by rfl⟩) R965773
theorem R137291 : Reach 137291 := rs (se 1 (by rfl) ⟨102968, by rfl⟩) R205937
theorem R268363 : Reach 268363 := rs (se 1 (by rfl) ⟨201272, by rfl⟩) R402545
theorem R137303 : Reach 137303 := rs (se 1 (by rfl) ⟨102977, by rfl⟩) R205955
theorem R170113 : Reach 170113 := rs (se 2 (by rfl) ⟨63792, by rfl⟩) R127585
theorem R137369 : Reach 137369 := rs (se 2 (by rfl) ⟨51513, by rfl⟩) R103027
theorem R104683 : Reach 104683 := rs (se 1 (by rfl) ⟨78512, by rfl⟩) R157025
theorem R661765 : Reach 661765 := rs (se 4 (by rfl) ⟨62040, by rfl⟩) R124081
theorem R137483 : Reach 137483 := rs (se 1 (by rfl) ⟨103112, by rfl⟩) R206225
theorem R137495 : Reach 137495 := rs (se 1 (by rfl) ⟨103121, by rfl⟩) R206243
theorem R203033 : Reach 203033 := rs (se 2 (by rfl) ⟨76137, by rfl⟩) R152275
theorem R268609 : Reach 268609 := rs (se 2 (by rfl) ⟨100728, by rfl⟩) R201457
theorem R104791 : Reach 104791 := rs (se 1 (by rfl) ⟨78593, by rfl⟩) R157187
theorem R137561 : Reach 137561 := rs (se 2 (by rfl) ⟨51585, by rfl⟩) R103171
theorem R137675 : Reach 137675 := rs (se 1 (by rfl) ⟨103256, by rfl⟩) R206513
theorem R137687 : Reach 137687 := rs (se 1 (by rfl) ⟨103265, by rfl⟩) R206531
theorem R235993 : Reach 235993 := rs (se 2 (by rfl) ⟨88497, by rfl⟩) R176995
theorem R104971 : Reach 104971 := rs (se 1 (by rfl) ⟨78728, by rfl⟩) R157457
theorem R465425 : Reach 465425 := rs (se 2 (by rfl) ⟨174534, by rfl⟩) R349069
theorem R137753 : Reach 137753 := rs (se 2 (by rfl) ⟨51657, by rfl⟩) R103315
theorem R268865 : Reach 268865 := rs (se 2 (by rfl) ⟨100824, by rfl⟩) R201649
theorem R105079 : Reach 105079 := rs (se 1 (by rfl) ⟨78809, by rfl⟩) R157619
theorem R137867 : Reach 137867 := rs (se 1 (by rfl) ⟨103400, by rfl⟩) R206801
theorem R137879 : Reach 137879 := rs (se 1 (by rfl) ⟨103409, by rfl⟩) R206819
theorem R465587 : Reach 465587 := rs (se 1 (by rfl) ⟨349190, by rfl⟩) R698381
theorem R170675 : Reach 170675 := rs (se 1 (by rfl) ⟨128006, by rfl⟩) R256013
theorem R137945 : Reach 137945 := rs (se 2 (by rfl) ⟨51729, by rfl⟩) R103459
theorem R105259 : Reach 105259 := rs (se 1 (by rfl) ⟨78944, by rfl⟩) R157889
theorem R138059 : Reach 138059 := rs (se 1 (by rfl) ⟨103544, by rfl⟩) R207089
theorem R138071 : Reach 138071 := rs (se 1 (by rfl) ⟨103553, by rfl⟩) R207107
theorem R2235235 : Reach 2235235 := rs (se 1 (by rfl) ⟨1676426, by rfl⟩) R3352853
theorem R105367 : Reach 105367 := rs (se 1 (by rfl) ⟨79025, by rfl⟩) R158051
theorem R269207 : Reach 269207 := rs (se 1 (by rfl) ⟨201905, by rfl⟩) R403811
theorem R138137 : Reach 138137 := rs (se 2 (by rfl) ⟨51801, by rfl⟩) R103603
theorem R564185 : Reach 564185 := rs (se 2 (by rfl) ⟨211569, by rfl⟩) R423139
theorem R138251 : Reach 138251 := rs (se 1 (by rfl) ⟨103688, by rfl⟩) R207377
theorem R138263 : Reach 138263 := rs (se 1 (by rfl) ⟨103697, by rfl⟩) R207395
theorem R105547 : Reach 105547 := rs (se 1 (by rfl) ⟨79160, by rfl⟩) R158321
theorem R138329 : Reach 138329 := rs (se 2 (by rfl) ⟨51873, by rfl⟩) R103747
theorem R335021 : Reach 335021 := rs (se 3 (by rfl) ⟨62816, by rfl⟩) R125633
theorem R105655 : Reach 105655 := rs (se 1 (by rfl) ⟨79241, by rfl⟩) R158483
theorem R138443 : Reach 138443 := rs (se 1 (by rfl) ⟨103832, by rfl⟩) R207665
theorem R138455 : Reach 138455 := rs (se 1 (by rfl) ⟨103841, by rfl⟩) R207683
theorem R138521 : Reach 138521 := rs (se 2 (by rfl) ⟨51945, by rfl⟩) R103891
theorem R531805 : Reach 531805 := rs (se 3 (by rfl) ⟨99713, by rfl⟩) R199427
theorem R105835 : Reach 105835 := rs (se 1 (by rfl) ⟨79376, by rfl⟩) R158753
theorem R138635 : Reach 138635 := rs (se 1 (by rfl) ⟨103976, by rfl⟩) R207953
theorem R138647 : Reach 138647 := rs (se 1 (by rfl) ⟨103985, by rfl⟩) R207971
theorem R105943 : Reach 105943 := rs (se 1 (by rfl) ⟨79457, by rfl⟩) R158915
theorem R138713 : Reach 138713 := rs (se 2 (by rfl) ⟨52017, by rfl⟩) R104035
theorem R237107 : Reach 237107 := rs (se 1 (by rfl) ⟨177830, by rfl⟩) R355661
theorem R138827 : Reach 138827 := rs (se 1 (by rfl) ⟨104120, by rfl⟩) R208241
theorem R138839 : Reach 138839 := rs (se 1 (by rfl) ⟨104129, by rfl⟩) R208259
theorem R106123 : Reach 106123 := rs (se 1 (by rfl) ⟨79592, by rfl⟩) R159185
theorem R401041 : Reach 401041 := rs (se 2 (by rfl) ⟨150390, by rfl⟩) R300781
theorem R204439 : Reach 204439 := rs (se 1 (by rfl) ⟨153329, by rfl⟩) R306659
theorem R138905 : Reach 138905 := rs (se 2 (by rfl) ⟨52089, by rfl⟩) R104179
theorem R106231 : Reach 106231 := rs (se 1 (by rfl) ⟨79673, by rfl⟩) R159347
theorem R139019 : Reach 139019 := rs (se 1 (by rfl) ⟨104264, by rfl⟩) R208529
theorem R139031 : Reach 139031 := rs (se 1 (by rfl) ⟨104273, by rfl⟩) R208547
theorem R139097 : Reach 139097 := rs (se 2 (by rfl) ⟨52161, by rfl⟩) R104323
theorem R237401 : Reach 237401 := rs (se 2 (by rfl) ⟨89025, by rfl⟩) R178051
theorem R106411 : Reach 106411 := rs (se 1 (by rfl) ⟨79808, by rfl⟩) R159617
theorem R139211 : Reach 139211 := rs (se 1 (by rfl) ⟨104408, by rfl⟩) R208817
theorem R139223 : Reach 139223 := rs (se 1 (by rfl) ⟨104417, by rfl⟩) R208835
theorem R892889 : Reach 892889 := rs (se 2 (by rfl) ⟨334833, by rfl⟩) R669667
theorem R1023961 : Reach 1023961 := rs (se 2 (by rfl) ⟨383985, by rfl⟩) R767971
theorem R106519 : Reach 106519 := rs (se 1 (by rfl) ⟨79889, by rfl⟩) R159779
theorem R139289 : Reach 139289 := rs (se 2 (by rfl) ⟨52233, by rfl⟩) R104467
theorem R139403 : Reach 139403 := rs (se 1 (by rfl) ⟨104552, by rfl⟩) R209105
theorem R139415 : Reach 139415 := rs (se 1 (by rfl) ⟨104561, by rfl⟩) R209123
theorem R1614005 : Reach 1614005 := rs (se 5 (by rfl) ⟨75656, by rfl⟩) R151313
theorem R106699 : Reach 106699 := rs (se 1 (by rfl) ⟨80024, by rfl⟩) R160049
theorem R139481 : Reach 139481 := rs (se 2 (by rfl) ⟨52305, by rfl⟩) R104611
theorem R106807 : Reach 106807 := rs (se 1 (by rfl) ⟨80105, by rfl⟩) R160211
theorem R139595 : Reach 139595 := rs (se 1 (by rfl) ⟨104696, by rfl⟩) R209393
theorem R139607 : Reach 139607 := rs (se 1 (by rfl) ⟨104705, by rfl⟩) R209411
theorem R205145 : Reach 205145 := rs (se 2 (by rfl) ⟨76929, by rfl⟩) R153859
theorem R139673 : Reach 139673 := rs (se 2 (by rfl) ⟨52377, by rfl⟩) R104755
theorem R205235 : Reach 205235 := rs (se 1 (by rfl) ⟨153926, by rfl⟩) R307853
theorem R205271 : Reach 205271 := rs (se 1 (by rfl) ⟨153953, by rfl⟩) R307907
theorem R106987 : Reach 106987 := rs (se 1 (by rfl) ⟨80240, by rfl⟩) R160481
theorem R139787 : Reach 139787 := rs (se 1 (by rfl) ⟨104840, by rfl⟩) R209681
theorem R139799 : Reach 139799 := rs (se 1 (by rfl) ⟨104849, by rfl⟩) R209699
theorem R205337 : Reach 205337 := rs (se 2 (by rfl) ⟨77001, by rfl⟩) R154003
theorem R336449 : Reach 336449 := rs (se 2 (by rfl) ⟨126168, by rfl⟩) R252337
theorem R467531 : Reach 467531 := rs (se 1 (by rfl) ⟨350648, by rfl⟩) R701297
theorem R139865 : Reach 139865 := rs (se 2 (by rfl) ⟨52449, by rfl⟩) R104899
theorem R205451 : Reach 205451 := rs (se 1 (by rfl) ⟨154088, by rfl⟩) R308177
theorem R205505 : Reach 205505 := rs (se 2 (by rfl) ⟨77064, by rfl⟩) R154129
theorem R139979 : Reach 139979 := rs (se 1 (by rfl) ⟨104984, by rfl⟩) R209969
theorem R139991 : Reach 139991 := rs (se 1 (by rfl) ⟨104993, by rfl⟩) R209987
theorem R140057 : Reach 140057 := rs (se 2 (by rfl) ⟨52521, by rfl⟩) R105043
theorem R140171 : Reach 140171 := rs (se 1 (by rfl) ⟨105128, by rfl⟩) R210257
theorem R140183 : Reach 140183 := rs (se 1 (by rfl) ⟨105137, by rfl⟩) R210275
theorem R205721 : Reach 205721 := rs (se 2 (by rfl) ⟨77145, by rfl⟩) R154291
theorem R140249 : Reach 140249 := rs (se 2 (by rfl) ⟨52593, by rfl⟩) R105187
theorem R205811 : Reach 205811 := rs (se 1 (by rfl) ⟨154358, by rfl⟩) R308717
theorem R205847 : Reach 205847 := rs (se 1 (by rfl) ⟨154385, by rfl⟩) R308771
theorem R173107 : Reach 173107 := rs (se 1 (by rfl) ⟨129830, by rfl⟩) R259661
theorem R697409 : Reach 697409 := rs (se 2 (by rfl) ⟨261528, by rfl⟩) R523057
theorem R140363 : Reach 140363 := rs (se 1 (by rfl) ⟨105272, by rfl⟩) R210545
theorem R140375 : Reach 140375 := rs (se 1 (by rfl) ⟨105281, by rfl⟩) R210563
theorem R140441 : Reach 140441 := rs (se 2 (by rfl) ⟨52665, by rfl⟩) R105331
theorem R206027 : Reach 206027 := rs (se 1 (by rfl) ⟨154520, by rfl⟩) R309041
theorem R206081 : Reach 206081 := rs (se 2 (by rfl) ⟨77280, by rfl⟩) R154561
theorem R140555 : Reach 140555 := rs (se 1 (by rfl) ⟨105416, by rfl⟩) R210833
theorem R173335 : Reach 173335 := rs (se 1 (by rfl) ⟨130001, by rfl⟩) R260003
theorem R140567 : Reach 140567 := rs (se 1 (by rfl) ⟨105425, by rfl⟩) R210851
theorem R140633 : Reach 140633 := rs (se 2 (by rfl) ⟨52737, by rfl⟩) R105475
theorem R173441 : Reach 173441 := rs (se 2 (by rfl) ⟨65040, by rfl⟩) R130081
theorem R206233 : Reach 206233 := rs (se 2 (by rfl) ⟨77337, by rfl⟩) R154675
theorem R1156531 : Reach 1156531 := rs (se 1 (by rfl) ⟨867398, by rfl⟩) R1734797
theorem R140747 : Reach 140747 := rs (se 1 (by rfl) ⟨105560, by rfl⟩) R211121
theorem R239051 : Reach 239051 := rs (se 1 (by rfl) ⟨179288, by rfl⟩) R358577
theorem R4793813 : Reach 4793813 := rs (se 7 (by rfl) ⟨56177, by rfl⟩) R112355
theorem R140759 : Reach 140759 := rs (se 1 (by rfl) ⟨105569, by rfl⟩) R211139
theorem R206297 : Reach 206297 := rs (se 2 (by rfl) ⟨77361, by rfl⟩) R154723
theorem R468497 : Reach 468497 := rs (se 2 (by rfl) ⟨175686, by rfl⟩) R351373
theorem R173593 : Reach 173593 := rs (se 2 (by rfl) ⟨65097, by rfl⟩) R130195
theorem R140825 : Reach 140825 := rs (se 2 (by rfl) ⟨52809, by rfl⟩) R105619
theorem R206387 : Reach 206387 := rs (se 1 (by rfl) ⟨154790, by rfl⟩) R309581
theorem R206423 : Reach 206423 := rs (se 1 (by rfl) ⟨154817, by rfl⟩) R309635
theorem R140939 : Reach 140939 := rs (se 1 (by rfl) ⟨105704, by rfl⟩) R211409
theorem R140951 : Reach 140951 := rs (se 1 (by rfl) ⟨105713, by rfl⟩) R211427
theorem R141017 : Reach 141017 := rs (se 2 (by rfl) ⟨52881, by rfl⟩) R105763
theorem R206603 : Reach 206603 := rs (se 1 (by rfl) ⟨154952, by rfl⟩) R309905
theorem R206657 : Reach 206657 := rs (se 2 (by rfl) ⟨77496, by rfl⟩) R154993
theorem R141131 : Reach 141131 := rs (se 1 (by rfl) ⟨105848, by rfl⟩) R211697
theorem R141143 : Reach 141143 := rs (se 1 (by rfl) ⟨105857, by rfl⟩) R211715
theorem R141209 : Reach 141209 := rs (se 2 (by rfl) ⟨52953, by rfl⟩) R105907
theorem R141323 : Reach 141323 := rs (se 1 (by rfl) ⟨105992, by rfl⟩) R211985
theorem R141335 : Reach 141335 := rs (se 1 (by rfl) ⟨106001, by rfl⟩) R212003
theorem R206873 : Reach 206873 := rs (se 2 (by rfl) ⟨77577, by rfl⟩) R155155
theorem R141401 : Reach 141401 := rs (se 2 (by rfl) ⟨53025, by rfl⟩) R106051
theorem R206963 : Reach 206963 := rs (se 1 (by rfl) ⟨155222, by rfl⟩) R310445
theorem R206999 : Reach 206999 := rs (se 1 (by rfl) ⟨155249, by rfl⟩) R310499
theorem R338093 : Reach 338093 := rs (se 3 (by rfl) ⟨63392, by rfl⟩) R126785
theorem R141515 : Reach 141515 := rs (se 1 (by rfl) ⟨106136, by rfl⟩) R212273
theorem R141527 : Reach 141527 := rs (se 1 (by rfl) ⟨106145, by rfl⟩) R212291
theorem R272605 : Reach 272605 := rs (se 3 (by rfl) ⟨51113, by rfl⟩) R102227
theorem R502033 : Reach 502033 := rs (se 2 (by rfl) ⟨188262, by rfl⟩) R376525
theorem R272663 : Reach 272663 := rs (se 1 (by rfl) ⟨204497, by rfl⟩) R408995
theorem R141593 : Reach 141593 := rs (se 2 (by rfl) ⟨53097, by rfl⟩) R106195
theorem R469313 : Reach 469313 := rs (se 2 (by rfl) ⟨175992, by rfl⟩) R351985
theorem R207179 : Reach 207179 := rs (se 1 (by rfl) ⟨155384, by rfl⟩) R310769
theorem R338251 : Reach 338251 := rs (se 1 (by rfl) ⟨253688, by rfl⟩) R507377
theorem R207233 : Reach 207233 := rs (se 2 (by rfl) ⟨77712, by rfl⟩) R155425
theorem R141707 : Reach 141707 := rs (se 1 (by rfl) ⟨106280, by rfl⟩) R212561
theorem R141719 : Reach 141719 := rs (se 1 (by rfl) ⟨106289, by rfl⟩) R212579
theorem R240023 : Reach 240023 := rs (se 1 (by rfl) ⟨180017, by rfl⟩) R360035
theorem R436697 : Reach 436697 := rs (se 2 (by rfl) ⟨163761, by rfl⟩) R327523
theorem R141785 : Reach 141785 := rs (se 2 (by rfl) ⟨53169, by rfl⟩) R106339
theorem R272857 : Reach 272857 := rs (se 2 (by rfl) ⟨102321, by rfl⟩) R204643
theorem R600641 : Reach 600641 := rs (se 2 (by rfl) ⟨225240, by rfl⟩) R450481
theorem R141899 : Reach 141899 := rs (se 1 (by rfl) ⟨106424, by rfl⟩) R212849
theorem R141911 : Reach 141911 := rs (se 1 (by rfl) ⟨106433, by rfl⟩) R212867
theorem R207449 : Reach 207449 := rs (se 2 (by rfl) ⟨77793, by rfl⟩) R155587
theorem R338525 : Reach 338525 := rs (se 3 (by rfl) ⟨63473, by rfl⟩) R126947
theorem R141977 : Reach 141977 := rs (se 2 (by rfl) ⟨53241, by rfl⟩) R106483
theorem R207539 : Reach 207539 := rs (se 1 (by rfl) ⟨155654, by rfl⟩) R311309
theorem R207575 : Reach 207575 := rs (se 1 (by rfl) ⟨155681, by rfl⟩) R311363
theorem R404185 : Reach 404185 := rs (se 2 (by rfl) ⟨151569, by rfl⟩) R303139
theorem R142091 : Reach 142091 := rs (se 1 (by rfl) ⟨106568, by rfl⟩) R213137
theorem R142103 : Reach 142103 := rs (se 1 (by rfl) ⟨106577, by rfl⟩) R213155
theorem R174899 : Reach 174899 := rs (se 1 (by rfl) ⟨131174, by rfl⟩) R262349
theorem R273227 : Reach 273227 := rs (se 1 (by rfl) ⟨204920, by rfl⟩) R409841
theorem R142169 : Reach 142169 := rs (se 2 (by rfl) ⟨53313, by rfl⟩) R106627
theorem R207755 : Reach 207755 := rs (se 1 (by rfl) ⟨155816, by rfl⟩) R311633
theorem R207809 : Reach 207809 := rs (se 2 (by rfl) ⟨77928, by rfl⟩) R155857
theorem R175051 : Reach 175051 := rs (se 1 (by rfl) ⟨131288, by rfl⟩) R262577
theorem R142283 : Reach 142283 := rs (se 1 (by rfl) ⟨106712, by rfl⟩) R213425
theorem R142295 : Reach 142295 := rs (se 1 (by rfl) ⟨106721, by rfl⟩) R213443
theorem R699353 : Reach 699353 := rs (se 2 (by rfl) ⟨262257, by rfl⟩) R524515
theorem R142361 : Reach 142361 := rs (se 2 (by rfl) ⟨53385, by rfl⟩) R106771
theorem R240691 : Reach 240691 := rs (se 1 (by rfl) ⟨180518, by rfl⟩) R361037
theorem R142475 : Reach 142475 := rs (se 1 (by rfl) ⟨106856, by rfl⟩) R213713
theorem R142487 : Reach 142487 := rs (se 1 (by rfl) ⟨106865, by rfl⟩) R213731
theorem R208025 : Reach 208025 := rs (se 2 (by rfl) ⟨78009, by rfl⟩) R156019
theorem R142553 : Reach 142553 := rs (se 2 (by rfl) ⟨53457, by rfl⟩) R106915
theorem R208115 : Reach 208115 := rs (se 1 (by rfl) ⟨156086, by rfl⟩) R312173
theorem R1682693 : Reach 1682693 := rs (se 4 (by rfl) ⟨157752, by rfl⟩) R315505
theorem R208151 : Reach 208151 := rs (se 1 (by rfl) ⟨156113, by rfl⟩) R312227
theorem R175385 : Reach 175385 := rs (se 2 (by rfl) ⟨65769, by rfl⟩) R131539
theorem R404801 : Reach 404801 := rs (se 2 (by rfl) ⟨151800, by rfl⟩) R303601
theorem R142667 : Reach 142667 := rs (se 1 (by rfl) ⟨107000, by rfl⟩) R214001
theorem R142679 : Reach 142679 := rs (se 1 (by rfl) ⟨107009, by rfl⟩) R214019
theorem R208279 : Reach 208279 := rs (se 1 (by rfl) ⟨156209, by rfl⟩) R312419
theorem R208331 : Reach 208331 := rs (se 1 (by rfl) ⟨156248, by rfl⟩) R312497
theorem R208385 : Reach 208385 := rs (se 2 (by rfl) ⟨78144, by rfl⟩) R156289
theorem R339635 : Reach 339635 := rs (se 1 (by rfl) ⟨254726, by rfl⟩) R509453
theorem R208601 : Reach 208601 := rs (se 2 (by rfl) ⟨78225, by rfl⟩) R156451
theorem R208691 : Reach 208691 := rs (se 1 (by rfl) ⟨156518, by rfl⟩) R313037
theorem R208727 : Reach 208727 := rs (se 1 (by rfl) ⟨156545, by rfl⟩) R313091
theorem R176023 : Reach 176023 := rs (se 1 (by rfl) ⟨132017, by rfl⟩) R264035
theorem R569267 : Reach 569267 := rs (se 1 (by rfl) ⟨426950, by rfl⟩) R853901
theorem R208907 : Reach 208907 := rs (se 1 (by rfl) ⟨156680, by rfl⟩) R313361
theorem R208961 : Reach 208961 := rs (se 2 (by rfl) ⟨78360, by rfl⟩) R156721
theorem R471257 : Reach 471257 := rs (se 2 (by rfl) ⟨176721, by rfl⟩) R353443
theorem R209177 : Reach 209177 := rs (se 2 (by rfl) ⟨78441, by rfl⟩) R156883
theorem R209267 : Reach 209267 := rs (se 1 (by rfl) ⟨156950, by rfl⟩) R313901
theorem R209303 : Reach 209303 := rs (se 1 (by rfl) ⟨156977, by rfl⟩) R313955
theorem R209483 : Reach 209483 := rs (se 1 (by rfl) ⟨157112, by rfl⟩) R314225
theorem R209537 : Reach 209537 := rs (se 2 (by rfl) ⟨78576, by rfl⟩) R157153
theorem R340631 : Reach 340631 := rs (se 1 (by rfl) ⟨255473, by rfl⟩) R510947
theorem R176843 : Reach 176843 := rs (se 1 (by rfl) ⟨132632, by rfl⟩) R265265
theorem R176897 : Reach 176897 := rs (se 2 (by rfl) ⟨66336, by rfl⟩) R132673
theorem R209753 : Reach 209753 := rs (se 2 (by rfl) ⟨78657, by rfl⟩) R157315
theorem R209843 : Reach 209843 := rs (se 1 (by rfl) ⟨157382, by rfl⟩) R314765
theorem R209879 : Reach 209879 := rs (se 1 (by rfl) ⟨157409, by rfl⟩) R314819
theorem R210059 : Reach 210059 := rs (se 1 (by rfl) ⟨157544, by rfl⟩) R315089
theorem R799895 : Reach 799895 := rs (se 1 (by rfl) ⟨599921, by rfl⟩) R1199843
theorem R210113 : Reach 210113 := rs (se 2 (by rfl) ⟨78792, by rfl⟩) R157585
theorem R341293 : Reach 341293 := rs (se 3 (by rfl) ⟨63992, by rfl⟩) R127985
theorem R308555 : Reach 308555 := rs (se 1 (by rfl) ⟨231416, by rfl⟩) R462833
theorem R210329 : Reach 210329 := rs (se 2 (by rfl) ⟨78873, by rfl⟩) R157747
theorem R210419 : Reach 210419 := rs (se 1 (by rfl) ⟨157814, by rfl⟩) R315629
theorem R210455 : Reach 210455 := rs (se 1 (by rfl) ⟨157841, by rfl⟩) R315683
theorem R308825 : Reach 308825 := rs (se 2 (by rfl) ⟨115809, by rfl⟩) R231619
theorem R341597 : Reach 341597 := rs (se 3 (by rfl) ⟨64049, by rfl⟩) R128099
theorem R177815 : Reach 177815 := rs (se 1 (by rfl) ⟨133361, by rfl⟩) R266723
theorem R210635 : Reach 210635 := rs (se 1 (by rfl) ⟨157976, by rfl⟩) R315953
theorem R210689 : Reach 210689 := rs (se 2 (by rfl) ⟨79008, by rfl⟩) R158017
theorem R341783 : Reach 341783 := rs (se 1 (by rfl) ⟨256337, by rfl⟩) R512675
theorem R472877 : Reach 472877 := rs (se 3 (by rfl) ⟨88664, by rfl⟩) R177329
theorem R210775 : Reach 210775 := rs (se 1 (by rfl) ⟨158081, by rfl⟩) R316163
theorem R210905 : Reach 210905 := rs (se 2 (by rfl) ⟨79089, by rfl⟩) R158179
theorem R604205 : Reach 604205 := rs (se 3 (by rfl) ⟨113288, by rfl⟩) R226577
theorem R210995 : Reach 210995 := rs (se 1 (by rfl) ⟨158246, by rfl⟩) R316493
theorem R211031 : Reach 211031 := rs (se 1 (by rfl) ⟨158273, by rfl⟩) R316547
theorem R178355 : Reach 178355 := rs (se 1 (by rfl) ⟨133766, by rfl⟩) R267533
theorem R833753 : Reach 833753 := rs (se 2 (by rfl) ⟨312657, by rfl⟩) R625315
theorem R211211 : Reach 211211 := rs (se 1 (by rfl) ⟨158408, by rfl⟩) R316817
theorem R309527 : Reach 309527 := rs (se 1 (by rfl) ⟨232145, by rfl⟩) R464291
theorem R702755 : Reach 702755 := rs (se 1 (by rfl) ⟨527066, by rfl⟩) R1054133
theorem R211265 : Reach 211265 := rs (se 2 (by rfl) ⟨79224, by rfl⟩) R158449
theorem R10271245 : Reach 10271245 := rs (se 3 (by rfl) ⟨1925858, by rfl⟩) R3851717
theorem R211481 : Reach 211481 := rs (se 2 (by rfl) ⟨79305, by rfl⟩) R158611
theorem R670301 : Reach 670301 := rs (se 3 (by rfl) ⟨125681, by rfl⟩) R251363
theorem R211571 : Reach 211571 := rs (se 1 (by rfl) ⟨158678, by rfl⟩) R317357
theorem R211607 : Reach 211607 := rs (se 1 (by rfl) ⟨158705, by rfl⟩) R317411
theorem R178841 : Reach 178841 := rs (se 2 (by rfl) ⟨67065, by rfl⟩) R134131
theorem R178967 : Reach 178967 := rs (se 1 (by rfl) ⟨134225, by rfl⟩) R268451
theorem R310067 : Reach 310067 := rs (se 1 (by rfl) ⟨232550, by rfl⟩) R465101
theorem R211787 : Reach 211787 := rs (se 1 (by rfl) ⟨158840, by rfl⟩) R317681
theorem R211841 : Reach 211841 := rs (se 2 (by rfl) ⟨79440, by rfl⟩) R158881
theorem R801809 : Reach 801809 := rs (se 2 (by rfl) ⟨300678, by rfl⟩) R601357
theorem R441409 : Reach 441409 := rs (se 2 (by rfl) ⟨165528, by rfl⟩) R331057
theorem R310337 : Reach 310337 := rs (se 2 (by rfl) ⟨116376, by rfl⟩) R232753
theorem R212057 : Reach 212057 := rs (se 2 (by rfl) ⟨79521, by rfl⟩) R159043
theorem R212147 : Reach 212147 := rs (se 1 (by rfl) ⟨159110, by rfl⟩) R318221
theorem R212183 : Reach 212183 := rs (se 1 (by rfl) ⟨159137, by rfl⟩) R318275
theorem R113995 : Reach 113995 := rs (se 1 (by rfl) ⟨85496, by rfl⟩) R170993
theorem R146777 : Reach 146777 := rs (se 2 (by rfl) ⟨55041, by rfl⟩) R110083
theorem R212363 : Reach 212363 := rs (se 1 (by rfl) ⟨159272, by rfl⟩) R318545
theorem R212417 : Reach 212417 := rs (se 2 (by rfl) ⟨79656, by rfl⟩) R159313
theorem R310877 : Reach 310877 := rs (se 3 (by rfl) ⟨58289, by rfl⟩) R116579
theorem R212633 : Reach 212633 := rs (se 2 (by rfl) ⟨79737, by rfl⟩) R159475
theorem R212723 : Reach 212723 := rs (se 1 (by rfl) ⟨159542, by rfl⟩) R319085
theorem R212759 : Reach 212759 := rs (se 1 (by rfl) ⟨159569, by rfl⟩) R319139
theorem R376721 : Reach 376721 := rs (se 2 (by rfl) ⟨141270, by rfl⟩) R282541
theorem R212939 : Reach 212939 := rs (se 1 (by rfl) ⟨159704, by rfl⟩) R319409
theorem R212993 : Reach 212993 := rs (se 2 (by rfl) ⟨79872, by rfl⟩) R159745
theorem R180299 : Reach 180299 := rs (se 1 (by rfl) ⟨135224, by rfl⟩) R270449
theorem R213209 : Reach 213209 := rs (se 2 (by rfl) ⟨79953, by rfl⟩) R159907
theorem R180481 : Reach 180481 := rs (se 2 (by rfl) ⟨67680, by rfl⟩) R135361
theorem R213299 : Reach 213299 := rs (se 1 (by rfl) ⟨159974, by rfl⟩) R319949
theorem R213335 : Reach 213335 := rs (se 1 (by rfl) ⟨160001, by rfl⟩) R320003
theorem R541079 : Reach 541079 := rs (se 1 (by rfl) ⟨405809, by rfl⟩) R811619
theorem R213515 : Reach 213515 := rs (se 1 (by rfl) ⟨160136, by rfl⟩) R320273
theorem R213569 : Reach 213569 := rs (se 2 (by rfl) ⟨80088, by rfl⟩) R160177
theorem R1065565 : Reach 1065565 := rs (se 3 (by rfl) ⟨199793, by rfl⟩) R399587
theorem R2507395 : Reach 2507395 := rs (se 1 (by rfl) ⟨1880546, by rfl⟩) R3761093
theorem R115339 : Reach 115339 := rs (se 1 (by rfl) ⟨86504, by rfl⟩) R173009
theorem R1557143 : Reach 1557143 := rs (se 1 (by rfl) ⟨1167857, by rfl⟩) R2335715
theorem R312011 : Reach 312011 := rs (se 1 (by rfl) ⟨234008, by rfl⟩) R468017
theorem R967373 : Reach 967373 := rs (se 3 (by rfl) ⟨181382, by rfl⟩) R362765
theorem R213785 : Reach 213785 := rs (se 2 (by rfl) ⟨80169, by rfl⟩) R160339
theorem R213875 : Reach 213875 := rs (se 1 (by rfl) ⟨160406, by rfl⟩) R320813
theorem R115607 : Reach 115607 := rs (se 1 (by rfl) ⟨86705, by rfl⟩) R173411
theorem R213911 : Reach 213911 := rs (se 1 (by rfl) ⟨160433, by rfl⟩) R320867
theorem R312281 : Reach 312281 := rs (se 2 (by rfl) ⟨117105, by rfl⟩) R234211
theorem R902501 : Reach 902501 := rs (se 4 (by rfl) ⟨84609, by rfl⟩) R169219
theorem R149015 : Reach 149015 := rs (se 1 (by rfl) ⟨111761, by rfl⟩) R223523
theorem R116311 : Reach 116311 := rs (se 1 (by rfl) ⟨87233, by rfl⟩) R174467
theorem R476765 : Reach 476765 := rs (se 3 (by rfl) ⟨89393, by rfl⟩) R178787
theorem R214643 : Reach 214643 := rs (se 1 (by rfl) ⟨160982, by rfl⟩) R321965
theorem R312983 : Reach 312983 := rs (se 1 (by rfl) ⟨234737, by rfl⟩) R469475
theorem R607895 : Reach 607895 := rs (se 1 (by rfl) ⟨455921, by rfl⟩) R911843
theorem R542387 : Reach 542387 := rs (se 1 (by rfl) ⟨406790, by rfl⟩) R813581
theorem R378769 : Reach 378769 := rs (se 2 (by rfl) ⟨142038, by rfl⟩) R284077
theorem R313523 : Reach 313523 := rs (se 1 (by rfl) ⟨235142, by rfl⟩) R470285
theorem R379073 : Reach 379073 := rs (se 2 (by rfl) ⟨142152, by rfl⟩) R284305
theorem R346457 : Reach 346457 := rs (se 2 (by rfl) ⟨129921, by rfl⟩) R259843
theorem R444851 : Reach 444851 := rs (se 1 (by rfl) ⟨333638, by rfl⟩) R667277
theorem R313793 : Reach 313793 := rs (se 2 (by rfl) ⟨117672, by rfl⟩) R235345
theorem R215795 : Reach 215795 := rs (se 1 (by rfl) ⟨161846, by rfl⟩) R323693
theorem R805697 : Reach 805697 := rs (se 2 (by rfl) ⟨302136, by rfl⟩) R604273
theorem R314333 : Reach 314333 := rs (se 3 (by rfl) ⟨58937, by rfl⟩) R117875
theorem R118027 : Reach 118027 := rs (se 1 (by rfl) ⟨88520, by rfl⟩) R177041
theorem R216395 : Reach 216395 := rs (se 1 (by rfl) ⟨162296, by rfl⟩) R324593
theorem R708101 : Reach 708101 := rs (se 4 (by rfl) ⟨66384, by rfl⟩) R132769
theorem R675373 : Reach 675373 := rs (se 3 (by rfl) ⟨126632, by rfl⟩) R253265
theorem R478871 : Reach 478871 := rs (se 1 (by rfl) ⟨359153, by rfl⟩) R718307
theorem R511895 : Reach 511895 := rs (se 1 (by rfl) ⟨383921, by rfl⟩) R767843
theorem R348083 : Reach 348083 := rs (se 1 (by rfl) ⟨261062, by rfl⟩) R522125
theorem R348097 : Reach 348097 := rs (se 2 (by rfl) ⟨130536, by rfl⟩) R261073
theorem R380875 : Reach 380875 := rs (se 1 (by rfl) ⟨285656, by rfl⟩) R571313
theorem R315467 : Reach 315467 := rs (se 1 (by rfl) ⟨236600, by rfl⟩) R473201
theorem R118999 : Reach 118999 := rs (se 1 (by rfl) ⟨89249, by rfl⟩) R178499
theorem R151769 : Reach 151769 := rs (se 2 (by rfl) ⟨56913, by rfl⟩) R113827
theorem R315737 : Reach 315737 := rs (se 2 (by rfl) ⟨118401, by rfl⟩) R236803
theorem R316381 : Reach 316381 := rs (se 3 (by rfl) ⟨59321, by rfl⟩) R118643
theorem R381917 : Reach 381917 := rs (se 3 (by rfl) ⟨71609, by rfl⟩) R143219
theorem R119819 : Reach 119819 := rs (se 1 (by rfl) ⟨89864, by rfl⟩) R179729
theorem R316439 : Reach 316439 := rs (se 1 (by rfl) ⟨237329, by rfl⟩) R474659
theorem R939043 : Reach 939043 := rs (se 1 (by rfl) ⟨704282, by rfl⟩) R1408565
theorem R250931 : Reach 250931 := rs (se 1 (by rfl) ⟨188198, by rfl⟩) R376397
theorem R382429 : Reach 382429 := rs (se 3 (by rfl) ⟨71705, by rfl⟩) R143411
theorem R316979 : Reach 316979 := rs (se 1 (by rfl) ⟨237734, by rfl⟩) R475469
theorem R382657 : Reach 382657 := rs (se 2 (by rfl) ⟨143496, by rfl⟩) R286993
theorem R317249 : Reach 317249 := rs (se 2 (by rfl) ⟨118968, by rfl⟩) R237937
theorem R350027 : Reach 350027 := rs (se 1 (by rfl) ⟨262520, by rfl⟩) R525041
theorem R350041 : Reach 350041 := rs (se 2 (by rfl) ⟨131265, by rfl⟩) R262531
theorem R841603 : Reach 841603 := rs (se 1 (by rfl) ⟨631202, by rfl⟩) R1262405
theorem R710531 : Reach 710531 := rs (se 1 (by rfl) ⟨532898, by rfl⟩) R1065797
theorem R2283821 : Reach 2283821 := rs (se 3 (by rfl) ⟨428216, by rfl⟩) R856433
theorem R317789 : Reach 317789 := rs (se 3 (by rfl) ⟨59585, by rfl⟩) R119171
theorem R645677 : Reach 645677 := rs (se 3 (by rfl) ⟨121064, by rfl⟩) R242129
theorem R449155 : Reach 449155 := rs (se 1 (by rfl) ⟨336866, by rfl⟩) R673733
theorem R154379 : Reach 154379 := rs (se 1 (by rfl) ⟨115784, by rfl⟩) R231569
theorem R350999 : Reach 350999 := rs (se 1 (by rfl) ⟨263249, by rfl⟩) R526499
theorem R154507 : Reach 154507 := rs (se 1 (by rfl) ⟨115880, by rfl⟩) R231761
theorem R154649 : Reach 154649 := rs (se 2 (by rfl) ⟨57993, by rfl⟩) R115987
theorem R1596509 : Reach 1596509 := rs (se 3 (by rfl) ⟨299345, by rfl⟩) R598691
theorem R154777 : Reach 154777 := rs (se 2 (by rfl) ⟨58041, by rfl⟩) R116083
theorem R318923 : Reach 318923 := rs (se 1 (by rfl) ⟨239192, by rfl⟩) R478385
theorem R155351 : Reach 155351 := rs (se 1 (by rfl) ⟨116513, by rfl⟩) R233027
theorem R319193 : Reach 319193 := rs (se 2 (by rfl) ⟨119697, by rfl⟩) R239395
theorem R155479 : Reach 155479 := rs (se 1 (by rfl) ⟨116609, by rfl⟩) R233219
theorem R352259 : Reach 352259 := rs (se 1 (by rfl) ⟨264194, by rfl⟩) R528389
theorem R319895 : Reach 319895 := rs (se 1 (by rfl) ⟨239921, by rfl⟩) R479843
theorem R156107 : Reach 156107 := rs (se 1 (by rfl) ⟨117080, by rfl⟩) R234161
theorem R156235 : Reach 156235 := rs (se 1 (by rfl) ⟨117176, by rfl⟩) R234353
theorem R156377 : Reach 156377 := rs (se 2 (by rfl) ⟨58641, by rfl⟩) R117283
theorem R1008389 : Reach 1008389 := rs (se 4 (by rfl) ⟨94536, by rfl⟩) R189073
theorem R156439 : Reach 156439 := rs (se 1 (by rfl) ⟨117329, by rfl⟩) R234659
theorem R451403 : Reach 451403 := rs (se 1 (by rfl) ⟨338552, by rfl⟩) R677105
theorem R222041 : Reach 222041 := rs (se 2 (by rfl) ⟨83265, by rfl⟩) R166531
theorem R156505 : Reach 156505 := rs (se 2 (by rfl) ⟨58689, by rfl⟩) R117379
theorem R320435 : Reach 320435 := rs (se 1 (by rfl) ⟨240326, by rfl⟩) R480653
theorem R91147 : Reach 91147 := rs (se 1 (by rfl) ⟨68360, by rfl⟩) R136721
theorem R91159 : Reach 91159 := rs (se 1 (by rfl) ⟨68369, by rfl⟩) R136739
theorem R91179 : Reach 91179 := rs (se 1 (by rfl) ⟨68384, by rfl⟩) R136769
theorem R91191 : Reach 91191 := rs (se 1 (by rfl) ⟨68393, by rfl⟩) R136787
theorem R91211 : Reach 91211 := rs (se 1 (by rfl) ⟨68408, by rfl⟩) R136817
theorem R91223 : Reach 91223 := rs (se 1 (by rfl) ⟨68417, by rfl⟩) R136835
theorem R91243 : Reach 91243 := rs (se 1 (by rfl) ⟨68432, by rfl⟩) R136865
theorem R91255 : Reach 91255 := rs (se 1 (by rfl) ⟨68441, by rfl⟩) R136883
theorem R91275 : Reach 91275 := rs (se 1 (by rfl) ⟨68456, by rfl⟩) R136913
theorem R91287 : Reach 91287 := rs (se 1 (by rfl) ⟨68465, by rfl⟩) R136931
theorem R91307 : Reach 91307 := rs (se 1 (by rfl) ⟨68480, by rfl⟩) R136961
theorem R91319 : Reach 91319 := rs (se 1 (by rfl) ⟨68489, by rfl⟩) R136979
theorem R320705 : Reach 320705 := rs (se 2 (by rfl) ⟨120264, by rfl⟩) R240529
theorem R91339 : Reach 91339 := rs (se 1 (by rfl) ⟨68504, by rfl⟩) R137009
theorem R713933 : Reach 713933 := rs (se 3 (by rfl) ⟨133862, by rfl⟩) R267725
theorem R91351 : Reach 91351 := rs (se 1 (by rfl) ⟨68513, by rfl⟩) R137027
theorem R91371 : Reach 91371 := rs (se 1 (by rfl) ⟨68528, by rfl⟩) R137057
theorem R91383 : Reach 91383 := rs (se 1 (by rfl) ⟨68537, by rfl⟩) R137075
theorem R91403 : Reach 91403 := rs (se 1 (by rfl) ⟨68552, by rfl⟩) R137105
theorem R91415 : Reach 91415 := rs (se 1 (by rfl) ⟨68561, by rfl⟩) R137123
theorem R91435 : Reach 91435 := rs (se 1 (by rfl) ⟨68576, by rfl⟩) R137153
theorem R91447 : Reach 91447 := rs (se 1 (by rfl) ⟨68585, by rfl⟩) R137171
theorem R91467 : Reach 91467 := rs (se 1 (by rfl) ⟨68600, by rfl⟩) R137201
theorem R91479 : Reach 91479 := rs (se 1 (by rfl) ⟨68609, by rfl⟩) R137219
theorem R91499 : Reach 91499 := rs (se 1 (by rfl) ⟨68624, by rfl⟩) R137249
theorem R91511 : Reach 91511 := rs (se 1 (by rfl) ⟨68633, by rfl⟩) R137267
theorem R91531 : Reach 91531 := rs (se 1 (by rfl) ⟨68648, by rfl⟩) R137297
theorem R91543 : Reach 91543 := rs (se 1 (by rfl) ⟨68657, by rfl⟩) R137315
theorem R157079 : Reach 157079 := rs (se 1 (by rfl) ⟨117809, by rfl⟩) R235619
theorem R91563 : Reach 91563 := rs (se 1 (by rfl) ⟨68672, by rfl⟩) R137345
theorem R1598899 : Reach 1598899 := rs (se 1 (by rfl) ⟨1199174, by rfl⟩) R2398349
theorem R91575 : Reach 91575 := rs (se 1 (by rfl) ⟨68681, by rfl⟩) R137363
theorem R91595 : Reach 91595 := rs (se 1 (by rfl) ⟨68696, by rfl⟩) R137393
theorem R124363 : Reach 124363 := rs (se 1 (by rfl) ⟨93272, by rfl⟩) R186545
theorem R91607 : Reach 91607 := rs (se 1 (by rfl) ⟨68705, by rfl⟩) R137411
theorem R91627 : Reach 91627 := rs (se 1 (by rfl) ⟨68720, by rfl⟩) R137441
theorem R91639 : Reach 91639 := rs (se 1 (by rfl) ⟨68729, by rfl⟩) R137459
theorem R91659 : Reach 91659 := rs (se 1 (by rfl) ⟨68744, by rfl⟩) R137489
theorem R91671 : Reach 91671 := rs (se 1 (by rfl) ⟨68753, by rfl⟩) R137507
theorem R157207 : Reach 157207 := rs (se 1 (by rfl) ⟨117905, by rfl⟩) R235811
theorem R91691 : Reach 91691 := rs (se 1 (by rfl) ⟨68768, by rfl⟩) R137537
theorem R91703 : Reach 91703 := rs (se 1 (by rfl) ⟨68777, by rfl⟩) R137555
theorem R91723 : Reach 91723 := rs (se 1 (by rfl) ⟨68792, by rfl⟩) R137585
theorem R91735 : Reach 91735 := rs (se 1 (by rfl) ⟨68801, by rfl⟩) R137603
theorem R91755 : Reach 91755 := rs (se 1 (by rfl) ⟨68816, by rfl⟩) R137633
theorem R91767 : Reach 91767 := rs (se 1 (by rfl) ⟨68825, by rfl⟩) R137651
theorem R91787 : Reach 91787 := rs (se 1 (by rfl) ⟨68840, by rfl⟩) R137681
theorem R91799 : Reach 91799 := rs (se 1 (by rfl) ⟨68849, by rfl⟩) R137699
theorem R91819 : Reach 91819 := rs (se 1 (by rfl) ⟨68864, by rfl⟩) R137729
theorem R714419 : Reach 714419 := rs (se 1 (by rfl) ⟨535814, by rfl⟩) R1071629
theorem R91831 : Reach 91831 := rs (se 1 (by rfl) ⟨68873, by rfl⟩) R137747
theorem R91851 : Reach 91851 := rs (se 1 (by rfl) ⟨68888, by rfl⟩) R137777
theorem R91863 : Reach 91863 := rs (se 1 (by rfl) ⟨68897, by rfl⟩) R137795
theorem R91883 : Reach 91883 := rs (se 1 (by rfl) ⟨68912, by rfl⟩) R137825
theorem R91895 : Reach 91895 := rs (se 1 (by rfl) ⟨68921, by rfl⟩) R137843
theorem R91915 : Reach 91915 := rs (se 1 (by rfl) ⟨68936, by rfl⟩) R137873
theorem R91927 : Reach 91927 := rs (se 1 (by rfl) ⟨68945, by rfl⟩) R137891
theorem R91947 : Reach 91947 := rs (se 1 (by rfl) ⟨68960, by rfl⟩) R137921
theorem R91959 : Reach 91959 := rs (se 1 (by rfl) ⟨68969, by rfl⟩) R137939
theorem R91979 : Reach 91979 := rs (se 1 (by rfl) ⟨68984, by rfl⟩) R137969
theorem R91991 : Reach 91991 := rs (se 1 (by rfl) ⟨68993, by rfl⟩) R137987
theorem R92011 : Reach 92011 := rs (se 1 (by rfl) ⟨69008, by rfl⟩) R138017
theorem R92023 : Reach 92023 := rs (se 1 (by rfl) ⟨69017, by rfl⟩) R138035
theorem R92043 : Reach 92043 := rs (se 1 (by rfl) ⟨69032, by rfl⟩) R138065
theorem R92055 : Reach 92055 := rs (se 1 (by rfl) ⟨69041, by rfl⟩) R138083
theorem R92075 : Reach 92075 := rs (se 1 (by rfl) ⟨69056, by rfl⟩) R138113
theorem R92087 : Reach 92087 := rs (se 1 (by rfl) ⟨69065, by rfl⟩) R138131
theorem R92107 : Reach 92107 := rs (se 1 (by rfl) ⟨69080, by rfl⟩) R138161
theorem R92119 : Reach 92119 := rs (se 1 (by rfl) ⟨69089, by rfl⟩) R138179
theorem R92139 : Reach 92139 := rs (se 1 (by rfl) ⟨69104, by rfl⟩) R138209
theorem R92151 : Reach 92151 := rs (se 1 (by rfl) ⟨69113, by rfl⟩) R138227
theorem R92171 : Reach 92171 := rs (se 1 (by rfl) ⟨69128, by rfl⟩) R138257
theorem R92183 : Reach 92183 := rs (se 1 (by rfl) ⟨69137, by rfl⟩) R138275
theorem R878627 : Reach 878627 := rs (se 1 (by rfl) ⟨658970, by rfl⟩) R1317941
theorem R92203 : Reach 92203 := rs (se 1 (by rfl) ⟨69152, by rfl⟩) R138305
theorem R92215 : Reach 92215 := rs (se 1 (by rfl) ⟨69161, by rfl⟩) R138323
theorem R92235 : Reach 92235 := rs (se 1 (by rfl) ⟨69176, by rfl⟩) R138353
theorem R92247 : Reach 92247 := rs (se 1 (by rfl) ⟨69185, by rfl⟩) R138371
theorem R92267 : Reach 92267 := rs (se 1 (by rfl) ⟨69200, by rfl⟩) R138401
theorem R92279 : Reach 92279 := rs (se 1 (by rfl) ⟨69209, by rfl⟩) R138419
theorem R583811 : Reach 583811 := rs (se 1 (by rfl) ⟨437858, by rfl⟩) R875717
theorem R157835 : Reach 157835 := rs (se 1 (by rfl) ⟨118376, by rfl⟩) R236753
theorem R92299 : Reach 92299 := rs (se 1 (by rfl) ⟨69224, by rfl⟩) R138449
theorem R92311 : Reach 92311 := rs (se 1 (by rfl) ⟨69233, by rfl⟩) R138467
theorem R92331 : Reach 92331 := rs (se 1 (by rfl) ⟨69248, by rfl⟩) R138497
theorem R92343 : Reach 92343 := rs (se 1 (by rfl) ⟨69257, by rfl⟩) R138515
theorem R92363 : Reach 92363 := rs (se 1 (by rfl) ⟨69272, by rfl⟩) R138545
theorem R92375 : Reach 92375 := rs (se 1 (by rfl) ⟨69281, by rfl⟩) R138563
theorem R92395 : Reach 92395 := rs (se 1 (by rfl) ⟨69296, by rfl⟩) R138593
theorem R92407 : Reach 92407 := rs (se 1 (by rfl) ⟨69305, by rfl⟩) R138611
theorem R92427 : Reach 92427 := rs (se 1 (by rfl) ⟨69320, by rfl⟩) R138641
theorem R157963 : Reach 157963 := rs (se 1 (by rfl) ⟨118472, by rfl⟩) R236945
theorem R92439 : Reach 92439 := rs (se 1 (by rfl) ⟨69329, by rfl⟩) R138659
theorem R92459 : Reach 92459 := rs (se 1 (by rfl) ⟨69344, by rfl⟩) R138689
theorem R92471 : Reach 92471 := rs (se 1 (by rfl) ⟨69353, by rfl⟩) R138707
theorem R92491 : Reach 92491 := rs (se 1 (by rfl) ⟨69368, by rfl⟩) R138737
theorem R92503 : Reach 92503 := rs (se 1 (by rfl) ⟨69377, by rfl⟩) R138755
theorem R158041 : Reach 158041 := rs (se 2 (by rfl) ⟨59265, by rfl⟩) R118531
theorem R92523 : Reach 92523 := rs (se 1 (by rfl) ⟨69392, by rfl⟩) R138785
theorem R92535 : Reach 92535 := rs (se 1 (by rfl) ⟨69401, by rfl⟩) R138803
theorem R92555 : Reach 92555 := rs (se 1 (by rfl) ⟨69416, by rfl⟩) R138833
theorem R92567 : Reach 92567 := rs (se 1 (by rfl) ⟨69425, by rfl⟩) R138851
theorem R158105 : Reach 158105 := rs (se 2 (by rfl) ⟨59289, by rfl⟩) R118579
theorem R92587 : Reach 92587 := rs (se 1 (by rfl) ⟨69440, by rfl⟩) R138881
theorem R92599 : Reach 92599 := rs (se 1 (by rfl) ⟨69449, by rfl⟩) R138899
theorem R92619 : Reach 92619 := rs (se 1 (by rfl) ⟨69464, by rfl⟩) R138929
theorem R321995 : Reach 321995 := rs (se 1 (by rfl) ⟨241496, by rfl⟩) R482993
theorem R92631 : Reach 92631 := rs (se 1 (by rfl) ⟨69473, by rfl⟩) R138947
theorem R125401 : Reach 125401 := rs (se 2 (by rfl) ⟨47025, by rfl⟩) R94051
theorem R92651 : Reach 92651 := rs (se 1 (by rfl) ⟨69488, by rfl⟩) R138977
theorem R92663 : Reach 92663 := rs (se 1 (by rfl) ⟨69497, by rfl⟩) R138995
theorem R92683 : Reach 92683 := rs (se 1 (by rfl) ⟨69512, by rfl⟩) R139025
theorem R92695 : Reach 92695 := rs (se 1 (by rfl) ⟨69521, by rfl⟩) R139043
theorem R158233 : Reach 158233 := rs (se 2 (by rfl) ⟨59337, by rfl⟩) R118675
theorem R92715 : Reach 92715 := rs (se 1 (by rfl) ⟨69536, by rfl⟩) R139073
theorem R92727 : Reach 92727 := rs (se 1 (by rfl) ⟨69545, by rfl⟩) R139091
theorem R92747 : Reach 92747 := rs (se 1 (by rfl) ⟨69560, by rfl⟩) R139121
theorem R92759 : Reach 92759 := rs (se 1 (by rfl) ⟨69569, by rfl⟩) R139139
theorem R92779 : Reach 92779 := rs (se 1 (by rfl) ⟨69584, by rfl⟩) R139169
theorem R92791 : Reach 92791 := rs (se 1 (by rfl) ⟨69593, by rfl⟩) R139187
theorem R92811 : Reach 92811 := rs (se 1 (by rfl) ⟨69608, by rfl⟩) R139217
theorem R92823 : Reach 92823 := rs (se 1 (by rfl) ⟨69617, by rfl⟩) R139235
theorem R92843 : Reach 92843 := rs (se 1 (by rfl) ⟨69632, by rfl⟩) R139265
theorem R92855 : Reach 92855 := rs (se 1 (by rfl) ⟨69641, by rfl⟩) R139283
theorem R92875 : Reach 92875 := rs (se 1 (by rfl) ⟨69656, by rfl⟩) R139313
theorem R92887 : Reach 92887 := rs (se 1 (by rfl) ⟨69665, by rfl⟩) R139331
theorem R92907 : Reach 92907 := rs (se 1 (by rfl) ⟨69680, by rfl⟩) R139361
theorem R92919 : Reach 92919 := rs (se 1 (by rfl) ⟨69689, by rfl⟩) R139379
theorem R92939 : Reach 92939 := rs (se 1 (by rfl) ⟨69704, by rfl⟩) R139409
theorem R92951 : Reach 92951 := rs (se 1 (by rfl) ⟨69713, by rfl⟩) R139427
theorem R92971 : Reach 92971 := rs (se 1 (by rfl) ⟨69728, by rfl⟩) R139457
theorem R92983 : Reach 92983 := rs (se 1 (by rfl) ⟨69737, by rfl⟩) R139475
theorem R93003 : Reach 93003 := rs (se 1 (by rfl) ⟨69752, by rfl⟩) R139505
theorem R93015 : Reach 93015 := rs (se 1 (by rfl) ⟨69761, by rfl⟩) R139523
theorem R93035 : Reach 93035 := rs (se 1 (by rfl) ⟨69776, by rfl⟩) R139553
theorem R93047 : Reach 93047 := rs (se 1 (by rfl) ⟨69785, by rfl⟩) R139571
theorem R93067 : Reach 93067 := rs (se 1 (by rfl) ⟨69800, by rfl⟩) R139601
theorem R93079 : Reach 93079 := rs (se 1 (by rfl) ⟨69809, by rfl⟩) R139619
theorem R93099 : Reach 93099 := rs (se 1 (by rfl) ⟨69824, by rfl⟩) R139649
theorem R93111 : Reach 93111 := rs (se 1 (by rfl) ⟨69833, by rfl⟩) R139667
theorem R93131 : Reach 93131 := rs (se 1 (by rfl) ⟨69848, by rfl⟩) R139697
theorem R93143 : Reach 93143 := rs (se 1 (by rfl) ⟨69857, by rfl⟩) R139715
theorem R93163 : Reach 93163 := rs (se 1 (by rfl) ⟨69872, by rfl⟩) R139745
theorem R93175 : Reach 93175 := rs (se 1 (by rfl) ⟨69881, by rfl⟩) R139763
theorem R191489 : Reach 191489 := rs (se 2 (by rfl) ⟨71808, by rfl⟩) R143617
theorem R93195 : Reach 93195 := rs (se 1 (by rfl) ⟨69896, by rfl⟩) R139793
theorem R93207 : Reach 93207 := rs (se 1 (by rfl) ⟨69905, by rfl⟩) R139811
theorem R93227 : Reach 93227 := rs (se 1 (by rfl) ⟨69920, by rfl⟩) R139841
theorem R355373 : Reach 355373 := rs (se 3 (by rfl) ⟨66632, by rfl⟩) R133265
theorem R584749 : Reach 584749 := rs (se 3 (by rfl) ⟨109640, by rfl⟩) R219281
theorem R93239 : Reach 93239 := rs (se 1 (by rfl) ⟨69929, by rfl⟩) R139859
theorem R93259 : Reach 93259 := rs (se 1 (by rfl) ⟨69944, by rfl⟩) R139889
theorem R93271 : Reach 93271 := rs (se 1 (by rfl) ⟨69953, by rfl⟩) R139907
theorem R158807 : Reach 158807 := rs (se 1 (by rfl) ⟨119105, by rfl⟩) R238211
theorem R715877 : Reach 715877 := rs (se 4 (by rfl) ⟨67113, by rfl⟩) R134227
theorem R93291 : Reach 93291 := rs (se 1 (by rfl) ⟨69968, by rfl⟩) R139937
theorem R93303 : Reach 93303 := rs (se 1 (by rfl) ⟨69977, by rfl⟩) R139955
theorem R93323 : Reach 93323 := rs (se 1 (by rfl) ⟨69992, by rfl⟩) R139985
theorem R93335 : Reach 93335 := rs (se 1 (by rfl) ⟨70001, by rfl⟩) R140003
theorem R93355 : Reach 93355 := rs (se 1 (by rfl) ⟨70016, by rfl⟩) R140033
theorem R93367 : Reach 93367 := rs (se 1 (by rfl) ⟨70025, by rfl⟩) R140051
theorem R93387 : Reach 93387 := rs (se 1 (by rfl) ⟨70040, by rfl⟩) R140081
theorem R93399 : Reach 93399 := rs (se 1 (by rfl) ⟨70049, by rfl⟩) R140099
theorem R158935 : Reach 158935 := rs (se 1 (by rfl) ⟨119201, by rfl⟩) R238403
theorem R93419 : Reach 93419 := rs (se 1 (by rfl) ⟨70064, by rfl⟩) R140129
theorem R93431 : Reach 93431 := rs (se 1 (by rfl) ⟨70073, by rfl⟩) R140147
theorem R93451 : Reach 93451 := rs (se 1 (by rfl) ⟨70088, by rfl⟩) R140177
theorem R93463 : Reach 93463 := rs (se 1 (by rfl) ⟨70097, by rfl⟩) R140195
theorem R93483 : Reach 93483 := rs (se 1 (by rfl) ⟨70112, by rfl⟩) R140225
theorem R93495 : Reach 93495 := rs (se 1 (by rfl) ⟨70121, by rfl⟩) R140243
theorem R93515 : Reach 93515 := rs (se 1 (by rfl) ⟨70136, by rfl⟩) R140273
theorem R93527 : Reach 93527 := rs (se 1 (by rfl) ⟨70145, by rfl⟩) R140291
theorem R93547 : Reach 93547 := rs (se 1 (by rfl) ⟨70160, by rfl⟩) R140321
theorem R93559 : Reach 93559 := rs (se 1 (by rfl) ⟨70169, by rfl⟩) R140339
theorem R93579 : Reach 93579 := rs (se 1 (by rfl) ⟨70184, by rfl⟩) R140369
theorem R93591 : Reach 93591 := rs (se 1 (by rfl) ⟨70193, by rfl⟩) R140387
theorem R93611 : Reach 93611 := rs (se 1 (by rfl) ⟨70208, by rfl⟩) R140417
theorem R93623 : Reach 93623 := rs (se 1 (by rfl) ⟨70217, by rfl⟩) R140435
theorem R93643 : Reach 93643 := rs (se 1 (by rfl) ⟨70232, by rfl⟩) R140465
theorem R93655 : Reach 93655 := rs (se 1 (by rfl) ⟨70241, by rfl⟩) R140483
theorem R519641 : Reach 519641 := rs (se 2 (by rfl) ⟨194865, by rfl⟩) R389731
theorem R650713 : Reach 650713 := rs (se 2 (by rfl) ⟨244017, by rfl⟩) R488035
theorem R93675 : Reach 93675 := rs (se 1 (by rfl) ⟨70256, by rfl⟩) R140513
theorem R93687 : Reach 93687 := rs (se 1 (by rfl) ⟨70265, by rfl⟩) R140531
theorem R93707 : Reach 93707 := rs (se 1 (by rfl) ⟨70280, by rfl⟩) R140561
theorem R93719 : Reach 93719 := rs (se 1 (by rfl) ⟨70289, by rfl⟩) R140579
theorem R192025 : Reach 192025 := rs (se 2 (by rfl) ⟨72009, by rfl⟩) R144019
theorem R93739 : Reach 93739 := rs (se 1 (by rfl) ⟨70304, by rfl⟩) R140609
theorem R93751 : Reach 93751 := rs (se 1 (by rfl) ⟨70313, by rfl⟩) R140627
theorem R93771 : Reach 93771 := rs (se 1 (by rfl) ⟨70328, by rfl⟩) R140657
theorem R716363 : Reach 716363 := rs (se 1 (by rfl) ⟨537272, by rfl⟩) R1074545
theorem R93783 : Reach 93783 := rs (se 1 (by rfl) ⟨70337, by rfl⟩) R140675
theorem R93803 : Reach 93803 := rs (se 1 (by rfl) ⟨70352, by rfl⟩) R140705
theorem R93815 : Reach 93815 := rs (se 1 (by rfl) ⟨70361, by rfl⟩) R140723
theorem R93835 : Reach 93835 := rs (se 1 (by rfl) ⟨70376, by rfl⟩) R140753
theorem R93847 : Reach 93847 := rs (se 1 (by rfl) ⟨70385, by rfl⟩) R140771
theorem R93867 : Reach 93867 := rs (se 1 (by rfl) ⟨70400, by rfl⟩) R140801
theorem R93879 : Reach 93879 := rs (se 1 (by rfl) ⟨70409, by rfl⟩) R140819
theorem R93899 : Reach 93899 := rs (se 1 (by rfl) ⟨70424, by rfl⟩) R140849
theorem R93911 : Reach 93911 := rs (se 1 (by rfl) ⟨70433, by rfl⟩) R140867
theorem R159449 : Reach 159449 := rs (se 2 (by rfl) ⟨59793, by rfl⟩) R119587
theorem R93931 : Reach 93931 := rs (se 1 (by rfl) ⟨70448, by rfl⟩) R140897
theorem R93943 : Reach 93943 := rs (se 1 (by rfl) ⟨70457, by rfl⟩) R140915
theorem R93963 : Reach 93963 := rs (se 1 (by rfl) ⟨70472, by rfl⟩) R140945
theorem R93975 : Reach 93975 := rs (se 1 (by rfl) ⟨70481, by rfl⟩) R140963
theorem R93995 : Reach 93995 := rs (se 1 (by rfl) ⟨70496, by rfl⟩) R140993
theorem R356147 : Reach 356147 := rs (se 1 (by rfl) ⟨267110, by rfl⟩) R534221
theorem R94007 : Reach 94007 := rs (se 1 (by rfl) ⟨70505, by rfl⟩) R141011
theorem R749387 : Reach 749387 := rs (se 1 (by rfl) ⟨562040, by rfl⟩) R1124081
theorem R94027 : Reach 94027 := rs (se 1 (by rfl) ⟨70520, by rfl⟩) R141041
theorem R159563 : Reach 159563 := rs (se 1 (by rfl) ⟨119672, by rfl⟩) R239345
theorem R94039 : Reach 94039 := rs (se 1 (by rfl) ⟨70529, by rfl⟩) R141059
theorem R94059 : Reach 94059 := rs (se 1 (by rfl) ⟨70544, by rfl⟩) R141089
theorem R94071 : Reach 94071 := rs (se 1 (by rfl) ⟨70553, by rfl⟩) R141107
theorem R94091 : Reach 94091 := rs (se 1 (by rfl) ⟨70568, by rfl⟩) R141137
theorem R94103 : Reach 94103 := rs (se 1 (by rfl) ⟨70577, by rfl⟩) R141155
theorem R94123 : Reach 94123 := rs (se 1 (by rfl) ⟨70592, by rfl⟩) R141185
theorem R94135 : Reach 94135 := rs (se 1 (by rfl) ⟨70601, by rfl⟩) R141203
theorem R192449 : Reach 192449 := rs (se 2 (by rfl) ⟨72168, by rfl⟩) R144337
theorem R94155 : Reach 94155 := rs (se 1 (by rfl) ⟨70616, by rfl⟩) R141233
theorem R159691 : Reach 159691 := rs (se 1 (by rfl) ⟨119768, by rfl⟩) R239537
theorem R94167 : Reach 94167 := rs (se 1 (by rfl) ⟨70625, by rfl⟩) R141251
theorem R94187 : Reach 94187 := rs (se 1 (by rfl) ⟨70640, by rfl⟩) R141281
theorem R94199 : Reach 94199 := rs (se 1 (by rfl) ⟨70649, by rfl⟩) R141299
theorem R94219 : Reach 94219 := rs (se 1 (by rfl) ⟨70664, by rfl⟩) R141329
theorem R94231 : Reach 94231 := rs (se 1 (by rfl) ⟨70673, by rfl⟩) R141347
theorem R94251 : Reach 94251 := rs (se 1 (by rfl) ⟨70688, by rfl⟩) R141377
theorem R94263 : Reach 94263 := rs (se 1 (by rfl) ⟨70697, by rfl⟩) R141395
theorem R94283 : Reach 94283 := rs (se 1 (by rfl) ⟨70712, by rfl⟩) R141425
theorem R94295 : Reach 94295 := rs (se 1 (by rfl) ⟨70721, by rfl⟩) R141443
theorem R192601 : Reach 192601 := rs (se 2 (by rfl) ⟨72225, by rfl⟩) R144451
theorem R159833 : Reach 159833 := rs (se 2 (by rfl) ⟨59937, by rfl⟩) R119875
theorem R94315 : Reach 94315 := rs (se 1 (by rfl) ⟨70736, by rfl⟩) R141473
theorem R94327 : Reach 94327 := rs (se 1 (by rfl) ⟨70745, by rfl⟩) R141491
theorem R94347 : Reach 94347 := rs (se 1 (by rfl) ⟨70760, by rfl⟩) R141521
theorem R94359 : Reach 94359 := rs (se 1 (by rfl) ⟨70769, by rfl⟩) R141539
theorem R94379 : Reach 94379 := rs (se 1 (by rfl) ⟨70784, by rfl⟩) R141569
theorem R94391 : Reach 94391 := rs (se 1 (by rfl) ⟨70793, by rfl⟩) R141587
theorem R94411 : Reach 94411 := rs (se 1 (by rfl) ⟨70808, by rfl⟩) R141617
theorem R94423 : Reach 94423 := rs (se 1 (by rfl) ⟨70817, by rfl⟩) R141635
theorem R159961 : Reach 159961 := rs (se 2 (by rfl) ⟨59985, by rfl⟩) R119971
theorem R94443 : Reach 94443 := rs (se 1 (by rfl) ⟨70832, by rfl⟩) R141665
theorem R94455 : Reach 94455 := rs (se 1 (by rfl) ⟨70841, by rfl⟩) R141683
theorem R94475 : Reach 94475 := rs (se 1 (by rfl) ⟨70856, by rfl⟩) R141713
theorem R94487 : Reach 94487 := rs (se 1 (by rfl) ⟨70865, by rfl⟩) R141731
theorem R94507 : Reach 94507 := rs (se 1 (by rfl) ⟨70880, by rfl⟩) R141761
theorem R94519 : Reach 94519 := rs (se 1 (by rfl) ⟨70889, by rfl⟩) R141779
theorem R94539 : Reach 94539 := rs (se 1 (by rfl) ⟨70904, by rfl⟩) R141809
theorem R94551 : Reach 94551 := rs (se 1 (by rfl) ⟨70913, by rfl⟩) R141827
theorem R94571 : Reach 94571 := rs (se 1 (by rfl) ⟨70928, by rfl⟩) R141857
theorem R94583 : Reach 94583 := rs (se 1 (by rfl) ⟨70937, by rfl⟩) R141875
theorem R94603 : Reach 94603 := rs (se 1 (by rfl) ⟨70952, by rfl⟩) R141905
theorem R94615 : Reach 94615 := rs (se 1 (by rfl) ⟨70961, by rfl⟩) R141923
theorem R94635 : Reach 94635 := rs (se 1 (by rfl) ⟨70976, by rfl⟩) R141953
theorem R94647 : Reach 94647 := rs (se 1 (by rfl) ⟨70985, by rfl⟩) R141971
theorem R94667 : Reach 94667 := rs (se 1 (by rfl) ⟨71000, by rfl⟩) R142001
theorem R94679 : Reach 94679 := rs (se 1 (by rfl) ⟨71009, by rfl⟩) R142019
theorem R94699 : Reach 94699 := rs (se 1 (by rfl) ⟨71024, by rfl⟩) R142049
theorem R94711 : Reach 94711 := rs (se 1 (by rfl) ⟨71033, by rfl⟩) R142067
theorem R94731 : Reach 94731 := rs (se 1 (by rfl) ⟨71048, by rfl⟩) R142097
theorem R422423 : Reach 422423 := rs (se 1 (by rfl) ⟨316817, by rfl⟩) R633635
theorem R94743 : Reach 94743 := rs (se 1 (by rfl) ⟨71057, by rfl⟩) R142115
theorem R94763 : Reach 94763 := rs (se 1 (by rfl) ⟨71072, by rfl⟩) R142145
theorem R94775 : Reach 94775 := rs (se 1 (by rfl) ⟨71081, by rfl⟩) R142163
theorem R94795 : Reach 94795 := rs (se 1 (by rfl) ⟨71096, by rfl⟩) R142193
theorem R94807 : Reach 94807 := rs (se 1 (by rfl) ⟨71105, by rfl⟩) R142211
theorem R94827 : Reach 94827 := rs (se 1 (by rfl) ⟨71120, by rfl⟩) R142241
theorem R94839 : Reach 94839 := rs (se 1 (by rfl) ⟨71129, by rfl⟩) R142259
theorem R94859 : Reach 94859 := rs (se 1 (by rfl) ⟨71144, by rfl⟩) R142289
theorem R94871 : Reach 94871 := rs (se 1 (by rfl) ⟨71153, by rfl⟩) R142307
theorem R94891 : Reach 94891 := rs (se 1 (by rfl) ⟨71168, by rfl⟩) R142337
theorem R94903 : Reach 94903 := rs (se 1 (by rfl) ⟨71177, by rfl⟩) R142355
theorem R94923 : Reach 94923 := rs (se 1 (by rfl) ⟨71192, by rfl⟩) R142385
theorem R94935 : Reach 94935 := rs (se 1 (by rfl) ⟨71201, by rfl⟩) R142403
theorem R94955 : Reach 94955 := rs (se 1 (by rfl) ⟨71216, by rfl⟩) R142433
theorem R94967 : Reach 94967 := rs (se 1 (by rfl) ⟨71225, by rfl⟩) R142451
theorem R94987 : Reach 94987 := rs (se 1 (by rfl) ⟨71240, by rfl⟩) R142481
theorem R94999 : Reach 94999 := rs (se 1 (by rfl) ⟨71249, by rfl⟩) R142499
theorem R95019 : Reach 95019 := rs (se 1 (by rfl) ⟨71264, by rfl⟩) R142529
theorem R95031 : Reach 95031 := rs (se 1 (by rfl) ⟨71273, by rfl⟩) R142547
theorem R95051 : Reach 95051 := rs (se 1 (by rfl) ⟨71288, by rfl⟩) R142577
theorem R95063 : Reach 95063 := rs (se 1 (by rfl) ⟨71297, by rfl⟩) R142595
theorem R95083 : Reach 95083 := rs (se 1 (by rfl) ⟨71312, by rfl⟩) R142625
theorem R95095 : Reach 95095 := rs (se 1 (by rfl) ⟨71321, by rfl⟩) R142643
theorem R95115 : Reach 95115 := rs (se 1 (by rfl) ⟨71336, by rfl⟩) R142673
theorem R95127 : Reach 95127 := rs (se 1 (by rfl) ⟨71345, by rfl⟩) R142691
theorem R128153 : Reach 128153 := rs (se 2 (by rfl) ⟨48057, by rfl⟩) R96115
theorem R390365 : Reach 390365 := rs (se 3 (by rfl) ⟨73193, by rfl⟩) R146387
theorem R357635 : Reach 357635 := rs (se 1 (by rfl) ⟨268226, by rfl⟩) R536453
theorem R226583 : Reach 226583 := rs (se 1 (by rfl) ⟨169937, by rfl⟩) R339875
theorem R423299 : Reach 423299 := rs (se 1 (by rfl) ⟨317474, by rfl⟩) R634949
theorem R128407 : Reach 128407 := rs (se 1 (by rfl) ⟨96305, by rfl⟩) R192611
theorem R1111475 : Reach 1111475 := rs (se 1 (by rfl) ⟨833606, by rfl⟩) R1667213
theorem R1570265 : Reach 1570265 := rs (se 2 (by rfl) ⟨588849, by rfl⟩) R1177699
theorem R259787 : Reach 259787 := rs (se 1 (by rfl) ⟨194840, by rfl⟩) R389681
theorem R358091 : Reach 358091 := rs (se 1 (by rfl) ⟨268568, by rfl⟩) R537137
theorem R358289 : Reach 358289 := rs (se 2 (by rfl) ⟨134358, by rfl⟩) R268717
theorem R391063 : Reach 391063 := rs (se 1 (by rfl) ⟨293297, by rfl⟩) R586595
theorem R423883 : Reach 423883 := rs (se 1 (by rfl) ⟨317912, by rfl⟩) R635825
theorem R456749 : Reach 456749 := rs (se 3 (by rfl) ⟨85640, by rfl⟩) R171281
theorem R260185 : Reach 260185 := rs (se 2 (by rfl) ⟨97569, by rfl⟩) R195139
theorem R129163 : Reach 129163 := rs (se 1 (by rfl) ⟨96872, by rfl⟩) R193745
theorem R293195 : Reach 293195 := rs (se 1 (by rfl) ⟨219896, by rfl⟩) R439793
theorem R784997 : Reach 784997 := rs (se 4 (by rfl) ⟨73593, by rfl⟩) R147187
theorem R162419 : Reach 162419 := rs (se 1 (by rfl) ⟨121814, by rfl⟩) R243629
theorem R359063 : Reach 359063 := rs (se 1 (by rfl) ⟨269297, by rfl⟩) R538595
theorem R359129 : Reach 359129 := rs (se 2 (by rfl) ⟨134673, by rfl⟩) R269347
theorem R359261 : Reach 359261 := rs (se 3 (by rfl) ⟨67361, by rfl⟩) R134723
theorem R293939 : Reach 293939 := rs (se 1 (by rfl) ⟨220454, by rfl⟩) R440909
theorem R195635 : Reach 195635 := rs (se 1 (by rfl) ⟨146726, by rfl⟩) R293453
theorem R97399 : Reach 97399 := rs (se 1 (by rfl) ⟨73049, by rfl⟩) R146099
theorem R392465 : Reach 392465 := rs (se 2 (by rfl) ⟨147174, by rfl⟩) R294349
theorem R261427 : Reach 261427 := rs (se 1 (by rfl) ⟨196070, by rfl⟩) R392141
theorem R130457 : Reach 130457 := rs (se 2 (by rfl) ⟨48921, by rfl⟩) R97843
theorem R3899011 : Reach 3899011 := rs (se 1 (by rfl) ⟨2924258, by rfl⟩) R5848517
theorem R196481 : Reach 196481 := rs (se 2 (by rfl) ⟨73680, by rfl⟩) R147361
theorem R98219 : Reach 98219 := rs (se 1 (by rfl) ⟨73664, by rfl⟩) R147329
theorem R1343411 : Reach 1343411 := rs (se 1 (by rfl) ⟨1007558, by rfl⟩) R2015117
theorem R294835 : Reach 294835 := rs (se 1 (by rfl) ⟨221126, by rfl⟩) R442253
theorem R131215 : Reach 131215 := rs (se 1 (by rfl) ⟨98411, by rfl⟩) R196823
theorem R360719 : Reach 360719 := rs (se 1 (by rfl) ⟨270539, by rfl⟩) R541079
theorem R17170805 : Reach 17170805 := rs (se 5 (by rfl) ⟨804881, by rfl⟩) R1609763
theorem R3343193 : Reach 3343193 := rs (se 2 (by rfl) ⟨1253697, by rfl⟩) R2507395
theorem R99343 : Reach 99343 := rs (se 1 (by rfl) ⟨74507, by rfl⟩) R149015
theorem R132359 : Reach 132359 := rs (se 1 (by rfl) ⟨99269, by rfl⟩) R198539
theorem R230809 : Reach 230809 := rs (se 2 (by rfl) ⟨86553, by rfl⟩) R173107
theorem R132553 : Reach 132553 := rs (se 2 (by rfl) ⟨49707, by rfl⟩) R99415
theorem R230971 : Reach 230971 := rs (se 1 (by rfl) ⟨173228, by rfl⟩) R346457
theorem R296567 : Reach 296567 := rs (se 1 (by rfl) ⟨222425, by rfl⟩) R444851
theorem R231113 : Reach 231113 := rs (se 2 (by rfl) ⟨86667, by rfl⟩) R173335
theorem R2131865 : Reach 2131865 := rs (se 2 (by rfl) ⟨799449, by rfl⟩) R1598899
theorem R1542041 : Reach 1542041 := rs (se 2 (by rfl) ⟨578265, by rfl⟩) R1156531
theorem R165817 : Reach 165817 := rs (se 2 (by rfl) ⟨62181, by rfl⟩) R124363
theorem R133111 : Reach 133111 := rs (se 1 (by rfl) ⟨99833, by rfl⟩) R199667
theorem R231457 : Reach 231457 := rs (se 2 (by rfl) ⟨86796, by rfl⟩) R173593
theorem R133255 : Reach 133255 := rs (se 1 (by rfl) ⟨99941, by rfl⟩) R199883
theorem R264377 : Reach 264377 := rs (se 2 (by rfl) ⟨99141, by rfl⟩) R198283
theorem R592109 : Reach 592109 := rs (se 3 (by rfl) ⟨111020, by rfl⟩) R222041
theorem R264491 : Reach 264491 := rs (se 1 (by rfl) ⟨198368, by rfl⟩) R396737
theorem R232055 : Reach 232055 := rs (se 1 (by rfl) ⟨174041, by rfl⟩) R348083
theorem R133817 : Reach 133817 := rs (se 2 (by rfl) ⟨50181, by rfl⟩) R100363
theorem R133903 : Reach 133903 := rs (se 1 (by rfl) ⟨100427, by rfl⟩) R200855
theorem R133931 : Reach 133931 := rs (se 1 (by rfl) ⟨100448, by rfl⟩) R200897
theorem R101179 : Reach 101179 := rs (se 1 (by rfl) ⟨75884, by rfl⟩) R151769
theorem R527249 : Reach 527249 := rs (se 2 (by rfl) ⟨197718, by rfl⟩) R395437
theorem R363473 : Reach 363473 := rs (se 2 (by rfl) ⟨136302, by rfl⟩) R272605
theorem R167201 : Reach 167201 := rs (se 2 (by rfl) ⟨62700, by rfl⟩) R125401
theorem R363809 : Reach 363809 := rs (se 2 (by rfl) ⟨136428, by rfl⟩) R272857
theorem R527705 : Reach 527705 := rs (se 2 (by rfl) ⟨197889, by rfl⟩) R395779
theorem R167287 : Reach 167287 := rs (se 1 (by rfl) ⟨125465, by rfl⟩) R250931
theorem R265619 : Reach 265619 := rs (se 1 (by rfl) ⟨199214, by rfl⟩) R398429
theorem R462347 : Reach 462347 := rs (se 1 (by rfl) ⟨346760, by rfl⟩) R693521
theorem R462509 : Reach 462509 := rs (se 3 (by rfl) ⟨86720, by rfl⟩) R173441
theorem R266017 : Reach 266017 := rs (se 2 (by rfl) ⟨99756, by rfl⟩) R199513
theorem R233351 : Reach 233351 := rs (se 1 (by rfl) ⟨175013, by rfl⟩) R350027
theorem R233401 : Reach 233401 := rs (se 2 (by rfl) ⟨87525, by rfl⟩) R175051
theorem R888893 : Reach 888893 := rs (se 3 (by rfl) ⟨166667, by rfl⟩) R333335
theorem R135355 : Reach 135355 := rs (se 1 (by rfl) ⟨101516, by rfl⟩) R203033
theorem R430451 : Reach 430451 := rs (se 1 (by rfl) ⟨322838, by rfl⟩) R645677
theorem R1446365 : Reach 1446365 := rs (se 3 (by rfl) ⟨271193, by rfl⟩) R542387
theorem R102919 : Reach 102919 := rs (se 1 (by rfl) ⟨77189, by rfl⟩) R154379
theorem R233999 : Reach 233999 := rs (se 1 (by rfl) ⟨175499, by rfl⟩) R350999
theorem R266905 : Reach 266905 := rs (se 2 (by rfl) ⟨100089, by rfl⟩) R200179
theorem R103099 : Reach 103099 := rs (se 1 (by rfl) ⟨77324, by rfl⟩) R154649
theorem R267293 : Reach 267293 := rs (se 3 (by rfl) ⟨50117, by rfl⟩) R100235
theorem R103567 : Reach 103567 := rs (se 1 (by rfl) ⟨77675, by rfl⟩) R155351
theorem R234697 : Reach 234697 := rs (se 2 (by rfl) ⟨88011, by rfl⟩) R176023
theorem R464129 : Reach 464129 := rs (se 2 (by rfl) ⟨174048, by rfl⟩) R348097
theorem R595259 : Reach 595259 := rs (se 1 (by rfl) ⟨446444, by rfl⟩) R892889
theorem R234839 : Reach 234839 := rs (se 1 (by rfl) ⟨176129, by rfl⟩) R352259
theorem R136763 : Reach 136763 := rs (se 1 (by rfl) ⟨102572, by rfl⟩) R205145
theorem R136823 : Reach 136823 := rs (se 1 (by rfl) ⟨102617, by rfl⟩) R205235
theorem R104071 : Reach 104071 := rs (se 1 (by rfl) ⟨78053, by rfl⟩) R156107
theorem R136847 : Reach 136847 := rs (se 1 (by rfl) ⟨102635, by rfl⟩) R205271
theorem R136889 : Reach 136889 := rs (se 2 (by rfl) ⟨51333, by rfl⟩) R102667
theorem R136891 : Reach 136891 := rs (se 1 (by rfl) ⟨102668, by rfl⟩) R205337
theorem R136967 : Reach 136967 := rs (se 1 (by rfl) ⟨102725, by rfl⟩) R205451
theorem R137003 : Reach 137003 := rs (se 1 (by rfl) ⟨102752, by rfl⟩) R205505
theorem R104251 : Reach 104251 := rs (se 1 (by rfl) ⟨78188, by rfl⟩) R156377
theorem R137033 : Reach 137033 := rs (se 2 (by rfl) ⟨51387, by rfl⟩) R102775
theorem R300935 : Reach 300935 := rs (se 1 (by rfl) ⟨225701, by rfl⟩) R451403
theorem R137147 : Reach 137147 := rs (se 1 (by rfl) ⟨102860, by rfl⟩) R205721
theorem R137207 : Reach 137207 := rs (se 1 (by rfl) ⟨102905, by rfl⟩) R205811
theorem R137231 : Reach 137231 := rs (se 1 (by rfl) ⟨102923, by rfl⟩) R205847
theorem R464939 : Reach 464939 := rs (se 1 (by rfl) ⟨348704, by rfl⟩) R697409
theorem R137273 : Reach 137273 := rs (se 2 (by rfl) ⟨51477, by rfl⟩) R102955
theorem R137351 : Reach 137351 := rs (se 1 (by rfl) ⟨103013, by rfl⟩) R206027
theorem R137387 : Reach 137387 := rs (se 1 (by rfl) ⟨103040, by rfl⟩) R206081
theorem R137417 : Reach 137417 := rs (se 2 (by rfl) ⟨51531, by rfl⟩) R103063
theorem R104719 : Reach 104719 := rs (se 1 (by rfl) ⟨78539, by rfl⟩) R157079
theorem R137531 : Reach 137531 := rs (se 1 (by rfl) ⟨103148, by rfl⟩) R206297
theorem R137591 : Reach 137591 := rs (se 1 (by rfl) ⟨103193, by rfl⟩) R206387
theorem R137615 : Reach 137615 := rs (se 1 (by rfl) ⟨103211, by rfl⟩) R206423
theorem R137657 : Reach 137657 := rs (se 2 (by rfl) ⟨51621, by rfl⟩) R103243
theorem R530873 : Reach 530873 := rs (se 2 (by rfl) ⟨199077, by rfl⟩) R398155
theorem R137735 : Reach 137735 := rs (se 1 (by rfl) ⟨103301, by rfl⟩) R206603
theorem R137771 : Reach 137771 := rs (se 1 (by rfl) ⟨103328, by rfl⟩) R206657
theorem R137801 : Reach 137801 := rs (se 2 (by rfl) ⟨51675, by rfl⟩) R103351
theorem R137915 : Reach 137915 := rs (se 1 (by rfl) ⟨103436, by rfl⟩) R206873
theorem R1252057 : Reach 1252057 := rs (se 2 (by rfl) ⟨469521, by rfl⟩) R939043
theorem R137975 : Reach 137975 := rs (se 1 (by rfl) ⟨103481, by rfl⟩) R206963
theorem R105223 : Reach 105223 := rs (se 1 (by rfl) ⟨78917, by rfl⟩) R157835
theorem R137999 : Reach 137999 := rs (se 1 (by rfl) ⟨103499, by rfl⟩) R206999
theorem R138041 : Reach 138041 := rs (se 2 (by rfl) ⟨51765, by rfl⟩) R103531
theorem R138119 : Reach 138119 := rs (se 1 (by rfl) ⟨103589, by rfl⟩) R207179
theorem R138155 : Reach 138155 := rs (se 1 (by rfl) ⟨103616, by rfl⟩) R207233
theorem R105403 : Reach 105403 := rs (se 1 (by rfl) ⟨79052, by rfl⟩) R158105
theorem R138185 : Reach 138185 := rs (se 2 (by rfl) ⟨51819, by rfl⟩) R103639
theorem R433117 : Reach 433117 := rs (se 3 (by rfl) ⟨81209, by rfl⟩) R162419
theorem R400427 : Reach 400427 := rs (se 1 (by rfl) ⟨300320, by rfl⟩) R600641
theorem R138299 : Reach 138299 := rs (se 1 (by rfl) ⟨103724, by rfl⟩) R207449
theorem R138359 : Reach 138359 := rs (se 1 (by rfl) ⟨103769, by rfl⟩) R207539
theorem R138383 : Reach 138383 := rs (se 1 (by rfl) ⟨103787, by rfl⟩) R207575
theorem R138425 : Reach 138425 := rs (se 2 (by rfl) ⟨51909, by rfl⟩) R103819
theorem R171209 : Reach 171209 := rs (se 2 (by rfl) ⟨64203, by rfl⟩) R128407
theorem R138503 : Reach 138503 := rs (se 1 (by rfl) ⟨103877, by rfl⟩) R207755
theorem R138539 : Reach 138539 := rs (se 1 (by rfl) ⟨103904, by rfl⟩) R207809
theorem R466235 : Reach 466235 := rs (se 1 (by rfl) ⟨349676, by rfl⟩) R699353
theorem R138569 : Reach 138569 := rs (se 2 (by rfl) ⟨51963, by rfl⟩) R103927
theorem R236915 : Reach 236915 := rs (se 1 (by rfl) ⟨177686, by rfl⟩) R355373
theorem R105871 : Reach 105871 := rs (se 1 (by rfl) ⟨79403, by rfl⟩) R158807
theorem R138683 : Reach 138683 := rs (se 1 (by rfl) ⟨104012, by rfl⟩) R208025
theorem R466397 : Reach 466397 := rs (se 3 (by rfl) ⟨87449, by rfl⟩) R174899
theorem R138743 : Reach 138743 := rs (se 1 (by rfl) ⟨104057, by rfl⟩) R208115
theorem R1121795 : Reach 1121795 := rs (se 1 (by rfl) ⟨841346, by rfl⟩) R1682693
theorem R138767 : Reach 138767 := rs (se 1 (by rfl) ⟨104075, by rfl⟩) R208151
theorem R728605 : Reach 728605 := rs (se 3 (by rfl) ⟨136613, by rfl⟩) R273227
theorem R269867 : Reach 269867 := rs (se 1 (by rfl) ⟨202400, by rfl⟩) R404801
theorem R138809 : Reach 138809 := rs (se 2 (by rfl) ⟨52053, by rfl⟩) R104107
theorem R138887 : Reach 138887 := rs (se 1 (by rfl) ⟨104165, by rfl⟩) R208331
theorem R138923 : Reach 138923 := rs (se 1 (by rfl) ⟨104192, by rfl⟩) R208385
theorem R138953 : Reach 138953 := rs (se 2 (by rfl) ⟨52107, by rfl⟩) R104215
theorem R466721 : Reach 466721 := rs (se 2 (by rfl) ⟨175020, by rfl⟩) R350041
theorem R139067 : Reach 139067 := rs (se 1 (by rfl) ⟨104300, by rfl⟩) R208601
theorem R1122137 : Reach 1122137 := rs (se 2 (by rfl) ⟨420801, by rfl⟩) R841603
theorem R139127 : Reach 139127 := rs (se 1 (by rfl) ⟨104345, by rfl⟩) R208691
theorem R237431 : Reach 237431 := rs (se 1 (by rfl) ⟨178073, by rfl⟩) R356147
theorem R499591 : Reach 499591 := rs (se 1 (by rfl) ⟨374693, by rfl⟩) R749387
theorem R106375 : Reach 106375 := rs (se 1 (by rfl) ⟨79781, by rfl⟩) R159563
theorem R139151 : Reach 139151 := rs (se 1 (by rfl) ⟨104363, by rfl⟩) R208727
theorem R139193 : Reach 139193 := rs (se 2 (by rfl) ⟨52197, by rfl⟩) R104395
theorem R565177 : Reach 565177 := rs (se 2 (by rfl) ⟨211941, by rfl⟩) R423883
theorem R139271 : Reach 139271 := rs (se 1 (by rfl) ⟨104453, by rfl⟩) R208907
theorem R139307 : Reach 139307 := rs (se 1 (by rfl) ⟨104480, by rfl⟩) R208961
theorem R106555 : Reach 106555 := rs (se 1 (by rfl) ⟨79916, by rfl⟩) R159833
theorem R139337 : Reach 139337 := rs (se 2 (by rfl) ⟨52251, by rfl⟩) R104503
theorem R172217 : Reach 172217 := rs (se 2 (by rfl) ⟨64581, by rfl⟩) R129163
theorem R139451 : Reach 139451 := rs (se 1 (by rfl) ⟨104588, by rfl⟩) R209177
theorem R139511 : Reach 139511 := rs (se 1 (by rfl) ⟨104633, by rfl⟩) R209267
theorem R139535 : Reach 139535 := rs (se 1 (by rfl) ⟨104651, by rfl⟩) R209303
theorem R139577 : Reach 139577 := rs (se 2 (by rfl) ⟨52341, by rfl⟩) R104683
theorem R139655 : Reach 139655 := rs (se 1 (by rfl) ⟨104741, by rfl⟩) R209483
theorem R139691 : Reach 139691 := rs (se 1 (by rfl) ⟨104768, by rfl⟩) R209537
theorem R139721 : Reach 139721 := rs (se 2 (by rfl) ⟨52395, by rfl⟩) R104791
theorem R893389 : Reach 893389 := rs (se 3 (by rfl) ⟨167510, by rfl⟩) R335021
theorem R139835 : Reach 139835 := rs (se 1 (by rfl) ⟨104876, by rfl⟩) R209753
theorem R139895 : Reach 139895 := rs (se 1 (by rfl) ⟨104921, by rfl⟩) R209843
theorem R139919 : Reach 139919 := rs (se 1 (by rfl) ⟨104939, by rfl⟩) R209879
theorem R139961 : Reach 139961 := rs (se 2 (by rfl) ⟨52485, by rfl⟩) R104971
theorem R467693 : Reach 467693 := rs (se 3 (by rfl) ⟨87692, by rfl⟩) R175385
theorem R140039 : Reach 140039 := rs (se 1 (by rfl) ⟨105029, by rfl⟩) R210059
theorem R533263 : Reach 533263 := rs (se 1 (by rfl) ⟨399947, by rfl⟩) R799895
theorem R140075 : Reach 140075 := rs (se 1 (by rfl) ⟨105056, by rfl⟩) R210113
theorem R140105 : Reach 140105 := rs (se 2 (by rfl) ⟨52539, by rfl⟩) R105079
theorem R238423 : Reach 238423 := rs (se 1 (by rfl) ⟨178817, by rfl⟩) R357635
theorem R598873 : Reach 598873 := rs (se 2 (by rfl) ⟨224577, by rfl⟩) R449155
theorem R205703 : Reach 205703 := rs (se 1 (by rfl) ⟨154277, by rfl⟩) R308555
theorem R140219 : Reach 140219 := rs (se 1 (by rfl) ⟨105164, by rfl⟩) R210329
theorem R140279 : Reach 140279 := rs (se 1 (by rfl) ⟨105209, by rfl⟩) R210419
theorem R140303 : Reach 140303 := rs (se 1 (by rfl) ⟨105227, by rfl⟩) R210455
theorem R140345 : Reach 140345 := rs (se 2 (by rfl) ⟨52629, by rfl⟩) R105259
theorem R205883 : Reach 205883 := rs (se 1 (by rfl) ⟨154412, by rfl⟩) R308825
theorem R173191 : Reach 173191 := rs (se 1 (by rfl) ⟨129893, by rfl⟩) R259787
theorem R140423 : Reach 140423 := rs (se 1 (by rfl) ⟨105317, by rfl⟩) R210635
theorem R238727 : Reach 238727 := rs (se 1 (by rfl) ⟨179045, by rfl⟩) R358091
theorem R140459 : Reach 140459 := rs (se 1 (by rfl) ⟨105344, by rfl⟩) R210689
theorem R206009 : Reach 206009 := rs (se 2 (by rfl) ⟨77253, by rfl⟩) R154507
theorem R140489 : Reach 140489 := rs (se 2 (by rfl) ⟨52683, by rfl⟩) R105367
theorem R238859 : Reach 238859 := rs (se 1 (by rfl) ⟨179144, by rfl⟩) R358289
theorem R140603 : Reach 140603 := rs (se 1 (by rfl) ⟨105452, by rfl⟩) R210905
theorem R402803 : Reach 402803 := rs (se 1 (by rfl) ⟨302102, by rfl⟩) R604205
theorem R304499 : Reach 304499 := rs (se 1 (by rfl) ⟨228374, by rfl⟩) R456749
theorem R140663 : Reach 140663 := rs (se 1 (by rfl) ⟨105497, by rfl⟩) R210995
theorem R140687 : Reach 140687 := rs (se 1 (by rfl) ⟨105515, by rfl⟩) R211031
theorem R140729 : Reach 140729 := rs (se 2 (by rfl) ⟨52773, by rfl⟩) R105547
theorem R140807 : Reach 140807 := rs (se 1 (by rfl) ⟨105605, by rfl⟩) R211211
theorem R206351 : Reach 206351 := rs (se 1 (by rfl) ⟨154763, by rfl⟩) R309527
theorem R468503 : Reach 468503 := rs (se 1 (by rfl) ⟨351377, by rfl⟩) R702755
theorem R206369 : Reach 206369 := rs (se 2 (by rfl) ⟨77388, by rfl⟩) R154777
theorem R140843 : Reach 140843 := rs (se 1 (by rfl) ⟨105632, by rfl⟩) R211265
theorem R140873 : Reach 140873 := rs (se 2 (by rfl) ⟨52827, by rfl⟩) R105655
theorem R140987 : Reach 140987 := rs (se 1 (by rfl) ⟨105740, by rfl⟩) R211481
theorem R141047 : Reach 141047 := rs (se 1 (by rfl) ⟨105785, by rfl⟩) R211571
theorem R141071 : Reach 141071 := rs (se 1 (by rfl) ⟨105803, by rfl⟩) R211607
theorem R239375 : Reach 239375 := rs (se 1 (by rfl) ⟨179531, by rfl⟩) R359063
theorem R141113 : Reach 141113 := rs (se 2 (by rfl) ⟨52917, by rfl⟩) R105835
theorem R239419 : Reach 239419 := rs (se 1 (by rfl) ⟨179564, by rfl⟩) R359129
theorem R206711 : Reach 206711 := rs (se 1 (by rfl) ⟨155033, by rfl⟩) R310067
theorem R141191 : Reach 141191 := rs (se 1 (by rfl) ⟨105893, by rfl⟩) R211787
theorem R239507 : Reach 239507 := rs (se 1 (by rfl) ⟨179630, by rfl⟩) R359261
theorem R141227 : Reach 141227 := rs (se 1 (by rfl) ⟨105920, by rfl⟩) R211841
theorem R141257 : Reach 141257 := rs (se 2 (by rfl) ⟨52971, by rfl⟩) R105943
theorem R534539 : Reach 534539 := rs (se 1 (by rfl) ⟨400904, by rfl⟩) R801809
theorem R206891 : Reach 206891 := rs (se 1 (by rfl) ⟨155168, by rfl⟩) R310337
theorem R141371 : Reach 141371 := rs (se 1 (by rfl) ⟨106028, by rfl⟩) R212057
theorem R141431 : Reach 141431 := rs (se 1 (by rfl) ⟨106073, by rfl⟩) R212147
theorem R141455 : Reach 141455 := rs (se 1 (by rfl) ⟨106091, by rfl⟩) R212183
theorem R141497 : Reach 141497 := rs (se 2 (by rfl) ⟨53061, by rfl⟩) R106123
theorem R534721 : Reach 534721 := rs (se 2 (by rfl) ⟨200520, by rfl⟩) R401041
theorem R272585 : Reach 272585 := rs (se 2 (by rfl) ⟨102219, by rfl⟩) R204439
theorem R141575 : Reach 141575 := rs (se 1 (by rfl) ⟨106181, by rfl⟩) R212363
theorem R141611 : Reach 141611 := rs (se 1 (by rfl) ⟨106208, by rfl⟩) R212417
theorem R141641 : Reach 141641 := rs (se 2 (by rfl) ⟨53115, by rfl⟩) R106231
theorem R207251 : Reach 207251 := rs (se 1 (by rfl) ⟨155438, by rfl⟩) R310877
theorem R141755 : Reach 141755 := rs (se 1 (by rfl) ⟨106316, by rfl⟩) R212633
theorem R207305 : Reach 207305 := rs (se 2 (by rfl) ⟨77739, by rfl⟩) R155479
theorem R141815 : Reach 141815 := rs (se 1 (by rfl) ⟨106361, by rfl⟩) R212723
theorem R141839 : Reach 141839 := rs (se 1 (by rfl) ⟨106379, by rfl⟩) R212759
theorem R141881 : Reach 141881 := rs (se 2 (by rfl) ⟨53205, by rfl⟩) R106411
theorem R895607 : Reach 895607 := rs (se 1 (by rfl) ⟨671705, by rfl⟩) R1343411
theorem R141959 : Reach 141959 := rs (se 1 (by rfl) ⟨106469, by rfl⟩) R212939
theorem R141995 : Reach 141995 := rs (se 1 (by rfl) ⟨106496, by rfl⟩) R212993
theorem R174793 : Reach 174793 := rs (se 2 (by rfl) ⟨65547, by rfl⟩) R131095
theorem R142025 : Reach 142025 := rs (se 2 (by rfl) ⟨53259, by rfl⟩) R106519
theorem R142139 : Reach 142139 := rs (se 1 (by rfl) ⟨106604, by rfl⟩) R213209
theorem R142199 : Reach 142199 := rs (se 1 (by rfl) ⟨106649, by rfl⟩) R213299
theorem R142223 : Reach 142223 := rs (se 1 (by rfl) ⟨106667, by rfl⟩) R213335
theorem R142265 : Reach 142265 := rs (se 2 (by rfl) ⟨53349, by rfl⟩) R106699
theorem R240641 : Reach 240641 := rs (se 2 (by rfl) ⟨90240, by rfl⟩) R180481
theorem R142343 : Reach 142343 := rs (se 1 (by rfl) ⟨106757, by rfl⟩) R213515
theorem R142379 : Reach 142379 := rs (se 1 (by rfl) ⟨106784, by rfl⟩) R213569
theorem R142409 : Reach 142409 := rs (se 2 (by rfl) ⟨53403, by rfl⟩) R106807
theorem R208007 : Reach 208007 := rs (se 1 (by rfl) ⟨156005, by rfl⟩) R312011
theorem R142523 : Reach 142523 := rs (se 1 (by rfl) ⟨106892, by rfl⟩) R213785
theorem R142583 : Reach 142583 := rs (se 1 (by rfl) ⟨106937, by rfl⟩) R213875
theorem R142607 : Reach 142607 := rs (se 1 (by rfl) ⟨106955, by rfl⟩) R213911
theorem R142649 : Reach 142649 := rs (se 2 (by rfl) ⟨53493, by rfl⟩) R106987
theorem R208187 : Reach 208187 := rs (se 1 (by rfl) ⟨156140, by rfl⟩) R312281
theorem R208313 : Reach 208313 := rs (se 2 (by rfl) ⟨78117, by rfl⟩) R156235
theorem R1420753 : Reach 1420753 := rs (se 2 (by rfl) ⟨532782, by rfl⟩) R1065565
theorem R896579 : Reach 896579 := rs (se 1 (by rfl) ⟨672434, by rfl⟩) R1344869
theorem R601667 : Reach 601667 := rs (se 1 (by rfl) ⟨451250, by rfl⟩) R902501
theorem R208585 : Reach 208585 := rs (se 2 (by rfl) ⟨78219, by rfl⟩) R156439
theorem R143095 : Reach 143095 := rs (se 1 (by rfl) ⟨107321, by rfl⟩) R214643
theorem R208655 : Reach 208655 := rs (se 1 (by rfl) ⟨156491, by rfl⟩) R312983
theorem R405263 : Reach 405263 := rs (se 1 (by rfl) ⟨303947, by rfl⟩) R607895
theorem R208673 : Reach 208673 := rs (se 2 (by rfl) ⟨78252, by rfl⟩) R156505
theorem R209015 : Reach 209015 := rs (se 1 (by rfl) ⟨156761, by rfl⟩) R313523
theorem R209195 : Reach 209195 := rs (se 1 (by rfl) ⟨156896, by rfl⟩) R313793
theorem R569753 : Reach 569753 := rs (se 2 (by rfl) ⟨213657, by rfl⟩) R427315
theorem R471581 : Reach 471581 := rs (se 3 (by rfl) ⟨88421, by rfl⟩) R176843
theorem R537131 : Reach 537131 := rs (se 1 (by rfl) ⟨402848, by rfl⟩) R805697
theorem R307799 : Reach 307799 := rs (se 1 (by rfl) ⟨230849, by rfl⟩) R461699
theorem R209555 : Reach 209555 := rs (se 1 (by rfl) ⟨157166, by rfl⟩) R314333
theorem R209609 : Reach 209609 := rs (se 2 (by rfl) ⟨78603, by rfl⟩) R157207
theorem R144263 : Reach 144263 := rs (se 1 (by rfl) ⟨108197, by rfl⟩) R216395
theorem R472067 : Reach 472067 := rs (se 1 (by rfl) ⟨354050, by rfl⟩) R708101
theorem R308285 : Reach 308285 := rs (se 3 (by rfl) ⟨57803, by rfl⟩) R115607
theorem R177299 : Reach 177299 := rs (se 1 (by rfl) ⟨132974, by rfl⟩) R265949
theorem R505025 : Reach 505025 := rs (se 2 (by rfl) ⟨189384, by rfl⟩) R378769
theorem R341263 : Reach 341263 := rs (se 1 (by rfl) ⟨255947, by rfl⟩) R511895
theorem R701729 : Reach 701729 := rs (se 2 (by rfl) ⟨263148, by rfl⟩) R526297
theorem R177527 : Reach 177527 := rs (se 1 (by rfl) ⟨133145, by rfl⟩) R266291
theorem R210311 : Reach 210311 := rs (se 1 (by rfl) ⟨157733, by rfl⟩) R315467
theorem R210491 : Reach 210491 := rs (se 1 (by rfl) ⟨157868, by rfl⟩) R315737
theorem R210617 : Reach 210617 := rs (se 2 (by rfl) ⟨78981, by rfl⟩) R157963
theorem R669377 : Reach 669377 := rs (se 2 (by rfl) ⟨251016, by rfl⟩) R502033
theorem R341741 : Reach 341741 := rs (se 3 (by rfl) ⟨64076, by rfl⟩) R128153
theorem R210959 : Reach 210959 := rs (se 1 (by rfl) ⟨158219, by rfl⟩) R316439
theorem R210977 : Reach 210977 := rs (se 2 (by rfl) ⟨79116, by rfl⟩) R158233
theorem R440407 : Reach 440407 := rs (se 1 (by rfl) ⟨330305, by rfl⟩) R660611
theorem R538913 : Reach 538913 := rs (se 2 (by rfl) ⟨202092, by rfl⟩) R404185
theorem R211319 : Reach 211319 := rs (se 1 (by rfl) ⟨158489, by rfl⟩) R316979
theorem R309689 : Reach 309689 := rs (se 2 (by rfl) ⟨116133, by rfl⟩) R232267
theorem R211499 : Reach 211499 := rs (se 1 (by rfl) ⟨158624, by rfl⟩) R317249
theorem R473687 : Reach 473687 := rs (se 1 (by rfl) ⟨355265, by rfl⟩) R710531
theorem R1522547 : Reach 1522547 := rs (se 1 (by rfl) ⟨1141910, by rfl⟩) R2283821
theorem R211859 : Reach 211859 := rs (se 1 (by rfl) ⟨158894, by rfl⟩) R317789
theorem R211913 : Reach 211913 := rs (se 2 (by rfl) ⟨79467, by rfl⟩) R158935
theorem R310283 : Reach 310283 := rs (se 1 (by rfl) ⟨232712, by rfl⟩) R465425
theorem R179243 : Reach 179243 := rs (se 1 (by rfl) ⟨134432, by rfl⟩) R268865
theorem R474173 : Reach 474173 := rs (se 3 (by rfl) ⟨88907, by rfl⟩) R177815
theorem R310391 : Reach 310391 := rs (se 1 (by rfl) ⟨232793, by rfl⟩) R465587
theorem R113783 : Reach 113783 := rs (se 1 (by rfl) ⟨85337, by rfl⟩) R170675
theorem R277705 : Reach 277705 := rs (se 2 (by rfl) ⟨104139, by rfl⟩) R208279
theorem R179471 : Reach 179471 := rs (se 1 (by rfl) ⟨134603, by rfl⟩) R269207
theorem R867617 : Reach 867617 := rs (se 2 (by rfl) ⟨325356, by rfl⟩) R650713
theorem R376123 : Reach 376123 := rs (se 1 (by rfl) ⟨282092, by rfl⟩) R564185
theorem R900497 : Reach 900497 := rs (se 2 (by rfl) ⟨337686, by rfl⟩) R675373
theorem R1064339 : Reach 1064339 := rs (se 1 (by rfl) ⟨798254, by rfl⟩) R1596509
theorem R212615 : Reach 212615 := rs (se 1 (by rfl) ⟨159461, by rfl⟩) R318923
theorem R310985 : Reach 310985 := rs (se 2 (by rfl) ⟨116619, by rfl⟩) R233239
theorem R212795 : Reach 212795 := rs (se 1 (by rfl) ⟨159596, by rfl⟩) R319193
theorem R507833 : Reach 507833 := rs (se 2 (by rfl) ⟨190437, by rfl⟩) R380875
theorem R212921 : Reach 212921 := rs (se 2 (by rfl) ⟨79845, by rfl⟩) R159691
theorem R213263 : Reach 213263 := rs (se 1 (by rfl) ⟨159947, by rfl⟩) R319895
theorem R213281 : Reach 213281 := rs (se 2 (by rfl) ⟨79980, by rfl⟩) R159961
theorem R311687 : Reach 311687 := rs (se 1 (by rfl) ⟨233765, by rfl⟩) R467531
theorem R672259 : Reach 672259 := rs (se 1 (by rfl) ⟨504194, by rfl⟩) R1008389
theorem R213623 : Reach 213623 := rs (se 1 (by rfl) ⟨160217, by rfl⟩) R320435
theorem R312065 : Reach 312065 := rs (se 2 (by rfl) ⟨117024, by rfl⟩) R234049
theorem R213803 : Reach 213803 := rs (se 1 (by rfl) ⟨160352, by rfl⟩) R320705
theorem R475955 : Reach 475955 := rs (se 1 (by rfl) ⟨356966, by rfl⟩) R713933
theorem R3195875 : Reach 3195875 := rs (se 1 (by rfl) ⟨2396906, by rfl⟩) R4793813
theorem R312331 : Reach 312331 := rs (se 1 (by rfl) ⟨234248, by rfl⟩) R468497
theorem R476279 : Reach 476279 := rs (se 1 (by rfl) ⟨357209, by rfl⟩) R714419
theorem R181775 : Reach 181775 := rs (se 1 (by rfl) ⟨136331, by rfl⟩) R272663
theorem R312875 : Reach 312875 := rs (se 1 (by rfl) ⟨234656, by rfl⟩) R469313
theorem R214663 : Reach 214663 := rs (se 1 (by rfl) ⟨160997, by rfl⟩) R321995
theorem R509905 : Reach 509905 := rs (se 2 (by rfl) ⟨191214, by rfl⟩) R382429
theorem R575453 : Reach 575453 := rs (se 3 (by rfl) ⟨107897, by rfl⟩) R215795
theorem R477245 : Reach 477245 := rs (se 3 (by rfl) ⟨89483, by rfl⟩) R178967
theorem R477251 : Reach 477251 := rs (se 1 (by rfl) ⟨357938, by rfl⟩) R715877
theorem R1099909 : Reach 1099909 := rs (se 4 (by rfl) ⟨103116, by rfl⟩) R206233
theorem R510209 : Reach 510209 := rs (se 2 (by rfl) ⟨191328, by rfl⟩) R382657
theorem R346427 : Reach 346427 := rs (se 1 (by rfl) ⟨259820, by rfl⟩) R519641
theorem R477575 : Reach 477575 := rs (se 1 (by rfl) ⟨358181, by rfl⟩) R716363
theorem R281033 : Reach 281033 := rs (se 2 (by rfl) ⟨105387, by rfl⟩) R210775
theorem R379511 : Reach 379511 := rs (se 1 (by rfl) ⟨284633, by rfl⟩) R569267
theorem R510637 : Reach 510637 := rs (se 3 (by rfl) ⟨95744, by rfl⟩) R191489
theorem R1231553 : Reach 1231553 := rs (se 2 (by rfl) ⟨461832, by rfl⟩) R923665
theorem R346913 : Reach 346913 := rs (se 2 (by rfl) ⟨130092, by rfl⟩) R260185
theorem R314171 : Reach 314171 := rs (se 1 (by rfl) ⟨235628, by rfl⟩) R471257
theorem R281615 : Reach 281615 := rs (se 1 (by rfl) ⟨211211, by rfl⟩) R422423
theorem R117931 : Reach 117931 := rs (se 1 (by rfl) ⟨88448, by rfl⟩) R176897
theorem R314657 : Reach 314657 := rs (se 2 (by rfl) ⟨117996, by rfl⟩) R235993
theorem R151055 : Reach 151055 := rs (se 1 (by rfl) ⟨113291, by rfl⟩) R226583
theorem R282199 : Reach 282199 := rs (se 1 (by rfl) ⟨211649, by rfl⟩) R423299
theorem R740983 : Reach 740983 := rs (se 1 (by rfl) ⟨555737, by rfl⟩) R1111475
theorem R347885 : Reach 347885 := rs (se 3 (by rfl) ⟨65228, by rfl⟩) R130457
theorem R315251 : Reach 315251 := rs (se 1 (by rfl) ⟨236438, by rfl⟩) R472877
theorem R118903 : Reach 118903 := rs (se 1 (by rfl) ⟨89177, by rfl⟩) R178355
theorem R446867 : Reach 446867 := rs (se 1 (by rfl) ⟨335150, by rfl⟩) R670301
theorem R348569 : Reach 348569 := rs (se 2 (by rfl) ⟨130713, by rfl⟩) R261427
theorem R151993 : Reach 151993 := rs (se 2 (by rfl) ⟨56997, by rfl⟩) R113995
theorem R119227 : Reach 119227 := rs (se 1 (by rfl) ⟨89420, by rfl⟩) R178841
theorem R709073 : Reach 709073 := rs (se 2 (by rfl) ⟨265902, by rfl⟩) R531805
theorem R5198681 : Reach 5198681 := rs (se 2 (by rfl) ⟨1949505, by rfl⟩) R3899011
theorem R251147 : Reach 251147 := rs (se 1 (by rfl) ⟨188360, by rfl⟩) R376721
theorem R1365281 : Reach 1365281 := rs (se 2 (by rfl) ⟨511980, by rfl⟩) R1023961
theorem R349555 : Reach 349555 := rs (se 1 (by rfl) ⟨262166, by rfl⟩) R524333
theorem R120199 : Reach 120199 := rs (se 1 (by rfl) ⟨90149, by rfl⟩) R180299
theorem R1038095 : Reach 1038095 := rs (se 1 (by rfl) ⟨778571, by rfl⟩) R1557143
theorem R644915 : Reach 644915 := rs (se 1 (by rfl) ⟨483686, by rfl⟩) R967373
theorem R481139 : Reach 481139 := rs (se 1 (by rfl) ⟨360854, by rfl⟩) R721709
theorem R448541 : Reach 448541 := rs (se 3 (by rfl) ⟨84101, by rfl⟩) R168203
theorem R153785 : Reach 153785 := rs (se 2 (by rfl) ⟨57669, by rfl⟩) R115339
theorem R13031725 : Reach 13031725 := rs (se 3 (by rfl) ⟨2443448, by rfl⟩) R4886897
theorem R317843 : Reach 317843 := rs (se 1 (by rfl) ⟨238382, by rfl⟩) R476765
theorem R481879 : Reach 481879 := rs (se 1 (by rfl) ⟨361409, by rfl⟩) R722819
theorem R219763 : Reach 219763 := rs (se 1 (by rfl) ⟨164822, by rfl⟩) R329645
theorem R252715 : Reach 252715 := rs (se 1 (by rfl) ⟨189536, by rfl⟩) R379073
theorem R154487 : Reach 154487 := rs (se 1 (by rfl) ⟨115865, by rfl⟩) R231731
theorem R842885 : Reach 842885 := rs (se 4 (by rfl) ⟨79020, by rfl⟩) R158041
theorem R220427 : Reach 220427 := rs (se 1 (by rfl) ⟨165320, by rfl⟩) R330641
theorem R154939 : Reach 154939 := rs (se 1 (by rfl) ⟨116204, by rfl⟩) R232409
theorem R155081 : Reach 155081 := rs (se 2 (by rfl) ⟨58155, by rfl⟩) R116311
theorem R351773 : Reach 351773 := rs (se 3 (by rfl) ⟨65957, by rfl⟩) R131915
theorem R319247 : Reach 319247 := rs (se 1 (by rfl) ⟨239435, by rfl⟩) R478871
theorem R221195 : Reach 221195 := rs (se 1 (by rfl) ⟨165896, by rfl⟩) R331793
theorem R319517 : Reach 319517 := rs (se 3 (by rfl) ⟨59909, by rfl⟩) R119819
theorem R155783 : Reach 155783 := rs (se 1 (by rfl) ⟨116837, by rfl⟩) R233675
theorem R352457 : Reach 352457 := rs (se 2 (by rfl) ⟨132171, by rfl⟩) R264343
theorem R451001 : Reach 451001 := rs (se 2 (by rfl) ⟨169125, by rfl⟩) R338251
theorem R287347 : Reach 287347 := rs (se 1 (by rfl) ⟨215510, by rfl⟩) R431021
theorem R254611 : Reach 254611 := rs (se 1 (by rfl) ⟨190958, by rfl⟩) R381917
theorem R156431 : Reach 156431 := rs (se 1 (by rfl) ⟨117323, by rfl⟩) R234647
theorem R91143 : Reach 91143 := rs (se 1 (by rfl) ⟨68357, by rfl⟩) R136715
theorem R91151 : Reach 91151 := rs (se 1 (by rfl) ⟨68363, by rfl⟩) R136727
theorem R91195 : Reach 91195 := rs (se 1 (by rfl) ⟨68396, by rfl⟩) R136793
theorem R91271 : Reach 91271 := rs (se 1 (by rfl) ⟨68453, by rfl⟩) R136907
theorem R91279 : Reach 91279 := rs (se 1 (by rfl) ⟨68459, by rfl⟩) R136919
theorem R91323 : Reach 91323 := rs (se 1 (by rfl) ⟨68492, by rfl⟩) R136985
theorem R91399 : Reach 91399 := rs (se 1 (by rfl) ⟨68549, by rfl⟩) R137099
theorem R91407 : Reach 91407 := rs (se 1 (by rfl) ⟨68555, by rfl⟩) R137111
theorem R156971 : Reach 156971 := rs (se 1 (by rfl) ⟨117728, by rfl⟩) R235457
theorem R91451 : Reach 91451 := rs (se 1 (by rfl) ⟨68588, by rfl⟩) R137177
theorem R222551 : Reach 222551 := rs (se 1 (by rfl) ⟨166913, by rfl⟩) R333827
theorem R3433859 : Reach 3433859 := rs (se 1 (by rfl) ⟨2575394, by rfl⟩) R5150789
theorem R91527 : Reach 91527 := rs (se 1 (by rfl) ⟨68645, by rfl⟩) R137291
theorem R91535 : Reach 91535 := rs (se 1 (by rfl) ⟨68651, by rfl⟩) R137303
theorem R779665 : Reach 779665 := rs (se 2 (by rfl) ⟨292374, by rfl⟩) R584749
theorem R320921 : Reach 320921 := rs (se 2 (by rfl) ⟨120345, by rfl⟩) R240691
theorem R91579 : Reach 91579 := rs (se 1 (by rfl) ⟨68684, by rfl⟩) R137369
theorem R91655 : Reach 91655 := rs (se 1 (by rfl) ⟨68741, by rfl⟩) R137483
theorem R91663 : Reach 91663 := rs (se 1 (by rfl) ⟨68747, by rfl⟩) R137495
theorem R91707 : Reach 91707 := rs (se 1 (by rfl) ⟨68780, by rfl⟩) R137561
theorem R91783 : Reach 91783 := rs (se 1 (by rfl) ⟨68837, by rfl⟩) R137675
theorem R91791 : Reach 91791 := rs (se 1 (by rfl) ⟨68843, by rfl⟩) R137687
theorem R157369 : Reach 157369 := rs (se 2 (by rfl) ⟨59013, by rfl⟩) R118027
theorem R91835 : Reach 91835 := rs (se 1 (by rfl) ⟨68876, by rfl⟩) R137753
theorem R91911 : Reach 91911 := rs (se 1 (by rfl) ⟨68933, by rfl⟩) R137867
theorem R91919 : Reach 91919 := rs (se 1 (by rfl) ⟨68939, by rfl⟩) R137879
theorem R91963 : Reach 91963 := rs (se 1 (by rfl) ⟨68972, by rfl⟩) R137945
theorem R92039 : Reach 92039 := rs (se 1 (by rfl) ⟨69029, by rfl⟩) R138059
theorem R92047 : Reach 92047 := rs (se 1 (by rfl) ⟨69035, by rfl⟩) R138071
theorem R354233 : Reach 354233 := rs (se 2 (by rfl) ⟨132837, by rfl⟩) R265675
theorem R92091 : Reach 92091 := rs (se 1 (by rfl) ⟨69068, by rfl⟩) R138137
theorem R92167 : Reach 92167 := rs (se 1 (by rfl) ⟨69125, by rfl⟩) R138251
theorem R92175 : Reach 92175 := rs (se 1 (by rfl) ⟨69131, by rfl⟩) R138263
theorem R256033 : Reach 256033 := rs (se 2 (by rfl) ⟨96012, by rfl⟩) R192025
theorem R92219 : Reach 92219 := rs (se 1 (by rfl) ⟨69164, by rfl⟩) R138329
theorem R92295 : Reach 92295 := rs (se 1 (by rfl) ⟨69221, by rfl⟩) R138443
theorem R92303 : Reach 92303 := rs (se 1 (by rfl) ⟨69227, by rfl⟩) R138455
theorem R92347 : Reach 92347 := rs (se 1 (by rfl) ⟨69260, by rfl⟩) R138521
theorem R92423 : Reach 92423 := rs (se 1 (by rfl) ⟨69317, by rfl⟩) R138635
theorem R92431 : Reach 92431 := rs (se 1 (by rfl) ⟨69323, by rfl⟩) R138647
theorem R92475 : Reach 92475 := rs (se 1 (by rfl) ⟨69356, by rfl⟩) R138713
theorem R158071 : Reach 158071 := rs (se 1 (by rfl) ⟨118553, by rfl⟩) R237107
theorem R92551 : Reach 92551 := rs (se 1 (by rfl) ⟨69413, by rfl⟩) R138827
theorem R92559 : Reach 92559 := rs (se 1 (by rfl) ⟨69419, by rfl⟩) R138839
theorem R92603 : Reach 92603 := rs (se 1 (by rfl) ⟨69452, by rfl⟩) R138905
theorem R92679 : Reach 92679 := rs (se 1 (by rfl) ⟨69509, by rfl⟩) R139019
theorem R92687 : Reach 92687 := rs (se 1 (by rfl) ⟨69515, by rfl⟩) R139031
theorem R92731 : Reach 92731 := rs (se 1 (by rfl) ⟨69548, by rfl⟩) R139097
theorem R158267 : Reach 158267 := rs (se 1 (by rfl) ⟨118700, by rfl⟩) R237401
theorem R92807 : Reach 92807 := rs (se 1 (by rfl) ⟨69605, by rfl⟩) R139211
theorem R92815 : Reach 92815 := rs (se 1 (by rfl) ⟨69611, by rfl⟩) R139223
theorem R92859 : Reach 92859 := rs (se 1 (by rfl) ⟨69644, by rfl⟩) R139289
theorem R92935 : Reach 92935 := rs (se 1 (by rfl) ⟨69701, by rfl⟩) R139403
theorem R92943 : Reach 92943 := rs (se 1 (by rfl) ⟨69707, by rfl⟩) R139415
theorem R256801 : Reach 256801 := rs (se 2 (by rfl) ⟨96300, by rfl⟩) R192601
theorem R1076003 : Reach 1076003 := rs (se 1 (by rfl) ⟨807002, by rfl⟩) R1614005
theorem R92987 : Reach 92987 := rs (se 1 (by rfl) ⟨69740, by rfl⟩) R139481
theorem R486233 : Reach 486233 := rs (se 2 (by rfl) ⟨182337, by rfl⟩) R364675
theorem R93063 : Reach 93063 := rs (se 1 (by rfl) ⟨69797, by rfl⟩) R139595
theorem R93071 : Reach 93071 := rs (se 1 (by rfl) ⟨69803, by rfl⟩) R139607
theorem R93115 : Reach 93115 := rs (se 1 (by rfl) ⟨69836, by rfl⟩) R139673
theorem R158665 : Reach 158665 := rs (se 2 (by rfl) ⟨59499, by rfl⟩) R118999
theorem R93191 : Reach 93191 := rs (se 1 (by rfl) ⟨69893, by rfl⟩) R139787
theorem R93199 : Reach 93199 := rs (se 1 (by rfl) ⟨69899, by rfl⟩) R139799
theorem R224299 : Reach 224299 := rs (se 1 (by rfl) ⟨168224, by rfl⟩) R336449
theorem R93243 : Reach 93243 := rs (se 1 (by rfl) ⟨69932, by rfl⟩) R139865
theorem R93319 : Reach 93319 := rs (se 1 (by rfl) ⟨69989, by rfl⟩) R139979
theorem R93327 : Reach 93327 := rs (se 1 (by rfl) ⟨69995, by rfl⟩) R139991
theorem R93371 : Reach 93371 := rs (se 1 (by rfl) ⟨70028, by rfl⟩) R140057
theorem R93447 : Reach 93447 := rs (se 1 (by rfl) ⟨70085, by rfl⟩) R140171
theorem R93455 : Reach 93455 := rs (se 1 (by rfl) ⟨70091, by rfl⟩) R140183
theorem R93499 : Reach 93499 := rs (se 1 (by rfl) ⟨70124, by rfl⟩) R140249
theorem R93575 : Reach 93575 := rs (se 1 (by rfl) ⟨70181, by rfl⟩) R140363
theorem R93583 : Reach 93583 := rs (se 1 (by rfl) ⟨70187, by rfl⟩) R140375
theorem R93627 : Reach 93627 := rs (se 1 (by rfl) ⟨70220, by rfl⟩) R140441
theorem R93703 : Reach 93703 := rs (se 1 (by rfl) ⟨70277, by rfl⟩) R140555
theorem R93711 : Reach 93711 := rs (se 1 (by rfl) ⟨70283, by rfl⟩) R140567
theorem R93755 : Reach 93755 := rs (se 1 (by rfl) ⟨70316, by rfl⟩) R140633
theorem R93831 : Reach 93831 := rs (se 1 (by rfl) ⟨70373, by rfl⟩) R140747
theorem R159367 : Reach 159367 := rs (se 1 (by rfl) ⟨119525, by rfl⟩) R239051
theorem R93839 : Reach 93839 := rs (se 1 (by rfl) ⟨70379, by rfl⟩) R140759
theorem R93883 : Reach 93883 := rs (se 1 (by rfl) ⟨70412, by rfl⟩) R140825
theorem R93959 : Reach 93959 := rs (se 1 (by rfl) ⟨70469, by rfl⟩) R140939
theorem R93967 : Reach 93967 := rs (se 1 (by rfl) ⟨70475, by rfl⟩) R140951
theorem R94011 : Reach 94011 := rs (se 1 (by rfl) ⟨70508, by rfl⟩) R141017
theorem R94087 : Reach 94087 := rs (se 1 (by rfl) ⟨70565, by rfl⟩) R141131
theorem R94095 : Reach 94095 := rs (se 1 (by rfl) ⟨70571, by rfl⟩) R141143
theorem R94139 : Reach 94139 := rs (se 1 (by rfl) ⟨70604, by rfl⟩) R141209
theorem R421841 : Reach 421841 := rs (se 2 (by rfl) ⟨158190, by rfl⟩) R316381
theorem R94215 : Reach 94215 := rs (se 1 (by rfl) ⟨70661, by rfl⟩) R141323
theorem R94223 : Reach 94223 := rs (se 1 (by rfl) ⟨70667, by rfl⟩) R141335
theorem R585751 : Reach 585751 := rs (se 1 (by rfl) ⟨439313, by rfl⟩) R878627
theorem R94267 : Reach 94267 := rs (se 1 (by rfl) ⟨70700, by rfl⟩) R141401
theorem R389207 : Reach 389207 := rs (se 1 (by rfl) ⟨291905, by rfl⟩) R583811
theorem R225395 : Reach 225395 := rs (se 1 (by rfl) ⟨169046, by rfl⟩) R338093
theorem R94343 : Reach 94343 := rs (se 1 (by rfl) ⟨70757, by rfl⟩) R141515
theorem R94351 : Reach 94351 := rs (se 1 (by rfl) ⟨70763, by rfl⟩) R141527
theorem R94395 : Reach 94395 := rs (se 1 (by rfl) ⟨70796, by rfl⟩) R141593
theorem R94471 : Reach 94471 := rs (se 1 (by rfl) ⟨70853, by rfl⟩) R141707
theorem R94479 : Reach 94479 := rs (se 1 (by rfl) ⟨70859, by rfl⟩) R141719
theorem R160015 : Reach 160015 := rs (se 1 (by rfl) ⟨120011, by rfl⟩) R240023
theorem R291131 : Reach 291131 := rs (se 1 (by rfl) ⟨218348, by rfl⟩) R436697
theorem R94523 : Reach 94523 := rs (se 1 (by rfl) ⟨70892, by rfl⟩) R141785
theorem R94599 : Reach 94599 := rs (se 1 (by rfl) ⟨70949, by rfl⟩) R141899
theorem R94607 : Reach 94607 := rs (se 1 (by rfl) ⟨70955, by rfl⟩) R141911
theorem R455057 : Reach 455057 := rs (se 2 (by rfl) ⟨170646, by rfl⟩) R341293
theorem R225683 : Reach 225683 := rs (se 1 (by rfl) ⟨169262, by rfl⟩) R338525
theorem R94651 : Reach 94651 := rs (se 1 (by rfl) ⟨70988, by rfl⟩) R141977
theorem R94727 : Reach 94727 := rs (se 1 (by rfl) ⟨71045, by rfl⟩) R142091
theorem R94735 : Reach 94735 := rs (se 1 (by rfl) ⟨71051, by rfl⟩) R142103
theorem R94779 : Reach 94779 := rs (se 1 (by rfl) ⟨71084, by rfl⟩) R142169
theorem R94855 : Reach 94855 := rs (se 1 (by rfl) ⟨71141, by rfl⟩) R142283
theorem R94863 : Reach 94863 := rs (se 1 (by rfl) ⟨71147, by rfl⟩) R142295
theorem R94907 : Reach 94907 := rs (se 1 (by rfl) ⟨71180, by rfl⟩) R142361
theorem R94983 : Reach 94983 := rs (se 1 (by rfl) ⟨71237, by rfl⟩) R142475
theorem R94991 : Reach 94991 := rs (se 1 (by rfl) ⟨71243, by rfl⟩) R142487
theorem R95035 : Reach 95035 := rs (se 1 (by rfl) ⟨71276, by rfl⟩) R142553
theorem R95111 : Reach 95111 := rs (se 1 (by rfl) ⟨71333, by rfl⟩) R142667
theorem R95119 : Reach 95119 := rs (se 1 (by rfl) ⟨71339, by rfl⟩) R142679
theorem R226201 : Reach 226201 := rs (se 2 (by rfl) ⟨84825, by rfl⟩) R169651
theorem R226423 : Reach 226423 := rs (se 1 (by rfl) ⟨169817, by rfl⟩) R339635
theorem R521417 : Reach 521417 := rs (se 2 (by rfl) ⟨195531, by rfl⟩) R391063
theorem R128299 : Reach 128299 := rs (se 1 (by rfl) ⟨96224, by rfl⟩) R192449
theorem R357817 : Reach 357817 := rs (se 2 (by rfl) ⟨134181, by rfl⟩) R268363
theorem R226817 : Reach 226817 := rs (se 2 (by rfl) ⟨85056, by rfl⟩) R170113
theorem R882353 : Reach 882353 := rs (se 2 (by rfl) ⟨330882, by rfl⟩) R661765
theorem R358145 : Reach 358145 := rs (se 2 (by rfl) ⟨134304, by rfl⟩) R268609
theorem R227087 : Reach 227087 := rs (se 1 (by rfl) ⟨170315, by rfl⟩) R340631
theorem R13694993 : Reach 13694993 := rs (se 2 (by rfl) ⟨5135622, by rfl⟩) R10271245
theorem R260243 : Reach 260243 := rs (se 1 (by rfl) ⟨195182, by rfl⟩) R390365
theorem R391405 : Reach 391405 := rs (se 3 (by rfl) ⟨73388, by rfl⟩) R146777
theorem R1046843 : Reach 1046843 := rs (se 1 (by rfl) ⟨785132, by rfl⟩) R1570265
theorem R227731 : Reach 227731 := rs (se 1 (by rfl) ⟨170798, by rfl⟩) R341597
theorem R2980313 : Reach 2980313 := rs (se 2 (by rfl) ⟨1117617, by rfl⟩) R2235235
theorem R227855 : Reach 227855 := rs (se 1 (by rfl) ⟨170891, by rfl⟩) R341783
theorem R588545 : Reach 588545 := rs (se 2 (by rfl) ⟨220704, by rfl⟩) R441409
theorem R555835 : Reach 555835 := rs (se 1 (by rfl) ⟨416876, by rfl⟩) R833753
theorem R129865 : Reach 129865 := rs (se 2 (by rfl) ⟨48699, by rfl⟩) R97399
theorem R195463 : Reach 195463 := rs (se 1 (by rfl) ⟨146597, by rfl⟩) R293195
theorem R523331 : Reach 523331 := rs (se 1 (by rfl) ⟨392498, by rfl⟩) R784997
theorem R425197 : Reach 425197 := rs (se 3 (by rfl) ⟨79724, by rfl⟩) R159449
theorem R130423 : Reach 130423 := rs (se 1 (by rfl) ⟨97817, by rfl⟩) R195635
theorem R195959 : Reach 195959 := rs (se 1 (by rfl) ⟨146969, by rfl⟩) R293939
theorem R261643 : Reach 261643 := rs (se 1 (by rfl) ⟨196232, by rfl⟩) R392465
theorem R261917 : Reach 261917 := rs (se 3 (by rfl) ⟨49109, by rfl⟩) R98219
theorem R393113 : Reach 393113 := rs (se 2 (by rfl) ⟨147417, by rfl⟩) R294835
theorem R130987 : Reach 130987 := rs (se 1 (by rfl) ⟨98240, by rfl⟩) R196481
theorem R589853 : Reach 589853 := rs (se 3 (by rfl) ⟨110597, by rfl⟩) R221195
theorem R459245 : Reach 459245 := rs (se 3 (by rfl) ⟨86108, by rfl⟩) R172217
theorem R2228795 : Reach 2228795 := rs (se 1 (by rfl) ⟨1671596, by rfl⟩) R3343193
theorem R2130583 : Reach 2130583 := rs (se 1 (by rfl) ⟨1597937, by rfl⟩) R3195875
theorem R197711 : Reach 197711 := rs (se 1 (by rfl) ⟨148283, by rfl⟩) R296567
theorem R132457 : Reach 132457 := rs (se 2 (by rfl) ⟨49671, by rfl⟩) R99343
theorem R394739 : Reach 394739 := rs (se 1 (by rfl) ⟨296054, by rfl⟩) R592109
theorem R230921 : Reach 230921 := rs (se 2 (by rfl) ⟨86595, by rfl⟩) R173191
theorem R230951 : Reach 230951 := rs (se 1 (by rfl) ⟨173213, by rfl⟩) R346427
theorem R821035 : Reach 821035 := rs (se 1 (by rfl) ⟨615776, by rfl⟩) R1231553
theorem R231275 : Reach 231275 := rs (se 1 (by rfl) ⟨173456, by rfl⟩) R346913
theorem R100703 : Reach 100703 := rs (se 1 (by rfl) ⟨75527, by rfl⟩) R151055
theorem R231923 : Reach 231923 := rs (se 1 (by rfl) ⟨173942, by rfl⟩) R347885
theorem R592595 : Reach 592595 := rs (se 1 (by rfl) ⟨444446, by rfl⟩) R888893
theorem R297911 : Reach 297911 := rs (se 1 (by rfl) ⟨223433, by rfl⟩) R446867
theorem R232379 : Reach 232379 := rs (se 1 (by rfl) ⟨174284, by rfl⟩) R348569
theorem R167431 : Reach 167431 := rs (se 1 (by rfl) ⟨125573, by rfl⟩) R251147
theorem R396839 : Reach 396839 := rs (se 1 (by rfl) ⟨297629, by rfl⟩) R595259
theorem R233057 : Reach 233057 := rs (se 2 (by rfl) ⟨87396, by rfl⟩) R174793
theorem R692063 : Reach 692063 := rs (se 1 (by rfl) ⟨519047, by rfl⟩) R1038095
theorem R429943 : Reach 429943 := rs (se 1 (by rfl) ⟨322457, by rfl⟩) R644915
theorem R299027 : Reach 299027 := rs (se 1 (by rfl) ⟨224270, by rfl⟩) R448541
theorem R299065 : Reach 299065 := rs (se 2 (by rfl) ⟨112149, by rfl⟩) R224299
theorem R102523 : Reach 102523 := rs (se 1 (by rfl) ⟨76892, by rfl⟩) R153785
theorem R102991 : Reach 102991 := rs (se 1 (by rfl) ⟨77243, by rfl⟩) R154487
theorem R266951 : Reach 266951 := rs (se 1 (by rfl) ⟨200213, by rfl⟩) R400427
theorem R561923 : Reach 561923 := rs (se 1 (by rfl) ⟨421442, by rfl⟩) R842885
theorem R987977 : Reach 987977 := rs (se 2 (by rfl) ⟨370491, by rfl⟩) R740983
theorem R103387 : Reach 103387 := rs (se 1 (by rfl) ⟨77540, by rfl⟩) R155081
theorem R234515 : Reach 234515 := rs (se 1 (by rfl) ⟨175886, by rfl⟩) R351773
theorem R103855 : Reach 103855 := rs (se 1 (by rfl) ⟨77891, by rfl⟩) R155783
theorem R234971 : Reach 234971 := rs (se 1 (by rfl) ⟨176228, by rfl⟩) R352457
theorem R300667 : Reach 300667 := rs (se 1 (by rfl) ⟨225500, by rfl⟩) R451001
theorem R104287 : Reach 104287 := rs (se 1 (by rfl) ⟨78215, by rfl⟩) R156431
theorem R202657 : Reach 202657 := rs (se 2 (by rfl) ⟨75996, by rfl⟩) R151993
theorem R137135 : Reach 137135 := rs (se 1 (by rfl) ⟨102851, by rfl⟩) R205703
theorem R137225 : Reach 137225 := rs (se 2 (by rfl) ⟨51459, by rfl⟩) R102919
theorem R137255 : Reach 137255 := rs (se 1 (by rfl) ⟨102941, by rfl⟩) R205883
theorem R137339 : Reach 137339 := rs (se 1 (by rfl) ⟨103004, by rfl⟩) R206009
theorem R104647 : Reach 104647 := rs (se 1 (by rfl) ⟨78485, by rfl⟩) R156971
theorem R268535 : Reach 268535 := rs (se 1 (by rfl) ⟨201401, by rfl⟩) R402803
theorem R202999 : Reach 202999 := rs (se 1 (by rfl) ⟨152249, by rfl⟩) R304499
theorem R137465 : Reach 137465 := rs (se 2 (by rfl) ⟨51549, by rfl⟩) R103099
theorem R137567 : Reach 137567 := rs (se 1 (by rfl) ⟨103175, by rfl⟩) R206351
theorem R137579 : Reach 137579 := rs (se 1 (by rfl) ⟨103184, by rfl⟩) R206369
theorem R301601 : Reach 301601 := rs (se 2 (by rfl) ⟨113100, by rfl⟩) R226201
theorem R137807 : Reach 137807 := rs (se 1 (by rfl) ⟨103355, by rfl⟩) R206711
theorem R236155 : Reach 236155 := rs (se 1 (by rfl) ⟨177116, by rfl⟩) R354233
theorem R137927 : Reach 137927 := rs (se 1 (by rfl) ⟨103445, by rfl⟩) R206891
theorem R301897 : Reach 301897 := rs (se 2 (by rfl) ⟨113211, by rfl⟩) R226423
theorem R138089 : Reach 138089 := rs (se 2 (by rfl) ⟨51783, by rfl⟩) R103567
theorem R138167 : Reach 138167 := rs (se 1 (by rfl) ⟨103625, by rfl⟩) R207251
theorem R138203 : Reach 138203 := rs (se 1 (by rfl) ⟨103652, by rfl⟩) R207305
theorem R105511 : Reach 105511 := rs (se 1 (by rfl) ⟨79133, by rfl⟩) R158267
theorem R171065 : Reach 171065 := rs (se 2 (by rfl) ⟨64149, by rfl⟩) R128299
theorem R597071 : Reach 597071 := rs (se 1 (by rfl) ⟨447803, by rfl⟩) R895607
theorem R466073 : Reach 466073 := rs (se 2 (by rfl) ⟨174777, by rfl⟩) R349555
theorem R138671 : Reach 138671 := rs (se 1 (by rfl) ⟨104003, by rfl⟩) R208007
theorem R138761 : Reach 138761 := rs (se 2 (by rfl) ⟨52035, by rfl⟩) R104071
theorem R138791 : Reach 138791 := rs (se 1 (by rfl) ⟨104093, by rfl⟩) R208187
theorem R138875 : Reach 138875 := rs (se 1 (by rfl) ⟨104156, by rfl⟩) R208313
theorem R597719 : Reach 597719 := rs (se 1 (by rfl) ⟨448289, by rfl⟩) R896579
theorem R401111 : Reach 401111 := rs (se 1 (by rfl) ⟨300833, by rfl⟩) R601667
theorem R139001 : Reach 139001 := rs (se 2 (by rfl) ⟨52125, by rfl⟩) R104251
theorem R139103 : Reach 139103 := rs (se 1 (by rfl) ⟨104327, by rfl⟩) R208655
theorem R270175 : Reach 270175 := rs (se 1 (by rfl) ⟨202631, by rfl⟩) R405263
theorem R139115 : Reach 139115 := rs (se 1 (by rfl) ⟨104336, by rfl⟩) R208673
theorem R139343 : Reach 139343 := rs (se 1 (by rfl) ⟨104507, by rfl⟩) R209015
theorem R139463 : Reach 139463 := rs (se 1 (by rfl) ⟨104597, by rfl⟩) R209195
theorem R303371 : Reach 303371 := rs (se 1 (by rfl) ⟨227528, by rfl⟩) R455057
theorem R303421 : Reach 303421 := rs (se 3 (by rfl) ⟨56891, by rfl⟩) R113783
theorem R139625 : Reach 139625 := rs (se 2 (by rfl) ⟨52359, by rfl⟩) R104719
theorem R205199 : Reach 205199 := rs (se 1 (by rfl) ⟨153899, by rfl⟩) R307799
theorem R17375633 : Reach 17375633 := rs (se 2 (by rfl) ⟨6515862, by rfl⟩) R13031725
theorem R139703 : Reach 139703 := rs (se 1 (by rfl) ⟨104777, by rfl⟩) R209555
theorem R139739 : Reach 139739 := rs (se 1 (by rfl) ⟨104804, by rfl⟩) R209609
theorem R303641 : Reach 303641 := rs (se 2 (by rfl) ⟨113865, by rfl⟩) R227731
theorem R205523 : Reach 205523 := rs (se 1 (by rfl) ⟨154142, by rfl⟩) R308285
theorem R336683 : Reach 336683 := rs (se 1 (by rfl) ⟨252512, by rfl⟩) R505025
theorem R467819 : Reach 467819 := rs (se 1 (by rfl) ⟨350864, by rfl⟩) R701729
theorem R140207 : Reach 140207 := rs (se 1 (by rfl) ⟨105155, by rfl⟩) R210311
theorem R140297 : Reach 140297 := rs (se 2 (by rfl) ⟨52611, by rfl⟩) R105223
theorem R140327 : Reach 140327 := rs (se 1 (by rfl) ⟨105245, by rfl⟩) R210491
theorem R2401325 : Reach 2401325 := rs (se 3 (by rfl) ⟨450248, by rfl⟩) R900497
theorem R336953 : Reach 336953 := rs (se 2 (by rfl) ⟨126357, by rfl⟩) R252715
theorem R173153 : Reach 173153 := rs (se 2 (by rfl) ⟨64932, by rfl⟩) R129865
theorem R140411 : Reach 140411 := rs (se 1 (by rfl) ⟨105308, by rfl⟩) R210617
theorem R238763 : Reach 238763 := rs (se 1 (by rfl) ⟨179072, by rfl⟩) R358145
theorem R140537 : Reach 140537 := rs (se 2 (by rfl) ⟨52701, by rfl⟩) R105403
theorem R140639 : Reach 140639 := rs (se 1 (by rfl) ⟨105479, by rfl⟩) R210959
theorem R140651 : Reach 140651 := rs (se 1 (by rfl) ⟨105488, by rfl⟩) R210977
theorem R173495 : Reach 173495 := rs (se 1 (by rfl) ⟨130121, by rfl⟩) R260243
theorem R697895 : Reach 697895 := rs (se 1 (by rfl) ⟨523421, by rfl⟩) R1046843
theorem R140879 : Reach 140879 := rs (se 1 (by rfl) ⟨105659, by rfl⟩) R211319
theorem R370273 : Reach 370273 := rs (se 2 (by rfl) ⟨138852, by rfl⟩) R277705
theorem R206459 : Reach 206459 := rs (se 1 (by rfl) ⟨154844, by rfl⟩) R309689
theorem R566929 : Reach 566929 := rs (se 2 (by rfl) ⟨212598, by rfl⟩) R425197
theorem R140999 : Reach 140999 := rs (se 1 (by rfl) ⟨105749, by rfl⟩) R211499
theorem R206585 : Reach 206585 := rs (se 2 (by rfl) ⟨77469, by rfl⟩) R154939
theorem R501497 : Reach 501497 := rs (se 2 (by rfl) ⟨188061, by rfl⟩) R376123
theorem R173897 : Reach 173897 := rs (se 2 (by rfl) ⟨65211, by rfl⟩) R130423
theorem R141161 : Reach 141161 := rs (se 2 (by rfl) ⟨52935, by rfl⟩) R105871
theorem R141239 : Reach 141239 := rs (se 1 (by rfl) ⟨105929, by rfl⟩) R211859
theorem R141275 : Reach 141275 := rs (se 1 (by rfl) ⟨105956, by rfl⟩) R211913
theorem R206855 : Reach 206855 := rs (se 1 (by rfl) ⟨155141, by rfl⟩) R310283
theorem R2664485 : Reach 2664485 := rs (se 4 (by rfl) ⟨249795, by rfl⟩) R499591
theorem R206927 : Reach 206927 := rs (se 1 (by rfl) ⟨155195, by rfl⟩) R310391
theorem R141743 : Reach 141743 := rs (se 1 (by rfl) ⟨106307, by rfl⟩) R212615
theorem R207323 : Reach 207323 := rs (se 1 (by rfl) ⟨155492, by rfl⟩) R310985
theorem R141833 : Reach 141833 := rs (se 2 (by rfl) ⟨53187, by rfl⟩) R106375
theorem R174611 : Reach 174611 := rs (se 1 (by rfl) ⟨130958, by rfl⟩) R261917
theorem R141863 : Reach 141863 := rs (se 1 (by rfl) ⟨106397, by rfl⟩) R212795
theorem R174649 : Reach 174649 := rs (se 2 (by rfl) ⟨65493, by rfl⟩) R130987
theorem R338555 : Reach 338555 := rs (se 1 (by rfl) ⟨253916, by rfl⟩) R507833
theorem R141947 : Reach 141947 := rs (se 1 (by rfl) ⟨106460, by rfl⟩) R212921
theorem R142073 : Reach 142073 := rs (se 2 (by rfl) ⟨53277, by rfl⟩) R106555
theorem R142175 : Reach 142175 := rs (se 1 (by rfl) ⟨106631, by rfl⟩) R213263
theorem R240479 : Reach 240479 := rs (se 1 (by rfl) ⟨180359, by rfl⟩) R360719
theorem R174953 : Reach 174953 := rs (se 2 (by rfl) ⟨65607, by rfl⟩) R131215
theorem R142187 : Reach 142187 := rs (se 1 (by rfl) ⟨106640, by rfl⟩) R213281
theorem R11447203 : Reach 11447203 := rs (se 1 (by rfl) ⟨8585402, by rfl⟩) R17170805
theorem R207791 : Reach 207791 := rs (se 1 (by rfl) ⟨155843, by rfl⟩) R311687
theorem R142415 : Reach 142415 := rs (se 1 (by rfl) ⟨106811, by rfl⟩) R213623
theorem R208043 : Reach 208043 := rs (se 1 (by rfl) ⟨156032, by rfl⟩) R312065
theorem R142535 : Reach 142535 := rs (se 1 (by rfl) ⟨106901, by rfl⟩) R213803
theorem R1191185 : Reach 1191185 := rs (se 2 (by rfl) ⟨446694, by rfl⟩) R893389
theorem R896345 : Reach 896345 := rs (se 2 (by rfl) ⟨336129, by rfl⟩) R672259
theorem R339481 : Reach 339481 := rs (se 2 (by rfl) ⟨127305, by rfl⟩) R254611
theorem R208583 : Reach 208583 := rs (se 1 (by rfl) ⟨156437, by rfl⟩) R312875
theorem R798497 : Reach 798497 := rs (se 2 (by rfl) ⟨299436, by rfl⟩) R598873
theorem R1421243 : Reach 1421243 := rs (se 1 (by rfl) ⟨1065932, by rfl⟩) R2131865
theorem R1028027 : Reach 1028027 := rs (se 1 (by rfl) ⟨771020, by rfl⟩) R1542041
theorem R176251 : Reach 176251 := rs (se 1 (by rfl) ⟨132188, by rfl⟩) R264377
theorem R340139 : Reach 340139 := rs (se 1 (by rfl) ⟨255104, by rfl⟩) R510209
theorem R176327 : Reach 176327 := rs (se 1 (by rfl) ⟨132245, by rfl⟩) R264491
theorem R307745 : Reach 307745 := rs (se 2 (by rfl) ⟨115404, by rfl⟩) R230809
theorem R209447 : Reach 209447 := rs (se 1 (by rfl) ⟨157085, by rfl⟩) R314171
theorem R176737 : Reach 176737 := rs (se 2 (by rfl) ⟨66276, by rfl⟩) R132553
theorem R242315 : Reach 242315 := rs (se 1 (by rfl) ⟨181736, by rfl⟩) R363473
theorem R307961 : Reach 307961 := rs (se 2 (by rfl) ⟨115485, by rfl⟩) R230971
theorem R111467 : Reach 111467 := rs (se 1 (by rfl) ⟨83600, by rfl⟩) R167201
theorem R209771 : Reach 209771 := rs (se 1 (by rfl) ⟨157328, by rfl⟩) R314657
theorem R209825 : Reach 209825 := rs (se 2 (by rfl) ⟨78684, by rfl⟩) R157369
theorem R177079 : Reach 177079 := rs (se 1 (by rfl) ⟨132809, by rfl⟩) R265619
theorem R308231 : Reach 308231 := rs (se 1 (by rfl) ⟨231173, by rfl⟩) R462347
theorem R308339 : Reach 308339 := rs (se 1 (by rfl) ⟨231254, by rfl⟩) R462509
theorem R210167 : Reach 210167 := rs (se 1 (by rfl) ⟨157625, by rfl⟩) R315251
theorem R177481 : Reach 177481 := rs (se 2 (by rfl) ⟨66555, by rfl⟩) R133111
theorem R308609 : Reach 308609 := rs (se 2 (by rfl) ⟨115728, by rfl⟩) R231457
theorem R341377 : Reach 341377 := rs (se 2 (by rfl) ⟨128016, by rfl⟩) R256033
theorem R472715 : Reach 472715 := rs (se 1 (by rfl) ⟨354536, by rfl⟩) R709073
theorem R964243 : Reach 964243 := rs (se 1 (by rfl) ⟨723182, by rfl⟩) R1446365
theorem R210761 : Reach 210761 := rs (se 2 (by rfl) ⟨79035, by rfl⟩) R158071
theorem R178195 : Reach 178195 := rs (se 1 (by rfl) ⟨133646, by rfl⟩) R267293
theorem R309419 : Reach 309419 := rs (se 1 (by rfl) ⟨232064, by rfl⟩) R464129
theorem R178537 : Reach 178537 := rs (se 2 (by rfl) ⟨66951, by rfl⟩) R133903
theorem R342401 : Reach 342401 := rs (se 2 (by rfl) ⟨128400, by rfl⟩) R256801
theorem R211553 : Reach 211553 := rs (se 2 (by rfl) ⟨79332, by rfl⟩) R158665
theorem R309959 : Reach 309959 := rs (se 1 (by rfl) ⟨232469, by rfl⟩) R464939
theorem R211895 : Reach 211895 := rs (se 1 (by rfl) ⟨158921, by rfl⟩) R317843
theorem R539621 : Reach 539621 := rs (se 4 (by rfl) ⟨50589, by rfl⟩) R101179
theorem R376265 : Reach 376265 := rs (se 2 (by rfl) ⟨141099, by rfl⟩) R282199
theorem R114139 : Reach 114139 := rs (se 1 (by rfl) ⟨85604, by rfl⟩) R171209
theorem R146951 : Reach 146951 := rs (se 1 (by rfl) ⟨110213, by rfl⟩) R220427
theorem R212489 : Reach 212489 := rs (se 2 (by rfl) ⟨79683, by rfl⟩) R159367
theorem R310823 : Reach 310823 := rs (se 1 (by rfl) ⟨233117, by rfl⟩) R466235
theorem R310931 : Reach 310931 := rs (se 1 (by rfl) ⟨233198, by rfl⟩) R466397
theorem R802493 : Reach 802493 := rs (se 3 (by rfl) ⟨150467, by rfl⟩) R300935
theorem R179911 : Reach 179911 := rs (se 1 (by rfl) ⟨134933, by rfl⟩) R269867
theorem R212831 : Reach 212831 := rs (se 1 (by rfl) ⟨159623, by rfl⟩) R319247
theorem R311147 : Reach 311147 := rs (se 1 (by rfl) ⟨233360, by rfl⟩) R466721
theorem R311201 : Reach 311201 := rs (se 2 (by rfl) ⟨116700, by rfl⟩) R233401
theorem R213011 : Reach 213011 := rs (se 1 (by rfl) ⟨159758, by rfl⟩) R319517
theorem R180473 : Reach 180473 := rs (se 2 (by rfl) ⟨67677, by rfl⟩) R135355
theorem R213353 : Reach 213353 := rs (se 2 (by rfl) ⟨80007, by rfl⟩) R160015
theorem R311795 : Reach 311795 := rs (se 1 (by rfl) ⟨233846, by rfl⟩) R467693
theorem R148367 : Reach 148367 := rs (se 1 (by rfl) ⟨111275, by rfl⟩) R222551
theorem R213947 : Reach 213947 := rs (se 1 (by rfl) ⟨160460, by rfl⟩) R320921
theorem R312335 : Reach 312335 := rs (se 1 (by rfl) ⟨234251, by rfl⟩) R468503
theorem R181723 : Reach 181723 := rs (se 1 (by rfl) ⟨136292, by rfl⟩) R272585
theorem R312929 : Reach 312929 := rs (se 2 (by rfl) ⟨117348, by rfl⟩) R234697
theorem R477089 : Reach 477089 := rs (se 2 (by rfl) ⟨178908, by rfl⟩) R357817
theorem R182521 : Reach 182521 := rs (se 2 (by rfl) ⟨68445, by rfl⟩) R136891
theorem R281227 : Reach 281227 := rs (se 1 (by rfl) ⟨210920, by rfl⟩) R421841
theorem R150263 : Reach 150263 := rs (se 1 (by rfl) ⟨112697, by rfl⟩) R225395
theorem R150455 : Reach 150455 := rs (se 1 (by rfl) ⟨112841, by rfl⟩) R225683
theorem R379835 : Reach 379835 := rs (se 1 (by rfl) ⟨284876, by rfl⟩) R569753
theorem R314387 : Reach 314387 := rs (se 1 (by rfl) ⟨235790, by rfl⟩) R471581
theorem R314711 : Reach 314711 := rs (se 1 (by rfl) ⟨236033, by rfl⟩) R472067
theorem R970157 : Reach 970157 := rs (se 3 (by rfl) ⟨181904, by rfl⟩) R363809
theorem R118199 : Reach 118199 := rs (se 1 (by rfl) ⟨88649, by rfl⟩) R177299
theorem R642505 : Reach 642505 := rs (se 2 (by rfl) ⟨240939, by rfl⟩) R481879
theorem R347611 : Reach 347611 := rs (se 1 (by rfl) ⟨260708, by rfl⟩) R521417
theorem R118351 : Reach 118351 := rs (se 1 (by rfl) ⟨88763, by rfl⟩) R177527
theorem R151211 : Reach 151211 := rs (se 1 (by rfl) ⟨113408, by rfl⟩) R226817
theorem R741113 : Reach 741113 := rs (se 2 (by rfl) ⟨277917, by rfl⟩) R555835
theorem R446251 : Reach 446251 := rs (se 1 (by rfl) ⟨334688, by rfl⟩) R669377
theorem R151391 : Reach 151391 := rs (se 1 (by rfl) ⟨113543, by rfl⟩) R227087
theorem R577489 : Reach 577489 := rs (se 2 (by rfl) ⟨216558, by rfl⟩) R433117
theorem R9129995 : Reach 9129995 := rs (se 1 (by rfl) ⟨6847496, by rfl⟩) R13694993
theorem R1986875 : Reach 1986875 := rs (se 1 (by rfl) ⟨1490156, by rfl⟩) R2980313
theorem R151903 : Reach 151903 := rs (se 1 (by rfl) ⟨113927, by rfl⟩) R227855
theorem R315791 : Reach 315791 := rs (se 1 (by rfl) ⟨236843, by rfl⟩) R473687
theorem R348857 : Reach 348857 := rs (se 2 (by rfl) ⟨130821, by rfl⟩) R261643
theorem R119495 : Reach 119495 := rs (se 1 (by rfl) ⟨89621, by rfl⟩) R179243
theorem R971473 : Reach 971473 := rs (se 2 (by rfl) ⟨364302, by rfl⟩) R728605
theorem R316115 : Reach 316115 := rs (se 1 (by rfl) ⟨237086, by rfl⟩) R474173
theorem R348887 : Reach 348887 := rs (se 1 (by rfl) ⟨261665, by rfl⟩) R523331
theorem R119647 : Reach 119647 := rs (se 1 (by rfl) ⟨89735, by rfl⟩) R179471
theorem R578411 : Reach 578411 := rs (se 1 (by rfl) ⟨433808, by rfl⟩) R867617
theorem R709559 : Reach 709559 := rs (se 1 (by rfl) ⟨532169, by rfl⟩) R1064339
theorem R2348837 : Reach 2348837 := rs (se 4 (by rfl) ⟨220203, by rfl⟩) R440407
theorem R317303 : Reach 317303 := rs (se 1 (by rfl) ⟨237977, by rfl⟩) R475955
theorem R710693 : Reach 710693 := rs (se 4 (by rfl) ⟨66627, by rfl⟩) R133255
theorem R317519 : Reach 317519 := rs (se 1 (by rfl) ⟨238139, by rfl⟩) R476279
theorem R383129 : Reach 383129 := rs (se 2 (by rfl) ⟨143673, by rfl⟩) R287347
theorem R711017 : Reach 711017 := rs (se 2 (by rfl) ⟨266631, by rfl⟩) R533263
theorem R317897 : Reach 317897 := rs (se 2 (by rfl) ⟨119211, by rfl⟩) R238423
theorem R154075 : Reach 154075 := rs (se 1 (by rfl) ⟨115556, by rfl⟩) R231113
theorem R383635 : Reach 383635 := rs (se 1 (by rfl) ⟨287726, by rfl⟩) R575453
theorem R416441 : Reach 416441 := rs (se 2 (by rfl) ⟨156165, by rfl⟩) R312331
theorem R318163 : Reach 318163 := rs (se 1 (by rfl) ⟨238622, by rfl⟩) R477245
theorem R318167 : Reach 318167 := rs (se 1 (by rfl) ⟨238625, by rfl⟩) R477251
theorem R1432349 : Reach 1432349 := rs (se 3 (by rfl) ⟨268565, by rfl⟩) R537131
theorem R318383 : Reach 318383 := rs (se 1 (by rfl) ⟨238787, by rfl⟩) R477575
theorem R187355 : Reach 187355 := rs (se 1 (by rfl) ⟨140516, by rfl⟩) R281033
theorem R154703 : Reach 154703 := rs (se 1 (by rfl) ⟨116027, by rfl⟩) R232055
theorem R253007 : Reach 253007 := rs (se 1 (by rfl) ⟨189755, by rfl⟩) R379511
theorem R253085 : Reach 253085 := rs (se 3 (by rfl) ⟨47453, by rfl⟩) R94907
theorem R1039553 : Reach 1039553 := rs (se 2 (by rfl) ⟨389832, by rfl⟩) R779665
theorem R351499 : Reach 351499 := rs (se 1 (by rfl) ⟨263624, by rfl⟩) R527249
theorem R286217 : Reach 286217 := rs (se 2 (by rfl) ⟨107331, by rfl⟩) R214663
theorem R351803 : Reach 351803 := rs (se 1 (by rfl) ⟨263852, by rfl⟩) R527705
theorem R221089 : Reach 221089 := rs (se 2 (by rfl) ⟨82908, by rfl⟩) R165817
theorem R155567 : Reach 155567 := rs (se 1 (by rfl) ⟨116675, by rfl⟩) R233351
theorem R679873 : Reach 679873 := rs (se 2 (by rfl) ⟨254952, by rfl⟩) R509905
theorem R1466545 : Reach 1466545 := rs (se 2 (by rfl) ⟨549954, by rfl⟩) R1099909
theorem R286967 : Reach 286967 := rs (se 1 (by rfl) ⟨215225, by rfl⟩) R430451
theorem R712961 : Reach 712961 := rs (se 2 (by rfl) ⟨267360, by rfl⟩) R534721
theorem R155999 : Reach 155999 := rs (se 1 (by rfl) ⟨116999, by rfl⟩) R233999
theorem R3465787 : Reach 3465787 := rs (se 1 (by rfl) ⟨2599340, by rfl⟩) R5198681
theorem R352957 : Reach 352957 := rs (se 3 (by rfl) ⟨66179, by rfl⟩) R132359
theorem R910187 : Reach 910187 := rs (se 1 (by rfl) ⟨682640, by rfl⟩) R1365281
theorem R156559 : Reach 156559 := rs (se 1 (by rfl) ⟨117419, by rfl⟩) R234839
theorem R680849 : Reach 680849 := rs (se 2 (by rfl) ⟨255318, by rfl⟩) R510637
theorem R91175 : Reach 91175 := rs (se 1 (by rfl) ⟨68381, by rfl⟩) R136763
theorem R91215 : Reach 91215 := rs (se 1 (by rfl) ⟨68411, by rfl⟩) R136823
theorem R91231 : Reach 91231 := rs (se 1 (by rfl) ⟨68423, by rfl⟩) R136847
theorem R91259 : Reach 91259 := rs (se 1 (by rfl) ⟨68444, by rfl⟩) R136889
theorem R91311 : Reach 91311 := rs (se 1 (by rfl) ⟨68483, by rfl⟩) R136967
theorem R91335 : Reach 91335 := rs (se 1 (by rfl) ⟨68501, by rfl⟩) R137003
theorem R91355 : Reach 91355 := rs (se 1 (by rfl) ⟨68516, by rfl⟩) R137033
theorem R320759 : Reach 320759 := rs (se 1 (by rfl) ⟨240569, by rfl⟩) R481139
theorem R91431 : Reach 91431 := rs (se 1 (by rfl) ⟨68573, by rfl⟩) R137147
theorem R91471 : Reach 91471 := rs (se 1 (by rfl) ⟨68603, by rfl⟩) R137207
theorem R91487 : Reach 91487 := rs (se 1 (by rfl) ⟨68615, by rfl⟩) R137231
theorem R91515 : Reach 91515 := rs (se 1 (by rfl) ⟨68636, by rfl⟩) R137273
theorem R484733 : Reach 484733 := rs (se 3 (by rfl) ⟨90887, by rfl⟩) R181775
theorem R91567 : Reach 91567 := rs (se 1 (by rfl) ⟨68675, by rfl⟩) R137351
theorem R91591 : Reach 91591 := rs (se 1 (by rfl) ⟨68693, by rfl⟩) R137387
theorem R91611 : Reach 91611 := rs (se 1 (by rfl) ⟨68708, by rfl⟩) R137417
theorem R91687 : Reach 91687 := rs (se 1 (by rfl) ⟨68765, by rfl⟩) R137531
theorem R157241 : Reach 157241 := rs (se 2 (by rfl) ⟨58965, by rfl⟩) R117931
theorem R91727 : Reach 91727 := rs (se 1 (by rfl) ⟨68795, by rfl⟩) R137591
theorem R91743 : Reach 91743 := rs (se 1 (by rfl) ⟨68807, by rfl⟩) R137615
theorem R91771 : Reach 91771 := rs (se 1 (by rfl) ⟨68828, by rfl⟩) R137657
theorem R353915 : Reach 353915 := rs (se 1 (by rfl) ⟨265436, by rfl⟩) R530873
theorem R91823 : Reach 91823 := rs (se 1 (by rfl) ⟨68867, by rfl⟩) R137735
theorem R91847 : Reach 91847 := rs (se 1 (by rfl) ⟨68885, by rfl⟩) R137771
theorem R91867 : Reach 91867 := rs (se 1 (by rfl) ⟨68900, by rfl⟩) R137801
theorem R91943 : Reach 91943 := rs (se 1 (by rfl) ⟨68957, by rfl⟩) R137915
theorem R223049 : Reach 223049 := rs (se 2 (by rfl) ⟨83643, by rfl⟩) R167287
theorem R91983 : Reach 91983 := rs (se 1 (by rfl) ⟨68987, by rfl⟩) R137975
theorem R91999 : Reach 91999 := rs (se 1 (by rfl) ⟨68999, by rfl⟩) R137999
theorem R92027 : Reach 92027 := rs (se 1 (by rfl) ⟨69020, by rfl⟩) R138041
theorem R92079 : Reach 92079 := rs (se 1 (by rfl) ⟨69059, by rfl⟩) R138119
theorem R1894337 : Reach 1894337 := rs (se 2 (by rfl) ⟨710376, by rfl⟩) R1420753
theorem R92103 : Reach 92103 := rs (se 1 (by rfl) ⟨69077, by rfl⟩) R138155
theorem R92123 : Reach 92123 := rs (se 1 (by rfl) ⟨69092, by rfl⟩) R138185
theorem R1042469 : Reach 1042469 := rs (se 4 (by rfl) ⟨97731, by rfl⟩) R195463
theorem R92199 : Reach 92199 := rs (se 1 (by rfl) ⟨69149, by rfl⟩) R138299
theorem R92239 : Reach 92239 := rs (se 1 (by rfl) ⟨69179, by rfl⟩) R138359
theorem R92255 : Reach 92255 := rs (se 1 (by rfl) ⟨69191, by rfl⟩) R138383
theorem R92283 : Reach 92283 := rs (se 1 (by rfl) ⟨69212, by rfl⟩) R138425
theorem R92335 : Reach 92335 := rs (se 1 (by rfl) ⟨69251, by rfl⟩) R138503
theorem R92359 : Reach 92359 := rs (se 1 (by rfl) ⟨69269, by rfl⟩) R138539
theorem R92379 : Reach 92379 := rs (se 1 (by rfl) ⟨69284, by rfl⟩) R138569
theorem R157943 : Reach 157943 := rs (se 1 (by rfl) ⟨118457, by rfl⟩) R236915
theorem R92455 : Reach 92455 := rs (se 1 (by rfl) ⟨69341, by rfl⟩) R138683
theorem R190793 : Reach 190793 := rs (se 2 (by rfl) ⟨71547, by rfl⟩) R143095
theorem R92495 : Reach 92495 := rs (se 1 (by rfl) ⟨69371, by rfl⟩) R138743
theorem R747863 : Reach 747863 := rs (se 1 (by rfl) ⟨560897, by rfl⟩) R1121795
theorem R92511 : Reach 92511 := rs (se 1 (by rfl) ⟨69383, by rfl⟩) R138767
theorem R92539 : Reach 92539 := rs (se 1 (by rfl) ⟨69404, by rfl⟩) R138809
theorem R354689 : Reach 354689 := rs (se 2 (by rfl) ⟨133008, by rfl⟩) R266017
theorem R92591 : Reach 92591 := rs (se 1 (by rfl) ⟨69443, by rfl⟩) R138887
theorem R92615 : Reach 92615 := rs (se 1 (by rfl) ⟨69461, by rfl⟩) R138923
theorem R92635 : Reach 92635 := rs (se 1 (by rfl) ⟨69476, by rfl⟩) R138953
theorem R92711 : Reach 92711 := rs (se 1 (by rfl) ⟨69533, by rfl⟩) R139067
theorem R748091 : Reach 748091 := rs (se 1 (by rfl) ⟨561068, by rfl⟩) R1122137
theorem R92751 : Reach 92751 := rs (se 1 (by rfl) ⟨69563, by rfl⟩) R139127
theorem R158287 : Reach 158287 := rs (se 1 (by rfl) ⟨118715, by rfl⟩) R237431
theorem R92767 : Reach 92767 := rs (se 1 (by rfl) ⟨69575, by rfl⟩) R139151
theorem R92795 : Reach 92795 := rs (se 1 (by rfl) ⟨69596, by rfl⟩) R139193
theorem R92847 : Reach 92847 := rs (se 1 (by rfl) ⟨69635, by rfl⟩) R139271
theorem R92871 : Reach 92871 := rs (se 1 (by rfl) ⟨69653, by rfl⟩) R139307
theorem R781001 : Reach 781001 := rs (se 2 (by rfl) ⟨292875, by rfl⟩) R585751
theorem R92891 : Reach 92891 := rs (se 1 (by rfl) ⟨69668, by rfl⟩) R139337
theorem R92967 : Reach 92967 := rs (se 1 (by rfl) ⟨69725, by rfl⟩) R139451
theorem R158537 : Reach 158537 := rs (se 2 (by rfl) ⟨59451, by rfl⟩) R118903
theorem R93007 : Reach 93007 := rs (se 1 (by rfl) ⟨69755, by rfl⟩) R139511
theorem R93023 : Reach 93023 := rs (se 1 (by rfl) ⟨69767, by rfl⟩) R139535
theorem R93051 : Reach 93051 := rs (se 1 (by rfl) ⟨69788, by rfl⟩) R139577
theorem R93103 : Reach 93103 := rs (se 1 (by rfl) ⟨69827, by rfl⟩) R139655
theorem R93127 : Reach 93127 := rs (se 1 (by rfl) ⟨69845, by rfl⟩) R139691
theorem R93147 : Reach 93147 := rs (se 1 (by rfl) ⟨69860, by rfl⟩) R139721
theorem R93223 : Reach 93223 := rs (se 1 (by rfl) ⟨69917, by rfl⟩) R139835
theorem R93263 : Reach 93263 := rs (se 1 (by rfl) ⟨69947, by rfl⟩) R139895
theorem R93279 : Reach 93279 := rs (se 1 (by rfl) ⟨69959, by rfl⟩) R139919
theorem R93307 : Reach 93307 := rs (se 1 (by rfl) ⟨69980, by rfl⟩) R139961
theorem R93359 : Reach 93359 := rs (se 1 (by rfl) ⟨70019, by rfl⟩) R140039
theorem R93383 : Reach 93383 := rs (se 1 (by rfl) ⟨70037, by rfl⟩) R140075
theorem R93403 : Reach 93403 := rs (se 1 (by rfl) ⟨70052, by rfl⟩) R140105
theorem R158969 : Reach 158969 := rs (se 2 (by rfl) ⟨59613, by rfl⟩) R119227
theorem R93479 : Reach 93479 := rs (se 1 (by rfl) ⟨70109, by rfl⟩) R140219
theorem R93519 : Reach 93519 := rs (se 1 (by rfl) ⟨70139, by rfl⟩) R140279
theorem R93535 : Reach 93535 := rs (se 1 (by rfl) ⟨70151, by rfl⟩) R140303
theorem R93563 : Reach 93563 := rs (se 1 (by rfl) ⟨70172, by rfl⟩) R140345
theorem R93615 : Reach 93615 := rs (se 1 (by rfl) ⟨70211, by rfl⟩) R140423
theorem R159151 : Reach 159151 := rs (se 1 (by rfl) ⟨119363, by rfl⟩) R238727
theorem R93639 : Reach 93639 := rs (se 1 (by rfl) ⟨70229, by rfl⟩) R140459
theorem R93659 : Reach 93659 := rs (se 1 (by rfl) ⟨70244, by rfl⟩) R140489
theorem R159239 : Reach 159239 := rs (se 1 (by rfl) ⟨119429, by rfl⟩) R238859
theorem R355873 : Reach 355873 := rs (se 2 (by rfl) ⟨133452, by rfl⟩) R266905
theorem R93735 : Reach 93735 := rs (se 1 (by rfl) ⟨70301, by rfl⟩) R140603
theorem R93775 : Reach 93775 := rs (se 1 (by rfl) ⟨70331, by rfl⟩) R140663
theorem R2289239 : Reach 2289239 := rs (se 1 (by rfl) ⟨1716929, by rfl⟩) R3433859
theorem R93791 : Reach 93791 := rs (se 1 (by rfl) ⟨70343, by rfl⟩) R140687
theorem R93819 : Reach 93819 := rs (se 1 (by rfl) ⟨70364, by rfl⟩) R140729
theorem R93871 : Reach 93871 := rs (se 1 (by rfl) ⟨70403, by rfl⟩) R140807
theorem R93895 : Reach 93895 := rs (se 1 (by rfl) ⟨70421, by rfl⟩) R140843
theorem R93915 : Reach 93915 := rs (se 1 (by rfl) ⟨70436, by rfl⟩) R140873
theorem R93991 : Reach 93991 := rs (se 1 (by rfl) ⟨70493, by rfl⟩) R140987
theorem R94031 : Reach 94031 := rs (se 1 (by rfl) ⟨70523, by rfl⟩) R141047
theorem R94047 : Reach 94047 := rs (se 1 (by rfl) ⟨70535, by rfl⟩) R141071
theorem R159583 : Reach 159583 := rs (se 1 (by rfl) ⟨119687, by rfl⟩) R239375
theorem R94075 : Reach 94075 := rs (se 1 (by rfl) ⟨70556, by rfl⟩) R141113
theorem R94127 : Reach 94127 := rs (se 1 (by rfl) ⟨70595, by rfl⟩) R141191
theorem R159671 : Reach 159671 := rs (se 1 (by rfl) ⟨119753, by rfl⟩) R239507
theorem R94151 : Reach 94151 := rs (se 1 (by rfl) ⟨70613, by rfl⟩) R141227
theorem R94171 : Reach 94171 := rs (se 1 (by rfl) ⟨70628, by rfl⟩) R141257
theorem R356359 : Reach 356359 := rs (se 1 (by rfl) ⟨267269, by rfl⟩) R534539
theorem R94247 : Reach 94247 := rs (se 1 (by rfl) ⟨70685, by rfl⟩) R141371
theorem R94287 : Reach 94287 := rs (se 1 (by rfl) ⟨70715, by rfl⟩) R141431
theorem R94303 : Reach 94303 := rs (se 1 (by rfl) ⟨70727, by rfl⟩) R141455
theorem R94331 : Reach 94331 := rs (se 1 (by rfl) ⟨70748, by rfl⟩) R141497
theorem R94383 : Reach 94383 := rs (se 1 (by rfl) ⟨70787, by rfl⟩) R141575
theorem R94407 : Reach 94407 := rs (se 1 (by rfl) ⟨70805, by rfl⟩) R141611
theorem R94427 : Reach 94427 := rs (se 1 (by rfl) ⟨70820, by rfl⟩) R141641
theorem R94503 : Reach 94503 := rs (se 1 (by rfl) ⟨70877, by rfl⟩) R141755
theorem R94543 : Reach 94543 := rs (se 1 (by rfl) ⟨70907, by rfl⟩) R141815
theorem R94559 : Reach 94559 := rs (se 1 (by rfl) ⟨70919, by rfl⟩) R141839
theorem R455017 : Reach 455017 := rs (se 2 (by rfl) ⟨170631, by rfl⟩) R341263
theorem R94587 : Reach 94587 := rs (se 1 (by rfl) ⟨70940, by rfl⟩) R141881
theorem R94639 : Reach 94639 := rs (se 1 (by rfl) ⟨70979, by rfl⟩) R141959
theorem R94663 : Reach 94663 := rs (se 1 (by rfl) ⟨70997, by rfl⟩) R141995
theorem R94683 : Reach 94683 := rs (se 1 (by rfl) ⟨71012, by rfl⟩) R142025
theorem R356845 : Reach 356845 := rs (se 3 (by rfl) ⟨66908, by rfl⟩) R133817
theorem R160265 : Reach 160265 := rs (se 2 (by rfl) ⟨60099, by rfl⟩) R120199
theorem R717335 : Reach 717335 := rs (se 1 (by rfl) ⟨538001, by rfl⟩) R1076003
theorem R94759 : Reach 94759 := rs (se 1 (by rfl) ⟨71069, by rfl⟩) R142139
theorem R324155 : Reach 324155 := rs (se 1 (by rfl) ⟨243116, by rfl⟩) R486233
theorem R94799 : Reach 94799 := rs (se 1 (by rfl) ⟨71099, by rfl⟩) R142199
theorem R94815 : Reach 94815 := rs (se 1 (by rfl) ⟨71111, by rfl⟩) R142223
theorem R94843 : Reach 94843 := rs (se 1 (by rfl) ⟨71132, by rfl⟩) R142265
theorem R160427 : Reach 160427 := rs (se 1 (by rfl) ⟨120320, by rfl⟩) R240641
theorem R94895 : Reach 94895 := rs (se 1 (by rfl) ⟨71171, by rfl⟩) R142343
theorem R94919 : Reach 94919 := rs (se 1 (by rfl) ⟨71189, by rfl⟩) R142379
theorem R94939 : Reach 94939 := rs (se 1 (by rfl) ⟨71204, by rfl⟩) R142409
theorem R357149 : Reach 357149 := rs (se 3 (by rfl) ⟨66965, by rfl⟩) R133931
theorem R95015 : Reach 95015 := rs (se 1 (by rfl) ⟨71261, by rfl⟩) R142523
theorem R95055 : Reach 95055 := rs (se 1 (by rfl) ⟨71291, by rfl⟩) R142583
theorem R95071 : Reach 95071 := rs (se 1 (by rfl) ⟨71303, by rfl⟩) R142607
theorem R95099 : Reach 95099 := rs (se 1 (by rfl) ⟨71324, by rfl⟩) R142649
theorem R750973 : Reach 750973 := rs (se 3 (by rfl) ⟨140807, by rfl⟩) R281615
theorem R259471 : Reach 259471 := rs (se 1 (by rfl) ⟨194603, by rfl⟩) R389207
theorem R194087 : Reach 194087 := rs (se 1 (by rfl) ⟨145565, by rfl⟩) R291131
theorem R521873 : Reach 521873 := rs (se 2 (by rfl) ⟨195702, by rfl⟩) R391405
theorem R96175 : Reach 96175 := rs (se 1 (by rfl) ⟨72131, by rfl⟩) R144263
theorem R293017 : Reach 293017 := rs (se 2 (by rfl) ⟨109881, by rfl⟩) R219763
theorem R1669409 : Reach 1669409 := rs (se 2 (by rfl) ⟨626028, by rfl⟩) R1252057
theorem R522557 : Reach 522557 := rs (se 3 (by rfl) ⟨97979, by rfl⟩) R195959
theorem R1112453 : Reach 1112453 := rs (se 4 (by rfl) ⟨104292, by rfl⟩) R208585
theorem R588235 : Reach 588235 := rs (se 1 (by rfl) ⟨441176, by rfl⟩) R882353
theorem R227827 : Reach 227827 := rs (se 1 (by rfl) ⟨170870, by rfl⟩) R341741
theorem R359275 : Reach 359275 := rs (se 1 (by rfl) ⟨269456, by rfl⟩) R538913
theorem R1276901 : Reach 1276901 := rs (se 4 (by rfl) ⟨119709, by rfl⟩) R239419
theorem R392363 : Reach 392363 := rs (se 1 (by rfl) ⟨294272, by rfl⟩) R588545
theorem R1015031 : Reach 1015031 := rs (se 1 (by rfl) ⟨761273, by rfl⟩) R1522547
theorem R1048301 : Reach 1048301 := rs (se 3 (by rfl) ⟨196556, by rfl⟩) R393113
theorem R753569 : Reach 753569 := rs (se 2 (by rfl) ⟨282588, by rfl⟩) R565177
theorem R1572941 : Reach 1572941 := rs (se 3 (by rfl) ⟨294926, by rfl⟩) R589853
theorem R98911 : Reach 98911 := rs (se 1 (by rfl) ⟨74183, by rfl⟩) R148367
theorem R131807 : Reach 131807 := rs (se 1 (by rfl) ⟨98855, by rfl⟩) R197711
theorem R4621049 : Reach 4621049 := rs (se 2 (by rfl) ⟨1732893, by rfl⟩) R3465787
theorem R263159 : Reach 263159 := rs (se 1 (by rfl) ⟨197369, by rfl⟩) R394739
theorem R395063 : Reach 395063 := rs (se 1 (by rfl) ⟨296297, by rfl⟩) R592595
theorem R100175 : Reach 100175 := rs (se 1 (by rfl) ⟨75131, by rfl⟩) R150263
theorem R198607 : Reach 198607 := rs (se 1 (by rfl) ⟨148955, by rfl⟩) R297911
theorem R493697 : Reach 493697 := rs (se 2 (by rfl) ⟨185136, by rfl⟩) R370273
theorem R755905 : Reach 755905 := rs (se 2 (by rfl) ⟨283464, by rfl⟩) R566929
theorem R297245 : Reach 297245 := rs (se 3 (by rfl) ⟨55733, by rfl⟩) R111467
theorem R264559 : Reach 264559 := rs (se 1 (by rfl) ⟨198419, by rfl⟩) R396839
theorem R100807 : Reach 100807 := rs (se 1 (by rfl) ⟨75605, by rfl⟩) R151211
theorem R494075 : Reach 494075 := rs (se 1 (by rfl) ⟨370556, by rfl⟩) R741113
theorem R461375 : Reach 461375 := rs (se 1 (by rfl) ⟨346031, by rfl⟩) R692063
theorem R100927 : Reach 100927 := rs (se 1 (by rfl) ⟨75695, by rfl⟩) R151391
theorem R199351 : Reach 199351 := rs (se 1 (by rfl) ⟨149513, by rfl⟩) R299027
theorem R232571 : Reach 232571 := rs (se 1 (by rfl) ⟨174428, by rfl⟩) R348857
theorem R232591 : Reach 232591 := rs (se 1 (by rfl) ⟨174443, by rfl⟩) R348887
theorem R232865 : Reach 232865 := rs (se 2 (by rfl) ⟨87324, by rfl⟩) R174649
theorem R954899 : Reach 954899 := rs (se 1 (by rfl) ⟨716174, by rfl⟩) R1432349
theorem R856673 : Reach 856673 := rs (se 2 (by rfl) ⟨321252, by rfl⟩) R642505
theorem R463481 : Reach 463481 := rs (se 2 (by rfl) ⟨173805, by rfl⟩) R347611
theorem R103135 : Reach 103135 := rs (se 1 (by rfl) ⟨77351, by rfl⟩) R154703
theorem R398047 : Reach 398047 := rs (se 1 (by rfl) ⟨298535, by rfl⟩) R597071
theorem R168671 : Reach 168671 := rs (se 1 (by rfl) ⟨126503, by rfl⟩) R253007
theorem R693035 : Reach 693035 := rs (se 1 (by rfl) ⟨519776, by rfl⟩) R1039553
theorem R234535 : Reach 234535 := rs (se 1 (by rfl) ⟨175901, by rfl⟩) R351803
theorem R595001 : Reach 595001 := rs (se 2 (by rfl) ⟨223125, by rfl⟩) R446251
theorem R398479 : Reach 398479 := rs (se 1 (by rfl) ⟨298859, by rfl⟩) R597719
theorem R267407 : Reach 267407 := rs (se 1 (by rfl) ⟨200555, by rfl⟩) R401111
theorem R103711 : Reach 103711 := rs (se 1 (by rfl) ⟨77783, by rfl⟩) R155567
theorem R398753 : Reach 398753 := rs (se 2 (by rfl) ⟨149532, by rfl⟩) R299065
theorem R136697 : Reach 136697 := rs (se 2 (by rfl) ⟨51261, by rfl⟩) R102523
theorem R235001 : Reach 235001 := rs (se 2 (by rfl) ⟨88125, by rfl⟩) R176251
theorem R202247 : Reach 202247 := rs (se 1 (by rfl) ⟨151685, by rfl⟩) R303371
theorem R103999 : Reach 103999 := rs (se 1 (by rfl) ⟨77999, by rfl⟩) R155999
theorem R136799 : Reach 136799 := rs (se 1 (by rfl) ⟨102599, by rfl⟩) R205199
theorem R202427 : Reach 202427 := rs (se 1 (by rfl) ⟨151820, by rfl⟩) R303641
theorem R202537 : Reach 202537 := rs (se 2 (by rfl) ⟨75951, by rfl⟩) R151903
theorem R137015 : Reach 137015 := rs (se 1 (by rfl) ⟨102761, by rfl⟩) R205523
theorem R137321 : Reach 137321 := rs (se 2 (by rfl) ⟨51495, by rfl⟩) R102991
theorem R235649 : Reach 235649 := rs (se 2 (by rfl) ⟨88368, by rfl⟩) R176737
theorem R268541 : Reach 268541 := rs (se 3 (by rfl) ⟨50351, by rfl⟩) R100703
theorem R465263 : Reach 465263 := rs (se 1 (by rfl) ⟨348947, by rfl⟩) R697895
theorem R104827 : Reach 104827 := rs (se 1 (by rfl) ⟨78620, by rfl⟩) R157241
theorem R137639 : Reach 137639 := rs (se 1 (by rfl) ⟨103229, by rfl⟩) R206459
theorem R235943 : Reach 235943 := rs (se 1 (by rfl) ⟨176957, by rfl⟩) R353915
theorem R137723 : Reach 137723 := rs (se 1 (by rfl) ⟨103292, by rfl⟩) R206585
theorem R334331 : Reach 334331 := rs (se 1 (by rfl) ⟨250748, by rfl⟩) R501497
theorem R236105 : Reach 236105 := rs (se 2 (by rfl) ⟨88539, by rfl⟩) R177079
theorem R137849 : Reach 137849 := rs (se 2 (by rfl) ⟨51693, by rfl⟩) R103387
theorem R137903 : Reach 137903 := rs (se 1 (by rfl) ⟨103427, by rfl⟩) R206855
theorem R1776323 : Reach 1776323 := rs (se 1 (by rfl) ⟨1332242, by rfl⟩) R2664485
theorem R694979 : Reach 694979 := rs (se 1 (by rfl) ⟨521234, by rfl⟩) R1042469
theorem R137951 : Reach 137951 := rs (se 1 (by rfl) ⟨103463, by rfl⟩) R206927
theorem R105295 : Reach 105295 := rs (se 1 (by rfl) ⟨78971, by rfl⟩) R157943
theorem R498575 : Reach 498575 := rs (se 1 (by rfl) ⟨373931, by rfl⟩) R747863
theorem R236459 : Reach 236459 := rs (se 1 (by rfl) ⟨177344, by rfl⟩) R354689
theorem R138215 : Reach 138215 := rs (se 1 (by rfl) ⟨103661, by rfl⟩) R207323
theorem R498727 : Reach 498727 := rs (se 1 (by rfl) ⟨374045, by rfl⟩) R748091
theorem R236641 : Reach 236641 := rs (se 2 (by rfl) ⟨88740, by rfl⟩) R177481
theorem R105691 : Reach 105691 := rs (se 1 (by rfl) ⟨79268, by rfl⟩) R158537
theorem R138473 : Reach 138473 := rs (se 2 (by rfl) ⟨51927, by rfl⟩) R103855
theorem R138527 : Reach 138527 := rs (se 1 (by rfl) ⟨103895, by rfl⟩) R207791
theorem R138695 : Reach 138695 := rs (se 1 (by rfl) ⟨104021, by rfl⟩) R208043
theorem R400889 : Reach 400889 := rs (se 2 (by rfl) ⟨150333, by rfl⟩) R300667
theorem R105979 : Reach 105979 := rs (se 1 (by rfl) ⟨79484, by rfl⟩) R158969
theorem R794123 : Reach 794123 := rs (se 1 (by rfl) ⟨595592, by rfl⟩) R1191185
theorem R597563 : Reach 597563 := rs (se 1 (by rfl) ⟨448172, by rfl⟩) R896345
theorem R106159 : Reach 106159 := rs (se 1 (by rfl) ⟨79619, by rfl⟩) R159239
theorem R139049 : Reach 139049 := rs (se 2 (by rfl) ⟨52143, by rfl⟩) R104287
theorem R139055 : Reach 139055 := rs (se 1 (by rfl) ⟨104291, by rfl⟩) R208583
theorem R401213 : Reach 401213 := rs (se 3 (by rfl) ⟨75227, by rfl⟩) R150455
theorem R532331 : Reach 532331 := rs (se 1 (by rfl) ⟨399248, by rfl⟩) R798497
theorem R270209 : Reach 270209 := rs (se 2 (by rfl) ⟨101328, by rfl⟩) R202657
theorem R106447 : Reach 106447 := rs (se 1 (by rfl) ⟨79835, by rfl⟩) R159671
theorem R237593 : Reach 237593 := rs (se 2 (by rfl) ⟨89097, by rfl⟩) R178195
theorem R139529 : Reach 139529 := rs (se 2 (by rfl) ⟨52323, by rfl⟩) R104647
theorem R270665 : Reach 270665 := rs (se 2 (by rfl) ⟨101499, by rfl⟩) R202999
theorem R106843 : Reach 106843 := rs (se 1 (by rfl) ⟨80132, by rfl⟩) R160265
theorem R205163 : Reach 205163 := rs (se 1 (by rfl) ⟨153872, by rfl⟩) R307745
theorem R139631 : Reach 139631 := rs (se 1 (by rfl) ⟨104723, by rfl⟩) R209447
theorem R106951 : Reach 106951 := rs (se 1 (by rfl) ⟨80213, by rfl⟩) R160427
theorem R238049 : Reach 238049 := rs (se 2 (by rfl) ⟨89268, by rfl⟩) R178537
theorem R205307 : Reach 205307 := rs (se 1 (by rfl) ⟨153980, by rfl⟩) R307961
theorem R238099 : Reach 238099 := rs (se 1 (by rfl) ⟨178574, by rfl⟩) R357149
theorem R139847 : Reach 139847 := rs (se 1 (by rfl) ⟨104885, by rfl⟩) R209771
theorem R139883 : Reach 139883 := rs (se 1 (by rfl) ⟨104912, by rfl⟩) R209825
theorem R205433 : Reach 205433 := rs (se 2 (by rfl) ⟨77037, by rfl⟩) R154075
theorem R303769 : Reach 303769 := rs (se 2 (by rfl) ⟨113913, by rfl⟩) R227827
theorem R205487 : Reach 205487 := rs (se 1 (by rfl) ⟨154115, by rfl⟩) R308231
theorem R205559 : Reach 205559 := rs (se 1 (by rfl) ⟨154169, by rfl⟩) R308339
theorem R140111 : Reach 140111 := rs (se 1 (by rfl) ⟨105083, by rfl⟩) R210167
theorem R205739 : Reach 205739 := rs (se 1 (by rfl) ⟨154304, by rfl⟩) R308609
theorem R402529 : Reach 402529 := rs (se 2 (by rfl) ⟨150948, by rfl⟩) R301897
theorem R140507 : Reach 140507 := rs (se 1 (by rfl) ⟨105380, by rfl⟩) R210761
theorem R140681 : Reach 140681 := rs (se 2 (by rfl) ⟨52755, by rfl⟩) R105511
theorem R206279 : Reach 206279 := rs (se 1 (by rfl) ⟨154709, by rfl⟩) R309419
theorem R468665 : Reach 468665 := rs (se 2 (by rfl) ⟨175749, by rfl⟩) R351499
theorem R141035 : Reach 141035 := rs (se 1 (by rfl) ⟨105776, by rfl⟩) R211553
theorem R206639 : Reach 206639 := rs (se 1 (by rfl) ⟨154979, by rfl⟩) R309959
theorem R141263 : Reach 141263 := rs (se 1 (by rfl) ⟨105947, by rfl⟩) R211895
theorem R239881 : Reach 239881 := rs (se 2 (by rfl) ⟨89955, by rfl⟩) R179911
theorem R141659 : Reach 141659 := rs (se 1 (by rfl) ⟨106244, by rfl⟩) R212489
theorem R207215 : Reach 207215 := rs (se 1 (by rfl) ⟨155411, by rfl⟩) R310823
theorem R207287 : Reach 207287 := rs (se 1 (by rfl) ⟨155465, by rfl⟩) R310931
theorem R534995 : Reach 534995 := rs (se 1 (by rfl) ⟨401246, by rfl⟩) R802493
theorem R698867 : Reach 698867 := rs (se 1 (by rfl) ⟨524150, by rfl⟩) R1048301
theorem R141887 : Reach 141887 := rs (se 1 (by rfl) ⟨106415, by rfl⟩) R212831
theorem R207431 : Reach 207431 := rs (se 1 (by rfl) ⟨155573, by rfl⟩) R311147
theorem R207467 : Reach 207467 := rs (se 1 (by rfl) ⟨155600, by rfl⟩) R311201
theorem R502379 : Reach 502379 := rs (se 1 (by rfl) ⟨376784, by rfl⟩) R753569
theorem R142007 : Reach 142007 := rs (se 1 (by rfl) ⟨106505, by rfl⟩) R213011
theorem R142235 : Reach 142235 := rs (se 1 (by rfl) ⟨106676, by rfl⟩) R213353
theorem R306163 : Reach 306163 := rs (se 1 (by rfl) ⟨229622, by rfl⟩) R459245
theorem R207863 : Reach 207863 := rs (se 1 (by rfl) ⟨155897, by rfl⟩) R311795
theorem R1485863 : Reach 1485863 := rs (se 1 (by rfl) ⟨1114397, by rfl⟩) R2228795
theorem R404561 : Reach 404561 := rs (se 2 (by rfl) ⟨151710, by rfl⟩) R303421
theorem R142631 : Reach 142631 := rs (se 1 (by rfl) ⟨106973, by rfl⟩) R213947
theorem R765245 : Reach 765245 := rs (se 3 (by rfl) ⟨143483, by rfl⟩) R286967
theorem R208223 : Reach 208223 := rs (se 1 (by rfl) ⟨156167, by rfl⟩) R312335
theorem R470609 : Reach 470609 := rs (se 2 (by rfl) ⟨176478, by rfl⟩) R352957
theorem R208619 : Reach 208619 := rs (se 1 (by rfl) ⟨156464, by rfl⟩) R312929
theorem R208745 : Reach 208745 := rs (se 2 (by rfl) ⟨78279, by rfl⟩) R156559
theorem R176609 : Reach 176609 := rs (se 2 (by rfl) ⟨66228, by rfl⟩) R132457
theorem R242297 : Reach 242297 := rs (se 2 (by rfl) ⟨90861, by rfl⟩) R181723
theorem R209591 : Reach 209591 := rs (se 1 (by rfl) ⟨157193, by rfl⟩) R314387
theorem R897821 : Reach 897821 := rs (se 3 (by rfl) ⟨168341, by rfl⟩) R336683
theorem R2634605 : Reach 2634605 := rs (se 3 (by rfl) ⟨493988, by rfl⟩) R987977
theorem R209807 : Reach 209807 := rs (se 1 (by rfl) ⟨157355, by rfl⟩) R314711
theorem R1324583 : Reach 1324583 := rs (se 1 (by rfl) ⟨993437, by rfl⟩) R1986875
theorem R210527 : Reach 210527 := rs (se 1 (by rfl) ⟨157895, by rfl⟩) R315791
theorem R243361 : Reach 243361 := rs (se 2 (by rfl) ⟨91260, by rfl⟩) R182521
theorem R177967 : Reach 177967 := rs (se 1 (by rfl) ⟨133475, by rfl⟩) R266951
theorem R210743 : Reach 210743 := rs (se 1 (by rfl) ⟨158057, by rfl⟩) R316115
theorem R374615 : Reach 374615 := rs (se 1 (by rfl) ⟨280961, by rfl⟩) R561923
theorem R473039 : Reach 473039 := rs (se 1 (by rfl) ⟨354779, by rfl⟩) R709559
theorem R2046053 : Reach 2046053 := rs (se 4 (by rfl) ⟨191817, by rfl⟩) R383635
theorem R211049 : Reach 211049 := rs (se 2 (by rfl) ⟨79143, by rfl⟩) R158287
theorem R374969 : Reach 374969 := rs (se 2 (by rfl) ⟨140613, by rfl⟩) R281227
theorem R506341 : Reach 506341 := rs (se 4 (by rfl) ⟨47469, by rfl⟩) R94939
theorem R211535 : Reach 211535 := rs (se 1 (by rfl) ⟨158651, by rfl⟩) R317303
theorem R473795 : Reach 473795 := rs (se 1 (by rfl) ⟨355346, by rfl⟩) R710693
theorem R211679 : Reach 211679 := rs (se 1 (by rfl) ⟨158759, by rfl⟩) R317519
theorem R179023 : Reach 179023 := rs (se 1 (by rfl) ⟨134267, by rfl⟩) R268535
theorem R474011 : Reach 474011 := rs (se 1 (by rfl) ⟨355508, by rfl⟩) R711017
theorem R211931 : Reach 211931 := rs (se 1 (by rfl) ⟨158948, by rfl⟩) R317897
theorem R277627 : Reach 277627 := rs (se 1 (by rfl) ⟨208220, by rfl⟩) R416441
theorem R212111 : Reach 212111 := rs (se 1 (by rfl) ⟨159083, by rfl⟩) R318167
theorem R212201 : Reach 212201 := rs (se 2 (by rfl) ⟨79575, by rfl⟩) R159151
theorem R212255 : Reach 212255 := rs (se 1 (by rfl) ⟨159191, by rfl⟩) R318383
theorem R114043 : Reach 114043 := rs (se 1 (by rfl) ⟨85532, by rfl⟩) R171065
theorem R474497 : Reach 474497 := rs (se 2 (by rfl) ⟨177936, by rfl⟩) R355873
theorem R310715 : Reach 310715 := rs (se 1 (by rfl) ⟨233036, by rfl⟩) R466073
theorem R212777 : Reach 212777 := rs (se 2 (by rfl) ⟨79791, by rfl⟩) R159583
theorem R573257 : Reach 573257 := rs (se 2 (by rfl) ⟨214971, by rfl⟩) R429943
theorem R769985 : Reach 769985 := rs (se 2 (by rfl) ⟨288744, by rfl⟩) R577489
theorem R475145 : Reach 475145 := rs (se 2 (by rfl) ⟨178179, by rfl⟩) R356359
theorem R475307 : Reach 475307 := rs (se 1 (by rfl) ⟨356480, by rfl⟩) R712961
theorem R11583755 : Reach 11583755 := rs (se 1 (by rfl) ⟨8687816, by rfl⟩) R17375633
theorem R606689 : Reach 606689 := rs (se 2 (by rfl) ⟨227508, by rfl⟩) R455017
theorem R311879 : Reach 311879 := rs (se 1 (by rfl) ⟨233909, by rfl⟩) R467819
theorem R606791 : Reach 606791 := rs (se 1 (by rfl) ⟨455093, by rfl⟩) R910187
theorem R475793 : Reach 475793 := rs (se 2 (by rfl) ⟨178422, by rfl⟩) R356845
theorem R115435 : Reach 115435 := rs (se 1 (by rfl) ⟨86576, by rfl⟩) R173153
theorem R213839 : Reach 213839 := rs (se 1 (by rfl) ⟨160379, by rfl⟩) R320759
theorem R508781 : Reach 508781 := rs (se 3 (by rfl) ⟨95396, by rfl⟩) R190793
theorem R1295297 : Reach 1295297 := rs (se 2 (by rfl) ⟨485736, by rfl⟩) R971473
theorem R115663 : Reach 115663 := rs (se 1 (by rfl) ⟨86747, by rfl⟩) R173495
theorem R115931 : Reach 115931 := rs (se 1 (by rfl) ⟨86948, by rfl⟩) R173897
theorem R148699 : Reach 148699 := rs (se 1 (by rfl) ⟨111524, by rfl⟩) R223049
theorem R1262891 : Reach 1262891 := rs (se 1 (by rfl) ⟨947168, by rfl⟩) R1894337
theorem R804269 : Reach 804269 := rs (se 3 (by rfl) ⟨150800, by rfl⟩) R301601
theorem R116407 : Reach 116407 := rs (se 1 (by rfl) ⟨87305, by rfl⟩) R174611
theorem R1001297 : Reach 1001297 := rs (se 2 (by rfl) ⟨375486, by rfl⟩) R750973
theorem R345961 : Reach 345961 := rs (se 2 (by rfl) ⟨129735, by rfl⟩) R259471
theorem R116635 : Reach 116635 := rs (se 1 (by rfl) ⟨87476, by rfl⟩) R174953
theorem R1820677 : Reach 1820677 := rs (se 4 (by rfl) ⟨170688, by rfl⟩) R341377
theorem R1526159 : Reach 1526159 := rs (se 1 (by rfl) ⟨1144619, by rfl⟩) R2289239
theorem R117551 : Reach 117551 := rs (se 1 (by rfl) ⟨88163, by rfl⟩) R176327
theorem R478223 : Reach 478223 := rs (se 1 (by rfl) ⟨358667, by rfl⟩) R717335
theorem R216103 : Reach 216103 := rs (se 1 (by rfl) ⟨162077, by rfl⟩) R324155
theorem R674893 : Reach 674893 := rs (se 3 (by rfl) ⟨126542, by rfl⟩) R253085
theorem R314873 : Reach 314873 := rs (se 2 (by rfl) ⟨118077, by rfl⟩) R236155
theorem R315143 : Reach 315143 := rs (se 1 (by rfl) ⟨236357, by rfl⟩) R472715
theorem R347915 : Reach 347915 := rs (se 1 (by rfl) ⟨260936, by rfl⟩) R521873
theorem R479033 : Reach 479033 := rs (se 2 (by rfl) ⟨179637, by rfl⟩) R359275
theorem R315197 : Reach 315197 := rs (se 3 (by rfl) ⟨59099, by rfl⟩) R118199
theorem R1003373 : Reach 1003373 := rs (se 3 (by rfl) ⟨188132, by rfl⟩) R376265
theorem R348371 : Reach 348371 := rs (se 1 (by rfl) ⟨261278, by rfl⟩) R522557
theorem R4378853 : Reach 4378853 := rs (se 4 (by rfl) ⟨410517, by rfl⟩) R821035
theorem R741635 : Reach 741635 := rs (se 1 (by rfl) ⟨556226, by rfl⟩) R1112453
theorem R152185 : Reach 152185 := rs (se 2 (by rfl) ⟨57069, by rfl⟩) R114139
theorem R676687 : Reach 676687 := rs (se 1 (by rfl) ⟨507515, by rfl⟩) R1015031
theorem R906497 : Reach 906497 := rs (se 2 (by rfl) ⟨339936, by rfl⟩) R679873
theorem R1496501 : Reach 1496501 := rs (se 5 (by rfl) ⟨70148, by rfl⟩) R140297
theorem R1955393 : Reach 1955393 := rs (se 2 (by rfl) ⟨733272, by rfl⟩) R1466545
theorem R907037 : Reach 907037 := rs (se 3 (by rfl) ⟨170069, by rfl⟩) R340139
theorem R481261 : Reach 481261 := rs (se 3 (by rfl) ⟨90236, by rfl⟩) R180473
theorem R2840777 : Reach 2840777 := rs (se 2 (by rfl) ⟨1065291, by rfl⟩) R2130583
theorem R153947 : Reach 153947 := rs (se 1 (by rfl) ⟨115460, by rfl⟩) R230921
theorem R153967 : Reach 153967 := rs (se 1 (by rfl) ⟨115475, by rfl⟩) R230951
theorem R154183 : Reach 154183 := rs (se 1 (by rfl) ⟨115637, by rfl⟩) R231275
theorem R318059 : Reach 318059 := rs (se 1 (by rfl) ⟨238544, by rfl⟩) R477089
theorem R154615 : Reach 154615 := rs (se 1 (by rfl) ⟨115961, by rfl⟩) R231923
theorem R318653 : Reach 318653 := rs (se 3 (by rfl) ⟨59747, by rfl⟩) R119495
theorem R154919 : Reach 154919 := rs (se 1 (by rfl) ⟨116189, by rfl⟩) R232379
theorem R253223 : Reach 253223 := rs (se 1 (by rfl) ⟨189917, by rfl⟩) R379835
theorem R155371 : Reach 155371 := rs (se 1 (by rfl) ⟨116528, by rfl⟩) R233057
theorem R6086663 : Reach 6086663 := rs (se 1 (by rfl) ⟨4564997, by rfl⟩) R9129995
theorem R123385 : Reach 123385 := rs (se 2 (by rfl) ⟨46269, by rfl⟩) R92539
theorem R385607 : Reach 385607 := rs (se 1 (by rfl) ⟨289205, by rfl⟩) R578411
theorem R156343 : Reach 156343 := rs (se 1 (by rfl) ⟨117257, by rfl⟩) R234515
theorem R156647 : Reach 156647 := rs (se 1 (by rfl) ⟨117485, by rfl⟩) R234971
theorem R1565891 : Reach 1565891 := rs (se 1 (by rfl) ⟨1174418, by rfl⟩) R2348837
theorem R15262937 : Reach 15262937 := rs (se 2 (by rfl) ⟨5723601, by rfl⟩) R11447203
theorem R91423 : Reach 91423 := rs (se 1 (by rfl) ⟨68567, by rfl⟩) R137135
theorem R91483 : Reach 91483 := rs (se 1 (by rfl) ⟨68612, by rfl⟩) R137225
theorem R91503 : Reach 91503 := rs (se 1 (by rfl) ⟨68627, by rfl⟩) R137255
theorem R91559 : Reach 91559 := rs (se 1 (by rfl) ⟨68669, by rfl⟩) R137339
theorem R255419 : Reach 255419 := rs (se 1 (by rfl) ⟨191564, by rfl⟩) R383129
theorem R517565 : Reach 517565 := rs (se 3 (by rfl) ⟨97043, by rfl⟩) R194087
theorem R91643 : Reach 91643 := rs (se 1 (by rfl) ⟨68732, by rfl⟩) R137465
theorem R91711 : Reach 91711 := rs (se 1 (by rfl) ⟨68783, by rfl⟩) R137567
theorem R91719 : Reach 91719 := rs (se 1 (by rfl) ⟨68789, by rfl⟩) R137579
theorem R91871 : Reach 91871 := rs (se 1 (by rfl) ⟨68903, by rfl⟩) R137807
theorem R91951 : Reach 91951 := rs (se 1 (by rfl) ⟨68963, by rfl⟩) R137927
theorem R92059 : Reach 92059 := rs (se 1 (by rfl) ⟨69044, by rfl⟩) R138089
theorem R92111 : Reach 92111 := rs (se 1 (by rfl) ⟨69083, by rfl⟩) R138167
theorem R92135 : Reach 92135 := rs (se 1 (by rfl) ⟨69101, by rfl⟩) R138203
theorem R124903 : Reach 124903 := rs (se 1 (by rfl) ⟨93677, by rfl⟩) R187355
theorem R223241 : Reach 223241 := rs (se 2 (by rfl) ⟨83715, by rfl⟩) R167431
theorem R452641 : Reach 452641 := rs (se 2 (by rfl) ⟨169740, by rfl⟩) R339481
theorem R157801 : Reach 157801 := rs (se 2 (by rfl) ⟨59175, by rfl⟩) R118351
theorem R92447 : Reach 92447 := rs (se 1 (by rfl) ⟨69335, by rfl⟩) R138671
theorem R92507 : Reach 92507 := rs (se 1 (by rfl) ⟨69380, by rfl⟩) R138761
theorem R190811 : Reach 190811 := rs (se 1 (by rfl) ⟨143108, by rfl⟩) R286217
theorem R92527 : Reach 92527 := rs (se 1 (by rfl) ⟨69395, by rfl⟩) R138791
theorem R92583 : Reach 92583 := rs (se 1 (by rfl) ⟨69437, by rfl⟩) R138875
theorem R92667 : Reach 92667 := rs (se 1 (by rfl) ⟨69500, by rfl⟩) R139001
theorem R92735 : Reach 92735 := rs (se 1 (by rfl) ⟨69551, by rfl⟩) R139103
theorem R92743 : Reach 92743 := rs (se 1 (by rfl) ⟨69557, by rfl⟩) R139115
theorem R92895 : Reach 92895 := rs (se 1 (by rfl) ⟨69671, by rfl⟩) R139343
theorem R92975 : Reach 92975 := rs (se 1 (by rfl) ⟨69731, by rfl⟩) R139463
theorem R93083 : Reach 93083 := rs (se 1 (by rfl) ⟨69812, by rfl⟩) R139625
theorem R93135 : Reach 93135 := rs (se 1 (by rfl) ⟨69851, by rfl⟩) R139703
theorem R93159 : Reach 93159 := rs (se 1 (by rfl) ⟨69869, by rfl⟩) R139739
theorem R453899 : Reach 453899 := rs (se 1 (by rfl) ⟨340424, by rfl⟩) R680849
theorem R93471 : Reach 93471 := rs (se 1 (by rfl) ⟨70103, by rfl⟩) R140207
theorem R93531 : Reach 93531 := rs (se 1 (by rfl) ⟨70148, by rfl⟩) R140297
theorem R93551 : Reach 93551 := rs (se 1 (by rfl) ⟨70163, by rfl⟩) R140327
theorem R1600883 : Reach 1600883 := rs (se 1 (by rfl) ⟨1200662, by rfl⟩) R2401325
theorem R224635 : Reach 224635 := rs (se 1 (by rfl) ⟨168476, by rfl⟩) R336953
theorem R93607 : Reach 93607 := rs (se 1 (by rfl) ⟨70205, by rfl⟩) R140411
theorem R159175 : Reach 159175 := rs (se 1 (by rfl) ⟨119381, by rfl⟩) R238763
theorem R93691 : Reach 93691 := rs (se 1 (by rfl) ⟨70268, by rfl⟩) R140537
theorem R93759 : Reach 93759 := rs (se 1 (by rfl) ⟨70319, by rfl⟩) R140639
theorem R93767 : Reach 93767 := rs (se 1 (by rfl) ⟨70325, by rfl⟩) R140651
theorem R323155 : Reach 323155 := rs (se 1 (by rfl) ⟨242366, by rfl⟩) R484733
theorem R913069 : Reach 913069 := rs (se 3 (by rfl) ⟨171200, by rfl⟩) R342401
theorem R93919 : Reach 93919 := rs (se 1 (by rfl) ⟨70439, by rfl⟩) R140879
theorem R159529 : Reach 159529 := rs (se 2 (by rfl) ⟨59823, by rfl⟩) R119647
theorem R93999 : Reach 93999 := rs (se 1 (by rfl) ⟨70499, by rfl⟩) R140999
theorem R94107 : Reach 94107 := rs (se 1 (by rfl) ⟨70580, by rfl⟩) R141161
theorem R94159 : Reach 94159 := rs (se 1 (by rfl) ⟨70619, by rfl⟩) R141239
theorem R94183 : Reach 94183 := rs (se 1 (by rfl) ⟨70637, by rfl⟩) R141275
theorem R94495 : Reach 94495 := rs (se 1 (by rfl) ⟨70871, by rfl⟩) R141743
theorem R94555 : Reach 94555 := rs (se 1 (by rfl) ⟨70916, by rfl⟩) R141833
theorem R94575 : Reach 94575 := rs (se 1 (by rfl) ⟨70931, by rfl⟩) R141863
theorem R225703 : Reach 225703 := rs (se 1 (by rfl) ⟨169277, by rfl⟩) R338555
theorem R94631 : Reach 94631 := rs (se 1 (by rfl) ⟨70973, by rfl⟩) R141947
theorem R520667 : Reach 520667 := rs (se 1 (by rfl) ⟨390500, by rfl⟩) R781001
theorem R94715 : Reach 94715 := rs (se 1 (by rfl) ⟨71036, by rfl⟩) R142073
theorem R94783 : Reach 94783 := rs (se 1 (by rfl) ⟨71087, by rfl⟩) R142175
theorem R160319 : Reach 160319 := rs (se 1 (by rfl) ⟨120239, by rfl⟩) R240479
theorem R94791 : Reach 94791 := rs (se 1 (by rfl) ⟨71093, by rfl⟩) R142187
theorem R94943 : Reach 94943 := rs (se 1 (by rfl) ⟨71207, by rfl⟩) R142415
theorem R95023 : Reach 95023 := rs (se 1 (by rfl) ⟨71267, by rfl⟩) R142535
theorem R128233 : Reach 128233 := rs (se 2 (by rfl) ⟨48087, by rfl⟩) R96175
theorem R947495 : Reach 947495 := rs (se 1 (by rfl) ⟨710621, by rfl⟩) R1421243
theorem R685351 : Reach 685351 := rs (se 1 (by rfl) ⟨514013, by rfl⟩) R1028027
theorem R390689 : Reach 390689 := rs (se 2 (by rfl) ⟨146508, by rfl⟩) R293017
theorem R161543 : Reach 161543 := rs (se 1 (by rfl) ⟨121157, by rfl⟩) R242315
theorem R784313 : Reach 784313 := rs (se 2 (by rfl) ⟨294117, by rfl⟩) R588235
theorem R5142629 : Reach 5142629 := rs (se 4 (by rfl) ⟨482121, by rfl⟩) R964243
theorem R424217 : Reach 424217 := rs (se 2 (by rfl) ⟨159081, by rfl⟩) R318163
theorem R2587085 : Reach 2587085 := rs (se 3 (by rfl) ⟨485078, by rfl⟩) R970157
theorem R1112939 : Reach 1112939 := rs (se 1 (by rfl) ⟨834704, by rfl⟩) R1669409
theorem R851267 : Reach 851267 := rs (se 1 (by rfl) ⟨638450, by rfl⟩) R1276901
theorem R359747 : Reach 359747 := rs (se 1 (by rfl) ⟨269810, by rfl⟩) R539621
theorem R261575 : Reach 261575 := rs (se 1 (by rfl) ⟨196181, by rfl⟩) R392363
theorem R97967 : Reach 97967 := rs (se 1 (by rfl) ⟨73475, by rfl⟩) R146951
theorem R360233 : Reach 360233 := rs (se 2 (by rfl) ⟨135087, by rfl⟩) R270175
theorem R294785 : Reach 294785 := rs (se 2 (by rfl) ⟨110544, by rfl⟩) R221089
theorem R1048627 : Reach 1048627 := rs (se 1 (by rfl) ⟨786470, by rfl⟩) R1572941
theorem R3080699 : Reach 3080699 := rs (se 1 (by rfl) ⟨2310524, by rfl⟩) R4621049
theorem R164513 : Reach 164513 := rs (se 2 (by rfl) ⟨61692, by rfl⟩) R123385
theorem R131881 : Reach 131881 := rs (se 2 (by rfl) ⟨49455, by rfl⟩) R98911
theorem R263375 : Reach 263375 := rs (se 1 (by rfl) ⟨197531, by rfl⟩) R395063
theorem R329131 : Reach 329131 := rs (se 1 (by rfl) ⟨246848, by rfl⟩) R493697
theorem R198163 : Reach 198163 := rs (se 1 (by rfl) ⟨148622, by rfl⟩) R297245
theorem R329383 : Reach 329383 := rs (se 1 (by rfl) ⟨247037, by rfl⟩) R494075
theorem R231943 : Reach 231943 := rs (se 1 (by rfl) ⟨173957, by rfl⟩) R347915
theorem R264809 : Reach 264809 := rs (se 2 (by rfl) ⟨99303, by rfl⟩) R198607
theorem R166537 : Reach 166537 := rs (se 2 (by rfl) ⟨62451, by rfl⟩) R124903
theorem R2427569 : Reach 2427569 := rs (se 2 (by rfl) ⟨910338, by rfl⟩) R1820677
theorem R232247 : Reach 232247 := rs (se 1 (by rfl) ⟨174185, by rfl⟩) R348371
theorem R2919235 : Reach 2919235 := rs (se 1 (by rfl) ⟨2189426, by rfl⟩) R4378853
theorem R494423 : Reach 494423 := rs (se 1 (by rfl) ⟨370817, by rfl⟩) R741635
theorem R462023 : Reach 462023 := rs (se 1 (by rfl) ⟨346517, by rfl⟩) R693035
theorem R396667 : Reach 396667 := rs (se 1 (by rfl) ⟨297500, by rfl⟩) R595001
theorem R134569 : Reach 134569 := rs (se 2 (by rfl) ⟨50463, by rfl⟩) R100927
theorem R2526653 : Reach 2526653 := rs (se 3 (by rfl) ⟨473747, by rfl⟩) R947495
theorem R265801 : Reach 265801 := rs (se 2 (by rfl) ⟨99675, by rfl⟩) R199351
theorem R265835 : Reach 265835 := rs (se 1 (by rfl) ⟨199376, by rfl⟩) R398753
theorem R134831 : Reach 134831 := rs (se 1 (by rfl) ⟨101123, by rfl⟩) R202247
theorem R134951 : Reach 134951 := rs (se 1 (by rfl) ⟨101213, by rfl⟩) R202427
theorem R102631 : Reach 102631 := rs (se 1 (by rfl) ⟨76973, by rfl⟩) R153947
theorem R1184215 : Reach 1184215 := rs (se 1 (by rfl) ⟨888161, by rfl⟩) R1776323
theorem R463319 : Reach 463319 := rs (se 1 (by rfl) ⟨347489, by rfl⟩) R694979
theorem R299513 : Reach 299513 := rs (se 2 (by rfl) ⟨112317, by rfl⟩) R224635
theorem R332383 : Reach 332383 := rs (se 1 (by rfl) ⟨249287, by rfl⟩) R498575
theorem R103279 : Reach 103279 := rs (se 1 (by rfl) ⟨77459, by rfl⟩) R154919
theorem R168815 : Reach 168815 := rs (se 1 (by rfl) ⟨126611, by rfl⟩) R253223
theorem R267133 : Reach 267133 := rs (se 3 (by rfl) ⟨50087, by rfl⟩) R100175
theorem R1217425 : Reach 1217425 := rs (se 2 (by rfl) ⟨456534, by rfl⟩) R913069
theorem R267259 : Reach 267259 := rs (se 1 (by rfl) ⟨200444, by rfl⟩) R400889
theorem R529415 : Reach 529415 := rs (se 1 (by rfl) ⟨397061, by rfl⟩) R794123
theorem R398375 : Reach 398375 := rs (se 1 (by rfl) ⟨298781, by rfl⟩) R597563
theorem R267475 : Reach 267475 := rs (se 1 (by rfl) ⟨200606, by rfl⟩) R401213
theorem R595309 : Reach 595309 := rs (se 3 (by rfl) ⟨111620, by rfl⟩) R223241
theorem R136775 : Reach 136775 := rs (se 1 (by rfl) ⟨102581, by rfl⟩) R205163
theorem R136871 : Reach 136871 := rs (se 1 (by rfl) ⟨102653, by rfl⟩) R205307
theorem R136955 : Reach 136955 := rs (se 1 (by rfl) ⟨102716, by rfl⟩) R205433
theorem R136991 : Reach 136991 := rs (se 1 (by rfl) ⟨102743, by rfl⟩) R205487
theorem R137039 : Reach 137039 := rs (se 1 (by rfl) ⟨102779, by rfl⟩) R205559
theorem R300937 : Reach 300937 := rs (se 2 (by rfl) ⟨112851, by rfl⟩) R225703
theorem R137159 : Reach 137159 := rs (se 1 (by rfl) ⟨102869, by rfl⟩) R205739
theorem R104431 : Reach 104431 := rs (se 1 (by rfl) ⟨78323, by rfl⟩) R156647
theorem R202913 : Reach 202913 := rs (se 2 (by rfl) ⟨76092, by rfl⟩) R152185
theorem R170279 : Reach 170279 := rs (se 1 (by rfl) ⟨127709, by rfl⟩) R255419
theorem R137513 : Reach 137513 := rs (se 2 (by rfl) ⟨51567, by rfl⟩) R103135
theorem R530729 : Reach 530729 := rs (se 2 (by rfl) ⟨199023, by rfl⟩) R398047
theorem R137519 : Reach 137519 := rs (se 1 (by rfl) ⟨103139, by rfl⟩) R206279
theorem R4069757 : Reach 4069757 := rs (se 3 (by rfl) ⟨763079, by rfl⟩) R1526159
theorem R793061 : Reach 793061 := rs (se 4 (by rfl) ⟨74349, by rfl⟩) R148699
theorem R137759 : Reach 137759 := rs (se 1 (by rfl) ⟨103319, by rfl⟩) R206639
theorem R531305 : Reach 531305 := rs (se 2 (by rfl) ⟨199239, by rfl⟩) R398479
theorem R138143 : Reach 138143 := rs (se 1 (by rfl) ⟨103607, by rfl⟩) R207215
theorem R138191 : Reach 138191 := rs (se 1 (by rfl) ⟨103643, by rfl⟩) R207287
theorem R465911 : Reach 465911 := rs (se 1 (by rfl) ⟨349433, by rfl⟩) R698867
theorem R138281 : Reach 138281 := rs (se 2 (by rfl) ⟨51855, by rfl⟩) R103711
theorem R138287 : Reach 138287 := rs (se 1 (by rfl) ⟨103715, by rfl⟩) R207431
theorem R138311 : Reach 138311 := rs (se 1 (by rfl) ⟨103733, by rfl⟩) R207467
theorem R334919 : Reach 334919 := rs (se 1 (by rfl) ⟨251189, by rfl⟩) R502379
theorem R138575 : Reach 138575 := rs (se 1 (by rfl) ⟨103931, by rfl⟩) R207863
theorem R990575 : Reach 990575 := rs (se 1 (by rfl) ⟨742931, by rfl⟩) R1485863
theorem R138665 : Reach 138665 := rs (se 2 (by rfl) ⟨51999, by rfl⟩) R103999
theorem R302599 : Reach 302599 := rs (se 1 (by rfl) ⟨226949, by rfl⟩) R453899
theorem R138815 : Reach 138815 := rs (se 1 (by rfl) ⟨104111, by rfl⟩) R208223
theorem R270049 : Reach 270049 := rs (se 2 (by rfl) ⟨101268, by rfl⟩) R202537
theorem R237289 : Reach 237289 := rs (se 2 (by rfl) ⟨88983, by rfl⟩) R177967
theorem R139079 : Reach 139079 := rs (se 1 (by rfl) ⟨104309, by rfl⟩) R208619
theorem R139163 : Reach 139163 := rs (se 1 (by rfl) ⟨104372, by rfl⟩) R208745
theorem R106879 : Reach 106879 := rs (se 1 (by rfl) ⟨80159, by rfl⟩) R160319
theorem R139727 : Reach 139727 := rs (se 1 (by rfl) ⟨104795, by rfl⟩) R209591
theorem R205289 : Reach 205289 := rs (se 2 (by rfl) ⟨76983, by rfl⟩) R153967
theorem R139769 : Reach 139769 := rs (se 2 (by rfl) ⟨52413, by rfl⟩) R104827
theorem R598547 : Reach 598547 := rs (se 1 (by rfl) ⟨448910, by rfl⟩) R897821
theorem R139871 : Reach 139871 := rs (se 1 (by rfl) ⟨104903, by rfl⟩) R209807
theorem R205577 : Reach 205577 := rs (se 2 (by rfl) ⟨77091, by rfl⟩) R154183
theorem R2040653 : Reach 2040653 := rs (se 3 (by rfl) ⟨382622, by rfl⟩) R765245
theorem R2270045 : Reach 2270045 := rs (se 3 (by rfl) ⟨425633, by rfl⟩) R851267
theorem R140351 : Reach 140351 := rs (se 1 (by rfl) ⟨105263, by rfl⟩) R210527
theorem R140393 : Reach 140393 := rs (se 2 (by rfl) ⟨52647, by rfl⟩) R105295
theorem R238697 : Reach 238697 := rs (se 2 (by rfl) ⟨89511, by rfl⟩) R179023
theorem R107695 : Reach 107695 := rs (se 1 (by rfl) ⟨80771, by rfl⟩) R161543
theorem R140495 : Reach 140495 := rs (se 1 (by rfl) ⟨105371, by rfl⟩) R210743
theorem R206153 : Reach 206153 := rs (se 2 (by rfl) ⟨77307, by rfl⟩) R154615
theorem R664969 : Reach 664969 := rs (se 2 (by rfl) ⟨249363, by rfl⟩) R498727
theorem R140699 : Reach 140699 := rs (se 1 (by rfl) ⟨105524, by rfl⟩) R211049
theorem R370169 : Reach 370169 := rs (se 2 (by rfl) ⟨138813, by rfl⟩) R277627
theorem R140921 : Reach 140921 := rs (se 2 (by rfl) ⟨52845, by rfl⟩) R105691
theorem R141023 : Reach 141023 := rs (se 1 (by rfl) ⟨105767, by rfl⟩) R211535
theorem R141119 : Reach 141119 := rs (se 1 (by rfl) ⟨105839, by rfl⟩) R211679
theorem R1845125 : Reach 1845125 := rs (se 4 (by rfl) ⟨172980, by rfl⟩) R345961
theorem R141287 : Reach 141287 := rs (se 1 (by rfl) ⟨105965, by rfl⟩) R211931
theorem R141305 : Reach 141305 := rs (se 2 (by rfl) ⟨52989, by rfl⟩) R105979
theorem R141407 : Reach 141407 := rs (se 1 (by rfl) ⟨106055, by rfl⟩) R212111
theorem R141467 : Reach 141467 := rs (se 1 (by rfl) ⟨106100, by rfl⟩) R212201
theorem R141503 : Reach 141503 := rs (se 1 (by rfl) ⟨106127, by rfl⟩) R212255
theorem R239831 : Reach 239831 := rs (se 1 (by rfl) ⟨179873, by rfl⟩) R359747
theorem R141545 : Reach 141545 := rs (se 2 (by rfl) ⟨53079, by rfl⟩) R106159
theorem R207143 : Reach 207143 := rs (se 1 (by rfl) ⟨155357, by rfl⟩) R310715
theorem R174383 : Reach 174383 := rs (se 1 (by rfl) ⟨130787, by rfl⟩) R261575
theorem R207161 : Reach 207161 := rs (se 2 (by rfl) ⟨77685, by rfl⟩) R155371
theorem R141851 : Reach 141851 := rs (se 1 (by rfl) ⟨106388, by rfl⟩) R212777
theorem R240155 : Reach 240155 := rs (se 1 (by rfl) ⟨180116, by rfl⟩) R360233
theorem R141929 : Reach 141929 := rs (se 2 (by rfl) ⟨53223, by rfl⟩) R106447
theorem R404459 : Reach 404459 := rs (se 1 (by rfl) ⟨303344, by rfl⟩) R606689
theorem R207919 : Reach 207919 := rs (se 1 (by rfl) ⟨155939, by rfl⟩) R311879
theorem R404527 : Reach 404527 := rs (se 1 (by rfl) ⟨303395, by rfl⟩) R606791
theorem R142457 : Reach 142457 := rs (se 2 (by rfl) ⟨53421, by rfl⟩) R106843
theorem R142559 : Reach 142559 := rs (se 1 (by rfl) ⟨106919, by rfl⟩) R213839
theorem R339187 : Reach 339187 := rs (se 1 (by rfl) ⟨254390, by rfl⟩) R508781
theorem R142601 : Reach 142601 := rs (se 2 (by rfl) ⟨53475, by rfl⟩) R106951
theorem R863531 : Reach 863531 := rs (se 1 (by rfl) ⟨647648, by rfl⟩) R1295297
theorem R175439 : Reach 175439 := rs (se 1 (by rfl) ⟨131579, by rfl⟩) R263159
theorem R208457 : Reach 208457 := rs (se 2 (by rfl) ⟨78171, by rfl⟩) R156343
theorem R536179 : Reach 536179 := rs (se 1 (by rfl) ⟨402134, by rfl⟩) R804269
theorem R667531 : Reach 667531 := rs (se 1 (by rfl) ⟨500648, by rfl⟩) R1001297
theorem R536705 : Reach 536705 := rs (se 2 (by rfl) ⟨201264, by rfl⟩) R402529
theorem R1028285 : Reach 1028285 := rs (se 3 (by rfl) ⟨192803, by rfl⟩) R385607
theorem R307583 : Reach 307583 := rs (se 1 (by rfl) ⟨230687, by rfl⟩) R461375
theorem R209915 : Reach 209915 := rs (se 1 (by rfl) ⟨157436, by rfl⟩) R314873
theorem R537637 : Reach 537637 := rs (se 4 (by rfl) ⟨50403, by rfl⟩) R100807
theorem R210095 : Reach 210095 := rs (se 1 (by rfl) ⟨157571, by rfl⟩) R315143
theorem R2700485 : Reach 2700485 := rs (se 4 (by rfl) ⟨253170, by rfl⟩) R506341
theorem R210131 : Reach 210131 := rs (se 1 (by rfl) ⟨157598, by rfl⟩) R315197
theorem R668915 : Reach 668915 := rs (se 1 (by rfl) ⟨501686, by rfl⟩) R1003373
theorem R603521 : Reach 603521 := rs (se 2 (by rfl) ⟨226320, by rfl⟩) R452641
theorem R210401 : Reach 210401 := rs (se 2 (by rfl) ⟨78900, by rfl⟩) R157801
theorem R636599 : Reach 636599 := rs (se 1 (by rfl) ⟨477449, by rfl⟩) R954899
theorem R571115 : Reach 571115 := rs (se 1 (by rfl) ⟨428336, by rfl⟩) R856673
theorem R308987 : Reach 308987 := rs (se 1 (by rfl) ⟨231740, by rfl⟩) R463481
theorem R112447 : Reach 112447 := rs (se 1 (by rfl) ⟨84335, by rfl⟩) R168671
theorem R309149 : Reach 309149 := rs (se 3 (by rfl) ⟨57965, by rfl⟩) R115931
theorem R178271 : Reach 178271 := rs (se 1 (by rfl) ⟨133703, by rfl⟩) R267407
theorem R1620101 : Reach 1620101 := rs (se 4 (by rfl) ⟨151884, by rfl⟩) R303769
theorem R604331 : Reach 604331 := rs (se 1 (by rfl) ⟨453248, by rfl⟩) R906497
theorem R997667 : Reach 997667 := rs (se 1 (by rfl) ⟨748250, by rfl⟩) R1496501
theorem R604691 : Reach 604691 := rs (se 1 (by rfl) ⟨453518, by rfl⟩) R907037
theorem R899857 : Reach 899857 := rs (se 2 (by rfl) ⟨337446, by rfl⟩) R674893
theorem R179027 : Reach 179027 := rs (se 1 (by rfl) ⟨134270, by rfl⟩) R268541
theorem R310121 : Reach 310121 := rs (se 2 (by rfl) ⟨116295, by rfl⟩) R232591
theorem R310175 : Reach 310175 := rs (se 1 (by rfl) ⟨232631, by rfl⟩) R465263
theorem R212039 : Reach 212039 := rs (se 1 (by rfl) ⟨159029, by rfl⟩) R318059
theorem R212435 : Reach 212435 := rs (se 1 (by rfl) ⟨159326, by rfl⟩) R318653
theorem R212705 : Reach 212705 := rs (se 2 (by rfl) ⟨79764, by rfl⟩) R159529
theorem R180139 : Reach 180139 := rs (se 1 (by rfl) ⟨135104, by rfl⟩) R270209
theorem R180443 : Reach 180443 := rs (se 1 (by rfl) ⟨135332, by rfl⟩) R270665
theorem R10175291 : Reach 10175291 := rs (se 1 (by rfl) ⟨7631468, by rfl⟩) R15262937
theorem R345043 : Reach 345043 := rs (se 1 (by rfl) ⟨258782, by rfl⟩) R517565
theorem R902249 : Reach 902249 := rs (se 2 (by rfl) ⟨338343, by rfl⟩) R676687
theorem R312443 : Reach 312443 := rs (se 1 (by rfl) ⟨234332, by rfl⟩) R468665
theorem R312713 : Reach 312713 := rs (se 2 (by rfl) ⟨117267, by rfl⟩) R234535
theorem R313469 : Reach 313469 := rs (se 3 (by rfl) ⟨58775, by rfl⟩) R117551
theorem R1067255 : Reach 1067255 := rs (se 1 (by rfl) ⟨800441, by rfl⟩) R1600883
theorem R313739 : Reach 313739 := rs (se 1 (by rfl) ⟨235304, by rfl⟩) R470609
theorem R641681 : Reach 641681 := rs (se 2 (by rfl) ⟨240630, by rfl⟩) R481261
theorem R347111 : Reach 347111 := rs (se 1 (by rfl) ⟨260333, by rfl⟩) R520667
theorem R117739 : Reach 117739 := rs (se 1 (by rfl) ⟨88304, by rfl⟩) R176609
theorem R1723493 : Reach 1723493 := rs (se 4 (by rfl) ⟨161577, by rfl⟩) R323155
theorem R1756403 : Reach 1756403 := rs (se 1 (by rfl) ⟨1317302, by rfl⟩) R2634605
theorem R249743 : Reach 249743 := rs (se 1 (by rfl) ⟨187307, by rfl⟩) R374615
theorem R315359 : Reach 315359 := rs (se 1 (by rfl) ⟨236519, by rfl⟩) R473039
theorem R1364035 : Reach 1364035 := rs (se 1 (by rfl) ⟨1023026, by rfl⟩) R2046053
theorem R3428419 : Reach 3428419 := rs (se 1 (by rfl) ⟨2571314, by rfl⟩) R5142629
theorem R249979 : Reach 249979 := rs (se 1 (by rfl) ⟨187484, by rfl⟩) R374969
theorem R315521 : Reach 315521 := rs (se 2 (by rfl) ⟨118320, by rfl⟩) R236641
theorem R282811 : Reach 282811 := rs (se 1 (by rfl) ⟨212108, by rfl⟩) R424217
theorem R1724723 : Reach 1724723 := rs (se 1 (by rfl) ⟨1293542, by rfl⟩) R2587085
theorem R315863 : Reach 315863 := rs (se 1 (by rfl) ⟨236897, by rfl⟩) R473795
theorem R152057 : Reach 152057 := rs (se 2 (by rfl) ⟨57021, by rfl⟩) R114043
theorem R741959 : Reach 741959 := rs (se 1 (by rfl) ⟨556469, by rfl⟩) R1112939
theorem R316007 : Reach 316007 := rs (se 1 (by rfl) ⟨237005, by rfl⟩) R474011
theorem R316331 : Reach 316331 := rs (se 1 (by rfl) ⟨237248, by rfl⟩) R474497
theorem R382171 : Reach 382171 := rs (se 1 (by rfl) ⟨286628, by rfl⟩) R573257
theorem R513323 : Reach 513323 := rs (se 1 (by rfl) ⟨384992, by rfl⟩) R769985
theorem R316763 : Reach 316763 := rs (se 1 (by rfl) ⟨237572, by rfl⟩) R475145
theorem R316871 : Reach 316871 := rs (se 1 (by rfl) ⟨237653, by rfl⟩) R475307
theorem R7722503 : Reach 7722503 := rs (se 1 (by rfl) ⟨5791877, by rfl⟩) R11583755
theorem R317195 : Reach 317195 := rs (se 1 (by rfl) ⟨237896, by rfl⟩) R475793
theorem R317465 : Reach 317465 := rs (se 2 (by rfl) ⟨119049, by rfl⟩) R238099
theorem R841927 : Reach 841927 := rs (se 1 (by rfl) ⟨631445, by rfl⟩) R1262891
theorem R153913 : Reach 153913 := rs (se 2 (by rfl) ⟨57717, by rfl⟩) R115435
theorem R154217 : Reach 154217 := rs (se 2 (by rfl) ⟨57831, by rfl⟩) R115663
theorem R351485 : Reach 351485 := rs (se 3 (by rfl) ⟨65903, by rfl⟩) R131807
theorem R318815 : Reach 318815 := rs (se 1 (by rfl) ⟨239111, by rfl⟩) R478223
theorem R155047 : Reach 155047 := rs (se 1 (by rfl) ⟨116285, by rfl⟩) R232571
theorem R155209 : Reach 155209 := rs (se 2 (by rfl) ⟨58203, by rfl⟩) R116407
theorem R155243 : Reach 155243 := rs (se 1 (by rfl) ⟨116432, by rfl⟩) R232865
theorem R155513 : Reach 155513 := rs (se 2 (by rfl) ⟨58317, by rfl⟩) R116635
theorem R319355 : Reach 319355 := rs (se 1 (by rfl) ⟨239516, by rfl⟩) R479033
theorem R1007873 : Reach 1007873 := rs (se 2 (by rfl) ⟨377952, by rfl⟩) R755905
theorem R319841 : Reach 319841 := rs (se 2 (by rfl) ⟨119940, by rfl⟩) R239881
theorem R352745 : Reach 352745 := rs (se 2 (by rfl) ⟨132279, by rfl⟩) R264559
theorem R91131 : Reach 91131 := rs (se 1 (by rfl) ⟨68348, by rfl⟩) R136697
theorem R156667 : Reach 156667 := rs (se 1 (by rfl) ⟨117500, by rfl⟩) R235001
theorem R1303595 : Reach 1303595 := rs (se 1 (by rfl) ⟨977696, by rfl⟩) R1955393
theorem R91199 : Reach 91199 := rs (se 1 (by rfl) ⟨68399, by rfl⟩) R136799
theorem R91343 : Reach 91343 := rs (se 1 (by rfl) ⟨68507, by rfl⟩) R137015
theorem R288137 : Reach 288137 := rs (se 2 (by rfl) ⟨108051, by rfl⟩) R216103
theorem R91547 : Reach 91547 := rs (se 1 (by rfl) ⟨68660, by rfl⟩) R137321
theorem R157099 : Reach 157099 := rs (se 1 (by rfl) ⟨117824, by rfl⟩) R235649
theorem R1893851 : Reach 1893851 := rs (se 1 (by rfl) ⟨1420388, by rfl⟩) R2840777
theorem R91759 : Reach 91759 := rs (se 1 (by rfl) ⟨68819, by rfl⟩) R137639
theorem R157295 : Reach 157295 := rs (se 1 (by rfl) ⟨117971, by rfl⟩) R235943
theorem R91815 : Reach 91815 := rs (se 1 (by rfl) ⟨68861, by rfl⟩) R137723
theorem R222887 : Reach 222887 := rs (se 1 (by rfl) ⟨167165, by rfl⟩) R334331
theorem R157403 : Reach 157403 := rs (se 1 (by rfl) ⟨118052, by rfl⟩) R236105
theorem R91899 : Reach 91899 := rs (se 1 (by rfl) ⟨68924, by rfl⟩) R137849
theorem R91935 : Reach 91935 := rs (se 1 (by rfl) ⟨68951, by rfl⟩) R137903
theorem R91967 : Reach 91967 := rs (se 1 (by rfl) ⟨68975, by rfl⟩) R137951
theorem R157639 : Reach 157639 := rs (se 1 (by rfl) ⟨118229, by rfl⟩) R236459
theorem R92143 : Reach 92143 := rs (se 1 (by rfl) ⟨69107, by rfl⟩) R138215
theorem R92315 : Reach 92315 := rs (se 1 (by rfl) ⟨69236, by rfl⟩) R138473
theorem R92351 : Reach 92351 := rs (se 1 (by rfl) ⟨69263, by rfl⟩) R138527
theorem R92463 : Reach 92463 := rs (se 1 (by rfl) ⟨69347, by rfl⟩) R138695
theorem R92699 : Reach 92699 := rs (se 1 (by rfl) ⟨69524, by rfl⟩) R139049
theorem R92703 : Reach 92703 := rs (se 1 (by rfl) ⟨69527, by rfl⟩) R139055
theorem R354887 : Reach 354887 := rs (se 1 (by rfl) ⟨266165, by rfl⟩) R532331
theorem R1632869 : Reach 1632869 := rs (se 4 (by rfl) ⟨153081, by rfl⟩) R306163
theorem R4057775 : Reach 4057775 := rs (se 1 (by rfl) ⟨3043331, by rfl⟩) R6086663
theorem R158395 : Reach 158395 := rs (se 1 (by rfl) ⟨118796, by rfl⟩) R237593
theorem R93019 : Reach 93019 := rs (se 1 (by rfl) ⟨69764, by rfl⟩) R139529
theorem R93087 : Reach 93087 := rs (se 1 (by rfl) ⟨69815, by rfl⟩) R139631
theorem R158699 : Reach 158699 := rs (se 1 (by rfl) ⟨119024, by rfl⟩) R238049
theorem R93231 : Reach 93231 := rs (se 1 (by rfl) ⟨69923, by rfl⟩) R139847
theorem R93255 : Reach 93255 := rs (se 1 (by rfl) ⟨69941, by rfl⟩) R139883
theorem R93407 : Reach 93407 := rs (se 1 (by rfl) ⟨70055, by rfl⟩) R140111
theorem R1043927 : Reach 1043927 := rs (se 1 (by rfl) ⟨782945, by rfl⟩) R1565891
theorem R93671 : Reach 93671 := rs (se 1 (by rfl) ⟨70253, by rfl⟩) R140507
theorem R93787 : Reach 93787 := rs (se 1 (by rfl) ⟨70340, by rfl⟩) R140681
theorem R94023 : Reach 94023 := rs (se 1 (by rfl) ⟨70517, by rfl⟩) R141035
theorem R683909 : Reach 683909 := rs (se 4 (by rfl) ⟨64116, by rfl⟩) R128233
theorem R94175 : Reach 94175 := rs (se 1 (by rfl) ⟨70631, by rfl⟩) R141263
theorem R127207 : Reach 127207 := rs (se 1 (by rfl) ⟨95405, by rfl⟩) R190811
theorem R94439 : Reach 94439 := rs (se 1 (by rfl) ⟨70829, by rfl⟩) R141659
theorem R356663 : Reach 356663 := rs (se 1 (by rfl) ⟨267497, by rfl⟩) R534995
theorem R94591 : Reach 94591 := rs (se 1 (by rfl) ⟨70943, by rfl⟩) R141887
theorem R913801 : Reach 913801 := rs (se 2 (by rfl) ⟨342675, by rfl⟩) R685351
theorem R94671 : Reach 94671 := rs (se 1 (by rfl) ⟨71003, by rfl⟩) R142007
theorem R94823 : Reach 94823 := rs (se 1 (by rfl) ⟨71117, by rfl⟩) R142235
theorem R95087 : Reach 95087 := rs (se 1 (by rfl) ⟨71315, by rfl⟩) R142631
theorem R324481 : Reach 324481 := rs (se 2 (by rfl) ⟨121680, by rfl⟩) R243361
theorem R848933 : Reach 848933 := rs (se 4 (by rfl) ⟨79587, by rfl⟩) R159175
theorem R1078829 : Reach 1078829 := rs (se 3 (by rfl) ⟨202280, by rfl⟩) R404561
theorem R161531 : Reach 161531 := rs (se 1 (by rfl) ⟨121148, by rfl⟩) R242297
theorem R260459 : Reach 260459 := rs (se 1 (by rfl) ⟨195344, by rfl⟩) R390689
theorem R883055 : Reach 883055 := rs (se 1 (by rfl) ⟨662291, by rfl⟩) R1324583
theorem R522875 : Reach 522875 := rs (se 1 (by rfl) ⟨392156, by rfl⟩) R784313
theorem R261245 : Reach 261245 := rs (se 3 (by rfl) ⟨48983, by rfl⟩) R97967
theorem R196523 : Reach 196523 := rs (se 1 (by rfl) ⟨147392, by rfl⟩) R294785
theorem R6783527 : Reach 6783527 := rs (se 1 (by rfl) ⟨5087645, by rfl⟩) R10175291
theorem R427787 : Reach 427787 := rs (se 1 (by rfl) ⟨320840, by rfl⟩) R641681
theorem R886625 : Reach 886625 := rs (se 2 (by rfl) ⟨332484, by rfl⟩) R664969
theorem R329615 : Reach 329615 := rs (se 1 (by rfl) ⟨247211, by rfl⟩) R494423
theorem R231407 : Reach 231407 := rs (se 1 (by rfl) ⟨173555, by rfl⟩) R347111
theorem R264217 : Reach 264217 := rs (se 2 (by rfl) ⟨99081, by rfl⟩) R198163
theorem R1148995 : Reach 1148995 := rs (se 1 (by rfl) ⟨861746, by rfl⟩) R1723493
theorem R166495 : Reach 166495 := rs (se 1 (by rfl) ⟨124871, by rfl⟩) R249743
theorem R1149815 : Reach 1149815 := rs (se 1 (by rfl) ⟨862361, by rfl⟩) R1724723
theorem R199675 : Reach 199675 := rs (se 1 (by rfl) ⟨149756, by rfl⟩) R299513
theorem R494639 : Reach 494639 := rs (se 1 (by rfl) ⟨370979, by rfl⟩) R741959
theorem R265583 : Reach 265583 := rs (se 1 (by rfl) ⟨199187, by rfl⟩) R398375
theorem R5148335 : Reach 5148335 := rs (se 1 (by rfl) ⟨3861251, by rfl⟩) R7722503
theorem R135275 : Reach 135275 := rs (se 1 (by rfl) ⟨101456, by rfl⟩) R202913
theorem R528707 : Reach 528707 := rs (se 1 (by rfl) ⟨396530, by rfl⟩) R793061
theorem R102811 : Reach 102811 := rs (se 1 (by rfl) ⟨77108, by rfl⟩) R154217
theorem R528889 : Reach 528889 := rs (se 2 (by rfl) ⟨198333, by rfl⟩) R396667
theorem R234323 : Reach 234323 := rs (se 1 (by rfl) ⟨175742, by rfl⟩) R351485
theorem R660383 : Reach 660383 := rs (se 1 (by rfl) ⟨495287, by rfl⟩) R990575
theorem R103495 : Reach 103495 := rs (se 1 (by rfl) ⟨77621, by rfl⟩) R155243
theorem R1840229 : Reach 1840229 := rs (se 4 (by rfl) ⟨172521, by rfl⟩) R345043
theorem R890041 : Reach 890041 := rs (se 2 (by rfl) ⟨333765, by rfl⟩) R667531
theorem R627941 : Reach 627941 := rs (se 4 (by rfl) ⟨58869, by rfl⟩) R117739
theorem R103675 : Reach 103675 := rs (se 1 (by rfl) ⟨77756, by rfl⟩) R155513
theorem R333305 : Reach 333305 := rs (se 2 (by rfl) ⟨124989, by rfl⟩) R249979
theorem R136841 : Reach 136841 := rs (se 2 (by rfl) ⟨51315, by rfl⟩) R102631
theorem R169609 : Reach 169609 := rs (se 2 (by rfl) ⟨63603, by rfl⟩) R127207
theorem R136859 : Reach 136859 := rs (se 1 (by rfl) ⟨102644, by rfl⟩) R205289
theorem R235163 : Reach 235163 := rs (se 1 (by rfl) ⟨176372, by rfl⟩) R352745
theorem R137051 : Reach 137051 := rs (se 1 (by rfl) ⟨102788, by rfl⟩) R205577
theorem R1218401 : Reach 1218401 := rs (se 2 (by rfl) ⟨456900, by rfl⟩) R913801
theorem R1513363 : Reach 1513363 := rs (se 1 (by rfl) ⟨1135022, by rfl⟩) R2270045
theorem R1578953 : Reach 1578953 := rs (se 2 (by rfl) ⟨592107, by rfl⟩) R1184215
theorem R137435 : Reach 137435 := rs (se 1 (by rfl) ⟨103076, by rfl⟩) R206153
theorem R104863 : Reach 104863 := rs (se 1 (by rfl) ⟨78647, by rfl⟩) R157295
theorem R104935 : Reach 104935 := rs (se 1 (by rfl) ⟨78701, by rfl⟩) R157403
theorem R137705 : Reach 137705 := rs (se 2 (by rfl) ⟨51639, by rfl⟩) R103279
theorem R432641 : Reach 432641 := rs (se 2 (by rfl) ⟨162240, by rfl⟩) R324481
theorem R138095 : Reach 138095 := rs (se 1 (by rfl) ⟨103571, by rfl⟩) R207143
theorem R138107 : Reach 138107 := rs (se 1 (by rfl) ⟨103580, by rfl⟩) R207161
theorem R236591 : Reach 236591 := rs (se 1 (by rfl) ⟨177443, by rfl⟩) R354887
theorem R1088579 : Reach 1088579 := rs (se 1 (by rfl) ⟨816434, by rfl⟩) R1632869
theorem R793745 : Reach 793745 := rs (se 2 (by rfl) ⟨297654, by rfl⟩) R595309
theorem R105799 : Reach 105799 := rs (se 1 (by rfl) ⟨79349, by rfl⟩) R158699
theorem R269639 : Reach 269639 := rs (se 1 (by rfl) ⟨202229, by rfl⟩) R404459
theorem R695951 : Reach 695951 := rs (se 1 (by rfl) ⟨521963, by rfl⟩) R1043927
theorem R138971 : Reach 138971 := rs (se 1 (by rfl) ⟨104228, by rfl⟩) R208457
theorem R401249 : Reach 401249 := rs (se 2 (by rfl) ⟨150468, by rfl⟩) R300937
theorem R139241 : Reach 139241 := rs (se 2 (by rfl) ⟨52215, by rfl⟩) R104431
theorem R237775 : Reach 237775 := rs (se 1 (by rfl) ⟨178331, by rfl⟩) R356663
theorem R205055 : Reach 205055 := rs (se 1 (by rfl) ⟨153791, by rfl⟩) R307583
theorem R1122569 : Reach 1122569 := rs (se 2 (by rfl) ⟨420963, by rfl⟩) R841927
theorem R205217 : Reach 205217 := rs (se 2 (by rfl) ⟨76956, by rfl⟩) R153913
theorem R139943 : Reach 139943 := rs (se 1 (by rfl) ⟨104957, by rfl⟩) R209915
theorem R565955 : Reach 565955 := rs (se 1 (by rfl) ⟨424466, by rfl⟩) R848933
theorem R140063 : Reach 140063 := rs (se 1 (by rfl) ⟨105047, by rfl⟩) R210095
theorem R140087 : Reach 140087 := rs (se 1 (by rfl) ⟨105065, by rfl⟩) R210131
theorem R402347 : Reach 402347 := rs (se 1 (by rfl) ⟨301760, by rfl⟩) R603521
theorem R140267 : Reach 140267 := rs (se 1 (by rfl) ⟨105200, by rfl⟩) R210401
theorem R205991 : Reach 205991 := rs (se 1 (by rfl) ⟨154493, by rfl⟩) R308987
theorem R107687 : Reach 107687 := rs (se 1 (by rfl) ⟨80765, by rfl⟩) R161531
theorem R206099 : Reach 206099 := rs (se 1 (by rfl) ⟨154574, by rfl⟩) R309149
theorem R402887 : Reach 402887 := rs (se 1 (by rfl) ⟨302165, by rfl⟩) R604331
theorem R665111 : Reach 665111 := rs (se 1 (by rfl) ⟨498833, by rfl⟩) R997667
theorem R173639 : Reach 173639 := rs (se 1 (by rfl) ⟨130229, by rfl⟩) R260459
theorem R599717 : Reach 599717 := rs (se 4 (by rfl) ⟨56223, by rfl⟩) R112447
theorem R403127 : Reach 403127 := rs (se 1 (by rfl) ⟨302345, by rfl⟩) R604691
theorem R206729 : Reach 206729 := rs (se 2 (by rfl) ⟨77523, by rfl⟩) R155047
theorem R206747 : Reach 206747 := rs (se 1 (by rfl) ⟨155060, by rfl⟩) R310121
theorem R206783 : Reach 206783 := rs (se 1 (by rfl) ⟨155087, by rfl⟩) R310175
theorem R403465 : Reach 403465 := rs (se 2 (by rfl) ⟨151299, by rfl⟩) R302599
theorem R141359 : Reach 141359 := rs (se 1 (by rfl) ⟨106019, by rfl⟩) R212039
theorem R174163 : Reach 174163 := rs (se 1 (by rfl) ⟨130622, by rfl⟩) R261245
theorem R206945 : Reach 206945 := rs (se 2 (by rfl) ⟨77604, by rfl⟩) R155209
theorem R141623 : Reach 141623 := rs (se 1 (by rfl) ⟨106217, by rfl⟩) R212435
theorem R141803 : Reach 141803 := rs (se 1 (by rfl) ⟨106352, by rfl⟩) R212705
theorem R240185 : Reach 240185 := rs (se 2 (by rfl) ⟨90069, by rfl⟩) R180139
theorem R109675 : Reach 109675 := rs (se 1 (by rfl) ⟨82256, by rfl⟩) R164513
theorem R142505 : Reach 142505 := rs (se 2 (by rfl) ⟨53439, by rfl⟩) R106879
theorem R601499 : Reach 601499 := rs (se 1 (by rfl) ⟨451124, by rfl⟩) R902249
theorem R208295 : Reach 208295 := rs (se 1 (by rfl) ⟨156221, by rfl⟩) R312443
theorem R175583 : Reach 175583 := rs (se 1 (by rfl) ⟨131687, by rfl⟩) R263375
theorem R208475 : Reach 208475 := rs (se 1 (by rfl) ⟨156356, by rfl⟩) R312713
theorem R175841 : Reach 175841 := rs (se 2 (by rfl) ⟨65940, by rfl⟩) R131881
theorem R405485 : Reach 405485 := rs (se 3 (by rfl) ⟨76028, by rfl⟩) R152057
theorem R208889 : Reach 208889 := rs (se 2 (by rfl) ⟨78333, by rfl⟩) R156667
theorem R208979 : Reach 208979 := rs (se 1 (by rfl) ⟨156734, by rfl⟩) R313469
theorem R209159 : Reach 209159 := rs (se 1 (by rfl) ⟨156869, by rfl⟩) R313739
theorem R1618379 : Reach 1618379 := rs (se 1 (by rfl) ⟨1213784, by rfl⟩) R2427569
theorem R209465 : Reach 209465 := rs (se 2 (by rfl) ⟨78549, by rfl⟩) R157099
theorem R438841 : Reach 438841 := rs (se 2 (by rfl) ⟨164565, by rfl⟩) R329131
theorem R308015 : Reach 308015 := rs (se 1 (by rfl) ⟨231011, by rfl⟩) R462023
theorem R439177 : Reach 439177 := rs (se 2 (by rfl) ⟨164691, by rfl⟩) R329383
theorem R1684435 : Reach 1684435 := rs (se 1 (by rfl) ⟨1263326, by rfl⟩) R2526653
theorem R177223 : Reach 177223 := rs (se 1 (by rfl) ⟨132917, by rfl⟩) R265835
theorem R210185 : Reach 210185 := rs (se 2 (by rfl) ⟨78819, by rfl⟩) R157639
theorem R210239 : Reach 210239 := rs (se 1 (by rfl) ⟨157679, by rfl⟩) R315359
theorem R210347 : Reach 210347 := rs (se 1 (by rfl) ⟨157760, by rfl⟩) R315521
theorem R308879 : Reach 308879 := rs (se 1 (by rfl) ⟨231659, by rfl⟩) R463319
theorem R210575 : Reach 210575 := rs (se 1 (by rfl) ⟨157931, by rfl⟩) R315863
theorem R210671 : Reach 210671 := rs (se 1 (by rfl) ⟨158003, by rfl⟩) R316007
theorem R210887 : Reach 210887 := rs (se 1 (by rfl) ⟨158165, by rfl⟩) R316331
theorem R309257 : Reach 309257 := rs (se 2 (by rfl) ⟨115971, by rfl⟩) R231943
theorem R342215 : Reach 342215 := rs (se 1 (by rfl) ⟨256661, by rfl⟩) R513323
theorem R211175 : Reach 211175 := rs (se 1 (by rfl) ⟨158381, by rfl⟩) R316763
theorem R211193 : Reach 211193 := rs (se 2 (by rfl) ⟨79197, by rfl⟩) R158395
theorem R211247 : Reach 211247 := rs (se 1 (by rfl) ⟨158435, by rfl⟩) R316871
theorem R768365 : Reach 768365 := rs (se 3 (by rfl) ⟨144068, by rfl⟩) R288137
theorem R211463 : Reach 211463 := rs (se 1 (by rfl) ⟨158597, by rfl⟩) R317195
theorem R211643 : Reach 211643 := rs (se 1 (by rfl) ⟨158732, by rfl⟩) R317465
theorem R277225 : Reach 277225 := rs (se 2 (by rfl) ⟨103959, by rfl⟩) R207919
theorem R539369 : Reach 539369 := rs (se 2 (by rfl) ⟨202263, by rfl⟩) R404527
theorem R113519 : Reach 113519 := rs (se 1 (by rfl) ⟨85139, by rfl⟩) R170279
theorem R179425 : Reach 179425 := rs (se 2 (by rfl) ⟨67284, by rfl⟩) R134569
theorem R310607 : Reach 310607 := rs (se 1 (by rfl) ⟨232955, by rfl⟩) R465911
theorem R212543 : Reach 212543 := rs (se 1 (by rfl) ⟨159407, by rfl⟩) R318815
theorem R212903 : Reach 212903 := rs (se 1 (by rfl) ⟨159677, by rfl⟩) R319355
theorem R1818713 : Reach 1818713 := rs (se 2 (by rfl) ⟨682017, by rfl⟩) R1364035
theorem R4571225 : Reach 4571225 := rs (se 2 (by rfl) ⟨1714209, by rfl⟩) R3428419
theorem R671915 : Reach 671915 := rs (se 1 (by rfl) ⟨503936, by rfl⟩) R1007873
theorem R213227 : Reach 213227 := rs (se 1 (by rfl) ⟨159920, by rfl⟩) R319841
theorem R377081 : Reach 377081 := rs (se 2 (by rfl) ⟨141405, by rfl⟩) R282811
theorem R1360435 : Reach 1360435 := rs (se 1 (by rfl) ⟨1020326, by rfl⟩) R2040653
theorem R869063 : Reach 869063 := rs (se 1 (by rfl) ⟨651797, by rfl⟩) R1303595
theorem R443177 : Reach 443177 := rs (se 2 (by rfl) ⟨166191, by rfl⟩) R332383
theorem R574373 : Reach 574373 := rs (se 4 (by rfl) ⟨53847, by rfl⟩) R107695
theorem R1262567 : Reach 1262567 := rs (se 1 (by rfl) ⟨946925, by rfl⟩) R1893851
theorem R246779 : Reach 246779 := rs (se 1 (by rfl) ⟨185084, by rfl⟩) R370169
theorem R148591 : Reach 148591 := rs (se 1 (by rfl) ⟨111443, by rfl⟩) R222887
theorem R1623233 : Reach 1623233 := rs (se 2 (by rfl) ⟨608712, by rfl⟩) R1217425
theorem R1230083 : Reach 1230083 := rs (se 1 (by rfl) ⟨922562, by rfl⟩) R1845125
theorem R116255 : Reach 116255 := rs (se 1 (by rfl) ⟨87191, by rfl⟩) R174383
theorem R706157 : Reach 706157 := rs (se 3 (by rfl) ⟨132404, by rfl⟩) R264809
theorem R509561 : Reach 509561 := rs (se 2 (by rfl) ⟨191085, by rfl⟩) R382171
theorem R2705183 : Reach 2705183 := rs (se 1 (by rfl) ⟨2028887, by rfl⟩) R4057775
theorem R575687 : Reach 575687 := rs (se 1 (by rfl) ⟨431765, by rfl⟩) R863531
theorem R116959 : Reach 116959 := rs (se 1 (by rfl) ⟨87719, by rfl⟩) R175439
theorem R445943 : Reach 445943 := rs (se 1 (by rfl) ⟨334457, by rfl⟩) R668915
theorem R1199809 : Reach 1199809 := rs (se 2 (by rfl) ⟨449928, by rfl⟩) R899857
theorem R380743 : Reach 380743 := rs (se 1 (by rfl) ⟨285557, by rfl⟩) R571115
theorem R118847 : Reach 118847 := rs (se 1 (by rfl) ⟨89135, by rfl⟩) R178271
theorem R348583 : Reach 348583 := rs (se 1 (by rfl) ⟨261437, by rfl⟩) R522875
theorem R119351 : Reach 119351 := rs (se 1 (by rfl) ⟨89513, by rfl⟩) R179027
theorem R316385 : Reach 316385 := rs (se 2 (by rfl) ⟨118644, by rfl⟩) R237289
theorem R1398169 : Reach 1398169 := rs (se 2 (by rfl) ⟨524313, by rfl⟩) R1048627
theorem R120295 : Reach 120295 := rs (se 1 (by rfl) ⟨90221, by rfl⟩) R180443
theorem R2053799 : Reach 2053799 := rs (se 1 (by rfl) ⟨1540349, by rfl⟩) R3080699
theorem R1596125 : Reach 1596125 := rs (se 3 (by rfl) ⟨299273, by rfl⟩) R598547
theorem R711503 : Reach 711503 := rs (se 1 (by rfl) ⟨533627, by rfl⟩) R1067255
theorem R154831 : Reach 154831 := rs (se 1 (by rfl) ⟨116123, by rfl⟩) R232247
theorem R1170935 : Reach 1170935 := rs (se 1 (by rfl) ⟨878201, by rfl⟩) R1756403
theorem R450173 : Reach 450173 := rs (se 3 (by rfl) ⟨84407, by rfl⟩) R168815
theorem R352943 : Reach 352943 := rs (se 1 (by rfl) ⟨264707, by rfl⟩) R529415
theorem R222049 : Reach 222049 := rs (se 2 (by rfl) ⟨83268, by rfl⟩) R166537
theorem R91183 : Reach 91183 := rs (se 1 (by rfl) ⟨68387, by rfl⟩) R136775
theorem R3892313 : Reach 3892313 := rs (se 2 (by rfl) ⟨1459617, by rfl⟩) R2919235
theorem R91247 : Reach 91247 := rs (se 1 (by rfl) ⟨68435, by rfl⟩) R136871
theorem R91303 : Reach 91303 := rs (se 1 (by rfl) ⟨68477, by rfl⟩) R136955
theorem R91327 : Reach 91327 := rs (se 1 (by rfl) ⟨68495, by rfl⟩) R136991
theorem R91359 : Reach 91359 := rs (se 1 (by rfl) ⟨68519, by rfl⟩) R137039
theorem R91439 : Reach 91439 := rs (se 1 (by rfl) ⟨68579, by rfl⟩) R137159
theorem R91675 : Reach 91675 := rs (se 1 (by rfl) ⟨68756, by rfl⟩) R137513
theorem R353819 : Reach 353819 := rs (se 1 (by rfl) ⟨265364, by rfl⟩) R530729
theorem R91679 : Reach 91679 := rs (se 1 (by rfl) ⟨68759, by rfl⟩) R137519
theorem R2713171 : Reach 2713171 := rs (se 1 (by rfl) ⟨2034878, by rfl⟩) R4069757
theorem R452249 : Reach 452249 := rs (se 2 (by rfl) ⟨169593, by rfl⟩) R339187
theorem R91839 : Reach 91839 := rs (se 1 (by rfl) ⟨68879, by rfl⟩) R137759
theorem R354203 : Reach 354203 := rs (se 1 (by rfl) ⟨265652, by rfl⟩) R531305
theorem R92095 : Reach 92095 := rs (se 1 (by rfl) ⟨69071, by rfl⟩) R138143
theorem R92127 : Reach 92127 := rs (se 1 (by rfl) ⟨69095, by rfl⟩) R138191
theorem R92187 : Reach 92187 := rs (se 1 (by rfl) ⟨69140, by rfl⟩) R138281
theorem R92191 : Reach 92191 := rs (se 1 (by rfl) ⟨69143, by rfl⟩) R138287
theorem R92207 : Reach 92207 := rs (se 1 (by rfl) ⟨69155, by rfl⟩) R138311
theorem R223279 : Reach 223279 := rs (se 1 (by rfl) ⟨167459, by rfl⟩) R334919
theorem R354401 : Reach 354401 := rs (se 2 (by rfl) ⟨132900, by rfl⟩) R265801
theorem R714905 : Reach 714905 := rs (se 2 (by rfl) ⟨268089, by rfl⟩) R536179
theorem R92383 : Reach 92383 := rs (se 1 (by rfl) ⟨69287, by rfl⟩) R138575
theorem R92443 : Reach 92443 := rs (se 1 (by rfl) ⟨69332, by rfl⟩) R138665
theorem R92543 : Reach 92543 := rs (se 1 (by rfl) ⟨69407, by rfl⟩) R138815
theorem R92719 : Reach 92719 := rs (se 1 (by rfl) ⟨69539, by rfl⟩) R139079
theorem R92775 : Reach 92775 := rs (se 1 (by rfl) ⟨69581, by rfl⟩) R139163
theorem R93151 : Reach 93151 := rs (se 1 (by rfl) ⟨69863, by rfl⟩) R139727
theorem R93179 : Reach 93179 := rs (se 1 (by rfl) ⟨69884, by rfl⟩) R139769
theorem R93247 : Reach 93247 := rs (se 1 (by rfl) ⟨69935, by rfl⟩) R139871
theorem R93567 : Reach 93567 := rs (se 1 (by rfl) ⟨70175, by rfl⟩) R140351
theorem R93595 : Reach 93595 := rs (se 1 (by rfl) ⟨70196, by rfl⟩) R140393
theorem R159131 : Reach 159131 := rs (se 1 (by rfl) ⟨119348, by rfl⟩) R238697
theorem R93663 : Reach 93663 := rs (se 1 (by rfl) ⟨70247, by rfl⟩) R140495
theorem R93799 : Reach 93799 := rs (se 1 (by rfl) ⟨70349, by rfl⟩) R140699
theorem R93947 : Reach 93947 := rs (se 1 (by rfl) ⟨70460, by rfl⟩) R140921
theorem R94015 : Reach 94015 := rs (se 1 (by rfl) ⟨70511, by rfl⟩) R141023
theorem R356177 : Reach 356177 := rs (se 2 (by rfl) ⟨133566, by rfl⟩) R267133
theorem R94079 : Reach 94079 := rs (se 1 (by rfl) ⟨70559, by rfl⟩) R141119
theorem R94191 : Reach 94191 := rs (se 1 (by rfl) ⟨70643, by rfl⟩) R141287
theorem R356345 : Reach 356345 := rs (se 2 (by rfl) ⟨133629, by rfl⟩) R267259
theorem R94203 : Reach 94203 := rs (se 1 (by rfl) ⟨70652, by rfl⟩) R141305
theorem R716849 : Reach 716849 := rs (se 2 (by rfl) ⟨268818, by rfl⟩) R537637
theorem R94271 : Reach 94271 := rs (se 1 (by rfl) ⟨70703, by rfl⟩) R141407
theorem R94311 : Reach 94311 := rs (se 1 (by rfl) ⟨70733, by rfl⟩) R141467
theorem R94335 : Reach 94335 := rs (se 1 (by rfl) ⟨70751, by rfl⟩) R141503
theorem R159887 : Reach 159887 := rs (se 1 (by rfl) ⟨119915, by rfl⟩) R239831
theorem R94363 : Reach 94363 := rs (se 1 (by rfl) ⟨70772, by rfl⟩) R141545
theorem R356633 : Reach 356633 := rs (se 2 (by rfl) ⟨133737, by rfl⟩) R267475
theorem R94567 : Reach 94567 := rs (se 1 (by rfl) ⟨70925, by rfl⟩) R141851
theorem R160103 : Reach 160103 := rs (se 1 (by rfl) ⟨120077, by rfl⟩) R240155
theorem R94619 : Reach 94619 := rs (se 1 (by rfl) ⟨70964, by rfl⟩) R141929
theorem R94971 : Reach 94971 := rs (se 1 (by rfl) ⟨71228, by rfl⟩) R142457
theorem R95039 : Reach 95039 := rs (se 1 (by rfl) ⟨71279, by rfl⟩) R142559
theorem R95067 : Reach 95067 := rs (se 1 (by rfl) ⟨71300, by rfl⟩) R142601
theorem R455939 : Reach 455939 := rs (se 1 (by rfl) ⟨341954, by rfl⟩) R683909
theorem R357803 : Reach 357803 := rs (se 1 (by rfl) ⟨268352, by rfl⟩) R536705
theorem R685523 : Reach 685523 := rs (se 1 (by rfl) ⟨514142, by rfl⟩) R1028285
theorem R1800323 : Reach 1800323 := rs (se 1 (by rfl) ⟨1350242, by rfl⟩) R2700485
theorem R719219 : Reach 719219 := rs (se 1 (by rfl) ⟨539414, by rfl⟩) R1078829
theorem R424399 : Reach 424399 := rs (se 1 (by rfl) ⟨318299, by rfl⟩) R636599
theorem R1080067 : Reach 1080067 := rs (se 1 (by rfl) ⟨810050, by rfl⟩) R1620101
theorem R588703 : Reach 588703 := rs (se 1 (by rfl) ⟨441527, by rfl⟩) R883055
theorem R359549 : Reach 359549 := rs (se 3 (by rfl) ⟨67415, by rfl⟩) R134831
theorem R359869 : Reach 359869 := rs (se 3 (by rfl) ⟨67475, by rfl⟩) R134951
theorem R360065 : Reach 360065 := rs (se 2 (by rfl) ⟨135024, by rfl⟩) R270049
theorem R131015 : Reach 131015 := rs (se 1 (by rfl) ⟨98261, by rfl⟩) R196523
theorem R3047483 : Reach 3047483 := rs (se 1 (by rfl) ⟨2285612, by rfl⟩) R4571225
theorem R4849901 : Reach 4849901 := rs (se 3 (by rfl) ⟨909356, by rfl⟩) R1818713
theorem R360733 : Reach 360733 := rs (se 3 (by rfl) ⟨67637, by rfl⟩) R135275
theorem R295451 : Reach 295451 := rs (se 1 (by rfl) ⟨221588, by rfl⟩) R443177
theorem R164519 : Reach 164519 := rs (se 1 (by rfl) ⟨123389, by rfl⟩) R246779
theorem R1082155 : Reach 1082155 := rs (se 1 (by rfl) ⟨811616, by rfl⟩) R1623233
theorem R820055 : Reach 820055 := rs (se 1 (by rfl) ⟨615041, by rfl⟩) R1230083
theorem R296065 : Reach 296065 := rs (se 2 (by rfl) ⟨111024, by rfl⟩) R222049
theorem R1803455 : Reach 1803455 := rs (se 1 (by rfl) ⟨1352591, by rfl⟩) R2705183
theorem R591083 : Reach 591083 := rs (se 1 (by rfl) ⟨443312, by rfl⟩) R886625
theorem R18089405 : Reach 18089405 := rs (se 3 (by rfl) ⟨3391763, by rfl⟩) R6783527
theorem R198121 : Reach 198121 := rs (se 2 (by rfl) ⟨74295, by rfl⟩) R148591
theorem R329759 : Reach 329759 := rs (se 1 (by rfl) ⟨247319, by rfl⟩) R494639
theorem R232217 : Reach 232217 := rs (se 2 (by rfl) ⟨87081, by rfl⟩) R174163
theorem R1478533 : Reach 1478533 := rs (se 4 (by rfl) ⟨138612, by rfl⟩) R277225
theorem R1052635 : Reach 1052635 := rs (se 1 (by rfl) ⟨789476, by rfl⟩) R1578953
theorem R725719 : Reach 725719 := rs (se 1 (by rfl) ⟨544289, by rfl⟩) R1088579
theorem R529163 : Reach 529163 := rs (se 1 (by rfl) ⟨396872, by rfl⟩) R793745
theorem R300115 : Reach 300115 := rs (se 1 (by rfl) ⟨225086, by rfl⟩) R450173
theorem R463967 : Reach 463967 := rs (se 1 (by rfl) ⟨347975, by rfl⟩) R695951
theorem R267499 : Reach 267499 := rs (se 1 (by rfl) ⟨200624, by rfl⟩) R401249
theorem R136703 : Reach 136703 := rs (se 1 (by rfl) ⟨102527, by rfl⟩) R205055
theorem R136811 : Reach 136811 := rs (se 1 (by rfl) ⟨102608, by rfl⟩) R205217
theorem R235295 : Reach 235295 := rs (se 1 (by rfl) ⟨176471, by rfl⟩) R352943
theorem R137081 : Reach 137081 := rs (se 2 (by rfl) ⟨51405, by rfl⟩) R102811
theorem R464777 : Reach 464777 := rs (se 2 (by rfl) ⟨174291, by rfl⟩) R348583
theorem R268231 : Reach 268231 := rs (se 1 (by rfl) ⟨201173, by rfl⟩) R402347
theorem R2594875 : Reach 2594875 := rs (se 1 (by rfl) ⟨1946156, by rfl⟩) R3892313
theorem R137327 : Reach 137327 := rs (se 1 (by rfl) ⟨102995, by rfl⟩) R205991
theorem R137399 : Reach 137399 := rs (se 1 (by rfl) ⟨103049, by rfl⟩) R206099
theorem R268591 : Reach 268591 := rs (se 1 (by rfl) ⟨201443, by rfl⟩) R402887
theorem R235879 : Reach 235879 := rs (se 1 (by rfl) ⟨176909, by rfl⟩) R353819
theorem R301499 : Reach 301499 := rs (se 1 (by rfl) ⟨226124, by rfl⟩) R452249
theorem R399811 : Reach 399811 := rs (se 1 (by rfl) ⟨299858, by rfl⟩) R599717
theorem R268751 : Reach 268751 := rs (se 1 (by rfl) ⟨201563, by rfl⟩) R403127
theorem R137819 : Reach 137819 := rs (se 1 (by rfl) ⟨103364, by rfl⟩) R206729
theorem R137831 : Reach 137831 := rs (se 1 (by rfl) ⟨103373, by rfl⟩) R206747
theorem R236135 : Reach 236135 := rs (se 1 (by rfl) ⟨177101, by rfl⟩) R354203
theorem R137855 : Reach 137855 := rs (se 1 (by rfl) ⟨103391, by rfl⟩) R206783
theorem R137963 : Reach 137963 := rs (se 1 (by rfl) ⟨103472, by rfl⟩) R206945
theorem R236267 : Reach 236267 := rs (se 1 (by rfl) ⟨177200, by rfl⟩) R354401
theorem R137993 : Reach 137993 := rs (se 2 (by rfl) ⟨51747, by rfl⟩) R103495
theorem R236297 : Reach 236297 := rs (se 2 (by rfl) ⟨88611, by rfl⟩) R177223
theorem R1186721 : Reach 1186721 := rs (se 2 (by rfl) ⟨445020, by rfl⟩) R890041
theorem R138233 : Reach 138233 := rs (se 2 (by rfl) ⟨51837, by rfl⟩) R103675
theorem R106087 : Reach 106087 := rs (se 1 (by rfl) ⟨79565, by rfl⟩) R159131
theorem R138863 : Reach 138863 := rs (se 1 (by rfl) ⟨104147, by rfl⟩) R208295
theorem R302717 : Reach 302717 := rs (se 3 (by rfl) ⟨56759, by rfl⟩) R113519
theorem R138983 : Reach 138983 := rs (se 1 (by rfl) ⟨104237, by rfl⟩) R208475
theorem R237451 : Reach 237451 := rs (se 1 (by rfl) ⟨178088, by rfl⟩) R356177
theorem R270323 : Reach 270323 := rs (se 1 (by rfl) ⟨202742, by rfl⟩) R405485
theorem R237563 : Reach 237563 := rs (se 1 (by rfl) ⟨178172, by rfl⟩) R356345
theorem R139259 : Reach 139259 := rs (se 1 (by rfl) ⟨104444, by rfl⟩) R208889
theorem R139319 : Reach 139319 := rs (se 1 (by rfl) ⟨104489, by rfl⟩) R208979
theorem R106591 : Reach 106591 := rs (se 1 (by rfl) ⟨79943, by rfl⟩) R159887
theorem R139439 : Reach 139439 := rs (se 1 (by rfl) ⟨104579, by rfl⟩) R209159
theorem R237755 : Reach 237755 := rs (se 1 (by rfl) ⟨178316, by rfl⟩) R356633
theorem R106735 : Reach 106735 := rs (se 1 (by rfl) ⟨80051, by rfl⟩) R160103
theorem R139643 : Reach 139643 := rs (se 1 (by rfl) ⟨104732, by rfl⟩) R209465
theorem R205343 : Reach 205343 := rs (se 1 (by rfl) ⟨154007, by rfl⟩) R308015
theorem R139817 : Reach 139817 := rs (se 2 (by rfl) ⟨52431, by rfl⟩) R104863
theorem R565865 : Reach 565865 := rs (se 2 (by rfl) ⟨212199, by rfl⟩) R424399
theorem R139913 : Reach 139913 := rs (se 2 (by rfl) ⟨52467, by rfl⟩) R104935
theorem R303959 : Reach 303959 := rs (se 1 (by rfl) ⟨227969, by rfl⟩) R455939
theorem R140123 : Reach 140123 := rs (se 1 (by rfl) ⟨105092, by rfl⟩) R210185
theorem R140159 : Reach 140159 := rs (se 1 (by rfl) ⟨105119, by rfl⟩) R210239
theorem R140231 : Reach 140231 := rs (se 1 (by rfl) ⟨105173, by rfl⟩) R210347
theorem R238535 : Reach 238535 := rs (se 1 (by rfl) ⟨178901, by rfl⟩) R357803
theorem R205919 : Reach 205919 := rs (se 1 (by rfl) ⟨154439, by rfl⟩) R308879
theorem R140383 : Reach 140383 := rs (se 1 (by rfl) ⟨105287, by rfl⟩) R210575
theorem R140447 : Reach 140447 := rs (se 1 (by rfl) ⟨105335, by rfl⟩) R210671
theorem R140591 : Reach 140591 := rs (se 1 (by rfl) ⟨105443, by rfl⟩) R210887
theorem R1189181 : Reach 1189181 := rs (se 3 (by rfl) ⟨222971, by rfl⟩) R445943
theorem R206171 : Reach 206171 := rs (se 1 (by rfl) ⟨154628, by rfl⟩) R309257
theorem R140783 : Reach 140783 := rs (se 1 (by rfl) ⟨105587, by rfl⟩) R211175
theorem R140795 : Reach 140795 := rs (se 1 (by rfl) ⟨105596, by rfl⟩) R211193
theorem R140831 : Reach 140831 := rs (se 1 (by rfl) ⟨105623, by rfl⟩) R211247
theorem R206441 : Reach 206441 := rs (se 2 (by rfl) ⟨77415, by rfl⟩) R154831
theorem R239233 : Reach 239233 := rs (se 2 (by rfl) ⟨89712, by rfl⟩) R179425
theorem R140975 : Reach 140975 := rs (se 1 (by rfl) ⟨105731, by rfl⟩) R211463
theorem R141065 : Reach 141065 := rs (se 2 (by rfl) ⟨52899, by rfl⟩) R105799
theorem R141095 : Reach 141095 := rs (se 1 (by rfl) ⟨105821, by rfl⟩) R211643
theorem R239699 : Reach 239699 := rs (se 1 (by rfl) ⟨179774, by rfl⟩) R359549
theorem R207071 : Reach 207071 := rs (se 1 (by rfl) ⟨155303, by rfl⟩) R310607
theorem R141695 : Reach 141695 := rs (se 1 (by rfl) ⟨106271, by rfl⟩) R212543
theorem R240043 : Reach 240043 := rs (se 1 (by rfl) ⟨180032, by rfl⟩) R360065
theorem R141935 : Reach 141935 := rs (se 1 (by rfl) ⟨106451, by rfl⟩) R212903
theorem R142151 : Reach 142151 := rs (se 1 (by rfl) ⟨106613, by rfl⟩) R213227
theorem R1190821 : Reach 1190821 := rs (se 4 (by rfl) ⟨111639, by rfl⟩) R223279
theorem R1813913 : Reach 1813913 := rs (se 2 (by rfl) ⟨680217, by rfl⟩) R1360435
theorem R470771 : Reach 470771 := rs (se 1 (by rfl) ⟨353078, by rfl⟩) R706157
theorem R339707 : Reach 339707 := rs (se 1 (by rfl) ⟨254780, by rfl⟩) R509561
theorem R3617561 : Reach 3617561 := rs (se 2 (by rfl) ⟨1356585, by rfl⟩) R2713171
theorem R537953 : Reach 537953 := rs (se 2 (by rfl) ⟨201732, by rfl⟩) R403465
theorem R2340485 : Reach 2340485 := rs (se 4 (by rfl) ⟨219420, by rfl⟩) R438841
theorem R440255 : Reach 440255 := rs (se 1 (by rfl) ⟨330191, by rfl⟩) R660383
theorem R210923 : Reach 210923 := rs (se 1 (by rfl) ⟨158192, by rfl⟩) R316385
theorem R1226819 : Reach 1226819 := rs (se 1 (by rfl) ⟨920114, by rfl⟩) R1840229
theorem R310013 : Reach 310013 := rs (se 3 (by rfl) ⟨58127, by rfl⟩) R116255
theorem R146233 : Reach 146233 := rs (se 2 (by rfl) ⟨54837, by rfl⟩) R109675
theorem R1064083 : Reach 1064083 := rs (se 1 (by rfl) ⟨798062, by rfl⟩) R1596125
theorem R474335 : Reach 474335 := rs (se 1 (by rfl) ⟨355751, by rfl⟩) R711503
theorem R179759 : Reach 179759 := rs (se 1 (by rfl) ⟨134819, by rfl⟩) R269639
theorem R1064933 : Reach 1064933 := rs (se 4 (by rfl) ⟨99837, by rfl⟩) R199675
theorem R377303 : Reach 377303 := rs (se 1 (by rfl) ⟨282977, by rfl⟩) R565955
theorem R705185 : Reach 705185 := rs (se 2 (by rfl) ⟨264444, by rfl⟩) R528889
theorem R1917917 : Reach 1917917 := rs (se 3 (by rfl) ⟨359609, by rfl⟩) R719219
theorem R443407 : Reach 443407 := rs (se 1 (by rfl) ⟨332555, by rfl⟩) R665111
theorem R115759 : Reach 115759 := rs (se 1 (by rfl) ⟨86819, by rfl⟩) R173639
theorem R2245913 : Reach 2245913 := rs (se 2 (by rfl) ⟨842217, by rfl⟩) R1684435
theorem R476603 : Reach 476603 := rs (se 1 (by rfl) ⟨357452, by rfl⟩) R714905
theorem R3066173 : Reach 3066173 := rs (se 3 (by rfl) ⟨574907, by rfl⟩) R1149815
theorem R117055 : Reach 117055 := rs (se 1 (by rfl) ⟨87791, by rfl⟩) R175583
theorem R117227 : Reach 117227 := rs (se 1 (by rfl) ⟨87920, by rfl⟩) R175841
theorem R2017817 : Reach 2017817 := rs (se 2 (by rfl) ⟨756681, by rfl⟩) R1513363
theorem R477899 : Reach 477899 := rs (se 1 (by rfl) ⟨358424, by rfl⟩) R716849
theorem R708221 : Reach 708221 := rs (se 3 (by rfl) ⟨132791, by rfl⟩) R265583
theorem R1200215 : Reach 1200215 := rs (se 1 (by rfl) ⟨900161, by rfl⟩) R1800323
theorem R512243 : Reach 512243 := rs (se 1 (by rfl) ⟨384182, by rfl⟩) R768365
theorem R479825 : Reach 479825 := rs (se 2 (by rfl) ⟨179934, by rfl⟩) R359869
theorem R349373 : Reach 349373 := rs (se 3 (by rfl) ⟨65507, by rfl⟩) R131015
theorem R447943 : Reach 447943 := rs (se 1 (by rfl) ⟨335957, by rfl⟩) R671915
theorem R251387 : Reach 251387 := rs (se 1 (by rfl) ⟨188540, by rfl⟩) R377081
theorem R316925 : Reach 316925 := rs (se 3 (by rfl) ⟨59423, by rfl⟩) R118847
theorem R317033 : Reach 317033 := rs (se 2 (by rfl) ⟨118887, by rfl⟩) R237775
theorem R382915 : Reach 382915 := rs (se 1 (by rfl) ⟨287186, by rfl⟩) R574373
theorem R841711 : Reach 841711 := rs (se 1 (by rfl) ⟨631283, by rfl⟩) R1262567
theorem R285191 : Reach 285191 := rs (se 1 (by rfl) ⟨213893, by rfl⟩) R427787
theorem R219743 : Reach 219743 := rs (se 1 (by rfl) ⟨164807, by rfl⟩) R329615
theorem R154271 : Reach 154271 := rs (se 1 (by rfl) ⟨115703, by rfl⟩) R231407
theorem R383791 : Reach 383791 := rs (se 1 (by rfl) ⟨287843, by rfl⟩) R575687
theorem R318269 : Reach 318269 := rs (se 3 (by rfl) ⟨59675, by rfl⟩) R119351
theorem R2317501 : Reach 2317501 := rs (se 3 (by rfl) ⟨434531, by rfl⟩) R869063
theorem R3432223 : Reach 3432223 := rs (se 1 (by rfl) ⟨2574167, by rfl⟩) R5148335
theorem R352289 : Reach 352289 := rs (se 2 (by rfl) ⟨132108, by rfl⟩) R264217
theorem R1531993 : Reach 1531993 := rs (se 2 (by rfl) ⟨574497, by rfl⟩) R1148995
theorem R352471 : Reach 352471 := rs (se 1 (by rfl) ⟨264353, by rfl⟩) R528707
theorem R155945 : Reach 155945 := rs (se 2 (by rfl) ⟨58479, by rfl⟩) R116959
theorem R287165 : Reach 287165 := rs (se 3 (by rfl) ⟨53843, by rfl⟩) R107687
theorem R156215 : Reach 156215 := rs (se 1 (by rfl) ⟨117161, by rfl⟩) R234323
theorem R221993 : Reach 221993 := rs (se 2 (by rfl) ⟨83247, by rfl⟩) R166495
theorem R418627 : Reach 418627 := rs (se 1 (by rfl) ⟨313970, by rfl⟩) R627941
theorem R222203 : Reach 222203 := rs (se 1 (by rfl) ⟨166652, by rfl⟩) R333305
theorem R91227 : Reach 91227 := rs (se 1 (by rfl) ⟨68420, by rfl⟩) R136841
theorem R91239 : Reach 91239 := rs (se 1 (by rfl) ⟨68429, by rfl⟩) R136859
theorem R156775 : Reach 156775 := rs (se 1 (by rfl) ⟨117581, by rfl⟩) R235163
theorem R1369199 : Reach 1369199 := rs (se 1 (by rfl) ⟨1026899, by rfl⟩) R2053799
theorem R91367 : Reach 91367 := rs (se 1 (by rfl) ⟨68525, by rfl⟩) R137051
theorem R812267 : Reach 812267 := rs (se 1 (by rfl) ⟨609200, by rfl⟩) R1218401
theorem R91623 : Reach 91623 := rs (se 1 (by rfl) ⟨68717, by rfl⟩) R137435
theorem R91803 : Reach 91803 := rs (se 1 (by rfl) ⟨68852, by rfl⟩) R137705
theorem R288427 : Reach 288427 := rs (se 1 (by rfl) ⟨216320, by rfl⟩) R432641
theorem R92063 : Reach 92063 := rs (se 1 (by rfl) ⟨69047, by rfl⟩) R138095
theorem R92071 : Reach 92071 := rs (se 1 (by rfl) ⟨69053, by rfl⟩) R138107
theorem R157727 : Reach 157727 := rs (se 1 (by rfl) ⟨118295, by rfl⟩) R236591
theorem R1599745 : Reach 1599745 := rs (se 2 (by rfl) ⟨599904, by rfl⟩) R1199809
theorem R780623 : Reach 780623 := rs (se 1 (by rfl) ⟨585467, by rfl⟩) R1170935
theorem R92647 : Reach 92647 := rs (se 1 (by rfl) ⟨69485, by rfl⟩) R138971
theorem R92827 : Reach 92827 := rs (se 1 (by rfl) ⟨69620, by rfl⟩) R139241
theorem R748379 : Reach 748379 := rs (se 1 (by rfl) ⟨561284, by rfl⟩) R1122569
theorem R93295 : Reach 93295 := rs (se 1 (by rfl) ⟨69971, by rfl⟩) R139943
theorem R93375 : Reach 93375 := rs (se 1 (by rfl) ⟨70031, by rfl⟩) R140063
theorem R93391 : Reach 93391 := rs (se 1 (by rfl) ⟨70043, by rfl⟩) R140087
theorem R93511 : Reach 93511 := rs (se 1 (by rfl) ⟨70133, by rfl⟩) R140267
theorem R585569 : Reach 585569 := rs (se 2 (by rfl) ⟨219588, by rfl⟩) R439177
theorem R94239 : Reach 94239 := rs (se 1 (by rfl) ⟨70679, by rfl⟩) R141359
theorem R94415 : Reach 94415 := rs (se 1 (by rfl) ⟨70811, by rfl⟩) R141623
theorem R94535 : Reach 94535 := rs (se 1 (by rfl) ⟨70901, by rfl⟩) R141803
theorem R160123 : Reach 160123 := rs (se 1 (by rfl) ⟨120092, by rfl⟩) R240185
theorem R1864225 : Reach 1864225 := rs (se 2 (by rfl) ⟨699084, by rfl⟩) R1398169
theorem R160393 : Reach 160393 := rs (se 2 (by rfl) ⟨60147, by rfl⟩) R120295
theorem R95003 : Reach 95003 := rs (se 1 (by rfl) ⟨71252, by rfl⟩) R142505
theorem R226145 : Reach 226145 := rs (se 2 (by rfl) ⟨84804, by rfl⟩) R169609
theorem R1078919 : Reach 1078919 := rs (se 1 (by rfl) ⟨809189, by rfl⟩) R1618379
theorem R457015 : Reach 457015 := rs (se 1 (by rfl) ⟨342761, by rfl⟩) R685523
theorem R1440089 : Reach 1440089 := rs (se 2 (by rfl) ⟨540033, by rfl⟩) R1080067
theorem R1603997 : Reach 1603997 := rs (se 3 (by rfl) ⟨300749, by rfl⟩) R601499
theorem R784937 : Reach 784937 := rs (se 2 (by rfl) ⟨294351, by rfl⟩) R588703
theorem R228143 : Reach 228143 := rs (se 1 (by rfl) ⟨171107, by rfl⟩) R342215
theorem R2030629 : Reach 2030629 := rs (se 4 (by rfl) ⟨190371, by rfl⟩) R380743
theorem R359579 : Reach 359579 := rs (se 1 (by rfl) ⟨269684, by rfl⟩) R539369
theorem R2031655 : Reach 2031655 := rs (se 1 (by rfl) ⟨1523741, by rfl⟩) R3047483
theorem R196967 : Reach 196967 := rs (se 1 (by rfl) ⟨147725, by rfl⟩) R295451
theorem R1278611 : Reach 1278611 := rs (se 1 (by rfl) ⟨958958, by rfl⟩) R1917917
theorem R394055 : Reach 394055 := rs (se 1 (by rfl) ⟨295541, by rfl⟩) R591083
theorem R12059603 : Reach 12059603 := rs (se 1 (by rfl) ⟨9044702, by rfl⟩) R18089405
theorem R1442873 : Reach 1442873 := rs (se 2 (by rfl) ⟨541077, by rfl⟩) R1082155
theorem R591209 : Reach 591209 := rs (se 2 (by rfl) ⟨221703, by rfl⟩) R443407
theorem R1345211 : Reach 1345211 := rs (se 1 (by rfl) ⟨1008908, by rfl⟩) R2017817
theorem R264161 : Reach 264161 := rs (se 2 (by rfl) ⟨99060, by rfl⟩) R198121
theorem R592541 : Reach 592541 := rs (se 3 (by rfl) ⟨111101, by rfl⟩) R222203
theorem R2132993 : Reach 2132993 := rs (se 2 (by rfl) ⟨799872, by rfl⟩) R1599745
theorem R232915 : Reach 232915 := rs (se 1 (by rfl) ⟨174686, by rfl⟩) R349373
theorem R167591 : Reach 167591 := rs (se 1 (by rfl) ⟨125693, by rfl⟩) R251387
theorem R5738165 : Reach 5738165 := rs (se 5 (by rfl) ⟨268976, by rfl⟩) R537953
theorem R200999 : Reach 200999 := rs (se 1 (by rfl) ⟨150749, by rfl⟩) R301499
theorem R2232677 : Reach 2232677 := rs (se 4 (by rfl) ⟨209313, by rfl⟩) R418627
theorem R102847 : Reach 102847 := rs (se 1 (by rfl) ⟨77135, by rfl⟩) R154271
theorem R791147 : Reach 791147 := rs (se 1 (by rfl) ⟨593360, by rfl⟩) R1186721
theorem R1971377 : Reach 1971377 := rs (se 2 (by rfl) ⟨739266, by rfl⟩) R1478533
theorem R234859 : Reach 234859 := rs (se 1 (by rfl) ⟨176144, by rfl⟩) R352289
theorem R103963 : Reach 103963 := rs (se 1 (by rfl) ⟨77972, by rfl⟩) R155945
theorem R136895 : Reach 136895 := rs (se 1 (by rfl) ⟨102671, by rfl⟩) R205343
theorem R104143 : Reach 104143 := rs (se 1 (by rfl) ⟨78107, by rfl⟩) R156215
theorem R1579013 : Reach 1579013 := rs (se 4 (by rfl) ⟨148032, by rfl⟩) R296065
theorem R137279 : Reach 137279 := rs (se 1 (by rfl) ⟨102959, by rfl⟩) R205919
theorem R792787 : Reach 792787 := rs (se 1 (by rfl) ⟨594590, by rfl⟩) R1189181
theorem R137447 : Reach 137447 := rs (se 1 (by rfl) ⟨103085, by rfl⟩) R206171
theorem R137627 : Reach 137627 := rs (se 1 (by rfl) ⟨103220, by rfl⟩) R206441
theorem R105151 : Reach 105151 := rs (se 1 (by rfl) ⟨78863, by rfl⟩) R157727
theorem R400153 : Reach 400153 := rs (se 2 (by rfl) ⟨150057, by rfl⟩) R300115
theorem R138047 : Reach 138047 := rs (se 1 (by rfl) ⟨103535, by rfl⟩) R207071
theorem R498919 : Reach 498919 := rs (se 1 (by rfl) ⟨374189, by rfl⟩) R748379
theorem R597257 : Reach 597257 := rs (se 2 (by rfl) ⟨223971, by rfl⟩) R447943
theorem R1122281 : Reach 1122281 := rs (se 2 (by rfl) ⟨420855, by rfl⟩) R841711
theorem R533081 : Reach 533081 := rs (se 2 (by rfl) ⟨199905, by rfl⟩) R399811
theorem R140615 : Reach 140615 := rs (se 1 (by rfl) ⟨105461, by rfl⟩) R210923
theorem R1418777 : Reach 1418777 := rs (se 2 (by rfl) ⟨532041, by rfl⟩) R1064083
theorem R960059 : Reach 960059 := rs (se 1 (by rfl) ⟨720044, by rfl⟩) R1440089
theorem R3090001 : Reach 3090001 := rs (se 2 (by rfl) ⟨1158750, by rfl⟩) R2317501
theorem R206675 : Reach 206675 := rs (se 1 (by rfl) ⟨155006, by rfl⟩) R310013
theorem R239719 : Reach 239719 := rs (se 1 (by rfl) ⟨179789, by rfl⟩) R359579
theorem R141449 : Reach 141449 := rs (se 2 (by rfl) ⟨53043, by rfl⟩) R106087
theorem R2042657 : Reach 2042657 := rs (se 2 (by rfl) ⟨765996, by rfl⟩) R1531993
theorem R142121 : Reach 142121 := rs (se 2 (by rfl) ⟨53295, by rfl⟩) R106591
theorem R469961 : Reach 469961 := rs (se 2 (by rfl) ⟨176235, by rfl⟩) R352471
theorem R142313 : Reach 142313 := rs (se 2 (by rfl) ⟨53367, by rfl⟩) R106735
theorem R470123 : Reach 470123 := rs (se 1 (by rfl) ⟨352592, by rfl⟩) R705185
theorem R109679 : Reach 109679 := rs (se 1 (by rfl) ⟨82259, by rfl⟩) R164519
theorem R209033 : Reach 209033 := rs (se 2 (by rfl) ⟨78387, by rfl⟩) R156775
theorem R2044115 : Reach 2044115 := rs (se 1 (by rfl) ⟨1533086, by rfl⟩) R3066173
theorem R1258021 : Reach 1258021 := rs (se 4 (by rfl) ⟨117939, by rfl⟩) R235879
theorem R341495 : Reach 341495 := rs (se 1 (by rfl) ⟨256121, by rfl⟩) R512243
theorem R309311 : Reach 309311 := rs (se 1 (by rfl) ⟨231983, by rfl⟩) R463967
theorem R211283 : Reach 211283 := rs (se 1 (by rfl) ⟨158462, by rfl⟩) R316925
theorem R211355 : Reach 211355 := rs (se 1 (by rfl) ⟨158516, by rfl⟩) R317033
theorem R1587761 : Reach 1587761 := rs (se 2 (by rfl) ⟨595410, by rfl⟩) R1190821
theorem R309851 : Reach 309851 := rs (se 1 (by rfl) ⟨232388, by rfl⟩) R464777
theorem R179167 : Reach 179167 := rs (se 1 (by rfl) ⟨134375, by rfl⟩) R268751
theorem R146495 : Reach 146495 := rs (se 1 (by rfl) ⟨109871, by rfl⟩) R219743
theorem R180215 : Reach 180215 := rs (se 1 (by rfl) ⟨135161, by rfl⟩) R270323
theorem R377243 : Reach 377243 := rs (se 1 (by rfl) ⟨282932, by rfl⟩) R565865
theorem R213497 : Reach 213497 := rs (se 2 (by rfl) ⟨80061, by rfl⟩) R160123
theorem R147995 : Reach 147995 := rs (se 1 (by rfl) ⟨110996, by rfl⟩) R221993
theorem R541511 : Reach 541511 := rs (se 1 (by rfl) ⟨406133, by rfl⟩) R812267
theorem R213857 : Reach 213857 := rs (se 2 (by rfl) ⟨80196, by rfl⟩) R160393
theorem R967625 : Reach 967625 := rs (se 2 (by rfl) ⟨362859, by rfl⟩) R725719
theorem R312605 : Reach 312605 := rs (se 3 (by rfl) ⟨58613, by rfl⟩) R117227
theorem R608381 : Reach 608381 := rs (se 3 (by rfl) ⟨114071, by rfl⟩) R228143
theorem R313847 : Reach 313847 := rs (se 1 (by rfl) ⟨235385, by rfl⟩) R470771
theorem R510553 : Reach 510553 := rs (se 2 (by rfl) ⟨191457, by rfl⟩) R382915
theorem R3459833 : Reach 3459833 := rs (se 2 (by rfl) ⟨1297437, by rfl⟩) R2594875
theorem R609353 : Reach 609353 := rs (se 2 (by rfl) ⟨228507, by rfl⟩) R457015
theorem R2411707 : Reach 2411707 := rs (se 1 (by rfl) ⟨1808780, by rfl⟩) R3617561
theorem R150763 : Reach 150763 := rs (se 1 (by rfl) ⟨113072, by rfl⟩) R226145
theorem R511721 : Reach 511721 := rs (se 2 (by rfl) ⟨191895, by rfl⟩) R383791
theorem R1560323 : Reach 1560323 := rs (se 1 (by rfl) ⟨1170242, by rfl⟩) R2340485
theorem R2707505 : Reach 2707505 := rs (se 2 (by rfl) ⟨1015314, by rfl⟩) R2030629
theorem R479357 : Reach 479357 := rs (se 3 (by rfl) ⟨89879, by rfl⟩) R179759
theorem R1069331 : Reach 1069331 := rs (se 1 (by rfl) ⟨801998, by rfl⟩) R1603997
theorem R1888589 : Reach 1888589 := rs (se 3 (by rfl) ⟨354110, by rfl⟩) R708221
theorem R807245 : Reach 807245 := rs (se 3 (by rfl) ⟨151358, by rfl⟩) R302717
theorem R316223 : Reach 316223 := rs (se 1 (by rfl) ⟨237167, by rfl⟩) R474335
theorem R1561517 : Reach 1561517 := rs (se 3 (by rfl) ⟨292784, by rfl⟩) R585569
theorem R4576297 : Reach 4576297 := rs (se 2 (by rfl) ⟨1716111, by rfl⟩) R3432223
theorem R316601 : Reach 316601 := rs (se 2 (by rfl) ⟨118725, by rfl⟩) R237451
theorem R709955 : Reach 709955 := rs (se 1 (by rfl) ⟨532466, by rfl⟩) R1064933
theorem R3233267 : Reach 3233267 := rs (se 1 (by rfl) ⟨2424950, by rfl⟩) R4849901
theorem R3200573 : Reach 3200573 := rs (se 3 (by rfl) ⟨600107, by rfl⟩) R1200215
theorem R480977 : Reach 480977 := rs (se 2 (by rfl) ⟨180366, by rfl⟩) R360733
theorem R1202303 : Reach 1202303 := rs (se 1 (by rfl) ⟨901727, by rfl⟩) R1803455
theorem R1497275 : Reach 1497275 := rs (se 1 (by rfl) ⟨1122956, by rfl⟩) R2245913
theorem R317735 : Reach 317735 := rs (se 1 (by rfl) ⟨238301, by rfl⟩) R476603
theorem R1006141 : Reach 1006141 := rs (se 3 (by rfl) ⟨188651, by rfl⟩) R377303
theorem R219839 : Reach 219839 := rs (se 1 (by rfl) ⟨164879, by rfl⟩) R329759
theorem R154345 : Reach 154345 := rs (se 2 (by rfl) ⟨57879, by rfl⟩) R115759
theorem R187177 : Reach 187177 := rs (se 2 (by rfl) ⟨70191, by rfl⟩) R140383
theorem R318599 : Reach 318599 := rs (se 1 (by rfl) ⟨238949, by rfl⟩) R477899
theorem R154811 : Reach 154811 := rs (se 1 (by rfl) ⟨116108, by rfl⟩) R232217
theorem R318977 : Reach 318977 := rs (se 2 (by rfl) ⟨119616, by rfl⟩) R239233
theorem R384569 : Reach 384569 := rs (se 2 (by rfl) ⟨144213, by rfl⟩) R288427
theorem R2186813 : Reach 2186813 := rs (se 3 (by rfl) ⟨410027, by rfl⟩) R820055
theorem R810557 : Reach 810557 := rs (se 3 (by rfl) ⟨151979, by rfl⟩) R303959
theorem R319883 : Reach 319883 := rs (se 1 (by rfl) ⟨239912, by rfl⟩) R479825
theorem R156073 : Reach 156073 := rs (se 2 (by rfl) ⟨58527, by rfl⟩) R117055
theorem R352775 : Reach 352775 := rs (se 1 (by rfl) ⟨264581, by rfl⟩) R529163
theorem R320057 : Reach 320057 := rs (se 2 (by rfl) ⟨120021, by rfl⟩) R240043
theorem R91135 : Reach 91135 := rs (se 1 (by rfl) ⟨68351, by rfl⟩) R136703
theorem R91207 : Reach 91207 := rs (se 1 (by rfl) ⟨68405, by rfl⟩) R136811
theorem R156863 : Reach 156863 := rs (se 1 (by rfl) ⟨117647, by rfl⟩) R235295
theorem R91387 : Reach 91387 := rs (se 1 (by rfl) ⟨68540, by rfl⟩) R137081
theorem R91551 : Reach 91551 := rs (se 1 (by rfl) ⟨68663, by rfl⟩) R137327
theorem R91599 : Reach 91599 := rs (se 1 (by rfl) ⟨68699, by rfl⟩) R137399
theorem R190127 : Reach 190127 := rs (se 1 (by rfl) ⟨142595, by rfl⟩) R285191
theorem R91879 : Reach 91879 := rs (se 1 (by rfl) ⟨68909, by rfl⟩) R137819
theorem R91887 : Reach 91887 := rs (se 1 (by rfl) ⟨68915, by rfl⟩) R137831
theorem R157423 : Reach 157423 := rs (se 1 (by rfl) ⟨118067, by rfl⟩) R236135
theorem R91903 : Reach 91903 := rs (se 1 (by rfl) ⟨68927, by rfl⟩) R137855
theorem R91975 : Reach 91975 := rs (se 1 (by rfl) ⟨68981, by rfl⟩) R137963
theorem R157511 : Reach 157511 := rs (se 1 (by rfl) ⟨118133, by rfl⟩) R236267
theorem R91995 : Reach 91995 := rs (se 1 (by rfl) ⟨68996, by rfl⟩) R137993
theorem R157531 : Reach 157531 := rs (se 1 (by rfl) ⟨118148, by rfl⟩) R236297
theorem R92155 : Reach 92155 := rs (se 1 (by rfl) ⟨69116, by rfl⟩) R138233
theorem R92575 : Reach 92575 := rs (se 1 (by rfl) ⟨69431, by rfl⟩) R138863
theorem R92655 : Reach 92655 := rs (se 1 (by rfl) ⟨69491, by rfl⟩) R138983
theorem R1403513 : Reach 1403513 := rs (se 2 (by rfl) ⟨526317, by rfl⟩) R1052635
theorem R92839 : Reach 92839 := rs (se 1 (by rfl) ⟨69629, by rfl⟩) R139259
theorem R158375 : Reach 158375 := rs (se 1 (by rfl) ⟨118781, by rfl⟩) R237563
theorem R92879 : Reach 92879 := rs (se 1 (by rfl) ⟨69659, by rfl⟩) R139319
theorem R92959 : Reach 92959 := rs (se 1 (by rfl) ⟨69719, by rfl⟩) R139439
theorem R158503 : Reach 158503 := rs (se 1 (by rfl) ⟨118877, by rfl⟩) R237755
theorem R93095 : Reach 93095 := rs (se 1 (by rfl) ⟨69821, by rfl⟩) R139643
theorem R191443 : Reach 191443 := rs (se 1 (by rfl) ⟨143582, by rfl⟩) R287165
theorem R93211 : Reach 93211 := rs (se 1 (by rfl) ⟨69908, by rfl⟩) R139817
theorem R93275 : Reach 93275 := rs (se 1 (by rfl) ⟨69956, by rfl⟩) R139913
theorem R93415 : Reach 93415 := rs (se 1 (by rfl) ⟨70061, by rfl⟩) R140123
theorem R93439 : Reach 93439 := rs (se 1 (by rfl) ⟨70079, by rfl⟩) R140159
theorem R93487 : Reach 93487 := rs (se 1 (by rfl) ⟨70115, by rfl⟩) R140231
theorem R159023 : Reach 159023 := rs (se 1 (by rfl) ⟨119267, by rfl⟩) R238535
theorem R2485633 : Reach 2485633 := rs (se 2 (by rfl) ⟨932112, by rfl⟩) R1864225
theorem R912799 : Reach 912799 := rs (se 1 (by rfl) ⟨684599, by rfl⟩) R1369199
theorem R93631 : Reach 93631 := rs (se 1 (by rfl) ⟨70223, by rfl⟩) R140447
theorem R93727 : Reach 93727 := rs (se 1 (by rfl) ⟨70295, by rfl⟩) R140591
theorem R93855 : Reach 93855 := rs (se 1 (by rfl) ⟨70391, by rfl⟩) R140783
theorem R93863 : Reach 93863 := rs (se 1 (by rfl) ⟨70397, by rfl⟩) R140795
theorem R93887 : Reach 93887 := rs (se 1 (by rfl) ⟨70415, by rfl⟩) R140831
theorem R93983 : Reach 93983 := rs (se 1 (by rfl) ⟨70487, by rfl⟩) R140975
theorem R94043 : Reach 94043 := rs (se 1 (by rfl) ⟨70532, by rfl⟩) R141065
theorem R94063 : Reach 94063 := rs (se 1 (by rfl) ⟨70547, by rfl⟩) R141095
theorem R159799 : Reach 159799 := rs (se 1 (by rfl) ⟨119849, by rfl⟩) R239699
theorem R2093165 : Reach 2093165 := rs (se 3 (by rfl) ⟨392468, by rfl⟩) R784937
theorem R520415 : Reach 520415 := rs (se 1 (by rfl) ⟨390311, by rfl⟩) R780623
theorem R94463 : Reach 94463 := rs (se 1 (by rfl) ⟨70847, by rfl⟩) R141695
theorem R356665 : Reach 356665 := rs (se 2 (by rfl) ⟨133749, by rfl⟩) R267499
theorem R94623 : Reach 94623 := rs (se 1 (by rfl) ⟨70967, by rfl⟩) R141935
theorem R94767 : Reach 94767 := rs (se 1 (by rfl) ⟨71075, by rfl⟩) R142151
theorem R848717 : Reach 848717 := rs (se 3 (by rfl) ⟨159134, by rfl⟩) R318269
theorem R1209275 : Reach 1209275 := rs (se 1 (by rfl) ⟨906956, by rfl⟩) R1813913
theorem R226471 : Reach 226471 := rs (se 1 (by rfl) ⟨169853, by rfl⟩) R339707
theorem R357641 : Reach 357641 := rs (se 2 (by rfl) ⟨134115, by rfl⟩) R268231
theorem R358121 : Reach 358121 := rs (se 2 (by rfl) ⟨134295, by rfl⟩) R268591
theorem R194977 : Reach 194977 := rs (se 2 (by rfl) ⟨73116, by rfl⟩) R146233
theorem R719279 : Reach 719279 := rs (se 1 (by rfl) ⟨539459, by rfl⟩) R1078919
theorem R293503 : Reach 293503 := rs (se 1 (by rfl) ⟨220127, by rfl⟩) R440255
theorem R817879 : Reach 817879 := rs (se 1 (by rfl) ⟨613409, by rfl⟩) R1226819
theorem R131311 : Reach 131311 := rs (se 1 (by rfl) ⟨98483, by rfl⟩) R196967
theorem R98663 : Reach 98663 := rs (se 1 (by rfl) ⟨73997, by rfl⟩) R147995
theorem R852407 : Reach 852407 := rs (se 1 (by rfl) ⟨639305, by rfl⟩) R1278611
theorem R262703 : Reach 262703 := rs (se 1 (by rfl) ⟨197027, by rfl⟩) R394055
theorem R361007 : Reach 361007 := rs (se 1 (by rfl) ⟨270755, by rfl⟩) R541511
theorem R2851549 : Reach 2851549 := rs (se 3 (by rfl) ⟨534665, by rfl⟩) R1069331
theorem R394139 : Reach 394139 := rs (se 1 (by rfl) ⟨295604, by rfl⟩) R591209
theorem R853021 : Reach 853021 := rs (se 3 (by rfl) ⟨159941, by rfl⟩) R319883
theorem R395027 : Reach 395027 := rs (se 1 (by rfl) ⟨296270, by rfl⟩) R592541
theorem R1805003 : Reach 1805003 := rs (se 1 (by rfl) ⟨1353752, by rfl⟩) R2707505
theorem R527431 : Reach 527431 := rs (se 1 (by rfl) ⟨395573, by rfl⟩) R791147
theorem R1314251 : Reach 1314251 := rs (se 1 (by rfl) ⟨985688, by rfl⟩) R1971377
theorem R2133715 : Reach 2133715 := rs (se 1 (by rfl) ⟨1600286, by rfl⟩) R3200573
theorem R1052675 : Reach 1052675 := rs (se 1 (by rfl) ⟨789506, by rfl⟩) R1579013
theorem R2560157 : Reach 2560157 := rs (se 3 (by rfl) ⟨480029, by rfl⟩) R960059
theorem R3215609 : Reach 3215609 := rs (se 2 (by rfl) ⟨1205853, by rfl⟩) R2411707
theorem R201017 : Reach 201017 := rs (se 2 (by rfl) ⟨75381, by rfl⟩) R150763
theorem R3314177 : Reach 3314177 := rs (se 2 (by rfl) ⟨1242816, by rfl⟩) R2485633
theorem R1217065 : Reach 1217065 := rs (se 2 (by rfl) ⟨456399, by rfl⟩) R912799
theorem R103207 : Reach 103207 := rs (se 1 (by rfl) ⟨77405, by rfl⟩) R154811
theorem R398171 : Reach 398171 := rs (se 1 (by rfl) ⟨298628, by rfl⟩) R597257
theorem R235183 : Reach 235183 := rs (se 1 (by rfl) ⟨176387, by rfl⟩) R352775
theorem R137129 : Reach 137129 := rs (se 2 (by rfl) ⟨51423, by rfl⟩) R102847
theorem R1677361 : Reach 1677361 := rs (se 2 (by rfl) ⟨629010, by rfl⟩) R1258021
theorem R104575 : Reach 104575 := rs (se 1 (by rfl) ⟨78431, by rfl⟩) R156863
theorem R105007 : Reach 105007 := rs (se 1 (by rfl) ⟨78755, by rfl⟩) R157511
theorem R137783 : Reach 137783 := rs (se 1 (by rfl) ⟨103337, by rfl⟩) R206675
theorem R6101729 : Reach 6101729 := rs (se 2 (by rfl) ⟨2288148, by rfl⟩) R4576297
theorem R301961 : Reach 301961 := rs (se 2 (by rfl) ⟨113235, by rfl⟩) R226471
theorem R105583 : Reach 105583 := rs (se 1 (by rfl) ⟨79187, by rfl⟩) R158375
theorem R138617 : Reach 138617 := rs (se 2 (by rfl) ⟨51981, by rfl⟩) R103963
theorem R106015 : Reach 106015 := rs (se 1 (by rfl) ⟨79511, by rfl⟩) R159023
theorem R138857 : Reach 138857 := rs (se 2 (by rfl) ⟨52071, by rfl⟩) R104143
theorem R139355 : Reach 139355 := rs (se 1 (by rfl) ⟨104516, by rfl⟩) R209033
theorem R1057049 : Reach 1057049 := rs (se 2 (by rfl) ⟨396393, by rfl⟩) R792787
theorem R565811 : Reach 565811 := rs (se 1 (by rfl) ⟨424358, by rfl⟩) R848717
theorem R238427 : Reach 238427 := rs (se 1 (by rfl) ⟨178820, by rfl⟩) R357641
theorem R140201 : Reach 140201 := rs (se 2 (by rfl) ⟨52575, by rfl⟩) R105151
theorem R1090505 : Reach 1090505 := rs (se 2 (by rfl) ⟨408939, by rfl⟩) R817879
theorem R205793 : Reach 205793 := rs (se 2 (by rfl) ⟨77172, by rfl⟩) R154345
theorem R533537 : Reach 533537 := rs (se 2 (by rfl) ⟨200076, by rfl⟩) R400153
theorem R238747 : Reach 238747 := rs (se 1 (by rfl) ⟨179060, by rfl⟩) R358121
theorem R238889 : Reach 238889 := rs (se 2 (by rfl) ⟨89583, by rfl⟩) R179167
theorem R206207 : Reach 206207 := rs (se 1 (by rfl) ⟨154655, by rfl⟩) R309311
theorem R140855 : Reach 140855 := rs (se 1 (by rfl) ⟨105641, by rfl⟩) R211283
theorem R140903 : Reach 140903 := rs (se 1 (by rfl) ⟨105677, by rfl⟩) R211355
theorem R665225 : Reach 665225 := rs (se 2 (by rfl) ⟨249459, by rfl⟩) R498919
theorem R1058507 : Reach 1058507 := rs (se 1 (by rfl) ⟨793880, by rfl⟩) R1587761
theorem R206567 : Reach 206567 := rs (se 1 (by rfl) ⟨154925, by rfl⟩) R309851
theorem R142331 : Reach 142331 := rs (se 1 (by rfl) ⟨106748, by rfl⟩) R213497
theorem R208097 : Reach 208097 := rs (se 2 (by rfl) ⟨78036, by rfl⟩) R156073
theorem R142571 : Reach 142571 := rs (se 1 (by rfl) ⟨106928, by rfl⟩) R213857
theorem R8039735 : Reach 8039735 := rs (se 1 (by rfl) ⟨6029801, by rfl⟩) R12059603
theorem R961915 : Reach 961915 := rs (se 1 (by rfl) ⟨721436, by rfl⟩) R1442873
theorem R535997 : Reach 535997 := rs (se 3 (by rfl) ⟨100499, by rfl⟩) R200999
theorem R208403 : Reach 208403 := rs (se 1 (by rfl) ⟨156302, by rfl⟩) R312605
theorem R896807 : Reach 896807 := rs (se 1 (by rfl) ⟨672605, by rfl⟩) R1345211
theorem R176107 : Reach 176107 := rs (se 1 (by rfl) ⟨132080, by rfl⟩) R264161
theorem R405587 : Reach 405587 := rs (se 1 (by rfl) ⟨304190, by rfl⟩) R608381
theorem R209231 : Reach 209231 := rs (se 1 (by rfl) ⟨156923, by rfl⟩) R313847
theorem R2306555 : Reach 2306555 := rs (se 1 (by rfl) ⟨1729916, by rfl⟩) R3459833
theorem R1421995 : Reach 1421995 := rs (se 1 (by rfl) ⟨1066496, by rfl⟩) R2132993
theorem R406235 : Reach 406235 := rs (se 1 (by rfl) ⟨304676, by rfl⟩) R609353
theorem R209897 : Reach 209897 := rs (se 2 (by rfl) ⟨78711, by rfl⟩) R157423
theorem R111727 : Reach 111727 := rs (se 1 (by rfl) ⟨83795, by rfl⟩) R167591
theorem R210041 : Reach 210041 := rs (se 2 (by rfl) ⟨78765, by rfl⟩) R157531
theorem R341147 : Reach 341147 := rs (se 1 (by rfl) ⟨255860, by rfl⟩) R511721
theorem R1259059 : Reach 1259059 := rs (se 1 (by rfl) ⟨944294, by rfl⟩) R1888589
theorem R538163 : Reach 538163 := rs (se 1 (by rfl) ⟨403622, by rfl⟩) R807245
theorem R1488451 : Reach 1488451 := rs (se 1 (by rfl) ⟨1116338, by rfl⟩) R2232677
theorem R210815 : Reach 210815 := rs (se 1 (by rfl) ⟨158111, by rfl⟩) R316223
theorem R211067 : Reach 211067 := rs (se 1 (by rfl) ⟨158300, by rfl⟩) R316601
theorem R473303 : Reach 473303 := rs (se 1 (by rfl) ⟨354977, by rfl⟩) R709955
theorem R211337 : Reach 211337 := rs (se 2 (by rfl) ⟨79251, by rfl⟩) R158503
theorem R801535 : Reach 801535 := rs (se 1 (by rfl) ⟨601151, by rfl⟩) R1202303
theorem R998183 : Reach 998183 := rs (se 1 (by rfl) ⟨748637, by rfl⟩) R1497275
theorem R211823 : Reach 211823 := rs (se 1 (by rfl) ⟨158867, by rfl⟩) R317735
theorem R507005 : Reach 507005 := rs (se 3 (by rfl) ⟨95063, by rfl⟩) R190127
theorem R310553 : Reach 310553 := rs (se 2 (by rfl) ⟨116457, by rfl⟩) R232915
theorem R212399 : Reach 212399 := rs (se 1 (by rfl) ⟨159299, by rfl⟩) R318599
theorem R212651 : Reach 212651 := rs (se 1 (by rfl) ⟨159488, by rfl⟩) R318977
theorem R1457875 : Reach 1457875 := rs (se 1 (by rfl) ⟨1093406, by rfl⟩) R2186813
theorem R540371 : Reach 540371 := rs (se 1 (by rfl) ⟨405278, by rfl⟩) R810557
theorem R213065 : Reach 213065 := rs (se 2 (by rfl) ⟨79899, by rfl⟩) R159799
theorem R213371 : Reach 213371 := rs (se 1 (by rfl) ⟨160028, by rfl⟩) R320057
theorem R475553 : Reach 475553 := rs (se 2 (by rfl) ⟨178332, by rfl⟩) R356665
theorem R935675 : Reach 935675 := rs (se 1 (by rfl) ⟨701756, by rfl⟩) R1403513
theorem R313145 : Reach 313145 := rs (se 2 (by rfl) ⟨117429, by rfl⟩) R234859
theorem R1361771 : Reach 1361771 := rs (se 1 (by rfl) ⟨1021328, by rfl⟩) R2042657
theorem R313307 : Reach 313307 := rs (se 1 (by rfl) ⟨234980, by rfl⟩) R469961
theorem R313415 : Reach 313415 := rs (se 1 (by rfl) ⟨235061, by rfl⟩) R470123
theorem R1395443 : Reach 1395443 := rs (se 1 (by rfl) ⟨1046582, by rfl⟩) R2093165
theorem R1362743 : Reach 1362743 := rs (se 1 (by rfl) ⟨1022057, by rfl⟩) R2044115
theorem R346943 : Reach 346943 := rs (se 1 (by rfl) ⟨260207, by rfl⟩) R520415
theorem R806183 : Reach 806183 := rs (se 1 (by rfl) ⟨604637, by rfl⟩) R1209275
theorem R249569 : Reach 249569 := rs (se 2 (by rfl) ⟨93588, by rfl⟩) R187177
theorem R479519 : Reach 479519 := rs (se 1 (by rfl) ⟨359639, by rfl⟩) R719279
theorem R120143 : Reach 120143 := rs (se 1 (by rfl) ⟨90107, by rfl⟩) R180215
theorem R2708873 : Reach 2708873 := rs (se 2 (by rfl) ⟨1015827, by rfl⟩) R2031655
theorem R251495 : Reach 251495 := rs (se 1 (by rfl) ⟨188621, by rfl⟩) R377243
theorem R645083 : Reach 645083 := rs (se 1 (by rfl) ⟨483812, by rfl⟩) R967625
theorem R1169909 : Reach 1169909 := rs (se 5 (by rfl) ⟨54839, by rfl⟩) R109679
theorem R4120001 : Reach 4120001 := rs (se 2 (by rfl) ⟨1545000, by rfl⟩) R3090001
theorem R3825443 : Reach 3825443 := rs (se 1 (by rfl) ⟨2869082, by rfl⟩) R5738165
theorem R1040215 : Reach 1040215 := rs (se 1 (by rfl) ⟨780161, by rfl⟩) R1560323
theorem R319571 : Reach 319571 := rs (se 1 (by rfl) ⟨239678, by rfl⟩) R479357
theorem R319625 : Reach 319625 := rs (se 2 (by rfl) ⟨119859, by rfl⟩) R239719
theorem R1041011 : Reach 1041011 := rs (se 1 (by rfl) ⟨780758, by rfl⟩) R1561517
theorem R680737 : Reach 680737 := rs (se 2 (by rfl) ⟨255276, by rfl⟩) R510553
theorem R2155511 : Reach 2155511 := rs (se 1 (by rfl) ⟨1616633, by rfl⟩) R3233267
theorem R91263 : Reach 91263 := rs (se 1 (by rfl) ⟨68447, by rfl⟩) R136895
theorem R320651 : Reach 320651 := rs (se 1 (by rfl) ⟨240488, by rfl⟩) R480977
theorem R255257 : Reach 255257 := rs (se 2 (by rfl) ⟨95721, by rfl⟩) R191443
theorem R91519 : Reach 91519 := rs (se 1 (by rfl) ⟨68639, by rfl⟩) R137279
theorem R91631 : Reach 91631 := rs (se 1 (by rfl) ⟨68723, by rfl⟩) R137447
theorem R91751 : Reach 91751 := rs (se 1 (by rfl) ⟨68813, by rfl⟩) R137627
theorem R92031 : Reach 92031 := rs (se 1 (by rfl) ⟨69023, by rfl⟩) R138047
theorem R256379 : Reach 256379 := rs (se 1 (by rfl) ⟨192284, by rfl⟩) R384569
theorem R748187 : Reach 748187 := rs (se 1 (by rfl) ⟨561140, by rfl⟩) R1122281
theorem R355387 : Reach 355387 := rs (se 1 (by rfl) ⟨266540, by rfl⟩) R533081
theorem R93743 : Reach 93743 := rs (se 1 (by rfl) ⟨70307, by rfl⟩) R140615
theorem R945851 : Reach 945851 := rs (se 1 (by rfl) ⟨709388, by rfl⟩) R1418777
theorem R94299 : Reach 94299 := rs (se 1 (by rfl) ⟨70724, by rfl⟩) R141449
theorem R586237 : Reach 586237 := rs (se 3 (by rfl) ⟨109919, by rfl⟩) R219839
theorem R94747 : Reach 94747 := rs (se 1 (by rfl) ⟨71060, by rfl⟩) R142121
theorem R94875 : Reach 94875 := rs (se 1 (by rfl) ⟨71156, by rfl⟩) R142313
theorem R390653 : Reach 390653 := rs (se 3 (by rfl) ⟨73247, by rfl⟩) R146495
theorem R259969 : Reach 259969 := rs (se 2 (by rfl) ⟨97488, by rfl⟩) R194977
theorem R1341521 : Reach 1341521 := rs (se 2 (by rfl) ⟨503070, by rfl⟩) R1006141
theorem R391337 : Reach 391337 := rs (se 2 (by rfl) ⟨146751, by rfl⟩) R293503
theorem R227663 : Reach 227663 := rs (se 1 (by rfl) ⟨170747, by rfl⟩) R341495
theorem R262759 : Reach 262759 := rs (se 1 (by rfl) ⟨197069, by rfl⟩) R394139
theorem R263101 : Reach 263101 := rs (se 3 (by rfl) ⟨49331, by rfl⟩) R98663
theorem R623783 : Reach 623783 := rs (se 1 (by rfl) ⟨467837, by rfl⟩) R935675
theorem R263351 : Reach 263351 := rs (se 1 (by rfl) ⟨197513, by rfl⟩) R395027
theorem R231295 : Reach 231295 := rs (se 1 (by rfl) ⟨173471, by rfl⟩) R346943
theorem R1083293 : Reach 1083293 := rs (se 3 (by rfl) ⟨203117, by rfl⟩) R406235
theorem R166379 : Reach 166379 := rs (se 1 (by rfl) ⟨124784, by rfl⟩) R249569
theorem R1706771 : Reach 1706771 := rs (se 1 (by rfl) ⟨1280078, by rfl⟩) R2560157
theorem R134011 : Reach 134011 := rs (se 1 (by rfl) ⟨100508, by rfl⟩) R201017
theorem R265447 : Reach 265447 := rs (se 1 (by rfl) ⟨199085, by rfl⟩) R398171
theorem R1805915 : Reach 1805915 := rs (se 1 (by rfl) ⟨1354436, by rfl⟩) R2708873
theorem R167663 : Reach 167663 := rs (se 1 (by rfl) ⟨125747, by rfl⟩) R251495
theorem R430055 : Reach 430055 := rs (se 1 (by rfl) ⟨322541, by rfl⟩) R645083
theorem R4067819 : Reach 4067819 := rs (se 1 (by rfl) ⟨3050864, by rfl⟩) R6101729
theorem R1282553 : Reach 1282553 := rs (se 2 (by rfl) ⟨480957, by rfl⟩) R961915
theorem R201307 : Reach 201307 := rs (se 1 (by rfl) ⟨150980, by rfl⟩) R301961
theorem R234809 : Reach 234809 := rs (se 2 (by rfl) ⟨88053, by rfl⟩) R176107
theorem R694007 : Reach 694007 := rs (se 1 (by rfl) ⟨520505, by rfl⟩) R1041011
theorem R727003 : Reach 727003 := rs (se 1 (by rfl) ⟨545252, by rfl⟩) R1090505
theorem R137195 : Reach 137195 := rs (se 1 (by rfl) ⟨102896, by rfl⟩) R205793
theorem R170171 : Reach 170171 := rs (se 1 (by rfl) ⟨127628, by rfl⟩) R255257
theorem R137471 : Reach 137471 := rs (se 1 (by rfl) ⟨103103, by rfl⟩) R206207
theorem R137609 : Reach 137609 := rs (se 2 (by rfl) ⟨51603, by rfl⟩) R103207
theorem R137711 : Reach 137711 := rs (se 1 (by rfl) ⟨103283, by rfl⟩) R206567
theorem R498791 : Reach 498791 := rs (se 1 (by rfl) ⟨374093, by rfl⟩) R748187
theorem R1678745 : Reach 1678745 := rs (se 2 (by rfl) ⟨629529, by rfl⟩) R1259059
theorem R2661821 : Reach 2661821 := rs (se 3 (by rfl) ⟨499091, by rfl⟩) R998183
theorem R138731 : Reach 138731 := rs (se 1 (by rfl) ⟨104048, by rfl⟩) R208097
theorem R138935 : Reach 138935 := rs (se 1 (by rfl) ⟨104201, by rfl⟩) R208403
theorem R597871 : Reach 597871 := rs (se 1 (by rfl) ⟨448403, by rfl⟩) R896807
theorem R270391 : Reach 270391 := rs (se 1 (by rfl) ⟨202793, by rfl⟩) R405587
theorem R2236481 : Reach 2236481 := rs (se 2 (by rfl) ⟨838680, by rfl⟩) R1677361
theorem R139433 : Reach 139433 := rs (se 2 (by rfl) ⟨52287, by rfl⟩) R104575
theorem R139487 : Reach 139487 := rs (se 1 (by rfl) ⟨104615, by rfl⟩) R209231
theorem R139931 : Reach 139931 := rs (se 1 (by rfl) ⟨104948, by rfl⟩) R209897
theorem R140009 : Reach 140009 := rs (se 2 (by rfl) ⟨52503, by rfl⟩) R105007
theorem R140027 : Reach 140027 := rs (se 1 (by rfl) ⟨105020, by rfl⟩) R210041
theorem R140543 : Reach 140543 := rs (se 1 (by rfl) ⟨105407, by rfl⟩) R210815
theorem R894347 : Reach 894347 := rs (se 1 (by rfl) ⟨670760, by rfl⟩) R1341521
theorem R140711 : Reach 140711 := rs (se 1 (by rfl) ⟨105533, by rfl⟩) R211067
theorem R140777 : Reach 140777 := rs (se 2 (by rfl) ⟨52791, by rfl⟩) R105583
theorem R140891 : Reach 140891 := rs (se 1 (by rfl) ⟨105668, by rfl⟩) R211337
theorem R141215 : Reach 141215 := rs (se 1 (by rfl) ⟨105911, by rfl⟩) R211823
theorem R141353 : Reach 141353 := rs (se 2 (by rfl) ⟨53007, by rfl⟩) R106015
theorem R338003 : Reach 338003 := rs (se 1 (by rfl) ⟨253502, by rfl⟩) R507005
theorem R207035 : Reach 207035 := rs (se 1 (by rfl) ⟨155276, by rfl⟩) R310553
theorem R1943833 : Reach 1943833 := rs (se 2 (by rfl) ⟨728937, by rfl⟩) R1457875
theorem R141599 : Reach 141599 := rs (se 1 (by rfl) ⟨106199, by rfl⟩) R212399
theorem R141767 : Reach 141767 := rs (se 1 (by rfl) ⟨106325, by rfl⟩) R212651
theorem R1386953 : Reach 1386953 := rs (se 2 (by rfl) ⟨520107, by rfl⟩) R1040215
theorem R142043 : Reach 142043 := rs (se 1 (by rfl) ⟨106532, by rfl⟩) R213065
theorem R142247 : Reach 142247 := rs (se 1 (by rfl) ⟨106685, by rfl⟩) R213371
theorem R568271 : Reach 568271 := rs (se 1 (by rfl) ⟨426203, by rfl⟩) R852407
theorem R175135 : Reach 175135 := rs (se 1 (by rfl) ⟨131351, by rfl⟩) R262703
theorem R240671 : Reach 240671 := rs (se 1 (by rfl) ⟨180503, by rfl⟩) R361007
theorem R208763 : Reach 208763 := rs (se 1 (by rfl) ⟨156572, by rfl⟩) R313145
theorem R700325 : Reach 700325 := rs (se 4 (by rfl) ⟨65655, by rfl⟩) R131311
theorem R208871 : Reach 208871 := rs (se 1 (by rfl) ⟨156653, by rfl⟩) R313307
theorem R208943 : Reach 208943 := rs (se 1 (by rfl) ⟨156707, by rfl⟩) R313415
theorem R930295 : Reach 930295 := rs (se 1 (by rfl) ⟨697721, by rfl⟩) R1395443
theorem R537455 : Reach 537455 := rs (se 1 (by rfl) ⟨403091, by rfl⟩) R806183
theorem R5748029 : Reach 5748029 := rs (se 3 (by rfl) ⟨1077755, by rfl⟩) R2155511
theorem R701783 : Reach 701783 := rs (se 1 (by rfl) ⟨526337, by rfl⟩) R1052675
theorem R2143739 : Reach 2143739 := rs (se 1 (by rfl) ⟨1607804, by rfl⟩) R3215609
theorem R2209451 : Reach 2209451 := rs (se 1 (by rfl) ⟨1657088, by rfl⟩) R3314177
theorem R473849 : Reach 473849 := rs (se 2 (by rfl) ⟨177693, by rfl⟩) R355387
theorem R703241 : Reach 703241 := rs (se 2 (by rfl) ⟨263715, by rfl⟩) R527431
theorem R60833045 : Reach 60833045 := rs (se 6 (by rfl) ⟨1425774, by rfl⟩) R2851549
theorem R213047 : Reach 213047 := rs (se 1 (by rfl) ⟨159785, by rfl⟩) R319571
theorem R213083 : Reach 213083 := rs (se 1 (by rfl) ⟨159812, by rfl⟩) R319625
theorem R704699 : Reach 704699 := rs (se 1 (by rfl) ⟨528524, by rfl⟩) R1057049
theorem R377207 : Reach 377207 := rs (se 1 (by rfl) ⟨282905, by rfl⟩) R565811
theorem R1262141 : Reach 1262141 := rs (se 3 (by rfl) ⟨236651, by rfl⟩) R473303
theorem R1622753 : Reach 1622753 := rs (se 2 (by rfl) ⟨608532, by rfl⟩) R1217065
theorem R213767 : Reach 213767 := rs (se 1 (by rfl) ⟨160325, by rfl⟩) R320651
theorem R443483 : Reach 443483 := rs (se 1 (by rfl) ⟨332612, by rfl⟩) R665225
theorem R705671 : Reach 705671 := rs (se 1 (by rfl) ⟨529253, by rfl⟩) R1058507
theorem R148969 : Reach 148969 := rs (se 2 (by rfl) ⟨55863, by rfl⟩) R111727
theorem R1984601 : Reach 1984601 := rs (se 2 (by rfl) ⟨744225, by rfl⟩) R1488451
theorem R5359823 : Reach 5359823 := rs (se 1 (by rfl) ⟨4019867, by rfl⟩) R8039735
theorem R313577 : Reach 313577 := rs (se 2 (by rfl) ⟨117591, by rfl⟩) R235183
theorem R346625 : Reach 346625 := rs (se 2 (by rfl) ⟨129984, by rfl⟩) R259969
theorem R1068713 : Reach 1068713 := rs (se 2 (by rfl) ⟨400767, by rfl⟩) R801535
theorem R151775 : Reach 151775 := rs (se 1 (by rfl) ⟨113831, by rfl⟩) R227663
theorem R907649 : Reach 907649 := rs (se 2 (by rfl) ⟨340368, by rfl⟩) R680737
theorem R1268141 : Reach 1268141 := rs (se 3 (by rfl) ⟨237776, by rfl⟩) R475553
theorem R907847 : Reach 907847 := rs (se 1 (by rfl) ⟨680885, by rfl⟩) R1361771
theorem R1137361 : Reach 1137361 := rs (se 2 (by rfl) ⟨426510, by rfl⟩) R853021
theorem R318329 : Reach 318329 := rs (se 2 (by rfl) ⟨119373, by rfl⟩) R238747
theorem R1203335 : Reach 1203335 := rs (se 1 (by rfl) ⟨902501, by rfl⟩) R1805003
theorem R908495 : Reach 908495 := rs (se 1 (by rfl) ⟨681371, by rfl⟩) R1362743
theorem R876167 : Reach 876167 := rs (se 1 (by rfl) ⟨657125, by rfl⟩) R1314251
theorem R319679 : Reach 319679 := rs (se 1 (by rfl) ⟨239759, by rfl⟩) R479519
theorem R320381 : Reach 320381 := rs (se 3 (by rfl) ⟨60071, by rfl⟩) R120143
theorem R91419 : Reach 91419 := rs (se 1 (by rfl) ⟨68564, by rfl⟩) R137129
theorem R779939 : Reach 779939 := rs (se 1 (by rfl) ⟨584954, by rfl⟩) R1169909
theorem R91855 : Reach 91855 := rs (se 1 (by rfl) ⟨68891, by rfl⟩) R137783
theorem R92411 : Reach 92411 := rs (se 1 (by rfl) ⟨69308, by rfl⟩) R138617
theorem R2844953 : Reach 2844953 := rs (se 2 (by rfl) ⟨1066857, by rfl⟩) R2133715
theorem R2746667 : Reach 2746667 := rs (se 1 (by rfl) ⟨2060000, by rfl⟩) R4120001
theorem R92571 : Reach 92571 := rs (se 1 (by rfl) ⟨69428, by rfl⟩) R138857
theorem R2550295 : Reach 2550295 := rs (se 1 (by rfl) ⟨1912721, by rfl⟩) R3825443
theorem R92903 : Reach 92903 := rs (se 1 (by rfl) ⟨69677, by rfl⟩) R139355
theorem R158951 : Reach 158951 := rs (se 1 (by rfl) ⟨119213, by rfl⟩) R238427
theorem R93467 : Reach 93467 := rs (se 1 (by rfl) ⟨70100, by rfl⟩) R140201
theorem R781649 : Reach 781649 := rs (se 2 (by rfl) ⟨293118, by rfl⟩) R586237
theorem R355691 : Reach 355691 := rs (se 1 (by rfl) ⟨266768, by rfl⟩) R533537
theorem R159259 : Reach 159259 := rs (se 1 (by rfl) ⟨119444, by rfl⟩) R238889
theorem R1895993 : Reach 1895993 := rs (se 2 (by rfl) ⟨710997, by rfl⟩) R1421995
theorem R683677 : Reach 683677 := rs (se 3 (by rfl) ⟨128189, by rfl⟩) R256379
theorem R93903 : Reach 93903 := rs (se 1 (by rfl) ⟨70427, by rfl⟩) R140855
theorem R93935 : Reach 93935 := rs (se 1 (by rfl) ⟨70451, by rfl⟩) R140903
theorem R94887 : Reach 94887 := rs (se 1 (by rfl) ⟨71165, by rfl⟩) R142331
theorem R95047 : Reach 95047 := rs (se 1 (by rfl) ⟨71285, by rfl⟩) R142571
theorem R357331 : Reach 357331 := rs (se 1 (by rfl) ⟨267998, by rfl⟩) R535997
theorem R1537703 : Reach 1537703 := rs (se 1 (by rfl) ⟨1153277, by rfl⟩) R2306555
theorem R227431 : Reach 227431 := rs (se 1 (by rfl) ⟨170573, by rfl⟩) R341147
theorem R260435 : Reach 260435 := rs (se 1 (by rfl) ⟨195326, by rfl⟩) R390653
theorem R358775 : Reach 358775 := rs (se 1 (by rfl) ⟨269081, by rfl⟩) R538163
theorem R260891 : Reach 260891 := rs (se 1 (by rfl) ⟨195668, by rfl⟩) R391337
theorem R2522269 : Reach 2522269 := rs (se 3 (by rfl) ⟨472925, by rfl⟩) R945851
theorem R360247 : Reach 360247 := rs (se 1 (by rfl) ⟨270185, by rfl⟩) R540371
theorem R360521 : Reach 360521 := rs (se 2 (by rfl) ⟨135195, by rfl⟩) R270391
theorem R1081835 : Reach 1081835 := rs (se 1 (by rfl) ⟨811376, by rfl⟩) R1622753
theorem R1212965 : Reach 1212965 := rs (se 4 (by rfl) ⟨113715, by rfl⟩) R227431
theorem R295655 : Reach 295655 := rs (se 1 (by rfl) ⟨221741, by rfl⟩) R443483
theorem R722195 : Reach 722195 := rs (se 1 (by rfl) ⟨541646, by rfl⟩) R1083293
theorem R3573215 : Reach 3573215 := rs (se 1 (by rfl) ⟨2679911, by rfl⟩) R5359823
theorem R231083 : Reach 231083 := rs (se 1 (by rfl) ⟨173312, by rfl⟩) R346625
theorem R198625 : Reach 198625 := rs (se 2 (by rfl) ⟨74484, by rfl⟩) R148969
theorem R101183 : Reach 101183 := rs (se 1 (by rfl) ⟨75887, by rfl⟩) R151775
theorem R855035 : Reach 855035 := rs (se 1 (by rfl) ⟨641276, by rfl⟩) R1282553
theorem R2591777 : Reach 2591777 := rs (se 2 (by rfl) ⟨971916, by rfl⟩) R1943833
theorem R462671 : Reach 462671 := rs (se 1 (by rfl) ⟨347003, by rfl⟩) R694007
theorem R233513 : Reach 233513 := rs (se 2 (by rfl) ⟨87567, by rfl⟩) R175135
theorem R332527 : Reach 332527 := rs (se 1 (by rfl) ⟨249395, by rfl⟩) R498791
theorem R1774547 : Reach 1774547 := rs (se 1 (by rfl) ⟨1330910, by rfl⟩) R2661821
theorem R268409 : Reach 268409 := rs (se 2 (by rfl) ⟨100653, by rfl⟩) R201307
theorem R694493 : Reach 694493 := rs (se 3 (by rfl) ⟨130217, by rfl⟩) R260435
theorem R596231 : Reach 596231 := rs (se 1 (by rfl) ⟨447173, by rfl⟩) R894347
theorem R138023 : Reach 138023 := rs (se 1 (by rfl) ⟨103517, by rfl⟩) R207035
theorem R924635 : Reach 924635 := rs (se 1 (by rfl) ⟨693476, by rfl⟩) R1386953
theorem R105967 : Reach 105967 := rs (se 1 (by rfl) ⟨79475, by rfl⟩) R158951
theorem R237127 : Reach 237127 := rs (se 1 (by rfl) ⟨177845, by rfl⟩) R355691
theorem R139175 : Reach 139175 := rs (se 1 (by rfl) ⟨104381, by rfl⟩) R208763
theorem R466883 : Reach 466883 := rs (se 1 (by rfl) ⟨350162, by rfl⟩) R700325
theorem R139247 : Reach 139247 := rs (se 1 (by rfl) ⟨104435, by rfl⟩) R208871
theorem R139295 : Reach 139295 := rs (se 1 (by rfl) ⟨104471, by rfl⟩) R208943
theorem R467855 : Reach 467855 := rs (se 1 (by rfl) ⟨350891, by rfl⟩) R701783
theorem R1516481 : Reach 1516481 := rs (se 2 (by rfl) ⟨568680, by rfl⟩) R1137361
theorem R1025135 : Reach 1025135 := rs (se 1 (by rfl) ⟨768851, by rfl⟩) R1537703
theorem R239183 : Reach 239183 := rs (se 1 (by rfl) ⟨179387, by rfl⟩) R358775
theorem R468827 : Reach 468827 := rs (se 1 (by rfl) ⟨351620, by rfl⟩) R703241
theorem R173927 : Reach 173927 := rs (se 1 (by rfl) ⟨130445, by rfl⟩) R260891
theorem R797161 : Reach 797161 := rs (se 2 (by rfl) ⟨298935, by rfl⟩) R597871
theorem R142031 : Reach 142031 := rs (se 1 (by rfl) ⟨106523, by rfl⟩) R213047
theorem R142055 : Reach 142055 := rs (se 1 (by rfl) ⟨106541, by rfl⟩) R213083
theorem R469799 : Reach 469799 := rs (se 1 (by rfl) ⟨352349, by rfl⟩) R704699
theorem R142511 : Reach 142511 := rs (se 1 (by rfl) ⟨106883, by rfl⟩) R213767
theorem R470447 : Reach 470447 := rs (se 1 (by rfl) ⟨352835, by rfl⟩) R705671
theorem R1323067 : Reach 1323067 := rs (se 1 (by rfl) ⟨992300, by rfl⟩) R1984601
theorem R209051 : Reach 209051 := rs (se 1 (by rfl) ⟨156788, by rfl⟩) R313577
theorem R111775 : Reach 111775 := rs (se 1 (by rfl) ⟨83831, by rfl⟩) R167663
theorem R308393 : Reach 308393 := rs (se 2 (by rfl) ⟨115647, by rfl⟩) R231295
theorem R4961573 : Reach 4961573 := rs (se 4 (by rfl) ⟨465147, by rfl⟩) R930295
theorem R702269 : Reach 702269 := rs (se 3 (by rfl) ⟨131675, by rfl⟩) R263351
theorem R178681 : Reach 178681 := rs (se 2 (by rfl) ⟨67005, by rfl⟩) R134011
theorem R113447 : Reach 113447 := rs (se 1 (by rfl) ⟨85085, by rfl⟩) R170171
theorem R605099 : Reach 605099 := rs (se 1 (by rfl) ⟨453824, by rfl⟩) R907649
theorem R605231 : Reach 605231 := rs (se 1 (by rfl) ⟨453923, by rfl⟩) R907847
theorem R212219 : Reach 212219 := rs (se 1 (by rfl) ⟨159164, by rfl⟩) R318329
theorem R212345 : Reach 212345 := rs (se 2 (by rfl) ⟨79629, by rfl⟩) R159259
theorem R802223 : Reach 802223 := rs (se 1 (by rfl) ⟨601667, by rfl⟩) R1203335
theorem R605663 : Reach 605663 := rs (se 1 (by rfl) ⟨454247, by rfl⟩) R908495
theorem R1490987 : Reach 1490987 := rs (se 1 (by rfl) ⟨1118240, by rfl⟩) R2236481
theorem R213119 : Reach 213119 := rs (se 1 (by rfl) ⟨159839, by rfl⟩) R319679
theorem R213587 : Reach 213587 := rs (se 1 (by rfl) ⟨160190, by rfl⟩) R320381
theorem R7324445 : Reach 7324445 := rs (se 3 (by rfl) ⟨1373333, by rfl⟩) R2746667
theorem R13452101 : Reach 13452101 := rs (se 4 (by rfl) ⟨1261134, by rfl⟩) R2522269
theorem R476441 : Reach 476441 := rs (se 2 (by rfl) ⟨178665, by rfl⟩) R357331
theorem R443677 : Reach 443677 := rs (se 3 (by rfl) ⟨83189, by rfl⟩) R166379
theorem R378847 : Reach 378847 := rs (se 1 (by rfl) ⟨284135, by rfl⟩) R568271
theorem R1263995 : Reach 1263995 := rs (se 1 (by rfl) ⟨947996, by rfl⟩) R1895993
theorem R969337 : Reach 969337 := rs (se 2 (by rfl) ⟨363501, by rfl⟩) R727003
theorem R1429159 : Reach 1429159 := rs (se 1 (by rfl) ⟨1071869, by rfl⟩) R2143739
theorem R4476653 : Reach 4476653 := rs (se 3 (by rfl) ⟨839372, by rfl⟩) R1678745
theorem R315899 : Reach 315899 := rs (se 1 (by rfl) ⟨236924, by rfl⟩) R473849
theorem R40555363 : Reach 40555363 := rs (se 1 (by rfl) ⟨30416522, by rfl⟩) R60833045
theorem R480329 : Reach 480329 := rs (se 2 (by rfl) ⟨180123, by rfl⟩) R360247
theorem R251471 : Reach 251471 := rs (se 1 (by rfl) ⟨188603, by rfl⟩) R377207
theorem R841427 : Reach 841427 := rs (se 1 (by rfl) ⟨631070, by rfl⟩) R1262141
theorem R415855 : Reach 415855 := rs (se 1 (by rfl) ⟨311891, by rfl⟩) R623783
theorem R350345 : Reach 350345 := rs (se 2 (by rfl) ⟨131379, by rfl⟩) R262759
theorem R350801 : Reach 350801 := rs (se 2 (by rfl) ⟨131550, by rfl⟩) R263101
theorem R1203943 : Reach 1203943 := rs (se 1 (by rfl) ⟨902957, by rfl⟩) R1805915
theorem R712475 : Reach 712475 := rs (se 1 (by rfl) ⟨534356, by rfl⟩) R1068713
theorem R286703 : Reach 286703 := rs (se 1 (by rfl) ⟨215027, by rfl⟩) R430055
theorem R2711879 : Reach 2711879 := rs (se 1 (by rfl) ⟨2033909, by rfl⟩) R4067819
theorem R3400393 : Reach 3400393 := rs (se 2 (by rfl) ⟨1275147, by rfl⟩) R2550295
theorem R156539 : Reach 156539 := rs (se 1 (by rfl) ⟨117404, by rfl⟩) R234809
theorem R91463 : Reach 91463 := rs (se 1 (by rfl) ⟨68597, by rfl⟩) R137195
theorem R91647 : Reach 91647 := rs (se 1 (by rfl) ⟨68735, by rfl⟩) R137471
theorem R91739 : Reach 91739 := rs (se 1 (by rfl) ⟨68804, by rfl⟩) R137609
theorem R353929 : Reach 353929 := rs (se 2 (by rfl) ⟨132723, by rfl⟩) R265447
theorem R91807 : Reach 91807 := rs (se 1 (by rfl) ⟨68855, by rfl⟩) R137711
theorem R5891869 : Reach 5891869 := rs (se 3 (by rfl) ⟨1104725, by rfl⟩) R2209451
theorem R13526837 : Reach 13526837 := rs (se 5 (by rfl) ⟨634070, by rfl⟩) R1268141
theorem R911569 : Reach 911569 := rs (se 2 (by rfl) ⟨341838, by rfl⟩) R683677
theorem R92487 : Reach 92487 := rs (se 1 (by rfl) ⟨69365, by rfl⟩) R138731
theorem R584111 : Reach 584111 := rs (se 1 (by rfl) ⟨438083, by rfl⟩) R876167
theorem R92623 : Reach 92623 := rs (se 1 (by rfl) ⟨69467, by rfl⟩) R138935
theorem R92955 : Reach 92955 := rs (se 1 (by rfl) ⟨69716, by rfl⟩) R139433
theorem R92991 : Reach 92991 := rs (se 1 (by rfl) ⟨69743, by rfl⟩) R139487
theorem R93287 : Reach 93287 := rs (se 1 (by rfl) ⟨69965, by rfl⟩) R139931
theorem R93339 : Reach 93339 := rs (se 1 (by rfl) ⟨70004, by rfl⟩) R140009
theorem R93351 : Reach 93351 := rs (se 1 (by rfl) ⟨70013, by rfl⟩) R140027
theorem R93695 : Reach 93695 := rs (se 1 (by rfl) ⟨70271, by rfl⟩) R140543
theorem R93807 : Reach 93807 := rs (se 1 (by rfl) ⟨70355, by rfl⟩) R140711
theorem R93851 : Reach 93851 := rs (se 1 (by rfl) ⟨70388, by rfl⟩) R140777
theorem R93927 : Reach 93927 := rs (se 1 (by rfl) ⟨70445, by rfl⟩) R140891
theorem R519959 : Reach 519959 := rs (se 1 (by rfl) ⟨389969, by rfl⟩) R779939
theorem R94143 : Reach 94143 := rs (se 1 (by rfl) ⟨70607, by rfl⟩) R141215
theorem R94235 : Reach 94235 := rs (se 1 (by rfl) ⟨70676, by rfl⟩) R141353
theorem R225335 : Reach 225335 := rs (se 1 (by rfl) ⟨169001, by rfl⟩) R338003
theorem R1896635 : Reach 1896635 := rs (se 1 (by rfl) ⟨1422476, by rfl⟩) R2844953
theorem R94399 : Reach 94399 := rs (se 1 (by rfl) ⟨70799, by rfl⟩) R141599
theorem R94511 : Reach 94511 := rs (se 1 (by rfl) ⟨70883, by rfl⟩) R141767
theorem R94695 : Reach 94695 := rs (se 1 (by rfl) ⟨71021, by rfl⟩) R142043
theorem R94831 : Reach 94831 := rs (se 1 (by rfl) ⟨71123, by rfl⟩) R142247
theorem R160447 : Reach 160447 := rs (se 1 (by rfl) ⟨120335, by rfl⟩) R240671
theorem R4551389 : Reach 4551389 := rs (se 3 (by rfl) ⟨853385, by rfl⟩) R1706771
theorem R521099 : Reach 521099 := rs (se 1 (by rfl) ⟨390824, by rfl⟩) R781649
theorem R358303 : Reach 358303 := rs (se 1 (by rfl) ⟨268727, by rfl⟩) R537455
theorem R3832019 : Reach 3832019 := rs (se 1 (by rfl) ⟨2874014, by rfl⟩) R5748029
theorem R721223 : Reach 721223 := rs (se 1 (by rfl) ⟨540917, by rfl⟩) R1081835
theorem R4882963 : Reach 4882963 := rs (se 1 (by rfl) ⟨3662222, by rfl⟩) R7324445
theorem R591569 : Reach 591569 := rs (se 2 (by rfl) ⟨221838, by rfl⟩) R443677
theorem R788413 : Reach 788413 := rs (se 3 (by rfl) ⟨147827, by rfl⟩) R295655
theorem R2984435 : Reach 2984435 := rs (se 1 (by rfl) ⟨2238326, by rfl⟩) R4476653
theorem R264833 : Reach 264833 := rs (se 2 (by rfl) ⟨99312, by rfl⟩) R198625
theorem R1215425 : Reach 1215425 := rs (se 2 (by rfl) ⟨455784, by rfl⟩) R911569
theorem R1183031 : Reach 1183031 := rs (se 1 (by rfl) ⟨887273, by rfl⟩) R1774547
theorem R560951 : Reach 560951 := rs (se 1 (by rfl) ⟨420713, by rfl⟩) R841427
theorem R233563 : Reach 233563 := rs (se 1 (by rfl) ⟨175172, by rfl⟩) R350345
theorem R462995 : Reach 462995 := rs (se 1 (by rfl) ⟨347246, by rfl⟩) R694493
theorem R397487 : Reach 397487 := rs (se 1 (by rfl) ⟨298115, by rfl⟩) R596231
theorem R233867 : Reach 233867 := rs (se 1 (by rfl) ⟨175400, by rfl⟩) R350801
theorem R1905545 : Reach 1905545 := rs (se 2 (by rfl) ⟨714579, by rfl⟩) R1429159
theorem R463805 : Reach 463805 := rs (se 3 (by rfl) ⟨86963, by rfl⟩) R173927
theorem R1807919 : Reach 1807919 := rs (se 1 (by rfl) ⟨1355939, by rfl⟩) R2711879
theorem R104359 : Reach 104359 := rs (se 1 (by rfl) ⟨78269, by rfl⟩) R156539
theorem R54073817 : Reach 54073817 := rs (se 2 (by rfl) ⟨20277681, by rfl⟩) R40555363
theorem R9017891 : Reach 9017891 := rs (se 1 (by rfl) ⟨6763418, by rfl⟩) R13526837
theorem R302525 : Reach 302525 := rs (se 3 (by rfl) ⟨56723, by rfl⟩) R113447
theorem R269821 : Reach 269821 := rs (se 3 (by rfl) ⟨50591, by rfl⟩) R101183
theorem R565157 : Reach 565157 := rs (se 4 (by rfl) ⟨52983, by rfl⟩) R105967
theorem R139367 : Reach 139367 := rs (se 1 (by rfl) ⟨104525, by rfl⟩) R209051
theorem R238241 : Reach 238241 := rs (se 2 (by rfl) ⟨89340, by rfl⟩) R178681
theorem R205595 : Reach 205595 := rs (se 1 (by rfl) ⟨154196, by rfl⟩) R308393
theorem R468179 : Reach 468179 := rs (se 1 (by rfl) ⟨351134, by rfl⟩) R702269
theorem R403399 : Reach 403399 := rs (se 1 (by rfl) ⟨302549, by rfl⟩) R605099
theorem R403487 : Reach 403487 := rs (se 1 (by rfl) ⟨302615, by rfl⟩) R605231
theorem R141479 : Reach 141479 := rs (se 1 (by rfl) ⟨106109, by rfl⟩) R212219
theorem R141563 : Reach 141563 := rs (se 1 (by rfl) ⟨106172, by rfl⟩) R212345
theorem R534815 : Reach 534815 := rs (se 1 (by rfl) ⟨401111, by rfl⟩) R802223
theorem R403775 : Reach 403775 := rs (se 1 (by rfl) ⟨302831, by rfl⟩) R605663
theorem R240347 : Reach 240347 := rs (se 1 (by rfl) ⟨180260, by rfl⟩) R360521
theorem R142079 : Reach 142079 := rs (se 1 (by rfl) ⟨106559, by rfl⟩) R213119
theorem R3975965 : Reach 3975965 := rs (se 3 (by rfl) ⟨745493, by rfl⟩) R1490987
theorem R142391 : Reach 142391 := rs (se 1 (by rfl) ⟨106793, by rfl⟩) R213587
theorem R4533857 : Reach 4533857 := rs (se 2 (by rfl) ⟨1700196, by rfl⟩) R3400393
theorem R570023 : Reach 570023 := rs (se 1 (by rfl) ⟨427517, by rfl⟩) R855035
theorem R471905 : Reach 471905 := rs (se 2 (by rfl) ⟨176964, by rfl⟩) R353929
theorem R308447 : Reach 308447 := rs (se 1 (by rfl) ⟨231335, by rfl⟩) R462671
theorem R505129 : Reach 505129 := rs (se 2 (by rfl) ⟨189423, by rfl⟩) R378847
theorem R210599 : Reach 210599 := rs (se 1 (by rfl) ⟨157949, by rfl⟩) R315899
theorem R1062881 : Reach 1062881 := rs (se 2 (by rfl) ⟨398580, by rfl⟩) R797161
theorem R1292449 : Reach 1292449 := rs (se 2 (by rfl) ⟨484668, by rfl⟩) R969337
theorem R178939 : Reach 178939 := rs (se 1 (by rfl) ⟨134204, by rfl⟩) R268409
theorem R670589 : Reach 670589 := rs (se 3 (by rfl) ⟨125735, by rfl⟩) R251471
theorem R474983 : Reach 474983 := rs (se 1 (by rfl) ⟨356237, by rfl⟩) R712475
theorem R311255 : Reach 311255 := rs (se 1 (by rfl) ⟨233441, by rfl⟩) R466883
theorem R311903 : Reach 311903 := rs (se 1 (by rfl) ⟨233927, by rfl⟩) R467855
theorem R213929 : Reach 213929 := rs (se 2 (by rfl) ⟨80223, by rfl⟩) R160447
theorem R443369 : Reach 443369 := rs (se 2 (by rfl) ⟨166263, by rfl⟩) R332527
theorem R312551 : Reach 312551 := rs (se 1 (by rfl) ⟨234413, by rfl⟩) R468827
theorem R149033 : Reach 149033 := rs (se 2 (by rfl) ⟨55887, by rfl⟩) R111775
theorem R313199 : Reach 313199 := rs (se 1 (by rfl) ⟨234899, by rfl⟩) R469799
theorem R313631 : Reach 313631 := rs (se 1 (by rfl) ⟨235223, by rfl⟩) R470447
theorem R346639 : Reach 346639 := rs (se 1 (by rfl) ⟨259979, by rfl⟩) R519959
theorem R477737 : Reach 477737 := rs (se 2 (by rfl) ⟨179151, by rfl⟩) R358303
theorem R150223 : Reach 150223 := rs (se 1 (by rfl) ⟨112667, by rfl⟩) R225335
theorem R1264423 : Reach 1264423 := rs (se 1 (by rfl) ⟨948317, by rfl⟩) R1896635
theorem R3034259 : Reach 3034259 := rs (se 1 (by rfl) ⟨2275694, by rfl⟩) R4551389
theorem R347399 : Reach 347399 := rs (se 1 (by rfl) ⟨260549, by rfl⟩) R521099
theorem R316169 : Reach 316169 := rs (se 2 (by rfl) ⟨118563, by rfl⟩) R237127
theorem R808643 : Reach 808643 := rs (se 1 (by rfl) ⟨606482, by rfl⟩) R1212965
theorem R8968067 : Reach 8968067 := rs (se 1 (by rfl) ⟨6726050, by rfl⟩) R13452101
theorem R481463 : Reach 481463 := rs (se 1 (by rfl) ⟨361097, by rfl⟩) R722195
theorem R317627 : Reach 317627 := rs (se 1 (by rfl) ⟨238220, by rfl⟩) R476441
theorem R2382143 : Reach 2382143 := rs (se 1 (by rfl) ⟨1786607, by rfl⟩) R3573215
theorem R154055 : Reach 154055 := rs (se 1 (by rfl) ⟨115541, by rfl⟩) R231083
theorem R842663 : Reach 842663 := rs (se 1 (by rfl) ⟨631997, by rfl⟩) R1263995
theorem R1727851 : Reach 1727851 := rs (se 1 (by rfl) ⟨1295888, by rfl⟩) R2591777
theorem R7855825 : Reach 7855825 := rs (se 2 (by rfl) ⟨2945934, by rfl⟩) R5891869
theorem R155675 : Reach 155675 := rs (se 1 (by rfl) ⟨116756, by rfl⟩) R233513
theorem R320219 : Reach 320219 := rs (se 1 (by rfl) ⟨240164, by rfl⟩) R480329
theorem R92015 : Reach 92015 := rs (se 1 (by rfl) ⟨69011, by rfl⟩) R138023
theorem R616423 : Reach 616423 := rs (se 1 (by rfl) ⟨462317, by rfl⟩) R924635
theorem R92783 : Reach 92783 := rs (se 1 (by rfl) ⟨69587, by rfl⟩) R139175
theorem R92831 : Reach 92831 := rs (se 1 (by rfl) ⟨69623, by rfl⟩) R139247
theorem R191135 : Reach 191135 := rs (se 1 (by rfl) ⟨143351, by rfl⟩) R286703
theorem R92863 : Reach 92863 := rs (se 1 (by rfl) ⟨69647, by rfl⟩) R139295
theorem R1764089 : Reach 1764089 := rs (se 2 (by rfl) ⟨661533, by rfl⟩) R1323067
theorem R1010987 : Reach 1010987 := rs (se 1 (by rfl) ⟨758240, by rfl⟩) R1516481
theorem R683423 : Reach 683423 := rs (se 1 (by rfl) ⟨512567, by rfl⟩) R1025135
theorem R159455 : Reach 159455 := rs (se 1 (by rfl) ⟨119591, by rfl⟩) R239183
theorem R389407 : Reach 389407 := rs (se 1 (by rfl) ⟨292055, by rfl⟩) R584111
theorem R94687 : Reach 94687 := rs (se 1 (by rfl) ⟨71015, by rfl⟩) R142031
theorem R94703 : Reach 94703 := rs (se 1 (by rfl) ⟨71027, by rfl⟩) R142055
theorem R95007 : Reach 95007 := rs (se 1 (by rfl) ⟨71255, by rfl⟩) R142511
theorem R554473 : Reach 554473 := rs (se 2 (by rfl) ⟨207927, by rfl⟩) R415855
theorem R3307715 : Reach 3307715 := rs (se 1 (by rfl) ⟨2480786, by rfl⟩) R4961573
theorem R2554679 : Reach 2554679 := rs (se 1 (by rfl) ⟨1916009, by rfl⟩) R3832019
theorem R1605257 : Reach 1605257 := rs (se 2 (by rfl) ⟨601971, by rfl⟩) R1203943
theorem R295579 : Reach 295579 := rs (se 1 (by rfl) ⟨221684, by rfl⟩) R443369
theorem R99355 : Reach 99355 := rs (se 1 (by rfl) ⟨74516, by rfl⟩) R149033
theorem R394379 : Reach 394379 := rs (se 1 (by rfl) ⟨295784, by rfl⟩) R591569
theorem R231599 : Reach 231599 := rs (se 1 (by rfl) ⟨173699, by rfl⟩) R347399
theorem R788687 : Reach 788687 := rs (se 1 (by rfl) ⟨591515, by rfl⟩) R1183031
theorem R1051217 : Reach 1051217 := rs (se 2 (by rfl) ⟨394206, by rfl⟩) R788413
theorem R821897 : Reach 821897 := rs (se 2 (by rfl) ⟨308211, by rfl⟩) R616423
theorem R462185 : Reach 462185 := rs (se 2 (by rfl) ⟨173319, by rfl⟩) R346639
theorem R200297 : Reach 200297 := rs (se 2 (by rfl) ⟨75111, by rfl⟩) R150223
theorem R102703 : Reach 102703 := rs (se 1 (by rfl) ⟨77027, by rfl⟩) R154055
theorem R36049211 : Reach 36049211 := rs (se 1 (by rfl) ⟨27036908, by rfl⟩) R54073817
theorem R561775 : Reach 561775 := rs (se 1 (by rfl) ⟨421331, by rfl⟩) R842663
theorem R201683 : Reach 201683 := rs (se 1 (by rfl) ⟨151262, by rfl⟩) R302525
theorem R103783 : Reach 103783 := rs (se 1 (by rfl) ⟨77837, by rfl⟩) R155675
theorem R137063 : Reach 137063 := rs (se 1 (by rfl) ⟨102797, by rfl⟩) R205595
theorem R268991 : Reach 268991 := rs (se 1 (by rfl) ⟨201743, by rfl⟩) R403487
theorem R269183 : Reach 269183 := rs (se 1 (by rfl) ⟨201887, by rfl⟩) R403775
theorem R3022571 : Reach 3022571 := rs (se 1 (by rfl) ⟨2266928, by rfl⟩) R4533857
theorem R106303 : Reach 106303 := rs (se 1 (by rfl) ⟨79727, by rfl⟩) R159455
theorem R139145 : Reach 139145 := rs (se 2 (by rfl) ⟨52179, by rfl⟩) R104359
theorem R205631 : Reach 205631 := rs (se 1 (by rfl) ⟨154223, by rfl⟩) R308447
theorem R238585 : Reach 238585 := rs (se 2 (by rfl) ⟨89469, by rfl⟩) R178939
theorem R140399 : Reach 140399 := rs (se 1 (by rfl) ⟨105299, by rfl⟩) R210599
theorem R2205143 : Reach 2205143 := rs (se 1 (by rfl) ⟨1653857, by rfl⟩) R3307715
theorem R2303801 : Reach 2303801 := rs (se 2 (by rfl) ⟨863925, by rfl⟩) R1727851
theorem R207503 : Reach 207503 := rs (se 1 (by rfl) ⟨155627, by rfl⟩) R311255
theorem R207935 : Reach 207935 := rs (se 1 (by rfl) ⟨155951, by rfl⟩) R311903
theorem R1059965 : Reach 1059965 := rs (se 3 (by rfl) ⟨198743, by rfl⟩) R397487
theorem R142619 : Reach 142619 := rs (se 1 (by rfl) ⟨106964, by rfl⟩) R213929
theorem R208367 : Reach 208367 := rs (se 1 (by rfl) ⟨156275, by rfl⟩) R312551
theorem R208799 : Reach 208799 := rs (se 1 (by rfl) ⟨156599, by rfl⟩) R313199
theorem R209087 : Reach 209087 := rs (se 1 (by rfl) ⟨156815, by rfl⟩) R313631
theorem R176555 : Reach 176555 := rs (se 1 (by rfl) ⟨132416, by rfl⟩) R264833
theorem R373967 : Reach 373967 := rs (se 1 (by rfl) ⟨280475, by rfl⟩) R560951
theorem R308663 : Reach 308663 := rs (se 1 (by rfl) ⟨231497, by rfl⟩) R462995
theorem R210779 : Reach 210779 := rs (se 1 (by rfl) ⟨158084, by rfl⟩) R316169
theorem R309203 : Reach 309203 := rs (se 1 (by rfl) ⟨231902, by rfl⟩) R463805
theorem R1685897 : Reach 1685897 := rs (se 2 (by rfl) ⟨632211, by rfl⟩) R1264423
theorem R539095 : Reach 539095 := rs (se 1 (by rfl) ⟨404321, by rfl⟩) R808643
theorem R5978711 : Reach 5978711 := rs (se 1 (by rfl) ⟨4484033, by rfl⟩) R8968067
theorem R211751 : Reach 211751 := rs (se 1 (by rfl) ⟨158813, by rfl⟩) R317627
theorem R6011927 : Reach 6011927 := rs (se 1 (by rfl) ⟨4508945, by rfl⟩) R9017891
theorem R311417 : Reach 311417 := rs (se 2 (by rfl) ⟨116781, by rfl⟩) R233563
theorem R213479 : Reach 213479 := rs (se 1 (by rfl) ⟨160109, by rfl⟩) R320219
theorem R312119 : Reach 312119 := rs (se 1 (by rfl) ⟨234089, by rfl⟩) R468179
theorem R673505 : Reach 673505 := rs (se 2 (by rfl) ⟨252564, by rfl⟩) R505129
theorem R739297 : Reach 739297 := rs (se 2 (by rfl) ⟨277236, by rfl⟩) R554473
theorem R673991 : Reach 673991 := rs (se 1 (by rfl) ⟨505493, by rfl⟩) R1010987
theorem R1723265 : Reach 1723265 := rs (se 2 (by rfl) ⟨646224, by rfl⟩) R1292449
theorem R380015 : Reach 380015 := rs (se 1 (by rfl) ⟨285011, by rfl⟩) R570023
theorem R314603 : Reach 314603 := rs (se 1 (by rfl) ⟨235952, by rfl⟩) R471905
theorem R708587 : Reach 708587 := rs (se 1 (by rfl) ⟨531440, by rfl⟩) R1062881
theorem R447059 : Reach 447059 := rs (se 1 (by rfl) ⟨335294, by rfl⟩) R670589
theorem R10474433 : Reach 10474433 := rs (se 2 (by rfl) ⟨3927912, by rfl⟩) R7855825
theorem R2151461 : Reach 2151461 := rs (se 4 (by rfl) ⟨201699, by rfl⟩) R403399
theorem R1070171 : Reach 1070171 := rs (se 1 (by rfl) ⟨802628, by rfl⟩) R1605257
theorem R316655 : Reach 316655 := rs (se 1 (by rfl) ⟨237491, by rfl⟩) R474983
theorem R480815 : Reach 480815 := rs (se 1 (by rfl) ⟨360611, by rfl⟩) R721223
theorem R6510617 : Reach 6510617 := rs (se 2 (by rfl) ⟨2441481, by rfl⟩) R4882963
theorem R1989623 : Reach 1989623 := rs (se 1 (by rfl) ⟨1492217, by rfl⟩) R2984435
theorem R318491 : Reach 318491 := rs (se 1 (by rfl) ⟨238868, by rfl⟩) R477737
theorem R810283 : Reach 810283 := rs (se 1 (by rfl) ⟨607712, by rfl⟩) R1215425
theorem R2022839 : Reach 2022839 := rs (se 1 (by rfl) ⟨1517129, by rfl⟩) R3034259
theorem R155911 : Reach 155911 := rs (se 1 (by rfl) ⟨116933, by rfl⟩) R233867
theorem R1270363 : Reach 1270363 := rs (se 1 (by rfl) ⟨952772, by rfl⟩) R1905545
theorem R1205279 : Reach 1205279 := rs (se 1 (by rfl) ⟨903959, by rfl⟩) R1807919
theorem R320975 : Reach 320975 := rs (se 1 (by rfl) ⟨240731, by rfl⟩) R481463
theorem R92911 : Reach 92911 := rs (se 1 (by rfl) ⟨69683, by rfl⟩) R139367
theorem R519209 : Reach 519209 := rs (se 2 (by rfl) ⟨194703, by rfl⟩) R389407
theorem R158827 : Reach 158827 := rs (se 1 (by rfl) ⟨119120, by rfl⟩) R238241
theorem R6352381 : Reach 6352381 := rs (se 3 (by rfl) ⟨1191071, by rfl⟩) R2382143
theorem R94319 : Reach 94319 := rs (se 1 (by rfl) ⟨70739, by rfl⟩) R141479
theorem R94375 : Reach 94375 := rs (se 1 (by rfl) ⟨70781, by rfl⟩) R141563
theorem R356543 : Reach 356543 := rs (se 1 (by rfl) ⟨267407, by rfl⟩) R534815
theorem R127423 : Reach 127423 := rs (se 1 (by rfl) ⟨95567, by rfl⟩) R191135
theorem R160231 : Reach 160231 := rs (se 1 (by rfl) ⟨120173, by rfl⟩) R240347
theorem R1176059 : Reach 1176059 := rs (se 1 (by rfl) ⟨882044, by rfl⟩) R1764089
theorem R94719 : Reach 94719 := rs (se 1 (by rfl) ⟨71039, by rfl⟩) R142079
theorem R2650643 : Reach 2650643 := rs (se 1 (by rfl) ⟨1987982, by rfl⟩) R3975965
theorem R94927 : Reach 94927 := rs (se 1 (by rfl) ⟨71195, by rfl⟩) R142391
theorem R455615 : Reach 455615 := rs (se 1 (by rfl) ⟨341711, by rfl⟩) R683423
theorem R1703119 : Reach 1703119 := rs (se 1 (by rfl) ⟨1277339, by rfl⟩) R2554679
theorem R359761 : Reach 359761 := rs (se 2 (by rfl) ⟨134910, by rfl⟩) R269821
theorem R1507085 : Reach 1507085 := rs (se 3 (by rfl) ⟨282578, by rfl⟩) R565157
theorem R262919 : Reach 262919 := rs (se 1 (by rfl) ⟨197189, by rfl⟩) R394379
theorem R394105 : Reach 394105 := rs (se 2 (by rfl) ⟨147789, by rfl⟩) R295579
theorem R132473 : Reach 132473 := rs (se 2 (by rfl) ⟨49677, by rfl⟩) R99355
theorem R525791 : Reach 525791 := rs (se 1 (by rfl) ⟨394343, by rfl⟩) R788687
theorem R1148843 : Reach 1148843 := rs (se 1 (by rfl) ⟨861632, by rfl⟩) R1723265
theorem R3803125 : Reach 3803125 := rs (se 5 (by rfl) ⟨178271, by rfl⟩) R356543
theorem R133531 : Reach 133531 := rs (se 1 (by rfl) ⟨100148, by rfl⟩) R200297
theorem R985729 : Reach 985729 := rs (se 2 (by rfl) ⟨369648, by rfl⟩) R739297
theorem R6982955 : Reach 6982955 := rs (se 1 (by rfl) ⟨5237216, by rfl⟩) R10474433
theorem R134455 : Reach 134455 := rs (se 1 (by rfl) ⟨100841, by rfl⟩) R201683
theorem R1348559 : Reach 1348559 := rs (se 1 (by rfl) ⟨1011419, by rfl⟩) R2022839
theorem R136937 : Reach 136937 := rs (se 2 (by rfl) ⟨51351, by rfl⟩) R102703
theorem R137087 : Reach 137087 := rs (se 1 (by rfl) ⟨102815, by rfl⟩) R205631
theorem R138335 : Reach 138335 := rs (se 1 (by rfl) ⟨103751, by rfl⟩) R207503
theorem R138377 : Reach 138377 := rs (se 2 (by rfl) ⟨51891, by rfl⟩) R103783
theorem R138623 : Reach 138623 := rs (se 1 (by rfl) ⟨103967, by rfl⟩) R207935
theorem R138911 : Reach 138911 := rs (se 1 (by rfl) ⟨104183, by rfl⟩) R208367
theorem R139199 : Reach 139199 := rs (se 1 (by rfl) ⟨104399, by rfl⟩) R208799
theorem R139391 : Reach 139391 := rs (se 1 (by rfl) ⟨104543, by rfl⟩) R209087
theorem R303743 : Reach 303743 := rs (se 1 (by rfl) ⟨227807, by rfl⟩) R455615
theorem R205775 : Reach 205775 := rs (se 1 (by rfl) ⟨154331, by rfl⟩) R308663
theorem R140519 : Reach 140519 := rs (se 1 (by rfl) ⟨105389, by rfl⟩) R210779
theorem R206135 : Reach 206135 := rs (se 1 (by rfl) ⟨154601, by rfl⟩) R309203
theorem R1123931 : Reach 1123931 := rs (se 1 (by rfl) ⟨842948, by rfl⟩) R1685897
theorem R2270825 : Reach 2270825 := rs (se 2 (by rfl) ⟨851559, by rfl⟩) R1703119
theorem R141167 : Reach 141167 := rs (se 1 (by rfl) ⟨105875, by rfl⟩) R211751
theorem R4007951 : Reach 4007951 := rs (se 1 (by rfl) ⟨3005963, by rfl⟩) R6011927
theorem R141737 : Reach 141737 := rs (se 2 (by rfl) ⟨53151, by rfl⟩) R106303
theorem R207611 : Reach 207611 := rs (se 1 (by rfl) ⟨155708, by rfl⟩) R311417
theorem R142319 : Reach 142319 := rs (se 1 (by rfl) ⟨106739, by rfl⟩) R213479
theorem R207881 : Reach 207881 := rs (se 2 (by rfl) ⟨77955, by rfl⟩) R155911
theorem R208079 : Reach 208079 := rs (se 1 (by rfl) ⟨156059, by rfl⟩) R312119
theorem R1192157 : Reach 1192157 := rs (se 3 (by rfl) ⟨223529, by rfl⟩) R447059
theorem R700811 : Reach 700811 := rs (se 1 (by rfl) ⟨525608, by rfl⟩) R1051217
theorem R209735 : Reach 209735 := rs (se 1 (by rfl) ⟨157301, by rfl⟩) R314603
theorem R308123 : Reach 308123 := rs (se 1 (by rfl) ⟨231092, by rfl⟩) R462185
theorem R472391 : Reach 472391 := rs (se 1 (by rfl) ⟨354293, by rfl⟩) R708587
theorem R24032807 : Reach 24032807 := rs (se 1 (by rfl) ⟨18024605, by rfl⟩) R36049211
theorem R211103 : Reach 211103 := rs (se 1 (by rfl) ⟨158327, by rfl⟩) R316655
theorem R4340411 : Reach 4340411 := rs (se 1 (by rfl) ⟨3255308, by rfl⟩) R6510617
theorem R211769 : Reach 211769 := rs (se 2 (by rfl) ⟨79413, by rfl⟩) R158827
theorem R179327 : Reach 179327 := rs (se 1 (by rfl) ⟨134495, by rfl⟩) R268991
theorem R1326415 : Reach 1326415 := rs (se 1 (by rfl) ⟨994811, by rfl⟩) R1989623
theorem R8469841 : Reach 8469841 := rs (se 2 (by rfl) ⟨3176190, by rfl⟩) R6352381
theorem R212327 : Reach 212327 := rs (se 1 (by rfl) ⟨159245, by rfl⟩) R318491
theorem R2015047 : Reach 2015047 := rs (se 1 (by rfl) ⟨1511285, by rfl⟩) R3022571
theorem R213641 : Reach 213641 := rs (se 2 (by rfl) ⟨80115, by rfl⟩) R160231
theorem R803519 : Reach 803519 := rs (se 1 (by rfl) ⟨602639, by rfl⟩) R1205279
theorem R213983 : Reach 213983 := rs (se 1 (by rfl) ⟨160487, by rfl⟩) R320975
theorem R346139 : Reach 346139 := rs (se 1 (by rfl) ⟨259604, by rfl⟩) R519209
theorem R706643 : Reach 706643 := rs (se 1 (by rfl) ⟨529982, by rfl⟩) R1059965
theorem R117703 : Reach 117703 := rs (se 1 (by rfl) ⟨88277, by rfl⟩) R176555
theorem R249311 : Reach 249311 := rs (se 1 (by rfl) ⟨186983, by rfl⟩) R373967
theorem R3985807 : Reach 3985807 := rs (se 1 (by rfl) ⟨2989355, by rfl⟩) R5978711
theorem R479681 : Reach 479681 := rs (se 2 (by rfl) ⟨179880, by rfl⟩) R359761
theorem R1004723 : Reach 1004723 := rs (se 1 (by rfl) ⟨753542, by rfl⟩) R1507085
theorem R1693817 : Reach 1693817 := rs (se 2 (by rfl) ⟨635181, by rfl⟩) R1270363
theorem R449003 : Reach 449003 := rs (se 1 (by rfl) ⟨336752, by rfl⟩) R673505
theorem R318113 : Reach 318113 := rs (se 2 (by rfl) ⟨119292, by rfl⟩) R238585
theorem R154399 : Reach 154399 := rs (se 1 (by rfl) ⟨115799, by rfl⟩) R231599
theorem R449327 : Reach 449327 := rs (se 1 (by rfl) ⟨336995, by rfl⟩) R673991
theorem R547931 : Reach 547931 := rs (se 1 (by rfl) ⟨410948, by rfl⟩) R821897
theorem R253343 : Reach 253343 := rs (se 1 (by rfl) ⟨190007, by rfl⟩) R380015
theorem R679589 : Reach 679589 := rs (se 4 (by rfl) ⟨63711, by rfl⟩) R127423
theorem R1434307 : Reach 1434307 := rs (se 1 (by rfl) ⟨1075730, by rfl⟩) R2151461
theorem R713447 : Reach 713447 := rs (se 1 (by rfl) ⟨535085, by rfl⟩) R1070171
theorem R320543 : Reach 320543 := rs (se 1 (by rfl) ⟨240407, by rfl⟩) R480815
theorem R91375 : Reach 91375 := rs (se 1 (by rfl) ⟨68531, by rfl⟩) R137063
theorem R92763 : Reach 92763 := rs (se 1 (by rfl) ⟨69572, by rfl⟩) R139145
theorem R93599 : Reach 93599 := rs (se 1 (by rfl) ⟨70199, by rfl⟩) R140399
theorem R749033 : Reach 749033 := rs (se 2 (by rfl) ⟨280887, by rfl⟩) R561775
theorem R126569 : Reach 126569 := rs (se 2 (by rfl) ⟨47463, by rfl⟩) R94927
theorem R1470095 : Reach 1470095 := rs (se 1 (by rfl) ⟨1102571, by rfl⟩) R2205143
theorem R1535867 : Reach 1535867 := rs (se 1 (by rfl) ⟨1151900, by rfl⟩) R2303801
theorem R95079 : Reach 95079 := rs (se 1 (by rfl) ⟨71309, by rfl⟩) R142619
theorem R717821 : Reach 717821 := rs (se 3 (by rfl) ⟨134591, by rfl⟩) R269183
theorem R784039 : Reach 784039 := rs (se 1 (by rfl) ⟨588029, by rfl⟩) R1176059
theorem R1767095 : Reach 1767095 := rs (se 1 (by rfl) ⟨1325321, by rfl⟩) R2650643
theorem R718793 : Reach 718793 := rs (se 2 (by rfl) ⟨269547, by rfl⟩) R539095
theorem R1080377 : Reach 1080377 := rs (se 2 (by rfl) ⟨405141, by rfl⟩) R810283
theorem R525473 : Reach 525473 := rs (se 2 (by rfl) ⟨197052, by rfl⟩) R394105
theorem R230759 : Reach 230759 := rs (se 1 (by rfl) ⟨173069, by rfl⟩) R346139
theorem R4655303 : Reach 4655303 := rs (se 1 (by rfl) ⟨3491477, by rfl⟩) R6982955
theorem R166207 : Reach 166207 := rs (se 1 (by rfl) ⟨124655, by rfl⟩) R249311
theorem R1314305 : Reach 1314305 := rs (se 2 (by rfl) ⟨492864, by rfl⟩) R985729
theorem R299335 : Reach 299335 := rs (se 1 (by rfl) ⟨224501, by rfl⟩) R449003
theorem R299551 : Reach 299551 := rs (se 1 (by rfl) ⟨224663, by rfl⟩) R449327
theorem R168895 : Reach 168895 := rs (se 1 (by rfl) ⟨126671, by rfl⟩) R253343
theorem R202495 : Reach 202495 := rs (se 1 (by rfl) ⟨151871, by rfl⟩) R303743
theorem R5314409 : Reach 5314409 := rs (se 2 (by rfl) ⟨1992903, by rfl⟩) R3985807
theorem R137183 : Reach 137183 := rs (se 1 (by rfl) ⟨102887, by rfl⟩) R205775
theorem R137423 : Reach 137423 := rs (se 1 (by rfl) ⟨103067, by rfl⟩) R206135
theorem R1513883 : Reach 1513883 := rs (se 1 (by rfl) ⟨1135412, by rfl⟩) R2270825
theorem R138407 : Reach 138407 := rs (se 1 (by rfl) ⟨103805, by rfl⟩) R207611
theorem R138587 : Reach 138587 := rs (se 1 (by rfl) ⟨103940, by rfl⟩) R207881
theorem R138719 : Reach 138719 := rs (se 1 (by rfl) ⟨104039, by rfl⟩) R208079
theorem R499355 : Reach 499355 := rs (se 1 (by rfl) ⟨374516, by rfl⟩) R749033
theorem R1023911 : Reach 1023911 := rs (se 1 (by rfl) ⟨767933, by rfl⟩) R1535867
theorem R794771 : Reach 794771 := rs (se 1 (by rfl) ⟨596078, by rfl⟩) R1192157
theorem R467207 : Reach 467207 := rs (se 1 (by rfl) ⟨350405, by rfl⟩) R700811
theorem R139823 : Reach 139823 := rs (se 1 (by rfl) ⟨104867, by rfl⟩) R209735
theorem R205415 : Reach 205415 := rs (se 1 (by rfl) ⟨154061, by rfl⟩) R308123
theorem R205865 : Reach 205865 := rs (se 2 (by rfl) ⟨77199, by rfl⟩) R154399
theorem R140735 : Reach 140735 := rs (se 1 (by rfl) ⟨105551, by rfl⟩) R211103
theorem R337517 : Reach 337517 := rs (se 3 (by rfl) ⟨63284, by rfl⟩) R126569
theorem R2893607 : Reach 2893607 := rs (se 1 (by rfl) ⟨2170205, by rfl⟩) R4340411
theorem R141179 : Reach 141179 := rs (se 1 (by rfl) ⟨105884, by rfl⟩) R211769
theorem R141551 : Reach 141551 := rs (se 1 (by rfl) ⟨106163, by rfl⟩) R212327
theorem R142427 : Reach 142427 := rs (se 1 (by rfl) ⟨106820, by rfl⟩) R213641
theorem R535679 : Reach 535679 := rs (se 1 (by rfl) ⟨401759, by rfl⟩) R803519
theorem R175279 : Reach 175279 := rs (se 1 (by rfl) ⟨131459, by rfl⟩) R262919
theorem R142655 : Reach 142655 := rs (se 1 (by rfl) ⟨106991, by rfl⟩) R213983
theorem R1912409 : Reach 1912409 := rs (se 2 (by rfl) ⟨717153, by rfl⟩) R1434307
theorem R765895 : Reach 765895 := rs (se 1 (by rfl) ⟨574421, by rfl⟩) R1148843
theorem R471095 : Reach 471095 := rs (se 1 (by rfl) ⟨353321, by rfl⟩) R706643
theorem R899039 : Reach 899039 := rs (se 1 (by rfl) ⟨674279, by rfl⟩) R1348559
theorem R669815 : Reach 669815 := rs (se 1 (by rfl) ⟨502361, by rfl⟩) R1004723
theorem R1129211 : Reach 1129211 := rs (se 1 (by rfl) ⟨846908, by rfl⟩) R1693817
theorem R179273 : Reach 179273 := rs (se 2 (by rfl) ⟨67227, by rfl⟩) R134455
theorem R212075 : Reach 212075 := rs (se 1 (by rfl) ⟨159056, by rfl⟩) R318113
theorem R475631 : Reach 475631 := rs (se 1 (by rfl) ⟨356723, by rfl⟩) R713447
theorem R213695 : Reach 213695 := rs (se 1 (by rfl) ⟨160271, by rfl⟩) R320543
theorem R2671967 : Reach 2671967 := rs (se 1 (by rfl) ⟨2003975, by rfl⟩) R4007951
theorem R1461149 : Reach 1461149 := rs (se 3 (by rfl) ⟨273965, by rfl⟩) R547931
theorem R478547 : Reach 478547 := rs (se 1 (by rfl) ⟨358910, by rfl⟩) R717821
theorem R314927 : Reach 314927 := rs (se 1 (by rfl) ⟨236195, by rfl⟩) R472391
theorem R479195 : Reach 479195 := rs (se 1 (by rfl) ⟨359396, by rfl⟩) R718793
theorem R11293121 : Reach 11293121 := rs (se 2 (by rfl) ⟨4234920, by rfl⟩) R8469841
theorem R119551 : Reach 119551 := rs (se 1 (by rfl) ⟨89663, by rfl⟩) R179327
theorem R350527 : Reach 350527 := rs (se 1 (by rfl) ⟨262895, by rfl⟩) R525791
theorem R712165 : Reach 712165 := rs (se 4 (by rfl) ⟨66765, by rfl⟩) R133531
theorem R5070833 : Reach 5070833 := rs (se 2 (by rfl) ⟨1901562, by rfl⟩) R3803125
theorem R319787 : Reach 319787 := rs (se 1 (by rfl) ⟨239840, by rfl⟩) R479681
theorem R353261 : Reach 353261 := rs (se 3 (by rfl) ⟨66236, by rfl⟩) R132473
theorem R91291 : Reach 91291 := rs (se 1 (by rfl) ⟨68468, by rfl⟩) R136937
theorem R91391 : Reach 91391 := rs (se 1 (by rfl) ⟨68543, by rfl⟩) R137087
theorem R156937 : Reach 156937 := rs (se 2 (by rfl) ⟨58851, by rfl⟩) R117703
theorem R92223 : Reach 92223 := rs (se 1 (by rfl) ⟨69167, by rfl⟩) R138335
theorem R92251 : Reach 92251 := rs (se 1 (by rfl) ⟨69188, by rfl⟩) R138377
theorem R92415 : Reach 92415 := rs (se 1 (by rfl) ⟨69311, by rfl⟩) R138623
theorem R92607 : Reach 92607 := rs (se 1 (by rfl) ⟨69455, by rfl⟩) R138911
theorem R453059 : Reach 453059 := rs (se 1 (by rfl) ⟨339794, by rfl⟩) R679589
theorem R92799 : Reach 92799 := rs (se 1 (by rfl) ⟨69599, by rfl⟩) R139199
theorem R92927 : Reach 92927 := rs (se 1 (by rfl) ⟨69695, by rfl⟩) R139391
theorem R93679 : Reach 93679 := rs (se 1 (by rfl) ⟨70259, by rfl⟩) R140519
theorem R749287 : Reach 749287 := rs (se 1 (by rfl) ⟨561965, by rfl⟩) R1123931
theorem R94111 : Reach 94111 := rs (se 1 (by rfl) ⟨70583, by rfl⟩) R141167
theorem R94491 : Reach 94491 := rs (se 1 (by rfl) ⟨70868, by rfl⟩) R141737
theorem R94879 : Reach 94879 := rs (se 1 (by rfl) ⟨71159, by rfl⟩) R142319
theorem R1045385 : Reach 1045385 := rs (se 2 (by rfl) ⟨392019, by rfl⟩) R784039
theorem R980063 : Reach 980063 := rs (se 1 (by rfl) ⟨735047, by rfl⟩) R1470095
theorem R16021871 : Reach 16021871 := rs (se 1 (by rfl) ⟨12016403, by rfl⟩) R24032807
theorem R1178063 : Reach 1178063 := rs (se 1 (by rfl) ⟨883547, by rfl⟩) R1767095
theorem R1768553 : Reach 1768553 := rs (se 2 (by rfl) ⟨663207, by rfl⟩) R1326415
theorem R720251 : Reach 720251 := rs (se 1 (by rfl) ⟨540188, by rfl⟩) R1080377
theorem R2686729 : Reach 2686729 := rs (se 2 (by rfl) ⟨1007523, by rfl⟩) R2015047
theorem R3542939 : Reach 3542939 := rs (se 1 (by rfl) ⟨2657204, by rfl⟩) R5314409
theorem R233705 : Reach 233705 := rs (se 2 (by rfl) ⟨87639, by rfl⟩) R175279
theorem R332903 : Reach 332903 := rs (se 1 (by rfl) ⟨249677, by rfl⟩) R499355
theorem R1021193 : Reach 1021193 := rs (se 2 (by rfl) ⟨382947, by rfl⟩) R765895
theorem R3380555 : Reach 3380555 := rs (se 1 (by rfl) ⟨2535416, by rfl⟩) R5070833
theorem R529847 : Reach 529847 := rs (se 1 (by rfl) ⟨397385, by rfl⟩) R794771
theorem R136943 : Reach 136943 := rs (se 1 (by rfl) ⟨102707, by rfl⟩) R205415
theorem R399113 : Reach 399113 := rs (se 2 (by rfl) ⟨149667, by rfl⟩) R299335
theorem R235507 : Reach 235507 := rs (se 1 (by rfl) ⟨176630, by rfl⟩) R353261
theorem R137243 : Reach 137243 := rs (se 1 (by rfl) ⟨102932, by rfl⟩) R205865
theorem R399401 : Reach 399401 := rs (se 2 (by rfl) ⟨149775, by rfl⟩) R299551
theorem R302039 : Reach 302039 := rs (se 1 (by rfl) ⟨226529, by rfl⟩) R453059
theorem R269993 : Reach 269993 := rs (se 2 (by rfl) ⟨101247, by rfl⟩) R202495
theorem R467369 : Reach 467369 := rs (se 2 (by rfl) ⟨175263, by rfl⟩) R350527
theorem R696923 : Reach 696923 := rs (se 1 (by rfl) ⟨522692, by rfl⟩) R1045385
theorem R599359 : Reach 599359 := rs (se 1 (by rfl) ⟨449519, by rfl⟩) R899039
theorem R141383 : Reach 141383 := rs (se 1 (by rfl) ⟨106037, by rfl⟩) R212075
theorem R3582305 : Reach 3582305 := rs (se 2 (by rfl) ⟨1343364, by rfl⟩) R2686729
theorem R142463 : Reach 142463 := rs (se 1 (by rfl) ⟨106847, by rfl⟩) R213695
theorem R1781311 : Reach 1781311 := rs (se 1 (by rfl) ⟨1335983, by rfl⟩) R2671967
theorem R209249 : Reach 209249 := rs (se 2 (by rfl) ⟨78468, by rfl⟩) R156937
theorem R209951 : Reach 209951 := rs (se 1 (by rfl) ⟨157463, by rfl⟩) R314927
theorem R999049 : Reach 999049 := rs (se 2 (by rfl) ⟨374643, by rfl⟩) R749287
theorem R311471 : Reach 311471 := rs (se 1 (by rfl) ⟨233603, by rfl⟩) R467207
theorem R213191 : Reach 213191 := rs (se 1 (by rfl) ⟨159893, by rfl⟩) R319787
theorem R314063 : Reach 314063 := rs (se 1 (by rfl) ⟨235547, by rfl⟩) R471095
theorem R478061 : Reach 478061 := rs (se 3 (by rfl) ⟨89636, by rfl⟩) R179273
theorem R446543 : Reach 446543 := rs (se 1 (by rfl) ⟨334907, by rfl⟩) R669815
theorem R480167 : Reach 480167 := rs (se 1 (by rfl) ⟨360125, by rfl⟩) R720251
theorem R317087 : Reach 317087 := rs (se 1 (by rfl) ⟨237815, by rfl⟩) R475631
theorem R350315 : Reach 350315 := rs (se 1 (by rfl) ⟨262736, by rfl⟩) R525473
theorem R153839 : Reach 153839 := rs (se 1 (by rfl) ⟨115379, by rfl⟩) R230759
theorem R3103535 : Reach 3103535 := rs (se 1 (by rfl) ⟨2327651, by rfl⟩) R4655303
theorem R974099 : Reach 974099 := rs (se 1 (by rfl) ⟨730574, by rfl⟩) R1461149
theorem R319031 : Reach 319031 := rs (se 1 (by rfl) ⟨239273, by rfl⟩) R478547
theorem R876203 : Reach 876203 := rs (se 1 (by rfl) ⟨657152, by rfl⟩) R1314305
theorem R319463 : Reach 319463 := rs (se 1 (by rfl) ⟨239597, by rfl⟩) R479195
theorem R7528747 : Reach 7528747 := rs (se 1 (by rfl) ⟨5646560, by rfl⟩) R11293121
theorem R221609 : Reach 221609 := rs (se 2 (by rfl) ⟨83103, by rfl⟩) R166207
theorem R91455 : Reach 91455 := rs (se 1 (by rfl) ⟨68591, by rfl⟩) R137183
theorem R91615 : Reach 91615 := rs (se 1 (by rfl) ⟨68711, by rfl⟩) R137423
theorem R1009255 : Reach 1009255 := rs (se 1 (by rfl) ⟨756941, by rfl⟩) R1513883
theorem R92271 : Reach 92271 := rs (se 1 (by rfl) ⟨69203, by rfl⟩) R138407
theorem R92391 : Reach 92391 := rs (se 1 (by rfl) ⟨69293, by rfl⟩) R138587
theorem R92479 : Reach 92479 := rs (se 1 (by rfl) ⟨69359, by rfl⟩) R138719
theorem R682607 : Reach 682607 := rs (se 1 (by rfl) ⟨511955, by rfl⟩) R1023911
theorem R93215 : Reach 93215 := rs (se 1 (by rfl) ⟨69911, by rfl⟩) R139823
theorem R93823 : Reach 93823 := rs (se 1 (by rfl) ⟨70367, by rfl⟩) R140735
theorem R159401 : Reach 159401 := rs (se 2 (by rfl) ⟨59775, by rfl⟩) R119551
theorem R225011 : Reach 225011 := rs (se 1 (by rfl) ⟨168758, by rfl⟩) R337517
theorem R1929071 : Reach 1929071 := rs (se 1 (by rfl) ⟨1446803, by rfl⟩) R2893607
theorem R94119 : Reach 94119 := rs (se 1 (by rfl) ⟨70589, by rfl⟩) R141179
theorem R225193 : Reach 225193 := rs (se 2 (by rfl) ⟨84447, by rfl⟩) R168895
theorem R94367 : Reach 94367 := rs (se 1 (by rfl) ⟨70775, by rfl⟩) R141551
theorem R94951 : Reach 94951 := rs (se 1 (by rfl) ⟨71213, by rfl⟩) R142427
theorem R357119 : Reach 357119 := rs (se 1 (by rfl) ⟨267839, by rfl⟩) R535679
theorem R95103 : Reach 95103 := rs (se 1 (by rfl) ⟨71327, by rfl⟩) R142655
theorem R1274939 : Reach 1274939 := rs (se 1 (by rfl) ⟨956204, by rfl⟩) R1912409
theorem R653375 : Reach 653375 := rs (se 1 (by rfl) ⟨490031, by rfl⟩) R980063
theorem R10681247 : Reach 10681247 := rs (se 1 (by rfl) ⟨8010935, by rfl⟩) R16021871
theorem R785375 : Reach 785375 := rs (se 1 (by rfl) ⟨589031, by rfl⟩) R1178063
theorem R752807 : Reach 752807 := rs (se 1 (by rfl) ⟨564605, by rfl⟩) R1129211
theorem R949553 : Reach 949553 := rs (se 2 (by rfl) ⟨356082, by rfl⟩) R712165
theorem R1179035 : Reach 1179035 := rs (se 1 (by rfl) ⟨884276, by rfl⟩) R1768553
theorem R1345673 : Reach 1345673 := rs (se 2 (by rfl) ⟨504627, by rfl⟩) R1009255
theorem R2361959 : Reach 2361959 := rs (se 1 (by rfl) ⟨1771469, by rfl⟩) R3542939
theorem R297695 : Reach 297695 := rs (se 1 (by rfl) ⟨223271, by rfl⟩) R446543
theorem R266075 : Reach 266075 := rs (se 1 (by rfl) ⟨199556, by rfl⟩) R399113
theorem R266267 : Reach 266267 := rs (se 1 (by rfl) ⟨199700, by rfl⟩) R399401
theorem R233543 : Reach 233543 := rs (se 1 (by rfl) ⟨175157, by rfl⟩) R350315
theorem R102559 : Reach 102559 := rs (se 1 (by rfl) ⟨76919, by rfl⟩) R153839
theorem R2069023 : Reach 2069023 := rs (se 1 (by rfl) ⟨1551767, by rfl⟩) R3103535
theorem R201359 : Reach 201359 := rs (se 1 (by rfl) ⟨151019, by rfl⟩) R302039
theorem R300257 : Reach 300257 := rs (se 2 (by rfl) ⟨112596, by rfl⟩) R225193
theorem R464615 : Reach 464615 := rs (se 1 (by rfl) ⟨348461, by rfl⟩) R696923
theorem R106267 : Reach 106267 := rs (se 1 (by rfl) ⟨79700, by rfl⟩) R159401
theorem R1286047 : Reach 1286047 := rs (se 1 (by rfl) ⟨964535, by rfl⟩) R1929071
theorem R139499 : Reach 139499 := rs (se 1 (by rfl) ⟨104624, by rfl⟩) R209249
theorem R238079 : Reach 238079 := rs (se 1 (by rfl) ⟨178559, by rfl⟩) R357119
theorem R139967 : Reach 139967 := rs (se 1 (by rfl) ⟨104975, by rfl⟩) R209951
theorem R435583 : Reach 435583 := rs (se 1 (by rfl) ⟨326687, by rfl⟩) R653375
theorem R7120831 : Reach 7120831 := rs (se 1 (by rfl) ⟨5340623, by rfl⟩) R10681247
theorem R501871 : Reach 501871 := rs (se 1 (by rfl) ⟨376403, by rfl⟩) R752807
theorem R633035 : Reach 633035 := rs (se 1 (by rfl) ⟨474776, by rfl⟩) R949553
theorem R207647 : Reach 207647 := rs (se 1 (by rfl) ⟨155735, by rfl⟩) R311471
theorem R142127 : Reach 142127 := rs (se 1 (by rfl) ⟨106595, by rfl⟩) R213191
theorem R10038329 : Reach 10038329 := rs (se 2 (by rfl) ⟨3764373, by rfl⟩) R7528747
theorem R799145 : Reach 799145 := rs (se 2 (by rfl) ⟨299679, by rfl⟩) R599359
theorem R209375 : Reach 209375 := rs (se 1 (by rfl) ⟨157031, by rfl⟩) R314063
theorem R211391 : Reach 211391 := rs (se 1 (by rfl) ⟨158543, by rfl⟩) R317087
theorem R2375081 : Reach 2375081 := rs (se 2 (by rfl) ⟨890655, by rfl⟩) R1781311
theorem R212687 : Reach 212687 := rs (se 1 (by rfl) ⟨159515, by rfl⟩) R319031
theorem R179995 : Reach 179995 := rs (se 1 (by rfl) ⟨134996, by rfl⟩) R269993
theorem R212975 : Reach 212975 := rs (se 1 (by rfl) ⟨159731, by rfl⟩) R319463
theorem R147739 : Reach 147739 := rs (se 1 (by rfl) ⟨110804, by rfl⟩) R221609
theorem R311579 : Reach 311579 := rs (se 1 (by rfl) ⟨233684, by rfl⟩) R467369
theorem R150007 : Reach 150007 := rs (se 1 (by rfl) ⟨112505, by rfl⟩) R225011
theorem R314009 : Reach 314009 := rs (se 2 (by rfl) ⟨117753, by rfl⟩) R235507
theorem R1332065 : Reach 1332065 := rs (se 2 (by rfl) ⟨499524, by rfl⟩) R999049
theorem R318707 : Reach 318707 := rs (se 1 (by rfl) ⟨239030, by rfl⟩) R478061
theorem R155803 : Reach 155803 := rs (se 1 (by rfl) ⟨116852, by rfl⟩) R233705
theorem R320111 : Reach 320111 := rs (se 1 (by rfl) ⟨240083, by rfl⟩) R480167
theorem R221935 : Reach 221935 := rs (se 1 (by rfl) ⟨166451, by rfl⟩) R332903
theorem R680795 : Reach 680795 := rs (se 1 (by rfl) ⟨510596, by rfl⟩) R1021193
theorem R2253703 : Reach 2253703 := rs (se 1 (by rfl) ⟨1690277, by rfl⟩) R3380555
theorem R353231 : Reach 353231 := rs (se 1 (by rfl) ⟨264923, by rfl⟩) R529847
theorem R91295 : Reach 91295 := rs (se 1 (by rfl) ⟨68471, by rfl⟩) R136943
theorem R91495 : Reach 91495 := rs (se 1 (by rfl) ⟨68621, by rfl⟩) R137243
theorem R649399 : Reach 649399 := rs (se 1 (by rfl) ⟨487049, by rfl⟩) R974099
theorem R584135 : Reach 584135 := rs (se 1 (by rfl) ⟨438101, by rfl⟩) R876203
theorem R94255 : Reach 94255 := rs (se 1 (by rfl) ⟨70691, by rfl⟩) R141383
theorem R2388203 : Reach 2388203 := rs (se 1 (by rfl) ⟨1791152, by rfl⟩) R3582305
theorem R455071 : Reach 455071 := rs (se 1 (by rfl) ⟨341303, by rfl⟩) R682607
theorem R94975 : Reach 94975 := rs (se 1 (by rfl) ⟨71231, by rfl⟩) R142463
theorem R849959 : Reach 849959 := rs (se 1 (by rfl) ⟨637469, by rfl⟩) R1274939
theorem R523583 : Reach 523583 := rs (se 1 (by rfl) ⟨392687, by rfl⟩) R785375
theorem R786023 : Reach 786023 := rs (se 1 (by rfl) ⟨589517, by rfl⟩) R1179035
theorem R196985 : Reach 196985 := rs (se 2 (by rfl) ⟨73869, by rfl⟩) R147739
theorem R295913 : Reach 295913 := rs (se 2 (by rfl) ⟨110967, by rfl⟩) R221935
theorem R1574639 : Reach 1574639 := rs (se 1 (by rfl) ⟨1180979, by rfl⟩) R2361959
theorem R198463 : Reach 198463 := rs (se 1 (by rfl) ⟨148847, by rfl⟩) R297695
theorem R134239 : Reach 134239 := rs (se 1 (by rfl) ⟨100679, by rfl⟩) R201359
theorem R888043 : Reach 888043 := rs (se 1 (by rfl) ⟨666032, by rfl⟩) R1332065
theorem R200009 : Reach 200009 := rs (se 2 (by rfl) ⟨75003, by rfl⟩) R150007
theorem R200171 : Reach 200171 := rs (se 1 (by rfl) ⟨150128, by rfl⟩) R300257
theorem R136745 : Reach 136745 := rs (se 2 (by rfl) ⟨51279, by rfl⟩) R102559
theorem R235487 : Reach 235487 := rs (se 1 (by rfl) ⟨176615, by rfl⟩) R353231
theorem R2758697 : Reach 2758697 := rs (se 2 (by rfl) ⟨1034511, by rfl⟩) R2069023
theorem R138431 : Reach 138431 := rs (se 1 (by rfl) ⟨103823, by rfl⟩) R207647
theorem R6692219 : Reach 6692219 := rs (se 1 (by rfl) ⟨5019164, by rfl⟩) R10038329
theorem R532763 : Reach 532763 := rs (se 1 (by rfl) ⟨399572, by rfl⟩) R799145
theorem R139583 : Reach 139583 := rs (se 1 (by rfl) ⟨104687, by rfl⟩) R209375
theorem R566639 : Reach 566639 := rs (se 1 (by rfl) ⟨424979, by rfl⟩) R849959
theorem R140927 : Reach 140927 := rs (se 1 (by rfl) ⟨105695, by rfl⟩) R211391
theorem R1583387 : Reach 1583387 := rs (se 1 (by rfl) ⟨1187540, by rfl⟩) R2375081
theorem R141689 : Reach 141689 := rs (se 2 (by rfl) ⟨53133, by rfl⟩) R106267
theorem R239993 : Reach 239993 := rs (se 2 (by rfl) ⟨89997, by rfl⟩) R179995
theorem R141791 : Reach 141791 := rs (se 1 (by rfl) ⟨106343, by rfl⟩) R212687
theorem R1714729 : Reach 1714729 := rs (se 2 (by rfl) ⟨643023, by rfl⟩) R1286047
theorem R141983 : Reach 141983 := rs (se 1 (by rfl) ⟨106487, by rfl⟩) R212975
theorem R207719 : Reach 207719 := rs (se 1 (by rfl) ⟨155789, by rfl⟩) R311579
theorem R207737 : Reach 207737 := rs (se 2 (by rfl) ⟨77901, by rfl⟩) R155803
theorem R897115 : Reach 897115 := rs (se 1 (by rfl) ⟨672836, by rfl⟩) R1345673
theorem R209339 : Reach 209339 := rs (se 1 (by rfl) ⟨157004, by rfl⟩) R314009
theorem R177383 : Reach 177383 := rs (se 1 (by rfl) ⟨133037, by rfl⟩) R266075
theorem R669161 : Reach 669161 := rs (se 2 (by rfl) ⟨250935, by rfl⟩) R501871
theorem R865865 : Reach 865865 := rs (se 2 (by rfl) ⟨324699, by rfl⟩) R649399
theorem R309743 : Reach 309743 := rs (se 1 (by rfl) ⟨232307, by rfl⟩) R464615
theorem R212471 : Reach 212471 := rs (se 1 (by rfl) ⟨159353, by rfl⟩) R318707
theorem R213407 : Reach 213407 := rs (se 1 (by rfl) ⟨160055, by rfl⟩) R320111
theorem R606761 : Reach 606761 := rs (se 2 (by rfl) ⟨227535, by rfl⟩) R455071
theorem R1592135 : Reach 1592135 := rs (se 1 (by rfl) ⟨1194101, by rfl⟩) R2388203
theorem R349055 : Reach 349055 := rs (se 1 (by rfl) ⟨261791, by rfl⟩) R523583
theorem R710045 : Reach 710045 := rs (se 3 (by rfl) ⟨133133, by rfl⟩) R266267
theorem R3004937 : Reach 3004937 := rs (se 2 (by rfl) ⟨1126851, by rfl⟩) R2253703
theorem R9494441 : Reach 9494441 := rs (se 2 (by rfl) ⟨3560415, by rfl⟩) R7120831
theorem R155695 : Reach 155695 := rs (se 1 (by rfl) ⟨116771, by rfl⟩) R233543
theorem R92999 : Reach 92999 := rs (se 1 (by rfl) ⟨69749, by rfl⟩) R139499
theorem R158719 : Reach 158719 := rs (se 1 (by rfl) ⟨119039, by rfl⟩) R238079
theorem R93311 : Reach 93311 := rs (se 1 (by rfl) ⟨69983, by rfl⟩) R139967
theorem R453863 : Reach 453863 := rs (se 1 (by rfl) ⟨340397, by rfl⟩) R680795
theorem R422023 : Reach 422023 := rs (se 1 (by rfl) ⟨316517, by rfl⟩) R633035
theorem R389423 : Reach 389423 := rs (se 1 (by rfl) ⟨292067, by rfl⟩) R584135
theorem R94751 : Reach 94751 := rs (se 1 (by rfl) ⟨71063, by rfl⟩) R142127
theorem R2323109 : Reach 2323109 := rs (se 4 (by rfl) ⟨217791, by rfl⟩) R435583
theorem R524015 : Reach 524015 := rs (se 1 (by rfl) ⟨393011, by rfl⟩) R786023
theorem R131323 : Reach 131323 := rs (se 1 (by rfl) ⟨98492, by rfl⟩) R196985
theorem R197275 : Reach 197275 := rs (se 1 (by rfl) ⟨147956, by rfl⟩) R295913
theorem R1049759 : Reach 1049759 := rs (se 1 (by rfl) ⟨787319, by rfl⟩) R1574639
theorem R133339 : Reach 133339 := rs (se 1 (by rfl) ⟨100004, by rfl⟩) R200009
theorem R264617 : Reach 264617 := rs (se 2 (by rfl) ⟨99231, by rfl⟩) R198463
theorem R232703 : Reach 232703 := rs (se 1 (by rfl) ⟨174527, by rfl⟩) R349055
theorem R1839131 : Reach 1839131 := rs (se 1 (by rfl) ⟨1379348, by rfl⟩) R2758697
theorem R1184057 : Reach 1184057 := rs (se 2 (by rfl) ⟨444021, by rfl⟩) R888043
theorem R2003291 : Reach 2003291 := rs (se 1 (by rfl) ⟨1502468, by rfl⟩) R3004937
theorem R4461479 : Reach 4461479 := rs (se 1 (by rfl) ⟨3346109, by rfl⟩) R6692219
theorem R6329627 : Reach 6329627 := rs (se 1 (by rfl) ⟨4747220, by rfl⟩) R9494441
theorem R562697 : Reach 562697 := rs (se 2 (by rfl) ⟨211011, by rfl⟩) R422023
theorem R1055591 : Reach 1055591 := rs (se 1 (by rfl) ⟨791693, by rfl⟩) R1583387
theorem R138479 : Reach 138479 := rs (se 1 (by rfl) ⟨103859, by rfl⟩) R207719
theorem R138491 : Reach 138491 := rs (se 1 (by rfl) ⟨103868, by rfl⟩) R207737
theorem R139559 : Reach 139559 := rs (se 1 (by rfl) ⟨104669, by rfl⟩) R209339
theorem R1548739 : Reach 1548739 := rs (se 1 (by rfl) ⟨1161554, by rfl⟩) R2323109
theorem R533789 : Reach 533789 := rs (se 3 (by rfl) ⟨100085, by rfl⟩) R200171
theorem R206495 : Reach 206495 := rs (se 1 (by rfl) ⟨154871, by rfl⟩) R309743
theorem R141647 : Reach 141647 := rs (se 1 (by rfl) ⟨106235, by rfl⟩) R212471
theorem R207593 : Reach 207593 := rs (se 2 (by rfl) ⟨77847, by rfl⟩) R155695
theorem R142271 : Reach 142271 := rs (se 1 (by rfl) ⟨106703, by rfl⟩) R213407
theorem R404507 : Reach 404507 := rs (se 1 (by rfl) ⟨303380, by rfl⟩) R606761
theorem R1061423 : Reach 1061423 := rs (se 1 (by rfl) ⟨796067, by rfl⟩) R1592135
theorem R473363 : Reach 473363 := rs (se 1 (by rfl) ⟨355022, by rfl⟩) R710045
theorem R211625 : Reach 211625 := rs (se 2 (by rfl) ⟨79359, by rfl⟩) R158719
theorem R178985 : Reach 178985 := rs (se 2 (by rfl) ⟨67119, by rfl⟩) R134239
theorem R1196153 : Reach 1196153 := rs (se 2 (by rfl) ⟨448557, by rfl⟩) R897115
theorem R377759 : Reach 377759 := rs (se 1 (by rfl) ⟨283319, by rfl⟩) R566639
theorem R118255 : Reach 118255 := rs (se 1 (by rfl) ⟨88691, by rfl⟩) R177383
theorem R446107 : Reach 446107 := rs (se 1 (by rfl) ⟨334580, by rfl⟩) R669161
theorem R577243 : Reach 577243 := rs (se 1 (by rfl) ⟨432932, by rfl⟩) R865865
theorem R349343 : Reach 349343 := rs (se 1 (by rfl) ⟨262007, by rfl⟩) R524015
theorem R2286305 : Reach 2286305 := rs (se 2 (by rfl) ⟨857364, by rfl⟩) R1714729
theorem R91163 : Reach 91163 := rs (se 1 (by rfl) ⟨68372, by rfl⟩) R136745
theorem R156991 : Reach 156991 := rs (se 1 (by rfl) ⟨117743, by rfl⟩) R235487
theorem R92287 : Reach 92287 := rs (se 1 (by rfl) ⟨69215, by rfl⟩) R138431
theorem R355175 : Reach 355175 := rs (se 1 (by rfl) ⟨266381, by rfl⟩) R532763
theorem R93055 : Reach 93055 := rs (se 1 (by rfl) ⟨69791, by rfl⟩) R139583
theorem R93951 : Reach 93951 := rs (se 1 (by rfl) ⟨70463, by rfl⟩) R140927
theorem R94459 : Reach 94459 := rs (se 1 (by rfl) ⟨70844, by rfl⟩) R141689
theorem R159995 : Reach 159995 := rs (se 1 (by rfl) ⟨119996, by rfl⟩) R239993
theorem R94527 : Reach 94527 := rs (se 1 (by rfl) ⟨70895, by rfl⟩) R141791
theorem R94655 : Reach 94655 := rs (se 1 (by rfl) ⟨70991, by rfl⟩) R141983
theorem R259615 : Reach 259615 := rs (se 1 (by rfl) ⟨194711, by rfl⟩) R389423
theorem R1210301 : Reach 1210301 := rs (se 3 (by rfl) ⟨226931, by rfl⟩) R453863
theorem R263033 : Reach 263033 := rs (se 2 (by rfl) ⟨98637, by rfl⟩) R197275
theorem R8259941 : Reach 8259941 := rs (se 4 (by rfl) ⟨774369, by rfl⟩) R1548739
theorem R789371 : Reach 789371 := rs (se 1 (by rfl) ⟨592028, by rfl⟩) R1184057
theorem R232895 : Reach 232895 := rs (se 1 (by rfl) ⟨174671, by rfl⟩) R349343
theorem R594809 : Reach 594809 := rs (se 2 (by rfl) ⟨223053, by rfl⟩) R446107
theorem R137663 : Reach 137663 := rs (se 1 (by rfl) ⟨103247, by rfl⟩) R206495
theorem R138395 : Reach 138395 := rs (se 1 (by rfl) ⟨103796, by rfl⟩) R207593
theorem R236783 : Reach 236783 := rs (se 1 (by rfl) ⟨177587, by rfl⟩) R355175
theorem R269671 : Reach 269671 := rs (se 1 (by rfl) ⟨202253, by rfl⟩) R404507
theorem R106663 : Reach 106663 := rs (se 1 (by rfl) ⟨79997, by rfl⟩) R159995
theorem R141083 : Reach 141083 := rs (se 1 (by rfl) ⟨105812, by rfl⟩) R211625
theorem R797435 : Reach 797435 := rs (se 1 (by rfl) ⟨598076, by rfl⟩) R1196153
theorem R175097 : Reach 175097 := rs (se 2 (by rfl) ⟨65661, by rfl⟩) R131323
theorem R699839 : Reach 699839 := rs (se 1 (by rfl) ⟨524879, by rfl⟩) R1049759
theorem R176411 : Reach 176411 := rs (se 1 (by rfl) ⟨132308, by rfl⟩) R264617
theorem R209321 : Reach 209321 := rs (se 2 (by rfl) ⟨78495, by rfl⟩) R156991
theorem R1226087 : Reach 1226087 := rs (se 1 (by rfl) ⟨919565, by rfl⟩) R1839131
theorem R177785 : Reach 177785 := rs (se 2 (by rfl) ⟨66669, by rfl⟩) R133339
theorem R375131 : Reach 375131 := rs (se 1 (by rfl) ⟨281348, by rfl⟩) R562697
theorem R703727 : Reach 703727 := rs (se 1 (by rfl) ⟨527795, by rfl⟩) R1055591
theorem R769657 : Reach 769657 := rs (se 2 (by rfl) ⟨288621, by rfl⟩) R577243
theorem R1524203 : Reach 1524203 := rs (se 1 (by rfl) ⟨1143152, by rfl⟩) R2286305
theorem R346153 : Reach 346153 := rs (se 2 (by rfl) ⟨129807, by rfl⟩) R259615
theorem R707615 : Reach 707615 := rs (se 1 (by rfl) ⟨530711, by rfl⟩) R1061423
theorem R806867 : Reach 806867 := rs (se 1 (by rfl) ⟨605150, by rfl⟩) R1210301
theorem R315575 : Reach 315575 := rs (se 1 (by rfl) ⟨236681, by rfl⟩) R473363
theorem R119323 : Reach 119323 := rs (se 1 (by rfl) ⟨89492, by rfl⟩) R178985
theorem R251839 : Reach 251839 := rs (se 1 (by rfl) ⟨188879, by rfl⟩) R377759
theorem R155135 : Reach 155135 := rs (se 1 (by rfl) ⟨116351, by rfl⟩) R232703
theorem R1335527 : Reach 1335527 := rs (se 1 (by rfl) ⟨1001645, by rfl⟩) R2003291
theorem R2974319 : Reach 2974319 := rs (se 1 (by rfl) ⟨2230739, by rfl⟩) R4461479
theorem R4219751 : Reach 4219751 := rs (se 1 (by rfl) ⟨3164813, by rfl⟩) R6329627
theorem R157673 : Reach 157673 := rs (se 2 (by rfl) ⟨59127, by rfl⟩) R118255
theorem R92319 : Reach 92319 := rs (se 1 (by rfl) ⟨69239, by rfl⟩) R138479
theorem R92327 : Reach 92327 := rs (se 1 (by rfl) ⟨69245, by rfl⟩) R138491
theorem R93039 : Reach 93039 := rs (se 1 (by rfl) ⟨69779, by rfl⟩) R139559
theorem R355859 : Reach 355859 := rs (se 1 (by rfl) ⟨266894, by rfl⟩) R533789
theorem R94431 : Reach 94431 := rs (se 1 (by rfl) ⟨70823, by rfl⟩) R141647
theorem R94847 : Reach 94847 := rs (se 1 (by rfl) ⟨71135, by rfl⟩) R142271
theorem R1016135 : Reach 1016135 := rs (se 1 (by rfl) ⟨762101, by rfl⟩) R1524203
theorem R5506627 : Reach 5506627 := rs (se 1 (by rfl) ⟨4129970, by rfl⟩) R8259941
theorem R526247 : Reach 526247 := rs (se 1 (by rfl) ⟨394685, by rfl⟩) R789371
theorem R461537 : Reach 461537 := rs (se 2 (by rfl) ⟨173076, by rfl⟩) R346153
theorem R396539 : Reach 396539 := rs (se 1 (by rfl) ⟨297404, by rfl⟩) R594809
theorem R103423 : Reach 103423 := rs (se 1 (by rfl) ⟨77567, by rfl⟩) R155135
theorem R890351 : Reach 890351 := rs (se 1 (by rfl) ⟨667763, by rfl⟩) R1335527
theorem R105115 : Reach 105115 := rs (se 1 (by rfl) ⟨78836, by rfl⟩) R157673
theorem R531623 : Reach 531623 := rs (se 1 (by rfl) ⟨398717, by rfl⟩) R797435
theorem R466559 : Reach 466559 := rs (se 1 (by rfl) ⟨349919, by rfl⟩) R699839
theorem R237239 : Reach 237239 := rs (se 1 (by rfl) ⟨177929, by rfl⟩) R355859
theorem R335785 : Reach 335785 := rs (se 2 (by rfl) ⟨125919, by rfl⟩) R251839
theorem R139547 : Reach 139547 := rs (se 1 (by rfl) ⟨104660, by rfl⟩) R209321
theorem R469151 : Reach 469151 := rs (se 1 (by rfl) ⟨351863, by rfl⟩) R703727
theorem R1026209 : Reach 1026209 := rs (se 2 (by rfl) ⟨384828, by rfl⟩) R769657
theorem R142217 : Reach 142217 := rs (se 2 (by rfl) ⟨53331, by rfl⟩) R106663
theorem R175355 : Reach 175355 := rs (se 1 (by rfl) ⟨131516, by rfl⟩) R263033
theorem R471743 : Reach 471743 := rs (se 1 (by rfl) ⟨353807, by rfl⟩) R707615
theorem R537911 : Reach 537911 := rs (se 1 (by rfl) ⟨403433, by rfl⟩) R806867
theorem R210383 : Reach 210383 := rs (se 1 (by rfl) ⟨157787, by rfl⟩) R315575
theorem R180042709 : Reach 180042709 := rs (se 7 (by rfl) ⟨2109875, by rfl⟩) R4219751
theorem R1982879 : Reach 1982879 := rs (se 1 (by rfl) ⟨1487159, by rfl⟩) R2974319
theorem R1000349 : Reach 1000349 := rs (se 3 (by rfl) ⟨187565, by rfl⟩) R375131
theorem R116731 : Reach 116731 := rs (se 1 (by rfl) ⟨87548, by rfl⟩) R175097
theorem R117607 : Reach 117607 := rs (se 1 (by rfl) ⟨88205, by rfl⟩) R176411
theorem R118523 : Reach 118523 := rs (se 1 (by rfl) ⟨88892, by rfl⟩) R177785
theorem R155263 : Reach 155263 := rs (se 1 (by rfl) ⟨116447, by rfl⟩) R232895
theorem R91775 : Reach 91775 := rs (se 1 (by rfl) ⟨68831, by rfl⟩) R137663
theorem R92263 : Reach 92263 := rs (se 1 (by rfl) ⟨69197, by rfl⟩) R138395
theorem R157855 : Reach 157855 := rs (se 1 (by rfl) ⟨118391, by rfl⟩) R236783
theorem R159097 : Reach 159097 := rs (se 2 (by rfl) ⟨59661, by rfl⟩) R119323
theorem R94055 : Reach 94055 := rs (se 1 (by rfl) ⟨70541, by rfl⟩) R141083
theorem R817391 : Reach 817391 := rs (se 1 (by rfl) ⟨613043, by rfl⟩) R1226087
theorem R359561 : Reach 359561 := rs (se 2 (by rfl) ⟨134835, by rfl⟩) R269671
theorem R7342169 : Reach 7342169 := rs (se 2 (by rfl) ⟨2753313, by rfl⟩) R5506627
theorem R264359 : Reach 264359 := rs (se 1 (by rfl) ⟨198269, by rfl⟩) R396539
theorem R593567 : Reach 593567 := rs (se 1 (by rfl) ⟨445175, by rfl⟩) R890351
theorem R137897 : Reach 137897 := rs (se 2 (by rfl) ⟨51711, by rfl⟩) R103423
theorem R140153 : Reach 140153 := rs (se 2 (by rfl) ⟨52557, by rfl⟩) R105115
theorem R140255 : Reach 140255 := rs (se 1 (by rfl) ⟨105191, by rfl⟩) R210383
theorem R239707 : Reach 239707 := rs (se 1 (by rfl) ⟨179780, by rfl⟩) R359561
theorem R207017 : Reach 207017 := rs (se 2 (by rfl) ⟨77631, by rfl⟩) R155263
theorem R1321919 : Reach 1321919 := rs (se 1 (by rfl) ⟨991439, by rfl⟩) R1982879
theorem R666899 : Reach 666899 := rs (se 1 (by rfl) ⟨500174, by rfl⟩) R1000349
theorem R307691 : Reach 307691 := rs (se 1 (by rfl) ⟨230768, by rfl⟩) R461537
theorem R210473 : Reach 210473 := rs (se 2 (by rfl) ⟨78927, by rfl⟩) R157855
theorem R212129 : Reach 212129 := rs (se 2 (by rfl) ⟨79548, by rfl⟩) R159097
theorem R311039 : Reach 311039 := rs (se 1 (by rfl) ⟨233279, by rfl⟩) R466559
theorem R2179709 : Reach 2179709 := rs (se 3 (by rfl) ⟨408695, by rfl⟩) R817391
theorem R312767 : Reach 312767 := rs (se 1 (by rfl) ⟨234575, by rfl⟩) R469151
theorem R116903 : Reach 116903 := rs (se 1 (by rfl) ⟨87677, by rfl⟩) R175355
theorem R314495 : Reach 314495 := rs (se 1 (by rfl) ⟨235871, by rfl⟩) R471743
theorem R316061 : Reach 316061 := rs (se 3 (by rfl) ⟨59261, by rfl⟩) R118523
theorem R447713 : Reach 447713 := rs (se 2 (by rfl) ⟨167892, by rfl⟩) R335785
theorem R677423 : Reach 677423 := rs (se 1 (by rfl) ⟨508067, by rfl⟩) R1016135
theorem R350831 : Reach 350831 := rs (se 1 (by rfl) ⟨263123, by rfl⟩) R526247
theorem R155641 : Reach 155641 := rs (se 2 (by rfl) ⟨58365, by rfl⟩) R116731
theorem R156809 : Reach 156809 := rs (se 2 (by rfl) ⟨58803, by rfl⟩) R117607
theorem R354415 : Reach 354415 := rs (se 1 (by rfl) ⟨265811, by rfl⟩) R531623
theorem R158159 : Reach 158159 := rs (se 1 (by rfl) ⟨118619, by rfl⟩) R237239
theorem R93031 : Reach 93031 := rs (se 1 (by rfl) ⟨69773, by rfl⟩) R139547
theorem R684139 : Reach 684139 := rs (se 1 (by rfl) ⟨513104, by rfl⟩) R1026209
theorem R94811 : Reach 94811 := rs (se 1 (by rfl) ⟨71108, by rfl⟩) R142217
theorem R358607 : Reach 358607 := rs (se 1 (by rfl) ⟨268955, by rfl⟩) R537911
theorem R240056945 : Reach 240056945 := rs (se 2 (by rfl) ⟨90021354, by rfl⟩) R180042709
theorem R395711 : Reach 395711 := rs (se 1 (by rfl) ⟨296783, by rfl⟩) R593567
theorem R298475 : Reach 298475 := rs (se 1 (by rfl) ⟨223856, by rfl⟩) R447713
theorem R1806461 : Reach 1806461 := rs (se 3 (by rfl) ⟨338711, by rfl⟩) R677423
theorem R233887 : Reach 233887 := rs (se 1 (by rfl) ⟨175415, by rfl⟩) R350831
theorem R104539 : Reach 104539 := rs (se 1 (by rfl) ⟨78404, by rfl⟩) R156809
theorem R138011 : Reach 138011 := rs (se 1 (by rfl) ⟨103508, by rfl⟩) R207017
theorem R105439 : Reach 105439 := rs (se 1 (by rfl) ⟨79079, by rfl⟩) R158159
theorem R205127 : Reach 205127 := rs (se 1 (by rfl) ⟨153845, by rfl⟩) R307691
theorem R140315 : Reach 140315 := rs (se 1 (by rfl) ⟨105236, by rfl⟩) R210473
theorem R239071 : Reach 239071 := rs (se 1 (by rfl) ⟨179303, by rfl⟩) R358607
theorem R141419 : Reach 141419 := rs (se 1 (by rfl) ⟨106064, by rfl⟩) R212129
theorem R207359 : Reach 207359 := rs (se 1 (by rfl) ⟨155519, by rfl⟩) R311039
theorem R207521 : Reach 207521 := rs (se 2 (by rfl) ⟨77820, by rfl⟩) R155641
theorem R1453139 : Reach 1453139 := rs (se 1 (by rfl) ⟨1089854, by rfl⟩) R2179709
theorem R208511 : Reach 208511 := rs (se 1 (by rfl) ⟨156383, by rfl⟩) R312767
theorem R176239 : Reach 176239 := rs (se 1 (by rfl) ⟨132179, by rfl⟩) R264359
theorem R209663 : Reach 209663 := rs (se 1 (by rfl) ⟨157247, by rfl⟩) R314495
theorem R472553 : Reach 472553 := rs (se 2 (by rfl) ⟨177207, by rfl⟩) R354415
theorem R210707 : Reach 210707 := rs (se 1 (by rfl) ⟨158030, by rfl⟩) R316061
theorem R19579117 : Reach 19579117 := rs (se 3 (by rfl) ⟨3671084, by rfl⟩) R7342169
theorem R311741 : Reach 311741 := rs (se 3 (by rfl) ⟨58451, by rfl⟩) R116903
theorem R444599 : Reach 444599 := rs (se 1 (by rfl) ⟨333449, by rfl⟩) R666899
theorem R319609 : Reach 319609 := rs (se 2 (by rfl) ⟨119853, by rfl⟩) R239707
theorem R91931 : Reach 91931 := rs (se 1 (by rfl) ⟨68948, by rfl⟩) R137897
theorem R912185 : Reach 912185 := rs (se 2 (by rfl) ⟨342069, by rfl⟩) R684139
theorem R93435 : Reach 93435 := rs (se 1 (by rfl) ⟨70076, by rfl⟩) R140153
theorem R93503 : Reach 93503 := rs (se 1 (by rfl) ⟨70127, by rfl⟩) R140255
theorem R881279 : Reach 881279 := rs (se 1 (by rfl) ⟨660959, by rfl⟩) R1321919
theorem R160037963 : Reach 160037963 := rs (se 1 (by rfl) ⟨120028472, by rfl⟩) R240056945
theorem R426145 : Reach 426145 := rs (se 2 (by rfl) ⟨159804, by rfl⟩) R319609
theorem R296399 : Reach 296399 := rs (se 1 (by rfl) ⟨222299, by rfl⟩) R444599
theorem R263807 : Reach 263807 := rs (se 1 (by rfl) ⟨197855, by rfl⟩) R395711
theorem R198983 : Reach 198983 := rs (se 1 (by rfl) ⟨149237, by rfl⟩) R298475
theorem R136751 : Reach 136751 := rs (se 1 (by rfl) ⟨102563, by rfl⟩) R205127
theorem R138239 : Reach 138239 := rs (se 1 (by rfl) ⟨103679, by rfl⟩) R207359
theorem R138347 : Reach 138347 := rs (se 1 (by rfl) ⟨103760, by rfl⟩) R207521
theorem R139007 : Reach 139007 := rs (se 1 (by rfl) ⟨104255, by rfl⟩) R208511
theorem R139385 : Reach 139385 := rs (se 2 (by rfl) ⟨52269, by rfl⟩) R104539
theorem R139775 : Reach 139775 := rs (se 1 (by rfl) ⟨104831, by rfl⟩) R209663
theorem R140471 : Reach 140471 := rs (se 1 (by rfl) ⟨105353, by rfl⟩) R210707
theorem R140585 : Reach 140585 := rs (se 2 (by rfl) ⟨52719, by rfl⟩) R105439
theorem R207827 : Reach 207827 := rs (se 1 (by rfl) ⟨155870, by rfl⟩) R311741
theorem R311849 : Reach 311849 := rs (se 2 (by rfl) ⟨116943, by rfl⟩) R233887
theorem R608123 : Reach 608123 := rs (se 1 (by rfl) ⟨456092, by rfl⟩) R912185
theorem R968759 : Reach 968759 := rs (se 1 (by rfl) ⟨726569, by rfl⟩) R1453139
theorem R315035 : Reach 315035 := rs (se 1 (by rfl) ⟨236276, by rfl⟩) R472553
theorem R26105489 : Reach 26105489 := rs (se 2 (by rfl) ⟨9789558, by rfl⟩) R19579117
theorem R939941 : Reach 939941 := rs (se 4 (by rfl) ⟨88119, by rfl⟩) R176239
theorem R318761 : Reach 318761 := rs (se 2 (by rfl) ⟨119535, by rfl⟩) R239071
theorem R1204307 : Reach 1204307 := rs (se 1 (by rfl) ⟨903230, by rfl⟩) R1806461
theorem R92007 : Reach 92007 := rs (se 1 (by rfl) ⟨69005, by rfl⟩) R138011
theorem R93543 : Reach 93543 := rs (se 1 (by rfl) ⟨70157, by rfl⟩) R140315
theorem R94279 : Reach 94279 := rs (se 1 (by rfl) ⟨70709, by rfl⟩) R141419
theorem R587519 : Reach 587519 := rs (se 1 (by rfl) ⟨440639, by rfl⟩) R881279
theorem R106691975 : Reach 106691975 := rs (se 1 (by rfl) ⟨80018981, by rfl⟩) R160037963
theorem R17403659 : Reach 17403659 := rs (se 1 (by rfl) ⟨13052744, by rfl⟩) R26105489
theorem R790397 : Reach 790397 := rs (se 3 (by rfl) ⟨148199, by rfl⟩) R296399
theorem R626627 : Reach 626627 := rs (se 1 (by rfl) ⟨469970, by rfl⟩) R939941
theorem R530621 : Reach 530621 := rs (se 3 (by rfl) ⟨99491, by rfl⟩) R198983
theorem R138551 : Reach 138551 := rs (se 1 (by rfl) ⟨103913, by rfl⟩) R207827
theorem R568193 : Reach 568193 := rs (se 2 (by rfl) ⟨213072, by rfl⟩) R426145
theorem R207899 : Reach 207899 := rs (se 1 (by rfl) ⟨155924, by rfl⟩) R311849
theorem R175871 : Reach 175871 := rs (se 1 (by rfl) ⟨131903, by rfl⟩) R263807
theorem R405415 : Reach 405415 := rs (se 1 (by rfl) ⟨304061, by rfl⟩) R608123
theorem R210023 : Reach 210023 := rs (se 1 (by rfl) ⟨157517, by rfl⟩) R315035
theorem R212507 : Reach 212507 := rs (se 1 (by rfl) ⟨159380, by rfl⟩) R318761
theorem R802871 : Reach 802871 := rs (se 1 (by rfl) ⟨602153, by rfl⟩) R1204307
theorem R71127983 : Reach 71127983 := rs (se 1 (by rfl) ⟨53345987, by rfl⟩) R106691975
theorem R645839 : Reach 645839 := rs (se 1 (by rfl) ⟨484379, by rfl⟩) R968759
theorem R91167 : Reach 91167 := rs (se 1 (by rfl) ⟨68375, by rfl⟩) R136751
theorem R92159 : Reach 92159 := rs (se 1 (by rfl) ⟨69119, by rfl⟩) R138239
theorem R92231 : Reach 92231 := rs (se 1 (by rfl) ⟨69173, by rfl⟩) R138347
theorem R92671 : Reach 92671 := rs (se 1 (by rfl) ⟨69503, by rfl⟩) R139007
theorem R92923 : Reach 92923 := rs (se 1 (by rfl) ⟨69692, by rfl⟩) R139385
theorem R93183 : Reach 93183 := rs (se 1 (by rfl) ⟨69887, by rfl⟩) R139775
theorem R93647 : Reach 93647 := rs (se 1 (by rfl) ⟨70235, by rfl⟩) R140471
theorem R93723 : Reach 93723 := rs (se 1 (by rfl) ⟨70292, by rfl⟩) R140585
theorem R391679 : Reach 391679 := rs (se 1 (by rfl) ⟨293759, by rfl⟩) R587519
theorem R11602439 : Reach 11602439 := rs (se 1 (by rfl) ⟨8701829, by rfl⟩) R17403659
theorem R526931 : Reach 526931 := rs (se 1 (by rfl) ⟨395198, by rfl⟩) R790397
theorem R47418655 : Reach 47418655 := rs (se 1 (by rfl) ⟨35563991, by rfl⟩) R71127983
theorem R430559 : Reach 430559 := rs (se 1 (by rfl) ⟨322919, by rfl⟩) R645839
theorem R138599 : Reach 138599 := rs (se 1 (by rfl) ⟨103949, by rfl⟩) R207899
theorem R1515181 : Reach 1515181 := rs (se 3 (by rfl) ⟨284096, by rfl⟩) R568193
theorem R140015 : Reach 140015 := rs (se 1 (by rfl) ⟨105011, by rfl⟩) R210023
theorem R468989 : Reach 468989 := rs (se 3 (by rfl) ⟨87935, by rfl⟩) R175871
theorem R141671 : Reach 141671 := rs (se 1 (by rfl) ⟨106253, by rfl⟩) R212507
theorem R535247 : Reach 535247 := rs (se 1 (by rfl) ⟨401435, by rfl⟩) R802871
theorem R540553 : Reach 540553 := rs (se 2 (by rfl) ⟨202707, by rfl⟩) R405415
theorem R353747 : Reach 353747 := rs (se 1 (by rfl) ⟨265310, by rfl⟩) R530621
theorem R92367 : Reach 92367 := rs (se 1 (by rfl) ⟨69275, by rfl⟩) R138551
theorem R261119 : Reach 261119 := rs (se 1 (by rfl) ⟨195839, by rfl⟩) R391679
theorem R1671005 : Reach 1671005 := rs (se 3 (by rfl) ⟨313313, by rfl⟩) R626627
theorem R7734959 : Reach 7734959 := rs (se 1 (by rfl) ⟨5801219, by rfl⟩) R11602439
theorem R235831 : Reach 235831 := rs (se 1 (by rfl) ⟨176873, by rfl⟩) R353747
theorem R174079 : Reach 174079 := rs (se 1 (by rfl) ⟨130559, by rfl⟩) R261119
theorem R63224873 : Reach 63224873 := rs (se 2 (by rfl) ⟨23709327, by rfl⟩) R47418655
theorem R312659 : Reach 312659 := rs (se 1 (by rfl) ⟨234494, by rfl⟩) R468989
theorem R2020241 : Reach 2020241 := rs (se 2 (by rfl) ⟨757590, by rfl⟩) R1515181
theorem R351287 : Reach 351287 := rs (se 1 (by rfl) ⟨263465, by rfl⟩) R526931
theorem R287039 : Reach 287039 := rs (se 1 (by rfl) ⟨215279, by rfl⟩) R430559
theorem R92399 : Reach 92399 := rs (se 1 (by rfl) ⟨69299, by rfl⟩) R138599
theorem R93343 : Reach 93343 := rs (se 1 (by rfl) ⟨70007, by rfl⟩) R140015
theorem R94447 : Reach 94447 := rs (se 1 (by rfl) ⟨70835, by rfl⟩) R141671
theorem R356831 : Reach 356831 := rs (se 1 (by rfl) ⟨267623, by rfl⟩) R535247
theorem R720737 : Reach 720737 := rs (se 2 (by rfl) ⟨270276, by rfl⟩) R540553
theorem R1114003 : Reach 1114003 := rs (se 1 (by rfl) ⟨835502, by rfl⟩) R1671005
theorem R232105 : Reach 232105 := rs (se 2 (by rfl) ⟨87039, by rfl⟩) R174079
theorem R1346827 : Reach 1346827 := rs (se 1 (by rfl) ⟨1010120, by rfl⟩) R2020241
theorem R234191 : Reach 234191 := rs (se 1 (by rfl) ⟨175643, by rfl⟩) R351287
theorem R237887 : Reach 237887 := rs (se 1 (by rfl) ⟨178415, by rfl⟩) R356831
theorem R42149915 : Reach 42149915 := rs (se 1 (by rfl) ⟨31612436, by rfl⟩) R63224873
theorem R5941349 : Reach 5941349 := rs (se 4 (by rfl) ⟨557001, by rfl⟩) R1114003
theorem R208439 : Reach 208439 := rs (se 1 (by rfl) ⟨156329, by rfl⟩) R312659
theorem R5156639 : Reach 5156639 := rs (se 1 (by rfl) ⟨3867479, by rfl⟩) R7734959
theorem R314441 : Reach 314441 := rs (se 2 (by rfl) ⟨117915, by rfl⟩) R235831
theorem R480491 : Reach 480491 := rs (se 1 (by rfl) ⟨360368, by rfl⟩) R720737
theorem R191359 : Reach 191359 := rs (se 1 (by rfl) ⟨143519, by rfl⟩) R287039
theorem R138959 : Reach 138959 := rs (se 1 (by rfl) ⟨104219, by rfl⟩) R208439
theorem R209627 : Reach 209627 := rs (se 1 (by rfl) ⟨157220, by rfl⟩) R314441
theorem R309473 : Reach 309473 := rs (se 2 (by rfl) ⟨116052, by rfl⟩) R232105
theorem R28099943 : Reach 28099943 := rs (se 1 (by rfl) ⟨21074957, by rfl⟩) R42149915
theorem R156127 : Reach 156127 := rs (se 1 (by rfl) ⟨117095, by rfl⟩) R234191
theorem R320327 : Reach 320327 := rs (se 1 (by rfl) ⟨240245, by rfl⟩) R480491
theorem R255145 : Reach 255145 := rs (se 2 (by rfl) ⟨95679, by rfl⟩) R191359
theorem R1795769 : Reach 1795769 := rs (se 2 (by rfl) ⟨673413, by rfl⟩) R1346827
theorem R158591 : Reach 158591 := rs (se 1 (by rfl) ⟨118943, by rfl⟩) R237887
theorem R3960899 : Reach 3960899 := rs (se 1 (by rfl) ⟨2970674, by rfl⟩) R5941349
theorem R3437759 : Reach 3437759 := rs (se 1 (by rfl) ⟨2578319, by rfl⟩) R5156639
theorem R105727 : Reach 105727 := rs (se 1 (by rfl) ⟨79295, by rfl⟩) R158591
theorem R139751 : Reach 139751 := rs (se 1 (by rfl) ⟨104813, by rfl⟩) R209627
theorem R206315 : Reach 206315 := rs (se 1 (by rfl) ⟨154736, by rfl⟩) R309473
theorem R208169 : Reach 208169 := rs (se 2 (by rfl) ⟨78063, by rfl⟩) R156127
theorem R340193 : Reach 340193 := rs (se 2 (by rfl) ⟨127572, by rfl⟩) R255145
theorem R213551 : Reach 213551 := rs (se 1 (by rfl) ⟨160163, by rfl⟩) R320327
theorem R1197179 : Reach 1197179 := rs (se 1 (by rfl) ⟨897884, by rfl⟩) R1795769
theorem R2640599 : Reach 2640599 := rs (se 1 (by rfl) ⟨1980449, by rfl⟩) R3960899
theorem R18733295 : Reach 18733295 := rs (se 1 (by rfl) ⟨14049971, by rfl⟩) R28099943
theorem R9167357 : Reach 9167357 := rs (se 3 (by rfl) ⟨1718879, by rfl⟩) R3437759
theorem R92639 : Reach 92639 := rs (se 1 (by rfl) ⟨69479, by rfl⟩) R138959
theorem R137543 : Reach 137543 := rs (se 1 (by rfl) ⟨103157, by rfl⟩) R206315
theorem R138779 : Reach 138779 := rs (se 1 (by rfl) ⟨104084, by rfl⟩) R208169
theorem R140969 : Reach 140969 := rs (se 2 (by rfl) ⟨52863, by rfl⟩) R105727
theorem R142367 : Reach 142367 := rs (se 1 (by rfl) ⟨106775, by rfl⟩) R213551
theorem R798119 : Reach 798119 := rs (se 1 (by rfl) ⟨598589, by rfl⟩) R1197179
theorem R6111571 : Reach 6111571 := rs (se 1 (by rfl) ⟨4583678, by rfl⟩) R9167357
theorem R49955453 : Reach 49955453 := rs (se 3 (by rfl) ⟨9366647, by rfl⟩) R18733295
theorem R1760399 : Reach 1760399 := rs (se 1 (by rfl) ⟨1320299, by rfl⟩) R2640599
theorem R93167 : Reach 93167 := rs (se 1 (by rfl) ⟨69875, by rfl⟩) R139751
theorem R226795 : Reach 226795 := rs (se 1 (by rfl) ⟨170096, by rfl⟩) R340193
theorem R302393 : Reach 302393 := rs (se 2 (by rfl) ⟨113397, by rfl⟩) R226795
theorem R532079 : Reach 532079 := rs (se 1 (by rfl) ⟨399059, by rfl⟩) R798119
theorem R33303635 : Reach 33303635 := rs (se 1 (by rfl) ⟨24977726, by rfl⟩) R49955453
theorem R8148761 : Reach 8148761 := rs (se 2 (by rfl) ⟨3055785, by rfl⟩) R6111571
theorem R91695 : Reach 91695 := rs (se 1 (by rfl) ⟨68771, by rfl⟩) R137543
theorem R1173599 : Reach 1173599 := rs (se 1 (by rfl) ⟨880199, by rfl⟩) R1760399
theorem R92519 : Reach 92519 := rs (se 1 (by rfl) ⟨69389, by rfl⟩) R138779
theorem R93979 : Reach 93979 := rs (se 1 (by rfl) ⟨70484, by rfl⟩) R140969
theorem R94911 : Reach 94911 := rs (se 1 (by rfl) ⟨71183, by rfl⟩) R142367
theorem R22202423 : Reach 22202423 := rs (se 1 (by rfl) ⟨16651817, by rfl⟩) R33303635
theorem R806381 : Reach 806381 := rs (se 3 (by rfl) ⟨151196, by rfl⟩) R302393
theorem R5432507 : Reach 5432507 := rs (se 1 (by rfl) ⟨4074380, by rfl⟩) R8148761
theorem R354719 : Reach 354719 := rs (se 1 (by rfl) ⟨266039, by rfl⟩) R532079
theorem R782399 : Reach 782399 := rs (se 1 (by rfl) ⟨586799, by rfl⟩) R1173599
theorem R236479 : Reach 236479 := rs (se 1 (by rfl) ⟨177359, by rfl⟩) R354719
theorem R537587 : Reach 537587 := rs (se 1 (by rfl) ⟨403190, by rfl⟩) R806381
theorem R3621671 : Reach 3621671 := rs (se 1 (by rfl) ⟨2716253, by rfl⟩) R5432507
theorem R14801615 : Reach 14801615 := rs (se 1 (by rfl) ⟨11101211, by rfl⟩) R22202423
theorem R521599 : Reach 521599 := rs (se 1 (by rfl) ⟨391199, by rfl⟩) R782399
theorem R9867743 : Reach 9867743 := rs (se 1 (by rfl) ⟨7400807, by rfl⟩) R14801615
theorem R695465 : Reach 695465 := rs (se 2 (by rfl) ⟨260799, by rfl⟩) R521599
theorem R315305 : Reach 315305 := rs (se 2 (by rfl) ⟨118239, by rfl⟩) R236479
theorem R2414447 : Reach 2414447 := rs (se 1 (by rfl) ⟨1810835, by rfl⟩) R3621671
theorem R358391 : Reach 358391 := rs (se 1 (by rfl) ⟨268793, by rfl⟩) R537587
theorem R1609631 : Reach 1609631 := rs (se 1 (by rfl) ⟨1207223, by rfl⟩) R2414447
theorem R463643 : Reach 463643 := rs (se 1 (by rfl) ⟨347732, by rfl⟩) R695465
theorem R955709 : Reach 955709 := rs (se 3 (by rfl) ⟨179195, by rfl⟩) R358391
theorem R210203 : Reach 210203 := rs (se 1 (by rfl) ⟨157652, by rfl⟩) R315305
theorem R6578495 : Reach 6578495 := rs (se 1 (by rfl) ⟨4933871, by rfl⟩) R9867743
theorem R140135 : Reach 140135 := rs (se 1 (by rfl) ⟨105101, by rfl⟩) R210203
theorem R309095 : Reach 309095 := rs (se 1 (by rfl) ⟨231821, by rfl⟩) R463643
theorem R637139 : Reach 637139 := rs (se 1 (by rfl) ⟨477854, by rfl⟩) R955709
theorem R1073087 : Reach 1073087 := rs (se 1 (by rfl) ⟨804815, by rfl⟩) R1609631
theorem R4385663 : Reach 4385663 := rs (se 1 (by rfl) ⟨3289247, by rfl⟩) R6578495
theorem R2923775 : Reach 2923775 := rs (se 1 (by rfl) ⟨2192831, by rfl⟩) R4385663
theorem R206063 : Reach 206063 := rs (se 1 (by rfl) ⟨154547, by rfl⟩) R309095
theorem R715391 : Reach 715391 := rs (se 1 (by rfl) ⟨536543, by rfl⟩) R1073087
theorem R93423 : Reach 93423 := rs (se 1 (by rfl) ⟨70067, by rfl⟩) R140135
theorem R424759 : Reach 424759 := rs (se 1 (by rfl) ⟨318569, by rfl⟩) R637139
theorem R137375 : Reach 137375 := rs (se 1 (by rfl) ⟨103031, by rfl⟩) R206063
theorem R566345 : Reach 566345 := rs (se 2 (by rfl) ⟨212379, by rfl⟩) R424759
theorem R1949183 : Reach 1949183 := rs (se 1 (by rfl) ⟨1461887, by rfl⟩) R2923775
theorem R476927 : Reach 476927 := rs (se 1 (by rfl) ⟨357695, by rfl⟩) R715391
theorem R377563 : Reach 377563 := rs (se 1 (by rfl) ⟨283172, by rfl⟩) R566345
theorem R1299455 : Reach 1299455 := rs (se 1 (by rfl) ⟨974591, by rfl⟩) R1949183
theorem R317951 : Reach 317951 := rs (se 1 (by rfl) ⟨238463, by rfl⟩) R476927
theorem R91583 : Reach 91583 := rs (se 1 (by rfl) ⟨68687, by rfl⟩) R137375
theorem R503417 : Reach 503417 := rs (se 2 (by rfl) ⟨188781, by rfl⟩) R377563
theorem R866303 : Reach 866303 := rs (se 1 (by rfl) ⟨649727, by rfl⟩) R1299455
theorem R211967 : Reach 211967 := rs (se 1 (by rfl) ⟨158975, by rfl⟩) R317951
theorem R335611 : Reach 335611 := rs (se 1 (by rfl) ⟨251708, by rfl⟩) R503417
theorem R141311 : Reach 141311 := rs (se 1 (by rfl) ⟨105983, by rfl⟩) R211967
theorem R577535 : Reach 577535 := rs (se 1 (by rfl) ⟨433151, by rfl⟩) R866303
theorem R447481 : Reach 447481 := rs (se 2 (by rfl) ⟨167805, by rfl⟩) R335611
theorem R94207 : Reach 94207 := rs (se 1 (by rfl) ⟨70655, by rfl⟩) R141311
theorem R1540093 : Reach 1540093 := rs (se 3 (by rfl) ⟨288767, by rfl⟩) R577535
theorem R596641 : Reach 596641 := rs (se 2 (by rfl) ⟨223740, by rfl⟩) R447481
theorem R2053457 : Reach 2053457 := rs (se 2 (by rfl) ⟨770046, by rfl⟩) R1540093
theorem R795521 : Reach 795521 := rs (se 2 (by rfl) ⟨298320, by rfl⟩) R596641
theorem R1368971 : Reach 1368971 := rs (se 1 (by rfl) ⟨1026728, by rfl⟩) R2053457
theorem R530347 : Reach 530347 := rs (se 1 (by rfl) ⟨397760, by rfl⟩) R795521
theorem R912647 : Reach 912647 := rs (se 1 (by rfl) ⟨684485, by rfl⟩) R1368971
theorem R608431 : Reach 608431 := rs (se 1 (by rfl) ⟨456323, by rfl⟩) R912647
theorem R707129 : Reach 707129 := rs (se 2 (by rfl) ⟨265173, by rfl⟩) R530347
theorem R471419 : Reach 471419 := rs (se 1 (by rfl) ⟨353564, by rfl⟩) R707129
theorem R811241 : Reach 811241 := rs (se 2 (by rfl) ⟨304215, by rfl⟩) R608431
theorem R540827 : Reach 540827 := rs (se 1 (by rfl) ⟨405620, by rfl⟩) R811241
theorem R314279 : Reach 314279 := rs (se 1 (by rfl) ⟨235709, by rfl⟩) R471419
theorem R360551 : Reach 360551 := rs (se 1 (by rfl) ⟨270413, by rfl⟩) R540827
theorem R209519 : Reach 209519 := rs (se 1 (by rfl) ⟨157139, by rfl⟩) R314279
theorem R139679 : Reach 139679 := rs (se 1 (by rfl) ⟨104759, by rfl⟩) R209519
theorem R240367 : Reach 240367 := rs (se 1 (by rfl) ⟨180275, by rfl⟩) R360551
theorem R320489 : Reach 320489 := rs (se 2 (by rfl) ⟨120183, by rfl⟩) R240367
theorem R93119 : Reach 93119 := rs (se 1 (by rfl) ⟨69839, by rfl⟩) R139679
theorem R213659 : Reach 213659 := rs (se 1 (by rfl) ⟨160244, by rfl⟩) R320489
theorem R142439 : Reach 142439 := rs (se 1 (by rfl) ⟨106829, by rfl⟩) R213659
theorem R94959 : Reach 94959 := rs (se 1 (by rfl) ⟨71219, by rfl⟩) R142439

theorem C0 (j : ℕ) (h1 : 45565 ≤ j) (h2 : j ≤ 46264) : Reach (2 * j + 1) := by
  interval_cases j
  · exact R91131
  · exact R91133
  · exact R91135
  · exact R91137
  · exact R91139
  · exact R91141
  · exact R91143
  · exact R91145
  · exact R91147
  · exact R91149
  · exact R91151
  · exact R91153
  · exact R91155
  · exact R91157
  · exact R91159
  · exact R91161
  · exact R91163
  · exact R91165
  · exact R91167
  · exact R91169
  · exact R91171
  · exact R91173
  · exact R91175
  · exact R91177
  · exact R91179
  · exact R91181
  · exact R91183
  · exact R91185
  · exact R91187
  · exact R91189
  · exact R91191
  · exact R91193
  · exact R91195
  · exact R91197
  · exact R91199
  · exact R91201
  · exact R91203
  · exact R91205
  · exact R91207
  · exact R91209
  · exact R91211
  · exact R91213
  · exact R91215
  · exact R91217
  · exact R91219
  · exact R91221
  · exact R91223
  · exact R91225
  · exact R91227
  · exact R91229
  · exact R91231
  · exact R91233
  · exact R91235
  · exact R91237
  · exact R91239
  · exact R91241
  · exact R91243
  · exact R91245
  · exact R91247
  · exact R91249
  · exact R91251
  · exact R91253
  · exact R91255
  · exact R91257
  · exact R91259
  · exact R91261
  · exact R91263
  · exact R91265
  · exact R91267
  · exact R91269
  · exact R91271
  · exact R91273
  · exact R91275
  · exact R91277
  · exact R91279
  · exact R91281
  · exact R91283
  · exact R91285
  · exact R91287
  · exact R91289
  · exact R91291
  · exact R91293
  · exact R91295
  · exact R91297
  · exact R91299
  · exact R91301
  · exact R91303
  · exact R91305
  · exact R91307
  · exact R91309
  · exact R91311
  · exact R91313
  · exact R91315
  · exact R91317
  · exact R91319
  · exact R91321
  · exact R91323
  · exact R91325
  · exact R91327
  · exact R91329
  · exact R91331
  · exact R91333
  · exact R91335
  · exact R91337
  · exact R91339
  · exact R91341
  · exact R91343
  · exact R91345
  · exact R91347
  · exact R91349
  · exact R91351
  · exact R91353
  · exact R91355
  · exact R91357
  · exact R91359
  · exact R91361
  · exact R91363
  · exact R91365
  · exact R91367
  · exact R91369
  · exact R91371
  · exact R91373
  · exact R91375
  · exact R91377
  · exact R91379
  · exact R91381
  · exact R91383
  · exact R91385
  · exact R91387
  · exact R91389
  · exact R91391
  · exact R91393
  · exact R91395
  · exact R91397
  · exact R91399
  · exact R91401
  · exact R91403
  · exact R91405
  · exact R91407
  · exact R91409
  · exact R91411
  · exact R91413
  · exact R91415
  · exact R91417
  · exact R91419
  · exact R91421
  · exact R91423
  · exact R91425
  · exact R91427
  · exact R91429
  · exact R91431
  · exact R91433
  · exact R91435
  · exact R91437
  · exact R91439
  · exact R91441
  · exact R91443
  · exact R91445
  · exact R91447
  · exact R91449
  · exact R91451
  · exact R91453
  · exact R91455
  · exact R91457
  · exact R91459
  · exact R91461
  · exact R91463
  · exact R91465
  · exact R91467
  · exact R91469
  · exact R91471
  · exact R91473
  · exact R91475
  · exact R91477
  · exact R91479
  · exact R91481
  · exact R91483
  · exact R91485
  · exact R91487
  · exact R91489
  · exact R91491
  · exact R91493
  · exact R91495
  · exact R91497
  · exact R91499
  · exact R91501
  · exact R91503
  · exact R91505
  · exact R91507
  · exact R91509
  · exact R91511
  · exact R91513
  · exact R91515
  · exact R91517
  · exact R91519
  · exact R91521
  · exact R91523
  · exact R91525
  · exact R91527
  · exact R91529
  · exact R91531
  · exact R91533
  · exact R91535
  · exact R91537
  · exact R91539
  · exact R91541
  · exact R91543
  · exact R91545
  · exact R91547
  · exact R91549
  · exact R91551
  · exact R91553
  · exact R91555
  · exact R91557
  · exact R91559
  · exact R91561
  · exact R91563
  · exact R91565
  · exact R91567
  · exact R91569
  · exact R91571
  · exact R91573
  · exact R91575
  · exact R91577
  · exact R91579
  · exact R91581
  · exact R91583
  · exact R91585
  · exact R91587
  · exact R91589
  · exact R91591
  · exact R91593
  · exact R91595
  · exact R91597
  · exact R91599
  · exact R91601
  · exact R91603
  · exact R91605
  · exact R91607
  · exact R91609
  · exact R91611
  · exact R91613
  · exact R91615
  · exact R91617
  · exact R91619
  · exact R91621
  · exact R91623
  · exact R91625
  · exact R91627
  · exact R91629
  · exact R91631
  · exact R91633
  · exact R91635
  · exact R91637
  · exact R91639
  · exact R91641
  · exact R91643
  · exact R91645
  · exact R91647
  · exact R91649
  · exact R91651
  · exact R91653
  · exact R91655
  · exact R91657
  · exact R91659
  · exact R91661
  · exact R91663
  · exact R91665
  · exact R91667
  · exact R91669
  · exact R91671
  · exact R91673
  · exact R91675
  · exact R91677
  · exact R91679
  · exact R91681
  · exact R91683
  · exact R91685
  · exact R91687
  · exact R91689
  · exact R91691
  · exact R91693
  · exact R91695
  · exact R91697
  · exact R91699
  · exact R91701
  · exact R91703
  · exact R91705
  · exact R91707
  · exact R91709
  · exact R91711
  · exact R91713
  · exact R91715
  · exact R91717
  · exact R91719
  · exact R91721
  · exact R91723
  · exact R91725
  · exact R91727
  · exact R91729
  · exact R91731
  · exact R91733
  · exact R91735
  · exact R91737
  · exact R91739
  · exact R91741
  · exact R91743
  · exact R91745
  · exact R91747
  · exact R91749
  · exact R91751
  · exact R91753
  · exact R91755
  · exact R91757
  · exact R91759
  · exact R91761
  · exact R91763
  · exact R91765
  · exact R91767
  · exact R91769
  · exact R91771
  · exact R91773
  · exact R91775
  · exact R91777
  · exact R91779
  · exact R91781
  · exact R91783
  · exact R91785
  · exact R91787
  · exact R91789
  · exact R91791
  · exact R91793
  · exact R91795
  · exact R91797
  · exact R91799
  · exact R91801
  · exact R91803
  · exact R91805
  · exact R91807
  · exact R91809
  · exact R91811
  · exact R91813
  · exact R91815
  · exact R91817
  · exact R91819
  · exact R91821
  · exact R91823
  · exact R91825
  · exact R91827
  · exact R91829
  · exact R91831
  · exact R91833
  · exact R91835
  · exact R91837
  · exact R91839
  · exact R91841
  · exact R91843
  · exact R91845
  · exact R91847
  · exact R91849
  · exact R91851
  · exact R91853
  · exact R91855
  · exact R91857
  · exact R91859
  · exact R91861
  · exact R91863
  · exact R91865
  · exact R91867
  · exact R91869
  · exact R91871
  · exact R91873
  · exact R91875
  · exact R91877
  · exact R91879
  · exact R91881
  · exact R91883
  · exact R91885
  · exact R91887
  · exact R91889
  · exact R91891
  · exact R91893
  · exact R91895
  · exact R91897
  · exact R91899
  · exact R91901
  · exact R91903
  · exact R91905
  · exact R91907
  · exact R91909
  · exact R91911
  · exact R91913
  · exact R91915
  · exact R91917
  · exact R91919
  · exact R91921
  · exact R91923
  · exact R91925
  · exact R91927
  · exact R91929
  · exact R91931
  · exact R91933
  · exact R91935
  · exact R91937
  · exact R91939
  · exact R91941
  · exact R91943
  · exact R91945
  · exact R91947
  · exact R91949
  · exact R91951
  · exact R91953
  · exact R91955
  · exact R91957
  · exact R91959
  · exact R91961
  · exact R91963
  · exact R91965
  · exact R91967
  · exact R91969
  · exact R91971
  · exact R91973
  · exact R91975
  · exact R91977
  · exact R91979
  · exact R91981
  · exact R91983
  · exact R91985
  · exact R91987
  · exact R91989
  · exact R91991
  · exact R91993
  · exact R91995
  · exact R91997
  · exact R91999
  · exact R92001
  · exact R92003
  · exact R92005
  · exact R92007
  · exact R92009
  · exact R92011
  · exact R92013
  · exact R92015
  · exact R92017
  · exact R92019
  · exact R92021
  · exact R92023
  · exact R92025
  · exact R92027
  · exact R92029
  · exact R92031
  · exact R92033
  · exact R92035
  · exact R92037
  · exact R92039
  · exact R92041
  · exact R92043
  · exact R92045
  · exact R92047
  · exact R92049
  · exact R92051
  · exact R92053
  · exact R92055
  · exact R92057
  · exact R92059
  · exact R92061
  · exact R92063
  · exact R92065
  · exact R92067
  · exact R92069
  · exact R92071
  · exact R92073
  · exact R92075
  · exact R92077
  · exact R92079
  · exact R92081
  · exact R92083
  · exact R92085
  · exact R92087
  · exact R92089
  · exact R92091
  · exact R92093
  · exact R92095
  · exact R92097
  · exact R92099
  · exact R92101
  · exact R92103
  · exact R92105
  · exact R92107
  · exact R92109
  · exact R92111
  · exact R92113
  · exact R92115
  · exact R92117
  · exact R92119
  · exact R92121
  · exact R92123
  · exact R92125
  · exact R92127
  · exact R92129
  · exact R92131
  · exact R92133
  · exact R92135
  · exact R92137
  · exact R92139
  · exact R92141
  · exact R92143
  · exact R92145
  · exact R92147
  · exact R92149
  · exact R92151
  · exact R92153
  · exact R92155
  · exact R92157
  · exact R92159
  · exact R92161
  · exact R92163
  · exact R92165
  · exact R92167
  · exact R92169
  · exact R92171
  · exact R92173
  · exact R92175
  · exact R92177
  · exact R92179
  · exact R92181
  · exact R92183
  · exact R92185
  · exact R92187
  · exact R92189
  · exact R92191
  · exact R92193
  · exact R92195
  · exact R92197
  · exact R92199
  · exact R92201
  · exact R92203
  · exact R92205
  · exact R92207
  · exact R92209
  · exact R92211
  · exact R92213
  · exact R92215
  · exact R92217
  · exact R92219
  · exact R92221
  · exact R92223
  · exact R92225
  · exact R92227
  · exact R92229
  · exact R92231
  · exact R92233
  · exact R92235
  · exact R92237
  · exact R92239
  · exact R92241
  · exact R92243
  · exact R92245
  · exact R92247
  · exact R92249
  · exact R92251
  · exact R92253
  · exact R92255
  · exact R92257
  · exact R92259
  · exact R92261
  · exact R92263
  · exact R92265
  · exact R92267
  · exact R92269
  · exact R92271
  · exact R92273
  · exact R92275
  · exact R92277
  · exact R92279
  · exact R92281
  · exact R92283
  · exact R92285
  · exact R92287
  · exact R92289
  · exact R92291
  · exact R92293
  · exact R92295
  · exact R92297
  · exact R92299
  · exact R92301
  · exact R92303
  · exact R92305
  · exact R92307
  · exact R92309
  · exact R92311
  · exact R92313
  · exact R92315
  · exact R92317
  · exact R92319
  · exact R92321
  · exact R92323
  · exact R92325
  · exact R92327
  · exact R92329
  · exact R92331
  · exact R92333
  · exact R92335
  · exact R92337
  · exact R92339
  · exact R92341
  · exact R92343
  · exact R92345
  · exact R92347
  · exact R92349
  · exact R92351
  · exact R92353
  · exact R92355
  · exact R92357
  · exact R92359
  · exact R92361
  · exact R92363
  · exact R92365
  · exact R92367
  · exact R92369
  · exact R92371
  · exact R92373
  · exact R92375
  · exact R92377
  · exact R92379
  · exact R92381
  · exact R92383
  · exact R92385
  · exact R92387
  · exact R92389
  · exact R92391
  · exact R92393
  · exact R92395
  · exact R92397
  · exact R92399
  · exact R92401
  · exact R92403
  · exact R92405
  · exact R92407
  · exact R92409
  · exact R92411
  · exact R92413
  · exact R92415
  · exact R92417
  · exact R92419
  · exact R92421
  · exact R92423
  · exact R92425
  · exact R92427
  · exact R92429
  · exact R92431
  · exact R92433
  · exact R92435
  · exact R92437
  · exact R92439
  · exact R92441
  · exact R92443
  · exact R92445
  · exact R92447
  · exact R92449
  · exact R92451
  · exact R92453
  · exact R92455
  · exact R92457
  · exact R92459
  · exact R92461
  · exact R92463
  · exact R92465
  · exact R92467
  · exact R92469
  · exact R92471
  · exact R92473
  · exact R92475
  · exact R92477
  · exact R92479
  · exact R92481
  · exact R92483
  · exact R92485
  · exact R92487
  · exact R92489
  · exact R92491
  · exact R92493
  · exact R92495
  · exact R92497
  · exact R92499
  · exact R92501
  · exact R92503
  · exact R92505
  · exact R92507
  · exact R92509
  · exact R92511
  · exact R92513
  · exact R92515
  · exact R92517
  · exact R92519
  · exact R92521
  · exact R92523
  · exact R92525
  · exact R92527
  · exact R92529

theorem C1 (j : ℕ) (h1 : 46265 ≤ j) (h2 : j ≤ 46964) : Reach (2 * j + 1) := by
  interval_cases j
  · exact R92531
  · exact R92533
  · exact R92535
  · exact R92537
  · exact R92539
  · exact R92541
  · exact R92543
  · exact R92545
  · exact R92547
  · exact R92549
  · exact R92551
  · exact R92553
  · exact R92555
  · exact R92557
  · exact R92559
  · exact R92561
  · exact R92563
  · exact R92565
  · exact R92567
  · exact R92569
  · exact R92571
  · exact R92573
  · exact R92575
  · exact R92577
  · exact R92579
  · exact R92581
  · exact R92583
  · exact R92585
  · exact R92587
  · exact R92589
  · exact R92591
  · exact R92593
  · exact R92595
  · exact R92597
  · exact R92599
  · exact R92601
  · exact R92603
  · exact R92605
  · exact R92607
  · exact R92609
  · exact R92611
  · exact R92613
  · exact R92615
  · exact R92617
  · exact R92619
  · exact R92621
  · exact R92623
  · exact R92625
  · exact R92627
  · exact R92629
  · exact R92631
  · exact R92633
  · exact R92635
  · exact R92637
  · exact R92639
  · exact R92641
  · exact R92643
  · exact R92645
  · exact R92647
  · exact R92649
  · exact R92651
  · exact R92653
  · exact R92655
  · exact R92657
  · exact R92659
  · exact R92661
  · exact R92663
  · exact R92665
  · exact R92667
  · exact R92669
  · exact R92671
  · exact R92673
  · exact R92675
  · exact R92677
  · exact R92679
  · exact R92681
  · exact R92683
  · exact R92685
  · exact R92687
  · exact R92689
  · exact R92691
  · exact R92693
  · exact R92695
  · exact R92697
  · exact R92699
  · exact R92701
  · exact R92703
  · exact R92705
  · exact R92707
  · exact R92709
  · exact R92711
  · exact R92713
  · exact R92715
  · exact R92717
  · exact R92719
  · exact R92721
  · exact R92723
  · exact R92725
  · exact R92727
  · exact R92729
  · exact R92731
  · exact R92733
  · exact R92735
  · exact R92737
  · exact R92739
  · exact R92741
  · exact R92743
  · exact R92745
  · exact R92747
  · exact R92749
  · exact R92751
  · exact R92753
  · exact R92755
  · exact R92757
  · exact R92759
  · exact R92761
  · exact R92763
  · exact R92765
  · exact R92767
  · exact R92769
  · exact R92771
  · exact R92773
  · exact R92775
  · exact R92777
  · exact R92779
  · exact R92781
  · exact R92783
  · exact R92785
  · exact R92787
  · exact R92789
  · exact R92791
  · exact R92793
  · exact R92795
  · exact R92797
  · exact R92799
  · exact R92801
  · exact R92803
  · exact R92805
  · exact R92807
  · exact R92809
  · exact R92811
  · exact R92813
  · exact R92815
  · exact R92817
  · exact R92819
  · exact R92821
  · exact R92823
  · exact R92825
  · exact R92827
  · exact R92829
  · exact R92831
  · exact R92833
  · exact R92835
  · exact R92837
  · exact R92839
  · exact R92841
  · exact R92843
  · exact R92845
  · exact R92847
  · exact R92849
  · exact R92851
  · exact R92853
  · exact R92855
  · exact R92857
  · exact R92859
  · exact R92861
  · exact R92863
  · exact R92865
  · exact R92867
  · exact R92869
  · exact R92871
  · exact R92873
  · exact R92875
  · exact R92877
  · exact R92879
  · exact R92881
  · exact R92883
  · exact R92885
  · exact R92887
  · exact R92889
  · exact R92891
  · exact R92893
  · exact R92895
  · exact R92897
  · exact R92899
  · exact R92901
  · exact R92903
  · exact R92905
  · exact R92907
  · exact R92909
  · exact R92911
  · exact R92913
  · exact R92915
  · exact R92917
  · exact R92919
  · exact R92921
  · exact R92923
  · exact R92925
  · exact R92927
  · exact R92929
  · exact R92931
  · exact R92933
  · exact R92935
  · exact R92937
  · exact R92939
  · exact R92941
  · exact R92943
  · exact R92945
  · exact R92947
  · exact R92949
  · exact R92951
  · exact R92953
  · exact R92955
  · exact R92957
  · exact R92959
  · exact R92961
  · exact R92963
  · exact R92965
  · exact R92967
  · exact R92969
  · exact R92971
  · exact R92973
  · exact R92975
  · exact R92977
  · exact R92979
  · exact R92981
  · exact R92983
  · exact R92985
  · exact R92987
  · exact R92989
  · exact R92991
  · exact R92993
  · exact R92995
  · exact R92997
  · exact R92999
  · exact R93001
  · exact R93003
  · exact R93005
  · exact R93007
  · exact R93009
  · exact R93011
  · exact R93013
  · exact R93015
  · exact R93017
  · exact R93019
  · exact R93021
  · exact R93023
  · exact R93025
  · exact R93027
  · exact R93029
  · exact R93031
  · exact R93033
  · exact R93035
  · exact R93037
  · exact R93039
  · exact R93041
  · exact R93043
  · exact R93045
  · exact R93047
  · exact R93049
  · exact R93051
  · exact R93053
  · exact R93055
  · exact R93057
  · exact R93059
  · exact R93061
  · exact R93063
  · exact R93065
  · exact R93067
  · exact R93069
  · exact R93071
  · exact R93073
  · exact R93075
  · exact R93077
  · exact R93079
  · exact R93081
  · exact R93083
  · exact R93085
  · exact R93087
  · exact R93089
  · exact R93091
  · exact R93093
  · exact R93095
  · exact R93097
  · exact R93099
  · exact R93101
  · exact R93103
  · exact R93105
  · exact R93107
  · exact R93109
  · exact R93111
  · exact R93113
  · exact R93115
  · exact R93117
  · exact R93119
  · exact R93121
  · exact R93123
  · exact R93125
  · exact R93127
  · exact R93129
  · exact R93131
  · exact R93133
  · exact R93135
  · exact R93137
  · exact R93139
  · exact R93141
  · exact R93143
  · exact R93145
  · exact R93147
  · exact R93149
  · exact R93151
  · exact R93153
  · exact R93155
  · exact R93157
  · exact R93159
  · exact R93161
  · exact R93163
  · exact R93165
  · exact R93167
  · exact R93169
  · exact R93171
  · exact R93173
  · exact R93175
  · exact R93177
  · exact R93179
  · exact R93181
  · exact R93183
  · exact R93185
  · exact R93187
  · exact R93189
  · exact R93191
  · exact R93193
  · exact R93195
  · exact R93197
  · exact R93199
  · exact R93201
  · exact R93203
  · exact R93205
  · exact R93207
  · exact R93209
  · exact R93211
  · exact R93213
  · exact R93215
  · exact R93217
  · exact R93219
  · exact R93221
  · exact R93223
  · exact R93225
  · exact R93227
  · exact R93229
  · exact R93231
  · exact R93233
  · exact R93235
  · exact R93237
  · exact R93239
  · exact R93241
  · exact R93243
  · exact R93245
  · exact R93247
  · exact R93249
  · exact R93251
  · exact R93253
  · exact R93255
  · exact R93257
  · exact R93259
  · exact R93261
  · exact R93263
  · exact R93265
  · exact R93267
  · exact R93269
  · exact R93271
  · exact R93273
  · exact R93275
  · exact R93277
  · exact R93279
  · exact R93281
  · exact R93283
  · exact R93285
  · exact R93287
  · exact R93289
  · exact R93291
  · exact R93293
  · exact R93295
  · exact R93297
  · exact R93299
  · exact R93301
  · exact R93303
  · exact R93305
  · exact R93307
  · exact R93309
  · exact R93311
  · exact R93313
  · exact R93315
  · exact R93317
  · exact R93319
  · exact R93321
  · exact R93323
  · exact R93325
  · exact R93327
  · exact R93329
  · exact R93331
  · exact R93333
  · exact R93335
  · exact R93337
  · exact R93339
  · exact R93341
  · exact R93343
  · exact R93345
  · exact R93347
  · exact R93349
  · exact R93351
  · exact R93353
  · exact R93355
  · exact R93357
  · exact R93359
  · exact R93361
  · exact R93363
  · exact R93365
  · exact R93367
  · exact R93369
  · exact R93371
  · exact R93373
  · exact R93375
  · exact R93377
  · exact R93379
  · exact R93381
  · exact R93383
  · exact R93385
  · exact R93387
  · exact R93389
  · exact R93391
  · exact R93393
  · exact R93395
  · exact R93397
  · exact R93399
  · exact R93401
  · exact R93403
  · exact R93405
  · exact R93407
  · exact R93409
  · exact R93411
  · exact R93413
  · exact R93415
  · exact R93417
  · exact R93419
  · exact R93421
  · exact R93423
  · exact R93425
  · exact R93427
  · exact R93429
  · exact R93431
  · exact R93433
  · exact R93435
  · exact R93437
  · exact R93439
  · exact R93441
  · exact R93443
  · exact R93445
  · exact R93447
  · exact R93449
  · exact R93451
  · exact R93453
  · exact R93455
  · exact R93457
  · exact R93459
  · exact R93461
  · exact R93463
  · exact R93465
  · exact R93467
  · exact R93469
  · exact R93471
  · exact R93473
  · exact R93475
  · exact R93477
  · exact R93479
  · exact R93481
  · exact R93483
  · exact R93485
  · exact R93487
  · exact R93489
  · exact R93491
  · exact R93493
  · exact R93495
  · exact R93497
  · exact R93499
  · exact R93501
  · exact R93503
  · exact R93505
  · exact R93507
  · exact R93509
  · exact R93511
  · exact R93513
  · exact R93515
  · exact R93517
  · exact R93519
  · exact R93521
  · exact R93523
  · exact R93525
  · exact R93527
  · exact R93529
  · exact R93531
  · exact R93533
  · exact R93535
  · exact R93537
  · exact R93539
  · exact R93541
  · exact R93543
  · exact R93545
  · exact R93547
  · exact R93549
  · exact R93551
  · exact R93553
  · exact R93555
  · exact R93557
  · exact R93559
  · exact R93561
  · exact R93563
  · exact R93565
  · exact R93567
  · exact R93569
  · exact R93571
  · exact R93573
  · exact R93575
  · exact R93577
  · exact R93579
  · exact R93581
  · exact R93583
  · exact R93585
  · exact R93587
  · exact R93589
  · exact R93591
  · exact R93593
  · exact R93595
  · exact R93597
  · exact R93599
  · exact R93601
  · exact R93603
  · exact R93605
  · exact R93607
  · exact R93609
  · exact R93611
  · exact R93613
  · exact R93615
  · exact R93617
  · exact R93619
  · exact R93621
  · exact R93623
  · exact R93625
  · exact R93627
  · exact R93629
  · exact R93631
  · exact R93633
  · exact R93635
  · exact R93637
  · exact R93639
  · exact R93641
  · exact R93643
  · exact R93645
  · exact R93647
  · exact R93649
  · exact R93651
  · exact R93653
  · exact R93655
  · exact R93657
  · exact R93659
  · exact R93661
  · exact R93663
  · exact R93665
  · exact R93667
  · exact R93669
  · exact R93671
  · exact R93673
  · exact R93675
  · exact R93677
  · exact R93679
  · exact R93681
  · exact R93683
  · exact R93685
  · exact R93687
  · exact R93689
  · exact R93691
  · exact R93693
  · exact R93695
  · exact R93697
  · exact R93699
  · exact R93701
  · exact R93703
  · exact R93705
  · exact R93707
  · exact R93709
  · exact R93711
  · exact R93713
  · exact R93715
  · exact R93717
  · exact R93719
  · exact R93721
  · exact R93723
  · exact R93725
  · exact R93727
  · exact R93729
  · exact R93731
  · exact R93733
  · exact R93735
  · exact R93737
  · exact R93739
  · exact R93741
  · exact R93743
  · exact R93745
  · exact R93747
  · exact R93749
  · exact R93751
  · exact R93753
  · exact R93755
  · exact R93757
  · exact R93759
  · exact R93761
  · exact R93763
  · exact R93765
  · exact R93767
  · exact R93769
  · exact R93771
  · exact R93773
  · exact R93775
  · exact R93777
  · exact R93779
  · exact R93781
  · exact R93783
  · exact R93785
  · exact R93787
  · exact R93789
  · exact R93791
  · exact R93793
  · exact R93795
  · exact R93797
  · exact R93799
  · exact R93801
  · exact R93803
  · exact R93805
  · exact R93807
  · exact R93809
  · exact R93811
  · exact R93813
  · exact R93815
  · exact R93817
  · exact R93819
  · exact R93821
  · exact R93823
  · exact R93825
  · exact R93827
  · exact R93829
  · exact R93831
  · exact R93833
  · exact R93835
  · exact R93837
  · exact R93839
  · exact R93841
  · exact R93843
  · exact R93845
  · exact R93847
  · exact R93849
  · exact R93851
  · exact R93853
  · exact R93855
  · exact R93857
  · exact R93859
  · exact R93861
  · exact R93863
  · exact R93865
  · exact R93867
  · exact R93869
  · exact R93871
  · exact R93873
  · exact R93875
  · exact R93877
  · exact R93879
  · exact R93881
  · exact R93883
  · exact R93885
  · exact R93887
  · exact R93889
  · exact R93891
  · exact R93893
  · exact R93895
  · exact R93897
  · exact R93899
  · exact R93901
  · exact R93903
  · exact R93905
  · exact R93907
  · exact R93909
  · exact R93911
  · exact R93913
  · exact R93915
  · exact R93917
  · exact R93919
  · exact R93921
  · exact R93923
  · exact R93925
  · exact R93927
  · exact R93929

theorem C2 (j : ℕ) (h1 : 46965 ≤ j) (h2 : j ≤ 47564) : Reach (2 * j + 1) := by
  interval_cases j
  · exact R93931
  · exact R93933
  · exact R93935
  · exact R93937
  · exact R93939
  · exact R93941
  · exact R93943
  · exact R93945
  · exact R93947
  · exact R93949
  · exact R93951
  · exact R93953
  · exact R93955
  · exact R93957
  · exact R93959
  · exact R93961
  · exact R93963
  · exact R93965
  · exact R93967
  · exact R93969
  · exact R93971
  · exact R93973
  · exact R93975
  · exact R93977
  · exact R93979
  · exact R93981
  · exact R93983
  · exact R93985
  · exact R93987
  · exact R93989
  · exact R93991
  · exact R93993
  · exact R93995
  · exact R93997
  · exact R93999
  · exact R94001
  · exact R94003
  · exact R94005
  · exact R94007
  · exact R94009
  · exact R94011
  · exact R94013
  · exact R94015
  · exact R94017
  · exact R94019
  · exact R94021
  · exact R94023
  · exact R94025
  · exact R94027
  · exact R94029
  · exact R94031
  · exact R94033
  · exact R94035
  · exact R94037
  · exact R94039
  · exact R94041
  · exact R94043
  · exact R94045
  · exact R94047
  · exact R94049
  · exact R94051
  · exact R94053
  · exact R94055
  · exact R94057
  · exact R94059
  · exact R94061
  · exact R94063
  · exact R94065
  · exact R94067
  · exact R94069
  · exact R94071
  · exact R94073
  · exact R94075
  · exact R94077
  · exact R94079
  · exact R94081
  · exact R94083
  · exact R94085
  · exact R94087
  · exact R94089
  · exact R94091
  · exact R94093
  · exact R94095
  · exact R94097
  · exact R94099
  · exact R94101
  · exact R94103
  · exact R94105
  · exact R94107
  · exact R94109
  · exact R94111
  · exact R94113
  · exact R94115
  · exact R94117
  · exact R94119
  · exact R94121
  · exact R94123
  · exact R94125
  · exact R94127
  · exact R94129
  · exact R94131
  · exact R94133
  · exact R94135
  · exact R94137
  · exact R94139
  · exact R94141
  · exact R94143
  · exact R94145
  · exact R94147
  · exact R94149
  · exact R94151
  · exact R94153
  · exact R94155
  · exact R94157
  · exact R94159
  · exact R94161
  · exact R94163
  · exact R94165
  · exact R94167
  · exact R94169
  · exact R94171
  · exact R94173
  · exact R94175
  · exact R94177
  · exact R94179
  · exact R94181
  · exact R94183
  · exact R94185
  · exact R94187
  · exact R94189
  · exact R94191
  · exact R94193
  · exact R94195
  · exact R94197
  · exact R94199
  · exact R94201
  · exact R94203
  · exact R94205
  · exact R94207
  · exact R94209
  · exact R94211
  · exact R94213
  · exact R94215
  · exact R94217
  · exact R94219
  · exact R94221
  · exact R94223
  · exact R94225
  · exact R94227
  · exact R94229
  · exact R94231
  · exact R94233
  · exact R94235
  · exact R94237
  · exact R94239
  · exact R94241
  · exact R94243
  · exact R94245
  · exact R94247
  · exact R94249
  · exact R94251
  · exact R94253
  · exact R94255
  · exact R94257
  · exact R94259
  · exact R94261
  · exact R94263
  · exact R94265
  · exact R94267
  · exact R94269
  · exact R94271
  · exact R94273
  · exact R94275
  · exact R94277
  · exact R94279
  · exact R94281
  · exact R94283
  · exact R94285
  · exact R94287
  · exact R94289
  · exact R94291
  · exact R94293
  · exact R94295
  · exact R94297
  · exact R94299
  · exact R94301
  · exact R94303
  · exact R94305
  · exact R94307
  · exact R94309
  · exact R94311
  · exact R94313
  · exact R94315
  · exact R94317
  · exact R94319
  · exact R94321
  · exact R94323
  · exact R94325
  · exact R94327
  · exact R94329
  · exact R94331
  · exact R94333
  · exact R94335
  · exact R94337
  · exact R94339
  · exact R94341
  · exact R94343
  · exact R94345
  · exact R94347
  · exact R94349
  · exact R94351
  · exact R94353
  · exact R94355
  · exact R94357
  · exact R94359
  · exact R94361
  · exact R94363
  · exact R94365
  · exact R94367
  · exact R94369
  · exact R94371
  · exact R94373
  · exact R94375
  · exact R94377
  · exact R94379
  · exact R94381
  · exact R94383
  · exact R94385
  · exact R94387
  · exact R94389
  · exact R94391
  · exact R94393
  · exact R94395
  · exact R94397
  · exact R94399
  · exact R94401
  · exact R94403
  · exact R94405
  · exact R94407
  · exact R94409
  · exact R94411
  · exact R94413
  · exact R94415
  · exact R94417
  · exact R94419
  · exact R94421
  · exact R94423
  · exact R94425
  · exact R94427
  · exact R94429
  · exact R94431
  · exact R94433
  · exact R94435
  · exact R94437
  · exact R94439
  · exact R94441
  · exact R94443
  · exact R94445
  · exact R94447
  · exact R94449
  · exact R94451
  · exact R94453
  · exact R94455
  · exact R94457
  · exact R94459
  · exact R94461
  · exact R94463
  · exact R94465
  · exact R94467
  · exact R94469
  · exact R94471
  · exact R94473
  · exact R94475
  · exact R94477
  · exact R94479
  · exact R94481
  · exact R94483
  · exact R94485
  · exact R94487
  · exact R94489
  · exact R94491
  · exact R94493
  · exact R94495
  · exact R94497
  · exact R94499
  · exact R94501
  · exact R94503
  · exact R94505
  · exact R94507
  · exact R94509
  · exact R94511
  · exact R94513
  · exact R94515
  · exact R94517
  · exact R94519
  · exact R94521
  · exact R94523
  · exact R94525
  · exact R94527
  · exact R94529
  · exact R94531
  · exact R94533
  · exact R94535
  · exact R94537
  · exact R94539
  · exact R94541
  · exact R94543
  · exact R94545
  · exact R94547
  · exact R94549
  · exact R94551
  · exact R94553
  · exact R94555
  · exact R94557
  · exact R94559
  · exact R94561
  · exact R94563
  · exact R94565
  · exact R94567
  · exact R94569
  · exact R94571
  · exact R94573
  · exact R94575
  · exact R94577
  · exact R94579
  · exact R94581
  · exact R94583
  · exact R94585
  · exact R94587
  · exact R94589
  · exact R94591
  · exact R94593
  · exact R94595
  · exact R94597
  · exact R94599
  · exact R94601
  · exact R94603
  · exact R94605
  · exact R94607
  · exact R94609
  · exact R94611
  · exact R94613
  · exact R94615
  · exact R94617
  · exact R94619
  · exact R94621
  · exact R94623
  · exact R94625
  · exact R94627
  · exact R94629
  · exact R94631
  · exact R94633
  · exact R94635
  · exact R94637
  · exact R94639
  · exact R94641
  · exact R94643
  · exact R94645
  · exact R94647
  · exact R94649
  · exact R94651
  · exact R94653
  · exact R94655
  · exact R94657
  · exact R94659
  · exact R94661
  · exact R94663
  · exact R94665
  · exact R94667
  · exact R94669
  · exact R94671
  · exact R94673
  · exact R94675
  · exact R94677
  · exact R94679
  · exact R94681
  · exact R94683
  · exact R94685
  · exact R94687
  · exact R94689
  · exact R94691
  · exact R94693
  · exact R94695
  · exact R94697
  · exact R94699
  · exact R94701
  · exact R94703
  · exact R94705
  · exact R94707
  · exact R94709
  · exact R94711
  · exact R94713
  · exact R94715
  · exact R94717
  · exact R94719
  · exact R94721
  · exact R94723
  · exact R94725
  · exact R94727
  · exact R94729
  · exact R94731
  · exact R94733
  · exact R94735
  · exact R94737
  · exact R94739
  · exact R94741
  · exact R94743
  · exact R94745
  · exact R94747
  · exact R94749
  · exact R94751
  · exact R94753
  · exact R94755
  · exact R94757
  · exact R94759
  · exact R94761
  · exact R94763
  · exact R94765
  · exact R94767
  · exact R94769
  · exact R94771
  · exact R94773
  · exact R94775
  · exact R94777
  · exact R94779
  · exact R94781
  · exact R94783
  · exact R94785
  · exact R94787
  · exact R94789
  · exact R94791
  · exact R94793
  · exact R94795
  · exact R94797
  · exact R94799
  · exact R94801
  · exact R94803
  · exact R94805
  · exact R94807
  · exact R94809
  · exact R94811
  · exact R94813
  · exact R94815
  · exact R94817
  · exact R94819
  · exact R94821
  · exact R94823
  · exact R94825
  · exact R94827
  · exact R94829
  · exact R94831
  · exact R94833
  · exact R94835
  · exact R94837
  · exact R94839
  · exact R94841
  · exact R94843
  · exact R94845
  · exact R94847
  · exact R94849
  · exact R94851
  · exact R94853
  · exact R94855
  · exact R94857
  · exact R94859
  · exact R94861
  · exact R94863
  · exact R94865
  · exact R94867
  · exact R94869
  · exact R94871
  · exact R94873
  · exact R94875
  · exact R94877
  · exact R94879
  · exact R94881
  · exact R94883
  · exact R94885
  · exact R94887
  · exact R94889
  · exact R94891
  · exact R94893
  · exact R94895
  · exact R94897
  · exact R94899
  · exact R94901
  · exact R94903
  · exact R94905
  · exact R94907
  · exact R94909
  · exact R94911
  · exact R94913
  · exact R94915
  · exact R94917
  · exact R94919
  · exact R94921
  · exact R94923
  · exact R94925
  · exact R94927
  · exact R94929
  · exact R94931
  · exact R94933
  · exact R94935
  · exact R94937
  · exact R94939
  · exact R94941
  · exact R94943
  · exact R94945
  · exact R94947
  · exact R94949
  · exact R94951
  · exact R94953
  · exact R94955
  · exact R94957
  · exact R94959
  · exact R94961
  · exact R94963
  · exact R94965
  · exact R94967
  · exact R94969
  · exact R94971
  · exact R94973
  · exact R94975
  · exact R94977
  · exact R94979
  · exact R94981
  · exact R94983
  · exact R94985
  · exact R94987
  · exact R94989
  · exact R94991
  · exact R94993
  · exact R94995
  · exact R94997
  · exact R94999
  · exact R95001
  · exact R95003
  · exact R95005
  · exact R95007
  · exact R95009
  · exact R95011
  · exact R95013
  · exact R95015
  · exact R95017
  · exact R95019
  · exact R95021
  · exact R95023
  · exact R95025
  · exact R95027
  · exact R95029
  · exact R95031
  · exact R95033
  · exact R95035
  · exact R95037
  · exact R95039
  · exact R95041
  · exact R95043
  · exact R95045
  · exact R95047
  · exact R95049
  · exact R95051
  · exact R95053
  · exact R95055
  · exact R95057
  · exact R95059
  · exact R95061
  · exact R95063
  · exact R95065
  · exact R95067
  · exact R95069
  · exact R95071
  · exact R95073
  · exact R95075
  · exact R95077
  · exact R95079
  · exact R95081
  · exact R95083
  · exact R95085
  · exact R95087
  · exact R95089
  · exact R95091
  · exact R95093
  · exact R95095
  · exact R95097
  · exact R95099
  · exact R95101
  · exact R95103
  · exact R95105
  · exact R95107
  · exact R95109
  · exact R95111
  · exact R95113
  · exact R95115
  · exact R95117
  · exact R95119
  · exact R95121
  · exact R95123
  · exact R95125
  · exact R95127
  · exact R95129

theorem solution (m : ℕ) (hm : 0 < m) (hodd : Odd m) (hle : m ≤ 95130) :
    ∃ k : ℕ, syracuseStep^[k] m = 1 := by
  rcases Nat.lt_or_ge m 91130 with hlo | hlo
  · exact syracuse_reaches_one_below_91130 m hm hodd (by omega)
  obtain ⟨j, rfl⟩ : ∃ j, m = 2 * j + 1 := by obtain ⟨t, ht⟩ := hodd; exact ⟨t, by omega⟩
  rcases Nat.lt_or_ge j 46265 with h0 | h0
  · exact C0 j (by omega) (by omega)
  rcases Nat.lt_or_ge j 46965 with h1 | h1
  · exact C1 j (by omega) (by omega)
  exact C2 j (by omega) (by omega)
