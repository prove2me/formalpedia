-- Prove2me | solution 1 for syracuse_reaches_one_below_83128
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T06:33:15.501349+00:00
-- url     : https://prove2.me/submissions/f2843d14-faa9-4ead-8134-65c42d0ef6e9

import Mathlib
import Definitions.Def_syracuseStep
import Theorems.Thm_syracuse_reaches_one_below_79127

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
theorem B (n : ℕ) (h1 : 0 < n) (h2 : Odd n) (h3 : n ≤ 79126) : Reach n :=
  syracuse_reaches_one_below_79127 n h1 h2 h3
theorem R327685 : Reach 327685 := rs (se 4 (by rfl) ⟨30720, by rfl⟩) (B 61441 (by norm_num) ⟨30720, by rfl⟩ (by norm_num))
theorem R557237 : Reach 557237 := rs (se 5 (by rfl) ⟨26120, by rfl⟩) (B 52241 (by norm_num) ⟨26120, by rfl⟩ (by norm_num))
theorem R98569 : Reach 98569 := rs (se 2 (by rfl) ⟨36963, by rfl⟩) (B 73927 (by norm_num) ⟨36963, by rfl⟩ (by norm_num))
theorem R327989 : Reach 327989 := rs (se 5 (by rfl) ⟨15374, by rfl⟩) (B 30749 (by norm_num) ⟨15374, by rfl⟩ (by norm_num))
theorem R197005 : Reach 197005 := rs (se 3 (by rfl) ⟨36938, by rfl⟩) (B 73877 (by norm_num) ⟨36938, by rfl⟩ (by norm_num))
theorem R393797 : Reach 393797 := rs (se 4 (by rfl) ⟨36918, by rfl⟩) (B 73837 (by norm_num) ⟨36918, by rfl⟩ (by norm_num))
theorem R393893 : Reach 393893 := rs (se 4 (by rfl) ⟨36927, by rfl⟩) (B 73855 (by norm_num) ⟨36927, by rfl⟩ (by norm_num))
theorem R131765 : Reach 131765 := rs (se 5 (by rfl) ⟨6176, by rfl⟩) (B 12353 (by norm_num) ⟨6176, by rfl⟩ (by norm_num))
theorem R131797 : Reach 131797 := rs (se 7 (by rfl) ⟨1544, by rfl⟩) (B 3089 (by norm_num) ⟨1544, by rfl⟩ (by norm_num))
theorem R99145 : Reach 99145 := rs (se 2 (by rfl) ⟨37179, by rfl⟩) (B 74359 (by norm_num) ⟨37179, by rfl⟩ (by norm_num))
theorem R99389 : Reach 99389 := rs (se 3 (by rfl) ⟨18635, by rfl⟩) (B 37271 (by norm_num) ⟨18635, by rfl⟩ (by norm_num))
theorem R99425 : Reach 99425 := rs (se 2 (by rfl) ⟨37284, by rfl⟩) (B 74569 (by norm_num) ⟨37284, by rfl⟩ (by norm_num))
theorem R230501 : Reach 230501 := rs (se 4 (by rfl) ⟨21609, by rfl⟩) (B 43219 (by norm_num) ⟨21609, by rfl⟩ (by norm_num))
theorem R132445 : Reach 132445 := rs (se 3 (by rfl) ⟨24833, by rfl⟩) (B 49667 (by norm_num) ⟨24833, by rfl⟩ (by norm_num))
theorem R460181 : Reach 460181 := rs (se 6 (by rfl) ⟨10785, by rfl⟩) (B 21571 (by norm_num) ⟨10785, by rfl⟩ (by norm_num))
theorem R99733 : Reach 99733 := rs (se 6 (by rfl) ⟨2337, by rfl⟩) (B 4675 (by norm_num) ⟨2337, by rfl⟩ (by norm_num))
theorem R362165 : Reach 362165 := rs (se 5 (by rfl) ⟨16976, by rfl⟩) (B 33953 (by norm_num) ⟨16976, by rfl⟩ (by norm_num))
theorem R198445 : Reach 198445 := rs (se 3 (by rfl) ⟨37208, by rfl⟩) (B 74417 (by norm_num) ⟨37208, by rfl⟩ (by norm_num))
theorem R264005 : Reach 264005 := rs (se 4 (by rfl) ⟨24750, by rfl⟩) (B 49501 (by norm_num) ⟨24750, by rfl⟩ (by norm_num))
theorem R100217 : Reach 100217 := rs (se 2 (by rfl) ⟨37581, by rfl⟩) (B 75163 (by norm_num) ⟨37581, by rfl⟩ (by norm_num))
theorem R100273 : Reach 100273 := rs (se 2 (by rfl) ⟨37602, by rfl⟩) (B 75205 (by norm_num) ⟨37602, by rfl⟩ (by norm_num))
theorem R755669 : Reach 755669 := rs (se 7 (by rfl) ⟨8855, by rfl⟩) (B 17711 (by norm_num) ⟨8855, by rfl⟩ (by norm_num))
theorem R100369 : Reach 100369 := rs (se 2 (by rfl) ⟨37638, by rfl⟩) (B 75277 (by norm_num) ⟨37638, by rfl⟩ (by norm_num))
theorem R166045 : Reach 166045 := rs (se 3 (by rfl) ⟨31133, by rfl⟩) (B 62267 (by norm_num) ⟨31133, by rfl⟩ (by norm_num))
theorem R100541 : Reach 100541 := rs (se 3 (by rfl) ⟨18851, by rfl⟩) (B 37703 (by norm_num) ⟨18851, by rfl⟩ (by norm_num))
theorem R100597 : Reach 100597 := rs (se 5 (by rfl) ⟨4715, by rfl⟩) (B 9431 (by norm_num) ⟨4715, by rfl⟩ (by norm_num))
theorem R166141 : Reach 166141 := rs (se 3 (by rfl) ⟨31151, by rfl⟩) (B 62303 (by norm_num) ⟨31151, by rfl⟩ (by norm_num))
theorem R100693 : Reach 100693 := rs (se 10 (by rfl) ⟨147, by rfl⟩) (B 295 (by norm_num) ⟨147, by rfl⟩ (by norm_num))
theorem R199061 : Reach 199061 := rs (se 6 (by rfl) ⟨4665, by rfl⟩) (B 9331 (by norm_num) ⟨4665, by rfl⟩ (by norm_num))
theorem R133589 : Reach 133589 := rs (se 7 (by rfl) ⟨1565, by rfl⟩) (B 3131 (by norm_num) ⟨1565, by rfl⟩ (by norm_num))
theorem R100865 : Reach 100865 := rs (se 2 (by rfl) ⟨37824, by rfl⟩) (B 75649 (by norm_num) ⟨37824, by rfl⟩ (by norm_num))
theorem R395813 : Reach 395813 := rs (se 4 (by rfl) ⟨37107, by rfl⟩) (B 74215 (by norm_num) ⟨37107, by rfl⟩ (by norm_num))
theorem R100921 : Reach 100921 := rs (se 2 (by rfl) ⟨37845, by rfl⟩) (B 75691 (by norm_num) ⟨37845, by rfl⟩ (by norm_num))
theorem R133717 : Reach 133717 := rs (se 8 (by rfl) ⟨783, by rfl⟩) (B 1567 (by norm_num) ⟨783, by rfl⟩ (by norm_num))
theorem R199253 : Reach 199253 := rs (se 8 (by rfl) ⟨1167, by rfl⟩) (B 2335 (by norm_num) ⟨1167, by rfl⟩ (by norm_num))
theorem R232085 : Reach 232085 := rs (se 6 (by rfl) ⟨5439, by rfl⟩) (B 10879 (by norm_num) ⟨5439, by rfl⟩ (by norm_num))
theorem R101017 : Reach 101017 := rs (se 2 (by rfl) ⟨37881, by rfl⟩) (B 75763 (by norm_num) ⟨37881, by rfl⟩ (by norm_num))
theorem R133805 : Reach 133805 := rs (se 3 (by rfl) ⟨25088, by rfl⟩) (B 50177 (by norm_num) ⟨25088, by rfl⟩ (by norm_num))
theorem R133933 : Reach 133933 := rs (se 3 (by rfl) ⟨25112, by rfl⟩) (B 50225 (by norm_num) ⟨25112, by rfl⟩ (by norm_num))
theorem R101189 : Reach 101189 := rs (se 4 (by rfl) ⟨9486, by rfl⟩) (B 18973 (by norm_num) ⟨9486, by rfl⟩ (by norm_num))
theorem R199541 : Reach 199541 := rs (se 5 (by rfl) ⟨9353, by rfl⟩) (B 18707 (by norm_num) ⟨9353, by rfl⟩ (by norm_num))
theorem R101245 : Reach 101245 := rs (se 3 (by rfl) ⟨18983, by rfl⟩) (B 37967 (by norm_num) ⟨18983, by rfl⟩ (by norm_num))
theorem R134021 : Reach 134021 := rs (se 4 (by rfl) ⟨12564, by rfl⟩) (B 25129 (by norm_num) ⟨12564, by rfl⟩ (by norm_num))
theorem R101341 : Reach 101341 := rs (se 3 (by rfl) ⟨19001, by rfl⟩) (B 38003 (by norm_num) ⟨19001, by rfl⟩ (by norm_num))
theorem R330725 : Reach 330725 := rs (se 4 (by rfl) ⟨31005, by rfl⟩) (B 62011 (by norm_num) ⟨31005, by rfl⟩ (by norm_num))
theorem R134149 : Reach 134149 := rs (se 4 (by rfl) ⟨12576, by rfl⟩) (B 25153 (by norm_num) ⟨12576, by rfl⟩ (by norm_num))
theorem R134237 : Reach 134237 := rs (se 3 (by rfl) ⟨25169, by rfl⟩) (B 50339 (by norm_num) ⟨25169, by rfl⟩ (by norm_num))
theorem R101513 : Reach 101513 := rs (se 2 (by rfl) ⟨38067, by rfl⟩) (B 76135 (by norm_num) ⟨38067, by rfl⟩ (by norm_num))
theorem R101569 : Reach 101569 := rs (se 2 (by rfl) ⟨38088, by rfl⟩) (B 76177 (by norm_num) ⟨38088, by rfl⟩ (by norm_num))
theorem R134365 : Reach 134365 := rs (se 3 (by rfl) ⟨25193, by rfl⟩) (B 50387 (by norm_num) ⟨25193, by rfl⟩ (by norm_num))
theorem R789749 : Reach 789749 := rs (se 5 (by rfl) ⟨37019, by rfl⟩) (B 74039 (by norm_num) ⟨37019, by rfl⟩ (by norm_num))
theorem R101665 : Reach 101665 := rs (se 2 (by rfl) ⟨38124, by rfl⟩) (B 76249 (by norm_num) ⟨38124, by rfl⟩ (by norm_num))
theorem R134453 : Reach 134453 := rs (se 5 (by rfl) ⟨6302, by rfl⟩) (B 12605 (by norm_num) ⟨6302, by rfl⟩ (by norm_num))
theorem R232757 : Reach 232757 := rs (se 5 (by rfl) ⟨10910, by rfl⟩) (B 21821 (by norm_num) ⟨10910, by rfl⟩ (by norm_num))
theorem R134581 : Reach 134581 := rs (se 5 (by rfl) ⟨6308, by rfl⟩) (B 12617 (by norm_num) ⟨6308, by rfl⟩ (by norm_num))
theorem R101837 : Reach 101837 := rs (se 3 (by rfl) ⟨19094, by rfl⟩) (B 38189 (by norm_num) ⟨19094, by rfl⟩ (by norm_num))
theorem R101893 : Reach 101893 := rs (se 4 (by rfl) ⟨9552, by rfl⟩) (B 19105 (by norm_num) ⟨9552, by rfl⟩ (by norm_num))
theorem R134669 : Reach 134669 := rs (se 3 (by rfl) ⟨25250, by rfl⟩) (B 50501 (by norm_num) ⟨25250, by rfl⟩ (by norm_num))
theorem R527957 : Reach 527957 := rs (se 8 (by rfl) ⟨3093, by rfl⟩) (B 6187 (by norm_num) ⟨3093, by rfl⟩ (by norm_num))
theorem R101989 : Reach 101989 := rs (se 4 (by rfl) ⟨9561, by rfl⟩) (B 19123 (by norm_num) ⟨9561, by rfl⟩ (by norm_num))
theorem R200333 : Reach 200333 := rs (se 3 (by rfl) ⟨37562, by rfl⟩) (B 75125 (by norm_num) ⟨37562, by rfl⟩ (by norm_num))
theorem R134797 : Reach 134797 := rs (se 3 (by rfl) ⟨25274, by rfl⟩) (B 50549 (by norm_num) ⟨25274, by rfl⟩ (by norm_num))
theorem R134885 : Reach 134885 := rs (se 4 (by rfl) ⟨12645, by rfl⟩) (B 25291 (by norm_num) ⟨12645, by rfl⟩ (by norm_num))
theorem R233189 : Reach 233189 := rs (se 4 (by rfl) ⟨21861, by rfl⟩) (B 43723 (by norm_num) ⟨21861, by rfl⟩ (by norm_num))
theorem R102161 : Reach 102161 := rs (se 2 (by rfl) ⟨38310, by rfl⟩) (B 76621 (by norm_num) ⟨38310, by rfl⟩ (by norm_num))
theorem R626453 : Reach 626453 := rs (se 6 (by rfl) ⟨14682, by rfl⟩) (B 29365 (by norm_num) ⟨14682, by rfl⟩ (by norm_num))
theorem R102217 : Reach 102217 := rs (se 2 (by rfl) ⟨38331, by rfl⟩) (B 76663 (by norm_num) ⟨38331, by rfl⟩ (by norm_num))
theorem R135013 : Reach 135013 := rs (se 4 (by rfl) ⟨12657, by rfl⟩) (B 25315 (by norm_num) ⟨12657, by rfl⟩ (by norm_num))
theorem R102313 : Reach 102313 := rs (se 2 (by rfl) ⟨38367, by rfl⟩) (B 76735 (by norm_num) ⟨38367, by rfl⟩ (by norm_num))
theorem R397237 : Reach 397237 := rs (se 5 (by rfl) ⟨18620, by rfl⟩) (B 37241 (by norm_num) ⟨18620, by rfl⟩ (by norm_num))
theorem R135101 : Reach 135101 := rs (se 3 (by rfl) ⟨25331, by rfl⟩) (B 50663 (by norm_num) ⟨25331, by rfl⟩ (by norm_num))
theorem R200677 : Reach 200677 := rs (se 4 (by rfl) ⟨18813, by rfl⟩) (B 37627 (by norm_num) ⟨18813, by rfl⟩ (by norm_num))
theorem R135229 : Reach 135229 := rs (se 3 (by rfl) ⟨25355, by rfl⟩) (B 50711 (by norm_num) ⟨25355, by rfl⟩ (by norm_num))
theorem R200789 : Reach 200789 := rs (se 8 (by rfl) ⟨1176, by rfl⟩) (B 2353 (by norm_num) ⟨1176, by rfl⟩ (by norm_num))
theorem R102485 : Reach 102485 := rs (se 8 (by rfl) ⟨600, by rfl⟩) (B 1201 (by norm_num) ⟨600, by rfl⟩ (by norm_num))
theorem R102541 : Reach 102541 := rs (se 3 (by rfl) ⟨19226, by rfl⟩) (B 38453 (by norm_num) ⟨19226, by rfl⟩ (by norm_num))
theorem R135317 : Reach 135317 := rs (se 6 (by rfl) ⟨3171, by rfl⟩) (B 6343 (by norm_num) ⟨3171, by rfl⟩ (by norm_num))
theorem R102637 : Reach 102637 := rs (se 3 (by rfl) ⟨19244, by rfl⟩) (B 38489 (by norm_num) ⟨19244, by rfl⟩ (by norm_num))
theorem R200981 : Reach 200981 := rs (se 6 (by rfl) ⟨4710, by rfl⟩) (B 9421 (by norm_num) ⟨4710, by rfl⟩ (by norm_num))
theorem R135445 : Reach 135445 := rs (se 6 (by rfl) ⟨3174, by rfl⟩) (B 6349 (by norm_num) ⟨3174, by rfl⟩ (by norm_num))
theorem R135533 : Reach 135533 := rs (se 3 (by rfl) ⟨25412, by rfl⟩) (B 50825 (by norm_num) ⟨25412, by rfl⟩ (by norm_num))
theorem R102809 : Reach 102809 := rs (se 2 (by rfl) ⟨38553, by rfl⟩) (B 77107 (by norm_num) ⟨38553, by rfl⟩ (by norm_num))
theorem R102865 : Reach 102865 := rs (se 2 (by rfl) ⟨38574, by rfl⟩) (B 77149 (by norm_num) ⟨38574, by rfl⟩ (by norm_num))
theorem R233941 : Reach 233941 := rs (se 7 (by rfl) ⟨2741, by rfl⟩) (B 5483 (by norm_num) ⟨2741, by rfl⟩ (by norm_num))
theorem R102889 : Reach 102889 := rs (se 2 (by rfl) ⟨38583, by rfl⟩) (B 77167 (by norm_num) ⟨38583, by rfl⟩ (by norm_num))
theorem R135661 : Reach 135661 := rs (se 3 (by rfl) ⟨25436, by rfl⟩) (B 50873 (by norm_num) ⟨25436, by rfl⟩ (by norm_num))
theorem R102961 : Reach 102961 := rs (se 2 (by rfl) ⟨38610, by rfl⟩) (B 77221 (by norm_num) ⟨38610, by rfl⟩ (by norm_num))
theorem R135749 : Reach 135749 := rs (se 4 (by rfl) ⟨12726, by rfl⟩) (B 25453 (by norm_num) ⟨12726, by rfl⟩ (by norm_num))
theorem R168533 : Reach 168533 := rs (se 8 (by rfl) ⟨987, by rfl⟩) (B 1975 (by norm_num) ⟨987, by rfl⟩ (by norm_num))
theorem R201325 : Reach 201325 := rs (se 3 (by rfl) ⟨37748, by rfl⟩) (B 75497 (by norm_num) ⟨37748, by rfl⟩ (by norm_num))
theorem R135877 : Reach 135877 := rs (se 4 (by rfl) ⟨12738, by rfl⟩) (B 25477 (by norm_num) ⟨12738, by rfl⟩ (by norm_num))
theorem R201437 : Reach 201437 := rs (se 3 (by rfl) ⟨37769, by rfl⟩) (B 75539 (by norm_num) ⟨37769, by rfl⟩ (by norm_num))
theorem R103133 : Reach 103133 := rs (se 3 (by rfl) ⟨19337, by rfl⟩) (B 38675 (by norm_num) ⟨19337, by rfl⟩ (by norm_num))
theorem R103189 : Reach 103189 := rs (se 6 (by rfl) ⟨2418, by rfl⟩) (B 4837 (by norm_num) ⟨2418, by rfl⟩ (by norm_num))
theorem R135965 : Reach 135965 := rs (se 3 (by rfl) ⟨25493, by rfl⟩) (B 50987 (by norm_num) ⟨25493, by rfl⟩ (by norm_num))
theorem R103285 : Reach 103285 := rs (se 5 (by rfl) ⟨4841, by rfl⟩) (B 9683 (by norm_num) ⟨4841, by rfl⟩ (by norm_num))
theorem R103289 : Reach 103289 := rs (se 2 (by rfl) ⟨38733, by rfl⟩) (B 77467 (by norm_num) ⟨38733, by rfl⟩ (by norm_num))
theorem R234389 : Reach 234389 := rs (se 6 (by rfl) ⟨5493, by rfl⟩) (B 10987 (by norm_num) ⟨5493, by rfl⟩ (by norm_num))
theorem R201629 : Reach 201629 := rs (se 3 (by rfl) ⟨37805, by rfl⟩) (B 75611 (by norm_num) ⟨37805, by rfl⟩ (by norm_num))
theorem R136093 : Reach 136093 := rs (se 3 (by rfl) ⟨25517, by rfl⟩) (B 51035 (by norm_num) ⟨25517, by rfl⟩ (by norm_num))
theorem R103393 : Reach 103393 := rs (se 2 (by rfl) ⟨38772, by rfl⟩) (B 77545 (by norm_num) ⟨38772, by rfl⟩ (by norm_num))
theorem R136181 : Reach 136181 := rs (se 5 (by rfl) ⟨6383, by rfl⟩) (B 12767 (by norm_num) ⟨6383, by rfl⟩ (by norm_num))
theorem R103457 : Reach 103457 := rs (se 2 (by rfl) ⟨38796, by rfl⟩) (B 77593 (by norm_num) ⟨38796, by rfl⟩ (by norm_num))
theorem R103513 : Reach 103513 := rs (se 2 (by rfl) ⟨38817, by rfl⟩) (B 77635 (by norm_num) ⟨38817, by rfl⟩ (by norm_num))
theorem R136309 : Reach 136309 := rs (se 5 (by rfl) ⟨6389, by rfl⟩) (B 12779 (by norm_num) ⟨6389, by rfl⟩ (by norm_num))
theorem R103609 : Reach 103609 := rs (se 2 (by rfl) ⟨38853, by rfl⟩) (B 77707 (by norm_num) ⟨38853, by rfl⟩ (by norm_num))
theorem R267461 : Reach 267461 := rs (se 4 (by rfl) ⟨25074, by rfl⟩) (B 50149 (by norm_num) ⟨25074, by rfl⟩ (by norm_num))
theorem R136397 : Reach 136397 := rs (se 3 (by rfl) ⟨25574, by rfl⟩) (B 51149 (by norm_num) ⟨25574, by rfl⟩ (by norm_num))
theorem R201973 : Reach 201973 := rs (se 5 (by rfl) ⟨9467, by rfl⟩) (B 18935 (by norm_num) ⟨9467, by rfl⟩ (by norm_num))
theorem R136525 : Reach 136525 := rs (se 3 (by rfl) ⟨25598, by rfl⟩) (B 51197 (by norm_num) ⟨25598, by rfl⟩ (by norm_num))
theorem R202085 : Reach 202085 := rs (se 4 (by rfl) ⟨18945, by rfl⟩) (B 37891 (by norm_num) ⟨18945, by rfl⟩ (by norm_num))
theorem R103781 : Reach 103781 := rs (se 4 (by rfl) ⟨9729, by rfl⟩) (B 19459 (by norm_num) ⟨9729, by rfl⟩ (by norm_num))
theorem R103837 : Reach 103837 := rs (se 3 (by rfl) ⟨19469, by rfl⟩) (B 38939 (by norm_num) ⟨19469, by rfl⟩ (by norm_num))
theorem R136613 : Reach 136613 := rs (se 4 (by rfl) ⟨12807, by rfl⟩) (B 25615 (by norm_num) ⟨12807, by rfl⟩ (by norm_num))
theorem R300469 : Reach 300469 := rs (se 5 (by rfl) ⟨14084, by rfl⟩) (B 28169 (by norm_num) ⟨14084, by rfl⟩ (by norm_num))
theorem R103933 : Reach 103933 := rs (se 3 (by rfl) ⟨19487, by rfl⟩) (B 38975 (by norm_num) ⟨19487, by rfl⟩ (by norm_num))
theorem R955925 : Reach 955925 := rs (se 6 (by rfl) ⟨22404, by rfl⟩) (B 44809 (by norm_num) ⟨22404, by rfl⟩ (by norm_num))
theorem R202277 : Reach 202277 := rs (se 4 (by rfl) ⟨18963, by rfl⟩) (B 37927 (by norm_num) ⟨18963, by rfl⟩ (by norm_num))
theorem R136741 : Reach 136741 := rs (se 4 (by rfl) ⟨12819, by rfl⟩) (B 25639 (by norm_num) ⟨12819, by rfl⟩ (by norm_num))
theorem R267893 : Reach 267893 := rs (se 5 (by rfl) ⟨12557, by rfl⟩) (B 25115 (by norm_num) ⟨12557, by rfl⟩ (by norm_num))
theorem R136829 : Reach 136829 := rs (se 3 (by rfl) ⟨25655, by rfl⟩) (B 51311 (by norm_num) ⟨25655, by rfl⟩ (by norm_num))
theorem R104105 : Reach 104105 := rs (se 2 (by rfl) ⟨39039, by rfl⟩) (B 78079 (by norm_num) ⟨39039, by rfl⟩ (by norm_num))
theorem R104161 : Reach 104161 := rs (se 2 (by rfl) ⟨39060, by rfl⟩) (B 78121 (by norm_num) ⟨39060, by rfl⟩ (by norm_num))
theorem R300773 : Reach 300773 := rs (se 4 (by rfl) ⟨28197, by rfl⟩) (B 56395 (by norm_num) ⟨28197, by rfl⟩ (by norm_num))
theorem R136957 : Reach 136957 := rs (se 3 (by rfl) ⟨25679, by rfl⟩) (B 51359 (by norm_num) ⟨25679, by rfl⟩ (by norm_num))
theorem R104257 : Reach 104257 := rs (se 2 (by rfl) ⟨39096, by rfl⟩) (B 78193 (by norm_num) ⟨39096, by rfl⟩ (by norm_num))
theorem R137045 : Reach 137045 := rs (se 9 (by rfl) ⟨401, by rfl⟩) (B 803 (by norm_num) ⟨401, by rfl⟩ (by norm_num))
theorem R202621 : Reach 202621 := rs (se 3 (by rfl) ⟨37991, by rfl⟩) (B 75983 (by norm_num) ⟨37991, by rfl⟩ (by norm_num))
theorem R137173 : Reach 137173 := rs (se 7 (by rfl) ⟨1607, by rfl⟩) (B 3215 (by norm_num) ⟨1607, by rfl⟩ (by norm_num))
theorem R202733 : Reach 202733 := rs (se 3 (by rfl) ⟨38012, by rfl⟩) (B 76025 (by norm_num) ⟨38012, by rfl⟩ (by norm_num))
theorem R104429 : Reach 104429 := rs (se 3 (by rfl) ⟨19580, by rfl⟩) (B 39161 (by norm_num) ⟨19580, by rfl⟩ (by norm_num))
theorem R268325 : Reach 268325 := rs (se 4 (by rfl) ⟨25155, by rfl⟩) (B 50311 (by norm_num) ⟨25155, by rfl⟩ (by norm_num))
theorem R104485 : Reach 104485 := rs (se 4 (by rfl) ⟨9795, by rfl⟩) (B 19591 (by norm_num) ⟨9795, by rfl⟩ (by norm_num))
theorem R137261 : Reach 137261 := rs (se 3 (by rfl) ⟨25736, by rfl⟩) (B 51473 (by norm_num) ⟨25736, by rfl⟩ (by norm_num))
theorem R104581 : Reach 104581 := rs (se 4 (by rfl) ⟨9804, by rfl⟩) (B 19609 (by norm_num) ⟨9804, by rfl⟩ (by norm_num))
theorem R137389 : Reach 137389 := rs (se 3 (by rfl) ⟨25760, by rfl⟩) (B 51521 (by norm_num) ⟨25760, by rfl⟩ (by norm_num))
theorem R202925 : Reach 202925 := rs (se 3 (by rfl) ⟨38048, by rfl⟩) (B 76097 (by norm_num) ⟨38048, by rfl⟩ (by norm_num))
theorem R170237 : Reach 170237 := rs (se 3 (by rfl) ⟨31919, by rfl⟩) (B 63839 (by norm_num) ⟨31919, by rfl⟩ (by norm_num))
theorem R137477 : Reach 137477 := rs (se 4 (by rfl) ⟨12888, by rfl⟩) (B 25777 (by norm_num) ⟨12888, by rfl⟩ (by norm_num))
theorem R104753 : Reach 104753 := rs (se 2 (by rfl) ⟨39282, by rfl⟩) (B 78565 (by norm_num) ⟨39282, by rfl⟩ (by norm_num))
theorem R104809 : Reach 104809 := rs (se 2 (by rfl) ⟨39303, by rfl⟩) (B 78607 (by norm_num) ⟨39303, by rfl⟩ (by norm_num))
theorem R137605 : Reach 137605 := rs (se 4 (by rfl) ⟨12900, by rfl⟩) (B 25801 (by norm_num) ⟨12900, by rfl⟩ (by norm_num))
theorem R170381 : Reach 170381 := rs (se 3 (by rfl) ⟨31946, by rfl⟩) (B 63893 (by norm_num) ⟨31946, by rfl⟩ (by norm_num))
theorem R104905 : Reach 104905 := rs (se 2 (by rfl) ⟨39339, by rfl⟩) (B 78679 (by norm_num) ⟨39339, by rfl⟩ (by norm_num))
theorem R268757 : Reach 268757 := rs (se 7 (by rfl) ⟨3149, by rfl⟩) (B 6299 (by norm_num) ⟨3149, by rfl⟩ (by norm_num))
theorem R137693 : Reach 137693 := rs (se 3 (by rfl) ⟨25817, by rfl⟩) (B 51635 (by norm_num) ⟨25817, by rfl⟩ (by norm_num))
theorem R203269 : Reach 203269 := rs (se 4 (by rfl) ⟨19056, by rfl⟩) (B 38113 (by norm_num) ⟨19056, by rfl⟩ (by norm_num))
theorem R137821 : Reach 137821 := rs (se 3 (by rfl) ⟨25841, by rfl⟩) (B 51683 (by norm_num) ⟨25841, by rfl⟩ (by norm_num))
theorem R203381 : Reach 203381 := rs (se 5 (by rfl) ⟨9533, by rfl⟩) (B 19067 (by norm_num) ⟨9533, by rfl⟩ (by norm_num))
theorem R105077 : Reach 105077 := rs (se 5 (by rfl) ⟨4925, by rfl⟩) (B 9851 (by norm_num) ⟨4925, by rfl⟩ (by norm_num))
theorem R105133 : Reach 105133 := rs (se 3 (by rfl) ⟨19712, by rfl⟩) (B 39425 (by norm_num) ⟨19712, by rfl⟩ (by norm_num))
theorem R137909 : Reach 137909 := rs (se 5 (by rfl) ⟨6464, by rfl⟩) (B 12929 (by norm_num) ⟨6464, by rfl⟩ (by norm_num))
theorem R137933 : Reach 137933 := rs (se 3 (by rfl) ⟨25862, by rfl⟩) (B 51725 (by norm_num) ⟨25862, by rfl⟩ (by norm_num))
theorem R170741 : Reach 170741 := rs (se 5 (by rfl) ⟨8003, by rfl⟩) (B 16007 (by norm_num) ⟨8003, by rfl⟩ (by norm_num))
theorem R138037 : Reach 138037 := rs (se 5 (by rfl) ⟨6470, by rfl⟩) (B 12941 (by norm_num) ⟨6470, by rfl⟩ (by norm_num))
theorem R727861 : Reach 727861 := rs (se 5 (by rfl) ⟨34118, by rfl⟩) (B 68237 (by norm_num) ⟨34118, by rfl⟩ (by norm_num))
theorem R203573 : Reach 203573 := rs (se 5 (by rfl) ⟨9542, by rfl⟩) (B 19085 (by norm_num) ⟨9542, by rfl⟩ (by norm_num))
theorem R105301 : Reach 105301 := rs (se 9 (by rfl) ⟨308, by rfl⟩) (B 617 (by norm_num) ⟨308, by rfl⟩ (by norm_num))
theorem R269189 : Reach 269189 := rs (se 4 (by rfl) ⟨25236, by rfl⟩) (B 50473 (by norm_num) ⟨25236, by rfl⟩ (by norm_num))
theorem R138125 : Reach 138125 := rs (se 3 (by rfl) ⟨25898, by rfl⟩) (B 51797 (by norm_num) ⟨25898, by rfl⟩ (by norm_num))
theorem R1579925 : Reach 1579925 := rs (se 6 (by rfl) ⟨37029, by rfl⟩) (B 74059 (by norm_num) ⟨37029, by rfl⟩ (by norm_num))
theorem R138253 : Reach 138253 := rs (se 3 (by rfl) ⟨25922, by rfl⟩) (B 51845 (by norm_num) ⟨25922, by rfl⟩ (by norm_num))
theorem R138341 : Reach 138341 := rs (se 4 (by rfl) ⟨12969, by rfl⟩) (B 25939 (by norm_num) ⟨12969, by rfl⟩ (by norm_num))
theorem R203917 : Reach 203917 := rs (se 3 (by rfl) ⟨38234, by rfl⟩) (B 76469 (by norm_num) ⟨38234, by rfl⟩ (by norm_num))
theorem R138469 : Reach 138469 := rs (se 4 (by rfl) ⟨12981, by rfl⟩) (B 25963 (by norm_num) ⟨12981, by rfl⟩ (by norm_num))
theorem R236789 : Reach 236789 := rs (se 5 (by rfl) ⟨11099, by rfl⟩) (B 22199 (by norm_num) ⟨11099, by rfl⟩ (by norm_num))
theorem R204029 : Reach 204029 := rs (se 3 (by rfl) ⟨38255, by rfl⟩) (B 76511 (by norm_num) ⟨38255, by rfl⟩ (by norm_num))
theorem R269621 : Reach 269621 := rs (se 5 (by rfl) ⟨12638, by rfl⟩) (B 25277 (by norm_num) ⟨12638, by rfl⟩ (by norm_num))
theorem R138557 : Reach 138557 := rs (se 3 (by rfl) ⟨25979, by rfl⟩) (B 51959 (by norm_num) ⟨25979, by rfl⟩ (by norm_num))
theorem R204221 : Reach 204221 := rs (se 3 (by rfl) ⟨38291, by rfl⟩) (B 76583 (by norm_num) ⟨38291, by rfl⟩ (by norm_num))
theorem R138685 : Reach 138685 := rs (se 3 (by rfl) ⟨26003, by rfl⟩) (B 52007 (by norm_num) ⟨26003, by rfl⟩ (by norm_num))
theorem R138773 : Reach 138773 := rs (se 6 (by rfl) ⟨3252, by rfl⟩) (B 6505 (by norm_num) ⟨3252, by rfl⟩ (by norm_num))
theorem R400949 : Reach 400949 := rs (se 5 (by rfl) ⟨18794, by rfl⟩) (B 37589 (by norm_num) ⟨18794, by rfl⟩ (by norm_num))
theorem R171629 : Reach 171629 := rs (se 3 (by rfl) ⟨32180, by rfl⟩) (B 64361 (by norm_num) ⟨32180, by rfl⟩ (by norm_num))
theorem R138901 : Reach 138901 := rs (se 6 (by rfl) ⟨3255, by rfl⟩) (B 6511 (by norm_num) ⟨3255, by rfl⟩ (by norm_num))
theorem R270053 : Reach 270053 := rs (se 4 (by rfl) ⟨25317, by rfl⟩) (B 50635 (by norm_num) ⟨25317, by rfl⟩ (by norm_num))
theorem R138989 : Reach 138989 := rs (se 3 (by rfl) ⟨26060, by rfl⟩) (B 52121 (by norm_num) ⟨26060, by rfl⟩ (by norm_num))
theorem R204565 : Reach 204565 := rs (se 6 (by rfl) ⟨4794, by rfl⟩) (B 9589 (by norm_num) ⟨4794, by rfl⟩ (by norm_num))
theorem R302885 : Reach 302885 := rs (se 4 (by rfl) ⟨28395, by rfl⟩) (B 56791 (by norm_num) ⟨28395, by rfl⟩ (by norm_num))
theorem R171877 : Reach 171877 := rs (se 4 (by rfl) ⟨16113, by rfl⟩) (B 32227 (by norm_num) ⟨16113, by rfl⟩ (by norm_num))
theorem R237413 : Reach 237413 := rs (se 4 (by rfl) ⟨22257, by rfl⟩) (B 44515 (by norm_num) ⟨22257, by rfl⟩ (by norm_num))
theorem R139117 : Reach 139117 := rs (se 3 (by rfl) ⟨26084, by rfl⟩) (B 52169 (by norm_num) ⟨26084, by rfl⟩ (by norm_num))
theorem R204677 : Reach 204677 := rs (se 4 (by rfl) ⟨19188, by rfl⟩) (B 38377 (by norm_num) ⟨19188, by rfl⟩ (by norm_num))
theorem R794549 : Reach 794549 := rs (se 5 (by rfl) ⟨37244, by rfl⟩) (B 74489 (by norm_num) ⟨37244, by rfl⟩ (by norm_num))
theorem R139205 : Reach 139205 := rs (se 4 (by rfl) ⟨13050, by rfl⟩) (B 26101 (by norm_num) ⟨13050, by rfl⟩ (by norm_num))
theorem R303173 : Reach 303173 := rs (se 4 (by rfl) ⟨28422, by rfl⟩) (B 56845 (by norm_num) ⟨28422, by rfl⟩ (by norm_num))
theorem R204869 : Reach 204869 := rs (se 4 (by rfl) ⟨19206, by rfl⟩) (B 38413 (by norm_num) ⟨19206, by rfl⟩ (by norm_num))
theorem R139333 : Reach 139333 := rs (se 4 (by rfl) ⟨13062, by rfl⟩) (B 26125 (by norm_num) ⟨13062, by rfl⟩ (by norm_num))
theorem R270485 : Reach 270485 := rs (se 6 (by rfl) ⟨6339, by rfl⟩) (B 12679 (by norm_num) ⟨6339, by rfl⟩ (by norm_num))
theorem R139421 : Reach 139421 := rs (se 3 (by rfl) ⟨26141, by rfl⟩) (B 52283 (by norm_num) ⟨26141, by rfl⟩ (by norm_num))
theorem R139549 : Reach 139549 := rs (se 3 (by rfl) ⟨26165, by rfl⟩) (B 52331 (by norm_num) ⟨26165, by rfl⟩ (by norm_num))
theorem R172381 : Reach 172381 := rs (se 3 (by rfl) ⟨32321, by rfl⟩) (B 64643 (by norm_num) ⟨32321, by rfl⟩ (by norm_num))
theorem R139637 : Reach 139637 := rs (se 5 (by rfl) ⟨6545, by rfl⟩) (B 13091 (by norm_num) ⟨6545, by rfl⟩ (by norm_num))
theorem R205213 : Reach 205213 := rs (se 3 (by rfl) ⟨38477, by rfl⟩) (B 76955 (by norm_num) ⟨38477, by rfl⟩ (by norm_num))
theorem R139765 : Reach 139765 := rs (se 5 (by rfl) ⟨6551, by rfl⟩) (B 13103 (by norm_num) ⟨6551, by rfl⟩ (by norm_num))
theorem R205325 : Reach 205325 := rs (se 3 (by rfl) ⟨38498, by rfl⟩) (B 76997 (by norm_num) ⟨38498, by rfl⟩ (by norm_num))
theorem R270917 : Reach 270917 := rs (se 4 (by rfl) ⟨25398, by rfl⟩) (B 50797 (by norm_num) ⟨25398, by rfl⟩ (by norm_num))
theorem R139853 : Reach 139853 := rs (se 3 (by rfl) ⟨26222, by rfl⟩) (B 52445 (by norm_num) ⟨26222, by rfl⟩ (by norm_num))
theorem R139909 : Reach 139909 := rs (se 4 (by rfl) ⟨13116, by rfl⟩) (B 26233 (by norm_num) ⟨13116, by rfl⟩ (by norm_num))
theorem R205517 : Reach 205517 := rs (se 3 (by rfl) ⟨38534, by rfl⟩) (B 77069 (by norm_num) ⟨38534, by rfl⟩ (by norm_num))
theorem R139981 : Reach 139981 := rs (se 3 (by rfl) ⟨26246, by rfl⟩) (B 52493 (by norm_num) ⟨26246, by rfl⟩ (by norm_num))
theorem R402149 : Reach 402149 := rs (se 4 (by rfl) ⟨37701, by rfl⟩) (B 75403 (by norm_num) ⟨37701, by rfl⟩ (by norm_num))
theorem R140069 : Reach 140069 := rs (se 4 (by rfl) ⟨13131, by rfl⟩) (B 26263 (by norm_num) ⟨13131, by rfl⟩ (by norm_num))
theorem R402245 : Reach 402245 := rs (se 4 (by rfl) ⟨37710, by rfl⟩) (B 75421 (by norm_num) ⟨37710, by rfl⟩ (by norm_num))
theorem R140197 : Reach 140197 := rs (se 4 (by rfl) ⟨13143, by rfl⟩) (B 26287 (by norm_num) ⟨13143, by rfl⟩ (by norm_num))
theorem R271349 : Reach 271349 := rs (se 5 (by rfl) ⟨12719, by rfl⟩) (B 25439 (by norm_num) ⟨12719, by rfl⟩ (by norm_num))
theorem R205861 : Reach 205861 := rs (se 4 (by rfl) ⟨19299, by rfl⟩) (B 38599 (by norm_num) ⟨19299, by rfl⟩ (by norm_num))
theorem R205973 : Reach 205973 := rs (se 6 (by rfl) ⟨4827, by rfl⟩) (B 9655 (by norm_num) ⟨4827, by rfl⟩ (by norm_num))
theorem R173261 : Reach 173261 := rs (se 3 (by rfl) ⟨32486, by rfl⟩) (B 64973 (by norm_num) ⟨32486, by rfl⟩ (by norm_num))
theorem R173269 : Reach 173269 := rs (se 7 (by rfl) ⟨2030, by rfl⟩) (B 4061 (by norm_num) ⟨2030, by rfl⟩ (by norm_num))
theorem R304357 : Reach 304357 := rs (se 4 (by rfl) ⟨28533, by rfl⟩) (B 57067 (by norm_num) ⟨28533, by rfl⟩ (by norm_num))
theorem R599381 : Reach 599381 := rs (se 12 (by rfl) ⟨219, by rfl⟩) (B 439 (by norm_num) ⟨219, by rfl⟩ (by norm_num))
theorem R206165 : Reach 206165 := rs (se 12 (by rfl) ⟨75, by rfl⟩) (B 151 (by norm_num) ⟨75, by rfl⟩ (by norm_num))
theorem R664949 : Reach 664949 := rs (se 5 (by rfl) ⟨31169, by rfl⟩) (B 62339 (by norm_num) ⟨31169, by rfl⟩ (by norm_num))
theorem R271781 : Reach 271781 := rs (se 4 (by rfl) ⟨25479, by rfl⟩) (B 50959 (by norm_num) ⟨25479, by rfl⟩ (by norm_num))
theorem R304661 : Reach 304661 := rs (se 6 (by rfl) ⟨7140, by rfl⟩) (B 14281 (by norm_num) ⟨7140, by rfl⟩ (by norm_num))
theorem R108101 : Reach 108101 := rs (se 4 (by rfl) ⟨10134, by rfl⟩) (B 20269 (by norm_num) ⟨10134, by rfl⟩ (by norm_num))
theorem R206509 : Reach 206509 := rs (se 3 (by rfl) ⟨38720, by rfl⟩) (B 77441 (by norm_num) ⟨38720, by rfl⟩ (by norm_num))
theorem R173765 : Reach 173765 := rs (se 4 (by rfl) ⟨16290, by rfl⟩) (B 32581 (by norm_num) ⟨16290, by rfl⟩ (by norm_num))
theorem R108253 : Reach 108253 := rs (se 3 (by rfl) ⟨20297, by rfl⟩) (B 40595 (by norm_num) ⟨20297, by rfl⟩ (by norm_num))
theorem R206621 : Reach 206621 := rs (se 3 (by rfl) ⟨38741, by rfl⟩) (B 77483 (by norm_num) ⟨38741, by rfl⟩ (by norm_num))
theorem R272213 : Reach 272213 := rs (se 9 (by rfl) ⟨797, by rfl⟩) (B 1595 (by norm_num) ⟨797, by rfl⟩ (by norm_num))
theorem R108469 : Reach 108469 := rs (se 5 (by rfl) ⟨5084, by rfl⟩) (B 10169 (by norm_num) ⟨5084, by rfl⟩ (by norm_num))
theorem R206813 : Reach 206813 := rs (se 3 (by rfl) ⟨38777, by rfl⟩) (B 77555 (by norm_num) ⟨38777, by rfl⟩ (by norm_num))
theorem R403541 : Reach 403541 := rs (se 8 (by rfl) ⟨2364, by rfl⟩) (B 4729 (by norm_num) ⟨2364, by rfl⟩ (by norm_num))
theorem R338165 : Reach 338165 := rs (se 5 (by rfl) ⟨15851, by rfl⟩) (B 31703 (by norm_num) ⟨15851, by rfl⟩ (by norm_num))
theorem R272645 : Reach 272645 := rs (se 4 (by rfl) ⟨25560, by rfl⟩) (B 51121 (by norm_num) ⟨25560, by rfl⟩ (by norm_num))
theorem R207157 : Reach 207157 := rs (se 5 (by rfl) ⟨9710, by rfl⟩) (B 19421 (by norm_num) ⟨9710, by rfl⟩ (by norm_num))
theorem R108869 : Reach 108869 := rs (se 4 (by rfl) ⟨10206, by rfl⟩) (B 20413 (by norm_num) ⟨10206, by rfl⟩ (by norm_num))
theorem R108901 : Reach 108901 := rs (se 4 (by rfl) ⟨10209, by rfl⟩) (B 20419 (by norm_num) ⟨10209, by rfl⟩ (by norm_num))
theorem R207269 : Reach 207269 := rs (se 4 (by rfl) ⟨19431, by rfl⟩) (B 38863 (by norm_num) ⟨19431, by rfl⟩ (by norm_num))
theorem R404021 : Reach 404021 := rs (se 5 (by rfl) ⟨18938, by rfl⟩) (B 37877 (by norm_num) ⟨18938, by rfl⟩ (by norm_num))
theorem R174653 : Reach 174653 := rs (se 3 (by rfl) ⟨32747, by rfl⟩) (B 65495 (by norm_num) ⟨32747, by rfl⟩ (by norm_num))
theorem R207461 : Reach 207461 := rs (se 4 (by rfl) ⟨19449, by rfl⟩) (B 38899 (by norm_num) ⟨19449, by rfl⟩ (by norm_num))
theorem R207485 : Reach 207485 := rs (se 3 (by rfl) ⟨38903, by rfl⟩) (B 77807 (by norm_num) ⟨38903, by rfl⟩ (by norm_num))
theorem R273077 : Reach 273077 := rs (se 5 (by rfl) ⟨12800, by rfl⟩) (B 25601 (by norm_num) ⟨12800, by rfl⟩ (by norm_num))
theorem R174773 : Reach 174773 := rs (se 5 (by rfl) ⟨8192, by rfl⟩) (B 16385 (by norm_num) ⟨8192, by rfl⟩ (by norm_num))
theorem R404165 : Reach 404165 := rs (se 4 (by rfl) ⟨37890, by rfl⟩) (B 75781 (by norm_num) ⟨37890, by rfl⟩ (by norm_num))
theorem R207805 : Reach 207805 := rs (se 3 (by rfl) ⟨38963, by rfl⟩) (B 77927 (by norm_num) ⟨38963, by rfl⟩ (by norm_num))
theorem R338917 : Reach 338917 := rs (se 4 (by rfl) ⟨31773, by rfl⟩) (B 63547 (by norm_num) ⟨31773, by rfl⟩ (by norm_num))
theorem R207917 : Reach 207917 := rs (se 3 (by rfl) ⟨38984, by rfl⟩) (B 77969 (by norm_num) ⟨38984, by rfl⟩ (by norm_num))
theorem R470069 : Reach 470069 := rs (se 5 (by rfl) ⟨22034, by rfl⟩) (B 44069 (by norm_num) ⟨22034, by rfl⟩ (by norm_num))
theorem R207973 : Reach 207973 := rs (se 4 (by rfl) ⟨19497, by rfl⟩) (B 38995 (by norm_num) ⟨19497, by rfl⟩ (by norm_num))
theorem R273509 : Reach 273509 := rs (se 4 (by rfl) ⟨25641, by rfl⟩) (B 51283 (by norm_num) ⟨25641, by rfl⟩ (by norm_num))
theorem R208109 : Reach 208109 := rs (se 3 (by rfl) ⟨39020, by rfl⟩) (B 78041 (by norm_num) ⟨39020, by rfl⟩ (by norm_num))
theorem R175405 : Reach 175405 := rs (se 3 (by rfl) ⟨32888, by rfl⟩) (B 65777 (by norm_num) ⟨32888, by rfl⟩ (by norm_num))
theorem R404837 : Reach 404837 := rs (se 4 (by rfl) ⟨37953, by rfl⟩) (B 75907 (by norm_num) ⟨37953, by rfl⟩ (by norm_num))
theorem R273941 : Reach 273941 := rs (se 6 (by rfl) ⟨6420, by rfl⟩) (B 12841 (by norm_num) ⟨6420, by rfl⟩ (by norm_num))
theorem R208453 : Reach 208453 := rs (se 4 (by rfl) ⟨19542, by rfl⟩) (B 39085 (by norm_num) ⟨19542, by rfl⟩ (by norm_num))
theorem R306773 : Reach 306773 := rs (se 8 (by rfl) ⟨1797, by rfl⟩) (B 3595 (by norm_num) ⟨1797, by rfl⟩ (by norm_num))
theorem R536149 : Reach 536149 := rs (se 8 (by rfl) ⟨3141, by rfl⟩) (B 6283 (by norm_num) ⟨3141, by rfl⟩ (by norm_num))
theorem R208565 : Reach 208565 := rs (se 5 (by rfl) ⟨9776, by rfl⟩) (B 19553 (by norm_num) ⟨9776, by rfl⟩ (by norm_num))
theorem R110269 : Reach 110269 := rs (se 3 (by rfl) ⟨20675, by rfl⟩) (B 41351 (by norm_num) ⟨20675, by rfl⟩ (by norm_num))
theorem R339653 : Reach 339653 := rs (se 4 (by rfl) ⟨31842, by rfl⟩) (B 63685 (by norm_num) ⟨31842, by rfl⟩ (by norm_num))
theorem R307061 : Reach 307061 := rs (se 5 (by rfl) ⟨14393, by rfl⟩) (B 28787 (by norm_num) ⟨14393, by rfl⟩ (by norm_num))
theorem R208757 : Reach 208757 := rs (se 5 (by rfl) ⟨9785, by rfl⟩) (B 19571 (by norm_num) ⟨9785, by rfl⟩ (by norm_num))
theorem R274373 : Reach 274373 := rs (se 4 (by rfl) ⟨25722, by rfl⟩) (B 51445 (by norm_num) ⟨25722, by rfl⟩ (by norm_num))
theorem R176293 : Reach 176293 := rs (se 4 (by rfl) ⟨16527, by rfl⟩) (B 33055 (by norm_num) ⟨16527, by rfl⟩ (by norm_num))
theorem R209101 : Reach 209101 := rs (se 3 (by rfl) ⟨39206, by rfl⟩) (B 78413 (by norm_num) ⟨39206, by rfl⟩ (by norm_num))
theorem R176413 : Reach 176413 := rs (se 3 (by rfl) ⟨33077, by rfl⟩) (B 66155 (by norm_num) ⟨33077, by rfl⟩ (by norm_num))
theorem R209213 : Reach 209213 := rs (se 3 (by rfl) ⟨39227, by rfl⟩) (B 78455 (by norm_num) ⟨39227, by rfl⟩ (by norm_num))
theorem R274805 : Reach 274805 := rs (se 5 (by rfl) ⟨12881, by rfl⟩) (B 25763 (by norm_num) ⟨12881, by rfl⟩ (by norm_num))
theorem R209405 : Reach 209405 := rs (se 3 (by rfl) ⟨39263, by rfl⟩) (B 78527 (by norm_num) ⟨39263, by rfl⟩ (by norm_num))
theorem R176669 : Reach 176669 := rs (se 3 (by rfl) ⟨33125, by rfl⟩) (B 66251 (by norm_num) ⟨33125, by rfl⟩ (by norm_num))
theorem R406133 : Reach 406133 := rs (se 5 (by rfl) ⟨19037, by rfl⟩) (B 38075 (by norm_num) ⟨19037, by rfl⟩ (by norm_num))
theorem R209533 : Reach 209533 := rs (se 3 (by rfl) ⟨39287, by rfl⟩) (B 78575 (by norm_num) ⟨39287, by rfl⟩ (by norm_num))
theorem R111397 : Reach 111397 := rs (se 4 (by rfl) ⟨10443, by rfl⟩) (B 20887 (by norm_num) ⟨10443, by rfl⟩ (by norm_num))
theorem R275237 : Reach 275237 := rs (se 4 (by rfl) ⟨25803, by rfl⟩) (B 51607 (by norm_num) ⟨25803, by rfl⟩ (by norm_num))
theorem R8926037 : Reach 8926037 := rs (se 9 (by rfl) ⟨26150, by rfl⟩) (B 52301 (by norm_num) ⟨26150, by rfl⟩ (by norm_num))
theorem R209749 : Reach 209749 := rs (se 9 (by rfl) ⟨614, by rfl⟩) (B 1229 (by norm_num) ⟨614, by rfl⟩ (by norm_num))
theorem R209861 : Reach 209861 := rs (se 4 (by rfl) ⟨19674, by rfl⟩) (B 39349 (by norm_num) ⟨19674, by rfl⟩ (by norm_num))
theorem R603125 : Reach 603125 := rs (se 5 (by rfl) ⟨28271, by rfl⟩) (B 56543 (by norm_num) ⟨28271, by rfl⟩ (by norm_num))
theorem R308245 : Reach 308245 := rs (se 6 (by rfl) ⟨7224, by rfl⟩) (B 14449 (by norm_num) ⟨7224, by rfl⟩ (by norm_num))
theorem R144445 : Reach 144445 := rs (se 3 (by rfl) ⟨27083, by rfl⟩) (B 54167 (by norm_num) ⟨27083, by rfl⟩ (by norm_num))
theorem R144509 : Reach 144509 := rs (se 3 (by rfl) ⟨27095, by rfl⟩) (B 54191 (by norm_num) ⟨27095, by rfl⟩ (by norm_num))
theorem R210053 : Reach 210053 := rs (se 4 (by rfl) ⟨19692, by rfl⟩) (B 39385 (by norm_num) ⟨19692, by rfl⟩ (by norm_num))
theorem R275669 : Reach 275669 := rs (se 7 (by rfl) ⟨3230, by rfl⟩) (B 6461 (by norm_num) ⟨3230, by rfl⟩ (by norm_num))
theorem R79129 : Reach 79129 := rs (se 2 (by rfl) ⟨29673, by rfl⟩) (B 59347 (by norm_num) ⟨29673, by rfl⟩ (by norm_num))
theorem R79133 : Reach 79133 := rs (se 3 (by rfl) ⟨14837, by rfl⟩) (B 29675 (by norm_num) ⟨14837, by rfl⟩ (by norm_num))
theorem R79137 : Reach 79137 := rs (se 2 (by rfl) ⟨29676, by rfl⟩) (B 59353 (by norm_num) ⟨29676, by rfl⟩ (by norm_num))
theorem R79141 : Reach 79141 := rs (se 4 (by rfl) ⟨7419, by rfl⟩) (B 14839 (by norm_num) ⟨7419, by rfl⟩ (by norm_num))
theorem R79145 : Reach 79145 := rs (se 2 (by rfl) ⟨29679, by rfl⟩) (B 59359 (by norm_num) ⟨29679, by rfl⟩ (by norm_num))
theorem R79149 : Reach 79149 := rs (se 3 (by rfl) ⟨14840, by rfl⟩) (B 29681 (by norm_num) ⟨14840, by rfl⟩ (by norm_num))
theorem R79153 : Reach 79153 := rs (se 2 (by rfl) ⟨29682, by rfl⟩) (B 59365 (by norm_num) ⟨29682, by rfl⟩ (by norm_num))
theorem R79157 : Reach 79157 := rs (se 5 (by rfl) ⟨3710, by rfl⟩) (B 7421 (by norm_num) ⟨3710, by rfl⟩ (by norm_num))
theorem R79161 : Reach 79161 := rs (se 2 (by rfl) ⟨29685, by rfl⟩) (B 59371 (by norm_num) ⟨29685, by rfl⟩ (by norm_num))
theorem R79165 : Reach 79165 := rs (se 3 (by rfl) ⟨14843, by rfl⟩) (B 29687 (by norm_num) ⟨14843, by rfl⟩ (by norm_num))
theorem R79169 : Reach 79169 := rs (se 2 (by rfl) ⟨29688, by rfl⟩) (B 59377 (by norm_num) ⟨29688, by rfl⟩ (by norm_num))
theorem R79173 : Reach 79173 := rs (se 4 (by rfl) ⟨7422, by rfl⟩) (B 14845 (by norm_num) ⟨7422, by rfl⟩ (by norm_num))
theorem R308549 : Reach 308549 := rs (se 4 (by rfl) ⟨28926, by rfl⟩) (B 57853 (by norm_num) ⟨28926, by rfl⟩ (by norm_num))
theorem R79177 : Reach 79177 := rs (se 2 (by rfl) ⟨29691, by rfl⟩) (B 59383 (by norm_num) ⟨29691, by rfl⟩ (by norm_num))
theorem R79181 : Reach 79181 := rs (se 3 (by rfl) ⟨14846, by rfl⟩) (B 29693 (by norm_num) ⟨14846, by rfl⟩ (by norm_num))
theorem R79185 : Reach 79185 := rs (se 2 (by rfl) ⟨29694, by rfl⟩) (B 59389 (by norm_num) ⟨29694, by rfl⟩ (by norm_num))
theorem R79189 : Reach 79189 := rs (se 13 (by rfl) ⟨14, by rfl⟩) (B 29 (by norm_num) ⟨14, by rfl⟩ (by norm_num))
theorem R79193 : Reach 79193 := rs (se 2 (by rfl) ⟨29697, by rfl⟩) (B 59395 (by norm_num) ⟨29697, by rfl⟩ (by norm_num))
theorem R79197 : Reach 79197 := rs (se 3 (by rfl) ⟨14849, by rfl⟩) (B 29699 (by norm_num) ⟨14849, by rfl⟩ (by norm_num))
theorem R79201 : Reach 79201 := rs (se 2 (by rfl) ⟨29700, by rfl⟩) (B 59401 (by norm_num) ⟨29700, by rfl⟩ (by norm_num))
theorem R79205 : Reach 79205 := rs (se 4 (by rfl) ⟨7425, by rfl⟩) (B 14851 (by norm_num) ⟨7425, by rfl⟩ (by norm_num))
theorem R79209 : Reach 79209 := rs (se 2 (by rfl) ⟨29703, by rfl⟩) (B 59407 (by norm_num) ⟨29703, by rfl⟩ (by norm_num))
theorem R79213 : Reach 79213 := rs (se 3 (by rfl) ⟨14852, by rfl⟩) (B 29705 (by norm_num) ⟨14852, by rfl⟩ (by norm_num))
theorem R79217 : Reach 79217 := rs (se 2 (by rfl) ⟨29706, by rfl⟩) (B 59413 (by norm_num) ⟨29706, by rfl⟩ (by norm_num))
theorem R79221 : Reach 79221 := rs (se 5 (by rfl) ⟨3713, by rfl⟩) (B 7427 (by norm_num) ⟨3713, by rfl⟩ (by norm_num))
theorem R79225 : Reach 79225 := rs (se 2 (by rfl) ⟨29709, by rfl⟩) (B 59419 (by norm_num) ⟨29709, by rfl⟩ (by norm_num))
theorem R79229 : Reach 79229 := rs (se 3 (by rfl) ⟨14855, by rfl⟩) (B 29711 (by norm_num) ⟨14855, by rfl⟩ (by norm_num))
theorem R79233 : Reach 79233 := rs (se 2 (by rfl) ⟨29712, by rfl⟩) (B 59425 (by norm_num) ⟨29712, by rfl⟩ (by norm_num))
theorem R79237 : Reach 79237 := rs (se 4 (by rfl) ⟨7428, by rfl⟩) (B 14857 (by norm_num) ⟨7428, by rfl⟩ (by norm_num))
theorem R79241 : Reach 79241 := rs (se 2 (by rfl) ⟨29715, by rfl⟩) (B 59431 (by norm_num) ⟨29715, by rfl⟩ (by norm_num))
theorem R79245 : Reach 79245 := rs (se 3 (by rfl) ⟨14858, by rfl⟩) (B 29717 (by norm_num) ⟨14858, by rfl⟩ (by norm_num))
theorem R79249 : Reach 79249 := rs (se 2 (by rfl) ⟨29718, by rfl⟩) (B 59437 (by norm_num) ⟨29718, by rfl⟩ (by norm_num))
theorem R79253 : Reach 79253 := rs (se 6 (by rfl) ⟨1857, by rfl⟩) (B 3715 (by norm_num) ⟨1857, by rfl⟩ (by norm_num))
theorem R79257 : Reach 79257 := rs (se 2 (by rfl) ⟨29721, by rfl⟩) (B 59443 (by norm_num) ⟨29721, by rfl⟩ (by norm_num))
theorem R79261 : Reach 79261 := rs (se 3 (by rfl) ⟨14861, by rfl⟩) (B 29723 (by norm_num) ⟨14861, by rfl⟩ (by norm_num))
theorem R79265 : Reach 79265 := rs (se 2 (by rfl) ⟨29724, by rfl⟩) (B 59449 (by norm_num) ⟨29724, by rfl⟩ (by norm_num))
theorem R79269 : Reach 79269 := rs (se 4 (by rfl) ⟨7431, by rfl⟩) (B 14863 (by norm_num) ⟨7431, by rfl⟩ (by norm_num))
theorem R79273 : Reach 79273 := rs (se 2 (by rfl) ⟨29727, by rfl⟩) (B 59455 (by norm_num) ⟨29727, by rfl⟩ (by norm_num))
theorem R79277 : Reach 79277 := rs (se 3 (by rfl) ⟨14864, by rfl⟩) (B 29729 (by norm_num) ⟨14864, by rfl⟩ (by norm_num))
theorem R79281 : Reach 79281 := rs (se 2 (by rfl) ⟨29730, by rfl⟩) (B 59461 (by norm_num) ⟨29730, by rfl⟩ (by norm_num))
theorem R79285 : Reach 79285 := rs (se 5 (by rfl) ⟨3716, by rfl⟩) (B 7433 (by norm_num) ⟨3716, by rfl⟩ (by norm_num))
theorem R79289 : Reach 79289 := rs (se 2 (by rfl) ⟨29733, by rfl⟩) (B 59467 (by norm_num) ⟨29733, by rfl⟩ (by norm_num))
theorem R79293 : Reach 79293 := rs (se 3 (by rfl) ⟨14867, by rfl⟩) (B 29735 (by norm_num) ⟨14867, by rfl⟩ (by norm_num))
theorem R79297 : Reach 79297 := rs (se 2 (by rfl) ⟨29736, by rfl⟩) (B 59473 (by norm_num) ⟨29736, by rfl⟩ (by norm_num))
theorem R79301 : Reach 79301 := rs (se 4 (by rfl) ⟨7434, by rfl⟩) (B 14869 (by norm_num) ⟨7434, by rfl⟩ (by norm_num))
theorem R79305 : Reach 79305 := rs (se 2 (by rfl) ⟨29739, by rfl⟩) (B 59479 (by norm_num) ⟨29739, by rfl⟩ (by norm_num))
theorem R79309 : Reach 79309 := rs (se 3 (by rfl) ⟨14870, by rfl⟩) (B 29741 (by norm_num) ⟨14870, by rfl⟩ (by norm_num))
theorem R79313 : Reach 79313 := rs (se 2 (by rfl) ⟨29742, by rfl⟩) (B 59485 (by norm_num) ⟨29742, by rfl⟩ (by norm_num))
theorem R79317 : Reach 79317 := rs (se 7 (by rfl) ⟨929, by rfl⟩) (B 1859 (by norm_num) ⟨929, by rfl⟩ (by norm_num))
theorem R79321 : Reach 79321 := rs (se 2 (by rfl) ⟨29745, by rfl⟩) (B 59491 (by norm_num) ⟨29745, by rfl⟩ (by norm_num))
theorem R79325 : Reach 79325 := rs (se 3 (by rfl) ⟨14873, by rfl⟩) (B 29747 (by norm_num) ⟨14873, by rfl⟩ (by norm_num))
theorem R210397 : Reach 210397 := rs (se 3 (by rfl) ⟨39449, by rfl⟩) (B 78899 (by norm_num) ⟨39449, by rfl⟩ (by norm_num))
theorem R79329 : Reach 79329 := rs (se 2 (by rfl) ⟨29748, by rfl⟩) (B 59497 (by norm_num) ⟨29748, by rfl⟩ (by norm_num))
theorem R79333 : Reach 79333 := rs (se 4 (by rfl) ⟨7437, by rfl⟩) (B 14875 (by norm_num) ⟨7437, by rfl⟩ (by norm_num))
theorem R79337 : Reach 79337 := rs (se 2 (by rfl) ⟨29751, by rfl⟩) (B 59503 (by norm_num) ⟨29751, by rfl⟩ (by norm_num))
theorem R79341 : Reach 79341 := rs (se 3 (by rfl) ⟨14876, by rfl⟩) (B 29753 (by norm_num) ⟨14876, by rfl⟩ (by norm_num))
theorem R79345 : Reach 79345 := rs (se 2 (by rfl) ⟨29754, by rfl⟩) (B 59509 (by norm_num) ⟨29754, by rfl⟩ (by norm_num))
theorem R79349 : Reach 79349 := rs (se 5 (by rfl) ⟨3719, by rfl⟩) (B 7439 (by norm_num) ⟨3719, by rfl⟩ (by norm_num))
theorem R79353 : Reach 79353 := rs (se 2 (by rfl) ⟨29757, by rfl⟩) (B 59515 (by norm_num) ⟨29757, by rfl⟩ (by norm_num))
theorem R79357 : Reach 79357 := rs (se 3 (by rfl) ⟨14879, by rfl⟩) (B 29759 (by norm_num) ⟨14879, by rfl⟩ (by norm_num))
theorem R79361 : Reach 79361 := rs (se 2 (by rfl) ⟨29760, by rfl⟩) (B 59521 (by norm_num) ⟨29760, by rfl⟩ (by norm_num))
theorem R79365 : Reach 79365 := rs (se 4 (by rfl) ⟨7440, by rfl⟩) (B 14881 (by norm_num) ⟨7440, by rfl⟩ (by norm_num))
theorem R79369 : Reach 79369 := rs (se 2 (by rfl) ⟨29763, by rfl⟩) (B 59527 (by norm_num) ⟨29763, by rfl⟩ (by norm_num))
theorem R79373 : Reach 79373 := rs (se 3 (by rfl) ⟨14882, by rfl⟩) (B 29765 (by norm_num) ⟨14882, by rfl⟩ (by norm_num))
theorem R79377 : Reach 79377 := rs (se 2 (by rfl) ⟨29766, by rfl⟩) (B 59533 (by norm_num) ⟨29766, by rfl⟩ (by norm_num))
theorem R79381 : Reach 79381 := rs (se 6 (by rfl) ⟨1860, by rfl⟩) (B 3721 (by norm_num) ⟨1860, by rfl⟩ (by norm_num))
theorem R79385 : Reach 79385 := rs (se 2 (by rfl) ⟨29769, by rfl⟩) (B 59539 (by norm_num) ⟨29769, by rfl⟩ (by norm_num))
theorem R79389 : Reach 79389 := rs (se 3 (by rfl) ⟨14885, by rfl⟩) (B 29771 (by norm_num) ⟨14885, by rfl⟩ (by norm_num))
theorem R79393 : Reach 79393 := rs (se 2 (by rfl) ⟨29772, by rfl⟩) (B 59545 (by norm_num) ⟨29772, by rfl⟩ (by norm_num))
theorem R79397 : Reach 79397 := rs (se 4 (by rfl) ⟨7443, by rfl⟩) (B 14887 (by norm_num) ⟨7443, by rfl⟩ (by norm_num))
theorem R79401 : Reach 79401 := rs (se 2 (by rfl) ⟨29775, by rfl⟩) (B 59551 (by norm_num) ⟨29775, by rfl⟩ (by norm_num))
theorem R79405 : Reach 79405 := rs (se 3 (by rfl) ⟨14888, by rfl⟩) (B 29777 (by norm_num) ⟨14888, by rfl⟩ (by norm_num))
theorem R79409 : Reach 79409 := rs (se 2 (by rfl) ⟨29778, by rfl⟩) (B 59557 (by norm_num) ⟨29778, by rfl⟩ (by norm_num))
theorem R79413 : Reach 79413 := rs (se 5 (by rfl) ⟨3722, by rfl⟩) (B 7445 (by norm_num) ⟨3722, by rfl⟩ (by norm_num))
theorem R79417 : Reach 79417 := rs (se 2 (by rfl) ⟨29781, by rfl⟩) (B 59563 (by norm_num) ⟨29781, by rfl⟩ (by norm_num))
theorem R79421 : Reach 79421 := rs (se 3 (by rfl) ⟨14891, by rfl⟩) (B 29783 (by norm_num) ⟨14891, by rfl⟩ (by norm_num))
theorem R79425 : Reach 79425 := rs (se 2 (by rfl) ⟨29784, by rfl⟩) (B 59569 (by norm_num) ⟨29784, by rfl⟩ (by norm_num))
theorem R79429 : Reach 79429 := rs (se 4 (by rfl) ⟨7446, by rfl⟩) (B 14893 (by norm_num) ⟨7446, by rfl⟩ (by norm_num))
theorem R374341 : Reach 374341 := rs (se 4 (by rfl) ⟨35094, by rfl⟩) (B 70189 (by norm_num) ⟨35094, by rfl⟩ (by norm_num))
theorem R79433 : Reach 79433 := rs (se 2 (by rfl) ⟨29787, by rfl⟩) (B 59575 (by norm_num) ⟨29787, by rfl⟩ (by norm_num))
theorem R79437 : Reach 79437 := rs (se 3 (by rfl) ⟨14894, by rfl⟩) (B 29789 (by norm_num) ⟨14894, by rfl⟩ (by norm_num))
theorem R79441 : Reach 79441 := rs (se 2 (by rfl) ⟨29790, by rfl⟩) (B 59581 (by norm_num) ⟨29790, by rfl⟩ (by norm_num))
theorem R79445 : Reach 79445 := rs (se 8 (by rfl) ⟨465, by rfl⟩) (B 931 (by norm_num) ⟨465, by rfl⟩ (by norm_num))
theorem R79449 : Reach 79449 := rs (se 2 (by rfl) ⟨29793, by rfl⟩) (B 59587 (by norm_num) ⟨29793, by rfl⟩ (by norm_num))
theorem R79453 : Reach 79453 := rs (se 3 (by rfl) ⟨14897, by rfl⟩) (B 29795 (by norm_num) ⟨14897, by rfl⟩ (by norm_num))
theorem R79457 : Reach 79457 := rs (se 2 (by rfl) ⟨29796, by rfl⟩) (B 59593 (by norm_num) ⟨29796, by rfl⟩ (by norm_num))
theorem R79461 : Reach 79461 := rs (se 4 (by rfl) ⟨7449, by rfl⟩) (B 14899 (by norm_num) ⟨7449, by rfl⟩ (by norm_num))
theorem R79465 : Reach 79465 := rs (se 2 (by rfl) ⟨29799, by rfl⟩) (B 59599 (by norm_num) ⟨29799, by rfl⟩ (by norm_num))
theorem R79469 : Reach 79469 := rs (se 3 (by rfl) ⟨14900, by rfl⟩) (B 29801 (by norm_num) ⟨14900, by rfl⟩ (by norm_num))
theorem R79473 : Reach 79473 := rs (se 2 (by rfl) ⟨29802, by rfl⟩) (B 59605 (by norm_num) ⟨29802, by rfl⟩ (by norm_num))
theorem R79477 : Reach 79477 := rs (se 5 (by rfl) ⟨3725, by rfl⟩) (B 7451 (by norm_num) ⟨3725, by rfl⟩ (by norm_num))
theorem R79481 : Reach 79481 := rs (se 2 (by rfl) ⟨29805, by rfl⟩) (B 59611 (by norm_num) ⟨29805, by rfl⟩ (by norm_num))
theorem R79485 : Reach 79485 := rs (se 3 (by rfl) ⟨14903, by rfl⟩) (B 29807 (by norm_num) ⟨14903, by rfl⟩ (by norm_num))
theorem R79489 : Reach 79489 := rs (se 2 (by rfl) ⟨29808, by rfl⟩) (B 59617 (by norm_num) ⟨29808, by rfl⟩ (by norm_num))
theorem R276101 : Reach 276101 := rs (se 4 (by rfl) ⟨25884, by rfl⟩) (B 51769 (by norm_num) ⟨25884, by rfl⟩ (by norm_num))
theorem R79493 : Reach 79493 := rs (se 4 (by rfl) ⟨7452, by rfl⟩) (B 14905 (by norm_num) ⟨7452, by rfl⟩ (by norm_num))
theorem R79497 : Reach 79497 := rs (se 2 (by rfl) ⟨29811, by rfl⟩) (B 59623 (by norm_num) ⟨29811, by rfl⟩ (by norm_num))
theorem R79501 : Reach 79501 := rs (se 3 (by rfl) ⟨14906, by rfl⟩) (B 29813 (by norm_num) ⟨14906, by rfl⟩ (by norm_num))
theorem R79505 : Reach 79505 := rs (se 2 (by rfl) ⟨29814, by rfl⟩) (B 59629 (by norm_num) ⟨29814, by rfl⟩ (by norm_num))
theorem R79509 : Reach 79509 := rs (se 6 (by rfl) ⟨1863, by rfl⟩) (B 3727 (by norm_num) ⟨1863, by rfl⟩ (by norm_num))
theorem R79513 : Reach 79513 := rs (se 2 (by rfl) ⟨29817, by rfl⟩) (B 59635 (by norm_num) ⟨29817, by rfl⟩ (by norm_num))
theorem R79517 : Reach 79517 := rs (se 3 (by rfl) ⟨14909, by rfl⟩) (B 29819 (by norm_num) ⟨14909, by rfl⟩ (by norm_num))
theorem R79521 : Reach 79521 := rs (se 2 (by rfl) ⟨29820, by rfl⟩) (B 59641 (by norm_num) ⟨29820, by rfl⟩ (by norm_num))
theorem R79525 : Reach 79525 := rs (se 4 (by rfl) ⟨7455, by rfl⟩) (B 14911 (by norm_num) ⟨7455, by rfl⟩ (by norm_num))
theorem R79529 : Reach 79529 := rs (se 2 (by rfl) ⟨29823, by rfl⟩) (B 59647 (by norm_num) ⟨29823, by rfl⟩ (by norm_num))
theorem R79533 : Reach 79533 := rs (se 3 (by rfl) ⟨14912, by rfl⟩) (B 29825 (by norm_num) ⟨14912, by rfl⟩ (by norm_num))
theorem R79537 : Reach 79537 := rs (se 2 (by rfl) ⟨29826, by rfl⟩) (B 59653 (by norm_num) ⟨29826, by rfl⟩ (by norm_num))
theorem R79541 : Reach 79541 := rs (se 5 (by rfl) ⟨3728, by rfl⟩) (B 7457 (by norm_num) ⟨3728, by rfl⟩ (by norm_num))
theorem R79545 : Reach 79545 := rs (se 2 (by rfl) ⟨29829, by rfl⟩) (B 59659 (by norm_num) ⟨29829, by rfl⟩ (by norm_num))
theorem R79549 : Reach 79549 := rs (se 3 (by rfl) ⟨14915, by rfl⟩) (B 29831 (by norm_num) ⟨14915, by rfl⟩ (by norm_num))
theorem R79553 : Reach 79553 := rs (se 2 (by rfl) ⟨29832, by rfl⟩) (B 59665 (by norm_num) ⟨29832, by rfl⟩ (by norm_num))
theorem R79557 : Reach 79557 := rs (se 4 (by rfl) ⟨7458, by rfl⟩) (B 14917 (by norm_num) ⟨7458, by rfl⟩ (by norm_num))
theorem R79561 : Reach 79561 := rs (se 2 (by rfl) ⟨29835, by rfl⟩) (B 59671 (by norm_num) ⟨29835, by rfl⟩ (by norm_num))
theorem R79565 : Reach 79565 := rs (se 3 (by rfl) ⟨14918, by rfl⟩) (B 29837 (by norm_num) ⟨14918, by rfl⟩ (by norm_num))
theorem R177869 : Reach 177869 := rs (se 3 (by rfl) ⟨33350, by rfl⟩) (B 66701 (by norm_num) ⟨33350, by rfl⟩ (by norm_num))
theorem R79569 : Reach 79569 := rs (se 2 (by rfl) ⟨29838, by rfl⟩) (B 59677 (by norm_num) ⟨29838, by rfl⟩ (by norm_num))
theorem R79573 : Reach 79573 := rs (se 7 (by rfl) ⟨932, by rfl⟩) (B 1865 (by norm_num) ⟨932, by rfl⟩ (by norm_num))
theorem R79577 : Reach 79577 := rs (se 2 (by rfl) ⟨29841, by rfl⟩) (B 59683 (by norm_num) ⟨29841, by rfl⟩ (by norm_num))
theorem R79581 : Reach 79581 := rs (se 3 (by rfl) ⟨14921, by rfl⟩) (B 29843 (by norm_num) ⟨14921, by rfl⟩ (by norm_num))
theorem R79585 : Reach 79585 := rs (se 2 (by rfl) ⟨29844, by rfl⟩) (B 59689 (by norm_num) ⟨29844, by rfl⟩ (by norm_num))
theorem R79589 : Reach 79589 := rs (se 4 (by rfl) ⟨7461, by rfl⟩) (B 14923 (by norm_num) ⟨7461, by rfl⟩ (by norm_num))
theorem R79593 : Reach 79593 := rs (se 2 (by rfl) ⟨29847, by rfl⟩) (B 59695 (by norm_num) ⟨29847, by rfl⟩ (by norm_num))
theorem R79597 : Reach 79597 := rs (se 3 (by rfl) ⟨14924, by rfl⟩) (B 29849 (by norm_num) ⟨14924, by rfl⟩ (by norm_num))
theorem R79601 : Reach 79601 := rs (se 2 (by rfl) ⟨29850, by rfl⟩) (B 59701 (by norm_num) ⟨29850, by rfl⟩ (by norm_num))
theorem R79605 : Reach 79605 := rs (se 5 (by rfl) ⟨3731, by rfl⟩) (B 7463 (by norm_num) ⟨3731, by rfl⟩ (by norm_num))
theorem R79609 : Reach 79609 := rs (se 2 (by rfl) ⟨29853, by rfl⟩) (B 59707 (by norm_num) ⟨29853, by rfl⟩ (by norm_num))
theorem R79613 : Reach 79613 := rs (se 3 (by rfl) ⟨14927, by rfl⟩) (B 29855 (by norm_num) ⟨14927, by rfl⟩ (by norm_num))
theorem R79617 : Reach 79617 := rs (se 2 (by rfl) ⟨29856, by rfl⟩) (B 59713 (by norm_num) ⟨29856, by rfl⟩ (by norm_num))
theorem R79621 : Reach 79621 := rs (se 4 (by rfl) ⟨7464, by rfl⟩) (B 14929 (by norm_num) ⟨7464, by rfl⟩ (by norm_num))
theorem R79625 : Reach 79625 := rs (se 2 (by rfl) ⟨29859, by rfl⟩) (B 59719 (by norm_num) ⟨29859, by rfl⟩ (by norm_num))
theorem R79629 : Reach 79629 := rs (se 3 (by rfl) ⟨14930, by rfl⟩) (B 29861 (by norm_num) ⟨14930, by rfl⟩ (by norm_num))
theorem R79633 : Reach 79633 := rs (se 2 (by rfl) ⟨29862, by rfl⟩) (B 59725 (by norm_num) ⟨29862, by rfl⟩ (by norm_num))
theorem R79637 : Reach 79637 := rs (se 6 (by rfl) ⟨1866, by rfl⟩) (B 3733 (by norm_num) ⟨1866, by rfl⟩ (by norm_num))
theorem R79641 : Reach 79641 := rs (se 2 (by rfl) ⟨29865, by rfl⟩) (B 59731 (by norm_num) ⟨29865, by rfl⟩ (by norm_num))
theorem R79645 : Reach 79645 := rs (se 3 (by rfl) ⟨14933, by rfl⟩) (B 29867 (by norm_num) ⟨14933, by rfl⟩ (by norm_num))
theorem R79649 : Reach 79649 := rs (se 2 (by rfl) ⟨29868, by rfl⟩) (B 59737 (by norm_num) ⟨29868, by rfl⟩ (by norm_num))
theorem R79653 : Reach 79653 := rs (se 4 (by rfl) ⟨7467, by rfl⟩) (B 14935 (by norm_num) ⟨7467, by rfl⟩ (by norm_num))
theorem R79657 : Reach 79657 := rs (se 2 (by rfl) ⟨29871, by rfl⟩) (B 59743 (by norm_num) ⟨29871, by rfl⟩ (by norm_num))
theorem R79661 : Reach 79661 := rs (se 3 (by rfl) ⟨14936, by rfl⟩) (B 29873 (by norm_num) ⟨14936, by rfl⟩ (by norm_num))
theorem R177965 : Reach 177965 := rs (se 3 (by rfl) ⟨33368, by rfl⟩) (B 66737 (by norm_num) ⟨33368, by rfl⟩ (by norm_num))
theorem R79665 : Reach 79665 := rs (se 2 (by rfl) ⟨29874, by rfl⟩) (B 59749 (by norm_num) ⟨29874, by rfl⟩ (by norm_num))
theorem R79669 : Reach 79669 := rs (se 5 (by rfl) ⟨3734, by rfl⟩) (B 7469 (by norm_num) ⟨3734, by rfl⟩ (by norm_num))
theorem R79673 : Reach 79673 := rs (se 2 (by rfl) ⟨29877, by rfl⟩) (B 59755 (by norm_num) ⟨29877, by rfl⟩ (by norm_num))
theorem R79677 : Reach 79677 := rs (se 3 (by rfl) ⟨14939, by rfl⟩) (B 29879 (by norm_num) ⟨14939, by rfl⟩ (by norm_num))
theorem R79681 : Reach 79681 := rs (se 2 (by rfl) ⟨29880, by rfl⟩) (B 59761 (by norm_num) ⟨29880, by rfl⟩ (by norm_num))
theorem R79685 : Reach 79685 := rs (se 4 (by rfl) ⟨7470, by rfl⟩) (B 14941 (by norm_num) ⟨7470, by rfl⟩ (by norm_num))
theorem R79689 : Reach 79689 := rs (se 2 (by rfl) ⟨29883, by rfl⟩) (B 59767 (by norm_num) ⟨29883, by rfl⟩ (by norm_num))
theorem R79693 : Reach 79693 := rs (se 3 (by rfl) ⟨14942, by rfl⟩) (B 29885 (by norm_num) ⟨14942, by rfl⟩ (by norm_num))
theorem R79697 : Reach 79697 := rs (se 2 (by rfl) ⟨29886, by rfl⟩) (B 59773 (by norm_num) ⟨29886, by rfl⟩ (by norm_num))
theorem R79701 : Reach 79701 := rs (se 9 (by rfl) ⟨233, by rfl⟩) (B 467 (by norm_num) ⟨233, by rfl⟩ (by norm_num))
theorem R79705 : Reach 79705 := rs (se 2 (by rfl) ⟨29889, by rfl⟩) (B 59779 (by norm_num) ⟨29889, by rfl⟩ (by norm_num))
theorem R79709 : Reach 79709 := rs (se 3 (by rfl) ⟨14945, by rfl⟩) (B 29891 (by norm_num) ⟨14945, by rfl⟩ (by norm_num))
theorem R79713 : Reach 79713 := rs (se 2 (by rfl) ⟨29892, by rfl⟩) (B 59785 (by norm_num) ⟨29892, by rfl⟩ (by norm_num))
theorem R79717 : Reach 79717 := rs (se 4 (by rfl) ⟨7473, by rfl⟩) (B 14947 (by norm_num) ⟨7473, by rfl⟩ (by norm_num))
theorem R79721 : Reach 79721 := rs (se 2 (by rfl) ⟨29895, by rfl⟩) (B 59791 (by norm_num) ⟨29895, by rfl⟩ (by norm_num))
theorem R79725 : Reach 79725 := rs (se 3 (by rfl) ⟨14948, by rfl⟩) (B 29897 (by norm_num) ⟨14948, by rfl⟩ (by norm_num))
theorem R79729 : Reach 79729 := rs (se 2 (by rfl) ⟨29898, by rfl⟩) (B 59797 (by norm_num) ⟨29898, by rfl⟩ (by norm_num))
theorem R178037 : Reach 178037 := rs (se 5 (by rfl) ⟨8345, by rfl⟩) (B 16691 (by norm_num) ⟨8345, by rfl⟩ (by norm_num))
theorem R79733 : Reach 79733 := rs (se 5 (by rfl) ⟨3737, by rfl⟩) (B 7475 (by norm_num) ⟨3737, by rfl⟩ (by norm_num))
theorem R79737 : Reach 79737 := rs (se 2 (by rfl) ⟨29901, by rfl⟩) (B 59803 (by norm_num) ⟨29901, by rfl⟩ (by norm_num))
theorem R79741 : Reach 79741 := rs (se 3 (by rfl) ⟨14951, by rfl⟩) (B 29903 (by norm_num) ⟨14951, by rfl⟩ (by norm_num))
theorem R79745 : Reach 79745 := rs (se 2 (by rfl) ⟨29904, by rfl⟩) (B 59809 (by norm_num) ⟨29904, by rfl⟩ (by norm_num))
theorem R407429 : Reach 407429 := rs (se 4 (by rfl) ⟨38196, by rfl⟩) (B 76393 (by norm_num) ⟨38196, by rfl⟩ (by norm_num))
theorem R79749 : Reach 79749 := rs (se 4 (by rfl) ⟨7476, by rfl⟩) (B 14953 (by norm_num) ⟨7476, by rfl⟩ (by norm_num))
theorem R79753 : Reach 79753 := rs (se 2 (by rfl) ⟨29907, by rfl⟩) (B 59815 (by norm_num) ⟨29907, by rfl⟩ (by norm_num))
theorem R79757 : Reach 79757 := rs (se 3 (by rfl) ⟨14954, by rfl⟩) (B 29909 (by norm_num) ⟨14954, by rfl⟩ (by norm_num))
theorem R79761 : Reach 79761 := rs (se 2 (by rfl) ⟨29910, by rfl⟩) (B 59821 (by norm_num) ⟨29910, by rfl⟩ (by norm_num))
theorem R79765 : Reach 79765 := rs (se 6 (by rfl) ⟨1869, by rfl⟩) (B 3739 (by norm_num) ⟨1869, by rfl⟩ (by norm_num))
theorem R79769 : Reach 79769 := rs (se 2 (by rfl) ⟨29913, by rfl⟩) (B 59827 (by norm_num) ⟨29913, by rfl⟩ (by norm_num))
theorem R79773 : Reach 79773 := rs (se 3 (by rfl) ⟨14957, by rfl⟩) (B 29915 (by norm_num) ⟨14957, by rfl⟩ (by norm_num))
theorem R79777 : Reach 79777 := rs (se 2 (by rfl) ⟨29916, by rfl⟩) (B 59833 (by norm_num) ⟨29916, by rfl⟩ (by norm_num))
theorem R79781 : Reach 79781 := rs (se 4 (by rfl) ⟨7479, by rfl⟩) (B 14959 (by norm_num) ⟨7479, by rfl⟩ (by norm_num))
theorem R79785 : Reach 79785 := rs (se 2 (by rfl) ⟨29919, by rfl⟩) (B 59839 (by norm_num) ⟨29919, by rfl⟩ (by norm_num))
theorem R79789 : Reach 79789 := rs (se 3 (by rfl) ⟨14960, by rfl⟩) (B 29921 (by norm_num) ⟨14960, by rfl⟩ (by norm_num))
theorem R79793 : Reach 79793 := rs (se 2 (by rfl) ⟨29922, by rfl⟩) (B 59845 (by norm_num) ⟨29922, by rfl⟩ (by norm_num))
theorem R79797 : Reach 79797 := rs (se 5 (by rfl) ⟨3740, by rfl⟩) (B 7481 (by norm_num) ⟨3740, by rfl⟩ (by norm_num))
theorem R79801 : Reach 79801 := rs (se 2 (by rfl) ⟨29925, by rfl⟩) (B 59851 (by norm_num) ⟨29925, by rfl⟩ (by norm_num))
theorem R178109 : Reach 178109 := rs (se 3 (by rfl) ⟨33395, by rfl⟩) (B 66791 (by norm_num) ⟨33395, by rfl⟩ (by norm_num))
theorem R79805 : Reach 79805 := rs (se 3 (by rfl) ⟨14963, by rfl⟩) (B 29927 (by norm_num) ⟨14963, by rfl⟩ (by norm_num))
theorem R79809 : Reach 79809 := rs (se 2 (by rfl) ⟨29928, by rfl⟩) (B 59857 (by norm_num) ⟨29928, by rfl⟩ (by norm_num))
theorem R79813 : Reach 79813 := rs (se 4 (by rfl) ⟨7482, by rfl⟩) (B 14965 (by norm_num) ⟨7482, by rfl⟩ (by norm_num))
theorem R79817 : Reach 79817 := rs (se 2 (by rfl) ⟨29931, by rfl⟩) (B 59863 (by norm_num) ⟨29931, by rfl⟩ (by norm_num))
theorem R79821 : Reach 79821 := rs (se 3 (by rfl) ⟨14966, by rfl⟩) (B 29933 (by norm_num) ⟨14966, by rfl⟩ (by norm_num))
theorem R79825 : Reach 79825 := rs (se 2 (by rfl) ⟨29934, by rfl⟩) (B 59869 (by norm_num) ⟨29934, by rfl⟩ (by norm_num))
theorem R79829 : Reach 79829 := rs (se 7 (by rfl) ⟨935, by rfl⟩) (B 1871 (by norm_num) ⟨935, by rfl⟩ (by norm_num))
theorem R79833 : Reach 79833 := rs (se 2 (by rfl) ⟨29937, by rfl⟩) (B 59875 (by norm_num) ⟨29937, by rfl⟩ (by norm_num))
theorem R79837 : Reach 79837 := rs (se 3 (by rfl) ⟨14969, by rfl⟩) (B 29939 (by norm_num) ⟨14969, by rfl⟩ (by norm_num))
theorem R79841 : Reach 79841 := rs (se 2 (by rfl) ⟨29940, by rfl⟩) (B 59881 (by norm_num) ⟨29940, by rfl⟩ (by norm_num))
theorem R79845 : Reach 79845 := rs (se 4 (by rfl) ⟨7485, by rfl⟩) (B 14971 (by norm_num) ⟨7485, by rfl⟩ (by norm_num))
theorem R79849 : Reach 79849 := rs (se 2 (by rfl) ⟨29943, by rfl⟩) (B 59887 (by norm_num) ⟨29943, by rfl⟩ (by norm_num))
theorem R79853 : Reach 79853 := rs (se 3 (by rfl) ⟨14972, by rfl⟩) (B 29945 (by norm_num) ⟨14972, by rfl⟩ (by norm_num))
theorem R79857 : Reach 79857 := rs (se 2 (by rfl) ⟨29946, by rfl⟩) (B 59893 (by norm_num) ⟨29946, by rfl⟩ (by norm_num))
theorem R79861 : Reach 79861 := rs (se 5 (by rfl) ⟨3743, by rfl⟩) (B 7487 (by norm_num) ⟨3743, by rfl⟩ (by norm_num))
theorem R79865 : Reach 79865 := rs (se 2 (by rfl) ⟨29949, by rfl⟩) (B 59899 (by norm_num) ⟨29949, by rfl⟩ (by norm_num))
theorem R79869 : Reach 79869 := rs (se 3 (by rfl) ⟨14975, by rfl⟩) (B 29951 (by norm_num) ⟨14975, by rfl⟩ (by norm_num))
theorem R79873 : Reach 79873 := rs (se 2 (by rfl) ⟨29952, by rfl⟩) (B 59905 (by norm_num) ⟨29952, by rfl⟩ (by norm_num))
theorem R178181 : Reach 178181 := rs (se 4 (by rfl) ⟨16704, by rfl⟩) (B 33409 (by norm_num) ⟨16704, by rfl⟩ (by norm_num))
theorem R79877 : Reach 79877 := rs (se 4 (by rfl) ⟨7488, by rfl⟩) (B 14977 (by norm_num) ⟨7488, by rfl⟩ (by norm_num))
theorem R79881 : Reach 79881 := rs (se 2 (by rfl) ⟨29955, by rfl⟩) (B 59911 (by norm_num) ⟨29955, by rfl⟩ (by norm_num))
theorem R79885 : Reach 79885 := rs (se 3 (by rfl) ⟨14978, by rfl⟩) (B 29957 (by norm_num) ⟨14978, by rfl⟩ (by norm_num))
theorem R79889 : Reach 79889 := rs (se 2 (by rfl) ⟨29958, by rfl⟩) (B 59917 (by norm_num) ⟨29958, by rfl⟩ (by norm_num))
theorem R79893 : Reach 79893 := rs (se 6 (by rfl) ⟨1872, by rfl⟩) (B 3745 (by norm_num) ⟨1872, by rfl⟩ (by norm_num))
theorem R79897 : Reach 79897 := rs (se 2 (by rfl) ⟨29961, by rfl⟩) (B 59923 (by norm_num) ⟨29961, by rfl⟩ (by norm_num))
theorem R79901 : Reach 79901 := rs (se 3 (by rfl) ⟨14981, by rfl⟩) (B 29963 (by norm_num) ⟨14981, by rfl⟩ (by norm_num))
theorem R79905 : Reach 79905 := rs (se 2 (by rfl) ⟨29964, by rfl⟩) (B 59929 (by norm_num) ⟨29964, by rfl⟩ (by norm_num))
theorem R79909 : Reach 79909 := rs (se 4 (by rfl) ⟨7491, by rfl⟩) (B 14983 (by norm_num) ⟨7491, by rfl⟩ (by norm_num))
theorem R79913 : Reach 79913 := rs (se 2 (by rfl) ⟨29967, by rfl⟩) (B 59935 (by norm_num) ⟨29967, by rfl⟩ (by norm_num))
theorem R79917 : Reach 79917 := rs (se 3 (by rfl) ⟨14984, by rfl⟩) (B 29969 (by norm_num) ⟨14984, by rfl⟩ (by norm_num))
theorem R79921 : Reach 79921 := rs (se 2 (by rfl) ⟨29970, by rfl⟩) (B 59941 (by norm_num) ⟨29970, by rfl⟩ (by norm_num))
theorem R276533 : Reach 276533 := rs (se 5 (by rfl) ⟨12962, by rfl⟩) (B 25925 (by norm_num) ⟨12962, by rfl⟩ (by norm_num))
theorem R79925 : Reach 79925 := rs (se 5 (by rfl) ⟨3746, by rfl⟩) (B 7493 (by norm_num) ⟨3746, by rfl⟩ (by norm_num))
theorem R79929 : Reach 79929 := rs (se 2 (by rfl) ⟨29973, by rfl⟩) (B 59947 (by norm_num) ⟨29973, by rfl⟩ (by norm_num))
theorem R79933 : Reach 79933 := rs (se 3 (by rfl) ⟨14987, by rfl⟩) (B 29975 (by norm_num) ⟨14987, by rfl⟩ (by norm_num))
theorem R79937 : Reach 79937 := rs (se 2 (by rfl) ⟨29976, by rfl⟩) (B 59953 (by norm_num) ⟨29976, by rfl⟩ (by norm_num))
theorem R79941 : Reach 79941 := rs (se 4 (by rfl) ⟨7494, by rfl⟩) (B 14989 (by norm_num) ⟨7494, by rfl⟩ (by norm_num))
theorem R79945 : Reach 79945 := rs (se 2 (by rfl) ⟨29979, by rfl⟩) (B 59959 (by norm_num) ⟨29979, by rfl⟩ (by norm_num))
theorem R178253 : Reach 178253 := rs (se 3 (by rfl) ⟨33422, by rfl⟩) (B 66845 (by norm_num) ⟨33422, by rfl⟩ (by norm_num))
theorem R79949 : Reach 79949 := rs (se 3 (by rfl) ⟨14990, by rfl⟩) (B 29981 (by norm_num) ⟨14990, by rfl⟩ (by norm_num))
theorem R79953 : Reach 79953 := rs (se 2 (by rfl) ⟨29982, by rfl⟩) (B 59965 (by norm_num) ⟨29982, by rfl⟩ (by norm_num))
theorem R79957 : Reach 79957 := rs (se 8 (by rfl) ⟨468, by rfl⟩) (B 937 (by norm_num) ⟨468, by rfl⟩ (by norm_num))
theorem R79961 : Reach 79961 := rs (se 2 (by rfl) ⟨29985, by rfl⟩) (B 59971 (by norm_num) ⟨29985, by rfl⟩ (by norm_num))
theorem R79965 : Reach 79965 := rs (se 3 (by rfl) ⟨14993, by rfl⟩) (B 29987 (by norm_num) ⟨14993, by rfl⟩ (by norm_num))
theorem R79969 : Reach 79969 := rs (se 2 (by rfl) ⟨29988, by rfl⟩) (B 59977 (by norm_num) ⟨29988, by rfl⟩ (by norm_num))
theorem R79973 : Reach 79973 := rs (se 4 (by rfl) ⟨7497, by rfl⟩) (B 14995 (by norm_num) ⟨7497, by rfl⟩ (by norm_num))
theorem R79977 : Reach 79977 := rs (se 2 (by rfl) ⟨29991, by rfl⟩) (B 59983 (by norm_num) ⟨29991, by rfl⟩ (by norm_num))
theorem R79981 : Reach 79981 := rs (se 3 (by rfl) ⟨14996, by rfl⟩) (B 29993 (by norm_num) ⟨14996, by rfl⟩ (by norm_num))
theorem R79985 : Reach 79985 := rs (se 2 (by rfl) ⟨29994, by rfl⟩) (B 59989 (by norm_num) ⟨29994, by rfl⟩ (by norm_num))
theorem R79989 : Reach 79989 := rs (se 5 (by rfl) ⟨3749, by rfl⟩) (B 7499 (by norm_num) ⟨3749, by rfl⟩ (by norm_num))
theorem R79993 : Reach 79993 := rs (se 2 (by rfl) ⟨29997, by rfl⟩) (B 59995 (by norm_num) ⟨29997, by rfl⟩ (by norm_num))
theorem R79997 : Reach 79997 := rs (se 3 (by rfl) ⟨14999, by rfl⟩) (B 29999 (by norm_num) ⟨14999, by rfl⟩ (by norm_num))
theorem R80001 : Reach 80001 := rs (se 2 (by rfl) ⟨30000, by rfl⟩) (B 60001 (by norm_num) ⟨30000, by rfl⟩ (by norm_num))
theorem R80005 : Reach 80005 := rs (se 4 (by rfl) ⟨7500, by rfl⟩) (B 15001 (by norm_num) ⟨7500, by rfl⟩ (by norm_num))
theorem R80009 : Reach 80009 := rs (se 2 (by rfl) ⟨30003, by rfl⟩) (B 60007 (by norm_num) ⟨30003, by rfl⟩ (by norm_num))
theorem R80013 : Reach 80013 := rs (se 3 (by rfl) ⟨15002, by rfl⟩) (B 30005 (by norm_num) ⟨15002, by rfl⟩ (by norm_num))
theorem R80017 : Reach 80017 := rs (se 2 (by rfl) ⟨30006, by rfl⟩) (B 60013 (by norm_num) ⟨30006, by rfl⟩ (by norm_num))
theorem R178325 : Reach 178325 := rs (se 6 (by rfl) ⟨4179, by rfl⟩) (B 8359 (by norm_num) ⟨4179, by rfl⟩ (by norm_num))
theorem R80021 : Reach 80021 := rs (se 6 (by rfl) ⟨1875, by rfl⟩) (B 3751 (by norm_num) ⟨1875, by rfl⟩ (by norm_num))
theorem R80025 : Reach 80025 := rs (se 2 (by rfl) ⟨30009, by rfl⟩) (B 60019 (by norm_num) ⟨30009, by rfl⟩ (by norm_num))
theorem R80029 : Reach 80029 := rs (se 3 (by rfl) ⟨15005, by rfl⟩) (B 30011 (by norm_num) ⟨15005, by rfl⟩ (by norm_num))
theorem R80033 : Reach 80033 := rs (se 2 (by rfl) ⟨30012, by rfl⟩) (B 60025 (by norm_num) ⟨30012, by rfl⟩ (by norm_num))
theorem R80037 : Reach 80037 := rs (se 4 (by rfl) ⟨7503, by rfl⟩) (B 15007 (by norm_num) ⟨7503, by rfl⟩ (by norm_num))
theorem R80041 : Reach 80041 := rs (se 2 (by rfl) ⟨30015, by rfl⟩) (B 60031 (by norm_num) ⟨30015, by rfl⟩ (by norm_num))
theorem R80045 : Reach 80045 := rs (se 3 (by rfl) ⟨15008, by rfl⟩) (B 30017 (by norm_num) ⟨15008, by rfl⟩ (by norm_num))
theorem R80049 : Reach 80049 := rs (se 2 (by rfl) ⟨30018, by rfl⟩) (B 60037 (by norm_num) ⟨30018, by rfl⟩ (by norm_num))
theorem R80053 : Reach 80053 := rs (se 5 (by rfl) ⟨3752, by rfl⟩) (B 7505 (by norm_num) ⟨3752, by rfl⟩ (by norm_num))
theorem R80057 : Reach 80057 := rs (se 2 (by rfl) ⟨30021, by rfl⟩) (B 60043 (by norm_num) ⟨30021, by rfl⟩ (by norm_num))
theorem R80061 : Reach 80061 := rs (se 3 (by rfl) ⟨15011, by rfl⟩) (B 30023 (by norm_num) ⟨15011, by rfl⟩ (by norm_num))
theorem R80065 : Reach 80065 := rs (se 2 (by rfl) ⟨30024, by rfl⟩) (B 60049 (by norm_num) ⟨30024, by rfl⟩ (by norm_num))
theorem R80069 : Reach 80069 := rs (se 4 (by rfl) ⟨7506, by rfl⟩) (B 15013 (by norm_num) ⟨7506, by rfl⟩ (by norm_num))
theorem R80073 : Reach 80073 := rs (se 2 (by rfl) ⟨30027, by rfl⟩) (B 60055 (by norm_num) ⟨30027, by rfl⟩ (by norm_num))
theorem R80077 : Reach 80077 := rs (se 3 (by rfl) ⟨15014, by rfl⟩) (B 30029 (by norm_num) ⟨15014, by rfl⟩ (by norm_num))
theorem R80081 : Reach 80081 := rs (se 2 (by rfl) ⟨30030, by rfl⟩) (B 60061 (by norm_num) ⟨30030, by rfl⟩ (by norm_num))
theorem R112853 : Reach 112853 := rs (se 7 (by rfl) ⟨1322, by rfl⟩) (B 2645 (by norm_num) ⟨1322, by rfl⟩ (by norm_num))
theorem R80085 : Reach 80085 := rs (se 7 (by rfl) ⟨938, by rfl⟩) (B 1877 (by norm_num) ⟨938, by rfl⟩ (by norm_num))
theorem R80089 : Reach 80089 := rs (se 2 (by rfl) ⟨30033, by rfl⟩) (B 60067 (by norm_num) ⟨30033, by rfl⟩ (by norm_num))
theorem R178397 : Reach 178397 := rs (se 3 (by rfl) ⟨33449, by rfl⟩) (B 66899 (by norm_num) ⟨33449, by rfl⟩ (by norm_num))
theorem R80093 : Reach 80093 := rs (se 3 (by rfl) ⟨15017, by rfl⟩) (B 30035 (by norm_num) ⟨15017, by rfl⟩ (by norm_num))
theorem R80097 : Reach 80097 := rs (se 2 (by rfl) ⟨30036, by rfl⟩) (B 60073 (by norm_num) ⟨30036, by rfl⟩ (by norm_num))
theorem R80101 : Reach 80101 := rs (se 4 (by rfl) ⟨7509, by rfl⟩) (B 15019 (by norm_num) ⟨7509, by rfl⟩ (by norm_num))
theorem R80105 : Reach 80105 := rs (se 2 (by rfl) ⟨30039, by rfl⟩) (B 60079 (by norm_num) ⟨30039, by rfl⟩ (by norm_num))
theorem R80109 : Reach 80109 := rs (se 3 (by rfl) ⟨15020, by rfl⟩) (B 30041 (by norm_num) ⟨15020, by rfl⟩ (by norm_num))
theorem R80113 : Reach 80113 := rs (se 2 (by rfl) ⟨30042, by rfl⟩) (B 60085 (by norm_num) ⟨30042, by rfl⟩ (by norm_num))
theorem R80117 : Reach 80117 := rs (se 5 (by rfl) ⟨3755, by rfl⟩) (B 7511 (by norm_num) ⟨3755, by rfl⟩ (by norm_num))
theorem R80121 : Reach 80121 := rs (se 2 (by rfl) ⟨30045, by rfl⟩) (B 60091 (by norm_num) ⟨30045, by rfl⟩ (by norm_num))
theorem R80125 : Reach 80125 := rs (se 3 (by rfl) ⟨15023, by rfl⟩) (B 30047 (by norm_num) ⟨15023, by rfl⟩ (by norm_num))
theorem R80129 : Reach 80129 := rs (se 2 (by rfl) ⟨30048, by rfl⟩) (B 60097 (by norm_num) ⟨30048, by rfl⟩ (by norm_num))
theorem R80133 : Reach 80133 := rs (se 4 (by rfl) ⟨7512, by rfl⟩) (B 15025 (by norm_num) ⟨7512, by rfl⟩ (by norm_num))
theorem R80137 : Reach 80137 := rs (se 2 (by rfl) ⟨30051, by rfl⟩) (B 60103 (by norm_num) ⟨30051, by rfl⟩ (by norm_num))
theorem R80141 : Reach 80141 := rs (se 3 (by rfl) ⟨15026, by rfl⟩) (B 30053 (by norm_num) ⟨15026, by rfl⟩ (by norm_num))
theorem R112909 : Reach 112909 := rs (se 3 (by rfl) ⟨21170, by rfl⟩) (B 42341 (by norm_num) ⟨21170, by rfl⟩ (by norm_num))
theorem R80145 : Reach 80145 := rs (se 2 (by rfl) ⟨30054, by rfl⟩) (B 60109 (by norm_num) ⟨30054, by rfl⟩ (by norm_num))
theorem R80149 : Reach 80149 := rs (se 6 (by rfl) ⟨1878, by rfl⟩) (B 3757 (by norm_num) ⟨1878, by rfl⟩ (by norm_num))
theorem R80153 : Reach 80153 := rs (se 2 (by rfl) ⟨30057, by rfl⟩) (B 60115 (by norm_num) ⟨30057, by rfl⟩ (by norm_num))
theorem R80157 : Reach 80157 := rs (se 3 (by rfl) ⟨15029, by rfl⟩) (B 30059 (by norm_num) ⟨15029, by rfl⟩ (by norm_num))
theorem R80161 : Reach 80161 := rs (se 2 (by rfl) ⟨30060, by rfl⟩) (B 60121 (by norm_num) ⟨30060, by rfl⟩ (by norm_num))
theorem R178469 : Reach 178469 := rs (se 4 (by rfl) ⟨16731, by rfl⟩) (B 33463 (by norm_num) ⟨16731, by rfl⟩ (by norm_num))
theorem R80165 : Reach 80165 := rs (se 4 (by rfl) ⟨7515, by rfl⟩) (B 15031 (by norm_num) ⟨7515, by rfl⟩ (by norm_num))
theorem R80169 : Reach 80169 := rs (se 2 (by rfl) ⟨30063, by rfl⟩) (B 60127 (by norm_num) ⟨30063, by rfl⟩ (by norm_num))
theorem R80173 : Reach 80173 := rs (se 3 (by rfl) ⟨15032, by rfl⟩) (B 30065 (by norm_num) ⟨15032, by rfl⟩ (by norm_num))
theorem R80177 : Reach 80177 := rs (se 2 (by rfl) ⟨30066, by rfl⟩) (B 60133 (by norm_num) ⟨30066, by rfl⟩ (by norm_num))
theorem R80181 : Reach 80181 := rs (se 5 (by rfl) ⟨3758, by rfl⟩) (B 7517 (by norm_num) ⟨3758, by rfl⟩ (by norm_num))
theorem R80185 : Reach 80185 := rs (se 2 (by rfl) ⟨30069, by rfl⟩) (B 60139 (by norm_num) ⟨30069, by rfl⟩ (by norm_num))
theorem R80189 : Reach 80189 := rs (se 3 (by rfl) ⟨15035, by rfl⟩) (B 30071 (by norm_num) ⟨15035, by rfl⟩ (by norm_num))
theorem R80193 : Reach 80193 := rs (se 2 (by rfl) ⟨30072, by rfl⟩) (B 60145 (by norm_num) ⟨30072, by rfl⟩ (by norm_num))
theorem R80197 : Reach 80197 := rs (se 4 (by rfl) ⟨7518, by rfl⟩) (B 15037 (by norm_num) ⟨7518, by rfl⟩ (by norm_num))
theorem R80201 : Reach 80201 := rs (se 2 (by rfl) ⟨30075, by rfl⟩) (B 60151 (by norm_num) ⟨30075, by rfl⟩ (by norm_num))
theorem R80205 : Reach 80205 := rs (se 3 (by rfl) ⟨15038, by rfl⟩) (B 30077 (by norm_num) ⟨15038, by rfl⟩ (by norm_num))
theorem R80209 : Reach 80209 := rs (se 2 (by rfl) ⟨30078, by rfl⟩) (B 60157 (by norm_num) ⟨30078, by rfl⟩ (by norm_num))
theorem R80213 : Reach 80213 := rs (se 10 (by rfl) ⟨117, by rfl⟩) (B 235 (by norm_num) ⟨117, by rfl⟩ (by norm_num))
theorem R80217 : Reach 80217 := rs (se 2 (by rfl) ⟨30081, by rfl⟩) (B 60163 (by norm_num) ⟨30081, by rfl⟩ (by norm_num))
theorem R80221 : Reach 80221 := rs (se 3 (by rfl) ⟨15041, by rfl⟩) (B 30083 (by norm_num) ⟨15041, by rfl⟩ (by norm_num))
theorem R80225 : Reach 80225 := rs (se 2 (by rfl) ⟨30084, by rfl⟩) (B 60169 (by norm_num) ⟨30084, by rfl⟩ (by norm_num))
theorem R80229 : Reach 80229 := rs (se 4 (by rfl) ⟨7521, by rfl⟩) (B 15043 (by norm_num) ⟨7521, by rfl⟩ (by norm_num))
theorem R80233 : Reach 80233 := rs (se 2 (by rfl) ⟨30087, by rfl⟩) (B 60175 (by norm_num) ⟨30087, by rfl⟩ (by norm_num))
theorem R178541 : Reach 178541 := rs (se 3 (by rfl) ⟨33476, by rfl⟩) (B 66953 (by norm_num) ⟨33476, by rfl⟩ (by norm_num))
theorem R80237 : Reach 80237 := rs (se 3 (by rfl) ⟨15044, by rfl⟩) (B 30089 (by norm_num) ⟨15044, by rfl⟩ (by norm_num))
theorem R80241 : Reach 80241 := rs (se 2 (by rfl) ⟨30090, by rfl⟩) (B 60181 (by norm_num) ⟨30090, by rfl⟩ (by norm_num))
theorem R80245 : Reach 80245 := rs (se 5 (by rfl) ⟨3761, by rfl⟩) (B 7523 (by norm_num) ⟨3761, by rfl⟩ (by norm_num))
theorem R80249 : Reach 80249 := rs (se 2 (by rfl) ⟨30093, by rfl⟩) (B 60187 (by norm_num) ⟨30093, by rfl⟩ (by norm_num))
theorem R80253 : Reach 80253 := rs (se 3 (by rfl) ⟨15047, by rfl⟩) (B 30095 (by norm_num) ⟨15047, by rfl⟩ (by norm_num))
theorem R80257 : Reach 80257 := rs (se 2 (by rfl) ⟨30096, by rfl⟩) (B 60193 (by norm_num) ⟨30096, by rfl⟩ (by norm_num))
theorem R80261 : Reach 80261 := rs (se 4 (by rfl) ⟨7524, by rfl⟩) (B 15049 (by norm_num) ⟨7524, by rfl⟩ (by norm_num))
theorem R80265 : Reach 80265 := rs (se 2 (by rfl) ⟨30099, by rfl⟩) (B 60199 (by norm_num) ⟨30099, by rfl⟩ (by norm_num))
theorem R80269 : Reach 80269 := rs (se 3 (by rfl) ⟨15050, by rfl⟩) (B 30101 (by norm_num) ⟨15050, by rfl⟩ (by norm_num))
theorem R80273 : Reach 80273 := rs (se 2 (by rfl) ⟨30102, by rfl⟩) (B 60205 (by norm_num) ⟨30102, by rfl⟩ (by norm_num))
theorem R80277 : Reach 80277 := rs (se 6 (by rfl) ⟨1881, by rfl⟩) (B 3763 (by norm_num) ⟨1881, by rfl⟩ (by norm_num))
theorem R80281 : Reach 80281 := rs (se 2 (by rfl) ⟨30105, by rfl⟩) (B 60211 (by norm_num) ⟨30105, by rfl⟩ (by norm_num))
theorem R80285 : Reach 80285 := rs (se 3 (by rfl) ⟨15053, by rfl⟩) (B 30107 (by norm_num) ⟨15053, by rfl⟩ (by norm_num))
theorem R80289 : Reach 80289 := rs (se 2 (by rfl) ⟨30108, by rfl⟩) (B 60217 (by norm_num) ⟨30108, by rfl⟩ (by norm_num))
theorem R145829 : Reach 145829 := rs (se 4 (by rfl) ⟨13671, by rfl⟩) (B 27343 (by norm_num) ⟨13671, by rfl⟩ (by norm_num))
theorem R80293 : Reach 80293 := rs (se 4 (by rfl) ⟨7527, by rfl⟩) (B 15055 (by norm_num) ⟨7527, by rfl⟩ (by norm_num))
theorem R80297 : Reach 80297 := rs (se 2 (by rfl) ⟨30111, by rfl⟩) (B 60223 (by norm_num) ⟨30111, by rfl⟩ (by norm_num))
theorem R80301 : Reach 80301 := rs (se 3 (by rfl) ⟨15056, by rfl⟩) (B 30113 (by norm_num) ⟨15056, by rfl⟩ (by norm_num))
theorem R80305 : Reach 80305 := rs (se 2 (by rfl) ⟨30114, by rfl⟩) (B 60229 (by norm_num) ⟨30114, by rfl⟩ (by norm_num))
theorem R178613 : Reach 178613 := rs (se 5 (by rfl) ⟨8372, by rfl⟩) (B 16745 (by norm_num) ⟨8372, by rfl⟩ (by norm_num))
theorem R80309 : Reach 80309 := rs (se 5 (by rfl) ⟨3764, by rfl⟩) (B 7529 (by norm_num) ⟨3764, by rfl⟩ (by norm_num))
theorem R80313 : Reach 80313 := rs (se 2 (by rfl) ⟨30117, by rfl⟩) (B 60235 (by norm_num) ⟨30117, by rfl⟩ (by norm_num))
theorem R80317 : Reach 80317 := rs (se 3 (by rfl) ⟨15059, by rfl⟩) (B 30119 (by norm_num) ⟨15059, by rfl⟩ (by norm_num))
theorem R80321 : Reach 80321 := rs (se 2 (by rfl) ⟨30120, by rfl⟩) (B 60241 (by norm_num) ⟨30120, by rfl⟩ (by norm_num))
theorem R80325 : Reach 80325 := rs (se 4 (by rfl) ⟨7530, by rfl⟩) (B 15061 (by norm_num) ⟨7530, by rfl⟩ (by norm_num))
theorem R80329 : Reach 80329 := rs (se 2 (by rfl) ⟨30123, by rfl⟩) (B 60247 (by norm_num) ⟨30123, by rfl⟩ (by norm_num))
theorem R80333 : Reach 80333 := rs (se 3 (by rfl) ⟨15062, by rfl⟩) (B 30125 (by norm_num) ⟨15062, by rfl⟩ (by norm_num))
theorem R80337 : Reach 80337 := rs (se 2 (by rfl) ⟨30126, by rfl⟩) (B 60253 (by norm_num) ⟨30126, by rfl⟩ (by norm_num))
theorem R80341 : Reach 80341 := rs (se 7 (by rfl) ⟨941, by rfl⟩) (B 1883 (by norm_num) ⟨941, by rfl⟩ (by norm_num))
theorem R80345 : Reach 80345 := rs (se 2 (by rfl) ⟨30129, by rfl⟩) (B 60259 (by norm_num) ⟨30129, by rfl⟩ (by norm_num))
theorem R80349 : Reach 80349 := rs (se 3 (by rfl) ⟨15065, by rfl⟩) (B 30131 (by norm_num) ⟨15065, by rfl⟩ (by norm_num))
theorem R80353 : Reach 80353 := rs (se 2 (by rfl) ⟨30132, by rfl⟩) (B 60265 (by norm_num) ⟨30132, by rfl⟩ (by norm_num))
theorem R80357 : Reach 80357 := rs (se 4 (by rfl) ⟨7533, by rfl⟩) (B 15067 (by norm_num) ⟨7533, by rfl⟩ (by norm_num))
theorem R276965 : Reach 276965 := rs (se 4 (by rfl) ⟨25965, by rfl⟩) (B 51931 (by norm_num) ⟨25965, by rfl⟩ (by norm_num))
theorem R80361 : Reach 80361 := rs (se 2 (by rfl) ⟨30135, by rfl⟩) (B 60271 (by norm_num) ⟨30135, by rfl⟩ (by norm_num))
theorem R80365 : Reach 80365 := rs (se 3 (by rfl) ⟨15068, by rfl⟩) (B 30137 (by norm_num) ⟨15068, by rfl⟩ (by norm_num))
theorem R80369 : Reach 80369 := rs (se 2 (by rfl) ⟨30138, by rfl⟩) (B 60277 (by norm_num) ⟨30138, by rfl⟩ (by norm_num))
theorem R80373 : Reach 80373 := rs (se 5 (by rfl) ⟨3767, by rfl⟩) (B 7535 (by norm_num) ⟨3767, by rfl⟩ (by norm_num))
theorem R80377 : Reach 80377 := rs (se 2 (by rfl) ⟨30141, by rfl⟩) (B 60283 (by norm_num) ⟨30141, by rfl⟩ (by norm_num))
theorem R178685 : Reach 178685 := rs (se 3 (by rfl) ⟨33503, by rfl⟩) (B 67007 (by norm_num) ⟨33503, by rfl⟩ (by norm_num))
theorem R80381 : Reach 80381 := rs (se 3 (by rfl) ⟨15071, by rfl⟩) (B 30143 (by norm_num) ⟨15071, by rfl⟩ (by norm_num))
theorem R80385 : Reach 80385 := rs (se 2 (by rfl) ⟨30144, by rfl⟩) (B 60289 (by norm_num) ⟨30144, by rfl⟩ (by norm_num))
theorem R80389 : Reach 80389 := rs (se 4 (by rfl) ⟨7536, by rfl⟩) (B 15073 (by norm_num) ⟨7536, by rfl⟩ (by norm_num))
theorem R80393 : Reach 80393 := rs (se 2 (by rfl) ⟨30147, by rfl⟩) (B 60295 (by norm_num) ⟨30147, by rfl⟩ (by norm_num))
theorem R80397 : Reach 80397 := rs (se 3 (by rfl) ⟨15074, by rfl⟩) (B 30149 (by norm_num) ⟨15074, by rfl⟩ (by norm_num))
theorem R80401 : Reach 80401 := rs (se 2 (by rfl) ⟨30150, by rfl⟩) (B 60301 (by norm_num) ⟨30150, by rfl⟩ (by norm_num))
theorem R80405 : Reach 80405 := rs (se 6 (by rfl) ⟨1884, by rfl⟩) (B 3769 (by norm_num) ⟨1884, by rfl⟩ (by norm_num))
theorem R80409 : Reach 80409 := rs (se 2 (by rfl) ⟨30153, by rfl⟩) (B 60307 (by norm_num) ⟨30153, by rfl⟩ (by norm_num))
theorem R80413 : Reach 80413 := rs (se 3 (by rfl) ⟨15077, by rfl⟩) (B 30155 (by norm_num) ⟨15077, by rfl⟩ (by norm_num))
theorem R80417 : Reach 80417 := rs (se 2 (by rfl) ⟨30156, by rfl⟩) (B 60313 (by norm_num) ⟨30156, by rfl⟩ (by norm_num))
theorem R80421 : Reach 80421 := rs (se 4 (by rfl) ⟨7539, by rfl⟩) (B 15079 (by norm_num) ⟨7539, by rfl⟩ (by norm_num))
theorem R80425 : Reach 80425 := rs (se 2 (by rfl) ⟨30159, by rfl⟩) (B 60319 (by norm_num) ⟨30159, by rfl⟩ (by norm_num))
theorem R80429 : Reach 80429 := rs (se 3 (by rfl) ⟨15080, by rfl⟩) (B 30161 (by norm_num) ⟨15080, by rfl⟩ (by norm_num))
theorem R80433 : Reach 80433 := rs (se 2 (by rfl) ⟨30162, by rfl⟩) (B 60325 (by norm_num) ⟨30162, by rfl⟩ (by norm_num))
theorem R80437 : Reach 80437 := rs (se 5 (by rfl) ⟨3770, by rfl⟩) (B 7541 (by norm_num) ⟨3770, by rfl⟩ (by norm_num))
theorem R80441 : Reach 80441 := rs (se 2 (by rfl) ⟨30165, by rfl⟩) (B 60331 (by norm_num) ⟨30165, by rfl⟩ (by norm_num))
theorem R80445 : Reach 80445 := rs (se 3 (by rfl) ⟨15083, by rfl⟩) (B 30167 (by norm_num) ⟨15083, by rfl⟩ (by norm_num))
theorem R80449 : Reach 80449 := rs (se 2 (by rfl) ⟨30168, by rfl⟩) (B 60337 (by norm_num) ⟨30168, by rfl⟩ (by norm_num))
theorem R178757 : Reach 178757 := rs (se 4 (by rfl) ⟨16758, by rfl⟩) (B 33517 (by norm_num) ⟨16758, by rfl⟩ (by norm_num))
theorem R80453 : Reach 80453 := rs (se 4 (by rfl) ⟨7542, by rfl⟩) (B 15085 (by norm_num) ⟨7542, by rfl⟩ (by norm_num))
theorem R80457 : Reach 80457 := rs (se 2 (by rfl) ⟨30171, by rfl⟩) (B 60343 (by norm_num) ⟨30171, by rfl⟩ (by norm_num))
theorem R80461 : Reach 80461 := rs (se 3 (by rfl) ⟨15086, by rfl⟩) (B 30173 (by norm_num) ⟨15086, by rfl⟩ (by norm_num))
theorem R80465 : Reach 80465 := rs (se 2 (by rfl) ⟨30174, by rfl⟩) (B 60349 (by norm_num) ⟨30174, by rfl⟩ (by norm_num))
theorem R80469 : Reach 80469 := rs (se 8 (by rfl) ⟨471, by rfl⟩) (B 943 (by norm_num) ⟨471, by rfl⟩ (by norm_num))
theorem R80473 : Reach 80473 := rs (se 2 (by rfl) ⟨30177, by rfl⟩) (B 60355 (by norm_num) ⟨30177, by rfl⟩ (by norm_num))
theorem R80477 : Reach 80477 := rs (se 3 (by rfl) ⟨15089, by rfl⟩) (B 30179 (by norm_num) ⟨15089, by rfl⟩ (by norm_num))
theorem R80481 : Reach 80481 := rs (se 2 (by rfl) ⟨30180, by rfl⟩) (B 60361 (by norm_num) ⟨30180, by rfl⟩ (by norm_num))
theorem R80485 : Reach 80485 := rs (se 4 (by rfl) ⟨7545, by rfl⟩) (B 15091 (by norm_num) ⟨7545, by rfl⟩ (by norm_num))
theorem R80489 : Reach 80489 := rs (se 2 (by rfl) ⟨30183, by rfl⟩) (B 60367 (by norm_num) ⟨30183, by rfl⟩ (by norm_num))
theorem R80493 : Reach 80493 := rs (se 3 (by rfl) ⟨15092, by rfl⟩) (B 30185 (by norm_num) ⟨15092, by rfl⟩ (by norm_num))
theorem R80497 : Reach 80497 := rs (se 2 (by rfl) ⟨30186, by rfl⟩) (B 60373 (by norm_num) ⟨30186, by rfl⟩ (by norm_num))
theorem R80501 : Reach 80501 := rs (se 5 (by rfl) ⟨3773, by rfl⟩) (B 7547 (by norm_num) ⟨3773, by rfl⟩ (by norm_num))
theorem R80505 : Reach 80505 := rs (se 2 (by rfl) ⟨30189, by rfl⟩) (B 60379 (by norm_num) ⟨30189, by rfl⟩ (by norm_num))
theorem R80509 : Reach 80509 := rs (se 3 (by rfl) ⟨15095, by rfl⟩) (B 30191 (by norm_num) ⟨15095, by rfl⟩ (by norm_num))
theorem R80513 : Reach 80513 := rs (se 2 (by rfl) ⟨30192, by rfl⟩) (B 60385 (by norm_num) ⟨30192, by rfl⟩ (by norm_num))
theorem R80517 : Reach 80517 := rs (se 4 (by rfl) ⟨7548, by rfl⟩) (B 15097 (by norm_num) ⟨7548, by rfl⟩ (by norm_num))
theorem R80521 : Reach 80521 := rs (se 2 (by rfl) ⟨30195, by rfl⟩) (B 60391 (by norm_num) ⟨30195, by rfl⟩ (by norm_num))
theorem R178829 : Reach 178829 := rs (se 3 (by rfl) ⟨33530, by rfl⟩) (B 67061 (by norm_num) ⟨33530, by rfl⟩ (by norm_num))
theorem R80525 : Reach 80525 := rs (se 3 (by rfl) ⟨15098, by rfl⟩) (B 30197 (by norm_num) ⟨15098, by rfl⟩ (by norm_num))
theorem R80529 : Reach 80529 := rs (se 2 (by rfl) ⟨30198, by rfl⟩) (B 60397 (by norm_num) ⟨30198, by rfl⟩ (by norm_num))
theorem R80533 : Reach 80533 := rs (se 6 (by rfl) ⟨1887, by rfl⟩) (B 3775 (by norm_num) ⟨1887, by rfl⟩ (by norm_num))
theorem R80537 : Reach 80537 := rs (se 2 (by rfl) ⟨30201, by rfl⟩) (B 60403 (by norm_num) ⟨30201, by rfl⟩ (by norm_num))
theorem R80541 : Reach 80541 := rs (se 3 (by rfl) ⟨15101, by rfl⟩) (B 30203 (by norm_num) ⟨15101, by rfl⟩ (by norm_num))
theorem R80545 : Reach 80545 := rs (se 2 (by rfl) ⟨30204, by rfl⟩) (B 60409 (by norm_num) ⟨30204, by rfl⟩ (by norm_num))
theorem R80549 : Reach 80549 := rs (se 4 (by rfl) ⟨7551, by rfl⟩) (B 15103 (by norm_num) ⟨7551, by rfl⟩ (by norm_num))
theorem R80553 : Reach 80553 := rs (se 2 (by rfl) ⟨30207, by rfl⟩) (B 60415 (by norm_num) ⟨30207, by rfl⟩ (by norm_num))
theorem R80557 : Reach 80557 := rs (se 3 (by rfl) ⟨15104, by rfl⟩) (B 30209 (by norm_num) ⟨15104, by rfl⟩ (by norm_num))
theorem R80561 : Reach 80561 := rs (se 2 (by rfl) ⟨30210, by rfl⟩) (B 60421 (by norm_num) ⟨30210, by rfl⟩ (by norm_num))
theorem R80565 : Reach 80565 := rs (se 5 (by rfl) ⟨3776, by rfl⟩) (B 7553 (by norm_num) ⟨3776, by rfl⟩ (by norm_num))
theorem R80569 : Reach 80569 := rs (se 2 (by rfl) ⟨30213, by rfl⟩) (B 60427 (by norm_num) ⟨30213, by rfl⟩ (by norm_num))
theorem R80573 : Reach 80573 := rs (se 3 (by rfl) ⟨15107, by rfl⟩) (B 30215 (by norm_num) ⟨15107, by rfl⟩ (by norm_num))
theorem R80577 : Reach 80577 := rs (se 2 (by rfl) ⟨30216, by rfl⟩) (B 60433 (by norm_num) ⟨30216, by rfl⟩ (by norm_num))
theorem R80581 : Reach 80581 := rs (se 4 (by rfl) ⟨7554, by rfl⟩) (B 15109 (by norm_num) ⟨7554, by rfl⟩ (by norm_num))
theorem R80585 : Reach 80585 := rs (se 2 (by rfl) ⟨30219, by rfl⟩) (B 60439 (by norm_num) ⟨30219, by rfl⟩ (by norm_num))
theorem R80589 : Reach 80589 := rs (se 3 (by rfl) ⟨15110, by rfl⟩) (B 30221 (by norm_num) ⟨15110, by rfl⟩ (by norm_num))
theorem R80593 : Reach 80593 := rs (se 2 (by rfl) ⟨30222, by rfl⟩) (B 60445 (by norm_num) ⟨30222, by rfl⟩ (by norm_num))
theorem R178901 : Reach 178901 := rs (se 7 (by rfl) ⟨2096, by rfl⟩) (B 4193 (by norm_num) ⟨2096, by rfl⟩ (by norm_num))
theorem R80597 : Reach 80597 := rs (se 7 (by rfl) ⟨944, by rfl⟩) (B 1889 (by norm_num) ⟨944, by rfl⟩ (by norm_num))
theorem R80601 : Reach 80601 := rs (se 2 (by rfl) ⟨30225, by rfl⟩) (B 60451 (by norm_num) ⟨30225, by rfl⟩ (by norm_num))
theorem R80605 : Reach 80605 := rs (se 3 (by rfl) ⟨15113, by rfl⟩) (B 30227 (by norm_num) ⟨15113, by rfl⟩ (by norm_num))
theorem R80609 : Reach 80609 := rs (se 2 (by rfl) ⟨30228, by rfl⟩) (B 60457 (by norm_num) ⟨30228, by rfl⟩ (by norm_num))
theorem R80613 : Reach 80613 := rs (se 4 (by rfl) ⟨7557, by rfl⟩) (B 15115 (by norm_num) ⟨7557, by rfl⟩ (by norm_num))
theorem R80617 : Reach 80617 := rs (se 2 (by rfl) ⟨30231, by rfl⟩) (B 60463 (by norm_num) ⟨30231, by rfl⟩ (by norm_num))
theorem R80621 : Reach 80621 := rs (se 3 (by rfl) ⟨15116, by rfl⟩) (B 30233 (by norm_num) ⟨15116, by rfl⟩ (by norm_num))
theorem R80625 : Reach 80625 := rs (se 2 (by rfl) ⟨30234, by rfl⟩) (B 60469 (by norm_num) ⟨30234, by rfl⟩ (by norm_num))
theorem R80629 : Reach 80629 := rs (se 5 (by rfl) ⟨3779, by rfl⟩) (B 7559 (by norm_num) ⟨3779, by rfl⟩ (by norm_num))
theorem R80633 : Reach 80633 := rs (se 2 (by rfl) ⟨30237, by rfl⟩) (B 60475 (by norm_num) ⟨30237, by rfl⟩ (by norm_num))
theorem R113405 : Reach 113405 := rs (se 3 (by rfl) ⟨21263, by rfl⟩) (B 42527 (by norm_num) ⟨21263, by rfl⟩ (by norm_num))
theorem R80637 : Reach 80637 := rs (se 3 (by rfl) ⟨15119, by rfl⟩) (B 30239 (by norm_num) ⟨15119, by rfl⟩ (by norm_num))
theorem R80641 : Reach 80641 := rs (se 2 (by rfl) ⟨30240, by rfl⟩) (B 60481 (by norm_num) ⟨30240, by rfl⟩ (by norm_num))
theorem R80645 : Reach 80645 := rs (se 4 (by rfl) ⟨7560, by rfl⟩) (B 15121 (by norm_num) ⟨7560, by rfl⟩ (by norm_num))
theorem R80649 : Reach 80649 := rs (se 2 (by rfl) ⟨30243, by rfl⟩) (B 60487 (by norm_num) ⟨30243, by rfl⟩ (by norm_num))
theorem R80653 : Reach 80653 := rs (se 3 (by rfl) ⟨15122, by rfl⟩) (B 30245 (by norm_num) ⟨15122, by rfl⟩ (by norm_num))
theorem R80657 : Reach 80657 := rs (se 2 (by rfl) ⟨30246, by rfl⟩) (B 60493 (by norm_num) ⟨30246, by rfl⟩ (by norm_num))
theorem R80661 : Reach 80661 := rs (se 6 (by rfl) ⟨1890, by rfl⟩) (B 3781 (by norm_num) ⟨1890, by rfl⟩ (by norm_num))
theorem R80665 : Reach 80665 := rs (se 2 (by rfl) ⟨30249, by rfl⟩) (B 60499 (by norm_num) ⟨30249, by rfl⟩ (by norm_num))
theorem R178973 : Reach 178973 := rs (se 3 (by rfl) ⟨33557, by rfl⟩) (B 67115 (by norm_num) ⟨33557, by rfl⟩ (by norm_num))
theorem R80669 : Reach 80669 := rs (se 3 (by rfl) ⟨15125, by rfl⟩) (B 30251 (by norm_num) ⟨15125, by rfl⟩ (by norm_num))
theorem R80673 : Reach 80673 := rs (se 2 (by rfl) ⟨30252, by rfl⟩) (B 60505 (by norm_num) ⟨30252, by rfl⟩ (by norm_num))
theorem R80677 : Reach 80677 := rs (se 4 (by rfl) ⟨7563, by rfl⟩) (B 15127 (by norm_num) ⟨7563, by rfl⟩ (by norm_num))
theorem R80681 : Reach 80681 := rs (se 2 (by rfl) ⟨30255, by rfl⟩) (B 60511 (by norm_num) ⟨30255, by rfl⟩ (by norm_num))
theorem R80685 : Reach 80685 := rs (se 3 (by rfl) ⟨15128, by rfl⟩) (B 30257 (by norm_num) ⟨15128, by rfl⟩ (by norm_num))
theorem R80689 : Reach 80689 := rs (se 2 (by rfl) ⟨30258, by rfl⟩) (B 60517 (by norm_num) ⟨30258, by rfl⟩ (by norm_num))
theorem R80693 : Reach 80693 := rs (se 5 (by rfl) ⟨3782, by rfl⟩) (B 7565 (by norm_num) ⟨3782, by rfl⟩ (by norm_num))
theorem R80697 : Reach 80697 := rs (se 2 (by rfl) ⟨30261, by rfl⟩) (B 60523 (by norm_num) ⟨30261, by rfl⟩ (by norm_num))
theorem R80701 : Reach 80701 := rs (se 3 (by rfl) ⟨15131, by rfl⟩) (B 30263 (by norm_num) ⟨15131, by rfl⟩ (by norm_num))
theorem R80705 : Reach 80705 := rs (se 2 (by rfl) ⟨30264, by rfl⟩) (B 60529 (by norm_num) ⟨30264, by rfl⟩ (by norm_num))
theorem R80709 : Reach 80709 := rs (se 4 (by rfl) ⟨7566, by rfl⟩) (B 15133 (by norm_num) ⟨7566, by rfl⟩ (by norm_num))
theorem R80713 : Reach 80713 := rs (se 2 (by rfl) ⟨30267, by rfl⟩) (B 60535 (by norm_num) ⟨30267, by rfl⟩ (by norm_num))
theorem R80717 : Reach 80717 := rs (se 3 (by rfl) ⟨15134, by rfl⟩) (B 30269 (by norm_num) ⟨15134, by rfl⟩ (by norm_num))
theorem R80721 : Reach 80721 := rs (se 2 (by rfl) ⟨30270, by rfl⟩) (B 60541 (by norm_num) ⟨30270, by rfl⟩ (by norm_num))
theorem R80725 : Reach 80725 := rs (se 9 (by rfl) ⟨236, by rfl⟩) (B 473 (by norm_num) ⟨236, by rfl⟩ (by norm_num))
theorem R80729 : Reach 80729 := rs (se 2 (by rfl) ⟨30273, by rfl⟩) (B 60547 (by norm_num) ⟨30273, by rfl⟩ (by norm_num))
theorem R80733 : Reach 80733 := rs (se 3 (by rfl) ⟨15137, by rfl⟩) (B 30275 (by norm_num) ⟨15137, by rfl⟩ (by norm_num))
theorem R80737 : Reach 80737 := rs (se 2 (by rfl) ⟨30276, by rfl⟩) (B 60553 (by norm_num) ⟨30276, by rfl⟩ (by norm_num))
theorem R179045 : Reach 179045 := rs (se 4 (by rfl) ⟨16785, by rfl⟩) (B 33571 (by norm_num) ⟨16785, by rfl⟩ (by norm_num))
theorem R80741 : Reach 80741 := rs (se 4 (by rfl) ⟨7569, by rfl⟩) (B 15139 (by norm_num) ⟨7569, by rfl⟩ (by norm_num))
theorem R80745 : Reach 80745 := rs (se 2 (by rfl) ⟨30279, by rfl⟩) (B 60559 (by norm_num) ⟨30279, by rfl⟩ (by norm_num))
theorem R80749 : Reach 80749 := rs (se 3 (by rfl) ⟨15140, by rfl⟩) (B 30281 (by norm_num) ⟨15140, by rfl⟩ (by norm_num))
theorem R80753 : Reach 80753 := rs (se 2 (by rfl) ⟨30282, by rfl⟩) (B 60565 (by norm_num) ⟨30282, by rfl⟩ (by norm_num))
theorem R80757 : Reach 80757 := rs (se 5 (by rfl) ⟨3785, by rfl⟩) (B 7571 (by norm_num) ⟨3785, by rfl⟩ (by norm_num))
theorem R80761 : Reach 80761 := rs (se 2 (by rfl) ⟨30285, by rfl⟩) (B 60571 (by norm_num) ⟨30285, by rfl⟩ (by norm_num))
theorem R80765 : Reach 80765 := rs (se 3 (by rfl) ⟨15143, by rfl⟩) (B 30287 (by norm_num) ⟨15143, by rfl⟩ (by norm_num))
theorem R80769 : Reach 80769 := rs (se 2 (by rfl) ⟨30288, by rfl⟩) (B 60577 (by norm_num) ⟨30288, by rfl⟩ (by norm_num))
theorem R80773 : Reach 80773 := rs (se 4 (by rfl) ⟨7572, by rfl⟩) (B 15145 (by norm_num) ⟨7572, by rfl⟩ (by norm_num))
theorem R80777 : Reach 80777 := rs (se 2 (by rfl) ⟨30291, by rfl⟩) (B 60583 (by norm_num) ⟨30291, by rfl⟩ (by norm_num))
theorem R80781 : Reach 80781 := rs (se 3 (by rfl) ⟨15146, by rfl⟩) (B 30293 (by norm_num) ⟨15146, by rfl⟩ (by norm_num))
theorem R80785 : Reach 80785 := rs (se 2 (by rfl) ⟨30294, by rfl⟩) (B 60589 (by norm_num) ⟨30294, by rfl⟩ (by norm_num))
theorem R80789 : Reach 80789 := rs (se 6 (by rfl) ⟨1893, by rfl⟩) (B 3787 (by norm_num) ⟨1893, by rfl⟩ (by norm_num))
theorem R277397 : Reach 277397 := rs (se 6 (by rfl) ⟨6501, by rfl⟩) (B 13003 (by norm_num) ⟨6501, by rfl⟩ (by norm_num))
theorem R80793 : Reach 80793 := rs (se 2 (by rfl) ⟨30297, by rfl⟩) (B 60595 (by norm_num) ⟨30297, by rfl⟩ (by norm_num))
theorem R80797 : Reach 80797 := rs (se 3 (by rfl) ⟨15149, by rfl⟩) (B 30299 (by norm_num) ⟨15149, by rfl⟩ (by norm_num))
theorem R80801 : Reach 80801 := rs (se 2 (by rfl) ⟨30300, by rfl⟩) (B 60601 (by norm_num) ⟨30300, by rfl⟩ (by norm_num))
theorem R342949 : Reach 342949 := rs (se 4 (by rfl) ⟨32151, by rfl⟩) (B 64303 (by norm_num) ⟨32151, by rfl⟩ (by norm_num))
theorem R80805 : Reach 80805 := rs (se 4 (by rfl) ⟨7575, by rfl⟩) (B 15151 (by norm_num) ⟨7575, by rfl⟩ (by norm_num))
theorem R80809 : Reach 80809 := rs (se 2 (by rfl) ⟨30303, by rfl⟩) (B 60607 (by norm_num) ⟨30303, by rfl⟩ (by norm_num))
theorem R179117 : Reach 179117 := rs (se 3 (by rfl) ⟨33584, by rfl⟩) (B 67169 (by norm_num) ⟨33584, by rfl⟩ (by norm_num))
theorem R80813 : Reach 80813 := rs (se 3 (by rfl) ⟨15152, by rfl⟩) (B 30305 (by norm_num) ⟨15152, by rfl⟩ (by norm_num))
theorem R80817 : Reach 80817 := rs (se 2 (by rfl) ⟨30306, by rfl⟩) (B 60613 (by norm_num) ⟨30306, by rfl⟩ (by norm_num))
theorem R80821 : Reach 80821 := rs (se 5 (by rfl) ⟨3788, by rfl⟩) (B 7577 (by norm_num) ⟨3788, by rfl⟩ (by norm_num))
theorem R80825 : Reach 80825 := rs (se 2 (by rfl) ⟨30309, by rfl⟩) (B 60619 (by norm_num) ⟨30309, by rfl⟩ (by norm_num))
theorem R80829 : Reach 80829 := rs (se 3 (by rfl) ⟨15155, by rfl⟩) (B 30311 (by norm_num) ⟨15155, by rfl⟩ (by norm_num))
theorem R80833 : Reach 80833 := rs (se 2 (by rfl) ⟨30312, by rfl⟩) (B 60625 (by norm_num) ⟨30312, by rfl⟩ (by norm_num))
theorem R80837 : Reach 80837 := rs (se 4 (by rfl) ⟨7578, by rfl⟩) (B 15157 (by norm_num) ⟨7578, by rfl⟩ (by norm_num))
theorem R80841 : Reach 80841 := rs (se 2 (by rfl) ⟨30315, by rfl⟩) (B 60631 (by norm_num) ⟨30315, by rfl⟩ (by norm_num))
theorem R80845 : Reach 80845 := rs (se 3 (by rfl) ⟨15158, by rfl⟩) (B 30317 (by norm_num) ⟨15158, by rfl⟩ (by norm_num))
theorem R80849 : Reach 80849 := rs (se 2 (by rfl) ⟨30318, by rfl⟩) (B 60637 (by norm_num) ⟨30318, by rfl⟩ (by norm_num))
theorem R80853 : Reach 80853 := rs (se 7 (by rfl) ⟨947, by rfl⟩) (B 1895 (by norm_num) ⟨947, by rfl⟩ (by norm_num))
theorem R80857 : Reach 80857 := rs (se 2 (by rfl) ⟨30321, by rfl⟩) (B 60643 (by norm_num) ⟨30321, by rfl⟩ (by norm_num))
theorem R80861 : Reach 80861 := rs (se 3 (by rfl) ⟨15161, by rfl⟩) (B 30323 (by norm_num) ⟨15161, by rfl⟩ (by norm_num))
theorem R80865 : Reach 80865 := rs (se 2 (by rfl) ⟨30324, by rfl⟩) (B 60649 (by norm_num) ⟨30324, by rfl⟩ (by norm_num))
theorem R80869 : Reach 80869 := rs (se 4 (by rfl) ⟨7581, by rfl⟩) (B 15163 (by norm_num) ⟨7581, by rfl⟩ (by norm_num))
theorem R80873 : Reach 80873 := rs (se 2 (by rfl) ⟨30327, by rfl⟩) (B 60655 (by norm_num) ⟨30327, by rfl⟩ (by norm_num))
theorem R80877 : Reach 80877 := rs (se 3 (by rfl) ⟨15164, by rfl⟩) (B 30329 (by norm_num) ⟨15164, by rfl⟩ (by norm_num))
theorem R80881 : Reach 80881 := rs (se 2 (by rfl) ⟨30330, by rfl⟩) (B 60661 (by norm_num) ⟨30330, by rfl⟩ (by norm_num))
theorem R179189 : Reach 179189 := rs (se 5 (by rfl) ⟨8399, by rfl⟩) (B 16799 (by norm_num) ⟨8399, by rfl⟩ (by norm_num))
theorem R80885 : Reach 80885 := rs (se 5 (by rfl) ⟨3791, by rfl⟩) (B 7583 (by norm_num) ⟨3791, by rfl⟩ (by norm_num))
theorem R80889 : Reach 80889 := rs (se 2 (by rfl) ⟨30333, by rfl⟩) (B 60667 (by norm_num) ⟨30333, by rfl⟩ (by norm_num))
theorem R80893 : Reach 80893 := rs (se 3 (by rfl) ⟨15167, by rfl⟩) (B 30335 (by norm_num) ⟨15167, by rfl⟩ (by norm_num))
theorem R80897 : Reach 80897 := rs (se 2 (by rfl) ⟨30336, by rfl⟩) (B 60673 (by norm_num) ⟨30336, by rfl⟩ (by norm_num))
theorem R80901 : Reach 80901 := rs (se 4 (by rfl) ⟨7584, by rfl⟩) (B 15169 (by norm_num) ⟨7584, by rfl⟩ (by norm_num))
theorem R80905 : Reach 80905 := rs (se 2 (by rfl) ⟨30339, by rfl⟩) (B 60679 (by norm_num) ⟨30339, by rfl⟩ (by norm_num))
theorem R80909 : Reach 80909 := rs (se 3 (by rfl) ⟨15170, by rfl⟩) (B 30341 (by norm_num) ⟨15170, by rfl⟩ (by norm_num))
theorem R80913 : Reach 80913 := rs (se 2 (by rfl) ⟨30342, by rfl⟩) (B 60685 (by norm_num) ⟨30342, by rfl⟩ (by norm_num))
theorem R80917 : Reach 80917 := rs (se 6 (by rfl) ⟨1896, by rfl⟩) (B 3793 (by norm_num) ⟨1896, by rfl⟩ (by norm_num))
theorem R80921 : Reach 80921 := rs (se 2 (by rfl) ⟨30345, by rfl⟩) (B 60691 (by norm_num) ⟨30345, by rfl⟩ (by norm_num))
theorem R80925 : Reach 80925 := rs (se 3 (by rfl) ⟨15173, by rfl⟩) (B 30347 (by norm_num) ⟨15173, by rfl⟩ (by norm_num))
theorem R80929 : Reach 80929 := rs (se 2 (by rfl) ⟨30348, by rfl⟩) (B 60697 (by norm_num) ⟨30348, by rfl⟩ (by norm_num))
theorem R80933 : Reach 80933 := rs (se 4 (by rfl) ⟨7587, by rfl⟩) (B 15175 (by norm_num) ⟨7587, by rfl⟩ (by norm_num))
theorem R80937 : Reach 80937 := rs (se 2 (by rfl) ⟨30351, by rfl⟩) (B 60703 (by norm_num) ⟨30351, by rfl⟩ (by norm_num))
theorem R80941 : Reach 80941 := rs (se 3 (by rfl) ⟨15176, by rfl⟩) (B 30353 (by norm_num) ⟨15176, by rfl⟩ (by norm_num))
theorem R80945 : Reach 80945 := rs (se 2 (by rfl) ⟨30354, by rfl⟩) (B 60709 (by norm_num) ⟨30354, by rfl⟩ (by norm_num))
theorem R80949 : Reach 80949 := rs (se 5 (by rfl) ⟨3794, by rfl⟩) (B 7589 (by norm_num) ⟨3794, by rfl⟩ (by norm_num))
theorem R80953 : Reach 80953 := rs (se 2 (by rfl) ⟨30357, by rfl⟩) (B 60715 (by norm_num) ⟨30357, by rfl⟩ (by norm_num))
theorem R179261 : Reach 179261 := rs (se 3 (by rfl) ⟨33611, by rfl⟩) (B 67223 (by norm_num) ⟨33611, by rfl⟩ (by norm_num))
theorem R80957 : Reach 80957 := rs (se 3 (by rfl) ⟨15179, by rfl⟩) (B 30359 (by norm_num) ⟨15179, by rfl⟩ (by norm_num))
theorem R80961 : Reach 80961 := rs (se 2 (by rfl) ⟨30360, by rfl⟩) (B 60721 (by norm_num) ⟨30360, by rfl⟩ (by norm_num))
theorem R80965 : Reach 80965 := rs (se 4 (by rfl) ⟨7590, by rfl⟩) (B 15181 (by norm_num) ⟨7590, by rfl⟩ (by norm_num))
theorem R80969 : Reach 80969 := rs (se 2 (by rfl) ⟨30363, by rfl⟩) (B 60727 (by norm_num) ⟨30363, by rfl⟩ (by norm_num))
theorem R80973 : Reach 80973 := rs (se 3 (by rfl) ⟨15182, by rfl⟩) (B 30365 (by norm_num) ⟨15182, by rfl⟩ (by norm_num))
theorem R80977 : Reach 80977 := rs (se 2 (by rfl) ⟨30366, by rfl⟩) (B 60733 (by norm_num) ⟨30366, by rfl⟩ (by norm_num))
theorem R80981 : Reach 80981 := rs (se 8 (by rfl) ⟨474, by rfl⟩) (B 949 (by norm_num) ⟨474, by rfl⟩ (by norm_num))
theorem R80985 : Reach 80985 := rs (se 2 (by rfl) ⟨30369, by rfl⟩) (B 60739 (by norm_num) ⟨30369, by rfl⟩ (by norm_num))
theorem R80989 : Reach 80989 := rs (se 3 (by rfl) ⟨15185, by rfl⟩) (B 30371 (by norm_num) ⟨15185, by rfl⟩ (by norm_num))
theorem R80993 : Reach 80993 := rs (se 2 (by rfl) ⟨30372, by rfl⟩) (B 60745 (by norm_num) ⟨30372, by rfl⟩ (by norm_num))
theorem R80997 : Reach 80997 := rs (se 4 (by rfl) ⟨7593, by rfl⟩) (B 15187 (by norm_num) ⟨7593, by rfl⟩ (by norm_num))
theorem R81001 : Reach 81001 := rs (se 2 (by rfl) ⟨30375, by rfl⟩) (B 60751 (by norm_num) ⟨30375, by rfl⟩ (by norm_num))
theorem R81005 : Reach 81005 := rs (se 3 (by rfl) ⟨15188, by rfl⟩) (B 30377 (by norm_num) ⟨15188, by rfl⟩ (by norm_num))
theorem R81009 : Reach 81009 := rs (se 2 (by rfl) ⟨30378, by rfl⟩) (B 60757 (by norm_num) ⟨30378, by rfl⟩ (by norm_num))
theorem R81013 : Reach 81013 := rs (se 5 (by rfl) ⟨3797, by rfl⟩) (B 7595 (by norm_num) ⟨3797, by rfl⟩ (by norm_num))
theorem R81017 : Reach 81017 := rs (se 2 (by rfl) ⟨30381, by rfl⟩) (B 60763 (by norm_num) ⟨30381, by rfl⟩ (by norm_num))
theorem R81021 : Reach 81021 := rs (se 3 (by rfl) ⟨15191, by rfl⟩) (B 30383 (by norm_num) ⟨15191, by rfl⟩ (by norm_num))
theorem R81025 : Reach 81025 := rs (se 2 (by rfl) ⟨30384, by rfl⟩) (B 60769 (by norm_num) ⟨30384, by rfl⟩ (by norm_num))
theorem R179333 : Reach 179333 := rs (se 4 (by rfl) ⟨16812, by rfl⟩) (B 33625 (by norm_num) ⟨16812, by rfl⟩ (by norm_num))
theorem R81029 : Reach 81029 := rs (se 4 (by rfl) ⟨7596, by rfl⟩) (B 15193 (by norm_num) ⟨7596, by rfl⟩ (by norm_num))
theorem R81033 : Reach 81033 := rs (se 2 (by rfl) ⟨30387, by rfl⟩) (B 60775 (by norm_num) ⟨30387, by rfl⟩ (by norm_num))
theorem R81037 : Reach 81037 := rs (se 3 (by rfl) ⟨15194, by rfl⟩) (B 30389 (by norm_num) ⟨15194, by rfl⟩ (by norm_num))
theorem R81041 : Reach 81041 := rs (se 2 (by rfl) ⟨30390, by rfl⟩) (B 60781 (by norm_num) ⟨30390, by rfl⟩ (by norm_num))
theorem R408725 : Reach 408725 := rs (se 6 (by rfl) ⟨9579, by rfl⟩) (B 19159 (by norm_num) ⟨9579, by rfl⟩ (by norm_num))
theorem R81045 : Reach 81045 := rs (se 6 (by rfl) ⟨1899, by rfl⟩) (B 3799 (by norm_num) ⟨1899, by rfl⟩ (by norm_num))
theorem R81049 : Reach 81049 := rs (se 2 (by rfl) ⟨30393, by rfl⟩) (B 60787 (by norm_num) ⟨30393, by rfl⟩ (by norm_num))
theorem R81053 : Reach 81053 := rs (se 3 (by rfl) ⟨15197, by rfl⟩) (B 30395 (by norm_num) ⟨15197, by rfl⟩ (by norm_num))
theorem R81057 : Reach 81057 := rs (se 2 (by rfl) ⟨30396, by rfl⟩) (B 60793 (by norm_num) ⟨30396, by rfl⟩ (by norm_num))
theorem R81061 : Reach 81061 := rs (se 4 (by rfl) ⟨7599, by rfl⟩) (B 15199 (by norm_num) ⟨7599, by rfl⟩ (by norm_num))
theorem R81065 : Reach 81065 := rs (se 2 (by rfl) ⟨30399, by rfl⟩) (B 60799 (by norm_num) ⟨30399, by rfl⟩ (by norm_num))
theorem R81069 : Reach 81069 := rs (se 3 (by rfl) ⟨15200, by rfl⟩) (B 30401 (by norm_num) ⟨15200, by rfl⟩ (by norm_num))
theorem R81073 : Reach 81073 := rs (se 2 (by rfl) ⟨30402, by rfl⟩) (B 60805 (by norm_num) ⟨30402, by rfl⟩ (by norm_num))
theorem R81077 : Reach 81077 := rs (se 5 (by rfl) ⟨3800, by rfl⟩) (B 7601 (by norm_num) ⟨3800, by rfl⟩ (by norm_num))
theorem R81081 : Reach 81081 := rs (se 2 (by rfl) ⟨30405, by rfl⟩) (B 60811 (by norm_num) ⟨30405, by rfl⟩ (by norm_num))
theorem R81085 : Reach 81085 := rs (se 3 (by rfl) ⟨15203, by rfl⟩) (B 30407 (by norm_num) ⟨15203, by rfl⟩ (by norm_num))
theorem R81089 : Reach 81089 := rs (se 2 (by rfl) ⟨30408, by rfl⟩) (B 60817 (by norm_num) ⟨30408, by rfl⟩ (by norm_num))
theorem R81093 : Reach 81093 := rs (se 4 (by rfl) ⟨7602, by rfl⟩) (B 15205 (by norm_num) ⟨7602, by rfl⟩ (by norm_num))
theorem R81097 : Reach 81097 := rs (se 2 (by rfl) ⟨30411, by rfl⟩) (B 60823 (by norm_num) ⟨30411, by rfl⟩ (by norm_num))
theorem R179405 : Reach 179405 := rs (se 3 (by rfl) ⟨33638, by rfl⟩) (B 67277 (by norm_num) ⟨33638, by rfl⟩ (by norm_num))
theorem R81101 : Reach 81101 := rs (se 3 (by rfl) ⟨15206, by rfl⟩) (B 30413 (by norm_num) ⟨15206, by rfl⟩ (by norm_num))
theorem R81105 : Reach 81105 := rs (se 2 (by rfl) ⟨30414, by rfl⟩) (B 60829 (by norm_num) ⟨30414, by rfl⟩ (by norm_num))
theorem R81109 : Reach 81109 := rs (se 7 (by rfl) ⟨950, by rfl⟩) (B 1901 (by norm_num) ⟨950, by rfl⟩ (by norm_num))
theorem R81113 : Reach 81113 := rs (se 2 (by rfl) ⟨30417, by rfl⟩) (B 60835 (by norm_num) ⟨30417, by rfl⟩ (by norm_num))
theorem R81117 : Reach 81117 := rs (se 3 (by rfl) ⟨15209, by rfl⟩) (B 30419 (by norm_num) ⟨15209, by rfl⟩ (by norm_num))
theorem R81121 : Reach 81121 := rs (se 2 (by rfl) ⟨30420, by rfl⟩) (B 60841 (by norm_num) ⟨30420, by rfl⟩ (by norm_num))
theorem R81125 : Reach 81125 := rs (se 4 (by rfl) ⟨7605, by rfl⟩) (B 15211 (by norm_num) ⟨7605, by rfl⟩ (by norm_num))
theorem R81129 : Reach 81129 := rs (se 2 (by rfl) ⟨30423, by rfl⟩) (B 60847 (by norm_num) ⟨30423, by rfl⟩ (by norm_num))
theorem R81133 : Reach 81133 := rs (se 3 (by rfl) ⟨15212, by rfl⟩) (B 30425 (by norm_num) ⟨15212, by rfl⟩ (by norm_num))
theorem R81137 : Reach 81137 := rs (se 2 (by rfl) ⟨30426, by rfl⟩) (B 60853 (by norm_num) ⟨30426, by rfl⟩ (by norm_num))
theorem R81141 : Reach 81141 := rs (se 5 (by rfl) ⟨3803, by rfl⟩) (B 7607 (by norm_num) ⟨3803, by rfl⟩ (by norm_num))
theorem R81145 : Reach 81145 := rs (se 2 (by rfl) ⟨30429, by rfl⟩) (B 60859 (by norm_num) ⟨30429, by rfl⟩ (by norm_num))
theorem R81149 : Reach 81149 := rs (se 3 (by rfl) ⟨15215, by rfl⟩) (B 30431 (by norm_num) ⟨15215, by rfl⟩ (by norm_num))
theorem R81153 : Reach 81153 := rs (se 2 (by rfl) ⟨30432, by rfl⟩) (B 60865 (by norm_num) ⟨30432, by rfl⟩ (by norm_num))
theorem R81157 : Reach 81157 := rs (se 4 (by rfl) ⟨7608, by rfl⟩) (B 15217 (by norm_num) ⟨7608, by rfl⟩ (by norm_num))
theorem R81161 : Reach 81161 := rs (se 2 (by rfl) ⟨30435, by rfl⟩) (B 60871 (by norm_num) ⟨30435, by rfl⟩ (by norm_num))
theorem R81165 : Reach 81165 := rs (se 3 (by rfl) ⟨15218, by rfl⟩) (B 30437 (by norm_num) ⟨15218, by rfl⟩ (by norm_num))
theorem R81169 : Reach 81169 := rs (se 2 (by rfl) ⟨30438, by rfl⟩) (B 60877 (by norm_num) ⟨30438, by rfl⟩ (by norm_num))
theorem R179477 : Reach 179477 := rs (se 6 (by rfl) ⟨4206, by rfl⟩) (B 8413 (by norm_num) ⟨4206, by rfl⟩ (by norm_num))
theorem R81173 : Reach 81173 := rs (se 6 (by rfl) ⟨1902, by rfl⟩) (B 3805 (by norm_num) ⟨1902, by rfl⟩ (by norm_num))
theorem R81177 : Reach 81177 := rs (se 2 (by rfl) ⟨30441, by rfl⟩) (B 60883 (by norm_num) ⟨30441, by rfl⟩ (by norm_num))
theorem R81181 : Reach 81181 := rs (se 3 (by rfl) ⟨15221, by rfl⟩) (B 30443 (by norm_num) ⟨15221, by rfl⟩ (by norm_num))
theorem R81185 : Reach 81185 := rs (se 2 (by rfl) ⟨30444, by rfl⟩) (B 60889 (by norm_num) ⟨30444, by rfl⟩ (by norm_num))
theorem R81189 : Reach 81189 := rs (se 4 (by rfl) ⟨7611, by rfl⟩) (B 15223 (by norm_num) ⟨7611, by rfl⟩ (by norm_num))
theorem R81193 : Reach 81193 := rs (se 2 (by rfl) ⟨30447, by rfl⟩) (B 60895 (by norm_num) ⟨30447, by rfl⟩ (by norm_num))
theorem R81197 : Reach 81197 := rs (se 3 (by rfl) ⟨15224, by rfl⟩) (B 30449 (by norm_num) ⟨15224, by rfl⟩ (by norm_num))
theorem R81201 : Reach 81201 := rs (se 2 (by rfl) ⟨30450, by rfl⟩) (B 60901 (by norm_num) ⟨30450, by rfl⟩ (by norm_num))
theorem R81205 : Reach 81205 := rs (se 5 (by rfl) ⟨3806, by rfl⟩) (B 7613 (by norm_num) ⟨3806, by rfl⟩ (by norm_num))
theorem R81209 : Reach 81209 := rs (se 2 (by rfl) ⟨30453, by rfl⟩) (B 60907 (by norm_num) ⟨30453, by rfl⟩ (by norm_num))
theorem R81213 : Reach 81213 := rs (se 3 (by rfl) ⟨15227, by rfl⟩) (B 30455 (by norm_num) ⟨15227, by rfl⟩ (by norm_num))
theorem R81217 : Reach 81217 := rs (se 2 (by rfl) ⟨30456, by rfl⟩) (B 60913 (by norm_num) ⟨30456, by rfl⟩ (by norm_num))
theorem R81221 : Reach 81221 := rs (se 4 (by rfl) ⟨7614, by rfl⟩) (B 15229 (by norm_num) ⟨7614, by rfl⟩ (by norm_num))
theorem R277829 : Reach 277829 := rs (se 4 (by rfl) ⟨26046, by rfl⟩) (B 52093 (by norm_num) ⟨26046, by rfl⟩ (by norm_num))
theorem R81225 : Reach 81225 := rs (se 2 (by rfl) ⟨30459, by rfl⟩) (B 60919 (by norm_num) ⟨30459, by rfl⟩ (by norm_num))
theorem R81229 : Reach 81229 := rs (se 3 (by rfl) ⟨15230, by rfl⟩) (B 30461 (by norm_num) ⟨15230, by rfl⟩ (by norm_num))
theorem R81233 : Reach 81233 := rs (se 2 (by rfl) ⟨30462, by rfl⟩) (B 60925 (by norm_num) ⟨30462, by rfl⟩ (by norm_num))
theorem R81237 : Reach 81237 := rs (se 11 (by rfl) ⟨59, by rfl⟩) (B 119 (by norm_num) ⟨59, by rfl⟩ (by norm_num))
theorem R81241 : Reach 81241 := rs (se 2 (by rfl) ⟨30465, by rfl⟩) (B 60931 (by norm_num) ⟨30465, by rfl⟩ (by norm_num))
theorem R179549 : Reach 179549 := rs (se 3 (by rfl) ⟨33665, by rfl⟩) (B 67331 (by norm_num) ⟨33665, by rfl⟩ (by norm_num))
theorem R81245 : Reach 81245 := rs (se 3 (by rfl) ⟨15233, by rfl⟩) (B 30467 (by norm_num) ⟨15233, by rfl⟩ (by norm_num))
theorem R81249 : Reach 81249 := rs (se 2 (by rfl) ⟨30468, by rfl⟩) (B 60937 (by norm_num) ⟨30468, by rfl⟩ (by norm_num))
theorem R81253 : Reach 81253 := rs (se 4 (by rfl) ⟨7617, by rfl⟩) (B 15235 (by norm_num) ⟨7617, by rfl⟩ (by norm_num))
theorem R81257 : Reach 81257 := rs (se 2 (by rfl) ⟨30471, by rfl⟩) (B 60943 (by norm_num) ⟨30471, by rfl⟩ (by norm_num))
theorem R81261 : Reach 81261 := rs (se 3 (by rfl) ⟨15236, by rfl⟩) (B 30473 (by norm_num) ⟨15236, by rfl⟩ (by norm_num))
theorem R81265 : Reach 81265 := rs (se 2 (by rfl) ⟨30474, by rfl⟩) (B 60949 (by norm_num) ⟨30474, by rfl⟩ (by norm_num))
theorem R81269 : Reach 81269 := rs (se 5 (by rfl) ⟨3809, by rfl⟩) (B 7619 (by norm_num) ⟨3809, by rfl⟩ (by norm_num))
theorem R81273 : Reach 81273 := rs (se 2 (by rfl) ⟨30477, by rfl⟩) (B 60955 (by norm_num) ⟨30477, by rfl⟩ (by norm_num))
theorem R81277 : Reach 81277 := rs (se 3 (by rfl) ⟨15239, by rfl⟩) (B 30479 (by norm_num) ⟨15239, by rfl⟩ (by norm_num))
theorem R81281 : Reach 81281 := rs (se 2 (by rfl) ⟨30480, by rfl⟩) (B 60961 (by norm_num) ⟨30480, by rfl⟩ (by norm_num))
theorem R81285 : Reach 81285 := rs (se 4 (by rfl) ⟨7620, by rfl⟩) (B 15241 (by norm_num) ⟨7620, by rfl⟩ (by norm_num))
theorem R310661 : Reach 310661 := rs (se 4 (by rfl) ⟨29124, by rfl⟩) (B 58249 (by norm_num) ⟨29124, by rfl⟩ (by norm_num))
theorem R81289 : Reach 81289 := rs (se 2 (by rfl) ⟨30483, by rfl⟩) (B 60967 (by norm_num) ⟨30483, by rfl⟩ (by norm_num))
theorem R81293 : Reach 81293 := rs (se 3 (by rfl) ⟨15242, by rfl⟩) (B 30485 (by norm_num) ⟨15242, by rfl⟩ (by norm_num))
theorem R81297 : Reach 81297 := rs (se 2 (by rfl) ⟨30486, by rfl⟩) (B 60973 (by norm_num) ⟨30486, by rfl⟩ (by norm_num))
theorem R81301 : Reach 81301 := rs (se 6 (by rfl) ⟨1905, by rfl⟩) (B 3811 (by norm_num) ⟨1905, by rfl⟩ (by norm_num))
theorem R81305 : Reach 81305 := rs (se 2 (by rfl) ⟨30489, by rfl⟩) (B 60979 (by norm_num) ⟨30489, by rfl⟩ (by norm_num))
theorem R81309 : Reach 81309 := rs (se 3 (by rfl) ⟨15245, by rfl⟩) (B 30491 (by norm_num) ⟨15245, by rfl⟩ (by norm_num))
theorem R81313 : Reach 81313 := rs (se 2 (by rfl) ⟨30492, by rfl⟩) (B 60985 (by norm_num) ⟨30492, by rfl⟩ (by norm_num))
theorem R179621 : Reach 179621 := rs (se 4 (by rfl) ⟨16839, by rfl⟩) (B 33679 (by norm_num) ⟨16839, by rfl⟩ (by norm_num))
theorem R81317 : Reach 81317 := rs (se 4 (by rfl) ⟨7623, by rfl⟩) (B 15247 (by norm_num) ⟨7623, by rfl⟩ (by norm_num))
theorem R81321 : Reach 81321 := rs (se 2 (by rfl) ⟨30495, by rfl⟩) (B 60991 (by norm_num) ⟨30495, by rfl⟩ (by norm_num))
theorem R81325 : Reach 81325 := rs (se 3 (by rfl) ⟨15248, by rfl⟩) (B 30497 (by norm_num) ⟨15248, by rfl⟩ (by norm_num))
theorem R81329 : Reach 81329 := rs (se 2 (by rfl) ⟨30498, by rfl⟩) (B 60997 (by norm_num) ⟨30498, by rfl⟩ (by norm_num))
theorem R81333 : Reach 81333 := rs (se 5 (by rfl) ⟨3812, by rfl⟩) (B 7625 (by norm_num) ⟨3812, by rfl⟩ (by norm_num))
theorem R81337 : Reach 81337 := rs (se 2 (by rfl) ⟨30501, by rfl⟩) (B 61003 (by norm_num) ⟨30501, by rfl⟩ (by norm_num))
theorem R81341 : Reach 81341 := rs (se 3 (by rfl) ⟨15251, by rfl⟩) (B 30503 (by norm_num) ⟨15251, by rfl⟩ (by norm_num))
theorem R81345 : Reach 81345 := rs (se 2 (by rfl) ⟨30504, by rfl⟩) (B 61009 (by norm_num) ⟨30504, by rfl⟩ (by norm_num))
theorem R81349 : Reach 81349 := rs (se 4 (by rfl) ⟨7626, by rfl⟩) (B 15253 (by norm_num) ⟨7626, by rfl⟩ (by norm_num))
theorem R81353 : Reach 81353 := rs (se 2 (by rfl) ⟨30507, by rfl⟩) (B 61015 (by norm_num) ⟨30507, by rfl⟩ (by norm_num))
theorem R81357 : Reach 81357 := rs (se 3 (by rfl) ⟨15254, by rfl⟩) (B 30509 (by norm_num) ⟨15254, by rfl⟩ (by norm_num))
theorem R81361 : Reach 81361 := rs (se 2 (by rfl) ⟨30510, by rfl⟩) (B 61021 (by norm_num) ⟨30510, by rfl⟩ (by norm_num))
theorem R81365 : Reach 81365 := rs (se 7 (by rfl) ⟨953, by rfl⟩) (B 1907 (by norm_num) ⟨953, by rfl⟩ (by norm_num))
theorem R81369 : Reach 81369 := rs (se 2 (by rfl) ⟨30513, by rfl⟩) (B 61027 (by norm_num) ⟨30513, by rfl⟩ (by norm_num))
theorem R81373 : Reach 81373 := rs (se 3 (by rfl) ⟨15257, by rfl⟩) (B 30515 (by norm_num) ⟨15257, by rfl⟩ (by norm_num))
theorem R81377 : Reach 81377 := rs (se 2 (by rfl) ⟨30516, by rfl⟩) (B 61033 (by norm_num) ⟨30516, by rfl⟩ (by norm_num))
theorem R81381 : Reach 81381 := rs (se 4 (by rfl) ⟨7629, by rfl⟩) (B 15259 (by norm_num) ⟨7629, by rfl⟩ (by norm_num))
theorem R81385 : Reach 81385 := rs (se 2 (by rfl) ⟨30519, by rfl⟩) (B 61039 (by norm_num) ⟨30519, by rfl⟩ (by norm_num))
theorem R179693 : Reach 179693 := rs (se 3 (by rfl) ⟨33692, by rfl⟩) (B 67385 (by norm_num) ⟨33692, by rfl⟩ (by norm_num))
theorem R114157 : Reach 114157 := rs (se 3 (by rfl) ⟨21404, by rfl⟩) (B 42809 (by norm_num) ⟨21404, by rfl⟩ (by norm_num))
theorem R81389 : Reach 81389 := rs (se 3 (by rfl) ⟨15260, by rfl⟩) (B 30521 (by norm_num) ⟨15260, by rfl⟩ (by norm_num))
theorem R81393 : Reach 81393 := rs (se 2 (by rfl) ⟨30522, by rfl⟩) (B 61045 (by norm_num) ⟨30522, by rfl⟩ (by norm_num))
theorem R81397 : Reach 81397 := rs (se 5 (by rfl) ⟨3815, by rfl⟩) (B 7631 (by norm_num) ⟨3815, by rfl⟩ (by norm_num))
theorem R81401 : Reach 81401 := rs (se 2 (by rfl) ⟨30525, by rfl⟩) (B 61051 (by norm_num) ⟨30525, by rfl⟩ (by norm_num))
theorem R81405 : Reach 81405 := rs (se 3 (by rfl) ⟨15263, by rfl⟩) (B 30527 (by norm_num) ⟨15263, by rfl⟩ (by norm_num))
theorem R81409 : Reach 81409 := rs (se 2 (by rfl) ⟨30528, by rfl⟩) (B 61057 (by norm_num) ⟨30528, by rfl⟩ (by norm_num))
theorem R81413 : Reach 81413 := rs (se 4 (by rfl) ⟨7632, by rfl⟩) (B 15265 (by norm_num) ⟨7632, by rfl⟩ (by norm_num))
theorem R81417 : Reach 81417 := rs (se 2 (by rfl) ⟨30531, by rfl⟩) (B 61063 (by norm_num) ⟨30531, by rfl⟩ (by norm_num))
theorem R81421 : Reach 81421 := rs (se 3 (by rfl) ⟨15266, by rfl⟩) (B 30533 (by norm_num) ⟨15266, by rfl⟩ (by norm_num))
theorem R81425 : Reach 81425 := rs (se 2 (by rfl) ⟨30534, by rfl⟩) (B 61069 (by norm_num) ⟨30534, by rfl⟩ (by norm_num))
theorem R81429 : Reach 81429 := rs (se 6 (by rfl) ⟨1908, by rfl⟩) (B 3817 (by norm_num) ⟨1908, by rfl⟩ (by norm_num))
theorem R81433 : Reach 81433 := rs (se 2 (by rfl) ⟨30537, by rfl⟩) (B 61075 (by norm_num) ⟨30537, by rfl⟩ (by norm_num))
theorem R81437 : Reach 81437 := rs (se 3 (by rfl) ⟨15269, by rfl⟩) (B 30539 (by norm_num) ⟨15269, by rfl⟩ (by norm_num))
theorem R81441 : Reach 81441 := rs (se 2 (by rfl) ⟨30540, by rfl⟩) (B 61081 (by norm_num) ⟨30540, by rfl⟩ (by norm_num))
theorem R81445 : Reach 81445 := rs (se 4 (by rfl) ⟨7635, by rfl⟩) (B 15271 (by norm_num) ⟨7635, by rfl⟩ (by norm_num))
theorem R81449 : Reach 81449 := rs (se 2 (by rfl) ⟨30543, by rfl⟩) (B 61087 (by norm_num) ⟨30543, by rfl⟩ (by norm_num))
theorem R81453 : Reach 81453 := rs (se 3 (by rfl) ⟨15272, by rfl⟩) (B 30545 (by norm_num) ⟨15272, by rfl⟩ (by norm_num))
theorem R81457 : Reach 81457 := rs (se 2 (by rfl) ⟨30546, by rfl⟩) (B 61093 (by norm_num) ⟨30546, by rfl⟩ (by norm_num))
theorem R179765 : Reach 179765 := rs (se 5 (by rfl) ⟨8426, by rfl⟩) (B 16853 (by norm_num) ⟨8426, by rfl⟩ (by norm_num))
theorem R81461 : Reach 81461 := rs (se 5 (by rfl) ⟨3818, by rfl⟩) (B 7637 (by norm_num) ⟨3818, by rfl⟩ (by norm_num))
theorem R81465 : Reach 81465 := rs (se 2 (by rfl) ⟨30549, by rfl⟩) (B 61099 (by norm_num) ⟨30549, by rfl⟩ (by norm_num))
theorem R81469 : Reach 81469 := rs (se 3 (by rfl) ⟨15275, by rfl⟩) (B 30551 (by norm_num) ⟨15275, by rfl⟩ (by norm_num))
theorem R81473 : Reach 81473 := rs (se 2 (by rfl) ⟨30552, by rfl⟩) (B 61105 (by norm_num) ⟨30552, by rfl⟩ (by norm_num))
theorem R81477 : Reach 81477 := rs (se 4 (by rfl) ⟨7638, by rfl⟩) (B 15277 (by norm_num) ⟨7638, by rfl⟩ (by norm_num))
theorem R81481 : Reach 81481 := rs (se 2 (by rfl) ⟨30555, by rfl⟩) (B 61111 (by norm_num) ⟨30555, by rfl⟩ (by norm_num))
theorem R81485 : Reach 81485 := rs (se 3 (by rfl) ⟨15278, by rfl⟩) (B 30557 (by norm_num) ⟨15278, by rfl⟩ (by norm_num))
theorem R81489 : Reach 81489 := rs (se 2 (by rfl) ⟨30558, by rfl⟩) (B 61117 (by norm_num) ⟨30558, by rfl⟩ (by norm_num))
theorem R81493 : Reach 81493 := rs (se 8 (by rfl) ⟨477, by rfl⟩) (B 955 (by norm_num) ⟨477, by rfl⟩ (by norm_num))
theorem R81497 : Reach 81497 := rs (se 2 (by rfl) ⟨30561, by rfl⟩) (B 61123 (by norm_num) ⟨30561, by rfl⟩ (by norm_num))
theorem R81501 : Reach 81501 := rs (se 3 (by rfl) ⟨15281, by rfl⟩) (B 30563 (by norm_num) ⟨15281, by rfl⟩ (by norm_num))
theorem R81505 : Reach 81505 := rs (se 2 (by rfl) ⟨30564, by rfl⟩) (B 61129 (by norm_num) ⟨30564, by rfl⟩ (by norm_num))
theorem R81509 : Reach 81509 := rs (se 4 (by rfl) ⟨7641, by rfl⟩) (B 15283 (by norm_num) ⟨7641, by rfl⟩ (by norm_num))
theorem R81513 : Reach 81513 := rs (se 2 (by rfl) ⟨30567, by rfl⟩) (B 61135 (by norm_num) ⟨30567, by rfl⟩ (by norm_num))
theorem R81517 : Reach 81517 := rs (se 3 (by rfl) ⟨15284, by rfl⟩) (B 30569 (by norm_num) ⟨15284, by rfl⟩ (by norm_num))
theorem R81521 : Reach 81521 := rs (se 2 (by rfl) ⟨30570, by rfl⟩) (B 61141 (by norm_num) ⟨30570, by rfl⟩ (by norm_num))
theorem R81525 : Reach 81525 := rs (se 5 (by rfl) ⟨3821, by rfl⟩) (B 7643 (by norm_num) ⟨3821, by rfl⟩ (by norm_num))
theorem R81529 : Reach 81529 := rs (se 2 (by rfl) ⟨30573, by rfl⟩) (B 61147 (by norm_num) ⟨30573, by rfl⟩ (by norm_num))
theorem R179837 : Reach 179837 := rs (se 3 (by rfl) ⟨33719, by rfl⟩) (B 67439 (by norm_num) ⟨33719, by rfl⟩ (by norm_num))
theorem R81533 : Reach 81533 := rs (se 3 (by rfl) ⟨15287, by rfl⟩) (B 30575 (by norm_num) ⟨15287, by rfl⟩ (by norm_num))
theorem R81537 : Reach 81537 := rs (se 2 (by rfl) ⟨30576, by rfl⟩) (B 61153 (by norm_num) ⟨30576, by rfl⟩ (by norm_num))
theorem R81541 : Reach 81541 := rs (se 4 (by rfl) ⟨7644, by rfl⟩) (B 15289 (by norm_num) ⟨7644, by rfl⟩ (by norm_num))
theorem R81545 : Reach 81545 := rs (se 2 (by rfl) ⟨30579, by rfl⟩) (B 61159 (by norm_num) ⟨30579, by rfl⟩ (by norm_num))
theorem R81549 : Reach 81549 := rs (se 3 (by rfl) ⟨15290, by rfl⟩) (B 30581 (by norm_num) ⟨15290, by rfl⟩ (by norm_num))
theorem R81553 : Reach 81553 := rs (se 2 (by rfl) ⟨30582, by rfl⟩) (B 61165 (by norm_num) ⟨30582, by rfl⟩ (by norm_num))
theorem R81557 : Reach 81557 := rs (se 6 (by rfl) ⟨1911, by rfl⟩) (B 3823 (by norm_num) ⟨1911, by rfl⟩ (by norm_num))
theorem R81561 : Reach 81561 := rs (se 2 (by rfl) ⟨30585, by rfl⟩) (B 61171 (by norm_num) ⟨30585, by rfl⟩ (by norm_num))
theorem R81565 : Reach 81565 := rs (se 3 (by rfl) ⟨15293, by rfl⟩) (B 30587 (by norm_num) ⟨15293, by rfl⟩ (by norm_num))
theorem R81569 : Reach 81569 := rs (se 2 (by rfl) ⟨30588, by rfl⟩) (B 61177 (by norm_num) ⟨30588, by rfl⟩ (by norm_num))
theorem R310949 : Reach 310949 := rs (se 4 (by rfl) ⟨29151, by rfl⟩) (B 58303 (by norm_num) ⟨29151, by rfl⟩ (by norm_num))
theorem R81573 : Reach 81573 := rs (se 4 (by rfl) ⟨7647, by rfl⟩) (B 15295 (by norm_num) ⟨7647, by rfl⟩ (by norm_num))
theorem R81577 : Reach 81577 := rs (se 2 (by rfl) ⟨30591, by rfl⟩) (B 61183 (by norm_num) ⟨30591, by rfl⟩ (by norm_num))
theorem R81581 : Reach 81581 := rs (se 3 (by rfl) ⟨15296, by rfl⟩) (B 30593 (by norm_num) ⟨15296, by rfl⟩ (by norm_num))
theorem R81585 : Reach 81585 := rs (se 2 (by rfl) ⟨30594, by rfl⟩) (B 61189 (by norm_num) ⟨30594, by rfl⟩ (by norm_num))
theorem R81589 : Reach 81589 := rs (se 5 (by rfl) ⟨3824, by rfl⟩) (B 7649 (by norm_num) ⟨3824, by rfl⟩ (by norm_num))
theorem R81593 : Reach 81593 := rs (se 2 (by rfl) ⟨30597, by rfl⟩) (B 61195 (by norm_num) ⟨30597, by rfl⟩ (by norm_num))
theorem R81597 : Reach 81597 := rs (se 3 (by rfl) ⟨15299, by rfl⟩) (B 30599 (by norm_num) ⟨15299, by rfl⟩ (by norm_num))
theorem R147133 : Reach 147133 := rs (se 3 (by rfl) ⟨27587, by rfl⟩) (B 55175 (by norm_num) ⟨27587, by rfl⟩ (by norm_num))
theorem R81601 : Reach 81601 := rs (se 2 (by rfl) ⟨30600, by rfl⟩) (B 61201 (by norm_num) ⟨30600, by rfl⟩ (by norm_num))
theorem R179909 : Reach 179909 := rs (se 4 (by rfl) ⟨16866, by rfl⟩) (B 33733 (by norm_num) ⟨16866, by rfl⟩ (by norm_num))
theorem R81605 : Reach 81605 := rs (se 4 (by rfl) ⟨7650, by rfl⟩) (B 15301 (by norm_num) ⟨7650, by rfl⟩ (by norm_num))
theorem R81609 : Reach 81609 := rs (se 2 (by rfl) ⟨30603, by rfl⟩) (B 61207 (by norm_num) ⟨30603, by rfl⟩ (by norm_num))
theorem R81613 : Reach 81613 := rs (se 3 (by rfl) ⟨15302, by rfl⟩) (B 30605 (by norm_num) ⟨15302, by rfl⟩ (by norm_num))
theorem R81617 : Reach 81617 := rs (se 2 (by rfl) ⟨30606, by rfl⟩) (B 61213 (by norm_num) ⟨30606, by rfl⟩ (by norm_num))
theorem R81621 : Reach 81621 := rs (se 7 (by rfl) ⟨956, by rfl⟩) (B 1913 (by norm_num) ⟨956, by rfl⟩ (by norm_num))
theorem R81625 : Reach 81625 := rs (se 2 (by rfl) ⟨30609, by rfl⟩) (B 61219 (by norm_num) ⟨30609, by rfl⟩ (by norm_num))
theorem R81629 : Reach 81629 := rs (se 3 (by rfl) ⟨15305, by rfl⟩) (B 30611 (by norm_num) ⟨15305, by rfl⟩ (by norm_num))
theorem R81633 : Reach 81633 := rs (se 2 (by rfl) ⟨30612, by rfl⟩) (B 61225 (by norm_num) ⟨30612, by rfl⟩ (by norm_num))
theorem R81637 : Reach 81637 := rs (se 4 (by rfl) ⟨7653, by rfl⟩) (B 15307 (by norm_num) ⟨7653, by rfl⟩ (by norm_num))
theorem R81641 : Reach 81641 := rs (se 2 (by rfl) ⟨30615, by rfl⟩) (B 61231 (by norm_num) ⟨30615, by rfl⟩ (by norm_num))
theorem R81645 : Reach 81645 := rs (se 3 (by rfl) ⟨15308, by rfl⟩) (B 30617 (by norm_num) ⟨15308, by rfl⟩ (by norm_num))
theorem R81649 : Reach 81649 := rs (se 2 (by rfl) ⟨30618, by rfl⟩) (B 61237 (by norm_num) ⟨30618, by rfl⟩ (by norm_num))
theorem R81653 : Reach 81653 := rs (se 5 (by rfl) ⟨3827, by rfl⟩) (B 7655 (by norm_num) ⟨3827, by rfl⟩ (by norm_num))
theorem R278261 : Reach 278261 := rs (se 5 (by rfl) ⟨13043, by rfl⟩) (B 26087 (by norm_num) ⟨13043, by rfl⟩ (by norm_num))
theorem R81657 : Reach 81657 := rs (se 2 (by rfl) ⟨30621, by rfl⟩) (B 61243 (by norm_num) ⟨30621, by rfl⟩ (by norm_num))
theorem R81661 : Reach 81661 := rs (se 3 (by rfl) ⟨15311, by rfl⟩) (B 30623 (by norm_num) ⟨15311, by rfl⟩ (by norm_num))
theorem R81665 : Reach 81665 := rs (se 2 (by rfl) ⟨30624, by rfl⟩) (B 61249 (by norm_num) ⟨30624, by rfl⟩ (by norm_num))
theorem R81669 : Reach 81669 := rs (se 4 (by rfl) ⟨7656, by rfl⟩) (B 15313 (by norm_num) ⟨7656, by rfl⟩ (by norm_num))
theorem R81673 : Reach 81673 := rs (se 2 (by rfl) ⟨30627, by rfl⟩) (B 61255 (by norm_num) ⟨30627, by rfl⟩ (by norm_num))
theorem R179981 : Reach 179981 := rs (se 3 (by rfl) ⟨33746, by rfl⟩) (B 67493 (by norm_num) ⟨33746, by rfl⟩ (by norm_num))
theorem R81677 : Reach 81677 := rs (se 3 (by rfl) ⟨15314, by rfl⟩) (B 30629 (by norm_num) ⟨15314, by rfl⟩ (by norm_num))
theorem R81681 : Reach 81681 := rs (se 2 (by rfl) ⟨30630, by rfl⟩) (B 61261 (by norm_num) ⟨30630, by rfl⟩ (by norm_num))
theorem R81685 : Reach 81685 := rs (se 6 (by rfl) ⟨1914, by rfl⟩) (B 3829 (by norm_num) ⟨1914, by rfl⟩ (by norm_num))
theorem R81689 : Reach 81689 := rs (se 2 (by rfl) ⟨30633, by rfl⟩) (B 61267 (by norm_num) ⟨30633, by rfl⟩ (by norm_num))
theorem R81693 : Reach 81693 := rs (se 3 (by rfl) ⟨15317, by rfl⟩) (B 30635 (by norm_num) ⟨15317, by rfl⟩ (by norm_num))
theorem R81697 : Reach 81697 := rs (se 2 (by rfl) ⟨30636, by rfl⟩) (B 61273 (by norm_num) ⟨30636, by rfl⟩ (by norm_num))
theorem R81701 : Reach 81701 := rs (se 4 (by rfl) ⟨7659, by rfl⟩) (B 15319 (by norm_num) ⟨7659, by rfl⟩ (by norm_num))
theorem R81705 : Reach 81705 := rs (se 2 (by rfl) ⟨30639, by rfl⟩) (B 61279 (by norm_num) ⟨30639, by rfl⟩ (by norm_num))
theorem R81709 : Reach 81709 := rs (se 3 (by rfl) ⟨15320, by rfl⟩) (B 30641 (by norm_num) ⟨15320, by rfl⟩ (by norm_num))
theorem R81713 : Reach 81713 := rs (se 2 (by rfl) ⟨30642, by rfl⟩) (B 61285 (by norm_num) ⟨30642, by rfl⟩ (by norm_num))
theorem R81717 : Reach 81717 := rs (se 5 (by rfl) ⟨3830, by rfl⟩) (B 7661 (by norm_num) ⟨3830, by rfl⟩ (by norm_num))
theorem R81721 : Reach 81721 := rs (se 2 (by rfl) ⟨30645, by rfl⟩) (B 61291 (by norm_num) ⟨30645, by rfl⟩ (by norm_num))
theorem R81725 : Reach 81725 := rs (se 3 (by rfl) ⟨15323, by rfl⟩) (B 30647 (by norm_num) ⟨15323, by rfl⟩ (by norm_num))
theorem R81729 : Reach 81729 := rs (se 2 (by rfl) ⟨30648, by rfl⟩) (B 61297 (by norm_num) ⟨30648, by rfl⟩ (by norm_num))
theorem R81733 : Reach 81733 := rs (se 4 (by rfl) ⟨7662, by rfl⟩) (B 15325 (by norm_num) ⟨7662, by rfl⟩ (by norm_num))
theorem R81737 : Reach 81737 := rs (se 2 (by rfl) ⟨30651, by rfl⟩) (B 61303 (by norm_num) ⟨30651, by rfl⟩ (by norm_num))
theorem R81741 : Reach 81741 := rs (se 3 (by rfl) ⟨15326, by rfl⟩) (B 30653 (by norm_num) ⟨15326, by rfl⟩ (by norm_num))
theorem R81745 : Reach 81745 := rs (se 2 (by rfl) ⟨30654, by rfl⟩) (B 61309 (by norm_num) ⟨30654, by rfl⟩ (by norm_num))
theorem R180053 : Reach 180053 := rs (se 9 (by rfl) ⟨527, by rfl⟩) (B 1055 (by norm_num) ⟨527, by rfl⟩ (by norm_num))
theorem R81749 : Reach 81749 := rs (se 9 (by rfl) ⟨239, by rfl⟩) (B 479 (by norm_num) ⟨239, by rfl⟩ (by norm_num))
theorem R81753 : Reach 81753 := rs (se 2 (by rfl) ⟨30657, by rfl⟩) (B 61315 (by norm_num) ⟨30657, by rfl⟩ (by norm_num))
theorem R81757 : Reach 81757 := rs (se 3 (by rfl) ⟨15329, by rfl⟩) (B 30659 (by norm_num) ⟨15329, by rfl⟩ (by norm_num))
theorem R81761 : Reach 81761 := rs (se 2 (by rfl) ⟨30660, by rfl⟩) (B 61321 (by norm_num) ⟨30660, by rfl⟩ (by norm_num))
theorem R81765 : Reach 81765 := rs (se 4 (by rfl) ⟨7665, by rfl⟩) (B 15331 (by norm_num) ⟨7665, by rfl⟩ (by norm_num))
theorem R81769 : Reach 81769 := rs (se 2 (by rfl) ⟨30663, by rfl⟩) (B 61327 (by norm_num) ⟨30663, by rfl⟩ (by norm_num))
theorem R81773 : Reach 81773 := rs (se 3 (by rfl) ⟨15332, by rfl⟩) (B 30665 (by norm_num) ⟨15332, by rfl⟩ (by norm_num))
theorem R81777 : Reach 81777 := rs (se 2 (by rfl) ⟨30666, by rfl⟩) (B 61333 (by norm_num) ⟨30666, by rfl⟩ (by norm_num))
theorem R81781 : Reach 81781 := rs (se 5 (by rfl) ⟨3833, by rfl⟩) (B 7667 (by norm_num) ⟨3833, by rfl⟩ (by norm_num))
theorem R81785 : Reach 81785 := rs (se 2 (by rfl) ⟨30669, by rfl⟩) (B 61339 (by norm_num) ⟨30669, by rfl⟩ (by norm_num))
theorem R81789 : Reach 81789 := rs (se 3 (by rfl) ⟨15335, by rfl⟩) (B 30671 (by norm_num) ⟨15335, by rfl⟩ (by norm_num))
theorem R81793 : Reach 81793 := rs (se 2 (by rfl) ⟨30672, by rfl⟩) (B 61345 (by norm_num) ⟨30672, by rfl⟩ (by norm_num))
theorem R81797 : Reach 81797 := rs (se 4 (by rfl) ⟨7668, by rfl⟩) (B 15337 (by norm_num) ⟨7668, by rfl⟩ (by norm_num))
theorem R81801 : Reach 81801 := rs (se 2 (by rfl) ⟨30675, by rfl⟩) (B 61351 (by norm_num) ⟨30675, by rfl⟩ (by norm_num))
theorem R81805 : Reach 81805 := rs (se 3 (by rfl) ⟨15338, by rfl⟩) (B 30677 (by norm_num) ⟨15338, by rfl⟩ (by norm_num))
theorem R81809 : Reach 81809 := rs (se 2 (by rfl) ⟨30678, by rfl⟩) (B 61357 (by norm_num) ⟨30678, by rfl⟩ (by norm_num))
theorem R81813 : Reach 81813 := rs (se 6 (by rfl) ⟨1917, by rfl⟩) (B 3835 (by norm_num) ⟨1917, by rfl⟩ (by norm_num))
theorem R81817 : Reach 81817 := rs (se 2 (by rfl) ⟨30681, by rfl⟩) (B 61363 (by norm_num) ⟨30681, by rfl⟩ (by norm_num))
theorem R180125 : Reach 180125 := rs (se 3 (by rfl) ⟨33773, by rfl⟩) (B 67547 (by norm_num) ⟨33773, by rfl⟩ (by norm_num))
theorem R81821 : Reach 81821 := rs (se 3 (by rfl) ⟨15341, by rfl⟩) (B 30683 (by norm_num) ⟨15341, by rfl⟩ (by norm_num))
theorem R81825 : Reach 81825 := rs (se 2 (by rfl) ⟨30684, by rfl⟩) (B 61369 (by norm_num) ⟨30684, by rfl⟩ (by norm_num))
theorem R376741 : Reach 376741 := rs (se 4 (by rfl) ⟨35319, by rfl⟩) (B 70639 (by norm_num) ⟨35319, by rfl⟩ (by norm_num))
theorem R81829 : Reach 81829 := rs (se 4 (by rfl) ⟨7671, by rfl⟩) (B 15343 (by norm_num) ⟨7671, by rfl⟩ (by norm_num))
theorem R81833 : Reach 81833 := rs (se 2 (by rfl) ⟨30687, by rfl⟩) (B 61375 (by norm_num) ⟨30687, by rfl⟩ (by norm_num))
theorem R81837 : Reach 81837 := rs (se 3 (by rfl) ⟨15344, by rfl⟩) (B 30689 (by norm_num) ⟨15344, by rfl⟩ (by norm_num))
theorem R81841 : Reach 81841 := rs (se 2 (by rfl) ⟨30690, by rfl⟩) (B 61381 (by norm_num) ⟨30690, by rfl⟩ (by norm_num))
theorem R81845 : Reach 81845 := rs (se 5 (by rfl) ⟨3836, by rfl⟩) (B 7673 (by norm_num) ⟨3836, by rfl⟩ (by norm_num))
theorem R81849 : Reach 81849 := rs (se 2 (by rfl) ⟨30693, by rfl⟩) (B 61387 (by norm_num) ⟨30693, by rfl⟩ (by norm_num))
theorem R81853 : Reach 81853 := rs (se 3 (by rfl) ⟨15347, by rfl⟩) (B 30695 (by norm_num) ⟨15347, by rfl⟩ (by norm_num))
theorem R81857 : Reach 81857 := rs (se 2 (by rfl) ⟨30696, by rfl⟩) (B 61393 (by norm_num) ⟨30696, by rfl⟩ (by norm_num))
theorem R81861 : Reach 81861 := rs (se 4 (by rfl) ⟨7674, by rfl⟩) (B 15349 (by norm_num) ⟨7674, by rfl⟩ (by norm_num))
theorem R81865 : Reach 81865 := rs (se 2 (by rfl) ⟨30699, by rfl⟩) (B 61399 (by norm_num) ⟨30699, by rfl⟩ (by norm_num))
theorem R81869 : Reach 81869 := rs (se 3 (by rfl) ⟨15350, by rfl⟩) (B 30701 (by norm_num) ⟨15350, by rfl⟩ (by norm_num))
theorem R81873 : Reach 81873 := rs (se 2 (by rfl) ⟨30702, by rfl⟩) (B 61405 (by norm_num) ⟨30702, by rfl⟩ (by norm_num))
theorem R81877 : Reach 81877 := rs (se 7 (by rfl) ⟨959, by rfl⟩) (B 1919 (by norm_num) ⟨959, by rfl⟩ (by norm_num))
theorem R81881 : Reach 81881 := rs (se 2 (by rfl) ⟨30705, by rfl⟩) (B 61411 (by norm_num) ⟨30705, by rfl⟩ (by norm_num))
theorem R81885 : Reach 81885 := rs (se 3 (by rfl) ⟨15353, by rfl⟩) (B 30707 (by norm_num) ⟨15353, by rfl⟩ (by norm_num))
theorem R81889 : Reach 81889 := rs (se 2 (by rfl) ⟨30708, by rfl⟩) (B 61417 (by norm_num) ⟨30708, by rfl⟩ (by norm_num))
theorem R180197 : Reach 180197 := rs (se 4 (by rfl) ⟨16893, by rfl⟩) (B 33787 (by norm_num) ⟨16893, by rfl⟩ (by norm_num))
theorem R81893 : Reach 81893 := rs (se 4 (by rfl) ⟨7677, by rfl⟩) (B 15355 (by norm_num) ⟨7677, by rfl⟩ (by norm_num))
theorem R81897 : Reach 81897 := rs (se 2 (by rfl) ⟨30711, by rfl⟩) (B 61423 (by norm_num) ⟨30711, by rfl⟩ (by norm_num))
theorem R81901 : Reach 81901 := rs (se 3 (by rfl) ⟨15356, by rfl⟩) (B 30713 (by norm_num) ⟨15356, by rfl⟩ (by norm_num))
theorem R81905 : Reach 81905 := rs (se 2 (by rfl) ⟨30714, by rfl⟩) (B 61429 (by norm_num) ⟨30714, by rfl⟩ (by norm_num))
theorem R81909 : Reach 81909 := rs (se 5 (by rfl) ⟨3839, by rfl⟩) (B 7679 (by norm_num) ⟨3839, by rfl⟩ (by norm_num))
theorem R81913 : Reach 81913 := rs (se 2 (by rfl) ⟨30717, by rfl⟩) (B 61435 (by norm_num) ⟨30717, by rfl⟩ (by norm_num))
theorem R81917 : Reach 81917 := rs (se 3 (by rfl) ⟨15359, by rfl⟩) (B 30719 (by norm_num) ⟨15359, by rfl⟩ (by norm_num))
theorem R81921 : Reach 81921 := rs (se 2 (by rfl) ⟨30720, by rfl⟩) (B 61441 (by norm_num) ⟨30720, by rfl⟩ (by norm_num))
theorem R81925 : Reach 81925 := rs (se 4 (by rfl) ⟨7680, by rfl⟩) (B 15361 (by norm_num) ⟨7680, by rfl⟩ (by norm_num))
theorem R81929 : Reach 81929 := rs (se 2 (by rfl) ⟨30723, by rfl⟩) (B 61447 (by norm_num) ⟨30723, by rfl⟩ (by norm_num))
theorem R81933 : Reach 81933 := rs (se 3 (by rfl) ⟨15362, by rfl⟩) (B 30725 (by norm_num) ⟨15362, by rfl⟩ (by norm_num))
theorem R81937 : Reach 81937 := rs (se 2 (by rfl) ⟨30726, by rfl⟩) (B 61453 (by norm_num) ⟨30726, by rfl⟩ (by norm_num))
theorem R81941 : Reach 81941 := rs (se 6 (by rfl) ⟨1920, by rfl⟩) (B 3841 (by norm_num) ⟨1920, by rfl⟩ (by norm_num))
theorem R81945 : Reach 81945 := rs (se 2 (by rfl) ⟨30729, by rfl⟩) (B 61459 (by norm_num) ⟨30729, by rfl⟩ (by norm_num))
theorem R81949 : Reach 81949 := rs (se 3 (by rfl) ⟨15365, by rfl⟩) (B 30731 (by norm_num) ⟨15365, by rfl⟩ (by norm_num))
theorem R81953 : Reach 81953 := rs (se 2 (by rfl) ⟨30732, by rfl⟩) (B 61465 (by norm_num) ⟨30732, by rfl⟩ (by norm_num))
theorem R81957 : Reach 81957 := rs (se 4 (by rfl) ⟨7683, by rfl⟩) (B 15367 (by norm_num) ⟨7683, by rfl⟩ (by norm_num))
theorem R81961 : Reach 81961 := rs (se 2 (by rfl) ⟨30735, by rfl⟩) (B 61471 (by norm_num) ⟨30735, by rfl⟩ (by norm_num))
theorem R180269 : Reach 180269 := rs (se 3 (by rfl) ⟨33800, by rfl⟩) (B 67601 (by norm_num) ⟨33800, by rfl⟩ (by norm_num))
theorem R81965 : Reach 81965 := rs (se 3 (by rfl) ⟨15368, by rfl⟩) (B 30737 (by norm_num) ⟨15368, by rfl⟩ (by norm_num))
theorem R81969 : Reach 81969 := rs (se 2 (by rfl) ⟨30738, by rfl⟩) (B 61477 (by norm_num) ⟨30738, by rfl⟩ (by norm_num))
theorem R81973 : Reach 81973 := rs (se 5 (by rfl) ⟨3842, by rfl⟩) (B 7685 (by norm_num) ⟨3842, by rfl⟩ (by norm_num))
theorem R81977 : Reach 81977 := rs (se 2 (by rfl) ⟨30741, by rfl⟩) (B 61483 (by norm_num) ⟨30741, by rfl⟩ (by norm_num))
theorem R81981 : Reach 81981 := rs (se 3 (by rfl) ⟨15371, by rfl⟩) (B 30743 (by norm_num) ⟨15371, by rfl⟩ (by norm_num))
theorem R81985 : Reach 81985 := rs (se 2 (by rfl) ⟨30744, by rfl⟩) (B 61489 (by norm_num) ⟨30744, by rfl⟩ (by norm_num))
theorem R81989 : Reach 81989 := rs (se 4 (by rfl) ⟨7686, by rfl⟩) (B 15373 (by norm_num) ⟨7686, by rfl⟩ (by norm_num))
theorem R81993 : Reach 81993 := rs (se 2 (by rfl) ⟨30747, by rfl⟩) (B 61495 (by norm_num) ⟨30747, by rfl⟩ (by norm_num))
theorem R81997 : Reach 81997 := rs (se 3 (by rfl) ⟨15374, by rfl⟩) (B 30749 (by norm_num) ⟨15374, by rfl⟩ (by norm_num))
theorem R82001 : Reach 82001 := rs (se 2 (by rfl) ⟨30750, by rfl⟩) (B 61501 (by norm_num) ⟨30750, by rfl⟩ (by norm_num))
theorem R82005 : Reach 82005 := rs (se 8 (by rfl) ⟨480, by rfl⟩) (B 961 (by norm_num) ⟨480, by rfl⟩ (by norm_num))
theorem R82009 : Reach 82009 := rs (se 2 (by rfl) ⟨30753, by rfl⟩) (B 61507 (by norm_num) ⟨30753, by rfl⟩ (by norm_num))
theorem R82013 : Reach 82013 := rs (se 3 (by rfl) ⟨15377, by rfl⟩) (B 30755 (by norm_num) ⟨15377, by rfl⟩ (by norm_num))
theorem R82017 : Reach 82017 := rs (se 2 (by rfl) ⟨30756, by rfl⟩) (B 61513 (by norm_num) ⟨30756, by rfl⟩ (by norm_num))
theorem R82021 : Reach 82021 := rs (se 4 (by rfl) ⟨7689, by rfl⟩) (B 15379 (by norm_num) ⟨7689, by rfl⟩ (by norm_num))
theorem R82025 : Reach 82025 := rs (se 2 (by rfl) ⟨30759, by rfl⟩) (B 61519 (by norm_num) ⟨30759, by rfl⟩ (by norm_num))
theorem R82029 : Reach 82029 := rs (se 3 (by rfl) ⟨15380, by rfl⟩) (B 30761 (by norm_num) ⟨15380, by rfl⟩ (by norm_num))
theorem R82033 : Reach 82033 := rs (se 2 (by rfl) ⟨30762, by rfl⟩) (B 61525 (by norm_num) ⟨30762, by rfl⟩ (by norm_num))
theorem R180341 : Reach 180341 := rs (se 5 (by rfl) ⟨8453, by rfl⟩) (B 16907 (by norm_num) ⟨8453, by rfl⟩ (by norm_num))
theorem R82037 : Reach 82037 := rs (se 5 (by rfl) ⟨3845, by rfl⟩) (B 7691 (by norm_num) ⟨3845, by rfl⟩ (by norm_num))
theorem R82041 : Reach 82041 := rs (se 2 (by rfl) ⟨30765, by rfl⟩) (B 61531 (by norm_num) ⟨30765, by rfl⟩ (by norm_num))
theorem R82045 : Reach 82045 := rs (se 3 (by rfl) ⟨15383, by rfl⟩) (B 30767 (by norm_num) ⟨15383, by rfl⟩ (by norm_num))
theorem R82049 : Reach 82049 := rs (se 2 (by rfl) ⟨30768, by rfl⟩) (B 61537 (by norm_num) ⟨30768, by rfl⟩ (by norm_num))
theorem R82053 : Reach 82053 := rs (se 4 (by rfl) ⟨7692, by rfl⟩) (B 15385 (by norm_num) ⟨7692, by rfl⟩ (by norm_num))
theorem R82057 : Reach 82057 := rs (se 2 (by rfl) ⟨30771, by rfl⟩) (B 61543 (by norm_num) ⟨30771, by rfl⟩ (by norm_num))
theorem R82061 : Reach 82061 := rs (se 3 (by rfl) ⟨15386, by rfl⟩) (B 30773 (by norm_num) ⟨15386, by rfl⟩ (by norm_num))
theorem R82065 : Reach 82065 := rs (se 2 (by rfl) ⟨30774, by rfl⟩) (B 61549 (by norm_num) ⟨30774, by rfl⟩ (by norm_num))
theorem R82069 : Reach 82069 := rs (se 6 (by rfl) ⟨1923, by rfl⟩) (B 3847 (by norm_num) ⟨1923, by rfl⟩ (by norm_num))
theorem R1130645 : Reach 1130645 := rs (se 6 (by rfl) ⟨26499, by rfl⟩) (B 52999 (by norm_num) ⟨26499, by rfl⟩ (by norm_num))
theorem R82073 : Reach 82073 := rs (se 2 (by rfl) ⟨30777, by rfl⟩) (B 61555 (by norm_num) ⟨30777, by rfl⟩ (by norm_num))
theorem R82077 : Reach 82077 := rs (se 3 (by rfl) ⟨15389, by rfl⟩) (B 30779 (by norm_num) ⟨15389, by rfl⟩ (by norm_num))
theorem R82081 : Reach 82081 := rs (se 2 (by rfl) ⟨30780, by rfl⟩) (B 61561 (by norm_num) ⟨30780, by rfl⟩ (by norm_num))
theorem R82085 : Reach 82085 := rs (se 4 (by rfl) ⟨7695, by rfl⟩) (B 15391 (by norm_num) ⟨7695, by rfl⟩ (by norm_num))
theorem R278693 : Reach 278693 := rs (se 4 (by rfl) ⟨26127, by rfl⟩) (B 52255 (by norm_num) ⟨26127, by rfl⟩ (by norm_num))
theorem R82089 : Reach 82089 := rs (se 2 (by rfl) ⟨30783, by rfl⟩) (B 61567 (by norm_num) ⟨30783, by rfl⟩ (by norm_num))
theorem R82093 : Reach 82093 := rs (se 3 (by rfl) ⟨15392, by rfl⟩) (B 30785 (by norm_num) ⟨15392, by rfl⟩ (by norm_num))
theorem R82097 : Reach 82097 := rs (se 2 (by rfl) ⟨30786, by rfl⟩) (B 61573 (by norm_num) ⟨30786, by rfl⟩ (by norm_num))
theorem R82101 : Reach 82101 := rs (se 5 (by rfl) ⟨3848, by rfl⟩) (B 7697 (by norm_num) ⟨3848, by rfl⟩ (by norm_num))
theorem R82105 : Reach 82105 := rs (se 2 (by rfl) ⟨30789, by rfl⟩) (B 61579 (by norm_num) ⟨30789, by rfl⟩ (by norm_num))
theorem R180413 : Reach 180413 := rs (se 3 (by rfl) ⟨33827, by rfl⟩) (B 67655 (by norm_num) ⟨33827, by rfl⟩ (by norm_num))
theorem R82109 : Reach 82109 := rs (se 3 (by rfl) ⟨15395, by rfl⟩) (B 30791 (by norm_num) ⟨15395, by rfl⟩ (by norm_num))
theorem R82113 : Reach 82113 := rs (se 2 (by rfl) ⟨30792, by rfl⟩) (B 61585 (by norm_num) ⟨30792, by rfl⟩ (by norm_num))
theorem R82117 : Reach 82117 := rs (se 4 (by rfl) ⟨7698, by rfl⟩) (B 15397 (by norm_num) ⟨7698, by rfl⟩ (by norm_num))
theorem R82121 : Reach 82121 := rs (se 2 (by rfl) ⟨30795, by rfl⟩) (B 61591 (by norm_num) ⟨30795, by rfl⟩ (by norm_num))
theorem R82125 : Reach 82125 := rs (se 3 (by rfl) ⟨15398, by rfl⟩) (B 30797 (by norm_num) ⟨15398, by rfl⟩ (by norm_num))
theorem R82129 : Reach 82129 := rs (se 2 (by rfl) ⟨30798, by rfl⟩) (B 61597 (by norm_num) ⟨30798, by rfl⟩ (by norm_num))
theorem R82133 : Reach 82133 := rs (se 7 (by rfl) ⟨962, by rfl⟩) (B 1925 (by norm_num) ⟨962, by rfl⟩ (by norm_num))
theorem R82137 : Reach 82137 := rs (se 2 (by rfl) ⟨30801, by rfl⟩) (B 61603 (by norm_num) ⟨30801, by rfl⟩ (by norm_num))
theorem R82141 : Reach 82141 := rs (se 3 (by rfl) ⟨15401, by rfl⟩) (B 30803 (by norm_num) ⟨15401, by rfl⟩ (by norm_num))
theorem R82145 : Reach 82145 := rs (se 2 (by rfl) ⟨30804, by rfl⟩) (B 61609 (by norm_num) ⟨30804, by rfl⟩ (by norm_num))
theorem R82149 : Reach 82149 := rs (se 4 (by rfl) ⟨7701, by rfl⟩) (B 15403 (by norm_num) ⟨7701, by rfl⟩ (by norm_num))
theorem R82153 : Reach 82153 := rs (se 2 (by rfl) ⟨30807, by rfl⟩) (B 61615 (by norm_num) ⟨30807, by rfl⟩ (by norm_num))
theorem R82157 : Reach 82157 := rs (se 3 (by rfl) ⟨15404, by rfl⟩) (B 30809 (by norm_num) ⟨15404, by rfl⟩ (by norm_num))
theorem R82161 : Reach 82161 := rs (se 2 (by rfl) ⟨30810, by rfl⟩) (B 61621 (by norm_num) ⟨30810, by rfl⟩ (by norm_num))
theorem R82165 : Reach 82165 := rs (se 5 (by rfl) ⟨3851, by rfl⟩) (B 7703 (by norm_num) ⟨3851, by rfl⟩ (by norm_num))
theorem R82169 : Reach 82169 := rs (se 2 (by rfl) ⟨30813, by rfl⟩) (B 61627 (by norm_num) ⟨30813, by rfl⟩ (by norm_num))
theorem R82173 : Reach 82173 := rs (se 3 (by rfl) ⟨15407, by rfl⟩) (B 30815 (by norm_num) ⟨15407, by rfl⟩ (by norm_num))
theorem R82177 : Reach 82177 := rs (se 2 (by rfl) ⟨30816, by rfl⟩) (B 61633 (by norm_num) ⟨30816, by rfl⟩ (by norm_num))
theorem R180485 : Reach 180485 := rs (se 4 (by rfl) ⟨16920, by rfl⟩) (B 33841 (by norm_num) ⟨16920, by rfl⟩ (by norm_num))
theorem R114949 : Reach 114949 := rs (se 4 (by rfl) ⟨10776, by rfl⟩) (B 21553 (by norm_num) ⟨10776, by rfl⟩ (by norm_num))
theorem R82181 : Reach 82181 := rs (se 4 (by rfl) ⟨7704, by rfl⟩) (B 15409 (by norm_num) ⟨7704, by rfl⟩ (by norm_num))
theorem R82185 : Reach 82185 := rs (se 2 (by rfl) ⟨30819, by rfl⟩) (B 61639 (by norm_num) ⟨30819, by rfl⟩ (by norm_num))
theorem R82189 : Reach 82189 := rs (se 3 (by rfl) ⟨15410, by rfl⟩) (B 30821 (by norm_num) ⟨15410, by rfl⟩ (by norm_num))
theorem R82193 : Reach 82193 := rs (se 2 (by rfl) ⟨30822, by rfl⟩) (B 61645 (by norm_num) ⟨30822, by rfl⟩ (by norm_num))
theorem R82197 : Reach 82197 := rs (se 6 (by rfl) ⟨1926, by rfl⟩) (B 3853 (by norm_num) ⟨1926, by rfl⟩ (by norm_num))
theorem R82201 : Reach 82201 := rs (se 2 (by rfl) ⟨30825, by rfl⟩) (B 61651 (by norm_num) ⟨30825, by rfl⟩ (by norm_num))
theorem R82205 : Reach 82205 := rs (se 3 (by rfl) ⟨15413, by rfl⟩) (B 30827 (by norm_num) ⟨15413, by rfl⟩ (by norm_num))
theorem R82209 : Reach 82209 := rs (se 2 (by rfl) ⟨30828, by rfl⟩) (B 61657 (by norm_num) ⟨30828, by rfl⟩ (by norm_num))
theorem R82213 : Reach 82213 := rs (se 4 (by rfl) ⟨7707, by rfl⟩) (B 15415 (by norm_num) ⟨7707, by rfl⟩ (by norm_num))
theorem R82217 : Reach 82217 := rs (se 2 (by rfl) ⟨30831, by rfl⟩) (B 61663 (by norm_num) ⟨30831, by rfl⟩ (by norm_num))
theorem R82221 : Reach 82221 := rs (se 3 (by rfl) ⟨15416, by rfl⟩) (B 30833 (by norm_num) ⟨15416, by rfl⟩ (by norm_num))
theorem R82225 : Reach 82225 := rs (se 2 (by rfl) ⟨30834, by rfl⟩) (B 61669 (by norm_num) ⟨30834, by rfl⟩ (by norm_num))
theorem R82229 : Reach 82229 := rs (se 5 (by rfl) ⟨3854, by rfl⟩) (B 7709 (by norm_num) ⟨3854, by rfl⟩ (by norm_num))
theorem R82233 : Reach 82233 := rs (se 2 (by rfl) ⟨30837, by rfl⟩) (B 61675 (by norm_num) ⟨30837, by rfl⟩ (by norm_num))
theorem R82237 : Reach 82237 := rs (se 3 (by rfl) ⟨15419, by rfl⟩) (B 30839 (by norm_num) ⟨15419, by rfl⟩ (by norm_num))
theorem R82241 : Reach 82241 := rs (se 2 (by rfl) ⟨30840, by rfl⟩) (B 61681 (by norm_num) ⟨30840, by rfl⟩ (by norm_num))
theorem R82245 : Reach 82245 := rs (se 4 (by rfl) ⟨7710, by rfl⟩) (B 15421 (by norm_num) ⟨7710, by rfl⟩ (by norm_num))
theorem R82249 : Reach 82249 := rs (se 2 (by rfl) ⟨30843, by rfl⟩) (B 61687 (by norm_num) ⟨30843, by rfl⟩ (by norm_num))
theorem R180557 : Reach 180557 := rs (se 3 (by rfl) ⟨33854, by rfl⟩) (B 67709 (by norm_num) ⟨33854, by rfl⟩ (by norm_num))
theorem R82253 : Reach 82253 := rs (se 3 (by rfl) ⟨15422, by rfl⟩) (B 30845 (by norm_num) ⟨15422, by rfl⟩ (by norm_num))
theorem R82257 : Reach 82257 := rs (se 2 (by rfl) ⟨30846, by rfl⟩) (B 61693 (by norm_num) ⟨30846, by rfl⟩ (by norm_num))
theorem R82261 : Reach 82261 := rs (se 10 (by rfl) ⟨120, by rfl⟩) (B 241 (by norm_num) ⟨120, by rfl⟩ (by norm_num))
theorem R82265 : Reach 82265 := rs (se 2 (by rfl) ⟨30849, by rfl⟩) (B 61699 (by norm_num) ⟨30849, by rfl⟩ (by norm_num))
theorem R82269 : Reach 82269 := rs (se 3 (by rfl) ⟨15425, by rfl⟩) (B 30851 (by norm_num) ⟨15425, by rfl⟩ (by norm_num))
theorem R82273 : Reach 82273 := rs (se 2 (by rfl) ⟨30852, by rfl⟩) (B 61705 (by norm_num) ⟨30852, by rfl⟩ (by norm_num))
theorem R82277 : Reach 82277 := rs (se 4 (by rfl) ⟨7713, by rfl⟩) (B 15427 (by norm_num) ⟨7713, by rfl⟩ (by norm_num))
theorem R82281 : Reach 82281 := rs (se 2 (by rfl) ⟨30855, by rfl⟩) (B 61711 (by norm_num) ⟨30855, by rfl⟩ (by norm_num))
theorem R82285 : Reach 82285 := rs (se 3 (by rfl) ⟨15428, by rfl⟩) (B 30857 (by norm_num) ⟨15428, by rfl⟩ (by norm_num))
theorem R82289 : Reach 82289 := rs (se 2 (by rfl) ⟨30858, by rfl⟩) (B 61717 (by norm_num) ⟨30858, by rfl⟩ (by norm_num))
theorem R82293 : Reach 82293 := rs (se 5 (by rfl) ⟨3857, by rfl⟩) (B 7715 (by norm_num) ⟨3857, by rfl⟩ (by norm_num))
theorem R82297 : Reach 82297 := rs (se 2 (by rfl) ⟨30861, by rfl⟩) (B 61723 (by norm_num) ⟨30861, by rfl⟩ (by norm_num))
theorem R82301 : Reach 82301 := rs (se 3 (by rfl) ⟨15431, by rfl⟩) (B 30863 (by norm_num) ⟨15431, by rfl⟩ (by norm_num))
theorem R82305 : Reach 82305 := rs (se 2 (by rfl) ⟨30864, by rfl⟩) (B 61729 (by norm_num) ⟨30864, by rfl⟩ (by norm_num))
theorem R82309 : Reach 82309 := rs (se 4 (by rfl) ⟨7716, by rfl⟩) (B 15433 (by norm_num) ⟨7716, by rfl⟩ (by norm_num))
theorem R82313 : Reach 82313 := rs (se 2 (by rfl) ⟨30867, by rfl⟩) (B 61735 (by norm_num) ⟨30867, by rfl⟩ (by norm_num))
theorem R82317 : Reach 82317 := rs (se 3 (by rfl) ⟨15434, by rfl⟩) (B 30869 (by norm_num) ⟨15434, by rfl⟩ (by norm_num))
theorem R82321 : Reach 82321 := rs (se 2 (by rfl) ⟨30870, by rfl⟩) (B 61741 (by norm_num) ⟨30870, by rfl⟩ (by norm_num))
theorem R180629 : Reach 180629 := rs (se 6 (by rfl) ⟨4233, by rfl⟩) (B 8467 (by norm_num) ⟨4233, by rfl⟩ (by norm_num))
theorem R82325 : Reach 82325 := rs (se 6 (by rfl) ⟨1929, by rfl⟩) (B 3859 (by norm_num) ⟨1929, by rfl⟩ (by norm_num))
theorem R82329 : Reach 82329 := rs (se 2 (by rfl) ⟨30873, by rfl⟩) (B 61747 (by norm_num) ⟨30873, by rfl⟩ (by norm_num))
theorem R82333 : Reach 82333 := rs (se 3 (by rfl) ⟨15437, by rfl⟩) (B 30875 (by norm_num) ⟨15437, by rfl⟩ (by norm_num))
theorem R82337 : Reach 82337 := rs (se 2 (by rfl) ⟨30876, by rfl⟩) (B 61753 (by norm_num) ⟨30876, by rfl⟩ (by norm_num))
theorem R410021 : Reach 410021 := rs (se 4 (by rfl) ⟨38439, by rfl⟩) (B 76879 (by norm_num) ⟨38439, by rfl⟩ (by norm_num))
theorem R82341 : Reach 82341 := rs (se 4 (by rfl) ⟨7719, by rfl⟩) (B 15439 (by norm_num) ⟨7719, by rfl⟩ (by norm_num))
theorem R82345 : Reach 82345 := rs (se 2 (by rfl) ⟨30879, by rfl⟩) (B 61759 (by norm_num) ⟨30879, by rfl⟩ (by norm_num))
theorem R82349 : Reach 82349 := rs (se 3 (by rfl) ⟨15440, by rfl⟩) (B 30881 (by norm_num) ⟨15440, by rfl⟩ (by norm_num))
theorem R82353 : Reach 82353 := rs (se 2 (by rfl) ⟨30882, by rfl⟩) (B 61765 (by norm_num) ⟨30882, by rfl⟩ (by norm_num))
theorem R82357 : Reach 82357 := rs (se 5 (by rfl) ⟨3860, by rfl⟩) (B 7721 (by norm_num) ⟨3860, by rfl⟩ (by norm_num))
theorem R82361 : Reach 82361 := rs (se 2 (by rfl) ⟨30885, by rfl⟩) (B 61771 (by norm_num) ⟨30885, by rfl⟩ (by norm_num))
theorem R82365 : Reach 82365 := rs (se 3 (by rfl) ⟨15443, by rfl⟩) (B 30887 (by norm_num) ⟨15443, by rfl⟩ (by norm_num))
theorem R82369 : Reach 82369 := rs (se 2 (by rfl) ⟨30888, by rfl⟩) (B 61777 (by norm_num) ⟨30888, by rfl⟩ (by norm_num))
theorem R82373 : Reach 82373 := rs (se 4 (by rfl) ⟨7722, by rfl⟩) (B 15445 (by norm_num) ⟨7722, by rfl⟩ (by norm_num))
theorem R82377 : Reach 82377 := rs (se 2 (by rfl) ⟨30891, by rfl⟩) (B 61783 (by norm_num) ⟨30891, by rfl⟩ (by norm_num))
theorem R82381 : Reach 82381 := rs (se 3 (by rfl) ⟨15446, by rfl⟩) (B 30893 (by norm_num) ⟨15446, by rfl⟩ (by norm_num))
theorem R82385 : Reach 82385 := rs (se 2 (by rfl) ⟨30894, by rfl⟩) (B 61789 (by norm_num) ⟨30894, by rfl⟩ (by norm_num))
theorem R82389 : Reach 82389 := rs (se 7 (by rfl) ⟨965, by rfl⟩) (B 1931 (by norm_num) ⟨965, by rfl⟩ (by norm_num))
theorem R82393 : Reach 82393 := rs (se 2 (by rfl) ⟨30897, by rfl⟩) (B 61795 (by norm_num) ⟨30897, by rfl⟩ (by norm_num))
theorem R180701 : Reach 180701 := rs (se 3 (by rfl) ⟨33881, by rfl⟩) (B 67763 (by norm_num) ⟨33881, by rfl⟩ (by norm_num))
theorem R82397 : Reach 82397 := rs (se 3 (by rfl) ⟨15449, by rfl⟩) (B 30899 (by norm_num) ⟨15449, by rfl⟩ (by norm_num))
theorem R82401 : Reach 82401 := rs (se 2 (by rfl) ⟨30900, by rfl⟩) (B 61801 (by norm_num) ⟨30900, by rfl⟩ (by norm_num))
theorem R82405 : Reach 82405 := rs (se 4 (by rfl) ⟨7725, by rfl⟩) (B 15451 (by norm_num) ⟨7725, by rfl⟩ (by norm_num))
theorem R82409 : Reach 82409 := rs (se 2 (by rfl) ⟨30903, by rfl⟩) (B 61807 (by norm_num) ⟨30903, by rfl⟩ (by norm_num))
theorem R82413 : Reach 82413 := rs (se 3 (by rfl) ⟨15452, by rfl⟩) (B 30905 (by norm_num) ⟨15452, by rfl⟩ (by norm_num))
theorem R82417 : Reach 82417 := rs (se 2 (by rfl) ⟨30906, by rfl⟩) (B 61813 (by norm_num) ⟨30906, by rfl⟩ (by norm_num))
theorem R82421 : Reach 82421 := rs (se 5 (by rfl) ⟨3863, by rfl⟩) (B 7727 (by norm_num) ⟨3863, by rfl⟩ (by norm_num))
theorem R82425 : Reach 82425 := rs (se 2 (by rfl) ⟨30909, by rfl⟩) (B 61819 (by norm_num) ⟨30909, by rfl⟩ (by norm_num))
theorem R82429 : Reach 82429 := rs (se 3 (by rfl) ⟨15455, by rfl⟩) (B 30911 (by norm_num) ⟨15455, by rfl⟩ (by norm_num))
theorem R82433 : Reach 82433 := rs (se 2 (by rfl) ⟨30912, by rfl⟩) (B 61825 (by norm_num) ⟨30912, by rfl⟩ (by norm_num))
theorem R82437 : Reach 82437 := rs (se 4 (by rfl) ⟨7728, by rfl⟩) (B 15457 (by norm_num) ⟨7728, by rfl⟩ (by norm_num))
theorem R82441 : Reach 82441 := rs (se 2 (by rfl) ⟨30915, by rfl⟩) (B 61831 (by norm_num) ⟨30915, by rfl⟩ (by norm_num))
theorem R82445 : Reach 82445 := rs (se 3 (by rfl) ⟨15458, by rfl⟩) (B 30917 (by norm_num) ⟨15458, by rfl⟩ (by norm_num))
theorem R82449 : Reach 82449 := rs (se 2 (by rfl) ⟨30918, by rfl⟩) (B 61837 (by norm_num) ⟨30918, by rfl⟩ (by norm_num))
theorem R82453 : Reach 82453 := rs (se 6 (by rfl) ⟨1932, by rfl⟩) (B 3865 (by norm_num) ⟨1932, by rfl⟩ (by norm_num))
theorem R82457 : Reach 82457 := rs (se 2 (by rfl) ⟨30921, by rfl⟩) (B 61843 (by norm_num) ⟨30921, by rfl⟩ (by norm_num))
theorem R82461 : Reach 82461 := rs (se 3 (by rfl) ⟨15461, by rfl⟩) (B 30923 (by norm_num) ⟨15461, by rfl⟩ (by norm_num))
theorem R82465 : Reach 82465 := rs (se 2 (by rfl) ⟨30924, by rfl⟩) (B 61849 (by norm_num) ⟨30924, by rfl⟩ (by norm_num))
theorem R180773 : Reach 180773 := rs (se 4 (by rfl) ⟨16947, by rfl⟩) (B 33895 (by norm_num) ⟨16947, by rfl⟩ (by norm_num))
theorem R82469 : Reach 82469 := rs (se 4 (by rfl) ⟨7731, by rfl⟩) (B 15463 (by norm_num) ⟨7731, by rfl⟩ (by norm_num))
theorem R82473 : Reach 82473 := rs (se 2 (by rfl) ⟨30927, by rfl⟩) (B 61855 (by norm_num) ⟨30927, by rfl⟩ (by norm_num))
theorem R82477 : Reach 82477 := rs (se 3 (by rfl) ⟨15464, by rfl⟩) (B 30929 (by norm_num) ⟨15464, by rfl⟩ (by norm_num))
theorem R82481 : Reach 82481 := rs (se 2 (by rfl) ⟨30930, by rfl⟩) (B 61861 (by norm_num) ⟨30930, by rfl⟩ (by norm_num))
theorem R82485 : Reach 82485 := rs (se 5 (by rfl) ⟨3866, by rfl⟩) (B 7733 (by norm_num) ⟨3866, by rfl⟩ (by norm_num))
theorem R82489 : Reach 82489 := rs (se 2 (by rfl) ⟨30933, by rfl⟩) (B 61867 (by norm_num) ⟨30933, by rfl⟩ (by norm_num))
theorem R82493 : Reach 82493 := rs (se 3 (by rfl) ⟨15467, by rfl⟩) (B 30935 (by norm_num) ⟨15467, by rfl⟩ (by norm_num))
theorem R82497 : Reach 82497 := rs (se 2 (by rfl) ⟨30936, by rfl⟩) (B 61873 (by norm_num) ⟨30936, by rfl⟩ (by norm_num))
theorem R82501 : Reach 82501 := rs (se 4 (by rfl) ⟨7734, by rfl⟩) (B 15469 (by norm_num) ⟨7734, by rfl⟩ (by norm_num))
theorem R82505 : Reach 82505 := rs (se 2 (by rfl) ⟨30939, by rfl⟩) (B 61879 (by norm_num) ⟨30939, by rfl⟩ (by norm_num))
theorem R82509 : Reach 82509 := rs (se 3 (by rfl) ⟨15470, by rfl⟩) (B 30941 (by norm_num) ⟨15470, by rfl⟩ (by norm_num))
theorem R82513 : Reach 82513 := rs (se 2 (by rfl) ⟨30942, by rfl⟩) (B 61885 (by norm_num) ⟨30942, by rfl⟩ (by norm_num))
theorem R115285 : Reach 115285 := rs (se 8 (by rfl) ⟨675, by rfl⟩) (B 1351 (by norm_num) ⟨675, by rfl⟩ (by norm_num))
theorem R82517 : Reach 82517 := rs (se 8 (by rfl) ⟨483, by rfl⟩) (B 967 (by norm_num) ⟨483, by rfl⟩ (by norm_num))
theorem R279125 : Reach 279125 := rs (se 8 (by rfl) ⟨1635, by rfl⟩) (B 3271 (by norm_num) ⟨1635, by rfl⟩ (by norm_num))
theorem R82521 : Reach 82521 := rs (se 2 (by rfl) ⟨30945, by rfl⟩) (B 61891 (by norm_num) ⟨30945, by rfl⟩ (by norm_num))
theorem R82525 : Reach 82525 := rs (se 3 (by rfl) ⟨15473, by rfl⟩) (B 30947 (by norm_num) ⟨15473, by rfl⟩ (by norm_num))
theorem R82529 : Reach 82529 := rs (se 2 (by rfl) ⟨30948, by rfl⟩) (B 61897 (by norm_num) ⟨30948, by rfl⟩ (by norm_num))
theorem R82533 : Reach 82533 := rs (se 4 (by rfl) ⟨7737, by rfl⟩) (B 15475 (by norm_num) ⟨7737, by rfl⟩ (by norm_num))
theorem R82537 : Reach 82537 := rs (se 2 (by rfl) ⟨30951, by rfl⟩) (B 61903 (by norm_num) ⟨30951, by rfl⟩ (by norm_num))
theorem R180845 : Reach 180845 := rs (se 3 (by rfl) ⟨33908, by rfl⟩) (B 67817 (by norm_num) ⟨33908, by rfl⟩ (by norm_num))
theorem R82541 : Reach 82541 := rs (se 3 (by rfl) ⟨15476, by rfl⟩) (B 30953 (by norm_num) ⟨15476, by rfl⟩ (by norm_num))
theorem R82545 : Reach 82545 := rs (se 2 (by rfl) ⟨30954, by rfl⟩) (B 61909 (by norm_num) ⟨30954, by rfl⟩ (by norm_num))
theorem R82549 : Reach 82549 := rs (se 5 (by rfl) ⟨3869, by rfl⟩) (B 7739 (by norm_num) ⟨3869, by rfl⟩ (by norm_num))
theorem R82553 : Reach 82553 := rs (se 2 (by rfl) ⟨30957, by rfl⟩) (B 61915 (by norm_num) ⟨30957, by rfl⟩ (by norm_num))
theorem R82557 : Reach 82557 := rs (se 3 (by rfl) ⟨15479, by rfl⟩) (B 30959 (by norm_num) ⟨15479, by rfl⟩ (by norm_num))
theorem R82561 : Reach 82561 := rs (se 2 (by rfl) ⟨30960, by rfl⟩) (B 61921 (by norm_num) ⟨30960, by rfl⟩ (by norm_num))
theorem R82565 : Reach 82565 := rs (se 4 (by rfl) ⟨7740, by rfl⟩) (B 15481 (by norm_num) ⟨7740, by rfl⟩ (by norm_num))
theorem R82569 : Reach 82569 := rs (se 2 (by rfl) ⟨30963, by rfl⟩) (B 61927 (by norm_num) ⟨30963, by rfl⟩ (by norm_num))
theorem R82573 : Reach 82573 := rs (se 3 (by rfl) ⟨15482, by rfl⟩) (B 30965 (by norm_num) ⟨15482, by rfl⟩ (by norm_num))
theorem R82577 : Reach 82577 := rs (se 2 (by rfl) ⟨30966, by rfl⟩) (B 61933 (by norm_num) ⟨30966, by rfl⟩ (by norm_num))
theorem R82581 : Reach 82581 := rs (se 6 (by rfl) ⟨1935, by rfl⟩) (B 3871 (by norm_num) ⟨1935, by rfl⟩ (by norm_num))
theorem R82585 : Reach 82585 := rs (se 2 (by rfl) ⟨30969, by rfl⟩) (B 61939 (by norm_num) ⟨30969, by rfl⟩ (by norm_num))
theorem R82589 : Reach 82589 := rs (se 3 (by rfl) ⟨15485, by rfl⟩) (B 30971 (by norm_num) ⟨15485, by rfl⟩ (by norm_num))
theorem R82593 : Reach 82593 := rs (se 2 (by rfl) ⟨30972, by rfl⟩) (B 61945 (by norm_num) ⟨30972, by rfl⟩ (by norm_num))
theorem R82597 : Reach 82597 := rs (se 4 (by rfl) ⟨7743, by rfl⟩) (B 15487 (by norm_num) ⟨7743, by rfl⟩ (by norm_num))
theorem R82601 : Reach 82601 := rs (se 2 (by rfl) ⟨30975, by rfl⟩) (B 61951 (by norm_num) ⟨30975, by rfl⟩ (by norm_num))
theorem R82605 : Reach 82605 := rs (se 3 (by rfl) ⟨15488, by rfl⟩) (B 30977 (by norm_num) ⟨15488, by rfl⟩ (by norm_num))
theorem R82609 : Reach 82609 := rs (se 2 (by rfl) ⟨30978, by rfl⟩) (B 61957 (by norm_num) ⟨30978, by rfl⟩ (by norm_num))
theorem R180917 : Reach 180917 := rs (se 5 (by rfl) ⟨8480, by rfl⟩) (B 16961 (by norm_num) ⟨8480, by rfl⟩ (by norm_num))
theorem R705205 : Reach 705205 := rs (se 5 (by rfl) ⟨33056, by rfl⟩) (B 66113 (by norm_num) ⟨33056, by rfl⟩ (by norm_num))
theorem R82613 : Reach 82613 := rs (se 5 (by rfl) ⟨3872, by rfl⟩) (B 7745 (by norm_num) ⟨3872, by rfl⟩ (by norm_num))
theorem R82617 : Reach 82617 := rs (se 2 (by rfl) ⟨30981, by rfl⟩) (B 61963 (by norm_num) ⟨30981, by rfl⟩ (by norm_num))
theorem R82621 : Reach 82621 := rs (se 3 (by rfl) ⟨15491, by rfl⟩) (B 30983 (by norm_num) ⟨15491, by rfl⟩ (by norm_num))
theorem R82625 : Reach 82625 := rs (se 2 (by rfl) ⟨30984, by rfl⟩) (B 61969 (by norm_num) ⟨30984, by rfl⟩ (by norm_num))
theorem R82629 : Reach 82629 := rs (se 4 (by rfl) ⟨7746, by rfl⟩) (B 15493 (by norm_num) ⟨7746, by rfl⟩ (by norm_num))
theorem R82633 : Reach 82633 := rs (se 2 (by rfl) ⟨30987, by rfl⟩) (B 61975 (by norm_num) ⟨30987, by rfl⟩ (by norm_num))
theorem R82637 : Reach 82637 := rs (se 3 (by rfl) ⟨15494, by rfl⟩) (B 30989 (by norm_num) ⟨15494, by rfl⟩ (by norm_num))
theorem R82641 : Reach 82641 := rs (se 2 (by rfl) ⟨30990, by rfl⟩) (B 61981 (by norm_num) ⟨30990, by rfl⟩ (by norm_num))
theorem R82645 : Reach 82645 := rs (se 7 (by rfl) ⟨968, by rfl⟩) (B 1937 (by norm_num) ⟨968, by rfl⟩ (by norm_num))
theorem R82649 : Reach 82649 := rs (se 2 (by rfl) ⟨30993, by rfl⟩) (B 61987 (by norm_num) ⟨30993, by rfl⟩ (by norm_num))
theorem R82653 : Reach 82653 := rs (se 3 (by rfl) ⟨15497, by rfl⟩) (B 30995 (by norm_num) ⟨15497, by rfl⟩ (by norm_num))
theorem R82657 : Reach 82657 := rs (se 2 (by rfl) ⟨30996, by rfl⟩) (B 61993 (by norm_num) ⟨30996, by rfl⟩ (by norm_num))
theorem R82661 : Reach 82661 := rs (se 4 (by rfl) ⟨7749, by rfl⟩) (B 15499 (by norm_num) ⟨7749, by rfl⟩ (by norm_num))
theorem R82665 : Reach 82665 := rs (se 2 (by rfl) ⟨30999, by rfl⟩) (B 61999 (by norm_num) ⟨30999, by rfl⟩ (by norm_num))
theorem R82669 : Reach 82669 := rs (se 3 (by rfl) ⟨15500, by rfl⟩) (B 31001 (by norm_num) ⟨15500, by rfl⟩ (by norm_num))
theorem R82673 : Reach 82673 := rs (se 2 (by rfl) ⟨31002, by rfl⟩) (B 62005 (by norm_num) ⟨31002, by rfl⟩ (by norm_num))
theorem R82677 : Reach 82677 := rs (se 5 (by rfl) ⟨3875, by rfl⟩) (B 7751 (by norm_num) ⟨3875, by rfl⟩ (by norm_num))
theorem R82681 : Reach 82681 := rs (se 2 (by rfl) ⟨31005, by rfl⟩) (B 62011 (by norm_num) ⟨31005, by rfl⟩ (by norm_num))
theorem R180989 : Reach 180989 := rs (se 3 (by rfl) ⟨33935, by rfl⟩) (B 67871 (by norm_num) ⟨33935, by rfl⟩ (by norm_num))
theorem R82685 : Reach 82685 := rs (se 3 (by rfl) ⟨15503, by rfl⟩) (B 31007 (by norm_num) ⟨15503, by rfl⟩ (by norm_num))
theorem R82689 : Reach 82689 := rs (se 2 (by rfl) ⟨31008, by rfl⟩) (B 62017 (by norm_num) ⟨31008, by rfl⟩ (by norm_num))
theorem R82693 : Reach 82693 := rs (se 4 (by rfl) ⟨7752, by rfl⟩) (B 15505 (by norm_num) ⟨7752, by rfl⟩ (by norm_num))
theorem R82697 : Reach 82697 := rs (se 2 (by rfl) ⟨31011, by rfl⟩) (B 62023 (by norm_num) ⟨31011, by rfl⟩ (by norm_num))
theorem R82701 : Reach 82701 := rs (se 3 (by rfl) ⟨15506, by rfl⟩) (B 31013 (by norm_num) ⟨15506, by rfl⟩ (by norm_num))
theorem R82705 : Reach 82705 := rs (se 2 (by rfl) ⟨31014, by rfl⟩) (B 62029 (by norm_num) ⟨31014, by rfl⟩ (by norm_num))
theorem R82709 : Reach 82709 := rs (se 6 (by rfl) ⟨1938, by rfl⟩) (B 3877 (by norm_num) ⟨1938, by rfl⟩ (by norm_num))
theorem R82713 : Reach 82713 := rs (se 2 (by rfl) ⟨31017, by rfl⟩) (B 62035 (by norm_num) ⟨31017, by rfl⟩ (by norm_num))
theorem R82717 : Reach 82717 := rs (se 3 (by rfl) ⟨15509, by rfl⟩) (B 31019 (by norm_num) ⟨15509, by rfl⟩ (by norm_num))
theorem R82721 : Reach 82721 := rs (se 2 (by rfl) ⟨31020, by rfl⟩) (B 62041 (by norm_num) ⟨31020, by rfl⟩ (by norm_num))
theorem R82725 : Reach 82725 := rs (se 4 (by rfl) ⟨7755, by rfl⟩) (B 15511 (by norm_num) ⟨7755, by rfl⟩ (by norm_num))
theorem R82729 : Reach 82729 := rs (se 2 (by rfl) ⟨31023, by rfl⟩) (B 62047 (by norm_num) ⟨31023, by rfl⟩ (by norm_num))
theorem R115501 : Reach 115501 := rs (se 3 (by rfl) ⟨21656, by rfl⟩) (B 43313 (by norm_num) ⟨21656, by rfl⟩ (by norm_num))
theorem R82733 : Reach 82733 := rs (se 3 (by rfl) ⟨15512, by rfl⟩) (B 31025 (by norm_num) ⟨15512, by rfl⟩ (by norm_num))
theorem R82737 : Reach 82737 := rs (se 2 (by rfl) ⟨31026, by rfl⟩) (B 62053 (by norm_num) ⟨31026, by rfl⟩ (by norm_num))
theorem R82741 : Reach 82741 := rs (se 5 (by rfl) ⟨3878, by rfl⟩) (B 7757 (by norm_num) ⟨3878, by rfl⟩ (by norm_num))
theorem R82745 : Reach 82745 := rs (se 2 (by rfl) ⟨31029, by rfl⟩) (B 62059 (by norm_num) ⟨31029, by rfl⟩ (by norm_num))
theorem R82749 : Reach 82749 := rs (se 3 (by rfl) ⟨15515, by rfl⟩) (B 31031 (by norm_num) ⟨15515, by rfl⟩ (by norm_num))
theorem R82753 : Reach 82753 := rs (se 2 (by rfl) ⟨31032, by rfl⟩) (B 62065 (by norm_num) ⟨31032, by rfl⟩ (by norm_num))
theorem R181061 : Reach 181061 := rs (se 4 (by rfl) ⟨16974, by rfl⟩) (B 33949 (by norm_num) ⟨16974, by rfl⟩ (by norm_num))
theorem R312133 : Reach 312133 := rs (se 4 (by rfl) ⟨29262, by rfl⟩) (B 58525 (by norm_num) ⟨29262, by rfl⟩ (by norm_num))
theorem R82757 : Reach 82757 := rs (se 4 (by rfl) ⟨7758, by rfl⟩) (B 15517 (by norm_num) ⟨7758, by rfl⟩ (by norm_num))
theorem R82761 : Reach 82761 := rs (se 2 (by rfl) ⟨31035, by rfl⟩) (B 62071 (by norm_num) ⟨31035, by rfl⟩ (by norm_num))
theorem R82765 : Reach 82765 := rs (se 3 (by rfl) ⟨15518, by rfl⟩) (B 31037 (by norm_num) ⟨15518, by rfl⟩ (by norm_num))
theorem R82769 : Reach 82769 := rs (se 2 (by rfl) ⟨31038, by rfl⟩) (B 62077 (by norm_num) ⟨31038, by rfl⟩ (by norm_num))
theorem R82773 : Reach 82773 := rs (se 9 (by rfl) ⟨242, by rfl⟩) (B 485 (by norm_num) ⟨242, by rfl⟩ (by norm_num))
theorem R82777 : Reach 82777 := rs (se 2 (by rfl) ⟨31041, by rfl⟩) (B 62083 (by norm_num) ⟨31041, by rfl⟩ (by norm_num))
theorem R82781 : Reach 82781 := rs (se 3 (by rfl) ⟨15521, by rfl⟩) (B 31043 (by norm_num) ⟨15521, by rfl⟩ (by norm_num))
theorem R82785 : Reach 82785 := rs (se 2 (by rfl) ⟨31044, by rfl⟩) (B 62089 (by norm_num) ⟨31044, by rfl⟩ (by norm_num))
theorem R82789 : Reach 82789 := rs (se 4 (by rfl) ⟨7761, by rfl⟩) (B 15523 (by norm_num) ⟨7761, by rfl⟩ (by norm_num))
theorem R82793 : Reach 82793 := rs (se 2 (by rfl) ⟨31047, by rfl⟩) (B 62095 (by norm_num) ⟨31047, by rfl⟩ (by norm_num))
theorem R82797 : Reach 82797 := rs (se 3 (by rfl) ⟨15524, by rfl⟩) (B 31049 (by norm_num) ⟨15524, by rfl⟩ (by norm_num))
theorem R82801 : Reach 82801 := rs (se 2 (by rfl) ⟨31050, by rfl⟩) (B 62101 (by norm_num) ⟨31050, by rfl⟩ (by norm_num))
theorem R82805 : Reach 82805 := rs (se 5 (by rfl) ⟨3881, by rfl⟩) (B 7763 (by norm_num) ⟨3881, by rfl⟩ (by norm_num))
theorem R82809 : Reach 82809 := rs (se 2 (by rfl) ⟨31053, by rfl⟩) (B 62107 (by norm_num) ⟨31053, by rfl⟩ (by norm_num))
theorem R82813 : Reach 82813 := rs (se 3 (by rfl) ⟨15527, by rfl⟩) (B 31055 (by norm_num) ⟨15527, by rfl⟩ (by norm_num))
theorem R82817 : Reach 82817 := rs (se 2 (by rfl) ⟨31056, by rfl⟩) (B 62113 (by norm_num) ⟨31056, by rfl⟩ (by norm_num))
theorem R82821 : Reach 82821 := rs (se 4 (by rfl) ⟨7764, by rfl⟩) (B 15529 (by norm_num) ⟨7764, by rfl⟩ (by norm_num))
theorem R82825 : Reach 82825 := rs (se 2 (by rfl) ⟨31059, by rfl⟩) (B 62119 (by norm_num) ⟨31059, by rfl⟩ (by norm_num))
theorem R181133 : Reach 181133 := rs (se 3 (by rfl) ⟨33962, by rfl⟩) (B 67925 (by norm_num) ⟨33962, by rfl⟩ (by norm_num))
theorem R82829 : Reach 82829 := rs (se 3 (by rfl) ⟨15530, by rfl⟩) (B 31061 (by norm_num) ⟨15530, by rfl⟩ (by norm_num))
theorem R82833 : Reach 82833 := rs (se 2 (by rfl) ⟨31062, by rfl⟩) (B 62125 (by norm_num) ⟨31062, by rfl⟩ (by norm_num))
theorem R148373 : Reach 148373 := rs (se 6 (by rfl) ⟨3477, by rfl⟩) (B 6955 (by norm_num) ⟨3477, by rfl⟩ (by norm_num))
theorem R82837 : Reach 82837 := rs (se 6 (by rfl) ⟨1941, by rfl⟩) (B 3883 (by norm_num) ⟨1941, by rfl⟩ (by norm_num))
theorem R82841 : Reach 82841 := rs (se 2 (by rfl) ⟨31065, by rfl⟩) (B 62131 (by norm_num) ⟨31065, by rfl⟩ (by norm_num))
theorem R82845 : Reach 82845 := rs (se 3 (by rfl) ⟨15533, by rfl⟩) (B 31067 (by norm_num) ⟨15533, by rfl⟩ (by norm_num))
theorem R82849 : Reach 82849 := rs (se 2 (by rfl) ⟨31068, by rfl⟩) (B 62137 (by norm_num) ⟨31068, by rfl⟩ (by norm_num))
theorem R82853 : Reach 82853 := rs (se 4 (by rfl) ⟨7767, by rfl⟩) (B 15535 (by norm_num) ⟨7767, by rfl⟩ (by norm_num))
theorem R82857 : Reach 82857 := rs (se 2 (by rfl) ⟨31071, by rfl⟩) (B 62143 (by norm_num) ⟨31071, by rfl⟩ (by norm_num))
theorem R82861 : Reach 82861 := rs (se 3 (by rfl) ⟨15536, by rfl⟩) (B 31073 (by norm_num) ⟨15536, by rfl⟩ (by norm_num))
theorem R82865 : Reach 82865 := rs (se 2 (by rfl) ⟨31074, by rfl⟩) (B 62149 (by norm_num) ⟨31074, by rfl⟩ (by norm_num))
theorem R82869 : Reach 82869 := rs (se 5 (by rfl) ⟨3884, by rfl⟩) (B 7769 (by norm_num) ⟨3884, by rfl⟩ (by norm_num))
theorem R82873 : Reach 82873 := rs (se 2 (by rfl) ⟨31077, by rfl⟩) (B 62155 (by norm_num) ⟨31077, by rfl⟩ (by norm_num))
theorem R82877 : Reach 82877 := rs (se 3 (by rfl) ⟨15539, by rfl⟩) (B 31079 (by norm_num) ⟨15539, by rfl⟩ (by norm_num))
theorem R82881 : Reach 82881 := rs (se 2 (by rfl) ⟨31080, by rfl⟩) (B 62161 (by norm_num) ⟨31080, by rfl⟩ (by norm_num))
theorem R82885 : Reach 82885 := rs (se 4 (by rfl) ⟨7770, by rfl⟩) (B 15541 (by norm_num) ⟨7770, by rfl⟩ (by norm_num))
theorem R82889 : Reach 82889 := rs (se 2 (by rfl) ⟨31083, by rfl⟩) (B 62167 (by norm_num) ⟨31083, by rfl⟩ (by norm_num))
theorem R82893 : Reach 82893 := rs (se 3 (by rfl) ⟨15542, by rfl⟩) (B 31085 (by norm_num) ⟨15542, by rfl⟩ (by norm_num))
theorem R82897 : Reach 82897 := rs (se 2 (by rfl) ⟨31086, by rfl⟩) (B 62173 (by norm_num) ⟨31086, by rfl⟩ (by norm_num))
theorem R181205 : Reach 181205 := rs (se 7 (by rfl) ⟨2123, by rfl⟩) (B 4247 (by norm_num) ⟨2123, by rfl⟩ (by norm_num))
theorem R82901 : Reach 82901 := rs (se 7 (by rfl) ⟨971, by rfl⟩) (B 1943 (by norm_num) ⟨971, by rfl⟩ (by norm_num))
theorem R82905 : Reach 82905 := rs (se 2 (by rfl) ⟨31089, by rfl⟩) (B 62179 (by norm_num) ⟨31089, by rfl⟩ (by norm_num))
theorem R82909 : Reach 82909 := rs (se 3 (by rfl) ⟨15545, by rfl⟩) (B 31091 (by norm_num) ⟨15545, by rfl⟩ (by norm_num))
theorem R82913 : Reach 82913 := rs (se 2 (by rfl) ⟨31092, by rfl⟩) (B 62185 (by norm_num) ⟨31092, by rfl⟩ (by norm_num))
theorem R82917 : Reach 82917 := rs (se 4 (by rfl) ⟨7773, by rfl⟩) (B 15547 (by norm_num) ⟨7773, by rfl⟩ (by norm_num))
theorem R82921 : Reach 82921 := rs (se 2 (by rfl) ⟨31095, by rfl⟩) (B 62191 (by norm_num) ⟨31095, by rfl⟩ (by norm_num))
theorem R82925 : Reach 82925 := rs (se 3 (by rfl) ⟨15548, by rfl⟩) (B 31097 (by norm_num) ⟨15548, by rfl⟩ (by norm_num))
theorem R82929 : Reach 82929 := rs (se 2 (by rfl) ⟨31098, by rfl⟩) (B 62197 (by norm_num) ⟨31098, by rfl⟩ (by norm_num))
theorem R82933 : Reach 82933 := rs (se 5 (by rfl) ⟨3887, by rfl⟩) (B 7775 (by norm_num) ⟨3887, by rfl⟩ (by norm_num))
theorem R82937 : Reach 82937 := rs (se 2 (by rfl) ⟨31101, by rfl⟩) (B 62203 (by norm_num) ⟨31101, by rfl⟩ (by norm_num))
theorem R82941 : Reach 82941 := rs (se 3 (by rfl) ⟨15551, by rfl⟩) (B 31103 (by norm_num) ⟨15551, by rfl⟩ (by norm_num))
theorem R82945 : Reach 82945 := rs (se 2 (by rfl) ⟨31104, by rfl⟩) (B 62209 (by norm_num) ⟨31104, by rfl⟩ (by norm_num))
theorem R279557 : Reach 279557 := rs (se 4 (by rfl) ⟨26208, by rfl⟩) (B 52417 (by norm_num) ⟨26208, by rfl⟩ (by norm_num))
theorem R82949 : Reach 82949 := rs (se 4 (by rfl) ⟨7776, by rfl⟩) (B 15553 (by norm_num) ⟨7776, by rfl⟩ (by norm_num))
theorem R82953 : Reach 82953 := rs (se 2 (by rfl) ⟨31107, by rfl⟩) (B 62215 (by norm_num) ⟨31107, by rfl⟩ (by norm_num))
theorem R82957 : Reach 82957 := rs (se 3 (by rfl) ⟨15554, by rfl⟩) (B 31109 (by norm_num) ⟨15554, by rfl⟩ (by norm_num))
theorem R82961 : Reach 82961 := rs (se 2 (by rfl) ⟨31110, by rfl⟩) (B 62221 (by norm_num) ⟨31110, by rfl⟩ (by norm_num))
theorem R82965 : Reach 82965 := rs (se 6 (by rfl) ⟨1944, by rfl⟩) (B 3889 (by norm_num) ⟨1944, by rfl⟩ (by norm_num))
theorem R82969 : Reach 82969 := rs (se 2 (by rfl) ⟨31113, by rfl⟩) (B 62227 (by norm_num) ⟨31113, by rfl⟩ (by norm_num))
theorem R181277 : Reach 181277 := rs (se 3 (by rfl) ⟨33989, by rfl⟩) (B 67979 (by norm_num) ⟨33989, by rfl⟩ (by norm_num))
theorem R82973 : Reach 82973 := rs (se 3 (by rfl) ⟨15557, by rfl⟩) (B 31115 (by norm_num) ⟨15557, by rfl⟩ (by norm_num))
theorem R82977 : Reach 82977 := rs (se 2 (by rfl) ⟨31116, by rfl⟩) (B 62233 (by norm_num) ⟨31116, by rfl⟩ (by norm_num))
theorem R82981 : Reach 82981 := rs (se 4 (by rfl) ⟨7779, by rfl⟩) (B 15559 (by norm_num) ⟨7779, by rfl⟩ (by norm_num))
theorem R82985 : Reach 82985 := rs (se 2 (by rfl) ⟨31119, by rfl⟩) (B 62239 (by norm_num) ⟨31119, by rfl⟩ (by norm_num))
theorem R82989 : Reach 82989 := rs (se 3 (by rfl) ⟨15560, by rfl⟩) (B 31121 (by norm_num) ⟨15560, by rfl⟩ (by norm_num))
theorem R82993 : Reach 82993 := rs (se 2 (by rfl) ⟨31122, by rfl⟩) (B 62245 (by norm_num) ⟨31122, by rfl⟩ (by norm_num))
theorem R82997 : Reach 82997 := rs (se 5 (by rfl) ⟨3890, by rfl⟩) (B 7781 (by norm_num) ⟨3890, by rfl⟩ (by norm_num))
theorem R83001 : Reach 83001 := rs (se 2 (by rfl) ⟨31125, by rfl⟩) (B 62251 (by norm_num) ⟨31125, by rfl⟩ (by norm_num))
theorem R83005 : Reach 83005 := rs (se 3 (by rfl) ⟨15563, by rfl⟩) (B 31127 (by norm_num) ⟨15563, by rfl⟩ (by norm_num))
theorem R83009 : Reach 83009 := rs (se 2 (by rfl) ⟨31128, by rfl⟩) (B 62257 (by norm_num) ⟨31128, by rfl⟩ (by norm_num))
theorem R83013 : Reach 83013 := rs (se 4 (by rfl) ⟨7782, by rfl⟩) (B 15565 (by norm_num) ⟨7782, by rfl⟩ (by norm_num))
theorem R83017 : Reach 83017 := rs (se 2 (by rfl) ⟨31131, by rfl⟩) (B 62263 (by norm_num) ⟨31131, by rfl⟩ (by norm_num))
theorem R83021 : Reach 83021 := rs (se 3 (by rfl) ⟨15566, by rfl⟩) (B 31133 (by norm_num) ⟨15566, by rfl⟩ (by norm_num))
theorem R83025 : Reach 83025 := rs (se 2 (by rfl) ⟨31134, by rfl⟩) (B 62269 (by norm_num) ⟨31134, by rfl⟩ (by norm_num))
theorem R83029 : Reach 83029 := rs (se 8 (by rfl) ⟨486, by rfl⟩) (B 973 (by norm_num) ⟨486, by rfl⟩ (by norm_num))
theorem R83033 : Reach 83033 := rs (se 2 (by rfl) ⟨31137, by rfl⟩) (B 62275 (by norm_num) ⟨31137, by rfl⟩ (by norm_num))
theorem R83037 : Reach 83037 := rs (se 3 (by rfl) ⟨15569, by rfl⟩) (B 31139 (by norm_num) ⟨15569, by rfl⟩ (by norm_num))
theorem R83041 : Reach 83041 := rs (se 2 (by rfl) ⟨31140, by rfl⟩) (B 62281 (by norm_num) ⟨31140, by rfl⟩ (by norm_num))
theorem R181349 : Reach 181349 := rs (se 4 (by rfl) ⟨17001, by rfl⟩) (B 34003 (by norm_num) ⟨17001, by rfl⟩ (by norm_num))
theorem R83045 : Reach 83045 := rs (se 4 (by rfl) ⟨7785, by rfl⟩) (B 15571 (by norm_num) ⟨7785, by rfl⟩ (by norm_num))
theorem R83049 : Reach 83049 := rs (se 2 (by rfl) ⟨31143, by rfl⟩) (B 62287 (by norm_num) ⟨31143, by rfl⟩ (by norm_num))
theorem R83053 : Reach 83053 := rs (se 3 (by rfl) ⟨15572, by rfl⟩) (B 31145 (by norm_num) ⟨15572, by rfl⟩ (by norm_num))
theorem R83057 : Reach 83057 := rs (se 2 (by rfl) ⟨31146, by rfl⟩) (B 62293 (by norm_num) ⟨31146, by rfl⟩ (by norm_num))
theorem R312437 : Reach 312437 := rs (se 5 (by rfl) ⟨14645, by rfl⟩) (B 29291 (by norm_num) ⟨14645, by rfl⟩ (by norm_num))
theorem R83061 : Reach 83061 := rs (se 5 (by rfl) ⟨3893, by rfl⟩) (B 7787 (by norm_num) ⟨3893, by rfl⟩ (by norm_num))
theorem R83065 : Reach 83065 := rs (se 2 (by rfl) ⟨31149, by rfl⟩) (B 62299 (by norm_num) ⟨31149, by rfl⟩ (by norm_num))
theorem R83069 : Reach 83069 := rs (se 3 (by rfl) ⟨15575, by rfl⟩) (B 31151 (by norm_num) ⟨15575, by rfl⟩ (by norm_num))
theorem R83073 : Reach 83073 := rs (se 2 (by rfl) ⟨31152, by rfl⟩) (B 62305 (by norm_num) ⟨31152, by rfl⟩ (by norm_num))
theorem R83077 : Reach 83077 := rs (se 4 (by rfl) ⟨7788, by rfl⟩) (B 15577 (by norm_num) ⟨7788, by rfl⟩ (by norm_num))
theorem R83081 : Reach 83081 := rs (se 2 (by rfl) ⟨31155, by rfl⟩) (B 62311 (by norm_num) ⟨31155, by rfl⟩ (by norm_num))
theorem R83085 : Reach 83085 := rs (se 3 (by rfl) ⟨15578, by rfl⟩) (B 31157 (by norm_num) ⟨15578, by rfl⟩ (by norm_num))
theorem R83089 : Reach 83089 := rs (se 2 (by rfl) ⟨31158, by rfl⟩) (B 62317 (by norm_num) ⟨31158, by rfl⟩ (by norm_num))
theorem R83093 : Reach 83093 := rs (se 6 (by rfl) ⟨1947, by rfl⟩) (B 3895 (by norm_num) ⟨1947, by rfl⟩ (by norm_num))
theorem R83097 : Reach 83097 := rs (se 2 (by rfl) ⟨31161, by rfl⟩) (B 62323 (by norm_num) ⟨31161, by rfl⟩ (by norm_num))
theorem R83101 : Reach 83101 := rs (se 3 (by rfl) ⟨15581, by rfl⟩) (B 31163 (by norm_num) ⟨15581, by rfl⟩ (by norm_num))
theorem R83105 : Reach 83105 := rs (se 2 (by rfl) ⟨31164, by rfl⟩) (B 62329 (by norm_num) ⟨31164, by rfl⟩ (by norm_num))
theorem R115877 : Reach 115877 := rs (se 4 (by rfl) ⟨10863, by rfl⟩) (B 21727 (by norm_num) ⟨10863, by rfl⟩ (by norm_num))
theorem R83109 : Reach 83109 := rs (se 4 (by rfl) ⟨7791, by rfl⟩) (B 15583 (by norm_num) ⟨7791, by rfl⟩ (by norm_num))
theorem R83113 : Reach 83113 := rs (se 2 (by rfl) ⟨31167, by rfl⟩) (B 62335 (by norm_num) ⟨31167, by rfl⟩ (by norm_num))
theorem R181421 : Reach 181421 := rs (se 3 (by rfl) ⟨34016, by rfl⟩) (B 68033 (by norm_num) ⟨34016, by rfl⟩ (by norm_num))
theorem R83117 : Reach 83117 := rs (se 3 (by rfl) ⟨15584, by rfl⟩) (B 31169 (by norm_num) ⟨15584, by rfl⟩ (by norm_num))
theorem R83121 : Reach 83121 := rs (se 2 (by rfl) ⟨31170, by rfl⟩) (B 62341 (by norm_num) ⟨31170, by rfl⟩ (by norm_num))
theorem R83125 : Reach 83125 := rs (se 5 (by rfl) ⟨3896, by rfl⟩) (B 7793 (by norm_num) ⟨3896, by rfl⟩ (by norm_num))
theorem R181493 : Reach 181493 := rs (se 5 (by rfl) ⟨8507, by rfl⟩) (B 17015 (by norm_num) ⟨8507, by rfl⟩ (by norm_num))
theorem R83197 : Reach 83197 := rs (se 3 (by rfl) ⟨15599, by rfl⟩) (B 31199 (by norm_num) ⟨15599, by rfl⟩ (by norm_num))
theorem R181565 : Reach 181565 := rs (se 3 (by rfl) ⟨34043, by rfl⟩) (B 68087 (by norm_num) ⟨34043, by rfl⟩ (by norm_num))
theorem R181637 : Reach 181637 := rs (se 4 (by rfl) ⟨17028, by rfl⟩) (B 34057 (by norm_num) ⟨17028, by rfl⟩ (by norm_num))
theorem R181645 : Reach 181645 := rs (se 3 (by rfl) ⟨34058, by rfl⟩) (B 68117 (by norm_num) ⟨34058, by rfl⟩ (by norm_num))
theorem R279989 : Reach 279989 := rs (se 5 (by rfl) ⟨13124, by rfl⟩) (B 26249 (by norm_num) ⟨13124, by rfl⟩ (by norm_num))
theorem R181709 : Reach 181709 := rs (se 3 (by rfl) ⟨34070, by rfl⟩) (B 68141 (by norm_num) ⟨34070, by rfl⟩ (by norm_num))
theorem R2803157 : Reach 2803157 := rs (se 7 (by rfl) ⟨32849, by rfl⟩) (B 65699 (by norm_num) ⟨32849, by rfl⟩ (by norm_num))
theorem R181781 : Reach 181781 := rs (se 6 (by rfl) ⟨4260, by rfl⟩) (B 8521 (by norm_num) ⟨4260, by rfl⟩ (by norm_num))
theorem R181853 : Reach 181853 := rs (se 3 (by rfl) ⟨34097, by rfl⟩) (B 68195 (by norm_num) ⟨34097, by rfl⟩ (by norm_num))
theorem R214645 : Reach 214645 := rs (se 5 (by rfl) ⟨10061, by rfl⟩) (B 20123 (by norm_num) ⟨10061, by rfl⟩ (by norm_num))
theorem R181925 : Reach 181925 := rs (se 4 (by rfl) ⟨17055, by rfl⟩) (B 34111 (by norm_num) ⟨17055, by rfl⟩ (by norm_num))
theorem R411317 : Reach 411317 := rs (se 5 (by rfl) ⟨19280, by rfl⟩) (B 38561 (by norm_num) ⟨19280, by rfl⟩ (by norm_num))
theorem R181997 : Reach 181997 := rs (se 3 (by rfl) ⟨34124, by rfl⟩) (B 68249 (by norm_num) ⟨34124, by rfl⟩ (by norm_num))
theorem R182069 : Reach 182069 := rs (se 5 (by rfl) ⟨8534, by rfl⟩) (B 17069 (by norm_num) ⟨8534, by rfl⟩ (by norm_num))
theorem R345941 : Reach 345941 := rs (se 9 (by rfl) ⟨1013, by rfl⟩) (B 2027 (by norm_num) ⟨1013, by rfl⟩ (by norm_num))
theorem R280421 : Reach 280421 := rs (se 4 (by rfl) ⟨26289, by rfl⟩) (B 52579 (by norm_num) ⟨26289, by rfl⟩ (by norm_num))
theorem R509813 : Reach 509813 := rs (se 5 (by rfl) ⟨23897, by rfl⟩) (B 47795 (by norm_num) ⟨23897, by rfl⟩ (by norm_num))
theorem R182141 : Reach 182141 := rs (se 3 (by rfl) ⟨34151, by rfl⟩) (B 68303 (by norm_num) ⟨34151, by rfl⟩ (by norm_num))
theorem R182213 : Reach 182213 := rs (se 4 (by rfl) ⟨17082, by rfl⟩) (B 34165 (by norm_num) ⟨17082, by rfl⟩ (by norm_num))
theorem R182285 : Reach 182285 := rs (se 3 (by rfl) ⟨34178, by rfl⟩) (B 68357 (by norm_num) ⟨34178, by rfl⟩ (by norm_num))
theorem R182357 : Reach 182357 := rs (se 8 (by rfl) ⟨1068, by rfl⟩) (B 2137 (by norm_num) ⟨1068, by rfl⟩ (by norm_num))
theorem R182429 : Reach 182429 := rs (se 3 (by rfl) ⟨34205, by rfl⟩) (B 68411 (by norm_num) ⟨34205, by rfl⟩ (by norm_num))
theorem R182501 : Reach 182501 := rs (se 4 (by rfl) ⟨17109, by rfl⟩) (B 34219 (by norm_num) ⟨17109, by rfl⟩ (by norm_num))
theorem R182573 : Reach 182573 := rs (se 3 (by rfl) ⟨34232, by rfl⟩) (B 68465 (by norm_num) ⟨34232, by rfl⟩ (by norm_num))
theorem R182645 : Reach 182645 := rs (se 5 (by rfl) ⟨8561, by rfl⟩) (B 17123 (by norm_num) ⟨8561, by rfl⟩ (by norm_num))
theorem R182717 : Reach 182717 := rs (se 3 (by rfl) ⟨34259, by rfl⟩) (B 68519 (by norm_num) ⟨34259, by rfl⟩ (by norm_num))
theorem R182741 : Reach 182741 := rs (se 7 (by rfl) ⟨2141, by rfl⟩) (B 4283 (by norm_num) ⟨2141, by rfl⟩ (by norm_num))
theorem R182749 : Reach 182749 := rs (se 3 (by rfl) ⟨34265, by rfl⟩) (B 68531 (by norm_num) ⟨34265, by rfl⟩ (by norm_num))
theorem R182789 : Reach 182789 := rs (se 4 (by rfl) ⟨17136, by rfl⟩) (B 34273 (by norm_num) ⟨17136, by rfl⟩ (by norm_num))
theorem R117301 : Reach 117301 := rs (se 5 (by rfl) ⟨5498, by rfl⟩) (B 10997 (by norm_num) ⟨5498, by rfl⟩ (by norm_num))
theorem R182861 : Reach 182861 := rs (se 3 (by rfl) ⟨34286, by rfl⟩) (B 68573 (by norm_num) ⟨34286, by rfl⟩ (by norm_num))
theorem R182933 : Reach 182933 := rs (se 6 (by rfl) ⟨4287, by rfl⟩) (B 8575 (by norm_num) ⟨4287, by rfl⟩ (by norm_num))
theorem R183005 : Reach 183005 := rs (se 3 (by rfl) ⟨34313, by rfl⟩) (B 68627 (by norm_num) ⟨34313, by rfl⟩ (by norm_num))
theorem R84721 : Reach 84721 := rs (se 2 (by rfl) ⟨31770, by rfl⟩) (B 63541 (by norm_num) ⟨31770, by rfl⟩ (by norm_num))
theorem R183077 : Reach 183077 := rs (se 4 (by rfl) ⟨17163, by rfl⟩) (B 34327 (by norm_num) ⟨17163, by rfl⟩ (by norm_num))
theorem R346949 : Reach 346949 := rs (se 4 (by rfl) ⟨32526, by rfl⟩) (B 65053 (by norm_num) ⟨32526, by rfl⟩ (by norm_num))
theorem R150349 : Reach 150349 := rs (se 3 (by rfl) ⟨28190, by rfl⟩) (B 56381 (by norm_num) ⟨28190, by rfl⟩ (by norm_num))
theorem R84845 : Reach 84845 := rs (se 3 (by rfl) ⟨15908, by rfl⟩) (B 31817 (by norm_num) ⟨15908, by rfl⟩ (by norm_num))
theorem R183149 : Reach 183149 := rs (se 3 (by rfl) ⟨34340, by rfl⟩) (B 68681 (by norm_num) ⟨34340, by rfl⟩ (by norm_num))
theorem R183221 : Reach 183221 := rs (se 5 (by rfl) ⟨8588, by rfl⟩) (B 17177 (by norm_num) ⟨8588, by rfl⟩ (by norm_num))
theorem R412613 : Reach 412613 := rs (se 4 (by rfl) ⟨38682, by rfl⟩) (B 77365 (by norm_num) ⟨38682, by rfl⟩ (by norm_num))
theorem R150493 : Reach 150493 := rs (se 3 (by rfl) ⟨28217, by rfl⟩) (B 56435 (by norm_num) ⟨28217, by rfl⟩ (by norm_num))
theorem R183293 : Reach 183293 := rs (se 3 (by rfl) ⟨34367, by rfl⟩) (B 68735 (by norm_num) ⟨34367, by rfl⟩ (by norm_num))
theorem R1559573 : Reach 1559573 := rs (se 6 (by rfl) ⟨36552, by rfl⟩) (B 73105 (by norm_num) ⟨36552, by rfl⟩ (by norm_num))
theorem R183365 : Reach 183365 := rs (se 4 (by rfl) ⟨17190, by rfl⟩) (B 34381 (by norm_num) ⟨17190, by rfl⟩ (by norm_num))
theorem R85097 : Reach 85097 := rs (se 2 (by rfl) ⟨31911, by rfl⟩) (B 63823 (by norm_num) ⟨31911, by rfl⟩ (by norm_num))
theorem R150653 : Reach 150653 := rs (se 3 (by rfl) ⟨28247, by rfl⟩) (B 56495 (by norm_num) ⟨28247, by rfl⟩ (by norm_num))
theorem R117893 : Reach 117893 := rs (se 4 (by rfl) ⟨11052, by rfl⟩) (B 22105 (by norm_num) ⟨11052, by rfl⟩ (by norm_num))
theorem R183437 : Reach 183437 := rs (se 3 (by rfl) ⟨34394, by rfl⟩) (B 68789 (by norm_num) ⟨34394, by rfl⟩ (by norm_num))
theorem R216245 : Reach 216245 := rs (se 5 (by rfl) ⟨10136, by rfl⟩) (B 20273 (by norm_num) ⟨10136, by rfl⟩ (by norm_num))
theorem R314549 : Reach 314549 := rs (se 5 (by rfl) ⟨14744, by rfl⟩) (B 29489 (by norm_num) ⟨14744, by rfl⟩ (by norm_num))
theorem R183509 : Reach 183509 := rs (se 7 (by rfl) ⟨2150, by rfl⟩) (B 4301 (by norm_num) ⟨2150, by rfl⟩ (by norm_num))
theorem R117973 : Reach 117973 := rs (se 7 (by rfl) ⟨1382, by rfl⟩) (B 2765 (by norm_num) ⟨1382, by rfl⟩ (by norm_num))
theorem R150797 : Reach 150797 := rs (se 3 (by rfl) ⟨28274, by rfl⟩) (B 56549 (by norm_num) ⟨28274, by rfl⟩ (by norm_num))
theorem R183581 : Reach 183581 := rs (se 3 (by rfl) ⟨34421, by rfl⟩) (B 68843 (by norm_num) ⟨34421, by rfl⟩ (by norm_num))
theorem R118093 : Reach 118093 := rs (se 3 (by rfl) ⟨22142, by rfl⟩) (B 44285 (by norm_num) ⟨22142, by rfl⟩ (by norm_num))
theorem R544085 : Reach 544085 := rs (se 11 (by rfl) ⟨398, by rfl⟩) (B 797 (by norm_num) ⟨398, by rfl⟩ (by norm_num))
theorem R183653 : Reach 183653 := rs (se 4 (by rfl) ⟨17217, by rfl⟩) (B 34435 (by norm_num) ⟨17217, by rfl⟩ (by norm_num))
theorem R183725 : Reach 183725 := rs (se 3 (by rfl) ⟨34448, by rfl⟩) (B 68897 (by norm_num) ⟨34448, by rfl⟩ (by norm_num))
theorem R118189 : Reach 118189 := rs (se 3 (by rfl) ⟨22160, by rfl⟩) (B 44321 (by norm_num) ⟨22160, by rfl⟩ (by norm_num))
theorem R314837 : Reach 314837 := rs (se 7 (by rfl) ⟨3689, by rfl⟩) (B 7379 (by norm_num) ⟨3689, by rfl⟩ (by norm_num))
theorem R183797 : Reach 183797 := rs (se 5 (by rfl) ⟨8615, by rfl⟩) (B 17231 (by norm_num) ⟨8615, by rfl⟩ (by norm_num))
theorem R937493 : Reach 937493 := rs (se 6 (by rfl) ⟨21972, by rfl⟩) (B 43945 (by norm_num) ⟨21972, by rfl⟩ (by norm_num))
theorem R85541 : Reach 85541 := rs (se 4 (by rfl) ⟨8019, by rfl⟩) (B 16039 (by norm_num) ⟨8019, by rfl⟩ (by norm_num))
theorem R151085 : Reach 151085 := rs (se 3 (by rfl) ⟨28328, by rfl⟩) (B 56657 (by norm_num) ⟨28328, by rfl⟩ (by norm_num))
theorem R151093 : Reach 151093 := rs (se 5 (by rfl) ⟨7082, by rfl⟩) (B 14165 (by norm_num) ⟨7082, by rfl⟩ (by norm_num))
theorem R183869 : Reach 183869 := rs (se 3 (by rfl) ⟨34475, by rfl⟩) (B 68951 (by norm_num) ⟨34475, by rfl⟩ (by norm_num))
theorem R183941 : Reach 183941 := rs (se 4 (by rfl) ⟨17244, by rfl⟩) (B 34489 (by norm_num) ⟨17244, by rfl⟩ (by norm_num))
theorem R151237 : Reach 151237 := rs (se 4 (by rfl) ⟨14178, by rfl⟩) (B 28357 (by norm_num) ⟨14178, by rfl⟩ (by norm_num))
theorem R184013 : Reach 184013 := rs (se 3 (by rfl) ⟨34502, by rfl⟩) (B 69005 (by norm_num) ⟨34502, by rfl⟩ (by norm_num))
theorem R380629 : Reach 380629 := rs (se 7 (by rfl) ⟨4460, by rfl⟩) (B 8921 (by norm_num) ⟨4460, by rfl⟩ (by norm_num))
theorem R216821 : Reach 216821 := rs (se 5 (by rfl) ⟨10163, by rfl⟩) (B 20327 (by norm_num) ⟨10163, by rfl⟩ (by norm_num))
theorem R184085 : Reach 184085 := rs (se 6 (by rfl) ⟨4314, by rfl⟩) (B 8629 (by norm_num) ⟨4314, by rfl⟩ (by norm_num))
theorem R85789 : Reach 85789 := rs (se 3 (by rfl) ⟨16085, by rfl⟩) (B 32171 (by norm_num) ⟨16085, by rfl⟩ (by norm_num))
theorem R5820245 : Reach 5820245 := rs (se 9 (by rfl) ⟨17051, by rfl⟩) (B 34103 (by norm_num) ⟨17051, by rfl⟩ (by norm_num))
theorem R184157 : Reach 184157 := rs (se 3 (by rfl) ⟨34529, by rfl⟩) (B 69059 (by norm_num) ⟨34529, by rfl⟩ (by norm_num))
theorem R184229 : Reach 184229 := rs (se 4 (by rfl) ⟨17271, by rfl⟩) (B 34543 (by norm_num) ⟨17271, by rfl⟩ (by norm_num))
theorem R118709 : Reach 118709 := rs (se 5 (by rfl) ⟨5564, by rfl⟩) (B 11129 (by norm_num) ⟨5564, by rfl⟩ (by norm_num))
theorem R249797 : Reach 249797 := rs (se 4 (by rfl) ⟨23418, by rfl⟩) (B 46837 (by norm_num) ⟨23418, by rfl⟩ (by norm_num))
theorem R118733 : Reach 118733 := rs (se 3 (by rfl) ⟨22262, by rfl⟩) (B 44525 (by norm_num) ⟨22262, by rfl⟩ (by norm_num))
theorem R118757 : Reach 118757 := rs (se 4 (by rfl) ⟨11133, by rfl⟩) (B 22267 (by norm_num) ⟨11133, by rfl⟩ (by norm_num))
theorem R184301 : Reach 184301 := rs (se 3 (by rfl) ⟨34556, by rfl⟩) (B 69113 (by norm_num) ⟨34556, by rfl⟩ (by norm_num))
theorem R151541 : Reach 151541 := rs (se 5 (by rfl) ⟨7103, by rfl⟩) (B 14207 (by norm_num) ⟨7103, by rfl⟩ (by norm_num))
theorem R118781 : Reach 118781 := rs (se 3 (by rfl) ⟨22271, by rfl⟩) (B 44543 (by norm_num) ⟨22271, by rfl⟩ (by norm_num))
theorem R118805 : Reach 118805 := rs (se 6 (by rfl) ⟨2784, by rfl⟩) (B 5569 (by norm_num) ⟨2784, by rfl⟩ (by norm_num))
theorem R118829 : Reach 118829 := rs (se 3 (by rfl) ⟨22280, by rfl⟩) (B 44561 (by norm_num) ⟨22280, by rfl⟩ (by norm_num))
theorem R184373 : Reach 184373 := rs (se 5 (by rfl) ⟨8642, by rfl⟩) (B 17285 (by norm_num) ⟨8642, by rfl⟩ (by norm_num))
theorem R118853 : Reach 118853 := rs (se 4 (by rfl) ⟨11142, by rfl⟩) (B 22285 (by norm_num) ⟨11142, by rfl⟩ (by norm_num))
theorem R1527893 : Reach 1527893 := rs (se 8 (by rfl) ⟨8952, by rfl⟩) (B 17905 (by norm_num) ⟨8952, by rfl⟩ (by norm_num))
theorem R118877 : Reach 118877 := rs (se 3 (by rfl) ⟨22289, by rfl⟩) (B 44579 (by norm_num) ⟨22289, by rfl⟩ (by norm_num))
theorem R118901 : Reach 118901 := rs (se 5 (by rfl) ⟨5573, by rfl⟩) (B 11147 (by norm_num) ⟨5573, by rfl⟩ (by norm_num))
theorem R184445 : Reach 184445 := rs (se 3 (by rfl) ⟨34583, by rfl⟩) (B 69167 (by norm_num) ⟨34583, by rfl⟩ (by norm_num))
theorem R118925 : Reach 118925 := rs (se 3 (by rfl) ⟨22298, by rfl⟩) (B 44597 (by norm_num) ⟨22298, by rfl⟩ (by norm_num))
theorem R118949 : Reach 118949 := rs (se 4 (by rfl) ⟨11151, by rfl⟩) (B 22303 (by norm_num) ⟨11151, by rfl⟩ (by norm_num))
theorem R118973 : Reach 118973 := rs (se 3 (by rfl) ⟨22307, by rfl⟩) (B 44615 (by norm_num) ⟨22307, by rfl⟩ (by norm_num))
theorem R184517 : Reach 184517 := rs (se 4 (by rfl) ⟨17298, by rfl⟩) (B 34597 (by norm_num) ⟨17298, by rfl⟩ (by norm_num))
theorem R118997 : Reach 118997 := rs (se 7 (by rfl) ⟨1394, by rfl⟩) (B 2789 (by norm_num) ⟨1394, by rfl⟩ (by norm_num))
theorem R413909 : Reach 413909 := rs (se 7 (by rfl) ⟨4850, by rfl⟩) (B 9701 (by norm_num) ⟨4850, by rfl⟩ (by norm_num))
theorem R86233 : Reach 86233 := rs (se 2 (by rfl) ⟨32337, by rfl⟩) (B 64675 (by norm_num) ⟨32337, by rfl⟩ (by norm_num))
theorem R119021 : Reach 119021 := rs (se 3 (by rfl) ⟨22316, by rfl⟩) (B 44633 (by norm_num) ⟨22316, by rfl⟩ (by norm_num))
theorem R119045 : Reach 119045 := rs (se 4 (by rfl) ⟨11160, by rfl⟩) (B 22321 (by norm_num) ⟨11160, by rfl⟩ (by norm_num))
theorem R413957 : Reach 413957 := rs (se 4 (by rfl) ⟨38808, by rfl⟩) (B 77617 (by norm_num) ⟨38808, by rfl⟩ (by norm_num))
theorem R184589 : Reach 184589 := rs (se 3 (by rfl) ⟨34610, by rfl⟩) (B 69221 (by norm_num) ⟨34610, by rfl⟩ (by norm_num))
theorem R86293 : Reach 86293 := rs (se 6 (by rfl) ⟨2022, by rfl⟩) (B 4045 (by norm_num) ⟨2022, by rfl⟩ (by norm_num))
theorem R119069 : Reach 119069 := rs (se 3 (by rfl) ⟨22325, by rfl⟩) (B 44651 (by norm_num) ⟨22325, by rfl⟩ (by norm_num))
theorem R119093 : Reach 119093 := rs (se 5 (by rfl) ⟨5582, by rfl⟩) (B 11165 (by norm_num) ⟨5582, by rfl⟩ (by norm_num))
theorem R119117 : Reach 119117 := rs (se 3 (by rfl) ⟨22334, by rfl⟩) (B 44669 (by norm_num) ⟨22334, by rfl⟩ (by norm_num))
theorem R184661 : Reach 184661 := rs (se 10 (by rfl) ⟨270, by rfl⟩) (B 541 (by norm_num) ⟨270, by rfl⟩ (by norm_num))
theorem R119141 : Reach 119141 := rs (se 4 (by rfl) ⟨11169, by rfl⟩) (B 22339 (by norm_num) ⟨11169, by rfl⟩ (by norm_num))
theorem R119165 : Reach 119165 := rs (se 3 (by rfl) ⟨22343, by rfl⟩) (B 44687 (by norm_num) ⟨22343, by rfl⟩ (by norm_num))
theorem R119189 : Reach 119189 := rs (se 6 (by rfl) ⟨2793, by rfl⟩) (B 5587 (by norm_num) ⟨2793, by rfl⟩ (by norm_num))
theorem R184733 : Reach 184733 := rs (se 3 (by rfl) ⟨34637, by rfl⟩) (B 69275 (by norm_num) ⟨34637, by rfl⟩ (by norm_num))
theorem R119213 : Reach 119213 := rs (se 3 (by rfl) ⟨22352, by rfl⟩) (B 44705 (by norm_num) ⟨22352, by rfl⟩ (by norm_num))
theorem R119237 : Reach 119237 := rs (se 4 (by rfl) ⟨11178, by rfl⟩) (B 22357 (by norm_num) ⟨11178, by rfl⟩ (by norm_num))
theorem R119261 : Reach 119261 := rs (se 3 (by rfl) ⟨22361, by rfl⟩) (B 44723 (by norm_num) ⟨22361, by rfl⟩ (by norm_num))
theorem R184805 : Reach 184805 := rs (se 4 (by rfl) ⟨17325, by rfl⟩) (B 34651 (by norm_num) ⟨17325, by rfl⟩ (by norm_num))
theorem R119285 : Reach 119285 := rs (se 5 (by rfl) ⟨5591, by rfl⟩) (B 11183 (by norm_num) ⟨5591, by rfl⟩ (by norm_num))
theorem R119309 : Reach 119309 := rs (se 3 (by rfl) ⟨22370, by rfl⟩) (B 44741 (by norm_num) ⟨22370, by rfl⟩ (by norm_num))
theorem R119333 : Reach 119333 := rs (se 4 (by rfl) ⟨11187, by rfl⟩) (B 22375 (by norm_num) ⟨11187, by rfl⟩ (by norm_num))
theorem R184877 : Reach 184877 := rs (se 3 (by rfl) ⟨34664, by rfl⟩) (B 69329 (by norm_num) ⟨34664, by rfl⟩ (by norm_num))
theorem R348725 : Reach 348725 := rs (se 5 (by rfl) ⟨16346, by rfl⟩) (B 32693 (by norm_num) ⟨16346, by rfl⟩ (by norm_num))
theorem R119357 : Reach 119357 := rs (se 3 (by rfl) ⟨22379, by rfl⟩) (B 44759 (by norm_num) ⟨22379, by rfl⟩ (by norm_num))
theorem R86609 : Reach 86609 := rs (se 2 (by rfl) ⟨32478, by rfl⟩) (B 64957 (by norm_num) ⟨32478, by rfl⟩ (by norm_num))
theorem R119381 : Reach 119381 := rs (se 8 (by rfl) ⟨699, by rfl⟩) (B 1399 (by norm_num) ⟨699, by rfl⟩ (by norm_num))
theorem R610901 : Reach 610901 := rs (se 8 (by rfl) ⟨3579, by rfl⟩) (B 7159 (by norm_num) ⟨3579, by rfl⟩ (by norm_num))
theorem R119405 : Reach 119405 := rs (se 3 (by rfl) ⟨22388, by rfl⟩) (B 44777 (by norm_num) ⟨22388, by rfl⟩ (by norm_num))
theorem R184949 : Reach 184949 := rs (se 5 (by rfl) ⟨8669, by rfl⟩) (B 17339 (by norm_num) ⟨8669, by rfl⟩ (by norm_num))
theorem R119429 : Reach 119429 := rs (se 4 (by rfl) ⟨11196, by rfl⟩) (B 22393 (by norm_num) ⟨11196, by rfl⟩ (by norm_num))
theorem R119453 : Reach 119453 := rs (se 3 (by rfl) ⟨22397, by rfl⟩) (B 44795 (by norm_num) ⟨22397, by rfl⟩ (by norm_num))
theorem R119477 : Reach 119477 := rs (se 5 (by rfl) ⟨5600, by rfl⟩) (B 11201 (by norm_num) ⟨5600, by rfl⟩ (by norm_num))
theorem R185021 : Reach 185021 := rs (se 3 (by rfl) ⟨34691, by rfl⟩) (B 69383 (by norm_num) ⟨34691, by rfl⟩ (by norm_num))
theorem R119501 : Reach 119501 := rs (se 3 (by rfl) ⟨22406, by rfl⟩) (B 44813 (by norm_num) ⟨22406, by rfl⟩ (by norm_num))
theorem R119525 : Reach 119525 := rs (se 4 (by rfl) ⟨11205, by rfl⟩) (B 22411 (by norm_num) ⟨11205, by rfl⟩ (by norm_num))
theorem R152293 : Reach 152293 := rs (se 4 (by rfl) ⟨14277, by rfl⟩) (B 28555 (by norm_num) ⟨14277, by rfl⟩ (by norm_num))
theorem R119549 : Reach 119549 := rs (se 3 (by rfl) ⟨22415, by rfl⟩) (B 44831 (by norm_num) ⟨22415, by rfl⟩ (by norm_num))
theorem R185093 : Reach 185093 := rs (se 4 (by rfl) ⟨17352, by rfl⟩) (B 34705 (by norm_num) ⟨17352, by rfl⟩ (by norm_num))
theorem R119573 : Reach 119573 := rs (se 6 (by rfl) ⟨2802, by rfl⟩) (B 5605 (by norm_num) ⟨2802, by rfl⟩ (by norm_num))
theorem R119597 : Reach 119597 := rs (se 3 (by rfl) ⟨22424, by rfl⟩) (B 44849 (by norm_num) ⟨22424, by rfl⟩ (by norm_num))
theorem R119621 : Reach 119621 := rs (se 4 (by rfl) ⟨11214, by rfl⟩) (B 22429 (by norm_num) ⟨11214, by rfl⟩ (by norm_num))
theorem R185165 : Reach 185165 := rs (se 3 (by rfl) ⟨34718, by rfl⟩) (B 69437 (by norm_num) ⟨34718, by rfl⟩ (by norm_num))
theorem R119645 : Reach 119645 := rs (se 3 (by rfl) ⟨22433, by rfl⟩) (B 44867 (by norm_num) ⟨22433, by rfl⟩ (by norm_num))
theorem R119669 : Reach 119669 := rs (se 5 (by rfl) ⟨5609, by rfl⟩) (B 11219 (by norm_num) ⟨5609, by rfl⟩ (by norm_num))
theorem R152437 : Reach 152437 := rs (se 5 (by rfl) ⟨7145, by rfl⟩) (B 14291 (by norm_num) ⟨7145, by rfl⟩ (by norm_num))
theorem R119693 : Reach 119693 := rs (se 3 (by rfl) ⟨22442, by rfl⟩) (B 44885 (by norm_num) ⟨22442, by rfl⟩ (by norm_num))
theorem R185237 : Reach 185237 := rs (se 6 (by rfl) ⟨4341, by rfl⟩) (B 8683 (by norm_num) ⟨4341, by rfl⟩ (by norm_num))
theorem R119717 : Reach 119717 := rs (se 4 (by rfl) ⟨11223, by rfl⟩) (B 22447 (by norm_num) ⟨11223, by rfl⟩ (by norm_num))
theorem R119741 : Reach 119741 := rs (se 3 (by rfl) ⟨22451, by rfl⟩) (B 44903 (by norm_num) ⟨22451, by rfl⟩ (by norm_num))
theorem R119765 : Reach 119765 := rs (se 7 (by rfl) ⟨1403, by rfl⟩) (B 2807 (by norm_num) ⟨1403, by rfl⟩ (by norm_num))
theorem R87005 : Reach 87005 := rs (se 3 (by rfl) ⟨16313, by rfl⟩) (B 32627 (by norm_num) ⟨16313, by rfl⟩ (by norm_num))
theorem R185309 : Reach 185309 := rs (se 3 (by rfl) ⟨34745, by rfl⟩) (B 69491 (by norm_num) ⟨34745, by rfl⟩ (by norm_num))
theorem R119789 : Reach 119789 := rs (se 3 (by rfl) ⟨22460, by rfl⟩) (B 44921 (by norm_num) ⟨22460, by rfl⟩ (by norm_num))
theorem R119813 : Reach 119813 := rs (se 4 (by rfl) ⟨11232, by rfl⟩) (B 22465 (by norm_num) ⟨11232, by rfl⟩ (by norm_num))
theorem R87053 : Reach 87053 := rs (se 3 (by rfl) ⟨16322, by rfl⟩) (B 32645 (by norm_num) ⟨16322, by rfl⟩ (by norm_num))
theorem R152597 : Reach 152597 := rs (se 6 (by rfl) ⟨3576, by rfl⟩) (B 7153 (by norm_num) ⟨3576, by rfl⟩ (by norm_num))
theorem R119837 : Reach 119837 := rs (se 3 (by rfl) ⟨22469, by rfl⟩) (B 44939 (by norm_num) ⟨22469, by rfl⟩ (by norm_num))
theorem R185381 : Reach 185381 := rs (se 4 (by rfl) ⟨17379, by rfl⟩) (B 34759 (by norm_num) ⟨17379, by rfl⟩ (by norm_num))
theorem R119861 : Reach 119861 := rs (se 5 (by rfl) ⟨5618, by rfl⟩) (B 11237 (by norm_num) ⟨5618, by rfl⟩ (by norm_num))
theorem R87113 : Reach 87113 := rs (se 2 (by rfl) ⟨32667, by rfl⟩) (B 65335 (by norm_num) ⟨32667, by rfl⟩ (by norm_num))
theorem R119885 : Reach 119885 := rs (se 3 (by rfl) ⟨22478, by rfl⟩) (B 44957 (by norm_num) ⟨22478, by rfl⟩ (by norm_num))
theorem R119909 : Reach 119909 := rs (se 4 (by rfl) ⟨11241, by rfl⟩) (B 22483 (by norm_num) ⟨11241, by rfl⟩ (by norm_num))
theorem R185453 : Reach 185453 := rs (se 3 (by rfl) ⟨34772, by rfl⟩) (B 69545 (by norm_num) ⟨34772, by rfl⟩ (by norm_num))
theorem R119933 : Reach 119933 := rs (se 3 (by rfl) ⟨22487, by rfl⟩) (B 44975 (by norm_num) ⟨22487, by rfl⟩ (by norm_num))
theorem R119957 : Reach 119957 := rs (se 6 (by rfl) ⟨2811, by rfl⟩) (B 5623 (by norm_num) ⟨2811, by rfl⟩ (by norm_num))
theorem R152741 : Reach 152741 := rs (se 4 (by rfl) ⟨14319, by rfl⟩) (B 28639 (by norm_num) ⟨14319, by rfl⟩ (by norm_num))
theorem R119981 : Reach 119981 := rs (se 3 (by rfl) ⟨22496, by rfl⟩) (B 44993 (by norm_num) ⟨22496, by rfl⟩ (by norm_num))
theorem R185525 : Reach 185525 := rs (se 5 (by rfl) ⟨8696, by rfl⟩) (B 17393 (by norm_num) ⟨8696, by rfl⟩ (by norm_num))
theorem R120005 : Reach 120005 := rs (se 4 (by rfl) ⟨11250, by rfl⟩) (B 22501 (by norm_num) ⟨11250, by rfl⟩ (by norm_num))
theorem R87241 : Reach 87241 := rs (se 2 (by rfl) ⟨32715, by rfl⟩) (B 65431 (by norm_num) ⟨32715, by rfl⟩ (by norm_num))
theorem R120029 : Reach 120029 := rs (se 3 (by rfl) ⟨22505, by rfl⟩) (B 45011 (by norm_num) ⟨22505, by rfl⟩ (by norm_num))
theorem R120053 : Reach 120053 := rs (se 5 (by rfl) ⟨5627, by rfl⟩) (B 11255 (by norm_num) ⟨5627, by rfl⟩ (by norm_num))
theorem R185597 : Reach 185597 := rs (se 3 (by rfl) ⟨34799, by rfl⟩) (B 69599 (by norm_num) ⟨34799, by rfl⟩ (by norm_num))
theorem R120077 : Reach 120077 := rs (se 3 (by rfl) ⟨22514, by rfl⟩) (B 45029 (by norm_num) ⟨22514, by rfl⟩ (by norm_num))
theorem R120101 : Reach 120101 := rs (se 4 (by rfl) ⟨11259, by rfl⟩) (B 22519 (by norm_num) ⟨11259, by rfl⟩ (by norm_num))
theorem R120125 : Reach 120125 := rs (se 3 (by rfl) ⟨22523, by rfl⟩) (B 45047 (by norm_num) ⟨22523, by rfl⟩ (by norm_num))
theorem R185669 : Reach 185669 := rs (se 4 (by rfl) ⟨17406, by rfl⟩) (B 34813 (by norm_num) ⟨17406, by rfl⟩ (by norm_num))
theorem R120149 : Reach 120149 := rs (se 15 (by rfl) ⟨5, by rfl⟩) (B 11 (by norm_num) ⟨5, by rfl⟩ (by norm_num))
theorem R120173 : Reach 120173 := rs (se 3 (by rfl) ⟨22532, by rfl⟩) (B 45065 (by norm_num) ⟨22532, by rfl⟩ (by norm_num))
theorem R120197 : Reach 120197 := rs (se 4 (by rfl) ⟨11268, by rfl⟩) (B 22537 (by norm_num) ⟨11268, by rfl⟩ (by norm_num))
theorem R185741 : Reach 185741 := rs (se 3 (by rfl) ⟨34826, by rfl⟩) (B 69653 (by norm_num) ⟨34826, by rfl⟩ (by norm_num))
theorem R120221 : Reach 120221 := rs (se 3 (by rfl) ⟨22541, by rfl⟩) (B 45083 (by norm_num) ⟨22541, by rfl⟩ (by norm_num))
theorem R120245 : Reach 120245 := rs (se 5 (by rfl) ⟨5636, by rfl⟩) (B 11273 (by norm_num) ⟨5636, by rfl⟩ (by norm_num))
theorem R153029 : Reach 153029 := rs (se 4 (by rfl) ⟨14346, by rfl⟩) (B 28693 (by norm_num) ⟨14346, by rfl⟩ (by norm_num))
theorem R120269 : Reach 120269 := rs (se 3 (by rfl) ⟨22550, by rfl⟩) (B 45101 (by norm_num) ⟨22550, by rfl⟩ (by norm_num))
theorem R185813 : Reach 185813 := rs (se 7 (by rfl) ⟨2177, by rfl⟩) (B 4355 (by norm_num) ⟨2177, by rfl⟩ (by norm_num))
theorem R120293 : Reach 120293 := rs (se 4 (by rfl) ⟨11277, by rfl⟩) (B 22555 (by norm_num) ⟨11277, by rfl⟩ (by norm_num))
theorem R415205 : Reach 415205 := rs (se 4 (by rfl) ⟨38925, by rfl⟩) (B 77851 (by norm_num) ⟨38925, by rfl⟩ (by norm_num))
theorem R120317 : Reach 120317 := rs (se 3 (by rfl) ⟨22559, by rfl⟩) (B 45119 (by norm_num) ⟨22559, by rfl⟩ (by norm_num))
theorem R120341 : Reach 120341 := rs (se 6 (by rfl) ⟨2820, by rfl⟩) (B 5641 (by norm_num) ⟨2820, by rfl⟩ (by norm_num))
theorem R185885 : Reach 185885 := rs (se 3 (by rfl) ⟨34853, by rfl⟩) (B 69707 (by norm_num) ⟨34853, by rfl⟩ (by norm_num))
theorem R120365 : Reach 120365 := rs (se 3 (by rfl) ⟨22568, by rfl⟩) (B 45137 (by norm_num) ⟨22568, by rfl⟩ (by norm_num))
theorem R120389 : Reach 120389 := rs (se 4 (by rfl) ⟨11286, by rfl⟩) (B 22573 (by norm_num) ⟨11286, by rfl⟩ (by norm_num))
theorem R120413 : Reach 120413 := rs (se 3 (by rfl) ⟨22577, by rfl⟩) (B 45155 (by norm_num) ⟨22577, by rfl⟩ (by norm_num))
theorem R153181 : Reach 153181 := rs (se 3 (by rfl) ⟨28721, by rfl⟩) (B 57443 (by norm_num) ⟨28721, by rfl⟩ (by norm_num))
theorem R185957 : Reach 185957 := rs (se 4 (by rfl) ⟨17433, by rfl⟩) (B 34867 (by norm_num) ⟨17433, by rfl⟩ (by norm_num))
theorem R120437 : Reach 120437 := rs (se 5 (by rfl) ⟨5645, by rfl⟩) (B 11291 (by norm_num) ⟨5645, by rfl⟩ (by norm_num))
theorem R87685 : Reach 87685 := rs (se 4 (by rfl) ⟨8220, by rfl⟩) (B 16441 (by norm_num) ⟨8220, by rfl⟩ (by norm_num))
theorem R120461 : Reach 120461 := rs (se 3 (by rfl) ⟨22586, by rfl⟩) (B 45173 (by norm_num) ⟨22586, by rfl⟩ (by norm_num))
theorem R120485 : Reach 120485 := rs (se 4 (by rfl) ⟨11295, by rfl⟩) (B 22591 (by norm_num) ⟨11295, by rfl⟩ (by norm_num))
theorem R186029 : Reach 186029 := rs (se 3 (by rfl) ⟨34880, by rfl⟩) (B 69761 (by norm_num) ⟨34880, by rfl⟩ (by norm_num))
theorem R120509 : Reach 120509 := rs (se 3 (by rfl) ⟨22595, by rfl⟩) (B 45191 (by norm_num) ⟨22595, by rfl⟩ (by norm_num))
theorem R120533 : Reach 120533 := rs (se 7 (by rfl) ⟨1412, by rfl⟩) (B 2825 (by norm_num) ⟨1412, by rfl⟩ (by norm_num))
theorem R120557 : Reach 120557 := rs (se 3 (by rfl) ⟨22604, by rfl⟩) (B 45209 (by norm_num) ⟨22604, by rfl⟩ (by norm_num))
theorem R186101 : Reach 186101 := rs (se 5 (by rfl) ⟨8723, by rfl⟩) (B 17447 (by norm_num) ⟨8723, by rfl⟩ (by norm_num))
theorem R87805 : Reach 87805 := rs (se 3 (by rfl) ⟨16463, by rfl⟩) (B 32927 (by norm_num) ⟨16463, by rfl⟩ (by norm_num))
theorem R153341 : Reach 153341 := rs (se 3 (by rfl) ⟨28751, by rfl⟩) (B 57503 (by norm_num) ⟨28751, by rfl⟩ (by norm_num))
theorem R120581 : Reach 120581 := rs (se 4 (by rfl) ⟨11304, by rfl⟩) (B 22609 (by norm_num) ⟨11304, by rfl⟩ (by norm_num))
theorem R120605 : Reach 120605 := rs (se 3 (by rfl) ⟨22613, by rfl⟩) (B 45227 (by norm_num) ⟨22613, by rfl⟩ (by norm_num))
theorem R87841 : Reach 87841 := rs (se 2 (by rfl) ⟨32940, by rfl⟩) (B 65881 (by norm_num) ⟨32940, by rfl⟩ (by norm_num))
theorem R120629 : Reach 120629 := rs (se 5 (by rfl) ⟨5654, by rfl⟩) (B 11309 (by norm_num) ⟨5654, by rfl⟩ (by norm_num))
theorem R186173 : Reach 186173 := rs (se 3 (by rfl) ⟨34907, by rfl⟩) (B 69815 (by norm_num) ⟨34907, by rfl⟩ (by norm_num))
theorem R120653 : Reach 120653 := rs (se 3 (by rfl) ⟨22622, by rfl⟩) (B 45245 (by norm_num) ⟨22622, by rfl⟩ (by norm_num))
theorem R120677 : Reach 120677 := rs (se 4 (by rfl) ⟨11313, by rfl⟩) (B 22627 (by norm_num) ⟨11313, by rfl⟩ (by norm_num))
theorem R120701 : Reach 120701 := rs (se 3 (by rfl) ⟨22631, by rfl⟩) (B 45263 (by norm_num) ⟨22631, by rfl⟩ (by norm_num))
theorem R186245 : Reach 186245 := rs (se 4 (by rfl) ⟨17460, by rfl⟩) (B 34921 (by norm_num) ⟨17460, by rfl⟩ (by norm_num))
theorem R153485 : Reach 153485 := rs (se 3 (by rfl) ⟨28778, by rfl⟩) (B 57557 (by norm_num) ⟨28778, by rfl⟩ (by norm_num))
theorem R120725 : Reach 120725 := rs (se 6 (by rfl) ⟨2829, by rfl⟩) (B 5659 (by norm_num) ⟨2829, by rfl⟩ (by norm_num))
theorem R120749 : Reach 120749 := rs (se 3 (by rfl) ⟨22640, by rfl⟩) (B 45281 (by norm_num) ⟨22640, by rfl⟩ (by norm_num))
theorem R120773 : Reach 120773 := rs (se 4 (by rfl) ⟨11322, by rfl⟩) (B 22645 (by norm_num) ⟨11322, by rfl⟩ (by norm_num))
theorem R186317 : Reach 186317 := rs (se 3 (by rfl) ⟨34934, by rfl⟩) (B 69869 (by norm_num) ⟨34934, by rfl⟩ (by norm_num))
theorem R120797 : Reach 120797 := rs (se 3 (by rfl) ⟨22649, by rfl⟩) (B 45299 (by norm_num) ⟨22649, by rfl⟩ (by norm_num))
theorem R120821 : Reach 120821 := rs (se 5 (by rfl) ⟨5663, by rfl⟩) (B 11327 (by norm_num) ⟨5663, by rfl⟩ (by norm_num))
theorem R88057 : Reach 88057 := rs (se 2 (by rfl) ⟨33021, by rfl⟩) (B 66043 (by norm_num) ⟨33021, by rfl⟩ (by norm_num))
theorem R88061 : Reach 88061 := rs (se 3 (by rfl) ⟨16511, by rfl⟩) (B 33023 (by norm_num) ⟨16511, by rfl⟩ (by norm_num))
theorem R120845 : Reach 120845 := rs (se 3 (by rfl) ⟨22658, by rfl⟩) (B 45317 (by norm_num) ⟨22658, by rfl⟩ (by norm_num))
theorem R186389 : Reach 186389 := rs (se 6 (by rfl) ⟨4368, by rfl⟩) (B 8737 (by norm_num) ⟨4368, by rfl⟩ (by norm_num))
theorem R120869 : Reach 120869 := rs (se 4 (by rfl) ⟨11331, by rfl⟩) (B 22663 (by norm_num) ⟨11331, by rfl⟩ (by norm_num))
theorem R120893 : Reach 120893 := rs (se 3 (by rfl) ⟨22667, by rfl⟩) (B 45335 (by norm_num) ⟨22667, by rfl⟩ (by norm_num))
theorem R120917 : Reach 120917 := rs (se 8 (by rfl) ⟨708, by rfl⟩) (B 1417 (by norm_num) ⟨708, by rfl⟩ (by norm_num))
theorem R186461 : Reach 186461 := rs (se 3 (by rfl) ⟨34961, by rfl⟩) (B 69923 (by norm_num) ⟨34961, by rfl⟩ (by norm_num))
theorem R120941 : Reach 120941 := rs (se 3 (by rfl) ⟨22676, by rfl⟩) (B 45353 (by norm_num) ⟨22676, by rfl⟩ (by norm_num))
theorem R120965 : Reach 120965 := rs (se 4 (by rfl) ⟨11340, by rfl⟩) (B 22681 (by norm_num) ⟨11340, by rfl⟩ (by norm_num))
theorem R120989 : Reach 120989 := rs (se 3 (by rfl) ⟨22685, by rfl⟩) (B 45371 (by norm_num) ⟨22685, by rfl⟩ (by norm_num))
theorem R186533 : Reach 186533 := rs (se 4 (by rfl) ⟨17487, by rfl⟩) (B 34975 (by norm_num) ⟨17487, by rfl⟩ (by norm_num))
theorem R121013 : Reach 121013 := rs (se 5 (by rfl) ⟨5672, by rfl⟩) (B 11345 (by norm_num) ⟨5672, by rfl⟩ (by norm_num))
theorem R121037 : Reach 121037 := rs (se 3 (by rfl) ⟨22694, by rfl⟩) (B 45389 (by norm_num) ⟨22694, by rfl⟩ (by norm_num))
theorem R121061 : Reach 121061 := rs (se 4 (by rfl) ⟨11349, by rfl⟩) (B 22699 (by norm_num) ⟨11349, by rfl⟩ (by norm_num))
theorem R186605 : Reach 186605 := rs (se 3 (by rfl) ⟨34988, by rfl⟩) (B 69977 (by norm_num) ⟨34988, by rfl⟩ (by norm_num))
theorem R121085 : Reach 121085 := rs (se 3 (by rfl) ⟨22703, by rfl⟩) (B 45407 (by norm_num) ⟨22703, by rfl⟩ (by norm_num))
theorem R121109 : Reach 121109 := rs (se 6 (by rfl) ⟨2838, by rfl⟩) (B 5677 (by norm_num) ⟨2838, by rfl⟩ (by norm_num))
theorem R121133 : Reach 121133 := rs (se 3 (by rfl) ⟨22712, by rfl⟩) (B 45425 (by norm_num) ⟨22712, by rfl⟩ (by norm_num))
theorem R186677 : Reach 186677 := rs (se 5 (by rfl) ⟨8750, by rfl⟩) (B 17501 (by norm_num) ⟨8750, by rfl⟩ (by norm_num))
theorem R121157 : Reach 121157 := rs (se 4 (by rfl) ⟨11358, by rfl⟩) (B 22717 (by norm_num) ⟨11358, by rfl⟩ (by norm_num))
theorem R121181 : Reach 121181 := rs (se 3 (by rfl) ⟨22721, by rfl⟩) (B 45443 (by norm_num) ⟨22721, by rfl⟩ (by norm_num))
theorem R121205 : Reach 121205 := rs (se 5 (by rfl) ⟨5681, by rfl⟩) (B 11363 (by norm_num) ⟨5681, by rfl⟩ (by norm_num))
theorem R186749 : Reach 186749 := rs (se 3 (by rfl) ⟨35015, by rfl⟩) (B 70031 (by norm_num) ⟨35015, by rfl⟩ (by norm_num))
theorem R121229 : Reach 121229 := rs (se 3 (by rfl) ⟨22730, by rfl⟩) (B 45461 (by norm_num) ⟨22730, by rfl⟩ (by norm_num))
theorem R121253 : Reach 121253 := rs (se 4 (by rfl) ⟨11367, by rfl⟩) (B 22735 (by norm_num) ⟨11367, by rfl⟩ (by norm_num))
theorem R121277 : Reach 121277 := rs (se 3 (by rfl) ⟨22739, by rfl⟩) (B 45479 (by norm_num) ⟨22739, by rfl⟩ (by norm_num))
theorem R186821 : Reach 186821 := rs (se 4 (by rfl) ⟨17514, by rfl⟩) (B 35029 (by norm_num) ⟨17514, by rfl⟩ (by norm_num))
theorem R121301 : Reach 121301 := rs (se 7 (by rfl) ⟨1421, by rfl⟩) (B 2843 (by norm_num) ⟨1421, by rfl⟩ (by norm_num))
theorem R121325 : Reach 121325 := rs (se 3 (by rfl) ⟨22748, by rfl⟩) (B 45497 (by norm_num) ⟨22748, by rfl⟩ (by norm_num))
theorem R121349 : Reach 121349 := rs (se 4 (by rfl) ⟨11376, by rfl⟩) (B 22753 (by norm_num) ⟨11376, by rfl⟩ (by norm_num))
theorem R186893 : Reach 186893 := rs (se 3 (by rfl) ⟨35042, by rfl⟩) (B 70085 (by norm_num) ⟨35042, by rfl⟩ (by norm_num))
theorem R121373 : Reach 121373 := rs (se 3 (by rfl) ⟨22757, by rfl⟩) (B 45515 (by norm_num) ⟨22757, by rfl⟩ (by norm_num))
theorem R88625 : Reach 88625 := rs (se 2 (by rfl) ⟨33234, by rfl⟩) (B 66469 (by norm_num) ⟨33234, by rfl⟩ (by norm_num))
theorem R121397 : Reach 121397 := rs (se 5 (by rfl) ⟨5690, by rfl⟩) (B 11381 (by norm_num) ⟨5690, by rfl⟩ (by norm_num))
theorem R121421 : Reach 121421 := rs (se 3 (by rfl) ⟨22766, by rfl⟩) (B 45533 (by norm_num) ⟨22766, by rfl⟩ (by norm_num))
theorem R186965 : Reach 186965 := rs (se 8 (by rfl) ⟨1095, by rfl⟩) (B 2191 (by norm_num) ⟨1095, by rfl⟩ (by norm_num))
theorem R121445 : Reach 121445 := rs (se 4 (by rfl) ⟨11385, by rfl⟩) (B 22771 (by norm_num) ⟨11385, by rfl⟩ (by norm_num))
theorem R121469 : Reach 121469 := rs (se 3 (by rfl) ⟨22775, by rfl⟩) (B 45551 (by norm_num) ⟨22775, by rfl⟩ (by norm_num))
theorem R154237 : Reach 154237 := rs (se 3 (by rfl) ⟨28919, by rfl⟩) (B 57839 (by norm_num) ⟨28919, by rfl⟩ (by norm_num))
theorem R121493 : Reach 121493 := rs (se 6 (by rfl) ⟨2847, by rfl⟩) (B 5695 (by norm_num) ⟨2847, by rfl⟩ (by norm_num))
theorem R187037 : Reach 187037 := rs (se 3 (by rfl) ⟨35069, by rfl⟩) (B 70139 (by norm_num) ⟨35069, by rfl⟩ (by norm_num))
theorem R121517 : Reach 121517 := rs (se 3 (by rfl) ⟨22784, by rfl⟩) (B 45569 (by norm_num) ⟨22784, by rfl⟩ (by norm_num))
theorem R121541 : Reach 121541 := rs (se 4 (by rfl) ⟨11394, by rfl⟩) (B 22789 (by norm_num) ⟨11394, by rfl⟩ (by norm_num))
theorem R121565 : Reach 121565 := rs (se 3 (by rfl) ⟨22793, by rfl⟩) (B 45587 (by norm_num) ⟨22793, by rfl⟩ (by norm_num))
theorem R219877 : Reach 219877 := rs (se 4 (by rfl) ⟨20613, by rfl⟩) (B 41227 (by norm_num) ⟨20613, by rfl⟩ (by norm_num))
theorem R121589 : Reach 121589 := rs (se 5 (by rfl) ⟨5699, by rfl⟩) (B 11399 (by norm_num) ⟨5699, by rfl⟩ (by norm_num))
theorem R416501 : Reach 416501 := rs (se 5 (by rfl) ⟨19523, by rfl⟩) (B 39047 (by norm_num) ⟨19523, by rfl⟩ (by norm_num))
theorem R121613 : Reach 121613 := rs (se 3 (by rfl) ⟨22802, by rfl⟩) (B 45605 (by norm_num) ⟨22802, by rfl⟩ (by norm_num))
theorem R154381 : Reach 154381 := rs (se 3 (by rfl) ⟨28946, by rfl⟩) (B 57893 (by norm_num) ⟨28946, by rfl⟩ (by norm_num))
theorem R121637 : Reach 121637 := rs (se 4 (by rfl) ⟨11403, by rfl⟩) (B 22807 (by norm_num) ⟨11403, by rfl⟩ (by norm_num))
theorem R121661 : Reach 121661 := rs (se 3 (by rfl) ⟨22811, by rfl⟩) (B 45623 (by norm_num) ⟨22811, by rfl⟩ (by norm_num))
theorem R121685 : Reach 121685 := rs (se 9 (by rfl) ⟨356, by rfl⟩) (B 713 (by norm_num) ⟨356, by rfl⟩ (by norm_num))
theorem R121709 : Reach 121709 := rs (se 3 (by rfl) ⟨22820, by rfl⟩) (B 45641 (by norm_num) ⟨22820, by rfl⟩ (by norm_num))
theorem R121733 : Reach 121733 := rs (se 4 (by rfl) ⟨11412, by rfl⟩) (B 22825 (by norm_num) ⟨11412, by rfl⟩ (by norm_num))
theorem R121757 : Reach 121757 := rs (se 3 (by rfl) ⟨22829, by rfl⟩) (B 45659 (by norm_num) ⟨22829, by rfl⟩ (by norm_num))
theorem R154541 : Reach 154541 := rs (se 3 (by rfl) ⟨28976, by rfl⟩) (B 57953 (by norm_num) ⟨28976, by rfl⟩ (by norm_num))
theorem R121781 : Reach 121781 := rs (se 5 (by rfl) ⟨5708, by rfl⟩) (B 11417 (by norm_num) ⟨5708, by rfl⟩ (by norm_num))
theorem R121805 : Reach 121805 := rs (se 3 (by rfl) ⟨22838, by rfl⟩) (B 45677 (by norm_num) ⟨22838, by rfl⟩ (by norm_num))
theorem R89041 : Reach 89041 := rs (se 2 (by rfl) ⟨33390, by rfl⟩) (B 66781 (by norm_num) ⟨33390, by rfl⟩ (by norm_num))
theorem R121829 : Reach 121829 := rs (se 4 (by rfl) ⟨11421, by rfl⟩) (B 22843 (by norm_num) ⟨11421, by rfl⟩ (by norm_num))
theorem R89077 : Reach 89077 := rs (se 5 (by rfl) ⟨4175, by rfl⟩) (B 8351 (by norm_num) ⟨4175, by rfl⟩ (by norm_num))
theorem R121853 : Reach 121853 := rs (se 3 (by rfl) ⟨22847, by rfl⟩) (B 45695 (by norm_num) ⟨22847, by rfl⟩ (by norm_num))
theorem R121877 : Reach 121877 := rs (se 6 (by rfl) ⟨2856, by rfl⟩) (B 5713 (by norm_num) ⟨2856, by rfl⟩ (by norm_num))
theorem R89113 : Reach 89113 := rs (se 2 (by rfl) ⟨33417, by rfl⟩) (B 66835 (by norm_num) ⟨33417, by rfl⟩ (by norm_num))
theorem R121901 : Reach 121901 := rs (se 3 (by rfl) ⟨22856, by rfl⟩) (B 45713 (by norm_num) ⟨22856, by rfl⟩ (by norm_num))
theorem R154685 : Reach 154685 := rs (se 3 (by rfl) ⟨29003, by rfl⟩) (B 58007 (by norm_num) ⟨29003, by rfl⟩ (by norm_num))
theorem R89149 : Reach 89149 := rs (se 3 (by rfl) ⟨16715, by rfl⟩) (B 33431 (by norm_num) ⟨16715, by rfl⟩ (by norm_num))
theorem R121925 : Reach 121925 := rs (se 4 (by rfl) ⟨11430, by rfl⟩) (B 22861 (by norm_num) ⟨11430, by rfl⟩ (by norm_num))
theorem R121949 : Reach 121949 := rs (se 3 (by rfl) ⟨22865, by rfl⟩) (B 45731 (by norm_num) ⟨22865, by rfl⟩ (by norm_num))
theorem R89185 : Reach 89185 := rs (se 2 (by rfl) ⟨33444, by rfl⟩) (B 66889 (by norm_num) ⟨33444, by rfl⟩ (by norm_num))
theorem R121973 : Reach 121973 := rs (se 5 (by rfl) ⟨5717, by rfl⟩) (B 11435 (by norm_num) ⟨5717, by rfl⟩ (by norm_num))
theorem R89221 : Reach 89221 := rs (se 4 (by rfl) ⟨8364, by rfl⟩) (B 16729 (by norm_num) ⟨8364, by rfl⟩ (by norm_num))
theorem R121997 : Reach 121997 := rs (se 3 (by rfl) ⟨22874, by rfl⟩) (B 45749 (by norm_num) ⟨22874, by rfl⟩ (by norm_num))
theorem R122021 : Reach 122021 := rs (se 4 (by rfl) ⟨11439, by rfl⟩) (B 22879 (by norm_num) ⟨11439, by rfl⟩ (by norm_num))
theorem R89257 : Reach 89257 := rs (se 2 (by rfl) ⟨33471, by rfl⟩) (B 66943 (by norm_num) ⟨33471, by rfl⟩ (by norm_num))
theorem R122045 : Reach 122045 := rs (se 3 (by rfl) ⟨22883, by rfl⟩) (B 45767 (by norm_num) ⟨22883, by rfl⟩ (by norm_num))
theorem R89293 : Reach 89293 := rs (se 3 (by rfl) ⟨16742, by rfl⟩) (B 33485 (by norm_num) ⟨16742, by rfl⟩ (by norm_num))
theorem R122069 : Reach 122069 := rs (se 7 (by rfl) ⟨1430, by rfl⟩) (B 2861 (by norm_num) ⟨1430, by rfl⟩ (by norm_num))
theorem R122093 : Reach 122093 := rs (se 3 (by rfl) ⟨22892, by rfl⟩) (B 45785 (by norm_num) ⟨22892, by rfl⟩ (by norm_num))
theorem R89329 : Reach 89329 := rs (se 2 (by rfl) ⟨33498, by rfl⟩) (B 66997 (by norm_num) ⟨33498, by rfl⟩ (by norm_num))
theorem R122117 : Reach 122117 := rs (se 4 (by rfl) ⟨11448, by rfl⟩) (B 22897 (by norm_num) ⟨11448, by rfl⟩ (by norm_num))
theorem R89365 : Reach 89365 := rs (se 6 (by rfl) ⟨2094, by rfl⟩) (B 4189 (by norm_num) ⟨2094, by rfl⟩ (by norm_num))
theorem R122141 : Reach 122141 := rs (se 3 (by rfl) ⟨22901, by rfl⟩) (B 45803 (by norm_num) ⟨22901, by rfl⟩ (by norm_num))
theorem R122165 : Reach 122165 := rs (se 5 (by rfl) ⟨5726, by rfl⟩) (B 11453 (by norm_num) ⟨5726, by rfl⟩ (by norm_num))
theorem R89401 : Reach 89401 := rs (se 2 (by rfl) ⟨33525, by rfl⟩) (B 67051 (by norm_num) ⟨33525, by rfl⟩ (by norm_num))
theorem R122189 : Reach 122189 := rs (se 3 (by rfl) ⟨22910, by rfl⟩) (B 45821 (by norm_num) ⟨22910, by rfl⟩ (by norm_num))
theorem R154973 : Reach 154973 := rs (se 3 (by rfl) ⟨29057, by rfl⟩) (B 58115 (by norm_num) ⟨29057, by rfl⟩ (by norm_num))
theorem R89437 : Reach 89437 := rs (se 3 (by rfl) ⟨16769, by rfl⟩) (B 33539 (by norm_num) ⟨16769, by rfl⟩ (by norm_num))
theorem R122213 : Reach 122213 := rs (se 4 (by rfl) ⟨11457, by rfl⟩) (B 22915 (by norm_num) ⟨11457, by rfl⟩ (by norm_num))
theorem R122237 : Reach 122237 := rs (se 3 (by rfl) ⟨22919, by rfl⟩) (B 45839 (by norm_num) ⟨22919, by rfl⟩ (by norm_num))
theorem R89473 : Reach 89473 := rs (se 2 (by rfl) ⟨33552, by rfl⟩) (B 67105 (by norm_num) ⟨33552, by rfl⟩ (by norm_num))
theorem R122261 : Reach 122261 := rs (se 6 (by rfl) ⟨2865, by rfl⟩) (B 5731 (by norm_num) ⟨2865, by rfl⟩ (by norm_num))
theorem R89509 : Reach 89509 := rs (se 4 (by rfl) ⟨8391, by rfl⟩) (B 16783 (by norm_num) ⟨8391, by rfl⟩ (by norm_num))
theorem R122285 : Reach 122285 := rs (se 3 (by rfl) ⟨22928, by rfl⟩) (B 45857 (by norm_num) ⟨22928, by rfl⟩ (by norm_num))
theorem R122309 : Reach 122309 := rs (se 4 (by rfl) ⟨11466, by rfl⟩) (B 22933 (by norm_num) ⟨11466, by rfl⟩ (by norm_num))
theorem R89545 : Reach 89545 := rs (se 2 (by rfl) ⟨33579, by rfl⟩) (B 67159 (by norm_num) ⟨33579, by rfl⟩ (by norm_num))
theorem R122333 : Reach 122333 := rs (se 3 (by rfl) ⟨22937, by rfl⟩) (B 45875 (by norm_num) ⟨22937, by rfl⟩ (by norm_num))
theorem R89581 : Reach 89581 := rs (se 3 (by rfl) ⟨16796, by rfl⟩) (B 33593 (by norm_num) ⟨16796, by rfl⟩ (by norm_num))
theorem R155125 : Reach 155125 := rs (se 5 (by rfl) ⟨7271, by rfl⟩) (B 14543 (by norm_num) ⟨7271, by rfl⟩ (by norm_num))
theorem R122357 : Reach 122357 := rs (se 5 (by rfl) ⟨5735, by rfl⟩) (B 11471 (by norm_num) ⟨5735, by rfl⟩ (by norm_num))
theorem R122381 : Reach 122381 := rs (se 3 (by rfl) ⟨22946, by rfl⟩) (B 45893 (by norm_num) ⟨22946, by rfl⟩ (by norm_num))
theorem R89617 : Reach 89617 := rs (se 2 (by rfl) ⟨33606, by rfl⟩) (B 67213 (by norm_num) ⟨33606, by rfl⟩ (by norm_num))
theorem R122405 : Reach 122405 := rs (se 4 (by rfl) ⟨11475, by rfl⟩) (B 22951 (by norm_num) ⟨11475, by rfl⟩ (by norm_num))
theorem R89653 : Reach 89653 := rs (se 5 (by rfl) ⟨4202, by rfl⟩) (B 8405 (by norm_num) ⟨4202, by rfl⟩ (by norm_num))
theorem R122429 : Reach 122429 := rs (se 3 (by rfl) ⟨22955, by rfl⟩) (B 45911 (by norm_num) ⟨22955, by rfl⟩ (by norm_num))
theorem R122453 : Reach 122453 := rs (se 8 (by rfl) ⟨717, by rfl⟩) (B 1435 (by norm_num) ⟨717, by rfl⟩ (by norm_num))
theorem R89689 : Reach 89689 := rs (se 2 (by rfl) ⟨33633, by rfl⟩) (B 67267 (by norm_num) ⟨33633, by rfl⟩ (by norm_num))
theorem R122477 : Reach 122477 := rs (se 3 (by rfl) ⟨22964, by rfl⟩) (B 45929 (by norm_num) ⟨22964, by rfl⟩ (by norm_num))
theorem R89725 : Reach 89725 := rs (se 3 (by rfl) ⟨16823, by rfl⟩) (B 33647 (by norm_num) ⟨16823, by rfl⟩ (by norm_num))
theorem R122501 : Reach 122501 := rs (se 4 (by rfl) ⟨11484, by rfl⟩) (B 22969 (by norm_num) ⟨11484, by rfl⟩ (by norm_num))
theorem R122525 : Reach 122525 := rs (se 3 (by rfl) ⟨22973, by rfl⟩) (B 45947 (by norm_num) ⟨22973, by rfl⟩ (by norm_num))
theorem R89761 : Reach 89761 := rs (se 2 (by rfl) ⟨33660, by rfl⟩) (B 67321 (by norm_num) ⟨33660, by rfl⟩ (by norm_num))
theorem R122549 : Reach 122549 := rs (se 5 (by rfl) ⟨5744, by rfl⟩) (B 11489 (by norm_num) ⟨5744, by rfl⟩ (by norm_num))
theorem R89797 : Reach 89797 := rs (se 4 (by rfl) ⟨8418, by rfl⟩) (B 16837 (by norm_num) ⟨8418, by rfl⟩ (by norm_num))
theorem R122573 : Reach 122573 := rs (se 3 (by rfl) ⟨22982, by rfl⟩) (B 45965 (by norm_num) ⟨22982, by rfl⟩ (by norm_num))
theorem R122597 : Reach 122597 := rs (se 4 (by rfl) ⟨11493, by rfl⟩) (B 22987 (by norm_num) ⟨11493, by rfl⟩ (by norm_num))
theorem R89833 : Reach 89833 := rs (se 2 (by rfl) ⟨33687, by rfl⟩) (B 67375 (by norm_num) ⟨33687, by rfl⟩ (by norm_num))
theorem R122621 : Reach 122621 := rs (se 3 (by rfl) ⟨22991, by rfl⟩) (B 45983 (by norm_num) ⟨22991, by rfl⟩ (by norm_num))
theorem R89869 : Reach 89869 := rs (se 3 (by rfl) ⟨16850, by rfl⟩) (B 33701 (by norm_num) ⟨16850, by rfl⟩ (by norm_num))
theorem R122645 : Reach 122645 := rs (se 6 (by rfl) ⟨2874, by rfl⟩) (B 5749 (by norm_num) ⟨2874, by rfl⟩ (by norm_num))
theorem R155429 : Reach 155429 := rs (se 4 (by rfl) ⟨14571, by rfl⟩) (B 29143 (by norm_num) ⟨14571, by rfl⟩ (by norm_num))
theorem R122669 : Reach 122669 := rs (se 3 (by rfl) ⟨23000, by rfl⟩) (B 46001 (by norm_num) ⟨23000, by rfl⟩ (by norm_num))
theorem R89905 : Reach 89905 := rs (se 2 (by rfl) ⟨33714, by rfl⟩) (B 67429 (by norm_num) ⟨33714, by rfl⟩ (by norm_num))
theorem R384821 : Reach 384821 := rs (se 5 (by rfl) ⟨18038, by rfl⟩) (B 36077 (by norm_num) ⟨18038, by rfl⟩ (by norm_num))
theorem R122693 : Reach 122693 := rs (se 4 (by rfl) ⟨11502, by rfl⟩) (B 23005 (by norm_num) ⟨11502, by rfl⟩ (by norm_num))
theorem R89941 : Reach 89941 := rs (se 9 (by rfl) ⟨263, by rfl⟩) (B 527 (by norm_num) ⟨263, by rfl⟩ (by norm_num))
theorem R122717 : Reach 122717 := rs (se 3 (by rfl) ⟨23009, by rfl⟩) (B 46019 (by norm_num) ⟨23009, by rfl⟩ (by norm_num))
theorem R122741 : Reach 122741 := rs (se 5 (by rfl) ⟨5753, by rfl⟩) (B 11507 (by norm_num) ⟨5753, by rfl⟩ (by norm_num))
theorem R89977 : Reach 89977 := rs (se 2 (by rfl) ⟨33741, by rfl⟩) (B 67483 (by norm_num) ⟨33741, by rfl⟩ (by norm_num))
theorem R253829 : Reach 253829 := rs (se 4 (by rfl) ⟨23796, by rfl⟩) (B 47593 (by norm_num) ⟨23796, by rfl⟩ (by norm_num))
theorem R122765 : Reach 122765 := rs (se 3 (by rfl) ⟨23018, by rfl⟩) (B 46037 (by norm_num) ⟨23018, by rfl⟩ (by norm_num))
theorem R90013 : Reach 90013 := rs (se 3 (by rfl) ⟨16877, by rfl⟩) (B 33755 (by norm_num) ⟨16877, by rfl⟩ (by norm_num))
theorem R122789 : Reach 122789 := rs (se 4 (by rfl) ⟨11511, by rfl⟩) (B 23023 (by norm_num) ⟨11511, by rfl⟩ (by norm_num))
theorem R122813 : Reach 122813 := rs (se 3 (by rfl) ⟨23027, by rfl⟩) (B 46055 (by norm_num) ⟨23027, by rfl⟩ (by norm_num))
theorem R90049 : Reach 90049 := rs (se 2 (by rfl) ⟨33768, by rfl⟩) (B 67537 (by norm_num) ⟨33768, by rfl⟩ (by norm_num))
theorem R122837 : Reach 122837 := rs (se 7 (by rfl) ⟨1439, by rfl⟩) (B 2879 (by norm_num) ⟨1439, by rfl⟩ (by norm_num))
theorem R90085 : Reach 90085 := rs (se 4 (by rfl) ⟨8445, by rfl⟩) (B 16891 (by norm_num) ⟨8445, by rfl⟩ (by norm_num))
theorem R122861 : Reach 122861 := rs (se 3 (by rfl) ⟨23036, by rfl⟩) (B 46073 (by norm_num) ⟨23036, by rfl⟩ (by norm_num))
theorem R122885 : Reach 122885 := rs (se 4 (by rfl) ⟨11520, by rfl⟩) (B 23041 (by norm_num) ⟨11520, by rfl⟩ (by norm_num))
theorem R417797 : Reach 417797 := rs (se 4 (by rfl) ⟨39168, by rfl⟩) (B 78337 (by norm_num) ⟨39168, by rfl⟩ (by norm_num))
theorem R90121 : Reach 90121 := rs (se 2 (by rfl) ⟨33795, by rfl⟩) (B 67591 (by norm_num) ⟨33795, by rfl⟩ (by norm_num))
theorem R122909 : Reach 122909 := rs (se 3 (by rfl) ⟨23045, by rfl⟩) (B 46091 (by norm_num) ⟨23045, by rfl⟩ (by norm_num))
theorem R90157 : Reach 90157 := rs (se 3 (by rfl) ⟨16904, by rfl⟩) (B 33809 (by norm_num) ⟨16904, by rfl⟩ (by norm_num))
theorem R122933 : Reach 122933 := rs (se 5 (by rfl) ⟨5762, by rfl⟩) (B 11525 (by norm_num) ⟨5762, by rfl⟩ (by norm_num))
theorem R122957 : Reach 122957 := rs (se 3 (by rfl) ⟨23054, by rfl⟩) (B 46109 (by norm_num) ⟨23054, by rfl⟩ (by norm_num))
theorem R90193 : Reach 90193 := rs (se 2 (by rfl) ⟨33822, by rfl⟩) (B 67645 (by norm_num) ⟨33822, by rfl⟩ (by norm_num))
theorem R680021 : Reach 680021 := rs (se 8 (by rfl) ⟨3984, by rfl⟩) (B 7969 (by norm_num) ⟨3984, by rfl⟩ (by norm_num))
theorem R122981 : Reach 122981 := rs (se 4 (by rfl) ⟨11529, by rfl⟩) (B 23059 (by norm_num) ⟨11529, by rfl⟩ (by norm_num))
theorem R90229 : Reach 90229 := rs (se 5 (by rfl) ⟨4229, by rfl⟩) (B 8459 (by norm_num) ⟨4229, by rfl⟩ (by norm_num))
theorem R123005 : Reach 123005 := rs (se 3 (by rfl) ⟨23063, by rfl⟩) (B 46127 (by norm_num) ⟨23063, by rfl⟩ (by norm_num))
theorem R123029 : Reach 123029 := rs (se 6 (by rfl) ⟨2883, by rfl⟩) (B 5767 (by norm_num) ⟨2883, by rfl⟩ (by norm_num))
theorem R90265 : Reach 90265 := rs (se 2 (by rfl) ⟨33849, by rfl⟩) (B 67699 (by norm_num) ⟨33849, by rfl⟩ (by norm_num))
theorem R123053 : Reach 123053 := rs (se 3 (by rfl) ⟨23072, by rfl⟩) (B 46145 (by norm_num) ⟨23072, by rfl⟩ (by norm_num))
theorem R90301 : Reach 90301 := rs (se 3 (by rfl) ⟨16931, by rfl⟩) (B 33863 (by norm_num) ⟨16931, by rfl⟩ (by norm_num))
theorem R123077 : Reach 123077 := rs (se 4 (by rfl) ⟨11538, by rfl⟩) (B 23077 (by norm_num) ⟨11538, by rfl⟩ (by norm_num))
theorem R123101 : Reach 123101 := rs (se 3 (by rfl) ⟨23081, by rfl⟩) (B 46163 (by norm_num) ⟨23081, by rfl⟩ (by norm_num))
theorem R90337 : Reach 90337 := rs (se 2 (by rfl) ⟨33876, by rfl⟩) (B 67753 (by norm_num) ⟨33876, by rfl⟩ (by norm_num))
theorem R123125 : Reach 123125 := rs (se 5 (by rfl) ⟨5771, by rfl⟩) (B 11543 (by norm_num) ⟨5771, by rfl⟩ (by norm_num))
theorem R90373 : Reach 90373 := rs (se 4 (by rfl) ⟨8472, by rfl⟩) (B 16945 (by norm_num) ⟨8472, by rfl⟩ (by norm_num))
theorem R123149 : Reach 123149 := rs (se 3 (by rfl) ⟨23090, by rfl⟩) (B 46181 (by norm_num) ⟨23090, by rfl⟩ (by norm_num))
theorem R123173 : Reach 123173 := rs (se 4 (by rfl) ⟨11547, by rfl⟩) (B 23095 (by norm_num) ⟨11547, by rfl⟩ (by norm_num))
theorem R90409 : Reach 90409 := rs (se 2 (by rfl) ⟨33903, by rfl⟩) (B 67807 (by norm_num) ⟨33903, by rfl⟩ (by norm_num))
theorem R123197 : Reach 123197 := rs (se 3 (by rfl) ⟨23099, by rfl⟩) (B 46199 (by norm_num) ⟨23099, by rfl⟩ (by norm_num))
theorem R90445 : Reach 90445 := rs (se 3 (by rfl) ⟨16958, by rfl⟩) (B 33917 (by norm_num) ⟨16958, by rfl⟩ (by norm_num))
theorem R123221 : Reach 123221 := rs (se 10 (by rfl) ⟨180, by rfl⟩) (B 361 (by norm_num) ⟨180, by rfl⟩ (by norm_num))
theorem R123245 : Reach 123245 := rs (se 3 (by rfl) ⟨23108, by rfl⟩) (B 46217 (by norm_num) ⟨23108, by rfl⟩ (by norm_num))
theorem R90481 : Reach 90481 := rs (se 2 (by rfl) ⟨33930, by rfl⟩) (B 67861 (by norm_num) ⟨33930, by rfl⟩ (by norm_num))
theorem R123269 : Reach 123269 := rs (se 4 (by rfl) ⟨11556, by rfl⟩) (B 23113 (by norm_num) ⟨11556, by rfl⟩ (by norm_num))
theorem R90517 : Reach 90517 := rs (se 6 (by rfl) ⟨2121, by rfl⟩) (B 4243 (by norm_num) ⟨2121, by rfl⟩ (by norm_num))
theorem R123293 : Reach 123293 := rs (se 3 (by rfl) ⟨23117, by rfl⟩) (B 46235 (by norm_num) ⟨23117, by rfl⟩ (by norm_num))
theorem R123317 : Reach 123317 := rs (se 5 (by rfl) ⟨5780, by rfl⟩) (B 11561 (by norm_num) ⟨5780, by rfl⟩ (by norm_num))
theorem R90553 : Reach 90553 := rs (se 2 (by rfl) ⟨33957, by rfl⟩) (B 67915 (by norm_num) ⟨33957, by rfl⟩ (by norm_num))
theorem R123341 : Reach 123341 := rs (se 3 (by rfl) ⟨23126, by rfl⟩) (B 46253 (by norm_num) ⟨23126, by rfl⟩ (by norm_num))
theorem R778709 : Reach 778709 := rs (se 7 (by rfl) ⟨9125, by rfl⟩) (B 18251 (by norm_num) ⟨9125, by rfl⟩ (by norm_num))
theorem R90589 : Reach 90589 := rs (se 3 (by rfl) ⟨16985, by rfl⟩) (B 33971 (by norm_num) ⟨16985, by rfl⟩ (by norm_num))
theorem R123365 : Reach 123365 := rs (se 4 (by rfl) ⟨11565, by rfl⟩) (B 23131 (by norm_num) ⟨11565, by rfl⟩ (by norm_num))
theorem R123389 : Reach 123389 := rs (se 3 (by rfl) ⟨23135, by rfl⟩) (B 46271 (by norm_num) ⟨23135, by rfl⟩ (by norm_num))
theorem R90625 : Reach 90625 := rs (se 2 (by rfl) ⟨33984, by rfl⟩) (B 67969 (by norm_num) ⟨33984, by rfl⟩ (by norm_num))
theorem R221717 : Reach 221717 := rs (se 6 (by rfl) ⟨5196, by rfl⟩) (B 10393 (by norm_num) ⟨5196, by rfl⟩ (by norm_num))
theorem R156181 : Reach 156181 := rs (se 6 (by rfl) ⟨3660, by rfl⟩) (B 7321 (by norm_num) ⟨3660, by rfl⟩ (by norm_num))
theorem R123413 : Reach 123413 := rs (se 6 (by rfl) ⟨2892, by rfl⟩) (B 5785 (by norm_num) ⟨2892, by rfl⟩ (by norm_num))
theorem R90661 : Reach 90661 := rs (se 4 (by rfl) ⟨8499, by rfl⟩) (B 16999 (by norm_num) ⟨8499, by rfl⟩ (by norm_num))
theorem R123437 : Reach 123437 := rs (se 3 (by rfl) ⟨23144, by rfl⟩) (B 46289 (by norm_num) ⟨23144, by rfl⟩ (by norm_num))
theorem R123461 : Reach 123461 := rs (se 4 (by rfl) ⟨11574, by rfl⟩) (B 23149 (by norm_num) ⟨11574, by rfl⟩ (by norm_num))
theorem R90697 : Reach 90697 := rs (se 2 (by rfl) ⟨34011, by rfl⟩) (B 68023 (by norm_num) ⟨34011, by rfl⟩ (by norm_num))
theorem R287317 : Reach 287317 := rs (se 8 (by rfl) ⟨1683, by rfl⟩) (B 3367 (by norm_num) ⟨1683, by rfl⟩ (by norm_num))
theorem R123485 : Reach 123485 := rs (se 3 (by rfl) ⟨23153, by rfl⟩) (B 46307 (by norm_num) ⟨23153, by rfl⟩ (by norm_num))
theorem R90733 : Reach 90733 := rs (se 3 (by rfl) ⟨17012, by rfl⟩) (B 34025 (by norm_num) ⟨17012, by rfl⟩ (by norm_num))
theorem R123509 : Reach 123509 := rs (se 5 (by rfl) ⟨5789, by rfl⟩) (B 11579 (by norm_num) ⟨5789, by rfl⟩ (by norm_num))
theorem R123533 : Reach 123533 := rs (se 3 (by rfl) ⟨23162, by rfl⟩) (B 46325 (by norm_num) ⟨23162, by rfl⟩ (by norm_num))
theorem R90769 : Reach 90769 := rs (se 2 (by rfl) ⟨34038, by rfl⟩) (B 68077 (by norm_num) ⟨34038, by rfl⟩ (by norm_num))
theorem R156325 : Reach 156325 := rs (se 4 (by rfl) ⟨14655, by rfl⟩) (B 29311 (by norm_num) ⟨14655, by rfl⟩ (by norm_num))
theorem R123557 : Reach 123557 := rs (se 4 (by rfl) ⟨11583, by rfl⟩) (B 23167 (by norm_num) ⟨11583, by rfl⟩ (by norm_num))
theorem R90805 : Reach 90805 := rs (se 5 (by rfl) ⟨4256, by rfl⟩) (B 8513 (by norm_num) ⟨4256, by rfl⟩ (by norm_num))
theorem R123581 : Reach 123581 := rs (se 3 (by rfl) ⟨23171, by rfl⟩) (B 46343 (by norm_num) ⟨23171, by rfl⟩ (by norm_num))
theorem R123605 : Reach 123605 := rs (se 7 (by rfl) ⟨1448, by rfl⟩) (B 2897 (by norm_num) ⟨1448, by rfl⟩ (by norm_num))
theorem R90841 : Reach 90841 := rs (se 2 (by rfl) ⟨34065, by rfl⟩) (B 68131 (by norm_num) ⟨34065, by rfl⟩ (by norm_num))
theorem R352997 : Reach 352997 := rs (se 4 (by rfl) ⟨33093, by rfl⟩) (B 66187 (by norm_num) ⟨33093, by rfl⟩ (by norm_num))
theorem R123629 : Reach 123629 := rs (se 3 (by rfl) ⟨23180, by rfl⟩) (B 46361 (by norm_num) ⟨23180, by rfl⟩ (by norm_num))
theorem R90877 : Reach 90877 := rs (se 3 (by rfl) ⟨17039, by rfl⟩) (B 34079 (by norm_num) ⟨17039, by rfl⟩ (by norm_num))
theorem R123653 : Reach 123653 := rs (se 4 (by rfl) ⟨11592, by rfl⟩) (B 23185 (by norm_num) ⟨11592, by rfl⟩ (by norm_num))
theorem R123677 : Reach 123677 := rs (se 3 (by rfl) ⟨23189, by rfl⟩) (B 46379 (by norm_num) ⟨23189, by rfl⟩ (by norm_num))
theorem R90913 : Reach 90913 := rs (se 2 (by rfl) ⟨34092, by rfl⟩) (B 68185 (by norm_num) ⟨34092, by rfl⟩ (by norm_num))
theorem R123701 : Reach 123701 := rs (se 5 (by rfl) ⟨5798, by rfl⟩) (B 11597 (by norm_num) ⟨5798, by rfl⟩ (by norm_num))
theorem R90949 : Reach 90949 := rs (se 4 (by rfl) ⟨8526, by rfl⟩) (B 17053 (by norm_num) ⟨8526, by rfl⟩ (by norm_num))
theorem R156485 : Reach 156485 := rs (se 4 (by rfl) ⟨14670, by rfl⟩) (B 29341 (by norm_num) ⟨14670, by rfl⟩ (by norm_num))
theorem R123725 : Reach 123725 := rs (se 3 (by rfl) ⟨23198, by rfl⟩) (B 46397 (by norm_num) ⟨23198, by rfl⟩ (by norm_num))
theorem R123749 : Reach 123749 := rs (se 4 (by rfl) ⟨11601, by rfl⟩) (B 23203 (by norm_num) ⟨11601, by rfl⟩ (by norm_num))
theorem R90985 : Reach 90985 := rs (se 2 (by rfl) ⟨34119, by rfl⟩) (B 68239 (by norm_num) ⟨34119, by rfl⟩ (by norm_num))
theorem R123773 : Reach 123773 := rs (se 3 (by rfl) ⟨23207, by rfl⟩) (B 46415 (by norm_num) ⟨23207, by rfl⟩ (by norm_num))
theorem R91021 : Reach 91021 := rs (se 3 (by rfl) ⟨17066, by rfl⟩) (B 34133 (by norm_num) ⟨17066, by rfl⟩ (by norm_num))
theorem R123797 : Reach 123797 := rs (se 6 (by rfl) ⟨2901, by rfl⟩) (B 5803 (by norm_num) ⟨2901, by rfl⟩ (by norm_num))
theorem R123821 : Reach 123821 := rs (se 3 (by rfl) ⟨23216, by rfl⟩) (B 46433 (by norm_num) ⟨23216, by rfl⟩ (by norm_num))
theorem R91057 : Reach 91057 := rs (se 2 (by rfl) ⟨34146, by rfl⟩) (B 68293 (by norm_num) ⟨34146, by rfl⟩ (by norm_num))
theorem R123845 : Reach 123845 := rs (se 4 (by rfl) ⟨11610, by rfl⟩) (B 23221 (by norm_num) ⟨11610, by rfl⟩ (by norm_num))
theorem R91093 : Reach 91093 := rs (se 7 (by rfl) ⟨1067, by rfl⟩) (B 2135 (by norm_num) ⟨1067, by rfl⟩ (by norm_num))
theorem R156629 : Reach 156629 := rs (se 7 (by rfl) ⟨1835, by rfl⟩) (B 3671 (by norm_num) ⟨1835, by rfl⟩ (by norm_num))
theorem R123869 : Reach 123869 := rs (se 3 (by rfl) ⟨23225, by rfl⟩) (B 46451 (by norm_num) ⟨23225, by rfl⟩ (by norm_num))
theorem R123893 : Reach 123893 := rs (se 5 (by rfl) ⟨5807, by rfl⟩) (B 11615 (by norm_num) ⟨5807, by rfl⟩ (by norm_num))
theorem R91129 : Reach 91129 := rs (se 2 (by rfl) ⟨34173, by rfl⟩) (B 68347 (by norm_num) ⟨34173, by rfl⟩ (by norm_num))
theorem R123917 : Reach 123917 := rs (se 3 (by rfl) ⟨23234, by rfl⟩) (B 46469 (by norm_num) ⟨23234, by rfl⟩ (by norm_num))
theorem R91165 : Reach 91165 := rs (se 3 (by rfl) ⟨17093, by rfl⟩) (B 34187 (by norm_num) ⟨17093, by rfl⟩ (by norm_num))
theorem R123941 : Reach 123941 := rs (se 4 (by rfl) ⟨11619, by rfl⟩) (B 23239 (by norm_num) ⟨11619, by rfl⟩ (by norm_num))
theorem R123965 : Reach 123965 := rs (se 3 (by rfl) ⟨23243, by rfl⟩) (B 46487 (by norm_num) ⟨23243, by rfl⟩ (by norm_num))
theorem R91201 : Reach 91201 := rs (se 2 (by rfl) ⟨34200, by rfl⟩) (B 68401 (by norm_num) ⟨34200, by rfl⟩ (by norm_num))
theorem R123989 : Reach 123989 := rs (se 8 (by rfl) ⟨726, by rfl⟩) (B 1453 (by norm_num) ⟨726, by rfl⟩ (by norm_num))
theorem R91237 : Reach 91237 := rs (se 4 (by rfl) ⟨8553, by rfl⟩) (B 17107 (by norm_num) ⟨8553, by rfl⟩ (by norm_num))
theorem R124013 : Reach 124013 := rs (se 3 (by rfl) ⟨23252, by rfl⟩) (B 46505 (by norm_num) ⟨23252, by rfl⟩ (by norm_num))
theorem R124037 : Reach 124037 := rs (se 4 (by rfl) ⟨11628, by rfl⟩) (B 23257 (by norm_num) ⟨11628, by rfl⟩ (by norm_num))
theorem R91273 : Reach 91273 := rs (se 2 (by rfl) ⟨34227, by rfl⟩) (B 68455 (by norm_num) ⟨34227, by rfl⟩ (by norm_num))
theorem R124061 : Reach 124061 := rs (se 3 (by rfl) ⟨23261, by rfl⟩) (B 46523 (by norm_num) ⟨23261, by rfl⟩ (by norm_num))
theorem R91309 : Reach 91309 := rs (se 3 (by rfl) ⟨17120, by rfl⟩) (B 34241 (by norm_num) ⟨17120, by rfl⟩ (by norm_num))
theorem R124085 : Reach 124085 := rs (se 5 (by rfl) ⟨5816, by rfl⟩) (B 11633 (by norm_num) ⟨5816, by rfl⟩ (by norm_num))
theorem R124109 : Reach 124109 := rs (se 3 (by rfl) ⟨23270, by rfl⟩) (B 46541 (by norm_num) ⟨23270, by rfl⟩ (by norm_num))
theorem R91345 : Reach 91345 := rs (se 2 (by rfl) ⟨34254, by rfl⟩) (B 68509 (by norm_num) ⟨34254, by rfl⟩ (by norm_num))
theorem R124133 : Reach 124133 := rs (se 4 (by rfl) ⟨11637, by rfl⟩) (B 23275 (by norm_num) ⟨11637, by rfl⟩ (by norm_num))
theorem R91381 : Reach 91381 := rs (se 5 (by rfl) ⟨4283, by rfl⟩) (B 8567 (by norm_num) ⟨4283, by rfl⟩ (by norm_num))
theorem R156917 : Reach 156917 := rs (se 5 (by rfl) ⟨7355, by rfl⟩) (B 14711 (by norm_num) ⟨7355, by rfl⟩ (by norm_num))
theorem R124157 : Reach 124157 := rs (se 3 (by rfl) ⟨23279, by rfl⟩) (B 46559 (by norm_num) ⟨23279, by rfl⟩ (by norm_num))
theorem R419093 : Reach 419093 := rs (se 6 (by rfl) ⟨9822, by rfl⟩) (B 19645 (by norm_num) ⟨9822, by rfl⟩ (by norm_num))
theorem R124181 : Reach 124181 := rs (se 6 (by rfl) ⟨2910, by rfl⟩) (B 5821 (by norm_num) ⟨2910, by rfl⟩ (by norm_num))
theorem R91417 : Reach 91417 := rs (se 2 (by rfl) ⟨34281, by rfl⟩) (B 68563 (by norm_num) ⟨34281, by rfl⟩ (by norm_num))
theorem R124205 : Reach 124205 := rs (se 3 (by rfl) ⟨23288, by rfl⟩) (B 46577 (by norm_num) ⟨23288, by rfl⟩ (by norm_num))
theorem R91453 : Reach 91453 := rs (se 3 (by rfl) ⟨17147, by rfl⟩) (B 34295 (by norm_num) ⟨17147, by rfl⟩ (by norm_num))
theorem R124229 : Reach 124229 := rs (se 4 (by rfl) ⟨11646, by rfl⟩) (B 23293 (by norm_num) ⟨11646, by rfl⟩ (by norm_num))
theorem R124253 : Reach 124253 := rs (se 3 (by rfl) ⟨23297, by rfl⟩) (B 46595 (by norm_num) ⟨23297, by rfl⟩ (by norm_num))
theorem R91489 : Reach 91489 := rs (se 2 (by rfl) ⟨34308, by rfl⟩) (B 68617 (by norm_num) ⟨34308, by rfl⟩ (by norm_num))
theorem R124277 : Reach 124277 := rs (se 5 (by rfl) ⟨5825, by rfl⟩) (B 11651 (by norm_num) ⟨5825, by rfl⟩ (by norm_num))
theorem R91525 : Reach 91525 := rs (se 4 (by rfl) ⟨8580, by rfl⟩) (B 17161 (by norm_num) ⟨8580, by rfl⟩ (by norm_num))
theorem R157069 : Reach 157069 := rs (se 3 (by rfl) ⟨29450, by rfl⟩) (B 58901 (by norm_num) ⟨29450, by rfl⟩ (by norm_num))
theorem R124301 : Reach 124301 := rs (se 3 (by rfl) ⟨23306, by rfl⟩) (B 46613 (by norm_num) ⟨23306, by rfl⟩ (by norm_num))
theorem R124325 : Reach 124325 := rs (se 4 (by rfl) ⟨11655, by rfl⟩) (B 23311 (by norm_num) ⟨11655, by rfl⟩ (by norm_num))
theorem R91561 : Reach 91561 := rs (se 2 (by rfl) ⟨34335, by rfl⟩) (B 68671 (by norm_num) ⟨34335, by rfl⟩ (by norm_num))
theorem R124349 : Reach 124349 := rs (se 3 (by rfl) ⟨23315, by rfl⟩) (B 46631 (by norm_num) ⟨23315, by rfl⟩ (by norm_num))
theorem R91597 : Reach 91597 := rs (se 3 (by rfl) ⟨17174, by rfl⟩) (B 34349 (by norm_num) ⟨17174, by rfl⟩ (by norm_num))
theorem R124373 : Reach 124373 := rs (se 7 (by rfl) ⟨1457, by rfl⟩) (B 2915 (by norm_num) ⟨1457, by rfl⟩ (by norm_num))
theorem R124397 : Reach 124397 := rs (se 3 (by rfl) ⟨23324, by rfl⟩) (B 46649 (by norm_num) ⟨23324, by rfl⟩ (by norm_num))
theorem R91633 : Reach 91633 := rs (se 2 (by rfl) ⟨34362, by rfl⟩) (B 68725 (by norm_num) ⟨34362, by rfl⟩ (by norm_num))
theorem R321029 : Reach 321029 := rs (se 4 (by rfl) ⟨30096, by rfl⟩) (B 60193 (by norm_num) ⟨30096, by rfl⟩ (by norm_num))
theorem R124421 : Reach 124421 := rs (se 4 (by rfl) ⟨11664, by rfl⟩) (B 23329 (by norm_num) ⟨11664, by rfl⟩ (by norm_num))
theorem R91669 : Reach 91669 := rs (se 6 (by rfl) ⟨2148, by rfl⟩) (B 4297 (by norm_num) ⟨2148, by rfl⟩ (by norm_num))
theorem R124445 : Reach 124445 := rs (se 3 (by rfl) ⟨23333, by rfl⟩) (B 46667 (by norm_num) ⟨23333, by rfl⟩ (by norm_num))
theorem R124469 : Reach 124469 := rs (se 5 (by rfl) ⟨5834, by rfl⟩) (B 11669 (by norm_num) ⟨5834, by rfl⟩ (by norm_num))
theorem R91705 : Reach 91705 := rs (se 2 (by rfl) ⟨34389, by rfl⟩) (B 68779 (by norm_num) ⟨34389, by rfl⟩ (by norm_num))
theorem R124493 : Reach 124493 := rs (se 3 (by rfl) ⟨23342, by rfl⟩) (B 46685 (by norm_num) ⟨23342, by rfl⟩ (by norm_num))
theorem R91741 : Reach 91741 := rs (se 3 (by rfl) ⟨17201, by rfl⟩) (B 34403 (by norm_num) ⟨17201, by rfl⟩ (by norm_num))
theorem R124517 : Reach 124517 := rs (se 4 (by rfl) ⟨11673, by rfl⟩) (B 23347 (by norm_num) ⟨11673, by rfl⟩ (by norm_num))
theorem R124541 : Reach 124541 := rs (se 3 (by rfl) ⟨23351, by rfl⟩) (B 46703 (by norm_num) ⟨23351, by rfl⟩ (by norm_num))
theorem R91777 : Reach 91777 := rs (se 2 (by rfl) ⟨34416, by rfl⟩) (B 68833 (by norm_num) ⟨34416, by rfl⟩ (by norm_num))
theorem R124565 : Reach 124565 := rs (se 6 (by rfl) ⟨2919, by rfl⟩) (B 5839 (by norm_num) ⟨2919, by rfl⟩ (by norm_num))
theorem R91813 : Reach 91813 := rs (se 4 (by rfl) ⟨8607, by rfl⟩) (B 17215 (by norm_num) ⟨8607, by rfl⟩ (by norm_num))
theorem R124589 : Reach 124589 := rs (se 3 (by rfl) ⟨23360, by rfl⟩) (B 46721 (by norm_num) ⟨23360, by rfl⟩ (by norm_num))
theorem R157373 : Reach 157373 := rs (se 3 (by rfl) ⟨29507, by rfl⟩) (B 59015 (by norm_num) ⟨29507, by rfl⟩ (by norm_num))
theorem R124613 : Reach 124613 := rs (se 4 (by rfl) ⟨11682, by rfl⟩) (B 23365 (by norm_num) ⟨11682, by rfl⟩ (by norm_num))
theorem R91849 : Reach 91849 := rs (se 2 (by rfl) ⟨34443, by rfl⟩) (B 68887 (by norm_num) ⟨34443, by rfl⟩ (by norm_num))
theorem R124637 : Reach 124637 := rs (se 3 (by rfl) ⟨23369, by rfl⟩) (B 46739 (by norm_num) ⟨23369, by rfl⟩ (by norm_num))
theorem R190181 : Reach 190181 := rs (se 4 (by rfl) ⟨17829, by rfl⟩) (B 35659 (by norm_num) ⟨17829, by rfl⟩ (by norm_num))
theorem R222949 : Reach 222949 := rs (se 4 (by rfl) ⟨20901, by rfl⟩) (B 41803 (by norm_num) ⟨20901, by rfl⟩ (by norm_num))
theorem R91885 : Reach 91885 := rs (se 3 (by rfl) ⟨17228, by rfl⟩) (B 34457 (by norm_num) ⟨17228, by rfl⟩ (by norm_num))
theorem R124661 : Reach 124661 := rs (se 5 (by rfl) ⟨5843, by rfl⟩) (B 11687 (by norm_num) ⟨5843, by rfl⟩ (by norm_num))
theorem R124685 : Reach 124685 := rs (se 3 (by rfl) ⟨23378, by rfl⟩) (B 46757 (by norm_num) ⟨23378, by rfl⟩ (by norm_num))
theorem R91921 : Reach 91921 := rs (se 2 (by rfl) ⟨34470, by rfl⟩) (B 68941 (by norm_num) ⟨34470, by rfl⟩ (by norm_num))
theorem R517909 : Reach 517909 := rs (se 6 (by rfl) ⟨12138, by rfl⟩) (B 24277 (by norm_num) ⟨12138, by rfl⟩ (by norm_num))
theorem R91957 : Reach 91957 := rs (se 5 (by rfl) ⟨4310, by rfl⟩) (B 8621 (by norm_num) ⟨4310, by rfl⟩ (by norm_num))
theorem R91993 : Reach 91993 := rs (se 2 (by rfl) ⟨34497, by rfl⟩) (B 68995 (by norm_num) ⟨34497, by rfl⟩ (by norm_num))
theorem R92029 : Reach 92029 := rs (se 3 (by rfl) ⟨17255, by rfl⟩) (B 34511 (by norm_num) ⟨17255, by rfl⟩ (by norm_num))
theorem R124813 : Reach 124813 := rs (se 3 (by rfl) ⟨23402, by rfl⟩) (B 46805 (by norm_num) ⟨23402, by rfl⟩ (by norm_num))
theorem R92065 : Reach 92065 := rs (se 2 (by rfl) ⟨34524, by rfl⟩) (B 69049 (by norm_num) ⟨34524, by rfl⟩ (by norm_num))
theorem R92101 : Reach 92101 := rs (se 4 (by rfl) ⟨8634, by rfl⟩) (B 17269 (by norm_num) ⟨8634, by rfl⟩ (by norm_num))
theorem R92137 : Reach 92137 := rs (se 2 (by rfl) ⟨34551, by rfl⟩) (B 69103 (by norm_num) ⟨34551, by rfl⟩ (by norm_num))
theorem R92173 : Reach 92173 := rs (se 3 (by rfl) ⟨17282, by rfl⟩) (B 34565 (by norm_num) ⟨17282, by rfl⟩ (by norm_num))
theorem R92209 : Reach 92209 := rs (se 2 (by rfl) ⟨34578, by rfl⟩) (B 69157 (by norm_num) ⟨34578, by rfl⟩ (by norm_num))
theorem R256085 : Reach 256085 := rs (se 8 (by rfl) ⟨1500, by rfl⟩) (B 3001 (by norm_num) ⟨1500, by rfl⟩ (by norm_num))
theorem R92245 : Reach 92245 := rs (se 8 (by rfl) ⟨540, by rfl⟩) (B 1081 (by norm_num) ⟨540, by rfl⟩ (by norm_num))
theorem R92281 : Reach 92281 := rs (se 2 (by rfl) ⟨34605, by rfl⟩) (B 69211 (by norm_num) ⟨34605, by rfl⟩ (by norm_num))
theorem R92317 : Reach 92317 := rs (se 3 (by rfl) ⟨17309, by rfl⟩) (B 34619 (by norm_num) ⟨17309, by rfl⟩ (by norm_num))
theorem R583861 : Reach 583861 := rs (se 5 (by rfl) ⟨27368, by rfl⟩) (B 54737 (by norm_num) ⟨27368, by rfl⟩ (by norm_num))
theorem R92353 : Reach 92353 := rs (se 2 (by rfl) ⟨34632, by rfl⟩) (B 69265 (by norm_num) ⟨34632, by rfl⟩ (by norm_num))
theorem R256213 : Reach 256213 := rs (se 7 (by rfl) ⟨3002, by rfl⟩) (B 6005 (by norm_num) ⟨3002, by rfl⟩ (by norm_num))
theorem R92389 : Reach 92389 := rs (se 4 (by rfl) ⟨8661, by rfl⟩) (B 17323 (by norm_num) ⟨8661, by rfl⟩ (by norm_num))
theorem R92425 : Reach 92425 := rs (se 2 (by rfl) ⟨34659, by rfl⟩) (B 69319 (by norm_num) ⟨34659, by rfl⟩ (by norm_num))
theorem R190757 : Reach 190757 := rs (se 4 (by rfl) ⟨17883, by rfl⟩) (B 35767 (by norm_num) ⟨17883, by rfl⟩ (by norm_num))
theorem R92461 : Reach 92461 := rs (se 3 (by rfl) ⟨17336, by rfl⟩) (B 34673 (by norm_num) ⟨17336, by rfl⟩ (by norm_num))
theorem R92497 : Reach 92497 := rs (se 2 (by rfl) ⟨34686, by rfl⟩) (B 69373 (by norm_num) ⟨34686, by rfl⟩ (by norm_num))
theorem R92533 : Reach 92533 := rs (se 5 (by rfl) ⟨4337, by rfl⟩) (B 8675 (by norm_num) ⟨4337, by rfl⟩ (by norm_num))
theorem R92569 : Reach 92569 := rs (se 2 (by rfl) ⟨34713, by rfl⟩) (B 69427 (by norm_num) ⟨34713, by rfl⟩ (by norm_num))
theorem R387509 : Reach 387509 := rs (se 5 (by rfl) ⟨18164, by rfl⟩) (B 36329 (by norm_num) ⟨18164, by rfl⟩ (by norm_num))
theorem R92605 : Reach 92605 := rs (se 3 (by rfl) ⟨17363, by rfl⟩) (B 34727 (by norm_num) ⟨17363, by rfl⟩ (by norm_num))
theorem R223685 : Reach 223685 := rs (se 4 (by rfl) ⟨20970, by rfl⟩) (B 41941 (by norm_num) ⟨20970, by rfl⟩ (by norm_num))
theorem R354773 : Reach 354773 := rs (se 7 (by rfl) ⟨4157, by rfl⟩) (B 8315 (by norm_num) ⟨4157, by rfl⟩ (by norm_num))
theorem R92641 : Reach 92641 := rs (se 2 (by rfl) ⟨34740, by rfl⟩) (B 69481 (by norm_num) ⟨34740, by rfl⟩ (by norm_num))
theorem R92677 : Reach 92677 := rs (se 4 (by rfl) ⟨8688, by rfl⟩) (B 17377 (by norm_num) ⟨8688, by rfl⟩ (by norm_num))
theorem R125477 : Reach 125477 := rs (se 4 (by rfl) ⟨11763, by rfl⟩) (B 23527 (by norm_num) ⟨11763, by rfl⟩ (by norm_num))
theorem R420389 : Reach 420389 := rs (se 4 (by rfl) ⟨39411, by rfl⟩) (B 78823 (by norm_num) ⟨39411, by rfl⟩ (by norm_num))
theorem R92713 : Reach 92713 := rs (se 2 (by rfl) ⟨34767, by rfl⟩) (B 69535 (by norm_num) ⟨34767, by rfl⟩ (by norm_num))
theorem R92749 : Reach 92749 := rs (se 3 (by rfl) ⟨17390, by rfl⟩) (B 34781 (by norm_num) ⟨17390, by rfl⟩ (by norm_num))
theorem R92785 : Reach 92785 := rs (se 2 (by rfl) ⟨34794, by rfl⟩) (B 69589 (by norm_num) ⟨34794, by rfl⟩ (by norm_num))
theorem R92821 : Reach 92821 := rs (se 6 (by rfl) ⟨2175, by rfl⟩) (B 4351 (by norm_num) ⟨2175, by rfl⟩ (by norm_num))
theorem R191141 : Reach 191141 := rs (se 4 (by rfl) ⟨17919, by rfl⟩) (B 35839 (by norm_num) ⟨17919, by rfl⟩ (by norm_num))
theorem R92857 : Reach 92857 := rs (se 2 (by rfl) ⟨34821, by rfl⟩) (B 69643 (by norm_num) ⟨34821, by rfl⟩ (by norm_num))
theorem R355013 : Reach 355013 := rs (se 4 (by rfl) ⟨33282, by rfl⟩) (B 66565 (by norm_num) ⟨33282, by rfl⟩ (by norm_num))
theorem R92893 : Reach 92893 := rs (se 3 (by rfl) ⟨17417, by rfl⟩) (B 34835 (by norm_num) ⟨17417, by rfl⟩ (by norm_num))
theorem R92929 : Reach 92929 := rs (se 2 (by rfl) ⟨34848, by rfl⟩) (B 69697 (by norm_num) ⟨34848, by rfl⟩ (by norm_num))
theorem R125725 : Reach 125725 := rs (se 3 (by rfl) ⟨23573, by rfl⟩) (B 47147 (by norm_num) ⟨23573, by rfl⟩ (by norm_num))
theorem R92965 : Reach 92965 := rs (se 4 (by rfl) ⟨8715, by rfl⟩) (B 17431 (by norm_num) ⟨8715, by rfl⟩ (by norm_num))
theorem R93001 : Reach 93001 := rs (se 2 (by rfl) ⟨34875, by rfl⟩) (B 69751 (by norm_num) ⟨34875, by rfl⟩ (by norm_num))
theorem R93037 : Reach 93037 := rs (se 3 (by rfl) ⟨17444, by rfl⟩) (B 34889 (by norm_num) ⟨17444, by rfl⟩ (by norm_num))
theorem R224117 : Reach 224117 := rs (se 5 (by rfl) ⟨10505, by rfl⟩) (B 21011 (by norm_num) ⟨10505, by rfl⟩ (by norm_num))
theorem R93053 : Reach 93053 := rs (se 3 (by rfl) ⟨17447, by rfl⟩) (B 34895 (by norm_num) ⟨17447, by rfl⟩ (by norm_num))
theorem R93073 : Reach 93073 := rs (se 2 (by rfl) ⟨34902, by rfl⟩) (B 69805 (by norm_num) ⟨34902, by rfl⟩ (by norm_num))
theorem R93109 : Reach 93109 := rs (se 5 (by rfl) ⟨4364, by rfl⟩) (B 8729 (by norm_num) ⟨4364, by rfl⟩ (by norm_num))
theorem R93145 : Reach 93145 := rs (se 2 (by rfl) ⟨34929, by rfl⟩) (B 69859 (by norm_num) ⟨34929, by rfl⟩ (by norm_num))
theorem R93181 : Reach 93181 := rs (se 3 (by rfl) ⟨17471, by rfl⟩) (B 34943 (by norm_num) ⟨17471, by rfl⟩ (by norm_num))
theorem R93217 : Reach 93217 := rs (se 2 (by rfl) ⟨34956, by rfl⟩) (B 69913 (by norm_num) ⟨34956, by rfl⟩ (by norm_num))
theorem R93253 : Reach 93253 := rs (se 4 (by rfl) ⟨8742, by rfl⟩) (B 17485 (by norm_num) ⟨8742, by rfl⟩ (by norm_num))
theorem R93289 : Reach 93289 := rs (se 2 (by rfl) ⟨34983, by rfl⟩) (B 69967 (by norm_num) ⟨34983, by rfl⟩ (by norm_num))
theorem R93325 : Reach 93325 := rs (se 3 (by rfl) ⟨17498, by rfl⟩) (B 34997 (by norm_num) ⟨17498, by rfl⟩ (by norm_num))
theorem R1404053 : Reach 1404053 := rs (se 6 (by rfl) ⟨32907, by rfl⟩) (B 65815 (by norm_num) ⟨32907, by rfl⟩ (by norm_num))
theorem R93361 : Reach 93361 := rs (se 2 (by rfl) ⟨35010, by rfl⟩) (B 70021 (by norm_num) ⟨35010, by rfl⟩ (by norm_num))
theorem R224453 : Reach 224453 := rs (se 4 (by rfl) ⟨21042, by rfl⟩) (B 42085 (by norm_num) ⟨21042, by rfl⟩ (by norm_num))
theorem R93397 : Reach 93397 := rs (se 7 (by rfl) ⟨1094, by rfl⟩) (B 2189 (by norm_num) ⟨1094, by rfl⟩ (by norm_num))
theorem R93433 : Reach 93433 := rs (se 2 (by rfl) ⟨35037, by rfl⟩) (B 70075 (by norm_num) ⟨35037, by rfl⟩ (by norm_num))
theorem R93469 : Reach 93469 := rs (se 3 (by rfl) ⟨17525, by rfl⟩) (B 35051 (by norm_num) ⟨17525, by rfl⟩ (by norm_num))
theorem R224549 : Reach 224549 := rs (se 4 (by rfl) ⟨21051, by rfl⟩) (B 42103 (by norm_num) ⟨21051, by rfl⟩ (by norm_num))
theorem R93505 : Reach 93505 := rs (se 2 (by rfl) ⟨35064, by rfl⟩) (B 70129 (by norm_num) ⟨35064, by rfl⟩ (by norm_num))
theorem R93889 : Reach 93889 := rs (se 2 (by rfl) ⟨35208, by rfl⟩) (B 70417 (by norm_num) ⟨35208, by rfl⟩ (by norm_num))
theorem R454805 : Reach 454805 := rs (se 6 (by rfl) ⟨10659, by rfl⟩) (B 21319 (by norm_num) ⟨10659, by rfl⟩ (by norm_num))
theorem R618677 : Reach 618677 := rs (se 5 (by rfl) ⟨29000, by rfl⟩) (B 58001 (by norm_num) ⟨29000, by rfl⟩ (by norm_num))
theorem R127165 : Reach 127165 := rs (se 3 (by rfl) ⟨23843, by rfl⟩) (B 47687 (by norm_num) ⟨23843, by rfl⟩ (by norm_num))
theorem R192725 : Reach 192725 := rs (se 7 (by rfl) ⟨2258, by rfl⟩) (B 4517 (by norm_num) ⟨2258, by rfl⟩ (by norm_num))
theorem R94513 : Reach 94513 := rs (se 2 (by rfl) ⟨35442, by rfl⟩) (B 70885 (by norm_num) ⟨35442, by rfl⟩ (by norm_num))
theorem R192901 : Reach 192901 := rs (se 4 (by rfl) ⟨18084, by rfl⟩) (B 36169 (by norm_num) ⟨18084, by rfl⟩ (by norm_num))
theorem R94765 : Reach 94765 := rs (se 3 (by rfl) ⟨17768, by rfl⟩) (B 35537 (by norm_num) ⟨17768, by rfl⟩ (by norm_num))
theorem R1504021 : Reach 1504021 := rs (se 6 (by rfl) ⟨35250, by rfl⟩) (B 70501 (by norm_num) ⟨35250, by rfl⟩ (by norm_num))
theorem R127837 : Reach 127837 := rs (se 3 (by rfl) ⟨23969, by rfl⟩) (B 47939 (by norm_num) ⟨23969, by rfl⟩ (by norm_num))
theorem R226309 : Reach 226309 := rs (se 4 (by rfl) ⟨21216, by rfl⟩) (B 42433 (by norm_num) ⟨21216, by rfl⟩ (by norm_num))
theorem R259109 : Reach 259109 := rs (se 4 (by rfl) ⟨24291, by rfl⟩) (B 48583 (by norm_num) ⟨24291, by rfl⟩ (by norm_num))
theorem R226469 : Reach 226469 := rs (se 4 (by rfl) ⟨21231, by rfl⟩) (B 42463 (by norm_num) ⟨21231, by rfl⟩ (by norm_num))
theorem R324821 : Reach 324821 := rs (se 7 (by rfl) ⟨3806, by rfl⟩) (B 7613 (by norm_num) ⟨3806, by rfl⟩ (by norm_num))
theorem R95465 : Reach 95465 := rs (se 2 (by rfl) ⟨35799, by rfl⟩) (B 71599 (by norm_num) ⟨35799, by rfl⟩ (by norm_num))
theorem R488693 : Reach 488693 := rs (se 5 (by rfl) ⟨22907, by rfl⟩) (B 45815 (by norm_num) ⟨22907, by rfl⟩ (by norm_num))
theorem R455989 : Reach 455989 := rs (se 5 (by rfl) ⟨21374, by rfl⟩) (B 42749 (by norm_num) ⟨21374, by rfl⟩ (by norm_num))
theorem R193909 : Reach 193909 := rs (se 5 (by rfl) ⟨9089, by rfl⟩) (B 18179 (by norm_num) ⟨9089, by rfl⟩ (by norm_num))
theorem R226709 : Reach 226709 := rs (se 6 (by rfl) ⟨5313, by rfl⟩) (B 10627 (by norm_num) ⟨5313, by rfl⟩ (by norm_num))
theorem R194005 : Reach 194005 := rs (se 7 (by rfl) ⟨2273, by rfl⟩) (B 4547 (by norm_num) ⟨2273, by rfl⟩ (by norm_num))
theorem R95801 : Reach 95801 := rs (se 2 (by rfl) ⟨35925, by rfl⟩) (B 71851 (by norm_num) ⟨35925, by rfl⟩ (by norm_num))
theorem R161357 : Reach 161357 := rs (se 3 (by rfl) ⟨30254, by rfl⟩) (B 60509 (by norm_num) ⟨30254, by rfl⟩ (by norm_num))
theorem R226901 : Reach 226901 := rs (se 8 (by rfl) ⟨1329, by rfl⟩) (B 2659 (by norm_num) ⟨1329, by rfl⟩ (by norm_num))
theorem R161405 : Reach 161405 := rs (se 3 (by rfl) ⟨30263, by rfl⟩) (B 60527 (by norm_num) ⟨30263, by rfl⟩ (by norm_num))
theorem R95917 : Reach 95917 := rs (se 3 (by rfl) ⟨17984, by rfl⟩) (B 35969 (by norm_num) ⟨17984, by rfl⟩ (by norm_num))
theorem R521909 : Reach 521909 := rs (se 5 (by rfl) ⟨24464, by rfl⟩) (B 48929 (by norm_num) ⟨24464, by rfl⟩ (by norm_num))
theorem R980693 : Reach 980693 := rs (se 7 (by rfl) ⟨11492, by rfl⟩) (B 22985 (by norm_num) ⟨11492, by rfl⟩ (by norm_num))
theorem R95989 : Reach 95989 := rs (se 5 (by rfl) ⟨4499, by rfl⟩) (B 8999 (by norm_num) ⟨4499, by rfl⟩ (by norm_num))
theorem R96013 : Reach 96013 := rs (se 3 (by rfl) ⟨18002, by rfl⟩) (B 36005 (by norm_num) ⟨18002, by rfl⟩ (by norm_num))
theorem R128837 : Reach 128837 := rs (se 4 (by rfl) ⟨12078, by rfl⟩) (B 24157 (by norm_num) ⟨12078, by rfl⟩ (by norm_num))
theorem R292709 : Reach 292709 := rs (se 4 (by rfl) ⟨27441, by rfl⟩) (B 54883 (by norm_num) ⟨27441, by rfl⟩ (by norm_num))
theorem R96157 : Reach 96157 := rs (se 3 (by rfl) ⟨18029, by rfl⟩) (B 36059 (by norm_num) ⟨18029, by rfl⟩ (by norm_num))
theorem R194525 : Reach 194525 := rs (se 3 (by rfl) ⟨36473, by rfl⟩) (B 72947 (by norm_num) ⟨36473, by rfl⟩ (by norm_num))
theorem R292853 : Reach 292853 := rs (se 5 (by rfl) ⟨13727, by rfl⟩) (B 27455 (by norm_num) ⟨13727, by rfl⟩ (by norm_num))
theorem R195053 : Reach 195053 := rs (se 3 (by rfl) ⟨36572, by rfl⟩) (B 73145 (by norm_num) ⟨36572, by rfl⟩ (by norm_num))
theorem R227893 : Reach 227893 := rs (se 5 (by rfl) ⟨10682, by rfl⟩) (B 21365 (by norm_num) ⟨10682, by rfl⟩ (by norm_num))
theorem R195293 : Reach 195293 := rs (se 3 (by rfl) ⟨36617, by rfl⟩) (B 73235 (by norm_num) ⟨36617, by rfl⟩ (by norm_num))
theorem R97373 : Reach 97373 := rs (se 3 (by rfl) ⟨18257, by rfl⟩) (B 36515 (by norm_num) ⟨18257, by rfl⟩ (by norm_num))
theorem R261301 : Reach 261301 := rs (se 5 (by rfl) ⟨12248, by rfl⟩) (B 24497 (by norm_num) ⟨12248, by rfl⟩ (by norm_num))
theorem R457973 : Reach 457973 := rs (se 5 (by rfl) ⟨21467, by rfl⟩) (B 42935 (by norm_num) ⟨21467, by rfl⟩ (by norm_num))
theorem R130349 : Reach 130349 := rs (se 3 (by rfl) ⟨24440, by rfl⟩) (B 48881 (by norm_num) ⟨24440, by rfl⟩ (by norm_num))
theorem R97681 : Reach 97681 := rs (se 2 (by rfl) ⟨36630, by rfl⟩) (B 73261 (by norm_num) ⟨36630, by rfl⟩ (by norm_num))
theorem R97781 : Reach 97781 := rs (se 5 (by rfl) ⟨4583, by rfl⟩) (B 9167 (by norm_num) ⟨4583, by rfl⟩ (by norm_num))
theorem R228997 : Reach 228997 := rs (se 4 (by rfl) ⟨21468, by rfl⟩) (B 42937 (by norm_num) ⟨21468, by rfl⟩ (by norm_num))
theorem R491221 : Reach 491221 := rs (se 7 (by rfl) ⟨5756, by rfl⟩) (B 11513 (by norm_num) ⟨5756, by rfl⟩ (by norm_num))
theorem R130805 : Reach 130805 := rs (se 5 (by rfl) ⟨6131, by rfl⟩) (B 12263 (by norm_num) ⟨6131, by rfl⟩ (by norm_num))
theorem R98185 : Reach 98185 := rs (se 2 (by rfl) ⟨36819, by rfl⟩) (B 73639 (by norm_num) ⟨36819, by rfl⟩ (by norm_num))
theorem R360389 : Reach 360389 := rs (se 4 (by rfl) ⟨33786, by rfl⟩) (B 67573 (by norm_num) ⟨33786, by rfl⟩ (by norm_num))
theorem R688085 : Reach 688085 := rs (se 7 (by rfl) ⟨8063, by rfl⟩) (B 16127 (by norm_num) ⟨8063, by rfl⟩ (by norm_num))
theorem R262133 : Reach 262133 := rs (se 5 (by rfl) ⟨12287, by rfl⟩) (B 24575 (by norm_num) ⟨12287, by rfl⟩ (by norm_num))
theorem R131425 : Reach 131425 := rs (se 2 (by rfl) ⟨49284, by rfl⟩) R98569
theorem R262531 : Reach 262531 := rs (se 1 (by rfl) ⟨196898, by rfl⟩) R393797
theorem R3015053 : Reach 3015053 := rs (se 3 (by rfl) ⟨565322, by rfl⟩) R1130645
theorem R262595 : Reach 262595 := rs (se 1 (by rfl) ⟨196946, by rfl⟩) R393893
theorem R229841 : Reach 229841 := rs (se 2 (by rfl) ⟨86190, by rfl⟩) R172381
theorem R262673 : Reach 262673 := rs (se 2 (by rfl) ⟨98502, by rfl⟩) R197005
theorem R98915 : Reach 98915 := rs (se 1 (by rfl) ⟨74186, by rfl⟩) R148373
theorem R1868771 : Reach 1868771 := rs (se 1 (by rfl) ⟨1401578, by rfl⟩) R2803157
theorem R132193 : Reach 132193 := rs (se 2 (by rfl) ⟨49572, by rfl⟩) R99145
theorem R230627 : Reach 230627 := rs (se 1 (by rfl) ⟨172970, by rfl⟩) R345941
theorem R886085 : Reach 886085 := rs (se 4 (by rfl) ⟨83070, by rfl⟩) R166141
theorem R230957 : Reach 230957 := rs (se 3 (by rfl) ⟨43304, by rfl⟩) R86609
theorem R132707 : Reach 132707 := rs (se 1 (by rfl) ⟨99530, by rfl⟩) R199061
theorem R231025 : Reach 231025 := rs (se 2 (by rfl) ⟨86634, by rfl⟩) R173269
theorem R132835 : Reach 132835 := rs (se 1 (by rfl) ⟨99626, by rfl⟩) R199253
theorem R132977 : Reach 132977 := rs (se 2 (by rfl) ⟨49866, by rfl⟩) R99733
theorem R231299 : Reach 231299 := rs (se 1 (by rfl) ⟨173474, by rfl⟩) R346949
theorem R100435 : Reach 100435 := rs (se 1 (by rfl) ⟨75326, by rfl⟩) R150653
theorem R526499 : Reach 526499 := rs (se 1 (by rfl) ⟨394874, by rfl⟩) R789749
theorem R100531 : Reach 100531 := rs (se 1 (by rfl) ⟨75398, by rfl⟩) R150797
theorem R362723 : Reach 362723 := rs (se 1 (by rfl) ⟨272042, by rfl⟩) R544085
theorem R297265 : Reach 297265 := rs (se 2 (by rfl) ⟨111474, by rfl⟩) R222949
theorem R624995 : Reach 624995 := rs (se 1 (by rfl) ⟨468746, by rfl⟩) R937493
theorem R690545 : Reach 690545 := rs (se 2 (by rfl) ⟨258954, by rfl⟩) R517909
theorem R264593 : Reach 264593 := rs (se 2 (by rfl) ⟨99222, by rfl⟩) R198445
theorem R133555 : Reach 133555 := rs (se 1 (by rfl) ⟨100166, by rfl⟩) R200333
theorem R166417 : Reach 166417 := rs (se 2 (by rfl) ⟨62406, by rfl⟩) R124813
theorem R133697 : Reach 133697 := rs (se 2 (by rfl) ⟨50136, by rfl⟩) R100273
theorem R232013 : Reach 232013 := rs (se 3 (by rfl) ⟨43502, by rfl⟩) R87005
theorem R166531 : Reach 166531 := rs (se 1 (by rfl) ⟨124898, by rfl⟩) R249797
theorem R101027 : Reach 101027 := rs (se 1 (by rfl) ⟨75770, by rfl⟩) R151541
theorem R133825 : Reach 133825 := rs (se 2 (by rfl) ⟨50184, by rfl⟩) R100369
theorem R232141 : Reach 232141 := rs (se 3 (by rfl) ⟨43526, by rfl⟩) R87053
theorem R133859 : Reach 133859 := rs (se 1 (by rfl) ⟨100394, by rfl⟩) R200789
theorem R1018595 : Reach 1018595 := rs (se 1 (by rfl) ⟨763946, by rfl⟩) R1527893
theorem R265037 : Reach 265037 := rs (se 3 (by rfl) ⟨49694, by rfl⟩) R99389
theorem R133987 : Reach 133987 := rs (se 1 (by rfl) ⟨100490, by rfl⟩) R200981
theorem R232301 : Reach 232301 := rs (se 3 (by rfl) ⟨43556, by rfl⟩) R87113
theorem R265133 : Reach 265133 := rs (se 3 (by rfl) ⟨49712, by rfl⟩) R99425
theorem R134129 : Reach 134129 := rs (se 2 (by rfl) ⟨50298, by rfl⟩) R100597
theorem R232483 : Reach 232483 := rs (se 1 (by rfl) ⟨174362, by rfl⟩) R348725
theorem R134257 : Reach 134257 := rs (se 2 (by rfl) ⟨50346, by rfl⟩) R100693
theorem R134291 : Reach 134291 := rs (se 1 (by rfl) ⟨100718, by rfl⟩) R201437
theorem R134419 : Reach 134419 := rs (se 1 (by rfl) ⟨100814, by rfl⟩) R201629
theorem R101731 : Reach 101731 := rs (se 1 (by rfl) ⟨76298, by rfl⟩) R152597
theorem R134561 : Reach 134561 := rs (se 2 (by rfl) ⟨50460, by rfl⟩) R100921
theorem R101827 : Reach 101827 := rs (se 1 (by rfl) ⟨76370, by rfl⟩) R152741
theorem R134689 : Reach 134689 := rs (se 2 (by rfl) ⟨50508, by rfl⟩) R101017
theorem R134723 : Reach 134723 := rs (se 1 (by rfl) ⟨101042, by rfl⟩) R202085
theorem R1773197 : Reach 1773197 := rs (se 3 (by rfl) ⟨332474, by rfl⟩) R664949
theorem R134851 : Reach 134851 := rs (se 1 (by rfl) ⟨101138, by rfl⟩) R202277
theorem R167633 : Reach 167633 := rs (se 2 (by rfl) ⟨62862, by rfl⟩) R125725
theorem R200465 : Reach 200465 := rs (se 2 (by rfl) ⟨75174, by rfl⟩) R150349
theorem R200515 : Reach 200515 := rs (se 1 (by rfl) ⟨150386, by rfl⟩) R300773
theorem R134993 : Reach 134993 := rs (se 2 (by rfl) ⟨50622, by rfl⟩) R101245
theorem R102227 : Reach 102227 := rs (se 1 (by rfl) ⟨76670, by rfl⟩) R153341
theorem R102323 : Reach 102323 := rs (se 1 (by rfl) ⟨76742, by rfl⟩) R153485
theorem R200657 : Reach 200657 := rs (se 2 (by rfl) ⟨75246, by rfl⟩) R150493
theorem R135121 : Reach 135121 := rs (se 2 (by rfl) ⟨50670, by rfl⟩) R101341
theorem R135155 : Reach 135155 := rs (se 1 (by rfl) ⟨101366, by rfl⟩) R202733
theorem R135283 : Reach 135283 := rs (se 1 (by rfl) ⟨101462, by rfl⟩) R202925
theorem R430285 : Reach 430285 := rs (se 3 (by rfl) ⟨80678, by rfl⟩) R161357
theorem R135425 : Reach 135425 := rs (se 2 (by rfl) ⟨50784, by rfl⟩) R101569
theorem R135553 : Reach 135553 := rs (se 2 (by rfl) ⟨50832, by rfl⟩) R101665
theorem R233873 : Reach 233873 := rs (se 2 (by rfl) ⟨87702, by rfl⟩) R175405
theorem R135587 : Reach 135587 := rs (se 1 (by rfl) ⟨101690, by rfl⟩) R203381
theorem R135715 : Reach 135715 := rs (se 1 (by rfl) ⟨101786, by rfl⟩) R203573
theorem R1053283 : Reach 1053283 := rs (se 1 (by rfl) ⟨789962, by rfl⟩) R1579925
theorem R103027 : Reach 103027 := rs (se 1 (by rfl) ⟨77270, by rfl⟩) R154541
theorem R135857 : Reach 135857 := rs (se 2 (by rfl) ⟨50946, by rfl⟩) R101893
theorem R103123 : Reach 103123 := rs (se 1 (by rfl) ⟨77342, by rfl⟩) R154685
theorem R201457 : Reach 201457 := rs (se 2 (by rfl) ⟨75546, by rfl⟩) R151093
theorem R135985 : Reach 135985 := rs (se 2 (by rfl) ⟨50994, by rfl⟩) R101989
theorem R136019 : Reach 136019 := rs (se 1 (by rfl) ⟨102014, by rfl⟩) R204029
theorem R201649 : Reach 201649 := rs (se 2 (by rfl) ⟨75618, by rfl⟩) R151237
theorem R136147 : Reach 136147 := rs (se 1 (by rfl) ⟨102110, by rfl⟩) R204221
theorem R267245 : Reach 267245 := rs (se 3 (by rfl) ⟨50108, by rfl⟩) R100217
theorem R267299 : Reach 267299 := rs (se 1 (by rfl) ⟨200474, by rfl⟩) R400949
theorem R136289 : Reach 136289 := rs (se 2 (by rfl) ⟨51108, by rfl⟩) R102217
theorem R201923 : Reach 201923 := rs (se 1 (by rfl) ⟨151442, by rfl⟩) R302885
theorem R103619 : Reach 103619 := rs (se 1 (by rfl) ⟨77714, by rfl⟩) R155429
theorem R136417 : Reach 136417 := rs (se 2 (by rfl) ⟨51156, by rfl⟩) R102313
theorem R529649 : Reach 529649 := rs (se 2 (by rfl) ⟨198618, by rfl⟩) R397237
theorem R169219 : Reach 169219 := rs (se 1 (by rfl) ⟨126914, by rfl⟩) R253829
theorem R136451 : Reach 136451 := rs (se 1 (by rfl) ⟨102338, by rfl⟩) R204677
theorem R529699 : Reach 529699 := rs (se 1 (by rfl) ⟨397274, by rfl⟩) R794549
theorem R267569 : Reach 267569 := rs (se 2 (by rfl) ⟨100338, by rfl⟩) R200677
theorem R234829 : Reach 234829 := rs (se 3 (by rfl) ⟨44030, by rfl⟩) R88061
theorem R202115 : Reach 202115 := rs (se 1 (by rfl) ⟨151586, by rfl⟩) R303173
theorem R136579 : Reach 136579 := rs (se 1 (by rfl) ⟨102434, by rfl⟩) R204869
theorem R136721 : Reach 136721 := rs (se 2 (by rfl) ⟨51270, by rfl⟩) R102541
theorem R235057 : Reach 235057 := rs (se 2 (by rfl) ⟨88146, by rfl⟩) R176293
theorem R169553 : Reach 169553 := rs (se 2 (by rfl) ⟨63582, by rfl⟩) R127165
theorem R136849 : Reach 136849 := rs (se 2 (by rfl) ⟨51318, by rfl⟩) R102637
theorem R136883 : Reach 136883 := rs (se 1 (by rfl) ⟨102662, by rfl⟩) R205325
theorem R235217 : Reach 235217 := rs (se 2 (by rfl) ⟨88206, by rfl⟩) R176413
theorem R137011 : Reach 137011 := rs (se 1 (by rfl) ⟨102758, by rfl⟩) R205517
theorem R235331 : Reach 235331 := rs (se 1 (by rfl) ⟨176498, by rfl⟩) R352997
theorem R268109 : Reach 268109 := rs (se 3 (by rfl) ⟨50270, by rfl⟩) R100541
theorem R268163 : Reach 268163 := rs (se 1 (by rfl) ⟨201122, by rfl⟩) R402245
theorem R104323 : Reach 104323 := rs (se 1 (by rfl) ⟨78242, by rfl⟩) R156485
theorem R300941 : Reach 300941 := rs (se 3 (by rfl) ⟨56426, by rfl⟩) R112853
theorem R137153 : Reach 137153 := rs (se 2 (by rfl) ⟨51432, by rfl⟩) R102865
theorem R104419 : Reach 104419 := rs (se 1 (by rfl) ⟨78314, by rfl⟩) R156629
theorem R137281 : Reach 137281 := rs (se 2 (by rfl) ⟨51480, by rfl⟩) R102961
theorem R137315 : Reach 137315 := rs (se 1 (by rfl) ⟨102986, by rfl⟩) R205973
theorem R268433 : Reach 268433 := rs (se 2 (by rfl) ⟨100662, by rfl⟩) R201325
theorem R399587 : Reach 399587 := rs (se 1 (by rfl) ⟨299690, by rfl⟩) R599381
theorem R137443 : Reach 137443 := rs (se 1 (by rfl) ⟨103082, by rfl⟩) R206165
theorem R203057 : Reach 203057 := rs (se 2 (by rfl) ⟨76146, by rfl⟩) R152293
theorem R203107 : Reach 203107 := rs (se 1 (by rfl) ⟨152330, by rfl⟩) R304661
theorem R137585 : Reach 137585 := rs (se 2 (by rfl) ⟨51594, by rfl⟩) R103189
theorem R2005361 : Reach 2005361 := rs (se 2 (by rfl) ⟨752010, by rfl⟩) R1504021
theorem R104915 : Reach 104915 := rs (se 1 (by rfl) ⟨78686, by rfl⟩) R157373
theorem R137713 : Reach 137713 := rs (se 2 (by rfl) ⟨51642, by rfl⟩) R103285
theorem R203249 : Reach 203249 := rs (se 2 (by rfl) ⟨76218, by rfl⟩) R152437
theorem R137747 : Reach 137747 := rs (se 1 (by rfl) ⟨103310, by rfl⟩) R206621
theorem R137857 : Reach 137857 := rs (se 2 (by rfl) ⟨51696, by rfl⟩) R103393
theorem R137875 : Reach 137875 := rs (se 1 (by rfl) ⟨103406, by rfl⟩) R206813
theorem R268973 : Reach 268973 := rs (se 3 (by rfl) ⟨50432, by rfl⟩) R100865
theorem R301745 : Reach 301745 := rs (se 2 (by rfl) ⟨113154, by rfl⟩) R226309
theorem R269027 : Reach 269027 := rs (se 1 (by rfl) ⟨201770, by rfl⟩) R403541
theorem R170723 : Reach 170723 := rs (se 1 (by rfl) ⟨128042, by rfl⟩) R256085
theorem R1055501 : Reach 1055501 := rs (se 3 (by rfl) ⟨197906, by rfl⟩) R395813
theorem R138017 : Reach 138017 := rs (se 2 (by rfl) ⟨51756, by rfl⟩) R103513
theorem R236333 : Reach 236333 := rs (se 3 (by rfl) ⟨44312, by rfl⟩) R88625
theorem R138145 : Reach 138145 := rs (se 2 (by rfl) ⟨51804, by rfl⟩) R103609
theorem R138179 : Reach 138179 := rs (se 1 (by rfl) ⟨103634, by rfl⟩) R207269
theorem R236515 : Reach 236515 := rs (se 1 (by rfl) ⟨177386, by rfl⟩) R354773
theorem R269297 : Reach 269297 := rs (se 2 (by rfl) ⟨100986, by rfl⟩) R201973
theorem R269347 : Reach 269347 := rs (se 1 (by rfl) ⟨202010, by rfl⟩) R404021
theorem R138307 : Reach 138307 := rs (se 1 (by rfl) ⟨103730, by rfl⟩) R207461
theorem R138323 : Reach 138323 := rs (se 1 (by rfl) ⟨103742, by rfl⟩) R207485
theorem R269443 : Reach 269443 := rs (se 1 (by rfl) ⟨202082, by rfl⟩) R404165
theorem R236675 : Reach 236675 := rs (se 1 (by rfl) ⟨177506, by rfl⟩) R355013
theorem R138449 : Reach 138449 := rs (se 2 (by rfl) ⟨51918, by rfl⟩) R103837
theorem R400625 : Reach 400625 := rs (se 2 (by rfl) ⟨150234, by rfl⟩) R300469
theorem R302413 : Reach 302413 := rs (se 3 (by rfl) ⟨56702, by rfl⟩) R113405
theorem R138577 : Reach 138577 := rs (se 2 (by rfl) ⟨51966, by rfl⟩) R103933
theorem R138611 : Reach 138611 := rs (se 1 (by rfl) ⟨103958, by rfl⟩) R207917
theorem R499121 : Reach 499121 := rs (se 2 (by rfl) ⟨187170, by rfl⟩) R374341
theorem R204241 : Reach 204241 := rs (se 2 (by rfl) ⟨76590, by rfl⟩) R153181
theorem R105953 : Reach 105953 := rs (se 2 (by rfl) ⟨39732, by rfl⟩) R79465
theorem R138739 : Reach 138739 := rs (se 1 (by rfl) ⟨104054, by rfl⟩) R208109
theorem R269837 : Reach 269837 := rs (se 3 (by rfl) ⟨50594, by rfl⟩) R101189
theorem R269891 : Reach 269891 := rs (se 1 (by rfl) ⟨202418, by rfl⟩) R404837
theorem R630341 : Reach 630341 := rs (se 4 (by rfl) ⟨59094, by rfl⟩) R118189
theorem R138881 : Reach 138881 := rs (se 2 (by rfl) ⟨52080, by rfl⟩) R104161
theorem R532109 : Reach 532109 := rs (se 3 (by rfl) ⟨99770, by rfl⟩) R199541
theorem R204515 : Reach 204515 := rs (se 1 (by rfl) ⟨153386, by rfl⟩) R306773
theorem R139009 : Reach 139009 := rs (se 2 (by rfl) ⟨52128, by rfl⟩) R104257
theorem R139043 : Reach 139043 := rs (se 1 (by rfl) ⟨104282, by rfl⟩) R208565
theorem R270161 : Reach 270161 := rs (se 2 (by rfl) ⟨101310, by rfl⟩) R202621
theorem R204707 : Reach 204707 := rs (se 1 (by rfl) ⟨153530, by rfl⟩) R307061
theorem R139171 : Reach 139171 := rs (se 1 (by rfl) ⟨104378, by rfl⟩) R208757
theorem R106529 : Reach 106529 := rs (se 2 (by rfl) ⟨39948, by rfl⟩) R79897
theorem R139313 : Reach 139313 := rs (se 2 (by rfl) ⟨52242, by rfl⟩) R104485
theorem R303203 : Reach 303203 := rs (se 1 (by rfl) ⟨227402, by rfl⟩) R454805
theorem R139441 : Reach 139441 := rs (se 2 (by rfl) ⟨52290, by rfl⟩) R104581
theorem R139475 : Reach 139475 := rs (se 1 (by rfl) ⟨104606, by rfl⟩) R209213
theorem R139603 : Reach 139603 := rs (se 1 (by rfl) ⟨104702, by rfl⟩) R209405
theorem R270701 : Reach 270701 := rs (se 3 (by rfl) ⟨50756, by rfl⟩) R101513
theorem R270755 : Reach 270755 := rs (se 1 (by rfl) ⟨203066, by rfl⟩) R406133
theorem R139745 : Reach 139745 := rs (se 2 (by rfl) ⟨52404, by rfl⟩) R104809
theorem R139873 : Reach 139873 := rs (se 2 (by rfl) ⟨52452, by rfl⟩) R104905
theorem R139907 : Reach 139907 := rs (se 1 (by rfl) ⟨104930, by rfl⟩) R209861
theorem R402083 : Reach 402083 := rs (se 1 (by rfl) ⟨301562, by rfl⟩) R603125
theorem R271025 : Reach 271025 := rs (se 2 (by rfl) ⟨101634, by rfl⟩) R203269
theorem R172739 : Reach 172739 := rs (se 1 (by rfl) ⟨129554, by rfl⟩) R259109
theorem R467653 : Reach 467653 := rs (se 4 (by rfl) ⟨43842, by rfl⟩) R87685
theorem R303857 : Reach 303857 := rs (se 2 (by rfl) ⟨113946, by rfl⟩) R227893
theorem R140035 : Reach 140035 := rs (se 1 (by rfl) ⟨105026, by rfl⟩) R210053
theorem R205649 : Reach 205649 := rs (se 2 (by rfl) ⟨77118, by rfl⟩) R154237
theorem R205699 : Reach 205699 := rs (se 1 (by rfl) ⟨154274, by rfl⟩) R308549
theorem R140177 : Reach 140177 := rs (se 2 (by rfl) ⟨52566, by rfl⟩) R105133
theorem R500741 : Reach 500741 := rs (se 4 (by rfl) ⟨46944, by rfl⟩) R93889
theorem R205841 : Reach 205841 := rs (se 2 (by rfl) ⟨77190, by rfl⟩) R154381
theorem R107603 : Reach 107603 := rs (se 1 (by rfl) ⟨80702, by rfl⟩) R161405
theorem R140401 : Reach 140401 := rs (se 2 (by rfl) ⟨52650, by rfl⟩) R105301
theorem R271565 : Reach 271565 := rs (se 3 (by rfl) ⟨50918, by rfl⟩) R101837
theorem R271619 : Reach 271619 := rs (se 1 (by rfl) ⟨203714, by rfl⟩) R407429
theorem R402893 : Reach 402893 := rs (se 3 (by rfl) ⟨75542, by rfl⟩) R151085
theorem R271889 : Reach 271889 := rs (se 2 (by rfl) ⟨101958, by rfl⟩) R203917
theorem R206833 : Reach 206833 := rs (se 2 (by rfl) ⟨77562, by rfl⟩) R155125
theorem R272429 : Reach 272429 := rs (se 3 (by rfl) ⟨51080, by rfl⟩) R102161
theorem R272483 : Reach 272483 := rs (se 1 (by rfl) ⟨204362, by rfl⟩) R408725
theorem R305315 : Reach 305315 := rs (se 1 (by rfl) ⟨228986, by rfl⟩) R457973
theorem R305329 : Reach 305329 := rs (se 2 (by rfl) ⟨114498, by rfl⟩) R228997
theorem R2009285 : Reach 2009285 := rs (se 4 (by rfl) ⟨188370, by rfl⟩) R376741
theorem R207107 : Reach 207107 := rs (se 1 (by rfl) ⟨155330, by rfl⟩) R310661
theorem R272753 : Reach 272753 := rs (se 2 (by rfl) ⟨102282, by rfl⟩) R204565
theorem R207299 : Reach 207299 := rs (se 1 (by rfl) ⟨155474, by rfl⟩) R310949
theorem R240259 : Reach 240259 := rs (se 1 (by rfl) ⟨180194, by rfl⟩) R360389
theorem R469637 : Reach 469637 := rs (se 4 (by rfl) ⟨44028, by rfl⟩) R88057
theorem R174755 : Reach 174755 := rs (se 1 (by rfl) ⟨131066, by rfl⟩) R262133
theorem R436913 : Reach 436913 := rs (se 2 (by rfl) ⟨163842, by rfl⟩) R327685
theorem R371491 : Reach 371491 := rs (se 1 (by rfl) ⟨278618, by rfl⟩) R557237
theorem R273293 : Reach 273293 := rs (se 3 (by rfl) ⟨51242, by rfl⟩) R102485
theorem R273347 : Reach 273347 := rs (se 1 (by rfl) ⟨205010, by rfl⟩) R410021
theorem R273617 : Reach 273617 := rs (se 2 (by rfl) ⟨102606, by rfl⟩) R205213
theorem R208241 : Reach 208241 := rs (se 2 (by rfl) ⟨78090, by rfl⟩) R156181
theorem R208291 : Reach 208291 := rs (se 1 (by rfl) ⟨156218, by rfl⟩) R312437
theorem R208433 : Reach 208433 := rs (se 2 (by rfl) ⟨78162, by rfl⟩) R156325
theorem R306787 : Reach 306787 := rs (se 1 (by rfl) ⟨230090, by rfl⟩) R460181
theorem R274157 : Reach 274157 := rs (se 3 (by rfl) ⟨51404, by rfl⟩) R102809
theorem R274211 : Reach 274211 := rs (se 1 (by rfl) ⟨205658, by rfl⟩) R411317
theorem R176003 : Reach 176003 := rs (se 1 (by rfl) ⟨132002, by rfl⟩) R264005
theorem R110497 : Reach 110497 := rs (se 2 (by rfl) ⟨41436, by rfl⟩) R82873
theorem R339875 : Reach 339875 := rs (se 1 (by rfl) ⟨254906, by rfl⟩) R509813
theorem R274481 : Reach 274481 := rs (se 2 (by rfl) ⟨102930, by rfl⟩) R205861
theorem R405809 : Reach 405809 := rs (se 2 (by rfl) ⟨152178, by rfl⟩) R304357
theorem R176593 : Reach 176593 := rs (se 2 (by rfl) ⟨66222, by rfl⟩) R132445
theorem R209425 : Reach 209425 := rs (se 2 (by rfl) ⟨78534, by rfl⟩) R157069
theorem R275021 : Reach 275021 := rs (se 3 (by rfl) ⟨51566, by rfl⟩) R103133
theorem R275075 : Reach 275075 := rs (se 1 (by rfl) ⟨206306, by rfl⟩) R412613
theorem R144163 : Reach 144163 := rs (se 1 (by rfl) ⟨108122, by rfl⟩) R216245
theorem R209699 : Reach 209699 := rs (se 1 (by rfl) ⟨157274, by rfl⟩) R314549
theorem R275345 : Reach 275345 := rs (se 2 (by rfl) ⟨103254, by rfl⟩) R206509
theorem R144337 : Reach 144337 := rs (se 2 (by rfl) ⟨54126, by rfl⟩) R108253
theorem R209891 : Reach 209891 := rs (se 1 (by rfl) ⟨157418, by rfl⟩) R314837
theorem R275437 : Reach 275437 := rs (se 3 (by rfl) ⟨51644, by rfl⟩) R103289
theorem R144547 : Reach 144547 := rs (se 1 (by rfl) ⟨108410, by rfl⟩) R216821
theorem R3880163 : Reach 3880163 := rs (se 1 (by rfl) ⟨2910122, by rfl⟩) R5820245
theorem R144625 : Reach 144625 := rs (se 2 (by rfl) ⟨54234, by rfl⟩) R108469
theorem R79139 : Reach 79139 := rs (se 1 (by rfl) ⟨59354, by rfl⟩) R118709
theorem R79155 : Reach 79155 := rs (se 1 (by rfl) ⟨59366, by rfl⟩) R118733
theorem R79171 : Reach 79171 := rs (se 1 (by rfl) ⟨59378, by rfl⟩) R118757
theorem R79187 : Reach 79187 := rs (se 1 (by rfl) ⟨59390, by rfl⟩) R118781
theorem R79203 : Reach 79203 := rs (se 1 (by rfl) ⟨59402, by rfl⟩) R118805
theorem R79219 : Reach 79219 := rs (se 1 (by rfl) ⟨59414, by rfl⟩) R118829
theorem R79235 : Reach 79235 := rs (se 1 (by rfl) ⟨59426, by rfl⟩) R118853
theorem R79251 : Reach 79251 := rs (se 1 (by rfl) ⟨59438, by rfl⟩) R118877
theorem R79267 : Reach 79267 := rs (se 1 (by rfl) ⟨59450, by rfl⟩) R118901
theorem R275885 : Reach 275885 := rs (se 3 (by rfl) ⟨51728, by rfl⟩) R103457
theorem R79283 : Reach 79283 := rs (se 1 (by rfl) ⟨59462, by rfl⟩) R118925
theorem R79299 : Reach 79299 := rs (se 1 (by rfl) ⟨59474, by rfl⟩) R118949
theorem R79315 : Reach 79315 := rs (se 1 (by rfl) ⟨59486, by rfl⟩) R118973
theorem R79331 : Reach 79331 := rs (se 1 (by rfl) ⟨59498, by rfl⟩) R118997
theorem R275939 : Reach 275939 := rs (se 1 (by rfl) ⟨206954, by rfl⟩) R413909
theorem R79347 : Reach 79347 := rs (se 1 (by rfl) ⟨59510, by rfl⟩) R119021
theorem R275971 : Reach 275971 := rs (se 1 (by rfl) ⟨206978, by rfl⟩) R413957
theorem R79363 : Reach 79363 := rs (se 1 (by rfl) ⟨59522, by rfl⟩) R119045
theorem R79379 : Reach 79379 := rs (se 1 (by rfl) ⟨59534, by rfl⟩) R119069
theorem R79395 : Reach 79395 := rs (se 1 (by rfl) ⟨59546, by rfl⟩) R119093
theorem R79411 : Reach 79411 := rs (se 1 (by rfl) ⟨59558, by rfl⟩) R119117
theorem R79427 : Reach 79427 := rs (se 1 (by rfl) ⟨59570, by rfl⟩) R119141
theorem R79443 : Reach 79443 := rs (se 1 (by rfl) ⟨59582, by rfl⟩) R119165
theorem R79459 : Reach 79459 := rs (se 1 (by rfl) ⟨59594, by rfl⟩) R119189
theorem R341617 : Reach 341617 := rs (se 2 (by rfl) ⟨128106, by rfl⟩) R256213
theorem R79475 : Reach 79475 := rs (se 1 (by rfl) ⟨59606, by rfl⟩) R119213
theorem R79491 : Reach 79491 := rs (se 1 (by rfl) ⟨59618, by rfl⟩) R119237
theorem R79507 : Reach 79507 := rs (se 1 (by rfl) ⟨59630, by rfl⟩) R119261
theorem R79523 : Reach 79523 := rs (se 1 (by rfl) ⟨59642, by rfl⟩) R119285
theorem R79539 : Reach 79539 := rs (se 1 (by rfl) ⟨59654, by rfl⟩) R119309
theorem R79555 : Reach 79555 := rs (se 1 (by rfl) ⟨59666, by rfl⟩) R119333
theorem R79571 : Reach 79571 := rs (se 1 (by rfl) ⟨59678, by rfl⟩) R119357
theorem R407267 : Reach 407267 := rs (se 1 (by rfl) ⟨305450, by rfl⟩) R610901
theorem R79587 : Reach 79587 := rs (se 1 (by rfl) ⟨59690, by rfl⟩) R119381
theorem R112355 : Reach 112355 := rs (se 1 (by rfl) ⟨84266, by rfl⟩) R168533
theorem R276209 : Reach 276209 := rs (se 2 (by rfl) ⟨103578, by rfl⟩) R207157
theorem R79603 : Reach 79603 := rs (se 1 (by rfl) ⟨59702, by rfl⟩) R119405
theorem R79619 : Reach 79619 := rs (se 1 (by rfl) ⟨59714, by rfl⟩) R119429
theorem R309005 : Reach 309005 := rs (se 3 (by rfl) ⟨57938, by rfl⟩) R115877
theorem R79635 : Reach 79635 := rs (se 1 (by rfl) ⟨59726, by rfl⟩) R119453
theorem R79651 : Reach 79651 := rs (se 1 (by rfl) ⟨59738, by rfl⟩) R119477
theorem R145201 : Reach 145201 := rs (se 2 (by rfl) ⟨54450, by rfl⟩) R108901
theorem R79667 : Reach 79667 := rs (se 1 (by rfl) ⟨59750, by rfl⟩) R119501
theorem R79683 : Reach 79683 := rs (se 1 (by rfl) ⟨59762, by rfl⟩) R119525
theorem R79699 : Reach 79699 := rs (se 1 (by rfl) ⟨59774, by rfl⟩) R119549
theorem R79715 : Reach 79715 := rs (se 1 (by rfl) ⟨59786, by rfl⟩) R119573
theorem R79731 : Reach 79731 := rs (se 1 (by rfl) ⟨59798, by rfl⟩) R119597
theorem R79747 : Reach 79747 := rs (se 1 (by rfl) ⟨59810, by rfl⟩) R119621
theorem R866189 : Reach 866189 := rs (se 3 (by rfl) ⟨162410, by rfl⟩) R324821
theorem R79763 : Reach 79763 := rs (se 1 (by rfl) ⟨59822, by rfl⟩) R119645
theorem R79779 : Reach 79779 := rs (se 1 (by rfl) ⟨59834, by rfl⟩) R119669
theorem R79795 : Reach 79795 := rs (se 1 (by rfl) ⟨59846, by rfl⟩) R119693
theorem R79811 : Reach 79811 := rs (se 1 (by rfl) ⟨59858, by rfl⟩) R119717
theorem R243665 : Reach 243665 := rs (se 2 (by rfl) ⟨91374, by rfl⟩) R182749
theorem R79827 : Reach 79827 := rs (se 1 (by rfl) ⟨59870, by rfl⟩) R119741
theorem R79843 : Reach 79843 := rs (se 1 (by rfl) ⟨59882, by rfl⟩) R119765
theorem R79859 : Reach 79859 := rs (se 1 (by rfl) ⟨59894, by rfl⟩) R119789
theorem R79875 : Reach 79875 := rs (se 1 (by rfl) ⟨59906, by rfl⟩) R119813
theorem R79891 : Reach 79891 := rs (se 1 (by rfl) ⟨59918, by rfl⟩) R119837
theorem R79907 : Reach 79907 := rs (se 1 (by rfl) ⟨59930, by rfl⟩) R119861
theorem R79923 : Reach 79923 := rs (se 1 (by rfl) ⟨59942, by rfl⟩) R119885
theorem R79939 : Reach 79939 := rs (se 1 (by rfl) ⟨59954, by rfl⟩) R119909
theorem R79955 : Reach 79955 := rs (se 1 (by rfl) ⟨59966, by rfl⟩) R119933
theorem R79971 : Reach 79971 := rs (se 1 (by rfl) ⟨59978, by rfl⟩) R119957
theorem R178289 : Reach 178289 := rs (se 2 (by rfl) ⟨66858, by rfl⟩) R133717
theorem R79987 : Reach 79987 := rs (se 1 (by rfl) ⟨59990, by rfl⟩) R119981
theorem R178307 : Reach 178307 := rs (se 1 (by rfl) ⟨133730, by rfl⟩) R267461
theorem R80003 : Reach 80003 := rs (se 1 (by rfl) ⟨60002, by rfl⟩) R120005
theorem R80019 : Reach 80019 := rs (se 1 (by rfl) ⟨60014, by rfl⟩) R120029
theorem R80035 : Reach 80035 := rs (se 1 (by rfl) ⟨60026, by rfl⟩) R120053
theorem R80051 : Reach 80051 := rs (se 1 (by rfl) ⟨60038, by rfl⟩) R120077
theorem R80067 : Reach 80067 := rs (se 1 (by rfl) ⟨60050, by rfl⟩) R120101
theorem R80083 : Reach 80083 := rs (se 1 (by rfl) ⟨60062, by rfl⟩) R120125
theorem R80099 : Reach 80099 := rs (se 1 (by rfl) ⟨60074, by rfl⟩) R120149
theorem R80115 : Reach 80115 := rs (se 1 (by rfl) ⟨60086, by rfl⟩) R120173
theorem R80131 : Reach 80131 := rs (se 1 (by rfl) ⟨60098, by rfl⟩) R120197
theorem R276749 : Reach 276749 := rs (se 3 (by rfl) ⟨51890, by rfl⟩) R103781
theorem R80147 : Reach 80147 := rs (se 1 (by rfl) ⟨60110, by rfl⟩) R120221
theorem R80163 : Reach 80163 := rs (se 1 (by rfl) ⟨60122, by rfl⟩) R120245
theorem R80179 : Reach 80179 := rs (se 1 (by rfl) ⟨60134, by rfl⟩) R120269
theorem R112961 : Reach 112961 := rs (se 2 (by rfl) ⟨42360, by rfl⟩) R84721
theorem R80195 : Reach 80195 := rs (se 1 (by rfl) ⟨60146, by rfl⟩) R120293
theorem R276803 : Reach 276803 := rs (se 1 (by rfl) ⟨207602, by rfl⟩) R415205
theorem R80211 : Reach 80211 := rs (se 1 (by rfl) ⟨60158, by rfl⟩) R120317
theorem R80227 : Reach 80227 := rs (se 1 (by rfl) ⟨60170, by rfl⟩) R120341
theorem R637283 : Reach 637283 := rs (se 1 (by rfl) ⟨477962, by rfl⟩) R955925
theorem R80243 : Reach 80243 := rs (se 1 (by rfl) ⟨60182, by rfl⟩) R120365
theorem R80259 : Reach 80259 := rs (se 1 (by rfl) ⟨60194, by rfl⟩) R120389
theorem R178577 : Reach 178577 := rs (se 2 (by rfl) ⟨66966, by rfl⟩) R133933
theorem R80275 : Reach 80275 := rs (se 1 (by rfl) ⟨60206, by rfl⟩) R120413
theorem R178595 : Reach 178595 := rs (se 1 (by rfl) ⟨133946, by rfl⟩) R267893
theorem R80291 : Reach 80291 := rs (se 1 (by rfl) ⟨60218, by rfl⟩) R120437
theorem R80307 : Reach 80307 := rs (se 1 (by rfl) ⟨60230, by rfl⟩) R120461
theorem R80323 : Reach 80323 := rs (se 1 (by rfl) ⟨60242, by rfl⟩) R120485
theorem R702917 : Reach 702917 := rs (se 4 (by rfl) ⟨65898, by rfl⟩) R131797
theorem R80339 : Reach 80339 := rs (se 1 (by rfl) ⟨60254, by rfl⟩) R120509
theorem R80355 : Reach 80355 := rs (se 1 (by rfl) ⟨60266, by rfl⟩) R120533
theorem R80371 : Reach 80371 := rs (se 1 (by rfl) ⟨60278, by rfl⟩) R120557
theorem R80387 : Reach 80387 := rs (se 1 (by rfl) ⟨60290, by rfl⟩) R120581
theorem R408077 : Reach 408077 := rs (se 3 (by rfl) ⟨76514, by rfl⟩) R153029
theorem R80403 : Reach 80403 := rs (se 1 (by rfl) ⟨60302, by rfl⟩) R120605
theorem R80419 : Reach 80419 := rs (se 1 (by rfl) ⟨60314, by rfl⟩) R120629
theorem R80435 : Reach 80435 := rs (se 1 (by rfl) ⟨60326, by rfl⟩) R120653
theorem R80451 : Reach 80451 := rs (se 1 (by rfl) ⟨60338, by rfl⟩) R120677
theorem R277073 : Reach 277073 := rs (se 2 (by rfl) ⟨103902, by rfl⟩) R207805
theorem R80467 : Reach 80467 := rs (se 1 (by rfl) ⟨60350, by rfl⟩) R120701
theorem R80483 : Reach 80483 := rs (se 1 (by rfl) ⟨60362, by rfl⟩) R120725
theorem R80499 : Reach 80499 := rs (se 1 (by rfl) ⟨60374, by rfl⟩) R120749
theorem R80515 : Reach 80515 := rs (se 1 (by rfl) ⟨60386, by rfl⟩) R120773
theorem R80531 : Reach 80531 := rs (se 1 (by rfl) ⟨60398, by rfl⟩) R120797
theorem R80547 : Reach 80547 := rs (se 1 (by rfl) ⟨60410, by rfl⟩) R120821
theorem R178865 : Reach 178865 := rs (se 2 (by rfl) ⟨67074, by rfl⟩) R134149
theorem R80563 : Reach 80563 := rs (se 1 (by rfl) ⟨60422, by rfl⟩) R120845
theorem R178883 : Reach 178883 := rs (se 1 (by rfl) ⟨134162, by rfl⟩) R268325
theorem R80579 : Reach 80579 := rs (se 1 (by rfl) ⟨60434, by rfl⟩) R120869
theorem R80595 : Reach 80595 := rs (se 1 (by rfl) ⟨60446, by rfl⟩) R120893
theorem R80611 : Reach 80611 := rs (se 1 (by rfl) ⟨60458, by rfl⟩) R120917
theorem R80627 : Reach 80627 := rs (se 1 (by rfl) ⟨60470, by rfl⟩) R120941
theorem R80643 : Reach 80643 := rs (se 1 (by rfl) ⟨60482, by rfl⟩) R120965
theorem R80659 : Reach 80659 := rs (se 1 (by rfl) ⟨60494, by rfl⟩) R120989
theorem R80675 : Reach 80675 := rs (se 1 (by rfl) ⟨60506, by rfl⟩) R121013
theorem R80691 : Reach 80691 := rs (se 1 (by rfl) ⟨60518, by rfl⟩) R121037
theorem R80707 : Reach 80707 := rs (se 1 (by rfl) ⟨60530, by rfl⟩) R121061
theorem R113491 : Reach 113491 := rs (se 1 (by rfl) ⟨85118, by rfl⟩) R170237
theorem R80723 : Reach 80723 := rs (se 1 (by rfl) ⟨60542, by rfl⟩) R121085
theorem R80739 : Reach 80739 := rs (se 1 (by rfl) ⟨60554, by rfl⟩) R121109
theorem R80755 : Reach 80755 := rs (se 1 (by rfl) ⟨60566, by rfl⟩) R121133
theorem R80771 : Reach 80771 := rs (se 1 (by rfl) ⟨60578, by rfl⟩) R121157
theorem R605069 : Reach 605069 := rs (se 3 (by rfl) ⟨113450, by rfl⟩) R226901
theorem R80787 : Reach 80787 := rs (se 1 (by rfl) ⟨60590, by rfl⟩) R121181
theorem R80803 : Reach 80803 := rs (se 1 (by rfl) ⟨60602, by rfl⟩) R121205
theorem R80819 : Reach 80819 := rs (se 1 (by rfl) ⟨60614, by rfl⟩) R121229
theorem R80835 : Reach 80835 := rs (se 1 (by rfl) ⟨60626, by rfl⟩) R121253
theorem R179153 : Reach 179153 := rs (se 2 (by rfl) ⟨67182, by rfl⟩) R134365
theorem R80851 : Reach 80851 := rs (se 1 (by rfl) ⟨60638, by rfl⟩) R121277
theorem R179171 : Reach 179171 := rs (se 1 (by rfl) ⟨134378, by rfl⟩) R268757
theorem R80867 : Reach 80867 := rs (se 1 (by rfl) ⟨60650, by rfl⟩) R121301
theorem R80883 : Reach 80883 := rs (se 1 (by rfl) ⟨60662, by rfl⟩) R121325
theorem R80899 : Reach 80899 := rs (se 1 (by rfl) ⟨60674, by rfl⟩) R121349
theorem R80915 : Reach 80915 := rs (se 1 (by rfl) ⟨60686, by rfl⟩) R121373
theorem R80931 : Reach 80931 := rs (se 1 (by rfl) ⟨60698, by rfl⟩) R121397
theorem R80947 : Reach 80947 := rs (se 1 (by rfl) ⟨60710, by rfl⟩) R121421
theorem R80963 : Reach 80963 := rs (se 1 (by rfl) ⟨60722, by rfl⟩) R121445
theorem R80979 : Reach 80979 := rs (se 1 (by rfl) ⟨60734, by rfl⟩) R121469
theorem R80995 : Reach 80995 := rs (se 1 (by rfl) ⟨60746, by rfl⟩) R121493
theorem R277613 : Reach 277613 := rs (se 3 (by rfl) ⟨52052, by rfl⟩) R104105
theorem R81011 : Reach 81011 := rs (se 1 (by rfl) ⟨60758, by rfl⟩) R121517
theorem R81027 : Reach 81027 := rs (se 1 (by rfl) ⟨60770, by rfl⟩) R121541
theorem R965773 : Reach 965773 := rs (se 3 (by rfl) ⟨181082, by rfl⟩) R362165
theorem R81043 : Reach 81043 := rs (se 1 (by rfl) ⟨60782, by rfl⟩) R121565
theorem R113827 : Reach 113827 := rs (se 1 (by rfl) ⟨85370, by rfl⟩) R170741
theorem R81059 : Reach 81059 := rs (se 1 (by rfl) ⟨60794, by rfl⟩) R121589
theorem R277667 : Reach 277667 := rs (se 1 (by rfl) ⟨208250, by rfl⟩) R416501
theorem R81075 : Reach 81075 := rs (se 1 (by rfl) ⟨60806, by rfl⟩) R121613
theorem R81091 : Reach 81091 := rs (se 1 (by rfl) ⟨60818, by rfl⟩) R121637
theorem R81107 : Reach 81107 := rs (se 1 (by rfl) ⟨60830, by rfl⟩) R121661
theorem R81123 : Reach 81123 := rs (se 1 (by rfl) ⟨60842, by rfl⟩) R121685
theorem R179441 : Reach 179441 := rs (se 2 (by rfl) ⟨67290, by rfl⟩) R134581
theorem R81139 : Reach 81139 := rs (se 1 (by rfl) ⟨60854, by rfl⟩) R121709
theorem R179459 : Reach 179459 := rs (se 1 (by rfl) ⟨134594, by rfl⟩) R269189
theorem R81155 : Reach 81155 := rs (se 1 (by rfl) ⟨60866, by rfl⟩) R121733
theorem R81171 : Reach 81171 := rs (se 1 (by rfl) ⟨60878, by rfl⟩) R121757
theorem R81187 : Reach 81187 := rs (se 1 (by rfl) ⟨60890, by rfl⟩) R121781
theorem R81203 : Reach 81203 := rs (se 1 (by rfl) ⟨60902, by rfl⟩) R121805
theorem R81219 : Reach 81219 := rs (se 1 (by rfl) ⟨60914, by rfl⟩) R121829
theorem R81235 : Reach 81235 := rs (se 1 (by rfl) ⟨60926, by rfl⟩) R121853
theorem R81251 : Reach 81251 := rs (se 1 (by rfl) ⟨60938, by rfl⟩) R121877
theorem R81267 : Reach 81267 := rs (se 1 (by rfl) ⟨60950, by rfl⟩) R121901
theorem R81283 : Reach 81283 := rs (se 1 (by rfl) ⟨60962, by rfl⟩) R121925
theorem R81299 : Reach 81299 := rs (se 1 (by rfl) ⟨60974, by rfl⟩) R121949
theorem R81315 : Reach 81315 := rs (se 1 (by rfl) ⟨60986, by rfl⟩) R121973
theorem R277937 : Reach 277937 := rs (se 2 (by rfl) ⟨104226, by rfl⟩) R208453
theorem R81331 : Reach 81331 := rs (se 1 (by rfl) ⟨60998, by rfl⟩) R121997
theorem R81347 : Reach 81347 := rs (se 1 (by rfl) ⟨61010, by rfl⟩) R122021
theorem R81363 : Reach 81363 := rs (se 1 (by rfl) ⟨61022, by rfl⟩) R122045
theorem R81379 : Reach 81379 := rs (se 1 (by rfl) ⟨61034, by rfl⟩) R122069
theorem R81395 : Reach 81395 := rs (se 1 (by rfl) ⟨61046, by rfl⟩) R122093
theorem R81411 : Reach 81411 := rs (se 1 (by rfl) ⟨61058, by rfl⟩) R122117
theorem R343565 : Reach 343565 := rs (se 3 (by rfl) ⟨64418, by rfl⟩) R128837
theorem R179729 : Reach 179729 := rs (se 2 (by rfl) ⟨67398, by rfl⟩) R134797
theorem R81427 : Reach 81427 := rs (se 1 (by rfl) ⟨61070, by rfl⟩) R122141
theorem R179747 : Reach 179747 := rs (se 1 (by rfl) ⟨134810, by rfl⟩) R269621
theorem R81443 : Reach 81443 := rs (se 1 (by rfl) ⟨61082, by rfl⟩) R122165
theorem R81459 : Reach 81459 := rs (se 1 (by rfl) ⟨61094, by rfl⟩) R122189
theorem R81475 : Reach 81475 := rs (se 1 (by rfl) ⟨61106, by rfl⟩) R122213
theorem R147025 : Reach 147025 := rs (se 2 (by rfl) ⟨55134, by rfl⟩) R110269
theorem R81491 : Reach 81491 := rs (se 1 (by rfl) ⟨61118, by rfl⟩) R122237
theorem R81507 : Reach 81507 := rs (se 1 (by rfl) ⟨61130, by rfl⟩) R122261
theorem R507505 : Reach 507505 := rs (se 2 (by rfl) ⟨190314, by rfl⟩) R380629
theorem R81523 : Reach 81523 := rs (se 1 (by rfl) ⟨61142, by rfl⟩) R122285
theorem R81539 : Reach 81539 := rs (se 1 (by rfl) ⟨61154, by rfl⟩) R122309
theorem R81555 : Reach 81555 := rs (se 1 (by rfl) ⟨61166, by rfl⟩) R122333
theorem R81571 : Reach 81571 := rs (se 1 (by rfl) ⟨61178, by rfl⟩) R122357
theorem R81587 : Reach 81587 := rs (se 1 (by rfl) ⟨61190, by rfl⟩) R122381
theorem R81603 : Reach 81603 := rs (se 1 (by rfl) ⟨61202, by rfl⟩) R122405
theorem R114385 : Reach 114385 := rs (se 2 (by rfl) ⟨42894, by rfl⟩) R85789
theorem R81619 : Reach 81619 := rs (se 1 (by rfl) ⟨61214, by rfl⟩) R122429
theorem R81635 : Reach 81635 := rs (se 1 (by rfl) ⟨61226, by rfl⟩) R122453
theorem R114419 : Reach 114419 := rs (se 1 (by rfl) ⟨85814, by rfl⟩) R171629
theorem R81651 : Reach 81651 := rs (se 1 (by rfl) ⟨61238, by rfl⟩) R122477
theorem R81667 : Reach 81667 := rs (se 1 (by rfl) ⟨61250, by rfl⟩) R122501
theorem R81683 : Reach 81683 := rs (se 1 (by rfl) ⟨61262, by rfl⟩) R122525
theorem R81699 : Reach 81699 := rs (se 1 (by rfl) ⟨61274, by rfl⟩) R122549
theorem R180017 : Reach 180017 := rs (se 2 (by rfl) ⟨67506, by rfl⟩) R135013
theorem R81715 : Reach 81715 := rs (se 1 (by rfl) ⟨61286, by rfl⟩) R122573
theorem R180035 : Reach 180035 := rs (se 1 (by rfl) ⟨135026, by rfl⟩) R270053
theorem R81731 : Reach 81731 := rs (se 1 (by rfl) ⟨61298, by rfl⟩) R122597
theorem R81747 : Reach 81747 := rs (se 1 (by rfl) ⟨61310, by rfl⟩) R122621
theorem R81763 : Reach 81763 := rs (se 1 (by rfl) ⟨61322, by rfl⟩) R122645
theorem R81779 : Reach 81779 := rs (se 1 (by rfl) ⟨61334, by rfl⟩) R122669
theorem R81795 : Reach 81795 := rs (se 1 (by rfl) ⟨61346, by rfl⟩) R122693
theorem R2015117 : Reach 2015117 := rs (se 3 (by rfl) ⟨377834, by rfl⟩) R755669
theorem R81811 : Reach 81811 := rs (se 1 (by rfl) ⟨61358, by rfl⟩) R122717
theorem R81827 : Reach 81827 := rs (se 1 (by rfl) ⟨61370, by rfl⟩) R122741
theorem R81843 : Reach 81843 := rs (se 1 (by rfl) ⟨61382, by rfl⟩) R122765
theorem R81859 : Reach 81859 := rs (se 1 (by rfl) ⟨61394, by rfl⟩) R122789
theorem R278477 : Reach 278477 := rs (se 3 (by rfl) ⟨52214, by rfl⟩) R104429
theorem R81875 : Reach 81875 := rs (se 1 (by rfl) ⟨61406, by rfl⟩) R122813
theorem R81891 : Reach 81891 := rs (se 1 (by rfl) ⟨61418, by rfl⟩) R122837
theorem R81907 : Reach 81907 := rs (se 1 (by rfl) ⟨61430, by rfl⟩) R122861
theorem R81923 : Reach 81923 := rs (se 1 (by rfl) ⟨61442, by rfl⟩) R122885
theorem R278531 : Reach 278531 := rs (se 1 (by rfl) ⟨208898, by rfl⟩) R417797
theorem R81939 : Reach 81939 := rs (se 1 (by rfl) ⟨61454, by rfl⟩) R122909
theorem R81955 : Reach 81955 := rs (se 1 (by rfl) ⟨61466, by rfl⟩) R122933
theorem R81971 : Reach 81971 := rs (se 1 (by rfl) ⟨61478, by rfl⟩) R122957
theorem R81987 : Reach 81987 := rs (se 1 (by rfl) ⟨61490, by rfl⟩) R122981
theorem R180305 : Reach 180305 := rs (se 2 (by rfl) ⟨67614, by rfl⟩) R135229
theorem R82003 : Reach 82003 := rs (se 1 (by rfl) ⟨61502, by rfl⟩) R123005
theorem R180323 : Reach 180323 := rs (se 1 (by rfl) ⟨135242, by rfl⟩) R270485
theorem R82019 : Reach 82019 := rs (se 1 (by rfl) ⟨61514, by rfl⟩) R123029
theorem R82035 : Reach 82035 := rs (se 1 (by rfl) ⟨61526, by rfl⟩) R123053
theorem R82051 : Reach 82051 := rs (se 1 (by rfl) ⟨61538, by rfl⟩) R123077
theorem R82067 : Reach 82067 := rs (se 1 (by rfl) ⟨61550, by rfl⟩) R123101
theorem R82083 : Reach 82083 := rs (se 1 (by rfl) ⟨61562, by rfl⟩) R123125
theorem R82099 : Reach 82099 := rs (se 1 (by rfl) ⟨61574, by rfl⟩) R123149
theorem R82115 : Reach 82115 := rs (se 1 (by rfl) ⟨61586, by rfl⟩) R123173
theorem R82131 : Reach 82131 := rs (se 1 (by rfl) ⟨61598, by rfl⟩) R123197
theorem R82147 : Reach 82147 := rs (se 1 (by rfl) ⟨61610, by rfl⟩) R123221
theorem R213229 : Reach 213229 := rs (se 3 (by rfl) ⟨39980, by rfl⟩) R79961
theorem R82163 : Reach 82163 := rs (se 1 (by rfl) ⟨61622, by rfl⟩) R123245
theorem R82179 : Reach 82179 := rs (se 1 (by rfl) ⟨61634, by rfl⟩) R123269
theorem R82195 : Reach 82195 := rs (se 1 (by rfl) ⟨61646, by rfl⟩) R123293
theorem R278801 : Reach 278801 := rs (se 2 (by rfl) ⟨104550, by rfl⟩) R209101
theorem R114977 : Reach 114977 := rs (se 2 (by rfl) ⟨43116, by rfl⟩) R86233
theorem R82211 : Reach 82211 := rs (se 1 (by rfl) ⟨61658, by rfl⟩) R123317
theorem R82227 : Reach 82227 := rs (se 1 (by rfl) ⟨61670, by rfl⟩) R123341
theorem R82243 : Reach 82243 := rs (se 1 (by rfl) ⟨61682, by rfl⟩) R123365
theorem R82259 : Reach 82259 := rs (se 1 (by rfl) ⟨61694, by rfl⟩) R123389
theorem R147811 : Reach 147811 := rs (se 1 (by rfl) ⟨110858, by rfl⟩) R221717
theorem R82275 : Reach 82275 := rs (se 1 (by rfl) ⟨61706, by rfl⟩) R123413
theorem R180593 : Reach 180593 := rs (se 2 (by rfl) ⟨67722, by rfl⟩) R135445
theorem R115057 : Reach 115057 := rs (se 2 (by rfl) ⟨43146, by rfl⟩) R86293
theorem R82291 : Reach 82291 := rs (se 1 (by rfl) ⟨61718, by rfl⟩) R123437
theorem R180611 : Reach 180611 := rs (se 1 (by rfl) ⟨135458, by rfl⟩) R270917
theorem R82307 : Reach 82307 := rs (se 1 (by rfl) ⟨61730, by rfl⟩) R123461
theorem R82323 : Reach 82323 := rs (se 1 (by rfl) ⟨61742, by rfl⟩) R123485
theorem R82339 : Reach 82339 := rs (se 1 (by rfl) ⟨61754, by rfl⟩) R123509
theorem R82355 : Reach 82355 := rs (se 1 (by rfl) ⟨61766, by rfl⟩) R123533
theorem R82371 : Reach 82371 := rs (se 1 (by rfl) ⟨61778, by rfl⟩) R123557
theorem R82387 : Reach 82387 := rs (se 1 (by rfl) ⟨61790, by rfl⟩) R123581
theorem R82403 : Reach 82403 := rs (se 1 (by rfl) ⟨61802, by rfl⟩) R123605
theorem R82419 : Reach 82419 := rs (se 1 (by rfl) ⟨61814, by rfl⟩) R123629
theorem R82435 : Reach 82435 := rs (se 1 (by rfl) ⟨61826, by rfl⟩) R123653
theorem R82451 : Reach 82451 := rs (se 1 (by rfl) ⟨61838, by rfl⟩) R123677
theorem R82467 : Reach 82467 := rs (se 1 (by rfl) ⟨61850, by rfl⟩) R123701
theorem R82483 : Reach 82483 := rs (se 1 (by rfl) ⟨61862, by rfl⟩) R123725
theorem R82499 : Reach 82499 := rs (se 1 (by rfl) ⟨61874, by rfl⟩) R123749
theorem R82515 : Reach 82515 := rs (se 1 (by rfl) ⟨61886, by rfl⟩) R123773
theorem R82531 : Reach 82531 := rs (se 1 (by rfl) ⟨61898, by rfl⟩) R123797
theorem R311921 : Reach 311921 := rs (se 2 (by rfl) ⟨116970, by rfl⟩) R233941
theorem R82547 : Reach 82547 := rs (se 1 (by rfl) ⟨61910, by rfl⟩) R123821
theorem R82563 : Reach 82563 := rs (se 1 (by rfl) ⟨61922, by rfl⟩) R123845
theorem R180881 : Reach 180881 := rs (se 2 (by rfl) ⟨67830, by rfl⟩) R135661
theorem R82579 : Reach 82579 := rs (se 1 (by rfl) ⟨61934, by rfl⟩) R123869
theorem R180899 : Reach 180899 := rs (se 1 (by rfl) ⟨135674, by rfl⟩) R271349
theorem R82595 : Reach 82595 := rs (se 1 (by rfl) ⟨61946, by rfl⟩) R123893
theorem R82611 : Reach 82611 := rs (se 1 (by rfl) ⟨61958, by rfl⟩) R123917
theorem R82627 : Reach 82627 := rs (se 1 (by rfl) ⟨61970, by rfl⟩) R123941
theorem R82643 : Reach 82643 := rs (se 1 (by rfl) ⟨61982, by rfl⟩) R123965
theorem R82659 : Reach 82659 := rs (se 1 (by rfl) ⟨61994, by rfl⟩) R123989
theorem R82675 : Reach 82675 := rs (se 1 (by rfl) ⟨62006, by rfl⟩) R124013
theorem R82691 : Reach 82691 := rs (se 1 (by rfl) ⟨62018, by rfl⟩) R124037
theorem R82707 : Reach 82707 := rs (se 1 (by rfl) ⟨62030, by rfl⟩) R124061
theorem R82723 : Reach 82723 := rs (se 1 (by rfl) ⟨62042, by rfl⟩) R124085
theorem R279341 : Reach 279341 := rs (se 3 (by rfl) ⟨52376, by rfl⟩) R104753
theorem R115507 : Reach 115507 := rs (se 1 (by rfl) ⟨86630, by rfl⟩) R173261
theorem R82739 : Reach 82739 := rs (se 1 (by rfl) ⟨62054, by rfl⟩) R124109
theorem R82755 : Reach 82755 := rs (se 1 (by rfl) ⟨62066, by rfl⟩) R124133
theorem R279377 : Reach 279377 := rs (se 2 (by rfl) ⟨104766, by rfl⟩) R209533
theorem R82771 : Reach 82771 := rs (se 1 (by rfl) ⟨62078, by rfl⟩) R124157
theorem R279395 : Reach 279395 := rs (se 1 (by rfl) ⟨209546, by rfl⟩) R419093
theorem R82787 : Reach 82787 := rs (se 1 (by rfl) ⟨62090, by rfl⟩) R124181
theorem R82803 : Reach 82803 := rs (se 1 (by rfl) ⟨62102, by rfl⟩) R124205
theorem R82819 : Reach 82819 := rs (se 1 (by rfl) ⟨62114, by rfl⟩) R124229
theorem R82835 : Reach 82835 := rs (se 1 (by rfl) ⟨62126, by rfl⟩) R124253
theorem R82851 : Reach 82851 := rs (se 1 (by rfl) ⟨62138, by rfl⟩) R124277
theorem R181169 : Reach 181169 := rs (se 2 (by rfl) ⟨67938, by rfl⟩) R135877
theorem R82867 : Reach 82867 := rs (se 1 (by rfl) ⟨62150, by rfl⟩) R124301
theorem R181187 : Reach 181187 := rs (se 1 (by rfl) ⟨135890, by rfl⟩) R271781
theorem R82883 : Reach 82883 := rs (se 1 (by rfl) ⟨62162, by rfl⟩) R124325
theorem R82899 : Reach 82899 := rs (se 1 (by rfl) ⟨62174, by rfl⟩) R124349
theorem R82915 : Reach 82915 := rs (se 1 (by rfl) ⟨62186, by rfl⟩) R124373
theorem R82931 : Reach 82931 := rs (se 1 (by rfl) ⟨62198, by rfl⟩) R124397
theorem R214019 : Reach 214019 := rs (se 1 (by rfl) ⟨160514, by rfl⟩) R321029
theorem R82947 : Reach 82947 := rs (se 1 (by rfl) ⟨62210, by rfl⟩) R124421
theorem R82963 : Reach 82963 := rs (se 1 (by rfl) ⟨62222, by rfl⟩) R124445
theorem R82979 : Reach 82979 := rs (se 1 (by rfl) ⟨62234, by rfl⟩) R124469
theorem R148529 : Reach 148529 := rs (se 2 (by rfl) ⟨55698, by rfl⟩) R111397
theorem R82995 : Reach 82995 := rs (se 1 (by rfl) ⟨62246, by rfl⟩) R124493
theorem R83011 : Reach 83011 := rs (se 1 (by rfl) ⟨62258, by rfl⟩) R124517
theorem R83027 : Reach 83027 := rs (se 1 (by rfl) ⟨62270, by rfl⟩) R124541
theorem R83043 : Reach 83043 := rs (se 1 (by rfl) ⟨62282, by rfl⟩) R124565
theorem R279665 : Reach 279665 := rs (se 2 (by rfl) ⟨104874, by rfl⟩) R209749
theorem R83059 : Reach 83059 := rs (se 1 (by rfl) ⟨62294, by rfl⟩) R124589
theorem R115843 : Reach 115843 := rs (se 1 (by rfl) ⟨86882, by rfl⟩) R173765
theorem R83075 : Reach 83075 := rs (se 1 (by rfl) ⟨62306, by rfl⟩) R124613
theorem R1033357 : Reach 1033357 := rs (se 3 (by rfl) ⟨193754, by rfl⟩) R387509
theorem R83091 : Reach 83091 := rs (se 1 (by rfl) ⟨62318, by rfl⟩) R124637
theorem R83107 : Reach 83107 := rs (se 1 (by rfl) ⟨62330, by rfl⟩) R124661
theorem R83123 : Reach 83123 := rs (se 1 (by rfl) ⟨62342, by rfl⟩) R124685
theorem R181457 : Reach 181457 := rs (se 2 (by rfl) ⟨68046, by rfl⟩) R136093
theorem R181475 : Reach 181475 := rs (se 1 (by rfl) ⟨136106, by rfl⟩) R272213
theorem R443717 : Reach 443717 := rs (se 4 (by rfl) ⟨41598, by rfl⟩) R83197
theorem R410993 : Reach 410993 := rs (se 2 (by rfl) ⟨154122, by rfl⟩) R308245
theorem R181745 : Reach 181745 := rs (se 2 (by rfl) ⟨68154, by rfl⟩) R136309
theorem R181763 : Reach 181763 := rs (se 1 (by rfl) ⟨136322, by rfl⟩) R272645
theorem R116321 : Reach 116321 := rs (se 2 (by rfl) ⟨43620, by rfl⟩) R87241
theorem R149123 : Reach 149123 := rs (se 1 (by rfl) ⟨111842, by rfl⟩) R223685
theorem R280205 : Reach 280205 := rs (se 3 (by rfl) ⟨52538, by rfl⟩) R105077
theorem R83651 : Reach 83651 := rs (se 1 (by rfl) ⟨62738, by rfl⟩) R125477
theorem R280259 : Reach 280259 := rs (se 1 (by rfl) ⟨210194, by rfl⟩) R420389
theorem R116435 : Reach 116435 := rs (se 1 (by rfl) ⟨87326, by rfl⟩) R174653
theorem R607985 : Reach 607985 := rs (se 2 (by rfl) ⟨227994, by rfl⟩) R455989
theorem R182033 : Reach 182033 := rs (se 2 (by rfl) ⟨68262, by rfl⟩) R136525
theorem R182051 : Reach 182051 := rs (se 1 (by rfl) ⟨136538, by rfl⟩) R273077
theorem R116515 : Reach 116515 := rs (se 1 (by rfl) ⟨87386, by rfl⟩) R174773
theorem R149411 : Reach 149411 := rs (se 1 (by rfl) ⟨112058, by rfl⟩) R224117
theorem R280529 : Reach 280529 := rs (se 2 (by rfl) ⟨105198, by rfl⟩) R210397
theorem R313379 : Reach 313379 := rs (se 1 (by rfl) ⟨235034, by rfl⟩) R470069
theorem R182321 : Reach 182321 := rs (se 2 (by rfl) ⟨68370, by rfl⟩) R136741
theorem R182339 : Reach 182339 := rs (se 1 (by rfl) ⟨136754, by rfl⟩) R273509
theorem R968773 : Reach 968773 := rs (se 4 (by rfl) ⟨90822, by rfl⟩) R181645
theorem R936035 : Reach 936035 := rs (se 1 (by rfl) ⟨702026, by rfl⟩) R1404053
theorem R149635 : Reach 149635 := rs (se 1 (by rfl) ⟨112226, by rfl⟩) R224453
theorem R149699 : Reach 149699 := rs (se 1 (by rfl) ⟨112274, by rfl⟩) R224549
theorem R248141 : Reach 248141 := rs (se 3 (by rfl) ⟨46526, by rfl⟩) R93053
theorem R182609 : Reach 182609 := rs (se 2 (by rfl) ⟨68478, by rfl⟩) R136957
theorem R117073 : Reach 117073 := rs (se 2 (by rfl) ⟨43902, by rfl⟩) R87805
theorem R182627 : Reach 182627 := rs (se 1 (by rfl) ⟨136970, by rfl⟩) R273941
theorem R117121 : Reach 117121 := rs (se 2 (by rfl) ⟨43920, by rfl⟩) R87841
theorem R1034693 : Reach 1034693 := rs (se 4 (by rfl) ⟨97002, by rfl⟩) R194005
theorem R182897 : Reach 182897 := rs (se 2 (by rfl) ⟨68586, by rfl⟩) R137173
theorem R182915 : Reach 182915 := rs (se 1 (by rfl) ⟨137186, by rfl⟩) R274373
theorem R412451 : Reach 412451 := rs (se 1 (by rfl) ⟨309338, by rfl⟩) R618677
theorem R183185 : Reach 183185 := rs (se 2 (by rfl) ⟨68694, by rfl⟩) R137389
theorem R183203 : Reach 183203 := rs (se 1 (by rfl) ⟨137402, by rfl⟩) R274805
theorem R314381 : Reach 314381 := rs (se 3 (by rfl) ⟨58946, by rfl⟩) R117893
theorem R150545 : Reach 150545 := rs (se 2 (by rfl) ⟨56454, by rfl⟩) R112909
theorem R117779 : Reach 117779 := rs (se 1 (by rfl) ⟨88334, by rfl⟩) R176669
theorem R183473 : Reach 183473 := rs (se 2 (by rfl) ⟨68802, by rfl⟩) R137605
theorem R183491 : Reach 183491 := rs (se 1 (by rfl) ⟨137618, by rfl⟩) R275237
theorem R5950691 : Reach 5950691 := rs (se 1 (by rfl) ⟨4463018, by rfl⟩) R8926037
theorem R150979 : Reach 150979 := rs (se 1 (by rfl) ⟨113234, by rfl⟩) R226469
theorem R347597 : Reach 347597 := rs (se 3 (by rfl) ⟨65174, by rfl⟩) R130349
theorem R183761 : Reach 183761 := rs (se 2 (by rfl) ⟨68910, by rfl⟩) R137821
theorem R183779 : Reach 183779 := rs (se 1 (by rfl) ⟨137834, by rfl⟩) R275669
theorem R413261 : Reach 413261 := rs (se 3 (by rfl) ⟨77486, by rfl⟩) R154973
theorem R151139 : Reach 151139 := rs (se 1 (by rfl) ⟨113354, by rfl⟩) R226709
theorem R970481 : Reach 970481 := rs (se 2 (by rfl) ⟨363930, by rfl⟩) R727861
theorem R184049 : Reach 184049 := rs (se 2 (by rfl) ⟨69018, by rfl⟩) R138037
theorem R184067 : Reach 184067 := rs (se 1 (by rfl) ⟨138050, by rfl⟩) R276101
theorem R347939 : Reach 347939 := rs (se 1 (by rfl) ⟨260954, by rfl⟩) R521909
theorem R118579 : Reach 118579 := rs (se 1 (by rfl) ⟨88934, by rfl⟩) R177869
theorem R118643 : Reach 118643 := rs (se 1 (by rfl) ⟨88982, by rfl⟩) R177965
theorem R118691 : Reach 118691 := rs (se 1 (by rfl) ⟨89018, by rfl⟩) R178037
theorem R118721 : Reach 118721 := rs (se 2 (by rfl) ⟨44520, by rfl⟩) R89041
theorem R118739 : Reach 118739 := rs (se 1 (by rfl) ⟨89054, by rfl⟩) R178109
theorem R118769 : Reach 118769 := rs (se 2 (by rfl) ⟨44538, by rfl⟩) R89077
theorem R118787 : Reach 118787 := rs (se 1 (by rfl) ⟨89090, by rfl⟩) R178181
theorem R184337 : Reach 184337 := rs (se 2 (by rfl) ⟨69126, by rfl⟩) R138253
theorem R118817 : Reach 118817 := rs (se 2 (by rfl) ⟨44556, by rfl⟩) R89113
theorem R184355 : Reach 184355 := rs (se 1 (by rfl) ⟨138266, by rfl⟩) R276533
theorem R118835 : Reach 118835 := rs (se 1 (by rfl) ⟨89126, by rfl⟩) R178253
theorem R118865 : Reach 118865 := rs (se 2 (by rfl) ⟨44574, by rfl⟩) R89149
theorem R118883 : Reach 118883 := rs (se 1 (by rfl) ⟨89162, by rfl⟩) R178325
theorem R118913 : Reach 118913 := rs (se 2 (by rfl) ⟨44592, by rfl⟩) R89185
theorem R118931 : Reach 118931 := rs (se 1 (by rfl) ⟨89198, by rfl⟩) R178397
theorem R118961 : Reach 118961 := rs (se 2 (by rfl) ⟨44610, by rfl⟩) R89221
theorem R118979 : Reach 118979 := rs (se 1 (by rfl) ⟨89234, by rfl⟩) R178469
theorem R119009 : Reach 119009 := rs (se 2 (by rfl) ⟨44628, by rfl⟩) R89257
theorem R348401 : Reach 348401 := rs (se 2 (by rfl) ⟨130650, by rfl⟩) R261301
theorem R119027 : Reach 119027 := rs (se 1 (by rfl) ⟨89270, by rfl⟩) R178541
theorem R119057 : Reach 119057 := rs (se 2 (by rfl) ⟨44646, by rfl⟩) R89293
theorem R119075 : Reach 119075 := rs (se 1 (by rfl) ⟨89306, by rfl⟩) R178613
theorem R184625 : Reach 184625 := rs (se 2 (by rfl) ⟨69234, by rfl⟩) R138469
theorem R119105 : Reach 119105 := rs (se 2 (by rfl) ⟨44664, by rfl⟩) R89329
theorem R184643 : Reach 184643 := rs (se 1 (by rfl) ⟨138482, by rfl⟩) R276965
theorem R119123 : Reach 119123 := rs (se 1 (by rfl) ⟨89342, by rfl⟩) R178685
theorem R119153 : Reach 119153 := rs (se 2 (by rfl) ⟨44682, by rfl⟩) R89365
theorem R119171 : Reach 119171 := rs (se 1 (by rfl) ⟨89378, by rfl⟩) R178757
theorem R119201 : Reach 119201 := rs (se 2 (by rfl) ⟨44700, by rfl⟩) R89401
theorem R119219 : Reach 119219 := rs (se 1 (by rfl) ⟨89414, by rfl⟩) R178829
theorem R119249 : Reach 119249 := rs (se 2 (by rfl) ⟨44718, by rfl⟩) R89437
theorem R119267 : Reach 119267 := rs (se 1 (by rfl) ⟨89450, by rfl⟩) R178901
theorem R119297 : Reach 119297 := rs (se 2 (by rfl) ⟨44736, by rfl⟩) R89473
theorem R119315 : Reach 119315 := rs (se 1 (by rfl) ⟨89486, by rfl⟩) R178973
theorem R119345 : Reach 119345 := rs (se 2 (by rfl) ⟨44754, by rfl⟩) R89509
theorem R119363 : Reach 119363 := rs (se 1 (by rfl) ⟨89522, by rfl⟩) R179045
theorem R184913 : Reach 184913 := rs (se 2 (by rfl) ⟨69342, by rfl⟩) R138685
theorem R119393 : Reach 119393 := rs (se 2 (by rfl) ⟨44772, by rfl⟩) R89545
theorem R184931 : Reach 184931 := rs (se 1 (by rfl) ⟨138698, by rfl⟩) R277397
theorem R119411 : Reach 119411 := rs (se 1 (by rfl) ⟨89558, by rfl⟩) R179117
theorem R119441 : Reach 119441 := rs (se 2 (by rfl) ⟨44790, by rfl⟩) R89581
theorem R152209 : Reach 152209 := rs (se 2 (by rfl) ⟨57078, by rfl⟩) R114157
theorem R119459 : Reach 119459 := rs (se 1 (by rfl) ⟨89594, by rfl⟩) R179189
theorem R119489 : Reach 119489 := rs (se 2 (by rfl) ⟨44808, by rfl⟩) R89617
theorem R119507 : Reach 119507 := rs (se 1 (by rfl) ⟨89630, by rfl⟩) R179261
theorem R119537 : Reach 119537 := rs (se 2 (by rfl) ⟨44826, by rfl⟩) R89653
theorem R119555 : Reach 119555 := rs (se 1 (by rfl) ⟨89666, by rfl⟩) R179333
theorem R119585 : Reach 119585 := rs (se 2 (by rfl) ⟨44844, by rfl⟩) R89689
theorem R119603 : Reach 119603 := rs (se 1 (by rfl) ⟨89702, by rfl⟩) R179405
theorem R512837 : Reach 512837 := rs (se 4 (by rfl) ⟨48078, by rfl⟩) R96157
theorem R119633 : Reach 119633 := rs (se 2 (by rfl) ⟨44862, by rfl⟩) R89725
theorem R119651 : Reach 119651 := rs (se 1 (by rfl) ⟨89738, by rfl⟩) R179477
theorem R185201 : Reach 185201 := rs (se 2 (by rfl) ⟨69450, by rfl⟩) R138901
theorem R119681 : Reach 119681 := rs (se 2 (by rfl) ⟨44880, by rfl⟩) R89761
theorem R185219 : Reach 185219 := rs (se 1 (by rfl) ⟨138914, by rfl⟩) R277829
theorem R119699 : Reach 119699 := rs (se 1 (by rfl) ⟨89774, by rfl⟩) R179549
theorem R119729 : Reach 119729 := rs (se 2 (by rfl) ⟨44898, by rfl⟩) R89797
theorem R119747 : Reach 119747 := rs (se 1 (by rfl) ⟨89810, by rfl⟩) R179621
theorem R119777 : Reach 119777 := rs (se 2 (by rfl) ⟨44916, by rfl⟩) R89833
theorem R119795 : Reach 119795 := rs (se 1 (by rfl) ⟨89846, by rfl⟩) R179693
theorem R119825 : Reach 119825 := rs (se 2 (by rfl) ⟨44934, by rfl⟩) R89869
theorem R119843 : Reach 119843 := rs (se 1 (by rfl) ⟨89882, by rfl⟩) R179765
theorem R119873 : Reach 119873 := rs (se 2 (by rfl) ⟨44952, by rfl⟩) R89905
theorem R119891 : Reach 119891 := rs (se 1 (by rfl) ⟨89918, by rfl⟩) R179837
theorem R119921 : Reach 119921 := rs (se 2 (by rfl) ⟨44970, by rfl⟩) R89941
theorem R119939 : Reach 119939 := rs (se 1 (by rfl) ⟨89954, by rfl⟩) R179909
theorem R185489 : Reach 185489 := rs (se 2 (by rfl) ⟨69558, by rfl⟩) R139117
theorem R119969 : Reach 119969 := rs (se 2 (by rfl) ⟨44988, by rfl⟩) R89977
theorem R87203 : Reach 87203 := rs (se 1 (by rfl) ⟨65402, by rfl⟩) R130805
theorem R185507 : Reach 185507 := rs (se 1 (by rfl) ⟨139130, by rfl⟩) R278261
theorem R119987 : Reach 119987 := rs (se 1 (by rfl) ⟨89990, by rfl⟩) R179981
theorem R120017 : Reach 120017 := rs (se 2 (by rfl) ⟨45006, by rfl⟩) R90013
theorem R120035 : Reach 120035 := rs (se 1 (by rfl) ⟨90026, by rfl⟩) R180053
theorem R120065 : Reach 120065 := rs (se 2 (by rfl) ⟨45024, by rfl⟩) R90049
theorem R120083 : Reach 120083 := rs (se 1 (by rfl) ⟨90062, by rfl⟩) R180125
theorem R120113 : Reach 120113 := rs (se 2 (by rfl) ⟨45042, by rfl⟩) R90085
theorem R120131 : Reach 120131 := rs (se 1 (by rfl) ⟨90098, by rfl⟩) R180197
theorem R120161 : Reach 120161 := rs (se 2 (by rfl) ⟨45060, by rfl⟩) R90121
theorem R120179 : Reach 120179 := rs (se 1 (by rfl) ⟨90134, by rfl⟩) R180269
theorem R120209 : Reach 120209 := rs (se 2 (by rfl) ⟨45078, by rfl⟩) R90157
theorem R120227 : Reach 120227 := rs (se 1 (by rfl) ⟨90170, by rfl⟩) R180341
theorem R185777 : Reach 185777 := rs (se 2 (by rfl) ⟨69666, by rfl⟩) R139333
theorem R120257 : Reach 120257 := rs (se 2 (by rfl) ⟨45096, by rfl⟩) R90193
theorem R185795 : Reach 185795 := rs (se 1 (by rfl) ⟨139346, by rfl⟩) R278693
theorem R120275 : Reach 120275 := rs (se 1 (by rfl) ⟨90206, by rfl⟩) R180413
theorem R120305 : Reach 120305 := rs (se 2 (by rfl) ⟨45114, by rfl⟩) R90229
theorem R120323 : Reach 120323 := rs (se 1 (by rfl) ⟨90242, by rfl⟩) R180485
theorem R120353 : Reach 120353 := rs (se 2 (by rfl) ⟨45132, by rfl⟩) R90265
theorem R218659 : Reach 218659 := rs (se 1 (by rfl) ⟨163994, by rfl⟩) R327989
theorem R120371 : Reach 120371 := rs (se 1 (by rfl) ⟨90278, by rfl⟩) R180557
theorem R120401 : Reach 120401 := rs (se 2 (by rfl) ⟨45150, by rfl⟩) R90301
theorem R120419 : Reach 120419 := rs (se 1 (by rfl) ⟨90314, by rfl⟩) R180629
theorem R120449 : Reach 120449 := rs (se 2 (by rfl) ⟨45168, by rfl⟩) R90337
theorem R120467 : Reach 120467 := rs (se 1 (by rfl) ⟨90350, by rfl⟩) R180701
theorem R120497 : Reach 120497 := rs (se 2 (by rfl) ⟨45186, by rfl⟩) R90373
theorem R153265 : Reach 153265 := rs (se 2 (by rfl) ⟨57474, by rfl⟩) R114949
theorem R120515 : Reach 120515 := rs (se 1 (by rfl) ⟨90386, by rfl⟩) R180773
theorem R186065 : Reach 186065 := rs (se 2 (by rfl) ⟨69774, by rfl⟩) R139549
theorem R120545 : Reach 120545 := rs (se 2 (by rfl) ⟨45204, by rfl⟩) R90409
theorem R186083 : Reach 186083 := rs (se 1 (by rfl) ⟨139562, by rfl⟩) R279125
theorem R120563 : Reach 120563 := rs (se 1 (by rfl) ⟨90422, by rfl⟩) R180845
theorem R120593 : Reach 120593 := rs (se 2 (by rfl) ⟨45222, by rfl⟩) R90445
theorem R120611 : Reach 120611 := rs (se 1 (by rfl) ⟨90458, by rfl⟩) R180917
theorem R120641 : Reach 120641 := rs (se 2 (by rfl) ⟨45240, by rfl⟩) R90481
theorem R120659 : Reach 120659 := rs (se 1 (by rfl) ⟨90494, by rfl⟩) R180989
theorem R120689 : Reach 120689 := rs (se 2 (by rfl) ⟨45258, by rfl⟩) R90517
theorem R120707 : Reach 120707 := rs (se 1 (by rfl) ⟨90530, by rfl⟩) R181061
theorem R120737 : Reach 120737 := rs (se 2 (by rfl) ⟨45276, by rfl⟩) R90553
theorem R120755 : Reach 120755 := rs (se 1 (by rfl) ⟨90566, by rfl⟩) R181133
theorem R120785 : Reach 120785 := rs (se 2 (by rfl) ⟨45294, by rfl⟩) R90589
theorem R120803 : Reach 120803 := rs (se 1 (by rfl) ⟨90602, by rfl⟩) R181205
theorem R186353 : Reach 186353 := rs (se 2 (by rfl) ⟨69882, by rfl⟩) R139765
theorem R120833 : Reach 120833 := rs (se 2 (by rfl) ⟨45312, by rfl⟩) R90625
theorem R186371 : Reach 186371 := rs (se 1 (by rfl) ⟨139778, by rfl⟩) R279557
theorem R120851 : Reach 120851 := rs (se 1 (by rfl) ⟨90638, by rfl⟩) R181277
theorem R120881 : Reach 120881 := rs (se 2 (by rfl) ⟨45330, by rfl⟩) R90661
theorem R120899 : Reach 120899 := rs (se 1 (by rfl) ⟨90674, by rfl⟩) R181349
theorem R153667 : Reach 153667 := rs (se 1 (by rfl) ⟨115250, by rfl⟩) R230501
theorem R120929 : Reach 120929 := rs (se 2 (by rfl) ⟨45348, by rfl⟩) R90697
theorem R153713 : Reach 153713 := rs (se 2 (by rfl) ⟨57642, by rfl⟩) R115285
theorem R120947 : Reach 120947 := rs (se 1 (by rfl) ⟨90710, by rfl⟩) R181421
theorem R120977 : Reach 120977 := rs (se 2 (by rfl) ⟨45366, by rfl⟩) R90733
theorem R120995 : Reach 120995 := rs (se 1 (by rfl) ⟨90746, by rfl⟩) R181493
theorem R186545 : Reach 186545 := rs (se 2 (by rfl) ⟨69954, by rfl⟩) R139909
theorem R121025 : Reach 121025 := rs (se 2 (by rfl) ⟨45384, by rfl⟩) R90769
theorem R121043 : Reach 121043 := rs (se 1 (by rfl) ⟨90782, by rfl⟩) R181565
theorem R121073 : Reach 121073 := rs (se 2 (by rfl) ⟨45402, by rfl⟩) R90805
theorem R121091 : Reach 121091 := rs (se 1 (by rfl) ⟨90818, by rfl⟩) R181637
theorem R186641 : Reach 186641 := rs (se 2 (by rfl) ⟨69990, by rfl⟩) R139981
theorem R121121 : Reach 121121 := rs (se 2 (by rfl) ⟨45420, by rfl⟩) R90841
theorem R186659 : Reach 186659 := rs (se 1 (by rfl) ⟨139994, by rfl⟩) R279989
theorem R121139 : Reach 121139 := rs (se 1 (by rfl) ⟨90854, by rfl⟩) R181709
theorem R121169 : Reach 121169 := rs (se 2 (by rfl) ⟨45438, by rfl⟩) R90877
theorem R121187 : Reach 121187 := rs (se 1 (by rfl) ⟨90890, by rfl⟩) R181781
theorem R121217 : Reach 121217 := rs (se 2 (by rfl) ⟨45456, by rfl⟩) R90913
theorem R154001 : Reach 154001 := rs (se 2 (by rfl) ⟨57750, by rfl⟩) R115501
theorem R121235 : Reach 121235 := rs (se 1 (by rfl) ⟨90926, by rfl⟩) R181853
theorem R121265 : Reach 121265 := rs (se 2 (by rfl) ⟨45474, by rfl⟩) R90949
theorem R416177 : Reach 416177 := rs (se 2 (by rfl) ⟨156066, by rfl⟩) R312133
theorem R121283 : Reach 121283 := rs (se 1 (by rfl) ⟨90962, by rfl⟩) R181925
theorem R121313 : Reach 121313 := rs (se 2 (by rfl) ⟨45492, by rfl⟩) R90985
theorem R121331 : Reach 121331 := rs (se 1 (by rfl) ⟨90998, by rfl⟩) R181997
theorem R121361 : Reach 121361 := rs (se 2 (by rfl) ⟨45510, by rfl⟩) R91021
theorem R121379 : Reach 121379 := rs (se 1 (by rfl) ⟨91034, by rfl⟩) R182069
theorem R186929 : Reach 186929 := rs (se 2 (by rfl) ⟨70098, by rfl⟩) R140197
theorem R121409 : Reach 121409 := rs (se 2 (by rfl) ⟨45528, by rfl⟩) R91057
theorem R186947 : Reach 186947 := rs (se 1 (by rfl) ⟨140210, by rfl⟩) R280421
theorem R121427 : Reach 121427 := rs (se 1 (by rfl) ⟨91070, by rfl⟩) R182141
theorem R121457 : Reach 121457 := rs (se 2 (by rfl) ⟨45546, by rfl⟩) R91093
theorem R121475 : Reach 121475 := rs (se 1 (by rfl) ⟨91106, by rfl⟩) R182213
theorem R121505 : Reach 121505 := rs (se 2 (by rfl) ⟨45564, by rfl⟩) R91129
theorem R121523 : Reach 121523 := rs (se 1 (by rfl) ⟨91142, by rfl⟩) R182285
theorem R121553 : Reach 121553 := rs (se 2 (by rfl) ⟨45582, by rfl⟩) R91165
theorem R121571 : Reach 121571 := rs (se 1 (by rfl) ⟨91178, by rfl⟩) R182357
theorem R121601 : Reach 121601 := rs (se 2 (by rfl) ⟨45600, by rfl⟩) R91201
theorem R121619 : Reach 121619 := rs (se 1 (by rfl) ⟨91214, by rfl⟩) R182429
theorem R121649 : Reach 121649 := rs (se 2 (by rfl) ⟨45618, by rfl⟩) R91237
theorem R121667 : Reach 121667 := rs (se 1 (by rfl) ⟨91250, by rfl⟩) R182501
theorem R121697 : Reach 121697 := rs (se 2 (by rfl) ⟨45636, by rfl⟩) R91273
theorem R121715 : Reach 121715 := rs (se 1 (by rfl) ⟨91286, by rfl⟩) R182573
theorem R121745 : Reach 121745 := rs (se 2 (by rfl) ⟨45654, by rfl⟩) R91309
theorem R121763 : Reach 121763 := rs (se 1 (by rfl) ⟨91322, by rfl⟩) R182645
theorem R121793 : Reach 121793 := rs (se 2 (by rfl) ⟨45672, by rfl⟩) R91345
theorem R121811 : Reach 121811 := rs (se 1 (by rfl) ⟨91358, by rfl⟩) R182717
theorem R89059 : Reach 89059 := rs (se 1 (by rfl) ⟨66794, by rfl⟩) R133589
theorem R121841 : Reach 121841 := rs (se 2 (by rfl) ⟨45690, by rfl⟩) R91381
theorem R121859 : Reach 121859 := rs (se 1 (by rfl) ⟨91394, by rfl⟩) R182789
theorem R121889 : Reach 121889 := rs (se 2 (by rfl) ⟨45708, by rfl⟩) R91417
theorem R220205 : Reach 220205 := rs (se 3 (by rfl) ⟨41288, by rfl⟩) R82577
theorem R121907 : Reach 121907 := rs (se 1 (by rfl) ⟨91430, by rfl⟩) R182861
theorem R121937 : Reach 121937 := rs (se 2 (by rfl) ⟨45726, by rfl⟩) R91453
theorem R121955 : Reach 121955 := rs (se 1 (by rfl) ⟨91466, by rfl⟩) R182933
theorem R154723 : Reach 154723 := rs (se 1 (by rfl) ⟨116042, by rfl⟩) R232085
theorem R89203 : Reach 89203 := rs (se 1 (by rfl) ⟨66902, by rfl⟩) R133805
theorem R121985 : Reach 121985 := rs (se 2 (by rfl) ⟨45744, by rfl⟩) R91489
theorem R351373 : Reach 351373 := rs (se 3 (by rfl) ⟨65882, by rfl⟩) R131765
theorem R122003 : Reach 122003 := rs (se 1 (by rfl) ⟨91502, by rfl⟩) R183005
theorem R220333 : Reach 220333 := rs (se 3 (by rfl) ⟨41312, by rfl⟩) R82625
theorem R122033 : Reach 122033 := rs (se 2 (by rfl) ⟨45762, by rfl⟩) R91525
theorem R122051 : Reach 122051 := rs (se 1 (by rfl) ⟨91538, by rfl⟩) R183077
theorem R122081 : Reach 122081 := rs (se 2 (by rfl) ⟨45780, by rfl⟩) R91561
theorem R122099 : Reach 122099 := rs (se 1 (by rfl) ⟨91574, by rfl⟩) R183149
theorem R89347 : Reach 89347 := rs (se 1 (by rfl) ⟨67010, by rfl⟩) R134021
theorem R1072397 : Reach 1072397 := rs (se 3 (by rfl) ⟨201074, by rfl⟩) R402149
theorem R122129 : Reach 122129 := rs (se 2 (by rfl) ⟨45798, by rfl⟩) R91597
theorem R122147 : Reach 122147 := rs (se 1 (by rfl) ⟨91610, by rfl⟩) R183221
theorem R122177 : Reach 122177 := rs (se 2 (by rfl) ⟨45816, by rfl⟩) R91633
theorem R220483 : Reach 220483 := rs (se 1 (by rfl) ⟨165362, by rfl⟩) R330725
theorem R122195 : Reach 122195 := rs (se 1 (by rfl) ⟨91646, by rfl⟩) R183293
theorem R1039715 : Reach 1039715 := rs (se 1 (by rfl) ⟨779786, by rfl⟩) R1559573
theorem R122225 : Reach 122225 := rs (se 2 (by rfl) ⟨45834, by rfl⟩) R91669
theorem R122243 : Reach 122243 := rs (se 1 (by rfl) ⟨91682, by rfl⟩) R183365
theorem R89491 : Reach 89491 := rs (se 1 (by rfl) ⟨67118, by rfl⟩) R134237
theorem R122273 : Reach 122273 := rs (se 2 (by rfl) ⟨45852, by rfl⟩) R91705
theorem R122291 : Reach 122291 := rs (se 1 (by rfl) ⟨91718, by rfl⟩) R183437
theorem R122321 : Reach 122321 := rs (se 2 (by rfl) ⟨45870, by rfl⟩) R91741
theorem R122339 : Reach 122339 := rs (se 1 (by rfl) ⟨91754, by rfl⟩) R183509
theorem R286193 : Reach 286193 := rs (se 2 (by rfl) ⟨107322, by rfl⟩) R214645
theorem R122369 : Reach 122369 := rs (se 2 (by rfl) ⟨45888, by rfl⟩) R91777
theorem R122387 : Reach 122387 := rs (se 1 (by rfl) ⟨91790, by rfl⟩) R183581
theorem R155171 : Reach 155171 := rs (se 1 (by rfl) ⟨116378, by rfl⟩) R232757
theorem R89635 : Reach 89635 := rs (se 1 (by rfl) ⟨67226, by rfl⟩) R134453
theorem R122417 : Reach 122417 := rs (se 2 (by rfl) ⟨45906, by rfl⟩) R91813
theorem R122435 : Reach 122435 := rs (se 1 (by rfl) ⟨91826, by rfl⟩) R183653
theorem R122465 : Reach 122465 := rs (se 2 (by rfl) ⟨45924, by rfl⟩) R91849
theorem R122483 : Reach 122483 := rs (se 1 (by rfl) ⟨91862, by rfl⟩) R183725
theorem R122513 : Reach 122513 := rs (se 2 (by rfl) ⟨45942, by rfl⟩) R91885
theorem R122531 : Reach 122531 := rs (se 1 (by rfl) ⟨91898, by rfl⟩) R183797
theorem R89779 : Reach 89779 := rs (se 1 (by rfl) ⟨67334, by rfl⟩) R134669
theorem R122561 : Reach 122561 := rs (se 2 (by rfl) ⟨45960, by rfl⟩) R91921
theorem R122579 : Reach 122579 := rs (se 1 (by rfl) ⟨91934, by rfl⟩) R183869
theorem R351971 : Reach 351971 := rs (se 1 (by rfl) ⟨263978, by rfl⟩) R527957
theorem R122609 : Reach 122609 := rs (se 2 (by rfl) ⟨45978, by rfl⟩) R91957
theorem R122627 : Reach 122627 := rs (se 1 (by rfl) ⟨91970, by rfl⟩) R183941
theorem R122657 : Reach 122657 := rs (se 2 (by rfl) ⟨45996, by rfl⟩) R91993
theorem R122675 : Reach 122675 := rs (se 1 (by rfl) ⟨92006, by rfl⟩) R184013
theorem R89923 : Reach 89923 := rs (se 1 (by rfl) ⟨67442, by rfl⟩) R134885
theorem R155459 : Reach 155459 := rs (se 1 (by rfl) ⟨116594, by rfl⟩) R233189
theorem R122705 : Reach 122705 := rs (se 2 (by rfl) ⟨46014, by rfl⟩) R92029
theorem R122723 : Reach 122723 := rs (se 1 (by rfl) ⟨92042, by rfl⟩) R184085
theorem R417635 : Reach 417635 := rs (se 1 (by rfl) ⟨313226, by rfl⟩) R626453
theorem R122753 : Reach 122753 := rs (se 2 (by rfl) ⟨46032, by rfl⟩) R92065
theorem R548741 : Reach 548741 := rs (se 4 (by rfl) ⟨51444, by rfl⟩) R102889
theorem R122771 : Reach 122771 := rs (se 1 (by rfl) ⟨92078, by rfl⟩) R184157
theorem R122801 : Reach 122801 := rs (se 2 (by rfl) ⟨46050, by rfl⟩) R92101
theorem R122819 : Reach 122819 := rs (se 1 (by rfl) ⟨92114, by rfl⟩) R184229
theorem R90067 : Reach 90067 := rs (se 1 (by rfl) ⟨67550, by rfl⟩) R135101
theorem R122849 : Reach 122849 := rs (se 2 (by rfl) ⟨46068, by rfl⟩) R92137
theorem R122867 : Reach 122867 := rs (se 1 (by rfl) ⟨92150, by rfl⟩) R184301
theorem R122897 : Reach 122897 := rs (se 2 (by rfl) ⟨46086, by rfl⟩) R92173
theorem R122915 : Reach 122915 := rs (se 1 (by rfl) ⟨92186, by rfl⟩) R184373
theorem R122945 : Reach 122945 := rs (se 2 (by rfl) ⟨46104, by rfl⟩) R92209
theorem R122963 : Reach 122963 := rs (se 1 (by rfl) ⟨92222, by rfl⟩) R184445
theorem R90211 : Reach 90211 := rs (se 1 (by rfl) ⟨67658, by rfl⟩) R135317
theorem R122993 : Reach 122993 := rs (se 2 (by rfl) ⟨46122, by rfl⟩) R92245
theorem R123011 : Reach 123011 := rs (se 1 (by rfl) ⟨92258, by rfl⟩) R184517
theorem R123041 : Reach 123041 := rs (se 2 (by rfl) ⟨46140, by rfl⟩) R92281
theorem R123059 : Reach 123059 := rs (se 1 (by rfl) ⟨92294, by rfl⟩) R184589
theorem R221393 : Reach 221393 := rs (se 2 (by rfl) ⟨83022, by rfl⟩) R166045
theorem R123089 : Reach 123089 := rs (se 2 (by rfl) ⟨46158, by rfl⟩) R92317
theorem R123107 : Reach 123107 := rs (se 1 (by rfl) ⟨92330, by rfl⟩) R184661
theorem R778481 : Reach 778481 := rs (se 2 (by rfl) ⟨291930, by rfl⟩) R583861
theorem R90355 : Reach 90355 := rs (se 1 (by rfl) ⟨67766, by rfl⟩) R135533
theorem R123137 : Reach 123137 := rs (se 2 (by rfl) ⟨46176, by rfl⟩) R92353
theorem R123155 : Reach 123155 := rs (se 1 (by rfl) ⟨92366, by rfl⟩) R184733
theorem R123185 : Reach 123185 := rs (se 2 (by rfl) ⟨46194, by rfl⟩) R92389
theorem R123203 : Reach 123203 := rs (se 1 (by rfl) ⟨92402, by rfl⟩) R184805
theorem R385357 : Reach 385357 := rs (se 3 (by rfl) ⟨72254, by rfl⟩) R144509
theorem R123233 : Reach 123233 := rs (se 2 (by rfl) ⟨46212, by rfl⟩) R92425
theorem R123251 : Reach 123251 := rs (se 1 (by rfl) ⟨92438, by rfl⟩) R184877
theorem R90499 : Reach 90499 := rs (se 1 (by rfl) ⟨67874, by rfl⟩) R135749
theorem R123281 : Reach 123281 := rs (se 2 (by rfl) ⟨46230, by rfl⟩) R92461
theorem R123299 : Reach 123299 := rs (se 1 (by rfl) ⟨92474, by rfl⟩) R184949
theorem R123329 : Reach 123329 := rs (se 2 (by rfl) ⟨46248, by rfl⟩) R92497
theorem R1532357 : Reach 1532357 := rs (se 4 (by rfl) ⟨143658, by rfl⟩) R287317
theorem R123347 : Reach 123347 := rs (se 1 (by rfl) ⟨92510, by rfl⟩) R185021
theorem R123377 : Reach 123377 := rs (se 2 (by rfl) ⟨46266, by rfl⟩) R92533
theorem R123395 : Reach 123395 := rs (se 1 (by rfl) ⟨92546, by rfl⟩) R185093
theorem R90643 : Reach 90643 := rs (se 1 (by rfl) ⟨67982, by rfl⟩) R135965
theorem R123425 : Reach 123425 := rs (se 2 (by rfl) ⟨46284, by rfl⟩) R92569
theorem R123443 : Reach 123443 := rs (se 1 (by rfl) ⟨92582, by rfl⟩) R185165
theorem R123473 : Reach 123473 := rs (se 2 (by rfl) ⟨46302, by rfl⟩) R92605
theorem R156259 : Reach 156259 := rs (se 1 (by rfl) ⟨117194, by rfl⟩) R234389
theorem R123491 : Reach 123491 := rs (se 1 (by rfl) ⟨92618, by rfl⟩) R185237
theorem R254573 : Reach 254573 := rs (se 3 (by rfl) ⟨47732, by rfl⟩) R95465
theorem R123521 : Reach 123521 := rs (se 2 (by rfl) ⟨46320, by rfl⟩) R92641
theorem R418445 : Reach 418445 := rs (se 3 (by rfl) ⟨78458, by rfl⟩) R156917
theorem R123539 : Reach 123539 := rs (se 1 (by rfl) ⟨92654, by rfl⟩) R185309
theorem R90787 : Reach 90787 := rs (se 1 (by rfl) ⟨68090, by rfl⟩) R136181
theorem R123569 : Reach 123569 := rs (se 2 (by rfl) ⟨46338, by rfl⟩) R92677
theorem R123587 : Reach 123587 := rs (se 1 (by rfl) ⟨92690, by rfl⟩) R185381
theorem R123617 : Reach 123617 := rs (se 2 (by rfl) ⟨46356, by rfl⟩) R92713
theorem R156401 : Reach 156401 := rs (se 2 (by rfl) ⟨58650, by rfl⟩) R117301
theorem R123635 : Reach 123635 := rs (se 1 (by rfl) ⟨92726, by rfl⟩) R185453
theorem R123665 : Reach 123665 := rs (se 2 (by rfl) ⟨46374, by rfl⟩) R92749
theorem R123683 : Reach 123683 := rs (se 1 (by rfl) ⟨92762, by rfl⟩) R185525
theorem R90931 : Reach 90931 := rs (se 1 (by rfl) ⟨68198, by rfl⟩) R136397
theorem R123713 : Reach 123713 := rs (se 2 (by rfl) ⟨46392, by rfl⟩) R92785
theorem R123731 : Reach 123731 := rs (se 1 (by rfl) ⟨92798, by rfl⟩) R185597
theorem R123761 : Reach 123761 := rs (se 2 (by rfl) ⟨46410, by rfl⟩) R92821
theorem R123779 : Reach 123779 := rs (se 1 (by rfl) ⟨92834, by rfl⟩) R185669
theorem R123809 : Reach 123809 := rs (se 2 (by rfl) ⟨46428, by rfl⟩) R92857
theorem R123827 : Reach 123827 := rs (se 1 (by rfl) ⟨92870, by rfl⟩) R185741
theorem R91075 : Reach 91075 := rs (se 1 (by rfl) ⟨68306, by rfl⟩) R136613
theorem R3761093 : Reach 3761093 := rs (se 4 (by rfl) ⟨352602, by rfl⟩) R705205
theorem R123857 : Reach 123857 := rs (se 2 (by rfl) ⟨46446, by rfl⟩) R92893
theorem R123875 : Reach 123875 := rs (se 1 (by rfl) ⟨92906, by rfl⟩) R185813
theorem R123905 : Reach 123905 := rs (se 2 (by rfl) ⟨46464, by rfl⟩) R92929
theorem R123923 : Reach 123923 := rs (se 1 (by rfl) ⟨92942, by rfl⟩) R185885
theorem R123953 : Reach 123953 := rs (se 2 (by rfl) ⟨46482, by rfl⟩) R92965
theorem R123971 : Reach 123971 := rs (se 1 (by rfl) ⟨92978, by rfl⟩) R185957
theorem R91219 : Reach 91219 := rs (se 1 (by rfl) ⟨68414, by rfl⟩) R136829
theorem R124001 : Reach 124001 := rs (se 2 (by rfl) ⟨46500, by rfl⟩) R93001
theorem R124019 : Reach 124019 := rs (se 1 (by rfl) ⟨93014, by rfl⟩) R186029
theorem R124049 : Reach 124049 := rs (se 2 (by rfl) ⟨46518, by rfl⟩) R93037
theorem R124067 : Reach 124067 := rs (se 1 (by rfl) ⟨93050, by rfl⟩) R186101
theorem R124097 : Reach 124097 := rs (se 2 (by rfl) ⟨46536, by rfl⟩) R93073
theorem R1172677 : Reach 1172677 := rs (se 4 (by rfl) ⟨109938, by rfl⟩) R219877
theorem R124115 : Reach 124115 := rs (se 1 (by rfl) ⟨93086, by rfl⟩) R186173
theorem R91363 : Reach 91363 := rs (se 1 (by rfl) ⟨68522, by rfl⟩) R137045
theorem R124145 : Reach 124145 := rs (se 2 (by rfl) ⟨46554, by rfl⟩) R93109
theorem R124163 : Reach 124163 := rs (se 1 (by rfl) ⟨93122, by rfl⟩) R186245
theorem R124193 : Reach 124193 := rs (se 2 (by rfl) ⟨46572, by rfl⟩) R93145
theorem R451889 : Reach 451889 := rs (se 2 (by rfl) ⟨169458, by rfl⟩) R338917
theorem R124211 : Reach 124211 := rs (se 1 (by rfl) ⟨93158, by rfl⟩) R186317
theorem R124241 : Reach 124241 := rs (se 2 (by rfl) ⟨46590, by rfl⟩) R93181
theorem R124259 : Reach 124259 := rs (se 1 (by rfl) ⟨93194, by rfl⟩) R186389
theorem R91507 : Reach 91507 := rs (se 1 (by rfl) ⟨68630, by rfl⟩) R137261
theorem R124289 : Reach 124289 := rs (se 2 (by rfl) ⟨46608, by rfl⟩) R93217
theorem R124307 : Reach 124307 := rs (se 1 (by rfl) ⟨93230, by rfl⟩) R186461
theorem R124337 : Reach 124337 := rs (se 2 (by rfl) ⟨46626, by rfl⟩) R93253
theorem R124355 : Reach 124355 := rs (se 1 (by rfl) ⟨93266, by rfl⟩) R186533
theorem R124385 : Reach 124385 := rs (se 2 (by rfl) ⟨46644, by rfl⟩) R93289
theorem R255469 : Reach 255469 := rs (se 3 (by rfl) ⟨47900, by rfl⟩) R95801
theorem R124403 : Reach 124403 := rs (se 1 (by rfl) ⟨93302, by rfl⟩) R186605
theorem R91651 : Reach 91651 := rs (se 1 (by rfl) ⟨68738, by rfl⟩) R137477
theorem R288269 : Reach 288269 := rs (se 3 (by rfl) ⟨54050, by rfl⟩) R108101
theorem R124433 : Reach 124433 := rs (se 2 (by rfl) ⟨46662, by rfl⟩) R93325
theorem R124451 : Reach 124451 := rs (se 1 (by rfl) ⟨93338, by rfl⟩) R186677
theorem R124481 : Reach 124481 := rs (se 2 (by rfl) ⟨46680, by rfl⟩) R93361
theorem R124499 : Reach 124499 := rs (se 1 (by rfl) ⟨93374, by rfl⟩) R186749
theorem R157297 : Reach 157297 := rs (se 2 (by rfl) ⟨58986, by rfl⟩) R117973
theorem R124529 : Reach 124529 := rs (se 2 (by rfl) ⟨46698, by rfl⟩) R93397
theorem R124547 : Reach 124547 := rs (se 1 (by rfl) ⟨93410, by rfl⟩) R186821
theorem R91795 : Reach 91795 := rs (se 1 (by rfl) ⟨68846, by rfl⟩) R137693
theorem R124577 : Reach 124577 := rs (se 2 (by rfl) ⟨46716, by rfl⟩) R93433
theorem R124595 : Reach 124595 := rs (se 1 (by rfl) ⟨93446, by rfl⟩) R186893
theorem R124625 : Reach 124625 := rs (se 2 (by rfl) ⟨46734, by rfl⟩) R93469
theorem R124643 : Reach 124643 := rs (se 1 (by rfl) ⟨93482, by rfl⟩) R186965
theorem R124673 : Reach 124673 := rs (se 2 (by rfl) ⟨46752, by rfl⟩) R93505
theorem R157457 : Reach 157457 := rs (se 2 (by rfl) ⟨59046, by rfl⟩) R118093
theorem R124691 : Reach 124691 := rs (se 1 (by rfl) ⟨93518, by rfl⟩) R187037
theorem R91939 : Reach 91939 := rs (se 1 (by rfl) ⟨68954, by rfl⟩) R137909
theorem R91955 : Reach 91955 := rs (se 1 (by rfl) ⟨68966, by rfl⟩) R137933
theorem R681797 : Reach 681797 := rs (se 4 (by rfl) ⟨63918, by rfl⟩) R127837
theorem R92083 : Reach 92083 := rs (se 1 (by rfl) ⟨69062, by rfl⟩) R138125
theorem R92227 : Reach 92227 := rs (se 1 (by rfl) ⟨69170, by rfl⟩) R138341
theorem R714865 : Reach 714865 := rs (se 2 (by rfl) ⟨268074, by rfl⟩) R536149
theorem R157859 : Reach 157859 := rs (se 1 (by rfl) ⟨118394, by rfl⟩) R236789
theorem R92371 : Reach 92371 := rs (se 1 (by rfl) ⟨69278, by rfl⟩) R138557
theorem R92515 : Reach 92515 := rs (se 1 (by rfl) ⟨69386, by rfl⟩) R138773
theorem R92659 : Reach 92659 := rs (se 1 (by rfl) ⟨69494, by rfl⟩) R138989
theorem R256547 : Reach 256547 := rs (se 1 (by rfl) ⟨192410, by rfl⟩) R384821
theorem R158275 : Reach 158275 := rs (se 1 (by rfl) ⟨118706, by rfl⟩) R237413
theorem R92803 : Reach 92803 := rs (se 1 (by rfl) ⟨69602, by rfl⟩) R139205
theorem R780941 : Reach 780941 := rs (se 3 (by rfl) ⟨146426, by rfl⟩) R292853
theorem R453347 : Reach 453347 := rs (se 1 (by rfl) ⟨340010, by rfl⟩) R680021
theorem R92947 : Reach 92947 := rs (se 1 (by rfl) ⟨69710, by rfl⟩) R139421
theorem R93091 : Reach 93091 := rs (se 1 (by rfl) ⟨69818, by rfl⟩) R139637
theorem R519139 : Reach 519139 := rs (se 1 (by rfl) ⟨389354, by rfl⟩) R778709
theorem R93235 : Reach 93235 := rs (se 1 (by rfl) ⟨69926, by rfl⟩) R139853
theorem R126017 : Reach 126017 := rs (se 2 (by rfl) ⟨47256, by rfl⟩) R94513
theorem R257201 : Reach 257201 := rs (se 2 (by rfl) ⟨96450, by rfl⟩) R192901
theorem R93379 : Reach 93379 := rs (se 1 (by rfl) ⟨70034, by rfl⟩) R140069
theorem R1109189 : Reach 1109189 := rs (se 4 (by rfl) ⟨103986, by rfl⟩) R207973
theorem R126353 : Reach 126353 := rs (se 2 (by rfl) ⟨47382, by rfl⟩) R94765
theorem R290317 : Reach 290317 := rs (se 3 (by rfl) ⟨54434, by rfl⟩) R108869
theorem R454349 : Reach 454349 := rs (se 3 (by rfl) ⟨85190, by rfl⟩) R170381
theorem R126787 : Reach 126787 := rs (se 1 (by rfl) ⟨95090, by rfl⟩) R190181
theorem R487309 : Reach 487309 := rs (se 3 (by rfl) ⟨91370, by rfl⟩) R182741
theorem R520141 : Reach 520141 := rs (se 3 (by rfl) ⟨97526, by rfl⟩) R195053
theorem R192593 : Reach 192593 := rs (se 2 (by rfl) ⟨72222, by rfl⟩) R144445
theorem R225443 : Reach 225443 := rs (se 1 (by rfl) ⟨169082, by rfl⟩) R338165
theorem R127171 : Reach 127171 := rs (se 1 (by rfl) ⟨95378, by rfl⟩) R190757
theorem R127427 : Reach 127427 := rs (se 1 (by rfl) ⟨95570, by rfl⟩) R191141
theorem R258545 : Reach 258545 := rs (se 2 (by rfl) ⟨96954, by rfl⟩) R193909
theorem R127889 : Reach 127889 := rs (se 2 (by rfl) ⟨47958, by rfl⟩) R95917
theorem R226253 : Reach 226253 := rs (se 3 (by rfl) ⟨42422, by rfl⟩) R84845
theorem R127985 : Reach 127985 := rs (se 2 (by rfl) ⟨47994, by rfl⟩) R95989
theorem R128017 : Reach 128017 := rs (se 2 (by rfl) ⟨48006, by rfl⟩) R96013
theorem R226435 : Reach 226435 := rs (se 1 (by rfl) ⟨169826, by rfl⟩) R339653
theorem R128483 : Reach 128483 := rs (se 1 (by rfl) ⟨96362, by rfl⟩) R192725
theorem R259661 : Reach 259661 := rs (se 3 (by rfl) ⟨48686, by rfl⟩) R97373
theorem R226925 : Reach 226925 := rs (se 3 (by rfl) ⟨42548, by rfl⟩) R85097
theorem R325795 : Reach 325795 := rs (se 1 (by rfl) ⟨244346, by rfl⟩) R488693
theorem R653795 : Reach 653795 := rs (se 1 (by rfl) ⟨490346, by rfl⟩) R980693
theorem R457265 : Reach 457265 := rs (se 2 (by rfl) ⟨171474, by rfl⟩) R342949
theorem R195139 : Reach 195139 := rs (se 1 (by rfl) ⟨146354, by rfl⟩) R292709
theorem R260749 : Reach 260749 := rs (se 3 (by rfl) ⟨48890, by rfl⟩) R97781
theorem R129683 : Reach 129683 := rs (se 1 (by rfl) ⟨97262, by rfl⟩) R194525
theorem R228109 : Reach 228109 := rs (se 3 (by rfl) ⟨42770, by rfl⟩) R85541
theorem R97219 : Reach 97219 := rs (se 1 (by rfl) ⟨72914, by rfl⟩) R145829
theorem R130195 : Reach 130195 := rs (se 1 (by rfl) ⟨97646, by rfl⟩) R195293
theorem R130241 : Reach 130241 := rs (se 2 (by rfl) ⟨48840, by rfl⟩) R97681
theorem R196177 : Reach 196177 := rs (se 2 (by rfl) ⟨73566, by rfl⟩) R147133
theorem R654961 : Reach 654961 := rs (se 2 (by rfl) ⟨245610, by rfl⟩) R491221
theorem R229169 : Reach 229169 := rs (se 2 (by rfl) ⟨85938, by rfl⟩) R171877
theorem R130913 : Reach 130913 := rs (se 2 (by rfl) ⟨49092, by rfl⟩) R98185
theorem R458723 : Reach 458723 := rs (se 1 (by rfl) ⟨344042, by rfl⟩) R688085
theorem R197081 : Reach 197081 := rs (se 2 (by rfl) ⟨73905, by rfl⟩) R147811
theorem R99019 : Reach 99019 := rs (se 1 (by rfl) ⟨74264, by rfl⟩) R148529
theorem R1147765 : Reach 1147765 := rs (se 5 (by rfl) ⟨53801, by rfl⟩) R107603
theorem R590723 : Reach 590723 := rs (se 1 (by rfl) ⟨443042, by rfl⟩) R886085
theorem R295811 : Reach 295811 := rs (se 1 (by rfl) ⟨221858, by rfl⟩) R443717
theorem R623537 : Reach 623537 := rs (se 2 (by rfl) ⟨233826, by rfl⟩) R467653
theorem R99415 : Reach 99415 := rs (se 1 (by rfl) ⟨74561, by rfl⟩) R149123
theorem R624023 : Reach 624023 := rs (se 1 (by rfl) ⟨468017, by rfl⟩) R936035
theorem R99799 : Reach 99799 := rs (se 1 (by rfl) ⟨74849, by rfl⟩) R149699
theorem R1377809 : Reach 1377809 := rs (se 2 (by rfl) ⟨516678, by rfl⟩) R1033357
theorem R460363 : Reach 460363 := rs (se 1 (by rfl) ⟨345272, by rfl⟩) R690545
theorem R263773 : Reach 263773 := rs (se 3 (by rfl) ⟨49457, by rfl⟩) R98915
theorem R689795 : Reach 689795 := rs (se 1 (by rfl) ⟨517346, by rfl⟩) R1034693
theorem R460637 : Reach 460637 := rs (se 3 (by rfl) ⟨86369, by rfl⟩) R172739
theorem R100363 : Reach 100363 := rs (se 1 (by rfl) ⟨75272, by rfl⟩) R150545
theorem R3967127 : Reach 3967127 := rs (se 1 (by rfl) ⟨2975345, by rfl⟩) R5950691
theorem R231731 : Reach 231731 := rs (se 1 (by rfl) ⟨173798, by rfl⟩) R347597
theorem R3869045 : Reach 3869045 := rs (se 5 (by rfl) ⟨181361, by rfl⟩) R362723
theorem R100759 : Reach 100759 := rs (se 1 (by rfl) ⟨75569, by rfl⟩) R151139
theorem R1182131 : Reach 1182131 := rs (se 1 (by rfl) ⟨886598, by rfl⟩) R1773197
theorem R133643 : Reach 133643 := rs (se 1 (by rfl) ⟨100232, by rfl⟩) R200465
theorem R231959 : Reach 231959 := rs (se 1 (by rfl) ⟨173969, by rfl⟩) R347939
theorem R4983389 : Reach 4983389 := rs (se 3 (by rfl) ⟨934385, by rfl⟩) R1868771
theorem R133771 : Reach 133771 := rs (se 1 (by rfl) ⟨100328, by rfl⟩) R200657
theorem R887557 : Reach 887557 := rs (se 4 (by rfl) ⟨83208, by rfl⟩) R166417
theorem R133913 : Reach 133913 := rs (se 2 (by rfl) ⟨50217, by rfl⟩) R100435
theorem R953153 : Reach 953153 := rs (se 2 (by rfl) ⟨357432, by rfl⟩) R714865
theorem R232267 : Reach 232267 := rs (se 1 (by rfl) ⟨174200, by rfl⟩) R348401
theorem R199513 : Reach 199513 := rs (se 2 (by rfl) ⟨74817, by rfl⟩) R149635
theorem R134041 : Reach 134041 := rs (se 2 (by rfl) ⟨50265, by rfl⟩) R100531
theorem R396353 : Reach 396353 := rs (se 2 (by rfl) ⟨148632, by rfl⟩) R297265
theorem R232541 : Reach 232541 := rs (se 3 (by rfl) ⟨43601, by rfl⟩) R87203
theorem R134615 : Reach 134615 := rs (se 1 (by rfl) ⟨100961, by rfl⟩) R201923
theorem R134743 : Reach 134743 := rs (se 1 (by rfl) ⟨101057, by rfl⟩) R202115
theorem R200627 : Reach 200627 := rs (se 1 (by rfl) ⟨150470, by rfl⟩) R300941
theorem R692185 : Reach 692185 := rs (se 2 (by rfl) ⟨259569, by rfl⟩) R519139
theorem R102475 : Reach 102475 := rs (se 1 (by rfl) ⟨76856, by rfl⟩) R153713
theorem R135371 : Reach 135371 := rs (se 1 (by rfl) ⟨101528, by rfl⟩) R203057
theorem R135499 : Reach 135499 := rs (se 1 (by rfl) ⟨101624, by rfl⟩) R203249
theorem R201163 : Reach 201163 := rs (se 1 (by rfl) ⟨150872, by rfl⟩) R301745
theorem R135641 : Reach 135641 := rs (se 2 (by rfl) ⟨50865, by rfl⟩) R101731
theorem R201305 : Reach 201305 := rs (se 2 (by rfl) ⟨75489, by rfl⟩) R150979
theorem R135769 : Reach 135769 := rs (se 2 (by rfl) ⟨50913, by rfl⟩) R101827
theorem R267083 : Reach 267083 := rs (se 1 (by rfl) ⟨200312, by rfl⟩) R400625
theorem R693143 : Reach 693143 := rs (se 1 (by rfl) ⟨519857, by rfl⟩) R1039715
theorem R332747 : Reach 332747 := rs (se 1 (by rfl) ⟨249560, by rfl⟩) R499121
theorem R103447 : Reach 103447 := rs (se 1 (by rfl) ⟨77585, by rfl⟩) R155171
theorem R169049 : Reach 169049 := rs (se 2 (by rfl) ⟨63393, by rfl⟩) R126787
theorem R267353 : Reach 267353 := rs (se 2 (by rfl) ⟨100257, by rfl⟩) R200515
theorem R398429 : Reach 398429 := rs (se 3 (by rfl) ⟨74705, by rfl⟩) R149411
theorem R136343 : Reach 136343 := rs (se 1 (by rfl) ⟨102257, by rfl⟩) R204515
theorem R234647 : Reach 234647 := rs (se 1 (by rfl) ⟨175985, by rfl⟩) R351971
theorem R693521 : Reach 693521 := rs (se 2 (by rfl) ⟨260070, by rfl⟩) R520141
theorem R136471 : Reach 136471 := rs (se 1 (by rfl) ⟨102353, by rfl⟩) R204707
theorem R202135 : Reach 202135 := rs (se 1 (by rfl) ⟨151601, by rfl⟩) R303203
theorem R169561 : Reach 169561 := rs (se 2 (by rfl) ⟨63585, by rfl⟩) R127171
theorem R1021571 : Reach 1021571 := rs (se 1 (by rfl) ⟨766178, by rfl⟩) R1532357
theorem R169715 : Reach 169715 := rs (se 1 (by rfl) ⟨127286, by rfl⟩) R254573
theorem R268055 : Reach 268055 := rs (se 1 (by rfl) ⟨201041, by rfl⟩) R402083
theorem R202571 : Reach 202571 := rs (se 1 (by rfl) ⟨151928, by rfl⟩) R303857
theorem R104267 : Reach 104267 := rs (se 1 (by rfl) ⟨78200, by rfl⟩) R156401
theorem R137099 : Reach 137099 := rs (se 1 (by rfl) ⟨102824, by rfl⟩) R205649
theorem R235457 : Reach 235457 := rs (se 2 (by rfl) ⟨88296, by rfl⟩) R176593
theorem R333827 : Reach 333827 := rs (se 1 (by rfl) ⟨250370, by rfl⟩) R500741
theorem R137227 : Reach 137227 := rs (se 1 (by rfl) ⟨102920, by rfl⟩) R205841
theorem R5150789 : Reach 5150789 := rs (se 4 (by rfl) ⟨482886, by rfl⟩) R965773
theorem R137369 : Reach 137369 := rs (se 2 (by rfl) ⟨51513, by rfl⟩) R103027
theorem R301229 : Reach 301229 := rs (se 3 (by rfl) ⟨56480, by rfl⟩) R112961
theorem R202945 : Reach 202945 := rs (se 2 (by rfl) ⟨76104, by rfl⟩) R152209
theorem R301259 : Reach 301259 := rs (se 1 (by rfl) ⟨225944, by rfl⟩) R451889
theorem R661709 : Reach 661709 := rs (se 3 (by rfl) ⟨124070, by rfl⟩) R248141
theorem R137497 : Reach 137497 := rs (se 2 (by rfl) ⟨51561, by rfl⟩) R103123
theorem R268595 : Reach 268595 := rs (se 1 (by rfl) ⟨201446, by rfl⟩) R402893
theorem R268609 : Reach 268609 := rs (se 2 (by rfl) ⟨100728, by rfl⟩) R201457
theorem R104971 : Reach 104971 := rs (se 1 (by rfl) ⟨78728, by rfl⟩) R157457
theorem R268865 : Reach 268865 := rs (se 2 (by rfl) ⟨100824, by rfl⟩) R201649
theorem R367249 : Reach 367249 := rs (se 2 (by rfl) ⟨137718, by rfl⟩) R275437
theorem R170689 : Reach 170689 := rs (se 2 (by rfl) ⟨64008, by rfl⟩) R128017
theorem R203543 : Reach 203543 := rs (se 1 (by rfl) ⟨152657, by rfl⟩) R305315
theorem R105239 : Reach 105239 := rs (se 1 (by rfl) ⟨78929, by rfl⟩) R157859
theorem R138071 : Reach 138071 := rs (se 1 (by rfl) ⟨103553, by rfl⟩) R207107
theorem R301913 : Reach 301913 := rs (se 2 (by rfl) ⟨113217, by rfl⟩) R226435
theorem R138199 : Reach 138199 := rs (se 1 (by rfl) ⟨103649, by rfl⟩) R207299
theorem R171031 : Reach 171031 := rs (se 1 (by rfl) ⟨128273, by rfl⟩) R256547
theorem R466013 : Reach 466013 := rs (se 3 (by rfl) ⟨87377, by rfl⟩) R174755
theorem R269405 : Reach 269405 := rs (se 3 (by rfl) ⟨50513, by rfl⟩) R101027
theorem R302231 : Reach 302231 := rs (se 1 (by rfl) ⟨226673, by rfl⟩) R453347
theorem R367961 : Reach 367961 := rs (se 2 (by rfl) ⟨137985, by rfl⟩) R275971
theorem R171467 : Reach 171467 := rs (se 1 (by rfl) ⟨128600, by rfl⟩) R257201
theorem R204353 : Reach 204353 := rs (se 2 (by rfl) ⟨76632, by rfl⟩) R153265
theorem R138827 : Reach 138827 := rs (se 1 (by rfl) ⟨104120, by rfl⟩) R208241
theorem R138955 : Reach 138955 := rs (se 1 (by rfl) ⟨104216, by rfl⟩) R208433
theorem R106201 : Reach 106201 := rs (se 2 (by rfl) ⟨39825, by rfl⟩) R79651
theorem R302899 : Reach 302899 := rs (se 1 (by rfl) ⟨227174, by rfl⟩) R454349
theorem R139097 : Reach 139097 := rs (se 2 (by rfl) ⟨52161, by rfl⟩) R104323
theorem R139225 : Reach 139225 := rs (se 2 (by rfl) ⟨52209, by rfl⟩) R104419
theorem R204889 : Reach 204889 := rs (se 2 (by rfl) ⟨76833, by rfl⟩) R153667
theorem R270539 : Reach 270539 := rs (se 1 (by rfl) ⟨202904, by rfl⟩) R405809
theorem R434393 : Reach 434393 := rs (se 2 (by rfl) ⟨162897, by rfl⟩) R325795
theorem R172363 : Reach 172363 := rs (se 1 (by rfl) ⟨129272, by rfl⟩) R258545
theorem R270809 : Reach 270809 := rs (se 2 (by rfl) ⟨101553, by rfl⟩) R203107
theorem R139799 : Reach 139799 := rs (se 1 (by rfl) ⟨104849, by rfl⟩) R209699
theorem R139927 : Reach 139927 := rs (se 1 (by rfl) ⟨104945, by rfl⟩) R209891
theorem R2859725 : Reach 2859725 := rs (se 3 (by rfl) ⟨536198, by rfl⟩) R1072397
theorem R304145 : Reach 304145 := rs (se 2 (by rfl) ⟨114054, by rfl⟩) R228109
theorem R173107 : Reach 173107 := rs (se 1 (by rfl) ⟨129830, by rfl⟩) R259661
theorem R271511 : Reach 271511 := rs (se 1 (by rfl) ⟨203633, by rfl⟩) R407267
theorem R206003 : Reach 206003 := rs (se 1 (by rfl) ⟨154502, by rfl⟩) R309005
theorem R763181 : Reach 763181 := rs (se 3 (by rfl) ⟨143096, by rfl⟩) R286193
theorem R4793813 : Reach 4793813 := rs (se 7 (by rfl) ⟨56177, by rfl⟩) R112355
theorem R107993 : Reach 107993 := rs (se 2 (by rfl) ⟨40497, by rfl⟩) R80995
theorem R206297 : Reach 206297 := rs (se 2 (by rfl) ⟨77361, by rfl⟩) R154723
theorem R468497 : Reach 468497 := rs (se 2 (by rfl) ⟨175686, by rfl⟩) R351373
theorem R173593 : Reach 173593 := rs (se 2 (by rfl) ⟨65097, by rfl⟩) R130195
theorem R468611 : Reach 468611 := rs (se 1 (by rfl) ⟨351458, by rfl⟩) R702917
theorem R435863 : Reach 435863 := rs (se 1 (by rfl) ⟨326897, by rfl⟩) R653795
theorem R272051 : Reach 272051 := rs (se 1 (by rfl) ⟨204038, by rfl⟩) R408077
theorem R304843 : Reach 304843 := rs (se 1 (by rfl) ⟨228632, by rfl⟩) R457265
theorem R403217 : Reach 403217 := rs (se 2 (by rfl) ⟨151206, by rfl⟩) R302413
theorem R403379 : Reach 403379 := rs (se 1 (by rfl) ⟨302534, by rfl⟩) R605069
theorem R272321 : Reach 272321 := rs (se 2 (by rfl) ⟨102120, by rfl⟩) R204241
theorem R305117 : Reach 305117 := rs (se 3 (by rfl) ⟨57209, by rfl⟩) R114419
theorem R272605 : Reach 272605 := rs (se 3 (by rfl) ⟨51113, by rfl⟩) R102227
theorem R272861 : Reach 272861 := rs (se 3 (by rfl) ⟨51161, by rfl⟩) R102323
theorem R305815 : Reach 305815 := rs (se 1 (by rfl) ⟨229361, by rfl⟩) R458723
theorem R2010035 : Reach 2010035 := rs (se 1 (by rfl) ⟨1507526, by rfl⟩) R3015053
theorem R175063 : Reach 175063 := rs (se 1 (by rfl) ⟨131297, by rfl⟩) R262595
theorem R175115 : Reach 175115 := rs (se 1 (by rfl) ⟨131336, by rfl⟩) R262673
theorem R207947 : Reach 207947 := rs (se 1 (by rfl) ⟨155960, by rfl⟩) R311921
theorem R601181 : Reach 601181 := rs (se 3 (by rfl) ⟨112721, by rfl⟩) R225443
theorem R142679 : Reach 142679 := rs (se 1 (by rfl) ⟨107009, by rfl⟩) R214019
theorem R306605 : Reach 306605 := rs (se 3 (by rfl) ⟨57488, by rfl⟩) R114977
theorem R208345 : Reach 208345 := rs (se 2 (by rfl) ⟨78129, by rfl⟩) R156259
theorem R273995 : Reach 273995 := rs (se 1 (by rfl) ⟨205496, by rfl⟩) R410993
theorem R405323 : Reach 405323 := rs (se 1 (by rfl) ⟨303992, by rfl⟩) R607985
theorem R274265 : Reach 274265 := rs (se 2 (by rfl) ⟨102849, by rfl⟩) R205699
theorem R339805 : Reach 339805 := rs (se 3 (by rfl) ⟨63713, by rfl⟩) R127427
theorem R208919 : Reach 208919 := rs (se 1 (by rfl) ⟨156689, by rfl⟩) R313379
theorem R176257 : Reach 176257 := rs (se 2 (by rfl) ⟨66096, by rfl⟩) R132193
theorem R700933 : Reach 700933 := rs (se 4 (by rfl) ⟨65712, by rfl⟩) R131425
theorem R274967 : Reach 274967 := rs (se 1 (by rfl) ⟨206225, by rfl⟩) R412451
theorem R176755 : Reach 176755 := rs (se 1 (by rfl) ⟨132566, by rfl⟩) R265133
theorem R340625 : Reach 340625 := rs (se 2 (by rfl) ⟨127734, by rfl⟩) R255469
theorem R209587 : Reach 209587 := rs (se 1 (by rfl) ⟨157190, by rfl⟩) R314381
theorem R308033 : Reach 308033 := rs (se 2 (by rfl) ⟨115512, by rfl⟩) R231025
theorem R209729 : Reach 209729 := rs (se 2 (by rfl) ⟨78648, by rfl⟩) R157297
theorem R177113 : Reach 177113 := rs (se 2 (by rfl) ⟨66417, by rfl⟩) R132835
theorem R275507 : Reach 275507 := rs (se 1 (by rfl) ⟨206630, by rfl⟩) R413261
theorem R111755 : Reach 111755 := rs (se 1 (by rfl) ⟨83816, by rfl⟩) R167633
theorem R79127 : Reach 79127 := rs (se 1 (by rfl) ⟨59345, by rfl⟩) R118691
theorem R79147 : Reach 79147 := rs (se 1 (by rfl) ⟨59360, by rfl⟩) R118721
theorem R341293 : Reach 341293 := rs (se 3 (by rfl) ⟨63992, by rfl⟩) R127985
theorem R79159 : Reach 79159 := rs (se 1 (by rfl) ⟨59369, by rfl⟩) R118739
theorem R275777 : Reach 275777 := rs (se 2 (by rfl) ⟨103416, by rfl⟩) R206833
theorem R79179 : Reach 79179 := rs (se 1 (by rfl) ⟨59384, by rfl⟩) R118769
theorem R79191 : Reach 79191 := rs (se 1 (by rfl) ⟨59393, by rfl⟩) R118787
theorem R79211 : Reach 79211 := rs (se 1 (by rfl) ⟨59408, by rfl⟩) R118817
theorem R79223 : Reach 79223 := rs (se 1 (by rfl) ⟨59417, by rfl⟩) R118835
theorem R79243 : Reach 79243 := rs (se 1 (by rfl) ⟨59432, by rfl⟩) R118865
theorem R79255 : Reach 79255 := rs (se 1 (by rfl) ⟨59441, by rfl⟩) R118883
theorem R79275 : Reach 79275 := rs (se 1 (by rfl) ⟨59456, by rfl⟩) R118913
theorem R1291697 : Reach 1291697 := rs (se 2 (by rfl) ⟨484386, by rfl⟩) R968773
theorem R79287 : Reach 79287 := rs (se 1 (by rfl) ⟨59465, by rfl⟩) R118931
theorem R79307 : Reach 79307 := rs (se 1 (by rfl) ⟨59480, by rfl⟩) R118961
theorem R79319 : Reach 79319 := rs (se 1 (by rfl) ⟨59489, by rfl⟩) R118979
theorem R79339 : Reach 79339 := rs (se 1 (by rfl) ⟨59504, by rfl⟩) R119009
theorem R79351 : Reach 79351 := rs (se 1 (by rfl) ⟨59513, by rfl⟩) R119027
theorem R79371 : Reach 79371 := rs (se 1 (by rfl) ⟨59528, by rfl⟩) R119057
theorem R79383 : Reach 79383 := rs (se 1 (by rfl) ⟨59537, by rfl⟩) R119075
theorem R79403 : Reach 79403 := rs (se 1 (by rfl) ⟨59552, by rfl⟩) R119105
theorem R79415 : Reach 79415 := rs (se 1 (by rfl) ⟨59561, by rfl⟩) R119123
theorem R407105 : Reach 407105 := rs (se 2 (by rfl) ⟨152664, by rfl⟩) R305329
theorem R79435 : Reach 79435 := rs (se 1 (by rfl) ⟨59576, by rfl⟩) R119153
theorem R79447 : Reach 79447 := rs (se 1 (by rfl) ⟨59585, by rfl⟩) R119171
theorem R79467 : Reach 79467 := rs (se 1 (by rfl) ⟨59600, by rfl⟩) R119201
theorem R79479 : Reach 79479 := rs (se 1 (by rfl) ⟨59609, by rfl⟩) R119219
theorem R79499 : Reach 79499 := rs (se 1 (by rfl) ⟨59624, by rfl⟩) R119249
theorem R79511 : Reach 79511 := rs (se 1 (by rfl) ⟨59633, by rfl⟩) R119267
theorem R79531 : Reach 79531 := rs (se 1 (by rfl) ⟨59648, by rfl⟩) R119297
theorem R79543 : Reach 79543 := rs (se 1 (by rfl) ⟨59657, by rfl⟩) R119315
theorem R79563 : Reach 79563 := rs (se 1 (by rfl) ⟨59672, by rfl⟩) R119345
theorem R79575 : Reach 79575 := rs (se 1 (by rfl) ⟨59681, by rfl⟩) R119363
theorem R79595 : Reach 79595 := rs (se 1 (by rfl) ⟨59696, by rfl⟩) R119393
theorem R79607 : Reach 79607 := rs (se 1 (by rfl) ⟨59705, by rfl⟩) R119411
theorem R79627 : Reach 79627 := rs (se 1 (by rfl) ⟨59720, by rfl⟩) R119441
theorem R79639 : Reach 79639 := rs (se 1 (by rfl) ⟨59729, by rfl⟩) R119459
theorem R79659 : Reach 79659 := rs (se 1 (by rfl) ⟨59744, by rfl⟩) R119489
theorem R79671 : Reach 79671 := rs (se 1 (by rfl) ⟨59753, by rfl⟩) R119507
theorem R79691 : Reach 79691 := rs (se 1 (by rfl) ⟨59768, by rfl⟩) R119537
theorem R79703 : Reach 79703 := rs (se 1 (by rfl) ⟨59777, by rfl⟩) R119555
theorem R276317 : Reach 276317 := rs (se 3 (by rfl) ⟨51809, by rfl⟩) R103619
theorem R79723 : Reach 79723 := rs (se 1 (by rfl) ⟨59792, by rfl⟩) R119585
theorem R79735 : Reach 79735 := rs (se 1 (by rfl) ⟨59801, by rfl⟩) R119603
theorem R341891 : Reach 341891 := rs (se 1 (by rfl) ⟨256418, by rfl⟩) R512837
theorem R79755 : Reach 79755 := rs (se 1 (by rfl) ⟨59816, by rfl⟩) R119633
theorem R79767 : Reach 79767 := rs (se 1 (by rfl) ⟨59825, by rfl⟩) R119651
theorem R178073 : Reach 178073 := rs (se 2 (by rfl) ⟨66777, by rfl⟩) R133555
theorem R79787 : Reach 79787 := rs (se 1 (by rfl) ⟨59840, by rfl⟩) R119681
theorem R79799 : Reach 79799 := rs (se 1 (by rfl) ⟨59849, by rfl⟩) R119699
theorem R79819 : Reach 79819 := rs (se 1 (by rfl) ⟨59864, by rfl⟩) R119729
theorem R79831 : Reach 79831 := rs (se 1 (by rfl) ⟨59873, by rfl⟩) R119747
theorem R79851 : Reach 79851 := rs (se 1 (by rfl) ⟨59888, by rfl⟩) R119777
theorem R178163 : Reach 178163 := rs (se 1 (by rfl) ⟨133622, by rfl⟩) R267245
theorem R79863 : Reach 79863 := rs (se 1 (by rfl) ⟨59897, by rfl⟩) R119795
theorem R79883 : Reach 79883 := rs (se 1 (by rfl) ⟨59912, by rfl⟩) R119825
theorem R178199 : Reach 178199 := rs (se 1 (by rfl) ⟨133649, by rfl⟩) R267299
theorem R79895 : Reach 79895 := rs (se 1 (by rfl) ⟨59921, by rfl⟩) R119843
theorem R79915 : Reach 79915 := rs (se 1 (by rfl) ⟨59936, by rfl⟩) R119873
theorem R79927 : Reach 79927 := rs (se 1 (by rfl) ⟨59945, by rfl⟩) R119891
theorem R79947 : Reach 79947 := rs (se 1 (by rfl) ⟨59960, by rfl⟩) R119921
theorem R79959 : Reach 79959 := rs (se 1 (by rfl) ⟨59969, by rfl⟩) R119939
theorem R211033 : Reach 211033 := rs (se 2 (by rfl) ⟨79137, by rfl⟩) R158275
theorem R79979 : Reach 79979 := rs (se 1 (by rfl) ⟨59984, by rfl⟩) R119969
theorem R79991 : Reach 79991 := rs (se 1 (by rfl) ⟨59993, by rfl⟩) R119987
theorem R80011 : Reach 80011 := rs (se 1 (by rfl) ⟨60008, by rfl⟩) R120017
theorem R80023 : Reach 80023 := rs (se 1 (by rfl) ⟨60017, by rfl⟩) R120035
theorem R80043 : Reach 80043 := rs (se 1 (by rfl) ⟨60032, by rfl⟩) R120065
theorem R80055 : Reach 80055 := rs (se 1 (by rfl) ⟨60041, by rfl⟩) R120083
theorem R178379 : Reach 178379 := rs (se 1 (by rfl) ⟨133784, by rfl⟩) R267569
theorem R80075 : Reach 80075 := rs (se 1 (by rfl) ⟨60056, by rfl⟩) R120113
theorem R80087 : Reach 80087 := rs (se 1 (by rfl) ⟨60065, by rfl⟩) R120131
theorem R80107 : Reach 80107 := rs (se 1 (by rfl) ⟨60080, by rfl⟩) R120161
theorem R80119 : Reach 80119 := rs (se 1 (by rfl) ⟨60089, by rfl⟩) R120179
theorem R178433 : Reach 178433 := rs (se 2 (by rfl) ⟨66912, by rfl⟩) R133825
theorem R80139 : Reach 80139 := rs (se 1 (by rfl) ⟨60104, by rfl⟩) R120209
theorem R309521 : Reach 309521 := rs (se 2 (by rfl) ⟨116070, by rfl⟩) R232141
theorem R80151 : Reach 80151 := rs (se 1 (by rfl) ⟨60113, by rfl⟩) R120227
theorem R80171 : Reach 80171 := rs (se 1 (by rfl) ⟨60128, by rfl⟩) R120257
theorem R80183 : Reach 80183 := rs (se 1 (by rfl) ⟨60137, by rfl⟩) R120275
theorem R80203 : Reach 80203 := rs (se 1 (by rfl) ⟨60152, by rfl⟩) R120305
theorem R80215 : Reach 80215 := rs (se 1 (by rfl) ⟨60161, by rfl⟩) R120323
theorem R80235 : Reach 80235 := rs (se 1 (by rfl) ⟨60176, by rfl⟩) R120353
theorem R80247 : Reach 80247 := rs (se 1 (by rfl) ⟨60185, by rfl⟩) R120371
theorem R80267 : Reach 80267 := rs (se 1 (by rfl) ⟨60200, by rfl⟩) R120401
theorem R80279 : Reach 80279 := rs (se 1 (by rfl) ⟨60209, by rfl⟩) R120419
theorem R80299 : Reach 80299 := rs (se 1 (by rfl) ⟨60224, by rfl⟩) R120449
theorem R80311 : Reach 80311 := rs (se 1 (by rfl) ⟨60233, by rfl⟩) R120467
theorem R80331 : Reach 80331 := rs (se 1 (by rfl) ⟨60248, by rfl⟩) R120497
theorem R80343 : Reach 80343 := rs (se 1 (by rfl) ⟨60257, by rfl⟩) R120515
theorem R178649 : Reach 178649 := rs (se 2 (by rfl) ⟨66993, by rfl⟩) R133987
theorem R80363 : Reach 80363 := rs (se 1 (by rfl) ⟨60272, by rfl⟩) R120545
theorem R80375 : Reach 80375 := rs (se 1 (by rfl) ⟨60281, by rfl⟩) R120563
theorem R80395 : Reach 80395 := rs (se 1 (by rfl) ⟨60296, by rfl⟩) R120593
theorem R80407 : Reach 80407 := rs (se 1 (by rfl) ⟨60305, by rfl⟩) R120611
theorem R80427 : Reach 80427 := rs (se 1 (by rfl) ⟨60320, by rfl⟩) R120641
theorem R178739 : Reach 178739 := rs (se 1 (by rfl) ⟨134054, by rfl⟩) R268109
theorem R80439 : Reach 80439 := rs (se 1 (by rfl) ⟨60329, by rfl⟩) R120659
theorem R80459 : Reach 80459 := rs (se 1 (by rfl) ⟨60344, by rfl⟩) R120689
theorem R178775 : Reach 178775 := rs (se 1 (by rfl) ⟨134081, by rfl⟩) R268163
theorem R80471 : Reach 80471 := rs (se 1 (by rfl) ⟨60353, by rfl⟩) R120707
theorem R80491 : Reach 80491 := rs (se 1 (by rfl) ⟨60368, by rfl⟩) R120737
theorem R80503 : Reach 80503 := rs (se 1 (by rfl) ⟨60377, by rfl⟩) R120755
theorem R80523 : Reach 80523 := rs (se 1 (by rfl) ⟨60392, by rfl⟩) R120785
theorem R80535 : Reach 80535 := rs (se 1 (by rfl) ⟨60401, by rfl⟩) R120803
theorem R80555 : Reach 80555 := rs (se 1 (by rfl) ⟨60416, by rfl⟩) R120833
theorem R80567 : Reach 80567 := rs (se 1 (by rfl) ⟨60425, by rfl⟩) R120851
theorem R80587 : Reach 80587 := rs (se 1 (by rfl) ⟨60440, by rfl⟩) R120881
theorem R80599 : Reach 80599 := rs (se 1 (by rfl) ⟨60449, by rfl⟩) R120899
theorem R309977 : Reach 309977 := rs (se 2 (by rfl) ⟨116241, by rfl⟩) R232483
theorem R80619 : Reach 80619 := rs (se 1 (by rfl) ⟨60464, by rfl⟩) R120929
theorem R80631 : Reach 80631 := rs (se 1 (by rfl) ⟨60473, by rfl⟩) R120947
theorem R178955 : Reach 178955 := rs (se 1 (by rfl) ⟨134216, by rfl⟩) R268433
theorem R80651 : Reach 80651 := rs (se 1 (by rfl) ⟨60488, by rfl⟩) R120977
theorem R80663 : Reach 80663 := rs (se 1 (by rfl) ⟨60497, by rfl⟩) R120995
theorem R80683 : Reach 80683 := rs (se 1 (by rfl) ⟨60512, by rfl⟩) R121025
theorem R80695 : Reach 80695 := rs (se 1 (by rfl) ⟨60521, by rfl⟩) R121043
theorem R179009 : Reach 179009 := rs (se 2 (by rfl) ⟨67128, by rfl⟩) R134257
theorem R80715 : Reach 80715 := rs (se 1 (by rfl) ⟨60536, by rfl⟩) R121073
theorem R80727 : Reach 80727 := rs (se 1 (by rfl) ⟨60545, by rfl⟩) R121091
theorem R80747 : Reach 80747 := rs (se 1 (by rfl) ⟨60560, by rfl⟩) R121121
theorem R80759 : Reach 80759 := rs (se 1 (by rfl) ⟨60569, by rfl⟩) R121139
theorem R80779 : Reach 80779 := rs (se 1 (by rfl) ⟨60584, by rfl⟩) R121169
theorem R80791 : Reach 80791 := rs (se 1 (by rfl) ⟨60593, by rfl⟩) R121187
theorem R80811 : Reach 80811 := rs (se 1 (by rfl) ⟨60608, by rfl⟩) R121217
theorem R310189 : Reach 310189 := rs (se 3 (by rfl) ⟨58160, by rfl⟩) R116321
theorem R80823 : Reach 80823 := rs (se 1 (by rfl) ⟨60617, by rfl⟩) R121235
theorem R80843 : Reach 80843 := rs (se 1 (by rfl) ⟨60632, by rfl⟩) R121265
theorem R277451 : Reach 277451 := rs (se 1 (by rfl) ⟨208088, by rfl⟩) R416177
theorem R80855 : Reach 80855 := rs (se 1 (by rfl) ⟨60641, by rfl⟩) R121283
theorem R80875 : Reach 80875 := rs (se 1 (by rfl) ⟨60656, by rfl⟩) R121313
theorem R80887 : Reach 80887 := rs (se 1 (by rfl) ⟨60665, by rfl⟩) R121331
theorem R80907 : Reach 80907 := rs (se 1 (by rfl) ⟨60680, by rfl⟩) R121361
theorem R80919 : Reach 80919 := rs (se 1 (by rfl) ⟨60689, by rfl⟩) R121379
theorem R179225 : Reach 179225 := rs (se 2 (by rfl) ⟨67209, by rfl⟩) R134419
theorem R80939 : Reach 80939 := rs (se 1 (by rfl) ⟨60704, by rfl⟩) R121409
theorem R80951 : Reach 80951 := rs (se 1 (by rfl) ⟨60713, by rfl⟩) R121427
theorem R80971 : Reach 80971 := rs (se 1 (by rfl) ⟨60728, by rfl⟩) R121457
theorem R80983 : Reach 80983 := rs (se 1 (by rfl) ⟨60737, by rfl⟩) R121475
theorem R81003 : Reach 81003 := rs (se 1 (by rfl) ⟨60752, by rfl⟩) R121505
theorem R179315 : Reach 179315 := rs (se 1 (by rfl) ⟨134486, by rfl⟩) R268973
theorem R81015 : Reach 81015 := rs (se 1 (by rfl) ⟨60761, by rfl⟩) R121523
theorem R81035 : Reach 81035 := rs (se 1 (by rfl) ⟨60776, by rfl⟩) R121553
theorem R179351 : Reach 179351 := rs (se 1 (by rfl) ⟨134513, by rfl⟩) R269027
theorem R113815 : Reach 113815 := rs (se 1 (by rfl) ⟨85361, by rfl⟩) R170723
theorem R81047 : Reach 81047 := rs (se 1 (by rfl) ⟨60785, by rfl⟩) R121571
theorem R81067 : Reach 81067 := rs (se 1 (by rfl) ⟨60800, by rfl⟩) R121601
theorem R703667 : Reach 703667 := rs (se 1 (by rfl) ⟨527750, by rfl⟩) R1055501
theorem R81079 : Reach 81079 := rs (se 1 (by rfl) ⟨60809, by rfl⟩) R121619
theorem R81099 : Reach 81099 := rs (se 1 (by rfl) ⟨60824, by rfl⟩) R121649
theorem R81111 : Reach 81111 := rs (se 1 (by rfl) ⟨60833, by rfl⟩) R121667
theorem R277721 : Reach 277721 := rs (se 2 (by rfl) ⟨104145, by rfl⟩) R208291
theorem R310493 : Reach 310493 := rs (se 3 (by rfl) ⟨58217, by rfl⟩) R116435
theorem R81131 : Reach 81131 := rs (se 1 (by rfl) ⟨60848, by rfl⟩) R121697
theorem R81143 : Reach 81143 := rs (se 1 (by rfl) ⟨60857, by rfl⟩) R121715
theorem R81163 : Reach 81163 := rs (se 1 (by rfl) ⟨60872, by rfl⟩) R121745
theorem R81175 : Reach 81175 := rs (se 1 (by rfl) ⟨60881, by rfl⟩) R121763
theorem R81195 : Reach 81195 := rs (se 1 (by rfl) ⟨60896, by rfl⟩) R121793
theorem R81207 : Reach 81207 := rs (se 1 (by rfl) ⟨60905, by rfl⟩) R121811
theorem R179531 : Reach 179531 := rs (se 1 (by rfl) ⟨134648, by rfl⟩) R269297
theorem R81227 : Reach 81227 := rs (se 1 (by rfl) ⟨60920, by rfl⟩) R121841
theorem R81239 : Reach 81239 := rs (se 1 (by rfl) ⟨60929, by rfl⟩) R121859
theorem R81259 : Reach 81259 := rs (se 1 (by rfl) ⟨60944, by rfl⟩) R121889
theorem R81271 : Reach 81271 := rs (se 1 (by rfl) ⟨60953, by rfl⟩) R121907
theorem R179585 : Reach 179585 := rs (se 2 (by rfl) ⟨67344, by rfl⟩) R134689
theorem R81291 : Reach 81291 := rs (se 1 (by rfl) ⟨60968, by rfl⟩) R121937
theorem R81303 : Reach 81303 := rs (se 1 (by rfl) ⟨60977, by rfl⟩) R121955
theorem R81323 : Reach 81323 := rs (se 1 (by rfl) ⟨60992, by rfl⟩) R121985
theorem R81335 : Reach 81335 := rs (se 1 (by rfl) ⟨61001, by rfl⟩) R122003
theorem R81355 : Reach 81355 := rs (se 1 (by rfl) ⟨61016, by rfl⟩) R122033
theorem R81367 : Reach 81367 := rs (se 1 (by rfl) ⟨61025, by rfl⟩) R122051
theorem R409049 : Reach 409049 := rs (se 2 (by rfl) ⟨153393, by rfl⟩) R306787
theorem R245213 : Reach 245213 := rs (se 3 (by rfl) ⟨45977, by rfl⟩) R91955
theorem R81387 : Reach 81387 := rs (se 1 (by rfl) ⟨61040, by rfl⟩) R122081
theorem R81399 : Reach 81399 := rs (se 1 (by rfl) ⟨61049, by rfl⟩) R122099
theorem R81419 : Reach 81419 := rs (se 1 (by rfl) ⟨61064, by rfl⟩) R122129
theorem R81431 : Reach 81431 := rs (se 1 (by rfl) ⟨61073, by rfl⟩) R122147
theorem R81451 : Reach 81451 := rs (se 1 (by rfl) ⟨61088, by rfl⟩) R122177
theorem R81463 : Reach 81463 := rs (se 1 (by rfl) ⟨61097, by rfl⟩) R122195
theorem R81483 : Reach 81483 := rs (se 1 (by rfl) ⟨61112, by rfl⟩) R122225
theorem R81495 : Reach 81495 := rs (se 1 (by rfl) ⟨61121, by rfl⟩) R122243
theorem R179801 : Reach 179801 := rs (se 2 (by rfl) ⟨67425, by rfl⟩) R134851
theorem R81515 : Reach 81515 := rs (se 1 (by rfl) ⟨61136, by rfl⟩) R122273
theorem R81527 : Reach 81527 := rs (se 1 (by rfl) ⟨61145, by rfl⟩) R122291
theorem R81547 : Reach 81547 := rs (se 1 (by rfl) ⟨61160, by rfl⟩) R122321
theorem R81559 : Reach 81559 := rs (se 1 (by rfl) ⟨61169, by rfl⟩) R122339
theorem R81579 : Reach 81579 := rs (se 1 (by rfl) ⟨61184, by rfl⟩) R122369
theorem R179891 : Reach 179891 := rs (se 1 (by rfl) ⟨134918, by rfl⟩) R269837
theorem R81591 : Reach 81591 := rs (se 1 (by rfl) ⟨61193, by rfl⟩) R122387
theorem R81611 : Reach 81611 := rs (se 1 (by rfl) ⟨61208, by rfl⟩) R122417
theorem R179927 : Reach 179927 := rs (se 1 (by rfl) ⟨134945, by rfl⟩) R269891
theorem R81623 : Reach 81623 := rs (se 1 (by rfl) ⟨61217, by rfl⟩) R122435
theorem R81643 : Reach 81643 := rs (se 1 (by rfl) ⟨61232, by rfl⟩) R122465
theorem R81655 : Reach 81655 := rs (se 1 (by rfl) ⟨61241, by rfl⟩) R122483
theorem R81675 : Reach 81675 := rs (se 1 (by rfl) ⟨61256, by rfl⟩) R122513
theorem R81687 : Reach 81687 := rs (se 1 (by rfl) ⟨61265, by rfl⟩) R122531
theorem R81707 : Reach 81707 := rs (se 1 (by rfl) ⟨61280, by rfl⟩) R122561
theorem R81719 : Reach 81719 := rs (se 1 (by rfl) ⟨61289, by rfl⟩) R122579
theorem R81739 : Reach 81739 := rs (se 1 (by rfl) ⟨61304, by rfl⟩) R122609
theorem R81751 : Reach 81751 := rs (se 1 (by rfl) ⟨61313, by rfl⟩) R122627
theorem R81771 : Reach 81771 := rs (se 1 (by rfl) ⟨61328, by rfl⟩) R122657
theorem R81783 : Reach 81783 := rs (se 1 (by rfl) ⟨61337, by rfl⟩) R122675
theorem R147329 : Reach 147329 := rs (se 2 (by rfl) ⟨55248, by rfl⟩) R110497
theorem R180107 : Reach 180107 := rs (se 1 (by rfl) ⟨135080, by rfl⟩) R270161
theorem R81803 : Reach 81803 := rs (se 1 (by rfl) ⟨61352, by rfl⟩) R122705
theorem R81815 : Reach 81815 := rs (se 1 (by rfl) ⟨61361, by rfl⟩) R122723
theorem R278423 : Reach 278423 := rs (se 1 (by rfl) ⟨208817, by rfl⟩) R417635
theorem R81835 : Reach 81835 := rs (se 1 (by rfl) ⟨61376, by rfl⟩) R122753
theorem R81847 : Reach 81847 := rs (se 1 (by rfl) ⟨61385, by rfl⟩) R122771
theorem R180161 : Reach 180161 := rs (se 2 (by rfl) ⟨67560, by rfl⟩) R135121
theorem R81867 : Reach 81867 := rs (se 1 (by rfl) ⟨61400, by rfl⟩) R122801
theorem R81879 : Reach 81879 := rs (se 1 (by rfl) ⟨61409, by rfl⟩) R122819
theorem R81899 : Reach 81899 := rs (se 1 (by rfl) ⟨61424, by rfl⟩) R122849
theorem R81911 : Reach 81911 := rs (se 1 (by rfl) ⟨61433, by rfl⟩) R122867
theorem R81931 : Reach 81931 := rs (se 1 (by rfl) ⟨61448, by rfl⟩) R122897
theorem R81943 : Reach 81943 := rs (se 1 (by rfl) ⟨61457, by rfl⟩) R122915
theorem R81963 : Reach 81963 := rs (se 1 (by rfl) ⟨61472, by rfl⟩) R122945
theorem R81975 : Reach 81975 := rs (se 1 (by rfl) ⟨61481, by rfl⟩) R122963
theorem R81995 : Reach 81995 := rs (se 1 (by rfl) ⟨61496, by rfl⟩) R122993
theorem R82007 : Reach 82007 := rs (se 1 (by rfl) ⟨61505, by rfl⟩) R123011
theorem R82027 : Reach 82027 := rs (se 1 (by rfl) ⟨61520, by rfl⟩) R123041
theorem R82039 : Reach 82039 := rs (se 1 (by rfl) ⟨61529, by rfl⟩) R123059
theorem R147595 : Reach 147595 := rs (se 1 (by rfl) ⟨110696, by rfl⟩) R221393
theorem R82059 : Reach 82059 := rs (se 1 (by rfl) ⟨61544, by rfl⟩) R123089
theorem R82071 : Reach 82071 := rs (se 1 (by rfl) ⟨61553, by rfl⟩) R123107
theorem R180377 : Reach 180377 := rs (se 2 (by rfl) ⟨67641, by rfl⟩) R135283
theorem R82091 : Reach 82091 := rs (se 1 (by rfl) ⟨61568, by rfl⟩) R123137
theorem R82103 : Reach 82103 := rs (se 1 (by rfl) ⟨61577, by rfl⟩) R123155
theorem R82123 : Reach 82123 := rs (se 1 (by rfl) ⟨61592, by rfl⟩) R123185
theorem R82135 : Reach 82135 := rs (se 1 (by rfl) ⟨61601, by rfl⟩) R123203
theorem R82155 : Reach 82155 := rs (se 1 (by rfl) ⟨61616, by rfl⟩) R123233
theorem R180467 : Reach 180467 := rs (se 1 (by rfl) ⟨135350, by rfl⟩) R270701
theorem R82167 : Reach 82167 := rs (se 1 (by rfl) ⟨61625, by rfl⟩) R123251
theorem R82187 : Reach 82187 := rs (se 1 (by rfl) ⟨61640, by rfl⟩) R123281
theorem R573713 : Reach 573713 := rs (se 2 (by rfl) ⟨215142, by rfl⟩) R430285
theorem R180503 : Reach 180503 := rs (se 1 (by rfl) ⟨135377, by rfl⟩) R270755
theorem R82199 : Reach 82199 := rs (se 1 (by rfl) ⟨61649, by rfl⟩) R123299
theorem R82219 : Reach 82219 := rs (se 1 (by rfl) ⟨61664, by rfl⟩) R123329
theorem R82231 : Reach 82231 := rs (se 1 (by rfl) ⟨61673, by rfl⟩) R123347
theorem R82251 : Reach 82251 := rs (se 1 (by rfl) ⟨61688, by rfl⟩) R123377
theorem R82263 : Reach 82263 := rs (se 1 (by rfl) ⟨61697, by rfl⟩) R123395
theorem R82283 : Reach 82283 := rs (se 1 (by rfl) ⟨61712, by rfl⟩) R123425
theorem R82295 : Reach 82295 := rs (se 1 (by rfl) ⟨61721, by rfl⟩) R123443
theorem R82315 : Reach 82315 := rs (se 1 (by rfl) ⟨61736, by rfl⟩) R123473
theorem R82327 : Reach 82327 := rs (se 1 (by rfl) ⟨61745, by rfl⟩) R123491
theorem R82347 : Reach 82347 := rs (se 1 (by rfl) ⟨61760, by rfl⟩) R123521
theorem R278963 : Reach 278963 := rs (se 1 (by rfl) ⟨209222, by rfl⟩) R418445
theorem R82359 : Reach 82359 := rs (se 1 (by rfl) ⟨61769, by rfl⟩) R123539
theorem R180683 : Reach 180683 := rs (se 1 (by rfl) ⟨135512, by rfl⟩) R271025
theorem R82379 : Reach 82379 := rs (se 1 (by rfl) ⟨61784, by rfl⟩) R123569
theorem R82391 : Reach 82391 := rs (se 1 (by rfl) ⟨61793, by rfl⟩) R123587
theorem R82411 : Reach 82411 := rs (se 1 (by rfl) ⟨61808, by rfl⟩) R123617
theorem R82423 : Reach 82423 := rs (se 1 (by rfl) ⟨61817, by rfl⟩) R123635
theorem R180737 : Reach 180737 := rs (se 2 (by rfl) ⟨67776, by rfl⟩) R135553
theorem R82443 : Reach 82443 := rs (se 1 (by rfl) ⟨61832, by rfl⟩) R123665
theorem R82455 : Reach 82455 := rs (se 1 (by rfl) ⟨61841, by rfl⟩) R123683
theorem R82475 : Reach 82475 := rs (se 1 (by rfl) ⟨61856, by rfl⟩) R123713
theorem R82487 : Reach 82487 := rs (se 1 (by rfl) ⟨61865, by rfl⟩) R123731
theorem R82507 : Reach 82507 := rs (se 1 (by rfl) ⟨61880, by rfl⟩) R123761
theorem R82519 : Reach 82519 := rs (se 1 (by rfl) ⟨61889, by rfl⟩) R123779
theorem R1065565 : Reach 1065565 := rs (se 3 (by rfl) ⟨199793, by rfl⟩) R399587
theorem R82539 : Reach 82539 := rs (se 1 (by rfl) ⟨61904, by rfl⟩) R123809
theorem R82551 : Reach 82551 := rs (se 1 (by rfl) ⟨61913, by rfl⟩) R123827
theorem R2507395 : Reach 2507395 := rs (se 1 (by rfl) ⟨1880546, by rfl⟩) R3761093
theorem R82571 : Reach 82571 := rs (se 1 (by rfl) ⟨61928, by rfl⟩) R123857
theorem R82583 : Reach 82583 := rs (se 1 (by rfl) ⟨61937, by rfl⟩) R123875
theorem R82603 : Reach 82603 := rs (se 1 (by rfl) ⟨61952, by rfl⟩) R123905
theorem R82615 : Reach 82615 := rs (se 1 (by rfl) ⟨61961, by rfl⟩) R123923
theorem R279233 : Reach 279233 := rs (se 2 (by rfl) ⟨104712, by rfl⟩) R209425
theorem R82635 : Reach 82635 := rs (se 1 (by rfl) ⟨61976, by rfl⟩) R123953
theorem R82647 : Reach 82647 := rs (se 1 (by rfl) ⟨61985, by rfl⟩) R123971
theorem R180953 : Reach 180953 := rs (se 2 (by rfl) ⟨67857, by rfl⟩) R135715
theorem R82667 : Reach 82667 := rs (se 1 (by rfl) ⟨62000, by rfl⟩) R124001
theorem R82679 : Reach 82679 := rs (se 1 (by rfl) ⟨62009, by rfl⟩) R124019
theorem R82699 : Reach 82699 := rs (se 1 (by rfl) ⟨62024, by rfl⟩) R124049
theorem R82711 : Reach 82711 := rs (se 1 (by rfl) ⟨62033, by rfl⟩) R124067
theorem R82731 : Reach 82731 := rs (se 1 (by rfl) ⟨62048, by rfl⟩) R124097
theorem R181043 : Reach 181043 := rs (se 1 (by rfl) ⟨135782, by rfl⟩) R271565
theorem R82743 : Reach 82743 := rs (se 1 (by rfl) ⟨62057, by rfl⟩) R124115
theorem R82763 : Reach 82763 := rs (se 1 (by rfl) ⟨62072, by rfl⟩) R124145
theorem R181079 : Reach 181079 := rs (se 1 (by rfl) ⟨135809, by rfl⟩) R271619
theorem R82775 : Reach 82775 := rs (se 1 (by rfl) ⟨62081, by rfl⟩) R124163
theorem R770917 : Reach 770917 := rs (se 4 (by rfl) ⟨72273, by rfl⟩) R144547
theorem R82795 : Reach 82795 := rs (se 1 (by rfl) ⟨62096, by rfl⟩) R124193
theorem R82807 : Reach 82807 := rs (se 1 (by rfl) ⟨62105, by rfl⟩) R124211
theorem R82827 : Reach 82827 := rs (se 1 (by rfl) ⟨62120, by rfl⟩) R124241
theorem R82839 : Reach 82839 := rs (se 1 (by rfl) ⟨62129, by rfl⟩) R124259
theorem R82859 : Reach 82859 := rs (se 1 (by rfl) ⟨62144, by rfl⟩) R124289
theorem R82871 : Reach 82871 := rs (se 1 (by rfl) ⟨62153, by rfl⟩) R124307
theorem R82891 : Reach 82891 := rs (se 1 (by rfl) ⟨62168, by rfl⟩) R124337
theorem R82903 : Reach 82903 := rs (se 1 (by rfl) ⟨62177, by rfl⟩) R124355
theorem R82923 : Reach 82923 := rs (se 1 (by rfl) ⟨62192, by rfl⟩) R124385
theorem R82935 : Reach 82935 := rs (se 1 (by rfl) ⟨62201, by rfl⟩) R124403
theorem R181259 : Reach 181259 := rs (se 1 (by rfl) ⟨135944, by rfl⟩) R271889
theorem R82955 : Reach 82955 := rs (se 1 (by rfl) ⟨62216, by rfl⟩) R124433
theorem R82967 : Reach 82967 := rs (se 1 (by rfl) ⟨62225, by rfl⟩) R124451
theorem R82987 : Reach 82987 := rs (se 1 (by rfl) ⟨62240, by rfl⟩) R124481
theorem R410669 : Reach 410669 := rs (se 3 (by rfl) ⟨77000, by rfl⟩) R154001
theorem R705581 : Reach 705581 := rs (se 3 (by rfl) ⟨132296, by rfl⟩) R264593
theorem R82999 : Reach 82999 := rs (se 1 (by rfl) ⟨62249, by rfl⟩) R124499
theorem R181313 : Reach 181313 := rs (se 2 (by rfl) ⟨67992, by rfl⟩) R135985
theorem R83019 : Reach 83019 := rs (se 1 (by rfl) ⟨62264, by rfl⟩) R124529
theorem R83031 : Reach 83031 := rs (se 1 (by rfl) ⟨62273, by rfl⟩) R124547
theorem R83051 : Reach 83051 := rs (se 1 (by rfl) ⟨62288, by rfl⟩) R124577
theorem R83063 : Reach 83063 := rs (se 1 (by rfl) ⟨62297, by rfl⟩) R124595
theorem R83083 : Reach 83083 := rs (se 1 (by rfl) ⟨62312, by rfl⟩) R124625
theorem R83095 : Reach 83095 := rs (se 1 (by rfl) ⟨62321, by rfl⟩) R124643
theorem R83115 : Reach 83115 := rs (se 1 (by rfl) ⟨62336, by rfl⟩) R124673
theorem R83127 : Reach 83127 := rs (se 1 (by rfl) ⟨62345, by rfl⟩) R124691
theorem R279773 : Reach 279773 := rs (se 3 (by rfl) ⟨52457, by rfl⟩) R104915
theorem R181529 : Reach 181529 := rs (se 2 (by rfl) ⟨68073, by rfl⟩) R136147
theorem R902501 : Reach 902501 := rs (se 4 (by rfl) ⟨84609, by rfl⟩) R169219
theorem R181619 : Reach 181619 := rs (se 1 (by rfl) ⟨136214, by rfl⟩) R272429
theorem R181655 : Reach 181655 := rs (se 1 (by rfl) ⟨136241, by rfl⟩) R272483
theorem R181835 : Reach 181835 := rs (se 1 (by rfl) ⟨136376, by rfl⟩) R272753
theorem R181889 : Reach 181889 := rs (se 2 (by rfl) ⟨68208, by rfl⟩) R136417
theorem R706265 : Reach 706265 := rs (se 2 (by rfl) ⟨264849, by rfl⟩) R529699
theorem R313091 : Reach 313091 := rs (se 1 (by rfl) ⟨234818, by rfl⟩) R469637
theorem R313105 : Reach 313105 := rs (se 2 (by rfl) ⟨117414, by rfl⟩) R234829
theorem R182105 : Reach 182105 := rs (se 2 (by rfl) ⟨68289, by rfl⟩) R136579
theorem R182195 : Reach 182195 := rs (se 1 (by rfl) ⟨136646, by rfl⟩) R273293
theorem R182231 : Reach 182231 := rs (se 1 (by rfl) ⟨136673, by rfl⟩) R273347
theorem R84011 : Reach 84011 := rs (se 1 (by rfl) ⟨63008, by rfl⟩) R126017
theorem R313409 : Reach 313409 := rs (se 2 (by rfl) ⟨117528, by rfl⟩) R235057
theorem R739459 : Reach 739459 := rs (se 1 (by rfl) ⟨554594, by rfl⟩) R1109189
theorem R182411 : Reach 182411 := rs (se 1 (by rfl) ⟨136808, by rfl⟩) R273617
theorem R182465 : Reach 182465 := rs (se 2 (by rfl) ⟨68424, by rfl⟩) R136849
theorem R706765 : Reach 706765 := rs (se 3 (by rfl) ⟨132518, by rfl⟩) R265037
theorem R84235 : Reach 84235 := rs (se 1 (by rfl) ⟨63176, by rfl⟩) R126353
theorem R182681 : Reach 182681 := rs (se 2 (by rfl) ⟨68505, by rfl⟩) R137011
theorem R182771 : Reach 182771 := rs (se 1 (by rfl) ⟨137078, by rfl⟩) R274157
theorem R182807 : Reach 182807 := rs (se 1 (by rfl) ⟨137105, by rfl⟩) R274211
theorem R117335 : Reach 117335 := rs (se 1 (by rfl) ⟨88001, by rfl⟩) R176003
theorem R182987 : Reach 182987 := rs (se 1 (by rfl) ⟨137240, by rfl⟩) R274481
theorem R314077 : Reach 314077 := rs (se 3 (by rfl) ⟨58889, by rfl⟩) R117779
theorem R183041 : Reach 183041 := rs (se 2 (by rfl) ⟨68640, by rfl⟩) R137281
theorem R183257 : Reach 183257 := rs (se 2 (by rfl) ⟨68721, by rfl⟩) R137443
theorem R183347 : Reach 183347 := rs (se 1 (by rfl) ⟨137510, by rfl⟩) R275021
theorem R183383 : Reach 183383 := rs (se 1 (by rfl) ⟨137537, by rfl⟩) R275075
theorem R85259 : Reach 85259 := rs (se 1 (by rfl) ⟨63944, by rfl⟩) R127889
theorem R183563 : Reach 183563 := rs (se 1 (by rfl) ⟨137672, by rfl⟩) R275345
theorem R150835 : Reach 150835 := rs (se 1 (by rfl) ⟨113126, by rfl⟩) R226253
theorem R183617 : Reach 183617 := rs (se 2 (by rfl) ⟨68856, by rfl⟩) R137713
theorem R183809 : Reach 183809 := rs (se 2 (by rfl) ⟨68928, by rfl⟩) R137857
theorem R347665 : Reach 347665 := rs (se 2 (by rfl) ⟨130374, by rfl⟩) R260749
theorem R183833 : Reach 183833 := rs (se 2 (by rfl) ⟨68937, by rfl⟩) R137875
theorem R183923 : Reach 183923 := rs (se 1 (by rfl) ⟨137942, by rfl⟩) R275885
theorem R183959 : Reach 183959 := rs (se 1 (by rfl) ⟨137969, by rfl⟩) R275939
theorem R85655 : Reach 85655 := rs (se 1 (by rfl) ⟨64241, by rfl⟩) R128483
theorem R151283 : Reach 151283 := rs (se 1 (by rfl) ⟨113462, by rfl⟩) R226925
theorem R151321 : Reach 151321 := rs (se 2 (by rfl) ⟨56745, by rfl⟩) R113491
theorem R184139 : Reach 184139 := rs (se 1 (by rfl) ⟨138104, by rfl⟩) R276209
theorem R184193 : Reach 184193 := rs (se 2 (by rfl) ⟨69072, by rfl⟩) R138145
theorem R282541 : Reach 282541 := rs (se 3 (by rfl) ⟨52976, by rfl⟩) R105953
theorem R577459 : Reach 577459 := rs (se 1 (by rfl) ⟨433094, by rfl⟩) R866189
theorem R118745 : Reach 118745 := rs (se 2 (by rfl) ⟨44529, by rfl⟩) R89059
theorem R315353 : Reach 315353 := rs (se 2 (by rfl) ⟨118257, by rfl⟩) R236515
theorem R118859 : Reach 118859 := rs (se 1 (by rfl) ⟨89144, by rfl⟩) R178289
theorem R118871 : Reach 118871 := rs (se 1 (by rfl) ⟨89153, by rfl⟩) R178307
theorem R184409 : Reach 184409 := rs (se 2 (by rfl) ⟨69153, by rfl⟩) R138307
theorem R118937 : Reach 118937 := rs (se 2 (by rfl) ⟨44601, by rfl⟩) R89203
theorem R184499 : Reach 184499 := rs (se 1 (by rfl) ⟨138374, by rfl⟩) R276749
theorem R184535 : Reach 184535 := rs (se 1 (by rfl) ⟨138401, by rfl⟩) R276803
theorem R151769 : Reach 151769 := rs (se 2 (by rfl) ⟨56913, by rfl⟩) R113827
theorem R119051 : Reach 119051 := rs (se 1 (by rfl) ⟨89288, by rfl⟩) R178577
theorem R119063 : Reach 119063 := rs (se 1 (by rfl) ⟨89297, by rfl⟩) R178595
theorem R119129 : Reach 119129 := rs (se 2 (by rfl) ⟨44673, by rfl⟩) R89347
theorem R184715 : Reach 184715 := rs (se 1 (by rfl) ⟨138536, by rfl⟩) R277073
theorem R86455 : Reach 86455 := rs (se 1 (by rfl) ⟨64841, by rfl⟩) R129683
theorem R184769 : Reach 184769 := rs (se 2 (by rfl) ⟨69288, by rfl⟩) R138577
theorem R119243 : Reach 119243 := rs (se 1 (by rfl) ⟨89432, by rfl⟩) R178865
theorem R119255 : Reach 119255 := rs (se 1 (by rfl) ⟨89441, by rfl⟩) R178883
theorem R119321 : Reach 119321 := rs (se 2 (by rfl) ⟨44745, by rfl⟩) R89491
theorem R119435 : Reach 119435 := rs (se 1 (by rfl) ⟨89576, by rfl⟩) R179153
theorem R119447 : Reach 119447 := rs (se 1 (by rfl) ⟨89585, by rfl⟩) R179171
theorem R184985 : Reach 184985 := rs (se 2 (by rfl) ⟨69369, by rfl⟩) R138739
theorem R119513 : Reach 119513 := rs (se 2 (by rfl) ⟨44817, by rfl⟩) R89635
theorem R185075 : Reach 185075 := rs (se 1 (by rfl) ⟨138806, by rfl⟩) R277613
theorem R185111 : Reach 185111 := rs (se 1 (by rfl) ⟨138833, by rfl⟩) R277667
theorem R86827 : Reach 86827 := rs (se 1 (by rfl) ⟨65120, by rfl⟩) R130241
theorem R676673 : Reach 676673 := rs (se 2 (by rfl) ⟨253752, by rfl⟩) R507505
theorem R873281 : Reach 873281 := rs (se 2 (by rfl) ⟨327480, by rfl⟩) R654961
theorem R119627 : Reach 119627 := rs (se 1 (by rfl) ⟨89720, by rfl⟩) R179441
theorem R119639 : Reach 119639 := rs (se 1 (by rfl) ⟨89729, by rfl⟩) R179459
theorem R414557 : Reach 414557 := rs (se 3 (by rfl) ⟨77729, by rfl⟩) R155459
theorem R119705 : Reach 119705 := rs (se 2 (by rfl) ⟨44889, by rfl⟩) R89779
theorem R152513 : Reach 152513 := rs (se 2 (by rfl) ⟨57192, by rfl⟩) R114385
theorem R185291 : Reach 185291 := rs (se 1 (by rfl) ⟨138968, by rfl⟩) R277937
theorem R316381 : Reach 316381 := rs (se 3 (by rfl) ⟨59321, by rfl⟩) R118643
theorem R185345 : Reach 185345 := rs (se 2 (by rfl) ⟨69504, by rfl⟩) R139009
theorem R119819 : Reach 119819 := rs (se 1 (by rfl) ⟨89864, by rfl⟩) R179729
theorem R1463309 : Reach 1463309 := rs (se 3 (by rfl) ⟨274370, by rfl⟩) R548741
theorem R119831 : Reach 119831 := rs (se 1 (by rfl) ⟨89873, by rfl⟩) R179747
theorem R119897 : Reach 119897 := rs (se 2 (by rfl) ⟨44961, by rfl⟩) R89923
theorem R120011 : Reach 120011 := rs (se 1 (by rfl) ⟨90008, by rfl⟩) R180017
theorem R152779 : Reach 152779 := rs (se 1 (by rfl) ⟨114584, by rfl⟩) R229169
theorem R120023 : Reach 120023 := rs (se 1 (by rfl) ⟨90017, by rfl⟩) R180035
theorem R185561 : Reach 185561 := rs (se 2 (by rfl) ⟨69585, by rfl⟩) R139171
theorem R87275 : Reach 87275 := rs (se 1 (by rfl) ⟨65456, by rfl⟩) R130913
theorem R120089 : Reach 120089 := rs (se 2 (by rfl) ⟨45033, by rfl⟩) R90067
theorem R185651 : Reach 185651 := rs (se 1 (by rfl) ⟨139238, by rfl⟩) R278477
theorem R185687 : Reach 185687 := rs (se 1 (by rfl) ⟨139265, by rfl⟩) R278531
theorem R120203 : Reach 120203 := rs (se 1 (by rfl) ⟨90152, by rfl⟩) R180305
theorem R120215 : Reach 120215 := rs (se 1 (by rfl) ⟨90161, by rfl⟩) R180323
theorem R284077 : Reach 284077 := rs (se 3 (by rfl) ⟨53264, by rfl⟩) R106529
theorem R120281 : Reach 120281 := rs (se 2 (by rfl) ⟨45105, by rfl⟩) R90211
theorem R185867 : Reach 185867 := rs (se 1 (by rfl) ⟨139400, by rfl⟩) R278801
theorem R185921 : Reach 185921 := rs (se 2 (by rfl) ⟨69720, by rfl⟩) R139441
theorem R120395 : Reach 120395 := rs (se 1 (by rfl) ⟨90296, by rfl⟩) R180593
theorem R120407 : Reach 120407 := rs (se 1 (by rfl) ⟨90305, by rfl⟩) R180611
theorem R153227 : Reach 153227 := rs (se 1 (by rfl) ⟨114920, by rfl⟩) R229841
theorem R284305 : Reach 284305 := rs (se 2 (by rfl) ⟨106614, by rfl⟩) R213229
theorem R120473 : Reach 120473 := rs (se 2 (by rfl) ⟨45177, by rfl⟩) R90355
theorem R120587 : Reach 120587 := rs (se 1 (by rfl) ⟨90440, by rfl⟩) R180881
theorem R513809 : Reach 513809 := rs (se 2 (by rfl) ⟨192678, by rfl⟩) R385357
theorem R120599 : Reach 120599 := rs (se 1 (by rfl) ⟨90449, by rfl⟩) R180899
theorem R186137 : Reach 186137 := rs (se 2 (by rfl) ⟨69801, by rfl⟩) R139603
theorem R153409 : Reach 153409 := rs (se 2 (by rfl) ⟨57528, by rfl⟩) R115057
theorem R120665 : Reach 120665 := rs (se 2 (by rfl) ⟨45249, by rfl⟩) R90499
theorem R350041 : Reach 350041 := rs (se 2 (by rfl) ⟨131265, by rfl⟩) R262531
theorem R186227 : Reach 186227 := rs (se 1 (by rfl) ⟨139670, by rfl⟩) R279341
theorem R186251 : Reach 186251 := rs (se 1 (by rfl) ⟨139688, by rfl⟩) R279377
theorem R186263 : Reach 186263 := rs (se 1 (by rfl) ⟨139697, by rfl⟩) R279395
theorem R120779 : Reach 120779 := rs (se 1 (by rfl) ⟨90584, by rfl⟩) R181169
theorem R120791 : Reach 120791 := rs (se 1 (by rfl) ⟨90593, by rfl⟩) R181187
theorem R120857 : Reach 120857 := rs (se 2 (by rfl) ⟨45321, by rfl⟩) R90643
theorem R186443 : Reach 186443 := rs (se 1 (by rfl) ⟨139832, by rfl⟩) R279665
theorem R186497 : Reach 186497 := rs (se 2 (by rfl) ⟨69936, by rfl⟩) R139873
theorem R120971 : Reach 120971 := rs (se 1 (by rfl) ⟨90728, by rfl⟩) R181457
theorem R120983 : Reach 120983 := rs (se 1 (by rfl) ⟨90737, by rfl⟩) R181475
theorem R153751 : Reach 153751 := rs (se 1 (by rfl) ⟨115313, by rfl⟩) R230627
theorem R121049 : Reach 121049 := rs (se 2 (by rfl) ⟨45393, by rfl⟩) R90787
theorem R121163 : Reach 121163 := rs (se 1 (by rfl) ⟨90872, by rfl⟩) R181745
theorem R121175 : Reach 121175 := rs (se 1 (by rfl) ⟨90881, by rfl⟩) R181763
theorem R186713 : Reach 186713 := rs (se 2 (by rfl) ⟨70017, by rfl⟩) R140035
theorem R153971 : Reach 153971 := rs (se 1 (by rfl) ⟨115478, by rfl⟩) R230957
theorem R88471 : Reach 88471 := rs (se 1 (by rfl) ⟨66353, by rfl⟩) R132707
theorem R154009 : Reach 154009 := rs (se 2 (by rfl) ⟨57753, by rfl⟩) R115507
theorem R121241 : Reach 121241 := rs (se 2 (by rfl) ⟨45465, by rfl⟩) R90931
theorem R186803 : Reach 186803 := rs (se 1 (by rfl) ⟨140102, by rfl⟩) R280205
theorem R186839 : Reach 186839 := rs (se 1 (by rfl) ⟨140129, by rfl⟩) R280259
theorem R121355 : Reach 121355 := rs (se 1 (by rfl) ⟨91016, by rfl⟩) R182033
theorem R121367 : Reach 121367 := rs (se 1 (by rfl) ⟨91025, by rfl⟩) R182051
theorem R88651 : Reach 88651 := rs (se 1 (by rfl) ⟨66488, by rfl⟩) R132977
theorem R154199 : Reach 154199 := rs (se 1 (by rfl) ⟨115649, by rfl⟩) R231299
theorem R121433 : Reach 121433 := rs (se 2 (by rfl) ⟨45537, by rfl⟩) R91075
theorem R187019 : Reach 187019 := rs (se 1 (by rfl) ⟨140264, by rfl⟩) R280529
theorem R121547 : Reach 121547 := rs (se 1 (by rfl) ⟨91160, by rfl⟩) R182321
theorem R121559 : Reach 121559 := rs (se 1 (by rfl) ⟨91169, by rfl⟩) R182339
theorem R350999 : Reach 350999 := rs (se 1 (by rfl) ⟨263249, by rfl⟩) R526499
theorem R121625 : Reach 121625 := rs (se 2 (by rfl) ⟨45609, by rfl⟩) R91219
theorem R187201 : Reach 187201 := rs (se 2 (by rfl) ⟨70200, by rfl⟩) R140401
theorem R154457 : Reach 154457 := rs (se 2 (by rfl) ⟨57921, by rfl⟩) R115843
theorem R121739 : Reach 121739 := rs (se 1 (by rfl) ⟨91304, by rfl⟩) R182609
theorem R121751 : Reach 121751 := rs (se 1 (by rfl) ⟨91313, by rfl⟩) R182627
theorem R416663 : Reach 416663 := rs (se 1 (by rfl) ⟨312497, by rfl⟩) R624995
theorem R1563569 : Reach 1563569 := rs (se 2 (by rfl) ⟨586338, by rfl⟩) R1172677
theorem R121817 : Reach 121817 := rs (se 2 (by rfl) ⟨45681, by rfl⟩) R91363
theorem R89131 : Reach 89131 := rs (se 1 (by rfl) ⟨66848, by rfl⟩) R133697
theorem R154675 : Reach 154675 := rs (se 1 (by rfl) ⟨116006, by rfl⟩) R232013
theorem R121931 : Reach 121931 := rs (se 1 (by rfl) ⟨91448, by rfl⟩) R182897
theorem R121943 : Reach 121943 := rs (se 1 (by rfl) ⟨91457, by rfl⟩) R182915
theorem R89239 : Reach 89239 := rs (se 1 (by rfl) ⟨66929, by rfl⟩) R133859
theorem R679063 : Reach 679063 := rs (se 1 (by rfl) ⟨509297, by rfl⟩) R1018595
theorem R122009 : Reach 122009 := rs (se 2 (by rfl) ⟨45753, by rfl⟩) R91507
theorem R154867 : Reach 154867 := rs (se 1 (by rfl) ⟨116150, by rfl⟩) R232301
theorem R122123 : Reach 122123 := rs (se 1 (by rfl) ⟨91592, by rfl⟩) R183185
theorem R122135 : Reach 122135 := rs (se 1 (by rfl) ⟨91601, by rfl⟩) R183203
theorem R89419 : Reach 89419 := rs (se 1 (by rfl) ⟨67064, by rfl⟩) R134129
theorem R122201 : Reach 122201 := rs (se 2 (by rfl) ⟨45825, by rfl⟩) R91651
theorem R89527 : Reach 89527 := rs (se 1 (by rfl) ⟨67145, by rfl⟩) R134291
theorem R122315 : Reach 122315 := rs (se 1 (by rfl) ⟨91736, by rfl⟩) R183473
theorem R122327 : Reach 122327 := rs (se 1 (by rfl) ⟨91745, by rfl⟩) R183491
theorem R122393 : Reach 122393 := rs (se 2 (by rfl) ⟨45897, by rfl⟩) R91795
theorem R89707 : Reach 89707 := rs (se 1 (by rfl) ⟨67280, by rfl⟩) R134561
theorem R122507 : Reach 122507 := rs (se 1 (by rfl) ⟨91880, by rfl⟩) R183761
theorem R122519 : Reach 122519 := rs (se 1 (by rfl) ⟨91889, by rfl⟩) R183779
theorem R89815 : Reach 89815 := rs (se 1 (by rfl) ⟨67361, by rfl⟩) R134723
theorem R155353 : Reach 155353 := rs (se 2 (by rfl) ⟨58257, by rfl⟩) R116515
theorem R122585 : Reach 122585 := rs (se 2 (by rfl) ⟨45969, by rfl⟩) R91939
theorem R646987 : Reach 646987 := rs (se 1 (by rfl) ⟨485240, by rfl⟩) R970481
theorem R122699 : Reach 122699 := rs (se 1 (by rfl) ⟨92024, by rfl⟩) R184049
theorem R122711 : Reach 122711 := rs (se 1 (by rfl) ⟨92033, by rfl⟩) R184067
theorem R89995 : Reach 89995 := rs (se 1 (by rfl) ⟨67496, by rfl⟩) R134993
theorem R122777 : Reach 122777 := rs (se 2 (by rfl) ⟨46041, by rfl⟩) R92083
theorem R90103 : Reach 90103 := rs (se 1 (by rfl) ⟨67577, by rfl⟩) R135155
theorem R122891 : Reach 122891 := rs (se 1 (by rfl) ⟨92168, by rfl⟩) R184337
theorem R122903 : Reach 122903 := rs (se 1 (by rfl) ⟨92177, by rfl⟩) R184355
theorem R122969 : Reach 122969 := rs (se 2 (by rfl) ⟨46113, by rfl⟩) R92227
theorem R90283 : Reach 90283 := rs (se 1 (by rfl) ⟨67712, by rfl⟩) R135425
theorem R123083 : Reach 123083 := rs (se 1 (by rfl) ⟨92312, by rfl⟩) R184625
theorem R123095 : Reach 123095 := rs (se 1 (by rfl) ⟨92321, by rfl⟩) R184643
theorem R155915 : Reach 155915 := rs (se 1 (by rfl) ⟨116936, by rfl⟩) R233873
theorem R90391 : Reach 90391 := rs (se 1 (by rfl) ⟨67793, by rfl⟩) R135587
theorem R123161 : Reach 123161 := rs (se 2 (by rfl) ⟨46185, by rfl⟩) R92371
theorem R123275 : Reach 123275 := rs (se 1 (by rfl) ⟨92456, by rfl⟩) R184913
theorem R123287 : Reach 123287 := rs (se 1 (by rfl) ⟨92465, by rfl⟩) R184931
theorem R156097 : Reach 156097 := rs (se 2 (by rfl) ⟨58536, by rfl⟩) R117073
theorem R90571 : Reach 90571 := rs (se 1 (by rfl) ⟨67928, by rfl⟩) R135857
theorem R123353 : Reach 123353 := rs (se 2 (by rfl) ⟨46257, by rfl⟩) R92515
theorem R156161 : Reach 156161 := rs (se 2 (by rfl) ⟨58560, by rfl⟩) R117121
theorem R90679 : Reach 90679 := rs (se 1 (by rfl) ⟨68009, by rfl⟩) R136019
theorem R123467 : Reach 123467 := rs (se 1 (by rfl) ⟨92600, by rfl⟩) R185201
theorem R123479 : Reach 123479 := rs (se 1 (by rfl) ⟨92609, by rfl⟩) R185219
theorem R123545 : Reach 123545 := rs (se 2 (by rfl) ⟨46329, by rfl⟩) R92659
theorem R90859 : Reach 90859 := rs (se 1 (by rfl) ⟨68144, by rfl⟩) R136289
theorem R123659 : Reach 123659 := rs (se 1 (by rfl) ⟨92744, by rfl⟩) R185489
theorem R123671 : Reach 123671 := rs (se 1 (by rfl) ⟨92753, by rfl⟩) R185507
theorem R353099 : Reach 353099 := rs (se 1 (by rfl) ⟨264824, by rfl⟩) R529649
theorem R90967 : Reach 90967 := rs (se 1 (by rfl) ⟨68225, by rfl⟩) R136451
theorem R320345 : Reach 320345 := rs (se 2 (by rfl) ⟨120129, by rfl⟩) R240259
theorem R222041 : Reach 222041 := rs (se 2 (by rfl) ⟨83265, by rfl⟩) R166531
theorem R123737 : Reach 123737 := rs (se 2 (by rfl) ⟨46401, by rfl⟩) R92803
theorem R123851 : Reach 123851 := rs (se 1 (by rfl) ⟨92888, by rfl⟩) R185777
theorem R123863 : Reach 123863 := rs (se 1 (by rfl) ⟨92897, by rfl⟩) R185795
theorem R91147 : Reach 91147 := rs (se 1 (by rfl) ⟨68360, by rfl⟩) R136721
theorem R123929 : Reach 123929 := rs (se 2 (by rfl) ⟨46473, by rfl⟩) R92947
theorem R91255 : Reach 91255 := rs (se 1 (by rfl) ⟨68441, by rfl⟩) R136883
theorem R156811 : Reach 156811 := rs (se 1 (by rfl) ⟨117608, by rfl⟩) R235217
theorem R124043 : Reach 124043 := rs (se 1 (by rfl) ⟨93032, by rfl⟩) R186065
theorem R124055 : Reach 124055 := rs (se 1 (by rfl) ⟨93041, by rfl⟩) R186083
theorem R156887 : Reach 156887 := rs (se 1 (by rfl) ⟨117665, by rfl⟩) R235331
theorem R124121 : Reach 124121 := rs (se 2 (by rfl) ⟨46545, by rfl⟩) R93091
theorem R91435 : Reach 91435 := rs (se 1 (by rfl) ⟨68576, by rfl⟩) R137153
theorem R124235 : Reach 124235 := rs (se 1 (by rfl) ⟨93176, by rfl⟩) R186353
theorem R124247 : Reach 124247 := rs (se 1 (by rfl) ⟨93185, by rfl⟩) R186371
theorem R91543 : Reach 91543 := rs (se 1 (by rfl) ⟨68657, by rfl⟩) R137315
theorem R124313 : Reach 124313 := rs (se 2 (by rfl) ⟨46617, by rfl⟩) R93235
theorem R124363 : Reach 124363 := rs (se 1 (by rfl) ⟨93272, by rfl⟩) R186545
theorem R124427 : Reach 124427 := rs (se 1 (by rfl) ⟨93320, by rfl⟩) R186641
theorem R124439 : Reach 124439 := rs (se 1 (by rfl) ⟨93329, by rfl⟩) R186659
theorem R452141 : Reach 452141 := rs (se 3 (by rfl) ⟨84776, by rfl⟩) R169553
theorem R91723 : Reach 91723 := rs (se 1 (by rfl) ⟨68792, by rfl⟩) R137585
theorem R1336907 : Reach 1336907 := rs (se 1 (by rfl) ⟨1002680, by rfl⟩) R2005361
theorem R124505 : Reach 124505 := rs (se 2 (by rfl) ⟨46689, by rfl⟩) R93379
theorem R91831 : Reach 91831 := rs (se 1 (by rfl) ⟨68873, by rfl⟩) R137747
theorem R124619 : Reach 124619 := rs (se 1 (by rfl) ⟨93464, by rfl⟩) R186929
theorem R124631 : Reach 124631 := rs (se 1 (by rfl) ⟨93473, by rfl⟩) R186947
theorem R223069 : Reach 223069 := rs (se 3 (by rfl) ⟨41825, by rfl⟩) R83651
theorem R92011 : Reach 92011 := rs (se 1 (by rfl) ⟨69008, by rfl⟩) R138017
theorem R157555 : Reach 157555 := rs (se 1 (by rfl) ⟨118166, by rfl⟩) R236333
theorem R92119 : Reach 92119 := rs (se 1 (by rfl) ⟨69089, by rfl⟩) R138179
theorem R387089 : Reach 387089 := rs (se 2 (by rfl) ⟨145158, by rfl⟩) R290317
theorem R92215 : Reach 92215 := rs (se 1 (by rfl) ⟨69161, by rfl⟩) R138323
theorem R157783 : Reach 157783 := rs (se 1 (by rfl) ⟨118337, by rfl⟩) R236675
theorem R92299 : Reach 92299 := rs (se 1 (by rfl) ⟨69224, by rfl⟩) R138449
theorem R92407 : Reach 92407 := rs (se 1 (by rfl) ⟨69305, by rfl⟩) R138611
theorem R518501 : Reach 518501 := rs (se 4 (by rfl) ⟨48609, by rfl⟩) R97219
theorem R420227 : Reach 420227 := rs (se 1 (by rfl) ⟨315170, by rfl⟩) R630341
theorem R158105 : Reach 158105 := rs (se 2 (by rfl) ⟨59289, by rfl⟩) R118579
theorem R92587 : Reach 92587 := rs (se 1 (by rfl) ⟨69440, by rfl⟩) R138881
theorem R354739 : Reach 354739 := rs (se 1 (by rfl) ⟨266054, by rfl⟩) R532109
theorem R649745 : Reach 649745 := rs (se 2 (by rfl) ⟨243654, by rfl⟩) R487309
theorem R92695 : Reach 92695 := rs (se 1 (by rfl) ⟨69521, by rfl⟩) R139043
theorem R92875 : Reach 92875 := rs (se 1 (by rfl) ⟨69656, by rfl⟩) R139313
theorem R92983 : Reach 92983 := rs (se 1 (by rfl) ⟨69737, by rfl⟩) R139475
theorem R518987 : Reach 518987 := rs (se 1 (by rfl) ⟨389240, by rfl⟩) R778481
theorem R93163 : Reach 93163 := rs (se 1 (by rfl) ⟨69872, by rfl⟩) R139745
theorem R93271 : Reach 93271 := rs (se 1 (by rfl) ⟨69953, by rfl⟩) R139907
theorem R93451 : Reach 93451 := rs (se 1 (by rfl) ⟨70088, by rfl⟩) R140177
theorem R7925141 : Reach 7925141 := rs (se 6 (by rfl) ⟨185745, by rfl⟩) R371491
theorem R1404377 : Reach 1404377 := rs (se 2 (by rfl) ⟨526641, by rfl⟩) R1053283
theorem R192179 : Reach 192179 := rs (se 1 (by rfl) ⟨144134, by rfl⟩) R288269
theorem R192217 : Reach 192217 := rs (se 2 (by rfl) ⟨72081, by rfl⟩) R144163
theorem R454531 : Reach 454531 := rs (se 1 (by rfl) ⟨340898, by rfl⟩) R681797
theorem R192449 : Reach 192449 := rs (se 2 (by rfl) ⟨72168, by rfl⟩) R144337
theorem R1339523 : Reach 1339523 := rs (se 1 (by rfl) ⟨1004642, by rfl⟩) R2009285
theorem R192833 : Reach 192833 := rs (se 2 (by rfl) ⟨72312, by rfl⟩) R144625
theorem R520627 : Reach 520627 := rs (se 1 (by rfl) ⟨390470, by rfl⟩) R780941
theorem R291275 : Reach 291275 := rs (se 1 (by rfl) ⟨218456, by rfl⟩) R436913
theorem R291545 : Reach 291545 := rs (se 2 (by rfl) ⟨109329, by rfl⟩) R218659
theorem R455489 : Reach 455489 := rs (se 2 (by rfl) ⟨170808, by rfl⟩) R341617
theorem R193601 : Reach 193601 := rs (se 2 (by rfl) ⟨72600, by rfl⟩) R145201
theorem R226583 : Reach 226583 := rs (se 1 (by rfl) ⟨169937, by rfl⟩) R339875
theorem R128395 : Reach 128395 := rs (se 1 (by rfl) ⟨96296, by rfl⟩) R192593
theorem R587213 : Reach 587213 := rs (se 3 (by rfl) ⟨110102, by rfl⟩) R220205
theorem R260185 : Reach 260185 := rs (se 2 (by rfl) ⟨97569, by rfl⟩) R195139
theorem R2586775 : Reach 2586775 := rs (se 1 (by rfl) ⟨1940081, by rfl⟩) R3880163
theorem R162443 : Reach 162443 := rs (se 1 (by rfl) ⟨121832, by rfl⟩) R243665
theorem R359129 : Reach 359129 := rs (se 2 (by rfl) ⟨134673, by rfl⟩) R269347
theorem R359257 : Reach 359257 := rs (se 2 (by rfl) ⟨134721, by rfl⟩) R269443
theorem R293777 : Reach 293777 := rs (se 2 (by rfl) ⟨110166, by rfl⟩) R220333
theorem R424855 : Reach 424855 := rs (se 1 (by rfl) ⟨318641, by rfl⟩) R637283
theorem R293977 : Reach 293977 := rs (se 2 (by rfl) ⟨110241, by rfl⟩) R220483
theorem R261569 : Reach 261569 := rs (se 2 (by rfl) ⟨98088, by rfl⟩) R196177
theorem R196033 : Reach 196033 := rs (se 2 (by rfl) ⟨73512, by rfl⟩) R147025
theorem R229043 : Reach 229043 := rs (se 1 (by rfl) ⟨171782, by rfl⟩) R343565
theorem R1343411 : Reach 1343411 := rs (se 1 (by rfl) ⟨1007558, by rfl⟩) R2015117
theorem R196793 : Reach 196793 := rs (se 2 (by rfl) ⟨73797, by rfl⟩) R147595
theorem R131387 : Reach 131387 := rs (se 1 (by rfl) ⟨98540, by rfl⟩) R197081
theorem R229817 : Reach 229817 := rs (se 2 (by rfl) ⟨86181, by rfl⟩) R172363
theorem R393815 : Reach 393815 := rs (se 1 (by rfl) ⟨295361, by rfl⟩) R590723
theorem R197207 : Reach 197207 := rs (se 1 (by rfl) ⟨147905, by rfl⟩) R295811
theorem R3343193 : Reach 3343193 := rs (se 2 (by rfl) ⟨1253697, by rfl⟩) R2507395
theorem R132025 : Reach 132025 := rs (se 2 (by rfl) ⟨49509, by rfl⟩) R99019
theorem R918539 : Reach 918539 := rs (se 1 (by rfl) ⟨688904, by rfl⟩) R1377809
theorem R459863 : Reach 459863 := rs (se 1 (by rfl) ⟨344897, by rfl⟩) R689795
theorem R230809 : Reach 230809 := rs (se 2 (by rfl) ⟨86553, by rfl⟩) R173107
theorem R132553 : Reach 132553 := rs (se 2 (by rfl) ⟨49707, by rfl⟩) R99415
theorem R788087 : Reach 788087 := rs (se 1 (by rfl) ⟨591065, by rfl⟩) R1182131
theorem R165817 : Reach 165817 := rs (se 2 (by rfl) ⟨62181, by rfl⟩) R124363
theorem R264235 : Reach 264235 := rs (se 1 (by rfl) ⟨198176, by rfl⟩) R396353
theorem R821381 : Reach 821381 := rs (se 4 (by rfl) ⟨77004, by rfl⟩) R154009
theorem R592109 : Reach 592109 := rs (se 3 (by rfl) ⟨111020, by rfl⟩) R222041
theorem R297425 : Reach 297425 := rs (se 2 (by rfl) ⟨111534, by rfl⟩) R223069
theorem R100855 : Reach 100855 := rs (se 1 (by rfl) ⟨75641, by rfl⟩) R151283
theorem R133751 : Reach 133751 := rs (se 1 (by rfl) ⟨100313, by rfl⟩) R200627
theorem R133817 : Reach 133817 := rs (se 2 (by rfl) ⟨50181, by rfl⟩) R100363
theorem R428773 : Reach 428773 := rs (se 4 (by rfl) ⟨40197, by rfl⟩) R80395
theorem R101179 : Reach 101179 := rs (se 1 (by rfl) ⟨75884, by rfl⟩) R151769
theorem R985945 : Reach 985945 := rs (se 2 (by rfl) ⟨369729, by rfl⟩) R739459
theorem R363473 : Reach 363473 := rs (se 2 (by rfl) ⟨136302, by rfl⟩) R272605
theorem R298013 : Reach 298013 := rs (se 3 (by rfl) ⟨55877, by rfl⟩) R111755
theorem R134203 : Reach 134203 := rs (se 1 (by rfl) ⟨100652, by rfl⟩) R201305
theorem R134345 : Reach 134345 := rs (se 2 (by rfl) ⟨50379, by rfl⟩) R100759
theorem R462095 : Reach 462095 := rs (se 1 (by rfl) ⟨346571, by rfl⟩) R693143
theorem R232733 : Reach 232733 := rs (se 3 (by rfl) ⟨43637, by rfl⟩) R87275
theorem R101675 : Reach 101675 := rs (se 1 (by rfl) ⟨76256, by rfl⟩) R152513
theorem R265619 : Reach 265619 := rs (se 1 (by rfl) ⟨199214, by rfl⟩) R398429
theorem R462347 : Reach 462347 := rs (se 1 (by rfl) ⟨346760, by rfl⟩) R693521
theorem R1183409 : Reach 1183409 := rs (se 2 (by rfl) ⟨443778, by rfl⟩) R887557
theorem R102151 : Reach 102151 := rs (se 1 (by rfl) ⟨76613, by rfl⟩) R153227
theorem R266017 : Reach 266017 := rs (se 2 (by rfl) ⟨99756, by rfl⟩) R199513
theorem R135047 : Reach 135047 := rs (se 1 (by rfl) ⟨101285, by rfl⟩) R202571
theorem R233417 : Reach 233417 := rs (se 2 (by rfl) ⟨87531, by rfl⟩) R175063
theorem R200819 : Reach 200819 := rs (se 1 (by rfl) ⟨150614, by rfl⟩) R301229
theorem R200839 : Reach 200839 := rs (se 1 (by rfl) ⟨150629, by rfl⟩) R301259
theorem R102647 : Reach 102647 := rs (se 1 (by rfl) ⟨76985, by rfl⟩) R153971
theorem R102799 : Reach 102799 := rs (se 1 (by rfl) ⟨77099, by rfl⟩) R154199
theorem R201113 : Reach 201113 := rs (se 2 (by rfl) ⟨75417, by rfl⟩) R150835
theorem R135695 : Reach 135695 := rs (se 1 (by rfl) ⟨101771, by rfl⟩) R203543
theorem R233999 : Reach 233999 := rs (se 1 (by rfl) ⟨175499, by rfl⟩) R350999
theorem R201275 : Reach 201275 := rs (se 1 (by rfl) ⟨150956, by rfl⟩) R301913
theorem R102971 : Reach 102971 := rs (se 1 (by rfl) ⟨77228, by rfl⟩) R154457
theorem R463553 : Reach 463553 := rs (se 2 (by rfl) ⟨173832, by rfl⟩) R347665
theorem R201487 : Reach 201487 := rs (se 1 (by rfl) ⟨151115, by rfl⟩) R302231
theorem R2265893 : Reach 2265893 := rs (se 4 (by rfl) ⟨212427, by rfl⟩) R424855
theorem R201761 : Reach 201761 := rs (se 2 (by rfl) ⟨75660, by rfl⟩) R151321
theorem R136235 : Reach 136235 := rs (se 1 (by rfl) ⟨102176, by rfl⟩) R204353
theorem R922913 : Reach 922913 := rs (se 2 (by rfl) ⟨346092, by rfl⟩) R692185
theorem R136633 : Reach 136633 := rs (se 2 (by rfl) ⟨51237, by rfl⟩) R102475
theorem R235009 : Reach 235009 := rs (se 2 (by rfl) ⟨88128, by rfl⟩) R176257
theorem R103943 : Reach 103943 := rs (se 1 (by rfl) ⟨77957, by rfl⟩) R155915
theorem R104107 : Reach 104107 := rs (se 1 (by rfl) ⟨78080, by rfl⟩) R156161
theorem R235399 : Reach 235399 := rs (se 1 (by rfl) ⟨176549, by rfl⟩) R353099
theorem R694169 : Reach 694169 := rs (se 2 (by rfl) ⟨260313, by rfl⟩) R520627
theorem R268217 : Reach 268217 := rs (se 2 (by rfl) ⟨100581, by rfl⟩) R201163
theorem R202763 : Reach 202763 := rs (se 1 (by rfl) ⟨152072, by rfl⟩) R304145
theorem R137335 : Reach 137335 := rs (se 1 (by rfl) ⟨103001, by rfl⟩) R206003
theorem R104591 : Reach 104591 := rs (se 1 (by rfl) ⟨78443, by rfl⟩) R156887
theorem R235673 : Reach 235673 := rs (se 2 (by rfl) ⟨88377, by rfl⟩) R176755
theorem R137531 : Reach 137531 := rs (se 1 (by rfl) ⟨103148, by rfl⟩) R206297
theorem R301427 : Reach 301427 := rs (se 1 (by rfl) ⟨226070, by rfl⟩) R452141
theorem R891271 : Reach 891271 := rs (se 1 (by rfl) ⟨668453, by rfl⟩) R1336907
theorem R268811 : Reach 268811 := rs (se 1 (by rfl) ⟨201608, by rfl⟩) R403217
theorem R268919 : Reach 268919 := rs (se 1 (by rfl) ⟨201689, by rfl⟩) R403379
theorem R203411 : Reach 203411 := rs (se 1 (by rfl) ⟨152558, by rfl⟩) R305117
theorem R137929 : Reach 137929 := rs (se 2 (by rfl) ⟨51723, by rfl⟩) R103447
theorem R203705 : Reach 203705 := rs (se 2 (by rfl) ⟨76389, by rfl⟩) R152779
theorem R433163 : Reach 433163 := rs (se 1 (by rfl) ⟨324872, by rfl⟩) R649745
theorem R433181 : Reach 433181 := rs (se 3 (by rfl) ⟨81221, by rfl⟩) R162443
theorem R269513 : Reach 269513 := rs (se 2 (by rfl) ⟨101067, by rfl⟩) R202135
theorem R138631 : Reach 138631 := rs (se 1 (by rfl) ⟨103973, by rfl⟩) R207947
theorem R400787 : Reach 400787 := rs (se 1 (by rfl) ⟨300590, by rfl⟩) R601181
theorem R5283427 : Reach 5283427 := rs (se 1 (by rfl) ⟨3962570, by rfl⟩) R7925141
theorem R204403 : Reach 204403 := rs (se 1 (by rfl) ⟨153302, by rfl⟩) R306605
theorem R204545 : Reach 204545 := rs (se 2 (by rfl) ⟨76704, by rfl⟩) R153409
theorem R466721 : Reach 466721 := rs (se 2 (by rfl) ⟨175020, by rfl⟩) R350041
theorem R532261 : Reach 532261 := rs (se 4 (by rfl) ⟨49899, by rfl⟩) R99799
theorem R270215 : Reach 270215 := rs (se 1 (by rfl) ⟨202661, by rfl⟩) R405323
theorem R139279 : Reach 139279 := rs (se 1 (by rfl) ⟨104459, by rfl⟩) R208919
theorem R893015 : Reach 893015 := rs (se 1 (by rfl) ⟨669761, by rfl⟩) R1339523
theorem R925829 : Reach 925829 := rs (se 4 (by rfl) ⟨86796, by rfl⟩) R173593
theorem R205001 : Reach 205001 := rs (se 2 (by rfl) ⟨76875, by rfl⟩) R153751
theorem R3449033 : Reach 3449033 := rs (se 2 (by rfl) ⟨1293387, by rfl⟩) R2586775
theorem R270593 : Reach 270593 := rs (se 2 (by rfl) ⟨101472, by rfl⟩) R202945
theorem R303659 : Reach 303659 := rs (se 1 (by rfl) ⟨227744, by rfl⟩) R455489
theorem R205355 : Reach 205355 := rs (se 1 (by rfl) ⟨154016, by rfl⟩) R308033
theorem R139819 : Reach 139819 := rs (se 1 (by rfl) ⟨104864, by rfl⟩) R209729
theorem R139961 : Reach 139961 := rs (se 2 (by rfl) ⟨52485, by rfl⟩) R104971
theorem R861131 : Reach 861131 := rs (se 1 (by rfl) ⟨645848, by rfl⟩) R1291697
theorem R271403 : Reach 271403 := rs (se 1 (by rfl) ⟨203552, by rfl⟩) R407105
theorem R697517 : Reach 697517 := rs (se 3 (by rfl) ⟨130784, by rfl⟩) R261569
theorem R206233 : Reach 206233 := rs (se 2 (by rfl) ⟨77337, by rfl⟩) R154675
theorem R206347 : Reach 206347 := rs (se 1 (by rfl) ⟨154760, by rfl⟩) R309521
theorem R206489 : Reach 206489 := rs (se 2 (by rfl) ⟨77433, by rfl⟩) R154867
theorem R206651 : Reach 206651 := rs (se 1 (by rfl) ⟨154988, by rfl⟩) R309977
theorem R239419 : Reach 239419 := rs (se 1 (by rfl) ⟨179564, by rfl⟩) R359129
theorem R469111 : Reach 469111 := rs (se 1 (by rfl) ⟨351833, by rfl⟩) R703667
theorem R206995 : Reach 206995 := rs (se 1 (by rfl) ⟨155246, by rfl⟩) R310493
theorem R207137 : Reach 207137 := rs (se 2 (by rfl) ⟨77676, by rfl⟩) R155353
theorem R141601 : Reach 141601 := rs (se 2 (by rfl) ⟨53100, by rfl⟩) R106201
theorem R272699 : Reach 272699 := rs (se 1 (by rfl) ⟨204524, by rfl⟩) R409049
theorem R403865 : Reach 403865 := rs (se 2 (by rfl) ⟨151449, by rfl⟩) R302899
theorem R862649 : Reach 862649 := rs (se 2 (by rfl) ⟨323493, by rfl⟩) R646987
theorem R895607 : Reach 895607 := rs (se 1 (by rfl) ⟨671705, by rfl⟩) R1343411
theorem R273185 : Reach 273185 := rs (se 2 (by rfl) ⟨102444, by rfl⟩) R204889
theorem R208129 : Reach 208129 := rs (se 2 (by rfl) ⟨78048, by rfl⟩) R156097
theorem R273779 : Reach 273779 := rs (se 1 (by rfl) ⟨205334, by rfl⟩) R410669
theorem R470387 : Reach 470387 := rs (se 1 (by rfl) ⟨352790, by rfl⟩) R705581
theorem R1420753 : Reach 1420753 := rs (se 2 (by rfl) ⟨532782, by rfl⟩) R1065565
theorem R601667 : Reach 601667 := rs (se 1 (by rfl) ⟨451250, by rfl⟩) R902501
theorem R1027889 : Reach 1027889 := rs (se 2 (by rfl) ⟨385458, by rfl⟩) R770917
theorem R470843 : Reach 470843 := rs (se 1 (by rfl) ⟨353132, by rfl⟩) R706265
theorem R208727 : Reach 208727 := rs (se 1 (by rfl) ⟨156545, by rfl⟩) R313091
theorem R307091 : Reach 307091 := rs (se 1 (by rfl) ⟨230318, by rfl⟩) R460637
theorem R110521 : Reach 110521 := rs (se 2 (by rfl) ⟨41445, by rfl⟩) R82891
theorem R208939 : Reach 208939 := rs (se 1 (by rfl) ⟨156704, by rfl⟩) R313409
theorem R209081 : Reach 209081 := rs (se 2 (by rfl) ⟨78405, by rfl⟩) R156811
theorem R3322259 : Reach 3322259 := rs (se 1 (by rfl) ⟨2491694, by rfl⟩) R4983389
theorem R635435 : Reach 635435 := rs (se 1 (by rfl) ⟨476576, by rfl⟩) R953153
theorem R471845 : Reach 471845 := rs (se 4 (by rfl) ⟨44235, by rfl⟩) R88471
theorem R406457 : Reach 406457 := rs (se 2 (by rfl) ⟨152421, by rfl⟩) R304843
theorem R210073 : Reach 210073 := rs (se 2 (by rfl) ⟨78777, by rfl⟩) R157555
theorem R472301 : Reach 472301 := rs (se 3 (by rfl) ⟨88556, by rfl⟩) R177113
theorem R79163 : Reach 79163 := rs (se 1 (by rfl) ⟨59372, by rfl⟩) R118745
theorem R210235 : Reach 210235 := rs (se 1 (by rfl) ⟨157676, by rfl⟩) R315353
theorem R79239 : Reach 79239 := rs (se 1 (by rfl) ⟨59429, by rfl⟩) R118859
theorem R79247 : Reach 79247 := rs (se 1 (by rfl) ⟨59435, by rfl⟩) R118871
theorem R79291 : Reach 79291 := rs (se 1 (by rfl) ⟨59468, by rfl⟩) R118937
theorem R210377 : Reach 210377 := rs (se 2 (by rfl) ⟨78891, by rfl⟩) R157783
theorem R79367 : Reach 79367 := rs (se 1 (by rfl) ⟨59525, by rfl⟩) R119051
theorem R79375 : Reach 79375 := rs (se 1 (by rfl) ⟨59531, by rfl⟩) R119063
theorem R79419 : Reach 79419 := rs (se 1 (by rfl) ⟨59564, by rfl⟩) R119129
theorem R79495 : Reach 79495 := rs (se 1 (by rfl) ⟨59621, by rfl⟩) R119243
theorem R79503 : Reach 79503 := rs (se 1 (by rfl) ⟨59627, by rfl⟩) R119255
theorem R112313 : Reach 112313 := rs (se 2 (by rfl) ⟨42117, by rfl⟩) R84235
theorem R79547 : Reach 79547 := rs (se 1 (by rfl) ⟨59660, by rfl⟩) R119321
theorem R79623 : Reach 79623 := rs (se 1 (by rfl) ⟨59717, by rfl⟩) R119435
theorem R79631 : Reach 79631 := rs (se 1 (by rfl) ⟨59723, by rfl⟩) R119447
theorem R79675 : Reach 79675 := rs (se 1 (by rfl) ⟨59756, by rfl⟩) R119513
theorem R178055 : Reach 178055 := rs (se 1 (by rfl) ⟨133541, by rfl⟩) R267083
theorem R79751 : Reach 79751 := rs (se 1 (by rfl) ⟨59813, by rfl⟩) R119627
theorem R79759 : Reach 79759 := rs (se 1 (by rfl) ⟨59819, by rfl⟩) R119639
theorem R276371 : Reach 276371 := rs (se 1 (by rfl) ⟨207278, by rfl⟩) R414557
theorem R472985 : Reach 472985 := rs (se 2 (by rfl) ⟨177369, by rfl⟩) R354739
theorem R79803 : Reach 79803 := rs (se 1 (by rfl) ⟨59852, by rfl⟩) R119705
theorem R79879 : Reach 79879 := rs (se 1 (by rfl) ⟨59909, by rfl⟩) R119819
theorem R79887 : Reach 79887 := rs (se 1 (by rfl) ⟨59915, by rfl⟩) R119831
theorem R112699 : Reach 112699 := rs (se 1 (by rfl) ⟨84524, by rfl⟩) R169049
theorem R178235 : Reach 178235 := rs (se 1 (by rfl) ⟨133676, by rfl⟩) R267353
theorem R79931 : Reach 79931 := rs (se 1 (by rfl) ⟨59948, by rfl⟩) R119897
theorem R80007 : Reach 80007 := rs (se 1 (by rfl) ⟨60005, by rfl⟩) R120011
theorem R80015 : Reach 80015 := rs (se 1 (by rfl) ⟨60011, by rfl⟩) R120023
theorem R178361 : Reach 178361 := rs (se 2 (by rfl) ⟨66885, by rfl⟩) R133771
theorem R80059 : Reach 80059 := rs (se 1 (by rfl) ⟨60044, by rfl⟩) R120089
theorem R407753 : Reach 407753 := rs (se 2 (by rfl) ⟨152907, by rfl⟩) R305815
theorem R80135 : Reach 80135 := rs (se 1 (by rfl) ⟨60101, by rfl⟩) R120203
theorem R80143 : Reach 80143 := rs (se 1 (by rfl) ⟨60107, by rfl⟩) R120215
theorem R80187 : Reach 80187 := rs (se 1 (by rfl) ⟨60140, by rfl⟩) R120281
theorem R80263 : Reach 80263 := rs (se 1 (by rfl) ⟨60197, by rfl⟩) R120395
theorem R80271 : Reach 80271 := rs (se 1 (by rfl) ⟨60203, by rfl⟩) R120407
theorem R309689 : Reach 309689 := rs (se 2 (by rfl) ⟨116133, by rfl⟩) R232267
theorem R80315 : Reach 80315 := rs (se 1 (by rfl) ⟨60236, by rfl⟩) R120473
theorem R80391 : Reach 80391 := rs (se 1 (by rfl) ⟨60293, by rfl⟩) R120587
theorem R342539 : Reach 342539 := rs (se 1 (by rfl) ⟨256904, by rfl⟩) R513809
theorem R178703 : Reach 178703 := rs (se 1 (by rfl) ⟨134027, by rfl⟩) R268055
theorem R80399 : Reach 80399 := rs (se 1 (by rfl) ⟨60299, by rfl⟩) R120599
theorem R178721 : Reach 178721 := rs (se 2 (by rfl) ⟨67020, by rfl⟩) R134041
theorem R80443 : Reach 80443 := rs (se 1 (by rfl) ⟨60332, by rfl⟩) R120665
theorem R80519 : Reach 80519 := rs (se 1 (by rfl) ⟨60389, by rfl⟩) R120779
theorem R80527 : Reach 80527 := rs (se 1 (by rfl) ⟨60395, by rfl⟩) R120791
theorem R80571 : Reach 80571 := rs (se 1 (by rfl) ⟨60428, by rfl⟩) R120857
theorem R80647 : Reach 80647 := rs (se 1 (by rfl) ⟨60485, by rfl⟩) R120971
theorem R80655 : Reach 80655 := rs (se 1 (by rfl) ⟨60491, by rfl⟩) R120983
theorem R441139 : Reach 441139 := rs (se 1 (by rfl) ⟨330854, by rfl⟩) R661709
theorem R80699 : Reach 80699 := rs (se 1 (by rfl) ⟨60524, by rfl⟩) R121049
theorem R179063 : Reach 179063 := rs (se 1 (by rfl) ⟨134297, by rfl⟩) R268595
theorem R80775 : Reach 80775 := rs (se 1 (by rfl) ⟨60581, by rfl⟩) R121163
theorem R80783 : Reach 80783 := rs (se 1 (by rfl) ⟨60587, by rfl⟩) R121175
theorem R80827 : Reach 80827 := rs (se 1 (by rfl) ⟨60620, by rfl⟩) R121241
theorem R80903 : Reach 80903 := rs (se 1 (by rfl) ⟨60677, by rfl⟩) R121355
theorem R80911 : Reach 80911 := rs (se 1 (by rfl) ⟨60683, by rfl⟩) R121367
theorem R179243 : Reach 179243 := rs (se 1 (by rfl) ⟨134432, by rfl⟩) R268865
theorem R80955 : Reach 80955 := rs (se 1 (by rfl) ⟨60716, by rfl⟩) R121433
theorem R81031 : Reach 81031 := rs (se 1 (by rfl) ⟨60773, by rfl⟩) R121547
theorem R81039 : Reach 81039 := rs (se 1 (by rfl) ⟨60779, by rfl⟩) R121559
theorem R81083 : Reach 81083 := rs (se 1 (by rfl) ⟨60812, by rfl⟩) R121625
theorem R81159 : Reach 81159 := rs (se 1 (by rfl) ⟨60869, by rfl⟩) R121739
theorem R81167 : Reach 81167 := rs (se 1 (by rfl) ⟨60875, by rfl⟩) R121751
theorem R277775 : Reach 277775 := rs (se 1 (by rfl) ⟨208331, by rfl⟩) R416663
theorem R277793 : Reach 277793 := rs (se 2 (by rfl) ⟨104172, by rfl⟩) R208345
theorem R81211 : Reach 81211 := rs (se 1 (by rfl) ⟨60908, by rfl⟩) R121817
theorem R81287 : Reach 81287 := rs (se 1 (by rfl) ⟨60965, by rfl⟩) R121931
theorem R81295 : Reach 81295 := rs (se 1 (by rfl) ⟨60971, by rfl⟩) R121943
theorem R310675 : Reach 310675 := rs (se 1 (by rfl) ⟨233006, by rfl⟩) R466013
theorem R179603 : Reach 179603 := rs (se 1 (by rfl) ⟨134702, by rfl⟩) R269405
theorem R81339 : Reach 81339 := rs (se 1 (by rfl) ⟨61004, by rfl⟩) R122009
theorem R179657 : Reach 179657 := rs (se 2 (by rfl) ⟨67371, by rfl⟩) R134743
theorem R81415 : Reach 81415 := rs (se 1 (by rfl) ⟨61061, by rfl⟩) R122123
theorem R81423 : Reach 81423 := rs (se 1 (by rfl) ⟨61067, by rfl⟩) R122135
theorem R278045 : Reach 278045 := rs (se 3 (by rfl) ⟨52133, by rfl⟩) R104267
theorem R81467 : Reach 81467 := rs (se 1 (by rfl) ⟨61100, by rfl⟩) R122201
theorem R114311 : Reach 114311 := rs (se 1 (by rfl) ⟨85733, by rfl⟩) R171467
theorem R81543 : Reach 81543 := rs (se 1 (by rfl) ⟨61157, by rfl⟩) R122315
theorem R81551 : Reach 81551 := rs (se 1 (by rfl) ⟨61163, by rfl⟩) R122327
theorem R81595 : Reach 81595 := rs (se 1 (by rfl) ⟨61196, by rfl⟩) R122393
theorem R81671 : Reach 81671 := rs (se 1 (by rfl) ⟨61253, by rfl⟩) R122507
theorem R81679 : Reach 81679 := rs (se 1 (by rfl) ⟨61259, by rfl⟩) R122519
theorem R81723 : Reach 81723 := rs (se 1 (by rfl) ⟨61292, by rfl⟩) R122585
theorem R606041 : Reach 606041 := rs (se 2 (by rfl) ⟨227265, by rfl⟩) R454531
theorem R81799 : Reach 81799 := rs (se 1 (by rfl) ⟨61349, by rfl⟩) R122699
theorem R81807 : Reach 81807 := rs (se 1 (by rfl) ⟨61355, by rfl⟩) R122711
theorem R376721 : Reach 376721 := rs (se 2 (by rfl) ⟨141270, by rfl⟩) R282541
theorem R769945 : Reach 769945 := rs (se 2 (by rfl) ⟨288729, by rfl⟩) R577459
theorem R81851 : Reach 81851 := rs (se 1 (by rfl) ⟨61388, by rfl⟩) R122777
theorem R81927 : Reach 81927 := rs (se 1 (by rfl) ⟨61445, by rfl⟩) R122891
theorem R81935 : Reach 81935 := rs (se 1 (by rfl) ⟨61451, by rfl⟩) R122903
theorem R81979 : Reach 81979 := rs (se 1 (by rfl) ⟨61484, by rfl⟩) R122969
theorem R180359 : Reach 180359 := rs (se 1 (by rfl) ⟨135269, by rfl⟩) R270539
theorem R82055 : Reach 82055 := rs (se 1 (by rfl) ⟨61541, by rfl⟩) R123083
theorem R82063 : Reach 82063 := rs (se 1 (by rfl) ⟨61547, by rfl⟩) R123095
theorem R82107 : Reach 82107 := rs (se 1 (by rfl) ⟨61580, by rfl⟩) R123161
theorem R82183 : Reach 82183 := rs (se 1 (by rfl) ⟨61637, by rfl⟩) R123275
theorem R82191 : Reach 82191 := rs (se 1 (by rfl) ⟨61643, by rfl⟩) R123287
theorem R180539 : Reach 180539 := rs (se 1 (by rfl) ⟨135404, by rfl⟩) R270809
theorem R82235 : Reach 82235 := rs (se 1 (by rfl) ⟨61676, by rfl⟩) R123353
theorem R82311 : Reach 82311 := rs (se 1 (by rfl) ⟨61733, by rfl⟩) R123467
theorem R82319 : Reach 82319 := rs (se 1 (by rfl) ⟨61739, by rfl⟩) R123479
theorem R180665 : Reach 180665 := rs (se 2 (by rfl) ⟨67749, by rfl⟩) R135499
theorem R82363 : Reach 82363 := rs (se 1 (by rfl) ⟨61772, by rfl⟩) R123545
theorem R82439 : Reach 82439 := rs (se 1 (by rfl) ⟨61829, by rfl⟩) R123659
theorem R82447 : Reach 82447 := rs (se 1 (by rfl) ⟨61835, by rfl⟩) R123671
theorem R213563 : Reach 213563 := rs (se 1 (by rfl) ⟨160172, by rfl⟩) R320345
theorem R82491 : Reach 82491 := rs (se 1 (by rfl) ⟨61868, by rfl⟩) R123737
theorem R115273 : Reach 115273 := rs (se 2 (by rfl) ⟨43227, by rfl⟩) R86455
theorem R82567 : Reach 82567 := rs (se 1 (by rfl) ⟨61925, by rfl⟩) R123851
theorem R82575 : Reach 82575 := rs (se 1 (by rfl) ⟨61931, by rfl⟩) R123863
theorem R934577 : Reach 934577 := rs (se 2 (by rfl) ⟨350466, by rfl⟩) R700933
theorem R82619 : Reach 82619 := rs (se 1 (by rfl) ⟨61964, by rfl⟩) R123929
theorem R82695 : Reach 82695 := rs (se 1 (by rfl) ⟨62021, by rfl⟩) R124043
theorem R181007 : Reach 181007 := rs (se 1 (by rfl) ⟨135755, by rfl⟩) R271511
theorem R82703 : Reach 82703 := rs (se 1 (by rfl) ⟨62027, by rfl⟩) R124055
theorem R181025 : Reach 181025 := rs (se 2 (by rfl) ⟨67884, by rfl⟩) R135769
theorem R607013 : Reach 607013 := rs (se 4 (by rfl) ⟨56907, by rfl⟩) R113815
theorem R82747 : Reach 82747 := rs (se 1 (by rfl) ⟨62060, by rfl⟩) R124121
theorem R508787 : Reach 508787 := rs (se 1 (by rfl) ⟨381590, by rfl⟩) R763181
theorem R82823 : Reach 82823 := rs (se 1 (by rfl) ⟨62117, by rfl⟩) R124235
theorem R82831 : Reach 82831 := rs (se 1 (by rfl) ⟨62123, by rfl⟩) R124247
theorem R279449 : Reach 279449 := rs (se 2 (by rfl) ⟨104793, by rfl⟩) R209587
theorem R82875 : Reach 82875 := rs (se 1 (by rfl) ⟨62156, by rfl⟩) R124313
theorem R3195875 : Reach 3195875 := rs (se 1 (by rfl) ⟨2396906, by rfl⟩) R4793813
theorem R82951 : Reach 82951 := rs (se 1 (by rfl) ⟨62213, by rfl⟩) R124427
theorem R312331 : Reach 312331 := rs (se 1 (by rfl) ⟨234248, by rfl⟩) R468497
theorem R82959 : Reach 82959 := rs (se 1 (by rfl) ⟨62219, by rfl⟩) R124439
theorem R115769 : Reach 115769 := rs (se 2 (by rfl) ⟨43413, by rfl⟩) R86827
theorem R83003 : Reach 83003 := rs (se 1 (by rfl) ⟨62252, by rfl⟩) R124505
theorem R312407 : Reach 312407 := rs (se 1 (by rfl) ⟨234305, by rfl⟩) R468611
theorem R181367 : Reach 181367 := rs (se 1 (by rfl) ⟨136025, by rfl⟩) R272051
theorem R83079 : Reach 83079 := rs (se 1 (by rfl) ⟨62309, by rfl⟩) R124619
theorem R83087 : Reach 83087 := rs (se 1 (by rfl) ⟨62315, by rfl⟩) R124631
theorem R181547 : Reach 181547 := rs (se 1 (by rfl) ⟨136160, by rfl⟩) R272321
theorem R312893 : Reach 312893 := rs (se 3 (by rfl) ⟨58667, by rfl⟩) R117335
theorem R345667 : Reach 345667 := rs (se 1 (by rfl) ⟨259250, by rfl⟩) R518501
theorem R280151 : Reach 280151 := rs (se 1 (by rfl) ⟨210113, by rfl⟩) R420227
theorem R181907 : Reach 181907 := rs (se 1 (by rfl) ⟨136430, by rfl⟩) R272861
theorem R181961 : Reach 181961 := rs (se 2 (by rfl) ⟨68235, by rfl⟩) R136471
theorem R345991 : Reach 345991 := rs (se 1 (by rfl) ⟨259493, by rfl⟩) R518987
theorem R378769 : Reach 378769 := rs (se 2 (by rfl) ⟨142038, by rfl⟩) R284077
theorem R116743 : Reach 116743 := rs (se 1 (by rfl) ⟨87557, by rfl⟩) R175115
theorem R280637 : Reach 280637 := rs (se 3 (by rfl) ⟨52619, by rfl⟩) R105239
theorem R379073 : Reach 379073 := rs (se 2 (by rfl) ⟨142152, by rfl⟩) R284305
theorem R936251 : Reach 936251 := rs (se 1 (by rfl) ⟨702188, by rfl⟩) R1404377
theorem R182663 : Reach 182663 := rs (se 1 (by rfl) ⟨136997, by rfl⟩) R273995
theorem R182843 : Reach 182843 := rs (se 1 (by rfl) ⟨137132, by rfl⟩) R274265
theorem R182969 : Reach 182969 := rs (se 2 (by rfl) ⟨68613, by rfl⟩) R137227
theorem R346913 : Reach 346913 := rs (se 2 (by rfl) ⟨130092, by rfl⟩) R260185
theorem R281377 : Reach 281377 := rs (se 2 (by rfl) ⟨105516, by rfl⟩) R211033
theorem R183311 : Reach 183311 := rs (se 1 (by rfl) ⟨137483, by rfl⟩) R274967
theorem R183329 : Reach 183329 := rs (se 2 (by rfl) ⟨68748, by rfl⟩) R137497
theorem R183671 : Reach 183671 := rs (se 1 (by rfl) ⟨137753, by rfl⟩) R275507
theorem R118201 : Reach 118201 := rs (se 2 (by rfl) ⟨44325, by rfl⟩) R88651
theorem R151055 : Reach 151055 := rs (se 1 (by rfl) ⟨113291, by rfl⟩) R226583
theorem R183851 : Reach 183851 := rs (se 1 (by rfl) ⟨137888, by rfl⟩) R275777
theorem R380477 : Reach 380477 := rs (se 3 (by rfl) ⟨71339, by rfl⟩) R142679
theorem R249601 : Reach 249601 := rs (se 2 (by rfl) ⟨93600, by rfl⟩) R187201
theorem R479009 : Reach 479009 := rs (se 2 (by rfl) ⟨179628, by rfl⟩) R359257
theorem R413585 : Reach 413585 := rs (se 2 (by rfl) ⟨155094, by rfl⟩) R310189
theorem R184211 : Reach 184211 := rs (se 1 (by rfl) ⟨138158, by rfl⟩) R276317
theorem R118715 : Reach 118715 := rs (se 1 (by rfl) ⟨89036, by rfl⟩) R178073
theorem R184265 : Reach 184265 := rs (se 2 (by rfl) ⟨69099, by rfl⟩) R138199
theorem R118775 : Reach 118775 := rs (se 1 (by rfl) ⟨89081, by rfl⟩) R178163
theorem R118799 : Reach 118799 := rs (se 1 (by rfl) ⟨89099, by rfl⟩) R178199
theorem R118841 : Reach 118841 := rs (se 2 (by rfl) ⟨44565, by rfl⟩) R89131
theorem R1986677 : Reach 1986677 := rs (se 5 (by rfl) ⟨93125, by rfl⟩) R186251
theorem R118919 : Reach 118919 := rs (se 1 (by rfl) ⟨89189, by rfl⟩) R178379
theorem R118955 : Reach 118955 := rs (se 1 (by rfl) ⟨89216, by rfl⟩) R178433
theorem R118985 : Reach 118985 := rs (se 2 (by rfl) ⟨44619, by rfl⟩) R89239
theorem R905417 : Reach 905417 := rs (se 2 (by rfl) ⟨339531, by rfl⟩) R679063
theorem R119099 : Reach 119099 := rs (se 1 (by rfl) ⟨89324, by rfl⟩) R178649
theorem R119159 : Reach 119159 := rs (se 1 (by rfl) ⟨89369, by rfl⟩) R178739
theorem R119183 : Reach 119183 := rs (se 1 (by rfl) ⟨89387, by rfl⟩) R178775
theorem R119225 : Reach 119225 := rs (se 2 (by rfl) ⟨44709, by rfl⟩) R89419
theorem R512477 : Reach 512477 := rs (se 3 (by rfl) ⟨96089, by rfl⟩) R192179
theorem R119303 : Reach 119303 := rs (se 1 (by rfl) ⟨89477, by rfl⟩) R178955
theorem R119339 : Reach 119339 := rs (se 1 (by rfl) ⟨89504, by rfl⟩) R179009
theorem R119369 : Reach 119369 := rs (se 2 (by rfl) ⟨44763, by rfl⟩) R89527
theorem R184967 : Reach 184967 := rs (se 1 (by rfl) ⟨138725, by rfl⟩) R277451
theorem R119483 : Reach 119483 := rs (se 1 (by rfl) ⟨89612, by rfl⟩) R179225
theorem R119543 : Reach 119543 := rs (se 1 (by rfl) ⟨89657, by rfl⟩) R179315
theorem R119567 : Reach 119567 := rs (se 1 (by rfl) ⟨89675, by rfl⟩) R179351
theorem R119609 : Reach 119609 := rs (se 2 (by rfl) ⟨44853, by rfl⟩) R89707
theorem R185147 : Reach 185147 := rs (se 1 (by rfl) ⟨138860, by rfl⟩) R277721
theorem R119687 : Reach 119687 := rs (se 1 (by rfl) ⟨89765, by rfl⟩) R179531
theorem R119723 : Reach 119723 := rs (se 1 (by rfl) ⟨89792, by rfl⟩) R179585
theorem R185273 : Reach 185273 := rs (se 2 (by rfl) ⟨69477, by rfl⟩) R138955
theorem R119753 : Reach 119753 := rs (se 2 (by rfl) ⟨44907, by rfl⟩) R89815
theorem R119867 : Reach 119867 := rs (se 1 (by rfl) ⟨89900, by rfl⟩) R179801
theorem R119927 : Reach 119927 := rs (se 1 (by rfl) ⟨89945, by rfl⟩) R179891
theorem R152695 : Reach 152695 := rs (se 1 (by rfl) ⟨114521, by rfl⟩) R229043
theorem R119951 : Reach 119951 := rs (se 1 (by rfl) ⟨89963, by rfl⟩) R179927
theorem R119993 : Reach 119993 := rs (se 2 (by rfl) ⟨44997, by rfl⟩) R89995
theorem R120071 : Reach 120071 := rs (se 1 (by rfl) ⟨90053, by rfl⟩) R180107
theorem R185615 : Reach 185615 := rs (se 1 (by rfl) ⟨139211, by rfl⟩) R278423
theorem R185633 : Reach 185633 := rs (se 2 (by rfl) ⟨69612, by rfl⟩) R139225
theorem R120107 : Reach 120107 := rs (se 1 (by rfl) ⟨90080, by rfl⟩) R180161
theorem R120137 : Reach 120137 := rs (se 2 (by rfl) ⟨45051, by rfl⟩) R90103
theorem R120251 : Reach 120251 := rs (se 1 (by rfl) ⟨90188, by rfl⟩) R180377
theorem R120311 : Reach 120311 := rs (se 1 (by rfl) ⟨90233, by rfl⟩) R180467
theorem R382475 : Reach 382475 := rs (se 1 (by rfl) ⟨286856, by rfl⟩) R573713
theorem R120335 : Reach 120335 := rs (se 1 (by rfl) ⟨90251, by rfl⟩) R180503
theorem R120377 : Reach 120377 := rs (se 2 (by rfl) ⟨45141, by rfl⟩) R90283
theorem R185975 : Reach 185975 := rs (se 1 (by rfl) ⟨139481, by rfl⟩) R278963
theorem R120455 : Reach 120455 := rs (se 1 (by rfl) ⟨90341, by rfl⟩) R180683
theorem R120491 : Reach 120491 := rs (se 1 (by rfl) ⟨90368, by rfl⟩) R180737
theorem R120521 : Reach 120521 := rs (se 2 (by rfl) ⟨45195, by rfl⟩) R90391
theorem R186155 : Reach 186155 := rs (se 1 (by rfl) ⟨139616, by rfl⟩) R279233
theorem R120635 : Reach 120635 := rs (se 1 (by rfl) ⟨90476, by rfl⟩) R180953
theorem R120695 : Reach 120695 := rs (se 1 (by rfl) ⟨90521, by rfl⟩) R181043
theorem R120719 : Reach 120719 := rs (se 1 (by rfl) ⟨90539, by rfl⟩) R181079
theorem R120761 : Reach 120761 := rs (se 2 (by rfl) ⟨45285, by rfl⟩) R90571
theorem R415691 : Reach 415691 := rs (se 1 (by rfl) ⟨311768, by rfl⟩) R623537
theorem R120839 : Reach 120839 := rs (se 1 (by rfl) ⟨90629, by rfl⟩) R181259
theorem R120875 : Reach 120875 := rs (se 1 (by rfl) ⟨90656, by rfl⟩) R181313
theorem R120905 : Reach 120905 := rs (se 2 (by rfl) ⟨45339, by rfl⟩) R90679
theorem R186515 : Reach 186515 := rs (se 1 (by rfl) ⟨139886, by rfl⟩) R279773
theorem R121019 : Reach 121019 := rs (se 1 (by rfl) ⟨90764, by rfl⟩) R181529
theorem R186569 : Reach 186569 := rs (se 2 (by rfl) ⟨69963, by rfl⟩) R139927
theorem R121079 : Reach 121079 := rs (se 1 (by rfl) ⟨90809, by rfl⟩) R181619
theorem R121103 : Reach 121103 := rs (se 1 (by rfl) ⟨90827, by rfl⟩) R181655
theorem R416015 : Reach 416015 := rs (se 1 (by rfl) ⟨312011, by rfl⟩) R624023
theorem R121145 : Reach 121145 := rs (se 2 (by rfl) ⟨45429, by rfl⟩) R90859
theorem R121223 : Reach 121223 := rs (se 1 (by rfl) ⟨90917, by rfl⟩) R181835
theorem R121259 : Reach 121259 := rs (se 1 (by rfl) ⟨90944, by rfl⟩) R181889
theorem R121289 : Reach 121289 := rs (se 2 (by rfl) ⟨45483, by rfl⟩) R90967
theorem R1530353 : Reach 1530353 := rs (se 2 (by rfl) ⟨573882, by rfl⟩) R1147765
theorem R121403 : Reach 121403 := rs (se 1 (by rfl) ⟨91052, by rfl⟩) R182105
theorem R121463 : Reach 121463 := rs (se 1 (by rfl) ⟨91097, by rfl⟩) R182195
theorem R121487 : Reach 121487 := rs (se 1 (by rfl) ⟨91115, by rfl⟩) R182231
theorem R121529 : Reach 121529 := rs (se 2 (by rfl) ⟨45573, by rfl⟩) R91147
theorem R121607 : Reach 121607 := rs (se 1 (by rfl) ⟨91205, by rfl⟩) R182411
theorem R2644751 : Reach 2644751 := rs (se 1 (by rfl) ⟨1983563, by rfl⟩) R3967127
theorem R121643 : Reach 121643 := rs (se 1 (by rfl) ⟨91232, by rfl⟩) R182465
theorem R121673 : Reach 121673 := rs (se 2 (by rfl) ⟨45627, by rfl⟩) R91255
theorem R154487 : Reach 154487 := rs (se 1 (by rfl) ⟨115865, by rfl⟩) R231731
theorem R2579363 : Reach 2579363 := rs (se 1 (by rfl) ⟨1934522, by rfl⟩) R3869045
theorem R121787 : Reach 121787 := rs (se 1 (by rfl) ⟨91340, by rfl⟩) R182681
theorem R121847 : Reach 121847 := rs (se 1 (by rfl) ⟨91385, by rfl⟩) R182771
theorem R89095 : Reach 89095 := rs (se 1 (by rfl) ⟨66821, by rfl⟩) R133643
theorem R121871 : Reach 121871 := rs (se 1 (by rfl) ⟨91403, by rfl⟩) R182807
theorem R154639 : Reach 154639 := rs (se 1 (by rfl) ⟨115979, by rfl⟩) R231959
theorem R908333 : Reach 908333 := rs (se 3 (by rfl) ⟨170312, by rfl⟩) R340625
theorem R121913 : Reach 121913 := rs (se 2 (by rfl) ⟨45717, by rfl⟩) R91435
theorem R121991 : Reach 121991 := rs (se 1 (by rfl) ⟨91493, by rfl⟩) R182987
theorem R122027 : Reach 122027 := rs (se 1 (by rfl) ⟨91520, by rfl⟩) R183041
theorem R89275 : Reach 89275 := rs (se 1 (by rfl) ⟨66956, by rfl⟩) R133913
theorem R122057 : Reach 122057 := rs (se 2 (by rfl) ⟨45771, by rfl⟩) R91543
theorem R7625933 : Reach 7625933 := rs (se 3 (by rfl) ⟨1429862, by rfl⟩) R2859725
theorem R122171 : Reach 122171 := rs (se 1 (by rfl) ⟨91628, by rfl⟩) R183257
theorem R122231 : Reach 122231 := rs (se 1 (by rfl) ⟨91673, by rfl⟩) R183347
theorem R122255 : Reach 122255 := rs (se 1 (by rfl) ⟨91691, by rfl⟩) R183383
theorem R155027 : Reach 155027 := rs (se 1 (by rfl) ⟨116270, by rfl⟩) R232541
theorem R122297 : Reach 122297 := rs (se 2 (by rfl) ⟨45861, by rfl⟩) R91723
theorem R613817 : Reach 613817 := rs (se 2 (by rfl) ⟨230181, by rfl⟩) R460363
theorem R351697 : Reach 351697 := rs (se 2 (by rfl) ⟨131886, by rfl⟩) R263773
theorem R122375 : Reach 122375 := rs (se 1 (by rfl) ⟨91781, by rfl⟩) R183563
theorem R122411 : Reach 122411 := rs (se 1 (by rfl) ⟨91808, by rfl⟩) R183617
theorem R122441 : Reach 122441 := rs (se 2 (by rfl) ⟨45915, by rfl⟩) R91831
theorem R89743 : Reach 89743 := rs (se 1 (by rfl) ⟨67307, by rfl⟩) R134615
theorem R122539 : Reach 122539 := rs (se 1 (by rfl) ⟨91904, by rfl⟩) R183809
theorem R122555 : Reach 122555 := rs (se 1 (by rfl) ⟨91916, by rfl⟩) R183833
theorem R417473 : Reach 417473 := rs (se 2 (by rfl) ⟨156552, by rfl⟩) R313105
theorem R122615 : Reach 122615 := rs (se 1 (by rfl) ⟨91961, by rfl⟩) R183923
theorem R122639 : Reach 122639 := rs (se 1 (by rfl) ⟨91979, by rfl⟩) R183959
theorem R122681 : Reach 122681 := rs (se 2 (by rfl) ⟨46005, by rfl⟩) R92011
theorem R122759 : Reach 122759 := rs (se 1 (by rfl) ⟨92069, by rfl⟩) R184139
theorem R122795 : Reach 122795 := rs (se 1 (by rfl) ⟨92096, by rfl⟩) R184193
theorem R122825 : Reach 122825 := rs (se 2 (by rfl) ⟨46059, by rfl⟩) R92119
theorem R122939 : Reach 122939 := rs (se 1 (by rfl) ⟨92204, by rfl⟩) R184409
theorem R122953 : Reach 122953 := rs (se 2 (by rfl) ⟨46107, by rfl⟩) R92215
theorem R122999 : Reach 122999 := rs (se 1 (by rfl) ⟨92249, by rfl⟩) R184499
theorem R90247 : Reach 90247 := rs (se 1 (by rfl) ⟨67685, by rfl⟩) R135371
theorem R123023 : Reach 123023 := rs (se 1 (by rfl) ⟨92267, by rfl⟩) R184535
theorem R516269 : Reach 516269 := rs (se 3 (by rfl) ⟨96800, by rfl⟩) R193601
theorem R123065 : Reach 123065 := rs (se 2 (by rfl) ⟨46149, by rfl⟩) R92299
theorem R123143 : Reach 123143 := rs (se 1 (by rfl) ⟨92357, by rfl⟩) R184715
theorem R942353 : Reach 942353 := rs (se 2 (by rfl) ⟨353382, by rfl⟩) R706765
theorem R123179 : Reach 123179 := rs (se 1 (by rfl) ⟨92384, by rfl⟩) R184769
theorem R90427 : Reach 90427 := rs (se 1 (by rfl) ⟨67820, by rfl⟩) R135641
theorem R123209 : Reach 123209 := rs (se 2 (by rfl) ⟨46203, by rfl⟩) R92407
theorem R123323 : Reach 123323 := rs (se 1 (by rfl) ⟨92492, by rfl⟩) R184985
theorem R123383 : Reach 123383 := rs (se 1 (by rfl) ⟨92537, by rfl⟩) R185075
theorem R123407 : Reach 123407 := rs (se 1 (by rfl) ⟨92555, by rfl⟩) R185111
theorem R451115 : Reach 451115 := rs (se 1 (by rfl) ⟨338336, by rfl⟩) R676673
theorem R582187 : Reach 582187 := rs (se 1 (by rfl) ⟨436640, by rfl⟩) R873281
theorem R123449 : Reach 123449 := rs (se 2 (by rfl) ⟨46293, by rfl⟩) R92587
theorem R221831 : Reach 221831 := rs (se 1 (by rfl) ⟨166373, by rfl⟩) R332747
theorem R123527 : Reach 123527 := rs (se 1 (by rfl) ⟨92645, by rfl⟩) R185291
theorem R123563 : Reach 123563 := rs (se 1 (by rfl) ⟨92672, by rfl⟩) R185345
theorem R975539 : Reach 975539 := rs (se 1 (by rfl) ⟨731654, by rfl⟩) R1463309
theorem R123593 : Reach 123593 := rs (se 2 (by rfl) ⟨46347, by rfl⟩) R92695
theorem R90895 : Reach 90895 := rs (se 1 (by rfl) ⟨68171, by rfl⟩) R136343
theorem R156431 : Reach 156431 := rs (se 1 (by rfl) ⟨117323, by rfl⟩) R234647
theorem R123707 : Reach 123707 := rs (se 1 (by rfl) ⟨92780, by rfl⟩) R185561
theorem R123767 : Reach 123767 := rs (se 1 (by rfl) ⟨92825, by rfl⟩) R185651
theorem R123791 : Reach 123791 := rs (se 1 (by rfl) ⟨92843, by rfl⟩) R185687
theorem R123833 : Reach 123833 := rs (se 2 (by rfl) ⟨46437, by rfl⟩) R92875
theorem R418769 : Reach 418769 := rs (se 2 (by rfl) ⟨157038, by rfl⟩) R314077
theorem R123911 : Reach 123911 := rs (se 1 (by rfl) ⟨92933, by rfl⟩) R185867
theorem R123947 : Reach 123947 := rs (se 1 (by rfl) ⟨92960, by rfl⟩) R185921
theorem R123977 : Reach 123977 := rs (se 2 (by rfl) ⟨46491, by rfl⟩) R92983
theorem R681047 : Reach 681047 := rs (se 1 (by rfl) ⟨510785, by rfl⟩) R1021571
theorem R124091 : Reach 124091 := rs (se 1 (by rfl) ⟨93068, by rfl⟩) R186137
theorem R287981 : Reach 287981 := rs (se 3 (by rfl) ⟨53996, by rfl⟩) R107993
theorem R124151 : Reach 124151 := rs (se 1 (by rfl) ⟨93113, by rfl⟩) R186227
theorem R91399 : Reach 91399 := rs (se 1 (by rfl) ⟨68549, by rfl⟩) R137099
theorem R124175 : Reach 124175 := rs (se 1 (by rfl) ⟨93131, by rfl⟩) R186263
theorem R156971 : Reach 156971 := rs (se 1 (by rfl) ⟨117728, by rfl⟩) R235457
theorem R124217 : Reach 124217 := rs (se 2 (by rfl) ⟨46581, by rfl⟩) R93163
theorem R222551 : Reach 222551 := rs (se 1 (by rfl) ⟨166913, by rfl⟩) R333827
theorem R3433859 : Reach 3433859 := rs (se 1 (by rfl) ⟨2575394, by rfl⟩) R5150789
theorem R124295 : Reach 124295 := rs (se 1 (by rfl) ⟨93221, by rfl⟩) R186443
theorem R124331 : Reach 124331 := rs (se 1 (by rfl) ⟨93248, by rfl⟩) R186497
theorem R91579 : Reach 91579 := rs (se 1 (by rfl) ⟨68684, by rfl⟩) R137369
theorem R124361 : Reach 124361 := rs (se 2 (by rfl) ⟨46635, by rfl⟩) R93271
theorem R124475 : Reach 124475 := rs (se 1 (by rfl) ⟨93356, by rfl⟩) R186713
theorem R124535 : Reach 124535 := rs (se 1 (by rfl) ⟨93401, by rfl⟩) R186803
theorem R124559 : Reach 124559 := rs (se 1 (by rfl) ⟨93419, by rfl⟩) R186839
theorem R124601 : Reach 124601 := rs (se 2 (by rfl) ⟨46725, by rfl⟩) R93451
theorem R124679 : Reach 124679 := rs (se 1 (by rfl) ⟨93509, by rfl⟩) R187019
theorem R92047 : Reach 92047 := rs (se 1 (by rfl) ⟨69035, by rfl⟩) R138071
theorem R1042379 : Reach 1042379 := rs (se 1 (by rfl) ⟨781784, by rfl⟩) R1563569
theorem R452573 : Reach 452573 := rs (se 3 (by rfl) ⟨84857, by rfl⟩) R169715
theorem R256289 : Reach 256289 := rs (se 2 (by rfl) ⟨96108, by rfl⟩) R192217
theorem R92551 : Reach 92551 := rs (se 1 (by rfl) ⟨69413, by rfl⟩) R138827
theorem R453073 : Reach 453073 := rs (se 2 (by rfl) ⟨169902, by rfl⟩) R339805
theorem R92731 : Reach 92731 := rs (se 1 (by rfl) ⟨69548, by rfl⟩) R139097
theorem R224029 : Reach 224029 := rs (se 3 (by rfl) ⟨42005, by rfl⟩) R84011
theorem R289595 : Reach 289595 := rs (se 1 (by rfl) ⟨217196, by rfl⟩) R434393
theorem R93199 : Reach 93199 := rs (se 1 (by rfl) ⟨69899, by rfl⟩) R139799
theorem R421613 : Reach 421613 := rs (se 3 (by rfl) ⟨79052, by rfl⟩) R158105
theorem R290575 : Reach 290575 := rs (se 1 (by rfl) ⟨217931, by rfl⟩) R435863
theorem R421841 : Reach 421841 := rs (se 2 (by rfl) ⟨158190, by rfl⟩) R316381
theorem R258059 : Reach 258059 := rs (se 1 (by rfl) ⟨193544, by rfl⟩) R387089
theorem R455057 : Reach 455057 := rs (se 2 (by rfl) ⟨170646, by rfl⟩) R341293
theorem R1340023 : Reach 1340023 := rs (se 1 (by rfl) ⟨1005017, by rfl⟩) R2010035
theorem R684773 : Reach 684773 := rs (se 4 (by rfl) ⟨64197, by rfl⟩) R128395
theorem R226081 : Reach 226081 := rs (se 2 (by rfl) ⟨84780, by rfl⟩) R169561
theorem R1766549 : Reach 1766549 := rs (se 6 (by rfl) ⟨41403, by rfl⟩) R82807
theorem R128299 : Reach 128299 := rs (se 1 (by rfl) ⟨96224, by rfl⟩) R192449
theorem R128555 : Reach 128555 := rs (se 1 (by rfl) ⟨96416, by rfl⟩) R192833
theorem R194183 : Reach 194183 := rs (se 1 (by rfl) ⟨145637, by rfl⟩) R291275
theorem R358145 : Reach 358145 := rs (se 2 (by rfl) ⟨134304, by rfl⟩) R268609
theorem R194363 : Reach 194363 := rs (se 1 (by rfl) ⟨145772, by rfl⟩) R291545
theorem R227357 : Reach 227357 := rs (se 3 (by rfl) ⟨42629, by rfl⟩) R85259
theorem R489665 : Reach 489665 := rs (se 2 (by rfl) ⟨183624, by rfl⟩) R367249
theorem R981229 : Reach 981229 := rs (se 3 (by rfl) ⟨183980, by rfl⟩) R367961
theorem R227585 : Reach 227585 := rs (se 2 (by rfl) ⟨85344, by rfl⟩) R170689
theorem R391475 : Reach 391475 := rs (se 1 (by rfl) ⟨293606, by rfl⟩) R587213
theorem R227927 : Reach 227927 := rs (se 1 (by rfl) ⟨170945, by rfl⟩) R341891
theorem R228041 : Reach 228041 := rs (se 2 (by rfl) ⟨85515, by rfl⟩) R171031
theorem R391969 : Reach 391969 := rs (se 2 (by rfl) ⟨146988, by rfl⟩) R293977
theorem R228413 : Reach 228413 := rs (se 3 (by rfl) ⟨42827, by rfl⟩) R85655
theorem R261377 : Reach 261377 := rs (se 2 (by rfl) ⟨98016, by rfl⟩) R196033
theorem R195851 : Reach 195851 := rs (se 1 (by rfl) ⟨146888, by rfl⟩) R293777
theorem R163475 : Reach 163475 := rs (se 1 (by rfl) ⟨122606, by rfl⟩) R245213
theorem R98219 : Reach 98219 := rs (se 1 (by rfl) ⟨73664, by rfl⟩) R147329
theorem R163937 : Reach 163937 := rs (se 2 (by rfl) ⟨61476, by rfl⟩) R122953
theorem R131195 : Reach 131195 := rs (se 1 (by rfl) ⟨98396, by rfl⟩) R196793
theorem R262543 : Reach 262543 := rs (se 1 (by rfl) ⟨196907, by rfl⟩) R393815
theorem R131471 : Reach 131471 := rs (se 1 (by rfl) ⟨98603, by rfl⟩) R197207
theorem R623051 : Reach 623051 := rs (se 1 (by rfl) ⟨467288, by rfl⟩) R934577
theorem R2228795 : Reach 2228795 := rs (se 1 (by rfl) ⟨1671596, by rfl⟩) R3343193
theorem R2130583 : Reach 2130583 := rs (se 1 (by rfl) ⟨1597937, by rfl⟩) R3195875
theorem R394739 : Reach 394739 := rs (se 1 (by rfl) ⟨296054, by rfl⟩) R592109
theorem R624167 : Reach 624167 := rs (se 1 (by rfl) ⟨468125, by rfl⟩) R936251
theorem R198283 : Reach 198283 := rs (se 1 (by rfl) ⟨148712, by rfl⟩) R297425
theorem R231275 : Reach 231275 := rs (se 1 (by rfl) ⟨173456, by rfl⟩) R346913
theorem R460889 : Reach 460889 := rs (se 2 (by rfl) ⟨172833, by rfl⟩) R345667
theorem R100703 : Reach 100703 := rs (se 1 (by rfl) ⟨75527, by rfl⟩) R151055
theorem R788939 : Reach 788939 := rs (se 1 (by rfl) ⟨591704, by rfl⟩) R1183409
theorem R461321 : Reach 461321 := rs (se 2 (by rfl) ⟨172995, by rfl⟩) R345991
theorem R2296349 : Reach 2296349 := rs (se 3 (by rfl) ⟨430565, by rfl⟩) R861131
theorem R133879 : Reach 133879 := rs (se 1 (by rfl) ⟨100409, by rfl⟩) R200819
theorem R625481 : Reach 625481 := rs (se 2 (by rfl) ⟨234555, by rfl⟩) R469111
theorem R134075 : Reach 134075 := rs (se 1 (by rfl) ⟨100556, by rfl⟩) R201113
theorem R429029 : Reach 429029 := rs (se 4 (by rfl) ⟨40221, by rfl⟩) R80443
theorem R134183 : Reach 134183 := rs (se 1 (by rfl) ⟨100637, by rfl⟩) R201275
theorem R1510595 : Reach 1510595 := rs (se 1 (by rfl) ⟨1132946, by rfl⟩) R2265893
theorem R134473 : Reach 134473 := rs (se 2 (by rfl) ⟨50427, by rfl⟩) R100855
theorem R134507 : Reach 134507 := rs (se 1 (by rfl) ⟨100880, by rfl⟩) R201761
theorem R134905 : Reach 134905 := rs (se 2 (by rfl) ⟨50589, by rfl⟩) R101179
theorem R1314593 : Reach 1314593 := rs (se 2 (by rfl) ⟨492972, by rfl⟩) R985945
theorem R462779 : Reach 462779 := rs (se 1 (by rfl) ⟨347084, by rfl⟩) R694169
theorem R135175 : Reach 135175 := rs (se 1 (by rfl) ⟨101381, by rfl⟩) R202763
theorem R200951 : Reach 200951 := rs (se 1 (by rfl) ⟨150713, by rfl⟩) R301427
theorem R2101565 : Reach 2101565 := rs (se 3 (by rfl) ⟨394043, by rfl⟩) R788087
theorem R1020235 : Reach 1020235 := rs (se 1 (by rfl) ⟨765176, by rfl⟩) R1530353
theorem R135607 : Reach 135607 := rs (se 1 (by rfl) ⟨101705, by rfl⟩) R203411
theorem R299501 : Reach 299501 := rs (se 3 (by rfl) ⟨56156, by rfl⟩) R112313
theorem R135803 : Reach 135803 := rs (se 1 (by rfl) ⟨101852, by rfl⟩) R203705
theorem R5083955 : Reach 5083955 := rs (se 1 (by rfl) ⟨3812966, by rfl⟩) R7625933
theorem R267191 : Reach 267191 := rs (se 1 (by rfl) ⟨200393, by rfl⟩) R400787
theorem R103351 : Reach 103351 := rs (se 1 (by rfl) ⟨77513, by rfl⟩) R155027
theorem R332801 : Reach 332801 := rs (se 2 (by rfl) ⟨124800, by rfl⟩) R249601
theorem R136201 : Reach 136201 := rs (se 2 (by rfl) ⟨51075, by rfl⟩) R102151
theorem R136363 : Reach 136363 := rs (se 1 (by rfl) ⟨102272, by rfl⟩) R204545
theorem R595343 : Reach 595343 := rs (se 1 (by rfl) ⟨446507, by rfl⟩) R893015
theorem R2299355 : Reach 2299355 := rs (se 1 (by rfl) ⟨1724516, by rfl⟩) R3449033
theorem R136667 : Reach 136667 := rs (se 1 (by rfl) ⟨102500, by rfl⟩) R205001
theorem R267785 : Reach 267785 := rs (se 2 (by rfl) ⟨100419, by rfl⟩) R200839
theorem R628235 : Reach 628235 := rs (se 1 (by rfl) ⟨471176, by rfl⟩) R942353
theorem R136903 : Reach 136903 := rs (se 1 (by rfl) ⟨102677, by rfl⟩) R205355
theorem R300743 : Reach 300743 := rs (se 1 (by rfl) ⟨225557, by rfl⟩) R451115
theorem R202439 : Reach 202439 := rs (se 1 (by rfl) ⟨151829, by rfl⟩) R303659
theorem R137065 : Reach 137065 := rs (se 2 (by rfl) ⟨51399, by rfl⟩) R102799
theorem R465011 : Reach 465011 := rs (se 1 (by rfl) ⟨348758, by rfl⟩) R697517
theorem R104647 : Reach 104647 := rs (se 1 (by rfl) ⟨78485, by rfl⟩) R156971
theorem R268649 : Reach 268649 := rs (se 2 (by rfl) ⟨100743, by rfl⟩) R201487
theorem R301441 : Reach 301441 := rs (se 2 (by rfl) ⟨113040, by rfl⟩) R226081
theorem R137659 : Reach 137659 := rs (se 1 (by rfl) ⟨103244, by rfl⟩) R206489
theorem R137767 : Reach 137767 := rs (se 1 (by rfl) ⟨103325, by rfl⟩) R206651
theorem R694919 : Reach 694919 := rs (se 1 (by rfl) ⟨521189, by rfl⟩) R1042379
theorem R301715 : Reach 301715 := rs (se 1 (by rfl) ⟨226286, by rfl⟩) R452573
theorem R203593 : Reach 203593 := rs (se 2 (by rfl) ⟨76347, by rfl⟩) R152695
theorem R138091 : Reach 138091 := rs (se 1 (by rfl) ⟨103568, by rfl⟩) R207137
theorem R269243 : Reach 269243 := rs (se 1 (by rfl) ⟨201932, by rfl⟩) R403865
theorem R171065 : Reach 171065 := rs (se 2 (by rfl) ⟨64149, by rfl⟩) R128299
theorem R597071 : Reach 597071 := rs (se 1 (by rfl) ⟨447803, by rfl⟩) R895607
theorem R138809 : Reach 138809 := rs (se 2 (by rfl) ⟨52053, by rfl⟩) R104107
theorem R401111 : Reach 401111 := rs (se 1 (by rfl) ⟨300833, by rfl⟩) R601667
theorem R139151 : Reach 139151 := rs (se 1 (by rfl) ⟨104363, by rfl⟩) R208727
theorem R204727 : Reach 204727 := rs (se 1 (by rfl) ⟨153545, by rfl⟩) R307091
theorem R172039 : Reach 172039 := rs (se 1 (by rfl) ⟨129029, by rfl⟩) R258059
theorem R794701 : Reach 794701 := rs (se 3 (by rfl) ⟨149006, by rfl⟩) R298013
theorem R139387 : Reach 139387 := rs (se 1 (by rfl) ⟨104540, by rfl⟩) R209081
theorem R303371 : Reach 303371 := rs (se 1 (by rfl) ⟨227528, by rfl⟩) R455057
theorem R1188361 : Reach 1188361 := rs (se 2 (by rfl) ⟨445635, by rfl⟩) R891271
theorem R270971 : Reach 270971 := rs (se 1 (by rfl) ⟨203228, by rfl⟩) R406457
theorem R271133 : Reach 271133 := rs (se 3 (by rfl) ⟨50837, by rfl⟩) R101675
theorem R140251 : Reach 140251 := rs (se 1 (by rfl) ⟨105188, by rfl⟩) R210377
theorem R238763 : Reach 238763 := rs (se 1 (by rfl) ⟨179072, by rfl⟩) R358145
theorem R206185 : Reach 206185 := rs (se 2 (by rfl) ⟨77319, by rfl⟩) R154639
theorem R271835 : Reach 271835 := rs (se 1 (by rfl) ⟨203876, by rfl⟩) R407753
theorem R206459 : Reach 206459 := rs (se 1 (by rfl) ⟨154844, by rfl⟩) R309689
theorem R304829 : Reach 304829 := rs (se 3 (by rfl) ⟨57155, by rfl⟩) R114311
theorem R468929 : Reach 468929 := rs (se 2 (by rfl) ⟨175848, by rfl⟩) R351697
theorem R272537 : Reach 272537 := rs (se 2 (by rfl) ⟨102201, by rfl⟩) R204403
theorem R174251 : Reach 174251 := rs (se 1 (by rfl) ⟨130688, by rfl⟩) R261377
theorem R108793 : Reach 108793 := rs (se 2 (by rfl) ⟨40797, by rfl⟩) R81595
theorem R108983 : Reach 108983 := rs (se 1 (by rfl) ⟨81737, by rfl⟩) R163475
theorem R1026593 : Reach 1026593 := rs (se 2 (by rfl) ⟨384972, by rfl⟩) R769945
theorem R404027 : Reach 404027 := rs (se 1 (by rfl) ⟨303020, by rfl⟩) R606041
theorem R404675 : Reach 404675 := rs (se 1 (by rfl) ⟨303506, by rfl⟩) R607013
theorem R339191 : Reach 339191 := rs (se 1 (by rfl) ⟨254393, by rfl⟩) R508787
theorem R273725 : Reach 273725 := rs (se 3 (by rfl) ⟨51323, by rfl⟩) R102647
theorem R306575 : Reach 306575 := rs (se 1 (by rfl) ⟨229931, by rfl⟩) R459863
theorem R208271 : Reach 208271 := rs (se 1 (by rfl) ⟨156203, by rfl⟩) R312407
theorem R208595 : Reach 208595 := rs (se 1 (by rfl) ⟨156446, by rfl⟩) R312893
theorem R176033 : Reach 176033 := rs (se 2 (by rfl) ⟨66012, by rfl⟩) R132025
theorem R569501 : Reach 569501 := rs (se 3 (by rfl) ⟨106781, by rfl⟩) R213563
theorem R274589 : Reach 274589 := rs (se 3 (by rfl) ⟨51485, by rfl⟩) R102971
theorem R307745 : Reach 307745 := rs (se 2 (by rfl) ⟨115404, by rfl⟩) R230809
theorem R176737 : Reach 176737 := rs (se 2 (by rfl) ⟨66276, by rfl⟩) R132553
theorem R242315 : Reach 242315 := rs (se 1 (by rfl) ⟨181736, by rfl⟩) R363473
theorem R275129 : Reach 275129 := rs (se 2 (by rfl) ⟨103173, by rfl⟩) R206347
theorem R308063 : Reach 308063 := rs (se 1 (by rfl) ⟨231047, by rfl⟩) R462095
theorem R177079 : Reach 177079 := rs (se 1 (by rfl) ⟨132809, by rfl⟩) R265619
theorem R308231 : Reach 308231 := rs (se 1 (by rfl) ⟨231173, by rfl⟩) R462347
theorem R505025 : Reach 505025 := rs (se 2 (by rfl) ⟨189384, by rfl⟩) R378769
theorem R275723 : Reach 275723 := rs (se 1 (by rfl) ⟨206792, by rfl⟩) R413585
theorem R79143 : Reach 79143 := rs (se 1 (by rfl) ⟨59357, by rfl⟩) R118715
theorem R79183 : Reach 79183 := rs (se 1 (by rfl) ⟨59387, by rfl⟩) R118775
theorem R79199 : Reach 79199 := rs (se 1 (by rfl) ⟨59399, by rfl⟩) R118799
theorem R79227 : Reach 79227 := rs (se 1 (by rfl) ⟨59420, by rfl⟩) R118841
theorem R1324451 : Reach 1324451 := rs (se 1 (by rfl) ⟨993338, by rfl⟩) R1986677
theorem R79279 : Reach 79279 := rs (se 1 (by rfl) ⟨59459, by rfl⟩) R118919
theorem R79303 : Reach 79303 := rs (se 1 (by rfl) ⟨59477, by rfl⟩) R118955
theorem R79323 : Reach 79323 := rs (se 1 (by rfl) ⟨59492, by rfl⟩) R118985
theorem R603611 : Reach 603611 := rs (se 1 (by rfl) ⟨452708, by rfl⟩) R905417
theorem R308717 : Reach 308717 := rs (se 3 (by rfl) ⟨57884, by rfl⟩) R115769
theorem R275993 : Reach 275993 := rs (se 2 (by rfl) ⟨103497, by rfl⟩) R206995
theorem R79399 : Reach 79399 := rs (se 1 (by rfl) ⟨59549, by rfl⟩) R119099
theorem R79439 : Reach 79439 := rs (se 1 (by rfl) ⟨59579, by rfl⟩) R119159
theorem R79455 : Reach 79455 := rs (se 1 (by rfl) ⟨59591, by rfl⟩) R119183
theorem R79483 : Reach 79483 := rs (se 1 (by rfl) ⟨59612, by rfl⟩) R119225
theorem R341651 : Reach 341651 := rs (se 1 (by rfl) ⟨256238, by rfl⟩) R512477
theorem R79535 : Reach 79535 := rs (se 1 (by rfl) ⟨59651, by rfl⟩) R119303
theorem R79559 : Reach 79559 := rs (se 1 (by rfl) ⟨59669, by rfl⟩) R119339
theorem R79579 : Reach 79579 := rs (se 1 (by rfl) ⟨59684, by rfl⟩) R119369
theorem R79655 : Reach 79655 := rs (se 1 (by rfl) ⟨59741, by rfl⟩) R119483
theorem R309035 : Reach 309035 := rs (se 1 (by rfl) ⟨231776, by rfl⟩) R463553
theorem R79695 : Reach 79695 := rs (se 1 (by rfl) ⟨59771, by rfl⟩) R119543
theorem R79711 : Reach 79711 := rs (se 1 (by rfl) ⟨59783, by rfl⟩) R119567
theorem R79739 : Reach 79739 := rs (se 1 (by rfl) ⟨59804, by rfl⟩) R119609
theorem R79791 : Reach 79791 := rs (se 1 (by rfl) ⟨59843, by rfl⟩) R119687
theorem R604097 : Reach 604097 := rs (se 2 (by rfl) ⟨226536, by rfl⟩) R453073
theorem R79815 : Reach 79815 := rs (se 1 (by rfl) ⟨59861, by rfl⟩) R119723
theorem R79835 : Reach 79835 := rs (se 1 (by rfl) ⟨59876, by rfl⟩) R119753
theorem R79911 : Reach 79911 := rs (se 1 (by rfl) ⟨59933, by rfl⟩) R119867
theorem R79951 : Reach 79951 := rs (se 1 (by rfl) ⟨59963, by rfl⟩) R119927
theorem R79967 : Reach 79967 := rs (se 1 (by rfl) ⟨59975, by rfl⟩) R119951
theorem R79995 : Reach 79995 := rs (se 1 (by rfl) ⟨59996, by rfl⟩) R119993
theorem R80047 : Reach 80047 := rs (se 1 (by rfl) ⟨60035, by rfl⟩) R120071
theorem R80071 : Reach 80071 := rs (se 1 (by rfl) ⟨60053, by rfl⟩) R120107
theorem R80091 : Reach 80091 := rs (se 1 (by rfl) ⟨60068, by rfl⟩) R120137
theorem R80167 : Reach 80167 := rs (se 1 (by rfl) ⟨60125, by rfl⟩) R120251
theorem R571697 : Reach 571697 := rs (se 2 (by rfl) ⟨214386, by rfl⟩) R428773
theorem R80207 : Reach 80207 := rs (se 1 (by rfl) ⟨60155, by rfl⟩) R120311
theorem R80223 : Reach 80223 := rs (se 1 (by rfl) ⟨60167, by rfl⟩) R120335
theorem R80251 : Reach 80251 := rs (se 1 (by rfl) ⟨60188, by rfl⟩) R120377
theorem R80303 : Reach 80303 := rs (se 1 (by rfl) ⟨60227, by rfl⟩) R120455
theorem R80327 : Reach 80327 := rs (se 1 (by rfl) ⟨60245, by rfl⟩) R120491
theorem R80347 : Reach 80347 := rs (se 1 (by rfl) ⟨60260, by rfl⟩) R120521
theorem R80423 : Reach 80423 := rs (se 1 (by rfl) ⟨60317, by rfl⟩) R120635
theorem R80463 : Reach 80463 := rs (se 1 (by rfl) ⟨60347, by rfl⟩) R120695
theorem R80479 : Reach 80479 := rs (se 1 (by rfl) ⟨60359, by rfl⟩) R120719
theorem R178811 : Reach 178811 := rs (se 1 (by rfl) ⟨134108, by rfl⟩) R268217
theorem R80507 : Reach 80507 := rs (se 1 (by rfl) ⟨60380, by rfl⟩) R120761
theorem R277127 : Reach 277127 := rs (se 1 (by rfl) ⟨207845, by rfl⟩) R415691
theorem R80559 : Reach 80559 := rs (se 1 (by rfl) ⟨60419, by rfl⟩) R120839
theorem R277181 : Reach 277181 := rs (se 3 (by rfl) ⟨51971, by rfl⟩) R103943
theorem R80583 : Reach 80583 := rs (se 1 (by rfl) ⟨60437, by rfl⟩) R120875
theorem R80603 : Reach 80603 := rs (se 1 (by rfl) ⟨60452, by rfl⟩) R120905
theorem R178937 : Reach 178937 := rs (se 2 (by rfl) ⟨67101, by rfl⟩) R134203
theorem R80679 : Reach 80679 := rs (se 1 (by rfl) ⟨60509, by rfl⟩) R121019
theorem R1194821 : Reach 1194821 := rs (se 4 (by rfl) ⟨112014, by rfl⟩) R224029
theorem R80719 : Reach 80719 := rs (se 1 (by rfl) ⟨60539, by rfl⟩) R121079
theorem R80735 : Reach 80735 := rs (se 1 (by rfl) ⟨60551, by rfl⟩) R121103
theorem R277343 : Reach 277343 := rs (se 1 (by rfl) ⟨208007, by rfl⟩) R416015
theorem R80763 : Reach 80763 := rs (se 1 (by rfl) ⟨60572, by rfl⟩) R121145
theorem R80815 : Reach 80815 := rs (se 1 (by rfl) ⟨60611, by rfl⟩) R121223
theorem R80839 : Reach 80839 := rs (se 1 (by rfl) ⟨60629, by rfl⟩) R121259
theorem R80859 : Reach 80859 := rs (se 1 (by rfl) ⟨60644, by rfl⟩) R121289
theorem R277505 : Reach 277505 := rs (se 2 (by rfl) ⟨104064, by rfl⟩) R208129
theorem R179207 : Reach 179207 := rs (se 1 (by rfl) ⟨134405, by rfl⟩) R268811
theorem R80935 : Reach 80935 := rs (se 1 (by rfl) ⟨60701, by rfl⟩) R121403
theorem R179279 : Reach 179279 := rs (se 1 (by rfl) ⟨134459, by rfl⟩) R268919
theorem R80975 : Reach 80975 := rs (se 1 (by rfl) ⟨60731, by rfl⟩) R121463
theorem R80991 : Reach 80991 := rs (se 1 (by rfl) ⟨60743, by rfl⟩) R121487
theorem R81019 : Reach 81019 := rs (se 1 (by rfl) ⟨60764, by rfl⟩) R121529
theorem R81071 : Reach 81071 := rs (se 1 (by rfl) ⟨60803, by rfl⟩) R121607
theorem R81095 : Reach 81095 := rs (se 1 (by rfl) ⟨60821, by rfl⟩) R121643
theorem R81115 : Reach 81115 := rs (se 1 (by rfl) ⟨60836, by rfl⟩) R121673
theorem R1719575 : Reach 1719575 := rs (se 1 (by rfl) ⟨1289681, by rfl⟩) R2579363
theorem R81191 : Reach 81191 := rs (se 1 (by rfl) ⟨60893, by rfl⟩) R121787
theorem R81231 : Reach 81231 := rs (se 1 (by rfl) ⟨60923, by rfl⟩) R121847
theorem R81247 : Reach 81247 := rs (se 1 (by rfl) ⟨60935, by rfl⟩) R121871
theorem R605555 : Reach 605555 := rs (se 1 (by rfl) ⟨454166, by rfl⟩) R908333
theorem R81275 : Reach 81275 := rs (se 1 (by rfl) ⟨60956, by rfl⟩) R121913
theorem R81327 : Reach 81327 := rs (se 1 (by rfl) ⟨60995, by rfl⟩) R121991
theorem R81351 : Reach 81351 := rs (se 1 (by rfl) ⟨61013, by rfl⟩) R122027
theorem R179675 : Reach 179675 := rs (se 1 (by rfl) ⟨134756, by rfl⟩) R269513
theorem R81371 : Reach 81371 := rs (se 1 (by rfl) ⟨61028, by rfl⟩) R122057
theorem R81447 : Reach 81447 := rs (se 1 (by rfl) ⟨61085, by rfl⟩) R122171
theorem R81487 : Reach 81487 := rs (se 1 (by rfl) ⟨61115, by rfl⟩) R122231
theorem R81503 : Reach 81503 := rs (se 1 (by rfl) ⟨61127, by rfl⟩) R122255
theorem R409211 : Reach 409211 := rs (se 1 (by rfl) ⟨306908, by rfl⟩) R613817
theorem R81531 : Reach 81531 := rs (se 1 (by rfl) ⟨61148, by rfl⟩) R122297
theorem R81583 : Reach 81583 := rs (se 1 (by rfl) ⟨61187, by rfl⟩) R122375
theorem R81607 : Reach 81607 := rs (se 1 (by rfl) ⟨61205, by rfl⟩) R122411
theorem R81627 : Reach 81627 := rs (se 1 (by rfl) ⟨61220, by rfl⟩) R122441
theorem R81703 : Reach 81703 := rs (se 1 (by rfl) ⟨61277, by rfl⟩) R122555
theorem R278315 : Reach 278315 := rs (se 1 (by rfl) ⟨208736, by rfl⟩) R417473
theorem R81743 : Reach 81743 := rs (se 1 (by rfl) ⟨61307, by rfl⟩) R122615
theorem R81759 : Reach 81759 := rs (se 1 (by rfl) ⟨61319, by rfl⟩) R122639
theorem R311147 : Reach 311147 := rs (se 1 (by rfl) ⟨233360, by rfl⟩) R466721
theorem R81787 : Reach 81787 := rs (se 1 (by rfl) ⟨61340, by rfl⟩) R122681
theorem R147361 : Reach 147361 := rs (se 2 (by rfl) ⟨55260, by rfl⟩) R110521
theorem R180143 : Reach 180143 := rs (se 1 (by rfl) ⟨135107, by rfl⟩) R270215
theorem R81839 : Reach 81839 := rs (se 1 (by rfl) ⟨61379, by rfl⟩) R122759
theorem R81863 : Reach 81863 := rs (se 1 (by rfl) ⟨61397, by rfl⟩) R122795
theorem R81883 : Reach 81883 := rs (se 1 (by rfl) ⟨61412, by rfl⟩) R122825
theorem R81959 : Reach 81959 := rs (se 1 (by rfl) ⟨61469, by rfl⟩) R122939
theorem R278585 : Reach 278585 := rs (se 2 (by rfl) ⟨104469, by rfl⟩) R208939
theorem R81999 : Reach 81999 := rs (se 1 (by rfl) ⟨61499, by rfl⟩) R122999
theorem R82015 : Reach 82015 := rs (se 1 (by rfl) ⟨61511, by rfl⟩) R123023
theorem R344179 : Reach 344179 := rs (se 1 (by rfl) ⟨258134, by rfl⟩) R516269
theorem R82043 : Reach 82043 := rs (se 1 (by rfl) ⟨61532, by rfl⟩) R123065
theorem R180395 : Reach 180395 := rs (se 1 (by rfl) ⟨135296, by rfl⟩) R270593
theorem R82095 : Reach 82095 := rs (se 1 (by rfl) ⟨61571, by rfl⟩) R123143
theorem R82119 : Reach 82119 := rs (se 1 (by rfl) ⟨61589, by rfl⟩) R123179
theorem R82139 : Reach 82139 := rs (se 1 (by rfl) ⟨61604, by rfl⟩) R123209
theorem R82215 : Reach 82215 := rs (se 1 (by rfl) ⟨61661, by rfl⟩) R123323
theorem R82255 : Reach 82255 := rs (se 1 (by rfl) ⟨61691, by rfl⟩) R123383
theorem R82271 : Reach 82271 := rs (se 1 (by rfl) ⟨61703, by rfl⟩) R123407
theorem R82299 : Reach 82299 := rs (se 1 (by rfl) ⟨61724, by rfl⟩) R123449
theorem R278909 : Reach 278909 := rs (se 3 (by rfl) ⟨52295, by rfl⟩) R104591
theorem R147887 : Reach 147887 := rs (se 1 (by rfl) ⟨110915, by rfl⟩) R221831
theorem R82351 : Reach 82351 := rs (se 1 (by rfl) ⟨61763, by rfl⟩) R123527
theorem R82375 : Reach 82375 := rs (se 1 (by rfl) ⟨61781, by rfl⟩) R123563
theorem R82395 : Reach 82395 := rs (se 1 (by rfl) ⟨61796, by rfl⟩) R123593
theorem R82471 : Reach 82471 := rs (se 1 (by rfl) ⟨61853, by rfl⟩) R123707
theorem R82511 : Reach 82511 := rs (se 1 (by rfl) ⟨61883, by rfl⟩) R123767
theorem R82527 : Reach 82527 := rs (se 1 (by rfl) ⟨61895, by rfl⟩) R123791
theorem R82555 : Reach 82555 := rs (se 1 (by rfl) ⟨61916, by rfl⟩) R123833
theorem R279179 : Reach 279179 := rs (se 1 (by rfl) ⟨209384, by rfl⟩) R418769
theorem R82607 : Reach 82607 := rs (se 1 (by rfl) ⟨61955, by rfl⟩) R123911
theorem R180935 : Reach 180935 := rs (se 1 (by rfl) ⟨135701, by rfl⟩) R271403
theorem R82631 : Reach 82631 := rs (se 1 (by rfl) ⟨61973, by rfl⟩) R123947
theorem R82651 : Reach 82651 := rs (se 1 (by rfl) ⟨61988, by rfl⟩) R123977
theorem R82727 : Reach 82727 := rs (se 1 (by rfl) ⟨62045, by rfl⟩) R124091
theorem R1786697 : Reach 1786697 := rs (se 2 (by rfl) ⟨670011, by rfl⟩) R1340023
theorem R82767 : Reach 82767 := rs (se 1 (by rfl) ⟨62075, by rfl⟩) R124151
theorem R82783 : Reach 82783 := rs (se 1 (by rfl) ⟨62087, by rfl⟩) R124175
theorem R82811 : Reach 82811 := rs (se 1 (by rfl) ⟨62108, by rfl⟩) R124217
theorem R148367 : Reach 148367 := rs (se 1 (by rfl) ⟨111275, by rfl⟩) R222551
theorem R82863 : Reach 82863 := rs (se 1 (by rfl) ⟨62147, by rfl⟩) R124295
theorem R82887 : Reach 82887 := rs (se 1 (by rfl) ⟨62165, by rfl⟩) R124331
theorem R82907 : Reach 82907 := rs (se 1 (by rfl) ⟨62180, by rfl⟩) R124361
theorem R82983 : Reach 82983 := rs (se 1 (by rfl) ⟨62237, by rfl⟩) R124475
theorem R83023 : Reach 83023 := rs (se 1 (by rfl) ⟨62267, by rfl⟩) R124535
theorem R83039 : Reach 83039 := rs (se 1 (by rfl) ⟨62279, by rfl⟩) R124559
theorem R83067 : Reach 83067 := rs (se 1 (by rfl) ⟨62300, by rfl⟩) R124601
theorem R83119 : Reach 83119 := rs (se 1 (by rfl) ⟨62339, by rfl⟩) R124679
theorem R280097 : Reach 280097 := rs (se 2 (by rfl) ⟨105036, by rfl⟩) R210073
theorem R181799 : Reach 181799 := rs (se 1 (by rfl) ⟨136349, by rfl⟩) R272699
theorem R575099 : Reach 575099 := rs (se 1 (by rfl) ⟨431324, by rfl⟩) R862649
theorem R280313 : Reach 280313 := rs (se 2 (by rfl) ⟨105117, by rfl⟩) R210235
theorem R182123 : Reach 182123 := rs (se 1 (by rfl) ⟨136592, by rfl⟩) R273185
theorem R182177 : Reach 182177 := rs (se 2 (by rfl) ⟨68316, by rfl⟩) R136633
theorem R1427381 : Reach 1427381 := rs (se 5 (by rfl) ⟨66908, by rfl⟩) R133817
theorem R313345 : Reach 313345 := rs (se 2 (by rfl) ⟨117504, by rfl⟩) R235009
theorem R1099909 : Reach 1099909 := rs (se 4 (by rfl) ⟨103116, by rfl⟩) R206233
theorem R772253 : Reach 772253 := rs (se 3 (by rfl) ⟨144797, by rfl⟩) R289595
theorem R182519 : Reach 182519 := rs (se 1 (by rfl) ⟨136889, by rfl⟩) R273779
theorem R313591 : Reach 313591 := rs (se 1 (by rfl) ⟨235193, by rfl⟩) R470387
theorem R411965 : Reach 411965 := rs (se 3 (by rfl) ⟨77243, by rfl⟩) R154487
theorem R281075 : Reach 281075 := rs (se 1 (by rfl) ⟨210806, by rfl⟩) R421613
theorem R313865 : Reach 313865 := rs (se 2 (by rfl) ⟨117699, by rfl⟩) R235399
theorem R313895 : Reach 313895 := rs (se 1 (by rfl) ⟨235421, by rfl⟩) R470843
theorem R281227 : Reach 281227 := rs (se 1 (by rfl) ⟨210920, by rfl⟩) R421841
theorem R150265 : Reach 150265 := rs (se 2 (by rfl) ⟨56349, by rfl⟩) R112699
theorem R183113 : Reach 183113 := rs (se 2 (by rfl) ⟨68667, by rfl⟩) R137335
theorem R2214839 : Reach 2214839 := rs (se 1 (by rfl) ⟨1661129, by rfl⟩) R3322259
theorem R314563 : Reach 314563 := rs (se 1 (by rfl) ⟨235922, by rfl⟩) R471845
theorem R314867 : Reach 314867 := rs (se 1 (by rfl) ⟨236150, by rfl⟩) R472301
theorem R183905 : Reach 183905 := rs (se 2 (by rfl) ⟨68964, by rfl⟩) R137929
theorem R85703 : Reach 85703 := rs (se 1 (by rfl) ⟨64277, by rfl⟩) R128555
theorem R118703 : Reach 118703 := rs (se 1 (by rfl) ⟨89027, by rfl⟩) R178055
theorem R184247 : Reach 184247 := rs (se 1 (by rfl) ⟨138185, by rfl⟩) R276371
theorem R315323 : Reach 315323 := rs (se 1 (by rfl) ⟨236492, by rfl⟩) R472985
theorem R118793 : Reach 118793 := rs (se 2 (by rfl) ⟨44547, by rfl⟩) R89095
theorem R151571 : Reach 151571 := rs (se 1 (by rfl) ⟨113678, by rfl⟩) R227357
theorem R118823 : Reach 118823 := rs (se 1 (by rfl) ⟨89117, by rfl⟩) R178235
theorem R118907 : Reach 118907 := rs (se 1 (by rfl) ⟨89180, by rfl⟩) R178361
theorem R151723 : Reach 151723 := rs (se 1 (by rfl) ⟨113792, by rfl⟩) R227585
theorem R119033 : Reach 119033 := rs (se 2 (by rfl) ⟨44637, by rfl⟩) R89275
theorem R119135 : Reach 119135 := rs (se 1 (by rfl) ⟨89351, by rfl⟩) R178703
theorem R119147 : Reach 119147 := rs (se 1 (by rfl) ⟨89360, by rfl⟩) R178721
theorem R151951 : Reach 151951 := rs (se 1 (by rfl) ⟨113963, by rfl⟩) R227927
theorem R152027 : Reach 152027 := rs (se 1 (by rfl) ⟨114020, by rfl⟩) R228041
theorem R184841 : Reach 184841 := rs (se 2 (by rfl) ⟨69315, by rfl⟩) R138631
theorem R414233 : Reach 414233 := rs (se 2 (by rfl) ⟨155337, by rfl⟩) R310675
theorem R119375 : Reach 119375 := rs (se 1 (by rfl) ⟨89531, by rfl⟩) R179063
theorem R119495 : Reach 119495 := rs (se 1 (by rfl) ⟨89621, by rfl⟩) R179243
theorem R152275 : Reach 152275 := rs (se 1 (by rfl) ⟨114206, by rfl⟩) R228413
theorem R185183 : Reach 185183 := rs (se 1 (by rfl) ⟨138887, by rfl⟩) R277775
theorem R119657 : Reach 119657 := rs (se 2 (by rfl) ⟨44871, by rfl⟩) R89743
theorem R185195 : Reach 185195 := rs (se 1 (by rfl) ⟨138896, by rfl⟩) R277793
theorem R119735 : Reach 119735 := rs (se 1 (by rfl) ⟨89801, by rfl⟩) R179603
theorem R119771 : Reach 119771 := rs (se 1 (by rfl) ⟨89828, by rfl⟩) R179657
theorem R185363 : Reach 185363 := rs (se 1 (by rfl) ⟨139022, by rfl⟩) R278045
theorem R709681 : Reach 709681 := rs (se 2 (by rfl) ⟨266130, by rfl⟩) R532261
theorem R251147 : Reach 251147 := rs (se 1 (by rfl) ⟨188360, by rfl⟩) R376721
theorem R185705 : Reach 185705 := rs (se 2 (by rfl) ⟨69639, by rfl⟩) R139279
theorem R120239 : Reach 120239 := rs (se 1 (by rfl) ⟨90179, by rfl⟩) R180359
theorem R120329 : Reach 120329 := rs (se 2 (by rfl) ⟨45123, by rfl⟩) R90247
theorem R120359 : Reach 120359 := rs (se 1 (by rfl) ⟨90269, by rfl⟩) R180539
theorem R120443 : Reach 120443 := rs (se 1 (by rfl) ⟨90332, by rfl⟩) R180665
theorem R120569 : Reach 120569 := rs (se 2 (by rfl) ⟨45213, by rfl⟩) R90427
theorem R120671 : Reach 120671 := rs (se 1 (by rfl) ⟨90503, by rfl⟩) R181007
theorem R120683 : Reach 120683 := rs (se 1 (by rfl) ⟨90512, by rfl⟩) R181025
theorem R186299 : Reach 186299 := rs (se 1 (by rfl) ⟨139724, by rfl⟩) R279449
theorem R612359 : Reach 612359 := rs (se 1 (by rfl) ⟨459269, by rfl⟩) R918539
theorem R776249 : Reach 776249 := rs (se 2 (by rfl) ⟨291093, by rfl⟩) R582187
theorem R186425 : Reach 186425 := rs (se 2 (by rfl) ⟨69909, by rfl⟩) R139819
theorem R120911 : Reach 120911 := rs (se 1 (by rfl) ⟨90683, by rfl⟩) R181367
theorem R350365 : Reach 350365 := rs (se 3 (by rfl) ⟨65693, by rfl⟩) R131387
theorem R121031 : Reach 121031 := rs (se 1 (by rfl) ⟨90773, by rfl⟩) R181547
theorem R121193 : Reach 121193 := rs (se 2 (by rfl) ⟨45447, by rfl⟩) R90895
theorem R186767 : Reach 186767 := rs (se 1 (by rfl) ⟨140075, by rfl⟩) R280151
theorem R121271 : Reach 121271 := rs (se 1 (by rfl) ⟨90953, by rfl⟩) R181907
theorem R121307 : Reach 121307 := rs (se 1 (by rfl) ⟨90980, by rfl⟩) R181961
theorem R612845 : Reach 612845 := rs (se 3 (by rfl) ⟨114908, by rfl⟩) R229817
theorem R416441 : Reach 416441 := rs (se 2 (by rfl) ⟨156165, by rfl⟩) R312331
theorem R187091 : Reach 187091 := rs (se 1 (by rfl) ⟨140318, by rfl⟩) R280637
theorem R252715 : Reach 252715 := rs (se 1 (by rfl) ⟨189536, by rfl⟩) R379073
theorem R121775 : Reach 121775 := rs (se 1 (by rfl) ⟨91331, by rfl⟩) R182663
theorem R121865 : Reach 121865 := rs (se 2 (by rfl) ⟨45699, by rfl⟩) R91399
theorem R121895 : Reach 121895 := rs (se 1 (by rfl) ⟨91421, by rfl⟩) R182843
theorem R89167 : Reach 89167 := rs (se 1 (by rfl) ⟨66875, by rfl⟩) R133751
theorem R121979 : Reach 121979 := rs (se 1 (by rfl) ⟨91484, by rfl⟩) R182969
theorem R122105 : Reach 122105 := rs (se 2 (by rfl) ⟨45789, by rfl⟩) R91579
theorem R122207 : Reach 122207 := rs (se 1 (by rfl) ⟨91655, by rfl⟩) R183311
theorem R122219 : Reach 122219 := rs (se 1 (by rfl) ⟨91664, by rfl⟩) R183329
theorem R417149 : Reach 417149 := rs (se 3 (by rfl) ⟨78215, by rfl⟩) R156431
theorem R89563 : Reach 89563 := rs (se 1 (by rfl) ⟨67172, by rfl⟩) R134345
theorem R122447 : Reach 122447 := rs (se 1 (by rfl) ⟨91835, by rfl⟩) R183671
theorem R122567 : Reach 122567 := rs (se 1 (by rfl) ⟨91925, by rfl⟩) R183851
theorem R253651 : Reach 253651 := rs (se 1 (by rfl) ⟨190238, by rfl⟩) R380477
theorem R122729 : Reach 122729 := rs (se 2 (by rfl) ⟨46023, by rfl⟩) R92047
theorem R319339 : Reach 319339 := rs (se 1 (by rfl) ⟨239504, by rfl⟩) R479009
theorem R221089 : Reach 221089 := rs (se 2 (by rfl) ⟨82908, by rfl⟩) R165817
theorem R90031 : Reach 90031 := rs (se 1 (by rfl) ⟨67523, by rfl⟩) R135047
theorem R122807 : Reach 122807 := rs (se 1 (by rfl) ⟨92105, by rfl⟩) R184211
theorem R155611 : Reach 155611 := rs (se 1 (by rfl) ⟨116708, by rfl⟩) R233417
theorem R122843 : Reach 122843 := rs (se 1 (by rfl) ⟨92132, by rfl⟩) R184265
theorem R155657 : Reach 155657 := rs (se 2 (by rfl) ⟨58371, by rfl⟩) R116743
theorem R352313 : Reach 352313 := rs (se 2 (by rfl) ⟨132117, by rfl⟩) R264235
theorem R90463 : Reach 90463 := rs (se 1 (by rfl) ⟨67847, by rfl⟩) R135695
theorem R155999 : Reach 155999 := rs (se 1 (by rfl) ⟨116999, by rfl⟩) R233999
theorem R188801 : Reach 188801 := rs (se 2 (by rfl) ⟨70800, by rfl⟩) R141601
theorem R614789 : Reach 614789 := rs (se 4 (by rfl) ⟨57636, by rfl⟩) R115273
theorem R123311 : Reach 123311 := rs (se 1 (by rfl) ⟨92483, by rfl⟩) R184967
theorem R123401 : Reach 123401 := rs (se 2 (by rfl) ⟨46275, by rfl⟩) R92551
theorem R123431 : Reach 123431 := rs (se 1 (by rfl) ⟨92573, by rfl⟩) R185147
theorem R123515 : Reach 123515 := rs (se 1 (by rfl) ⟨92636, by rfl⟩) R185273
theorem R90823 : Reach 90823 := rs (se 1 (by rfl) ⟨68117, by rfl⟩) R136235
theorem R123641 : Reach 123641 := rs (se 2 (by rfl) ⟨46365, by rfl⟩) R92731
theorem R123743 : Reach 123743 := rs (se 1 (by rfl) ⟨92807, by rfl⟩) R185615
theorem R615275 : Reach 615275 := rs (se 1 (by rfl) ⟨461456, by rfl⟩) R922913
theorem R123755 : Reach 123755 := rs (se 1 (by rfl) ⟨92816, by rfl⟩) R185633
theorem R254983 : Reach 254983 := rs (se 1 (by rfl) ⟨191237, by rfl⟩) R382475
theorem R123983 : Reach 123983 := rs (se 1 (by rfl) ⟨92987, by rfl⟩) R185975
theorem R124103 : Reach 124103 := rs (se 1 (by rfl) ⟨93077, by rfl⟩) R186155
theorem R124265 : Reach 124265 := rs (se 2 (by rfl) ⟨46599, by rfl⟩) R93199
theorem R124343 : Reach 124343 := rs (se 1 (by rfl) ⟨93257, by rfl⟩) R186515
theorem R157115 : Reach 157115 := rs (se 1 (by rfl) ⟨117836, by rfl⟩) R235673
theorem R124379 : Reach 124379 := rs (se 1 (by rfl) ⟨93284, by rfl⟩) R186569
theorem R1500677 : Reach 1500677 := rs (se 4 (by rfl) ⟨140688, by rfl⟩) R281377
theorem R91687 : Reach 91687 := rs (se 1 (by rfl) ⟨68765, by rfl⟩) R137531
theorem R1763167 : Reach 1763167 := rs (se 1 (by rfl) ⟨1322375, by rfl⟩) R2644751
theorem R157601 : Reach 157601 := rs (se 2 (by rfl) ⟨59100, by rfl⟩) R118201
theorem R1894337 : Reach 1894337 := rs (se 2 (by rfl) ⟨710376, by rfl⟩) R1420753
theorem R288775 : Reach 288775 := rs (se 1 (by rfl) ⟨216581, by rfl⟩) R433163
theorem R288787 : Reach 288787 := rs (se 1 (by rfl) ⟨216590, by rfl⟩) R433181
theorem R551069 : Reach 551069 := rs (se 3 (by rfl) ⟨103325, by rfl⟩) R206651
theorem R387433 : Reach 387433 := rs (se 2 (by rfl) ⟨145287, by rfl⟩) R290575
theorem R354689 : Reach 354689 := rs (se 2 (by rfl) ⟨133008, by rfl⟩) R266017
theorem R617219 : Reach 617219 := rs (se 1 (by rfl) ⟨462914, by rfl⟩) R925829
theorem R2190349 : Reach 2190349 := rs (se 3 (by rfl) ⟨410690, by rfl⟩) R821381
theorem R650359 : Reach 650359 := rs (se 1 (by rfl) ⟨487769, by rfl⟩) R975539
theorem R93307 : Reach 93307 := rs (se 1 (by rfl) ⟨69980, by rfl⟩) R139961
theorem R454031 : Reach 454031 := rs (se 1 (by rfl) ⟨340523, by rfl⟩) R681047
theorem R683437 : Reach 683437 := rs (se 3 (by rfl) ⟨128144, by rfl⟩) R256289
theorem R191987 : Reach 191987 := rs (se 1 (by rfl) ⟨143990, by rfl⟩) R287981
theorem R2289239 : Reach 2289239 := rs (se 1 (by rfl) ⟨1716929, by rfl⟩) R3433859
theorem R685259 : Reach 685259 := rs (se 1 (by rfl) ⟨513944, by rfl⟩) R1027889
theorem R1308305 : Reach 1308305 := rs (se 2 (by rfl) ⟨490614, by rfl⟩) R981229
theorem R325309 : Reach 325309 := rs (se 3 (by rfl) ⟨60995, by rfl⟩) R121991
theorem R423623 : Reach 423623 := rs (se 1 (by rfl) ⟨317717, by rfl⟩) R635435
theorem R456515 : Reach 456515 := rs (se 1 (by rfl) ⟨342386, by rfl⟩) R684773
theorem R620621 : Reach 620621 := rs (se 3 (by rfl) ⟨116366, by rfl⟩) R232733
theorem R1177699 : Reach 1177699 := rs (se 1 (by rfl) ⟨883274, by rfl⟩) R1766549
theorem R522625 : Reach 522625 := rs (se 2 (by rfl) ⟨195984, by rfl⟩) R391969
theorem R588185 : Reach 588185 := rs (se 2 (by rfl) ⟨220569, by rfl⟩) R441139
theorem R129455 : Reach 129455 := rs (se 1 (by rfl) ⟨97091, by rfl⟩) R194183
theorem R129575 : Reach 129575 := rs (se 1 (by rfl) ⟨97181, by rfl⟩) R194363
theorem R326443 : Reach 326443 := rs (se 1 (by rfl) ⟨244832, by rfl⟩) R489665
theorem R260983 : Reach 260983 := rs (se 1 (by rfl) ⟨195737, by rfl⟩) R391475
theorem R1276901 : Reach 1276901 := rs (se 4 (by rfl) ⟨119709, by rfl⟩) R239419
theorem R228359 : Reach 228359 := rs (se 1 (by rfl) ⟨171269, by rfl⟩) R342539
theorem R7044569 : Reach 7044569 := rs (se 2 (by rfl) ⟨2641713, by rfl⟩) R5283427
theorem R130567 : Reach 130567 := rs (se 1 (by rfl) ⟨97925, by rfl⟩) R195851
theorem R163385 : Reach 163385 := rs (se 2 (by rfl) ⟨61269, by rfl⟩) R122539
theorem R261917 : Reach 261917 := rs (se 3 (by rfl) ⟨49109, by rfl⟩) R98219
theorem R229385 : Reach 229385 := rs (se 2 (by rfl) ⟨86019, by rfl⟩) R172039
theorem R458905 : Reach 458905 := rs (se 2 (by rfl) ⟨172089, by rfl⟩) R344179
theorem R98591 : Reach 98591 := rs (se 1 (by rfl) ⟨73943, by rfl⟩) R147887
theorem R98911 : Reach 98911 := rs (se 1 (by rfl) ⟨74183, by rfl⟩) R148367
theorem R5604173 : Reach 5604173 := rs (se 3 (by rfl) ⟨1050782, by rfl⟩) R2101565
theorem R263159 : Reach 263159 := rs (se 1 (by rfl) ⟨197369, by rfl⟩) R394739
theorem R951587 : Reach 951587 := rs (se 1 (by rfl) ⟨713690, by rfl⟩) R1427381
theorem R525959 : Reach 525959 := rs (se 1 (by rfl) ⟨394469, by rfl⟩) R788939
theorem R1476559 : Reach 1476559 := rs (se 1 (by rfl) ⟨1107419, by rfl⟩) R2214839
theorem R264377 : Reach 264377 := rs (se 2 (by rfl) ⟨99141, by rfl⟩) R198283
theorem R133967 : Reach 133967 := rs (se 1 (by rfl) ⟨100475, by rfl⟩) R200951
theorem R101351 : Reach 101351 := rs (se 1 (by rfl) ⟨76013, by rfl⟩) R152027
theorem R199667 : Reach 199667 := rs (se 1 (by rfl) ⟨149750, by rfl⟩) R299501
theorem R167431 : Reach 167431 := rs (se 1 (by rfl) ⟨125573, by rfl⟩) R251147
theorem R396895 : Reach 396895 := rs (se 1 (by rfl) ⟨297671, by rfl⟩) R595343
theorem R200353 : Reach 200353 := rs (se 2 (by rfl) ⟨75132, by rfl⟩) R150265
theorem R200495 : Reach 200495 := rs (se 1 (by rfl) ⟨150371, by rfl⟩) R300743
theorem R134959 : Reach 134959 := rs (se 1 (by rfl) ⟨101219, by rfl⟩) R202439
theorem R2920465 : Reach 2920465 := rs (se 2 (by rfl) ⟨1095174, by rfl⟩) R2190349
theorem R463279 : Reach 463279 := rs (se 1 (by rfl) ⟨347459, by rfl⟩) R694919
theorem R201143 : Reach 201143 := rs (se 1 (by rfl) ⟨150857, by rfl⟩) R301715
theorem R398047 : Reach 398047 := rs (se 1 (by rfl) ⟨298535, by rfl⟩) R597071
theorem R267407 : Reach 267407 := rs (se 1 (by rfl) ⟨200555, by rfl⟩) R401111
theorem R103771 : Reach 103771 := rs (se 1 (by rfl) ⟨77828, by rfl⟩) R155657
theorem R234875 : Reach 234875 := rs (se 1 (by rfl) ⟨176156, by rfl⟩) R352313
theorem R202247 : Reach 202247 := rs (se 1 (by rfl) ⟨151685, by rfl⟩) R303371
theorem R202297 : Reach 202297 := rs (se 2 (by rfl) ⟨75861, by rfl⟩) R151723
theorem R103999 : Reach 103999 := rs (se 1 (by rfl) ⟨77999, by rfl⟩) R155999
theorem R202601 : Reach 202601 := rs (se 2 (by rfl) ⟨75975, by rfl⟩) R151951
theorem R235649 : Reach 235649 := rs (se 2 (by rfl) ⟨88368, by rfl⟩) R176737
theorem R268541 : Reach 268541 := rs (se 3 (by rfl) ⟨50351, by rfl⟩) R100703
theorem R203033 : Reach 203033 := rs (se 2 (by rfl) ⟨76137, by rfl⟩) R152275
theorem R104743 : Reach 104743 := rs (se 1 (by rfl) ⟨78557, by rfl⟩) R157115
theorem R137639 : Reach 137639 := rs (se 1 (by rfl) ⟨103229, by rfl⟩) R206459
theorem R203219 : Reach 203219 := rs (se 1 (by rfl) ⟨152414, by rfl⟩) R304829
theorem R137801 : Reach 137801 := rs (se 2 (by rfl) ⟨51675, by rfl⟩) R103351
theorem R236105 : Reach 236105 := rs (se 2 (by rfl) ⟨88539, by rfl⟩) R177079
theorem R105067 : Reach 105067 := rs (se 1 (by rfl) ⟨78800, by rfl⟩) R157601
theorem R367379 : Reach 367379 := rs (se 1 (by rfl) ⟨275534, by rfl⟩) R551069
theorem R236459 : Reach 236459 := rs (se 1 (by rfl) ⟨177344, by rfl⟩) R354689
theorem R269351 : Reach 269351 := rs (se 1 (by rfl) ⟨202013, by rfl⟩) R404027
theorem R269783 : Reach 269783 := rs (se 1 (by rfl) ⟨202337, by rfl⟩) R404675
theorem R433745 : Reach 433745 := rs (se 2 (by rfl) ⟨162654, by rfl⟩) R325309
theorem R302687 : Reach 302687 := rs (se 1 (by rfl) ⟨227015, by rfl⟩) R454031
theorem R204383 : Reach 204383 := rs (se 1 (by rfl) ⟨153287, by rfl⟩) R306575
theorem R138847 : Reach 138847 := rs (se 1 (by rfl) ⟨104135, by rfl⟩) R208271
theorem R139063 : Reach 139063 := rs (se 1 (by rfl) ⟨104297, by rfl⟩) R208595
theorem R467153 : Reach 467153 := rs (se 2 (by rfl) ⟨175182, by rfl⟩) R350365
theorem R139529 : Reach 139529 := rs (se 2 (by rfl) ⟨52323, by rfl⟩) R104647
theorem R205163 : Reach 205163 := rs (se 1 (by rfl) ⟨153872, by rfl⟩) R307745
theorem R401921 : Reach 401921 := rs (se 2 (by rfl) ⟨150720, by rfl⟩) R301441
theorem R696833 : Reach 696833 := rs (se 2 (by rfl) ⟨261312, by rfl⟩) R522625
theorem R205375 : Reach 205375 := rs (se 1 (by rfl) ⟨154031, by rfl⟩) R308063
theorem R205487 : Reach 205487 := rs (se 1 (by rfl) ⟨154115, by rfl⟩) R308231
theorem R336683 : Reach 336683 := rs (se 1 (by rfl) ⟨252512, by rfl⟩) R505025
theorem R402407 : Reach 402407 := rs (se 1 (by rfl) ⟨301805, by rfl⟩) R603611
theorem R205811 : Reach 205811 := rs (se 1 (by rfl) ⟨154358, by rfl⟩) R308717
theorem R435257 : Reach 435257 := rs (se 2 (by rfl) ⟨163221, by rfl⟩) R326443
theorem R336953 : Reach 336953 := rs (se 2 (by rfl) ⟨126357, by rfl⟩) R252715
theorem R271457 : Reach 271457 := rs (se 2 (by rfl) ⟨101796, by rfl⟩) R203593
theorem R206023 : Reach 206023 := rs (se 1 (by rfl) ⟨154517, by rfl⟩) R309035
theorem R304343 : Reach 304343 := rs (se 1 (by rfl) ⟨228257, by rfl⟩) R456515
theorem R402731 : Reach 402731 := rs (se 1 (by rfl) ⟨302048, by rfl⟩) R604097
theorem R796547 : Reach 796547 := rs (se 1 (by rfl) ⟨597410, by rfl⟩) R1194821
theorem R174089 : Reach 174089 := rs (se 2 (by rfl) ⟨65283, by rfl⟩) R130567
theorem R403703 : Reach 403703 := rs (se 1 (by rfl) ⟨302777, by rfl⟩) R605555
theorem R338201 : Reach 338201 := rs (se 2 (by rfl) ⟨126825, by rfl⟩) R253651
theorem R4696379 : Reach 4696379 := rs (se 1 (by rfl) ⟨3522284, by rfl⟩) R7044569
theorem R108923 : Reach 108923 := rs (se 1 (by rfl) ⟨81692, by rfl⟩) R163385
theorem R272807 : Reach 272807 := rs (se 1 (by rfl) ⟨204605, by rfl⟩) R409211
theorem R469421 : Reach 469421 := rs (se 3 (by rfl) ⟨88016, by rfl⟩) R176033
theorem R174611 : Reach 174611 := rs (se 1 (by rfl) ⟨130958, by rfl⟩) R261917
theorem R207431 : Reach 207431 := rs (se 1 (by rfl) ⟨155573, by rfl⟩) R311147
theorem R272969 : Reach 272969 := rs (se 2 (by rfl) ⟨102363, by rfl⟩) R204727
theorem R207481 : Reach 207481 := rs (se 2 (by rfl) ⟨77805, by rfl⟩) R155611
theorem R404189 : Reach 404189 := rs (se 3 (by rfl) ⟨75785, by rfl⟩) R151571
theorem R109291 : Reach 109291 := rs (se 1 (by rfl) ⟨81968, by rfl⟩) R163937
theorem R1059601 : Reach 1059601 := rs (se 2 (by rfl) ⟨397350, by rfl⟩) R794701
theorem R1485863 : Reach 1485863 := rs (se 1 (by rfl) ⟨1114397, by rfl⟩) R2228795
theorem R1191131 : Reach 1191131 := rs (se 1 (by rfl) ⟨893348, by rfl⟩) R1786697
theorem R1584481 : Reach 1584481 := rs (se 2 (by rfl) ⟨594180, by rfl⟩) R1188361
theorem R339977 : Reach 339977 := rs (se 2 (by rfl) ⟨127491, by rfl⟩) R254983
theorem R307259 : Reach 307259 := rs (se 1 (by rfl) ⟨230444, by rfl⟩) R460889
theorem R274643 : Reach 274643 := rs (se 1 (by rfl) ⟨205982, by rfl⟩) R411965
theorem R307547 : Reach 307547 := rs (se 1 (by rfl) ⟨230660, by rfl⟩) R461321
theorem R209243 : Reach 209243 := rs (se 1 (by rfl) ⟨156932, by rfl⟩) R313865
theorem R209263 : Reach 209263 := rs (se 1 (by rfl) ⟨156947, by rfl⟩) R313895
theorem R274913 : Reach 274913 := rs (se 2 (by rfl) ⟨103092, by rfl⟩) R206185
theorem R209911 : Reach 209911 := rs (se 1 (by rfl) ⟨157433, by rfl⟩) R314867
theorem R79135 : Reach 79135 := rs (se 1 (by rfl) ⟨59351, by rfl⟩) R118703
theorem R308519 : Reach 308519 := rs (se 1 (by rfl) ⟨231389, by rfl⟩) R462779
theorem R210215 : Reach 210215 := rs (se 1 (by rfl) ⟨157661, by rfl⟩) R315323
theorem R79195 : Reach 79195 := rs (se 1 (by rfl) ⟨59396, by rfl⟩) R118793
theorem R79215 : Reach 79215 := rs (se 1 (by rfl) ⟨59411, by rfl⟩) R118823
theorem R79271 : Reach 79271 := rs (se 1 (by rfl) ⟨59453, by rfl⟩) R118907
theorem R79355 : Reach 79355 := rs (se 1 (by rfl) ⟨59516, by rfl⟩) R119033
theorem R79423 : Reach 79423 := rs (se 1 (by rfl) ⟨59567, by rfl⟩) R119135
theorem R79431 : Reach 79431 := rs (se 1 (by rfl) ⟨59573, by rfl⟩) R119147
theorem R276155 : Reach 276155 := rs (se 1 (by rfl) ⟨207116, by rfl⟩) R414233
theorem R79583 : Reach 79583 := rs (se 1 (by rfl) ⟨59687, by rfl⟩) R119375
theorem R79663 : Reach 79663 := rs (se 1 (by rfl) ⟨59747, by rfl⟩) R119495
theorem R3389303 : Reach 3389303 := rs (se 1 (by rfl) ⟨2541977, by rfl⟩) R5083955
theorem R79771 : Reach 79771 := rs (se 1 (by rfl) ⟨59828, by rfl⟩) R119657
theorem R178127 : Reach 178127 := rs (se 1 (by rfl) ⟨133595, by rfl⟩) R267191
theorem R79823 : Reach 79823 := rs (se 1 (by rfl) ⟨59867, by rfl⟩) R119735
theorem R79847 : Reach 79847 := rs (se 1 (by rfl) ⟨59885, by rfl⟩) R119771
theorem R374969 : Reach 374969 := rs (se 2 (by rfl) ⟨140613, by rfl⟩) R281227
theorem R80159 : Reach 80159 := rs (se 1 (by rfl) ⟨60119, by rfl⟩) R120239
theorem R178505 : Reach 178505 := rs (se 2 (by rfl) ⟨66939, by rfl⟩) R133879
theorem R178523 : Reach 178523 := rs (se 1 (by rfl) ⟨133892, by rfl⟩) R267785
theorem R80219 : Reach 80219 := rs (se 1 (by rfl) ⟨60164, by rfl⟩) R120329
theorem R80239 : Reach 80239 := rs (se 1 (by rfl) ⟨60179, by rfl⟩) R120359
theorem R80295 : Reach 80295 := rs (se 1 (by rfl) ⟨60221, by rfl⟩) R120443
theorem R80379 : Reach 80379 := rs (se 1 (by rfl) ⟨60284, by rfl⟩) R120569
theorem R80447 : Reach 80447 := rs (se 1 (by rfl) ⟨60335, by rfl⟩) R120671
theorem R80455 : Reach 80455 := rs (se 1 (by rfl) ⟨60341, by rfl⟩) R120683
theorem R408239 : Reach 408239 := rs (se 1 (by rfl) ⟨306179, by rfl⟩) R612359
theorem R80607 : Reach 80607 := rs (se 1 (by rfl) ⟨60455, by rfl⟩) R120911
theorem R310007 : Reach 310007 := rs (se 1 (by rfl) ⟨232505, by rfl⟩) R465011
theorem R80687 : Reach 80687 := rs (se 1 (by rfl) ⟨60515, by rfl⟩) R121031
theorem R867145 : Reach 867145 := rs (se 2 (by rfl) ⟨325179, by rfl⟩) R650359
theorem R179099 : Reach 179099 := rs (se 1 (by rfl) ⟨134324, by rfl⟩) R268649
theorem R80795 : Reach 80795 := rs (se 1 (by rfl) ⟨60596, by rfl⟩) R121193
theorem R80847 : Reach 80847 := rs (se 1 (by rfl) ⟨60635, by rfl⟩) R121271
theorem R80871 : Reach 80871 := rs (se 1 (by rfl) ⟨60653, by rfl⟩) R121307
theorem R408563 : Reach 408563 := rs (se 1 (by rfl) ⟨306422, by rfl⟩) R612845
theorem R179297 : Reach 179297 := rs (se 2 (by rfl) ⟨67236, by rfl⟩) R134473
theorem R277627 : Reach 277627 := rs (se 1 (by rfl) ⟨208220, by rfl⟩) R416441
theorem R81183 : Reach 81183 := rs (se 1 (by rfl) ⟨60887, by rfl⟩) R121775
theorem R179495 : Reach 179495 := rs (se 1 (by rfl) ⟨134621, by rfl⟩) R269243
theorem R81243 : Reach 81243 := rs (se 1 (by rfl) ⟨60932, by rfl⟩) R121865
theorem R81263 : Reach 81263 := rs (se 1 (by rfl) ⟨60947, by rfl⟩) R121895
theorem R114043 : Reach 114043 := rs (se 1 (by rfl) ⟨85532, by rfl⟩) R171065
theorem R81319 : Reach 81319 := rs (se 1 (by rfl) ⟨60989, by rfl⟩) R121979
theorem R81403 : Reach 81403 := rs (se 1 (by rfl) ⟨61052, by rfl⟩) R122105
theorem R81471 : Reach 81471 := rs (se 1 (by rfl) ⟨61103, by rfl⟩) R122207
theorem R81479 : Reach 81479 := rs (se 1 (by rfl) ⟨61109, by rfl⟩) R122219
theorem R278099 : Reach 278099 := rs (se 1 (by rfl) ⟨208574, by rfl⟩) R417149
theorem R179873 : Reach 179873 := rs (se 2 (by rfl) ⟨67452, by rfl⟩) R134905
theorem R81631 : Reach 81631 := rs (se 1 (by rfl) ⟨61223, by rfl⟩) R122447
theorem R81711 : Reach 81711 := rs (se 1 (by rfl) ⟨61283, by rfl⟩) R122567
theorem R81819 : Reach 81819 := rs (se 1 (by rfl) ⟨61364, by rfl⟩) R122729
theorem R81871 : Reach 81871 := rs (se 1 (by rfl) ⟨61403, by rfl⟩) R122807
theorem R81895 : Reach 81895 := rs (se 1 (by rfl) ⟨61421, by rfl⟩) R122843
theorem R180233 : Reach 180233 := rs (se 2 (by rfl) ⟨67587, by rfl⟩) R135175
theorem R409859 : Reach 409859 := rs (se 1 (by rfl) ⟨307394, by rfl⟩) R614789
theorem R82207 : Reach 82207 := rs (se 1 (by rfl) ⟨61655, by rfl⟩) R123311
theorem R82267 : Reach 82267 := rs (se 1 (by rfl) ⟨61700, by rfl⟩) R123401
theorem R82287 : Reach 82287 := rs (se 1 (by rfl) ⟨61715, by rfl⟩) R123431
theorem R180647 : Reach 180647 := rs (se 1 (by rfl) ⟨135485, by rfl⟩) R270971
theorem R82343 : Reach 82343 := rs (se 1 (by rfl) ⟨61757, by rfl⟩) R123515
theorem R1360313 : Reach 1360313 := rs (se 2 (by rfl) ⟨510117, by rfl⟩) R1020235
theorem R82427 : Reach 82427 := rs (se 1 (by rfl) ⟨61820, by rfl⟩) R123641
theorem R180755 : Reach 180755 := rs (se 1 (by rfl) ⟨135566, by rfl⟩) R271133
theorem R82495 : Reach 82495 := rs (se 1 (by rfl) ⟨61871, by rfl⟩) R123743
theorem R410183 : Reach 410183 := rs (se 1 (by rfl) ⟨307637, by rfl⟩) R615275
theorem R82503 : Reach 82503 := rs (se 1 (by rfl) ⟨61877, by rfl⟩) R123755
theorem R180809 : Reach 180809 := rs (se 2 (by rfl) ⟨67803, by rfl⟩) R135607
theorem R82655 : Reach 82655 := rs (se 1 (by rfl) ⟨61991, by rfl⟩) R123983
theorem R82735 : Reach 82735 := rs (se 1 (by rfl) ⟨62051, by rfl⟩) R124103
theorem R82843 : Reach 82843 := rs (se 1 (by rfl) ⟨62132, by rfl⟩) R124265
theorem R82895 : Reach 82895 := rs (se 1 (by rfl) ⟨62171, by rfl⟩) R124343
theorem R181223 : Reach 181223 := rs (se 1 (by rfl) ⟨135917, by rfl⟩) R271835
theorem R82919 : Reach 82919 := rs (se 1 (by rfl) ⟨62189, by rfl⟩) R124379
theorem R1000451 : Reach 1000451 := rs (se 1 (by rfl) ⟨750338, by rfl⟩) R1500677
theorem R1262891 : Reach 1262891 := rs (se 1 (by rfl) ⟨947168, by rfl⟩) R1894337
theorem R312619 : Reach 312619 := rs (se 1 (by rfl) ⟨234464, by rfl⟩) R468929
theorem R181601 : Reach 181601 := rs (se 2 (by rfl) ⟨68100, by rfl⟩) R136201
theorem R181691 : Reach 181691 := rs (se 1 (by rfl) ⟨136268, by rfl⟩) R272537
theorem R116167 : Reach 116167 := rs (se 1 (by rfl) ⟨87125, by rfl⟩) R174251
theorem R181817 : Reach 181817 := rs (se 2 (by rfl) ⟨68181, by rfl⟩) R136363
theorem R411479 : Reach 411479 := rs (se 1 (by rfl) ⟨308609, by rfl⟩) R617219
theorem R182483 : Reach 182483 := rs (se 1 (by rfl) ⟨136862, by rfl⟩) R273725
theorem R182537 : Reach 182537 := rs (se 2 (by rfl) ⟨68451, by rfl⟩) R136903
theorem R1526159 : Reach 1526159 := rs (se 1 (by rfl) ⟨1144619, by rfl⟩) R2289239
theorem R182753 : Reach 182753 := rs (se 2 (by rfl) ⟨68532, by rfl⟩) R137065
theorem R608957 : Reach 608957 := rs (se 3 (by rfl) ⟨114179, by rfl⟩) R228359
theorem R379667 : Reach 379667 := rs (se 1 (by rfl) ⟨284750, by rfl⟩) R569501
theorem R183059 : Reach 183059 := rs (se 1 (by rfl) ⟨137294, by rfl⟩) R274589
theorem R183419 : Reach 183419 := rs (se 1 (by rfl) ⟨137564, by rfl⟩) R275129
theorem R183545 : Reach 183545 := rs (se 2 (by rfl) ⟨68829, by rfl⟩) R137659
theorem R183689 : Reach 183689 := rs (se 2 (by rfl) ⟨68883, by rfl⟩) R137767
theorem R183815 : Reach 183815 := rs (se 1 (by rfl) ⟨137861, by rfl⟩) R275723
theorem R183995 : Reach 183995 := rs (se 1 (by rfl) ⟨137996, by rfl⟩) R275993
theorem R872203 : Reach 872203 := rs (se 1 (by rfl) ⟨654152, by rfl⟩) R1308305
theorem R282415 : Reach 282415 := rs (se 1 (by rfl) ⟨211811, by rfl⟩) R423623
theorem R184121 : Reach 184121 := rs (se 2 (by rfl) ⟨69045, by rfl⟩) R138091
theorem R347977 : Reach 347977 := rs (se 2 (by rfl) ⟨130491, by rfl⟩) R260983
theorem R413747 : Reach 413747 := rs (se 1 (by rfl) ⟨310310, by rfl⟩) R620621
theorem R118889 : Reach 118889 := rs (se 2 (by rfl) ⟨44583, by rfl⟩) R89167
theorem R381131 : Reach 381131 := rs (se 1 (by rfl) ⟨285848, by rfl⟩) R571697
theorem R86303 : Reach 86303 := rs (se 1 (by rfl) ⟨64727, by rfl⟩) R129455
theorem R86383 : Reach 86383 := rs (se 1 (by rfl) ⟨64787, by rfl⟩) R129575
theorem R119207 : Reach 119207 := rs (se 1 (by rfl) ⟨89405, by rfl⟩) R178811
theorem R184751 : Reach 184751 := rs (se 1 (by rfl) ⟨138563, by rfl⟩) R277127
theorem R184787 : Reach 184787 := rs (se 1 (by rfl) ⟨138590, by rfl⟩) R277181
theorem R119291 : Reach 119291 := rs (se 1 (by rfl) ⟨89468, by rfl⟩) R178937
theorem R184895 : Reach 184895 := rs (se 1 (by rfl) ⟨138671, by rfl⟩) R277343
theorem R119417 : Reach 119417 := rs (se 2 (by rfl) ⟨44781, by rfl⟩) R89563
theorem R185003 : Reach 185003 := rs (se 1 (by rfl) ⟨138752, by rfl⟩) R277505
theorem R119471 : Reach 119471 := rs (se 1 (by rfl) ⟨89603, by rfl⟩) R179207
theorem R119519 : Reach 119519 := rs (se 1 (by rfl) ⟨89639, by rfl⟩) R179279
theorem R119783 : Reach 119783 := rs (se 1 (by rfl) ⟨89837, by rfl⟩) R179675
theorem R185543 : Reach 185543 := rs (se 1 (by rfl) ⟨139157, by rfl⟩) R278315
theorem R120041 : Reach 120041 := rs (se 2 (by rfl) ⟨45015, by rfl⟩) R90031
theorem R120095 : Reach 120095 := rs (se 1 (by rfl) ⟨90071, by rfl⟩) R180143
theorem R185723 : Reach 185723 := rs (se 1 (by rfl) ⟨139292, by rfl⟩) R278585
theorem R87463 : Reach 87463 := rs (se 1 (by rfl) ⟨65597, by rfl⟩) R131195
theorem R120263 : Reach 120263 := rs (se 1 (by rfl) ⟨90197, by rfl⟩) R180395
theorem R185849 : Reach 185849 := rs (se 2 (by rfl) ⟨69693, by rfl⟩) R139387
theorem R185939 : Reach 185939 := rs (se 1 (by rfl) ⟨139454, by rfl⟩) R278909
theorem R87647 : Reach 87647 := rs (se 1 (by rfl) ⟨65735, by rfl⟩) R131471
theorem R415367 : Reach 415367 := rs (se 1 (by rfl) ⟨311525, by rfl⟩) R623051
theorem R186119 : Reach 186119 := rs (se 1 (by rfl) ⟨139589, by rfl⟩) R279179
theorem R120617 : Reach 120617 := rs (se 2 (by rfl) ⟨45231, by rfl⟩) R90463
theorem R120623 : Reach 120623 := rs (se 1 (by rfl) ⟨90467, by rfl⟩) R180935
theorem R350057 : Reach 350057 := rs (se 2 (by rfl) ⟨131271, by rfl⟩) R262543
theorem R2840777 : Reach 2840777 := rs (se 2 (by rfl) ⟨1065291, by rfl⟩) R2130583
theorem R121097 : Reach 121097 := rs (se 2 (by rfl) ⟨45411, by rfl⟩) R90823
theorem R186731 : Reach 186731 := rs (se 1 (by rfl) ⟨140048, by rfl⟩) R280097
theorem R416111 : Reach 416111 := rs (se 1 (by rfl) ⟨312083, by rfl⟩) R624167
theorem R121199 : Reach 121199 := rs (se 1 (by rfl) ⟨90899, by rfl⟩) R181799
theorem R383399 : Reach 383399 := rs (se 1 (by rfl) ⟨287549, by rfl⟩) R575099
theorem R186875 : Reach 186875 := rs (se 1 (by rfl) ⟨140156, by rfl⟩) R280313
theorem R121415 : Reach 121415 := rs (se 1 (by rfl) ⟨91061, by rfl⟩) R182123
theorem R121451 : Reach 121451 := rs (se 1 (by rfl) ⟨91088, by rfl⟩) R182177
theorem R187001 : Reach 187001 := rs (se 2 (by rfl) ⟨70125, by rfl⟩) R140251
theorem R580229 : Reach 580229 := rs (se 4 (by rfl) ⟨54396, by rfl⟩) R108793
theorem R514835 : Reach 514835 := rs (se 1 (by rfl) ⟨386126, by rfl⟩) R772253
theorem R121679 : Reach 121679 := rs (se 1 (by rfl) ⟨91259, by rfl⟩) R182519
theorem R1530899 : Reach 1530899 := rs (se 1 (by rfl) ⟨1148174, by rfl⟩) R2296349
theorem R122075 : Reach 122075 := rs (se 1 (by rfl) ⟨91556, by rfl⟩) R183113
theorem R416987 : Reach 416987 := rs (se 1 (by rfl) ⟨312740, by rfl⟩) R625481
theorem R89383 : Reach 89383 := rs (se 1 (by rfl) ⟨67037, by rfl⟩) R134075
theorem R286019 : Reach 286019 := rs (se 1 (by rfl) ⟨214514, by rfl⟩) R429029
theorem R89455 : Reach 89455 := rs (se 1 (by rfl) ⟨67091, by rfl⟩) R134183
theorem R122249 : Reach 122249 := rs (se 2 (by rfl) ⟨45843, by rfl⟩) R91687
theorem R1007063 : Reach 1007063 := rs (se 1 (by rfl) ⟨755297, by rfl⟩) R1510595
theorem R89671 : Reach 89671 := rs (se 1 (by rfl) ⟨67253, by rfl⟩) R134507
theorem R122603 : Reach 122603 := rs (se 1 (by rfl) ⟨91952, by rfl⟩) R183905
theorem R2350889 : Reach 2350889 := rs (se 2 (by rfl) ⟨881583, by rfl⟩) R1763167
theorem R876395 : Reach 876395 := rs (se 1 (by rfl) ⟨657296, by rfl⟩) R1314593
theorem R122831 : Reach 122831 := rs (se 1 (by rfl) ⟨92123, by rfl⟩) R184247
theorem R417793 : Reach 417793 := rs (se 2 (by rfl) ⟨156672, by rfl⟩) R313345
theorem R385033 : Reach 385033 := rs (se 2 (by rfl) ⟨144387, by rfl⟩) R288775
theorem R385049 : Reach 385049 := rs (se 2 (by rfl) ⟨144393, by rfl⟩) R288787
theorem R1466545 : Reach 1466545 := rs (se 2 (by rfl) ⟨549954, by rfl⟩) R1099909
theorem R418121 : Reach 418121 := rs (se 2 (by rfl) ⟨156795, by rfl⟩) R313591
theorem R123227 : Reach 123227 := rs (se 1 (by rfl) ⟨92420, by rfl⟩) R184841
theorem R90535 : Reach 90535 := rs (se 1 (by rfl) ⟨67901, by rfl⟩) R135803
theorem R516577 : Reach 516577 := rs (se 2 (by rfl) ⟨193716, by rfl⟩) R387433
theorem R123455 : Reach 123455 := rs (se 1 (by rfl) ⟨92591, by rfl⟩) R185183
theorem R123463 : Reach 123463 := rs (se 1 (by rfl) ⟨92597, by rfl⟩) R185195
theorem R221867 : Reach 221867 := rs (se 1 (by rfl) ⟨166400, by rfl⟩) R332801
theorem R123575 : Reach 123575 := rs (se 1 (by rfl) ⟨92681, by rfl⟩) R185363
theorem R123803 : Reach 123803 := rs (se 1 (by rfl) ⟨92852, by rfl⟩) R185705
theorem R91111 : Reach 91111 := rs (se 1 (by rfl) ⟨68333, by rfl⟩) R136667
theorem R1532903 : Reach 1532903 := rs (se 1 (by rfl) ⟨1149677, by rfl⟩) R2299355
theorem R418823 : Reach 418823 := rs (se 1 (by rfl) ⟨314117, by rfl⟩) R628235
theorem R3531869 : Reach 3531869 := rs (se 3 (by rfl) ⟨662225, by rfl⟩) R1324451
theorem R124199 : Reach 124199 := rs (se 1 (by rfl) ⟨93149, by rfl⟩) R186299
theorem R517499 : Reach 517499 := rs (se 1 (by rfl) ⟨388124, by rfl⟩) R776249
theorem R124283 : Reach 124283 := rs (se 1 (by rfl) ⟨93212, by rfl⟩) R186425
theorem R124409 : Reach 124409 := rs (se 2 (by rfl) ⟨46653, by rfl⟩) R93307
theorem R419417 : Reach 419417 := rs (se 2 (by rfl) ⟨157281, by rfl⟩) R314563
theorem R124511 : Reach 124511 := rs (se 1 (by rfl) ⟨93383, by rfl⟩) R186767
theorem R911249 : Reach 911249 := rs (se 2 (by rfl) ⟨341718, by rfl⟩) R683437
theorem R616733 : Reach 616733 := rs (se 3 (by rfl) ⟨115637, by rfl⟩) R231275
theorem R92539 : Reach 92539 := rs (se 1 (by rfl) ⟨69404, by rfl⟩) R138809
theorem R92767 : Reach 92767 := rs (se 1 (by rfl) ⟨69575, by rfl⟩) R139151
theorem R125867 : Reach 125867 := rs (se 1 (by rfl) ⟨94400, by rfl⟩) R188801
theorem R159175 : Reach 159175 := rs (se 1 (by rfl) ⟨119381, by rfl⟩) R238763
theorem R290621 : Reach 290621 := rs (se 3 (by rfl) ⟨54491, by rfl⟩) R108983
theorem R749533 : Reach 749533 := rs (se 3 (by rfl) ⟨140537, by rfl⟩) R281075
theorem R946241 : Reach 946241 := rs (se 2 (by rfl) ⟨354840, by rfl⟩) R709681
theorem R684395 : Reach 684395 := rs (se 1 (by rfl) ⟨513296, by rfl⟩) R1026593
theorem R914165 : Reach 914165 := rs (se 5 (by rfl) ⟨42851, by rfl⟩) R85703
theorem R226127 : Reach 226127 := rs (se 1 (by rfl) ⟨169595, by rfl⟩) R339191
theorem R1995637 : Reach 1995637 := rs (se 5 (by rfl) ⟨93545, by rfl⟩) R187091
theorem R127991 : Reach 127991 := rs (se 1 (by rfl) ⟨95993, by rfl⟩) R191987
theorem R1570265 : Reach 1570265 := rs (se 2 (by rfl) ⟨588849, by rfl⟩) R1177699
theorem R161543 : Reach 161543 := rs (se 1 (by rfl) ⟨121157, by rfl⟩) R242315
theorem R456839 : Reach 456839 := rs (se 1 (by rfl) ⟨342629, by rfl⟩) R685259
theorem R227767 : Reach 227767 := rs (se 1 (by rfl) ⟨170825, by rfl⟩) R341651
theorem R392123 : Reach 392123 := rs (se 1 (by rfl) ⟨294092, by rfl⟩) R588185
theorem R851267 : Reach 851267 := rs (se 1 (by rfl) ⟨638450, by rfl⟩) R1276901
theorem R1146383 : Reach 1146383 := rs (se 1 (by rfl) ⟨859787, by rfl⟩) R1719575
theorem R425785 : Reach 425785 := rs (se 2 (by rfl) ⟨159669, by rfl⟩) R319339
theorem R196481 : Reach 196481 := rs (se 2 (by rfl) ⟨73680, by rfl⟩) R147361
theorem R294785 : Reach 294785 := rs (se 2 (by rfl) ⟨110544, by rfl⟩) R221089
theorem R557057 : Reach 557057 := rs (se 2 (by rfl) ⟨208896, by rfl⟩) R417793
theorem R3736115 : Reach 3736115 := rs (se 1 (by rfl) ⟨2802086, by rfl⟩) R5604173
theorem R688769 : Reach 688769 := rs (se 2 (by rfl) ⟨258288, by rfl⟩) R516577
theorem R230141 : Reach 230141 := rs (se 3 (by rfl) ⟨43151, by rfl⟩) R86303
theorem R262909 : Reach 262909 := rs (se 3 (by rfl) ⟨49295, by rfl⟩) R98591
theorem R131881 : Reach 131881 := rs (se 2 (by rfl) ⟨49455, by rfl⟩) R98911
theorem R133111 : Reach 133111 := rs (se 1 (by rfl) ⟨99833, by rfl⟩) R199667
theorem R133663 : Reach 133663 := rs (se 1 (by rfl) ⟨100247, by rfl⟩) R200495
theorem R1968745 : Reach 1968745 := rs (se 2 (by rfl) ⟨738279, by rfl⟩) R1476559
theorem R134095 : Reach 134095 := rs (se 1 (by rfl) ⟨100571, by rfl⟩) R201143
theorem R658469 : Reach 658469 := rs (se 4 (by rfl) ⟨61731, by rfl⟩) R123463
theorem R134831 : Reach 134831 := rs (se 1 (by rfl) ⟨101123, by rfl⟩) R202247
theorem R1412801 : Reach 1412801 := rs (se 2 (by rfl) ⟨529800, by rfl⟩) R1059601
theorem R135067 : Reach 135067 := rs (se 1 (by rfl) ⟨101300, by rfl⟩) R202601
theorem R233371 : Reach 233371 := rs (se 1 (by rfl) ⟨175028, by rfl⟩) R350057
theorem R135355 : Reach 135355 := rs (se 1 (by rfl) ⟨101516, by rfl⟩) R203033
theorem R233725 : Reach 233725 := rs (se 3 (by rfl) ⟨43823, by rfl⟩) R87647
theorem R135479 : Reach 135479 := rs (se 1 (by rfl) ⟨101609, by rfl⟩) R203219
theorem R1020599 : Reach 1020599 := rs (se 1 (by rfl) ⟨765449, by rfl⟩) R1530899
theorem R529193 : Reach 529193 := rs (se 2 (by rfl) ⟨198447, by rfl⟩) R396895
theorem R267137 : Reach 267137 := rs (se 2 (by rfl) ⟨100176, by rfl⟩) R200353
theorem R201791 : Reach 201791 := rs (se 1 (by rfl) ⟨151343, by rfl⟩) R302687
theorem R136255 : Reach 136255 := rs (se 1 (by rfl) ⟨102191, by rfl⟩) R204383
theorem R463969 : Reach 463969 := rs (se 2 (by rfl) ⟨173988, by rfl⟩) R347977
theorem R464237 : Reach 464237 := rs (se 3 (by rfl) ⟨87044, by rfl⟩) R174089
theorem R136775 : Reach 136775 := rs (se 1 (by rfl) ⟨102581, by rfl⟩) R205163
theorem R464555 : Reach 464555 := rs (se 1 (by rfl) ⟨348416, by rfl⟩) R696833
theorem R267947 : Reach 267947 := rs (se 1 (by rfl) ⟨200960, by rfl⟩) R401921
theorem R628397 : Reach 628397 := rs (se 3 (by rfl) ⟨117824, by rfl⟩) R235649
theorem R136991 : Reach 136991 := rs (se 1 (by rfl) ⟨102743, by rfl⟩) R205487
theorem R268271 : Reach 268271 := rs (se 1 (by rfl) ⟨201203, by rfl⟩) R402407
theorem R137207 : Reach 137207 := rs (se 1 (by rfl) ⟨102905, by rfl⟩) R205811
theorem R202895 : Reach 202895 := rs (se 1 (by rfl) ⟨152171, by rfl⟩) R304343
theorem R268487 : Reach 268487 := rs (se 1 (by rfl) ⟨201365, by rfl⟩) R402731
theorem R530729 : Reach 530729 := rs (se 2 (by rfl) ⟨199023, by rfl⟩) R398047
theorem R4069757 : Reach 4069757 := rs (se 3 (by rfl) ⟨763079, by rfl⟩) R1526159
theorem R2660849 : Reach 2660849 := rs (se 2 (by rfl) ⟨997818, by rfl⟩) R1995637
theorem R531031 : Reach 531031 := rs (se 1 (by rfl) ⟨398273, by rfl⟩) R796547
theorem R269135 : Reach 269135 := rs (se 1 (by rfl) ⟨201851, by rfl⟩) R403703
theorem R138287 : Reach 138287 := rs (se 1 (by rfl) ⟨103715, by rfl⟩) R207431
theorem R138361 : Reach 138361 := rs (se 2 (by rfl) ⟨51885, by rfl⟩) R103771
theorem R269459 : Reach 269459 := rs (se 1 (by rfl) ⟨202094, by rfl⟩) R404189
theorem R990575 : Reach 990575 := rs (se 1 (by rfl) ⟨742931, by rfl⟩) R1485863
theorem R269729 : Reach 269729 := rs (se 2 (by rfl) ⟨101148, by rfl⟩) R202297
theorem R138665 : Reach 138665 := rs (se 2 (by rfl) ⟨51999, by rfl⟩) R103999
theorem R794087 : Reach 794087 := rs (se 1 (by rfl) ⟨595565, by rfl⟩) R1191131
theorem R466469 : Reach 466469 := rs (se 4 (by rfl) ⟨43731, by rfl⟩) R87463
theorem R270269 : Reach 270269 := rs (se 3 (by rfl) ⟨50675, by rfl⟩) R101351
theorem R204839 : Reach 204839 := rs (se 1 (by rfl) ⟨153629, by rfl⟩) R307259
theorem R630827 : Reach 630827 := rs (se 1 (by rfl) ⟨473120, by rfl⟩) R946241
theorem R205031 : Reach 205031 := rs (se 1 (by rfl) ⟨153773, by rfl⟩) R307547
theorem R139495 : Reach 139495 := rs (se 1 (by rfl) ⟨104621, by rfl⟩) R209243
theorem R139657 : Reach 139657 := rs (se 2 (by rfl) ⟨52371, by rfl⟩) R104743
theorem R303689 : Reach 303689 := rs (se 2 (by rfl) ⟨113883, by rfl⟩) R227767
theorem R140089 : Reach 140089 := rs (se 2 (by rfl) ⟨52533, by rfl⟩) R105067
theorem R2270045 : Reach 2270045 := rs (se 3 (by rfl) ⟨425633, by rfl⟩) R851267
theorem R205679 : Reach 205679 := rs (se 1 (by rfl) ⟨154259, by rfl⟩) R308519
theorem R140143 : Reach 140143 := rs (se 1 (by rfl) ⟨105107, by rfl⟩) R210215
theorem R1156193 : Reach 1156193 := rs (se 2 (by rfl) ⟨433572, by rfl⟩) R867145
theorem R107695 : Reach 107695 := rs (se 1 (by rfl) ⟨80771, by rfl⟩) R161543
theorem R304559 : Reach 304559 := rs (se 1 (by rfl) ⟨228419, by rfl⟩) R456839
theorem R370169 : Reach 370169 := rs (se 2 (by rfl) ⟨138813, by rfl⟩) R277627
theorem R272159 : Reach 272159 := rs (se 1 (by rfl) ⟨204119, by rfl⟩) R408239
theorem R206671 : Reach 206671 := rs (se 1 (by rfl) ⟨155003, by rfl⟩) R310007
theorem R272375 : Reach 272375 := rs (se 1 (by rfl) ⟨204281, by rfl⟩) R408563
theorem R764255 : Reach 764255 := rs (se 1 (by rfl) ⟨573191, by rfl⟩) R1146383
theorem R567713 : Reach 567713 := rs (se 2 (by rfl) ⟨212892, by rfl⟩) R425785
theorem R273239 : Reach 273239 := rs (se 1 (by rfl) ⟨204929, by rfl⟩) R409859
theorem R273455 : Reach 273455 := rs (se 1 (by rfl) ⟨205091, by rfl⟩) R410183
theorem R175439 : Reach 175439 := rs (se 1 (by rfl) ⟨131579, by rfl⟩) R263159
theorem R666967 : Reach 666967 := rs (se 1 (by rfl) ⟨500225, by rfl⟩) R1000451
theorem R273833 : Reach 273833 := rs (se 2 (by rfl) ⟨102687, by rfl⟩) R205375
theorem R634391 : Reach 634391 := rs (se 1 (by rfl) ⟨475793, by rfl⟩) R951587
theorem R274319 : Reach 274319 := rs (se 1 (by rfl) ⟨205739, by rfl⟩) R411479
theorem R176251 : Reach 176251 := rs (se 1 (by rfl) ⟨132188, by rfl⟩) R264377
theorem R274697 : Reach 274697 := rs (se 2 (by rfl) ⟨103011, by rfl⟩) R206023
theorem R405971 : Reach 405971 := rs (se 1 (by rfl) ⟨304478, by rfl⟩) R608957
theorem R897821 : Reach 897821 := rs (se 3 (by rfl) ⟨168341, by rfl⟩) R336683
theorem R341309 : Reach 341309 := rs (se 3 (by rfl) ⟨63995, by rfl⟩) R127991
theorem R275831 : Reach 275831 := rs (se 1 (by rfl) ⟨206873, by rfl⟩) R413747
theorem R79259 : Reach 79259 := rs (se 1 (by rfl) ⟨59444, by rfl⟩) R118889
theorem R79471 : Reach 79471 := rs (se 1 (by rfl) ⟨59603, by rfl⟩) R119207
theorem R79527 : Reach 79527 := rs (se 1 (by rfl) ⟨59645, by rfl⟩) R119291
theorem R79611 : Reach 79611 := rs (se 1 (by rfl) ⟨59708, by rfl⟩) R119417
theorem R79647 : Reach 79647 := rs (se 1 (by rfl) ⟨59735, by rfl⟩) R119471
theorem R79679 : Reach 79679 := rs (se 1 (by rfl) ⟨59759, by rfl⟩) R119519
theorem R79855 : Reach 79855 := rs (se 1 (by rfl) ⟨59891, by rfl⟩) R119783
theorem R178271 : Reach 178271 := rs (se 1 (by rfl) ⟨133703, by rfl⟩) R267407
theorem R80027 : Reach 80027 := rs (se 1 (by rfl) ⟨60020, by rfl⟩) R120041
theorem R276641 : Reach 276641 := rs (se 2 (by rfl) ⟨103740, by rfl⟩) R207481
theorem R80063 : Reach 80063 := rs (se 1 (by rfl) ⟨60047, by rfl⟩) R120095
theorem R80175 : Reach 80175 := rs (se 1 (by rfl) ⟨60131, by rfl⟩) R120263
theorem R145721 : Reach 145721 := rs (se 2 (by rfl) ⟨54645, by rfl⟩) R109291
theorem R276911 : Reach 276911 := rs (se 1 (by rfl) ⟨207683, by rfl⟩) R415367
theorem R80411 : Reach 80411 := rs (se 1 (by rfl) ⟨60308, by rfl⟩) R120617
theorem R80415 : Reach 80415 := rs (se 1 (by rfl) ⟨60311, by rfl⟩) R120623
theorem R179027 : Reach 179027 := rs (se 1 (by rfl) ⟨134270, by rfl⟩) R268541
theorem R80731 : Reach 80731 := rs (se 1 (by rfl) ⟨60548, by rfl⟩) R121097
theorem R80799 : Reach 80799 := rs (se 1 (by rfl) ⟨60599, by rfl⟩) R121199
theorem R80943 : Reach 80943 := rs (se 1 (by rfl) ⟨60707, by rfl⟩) R121415
theorem R80967 : Reach 80967 := rs (se 1 (by rfl) ⟨60725, by rfl⟩) R121451
theorem R2112641 : Reach 2112641 := rs (se 2 (by rfl) ⟨792240, by rfl⟩) R1584481
theorem R343223 : Reach 343223 := rs (se 1 (by rfl) ⟨257417, by rfl⟩) R514835
theorem R244919 : Reach 244919 := rs (se 1 (by rfl) ⟨183689, by rfl⟩) R367379
theorem R81119 : Reach 81119 := rs (se 1 (by rfl) ⟨60839, by rfl⟩) R121679
theorem R179567 : Reach 179567 := rs (se 1 (by rfl) ⟨134675, by rfl⟩) R269351
theorem R81383 : Reach 81383 := rs (se 1 (by rfl) ⟨61037, by rfl⟩) R122075
theorem R277991 : Reach 277991 := rs (se 1 (by rfl) ⟨208493, by rfl⟩) R416987
theorem R81499 : Reach 81499 := rs (se 1 (by rfl) ⟨61124, by rfl⟩) R122249
theorem R179855 : Reach 179855 := rs (se 1 (by rfl) ⟨134891, by rfl⟩) R269783
theorem R671375 : Reach 671375 := rs (se 1 (by rfl) ⟨503531, by rfl⟩) R1007063
theorem R1162937 : Reach 1162937 := rs (se 2 (by rfl) ⟨436101, by rfl⟩) R872203
theorem R179945 : Reach 179945 := rs (se 2 (by rfl) ⟨67479, by rfl⟩) R134959
theorem R376553 : Reach 376553 := rs (se 2 (by rfl) ⟨141207, by rfl⟩) R282415
theorem R81735 : Reach 81735 := rs (se 1 (by rfl) ⟨61301, by rfl⟩) R122603
theorem R999377 : Reach 999377 := rs (se 2 (by rfl) ⟨374766, by rfl⟩) R749533
theorem R81887 : Reach 81887 := rs (se 1 (by rfl) ⟨61415, by rfl⟩) R122831
theorem R311435 : Reach 311435 := rs (se 1 (by rfl) ⟨233576, by rfl⟩) R467153
theorem R278747 : Reach 278747 := rs (se 1 (by rfl) ⟨209060, by rfl⟩) R418121
theorem R82151 : Reach 82151 := rs (se 1 (by rfl) ⟨61613, by rfl⟩) R123227
theorem R82303 : Reach 82303 := rs (se 1 (by rfl) ⟨61727, by rfl⟩) R123455
theorem R147911 : Reach 147911 := rs (se 1 (by rfl) ⟨110933, by rfl⟩) R221867
theorem R82383 : Reach 82383 := rs (se 1 (by rfl) ⟨61787, by rfl⟩) R123575
theorem R115177 : Reach 115177 := rs (se 2 (by rfl) ⟨43191, by rfl⟩) R86383
theorem R279017 : Reach 279017 := rs (se 2 (by rfl) ⟨104631, by rfl⟩) R209263
theorem R82535 : Reach 82535 := rs (se 1 (by rfl) ⟨61901, by rfl⟩) R123803
theorem R279215 : Reach 279215 := rs (se 1 (by rfl) ⟨209411, by rfl⟩) R418823
theorem R180971 : Reach 180971 := rs (se 1 (by rfl) ⟨135728, by rfl⟩) R271457
theorem R82799 : Reach 82799 := rs (se 1 (by rfl) ⟨62099, by rfl⟩) R124199
theorem R344999 : Reach 344999 := rs (se 1 (by rfl) ⟨258749, by rfl⟩) R517499
theorem R82855 : Reach 82855 := rs (se 1 (by rfl) ⟨62141, by rfl⟩) R124283
theorem R82939 : Reach 82939 := rs (se 1 (by rfl) ⟨62204, by rfl⟩) R124409
theorem R279611 : Reach 279611 := rs (se 1 (by rfl) ⟨209708, by rfl⟩) R419417
theorem R83007 : Reach 83007 := rs (se 1 (by rfl) ⟨62255, by rfl⟩) R124511
theorem R607499 : Reach 607499 := rs (se 1 (by rfl) ⟨455624, by rfl⟩) R911249
theorem R279881 : Reach 279881 := rs (se 2 (by rfl) ⟨104955, by rfl⟩) R209911
theorem R411155 : Reach 411155 := rs (se 1 (by rfl) ⟨308366, by rfl⟩) R616733
theorem R3130919 : Reach 3130919 := rs (se 1 (by rfl) ⟨2348189, by rfl⟩) R4696379
theorem R181871 : Reach 181871 := rs (se 1 (by rfl) ⟨136403, by rfl⟩) R272807
theorem R312947 : Reach 312947 := rs (se 1 (by rfl) ⟨234710, by rfl⟩) R469421
theorem R116407 : Reach 116407 := rs (se 1 (by rfl) ⟨87305, by rfl⟩) R174611
theorem R181979 : Reach 181979 := rs (se 1 (by rfl) ⟨136484, by rfl⟩) R272969
theorem R83911 : Reach 83911 := rs (se 1 (by rfl) ⟨62933, by rfl⟩) R125867
theorem R183095 : Reach 183095 := rs (se 1 (by rfl) ⟨137321, by rfl⟩) R274643
theorem R183275 : Reach 183275 := rs (se 1 (by rfl) ⟨137456, by rfl⟩) R274913
theorem R609443 : Reach 609443 := rs (se 1 (by rfl) ⟨457082, by rfl⟩) R914165
theorem R150751 : Reach 150751 := rs (se 1 (by rfl) ⟨113063, by rfl⟩) R226127
theorem R184103 : Reach 184103 := rs (se 1 (by rfl) ⟨138077, by rfl⟩) R276155
theorem R118751 : Reach 118751 := rs (se 1 (by rfl) ⟨89063, by rfl⟩) R178127
theorem R249979 : Reach 249979 := rs (se 1 (by rfl) ⟨187484, by rfl⟩) R374969
theorem R119003 : Reach 119003 := rs (se 1 (by rfl) ⟨89252, by rfl⟩) R178505
theorem R119015 : Reach 119015 := rs (se 1 (by rfl) ⟨89261, by rfl⟩) R178523
theorem R119177 : Reach 119177 := rs (se 2 (by rfl) ⟨44691, by rfl⟩) R89383
theorem R119273 : Reach 119273 := rs (se 2 (by rfl) ⟨44727, by rfl⟩) R89455
theorem R152057 : Reach 152057 := rs (se 2 (by rfl) ⟨57021, by rfl⟩) R114043
theorem R119399 : Reach 119399 := rs (se 1 (by rfl) ⟨89549, by rfl⟩) R179099
theorem R119531 : Reach 119531 := rs (se 1 (by rfl) ⟨89648, by rfl⟩) R179297
theorem R119561 : Reach 119561 := rs (se 2 (by rfl) ⟨44835, by rfl⟩) R89671
theorem R185129 : Reach 185129 := rs (se 2 (by rfl) ⟨69423, by rfl⟩) R138847
theorem R119663 : Reach 119663 := rs (se 1 (by rfl) ⟨89747, by rfl⟩) R179495
theorem R185399 : Reach 185399 := rs (se 1 (by rfl) ⟨139049, by rfl⟩) R278099
theorem R185417 : Reach 185417 := rs (se 2 (by rfl) ⟨69531, by rfl⟩) R139063
theorem R119915 : Reach 119915 := rs (se 1 (by rfl) ⟨89936, by rfl⟩) R179873
theorem R120155 : Reach 120155 := rs (se 1 (by rfl) ⟨90116, by rfl⟩) R180233
theorem R152923 : Reach 152923 := rs (se 1 (by rfl) ⟨114692, by rfl⟩) R229385
theorem R513377 : Reach 513377 := rs (se 2 (by rfl) ⟨192516, by rfl⟩) R385033
theorem R611873 : Reach 611873 := rs (se 2 (by rfl) ⟨229452, by rfl⟩) R458905
theorem R1955393 : Reach 1955393 := rs (se 2 (by rfl) ⟨733272, by rfl⟩) R1466545
theorem R120431 : Reach 120431 := rs (se 1 (by rfl) ⟨90323, by rfl⟩) R180647
theorem R906875 : Reach 906875 := rs (se 1 (by rfl) ⟨680156, by rfl⟩) R1360313
theorem R120503 : Reach 120503 := rs (se 1 (by rfl) ⟨90377, by rfl⟩) R180755
theorem R120539 : Reach 120539 := rs (se 1 (by rfl) ⟨90404, by rfl⟩) R180809
theorem R120713 : Reach 120713 := rs (se 2 (by rfl) ⟨45267, by rfl⟩) R90535
theorem R120815 : Reach 120815 := rs (se 1 (by rfl) ⟨90611, by rfl⟩) R181223
theorem R841927 : Reach 841927 := rs (se 1 (by rfl) ⟨631445, by rfl⟩) R1262891
theorem R121067 : Reach 121067 := rs (se 1 (by rfl) ⟨90800, by rfl⟩) R181601
theorem R121127 : Reach 121127 := rs (se 1 (by rfl) ⟨90845, by rfl⟩) R181691
theorem R121211 : Reach 121211 := rs (se 1 (by rfl) ⟨90908, by rfl⟩) R181817
theorem R350639 : Reach 350639 := rs (se 1 (by rfl) ⟨262979, by rfl⟩) R525959
theorem R121481 : Reach 121481 := rs (se 2 (by rfl) ⟨45555, by rfl⟩) R91111
theorem R121655 : Reach 121655 := rs (se 1 (by rfl) ⟨91241, by rfl⟩) R182483
theorem R121691 : Reach 121691 := rs (se 1 (by rfl) ⟨91268, by rfl⟩) R182537
theorem R121835 : Reach 121835 := rs (se 1 (by rfl) ⟨91376, by rfl⟩) R182753
theorem R416825 : Reach 416825 := rs (se 2 (by rfl) ⟨156309, by rfl⟩) R312619
theorem R122039 : Reach 122039 := rs (se 1 (by rfl) ⟨91529, by rfl⟩) R183059
theorem R89311 : Reach 89311 := rs (se 1 (by rfl) ⟨66983, by rfl⟩) R133967
theorem R154889 : Reach 154889 := rs (se 2 (by rfl) ⟨58083, by rfl⟩) R116167
theorem R122279 : Reach 122279 := rs (se 1 (by rfl) ⟨91709, by rfl⟩) R183419
theorem R122363 : Reach 122363 := rs (se 1 (by rfl) ⟨91772, by rfl⟩) R183545
theorem R122459 : Reach 122459 := rs (se 1 (by rfl) ⟨91844, by rfl⟩) R183689
theorem R122543 : Reach 122543 := rs (se 1 (by rfl) ⟨91907, by rfl⟩) R183815
theorem R122663 : Reach 122663 := rs (se 1 (by rfl) ⟨91997, by rfl⟩) R183995
theorem R122747 : Reach 122747 := rs (se 1 (by rfl) ⟨92060, by rfl⟩) R184121
theorem R4087741 : Reach 4087741 := rs (se 3 (by rfl) ⟨766451, by rfl⟩) R1532903
theorem R254087 : Reach 254087 := rs (se 1 (by rfl) ⟨190565, by rfl⟩) R381131
theorem R123167 : Reach 123167 := rs (se 1 (by rfl) ⟨92375, by rfl⟩) R184751
theorem R123191 : Reach 123191 := rs (se 1 (by rfl) ⟨92393, by rfl⟩) R184787
theorem R123263 : Reach 123263 := rs (se 1 (by rfl) ⟨92447, by rfl⟩) R184895
theorem R123335 : Reach 123335 := rs (se 1 (by rfl) ⟨92501, by rfl⟩) R185003
theorem R123385 : Reach 123385 := rs (se 2 (by rfl) ⟨46269, by rfl⟩) R92539
theorem R123689 : Reach 123689 := rs (se 2 (by rfl) ⟨46383, by rfl⟩) R92767
theorem R123695 : Reach 123695 := rs (se 1 (by rfl) ⟨92771, by rfl⟩) R185543
theorem R156583 : Reach 156583 := rs (se 1 (by rfl) ⟨117437, by rfl⟩) R234875
theorem R123815 : Reach 123815 := rs (se 1 (by rfl) ⟨92861, by rfl⟩) R185723
theorem R123899 : Reach 123899 := rs (se 1 (by rfl) ⟨92924, by rfl⟩) R185849
theorem R123959 : Reach 123959 := rs (se 1 (by rfl) ⟨92969, by rfl⟩) R185939
theorem R124079 : Reach 124079 := rs (se 1 (by rfl) ⟨93059, by rfl⟩) R186119
theorem R1893851 : Reach 1893851 := rs (se 1 (by rfl) ⟨1420388, by rfl⟩) R2840777
theorem R124487 : Reach 124487 := rs (se 1 (by rfl) ⟨93365, by rfl⟩) R186731
theorem R255599 : Reach 255599 := rs (se 1 (by rfl) ⟨191699, by rfl⟩) R383399
theorem R91759 : Reach 91759 := rs (se 1 (by rfl) ⟨68819, by rfl⟩) R137639
theorem R124583 : Reach 124583 := rs (se 1 (by rfl) ⟨93437, by rfl⟩) R186875
theorem R91867 : Reach 91867 := rs (se 1 (by rfl) ⟨68900, by rfl⟩) R137801
theorem R157403 : Reach 157403 := rs (se 1 (by rfl) ⟨118052, by rfl⟩) R236105
theorem R124667 : Reach 124667 := rs (se 1 (by rfl) ⟨93500, by rfl⟩) R187001
theorem R386819 : Reach 386819 := rs (se 1 (by rfl) ⟨290114, by rfl⟩) R580229
theorem R157639 : Reach 157639 := rs (se 1 (by rfl) ⟨118229, by rfl⟩) R236459
theorem R223241 : Reach 223241 := rs (se 2 (by rfl) ⟨83715, by rfl⟩) R167431
theorem R190679 : Reach 190679 := rs (se 1 (by rfl) ⟨143009, by rfl⟩) R286019
theorem R9038141 : Reach 9038141 := rs (se 3 (by rfl) ⟨1694651, by rfl⟩) R3389303
theorem R289163 : Reach 289163 := rs (se 1 (by rfl) ⟨216872, by rfl⟩) R433745
theorem R1567259 : Reach 1567259 := rs (se 1 (by rfl) ⟨1175444, by rfl⟩) R2350889
theorem R584263 : Reach 584263 := rs (se 1 (by rfl) ⟨438197, by rfl⟩) R876395
theorem R256699 : Reach 256699 := rs (se 1 (by rfl) ⟨192524, by rfl⟩) R385049
theorem R3893953 : Reach 3893953 := rs (se 2 (by rfl) ⟨1460232, by rfl⟩) R2920465
theorem R93019 : Reach 93019 := rs (se 1 (by rfl) ⟨69764, by rfl⟩) R139529
theorem R617705 : Reach 617705 := rs (se 2 (by rfl) ⟨231639, by rfl⟩) R463279
theorem R290171 : Reach 290171 := rs (se 1 (by rfl) ⟨217628, by rfl⟩) R435257
theorem R224635 : Reach 224635 := rs (se 1 (by rfl) ⟨168476, by rfl⟩) R336953
theorem R2354579 : Reach 2354579 := rs (se 1 (by rfl) ⟨1765934, by rfl⟩) R3531869
theorem R1109629 : Reach 1109629 := rs (se 3 (by rfl) ⟨208055, by rfl⟩) R416111
theorem R290461 : Reach 290461 := rs (se 3 (by rfl) ⟨54461, by rfl⟩) R108923
theorem R225467 : Reach 225467 := rs (se 1 (by rfl) ⟨169100, by rfl⟩) R338201
theorem R1012445 : Reach 1012445 := rs (se 3 (by rfl) ⟨189833, by rfl⟩) R379667
theorem R848933 : Reach 848933 := rs (se 4 (by rfl) ⟨79587, by rfl⟩) R159175
theorem R193747 : Reach 193747 := rs (se 1 (by rfl) ⟨145310, by rfl⟩) R290621
theorem R226651 : Reach 226651 := rs (se 1 (by rfl) ⟨169988, by rfl⟩) R339977
theorem R456263 : Reach 456263 := rs (se 1 (by rfl) ⟨342197, by rfl⟩) R684395
theorem R1046843 : Reach 1046843 := rs (se 1 (by rfl) ⟨785132, by rfl⟩) R1570265
theorem R261415 : Reach 261415 := rs (se 1 (by rfl) ⟨196061, by rfl⟩) R392123
theorem R130987 : Reach 130987 := rs (se 1 (by rfl) ⟨98240, by rfl⟩) R196481
theorem R196523 : Reach 196523 := rs (se 1 (by rfl) ⟨147392, by rfl⟩) R294785
theorem R2490743 : Reach 2490743 := rs (se 1 (by rfl) ⟨1868057, by rfl⟩) R3736115
theorem R459179 : Reach 459179 := rs (se 1 (by rfl) ⟨344384, by rfl⟩) R688769
theorem R164513 : Reach 164513 := rs (se 2 (by rfl) ⟨61692, by rfl⟩) R123385
theorem R1411181 : Reach 1411181 := rs (se 3 (by rfl) ⟨264596, by rfl⟩) R529193
theorem R2033909 : Reach 2033909 := rs (se 5 (by rfl) ⟨95339, by rfl⟩) R190679
theorem R919997 : Reach 919997 := rs (se 3 (by rfl) ⟨172499, by rfl⟩) R344999
theorem R134527 : Reach 134527 := rs (se 1 (by rfl) ⟨100895, by rfl⟩) R201791
theorem R2624993 : Reach 2624993 := rs (se 2 (by rfl) ⟨984372, by rfl⟩) R1968745
theorem R135263 : Reach 135263 := rs (se 1 (by rfl) ⟨101447, by rfl⟩) R202895
theorem R233759 : Reach 233759 := rs (se 1 (by rfl) ⟨175319, by rfl⟩) R350639
theorem R201001 : Reach 201001 := rs (se 2 (by rfl) ⟨75375, by rfl⟩) R150751
theorem R1773899 : Reach 1773899 := rs (se 1 (by rfl) ⟨1330424, by rfl⟩) R2660849
theorem R889289 : Reach 889289 := rs (se 2 (by rfl) ⟨333483, by rfl⟩) R666967
theorem R299513 : Reach 299513 := rs (se 2 (by rfl) ⟨112317, by rfl⟩) R224635
theorem R1577717 : Reach 1577717 := rs (se 5 (by rfl) ⟨73955, by rfl⟩) R147911
theorem R1479505 : Reach 1479505 := rs (se 2 (by rfl) ⟨554814, by rfl⟩) R1109629
theorem R103259 : Reach 103259 := rs (se 1 (by rfl) ⟨77444, by rfl⟩) R154889
theorem R660383 : Reach 660383 := rs (se 1 (by rfl) ⟨495287, by rfl⟩) R990575
theorem R529391 : Reach 529391 := rs (se 1 (by rfl) ⟨397043, by rfl⟩) R794087
theorem R595309 : Reach 595309 := rs (se 3 (by rfl) ⟨111620, by rfl⟩) R223241
theorem R136559 : Reach 136559 := rs (se 1 (by rfl) ⟨102419, by rfl⟩) R204839
theorem R169391 : Reach 169391 := rs (se 1 (by rfl) ⟨127043, by rfl⟩) R254087
theorem R136687 : Reach 136687 := rs (se 1 (by rfl) ⟨102515, by rfl⟩) R205031
theorem R333305 : Reach 333305 := rs (se 2 (by rfl) ⟨124989, by rfl⟩) R249979
theorem R235001 : Reach 235001 := rs (se 2 (by rfl) ⟨88125, by rfl⟩) R176251
theorem R202459 : Reach 202459 := rs (se 1 (by rfl) ⟨151844, by rfl⟩) R303689
theorem R1513363 : Reach 1513363 := rs (se 1 (by rfl) ⟨1135022, by rfl⟩) R2270045
theorem R137119 : Reach 137119 := rs (se 1 (by rfl) ⟨102839, by rfl⟩) R205679
theorem R203039 : Reach 203039 := rs (se 1 (by rfl) ⟨152279, by rfl⟩) R304559
theorem R170399 : Reach 170399 := rs (se 1 (by rfl) ⟨127799, by rfl⟩) R255599
theorem R302201 : Reach 302201 := rs (se 2 (by rfl) ⟨113325, by rfl⟩) R226651
theorem R203897 : Reach 203897 := rs (se 2 (by rfl) ⟨76461, by rfl⟩) R152923
theorem R1122569 : Reach 1122569 := rs (se 2 (by rfl) ⟨420963, by rfl⟩) R841927
theorem R270647 : Reach 270647 := rs (se 1 (by rfl) ⟨202985, by rfl⟩) R405971
theorem R598547 : Reach 598547 := rs (se 1 (by rfl) ⟨448910, by rfl⟩) R897821
theorem R565955 : Reach 565955 := rs (se 1 (by rfl) ⟨424466, by rfl⟩) R848933
theorem R304175 : Reach 304175 := rs (se 1 (by rfl) ⟨228131, by rfl⟩) R456263
theorem R697895 : Reach 697895 := rs (se 1 (by rfl) ⟨523421, by rfl⟩) R1046843
theorem R174649 : Reach 174649 := rs (se 2 (by rfl) ⟨65493, by rfl⟩) R130987
theorem R5450321 : Reach 5450321 := rs (se 2 (by rfl) ⟨2043870, by rfl⟩) R4087741
theorem R666251 : Reach 666251 := rs (se 1 (by rfl) ⟨499688, by rfl⟩) R999377
theorem R1485485 : Reach 1485485 := rs (se 3 (by rfl) ⟨278528, by rfl⟩) R557057
theorem R207623 : Reach 207623 := rs (se 1 (by rfl) ⟨155717, by rfl⟩) R311435
theorem R404999 : Reach 404999 := rs (se 1 (by rfl) ⟨303749, by rfl⟩) R607499
theorem R274103 : Reach 274103 := rs (se 1 (by rfl) ⟨205577, by rfl⟩) R411155
theorem R175841 : Reach 175841 := rs (se 2 (by rfl) ⟨65940, by rfl⟩) R131881
theorem R208631 : Reach 208631 := rs (se 1 (by rfl) ⟨156473, by rfl⟩) R312947
theorem R208777 : Reach 208777 := rs (se 2 (by rfl) ⟨78291, by rfl⟩) R156583
theorem R405485 : Reach 405485 := rs (se 3 (by rfl) ⟨76028, by rfl⟩) R152057
theorem R438979 : Reach 438979 := rs (se 1 (by rfl) ⟨329234, by rfl⟩) R658469
theorem R406295 : Reach 406295 := rs (se 1 (by rfl) ⟨304721, by rfl⟩) R609443
theorem R275561 : Reach 275561 := rs (se 2 (by rfl) ⟨103335, by rfl⟩) R206671
theorem R210185 : Reach 210185 := rs (se 2 (by rfl) ⟨78819, by rfl⟩) R157639
theorem R111881 : Reach 111881 := rs (se 2 (by rfl) ⟨41955, by rfl⟩) R83911
theorem R79167 : Reach 79167 := rs (se 1 (by rfl) ⟨59375, by rfl⟩) R118751
theorem R177481 : Reach 177481 := rs (se 2 (by rfl) ⟨66555, by rfl⟩) R133111
theorem R79335 : Reach 79335 := rs (se 1 (by rfl) ⟨59501, by rfl⟩) R119003
theorem R79343 : Reach 79343 := rs (se 1 (by rfl) ⟨59507, by rfl⟩) R119015
theorem R79451 : Reach 79451 := rs (se 1 (by rfl) ⟨59588, by rfl⟩) R119177
theorem R79515 : Reach 79515 := rs (se 1 (by rfl) ⟨59636, by rfl⟩) R119273
theorem R79599 : Reach 79599 := rs (se 1 (by rfl) ⟨59699, by rfl⟩) R119399
theorem R79687 : Reach 79687 := rs (se 1 (by rfl) ⟨59765, by rfl⟩) R119531
theorem R79707 : Reach 79707 := rs (se 1 (by rfl) ⟨59780, by rfl⟩) R119561
theorem R79775 : Reach 79775 := rs (se 1 (by rfl) ⟨59831, by rfl⟩) R119663
theorem R178091 : Reach 178091 := rs (se 1 (by rfl) ⟨133568, by rfl⟩) R267137
theorem R178217 : Reach 178217 := rs (se 2 (by rfl) ⟨66831, by rfl⟩) R133663
theorem R79943 : Reach 79943 := rs (se 1 (by rfl) ⟨59957, by rfl⟩) R119915
theorem R80103 : Reach 80103 := rs (se 1 (by rfl) ⟨60077, by rfl⟩) R120155
theorem R342251 : Reach 342251 := rs (se 1 (by rfl) ⟨256688, by rfl⟩) R513377
theorem R309491 : Reach 309491 := rs (se 1 (by rfl) ⟨232118, by rfl⟩) R464237
theorem R5191937 : Reach 5191937 := rs (se 2 (by rfl) ⟨1946976, by rfl⟩) R3893953
theorem R407915 : Reach 407915 := rs (se 1 (by rfl) ⟨305936, by rfl⟩) R611873
theorem R80287 : Reach 80287 := rs (se 1 (by rfl) ⟨60215, by rfl⟩) R120431
theorem R604583 : Reach 604583 := rs (se 1 (by rfl) ⟨453437, by rfl⟩) R906875
theorem R178631 : Reach 178631 := rs (se 1 (by rfl) ⟨133973, by rfl⟩) R267947
theorem R309703 : Reach 309703 := rs (se 1 (by rfl) ⟨232277, by rfl⟩) R464555
theorem R80335 : Reach 80335 := rs (se 1 (by rfl) ⟨60251, by rfl⟩) R120503
theorem R80359 : Reach 80359 := rs (se 1 (by rfl) ⟨60269, by rfl⟩) R120539
theorem R80475 : Reach 80475 := rs (se 1 (by rfl) ⟨60356, by rfl⟩) R120713
theorem R178793 : Reach 178793 := rs (se 2 (by rfl) ⟨67047, by rfl⟩) R134095
theorem R178847 : Reach 178847 := rs (se 1 (by rfl) ⟨134135, by rfl⟩) R268271
theorem R80543 : Reach 80543 := rs (se 1 (by rfl) ⟨60407, by rfl⟩) R120815
theorem R178991 : Reach 178991 := rs (se 1 (by rfl) ⟨134243, by rfl⟩) R268487
theorem R80711 : Reach 80711 := rs (se 1 (by rfl) ⟨60533, by rfl⟩) R121067
theorem R80751 : Reach 80751 := rs (se 1 (by rfl) ⟨60563, by rfl⟩) R121127
theorem R80807 : Reach 80807 := rs (se 1 (by rfl) ⟨60605, by rfl⟩) R121211
theorem R80987 : Reach 80987 := rs (se 1 (by rfl) ⟨60740, by rfl⟩) R121481
theorem R81103 : Reach 81103 := rs (se 1 (by rfl) ⟨60827, by rfl⟩) R121655
theorem R179423 : Reach 179423 := rs (se 1 (by rfl) ⟨134567, by rfl⟩) R269135
theorem R81127 : Reach 81127 := rs (se 1 (by rfl) ⟨60845, by rfl⟩) R121691
theorem R81223 : Reach 81223 := rs (se 1 (by rfl) ⟨60917, by rfl⟩) R121835
theorem R277883 : Reach 277883 := rs (se 1 (by rfl) ⟨208412, by rfl⟩) R416825
theorem R179639 : Reach 179639 := rs (se 1 (by rfl) ⟨134729, by rfl⟩) R269459
theorem R81359 : Reach 81359 := rs (se 1 (by rfl) ⟨61019, by rfl⟩) R122039
theorem R179819 : Reach 179819 := rs (se 1 (by rfl) ⟨134864, by rfl⟩) R269729
theorem R81519 : Reach 81519 := rs (se 1 (by rfl) ⟨61139, by rfl⟩) R122279
theorem R81575 : Reach 81575 := rs (se 1 (by rfl) ⟨61181, by rfl⟩) R122363
theorem R310979 : Reach 310979 := rs (se 1 (by rfl) ⟨233234, by rfl⟩) R466469
theorem R81639 : Reach 81639 := rs (se 1 (by rfl) ⟨61229, by rfl⟩) R122459
theorem R81695 : Reach 81695 := rs (se 1 (by rfl) ⟨61271, by rfl⟩) R122543
theorem R81775 : Reach 81775 := rs (se 1 (by rfl) ⟨61331, by rfl⟩) R122663
theorem R311161 : Reach 311161 := rs (se 2 (by rfl) ⟨116685, by rfl⟩) R233371
theorem R180089 : Reach 180089 := rs (se 2 (by rfl) ⟨67533, by rfl⟩) R135067
theorem R81831 : Reach 81831 := rs (se 1 (by rfl) ⟨61373, by rfl⟩) R122747
theorem R180179 : Reach 180179 := rs (se 1 (by rfl) ⟨135134, by rfl⟩) R270269
theorem R82111 : Reach 82111 := rs (se 1 (by rfl) ⟨61583, by rfl⟩) R123167
theorem R82127 : Reach 82127 := rs (se 1 (by rfl) ⟨61595, by rfl⟩) R123191
theorem R180473 : Reach 180473 := rs (se 2 (by rfl) ⟨67677, by rfl⟩) R135355
theorem R82175 : Reach 82175 := rs (se 1 (by rfl) ⟨61631, by rfl⟩) R123263
theorem R82223 : Reach 82223 := rs (se 1 (by rfl) ⟨61667, by rfl⟩) R123335
theorem R311633 : Reach 311633 := rs (se 2 (by rfl) ⟨116862, by rfl⟩) R233725
theorem R82459 : Reach 82459 := rs (se 1 (by rfl) ⟨61844, by rfl⟩) R123689
theorem R82463 : Reach 82463 := rs (se 1 (by rfl) ⟨61847, by rfl⟩) R123695
theorem R82543 : Reach 82543 := rs (se 1 (by rfl) ⟨61907, by rfl⟩) R123815
theorem R82599 : Reach 82599 := rs (se 1 (by rfl) ⟨61949, by rfl⟩) R123899
theorem R82639 : Reach 82639 := rs (se 1 (by rfl) ⟨61979, by rfl⟩) R123959
theorem R770795 : Reach 770795 := rs (se 1 (by rfl) ⟨578096, by rfl⟩) R1156193
theorem R82719 : Reach 82719 := rs (se 1 (by rfl) ⟨62039, by rfl⟩) R124079
theorem R574373 : Reach 574373 := rs (se 4 (by rfl) ⟨53847, by rfl⟩) R107695
theorem R1262567 : Reach 1262567 := rs (se 1 (by rfl) ⟨946925, by rfl⟩) R1893851
theorem R246779 : Reach 246779 := rs (se 1 (by rfl) ⟨185084, by rfl⟩) R370169
theorem R82991 : Reach 82991 := rs (se 1 (by rfl) ⟨62243, by rfl⟩) R124487
theorem R83055 : Reach 83055 := rs (se 1 (by rfl) ⟨62291, by rfl⟩) R124583
theorem R83111 : Reach 83111 := rs (se 1 (by rfl) ⟨62333, by rfl⟩) R124667
theorem R181439 : Reach 181439 := rs (se 1 (by rfl) ⟨136079, by rfl⟩) R272159
theorem R181583 : Reach 181583 := rs (se 1 (by rfl) ⟨136187, by rfl⟩) R272375
theorem R214429 : Reach 214429 := rs (se 3 (by rfl) ⟨40205, by rfl⟩) R80411
theorem R181673 : Reach 181673 := rs (se 2 (by rfl) ⟨68127, by rfl⟩) R136255
theorem R509503 : Reach 509503 := rs (se 1 (by rfl) ⟨382127, by rfl⟩) R764255
theorem R378475 : Reach 378475 := rs (se 1 (by rfl) ⟨283856, by rfl⟩) R567713
theorem R182159 : Reach 182159 := rs (se 1 (by rfl) ⟨136619, by rfl⟩) R273239
theorem R182303 : Reach 182303 := rs (se 1 (by rfl) ⟨136727, by rfl⟩) R273455
theorem R411803 : Reach 411803 := rs (se 1 (by rfl) ⟨308852, by rfl⟩) R617705
theorem R116959 : Reach 116959 := rs (se 1 (by rfl) ⟨87719, by rfl⟩) R175439
theorem R182555 : Reach 182555 := rs (se 1 (by rfl) ⟨136916, by rfl⟩) R273833
theorem R182879 : Reach 182879 := rs (se 1 (by rfl) ⟨137159, by rfl⟩) R274319
theorem R150311 : Reach 150311 := rs (se 1 (by rfl) ⟨112733, by rfl⟩) R225467
theorem R183131 : Reach 183131 := rs (se 1 (by rfl) ⟨137348, by rfl⟩) R274697
theorem R674963 : Reach 674963 := rs (se 1 (by rfl) ⟨506222, by rfl⟩) R1012445
theorem R708041 : Reach 708041 := rs (se 2 (by rfl) ⟨265515, by rfl⟩) R531031
theorem R183887 : Reach 183887 := rs (se 1 (by rfl) ⟨137915, by rfl⟩) R275831
theorem R118847 : Reach 118847 := rs (se 1 (by rfl) ⟨89135, by rfl⟩) R178271
theorem R184427 : Reach 184427 := rs (se 1 (by rfl) ⟨138320, by rfl⟩) R276641
theorem R184481 : Reach 184481 := rs (se 2 (by rfl) ⟨69180, by rfl⟩) R138361
theorem R184607 : Reach 184607 := rs (se 1 (by rfl) ⟨138455, by rfl⟩) R276911
theorem R119081 : Reach 119081 := rs (se 2 (by rfl) ⟨44655, by rfl⟩) R89311
theorem R1790333 : Reach 1790333 := rs (se 3 (by rfl) ⟨335687, by rfl⟩) R671375
theorem R348553 : Reach 348553 := rs (se 2 (by rfl) ⟨130707, by rfl⟩) R261415
theorem R119351 : Reach 119351 := rs (se 1 (by rfl) ⟨89513, by rfl⟩) R179027
theorem R1004141 : Reach 1004141 := rs (se 3 (by rfl) ⟨188276, by rfl⟩) R376553
theorem R119711 : Reach 119711 := rs (se 1 (by rfl) ⟨89783, by rfl⟩) R179567
theorem R185327 : Reach 185327 := rs (se 1 (by rfl) ⟨138995, by rfl⟩) R277991
theorem R119903 : Reach 119903 := rs (se 1 (by rfl) ⟨89927, by rfl⟩) R179855
theorem R775291 : Reach 775291 := rs (se 1 (by rfl) ⟨581468, by rfl⟩) R1162937
theorem R119963 : Reach 119963 := rs (se 1 (by rfl) ⟨89972, by rfl⟩) R179945
theorem R185831 : Reach 185831 := rs (se 1 (by rfl) ⟨139373, by rfl⟩) R278747
theorem R185993 : Reach 185993 := rs (se 2 (by rfl) ⟨69747, by rfl⟩) R139495
theorem R186011 : Reach 186011 := rs (se 1 (by rfl) ⟨139508, by rfl⟩) R279017
theorem R186143 : Reach 186143 := rs (se 1 (by rfl) ⟨139607, by rfl⟩) R279215
theorem R120647 : Reach 120647 := rs (se 1 (by rfl) ⟨90485, by rfl⟩) R180971
theorem R153427 : Reach 153427 := rs (se 1 (by rfl) ⟨115070, by rfl⟩) R230141
theorem R186209 : Reach 186209 := rs (se 2 (by rfl) ⟨69828, by rfl⟩) R139657
theorem R153569 : Reach 153569 := rs (se 2 (by rfl) ⟨57588, by rfl⟩) R115177
theorem R186407 : Reach 186407 := rs (se 1 (by rfl) ⟨139805, by rfl⟩) R279611
theorem R186587 : Reach 186587 := rs (se 1 (by rfl) ⟨139940, by rfl⟩) R279881
theorem R2087279 : Reach 2087279 := rs (se 1 (by rfl) ⟨1565459, by rfl⟩) R3130919
theorem R121247 : Reach 121247 := rs (se 1 (by rfl) ⟨90935, by rfl⟩) R181871
theorem R186785 : Reach 186785 := rs (se 2 (by rfl) ⟨70044, by rfl⟩) R140089
theorem R121319 : Reach 121319 := rs (se 1 (by rfl) ⟨90989, by rfl⟩) R181979
theorem R186857 : Reach 186857 := rs (se 2 (by rfl) ⟨70071, by rfl⟩) R140143
theorem R122063 : Reach 122063 := rs (se 1 (by rfl) ⟨91547, by rfl⟩) R183095
theorem R122183 : Reach 122183 := rs (se 1 (by rfl) ⟨91637, by rfl⟩) R183275
theorem R122345 : Reach 122345 := rs (se 2 (by rfl) ⟨45879, by rfl⟩) R91759
theorem R155209 : Reach 155209 := rs (se 2 (by rfl) ⟨58203, by rfl⟩) R116407
theorem R122489 : Reach 122489 := rs (se 2 (by rfl) ⟨45933, by rfl⟩) R91867
theorem R89887 : Reach 89887 := rs (se 1 (by rfl) ⟨67415, by rfl⟩) R134831
theorem R941867 : Reach 941867 := rs (se 1 (by rfl) ⟨706400, by rfl⟩) R1412801
theorem R122735 : Reach 122735 := rs (se 1 (by rfl) ⟨92051, by rfl⟩) R184103
theorem R90319 : Reach 90319 := rs (se 1 (by rfl) ⟨67739, by rfl⟩) R135479
theorem R680399 : Reach 680399 := rs (se 1 (by rfl) ⟨510299, by rfl⟩) R1020599
theorem R123419 : Reach 123419 := rs (se 1 (by rfl) ⟨92564, by rfl⟩) R185129
theorem R123599 : Reach 123599 := rs (se 1 (by rfl) ⟨92699, by rfl⟩) R185399
theorem R123611 : Reach 123611 := rs (se 1 (by rfl) ⟨92708, by rfl⟩) R185417
theorem R779017 : Reach 779017 := rs (se 2 (by rfl) ⟨292131, by rfl⟩) R584263
theorem R1369061 : Reach 1369061 := rs (se 4 (by rfl) ⟨128349, by rfl⟩) R256699
theorem R1303595 : Reach 1303595 := rs (se 1 (by rfl) ⟨977696, by rfl⟩) R1955393
theorem R91183 : Reach 91183 := rs (se 1 (by rfl) ⟨68387, by rfl⟩) R136775
theorem R418931 : Reach 418931 := rs (se 1 (by rfl) ⟨314198, by rfl⟩) R628397
theorem R124025 : Reach 124025 := rs (se 2 (by rfl) ⟨46509, by rfl⟩) R93019
theorem R91327 : Reach 91327 := rs (se 1 (by rfl) ⟨68495, by rfl⟩) R136991
theorem R1402181 : Reach 1402181 := rs (se 4 (by rfl) ⟨131454, by rfl⟩) R262909
theorem R91471 : Reach 91471 := rs (se 1 (by rfl) ⟨68603, by rfl⟩) R137207
theorem R353819 : Reach 353819 := rs (se 1 (by rfl) ⟨265364, by rfl⟩) R530729
theorem R2713171 : Reach 2713171 := rs (se 1 (by rfl) ⟨2034878, by rfl⟩) R4069757
theorem R419741 : Reach 419741 := rs (se 3 (by rfl) ⟨78701, by rfl⟩) R157403
theorem R92191 : Reach 92191 := rs (se 1 (by rfl) ⟨69143, by rfl⟩) R138287
theorem R387281 : Reach 387281 := rs (se 2 (by rfl) ⟨145230, by rfl⟩) R290461
theorem R92443 : Reach 92443 := rs (se 1 (by rfl) ⟨69332, by rfl⟩) R138665
theorem R420551 : Reach 420551 := rs (se 1 (by rfl) ⟨315413, by rfl⟩) R630827
theorem R257879 : Reach 257879 := rs (se 1 (by rfl) ⟨193409, by rfl⟩) R386819
theorem R618625 : Reach 618625 := rs (se 2 (by rfl) ⟨231984, by rfl⟩) R463969
theorem R6025427 : Reach 6025427 := rs (se 1 (by rfl) ⟨4519070, by rfl⟩) R9038141
theorem R192775 : Reach 192775 := rs (se 1 (by rfl) ⟨144581, by rfl⟩) R289163
theorem R258329 : Reach 258329 := rs (se 2 (by rfl) ⟨96873, by rfl⟩) R193747
theorem R1044839 : Reach 1044839 := rs (se 1 (by rfl) ⟨783629, by rfl⟩) R1567259
theorem R193447 : Reach 193447 := rs (se 1 (by rfl) ⟨145085, by rfl⟩) R290171
theorem R1569719 : Reach 1569719 := rs (se 1 (by rfl) ⟨1177289, by rfl⟩) R2354579
theorem R422927 : Reach 422927 := rs (se 1 (by rfl) ⟨317195, by rfl⟩) R634391
theorem R227539 : Reach 227539 := rs (se 1 (by rfl) ⟨170654, by rfl⟩) R341309
theorem R97147 : Reach 97147 := rs (se 1 (by rfl) ⟨72860, by rfl⟩) R145721
theorem R1408427 : Reach 1408427 := rs (se 1 (by rfl) ⟨1056320, by rfl⟩) R2112641
theorem R228815 : Reach 228815 := rs (se 1 (by rfl) ⟨171611, by rfl⟩) R343223
theorem R163279 : Reach 163279 := rs (se 1 (by rfl) ⟨122459, by rfl⟩) R244919
theorem R131015 : Reach 131015 := rs (se 1 (by rfl) ⟨98261, by rfl⟩) R196523
theorem R164519 : Reach 164519 := rs (se 1 (by rfl) ⟨123389, by rfl⟩) R246779
theorem R100207 : Reach 100207 := rs (se 1 (by rfl) ⟨75155, by rfl⟩) R150311
theorem R1182599 : Reach 1182599 := rs (se 1 (by rfl) ⟨886949, by rfl⟩) R1773899
theorem R592859 : Reach 592859 := rs (se 1 (by rfl) ⟨444644, by rfl⟩) R889289
theorem R199675 : Reach 199675 := rs (se 1 (by rfl) ⟨149756, by rfl⟩) R299513
theorem R1051811 : Reach 1051811 := rs (se 1 (by rfl) ⟨788858, by rfl⟩) R1577717
theorem R298349 : Reach 298349 := rs (se 3 (by rfl) ⟨55940, by rfl⟩) R111881
theorem R232865 : Reach 232865 := rs (se 2 (by rfl) ⟨87324, by rfl⟩) R174649
theorem R102379 : Reach 102379 := rs (se 1 (by rfl) ⟨76784, by rfl⟩) R153569
theorem R135359 : Reach 135359 := rs (se 1 (by rfl) ⟨101519, by rfl⟩) R203039
theorem R201467 : Reach 201467 := rs (se 1 (by rfl) ⟨151100, by rfl⟩) R302201
theorem R135931 : Reach 135931 := rs (se 1 (by rfl) ⟨101948, by rfl⟩) R203897
theorem R496381 : Reach 496381 := rs (se 3 (by rfl) ⟨93071, by rfl⟩) R186143
theorem R627911 : Reach 627911 := rs (se 1 (by rfl) ⟨470933, by rfl⟩) R941867
theorem R824833 : Reach 824833 := rs (se 2 (by rfl) ⟨309312, by rfl⟩) R618625
theorem R268001 : Reach 268001 := rs (se 2 (by rfl) ⟨100500, by rfl⟩) R201001
theorem R464737 : Reach 464737 := rs (se 2 (by rfl) ⟨174276, by rfl⟩) R348553
theorem R202783 : Reach 202783 := rs (se 1 (by rfl) ⟨152087, by rfl⟩) R304175
theorem R235879 : Reach 235879 := rs (se 1 (by rfl) ⟨176909, by rfl⟩) R353819
theorem R465263 : Reach 465263 := rs (se 1 (by rfl) ⟨348947, by rfl⟩) R697895
theorem R1972673 : Reach 1972673 := rs (se 2 (by rfl) ⟨739752, by rfl⟩) R1479505
theorem R236641 : Reach 236641 := rs (se 2 (by rfl) ⟨88740, by rfl⟩) R177481
theorem R990323 : Reach 990323 := rs (se 1 (by rfl) ⟨742742, by rfl⟩) R1485485
theorem R793745 : Reach 793745 := rs (se 2 (by rfl) ⟨297654, by rfl⟩) R595309
theorem R138415 : Reach 138415 := rs (se 1 (by rfl) ⟨103811, by rfl⟩) R207623
theorem R269945 : Reach 269945 := rs (se 2 (by rfl) ⟨101229, by rfl⟩) R202459
theorem R269999 : Reach 269999 := rs (se 1 (by rfl) ⟨202499, by rfl⟩) R404999
theorem R204569 : Reach 204569 := rs (se 2 (by rfl) ⟨76713, by rfl⟩) R153427
theorem R139087 : Reach 139087 := rs (se 1 (by rfl) ⟨104315, by rfl⟩) R208631
theorem R171919 : Reach 171919 := rs (se 1 (by rfl) ⟨128939, by rfl⟩) R257879
theorem R270323 : Reach 270323 := rs (se 1 (by rfl) ⟨202742, by rfl⟩) R405485
theorem R172219 : Reach 172219 := rs (se 1 (by rfl) ⟨129164, by rfl⟩) R258329
theorem R696559 : Reach 696559 := rs (se 1 (by rfl) ⟨522419, by rfl⟩) R1044839
theorem R303385 : Reach 303385 := rs (se 2 (by rfl) ⟨113769, by rfl⟩) R227539
theorem R270863 : Reach 270863 := rs (se 1 (by rfl) ⟨203147, by rfl⟩) R406295
theorem R140123 : Reach 140123 := rs (se 1 (by rfl) ⟨105092, by rfl⟩) R210185
theorem R206327 : Reach 206327 := rs (se 1 (by rfl) ⟨154745, by rfl⟩) R309491
theorem R271943 : Reach 271943 := rs (se 1 (by rfl) ⟨203957, by rfl⟩) R407915
theorem R403055 : Reach 403055 := rs (se 1 (by rfl) ⟨302291, by rfl⟩) R604583
theorem R206945 : Reach 206945 := rs (se 2 (by rfl) ⟨77604, by rfl⟩) R155209
theorem R207319 : Reach 207319 := rs (se 1 (by rfl) ⟨155489, by rfl⟩) R310979
theorem R207755 : Reach 207755 := rs (se 1 (by rfl) ⟨155816, by rfl⟩) R311633
theorem R306119 : Reach 306119 := rs (se 1 (by rfl) ⟨229589, by rfl⟩) R459179
theorem R109675 : Reach 109675 := rs (se 1 (by rfl) ⟨82256, by rfl⟩) R164513
theorem R274535 : Reach 274535 := rs (se 1 (by rfl) ⟨205901, by rfl⟩) R411803
theorem R1355939 : Reach 1355939 := rs (se 1 (by rfl) ⟨1016954, by rfl⟩) R2033909
theorem R3617561 : Reach 3617561 := rs (se 2 (by rfl) ⟨1356585, by rfl⟩) R2713171
theorem R275357 : Reach 275357 := rs (se 3 (by rfl) ⟨51629, by rfl⟩) R103259
theorem R472027 : Reach 472027 := rs (se 1 (by rfl) ⟨354020, by rfl⟩) R708041
theorem R1749995 : Reach 1749995 := rs (se 1 (by rfl) ⟨1312496, by rfl⟩) R2624993
theorem R79231 : Reach 79231 := rs (se 1 (by rfl) ⟨59423, by rfl⟩) R118847
theorem R79387 : Reach 79387 := rs (se 1 (by rfl) ⟨59540, by rfl⟩) R119081
theorem R1193555 : Reach 1193555 := rs (se 1 (by rfl) ⟨895166, by rfl⟩) R1790333
theorem R79567 : Reach 79567 := rs (se 1 (by rfl) ⟨59675, by rfl⟩) R119351
theorem R669427 : Reach 669427 := rs (se 1 (by rfl) ⟨502070, by rfl⟩) R1004141
theorem R79807 : Reach 79807 := rs (se 1 (by rfl) ⟨59855, by rfl⟩) R119711
theorem R440255 : Reach 440255 := rs (se 1 (by rfl) ⟨330191, by rfl⟩) R660383
theorem R14956597 : Reach 14956597 := rs (se 5 (by rfl) ⟨701090, by rfl⟩) R1402181
theorem R79935 : Reach 79935 := rs (se 1 (by rfl) ⟨59951, by rfl⟩) R119903
theorem R79975 : Reach 79975 := rs (se 1 (by rfl) ⟨59981, by rfl⟩) R119963
theorem R112927 : Reach 112927 := rs (se 1 (by rfl) ⟨84695, by rfl⟩) R169391
theorem R80431 : Reach 80431 := rs (se 1 (by rfl) ⟨60323, by rfl⟩) R120647
theorem R1391519 : Reach 1391519 := rs (se 1 (by rfl) ⟨1043639, by rfl⟩) R2087279
theorem R113599 : Reach 113599 := rs (se 1 (by rfl) ⟨85199, by rfl⟩) R170399
theorem R80831 : Reach 80831 := rs (se 1 (by rfl) ⟨60623, by rfl⟩) R121247
theorem R80879 : Reach 80879 := rs (se 1 (by rfl) ⟨60659, by rfl⟩) R121319
theorem R179369 : Reach 179369 := rs (se 2 (by rfl) ⟨67263, by rfl⟩) R134527
theorem R81375 : Reach 81375 := rs (se 1 (by rfl) ⟨61031, by rfl⟩) R122063
theorem R1031717 : Reach 1031717 := rs (se 4 (by rfl) ⟨96723, by rfl⟩) R193447
theorem R81455 : Reach 81455 := rs (se 1 (by rfl) ⟨61091, by rfl⟩) R122183
theorem R81563 : Reach 81563 := rs (se 1 (by rfl) ⟨61172, by rfl⟩) R122345
theorem R81659 : Reach 81659 := rs (se 1 (by rfl) ⟨61244, by rfl⟩) R122489
theorem R278369 : Reach 278369 := rs (se 2 (by rfl) ⟨104388, by rfl⟩) R208777
theorem R81823 : Reach 81823 := rs (se 1 (by rfl) ⟨61367, by rfl⟩) R122735
theorem R180431 : Reach 180431 := rs (se 1 (by rfl) ⟨135323, by rfl⟩) R270647
theorem R82279 : Reach 82279 := rs (se 1 (by rfl) ⟨61709, by rfl⟩) R123419
theorem R377303 : Reach 377303 := rs (se 1 (by rfl) ⟨282977, by rfl⟩) R565955
theorem R82399 : Reach 82399 := rs (se 1 (by rfl) ⟨61799, by rfl⟩) R123599
theorem R82407 : Reach 82407 := rs (se 1 (by rfl) ⟨61805, by rfl⟩) R123611
theorem R869063 : Reach 869063 := rs (se 1 (by rfl) ⟨651797, by rfl⟩) R1303595
theorem R279287 : Reach 279287 := rs (se 1 (by rfl) ⟨209465, by rfl⟩) R418931
theorem R82683 : Reach 82683 := rs (se 1 (by rfl) ⟨62012, by rfl⟩) R124025
theorem R279827 : Reach 279827 := rs (se 1 (by rfl) ⟨209870, by rfl⟩) R419741
theorem R1033721 : Reach 1033721 := rs (se 2 (by rfl) ⟨387645, by rfl⟩) R775291
theorem R444167 : Reach 444167 := rs (se 1 (by rfl) ⟨333125, by rfl⟩) R666251
theorem R280367 : Reach 280367 := rs (se 1 (by rfl) ⟨210275, by rfl⟩) R420551
theorem R182249 : Reach 182249 := rs (se 2 (by rfl) ⟨68343, by rfl⟩) R136687
theorem R870821 : Reach 870821 := rs (se 4 (by rfl) ⟨81639, by rfl⟩) R163279
theorem R182735 : Reach 182735 := rs (se 1 (by rfl) ⟨137051, by rfl⟩) R274103
theorem R117227 : Reach 117227 := rs (se 1 (by rfl) ⟨87920, by rfl⟩) R175841
theorem R2017817 : Reach 2017817 := rs (se 2 (by rfl) ⟨756681, by rfl⟩) R1513363
theorem R182825 : Reach 182825 := rs (se 2 (by rfl) ⟨68559, by rfl⟩) R137119
theorem R4016951 : Reach 4016951 := rs (se 1 (by rfl) ⟨3012713, by rfl⟩) R6025427
theorem R2018533 : Reach 2018533 := rs (se 4 (by rfl) ⟨189237, by rfl⟩) R378475
theorem R412937 : Reach 412937 := rs (se 2 (by rfl) ⟨154851, by rfl⟩) R309703
theorem R281951 : Reach 281951 := rs (se 1 (by rfl) ⟨211463, by rfl⟩) R422927
theorem R183707 : Reach 183707 := rs (se 1 (by rfl) ⟨137780, by rfl⟩) R275561
theorem R118727 : Reach 118727 := rs (se 1 (by rfl) ⟨89045, by rfl⟩) R178091
theorem R118811 : Reach 118811 := rs (se 1 (by rfl) ⟨89108, by rfl⟩) R178217
theorem R3461291 : Reach 3461291 := rs (se 1 (by rfl) ⟨2595968, by rfl⟩) R5191937
theorem R119087 : Reach 119087 := rs (se 1 (by rfl) ⟨89315, by rfl⟩) R178631
theorem R119195 : Reach 119195 := rs (se 1 (by rfl) ⟨89396, by rfl⟩) R178793
theorem R119231 : Reach 119231 := rs (se 1 (by rfl) ⟨89423, by rfl⟩) R178847
theorem R119327 : Reach 119327 := rs (se 1 (by rfl) ⟨89495, by rfl⟩) R178991
theorem R119615 : Reach 119615 := rs (se 1 (by rfl) ⟨89711, by rfl⟩) R179423
theorem R185255 : Reach 185255 := rs (se 1 (by rfl) ⟨138941, by rfl⟩) R277883
theorem R938951 : Reach 938951 := rs (se 1 (by rfl) ⟨704213, by rfl⟩) R1408427
theorem R119759 : Reach 119759 := rs (se 1 (by rfl) ⟨89819, by rfl⟩) R179639
theorem R152543 : Reach 152543 := rs (se 1 (by rfl) ⟨114407, by rfl⟩) R228815
theorem R119849 : Reach 119849 := rs (se 2 (by rfl) ⟨44943, by rfl⟩) R89887
theorem R119879 : Reach 119879 := rs (se 1 (by rfl) ⟨89909, by rfl⟩) R179819
theorem R414881 : Reach 414881 := rs (se 2 (by rfl) ⟨155580, by rfl⟩) R311161
theorem R349373 : Reach 349373 := rs (se 3 (by rfl) ⟨65507, by rfl⟩) R131015
theorem R120059 : Reach 120059 := rs (se 1 (by rfl) ⟨90044, by rfl⟩) R180089
theorem R120119 : Reach 120119 := rs (se 1 (by rfl) ⟨90089, by rfl⟩) R180179
theorem R1660495 : Reach 1660495 := rs (se 1 (by rfl) ⟨1245371, by rfl⟩) R2490743
theorem R120425 : Reach 120425 := rs (se 2 (by rfl) ⟨45159, by rfl⟩) R90319
theorem R513863 : Reach 513863 := rs (se 1 (by rfl) ⟨385397, by rfl⟩) R770795
theorem R382915 : Reach 382915 := rs (se 1 (by rfl) ⟨287186, by rfl⟩) R574373
theorem R481261 : Reach 481261 := rs (se 3 (by rfl) ⟨90236, by rfl⟩) R180473
theorem R841711 : Reach 841711 := rs (se 1 (by rfl) ⟨631283, by rfl⟩) R1262567
theorem R120959 : Reach 120959 := rs (se 1 (by rfl) ⟨90719, by rfl⟩) R181439
theorem R121055 : Reach 121055 := rs (se 1 (by rfl) ⟨90791, by rfl⟩) R181583
theorem R121115 : Reach 121115 := rs (se 1 (by rfl) ⟨90836, by rfl⟩) R181673
theorem R1038689 : Reach 1038689 := rs (se 2 (by rfl) ⟨389508, by rfl⟩) R779017
theorem R121439 : Reach 121439 := rs (se 1 (by rfl) ⟨91079, by rfl⟩) R182159
theorem R121535 : Reach 121535 := rs (se 1 (by rfl) ⟨91151, by rfl⟩) R182303
theorem R1596125 : Reach 1596125 := rs (se 3 (by rfl) ⟨299273, by rfl⟩) R598547
theorem R121577 : Reach 121577 := rs (se 2 (by rfl) ⟨45591, by rfl⟩) R91183
theorem R940787 : Reach 940787 := rs (se 1 (by rfl) ⟨705590, by rfl⟩) R1411181
theorem R121703 : Reach 121703 := rs (se 1 (by rfl) ⟨91277, by rfl⟩) R182555
theorem R121769 : Reach 121769 := rs (se 2 (by rfl) ⟨45663, by rfl⟩) R91327
theorem R613331 : Reach 613331 := rs (se 1 (by rfl) ⟨459998, by rfl⟩) R919997
theorem R121919 : Reach 121919 := rs (se 1 (by rfl) ⟨91439, by rfl⟩) R182879
theorem R121961 : Reach 121961 := rs (se 2 (by rfl) ⟨45735, by rfl⟩) R91471
theorem R285905 : Reach 285905 := rs (se 2 (by rfl) ⟨107214, by rfl⟩) R214429
theorem R122087 : Reach 122087 := rs (se 1 (by rfl) ⟨91565, by rfl⟩) R183131
theorem R679337 : Reach 679337 := rs (se 2 (by rfl) ⟨254751, by rfl⟩) R509503
theorem R449975 : Reach 449975 := rs (se 1 (by rfl) ⟨337481, by rfl⟩) R674963
theorem R122591 : Reach 122591 := rs (se 1 (by rfl) ⟨91943, by rfl⟩) R183887
theorem R122921 : Reach 122921 := rs (se 2 (by rfl) ⟨46095, by rfl⟩) R92191
theorem R90175 : Reach 90175 := rs (se 1 (by rfl) ⟨67631, by rfl⟩) R135263
theorem R122951 : Reach 122951 := rs (se 1 (by rfl) ⟨92213, by rfl⟩) R184427
theorem R122987 : Reach 122987 := rs (se 1 (by rfl) ⟨92240, by rfl⟩) R184481
theorem R123071 : Reach 123071 := rs (se 1 (by rfl) ⟨92303, by rfl⟩) R184607
theorem R155839 : Reach 155839 := rs (se 1 (by rfl) ⟨116879, by rfl⟩) R233759
theorem R155945 : Reach 155945 := rs (se 2 (by rfl) ⟨58479, by rfl⟩) R116959
theorem R123257 : Reach 123257 := rs (se 2 (by rfl) ⟨46221, by rfl⟩) R92443
theorem R123551 : Reach 123551 := rs (se 1 (by rfl) ⟨92663, by rfl⟩) R185327
theorem R352927 : Reach 352927 := rs (se 1 (by rfl) ⟨264695, by rfl⟩) R529391
theorem R91039 : Reach 91039 := rs (se 1 (by rfl) ⟨68279, by rfl⟩) R136559
theorem R123887 : Reach 123887 := rs (se 1 (by rfl) ⟨92915, by rfl⟩) R185831
theorem R222203 : Reach 222203 := rs (se 1 (by rfl) ⟨166652, by rfl⟩) R333305
theorem R156667 : Reach 156667 := rs (se 1 (by rfl) ⟨117500, by rfl⟩) R235001
theorem R123995 : Reach 123995 := rs (se 1 (by rfl) ⟨92996, by rfl⟩) R185993
theorem R124007 : Reach 124007 := rs (se 1 (by rfl) ⟨93005, by rfl⟩) R186011
theorem R124139 : Reach 124139 := rs (se 1 (by rfl) ⟨93104, by rfl⟩) R186209
theorem R124271 : Reach 124271 := rs (se 1 (by rfl) ⟨93203, by rfl⟩) R186407
theorem R124391 : Reach 124391 := rs (se 1 (by rfl) ⟨93293, by rfl⟩) R186587
theorem R124523 : Reach 124523 := rs (se 1 (by rfl) ⟨93392, by rfl⟩) R186785
theorem R124571 : Reach 124571 := rs (se 1 (by rfl) ⟨93428, by rfl⟩) R186857
theorem R748379 : Reach 748379 := rs (se 1 (by rfl) ⟨561284, by rfl⟩) R1122569
theorem R453599 : Reach 453599 := rs (se 1 (by rfl) ⟨340199, by rfl⟩) R680399
theorem R257033 : Reach 257033 := rs (se 2 (by rfl) ⟨96387, by rfl⟩) R192775
theorem R912707 : Reach 912707 := rs (se 1 (by rfl) ⟨684530, by rfl⟩) R1369061
theorem R585305 : Reach 585305 := rs (se 2 (by rfl) ⟨219489, by rfl⟩) R438979
theorem R258187 : Reach 258187 := rs (se 1 (by rfl) ⟨193640, by rfl⟩) R387281
theorem R3633547 : Reach 3633547 := rs (se 1 (by rfl) ⟨2725160, by rfl⟩) R5450321
theorem R1046479 : Reach 1046479 := rs (se 1 (by rfl) ⟨784859, by rfl⟩) R1569719
theorem R129529 : Reach 129529 := rs (se 2 (by rfl) ⟨48573, by rfl⟩) R97147
theorem R228167 : Reach 228167 := rs (se 1 (by rfl) ⟨171125, by rfl⟩) R342251
theorem R229625 : Reach 229625 := rs (se 2 (by rfl) ⟨86109, by rfl⟩) R172219
theorem R689147 : Reach 689147 := rs (se 1 (by rfl) ⟨516860, by rfl⟩) R1033721
theorem R296111 : Reach 296111 := rs (se 1 (by rfl) ⟨222083, by rfl⟩) R444167
theorem R1345211 : Reach 1345211 := rs (se 1 (by rfl) ⟨1008908, by rfl⟩) R2017817
theorem R788399 : Reach 788399 := rs (se 1 (by rfl) ⟨591299, by rfl⟩) R1182599
theorem R395239 : Reach 395239 := rs (se 1 (by rfl) ⟨296429, by rfl⟩) R592859
theorem R198899 : Reach 198899 := rs (se 1 (by rfl) ⟨149174, by rfl⟩) R298349
theorem R133609 : Reach 133609 := rs (se 2 (by rfl) ⟨50103, by rfl⟩) R100207
theorem R592541 : Reach 592541 := rs (se 3 (by rfl) ⟨111101, by rfl⟩) R222203
theorem R134311 : Reach 134311 := rs (se 1 (by rfl) ⟨100733, by rfl⟩) R201467
theorem R625967 : Reach 625967 := rs (se 1 (by rfl) ⟨469475, by rfl⟩) R938951
theorem R692459 : Reach 692459 := rs (se 1 (by rfl) ⟨519344, by rfl⟩) R1038689
theorem R1315115 : Reach 1315115 := rs (se 1 (by rfl) ⟨986336, by rfl⟩) R1972673
theorem R2691377 : Reach 2691377 := rs (se 2 (by rfl) ⟨1009266, by rfl⟩) R2018533
theorem R627191 : Reach 627191 := rs (se 1 (by rfl) ⟨470393, by rfl⟩) R940787
theorem R660215 : Reach 660215 := rs (se 1 (by rfl) ⟨495161, by rfl⟩) R990323
theorem R529163 : Reach 529163 := rs (se 1 (by rfl) ⟨396872, by rfl⟩) R793745
theorem R136379 : Reach 136379 := rs (se 1 (by rfl) ⟨102284, by rfl⟩) R204569
theorem R136505 : Reach 136505 := rs (se 2 (by rfl) ⟨51189, by rfl⟩) R102379
theorem R137551 : Reach 137551 := rs (se 1 (by rfl) ⟨103163, by rfl⟩) R206327
theorem R661841 : Reach 661841 := rs (se 2 (by rfl) ⟨248190, by rfl⟩) R496381
theorem R268703 : Reach 268703 := rs (se 1 (by rfl) ⟨201527, by rfl⟩) R403055
theorem R629369 : Reach 629369 := rs (se 2 (by rfl) ⟨236013, by rfl⟩) R472027
theorem R137963 : Reach 137963 := rs (se 1 (by rfl) ⟨103472, by rfl⟩) R206945
theorem R498919 : Reach 498919 := rs (se 1 (by rfl) ⟨374189, by rfl⟩) R748379
theorem R138503 : Reach 138503 := rs (se 1 (by rfl) ⟨103877, by rfl⟩) R207755
theorem R204079 : Reach 204079 := rs (se 1 (by rfl) ⟨153059, by rfl⟩) R306119
theorem R302399 : Reach 302399 := rs (se 1 (by rfl) ⟨226799, by rfl⟩) R453599
theorem R1122281 : Reach 1122281 := rs (se 2 (by rfl) ⟨420855, by rfl⟩) R841711
theorem R270377 : Reach 270377 := rs (se 2 (by rfl) ⟨101391, by rfl⟩) R202783
theorem R172705 : Reach 172705 := rs (se 2 (by rfl) ⟨64764, by rfl⟩) R129529
theorem R795703 : Reach 795703 := rs (se 1 (by rfl) ⟨596777, by rfl⟩) R1193555
theorem R927679 : Reach 927679 := rs (se 1 (by rfl) ⟨695759, by rfl⟩) R1391519
theorem R207785 : Reach 207785 := rs (se 2 (by rfl) ⟨77919, by rfl⟩) R155839
theorem R928745 : Reach 928745 := rs (se 2 (by rfl) ⟨348279, by rfl⟩) R696559
theorem R404513 : Reach 404513 := rs (se 2 (by rfl) ⟨151692, by rfl⟩) R303385
theorem R109679 : Reach 109679 := rs (se 1 (by rfl) ⟨82259, by rfl⟩) R164519
theorem R470569 : Reach 470569 := rs (se 2 (by rfl) ⟨176463, by rfl⟩) R352927
theorem R208889 : Reach 208889 := rs (se 2 (by rfl) ⟨78333, by rfl⟩) R156667
theorem R1258021 : Reach 1258021 := rs (se 4 (by rfl) ⟨117939, by rfl⟩) R235879
theorem R701207 : Reach 701207 := rs (se 1 (by rfl) ⟨525905, by rfl⟩) R1051811
theorem R275291 : Reach 275291 := rs (se 1 (by rfl) ⟨206468, by rfl⟩) R412937
theorem R734285 : Reach 734285 := rs (se 3 (by rfl) ⟨137678, by rfl⟩) R275357
theorem R406781 : Reach 406781 := rs (se 3 (by rfl) ⟨76271, by rfl⟩) R152543
theorem R79151 : Reach 79151 := rs (se 1 (by rfl) ⟨59363, by rfl⟩) R118727
theorem R79207 : Reach 79207 := rs (se 1 (by rfl) ⟨59405, by rfl⟩) R118811
theorem R2307527 : Reach 2307527 := rs (se 1 (by rfl) ⟨1730645, by rfl⟩) R3461291
theorem R79391 : Reach 79391 := rs (se 1 (by rfl) ⟨59543, by rfl⟩) R119087
theorem R79463 : Reach 79463 := rs (se 1 (by rfl) ⟨59597, by rfl⟩) R119195
theorem R79487 : Reach 79487 := rs (se 1 (by rfl) ⟨59615, by rfl⟩) R119231
theorem R79551 : Reach 79551 := rs (se 1 (by rfl) ⟨59663, by rfl⟩) R119327
theorem R931661 : Reach 931661 := rs (se 3 (by rfl) ⟨174686, by rfl⟩) R349373
theorem R79743 : Reach 79743 := rs (se 1 (by rfl) ⟨59807, by rfl⟩) R119615
theorem R276425 : Reach 276425 := rs (se 2 (by rfl) ⟨103659, by rfl⟩) R207319
theorem R79839 : Reach 79839 := rs (se 1 (by rfl) ⟨59879, by rfl⟩) R119759
theorem R79899 : Reach 79899 := rs (se 1 (by rfl) ⟨59924, by rfl⟩) R119849
theorem R79919 : Reach 79919 := rs (se 1 (by rfl) ⟨59939, by rfl⟩) R119879
theorem R276587 : Reach 276587 := rs (se 1 (by rfl) ⟨207440, by rfl⟩) R414881
theorem R80039 : Reach 80039 := rs (se 1 (by rfl) ⟨60029, by rfl⟩) R120059
theorem R80079 : Reach 80079 := rs (se 1 (by rfl) ⟨60059, by rfl⟩) R120119
theorem R80283 : Reach 80283 := rs (se 1 (by rfl) ⟨60212, by rfl⟩) R120425
theorem R178667 : Reach 178667 := rs (se 1 (by rfl) ⟨134000, by rfl⟩) R268001
theorem R342575 : Reach 342575 := rs (se 1 (by rfl) ⟨256931, by rfl⟩) R513863
theorem R80639 : Reach 80639 := rs (se 1 (by rfl) ⟨60479, by rfl⟩) R120959
theorem R146233 : Reach 146233 := rs (se 2 (by rfl) ⟨54837, by rfl⟩) R109675
theorem R80703 : Reach 80703 := rs (se 1 (by rfl) ⟨60527, by rfl⟩) R121055
theorem R80743 : Reach 80743 := rs (se 1 (by rfl) ⟨60557, by rfl⟩) R121115
theorem R310175 : Reach 310175 := rs (se 1 (by rfl) ⟨232631, by rfl⟩) R465263
theorem R80959 : Reach 80959 := rs (se 1 (by rfl) ⟨60719, by rfl⟩) R121439
theorem R81023 : Reach 81023 := rs (se 1 (by rfl) ⟨60767, by rfl⟩) R121535
theorem R1064083 : Reach 1064083 := rs (se 1 (by rfl) ⟨798062, by rfl⟩) R1596125
theorem R81051 : Reach 81051 := rs (se 1 (by rfl) ⟨60788, by rfl⟩) R121577
theorem R81135 : Reach 81135 := rs (se 1 (by rfl) ⟨60851, by rfl⟩) R121703
theorem R81179 : Reach 81179 := rs (se 1 (by rfl) ⟨60884, by rfl⟩) R121769
theorem R408887 : Reach 408887 := rs (se 1 (by rfl) ⟨306665, by rfl⟩) R613331
theorem R81279 : Reach 81279 := rs (se 1 (by rfl) ⟨60959, by rfl⟩) R121919
theorem R81307 : Reach 81307 := rs (se 1 (by rfl) ⟨60980, by rfl⟩) R121961
theorem R81391 : Reach 81391 := rs (se 1 (by rfl) ⟨61043, by rfl⟩) R122087
theorem R179963 : Reach 179963 := rs (se 1 (by rfl) ⟨134972, by rfl⟩) R269945
theorem R179999 : Reach 179999 := rs (se 1 (by rfl) ⟨134999, by rfl⟩) R269999
theorem R81727 : Reach 81727 := rs (se 1 (by rfl) ⟨61295, by rfl⟩) R122591
theorem R1064933 : Reach 1064933 := rs (se 4 (by rfl) ⟨99837, by rfl⟩) R199675
theorem R180215 : Reach 180215 := rs (se 1 (by rfl) ⟨135161, by rfl⟩) R270323
theorem R81947 : Reach 81947 := rs (se 1 (by rfl) ⟨61460, by rfl⟩) R122921
theorem R81967 : Reach 81967 := rs (se 1 (by rfl) ⟨61475, by rfl⟩) R122951
theorem R81991 : Reach 81991 := rs (se 1 (by rfl) ⟨61493, by rfl⟩) R122987
theorem R82047 : Reach 82047 := rs (se 1 (by rfl) ⟨61535, by rfl⟩) R123071
theorem R344249 : Reach 344249 := rs (se 2 (by rfl) ⟨129093, by rfl⟩) R258187
theorem R82171 : Reach 82171 := rs (se 1 (by rfl) ⟨61628, by rfl⟩) R123257
theorem R180575 : Reach 180575 := rs (se 1 (by rfl) ⟨135431, by rfl⟩) R270863
theorem R82367 : Reach 82367 := rs (se 1 (by rfl) ⟨61775, by rfl⟩) R123551
theorem R82591 : Reach 82591 := rs (se 1 (by rfl) ⟨61943, by rfl⟩) R123887
theorem R82663 : Reach 82663 := rs (se 1 (by rfl) ⟨61997, by rfl⟩) R123995
theorem R82671 : Reach 82671 := rs (se 1 (by rfl) ⟨62003, by rfl⟩) R124007
theorem R82759 : Reach 82759 := rs (se 1 (by rfl) ⟨62069, by rfl⟩) R124139
theorem R82847 : Reach 82847 := rs (se 1 (by rfl) ⟨62135, by rfl⟩) R124271
theorem R82927 : Reach 82927 := rs (se 1 (by rfl) ⟨62195, by rfl⟩) R124391
theorem R181241 : Reach 181241 := rs (se 2 (by rfl) ⟨67965, by rfl⟩) R135931
theorem R181295 : Reach 181295 := rs (se 1 (by rfl) ⟨135971, by rfl⟩) R271943
theorem R83015 : Reach 83015 := rs (se 1 (by rfl) ⟨62261, by rfl⟩) R124523
theorem R83047 : Reach 83047 := rs (se 1 (by rfl) ⟨62285, by rfl⟩) R124571
theorem R312605 : Reach 312605 := rs (se 3 (by rfl) ⟨58613, by rfl⟩) R117227
theorem R1099777 : Reach 1099777 := rs (se 2 (by rfl) ⟨412416, by rfl⟩) R824833
theorem R2213993 : Reach 2213993 := rs (se 2 (by rfl) ⟨830247, by rfl⟩) R1660495
theorem R608471 : Reach 608471 := rs (se 1 (by rfl) ⟨456353, by rfl⟩) R912707
theorem R510553 : Reach 510553 := rs (se 2 (by rfl) ⟨191457, by rfl⟩) R382915
theorem R1395305 : Reach 1395305 := rs (se 2 (by rfl) ⟨523239, by rfl⟩) R1046479
theorem R641681 : Reach 641681 := rs (se 2 (by rfl) ⟨240630, by rfl⟩) R481261
theorem R183023 : Reach 183023 := rs (se 1 (by rfl) ⟨137267, by rfl⟩) R274535
theorem R19942129 : Reach 19942129 := rs (se 2 (by rfl) ⟨7478298, by rfl⟩) R14956597
theorem R903959 : Reach 903959 := rs (se 1 (by rfl) ⟨677969, by rfl⟩) R1355939
theorem R150569 : Reach 150569 := rs (se 2 (by rfl) ⟨56463, by rfl⟩) R112927
theorem R2411707 : Reach 2411707 := rs (se 1 (by rfl) ⟨1808780, by rfl⟩) R3617561
theorem R1166663 : Reach 1166663 := rs (se 1 (by rfl) ⟨874997, by rfl⟩) R1749995
theorem R1199933 : Reach 1199933 := rs (se 3 (by rfl) ⟨224987, by rfl⟩) R449975
theorem R151465 : Reach 151465 := rs (se 2 (by rfl) ⟨56799, by rfl⟩) R113599
theorem R315521 : Reach 315521 := rs (se 2 (by rfl) ⟨118320, by rfl⟩) R236641
theorem R184553 : Reach 184553 := rs (se 2 (by rfl) ⟨69207, by rfl⟩) R138415
theorem R741797 : Reach 741797 := rs (se 4 (by rfl) ⟨69543, by rfl⟩) R139087
theorem R152111 : Reach 152111 := rs (se 1 (by rfl) ⟨114083, by rfl⟩) R228167
theorem R119579 : Reach 119579 := rs (se 1 (by rfl) ⟨89684, by rfl⟩) R179369
theorem R185579 : Reach 185579 := rs (se 1 (by rfl) ⟨139184, by rfl⟩) R278369
theorem R120233 : Reach 120233 := rs (se 2 (by rfl) ⟨45087, by rfl⟩) R90175
theorem R120287 : Reach 120287 := rs (se 1 (by rfl) ⟨90215, by rfl⟩) R180431
theorem R186191 : Reach 186191 := rs (se 1 (by rfl) ⟨139643, by rfl⟩) R279287
theorem R415853 : Reach 415853 := rs (se 3 (by rfl) ⟨77972, by rfl⟩) R155945
theorem R186551 : Reach 186551 := rs (se 1 (by rfl) ⟨139913, by rfl⟩) R279827
theorem R186911 : Reach 186911 := rs (se 1 (by rfl) ⟨140183, by rfl⟩) R280367
theorem R121385 : Reach 121385 := rs (se 2 (by rfl) ⟨45519, by rfl⟩) R91039
theorem R1006141 : Reach 1006141 := rs (se 3 (by rfl) ⟨188651, by rfl⟩) R377303
theorem R121499 : Reach 121499 := rs (se 1 (by rfl) ⟨91124, by rfl⟩) R182249
theorem R580547 : Reach 580547 := rs (se 1 (by rfl) ⟨435410, by rfl⟩) R870821
theorem R121823 : Reach 121823 := rs (se 1 (by rfl) ⟨91367, by rfl⟩) R182735
theorem R121883 : Reach 121883 := rs (se 1 (by rfl) ⟨91412, by rfl⟩) R182825
theorem R2317501 : Reach 2317501 := rs (se 3 (by rfl) ⟨434531, by rfl⟩) R869063
theorem R2677967 : Reach 2677967 := rs (se 1 (by rfl) ⟨2008475, by rfl⟩) R4016951
theorem R187967 : Reach 187967 := rs (se 1 (by rfl) ⟨140975, by rfl⟩) R281951
theorem R122471 : Reach 122471 := rs (se 1 (by rfl) ⟨91853, by rfl⟩) R183707
theorem R155243 : Reach 155243 := rs (se 1 (by rfl) ⟨116432, by rfl⟩) R232865
theorem R90239 : Reach 90239 := rs (se 1 (by rfl) ⟨67679, by rfl⟩) R135359
theorem R123503 : Reach 123503 := rs (se 1 (by rfl) ⟨92627, by rfl⟩) R185255
theorem R418607 : Reach 418607 := rs (se 1 (by rfl) ⟨313955, by rfl⟩) R627911
theorem R190603 : Reach 190603 := rs (se 1 (by rfl) ⟨142952, by rfl⟩) R285905
theorem R452891 : Reach 452891 := rs (se 1 (by rfl) ⟨339668, by rfl⟩) R679337
theorem R4844729 : Reach 4844729 := rs (se 2 (by rfl) ⟨1816773, by rfl⟩) R3633547
theorem R93415 : Reach 93415 := rs (se 1 (by rfl) ⟨70061, by rfl⟩) R140123
theorem R323837 : Reach 323837 := rs (se 3 (by rfl) ⟨60719, by rfl⟩) R121439
theorem R390203 : Reach 390203 := rs (se 1 (by rfl) ⟨292652, by rfl⟩) R585305
theorem R619649 : Reach 619649 := rs (se 2 (by rfl) ⟨232368, by rfl⟩) R464737
theorem R685421 : Reach 685421 := rs (se 3 (by rfl) ⟨128516, by rfl⟩) R257033
theorem R3570277 : Reach 3570277 := rs (se 4 (by rfl) ⟨334713, by rfl⟩) R669427
theorem R293503 : Reach 293503 := rs (se 1 (by rfl) ⟨220127, by rfl⟩) R440255
theorem R687811 : Reach 687811 := rs (se 1 (by rfl) ⟨515858, by rfl⟩) R1031717
theorem R229225 : Reach 229225 := rs (se 2 (by rfl) ⟨85959, by rfl⟩) R171919
theorem R229499 : Reach 229499 := rs (se 1 (by rfl) ⟨172124, by rfl⟩) R344249
theorem R459431 : Reach 459431 := rs (se 1 (by rfl) ⟨344573, by rfl⟩) R689147
theorem R197407 : Reach 197407 := rs (se 1 (by rfl) ⟨148055, by rfl⟩) R296111
theorem R230273 : Reach 230273 := rs (se 2 (by rfl) ⟨86352, by rfl⟩) R172705
theorem R525599 : Reach 525599 := rs (se 1 (by rfl) ⟨394199, by rfl⟩) R788399
theorem R1475995 : Reach 1475995 := rs (se 1 (by rfl) ⟨1106996, by rfl⟩) R2213993
theorem R132599 : Reach 132599 := rs (se 1 (by rfl) ⟨99449, by rfl⟩) R198899
theorem R427787 : Reach 427787 := rs (se 1 (by rfl) ⟨320840, by rfl⟩) R641681
theorem R395027 : Reach 395027 := rs (se 1 (by rfl) ⟨296270, by rfl⟩) R592541
theorem R100379 : Reach 100379 := rs (se 1 (by rfl) ⟨75284, by rfl⟩) R150569
theorem R526985 : Reach 526985 := rs (se 2 (by rfl) ⟨197619, by rfl⟩) R395239
theorem R461639 : Reach 461639 := rs (se 1 (by rfl) ⟨346229, by rfl⟩) R692459
theorem R494531 : Reach 494531 := rs (se 1 (by rfl) ⟨370898, by rfl⟩) R741797
theorem R101407 : Reach 101407 := rs (se 1 (by rfl) ⟨76055, by rfl⟩) R152111
theorem R3215609 : Reach 3215609 := rs (se 2 (by rfl) ⟨1205853, by rfl⟩) R2411707
theorem R627425 : Reach 627425 := rs (se 2 (by rfl) ⟨235284, by rfl⟩) R470569
theorem R201599 : Reach 201599 := rs (se 1 (by rfl) ⟨151199, by rfl⟩) R302399
theorem R201953 : Reach 201953 := rs (se 2 (by rfl) ⟨75732, by rfl⟩) R151465
theorem R1677361 : Reach 1677361 := rs (se 2 (by rfl) ⟨629010, by rfl⟩) R1258021
theorem R301927 : Reach 301927 := rs (se 1 (by rfl) ⟨226445, by rfl⟩) R452891
theorem R138523 : Reach 138523 := rs (se 1 (by rfl) ⟨103892, by rfl⟩) R207785
theorem R269675 : Reach 269675 := rs (se 1 (by rfl) ⟨202256, by rfl⟩) R404513
theorem R139259 : Reach 139259 := rs (se 1 (by rfl) ⟨104444, by rfl⟩) R208889
theorem R12919277 : Reach 12919277 := rs (se 3 (by rfl) ⟨2422364, by rfl⟩) R4844729
theorem R467471 : Reach 467471 := rs (se 1 (by rfl) ⟨350603, by rfl⟩) R701207
theorem R4760369 : Reach 4760369 := rs (se 2 (by rfl) ⟨1785138, by rfl⟩) R3570277
theorem R271187 : Reach 271187 := rs (se 1 (by rfl) ⟨203390, by rfl⟩) R406781
theorem R501245 : Reach 501245 := rs (se 3 (by rfl) ⟨93983, by rfl⟩) R187967
theorem R1418777 : Reach 1418777 := rs (se 2 (by rfl) ⟨532041, by rfl⟩) R1064083
theorem R3090001 : Reach 3090001 := rs (se 2 (by rfl) ⟨1158750, by rfl⟩) R2317501
theorem R665225 : Reach 665225 := rs (se 2 (by rfl) ⟨249459, by rfl⟩) R498919
theorem R272105 : Reach 272105 := rs (se 2 (by rfl) ⟨102039, by rfl⟩) R204079
theorem R206783 : Reach 206783 := rs (se 1 (by rfl) ⟨155087, by rfl⟩) R310175
theorem R272591 : Reach 272591 := rs (se 1 (by rfl) ⟨204443, by rfl⟩) R408887
theorem R305633 : Reach 305633 := rs (se 2 (by rfl) ⟨114612, by rfl⟩) R229225
theorem R109561 : Reach 109561 := rs (se 2 (by rfl) ⟨41085, by rfl⟩) R82171
theorem R240637 : Reach 240637 := rs (se 3 (by rfl) ⟨45119, by rfl⟩) R90239
theorem R208403 : Reach 208403 := rs (se 1 (by rfl) ⟨156302, by rfl⟩) R312605
theorem R896807 : Reach 896807 := rs (se 1 (by rfl) ⟨672605, by rfl⟩) R1345211
theorem R1060937 : Reach 1060937 := rs (se 2 (by rfl) ⟨397851, by rfl⟩) R795703
theorem R405647 : Reach 405647 := rs (se 1 (by rfl) ⟨304235, by rfl⟩) R608471
theorem R930203 : Reach 930203 := rs (se 1 (by rfl) ⟨697652, by rfl⟩) R1395305
theorem R602639 : Reach 602639 := rs (se 1 (by rfl) ⟨451979, by rfl⟩) R903959
theorem R799955 : Reach 799955 := rs (se 1 (by rfl) ⟨599966, by rfl⟩) R1199933
theorem R210347 : Reach 210347 := rs (se 1 (by rfl) ⟨157760, by rfl⟩) R315521
theorem R440143 : Reach 440143 := rs (se 1 (by rfl) ⟨330107, by rfl⟩) R660215
theorem R79719 : Reach 79719 := rs (se 1 (by rfl) ⟨59789, by rfl⟩) R119579
theorem R178145 : Reach 178145 := rs (se 2 (by rfl) ⟨66804, by rfl⟩) R133609
theorem R80155 : Reach 80155 := rs (se 1 (by rfl) ⟨60116, by rfl⟩) R120233
theorem R80191 : Reach 80191 := rs (se 1 (by rfl) ⟨60143, by rfl⟩) R120287
theorem R26589505 : Reach 26589505 := rs (se 2 (by rfl) ⟨9971064, by rfl⟩) R19942129
theorem R277235 : Reach 277235 := rs (se 1 (by rfl) ⟨207926, by rfl⟩) R415853
theorem R179081 : Reach 179081 := rs (se 2 (by rfl) ⟨67155, by rfl⟩) R134311
theorem R441227 : Reach 441227 := rs (se 1 (by rfl) ⟨330920, by rfl⟩) R661841
theorem R179135 : Reach 179135 := rs (se 1 (by rfl) ⟨134351, by rfl⟩) R268703
theorem R80923 : Reach 80923 := rs (se 1 (by rfl) ⟨60692, by rfl⟩) R121385
theorem R80999 : Reach 80999 := rs (se 1 (by rfl) ⟨60749, by rfl⟩) R121499
theorem R81215 : Reach 81215 := rs (se 1 (by rfl) ⟨60911, by rfl⟩) R121823
theorem R81255 : Reach 81255 := rs (se 1 (by rfl) ⟨60941, by rfl⟩) R121883
theorem R1785311 : Reach 1785311 := rs (se 1 (by rfl) ⟨1338983, by rfl⟩) R2677967
theorem R81647 : Reach 81647 := rs (se 1 (by rfl) ⟨61235, by rfl⟩) R122471
theorem R180251 : Reach 180251 := rs (se 1 (by rfl) ⟨135188, by rfl⟩) R270377
theorem R82335 : Reach 82335 := rs (se 1 (by rfl) ⟨61751, by rfl⟩) R123503
theorem R279071 : Reach 279071 := rs (se 1 (by rfl) ⟨209303, by rfl⟩) R418607
theorem R215891 : Reach 215891 := rs (se 1 (by rfl) ⟨161918, by rfl⟩) R323837
theorem R183401 : Reach 183401 := rs (se 2 (by rfl) ⟨68775, by rfl⟩) R137551
theorem R183527 : Reach 183527 := rs (se 1 (by rfl) ⟨137645, by rfl⟩) R275291
theorem R413099 : Reach 413099 := rs (se 1 (by rfl) ⟨309824, by rfl⟩) R619649
theorem R184283 : Reach 184283 := rs (se 1 (by rfl) ⟨138212, by rfl⟩) R276425
theorem R184391 : Reach 184391 := rs (se 1 (by rfl) ⟨138293, by rfl⟩) R276587
theorem R413981 : Reach 413981 := rs (se 3 (by rfl) ⟨77621, by rfl⟩) R155243
theorem R119111 : Reach 119111 := rs (se 1 (by rfl) ⟨89333, by rfl⟩) R178667
theorem R119975 : Reach 119975 := rs (se 1 (by rfl) ⟨89981, by rfl⟩) R179963
theorem R119999 : Reach 119999 := rs (se 1 (by rfl) ⟨89999, by rfl⟩) R179999
theorem R709955 : Reach 709955 := rs (se 1 (by rfl) ⟨532466, by rfl⟩) R1064933
theorem R120143 : Reach 120143 := rs (se 1 (by rfl) ⟨90107, by rfl⟩) R180215
theorem R153083 : Reach 153083 := rs (se 1 (by rfl) ⟨114812, by rfl⟩) R229625
theorem R120383 : Reach 120383 := rs (se 1 (by rfl) ⟨90287, by rfl⟩) R180575
theorem R120827 : Reach 120827 := rs (se 1 (by rfl) ⟨90620, by rfl⟩) R181241
theorem R120863 : Reach 120863 := rs (se 1 (by rfl) ⟨90647, by rfl⟩) R181295
theorem R1169909 : Reach 1169909 := rs (se 5 (by rfl) ⟨54839, by rfl⟩) R109679
theorem R122015 : Reach 122015 := rs (se 1 (by rfl) ⟨91511, by rfl⟩) R183023
theorem R417311 : Reach 417311 := rs (se 1 (by rfl) ⟨312983, by rfl⟩) R625967
theorem R777775 : Reach 777775 := rs (se 1 (by rfl) ⟨583331, by rfl⟩) R1166663
theorem R1236905 : Reach 1236905 := rs (se 2 (by rfl) ⟨463839, by rfl⟩) R927679
theorem R1466369 : Reach 1466369 := rs (se 2 (by rfl) ⟨549888, by rfl⟩) R1099777
theorem R123035 : Reach 123035 := rs (se 1 (by rfl) ⟨92276, by rfl⟩) R184553
theorem R254137 : Reach 254137 := rs (se 2 (by rfl) ⟨95301, by rfl⟩) R190603
theorem R876743 : Reach 876743 := rs (se 1 (by rfl) ⟨657557, by rfl⟩) R1315115
theorem R1794251 : Reach 1794251 := rs (se 1 (by rfl) ⟨1345688, by rfl⟩) R2691377
theorem R418127 : Reach 418127 := rs (se 1 (by rfl) ⟨313595, by rfl⟩) R627191
theorem R352775 : Reach 352775 := rs (se 1 (by rfl) ⟨264581, by rfl⟩) R529163
theorem R680737 : Reach 680737 := rs (se 2 (by rfl) ⟨255276, by rfl⟩) R510553
theorem R90919 : Reach 90919 := rs (se 1 (by rfl) ⟨68189, by rfl⟩) R136379
theorem R123719 : Reach 123719 := rs (se 1 (by rfl) ⟨92789, by rfl⟩) R185579
theorem R91003 : Reach 91003 := rs (se 1 (by rfl) ⟨68252, by rfl⟩) R136505
theorem R124127 : Reach 124127 := rs (se 1 (by rfl) ⟨93095, by rfl⟩) R186191
theorem R124367 : Reach 124367 := rs (se 1 (by rfl) ⟨93275, by rfl⟩) R186551
theorem R124553 : Reach 124553 := rs (se 2 (by rfl) ⟨46707, by rfl⟩) R93415
theorem R124607 : Reach 124607 := rs (se 1 (by rfl) ⟨93455, by rfl⟩) R186911
theorem R419579 : Reach 419579 := rs (se 1 (by rfl) ⟨314684, by rfl⟩) R629369
theorem R91975 : Reach 91975 := rs (se 1 (by rfl) ⟨68981, by rfl⟩) R137963
theorem R387031 : Reach 387031 := rs (se 1 (by rfl) ⟨290273, by rfl⟩) R580547
theorem R92335 : Reach 92335 := rs (se 1 (by rfl) ⟨69251, by rfl⟩) R138503
theorem R748187 : Reach 748187 := rs (se 1 (by rfl) ⟨561140, by rfl⟩) R1122281
theorem R323693 : Reach 323693 := rs (se 3 (by rfl) ⟨60692, by rfl⟩) R121385
theorem R619163 : Reach 619163 := rs (se 1 (by rfl) ⟨464372, by rfl⟩) R928745
theorem R260135 : Reach 260135 := rs (se 1 (by rfl) ⟨195101, by rfl⟩) R390203
theorem R489523 : Reach 489523 := rs (se 1 (by rfl) ⟨367142, by rfl⟩) R734285
theorem R1341521 : Reach 1341521 := rs (se 2 (by rfl) ⟨503070, by rfl⟩) R1006141
theorem R391337 : Reach 391337 := rs (se 2 (by rfl) ⟨146751, by rfl⟩) R293503
theorem R456947 : Reach 456947 := rs (se 1 (by rfl) ⟨342710, by rfl⟩) R685421
theorem R1538351 : Reach 1538351 := rs (se 1 (by rfl) ⟨1153763, by rfl⟩) R2307527
theorem R194977 : Reach 194977 := rs (se 2 (by rfl) ⟨73116, by rfl⟩) R146233
theorem R621107 : Reach 621107 := rs (se 1 (by rfl) ⟨465830, by rfl⟩) R931661
theorem R228383 : Reach 228383 := rs (se 1 (by rfl) ⟨171287, by rfl⟩) R342575
theorem R917081 : Reach 917081 := rs (se 2 (by rfl) ⟨343905, by rfl⟩) R687811
theorem R1115005 : Reach 1115005 := rs (se 3 (by rfl) ⟨209063, by rfl⟩) R418127
theorem R263351 : Reach 263351 := rs (se 1 (by rfl) ⟨197513, by rfl⟩) R395027
theorem R1967993 : Reach 1967993 := rs (se 2 (by rfl) ⟨737997, by rfl⟩) R1475995
theorem R329687 : Reach 329687 := rs (se 1 (by rfl) ⟨247265, by rfl⟩) R494531
theorem R134399 : Reach 134399 := rs (se 1 (by rfl) ⟨100799, by rfl⟩) R201599
theorem R134635 : Reach 134635 := rs (se 1 (by rfl) ⟨100976, by rfl⟩) R201953
theorem R102055 : Reach 102055 := rs (se 1 (by rfl) ⟨76541, by rfl⟩) R153083
theorem R135209 : Reach 135209 := rs (se 2 (by rfl) ⟨50703, by rfl⟩) R101407
theorem R1052837 : Reach 1052837 := rs (se 4 (by rfl) ⟨98703, by rfl⟩) R197407
theorem R824603 : Reach 824603 := rs (se 1 (by rfl) ⟨618452, by rfl⟩) R1236905
theorem R267677 : Reach 267677 := rs (se 3 (by rfl) ⟨50189, by rfl⟩) R100379
theorem R235183 : Reach 235183 := rs (se 1 (by rfl) ⟨176387, by rfl⟩) R352775
theorem R334163 : Reach 334163 := rs (se 1 (by rfl) ⟨250622, by rfl⟩) R501245
theorem R137855 : Reach 137855 := rs (se 1 (by rfl) ⟨103391, by rfl⟩) R206783
theorem R203755 : Reach 203755 := rs (se 1 (by rfl) ⟨152816, by rfl⟩) R305633
theorem R498791 : Reach 498791 := rs (se 1 (by rfl) ⟨374093, by rfl⟩) R748187
theorem R138935 : Reach 138935 := rs (se 1 (by rfl) ⟨104201, by rfl⟩) R208403
theorem R597871 : Reach 597871 := rs (se 1 (by rfl) ⟨448403, by rfl⟩) R896807
theorem R2236481 : Reach 2236481 := rs (se 2 (by rfl) ⟨838680, by rfl⟩) R1677361
theorem R270431 : Reach 270431 := rs (se 1 (by rfl) ⟨202823, by rfl⟩) R405647
theorem R401759 : Reach 401759 := rs (se 1 (by rfl) ⟨301319, by rfl⟩) R602639
theorem R533303 : Reach 533303 := rs (se 1 (by rfl) ⟨399977, by rfl⟩) R799955
theorem R140231 : Reach 140231 := rs (se 1 (by rfl) ⟨105173, by rfl⟩) R210347
theorem R402569 : Reach 402569 := rs (se 2 (by rfl) ⟨150963, by rfl⟩) R301927
theorem R173423 : Reach 173423 := rs (se 1 (by rfl) ⟨130067, by rfl⟩) R260135
theorem R894347 : Reach 894347 := rs (se 1 (by rfl) ⟨670760, by rfl⟩) R1341521
theorem R304631 : Reach 304631 := rs (se 1 (by rfl) ⟨228473, by rfl⟩) R456947
theorem R1025567 : Reach 1025567 := rs (se 1 (by rfl) ⟨769175, by rfl⟩) R1538351
theorem R1190207 : Reach 1190207 := rs (se 1 (by rfl) ⟨892655, by rfl⟩) R1785311
theorem R338849 : Reach 338849 := rs (se 2 (by rfl) ⟨127068, by rfl⟩) R254137
theorem R306287 : Reach 306287 := rs (se 1 (by rfl) ⟨229715, by rfl⟩) R459431
theorem R307759 : Reach 307759 := rs (se 1 (by rfl) ⟨230819, by rfl⟩) R461639
theorem R143927 : Reach 143927 := rs (se 1 (by rfl) ⟨107945, by rfl⟩) R215891
theorem R275399 : Reach 275399 := rs (se 1 (by rfl) ⟨206549, by rfl⟩) R413099
theorem R2143739 : Reach 2143739 := rs (se 1 (by rfl) ⟨1607804, by rfl⟩) R3215609
theorem R275987 : Reach 275987 := rs (se 1 (by rfl) ⟨206990, by rfl⟩) R413981
theorem R79407 : Reach 79407 := rs (se 1 (by rfl) ⟨59555, by rfl⟩) R119111
theorem R79983 : Reach 79983 := rs (se 1 (by rfl) ⟨59987, by rfl⟩) R119975
theorem R79999 : Reach 79999 := rs (se 1 (by rfl) ⟨59999, by rfl⟩) R119999
theorem R473303 : Reach 473303 := rs (se 1 (by rfl) ⟨354977, by rfl⟩) R709955
theorem R80095 : Reach 80095 := rs (se 1 (by rfl) ⟨60071, by rfl⟩) R120143
theorem R80255 : Reach 80255 := rs (se 1 (by rfl) ⟨60191, by rfl⟩) R120383
theorem R146081 : Reach 146081 := rs (se 2 (by rfl) ⟨54780, by rfl⟩) R109561
theorem R80551 : Reach 80551 := rs (se 1 (by rfl) ⟨60413, by rfl⟩) R120827
theorem R80575 : Reach 80575 := rs (se 1 (by rfl) ⟨60431, by rfl⟩) R120863
theorem R81343 : Reach 81343 := rs (se 1 (by rfl) ⟨61007, by rfl⟩) R122015
theorem R179783 : Reach 179783 := rs (se 1 (by rfl) ⟨134837, by rfl⟩) R269675
theorem R278207 : Reach 278207 := rs (se 1 (by rfl) ⟨208655, by rfl⟩) R417311
theorem R82023 : Reach 82023 := rs (se 1 (by rfl) ⟨61517, by rfl⟩) R123035
theorem R1196167 : Reach 1196167 := rs (se 1 (by rfl) ⟨897125, by rfl⟩) R1794251
theorem R311647 : Reach 311647 := rs (se 1 (by rfl) ⟨233735, by rfl⟩) R467471
theorem R82479 : Reach 82479 := rs (se 1 (by rfl) ⟨61859, by rfl⟩) R123719
theorem R180791 : Reach 180791 := rs (se 1 (by rfl) ⟨135593, by rfl⟩) R271187
theorem R82751 : Reach 82751 := rs (se 1 (by rfl) ⟨62063, by rfl⟩) R124127
theorem R82911 : Reach 82911 := rs (se 1 (by rfl) ⟨62183, by rfl⟩) R124367
theorem R443483 : Reach 443483 := rs (se 1 (by rfl) ⟨332612, by rfl⟩) R665225
theorem R83035 : Reach 83035 := rs (se 1 (by rfl) ⟨62276, by rfl⟩) R124553
theorem R83071 : Reach 83071 := rs (se 1 (by rfl) ⟨62303, by rfl⟩) R124607
theorem R181403 : Reach 181403 := rs (se 1 (by rfl) ⟨136052, by rfl⟩) R272105
theorem R279719 : Reach 279719 := rs (se 1 (by rfl) ⟨209789, by rfl⟩) R419579
theorem R181727 : Reach 181727 := rs (se 1 (by rfl) ⟨136295, by rfl⟩) R272591
theorem R1231037 : Reach 1231037 := rs (se 3 (by rfl) ⟨230819, by rfl⟩) R461639
theorem R707291 : Reach 707291 := rs (se 1 (by rfl) ⟨530468, by rfl⟩) R1060937
theorem R215795 : Reach 215795 := rs (se 1 (by rfl) ⟨161846, by rfl⟩) R323693
theorem R412775 : Reach 412775 := rs (se 1 (by rfl) ⟨309581, by rfl⟩) R619163
theorem R118763 : Reach 118763 := rs (se 1 (by rfl) ⟨89072, by rfl⟩) R178145
theorem R414071 : Reach 414071 := rs (se 1 (by rfl) ⟨310553, by rfl⟩) R621107
theorem R184697 : Reach 184697 := rs (se 2 (by rfl) ⟨69261, by rfl⟩) R138523
theorem R2347429 : Reach 2347429 := rs (se 4 (by rfl) ⟨220071, by rfl⟩) R440143
theorem R184823 : Reach 184823 := rs (se 1 (by rfl) ⟨138617, by rfl⟩) R277235
theorem R119387 : Reach 119387 := rs (se 1 (by rfl) ⟨89540, by rfl⟩) R179081
theorem R119423 : Reach 119423 := rs (se 1 (by rfl) ⟨89567, by rfl⟩) R179135
theorem R152255 : Reach 152255 := rs (se 1 (by rfl) ⟨114191, by rfl⟩) R228383
theorem R1037033 : Reach 1037033 := rs (se 2 (by rfl) ⟨388887, by rfl⟩) R777775
theorem R611387 : Reach 611387 := rs (se 1 (by rfl) ⟨458540, by rfl⟩) R917081
theorem R120167 : Reach 120167 := rs (se 1 (by rfl) ⟨90125, by rfl⟩) R180251
theorem R152999 : Reach 152999 := rs (se 1 (by rfl) ⟨114749, by rfl⟩) R229499
theorem R186047 : Reach 186047 := rs (se 1 (by rfl) ⟨139535, by rfl⟩) R279071
theorem R153515 : Reach 153515 := rs (se 1 (by rfl) ⟨115136, by rfl⟩) R230273
theorem R350399 : Reach 350399 := rs (se 1 (by rfl) ⟨262799, by rfl⟩) R525599
theorem R88399 : Reach 88399 := rs (se 1 (by rfl) ⟨66299, by rfl⟩) R132599
theorem R907649 : Reach 907649 := rs (se 2 (by rfl) ⟨340368, by rfl⟩) R680737
theorem R121225 : Reach 121225 := rs (se 2 (by rfl) ⟨45459, by rfl⟩) R90919
theorem R121337 : Reach 121337 := rs (se 2 (by rfl) ⟨45501, by rfl⟩) R91003
theorem R285191 : Reach 285191 := rs (se 1 (by rfl) ⟨213893, by rfl⟩) R427787
theorem R351323 : Reach 351323 := rs (se 1 (by rfl) ⟨263492, by rfl⟩) R526985
theorem R122267 : Reach 122267 := rs (se 1 (by rfl) ⟨91700, by rfl⟩) R183401
theorem R4120001 : Reach 4120001 := rs (se 2 (by rfl) ⟨1545000, by rfl⟩) R3090001
theorem R122351 : Reach 122351 := rs (se 1 (by rfl) ⟨91763, by rfl⟩) R183527
theorem R122633 : Reach 122633 := rs (se 2 (by rfl) ⟨45987, by rfl⟩) R91975
theorem R516041 : Reach 516041 := rs (se 2 (by rfl) ⟨193515, by rfl⟩) R387031
theorem R122855 : Reach 122855 := rs (se 1 (by rfl) ⟨92141, by rfl⟩) R184283
theorem R122927 : Reach 122927 := rs (se 1 (by rfl) ⟨92195, by rfl⟩) R184391
theorem R123113 : Reach 123113 := rs (se 2 (by rfl) ⟨46167, by rfl⟩) R92335
theorem R418283 : Reach 418283 := rs (se 1 (by rfl) ⟨313712, by rfl⟩) R627425
theorem R320849 : Reach 320849 := rs (se 2 (by rfl) ⟨120318, by rfl⟩) R240637
theorem R779939 : Reach 779939 := rs (se 1 (by rfl) ⟨584954, by rfl⟩) R1169909
theorem R92839 : Reach 92839 := rs (se 1 (by rfl) ⟨69629, by rfl⟩) R139259
theorem R977579 : Reach 977579 := rs (se 1 (by rfl) ⟨733184, by rfl⟩) R1466369
theorem R584495 : Reach 584495 := rs (se 1 (by rfl) ⟨438371, by rfl⟩) R876743
theorem R8612851 : Reach 8612851 := rs (se 1 (by rfl) ⟨6459638, by rfl⟩) R12919277
theorem R3173579 : Reach 3173579 := rs (se 1 (by rfl) ⟨2380184, by rfl⟩) R4760369
theorem R945851 : Reach 945851 := rs (se 1 (by rfl) ⟨709388, by rfl⟩) R1418777
theorem R1176605 : Reach 1176605 := rs (se 3 (by rfl) ⟨220613, by rfl⟩) R441227
theorem R652697 : Reach 652697 := rs (se 2 (by rfl) ⟨244761, by rfl⟩) R489523
theorem R620135 : Reach 620135 := rs (se 1 (by rfl) ⟨465101, by rfl⟩) R930203
theorem R35452673 : Reach 35452673 := rs (se 2 (by rfl) ⟨13294752, by rfl⟩) R26589505
theorem R259969 : Reach 259969 := rs (se 2 (by rfl) ⟨97488, by rfl⟩) R194977
theorem R260891 : Reach 260891 := rs (se 1 (by rfl) ⟨195668, by rfl⟩) R391337
theorem R295655 : Reach 295655 := rs (se 1 (by rfl) ⟨221741, by rfl⟩) R443483
theorem R1311995 : Reach 1311995 := rs (se 1 (by rfl) ⟨983996, by rfl⟩) R1967993
theorem R820691 : Reach 820691 := rs (se 1 (by rfl) ⟨615518, by rfl⟩) R1231037
theorem R101503 : Reach 101503 := rs (se 1 (by rfl) ⟨76127, by rfl⟩) R152255
theorem R691355 : Reach 691355 := rs (se 1 (by rfl) ⟨518516, by rfl⟩) R1037033
theorem R101999 : Reach 101999 := rs (se 1 (by rfl) ⟨76499, by rfl⟩) R152999
theorem R233599 : Reach 233599 := rs (se 1 (by rfl) ⟨175199, by rfl⟩) R350399
theorem R234215 : Reach 234215 := rs (se 1 (by rfl) ⟨175661, by rfl⟩) R351323
theorem R332527 : Reach 332527 := rs (se 1 (by rfl) ⟨249395, by rfl⟩) R498791
theorem R136073 : Reach 136073 := rs (se 2 (by rfl) ⟨51027, by rfl⟩) R102055
theorem R267839 : Reach 267839 := rs (se 1 (by rfl) ⟨200879, by rfl⟩) R401759
theorem R268379 : Reach 268379 := rs (se 1 (by rfl) ⟨201284, by rfl⟩) R402569
theorem R891101 : Reach 891101 := rs (se 3 (by rfl) ⟨167081, by rfl⟩) R334163
theorem R596231 : Reach 596231 := rs (se 1 (by rfl) ⟨447173, by rfl⟩) R894347
theorem R203087 : Reach 203087 := rs (se 1 (by rfl) ⟨152315, by rfl⟩) R304631
theorem R793471 : Reach 793471 := rs (se 1 (by rfl) ⟨595103, by rfl⟩) R1190207
theorem R204191 : Reach 204191 := rs (se 1 (by rfl) ⟨153143, by rfl⟩) R306287
theorem R435131 : Reach 435131 := rs (se 1 (by rfl) ⟨326348, by rfl⟩) R652697
theorem R23635115 : Reach 23635115 := rs (se 1 (by rfl) ⟨17726336, by rfl⟩) R35452673
theorem R271673 : Reach 271673 := rs (se 2 (by rfl) ⟨101877, by rfl⟩) R203755
theorem R173927 : Reach 173927 := rs (se 1 (by rfl) ⟨130445, by rfl⟩) R260891
theorem R3188645 : Reach 3188645 := rs (se 4 (by rfl) ⟨298935, by rfl⟩) R597871
theorem R1486673 : Reach 1486673 := rs (se 2 (by rfl) ⟨557502, by rfl⟩) R1115005
theorem R471527 : Reach 471527 := rs (se 1 (by rfl) ⟨353645, by rfl⟩) R707291
theorem R275183 : Reach 275183 := rs (se 1 (by rfl) ⟨206387, by rfl⟩) R412775
theorem R79175 : Reach 79175 := rs (se 1 (by rfl) ⟨59381, by rfl⟩) R118763
theorem R701891 : Reach 701891 := rs (se 1 (by rfl) ⟨526418, by rfl⟩) R1052837
theorem R276047 : Reach 276047 := rs (se 1 (by rfl) ⟨207035, by rfl⟩) R414071
theorem R8795765 : Reach 8795765 := rs (se 5 (by rfl) ⟨412301, by rfl⟩) R824603
theorem R79591 : Reach 79591 := rs (se 1 (by rfl) ⟨59693, by rfl⟩) R119387
theorem R79615 : Reach 79615 := rs (se 1 (by rfl) ⟨59711, by rfl⟩) R119423
theorem R702269 : Reach 702269 := rs (se 3 (by rfl) ⟨131675, by rfl⟩) R263351
theorem R407591 : Reach 407591 := rs (se 1 (by rfl) ⟨305693, by rfl⟩) R611387
theorem R80111 : Reach 80111 := rs (se 1 (by rfl) ⟨60083, by rfl⟩) R120167
theorem R178451 : Reach 178451 := rs (se 1 (by rfl) ⟨133838, by rfl⟩) R267677
theorem R11483801 : Reach 11483801 := rs (se 2 (by rfl) ⟨4306425, by rfl⟩) R8612851
theorem R605099 : Reach 605099 := rs (se 1 (by rfl) ⟨453824, by rfl⟩) R907649
theorem R80891 : Reach 80891 := rs (se 1 (by rfl) ⟨60668, by rfl⟩) R121337
theorem R179513 : Reach 179513 := rs (se 2 (by rfl) ⟨67317, by rfl⟩) R134635
theorem R81511 : Reach 81511 := rs (se 1 (by rfl) ⟨61133, by rfl⟩) R122267
theorem R81567 : Reach 81567 := rs (se 1 (by rfl) ⟨61175, by rfl⟩) R122351
theorem R409373 : Reach 409373 := rs (se 3 (by rfl) ⟨76757, by rfl⟩) R153515
theorem R81755 : Reach 81755 := rs (se 1 (by rfl) ⟨61316, by rfl⟩) R122633
theorem R344027 : Reach 344027 := rs (se 1 (by rfl) ⟨258020, by rfl⟩) R516041
theorem R81903 : Reach 81903 := rs (se 1 (by rfl) ⟨61427, by rfl⟩) R122855
theorem R81951 : Reach 81951 := rs (se 1 (by rfl) ⟨61463, by rfl⟩) R122927
theorem R1490987 : Reach 1490987 := rs (se 1 (by rfl) ⟨1118240, by rfl⟩) R2236481
theorem R180287 : Reach 180287 := rs (se 1 (by rfl) ⟨135215, by rfl⟩) R270431
theorem R82075 : Reach 82075 := rs (se 1 (by rfl) ⟨61556, by rfl⟩) R123113
theorem R278855 : Reach 278855 := rs (se 1 (by rfl) ⟨209141, by rfl⟩) R418283
theorem R442853 : Reach 442853 := rs (se 4 (by rfl) ⟨41517, by rfl⟩) R83035
theorem R3129905 : Reach 3129905 := rs (se 2 (by rfl) ⟨1173714, by rfl⟩) R2347429
theorem R1262141 : Reach 1262141 := rs (se 3 (by rfl) ⟨236651, by rfl⟩) R473303
theorem R410345 : Reach 410345 := rs (se 2 (by rfl) ⟨153879, by rfl⟩) R307759
theorem R213899 : Reach 213899 := rs (se 1 (by rfl) ⟨160424, by rfl⟩) R320849
theorem R115615 : Reach 115615 := rs (se 1 (by rfl) ⟨86711, by rfl⟩) R173423
theorem R575453 : Reach 575453 := rs (se 3 (by rfl) ⟨107897, by rfl⟩) R215795
theorem R2115719 : Reach 2115719 := rs (se 1 (by rfl) ⟨1586789, by rfl⟩) R3173579
theorem R313577 : Reach 313577 := rs (se 2 (by rfl) ⟨117591, by rfl⟩) R235183
theorem R346625 : Reach 346625 := rs (se 2 (by rfl) ⟨129984, by rfl⟩) R259969
theorem R117865 : Reach 117865 := rs (se 2 (by rfl) ⟨44199, by rfl⟩) R88399
theorem R183599 : Reach 183599 := rs (se 1 (by rfl) ⟨137699, by rfl⟩) R275399
theorem R1429159 : Reach 1429159 := rs (se 1 (by rfl) ⟨1071869, by rfl⟩) R2143739
theorem R183991 : Reach 183991 := rs (se 1 (by rfl) ⟨137993, by rfl⟩) R275987
theorem R413423 : Reach 413423 := rs (se 1 (by rfl) ⟨310067, by rfl⟩) R620135
theorem R315535 : Reach 315535 := rs (se 1 (by rfl) ⟨236651, by rfl⟩) R473303
theorem R119855 : Reach 119855 := rs (se 1 (by rfl) ⟨89891, by rfl⟩) R179783
theorem R185471 : Reach 185471 := rs (se 1 (by rfl) ⟨139103, by rfl⟩) R278207
theorem R1594889 : Reach 1594889 := rs (se 2 (by rfl) ⟨598083, by rfl⟩) R1196167
theorem R120527 : Reach 120527 := rs (se 1 (by rfl) ⟨90395, by rfl⟩) R180791
theorem R415529 : Reach 415529 := rs (se 2 (by rfl) ⟨155823, by rfl⟩) R311647
theorem R120935 : Reach 120935 := rs (se 1 (by rfl) ⟨90701, by rfl⟩) R181403
theorem R186479 : Reach 186479 := rs (se 1 (by rfl) ⟨139859, by rfl⟩) R279719
theorem R121151 : Reach 121151 := rs (se 1 (by rfl) ⟨90863, by rfl⟩) R181727
theorem R219791 : Reach 219791 := rs (se 1 (by rfl) ⟨164843, by rfl⟩) R329687
theorem R89599 : Reach 89599 := rs (se 1 (by rfl) ⟨67199, by rfl⟩) R134399
theorem R90139 : Reach 90139 := rs (se 1 (by rfl) ⟨67604, by rfl⟩) R135209
theorem R123131 : Reach 123131 := rs (se 1 (by rfl) ⟨92348, by rfl⟩) R184697
theorem R123215 : Reach 123215 := rs (se 1 (by rfl) ⟨92411, by rfl⟩) R184823
theorem R123785 : Reach 123785 := rs (se 2 (by rfl) ⟨46419, by rfl⟩) R92839
theorem R124031 : Reach 124031 := rs (se 1 (by rfl) ⟨93023, by rfl⟩) R186047
theorem R190127 : Reach 190127 := rs (se 1 (by rfl) ⟨142595, by rfl⟩) R285191
theorem R91903 : Reach 91903 := rs (se 1 (by rfl) ⟨68927, by rfl⟩) R137855
theorem R2746667 : Reach 2746667 := rs (se 1 (by rfl) ⟨2060000, by rfl⟩) R4120001
theorem R92623 : Reach 92623 := rs (se 1 (by rfl) ⟨69467, by rfl⟩) R138935
theorem R355535 : Reach 355535 := rs (se 1 (by rfl) ⟨266651, by rfl⟩) R533303
theorem R93487 : Reach 93487 := rs (se 1 (by rfl) ⟨70115, by rfl⟩) R140231
theorem R683711 : Reach 683711 := rs (se 1 (by rfl) ⟨512783, by rfl⟩) R1025567
theorem R519959 : Reach 519959 := rs (se 1 (by rfl) ⟨389969, by rfl⟩) R779939
theorem R389549 : Reach 389549 := rs (se 3 (by rfl) ⟨73040, by rfl⟩) R146081
theorem R651719 : Reach 651719 := rs (se 1 (by rfl) ⟨488789, by rfl⟩) R977579
theorem R389663 : Reach 389663 := rs (se 1 (by rfl) ⟨292247, by rfl⟩) R584495
theorem R225899 : Reach 225899 := rs (se 1 (by rfl) ⟨169424, by rfl⟩) R338849
theorem R95951 : Reach 95951 := rs (se 1 (by rfl) ⟨71963, by rfl⟩) R143927
theorem R161633 : Reach 161633 := rs (se 2 (by rfl) ⟨60612, by rfl⟩) R121225
theorem R784403 : Reach 784403 := rs (se 1 (by rfl) ⟨588302, by rfl⟩) R1176605
theorem R2522269 : Reach 2522269 := rs (se 3 (by rfl) ⟨472925, by rfl⟩) R945851
theorem R295235 : Reach 295235 := rs (se 1 (by rfl) ⟨221426, by rfl⟩) R442853
theorem R1410479 : Reach 1410479 := rs (se 1 (by rfl) ⟨1057859, by rfl⟩) R2115719
theorem R231083 : Reach 231083 := rs (se 1 (by rfl) ⟨173312, by rfl⟩) R346625
theorem R788413 : Reach 788413 := rs (se 3 (by rfl) ⟨147827, by rfl⟩) R295655
theorem R460903 : Reach 460903 := rs (se 1 (by rfl) ⟨345677, by rfl⟩) R691355
theorem R594067 : Reach 594067 := rs (se 1 (by rfl) ⟨445550, by rfl⟩) R891101
theorem R135337 : Reach 135337 := rs (se 2 (by rfl) ⟨50751, by rfl⟩) R101503
theorem R397487 : Reach 397487 := rs (se 1 (by rfl) ⟨298115, by rfl⟩) R596231
theorem R135391 : Reach 135391 := rs (se 1 (by rfl) ⟨101543, by rfl⟩) R203087
theorem R1905545 : Reach 1905545 := rs (se 2 (by rfl) ⟨714579, by rfl⟩) R1429159
theorem R431021 : Reach 431021 := rs (se 3 (by rfl) ⟨80816, by rfl⟩) R161633
theorem R463805 : Reach 463805 := rs (se 3 (by rfl) ⟨86963, by rfl⟩) R173927
theorem R136127 : Reach 136127 := rs (se 1 (by rfl) ⟨102095, by rfl⟩) R204191
theorem R237023 : Reach 237023 := rs (se 1 (by rfl) ⟨177767, by rfl⟩) R355535
theorem R991115 : Reach 991115 := rs (se 1 (by rfl) ⟨743336, by rfl⟩) R1486673
theorem R434479 : Reach 434479 := rs (se 1 (by rfl) ⟨325859, by rfl⟩) R651719
theorem R467927 : Reach 467927 := rs (se 1 (by rfl) ⟨350945, by rfl⟩) R701891
theorem R1057961 : Reach 1057961 := rs (se 2 (by rfl) ⟨396735, by rfl⟩) R793471
theorem R468179 : Reach 468179 := rs (se 1 (by rfl) ⟨351134, by rfl⟩) R702269
theorem R271727 : Reach 271727 := rs (se 1 (by rfl) ⟨203795, by rfl⟩) R407591
theorem R271997 : Reach 271997 := rs (se 3 (by rfl) ⟨50999, by rfl⟩) R101999
theorem R403399 : Reach 403399 := rs (se 1 (by rfl) ⟨302549, by rfl⟩) R605099
theorem R1386557 : Reach 1386557 := rs (se 3 (by rfl) ⟨259979, by rfl⟩) R519959
theorem R272915 : Reach 272915 := rs (se 1 (by rfl) ⟨204686, by rfl⟩) R409373
theorem R3975965 : Reach 3975965 := rs (se 3 (by rfl) ⟨745493, by rfl⟩) R1490987
theorem R273563 : Reach 273563 := rs (se 1 (by rfl) ⟨205172, by rfl⟩) R410345
theorem R209051 : Reach 209051 := rs (se 1 (by rfl) ⟨156788, by rfl⟩) R313577
theorem R570397 : Reach 570397 := rs (se 3 (by rfl) ⟨106949, by rfl⟩) R213899
theorem R275615 : Reach 275615 := rs (se 1 (by rfl) ⟨206711, by rfl⟩) R413423
theorem R79903 : Reach 79903 := rs (se 1 (by rfl) ⟨59927, by rfl⟩) R119855
theorem R1063259 : Reach 1063259 := rs (se 1 (by rfl) ⟨797444, by rfl⟩) R1594889
theorem R178559 : Reach 178559 := rs (se 1 (by rfl) ⟨133919, by rfl⟩) R267839
theorem R80351 : Reach 80351 := rs (se 1 (by rfl) ⟨60263, by rfl⟩) R120527
theorem R277019 : Reach 277019 := rs (se 1 (by rfl) ⟨207764, by rfl⟩) R415529
theorem R178919 : Reach 178919 := rs (se 1 (by rfl) ⟨134189, by rfl⟩) R268379
theorem R80623 : Reach 80623 := rs (se 1 (by rfl) ⟨60467, by rfl⟩) R120935
theorem R80767 : Reach 80767 := rs (se 1 (by rfl) ⟨60575, by rfl⟩) R121151
theorem R507005 : Reach 507005 := rs (se 3 (by rfl) ⟨95063, by rfl⟩) R190127
theorem R245321 : Reach 245321 := rs (se 2 (by rfl) ⟨91995, by rfl⟩) R183991
theorem R82087 : Reach 82087 := rs (se 1 (by rfl) ⟨61565, by rfl⟩) R123131
theorem R311465 : Reach 311465 := rs (se 2 (by rfl) ⟨116799, by rfl⟩) R233599
theorem R82143 : Reach 82143 := rs (se 1 (by rfl) ⟨61607, by rfl⟩) R123215
theorem R82523 : Reach 82523 := rs (se 1 (by rfl) ⟨61892, by rfl⟩) R123785
theorem R82687 : Reach 82687 := rs (se 1 (by rfl) ⟨62015, by rfl⟩) R124031
theorem R7324445 : Reach 7324445 := rs (se 3 (by rfl) ⟨1373333, by rfl⟩) R2746667
theorem R13452101 : Reach 13452101 := rs (se 4 (by rfl) ⟨1261134, by rfl⟩) R2522269
theorem R181115 : Reach 181115 := rs (se 1 (by rfl) ⟨135836, by rfl⟩) R271673
theorem R443369 : Reach 443369 := rs (se 2 (by rfl) ⟨166263, by rfl⟩) R332527
theorem R314351 : Reach 314351 := rs (se 1 (by rfl) ⟨235763, by rfl⟩) R471527
theorem R150599 : Reach 150599 := rs (se 1 (by rfl) ⟨112949, by rfl⟩) R225899
theorem R183455 : Reach 183455 := rs (se 1 (by rfl) ⟨137591, by rfl⟩) R275183
theorem R184031 : Reach 184031 := rs (se 1 (by rfl) ⟨138023, by rfl⟩) R276047
theorem R118967 : Reach 118967 := rs (se 1 (by rfl) ⟨89225, by rfl⟩) R178451
theorem R7655867 : Reach 7655867 := rs (se 1 (by rfl) ⟨5741900, by rfl⟩) R11483801
theorem R119465 : Reach 119465 := rs (se 2 (by rfl) ⟨44799, by rfl⟩) R89599
theorem R119675 : Reach 119675 := rs (se 1 (by rfl) ⟨89756, by rfl⟩) R179513
theorem R120185 : Reach 120185 := rs (se 2 (by rfl) ⟨45069, by rfl⟩) R90139
theorem R120191 : Reach 120191 := rs (se 1 (by rfl) ⟨90143, by rfl⟩) R180287
theorem R185903 : Reach 185903 := rs (se 1 (by rfl) ⟨139427, by rfl⟩) R278855
theorem R2086603 : Reach 2086603 := rs (se 1 (by rfl) ⟨1564952, by rfl⟩) R3129905
theorem R841427 : Reach 841427 := rs (se 1 (by rfl) ⟨631070, by rfl⟩) R1262141
theorem R547127 : Reach 547127 := rs (se 1 (by rfl) ⟨410345, by rfl⟩) R820691
theorem R154153 : Reach 154153 := rs (se 2 (by rfl) ⟨57807, by rfl⟩) R115615
theorem R383635 : Reach 383635 := rs (se 1 (by rfl) ⟨287726, by rfl⟩) R575453
theorem R122399 : Reach 122399 := rs (se 1 (by rfl) ⟨91799, by rfl⟩) R183599
theorem R122537 : Reach 122537 := rs (se 2 (by rfl) ⟨45951, by rfl⟩) R91903
theorem R156143 : Reach 156143 := rs (se 1 (by rfl) ⟨117107, by rfl⟩) R234215
theorem R90715 : Reach 90715 := rs (se 1 (by rfl) ⟨68036, by rfl⟩) R136073
theorem R123497 : Reach 123497 := rs (se 2 (by rfl) ⟨46311, by rfl⟩) R92623
theorem R3498653 : Reach 3498653 := rs (se 3 (by rfl) ⟨655997, by rfl⟩) R1311995
theorem R123647 : Reach 123647 := rs (se 1 (by rfl) ⟨92735, by rfl⟩) R185471
theorem R124319 : Reach 124319 := rs (se 1 (by rfl) ⟨93239, by rfl⟩) R186479
theorem R157153 : Reach 157153 := rs (se 2 (by rfl) ⟨58932, by rfl⟩) R117865
theorem R124649 : Reach 124649 := rs (se 2 (by rfl) ⟨46743, by rfl⟩) R93487
theorem R255869 : Reach 255869 := rs (se 3 (by rfl) ⟨47975, by rfl⟩) R95951
theorem R420713 : Reach 420713 := rs (se 2 (by rfl) ⟨157767, by rfl⟩) R315535
theorem R290087 : Reach 290087 := rs (se 1 (by rfl) ⟨217565, by rfl⟩) R435131
theorem R15756743 : Reach 15756743 := rs (se 1 (by rfl) ⟨11817557, by rfl⟩) R23635115
theorem R2125763 : Reach 2125763 := rs (se 1 (by rfl) ⟨1594322, by rfl⟩) R3188645
theorem R586109 : Reach 586109 := rs (se 3 (by rfl) ⟨109895, by rfl⟩) R219791
theorem R455807 : Reach 455807 := rs (se 1 (by rfl) ⟨341855, by rfl⟩) R683711
theorem R259699 : Reach 259699 := rs (se 1 (by rfl) ⟨194774, by rfl⟩) R389549
theorem R259775 : Reach 259775 := rs (se 1 (by rfl) ⟨194831, by rfl⟩) R389663
theorem R5863843 : Reach 5863843 := rs (se 1 (by rfl) ⟨4397882, by rfl⟩) R8795765
theorem R522935 : Reach 522935 := rs (se 1 (by rfl) ⟨392201, by rfl⟩) R784403
theorem R229351 : Reach 229351 := rs (se 1 (by rfl) ⟨172013, by rfl⟩) R344027
theorem R196823 : Reach 196823 := rs (se 1 (by rfl) ⟨147617, by rfl⟩) R295235
theorem R4882963 : Reach 4882963 := rs (se 1 (by rfl) ⟨3662222, by rfl⟩) R7324445
theorem R295579 : Reach 295579 := rs (se 1 (by rfl) ⟨221684, by rfl⟩) R443369
theorem R1051217 : Reach 1051217 := rs (se 2 (by rfl) ⟨394206, by rfl⟩) R788413
theorem R560951 : Reach 560951 := rs (se 1 (by rfl) ⟨420713, by rfl⟩) R841427
theorem R364751 : Reach 364751 := rs (se 1 (by rfl) ⟨273563, by rfl⟩) R547127
theorem R660743 : Reach 660743 := rs (se 1 (by rfl) ⟨495557, by rfl⟩) R991115
theorem R792089 : Reach 792089 := rs (se 2 (by rfl) ⟨297033, by rfl⟩) R594067
theorem R104095 : Reach 104095 := rs (se 1 (by rfl) ⟨78071, by rfl⟩) R156143
theorem R2332435 : Reach 2332435 := rs (se 1 (by rfl) ⟨1749326, by rfl⟩) R3498653
theorem R170579 : Reach 170579 := rs (se 1 (by rfl) ⟨127934, by rfl⟩) R255869
theorem R760529 : Reach 760529 := rs (se 2 (by rfl) ⟨285198, by rfl⟩) R570397
theorem R924371 : Reach 924371 := rs (se 1 (by rfl) ⟨693278, by rfl⟩) R1386557
theorem R1417175 : Reach 1417175 := rs (se 1 (by rfl) ⟨1062881, by rfl⟩) R2125763
theorem R139367 : Reach 139367 := rs (se 1 (by rfl) ⟨104525, by rfl⟩) R209051
theorem R401597 : Reach 401597 := rs (se 3 (by rfl) ⟨75299, by rfl⟩) R150599
theorem R205537 : Reach 205537 := rs (se 2 (by rfl) ⟨77076, by rfl⟩) R154153
theorem R303871 : Reach 303871 := rs (se 1 (by rfl) ⟨227903, by rfl⟩) R455807
theorem R173183 : Reach 173183 := rs (se 1 (by rfl) ⟨129887, by rfl⟩) R259775
theorem R338003 : Reach 338003 := rs (se 1 (by rfl) ⟨253502, by rfl⟩) R507005
theorem R305801 : Reach 305801 := rs (se 2 (by rfl) ⟨114675, by rfl⟩) R229351
theorem R207643 : Reach 207643 := rs (se 1 (by rfl) ⟨155732, by rfl⟩) R311465
theorem R1059965 : Reach 1059965 := rs (se 3 (by rfl) ⟨198743, by rfl⟩) R397487
theorem R209537 : Reach 209537 := rs (se 2 (by rfl) ⟨78576, by rfl⟩) R157153
theorem R209567 : Reach 209567 := rs (se 1 (by rfl) ⟨157175, by rfl⟩) R314351
theorem R79311 : Reach 79311 := rs (se 1 (by rfl) ⟨59483, by rfl⟩) R118967
theorem R79643 : Reach 79643 := rs (se 1 (by rfl) ⟨59732, by rfl⟩) R119465
theorem R79783 : Reach 79783 := rs (se 1 (by rfl) ⟨59837, by rfl⟩) R119675
theorem R309203 : Reach 309203 := rs (se 1 (by rfl) ⟨231902, by rfl⟩) R463805
theorem R2046053 : Reach 2046053 := rs (se 4 (by rfl) ⟨191817, by rfl⟩) R383635
theorem R80123 : Reach 80123 := rs (se 1 (by rfl) ⟨60092, by rfl⟩) R120185
theorem R80127 : Reach 80127 := rs (se 1 (by rfl) ⟨60095, by rfl⟩) R120191
theorem R81599 : Reach 81599 := rs (se 1 (by rfl) ⟨61199, by rfl⟩) R122399
theorem R81691 : Reach 81691 := rs (se 1 (by rfl) ⟨61268, by rfl⟩) R122537
theorem R180449 : Reach 180449 := rs (se 2 (by rfl) ⟨67668, by rfl⟩) R135337
theorem R180521 : Reach 180521 := rs (se 2 (by rfl) ⟨67695, by rfl⟩) R135391
theorem R82331 : Reach 82331 := rs (se 1 (by rfl) ⟨61748, by rfl⟩) R123497
theorem R82431 : Reach 82431 := rs (se 1 (by rfl) ⟨61823, by rfl⟩) R123647
theorem R311951 : Reach 311951 := rs (se 1 (by rfl) ⟨233963, by rfl⟩) R467927
theorem R705307 : Reach 705307 := rs (se 1 (by rfl) ⟨528980, by rfl⟩) R1057961
theorem R312119 : Reach 312119 := rs (se 1 (by rfl) ⟨234089, by rfl⟩) R468179
theorem R181151 : Reach 181151 := rs (se 1 (by rfl) ⟨135863, by rfl⟩) R271727
theorem R82879 : Reach 82879 := rs (se 1 (by rfl) ⟨62159, by rfl⟩) R124319
theorem R181331 : Reach 181331 := rs (se 1 (by rfl) ⟨135998, by rfl⟩) R271997
theorem R83099 : Reach 83099 := rs (se 1 (by rfl) ⟨62324, by rfl⟩) R124649
theorem R181943 : Reach 181943 := rs (se 1 (by rfl) ⟨136457, by rfl⟩) R272915
theorem R280475 : Reach 280475 := rs (se 1 (by rfl) ⟨210356, by rfl⟩) R420713
theorem R182375 : Reach 182375 := rs (se 1 (by rfl) ⟨136781, by rfl⟩) R273563
theorem R346265 : Reach 346265 := rs (se 2 (by rfl) ⟨129849, by rfl⟩) R259699
theorem R10504495 : Reach 10504495 := rs (se 1 (by rfl) ⟨7878371, by rfl⟩) R15756743
theorem R7818457 : Reach 7818457 := rs (se 2 (by rfl) ⟨2931921, by rfl⟩) R5863843
theorem R183743 : Reach 183743 := rs (se 1 (by rfl) ⟨137807, by rfl⟩) R275615
theorem R11128549 : Reach 11128549 := rs (se 4 (by rfl) ⟨1043301, by rfl⟩) R2086603
theorem R708839 : Reach 708839 := rs (se 1 (by rfl) ⟨531629, by rfl⟩) R1063259
theorem R119039 : Reach 119039 := rs (se 1 (by rfl) ⟨89279, by rfl⟩) R178559
theorem R184679 : Reach 184679 := rs (se 1 (by rfl) ⟨138509, by rfl⟩) R277019
theorem R348623 : Reach 348623 := rs (se 1 (by rfl) ⟨261467, by rfl⟩) R522935
theorem R119279 : Reach 119279 := rs (se 1 (by rfl) ⟨89459, by rfl⟩) R178919
theorem R2151461 : Reach 2151461 := rs (se 4 (by rfl) ⟨201699, by rfl⟩) R403399
theorem R579305 : Reach 579305 := rs (se 2 (by rfl) ⟨217239, by rfl⟩) R434479
theorem R8968067 : Reach 8968067 := rs (se 1 (by rfl) ⟨6726050, by rfl⟩) R13452101
theorem R120743 : Reach 120743 := rs (se 1 (by rfl) ⟨90557, by rfl⟩) R181115
theorem R120953 : Reach 120953 := rs (se 2 (by rfl) ⟨45357, by rfl⟩) R90715
theorem R940319 : Reach 940319 := rs (se 1 (by rfl) ⟨705239, by rfl⟩) R1410479
theorem R154055 : Reach 154055 := rs (se 1 (by rfl) ⟨115541, by rfl⟩) R231083
theorem R122303 : Reach 122303 := rs (se 1 (by rfl) ⟨91727, by rfl⟩) R183455
theorem R122687 : Reach 122687 := rs (se 1 (by rfl) ⟨92015, by rfl⟩) R184031
theorem R614537 : Reach 614537 := rs (se 2 (by rfl) ⟨230451, by rfl⟩) R460903
theorem R5103911 : Reach 5103911 := rs (se 1 (by rfl) ⟨3827933, by rfl⟩) R7655867
theorem R1270363 : Reach 1270363 := rs (se 1 (by rfl) ⟨952772, by rfl⟩) R1905545
theorem R287347 : Reach 287347 := rs (se 1 (by rfl) ⟨215510, by rfl⟩) R431021
theorem R90751 : Reach 90751 := rs (se 1 (by rfl) ⟨68063, by rfl⟩) R136127
theorem R123935 : Reach 123935 := rs (se 1 (by rfl) ⟨92951, by rfl⟩) R185903
theorem R158015 : Reach 158015 := rs (se 1 (by rfl) ⟨118511, by rfl⟩) R237023
theorem R2650643 : Reach 2650643 := rs (se 1 (by rfl) ⟨1987982, by rfl⟩) R3975965
theorem R193391 : Reach 193391 := rs (se 1 (by rfl) ⟨145043, by rfl⟩) R290087
theorem R390739 : Reach 390739 := rs (se 1 (by rfl) ⟨293054, by rfl⟩) R586109
theorem R163547 : Reach 163547 := rs (se 1 (by rfl) ⟨122660, by rfl⟩) R245321
theorem R131215 : Reach 131215 := rs (se 1 (by rfl) ⟨98411, by rfl⟩) R196823
theorem R394105 : Reach 394105 := rs (se 2 (by rfl) ⟨147789, by rfl⟩) R295579
theorem R230843 : Reach 230843 := rs (se 1 (by rfl) ⟨173132, by rfl⟩) R346265
theorem R232415 : Reach 232415 := rs (se 1 (by rfl) ⟨174311, by rfl⟩) R348623
theorem R461821 : Reach 461821 := rs (se 3 (by rfl) ⟨86591, by rfl⟩) R173183
theorem R528059 : Reach 528059 := rs (se 1 (by rfl) ⟨396044, by rfl⟩) R792089
theorem R626879 : Reach 626879 := rs (se 1 (by rfl) ⟨470159, by rfl⟩) R940319
theorem R10424609 : Reach 10424609 := rs (se 2 (by rfl) ⟨3909228, by rfl⟩) R7818457
theorem R102703 : Reach 102703 := rs (se 1 (by rfl) ⟨77027, by rfl⟩) R154055
theorem R267731 : Reach 267731 := rs (se 1 (by rfl) ⟨200798, by rfl⟩) R401597
theorem R203867 : Reach 203867 := rs (se 1 (by rfl) ⟨152900, by rfl⟩) R305801
theorem R138793 : Reach 138793 := rs (se 2 (by rfl) ⟨52047, by rfl⟩) R104095
theorem R139691 : Reach 139691 := rs (se 1 (by rfl) ⟨104768, by rfl⟩) R209537
theorem R139711 : Reach 139711 := rs (se 1 (by rfl) ⟨104783, by rfl⟩) R209567
theorem R206135 : Reach 206135 := rs (se 1 (by rfl) ⟨154601, by rfl⟩) R309203
theorem R109031 : Reach 109031 := rs (se 1 (by rfl) ⟨81773, by rfl⟩) R163547
theorem R207967 : Reach 207967 := rs (se 1 (by rfl) ⟨155975, by rfl⟩) R311951
theorem R208079 : Reach 208079 := rs (se 1 (by rfl) ⟨156059, by rfl⟩) R312119
theorem R274049 : Reach 274049 := rs (se 2 (by rfl) ⟨102768, by rfl⟩) R205537
theorem R405161 : Reach 405161 := rs (se 2 (by rfl) ⟨151935, by rfl⟩) R303871
theorem R700811 : Reach 700811 := rs (se 1 (by rfl) ⟨525608, by rfl⟩) R1051217
theorem R373967 : Reach 373967 := rs (se 1 (by rfl) ⟨280475, by rfl⟩) R560951
theorem R243167 : Reach 243167 := rs (se 1 (by rfl) ⟨182375, by rfl⟩) R364751
theorem R472559 : Reach 472559 := rs (se 1 (by rfl) ⟨354419, by rfl⟩) R708839
theorem R79359 : Reach 79359 := rs (se 1 (by rfl) ⟨59519, by rfl⟩) R119039
theorem R79519 : Reach 79519 := rs (se 1 (by rfl) ⟨59639, by rfl⟩) R119279
theorem R14005993 : Reach 14005993 := rs (se 2 (by rfl) ⟨5252247, by rfl⟩) R10504495
theorem R440495 : Reach 440495 := rs (se 1 (by rfl) ⟨330371, by rfl⟩) R660743
theorem R276857 : Reach 276857 := rs (se 2 (by rfl) ⟨103821, by rfl⟩) R207643
theorem R5978711 : Reach 5978711 := rs (se 1 (by rfl) ⟨4484033, by rfl⟩) R8968067
theorem R80495 : Reach 80495 := rs (se 1 (by rfl) ⟨60371, by rfl⟩) R120743
theorem R80635 : Reach 80635 := rs (se 1 (by rfl) ⟨60476, by rfl⟩) R120953
theorem R113719 : Reach 113719 := rs (se 1 (by rfl) ⟨85289, by rfl⟩) R170579
theorem R507019 : Reach 507019 := rs (se 1 (by rfl) ⟨380264, by rfl⟩) R760529
theorem R81535 : Reach 81535 := rs (se 1 (by rfl) ⟨61151, by rfl⟩) R122303
theorem R81791 : Reach 81791 := rs (se 1 (by rfl) ⟨61343, by rfl⟩) R122687
theorem R409691 : Reach 409691 := rs (se 1 (by rfl) ⟨307268, by rfl⟩) R614537
theorem R82623 : Reach 82623 := rs (se 1 (by rfl) ⟨61967, by rfl⟩) R123935
theorem R706643 : Reach 706643 := rs (se 1 (by rfl) ⟨529982, by rfl⟩) R1059965
theorem R1364035 : Reach 1364035 := rs (se 1 (by rfl) ⟨1023026, by rfl⟩) R2046053
theorem R120299 : Reach 120299 := rs (se 1 (by rfl) ⟨90224, by rfl⟩) R180449
theorem R120347 : Reach 120347 := rs (se 1 (by rfl) ⟨90260, by rfl⟩) R180521
theorem R120767 : Reach 120767 := rs (se 1 (by rfl) ⟨90575, by rfl⟩) R181151
theorem R6510617 : Reach 6510617 := rs (se 2 (by rfl) ⟨2441481, by rfl⟩) R4882963
theorem R120887 : Reach 120887 := rs (se 1 (by rfl) ⟨90665, by rfl⟩) R181331
theorem R1693817 : Reach 1693817 := rs (se 2 (by rfl) ⟨635181, by rfl⟩) R1270363
theorem R383129 : Reach 383129 := rs (se 2 (by rfl) ⟨143673, by rfl⟩) R287347
theorem R121001 : Reach 121001 := rs (se 2 (by rfl) ⟨45375, by rfl⟩) R90751
theorem R940409 : Reach 940409 := rs (se 2 (by rfl) ⟨352653, by rfl⟩) R705307
theorem R121295 : Reach 121295 := rs (se 1 (by rfl) ⟨90971, by rfl⟩) R181943
theorem R186983 : Reach 186983 := rs (se 1 (by rfl) ⟨140237, by rfl⟩) R280475
theorem R121583 : Reach 121583 := rs (se 1 (by rfl) ⟨91187, by rfl⟩) R182375
theorem R122495 : Reach 122495 := rs (se 1 (by rfl) ⟨91871, by rfl⟩) R183743
theorem R123119 : Reach 123119 := rs (se 1 (by rfl) ⟨92339, by rfl⟩) R184679
theorem R1434307 : Reach 1434307 := rs (se 1 (by rfl) ⟨1075730, by rfl⟩) R2151461
theorem R386203 : Reach 386203 := rs (se 1 (by rfl) ⟨289652, by rfl⟩) R579305
theorem R616247 : Reach 616247 := rs (se 1 (by rfl) ⟨462185, by rfl⟩) R924371
theorem R14838065 : Reach 14838065 := rs (se 2 (by rfl) ⟨5564274, by rfl⟩) R11128549
theorem R944783 : Reach 944783 := rs (se 1 (by rfl) ⟨708587, by rfl⟩) R1417175
theorem R92911 : Reach 92911 := rs (se 1 (by rfl) ⟨69683, by rfl⟩) R139367
theorem R3402607 : Reach 3402607 := rs (se 1 (by rfl) ⟨2551955, by rfl⟩) R5103911
theorem R421373 : Reach 421373 := rs (se 3 (by rfl) ⟨79007, by rfl⟩) R158015
theorem R225335 : Reach 225335 := rs (se 1 (by rfl) ⟨169001, by rfl⟩) R338003
theorem R520985 : Reach 520985 := rs (se 2 (by rfl) ⟨195369, by rfl⟩) R390739
theorem R3109913 : Reach 3109913 := rs (se 2 (by rfl) ⟨1166217, by rfl⟩) R2332435
theorem R1767095 : Reach 1767095 := rs (se 1 (by rfl) ⟨1325321, by rfl⟩) R2650643
theorem R128927 : Reach 128927 := rs (se 1 (by rfl) ⟨96695, by rfl⟩) R193391
theorem R525473 : Reach 525473 := rs (se 2 (by rfl) ⟨197052, by rfl⟩) R394105
theorem R6949739 : Reach 6949739 := rs (se 1 (by rfl) ⟨5212304, by rfl⟩) R10424609
theorem R626939 : Reach 626939 := rs (se 1 (by rfl) ⟨470204, by rfl⟩) R940409
theorem R135911 : Reach 135911 := rs (se 1 (by rfl) ⟨101933, by rfl⟩) R203867
theorem R2593781 : Reach 2593781 := rs (se 5 (by rfl) ⟨121583, by rfl⟩) R243167
theorem R136937 : Reach 136937 := rs (se 2 (by rfl) ⟨51351, by rfl⟩) R102703
theorem R137423 : Reach 137423 := rs (se 1 (by rfl) ⟨103067, by rfl⟩) R206135
theorem R629855 : Reach 629855 := rs (se 1 (by rfl) ⟨472391, by rfl⟩) R944783
theorem R138719 : Reach 138719 := rs (se 1 (by rfl) ⟨104039, by rfl⟩) R208079
theorem R270107 : Reach 270107 := rs (se 1 (by rfl) ⟨202580, by rfl⟩) R405161
theorem R467207 : Reach 467207 := rs (se 1 (by rfl) ⟨350405, by rfl⟩) R700811
theorem R2073275 : Reach 2073275 := rs (se 1 (by rfl) ⟨1554956, by rfl⟩) R3109913
theorem R1123661 : Reach 1123661 := rs (se 3 (by rfl) ⟨210686, by rfl⟩) R421373
theorem R174953 : Reach 174953 := rs (se 2 (by rfl) ⟨65607, by rfl⟩) R131215
theorem R1092509 : Reach 1092509 := rs (se 3 (by rfl) ⟨204845, by rfl⟩) R409691
theorem R1912409 : Reach 1912409 := rs (se 2 (by rfl) ⟨717153, by rfl⟩) R1434307
theorem R471095 : Reach 471095 := rs (se 1 (by rfl) ⟨353321, by rfl⟩) R706643
theorem R178487 : Reach 178487 := rs (se 1 (by rfl) ⟨133865, by rfl⟩) R267731
theorem R80199 : Reach 80199 := rs (se 1 (by rfl) ⟨60149, by rfl⟩) R120299
theorem R80231 : Reach 80231 := rs (se 1 (by rfl) ⟨60173, by rfl⟩) R120347
theorem R4536809 : Reach 4536809 := rs (se 2 (by rfl) ⟨1701303, by rfl⟩) R3402607
theorem R1260157 : Reach 1260157 := rs (se 3 (by rfl) ⟨236279, by rfl⟩) R472559
theorem R80511 : Reach 80511 := rs (se 1 (by rfl) ⟨60383, by rfl⟩) R120767
theorem R4340411 : Reach 4340411 := rs (se 1 (by rfl) ⟨3255308, by rfl⟩) R6510617
theorem R80591 : Reach 80591 := rs (se 1 (by rfl) ⟨60443, by rfl⟩) R120887
theorem R1129211 : Reach 1129211 := rs (se 1 (by rfl) ⟨846908, by rfl⟩) R1693817
theorem R80667 : Reach 80667 := rs (se 1 (by rfl) ⟨60500, by rfl⟩) R121001
theorem R277289 : Reach 277289 := rs (se 2 (by rfl) ⟨103983, by rfl⟩) R207967
theorem R80863 : Reach 80863 := rs (se 1 (by rfl) ⟨60647, by rfl⟩) R121295
theorem R81055 : Reach 81055 := rs (se 1 (by rfl) ⟨60791, by rfl⟩) R121583
theorem R81663 : Reach 81663 := rs (se 1 (by rfl) ⟨61247, by rfl⟩) R122495
theorem R1818713 : Reach 1818713 := rs (se 2 (by rfl) ⟨682017, by rfl⟩) R1364035
theorem R82079 : Reach 82079 := rs (se 1 (by rfl) ⟨61559, by rfl⟩) R123119
theorem R410831 : Reach 410831 := rs (se 1 (by rfl) ⟨308123, by rfl⟩) R616247
theorem R15943229 : Reach 15943229 := rs (se 3 (by rfl) ⟨2989355, by rfl⟩) R5978711
theorem R182699 : Reach 182699 := rs (se 1 (by rfl) ⟨137024, by rfl⟩) R274049
theorem R150223 : Reach 150223 := rs (se 1 (by rfl) ⟨112667, by rfl⟩) R225335
theorem R347323 : Reach 347323 := rs (se 1 (by rfl) ⟨260492, by rfl⟩) R520985
theorem R249311 : Reach 249311 := rs (se 1 (by rfl) ⟨186983, by rfl⟩) R373967
theorem R85951 : Reach 85951 := rs (se 1 (by rfl) ⟨64463, by rfl⟩) R128927
theorem R151625 : Reach 151625 := rs (se 2 (by rfl) ⟨56859, by rfl⟩) R113719
theorem R676025 : Reach 676025 := rs (se 2 (by rfl) ⟨253509, by rfl⟩) R507019
theorem R184571 : Reach 184571 := rs (se 1 (by rfl) ⟨138428, by rfl⟩) R276857
theorem R185057 : Reach 185057 := rs (se 2 (by rfl) ⟨69396, by rfl⟩) R138793
theorem R186281 : Reach 186281 := rs (se 2 (by rfl) ⟨69855, by rfl⟩) R139711
theorem R153895 : Reach 153895 := rs (se 1 (by rfl) ⟨115421, by rfl⟩) R230843
theorem R514937 : Reach 514937 := rs (se 2 (by rfl) ⟨193101, by rfl⟩) R386203
theorem R154943 : Reach 154943 := rs (se 1 (by rfl) ⟨116207, by rfl⟩) R232415
theorem R352039 : Reach 352039 := rs (se 1 (by rfl) ⟨264029, by rfl⟩) R528059
theorem R417919 : Reach 417919 := rs (se 1 (by rfl) ⟨313439, by rfl⟩) R626879
theorem R123881 : Reach 123881 := rs (se 2 (by rfl) ⟨46455, by rfl⟩) R92911
theorem R615761 : Reach 615761 := rs (se 2 (by rfl) ⟨230910, by rfl⟩) R461821
theorem R255419 : Reach 255419 := rs (se 1 (by rfl) ⟨191564, by rfl⟩) R383129
theorem R124655 : Reach 124655 := rs (se 1 (by rfl) ⟨93491, by rfl⟩) R186983
theorem R93127 : Reach 93127 := rs (se 1 (by rfl) ⟨69845, by rfl⟩) R139691
theorem R290749 : Reach 290749 := rs (se 3 (by rfl) ⟨54515, by rfl⟩) R109031
theorem R9892043 : Reach 9892043 := rs (se 1 (by rfl) ⟨7419032, by rfl⟩) R14838065
theorem R18674657 : Reach 18674657 := rs (se 2 (by rfl) ⟨7002996, by rfl⟩) R14005993
theorem R1178063 : Reach 1178063 := rs (se 1 (by rfl) ⟨883547, by rfl⟩) R1767095
theorem R293663 : Reach 293663 := rs (se 1 (by rfl) ⟨220247, by rfl⟩) R440495
theorem R557225 : Reach 557225 := rs (se 2 (by rfl) ⟨208959, by rfl⟩) R417919
theorem R4849901 : Reach 4849901 := rs (se 3 (by rfl) ⟨909356, by rfl⟩) R1818713
theorem R166207 : Reach 166207 := rs (se 1 (by rfl) ⟨124655, by rfl⟩) R249311
theorem R101083 : Reach 101083 := rs (se 1 (by rfl) ⟨75812, by rfl⟩) R151625
theorem R200297 : Reach 200297 := rs (se 2 (by rfl) ⟨75111, by rfl⟩) R150223
theorem R463097 : Reach 463097 := rs (se 2 (by rfl) ⟨173661, by rfl⟩) R347323
theorem R103295 : Reach 103295 := rs (se 1 (by rfl) ⟨77471, by rfl⟩) R154943
theorem R1382183 : Reach 1382183 := rs (se 1 (by rfl) ⟨1036637, by rfl⟩) R2073275
theorem R170279 : Reach 170279 := rs (se 1 (by rfl) ⟨127709, by rfl⟩) R255419
theorem R6594695 : Reach 6594695 := rs (se 1 (by rfl) ⟨4946021, by rfl⟩) R9892043
theorem R205193 : Reach 205193 := rs (se 2 (by rfl) ⟨76947, by rfl⟩) R153895
theorem R1680209 : Reach 1680209 := rs (se 2 (by rfl) ⟨630078, by rfl⟩) R1260157
theorem R3024539 : Reach 3024539 := rs (se 1 (by rfl) ⟨2268404, by rfl⟩) R4536809
theorem R2893607 : Reach 2893607 := rs (se 1 (by rfl) ⟨2170205, by rfl⟩) R4340411
theorem R469385 : Reach 469385 := rs (se 2 (by rfl) ⟨176019, by rfl⟩) R352039
theorem R273887 : Reach 273887 := rs (se 1 (by rfl) ⟨205415, by rfl⟩) R410831
theorem R10628819 : Reach 10628819 := rs (se 1 (by rfl) ⟨7971614, by rfl⟩) R15943229
theorem R4633159 : Reach 4633159 := rs (se 1 (by rfl) ⟨3474869, by rfl⟩) R6949739
theorem R343291 : Reach 343291 := rs (se 1 (by rfl) ⟨257468, by rfl⟩) R514937
theorem R180071 : Reach 180071 := rs (se 1 (by rfl) ⟨135053, by rfl⟩) R270107
theorem R311471 : Reach 311471 := rs (se 1 (by rfl) ⟨233603, by rfl⟩) R467207
theorem R82587 : Reach 82587 := rs (se 1 (by rfl) ⟨61940, by rfl⟩) R123881
theorem R410507 : Reach 410507 := rs (se 1 (by rfl) ⟨307880, by rfl⟩) R615761
theorem R83103 : Reach 83103 := rs (se 1 (by rfl) ⟨62327, by rfl⟩) R124655
theorem R46613717 : Reach 46613717 := rs (se 7 (by rfl) ⟨546254, by rfl⟩) R1092509
theorem R116635 : Reach 116635 := rs (se 1 (by rfl) ⟨87476, by rfl⟩) R174953
theorem R314063 : Reach 314063 := rs (se 1 (by rfl) ⟨235547, by rfl⟩) R471095
theorem R118991 : Reach 118991 := rs (se 1 (by rfl) ⟨89243, by rfl⟩) R178487
theorem R184859 : Reach 184859 := rs (se 1 (by rfl) ⟨138644, by rfl⟩) R277289
theorem R350315 : Reach 350315 := rs (se 1 (by rfl) ⟨262736, by rfl⟩) R525473
theorem R121799 : Reach 121799 := rs (se 1 (by rfl) ⟨91349, by rfl⟩) R182699
theorem R450683 : Reach 450683 := rs (se 1 (by rfl) ⟨338012, by rfl⟩) R676025
theorem R123047 : Reach 123047 := rs (se 1 (by rfl) ⟨92285, by rfl⟩) R184571
theorem R417959 : Reach 417959 := rs (se 1 (by rfl) ⟨313469, by rfl⟩) R626939
theorem R123371 : Reach 123371 := rs (se 1 (by rfl) ⟨92528, by rfl⟩) R185057
theorem R90607 : Reach 90607 := rs (se 1 (by rfl) ⟨67955, by rfl⟩) R135911
theorem R1729187 : Reach 1729187 := rs (se 1 (by rfl) ⟨1296890, by rfl⟩) R2593781
theorem R91291 : Reach 91291 := rs (se 1 (by rfl) ⟨68468, by rfl⟩) R136937
theorem R124169 : Reach 124169 := rs (se 2 (by rfl) ⟨46563, by rfl⟩) R93127
theorem R124187 : Reach 124187 := rs (se 1 (by rfl) ⟨93140, by rfl⟩) R186281
theorem R91615 : Reach 91615 := rs (se 1 (by rfl) ⟨68711, by rfl⟩) R137423
theorem R419903 : Reach 419903 := rs (se 1 (by rfl) ⟨314927, by rfl⟩) R629855
theorem R92479 : Reach 92479 := rs (se 1 (by rfl) ⟨69359, by rfl⟩) R138719
theorem R387665 : Reach 387665 := rs (se 2 (by rfl) ⟨145374, by rfl⟩) R290749
theorem R749107 : Reach 749107 := rs (se 1 (by rfl) ⟨561830, by rfl⟩) R1123661
theorem R783101 : Reach 783101 := rs (se 3 (by rfl) ⟨146831, by rfl⟩) R293663
theorem R1274939 : Reach 1274939 := rs (se 1 (by rfl) ⟨956204, by rfl⟩) R1912409
theorem R12449771 : Reach 12449771 := rs (se 1 (by rfl) ⟨9337328, by rfl⟩) R18674657
theorem R785375 : Reach 785375 := rs (se 1 (by rfl) ⟨589031, by rfl⟩) R1178063
theorem R752807 : Reach 752807 := rs (se 1 (by rfl) ⟨564605, by rfl⟩) R1129211
theorem R458405 : Reach 458405 := rs (se 4 (by rfl) ⟨42975, by rfl⟩) R85951
theorem R133531 : Reach 133531 := rs (se 1 (by rfl) ⟨100148, by rfl⟩) R200297
theorem R134777 : Reach 134777 := rs (se 2 (by rfl) ⟨50541, by rfl⟩) R101083
theorem R921455 : Reach 921455 := rs (se 1 (by rfl) ⟨691091, by rfl⟩) R1382183
theorem R233543 : Reach 233543 := rs (se 1 (by rfl) ⟨175157, by rfl⟩) R350315
theorem R300455 : Reach 300455 := rs (se 1 (by rfl) ⟨225341, by rfl⟩) R450683
theorem R4396463 : Reach 4396463 := rs (se 1 (by rfl) ⟨3297347, by rfl⟩) R6594695
theorem R136795 : Reach 136795 := rs (se 1 (by rfl) ⟨102596, by rfl⟩) R205193
theorem R1152791 : Reach 1152791 := rs (se 1 (by rfl) ⟨864593, by rfl⟩) R1729187
theorem R1120139 : Reach 1120139 := rs (se 1 (by rfl) ⟨840104, by rfl⟩) R1680209
theorem R7085879 : Reach 7085879 := rs (se 1 (by rfl) ⟨5314409, by rfl⟩) R10628819
theorem R8299847 : Reach 8299847 := rs (se 1 (by rfl) ⟨6224885, by rfl⟩) R12449771
theorem R501871 : Reach 501871 := rs (se 1 (by rfl) ⟨376403, by rfl⟩) R752807
theorem R305603 : Reach 305603 := rs (se 1 (by rfl) ⟨229202, by rfl⟩) R458405
theorem R371483 : Reach 371483 := rs (se 1 (by rfl) ⟨278612, by rfl⟩) R557225
theorem R207647 : Reach 207647 := rs (se 1 (by rfl) ⟨155735, by rfl⟩) R311471
theorem R273671 : Reach 273671 := rs (se 1 (by rfl) ⟨205253, by rfl⟩) R410507
theorem R31075811 : Reach 31075811 := rs (se 1 (by rfl) ⟨23306858, by rfl⟩) R46613717
theorem R209375 : Reach 209375 := rs (se 1 (by rfl) ⟨157031, by rfl⟩) R314063
theorem R275453 : Reach 275453 := rs (se 3 (by rfl) ⟨51647, by rfl⟩) R103295
theorem R79327 : Reach 79327 := rs (se 1 (by rfl) ⟨59495, by rfl⟩) R118991
theorem R308731 : Reach 308731 := rs (se 1 (by rfl) ⟨231548, by rfl⟩) R463097
theorem R113519 : Reach 113519 := rs (se 1 (by rfl) ⟨85139, by rfl⟩) R170279
theorem R81199 : Reach 81199 := rs (se 1 (by rfl) ⟨60899, by rfl⟩) R121799
theorem R82031 : Reach 82031 := rs (se 1 (by rfl) ⟨61523, by rfl⟩) R123047
theorem R278639 : Reach 278639 := rs (se 1 (by rfl) ⟨208979, by rfl⟩) R417959
theorem R82247 : Reach 82247 := rs (se 1 (by rfl) ⟨61685, by rfl⟩) R123371
theorem R6177545 : Reach 6177545 := rs (se 2 (by rfl) ⟨2316579, by rfl⟩) R4633159
theorem R82779 : Reach 82779 := rs (se 1 (by rfl) ⟨62084, by rfl⟩) R124169
theorem R82791 : Reach 82791 := rs (se 1 (by rfl) ⟨62093, by rfl⟩) R124187
theorem R2016359 : Reach 2016359 := rs (se 1 (by rfl) ⟨1512269, by rfl⟩) R3024539
theorem R279935 : Reach 279935 := rs (se 1 (by rfl) ⟨209951, by rfl⟩) R419903
theorem R312923 : Reach 312923 := rs (se 1 (by rfl) ⟨234692, by rfl⟩) R469385
theorem R182591 : Reach 182591 := rs (se 1 (by rfl) ⟨136943, by rfl⟩) R273887
theorem R120047 : Reach 120047 := rs (se 1 (by rfl) ⟨90035, by rfl⟩) R180071
theorem R3233267 : Reach 3233267 := rs (se 1 (by rfl) ⟨2424950, by rfl⟩) R4849901
theorem R120809 : Reach 120809 := rs (se 2 (by rfl) ⟨45303, by rfl⟩) R90607
theorem R121721 : Reach 121721 := rs (se 2 (by rfl) ⟨45645, by rfl⟩) R91291
theorem R122153 : Reach 122153 := rs (se 2 (by rfl) ⟨45807, by rfl⟩) R91615
theorem R155513 : Reach 155513 := rs (se 2 (by rfl) ⟨58317, by rfl⟩) R116635
theorem R123239 : Reach 123239 := rs (se 1 (by rfl) ⟨92429, by rfl⟩) R184859
theorem R221609 : Reach 221609 := rs (se 2 (by rfl) ⟨83103, by rfl⟩) R166207
theorem R123305 : Reach 123305 := rs (se 2 (by rfl) ⟨46239, by rfl⟩) R92479
theorem R1929071 : Reach 1929071 := rs (se 1 (by rfl) ⟨1446803, by rfl⟩) R2893607
theorem R258443 : Reach 258443 := rs (se 1 (by rfl) ⟨193832, by rfl⟩) R387665
theorem R3995237 : Reach 3995237 := rs (se 4 (by rfl) ⟨374553, by rfl⟩) R749107
theorem R522067 : Reach 522067 := rs (se 1 (by rfl) ⟨391550, by rfl⟩) R783101
theorem R849959 : Reach 849959 := rs (se 1 (by rfl) ⟨637469, by rfl⟩) R1274939
theorem R457721 : Reach 457721 := rs (se 2 (by rfl) ⟨171645, by rfl⟩) R343291
theorem R523583 : Reach 523583 := rs (se 1 (by rfl) ⟨392687, by rfl⟩) R785375
theorem R1344239 : Reach 1344239 := rs (se 1 (by rfl) ⟨1008179, by rfl⟩) R2016359
theorem R200303 : Reach 200303 := rs (se 1 (by rfl) ⟨150227, by rfl⟩) R300455
theorem R4723919 : Reach 4723919 := rs (se 1 (by rfl) ⟨3542939, by rfl⟩) R7085879
theorem R103675 : Reach 103675 := rs (se 1 (by rfl) ⟨77756, by rfl⟩) R155513
theorem R203735 : Reach 203735 := rs (se 1 (by rfl) ⟨152801, by rfl⟩) R305603
theorem R138431 : Reach 138431 := rs (se 1 (by rfl) ⟨103823, by rfl⟩) R207647
theorem R302717 : Reach 302717 := rs (se 3 (by rfl) ⟨56759, by rfl⟩) R113519
theorem R20717207 : Reach 20717207 := rs (se 1 (by rfl) ⟨15537905, by rfl⟩) R31075811
theorem R696089 : Reach 696089 := rs (se 2 (by rfl) ⟨261033, by rfl⟩) R522067
theorem R1286047 : Reach 1286047 := rs (se 1 (by rfl) ⟨964535, by rfl⟩) R1929071
theorem R172295 : Reach 172295 := rs (se 1 (by rfl) ⟨129221, by rfl⟩) R258443
theorem R139583 : Reach 139583 := rs (se 1 (by rfl) ⟨104687, by rfl⟩) R209375
theorem R2663491 : Reach 2663491 := rs (se 1 (by rfl) ⟨1997618, by rfl⟩) R3995237
theorem R566639 : Reach 566639 := rs (se 1 (by rfl) ⟨424979, by rfl⟩) R849959
theorem R305147 : Reach 305147 := rs (se 1 (by rfl) ⟨228860, by rfl⟩) R457721
theorem R208615 : Reach 208615 := rs (se 1 (by rfl) ⟨156461, by rfl⟩) R312923
theorem R669161 : Reach 669161 := rs (se 2 (by rfl) ⟨250935, by rfl⟩) R501871
theorem R80031 : Reach 80031 := rs (se 1 (by rfl) ⟨60023, by rfl⟩) R120047
theorem R2930975 : Reach 2930975 := rs (se 1 (by rfl) ⟨2198231, by rfl⟩) R4396463
theorem R768527 : Reach 768527 := rs (se 1 (by rfl) ⟨576395, by rfl⟩) R1152791
theorem R80539 : Reach 80539 := rs (se 1 (by rfl) ⟨60404, by rfl⟩) R120809
theorem R81147 : Reach 81147 := rs (se 1 (by rfl) ⟨60860, by rfl⟩) R121721
theorem R81435 : Reach 81435 := rs (se 1 (by rfl) ⟨61076, by rfl⟩) R122153
theorem R82159 : Reach 82159 := rs (se 1 (by rfl) ⟨61619, by rfl⟩) R123239
theorem R147739 : Reach 147739 := rs (se 1 (by rfl) ⟨110804, by rfl⟩) R221609
theorem R82203 : Reach 82203 := rs (se 1 (by rfl) ⟨61652, by rfl⟩) R123305
theorem R247655 : Reach 247655 := rs (se 1 (by rfl) ⟨185741, by rfl⟩) R371483
theorem R411641 : Reach 411641 := rs (se 2 (by rfl) ⟨154365, by rfl⟩) R308731
theorem R182393 : Reach 182393 := rs (se 2 (by rfl) ⟨68397, by rfl⟩) R136795
theorem R182447 : Reach 182447 := rs (se 1 (by rfl) ⟨136835, by rfl⟩) R273671
theorem R183635 : Reach 183635 := rs (se 1 (by rfl) ⟨137726, by rfl⟩) R275453
theorem R349055 : Reach 349055 := rs (se 1 (by rfl) ⟨261791, by rfl⟩) R523583
theorem R185759 : Reach 185759 := rs (se 1 (by rfl) ⟨139319, by rfl⟩) R278639
theorem R4118363 : Reach 4118363 := rs (se 1 (by rfl) ⟨3088772, by rfl⟩) R6177545
theorem R186623 : Reach 186623 := rs (se 1 (by rfl) ⟨139967, by rfl⟩) R279935
theorem R121727 : Reach 121727 := rs (se 1 (by rfl) ⟨91295, by rfl⟩) R182591
theorem R712165 : Reach 712165 := rs (se 4 (by rfl) ⟨66765, by rfl⟩) R133531
theorem R89851 : Reach 89851 := rs (se 1 (by rfl) ⟨67388, by rfl⟩) R134777
theorem R614303 : Reach 614303 := rs (se 1 (by rfl) ⟨460727, by rfl⟩) R921455
theorem R155695 : Reach 155695 := rs (se 1 (by rfl) ⟨116771, by rfl⟩) R233543
theorem R2155511 : Reach 2155511 := rs (se 1 (by rfl) ⟨1616633, by rfl⟩) R3233267
theorem R746759 : Reach 746759 := rs (se 1 (by rfl) ⟨560069, by rfl⟩) R1120139
theorem R5533231 : Reach 5533231 := rs (se 1 (by rfl) ⟨4149923, by rfl⟩) R8299847
theorem R196985 : Reach 196985 := rs (se 2 (by rfl) ⟨73869, by rfl⟩) R147739
theorem R133535 : Reach 133535 := rs (se 1 (by rfl) ⟨100151, by rfl⟩) R200303
theorem R232703 : Reach 232703 := rs (se 1 (by rfl) ⟨174527, by rfl⟩) R349055
theorem R3149279 : Reach 3149279 := rs (se 1 (by rfl) ⟨2361959, by rfl⟩) R4723919
theorem R135823 : Reach 135823 := rs (se 1 (by rfl) ⟨101867, by rfl⟩) R203735
theorem R7377641 : Reach 7377641 := rs (se 2 (by rfl) ⟨2766615, by rfl⟩) R5533231
theorem R660413 : Reach 660413 := rs (se 3 (by rfl) ⟨123827, by rfl⟩) R247655
theorem R201811 : Reach 201811 := rs (se 1 (by rfl) ⟨151358, by rfl⟩) R302717
theorem R464059 : Reach 464059 := rs (se 1 (by rfl) ⟨348044, by rfl⟩) R696089
theorem R497839 : Reach 497839 := rs (se 1 (by rfl) ⟨373379, by rfl⟩) R746759
theorem R203431 : Reach 203431 := rs (se 1 (by rfl) ⟨152573, by rfl⟩) R305147
theorem R138233 : Reach 138233 := rs (se 2 (by rfl) ⟨51837, by rfl⟩) R103675
theorem R1714729 : Reach 1714729 := rs (se 2 (by rfl) ⟨643023, by rfl⟩) R1286047
theorem R207593 : Reach 207593 := rs (se 2 (by rfl) ⟨77847, by rfl⟩) R155695
theorem R896159 : Reach 896159 := rs (se 1 (by rfl) ⟨672119, by rfl⟩) R1344239
theorem R274427 : Reach 274427 := rs (se 1 (by rfl) ⟨205820, by rfl⟩) R411641
theorem R3551321 : Reach 3551321 := rs (se 2 (by rfl) ⟨1331745, by rfl⟩) R2663491
theorem R5748029 : Reach 5748029 := rs (se 3 (by rfl) ⟨1077755, by rfl⟩) R2155511
theorem R81151 : Reach 81151 := rs (se 1 (by rfl) ⟨60863, by rfl⟩) R121727
theorem R278153 : Reach 278153 := rs (se 2 (by rfl) ⟨104307, by rfl⟩) R208615
theorem R13811471 : Reach 13811471 := rs (se 1 (by rfl) ⟨10358603, by rfl⟩) R20717207
theorem R409535 : Reach 409535 := rs (se 1 (by rfl) ⟨307151, by rfl⟩) R614303
theorem R114863 : Reach 114863 := rs (se 1 (by rfl) ⟨86147, by rfl⟩) R172295
theorem R377759 : Reach 377759 := rs (se 1 (by rfl) ⟨283319, by rfl⟩) R566639
theorem R446107 : Reach 446107 := rs (se 1 (by rfl) ⟨334580, by rfl⟩) R669161
theorem R1953983 : Reach 1953983 := rs (se 1 (by rfl) ⟨1465487, by rfl⟩) R2930975
theorem R512351 : Reach 512351 := rs (se 1 (by rfl) ⟨384263, by rfl⟩) R768527
theorem R119801 : Reach 119801 := rs (se 2 (by rfl) ⟨44925, by rfl⟩) R89851
theorem R121595 : Reach 121595 := rs (se 1 (by rfl) ⟨91196, by rfl⟩) R182393
theorem R121631 : Reach 121631 := rs (se 1 (by rfl) ⟨91223, by rfl⟩) R182447
theorem R122423 : Reach 122423 := rs (se 1 (by rfl) ⟨91817, by rfl⟩) R183635
theorem R123839 : Reach 123839 := rs (se 1 (by rfl) ⟨92879, by rfl⟩) R185759
theorem R2745575 : Reach 2745575 := rs (se 1 (by rfl) ⟨2059181, by rfl⟩) R4118363
theorem R124415 : Reach 124415 := rs (se 1 (by rfl) ⟨93311, by rfl⟩) R186623
theorem R92287 : Reach 92287 := rs (se 1 (by rfl) ⟨69215, by rfl⟩) R138431
theorem R93055 : Reach 93055 := rs (se 1 (by rfl) ⟨69791, by rfl⟩) R139583
theorem R949553 : Reach 949553 := rs (se 2 (by rfl) ⟨356082, by rfl⟩) R712165
theorem R9470189 : Reach 9470189 := rs (se 3 (by rfl) ⟨1775660, by rfl⟩) R3551321
theorem R131323 : Reach 131323 := rs (se 1 (by rfl) ⟨98492, by rfl⟩) R196985
theorem R2099519 : Reach 2099519 := rs (se 1 (by rfl) ⟨1574639, by rfl⟩) R3149279
theorem R4918427 : Reach 4918427 := rs (se 1 (by rfl) ⟨3688820, by rfl⟩) R7377641
theorem R594809 : Reach 594809 := rs (se 2 (by rfl) ⟨223053, by rfl⟩) R446107
theorem R269081 : Reach 269081 := rs (se 2 (by rfl) ⟨100905, by rfl⟩) R201811
theorem R138395 : Reach 138395 := rs (se 1 (by rfl) ⟨103796, by rfl⟩) R207593
theorem R597439 : Reach 597439 := rs (se 1 (by rfl) ⟨448079, by rfl⟩) R896159
theorem R663785 : Reach 663785 := rs (se 2 (by rfl) ⟨248919, by rfl⟩) R497839
theorem R271241 : Reach 271241 := rs (se 2 (by rfl) ⟨101715, by rfl⟩) R203431
theorem R633035 : Reach 633035 := rs (se 1 (by rfl) ⟨474776, by rfl⟩) R949553
theorem R273023 : Reach 273023 := rs (se 1 (by rfl) ⟨204767, by rfl⟩) R409535
theorem R306301 : Reach 306301 := rs (se 3 (by rfl) ⟨57431, by rfl⟩) R114863
theorem R341567 : Reach 341567 := rs (se 1 (by rfl) ⟨256175, by rfl⟩) R512351
theorem R440275 : Reach 440275 := rs (se 1 (by rfl) ⟨330206, by rfl⟩) R660413
theorem R79867 : Reach 79867 := rs (se 1 (by rfl) ⟨59900, by rfl⟩) R119801
theorem R81063 : Reach 81063 := rs (se 1 (by rfl) ⟨60797, by rfl⟩) R121595
theorem R81087 : Reach 81087 := rs (se 1 (by rfl) ⟨60815, by rfl⟩) R121631
theorem R81615 : Reach 81615 := rs (se 1 (by rfl) ⟨61211, by rfl⟩) R122423
theorem R82559 : Reach 82559 := rs (se 1 (by rfl) ⟨61919, by rfl⟩) R123839
theorem R181097 : Reach 181097 := rs (se 2 (by rfl) ⟨67911, by rfl⟩) R135823
theorem R82943 : Reach 82943 := rs (se 1 (by rfl) ⟨62207, by rfl⟩) R124415
theorem R182951 : Reach 182951 := rs (se 1 (by rfl) ⟨137213, by rfl⟩) R274427
theorem R185435 : Reach 185435 := rs (se 1 (by rfl) ⟨139076, by rfl⟩) R278153
theorem R251839 : Reach 251839 := rs (se 1 (by rfl) ⟨188879, by rfl⟩) R377759
theorem R89023 : Reach 89023 := rs (se 1 (by rfl) ⟨66767, by rfl⟩) R133535
theorem R155135 : Reach 155135 := rs (se 1 (by rfl) ⟨116351, by rfl⟩) R232703
theorem R1302655 : Reach 1302655 := rs (se 1 (by rfl) ⟨976991, by rfl⟩) R1953983
theorem R123049 : Reach 123049 := rs (se 2 (by rfl) ⟨46143, by rfl⟩) R92287
theorem R2286305 : Reach 2286305 := rs (se 2 (by rfl) ⟨857364, by rfl⟩) R1714729
theorem R124073 : Reach 124073 := rs (se 2 (by rfl) ⟨46527, by rfl⟩) R93055
theorem R92155 : Reach 92155 := rs (se 1 (by rfl) ⟨69116, by rfl⟩) R138233
theorem R1830383 : Reach 1830383 := rs (se 1 (by rfl) ⟨1372787, by rfl⟩) R2745575
theorem R618745 : Reach 618745 := rs (se 2 (by rfl) ⟨232029, by rfl⟩) R464059
theorem R3832019 : Reach 3832019 := rs (se 1 (by rfl) ⟨2874014, by rfl⟩) R5748029
theorem R9207647 : Reach 9207647 := rs (se 1 (by rfl) ⟨6905735, by rfl⟩) R13811471
theorem R1736873 : Reach 1736873 := rs (se 2 (by rfl) ⟨651327, by rfl⟩) R1302655
theorem R656261 : Reach 656261 := rs (se 4 (by rfl) ⟨61524, by rfl⟩) R123049
theorem R3278951 : Reach 3278951 := rs (se 1 (by rfl) ⟨2459213, by rfl⟩) R4918427
theorem R396539 : Reach 396539 := rs (se 1 (by rfl) ⟨297404, by rfl⟩) R594809
theorem R103423 : Reach 103423 := rs (se 1 (by rfl) ⟨77567, by rfl⟩) R155135
theorem R824993 : Reach 824993 := rs (se 2 (by rfl) ⟨309372, by rfl⟩) R618745
theorem R1220255 : Reach 1220255 := rs (se 1 (by rfl) ⟨915191, by rfl⟩) R1830383
theorem R3186341 : Reach 3186341 := rs (se 4 (by rfl) ⟨298719, by rfl⟩) R597439
theorem R335785 : Reach 335785 := rs (se 2 (by rfl) ⟨125919, by rfl⟩) R251839
theorem R6138431 : Reach 6138431 := rs (se 1 (by rfl) ⟨4603823, by rfl⟩) R9207647
theorem R175097 : Reach 175097 := rs (se 2 (by rfl) ⟨65661, by rfl⟩) R131323
theorem R408401 : Reach 408401 := rs (se 2 (by rfl) ⟨153150, by rfl⟩) R306301
theorem R179387 : Reach 179387 := rs (se 1 (by rfl) ⟨134540, by rfl⟩) R269081
theorem R442523 : Reach 442523 := rs (se 1 (by rfl) ⟨331892, by rfl⟩) R663785
theorem R1524203 : Reach 1524203 := rs (se 1 (by rfl) ⟨1143152, by rfl⟩) R2286305
theorem R180827 : Reach 180827 := rs (se 1 (by rfl) ⟨135620, by rfl⟩) R271241
theorem R82715 : Reach 82715 := rs (se 1 (by rfl) ⟨62036, by rfl⟩) R124073
theorem R182015 : Reach 182015 := rs (se 1 (by rfl) ⟨136511, by rfl⟩) R273023
theorem R118697 : Reach 118697 := rs (se 2 (by rfl) ⟨44511, by rfl⟩) R89023
theorem R6313459 : Reach 6313459 := rs (se 1 (by rfl) ⟨4735094, by rfl⟩) R9470189
theorem R120731 : Reach 120731 := rs (se 1 (by rfl) ⟨90548, by rfl⟩) R181097
theorem R1399679 : Reach 1399679 := rs (se 1 (by rfl) ⟨1049759, by rfl⟩) R2099519
theorem R121967 : Reach 121967 := rs (se 1 (by rfl) ⟨91475, by rfl⟩) R182951
theorem R122873 : Reach 122873 := rs (se 2 (by rfl) ⟨46077, by rfl⟩) R92155
theorem R123623 : Reach 123623 := rs (se 1 (by rfl) ⟨92717, by rfl⟩) R185435
theorem R92263 : Reach 92263 := rs (se 1 (by rfl) ⟨69197, by rfl⟩) R138395
theorem R422023 : Reach 422023 := rs (se 1 (by rfl) ⟨316517, by rfl⟩) R633035
theorem R587033 : Reach 587033 := rs (se 2 (by rfl) ⟨220137, by rfl⟩) R440275
theorem R227711 : Reach 227711 := rs (se 1 (by rfl) ⟨170783, by rfl⟩) R341567
theorem R2554679 : Reach 2554679 := rs (se 1 (by rfl) ⟨1916009, by rfl⟩) R3832019
theorem R295015 : Reach 295015 := rs (se 1 (by rfl) ⟨221261, by rfl⟩) R442523
theorem R1016135 : Reach 1016135 := rs (se 1 (by rfl) ⟨762101, by rfl⟩) R1524203
theorem R264359 : Reach 264359 := rs (se 1 (by rfl) ⟨198269, by rfl⟩) R396539
theorem R562697 : Reach 562697 := rs (se 2 (by rfl) ⟨211011, by rfl⟩) R422023
theorem R137897 : Reach 137897 := rs (se 2 (by rfl) ⟨51711, by rfl⟩) R103423
theorem R272267 : Reach 272267 := rs (se 1 (by rfl) ⟨204200, by rfl⟩) R408401
theorem R1157915 : Reach 1157915 := rs (se 1 (by rfl) ⟨868436, by rfl⟩) R1736873
theorem R437507 : Reach 437507 := rs (se 1 (by rfl) ⟨328130, by rfl⟩) R656261
theorem R79131 : Reach 79131 := rs (se 1 (by rfl) ⟨59348, by rfl⟩) R118697
theorem R80487 : Reach 80487 := rs (se 1 (by rfl) ⟨60365, by rfl⟩) R120731
theorem R933119 : Reach 933119 := rs (se 1 (by rfl) ⟨699839, by rfl⟩) R1399679
theorem R81311 : Reach 81311 := rs (se 1 (by rfl) ⟨60983, by rfl⟩) R121967
theorem R81915 : Reach 81915 := rs (se 1 (by rfl) ⟨61436, by rfl⟩) R122873
theorem R82415 : Reach 82415 := rs (se 1 (by rfl) ⟨61811, by rfl⟩) R123623
theorem R116731 : Reach 116731 := rs (se 1 (by rfl) ⟨87548, by rfl⟩) R175097
theorem R151807 : Reach 151807 := rs (se 1 (by rfl) ⟨113855, by rfl⟩) R227711
theorem R119591 : Reach 119591 := rs (se 1 (by rfl) ⟨89693, by rfl⟩) R179387
theorem R447713 : Reach 447713 := rs (se 2 (by rfl) ⟨167892, by rfl⟩) R335785
theorem R120551 : Reach 120551 := rs (se 1 (by rfl) ⟨90413, by rfl⟩) R180827
theorem R121343 : Reach 121343 := rs (se 1 (by rfl) ⟨91007, by rfl⟩) R182015
theorem R2185967 : Reach 2185967 := rs (se 1 (by rfl) ⟨1639475, by rfl⟩) R3278951
theorem R123017 : Reach 123017 := rs (se 2 (by rfl) ⟨46131, by rfl⟩) R92263
theorem R549995 : Reach 549995 := rs (se 1 (by rfl) ⟨412496, by rfl⟩) R824993
theorem R813503 : Reach 813503 := rs (se 1 (by rfl) ⟨610127, by rfl⟩) R1220255
theorem R2124227 : Reach 2124227 := rs (se 1 (by rfl) ⟨1593170, by rfl⟩) R3186341
theorem R4092287 : Reach 4092287 := rs (se 1 (by rfl) ⟨3069215, by rfl⟩) R6138431
theorem R8417945 : Reach 8417945 := rs (se 2 (by rfl) ⟨3156729, by rfl⟩) R6313459
theorem R391355 : Reach 391355 := rs (se 1 (by rfl) ⟨293516, by rfl⟩) R587033
theorem R1703119 : Reach 1703119 := rs (se 1 (by rfl) ⟨1277339, by rfl⟩) R2554679
theorem R393353 : Reach 393353 := rs (se 2 (by rfl) ⟨147507, by rfl⟩) R295015
theorem R10912765 : Reach 10912765 := rs (se 3 (by rfl) ⟨2046143, by rfl⟩) R4092287
theorem R5866613 : Reach 5866613 := rs (se 5 (by rfl) ⟨274997, by rfl⟩) R549995
theorem R298475 : Reach 298475 := rs (se 1 (by rfl) ⟨223856, by rfl⟩) R447713
theorem R202409 : Reach 202409 := rs (se 2 (by rfl) ⟨75903, by rfl⟩) R151807
theorem R1416151 : Reach 1416151 := rs (se 1 (by rfl) ⟨1062113, by rfl⟩) R2124227
theorem R5611963 : Reach 5611963 := rs (se 1 (by rfl) ⟨4208972, by rfl⟩) R8417945
theorem R2270825 : Reach 2270825 := rs (se 2 (by rfl) ⟨851559, by rfl⟩) R1703119
theorem R176239 : Reach 176239 := rs (se 1 (by rfl) ⟨132179, by rfl⟩) R264359
theorem R79727 : Reach 79727 := rs (se 1 (by rfl) ⟨59795, by rfl⟩) R119591
theorem R375131 : Reach 375131 := rs (se 1 (by rfl) ⟨281348, by rfl⟩) R562697
theorem R80367 : Reach 80367 := rs (se 1 (by rfl) ⟨60275, by rfl⟩) R120551
theorem R80895 : Reach 80895 := rs (se 1 (by rfl) ⟨60671, by rfl⟩) R121343
theorem R82011 : Reach 82011 := rs (se 1 (by rfl) ⟨61508, by rfl⟩) R123017
theorem R181511 : Reach 181511 := rs (se 1 (by rfl) ⟨136133, by rfl⟩) R272267
theorem R542335 : Reach 542335 := rs (se 1 (by rfl) ⟨406751, by rfl⟩) R813503
theorem R771943 : Reach 771943 := rs (se 1 (by rfl) ⟨578957, by rfl⟩) R1157915
theorem R677423 : Reach 677423 := rs (se 1 (by rfl) ⟨508067, by rfl⟩) R1016135
theorem R91931 : Reach 91931 := rs (se 1 (by rfl) ⟨68948, by rfl⟩) R137897
theorem R5829245 : Reach 5829245 := rs (se 3 (by rfl) ⟨1092983, by rfl⟩) R2185967
theorem R291671 : Reach 291671 := rs (se 1 (by rfl) ⟨218753, by rfl⟩) R437507
theorem R260903 : Reach 260903 := rs (se 1 (by rfl) ⟨195677, by rfl⟩) R391355
theorem R622079 : Reach 622079 := rs (se 1 (by rfl) ⟨466559, by rfl⟩) R933119
theorem R622565 : Reach 622565 := rs (se 4 (by rfl) ⟨58365, by rfl⟩) R116731
theorem R262235 : Reach 262235 := rs (se 1 (by rfl) ⟨196676, by rfl⟩) R393353
theorem R14550353 : Reach 14550353 := rs (se 2 (by rfl) ⟨5456382, by rfl⟩) R10912765
theorem R723113 : Reach 723113 := rs (se 2 (by rfl) ⟨271167, by rfl⟩) R542335
theorem R198983 : Reach 198983 := rs (se 1 (by rfl) ⟨149237, by rfl⟩) R298475
theorem R134939 : Reach 134939 := rs (se 1 (by rfl) ⟨101204, by rfl⟩) R202409
theorem R1513883 : Reach 1513883 := rs (se 1 (by rfl) ⟨1135412, by rfl⟩) R2270825
theorem R173935 : Reach 173935 := rs (se 1 (by rfl) ⟨130451, by rfl⟩) R260903
theorem R7482617 : Reach 7482617 := rs (se 2 (by rfl) ⟨2805981, by rfl⟩) R5611963
theorem R3911075 : Reach 3911075 := rs (se 1 (by rfl) ⟨2933306, by rfl⟩) R5866613
theorem R1029257 : Reach 1029257 := rs (se 2 (by rfl) ⟨385971, by rfl⟩) R771943
theorem R245149 : Reach 245149 := rs (se 3 (by rfl) ⟨45965, by rfl⟩) R91931
theorem R1000349 : Reach 1000349 := rs (se 3 (by rfl) ⟨187565, by rfl⟩) R375131
theorem R3886163 : Reach 3886163 := rs (se 1 (by rfl) ⟨2914622, by rfl⟩) R5829245
theorem R1888201 : Reach 1888201 := rs (se 2 (by rfl) ⟨708075, by rfl⟩) R1416151
theorem R414719 : Reach 414719 := rs (se 1 (by rfl) ⟨311039, by rfl⟩) R622079
theorem R415043 : Reach 415043 := rs (se 1 (by rfl) ⟨311282, by rfl⟩) R622565
theorem R939941 : Reach 939941 := rs (se 4 (by rfl) ⟨88119, by rfl⟩) R176239
theorem R121007 : Reach 121007 := rs (se 1 (by rfl) ⟨90755, by rfl⟩) R181511
theorem R451615 : Reach 451615 := rs (se 1 (by rfl) ⟨338711, by rfl⟩) R677423
theorem R194447 : Reach 194447 := rs (se 1 (by rfl) ⟨145835, by rfl⟩) R291671
theorem R9700235 : Reach 9700235 := rs (se 1 (by rfl) ⟨7275176, by rfl⟩) R14550353
theorem R2590775 : Reach 2590775 := rs (se 1 (by rfl) ⟨1943081, by rfl⟩) R3886163
theorem R231913 : Reach 231913 := rs (se 2 (by rfl) ⟨86967, by rfl⟩) R173935
theorem R626627 : Reach 626627 := rs (se 1 (by rfl) ⟨469970, by rfl⟩) R939941
theorem R530621 : Reach 530621 := rs (se 3 (by rfl) ⟨99491, by rfl⟩) R198983
theorem R4988411 : Reach 4988411 := rs (se 1 (by rfl) ⟨3741308, by rfl⟩) R7482617
theorem R699293 : Reach 699293 := rs (se 3 (by rfl) ⟨131117, by rfl⟩) R262235
theorem R666899 : Reach 666899 := rs (se 1 (by rfl) ⟨500174, by rfl⟩) R1000349
theorem R602153 : Reach 602153 := rs (se 2 (by rfl) ⟨225807, by rfl⟩) R451615
theorem R276479 : Reach 276479 := rs (se 1 (by rfl) ⟨207359, by rfl⟩) R414719
theorem R276695 : Reach 276695 := rs (se 1 (by rfl) ⟨207521, by rfl⟩) R415043
theorem R80671 : Reach 80671 := rs (se 1 (by rfl) ⟨60503, by rfl⟩) R121007
theorem R2607383 : Reach 2607383 := rs (se 1 (by rfl) ⟨1955537, by rfl⟩) R3911075
theorem R482075 : Reach 482075 := rs (se 1 (by rfl) ⟨361556, by rfl⟩) R723113
theorem R89959 : Reach 89959 := rs (se 1 (by rfl) ⟨67469, by rfl⟩) R134939
theorem R1009255 : Reach 1009255 := rs (se 1 (by rfl) ⟨756941, by rfl⟩) R1513883
theorem R518525 : Reach 518525 := rs (se 3 (by rfl) ⟨97223, by rfl⟩) R194447
theorem R2517601 : Reach 2517601 := rs (se 2 (by rfl) ⟨944100, by rfl⟩) R1888201
theorem R1307461 : Reach 1307461 := rs (se 4 (by rfl) ⟨122574, by rfl⟩) R245149
theorem R686171 : Reach 686171 := rs (se 1 (by rfl) ⟨514628, by rfl⟩) R1029257
theorem R1738255 : Reach 1738255 := rs (se 1 (by rfl) ⟨1303691, by rfl⟩) R2607383
theorem R1345673 : Reach 1345673 := rs (se 2 (by rfl) ⟨504627, by rfl⟩) R1009255
theorem R1743281 : Reach 1743281 := rs (se 2 (by rfl) ⟨653730, by rfl⟩) R1307461
theorem R466195 : Reach 466195 := rs (se 1 (by rfl) ⟨349646, by rfl⟩) R699293
theorem R401435 : Reach 401435 := rs (se 1 (by rfl) ⟨301076, by rfl⟩) R602153
theorem R6466823 : Reach 6466823 := rs (se 1 (by rfl) ⟨4850117, by rfl⟩) R9700235
theorem R309217 : Reach 309217 := rs (se 2 (by rfl) ⟨115956, by rfl⟩) R231913
theorem R3356801 : Reach 3356801 := rs (se 2 (by rfl) ⟨1258800, by rfl⟩) R2517601
theorem R3325607 : Reach 3325607 := rs (se 1 (by rfl) ⟨2494205, by rfl⟩) R4988411
theorem R345683 : Reach 345683 := rs (se 1 (by rfl) ⟨259262, by rfl⟩) R518525
theorem R444599 : Reach 444599 := rs (se 1 (by rfl) ⟨333449, by rfl⟩) R666899
theorem R184319 : Reach 184319 := rs (se 1 (by rfl) ⟨138239, by rfl⟩) R276479
theorem R184463 : Reach 184463 := rs (se 1 (by rfl) ⟨138347, by rfl⟩) R276695
theorem R119945 : Reach 119945 := rs (se 2 (by rfl) ⟨44979, by rfl⟩) R89959
theorem R1727183 : Reach 1727183 := rs (se 1 (by rfl) ⟨1295387, by rfl⟩) R2590775
theorem R353747 : Reach 353747 := rs (se 1 (by rfl) ⟨265310, by rfl⟩) R530621
theorem R321383 : Reach 321383 := rs (se 1 (by rfl) ⟨241037, by rfl⟩) R482075
theorem R457447 : Reach 457447 := rs (se 1 (by rfl) ⟨343085, by rfl⟩) R686171
theorem R1671005 : Reach 1671005 := rs (se 3 (by rfl) ⟨313313, by rfl⟩) R626627
theorem R230455 : Reach 230455 := rs (se 1 (by rfl) ⟨172841, by rfl⟩) R345683
theorem R296399 : Reach 296399 := rs (se 1 (by rfl) ⟨222299, by rfl⟩) R444599
theorem R267623 : Reach 267623 := rs (se 1 (by rfl) ⟨200717, by rfl⟩) R401435
theorem R2237867 : Reach 2237867 := rs (se 1 (by rfl) ⟨1678400, by rfl⟩) R3356801
theorem R897115 : Reach 897115 := rs (se 1 (by rfl) ⟨672836, by rfl⟩) R1345673
theorem R79963 : Reach 79963 := rs (se 1 (by rfl) ⟨59972, by rfl⟩) R119945
theorem R1162187 : Reach 1162187 := rs (se 1 (by rfl) ⟨871640, by rfl⟩) R1743281
theorem R214255 : Reach 214255 := rs (se 1 (by rfl) ⟨160691, by rfl⟩) R321383
theorem R4605821 : Reach 4605821 := rs (se 3 (by rfl) ⟨863591, by rfl⟩) R1727183
theorem R4311215 : Reach 4311215 := rs (se 1 (by rfl) ⟨3233411, by rfl⟩) R6466823
theorem R412289 : Reach 412289 := rs (se 2 (by rfl) ⟨154608, by rfl⟩) R309217
theorem R609929 : Reach 609929 := rs (se 2 (by rfl) ⟨228723, by rfl⟩) R457447
theorem R2217071 : Reach 2217071 := rs (se 1 (by rfl) ⟨1662803, by rfl⟩) R3325607
theorem R2317673 : Reach 2317673 := rs (se 2 (by rfl) ⟨869127, by rfl⟩) R1738255
theorem R122879 : Reach 122879 := rs (se 1 (by rfl) ⟨92159, by rfl⟩) R184319
theorem R122975 : Reach 122975 := rs (se 1 (by rfl) ⟨92231, by rfl⟩) R184463
theorem R943325 : Reach 943325 := rs (se 3 (by rfl) ⟨176873, by rfl⟩) R353747
theorem R621593 : Reach 621593 := rs (se 2 (by rfl) ⟨233097, by rfl⟩) R466195
theorem R1114003 : Reach 1114003 := rs (se 1 (by rfl) ⟨835502, by rfl⟩) R1671005
theorem R1478047 : Reach 1478047 := rs (se 1 (by rfl) ⟨1108535, by rfl⟩) R2217071
theorem R790397 : Reach 790397 := rs (se 3 (by rfl) ⟨148199, by rfl⟩) R296399
theorem R1545115 : Reach 1545115 := rs (se 1 (by rfl) ⟨1158836, by rfl⟩) R2317673
theorem R628883 : Reach 628883 := rs (se 1 (by rfl) ⟨471662, by rfl⟩) R943325
theorem R5941349 : Reach 5941349 := rs (se 4 (by rfl) ⟨557001, by rfl⟩) R1114003
theorem R307273 : Reach 307273 := rs (se 2 (by rfl) ⟨115227, by rfl⟩) R230455
theorem R274859 : Reach 274859 := rs (se 1 (by rfl) ⟨206144, by rfl⟩) R412289
theorem R406619 : Reach 406619 := rs (se 1 (by rfl) ⟨304964, by rfl⟩) R609929
theorem R178415 : Reach 178415 := rs (se 1 (by rfl) ⟨133811, by rfl⟩) R267623
theorem R81919 : Reach 81919 := rs (se 1 (by rfl) ⟨61439, by rfl⟩) R122879
theorem R81983 : Reach 81983 := rs (se 1 (by rfl) ⟨61487, by rfl⟩) R122975
theorem R1196153 : Reach 1196153 := rs (se 2 (by rfl) ⟨448557, by rfl⟩) R897115
theorem R1491911 : Reach 1491911 := rs (se 1 (by rfl) ⟨1118933, by rfl⟩) R2237867
theorem R774791 : Reach 774791 := rs (se 1 (by rfl) ⟨581093, by rfl⟩) R1162187
theorem R414395 : Reach 414395 := rs (se 1 (by rfl) ⟨310796, by rfl⟩) R621593
theorem R3070547 : Reach 3070547 := rs (se 1 (by rfl) ⟨2302910, by rfl⟩) R4605821
theorem R2874143 : Reach 2874143 := rs (se 1 (by rfl) ⟨2155607, by rfl⟩) R4311215
theorem R1142693 : Reach 1142693 := rs (se 4 (by rfl) ⟨107127, by rfl⟩) R214255
theorem R526931 : Reach 526931 := rs (se 1 (by rfl) ⟨395198, by rfl⟩) R790397
theorem R1970729 : Reach 1970729 := rs (se 2 (by rfl) ⟨739023, by rfl⟩) R1478047
theorem R761795 : Reach 761795 := rs (se 1 (by rfl) ⟨571346, by rfl⟩) R1142693
theorem R271079 : Reach 271079 := rs (se 1 (by rfl) ⟨203309, by rfl⟩) R406619
theorem R797435 : Reach 797435 := rs (se 1 (by rfl) ⟨598076, by rfl⟩) R1196153
theorem R994607 : Reach 994607 := rs (se 1 (by rfl) ⟨745955, by rfl⟩) R1491911
theorem R276263 : Reach 276263 := rs (se 1 (by rfl) ⟨207197, by rfl⟩) R414395
theorem R2047031 : Reach 2047031 := rs (se 1 (by rfl) ⟨1535273, by rfl⟩) R3070547
theorem R1916095 : Reach 1916095 := rs (se 1 (by rfl) ⟨1437071, by rfl⟩) R2874143
theorem R409697 : Reach 409697 := rs (se 2 (by rfl) ⟨153636, by rfl⟩) R307273
theorem R183239 : Reach 183239 := rs (se 1 (by rfl) ⟨137429, by rfl⟩) R274859
theorem R118943 : Reach 118943 := rs (se 1 (by rfl) ⟨89207, by rfl⟩) R178415
theorem R516527 : Reach 516527 := rs (se 1 (by rfl) ⟨387395, by rfl⟩) R774791
theorem R419255 : Reach 419255 := rs (se 1 (by rfl) ⟨314441, by rfl⟩) R628883
theorem R2060153 : Reach 2060153 := rs (se 2 (by rfl) ⟨772557, by rfl⟩) R1545115
theorem R3960899 : Reach 3960899 := rs (se 1 (by rfl) ⟨2970674, by rfl⟩) R5941349
theorem R1313819 : Reach 1313819 := rs (se 1 (by rfl) ⟨985364, by rfl⟩) R1970729
theorem R531623 : Reach 531623 := rs (se 1 (by rfl) ⟨398717, by rfl⟩) R797435
theorem R663071 : Reach 663071 := rs (se 1 (by rfl) ⟨497303, by rfl⟩) R994607
theorem R273131 : Reach 273131 := rs (se 1 (by rfl) ⟨204848, by rfl⟩) R409697
theorem R79295 : Reach 79295 := rs (se 1 (by rfl) ⟨59471, by rfl⟩) R118943
theorem R507863 : Reach 507863 := rs (se 1 (by rfl) ⟨380897, by rfl⟩) R761795
theorem R344351 : Reach 344351 := rs (se 1 (by rfl) ⟨258263, by rfl⟩) R516527
theorem R180719 : Reach 180719 := rs (se 1 (by rfl) ⟨135539, by rfl⟩) R271079
theorem R279503 : Reach 279503 := rs (se 1 (by rfl) ⟨209627, by rfl⟩) R419255
theorem R2640599 : Reach 2640599 := rs (se 1 (by rfl) ⟨1980449, by rfl⟩) R3960899
theorem R184175 : Reach 184175 := rs (se 1 (by rfl) ⟨138131, by rfl⟩) R276263
theorem R1364687 : Reach 1364687 := rs (se 1 (by rfl) ⟨1023515, by rfl⟩) R2047031
theorem R351287 : Reach 351287 := rs (se 1 (by rfl) ⟨263465, by rfl⟩) R526931
theorem R122159 : Reach 122159 := rs (se 1 (by rfl) ⟨91619, by rfl⟩) R183239
theorem R1373435 : Reach 1373435 := rs (se 1 (by rfl) ⟨1030076, by rfl⟩) R2060153
theorem R2554793 : Reach 2554793 := rs (se 2 (by rfl) ⟨958047, by rfl⟩) R1916095
theorem R229567 : Reach 229567 := rs (se 1 (by rfl) ⟨172175, by rfl⟩) R344351
theorem R234191 : Reach 234191 := rs (se 1 (by rfl) ⟨175643, by rfl⟩) R351287
theorem R338575 : Reach 338575 := rs (se 1 (by rfl) ⟨253931, by rfl⟩) R507863
theorem R81439 : Reach 81439 := rs (se 1 (by rfl) ⟨61079, by rfl⟩) R122159
theorem R182087 : Reach 182087 := rs (se 1 (by rfl) ⟨136565, by rfl⟩) R273131
theorem R120479 : Reach 120479 := rs (se 1 (by rfl) ⟨90359, by rfl⟩) R180719
theorem R186335 : Reach 186335 := rs (se 1 (by rfl) ⟨139751, by rfl⟩) R279503
theorem R1760399 : Reach 1760399 := rs (se 1 (by rfl) ⟨1320299, by rfl⟩) R2640599
theorem R875879 : Reach 875879 := rs (se 1 (by rfl) ⟨656909, by rfl⟩) R1313819
theorem R122783 : Reach 122783 := rs (se 1 (by rfl) ⟨92087, by rfl⟩) R184175
theorem R909791 : Reach 909791 := rs (se 1 (by rfl) ⟨682343, by rfl⟩) R1364687
theorem R354415 : Reach 354415 := rs (se 1 (by rfl) ⟨265811, by rfl⟩) R531623
theorem R915623 : Reach 915623 := rs (se 1 (by rfl) ⟨686717, by rfl⟩) R1373435
theorem R1768189 : Reach 1768189 := rs (se 3 (by rfl) ⟨331535, by rfl⟩) R663071
theorem R1703195 : Reach 1703195 := rs (se 1 (by rfl) ⟨1277396, by rfl⟩) R2554793
theorem R624509 : Reach 624509 := rs (se 3 (by rfl) ⟨117095, by rfl⟩) R234191
theorem R306089 : Reach 306089 := rs (se 2 (by rfl) ⟨114783, by rfl⟩) R229567
theorem R472553 : Reach 472553 := rs (se 2 (by rfl) ⟨177207, by rfl⟩) R354415
theorem R80319 : Reach 80319 := rs (se 1 (by rfl) ⟨60239, by rfl⟩) R120479
theorem R81855 : Reach 81855 := rs (se 1 (by rfl) ⟨61391, by rfl⟩) R122783
theorem R606527 : Reach 606527 := rs (se 1 (by rfl) ⟨454895, by rfl⟩) R909791
theorem R610415 : Reach 610415 := rs (se 1 (by rfl) ⟨457811, by rfl⟩) R915623
theorem R1135463 : Reach 1135463 := rs (se 1 (by rfl) ⟨851597, by rfl⟩) R1703195
theorem R121391 : Reach 121391 := rs (se 1 (by rfl) ⟨91043, by rfl⟩) R182087
theorem R451433 : Reach 451433 := rs (se 2 (by rfl) ⟨169287, by rfl⟩) R338575
theorem R124223 : Reach 124223 := rs (se 1 (by rfl) ⟨93167, by rfl⟩) R186335
theorem R1173599 : Reach 1173599 := rs (se 1 (by rfl) ⟨880199, by rfl⟩) R1760399
theorem R583919 : Reach 583919 := rs (se 1 (by rfl) ⟨437939, by rfl⟩) R875879
theorem R2357585 : Reach 2357585 := rs (se 2 (by rfl) ⟨884094, by rfl⟩) R1768189
theorem R300955 : Reach 300955 := rs (se 1 (by rfl) ⟨225716, by rfl⟩) R451433
theorem R204059 : Reach 204059 := rs (se 1 (by rfl) ⟨153044, by rfl⟩) R306089
theorem R404351 : Reach 404351 := rs (se 1 (by rfl) ⟨303263, by rfl⟩) R606527
theorem R3027901 : Reach 3027901 := rs (se 3 (by rfl) ⟨567731, by rfl⟩) R1135463
theorem R406943 : Reach 406943 := rs (se 1 (by rfl) ⟨305207, by rfl⟩) R610415
theorem R80927 : Reach 80927 := rs (se 1 (by rfl) ⟨60695, by rfl⟩) R121391
theorem R82815 : Reach 82815 := rs (se 1 (by rfl) ⟨62111, by rfl⟩) R124223
theorem R315035 : Reach 315035 := rs (se 1 (by rfl) ⟨236276, by rfl⟩) R472553
theorem R416339 : Reach 416339 := rs (se 1 (by rfl) ⟨312254, by rfl⟩) R624509
theorem R782399 : Reach 782399 := rs (se 1 (by rfl) ⟨586799, by rfl⟩) R1173599
theorem R389279 : Reach 389279 := rs (se 1 (by rfl) ⟨291959, by rfl⟩) R583919
theorem R1571723 : Reach 1571723 := rs (se 1 (by rfl) ⟨1178792, by rfl⟩) R2357585
theorem R136039 : Reach 136039 := rs (se 1 (by rfl) ⟨102029, by rfl⟩) R204059
theorem R4037201 : Reach 4037201 := rs (se 2 (by rfl) ⟨1513950, by rfl⟩) R3027901
theorem R269567 : Reach 269567 := rs (se 1 (by rfl) ⟨202175, by rfl⟩) R404351
theorem R401273 : Reach 401273 := rs (se 2 (by rfl) ⟨150477, by rfl⟩) R300955
theorem R271295 : Reach 271295 := rs (se 1 (by rfl) ⟨203471, by rfl⟩) R406943
theorem R210023 : Reach 210023 := rs (se 1 (by rfl) ⟨157517, by rfl⟩) R315035
theorem R277559 : Reach 277559 := rs (se 1 (by rfl) ⟨208169, by rfl⟩) R416339
theorem R2086397 : Reach 2086397 := rs (se 3 (by rfl) ⟨391199, by rfl⟩) R782399
theorem R259519 : Reach 259519 := rs (se 1 (by rfl) ⟨194639, by rfl⟩) R389279
theorem R1047815 : Reach 1047815 := rs (se 1 (by rfl) ⟨785861, by rfl⟩) R1571723
theorem R2691467 : Reach 2691467 := rs (se 1 (by rfl) ⟨2018600, by rfl⟩) R4037201
theorem R267515 : Reach 267515 := rs (se 1 (by rfl) ⟨200636, by rfl⟩) R401273
theorem R140015 : Reach 140015 := rs (se 1 (by rfl) ⟨105011, by rfl⟩) R210023
theorem R698543 : Reach 698543 := rs (se 1 (by rfl) ⟨523907, by rfl⟩) R1047815
theorem R1390931 : Reach 1390931 := rs (se 1 (by rfl) ⟨1043198, by rfl⟩) R2086397
theorem R179711 : Reach 179711 := rs (se 1 (by rfl) ⟨134783, by rfl⟩) R269567
theorem R180863 : Reach 180863 := rs (se 1 (by rfl) ⟨135647, by rfl⟩) R271295
theorem R181385 : Reach 181385 := rs (se 2 (by rfl) ⟨68019, by rfl⟩) R136039
theorem R346025 : Reach 346025 := rs (se 2 (by rfl) ⟨129759, by rfl⟩) R259519
theorem R185039 : Reach 185039 := rs (se 1 (by rfl) ⟨138779, by rfl⟩) R277559
theorem R230683 : Reach 230683 := rs (se 1 (by rfl) ⟨173012, by rfl⟩) R346025
theorem R465695 : Reach 465695 := rs (se 1 (by rfl) ⟨349271, by rfl⟩) R698543
theorem R927287 : Reach 927287 := rs (se 1 (by rfl) ⟨695465, by rfl⟩) R1390931
theorem R178343 : Reach 178343 := rs (se 1 (by rfl) ⟨133757, by rfl⟩) R267515
theorem R119807 : Reach 119807 := rs (se 1 (by rfl) ⟨89855, by rfl⟩) R179711
theorem R120575 : Reach 120575 := rs (se 1 (by rfl) ⟨90431, by rfl⟩) R180863
theorem R120923 : Reach 120923 := rs (se 1 (by rfl) ⟨90692, by rfl⟩) R181385
theorem R1794311 : Reach 1794311 := rs (se 1 (by rfl) ⟨1345733, by rfl⟩) R2691467
theorem R123359 : Reach 123359 := rs (se 1 (by rfl) ⟨92519, by rfl⟩) R185039
theorem R93343 : Reach 93343 := rs (se 1 (by rfl) ⟨70007, by rfl⟩) R140015
theorem R307577 : Reach 307577 := rs (se 2 (by rfl) ⟨115341, by rfl⟩) R230683
theorem R79871 : Reach 79871 := rs (se 1 (by rfl) ⟨59903, by rfl⟩) R119807
theorem R80383 : Reach 80383 := rs (se 1 (by rfl) ⟨60287, by rfl⟩) R120575
theorem R80615 : Reach 80615 := rs (se 1 (by rfl) ⟨60461, by rfl⟩) R120923
theorem R310463 : Reach 310463 := rs (se 1 (by rfl) ⟨232847, by rfl⟩) R465695
theorem R1196207 : Reach 1196207 := rs (se 1 (by rfl) ⟨897155, by rfl⟩) R1794311
theorem R82239 : Reach 82239 := rs (se 1 (by rfl) ⟨61679, by rfl⟩) R123359
theorem R118895 : Reach 118895 := rs (se 1 (by rfl) ⟨89171, by rfl⟩) R178343
theorem R124457 : Reach 124457 := rs (se 2 (by rfl) ⟨46671, by rfl⟩) R93343
theorem R618191 : Reach 618191 := rs (se 1 (by rfl) ⟨463643, by rfl⟩) R927287
theorem R205051 : Reach 205051 := rs (se 1 (by rfl) ⟨153788, by rfl⟩) R307577
theorem R206975 : Reach 206975 := rs (se 1 (by rfl) ⟨155231, by rfl⟩) R310463
theorem R797471 : Reach 797471 := rs (se 1 (by rfl) ⟨598103, by rfl⟩) R1196207
theorem R79263 : Reach 79263 := rs (se 1 (by rfl) ⟨59447, by rfl⟩) R118895
theorem R82971 : Reach 82971 := rs (se 1 (by rfl) ⟨62228, by rfl⟩) R124457
theorem R412127 : Reach 412127 := rs (se 1 (by rfl) ⟨309095, by rfl⟩) R618191
theorem R137983 : Reach 137983 := rs (se 1 (by rfl) ⟨103487, by rfl⟩) R206975
theorem R531647 : Reach 531647 := rs (se 1 (by rfl) ⟨398735, by rfl⟩) R797471
theorem R273401 : Reach 273401 := rs (se 2 (by rfl) ⟨102525, by rfl⟩) R205051
theorem R274751 : Reach 274751 := rs (se 1 (by rfl) ⟨206063, by rfl⟩) R412127
theorem R182267 : Reach 182267 := rs (se 1 (by rfl) ⟨136700, by rfl⟩) R273401
theorem R183167 : Reach 183167 := rs (se 1 (by rfl) ⟨137375, by rfl⟩) R274751
theorem R183977 : Reach 183977 := rs (se 2 (by rfl) ⟨68991, by rfl⟩) R137983
theorem R354431 : Reach 354431 := rs (se 1 (by rfl) ⟨265823, by rfl⟩) R531647
theorem R236287 : Reach 236287 := rs (se 1 (by rfl) ⟨177215, by rfl⟩) R354431
theorem R121511 : Reach 121511 := rs (se 1 (by rfl) ⟨91133, by rfl⟩) R182267
theorem R122111 : Reach 122111 := rs (se 1 (by rfl) ⟨91583, by rfl⟩) R183167
theorem R122651 : Reach 122651 := rs (se 1 (by rfl) ⟨91988, by rfl⟩) R183977
theorem R81007 : Reach 81007 := rs (se 1 (by rfl) ⟨60755, by rfl⟩) R121511
theorem R81407 : Reach 81407 := rs (se 1 (by rfl) ⟨61055, by rfl⟩) R122111
theorem R81767 : Reach 81767 := rs (se 1 (by rfl) ⟨61325, by rfl⟩) R122651
theorem R315049 : Reach 315049 := rs (se 2 (by rfl) ⟨118143, by rfl⟩) R236287
theorem R420065 : Reach 420065 := rs (se 2 (by rfl) ⟨157524, by rfl⟩) R315049
theorem R280043 : Reach 280043 := rs (se 1 (by rfl) ⟨210032, by rfl⟩) R420065
theorem R186695 : Reach 186695 := rs (se 1 (by rfl) ⟨140021, by rfl⟩) R280043
theorem R124463 : Reach 124463 := rs (se 1 (by rfl) ⟨93347, by rfl⟩) R186695
theorem R82975 : Reach 82975 := rs (se 1 (by rfl) ⟨62231, by rfl⟩) R124463

theorem C0 (j : ℕ) (h1 : 39563 ≤ j) (h2 : j ≤ 40262) : Reach (2 * j + 1) := by
  interval_cases j
  · exact R79127
  · exact R79129
  · exact R79131
  · exact R79133
  · exact R79135
  · exact R79137
  · exact R79139
  · exact R79141
  · exact R79143
  · exact R79145
  · exact R79147
  · exact R79149
  · exact R79151
  · exact R79153
  · exact R79155
  · exact R79157
  · exact R79159
  · exact R79161
  · exact R79163
  · exact R79165
  · exact R79167
  · exact R79169
  · exact R79171
  · exact R79173
  · exact R79175
  · exact R79177
  · exact R79179
  · exact R79181
  · exact R79183
  · exact R79185
  · exact R79187
  · exact R79189
  · exact R79191
  · exact R79193
  · exact R79195
  · exact R79197
  · exact R79199
  · exact R79201
  · exact R79203
  · exact R79205
  · exact R79207
  · exact R79209
  · exact R79211
  · exact R79213
  · exact R79215
  · exact R79217
  · exact R79219
  · exact R79221
  · exact R79223
  · exact R79225
  · exact R79227
  · exact R79229
  · exact R79231
  · exact R79233
  · exact R79235
  · exact R79237
  · exact R79239
  · exact R79241
  · exact R79243
  · exact R79245
  · exact R79247
  · exact R79249
  · exact R79251
  · exact R79253
  · exact R79255
  · exact R79257
  · exact R79259
  · exact R79261
  · exact R79263
  · exact R79265
  · exact R79267
  · exact R79269
  · exact R79271
  · exact R79273
  · exact R79275
  · exact R79277
  · exact R79279
  · exact R79281
  · exact R79283
  · exact R79285
  · exact R79287
  · exact R79289
  · exact R79291
  · exact R79293
  · exact R79295
  · exact R79297
  · exact R79299
  · exact R79301
  · exact R79303
  · exact R79305
  · exact R79307
  · exact R79309
  · exact R79311
  · exact R79313
  · exact R79315
  · exact R79317
  · exact R79319
  · exact R79321
  · exact R79323
  · exact R79325
  · exact R79327
  · exact R79329
  · exact R79331
  · exact R79333
  · exact R79335
  · exact R79337
  · exact R79339
  · exact R79341
  · exact R79343
  · exact R79345
  · exact R79347
  · exact R79349
  · exact R79351
  · exact R79353
  · exact R79355
  · exact R79357
  · exact R79359
  · exact R79361
  · exact R79363
  · exact R79365
  · exact R79367
  · exact R79369
  · exact R79371
  · exact R79373
  · exact R79375
  · exact R79377
  · exact R79379
  · exact R79381
  · exact R79383
  · exact R79385
  · exact R79387
  · exact R79389
  · exact R79391
  · exact R79393
  · exact R79395
  · exact R79397
  · exact R79399
  · exact R79401
  · exact R79403
  · exact R79405
  · exact R79407
  · exact R79409
  · exact R79411
  · exact R79413
  · exact R79415
  · exact R79417
  · exact R79419
  · exact R79421
  · exact R79423
  · exact R79425
  · exact R79427
  · exact R79429
  · exact R79431
  · exact R79433
  · exact R79435
  · exact R79437
  · exact R79439
  · exact R79441
  · exact R79443
  · exact R79445
  · exact R79447
  · exact R79449
  · exact R79451
  · exact R79453
  · exact R79455
  · exact R79457
  · exact R79459
  · exact R79461
  · exact R79463
  · exact R79465
  · exact R79467
  · exact R79469
  · exact R79471
  · exact R79473
  · exact R79475
  · exact R79477
  · exact R79479
  · exact R79481
  · exact R79483
  · exact R79485
  · exact R79487
  · exact R79489
  · exact R79491
  · exact R79493
  · exact R79495
  · exact R79497
  · exact R79499
  · exact R79501
  · exact R79503
  · exact R79505
  · exact R79507
  · exact R79509
  · exact R79511
  · exact R79513
  · exact R79515
  · exact R79517
  · exact R79519
  · exact R79521
  · exact R79523
  · exact R79525
  · exact R79527
  · exact R79529
  · exact R79531
  · exact R79533
  · exact R79535
  · exact R79537
  · exact R79539
  · exact R79541
  · exact R79543
  · exact R79545
  · exact R79547
  · exact R79549
  · exact R79551
  · exact R79553
  · exact R79555
  · exact R79557
  · exact R79559
  · exact R79561
  · exact R79563
  · exact R79565
  · exact R79567
  · exact R79569
  · exact R79571
  · exact R79573
  · exact R79575
  · exact R79577
  · exact R79579
  · exact R79581
  · exact R79583
  · exact R79585
  · exact R79587
  · exact R79589
  · exact R79591
  · exact R79593
  · exact R79595
  · exact R79597
  · exact R79599
  · exact R79601
  · exact R79603
  · exact R79605
  · exact R79607
  · exact R79609
  · exact R79611
  · exact R79613
  · exact R79615
  · exact R79617
  · exact R79619
  · exact R79621
  · exact R79623
  · exact R79625
  · exact R79627
  · exact R79629
  · exact R79631
  · exact R79633
  · exact R79635
  · exact R79637
  · exact R79639
  · exact R79641
  · exact R79643
  · exact R79645
  · exact R79647
  · exact R79649
  · exact R79651
  · exact R79653
  · exact R79655
  · exact R79657
  · exact R79659
  · exact R79661
  · exact R79663
  · exact R79665
  · exact R79667
  · exact R79669
  · exact R79671
  · exact R79673
  · exact R79675
  · exact R79677
  · exact R79679
  · exact R79681
  · exact R79683
  · exact R79685
  · exact R79687
  · exact R79689
  · exact R79691
  · exact R79693
  · exact R79695
  · exact R79697
  · exact R79699
  · exact R79701
  · exact R79703
  · exact R79705
  · exact R79707
  · exact R79709
  · exact R79711
  · exact R79713
  · exact R79715
  · exact R79717
  · exact R79719
  · exact R79721
  · exact R79723
  · exact R79725
  · exact R79727
  · exact R79729
  · exact R79731
  · exact R79733
  · exact R79735
  · exact R79737
  · exact R79739
  · exact R79741
  · exact R79743
  · exact R79745
  · exact R79747
  · exact R79749
  · exact R79751
  · exact R79753
  · exact R79755
  · exact R79757
  · exact R79759
  · exact R79761
  · exact R79763
  · exact R79765
  · exact R79767
  · exact R79769
  · exact R79771
  · exact R79773
  · exact R79775
  · exact R79777
  · exact R79779
  · exact R79781
  · exact R79783
  · exact R79785
  · exact R79787
  · exact R79789
  · exact R79791
  · exact R79793
  · exact R79795
  · exact R79797
  · exact R79799
  · exact R79801
  · exact R79803
  · exact R79805
  · exact R79807
  · exact R79809
  · exact R79811
  · exact R79813
  · exact R79815
  · exact R79817
  · exact R79819
  · exact R79821
  · exact R79823
  · exact R79825
  · exact R79827
  · exact R79829
  · exact R79831
  · exact R79833
  · exact R79835
  · exact R79837
  · exact R79839
  · exact R79841
  · exact R79843
  · exact R79845
  · exact R79847
  · exact R79849
  · exact R79851
  · exact R79853
  · exact R79855
  · exact R79857
  · exact R79859
  · exact R79861
  · exact R79863
  · exact R79865
  · exact R79867
  · exact R79869
  · exact R79871
  · exact R79873
  · exact R79875
  · exact R79877
  · exact R79879
  · exact R79881
  · exact R79883
  · exact R79885
  · exact R79887
  · exact R79889
  · exact R79891
  · exact R79893
  · exact R79895
  · exact R79897
  · exact R79899
  · exact R79901
  · exact R79903
  · exact R79905
  · exact R79907
  · exact R79909
  · exact R79911
  · exact R79913
  · exact R79915
  · exact R79917
  · exact R79919
  · exact R79921
  · exact R79923
  · exact R79925
  · exact R79927
  · exact R79929
  · exact R79931
  · exact R79933
  · exact R79935
  · exact R79937
  · exact R79939
  · exact R79941
  · exact R79943
  · exact R79945
  · exact R79947
  · exact R79949
  · exact R79951
  · exact R79953
  · exact R79955
  · exact R79957
  · exact R79959
  · exact R79961
  · exact R79963
  · exact R79965
  · exact R79967
  · exact R79969
  · exact R79971
  · exact R79973
  · exact R79975
  · exact R79977
  · exact R79979
  · exact R79981
  · exact R79983
  · exact R79985
  · exact R79987
  · exact R79989
  · exact R79991
  · exact R79993
  · exact R79995
  · exact R79997
  · exact R79999
  · exact R80001
  · exact R80003
  · exact R80005
  · exact R80007
  · exact R80009
  · exact R80011
  · exact R80013
  · exact R80015
  · exact R80017
  · exact R80019
  · exact R80021
  · exact R80023
  · exact R80025
  · exact R80027
  · exact R80029
  · exact R80031
  · exact R80033
  · exact R80035
  · exact R80037
  · exact R80039
  · exact R80041
  · exact R80043
  · exact R80045
  · exact R80047
  · exact R80049
  · exact R80051
  · exact R80053
  · exact R80055
  · exact R80057
  · exact R80059
  · exact R80061
  · exact R80063
  · exact R80065
  · exact R80067
  · exact R80069
  · exact R80071
  · exact R80073
  · exact R80075
  · exact R80077
  · exact R80079
  · exact R80081
  · exact R80083
  · exact R80085
  · exact R80087
  · exact R80089
  · exact R80091
  · exact R80093
  · exact R80095
  · exact R80097
  · exact R80099
  · exact R80101
  · exact R80103
  · exact R80105
  · exact R80107
  · exact R80109
  · exact R80111
  · exact R80113
  · exact R80115
  · exact R80117
  · exact R80119
  · exact R80121
  · exact R80123
  · exact R80125
  · exact R80127
  · exact R80129
  · exact R80131
  · exact R80133
  · exact R80135
  · exact R80137
  · exact R80139
  · exact R80141
  · exact R80143
  · exact R80145
  · exact R80147
  · exact R80149
  · exact R80151
  · exact R80153
  · exact R80155
  · exact R80157
  · exact R80159
  · exact R80161
  · exact R80163
  · exact R80165
  · exact R80167
  · exact R80169
  · exact R80171
  · exact R80173
  · exact R80175
  · exact R80177
  · exact R80179
  · exact R80181
  · exact R80183
  · exact R80185
  · exact R80187
  · exact R80189
  · exact R80191
  · exact R80193
  · exact R80195
  · exact R80197
  · exact R80199
  · exact R80201
  · exact R80203
  · exact R80205
  · exact R80207
  · exact R80209
  · exact R80211
  · exact R80213
  · exact R80215
  · exact R80217
  · exact R80219
  · exact R80221
  · exact R80223
  · exact R80225
  · exact R80227
  · exact R80229
  · exact R80231
  · exact R80233
  · exact R80235
  · exact R80237
  · exact R80239
  · exact R80241
  · exact R80243
  · exact R80245
  · exact R80247
  · exact R80249
  · exact R80251
  · exact R80253
  · exact R80255
  · exact R80257
  · exact R80259
  · exact R80261
  · exact R80263
  · exact R80265
  · exact R80267
  · exact R80269
  · exact R80271
  · exact R80273
  · exact R80275
  · exact R80277
  · exact R80279
  · exact R80281
  · exact R80283
  · exact R80285
  · exact R80287
  · exact R80289
  · exact R80291
  · exact R80293
  · exact R80295
  · exact R80297
  · exact R80299
  · exact R80301
  · exact R80303
  · exact R80305
  · exact R80307
  · exact R80309
  · exact R80311
  · exact R80313
  · exact R80315
  · exact R80317
  · exact R80319
  · exact R80321
  · exact R80323
  · exact R80325
  · exact R80327
  · exact R80329
  · exact R80331
  · exact R80333
  · exact R80335
  · exact R80337
  · exact R80339
  · exact R80341
  · exact R80343
  · exact R80345
  · exact R80347
  · exact R80349
  · exact R80351
  · exact R80353
  · exact R80355
  · exact R80357
  · exact R80359
  · exact R80361
  · exact R80363
  · exact R80365
  · exact R80367
  · exact R80369
  · exact R80371
  · exact R80373
  · exact R80375
  · exact R80377
  · exact R80379
  · exact R80381
  · exact R80383
  · exact R80385
  · exact R80387
  · exact R80389
  · exact R80391
  · exact R80393
  · exact R80395
  · exact R80397
  · exact R80399
  · exact R80401
  · exact R80403
  · exact R80405
  · exact R80407
  · exact R80409
  · exact R80411
  · exact R80413
  · exact R80415
  · exact R80417
  · exact R80419
  · exact R80421
  · exact R80423
  · exact R80425
  · exact R80427
  · exact R80429
  · exact R80431
  · exact R80433
  · exact R80435
  · exact R80437
  · exact R80439
  · exact R80441
  · exact R80443
  · exact R80445
  · exact R80447
  · exact R80449
  · exact R80451
  · exact R80453
  · exact R80455
  · exact R80457
  · exact R80459
  · exact R80461
  · exact R80463
  · exact R80465
  · exact R80467
  · exact R80469
  · exact R80471
  · exact R80473
  · exact R80475
  · exact R80477
  · exact R80479
  · exact R80481
  · exact R80483
  · exact R80485
  · exact R80487
  · exact R80489
  · exact R80491
  · exact R80493
  · exact R80495
  · exact R80497
  · exact R80499
  · exact R80501
  · exact R80503
  · exact R80505
  · exact R80507
  · exact R80509
  · exact R80511
  · exact R80513
  · exact R80515
  · exact R80517
  · exact R80519
  · exact R80521
  · exact R80523
  · exact R80525

theorem C1 (j : ℕ) (h1 : 40263 ≤ j) (h2 : j ≤ 40962) : Reach (2 * j + 1) := by
  interval_cases j
  · exact R80527
  · exact R80529
  · exact R80531
  · exact R80533
  · exact R80535
  · exact R80537
  · exact R80539
  · exact R80541
  · exact R80543
  · exact R80545
  · exact R80547
  · exact R80549
  · exact R80551
  · exact R80553
  · exact R80555
  · exact R80557
  · exact R80559
  · exact R80561
  · exact R80563
  · exact R80565
  · exact R80567
  · exact R80569
  · exact R80571
  · exact R80573
  · exact R80575
  · exact R80577
  · exact R80579
  · exact R80581
  · exact R80583
  · exact R80585
  · exact R80587
  · exact R80589
  · exact R80591
  · exact R80593
  · exact R80595
  · exact R80597
  · exact R80599
  · exact R80601
  · exact R80603
  · exact R80605
  · exact R80607
  · exact R80609
  · exact R80611
  · exact R80613
  · exact R80615
  · exact R80617
  · exact R80619
  · exact R80621
  · exact R80623
  · exact R80625
  · exact R80627
  · exact R80629
  · exact R80631
  · exact R80633
  · exact R80635
  · exact R80637
  · exact R80639
  · exact R80641
  · exact R80643
  · exact R80645
  · exact R80647
  · exact R80649
  · exact R80651
  · exact R80653
  · exact R80655
  · exact R80657
  · exact R80659
  · exact R80661
  · exact R80663
  · exact R80665
  · exact R80667
  · exact R80669
  · exact R80671
  · exact R80673
  · exact R80675
  · exact R80677
  · exact R80679
  · exact R80681
  · exact R80683
  · exact R80685
  · exact R80687
  · exact R80689
  · exact R80691
  · exact R80693
  · exact R80695
  · exact R80697
  · exact R80699
  · exact R80701
  · exact R80703
  · exact R80705
  · exact R80707
  · exact R80709
  · exact R80711
  · exact R80713
  · exact R80715
  · exact R80717
  · exact R80719
  · exact R80721
  · exact R80723
  · exact R80725
  · exact R80727
  · exact R80729
  · exact R80731
  · exact R80733
  · exact R80735
  · exact R80737
  · exact R80739
  · exact R80741
  · exact R80743
  · exact R80745
  · exact R80747
  · exact R80749
  · exact R80751
  · exact R80753
  · exact R80755
  · exact R80757
  · exact R80759
  · exact R80761
  · exact R80763
  · exact R80765
  · exact R80767
  · exact R80769
  · exact R80771
  · exact R80773
  · exact R80775
  · exact R80777
  · exact R80779
  · exact R80781
  · exact R80783
  · exact R80785
  · exact R80787
  · exact R80789
  · exact R80791
  · exact R80793
  · exact R80795
  · exact R80797
  · exact R80799
  · exact R80801
  · exact R80803
  · exact R80805
  · exact R80807
  · exact R80809
  · exact R80811
  · exact R80813
  · exact R80815
  · exact R80817
  · exact R80819
  · exact R80821
  · exact R80823
  · exact R80825
  · exact R80827
  · exact R80829
  · exact R80831
  · exact R80833
  · exact R80835
  · exact R80837
  · exact R80839
  · exact R80841
  · exact R80843
  · exact R80845
  · exact R80847
  · exact R80849
  · exact R80851
  · exact R80853
  · exact R80855
  · exact R80857
  · exact R80859
  · exact R80861
  · exact R80863
  · exact R80865
  · exact R80867
  · exact R80869
  · exact R80871
  · exact R80873
  · exact R80875
  · exact R80877
  · exact R80879
  · exact R80881
  · exact R80883
  · exact R80885
  · exact R80887
  · exact R80889
  · exact R80891
  · exact R80893
  · exact R80895
  · exact R80897
  · exact R80899
  · exact R80901
  · exact R80903
  · exact R80905
  · exact R80907
  · exact R80909
  · exact R80911
  · exact R80913
  · exact R80915
  · exact R80917
  · exact R80919
  · exact R80921
  · exact R80923
  · exact R80925
  · exact R80927
  · exact R80929
  · exact R80931
  · exact R80933
  · exact R80935
  · exact R80937
  · exact R80939
  · exact R80941
  · exact R80943
  · exact R80945
  · exact R80947
  · exact R80949
  · exact R80951
  · exact R80953
  · exact R80955
  · exact R80957
  · exact R80959
  · exact R80961
  · exact R80963
  · exact R80965
  · exact R80967
  · exact R80969
  · exact R80971
  · exact R80973
  · exact R80975
  · exact R80977
  · exact R80979
  · exact R80981
  · exact R80983
  · exact R80985
  · exact R80987
  · exact R80989
  · exact R80991
  · exact R80993
  · exact R80995
  · exact R80997
  · exact R80999
  · exact R81001
  · exact R81003
  · exact R81005
  · exact R81007
  · exact R81009
  · exact R81011
  · exact R81013
  · exact R81015
  · exact R81017
  · exact R81019
  · exact R81021
  · exact R81023
  · exact R81025
  · exact R81027
  · exact R81029
  · exact R81031
  · exact R81033
  · exact R81035
  · exact R81037
  · exact R81039
  · exact R81041
  · exact R81043
  · exact R81045
  · exact R81047
  · exact R81049
  · exact R81051
  · exact R81053
  · exact R81055
  · exact R81057
  · exact R81059
  · exact R81061
  · exact R81063
  · exact R81065
  · exact R81067
  · exact R81069
  · exact R81071
  · exact R81073
  · exact R81075
  · exact R81077
  · exact R81079
  · exact R81081
  · exact R81083
  · exact R81085
  · exact R81087
  · exact R81089
  · exact R81091
  · exact R81093
  · exact R81095
  · exact R81097
  · exact R81099
  · exact R81101
  · exact R81103
  · exact R81105
  · exact R81107
  · exact R81109
  · exact R81111
  · exact R81113
  · exact R81115
  · exact R81117
  · exact R81119
  · exact R81121
  · exact R81123
  · exact R81125
  · exact R81127
  · exact R81129
  · exact R81131
  · exact R81133
  · exact R81135
  · exact R81137
  · exact R81139
  · exact R81141
  · exact R81143
  · exact R81145
  · exact R81147
  · exact R81149
  · exact R81151
  · exact R81153
  · exact R81155
  · exact R81157
  · exact R81159
  · exact R81161
  · exact R81163
  · exact R81165
  · exact R81167
  · exact R81169
  · exact R81171
  · exact R81173
  · exact R81175
  · exact R81177
  · exact R81179
  · exact R81181
  · exact R81183
  · exact R81185
  · exact R81187
  · exact R81189
  · exact R81191
  · exact R81193
  · exact R81195
  · exact R81197
  · exact R81199
  · exact R81201
  · exact R81203
  · exact R81205
  · exact R81207
  · exact R81209
  · exact R81211
  · exact R81213
  · exact R81215
  · exact R81217
  · exact R81219
  · exact R81221
  · exact R81223
  · exact R81225
  · exact R81227
  · exact R81229
  · exact R81231
  · exact R81233
  · exact R81235
  · exact R81237
  · exact R81239
  · exact R81241
  · exact R81243
  · exact R81245
  · exact R81247
  · exact R81249
  · exact R81251
  · exact R81253
  · exact R81255
  · exact R81257
  · exact R81259
  · exact R81261
  · exact R81263
  · exact R81265
  · exact R81267
  · exact R81269
  · exact R81271
  · exact R81273
  · exact R81275
  · exact R81277
  · exact R81279
  · exact R81281
  · exact R81283
  · exact R81285
  · exact R81287
  · exact R81289
  · exact R81291
  · exact R81293
  · exact R81295
  · exact R81297
  · exact R81299
  · exact R81301
  · exact R81303
  · exact R81305
  · exact R81307
  · exact R81309
  · exact R81311
  · exact R81313
  · exact R81315
  · exact R81317
  · exact R81319
  · exact R81321
  · exact R81323
  · exact R81325
  · exact R81327
  · exact R81329
  · exact R81331
  · exact R81333
  · exact R81335
  · exact R81337
  · exact R81339
  · exact R81341
  · exact R81343
  · exact R81345
  · exact R81347
  · exact R81349
  · exact R81351
  · exact R81353
  · exact R81355
  · exact R81357
  · exact R81359
  · exact R81361
  · exact R81363
  · exact R81365
  · exact R81367
  · exact R81369
  · exact R81371
  · exact R81373
  · exact R81375
  · exact R81377
  · exact R81379
  · exact R81381
  · exact R81383
  · exact R81385
  · exact R81387
  · exact R81389
  · exact R81391
  · exact R81393
  · exact R81395
  · exact R81397
  · exact R81399
  · exact R81401
  · exact R81403
  · exact R81405
  · exact R81407
  · exact R81409
  · exact R81411
  · exact R81413
  · exact R81415
  · exact R81417
  · exact R81419
  · exact R81421
  · exact R81423
  · exact R81425
  · exact R81427
  · exact R81429
  · exact R81431
  · exact R81433
  · exact R81435
  · exact R81437
  · exact R81439
  · exact R81441
  · exact R81443
  · exact R81445
  · exact R81447
  · exact R81449
  · exact R81451
  · exact R81453
  · exact R81455
  · exact R81457
  · exact R81459
  · exact R81461
  · exact R81463
  · exact R81465
  · exact R81467
  · exact R81469
  · exact R81471
  · exact R81473
  · exact R81475
  · exact R81477
  · exact R81479
  · exact R81481
  · exact R81483
  · exact R81485
  · exact R81487
  · exact R81489
  · exact R81491
  · exact R81493
  · exact R81495
  · exact R81497
  · exact R81499
  · exact R81501
  · exact R81503
  · exact R81505
  · exact R81507
  · exact R81509
  · exact R81511
  · exact R81513
  · exact R81515
  · exact R81517
  · exact R81519
  · exact R81521
  · exact R81523
  · exact R81525
  · exact R81527
  · exact R81529
  · exact R81531
  · exact R81533
  · exact R81535
  · exact R81537
  · exact R81539
  · exact R81541
  · exact R81543
  · exact R81545
  · exact R81547
  · exact R81549
  · exact R81551
  · exact R81553
  · exact R81555
  · exact R81557
  · exact R81559
  · exact R81561
  · exact R81563
  · exact R81565
  · exact R81567
  · exact R81569
  · exact R81571
  · exact R81573
  · exact R81575
  · exact R81577
  · exact R81579
  · exact R81581
  · exact R81583
  · exact R81585
  · exact R81587
  · exact R81589
  · exact R81591
  · exact R81593
  · exact R81595
  · exact R81597
  · exact R81599
  · exact R81601
  · exact R81603
  · exact R81605
  · exact R81607
  · exact R81609
  · exact R81611
  · exact R81613
  · exact R81615
  · exact R81617
  · exact R81619
  · exact R81621
  · exact R81623
  · exact R81625
  · exact R81627
  · exact R81629
  · exact R81631
  · exact R81633
  · exact R81635
  · exact R81637
  · exact R81639
  · exact R81641
  · exact R81643
  · exact R81645
  · exact R81647
  · exact R81649
  · exact R81651
  · exact R81653
  · exact R81655
  · exact R81657
  · exact R81659
  · exact R81661
  · exact R81663
  · exact R81665
  · exact R81667
  · exact R81669
  · exact R81671
  · exact R81673
  · exact R81675
  · exact R81677
  · exact R81679
  · exact R81681
  · exact R81683
  · exact R81685
  · exact R81687
  · exact R81689
  · exact R81691
  · exact R81693
  · exact R81695
  · exact R81697
  · exact R81699
  · exact R81701
  · exact R81703
  · exact R81705
  · exact R81707
  · exact R81709
  · exact R81711
  · exact R81713
  · exact R81715
  · exact R81717
  · exact R81719
  · exact R81721
  · exact R81723
  · exact R81725
  · exact R81727
  · exact R81729
  · exact R81731
  · exact R81733
  · exact R81735
  · exact R81737
  · exact R81739
  · exact R81741
  · exact R81743
  · exact R81745
  · exact R81747
  · exact R81749
  · exact R81751
  · exact R81753
  · exact R81755
  · exact R81757
  · exact R81759
  · exact R81761
  · exact R81763
  · exact R81765
  · exact R81767
  · exact R81769
  · exact R81771
  · exact R81773
  · exact R81775
  · exact R81777
  · exact R81779
  · exact R81781
  · exact R81783
  · exact R81785
  · exact R81787
  · exact R81789
  · exact R81791
  · exact R81793
  · exact R81795
  · exact R81797
  · exact R81799
  · exact R81801
  · exact R81803
  · exact R81805
  · exact R81807
  · exact R81809
  · exact R81811
  · exact R81813
  · exact R81815
  · exact R81817
  · exact R81819
  · exact R81821
  · exact R81823
  · exact R81825
  · exact R81827
  · exact R81829
  · exact R81831
  · exact R81833
  · exact R81835
  · exact R81837
  · exact R81839
  · exact R81841
  · exact R81843
  · exact R81845
  · exact R81847
  · exact R81849
  · exact R81851
  · exact R81853
  · exact R81855
  · exact R81857
  · exact R81859
  · exact R81861
  · exact R81863
  · exact R81865
  · exact R81867
  · exact R81869
  · exact R81871
  · exact R81873
  · exact R81875
  · exact R81877
  · exact R81879
  · exact R81881
  · exact R81883
  · exact R81885
  · exact R81887
  · exact R81889
  · exact R81891
  · exact R81893
  · exact R81895
  · exact R81897
  · exact R81899
  · exact R81901
  · exact R81903
  · exact R81905
  · exact R81907
  · exact R81909
  · exact R81911
  · exact R81913
  · exact R81915
  · exact R81917
  · exact R81919
  · exact R81921
  · exact R81923
  · exact R81925

theorem C2 (j : ℕ) (h1 : 40963 ≤ j) (h2 : j ≤ 41563) : Reach (2 * j + 1) := by
  interval_cases j
  · exact R81927
  · exact R81929
  · exact R81931
  · exact R81933
  · exact R81935
  · exact R81937
  · exact R81939
  · exact R81941
  · exact R81943
  · exact R81945
  · exact R81947
  · exact R81949
  · exact R81951
  · exact R81953
  · exact R81955
  · exact R81957
  · exact R81959
  · exact R81961
  · exact R81963
  · exact R81965
  · exact R81967
  · exact R81969
  · exact R81971
  · exact R81973
  · exact R81975
  · exact R81977
  · exact R81979
  · exact R81981
  · exact R81983
  · exact R81985
  · exact R81987
  · exact R81989
  · exact R81991
  · exact R81993
  · exact R81995
  · exact R81997
  · exact R81999
  · exact R82001
  · exact R82003
  · exact R82005
  · exact R82007
  · exact R82009
  · exact R82011
  · exact R82013
  · exact R82015
  · exact R82017
  · exact R82019
  · exact R82021
  · exact R82023
  · exact R82025
  · exact R82027
  · exact R82029
  · exact R82031
  · exact R82033
  · exact R82035
  · exact R82037
  · exact R82039
  · exact R82041
  · exact R82043
  · exact R82045
  · exact R82047
  · exact R82049
  · exact R82051
  · exact R82053
  · exact R82055
  · exact R82057
  · exact R82059
  · exact R82061
  · exact R82063
  · exact R82065
  · exact R82067
  · exact R82069
  · exact R82071
  · exact R82073
  · exact R82075
  · exact R82077
  · exact R82079
  · exact R82081
  · exact R82083
  · exact R82085
  · exact R82087
  · exact R82089
  · exact R82091
  · exact R82093
  · exact R82095
  · exact R82097
  · exact R82099
  · exact R82101
  · exact R82103
  · exact R82105
  · exact R82107
  · exact R82109
  · exact R82111
  · exact R82113
  · exact R82115
  · exact R82117
  · exact R82119
  · exact R82121
  · exact R82123
  · exact R82125
  · exact R82127
  · exact R82129
  · exact R82131
  · exact R82133
  · exact R82135
  · exact R82137
  · exact R82139
  · exact R82141
  · exact R82143
  · exact R82145
  · exact R82147
  · exact R82149
  · exact R82151
  · exact R82153
  · exact R82155
  · exact R82157
  · exact R82159
  · exact R82161
  · exact R82163
  · exact R82165
  · exact R82167
  · exact R82169
  · exact R82171
  · exact R82173
  · exact R82175
  · exact R82177
  · exact R82179
  · exact R82181
  · exact R82183
  · exact R82185
  · exact R82187
  · exact R82189
  · exact R82191
  · exact R82193
  · exact R82195
  · exact R82197
  · exact R82199
  · exact R82201
  · exact R82203
  · exact R82205
  · exact R82207
  · exact R82209
  · exact R82211
  · exact R82213
  · exact R82215
  · exact R82217
  · exact R82219
  · exact R82221
  · exact R82223
  · exact R82225
  · exact R82227
  · exact R82229
  · exact R82231
  · exact R82233
  · exact R82235
  · exact R82237
  · exact R82239
  · exact R82241
  · exact R82243
  · exact R82245
  · exact R82247
  · exact R82249
  · exact R82251
  · exact R82253
  · exact R82255
  · exact R82257
  · exact R82259
  · exact R82261
  · exact R82263
  · exact R82265
  · exact R82267
  · exact R82269
  · exact R82271
  · exact R82273
  · exact R82275
  · exact R82277
  · exact R82279
  · exact R82281
  · exact R82283
  · exact R82285
  · exact R82287
  · exact R82289
  · exact R82291
  · exact R82293
  · exact R82295
  · exact R82297
  · exact R82299
  · exact R82301
  · exact R82303
  · exact R82305
  · exact R82307
  · exact R82309
  · exact R82311
  · exact R82313
  · exact R82315
  · exact R82317
  · exact R82319
  · exact R82321
  · exact R82323
  · exact R82325
  · exact R82327
  · exact R82329
  · exact R82331
  · exact R82333
  · exact R82335
  · exact R82337
  · exact R82339
  · exact R82341
  · exact R82343
  · exact R82345
  · exact R82347
  · exact R82349
  · exact R82351
  · exact R82353
  · exact R82355
  · exact R82357
  · exact R82359
  · exact R82361
  · exact R82363
  · exact R82365
  · exact R82367
  · exact R82369
  · exact R82371
  · exact R82373
  · exact R82375
  · exact R82377
  · exact R82379
  · exact R82381
  · exact R82383
  · exact R82385
  · exact R82387
  · exact R82389
  · exact R82391
  · exact R82393
  · exact R82395
  · exact R82397
  · exact R82399
  · exact R82401
  · exact R82403
  · exact R82405
  · exact R82407
  · exact R82409
  · exact R82411
  · exact R82413
  · exact R82415
  · exact R82417
  · exact R82419
  · exact R82421
  · exact R82423
  · exact R82425
  · exact R82427
  · exact R82429
  · exact R82431
  · exact R82433
  · exact R82435
  · exact R82437
  · exact R82439
  · exact R82441
  · exact R82443
  · exact R82445
  · exact R82447
  · exact R82449
  · exact R82451
  · exact R82453
  · exact R82455
  · exact R82457
  · exact R82459
  · exact R82461
  · exact R82463
  · exact R82465
  · exact R82467
  · exact R82469
  · exact R82471
  · exact R82473
  · exact R82475
  · exact R82477
  · exact R82479
  · exact R82481
  · exact R82483
  · exact R82485
  · exact R82487
  · exact R82489
  · exact R82491
  · exact R82493
  · exact R82495
  · exact R82497
  · exact R82499
  · exact R82501
  · exact R82503
  · exact R82505
  · exact R82507
  · exact R82509
  · exact R82511
  · exact R82513
  · exact R82515
  · exact R82517
  · exact R82519
  · exact R82521
  · exact R82523
  · exact R82525
  · exact R82527
  · exact R82529
  · exact R82531
  · exact R82533
  · exact R82535
  · exact R82537
  · exact R82539
  · exact R82541
  · exact R82543
  · exact R82545
  · exact R82547
  · exact R82549
  · exact R82551
  · exact R82553
  · exact R82555
  · exact R82557
  · exact R82559
  · exact R82561
  · exact R82563
  · exact R82565
  · exact R82567
  · exact R82569
  · exact R82571
  · exact R82573
  · exact R82575
  · exact R82577
  · exact R82579
  · exact R82581
  · exact R82583
  · exact R82585
  · exact R82587
  · exact R82589
  · exact R82591
  · exact R82593
  · exact R82595
  · exact R82597
  · exact R82599
  · exact R82601
  · exact R82603
  · exact R82605
  · exact R82607
  · exact R82609
  · exact R82611
  · exact R82613
  · exact R82615
  · exact R82617
  · exact R82619
  · exact R82621
  · exact R82623
  · exact R82625
  · exact R82627
  · exact R82629
  · exact R82631
  · exact R82633
  · exact R82635
  · exact R82637
  · exact R82639
  · exact R82641
  · exact R82643
  · exact R82645
  · exact R82647
  · exact R82649
  · exact R82651
  · exact R82653
  · exact R82655
  · exact R82657
  · exact R82659
  · exact R82661
  · exact R82663
  · exact R82665
  · exact R82667
  · exact R82669
  · exact R82671
  · exact R82673
  · exact R82675
  · exact R82677
  · exact R82679
  · exact R82681
  · exact R82683
  · exact R82685
  · exact R82687
  · exact R82689
  · exact R82691
  · exact R82693
  · exact R82695
  · exact R82697
  · exact R82699
  · exact R82701
  · exact R82703
  · exact R82705
  · exact R82707
  · exact R82709
  · exact R82711
  · exact R82713
  · exact R82715
  · exact R82717
  · exact R82719
  · exact R82721
  · exact R82723
  · exact R82725
  · exact R82727
  · exact R82729
  · exact R82731
  · exact R82733
  · exact R82735
  · exact R82737
  · exact R82739
  · exact R82741
  · exact R82743
  · exact R82745
  · exact R82747
  · exact R82749
  · exact R82751
  · exact R82753
  · exact R82755
  · exact R82757
  · exact R82759
  · exact R82761
  · exact R82763
  · exact R82765
  · exact R82767
  · exact R82769
  · exact R82771
  · exact R82773
  · exact R82775
  · exact R82777
  · exact R82779
  · exact R82781
  · exact R82783
  · exact R82785
  · exact R82787
  · exact R82789
  · exact R82791
  · exact R82793
  · exact R82795
  · exact R82797
  · exact R82799
  · exact R82801
  · exact R82803
  · exact R82805
  · exact R82807
  · exact R82809
  · exact R82811
  · exact R82813
  · exact R82815
  · exact R82817
  · exact R82819
  · exact R82821
  · exact R82823
  · exact R82825
  · exact R82827
  · exact R82829
  · exact R82831
  · exact R82833
  · exact R82835
  · exact R82837
  · exact R82839
  · exact R82841
  · exact R82843
  · exact R82845
  · exact R82847
  · exact R82849
  · exact R82851
  · exact R82853
  · exact R82855
  · exact R82857
  · exact R82859
  · exact R82861
  · exact R82863
  · exact R82865
  · exact R82867
  · exact R82869
  · exact R82871
  · exact R82873
  · exact R82875
  · exact R82877
  · exact R82879
  · exact R82881
  · exact R82883
  · exact R82885
  · exact R82887
  · exact R82889
  · exact R82891
  · exact R82893
  · exact R82895
  · exact R82897
  · exact R82899
  · exact R82901
  · exact R82903
  · exact R82905
  · exact R82907
  · exact R82909
  · exact R82911
  · exact R82913
  · exact R82915
  · exact R82917
  · exact R82919
  · exact R82921
  · exact R82923
  · exact R82925
  · exact R82927
  · exact R82929
  · exact R82931
  · exact R82933
  · exact R82935
  · exact R82937
  · exact R82939
  · exact R82941
  · exact R82943
  · exact R82945
  · exact R82947
  · exact R82949
  · exact R82951
  · exact R82953
  · exact R82955
  · exact R82957
  · exact R82959
  · exact R82961
  · exact R82963
  · exact R82965
  · exact R82967
  · exact R82969
  · exact R82971
  · exact R82973
  · exact R82975
  · exact R82977
  · exact R82979
  · exact R82981
  · exact R82983
  · exact R82985
  · exact R82987
  · exact R82989
  · exact R82991
  · exact R82993
  · exact R82995
  · exact R82997
  · exact R82999
  · exact R83001
  · exact R83003
  · exact R83005
  · exact R83007
  · exact R83009
  · exact R83011
  · exact R83013
  · exact R83015
  · exact R83017
  · exact R83019
  · exact R83021
  · exact R83023
  · exact R83025
  · exact R83027
  · exact R83029
  · exact R83031
  · exact R83033
  · exact R83035
  · exact R83037
  · exact R83039
  · exact R83041
  · exact R83043
  · exact R83045
  · exact R83047
  · exact R83049
  · exact R83051
  · exact R83053
  · exact R83055
  · exact R83057
  · exact R83059
  · exact R83061
  · exact R83063
  · exact R83065
  · exact R83067
  · exact R83069
  · exact R83071
  · exact R83073
  · exact R83075
  · exact R83077
  · exact R83079
  · exact R83081
  · exact R83083
  · exact R83085
  · exact R83087
  · exact R83089
  · exact R83091
  · exact R83093
  · exact R83095
  · exact R83097
  · exact R83099
  · exact R83101
  · exact R83103
  · exact R83105
  · exact R83107
  · exact R83109
  · exact R83111
  · exact R83113
  · exact R83115
  · exact R83117
  · exact R83119
  · exact R83121
  · exact R83123
  · exact R83125
  · exact R83127

theorem solution (m : ℕ) (hm : 0 < m) (hodd : Odd m) (hle : m ≤ 83127) :
    ∃ k : ℕ, syracuseStep^[k] m = 1 := by
  rcases Nat.lt_or_ge m 79127 with hlo | hlo
  · exact syracuse_reaches_one_below_79127 m hm hodd (by omega)
  obtain ⟨j, rfl⟩ : ∃ j, m = 2 * j + 1 := by obtain ⟨t, ht⟩ := hodd; exact ⟨t, by omega⟩
  rcases Nat.lt_or_ge j 40263 with h0 | h0
  · exact C0 j (by omega) (by omega)
  rcases Nat.lt_or_ge j 40963 with h1 | h1
  · exact C1 j (by omega) (by omega)
  exact C2 j (by omega) (by omega)
