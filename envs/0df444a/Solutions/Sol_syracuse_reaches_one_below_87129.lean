-- Prove2me | solution 1 for syracuse_reaches_one_below_87129
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T06:38:53.288567+00:00
-- url     : https://prove2.me/submissions/d628648e-2434-488e-97ee-82b104f4946d

import Mathlib
import Definitions.Def_syracuseStep
import Theorems.Thm_syracuse_reaches_one_below_83128

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
theorem B (n : ℕ) (h1 : 0 < n) (h2 : Odd n) (h3 : n ≤ 83127) : Reach n :=
  syracuse_reaches_one_below_83128 n h1 h2 h3
theorem R327685 : Reach 327685 := rs (se 4 (by rfl) ⟨30720, by rfl⟩) (B 61441 (by norm_num) ⟨30720, by rfl⟩ (by norm_num))
theorem R98345 : Reach 98345 := rs (se 2 (by rfl) ⟨36879, by rfl⟩) (B 73759 (by norm_num) ⟨36879, by rfl⟩ (by norm_num))
theorem R98381 : Reach 98381 := rs (se 3 (by rfl) ⟨18446, by rfl⟩) (B 36893 (by norm_num) ⟨18446, by rfl⟩ (by norm_num))
theorem R163957 : Reach 163957 := rs (se 5 (by rfl) ⟨7685, by rfl⟩) (B 15371 (by norm_num) ⟨7685, by rfl⟩ (by norm_num))
theorem R557237 : Reach 557237 := rs (se 5 (by rfl) ⟨26120, by rfl⟩) (B 52241 (by norm_num) ⟨26120, by rfl⟩ (by norm_num))
theorem R295093 : Reach 295093 := rs (se 5 (by rfl) ⟨13832, by rfl⟩) (B 27665 (by norm_num) ⟨13832, by rfl⟩ (by norm_num))
theorem R164101 : Reach 164101 := rs (se 4 (by rfl) ⟨15384, by rfl⟩) (B 30769 (by norm_num) ⟨15384, by rfl⟩ (by norm_num))
theorem R327989 : Reach 327989 := rs (se 5 (by rfl) ⟨15374, by rfl⟩) (B 30749 (by norm_num) ⟨15374, by rfl⟩ (by norm_num))
theorem R164261 : Reach 164261 := rs (se 4 (by rfl) ⟨15399, by rfl⟩) (B 30799 (by norm_num) ⟨15399, by rfl⟩ (by norm_num))
theorem R393653 : Reach 393653 := rs (se 5 (by rfl) ⟨18452, by rfl⟩) (B 36905 (by norm_num) ⟨18452, by rfl⟩ (by norm_num))
theorem R164405 : Reach 164405 := rs (se 5 (by rfl) ⟨7706, by rfl⟩) (B 15413 (by norm_num) ⟨7706, by rfl⟩ (by norm_num))
theorem R361061 : Reach 361061 := rs (se 4 (by rfl) ⟨33849, by rfl⟩) (B 67699 (by norm_num) ⟨33849, by rfl⟩ (by norm_num))
theorem R164693 : Reach 164693 := rs (se 9 (by rfl) ⟨482, by rfl⟩) (B 965 (by norm_num) ⟨482, by rfl⟩ (by norm_num))
theorem R426869 : Reach 426869 := rs (se 5 (by rfl) ⟨20009, by rfl⟩) (B 40019 (by norm_num) ⟨20009, by rfl⟩ (by norm_num))
theorem R623477 : Reach 623477 := rs (se 5 (by rfl) ⟨29225, by rfl⟩) (B 58451 (by norm_num) ⟨29225, by rfl⟩ (by norm_num))
theorem R263093 : Reach 263093 := rs (se 5 (by rfl) ⟨12332, by rfl⟩) (B 24665 (by norm_num) ⟨12332, by rfl⟩ (by norm_num))
theorem R99289 : Reach 99289 := rs (se 2 (by rfl) ⟨37233, by rfl⟩) (B 74467 (by norm_num) ⟨37233, by rfl⟩ (by norm_num))
theorem R164845 : Reach 164845 := rs (se 3 (by rfl) ⟨30908, by rfl⟩) (B 61817 (by norm_num) ⟨30908, by rfl⟩ (by norm_num))
theorem R984149 : Reach 984149 := rs (se 8 (by rfl) ⟨5766, by rfl⟩) (B 11533 (by norm_num) ⟨5766, by rfl⟩ (by norm_num))
theorem R165149 : Reach 165149 := rs (se 3 (by rfl) ⟨30965, by rfl⟩) (B 61931 (by norm_num) ⟨30965, by rfl⟩ (by norm_num))
theorem R165341 : Reach 165341 := rs (se 3 (by rfl) ⟨31001, by rfl⟩) (B 62003 (by norm_num) ⟨31001, by rfl⟩ (by norm_num))
theorem R99949 : Reach 99949 := rs (se 3 (by rfl) ⟨18740, by rfl⟩) (B 37481 (by norm_num) ⟨18740, by rfl⟩ (by norm_num))
theorem R264005 : Reach 264005 := rs (se 4 (by rfl) ⟨24750, by rfl⟩) (B 49501 (by norm_num) ⟨24750, by rfl⟩ (by norm_num))
theorem R493397 : Reach 493397 := rs (se 9 (by rfl) ⟨1445, by rfl⟩) (B 2891 (by norm_num) ⟨1445, by rfl⟩ (by norm_num))
theorem R755669 : Reach 755669 := rs (se 7 (by rfl) ⟨8855, by rfl⟩) (B 17711 (by norm_num) ⟨8855, by rfl⟩ (by norm_num))
theorem R428165 : Reach 428165 := rs (se 4 (by rfl) ⟨40140, by rfl⟩) (B 80281 (by norm_num) ⟨40140, by rfl⟩ (by norm_num))
theorem R657557 : Reach 657557 := rs (se 6 (by rfl) ⟨15411, by rfl⟩) (B 30823 (by norm_num) ⟨15411, by rfl⟩ (by norm_num))
theorem R100549 : Reach 100549 := rs (se 4 (by rfl) ⟨9426, by rfl⟩) (B 18853 (by norm_num) ⟨9426, by rfl⟩ (by norm_num))
theorem R133373 : Reach 133373 := rs (se 3 (by rfl) ⟨25007, by rfl⟩) (B 50015 (by norm_num) ⟨25007, by rfl⟩ (by norm_num))
theorem R166141 : Reach 166141 := rs (se 3 (by rfl) ⟨31151, by rfl⟩) (B 62303 (by norm_num) ⟨31151, by rfl⟩ (by norm_num))
theorem R330101 : Reach 330101 := rs (se 5 (by rfl) ⟨15473, by rfl⟩) (B 30947 (by norm_num) ⟨15473, by rfl⟩ (by norm_num))
theorem R658037 : Reach 658037 := rs (se 5 (by rfl) ⟨30845, by rfl⟩) (B 61691 (by norm_num) ⟨30845, by rfl⟩ (by norm_num))
theorem R330389 : Reach 330389 := rs (se 6 (by rfl) ⟨7743, by rfl⟩) (B 15487 (by norm_num) ⟨7743, by rfl⟩ (by norm_num))
theorem R133829 : Reach 133829 := rs (se 4 (by rfl) ⟨12546, by rfl⟩) (B 25093 (by norm_num) ⟨12546, by rfl⟩ (by norm_num))
theorem R232757 : Reach 232757 := rs (se 5 (by rfl) ⟨10910, by rfl⟩) (B 21821 (by norm_num) ⟨10910, by rfl⟩ (by norm_num))
theorem R101693 : Reach 101693 := rs (se 3 (by rfl) ⟨19067, by rfl⟩) (B 38135 (by norm_num) ⟨19067, by rfl⟩ (by norm_num))
theorem R101741 : Reach 101741 := rs (se 3 (by rfl) ⟨19076, by rfl⟩) (B 38153 (by norm_num) ⟨19076, by rfl⟩ (by norm_num))
theorem R429461 : Reach 429461 := rs (se 6 (by rfl) ⟨10065, by rfl⟩) (B 20131 (by norm_num) ⟨10065, by rfl⟩ (by norm_num))
theorem R101837 : Reach 101837 := rs (se 3 (by rfl) ⟨19094, by rfl⟩) (B 38189 (by norm_num) ⟨19094, by rfl⟩ (by norm_num))
theorem R102001 : Reach 102001 := rs (se 2 (by rfl) ⟨38250, by rfl⟩) (B 76501 (by norm_num) ⟨38250, by rfl⟩ (by norm_num))
theorem R102217 : Reach 102217 := rs (se 2 (by rfl) ⟨38331, by rfl⟩) (B 76663 (by norm_num) ⟨38331, by rfl⟩ (by norm_num))
theorem R102385 : Reach 102385 := rs (se 2 (by rfl) ⟨38394, by rfl⟩) (B 76789 (by norm_num) ⟨38394, by rfl⟩ (by norm_num))
theorem R135245 : Reach 135245 := rs (se 3 (by rfl) ⟨25358, by rfl⟩) (B 50717 (by norm_num) ⟨25358, by rfl⟩ (by norm_num))
theorem R102565 : Reach 102565 := rs (se 4 (by rfl) ⟨9615, by rfl⟩) (B 19231 (by norm_num) ⟨9615, by rfl⟩ (by norm_num))
theorem R135469 : Reach 135469 := rs (se 3 (by rfl) ⟨25400, by rfl⟩) (B 50801 (by norm_num) ⟨25400, by rfl⟩ (by norm_num))
theorem R463157 : Reach 463157 := rs (se 5 (by rfl) ⟨21710, by rfl⟩) (B 43421 (by norm_num) ⟨21710, by rfl⟩ (by norm_num))
theorem R1085845 : Reach 1085845 := rs (se 6 (by rfl) ⟨25449, by rfl⟩) (B 50899 (by norm_num) ⟨25449, by rfl⟩ (by norm_num))
theorem R102913 : Reach 102913 := rs (se 2 (by rfl) ⟨38592, by rfl⟩) (B 77185 (by norm_num) ⟨38592, by rfl⟩ (by norm_num))
theorem R266773 : Reach 266773 := rs (se 6 (by rfl) ⟨6252, by rfl⟩) (B 12505 (by norm_num) ⟨6252, by rfl⟩ (by norm_num))
theorem R365093 : Reach 365093 := rs (se 4 (by rfl) ⟨34227, by rfl⟩) (B 68455 (by norm_num) ⟨34227, by rfl⟩ (by norm_num))
theorem R135845 : Reach 135845 := rs (se 4 (by rfl) ⟨12735, by rfl⟩) (B 25471 (by norm_num) ⟨12735, by rfl⟩ (by norm_num))
theorem R430757 : Reach 430757 := rs (se 4 (by rfl) ⟨40383, by rfl⟩) (B 80767 (by norm_num) ⟨40383, by rfl⟩ (by norm_num))
theorem R201541 : Reach 201541 := rs (se 4 (by rfl) ⟨18894, by rfl⟩) (B 37789 (by norm_num) ⟨18894, by rfl⟩ (by norm_num))
theorem R1217429 : Reach 1217429 := rs (se 6 (by rfl) ⟨28533, by rfl⟩) (B 57067 (by norm_num) ⟨28533, by rfl⟩ (by norm_num))
theorem R267509 : Reach 267509 := rs (se 5 (by rfl) ⟨12539, by rfl⟩) (B 25079 (by norm_num) ⟨12539, by rfl⟩ (by norm_num))
theorem R104009 : Reach 104009 := rs (se 2 (by rfl) ⟨39003, by rfl⟩) (B 78007 (by norm_num) ⟨39003, by rfl⟩ (by norm_num))
theorem R104045 : Reach 104045 := rs (se 3 (by rfl) ⟨19508, by rfl⟩) (B 39017 (by norm_num) ⟨19508, by rfl⟩ (by norm_num))
theorem R300725 : Reach 300725 := rs (se 5 (by rfl) ⟨14096, by rfl⟩) (B 28193 (by norm_num) ⟨14096, by rfl⟩ (by norm_num))
theorem R136885 : Reach 136885 := rs (se 5 (by rfl) ⟨6416, by rfl⟩) (B 12833 (by norm_num) ⟨6416, by rfl⟩ (by norm_num))
theorem R169661 : Reach 169661 := rs (se 3 (by rfl) ⟨31811, by rfl⟩) (B 63623 (by norm_num) ⟨31811, by rfl⟩ (by norm_num))
theorem R432053 : Reach 432053 := rs (se 5 (by rfl) ⟨20252, by rfl⟩) (B 40505 (by norm_num) ⟨20252, by rfl⟩ (by norm_num))
theorem R137141 : Reach 137141 := rs (se 5 (by rfl) ⟨6428, by rfl⟩) (B 12857 (by norm_num) ⟨6428, by rfl⟩ (by norm_num))
theorem R563221 : Reach 563221 := rs (se 6 (by rfl) ⟨13200, by rfl⟩) (B 26401 (by norm_num) ⟨13200, by rfl⟩ (by norm_num))
theorem R137333 : Reach 137333 := rs (se 5 (by rfl) ⟨6437, by rfl⟩) (B 12875 (by norm_num) ⟨6437, by rfl⟩ (by norm_num))
theorem R104593 : Reach 104593 := rs (se 2 (by rfl) ⟨39222, by rfl⟩) (B 78445 (by norm_num) ⟨39222, by rfl⟩ (by norm_num))
theorem R202925 : Reach 202925 := rs (se 3 (by rfl) ⟨38048, by rfl⟩) (B 76097 (by norm_num) ⟨38048, by rfl⟩ (by norm_num))
theorem R891157 : Reach 891157 := rs (se 6 (by rfl) ⟨20886, by rfl⟩) (B 41773 (by norm_num) ⟨20886, by rfl⟩ (by norm_num))
theorem R366869 : Reach 366869 := rs (se 6 (by rfl) ⟨8598, by rfl⟩) (B 17197 (by norm_num) ⟨8598, by rfl⟩ (by norm_num))
theorem R203357 : Reach 203357 := rs (se 3 (by rfl) ⟨38129, by rfl⟩) (B 76259 (by norm_num) ⟨38129, by rfl⟩ (by norm_num))
theorem R170741 : Reach 170741 := rs (se 5 (by rfl) ⟨8003, by rfl⟩) (B 16007 (by norm_num) ⟨8003, by rfl⟩ (by norm_num))
theorem R105229 : Reach 105229 := rs (se 3 (by rfl) ⟨19730, by rfl⟩) (B 39461 (by norm_num) ⟨19730, by rfl⟩ (by norm_num))
theorem R105401 : Reach 105401 := rs (se 2 (by rfl) ⟨39525, by rfl⟩) (B 79051 (by norm_num) ⟨39525, by rfl⟩ (by norm_num))
theorem R105457 : Reach 105457 := rs (se 2 (by rfl) ⟨39546, by rfl⟩) (B 79093 (by norm_num) ⟨39546, by rfl⟩ (by norm_num))
theorem R138269 : Reach 138269 := rs (se 3 (by rfl) ⟨25925, by rfl⟩) (B 51851 (by norm_num) ⟨25925, by rfl⟩ (by norm_num))
theorem R105553 : Reach 105553 := rs (se 2 (by rfl) ⟨39582, by rfl⟩) (B 79165 (by norm_num) ⟨39582, by rfl⟩ (by norm_num))
theorem R433349 : Reach 433349 := rs (se 4 (by rfl) ⟨40626, by rfl⟩) (B 81253 (by norm_num) ⟨40626, by rfl⟩ (by norm_num))
theorem R236789 : Reach 236789 := rs (se 5 (by rfl) ⟨11099, by rfl⟩) (B 22199 (by norm_num) ⟨11099, by rfl⟩ (by norm_num))
theorem R367861 : Reach 367861 := rs (se 5 (by rfl) ⟨17243, by rfl⟩) (B 34487 (by norm_num) ⟨17243, by rfl⟩ (by norm_num))
theorem R105725 : Reach 105725 := rs (se 3 (by rfl) ⟨19823, by rfl⟩) (B 39647 (by norm_num) ⟨19823, by rfl⟩ (by norm_num))
theorem R105781 : Reach 105781 := rs (se 5 (by rfl) ⟨4958, by rfl⟩) (B 9917 (by norm_num) ⟨4958, by rfl⟩ (by norm_num))
theorem R269669 : Reach 269669 := rs (se 4 (by rfl) ⟨25281, by rfl⟩) (B 50563 (by norm_num) ⟨25281, by rfl⟩ (by norm_num))
theorem R105877 : Reach 105877 := rs (se 6 (by rfl) ⟨2481, by rfl⟩) (B 4963 (by norm_num) ⟨2481, by rfl⟩ (by norm_num))
theorem R138653 : Reach 138653 := rs (se 3 (by rfl) ⟨25997, by rfl⟩) (B 51995 (by norm_num) ⟨25997, by rfl⟩ (by norm_num))
theorem R138781 : Reach 138781 := rs (se 3 (by rfl) ⟨26021, by rfl⟩) (B 52043 (by norm_num) ⟨26021, by rfl⟩ (by norm_num))
theorem R106049 : Reach 106049 := rs (se 2 (by rfl) ⟨39768, by rfl⟩) (B 79537 (by norm_num) ⟨39768, by rfl⟩ (by norm_num))
theorem R106105 : Reach 106105 := rs (se 2 (by rfl) ⟨39789, by rfl⟩) (B 79579 (by norm_num) ⟨39789, by rfl⟩ (by norm_num))
theorem R106201 : Reach 106201 := rs (se 2 (by rfl) ⟨39825, by rfl⟩) (B 79651 (by norm_num) ⟨39825, by rfl⟩ (by norm_num))
theorem R106373 : Reach 106373 := rs (se 4 (by rfl) ⟨9972, by rfl⟩) (B 19945 (by norm_num) ⟨9972, by rfl⟩ (by norm_num))
theorem R106429 : Reach 106429 := rs (se 3 (by rfl) ⟨19955, by rfl⟩) (B 39911 (by norm_num) ⟨19955, by rfl⟩ (by norm_num))
theorem R106525 : Reach 106525 := rs (se 3 (by rfl) ⟨19973, by rfl⟩) (B 39947 (by norm_num) ⟨19973, by rfl⟩ (by norm_num))
theorem R106697 : Reach 106697 := rs (se 2 (by rfl) ⟨40011, by rfl⟩) (B 80023 (by norm_num) ⟨40011, by rfl⟩ (by norm_num))
theorem R2367701 : Reach 2367701 := rs (se 7 (by rfl) ⟨27746, by rfl⟩) (B 55493 (by norm_num) ⟨27746, by rfl⟩ (by norm_num))
theorem R106717 : Reach 106717 := rs (se 3 (by rfl) ⟨20009, by rfl⟩) (B 40019 (by norm_num) ⟨20009, by rfl⟩ (by norm_num))
theorem R106753 : Reach 106753 := rs (se 2 (by rfl) ⟨40032, by rfl⟩) (B 80065 (by norm_num) ⟨40032, by rfl⟩ (by norm_num))
theorem R106849 : Reach 106849 := rs (se 2 (by rfl) ⟨40068, by rfl⟩) (B 80137 (by norm_num) ⟨40068, by rfl⟩ (by norm_num))
theorem R827765 : Reach 827765 := rs (se 5 (by rfl) ⟨38801, by rfl⟩) (B 77603 (by norm_num) ⟨38801, by rfl⟩ (by norm_num))
theorem R237973 : Reach 237973 := rs (se 6 (by rfl) ⟨5577, by rfl⟩) (B 11155 (by norm_num) ⟨5577, by rfl⟩ (by norm_num))
theorem R434645 : Reach 434645 := rs (se 7 (by rfl) ⟨5093, by rfl⟩) (B 10187 (by norm_num) ⟨5093, by rfl⟩ (by norm_num))
theorem R107021 : Reach 107021 := rs (se 3 (by rfl) ⟨20066, by rfl⟩) (B 40133 (by norm_num) ⟨20066, by rfl⟩ (by norm_num))
theorem R238133 : Reach 238133 := rs (se 5 (by rfl) ⟨11162, by rfl⟩) (B 22325 (by norm_num) ⟨11162, by rfl⟩ (by norm_num))
theorem R107077 : Reach 107077 := rs (se 4 (by rfl) ⟨10038, by rfl⟩) (B 20077 (by norm_num) ⟨10038, by rfl⟩ (by norm_num))
theorem R172621 : Reach 172621 := rs (se 3 (by rfl) ⟨32366, by rfl⟩) (B 64733 (by norm_num) ⟨32366, by rfl⟩ (by norm_num))
theorem R107173 : Reach 107173 := rs (se 4 (by rfl) ⟨10047, by rfl⟩) (B 20095 (by norm_num) ⟨10047, by rfl⟩ (by norm_num))
theorem R238373 : Reach 238373 := rs (se 4 (by rfl) ⟨22347, by rfl⟩) (B 44695 (by norm_num) ⟨22347, by rfl⟩ (by norm_num))
theorem R303925 : Reach 303925 := rs (se 5 (by rfl) ⟨14246, by rfl⟩) (B 28493 (by norm_num) ⟨14246, by rfl⟩ (by norm_num))
theorem R107345 : Reach 107345 := rs (se 2 (by rfl) ⟨40254, by rfl⟩) (B 80509 (by norm_num) ⟨40254, by rfl⟩ (by norm_num))
theorem R107401 : Reach 107401 := rs (se 2 (by rfl) ⟨40275, by rfl⟩) (B 80551 (by norm_num) ⟨40275, by rfl⟩ (by norm_num))
theorem R238565 : Reach 238565 := rs (se 4 (by rfl) ⟨22365, by rfl⟩) (B 44731 (by norm_num) ⟨22365, by rfl⟩ (by norm_num))
theorem R107497 : Reach 107497 := rs (se 2 (by rfl) ⟨40311, by rfl⟩) (B 80623 (by norm_num) ⟨40311, by rfl⟩ (by norm_num))
theorem R173045 : Reach 173045 := rs (se 5 (by rfl) ⟨8111, by rfl⟩) (B 16223 (by norm_num) ⟨8111, by rfl⟩ (by norm_num))
theorem R140285 : Reach 140285 := rs (se 3 (by rfl) ⟨26303, by rfl⟩) (B 52607 (by norm_num) ⟨26303, by rfl⟩ (by norm_num))
theorem R926741 : Reach 926741 := rs (se 6 (by rfl) ⟨21720, by rfl⟩) (B 43441 (by norm_num) ⟨21720, by rfl⟩ (by norm_num))
theorem R140413 : Reach 140413 := rs (se 3 (by rfl) ⟨26327, by rfl⟩) (B 52655 (by norm_num) ⟨26327, by rfl⟩ (by norm_num))
theorem R107669 : Reach 107669 := rs (se 6 (by rfl) ⟨2523, by rfl⟩) (B 5047 (by norm_num) ⟨2523, by rfl⟩ (by norm_num))
theorem R107725 : Reach 107725 := rs (se 3 (by rfl) ⟨20198, by rfl⟩) (B 40397 (by norm_num) ⟨20198, by rfl⟩ (by norm_num))
theorem R140501 : Reach 140501 := rs (se 7 (by rfl) ⟨1646, by rfl⟩) (B 3293 (by norm_num) ⟨1646, by rfl⟩ (by norm_num))
theorem R533749 : Reach 533749 := rs (se 5 (by rfl) ⟨25019, by rfl⟩) (B 50039 (by norm_num) ⟨25019, by rfl⟩ (by norm_num))
theorem R402677 : Reach 402677 := rs (se 5 (by rfl) ⟨18875, by rfl⟩) (B 37751 (by norm_num) ⟨18875, by rfl⟩ (by norm_num))
theorem R107821 : Reach 107821 := rs (se 3 (by rfl) ⟨20216, by rfl⟩) (B 40433 (by norm_num) ⟨20216, by rfl⟩ (by norm_num))
theorem R140629 : Reach 140629 := rs (se 12 (by rfl) ⟨51, by rfl⟩) (B 103 (by norm_num) ⟨51, by rfl⟩ (by norm_num))
theorem R140717 : Reach 140717 := rs (se 3 (by rfl) ⟨26384, by rfl⟩) (B 52769 (by norm_num) ⟨26384, by rfl⟩ (by norm_num))
theorem R107993 : Reach 107993 := rs (se 2 (by rfl) ⟨40497, by rfl⟩) (B 80995 (by norm_num) ⟨40497, by rfl⟩ (by norm_num))
theorem R173573 : Reach 173573 := rs (se 4 (by rfl) ⟨16272, by rfl⟩) (B 32545 (by norm_num) ⟨16272, by rfl⟩ (by norm_num))
theorem R108049 : Reach 108049 := rs (se 2 (by rfl) ⟨40518, by rfl⟩) (B 81037 (by norm_num) ⟨40518, by rfl⟩ (by norm_num))
theorem R140845 : Reach 140845 := rs (se 3 (by rfl) ⟨26408, by rfl⟩) (B 52817 (by norm_num) ⟨26408, by rfl⟩ (by norm_num))
theorem R108145 : Reach 108145 := rs (se 2 (by rfl) ⟨40554, by rfl⟩) (B 81109 (by norm_num) ⟨40554, by rfl⟩ (by norm_num))
theorem R140933 : Reach 140933 := rs (se 4 (by rfl) ⟨13212, by rfl⟩) (B 26425 (by norm_num) ⟨13212, by rfl⟩ (by norm_num))
theorem R108253 : Reach 108253 := rs (se 3 (by rfl) ⟨20297, by rfl⟩) (B 40595 (by norm_num) ⟨20297, by rfl⟩ (by norm_num))
theorem R435941 : Reach 435941 := rs (se 4 (by rfl) ⟨40869, by rfl⟩) (B 81739 (by norm_num) ⟨40869, by rfl⟩ (by norm_num))
theorem R141061 : Reach 141061 := rs (se 4 (by rfl) ⟨13224, by rfl⟩) (B 26449 (by norm_num) ⟨13224, by rfl⟩ (by norm_num))
theorem R108317 : Reach 108317 := rs (se 3 (by rfl) ⟨20309, by rfl⟩) (B 40619 (by norm_num) ⟨20309, by rfl⟩ (by norm_num))
theorem R304933 : Reach 304933 := rs (se 4 (by rfl) ⟨28587, by rfl⟩) (B 57175 (by norm_num) ⟨28587, by rfl⟩ (by norm_num))
theorem R108373 : Reach 108373 := rs (se 9 (by rfl) ⟨317, by rfl⟩) (B 635 (by norm_num) ⟨317, by rfl⟩ (by norm_num))
theorem R141149 : Reach 141149 := rs (se 3 (by rfl) ⟨26465, by rfl⟩) (B 52931 (by norm_num) ⟨26465, by rfl⟩ (by norm_num))
theorem R108445 : Reach 108445 := rs (se 3 (by rfl) ⟨20333, by rfl⟩) (B 40667 (by norm_num) ⟨20333, by rfl⟩ (by norm_num))
theorem R206749 : Reach 206749 := rs (se 3 (by rfl) ⟨38765, by rfl⟩) (B 77531 (by norm_num) ⟨38765, by rfl⟩ (by norm_num))
theorem R141221 : Reach 141221 := rs (se 4 (by rfl) ⟨13239, by rfl⟩) (B 26479 (by norm_num) ⟨13239, by rfl⟩ (by norm_num))
theorem R108469 : Reach 108469 := rs (se 5 (by rfl) ⟨5084, by rfl⟩) (B 10169 (by norm_num) ⟨5084, by rfl⟩ (by norm_num))
theorem R239557 : Reach 239557 := rs (se 4 (by rfl) ⟨22458, by rfl⟩) (B 44917 (by norm_num) ⟨22458, by rfl⟩ (by norm_num))
theorem R337861 : Reach 337861 := rs (se 4 (by rfl) ⟨31674, by rfl⟩) (B 63349 (by norm_num) ⟨31674, by rfl⟩ (by norm_num))
theorem R141277 : Reach 141277 := rs (se 3 (by rfl) ⟨26489, by rfl⟩) (B 52979 (by norm_num) ⟨26489, by rfl⟩ (by norm_num))
theorem R141365 : Reach 141365 := rs (se 5 (by rfl) ⟨6626, by rfl⟩) (B 13253 (by norm_num) ⟨6626, by rfl⟩ (by norm_num))
theorem R108641 : Reach 108641 := rs (se 2 (by rfl) ⟨40740, by rfl⟩) (B 81481 (by norm_num) ⟨40740, by rfl⟩ (by norm_num))
theorem R108697 : Reach 108697 := rs (se 2 (by rfl) ⟨40761, by rfl⟩) (B 81523 (by norm_num) ⟨40761, by rfl⟩ (by norm_num))
theorem R141493 : Reach 141493 := rs (se 5 (by rfl) ⟨6632, by rfl⟩) (B 13265 (by norm_num) ⟨6632, by rfl⟩ (by norm_num))
theorem R108793 : Reach 108793 := rs (se 2 (by rfl) ⟨40797, by rfl⟩) (B 81595 (by norm_num) ⟨40797, by rfl⟩ (by norm_num))
theorem R141581 : Reach 141581 := rs (se 3 (by rfl) ⟨26546, by rfl⟩) (B 53093 (by norm_num) ⟨26546, by rfl⟩ (by norm_num))
theorem R207173 : Reach 207173 := rs (se 4 (by rfl) ⟨19422, by rfl⟩) (B 38845 (by norm_num) ⟨19422, by rfl⟩ (by norm_num))
theorem R141709 : Reach 141709 := rs (se 3 (by rfl) ⟨26570, by rfl⟩) (B 53141 (by norm_num) ⟨26570, by rfl⟩ (by norm_num))
theorem R108965 : Reach 108965 := rs (se 4 (by rfl) ⟨10215, by rfl⟩) (B 20431 (by norm_num) ⟨10215, by rfl⟩ (by norm_num))
theorem R272821 : Reach 272821 := rs (se 5 (by rfl) ⟨12788, by rfl⟩) (B 25577 (by norm_num) ⟨12788, by rfl⟩ (by norm_num))
theorem R109021 : Reach 109021 := rs (se 3 (by rfl) ⟨20441, by rfl⟩) (B 40883 (by norm_num) ⟨20441, by rfl⟩ (by norm_num))
theorem R141797 : Reach 141797 := rs (se 4 (by rfl) ⟨13293, by rfl⟩) (B 26587 (by norm_num) ⟨13293, by rfl⟩ (by norm_num))
theorem R109117 : Reach 109117 := rs (se 3 (by rfl) ⟨20459, by rfl⟩) (B 40919 (by norm_num) ⟨20459, by rfl⟩ (by norm_num))
theorem R141925 : Reach 141925 := rs (se 4 (by rfl) ⟨13305, by rfl⟩) (B 26611 (by norm_num) ⟨13305, by rfl⟩ (by norm_num))
theorem R207461 : Reach 207461 := rs (se 4 (by rfl) ⟨19449, by rfl⟩) (B 38899 (by norm_num) ⟨19449, by rfl⟩ (by norm_num))
theorem R404117 : Reach 404117 := rs (se 6 (by rfl) ⟨9471, by rfl⟩) (B 18943 (by norm_num) ⟨9471, by rfl⟩ (by norm_num))
theorem R142013 : Reach 142013 := rs (se 3 (by rfl) ⟨26627, by rfl⟩) (B 53255 (by norm_num) ⟨26627, by rfl⟩ (by norm_num))
theorem R109289 : Reach 109289 := rs (se 2 (by rfl) ⟨40983, by rfl⟩) (B 81967 (by norm_num) ⟨40983, by rfl⟩ (by norm_num))
theorem R109345 : Reach 109345 := rs (se 2 (by rfl) ⟨41004, by rfl⟩) (B 82009 (by norm_num) ⟨41004, by rfl⟩ (by norm_num))
theorem R142141 : Reach 142141 := rs (se 3 (by rfl) ⟨26651, by rfl⟩) (B 53303 (by norm_num) ⟨26651, by rfl⟩ (by norm_num))
theorem R109441 : Reach 109441 := rs (se 2 (by rfl) ⟨41040, by rfl⟩) (B 82081 (by norm_num) ⟨41040, by rfl⟩ (by norm_num))
theorem R142229 : Reach 142229 := rs (se 6 (by rfl) ⟨3333, by rfl⟩) (B 6667 (by norm_num) ⟨3333, by rfl⟩ (by norm_num))
theorem R437237 : Reach 437237 := rs (se 5 (by rfl) ⟨20495, by rfl⟩) (B 40991 (by norm_num) ⟨20495, by rfl⟩ (by norm_num))
theorem R142357 : Reach 142357 := rs (se 6 (by rfl) ⟨3336, by rfl⟩) (B 6673 (by norm_num) ⟨3336, by rfl⟩ (by norm_num))
theorem R240661 : Reach 240661 := rs (se 6 (by rfl) ⟨5640, by rfl⟩) (B 11281 (by norm_num) ⟨5640, by rfl⟩ (by norm_num))
theorem R109613 : Reach 109613 := rs (se 3 (by rfl) ⟨20552, by rfl⟩) (B 41105 (by norm_num) ⟨20552, by rfl⟩ (by norm_num))
theorem R339029 : Reach 339029 := rs (se 8 (by rfl) ⟨1986, by rfl⟩) (B 3973 (by norm_num) ⟨1986, by rfl⟩ (by norm_num))
theorem R109669 : Reach 109669 := rs (se 4 (by rfl) ⟨10281, by rfl⟩) (B 20563 (by norm_num) ⟨10281, by rfl⟩ (by norm_num))
theorem R142445 : Reach 142445 := rs (se 3 (by rfl) ⟨26708, by rfl⟩) (B 53417 (by norm_num) ⟨26708, by rfl⟩ (by norm_num))
theorem R208013 : Reach 208013 := rs (se 3 (by rfl) ⟨39002, by rfl⟩) (B 78005 (by norm_num) ⟨39002, by rfl⟩ (by norm_num))
theorem R109765 : Reach 109765 := rs (se 4 (by rfl) ⟨10290, by rfl⟩) (B 20581 (by norm_num) ⟨10290, by rfl⟩ (by norm_num))
theorem R142573 : Reach 142573 := rs (se 3 (by rfl) ⟨26732, by rfl⟩) (B 53465 (by norm_num) ⟨26732, by rfl⟩ (by norm_num))
theorem R142661 : Reach 142661 := rs (se 4 (by rfl) ⟨13374, by rfl⟩) (B 26749 (by norm_num) ⟨13374, by rfl⟩ (by norm_num))
theorem R109937 : Reach 109937 := rs (se 2 (by rfl) ⟨41226, by rfl⟩) (B 82453 (by norm_num) ⟨41226, by rfl⟩ (by norm_num))
theorem R634229 : Reach 634229 := rs (se 5 (by rfl) ⟨29729, by rfl⟩) (B 59459 (by norm_num) ⟨29729, by rfl⟩ (by norm_num))
theorem R109993 : Reach 109993 := rs (se 2 (by rfl) ⟨41247, by rfl⟩) (B 82495 (by norm_num) ⟨41247, by rfl⟩ (by norm_num))
theorem R142789 : Reach 142789 := rs (se 4 (by rfl) ⟨13386, by rfl⟩) (B 26773 (by norm_num) ⟨13386, by rfl⟩ (by norm_num))
theorem R110089 : Reach 110089 := rs (se 2 (by rfl) ⟨41283, by rfl⟩) (B 82567 (by norm_num) ⟨41283, by rfl⟩ (by norm_num))
theorem R142877 : Reach 142877 := rs (se 3 (by rfl) ⟨26789, by rfl⟩) (B 53579 (by norm_num) ⟨26789, by rfl⟩ (by norm_num))
theorem R142933 : Reach 142933 := rs (se 8 (by rfl) ⟨837, by rfl⟩) (B 1675 (by norm_num) ⟨837, by rfl⟩ (by norm_num))
theorem R143005 : Reach 143005 := rs (se 3 (by rfl) ⟨26813, by rfl⟩) (B 53627 (by norm_num) ⟨26813, by rfl⟩ (by norm_num))
theorem R110261 : Reach 110261 := rs (se 5 (by rfl) ⟨5168, by rfl⟩) (B 10337 (by norm_num) ⟨5168, by rfl⟩ (by norm_num))
theorem R110269 : Reach 110269 := rs (se 3 (by rfl) ⟨20675, by rfl⟩) (B 41351 (by norm_num) ⟨20675, by rfl⟩ (by norm_num))
theorem R143093 : Reach 143093 := rs (se 5 (by rfl) ⟨6707, by rfl⟩) (B 13415 (by norm_num) ⟨6707, by rfl⟩ (by norm_num))
theorem R143221 : Reach 143221 := rs (se 5 (by rfl) ⟨6713, by rfl⟩) (B 13427 (by norm_num) ⟨6713, by rfl⟩ (by norm_num))
theorem R143309 : Reach 143309 := rs (se 3 (by rfl) ⟨26870, by rfl⟩) (B 53741 (by norm_num) ⟨26870, by rfl⟩ (by norm_num))
theorem R143317 : Reach 143317 := rs (se 7 (by rfl) ⟨1679, by rfl⟩) (B 3359 (by norm_num) ⟨1679, by rfl⟩ (by norm_num))
theorem R143437 : Reach 143437 := rs (se 3 (by rfl) ⟨26894, by rfl⟩) (B 53789 (by norm_num) ⟨26894, by rfl⟩ (by norm_num))
theorem R143525 : Reach 143525 := rs (se 4 (by rfl) ⟨13455, by rfl⟩) (B 26911 (by norm_num) ⟨13455, by rfl⟩ (by norm_num))
theorem R438533 : Reach 438533 := rs (se 4 (by rfl) ⟨41112, by rfl⟩) (B 82225 (by norm_num) ⟨41112, by rfl⟩ (by norm_num))
theorem R143653 : Reach 143653 := rs (se 4 (by rfl) ⟨13467, by rfl⟩) (B 26935 (by norm_num) ⟨13467, by rfl⟩ (by norm_num))
theorem R143741 : Reach 143741 := rs (se 3 (by rfl) ⟨26951, by rfl⟩) (B 53903 (by norm_num) ⟨26951, by rfl⟩ (by norm_num))
theorem R766421 : Reach 766421 := rs (se 7 (by rfl) ⟨8981, by rfl⟩) (B 17963 (by norm_num) ⟨8981, by rfl⟩ (by norm_num))
theorem R242165 : Reach 242165 := rs (se 5 (by rfl) ⟨11351, by rfl⟩) (B 22703 (by norm_num) ⟨11351, by rfl⟩ (by norm_num))
theorem R143869 : Reach 143869 := rs (se 3 (by rfl) ⟨26975, by rfl⟩) (B 53951 (by norm_num) ⟨26975, by rfl⟩ (by norm_num))
theorem R143957 : Reach 143957 := rs (se 8 (by rfl) ⟨843, by rfl⟩) (B 1687 (by norm_num) ⟨843, by rfl⟩ (by norm_num))
theorem R144085 : Reach 144085 := rs (se 7 (by rfl) ⟨1688, by rfl⟩) (B 3377 (by norm_num) ⟨1688, by rfl⟩ (by norm_num))
theorem R144173 : Reach 144173 := rs (se 3 (by rfl) ⟨27032, by rfl⟩) (B 54065 (by norm_num) ⟨27032, by rfl⟩ (by norm_num))
theorem R144301 : Reach 144301 := rs (se 3 (by rfl) ⟨27056, by rfl⟩) (B 54113 (by norm_num) ⟨27056, by rfl⟩ (by norm_num))
theorem R144389 : Reach 144389 := rs (se 4 (by rfl) ⟨13536, by rfl⟩) (B 27073 (by norm_num) ⟨13536, by rfl⟩ (by norm_num))
theorem R144517 : Reach 144517 := rs (se 4 (by rfl) ⟨13548, by rfl⟩) (B 27097 (by norm_num) ⟨13548, by rfl⟩ (by norm_num))
theorem R275653 : Reach 275653 := rs (se 4 (by rfl) ⟨25842, by rfl⟩) (B 51685 (by norm_num) ⟨25842, by rfl⟩ (by norm_num))
theorem R144605 : Reach 144605 := rs (se 3 (by rfl) ⟨27113, by rfl⟩) (B 54227 (by norm_num) ⟨27113, by rfl⟩ (by norm_num))
theorem R275717 : Reach 275717 := rs (se 4 (by rfl) ⟨25848, by rfl⟩) (B 51697 (by norm_num) ⟨25848, by rfl⟩ (by norm_num))
theorem R144733 : Reach 144733 := rs (se 3 (by rfl) ⟨27137, by rfl⟩) (B 54275 (by norm_num) ⟨27137, by rfl⟩ (by norm_num))
theorem R406885 : Reach 406885 := rs (se 4 (by rfl) ⟨38145, by rfl⟩) (B 76291 (by norm_num) ⟨38145, by rfl⟩ (by norm_num))
theorem R177557 : Reach 177557 := rs (se 6 (by rfl) ⟨4161, by rfl⟩) (B 8323 (by norm_num) ⟨4161, by rfl⟩ (by norm_num))
theorem R144821 : Reach 144821 := rs (se 5 (by rfl) ⟨6788, by rfl⟩) (B 13577 (by norm_num) ⟨6788, by rfl⟩ (by norm_num))
theorem R439829 : Reach 439829 := rs (se 6 (by rfl) ⟨10308, by rfl⟩) (B 20617 (by norm_num) ⟨10308, by rfl⟩ (by norm_num))
theorem R144949 : Reach 144949 := rs (se 5 (by rfl) ⟨6794, by rfl⟩) (B 13589 (by norm_num) ⟨6794, by rfl⟩ (by norm_num))
theorem R210509 : Reach 210509 := rs (se 3 (by rfl) ⟨39470, by rfl⟩) (B 78941 (by norm_num) ⟨39470, by rfl⟩ (by norm_num))
theorem R177797 : Reach 177797 := rs (se 4 (by rfl) ⟨16668, by rfl⟩) (B 33337 (by norm_num) ⟨16668, by rfl⟩ (by norm_num))
theorem R145037 : Reach 145037 := rs (se 3 (by rfl) ⟨27194, by rfl⟩) (B 54389 (by norm_num) ⟨27194, by rfl⟩ (by norm_num))
theorem R308933 : Reach 308933 := rs (se 4 (by rfl) ⟨28962, by rfl⟩) (B 57925 (by norm_num) ⟨28962, by rfl⟩ (by norm_num))
theorem R210701 : Reach 210701 := rs (se 3 (by rfl) ⟨39506, by rfl⟩) (B 79013 (by norm_num) ⟨39506, by rfl⟩ (by norm_num))
theorem R145165 : Reach 145165 := rs (se 3 (by rfl) ⟨27218, by rfl⟩) (B 54437 (by norm_num) ⟨27218, by rfl⟩ (by norm_num))
theorem R145253 : Reach 145253 := rs (se 4 (by rfl) ⟨13617, by rfl⟩) (B 27235 (by norm_num) ⟨13617, by rfl⟩ (by norm_num))
theorem R145309 : Reach 145309 := rs (se 3 (by rfl) ⟨27245, by rfl⟩) (B 54491 (by norm_num) ⟨27245, by rfl⟩ (by norm_num))
theorem R145381 : Reach 145381 := rs (se 4 (by rfl) ⟨13629, by rfl⟩) (B 27259 (by norm_num) ⟨13629, by rfl⟩ (by norm_num))
theorem R276517 : Reach 276517 := rs (se 4 (by rfl) ⟨25923, by rfl⟩) (B 51847 (by norm_num) ⟨25923, by rfl⟩ (by norm_num))
theorem R243749 : Reach 243749 := rs (se 4 (by rfl) ⟨22851, by rfl⟩) (B 45703 (by norm_num) ⟨22851, by rfl⟩ (by norm_num))
theorem R145469 : Reach 145469 := rs (se 3 (by rfl) ⟨27275, by rfl⟩) (B 54551 (by norm_num) ⟨27275, by rfl⟩ (by norm_num))
theorem R211045 : Reach 211045 := rs (se 4 (by rfl) ⟨19785, by rfl⟩) (B 39571 (by norm_num) ⟨19785, by rfl⟩ (by norm_num))
theorem R178301 : Reach 178301 := rs (se 3 (by rfl) ⟨33431, by rfl⟩) (B 66863 (by norm_num) ⟨33431, by rfl⟩ (by norm_num))
theorem R178309 : Reach 178309 := rs (se 4 (by rfl) ⟨16716, by rfl⟩) (B 33433 (by norm_num) ⟨16716, by rfl⟩ (by norm_num))
theorem R145597 : Reach 145597 := rs (se 3 (by rfl) ⟨27299, by rfl⟩) (B 54599 (by norm_num) ⟨27299, by rfl⟩ (by norm_num))
theorem R211157 : Reach 211157 := rs (se 7 (by rfl) ⟨2474, by rfl⟩) (B 4949 (by norm_num) ⟨2474, by rfl⟩ (by norm_num))
theorem R145685 : Reach 145685 := rs (se 6 (by rfl) ⟨3414, by rfl⟩) (B 6829 (by norm_num) ⟨3414, by rfl⟩ (by norm_num))
theorem R113005 : Reach 113005 := rs (se 3 (by rfl) ⟨21188, by rfl⟩) (B 42377 (by norm_num) ⟨21188, by rfl⟩ (by norm_num))
theorem R211349 : Reach 211349 := rs (se 6 (by rfl) ⟨4953, by rfl⟩) (B 9907 (by norm_num) ⟨4953, by rfl⟩ (by norm_num))
theorem R145813 : Reach 145813 := rs (se 6 (by rfl) ⟨3417, by rfl⟩) (B 6835 (by norm_num) ⟨3417, by rfl⟩ (by norm_num))
theorem R145901 : Reach 145901 := rs (se 3 (by rfl) ⟨27356, by rfl⟩) (B 54713 (by norm_num) ⟨27356, by rfl⟩ (by norm_num))
theorem R146029 : Reach 146029 := rs (se 3 (by rfl) ⟨27380, by rfl⟩) (B 54761 (by norm_num) ⟨27380, by rfl⟩ (by norm_num))
theorem R735925 : Reach 735925 := rs (se 5 (by rfl) ⟨34496, by rfl⟩) (B 68993 (by norm_num) ⟨34496, by rfl⟩ (by norm_num))
theorem R244421 : Reach 244421 := rs (se 4 (by rfl) ⟨22914, by rfl⟩) (B 45829 (by norm_num) ⟨22914, by rfl⟩ (by norm_num))
theorem R146117 : Reach 146117 := rs (se 4 (by rfl) ⟨13698, by rfl⟩) (B 27397 (by norm_num) ⟨13698, by rfl⟩ (by norm_num))
theorem R211693 : Reach 211693 := rs (se 3 (by rfl) ⟨39692, by rfl⟩) (B 79385 (by norm_num) ⟨39692, by rfl⟩ (by norm_num))
theorem R146245 : Reach 146245 := rs (se 4 (by rfl) ⟨13710, by rfl⟩) (B 27421 (by norm_num) ⟨13710, by rfl⟩ (by norm_num))
theorem R211805 : Reach 211805 := rs (se 3 (by rfl) ⟨39713, by rfl⟩) (B 79427 (by norm_num) ⟨39713, by rfl⟩ (by norm_num))
theorem R146333 : Reach 146333 := rs (se 3 (by rfl) ⟨27437, by rfl⟩) (B 54875 (by norm_num) ⟨27437, by rfl⟩ (by norm_num))
theorem R211997 : Reach 211997 := rs (se 3 (by rfl) ⟨39749, by rfl⟩) (B 79499 (by norm_num) ⟨39749, by rfl⟩ (by norm_num))
theorem R146461 : Reach 146461 := rs (se 3 (by rfl) ⟨27461, by rfl⟩) (B 54923 (by norm_num) ⟨27461, by rfl⟩ (by norm_num))
theorem R244853 : Reach 244853 := rs (se 5 (by rfl) ⟨11477, by rfl⟩) (B 22955 (by norm_num) ⟨11477, by rfl⟩ (by norm_num))
theorem R146549 : Reach 146549 := rs (se 5 (by rfl) ⟨6869, by rfl⟩) (B 13739 (by norm_num) ⟨6869, by rfl⟩ (by norm_num))
theorem R179437 : Reach 179437 := rs (se 3 (by rfl) ⟨33644, by rfl⟩) (B 67289 (by norm_num) ⟨33644, by rfl⟩ (by norm_num))
theorem R146677 : Reach 146677 := rs (se 5 (by rfl) ⟨6875, by rfl⟩) (B 13751 (by norm_num) ⟨6875, by rfl⟩ (by norm_num))
theorem R146765 : Reach 146765 := rs (se 3 (by rfl) ⟨27518, by rfl⟩) (B 55037 (by norm_num) ⟨27518, by rfl⟩ (by norm_num))
theorem R212341 : Reach 212341 := rs (se 5 (by rfl) ⟨9953, by rfl⟩) (B 19907 (by norm_num) ⟨9953, by rfl⟩ (by norm_num))
theorem R540053 : Reach 540053 := rs (se 6 (by rfl) ⟨12657, by rfl⟩) (B 25315 (by norm_num) ⟨12657, by rfl⟩ (by norm_num))
theorem R146893 : Reach 146893 := rs (se 3 (by rfl) ⟨27542, by rfl⟩) (B 55085 (by norm_num) ⟨27542, by rfl⟩ (by norm_num))
theorem R212453 : Reach 212453 := rs (se 4 (by rfl) ⟨19917, by rfl⟩) (B 39835 (by norm_num) ⟨19917, by rfl⟩ (by norm_num))
theorem R605717 : Reach 605717 := rs (se 6 (by rfl) ⟨14196, by rfl⟩) (B 28393 (by norm_num) ⟨14196, by rfl⟩ (by norm_num))
theorem R146981 : Reach 146981 := rs (se 4 (by rfl) ⟨13779, by rfl⟩) (B 27559 (by norm_num) ⟨13779, by rfl⟩ (by norm_num))
theorem R179813 : Reach 179813 := rs (se 4 (by rfl) ⟨16857, by rfl⟩) (B 33715 (by norm_num) ⟨16857, by rfl⟩ (by norm_num))
theorem R212645 : Reach 212645 := rs (se 4 (by rfl) ⟨19935, by rfl⟩) (B 39871 (by norm_num) ⟨19935, by rfl⟩ (by norm_num))
theorem R245413 : Reach 245413 := rs (se 4 (by rfl) ⟨23007, by rfl⟩) (B 46015 (by norm_num) ⟨23007, by rfl⟩ (by norm_num))
theorem R606005 : Reach 606005 := rs (se 5 (by rfl) ⟨28406, by rfl⟩) (B 56813 (by norm_num) ⟨28406, by rfl⟩ (by norm_num))
theorem R245605 : Reach 245605 := rs (se 4 (by rfl) ⟨23025, by rfl⟩) (B 46051 (by norm_num) ⟨23025, by rfl⟩ (by norm_num))
theorem R212989 : Reach 212989 := rs (se 3 (by rfl) ⟨39935, by rfl⟩) (B 79871 (by norm_num) ⟨39935, by rfl⟩ (by norm_num))
theorem R409637 : Reach 409637 := rs (se 4 (by rfl) ⟨38403, by rfl⟩) (B 76807 (by norm_num) ⟨38403, by rfl⟩ (by norm_num))
theorem R213101 : Reach 213101 := rs (se 3 (by rfl) ⟨39956, by rfl⟩) (B 79913 (by norm_num) ⟨39956, by rfl⟩ (by norm_num))
theorem R147565 : Reach 147565 := rs (se 3 (by rfl) ⟨27668, by rfl⟩) (B 55337 (by norm_num) ⟨27668, by rfl⟩ (by norm_num))
theorem R278741 : Reach 278741 := rs (se 7 (by rfl) ⟨3266, by rfl⟩) (B 6533 (by norm_num) ⟨3266, by rfl⟩ (by norm_num))
theorem R213293 : Reach 213293 := rs (se 3 (by rfl) ⟨39992, by rfl⟩) (B 79985 (by norm_num) ⟨39992, by rfl⟩ (by norm_num))
theorem R115021 : Reach 115021 := rs (se 3 (by rfl) ⟨21566, by rfl⟩) (B 43133 (by norm_num) ⟨21566, by rfl⟩ (by norm_num))
theorem R737909 : Reach 737909 := rs (se 5 (by rfl) ⟨34589, by rfl⟩) (B 69179 (by norm_num) ⟨34589, by rfl⟩ (by norm_num))
theorem R213637 : Reach 213637 := rs (se 4 (by rfl) ⟨20028, by rfl⟩) (B 40057 (by norm_num) ⟨20028, by rfl⟩ (by norm_num))
theorem R311957 : Reach 311957 := rs (se 6 (by rfl) ⟨7311, by rfl⟩) (B 14623 (by norm_num) ⟨7311, by rfl⟩ (by norm_num))
theorem R705205 : Reach 705205 := rs (se 5 (by rfl) ⟨33056, by rfl⟩) (B 66113 (by norm_num) ⟨33056, by rfl⟩ (by norm_num))
theorem R541397 : Reach 541397 := rs (se 7 (by rfl) ⟨6344, by rfl⟩) (B 12689 (by norm_num) ⟨6344, by rfl⟩ (by norm_num))
theorem R213749 : Reach 213749 := rs (se 5 (by rfl) ⟨10019, by rfl⟩) (B 20039 (by norm_num) ⟨10019, by rfl⟩ (by norm_num))
theorem R148277 : Reach 148277 := rs (se 5 (by rfl) ⟨6950, by rfl⟩) (B 13901 (by norm_num) ⟨6950, by rfl⟩ (by norm_num))
theorem R213941 : Reach 213941 := rs (se 5 (by rfl) ⟨10028, by rfl⟩) (B 20057 (by norm_num) ⟨10028, by rfl⟩ (by norm_num))
theorem R574517 : Reach 574517 := rs (se 5 (by rfl) ⟨26930, by rfl⟩) (B 53861 (by norm_num) ⟨26930, by rfl⟩ (by norm_num))
theorem R83129 : Reach 83129 := rs (se 2 (by rfl) ⟨31173, by rfl⟩) (B 62347 (by norm_num) ⟨31173, by rfl⟩ (by norm_num))
theorem R83133 : Reach 83133 := rs (se 3 (by rfl) ⟨15587, by rfl⟩) (B 31175 (by norm_num) ⟨15587, by rfl⟩ (by norm_num))
theorem R83137 : Reach 83137 := rs (se 2 (by rfl) ⟨31176, by rfl⟩) (B 62353 (by norm_num) ⟨31176, by rfl⟩ (by norm_num))
theorem R83141 : Reach 83141 := rs (se 4 (by rfl) ⟨7794, by rfl⟩) (B 15589 (by norm_num) ⟨7794, by rfl⟩ (by norm_num))
theorem R83145 : Reach 83145 := rs (se 2 (by rfl) ⟨31179, by rfl⟩) (B 62359 (by norm_num) ⟨31179, by rfl⟩ (by norm_num))
theorem R83149 : Reach 83149 := rs (se 3 (by rfl) ⟨15590, by rfl⟩) (B 31181 (by norm_num) ⟨15590, by rfl⟩ (by norm_num))
theorem R181453 : Reach 181453 := rs (se 3 (by rfl) ⟨34022, by rfl⟩) (B 68045 (by norm_num) ⟨34022, by rfl⟩ (by norm_num))
theorem R83153 : Reach 83153 := rs (se 2 (by rfl) ⟨31182, by rfl⟩) (B 62365 (by norm_num) ⟨31182, by rfl⟩ (by norm_num))
theorem R83157 : Reach 83157 := rs (se 7 (by rfl) ⟨974, by rfl⟩) (B 1949 (by norm_num) ⟨974, by rfl⟩ (by norm_num))
theorem R83161 : Reach 83161 := rs (se 2 (by rfl) ⟨31185, by rfl⟩) (B 62371 (by norm_num) ⟨31185, by rfl⟩ (by norm_num))
theorem R83165 : Reach 83165 := rs (se 3 (by rfl) ⟨15593, by rfl⟩) (B 31187 (by norm_num) ⟨15593, by rfl⟩ (by norm_num))
theorem R83169 : Reach 83169 := rs (se 2 (by rfl) ⟨31188, by rfl⟩) (B 62377 (by norm_num) ⟨31188, by rfl⟩ (by norm_num))
theorem R83173 : Reach 83173 := rs (se 4 (by rfl) ⟨7797, by rfl⟩) (B 15595 (by norm_num) ⟨7797, by rfl⟩ (by norm_num))
theorem R83177 : Reach 83177 := rs (se 2 (by rfl) ⟨31191, by rfl⟩) (B 62383 (by norm_num) ⟨31191, by rfl⟩ (by norm_num))
theorem R83181 : Reach 83181 := rs (se 3 (by rfl) ⟨15596, by rfl⟩) (B 31193 (by norm_num) ⟨15596, by rfl⟩ (by norm_num))
theorem R83185 : Reach 83185 := rs (se 2 (by rfl) ⟨31194, by rfl⟩) (B 62389 (by norm_num) ⟨31194, by rfl⟩ (by norm_num))
theorem R83189 : Reach 83189 := rs (se 5 (by rfl) ⟨3899, by rfl⟩) (B 7799 (by norm_num) ⟨3899, by rfl⟩ (by norm_num))
theorem R83193 : Reach 83193 := rs (se 2 (by rfl) ⟨31197, by rfl⟩) (B 62395 (by norm_num) ⟨31197, by rfl⟩ (by norm_num))
theorem R83197 : Reach 83197 := rs (se 3 (by rfl) ⟨15599, by rfl⟩) (B 31199 (by norm_num) ⟨15599, by rfl⟩ (by norm_num))
theorem R83201 : Reach 83201 := rs (se 2 (by rfl) ⟨31200, by rfl⟩) (B 62401 (by norm_num) ⟨31200, by rfl⟩ (by norm_num))
theorem R83205 : Reach 83205 := rs (se 4 (by rfl) ⟨7800, by rfl⟩) (B 15601 (by norm_num) ⟨7800, by rfl⟩ (by norm_num))
theorem R83209 : Reach 83209 := rs (se 2 (by rfl) ⟨31203, by rfl⟩) (B 62407 (by norm_num) ⟨31203, by rfl⟩ (by norm_num))
theorem R83213 : Reach 83213 := rs (se 3 (by rfl) ⟨15602, by rfl⟩) (B 31205 (by norm_num) ⟨15602, by rfl⟩ (by norm_num))
theorem R214285 : Reach 214285 := rs (se 3 (by rfl) ⟨40178, by rfl⟩) (B 80357 (by norm_num) ⟨40178, by rfl⟩ (by norm_num))
theorem R83217 : Reach 83217 := rs (se 2 (by rfl) ⟨31206, by rfl⟩) (B 62413 (by norm_num) ⟨31206, by rfl⟩ (by norm_num))
theorem R83221 : Reach 83221 := rs (se 6 (by rfl) ⟨1950, by rfl⟩) (B 3901 (by norm_num) ⟨1950, by rfl⟩ (by norm_num))
theorem R83225 : Reach 83225 := rs (se 2 (by rfl) ⟨31209, by rfl⟩) (B 62419 (by norm_num) ⟨31209, by rfl⟩ (by norm_num))
theorem R83229 : Reach 83229 := rs (se 3 (by rfl) ⟨15605, by rfl⟩) (B 31211 (by norm_num) ⟨15605, by rfl⟩ (by norm_num))
theorem R83233 : Reach 83233 := rs (se 2 (by rfl) ⟨31212, by rfl⟩) (B 62425 (by norm_num) ⟨31212, by rfl⟩ (by norm_num))
theorem R83237 : Reach 83237 := rs (se 4 (by rfl) ⟨7803, by rfl⟩) (B 15607 (by norm_num) ⟨7803, by rfl⟩ (by norm_num))
theorem R83241 : Reach 83241 := rs (se 2 (by rfl) ⟨31215, by rfl⟩) (B 62431 (by norm_num) ⟨31215, by rfl⟩ (by norm_num))
theorem R83245 : Reach 83245 := rs (se 3 (by rfl) ⟨15608, by rfl⟩) (B 31217 (by norm_num) ⟨15608, by rfl⟩ (by norm_num))
theorem R83249 : Reach 83249 := rs (se 2 (by rfl) ⟨31218, by rfl⟩) (B 62437 (by norm_num) ⟨31218, by rfl⟩ (by norm_num))
theorem R83253 : Reach 83253 := rs (se 5 (by rfl) ⟨3902, by rfl⟩) (B 7805 (by norm_num) ⟨3902, by rfl⟩ (by norm_num))
theorem R83257 : Reach 83257 := rs (se 2 (by rfl) ⟨31221, by rfl⟩) (B 62443 (by norm_num) ⟨31221, by rfl⟩ (by norm_num))
theorem R83261 : Reach 83261 := rs (se 3 (by rfl) ⟨15611, by rfl⟩) (B 31223 (by norm_num) ⟨15611, by rfl⟩ (by norm_num))
theorem R83265 : Reach 83265 := rs (se 2 (by rfl) ⟨31224, by rfl⟩) (B 62449 (by norm_num) ⟨31224, by rfl⟩ (by norm_num))
theorem R83269 : Reach 83269 := rs (se 4 (by rfl) ⟨7806, by rfl⟩) (B 15613 (by norm_num) ⟨7806, by rfl⟩ (by norm_num))
theorem R83273 : Reach 83273 := rs (se 2 (by rfl) ⟨31227, by rfl⟩) (B 62455 (by norm_num) ⟨31227, by rfl⟩ (by norm_num))
theorem R83277 : Reach 83277 := rs (se 3 (by rfl) ⟨15614, by rfl⟩) (B 31229 (by norm_num) ⟨15614, by rfl⟩ (by norm_num))
theorem R83281 : Reach 83281 := rs (se 2 (by rfl) ⟨31230, by rfl⟩) (B 62461 (by norm_num) ⟨31230, by rfl⟩ (by norm_num))
theorem R83285 : Reach 83285 := rs (se 12 (by rfl) ⟨30, by rfl⟩) (B 61 (by norm_num) ⟨30, by rfl⟩ (by norm_num))
theorem R83289 : Reach 83289 := rs (se 2 (by rfl) ⟨31233, by rfl⟩) (B 62467 (by norm_num) ⟨31233, by rfl⟩ (by norm_num))
theorem R83293 : Reach 83293 := rs (se 3 (by rfl) ⟨15617, by rfl⟩) (B 31235 (by norm_num) ⟨15617, by rfl⟩ (by norm_num))
theorem R83297 : Reach 83297 := rs (se 2 (by rfl) ⟨31236, by rfl⟩) (B 62473 (by norm_num) ⟨31236, by rfl⟩ (by norm_num))
theorem R83301 : Reach 83301 := rs (se 4 (by rfl) ⟨7809, by rfl⟩) (B 15619 (by norm_num) ⟨7809, by rfl⟩ (by norm_num))
theorem R83305 : Reach 83305 := rs (se 2 (by rfl) ⟨31239, by rfl⟩) (B 62479 (by norm_num) ⟨31239, by rfl⟩ (by norm_num))
theorem R83309 : Reach 83309 := rs (se 3 (by rfl) ⟨15620, by rfl⟩) (B 31241 (by norm_num) ⟨15620, by rfl⟩ (by norm_num))
theorem R83313 : Reach 83313 := rs (se 2 (by rfl) ⟨31242, by rfl⟩) (B 62485 (by norm_num) ⟨31242, by rfl⟩ (by norm_num))
theorem R83317 : Reach 83317 := rs (se 5 (by rfl) ⟨3905, by rfl⟩) (B 7811 (by norm_num) ⟨3905, by rfl⟩ (by norm_num))
theorem R83321 : Reach 83321 := rs (se 2 (by rfl) ⟨31245, by rfl⟩) (B 62491 (by norm_num) ⟨31245, by rfl⟩ (by norm_num))
theorem R83325 : Reach 83325 := rs (se 3 (by rfl) ⟨15623, by rfl⟩) (B 31247 (by norm_num) ⟨15623, by rfl⟩ (by norm_num))
theorem R214397 : Reach 214397 := rs (se 3 (by rfl) ⟨40199, by rfl⟩) (B 80399 (by norm_num) ⟨40199, by rfl⟩ (by norm_num))
theorem R83329 : Reach 83329 := rs (se 2 (by rfl) ⟨31248, by rfl⟩) (B 62497 (by norm_num) ⟨31248, by rfl⟩ (by norm_num))
theorem R83333 : Reach 83333 := rs (se 4 (by rfl) ⟨7812, by rfl⟩) (B 15625 (by norm_num) ⟨7812, by rfl⟩ (by norm_num))
theorem R83337 : Reach 83337 := rs (se 2 (by rfl) ⟨31251, by rfl⟩) (B 62503 (by norm_num) ⟨31251, by rfl⟩ (by norm_num))
theorem R83341 : Reach 83341 := rs (se 3 (by rfl) ⟨15626, by rfl⟩) (B 31253 (by norm_num) ⟨15626, by rfl⟩ (by norm_num))
theorem R83345 : Reach 83345 := rs (se 2 (by rfl) ⟨31254, by rfl⟩) (B 62509 (by norm_num) ⟨31254, by rfl⟩ (by norm_num))
theorem R83349 : Reach 83349 := rs (se 6 (by rfl) ⟨1953, by rfl⟩) (B 3907 (by norm_num) ⟨1953, by rfl⟩ (by norm_num))
theorem R83353 : Reach 83353 := rs (se 2 (by rfl) ⟨31257, by rfl⟩) (B 62515 (by norm_num) ⟨31257, by rfl⟩ (by norm_num))
theorem R83357 : Reach 83357 := rs (se 3 (by rfl) ⟨15629, by rfl⟩) (B 31259 (by norm_num) ⟨15629, by rfl⟩ (by norm_num))
theorem R83361 : Reach 83361 := rs (se 2 (by rfl) ⟨31260, by rfl⟩) (B 62521 (by norm_num) ⟨31260, by rfl⟩ (by norm_num))
theorem R83365 : Reach 83365 := rs (se 4 (by rfl) ⟨7815, by rfl⟩) (B 15631 (by norm_num) ⟨7815, by rfl⟩ (by norm_num))
theorem R83369 : Reach 83369 := rs (se 2 (by rfl) ⟨31263, by rfl⟩) (B 62527 (by norm_num) ⟨31263, by rfl⟩ (by norm_num))
theorem R83373 : Reach 83373 := rs (se 3 (by rfl) ⟨15632, by rfl⟩) (B 31265 (by norm_num) ⟨15632, by rfl⟩ (by norm_num))
theorem R83377 : Reach 83377 := rs (se 2 (by rfl) ⟨31266, by rfl⟩) (B 62533 (by norm_num) ⟨31266, by rfl⟩ (by norm_num))
theorem R83381 : Reach 83381 := rs (se 5 (by rfl) ⟨3908, by rfl⟩) (B 7817 (by norm_num) ⟨3908, by rfl⟩ (by norm_num))
theorem R83385 : Reach 83385 := rs (se 2 (by rfl) ⟨31269, by rfl⟩) (B 62539 (by norm_num) ⟨31269, by rfl⟩ (by norm_num))
theorem R83389 : Reach 83389 := rs (se 3 (by rfl) ⟨15635, by rfl⟩) (B 31271 (by norm_num) ⟨15635, by rfl⟩ (by norm_num))
theorem R83393 : Reach 83393 := rs (se 2 (by rfl) ⟨31272, by rfl⟩) (B 62545 (by norm_num) ⟨31272, by rfl⟩ (by norm_num))
theorem R83397 : Reach 83397 := rs (se 4 (by rfl) ⟨7818, by rfl⟩) (B 15637 (by norm_num) ⟨7818, by rfl⟩ (by norm_num))
theorem R83401 : Reach 83401 := rs (se 2 (by rfl) ⟨31275, by rfl⟩) (B 62551 (by norm_num) ⟨31275, by rfl⟩ (by norm_num))
theorem R83405 : Reach 83405 := rs (se 3 (by rfl) ⟨15638, by rfl⟩) (B 31277 (by norm_num) ⟨15638, by rfl⟩ (by norm_num))
theorem R83409 : Reach 83409 := rs (se 2 (by rfl) ⟨31278, by rfl⟩) (B 62557 (by norm_num) ⟨31278, by rfl⟩ (by norm_num))
theorem R83413 : Reach 83413 := rs (se 7 (by rfl) ⟨977, by rfl⟩) (B 1955 (by norm_num) ⟨977, by rfl⟩ (by norm_num))
theorem R83417 : Reach 83417 := rs (se 2 (by rfl) ⟨31281, by rfl⟩) (B 62563 (by norm_num) ⟨31281, by rfl⟩ (by norm_num))
theorem R83421 : Reach 83421 := rs (se 3 (by rfl) ⟨15641, by rfl⟩) (B 31283 (by norm_num) ⟨15641, by rfl⟩ (by norm_num))
theorem R83425 : Reach 83425 := rs (se 2 (by rfl) ⟨31284, by rfl⟩) (B 62569 (by norm_num) ⟨31284, by rfl⟩ (by norm_num))
theorem R83429 : Reach 83429 := rs (se 4 (by rfl) ⟨7821, by rfl⟩) (B 15643 (by norm_num) ⟨7821, by rfl⟩ (by norm_num))
theorem R83433 : Reach 83433 := rs (se 2 (by rfl) ⟨31287, by rfl⟩) (B 62575 (by norm_num) ⟨31287, by rfl⟩ (by norm_num))
theorem R83437 : Reach 83437 := rs (se 3 (by rfl) ⟨15644, by rfl⟩) (B 31289 (by norm_num) ⟨15644, by rfl⟩ (by norm_num))
theorem R83441 : Reach 83441 := rs (se 2 (by rfl) ⟨31290, by rfl⟩) (B 62581 (by norm_num) ⟨31290, by rfl⟩ (by norm_num))
theorem R83445 : Reach 83445 := rs (se 5 (by rfl) ⟨3911, by rfl⟩) (B 7823 (by norm_num) ⟨3911, by rfl⟩ (by norm_num))
theorem R83449 : Reach 83449 := rs (se 2 (by rfl) ⟨31293, by rfl⟩) (B 62587 (by norm_num) ⟨31293, by rfl⟩ (by norm_num))
theorem R83453 : Reach 83453 := rs (se 3 (by rfl) ⟨15647, by rfl⟩) (B 31295 (by norm_num) ⟨15647, by rfl⟩ (by norm_num))
theorem R83457 : Reach 83457 := rs (se 2 (by rfl) ⟨31296, by rfl⟩) (B 62593 (by norm_num) ⟨31296, by rfl⟩ (by norm_num))
theorem R83461 : Reach 83461 := rs (se 4 (by rfl) ⟨7824, by rfl⟩) (B 15649 (by norm_num) ⟨7824, by rfl⟩ (by norm_num))
theorem R83465 : Reach 83465 := rs (se 2 (by rfl) ⟨31299, by rfl⟩) (B 62599 (by norm_num) ⟨31299, by rfl⟩ (by norm_num))
theorem R83469 : Reach 83469 := rs (se 3 (by rfl) ⟨15650, by rfl⟩) (B 31301 (by norm_num) ⟨15650, by rfl⟩ (by norm_num))
theorem R83473 : Reach 83473 := rs (se 2 (by rfl) ⟨31302, by rfl⟩) (B 62605 (by norm_num) ⟨31302, by rfl⟩ (by norm_num))
theorem R83477 : Reach 83477 := rs (se 6 (by rfl) ⟨1956, by rfl⟩) (B 3913 (by norm_num) ⟨1956, by rfl⟩ (by norm_num))
theorem R83481 : Reach 83481 := rs (se 2 (by rfl) ⟨31305, by rfl⟩) (B 62611 (by norm_num) ⟨31305, by rfl⟩ (by norm_num))
theorem R83485 : Reach 83485 := rs (se 3 (by rfl) ⟨15653, by rfl⟩) (B 31307 (by norm_num) ⟨15653, by rfl⟩ (by norm_num))
theorem R83489 : Reach 83489 := rs (se 2 (by rfl) ⟨31308, by rfl⟩) (B 62617 (by norm_num) ⟨31308, by rfl⟩ (by norm_num))
theorem R83493 : Reach 83493 := rs (se 4 (by rfl) ⟨7827, by rfl⟩) (B 15655 (by norm_num) ⟨7827, by rfl⟩ (by norm_num))
theorem R83497 : Reach 83497 := rs (se 2 (by rfl) ⟨31311, by rfl⟩) (B 62623 (by norm_num) ⟨31311, by rfl⟩ (by norm_num))
theorem R83501 : Reach 83501 := rs (se 3 (by rfl) ⟨15656, by rfl⟩) (B 31313 (by norm_num) ⟨15656, by rfl⟩ (by norm_num))
theorem R83505 : Reach 83505 := rs (se 2 (by rfl) ⟨31314, by rfl⟩) (B 62629 (by norm_num) ⟨31314, by rfl⟩ (by norm_num))
theorem R83509 : Reach 83509 := rs (se 5 (by rfl) ⟨3914, by rfl⟩) (B 7829 (by norm_num) ⟨3914, by rfl⟩ (by norm_num))
theorem R83513 : Reach 83513 := rs (se 2 (by rfl) ⟨31317, by rfl⟩) (B 62635 (by norm_num) ⟨31317, by rfl⟩ (by norm_num))
theorem R83517 : Reach 83517 := rs (se 3 (by rfl) ⟨15659, by rfl⟩) (B 31319 (by norm_num) ⟨15659, by rfl⟩ (by norm_num))
theorem R214589 : Reach 214589 := rs (se 3 (by rfl) ⟨40235, by rfl⟩) (B 80471 (by norm_num) ⟨40235, by rfl⟩ (by norm_num))
theorem R83521 : Reach 83521 := rs (se 2 (by rfl) ⟨31320, by rfl⟩) (B 62641 (by norm_num) ⟨31320, by rfl⟩ (by norm_num))
theorem R83525 : Reach 83525 := rs (se 4 (by rfl) ⟨7830, by rfl⟩) (B 15661 (by norm_num) ⟨7830, by rfl⟩ (by norm_num))
theorem R83529 : Reach 83529 := rs (se 2 (by rfl) ⟨31323, by rfl⟩) (B 62647 (by norm_num) ⟨31323, by rfl⟩ (by norm_num))
theorem R83533 : Reach 83533 := rs (se 3 (by rfl) ⟨15662, by rfl⟩) (B 31325 (by norm_num) ⟨15662, by rfl⟩ (by norm_num))
theorem R83537 : Reach 83537 := rs (se 2 (by rfl) ⟨31326, by rfl⟩) (B 62653 (by norm_num) ⟨31326, by rfl⟩ (by norm_num))
theorem R83541 : Reach 83541 := rs (se 8 (by rfl) ⟨489, by rfl⟩) (B 979 (by norm_num) ⟨489, by rfl⟩ (by norm_num))
theorem R83545 : Reach 83545 := rs (se 2 (by rfl) ⟨31329, by rfl⟩) (B 62659 (by norm_num) ⟨31329, by rfl⟩ (by norm_num))
theorem R83549 : Reach 83549 := rs (se 3 (by rfl) ⟨15665, by rfl⟩) (B 31331 (by norm_num) ⟨15665, by rfl⟩ (by norm_num))
theorem R83553 : Reach 83553 := rs (se 2 (by rfl) ⟨31332, by rfl⟩) (B 62665 (by norm_num) ⟨31332, by rfl⟩ (by norm_num))
theorem R83557 : Reach 83557 := rs (se 4 (by rfl) ⟨7833, by rfl⟩) (B 15667 (by norm_num) ⟨7833, by rfl⟩ (by norm_num))
theorem R83561 : Reach 83561 := rs (se 2 (by rfl) ⟨31335, by rfl⟩) (B 62671 (by norm_num) ⟨31335, by rfl⟩ (by norm_num))
theorem R83565 : Reach 83565 := rs (se 3 (by rfl) ⟨15668, by rfl⟩) (B 31337 (by norm_num) ⟨15668, by rfl⟩ (by norm_num))
theorem R83569 : Reach 83569 := rs (se 2 (by rfl) ⟨31338, by rfl⟩) (B 62677 (by norm_num) ⟨31338, by rfl⟩ (by norm_num))
theorem R83573 : Reach 83573 := rs (se 5 (by rfl) ⟨3917, by rfl⟩) (B 7835 (by norm_num) ⟨3917, by rfl⟩ (by norm_num))
theorem R83577 : Reach 83577 := rs (se 2 (by rfl) ⟨31341, by rfl⟩) (B 62683 (by norm_num) ⟨31341, by rfl⟩ (by norm_num))
theorem R83581 : Reach 83581 := rs (se 3 (by rfl) ⟨15671, by rfl⟩) (B 31343 (by norm_num) ⟨15671, by rfl⟩ (by norm_num))
theorem R83585 : Reach 83585 := rs (se 2 (by rfl) ⟨31344, by rfl⟩) (B 62689 (by norm_num) ⟨31344, by rfl⟩ (by norm_num))
theorem R83589 : Reach 83589 := rs (se 4 (by rfl) ⟨7836, by rfl⟩) (B 15673 (by norm_num) ⟨7836, by rfl⟩ (by norm_num))
theorem R83593 : Reach 83593 := rs (se 2 (by rfl) ⟨31347, by rfl⟩) (B 62695 (by norm_num) ⟨31347, by rfl⟩ (by norm_num))
theorem R83597 : Reach 83597 := rs (se 3 (by rfl) ⟨15674, by rfl⟩) (B 31349 (by norm_num) ⟨15674, by rfl⟩ (by norm_num))
theorem R83601 : Reach 83601 := rs (se 2 (by rfl) ⟨31350, by rfl⟩) (B 62701 (by norm_num) ⟨31350, by rfl⟩ (by norm_num))
theorem R83605 : Reach 83605 := rs (se 6 (by rfl) ⟨1959, by rfl⟩) (B 3919 (by norm_num) ⟨1959, by rfl⟩ (by norm_num))
theorem R83609 : Reach 83609 := rs (se 2 (by rfl) ⟨31353, by rfl⟩) (B 62707 (by norm_num) ⟨31353, by rfl⟩ (by norm_num))
theorem R83613 : Reach 83613 := rs (se 3 (by rfl) ⟨15677, by rfl⟩) (B 31355 (by norm_num) ⟨15677, by rfl⟩ (by norm_num))
theorem R83617 : Reach 83617 := rs (se 2 (by rfl) ⟨31356, by rfl⟩) (B 62713 (by norm_num) ⟨31356, by rfl⟩ (by norm_num))
theorem R83621 : Reach 83621 := rs (se 4 (by rfl) ⟨7839, by rfl⟩) (B 15679 (by norm_num) ⟨7839, by rfl⟩ (by norm_num))
theorem R83625 : Reach 83625 := rs (se 2 (by rfl) ⟨31359, by rfl⟩) (B 62719 (by norm_num) ⟨31359, by rfl⟩ (by norm_num))
theorem R83629 : Reach 83629 := rs (se 3 (by rfl) ⟨15680, by rfl⟩) (B 31361 (by norm_num) ⟨15680, by rfl⟩ (by norm_num))
theorem R83633 : Reach 83633 := rs (se 2 (by rfl) ⟨31362, by rfl⟩) (B 62725 (by norm_num) ⟨31362, by rfl⟩ (by norm_num))
theorem R83637 : Reach 83637 := rs (se 5 (by rfl) ⟨3920, by rfl⟩) (B 7841 (by norm_num) ⟨3920, by rfl⟩ (by norm_num))
theorem R83641 : Reach 83641 := rs (se 2 (by rfl) ⟨31365, by rfl⟩) (B 62731 (by norm_num) ⟨31365, by rfl⟩ (by norm_num))
theorem R83645 : Reach 83645 := rs (se 3 (by rfl) ⟨15683, by rfl⟩) (B 31367 (by norm_num) ⟨15683, by rfl⟩ (by norm_num))
theorem R83649 : Reach 83649 := rs (se 2 (by rfl) ⟨31368, by rfl⟩) (B 62737 (by norm_num) ⟨31368, by rfl⟩ (by norm_num))
theorem R83653 : Reach 83653 := rs (se 4 (by rfl) ⟨7842, by rfl⟩) (B 15685 (by norm_num) ⟨7842, by rfl⟩ (by norm_num))
theorem R83657 : Reach 83657 := rs (se 2 (by rfl) ⟨31371, by rfl⟩) (B 62743 (by norm_num) ⟨31371, by rfl⟩ (by norm_num))
theorem R83661 : Reach 83661 := rs (se 3 (by rfl) ⟨15686, by rfl⟩) (B 31373 (by norm_num) ⟨15686, by rfl⟩ (by norm_num))
theorem R83665 : Reach 83665 := rs (se 2 (by rfl) ⟨31374, by rfl⟩) (B 62749 (by norm_num) ⟨31374, by rfl⟩ (by norm_num))
theorem R83669 : Reach 83669 := rs (se 7 (by rfl) ⟨980, by rfl⟩) (B 1961 (by norm_num) ⟨980, by rfl⟩ (by norm_num))
theorem R83673 : Reach 83673 := rs (se 2 (by rfl) ⟨31377, by rfl⟩) (B 62755 (by norm_num) ⟨31377, by rfl⟩ (by norm_num))
theorem R83677 : Reach 83677 := rs (se 3 (by rfl) ⟨15689, by rfl⟩) (B 31379 (by norm_num) ⟨15689, by rfl⟩ (by norm_num))
theorem R83681 : Reach 83681 := rs (se 2 (by rfl) ⟨31380, by rfl⟩) (B 62761 (by norm_num) ⟨31380, by rfl⟩ (by norm_num))
theorem R83685 : Reach 83685 := rs (se 4 (by rfl) ⟨7845, by rfl⟩) (B 15691 (by norm_num) ⟨7845, by rfl⟩ (by norm_num))
theorem R83689 : Reach 83689 := rs (se 2 (by rfl) ⟨31383, by rfl⟩) (B 62767 (by norm_num) ⟨31383, by rfl⟩ (by norm_num))
theorem R83693 : Reach 83693 := rs (se 3 (by rfl) ⟨15692, by rfl⟩) (B 31385 (by norm_num) ⟨15692, by rfl⟩ (by norm_num))
theorem R83697 : Reach 83697 := rs (se 2 (by rfl) ⟨31386, by rfl⟩) (B 62773 (by norm_num) ⟨31386, by rfl⟩ (by norm_num))
theorem R83701 : Reach 83701 := rs (se 5 (by rfl) ⟨3923, by rfl⟩) (B 7847 (by norm_num) ⟨3923, by rfl⟩ (by norm_num))
theorem R83705 : Reach 83705 := rs (se 2 (by rfl) ⟨31389, by rfl⟩) (B 62779 (by norm_num) ⟨31389, by rfl⟩ (by norm_num))
theorem R83709 : Reach 83709 := rs (se 3 (by rfl) ⟨15695, by rfl⟩) (B 31391 (by norm_num) ⟨15695, by rfl⟩ (by norm_num))
theorem R83713 : Reach 83713 := rs (se 2 (by rfl) ⟨31392, by rfl⟩) (B 62785 (by norm_num) ⟨31392, by rfl⟩ (by norm_num))
theorem R83717 : Reach 83717 := rs (se 4 (by rfl) ⟨7848, by rfl⟩) (B 15697 (by norm_num) ⟨7848, by rfl⟩ (by norm_num))
theorem R83721 : Reach 83721 := rs (se 2 (by rfl) ⟨31395, by rfl⟩) (B 62791 (by norm_num) ⟨31395, by rfl⟩ (by norm_num))
theorem R83725 : Reach 83725 := rs (se 3 (by rfl) ⟨15698, by rfl⟩) (B 31397 (by norm_num) ⟨15698, by rfl⟩ (by norm_num))
theorem R83729 : Reach 83729 := rs (se 2 (by rfl) ⟨31398, by rfl⟩) (B 62797 (by norm_num) ⟨31398, by rfl⟩ (by norm_num))
theorem R83733 : Reach 83733 := rs (se 6 (by rfl) ⟨1962, by rfl⟩) (B 3925 (by norm_num) ⟨1962, by rfl⟩ (by norm_num))
theorem R83737 : Reach 83737 := rs (se 2 (by rfl) ⟨31401, by rfl⟩) (B 62803 (by norm_num) ⟨31401, by rfl⟩ (by norm_num))
theorem R83741 : Reach 83741 := rs (se 3 (by rfl) ⟨15701, by rfl⟩) (B 31403 (by norm_num) ⟨15701, by rfl⟩ (by norm_num))
theorem R83745 : Reach 83745 := rs (se 2 (by rfl) ⟨31404, by rfl⟩) (B 62809 (by norm_num) ⟨31404, by rfl⟩ (by norm_num))
theorem R83749 : Reach 83749 := rs (se 4 (by rfl) ⟨7851, by rfl⟩) (B 15703 (by norm_num) ⟨7851, by rfl⟩ (by norm_num))
theorem R83753 : Reach 83753 := rs (se 2 (by rfl) ⟨31407, by rfl⟩) (B 62815 (by norm_num) ⟨31407, by rfl⟩ (by norm_num))
theorem R83757 : Reach 83757 := rs (se 3 (by rfl) ⟨15704, by rfl⟩) (B 31409 (by norm_num) ⟨15704, by rfl⟩ (by norm_num))
theorem R83761 : Reach 83761 := rs (se 2 (by rfl) ⟨31410, by rfl⟩) (B 62821 (by norm_num) ⟨31410, by rfl⟩ (by norm_num))
theorem R83765 : Reach 83765 := rs (se 5 (by rfl) ⟨3926, by rfl⟩) (B 7853 (by norm_num) ⟨3926, by rfl⟩ (by norm_num))
theorem R83769 : Reach 83769 := rs (se 2 (by rfl) ⟨31413, by rfl⟩) (B 62827 (by norm_num) ⟨31413, by rfl⟩ (by norm_num))
theorem R83773 : Reach 83773 := rs (se 3 (by rfl) ⟨15707, by rfl⟩) (B 31415 (by norm_num) ⟨15707, by rfl⟩ (by norm_num))
theorem R83777 : Reach 83777 := rs (se 2 (by rfl) ⟨31416, by rfl⟩) (B 62833 (by norm_num) ⟨31416, by rfl⟩ (by norm_num))
theorem R83781 : Reach 83781 := rs (se 4 (by rfl) ⟨7854, by rfl⟩) (B 15709 (by norm_num) ⟨7854, by rfl⟩ (by norm_num))
theorem R83785 : Reach 83785 := rs (se 2 (by rfl) ⟨31419, by rfl⟩) (B 62839 (by norm_num) ⟨31419, by rfl⟩ (by norm_num))
theorem R83789 : Reach 83789 := rs (se 3 (by rfl) ⟨15710, by rfl⟩) (B 31421 (by norm_num) ⟨15710, by rfl⟩ (by norm_num))
theorem R83793 : Reach 83793 := rs (se 2 (by rfl) ⟨31422, by rfl⟩) (B 62845 (by norm_num) ⟨31422, by rfl⟩ (by norm_num))
theorem R83797 : Reach 83797 := rs (se 9 (by rfl) ⟨245, by rfl⟩) (B 491 (by norm_num) ⟨245, by rfl⟩ (by norm_num))
theorem R345941 : Reach 345941 := rs (se 9 (by rfl) ⟨1013, by rfl⟩) (B 2027 (by norm_num) ⟨1013, by rfl⟩ (by norm_num))
theorem R83801 : Reach 83801 := rs (se 2 (by rfl) ⟨31425, by rfl⟩) (B 62851 (by norm_num) ⟨31425, by rfl⟩ (by norm_num))
theorem R83805 : Reach 83805 := rs (se 3 (by rfl) ⟨15713, by rfl⟩) (B 31427 (by norm_num) ⟨15713, by rfl⟩ (by norm_num))
theorem R83809 : Reach 83809 := rs (se 2 (by rfl) ⟨31428, by rfl⟩) (B 62857 (by norm_num) ⟨31428, by rfl⟩ (by norm_num))
theorem R83813 : Reach 83813 := rs (se 4 (by rfl) ⟨7857, by rfl⟩) (B 15715 (by norm_num) ⟨7857, by rfl⟩ (by norm_num))
theorem R83817 : Reach 83817 := rs (se 2 (by rfl) ⟨31431, by rfl⟩) (B 62863 (by norm_num) ⟨31431, by rfl⟩ (by norm_num))
theorem R83821 : Reach 83821 := rs (se 3 (by rfl) ⟨15716, by rfl⟩) (B 31433 (by norm_num) ⟨15716, by rfl⟩ (by norm_num))
theorem R83825 : Reach 83825 := rs (se 2 (by rfl) ⟨31434, by rfl⟩) (B 62869 (by norm_num) ⟨31434, by rfl⟩ (by norm_num))
theorem R509813 : Reach 509813 := rs (se 5 (by rfl) ⟨23897, by rfl⟩) (B 47795 (by norm_num) ⟨23897, by rfl⟩ (by norm_num))
theorem R83829 : Reach 83829 := rs (se 5 (by rfl) ⟨3929, by rfl⟩) (B 7859 (by norm_num) ⟨3929, by rfl⟩ (by norm_num))
theorem R83833 : Reach 83833 := rs (se 2 (by rfl) ⟨31437, by rfl⟩) (B 62875 (by norm_num) ⟨31437, by rfl⟩ (by norm_num))
theorem R83837 : Reach 83837 := rs (se 3 (by rfl) ⟨15719, by rfl⟩) (B 31439 (by norm_num) ⟨15719, by rfl⟩ (by norm_num))
theorem R83841 : Reach 83841 := rs (se 2 (by rfl) ⟨31440, by rfl⟩) (B 62881 (by norm_num) ⟨31440, by rfl⟩ (by norm_num))
theorem R83845 : Reach 83845 := rs (se 4 (by rfl) ⟨7860, by rfl⟩) (B 15721 (by norm_num) ⟨7860, by rfl⟩ (by norm_num))
theorem R83849 : Reach 83849 := rs (se 2 (by rfl) ⟨31443, by rfl⟩) (B 62887 (by norm_num) ⟨31443, by rfl⟩ (by norm_num))
theorem R83853 : Reach 83853 := rs (se 3 (by rfl) ⟨15722, by rfl⟩) (B 31445 (by norm_num) ⟨15722, by rfl⟩ (by norm_num))
theorem R83857 : Reach 83857 := rs (se 2 (by rfl) ⟨31446, by rfl⟩) (B 62893 (by norm_num) ⟨31446, by rfl⟩ (by norm_num))
theorem R83861 : Reach 83861 := rs (se 6 (by rfl) ⟨1965, by rfl⟩) (B 3931 (by norm_num) ⟨1965, by rfl⟩ (by norm_num))
theorem R214933 : Reach 214933 := rs (se 6 (by rfl) ⟨5037, by rfl⟩) (B 10075 (by norm_num) ⟨5037, by rfl⟩ (by norm_num))
theorem R313237 : Reach 313237 := rs (se 6 (by rfl) ⟨7341, by rfl⟩) (B 14683 (by norm_num) ⟨7341, by rfl⟩ (by norm_num))
theorem R83865 : Reach 83865 := rs (se 2 (by rfl) ⟨31449, by rfl⟩) (B 62899 (by norm_num) ⟨31449, by rfl⟩ (by norm_num))
theorem R83869 : Reach 83869 := rs (se 3 (by rfl) ⟨15725, by rfl⟩) (B 31451 (by norm_num) ⟨15725, by rfl⟩ (by norm_num))
theorem R83873 : Reach 83873 := rs (se 2 (by rfl) ⟨31452, by rfl⟩) (B 62905 (by norm_num) ⟨31452, by rfl⟩ (by norm_num))
theorem R83877 : Reach 83877 := rs (se 4 (by rfl) ⟨7863, by rfl⟩) (B 15727 (by norm_num) ⟨7863, by rfl⟩ (by norm_num))
theorem R83881 : Reach 83881 := rs (se 2 (by rfl) ⟨31455, by rfl⟩) (B 62911 (by norm_num) ⟨31455, by rfl⟩ (by norm_num))
theorem R83885 : Reach 83885 := rs (se 3 (by rfl) ⟨15728, by rfl⟩) (B 31457 (by norm_num) ⟨15728, by rfl⟩ (by norm_num))
theorem R83889 : Reach 83889 := rs (se 2 (by rfl) ⟨31458, by rfl⟩) (B 62917 (by norm_num) ⟨31458, by rfl⟩ (by norm_num))
theorem R83893 : Reach 83893 := rs (se 5 (by rfl) ⟨3932, by rfl⟩) (B 7865 (by norm_num) ⟨3932, by rfl⟩ (by norm_num))
theorem R83897 : Reach 83897 := rs (se 2 (by rfl) ⟨31461, by rfl⟩) (B 62923 (by norm_num) ⟨31461, by rfl⟩ (by norm_num))
theorem R83901 : Reach 83901 := rs (se 3 (by rfl) ⟨15731, by rfl⟩) (B 31463 (by norm_num) ⟨15731, by rfl⟩ (by norm_num))
theorem R83905 : Reach 83905 := rs (se 2 (by rfl) ⟨31464, by rfl⟩) (B 62929 (by norm_num) ⟨31464, by rfl⟩ (by norm_num))
theorem R83909 : Reach 83909 := rs (se 4 (by rfl) ⟨7866, by rfl⟩) (B 15733 (by norm_num) ⟨7866, by rfl⟩ (by norm_num))
theorem R83913 : Reach 83913 := rs (se 2 (by rfl) ⟨31467, by rfl⟩) (B 62935 (by norm_num) ⟨31467, by rfl⟩ (by norm_num))
theorem R83917 : Reach 83917 := rs (se 3 (by rfl) ⟨15734, by rfl⟩) (B 31469 (by norm_num) ⟨15734, by rfl⟩ (by norm_num))
theorem R83921 : Reach 83921 := rs (se 2 (by rfl) ⟨31470, by rfl⟩) (B 62941 (by norm_num) ⟨31470, by rfl⟩ (by norm_num))
theorem R83925 : Reach 83925 := rs (se 7 (by rfl) ⟨983, by rfl⟩) (B 1967 (by norm_num) ⟨983, by rfl⟩ (by norm_num))
theorem R83929 : Reach 83929 := rs (se 2 (by rfl) ⟨31473, by rfl⟩) (B 62947 (by norm_num) ⟨31473, by rfl⟩ (by norm_num))
theorem R83933 : Reach 83933 := rs (se 3 (by rfl) ⟨15737, by rfl⟩) (B 31475 (by norm_num) ⟨15737, by rfl⟩ (by norm_num))
theorem R83937 : Reach 83937 := rs (se 2 (by rfl) ⟨31476, by rfl⟩) (B 62953 (by norm_num) ⟨31476, by rfl⟩ (by norm_num))
theorem R83941 : Reach 83941 := rs (se 4 (by rfl) ⟨7869, by rfl⟩) (B 15739 (by norm_num) ⟨7869, by rfl⟩ (by norm_num))
theorem R83945 : Reach 83945 := rs (se 2 (by rfl) ⟨31479, by rfl⟩) (B 62959 (by norm_num) ⟨31479, by rfl⟩ (by norm_num))
theorem R83949 : Reach 83949 := rs (se 3 (by rfl) ⟨15740, by rfl⟩) (B 31481 (by norm_num) ⟨15740, by rfl⟩ (by norm_num))
theorem R83953 : Reach 83953 := rs (se 2 (by rfl) ⟨31482, by rfl⟩) (B 62965 (by norm_num) ⟨31482, by rfl⟩ (by norm_num))
theorem R83957 : Reach 83957 := rs (se 5 (by rfl) ⟨3935, by rfl⟩) (B 7871 (by norm_num) ⟨3935, by rfl⟩ (by norm_num))
theorem R83961 : Reach 83961 := rs (se 2 (by rfl) ⟨31485, by rfl⟩) (B 62971 (by norm_num) ⟨31485, by rfl⟩ (by norm_num))
theorem R83965 : Reach 83965 := rs (se 3 (by rfl) ⟨15743, by rfl⟩) (B 31487 (by norm_num) ⟨15743, by rfl⟩ (by norm_num))
theorem R83969 : Reach 83969 := rs (se 2 (by rfl) ⟨31488, by rfl⟩) (B 62977 (by norm_num) ⟨31488, by rfl⟩ (by norm_num))
theorem R83973 : Reach 83973 := rs (se 4 (by rfl) ⟨7872, by rfl⟩) (B 15745 (by norm_num) ⟨7872, by rfl⟩ (by norm_num))
theorem R215045 : Reach 215045 := rs (se 4 (by rfl) ⟨20160, by rfl⟩) (B 40321 (by norm_num) ⟨20160, by rfl⟩ (by norm_num))
theorem R83977 : Reach 83977 := rs (se 2 (by rfl) ⟨31491, by rfl⟩) (B 62983 (by norm_num) ⟨31491, by rfl⟩ (by norm_num))
theorem R83981 : Reach 83981 := rs (se 3 (by rfl) ⟨15746, by rfl⟩) (B 31493 (by norm_num) ⟨15746, by rfl⟩ (by norm_num))
theorem R83985 : Reach 83985 := rs (se 2 (by rfl) ⟨31494, by rfl⟩) (B 62989 (by norm_num) ⟨31494, by rfl⟩ (by norm_num))
theorem R83989 : Reach 83989 := rs (se 6 (by rfl) ⟨1968, by rfl⟩) (B 3937 (by norm_num) ⟨1968, by rfl⟩ (by norm_num))
theorem R83993 : Reach 83993 := rs (se 2 (by rfl) ⟨31497, by rfl⟩) (B 62995 (by norm_num) ⟨31497, by rfl⟩ (by norm_num))
theorem R83997 : Reach 83997 := rs (se 3 (by rfl) ⟨15749, by rfl⟩) (B 31499 (by norm_num) ⟨15749, by rfl⟩ (by norm_num))
theorem R84001 : Reach 84001 := rs (se 2 (by rfl) ⟨31500, by rfl⟩) (B 63001 (by norm_num) ⟨31500, by rfl⟩ (by norm_num))
theorem R84005 : Reach 84005 := rs (se 4 (by rfl) ⟨7875, by rfl⟩) (B 15751 (by norm_num) ⟨7875, by rfl⟩ (by norm_num))
theorem R84009 : Reach 84009 := rs (se 2 (by rfl) ⟨31503, by rfl⟩) (B 63007 (by norm_num) ⟨31503, by rfl⟩ (by norm_num))
theorem R84013 : Reach 84013 := rs (se 3 (by rfl) ⟨15752, by rfl⟩) (B 31505 (by norm_num) ⟨15752, by rfl⟩ (by norm_num))
theorem R84017 : Reach 84017 := rs (se 2 (by rfl) ⟨31506, by rfl⟩) (B 63013 (by norm_num) ⟨31506, by rfl⟩ (by norm_num))
theorem R84021 : Reach 84021 := rs (se 5 (by rfl) ⟨3938, by rfl⟩) (B 7877 (by norm_num) ⟨3938, by rfl⟩ (by norm_num))
theorem R84025 : Reach 84025 := rs (se 2 (by rfl) ⟨31509, by rfl⟩) (B 63019 (by norm_num) ⟨31509, by rfl⟩ (by norm_num))
theorem R84029 : Reach 84029 := rs (se 3 (by rfl) ⟨15755, by rfl⟩) (B 31511 (by norm_num) ⟨15755, by rfl⟩ (by norm_num))
theorem R84033 : Reach 84033 := rs (se 2 (by rfl) ⟨31512, by rfl⟩) (B 63025 (by norm_num) ⟨31512, by rfl⟩ (by norm_num))
theorem R84037 : Reach 84037 := rs (se 4 (by rfl) ⟨7878, by rfl⟩) (B 15757 (by norm_num) ⟨7878, by rfl⟩ (by norm_num))
theorem R182341 : Reach 182341 := rs (se 4 (by rfl) ⟨17094, by rfl⟩) (B 34189 (by norm_num) ⟨17094, by rfl⟩ (by norm_num))
theorem R84041 : Reach 84041 := rs (se 2 (by rfl) ⟨31515, by rfl⟩) (B 63031 (by norm_num) ⟨31515, by rfl⟩ (by norm_num))
theorem R215117 : Reach 215117 := rs (se 3 (by rfl) ⟨40334, by rfl⟩) (B 80669 (by norm_num) ⟨40334, by rfl⟩ (by norm_num))
theorem R84045 : Reach 84045 := rs (se 3 (by rfl) ⟨15758, by rfl⟩) (B 31517 (by norm_num) ⟨15758, by rfl⟩ (by norm_num))
theorem R84049 : Reach 84049 := rs (se 2 (by rfl) ⟨31518, by rfl⟩) (B 63037 (by norm_num) ⟨31518, by rfl⟩ (by norm_num))
theorem R84053 : Reach 84053 := rs (se 8 (by rfl) ⟨492, by rfl⟩) (B 985 (by norm_num) ⟨492, by rfl⟩ (by norm_num))
theorem R84057 : Reach 84057 := rs (se 2 (by rfl) ⟨31521, by rfl⟩) (B 63043 (by norm_num) ⟨31521, by rfl⟩ (by norm_num))
theorem R84061 : Reach 84061 := rs (se 3 (by rfl) ⟨15761, by rfl⟩) (B 31523 (by norm_num) ⟨15761, by rfl⟩ (by norm_num))
theorem R84065 : Reach 84065 := rs (se 2 (by rfl) ⟨31524, by rfl⟩) (B 63049 (by norm_num) ⟨31524, by rfl⟩ (by norm_num))
theorem R84069 : Reach 84069 := rs (se 4 (by rfl) ⟨7881, by rfl⟩) (B 15763 (by norm_num) ⟨7881, by rfl⟩ (by norm_num))
theorem R84073 : Reach 84073 := rs (se 2 (by rfl) ⟨31527, by rfl⟩) (B 63055 (by norm_num) ⟨31527, by rfl⟩ (by norm_num))
theorem R84077 : Reach 84077 := rs (se 3 (by rfl) ⟨15764, by rfl⟩) (B 31529 (by norm_num) ⟨15764, by rfl⟩ (by norm_num))
theorem R84081 : Reach 84081 := rs (se 2 (by rfl) ⟨31530, by rfl⟩) (B 63061 (by norm_num) ⟨31530, by rfl⟩ (by norm_num))
theorem R84085 : Reach 84085 := rs (se 5 (by rfl) ⟨3941, by rfl⟩) (B 7883 (by norm_num) ⟨3941, by rfl⟩ (by norm_num))
theorem R84089 : Reach 84089 := rs (se 2 (by rfl) ⟨31533, by rfl⟩) (B 63067 (by norm_num) ⟨31533, by rfl⟩ (by norm_num))
theorem R84093 : Reach 84093 := rs (se 3 (by rfl) ⟨15767, by rfl⟩) (B 31535 (by norm_num) ⟨15767, by rfl⟩ (by norm_num))
theorem R84097 : Reach 84097 := rs (se 2 (by rfl) ⟨31536, by rfl⟩) (B 63073 (by norm_num) ⟨31536, by rfl⟩ (by norm_num))
theorem R84101 : Reach 84101 := rs (se 4 (by rfl) ⟨7884, by rfl⟩) (B 15769 (by norm_num) ⟨7884, by rfl⟩ (by norm_num))
theorem R84105 : Reach 84105 := rs (se 2 (by rfl) ⟨31539, by rfl⟩) (B 63079 (by norm_num) ⟨31539, by rfl⟩ (by norm_num))
theorem R84109 : Reach 84109 := rs (se 3 (by rfl) ⟨15770, by rfl⟩) (B 31541 (by norm_num) ⟨15770, by rfl⟩ (by norm_num))
theorem R84113 : Reach 84113 := rs (se 2 (by rfl) ⟨31542, by rfl⟩) (B 63085 (by norm_num) ⟨31542, by rfl⟩ (by norm_num))
theorem R84117 : Reach 84117 := rs (se 6 (by rfl) ⟨1971, by rfl⟩) (B 3943 (by norm_num) ⟨1971, by rfl⟩ (by norm_num))
theorem R84121 : Reach 84121 := rs (se 2 (by rfl) ⟨31545, by rfl⟩) (B 63091 (by norm_num) ⟨31545, by rfl⟩ (by norm_num))
theorem R84125 : Reach 84125 := rs (se 3 (by rfl) ⟨15773, by rfl⟩) (B 31547 (by norm_num) ⟨15773, by rfl⟩ (by norm_num))
theorem R84129 : Reach 84129 := rs (se 2 (by rfl) ⟨31548, by rfl⟩) (B 63097 (by norm_num) ⟨31548, by rfl⟩ (by norm_num))
theorem R84133 : Reach 84133 := rs (se 4 (by rfl) ⟨7887, by rfl⟩) (B 15775 (by norm_num) ⟨7887, by rfl⟩ (by norm_num))
theorem R84137 : Reach 84137 := rs (se 2 (by rfl) ⟨31551, by rfl⟩) (B 63103 (by norm_num) ⟨31551, by rfl⟩ (by norm_num))
theorem R84141 : Reach 84141 := rs (se 3 (by rfl) ⟨15776, by rfl⟩) (B 31553 (by norm_num) ⟨15776, by rfl⟩ (by norm_num))
theorem R84145 : Reach 84145 := rs (se 2 (by rfl) ⟨31554, by rfl⟩) (B 63109 (by norm_num) ⟨31554, by rfl⟩ (by norm_num))
theorem R84149 : Reach 84149 := rs (se 5 (by rfl) ⟨3944, by rfl⟩) (B 7889 (by norm_num) ⟨3944, by rfl⟩ (by norm_num))
theorem R84153 : Reach 84153 := rs (se 2 (by rfl) ⟨31557, by rfl⟩) (B 63115 (by norm_num) ⟨31557, by rfl⟩ (by norm_num))
theorem R84157 : Reach 84157 := rs (se 3 (by rfl) ⟨15779, by rfl⟩) (B 31559 (by norm_num) ⟨15779, by rfl⟩ (by norm_num))
theorem R84161 : Reach 84161 := rs (se 2 (by rfl) ⟨31560, by rfl⟩) (B 63121 (by norm_num) ⟨31560, by rfl⟩ (by norm_num))
theorem R84165 : Reach 84165 := rs (se 4 (by rfl) ⟨7890, by rfl⟩) (B 15781 (by norm_num) ⟨7890, by rfl⟩ (by norm_num))
theorem R215237 : Reach 215237 := rs (se 4 (by rfl) ⟨20178, by rfl⟩) (B 40357 (by norm_num) ⟨20178, by rfl⟩ (by norm_num))
theorem R84169 : Reach 84169 := rs (se 2 (by rfl) ⟨31563, by rfl⟩) (B 63127 (by norm_num) ⟨31563, by rfl⟩ (by norm_num))
theorem R84173 : Reach 84173 := rs (se 3 (by rfl) ⟨15782, by rfl⟩) (B 31565 (by norm_num) ⟨15782, by rfl⟩ (by norm_num))
theorem R84177 : Reach 84177 := rs (se 2 (by rfl) ⟨31566, by rfl⟩) (B 63133 (by norm_num) ⟨31566, by rfl⟩ (by norm_num))
theorem R84181 : Reach 84181 := rs (se 7 (by rfl) ⟨986, by rfl⟩) (B 1973 (by norm_num) ⟨986, by rfl⟩ (by norm_num))
theorem R84185 : Reach 84185 := rs (se 2 (by rfl) ⟨31569, by rfl⟩) (B 63139 (by norm_num) ⟨31569, by rfl⟩ (by norm_num))
theorem R84189 : Reach 84189 := rs (se 3 (by rfl) ⟨15785, by rfl⟩) (B 31571 (by norm_num) ⟨15785, by rfl⟩ (by norm_num))
theorem R84193 : Reach 84193 := rs (se 2 (by rfl) ⟨31572, by rfl⟩) (B 63145 (by norm_num) ⟨31572, by rfl⟩ (by norm_num))
theorem R84197 : Reach 84197 := rs (se 4 (by rfl) ⟨7893, by rfl⟩) (B 15787 (by norm_num) ⟨7893, by rfl⟩ (by norm_num))
theorem R84201 : Reach 84201 := rs (se 2 (by rfl) ⟨31575, by rfl⟩) (B 63151 (by norm_num) ⟨31575, by rfl⟩ (by norm_num))
theorem R84205 : Reach 84205 := rs (se 3 (by rfl) ⟨15788, by rfl⟩) (B 31577 (by norm_num) ⟨15788, by rfl⟩ (by norm_num))
theorem R84209 : Reach 84209 := rs (se 2 (by rfl) ⟨31578, by rfl⟩) (B 63157 (by norm_num) ⟨31578, by rfl⟩ (by norm_num))
theorem R84213 : Reach 84213 := rs (se 5 (by rfl) ⟨3947, by rfl⟩) (B 7895 (by norm_num) ⟨3947, by rfl⟩ (by norm_num))
theorem R84217 : Reach 84217 := rs (se 2 (by rfl) ⟨31581, by rfl⟩) (B 63163 (by norm_num) ⟨31581, by rfl⟩ (by norm_num))
theorem R84221 : Reach 84221 := rs (se 3 (by rfl) ⟨15791, by rfl⟩) (B 31583 (by norm_num) ⟨15791, by rfl⟩ (by norm_num))
theorem R84225 : Reach 84225 := rs (se 2 (by rfl) ⟨31584, by rfl⟩) (B 63169 (by norm_num) ⟨31584, by rfl⟩ (by norm_num))
theorem R84229 : Reach 84229 := rs (se 4 (by rfl) ⟨7896, by rfl⟩) (B 15793 (by norm_num) ⟨7896, by rfl⟩ (by norm_num))
theorem R84233 : Reach 84233 := rs (se 2 (by rfl) ⟨31587, by rfl⟩) (B 63175 (by norm_num) ⟨31587, by rfl⟩ (by norm_num))
theorem R84237 : Reach 84237 := rs (se 3 (by rfl) ⟨15794, by rfl⟩) (B 31589 (by norm_num) ⟨15794, by rfl⟩ (by norm_num))
theorem R84241 : Reach 84241 := rs (se 2 (by rfl) ⟨31590, by rfl⟩) (B 63181 (by norm_num) ⟨31590, by rfl⟩ (by norm_num))
theorem R280853 : Reach 280853 := rs (se 6 (by rfl) ⟨6582, by rfl⟩) (B 13165 (by norm_num) ⟨6582, by rfl⟩ (by norm_num))
theorem R84245 : Reach 84245 := rs (se 6 (by rfl) ⟨1974, by rfl⟩) (B 3949 (by norm_num) ⟨1974, by rfl⟩ (by norm_num))
theorem R84249 : Reach 84249 := rs (se 2 (by rfl) ⟨31593, by rfl⟩) (B 63187 (by norm_num) ⟨31593, by rfl⟩ (by norm_num))
theorem R84253 : Reach 84253 := rs (se 3 (by rfl) ⟨15797, by rfl⟩) (B 31595 (by norm_num) ⟨15797, by rfl⟩ (by norm_num))
theorem R84257 : Reach 84257 := rs (se 2 (by rfl) ⟨31596, by rfl⟩) (B 63193 (by norm_num) ⟨31596, by rfl⟩ (by norm_num))
theorem R84261 : Reach 84261 := rs (se 4 (by rfl) ⟨7899, by rfl⟩) (B 15799 (by norm_num) ⟨7899, by rfl⟩ (by norm_num))
theorem R84265 : Reach 84265 := rs (se 2 (by rfl) ⟨31599, by rfl⟩) (B 63199 (by norm_num) ⟨31599, by rfl⟩ (by norm_num))
theorem R84269 : Reach 84269 := rs (se 3 (by rfl) ⟨15800, by rfl⟩) (B 31601 (by norm_num) ⟨15800, by rfl⟩ (by norm_num))
theorem R84273 : Reach 84273 := rs (se 2 (by rfl) ⟨31602, by rfl⟩) (B 63205 (by norm_num) ⟨31602, by rfl⟩ (by norm_num))
theorem R84277 : Reach 84277 := rs (se 5 (by rfl) ⟨3950, by rfl⟩) (B 7901 (by norm_num) ⟨3950, by rfl⟩ (by norm_num))
theorem R84281 : Reach 84281 := rs (se 2 (by rfl) ⟨31605, by rfl⟩) (B 63211 (by norm_num) ⟨31605, by rfl⟩ (by norm_num))
theorem R84285 : Reach 84285 := rs (se 3 (by rfl) ⟨15803, by rfl⟩) (B 31607 (by norm_num) ⟨15803, by rfl⟩ (by norm_num))
theorem R84289 : Reach 84289 := rs (se 2 (by rfl) ⟨31608, by rfl⟩) (B 63217 (by norm_num) ⟨31608, by rfl⟩ (by norm_num))
theorem R84293 : Reach 84293 := rs (se 4 (by rfl) ⟨7902, by rfl⟩) (B 15805 (by norm_num) ⟨7902, by rfl⟩ (by norm_num))
theorem R84297 : Reach 84297 := rs (se 2 (by rfl) ⟨31611, by rfl⟩) (B 63223 (by norm_num) ⟨31611, by rfl⟩ (by norm_num))
theorem R84301 : Reach 84301 := rs (se 3 (by rfl) ⟨15806, by rfl⟩) (B 31613 (by norm_num) ⟨15806, by rfl⟩ (by norm_num))
theorem R84305 : Reach 84305 := rs (se 2 (by rfl) ⟨31614, by rfl⟩) (B 63229 (by norm_num) ⟨31614, by rfl⟩ (by norm_num))
theorem R84309 : Reach 84309 := rs (se 10 (by rfl) ⟨123, by rfl⟩) (B 247 (by norm_num) ⟨123, by rfl⟩ (by norm_num))
theorem R313685 : Reach 313685 := rs (se 10 (by rfl) ⟨459, by rfl⟩) (B 919 (by norm_num) ⟨459, by rfl⟩ (by norm_num))
theorem R84313 : Reach 84313 := rs (se 2 (by rfl) ⟨31617, by rfl⟩) (B 63235 (by norm_num) ⟨31617, by rfl⟩ (by norm_num))
theorem R84317 : Reach 84317 := rs (se 3 (by rfl) ⟨15809, by rfl⟩) (B 31619 (by norm_num) ⟨15809, by rfl⟩ (by norm_num))
theorem R84321 : Reach 84321 := rs (se 2 (by rfl) ⟨31620, by rfl⟩) (B 63241 (by norm_num) ⟨31620, by rfl⟩ (by norm_num))
theorem R84325 : Reach 84325 := rs (se 4 (by rfl) ⟨7905, by rfl⟩) (B 15811 (by norm_num) ⟨7905, by rfl⟩ (by norm_num))
theorem R84329 : Reach 84329 := rs (se 2 (by rfl) ⟨31623, by rfl⟩) (B 63247 (by norm_num) ⟨31623, by rfl⟩ (by norm_num))
theorem R84333 : Reach 84333 := rs (se 3 (by rfl) ⟨15812, by rfl⟩) (B 31625 (by norm_num) ⟨15812, by rfl⟩ (by norm_num))
theorem R84337 : Reach 84337 := rs (se 2 (by rfl) ⟨31626, by rfl⟩) (B 63253 (by norm_num) ⟨31626, by rfl⟩ (by norm_num))
theorem R84341 : Reach 84341 := rs (se 5 (by rfl) ⟨3953, by rfl⟩) (B 7907 (by norm_num) ⟨3953, by rfl⟩ (by norm_num))
theorem R84345 : Reach 84345 := rs (se 2 (by rfl) ⟨31629, by rfl⟩) (B 63259 (by norm_num) ⟨31629, by rfl⟩ (by norm_num))
theorem R84349 : Reach 84349 := rs (se 3 (by rfl) ⟨15815, by rfl⟩) (B 31631 (by norm_num) ⟨15815, by rfl⟩ (by norm_num))
theorem R84353 : Reach 84353 := rs (se 2 (by rfl) ⟨31632, by rfl⟩) (B 63265 (by norm_num) ⟨31632, by rfl⟩ (by norm_num))
theorem R412037 : Reach 412037 := rs (se 4 (by rfl) ⟨38628, by rfl⟩) (B 77257 (by norm_num) ⟨38628, by rfl⟩ (by norm_num))
theorem R84357 : Reach 84357 := rs (se 4 (by rfl) ⟨7908, by rfl⟩) (B 15817 (by norm_num) ⟨7908, by rfl⟩ (by norm_num))
theorem R84361 : Reach 84361 := rs (se 2 (by rfl) ⟨31635, by rfl⟩) (B 63271 (by norm_num) ⟨31635, by rfl⟩ (by norm_num))
theorem R84365 : Reach 84365 := rs (se 3 (by rfl) ⟨15818, by rfl⟩) (B 31637 (by norm_num) ⟨15818, by rfl⟩ (by norm_num))
theorem R84369 : Reach 84369 := rs (se 2 (by rfl) ⟨31638, by rfl⟩) (B 63277 (by norm_num) ⟨31638, by rfl⟩ (by norm_num))
theorem R84373 : Reach 84373 := rs (se 6 (by rfl) ⟨1977, by rfl⟩) (B 3955 (by norm_num) ⟨1977, by rfl⟩ (by norm_num))
theorem R84377 : Reach 84377 := rs (se 2 (by rfl) ⟨31641, by rfl⟩) (B 63283 (by norm_num) ⟨31641, by rfl⟩ (by norm_num))
theorem R84381 : Reach 84381 := rs (se 3 (by rfl) ⟨15821, by rfl⟩) (B 31643 (by norm_num) ⟨15821, by rfl⟩ (by norm_num))
theorem R84385 : Reach 84385 := rs (se 2 (by rfl) ⟨31644, by rfl⟩) (B 63289 (by norm_num) ⟨31644, by rfl⟩ (by norm_num))
theorem R84389 : Reach 84389 := rs (se 4 (by rfl) ⟨7911, by rfl⟩) (B 15823 (by norm_num) ⟨7911, by rfl⟩ (by norm_num))
theorem R84393 : Reach 84393 := rs (se 2 (by rfl) ⟨31647, by rfl⟩) (B 63295 (by norm_num) ⟨31647, by rfl⟩ (by norm_num))
theorem R84397 : Reach 84397 := rs (se 3 (by rfl) ⟨15824, by rfl⟩) (B 31649 (by norm_num) ⟨15824, by rfl⟩ (by norm_num))
theorem R84401 : Reach 84401 := rs (se 2 (by rfl) ⟨31650, by rfl⟩) (B 63301 (by norm_num) ⟨31650, by rfl⟩ (by norm_num))
theorem R84405 : Reach 84405 := rs (se 5 (by rfl) ⟨3956, by rfl⟩) (B 7913 (by norm_num) ⟨3956, by rfl⟩ (by norm_num))
theorem R117173 : Reach 117173 := rs (se 5 (by rfl) ⟨5492, by rfl⟩) (B 10985 (by norm_num) ⟨5492, by rfl⟩ (by norm_num))
theorem R84409 : Reach 84409 := rs (se 2 (by rfl) ⟨31653, by rfl⟩) (B 63307 (by norm_num) ⟨31653, by rfl⟩ (by norm_num))
theorem R84413 : Reach 84413 := rs (se 3 (by rfl) ⟨15827, by rfl⟩) (B 31655 (by norm_num) ⟨15827, by rfl⟩ (by norm_num))
theorem R84417 : Reach 84417 := rs (se 2 (by rfl) ⟨31656, by rfl⟩) (B 63313 (by norm_num) ⟨31656, by rfl⟩ (by norm_num))
theorem R84421 : Reach 84421 := rs (se 4 (by rfl) ⟨7914, by rfl⟩) (B 15829 (by norm_num) ⟨7914, by rfl⟩ (by norm_num))
theorem R84425 : Reach 84425 := rs (se 2 (by rfl) ⟨31659, by rfl⟩) (B 63319 (by norm_num) ⟨31659, by rfl⟩ (by norm_num))
theorem R84429 : Reach 84429 := rs (se 3 (by rfl) ⟨15830, by rfl⟩) (B 31661 (by norm_num) ⟨15830, by rfl⟩ (by norm_num))
theorem R84433 : Reach 84433 := rs (se 2 (by rfl) ⟨31662, by rfl⟩) (B 63325 (by norm_num) ⟨31662, by rfl⟩ (by norm_num))
theorem R84437 : Reach 84437 := rs (se 7 (by rfl) ⟨989, by rfl⟩) (B 1979 (by norm_num) ⟨989, by rfl⟩ (by norm_num))
theorem R84441 : Reach 84441 := rs (se 2 (by rfl) ⟨31665, by rfl⟩) (B 63331 (by norm_num) ⟨31665, by rfl⟩ (by norm_num))
theorem R84445 : Reach 84445 := rs (se 3 (by rfl) ⟨15833, by rfl⟩) (B 31667 (by norm_num) ⟨15833, by rfl⟩ (by norm_num))
theorem R84449 : Reach 84449 := rs (se 2 (by rfl) ⟨31668, by rfl⟩) (B 63337 (by norm_num) ⟨31668, by rfl⟩ (by norm_num))
theorem R84453 : Reach 84453 := rs (se 4 (by rfl) ⟨7917, by rfl⟩) (B 15835 (by norm_num) ⟨7917, by rfl⟩ (by norm_num))
theorem R84457 : Reach 84457 := rs (se 2 (by rfl) ⟨31671, by rfl⟩) (B 63343 (by norm_num) ⟨31671, by rfl⟩ (by norm_num))
theorem R84461 : Reach 84461 := rs (se 3 (by rfl) ⟨15836, by rfl⟩) (B 31673 (by norm_num) ⟨15836, by rfl⟩ (by norm_num))
theorem R84465 : Reach 84465 := rs (se 2 (by rfl) ⟨31674, by rfl⟩) (B 63349 (by norm_num) ⟨31674, by rfl⟩ (by norm_num))
theorem R84469 : Reach 84469 := rs (se 5 (by rfl) ⟨3959, by rfl⟩) (B 7919 (by norm_num) ⟨3959, by rfl⟩ (by norm_num))
theorem R84473 : Reach 84473 := rs (se 2 (by rfl) ⟨31677, by rfl⟩) (B 63355 (by norm_num) ⟨31677, by rfl⟩ (by norm_num))
theorem R84477 : Reach 84477 := rs (se 3 (by rfl) ⟨15839, by rfl⟩) (B 31679 (by norm_num) ⟨15839, by rfl⟩ (by norm_num))
theorem R84481 : Reach 84481 := rs (se 2 (by rfl) ⟨31680, by rfl⟩) (B 63361 (by norm_num) ⟨31680, by rfl⟩ (by norm_num))
theorem R84485 : Reach 84485 := rs (se 4 (by rfl) ⟨7920, by rfl⟩) (B 15841 (by norm_num) ⟨7920, by rfl⟩ (by norm_num))
theorem R84489 : Reach 84489 := rs (se 2 (by rfl) ⟨31683, by rfl⟩) (B 63367 (by norm_num) ⟨31683, by rfl⟩ (by norm_num))
theorem R84493 : Reach 84493 := rs (se 3 (by rfl) ⟨15842, by rfl⟩) (B 31685 (by norm_num) ⟨15842, by rfl⟩ (by norm_num))
theorem R84497 : Reach 84497 := rs (se 2 (by rfl) ⟨31686, by rfl⟩) (B 63373 (by norm_num) ⟨31686, by rfl⟩ (by norm_num))
theorem R84501 : Reach 84501 := rs (se 6 (by rfl) ⟨1980, by rfl⟩) (B 3961 (by norm_num) ⟨1980, by rfl⟩ (by norm_num))
theorem R84505 : Reach 84505 := rs (se 2 (by rfl) ⟨31689, by rfl⟩) (B 63379 (by norm_num) ⟨31689, by rfl⟩ (by norm_num))
theorem R84509 : Reach 84509 := rs (se 3 (by rfl) ⟨15845, by rfl⟩) (B 31691 (by norm_num) ⟨15845, by rfl⟩ (by norm_num))
theorem R215581 : Reach 215581 := rs (se 3 (by rfl) ⟨40421, by rfl⟩) (B 80843 (by norm_num) ⟨40421, by rfl⟩ (by norm_num))
theorem R84513 : Reach 84513 := rs (se 2 (by rfl) ⟨31692, by rfl⟩) (B 63385 (by norm_num) ⟨31692, by rfl⟩ (by norm_num))
theorem R84517 : Reach 84517 := rs (se 4 (by rfl) ⟨7923, by rfl⟩) (B 15847 (by norm_num) ⟨7923, by rfl⟩ (by norm_num))
theorem R84521 : Reach 84521 := rs (se 2 (by rfl) ⟨31695, by rfl⟩) (B 63391 (by norm_num) ⟨31695, by rfl⟩ (by norm_num))
theorem R84525 : Reach 84525 := rs (se 3 (by rfl) ⟨15848, by rfl⟩) (B 31697 (by norm_num) ⟨15848, by rfl⟩ (by norm_num))
theorem R84529 : Reach 84529 := rs (se 2 (by rfl) ⟨31698, by rfl⟩) (B 63397 (by norm_num) ⟨31698, by rfl⟩ (by norm_num))
theorem R84533 : Reach 84533 := rs (se 5 (by rfl) ⟨3962, by rfl⟩) (B 7925 (by norm_num) ⟨3962, by rfl⟩ (by norm_num))
theorem R182837 : Reach 182837 := rs (se 5 (by rfl) ⟨8570, by rfl⟩) (B 17141 (by norm_num) ⟨8570, by rfl⟩ (by norm_num))
theorem R84537 : Reach 84537 := rs (se 2 (by rfl) ⟨31701, by rfl⟩) (B 63403 (by norm_num) ⟨31701, by rfl⟩ (by norm_num))
theorem R84541 : Reach 84541 := rs (se 3 (by rfl) ⟨15851, by rfl⟩) (B 31703 (by norm_num) ⟨15851, by rfl⟩ (by norm_num))
theorem R84545 : Reach 84545 := rs (se 2 (by rfl) ⟨31704, by rfl⟩) (B 63409 (by norm_num) ⟨31704, by rfl⟩ (by norm_num))
theorem R84549 : Reach 84549 := rs (se 4 (by rfl) ⟨7926, by rfl⟩) (B 15853 (by norm_num) ⟨7926, by rfl⟩ (by norm_num))
theorem R84553 : Reach 84553 := rs (se 2 (by rfl) ⟨31707, by rfl⟩) (B 63415 (by norm_num) ⟨31707, by rfl⟩ (by norm_num))
theorem R84557 : Reach 84557 := rs (se 3 (by rfl) ⟨15854, by rfl⟩) (B 31709 (by norm_num) ⟨15854, by rfl⟩ (by norm_num))
theorem R84561 : Reach 84561 := rs (se 2 (by rfl) ⟨31710, by rfl⟩) (B 63421 (by norm_num) ⟨31710, by rfl⟩ (by norm_num))
theorem R84565 : Reach 84565 := rs (se 8 (by rfl) ⟨495, by rfl⟩) (B 991 (by norm_num) ⟨495, by rfl⟩ (by norm_num))
theorem R84569 : Reach 84569 := rs (se 2 (by rfl) ⟨31713, by rfl⟩) (B 63427 (by norm_num) ⟨31713, by rfl⟩ (by norm_num))
theorem R84573 : Reach 84573 := rs (se 3 (by rfl) ⟨15857, by rfl⟩) (B 31715 (by norm_num) ⟨15857, by rfl⟩ (by norm_num))
theorem R84577 : Reach 84577 := rs (se 2 (by rfl) ⟨31716, by rfl⟩) (B 63433 (by norm_num) ⟨31716, by rfl⟩ (by norm_num))
theorem R84581 : Reach 84581 := rs (se 4 (by rfl) ⟨7929, by rfl⟩) (B 15859 (by norm_num) ⟨7929, by rfl⟩ (by norm_num))
theorem R84585 : Reach 84585 := rs (se 2 (by rfl) ⟨31719, by rfl⟩) (B 63439 (by norm_num) ⟨31719, by rfl⟩ (by norm_num))
theorem R84589 : Reach 84589 := rs (se 3 (by rfl) ⟨15860, by rfl⟩) (B 31721 (by norm_num) ⟨15860, by rfl⟩ (by norm_num))
theorem R84593 : Reach 84593 := rs (se 2 (by rfl) ⟨31722, by rfl⟩) (B 63445 (by norm_num) ⟨31722, by rfl⟩ (by norm_num))
theorem R84597 : Reach 84597 := rs (se 5 (by rfl) ⟨3965, by rfl⟩) (B 7931 (by norm_num) ⟨3965, by rfl⟩ (by norm_num))
theorem R84601 : Reach 84601 := rs (se 2 (by rfl) ⟨31725, by rfl⟩) (B 63451 (by norm_num) ⟨31725, by rfl⟩ (by norm_num))
theorem R84605 : Reach 84605 := rs (se 3 (by rfl) ⟨15863, by rfl⟩) (B 31727 (by norm_num) ⟨15863, by rfl⟩ (by norm_num))
theorem R84609 : Reach 84609 := rs (se 2 (by rfl) ⟨31728, by rfl⟩) (B 63457 (by norm_num) ⟨31728, by rfl⟩ (by norm_num))
theorem R84613 : Reach 84613 := rs (se 4 (by rfl) ⟨7932, by rfl⟩) (B 15865 (by norm_num) ⟨7932, by rfl⟩ (by norm_num))
theorem R84617 : Reach 84617 := rs (se 2 (by rfl) ⟨31731, by rfl⟩) (B 63463 (by norm_num) ⟨31731, by rfl⟩ (by norm_num))
theorem R84621 : Reach 84621 := rs (se 3 (by rfl) ⟨15866, by rfl⟩) (B 31733 (by norm_num) ⟨15866, by rfl⟩ (by norm_num))
theorem R215693 : Reach 215693 := rs (se 3 (by rfl) ⟨40442, by rfl⟩) (B 80885 (by norm_num) ⟨40442, by rfl⟩ (by norm_num))
theorem R84625 : Reach 84625 := rs (se 2 (by rfl) ⟨31734, by rfl⟩) (B 63469 (by norm_num) ⟨31734, by rfl⟩ (by norm_num))
theorem R84629 : Reach 84629 := rs (se 6 (by rfl) ⟨1983, by rfl⟩) (B 3967 (by norm_num) ⟨1983, by rfl⟩ (by norm_num))
theorem R84633 : Reach 84633 := rs (se 2 (by rfl) ⟨31737, by rfl⟩) (B 63475 (by norm_num) ⟨31737, by rfl⟩ (by norm_num))
theorem R84637 : Reach 84637 := rs (se 3 (by rfl) ⟨15869, by rfl⟩) (B 31739 (by norm_num) ⟨15869, by rfl⟩ (by norm_num))
theorem R84641 : Reach 84641 := rs (se 2 (by rfl) ⟨31740, by rfl⟩) (B 63481 (by norm_num) ⟨31740, by rfl⟩ (by norm_num))
theorem R84645 : Reach 84645 := rs (se 4 (by rfl) ⟨7935, by rfl⟩) (B 15871 (by norm_num) ⟨7935, by rfl⟩ (by norm_num))
theorem R84649 : Reach 84649 := rs (se 2 (by rfl) ⟨31743, by rfl⟩) (B 63487 (by norm_num) ⟨31743, by rfl⟩ (by norm_num))
theorem R84653 : Reach 84653 := rs (se 3 (by rfl) ⟨15872, by rfl⟩) (B 31745 (by norm_num) ⟨15872, by rfl⟩ (by norm_num))
theorem R84657 : Reach 84657 := rs (se 2 (by rfl) ⟨31746, by rfl⟩) (B 63493 (by norm_num) ⟨31746, by rfl⟩ (by norm_num))
theorem R84661 : Reach 84661 := rs (se 5 (by rfl) ⟨3968, by rfl⟩) (B 7937 (by norm_num) ⟨3968, by rfl⟩ (by norm_num))
theorem R84665 : Reach 84665 := rs (se 2 (by rfl) ⟨31749, by rfl⟩) (B 63499 (by norm_num) ⟨31749, by rfl⟩ (by norm_num))
theorem R84669 : Reach 84669 := rs (se 3 (by rfl) ⟨15875, by rfl⟩) (B 31751 (by norm_num) ⟨15875, by rfl⟩ (by norm_num))
theorem R84673 : Reach 84673 := rs (se 2 (by rfl) ⟨31752, by rfl⟩) (B 63505 (by norm_num) ⟨31752, by rfl⟩ (by norm_num))
theorem R281285 : Reach 281285 := rs (se 4 (by rfl) ⟨26370, by rfl⟩) (B 52741 (by norm_num) ⟨26370, by rfl⟩ (by norm_num))
theorem R84677 : Reach 84677 := rs (se 4 (by rfl) ⟨7938, by rfl⟩) (B 15877 (by norm_num) ⟨7938, by rfl⟩ (by norm_num))
theorem R84681 : Reach 84681 := rs (se 2 (by rfl) ⟨31755, by rfl⟩) (B 63511 (by norm_num) ⟨31755, by rfl⟩ (by norm_num))
theorem R84685 : Reach 84685 := rs (se 3 (by rfl) ⟨15878, by rfl⟩) (B 31757 (by norm_num) ⟨15878, by rfl⟩ (by norm_num))
theorem R84689 : Reach 84689 := rs (se 2 (by rfl) ⟨31758, by rfl⟩) (B 63517 (by norm_num) ⟨31758, by rfl⟩ (by norm_num))
theorem R84693 : Reach 84693 := rs (se 7 (by rfl) ⟨992, by rfl⟩) (B 1985 (by norm_num) ⟨992, by rfl⟩ (by norm_num))
theorem R84697 : Reach 84697 := rs (se 2 (by rfl) ⟨31761, by rfl⟩) (B 63523 (by norm_num) ⟨31761, by rfl⟩ (by norm_num))
theorem R84701 : Reach 84701 := rs (se 3 (by rfl) ⟨15881, by rfl⟩) (B 31763 (by norm_num) ⟨15881, by rfl⟩ (by norm_num))
theorem R84705 : Reach 84705 := rs (se 2 (by rfl) ⟨31764, by rfl⟩) (B 63529 (by norm_num) ⟨31764, by rfl⟩ (by norm_num))
theorem R84709 : Reach 84709 := rs (se 4 (by rfl) ⟨7941, by rfl⟩) (B 15883 (by norm_num) ⟨7941, by rfl⟩ (by norm_num))
theorem R84713 : Reach 84713 := rs (se 2 (by rfl) ⟨31767, by rfl⟩) (B 63535 (by norm_num) ⟨31767, by rfl⟩ (by norm_num))
theorem R84717 : Reach 84717 := rs (se 3 (by rfl) ⟨15884, by rfl⟩) (B 31769 (by norm_num) ⟨15884, by rfl⟩ (by norm_num))
theorem R84721 : Reach 84721 := rs (se 2 (by rfl) ⟨31770, by rfl⟩) (B 63541 (by norm_num) ⟨31770, by rfl⟩ (by norm_num))
theorem R84725 : Reach 84725 := rs (se 5 (by rfl) ⟨3971, by rfl⟩) (B 7943 (by norm_num) ⟨3971, by rfl⟩ (by norm_num))
theorem R84729 : Reach 84729 := rs (se 2 (by rfl) ⟨31773, by rfl⟩) (B 63547 (by norm_num) ⟨31773, by rfl⟩ (by norm_num))
theorem R84733 : Reach 84733 := rs (se 3 (by rfl) ⟨15887, by rfl⟩) (B 31775 (by norm_num) ⟨15887, by rfl⟩ (by norm_num))
theorem R84737 : Reach 84737 := rs (se 2 (by rfl) ⟨31776, by rfl⟩) (B 63553 (by norm_num) ⟨31776, by rfl⟩ (by norm_num))
theorem R84741 : Reach 84741 := rs (se 4 (by rfl) ⟨7944, by rfl⟩) (B 15889 (by norm_num) ⟨7944, by rfl⟩ (by norm_num))
theorem R84745 : Reach 84745 := rs (se 2 (by rfl) ⟨31779, by rfl⟩) (B 63559 (by norm_num) ⟨31779, by rfl⟩ (by norm_num))
theorem R84749 : Reach 84749 := rs (se 3 (by rfl) ⟨15890, by rfl⟩) (B 31781 (by norm_num) ⟨15890, by rfl⟩ (by norm_num))
theorem R84753 : Reach 84753 := rs (se 2 (by rfl) ⟨31782, by rfl⟩) (B 63565 (by norm_num) ⟨31782, by rfl⟩ (by norm_num))
theorem R84757 : Reach 84757 := rs (se 6 (by rfl) ⟨1986, by rfl⟩) (B 3973 (by norm_num) ⟨1986, by rfl⟩ (by norm_num))
theorem R84761 : Reach 84761 := rs (se 2 (by rfl) ⟨31785, by rfl⟩) (B 63571 (by norm_num) ⟨31785, by rfl⟩ (by norm_num))
theorem R84765 : Reach 84765 := rs (se 3 (by rfl) ⟨15893, by rfl⟩) (B 31787 (by norm_num) ⟨15893, by rfl⟩ (by norm_num))
theorem R84769 : Reach 84769 := rs (se 2 (by rfl) ⟨31788, by rfl⟩) (B 63577 (by norm_num) ⟨31788, by rfl⟩ (by norm_num))
theorem R84773 : Reach 84773 := rs (se 4 (by rfl) ⟨7947, by rfl⟩) (B 15895 (by norm_num) ⟨7947, by rfl⟩ (by norm_num))
theorem R84777 : Reach 84777 := rs (se 2 (by rfl) ⟨31791, by rfl⟩) (B 63583 (by norm_num) ⟨31791, by rfl⟩ (by norm_num))
theorem R84781 : Reach 84781 := rs (se 3 (by rfl) ⟨15896, by rfl⟩) (B 31793 (by norm_num) ⟨15896, by rfl⟩ (by norm_num))
theorem R84785 : Reach 84785 := rs (se 2 (by rfl) ⟨31794, by rfl⟩) (B 63589 (by norm_num) ⟨31794, by rfl⟩ (by norm_num))
theorem R84789 : Reach 84789 := rs (se 5 (by rfl) ⟨3974, by rfl⟩) (B 7949 (by norm_num) ⟨3974, by rfl⟩ (by norm_num))
theorem R84793 : Reach 84793 := rs (se 2 (by rfl) ⟨31797, by rfl⟩) (B 63595 (by norm_num) ⟨31797, by rfl⟩ (by norm_num))
theorem R84797 : Reach 84797 := rs (se 3 (by rfl) ⟨15899, by rfl⟩) (B 31799 (by norm_num) ⟨15899, by rfl⟩ (by norm_num))
theorem R84801 : Reach 84801 := rs (se 2 (by rfl) ⟨31800, by rfl⟩) (B 63601 (by norm_num) ⟨31800, by rfl⟩ (by norm_num))
theorem R84805 : Reach 84805 := rs (se 4 (by rfl) ⟨7950, by rfl⟩) (B 15901 (by norm_num) ⟨7950, by rfl⟩ (by norm_num))
theorem R84809 : Reach 84809 := rs (se 2 (by rfl) ⟨31803, by rfl⟩) (B 63607 (by norm_num) ⟨31803, by rfl⟩ (by norm_num))
theorem R150349 : Reach 150349 := rs (se 3 (by rfl) ⟨28190, by rfl⟩) (B 56381 (by norm_num) ⟨28190, by rfl⟩ (by norm_num))
theorem R84813 : Reach 84813 := rs (se 3 (by rfl) ⟨15902, by rfl⟩) (B 31805 (by norm_num) ⟨15902, by rfl⟩ (by norm_num))
theorem R215885 : Reach 215885 := rs (se 3 (by rfl) ⟨40478, by rfl⟩) (B 80957 (by norm_num) ⟨40478, by rfl⟩ (by norm_num))
theorem R84817 : Reach 84817 := rs (se 2 (by rfl) ⟨31806, by rfl⟩) (B 63613 (by norm_num) ⟨31806, by rfl⟩ (by norm_num))
theorem R84821 : Reach 84821 := rs (se 9 (by rfl) ⟨248, by rfl⟩) (B 497 (by norm_num) ⟨248, by rfl⟩ (by norm_num))
theorem R84825 : Reach 84825 := rs (se 2 (by rfl) ⟨31809, by rfl⟩) (B 63619 (by norm_num) ⟨31809, by rfl⟩ (by norm_num))
theorem R84829 : Reach 84829 := rs (se 3 (by rfl) ⟨15905, by rfl⟩) (B 31811 (by norm_num) ⟨15905, by rfl⟩ (by norm_num))
theorem R84833 : Reach 84833 := rs (se 2 (by rfl) ⟨31812, by rfl⟩) (B 63625 (by norm_num) ⟨31812, by rfl⟩ (by norm_num))
theorem R84837 : Reach 84837 := rs (se 4 (by rfl) ⟨7953, by rfl⟩) (B 15907 (by norm_num) ⟨7953, by rfl⟩ (by norm_num))
theorem R84841 : Reach 84841 := rs (se 2 (by rfl) ⟨31815, by rfl⟩) (B 63631 (by norm_num) ⟨31815, by rfl⟩ (by norm_num))
theorem R84845 : Reach 84845 := rs (se 3 (by rfl) ⟨15908, by rfl⟩) (B 31817 (by norm_num) ⟨15908, by rfl⟩ (by norm_num))
theorem R84849 : Reach 84849 := rs (se 2 (by rfl) ⟨31818, by rfl⟩) (B 63637 (by norm_num) ⟨31818, by rfl⟩ (by norm_num))
theorem R84853 : Reach 84853 := rs (se 5 (by rfl) ⟨3977, by rfl⟩) (B 7955 (by norm_num) ⟨3977, by rfl⟩ (by norm_num))
theorem R84857 : Reach 84857 := rs (se 2 (by rfl) ⟨31821, by rfl⟩) (B 63643 (by norm_num) ⟨31821, by rfl⟩ (by norm_num))
theorem R84861 : Reach 84861 := rs (se 3 (by rfl) ⟨15911, by rfl⟩) (B 31823 (by norm_num) ⟨15911, by rfl⟩ (by norm_num))
theorem R84865 : Reach 84865 := rs (se 2 (by rfl) ⟨31824, by rfl⟩) (B 63649 (by norm_num) ⟨31824, by rfl⟩ (by norm_num))
theorem R84869 : Reach 84869 := rs (se 4 (by rfl) ⟨7956, by rfl⟩) (B 15913 (by norm_num) ⟨7956, by rfl⟩ (by norm_num))
theorem R84873 : Reach 84873 := rs (se 2 (by rfl) ⟨31827, by rfl⟩) (B 63655 (by norm_num) ⟨31827, by rfl⟩ (by norm_num))
theorem R84877 : Reach 84877 := rs (se 3 (by rfl) ⟨15914, by rfl⟩) (B 31829 (by norm_num) ⟨15914, by rfl⟩ (by norm_num))
theorem R84881 : Reach 84881 := rs (se 2 (by rfl) ⟨31830, by rfl⟩) (B 63661 (by norm_num) ⟨31830, by rfl⟩ (by norm_num))
theorem R84885 : Reach 84885 := rs (se 6 (by rfl) ⟨1989, by rfl⟩) (B 3979 (by norm_num) ⟨1989, by rfl⟩ (by norm_num))
theorem R84889 : Reach 84889 := rs (se 2 (by rfl) ⟨31833, by rfl⟩) (B 63667 (by norm_num) ⟨31833, by rfl⟩ (by norm_num))
theorem R84893 : Reach 84893 := rs (se 3 (by rfl) ⟨15917, by rfl⟩) (B 31835 (by norm_num) ⟨15917, by rfl⟩ (by norm_num))
theorem R84897 : Reach 84897 := rs (se 2 (by rfl) ⟨31836, by rfl⟩) (B 63673 (by norm_num) ⟨31836, by rfl⟩ (by norm_num))
theorem R84901 : Reach 84901 := rs (se 4 (by rfl) ⟨7959, by rfl⟩) (B 15919 (by norm_num) ⟨7959, by rfl⟩ (by norm_num))
theorem R84905 : Reach 84905 := rs (se 2 (by rfl) ⟨31839, by rfl⟩) (B 63679 (by norm_num) ⟨31839, by rfl⟩ (by norm_num))
theorem R84909 : Reach 84909 := rs (se 3 (by rfl) ⟨15920, by rfl⟩) (B 31841 (by norm_num) ⟨15920, by rfl⟩ (by norm_num))
theorem R84913 : Reach 84913 := rs (se 2 (by rfl) ⟨31842, by rfl⟩) (B 63685 (by norm_num) ⟨31842, by rfl⟩ (by norm_num))
theorem R478133 : Reach 478133 := rs (se 5 (by rfl) ⟨22412, by rfl⟩) (B 44825 (by norm_num) ⟨22412, by rfl⟩ (by norm_num))
theorem R84917 : Reach 84917 := rs (se 5 (by rfl) ⟨3980, by rfl⟩) (B 7961 (by norm_num) ⟨3980, by rfl⟩ (by norm_num))
theorem R84921 : Reach 84921 := rs (se 2 (by rfl) ⟨31845, by rfl⟩) (B 63691 (by norm_num) ⟨31845, by rfl⟩ (by norm_num))
theorem R84925 : Reach 84925 := rs (se 3 (by rfl) ⟨15923, by rfl⟩) (B 31847 (by norm_num) ⟨15923, by rfl⟩ (by norm_num))
theorem R84929 : Reach 84929 := rs (se 2 (by rfl) ⟨31848, by rfl⟩) (B 63697 (by norm_num) ⟨31848, by rfl⟩ (by norm_num))
theorem R84933 : Reach 84933 := rs (se 4 (by rfl) ⟨7962, by rfl⟩) (B 15925 (by norm_num) ⟨7962, by rfl⟩ (by norm_num))
theorem R84937 : Reach 84937 := rs (se 2 (by rfl) ⟨31851, by rfl⟩) (B 63703 (by norm_num) ⟨31851, by rfl⟩ (by norm_num))
theorem R84941 : Reach 84941 := rs (se 3 (by rfl) ⟨15926, by rfl⟩) (B 31853 (by norm_num) ⟨15926, by rfl⟩ (by norm_num))
theorem R84945 : Reach 84945 := rs (se 2 (by rfl) ⟨31854, by rfl⟩) (B 63709 (by norm_num) ⟨31854, by rfl⟩ (by norm_num))
theorem R642005 : Reach 642005 := rs (se 7 (by rfl) ⟨7523, by rfl⟩) (B 15047 (by norm_num) ⟨7523, by rfl⟩ (by norm_num))
theorem R84949 : Reach 84949 := rs (se 7 (by rfl) ⟨995, by rfl⟩) (B 1991 (by norm_num) ⟨995, by rfl⟩ (by norm_num))
theorem R84953 : Reach 84953 := rs (se 2 (by rfl) ⟨31857, by rfl⟩) (B 63715 (by norm_num) ⟨31857, by rfl⟩ (by norm_num))
theorem R84957 : Reach 84957 := rs (se 3 (by rfl) ⟨15929, by rfl⟩) (B 31859 (by norm_num) ⟨15929, by rfl⟩ (by norm_num))
theorem R84961 : Reach 84961 := rs (se 2 (by rfl) ⟨31860, by rfl⟩) (B 63721 (by norm_num) ⟨31860, by rfl⟩ (by norm_num))
theorem R84965 : Reach 84965 := rs (se 4 (by rfl) ⟨7965, by rfl⟩) (B 15931 (by norm_num) ⟨7965, by rfl⟩ (by norm_num))
theorem R84969 : Reach 84969 := rs (se 2 (by rfl) ⟨31863, by rfl⟩) (B 63727 (by norm_num) ⟨31863, by rfl⟩ (by norm_num))
theorem R84973 : Reach 84973 := rs (se 3 (by rfl) ⟨15932, by rfl⟩) (B 31865 (by norm_num) ⟨15932, by rfl⟩ (by norm_num))
theorem R84977 : Reach 84977 := rs (se 2 (by rfl) ⟨31866, by rfl⟩) (B 63733 (by norm_num) ⟨31866, by rfl⟩ (by norm_num))
theorem R84981 : Reach 84981 := rs (se 5 (by rfl) ⟨3983, by rfl⟩) (B 7967 (by norm_num) ⟨3983, by rfl⟩ (by norm_num))
theorem R84985 : Reach 84985 := rs (se 2 (by rfl) ⟨31869, by rfl⟩) (B 63739 (by norm_num) ⟨31869, by rfl⟩ (by norm_num))
theorem R84989 : Reach 84989 := rs (se 3 (by rfl) ⟨15935, by rfl⟩) (B 31871 (by norm_num) ⟨15935, by rfl⟩ (by norm_num))
theorem R84993 : Reach 84993 := rs (se 2 (by rfl) ⟨31872, by rfl⟩) (B 63745 (by norm_num) ⟨31872, by rfl⟩ (by norm_num))
theorem R84997 : Reach 84997 := rs (se 4 (by rfl) ⟨7968, by rfl⟩) (B 15937 (by norm_num) ⟨7968, by rfl⟩ (by norm_num))
theorem R85001 : Reach 85001 := rs (se 2 (by rfl) ⟨31875, by rfl⟩) (B 63751 (by norm_num) ⟨31875, by rfl⟩ (by norm_num))
theorem R85005 : Reach 85005 := rs (se 3 (by rfl) ⟨15938, by rfl⟩) (B 31877 (by norm_num) ⟨15938, by rfl⟩ (by norm_num))
theorem R85009 : Reach 85009 := rs (se 2 (by rfl) ⟨31878, by rfl⟩) (B 63757 (by norm_num) ⟨31878, by rfl⟩ (by norm_num))
theorem R85013 : Reach 85013 := rs (se 6 (by rfl) ⟨1992, by rfl⟩) (B 3985 (by norm_num) ⟨1992, by rfl⟩ (by norm_num))
theorem R85017 : Reach 85017 := rs (se 2 (by rfl) ⟨31881, by rfl⟩) (B 63763 (by norm_num) ⟨31881, by rfl⟩ (by norm_num))
theorem R85021 : Reach 85021 := rs (se 3 (by rfl) ⟨15941, by rfl⟩) (B 31883 (by norm_num) ⟨15941, by rfl⟩ (by norm_num))
theorem R85025 : Reach 85025 := rs (se 2 (by rfl) ⟨31884, by rfl⟩) (B 63769 (by norm_num) ⟨31884, by rfl⟩ (by norm_num))
theorem R85029 : Reach 85029 := rs (se 4 (by rfl) ⟨7971, by rfl⟩) (B 15943 (by norm_num) ⟨7971, by rfl⟩ (by norm_num))
theorem R85033 : Reach 85033 := rs (se 2 (by rfl) ⟨31887, by rfl⟩) (B 63775 (by norm_num) ⟨31887, by rfl⟩ (by norm_num))
theorem R85037 : Reach 85037 := rs (se 3 (by rfl) ⟨15944, by rfl⟩) (B 31889 (by norm_num) ⟨15944, by rfl⟩ (by norm_num))
theorem R85041 : Reach 85041 := rs (se 2 (by rfl) ⟨31890, by rfl⟩) (B 63781 (by norm_num) ⟨31890, by rfl⟩ (by norm_num))
theorem R85045 : Reach 85045 := rs (se 5 (by rfl) ⟨3986, by rfl⟩) (B 7973 (by norm_num) ⟨3986, by rfl⟩ (by norm_num))
theorem R85049 : Reach 85049 := rs (se 2 (by rfl) ⟨31893, by rfl⟩) (B 63787 (by norm_num) ⟨31893, by rfl⟩ (by norm_num))
theorem R85053 : Reach 85053 := rs (se 3 (by rfl) ⟨15947, by rfl⟩) (B 31895 (by norm_num) ⟨15947, by rfl⟩ (by norm_num))
theorem R85057 : Reach 85057 := rs (se 2 (by rfl) ⟨31896, by rfl⟩) (B 63793 (by norm_num) ⟨31896, by rfl⟩ (by norm_num))
theorem R85061 : Reach 85061 := rs (se 4 (by rfl) ⟨7974, by rfl⟩) (B 15949 (by norm_num) ⟨7974, by rfl⟩ (by norm_num))
theorem R85065 : Reach 85065 := rs (se 2 (by rfl) ⟨31899, by rfl⟩) (B 63799 (by norm_num) ⟨31899, by rfl⟩ (by norm_num))
theorem R85069 : Reach 85069 := rs (se 3 (by rfl) ⟨15950, by rfl⟩) (B 31901 (by norm_num) ⟨15950, by rfl⟩ (by norm_num))
theorem R85073 : Reach 85073 := rs (se 2 (by rfl) ⟨31902, by rfl⟩) (B 63805 (by norm_num) ⟨31902, by rfl⟩ (by norm_num))
theorem R85077 : Reach 85077 := rs (se 8 (by rfl) ⟨498, by rfl⟩) (B 997 (by norm_num) ⟨498, by rfl⟩ (by norm_num))
theorem R85081 : Reach 85081 := rs (se 2 (by rfl) ⟨31905, by rfl⟩) (B 63811 (by norm_num) ⟨31905, by rfl⟩ (by norm_num))
theorem R85085 : Reach 85085 := rs (se 3 (by rfl) ⟨15953, by rfl⟩) (B 31907 (by norm_num) ⟨15953, by rfl⟩ (by norm_num))
theorem R85089 : Reach 85089 := rs (se 2 (by rfl) ⟨31908, by rfl⟩) (B 63817 (by norm_num) ⟨31908, by rfl⟩ (by norm_num))
theorem R85093 : Reach 85093 := rs (se 4 (by rfl) ⟨7977, by rfl⟩) (B 15955 (by norm_num) ⟨7977, by rfl⟩ (by norm_num))
theorem R85097 : Reach 85097 := rs (se 2 (by rfl) ⟨31911, by rfl⟩) (B 63823 (by norm_num) ⟨31911, by rfl⟩ (by norm_num))
theorem R85101 : Reach 85101 := rs (se 3 (by rfl) ⟨15956, by rfl⟩) (B 31913 (by norm_num) ⟨15956, by rfl⟩ (by norm_num))
theorem R85105 : Reach 85105 := rs (se 2 (by rfl) ⟨31914, by rfl⟩) (B 63829 (by norm_num) ⟨31914, by rfl⟩ (by norm_num))
theorem R281717 : Reach 281717 := rs (se 5 (by rfl) ⟨13205, by rfl⟩) (B 26411 (by norm_num) ⟨13205, by rfl⟩ (by norm_num))
theorem R85109 : Reach 85109 := rs (se 5 (by rfl) ⟨3989, by rfl⟩) (B 7979 (by norm_num) ⟨3989, by rfl⟩ (by norm_num))
theorem R85113 : Reach 85113 := rs (se 2 (by rfl) ⟨31917, by rfl⟩) (B 63835 (by norm_num) ⟨31917, by rfl⟩ (by norm_num))
theorem R85117 : Reach 85117 := rs (se 3 (by rfl) ⟨15959, by rfl⟩) (B 31919 (by norm_num) ⟨15959, by rfl⟩ (by norm_num))
theorem R85121 : Reach 85121 := rs (se 2 (by rfl) ⟨31920, by rfl⟩) (B 63841 (by norm_num) ⟨31920, by rfl⟩ (by norm_num))
theorem R85125 : Reach 85125 := rs (se 4 (by rfl) ⟨7980, by rfl⟩) (B 15961 (by norm_num) ⟨7980, by rfl⟩ (by norm_num))
theorem R85129 : Reach 85129 := rs (se 2 (by rfl) ⟨31923, by rfl⟩) (B 63847 (by norm_num) ⟨31923, by rfl⟩ (by norm_num))
theorem R85133 : Reach 85133 := rs (se 3 (by rfl) ⟨15962, by rfl⟩) (B 31925 (by norm_num) ⟨15962, by rfl⟩ (by norm_num))
theorem R85137 : Reach 85137 := rs (se 2 (by rfl) ⟨31926, by rfl⟩) (B 63853 (by norm_num) ⟨31926, by rfl⟩ (by norm_num))
theorem R85141 : Reach 85141 := rs (se 6 (by rfl) ⟨1995, by rfl⟩) (B 3991 (by norm_num) ⟨1995, by rfl⟩ (by norm_num))
theorem R85145 : Reach 85145 := rs (se 2 (by rfl) ⟨31929, by rfl⟩) (B 63859 (by norm_num) ⟨31929, by rfl⟩ (by norm_num))
theorem R85149 : Reach 85149 := rs (se 3 (by rfl) ⟨15965, by rfl⟩) (B 31931 (by norm_num) ⟨15965, by rfl⟩ (by norm_num))
theorem R85153 : Reach 85153 := rs (se 2 (by rfl) ⟨31932, by rfl⟩) (B 63865 (by norm_num) ⟨31932, by rfl⟩ (by norm_num))
theorem R85157 : Reach 85157 := rs (se 4 (by rfl) ⟨7983, by rfl⟩) (B 15967 (by norm_num) ⟨7983, by rfl⟩ (by norm_num))
theorem R216229 : Reach 216229 := rs (se 4 (by rfl) ⟨20271, by rfl⟩) (B 40543 (by norm_num) ⟨20271, by rfl⟩ (by norm_num))
theorem R85161 : Reach 85161 := rs (se 2 (by rfl) ⟨31935, by rfl⟩) (B 63871 (by norm_num) ⟨31935, by rfl⟩ (by norm_num))
theorem R85165 : Reach 85165 := rs (se 3 (by rfl) ⟨15968, by rfl⟩) (B 31937 (by norm_num) ⟨15968, by rfl⟩ (by norm_num))
theorem R85169 : Reach 85169 := rs (se 2 (by rfl) ⟨31938, by rfl⟩) (B 63877 (by norm_num) ⟨31938, by rfl⟩ (by norm_num))
theorem R85173 : Reach 85173 := rs (se 5 (by rfl) ⟨3992, by rfl⟩) (B 7985 (by norm_num) ⟨3992, by rfl⟩ (by norm_num))
theorem R85177 : Reach 85177 := rs (se 2 (by rfl) ⟨31941, by rfl⟩) (B 63883 (by norm_num) ⟨31941, by rfl⟩ (by norm_num))
theorem R85181 : Reach 85181 := rs (se 3 (by rfl) ⟨15971, by rfl⟩) (B 31943 (by norm_num) ⟨15971, by rfl⟩ (by norm_num))
theorem R85185 : Reach 85185 := rs (se 2 (by rfl) ⟨31944, by rfl⟩) (B 63889 (by norm_num) ⟨31944, by rfl⟩ (by norm_num))
theorem R85189 : Reach 85189 := rs (se 4 (by rfl) ⟨7986, by rfl⟩) (B 15973 (by norm_num) ⟨7986, by rfl⟩ (by norm_num))
theorem R85193 : Reach 85193 := rs (se 2 (by rfl) ⟨31947, by rfl⟩) (B 63895 (by norm_num) ⟨31947, by rfl⟩ (by norm_num))
theorem R85197 : Reach 85197 := rs (se 3 (by rfl) ⟨15974, by rfl⟩) (B 31949 (by norm_num) ⟨15974, by rfl⟩ (by norm_num))
theorem R85201 : Reach 85201 := rs (se 2 (by rfl) ⟨31950, by rfl⟩) (B 63901 (by norm_num) ⟨31950, by rfl⟩ (by norm_num))
theorem R85205 : Reach 85205 := rs (se 7 (by rfl) ⟨998, by rfl⟩) (B 1997 (by norm_num) ⟨998, by rfl⟩ (by norm_num))
theorem R85209 : Reach 85209 := rs (se 2 (by rfl) ⟨31953, by rfl⟩) (B 63907 (by norm_num) ⟨31953, by rfl⟩ (by norm_num))
theorem R85213 : Reach 85213 := rs (se 3 (by rfl) ⟨15977, by rfl⟩) (B 31955 (by norm_num) ⟨15977, by rfl⟩ (by norm_num))
theorem R85217 : Reach 85217 := rs (se 2 (by rfl) ⟨31956, by rfl⟩) (B 63913 (by norm_num) ⟨31956, by rfl⟩ (by norm_num))
theorem R85221 : Reach 85221 := rs (se 4 (by rfl) ⟨7989, by rfl⟩) (B 15979 (by norm_num) ⟨7989, by rfl⟩ (by norm_num))
theorem R85225 : Reach 85225 := rs (se 2 (by rfl) ⟨31959, by rfl⟩) (B 63919 (by norm_num) ⟨31959, by rfl⟩ (by norm_num))
theorem R85229 : Reach 85229 := rs (se 3 (by rfl) ⟨15980, by rfl⟩) (B 31961 (by norm_num) ⟨15980, by rfl⟩ (by norm_num))
theorem R85233 : Reach 85233 := rs (se 2 (by rfl) ⟨31962, by rfl⟩) (B 63925 (by norm_num) ⟨31962, by rfl⟩ (by norm_num))
theorem R85237 : Reach 85237 := rs (se 5 (by rfl) ⟨3995, by rfl⟩) (B 7991 (by norm_num) ⟨3995, by rfl⟩ (by norm_num))
theorem R85241 : Reach 85241 := rs (se 2 (by rfl) ⟨31965, by rfl⟩) (B 63931 (by norm_num) ⟨31965, by rfl⟩ (by norm_num))
theorem R85245 : Reach 85245 := rs (se 3 (by rfl) ⟨15983, by rfl⟩) (B 31967 (by norm_num) ⟨15983, by rfl⟩ (by norm_num))
theorem R85249 : Reach 85249 := rs (se 2 (by rfl) ⟨31968, by rfl⟩) (B 63937 (by norm_num) ⟨31968, by rfl⟩ (by norm_num))
theorem R85253 : Reach 85253 := rs (se 4 (by rfl) ⟨7992, by rfl⟩) (B 15985 (by norm_num) ⟨7992, by rfl⟩ (by norm_num))
theorem R85257 : Reach 85257 := rs (se 2 (by rfl) ⟨31971, by rfl⟩) (B 63943 (by norm_num) ⟨31971, by rfl⟩ (by norm_num))
theorem R85261 : Reach 85261 := rs (se 3 (by rfl) ⟨15986, by rfl⟩) (B 31973 (by norm_num) ⟨15986, by rfl⟩ (by norm_num))
theorem R85265 : Reach 85265 := rs (se 2 (by rfl) ⟨31974, by rfl⟩) (B 63949 (by norm_num) ⟨31974, by rfl⟩ (by norm_num))
theorem R85269 : Reach 85269 := rs (se 6 (by rfl) ⟨1998, by rfl⟩) (B 3997 (by norm_num) ⟨1998, by rfl⟩ (by norm_num))
theorem R216341 : Reach 216341 := rs (se 6 (by rfl) ⟨5070, by rfl⟩) (B 10141 (by norm_num) ⟨5070, by rfl⟩ (by norm_num))
theorem R85273 : Reach 85273 := rs (se 2 (by rfl) ⟨31977, by rfl⟩) (B 63955 (by norm_num) ⟨31977, by rfl⟩ (by norm_num))
theorem R85277 : Reach 85277 := rs (se 3 (by rfl) ⟨15989, by rfl⟩) (B 31979 (by norm_num) ⟨15989, by rfl⟩ (by norm_num))
theorem R85281 : Reach 85281 := rs (se 2 (by rfl) ⟨31980, by rfl⟩) (B 63961 (by norm_num) ⟨31980, by rfl⟩ (by norm_num))
theorem R85285 : Reach 85285 := rs (se 4 (by rfl) ⟨7995, by rfl⟩) (B 15991 (by norm_num) ⟨7995, by rfl⟩ (by norm_num))
theorem R85289 : Reach 85289 := rs (se 2 (by rfl) ⟨31983, by rfl⟩) (B 63967 (by norm_num) ⟨31983, by rfl⟩ (by norm_num))
theorem R85293 : Reach 85293 := rs (se 3 (by rfl) ⟨15992, by rfl⟩) (B 31985 (by norm_num) ⟨15992, by rfl⟩ (by norm_num))
theorem R85297 : Reach 85297 := rs (se 2 (by rfl) ⟨31986, by rfl⟩) (B 63973 (by norm_num) ⟨31986, by rfl⟩ (by norm_num))
theorem R85301 : Reach 85301 := rs (se 5 (by rfl) ⟨3998, by rfl⟩) (B 7997 (by norm_num) ⟨3998, by rfl⟩ (by norm_num))
theorem R85305 : Reach 85305 := rs (se 2 (by rfl) ⟨31989, by rfl⟩) (B 63979 (by norm_num) ⟨31989, by rfl⟩ (by norm_num))
theorem R85309 : Reach 85309 := rs (se 3 (by rfl) ⟨15995, by rfl⟩) (B 31991 (by norm_num) ⟨15995, by rfl⟩ (by norm_num))
theorem R85313 : Reach 85313 := rs (se 2 (by rfl) ⟨31992, by rfl⟩) (B 63985 (by norm_num) ⟨31992, by rfl⟩ (by norm_num))
theorem R85317 : Reach 85317 := rs (se 4 (by rfl) ⟨7998, by rfl⟩) (B 15997 (by norm_num) ⟨7998, by rfl⟩ (by norm_num))
theorem R85321 : Reach 85321 := rs (se 2 (by rfl) ⟨31995, by rfl⟩) (B 63991 (by norm_num) ⟨31995, by rfl⟩ (by norm_num))
theorem R85325 : Reach 85325 := rs (se 3 (by rfl) ⟨15998, by rfl⟩) (B 31997 (by norm_num) ⟨15998, by rfl⟩ (by norm_num))
theorem R85329 : Reach 85329 := rs (se 2 (by rfl) ⟨31998, by rfl⟩) (B 63997 (by norm_num) ⟨31998, by rfl⟩ (by norm_num))
theorem R85333 : Reach 85333 := rs (se 11 (by rfl) ⟨62, by rfl⟩) (B 125 (by norm_num) ⟨62, by rfl⟩ (by norm_num))
theorem R85337 : Reach 85337 := rs (se 2 (by rfl) ⟨32001, by rfl⟩) (B 64003 (by norm_num) ⟨32001, by rfl⟩ (by norm_num))
theorem R85341 : Reach 85341 := rs (se 3 (by rfl) ⟨16001, by rfl⟩) (B 32003 (by norm_num) ⟨16001, by rfl⟩ (by norm_num))
theorem R85345 : Reach 85345 := rs (se 2 (by rfl) ⟨32004, by rfl⟩) (B 64009 (by norm_num) ⟨32004, by rfl⟩ (by norm_num))
theorem R85349 : Reach 85349 := rs (se 4 (by rfl) ⟨8001, by rfl⟩) (B 16003 (by norm_num) ⟨8001, by rfl⟩ (by norm_num))
theorem R85353 : Reach 85353 := rs (se 2 (by rfl) ⟨32007, by rfl⟩) (B 64015 (by norm_num) ⟨32007, by rfl⟩ (by norm_num))
theorem R85357 : Reach 85357 := rs (se 3 (by rfl) ⟨16004, by rfl⟩) (B 32009 (by norm_num) ⟨16004, by rfl⟩ (by norm_num))
theorem R85361 : Reach 85361 := rs (se 2 (by rfl) ⟨32010, by rfl⟩) (B 64021 (by norm_num) ⟨32010, by rfl⟩ (by norm_num))
theorem R85365 : Reach 85365 := rs (se 5 (by rfl) ⟨4001, by rfl⟩) (B 8003 (by norm_num) ⟨4001, by rfl⟩ (by norm_num))
theorem R85369 : Reach 85369 := rs (se 2 (by rfl) ⟨32013, by rfl⟩) (B 64027 (by norm_num) ⟨32013, by rfl⟩ (by norm_num))
theorem R85373 : Reach 85373 := rs (se 3 (by rfl) ⟨16007, by rfl⟩) (B 32015 (by norm_num) ⟨16007, by rfl⟩ (by norm_num))
theorem R85377 : Reach 85377 := rs (se 2 (by rfl) ⟨32016, by rfl⟩) (B 64033 (by norm_num) ⟨32016, by rfl⟩ (by norm_num))
theorem R85381 : Reach 85381 := rs (se 4 (by rfl) ⟨8004, by rfl⟩) (B 16009 (by norm_num) ⟨8004, by rfl⟩ (by norm_num))
theorem R85385 : Reach 85385 := rs (se 2 (by rfl) ⟨32019, by rfl⟩) (B 64039 (by norm_num) ⟨32019, by rfl⟩ (by norm_num))
theorem R85389 : Reach 85389 := rs (se 3 (by rfl) ⟨16010, by rfl⟩) (B 32021 (by norm_num) ⟨16010, by rfl⟩ (by norm_num))
theorem R85393 : Reach 85393 := rs (se 2 (by rfl) ⟨32022, by rfl⟩) (B 64045 (by norm_num) ⟨32022, by rfl⟩ (by norm_num))
theorem R85397 : Reach 85397 := rs (se 6 (by rfl) ⟨2001, by rfl⟩) (B 4003 (by norm_num) ⟨2001, by rfl⟩ (by norm_num))
theorem R183701 : Reach 183701 := rs (se 6 (by rfl) ⟨4305, by rfl⟩) (B 8611 (by norm_num) ⟨4305, by rfl⟩ (by norm_num))
theorem R85401 : Reach 85401 := rs (se 2 (by rfl) ⟨32025, by rfl⟩) (B 64051 (by norm_num) ⟨32025, by rfl⟩ (by norm_num))
theorem R85405 : Reach 85405 := rs (se 3 (by rfl) ⟨16013, by rfl⟩) (B 32027 (by norm_num) ⟨16013, by rfl⟩ (by norm_num))
theorem R85409 : Reach 85409 := rs (se 2 (by rfl) ⟨32028, by rfl⟩) (B 64057 (by norm_num) ⟨32028, by rfl⟩ (by norm_num))
theorem R85413 : Reach 85413 := rs (se 4 (by rfl) ⟨8007, by rfl⟩) (B 16015 (by norm_num) ⟨8007, by rfl⟩ (by norm_num))
theorem R85417 : Reach 85417 := rs (se 2 (by rfl) ⟨32031, by rfl⟩) (B 64063 (by norm_num) ⟨32031, by rfl⟩ (by norm_num))
theorem R85421 : Reach 85421 := rs (se 3 (by rfl) ⟨16016, by rfl⟩) (B 32033 (by norm_num) ⟨16016, by rfl⟩ (by norm_num))
theorem R85425 : Reach 85425 := rs (se 2 (by rfl) ⟨32034, by rfl⟩) (B 64069 (by norm_num) ⟨32034, by rfl⟩ (by norm_num))
theorem R85429 : Reach 85429 := rs (se 5 (by rfl) ⟨4004, by rfl⟩) (B 8009 (by norm_num) ⟨4004, by rfl⟩ (by norm_num))
theorem R85433 : Reach 85433 := rs (se 2 (by rfl) ⟨32037, by rfl⟩) (B 64075 (by norm_num) ⟨32037, by rfl⟩ (by norm_num))
theorem R85437 : Reach 85437 := rs (se 3 (by rfl) ⟨16019, by rfl⟩) (B 32039 (by norm_num) ⟨16019, by rfl⟩ (by norm_num))
theorem R85441 : Reach 85441 := rs (se 2 (by rfl) ⟨32040, by rfl⟩) (B 64081 (by norm_num) ⟨32040, by rfl⟩ (by norm_num))
theorem R85445 : Reach 85445 := rs (se 4 (by rfl) ⟨8010, by rfl⟩) (B 16021 (by norm_num) ⟨8010, by rfl⟩ (by norm_num))
theorem R282053 : Reach 282053 := rs (se 4 (by rfl) ⟨26442, by rfl⟩) (B 52885 (by norm_num) ⟨26442, by rfl⟩ (by norm_num))
theorem R85449 : Reach 85449 := rs (se 2 (by rfl) ⟨32043, by rfl⟩) (B 64087 (by norm_num) ⟨32043, by rfl⟩ (by norm_num))
theorem R85453 : Reach 85453 := rs (se 3 (by rfl) ⟨16022, by rfl⟩) (B 32045 (by norm_num) ⟨16022, by rfl⟩ (by norm_num))
theorem R85457 : Reach 85457 := rs (se 2 (by rfl) ⟨32046, by rfl⟩) (B 64093 (by norm_num) ⟨32046, by rfl⟩ (by norm_num))
theorem R85461 : Reach 85461 := rs (se 7 (by rfl) ⟨1001, by rfl⟩) (B 2003 (by norm_num) ⟨1001, by rfl⟩ (by norm_num))
theorem R216533 : Reach 216533 := rs (se 7 (by rfl) ⟨2537, by rfl⟩) (B 5075 (by norm_num) ⟨2537, by rfl⟩ (by norm_num))
theorem R85465 : Reach 85465 := rs (se 2 (by rfl) ⟨32049, by rfl⟩) (B 64099 (by norm_num) ⟨32049, by rfl⟩ (by norm_num))
theorem R85469 : Reach 85469 := rs (se 3 (by rfl) ⟨16025, by rfl⟩) (B 32051 (by norm_num) ⟨16025, by rfl⟩ (by norm_num))
theorem R85473 : Reach 85473 := rs (se 2 (by rfl) ⟨32052, by rfl⟩) (B 64105 (by norm_num) ⟨32052, by rfl⟩ (by norm_num))
theorem R85477 : Reach 85477 := rs (se 4 (by rfl) ⟨8013, by rfl⟩) (B 16027 (by norm_num) ⟨8013, by rfl⟩ (by norm_num))
theorem R85481 : Reach 85481 := rs (se 2 (by rfl) ⟨32055, by rfl⟩) (B 64111 (by norm_num) ⟨32055, by rfl⟩ (by norm_num))
theorem R85485 : Reach 85485 := rs (se 3 (by rfl) ⟨16028, by rfl⟩) (B 32057 (by norm_num) ⟨16028, by rfl⟩ (by norm_num))
theorem R85489 : Reach 85489 := rs (se 2 (by rfl) ⟨32058, by rfl⟩) (B 64117 (by norm_num) ⟨32058, by rfl⟩ (by norm_num))
theorem R85493 : Reach 85493 := rs (se 5 (by rfl) ⟨4007, by rfl⟩) (B 8015 (by norm_num) ⟨4007, by rfl⟩ (by norm_num))
theorem R85497 : Reach 85497 := rs (se 2 (by rfl) ⟨32061, by rfl⟩) (B 64123 (by norm_num) ⟨32061, by rfl⟩ (by norm_num))
theorem R85501 : Reach 85501 := rs (se 3 (by rfl) ⟨16031, by rfl⟩) (B 32063 (by norm_num) ⟨16031, by rfl⟩ (by norm_num))
theorem R85505 : Reach 85505 := rs (se 2 (by rfl) ⟨32064, by rfl⟩) (B 64129 (by norm_num) ⟨32064, by rfl⟩ (by norm_num))
theorem R85509 : Reach 85509 := rs (se 4 (by rfl) ⟨8016, by rfl⟩) (B 16033 (by norm_num) ⟨8016, by rfl⟩ (by norm_num))
theorem R85513 : Reach 85513 := rs (se 2 (by rfl) ⟨32067, by rfl⟩) (B 64135 (by norm_num) ⟨32067, by rfl⟩ (by norm_num))
theorem R85517 : Reach 85517 := rs (se 3 (by rfl) ⟨16034, by rfl⟩) (B 32069 (by norm_num) ⟨16034, by rfl⟩ (by norm_num))
theorem R85521 : Reach 85521 := rs (se 2 (by rfl) ⟨32070, by rfl⟩) (B 64141 (by norm_num) ⟨32070, by rfl⟩ (by norm_num))
theorem R85525 : Reach 85525 := rs (se 6 (by rfl) ⟨2004, by rfl⟩) (B 4009 (by norm_num) ⟨2004, by rfl⟩ (by norm_num))
theorem R85529 : Reach 85529 := rs (se 2 (by rfl) ⟨32073, by rfl⟩) (B 64147 (by norm_num) ⟨32073, by rfl⟩ (by norm_num))
theorem R85533 : Reach 85533 := rs (se 3 (by rfl) ⟨16037, by rfl⟩) (B 32075 (by norm_num) ⟨16037, by rfl⟩ (by norm_num))
theorem R85537 : Reach 85537 := rs (se 2 (by rfl) ⟨32076, by rfl⟩) (B 64153 (by norm_num) ⟨32076, by rfl⟩ (by norm_num))
theorem R282149 : Reach 282149 := rs (se 4 (by rfl) ⟨26451, by rfl⟩) (B 52903 (by norm_num) ⟨26451, by rfl⟩ (by norm_num))
theorem R85541 : Reach 85541 := rs (se 4 (by rfl) ⟨8019, by rfl⟩) (B 16039 (by norm_num) ⟨8019, by rfl⟩ (by norm_num))
theorem R183845 : Reach 183845 := rs (se 4 (by rfl) ⟨17235, by rfl⟩) (B 34471 (by norm_num) ⟨17235, by rfl⟩ (by norm_num))
theorem R85545 : Reach 85545 := rs (se 2 (by rfl) ⟨32079, by rfl⟩) (B 64159 (by norm_num) ⟨32079, by rfl⟩ (by norm_num))
theorem R85549 : Reach 85549 := rs (se 3 (by rfl) ⟨16040, by rfl⟩) (B 32081 (by norm_num) ⟨16040, by rfl⟩ (by norm_num))
theorem R85553 : Reach 85553 := rs (se 2 (by rfl) ⟨32082, by rfl⟩) (B 64165 (by norm_num) ⟨32082, by rfl⟩ (by norm_num))
theorem R85557 : Reach 85557 := rs (se 5 (by rfl) ⟨4010, by rfl⟩) (B 8021 (by norm_num) ⟨4010, by rfl⟩ (by norm_num))
theorem R85561 : Reach 85561 := rs (se 2 (by rfl) ⟨32085, by rfl⟩) (B 64171 (by norm_num) ⟨32085, by rfl⟩ (by norm_num))
theorem R85565 : Reach 85565 := rs (se 3 (by rfl) ⟨16043, by rfl⟩) (B 32087 (by norm_num) ⟨16043, by rfl⟩ (by norm_num))
theorem R85569 : Reach 85569 := rs (se 2 (by rfl) ⟨32088, by rfl⟩) (B 64177 (by norm_num) ⟨32088, by rfl⟩ (by norm_num))
theorem R85573 : Reach 85573 := rs (se 4 (by rfl) ⟨8022, by rfl⟩) (B 16045 (by norm_num) ⟨8022, by rfl⟩ (by norm_num))
theorem R85577 : Reach 85577 := rs (se 2 (by rfl) ⟨32091, by rfl⟩) (B 64183 (by norm_num) ⟨32091, by rfl⟩ (by norm_num))
theorem R85581 : Reach 85581 := rs (se 3 (by rfl) ⟨16046, by rfl⟩) (B 32093 (by norm_num) ⟨16046, by rfl⟩ (by norm_num))
theorem R85585 : Reach 85585 := rs (se 2 (by rfl) ⟨32094, by rfl⟩) (B 64189 (by norm_num) ⟨32094, by rfl⟩ (by norm_num))
theorem R85589 : Reach 85589 := rs (se 8 (by rfl) ⟨501, by rfl⟩) (B 1003 (by norm_num) ⟨501, by rfl⟩ (by norm_num))
theorem R85593 : Reach 85593 := rs (se 2 (by rfl) ⟨32097, by rfl⟩) (B 64195 (by norm_num) ⟨32097, by rfl⟩ (by norm_num))
theorem R85597 : Reach 85597 := rs (se 3 (by rfl) ⟨16049, by rfl⟩) (B 32099 (by norm_num) ⟨16049, by rfl⟩ (by norm_num))
theorem R85601 : Reach 85601 := rs (se 2 (by rfl) ⟨32100, by rfl⟩) (B 64201 (by norm_num) ⟨32100, by rfl⟩ (by norm_num))
theorem R151141 : Reach 151141 := rs (se 4 (by rfl) ⟨14169, by rfl⟩) (B 28339 (by norm_num) ⟨14169, by rfl⟩ (by norm_num))
theorem R85605 : Reach 85605 := rs (se 4 (by rfl) ⟨8025, by rfl⟩) (B 16051 (by norm_num) ⟨8025, by rfl⟩ (by norm_num))
theorem R85609 : Reach 85609 := rs (se 2 (by rfl) ⟨32103, by rfl⟩) (B 64207 (by norm_num) ⟨32103, by rfl⟩ (by norm_num))
theorem R85613 : Reach 85613 := rs (se 3 (by rfl) ⟨16052, by rfl⟩) (B 32105 (by norm_num) ⟨16052, by rfl⟩ (by norm_num))
theorem R85617 : Reach 85617 := rs (se 2 (by rfl) ⟨32106, by rfl⟩) (B 64213 (by norm_num) ⟨32106, by rfl⟩ (by norm_num))
theorem R380533 : Reach 380533 := rs (se 5 (by rfl) ⟨17837, by rfl⟩) (B 35675 (by norm_num) ⟨17837, by rfl⟩ (by norm_num))
theorem R85621 : Reach 85621 := rs (se 5 (by rfl) ⟨4013, by rfl⟩) (B 8027 (by norm_num) ⟨4013, by rfl⟩ (by norm_num))
theorem R85625 : Reach 85625 := rs (se 2 (by rfl) ⟨32109, by rfl⟩) (B 64219 (by norm_num) ⟨32109, by rfl⟩ (by norm_num))
theorem R85629 : Reach 85629 := rs (se 3 (by rfl) ⟨16055, by rfl⟩) (B 32111 (by norm_num) ⟨16055, by rfl⟩ (by norm_num))
theorem R85633 : Reach 85633 := rs (se 2 (by rfl) ⟨32112, by rfl⟩) (B 64225 (by norm_num) ⟨32112, by rfl⟩ (by norm_num))
theorem R85637 : Reach 85637 := rs (se 4 (by rfl) ⟨8028, by rfl⟩) (B 16057 (by norm_num) ⟨8028, by rfl⟩ (by norm_num))
theorem R85641 : Reach 85641 := rs (se 2 (by rfl) ⟨32115, by rfl⟩) (B 64231 (by norm_num) ⟨32115, by rfl⟩ (by norm_num))
theorem R85645 : Reach 85645 := rs (se 3 (by rfl) ⟨16058, by rfl⟩) (B 32117 (by norm_num) ⟨16058, by rfl⟩ (by norm_num))
theorem R85649 : Reach 85649 := rs (se 2 (by rfl) ⟨32118, by rfl⟩) (B 64237 (by norm_num) ⟨32118, by rfl⟩ (by norm_num))
theorem R85653 : Reach 85653 := rs (se 6 (by rfl) ⟨2007, by rfl⟩) (B 4015 (by norm_num) ⟨2007, by rfl⟩ (by norm_num))
theorem R85657 : Reach 85657 := rs (se 2 (by rfl) ⟨32121, by rfl⟩) (B 64243 (by norm_num) ⟨32121, by rfl⟩ (by norm_num))
theorem R85661 : Reach 85661 := rs (se 3 (by rfl) ⟨16061, by rfl⟩) (B 32123 (by norm_num) ⟨16061, by rfl⟩ (by norm_num))
theorem R85665 : Reach 85665 := rs (se 2 (by rfl) ⟨32124, by rfl⟩) (B 64249 (by norm_num) ⟨32124, by rfl⟩ (by norm_num))
theorem R85669 : Reach 85669 := rs (se 4 (by rfl) ⟨8031, by rfl⟩) (B 16063 (by norm_num) ⟨8031, by rfl⟩ (by norm_num))
theorem R85673 : Reach 85673 := rs (se 2 (by rfl) ⟨32127, by rfl⟩) (B 64255 (by norm_num) ⟨32127, by rfl⟩ (by norm_num))
theorem R85677 : Reach 85677 := rs (se 3 (by rfl) ⟨16064, by rfl⟩) (B 32129 (by norm_num) ⟨16064, by rfl⟩ (by norm_num))
theorem R85681 : Reach 85681 := rs (se 2 (by rfl) ⟨32130, by rfl⟩) (B 64261 (by norm_num) ⟨32130, by rfl⟩ (by norm_num))
theorem R85685 : Reach 85685 := rs (se 5 (by rfl) ⟨4016, by rfl⟩) (B 8033 (by norm_num) ⟨4016, by rfl⟩ (by norm_num))
theorem R85689 : Reach 85689 := rs (se 2 (by rfl) ⟨32133, by rfl⟩) (B 64267 (by norm_num) ⟨32133, by rfl⟩ (by norm_num))
theorem R85693 : Reach 85693 := rs (se 3 (by rfl) ⟨16067, by rfl⟩) (B 32135 (by norm_num) ⟨16067, by rfl⟩ (by norm_num))
theorem R85697 : Reach 85697 := rs (se 2 (by rfl) ⟨32136, by rfl⟩) (B 64273 (by norm_num) ⟨32136, by rfl⟩ (by norm_num))
theorem R85701 : Reach 85701 := rs (se 4 (by rfl) ⟨8034, by rfl⟩) (B 16069 (by norm_num) ⟨8034, by rfl⟩ (by norm_num))
theorem R85705 : Reach 85705 := rs (se 2 (by rfl) ⟨32139, by rfl⟩) (B 64279 (by norm_num) ⟨32139, by rfl⟩ (by norm_num))
theorem R85709 : Reach 85709 := rs (se 3 (by rfl) ⟨16070, by rfl⟩) (B 32141 (by norm_num) ⟨16070, by rfl⟩ (by norm_num))
theorem R85713 : Reach 85713 := rs (se 2 (by rfl) ⟨32142, by rfl⟩) (B 64285 (by norm_num) ⟨32142, by rfl⟩ (by norm_num))
theorem R85717 : Reach 85717 := rs (se 7 (by rfl) ⟨1004, by rfl⟩) (B 2009 (by norm_num) ⟨1004, by rfl⟩ (by norm_num))
theorem R85721 : Reach 85721 := rs (se 2 (by rfl) ⟨32145, by rfl⟩) (B 64291 (by norm_num) ⟨32145, by rfl⟩ (by norm_num))
theorem R85725 : Reach 85725 := rs (se 3 (by rfl) ⟨16073, by rfl⟩) (B 32147 (by norm_num) ⟨16073, by rfl⟩ (by norm_num))
theorem R85729 : Reach 85729 := rs (se 2 (by rfl) ⟨32148, by rfl⟩) (B 64297 (by norm_num) ⟨32148, by rfl⟩ (by norm_num))
theorem R85733 : Reach 85733 := rs (se 4 (by rfl) ⟨8037, by rfl⟩) (B 16075 (by norm_num) ⟨8037, by rfl⟩ (by norm_num))
theorem R85737 : Reach 85737 := rs (se 2 (by rfl) ⟨32151, by rfl⟩) (B 64303 (by norm_num) ⟨32151, by rfl⟩ (by norm_num))
theorem R85741 : Reach 85741 := rs (se 3 (by rfl) ⟨16076, by rfl⟩) (B 32153 (by norm_num) ⟨16076, by rfl⟩ (by norm_num))
theorem R85745 : Reach 85745 := rs (se 2 (by rfl) ⟨32154, by rfl⟩) (B 64309 (by norm_num) ⟨32154, by rfl⟩ (by norm_num))
theorem R85749 : Reach 85749 := rs (se 5 (by rfl) ⟨4019, by rfl⟩) (B 8039 (by norm_num) ⟨4019, by rfl⟩ (by norm_num))
theorem R85753 : Reach 85753 := rs (se 2 (by rfl) ⟨32157, by rfl⟩) (B 64315 (by norm_num) ⟨32157, by rfl⟩ (by norm_num))
theorem R85757 : Reach 85757 := rs (se 3 (by rfl) ⟨16079, by rfl⟩) (B 32159 (by norm_num) ⟨16079, by rfl⟩ (by norm_num))
theorem R85761 : Reach 85761 := rs (se 2 (by rfl) ⟨32160, by rfl⟩) (B 64321 (by norm_num) ⟨32160, by rfl⟩ (by norm_num))
theorem R85765 : Reach 85765 := rs (se 4 (by rfl) ⟨8040, by rfl⟩) (B 16081 (by norm_num) ⟨8040, by rfl⟩ (by norm_num))
theorem R85769 : Reach 85769 := rs (se 2 (by rfl) ⟨32163, by rfl⟩) (B 64327 (by norm_num) ⟨32163, by rfl⟩ (by norm_num))
theorem R85773 : Reach 85773 := rs (se 3 (by rfl) ⟨16082, by rfl⟩) (B 32165 (by norm_num) ⟨16082, by rfl⟩ (by norm_num))
theorem R85777 : Reach 85777 := rs (se 2 (by rfl) ⟨32166, by rfl⟩) (B 64333 (by norm_num) ⟨32166, by rfl⟩ (by norm_num))
theorem R85781 : Reach 85781 := rs (se 6 (by rfl) ⟨2010, by rfl⟩) (B 4021 (by norm_num) ⟨2010, by rfl⟩ (by norm_num))
theorem R85785 : Reach 85785 := rs (se 2 (by rfl) ⟨32169, by rfl⟩) (B 64339 (by norm_num) ⟨32169, by rfl⟩ (by norm_num))
theorem R85789 : Reach 85789 := rs (se 3 (by rfl) ⟨16085, by rfl⟩) (B 32171 (by norm_num) ⟨16085, by rfl⟩ (by norm_num))
theorem R85793 : Reach 85793 := rs (se 2 (by rfl) ⟨32172, by rfl⟩) (B 64345 (by norm_num) ⟨32172, by rfl⟩ (by norm_num))
theorem R85797 : Reach 85797 := rs (se 4 (by rfl) ⟨8043, by rfl⟩) (B 16087 (by norm_num) ⟨8043, by rfl⟩ (by norm_num))
theorem R85801 : Reach 85801 := rs (se 2 (by rfl) ⟨32175, by rfl⟩) (B 64351 (by norm_num) ⟨32175, by rfl⟩ (by norm_num))
theorem R216877 : Reach 216877 := rs (se 3 (by rfl) ⟨40664, by rfl⟩) (B 81329 (by norm_num) ⟨40664, by rfl⟩ (by norm_num))
theorem R85805 : Reach 85805 := rs (se 3 (by rfl) ⟨16088, by rfl⟩) (B 32177 (by norm_num) ⟨16088, by rfl⟩ (by norm_num))
theorem R85809 : Reach 85809 := rs (se 2 (by rfl) ⟨32178, by rfl⟩) (B 64357 (by norm_num) ⟨32178, by rfl⟩ (by norm_num))
theorem R85813 : Reach 85813 := rs (se 5 (by rfl) ⟨4022, by rfl⟩) (B 8045 (by norm_num) ⟨4022, by rfl⟩ (by norm_num))
theorem R85817 : Reach 85817 := rs (se 2 (by rfl) ⟨32181, by rfl⟩) (B 64363 (by norm_num) ⟨32181, by rfl⟩ (by norm_num))
theorem R85821 : Reach 85821 := rs (se 3 (by rfl) ⟨16091, by rfl⟩) (B 32183 (by norm_num) ⟨16091, by rfl⟩ (by norm_num))
theorem R85825 : Reach 85825 := rs (se 2 (by rfl) ⟨32184, by rfl⟩) (B 64369 (by norm_num) ⟨32184, by rfl⟩ (by norm_num))
theorem R85829 : Reach 85829 := rs (se 4 (by rfl) ⟨8046, by rfl⟩) (B 16093 (by norm_num) ⟨8046, by rfl⟩ (by norm_num))
theorem R85833 : Reach 85833 := rs (se 2 (by rfl) ⟨32187, by rfl⟩) (B 64375 (by norm_num) ⟨32187, by rfl⟩ (by norm_num))
theorem R85837 : Reach 85837 := rs (se 3 (by rfl) ⟨16094, by rfl⟩) (B 32189 (by norm_num) ⟨16094, by rfl⟩ (by norm_num))
theorem R85841 : Reach 85841 := rs (se 2 (by rfl) ⟨32190, by rfl⟩) (B 64381 (by norm_num) ⟨32190, by rfl⟩ (by norm_num))
theorem R85845 : Reach 85845 := rs (se 9 (by rfl) ⟨251, by rfl⟩) (B 503 (by norm_num) ⟨251, by rfl⟩ (by norm_num))
theorem R2117461 : Reach 2117461 := rs (se 9 (by rfl) ⟨6203, by rfl⟩) (B 12407 (by norm_num) ⟨6203, by rfl⟩ (by norm_num))
theorem R85849 : Reach 85849 := rs (se 2 (by rfl) ⟨32193, by rfl⟩) (B 64387 (by norm_num) ⟨32193, by rfl⟩ (by norm_num))
theorem R85853 : Reach 85853 := rs (se 3 (by rfl) ⟨16097, by rfl⟩) (B 32195 (by norm_num) ⟨16097, by rfl⟩ (by norm_num))
theorem R85857 : Reach 85857 := rs (se 2 (by rfl) ⟨32196, by rfl⟩) (B 64393 (by norm_num) ⟨32196, by rfl⟩ (by norm_num))
theorem R85861 : Reach 85861 := rs (se 4 (by rfl) ⟨8049, by rfl⟩) (B 16099 (by norm_num) ⟨8049, by rfl⟩ (by norm_num))
theorem R85865 : Reach 85865 := rs (se 2 (by rfl) ⟨32199, by rfl⟩) (B 64399 (by norm_num) ⟨32199, by rfl⟩ (by norm_num))
theorem R85869 : Reach 85869 := rs (se 3 (by rfl) ⟨16100, by rfl⟩) (B 32201 (by norm_num) ⟨16100, by rfl⟩ (by norm_num))
theorem R85873 : Reach 85873 := rs (se 2 (by rfl) ⟨32202, by rfl⟩) (B 64405 (by norm_num) ⟨32202, by rfl⟩ (by norm_num))
theorem R85877 : Reach 85877 := rs (se 5 (by rfl) ⟨4025, by rfl⟩) (B 8051 (by norm_num) ⟨4025, by rfl⟩ (by norm_num))
theorem R85881 : Reach 85881 := rs (se 2 (by rfl) ⟨32205, by rfl⟩) (B 64411 (by norm_num) ⟨32205, by rfl⟩ (by norm_num))
theorem R85885 : Reach 85885 := rs (se 3 (by rfl) ⟨16103, by rfl⟩) (B 32207 (by norm_num) ⟨16103, by rfl⟩ (by norm_num))
theorem R85889 : Reach 85889 := rs (se 2 (by rfl) ⟨32208, by rfl⟩) (B 64417 (by norm_num) ⟨32208, by rfl⟩ (by norm_num))
theorem R85893 : Reach 85893 := rs (se 4 (by rfl) ⟨8052, by rfl⟩) (B 16105 (by norm_num) ⟨8052, by rfl⟩ (by norm_num))
theorem R85897 : Reach 85897 := rs (se 2 (by rfl) ⟨32211, by rfl⟩) (B 64423 (by norm_num) ⟨32211, by rfl⟩ (by norm_num))
theorem R85901 : Reach 85901 := rs (se 3 (by rfl) ⟨16106, by rfl⟩) (B 32213 (by norm_num) ⟨16106, by rfl⟩ (by norm_num))
theorem R85905 : Reach 85905 := rs (se 2 (by rfl) ⟨32214, by rfl⟩) (B 64429 (by norm_num) ⟨32214, by rfl⟩ (by norm_num))
theorem R151445 : Reach 151445 := rs (se 6 (by rfl) ⟨3549, by rfl⟩) (B 7099 (by norm_num) ⟨3549, by rfl⟩ (by norm_num))
theorem R85909 : Reach 85909 := rs (se 6 (by rfl) ⟨2013, by rfl⟩) (B 4027 (by norm_num) ⟨2013, by rfl⟩ (by norm_num))
theorem R85913 : Reach 85913 := rs (se 2 (by rfl) ⟨32217, by rfl⟩) (B 64435 (by norm_num) ⟨32217, by rfl⟩ (by norm_num))
theorem R216989 : Reach 216989 := rs (se 3 (by rfl) ⟨40685, by rfl⟩) (B 81371 (by norm_num) ⟨40685, by rfl⟩ (by norm_num))
theorem R118685 : Reach 118685 := rs (se 3 (by rfl) ⟨22253, by rfl⟩) (B 44507 (by norm_num) ⟨22253, by rfl⟩ (by norm_num))
theorem R85921 : Reach 85921 := rs (se 2 (by rfl) ⟨32220, by rfl⟩) (B 64441 (by norm_num) ⟨32220, by rfl⟩ (by norm_num))
theorem R85917 : Reach 85917 := rs (se 3 (by rfl) ⟨16109, by rfl⟩) (B 32219 (by norm_num) ⟨16109, by rfl⟩ (by norm_num))
theorem R85925 : Reach 85925 := rs (se 4 (by rfl) ⟨8055, by rfl⟩) (B 16111 (by norm_num) ⟨8055, by rfl⟩ (by norm_num))
theorem R85929 : Reach 85929 := rs (se 2 (by rfl) ⟨32223, by rfl⟩) (B 64447 (by norm_num) ⟨32223, by rfl⟩ (by norm_num))
theorem R85933 : Reach 85933 := rs (se 3 (by rfl) ⟨16112, by rfl⟩) (B 32225 (by norm_num) ⟨16112, by rfl⟩ (by norm_num))
theorem R85937 : Reach 85937 := rs (se 2 (by rfl) ⟨32226, by rfl⟩) (B 64453 (by norm_num) ⟨32226, by rfl⟩ (by norm_num))
theorem R85941 : Reach 85941 := rs (se 5 (by rfl) ⟨4028, by rfl⟩) (B 8057 (by norm_num) ⟨4028, by rfl⟩ (by norm_num))
theorem R85945 : Reach 85945 := rs (se 2 (by rfl) ⟨32229, by rfl⟩) (B 64459 (by norm_num) ⟨32229, by rfl⟩ (by norm_num))
theorem R85949 : Reach 85949 := rs (se 3 (by rfl) ⟨16115, by rfl⟩) (B 32231 (by norm_num) ⟨16115, by rfl⟩ (by norm_num))
theorem R85953 : Reach 85953 := rs (se 2 (by rfl) ⟨32232, by rfl⟩) (B 64465 (by norm_num) ⟨32232, by rfl⟩ (by norm_num))
theorem R85957 : Reach 85957 := rs (se 4 (by rfl) ⟨8058, by rfl⟩) (B 16117 (by norm_num) ⟨8058, by rfl⟩ (by norm_num))
theorem R85961 : Reach 85961 := rs (se 2 (by rfl) ⟨32235, by rfl⟩) (B 64471 (by norm_num) ⟨32235, by rfl⟩ (by norm_num))
theorem R85965 : Reach 85965 := rs (se 3 (by rfl) ⟨16118, by rfl⟩) (B 32237 (by norm_num) ⟨16118, by rfl⟩ (by norm_num))
theorem R85969 : Reach 85969 := rs (se 2 (by rfl) ⟨32238, by rfl⟩) (B 64477 (by norm_num) ⟨32238, by rfl⟩ (by norm_num))
theorem R282581 : Reach 282581 := rs (se 7 (by rfl) ⟨3311, by rfl⟩) (B 6623 (by norm_num) ⟨3311, by rfl⟩ (by norm_num))
theorem R85973 : Reach 85973 := rs (se 7 (by rfl) ⟨1007, by rfl⟩) (B 2015 (by norm_num) ⟨1007, by rfl⟩ (by norm_num))
theorem R85977 : Reach 85977 := rs (se 2 (by rfl) ⟨32241, by rfl⟩) (B 64483 (by norm_num) ⟨32241, by rfl⟩ (by norm_num))
theorem R85981 : Reach 85981 := rs (se 3 (by rfl) ⟨16121, by rfl⟩) (B 32243 (by norm_num) ⟨16121, by rfl⟩ (by norm_num))
theorem R85985 : Reach 85985 := rs (se 2 (by rfl) ⟨32244, by rfl⟩) (B 64489 (by norm_num) ⟨32244, by rfl⟩ (by norm_num))
theorem R85989 : Reach 85989 := rs (se 4 (by rfl) ⟨8061, by rfl⟩) (B 16123 (by norm_num) ⟨8061, by rfl⟩ (by norm_num))
theorem R85993 : Reach 85993 := rs (se 2 (by rfl) ⟨32247, by rfl⟩) (B 64495 (by norm_num) ⟨32247, by rfl⟩ (by norm_num))
theorem R85997 : Reach 85997 := rs (se 3 (by rfl) ⟨16124, by rfl⟩) (B 32249 (by norm_num) ⟨16124, by rfl⟩ (by norm_num))
theorem R86001 : Reach 86001 := rs (se 2 (by rfl) ⟨32250, by rfl⟩) (B 64501 (by norm_num) ⟨32250, by rfl⟩ (by norm_num))
theorem R86005 : Reach 86005 := rs (se 5 (by rfl) ⟨4031, by rfl⟩) (B 8063 (by norm_num) ⟨4031, by rfl⟩ (by norm_num))
theorem R86009 : Reach 86009 := rs (se 2 (by rfl) ⟨32253, by rfl⟩) (B 64507 (by norm_num) ⟨32253, by rfl⟩ (by norm_num))
theorem R86013 : Reach 86013 := rs (se 3 (by rfl) ⟨16127, by rfl⟩) (B 32255 (by norm_num) ⟨16127, by rfl⟩ (by norm_num))
theorem R86017 : Reach 86017 := rs (se 2 (by rfl) ⟨32256, by rfl⟩) (B 64513 (by norm_num) ⟨32256, by rfl⟩ (by norm_num))
theorem R86021 : Reach 86021 := rs (se 4 (by rfl) ⟨8064, by rfl⟩) (B 16129 (by norm_num) ⟨8064, by rfl⟩ (by norm_num))
theorem R86025 : Reach 86025 := rs (se 2 (by rfl) ⟨32259, by rfl⟩) (B 64519 (by norm_num) ⟨32259, by rfl⟩ (by norm_num))
theorem R86029 : Reach 86029 := rs (se 3 (by rfl) ⟨16130, by rfl⟩) (B 32261 (by norm_num) ⟨16130, by rfl⟩ (by norm_num))
theorem R86033 : Reach 86033 := rs (se 2 (by rfl) ⟨32262, by rfl⟩) (B 64525 (by norm_num) ⟨32262, by rfl⟩ (by norm_num))
theorem R86037 : Reach 86037 := rs (se 6 (by rfl) ⟨2016, by rfl⟩) (B 4033 (by norm_num) ⟨2016, by rfl⟩ (by norm_num))
theorem R86041 : Reach 86041 := rs (se 2 (by rfl) ⟨32265, by rfl⟩) (B 64531 (by norm_num) ⟨32265, by rfl⟩ (by norm_num))
theorem R86045 : Reach 86045 := rs (se 3 (by rfl) ⟨16133, by rfl⟩) (B 32267 (by norm_num) ⟨16133, by rfl⟩ (by norm_num))
theorem R86049 : Reach 86049 := rs (se 2 (by rfl) ⟨32268, by rfl⟩) (B 64537 (by norm_num) ⟨32268, by rfl⟩ (by norm_num))
theorem R86053 : Reach 86053 := rs (se 4 (by rfl) ⟨8067, by rfl⟩) (B 16135 (by norm_num) ⟨8067, by rfl⟩ (by norm_num))
theorem R86057 : Reach 86057 := rs (se 2 (by rfl) ⟨32271, by rfl⟩) (B 64543 (by norm_num) ⟨32271, by rfl⟩ (by norm_num))
theorem R86061 : Reach 86061 := rs (se 3 (by rfl) ⟨16136, by rfl⟩) (B 32273 (by norm_num) ⟨16136, by rfl⟩ (by norm_num))
theorem R86065 : Reach 86065 := rs (se 2 (by rfl) ⟨32274, by rfl⟩) (B 64549 (by norm_num) ⟨32274, by rfl⟩ (by norm_num))
theorem R86069 : Reach 86069 := rs (se 5 (by rfl) ⟨4034, by rfl⟩) (B 8069 (by norm_num) ⟨4034, by rfl⟩ (by norm_num))
theorem R86073 : Reach 86073 := rs (se 2 (by rfl) ⟨32277, by rfl⟩) (B 64555 (by norm_num) ⟨32277, by rfl⟩ (by norm_num))
theorem R86077 : Reach 86077 := rs (se 3 (by rfl) ⟨16139, by rfl⟩) (B 32279 (by norm_num) ⟨16139, by rfl⟩ (by norm_num))
theorem R86081 : Reach 86081 := rs (se 2 (by rfl) ⟨32280, by rfl⟩) (B 64561 (by norm_num) ⟨32280, by rfl⟩ (by norm_num))
theorem R86085 : Reach 86085 := rs (se 4 (by rfl) ⟨8070, by rfl⟩) (B 16141 (by norm_num) ⟨8070, by rfl⟩ (by norm_num))
theorem R86089 : Reach 86089 := rs (se 2 (by rfl) ⟨32283, by rfl⟩) (B 64567 (by norm_num) ⟨32283, by rfl⟩ (by norm_num))
theorem R86093 : Reach 86093 := rs (se 3 (by rfl) ⟨16142, by rfl⟩) (B 32285 (by norm_num) ⟨16142, by rfl⟩ (by norm_num))
theorem R86097 : Reach 86097 := rs (se 2 (by rfl) ⟨32286, by rfl⟩) (B 64573 (by norm_num) ⟨32286, by rfl⟩ (by norm_num))
theorem R479317 : Reach 479317 := rs (se 8 (by rfl) ⟨2808, by rfl⟩) (B 5617 (by norm_num) ⟨2808, by rfl⟩ (by norm_num))
theorem R86101 : Reach 86101 := rs (se 8 (by rfl) ⟨504, by rfl⟩) (B 1009 (by norm_num) ⟨504, by rfl⟩ (by norm_num))
theorem R86105 : Reach 86105 := rs (se 2 (by rfl) ⟨32289, by rfl⟩) (B 64579 (by norm_num) ⟨32289, by rfl⟩ (by norm_num))
theorem R217181 : Reach 217181 := rs (se 3 (by rfl) ⟨40721, by rfl⟩) (B 81443 (by norm_num) ⟨40721, by rfl⟩ (by norm_num))
theorem R86109 : Reach 86109 := rs (se 3 (by rfl) ⟨16145, by rfl⟩) (B 32291 (by norm_num) ⟨16145, by rfl⟩ (by norm_num))
theorem R86113 : Reach 86113 := rs (se 2 (by rfl) ⟨32292, by rfl⟩) (B 64585 (by norm_num) ⟨32292, by rfl⟩ (by norm_num))
theorem R86117 : Reach 86117 := rs (se 4 (by rfl) ⟨8073, by rfl⟩) (B 16147 (by norm_num) ⟨8073, by rfl⟩ (by norm_num))
theorem R86121 : Reach 86121 := rs (se 2 (by rfl) ⟨32295, by rfl⟩) (B 64591 (by norm_num) ⟨32295, by rfl⟩ (by norm_num))
theorem R86125 : Reach 86125 := rs (se 3 (by rfl) ⟨16148, by rfl⟩) (B 32297 (by norm_num) ⟨16148, by rfl⟩ (by norm_num))
theorem R86129 : Reach 86129 := rs (se 2 (by rfl) ⟨32298, by rfl⟩) (B 64597 (by norm_num) ⟨32298, by rfl⟩ (by norm_num))
theorem R86133 : Reach 86133 := rs (se 5 (by rfl) ⟨4037, by rfl⟩) (B 8075 (by norm_num) ⟨4037, by rfl⟩ (by norm_num))
theorem R86137 : Reach 86137 := rs (se 2 (by rfl) ⟨32301, by rfl⟩) (B 64603 (by norm_num) ⟨32301, by rfl⟩ (by norm_num))
theorem R86141 : Reach 86141 := rs (se 3 (by rfl) ⟨16151, by rfl⟩) (B 32303 (by norm_num) ⟨16151, by rfl⟩ (by norm_num))
theorem R86145 : Reach 86145 := rs (se 2 (by rfl) ⟨32304, by rfl⟩) (B 64609 (by norm_num) ⟨32304, by rfl⟩ (by norm_num))
theorem R86149 : Reach 86149 := rs (se 4 (by rfl) ⟨8076, by rfl⟩) (B 16153 (by norm_num) ⟨8076, by rfl⟩ (by norm_num))
theorem R86153 : Reach 86153 := rs (se 2 (by rfl) ⟨32307, by rfl⟩) (B 64615 (by norm_num) ⟨32307, by rfl⟩ (by norm_num))
theorem R86157 : Reach 86157 := rs (se 3 (by rfl) ⟨16154, by rfl⟩) (B 32309 (by norm_num) ⟨16154, by rfl⟩ (by norm_num))
theorem R86161 : Reach 86161 := rs (se 2 (by rfl) ⟨32310, by rfl⟩) (B 64621 (by norm_num) ⟨32310, by rfl⟩ (by norm_num))
theorem R86165 : Reach 86165 := rs (se 6 (by rfl) ⟨2019, by rfl⟩) (B 4039 (by norm_num) ⟨2019, by rfl⟩ (by norm_num))
theorem R86169 : Reach 86169 := rs (se 2 (by rfl) ⟨32313, by rfl⟩) (B 64627 (by norm_num) ⟨32313, by rfl⟩ (by norm_num))
theorem R86173 : Reach 86173 := rs (se 3 (by rfl) ⟨16157, by rfl⟩) (B 32315 (by norm_num) ⟨16157, by rfl⟩ (by norm_num))
theorem R86177 : Reach 86177 := rs (se 2 (by rfl) ⟨32316, by rfl⟩) (B 64633 (by norm_num) ⟨32316, by rfl⟩ (by norm_num))
theorem R86181 : Reach 86181 := rs (se 4 (by rfl) ⟨8079, by rfl⟩) (B 16159 (by norm_num) ⟨8079, by rfl⟩ (by norm_num))
theorem R86185 : Reach 86185 := rs (se 2 (by rfl) ⟨32319, by rfl⟩) (B 64639 (by norm_num) ⟨32319, by rfl⟩ (by norm_num))
theorem R86189 : Reach 86189 := rs (se 3 (by rfl) ⟨16160, by rfl⟩) (B 32321 (by norm_num) ⟨16160, by rfl⟩ (by norm_num))
theorem R86193 : Reach 86193 := rs (se 2 (by rfl) ⟨32322, by rfl⟩) (B 64645 (by norm_num) ⟨32322, by rfl⟩ (by norm_num))
theorem R151733 : Reach 151733 := rs (se 5 (by rfl) ⟨7112, by rfl⟩) (B 14225 (by norm_num) ⟨7112, by rfl⟩ (by norm_num))
theorem R86197 : Reach 86197 := rs (se 5 (by rfl) ⟨4040, by rfl⟩) (B 8081 (by norm_num) ⟨4040, by rfl⟩ (by norm_num))
theorem R86201 : Reach 86201 := rs (se 2 (by rfl) ⟨32325, by rfl⟩) (B 64651 (by norm_num) ⟨32325, by rfl⟩ (by norm_num))
theorem R86205 : Reach 86205 := rs (se 3 (by rfl) ⟨16163, by rfl⟩) (B 32327 (by norm_num) ⟨16163, by rfl⟩ (by norm_num))
theorem R86209 : Reach 86209 := rs (se 2 (by rfl) ⟨32328, by rfl⟩) (B 64657 (by norm_num) ⟨32328, by rfl⟩ (by norm_num))
theorem R86213 : Reach 86213 := rs (se 4 (by rfl) ⟨8082, by rfl⟩) (B 16165 (by norm_num) ⟨8082, by rfl⟩ (by norm_num))
theorem R86217 : Reach 86217 := rs (se 2 (by rfl) ⟨32331, by rfl⟩) (B 64663 (by norm_num) ⟨32331, by rfl⟩ (by norm_num))
theorem R86221 : Reach 86221 := rs (se 3 (by rfl) ⟨16166, by rfl⟩) (B 32333 (by norm_num) ⟨16166, by rfl⟩ (by norm_num))
theorem R86225 : Reach 86225 := rs (se 2 (by rfl) ⟨32334, by rfl⟩) (B 64669 (by norm_num) ⟨32334, by rfl⟩ (by norm_num))
theorem R86229 : Reach 86229 := rs (se 7 (by rfl) ⟨1010, by rfl⟩) (B 2021 (by norm_num) ⟨1010, by rfl⟩ (by norm_num))
theorem R86233 : Reach 86233 := rs (se 2 (by rfl) ⟨32337, by rfl⟩) (B 64675 (by norm_num) ⟨32337, by rfl⟩ (by norm_num))
theorem R86237 : Reach 86237 := rs (se 3 (by rfl) ⟨16169, by rfl⟩) (B 32339 (by norm_num) ⟨16169, by rfl⟩ (by norm_num))
theorem R86241 : Reach 86241 := rs (se 2 (by rfl) ⟨32340, by rfl⟩) (B 64681 (by norm_num) ⟨32340, by rfl⟩ (by norm_num))
theorem R86245 : Reach 86245 := rs (se 4 (by rfl) ⟨8085, by rfl⟩) (B 16171 (by norm_num) ⟨8085, by rfl⟩ (by norm_num))
theorem R86249 : Reach 86249 := rs (se 2 (by rfl) ⟨32343, by rfl⟩) (B 64687 (by norm_num) ⟨32343, by rfl⟩ (by norm_num))
theorem R86253 : Reach 86253 := rs (se 3 (by rfl) ⟨16172, by rfl⟩) (B 32345 (by norm_num) ⟨16172, by rfl⟩ (by norm_num))
theorem R86257 : Reach 86257 := rs (se 2 (by rfl) ⟨32346, by rfl⟩) (B 64693 (by norm_num) ⟨32346, by rfl⟩ (by norm_num))
theorem R86261 : Reach 86261 := rs (se 5 (by rfl) ⟨4043, by rfl⟩) (B 8087 (by norm_num) ⟨4043, by rfl⟩ (by norm_num))
theorem R86265 : Reach 86265 := rs (se 2 (by rfl) ⟨32349, by rfl⟩) (B 64699 (by norm_num) ⟨32349, by rfl⟩ (by norm_num))
theorem R86269 : Reach 86269 := rs (se 3 (by rfl) ⟨16175, by rfl⟩) (B 32351 (by norm_num) ⟨16175, by rfl⟩ (by norm_num))
theorem R86273 : Reach 86273 := rs (se 2 (by rfl) ⟨32352, by rfl⟩) (B 64705 (by norm_num) ⟨32352, by rfl⟩ (by norm_num))
theorem R86277 : Reach 86277 := rs (se 4 (by rfl) ⟨8088, by rfl⟩) (B 16177 (by norm_num) ⟨8088, by rfl⟩ (by norm_num))
theorem R86281 : Reach 86281 := rs (se 2 (by rfl) ⟨32355, by rfl⟩) (B 64711 (by norm_num) ⟨32355, by rfl⟩ (by norm_num))
theorem R86285 : Reach 86285 := rs (se 3 (by rfl) ⟨16178, by rfl⟩) (B 32357 (by norm_num) ⟨16178, by rfl⟩ (by norm_num))
theorem R184589 : Reach 184589 := rs (se 3 (by rfl) ⟨34610, by rfl⟩) (B 69221 (by norm_num) ⟨34610, by rfl⟩ (by norm_num))
theorem R86289 : Reach 86289 := rs (se 2 (by rfl) ⟨32358, by rfl⟩) (B 64717 (by norm_num) ⟨32358, by rfl⟩ (by norm_num))
theorem R86293 : Reach 86293 := rs (se 6 (by rfl) ⟨2022, by rfl⟩) (B 4045 (by norm_num) ⟨2022, by rfl⟩ (by norm_num))
theorem R86297 : Reach 86297 := rs (se 2 (by rfl) ⟨32361, by rfl⟩) (B 64723 (by norm_num) ⟨32361, by rfl⟩ (by norm_num))
theorem R86301 : Reach 86301 := rs (se 3 (by rfl) ⟨16181, by rfl⟩) (B 32363 (by norm_num) ⟨16181, by rfl⟩ (by norm_num))
theorem R86305 : Reach 86305 := rs (se 2 (by rfl) ⟨32364, by rfl⟩) (B 64729 (by norm_num) ⟨32364, by rfl⟩ (by norm_num))
theorem R86309 : Reach 86309 := rs (se 4 (by rfl) ⟨8091, by rfl⟩) (B 16183 (by norm_num) ⟨8091, by rfl⟩ (by norm_num))
theorem R86313 : Reach 86313 := rs (se 2 (by rfl) ⟨32367, by rfl⟩) (B 64735 (by norm_num) ⟨32367, by rfl⟩ (by norm_num))
theorem R86317 : Reach 86317 := rs (se 3 (by rfl) ⟨16184, by rfl⟩) (B 32369 (by norm_num) ⟨16184, by rfl⟩ (by norm_num))
theorem R86321 : Reach 86321 := rs (se 2 (by rfl) ⟨32370, by rfl⟩) (B 64741 (by norm_num) ⟨32370, by rfl⟩ (by norm_num))
theorem R86325 : Reach 86325 := rs (se 5 (by rfl) ⟨4046, by rfl⟩) (B 8093 (by norm_num) ⟨4046, by rfl⟩ (by norm_num))
theorem R86329 : Reach 86329 := rs (se 2 (by rfl) ⟨32373, by rfl⟩) (B 64747 (by norm_num) ⟨32373, by rfl⟩ (by norm_num))
theorem R86333 : Reach 86333 := rs (se 3 (by rfl) ⟨16187, by rfl⟩) (B 32375 (by norm_num) ⟨16187, by rfl⟩ (by norm_num))
theorem R86337 : Reach 86337 := rs (se 2 (by rfl) ⟨32376, by rfl⟩) (B 64753 (by norm_num) ⟨32376, by rfl⟩ (by norm_num))
theorem R86341 : Reach 86341 := rs (se 4 (by rfl) ⟨8094, by rfl⟩) (B 16189 (by norm_num) ⟨8094, by rfl⟩ (by norm_num))
theorem R86345 : Reach 86345 := rs (se 2 (by rfl) ⟨32379, by rfl⟩) (B 64759 (by norm_num) ⟨32379, by rfl⟩ (by norm_num))
theorem R86349 : Reach 86349 := rs (se 3 (by rfl) ⟨16190, by rfl⟩) (B 32381 (by norm_num) ⟨16190, by rfl⟩ (by norm_num))
theorem R86353 : Reach 86353 := rs (se 2 (by rfl) ⟨32382, by rfl⟩) (B 64765 (by norm_num) ⟨32382, by rfl⟩ (by norm_num))
theorem R86357 : Reach 86357 := rs (se 10 (by rfl) ⟨126, by rfl⟩) (B 253 (by norm_num) ⟨126, by rfl⟩ (by norm_num))
theorem R86361 : Reach 86361 := rs (se 2 (by rfl) ⟨32385, by rfl⟩) (B 64771 (by norm_num) ⟨32385, by rfl⟩ (by norm_num))
theorem R86365 : Reach 86365 := rs (se 3 (by rfl) ⟨16193, by rfl⟩) (B 32387 (by norm_num) ⟨16193, by rfl⟩ (by norm_num))
theorem R86369 : Reach 86369 := rs (se 2 (by rfl) ⟨32388, by rfl⟩) (B 64777 (by norm_num) ⟨32388, by rfl⟩ (by norm_num))
theorem R86373 : Reach 86373 := rs (se 4 (by rfl) ⟨8097, by rfl⟩) (B 16195 (by norm_num) ⟨8097, by rfl⟩ (by norm_num))
theorem R86377 : Reach 86377 := rs (se 2 (by rfl) ⟨32391, by rfl⟩) (B 64783 (by norm_num) ⟨32391, by rfl⟩ (by norm_num))
theorem R86381 : Reach 86381 := rs (se 3 (by rfl) ⟨16196, by rfl⟩) (B 32393 (by norm_num) ⟨16196, by rfl⟩ (by norm_num))
theorem R86385 : Reach 86385 := rs (se 2 (by rfl) ⟨32394, by rfl⟩) (B 64789 (by norm_num) ⟨32394, by rfl⟩ (by norm_num))
theorem R86389 : Reach 86389 := rs (se 5 (by rfl) ⟨4049, by rfl⟩) (B 8099 (by norm_num) ⟨4049, by rfl⟩ (by norm_num))
theorem R250229 : Reach 250229 := rs (se 5 (by rfl) ⟨11729, by rfl⟩) (B 23459 (by norm_num) ⟨11729, by rfl⟩ (by norm_num))
theorem R86393 : Reach 86393 := rs (se 2 (by rfl) ⟨32397, by rfl⟩) (B 64795 (by norm_num) ⟨32397, by rfl⟩ (by norm_num))
theorem R86397 : Reach 86397 := rs (se 3 (by rfl) ⟨16199, by rfl⟩) (B 32399 (by norm_num) ⟨16199, by rfl⟩ (by norm_num))
theorem R86401 : Reach 86401 := rs (se 2 (by rfl) ⟨32400, by rfl⟩) (B 64801 (by norm_num) ⟨32400, by rfl⟩ (by norm_num))
theorem R283013 : Reach 283013 := rs (se 4 (by rfl) ⟨26532, by rfl⟩) (B 53065 (by norm_num) ⟨26532, by rfl⟩ (by norm_num))
theorem R86405 : Reach 86405 := rs (se 4 (by rfl) ⟨8100, by rfl⟩) (B 16201 (by norm_num) ⟨8100, by rfl⟩ (by norm_num))
theorem R86409 : Reach 86409 := rs (se 2 (by rfl) ⟨32403, by rfl⟩) (B 64807 (by norm_num) ⟨32403, by rfl⟩ (by norm_num))
theorem R86413 : Reach 86413 := rs (se 3 (by rfl) ⟨16202, by rfl⟩) (B 32405 (by norm_num) ⟨16202, by rfl⟩ (by norm_num))
theorem R86417 : Reach 86417 := rs (se 2 (by rfl) ⟨32406, by rfl⟩) (B 64813 (by norm_num) ⟨32406, by rfl⟩ (by norm_num))
theorem R86421 : Reach 86421 := rs (se 6 (by rfl) ⟨2025, by rfl⟩) (B 4051 (by norm_num) ⟨2025, by rfl⟩ (by norm_num))
theorem R86425 : Reach 86425 := rs (se 2 (by rfl) ⟨32409, by rfl⟩) (B 64819 (by norm_num) ⟨32409, by rfl⟩ (by norm_num))
theorem R86429 : Reach 86429 := rs (se 3 (by rfl) ⟨16205, by rfl⟩) (B 32411 (by norm_num) ⟨16205, by rfl⟩ (by norm_num))
theorem R86433 : Reach 86433 := rs (se 2 (by rfl) ⟨32412, by rfl⟩) (B 64825 (by norm_num) ⟨32412, by rfl⟩ (by norm_num))
theorem R86437 : Reach 86437 := rs (se 4 (by rfl) ⟨8103, by rfl⟩) (B 16207 (by norm_num) ⟨8103, by rfl⟩ (by norm_num))
theorem R86441 : Reach 86441 := rs (se 2 (by rfl) ⟨32415, by rfl⟩) (B 64831 (by norm_num) ⟨32415, by rfl⟩ (by norm_num))
theorem R86445 : Reach 86445 := rs (se 3 (by rfl) ⟨16208, by rfl⟩) (B 32417 (by norm_num) ⟨16208, by rfl⟩ (by norm_num))
theorem R86449 : Reach 86449 := rs (se 2 (by rfl) ⟨32418, by rfl⟩) (B 64837 (by norm_num) ⟨32418, by rfl⟩ (by norm_num))
theorem R217525 : Reach 217525 := rs (se 5 (by rfl) ⟨10196, by rfl⟩) (B 20393 (by norm_num) ⟨10196, by rfl⟩ (by norm_num))
theorem R86453 : Reach 86453 := rs (se 5 (by rfl) ⟨4052, by rfl⟩) (B 8105 (by norm_num) ⟨4052, by rfl⟩ (by norm_num))
theorem R86457 : Reach 86457 := rs (se 2 (by rfl) ⟨32421, by rfl⟩) (B 64843 (by norm_num) ⟨32421, by rfl⟩ (by norm_num))
theorem R86461 : Reach 86461 := rs (se 3 (by rfl) ⟨16211, by rfl⟩) (B 32423 (by norm_num) ⟨16211, by rfl⟩ (by norm_num))
theorem R86465 : Reach 86465 := rs (se 2 (by rfl) ⟨32424, by rfl⟩) (B 64849 (by norm_num) ⟨32424, by rfl⟩ (by norm_num))
theorem R119237 : Reach 119237 := rs (se 4 (by rfl) ⟨11178, by rfl⟩) (B 22357 (by norm_num) ⟨11178, by rfl⟩ (by norm_num))
theorem R86469 : Reach 86469 := rs (se 4 (by rfl) ⟨8106, by rfl⟩) (B 16213 (by norm_num) ⟨8106, by rfl⟩ (by norm_num))
theorem R86473 : Reach 86473 := rs (se 2 (by rfl) ⟨32427, by rfl⟩) (B 64855 (by norm_num) ⟨32427, by rfl⟩ (by norm_num))
theorem R86477 : Reach 86477 := rs (se 3 (by rfl) ⟨16214, by rfl⟩) (B 32429 (by norm_num) ⟨16214, by rfl⟩ (by norm_num))
theorem R86481 : Reach 86481 := rs (se 2 (by rfl) ⟨32430, by rfl⟩) (B 64861 (by norm_num) ⟨32430, by rfl⟩ (by norm_num))
theorem R86485 : Reach 86485 := rs (se 7 (by rfl) ⟨1013, by rfl⟩) (B 2027 (by norm_num) ⟨1013, by rfl⟩ (by norm_num))
theorem R86489 : Reach 86489 := rs (se 2 (by rfl) ⟨32433, by rfl⟩) (B 64867 (by norm_num) ⟨32433, by rfl⟩ (by norm_num))
theorem R86493 : Reach 86493 := rs (se 3 (by rfl) ⟨16217, by rfl⟩) (B 32435 (by norm_num) ⟨16217, by rfl⟩ (by norm_num))
theorem R86497 : Reach 86497 := rs (se 2 (by rfl) ⟨32436, by rfl⟩) (B 64873 (by norm_num) ⟨32436, by rfl⟩ (by norm_num))
theorem R86501 : Reach 86501 := rs (se 4 (by rfl) ⟨8109, by rfl⟩) (B 16219 (by norm_num) ⟨8109, by rfl⟩ (by norm_num))
theorem R86505 : Reach 86505 := rs (se 2 (by rfl) ⟨32439, by rfl⟩) (B 64879 (by norm_num) ⟨32439, by rfl⟩ (by norm_num))
theorem R86509 : Reach 86509 := rs (se 3 (by rfl) ⟨16220, by rfl⟩) (B 32441 (by norm_num) ⟨16220, by rfl⟩ (by norm_num))
theorem R86513 : Reach 86513 := rs (se 2 (by rfl) ⟨32442, by rfl⟩) (B 64885 (by norm_num) ⟨32442, by rfl⟩ (by norm_num))
theorem R86517 : Reach 86517 := rs (se 5 (by rfl) ⟨4055, by rfl⟩) (B 8111 (by norm_num) ⟨4055, by rfl⟩ (by norm_num))
theorem R86521 : Reach 86521 := rs (se 2 (by rfl) ⟨32445, by rfl⟩) (B 64891 (by norm_num) ⟨32445, by rfl⟩ (by norm_num))
theorem R86525 : Reach 86525 := rs (se 3 (by rfl) ⟨16223, by rfl⟩) (B 32447 (by norm_num) ⟨16223, by rfl⟩ (by norm_num))
theorem R86529 : Reach 86529 := rs (se 2 (by rfl) ⟨32448, by rfl⟩) (B 64897 (by norm_num) ⟨32448, by rfl⟩ (by norm_num))
theorem R86533 : Reach 86533 := rs (se 4 (by rfl) ⟨8112, by rfl⟩) (B 16225 (by norm_num) ⟨8112, by rfl⟩ (by norm_num))
theorem R86537 : Reach 86537 := rs (se 2 (by rfl) ⟨32451, by rfl⟩) (B 64903 (by norm_num) ⟨32451, by rfl⟩ (by norm_num))
theorem R86541 : Reach 86541 := rs (se 3 (by rfl) ⟨16226, by rfl⟩) (B 32453 (by norm_num) ⟨16226, by rfl⟩ (by norm_num))
theorem R86545 : Reach 86545 := rs (se 2 (by rfl) ⟨32454, by rfl⟩) (B 64909 (by norm_num) ⟨32454, by rfl⟩ (by norm_num))
theorem R86549 : Reach 86549 := rs (se 6 (by rfl) ⟨2028, by rfl⟩) (B 4057 (by norm_num) ⟨2028, by rfl⟩ (by norm_num))
theorem R86553 : Reach 86553 := rs (se 2 (by rfl) ⟨32457, by rfl⟩) (B 64915 (by norm_num) ⟨32457, by rfl⟩ (by norm_num))
theorem R86557 : Reach 86557 := rs (se 3 (by rfl) ⟨16229, by rfl⟩) (B 32459 (by norm_num) ⟨16229, by rfl⟩ (by norm_num))
theorem R86561 : Reach 86561 := rs (se 2 (by rfl) ⟨32460, by rfl⟩) (B 64921 (by norm_num) ⟨32460, by rfl⟩ (by norm_num))
theorem R217637 : Reach 217637 := rs (se 4 (by rfl) ⟨20403, by rfl⟩) (B 40807 (by norm_num) ⟨20403, by rfl⟩ (by norm_num))
theorem R86565 : Reach 86565 := rs (se 4 (by rfl) ⟨8115, by rfl⟩) (B 16231 (by norm_num) ⟨8115, by rfl⟩ (by norm_num))
theorem R86569 : Reach 86569 := rs (se 2 (by rfl) ⟨32463, by rfl⟩) (B 64927 (by norm_num) ⟨32463, by rfl⟩ (by norm_num))
theorem R86573 : Reach 86573 := rs (se 3 (by rfl) ⟨16232, by rfl⟩) (B 32465 (by norm_num) ⟨16232, by rfl⟩ (by norm_num))
theorem R86577 : Reach 86577 := rs (se 2 (by rfl) ⟨32466, by rfl⟩) (B 64933 (by norm_num) ⟨32466, by rfl⟩ (by norm_num))
theorem R348725 : Reach 348725 := rs (se 5 (by rfl) ⟨16346, by rfl⟩) (B 32693 (by norm_num) ⟨16346, by rfl⟩ (by norm_num))
theorem R86581 : Reach 86581 := rs (se 5 (by rfl) ⟨4058, by rfl⟩) (B 8117 (by norm_num) ⟨4058, by rfl⟩ (by norm_num))
theorem R86585 : Reach 86585 := rs (se 2 (by rfl) ⟨32469, by rfl⟩) (B 64939 (by norm_num) ⟨32469, by rfl⟩ (by norm_num))
theorem R86589 : Reach 86589 := rs (se 3 (by rfl) ⟨16235, by rfl⟩) (B 32471 (by norm_num) ⟨16235, by rfl⟩ (by norm_num))
theorem R86593 : Reach 86593 := rs (se 2 (by rfl) ⟨32472, by rfl⟩) (B 64945 (by norm_num) ⟨32472, by rfl⟩ (by norm_num))
theorem R86597 : Reach 86597 := rs (se 4 (by rfl) ⟨8118, by rfl⟩) (B 16237 (by norm_num) ⟨8118, by rfl⟩ (by norm_num))
theorem R86601 : Reach 86601 := rs (se 2 (by rfl) ⟨32475, by rfl⟩) (B 64951 (by norm_num) ⟨32475, by rfl⟩ (by norm_num))
theorem R86605 : Reach 86605 := rs (se 3 (by rfl) ⟨16238, by rfl⟩) (B 32477 (by norm_num) ⟨16238, by rfl⟩ (by norm_num))
theorem R86609 : Reach 86609 := rs (se 2 (by rfl) ⟨32478, by rfl⟩) (B 64957 (by norm_num) ⟨32478, by rfl⟩ (by norm_num))
theorem R86613 : Reach 86613 := rs (se 8 (by rfl) ⟨507, by rfl⟩) (B 1015 (by norm_num) ⟨507, by rfl⟩ (by norm_num))
theorem R86617 : Reach 86617 := rs (se 2 (by rfl) ⟨32481, by rfl⟩) (B 64963 (by norm_num) ⟨32481, by rfl⟩ (by norm_num))
theorem R86621 : Reach 86621 := rs (se 3 (by rfl) ⟨16241, by rfl⟩) (B 32483 (by norm_num) ⟨16241, by rfl⟩ (by norm_num))
theorem R86625 : Reach 86625 := rs (se 2 (by rfl) ⟨32484, by rfl⟩) (B 64969 (by norm_num) ⟨32484, by rfl⟩ (by norm_num))
theorem R86629 : Reach 86629 := rs (se 4 (by rfl) ⟨8121, by rfl⟩) (B 16243 (by norm_num) ⟨8121, by rfl⟩ (by norm_num))
theorem R86633 : Reach 86633 := rs (se 2 (by rfl) ⟨32487, by rfl⟩) (B 64975 (by norm_num) ⟨32487, by rfl⟩ (by norm_num))
theorem R86637 : Reach 86637 := rs (se 3 (by rfl) ⟨16244, by rfl⟩) (B 32489 (by norm_num) ⟨16244, by rfl⟩ (by norm_num))
theorem R86641 : Reach 86641 := rs (se 2 (by rfl) ⟨32490, by rfl⟩) (B 64981 (by norm_num) ⟨32490, by rfl⟩ (by norm_num))
theorem R316021 : Reach 316021 := rs (se 5 (by rfl) ⟨14813, by rfl⟩) (B 29627 (by norm_num) ⟨14813, by rfl⟩ (by norm_num))
theorem R86645 : Reach 86645 := rs (se 5 (by rfl) ⟨4061, by rfl⟩) (B 8123 (by norm_num) ⟨4061, by rfl⟩ (by norm_num))
theorem R86649 : Reach 86649 := rs (se 2 (by rfl) ⟨32493, by rfl⟩) (B 64987 (by norm_num) ⟨32493, by rfl⟩ (by norm_num))
theorem R86653 : Reach 86653 := rs (se 3 (by rfl) ⟨16247, by rfl⟩) (B 32495 (by norm_num) ⟨16247, by rfl⟩ (by norm_num))
theorem R86657 : Reach 86657 := rs (se 2 (by rfl) ⟨32496, by rfl⟩) (B 64993 (by norm_num) ⟨32496, by rfl⟩ (by norm_num))
theorem R86661 : Reach 86661 := rs (se 4 (by rfl) ⟨8124, by rfl⟩) (B 16249 (by norm_num) ⟨8124, by rfl⟩ (by norm_num))
theorem R86665 : Reach 86665 := rs (se 2 (by rfl) ⟨32499, by rfl⟩) (B 64999 (by norm_num) ⟨32499, by rfl⟩ (by norm_num))
theorem R86669 : Reach 86669 := rs (se 3 (by rfl) ⟨16250, by rfl⟩) (B 32501 (by norm_num) ⟨16250, by rfl⟩ (by norm_num))
theorem R86673 : Reach 86673 := rs (se 2 (by rfl) ⟨32502, by rfl⟩) (B 65005 (by norm_num) ⟨32502, by rfl⟩ (by norm_num))
theorem R86677 : Reach 86677 := rs (se 6 (by rfl) ⟨2031, by rfl⟩) (B 4063 (by norm_num) ⟨2031, by rfl⟩ (by norm_num))
theorem R86681 : Reach 86681 := rs (se 2 (by rfl) ⟨32505, by rfl⟩) (B 65011 (by norm_num) ⟨32505, by rfl⟩ (by norm_num))
theorem R86685 : Reach 86685 := rs (se 3 (by rfl) ⟨16253, by rfl⟩) (B 32507 (by norm_num) ⟨16253, by rfl⟩ (by norm_num))
theorem R86689 : Reach 86689 := rs (se 2 (by rfl) ⟨32508, by rfl⟩) (B 65017 (by norm_num) ⟨32508, by rfl⟩ (by norm_num))
theorem R86693 : Reach 86693 := rs (se 4 (by rfl) ⟨8127, by rfl⟩) (B 16255 (by norm_num) ⟨8127, by rfl⟩ (by norm_num))
theorem R86697 : Reach 86697 := rs (se 2 (by rfl) ⟨32511, by rfl⟩) (B 65023 (by norm_num) ⟨32511, by rfl⟩ (by norm_num))
theorem R86701 : Reach 86701 := rs (se 3 (by rfl) ⟨16256, by rfl⟩) (B 32513 (by norm_num) ⟨16256, by rfl⟩ (by norm_num))
theorem R86705 : Reach 86705 := rs (se 2 (by rfl) ⟨32514, by rfl⟩) (B 65029 (by norm_num) ⟨32514, by rfl⟩ (by norm_num))
theorem R86709 : Reach 86709 := rs (se 5 (by rfl) ⟨4064, by rfl⟩) (B 8129 (by norm_num) ⟨4064, by rfl⟩ (by norm_num))
theorem R86713 : Reach 86713 := rs (se 2 (by rfl) ⟨32517, by rfl⟩) (B 65035 (by norm_num) ⟨32517, by rfl⟩ (by norm_num))
theorem R86717 : Reach 86717 := rs (se 3 (by rfl) ⟨16259, by rfl⟩) (B 32519 (by norm_num) ⟨16259, by rfl⟩ (by norm_num))
theorem R86721 : Reach 86721 := rs (se 2 (by rfl) ⟨32520, by rfl⟩) (B 65041 (by norm_num) ⟨32520, by rfl⟩ (by norm_num))
theorem R86725 : Reach 86725 := rs (se 4 (by rfl) ⟨8130, by rfl⟩) (B 16261 (by norm_num) ⟨8130, by rfl⟩ (by norm_num))
theorem R86729 : Reach 86729 := rs (se 2 (by rfl) ⟨32523, by rfl⟩) (B 65047 (by norm_num) ⟨32523, by rfl⟩ (by norm_num))
theorem R86733 : Reach 86733 := rs (se 3 (by rfl) ⟨16262, by rfl⟩) (B 32525 (by norm_num) ⟨16262, by rfl⟩ (by norm_num))
theorem R86737 : Reach 86737 := rs (se 2 (by rfl) ⟨32526, by rfl⟩) (B 65053 (by norm_num) ⟨32526, by rfl⟩ (by norm_num))
theorem R86741 : Reach 86741 := rs (se 7 (by rfl) ⟨1016, by rfl⟩) (B 2033 (by norm_num) ⟨1016, by rfl⟩ (by norm_num))
theorem R86745 : Reach 86745 := rs (se 2 (by rfl) ⟨32529, by rfl⟩) (B 65059 (by norm_num) ⟨32529, by rfl⟩ (by norm_num))
theorem R86749 : Reach 86749 := rs (se 3 (by rfl) ⟨16265, by rfl⟩) (B 32531 (by norm_num) ⟨16265, by rfl⟩ (by norm_num))
theorem R86753 : Reach 86753 := rs (se 2 (by rfl) ⟨32532, by rfl⟩) (B 65065 (by norm_num) ⟨32532, by rfl⟩ (by norm_num))
theorem R217829 : Reach 217829 := rs (se 4 (by rfl) ⟨20421, by rfl⟩) (B 40843 (by norm_num) ⟨20421, by rfl⟩ (by norm_num))
theorem R86757 : Reach 86757 := rs (se 4 (by rfl) ⟨8133, by rfl⟩) (B 16267 (by norm_num) ⟨8133, by rfl⟩ (by norm_num))
theorem R86761 : Reach 86761 := rs (se 2 (by rfl) ⟨32535, by rfl⟩) (B 65071 (by norm_num) ⟨32535, by rfl⟩ (by norm_num))
theorem R86765 : Reach 86765 := rs (se 3 (by rfl) ⟨16268, by rfl⟩) (B 32537 (by norm_num) ⟨16268, by rfl⟩ (by norm_num))
theorem R86769 : Reach 86769 := rs (se 2 (by rfl) ⟨32538, by rfl⟩) (B 65077 (by norm_num) ⟨32538, by rfl⟩ (by norm_num))
theorem R86773 : Reach 86773 := rs (se 5 (by rfl) ⟨4067, by rfl⟩) (B 8135 (by norm_num) ⟨4067, by rfl⟩ (by norm_num))
theorem R86777 : Reach 86777 := rs (se 2 (by rfl) ⟨32541, by rfl⟩) (B 65083 (by norm_num) ⟨32541, by rfl⟩ (by norm_num))
theorem R86781 : Reach 86781 := rs (se 3 (by rfl) ⟨16271, by rfl⟩) (B 32543 (by norm_num) ⟨16271, by rfl⟩ (by norm_num))
theorem R86785 : Reach 86785 := rs (se 2 (by rfl) ⟨32544, by rfl⟩) (B 65089 (by norm_num) ⟨32544, by rfl⟩ (by norm_num))
theorem R86789 : Reach 86789 := rs (se 4 (by rfl) ⟨8136, by rfl⟩) (B 16273 (by norm_num) ⟨8136, by rfl⟩ (by norm_num))
theorem R86793 : Reach 86793 := rs (se 2 (by rfl) ⟨32547, by rfl⟩) (B 65095 (by norm_num) ⟨32547, by rfl⟩ (by norm_num))
theorem R86797 : Reach 86797 := rs (se 3 (by rfl) ⟨16274, by rfl⟩) (B 32549 (by norm_num) ⟨16274, by rfl⟩ (by norm_num))
theorem R86801 : Reach 86801 := rs (se 2 (by rfl) ⟨32550, by rfl⟩) (B 65101 (by norm_num) ⟨32550, by rfl⟩ (by norm_num))
theorem R86805 : Reach 86805 := rs (se 6 (by rfl) ⟨2034, by rfl⟩) (B 4069 (by norm_num) ⟨2034, by rfl⟩ (by norm_num))
theorem R86809 : Reach 86809 := rs (se 2 (by rfl) ⟨32553, by rfl⟩) (B 65107 (by norm_num) ⟨32553, by rfl⟩ (by norm_num))
theorem R86813 : Reach 86813 := rs (se 3 (by rfl) ⟨16277, by rfl⟩) (B 32555 (by norm_num) ⟨16277, by rfl⟩ (by norm_num))
theorem R86817 : Reach 86817 := rs (se 2 (by rfl) ⟨32556, by rfl⟩) (B 65113 (by norm_num) ⟨32556, by rfl⟩ (by norm_num))
theorem R86821 : Reach 86821 := rs (se 4 (by rfl) ⟨8139, by rfl⟩) (B 16279 (by norm_num) ⟨8139, by rfl⟩ (by norm_num))
theorem R86825 : Reach 86825 := rs (se 2 (by rfl) ⟨32559, by rfl⟩) (B 65119 (by norm_num) ⟨32559, by rfl⟩ (by norm_num))
theorem R86829 : Reach 86829 := rs (se 3 (by rfl) ⟨16280, by rfl⟩) (B 32561 (by norm_num) ⟨16280, by rfl⟩ (by norm_num))
theorem R86833 : Reach 86833 := rs (se 2 (by rfl) ⟨32562, by rfl⟩) (B 65125 (by norm_num) ⟨32562, by rfl⟩ (by norm_num))
theorem R283445 : Reach 283445 := rs (se 5 (by rfl) ⟨13286, by rfl⟩) (B 26573 (by norm_num) ⟨13286, by rfl⟩ (by norm_num))
theorem R86837 : Reach 86837 := rs (se 5 (by rfl) ⟨4070, by rfl⟩) (B 8141 (by norm_num) ⟨4070, by rfl⟩ (by norm_num))
theorem R86841 : Reach 86841 := rs (se 2 (by rfl) ⟨32565, by rfl⟩) (B 65131 (by norm_num) ⟨32565, by rfl⟩ (by norm_num))
theorem R86845 : Reach 86845 := rs (se 3 (by rfl) ⟨16283, by rfl⟩) (B 32567 (by norm_num) ⟨16283, by rfl⟩ (by norm_num))
theorem R86849 : Reach 86849 := rs (se 2 (by rfl) ⟨32568, by rfl⟩) (B 65137 (by norm_num) ⟨32568, by rfl⟩ (by norm_num))
theorem R86853 : Reach 86853 := rs (se 4 (by rfl) ⟨8142, by rfl⟩) (B 16285 (by norm_num) ⟨8142, by rfl⟩ (by norm_num))
theorem R86857 : Reach 86857 := rs (se 2 (by rfl) ⟨32571, by rfl⟩) (B 65143 (by norm_num) ⟨32571, by rfl⟩ (by norm_num))
theorem R86861 : Reach 86861 := rs (se 3 (by rfl) ⟨16286, by rfl⟩) (B 32573 (by norm_num) ⟨16286, by rfl⟩ (by norm_num))
theorem R86865 : Reach 86865 := rs (se 2 (by rfl) ⟨32574, by rfl⟩) (B 65149 (by norm_num) ⟨32574, by rfl⟩ (by norm_num))
theorem R86869 : Reach 86869 := rs (se 9 (by rfl) ⟨254, by rfl⟩) (B 509 (by norm_num) ⟨254, by rfl⟩ (by norm_num))
theorem R86873 : Reach 86873 := rs (se 2 (by rfl) ⟨32577, by rfl⟩) (B 65155 (by norm_num) ⟨32577, by rfl⟩ (by norm_num))
theorem R86877 : Reach 86877 := rs (se 3 (by rfl) ⟨16289, by rfl⟩) (B 32579 (by norm_num) ⟨16289, by rfl⟩ (by norm_num))
theorem R86881 : Reach 86881 := rs (se 2 (by rfl) ⟨32580, by rfl⟩) (B 65161 (by norm_num) ⟨32580, by rfl⟩ (by norm_num))
theorem R86885 : Reach 86885 := rs (se 4 (by rfl) ⟨8145, by rfl⟩) (B 16291 (by norm_num) ⟨8145, by rfl⟩ (by norm_num))
theorem R86889 : Reach 86889 := rs (se 2 (by rfl) ⟨32583, by rfl⟩) (B 65167 (by norm_num) ⟨32583, by rfl⟩ (by norm_num))
theorem R86893 : Reach 86893 := rs (se 3 (by rfl) ⟨16292, by rfl⟩) (B 32585 (by norm_num) ⟨16292, by rfl⟩ (by norm_num))
theorem R86897 : Reach 86897 := rs (se 2 (by rfl) ⟨32586, by rfl⟩) (B 65173 (by norm_num) ⟨32586, by rfl⟩ (by norm_num))
theorem R86901 : Reach 86901 := rs (se 5 (by rfl) ⟨4073, by rfl⟩) (B 8147 (by norm_num) ⟨4073, by rfl⟩ (by norm_num))
theorem R86905 : Reach 86905 := rs (se 2 (by rfl) ⟨32589, by rfl⟩) (B 65179 (by norm_num) ⟨32589, by rfl⟩ (by norm_num))
theorem R86909 : Reach 86909 := rs (se 3 (by rfl) ⟨16295, by rfl⟩) (B 32591 (by norm_num) ⟨16295, by rfl⟩ (by norm_num))
theorem R86913 : Reach 86913 := rs (se 2 (by rfl) ⟨32592, by rfl⟩) (B 65185 (by norm_num) ⟨32592, by rfl⟩ (by norm_num))
theorem R86917 : Reach 86917 := rs (se 4 (by rfl) ⟨8148, by rfl⟩) (B 16297 (by norm_num) ⟨8148, by rfl⟩ (by norm_num))
theorem R86921 : Reach 86921 := rs (se 2 (by rfl) ⟨32595, by rfl⟩) (B 65191 (by norm_num) ⟨32595, by rfl⟩ (by norm_num))
theorem R86925 : Reach 86925 := rs (se 3 (by rfl) ⟨16298, by rfl⟩) (B 32597 (by norm_num) ⟨16298, by rfl⟩ (by norm_num))
theorem R86929 : Reach 86929 := rs (se 2 (by rfl) ⟨32598, by rfl⟩) (B 65197 (by norm_num) ⟨32598, by rfl⟩ (by norm_num))
theorem R86933 : Reach 86933 := rs (se 6 (by rfl) ⟨2037, by rfl⟩) (B 4075 (by norm_num) ⟨2037, by rfl⟩ (by norm_num))
theorem R86937 : Reach 86937 := rs (se 2 (by rfl) ⟨32601, by rfl⟩) (B 65203 (by norm_num) ⟨32601, by rfl⟩ (by norm_num))
theorem R86941 : Reach 86941 := rs (se 3 (by rfl) ⟨16301, by rfl⟩) (B 32603 (by norm_num) ⟨16301, by rfl⟩ (by norm_num))
theorem R86945 : Reach 86945 := rs (se 2 (by rfl) ⟨32604, by rfl⟩) (B 65209 (by norm_num) ⟨32604, by rfl⟩ (by norm_num))
theorem R316325 : Reach 316325 := rs (se 4 (by rfl) ⟨29655, by rfl⟩) (B 59311 (by norm_num) ⟨29655, by rfl⟩ (by norm_num))
theorem R86949 : Reach 86949 := rs (se 4 (by rfl) ⟨8151, by rfl⟩) (B 16303 (by norm_num) ⟨8151, by rfl⟩ (by norm_num))
theorem R86953 : Reach 86953 := rs (se 2 (by rfl) ⟨32607, by rfl⟩) (B 65215 (by norm_num) ⟨32607, by rfl⟩ (by norm_num))
theorem R86957 : Reach 86957 := rs (se 3 (by rfl) ⟨16304, by rfl⟩) (B 32609 (by norm_num) ⟨16304, by rfl⟩ (by norm_num))
theorem R86961 : Reach 86961 := rs (se 2 (by rfl) ⟨32610, by rfl⟩) (B 65221 (by norm_num) ⟨32610, by rfl⟩ (by norm_num))
theorem R250805 : Reach 250805 := rs (se 5 (by rfl) ⟨11756, by rfl⟩) (B 23513 (by norm_num) ⟨11756, by rfl⟩ (by norm_num))
theorem R86965 : Reach 86965 := rs (se 5 (by rfl) ⟨4076, by rfl⟩) (B 8153 (by norm_num) ⟨4076, by rfl⟩ (by norm_num))
theorem R86969 : Reach 86969 := rs (se 2 (by rfl) ⟨32613, by rfl⟩) (B 65227 (by norm_num) ⟨32613, by rfl⟩ (by norm_num))
theorem R86973 : Reach 86973 := rs (se 3 (by rfl) ⟨16307, by rfl⟩) (B 32615 (by norm_num) ⟨16307, by rfl⟩ (by norm_num))
theorem R86977 : Reach 86977 := rs (se 2 (by rfl) ⟨32616, by rfl⟩) (B 65233 (by norm_num) ⟨32616, by rfl⟩ (by norm_num))
theorem R86981 : Reach 86981 := rs (se 4 (by rfl) ⟨8154, by rfl⟩) (B 16309 (by norm_num) ⟨8154, by rfl⟩ (by norm_num))
theorem R86985 : Reach 86985 := rs (se 2 (by rfl) ⟨32619, by rfl⟩) (B 65239 (by norm_num) ⟨32619, by rfl⟩ (by norm_num))
theorem R152525 : Reach 152525 := rs (se 3 (by rfl) ⟨28598, by rfl⟩) (B 57197 (by norm_num) ⟨28598, by rfl⟩ (by norm_num))
theorem R86989 : Reach 86989 := rs (se 3 (by rfl) ⟨16310, by rfl⟩) (B 32621 (by norm_num) ⟨16310, by rfl⟩ (by norm_num))
theorem R86993 : Reach 86993 := rs (se 2 (by rfl) ⟨32622, by rfl⟩) (B 65245 (by norm_num) ⟨32622, by rfl⟩ (by norm_num))
theorem R807893 : Reach 807893 := rs (se 7 (by rfl) ⟨9467, by rfl⟩) (B 18935 (by norm_num) ⟨9467, by rfl⟩ (by norm_num))
theorem R86997 : Reach 86997 := rs (se 7 (by rfl) ⟨1019, by rfl⟩) (B 2039 (by norm_num) ⟨1019, by rfl⟩ (by norm_num))
theorem R87001 : Reach 87001 := rs (se 2 (by rfl) ⟨32625, by rfl⟩) (B 65251 (by norm_num) ⟨32625, by rfl⟩ (by norm_num))
theorem R87005 : Reach 87005 := rs (se 3 (by rfl) ⟨16313, by rfl⟩) (B 32627 (by norm_num) ⟨16313, by rfl⟩ (by norm_num))
theorem R87009 : Reach 87009 := rs (se 2 (by rfl) ⟨32628, by rfl⟩) (B 65257 (by norm_num) ⟨32628, by rfl⟩ (by norm_num))
theorem R87013 : Reach 87013 := rs (se 4 (by rfl) ⟨8157, by rfl⟩) (B 16315 (by norm_num) ⟨8157, by rfl⟩ (by norm_num))
theorem R87017 : Reach 87017 := rs (se 2 (by rfl) ⟨32631, by rfl⟩) (B 65263 (by norm_num) ⟨32631, by rfl⟩ (by norm_num))
theorem R87021 : Reach 87021 := rs (se 3 (by rfl) ⟨16316, by rfl⟩) (B 32633 (by norm_num) ⟨16316, by rfl⟩ (by norm_num))
theorem R87025 : Reach 87025 := rs (se 2 (by rfl) ⟨32634, by rfl⟩) (B 65269 (by norm_num) ⟨32634, by rfl⟩ (by norm_num))
theorem R87029 : Reach 87029 := rs (se 5 (by rfl) ⟨4079, by rfl⟩) (B 8159 (by norm_num) ⟨4079, by rfl⟩ (by norm_num))
theorem R87033 : Reach 87033 := rs (se 2 (by rfl) ⟨32637, by rfl⟩) (B 65275 (by norm_num) ⟨32637, by rfl⟩ (by norm_num))
theorem R185341 : Reach 185341 := rs (se 3 (by rfl) ⟨34751, by rfl⟩) (B 69503 (by norm_num) ⟨34751, by rfl⟩ (by norm_num))
theorem R87037 : Reach 87037 := rs (se 3 (by rfl) ⟨16319, by rfl⟩) (B 32639 (by norm_num) ⟨16319, by rfl⟩ (by norm_num))
theorem R87041 : Reach 87041 := rs (se 2 (by rfl) ⟨32640, by rfl⟩) (B 65281 (by norm_num) ⟨32640, by rfl⟩ (by norm_num))
theorem R87045 : Reach 87045 := rs (se 4 (by rfl) ⟨8160, by rfl⟩) (B 16321 (by norm_num) ⟨8160, by rfl⟩ (by norm_num))
theorem R87049 : Reach 87049 := rs (se 2 (by rfl) ⟨32643, by rfl⟩) (B 65287 (by norm_num) ⟨32643, by rfl⟩ (by norm_num))
theorem R87053 : Reach 87053 := rs (se 3 (by rfl) ⟨16322, by rfl⟩) (B 32645 (by norm_num) ⟨16322, by rfl⟩ (by norm_num))
theorem R87057 : Reach 87057 := rs (se 2 (by rfl) ⟨32646, by rfl⟩) (B 65293 (by norm_num) ⟨32646, by rfl⟩ (by norm_num))
theorem R87061 : Reach 87061 := rs (se 6 (by rfl) ⟨2040, by rfl⟩) (B 4081 (by norm_num) ⟨2040, by rfl⟩ (by norm_num))
theorem R87065 : Reach 87065 := rs (se 2 (by rfl) ⟨32649, by rfl⟩) (B 65299 (by norm_num) ⟨32649, by rfl⟩ (by norm_num))
theorem R87069 : Reach 87069 := rs (se 3 (by rfl) ⟨16325, by rfl⟩) (B 32651 (by norm_num) ⟨16325, by rfl⟩ (by norm_num))
theorem R87073 : Reach 87073 := rs (se 2 (by rfl) ⟨32652, by rfl⟩) (B 65305 (by norm_num) ⟨32652, by rfl⟩ (by norm_num))
theorem R87077 : Reach 87077 := rs (se 4 (by rfl) ⟨8163, by rfl⟩) (B 16327 (by norm_num) ⟨8163, by rfl⟩ (by norm_num))
theorem R87081 : Reach 87081 := rs (se 2 (by rfl) ⟨32655, by rfl⟩) (B 65311 (by norm_num) ⟨32655, by rfl⟩ (by norm_num))
theorem R87085 : Reach 87085 := rs (se 3 (by rfl) ⟨16328, by rfl⟩) (B 32657 (by norm_num) ⟨16328, by rfl⟩ (by norm_num))
theorem R87089 : Reach 87089 := rs (se 2 (by rfl) ⟨32658, by rfl⟩) (B 65317 (by norm_num) ⟨32658, by rfl⟩ (by norm_num))
theorem R87093 : Reach 87093 := rs (se 5 (by rfl) ⟨4082, by rfl⟩) (B 8165 (by norm_num) ⟨4082, by rfl⟩ (by norm_num))
theorem R87097 : Reach 87097 := rs (se 2 (by rfl) ⟨32661, by rfl⟩) (B 65323 (by norm_num) ⟨32661, by rfl⟩ (by norm_num))
theorem R218173 : Reach 218173 := rs (se 3 (by rfl) ⟨40907, by rfl⟩) (B 81815 (by norm_num) ⟨40907, by rfl⟩ (by norm_num))
theorem R87101 : Reach 87101 := rs (se 3 (by rfl) ⟨16331, by rfl⟩) (B 32663 (by norm_num) ⟨16331, by rfl⟩ (by norm_num))
theorem R87105 : Reach 87105 := rs (se 2 (by rfl) ⟨32664, by rfl⟩) (B 65329 (by norm_num) ⟨32664, by rfl⟩ (by norm_num))
theorem R87109 : Reach 87109 := rs (se 4 (by rfl) ⟨8166, by rfl⟩) (B 16333 (by norm_num) ⟨8166, by rfl⟩ (by norm_num))
theorem R87113 : Reach 87113 := rs (se 2 (by rfl) ⟨32667, by rfl⟩) (B 65335 (by norm_num) ⟨32667, by rfl⟩ (by norm_num))
theorem R87117 : Reach 87117 := rs (se 3 (by rfl) ⟨16334, by rfl⟩) (B 32669 (by norm_num) ⟨16334, by rfl⟩ (by norm_num))
theorem R87121 : Reach 87121 := rs (se 2 (by rfl) ⟨32670, by rfl⟩) (B 65341 (by norm_num) ⟨32670, by rfl⟩ (by norm_num))
theorem R87125 : Reach 87125 := rs (se 8 (by rfl) ⟨510, by rfl⟩) (B 1021 (by norm_num) ⟨510, by rfl⟩ (by norm_num))
theorem R152669 : Reach 152669 := rs (se 3 (by rfl) ⟨28625, by rfl⟩) (B 57251 (by norm_num) ⟨28625, by rfl⟩ (by norm_num))
theorem R185485 : Reach 185485 := rs (se 3 (by rfl) ⟨34778, by rfl⟩) (B 69557 (by norm_num) ⟨34778, by rfl⟩ (by norm_num))
theorem R218285 : Reach 218285 := rs (se 3 (by rfl) ⟨40928, by rfl⟩) (B 81857 (by norm_num) ⟨40928, by rfl⟩ (by norm_num))
theorem R119989 : Reach 119989 := rs (se 5 (by rfl) ⟨5624, by rfl⟩) (B 11249 (by norm_num) ⟨5624, by rfl⟩ (by norm_num))
theorem R283877 : Reach 283877 := rs (se 4 (by rfl) ⟨26613, by rfl⟩) (B 53227 (by norm_num) ⟨26613, by rfl⟩ (by norm_num))
theorem R152813 : Reach 152813 := rs (se 3 (by rfl) ⟨28652, by rfl⟩) (B 57305 (by norm_num) ⟨28652, by rfl⟩ (by norm_num))
theorem R152885 : Reach 152885 := rs (se 5 (by rfl) ⟨7166, by rfl⟩) (B 14333 (by norm_num) ⟨7166, by rfl⟩ (by norm_num))
theorem R349541 : Reach 349541 := rs (se 4 (by rfl) ⟨32769, by rfl⟩) (B 65539 (by norm_num) ⟨32769, by rfl⟩ (by norm_num))
theorem R218477 : Reach 218477 := rs (se 3 (by rfl) ⟨40964, by rfl⟩) (B 81929 (by norm_num) ⟨40964, by rfl⟩ (by norm_num))
theorem R1037717 : Reach 1037717 := rs (se 6 (by rfl) ⟨24321, by rfl⟩) (B 48643 (by norm_num) ⟨24321, by rfl⟩ (by norm_num))
theorem R185861 : Reach 185861 := rs (se 4 (by rfl) ⟨17424, by rfl⟩) (B 34849 (by norm_num) ⟨17424, by rfl⟩ (by norm_num))
theorem R349733 : Reach 349733 := rs (se 4 (by rfl) ⟨32787, by rfl⟩) (B 65575 (by norm_num) ⟨32787, by rfl⟩ (by norm_num))
theorem R87685 : Reach 87685 := rs (se 4 (by rfl) ⟨8220, by rfl⟩) (B 16441 (by norm_num) ⟨8220, by rfl⟩ (by norm_num))
theorem R284309 : Reach 284309 := rs (se 6 (by rfl) ⟨6663, by rfl⟩) (B 13327 (by norm_num) ⟨6663, by rfl⟩ (by norm_num))
theorem R218821 : Reach 218821 := rs (se 4 (by rfl) ⟨20514, by rfl⟩) (B 41029 (by norm_num) ⟨20514, by rfl⟩ (by norm_num))
theorem R218933 : Reach 218933 := rs (se 5 (by rfl) ⟨10262, by rfl⟩) (B 20525 (by norm_num) ⟨10262, by rfl⟩ (by norm_num))
theorem R120781 : Reach 120781 := rs (se 3 (by rfl) ⟨22646, by rfl⟩) (B 45293 (by norm_num) ⟨22646, by rfl⟩ (by norm_num))
theorem R219125 : Reach 219125 := rs (se 5 (by rfl) ⟨10271, by rfl⟩) (B 20543 (by norm_num) ⟨10271, by rfl⟩ (by norm_num))
theorem R481301 : Reach 481301 := rs (se 6 (by rfl) ⟨11280, by rfl⟩) (B 22561 (by norm_num) ⟨11280, by rfl⟩ (by norm_num))
theorem R284741 : Reach 284741 := rs (se 4 (by rfl) ⟨26694, by rfl⟩) (B 53389 (by norm_num) ⟨26694, by rfl⟩ (by norm_num))
theorem R121117 : Reach 121117 := rs (se 3 (by rfl) ⟨22709, by rfl⟩) (B 45419 (by norm_num) ⟨22709, by rfl⟩ (by norm_num))
theorem R219469 : Reach 219469 := rs (se 3 (by rfl) ⟨41150, by rfl⟩) (B 82301 (by norm_num) ⟨41150, by rfl⟩ (by norm_num))
theorem R219581 : Reach 219581 := rs (se 3 (by rfl) ⟨41171, by rfl⟩) (B 82343 (by norm_num) ⟨41171, by rfl⟩ (by norm_num))
theorem R285173 : Reach 285173 := rs (se 5 (by rfl) ⟨13367, by rfl⟩) (B 26735 (by norm_num) ⟨13367, by rfl⟩ (by norm_num))
theorem R121333 : Reach 121333 := rs (se 5 (by rfl) ⟨5687, by rfl⟩) (B 11375 (by norm_num) ⟨5687, by rfl⟩ (by norm_num))
theorem R154133 : Reach 154133 := rs (se 6 (by rfl) ⟨3612, by rfl⟩) (B 7225 (by norm_num) ⟨3612, by rfl⟩ (by norm_num))
theorem R383525 : Reach 383525 := rs (se 4 (by rfl) ⟨35955, by rfl⟩) (B 71911 (by norm_num) ⟨35955, by rfl⟩ (by norm_num))
theorem R219773 : Reach 219773 := rs (se 3 (by rfl) ⟨41207, by rfl⟩) (B 82415 (by norm_num) ⟨41207, by rfl⟩ (by norm_num))
theorem R187109 : Reach 187109 := rs (se 4 (by rfl) ⟨17541, by rfl⟩) (B 35083 (by norm_num) ⟨17541, by rfl⟩ (by norm_num))
theorem R88813 : Reach 88813 := rs (se 3 (by rfl) ⟨16652, by rfl⟩) (B 33305 (by norm_num) ⟨16652, by rfl⟩ (by norm_num))
theorem R187181 : Reach 187181 := rs (se 3 (by rfl) ⟨35096, by rfl⟩) (B 70193 (by norm_num) ⟨35096, by rfl⟩ (by norm_num))
theorem R121709 : Reach 121709 := rs (se 3 (by rfl) ⟨22820, by rfl⟩) (B 45641 (by norm_num) ⟨22820, by rfl⟩ (by norm_num))
theorem R187253 : Reach 187253 := rs (se 5 (by rfl) ⟨8777, by rfl⟩) (B 17555 (by norm_num) ⟨8777, by rfl⟩ (by norm_num))
theorem R285605 : Reach 285605 := rs (se 4 (by rfl) ⟨26775, by rfl⟩) (B 53551 (by norm_num) ⟨26775, by rfl⟩ (by norm_num))
theorem R187325 : Reach 187325 := rs (se 3 (by rfl) ⟨35123, by rfl⟩) (B 70247 (by norm_num) ⟨35123, by rfl⟩ (by norm_num))
theorem R220117 : Reach 220117 := rs (se 7 (by rfl) ⟨2579, by rfl⟩) (B 5159 (by norm_num) ⟨2579, by rfl⟩ (by norm_num))
theorem R318437 : Reach 318437 := rs (se 4 (by rfl) ⟨29853, by rfl⟩) (B 59707 (by norm_num) ⟨29853, by rfl⟩ (by norm_num))
theorem R187397 : Reach 187397 := rs (se 4 (by rfl) ⟨17568, by rfl⟩) (B 35137 (by norm_num) ⟨17568, by rfl⟩ (by norm_num))
theorem R220229 : Reach 220229 := rs (se 4 (by rfl) ⟨20646, by rfl⟩) (B 41293 (by norm_num) ⟨20646, by rfl⟩ (by norm_num))
theorem R187469 : Reach 187469 := rs (se 3 (by rfl) ⟨35150, by rfl⟩) (B 70301 (by norm_num) ⟨35150, by rfl⟩ (by norm_num))
theorem R613493 : Reach 613493 := rs (se 5 (by rfl) ⟨28757, by rfl⟩) (B 57515 (by norm_num) ⟨28757, by rfl⟩ (by norm_num))
theorem R187525 : Reach 187525 := rs (se 4 (by rfl) ⟨17580, by rfl⟩) (B 35161 (by norm_num) ⟨17580, by rfl⟩ (by norm_num))
theorem R187541 : Reach 187541 := rs (se 6 (by rfl) ⟨4395, by rfl⟩) (B 8791 (by norm_num) ⟨4395, by rfl⟩ (by norm_num))
theorem R220333 : Reach 220333 := rs (se 3 (by rfl) ⟨41312, by rfl⟩) (B 82625 (by norm_num) ⟨41312, by rfl⟩ (by norm_num))
theorem R515285 : Reach 515285 := rs (se 7 (by rfl) ⟨6038, by rfl⟩) (B 12077 (by norm_num) ⟨6038, by rfl⟩ (by norm_num))
theorem R187613 : Reach 187613 := rs (se 3 (by rfl) ⟨35177, by rfl⟩) (B 70355 (by norm_num) ⟨35177, by rfl⟩ (by norm_num))
theorem R318725 : Reach 318725 := rs (se 4 (by rfl) ⟨29880, by rfl⟩) (B 59761 (by norm_num) ⟨29880, by rfl⟩ (by norm_num))
theorem R220421 : Reach 220421 := rs (se 4 (by rfl) ⟨20664, by rfl⟩) (B 41329 (by norm_num) ⟨20664, by rfl⟩ (by norm_num))
theorem R187685 : Reach 187685 := rs (se 4 (by rfl) ⟨17595, by rfl⟩) (B 35191 (by norm_num) ⟨17595, by rfl⟩ (by norm_num))
theorem R220477 : Reach 220477 := rs (se 3 (by rfl) ⟨41339, by rfl⟩) (B 82679 (by norm_num) ⟨41339, by rfl⟩ (by norm_num))
theorem R286037 : Reach 286037 := rs (se 11 (by rfl) ⟨209, by rfl⟩) (B 419 (by norm_num) ⟨209, by rfl⟩ (by norm_num))
theorem R187757 : Reach 187757 := rs (se 3 (by rfl) ⟨35204, by rfl⟩) (B 70409 (by norm_num) ⟨35204, by rfl⟩ (by norm_num))
theorem R187829 : Reach 187829 := rs (se 5 (by rfl) ⟨8804, by rfl⟩) (B 17609 (by norm_num) ⟨8804, by rfl⟩ (by norm_num))
theorem R187901 : Reach 187901 := rs (se 3 (by rfl) ⟨35231, by rfl⟩) (B 70463 (by norm_num) ⟨35231, by rfl⟩ (by norm_num))
theorem R89633 : Reach 89633 := rs (se 2 (by rfl) ⟨33612, by rfl⟩) (B 67225 (by norm_num) ⟨33612, by rfl⟩ (by norm_num))
theorem R187973 : Reach 187973 := rs (se 4 (by rfl) ⟨17622, by rfl⟩) (B 35245 (by norm_num) ⟨17622, by rfl⟩ (by norm_num))
theorem R188045 : Reach 188045 := rs (se 3 (by rfl) ⟨35258, by rfl⟩) (B 70517 (by norm_num) ⟨35258, by rfl⟩ (by norm_num))
theorem R188117 : Reach 188117 := rs (se 7 (by rfl) ⟨2204, by rfl⟩) (B 4409 (by norm_num) ⟨2204, by rfl⟩ (by norm_num))
theorem R351989 : Reach 351989 := rs (se 5 (by rfl) ⟨16499, by rfl⟩) (B 32999 (by norm_num) ⟨16499, by rfl⟩ (by norm_num))
theorem R286469 : Reach 286469 := rs (se 4 (by rfl) ⟨26856, by rfl⟩) (B 53713 (by norm_num) ⟨26856, by rfl⟩ (by norm_num))
theorem R188189 : Reach 188189 := rs (se 3 (by rfl) ⟨35285, by rfl⟩) (B 70571 (by norm_num) ⟨35285, by rfl⟩ (by norm_num))
theorem R188261 : Reach 188261 := rs (se 4 (by rfl) ⟨17649, by rfl⟩) (B 35299 (by norm_num) ⟨17649, by rfl⟩ (by norm_num))
theorem R581525 : Reach 581525 := rs (se 6 (by rfl) ⟨13629, by rfl⟩) (B 27259 (by norm_num) ⟨13629, by rfl⟩ (by norm_num))
theorem R188333 : Reach 188333 := rs (se 3 (by rfl) ⟨35312, by rfl⟩) (B 70625 (by norm_num) ⟨35312, by rfl⟩ (by norm_num))
theorem R90077 : Reach 90077 := rs (se 3 (by rfl) ⟨16889, by rfl⟩) (B 33779 (by norm_num) ⟨16889, by rfl⟩ (by norm_num))
theorem R188405 : Reach 188405 := rs (se 5 (by rfl) ⟨8831, by rfl⟩) (B 17663 (by norm_num) ⟨8831, by rfl⟩ (by norm_num))
theorem R188477 : Reach 188477 := rs (se 3 (by rfl) ⟨35339, by rfl⟩) (B 70679 (by norm_num) ⟨35339, by rfl⟩ (by norm_num))
theorem R188549 : Reach 188549 := rs (se 4 (by rfl) ⟨17676, by rfl⟩) (B 35353 (by norm_num) ⟨17676, by rfl⟩ (by norm_num))
theorem R483509 : Reach 483509 := rs (se 5 (by rfl) ⟨22664, by rfl⟩) (B 45329 (by norm_num) ⟨22664, by rfl⟩ (by norm_num))
theorem R286901 : Reach 286901 := rs (se 5 (by rfl) ⟨13448, by rfl⟩) (B 26897 (by norm_num) ⟨13448, by rfl⟩ (by norm_num))
theorem R123077 : Reach 123077 := rs (se 4 (by rfl) ⟨11538, by rfl⟩) (B 23077 (by norm_num) ⟨11538, by rfl⟩ (by norm_num))
theorem R188621 : Reach 188621 := rs (se 3 (by rfl) ⟨35366, by rfl⟩) (B 70733 (by norm_num) ⟨35366, by rfl⟩ (by norm_num))
theorem R90325 : Reach 90325 := rs (se 7 (by rfl) ⟨1058, by rfl⟩) (B 2117 (by norm_num) ⟨1058, by rfl⟩ (by norm_num))
theorem R123133 : Reach 123133 := rs (se 3 (by rfl) ⟨23087, by rfl⟩) (B 46175 (by norm_num) ⟨23087, by rfl⟩ (by norm_num))
theorem R188693 : Reach 188693 := rs (se 6 (by rfl) ⟨4422, by rfl⟩) (B 8845 (by norm_num) ⟨4422, by rfl⟩ (by norm_num))
theorem R188765 : Reach 188765 := rs (se 3 (by rfl) ⟨35393, by rfl⟩) (B 70787 (by norm_num) ⟨35393, by rfl⟩ (by norm_num))
theorem R188837 : Reach 188837 := rs (se 4 (by rfl) ⟨17703, by rfl⟩) (B 35407 (by norm_num) ⟨17703, by rfl⟩ (by norm_num))
theorem R319909 : Reach 319909 := rs (se 4 (by rfl) ⟨29991, by rfl⟩) (B 59983 (by norm_num) ⟨29991, by rfl⟩ (by norm_num))
theorem R188909 : Reach 188909 := rs (se 3 (by rfl) ⟨35420, by rfl⟩) (B 70841 (by norm_num) ⟨35420, by rfl⟩ (by norm_num))
theorem R156157 : Reach 156157 := rs (se 3 (by rfl) ⟨29279, by rfl⟩) (B 58559 (by norm_num) ⟨29279, by rfl⟩ (by norm_num))
theorem R221717 : Reach 221717 := rs (se 6 (by rfl) ⟨5196, by rfl⟩) (B 10393 (by norm_num) ⟨5196, by rfl⟩ (by norm_num))
theorem R188981 : Reach 188981 := rs (se 5 (by rfl) ⟨8858, by rfl⟩) (B 17717 (by norm_num) ⟨8858, by rfl⟩ (by norm_num))
theorem R287333 : Reach 287333 := rs (se 4 (by rfl) ⟨26937, by rfl⟩) (B 53875 (by norm_num) ⟨26937, by rfl⟩ (by norm_num))
theorem R189053 : Reach 189053 := rs (se 3 (by rfl) ⟨35447, by rfl⟩) (B 70895 (by norm_num) ⟨35447, by rfl⟩ (by norm_num))
theorem R90757 : Reach 90757 := rs (se 4 (by rfl) ⟨8508, by rfl⟩) (B 17017 (by norm_num) ⟨8508, by rfl⟩ (by norm_num))
theorem R189125 : Reach 189125 := rs (se 4 (by rfl) ⟨17730, by rfl⟩) (B 35461 (by norm_num) ⟨17730, by rfl⟩ (by norm_num))
theorem R123589 : Reach 123589 := rs (se 4 (by rfl) ⟨11586, by rfl⟩) (B 23173 (by norm_num) ⟨11586, by rfl⟩ (by norm_num))
theorem R90829 : Reach 90829 := rs (se 3 (by rfl) ⟨17030, by rfl⟩) (B 34061 (by norm_num) ⟨17030, by rfl⟩ (by norm_num))
theorem R320213 : Reach 320213 := rs (se 7 (by rfl) ⟨3752, by rfl⟩) (B 7505 (by norm_num) ⟨3752, by rfl⟩ (by norm_num))
theorem R189197 : Reach 189197 := rs (se 3 (by rfl) ⟨35474, by rfl⟩) (B 70949 (by norm_num) ⟨35474, by rfl⟩ (by norm_num))
theorem R123725 : Reach 123725 := rs (se 3 (by rfl) ⟨23198, by rfl⟩) (B 46397 (by norm_num) ⟨23198, by rfl⟩ (by norm_num))
theorem R189269 : Reach 189269 := rs (se 9 (by rfl) ⟨554, by rfl⟩) (B 1109 (by norm_num) ⟨554, by rfl⟩ (by norm_num))
theorem R189341 : Reach 189341 := rs (se 3 (by rfl) ⟨35501, by rfl⟩) (B 71003 (by norm_num) ⟨35501, by rfl⟩ (by norm_num))
theorem R123805 : Reach 123805 := rs (se 3 (by rfl) ⟨23213, by rfl⟩) (B 46427 (by norm_num) ⟨23213, by rfl⟩ (by norm_num))
theorem R189413 : Reach 189413 := rs (se 4 (by rfl) ⟨17757, by rfl⟩) (B 35515 (by norm_num) ⟨17757, by rfl⟩ (by norm_num))
theorem R287765 : Reach 287765 := rs (se 6 (by rfl) ⟨6744, by rfl⟩) (B 13489 (by norm_num) ⟨6744, by rfl⟩ (by norm_num))
theorem R123925 : Reach 123925 := rs (se 6 (by rfl) ⟨2904, by rfl⟩) (B 5809 (by norm_num) ⟨2904, by rfl⟩ (by norm_num))
theorem R189485 : Reach 189485 := rs (se 3 (by rfl) ⟨35528, by rfl⟩) (B 71057 (by norm_num) ⟨35528, by rfl⟩ (by norm_num))
theorem R91201 : Reach 91201 := rs (se 2 (by rfl) ⟨34200, by rfl⟩) (B 68401 (by norm_num) ⟨34200, by rfl⟩ (by norm_num))
theorem R189557 : Reach 189557 := rs (se 5 (by rfl) ⟨8885, by rfl⟩) (B 17771 (by norm_num) ⟨8885, by rfl⟩ (by norm_num))
theorem R124021 : Reach 124021 := rs (se 5 (by rfl) ⟨5813, by rfl⟩) (B 11627 (by norm_num) ⟨5813, by rfl⟩ (by norm_num))
theorem R189629 : Reach 189629 := rs (se 3 (by rfl) ⟨35555, by rfl⟩) (B 71111 (by norm_num) ⟨35555, by rfl⟩ (by norm_num))
theorem R189701 : Reach 189701 := rs (se 4 (by rfl) ⟨17784, by rfl⟩) (B 35569 (by norm_num) ⟨17784, by rfl⟩ (by norm_num))
theorem R877877 : Reach 877877 := rs (se 5 (by rfl) ⟨41150, by rfl⟩) (B 82301 (by norm_num) ⟨41150, by rfl⟩ (by norm_num))
theorem R189773 : Reach 189773 := rs (se 3 (by rfl) ⟨35582, by rfl⟩) (B 71165 (by norm_num) ⟨35582, by rfl⟩ (by norm_num))
theorem R3106133 : Reach 3106133 := rs (se 12 (by rfl) ⟨1137, by rfl⟩) (B 2275 (by norm_num) ⟨1137, by rfl⟩ (by norm_num))
theorem R189845 : Reach 189845 := rs (se 6 (by rfl) ⟨4449, by rfl⟩) (B 8899 (by norm_num) ⟨4449, by rfl⟩ (by norm_num))
theorem R222629 : Reach 222629 := rs (se 4 (by rfl) ⟨20871, by rfl⟩) (B 41743 (by norm_num) ⟨20871, by rfl⟩ (by norm_num))
theorem R91577 : Reach 91577 := rs (se 2 (by rfl) ⟨34341, by rfl⟩) (B 68683 (by norm_num) ⟨34341, by rfl⟩ (by norm_num))
theorem R288197 : Reach 288197 := rs (se 4 (by rfl) ⟨27018, by rfl⟩) (B 54037 (by norm_num) ⟨27018, by rfl⟩ (by norm_num))
theorem R189917 : Reach 189917 := rs (se 3 (by rfl) ⟨35609, by rfl⟩) (B 71219 (by norm_num) ⟨35609, by rfl⟩ (by norm_num))
theorem R157165 : Reach 157165 := rs (se 3 (by rfl) ⟨29468, by rfl⟩) (B 58937 (by norm_num) ⟨29468, by rfl⟩ (by norm_num))
theorem R91649 : Reach 91649 := rs (se 2 (by rfl) ⟨34368, by rfl⟩) (B 68737 (by norm_num) ⟨34368, by rfl⟩ (by norm_num))
theorem R189989 : Reach 189989 := rs (se 4 (by rfl) ⟨17811, by rfl⟩) (B 35623 (by norm_num) ⟨17811, by rfl⟩ (by norm_num))
theorem R190061 : Reach 190061 := rs (se 3 (by rfl) ⟨35636, by rfl⟩) (B 71273 (by norm_num) ⟨35636, by rfl⟩ (by norm_num))
theorem R190133 : Reach 190133 := rs (se 5 (by rfl) ⟨8912, by rfl⟩) (B 17825 (by norm_num) ⟨8912, by rfl⟩ (by norm_num))
theorem R91837 : Reach 91837 := rs (se 3 (by rfl) ⟨17219, by rfl⟩) (B 34439 (by norm_num) ⟨17219, by rfl⟩ (by norm_num))
theorem R190205 : Reach 190205 := rs (se 3 (by rfl) ⟨35663, by rfl⟩) (B 71327 (by norm_num) ⟨35663, by rfl⟩ (by norm_num))
theorem R124709 : Reach 124709 := rs (se 4 (by rfl) ⟨11691, by rfl⟩) (B 23383 (by norm_num) ⟨11691, by rfl⟩ (by norm_num))
theorem R124733 : Reach 124733 := rs (se 3 (by rfl) ⟨23387, by rfl⟩) (B 46775 (by norm_num) ⟨23387, by rfl⟩ (by norm_num))
theorem R190277 : Reach 190277 := rs (se 4 (by rfl) ⟨17838, by rfl⟩) (B 35677 (by norm_num) ⟨17838, by rfl⟩ (by norm_num))
theorem R124757 : Reach 124757 := rs (se 9 (by rfl) ⟨365, by rfl⟩) (B 731 (by norm_num) ⟨365, by rfl⟩ (by norm_num))
theorem R124781 : Reach 124781 := rs (se 3 (by rfl) ⟨23396, by rfl⟩) (B 46793 (by norm_num) ⟨23396, by rfl⟩ (by norm_num))
theorem R288629 : Reach 288629 := rs (se 5 (by rfl) ⟨13529, by rfl⟩) (B 27059 (by norm_num) ⟨13529, by rfl⟩ (by norm_num))
theorem R92021 : Reach 92021 := rs (se 5 (by rfl) ⟨4313, by rfl⟩) (B 8627 (by norm_num) ⟨4313, by rfl⟩ (by norm_num))
theorem R124805 : Reach 124805 := rs (se 4 (by rfl) ⟨11700, by rfl⟩) (B 23401 (by norm_num) ⟨11700, by rfl⟩ (by norm_num))
theorem R190349 : Reach 190349 := rs (se 3 (by rfl) ⟨35690, by rfl⟩) (B 71381 (by norm_num) ⟨35690, by rfl⟩ (by norm_num))
theorem R124829 : Reach 124829 := rs (se 3 (by rfl) ⟨23405, by rfl⟩) (B 46811 (by norm_num) ⟨23405, by rfl⟩ (by norm_num))
theorem R124853 : Reach 124853 := rs (se 5 (by rfl) ⟨5852, by rfl⟩) (B 11705 (by norm_num) ⟨5852, by rfl⟩ (by norm_num))
theorem R124877 : Reach 124877 := rs (se 3 (by rfl) ⟨23414, by rfl⟩) (B 46829 (by norm_num) ⟨23414, by rfl⟩ (by norm_num))
theorem R190421 : Reach 190421 := rs (se 7 (by rfl) ⟨2231, by rfl⟩) (B 4463 (by norm_num) ⟨2231, by rfl⟩ (by norm_num))
theorem R124901 : Reach 124901 := rs (se 4 (by rfl) ⟨11709, by rfl⟩) (B 23419 (by norm_num) ⟨11709, by rfl⟩ (by norm_num))
theorem R124925 : Reach 124925 := rs (se 3 (by rfl) ⟨23423, by rfl⟩) (B 46847 (by norm_num) ⟨23423, by rfl⟩ (by norm_num))
theorem R124949 : Reach 124949 := rs (se 6 (by rfl) ⟨2928, by rfl⟩) (B 5857 (by norm_num) ⟨2928, by rfl⟩ (by norm_num))
theorem R1107989 : Reach 1107989 := rs (se 6 (by rfl) ⟨25968, by rfl⟩) (B 51937 (by norm_num) ⟨25968, by rfl⟩ (by norm_num))
theorem R190493 : Reach 190493 := rs (se 3 (by rfl) ⟨35717, by rfl⟩) (B 71435 (by norm_num) ⟨35717, by rfl⟩ (by norm_num))
theorem R124973 : Reach 124973 := rs (se 3 (by rfl) ⟨23432, by rfl⟩) (B 46865 (by norm_num) ⟨23432, by rfl⟩ (by norm_num))
theorem R124997 : Reach 124997 := rs (se 4 (by rfl) ⟨11718, by rfl⟩) (B 23437 (by norm_num) ⟨11718, by rfl⟩ (by norm_num))
theorem R125021 : Reach 125021 := rs (se 3 (by rfl) ⟨23441, by rfl⟩) (B 46883 (by norm_num) ⟨23441, by rfl⟩ (by norm_num))
theorem R190565 : Reach 190565 := rs (se 4 (by rfl) ⟨17865, by rfl⟩) (B 35731 (by norm_num) ⟨17865, by rfl⟩ (by norm_num))
theorem R125045 : Reach 125045 := rs (se 5 (by rfl) ⟨5861, by rfl⟩) (B 11723 (by norm_num) ⟨5861, by rfl⟩ (by norm_num))
theorem R125069 : Reach 125069 := rs (se 3 (by rfl) ⟨23450, by rfl⟩) (B 46901 (by norm_num) ⟨23450, by rfl⟩ (by norm_num))
theorem R125093 : Reach 125093 := rs (se 4 (by rfl) ⟨11727, by rfl⟩) (B 23455 (by norm_num) ⟨11727, by rfl⟩ (by norm_num))
theorem R190637 : Reach 190637 := rs (se 3 (by rfl) ⟨35744, by rfl⟩) (B 71489 (by norm_num) ⟨35744, by rfl⟩ (by norm_num))
theorem R125117 : Reach 125117 := rs (se 3 (by rfl) ⟨23459, by rfl⟩) (B 46919 (by norm_num) ⟨23459, by rfl⟩ (by norm_num))
theorem R125141 : Reach 125141 := rs (se 7 (by rfl) ⟨1466, by rfl⟩) (B 2933 (by norm_num) ⟨1466, by rfl⟩ (by norm_num))
theorem R125165 : Reach 125165 := rs (se 3 (by rfl) ⟨23468, by rfl⟩) (B 46937 (by norm_num) ⟨23468, by rfl⟩ (by norm_num))
theorem R190709 : Reach 190709 := rs (se 5 (by rfl) ⟨8939, by rfl⟩) (B 17879 (by norm_num) ⟨8939, by rfl⟩ (by norm_num))
theorem R125189 : Reach 125189 := rs (se 4 (by rfl) ⟨11736, by rfl⟩) (B 23473 (by norm_num) ⟨11736, by rfl⟩ (by norm_num))
theorem R125213 : Reach 125213 := rs (se 3 (by rfl) ⟨23477, by rfl⟩) (B 46955 (by norm_num) ⟨23477, by rfl⟩ (by norm_num))
theorem R289061 : Reach 289061 := rs (se 4 (by rfl) ⟨27099, by rfl⟩) (B 54199 (by norm_num) ⟨27099, by rfl⟩ (by norm_num))
theorem R125237 : Reach 125237 := rs (se 5 (by rfl) ⟨5870, by rfl⟩) (B 11741 (by norm_num) ⟨5870, by rfl⟩ (by norm_num))
theorem R190781 : Reach 190781 := rs (se 3 (by rfl) ⟨35771, by rfl⟩) (B 71543 (by norm_num) ⟨35771, by rfl⟩ (by norm_num))
theorem R125261 : Reach 125261 := rs (se 3 (by rfl) ⟨23486, by rfl⟩) (B 46973 (by norm_num) ⟨23486, by rfl⟩ (by norm_num))
theorem R125285 : Reach 125285 := rs (se 4 (by rfl) ⟨11745, by rfl⟩) (B 23491 (by norm_num) ⟨11745, by rfl⟩ (by norm_num))
theorem R125309 : Reach 125309 := rs (se 3 (by rfl) ⟨23495, by rfl⟩) (B 46991 (by norm_num) ⟨23495, by rfl⟩ (by norm_num))
theorem R190853 : Reach 190853 := rs (se 4 (by rfl) ⟨17892, by rfl⟩) (B 35785 (by norm_num) ⟨17892, by rfl⟩ (by norm_num))
theorem R125333 : Reach 125333 := rs (se 6 (by rfl) ⟨2937, by rfl⟩) (B 5875 (by norm_num) ⟨2937, by rfl⟩ (by norm_num))
theorem R158125 : Reach 158125 := rs (se 3 (by rfl) ⟨29648, by rfl⟩) (B 59297 (by norm_num) ⟨29648, by rfl⟩ (by norm_num))
theorem R125357 : Reach 125357 := rs (se 3 (by rfl) ⟨23504, by rfl⟩) (B 47009 (by norm_num) ⟨23504, by rfl⟩ (by norm_num))
theorem R125381 : Reach 125381 := rs (se 4 (by rfl) ⟨11754, by rfl⟩) (B 23509 (by norm_num) ⟨11754, by rfl⟩ (by norm_num))
theorem R190925 : Reach 190925 := rs (se 3 (by rfl) ⟨35798, by rfl⟩) (B 71597 (by norm_num) ⟨35798, by rfl⟩ (by norm_num))
theorem R125405 : Reach 125405 := rs (se 3 (by rfl) ⟨23513, by rfl⟩) (B 47027 (by norm_num) ⟨23513, by rfl⟩ (by norm_num))
theorem R125429 : Reach 125429 := rs (se 5 (by rfl) ⟨5879, by rfl⟩) (B 11759 (by norm_num) ⟨5879, by rfl⟩ (by norm_num))
theorem R125453 : Reach 125453 := rs (se 3 (by rfl) ⟨23522, by rfl⟩) (B 47045 (by norm_num) ⟨23522, by rfl⟩ (by norm_num))
theorem R190997 : Reach 190997 := rs (se 6 (by rfl) ⟨4476, by rfl⟩) (B 8953 (by norm_num) ⟨4476, by rfl⟩ (by norm_num))
theorem R125477 : Reach 125477 := rs (se 4 (by rfl) ⟨11763, by rfl⟩) (B 23527 (by norm_num) ⟨11763, by rfl⟩ (by norm_num))
theorem R649781 : Reach 649781 := rs (se 5 (by rfl) ⟨30458, by rfl⟩) (B 60917 (by norm_num) ⟨30458, by rfl⟩ (by norm_num))
theorem R158269 : Reach 158269 := rs (se 3 (by rfl) ⟨29675, by rfl⟩) (B 59351 (by norm_num) ⟨29675, by rfl⟩ (by norm_num))
theorem R125501 : Reach 125501 := rs (se 3 (by rfl) ⟨23531, by rfl⟩) (B 47063 (by norm_num) ⟨23531, by rfl⟩ (by norm_num))
theorem R125525 : Reach 125525 := rs (se 8 (by rfl) ⟨735, by rfl⟩) (B 1471 (by norm_num) ⟨735, by rfl⟩ (by norm_num))
theorem R191069 : Reach 191069 := rs (se 3 (by rfl) ⟨35825, by rfl⟩) (B 71651 (by norm_num) ⟨35825, by rfl⟩ (by norm_num))
theorem R92773 : Reach 92773 := rs (se 4 (by rfl) ⟨8697, by rfl⟩) (B 17395 (by norm_num) ⟨8697, by rfl⟩ (by norm_num))
theorem R125549 : Reach 125549 := rs (se 3 (by rfl) ⟨23540, by rfl⟩) (B 47081 (by norm_num) ⟨23540, by rfl⟩ (by norm_num))
theorem R125573 : Reach 125573 := rs (se 4 (by rfl) ⟨11772, by rfl⟩) (B 23545 (by norm_num) ⟨11772, by rfl⟩ (by norm_num))
theorem R125597 : Reach 125597 := rs (se 3 (by rfl) ⟨23549, by rfl⟩) (B 47099 (by norm_num) ⟨23549, by rfl⟩ (by norm_num))
theorem R191141 : Reach 191141 := rs (se 4 (by rfl) ⟨17919, by rfl⟩) (B 35839 (by norm_num) ⟨17919, by rfl⟩ (by norm_num))
theorem R92845 : Reach 92845 := rs (se 3 (by rfl) ⟨17408, by rfl⟩) (B 34817 (by norm_num) ⟨17408, by rfl⟩ (by norm_num))
theorem R125621 : Reach 125621 := rs (se 5 (by rfl) ⟨5888, by rfl⟩) (B 11777 (by norm_num) ⟨5888, by rfl⟩ (by norm_num))
theorem R125645 : Reach 125645 := rs (se 3 (by rfl) ⟨23558, by rfl⟩) (B 47117 (by norm_num) ⟨23558, by rfl⟩ (by norm_num))
theorem R289493 : Reach 289493 := rs (se 7 (by rfl) ⟨3392, by rfl⟩) (B 6785 (by norm_num) ⟨3392, by rfl⟩ (by norm_num))
theorem R158429 : Reach 158429 := rs (se 3 (by rfl) ⟨29705, by rfl⟩) (B 59411 (by norm_num) ⟨29705, by rfl⟩ (by norm_num))
theorem R125669 : Reach 125669 := rs (se 4 (by rfl) ⟨11781, by rfl⟩) (B 23563 (by norm_num) ⟨11781, by rfl⟩ (by norm_num))
theorem R191213 : Reach 191213 := rs (se 3 (by rfl) ⟨35852, by rfl⟩) (B 71705 (by norm_num) ⟨35852, by rfl⟩ (by norm_num))
theorem R125693 : Reach 125693 := rs (se 3 (by rfl) ⟨23567, by rfl⟩) (B 47135 (by norm_num) ⟨23567, by rfl⟩ (by norm_num))
theorem R125717 : Reach 125717 := rs (se 6 (by rfl) ⟨2946, by rfl⟩) (B 5893 (by norm_num) ⟨2946, by rfl⟩ (by norm_num))
theorem R322325 : Reach 322325 := rs (se 6 (by rfl) ⟨7554, by rfl⟩) (B 15109 (by norm_num) ⟨7554, by rfl⟩ (by norm_num))
theorem R125741 : Reach 125741 := rs (se 3 (by rfl) ⟨23576, by rfl⟩) (B 47153 (by norm_num) ⟨23576, by rfl⟩ (by norm_num))
theorem R191285 : Reach 191285 := rs (se 5 (by rfl) ⟨8966, by rfl⟩) (B 17933 (by norm_num) ⟨8966, by rfl⟩ (by norm_num))
theorem R125765 : Reach 125765 := rs (se 4 (by rfl) ⟨11790, by rfl⟩) (B 23581 (by norm_num) ⟨11790, by rfl⟩ (by norm_num))
theorem R125789 : Reach 125789 := rs (se 3 (by rfl) ⟨23585, by rfl⟩) (B 47171 (by norm_num) ⟨23585, by rfl⟩ (by norm_num))
theorem R93025 : Reach 93025 := rs (se 2 (by rfl) ⟨34884, by rfl⟩) (B 69769 (by norm_num) ⟨34884, by rfl⟩ (by norm_num))
theorem R191333 : Reach 191333 := rs (se 4 (by rfl) ⟨17937, by rfl⟩) (B 35875 (by norm_num) ⟨17937, by rfl⟩ (by norm_num))
theorem R158573 : Reach 158573 := rs (se 3 (by rfl) ⟨29732, by rfl⟩) (B 59465 (by norm_num) ⟨29732, by rfl⟩ (by norm_num))
theorem R125813 : Reach 125813 := rs (se 5 (by rfl) ⟨5897, by rfl⟩) (B 11795 (by norm_num) ⟨5897, by rfl⟩ (by norm_num))
theorem R191357 : Reach 191357 := rs (se 3 (by rfl) ⟨35879, by rfl⟩) (B 71759 (by norm_num) ⟨35879, by rfl⟩ (by norm_num))
theorem R125837 : Reach 125837 := rs (se 3 (by rfl) ⟨23594, by rfl⟩) (B 47189 (by norm_num) ⟨23594, by rfl⟩ (by norm_num))
theorem R125861 : Reach 125861 := rs (se 4 (by rfl) ⟨11799, by rfl⟩) (B 23599 (by norm_num) ⟨11799, by rfl⟩ (by norm_num))
theorem R125885 : Reach 125885 := rs (se 3 (by rfl) ⟨23603, by rfl⟩) (B 47207 (by norm_num) ⟨23603, by rfl⟩ (by norm_num))
theorem R191429 : Reach 191429 := rs (se 4 (by rfl) ⟨17946, by rfl⟩) (B 35893 (by norm_num) ⟨17946, by rfl⟩ (by norm_num))
theorem R125909 : Reach 125909 := rs (se 7 (by rfl) ⟨1475, by rfl⟩) (B 2951 (by norm_num) ⟨1475, by rfl⟩ (by norm_num))
theorem R125933 : Reach 125933 := rs (se 3 (by rfl) ⟨23612, by rfl⟩) (B 47225 (by norm_num) ⟨23612, by rfl⟩ (by norm_num))
theorem R125957 : Reach 125957 := rs (se 4 (by rfl) ⟨11808, by rfl⟩) (B 23617 (by norm_num) ⟨11808, by rfl⟩ (by norm_num))
theorem R191501 : Reach 191501 := rs (se 3 (by rfl) ⟨35906, by rfl⟩) (B 71813 (by norm_num) ⟨35906, by rfl⟩ (by norm_num))
theorem R125981 : Reach 125981 := rs (se 3 (by rfl) ⟨23621, by rfl⟩) (B 47243 (by norm_num) ⟨23621, by rfl⟩ (by norm_num))
theorem R126005 : Reach 126005 := rs (se 5 (by rfl) ⟨5906, by rfl⟩) (B 11813 (by norm_num) ⟨5906, by rfl⟩ (by norm_num))
theorem R322613 : Reach 322613 := rs (se 5 (by rfl) ⟨15122, by rfl⟩) (B 30245 (by norm_num) ⟨15122, by rfl⟩ (by norm_num))
theorem R126029 : Reach 126029 := rs (se 3 (by rfl) ⟨23630, by rfl⟩) (B 47261 (by norm_num) ⟨23630, by rfl⟩ (by norm_num))
theorem R191573 : Reach 191573 := rs (se 8 (by rfl) ⟨1122, by rfl⟩) (B 2245 (by norm_num) ⟨1122, by rfl⟩ (by norm_num))
theorem R126053 : Reach 126053 := rs (se 4 (by rfl) ⟨11817, by rfl⟩) (B 23635 (by norm_num) ⟨11817, by rfl⟩ (by norm_num))
theorem R126077 : Reach 126077 := rs (se 3 (by rfl) ⟨23639, by rfl⟩) (B 47279 (by norm_num) ⟨23639, by rfl⟩ (by norm_num))
theorem R289925 : Reach 289925 := rs (se 4 (by rfl) ⟨27180, by rfl⟩) (B 54361 (by norm_num) ⟨27180, by rfl⟩ (by norm_num))
theorem R158861 : Reach 158861 := rs (se 3 (by rfl) ⟨29786, by rfl⟩) (B 59573 (by norm_num) ⟨29786, by rfl⟩ (by norm_num))
theorem R126101 : Reach 126101 := rs (se 6 (by rfl) ⟨2955, by rfl⟩) (B 5911 (by norm_num) ⟨2955, by rfl⟩ (by norm_num))
theorem R421013 : Reach 421013 := rs (se 6 (by rfl) ⟨9867, by rfl⟩) (B 19735 (by norm_num) ⟨9867, by rfl⟩ (by norm_num))
theorem R191645 : Reach 191645 := rs (se 3 (by rfl) ⟨35933, by rfl⟩) (B 71867 (by norm_num) ⟨35933, by rfl⟩ (by norm_num))
theorem R126125 : Reach 126125 := rs (se 3 (by rfl) ⟨23648, by rfl⟩) (B 47297 (by norm_num) ⟨23648, by rfl⟩ (by norm_num))
theorem R126149 : Reach 126149 := rs (se 4 (by rfl) ⟨11826, by rfl⟩) (B 23653 (by norm_num) ⟨11826, by rfl⟩ (by norm_num))
theorem R126173 : Reach 126173 := rs (se 3 (by rfl) ⟨23657, by rfl⟩) (B 47315 (by norm_num) ⟨23657, by rfl⟩ (by norm_num))
theorem R191717 : Reach 191717 := rs (se 4 (by rfl) ⟨17973, by rfl⟩) (B 35947 (by norm_num) ⟨17973, by rfl⟩ (by norm_num))
theorem R126197 : Reach 126197 := rs (se 5 (by rfl) ⟨5915, by rfl⟩) (B 11831 (by norm_num) ⟨5915, by rfl⟩ (by norm_num))
theorem R126221 : Reach 126221 := rs (se 3 (by rfl) ⟨23666, by rfl⟩) (B 47333 (by norm_num) ⟨23666, by rfl⟩ (by norm_num))
theorem R159013 : Reach 159013 := rs (se 4 (by rfl) ⟨14907, by rfl⟩) (B 29815 (by norm_num) ⟨14907, by rfl⟩ (by norm_num))
theorem R126245 : Reach 126245 := rs (se 4 (by rfl) ⟨11835, by rfl⟩) (B 23671 (by norm_num) ⟨11835, by rfl⟩ (by norm_num))
theorem R93485 : Reach 93485 := rs (se 3 (by rfl) ⟨17528, by rfl⟩) (B 35057 (by norm_num) ⟨17528, by rfl⟩ (by norm_num))
theorem R191789 : Reach 191789 := rs (se 3 (by rfl) ⟨35960, by rfl⟩) (B 71921 (by norm_num) ⟨35960, by rfl⟩ (by norm_num))
theorem R126269 : Reach 126269 := rs (se 3 (by rfl) ⟨23675, by rfl⟩) (B 47351 (by norm_num) ⟨23675, by rfl⟩ (by norm_num))
theorem R126293 : Reach 126293 := rs (se 11 (by rfl) ⟨92, by rfl⟩) (B 185 (by norm_num) ⟨92, by rfl⟩ (by norm_num))
theorem R93541 : Reach 93541 := rs (se 4 (by rfl) ⟨8769, by rfl⟩) (B 17539 (by norm_num) ⟨8769, by rfl⟩ (by norm_num))
theorem R126317 : Reach 126317 := rs (se 3 (by rfl) ⟨23684, by rfl⟩) (B 47369 (by norm_num) ⟨23684, by rfl⟩ (by norm_num))
theorem R191861 : Reach 191861 := rs (se 5 (by rfl) ⟨8993, by rfl⟩) (B 17987 (by norm_num) ⟨8993, by rfl⟩ (by norm_num))
theorem R126341 : Reach 126341 := rs (se 4 (by rfl) ⟨11844, by rfl⟩) (B 23689 (by norm_num) ⟨11844, by rfl⟩ (by norm_num))
theorem R93577 : Reach 93577 := rs (se 2 (by rfl) ⟨35091, by rfl⟩) (B 70183 (by norm_num) ⟨35091, by rfl⟩ (by norm_num))
theorem R126365 : Reach 126365 := rs (se 3 (by rfl) ⟨23693, by rfl⟩) (B 47387 (by norm_num) ⟨23693, by rfl⟩ (by norm_num))
theorem R93613 : Reach 93613 := rs (se 3 (by rfl) ⟨17552, by rfl⟩) (B 35105 (by norm_num) ⟨17552, by rfl⟩ (by norm_num))
theorem R126389 : Reach 126389 := rs (se 5 (by rfl) ⟨5924, by rfl⟩) (B 11849 (by norm_num) ⟨5924, by rfl⟩ (by norm_num))
theorem R191933 : Reach 191933 := rs (se 3 (by rfl) ⟨35987, by rfl⟩) (B 71975 (by norm_num) ⟨35987, by rfl⟩ (by norm_num))
theorem R126413 : Reach 126413 := rs (se 3 (by rfl) ⟨23702, by rfl⟩) (B 47405 (by norm_num) ⟨23702, by rfl⟩ (by norm_num))
theorem R93649 : Reach 93649 := rs (se 2 (by rfl) ⟨35118, by rfl⟩) (B 70237 (by norm_num) ⟨35118, by rfl⟩ (by norm_num))
theorem R126437 : Reach 126437 := rs (se 4 (by rfl) ⟨11853, by rfl⟩) (B 23707 (by norm_num) ⟨11853, by rfl⟩ (by norm_num))
theorem R93685 : Reach 93685 := rs (se 5 (by rfl) ⟨4391, by rfl⟩) (B 8783 (by norm_num) ⟨4391, by rfl⟩ (by norm_num))
theorem R126461 : Reach 126461 := rs (se 3 (by rfl) ⟨23711, by rfl⟩) (B 47423 (by norm_num) ⟨23711, by rfl⟩ (by norm_num))
theorem R192005 : Reach 192005 := rs (se 4 (by rfl) ⟨18000, by rfl⟩) (B 36001 (by norm_num) ⟨18000, by rfl⟩ (by norm_num))
theorem R126485 : Reach 126485 := rs (se 6 (by rfl) ⟨2964, by rfl⟩) (B 5929 (by norm_num) ⟨2964, by rfl⟩ (by norm_num))
theorem R93721 : Reach 93721 := rs (se 2 (by rfl) ⟨35145, by rfl⟩) (B 70291 (by norm_num) ⟨35145, by rfl⟩ (by norm_num))
theorem R126509 : Reach 126509 := rs (se 3 (by rfl) ⟨23720, by rfl⟩) (B 47441 (by norm_num) ⟨23720, by rfl⟩ (by norm_num))
theorem R290357 : Reach 290357 := rs (se 5 (by rfl) ⟨13610, by rfl⟩) (B 27221 (by norm_num) ⟨13610, by rfl⟩ (by norm_num))
theorem R93757 : Reach 93757 := rs (se 3 (by rfl) ⟨17579, by rfl⟩) (B 35159 (by norm_num) ⟨17579, by rfl⟩ (by norm_num))
theorem R126533 : Reach 126533 := rs (se 4 (by rfl) ⟨11862, by rfl⟩) (B 23725 (by norm_num) ⟨11862, by rfl⟩ (by norm_num))
theorem R192077 : Reach 192077 := rs (se 3 (by rfl) ⟨36014, by rfl⟩) (B 72029 (by norm_num) ⟨36014, by rfl⟩ (by norm_num))
theorem R159317 : Reach 159317 := rs (se 8 (by rfl) ⟨933, by rfl⟩) (B 1867 (by norm_num) ⟨933, by rfl⟩ (by norm_num))
theorem R126557 : Reach 126557 := rs (se 3 (by rfl) ⟨23729, by rfl⟩) (B 47459 (by norm_num) ⟨23729, by rfl⟩ (by norm_num))
theorem R93793 : Reach 93793 := rs (se 2 (by rfl) ⟨35172, by rfl⟩) (B 70345 (by norm_num) ⟨35172, by rfl⟩ (by norm_num))
theorem R126581 : Reach 126581 := rs (se 5 (by rfl) ⟨5933, by rfl⟩) (B 11867 (by norm_num) ⟨5933, by rfl⟩ (by norm_num))
theorem R126589 : Reach 126589 := rs (se 3 (by rfl) ⟨23735, by rfl⟩) (B 47471 (by norm_num) ⟨23735, by rfl⟩ (by norm_num))
theorem R93829 : Reach 93829 := rs (se 4 (by rfl) ⟨8796, by rfl⟩) (B 17593 (by norm_num) ⟨8796, by rfl⟩ (by norm_num))
theorem R126605 : Reach 126605 := rs (se 3 (by rfl) ⟨23738, by rfl⟩) (B 47477 (by norm_num) ⟨23738, by rfl⟩ (by norm_num))
theorem R192149 : Reach 192149 := rs (se 6 (by rfl) ⟨4503, by rfl⟩) (B 9007 (by norm_num) ⟨4503, by rfl⟩ (by norm_num))
theorem R126629 : Reach 126629 := rs (se 4 (by rfl) ⟨11871, by rfl⟩) (B 23743 (by norm_num) ⟨11871, by rfl⟩ (by norm_num))
theorem R93865 : Reach 93865 := rs (se 2 (by rfl) ⟨35199, by rfl⟩) (B 70399 (by norm_num) ⟨35199, by rfl⟩ (by norm_num))
theorem R126653 : Reach 126653 := rs (se 3 (by rfl) ⟨23747, by rfl⟩) (B 47495 (by norm_num) ⟨23747, by rfl⟩ (by norm_num))
theorem R93889 : Reach 93889 := rs (se 2 (by rfl) ⟨35208, by rfl⟩) (B 70417 (by norm_num) ⟨35208, by rfl⟩ (by norm_num))
theorem R93901 : Reach 93901 := rs (se 3 (by rfl) ⟨17606, by rfl⟩) (B 35213 (by norm_num) ⟨17606, by rfl⟩ (by norm_num))
theorem R126677 : Reach 126677 := rs (se 7 (by rfl) ⟨1484, by rfl⟩) (B 2969 (by norm_num) ⟨1484, by rfl⟩ (by norm_num))
theorem R192221 : Reach 192221 := rs (se 3 (by rfl) ⟨36041, by rfl⟩) (B 72083 (by norm_num) ⟨36041, by rfl⟩ (by norm_num))
theorem R126701 : Reach 126701 := rs (se 3 (by rfl) ⟨23756, by rfl⟩) (B 47513 (by norm_num) ⟨23756, by rfl⟩ (by norm_num))
theorem R93937 : Reach 93937 := rs (se 2 (by rfl) ⟨35226, by rfl⟩) (B 70453 (by norm_num) ⟨35226, by rfl⟩ (by norm_num))
theorem R126725 : Reach 126725 := rs (se 4 (by rfl) ⟨11880, by rfl⟩) (B 23761 (by norm_num) ⟨11880, by rfl⟩ (by norm_num))
theorem R93973 : Reach 93973 := rs (se 6 (by rfl) ⟨2202, by rfl⟩) (B 4405 (by norm_num) ⟨2202, by rfl⟩ (by norm_num))
theorem R126749 : Reach 126749 := rs (se 3 (by rfl) ⟨23765, by rfl⟩) (B 47531 (by norm_num) ⟨23765, by rfl⟩ (by norm_num))
theorem R192293 : Reach 192293 := rs (se 4 (by rfl) ⟨18027, by rfl⟩) (B 36055 (by norm_num) ⟨18027, by rfl⟩ (by norm_num))
theorem R421685 : Reach 421685 := rs (se 5 (by rfl) ⟨19766, by rfl⟩) (B 39533 (by norm_num) ⟨19766, by rfl⟩ (by norm_num))
theorem R126773 : Reach 126773 := rs (se 5 (by rfl) ⟨5942, by rfl⟩) (B 11885 (by norm_num) ⟨5942, by rfl⟩ (by norm_num))
theorem R94009 : Reach 94009 := rs (se 2 (by rfl) ⟨35253, by rfl⟩) (B 70507 (by norm_num) ⟨35253, by rfl⟩ (by norm_num))
theorem R126797 : Reach 126797 := rs (se 3 (by rfl) ⟨23774, by rfl⟩) (B 47549 (by norm_num) ⟨23774, by rfl⟩ (by norm_num))
theorem R94045 : Reach 94045 := rs (se 3 (by rfl) ⟨17633, by rfl⟩) (B 35267 (by norm_num) ⟨17633, by rfl⟩ (by norm_num))
theorem R126821 : Reach 126821 := rs (se 4 (by rfl) ⟨11889, by rfl⟩) (B 23779 (by norm_num) ⟨11889, by rfl⟩ (by norm_num))
theorem R192365 : Reach 192365 := rs (se 3 (by rfl) ⟨36068, by rfl⟩) (B 72137 (by norm_num) ⟨36068, by rfl⟩ (by norm_num))
theorem R126845 : Reach 126845 := rs (se 3 (by rfl) ⟨23783, by rfl⟩) (B 47567 (by norm_num) ⟨23783, by rfl⟩ (by norm_num))
theorem R94081 : Reach 94081 := rs (se 2 (by rfl) ⟨35280, by rfl⟩) (B 70561 (by norm_num) ⟨35280, by rfl⟩ (by norm_num))
theorem R126869 : Reach 126869 := rs (se 6 (by rfl) ⟨2973, by rfl⟩) (B 5947 (by norm_num) ⟨2973, by rfl⟩ (by norm_num))
theorem R94117 : Reach 94117 := rs (se 4 (by rfl) ⟨8823, by rfl⟩) (B 17647 (by norm_num) ⟨8823, by rfl⟩ (by norm_num))
theorem R126893 : Reach 126893 := rs (se 3 (by rfl) ⟨23792, by rfl⟩) (B 47585 (by norm_num) ⟨23792, by rfl⟩ (by norm_num))
theorem R192437 : Reach 192437 := rs (se 5 (by rfl) ⟨9020, by rfl⟩) (B 18041 (by norm_num) ⟨9020, by rfl⟩ (by norm_num))
theorem R126917 : Reach 126917 := rs (se 4 (by rfl) ⟨11898, by rfl⟩) (B 23797 (by norm_num) ⟨11898, by rfl⟩ (by norm_num))
theorem R94153 : Reach 94153 := rs (se 2 (by rfl) ⟨35307, by rfl⟩) (B 70615 (by norm_num) ⟨35307, by rfl⟩ (by norm_num))
theorem R126941 : Reach 126941 := rs (se 3 (by rfl) ⟨23801, by rfl⟩) (B 47603 (by norm_num) ⟨23801, by rfl⟩ (by norm_num))
theorem R290789 : Reach 290789 := rs (se 4 (by rfl) ⟨27261, by rfl⟩) (B 54523 (by norm_num) ⟨27261, by rfl⟩ (by norm_num))
theorem R94189 : Reach 94189 := rs (se 3 (by rfl) ⟨17660, by rfl⟩) (B 35321 (by norm_num) ⟨17660, by rfl⟩ (by norm_num))
theorem R716789 : Reach 716789 := rs (se 5 (by rfl) ⟨33599, by rfl⟩) (B 67199 (by norm_num) ⟨33599, by rfl⟩ (by norm_num))
theorem R126965 : Reach 126965 := rs (se 5 (by rfl) ⟨5951, by rfl⟩) (B 11903 (by norm_num) ⟨5951, by rfl⟩ (by norm_num))
theorem R192509 : Reach 192509 := rs (se 3 (by rfl) ⟨36095, by rfl⟩) (B 72191 (by norm_num) ⟨36095, by rfl⟩ (by norm_num))
theorem R126989 : Reach 126989 := rs (se 3 (by rfl) ⟨23810, by rfl⟩) (B 47621 (by norm_num) ⟨23810, by rfl⟩ (by norm_num))
theorem R94225 : Reach 94225 := rs (se 2 (by rfl) ⟨35334, by rfl⟩) (B 70669 (by norm_num) ⟨35334, by rfl⟩ (by norm_num))
theorem R127013 : Reach 127013 := rs (se 4 (by rfl) ⟨11907, by rfl⟩) (B 23815 (by norm_num) ⟨11907, by rfl⟩ (by norm_num))
theorem R94261 : Reach 94261 := rs (se 5 (by rfl) ⟨4418, by rfl⟩) (B 8837 (by norm_num) ⟨4418, by rfl⟩ (by norm_num))
theorem R127037 : Reach 127037 := rs (se 3 (by rfl) ⟨23819, by rfl⟩) (B 47639 (by norm_num) ⟨23819, by rfl⟩ (by norm_num))
theorem R192581 : Reach 192581 := rs (se 4 (by rfl) ⟨18054, by rfl⟩) (B 36109 (by norm_num) ⟨18054, by rfl⟩ (by norm_num))
theorem R127061 : Reach 127061 := rs (se 8 (by rfl) ⟨744, by rfl⟩) (B 1489 (by norm_num) ⟨744, by rfl⟩ (by norm_num))
theorem R94297 : Reach 94297 := rs (se 2 (by rfl) ⟨35361, by rfl⟩) (B 70723 (by norm_num) ⟨35361, by rfl⟩ (by norm_num))
theorem R127085 : Reach 127085 := rs (se 3 (by rfl) ⟨23828, by rfl⟩) (B 47657 (by norm_num) ⟨23828, by rfl⟩ (by norm_num))
theorem R94333 : Reach 94333 := rs (se 3 (by rfl) ⟨17687, by rfl⟩) (B 35375 (by norm_num) ⟨17687, by rfl⟩ (by norm_num))
theorem R127109 : Reach 127109 := rs (se 4 (by rfl) ⟨11916, by rfl⟩) (B 23833 (by norm_num) ⟨11916, by rfl⟩ (by norm_num))
theorem R192653 : Reach 192653 := rs (se 3 (by rfl) ⟨36122, by rfl⟩) (B 72245 (by norm_num) ⟨36122, by rfl⟩ (by norm_num))
theorem R127133 : Reach 127133 := rs (se 3 (by rfl) ⟨23837, by rfl⟩) (B 47675 (by norm_num) ⟨23837, by rfl⟩ (by norm_num))
theorem R94369 : Reach 94369 := rs (se 2 (by rfl) ⟨35388, by rfl⟩) (B 70777 (by norm_num) ⟨35388, by rfl⟩ (by norm_num))
theorem R127157 : Reach 127157 := rs (se 5 (by rfl) ⟨5960, by rfl⟩) (B 11921 (by norm_num) ⟨5960, by rfl⟩ (by norm_num))
theorem R94405 : Reach 94405 := rs (se 4 (by rfl) ⟨8850, by rfl⟩) (B 17701 (by norm_num) ⟨8850, by rfl⟩ (by norm_num))
theorem R127181 : Reach 127181 := rs (se 3 (by rfl) ⟨23846, by rfl⟩) (B 47693 (by norm_num) ⟨23846, by rfl⟩ (by norm_num))
theorem R323797 : Reach 323797 := rs (se 7 (by rfl) ⟨3794, by rfl⟩) (B 7589 (by norm_num) ⟨3794, by rfl⟩ (by norm_num))
theorem R192725 : Reach 192725 := rs (se 7 (by rfl) ⟨2258, by rfl⟩) (B 4517 (by norm_num) ⟨2258, by rfl⟩ (by norm_num))
theorem R127205 : Reach 127205 := rs (se 4 (by rfl) ⟨11925, by rfl⟩) (B 23851 (by norm_num) ⟨11925, by rfl⟩ (by norm_num))
theorem R94441 : Reach 94441 := rs (se 2 (by rfl) ⟨35415, by rfl⟩) (B 70831 (by norm_num) ⟨35415, by rfl⟩ (by norm_num))
theorem R127229 : Reach 127229 := rs (se 3 (by rfl) ⟨23855, by rfl⟩) (B 47711 (by norm_num) ⟨23855, by rfl⟩ (by norm_num))
theorem R94477 : Reach 94477 := rs (se 3 (by rfl) ⟨17714, by rfl⟩) (B 35429 (by norm_num) ⟨17714, by rfl⟩ (by norm_num))
theorem R127253 : Reach 127253 := rs (se 6 (by rfl) ⟨2982, by rfl⟩) (B 5965 (by norm_num) ⟨2982, by rfl⟩ (by norm_num))
theorem R94493 : Reach 94493 := rs (se 3 (by rfl) ⟨17717, by rfl⟩) (B 35435 (by norm_num) ⟨17717, by rfl⟩ (by norm_num))
theorem R192797 : Reach 192797 := rs (se 3 (by rfl) ⟨36149, by rfl⟩) (B 72299 (by norm_num) ⟨36149, by rfl⟩ (by norm_num))
theorem R127277 : Reach 127277 := rs (se 3 (by rfl) ⟨23864, by rfl⟩) (B 47729 (by norm_num) ⟨23864, by rfl⟩ (by norm_num))
theorem R94513 : Reach 94513 := rs (se 2 (by rfl) ⟨35442, by rfl⟩) (B 70885 (by norm_num) ⟨35442, by rfl⟩ (by norm_num))
theorem R160061 : Reach 160061 := rs (se 3 (by rfl) ⟨30011, by rfl⟩) (B 60023 (by norm_num) ⟨30011, by rfl⟩ (by norm_num))
theorem R160069 : Reach 160069 := rs (se 4 (by rfl) ⟨15006, by rfl⟩) (B 30013 (by norm_num) ⟨15006, by rfl⟩ (by norm_num))
theorem R127301 : Reach 127301 := rs (se 4 (by rfl) ⟨11934, by rfl⟩) (B 23869 (by norm_num) ⟨11934, by rfl⟩ (by norm_num))
theorem R94549 : Reach 94549 := rs (se 10 (by rfl) ⟨138, by rfl⟩) (B 277 (by norm_num) ⟨138, by rfl⟩ (by norm_num))
theorem R127325 : Reach 127325 := rs (se 3 (by rfl) ⟨23873, by rfl⟩) (B 47747 (by norm_num) ⟨23873, by rfl⟩ (by norm_num))
theorem R192869 : Reach 192869 := rs (se 4 (by rfl) ⟨18081, by rfl⟩) (B 36163 (by norm_num) ⟨18081, by rfl⟩ (by norm_num))
theorem R127349 : Reach 127349 := rs (se 5 (by rfl) ⟨5969, by rfl⟩) (B 11939 (by norm_num) ⟨5969, by rfl⟩ (by norm_num))
theorem R94585 : Reach 94585 := rs (se 2 (by rfl) ⟨35469, by rfl⟩) (B 70939 (by norm_num) ⟨35469, by rfl⟩ (by norm_num))
theorem R127373 : Reach 127373 := rs (se 3 (by rfl) ⟨23882, by rfl⟩) (B 47765 (by norm_num) ⟨23882, by rfl⟩ (by norm_num))
theorem R291221 : Reach 291221 := rs (se 6 (by rfl) ⟨6825, by rfl⟩) (B 13651 (by norm_num) ⟨6825, by rfl⟩ (by norm_num))
theorem R94621 : Reach 94621 := rs (se 3 (by rfl) ⟨17741, by rfl⟩) (B 35483 (by norm_num) ⟨17741, by rfl⟩ (by norm_num))
theorem R127397 : Reach 127397 := rs (se 4 (by rfl) ⟨11943, by rfl⟩) (B 23887 (by norm_num) ⟨11943, by rfl⟩ (by norm_num))
theorem R192941 : Reach 192941 := rs (se 3 (by rfl) ⟨36176, by rfl⟩) (B 72353 (by norm_num) ⟨36176, by rfl⟩ (by norm_num))
theorem R127421 : Reach 127421 := rs (se 3 (by rfl) ⟨23891, by rfl⟩) (B 47783 (by norm_num) ⟨23891, by rfl⟩ (by norm_num))
theorem R94657 : Reach 94657 := rs (se 2 (by rfl) ⟨35496, by rfl⟩) (B 70993 (by norm_num) ⟨35496, by rfl⟩ (by norm_num))
theorem R160213 : Reach 160213 := rs (se 7 (by rfl) ⟨1877, by rfl⟩) (B 3755 (by norm_num) ⟨1877, by rfl⟩ (by norm_num))
theorem R127445 : Reach 127445 := rs (se 7 (by rfl) ⟨1493, by rfl⟩) (B 2987 (by norm_num) ⟨1493, by rfl⟩ (by norm_num))
theorem R94693 : Reach 94693 := rs (se 4 (by rfl) ⟨8877, by rfl⟩) (B 17755 (by norm_num) ⟨8877, by rfl⟩ (by norm_num))
theorem R127469 : Reach 127469 := rs (se 3 (by rfl) ⟨23900, by rfl⟩) (B 47801 (by norm_num) ⟨23900, by rfl⟩ (by norm_num))
theorem R193013 : Reach 193013 := rs (se 5 (by rfl) ⟨9047, by rfl⟩) (B 18095 (by norm_num) ⟨9047, by rfl⟩ (by norm_num))
theorem R127493 : Reach 127493 := rs (se 4 (by rfl) ⟨11952, by rfl⟩) (B 23905 (by norm_num) ⟨11952, by rfl⟩ (by norm_num))
theorem R324101 : Reach 324101 := rs (se 4 (by rfl) ⟨30384, by rfl⟩) (B 60769 (by norm_num) ⟨30384, by rfl⟩ (by norm_num))
theorem R94729 : Reach 94729 := rs (se 2 (by rfl) ⟨35523, by rfl⟩) (B 71047 (by norm_num) ⟨35523, by rfl⟩ (by norm_num))
theorem R127517 : Reach 127517 := rs (se 3 (by rfl) ⟨23909, by rfl⟩) (B 47819 (by norm_num) ⟨23909, by rfl⟩ (by norm_num))
theorem R94765 : Reach 94765 := rs (se 3 (by rfl) ⟨17768, by rfl⟩) (B 35537 (by norm_num) ⟨17768, by rfl⟩ (by norm_num))
theorem R127541 : Reach 127541 := rs (se 5 (by rfl) ⟨5978, by rfl⟩) (B 11957 (by norm_num) ⟨5978, by rfl⟩ (by norm_num))
theorem R193085 : Reach 193085 := rs (se 3 (by rfl) ⟨36203, by rfl⟩) (B 72407 (by norm_num) ⟨36203, by rfl⟩ (by norm_num))
theorem R127565 : Reach 127565 := rs (se 3 (by rfl) ⟨23918, by rfl⟩) (B 47837 (by norm_num) ⟨23918, by rfl⟩ (by norm_num))
theorem R94801 : Reach 94801 := rs (se 2 (by rfl) ⟨35550, by rfl⟩) (B 71101 (by norm_num) ⟨35550, by rfl⟩ (by norm_num))
theorem R127589 : Reach 127589 := rs (se 4 (by rfl) ⟨11961, by rfl⟩) (B 23923 (by norm_num) ⟨11961, by rfl⟩ (by norm_num))
theorem R94837 : Reach 94837 := rs (se 5 (by rfl) ⟨4445, by rfl⟩) (B 8891 (by norm_num) ⟨4445, by rfl⟩ (by norm_num))
theorem R160373 : Reach 160373 := rs (se 5 (by rfl) ⟨7517, by rfl⟩) (B 15035 (by norm_num) ⟨7517, by rfl⟩ (by norm_num))
theorem R127613 : Reach 127613 := rs (se 3 (by rfl) ⟨23927, by rfl⟩) (B 47855 (by norm_num) ⟨23927, by rfl⟩ (by norm_num))
theorem R193157 : Reach 193157 := rs (se 4 (by rfl) ⟨18108, by rfl⟩) (B 36217 (by norm_num) ⟨18108, by rfl⟩ (by norm_num))
theorem R127637 : Reach 127637 := rs (se 6 (by rfl) ⟨2991, by rfl⟩) (B 5983 (by norm_num) ⟨2991, by rfl⟩ (by norm_num))
theorem R94873 : Reach 94873 := rs (se 2 (by rfl) ⟨35577, by rfl⟩) (B 71155 (by norm_num) ⟨35577, by rfl⟩ (by norm_num))
theorem R127661 : Reach 127661 := rs (se 3 (by rfl) ⟨23936, by rfl⟩) (B 47873 (by norm_num) ⟨23936, by rfl⟩ (by norm_num))
theorem R193205 : Reach 193205 := rs (se 5 (by rfl) ⟨9056, by rfl⟩) (B 18113 (by norm_num) ⟨9056, by rfl⟩ (by norm_num))
theorem R94909 : Reach 94909 := rs (se 3 (by rfl) ⟨17795, by rfl⟩) (B 35591 (by norm_num) ⟨17795, by rfl⟩ (by norm_num))
theorem R127685 : Reach 127685 := rs (se 4 (by rfl) ⟨11970, by rfl⟩) (B 23941 (by norm_num) ⟨11970, by rfl⟩ (by norm_num))
theorem R193229 : Reach 193229 := rs (se 3 (by rfl) ⟨36230, by rfl⟩) (B 72461 (by norm_num) ⟨36230, by rfl⟩ (by norm_num))
theorem R127709 : Reach 127709 := rs (se 3 (by rfl) ⟨23945, by rfl⟩) (B 47891 (by norm_num) ⟨23945, by rfl⟩ (by norm_num))
theorem R94945 : Reach 94945 := rs (se 2 (by rfl) ⟨35604, by rfl⟩) (B 71209 (by norm_num) ⟨35604, by rfl⟩ (by norm_num))
theorem R127733 : Reach 127733 := rs (se 5 (by rfl) ⟨5987, by rfl⟩) (B 11975 (by norm_num) ⟨5987, by rfl⟩ (by norm_num))
theorem R94981 : Reach 94981 := rs (se 4 (by rfl) ⟨8904, by rfl⟩) (B 17809 (by norm_num) ⟨8904, by rfl⟩ (by norm_num))
theorem R160517 : Reach 160517 := rs (se 4 (by rfl) ⟨15048, by rfl⟩) (B 30097 (by norm_num) ⟨15048, by rfl⟩ (by norm_num))
theorem R127757 : Reach 127757 := rs (se 3 (by rfl) ⟨23954, by rfl⟩) (B 47909 (by norm_num) ⟨23954, by rfl⟩ (by norm_num))
theorem R193301 : Reach 193301 := rs (se 6 (by rfl) ⟨4530, by rfl⟩) (B 9061 (by norm_num) ⟨4530, by rfl⟩ (by norm_num))
theorem R127781 : Reach 127781 := rs (se 4 (by rfl) ⟨11979, by rfl⟩) (B 23959 (by norm_num) ⟨11979, by rfl⟩ (by norm_num))
theorem R95017 : Reach 95017 := rs (se 2 (by rfl) ⟨35631, by rfl⟩) (B 71263 (by norm_num) ⟨35631, by rfl⟩ (by norm_num))
theorem R127805 : Reach 127805 := rs (se 3 (by rfl) ⟨23963, by rfl⟩) (B 47927 (by norm_num) ⟨23963, by rfl⟩ (by norm_num))
theorem R291653 : Reach 291653 := rs (se 4 (by rfl) ⟨27342, by rfl⟩) (B 54685 (by norm_num) ⟨27342, by rfl⟩ (by norm_num))
theorem R95053 : Reach 95053 := rs (se 3 (by rfl) ⟨17822, by rfl⟩) (B 35645 (by norm_num) ⟨17822, by rfl⟩ (by norm_num))
theorem R127829 : Reach 127829 := rs (se 9 (by rfl) ⟨374, by rfl⟩) (B 749 (by norm_num) ⟨374, by rfl⟩ (by norm_num))
theorem R193373 : Reach 193373 := rs (se 3 (by rfl) ⟨36257, by rfl⟩) (B 72515 (by norm_num) ⟨36257, by rfl⟩ (by norm_num))
theorem R127853 : Reach 127853 := rs (se 3 (by rfl) ⟨23972, by rfl⟩) (B 47945 (by norm_num) ⟨23972, by rfl⟩ (by norm_num))
theorem R95089 : Reach 95089 := rs (se 2 (by rfl) ⟨35658, by rfl⟩) (B 71317 (by norm_num) ⟨35658, by rfl⟩ (by norm_num))
theorem R127877 : Reach 127877 := rs (se 4 (by rfl) ⟨11988, by rfl⟩) (B 23977 (by norm_num) ⟨11988, by rfl⟩ (by norm_num))
theorem R95125 : Reach 95125 := rs (se 6 (by rfl) ⟨2229, by rfl⟩) (B 4459 (by norm_num) ⟨2229, by rfl⟩ (by norm_num))
theorem R127901 : Reach 127901 := rs (se 3 (by rfl) ⟨23981, by rfl⟩) (B 47963 (by norm_num) ⟨23981, by rfl⟩ (by norm_num))
theorem R193445 : Reach 193445 := rs (se 4 (by rfl) ⟨18135, by rfl⟩) (B 36271 (by norm_num) ⟨18135, by rfl⟩ (by norm_num))
theorem R357301 : Reach 357301 := rs (se 5 (by rfl) ⟨16748, by rfl⟩) (B 33497 (by norm_num) ⟨16748, by rfl⟩ (by norm_num))
theorem R127925 : Reach 127925 := rs (se 5 (by rfl) ⟨5996, by rfl⟩) (B 11993 (by norm_num) ⟨5996, by rfl⟩ (by norm_num))
theorem R95161 : Reach 95161 := rs (se 2 (by rfl) ⟨35685, by rfl⟩) (B 71371 (by norm_num) ⟨35685, by rfl⟩ (by norm_num))
theorem R127949 : Reach 127949 := rs (se 3 (by rfl) ⟨23990, by rfl⟩) (B 47981 (by norm_num) ⟨23990, by rfl⟩ (by norm_num))
theorem R95197 : Reach 95197 := rs (se 3 (by rfl) ⟨17849, by rfl⟩) (B 35699 (by norm_num) ⟨17849, by rfl⟩ (by norm_num))
theorem R127973 : Reach 127973 := rs (se 4 (by rfl) ⟨11997, by rfl⟩) (B 23995 (by norm_num) ⟨11997, by rfl⟩ (by norm_num))
theorem R193517 : Reach 193517 := rs (se 3 (by rfl) ⟨36284, by rfl⟩) (B 72569 (by norm_num) ⟨36284, by rfl⟩ (by norm_num))
theorem R127997 : Reach 127997 := rs (se 3 (by rfl) ⟨23999, by rfl⟩) (B 47999 (by norm_num) ⟨23999, by rfl⟩ (by norm_num))
theorem R95233 : Reach 95233 := rs (se 2 (by rfl) ⟨35712, by rfl⟩) (B 71425 (by norm_num) ⟨35712, by rfl⟩ (by norm_num))
theorem R128021 : Reach 128021 := rs (se 6 (by rfl) ⟨3000, by rfl⟩) (B 6001 (by norm_num) ⟨3000, by rfl⟩ (by norm_num))
theorem R95269 : Reach 95269 := rs (se 4 (by rfl) ⟨8931, by rfl⟩) (B 17863 (by norm_num) ⟨8931, by rfl⟩ (by norm_num))
theorem R160805 : Reach 160805 := rs (se 4 (by rfl) ⟨15075, by rfl⟩) (B 30151 (by norm_num) ⟨15075, by rfl⟩ (by norm_num))
theorem R128045 : Reach 128045 := rs (se 3 (by rfl) ⟨24008, by rfl⟩) (B 48017 (by norm_num) ⟨24008, by rfl⟩ (by norm_num))
theorem R193589 : Reach 193589 := rs (se 5 (by rfl) ⟨9074, by rfl⟩) (B 18149 (by norm_num) ⟨9074, by rfl⟩ (by norm_num))
theorem R422981 : Reach 422981 := rs (se 4 (by rfl) ⟨39654, by rfl⟩) (B 79309 (by norm_num) ⟨39654, by rfl⟩ (by norm_num))
theorem R128069 : Reach 128069 := rs (se 4 (by rfl) ⟨12006, by rfl⟩) (B 24013 (by norm_num) ⟨12006, by rfl⟩ (by norm_num))
theorem R95305 : Reach 95305 := rs (se 2 (by rfl) ⟨35739, by rfl⟩) (B 71479 (by norm_num) ⟨35739, by rfl⟩ (by norm_num))
theorem R128093 : Reach 128093 := rs (se 3 (by rfl) ⟨24017, by rfl⟩) (B 48035 (by norm_num) ⟨24017, by rfl⟩ (by norm_num))
theorem R95341 : Reach 95341 := rs (se 3 (by rfl) ⟨17876, by rfl⟩) (B 35753 (by norm_num) ⟨17876, by rfl⟩ (by norm_num))
theorem R128117 : Reach 128117 := rs (se 5 (by rfl) ⟨6005, by rfl⟩) (B 12011 (by norm_num) ⟨6005, by rfl⟩ (by norm_num))
theorem R193661 : Reach 193661 := rs (se 3 (by rfl) ⟨36311, by rfl⟩) (B 72623 (by norm_num) ⟨36311, by rfl⟩ (by norm_num))
theorem R128141 : Reach 128141 := rs (se 3 (by rfl) ⟨24026, by rfl⟩) (B 48053 (by norm_num) ⟨24026, by rfl⟩ (by norm_num))
theorem R95377 : Reach 95377 := rs (se 2 (by rfl) ⟨35766, by rfl⟩) (B 71533 (by norm_num) ⟨35766, by rfl⟩ (by norm_num))
theorem R128165 : Reach 128165 := rs (se 4 (by rfl) ⟨12015, by rfl⟩) (B 24031 (by norm_num) ⟨12015, by rfl⟩ (by norm_num))
theorem R95413 : Reach 95413 := rs (se 5 (by rfl) ⟨4472, by rfl⟩) (B 8945 (by norm_num) ⟨4472, by rfl⟩ (by norm_num))
theorem R160957 : Reach 160957 := rs (se 3 (by rfl) ⟨30179, by rfl⟩) (B 60359 (by norm_num) ⟨30179, by rfl⟩ (by norm_num))
theorem R128189 : Reach 128189 := rs (se 3 (by rfl) ⟨24035, by rfl⟩) (B 48071 (by norm_num) ⟨24035, by rfl⟩ (by norm_num))
theorem R193733 : Reach 193733 := rs (se 4 (by rfl) ⟨18162, by rfl⟩) (B 36325 (by norm_num) ⟨18162, by rfl⟩ (by norm_num))
theorem R128213 : Reach 128213 := rs (se 7 (by rfl) ⟨1502, by rfl⟩) (B 3005 (by norm_num) ⟨1502, by rfl⟩ (by norm_num))
theorem R95449 : Reach 95449 := rs (se 2 (by rfl) ⟨35793, by rfl⟩) (B 71587 (by norm_num) ⟨35793, by rfl⟩ (by norm_num))
theorem R95461 : Reach 95461 := rs (se 4 (by rfl) ⟨8949, by rfl⟩) (B 17899 (by norm_num) ⟨8949, by rfl⟩ (by norm_num))
theorem R128237 : Reach 128237 := rs (se 3 (by rfl) ⟨24044, by rfl⟩) (B 48089 (by norm_num) ⟨24044, by rfl⟩ (by norm_num))
theorem R292085 : Reach 292085 := rs (se 5 (by rfl) ⟨13691, by rfl⟩) (B 27383 (by norm_num) ⟨13691, by rfl⟩ (by norm_num))
theorem R95485 : Reach 95485 := rs (se 3 (by rfl) ⟨17903, by rfl⟩) (B 35807 (by norm_num) ⟨17903, by rfl⟩ (by norm_num))
theorem R128261 : Reach 128261 := rs (se 4 (by rfl) ⟨12024, by rfl⟩) (B 24049 (by norm_num) ⟨12024, by rfl⟩ (by norm_num))
theorem R193805 : Reach 193805 := rs (se 3 (by rfl) ⟨36338, by rfl⟩) (B 72677 (by norm_num) ⟨36338, by rfl⟩ (by norm_num))
theorem R128285 : Reach 128285 := rs (se 3 (by rfl) ⟨24053, by rfl⟩) (B 48107 (by norm_num) ⟨24053, by rfl⟩ (by norm_num))
theorem R95521 : Reach 95521 := rs (se 2 (by rfl) ⟨35820, by rfl⟩) (B 71641 (by norm_num) ⟨35820, by rfl⟩ (by norm_num))
theorem R128309 : Reach 128309 := rs (se 5 (by rfl) ⟨6014, by rfl⟩) (B 12029 (by norm_num) ⟨6014, by rfl⟩ (by norm_num))
theorem R95557 : Reach 95557 := rs (se 4 (by rfl) ⟨8958, by rfl⟩) (B 17917 (by norm_num) ⟨8958, by rfl⟩ (by norm_num))
theorem R128333 : Reach 128333 := rs (se 3 (by rfl) ⟨24062, by rfl⟩) (B 48125 (by norm_num) ⟨24062, by rfl⟩ (by norm_num))
theorem R193877 : Reach 193877 := rs (se 13 (by rfl) ⟨35, by rfl⟩) (B 71 (by norm_num) ⟨35, by rfl⟩ (by norm_num))
theorem R128357 : Reach 128357 := rs (se 4 (by rfl) ⟨12033, by rfl⟩) (B 24067 (by norm_num) ⟨12033, by rfl⟩ (by norm_num))
theorem R95593 : Reach 95593 := rs (se 2 (by rfl) ⟨35847, by rfl⟩) (B 71695 (by norm_num) ⟨35847, by rfl⟩ (by norm_num))
theorem R128381 : Reach 128381 := rs (se 3 (by rfl) ⟨24071, by rfl⟩) (B 48143 (by norm_num) ⟨24071, by rfl⟩ (by norm_num))
theorem R95629 : Reach 95629 := rs (se 3 (by rfl) ⟨17930, by rfl⟩) (B 35861 (by norm_num) ⟨17930, by rfl⟩ (by norm_num))
theorem R128405 : Reach 128405 := rs (se 6 (by rfl) ⟨3009, by rfl⟩) (B 6019 (by norm_num) ⟨3009, by rfl⟩ (by norm_num))
theorem R193949 : Reach 193949 := rs (se 3 (by rfl) ⟨36365, by rfl⟩) (B 72731 (by norm_num) ⟨36365, by rfl⟩ (by norm_num))
theorem R128429 : Reach 128429 := rs (se 3 (by rfl) ⟨24080, by rfl⟩) (B 48161 (by norm_num) ⟨24080, by rfl⟩ (by norm_num))
theorem R95665 : Reach 95665 := rs (se 2 (by rfl) ⟨35874, by rfl⟩) (B 71749 (by norm_num) ⟨35874, by rfl⟩ (by norm_num))
theorem R128453 : Reach 128453 := rs (se 4 (by rfl) ⟨12042, by rfl⟩) (B 24085 (by norm_num) ⟨12042, by rfl⟩ (by norm_num))
theorem R95701 : Reach 95701 := rs (se 7 (by rfl) ⟨1121, by rfl⟩) (B 2243 (by norm_num) ⟨1121, by rfl⟩ (by norm_num))
theorem R128477 : Reach 128477 := rs (se 3 (by rfl) ⟨24089, by rfl⟩) (B 48179 (by norm_num) ⟨24089, by rfl⟩ (by norm_num))
theorem R194021 : Reach 194021 := rs (se 4 (by rfl) ⟨18189, by rfl⟩) (B 36379 (by norm_num) ⟨18189, by rfl⟩ (by norm_num))
theorem R161261 : Reach 161261 := rs (se 3 (by rfl) ⟨30236, by rfl⟩) (B 60473 (by norm_num) ⟨30236, by rfl⟩ (by norm_num))
theorem R128501 : Reach 128501 := rs (se 5 (by rfl) ⟨6023, by rfl⟩) (B 12047 (by norm_num) ⟨6023, by rfl⟩ (by norm_num))
theorem R95737 : Reach 95737 := rs (se 2 (by rfl) ⟨35901, by rfl⟩) (B 71803 (by norm_num) ⟨35901, by rfl⟩ (by norm_num))
theorem R128525 : Reach 128525 := rs (se 3 (by rfl) ⟨24098, by rfl⟩) (B 48197 (by norm_num) ⟨24098, by rfl⟩ (by norm_num))
theorem R95773 : Reach 95773 := rs (se 3 (by rfl) ⟨17957, by rfl⟩) (B 35915 (by norm_num) ⟨17957, by rfl⟩ (by norm_num))
theorem R128549 : Reach 128549 := rs (se 4 (by rfl) ⟨12051, by rfl⟩) (B 24103 (by norm_num) ⟨12051, by rfl⟩ (by norm_num))
theorem R194093 : Reach 194093 := rs (se 3 (by rfl) ⟨36392, by rfl⟩) (B 72785 (by norm_num) ⟨36392, by rfl⟩ (by norm_num))
theorem R128573 : Reach 128573 := rs (se 3 (by rfl) ⟨24107, by rfl⟩) (B 48215 (by norm_num) ⟨24107, by rfl⟩ (by norm_num))
theorem R95809 : Reach 95809 := rs (se 2 (by rfl) ⟨35928, by rfl⟩) (B 71857 (by norm_num) ⟨35928, by rfl⟩ (by norm_num))
theorem R1799765 : Reach 1799765 := rs (se 8 (by rfl) ⟨10545, by rfl⟩) (B 21091 (by norm_num) ⟨10545, by rfl⟩ (by norm_num))
theorem R128597 : Reach 128597 := rs (se 8 (by rfl) ⟨753, by rfl⟩) (B 1507 (by norm_num) ⟨753, by rfl⟩ (by norm_num))
theorem R95845 : Reach 95845 := rs (se 4 (by rfl) ⟨8985, by rfl⟩) (B 17971 (by norm_num) ⟨8985, by rfl⟩ (by norm_num))
theorem R128621 : Reach 128621 := rs (se 3 (by rfl) ⟨24116, by rfl⟩) (B 48233 (by norm_num) ⟨24116, by rfl⟩ (by norm_num))
theorem R194165 : Reach 194165 := rs (se 5 (by rfl) ⟨9101, by rfl⟩) (B 18203 (by norm_num) ⟨9101, by rfl⟩ (by norm_num))
theorem R128645 : Reach 128645 := rs (se 4 (by rfl) ⟨12060, by rfl⟩) (B 24121 (by norm_num) ⟨12060, by rfl⟩ (by norm_num))
theorem R95881 : Reach 95881 := rs (se 2 (by rfl) ⟨35955, by rfl⟩) (B 71911 (by norm_num) ⟨35955, by rfl⟩ (by norm_num))
theorem R128669 : Reach 128669 := rs (se 3 (by rfl) ⟨24125, by rfl⟩) (B 48251 (by norm_num) ⟨24125, by rfl⟩ (by norm_num))
theorem R292517 : Reach 292517 := rs (se 4 (by rfl) ⟨27423, by rfl⟩) (B 54847 (by norm_num) ⟨27423, by rfl⟩ (by norm_num))
theorem R95917 : Reach 95917 := rs (se 3 (by rfl) ⟨17984, by rfl⟩) (B 35969 (by norm_num) ⟨17984, by rfl⟩ (by norm_num))
theorem R128693 : Reach 128693 := rs (se 5 (by rfl) ⟨6032, by rfl⟩) (B 12065 (by norm_num) ⟨6032, by rfl⟩ (by norm_num))
theorem R194237 : Reach 194237 := rs (se 3 (by rfl) ⟨36419, by rfl⟩) (B 72839 (by norm_num) ⟨36419, by rfl⟩ (by norm_num))
theorem R128717 : Reach 128717 := rs (se 3 (by rfl) ⟨24134, by rfl⟩) (B 48269 (by norm_num) ⟨24134, by rfl⟩ (by norm_num))
theorem R95953 : Reach 95953 := rs (se 2 (by rfl) ⟨35982, by rfl⟩) (B 71965 (by norm_num) ⟨35982, by rfl⟩ (by norm_num))
theorem R128741 : Reach 128741 := rs (se 4 (by rfl) ⟨12069, by rfl⟩) (B 24139 (by norm_num) ⟨12069, by rfl⟩ (by norm_num))
theorem R95989 : Reach 95989 := rs (se 5 (by rfl) ⟨4499, by rfl⟩) (B 8999 (by norm_num) ⟨4499, by rfl⟩ (by norm_num))
theorem R128765 : Reach 128765 := rs (se 3 (by rfl) ⟨24143, by rfl⟩) (B 48287 (by norm_num) ⟨24143, by rfl⟩ (by norm_num))
theorem R194309 : Reach 194309 := rs (se 4 (by rfl) ⟨18216, by rfl⟩) (B 36433 (by norm_num) ⟨18216, by rfl⟩ (by norm_num))
theorem R128789 : Reach 128789 := rs (se 6 (by rfl) ⟨3018, by rfl⟩) (B 6037 (by norm_num) ⟨3018, by rfl⟩ (by norm_num))
theorem R96025 : Reach 96025 := rs (se 2 (by rfl) ⟨36009, by rfl⟩) (B 72019 (by norm_num) ⟨36009, by rfl⟩ (by norm_num))
theorem R128813 : Reach 128813 := rs (se 3 (by rfl) ⟨24152, by rfl⟩) (B 48305 (by norm_num) ⟨24152, by rfl⟩ (by norm_num))
theorem R96061 : Reach 96061 := rs (se 3 (by rfl) ⟨18011, by rfl⟩) (B 36023 (by norm_num) ⟨18011, by rfl⟩ (by norm_num))
theorem R128837 : Reach 128837 := rs (se 4 (by rfl) ⟨12078, by rfl⟩) (B 24157 (by norm_num) ⟨12078, by rfl⟩ (by norm_num))
theorem R194381 : Reach 194381 := rs (se 3 (by rfl) ⟨36446, by rfl⟩) (B 72893 (by norm_num) ⟨36446, by rfl⟩ (by norm_num))
theorem R194389 : Reach 194389 := rs (se 9 (by rfl) ⟨569, by rfl⟩) (B 1139 (by norm_num) ⟨569, by rfl⟩ (by norm_num))
theorem R128861 : Reach 128861 := rs (se 3 (by rfl) ⟨24161, by rfl⟩) (B 48323 (by norm_num) ⟨24161, by rfl⟩ (by norm_num))
theorem R96097 : Reach 96097 := rs (se 2 (by rfl) ⟨36036, by rfl⟩) (B 72073 (by norm_num) ⟨36036, by rfl⟩ (by norm_num))
theorem R128885 : Reach 128885 := rs (se 5 (by rfl) ⟨6041, by rfl⟩) (B 12083 (by norm_num) ⟨6041, by rfl⟩ (by norm_num))
theorem R96133 : Reach 96133 := rs (se 4 (by rfl) ⟨9012, by rfl⟩) (B 18025 (by norm_num) ⟨9012, by rfl⟩ (by norm_num))
theorem R128909 : Reach 128909 := rs (se 3 (by rfl) ⟨24170, by rfl⟩) (B 48341 (by norm_num) ⟨24170, by rfl⟩ (by norm_num))
theorem R194453 : Reach 194453 := rs (se 6 (by rfl) ⟨4557, by rfl⟩) (B 9115 (by norm_num) ⟨4557, by rfl⟩ (by norm_num))
theorem R128933 : Reach 128933 := rs (se 4 (by rfl) ⟨12087, by rfl⟩) (B 24175 (by norm_num) ⟨12087, by rfl⟩ (by norm_num))
theorem R96169 : Reach 96169 := rs (se 2 (by rfl) ⟨36063, by rfl⟩) (B 72127 (by norm_num) ⟨36063, by rfl⟩ (by norm_num))
theorem R128957 : Reach 128957 := rs (se 3 (by rfl) ⟨24179, by rfl⟩) (B 48359 (by norm_num) ⟨24179, by rfl⟩ (by norm_num))
theorem R96205 : Reach 96205 := rs (se 3 (by rfl) ⟨18038, by rfl⟩) (B 36077 (by norm_num) ⟨18038, by rfl⟩ (by norm_num))
theorem R128981 : Reach 128981 := rs (se 7 (by rfl) ⟨1511, by rfl⟩) (B 3023 (by norm_num) ⟨1511, by rfl⟩ (by norm_num))
theorem R194525 : Reach 194525 := rs (se 3 (by rfl) ⟨36473, by rfl⟩) (B 72947 (by norm_num) ⟨36473, by rfl⟩ (by norm_num))
theorem R129005 : Reach 129005 := rs (se 3 (by rfl) ⟨24188, by rfl⟩) (B 48377 (by norm_num) ⟨24188, by rfl⟩ (by norm_num))
theorem R96241 : Reach 96241 := rs (se 2 (by rfl) ⟨36090, by rfl⟩) (B 72181 (by norm_num) ⟨36090, by rfl⟩ (by norm_num))
theorem R129029 : Reach 129029 := rs (se 4 (by rfl) ⟨12096, by rfl⟩) (B 24193 (by norm_num) ⟨12096, by rfl⟩ (by norm_num))
theorem R96277 : Reach 96277 := rs (se 6 (by rfl) ⟨2256, by rfl⟩) (B 4513 (by norm_num) ⟨2256, by rfl⟩ (by norm_num))
theorem R129053 : Reach 129053 := rs (se 3 (by rfl) ⟨24197, by rfl⟩) (B 48395 (by norm_num) ⟨24197, by rfl⟩ (by norm_num))
theorem R194597 : Reach 194597 := rs (se 4 (by rfl) ⟨18243, by rfl⟩) (B 36487 (by norm_num) ⟨18243, by rfl⟩ (by norm_num))
theorem R129077 : Reach 129077 := rs (se 5 (by rfl) ⟨6050, by rfl⟩) (B 12101 (by norm_num) ⟨6050, by rfl⟩ (by norm_num))
theorem R96313 : Reach 96313 := rs (se 2 (by rfl) ⟨36117, by rfl⟩) (B 72235 (by norm_num) ⟨36117, by rfl⟩ (by norm_num))
theorem R129101 : Reach 129101 := rs (se 3 (by rfl) ⟨24206, by rfl⟩) (B 48413 (by norm_num) ⟨24206, by rfl⟩ (by norm_num))
theorem R292949 : Reach 292949 := rs (se 8 (by rfl) ⟨1716, by rfl⟩) (B 3433 (by norm_num) ⟨1716, by rfl⟩ (by norm_num))
theorem R96349 : Reach 96349 := rs (se 3 (by rfl) ⟨18065, by rfl⟩) (B 36131 (by norm_num) ⟨18065, by rfl⟩ (by norm_num))
theorem R129125 : Reach 129125 := rs (se 4 (by rfl) ⟨12105, by rfl⟩) (B 24211 (by norm_num) ⟨12105, by rfl⟩ (by norm_num))
theorem R194669 : Reach 194669 := rs (se 3 (by rfl) ⟨36500, by rfl⟩) (B 73001 (by norm_num) ⟨36500, by rfl⟩ (by norm_num))
theorem R161909 : Reach 161909 := rs (se 5 (by rfl) ⟨7589, by rfl⟩) (B 15179 (by norm_num) ⟨7589, by rfl⟩ (by norm_num))
theorem R129149 : Reach 129149 := rs (se 3 (by rfl) ⟨24215, by rfl⟩) (B 48431 (by norm_num) ⟨24215, by rfl⟩ (by norm_num))
theorem R96385 : Reach 96385 := rs (se 2 (by rfl) ⟨36144, by rfl⟩) (B 72289 (by norm_num) ⟨36144, by rfl⟩ (by norm_num))
theorem R129173 : Reach 129173 := rs (se 6 (by rfl) ⟨3027, by rfl⟩) (B 6055 (by norm_num) ⟨3027, by rfl⟩ (by norm_num))
theorem R96421 : Reach 96421 := rs (se 4 (by rfl) ⟨9039, by rfl⟩) (B 18079 (by norm_num) ⟨9039, by rfl⟩ (by norm_num))
theorem R129197 : Reach 129197 := rs (se 3 (by rfl) ⟨24224, by rfl⟩) (B 48449 (by norm_num) ⟨24224, by rfl⟩ (by norm_num))
theorem R194741 : Reach 194741 := rs (se 5 (by rfl) ⟨9128, by rfl⟩) (B 18257 (by norm_num) ⟨9128, by rfl⟩ (by norm_num))
theorem R129221 : Reach 129221 := rs (se 4 (by rfl) ⟨12114, by rfl⟩) (B 24229 (by norm_num) ⟨12114, by rfl⟩ (by norm_num))
theorem R96457 : Reach 96457 := rs (se 2 (by rfl) ⟨36171, by rfl⟩) (B 72343 (by norm_num) ⟨36171, by rfl⟩ (by norm_num))
theorem R162013 : Reach 162013 := rs (se 3 (by rfl) ⟨30377, by rfl⟩) (B 60755 (by norm_num) ⟨30377, by rfl⟩ (by norm_num))
theorem R129245 : Reach 129245 := rs (se 3 (by rfl) ⟨24233, by rfl⟩) (B 48467 (by norm_num) ⟨24233, by rfl⟩ (by norm_num))
theorem R96493 : Reach 96493 := rs (se 3 (by rfl) ⟨18092, by rfl⟩) (B 36185 (by norm_num) ⟨18092, by rfl⟩ (by norm_num))
theorem R129269 : Reach 129269 := rs (se 5 (by rfl) ⟨6059, by rfl⟩) (B 12119 (by norm_num) ⟨6059, by rfl⟩ (by norm_num))
theorem R129277 : Reach 129277 := rs (se 3 (by rfl) ⟨24239, by rfl⟩) (B 48479 (by norm_num) ⟨24239, by rfl⟩ (by norm_num))
theorem R194813 : Reach 194813 := rs (se 3 (by rfl) ⟨36527, by rfl⟩) (B 73055 (by norm_num) ⟨36527, by rfl⟩ (by norm_num))
theorem R129293 : Reach 129293 := rs (se 3 (by rfl) ⟨24242, by rfl⟩) (B 48485 (by norm_num) ⟨24242, by rfl⟩ (by norm_num))
theorem R96529 : Reach 96529 := rs (se 2 (by rfl) ⟨36198, by rfl⟩) (B 72397 (by norm_num) ⟨36198, by rfl⟩ (by norm_num))
theorem R129317 : Reach 129317 := rs (se 4 (by rfl) ⟨12123, by rfl⟩) (B 24247 (by norm_num) ⟨12123, by rfl⟩ (by norm_num))
theorem R260405 : Reach 260405 := rs (se 5 (by rfl) ⟨12206, by rfl⟩) (B 24413 (by norm_num) ⟨12206, by rfl⟩ (by norm_num))
theorem R96565 : Reach 96565 := rs (se 5 (by rfl) ⟨4526, by rfl⟩) (B 9053 (by norm_num) ⟨4526, by rfl⟩ (by norm_num))
theorem R129341 : Reach 129341 := rs (se 3 (by rfl) ⟨24251, by rfl⟩) (B 48503 (by norm_num) ⟨24251, by rfl⟩ (by norm_num))
theorem R194885 : Reach 194885 := rs (se 4 (by rfl) ⟨18270, by rfl⟩) (B 36541 (by norm_num) ⟨18270, by rfl⟩ (by norm_num))
theorem R424277 : Reach 424277 := rs (se 10 (by rfl) ⟨621, by rfl⟩) (B 1243 (by norm_num) ⟨621, by rfl⟩ (by norm_num))
theorem R129365 : Reach 129365 := rs (se 10 (by rfl) ⟨189, by rfl⟩) (B 379 (by norm_num) ⟨189, by rfl⟩ (by norm_num))
theorem R96601 : Reach 96601 := rs (se 2 (by rfl) ⟨36225, by rfl⟩) (B 72451 (by norm_num) ⟨36225, by rfl⟩ (by norm_num))
theorem R162157 : Reach 162157 := rs (se 3 (by rfl) ⟨30404, by rfl⟩) (B 60809 (by norm_num) ⟨30404, by rfl⟩ (by norm_num))
theorem R129389 : Reach 129389 := rs (se 3 (by rfl) ⟨24260, by rfl⟩) (B 48521 (by norm_num) ⟨24260, by rfl⟩ (by norm_num))
theorem R96637 : Reach 96637 := rs (se 3 (by rfl) ⟨18119, by rfl⟩) (B 36239 (by norm_num) ⟨18119, by rfl⟩ (by norm_num))
theorem R358789 : Reach 358789 := rs (se 4 (by rfl) ⟨33636, by rfl⟩) (B 67273 (by norm_num) ⟨33636, by rfl⟩ (by norm_num))
theorem R129413 : Reach 129413 := rs (se 4 (by rfl) ⟨12132, by rfl⟩) (B 24265 (by norm_num) ⟨12132, by rfl⟩ (by norm_num))
theorem R194957 : Reach 194957 := rs (se 3 (by rfl) ⟨36554, by rfl⟩) (B 73109 (by norm_num) ⟨36554, by rfl⟩ (by norm_num))
theorem R358805 : Reach 358805 := rs (se 6 (by rfl) ⟨8409, by rfl⟩) (B 16819 (by norm_num) ⟨8409, by rfl⟩ (by norm_num))
theorem R129437 : Reach 129437 := rs (se 3 (by rfl) ⟨24269, by rfl⟩) (B 48539 (by norm_num) ⟨24269, by rfl⟩ (by norm_num))
theorem R96673 : Reach 96673 := rs (se 2 (by rfl) ⟨36252, by rfl⟩) (B 72505 (by norm_num) ⟨36252, by rfl⟩ (by norm_num))
theorem R129461 : Reach 129461 := rs (se 5 (by rfl) ⟨6068, by rfl⟩) (B 12137 (by norm_num) ⟨6068, by rfl⟩ (by norm_num))
theorem R96709 : Reach 96709 := rs (se 4 (by rfl) ⟨9066, by rfl⟩) (B 18133 (by norm_num) ⟨9066, by rfl⟩ (by norm_num))
theorem R129485 : Reach 129485 := rs (se 3 (by rfl) ⟨24278, by rfl⟩) (B 48557 (by norm_num) ⟨24278, by rfl⟩ (by norm_num))
theorem R195029 : Reach 195029 := rs (se 7 (by rfl) ⟨2285, by rfl⟩) (B 4571 (by norm_num) ⟨2285, by rfl⟩ (by norm_num))
theorem R129509 : Reach 129509 := rs (se 4 (by rfl) ⟨12141, by rfl⟩) (B 24283 (by norm_num) ⟨12141, by rfl⟩ (by norm_num))
theorem R96745 : Reach 96745 := rs (se 2 (by rfl) ⟨36279, by rfl⟩) (B 72559 (by norm_num) ⟨36279, by rfl⟩ (by norm_num))
theorem R260597 : Reach 260597 := rs (se 5 (by rfl) ⟨12215, by rfl⟩) (B 24431 (by norm_num) ⟨12215, by rfl⟩ (by norm_num))
theorem R129533 : Reach 129533 := rs (se 3 (by rfl) ⟨24287, by rfl⟩) (B 48575 (by norm_num) ⟨24287, by rfl⟩ (by norm_num))
theorem R293381 : Reach 293381 := rs (se 4 (by rfl) ⟨27504, by rfl⟩) (B 55009 (by norm_num) ⟨27504, by rfl⟩ (by norm_num))
theorem R162317 : Reach 162317 := rs (se 3 (by rfl) ⟨30434, by rfl⟩) (B 60869 (by norm_num) ⟨30434, by rfl⟩ (by norm_num))
theorem R96781 : Reach 96781 := rs (se 3 (by rfl) ⟨18146, by rfl⟩) (B 36293 (by norm_num) ⟨18146, by rfl⟩ (by norm_num))
theorem R129557 : Reach 129557 := rs (se 6 (by rfl) ⟨3036, by rfl⟩) (B 6073 (by norm_num) ⟨3036, by rfl⟩ (by norm_num))
theorem R195101 : Reach 195101 := rs (se 3 (by rfl) ⟨36581, by rfl⟩) (B 73163 (by norm_num) ⟨36581, by rfl⟩ (by norm_num))
theorem R129581 : Reach 129581 := rs (se 3 (by rfl) ⟨24296, by rfl⟩) (B 48593 (by norm_num) ⟨24296, by rfl⟩ (by norm_num))
theorem R96817 : Reach 96817 := rs (se 2 (by rfl) ⟨36306, by rfl⟩) (B 72613 (by norm_num) ⟨36306, by rfl⟩ (by norm_num))
theorem R326213 : Reach 326213 := rs (se 4 (by rfl) ⟨30582, by rfl⟩) (B 61165 (by norm_num) ⟨30582, by rfl⟩ (by norm_num))
theorem R129605 : Reach 129605 := rs (se 4 (by rfl) ⟨12150, by rfl⟩) (B 24301 (by norm_num) ⟨12150, by rfl⟩ (by norm_num))
theorem R96853 : Reach 96853 := rs (se 8 (by rfl) ⟨567, by rfl⟩) (B 1135 (by norm_num) ⟨567, by rfl⟩ (by norm_num))
theorem R129629 : Reach 129629 := rs (se 3 (by rfl) ⟨24305, by rfl⟩) (B 48611 (by norm_num) ⟨24305, by rfl⟩ (by norm_num))
theorem R195173 : Reach 195173 := rs (se 4 (by rfl) ⟨18297, by rfl⟩) (B 36595 (by norm_num) ⟨18297, by rfl⟩ (by norm_num))
theorem R129653 : Reach 129653 := rs (se 5 (by rfl) ⟨6077, by rfl⟩) (B 12155 (by norm_num) ⟨6077, by rfl⟩ (by norm_num))
theorem R96889 : Reach 96889 := rs (se 2 (by rfl) ⟨36333, by rfl⟩) (B 72667 (by norm_num) ⟨36333, by rfl⟩ (by norm_num))
theorem R129677 : Reach 129677 := rs (se 3 (by rfl) ⟨24314, by rfl⟩) (B 48629 (by norm_num) ⟨24314, by rfl⟩ (by norm_num))
theorem R162461 : Reach 162461 := rs (se 3 (by rfl) ⟨30461, by rfl⟩) (B 60923 (by norm_num) ⟨30461, by rfl⟩ (by norm_num))
theorem R96925 : Reach 96925 := rs (se 3 (by rfl) ⟨18173, by rfl⟩) (B 36347 (by norm_num) ⟨18173, by rfl⟩ (by norm_num))
theorem R129701 : Reach 129701 := rs (se 4 (by rfl) ⟨12159, by rfl⟩) (B 24319 (by norm_num) ⟨12159, by rfl⟩ (by norm_num))
theorem R195245 : Reach 195245 := rs (se 3 (by rfl) ⟨36608, by rfl⟩) (B 73217 (by norm_num) ⟨36608, by rfl⟩ (by norm_num))
theorem R129725 : Reach 129725 := rs (se 3 (by rfl) ⟨24323, by rfl⟩) (B 48647 (by norm_num) ⟨24323, by rfl⟩ (by norm_num))
theorem R96961 : Reach 96961 := rs (se 2 (by rfl) ⟨36360, by rfl⟩) (B 72721 (by norm_num) ⟨36360, by rfl⟩ (by norm_num))
theorem R129749 : Reach 129749 := rs (se 7 (by rfl) ⟨1520, by rfl⟩) (B 3041 (by norm_num) ⟨1520, by rfl⟩ (by norm_num))
theorem R96997 : Reach 96997 := rs (se 4 (by rfl) ⟨9093, by rfl⟩) (B 18187 (by norm_num) ⟨9093, by rfl⟩ (by norm_num))
theorem R129773 : Reach 129773 := rs (se 3 (by rfl) ⟨24332, by rfl⟩) (B 48665 (by norm_num) ⟨24332, by rfl⟩ (by norm_num))
theorem R195317 : Reach 195317 := rs (se 5 (by rfl) ⟨9155, by rfl⟩) (B 18311 (by norm_num) ⟨9155, by rfl⟩ (by norm_num))
theorem R326405 : Reach 326405 := rs (se 4 (by rfl) ⟨30600, by rfl⟩) (B 61201 (by norm_num) ⟨30600, by rfl⟩ (by norm_num))
theorem R129797 : Reach 129797 := rs (se 4 (by rfl) ⟨12168, by rfl⟩) (B 24337 (by norm_num) ⟨12168, by rfl⟩ (by norm_num))
theorem R97033 : Reach 97033 := rs (se 2 (by rfl) ⟨36387, by rfl⟩) (B 72775 (by norm_num) ⟨36387, by rfl⟩ (by norm_num))
theorem R129821 : Reach 129821 := rs (se 3 (by rfl) ⟨24341, by rfl⟩) (B 48683 (by norm_num) ⟨24341, by rfl⟩ (by norm_num))
theorem R97069 : Reach 97069 := rs (se 3 (by rfl) ⟨18200, by rfl⟩) (B 36401 (by norm_num) ⟨18200, by rfl⟩ (by norm_num))
theorem R129845 : Reach 129845 := rs (se 5 (by rfl) ⟨6086, by rfl⟩) (B 12173 (by norm_num) ⟨6086, by rfl⟩ (by norm_num))
theorem R195389 : Reach 195389 := rs (se 3 (by rfl) ⟨36635, by rfl⟩) (B 73271 (by norm_num) ⟨36635, by rfl⟩ (by norm_num))
theorem R129869 : Reach 129869 := rs (se 3 (by rfl) ⟨24350, by rfl⟩) (B 48701 (by norm_num) ⟨24350, by rfl⟩ (by norm_num))
theorem R97105 : Reach 97105 := rs (se 2 (by rfl) ⟨36414, by rfl⟩) (B 72829 (by norm_num) ⟨36414, by rfl⟩ (by norm_num))
theorem R228181 : Reach 228181 := rs (se 9 (by rfl) ⟨668, by rfl⟩) (B 1337 (by norm_num) ⟨668, by rfl⟩ (by norm_num))
theorem R326501 : Reach 326501 := rs (se 4 (by rfl) ⟨30609, by rfl⟩) (B 61219 (by norm_num) ⟨30609, by rfl⟩ (by norm_num))
theorem R129893 : Reach 129893 := rs (se 4 (by rfl) ⟨12177, by rfl⟩) (B 24355 (by norm_num) ⟨12177, by rfl⟩ (by norm_num))
theorem R97141 : Reach 97141 := rs (se 5 (by rfl) ⟨4553, by rfl⟩) (B 9107 (by norm_num) ⟨4553, by rfl⟩ (by norm_num))
theorem R555893 : Reach 555893 := rs (se 5 (by rfl) ⟨26057, by rfl⟩) (B 52115 (by norm_num) ⟨26057, by rfl⟩ (by norm_num))
theorem R129917 : Reach 129917 := rs (se 3 (by rfl) ⟨24359, by rfl⟩) (B 48719 (by norm_num) ⟨24359, by rfl⟩ (by norm_num))
theorem R195461 : Reach 195461 := rs (se 4 (by rfl) ⟨18324, by rfl⟩) (B 36649 (by norm_num) ⟨18324, by rfl⟩ (by norm_num))
theorem R719765 : Reach 719765 := rs (se 6 (by rfl) ⟨16869, by rfl⟩) (B 33739 (by norm_num) ⟨16869, by rfl⟩ (by norm_num))
theorem R129941 : Reach 129941 := rs (se 6 (by rfl) ⟨3045, by rfl⟩) (B 6091 (by norm_num) ⟨3045, by rfl⟩ (by norm_num))
theorem R97177 : Reach 97177 := rs (se 2 (by rfl) ⟨36441, by rfl⟩) (B 72883 (by norm_num) ⟨36441, by rfl⟩ (by norm_num))
theorem R129965 : Reach 129965 := rs (se 3 (by rfl) ⟨24368, by rfl⟩) (B 48737 (by norm_num) ⟨24368, by rfl⟩ (by norm_num))
theorem R293813 : Reach 293813 := rs (se 5 (by rfl) ⟨13772, by rfl⟩) (B 27545 (by norm_num) ⟨13772, by rfl⟩ (by norm_num))
theorem R162749 : Reach 162749 := rs (se 3 (by rfl) ⟨30515, by rfl⟩) (B 61031 (by norm_num) ⟨30515, by rfl⟩ (by norm_num))
theorem R97213 : Reach 97213 := rs (se 3 (by rfl) ⟨18227, by rfl⟩) (B 36455 (by norm_num) ⟨18227, by rfl⟩ (by norm_num))
theorem R129989 : Reach 129989 := rs (se 4 (by rfl) ⟨12186, by rfl⟩) (B 24373 (by norm_num) ⟨12186, by rfl⟩ (by norm_num))
theorem R195533 : Reach 195533 := rs (se 3 (by rfl) ⟨36662, by rfl⟩) (B 73325 (by norm_num) ⟨36662, by rfl⟩ (by norm_num))
theorem R130013 : Reach 130013 := rs (se 3 (by rfl) ⟨24377, by rfl⟩) (B 48755 (by norm_num) ⟨24377, by rfl⟩ (by norm_num))
theorem R97249 : Reach 97249 := rs (se 2 (by rfl) ⟨36468, by rfl⟩) (B 72937 (by norm_num) ⟨36468, by rfl⟩ (by norm_num))
theorem R130037 : Reach 130037 := rs (se 5 (by rfl) ⟨6095, by rfl⟩) (B 12191 (by norm_num) ⟨6095, by rfl⟩ (by norm_num))
theorem R97285 : Reach 97285 := rs (se 4 (by rfl) ⟨9120, by rfl⟩) (B 18241 (by norm_num) ⟨9120, by rfl⟩ (by norm_num))
theorem R130061 : Reach 130061 := rs (se 3 (by rfl) ⟨24386, by rfl⟩) (B 48773 (by norm_num) ⟨24386, by rfl⟩ (by norm_num))
theorem R195605 : Reach 195605 := rs (se 6 (by rfl) ⟨4584, by rfl⟩) (B 9169 (by norm_num) ⟨4584, by rfl⟩ (by norm_num))
theorem R130085 : Reach 130085 := rs (se 4 (by rfl) ⟨12195, by rfl⟩) (B 24391 (by norm_num) ⟨12195, by rfl⟩ (by norm_num))
theorem R97321 : Reach 97321 := rs (se 2 (by rfl) ⟨36495, by rfl⟩) (B 72991 (by norm_num) ⟨36495, by rfl⟩ (by norm_num))
theorem R130109 : Reach 130109 := rs (se 3 (by rfl) ⟨24395, by rfl⟩) (B 48791 (by norm_num) ⟨24395, by rfl⟩ (by norm_num))
theorem R97357 : Reach 97357 := rs (se 3 (by rfl) ⟨18254, by rfl⟩) (B 36509 (by norm_num) ⟨18254, by rfl⟩ (by norm_num))
theorem R162901 : Reach 162901 := rs (se 8 (by rfl) ⟨954, by rfl⟩) (B 1909 (by norm_num) ⟨954, by rfl⟩ (by norm_num))
theorem R130133 : Reach 130133 := rs (se 8 (by rfl) ⟨762, by rfl⟩) (B 1525 (by norm_num) ⟨762, by rfl⟩ (by norm_num))
theorem R195677 : Reach 195677 := rs (se 3 (by rfl) ⟨36689, by rfl⟩) (B 73379 (by norm_num) ⟨36689, by rfl⟩ (by norm_num))
theorem R130157 : Reach 130157 := rs (se 3 (by rfl) ⟨24404, by rfl⟩) (B 48809 (by norm_num) ⟨24404, by rfl⟩ (by norm_num))
theorem R97393 : Reach 97393 := rs (se 2 (by rfl) ⟨36522, by rfl⟩) (B 73045 (by norm_num) ⟨36522, by rfl⟩ (by norm_num))
theorem R130181 : Reach 130181 := rs (se 4 (by rfl) ⟨12204, by rfl⟩) (B 24409 (by norm_num) ⟨12204, by rfl⟩ (by norm_num))
theorem R97429 : Reach 97429 := rs (se 6 (by rfl) ⟨2283, by rfl⟩) (B 4567 (by norm_num) ⟨2283, by rfl⟩ (by norm_num))
theorem R130205 : Reach 130205 := rs (se 3 (by rfl) ⟨24413, by rfl⟩) (B 48827 (by norm_num) ⟨24413, by rfl⟩ (by norm_num))
theorem R195749 : Reach 195749 := rs (se 4 (by rfl) ⟨18351, by rfl⟩) (B 36703 (by norm_num) ⟨18351, by rfl⟩ (by norm_num))
theorem R130229 : Reach 130229 := rs (se 5 (by rfl) ⟨6104, by rfl⟩) (B 12209 (by norm_num) ⟨6104, by rfl⟩ (by norm_num))
theorem R97465 : Reach 97465 := rs (se 2 (by rfl) ⟨36549, by rfl⟩) (B 73099 (by norm_num) ⟨36549, by rfl⟩ (by norm_num))
theorem R130253 : Reach 130253 := rs (se 3 (by rfl) ⟨24422, by rfl⟩) (B 48845 (by norm_num) ⟨24422, by rfl⟩ (by norm_num))
theorem R195805 : Reach 195805 := rs (se 3 (by rfl) ⟨36713, by rfl⟩) (B 73427 (by norm_num) ⟨36713, by rfl⟩ (by norm_num))
theorem R97501 : Reach 97501 := rs (se 3 (by rfl) ⟨18281, by rfl⟩) (B 36563 (by norm_num) ⟨18281, by rfl⟩ (by norm_num))
theorem R130277 : Reach 130277 := rs (se 4 (by rfl) ⟨12213, by rfl⟩) (B 24427 (by norm_num) ⟨12213, by rfl⟩ (by norm_num))
theorem R195821 : Reach 195821 := rs (se 3 (by rfl) ⟨36716, by rfl⟩) (B 73433 (by norm_num) ⟨36716, by rfl⟩ (by norm_num))
theorem R130301 : Reach 130301 := rs (se 3 (by rfl) ⟨24431, by rfl⟩) (B 48863 (by norm_num) ⟨24431, by rfl⟩ (by norm_num))
theorem R97537 : Reach 97537 := rs (se 2 (by rfl) ⟨36576, by rfl⟩) (B 73153 (by norm_num) ⟨36576, by rfl⟩ (by norm_num))
theorem R130325 : Reach 130325 := rs (se 6 (by rfl) ⟨3054, by rfl⟩) (B 6109 (by norm_num) ⟨3054, by rfl⟩ (by norm_num))
theorem R97573 : Reach 97573 := rs (se 4 (by rfl) ⟨9147, by rfl⟩) (B 18295 (by norm_num) ⟨9147, by rfl⟩ (by norm_num))
theorem R130349 : Reach 130349 := rs (se 3 (by rfl) ⟨24440, by rfl⟩) (B 48881 (by norm_num) ⟨24440, by rfl⟩ (by norm_num))
theorem R195893 : Reach 195893 := rs (se 5 (by rfl) ⟨9182, by rfl⟩) (B 18365 (by norm_num) ⟨9182, by rfl⟩ (by norm_num))
theorem R130373 : Reach 130373 := rs (se 4 (by rfl) ⟨12222, by rfl⟩) (B 24445 (by norm_num) ⟨12222, by rfl⟩ (by norm_num))
theorem R97609 : Reach 97609 := rs (se 2 (by rfl) ⟨36603, by rfl⟩) (B 73207 (by norm_num) ⟨36603, by rfl⟩ (by norm_num))
theorem R130397 : Reach 130397 := rs (se 3 (by rfl) ⟨24449, by rfl⟩) (B 48899 (by norm_num) ⟨24449, by rfl⟩ (by norm_num))
theorem R97645 : Reach 97645 := rs (se 3 (by rfl) ⟨18308, by rfl⟩) (B 36617 (by norm_num) ⟨18308, by rfl⟩ (by norm_num))
theorem R130421 : Reach 130421 := rs (se 5 (by rfl) ⟨6113, by rfl⟩) (B 12227 (by norm_num) ⟨6113, by rfl⟩ (by norm_num))
theorem R195965 : Reach 195965 := rs (se 3 (by rfl) ⟨36743, by rfl⟩) (B 73487 (by norm_num) ⟨36743, by rfl⟩ (by norm_num))
theorem R163205 : Reach 163205 := rs (se 4 (by rfl) ⟨15300, by rfl⟩) (B 30601 (by norm_num) ⟨15300, by rfl⟩ (by norm_num))
theorem R130445 : Reach 130445 := rs (se 3 (by rfl) ⟨24458, by rfl⟩) (B 48917 (by norm_num) ⟨24458, by rfl⟩ (by norm_num))
theorem R97681 : Reach 97681 := rs (se 2 (by rfl) ⟨36630, by rfl⟩) (B 73261 (by norm_num) ⟨36630, by rfl⟩ (by norm_num))
theorem R130469 : Reach 130469 := rs (se 4 (by rfl) ⟨12231, by rfl⟩) (B 24463 (by norm_num) ⟨12231, by rfl⟩ (by norm_num))
theorem R97717 : Reach 97717 := rs (se 5 (by rfl) ⟨4580, by rfl⟩) (B 9161 (by norm_num) ⟨4580, by rfl⟩ (by norm_num))
theorem R130493 : Reach 130493 := rs (se 3 (by rfl) ⟨24467, by rfl⟩) (B 48935 (by norm_num) ⟨24467, by rfl⟩ (by norm_num))
theorem R196037 : Reach 196037 := rs (se 4 (by rfl) ⟨18378, by rfl⟩) (B 36757 (by norm_num) ⟨18378, by rfl⟩ (by norm_num))
theorem R261589 : Reach 261589 := rs (se 7 (by rfl) ⟨3065, by rfl⟩) (B 6131 (by norm_num) ⟨3065, by rfl⟩ (by norm_num))
theorem R130517 : Reach 130517 := rs (se 7 (by rfl) ⟨1529, by rfl⟩) (B 3059 (by norm_num) ⟨1529, by rfl⟩ (by norm_num))
theorem R97753 : Reach 97753 := rs (se 2 (by rfl) ⟨36657, by rfl⟩) (B 73315 (by norm_num) ⟨36657, by rfl⟩ (by norm_num))
theorem R130541 : Reach 130541 := rs (se 3 (by rfl) ⟨24476, by rfl⟩) (B 48953 (by norm_num) ⟨24476, by rfl⟩ (by norm_num))
theorem R97789 : Reach 97789 := rs (se 3 (by rfl) ⟨18335, by rfl⟩) (B 36671 (by norm_num) ⟨18335, by rfl⟩ (by norm_num))
theorem R130565 : Reach 130565 := rs (se 4 (by rfl) ⟨12240, by rfl⟩) (B 24481 (by norm_num) ⟨12240, by rfl⟩ (by norm_num))
theorem R130589 : Reach 130589 := rs (se 3 (by rfl) ⟨24485, by rfl⟩) (B 48971 (by norm_num) ⟨24485, by rfl⟩ (by norm_num))
theorem R97825 : Reach 97825 := rs (se 2 (by rfl) ⟨36684, by rfl⟩) (B 73369 (by norm_num) ⟨36684, by rfl⟩ (by norm_num))
theorem R130613 : Reach 130613 := rs (se 5 (by rfl) ⟨6122, by rfl⟩) (B 12245 (by norm_num) ⟨6122, by rfl⟩ (by norm_num))
theorem R97861 : Reach 97861 := rs (se 4 (by rfl) ⟨9174, by rfl⟩) (B 18349 (by norm_num) ⟨9174, by rfl⟩ (by norm_num))
theorem R130637 : Reach 130637 := rs (se 3 (by rfl) ⟨24494, by rfl⟩) (B 48989 (by norm_num) ⟨24494, by rfl⟩ (by norm_num))
theorem R425573 : Reach 425573 := rs (se 4 (by rfl) ⟨39897, by rfl⟩) (B 79795 (by norm_num) ⟨39897, by rfl⟩ (by norm_num))
theorem R130661 : Reach 130661 := rs (se 4 (by rfl) ⟨12249, by rfl⟩) (B 24499 (by norm_num) ⟨12249, by rfl⟩ (by norm_num))
theorem R97897 : Reach 97897 := rs (se 2 (by rfl) ⟨36711, by rfl⟩) (B 73423 (by norm_num) ⟨36711, by rfl⟩ (by norm_num))
theorem R130685 : Reach 130685 := rs (se 3 (by rfl) ⟨24503, by rfl⟩) (B 49007 (by norm_num) ⟨24503, by rfl⟩ (by norm_num))
theorem R97933 : Reach 97933 := rs (se 3 (by rfl) ⟨18362, by rfl⟩) (B 36725 (by norm_num) ⟨18362, by rfl⟩ (by norm_num))
theorem R97969 : Reach 97969 := rs (se 2 (by rfl) ⟨36738, by rfl⟩) (B 73477 (by norm_num) ⟨36738, by rfl⟩ (by norm_num))
theorem R98005 : Reach 98005 := rs (se 7 (by rfl) ⟨1148, by rfl⟩) (B 2297 (by norm_num) ⟨1148, by rfl⟩ (by norm_num))
theorem R98281 : Reach 98281 := rs (se 2 (by rfl) ⟨36855, by rfl⟩) (B 73711 (by norm_num) ⟨36855, by rfl⟩ (by norm_num))
theorem R262253 : Reach 262253 := rs (se 3 (by rfl) ⟨49172, by rfl⟩) R98345
theorem R1474757 : Reach 1474757 := rs (se 4 (by rfl) ⟨138258, by rfl⟩) R276517
theorem R262349 : Reach 262349 := rs (se 3 (by rfl) ⟨49190, by rfl⟩) R98381
theorem R262435 : Reach 262435 := rs (se 1 (by rfl) ⟨196826, by rfl⟩) R393653
theorem R164177 : Reach 164177 := rs (se 2 (by rfl) ⟨61566, by rfl⟩) R123133
theorem R491939 : Reach 491939 := rs (se 1 (by rfl) ⟨368954, by rfl⟩) R737909
theorem R360931 : Reach 360931 := rs (se 1 (by rfl) ⟨270698, by rfl⟩) R541397
theorem R328205 : Reach 328205 := rs (se 3 (by rfl) ⟨61538, by rfl⟩) R123077
theorem R98851 : Reach 98851 := rs (se 1 (by rfl) ⟨74138, by rfl⟩) R148277
theorem R426545 : Reach 426545 := rs (se 2 (by rfl) ⟨159954, by rfl⟩) R319909
theorem R787013 : Reach 787013 := rs (se 4 (by rfl) ⟨73782, by rfl⟩) R147565
theorem R656099 : Reach 656099 := rs (se 1 (by rfl) ⟨492074, by rfl⟩) R984149
theorem R1573829 : Reach 1573829 := rs (se 4 (by rfl) ⟨147546, by rfl⟩) R295093
theorem R165073 : Reach 165073 := rs (se 2 (by rfl) ⟨61902, by rfl⟩) R123805
theorem R230627 : Reach 230627 := rs (se 1 (by rfl) ⟨172970, by rfl⟩) R345941
theorem R328931 : Reach 328931 := rs (se 1 (by rfl) ⟨246698, by rfl⟩) R493397
theorem R132385 : Reach 132385 := rs (se 2 (by rfl) ⟨49644, by rfl⟩) R99289
theorem R886085 : Reach 886085 := rs (se 4 (by rfl) ⟨83070, by rfl⟩) R166141
theorem R165233 : Reach 165233 := rs (se 2 (by rfl) ⟨61962, by rfl⟩) R123925
theorem R853901 : Reach 853901 := rs (se 3 (by rfl) ⟨160106, by rfl⟩) R320213
theorem R428003 : Reach 428003 := rs (se 1 (by rfl) ⟨321002, by rfl⟩) R642005
theorem R133265 : Reach 133265 := rs (se 2 (by rfl) ⟨49974, by rfl⟩) R99949
theorem R329933 : Reach 329933 := rs (se 3 (by rfl) ⟨61862, by rfl⟩) R123725
theorem R100963 : Reach 100963 := rs (se 1 (by rfl) ⟨75722, by rfl⟩) R151445
theorem R428813 : Reach 428813 := rs (se 3 (by rfl) ⟨80402, by rfl⟩) R160805
theorem R101155 : Reach 101155 := rs (se 1 (by rfl) ⟨75866, by rfl⟩) R151733
theorem R134065 : Reach 134065 := rs (se 2 (by rfl) ⟨50274, by rfl⟩) R100549
theorem R232483 : Reach 232483 := rs (se 1 (by rfl) ⟨174362, by rfl⟩) R348725
theorem R920645 : Reach 920645 := rs (se 4 (by rfl) ⟨86310, by rfl⟩) R172621
theorem R363761 : Reach 363761 := rs (se 2 (by rfl) ⟨136410, by rfl⟩) R272821
theorem R167203 : Reach 167203 := rs (se 1 (by rfl) ⟨125402, by rfl⟩) R250805
theorem R101683 : Reach 101683 := rs (se 1 (by rfl) ⟨76262, by rfl⟩) R152525
theorem R1707317 : Reach 1707317 := rs (se 5 (by rfl) ⟨80030, by rfl⟩) R160061
theorem R101779 : Reach 101779 := rs (se 1 (by rfl) ⟨76334, by rfl⟩) R152669
theorem R233027 : Reach 233027 := rs (se 1 (by rfl) ⟨174770, by rfl⟩) R349541
theorem R495173 : Reach 495173 := rs (se 4 (by rfl) ⟨46422, by rfl⟩) R92845
theorem R691811 : Reach 691811 := rs (se 1 (by rfl) ⟨518858, by rfl⟩) R1037717
theorem R233155 : Reach 233155 := rs (se 1 (by rfl) ⟨174866, by rfl⟩) R349733
theorem R659141 : Reach 659141 := rs (se 4 (by rfl) ⟨61794, by rfl⟩) R123589
theorem R593677 : Reach 593677 := rs (se 3 (by rfl) ⟨111314, by rfl⟩) R222629
theorem R200465 : Reach 200465 := rs (se 2 (by rfl) ⟨75174, by rfl⟩) R150349
theorem R200483 : Reach 200483 := rs (se 1 (by rfl) ⟨150362, by rfl⟩) R300725
theorem R495629 : Reach 495629 := rs (se 3 (by rfl) ⟨92930, by rfl⟩) R185861
theorem R135283 : Reach 135283 := rs (se 1 (by rfl) ⟨101462, by rfl⟩) R202925
theorem R102755 : Reach 102755 := rs (se 1 (by rfl) ⟨77066, by rfl⟩) R154133
theorem R2036501 : Reach 2036501 := rs (se 6 (by rfl) ⟨47730, by rfl⟩) R95461
theorem R201521 : Reach 201521 := rs (se 2 (by rfl) ⟨75570, by rfl⟩) R151141
theorem R136001 : Reach 136001 := rs (se 2 (by rfl) ⟨51000, by rfl⟩) R102001
theorem R168785 : Reach 168785 := rs (se 2 (by rfl) ⟨63294, by rfl⟩) R126589
theorem R136289 : Reach 136289 := rs (se 2 (by rfl) ⟨51108, by rfl⟩) R102217
theorem R2823281 : Reach 2823281 := rs (se 2 (by rfl) ⟨1058730, by rfl⟩) R2117461
theorem R234659 : Reach 234659 := rs (se 1 (by rfl) ⟨175994, by rfl⟩) R351989
theorem R136513 : Reach 136513 := rs (se 2 (by rfl) ⟨51192, by rfl⟩) R102385
theorem R1578467 : Reach 1578467 := rs (se 1 (by rfl) ⟨1183850, by rfl⟩) R2367701
theorem R431729 : Reach 431729 := rs (se 2 (by rfl) ⟨161898, by rfl⟩) R323797
theorem R366221 : Reach 366221 := rs (se 3 (by rfl) ⟨68666, by rfl⟩) R137333
theorem R1447793 : Reach 1447793 := rs (se 2 (by rfl) ⟨542922, by rfl⟩) R1085845
theorem R661445 : Reach 661445 := rs (se 4 (by rfl) ⟨62010, by rfl⟩) R124021
theorem R268451 : Reach 268451 := rs (se 1 (by rfl) ⟨201338, by rfl⟩) R402677
theorem R2070755 : Reach 2070755 := rs (se 1 (by rfl) ⟨1553066, by rfl⟩) R3106133
theorem R268721 : Reach 268721 := rs (se 2 (by rfl) ⟨100770, by rfl⟩) R201541
theorem R694925 : Reach 694925 := rs (se 3 (by rfl) ⟨130298, by rfl⟩) R260597
theorem R138115 : Reach 138115 := rs (se 1 (by rfl) ⟨103586, by rfl⟩) R207173
theorem R367537 : Reach 367537 := rs (se 2 (by rfl) ⟨137826, by rfl⟩) R275653
theorem R433187 : Reach 433187 := rs (se 1 (by rfl) ⟨324890, by rfl⟩) R649781
theorem R269411 : Reach 269411 := rs (se 1 (by rfl) ⟨202058, by rfl⟩) R404117
theorem R105619 : Reach 105619 := rs (se 1 (by rfl) ⟨79214, by rfl⟩) R158429
theorem R105715 : Reach 105715 := rs (se 1 (by rfl) ⟨79286, by rfl⟩) R158573
theorem R335117 : Reach 335117 := rs (se 3 (by rfl) ⟨62834, by rfl⟩) R125669
theorem R106211 : Reach 106211 := rs (se 1 (by rfl) ⟨79658, by rfl⟩) R159317
theorem R433997 : Reach 433997 := rs (se 3 (by rfl) ⟨81374, by rfl⟩) R162749
theorem R237745 : Reach 237745 := rs (se 2 (by rfl) ⟨89154, by rfl⟩) R178309
theorem R139457 : Reach 139457 := rs (se 2 (by rfl) ⟨52296, by rfl⟩) R104593
theorem R172369 : Reach 172369 := rs (se 2 (by rfl) ⟨64638, by rfl⟩) R129277
theorem R1188209 : Reach 1188209 := rs (se 2 (by rfl) ⟨445578, by rfl⟩) R891157
theorem R106915 : Reach 106915 := rs (se 1 (by rfl) ⟨80186, by rfl⟩) R160373
theorem R107011 : Reach 107011 := rs (se 1 (by rfl) ⟨80258, by rfl⟩) R160517
theorem R467653 : Reach 467653 := rs (se 4 (by rfl) ⟨43842, by rfl⟩) R87685
theorem R271181 : Reach 271181 := rs (se 3 (by rfl) ⟨50846, by rfl⟩) R101693
theorem R271309 : Reach 271309 := rs (se 3 (by rfl) ⟨50870, by rfl⟩) R101741
theorem R107507 : Reach 107507 := rs (se 1 (by rfl) ⟨80630, by rfl⟩) R161261
theorem R500741 : Reach 500741 := rs (se 4 (by rfl) ⟨46944, by rfl⟩) R93889
theorem R140305 : Reach 140305 := rs (se 2 (by rfl) ⟨52614, by rfl⟩) R105229
theorem R140339 : Reach 140339 := rs (se 1 (by rfl) ⟨105254, by rfl⟩) R210509
theorem R304241 : Reach 304241 := rs (se 2 (by rfl) ⟨114090, by rfl⟩) R228181
theorem R205955 : Reach 205955 := rs (se 1 (by rfl) ⟨154466, by rfl⟩) R308933
theorem R140467 : Reach 140467 := rs (se 1 (by rfl) ⟨105350, by rfl⟩) R210701
theorem R271565 : Reach 271565 := rs (se 3 (by rfl) ⟨50918, by rfl⟩) R101837
theorem R140609 : Reach 140609 := rs (se 2 (by rfl) ⟨52728, by rfl⟩) R105457
theorem R107939 : Reach 107939 := rs (se 1 (by rfl) ⟨80954, by rfl⟩) R161909
theorem R239021 : Reach 239021 := rs (se 3 (by rfl) ⟨44816, by rfl⟩) R89633
theorem R140737 : Reach 140737 := rs (se 2 (by rfl) ⟨52776, by rfl⟩) R105553
theorem R140771 : Reach 140771 := rs (se 1 (by rfl) ⟨105578, by rfl⟩) R211157
theorem R173603 : Reach 173603 := rs (se 1 (by rfl) ⟨130202, by rfl⟩) R260405
theorem R140899 : Reach 140899 := rs (se 1 (by rfl) ⟨105674, by rfl⟩) R211349
theorem R239203 : Reach 239203 := rs (se 1 (by rfl) ⟨179402, by rfl⟩) R358805
theorem R239249 : Reach 239249 := rs (se 2 (by rfl) ⟨89718, by rfl⟩) R179437
theorem R108211 : Reach 108211 := rs (se 1 (by rfl) ⟨81158, by rfl⟩) R162317
theorem R141041 : Reach 141041 := rs (se 2 (by rfl) ⟨52890, by rfl⟩) R105781
theorem R108307 : Reach 108307 := rs (se 1 (by rfl) ⟨81230, by rfl⟩) R162461
theorem R141169 : Reach 141169 := rs (se 2 (by rfl) ⟨52938, by rfl⟩) R105877
theorem R141203 : Reach 141203 := rs (se 1 (by rfl) ⟨105902, by rfl⟩) R211805
theorem R370595 : Reach 370595 := rs (se 1 (by rfl) ⟨277946, by rfl⟩) R555893
theorem R141331 : Reach 141331 := rs (se 1 (by rfl) ⟨105998, by rfl⟩) R211997
theorem R141473 : Reach 141473 := rs (se 2 (by rfl) ⟨53052, by rfl⟩) R106105
theorem R108803 : Reach 108803 := rs (se 1 (by rfl) ⟨81602, by rfl⟩) R163205
theorem R3352853 : Reach 3352853 := rs (se 6 (by rfl) ⟨78582, by rfl⟩) R157165
theorem R141601 : Reach 141601 := rs (se 2 (by rfl) ⟨53100, by rfl⟩) R106201
theorem R960821 : Reach 960821 := rs (se 5 (by rfl) ⟨45038, by rfl⟩) R90077
theorem R141635 : Reach 141635 := rs (se 1 (by rfl) ⟨106226, by rfl⟩) R212453
theorem R403811 : Reach 403811 := rs (se 1 (by rfl) ⟨302858, by rfl⟩) R605717
theorem R141763 : Reach 141763 := rs (se 1 (by rfl) ⟨106322, by rfl⟩) R212645
theorem R404003 : Reach 404003 := rs (se 1 (by rfl) ⟨303002, by rfl⟩) R606005
theorem R141905 : Reach 141905 := rs (se 2 (by rfl) ⟨53214, by rfl⟩) R106429
theorem R436913 : Reach 436913 := rs (se 2 (by rfl) ⟨163842, by rfl⟩) R327685
theorem R273091 : Reach 273091 := rs (se 1 (by rfl) ⟨204818, by rfl⟩) R409637
theorem R142033 : Reach 142033 := rs (se 2 (by rfl) ⟨53262, by rfl⟩) R106525
theorem R142067 : Reach 142067 := rs (se 1 (by rfl) ⟨106550, by rfl⟩) R213101
theorem R371491 : Reach 371491 := rs (se 1 (by rfl) ⟨278618, by rfl⟩) R557237
theorem R142195 : Reach 142195 := rs (se 1 (by rfl) ⟨106646, by rfl⟩) R213293
theorem R109507 : Reach 109507 := rs (se 1 (by rfl) ⟨82130, by rfl⟩) R164261
theorem R142289 : Reach 142289 := rs (se 2 (by rfl) ⟨53358, by rfl⟩) R106717
theorem R142337 : Reach 142337 := rs (se 2 (by rfl) ⟨53376, by rfl⟩) R106753
theorem R109603 : Reach 109603 := rs (se 1 (by rfl) ⟨82202, by rfl⟩) R164405
theorem R240707 : Reach 240707 := rs (se 1 (by rfl) ⟨180530, by rfl⟩) R361061
theorem R207971 : Reach 207971 := rs (se 1 (by rfl) ⟨155978, by rfl⟩) R311957
theorem R142465 : Reach 142465 := rs (se 2 (by rfl) ⟨53424, by rfl⟩) R106849
theorem R142499 : Reach 142499 := rs (se 1 (by rfl) ⟨106874, by rfl⟩) R213749
theorem R142627 : Reach 142627 := rs (se 1 (by rfl) ⟨106970, by rfl⟩) R213941
theorem R142769 : Reach 142769 := rs (se 2 (by rfl) ⟨53538, by rfl⟩) R107077
theorem R110099 : Reach 110099 := rs (se 1 (by rfl) ⟨82574, by rfl⟩) R165149
theorem R142897 : Reach 142897 := rs (se 2 (by rfl) ⟨53586, by rfl⟩) R107173
theorem R142931 : Reach 142931 := rs (se 1 (by rfl) ⟨107198, by rfl⟩) R214397
theorem R667277 : Reach 667277 := rs (se 3 (by rfl) ⟨125114, by rfl⟩) R250229
theorem R143059 : Reach 143059 := rs (se 1 (by rfl) ⟨107294, by rfl⟩) R214589
theorem R405233 : Reach 405233 := rs (se 2 (by rfl) ⟨151962, by rfl⟩) R303925
theorem R143201 : Reach 143201 := rs (se 2 (by rfl) ⟨53700, by rfl⟩) R107401
theorem R176003 : Reach 176003 := rs (se 1 (by rfl) ⟨132002, by rfl⟩) R264005
theorem R339875 : Reach 339875 := rs (se 1 (by rfl) ⟨254906, by rfl⟩) R509813
theorem R143329 : Reach 143329 := rs (se 2 (by rfl) ⟨53748, by rfl⟩) R107497
theorem R143363 : Reach 143363 := rs (se 1 (by rfl) ⟨107522, by rfl⟩) R215045
theorem R143411 : Reach 143411 := rs (se 1 (by rfl) ⟨107558, by rfl⟩) R215117
theorem R438371 : Reach 438371 := rs (se 1 (by rfl) ⟨328778, by rfl⟩) R657557
theorem R143491 : Reach 143491 := rs (se 1 (by rfl) ⟨107618, by rfl⟩) R215237
theorem R209123 : Reach 209123 := rs (se 1 (by rfl) ⟨156842, by rfl⟩) R313685
theorem R274691 : Reach 274691 := rs (se 1 (by rfl) ⟨206018, by rfl⟩) R412037
theorem R241937 : Reach 241937 := rs (se 2 (by rfl) ⟨90726, by rfl⟩) R181453
theorem R143633 : Reach 143633 := rs (se 2 (by rfl) ⟨53862, by rfl⟩) R107725
theorem R143761 : Reach 143761 := rs (se 2 (by rfl) ⟨53910, by rfl⟩) R107821
theorem R438691 : Reach 438691 := rs (se 1 (by rfl) ⟨329018, by rfl⟩) R658037
theorem R143795 : Reach 143795 := rs (se 1 (by rfl) ⟨107846, by rfl⟩) R215693
theorem R143923 : Reach 143923 := rs (se 1 (by rfl) ⟨107942, by rfl⟩) R215885
theorem R144065 : Reach 144065 := rs (se 2 (by rfl) ⟨54024, by rfl⟩) R108049
theorem R144193 : Reach 144193 := rs (se 2 (by rfl) ⟨54072, by rfl⟩) R108145
theorem R144227 : Reach 144227 := rs (se 1 (by rfl) ⟨108170, by rfl⟩) R216341
theorem R439181 : Reach 439181 := rs (se 3 (by rfl) ⟨82346, by rfl⟩) R164693
theorem R144337 : Reach 144337 := rs (se 2 (by rfl) ⟨54126, by rfl⟩) R108253
theorem R144355 : Reach 144355 := rs (se 1 (by rfl) ⟨108266, by rfl⟩) R216533
theorem R406577 : Reach 406577 := rs (se 2 (by rfl) ⟨152466, by rfl⟩) R304933
theorem R144497 : Reach 144497 := rs (se 2 (by rfl) ⟨54186, by rfl⟩) R108373
theorem R701581 : Reach 701581 := rs (se 3 (by rfl) ⟨131546, by rfl⟩) R263093
theorem R144593 : Reach 144593 := rs (se 2 (by rfl) ⟨54222, by rfl⟩) R108445
theorem R275665 : Reach 275665 := rs (se 2 (by rfl) ⟨103374, by rfl⟩) R206749
theorem R144625 : Reach 144625 := rs (se 2 (by rfl) ⟨54234, by rfl⟩) R108469
theorem R636173 : Reach 636173 := rs (se 3 (by rfl) ⟨119282, by rfl⟩) R238565
theorem R144659 : Reach 144659 := rs (se 1 (by rfl) ⟨108494, by rfl⟩) R216989
theorem R832837 : Reach 832837 := rs (se 4 (by rfl) ⟨78078, by rfl⟩) R156157
theorem R144787 : Reach 144787 := rs (se 1 (by rfl) ⟨108590, by rfl⟩) R217181
theorem R144929 : Reach 144929 := rs (se 2 (by rfl) ⟨54348, by rfl⟩) R108697
theorem R308771 : Reach 308771 := rs (se 1 (by rfl) ⟨231578, by rfl⟩) R463157
theorem R145057 : Reach 145057 := rs (se 2 (by rfl) ⟨54396, by rfl⟩) R108793
theorem R243395 : Reach 243395 := rs (se 1 (by rfl) ⟨182546, by rfl⟩) R365093
theorem R145091 : Reach 145091 := rs (se 1 (by rfl) ⟨108818, by rfl⟩) R217637
theorem R145219 : Reach 145219 := rs (se 1 (by rfl) ⟨108914, by rfl⟩) R217829
theorem R210833 : Reach 210833 := rs (se 2 (by rfl) ⟨79062, by rfl⟩) R158125
theorem R210883 : Reach 210883 := rs (se 1 (by rfl) ⟨158162, by rfl⟩) R316325
theorem R407501 : Reach 407501 := rs (se 3 (by rfl) ⟨76406, by rfl⟩) R152813
theorem R145361 : Reach 145361 := rs (se 2 (by rfl) ⟨54510, by rfl⟩) R109021
theorem R538595 : Reach 538595 := rs (se 1 (by rfl) ⟨403946, by rfl⟩) R807893
theorem R211025 : Reach 211025 := rs (se 2 (by rfl) ⟨79134, by rfl⟩) R158269
theorem R145489 : Reach 145489 := rs (se 2 (by rfl) ⟨54558, by rfl⟩) R109117
theorem R145523 : Reach 145523 := rs (se 1 (by rfl) ⟨109142, by rfl⟩) R218285
theorem R407693 : Reach 407693 := rs (se 3 (by rfl) ⟨76442, by rfl⟩) R152885
theorem R145651 : Reach 145651 := rs (se 1 (by rfl) ⟨109238, by rfl⟩) R218477
theorem R145793 : Reach 145793 := rs (se 2 (by rfl) ⟨54672, by rfl⟩) R109345
theorem R473485 : Reach 473485 := rs (se 3 (by rfl) ⟨88778, by rfl⟩) R177557
theorem R244205 : Reach 244205 := rs (se 3 (by rfl) ⟨45788, by rfl⟩) R91577
theorem R145921 : Reach 145921 := rs (se 2 (by rfl) ⟨54720, by rfl⟩) R109441
theorem R145955 : Reach 145955 := rs (se 1 (by rfl) ⟨109466, by rfl⟩) R218933
theorem R440909 : Reach 440909 := rs (se 3 (by rfl) ⟨82670, by rfl⟩) R165341
theorem R146083 : Reach 146083 := rs (se 1 (by rfl) ⟨109562, by rfl⟩) R219125
theorem R244397 : Reach 244397 := rs (se 3 (by rfl) ⟨45824, by rfl⟩) R91649
theorem R146225 : Reach 146225 := rs (se 2 (by rfl) ⟨54834, by rfl⟩) R109669
theorem R277357 : Reach 277357 := rs (se 3 (by rfl) ⟨52004, by rfl⟩) R104009
theorem R146353 : Reach 146353 := rs (se 2 (by rfl) ⟨54882, by rfl⟩) R109765
theorem R277453 : Reach 277453 := rs (se 3 (by rfl) ⟨52022, by rfl⟩) R104045
theorem R146387 : Reach 146387 := rs (se 1 (by rfl) ⟨109790, by rfl⟩) R219581
theorem R212017 : Reach 212017 := rs (se 2 (by rfl) ⟨79506, by rfl⟩) R159013
theorem R146515 : Reach 146515 := rs (se 1 (by rfl) ⟨109886, by rfl⟩) R219773
theorem R113827 : Reach 113827 := rs (se 1 (by rfl) ⟨85370, by rfl⟩) R170741
theorem R146657 : Reach 146657 := rs (se 2 (by rfl) ⟨54996, by rfl⟩) R109993
theorem R212291 : Reach 212291 := rs (se 1 (by rfl) ⟨159218, by rfl⟩) R318437
theorem R146785 : Reach 146785 := rs (se 2 (by rfl) ⟨55044, by rfl⟩) R110089
theorem R146819 : Reach 146819 := rs (se 1 (by rfl) ⟨110114, by rfl⟩) R220229
theorem R408995 : Reach 408995 := rs (se 1 (by rfl) ⟨306746, by rfl⟩) R613493
theorem R343523 : Reach 343523 := rs (se 1 (by rfl) ⟨257642, by rfl⟩) R515285
theorem R507377 : Reach 507377 := rs (se 2 (by rfl) ⟨190266, by rfl⟩) R380533
theorem R212483 : Reach 212483 := rs (se 1 (by rfl) ⟨159362, by rfl⟩) R318725
theorem R146947 : Reach 146947 := rs (se 1 (by rfl) ⟨110210, by rfl⟩) R220421
theorem R179779 : Reach 179779 := rs (se 1 (by rfl) ⟨134834, by rfl⟩) R269669
theorem R376397 : Reach 376397 := rs (se 3 (by rfl) ⟨70574, by rfl⟩) R141149
theorem R147025 : Reach 147025 := rs (se 2 (by rfl) ⟨55134, by rfl⟩) R110269
theorem R245389 : Reach 245389 := rs (se 3 (by rfl) ⟨46010, by rfl⟩) R92021
theorem R376589 : Reach 376589 := rs (se 3 (by rfl) ⟨70610, by rfl⟩) R141221
theorem R2015117 : Reach 2015117 := rs (se 3 (by rfl) ⟨377834, by rfl⟩) R755669
theorem R639089 : Reach 639089 := rs (se 2 (by rfl) ⟨239658, by rfl⟩) R479317
theorem R475469 : Reach 475469 := rs (se 3 (by rfl) ⟨89150, by rfl⟩) R178301
theorem R147811 : Reach 147811 := rs (se 1 (by rfl) ⟨110858, by rfl⟩) R221717
theorem R180625 : Reach 180625 := rs (se 2 (by rfl) ⟨67734, by rfl⟩) R135469
theorem R213425 : Reach 213425 := rs (se 2 (by rfl) ⟨80034, by rfl⟩) R160069
theorem R213475 : Reach 213475 := rs (se 1 (by rfl) ⟨160106, by rfl⟩) R320213
theorem R213617 : Reach 213617 := rs (se 2 (by rfl) ⟨80106, by rfl⟩) R160213
theorem R115363 : Reach 115363 := rs (se 1 (by rfl) ⟨86522, by rfl⟩) R173045
theorem R1000133 : Reach 1000133 := rs (se 4 (by rfl) ⟨93762, by rfl⟩) R187525
theorem R115715 : Reach 115715 := rs (se 1 (by rfl) ⟨86786, by rfl⟩) R173573
theorem R312461 : Reach 312461 := rs (se 3 (by rfl) ⟨58586, by rfl⟩) R117173
theorem R83139 : Reach 83139 := rs (se 1 (by rfl) ⟨62354, by rfl⟩) R124709
theorem R83155 : Reach 83155 := rs (se 1 (by rfl) ⟨62366, by rfl⟩) R124733
theorem R83171 : Reach 83171 := rs (se 1 (by rfl) ⟨62378, by rfl⟩) R124757
theorem R476401 : Reach 476401 := rs (se 2 (by rfl) ⟨178650, by rfl⟩) R357301
theorem R83187 : Reach 83187 := rs (se 1 (by rfl) ⟨62390, by rfl⟩) R124781
theorem R83203 : Reach 83203 := rs (se 1 (by rfl) ⟨62402, by rfl⟩) R124805
theorem R83219 : Reach 83219 := rs (se 1 (by rfl) ⟨62414, by rfl⟩) R124829
theorem R83235 : Reach 83235 := rs (se 1 (by rfl) ⟨62426, by rfl⟩) R124853
theorem R83251 : Reach 83251 := rs (se 1 (by rfl) ⟨62438, by rfl⟩) R124877
theorem R83267 : Reach 83267 := rs (se 1 (by rfl) ⟨62450, by rfl⟩) R124901
theorem R247121 : Reach 247121 := rs (se 2 (by rfl) ⟨92670, by rfl⟩) R185341
theorem R83283 : Reach 83283 := rs (se 1 (by rfl) ⟨62462, by rfl⟩) R124925
theorem R83299 : Reach 83299 := rs (se 1 (by rfl) ⟨62474, by rfl⟩) R124949
theorem R738659 : Reach 738659 := rs (se 1 (by rfl) ⟨553994, by rfl⟩) R1107989
theorem R83315 : Reach 83315 := rs (se 1 (by rfl) ⟨62486, by rfl⟩) R124973
theorem R83331 : Reach 83331 := rs (se 1 (by rfl) ⟨62498, by rfl⟩) R124997
theorem R83347 : Reach 83347 := rs (se 1 (by rfl) ⟨62510, by rfl⟩) R125021
theorem R83363 : Reach 83363 := rs (se 1 (by rfl) ⟨62522, by rfl⟩) R125045
theorem R83379 : Reach 83379 := rs (se 1 (by rfl) ⟨62534, by rfl⟩) R125069
theorem R83395 : Reach 83395 := rs (se 1 (by rfl) ⟨62546, by rfl⟩) R125093
theorem R83411 : Reach 83411 := rs (se 1 (by rfl) ⟨62558, by rfl⟩) R125117
theorem R83427 : Reach 83427 := rs (se 1 (by rfl) ⟨62570, by rfl⟩) R125141
theorem R83443 : Reach 83443 := rs (se 1 (by rfl) ⟨62582, by rfl⟩) R125165
theorem R83459 : Reach 83459 := rs (se 1 (by rfl) ⟨62594, by rfl⟩) R125189
theorem R83475 : Reach 83475 := rs (se 1 (by rfl) ⟨62606, by rfl⟩) R125213
theorem R247313 : Reach 247313 := rs (se 2 (by rfl) ⟨92742, by rfl⟩) R185485
theorem R83491 : Reach 83491 := rs (se 1 (by rfl) ⟨62618, by rfl⟩) R125237
theorem R83507 : Reach 83507 := rs (se 1 (by rfl) ⟨62630, by rfl⟩) R125261
theorem R83523 : Reach 83523 := rs (se 1 (by rfl) ⟨62642, by rfl⟩) R125285
theorem R542285 : Reach 542285 := rs (se 3 (by rfl) ⟨101678, by rfl⟩) R203357
theorem R214609 : Reach 214609 := rs (se 2 (by rfl) ⟨80478, by rfl⟩) R160957
theorem R83539 : Reach 83539 := rs (se 1 (by rfl) ⟨62654, by rfl⟩) R125309
theorem R83555 : Reach 83555 := rs (se 1 (by rfl) ⟨62666, by rfl⟩) R125333
theorem R83571 : Reach 83571 := rs (se 1 (by rfl) ⟨62678, by rfl⟩) R125357
theorem R83587 : Reach 83587 := rs (se 1 (by rfl) ⟨62690, by rfl⟩) R125381
theorem R83603 : Reach 83603 := rs (se 1 (by rfl) ⟨62702, by rfl⟩) R125405
theorem R83619 : Reach 83619 := rs (se 1 (by rfl) ⟨62714, by rfl⟩) R125429
theorem R83635 : Reach 83635 := rs (se 1 (by rfl) ⟨62726, by rfl⟩) R125453
theorem R83651 : Reach 83651 := rs (se 1 (by rfl) ⟨62738, by rfl⟩) R125477
theorem R83667 : Reach 83667 := rs (se 1 (by rfl) ⟨62750, by rfl⟩) R125501
theorem R83683 : Reach 83683 := rs (se 1 (by rfl) ⟨62762, by rfl⟩) R125525
theorem R83699 : Reach 83699 := rs (se 1 (by rfl) ⟨62774, by rfl⟩) R125549
theorem R83715 : Reach 83715 := rs (se 1 (by rfl) ⟨62786, by rfl⟩) R125573
theorem R83731 : Reach 83731 := rs (se 1 (by rfl) ⟨62798, by rfl⟩) R125597
theorem R83747 : Reach 83747 := rs (se 1 (by rfl) ⟨62810, by rfl⟩) R125621
theorem R542513 : Reach 542513 := rs (se 2 (by rfl) ⟨203442, by rfl⟩) R406885
theorem R83763 : Reach 83763 := rs (se 1 (by rfl) ⟨62822, by rfl⟩) R125645
theorem R83779 : Reach 83779 := rs (se 1 (by rfl) ⟨62834, by rfl⟩) R125669
theorem R83795 : Reach 83795 := rs (se 1 (by rfl) ⟨62846, by rfl⟩) R125693
theorem R83811 : Reach 83811 := rs (se 1 (by rfl) ⟨62858, by rfl⟩) R125717
theorem R214883 : Reach 214883 := rs (se 1 (by rfl) ⟨161162, by rfl⟩) R322325
theorem R83827 : Reach 83827 := rs (se 1 (by rfl) ⟨62870, by rfl⟩) R125741
theorem R83843 : Reach 83843 := rs (se 1 (by rfl) ⟨62882, by rfl⟩) R125765
theorem R83859 : Reach 83859 := rs (se 1 (by rfl) ⟨62894, by rfl⟩) R125789
theorem R83875 : Reach 83875 := rs (se 1 (by rfl) ⟨62906, by rfl⟩) R125813
theorem R83891 : Reach 83891 := rs (se 1 (by rfl) ⟨62918, by rfl⟩) R125837
theorem R83907 : Reach 83907 := rs (se 1 (by rfl) ⟨62930, by rfl⟩) R125861
theorem R83923 : Reach 83923 := rs (se 1 (by rfl) ⟨62942, by rfl⟩) R125885
theorem R83939 : Reach 83939 := rs (se 1 (by rfl) ⟨62954, by rfl⟩) R125909
theorem R83955 : Reach 83955 := rs (se 1 (by rfl) ⟨62966, by rfl⟩) R125933
theorem R83971 : Reach 83971 := rs (se 1 (by rfl) ⟨62978, by rfl⟩) R125957
theorem R83987 : Reach 83987 := rs (se 1 (by rfl) ⟨62990, by rfl⟩) R125981
theorem R84003 : Reach 84003 := rs (se 1 (by rfl) ⟨63002, by rfl⟩) R126005
theorem R215075 : Reach 215075 := rs (se 1 (by rfl) ⟨161306, by rfl⟩) R322613
theorem R84019 : Reach 84019 := rs (se 1 (by rfl) ⟨63014, by rfl⟩) R126029
theorem R84035 : Reach 84035 := rs (se 1 (by rfl) ⟨63026, by rfl⟩) R126053
theorem R84051 : Reach 84051 := rs (se 1 (by rfl) ⟨63038, by rfl⟩) R126077
theorem R84067 : Reach 84067 := rs (se 1 (by rfl) ⟨63050, by rfl⟩) R126101
theorem R280675 : Reach 280675 := rs (se 1 (by rfl) ⟨210506, by rfl⟩) R421013
theorem R84083 : Reach 84083 := rs (se 1 (by rfl) ⟨63062, by rfl⟩) R126125
theorem R84099 : Reach 84099 := rs (se 1 (by rfl) ⟨63074, by rfl⟩) R126149
theorem R84115 : Reach 84115 := rs (se 1 (by rfl) ⟨63086, by rfl⟩) R126173
theorem R84131 : Reach 84131 := rs (se 1 (by rfl) ⟨63098, by rfl⟩) R126197
theorem R84147 : Reach 84147 := rs (se 1 (by rfl) ⟨63110, by rfl⟩) R126221
theorem R84163 : Reach 84163 := rs (se 1 (by rfl) ⟨63122, by rfl⟩) R126245
theorem R84179 : Reach 84179 := rs (se 1 (by rfl) ⟨63134, by rfl⟩) R126269
theorem R84195 : Reach 84195 := rs (se 1 (by rfl) ⟨63146, by rfl⟩) R126293
theorem R182513 : Reach 182513 := rs (se 2 (by rfl) ⟨68442, by rfl⟩) R136885
theorem R84211 : Reach 84211 := rs (se 1 (by rfl) ⟨63158, by rfl⟩) R126317
theorem R84227 : Reach 84227 := rs (se 1 (by rfl) ⟨63170, by rfl⟩) R126341
theorem R84243 : Reach 84243 := rs (se 1 (by rfl) ⟨63182, by rfl⟩) R126365
theorem R84259 : Reach 84259 := rs (se 1 (by rfl) ⟨63194, by rfl⟩) R126389
theorem R84275 : Reach 84275 := rs (se 1 (by rfl) ⟨63206, by rfl⟩) R126413
theorem R84291 : Reach 84291 := rs (se 1 (by rfl) ⟨63218, by rfl⟩) R126437
theorem R84307 : Reach 84307 := rs (se 1 (by rfl) ⟨63230, by rfl⟩) R126461
theorem R84323 : Reach 84323 := rs (se 1 (by rfl) ⟨63242, by rfl⟩) R126485
theorem R84339 : Reach 84339 := rs (se 1 (by rfl) ⟨63254, by rfl⟩) R126509
theorem R84355 : Reach 84355 := rs (se 1 (by rfl) ⟨63266, by rfl⟩) R126533
theorem R84371 : Reach 84371 := rs (se 1 (by rfl) ⟨63278, by rfl⟩) R126557
theorem R84387 : Reach 84387 := rs (se 1 (by rfl) ⟨63290, by rfl⟩) R126581
theorem R84403 : Reach 84403 := rs (se 1 (by rfl) ⟨63302, by rfl⟩) R126605
theorem R84419 : Reach 84419 := rs (se 1 (by rfl) ⟨63314, by rfl⟩) R126629
theorem R84435 : Reach 84435 := rs (se 1 (by rfl) ⟨63326, by rfl⟩) R126653
theorem R84451 : Reach 84451 := rs (se 1 (by rfl) ⟨63338, by rfl⟩) R126677
theorem R281069 : Reach 281069 := rs (se 3 (by rfl) ⟨52700, by rfl⟩) R105401
theorem R84467 : Reach 84467 := rs (se 1 (by rfl) ⟨63350, by rfl⟩) R126701
theorem R84483 : Reach 84483 := rs (se 1 (by rfl) ⟨63362, by rfl⟩) R126725
theorem R84499 : Reach 84499 := rs (se 1 (by rfl) ⟨63374, by rfl⟩) R126749
theorem R281123 : Reach 281123 := rs (se 1 (by rfl) ⟨210842, by rfl⟩) R421685
theorem R84515 : Reach 84515 := rs (se 1 (by rfl) ⟨63386, by rfl⟩) R126773
theorem R84531 : Reach 84531 := rs (se 1 (by rfl) ⟨63398, by rfl⟩) R126797
theorem R84547 : Reach 84547 := rs (se 1 (by rfl) ⟨63410, by rfl⟩) R126821
theorem R84563 : Reach 84563 := rs (se 1 (by rfl) ⟨63422, by rfl⟩) R126845
theorem R84579 : Reach 84579 := rs (se 1 (by rfl) ⟨63434, by rfl⟩) R126869
theorem R84595 : Reach 84595 := rs (se 1 (by rfl) ⟨63446, by rfl⟩) R126893
theorem R84611 : Reach 84611 := rs (se 1 (by rfl) ⟨63458, by rfl⟩) R126917
theorem R84627 : Reach 84627 := rs (se 1 (by rfl) ⟨63470, by rfl⟩) R126941
theorem R477859 : Reach 477859 := rs (se 1 (by rfl) ⟨358394, by rfl⟩) R716789
theorem R84643 : Reach 84643 := rs (se 1 (by rfl) ⟨63482, by rfl⟩) R126965
theorem R84659 : Reach 84659 := rs (se 1 (by rfl) ⟨63494, by rfl⟩) R126989
theorem R84675 : Reach 84675 := rs (se 1 (by rfl) ⟨63506, by rfl⟩) R127013
theorem R84691 : Reach 84691 := rs (se 1 (by rfl) ⟨63518, by rfl⟩) R127037
theorem R84707 : Reach 84707 := rs (se 1 (by rfl) ⟨63530, by rfl⟩) R127061
theorem R84723 : Reach 84723 := rs (se 1 (by rfl) ⟨63542, by rfl⟩) R127085
theorem R84739 : Reach 84739 := rs (se 1 (by rfl) ⟨63554, by rfl⟩) R127109
theorem R84755 : Reach 84755 := rs (se 1 (by rfl) ⟨63566, by rfl⟩) R127133
theorem R84771 : Reach 84771 := rs (se 1 (by rfl) ⟨63578, by rfl⟩) R127157
theorem R281393 : Reach 281393 := rs (se 2 (by rfl) ⟨105522, by rfl⟩) R211045
theorem R84787 : Reach 84787 := rs (se 1 (by rfl) ⟨63590, by rfl⟩) R127181
theorem R84803 : Reach 84803 := rs (se 1 (by rfl) ⟨63602, by rfl⟩) R127205
theorem R84819 : Reach 84819 := rs (se 1 (by rfl) ⟨63614, by rfl⟩) R127229
theorem R84835 : Reach 84835 := rs (se 1 (by rfl) ⟨63626, by rfl⟩) R127253
theorem R84851 : Reach 84851 := rs (se 1 (by rfl) ⟨63638, by rfl⟩) R127277
theorem R84867 : Reach 84867 := rs (se 1 (by rfl) ⟨63650, by rfl⟩) R127301
theorem R84883 : Reach 84883 := rs (se 1 (by rfl) ⟨63662, by rfl⟩) R127325
theorem R84899 : Reach 84899 := rs (se 1 (by rfl) ⟨63674, by rfl⟩) R127349
theorem R84915 : Reach 84915 := rs (se 1 (by rfl) ⟨63686, by rfl⟩) R127373
theorem R84931 : Reach 84931 := rs (se 1 (by rfl) ⟨63698, by rfl⟩) R127397
theorem R216017 : Reach 216017 := rs (se 2 (by rfl) ⟨81006, by rfl⟩) R162013
theorem R84947 : Reach 84947 := rs (se 1 (by rfl) ⟨63710, by rfl⟩) R127421
theorem R84963 : Reach 84963 := rs (se 1 (by rfl) ⟨63722, by rfl⟩) R127445
theorem R510947 : Reach 510947 := rs (se 1 (by rfl) ⟨383210, by rfl⟩) R766421
theorem R84979 : Reach 84979 := rs (se 1 (by rfl) ⟨63734, by rfl⟩) R127469
theorem R84995 : Reach 84995 := rs (se 1 (by rfl) ⟨63746, by rfl⟩) R127493
theorem R216067 : Reach 216067 := rs (se 1 (by rfl) ⟨162050, by rfl⟩) R324101
theorem R85011 : Reach 85011 := rs (se 1 (by rfl) ⟨63758, by rfl⟩) R127517
theorem R85027 : Reach 85027 := rs (se 1 (by rfl) ⟨63770, by rfl⟩) R127541
theorem R85043 : Reach 85043 := rs (se 1 (by rfl) ⟨63782, by rfl⟩) R127565
theorem R85059 : Reach 85059 := rs (se 1 (by rfl) ⟨63794, by rfl⟩) R127589
theorem R85075 : Reach 85075 := rs (se 1 (by rfl) ⟨63806, by rfl⟩) R127613
theorem R85091 : Reach 85091 := rs (se 1 (by rfl) ⟨63818, by rfl⟩) R127637
theorem R85107 : Reach 85107 := rs (se 1 (by rfl) ⟨63830, by rfl⟩) R127661
theorem R85123 : Reach 85123 := rs (se 1 (by rfl) ⟨63842, by rfl⟩) R127685
theorem R150673 : Reach 150673 := rs (se 2 (by rfl) ⟨56502, by rfl⟩) R113005
theorem R85139 : Reach 85139 := rs (se 1 (by rfl) ⟨63854, by rfl⟩) R127709
theorem R216209 : Reach 216209 := rs (se 2 (by rfl) ⟨81078, by rfl⟩) R162157
theorem R85155 : Reach 85155 := rs (se 1 (by rfl) ⟨63866, by rfl⟩) R127733
theorem R478385 : Reach 478385 := rs (se 2 (by rfl) ⟨179394, by rfl⟩) R358789
theorem R85171 : Reach 85171 := rs (se 1 (by rfl) ⟨63878, by rfl⟩) R127757
theorem R85187 : Reach 85187 := rs (se 1 (by rfl) ⟨63890, by rfl⟩) R127781
theorem R85203 : Reach 85203 := rs (se 1 (by rfl) ⟨63902, by rfl⟩) R127805
theorem R85219 : Reach 85219 := rs (se 1 (by rfl) ⟨63914, by rfl⟩) R127829
theorem R85235 : Reach 85235 := rs (se 1 (by rfl) ⟨63926, by rfl⟩) R127853
theorem R85251 : Reach 85251 := rs (se 1 (by rfl) ⟨63938, by rfl⟩) R127877
theorem R85267 : Reach 85267 := rs (se 1 (by rfl) ⟨63950, by rfl⟩) R127901
theorem R85283 : Reach 85283 := rs (se 1 (by rfl) ⟨63962, by rfl⟩) R127925
theorem R85299 : Reach 85299 := rs (se 1 (by rfl) ⟨63974, by rfl⟩) R127949
theorem R85315 : Reach 85315 := rs (se 1 (by rfl) ⟨63986, by rfl⟩) R127973
theorem R281933 : Reach 281933 := rs (se 3 (by rfl) ⟨52862, by rfl⟩) R105725
theorem R85331 : Reach 85331 := rs (se 1 (by rfl) ⟨63998, by rfl⟩) R127997
theorem R85347 : Reach 85347 := rs (se 1 (by rfl) ⟨64010, by rfl⟩) R128021
theorem R85363 : Reach 85363 := rs (se 1 (by rfl) ⟨64022, by rfl⟩) R128045
theorem R281987 : Reach 281987 := rs (se 1 (by rfl) ⟨211490, by rfl⟩) R422981
theorem R85379 : Reach 85379 := rs (se 1 (by rfl) ⟨64034, by rfl⟩) R128069
theorem R85395 : Reach 85395 := rs (se 1 (by rfl) ⟨64046, by rfl⟩) R128093
theorem R85411 : Reach 85411 := rs (se 1 (by rfl) ⟨64058, by rfl⟩) R128117
theorem R85427 : Reach 85427 := rs (se 1 (by rfl) ⟨64070, by rfl⟩) R128141
theorem R85443 : Reach 85443 := rs (se 1 (by rfl) ⟨64082, by rfl⟩) R128165
theorem R249293 : Reach 249293 := rs (se 3 (by rfl) ⟨46742, by rfl⟩) R93485
theorem R85459 : Reach 85459 := rs (se 1 (by rfl) ⟨64094, by rfl⟩) R128189
theorem R85475 : Reach 85475 := rs (se 1 (by rfl) ⟨64106, by rfl⟩) R128213
theorem R85491 : Reach 85491 := rs (se 1 (by rfl) ⟨64118, by rfl⟩) R128237
theorem R85507 : Reach 85507 := rs (se 1 (by rfl) ⟨64130, by rfl⟩) R128261
theorem R183811 : Reach 183811 := rs (se 1 (by rfl) ⟨137858, by rfl⟩) R275717
theorem R85523 : Reach 85523 := rs (se 1 (by rfl) ⟨64142, by rfl⟩) R128285
theorem R85539 : Reach 85539 := rs (se 1 (by rfl) ⟨64154, by rfl⟩) R128309
theorem R85555 : Reach 85555 := rs (se 1 (by rfl) ⟨64166, by rfl⟩) R128333
theorem R85571 : Reach 85571 := rs (se 1 (by rfl) ⟨64178, by rfl⟩) R128357
theorem R85587 : Reach 85587 := rs (se 1 (by rfl) ⟨64190, by rfl⟩) R128381
theorem R85603 : Reach 85603 := rs (se 1 (by rfl) ⟨64202, by rfl⟩) R128405
theorem R85619 : Reach 85619 := rs (se 1 (by rfl) ⟨64214, by rfl⟩) R128429
theorem R85635 : Reach 85635 := rs (se 1 (by rfl) ⟨64226, by rfl⟩) R128453
theorem R282257 : Reach 282257 := rs (se 2 (by rfl) ⟨105846, by rfl⟩) R211693
theorem R118417 : Reach 118417 := rs (se 2 (by rfl) ⟨44406, by rfl⟩) R88813
theorem R85651 : Reach 85651 := rs (se 1 (by rfl) ⟨64238, by rfl⟩) R128477
theorem R85667 : Reach 85667 := rs (se 1 (by rfl) ⟨64250, by rfl⟩) R128501
theorem R85683 : Reach 85683 := rs (se 1 (by rfl) ⟨64262, by rfl⟩) R128525
theorem R85699 : Reach 85699 := rs (se 1 (by rfl) ⟨64274, by rfl⟩) R128549
theorem R85715 : Reach 85715 := rs (se 1 (by rfl) ⟨64286, by rfl⟩) R128573
theorem R1199843 : Reach 1199843 := rs (se 1 (by rfl) ⟨899882, by rfl⟩) R1799765
theorem R85731 : Reach 85731 := rs (se 1 (by rfl) ⟨64298, by rfl⟩) R128597
theorem R85747 : Reach 85747 := rs (se 1 (by rfl) ⟨64310, by rfl⟩) R128621
theorem R118531 : Reach 118531 := rs (se 1 (by rfl) ⟨88898, by rfl⟩) R177797
theorem R85763 : Reach 85763 := rs (se 1 (by rfl) ⟨64322, by rfl⟩) R128645
theorem R85779 : Reach 85779 := rs (se 1 (by rfl) ⟨64334, by rfl⟩) R128669
theorem R85795 : Reach 85795 := rs (se 1 (by rfl) ⟨64346, by rfl⟩) R128693
theorem R85811 : Reach 85811 := rs (se 1 (by rfl) ⟨64358, by rfl⟩) R128717
theorem R85827 : Reach 85827 := rs (se 1 (by rfl) ⟨64370, by rfl⟩) R128741
theorem R85843 : Reach 85843 := rs (se 1 (by rfl) ⟨64382, by rfl⟩) R128765
theorem R85859 : Reach 85859 := rs (se 1 (by rfl) ⟨64394, by rfl⟩) R128789
theorem R85875 : Reach 85875 := rs (se 1 (by rfl) ⟨64406, by rfl⟩) R128813
theorem R85891 : Reach 85891 := rs (se 1 (by rfl) ⟨64418, by rfl⟩) R128837
theorem R85907 : Reach 85907 := rs (se 1 (by rfl) ⟨64430, by rfl⟩) R128861
theorem R85923 : Reach 85923 := rs (se 1 (by rfl) ⟨64442, by rfl⟩) R128885
theorem R85939 : Reach 85939 := rs (se 1 (by rfl) ⟨64454, by rfl⟩) R128909
theorem R85955 : Reach 85955 := rs (se 1 (by rfl) ⟨64466, by rfl⟩) R128933
theorem R85971 : Reach 85971 := rs (se 1 (by rfl) ⟨64478, by rfl⟩) R128957
theorem R85987 : Reach 85987 := rs (se 1 (by rfl) ⟨64490, by rfl⟩) R128981
theorem R86003 : Reach 86003 := rs (se 1 (by rfl) ⟨64502, by rfl⟩) R129005
theorem R86019 : Reach 86019 := rs (se 1 (by rfl) ⟨64514, by rfl⟩) R129029
theorem R86035 : Reach 86035 := rs (se 1 (by rfl) ⟨64526, by rfl⟩) R129053
theorem R86051 : Reach 86051 := rs (se 1 (by rfl) ⟨64538, by rfl⟩) R129077
theorem R86067 : Reach 86067 := rs (se 1 (by rfl) ⟨64550, by rfl⟩) R129101
theorem R86083 : Reach 86083 := rs (se 1 (by rfl) ⟨64562, by rfl⟩) R129125
theorem R86099 : Reach 86099 := rs (se 1 (by rfl) ⟨64574, by rfl⟩) R129149
theorem R86115 : Reach 86115 := rs (se 1 (by rfl) ⟨64586, by rfl⟩) R129173
theorem R217201 : Reach 217201 := rs (se 2 (by rfl) ⟨81450, by rfl⟩) R162901
theorem R86131 : Reach 86131 := rs (se 1 (by rfl) ⟨64598, by rfl⟩) R129197
theorem R86147 : Reach 86147 := rs (se 1 (by rfl) ⟨64610, by rfl⟩) R129221
theorem R86163 : Reach 86163 := rs (se 1 (by rfl) ⟨64622, by rfl⟩) R129245
theorem R86179 : Reach 86179 := rs (se 1 (by rfl) ⟨64634, by rfl⟩) R129269
theorem R282797 : Reach 282797 := rs (se 3 (by rfl) ⟨53024, by rfl⟩) R106049
theorem R86195 : Reach 86195 := rs (se 1 (by rfl) ⟨64646, by rfl⟩) R129293
theorem R86211 : Reach 86211 := rs (se 1 (by rfl) ⟨64658, by rfl⟩) R129317
theorem R86227 : Reach 86227 := rs (se 1 (by rfl) ⟨64670, by rfl⟩) R129341
theorem R282851 : Reach 282851 := rs (se 1 (by rfl) ⟨212138, by rfl⟩) R424277
theorem R86243 : Reach 86243 := rs (se 1 (by rfl) ⟨64682, by rfl⟩) R129365
theorem R86259 : Reach 86259 := rs (se 1 (by rfl) ⟨64694, by rfl⟩) R129389
theorem R86275 : Reach 86275 := rs (se 1 (by rfl) ⟨64706, by rfl⟩) R129413
theorem R86291 : Reach 86291 := rs (se 1 (by rfl) ⟨64718, by rfl⟩) R129437
theorem R86307 : Reach 86307 := rs (se 1 (by rfl) ⟨64730, by rfl⟩) R129461
theorem R86323 : Reach 86323 := rs (se 1 (by rfl) ⟨64742, by rfl⟩) R129485
theorem R86339 : Reach 86339 := rs (se 1 (by rfl) ⟨64754, by rfl⟩) R129509
theorem R86355 : Reach 86355 := rs (se 1 (by rfl) ⟨64766, by rfl⟩) R129533
theorem R86371 : Reach 86371 := rs (se 1 (by rfl) ⟨64778, by rfl⟩) R129557
theorem R86387 : Reach 86387 := rs (se 1 (by rfl) ⟨64790, by rfl⟩) R129581
theorem R217475 : Reach 217475 := rs (se 1 (by rfl) ⟨163106, by rfl⟩) R326213
theorem R86403 : Reach 86403 := rs (se 1 (by rfl) ⟨64802, by rfl⟩) R129605
theorem R86419 : Reach 86419 := rs (se 1 (by rfl) ⟨64814, by rfl⟩) R129629
theorem R86435 : Reach 86435 := rs (se 1 (by rfl) ⟨64826, by rfl⟩) R129653
theorem R86451 : Reach 86451 := rs (se 1 (by rfl) ⟨64838, by rfl⟩) R129677
theorem R86467 : Reach 86467 := rs (se 1 (by rfl) ⟨64850, by rfl⟩) R129701
theorem R1036741 : Reach 1036741 := rs (se 4 (by rfl) ⟨97194, by rfl⟩) R194389
theorem R86483 : Reach 86483 := rs (se 1 (by rfl) ⟨64862, by rfl⟩) R129725
theorem R86499 : Reach 86499 := rs (se 1 (by rfl) ⟨64874, by rfl⟩) R129749
theorem R283121 : Reach 283121 := rs (se 2 (by rfl) ⟨106170, by rfl⟩) R212341
theorem R86515 : Reach 86515 := rs (se 1 (by rfl) ⟨64886, by rfl⟩) R129773
theorem R217603 : Reach 217603 := rs (se 1 (by rfl) ⟨163202, by rfl⟩) R326405
theorem R86531 : Reach 86531 := rs (se 1 (by rfl) ⟨64898, by rfl⟩) R129797
theorem R86547 : Reach 86547 := rs (se 1 (by rfl) ⟨64910, by rfl⟩) R129821
theorem R86563 : Reach 86563 := rs (se 1 (by rfl) ⟨64922, by rfl⟩) R129845
theorem R86579 : Reach 86579 := rs (se 1 (by rfl) ⟨64934, by rfl⟩) R129869
theorem R217667 : Reach 217667 := rs (se 1 (by rfl) ⟨163250, by rfl⟩) R326501
theorem R86595 : Reach 86595 := rs (se 1 (by rfl) ⟨64946, by rfl⟩) R129893
theorem R86611 : Reach 86611 := rs (se 1 (by rfl) ⟨64958, by rfl⟩) R129917
theorem R479843 : Reach 479843 := rs (se 1 (by rfl) ⟨359882, by rfl⟩) R719765
theorem R86627 : Reach 86627 := rs (se 1 (by rfl) ⟨64970, by rfl⟩) R129941
theorem R348785 : Reach 348785 := rs (se 2 (by rfl) ⟨130794, by rfl⟩) R261589
theorem R86643 : Reach 86643 := rs (se 1 (by rfl) ⟨64982, by rfl⟩) R129965
theorem R86659 : Reach 86659 := rs (se 1 (by rfl) ⟨64994, by rfl⟩) R129989
theorem R86675 : Reach 86675 := rs (se 1 (by rfl) ⟨65006, by rfl⟩) R130013
theorem R86691 : Reach 86691 := rs (se 1 (by rfl) ⟨65018, by rfl⟩) R130037
theorem R86707 : Reach 86707 := rs (se 1 (by rfl) ⟨65030, by rfl⟩) R130061
theorem R86723 : Reach 86723 := rs (se 1 (by rfl) ⟨65042, by rfl⟩) R130085
theorem R185041 : Reach 185041 := rs (se 2 (by rfl) ⟨69390, by rfl⟩) R138781
theorem R86739 : Reach 86739 := rs (se 1 (by rfl) ⟨65054, by rfl⟩) R130109
theorem R86755 : Reach 86755 := rs (se 1 (by rfl) ⟨65066, by rfl⟩) R130133
theorem R86771 : Reach 86771 := rs (se 1 (by rfl) ⟨65078, by rfl⟩) R130157
theorem R86787 : Reach 86787 := rs (se 1 (by rfl) ⟨65090, by rfl⟩) R130181
theorem R86803 : Reach 86803 := rs (se 1 (by rfl) ⟨65102, by rfl⟩) R130205
theorem R86819 : Reach 86819 := rs (se 1 (by rfl) ⟨65114, by rfl⟩) R130229
theorem R86835 : Reach 86835 := rs (se 1 (by rfl) ⟨65126, by rfl⟩) R130253
theorem R86851 : Reach 86851 := rs (se 1 (by rfl) ⟨65138, by rfl⟩) R130277
theorem R86867 : Reach 86867 := rs (se 1 (by rfl) ⟨65150, by rfl⟩) R130301
theorem R86883 : Reach 86883 := rs (se 1 (by rfl) ⟨65162, by rfl⟩) R130325
theorem R86899 : Reach 86899 := rs (se 1 (by rfl) ⟨65174, by rfl⟩) R130349
theorem R86915 : Reach 86915 := rs (se 1 (by rfl) ⟨65186, by rfl⟩) R130373
theorem R86931 : Reach 86931 := rs (se 1 (by rfl) ⟨65198, by rfl⟩) R130397
theorem R86947 : Reach 86947 := rs (se 1 (by rfl) ⟨65210, by rfl⟩) R130421
theorem R86963 : Reach 86963 := rs (se 1 (by rfl) ⟨65222, by rfl⟩) R130445
theorem R86979 : Reach 86979 := rs (se 1 (by rfl) ⟨65234, by rfl⟩) R130469
theorem R86995 : Reach 86995 := rs (se 1 (by rfl) ⟨65246, by rfl⟩) R130493
theorem R87011 : Reach 87011 := rs (se 1 (by rfl) ⟨65258, by rfl⟩) R130517
theorem R87027 : Reach 87027 := rs (se 1 (by rfl) ⟨65270, by rfl⟩) R130541
theorem R87043 : Reach 87043 := rs (se 1 (by rfl) ⟨65282, by rfl⟩) R130565
theorem R283661 : Reach 283661 := rs (se 3 (by rfl) ⟨53186, by rfl⟩) R106373
theorem R87059 : Reach 87059 := rs (se 1 (by rfl) ⟨65294, by rfl⟩) R130589
theorem R87075 : Reach 87075 := rs (se 1 (by rfl) ⟨65306, by rfl⟩) R130613
theorem R87091 : Reach 87091 := rs (se 1 (by rfl) ⟨65318, by rfl⟩) R130637
theorem R283715 : Reach 283715 := rs (se 1 (by rfl) ⟨212786, by rfl⟩) R425573
theorem R119875 : Reach 119875 := rs (se 1 (by rfl) ⟨89906, by rfl⟩) R179813
theorem R87107 : Reach 87107 := rs (se 1 (by rfl) ⟨65330, by rfl⟩) R130661
theorem R316493 : Reach 316493 := rs (se 3 (by rfl) ⟨59342, by rfl⟩) R118685
theorem R87123 : Reach 87123 := rs (se 1 (by rfl) ⟨65342, by rfl⟩) R130685
theorem R283985 : Reach 283985 := rs (se 2 (by rfl) ⟨106494, by rfl⟩) R212989
theorem R185827 : Reach 185827 := rs (se 1 (by rfl) ⟨139370, by rfl⟩) R278741
theorem R218609 : Reach 218609 := rs (se 2 (by rfl) ⟨81978, by rfl⟩) R163957
theorem R218659 : Reach 218659 := rs (se 1 (by rfl) ⟨163994, by rfl⟩) R327989
theorem R218801 : Reach 218801 := rs (se 2 (by rfl) ⟨82050, by rfl⟩) R164101
theorem R972485 : Reach 972485 := rs (se 4 (by rfl) ⟨91170, by rfl⟩) R182341
theorem R153361 : Reach 153361 := rs (se 2 (by rfl) ⟨57510, by rfl⟩) R115021
theorem R284525 : Reach 284525 := rs (se 3 (by rfl) ⟨53348, by rfl⟩) R106697
theorem R317297 : Reach 317297 := rs (se 2 (by rfl) ⟨118986, by rfl⟩) R237973
theorem R284579 : Reach 284579 := rs (se 1 (by rfl) ⟨213434, by rfl⟩) R426869
theorem R415651 : Reach 415651 := rs (se 1 (by rfl) ⟨311738, by rfl⟩) R623477
theorem R251981 : Reach 251981 := rs (se 3 (by rfl) ⟨47246, by rfl⟩) R94493
theorem R284849 : Reach 284849 := rs (se 2 (by rfl) ⟨106818, by rfl⟩) R213637
theorem R121009 : Reach 121009 := rs (se 2 (by rfl) ⟨45378, by rfl⟩) R90757
theorem R547013 : Reach 547013 := rs (se 4 (by rfl) ⟨51282, by rfl⟩) R102565
theorem R121105 : Reach 121105 := rs (se 2 (by rfl) ⟨45414, by rfl⟩) R90829
theorem R481733 : Reach 481733 := rs (se 4 (by rfl) ⟨45162, by rfl⟩) R90325
theorem R317965 : Reach 317965 := rs (se 3 (by rfl) ⟨59618, by rfl⟩) R119237
theorem R219793 : Reach 219793 := rs (se 2 (by rfl) ⟨82422, by rfl⟩) R164845
theorem R285389 : Reach 285389 := rs (se 3 (by rfl) ⟨53510, by rfl⟩) R107021
theorem R121601 : Reach 121601 := rs (se 2 (by rfl) ⟨45600, by rfl⟩) R91201
theorem R285443 : Reach 285443 := rs (se 1 (by rfl) ⟨214082, by rfl⟩) R428165
theorem R187217 : Reach 187217 := rs (se 2 (by rfl) ⟨70206, by rfl⟩) R140413
theorem R187235 : Reach 187235 := rs (se 1 (by rfl) ⟨140426, by rfl⟩) R280853
theorem R220067 : Reach 220067 := rs (se 1 (by rfl) ⟨165050, by rfl⟩) R330101
theorem R711665 : Reach 711665 := rs (se 2 (by rfl) ⟨266874, by rfl⟩) R533749
theorem R285713 : Reach 285713 := rs (se 2 (by rfl) ⟨107142, by rfl⟩) R214285
theorem R220259 : Reach 220259 := rs (se 1 (by rfl) ⟨165194, by rfl⟩) R330389
theorem R187505 : Reach 187505 := rs (se 2 (by rfl) ⟨70314, by rfl⟩) R140629
theorem R187523 : Reach 187523 := rs (se 1 (by rfl) ⟨140642, by rfl⟩) R281285
theorem R89219 : Reach 89219 := rs (se 1 (by rfl) ⟨66914, by rfl⟩) R133829
theorem R318755 : Reach 318755 := rs (se 1 (by rfl) ⟨239066, by rfl⟩) R478133
theorem R187793 : Reach 187793 := rs (se 2 (by rfl) ⟨70422, by rfl⟩) R140845
theorem R187811 : Reach 187811 := rs (se 1 (by rfl) ⟨140858, by rfl⟩) R281717
theorem R155171 : Reach 155171 := rs (se 1 (by rfl) ⟨116378, by rfl⟩) R232757
theorem R286253 : Reach 286253 := rs (se 3 (by rfl) ⟨53672, by rfl⟩) R107345
theorem R286307 : Reach 286307 := rs (se 1 (by rfl) ⟨214730, by rfl⟩) R429461
theorem R122467 : Reach 122467 := rs (se 1 (by rfl) ⟨91850, by rfl⟩) R183701
theorem R188081 : Reach 188081 := rs (se 2 (by rfl) ⟨70530, by rfl⟩) R141061
theorem R188099 : Reach 188099 := rs (se 1 (by rfl) ⟨141074, by rfl⟩) R282149
theorem R122563 : Reach 122563 := rs (se 1 (by rfl) ⟨91922, by rfl⟩) R183845
theorem R286577 : Reach 286577 := rs (se 2 (by rfl) ⟨107466, by rfl⟩) R214933
theorem R417649 : Reach 417649 := rs (se 2 (by rfl) ⟨156618, by rfl⟩) R313237
theorem R450481 : Reach 450481 := rs (se 2 (by rfl) ⟨168930, by rfl⟩) R337861
theorem R319409 : Reach 319409 := rs (se 2 (by rfl) ⟨119778, by rfl⟩) R239557
theorem R188369 : Reach 188369 := rs (se 2 (by rfl) ⟨70638, by rfl⟩) R141277
theorem R188387 : Reach 188387 := rs (se 1 (by rfl) ⟨141290, by rfl⟩) R282581
theorem R548869 : Reach 548869 := rs (se 4 (by rfl) ⟨51456, by rfl⟩) R102913
theorem R90163 : Reach 90163 := rs (se 1 (by rfl) ⟨67622, by rfl⟩) R135245
theorem R1532045 : Reach 1532045 := rs (se 3 (by rfl) ⟨287258, by rfl⟩) R574517
theorem R123059 : Reach 123059 := rs (se 1 (by rfl) ⟨92294, by rfl⟩) R184589
theorem R188657 : Reach 188657 := rs (se 2 (by rfl) ⟨70746, by rfl⟩) R141493
theorem R188675 : Reach 188675 := rs (se 1 (by rfl) ⟨141506, by rfl⟩) R283013
theorem R287117 : Reach 287117 := rs (se 3 (by rfl) ⟨53834, by rfl⟩) R107669
theorem R90563 : Reach 90563 := rs (se 1 (by rfl) ⟨67922, by rfl⟩) R135845
theorem R287171 : Reach 287171 := rs (se 1 (by rfl) ⟨215378, by rfl⟩) R430757
theorem R188945 : Reach 188945 := rs (se 2 (by rfl) ⟨70854, by rfl⟩) R141709
theorem R188963 : Reach 188963 := rs (se 1 (by rfl) ⟨141722, by rfl⟩) R283445
theorem R811619 : Reach 811619 := rs (se 1 (by rfl) ⟨608714, by rfl⟩) R1217429
theorem R713357 : Reach 713357 := rs (se 3 (by rfl) ⟨133754, by rfl⟩) R267509
theorem R287441 : Reach 287441 := rs (se 2 (by rfl) ⟨107790, by rfl⟩) R215581
theorem R189233 : Reach 189233 := rs (se 2 (by rfl) ⟨70962, by rfl⟩) R141925
theorem R123697 : Reach 123697 := rs (se 2 (by rfl) ⟨46386, by rfl⟩) R92773
theorem R189251 : Reach 189251 := rs (se 1 (by rfl) ⟨141938, by rfl⟩) R283877
theorem R3761093 : Reach 3761093 := rs (se 4 (by rfl) ⟨352602, by rfl⟩) R705205
theorem R189521 : Reach 189521 := rs (se 2 (by rfl) ⟨71070, by rfl⟩) R142141
theorem R189539 : Reach 189539 := rs (se 1 (by rfl) ⟨142154, by rfl⟩) R284309
theorem R124033 : Reach 124033 := rs (se 2 (by rfl) ⟨46512, by rfl⟩) R93025
theorem R287981 : Reach 287981 := rs (se 3 (by rfl) ⟨53996, by rfl⟩) R107993
theorem R288035 : Reach 288035 := rs (se 1 (by rfl) ⟨216026, by rfl⟩) R432053
theorem R91427 : Reach 91427 := rs (se 1 (by rfl) ⟨68570, by rfl⟩) R137141
theorem R320867 : Reach 320867 := rs (se 1 (by rfl) ⟨240650, by rfl⟩) R481301
theorem R189809 : Reach 189809 := rs (se 2 (by rfl) ⟨71178, by rfl⟩) R142357
theorem R320881 : Reach 320881 := rs (se 2 (by rfl) ⟨120330, by rfl⟩) R240661
theorem R189827 : Reach 189827 := rs (se 1 (by rfl) ⟨142370, by rfl⟩) R284741
theorem R288305 : Reach 288305 := rs (se 2 (by rfl) ⟨108114, by rfl⟩) R216229
theorem R190097 : Reach 190097 := rs (se 2 (by rfl) ⟨71286, by rfl⟩) R142573
theorem R190115 : Reach 190115 := rs (se 1 (by rfl) ⟨142586, by rfl⟩) R285173
theorem R255683 : Reach 255683 := rs (se 1 (by rfl) ⟨191762, by rfl⟩) R383525
theorem R124721 : Reach 124721 := rs (se 2 (by rfl) ⟨46770, by rfl⟩) R93541
theorem R124739 : Reach 124739 := rs (se 1 (by rfl) ⟨93554, by rfl⟩) R187109
theorem R452429 : Reach 452429 := rs (se 3 (by rfl) ⟨84830, by rfl⟩) R169661
theorem R124769 : Reach 124769 := rs (se 2 (by rfl) ⟨46788, by rfl⟩) R93577
theorem R124787 : Reach 124787 := rs (se 1 (by rfl) ⟨93590, by rfl⟩) R187181
theorem R124817 : Reach 124817 := rs (se 2 (by rfl) ⟨46806, by rfl⟩) R93613
theorem R124835 : Reach 124835 := rs (se 1 (by rfl) ⟨93626, by rfl⟩) R187253
theorem R190385 : Reach 190385 := rs (se 2 (by rfl) ⟨71394, by rfl⟩) R142789
theorem R124865 : Reach 124865 := rs (se 2 (by rfl) ⟨46824, by rfl⟩) R93649
theorem R190403 : Reach 190403 := rs (se 1 (by rfl) ⟨142802, by rfl⟩) R285605
theorem R124883 : Reach 124883 := rs (se 1 (by rfl) ⟨93662, by rfl⟩) R187325
theorem R124913 : Reach 124913 := rs (se 2 (by rfl) ⟨46842, by rfl⟩) R93685
theorem R124931 : Reach 124931 := rs (se 1 (by rfl) ⟨93698, by rfl⟩) R187397
theorem R92179 : Reach 92179 := rs (se 1 (by rfl) ⟨69134, by rfl⟩) R138269
theorem R124961 : Reach 124961 := rs (se 2 (by rfl) ⟨46860, by rfl⟩) R93721
theorem R124979 : Reach 124979 := rs (se 1 (by rfl) ⟨93734, by rfl⟩) R187469
theorem R288845 : Reach 288845 := rs (se 3 (by rfl) ⟨54158, by rfl⟩) R108317
theorem R125009 : Reach 125009 := rs (se 2 (by rfl) ⟨46878, by rfl⟩) R93757
theorem R125027 : Reach 125027 := rs (se 1 (by rfl) ⟨93770, by rfl⟩) R187541
theorem R190577 : Reach 190577 := rs (se 2 (by rfl) ⟨71466, by rfl⟩) R142933
theorem R125057 : Reach 125057 := rs (se 2 (by rfl) ⟨46896, by rfl⟩) R93793
theorem R288899 : Reach 288899 := rs (se 1 (by rfl) ⟨216674, by rfl⟩) R433349
theorem R125075 : Reach 125075 := rs (se 1 (by rfl) ⟨93806, by rfl⟩) R187613
theorem R157859 : Reach 157859 := rs (se 1 (by rfl) ⟨118394, by rfl⟩) R236789
theorem R125105 : Reach 125105 := rs (se 2 (by rfl) ⟨46914, by rfl⟩) R93829
theorem R125123 : Reach 125123 := rs (se 1 (by rfl) ⟨93842, by rfl⟩) R187685
theorem R190673 : Reach 190673 := rs (se 2 (by rfl) ⟨71502, by rfl⟩) R143005
theorem R125153 : Reach 125153 := rs (se 2 (by rfl) ⟨46932, by rfl⟩) R93865
theorem R190691 : Reach 190691 := rs (se 1 (by rfl) ⟨143018, by rfl⟩) R286037
theorem R125171 : Reach 125171 := rs (se 1 (by rfl) ⟨93878, by rfl⟩) R187757
theorem R125201 : Reach 125201 := rs (se 2 (by rfl) ⟨46950, by rfl⟩) R93901
theorem R92435 : Reach 92435 := rs (se 1 (by rfl) ⟨69326, by rfl⟩) R138653
theorem R125219 : Reach 125219 := rs (se 1 (by rfl) ⟨93914, by rfl⟩) R187829
theorem R125249 : Reach 125249 := rs (se 2 (by rfl) ⟨46968, by rfl⟩) R93937
theorem R125267 : Reach 125267 := rs (se 1 (by rfl) ⟨93950, by rfl⟩) R187901
theorem R125297 : Reach 125297 := rs (se 2 (by rfl) ⟨46986, by rfl⟩) R93973
theorem R125315 : Reach 125315 := rs (se 1 (by rfl) ⟨93986, by rfl⟩) R187973
theorem R289169 : Reach 289169 := rs (se 2 (by rfl) ⟨108438, by rfl⟩) R216877
theorem R125345 : Reach 125345 := rs (se 2 (by rfl) ⟨47004, by rfl⟩) R94009
theorem R125363 : Reach 125363 := rs (se 1 (by rfl) ⟨94022, by rfl⟩) R188045
theorem R125393 : Reach 125393 := rs (se 2 (by rfl) ⟨47022, by rfl⟩) R94045
theorem R125411 : Reach 125411 := rs (se 1 (by rfl) ⟨94058, by rfl⟩) R188117
theorem R190961 : Reach 190961 := rs (se 2 (by rfl) ⟨71610, by rfl⟩) R143221
theorem R125441 : Reach 125441 := rs (se 2 (by rfl) ⟨47040, by rfl⟩) R94081
theorem R190979 : Reach 190979 := rs (se 1 (by rfl) ⟨143234, by rfl⟩) R286469
theorem R125459 : Reach 125459 := rs (se 1 (by rfl) ⟨94094, by rfl⟩) R188189
theorem R125489 : Reach 125489 := rs (se 2 (by rfl) ⟨47058, by rfl⟩) R94117
theorem R125507 : Reach 125507 := rs (se 1 (by rfl) ⟨94130, by rfl⟩) R188261
theorem R125537 : Reach 125537 := rs (se 2 (by rfl) ⟨47076, by rfl⟩) R94153
theorem R387683 : Reach 387683 := rs (se 1 (by rfl) ⟨290762, by rfl⟩) R581525
theorem R191089 : Reach 191089 := rs (se 2 (by rfl) ⟨71658, by rfl⟩) R143317
theorem R125555 : Reach 125555 := rs (se 1 (by rfl) ⟨94166, by rfl⟩) R188333
theorem R125585 : Reach 125585 := rs (se 2 (by rfl) ⟨47094, by rfl⟩) R94189
theorem R125603 : Reach 125603 := rs (se 1 (by rfl) ⟨94202, by rfl⟩) R188405
theorem R125633 : Reach 125633 := rs (se 2 (by rfl) ⟨47112, by rfl⟩) R94225
theorem R125651 : Reach 125651 := rs (se 1 (by rfl) ⟨94238, by rfl⟩) R188477
theorem R125681 : Reach 125681 := rs (se 2 (by rfl) ⟨47130, by rfl⟩) R94261
theorem R125699 : Reach 125699 := rs (se 1 (by rfl) ⟨94274, by rfl⟩) R188549
theorem R191249 : Reach 191249 := rs (se 2 (by rfl) ⟨71718, by rfl⟩) R143437
theorem R125729 : Reach 125729 := rs (se 2 (by rfl) ⟨47148, by rfl⟩) R94297
theorem R191267 : Reach 191267 := rs (se 1 (by rfl) ⟨143450, by rfl⟩) R286901
theorem R322339 : Reach 322339 := rs (se 1 (by rfl) ⟨241754, by rfl⟩) R483509
theorem R125747 : Reach 125747 := rs (se 1 (by rfl) ⟨94310, by rfl⟩) R188621
theorem R125777 : Reach 125777 := rs (se 2 (by rfl) ⟨47166, by rfl⟩) R94333
theorem R125795 : Reach 125795 := rs (se 1 (by rfl) ⟨94346, by rfl⟩) R188693
theorem R125825 : Reach 125825 := rs (se 2 (by rfl) ⟨47184, by rfl⟩) R94369
theorem R125843 : Reach 125843 := rs (se 1 (by rfl) ⟨94382, by rfl⟩) R188765
theorem R551843 : Reach 551843 := rs (se 1 (by rfl) ⟨413882, by rfl⟩) R827765
theorem R289709 : Reach 289709 := rs (se 3 (by rfl) ⟨54320, by rfl⟩) R108641
theorem R125873 : Reach 125873 := rs (se 2 (by rfl) ⟨47202, by rfl⟩) R94405
theorem R125891 : Reach 125891 := rs (se 1 (by rfl) ⟨94418, by rfl⟩) R188837
theorem R125921 : Reach 125921 := rs (se 2 (by rfl) ⟨47220, by rfl⟩) R94441
theorem R289763 : Reach 289763 := rs (se 1 (by rfl) ⟨217322, by rfl⟩) R434645
theorem R125939 : Reach 125939 := rs (se 1 (by rfl) ⟨94454, by rfl⟩) R188909
theorem R125969 : Reach 125969 := rs (se 2 (by rfl) ⟨47238, by rfl⟩) R94477
theorem R158755 : Reach 158755 := rs (se 1 (by rfl) ⟨119066, by rfl⟩) R238133
theorem R125987 : Reach 125987 := rs (se 1 (by rfl) ⟨94490, by rfl⟩) R188981
theorem R191537 : Reach 191537 := rs (se 2 (by rfl) ⟨71826, by rfl⟩) R143653
theorem R126017 : Reach 126017 := rs (se 2 (by rfl) ⟨47256, by rfl⟩) R94513
theorem R191555 : Reach 191555 := rs (se 1 (by rfl) ⟨143666, by rfl⟩) R287333
theorem R126035 : Reach 126035 := rs (se 1 (by rfl) ⟨94526, by rfl⟩) R189053
theorem R126065 : Reach 126065 := rs (se 2 (by rfl) ⟨47274, by rfl⟩) R94549
theorem R126083 : Reach 126083 := rs (se 1 (by rfl) ⟨94562, by rfl⟩) R189125
theorem R126113 : Reach 126113 := rs (se 2 (by rfl) ⟨47292, by rfl⟩) R94585
theorem R126131 : Reach 126131 := rs (se 1 (by rfl) ⟨94598, by rfl⟩) R189197
theorem R158915 : Reach 158915 := rs (se 1 (by rfl) ⟨119186, by rfl⟩) R238373
theorem R126161 : Reach 126161 := rs (se 2 (by rfl) ⟨47310, by rfl⟩) R94621
theorem R126179 : Reach 126179 := rs (se 1 (by rfl) ⟨94634, by rfl⟩) R189269
theorem R290033 : Reach 290033 := rs (se 2 (by rfl) ⟨108762, by rfl⟩) R217525
theorem R126209 : Reach 126209 := rs (se 2 (by rfl) ⟨47328, by rfl⟩) R94657
theorem R126227 : Reach 126227 := rs (se 1 (by rfl) ⟨94670, by rfl⟩) R189341
theorem R126257 : Reach 126257 := rs (se 2 (by rfl) ⟨47346, by rfl⟩) R94693
theorem R126275 : Reach 126275 := rs (se 1 (by rfl) ⟨94706, by rfl⟩) R189413
theorem R355661 : Reach 355661 := rs (se 3 (by rfl) ⟨66686, by rfl⟩) R133373
theorem R191825 : Reach 191825 := rs (se 2 (by rfl) ⟨71934, by rfl⟩) R143869
theorem R93523 : Reach 93523 := rs (se 1 (by rfl) ⟨70142, by rfl⟩) R140285
theorem R126305 : Reach 126305 := rs (se 2 (by rfl) ⟨47364, by rfl⟩) R94729
theorem R191843 : Reach 191843 := rs (se 1 (by rfl) ⟨143882, by rfl⟩) R287765
theorem R617827 : Reach 617827 := rs (se 1 (by rfl) ⟨463370, by rfl⟩) R926741
theorem R355697 : Reach 355697 := rs (se 2 (by rfl) ⟨133386, by rfl⟩) R266773
theorem R126323 : Reach 126323 := rs (se 1 (by rfl) ⟨94742, by rfl⟩) R189485
theorem R978317 : Reach 978317 := rs (se 3 (by rfl) ⟨183434, by rfl⟩) R366869
theorem R126353 : Reach 126353 := rs (se 2 (by rfl) ⟨47382, by rfl⟩) R94765
theorem R126371 : Reach 126371 := rs (se 1 (by rfl) ⟨94778, by rfl⟩) R189557
theorem R126401 : Reach 126401 := rs (se 2 (by rfl) ⟨47400, by rfl⟩) R94801
theorem R126419 : Reach 126419 := rs (se 1 (by rfl) ⟨94814, by rfl⟩) R189629
theorem R93667 : Reach 93667 := rs (se 1 (by rfl) ⟨70250, by rfl⟩) R140501
theorem R421361 : Reach 421361 := rs (se 2 (by rfl) ⟨158010, by rfl⟩) R316021
theorem R126449 : Reach 126449 := rs (se 2 (by rfl) ⟨47418, by rfl⟩) R94837
theorem R126467 : Reach 126467 := rs (se 1 (by rfl) ⟨94850, by rfl⟩) R189701
theorem R126497 : Reach 126497 := rs (se 2 (by rfl) ⟨47436, by rfl⟩) R94873
theorem R585251 : Reach 585251 := rs (se 1 (by rfl) ⟨438938, by rfl⟩) R877877
theorem R126515 : Reach 126515 := rs (se 1 (by rfl) ⟨94886, by rfl⟩) R189773
theorem R126545 : Reach 126545 := rs (se 2 (by rfl) ⟨47454, by rfl⟩) R94909
theorem R126563 : Reach 126563 := rs (se 1 (by rfl) ⟨94922, by rfl⟩) R189845
theorem R192113 : Reach 192113 := rs (se 2 (by rfl) ⟨72042, by rfl⟩) R144085
theorem R93811 : Reach 93811 := rs (se 1 (by rfl) ⟨70358, by rfl⟩) R140717
theorem R126593 : Reach 126593 := rs (se 2 (by rfl) ⟨47472, by rfl⟩) R94945
theorem R192131 : Reach 192131 := rs (se 1 (by rfl) ⟨144098, by rfl⟩) R288197
theorem R126611 : Reach 126611 := rs (se 1 (by rfl) ⟨94958, by rfl⟩) R189917
theorem R126641 : Reach 126641 := rs (se 2 (by rfl) ⟨47490, by rfl⟩) R94981
theorem R126659 : Reach 126659 := rs (se 1 (by rfl) ⟨94994, by rfl⟩) R189989
theorem R126689 : Reach 126689 := rs (se 2 (by rfl) ⟨47508, by rfl⟩) R95017
theorem R126707 : Reach 126707 := rs (se 1 (by rfl) ⟨95030, by rfl⟩) R190061
theorem R93955 : Reach 93955 := rs (se 1 (by rfl) ⟨70466, by rfl⟩) R140933
theorem R290573 : Reach 290573 := rs (se 3 (by rfl) ⟨54482, by rfl⟩) R108965
theorem R126737 : Reach 126737 := rs (se 2 (by rfl) ⟨47526, by rfl⟩) R95053
theorem R126755 : Reach 126755 := rs (se 1 (by rfl) ⟨95066, by rfl⟩) R190133
theorem R126785 : Reach 126785 := rs (se 2 (by rfl) ⟨47544, by rfl⟩) R95089
theorem R290627 : Reach 290627 := rs (se 1 (by rfl) ⟨217970, by rfl⟩) R435941
theorem R126803 : Reach 126803 := rs (se 1 (by rfl) ⟨95102, by rfl⟩) R190205
theorem R126833 : Reach 126833 := rs (se 2 (by rfl) ⟨47562, by rfl⟩) R95125
theorem R126851 : Reach 126851 := rs (se 1 (by rfl) ⟨95138, by rfl⟩) R190277
theorem R192401 : Reach 192401 := rs (se 2 (by rfl) ⟨72150, by rfl⟩) R144301
theorem R94099 : Reach 94099 := rs (se 1 (by rfl) ⟨70574, by rfl⟩) R141149
theorem R126881 : Reach 126881 := rs (se 2 (by rfl) ⟨47580, by rfl⟩) R95161
theorem R192419 : Reach 192419 := rs (se 1 (by rfl) ⟨144314, by rfl⟩) R288629
theorem R126899 : Reach 126899 := rs (se 1 (by rfl) ⟨95174, by rfl⟩) R190349
theorem R126929 : Reach 126929 := rs (se 2 (by rfl) ⟨47598, by rfl⟩) R95197
theorem R126947 : Reach 126947 := rs (se 1 (by rfl) ⟨95210, by rfl⟩) R190421
theorem R126977 : Reach 126977 := rs (se 2 (by rfl) ⟨47616, by rfl⟩) R95233
theorem R126995 : Reach 126995 := rs (se 1 (by rfl) ⟨95246, by rfl⟩) R190493
theorem R94243 : Reach 94243 := rs (se 1 (by rfl) ⟨70682, by rfl⟩) R141365
theorem R127025 : Reach 127025 := rs (se 2 (by rfl) ⟨47634, by rfl⟩) R95269
theorem R127043 : Reach 127043 := rs (se 1 (by rfl) ⟨95282, by rfl⟩) R190565
theorem R290897 : Reach 290897 := rs (se 2 (by rfl) ⟨109086, by rfl⟩) R218173
theorem R127073 : Reach 127073 := rs (se 2 (by rfl) ⟨47652, by rfl⟩) R95305
theorem R127091 : Reach 127091 := rs (se 1 (by rfl) ⟨95318, by rfl⟩) R190637
theorem R487565 : Reach 487565 := rs (se 3 (by rfl) ⟨91418, by rfl⟩) R182837
theorem R127121 : Reach 127121 := rs (se 2 (by rfl) ⟨47670, by rfl⟩) R95341
theorem R127139 : Reach 127139 := rs (se 1 (by rfl) ⟨95354, by rfl⟩) R190709
theorem R192689 : Reach 192689 := rs (se 2 (by rfl) ⟨72258, by rfl⟩) R144517
theorem R94387 : Reach 94387 := rs (se 1 (by rfl) ⟨70790, by rfl⟩) R141581
theorem R127169 : Reach 127169 := rs (se 2 (by rfl) ⟨47688, by rfl⟩) R95377
theorem R192707 : Reach 192707 := rs (se 1 (by rfl) ⟨144530, by rfl⟩) R289061
theorem R127187 : Reach 127187 := rs (se 1 (by rfl) ⟨95390, by rfl⟩) R190781
theorem R159985 : Reach 159985 := rs (se 2 (by rfl) ⟨59994, by rfl⟩) R119989
theorem R127217 : Reach 127217 := rs (se 2 (by rfl) ⟨47706, by rfl⟩) R95413
theorem R127235 : Reach 127235 := rs (se 1 (by rfl) ⟨95426, by rfl⟩) R190853
theorem R553229 : Reach 553229 := rs (se 3 (by rfl) ⟨103730, by rfl⟩) R207461
theorem R127265 : Reach 127265 := rs (se 2 (by rfl) ⟨47724, by rfl⟩) R95449
theorem R127283 : Reach 127283 := rs (se 1 (by rfl) ⟨95462, by rfl⟩) R190925
theorem R94531 : Reach 94531 := rs (se 1 (by rfl) ⟨70898, by rfl⟩) R141797
theorem R127313 : Reach 127313 := rs (se 2 (by rfl) ⟨47742, by rfl⟩) R95485
theorem R127331 : Reach 127331 := rs (se 1 (by rfl) ⟨95498, by rfl⟩) R190997
theorem R127361 : Reach 127361 := rs (se 2 (by rfl) ⟨47760, by rfl⟩) R95521
theorem R127379 : Reach 127379 := rs (se 1 (by rfl) ⟨95534, by rfl⟩) R191069
theorem R127409 : Reach 127409 := rs (se 2 (by rfl) ⟨47778, by rfl⟩) R95557
theorem R127427 : Reach 127427 := rs (se 1 (by rfl) ⟨95570, by rfl⟩) R191141
theorem R192977 : Reach 192977 := rs (se 2 (by rfl) ⟨72366, by rfl⟩) R144733
theorem R94675 : Reach 94675 := rs (se 1 (by rfl) ⟨71006, by rfl⟩) R142013
theorem R127457 : Reach 127457 := rs (se 2 (by rfl) ⟨47796, by rfl⟩) R95593
theorem R192995 : Reach 192995 := rs (se 1 (by rfl) ⟨144746, by rfl⟩) R289493
theorem R127475 : Reach 127475 := rs (se 1 (by rfl) ⟨95606, by rfl⟩) R191213
theorem R127505 : Reach 127505 := rs (se 2 (by rfl) ⟨47814, by rfl⟩) R95629
theorem R127523 : Reach 127523 := rs (se 1 (by rfl) ⟨95642, by rfl⟩) R191285
theorem R127553 : Reach 127553 := rs (se 2 (by rfl) ⟨47832, by rfl⟩) R95665
theorem R127555 : Reach 127555 := rs (se 1 (by rfl) ⟨95666, by rfl⟩) R191333
theorem R127571 : Reach 127571 := rs (se 1 (by rfl) ⟨95678, by rfl⟩) R191357
theorem R94819 : Reach 94819 := rs (se 1 (by rfl) ⟨71114, by rfl⟩) R142229
theorem R291437 : Reach 291437 := rs (se 3 (by rfl) ⟨54644, by rfl⟩) R109289
theorem R127601 : Reach 127601 := rs (se 2 (by rfl) ⟨47850, by rfl⟩) R95701
theorem R127619 : Reach 127619 := rs (se 1 (by rfl) ⟨95714, by rfl⟩) R191429
theorem R127649 : Reach 127649 := rs (se 2 (by rfl) ⟨47868, by rfl⟩) R95737
theorem R291491 : Reach 291491 := rs (se 1 (by rfl) ⟨218618, by rfl⟩) R437237
theorem R127667 : Reach 127667 := rs (se 1 (by rfl) ⟨95750, by rfl⟩) R191501
theorem R127697 : Reach 127697 := rs (se 2 (by rfl) ⟨47886, by rfl⟩) R95773
theorem R226019 : Reach 226019 := rs (se 1 (by rfl) ⟨169514, by rfl⟩) R339029
theorem R127715 : Reach 127715 := rs (se 1 (by rfl) ⟨95786, by rfl⟩) R191573
theorem R193265 : Reach 193265 := rs (se 2 (by rfl) ⟨72474, by rfl⟩) R144949
theorem R94963 : Reach 94963 := rs (se 1 (by rfl) ⟨71222, by rfl⟩) R142445
theorem R127745 : Reach 127745 := rs (se 2 (by rfl) ⟨47904, by rfl⟩) R95809
theorem R193283 : Reach 193283 := rs (se 1 (by rfl) ⟨144962, by rfl⟩) R289925
theorem R127763 : Reach 127763 := rs (se 1 (by rfl) ⟨95822, by rfl⟩) R191645
theorem R127793 : Reach 127793 := rs (se 2 (by rfl) ⟨47922, by rfl⟩) R95845
theorem R127811 : Reach 127811 := rs (se 1 (by rfl) ⟨95858, by rfl⟩) R191717
theorem R127841 : Reach 127841 := rs (se 2 (by rfl) ⟨47940, by rfl⟩) R95881
theorem R127859 : Reach 127859 := rs (se 1 (by rfl) ⟨95894, by rfl⟩) R191789
theorem R95107 : Reach 95107 := rs (se 1 (by rfl) ⟨71330, by rfl⟩) R142661
theorem R127889 : Reach 127889 := rs (se 2 (by rfl) ⟨47958, by rfl⟩) R95917
theorem R422819 : Reach 422819 := rs (se 1 (by rfl) ⟨317114, by rfl⟩) R634229
theorem R127907 : Reach 127907 := rs (se 1 (by rfl) ⟨95930, by rfl⟩) R191861
theorem R291761 : Reach 291761 := rs (se 2 (by rfl) ⟨109410, by rfl⟩) R218821
theorem R127937 : Reach 127937 := rs (se 2 (by rfl) ⟨47976, by rfl⟩) R95953
theorem R324557 : Reach 324557 := rs (se 3 (by rfl) ⟨60854, by rfl⟩) R121709
theorem R127955 : Reach 127955 := rs (se 1 (by rfl) ⟨95966, by rfl⟩) R191933
theorem R127985 : Reach 127985 := rs (se 2 (by rfl) ⟨47994, by rfl⟩) R95989
theorem R128003 : Reach 128003 := rs (se 1 (by rfl) ⟨96002, by rfl⟩) R192005
theorem R193553 : Reach 193553 := rs (se 2 (by rfl) ⟨72582, by rfl⟩) R145165
theorem R95251 : Reach 95251 := rs (se 1 (by rfl) ⟨71438, by rfl⟩) R142877
theorem R128033 : Reach 128033 := rs (se 2 (by rfl) ⟨48012, by rfl⟩) R96025
theorem R193571 : Reach 193571 := rs (se 1 (by rfl) ⟨145178, by rfl⟩) R290357
theorem R128051 : Reach 128051 := rs (se 1 (by rfl) ⟨96038, by rfl⟩) R192077
theorem R128081 : Reach 128081 := rs (se 2 (by rfl) ⟨48030, by rfl⟩) R96061
theorem R128099 : Reach 128099 := rs (se 1 (by rfl) ⟨96074, by rfl⟩) R192149
theorem R128129 : Reach 128129 := rs (se 2 (by rfl) ⟨48048, by rfl⟩) R96097
theorem R128147 : Reach 128147 := rs (se 1 (by rfl) ⟨96110, by rfl⟩) R192221
theorem R95395 : Reach 95395 := rs (se 1 (by rfl) ⟨71546, by rfl⟩) R143093
theorem R128177 : Reach 128177 := rs (se 2 (by rfl) ⟨48066, by rfl⟩) R96133
theorem R128195 : Reach 128195 := rs (se 1 (by rfl) ⟨96146, by rfl⟩) R192293
theorem R193745 : Reach 193745 := rs (se 2 (by rfl) ⟨72654, by rfl⟩) R145309
theorem R128225 : Reach 128225 := rs (se 2 (by rfl) ⟨48084, by rfl⟩) R96169
theorem R128243 : Reach 128243 := rs (se 1 (by rfl) ⟨96182, by rfl⟩) R192365
theorem R161041 : Reach 161041 := rs (se 2 (by rfl) ⟨60390, by rfl⟩) R120781
theorem R128273 : Reach 128273 := rs (se 2 (by rfl) ⟨48102, by rfl⟩) R96205
theorem R128291 : Reach 128291 := rs (se 1 (by rfl) ⟨96218, by rfl⟩) R192437
theorem R193841 : Reach 193841 := rs (se 2 (by rfl) ⟨72690, by rfl⟩) R145381
theorem R95539 : Reach 95539 := rs (se 1 (by rfl) ⟨71654, by rfl⟩) R143309
theorem R128321 : Reach 128321 := rs (se 2 (by rfl) ⟨48120, by rfl⟩) R96241
theorem R193859 : Reach 193859 := rs (se 1 (by rfl) ⟨145394, by rfl⟩) R290789
theorem R128339 : Reach 128339 := rs (se 1 (by rfl) ⟨96254, by rfl⟩) R192509
theorem R750961 : Reach 750961 := rs (se 2 (by rfl) ⟨281610, by rfl⟩) R563221
theorem R128369 : Reach 128369 := rs (se 2 (by rfl) ⟨48138, by rfl⟩) R96277
theorem R128387 : Reach 128387 := rs (se 1 (by rfl) ⟨96290, by rfl⟩) R192581
theorem R128417 : Reach 128417 := rs (se 2 (by rfl) ⟨48156, by rfl⟩) R96313
theorem R128435 : Reach 128435 := rs (se 1 (by rfl) ⟨96326, by rfl⟩) R192653
theorem R95683 : Reach 95683 := rs (se 1 (by rfl) ⟨71762, by rfl⟩) R143525
theorem R292301 : Reach 292301 := rs (se 3 (by rfl) ⟨54806, by rfl⟩) R109613
theorem R128465 : Reach 128465 := rs (se 2 (by rfl) ⟨48174, by rfl⟩) R96349
theorem R128483 : Reach 128483 := rs (se 1 (by rfl) ⟨96362, by rfl⟩) R192725
theorem R128513 : Reach 128513 := rs (se 2 (by rfl) ⟨48192, by rfl⟩) R96385
theorem R292355 : Reach 292355 := rs (se 1 (by rfl) ⟨219266, by rfl⟩) R438533
theorem R128531 : Reach 128531 := rs (se 1 (by rfl) ⟨96398, by rfl⟩) R192797
theorem R128561 : Reach 128561 := rs (se 2 (by rfl) ⟨48210, by rfl⟩) R96421
theorem R128579 : Reach 128579 := rs (se 1 (by rfl) ⟨96434, by rfl⟩) R192869
theorem R194129 : Reach 194129 := rs (se 2 (by rfl) ⟨72798, by rfl⟩) R145597
theorem R95827 : Reach 95827 := rs (se 1 (by rfl) ⟨71870, by rfl⟩) R143741
theorem R128609 : Reach 128609 := rs (se 2 (by rfl) ⟨48228, by rfl⟩) R96457
theorem R194147 : Reach 194147 := rs (se 1 (by rfl) ⟨145610, by rfl⟩) R291221
theorem R128627 : Reach 128627 := rs (se 1 (by rfl) ⟨96470, by rfl⟩) R192941
theorem R128657 : Reach 128657 := rs (se 2 (by rfl) ⟨48246, by rfl⟩) R96493
theorem R161443 : Reach 161443 := rs (se 1 (by rfl) ⟨121082, by rfl⟩) R242165
theorem R128675 : Reach 128675 := rs (se 1 (by rfl) ⟨96506, by rfl⟩) R193013
theorem R128705 : Reach 128705 := rs (se 2 (by rfl) ⟨48264, by rfl⟩) R96529
theorem R423629 : Reach 423629 := rs (se 3 (by rfl) ⟨79430, by rfl⟩) R158861
theorem R554701 : Reach 554701 := rs (se 3 (by rfl) ⟨104006, by rfl⟩) R208013
theorem R161489 : Reach 161489 := rs (se 2 (by rfl) ⟨60558, by rfl⟩) R121117
theorem R128723 : Reach 128723 := rs (se 1 (by rfl) ⟨96542, by rfl⟩) R193085
theorem R95971 : Reach 95971 := rs (se 1 (by rfl) ⟨71978, by rfl⟩) R143957
theorem R128753 : Reach 128753 := rs (se 2 (by rfl) ⟨48282, by rfl⟩) R96565
theorem R128771 : Reach 128771 := rs (se 1 (by rfl) ⟨96578, by rfl⟩) R193157
theorem R292625 : Reach 292625 := rs (se 2 (by rfl) ⟨109734, by rfl⟩) R219469
theorem R128801 : Reach 128801 := rs (se 2 (by rfl) ⟨48300, by rfl⟩) R96601
theorem R128803 : Reach 128803 := rs (se 1 (by rfl) ⟨96602, by rfl⟩) R193205
theorem R128819 : Reach 128819 := rs (se 1 (by rfl) ⟨96614, by rfl⟩) R193229
theorem R128849 : Reach 128849 := rs (se 2 (by rfl) ⟨48318, by rfl⟩) R96637
theorem R128867 : Reach 128867 := rs (se 1 (by rfl) ⟨96650, by rfl⟩) R193301
theorem R194417 : Reach 194417 := rs (se 2 (by rfl) ⟨72906, by rfl⟩) R145813
theorem R96115 : Reach 96115 := rs (se 1 (by rfl) ⟨72086, by rfl⟩) R144173
theorem R128897 : Reach 128897 := rs (se 2 (by rfl) ⟨48336, by rfl⟩) R96673
theorem R194435 : Reach 194435 := rs (se 1 (by rfl) ⟨145826, by rfl⟩) R291653
theorem R128915 : Reach 128915 := rs (se 1 (by rfl) ⟨96686, by rfl⟩) R193373
theorem R128945 : Reach 128945 := rs (se 2 (by rfl) ⟨48354, by rfl⟩) R96709
theorem R128963 : Reach 128963 := rs (se 1 (by rfl) ⟨96722, by rfl⟩) R193445
theorem R128993 : Reach 128993 := rs (se 2 (by rfl) ⟨48372, by rfl⟩) R96745
theorem R161777 : Reach 161777 := rs (se 2 (by rfl) ⟨60666, by rfl⟩) R121333
theorem R129011 : Reach 129011 := rs (se 1 (by rfl) ⟨96758, by rfl⟩) R193517
theorem R96259 : Reach 96259 := rs (se 1 (by rfl) ⟨72194, by rfl⟩) R144389
theorem R129041 : Reach 129041 := rs (se 2 (by rfl) ⟨48390, by rfl⟩) R96781
theorem R129059 : Reach 129059 := rs (se 1 (by rfl) ⟨96794, by rfl⟩) R193589
theorem R129089 : Reach 129089 := rs (se 2 (by rfl) ⟨48408, by rfl⟩) R96817
theorem R129107 : Reach 129107 := rs (se 1 (by rfl) ⟨96830, by rfl⟩) R193661
theorem R129137 : Reach 129137 := rs (se 2 (by rfl) ⟨48426, by rfl⟩) R96853
theorem R129155 : Reach 129155 := rs (se 1 (by rfl) ⟨96866, by rfl⟩) R193733
theorem R194705 : Reach 194705 := rs (se 2 (by rfl) ⟨73014, by rfl⟩) R146029
theorem R96403 : Reach 96403 := rs (se 1 (by rfl) ⟨72302, by rfl⟩) R144605
theorem R129185 : Reach 129185 := rs (se 2 (by rfl) ⟨48444, by rfl⟩) R96889
theorem R194723 : Reach 194723 := rs (se 1 (by rfl) ⟨146042, by rfl⟩) R292085
theorem R129203 : Reach 129203 := rs (se 1 (by rfl) ⟨96902, by rfl⟩) R193805
theorem R1308869 : Reach 1308869 := rs (se 4 (by rfl) ⟨122706, by rfl⟩) R245413
theorem R129233 : Reach 129233 := rs (se 2 (by rfl) ⟨48462, by rfl⟩) R96925
theorem R129251 : Reach 129251 := rs (se 1 (by rfl) ⟨96938, by rfl⟩) R193877
theorem R981233 : Reach 981233 := rs (se 2 (by rfl) ⟨367962, by rfl⟩) R735925
theorem R129281 : Reach 129281 := rs (se 2 (by rfl) ⟨48480, by rfl⟩) R96961
theorem R129299 : Reach 129299 := rs (se 1 (by rfl) ⟨96974, by rfl⟩) R193949
theorem R96547 : Reach 96547 := rs (se 1 (by rfl) ⟨72410, by rfl⟩) R144821
theorem R293165 : Reach 293165 := rs (se 3 (by rfl) ⟨54968, by rfl⟩) R109937
theorem R129329 : Reach 129329 := rs (se 2 (by rfl) ⟨48498, by rfl⟩) R96997
theorem R129347 : Reach 129347 := rs (se 1 (by rfl) ⟨97010, by rfl⟩) R194021
theorem R489797 : Reach 489797 := rs (se 4 (by rfl) ⟨45918, by rfl⟩) R91837
theorem R129377 : Reach 129377 := rs (se 2 (by rfl) ⟨48516, by rfl⟩) R97033
theorem R293219 : Reach 293219 := rs (se 1 (by rfl) ⟨219914, by rfl⟩) R439829
theorem R129395 : Reach 129395 := rs (se 1 (by rfl) ⟨97046, by rfl⟩) R194093
theorem R129425 : Reach 129425 := rs (se 2 (by rfl) ⟨48534, by rfl⟩) R97069
theorem R129443 : Reach 129443 := rs (se 1 (by rfl) ⟨97082, by rfl⟩) R194165
theorem R194993 : Reach 194993 := rs (se 2 (by rfl) ⟨73122, by rfl⟩) R146245
theorem R96691 : Reach 96691 := rs (se 1 (by rfl) ⟨72518, by rfl⟩) R145037
theorem R129473 : Reach 129473 := rs (se 2 (by rfl) ⟨48552, by rfl⟩) R97105
theorem R195011 : Reach 195011 := rs (se 1 (by rfl) ⟨146258, by rfl⟩) R292517
theorem R129491 : Reach 129491 := rs (se 1 (by rfl) ⟨97118, by rfl⟩) R194237
theorem R129521 : Reach 129521 := rs (se 2 (by rfl) ⟨48570, by rfl⟩) R97141
theorem R129539 : Reach 129539 := rs (se 1 (by rfl) ⟨97154, by rfl⟩) R194309
theorem R752141 : Reach 752141 := rs (se 3 (by rfl) ⟨141026, by rfl⟩) R282053
theorem R129569 : Reach 129569 := rs (se 2 (by rfl) ⟨48588, by rfl⟩) R97177
theorem R129587 : Reach 129587 := rs (se 1 (by rfl) ⟨97190, by rfl⟩) R194381
theorem R96835 : Reach 96835 := rs (se 1 (by rfl) ⟨72626, by rfl⟩) R145253
theorem R129617 : Reach 129617 := rs (se 2 (by rfl) ⟨48606, by rfl⟩) R97213
theorem R129635 : Reach 129635 := rs (se 1 (by rfl) ⟨97226, by rfl⟩) R194453
theorem R293489 : Reach 293489 := rs (se 2 (by rfl) ⟨110058, by rfl⟩) R220117
theorem R129665 : Reach 129665 := rs (se 2 (by rfl) ⟨48624, by rfl⟩) R97249
theorem R129683 : Reach 129683 := rs (se 1 (by rfl) ⟨97262, by rfl⟩) R194525
theorem R129713 : Reach 129713 := rs (se 2 (by rfl) ⟨48642, by rfl⟩) R97285
theorem R162499 : Reach 162499 := rs (se 1 (by rfl) ⟨121874, by rfl⟩) R243749
theorem R129731 : Reach 129731 := rs (se 1 (by rfl) ⟨97298, by rfl⟩) R194597
theorem R195281 : Reach 195281 := rs (se 2 (by rfl) ⟨73230, by rfl⟩) R146461
theorem R96979 : Reach 96979 := rs (se 1 (by rfl) ⟨72734, by rfl⟩) R145469
theorem R129761 : Reach 129761 := rs (se 2 (by rfl) ⟨48660, by rfl⟩) R97321
theorem R195299 : Reach 195299 := rs (se 1 (by rfl) ⟨146474, by rfl⟩) R292949
theorem R129779 : Reach 129779 := rs (se 1 (by rfl) ⟨97334, by rfl⟩) R194669
theorem R129809 : Reach 129809 := rs (se 2 (by rfl) ⟨48678, by rfl⟩) R97357
theorem R129827 : Reach 129827 := rs (se 1 (by rfl) ⟨97370, by rfl⟩) R194741
theorem R129857 : Reach 129857 := rs (se 2 (by rfl) ⟨48696, by rfl⟩) R97393
theorem R129875 : Reach 129875 := rs (se 1 (by rfl) ⟨97406, by rfl⟩) R194813
theorem R97123 : Reach 97123 := rs (se 1 (by rfl) ⟨72842, by rfl⟩) R145685
theorem R129905 : Reach 129905 := rs (se 2 (by rfl) ⟨48714, by rfl⟩) R97429
theorem R129923 : Reach 129923 := rs (se 1 (by rfl) ⟨97442, by rfl⟩) R194885
theorem R293777 : Reach 293777 := rs (se 2 (by rfl) ⟨110166, by rfl⟩) R220333
theorem R129953 : Reach 129953 := rs (se 2 (by rfl) ⟨48732, by rfl⟩) R97465
theorem R129971 : Reach 129971 := rs (se 1 (by rfl) ⟨97478, by rfl⟩) R194957
theorem R261073 : Reach 261073 := rs (se 2 (by rfl) ⟨97902, by rfl⟩) R195805
theorem R130001 : Reach 130001 := rs (se 2 (by rfl) ⟨48750, by rfl⟩) R97501
theorem R130019 : Reach 130019 := rs (se 1 (by rfl) ⟨97514, by rfl⟩) R195029
theorem R490481 : Reach 490481 := rs (se 2 (by rfl) ⟨183930, by rfl⟩) R367861
theorem R195569 : Reach 195569 := rs (se 2 (by rfl) ⟨73338, by rfl⟩) R146677
theorem R97267 : Reach 97267 := rs (se 1 (by rfl) ⟨72950, by rfl⟩) R145901
theorem R130049 : Reach 130049 := rs (se 2 (by rfl) ⟨48768, by rfl⟩) R97537
theorem R195587 : Reach 195587 := rs (se 1 (by rfl) ⟨146690, by rfl⟩) R293381
theorem R130067 : Reach 130067 := rs (se 1 (by rfl) ⟨97550, by rfl⟩) R195101
theorem R130097 : Reach 130097 := rs (se 2 (by rfl) ⟨48786, by rfl⟩) R97573
theorem R130115 : Reach 130115 := rs (se 1 (by rfl) ⟨97586, by rfl⟩) R195173
theorem R293969 : Reach 293969 := rs (se 2 (by rfl) ⟨110238, by rfl⟩) R220477
theorem R130145 : Reach 130145 := rs (se 2 (by rfl) ⟨48804, by rfl⟩) R97609
theorem R130163 : Reach 130163 := rs (se 1 (by rfl) ⟨97622, by rfl⟩) R195245
theorem R162947 : Reach 162947 := rs (se 1 (by rfl) ⟨122210, by rfl⟩) R244421
theorem R97411 : Reach 97411 := rs (se 1 (by rfl) ⟨73058, by rfl⟩) R146117
theorem R294029 : Reach 294029 := rs (se 3 (by rfl) ⟨55130, by rfl⟩) R110261
theorem R130193 : Reach 130193 := rs (se 2 (by rfl) ⟨48822, by rfl⟩) R97645
theorem R130211 : Reach 130211 := rs (se 1 (by rfl) ⟨97658, by rfl⟩) R195317
theorem R130241 : Reach 130241 := rs (se 2 (by rfl) ⟨48840, by rfl⟩) R97681
theorem R130259 : Reach 130259 := rs (se 1 (by rfl) ⟨97694, by rfl⟩) R195389
theorem R130289 : Reach 130289 := rs (se 2 (by rfl) ⟨48858, by rfl⟩) R97717
theorem R130307 : Reach 130307 := rs (se 1 (by rfl) ⟨97730, by rfl⟩) R195461
theorem R195857 : Reach 195857 := rs (se 2 (by rfl) ⟨73446, by rfl⟩) R146893
theorem R97555 : Reach 97555 := rs (se 1 (by rfl) ⟨73166, by rfl⟩) R146333
theorem R130337 : Reach 130337 := rs (se 2 (by rfl) ⟨48876, by rfl⟩) R97753
theorem R195875 : Reach 195875 := rs (se 1 (by rfl) ⟨146906, by rfl⟩) R293813
theorem R130355 : Reach 130355 := rs (se 1 (by rfl) ⟨97766, by rfl⟩) R195533
theorem R130385 : Reach 130385 := rs (se 2 (by rfl) ⟨48894, by rfl⟩) R97789
theorem R130403 : Reach 130403 := rs (se 1 (by rfl) ⟨97802, by rfl⟩) R195605
theorem R130433 : Reach 130433 := rs (se 2 (by rfl) ⟨48912, by rfl⟩) R97825
theorem R130451 : Reach 130451 := rs (se 1 (by rfl) ⟨97838, by rfl⟩) R195677
theorem R163235 : Reach 163235 := rs (se 1 (by rfl) ⟨122426, by rfl⟩) R244853
theorem R97699 : Reach 97699 := rs (se 1 (by rfl) ⟨73274, by rfl⟩) R146549
theorem R130481 : Reach 130481 := rs (se 2 (by rfl) ⟨48930, by rfl⟩) R97861
theorem R130499 : Reach 130499 := rs (se 1 (by rfl) ⟨97874, by rfl⟩) R195749
theorem R130529 : Reach 130529 := rs (se 2 (by rfl) ⟨48948, by rfl⟩) R97897
theorem R130547 : Reach 130547 := rs (se 1 (by rfl) ⟨97910, by rfl⟩) R195821
theorem R458245 : Reach 458245 := rs (se 4 (by rfl) ⟨42960, by rfl⟩) R85921
theorem R130577 : Reach 130577 := rs (se 2 (by rfl) ⟨48966, by rfl⟩) R97933
theorem R130595 : Reach 130595 := rs (se 1 (by rfl) ⟨97946, by rfl⟩) R195893
theorem R97843 : Reach 97843 := rs (se 1 (by rfl) ⟨73382, by rfl⟩) R146765
theorem R130625 : Reach 130625 := rs (se 2 (by rfl) ⟨48984, by rfl⟩) R97969
theorem R130643 : Reach 130643 := rs (se 1 (by rfl) ⟨97982, by rfl⟩) R195965
theorem R360035 : Reach 360035 := rs (se 1 (by rfl) ⟨270026, by rfl⟩) R540053
theorem R130673 : Reach 130673 := rs (se 2 (by rfl) ⟨49002, by rfl⟩) R98005
theorem R130691 : Reach 130691 := rs (se 1 (by rfl) ⟨98018, by rfl⟩) R196037
theorem R97987 : Reach 97987 := rs (se 1 (by rfl) ⟨73490, by rfl⟩) R146981
theorem R327473 : Reach 327473 := rs (se 2 (by rfl) ⟨122802, by rfl⟩) R245605
theorem R131041 : Reach 131041 := rs (se 2 (by rfl) ⟨49140, by rfl⟩) R98281
theorem R426059 : Reach 426059 := rs (se 1 (by rfl) ⟨319544, by rfl⟩) R639089
theorem R983171 : Reach 983171 := rs (se 1 (by rfl) ⟨737378, by rfl⟩) R1474757
theorem R327959 : Reach 327959 := rs (se 1 (by rfl) ⟨245969, by rfl⟩) R491939
theorem R524675 : Reach 524675 := rs (se 1 (by rfl) ⟨393506, by rfl⟩) R787013
theorem R229825 : Reach 229825 := rs (se 2 (by rfl) ⟨86184, by rfl⟩) R172369
theorem R197081 : Reach 197081 := rs (se 2 (by rfl) ⟨73905, by rfl⟩) R147811
theorem R328157 : Reach 328157 := rs (se 3 (by rfl) ⟨61529, by rfl⟩) R123059
theorem R1049219 : Reach 1049219 := rs (se 1 (by rfl) ⟨786914, by rfl⟩) R1573829
theorem R131801 : Reach 131801 := rs (se 2 (by rfl) ⟨49425, by rfl⟩) R98851
theorem R590723 : Reach 590723 := rs (se 1 (by rfl) ⟨443042, by rfl⟩) R886085
theorem R164747 : Reach 164747 := rs (se 1 (by rfl) ⟨123560, by rfl⟩) R247121
theorem R492439 : Reach 492439 := rs (se 1 (by rfl) ⟨369329, by rfl⟩) R738659
theorem R623537 : Reach 623537 := rs (se 2 (by rfl) ⟨233826, by rfl⟩) R467653
theorem R361523 : Reach 361523 := rs (se 1 (by rfl) ⟨271142, by rfl⟩) R542285
theorem R164929 : Reach 164929 := rs (se 2 (by rfl) ⟨61848, by rfl⟩) R123697
theorem R361675 : Reach 361675 := rs (se 1 (by rfl) ⟨271256, by rfl⟩) R542513
theorem R361745 : Reach 361745 := rs (se 2 (by rfl) ⟨135654, by rfl⟩) R271309
theorem R165377 : Reach 165377 := rs (se 2 (by rfl) ⟨62016, by rfl⟩) R124033
theorem R427841 : Reach 427841 := rs (se 2 (by rfl) ⟨160440, by rfl⟩) R320881
theorem R166195 : Reach 166195 := rs (se 1 (by rfl) ⟨124646, by rfl⟩) R249293
theorem R330115 : Reach 330115 := rs (se 1 (by rfl) ⟨247586, by rfl⟩) R495173
theorem R461207 : Reach 461207 := rs (se 1 (by rfl) ⟨345905, by rfl⟩) R691811
theorem R133643 : Reach 133643 := rs (se 1 (by rfl) ⟨100232, by rfl⟩) R200465
theorem R133655 : Reach 133655 := rs (se 1 (by rfl) ⟨100241, by rfl⟩) R200483
theorem R330419 : Reach 330419 := rs (se 1 (by rfl) ⟨247814, by rfl⟩) R495629
theorem R1084205 : Reach 1084205 := rs (se 3 (by rfl) ⟨203288, by rfl⟩) R406577
theorem R363437 : Reach 363437 := rs (se 3 (by rfl) ⟨68144, by rfl⟩) R136289
theorem R232523 : Reach 232523 := rs (se 1 (by rfl) ⟨174392, by rfl⟩) R348785
theorem R134347 : Reach 134347 := rs (se 1 (by rfl) ⟨100760, by rfl⟩) R201521
theorem R1019141 : Reach 1019141 := rs (se 4 (by rfl) ⟨95544, by rfl⟩) R191089
theorem R134617 : Reach 134617 := rs (se 2 (by rfl) ⟨50481, by rfl⟩) R100963
theorem R364121 : Reach 364121 := rs (se 2 (by rfl) ⟨136545, by rfl⟩) R273091
theorem R134873 : Reach 134873 := rs (se 2 (by rfl) ⟨50577, by rfl⟩) R101155
theorem R429785 : Reach 429785 := rs (se 2 (by rfl) ⟨161169, by rfl⟩) R322339
theorem R659501 : Reach 659501 := rs (se 3 (by rfl) ⟨123656, by rfl⟩) R247313
theorem R167987 : Reach 167987 := rs (se 1 (by rfl) ⟨125990, by rfl⟩) R251981
theorem R462941 : Reach 462941 := rs (se 3 (by rfl) ⟨86801, by rfl⟩) R173603
theorem R364675 : Reach 364675 := rs (se 1 (by rfl) ⟨273506, by rfl⟩) R547013
theorem R1380503 : Reach 1380503 := rs (se 1 (by rfl) ⟨1035377, by rfl⟩) R2070755
theorem R200897 : Reach 200897 := rs (se 2 (by rfl) ⟨75336, by rfl⟩) R150673
theorem R135577 : Reach 135577 := rs (se 2 (by rfl) ⟨50841, by rfl⟩) R101683
theorem R463283 : Reach 463283 := rs (se 1 (by rfl) ⟨347462, by rfl⟩) R694925
theorem R823769 : Reach 823769 := rs (se 2 (by rfl) ⟨308913, by rfl⟩) R617827
theorem R332765 : Reach 332765 := rs (se 3 (by rfl) ⟨62393, by rfl⟩) R124787
theorem R791569 : Reach 791569 := rs (se 2 (by rfl) ⟨296838, by rfl⟩) R593677
theorem R103447 : Reach 103447 := rs (se 1 (by rfl) ⟨77585, by rfl⟩) R155171
theorem R431405 : Reach 431405 := rs (se 3 (by rfl) ⟨80888, by rfl⟩) R161777
theorem R792139 : Reach 792139 := rs (se 1 (by rfl) ⟨594104, by rfl⟩) R1188209
theorem R1087181 : Reach 1087181 := rs (se 3 (by rfl) ⟨203846, by rfl⟩) R407693
theorem R1382321 : Reach 1382321 := rs (se 2 (by rfl) ⟨518370, by rfl⟩) R1036741
theorem R333827 : Reach 333827 := rs (se 1 (by rfl) ⟨250370, by rfl⟩) R500741
theorem R137303 : Reach 137303 := rs (se 1 (by rfl) ⟨102977, by rfl⟩) R205955
theorem R301619 : Reach 301619 := rs (se 1 (by rfl) ⟨226214, by rfl⟩) R452429
theorem R105239 : Reach 105239 := rs (se 1 (by rfl) ⟨78929, by rfl⟩) R157859
theorem R2235235 : Reach 2235235 := rs (se 1 (by rfl) ⟨1676426, by rfl⟩) R3352853
theorem R891749 : Reach 891749 := rs (se 4 (by rfl) ⟨83601, by rfl⟩) R167203
theorem R269207 : Reach 269207 := rs (se 1 (by rfl) ⟨201905, by rfl⟩) R403811
theorem R367553 : Reach 367553 := rs (se 2 (by rfl) ⟨137832, by rfl⟩) R275665
theorem R269335 : Reach 269335 := rs (se 1 (by rfl) ⟨202001, by rfl⟩) R404003
theorem R367895 : Reach 367895 := rs (se 1 (by rfl) ⟨275921, by rfl⟩) R551843
theorem R138647 : Reach 138647 := rs (se 1 (by rfl) ⟨103985, by rfl⟩) R207971
theorem R105943 : Reach 105943 := rs (se 1 (by rfl) ⟨79457, by rfl⟩) R158915
theorem R237107 : Reach 237107 := rs (se 1 (by rfl) ⟨177830, by rfl⟩) R355661
theorem R237131 : Reach 237131 := rs (se 1 (by rfl) ⟨177848, by rfl⟩) R355697
theorem R204481 : Reach 204481 := rs (se 2 (by rfl) ⟨76680, by rfl⟩) R153361
theorem R171737 : Reach 171737 := rs (se 2 (by rfl) ⟨64401, by rfl⟩) R128803
theorem R270155 : Reach 270155 := rs (se 1 (by rfl) ⟨202616, by rfl⟩) R405233
theorem R139415 : Reach 139415 := rs (se 1 (by rfl) ⟨104561, by rfl⟩) R209123
theorem R368819 : Reach 368819 := rs (se 1 (by rfl) ⟨276614, by rfl⟩) R553229
theorem R237917 : Reach 237917 := rs (se 3 (by rfl) ⟨44609, by rfl⟩) R89219
theorem R631313 : Reach 631313 := rs (se 2 (by rfl) ⟨236742, by rfl⟩) R473485
theorem R205847 : Reach 205847 := rs (se 1 (by rfl) ⟨154385, by rfl⟩) R308771
theorem R435293 : Reach 435293 := rs (se 3 (by rfl) ⟨81617, by rfl⟩) R163235
theorem R107659 : Reach 107659 := rs (se 1 (by rfl) ⟨80744, by rfl⟩) R161489
theorem R369809 : Reach 369809 := rs (se 2 (by rfl) ⟨138678, by rfl⟩) R277357
theorem R140555 : Reach 140555 := rs (se 1 (by rfl) ⟨105416, by rfl⟩) R210833
theorem R369937 : Reach 369937 := rs (se 2 (by rfl) ⟨138726, by rfl⟩) R277453
theorem R271667 : Reach 271667 := rs (se 1 (by rfl) ⟨203750, by rfl⟩) R407501
theorem R140683 : Reach 140683 := rs (se 1 (by rfl) ⟨105512, by rfl⟩) R211025
theorem R140825 : Reach 140825 := rs (se 2 (by rfl) ⟨52809, by rfl⟩) R105619
theorem R140953 : Reach 140953 := rs (se 2 (by rfl) ⟨52857, by rfl⟩) R105715
theorem R501427 : Reach 501427 := rs (se 1 (by rfl) ⟨376070, by rfl⟩) R752141
theorem R108631 : Reach 108631 := rs (se 1 (by rfl) ⟨81473, by rfl⟩) R162947
theorem R239705 : Reach 239705 := rs (se 2 (by rfl) ⟨89889, by rfl⟩) R179779
theorem R141527 : Reach 141527 := rs (se 1 (by rfl) ⟨106145, by rfl⟩) R212291
theorem R272663 : Reach 272663 := rs (se 1 (by rfl) ⟨204497, by rfl⟩) R408995
theorem R338251 : Reach 338251 := rs (se 1 (by rfl) ⟨253688, by rfl⟩) R507377
theorem R141655 : Reach 141655 := rs (se 1 (by rfl) ⟨106241, by rfl⟩) R212483
theorem R240023 : Reach 240023 := rs (se 1 (by rfl) ⟨180017, by rfl⟩) R360035
theorem R600641 : Reach 600641 := rs (se 2 (by rfl) ⟨225240, by rfl⟩) R450481
theorem R174721 : Reach 174721 := rs (se 2 (by rfl) ⟨65520, by rfl⟩) R131041
theorem R731825 : Reach 731825 := rs (se 2 (by rfl) ⟨274434, by rfl⟩) R548869
theorem R174835 : Reach 174835 := rs (se 1 (by rfl) ⟨131126, by rfl⟩) R262253
theorem R174899 : Reach 174899 := rs (se 1 (by rfl) ⟨131174, by rfl⟩) R262349
theorem R109451 : Reach 109451 := rs (se 1 (by rfl) ⟨82088, by rfl⟩) R164177
theorem R142283 : Reach 142283 := rs (se 1 (by rfl) ⟨106712, by rfl⟩) R213425
theorem R142411 : Reach 142411 := rs (se 1 (by rfl) ⟨106808, by rfl⟩) R213617
theorem R666755 : Reach 666755 := rs (se 1 (by rfl) ⟨500066, by rfl⟩) R1000133
theorem R437399 : Reach 437399 := rs (se 1 (by rfl) ⟨328049, by rfl⟩) R656099
theorem R240833 : Reach 240833 := rs (se 2 (by rfl) ⟨90312, by rfl⟩) R180625
theorem R142553 : Reach 142553 := rs (se 2 (by rfl) ⟨53457, by rfl⟩) R106915
theorem R142681 : Reach 142681 := rs (se 2 (by rfl) ⟨53505, by rfl⟩) R107011
theorem R732509 : Reach 732509 := rs (se 3 (by rfl) ⟨137345, by rfl⟩) R274691
theorem R208307 : Reach 208307 := rs (se 1 (by rfl) ⟨156230, by rfl⟩) R312461
theorem R110155 : Reach 110155 := rs (se 1 (by rfl) ⟨82616, by rfl⟩) R165233
theorem R274013 : Reach 274013 := rs (se 3 (by rfl) ⟨51377, by rfl⟩) R102755
theorem R241501 : Reach 241501 := rs (se 3 (by rfl) ⟨45281, by rfl⟩) R90563
theorem R143255 : Reach 143255 := rs (se 1 (by rfl) ⟨107441, by rfl⟩) R214883
theorem R569267 : Reach 569267 := rs (se 1 (by rfl) ⟨426950, by rfl⟩) R853901
theorem R143383 : Reach 143383 := rs (se 1 (by rfl) ⟨107537, by rfl⟩) R215075
theorem R635201 : Reach 635201 := rs (se 2 (by rfl) ⟨238200, by rfl⟩) R476401
theorem R176513 : Reach 176513 := rs (se 2 (by rfl) ⟨66192, by rfl⟩) R132385
theorem R144011 : Reach 144011 := rs (se 1 (by rfl) ⟨108008, by rfl⟩) R216017
theorem R340631 : Reach 340631 := rs (se 1 (by rfl) ⟨255473, by rfl⟩) R510947
theorem R144139 : Reach 144139 := rs (se 1 (by rfl) ⟨108104, by rfl⟩) R216209
theorem R242507 : Reach 242507 := rs (se 1 (by rfl) ⟨181880, by rfl⟩) R363761
theorem R144281 : Reach 144281 := rs (se 2 (by rfl) ⟨54105, by rfl⟩) R108211
theorem R144409 : Reach 144409 := rs (se 2 (by rfl) ⟨54153, by rfl⟩) R108307
theorem R439427 : Reach 439427 := rs (se 1 (by rfl) ⟨329570, by rfl⟩) R659141
theorem R799895 : Reach 799895 := rs (se 1 (by rfl) ⟨599921, by rfl⟩) R1199843
theorem R308573 : Reach 308573 := rs (se 3 (by rfl) ⟨57857, by rfl⟩) R115715
theorem R374233 : Reach 374233 := rs (se 2 (by rfl) ⟨140337, by rfl⟩) R280675
theorem R144983 : Reach 144983 := rs (se 1 (by rfl) ⟨108737, by rfl⟩) R217475
theorem R145111 : Reach 145111 := rs (se 1 (by rfl) ⟨108833, by rfl⟩) R217667
theorem R1357667 : Reach 1357667 := rs (se 1 (by rfl) ⟨1018250, by rfl⟩) R2036501
theorem R112523 : Reach 112523 := rs (se 1 (by rfl) ⟨84392, by rfl⟩) R168785
theorem R210995 : Reach 210995 := rs (se 1 (by rfl) ⟨158246, by rfl⟩) R316493
theorem R1882187 : Reach 1882187 := rs (se 1 (by rfl) ⟨1411640, by rfl⟩) R2823281
theorem R243805 : Reach 243805 := rs (se 3 (by rfl) ⟨45713, by rfl⟩) R91427
theorem R112793 : Reach 112793 := rs (se 2 (by rfl) ⟨42297, by rfl⟩) R84595
theorem R637145 : Reach 637145 := rs (se 2 (by rfl) ⟨238929, by rfl⟩) R477859
theorem R145739 : Reach 145739 := rs (se 1 (by rfl) ⟨109304, by rfl⟩) R218609
theorem R244147 : Reach 244147 := rs (se 1 (by rfl) ⟨183110, by rfl⟩) R366221
theorem R145867 : Reach 145867 := rs (se 1 (by rfl) ⟨109400, by rfl⟩) R218801
theorem R211531 : Reach 211531 := rs (se 1 (by rfl) ⟨158648, by rfl⟩) R317297
theorem R965195 : Reach 965195 := rs (se 1 (by rfl) ⟨723896, by rfl⟩) R1447793
theorem R146009 : Reach 146009 := rs (se 2 (by rfl) ⟨54753, by rfl⟩) R109507
theorem R4209245 : Reach 4209245 := rs (se 3 (by rfl) ⟨789233, by rfl⟩) R1578467
theorem R440963 : Reach 440963 := rs (se 1 (by rfl) ⟨330722, by rfl⟩) R661445
theorem R211673 : Reach 211673 := rs (se 2 (by rfl) ⟨79377, by rfl⟩) R158755
theorem R309977 : Reach 309977 := rs (se 2 (by rfl) ⟨116241, by rfl⟩) R232483
theorem R146137 : Reach 146137 := rs (se 2 (by rfl) ⟨54801, by rfl⟩) R109603
theorem R178967 : Reach 178967 := rs (se 1 (by rfl) ⟨134225, by rfl⟩) R268451
theorem R179147 : Reach 179147 := rs (se 1 (by rfl) ⟨134360, by rfl⟩) R268721
theorem R146711 : Reach 146711 := rs (se 1 (by rfl) ⟨110033, by rfl⟩) R220067
theorem R474443 : Reach 474443 := rs (se 1 (by rfl) ⟨355832, by rfl⟩) R711665
theorem R245081 : Reach 245081 := rs (se 2 (by rfl) ⟨91905, by rfl⟩) R183811
theorem R146839 : Reach 146839 := rs (se 1 (by rfl) ⟨110129, by rfl⟩) R220259
theorem R212503 : Reach 212503 := rs (se 1 (by rfl) ⟨159377, by rfl⟩) R318755
theorem R310873 : Reach 310873 := rs (se 2 (by rfl) ⟨116577, by rfl⟩) R233155
theorem R114329 : Reach 114329 := rs (se 2 (by rfl) ⟨42873, by rfl⟩) R85747
theorem R1392389 : Reach 1392389 := rs (se 4 (by rfl) ⟨130536, by rfl⟩) R261073
theorem R212939 : Reach 212939 := rs (se 1 (by rfl) ⟨159704, by rfl⟩) R319409
theorem R180377 : Reach 180377 := rs (se 2 (by rfl) ⟨67641, by rfl⟩) R135283
theorem R213313 : Reach 213313 := rs (se 2 (by rfl) ⟨79992, by rfl⟩) R159985
theorem R541079 : Reach 541079 := rs (se 1 (by rfl) ⟨405809, by rfl⟩) R811619
theorem R475571 : Reach 475571 := rs (se 1 (by rfl) ⟨356678, by rfl⟩) R713357
theorem R180787 : Reach 180787 := rs (se 1 (by rfl) ⟨135590, by rfl⟩) R271181
theorem R2507395 : Reach 2507395 := rs (se 1 (by rfl) ⟨1880546, by rfl⟩) R3761093
theorem R246493 : Reach 246493 := rs (se 3 (by rfl) ⟨46217, by rfl⟩) R92435
theorem R181043 : Reach 181043 := rs (se 1 (by rfl) ⟨135782, by rfl⟩) R271565
theorem R213911 : Reach 213911 := rs (se 1 (by rfl) ⟨160433, by rfl⟩) R320867
theorem R246721 : Reach 246721 := rs (se 2 (by rfl) ⟨92520, by rfl⟩) R185041
theorem R83147 : Reach 83147 := rs (se 1 (by rfl) ⟨62360, by rfl⟩) R124721
theorem R83159 : Reach 83159 := rs (se 1 (by rfl) ⟨62369, by rfl⟩) R124739
theorem R83179 : Reach 83179 := rs (se 1 (by rfl) ⟨62384, by rfl⟩) R124769
theorem R83191 : Reach 83191 := rs (se 1 (by rfl) ⟨62393, by rfl⟩) R124787
theorem R83211 : Reach 83211 := rs (se 1 (by rfl) ⟨62408, by rfl⟩) R124817
theorem R83223 : Reach 83223 := rs (se 1 (by rfl) ⟨62417, by rfl⟩) R124835
theorem R247063 : Reach 247063 := rs (se 1 (by rfl) ⟨185297, by rfl⟩) R370595
theorem R83243 : Reach 83243 := rs (se 1 (by rfl) ⟨62432, by rfl⟩) R124865
theorem R83255 : Reach 83255 := rs (se 1 (by rfl) ⟨62441, by rfl⟩) R124883
theorem R83275 : Reach 83275 := rs (se 1 (by rfl) ⟨62456, by rfl⟩) R124913
theorem R83287 : Reach 83287 := rs (se 1 (by rfl) ⟨62465, by rfl⟩) R124931
theorem R83307 : Reach 83307 := rs (se 1 (by rfl) ⟨62480, by rfl⟩) R124961
theorem R83319 : Reach 83319 := rs (se 1 (by rfl) ⟨62489, by rfl⟩) R124979
theorem R83339 : Reach 83339 := rs (se 1 (by rfl) ⟨62504, by rfl⟩) R125009
theorem R83351 : Reach 83351 := rs (se 1 (by rfl) ⟨62513, by rfl⟩) R125027
theorem R83371 : Reach 83371 := rs (se 1 (by rfl) ⟨62528, by rfl⟩) R125057
theorem R83383 : Reach 83383 := rs (se 1 (by rfl) ⟨62537, by rfl⟩) R125075
theorem R83403 : Reach 83403 := rs (se 1 (by rfl) ⟨62552, by rfl⟩) R125105
theorem R83415 : Reach 83415 := rs (se 1 (by rfl) ⟨62561, by rfl⟩) R125123
theorem R83435 : Reach 83435 := rs (se 1 (by rfl) ⟨62576, by rfl⟩) R125153
theorem R83447 : Reach 83447 := rs (se 1 (by rfl) ⟨62585, by rfl⟩) R125171
theorem R83467 : Reach 83467 := rs (se 1 (by rfl) ⟨62600, by rfl⟩) R125201
theorem R935441 : Reach 935441 := rs (se 2 (by rfl) ⟨350790, by rfl⟩) R701581
theorem R83479 : Reach 83479 := rs (se 1 (by rfl) ⟨62609, by rfl⟩) R125219
theorem R640547 : Reach 640547 := rs (se 1 (by rfl) ⟨480410, by rfl⟩) R960821
theorem R83499 : Reach 83499 := rs (se 1 (by rfl) ⟨62624, by rfl⟩) R125249
theorem R83511 : Reach 83511 := rs (se 1 (by rfl) ⟨62633, by rfl⟩) R125267
theorem R83531 : Reach 83531 := rs (se 1 (by rfl) ⟨62648, by rfl⟩) R125297
theorem R83543 : Reach 83543 := rs (se 1 (by rfl) ⟨62657, by rfl⟩) R125315
theorem R83563 : Reach 83563 := rs (se 1 (by rfl) ⟨62672, by rfl⟩) R125345
theorem R83575 : Reach 83575 := rs (se 1 (by rfl) ⟨62681, by rfl⟩) R125363
theorem R83595 : Reach 83595 := rs (se 1 (by rfl) ⟨62696, by rfl⟩) R125393
theorem R83607 : Reach 83607 := rs (se 1 (by rfl) ⟨62705, by rfl⟩) R125411
theorem R83627 : Reach 83627 := rs (se 1 (by rfl) ⟨62720, by rfl⟩) R125441
theorem R83639 : Reach 83639 := rs (se 1 (by rfl) ⟨62729, by rfl⟩) R125459
theorem R214721 : Reach 214721 := rs (se 2 (by rfl) ⟨80520, by rfl⟩) R161041
theorem R83659 : Reach 83659 := rs (se 1 (by rfl) ⟨62744, by rfl⟩) R125489
theorem R83671 : Reach 83671 := rs (se 1 (by rfl) ⟨62753, by rfl⟩) R125507
theorem R83691 : Reach 83691 := rs (se 1 (by rfl) ⟨62768, by rfl⟩) R125537
theorem R83703 : Reach 83703 := rs (se 1 (by rfl) ⟨62777, by rfl⟩) R125555
theorem R182017 : Reach 182017 := rs (se 2 (by rfl) ⟨68256, by rfl⟩) R136513
theorem R83723 : Reach 83723 := rs (se 1 (by rfl) ⟨62792, by rfl⟩) R125585
theorem R83735 : Reach 83735 := rs (se 1 (by rfl) ⟨62801, by rfl⟩) R125603
theorem R83755 : Reach 83755 := rs (se 1 (by rfl) ⟨62816, by rfl⟩) R125633
theorem R83767 : Reach 83767 := rs (se 1 (by rfl) ⟨62825, by rfl⟩) R125651
theorem R1001281 : Reach 1001281 := rs (se 2 (by rfl) ⟨375480, by rfl⟩) R750961
theorem R83787 : Reach 83787 := rs (se 1 (by rfl) ⟨62840, by rfl⟩) R125681
theorem R83799 : Reach 83799 := rs (se 1 (by rfl) ⟨62849, by rfl⟩) R125699
theorem R83819 : Reach 83819 := rs (se 1 (by rfl) ⟨62864, by rfl⟩) R125729
theorem R83831 : Reach 83831 := rs (se 1 (by rfl) ⟨62873, by rfl⟩) R125747
theorem R83851 : Reach 83851 := rs (se 1 (by rfl) ⟨62888, by rfl⟩) R125777
theorem R83863 : Reach 83863 := rs (se 1 (by rfl) ⟨62897, by rfl⟩) R125795
theorem R83883 : Reach 83883 := rs (se 1 (by rfl) ⟨62912, by rfl⟩) R125825
theorem R83895 : Reach 83895 := rs (se 1 (by rfl) ⟨62921, by rfl⟩) R125843
theorem R83915 : Reach 83915 := rs (se 1 (by rfl) ⟨62936, by rfl⟩) R125873
theorem R83927 : Reach 83927 := rs (se 1 (by rfl) ⟨62945, by rfl⟩) R125891
theorem R247769 : Reach 247769 := rs (se 2 (by rfl) ⟨92913, by rfl⟩) R185827
theorem R83947 : Reach 83947 := rs (se 1 (by rfl) ⟨62960, by rfl⟩) R125921
theorem R83959 : Reach 83959 := rs (se 1 (by rfl) ⟨62969, by rfl⟩) R125939
theorem R83979 : Reach 83979 := rs (se 1 (by rfl) ⟨62984, by rfl⟩) R125969
theorem R83991 : Reach 83991 := rs (se 1 (by rfl) ⟨62993, by rfl⟩) R125987
theorem R84011 : Reach 84011 := rs (se 1 (by rfl) ⟨63008, by rfl⟩) R126017
theorem R84023 : Reach 84023 := rs (se 1 (by rfl) ⟨63017, by rfl⟩) R126035
theorem R84043 : Reach 84043 := rs (se 1 (by rfl) ⟨63032, by rfl⟩) R126065
theorem R84055 : Reach 84055 := rs (se 1 (by rfl) ⟨63041, by rfl⟩) R126083
theorem R542821 : Reach 542821 := rs (se 4 (by rfl) ⟨50889, by rfl⟩) R101779
theorem R84075 : Reach 84075 := rs (se 1 (by rfl) ⟨63056, by rfl⟩) R126113
theorem R84087 : Reach 84087 := rs (se 1 (by rfl) ⟨63065, by rfl⟩) R126131
theorem R84107 : Reach 84107 := rs (se 1 (by rfl) ⟨63080, by rfl⟩) R126161
theorem R84119 : Reach 84119 := rs (se 1 (by rfl) ⟨63089, by rfl⟩) R126179
theorem R84139 : Reach 84139 := rs (se 1 (by rfl) ⟨63104, by rfl⟩) R126209
theorem R84151 : Reach 84151 := rs (se 1 (by rfl) ⟨63113, by rfl⟩) R126227
theorem R84171 : Reach 84171 := rs (se 1 (by rfl) ⟨63128, by rfl⟩) R126257
theorem R84183 : Reach 84183 := rs (se 1 (by rfl) ⟨63137, by rfl⟩) R126275
theorem R215257 : Reach 215257 := rs (se 2 (by rfl) ⟨80721, by rfl⟩) R161443
theorem R84203 : Reach 84203 := rs (se 1 (by rfl) ⟨63152, by rfl⟩) R126305
theorem R84215 : Reach 84215 := rs (se 1 (by rfl) ⟨63161, by rfl⟩) R126323
theorem R84235 : Reach 84235 := rs (se 1 (by rfl) ⟨63176, by rfl⟩) R126353
theorem R739601 : Reach 739601 := rs (se 2 (by rfl) ⟨277350, by rfl⟩) R554701
theorem R84247 : Reach 84247 := rs (se 1 (by rfl) ⟨63185, by rfl⟩) R126371
theorem R84267 : Reach 84267 := rs (se 1 (by rfl) ⟨63200, by rfl⟩) R126401
theorem R84279 : Reach 84279 := rs (se 1 (by rfl) ⟨63209, by rfl⟩) R126419
theorem R280907 : Reach 280907 := rs (se 1 (by rfl) ⟨210680, by rfl⟩) R421361
theorem R84299 : Reach 84299 := rs (se 1 (by rfl) ⟨63224, by rfl⟩) R126449
theorem R84311 : Reach 84311 := rs (se 1 (by rfl) ⟨63233, by rfl⟩) R126467
theorem R84331 : Reach 84331 := rs (se 1 (by rfl) ⟨63248, by rfl⟩) R126497
theorem R84343 : Reach 84343 := rs (se 1 (by rfl) ⟨63257, by rfl⟩) R126515
theorem R84363 : Reach 84363 := rs (se 1 (by rfl) ⟨63272, by rfl⟩) R126545
theorem R84375 : Reach 84375 := rs (se 1 (by rfl) ⟨63281, by rfl⟩) R126563
theorem R84395 : Reach 84395 := rs (se 1 (by rfl) ⟨63296, by rfl⟩) R126593
theorem R444851 : Reach 444851 := rs (se 1 (by rfl) ⟨333638, by rfl⟩) R667277
theorem R84407 : Reach 84407 := rs (se 1 (by rfl) ⟨63305, by rfl⟩) R126611
theorem R84427 : Reach 84427 := rs (se 1 (by rfl) ⟨63320, by rfl⟩) R126641
theorem R84439 : Reach 84439 := rs (se 1 (by rfl) ⟨63329, by rfl⟩) R126659
theorem R84459 : Reach 84459 := rs (se 1 (by rfl) ⟨63344, by rfl⟩) R126689
theorem R84471 : Reach 84471 := rs (se 1 (by rfl) ⟨63353, by rfl⟩) R126707
theorem R84491 : Reach 84491 := rs (se 1 (by rfl) ⟨63368, by rfl⟩) R126737
theorem R84503 : Reach 84503 := rs (se 1 (by rfl) ⟨63377, by rfl⟩) R126755
theorem R84523 : Reach 84523 := rs (se 1 (by rfl) ⟨63392, by rfl⟩) R126785
theorem R84535 : Reach 84535 := rs (se 1 (by rfl) ⟨63401, by rfl⟩) R126803
theorem R84555 : Reach 84555 := rs (se 1 (by rfl) ⟨63416, by rfl⟩) R126833
theorem R84567 : Reach 84567 := rs (se 1 (by rfl) ⟨63425, by rfl⟩) R126851
theorem R117335 : Reach 117335 := rs (se 1 (by rfl) ⟨88001, by rfl⟩) R176003
theorem R281177 : Reach 281177 := rs (se 2 (by rfl) ⟨105441, by rfl⟩) R210883
theorem R84587 : Reach 84587 := rs (se 1 (by rfl) ⟨63440, by rfl⟩) R126881
theorem R84599 : Reach 84599 := rs (se 1 (by rfl) ⟨63449, by rfl⟩) R126899
theorem R84619 : Reach 84619 := rs (se 1 (by rfl) ⟨63464, by rfl⟩) R126929
theorem R84631 : Reach 84631 := rs (se 1 (by rfl) ⟨63473, by rfl⟩) R126947
theorem R84651 : Reach 84651 := rs (se 1 (by rfl) ⟨63488, by rfl⟩) R126977
theorem R84663 : Reach 84663 := rs (se 1 (by rfl) ⟨63497, by rfl⟩) R126995
theorem R84683 : Reach 84683 := rs (se 1 (by rfl) ⟨63512, by rfl⟩) R127025
theorem R84695 : Reach 84695 := rs (se 1 (by rfl) ⟨63521, by rfl⟩) R127043
theorem R84715 : Reach 84715 := rs (se 1 (by rfl) ⟨63536, by rfl⟩) R127073
theorem R84727 : Reach 84727 := rs (se 1 (by rfl) ⟨63545, by rfl⟩) R127091
theorem R84747 : Reach 84747 := rs (se 1 (by rfl) ⟨63560, by rfl⟩) R127121
theorem R84759 : Reach 84759 := rs (se 1 (by rfl) ⟨63569, by rfl⟩) R127139
theorem R84779 : Reach 84779 := rs (se 1 (by rfl) ⟨63584, by rfl⟩) R127169
theorem R84791 : Reach 84791 := rs (se 1 (by rfl) ⟨63593, by rfl⟩) R127187
theorem R84811 : Reach 84811 := rs (se 1 (by rfl) ⟨63608, by rfl⟩) R127217
theorem R84823 : Reach 84823 := rs (se 1 (by rfl) ⟨63617, by rfl⟩) R127235
theorem R84843 : Reach 84843 := rs (se 1 (by rfl) ⟨63632, by rfl⟩) R127265
theorem R84855 : Reach 84855 := rs (se 1 (by rfl) ⟨63641, by rfl⟩) R127283
theorem R84875 : Reach 84875 := rs (se 1 (by rfl) ⟨63656, by rfl⟩) R127313
theorem R84887 : Reach 84887 := rs (se 1 (by rfl) ⟨63665, by rfl⟩) R127331
theorem R84907 : Reach 84907 := rs (se 1 (by rfl) ⟨63680, by rfl⟩) R127361
theorem R84919 : Reach 84919 := rs (se 1 (by rfl) ⟨63689, by rfl⟩) R127379
theorem R84939 : Reach 84939 := rs (se 1 (by rfl) ⟨63704, by rfl⟩) R127409
theorem R84951 : Reach 84951 := rs (se 1 (by rfl) ⟨63713, by rfl⟩) R127427
theorem R84971 : Reach 84971 := rs (se 1 (by rfl) ⟨63728, by rfl⟩) R127457
theorem R84983 : Reach 84983 := rs (se 1 (by rfl) ⟨63737, by rfl⟩) R127475
theorem R85003 : Reach 85003 := rs (se 1 (by rfl) ⟨63752, by rfl⟩) R127505
theorem R85015 : Reach 85015 := rs (se 1 (by rfl) ⟨63761, by rfl⟩) R127523
theorem R85035 : Reach 85035 := rs (se 1 (by rfl) ⟨63776, by rfl⟩) R127553
theorem R85047 : Reach 85047 := rs (se 1 (by rfl) ⟨63785, by rfl⟩) R127571
theorem R85067 : Reach 85067 := rs (se 1 (by rfl) ⟨63800, by rfl⟩) R127601
theorem R85079 : Reach 85079 := rs (se 1 (by rfl) ⟨63809, by rfl⟩) R127619
theorem R85099 : Reach 85099 := rs (se 1 (by rfl) ⟨63824, by rfl⟩) R127649
theorem R85111 : Reach 85111 := rs (se 1 (by rfl) ⟨63833, by rfl⟩) R127667
theorem R85131 : Reach 85131 := rs (se 1 (by rfl) ⟨63848, by rfl⟩) R127697
theorem R150679 : Reach 150679 := rs (se 1 (by rfl) ⟨113009, by rfl⟩) R226019
theorem R85143 : Reach 85143 := rs (se 1 (by rfl) ⟨63857, by rfl⟩) R127715
theorem R85163 : Reach 85163 := rs (se 1 (by rfl) ⟨63872, by rfl⟩) R127745
theorem R85175 : Reach 85175 := rs (se 1 (by rfl) ⟨63881, by rfl⟩) R127763
theorem R85195 : Reach 85195 := rs (se 1 (by rfl) ⟨63896, by rfl⟩) R127793
theorem R85207 : Reach 85207 := rs (se 1 (by rfl) ⟨63905, by rfl⟩) R127811
theorem R85227 : Reach 85227 := rs (se 1 (by rfl) ⟨63920, by rfl⟩) R127841
theorem R85239 : Reach 85239 := rs (se 1 (by rfl) ⟨63929, by rfl⟩) R127859
theorem R85259 : Reach 85259 := rs (se 1 (by rfl) ⟨63944, by rfl⟩) R127889
theorem R281879 : Reach 281879 := rs (se 1 (by rfl) ⟨211409, by rfl⟩) R422819
theorem R85271 : Reach 85271 := rs (se 1 (by rfl) ⟨63953, by rfl⟩) R127907
theorem R85291 : Reach 85291 := rs (se 1 (by rfl) ⟨63968, by rfl⟩) R127937
theorem R216371 : Reach 216371 := rs (se 1 (by rfl) ⟨162278, by rfl⟩) R324557
theorem R85303 : Reach 85303 := rs (se 1 (by rfl) ⟨63977, by rfl⟩) R127955
theorem R85323 : Reach 85323 := rs (se 1 (by rfl) ⟨63992, by rfl⟩) R127985
theorem R85335 : Reach 85335 := rs (se 1 (by rfl) ⟨64001, by rfl⟩) R128003
theorem R85355 : Reach 85355 := rs (se 1 (by rfl) ⟨64016, by rfl⟩) R128033
theorem R85367 : Reach 85367 := rs (se 1 (by rfl) ⟨64025, by rfl⟩) R128051
theorem R85387 : Reach 85387 := rs (se 1 (by rfl) ⟨64040, by rfl⟩) R128081
theorem R85399 : Reach 85399 := rs (se 1 (by rfl) ⟨64049, by rfl⟩) R128099
theorem R85419 : Reach 85419 := rs (se 1 (by rfl) ⟨64064, by rfl⟩) R128129
theorem R85431 : Reach 85431 := rs (se 1 (by rfl) ⟨64073, by rfl⟩) R128147
theorem R85451 : Reach 85451 := rs (se 1 (by rfl) ⟨64088, by rfl⟩) R128177
theorem R85463 : Reach 85463 := rs (se 1 (by rfl) ⟨64097, by rfl⟩) R128195
theorem R85483 : Reach 85483 := rs (se 1 (by rfl) ⟨64112, by rfl⟩) R128225
theorem R85495 : Reach 85495 := rs (se 1 (by rfl) ⟨64121, by rfl⟩) R128243
theorem R85515 : Reach 85515 := rs (se 1 (by rfl) ⟨64136, by rfl⟩) R128273
theorem R85527 : Reach 85527 := rs (se 1 (by rfl) ⟨64145, by rfl⟩) R128291
theorem R85547 : Reach 85547 := rs (se 1 (by rfl) ⟨64160, by rfl⟩) R128321
theorem R85559 : Reach 85559 := rs (se 1 (by rfl) ⟨64169, by rfl⟩) R128339
theorem R85579 : Reach 85579 := rs (se 1 (by rfl) ⟨64184, by rfl⟩) R128369
theorem R85591 : Reach 85591 := rs (se 1 (by rfl) ⟨64193, by rfl⟩) R128387
theorem R216665 : Reach 216665 := rs (se 2 (by rfl) ⟨81249, by rfl⟩) R162499
theorem R85611 : Reach 85611 := rs (se 1 (by rfl) ⟨64208, by rfl⟩) R128417
theorem R85623 : Reach 85623 := rs (se 1 (by rfl) ⟨64217, by rfl⟩) R128435
theorem R85643 : Reach 85643 := rs (se 1 (by rfl) ⟨64232, by rfl⟩) R128465
theorem R85655 : Reach 85655 := rs (se 1 (by rfl) ⟨64241, by rfl⟩) R128483
theorem R85675 : Reach 85675 := rs (se 1 (by rfl) ⟨64256, by rfl⟩) R128513
theorem R85687 : Reach 85687 := rs (se 1 (by rfl) ⟨64265, by rfl⟩) R128531
theorem R85707 : Reach 85707 := rs (se 1 (by rfl) ⟨64280, by rfl⟩) R128561
theorem R85719 : Reach 85719 := rs (se 1 (by rfl) ⟨64289, by rfl⟩) R128579
theorem R85739 : Reach 85739 := rs (se 1 (by rfl) ⟨64304, by rfl⟩) R128609
theorem R85751 : Reach 85751 := rs (se 1 (by rfl) ⟨64313, by rfl⟩) R128627
theorem R85771 : Reach 85771 := rs (se 1 (by rfl) ⟨64328, by rfl⟩) R128657
theorem R85783 : Reach 85783 := rs (se 1 (by rfl) ⟨64337, by rfl⟩) R128675
theorem R85803 : Reach 85803 := rs (se 1 (by rfl) ⟨64352, by rfl⟩) R128705
theorem R282419 : Reach 282419 := rs (se 1 (by rfl) ⟨211814, by rfl⟩) R423629
theorem R85815 : Reach 85815 := rs (se 1 (by rfl) ⟨64361, by rfl⟩) R128723
theorem R85835 : Reach 85835 := rs (se 1 (by rfl) ⟨64376, by rfl⟩) R128753
theorem R85847 : Reach 85847 := rs (se 1 (by rfl) ⟨64385, by rfl⟩) R128771
theorem R184153 : Reach 184153 := rs (se 2 (by rfl) ⟨69057, by rfl⟩) R138115
theorem R85867 : Reach 85867 := rs (se 1 (by rfl) ⟨64400, by rfl⟩) R128801
theorem R85879 : Reach 85879 := rs (se 1 (by rfl) ⟨64409, by rfl⟩) R128819
theorem R85899 : Reach 85899 := rs (se 1 (by rfl) ⟨64424, by rfl⟩) R128849
theorem R85911 : Reach 85911 := rs (se 1 (by rfl) ⟨64433, by rfl⟩) R128867
theorem R85931 : Reach 85931 := rs (se 1 (by rfl) ⟨64448, by rfl⟩) R128897
theorem R85943 : Reach 85943 := rs (se 1 (by rfl) ⟨64457, by rfl⟩) R128915
theorem R85963 : Reach 85963 := rs (se 1 (by rfl) ⟨64472, by rfl⟩) R128945
theorem R85975 : Reach 85975 := rs (se 1 (by rfl) ⟨64481, by rfl⟩) R128963
theorem R85995 : Reach 85995 := rs (se 1 (by rfl) ⟨64496, by rfl⟩) R128993
theorem R86007 : Reach 86007 := rs (se 1 (by rfl) ⟨64505, by rfl⟩) R129011
theorem R86027 : Reach 86027 := rs (se 1 (by rfl) ⟨64520, by rfl⟩) R129041
theorem R86039 : Reach 86039 := rs (se 1 (by rfl) ⟨64529, by rfl⟩) R129059
theorem R86059 : Reach 86059 := rs (se 1 (by rfl) ⟨64544, by rfl⟩) R129089
theorem R86071 : Reach 86071 := rs (se 1 (by rfl) ⟨64553, by rfl⟩) R129107
theorem R282689 : Reach 282689 := rs (se 2 (by rfl) ⟨106008, by rfl⟩) R212017
theorem R86091 : Reach 86091 := rs (se 1 (by rfl) ⟨64568, by rfl⟩) R129137
theorem R86103 : Reach 86103 := rs (se 1 (by rfl) ⟨64577, by rfl⟩) R129155
theorem R86123 : Reach 86123 := rs (se 1 (by rfl) ⟨64592, by rfl⟩) R129185
theorem R86135 : Reach 86135 := rs (se 1 (by rfl) ⟨64601, by rfl⟩) R129203
theorem R872579 : Reach 872579 := rs (se 1 (by rfl) ⟨654434, by rfl⟩) R1308869
theorem R86155 : Reach 86155 := rs (se 1 (by rfl) ⟨64616, by rfl⟩) R129233
theorem R86167 : Reach 86167 := rs (se 1 (by rfl) ⟨64625, by rfl⟩) R129251
theorem R86187 : Reach 86187 := rs (se 1 (by rfl) ⟨64640, by rfl⟩) R129281
theorem R86199 : Reach 86199 := rs (se 1 (by rfl) ⟨64649, by rfl⟩) R129299
theorem R86219 : Reach 86219 := rs (se 1 (by rfl) ⟨64664, by rfl⟩) R129329
theorem R86231 : Reach 86231 := rs (se 1 (by rfl) ⟨64673, by rfl⟩) R129347
theorem R151769 : Reach 151769 := rs (se 2 (by rfl) ⟨56913, by rfl⟩) R113827
theorem R86251 : Reach 86251 := rs (se 1 (by rfl) ⟨64688, by rfl⟩) R129377
theorem R86263 : Reach 86263 := rs (se 1 (by rfl) ⟨64697, by rfl⟩) R129395
theorem R86283 : Reach 86283 := rs (se 1 (by rfl) ⟨64712, by rfl⟩) R129425
theorem R86295 : Reach 86295 := rs (se 1 (by rfl) ⟨64721, by rfl⟩) R129443
theorem R86315 : Reach 86315 := rs (se 1 (by rfl) ⟨64736, by rfl⟩) R129473
theorem R86327 : Reach 86327 := rs (se 1 (by rfl) ⟨64745, by rfl⟩) R129491
theorem R86347 : Reach 86347 := rs (se 1 (by rfl) ⟨64760, by rfl⟩) R129521
theorem R86359 : Reach 86359 := rs (se 1 (by rfl) ⟨64769, by rfl⟩) R129539
theorem R86379 : Reach 86379 := rs (se 1 (by rfl) ⟨64784, by rfl⟩) R129569
theorem R86391 : Reach 86391 := rs (se 1 (by rfl) ⟨64793, by rfl⟩) R129587
theorem R86411 : Reach 86411 := rs (se 1 (by rfl) ⟨64808, by rfl⟩) R129617
theorem R86423 : Reach 86423 := rs (se 1 (by rfl) ⟨64817, by rfl⟩) R129635
theorem R86443 : Reach 86443 := rs (se 1 (by rfl) ⟨64832, by rfl⟩) R129665
theorem R86455 : Reach 86455 := rs (se 1 (by rfl) ⟨64841, by rfl⟩) R129683
theorem R86475 : Reach 86475 := rs (se 1 (by rfl) ⟨64856, by rfl⟩) R129713
theorem R86487 : Reach 86487 := rs (se 1 (by rfl) ⟨64865, by rfl⟩) R129731
theorem R86507 : Reach 86507 := rs (se 1 (by rfl) ⟨64880, by rfl⟩) R129761
theorem R86519 : Reach 86519 := rs (se 1 (by rfl) ⟨64889, by rfl⟩) R129779
theorem R86539 : Reach 86539 := rs (se 1 (by rfl) ⟨64904, by rfl⟩) R129809
theorem R86551 : Reach 86551 := rs (se 1 (by rfl) ⟨64913, by rfl⟩) R129827
theorem R86571 : Reach 86571 := rs (se 1 (by rfl) ⟨64928, by rfl⟩) R129857
theorem R86583 : Reach 86583 := rs (se 1 (by rfl) ⟨64937, by rfl⟩) R129875
theorem R86603 : Reach 86603 := rs (se 1 (by rfl) ⟨64952, by rfl⟩) R129905
theorem R86615 : Reach 86615 := rs (se 1 (by rfl) ⟨64961, by rfl⟩) R129923
theorem R283229 : Reach 283229 := rs (se 3 (by rfl) ⟨53105, by rfl⟩) R106211
theorem R86635 : Reach 86635 := rs (se 1 (by rfl) ⟨64976, by rfl⟩) R129953
theorem R86647 : Reach 86647 := rs (se 1 (by rfl) ⟨64985, by rfl⟩) R129971
theorem R86667 : Reach 86667 := rs (se 1 (by rfl) ⟨65000, by rfl⟩) R130001
theorem R86679 : Reach 86679 := rs (se 1 (by rfl) ⟨65009, by rfl⟩) R130019
theorem R86699 : Reach 86699 := rs (se 1 (by rfl) ⟨65024, by rfl⟩) R130049
theorem R610993 : Reach 610993 := rs (se 2 (by rfl) ⟨229122, by rfl⟩) R458245
theorem R86711 : Reach 86711 := rs (se 1 (by rfl) ⟨65033, by rfl⟩) R130067
theorem R86731 : Reach 86731 := rs (se 1 (by rfl) ⟨65048, by rfl⟩) R130097
theorem R86743 : Reach 86743 := rs (se 1 (by rfl) ⟨65057, by rfl⟩) R130115
theorem R86763 : Reach 86763 := rs (se 1 (by rfl) ⟨65072, by rfl⟩) R130145
theorem R86775 : Reach 86775 := rs (se 1 (by rfl) ⟨65081, by rfl⟩) R130163
theorem R86795 : Reach 86795 := rs (se 1 (by rfl) ⟨65096, by rfl⟩) R130193
theorem R86807 : Reach 86807 := rs (se 1 (by rfl) ⟨65105, by rfl⟩) R130211
theorem R86827 : Reach 86827 := rs (se 1 (by rfl) ⟨65120, by rfl⟩) R130241
theorem R86839 : Reach 86839 := rs (se 1 (by rfl) ⟨65129, by rfl⟩) R130259
theorem R86859 : Reach 86859 := rs (se 1 (by rfl) ⟨65144, by rfl⟩) R130289
theorem R86871 : Reach 86871 := rs (se 1 (by rfl) ⟨65153, by rfl⟩) R130307
theorem R86891 : Reach 86891 := rs (se 1 (by rfl) ⟨65168, by rfl⟩) R130337
theorem R86903 : Reach 86903 := rs (se 1 (by rfl) ⟨65177, by rfl⟩) R130355
theorem R86923 : Reach 86923 := rs (se 1 (by rfl) ⟨65192, by rfl⟩) R130385
theorem R86935 : Reach 86935 := rs (se 1 (by rfl) ⟨65201, by rfl⟩) R130403
theorem R86955 : Reach 86955 := rs (se 1 (by rfl) ⟨65216, by rfl⟩) R130433
theorem R86967 : Reach 86967 := rs (se 1 (by rfl) ⟨65225, by rfl⟩) R130451
theorem R86987 : Reach 86987 := rs (se 1 (by rfl) ⟨65240, by rfl⟩) R130481
theorem R86999 : Reach 86999 := rs (se 1 (by rfl) ⟨65249, by rfl⟩) R130499
theorem R87019 : Reach 87019 := rs (se 1 (by rfl) ⟨65264, by rfl⟩) R130529
theorem R87031 : Reach 87031 := rs (se 1 (by rfl) ⟨65273, by rfl⟩) R130547
theorem R87051 : Reach 87051 := rs (se 1 (by rfl) ⟨65288, by rfl⟩) R130577
theorem R87063 : Reach 87063 := rs (se 1 (by rfl) ⟨65297, by rfl⟩) R130595
theorem R87083 : Reach 87083 := rs (se 1 (by rfl) ⟨65312, by rfl⟩) R130625
theorem R250931 : Reach 250931 := rs (se 1 (by rfl) ⟨188198, by rfl⟩) R376397
theorem R87095 : Reach 87095 := rs (se 1 (by rfl) ⟨65321, by rfl⟩) R130643
theorem R87115 : Reach 87115 := rs (se 1 (by rfl) ⟨65336, by rfl⟩) R130673
theorem R87127 : Reach 87127 := rs (se 1 (by rfl) ⟨65345, by rfl⟩) R130691
theorem R251059 : Reach 251059 := rs (se 1 (by rfl) ⟨188294, by rfl⟩) R376589
theorem R218315 : Reach 218315 := rs (se 1 (by rfl) ⟨163736, by rfl⟩) R327473
theorem R120217 : Reach 120217 := rs (se 2 (by rfl) ⟨45081, by rfl⟩) R90163
theorem R382429 : Reach 382429 := rs (se 3 (by rfl) ⟨71705, by rfl⟩) R143411
theorem R316979 : Reach 316979 := rs (se 1 (by rfl) ⟨237734, by rfl⟩) R475469
theorem R316993 : Reach 316993 := rs (se 2 (by rfl) ⟨118872, by rfl⟩) R237745
theorem R218803 : Reach 218803 := rs (se 1 (by rfl) ⟨164102, by rfl⟩) R328205
theorem R284363 : Reach 284363 := rs (se 1 (by rfl) ⟨213272, by rfl⟩) R426545
theorem R4085453 : Reach 4085453 := rs (se 3 (by rfl) ⟨766022, by rfl⟩) R1532045
theorem R349913 : Reach 349913 := rs (se 2 (by rfl) ⟨131217, by rfl⟩) R262435
theorem R481241 : Reach 481241 := rs (se 2 (by rfl) ⟨180465, by rfl⟩) R360931
theorem R284633 : Reach 284633 := rs (se 2 (by rfl) ⟨106737, by rfl⟩) R213475
theorem R153751 : Reach 153751 := rs (se 1 (by rfl) ⟨115313, by rfl⟩) R230627
theorem R219287 : Reach 219287 := rs (se 1 (by rfl) ⟨164465, by rfl⟩) R328931
theorem R285335 : Reach 285335 := rs (se 1 (by rfl) ⟨214001, by rfl⟩) R428003
theorem R187073 : Reach 187073 := rs (se 2 (by rfl) ⟨70152, by rfl⟩) R140305
theorem R645893 : Reach 645893 := rs (se 4 (by rfl) ⟨60552, by rfl⟩) R121105
theorem R219955 : Reach 219955 := rs (se 1 (by rfl) ⟨164966, by rfl⟩) R329933
theorem R121675 : Reach 121675 := rs (se 1 (by rfl) ⟨91256, by rfl⟩) R182513
theorem R187289 : Reach 187289 := rs (se 2 (by rfl) ⟨70233, by rfl⟩) R140467
theorem R220097 : Reach 220097 := rs (se 2 (by rfl) ⟨82536, by rfl⟩) R165073
theorem R187379 : Reach 187379 := rs (se 1 (by rfl) ⟨140534, by rfl⟩) R281069
theorem R187415 : Reach 187415 := rs (se 1 (by rfl) ⟨140561, by rfl⟩) R281123
theorem R285875 : Reach 285875 := rs (se 1 (by rfl) ⟨214406, by rfl⟩) R428813
theorem R187595 : Reach 187595 := rs (se 1 (by rfl) ⟨140696, by rfl⟩) R281393
theorem R187649 : Reach 187649 := rs (se 2 (by rfl) ⟨70368, by rfl⟩) R140737
theorem R613763 : Reach 613763 := rs (se 1 (by rfl) ⟨460322, by rfl⟩) R920645
theorem R286145 : Reach 286145 := rs (se 2 (by rfl) ⟨107304, by rfl⟩) R214609
theorem R318923 : Reach 318923 := rs (se 1 (by rfl) ⟨239192, by rfl⟩) R478385
theorem R187865 : Reach 187865 := rs (se 2 (by rfl) ⟨70449, by rfl⟩) R140899
theorem R318937 : Reach 318937 := rs (se 2 (by rfl) ⟨119601, by rfl⟩) R239203
theorem R1138211 : Reach 1138211 := rs (se 1 (by rfl) ⟨853658, by rfl⟩) R1707317
theorem R187955 : Reach 187955 := rs (se 1 (by rfl) ⟨140966, by rfl⟩) R281933
theorem R187991 : Reach 187991 := rs (se 1 (by rfl) ⟨140993, by rfl⟩) R281987
theorem R155351 : Reach 155351 := rs (se 1 (by rfl) ⟨116513, by rfl⟩) R233027
theorem R188171 : Reach 188171 := rs (se 1 (by rfl) ⟨141128, by rfl⟩) R282257
theorem R188225 : Reach 188225 := rs (se 2 (by rfl) ⟨70584, by rfl⟩) R141169
theorem R286685 : Reach 286685 := rs (se 3 (by rfl) ⟨53753, by rfl⟩) R107507
theorem R188441 : Reach 188441 := rs (se 2 (by rfl) ⟨70665, by rfl⟩) R141331
theorem R122905 : Reach 122905 := rs (se 2 (by rfl) ⟨46089, by rfl⟩) R92179
theorem R188531 : Reach 188531 := rs (se 1 (by rfl) ⟨141398, by rfl⟩) R282797
theorem R188567 : Reach 188567 := rs (se 1 (by rfl) ⟨141425, by rfl⟩) R282851
theorem R811309 : Reach 811309 := rs (se 3 (by rfl) ⟨152120, by rfl⟩) R304241
theorem R188747 : Reach 188747 := rs (se 1 (by rfl) ⟨141560, by rfl⟩) R283121
theorem R450917 : Reach 450917 := rs (se 4 (by rfl) ⟨42273, by rfl⟩) R84547
theorem R680293 : Reach 680293 := rs (se 4 (by rfl) ⟨63777, by rfl⟩) R127555
theorem R188801 : Reach 188801 := rs (se 2 (by rfl) ⟨70800, by rfl⟩) R141601
theorem R319895 : Reach 319895 := rs (se 1 (by rfl) ⟨239921, by rfl⟩) R479843
theorem R90667 : Reach 90667 := rs (se 1 (by rfl) ⟨68000, by rfl⟩) R136001
theorem R189017 : Reach 189017 := rs (se 2 (by rfl) ⟨70881, by rfl⟩) R141763
theorem R189107 : Reach 189107 := rs (se 1 (by rfl) ⟨141830, by rfl⟩) R283661
theorem R189143 : Reach 189143 := rs (se 1 (by rfl) ⟨141857, by rfl⟩) R283715
theorem R156439 : Reach 156439 := rs (se 1 (by rfl) ⟨117329, by rfl⟩) R234659
theorem R615269 : Reach 615269 := rs (se 4 (by rfl) ⟨57681, by rfl⟩) R115363
theorem R189323 : Reach 189323 := rs (se 1 (by rfl) ⟨141992, by rfl⟩) R283985
theorem R189377 : Reach 189377 := rs (se 2 (by rfl) ⟨71016, by rfl⟩) R142033
theorem R287819 : Reach 287819 := rs (se 1 (by rfl) ⟨215864, by rfl⟩) R431729
theorem R287837 : Reach 287837 := rs (se 3 (by rfl) ⟨53969, by rfl⟩) R107939
theorem R648323 : Reach 648323 := rs (se 1 (by rfl) ⟨486242, by rfl⟩) R972485
theorem R189593 : Reach 189593 := rs (se 2 (by rfl) ⟨71097, by rfl⟩) R142195
theorem R189683 : Reach 189683 := rs (se 1 (by rfl) ⟨142262, by rfl⟩) R284525
theorem R189719 : Reach 189719 := rs (se 1 (by rfl) ⟨142289, by rfl⟩) R284579
theorem R288089 : Reach 288089 := rs (se 2 (by rfl) ⟨108033, by rfl⟩) R216067
theorem R189899 : Reach 189899 := rs (se 1 (by rfl) ⟨142424, by rfl⟩) R284849
theorem R189953 : Reach 189953 := rs (se 2 (by rfl) ⟨71232, by rfl⟩) R142465
theorem R321155 : Reach 321155 := rs (se 1 (by rfl) ⟨240866, by rfl⟩) R481733
theorem R190169 : Reach 190169 := rs (se 2 (by rfl) ⟨71313, by rfl⟩) R142627
theorem R124697 : Reach 124697 := rs (se 2 (by rfl) ⟨46761, by rfl⟩) R93523
theorem R583469 : Reach 583469 := rs (se 3 (by rfl) ⟨109400, by rfl⟩) R218801
theorem R190259 : Reach 190259 := rs (se 1 (by rfl) ⟨142694, by rfl⟩) R285389
theorem R190295 : Reach 190295 := rs (se 1 (by rfl) ⟨142721, by rfl⟩) R285443
theorem R681821 : Reach 681821 := rs (se 3 (by rfl) ⟨127841, by rfl⟩) R255683
theorem R124811 : Reach 124811 := rs (se 1 (by rfl) ⟨93608, by rfl⟩) R187217
theorem R124823 : Reach 124823 := rs (se 1 (by rfl) ⟨93617, by rfl⟩) R187235
theorem R124889 : Reach 124889 := rs (se 2 (by rfl) ⟨46833, by rfl⟩) R93667
theorem R190475 : Reach 190475 := rs (se 1 (by rfl) ⟨142856, by rfl⟩) R285713
theorem R288791 : Reach 288791 := rs (se 1 (by rfl) ⟨216593, by rfl⟩) R433187
theorem R190529 : Reach 190529 := rs (se 2 (by rfl) ⟨71448, by rfl⟩) R142897
theorem R125003 : Reach 125003 := rs (se 1 (by rfl) ⟨93752, by rfl⟩) R187505
theorem R125015 : Reach 125015 := rs (se 1 (by rfl) ⟨93761, by rfl⟩) R187523
theorem R125081 : Reach 125081 := rs (se 2 (by rfl) ⟨46905, by rfl⟩) R93811
theorem R223411 : Reach 223411 := rs (se 1 (by rfl) ⟨167558, by rfl⟩) R335117
theorem R157889 : Reach 157889 := rs (se 2 (by rfl) ⟨59208, by rfl⟩) R118417
theorem R715013 : Reach 715013 := rs (se 4 (by rfl) ⟨67032, by rfl⟩) R134065
theorem R125195 : Reach 125195 := rs (se 1 (by rfl) ⟨93896, by rfl⟩) R187793
theorem R125207 : Reach 125207 := rs (se 1 (by rfl) ⟨93905, by rfl⟩) R187811
theorem R190745 : Reach 190745 := rs (se 2 (by rfl) ⟨71529, by rfl⟩) R143059
theorem R158041 : Reach 158041 := rs (se 2 (by rfl) ⟨59265, by rfl⟩) R118531
theorem R125273 : Reach 125273 := rs (se 2 (by rfl) ⟨46977, by rfl⟩) R93955
theorem R190835 : Reach 190835 := rs (se 1 (by rfl) ⟨143126, by rfl⟩) R286253
theorem R190871 : Reach 190871 := rs (se 1 (by rfl) ⟨143153, by rfl⟩) R286307
theorem R125387 : Reach 125387 := rs (se 1 (by rfl) ⟨94040, by rfl⟩) R188081
theorem R125399 : Reach 125399 := rs (se 1 (by rfl) ⟨94049, by rfl⟩) R188099
theorem R125465 : Reach 125465 := rs (se 2 (by rfl) ⟨47049, by rfl⟩) R94099
theorem R289331 : Reach 289331 := rs (se 1 (by rfl) ⟨216998, by rfl⟩) R433997
theorem R191051 : Reach 191051 := rs (se 1 (by rfl) ⟨143288, by rfl⟩) R286577
theorem R191105 : Reach 191105 := rs (se 2 (by rfl) ⟨71664, by rfl⟩) R143329
theorem R125579 : Reach 125579 := rs (se 1 (by rfl) ⟨94184, by rfl⟩) R188369
theorem R125591 : Reach 125591 := rs (se 1 (by rfl) ⟨94193, by rfl⟩) R188387
theorem R125657 : Reach 125657 := rs (se 2 (by rfl) ⟨47121, by rfl⟩) R94243
theorem R92971 : Reach 92971 := rs (se 1 (by rfl) ⟨69728, by rfl⟩) R139457
theorem R289601 : Reach 289601 := rs (se 2 (by rfl) ⟨108600, by rfl⟩) R217201
theorem R125771 : Reach 125771 := rs (se 1 (by rfl) ⟨94328, by rfl⟩) R188657
theorem R125783 : Reach 125783 := rs (se 1 (by rfl) ⟨94337, by rfl⟩) R188675
theorem R191321 : Reach 191321 := rs (se 2 (by rfl) ⟨71745, by rfl⟩) R143491
theorem R125849 : Reach 125849 := rs (se 2 (by rfl) ⟨47193, by rfl⟩) R94387
theorem R191411 : Reach 191411 := rs (se 1 (by rfl) ⟨143558, by rfl⟩) R287117
theorem R191447 : Reach 191447 := rs (se 1 (by rfl) ⟨143585, by rfl⟩) R287171
theorem R125963 : Reach 125963 := rs (se 1 (by rfl) ⟨94472, by rfl⟩) R188945
theorem R125975 : Reach 125975 := rs (se 1 (by rfl) ⟨94481, by rfl⟩) R188963
theorem R355373 : Reach 355373 := rs (se 3 (by rfl) ⟨66632, by rfl⟩) R133265
theorem R126041 : Reach 126041 := rs (se 2 (by rfl) ⟨47265, by rfl⟩) R94531
theorem R191627 : Reach 191627 := rs (se 1 (by rfl) ⟨143720, by rfl⟩) R287441
theorem R191681 : Reach 191681 := rs (se 2 (by rfl) ⟨71880, by rfl⟩) R143761
theorem R126155 : Reach 126155 := rs (se 1 (by rfl) ⟨94616, by rfl⟩) R189233
theorem R126167 : Reach 126167 := rs (se 1 (by rfl) ⟨94625, by rfl⟩) R189251
theorem R584921 : Reach 584921 := rs (se 2 (by rfl) ⟨219345, by rfl⟩) R438691
theorem R126233 : Reach 126233 := rs (se 2 (by rfl) ⟨47337, by rfl⟩) R94675
theorem R290137 : Reach 290137 := rs (se 2 (by rfl) ⟨108801, by rfl⟩) R217603
theorem R290141 : Reach 290141 := rs (se 3 (by rfl) ⟨54401, by rfl⟩) R108803
theorem R93559 : Reach 93559 := rs (se 1 (by rfl) ⟨70169, by rfl⟩) R140339
theorem R126347 : Reach 126347 := rs (se 1 (by rfl) ⟨94760, by rfl⟩) R189521
theorem R7925141 : Reach 7925141 := rs (se 6 (by rfl) ⟨185745, by rfl⟩) R371491
theorem R126359 : Reach 126359 := rs (se 1 (by rfl) ⟨94769, by rfl⟩) R189539
theorem R191897 : Reach 191897 := rs (se 2 (by rfl) ⟨71961, by rfl⟩) R143923
theorem R126425 : Reach 126425 := rs (se 2 (by rfl) ⟨47409, by rfl⟩) R94819
theorem R191987 : Reach 191987 := rs (se 1 (by rfl) ⟨143990, by rfl⟩) R287981
theorem R192023 : Reach 192023 := rs (se 1 (by rfl) ⟨144017, by rfl⟩) R288035
theorem R93739 : Reach 93739 := rs (se 1 (by rfl) ⟨70304, by rfl⟩) R140609
theorem R126539 : Reach 126539 := rs (se 1 (by rfl) ⟨94904, by rfl⟩) R189809
theorem R126551 : Reach 126551 := rs (se 1 (by rfl) ⟨94913, by rfl⟩) R189827
theorem R159347 : Reach 159347 := rs (se 1 (by rfl) ⟨119510, by rfl⟩) R239021
theorem R93847 : Reach 93847 := rs (se 1 (by rfl) ⟨70385, by rfl⟩) R140771
theorem R126617 : Reach 126617 := rs (se 2 (by rfl) ⟨47481, by rfl⟩) R94963
theorem R192203 : Reach 192203 := rs (se 1 (by rfl) ⟨144152, by rfl⟩) R288305
theorem R192257 : Reach 192257 := rs (se 2 (by rfl) ⟨72096, by rfl⟩) R144193
theorem R159499 : Reach 159499 := rs (se 1 (by rfl) ⟨119624, by rfl⟩) R239249
theorem R126731 : Reach 126731 := rs (se 1 (by rfl) ⟨95048, by rfl⟩) R190097
theorem R126743 : Reach 126743 := rs (se 1 (by rfl) ⟨95057, by rfl⟩) R190115
theorem R94027 : Reach 94027 := rs (se 1 (by rfl) ⟨70520, by rfl⟩) R141041
theorem R126809 : Reach 126809 := rs (se 2 (by rfl) ⟨47553, by rfl⟩) R95107
theorem R94135 : Reach 94135 := rs (se 1 (by rfl) ⟨70601, by rfl⟩) R141203
theorem R192449 : Reach 192449 := rs (se 2 (by rfl) ⟨72168, by rfl⟩) R144337
theorem R126923 : Reach 126923 := rs (se 1 (by rfl) ⟨95192, by rfl⟩) R190385
theorem R126935 : Reach 126935 := rs (se 1 (by rfl) ⟨95201, by rfl⟩) R190403
theorem R192473 : Reach 192473 := rs (se 2 (by rfl) ⟨72177, by rfl⟩) R144355
theorem R127001 : Reach 127001 := rs (se 2 (by rfl) ⟨47625, by rfl⟩) R95251
theorem R192563 : Reach 192563 := rs (se 1 (by rfl) ⟨144422, by rfl⟩) R288845
theorem R127051 : Reach 127051 := rs (se 1 (by rfl) ⟨95288, by rfl⟩) R190577
theorem R192599 : Reach 192599 := rs (se 1 (by rfl) ⟨144449, by rfl⟩) R288899
theorem R159833 : Reach 159833 := rs (se 2 (by rfl) ⟨59937, by rfl⟩) R119875
theorem R94315 : Reach 94315 := rs (se 1 (by rfl) ⟨70736, by rfl⟩) R141473
theorem R127115 : Reach 127115 := rs (se 1 (by rfl) ⟨95336, by rfl⟩) R190673
theorem R127127 : Reach 127127 := rs (se 1 (by rfl) ⟨95345, by rfl⟩) R190691
theorem R94423 : Reach 94423 := rs (se 1 (by rfl) ⟨70817, by rfl⟩) R141635
theorem R127193 : Reach 127193 := rs (se 2 (by rfl) ⟨47697, by rfl⟩) R95395
theorem R192779 : Reach 192779 := rs (se 1 (by rfl) ⟨144584, by rfl⟩) R289169
theorem R192833 : Reach 192833 := rs (se 2 (by rfl) ⟨72312, by rfl⟩) R144625
theorem R127307 : Reach 127307 := rs (se 1 (by rfl) ⟨95480, by rfl⟩) R190961
theorem R127319 : Reach 127319 := rs (se 1 (by rfl) ⟨95489, by rfl⟩) R190979
theorem R94603 : Reach 94603 := rs (se 1 (by rfl) ⟨70952, by rfl⟩) R141905
theorem R258455 : Reach 258455 := rs (se 1 (by rfl) ⟨193841, by rfl⟩) R387683
theorem R127385 : Reach 127385 := rs (se 2 (by rfl) ⟨47769, by rfl⟩) R95539
theorem R1110449 : Reach 1110449 := rs (se 2 (by rfl) ⟨416418, by rfl⟩) R832837
theorem R291275 : Reach 291275 := rs (se 1 (by rfl) ⟨218456, by rfl⟩) R436913
theorem R651725 : Reach 651725 := rs (se 3 (by rfl) ⟨122198, by rfl⟩) R244397
theorem R94711 : Reach 94711 := rs (se 1 (by rfl) ⟨71033, by rfl⟩) R142067
theorem R127499 : Reach 127499 := rs (se 1 (by rfl) ⟨95624, by rfl⟩) R191249
theorem R127511 : Reach 127511 := rs (se 1 (by rfl) ⟨95633, by rfl⟩) R191267
theorem R193049 : Reach 193049 := rs (se 2 (by rfl) ⟨72393, by rfl⟩) R144787
theorem R127577 : Reach 127577 := rs (se 2 (by rfl) ⟨47841, by rfl⟩) R95683
theorem R193139 : Reach 193139 := rs (se 1 (by rfl) ⟨144854, by rfl⟩) R289709
theorem R94859 : Reach 94859 := rs (se 1 (by rfl) ⟨71144, by rfl⟩) R142289
theorem R193175 : Reach 193175 := rs (se 1 (by rfl) ⟨144881, by rfl⟩) R289763
theorem R94891 : Reach 94891 := rs (se 1 (by rfl) ⟨71168, by rfl⟩) R142337
theorem R324269 : Reach 324269 := rs (se 3 (by rfl) ⟨60800, by rfl⟩) R121601
theorem R127691 : Reach 127691 := rs (se 1 (by rfl) ⟨95768, by rfl⟩) R191537
theorem R160471 : Reach 160471 := rs (se 1 (by rfl) ⟨120353, by rfl⟩) R240707
theorem R127703 : Reach 127703 := rs (se 1 (by rfl) ⟨95777, by rfl⟩) R191555
theorem R291545 : Reach 291545 := rs (se 2 (by rfl) ⟨109329, by rfl⟩) R218659
theorem R94999 : Reach 94999 := rs (se 1 (by rfl) ⟨71249, by rfl⟩) R142499
theorem R127769 : Reach 127769 := rs (se 2 (by rfl) ⟨47913, by rfl⟩) R95827
theorem R193355 : Reach 193355 := rs (se 1 (by rfl) ⟨145016, by rfl⟩) R290033
theorem R193409 : Reach 193409 := rs (se 2 (by rfl) ⟨72528, by rfl⟩) R145057
theorem R127883 : Reach 127883 := rs (se 1 (by rfl) ⟨95912, by rfl⟩) R191825
theorem R127895 : Reach 127895 := rs (se 1 (by rfl) ⟨95921, by rfl⟩) R191843
theorem R652211 : Reach 652211 := rs (se 1 (by rfl) ⟨489158, by rfl⟩) R978317
theorem R95179 : Reach 95179 := rs (se 1 (by rfl) ⟨71384, by rfl⟩) R142769
theorem R127961 : Reach 127961 := rs (se 2 (by rfl) ⟨47985, by rfl⟩) R95971
theorem R390167 : Reach 390167 := rs (se 1 (by rfl) ⟨292625, by rfl⟩) R585251
theorem R95287 : Reach 95287 := rs (se 1 (by rfl) ⟨71465, by rfl⟩) R142931
theorem R128075 : Reach 128075 := rs (se 1 (by rfl) ⟨96056, by rfl⟩) R192113
theorem R128087 : Reach 128087 := rs (se 1 (by rfl) ⟨96065, by rfl⟩) R192131
theorem R193625 : Reach 193625 := rs (se 2 (by rfl) ⟨72609, by rfl⟩) R145219
theorem R128153 : Reach 128153 := rs (se 2 (by rfl) ⟨48057, by rfl⟩) R96115
theorem R193715 : Reach 193715 := rs (se 1 (by rfl) ⟨145286, by rfl⟩) R290573
theorem R193751 : Reach 193751 := rs (se 1 (by rfl) ⟨145313, by rfl⟩) R290627
theorem R554201 : Reach 554201 := rs (se 2 (by rfl) ⟨207825, by rfl⟩) R415651
theorem R95467 : Reach 95467 := rs (se 1 (by rfl) ⟨71600, by rfl⟩) R143201
theorem R128267 : Reach 128267 := rs (se 1 (by rfl) ⟨96200, by rfl⟩) R192401
theorem R226583 : Reach 226583 := rs (se 1 (by rfl) ⟨169937, by rfl⟩) R339875
theorem R128279 : Reach 128279 := rs (se 1 (by rfl) ⟨96209, by rfl⟩) R192419
theorem R95575 : Reach 95575 := rs (se 1 (by rfl) ⟨71681, by rfl⟩) R143363
theorem R128345 : Reach 128345 := rs (se 2 (by rfl) ⟨48129, by rfl⟩) R96259
theorem R193931 : Reach 193931 := rs (se 1 (by rfl) ⟨145448, by rfl⟩) R290897
theorem R292247 : Reach 292247 := rs (se 1 (by rfl) ⟨219185, by rfl⟩) R438371
theorem R325043 : Reach 325043 := rs (se 1 (by rfl) ⟨243782, by rfl⟩) R487565
theorem R193985 : Reach 193985 := rs (se 2 (by rfl) ⟨72744, by rfl⟩) R145489
theorem R128459 : Reach 128459 := rs (se 1 (by rfl) ⟨96344, by rfl⟩) R192689
theorem R128471 : Reach 128471 := rs (se 1 (by rfl) ⟨96353, by rfl⟩) R192707
theorem R161291 : Reach 161291 := rs (se 1 (by rfl) ⟨120968, by rfl⟩) R241937
theorem R95755 : Reach 95755 := rs (se 1 (by rfl) ⟨71816, by rfl⟩) R143633
theorem R128537 : Reach 128537 := rs (se 2 (by rfl) ⟨48201, by rfl⟩) R96403
theorem R783917 : Reach 783917 := rs (se 3 (by rfl) ⟨146984, by rfl⟩) R293969
theorem R161345 : Reach 161345 := rs (se 2 (by rfl) ⟨60504, by rfl⟩) R121009
theorem R718429 : Reach 718429 := rs (se 3 (by rfl) ⟨134705, by rfl⟩) R269411
theorem R95863 : Reach 95863 := rs (se 1 (by rfl) ⟨71897, by rfl⟩) R143795
theorem R128651 : Reach 128651 := rs (se 1 (by rfl) ⟨96488, by rfl⟩) R192977
theorem R128663 : Reach 128663 := rs (se 1 (by rfl) ⟨96497, by rfl⟩) R192995
theorem R194201 : Reach 194201 := rs (se 2 (by rfl) ⟨72825, by rfl⟩) R145651
theorem R128729 : Reach 128729 := rs (se 2 (by rfl) ⟨48273, by rfl⟩) R96547
theorem R194291 : Reach 194291 := rs (se 1 (by rfl) ⟨145718, by rfl⟩) R291437
theorem R194327 : Reach 194327 := rs (se 1 (by rfl) ⟨145745, by rfl⟩) R291491
theorem R96043 : Reach 96043 := rs (se 1 (by rfl) ⟨72032, by rfl⟩) R144065
theorem R128843 : Reach 128843 := rs (se 1 (by rfl) ⟨96632, by rfl⟩) R193265
theorem R128855 : Reach 128855 := rs (se 1 (by rfl) ⟨96641, by rfl⟩) R193283
theorem R96151 : Reach 96151 := rs (se 1 (by rfl) ⟨72113, by rfl⟩) R144227
theorem R128921 : Reach 128921 := rs (se 2 (by rfl) ⟨48345, by rfl⟩) R96691
theorem R292787 : Reach 292787 := rs (se 1 (by rfl) ⟨219590, by rfl⟩) R439181
theorem R194507 : Reach 194507 := rs (se 1 (by rfl) ⟨145880, by rfl⟩) R291761
theorem R194561 : Reach 194561 := rs (se 2 (by rfl) ⟨72960, by rfl⟩) R145921
theorem R129035 : Reach 129035 := rs (se 1 (by rfl) ⟨96776, by rfl⟩) R193553
theorem R423953 : Reach 423953 := rs (se 2 (by rfl) ⟨158982, by rfl⟩) R317965
theorem R129047 : Reach 129047 := rs (se 1 (by rfl) ⟨96785, by rfl⟩) R193571
theorem R96331 : Reach 96331 := rs (se 1 (by rfl) ⟨72248, by rfl⟩) R144497
theorem R129113 : Reach 129113 := rs (se 2 (by rfl) ⟨48417, by rfl⟩) R96835
theorem R96395 : Reach 96395 := rs (se 1 (by rfl) ⟨72296, by rfl⟩) R144593
theorem R129163 : Reach 129163 := rs (se 1 (by rfl) ⟨96872, by rfl⟩) R193745
theorem R424115 : Reach 424115 := rs (se 1 (by rfl) ⟨318086, by rfl⟩) R636173
theorem R96439 : Reach 96439 := rs (se 1 (by rfl) ⟨72329, by rfl⟩) R144659
theorem R293057 : Reach 293057 := rs (se 2 (by rfl) ⟨109896, by rfl⟩) R219793
theorem R129227 : Reach 129227 := rs (se 1 (by rfl) ⟨96920, by rfl⟩) R193841
theorem R129239 : Reach 129239 := rs (se 1 (by rfl) ⟨96929, by rfl⟩) R193859
theorem R194777 : Reach 194777 := rs (se 2 (by rfl) ⟨73041, by rfl⟩) R146083
theorem R129305 : Reach 129305 := rs (se 2 (by rfl) ⟨48489, by rfl⟩) R96979
theorem R194867 : Reach 194867 := rs (se 1 (by rfl) ⟨146150, by rfl⟩) R292301
theorem R194903 : Reach 194903 := rs (se 1 (by rfl) ⟨146177, by rfl⟩) R292355
theorem R653669 : Reach 653669 := rs (se 4 (by rfl) ⟨61281, by rfl⟩) R122563
theorem R96619 : Reach 96619 := rs (se 1 (by rfl) ⟨72464, by rfl⟩) R144929
theorem R129419 : Reach 129419 := rs (se 1 (by rfl) ⟨97064, by rfl⟩) R194129
theorem R129431 : Reach 129431 := rs (se 1 (by rfl) ⟨97073, by rfl⟩) R194147
theorem R162263 : Reach 162263 := rs (se 1 (by rfl) ⟨121697, by rfl⟩) R243395
theorem R96727 : Reach 96727 := rs (se 1 (by rfl) ⟨72545, by rfl⟩) R145091
theorem R129497 : Reach 129497 := rs (se 2 (by rfl) ⟨48561, by rfl⟩) R97123
theorem R195083 : Reach 195083 := rs (se 1 (by rfl) ⟨146312, by rfl⟩) R292625
theorem R490049 : Reach 490049 := rs (se 2 (by rfl) ⟨183768, by rfl⟩) R367537
theorem R195137 : Reach 195137 := rs (se 2 (by rfl) ⟨73176, by rfl⟩) R146353
theorem R129611 : Reach 129611 := rs (se 1 (by rfl) ⟨97208, by rfl⟩) R194417
theorem R129623 : Reach 129623 := rs (se 1 (by rfl) ⟨97217, by rfl⟩) R194435
theorem R96907 : Reach 96907 := rs (se 1 (by rfl) ⟨72680, by rfl⟩) R145361
theorem R359063 : Reach 359063 := rs (se 1 (by rfl) ⟨269297, by rfl⟩) R538595
theorem R129689 : Reach 129689 := rs (se 2 (by rfl) ⟨48633, by rfl⟩) R97267
theorem R293597 : Reach 293597 := rs (se 3 (by rfl) ⟨55049, by rfl⟩) R110099
theorem R97015 : Reach 97015 := rs (se 1 (by rfl) ⟨72761, by rfl⟩) R145523
theorem R129803 : Reach 129803 := rs (se 1 (by rfl) ⟨97352, by rfl⟩) R194705
theorem R129815 : Reach 129815 := rs (se 1 (by rfl) ⟨97361, by rfl⟩) R194723
theorem R195353 : Reach 195353 := rs (se 2 (by rfl) ⟨73257, by rfl⟩) R146515
theorem R654155 : Reach 654155 := rs (se 1 (by rfl) ⟨490616, by rfl⟩) R981233
theorem R129881 : Reach 129881 := rs (se 2 (by rfl) ⟨48705, by rfl⟩) R97411
theorem R195443 : Reach 195443 := rs (se 1 (by rfl) ⟨146582, by rfl⟩) R293165
theorem R326531 : Reach 326531 := rs (se 1 (by rfl) ⟨244898, by rfl⟩) R489797
theorem R195479 : Reach 195479 := rs (se 1 (by rfl) ⟨146609, by rfl⟩) R293219
theorem R97195 : Reach 97195 := rs (se 1 (by rfl) ⟨72896, by rfl⟩) R145793
theorem R129995 : Reach 129995 := rs (se 1 (by rfl) ⟨97496, by rfl⟩) R194993
theorem R130007 : Reach 130007 := rs (se 1 (by rfl) ⟨97505, by rfl⟩) R195011
theorem R162803 : Reach 162803 := rs (se 1 (by rfl) ⟨122102, by rfl⟩) R244205
theorem R97303 : Reach 97303 := rs (se 1 (by rfl) ⟨72977, by rfl⟩) R145955
theorem R130073 : Reach 130073 := rs (se 2 (by rfl) ⟨48777, by rfl⟩) R97555
theorem R293939 : Reach 293939 := rs (se 1 (by rfl) ⟨220454, by rfl⟩) R440909
theorem R195659 : Reach 195659 := rs (se 1 (by rfl) ⟨146744, by rfl⟩) R293489
theorem R195713 : Reach 195713 := rs (se 2 (by rfl) ⟨73392, by rfl⟩) R146785
theorem R130187 : Reach 130187 := rs (se 1 (by rfl) ⟨97640, by rfl⟩) R195281
theorem R130199 : Reach 130199 := rs (se 1 (by rfl) ⟨97649, by rfl⟩) R195299
theorem R97483 : Reach 97483 := rs (se 1 (by rfl) ⟨73112, by rfl⟩) R146225
theorem R130265 : Reach 130265 := rs (se 2 (by rfl) ⟨48849, by rfl⟩) R97699
theorem R195851 : Reach 195851 := rs (se 1 (by rfl) ⟨146888, by rfl⟩) R293777
theorem R97591 : Reach 97591 := rs (se 1 (by rfl) ⟨73193, by rfl⟩) R146387
theorem R326987 : Reach 326987 := rs (se 1 (by rfl) ⟨245240, by rfl⟩) R490481
theorem R130379 : Reach 130379 := rs (se 1 (by rfl) ⟨97784, by rfl⟩) R195569
theorem R130391 : Reach 130391 := rs (se 1 (by rfl) ⟨97793, by rfl⟩) R195587
theorem R195929 : Reach 195929 := rs (se 2 (by rfl) ⟨73473, by rfl⟩) R146947
theorem R130457 : Reach 130457 := rs (se 2 (by rfl) ⟨48921, by rfl⟩) R97843
theorem R196019 : Reach 196019 := rs (se 1 (by rfl) ⟨147014, by rfl⟩) R294029
theorem R196033 : Reach 196033 := rs (se 2 (by rfl) ⟨73512, by rfl⟩) R147025
theorem R163289 : Reach 163289 := rs (se 2 (by rfl) ⟨61233, by rfl⟩) R122467
theorem R97771 : Reach 97771 := rs (se 1 (by rfl) ⟨73328, by rfl⟩) R146657
theorem R130571 : Reach 130571 := rs (se 1 (by rfl) ⟨97928, by rfl⟩) R195857
theorem R327185 : Reach 327185 := rs (se 2 (by rfl) ⟨122694, by rfl⟩) R245389
theorem R130583 : Reach 130583 := rs (se 1 (by rfl) ⟨97937, by rfl⟩) R195875
theorem R97879 : Reach 97879 := rs (se 1 (by rfl) ⟨73409, by rfl⟩) R146819
theorem R130649 : Reach 130649 := rs (se 2 (by rfl) ⟨48993, by rfl⟩) R97987
theorem R229015 : Reach 229015 := rs (se 1 (by rfl) ⟨171761, by rfl⟩) R343523
theorem R556865 : Reach 556865 := rs (se 2 (by rfl) ⟨208824, by rfl⟩) R417649
theorem R1343411 : Reach 1343411 := rs (se 1 (by rfl) ⟨1007558, by rfl⟩) R2015117
theorem R163873 : Reach 163873 := rs (se 2 (by rfl) ⟨61452, by rfl⟩) R122905
theorem R655447 : Reach 655447 := rs (se 1 (by rfl) ⟨491585, by rfl⟩) R983171
theorem R426221 : Reach 426221 := rs (se 3 (by rfl) ⟨79916, by rfl⟩) R159833
theorem R360719 : Reach 360719 := rs (se 1 (by rfl) ⟨270539, by rfl⟩) R541079
theorem R131387 : Reach 131387 := rs (se 1 (by rfl) ⟨98540, by rfl⟩) R197081
theorem R2326877 : Reach 2326877 := rs (se 3 (by rfl) ⟨436289, by rfl⟩) R872579
theorem R1081745 : Reach 1081745 := rs (se 2 (by rfl) ⟨405654, by rfl⟩) R811309
theorem R393815 : Reach 393815 := rs (se 1 (by rfl) ⟨295361, by rfl⟩) R590723
theorem R3343193 : Reach 3343193 := rs (se 2 (by rfl) ⟨1253697, by rfl⟩) R2507395
theorem R328657 : Reach 328657 := rs (se 2 (by rfl) ⟨123246, by rfl⟩) R246493
theorem R623627 : Reach 623627 := rs (se 1 (by rfl) ⟨467720, by rfl⟩) R935441
theorem R427031 : Reach 427031 := rs (se 1 (by rfl) ⟨320273, by rfl⟩) R640547
theorem R689213 : Reach 689213 := rs (se 3 (by rfl) ⟨129227, by rfl⟩) R258455
theorem R656585 : Reach 656585 := rs (se 2 (by rfl) ⟨246219, by rfl⟩) R492439
theorem R328961 : Reach 328961 := rs (se 2 (by rfl) ⟨123360, by rfl⟩) R246721
theorem R165179 : Reach 165179 := rs (se 1 (by rfl) ⟨123884, by rfl⟩) R247769
theorem R493067 : Reach 493067 := rs (se 1 (by rfl) ⟨369800, by rfl⟩) R739601
theorem R886373 : Reach 886373 := rs (se 4 (by rfl) ⟨83097, by rfl⟩) R166195
theorem R296567 : Reach 296567 := rs (se 1 (by rfl) ⟨222425, by rfl⟩) R444851
theorem R493249 : Reach 493249 := rs (se 2 (by rfl) ⟨184968, by rfl⟩) R369937
theorem R329417 : Reach 329417 := rs (se 2 (by rfl) ⟨123531, by rfl⟩) R247063
theorem R722803 : Reach 722803 := rs (se 1 (by rfl) ⟨542102, by rfl⟩) R1084205
theorem R723077 : Reach 723077 := rs (se 4 (by rfl) ⟨67788, by rfl⟩) R135577
theorem R920335 : Reach 920335 := rs (se 1 (by rfl) ⟨690251, by rfl⟩) R1380503
theorem R133931 : Reach 133931 := rs (se 1 (by rfl) ⟨100448, by rfl⟩) R200897
theorem R723761 : Reach 723761 := rs (se 2 (by rfl) ⟨271410, by rfl⟩) R542821
theorem R101179 : Reach 101179 := rs (se 1 (by rfl) ⟨75884, by rfl⟩) R151769
theorem R297881 : Reach 297881 := rs (se 2 (by rfl) ⟨111705, by rfl⟩) R223411
theorem R167287 : Reach 167287 := rs (se 1 (by rfl) ⟨125465, by rfl⟩) R250931
theorem R232961 : Reach 232961 := rs (se 2 (by rfl) ⟨87360, by rfl⟩) R174721
theorem R233113 : Reach 233113 := rs (se 2 (by rfl) ⟨87417, by rfl⟩) R174835
theorem R2723635 : Reach 2723635 := rs (se 1 (by rfl) ⟨2042726, by rfl⟩) R4085453
theorem R724787 : Reach 724787 := rs (se 1 (by rfl) ⟨543590, by rfl⟩) R1087181
theorem R233275 : Reach 233275 := rs (se 1 (by rfl) ⟨174956, by rfl⟩) R349913
theorem R921547 : Reach 921547 := rs (se 1 (by rfl) ⟨691160, by rfl⟩) R1382321
theorem R430109 : Reach 430109 := rs (se 3 (by rfl) ⟨80645, by rfl⟩) R161291
theorem R201079 : Reach 201079 := rs (se 1 (by rfl) ⟨150809, by rfl⟩) R301619
theorem R430595 : Reach 430595 := rs (se 1 (by rfl) ⟨322946, by rfl⟩) R645893
theorem R758807 : Reach 758807 := rs (se 1 (by rfl) ⟨569105, by rfl⟩) R1138211
theorem R300061 : Reach 300061 := rs (se 3 (by rfl) ⟨56261, by rfl⟩) R112523
theorem R103567 : Reach 103567 := rs (se 1 (by rfl) ⟨77675, by rfl⟩) R155351
theorem R1283309 : Reach 1283309 := rs (se 3 (by rfl) ⟨240620, by rfl⟩) R481241
theorem R300611 : Reach 300611 := rs (se 1 (by rfl) ⟨225458, by rfl⟩) R450917
theorem R300781 : Reach 300781 := rs (se 3 (by rfl) ⟨56396, by rfl⟩) R112793
theorem R137231 : Reach 137231 := rs (se 1 (by rfl) ⟨102923, by rfl⟩) R205847
theorem R432215 : Reach 432215 := rs (se 1 (by rfl) ⟨324161, by rfl⟩) R648323
theorem R432701 : Reach 432701 := rs (se 3 (by rfl) ⟨81131, by rfl⟩) R162263
theorem R1055425 : Reach 1055425 := rs (se 2 (by rfl) ⟨395784, by rfl⟩) R791569
theorem R334745 : Reach 334745 := rs (se 2 (by rfl) ⟨125529, by rfl⟩) R251059
theorem R400427 : Reach 400427 := rs (se 1 (by rfl) ⟨300320, by rfl⟩) R600641
theorem R498977 : Reach 498977 := rs (se 2 (by rfl) ⟨187116, by rfl⟩) R374233
theorem R236915 : Reach 236915 := rs (se 1 (by rfl) ⟨177686, by rfl⟩) R355373
theorem R1056185 : Reach 1056185 := rs (se 2 (by rfl) ⟨396069, by rfl⟩) R792139
theorem R957905 : Reach 957905 := rs (se 2 (by rfl) ⟨359214, by rfl⟩) R718429
theorem R466397 : Reach 466397 := rs (se 3 (by rfl) ⟨87449, by rfl⟩) R174899
theorem R5283427 : Reach 5283427 := rs (se 1 (by rfl) ⟨3962570, by rfl⟩) R7925141
theorem R138871 : Reach 138871 := rs (se 1 (by rfl) ⟨104153, by rfl⟩) R208307
theorem R172217 : Reach 172217 := rs (se 2 (by rfl) ⟨64581, by rfl⟩) R129163
theorem R205001 : Reach 205001 := rs (se 2 (by rfl) ⟨76875, by rfl⟩) R153751
theorem R434483 : Reach 434483 := rs (se 1 (by rfl) ⟨325862, by rfl⟩) R651725
theorem R434807 : Reach 434807 := rs (se 1 (by rfl) ⟨326105, by rfl⟩) R652211
theorem R533263 : Reach 533263 := rs (se 1 (by rfl) ⟨399947, by rfl⟩) R799895
theorem R369467 : Reach 369467 := rs (se 1 (by rfl) ⟨277100, by rfl⟩) R554201
theorem R205715 : Reach 205715 := rs (se 1 (by rfl) ⟨154286, by rfl⟩) R308573
theorem R107563 : Reach 107563 := rs (se 1 (by rfl) ⟨80672, by rfl⟩) R161345
theorem R140663 : Reach 140663 := rs (se 1 (by rfl) ⟨105497, by rfl⟩) R210995
theorem R1254791 : Reach 1254791 := rs (se 1 (by rfl) ⟨941093, by rfl⟩) R1882187
theorem R632285 : Reach 632285 := rs (se 3 (by rfl) ⟨118553, by rfl⟩) R237107
theorem R435779 : Reach 435779 := rs (se 1 (by rfl) ⟨326834, by rfl⟩) R653669
theorem R304877 : Reach 304877 := rs (se 3 (by rfl) ⟨57164, by rfl⟩) R114329
theorem R239375 : Reach 239375 := rs (se 1 (by rfl) ⟨179531, by rfl⟩) R359063
theorem R141115 : Reach 141115 := rs (se 1 (by rfl) ⟨105836, by rfl⟩) R211673
theorem R206651 : Reach 206651 := rs (se 1 (by rfl) ⟨154988, by rfl⟩) R309977
theorem R436103 : Reach 436103 := rs (se 1 (by rfl) ⟨327077, by rfl⟩) R654155
theorem R141257 : Reach 141257 := rs (se 2 (by rfl) ⟨52971, by rfl⟩) R105943
theorem R108535 : Reach 108535 := rs (se 1 (by rfl) ⟨81401, by rfl⟩) R162803
theorem R305353 : Reach 305353 := rs (se 2 (by rfl) ⟨114507, by rfl⟩) R229015
theorem R272641 : Reach 272641 := rs (se 2 (by rfl) ⟨102240, by rfl⟩) R204481
theorem R108859 : Reach 108859 := rs (se 1 (by rfl) ⟨81644, by rfl⟩) R163289
theorem R928259 : Reach 928259 := rs (se 1 (by rfl) ⟨696194, by rfl⟩) R1392389
theorem R371243 : Reach 371243 := rs (se 1 (by rfl) ⟨278432, by rfl⟩) R556865
theorem R895607 : Reach 895607 := rs (se 1 (by rfl) ⟨671705, by rfl⟩) R1343411
theorem R141959 : Reach 141959 := rs (se 1 (by rfl) ⟨106469, by rfl⟩) R212939
theorem R371773 : Reach 371773 := rs (se 3 (by rfl) ⟨69707, by rfl⟩) R139415
theorem R699479 : Reach 699479 := rs (se 1 (by rfl) ⟨524609, by rfl⟩) R1049219
theorem R306433 : Reach 306433 := rs (se 2 (by rfl) ⟨114912, by rfl⟩) R229825
theorem R109831 : Reach 109831 := rs (se 1 (by rfl) ⟨82373, by rfl⟩) R164747
theorem R142607 : Reach 142607 := rs (se 1 (by rfl) ⟨106955, by rfl⟩) R213911
theorem R241015 : Reach 241015 := rs (se 1 (by rfl) ⟨180761, by rfl⟩) R361523
theorem R241049 : Reach 241049 := rs (se 2 (by rfl) ⟨90393, by rfl⟩) R180787
theorem R241163 : Reach 241163 := rs (se 1 (by rfl) ⟨180872, by rfl⟩) R361745
theorem R110251 : Reach 110251 := rs (se 1 (by rfl) ⟨82688, by rfl⟩) R165377
theorem R470701 : Reach 470701 := rs (se 3 (by rfl) ⟨88256, by rfl⟩) R176513
theorem R208585 : Reach 208585 := rs (se 2 (by rfl) ⟨78219, by rfl⟩) R156439
theorem R143147 : Reach 143147 := rs (se 1 (by rfl) ⟨107360, by rfl⟩) R214721
theorem R143545 : Reach 143545 := rs (se 2 (by rfl) ⟨53829, by rfl⟩) R107659
theorem R307471 : Reach 307471 := rs (se 1 (by rfl) ⟨230603, by rfl⟩) R461207
theorem R242291 : Reach 242291 := rs (se 1 (by rfl) ⟨181718, by rfl⟩) R363437
theorem R144247 : Reach 144247 := rs (se 1 (by rfl) ⟨108185, by rfl⟩) R216371
theorem R668569 : Reach 668569 := rs (se 2 (by rfl) ⟨250713, by rfl⟩) R501427
theorem R242689 : Reach 242689 := rs (se 2 (by rfl) ⟨91008, by rfl⟩) R182017
theorem R242747 : Reach 242747 := rs (se 1 (by rfl) ⟨182060, by rfl⟩) R364121
theorem R144443 : Reach 144443 := rs (se 1 (by rfl) ⟨108332, by rfl⟩) R216665
theorem R439667 : Reach 439667 := rs (se 1 (by rfl) ⟨329750, by rfl⟩) R659501
theorem R111991 : Reach 111991 := rs (se 1 (by rfl) ⟨83993, by rfl⟩) R167987
theorem R308627 : Reach 308627 := rs (se 1 (by rfl) ⟨231470, by rfl⟩) R462941
theorem R144841 : Reach 144841 := rs (se 2 (by rfl) ⟨54315, by rfl⟩) R108631
theorem R308855 : Reach 308855 := rs (se 1 (by rfl) ⟨231641, by rfl⟩) R463283
theorem R210721 : Reach 210721 := rs (se 2 (by rfl) ⟨79020, by rfl⟩) R158041
theorem R440153 : Reach 440153 := rs (se 2 (by rfl) ⟨165057, by rfl⟩) R330115
theorem R145543 : Reach 145543 := rs (se 1 (by rfl) ⟨109157, by rfl⟩) R218315
theorem R211319 : Reach 211319 := rs (se 1 (by rfl) ⟨158489, by rfl⟩) R316979
theorem R146191 : Reach 146191 := rs (se 1 (by rfl) ⟨109643, by rfl⟩) R219287
theorem R179129 : Reach 179129 := rs (se 2 (by rfl) ⟨67173, by rfl⟩) R134347
theorem R179471 : Reach 179471 := rs (se 1 (by rfl) ⟨134603, by rfl⟩) R269207
theorem R179489 : Reach 179489 := rs (se 2 (by rfl) ⟨67308, by rfl⟩) R134617
theorem R245035 : Reach 245035 := rs (se 1 (by rfl) ⟨183776, by rfl⟩) R367553
theorem R146731 : Reach 146731 := rs (se 1 (by rfl) ⟨110048, by rfl⟩) R220097
theorem R146873 : Reach 146873 := rs (se 2 (by rfl) ⟨55077, by rfl⟩) R110155
theorem R245263 : Reach 245263 := rs (se 1 (by rfl) ⟨183947, by rfl⟩) R367895
theorem R409175 : Reach 409175 := rs (se 1 (by rfl) ⟨306881, by rfl⟩) R613763
theorem R212615 : Reach 212615 := rs (se 1 (by rfl) ⟨159461, by rfl⟩) R318923
theorem R212665 : Reach 212665 := rs (se 2 (by rfl) ⟨79749, by rfl⟩) R159499
theorem R245537 : Reach 245537 := rs (se 2 (by rfl) ⟨92076, by rfl⟩) R184153
theorem R114491 : Reach 114491 := rs (se 1 (by rfl) ⟨85868, by rfl⟩) R171737
theorem R245879 : Reach 245879 := rs (se 1 (by rfl) ⟨184409, by rfl⟩) R368819
theorem R213263 : Reach 213263 := rs (se 1 (by rfl) ⟨159947, by rfl⟩) R319895
theorem R115129 : Reach 115129 := rs (se 2 (by rfl) ⟨43173, by rfl⟩) R86347
theorem R4047317 : Reach 4047317 := rs (se 7 (by rfl) ⟨47429, by rfl⟩) R94859
theorem R410179 : Reach 410179 := rs (se 1 (by rfl) ⟨307634, by rfl⟩) R615269
theorem R246539 : Reach 246539 := rs (se 1 (by rfl) ⟨184904, by rfl⟩) R369809
theorem R803621 : Reach 803621 := rs (se 4 (by rfl) ⟨75339, by rfl⟩) R150679
theorem R181111 : Reach 181111 := rs (se 1 (by rfl) ⟨135833, by rfl⟩) R271667
theorem R213961 : Reach 213961 := rs (se 2 (by rfl) ⟨80235, by rfl⟩) R160471
theorem R640061 : Reach 640061 := rs (se 3 (by rfl) ⟨120011, by rfl⟩) R240023
theorem R214103 : Reach 214103 := rs (se 1 (by rfl) ⟨160577, by rfl⟩) R321155
theorem R83131 : Reach 83131 := rs (se 1 (by rfl) ⟨62348, by rfl⟩) R124697
theorem R83207 : Reach 83207 := rs (se 1 (by rfl) ⟨62405, by rfl⟩) R124811
theorem R83215 : Reach 83215 := rs (se 1 (by rfl) ⟨62411, by rfl⟩) R124823
theorem R83259 : Reach 83259 := rs (se 1 (by rfl) ⟨62444, by rfl⟩) R124889
theorem R83335 : Reach 83335 := rs (se 1 (by rfl) ⟨62501, by rfl⟩) R125003
theorem R83343 : Reach 83343 := rs (se 1 (by rfl) ⟨62507, by rfl⟩) R125015
theorem R83387 : Reach 83387 := rs (se 1 (by rfl) ⟨62540, by rfl⟩) R125081
theorem R476675 : Reach 476675 := rs (se 1 (by rfl) ⟨357506, by rfl⟩) R715013
theorem R83463 : Reach 83463 := rs (se 1 (by rfl) ⟨62597, by rfl⟩) R125195
theorem R83471 : Reach 83471 := rs (se 1 (by rfl) ⟨62603, by rfl⟩) R125207
theorem R181775 : Reach 181775 := rs (se 1 (by rfl) ⟨136331, by rfl⟩) R272663
theorem R83515 : Reach 83515 := rs (se 1 (by rfl) ⟨62636, by rfl⟩) R125273
theorem R312893 : Reach 312893 := rs (se 3 (by rfl) ⟨58667, by rfl⟩) R117335
theorem R83591 : Reach 83591 := rs (se 1 (by rfl) ⟨62693, by rfl⟩) R125387
theorem R83599 : Reach 83599 := rs (se 1 (by rfl) ⟨62699, by rfl⟩) R125399
theorem R83643 : Reach 83643 := rs (se 1 (by rfl) ⟨62732, by rfl⟩) R125465
theorem R83719 : Reach 83719 := rs (se 1 (by rfl) ⟨62789, by rfl⟩) R125579
theorem R83727 : Reach 83727 := rs (se 1 (by rfl) ⟨62795, by rfl⟩) R125591
theorem R83771 : Reach 83771 := rs (se 1 (by rfl) ⟨62828, by rfl⟩) R125657
theorem R83847 : Reach 83847 := rs (se 1 (by rfl) ⟨62885, by rfl⟩) R125771
theorem R83855 : Reach 83855 := rs (se 1 (by rfl) ⟨62891, by rfl⟩) R125783
theorem R83899 : Reach 83899 := rs (se 1 (by rfl) ⟨62924, by rfl⟩) R125849
theorem R509905 : Reach 509905 := rs (se 2 (by rfl) ⟨191214, by rfl⟩) R382429
theorem R83975 : Reach 83975 := rs (se 1 (by rfl) ⟨62981, by rfl⟩) R125963
theorem R83983 : Reach 83983 := rs (se 1 (by rfl) ⟨62987, by rfl⟩) R125975
theorem R84027 : Reach 84027 := rs (se 1 (by rfl) ⟨63020, by rfl⟩) R126041
theorem R280637 : Reach 280637 := rs (se 3 (by rfl) ⟨52619, by rfl⟩) R105239
theorem R477245 : Reach 477245 := rs (se 3 (by rfl) ⟨89483, by rfl⟩) R178967
theorem R444503 : Reach 444503 := rs (se 1 (by rfl) ⟨333377, by rfl⟩) R666755
theorem R84103 : Reach 84103 := rs (se 1 (by rfl) ⟨63077, by rfl⟩) R126155
theorem R84111 : Reach 84111 := rs (se 1 (by rfl) ⟨63083, by rfl⟩) R126167
theorem R84155 : Reach 84155 := rs (se 1 (by rfl) ⟨63116, by rfl⟩) R126233
theorem R84231 : Reach 84231 := rs (se 1 (by rfl) ⟨63173, by rfl⟩) R126347
theorem R2377997 : Reach 2377997 := rs (se 3 (by rfl) ⟨445874, by rfl⟩) R891749
theorem R84239 : Reach 84239 := rs (se 1 (by rfl) ⟨63179, by rfl⟩) R126359
theorem R84283 : Reach 84283 := rs (se 1 (by rfl) ⟨63212, by rfl⟩) R126425
theorem R84359 : Reach 84359 := rs (se 1 (by rfl) ⟨63269, by rfl⟩) R126539
theorem R84367 : Reach 84367 := rs (se 1 (by rfl) ⟨63275, by rfl⟩) R126551
theorem R182675 : Reach 182675 := rs (se 1 (by rfl) ⟨137006, by rfl⟩) R274013
theorem R84411 : Reach 84411 := rs (se 1 (by rfl) ⟨63308, by rfl⟩) R126617
theorem R84487 : Reach 84487 := rs (se 1 (by rfl) ⟨63365, by rfl⟩) R126731
theorem R84495 : Reach 84495 := rs (se 1 (by rfl) ⟨63371, by rfl⟩) R126743
theorem R84539 : Reach 84539 := rs (se 1 (by rfl) ⟨63404, by rfl⟩) R126809
theorem R379511 : Reach 379511 := rs (se 1 (by rfl) ⟨284633, by rfl⟩) R569267
theorem R84615 : Reach 84615 := rs (se 1 (by rfl) ⟨63461, by rfl⟩) R126923
theorem R84623 : Reach 84623 := rs (se 1 (by rfl) ⟨63467, by rfl⟩) R126935
theorem R84667 : Reach 84667 := rs (se 1 (by rfl) ⟨63500, by rfl⟩) R127001
theorem R84743 : Reach 84743 := rs (se 1 (by rfl) ⟨63557, by rfl⟩) R127115
theorem R84751 : Reach 84751 := rs (se 1 (by rfl) ⟨63563, by rfl⟩) R127127
theorem R84795 : Reach 84795 := rs (se 1 (by rfl) ⟨63596, by rfl⟩) R127193
theorem R84871 : Reach 84871 := rs (se 1 (by rfl) ⟨63653, by rfl⟩) R127307
theorem R84879 : Reach 84879 := rs (se 1 (by rfl) ⟨63659, by rfl⟩) R127319
theorem R84923 : Reach 84923 := rs (se 1 (by rfl) ⟨63692, by rfl⟩) R127385
theorem R740299 : Reach 740299 := rs (se 1 (by rfl) ⟨555224, by rfl⟩) R1110449
theorem R84999 : Reach 84999 := rs (se 1 (by rfl) ⟨63749, by rfl⟩) R127499
theorem R85007 : Reach 85007 := rs (se 1 (by rfl) ⟨63755, by rfl⟩) R127511
theorem R85051 : Reach 85051 := rs (se 1 (by rfl) ⟨63788, by rfl⟩) R127577
theorem R216179 : Reach 216179 := rs (se 1 (by rfl) ⟨162134, by rfl⟩) R324269
theorem R85127 : Reach 85127 := rs (se 1 (by rfl) ⟨63845, by rfl⟩) R127691
theorem R85135 : Reach 85135 := rs (se 1 (by rfl) ⟨63851, by rfl⟩) R127703
theorem R85179 : Reach 85179 := rs (se 1 (by rfl) ⟨63884, by rfl⟩) R127769
theorem R85255 : Reach 85255 := rs (se 1 (by rfl) ⟨63941, by rfl⟩) R127883
theorem R85263 : Reach 85263 := rs (se 1 (by rfl) ⟨63947, by rfl⟩) R127895
theorem R85307 : Reach 85307 := rs (se 1 (by rfl) ⟨63980, by rfl⟩) R127961
theorem R85383 : Reach 85383 := rs (se 1 (by rfl) ⟨64037, by rfl⟩) R128075
theorem R85391 : Reach 85391 := rs (se 1 (by rfl) ⟨64043, by rfl⟩) R128087
theorem R282041 : Reach 282041 := rs (se 2 (by rfl) ⟨105765, by rfl⟩) R211531
theorem R85435 : Reach 85435 := rs (se 1 (by rfl) ⟨64076, by rfl⟩) R128153
theorem R85511 : Reach 85511 := rs (se 1 (by rfl) ⟨64133, by rfl⟩) R128267
theorem R151055 : Reach 151055 := rs (se 1 (by rfl) ⟨113291, by rfl⟩) R226583
theorem R85519 : Reach 85519 := rs (se 1 (by rfl) ⟨64139, by rfl⟩) R128279
theorem R85563 : Reach 85563 := rs (se 1 (by rfl) ⟨64172, by rfl⟩) R128345
theorem R216695 : Reach 216695 := rs (se 1 (by rfl) ⟨162521, by rfl⟩) R325043
theorem R85639 : Reach 85639 := rs (se 1 (by rfl) ⟨64229, by rfl⟩) R128459
theorem R85647 : Reach 85647 := rs (se 1 (by rfl) ⟨64235, by rfl⟩) R128471
theorem R85691 : Reach 85691 := rs (se 1 (by rfl) ⟨64268, by rfl⟩) R128537
theorem R85767 : Reach 85767 := rs (se 1 (by rfl) ⟨64325, by rfl⟩) R128651
theorem R85775 : Reach 85775 := rs (se 1 (by rfl) ⟨64331, by rfl⟩) R128663
theorem R85819 : Reach 85819 := rs (se 1 (by rfl) ⟨64364, by rfl⟩) R128729
theorem R85895 : Reach 85895 := rs (se 1 (by rfl) ⟨64421, by rfl⟩) R128843
theorem R85903 : Reach 85903 := rs (se 1 (by rfl) ⟨64427, by rfl⟩) R128855
theorem R905111 : Reach 905111 := rs (se 1 (by rfl) ⟨678833, by rfl⟩) R1357667
theorem R85947 : Reach 85947 := rs (se 1 (by rfl) ⟨64460, by rfl⟩) R128921
theorem R86023 : Reach 86023 := rs (se 1 (by rfl) ⟨64517, by rfl⟩) R129035
theorem R282635 : Reach 282635 := rs (se 1 (by rfl) ⟨211976, by rfl⟩) R423953
theorem R86031 : Reach 86031 := rs (se 1 (by rfl) ⟨64523, by rfl⟩) R129047
theorem R86075 : Reach 86075 := rs (se 1 (by rfl) ⟨64556, by rfl⟩) R129113
theorem R282743 : Reach 282743 := rs (se 1 (by rfl) ⟨212057, by rfl⟩) R424115
theorem R86151 : Reach 86151 := rs (se 1 (by rfl) ⟨64613, by rfl⟩) R129227
theorem R86159 : Reach 86159 := rs (se 1 (by rfl) ⟨64619, by rfl⟩) R129239
theorem R86203 : Reach 86203 := rs (se 1 (by rfl) ⟨64652, by rfl⟩) R129305
theorem R86279 : Reach 86279 := rs (se 1 (by rfl) ⟨64709, by rfl⟩) R129419
theorem R86287 : Reach 86287 := rs (se 1 (by rfl) ⟨64715, by rfl⟩) R129431
theorem R86331 : Reach 86331 := rs (se 1 (by rfl) ⟨64748, by rfl⟩) R129497
theorem R643463 : Reach 643463 := rs (se 1 (by rfl) ⟨482597, by rfl⟩) R965195
theorem R86407 : Reach 86407 := rs (se 1 (by rfl) ⟨64805, by rfl⟩) R129611
theorem R86415 : Reach 86415 := rs (se 1 (by rfl) ⟨64811, by rfl⟩) R129623
theorem R2806163 : Reach 2806163 := rs (se 1 (by rfl) ⟨2104622, by rfl⟩) R4209245
theorem R86459 : Reach 86459 := rs (se 1 (by rfl) ⟨64844, by rfl⟩) R129689
theorem R86535 : Reach 86535 := rs (se 1 (by rfl) ⟨64901, by rfl⟩) R129803
theorem R86543 : Reach 86543 := rs (se 1 (by rfl) ⟨64907, by rfl⟩) R129815
theorem R86587 : Reach 86587 := rs (se 1 (by rfl) ⟨64940, by rfl⟩) R129881
theorem R217687 : Reach 217687 := rs (se 1 (by rfl) ⟨163265, by rfl⟩) R326531
theorem R119431 : Reach 119431 := rs (se 1 (by rfl) ⟨89573, by rfl⟩) R179147
theorem R86663 : Reach 86663 := rs (se 1 (by rfl) ⟨64997, by rfl⟩) R129995
theorem R86671 : Reach 86671 := rs (se 1 (by rfl) ⟨65003, by rfl⟩) R130007
theorem R86715 : Reach 86715 := rs (se 1 (by rfl) ⟨65036, by rfl⟩) R130073
theorem R283337 : Reach 283337 := rs (se 2 (by rfl) ⟨106251, by rfl⟩) R212503
theorem R86791 : Reach 86791 := rs (se 1 (by rfl) ⟨65093, by rfl⟩) R130187
theorem R86799 : Reach 86799 := rs (se 1 (by rfl) ⟨65099, by rfl⟩) R130199
theorem R414497 : Reach 414497 := rs (se 2 (by rfl) ⟨155436, by rfl⟩) R310873
theorem R86843 : Reach 86843 := rs (se 1 (by rfl) ⟨65132, by rfl⟩) R130265
theorem R316295 : Reach 316295 := rs (se 1 (by rfl) ⟨237221, by rfl⟩) R474443
theorem R217991 : Reach 217991 := rs (se 1 (by rfl) ⟨163493, by rfl⟩) R326987
theorem R86919 : Reach 86919 := rs (se 1 (by rfl) ⟨65189, by rfl⟩) R130379
theorem R86927 : Reach 86927 := rs (se 1 (by rfl) ⟨65195, by rfl⟩) R130391
theorem R86971 : Reach 86971 := rs (se 1 (by rfl) ⟨65228, by rfl⟩) R130457
theorem R87047 : Reach 87047 := rs (se 1 (by rfl) ⟨65285, by rfl⟩) R130571
theorem R218123 : Reach 218123 := rs (se 1 (by rfl) ⟨163592, by rfl⟩) R327185
theorem R87055 : Reach 87055 := rs (se 1 (by rfl) ⟨65291, by rfl⟩) R130583
theorem R87099 : Reach 87099 := rs (se 1 (by rfl) ⟨65324, by rfl⟩) R130649
theorem R284039 : Reach 284039 := rs (se 1 (by rfl) ⟨213029, by rfl⟩) R426059
theorem R120251 : Reach 120251 := rs (se 1 (by rfl) ⟨90188, by rfl⟩) R180377
theorem R218639 : Reach 218639 := rs (se 1 (by rfl) ⟨163979, by rfl⟩) R327959
theorem R317047 : Reach 317047 := rs (se 1 (by rfl) ⟨237785, by rfl⟩) R475571
theorem R218771 : Reach 218771 := rs (se 1 (by rfl) ⟨164078, by rfl⟩) R328157
theorem R677605 : Reach 677605 := rs (se 4 (by rfl) ⟨63525, by rfl⟩) R127051
theorem R284417 : Reach 284417 := rs (se 2 (by rfl) ⟨106656, by rfl⟩) R213313
theorem R907057 : Reach 907057 := rs (se 2 (by rfl) ⟨340146, by rfl⟩) R680293
theorem R120695 : Reach 120695 := rs (se 1 (by rfl) ⟨90521, by rfl⟩) R181043
theorem R415691 : Reach 415691 := rs (se 1 (by rfl) ⟨311768, by rfl⟩) R623537
theorem R120889 : Reach 120889 := rs (se 2 (by rfl) ⟨45333, by rfl⟩) R90667
theorem R1399133 : Reach 1399133 := rs (se 3 (by rfl) ⟨262337, by rfl⟩) R524675
theorem R285227 : Reach 285227 := rs (se 1 (by rfl) ⟨213920, by rfl⟩) R427841
theorem R219905 : Reach 219905 := rs (se 2 (by rfl) ⟨82464, by rfl⟩) R164929
theorem R187271 : Reach 187271 := rs (se 1 (by rfl) ⟨140453, by rfl⟩) R280907
theorem R482233 : Reach 482233 := rs (se 2 (by rfl) ⟨180837, by rfl⟩) R361675
theorem R89095 : Reach 89095 := rs (se 1 (by rfl) ⟨66821, by rfl⟩) R133643
theorem R187451 : Reach 187451 := rs (se 1 (by rfl) ⟨140588, by rfl⟩) R281177
theorem R220279 : Reach 220279 := rs (se 1 (by rfl) ⟨165209, by rfl⟩) R330419
theorem R187577 : Reach 187577 := rs (se 2 (by rfl) ⟨70341, by rfl⟩) R140683
theorem R351469 : Reach 351469 := rs (se 3 (by rfl) ⟨65900, by rfl⟩) R131801
theorem R155015 : Reach 155015 := rs (se 1 (by rfl) ⟨116261, by rfl⟩) R232523
theorem R679427 : Reach 679427 := rs (se 1 (by rfl) ⟨509570, by rfl⟩) R1019141
theorem R187919 : Reach 187919 := rs (se 1 (by rfl) ⟨140939, by rfl⟩) R281879
theorem R187937 : Reach 187937 := rs (se 2 (by rfl) ⟨70476, by rfl⟩) R140953
theorem R1335041 : Reach 1335041 := rs (se 2 (by rfl) ⟨500640, by rfl⟩) R1001281
theorem R89915 : Reach 89915 := rs (se 1 (by rfl) ⟨67436, by rfl⟩) R134873
theorem R286523 : Reach 286523 := rs (se 1 (by rfl) ⟨214892, by rfl⟩) R429785
theorem R188279 : Reach 188279 := rs (se 1 (by rfl) ⟨141209, by rfl⟩) R282419
theorem R188459 : Reach 188459 := rs (se 1 (by rfl) ⟨141344, by rfl⟩) R282689
theorem R287009 : Reach 287009 := rs (se 2 (by rfl) ⟨107628, by rfl⟩) R215257
theorem R549179 : Reach 549179 := rs (se 1 (by rfl) ⟨411884, by rfl⟩) R823769
theorem R1171805 : Reach 1171805 := rs (se 3 (by rfl) ⟨219713, by rfl⟩) R439427
theorem R188819 : Reach 188819 := rs (se 1 (by rfl) ⟨141614, by rfl⟩) R283229
theorem R451001 : Reach 451001 := rs (se 2 (by rfl) ⟨169125, by rfl⟩) R338251
theorem R188873 : Reach 188873 := rs (se 2 (by rfl) ⟨70827, by rfl⟩) R141655
theorem R221843 : Reach 221843 := rs (se 1 (by rfl) ⟨166382, by rfl⟩) R332765
theorem R287603 : Reach 287603 := rs (se 1 (by rfl) ⟨215702, by rfl⟩) R431405
theorem R123961 : Reach 123961 := rs (se 2 (by rfl) ⟨46485, by rfl⟩) R92971
theorem R189575 : Reach 189575 := rs (se 1 (by rfl) ⟨142181, by rfl⟩) R284363
theorem R189755 : Reach 189755 := rs (se 1 (by rfl) ⟨142316, by rfl⟩) R284633
theorem R222551 : Reach 222551 := rs (se 1 (by rfl) ⟨166913, by rfl⟩) R333827
theorem R91535 : Reach 91535 := rs (se 1 (by rfl) ⟨68651, by rfl⟩) R137303
theorem R189881 : Reach 189881 := rs (se 2 (by rfl) ⟨71205, by rfl⟩) R142411
theorem R190223 : Reach 190223 := rs (se 1 (by rfl) ⟨142667, by rfl⟩) R285335
theorem R190241 : Reach 190241 := rs (se 2 (by rfl) ⟨71340, by rfl⟩) R142681
theorem R386849 : Reach 386849 := rs (se 2 (by rfl) ⟨145068, by rfl⟩) R290137
theorem R124715 : Reach 124715 := rs (se 1 (by rfl) ⟨93536, by rfl⟩) R187073
theorem R124745 : Reach 124745 := rs (se 2 (by rfl) ⟨46779, by rfl⟩) R93559
theorem R124859 : Reach 124859 := rs (se 1 (by rfl) ⟨93644, by rfl⟩) R187289
theorem R124919 : Reach 124919 := rs (se 1 (by rfl) ⟨93689, by rfl⟩) R187379
theorem R124943 : Reach 124943 := rs (se 1 (by rfl) ⟨93707, by rfl⟩) R187415
theorem R124985 : Reach 124985 := rs (se 2 (by rfl) ⟨46869, by rfl⟩) R93739
theorem R190583 : Reach 190583 := rs (se 1 (by rfl) ⟨142937, by rfl⟩) R285875
theorem R125063 : Reach 125063 := rs (se 1 (by rfl) ⟨93797, by rfl⟩) R187595
theorem R125099 : Reach 125099 := rs (se 1 (by rfl) ⟨93824, by rfl⟩) R187649
theorem R125129 : Reach 125129 := rs (se 2 (by rfl) ⟨46923, by rfl⟩) R93847
theorem R92431 : Reach 92431 := rs (se 1 (by rfl) ⟨69323, by rfl⟩) R138647
theorem R190763 : Reach 190763 := rs (se 1 (by rfl) ⟨143072, by rfl⟩) R286145
theorem R125243 : Reach 125243 := rs (se 1 (by rfl) ⟨93932, by rfl⟩) R187865
theorem R125303 : Reach 125303 := rs (se 1 (by rfl) ⟨93977, by rfl⟩) R187955
theorem R158087 : Reach 158087 := rs (se 1 (by rfl) ⟨118565, by rfl⟩) R237131
theorem R125327 : Reach 125327 := rs (se 1 (by rfl) ⟨93995, by rfl⟩) R187991
theorem R125369 : Reach 125369 := rs (se 2 (by rfl) ⟨47013, by rfl⟩) R94027
theorem R322001 : Reach 322001 := rs (se 2 (by rfl) ⟨120750, by rfl⟩) R241501
theorem R125447 : Reach 125447 := rs (se 1 (by rfl) ⟨94085, by rfl⟩) R188171
theorem R125483 : Reach 125483 := rs (se 1 (by rfl) ⟨94112, by rfl⟩) R188225
theorem R125513 : Reach 125513 := rs (se 2 (by rfl) ⟨47067, by rfl⟩) R94135
theorem R191123 : Reach 191123 := rs (se 1 (by rfl) ⟨143342, by rfl⟩) R286685
theorem R125627 : Reach 125627 := rs (se 1 (by rfl) ⟨94220, by rfl⟩) R188441
theorem R191177 : Reach 191177 := rs (se 2 (by rfl) ⟨71691, by rfl⟩) R143383
theorem R125687 : Reach 125687 := rs (se 1 (by rfl) ⟨94265, by rfl⟩) R188531
theorem R125711 : Reach 125711 := rs (se 1 (by rfl) ⟨94283, by rfl⟩) R188567
theorem R551717 : Reach 551717 := rs (se 4 (by rfl) ⟨51723, by rfl⟩) R103447
theorem R125753 : Reach 125753 := rs (se 2 (by rfl) ⟨47157, by rfl⟩) R94315
theorem R486233 : Reach 486233 := rs (se 2 (by rfl) ⟨182337, by rfl⟩) R364675
theorem R125831 : Reach 125831 := rs (se 1 (by rfl) ⟨94373, by rfl⟩) R188747
theorem R158611 : Reach 158611 := rs (se 1 (by rfl) ⟨118958, by rfl⟩) R237917
theorem R125867 : Reach 125867 := rs (se 1 (by rfl) ⟨94400, by rfl⟩) R188801
theorem R125897 : Reach 125897 := rs (se 2 (by rfl) ⟨47211, by rfl⟩) R94423
theorem R420875 : Reach 420875 := rs (se 1 (by rfl) ⟨315656, by rfl⟩) R631313
theorem R257053 : Reach 257053 := rs (se 3 (by rfl) ⟨48197, by rfl⟩) R96395
theorem R126011 : Reach 126011 := rs (se 1 (by rfl) ⟨94508, by rfl⟩) R189017
theorem R126071 : Reach 126071 := rs (se 1 (by rfl) ⟨94553, by rfl⟩) R189107
theorem R126095 : Reach 126095 := rs (se 1 (by rfl) ⟨94571, by rfl⟩) R189143
theorem R421037 : Reach 421037 := rs (se 3 (by rfl) ⟨78944, by rfl⟩) R157889
theorem R126137 : Reach 126137 := rs (se 2 (by rfl) ⟨47301, by rfl⟩) R94603
theorem R126215 : Reach 126215 := rs (se 1 (by rfl) ⟨94661, by rfl⟩) R189323
theorem R126251 : Reach 126251 := rs (se 1 (by rfl) ⟨94688, by rfl⟩) R189377
theorem R126281 : Reach 126281 := rs (se 2 (by rfl) ⟨47355, by rfl⟩) R94711
theorem R191879 : Reach 191879 := rs (se 1 (by rfl) ⟨143909, by rfl⟩) R287819
theorem R191891 : Reach 191891 := rs (se 1 (by rfl) ⟨143918, by rfl⟩) R287837
theorem R290195 : Reach 290195 := rs (se 1 (by rfl) ⟨217646, by rfl⟩) R435293
theorem R126395 : Reach 126395 := rs (se 1 (by rfl) ⟨94796, by rfl⟩) R189593
theorem R126455 : Reach 126455 := rs (se 1 (by rfl) ⟨94841, by rfl⟩) R189683
theorem R93703 : Reach 93703 := rs (se 1 (by rfl) ⟨70277, by rfl⟩) R140555
theorem R126479 : Reach 126479 := rs (se 1 (by rfl) ⟨94859, by rfl⟩) R189719
theorem R126521 : Reach 126521 := rs (se 2 (by rfl) ⟨47445, by rfl⟩) R94891
theorem R192059 : Reach 192059 := rs (se 1 (by rfl) ⟨144044, by rfl⟩) R288089
theorem R814657 : Reach 814657 := rs (se 2 (by rfl) ⟨305496, by rfl⟩) R610993
theorem R126599 : Reach 126599 := rs (se 1 (by rfl) ⟨94949, by rfl⟩) R189899
theorem R126635 : Reach 126635 := rs (se 1 (by rfl) ⟨94976, by rfl⟩) R189953
theorem R192185 : Reach 192185 := rs (se 2 (by rfl) ⟨72069, by rfl⟩) R144139
theorem R93883 : Reach 93883 := rs (se 1 (by rfl) ⟨70412, by rfl⟩) R140825
theorem R126665 : Reach 126665 := rs (se 2 (by rfl) ⟨47499, by rfl⟩) R94999
theorem R454373 : Reach 454373 := rs (se 4 (by rfl) ⟨42597, by rfl⟩) R85195
theorem R126779 : Reach 126779 := rs (se 1 (by rfl) ⟨95084, by rfl⟩) R190169
theorem R388979 : Reach 388979 := rs (se 1 (by rfl) ⟨291734, by rfl⟩) R583469
theorem R126839 : Reach 126839 := rs (se 1 (by rfl) ⟨95129, by rfl⟩) R190259
theorem R126863 : Reach 126863 := rs (se 1 (by rfl) ⟨95147, by rfl⟩) R190295
theorem R454547 : Reach 454547 := rs (se 1 (by rfl) ⟨340910, by rfl⟩) R681821
theorem R126905 : Reach 126905 := rs (se 2 (by rfl) ⟨47589, by rfl⟩) R95179
theorem R126983 : Reach 126983 := rs (se 1 (by rfl) ⟨95237, by rfl⟩) R190475
theorem R192527 : Reach 192527 := rs (se 1 (by rfl) ⟨144395, by rfl⟩) R288791
theorem R192545 : Reach 192545 := rs (se 2 (by rfl) ⟨72204, by rfl⟩) R144409
theorem R127019 : Reach 127019 := rs (se 1 (by rfl) ⟨95264, by rfl⟩) R190529
theorem R159803 : Reach 159803 := rs (se 1 (by rfl) ⟨119852, by rfl⟩) R239705
theorem R356413 : Reach 356413 := rs (se 3 (by rfl) ⟨66827, by rfl⟩) R133655
theorem R127049 : Reach 127049 := rs (se 2 (by rfl) ⟨47643, by rfl⟩) R95287
theorem R94351 : Reach 94351 := rs (se 1 (by rfl) ⟨70763, by rfl⟩) R141527
theorem R127163 : Reach 127163 := rs (se 1 (by rfl) ⟨95372, by rfl⟩) R190745
theorem R127223 : Reach 127223 := rs (se 1 (by rfl) ⟨95417, by rfl⟩) R190835
theorem R127247 : Reach 127247 := rs (se 1 (by rfl) ⟨95435, by rfl⟩) R190871
theorem R127289 : Reach 127289 := rs (se 2 (by rfl) ⟨47733, by rfl⟩) R95467
theorem R192887 : Reach 192887 := rs (se 1 (by rfl) ⟨144665, by rfl⟩) R289331
theorem R127367 : Reach 127367 := rs (se 1 (by rfl) ⟨95525, by rfl⟩) R191051
theorem R127403 : Reach 127403 := rs (se 1 (by rfl) ⟨95552, by rfl⟩) R191105
theorem R127433 : Reach 127433 := rs (se 2 (by rfl) ⟨47787, by rfl⟩) R95575
theorem R487883 : Reach 487883 := rs (se 1 (by rfl) ⟨365912, by rfl⟩) R731825
theorem R160289 : Reach 160289 := rs (se 2 (by rfl) ⟨60108, by rfl⟩) R120217
theorem R193067 : Reach 193067 := rs (se 1 (by rfl) ⟨144800, by rfl⟩) R289601
theorem R127547 : Reach 127547 := rs (se 1 (by rfl) ⟨95660, by rfl⟩) R191321
theorem R127607 : Reach 127607 := rs (se 1 (by rfl) ⟨95705, by rfl⟩) R191411
theorem R94855 : Reach 94855 := rs (se 1 (by rfl) ⟨71141, by rfl⟩) R142283
theorem R127631 : Reach 127631 := rs (se 1 (by rfl) ⟨95723, by rfl⟩) R191447
theorem R127673 : Reach 127673 := rs (se 2 (by rfl) ⟨47877, by rfl⟩) R95755
theorem R422657 : Reach 422657 := rs (se 2 (by rfl) ⟨158496, by rfl⟩) R316993
theorem R127751 : Reach 127751 := rs (se 1 (by rfl) ⟨95813, by rfl⟩) R191627
theorem R291599 : Reach 291599 := rs (se 1 (by rfl) ⟨218699, by rfl⟩) R437399
theorem R160555 : Reach 160555 := rs (se 1 (by rfl) ⟨120416, by rfl⟩) R240833
theorem R127787 : Reach 127787 := rs (se 1 (by rfl) ⟨95840, by rfl⟩) R191681
theorem R95035 : Reach 95035 := rs (se 1 (by rfl) ⟨71276, by rfl⟩) R142553
theorem R389947 : Reach 389947 := rs (se 1 (by rfl) ⟨292460, by rfl⟩) R584921
theorem R127817 : Reach 127817 := rs (se 2 (by rfl) ⟨47931, by rfl⟩) R95863
theorem R488339 : Reach 488339 := rs (se 1 (by rfl) ⟨366254, by rfl⟩) R732509
theorem R193427 : Reach 193427 := rs (se 1 (by rfl) ⟨145070, by rfl⟩) R290141
theorem R291737 : Reach 291737 := rs (se 2 (by rfl) ⟨109401, by rfl⟩) R218803
theorem R127931 : Reach 127931 := rs (se 1 (by rfl) ⟨95948, by rfl⟩) R191897
theorem R193481 : Reach 193481 := rs (se 2 (by rfl) ⟨72555, by rfl⟩) R145111
theorem R127991 : Reach 127991 := rs (se 1 (by rfl) ⟨95993, by rfl⟩) R191987
theorem R128015 : Reach 128015 := rs (se 1 (by rfl) ⟨96011, by rfl⟩) R192023
theorem R291869 : Reach 291869 := rs (se 3 (by rfl) ⟨54725, by rfl⟩) R109451
theorem R128057 : Reach 128057 := rs (se 2 (by rfl) ⟨48021, by rfl⟩) R96043
theorem R128135 : Reach 128135 := rs (se 1 (by rfl) ⟨96101, by rfl⟩) R192203
theorem R128171 : Reach 128171 := rs (se 1 (by rfl) ⟨96128, by rfl⟩) R192257
theorem R128201 : Reach 128201 := rs (se 2 (by rfl) ⟨48075, by rfl⟩) R96151
theorem R95503 : Reach 95503 := rs (se 1 (by rfl) ⟨71627, by rfl⟩) R143255
theorem R128299 : Reach 128299 := rs (se 1 (by rfl) ⟨96224, by rfl⟩) R192449
theorem R128315 : Reach 128315 := rs (se 1 (by rfl) ⟨96236, by rfl⟩) R192473
theorem R128375 : Reach 128375 := rs (se 1 (by rfl) ⟨96281, by rfl⟩) R192563
theorem R128399 : Reach 128399 := rs (se 1 (by rfl) ⟨96299, by rfl⟩) R192599
theorem R128441 : Reach 128441 := rs (se 2 (by rfl) ⟨48165, by rfl⟩) R96331
theorem R325073 : Reach 325073 := rs (se 2 (by rfl) ⟨121902, by rfl⟩) R243805
theorem R128519 : Reach 128519 := rs (se 1 (by rfl) ⟨96389, by rfl⟩) R192779
theorem R423467 : Reach 423467 := rs (se 1 (by rfl) ⟨317600, by rfl⟩) R635201
theorem R128555 : Reach 128555 := rs (se 1 (by rfl) ⟨96416, by rfl⟩) R192833
theorem R128585 : Reach 128585 := rs (se 2 (by rfl) ⟨48219, by rfl⟩) R96439
theorem R194183 : Reach 194183 := rs (se 1 (by rfl) ⟨145637, by rfl⟩) R291275
theorem R128699 : Reach 128699 := rs (se 1 (by rfl) ⟨96524, by rfl⟩) R193049
theorem R128759 : Reach 128759 := rs (se 1 (by rfl) ⟨96569, by rfl⟩) R193139
theorem R96007 : Reach 96007 := rs (se 1 (by rfl) ⟨72005, by rfl⟩) R144011
theorem R227087 : Reach 227087 := rs (se 1 (by rfl) ⟨170315, by rfl⟩) R340631
theorem R128783 : Reach 128783 := rs (se 1 (by rfl) ⟨96587, by rfl⟩) R193175
theorem R128825 : Reach 128825 := rs (se 2 (by rfl) ⟨48309, by rfl⟩) R96619
theorem R194363 : Reach 194363 := rs (se 1 (by rfl) ⟨145772, by rfl⟩) R291545
theorem R161671 : Reach 161671 := rs (se 1 (by rfl) ⟨121253, by rfl⟩) R242507
theorem R128903 : Reach 128903 := rs (se 1 (by rfl) ⟨96677, by rfl⟩) R193355
theorem R325529 : Reach 325529 := rs (se 2 (by rfl) ⟨122073, by rfl⟩) R244147
theorem R128939 : Reach 128939 := rs (se 1 (by rfl) ⟨96704, by rfl⟩) R193409
theorem R194489 : Reach 194489 := rs (se 2 (by rfl) ⟨72933, by rfl⟩) R145867
theorem R96187 : Reach 96187 := rs (se 1 (by rfl) ⟨72140, by rfl⟩) R144281
theorem R128969 : Reach 128969 := rs (se 2 (by rfl) ⟨48363, by rfl⟩) R96727
theorem R260111 : Reach 260111 := rs (se 1 (by rfl) ⟨195083, by rfl⟩) R390167
theorem R129083 : Reach 129083 := rs (se 1 (by rfl) ⟨96812, by rfl⟩) R193625
theorem R129143 : Reach 129143 := rs (se 1 (by rfl) ⟨96857, by rfl⟩) R193715
theorem R129167 : Reach 129167 := rs (se 1 (by rfl) ⟨96875, by rfl⟩) R193751
theorem R129209 : Reach 129209 := rs (se 2 (by rfl) ⟨48453, by rfl⟩) R96907
theorem R129287 : Reach 129287 := rs (se 1 (by rfl) ⟨96965, by rfl⟩) R193931
theorem R194831 : Reach 194831 := rs (se 1 (by rfl) ⟨146123, by rfl⟩) R292247
theorem R194849 : Reach 194849 := rs (se 2 (by rfl) ⟨73068, by rfl⟩) R146137
theorem R129323 : Reach 129323 := rs (se 1 (by rfl) ⟨96992, by rfl⟩) R193985
theorem R129353 : Reach 129353 := rs (se 2 (by rfl) ⟨48507, by rfl⟩) R97015
theorem R522611 : Reach 522611 := rs (se 1 (by rfl) ⟨391958, by rfl⟩) R783917
theorem R96655 : Reach 96655 := rs (se 1 (by rfl) ⟨72491, by rfl⟩) R144983
theorem R293273 : Reach 293273 := rs (se 2 (by rfl) ⟨109977, by rfl⟩) R219955
theorem R162233 : Reach 162233 := rs (se 2 (by rfl) ⟨60837, by rfl⟩) R121675
theorem R129467 : Reach 129467 := rs (se 1 (by rfl) ⟨97100, by rfl⟩) R194201
theorem R2980313 : Reach 2980313 := rs (se 2 (by rfl) ⟨1117617, by rfl⟩) R2235235
theorem R129527 : Reach 129527 := rs (se 1 (by rfl) ⟨97145, by rfl⟩) R194291
theorem R129551 : Reach 129551 := rs (se 1 (by rfl) ⟨97163, by rfl⟩) R194327
theorem R129593 : Reach 129593 := rs (se 2 (by rfl) ⟨48597, by rfl⟩) R97195
theorem R195191 : Reach 195191 := rs (se 1 (by rfl) ⟨146393, by rfl⟩) R292787
theorem R129671 : Reach 129671 := rs (se 1 (by rfl) ⟨97253, by rfl⟩) R194507
theorem R129707 : Reach 129707 := rs (se 1 (by rfl) ⟨97280, by rfl⟩) R194561
theorem R359113 : Reach 359113 := rs (se 2 (by rfl) ⟨134667, by rfl⟩) R269335
theorem R129737 : Reach 129737 := rs (se 2 (by rfl) ⟨48651, by rfl⟩) R97303
theorem R195371 : Reach 195371 := rs (se 1 (by rfl) ⟨146528, by rfl⟩) R293057
theorem R424763 : Reach 424763 := rs (se 1 (by rfl) ⟨318572, by rfl⟩) R637145
theorem R129851 : Reach 129851 := rs (se 1 (by rfl) ⟨97388, by rfl⟩) R194777
theorem R129911 : Reach 129911 := rs (se 1 (by rfl) ⟨97433, by rfl⟩) R194867
theorem R97159 : Reach 97159 := rs (se 1 (by rfl) ⟨72869, by rfl⟩) R145739
theorem R129935 : Reach 129935 := rs (se 1 (by rfl) ⟨97451, by rfl⟩) R194903
theorem R129977 : Reach 129977 := rs (se 2 (by rfl) ⟨48741, by rfl⟩) R97483
theorem R424925 : Reach 424925 := rs (se 3 (by rfl) ⟨79673, by rfl⟩) R159347
theorem R130055 : Reach 130055 := rs (se 1 (by rfl) ⟨97541, by rfl⟩) R195083
theorem R326699 : Reach 326699 := rs (se 1 (by rfl) ⟨245024, by rfl⟩) R490049
theorem R130091 : Reach 130091 := rs (se 1 (by rfl) ⟨97568, by rfl⟩) R195137
theorem R97339 : Reach 97339 := rs (se 1 (by rfl) ⟨73004, by rfl⟩) R146009
theorem R130121 : Reach 130121 := rs (se 2 (by rfl) ⟨48795, by rfl⟩) R97591
theorem R293975 : Reach 293975 := rs (se 1 (by rfl) ⟨220481, by rfl⟩) R440963
theorem R195731 : Reach 195731 := rs (se 1 (by rfl) ⟨146798, by rfl⟩) R293597
theorem R130235 : Reach 130235 := rs (se 1 (by rfl) ⟨97676, by rfl⟩) R195353
theorem R195785 : Reach 195785 := rs (se 2 (by rfl) ⟨73419, by rfl⟩) R146839
theorem R130295 : Reach 130295 := rs (se 1 (by rfl) ⟨97721, by rfl⟩) R195443
theorem R261377 : Reach 261377 := rs (se 2 (by rfl) ⟨98016, by rfl⟩) R196033
theorem R130319 : Reach 130319 := rs (se 1 (by rfl) ⟨97739, by rfl⟩) R195479
theorem R425249 : Reach 425249 := rs (se 2 (by rfl) ⟨159468, by rfl⟩) R318937
theorem R130361 : Reach 130361 := rs (se 2 (by rfl) ⟨48885, by rfl⟩) R97771
theorem R195959 : Reach 195959 := rs (se 1 (by rfl) ⟨146969, by rfl⟩) R293939
theorem R130439 : Reach 130439 := rs (se 1 (by rfl) ⟨97829, by rfl⟩) R195659
theorem R130475 : Reach 130475 := rs (se 1 (by rfl) ⟨97856, by rfl⟩) R195713
theorem R130505 : Reach 130505 := rs (se 2 (by rfl) ⟨48939, by rfl⟩) R97879
theorem R130567 : Reach 130567 := rs (se 1 (by rfl) ⟨97925, by rfl⟩) R195851
theorem R97807 : Reach 97807 := rs (se 1 (by rfl) ⟨73355, by rfl⟩) R146711
theorem R720413 : Reach 720413 := rs (se 3 (by rfl) ⟨135077, by rfl⟩) R270155
theorem R163387 : Reach 163387 := rs (se 1 (by rfl) ⟨122540, by rfl⟩) R245081
theorem R130619 : Reach 130619 := rs (se 1 (by rfl) ⟨97964, by rfl⟩) R195929
theorem R130679 : Reach 130679 := rs (se 1 (by rfl) ⟨98009, by rfl⟩) R196019
theorem R163919 : Reach 163919 := rs (se 1 (by rfl) ⟨122939, by rfl⟩) R245879
theorem R721163 : Reach 721163 := rs (se 1 (by rfl) ⟨540872, by rfl⟩) R1081745
theorem R262543 : Reach 262543 := rs (se 1 (by rfl) ⟨196907, by rfl⟩) R393815
theorem R459245 : Reach 459245 := rs (se 3 (by rfl) ⟨86108, by rfl⟩) R172217
theorem R164359 : Reach 164359 := rs (se 1 (by rfl) ⟨123269, by rfl⟩) R246539
theorem R2228795 : Reach 2228795 := rs (se 1 (by rfl) ⟨1671596, by rfl⟩) R3343193
theorem R426707 : Reach 426707 := rs (se 1 (by rfl) ⟨320030, by rfl⟩) R640061
theorem R459475 : Reach 459475 := rs (se 1 (by rfl) ⟨344606, by rfl⟩) R689213
theorem R328711 : Reach 328711 := rs (se 1 (by rfl) ⟨246533, by rfl⟩) R493067
theorem R590915 : Reach 590915 := rs (se 1 (by rfl) ⟨443186, by rfl⟩) R886373
theorem R197711 : Reach 197711 := rs (se 1 (by rfl) ⟨148283, by rfl⟩) R296567
theorem R296335 : Reach 296335 := rs (se 1 (by rfl) ⟨222251, by rfl⟩) R444503
theorem R165281 : Reach 165281 := rs (se 2 (by rfl) ⟨61980, by rfl⟩) R123961
theorem R492965 : Reach 492965 := rs (se 4 (by rfl) ⟨46215, by rfl⟩) R92431
theorem R198587 : Reach 198587 := rs (se 1 (by rfl) ⟨148940, by rfl⟩) R297881
theorem R657665 : Reach 657665 := rs (se 2 (by rfl) ⟨246624, by rfl⟩) R493249
theorem R100703 : Reach 100703 := rs (se 1 (by rfl) ⟨75527, by rfl⟩) R151055
theorem R428975 : Reach 428975 := rs (se 1 (by rfl) ⟨321731, by rfl⟩) R643463
theorem R1870775 : Reach 1870775 := rs (se 1 (by rfl) ⟨1403081, by rfl⟩) R2806163
theorem R363521 : Reach 363521 := rs (se 2 (by rfl) ⟨136320, by rfl⟩) R272641
theorem R855539 : Reach 855539 := rs (se 1 (by rfl) ⟨641654, by rfl⟩) R1283309
theorem R3346109 : Reach 3346109 := rs (se 3 (by rfl) ⟨627395, by rfl⟩) R1254791
theorem R200407 : Reach 200407 := rs (se 1 (by rfl) ⟨150305, by rfl⟩) R300611
theorem R987065 : Reach 987065 := rs (se 2 (by rfl) ⟨370149, by rfl⟩) R740299
theorem R266951 : Reach 266951 := rs (se 1 (by rfl) ⟨200213, by rfl⟩) R400427
theorem R1086209 : Reach 1086209 := rs (se 2 (by rfl) ⟨407328, by rfl⟩) R814657
theorem R332651 : Reach 332651 := rs (se 1 (by rfl) ⟨249488, by rfl⟩) R498977
theorem R627601 : Reach 627601 := rs (se 2 (by rfl) ⟨235350, by rfl⟩) R470701
theorem R103343 : Reach 103343 := rs (se 1 (by rfl) ⟨77507, by rfl⟩) R155015
theorem R890027 : Reach 890027 := rs (se 1 (by rfl) ⟨667520, by rfl⟩) R1335041
theorem R693629 : Reach 693629 := rs (se 3 (by rfl) ⟨130055, by rfl⟩) R260111
theorem R136667 : Reach 136667 := rs (se 1 (by rfl) ⟨102500, by rfl⟩) R205001
theorem R366119 : Reach 366119 := rs (se 1 (by rfl) ⟨274589, by rfl⟩) R549179
theorem R300667 : Reach 300667 := rs (se 1 (by rfl) ⟨225500, by rfl⟩) R451001
theorem R268105 : Reach 268105 := rs (se 2 (by rfl) ⟨100539, by rfl⟩) R201079
theorem R137143 : Reach 137143 := rs (se 1 (by rfl) ⟨102857, by rfl⟩) R205715
theorem R203251 : Reach 203251 := rs (se 1 (by rfl) ⟨152438, by rfl⟩) R304877
theorem R891425 : Reach 891425 := rs (se 2 (by rfl) ⟨334284, by rfl⟩) R668569
theorem R1874501 : Reach 1874501 := rs (se 4 (by rfl) ⟨175734, by rfl⟩) R351469
theorem R400081 : Reach 400081 := rs (se 2 (by rfl) ⟨150030, by rfl⟩) R300061
theorem R989981 : Reach 989981 := rs (se 3 (by rfl) ⟨185621, by rfl⟩) R371243
theorem R138089 : Reach 138089 := rs (se 2 (by rfl) ⟨51783, by rfl⟩) R103567
theorem R105391 : Reach 105391 := rs (se 1 (by rfl) ⟨79043, by rfl⟩) R158087
theorem R171065 : Reach 171065 := rs (se 2 (by rfl) ⟨64149, by rfl⟩) R128299
theorem R597071 : Reach 597071 := rs (se 1 (by rfl) ⟨447803, by rfl⟩) R895607
theorem R367811 : Reach 367811 := rs (se 1 (by rfl) ⟨275858, by rfl⟩) R551717
theorem R466319 : Reach 466319 := rs (se 1 (by rfl) ⟨349739, by rfl⟩) R699479
theorem R401041 : Reach 401041 := rs (se 2 (by rfl) ⟨150390, by rfl⟩) R300781
theorem R302915 : Reach 302915 := rs (se 1 (by rfl) ⟨227186, by rfl⟩) R454373
theorem R303031 : Reach 303031 := rs (se 1 (by rfl) ⟨227273, by rfl⟩) R454547
theorem R106535 : Reach 106535 := rs (se 1 (by rfl) ⟨79901, by rfl⟩) R159803
theorem R106859 : Reach 106859 := rs (se 1 (by rfl) ⟨80144, by rfl⟩) R160289
theorem R205751 : Reach 205751 := rs (se 1 (by rfl) ⟨154313, by rfl⟩) R308627
theorem R205903 : Reach 205903 := rs (se 1 (by rfl) ⟨154427, by rfl⟩) R308855
theorem R140879 : Reach 140879 := rs (se 1 (by rfl) ⟨105659, by rfl⟩) R211319
theorem R108155 : Reach 108155 := rs (se 1 (by rfl) ⟨81116, by rfl⟩) R162233
theorem R174089 : Reach 174089 := rs (se 2 (by rfl) ⟨65283, by rfl⟩) R130567
theorem R239773 : Reach 239773 := rs (se 3 (by rfl) ⟨44957, by rfl⟩) R89915
theorem R305309 : Reach 305309 := rs (se 3 (by rfl) ⟨57245, by rfl⟩) R114491
theorem R174251 : Reach 174251 := rs (se 1 (by rfl) ⟨130688, by rfl⟩) R261377
theorem R272783 : Reach 272783 := rs (se 1 (by rfl) ⟨204587, by rfl⟩) R409175
theorem R141743 : Reach 141743 := rs (se 1 (by rfl) ⟨106307, by rfl⟩) R212615
theorem R142175 : Reach 142175 := rs (se 1 (by rfl) ⟨106631, by rfl⟩) R213263
theorem R240479 : Reach 240479 := rs (se 1 (by rfl) ⟨180359, by rfl⟩) R360719
theorem R1551251 : Reach 1551251 := rs (se 1 (by rfl) ⟨1163438, by rfl⟩) R2326877
theorem R2698211 : Reach 2698211 := rs (se 1 (by rfl) ⟨2023658, by rfl⟩) R4047317
theorem R535747 : Reach 535747 := rs (se 1 (by rfl) ⟨401810, by rfl⟩) R803621
theorem R142735 : Reach 142735 := rs (se 1 (by rfl) ⟨107051, by rfl⟩) R214103
theorem R437723 : Reach 437723 := rs (se 1 (by rfl) ⟨328292, by rfl⟩) R656585
theorem R3124813 : Reach 3124813 := rs (se 3 (by rfl) ⟨585902, by rfl⟩) R1171805
theorem R208595 : Reach 208595 := rs (se 1 (by rfl) ⟨156446, by rfl⟩) R312893
theorem R241481 : Reach 241481 := rs (se 2 (by rfl) ⟨90555, by rfl⟩) R181111
theorem R438209 : Reach 438209 := rs (se 2 (by rfl) ⟨164328, by rfl⟩) R328657
theorem R143417 : Reach 143417 := rs (se 2 (by rfl) ⟨53781, by rfl⟩) R107563
theorem R1585331 : Reach 1585331 := rs (se 1 (by rfl) ⟨1188998, by rfl⟩) R2377997
theorem R144119 : Reach 144119 := rs (se 1 (by rfl) ⟨108089, by rfl⟩) R216179
theorem R144463 : Reach 144463 := rs (se 1 (by rfl) ⟨108347, by rfl⟩) R216695
theorem R963737 : Reach 963737 := rs (se 2 (by rfl) ⟨361401, by rfl⟩) R722803
theorem R603407 : Reach 603407 := rs (se 1 (by rfl) ⟨452555, by rfl⟩) R905111
theorem R144713 : Reach 144713 := rs (se 2 (by rfl) ⟨54267, by rfl⟩) R108535
theorem R145145 : Reach 145145 := rs (se 2 (by rfl) ⟨54429, by rfl⟩) R108859
theorem R210863 : Reach 210863 := rs (se 1 (by rfl) ⟨158147, by rfl⟩) R316295
theorem R145327 : Reach 145327 := rs (se 1 (by rfl) ⟨108995, by rfl⟩) R217991
theorem R145415 : Reach 145415 := rs (se 1 (by rfl) ⟨109061, by rfl⟩) R218123
theorem R505871 : Reach 505871 := rs (se 1 (by rfl) ⟨379403, by rfl⟩) R758807
theorem R440477 : Reach 440477 := rs (se 3 (by rfl) ⟨82589, by rfl⟩) R165179
theorem R145759 : Reach 145759 := rs (se 1 (by rfl) ⟨109319, by rfl⟩) R218639
theorem R1227113 : Reach 1227113 := rs (se 2 (by rfl) ⟨460167, by rfl⟩) R920335
theorem R145847 : Reach 145847 := rs (se 1 (by rfl) ⟨109385, by rfl⟩) R218771
theorem R211481 : Reach 211481 := rs (se 2 (by rfl) ⟨79305, by rfl⟩) R158611
theorem R277127 : Reach 277127 := rs (se 1 (by rfl) ⟨207845, by rfl⟩) R415691
theorem R342737 : Reach 342737 := rs (se 2 (by rfl) ⟨128526, by rfl⟩) R257053
theorem R932755 : Reach 932755 := rs (se 1 (by rfl) ⟨699566, by rfl⟩) R1399133
theorem R539621 : Reach 539621 := rs (se 4 (by rfl) ⟨50589, by rfl⟩) R101179
theorem R408577 : Reach 408577 := rs (se 2 (by rfl) ⟨153216, by rfl⟩) R306433
theorem R146441 : Reach 146441 := rs (se 2 (by rfl) ⟨54915, by rfl⟩) R109831
theorem R146603 : Reach 146603 := rs (se 1 (by rfl) ⟨109952, by rfl⟩) R219905
theorem R310817 : Reach 310817 := rs (se 2 (by rfl) ⟨116556, by rfl⟩) R233113
theorem R147001 : Reach 147001 := rs (se 2 (by rfl) ⟨55125, by rfl⟩) R110251
theorem R704123 : Reach 704123 := rs (se 1 (by rfl) ⟨528092, by rfl⟩) R1056185
theorem R638603 : Reach 638603 := rs (se 1 (by rfl) ⟨478952, by rfl⟩) R957905
theorem R310931 : Reach 310931 := rs (se 1 (by rfl) ⟨233198, by rfl⟩) R466397
theorem R311033 : Reach 311033 := rs (se 2 (by rfl) ⟨116637, by rfl⟩) R233275
theorem R1228729 : Reach 1228729 := rs (se 2 (by rfl) ⟨460773, by rfl⟩) R921547
theorem R475217 : Reach 475217 := rs (se 2 (by rfl) ⟨178206, by rfl⟩) R356413
theorem R1982789 : Reach 1982789 := rs (se 4 (by rfl) ⟨185886, by rfl⟩) R371773
theorem R409961 : Reach 409961 := rs (se 2 (by rfl) ⟨153735, by rfl⟩) R307471
theorem R147895 : Reach 147895 := rs (se 1 (by rfl) ⟨110921, by rfl⟩) R221843
theorem R246311 : Reach 246311 := rs (se 1 (by rfl) ⟨184733, by rfl⟩) R369467
theorem R115561 : Reach 115561 := rs (se 2 (by rfl) ⟨43335, by rfl⟩) R86671
theorem R148367 : Reach 148367 := rs (se 1 (by rfl) ⟨111275, by rfl⟩) R222551
theorem R214073 : Reach 214073 := rs (se 2 (by rfl) ⟨80277, by rfl⟩) R160555
theorem R83143 : Reach 83143 := rs (se 1 (by rfl) ⟨62357, by rfl⟩) R124715
theorem R83163 : Reach 83163 := rs (se 1 (by rfl) ⟨62372, by rfl⟩) R124745
theorem R83239 : Reach 83239 := rs (se 1 (by rfl) ⟨62429, by rfl⟩) R124859
theorem R83279 : Reach 83279 := rs (se 1 (by rfl) ⟨62459, by rfl⟩) R124919
theorem R83295 : Reach 83295 := rs (se 1 (by rfl) ⟨62471, by rfl⟩) R124943
theorem R83323 : Reach 83323 := rs (se 1 (by rfl) ⟨62492, by rfl⟩) R124985
theorem R83375 : Reach 83375 := rs (se 1 (by rfl) ⟨62531, by rfl⟩) R125063
theorem R83399 : Reach 83399 := rs (se 1 (by rfl) ⟨62549, by rfl⟩) R125099
theorem R83419 : Reach 83419 := rs (se 1 (by rfl) ⟨62564, by rfl⟩) R125129
theorem R83495 : Reach 83495 := rs (se 1 (by rfl) ⟨62621, by rfl⟩) R125243
theorem R83535 : Reach 83535 := rs (se 1 (by rfl) ⟨62651, by rfl⟩) R125303
theorem R83551 : Reach 83551 := rs (se 1 (by rfl) ⟨62663, by rfl⟩) R125327
theorem R83579 : Reach 83579 := rs (se 1 (by rfl) ⟨62684, by rfl⟩) R125369
theorem R214667 : Reach 214667 := rs (se 1 (by rfl) ⟨161000, by rfl⟩) R322001
theorem R83631 : Reach 83631 := rs (se 1 (by rfl) ⟨62723, by rfl⟩) R125447
theorem R83655 : Reach 83655 := rs (se 1 (by rfl) ⟨62741, by rfl⟩) R125483
theorem R83675 : Reach 83675 := rs (se 1 (by rfl) ⟨62756, by rfl⟩) R125513
theorem R83751 : Reach 83751 := rs (se 1 (by rfl) ⟨62813, by rfl⟩) R125627
theorem R149321 : Reach 149321 := rs (se 2 (by rfl) ⟨55995, by rfl⟩) R111991
theorem R83791 : Reach 83791 := rs (se 1 (by rfl) ⟨62843, by rfl⟩) R125687
theorem R83807 : Reach 83807 := rs (se 1 (by rfl) ⟨62855, by rfl⟩) R125711
theorem R83835 : Reach 83835 := rs (se 1 (by rfl) ⟨62876, by rfl⟩) R125753
theorem R83887 : Reach 83887 := rs (se 1 (by rfl) ⟨62915, by rfl⟩) R125831
theorem R83911 : Reach 83911 := rs (se 1 (by rfl) ⟨62933, by rfl⟩) R125867
theorem R83931 : Reach 83931 := rs (se 1 (by rfl) ⟨62948, by rfl⟩) R125897
theorem R280583 : Reach 280583 := rs (se 1 (by rfl) ⟨210437, by rfl⟩) R420875
theorem R84007 : Reach 84007 := rs (se 1 (by rfl) ⟨63005, by rfl⟩) R126011
theorem R84047 : Reach 84047 := rs (se 1 (by rfl) ⟨63035, by rfl⟩) R126071
theorem R84063 : Reach 84063 := rs (se 1 (by rfl) ⟨63047, by rfl⟩) R126095
theorem R280691 : Reach 280691 := rs (se 1 (by rfl) ⟨210518, by rfl⟩) R421037
theorem R84091 : Reach 84091 := rs (se 1 (by rfl) ⟨63068, by rfl⟩) R126137
theorem R84143 : Reach 84143 := rs (se 1 (by rfl) ⟨63107, by rfl⟩) R126215
theorem R84167 : Reach 84167 := rs (se 1 (by rfl) ⟨63125, by rfl⟩) R126251
theorem R84187 : Reach 84187 := rs (se 1 (by rfl) ⟨63140, by rfl⟩) R126281
theorem R84263 : Reach 84263 := rs (se 1 (by rfl) ⟨63197, by rfl⟩) R126395
theorem R903473 : Reach 903473 := rs (se 2 (by rfl) ⟨338802, by rfl⟩) R677605
theorem R84303 : Reach 84303 := rs (se 1 (by rfl) ⟨63227, by rfl⟩) R126455
theorem R84319 : Reach 84319 := rs (se 1 (by rfl) ⟨63239, by rfl⟩) R126479
theorem R84347 : Reach 84347 := rs (se 1 (by rfl) ⟨63260, by rfl⟩) R126521
theorem R280961 : Reach 280961 := rs (se 2 (by rfl) ⟨105360, by rfl⟩) R210721
theorem R84399 : Reach 84399 := rs (se 1 (by rfl) ⟨63299, by rfl⟩) R126599
theorem R84423 : Reach 84423 := rs (se 1 (by rfl) ⟨63317, by rfl⟩) R126635
theorem R84443 : Reach 84443 := rs (se 1 (by rfl) ⟨63332, by rfl⟩) R126665
theorem R477677 : Reach 477677 := rs (se 3 (by rfl) ⟨89564, by rfl⟩) R179129
theorem R215561 : Reach 215561 := rs (se 2 (by rfl) ⟨80835, by rfl⟩) R161671
theorem R84519 : Reach 84519 := rs (se 1 (by rfl) ⟨63389, by rfl⟩) R126779
theorem R84559 : Reach 84559 := rs (se 1 (by rfl) ⟨63419, by rfl⟩) R126839
theorem R84575 : Reach 84575 := rs (se 1 (by rfl) ⟨63431, by rfl⟩) R126863
theorem R84603 : Reach 84603 := rs (se 1 (by rfl) ⟨63452, by rfl⟩) R126905
theorem R84655 : Reach 84655 := rs (se 1 (by rfl) ⟨63491, by rfl⟩) R126983
theorem R84679 : Reach 84679 := rs (se 1 (by rfl) ⟨63509, by rfl⟩) R127019
theorem R84699 : Reach 84699 := rs (se 1 (by rfl) ⟨63524, by rfl⟩) R127049
theorem R84775 : Reach 84775 := rs (se 1 (by rfl) ⟨63581, by rfl⟩) R127163
theorem R84815 : Reach 84815 := rs (se 1 (by rfl) ⟨63611, by rfl⟩) R127223
theorem R84831 : Reach 84831 := rs (se 1 (by rfl) ⟨63623, by rfl⟩) R127247
theorem R84859 : Reach 84859 := rs (se 1 (by rfl) ⟨63644, by rfl⟩) R127289
theorem R84911 : Reach 84911 := rs (se 1 (by rfl) ⟨63683, by rfl⟩) R127367
theorem R84935 : Reach 84935 := rs (se 1 (by rfl) ⟨63701, by rfl⟩) R127403
theorem R84955 : Reach 84955 := rs (se 1 (by rfl) ⟨63716, by rfl⟩) R127433
theorem R85031 : Reach 85031 := rs (se 1 (by rfl) ⟨63773, by rfl⟩) R127547
theorem R85071 : Reach 85071 := rs (se 1 (by rfl) ⟨63803, by rfl⟩) R127607
theorem R85087 : Reach 85087 := rs (se 1 (by rfl) ⟨63815, by rfl⟩) R127631
theorem R85115 : Reach 85115 := rs (se 1 (by rfl) ⟨63836, by rfl⟩) R127673
theorem R281771 : Reach 281771 := rs (se 1 (by rfl) ⟨211328, by rfl⟩) R422657
theorem R85167 : Reach 85167 := rs (se 1 (by rfl) ⟨63875, by rfl⟩) R127751
theorem R85191 : Reach 85191 := rs (se 1 (by rfl) ⟨63893, by rfl⟩) R127787
theorem R85211 : Reach 85211 := rs (se 1 (by rfl) ⟨63908, by rfl⟩) R127817
theorem R85287 : Reach 85287 := rs (se 1 (by rfl) ⟨63965, by rfl⟩) R127931
theorem R85327 : Reach 85327 := rs (se 1 (by rfl) ⟨63995, by rfl⟩) R127991
theorem R85343 : Reach 85343 := rs (se 1 (by rfl) ⟨64007, by rfl⟩) R128015
theorem R85371 : Reach 85371 := rs (se 1 (by rfl) ⟨64028, by rfl⟩) R128057
theorem R85423 : Reach 85423 := rs (se 1 (by rfl) ⟨64067, by rfl⟩) R128135
theorem R85447 : Reach 85447 := rs (se 1 (by rfl) ⟨64085, by rfl⟩) R128171
theorem R85467 : Reach 85467 := rs (se 1 (by rfl) ⟨64100, by rfl⟩) R128201
theorem R85543 : Reach 85543 := rs (se 1 (by rfl) ⟨64157, by rfl⟩) R128315
theorem R85583 : Reach 85583 := rs (se 1 (by rfl) ⟨64187, by rfl⟩) R128375
theorem R85599 : Reach 85599 := rs (se 1 (by rfl) ⟨64199, by rfl⟩) R128399
theorem R478817 : Reach 478817 := rs (se 2 (by rfl) ⟨179556, by rfl⟩) R359113
theorem R85627 : Reach 85627 := rs (se 1 (by rfl) ⟨64220, by rfl⟩) R128441
theorem R216715 : Reach 216715 := rs (se 1 (by rfl) ⟨162536, by rfl⟩) R325073
theorem R85679 : Reach 85679 := rs (se 1 (by rfl) ⟨64259, by rfl⟩) R128519
theorem R282311 : Reach 282311 := rs (se 1 (by rfl) ⟨211733, by rfl⟩) R423467
theorem R85703 : Reach 85703 := rs (se 1 (by rfl) ⟨64277, by rfl⟩) R128555
theorem R85723 : Reach 85723 := rs (se 1 (by rfl) ⟨64292, by rfl⟩) R128585
theorem R85799 : Reach 85799 := rs (se 1 (by rfl) ⟨64349, by rfl⟩) R128699
theorem R85839 : Reach 85839 := rs (se 1 (by rfl) ⟨64379, by rfl⟩) R128759
theorem R151391 : Reach 151391 := rs (se 1 (by rfl) ⟨113543, by rfl⟩) R227087
theorem R85855 : Reach 85855 := rs (se 1 (by rfl) ⟨64391, by rfl⟩) R128783
theorem R85883 : Reach 85883 := rs (se 1 (by rfl) ⟨64412, by rfl⟩) R128825
theorem R642977 : Reach 642977 := rs (se 2 (by rfl) ⟨241116, by rfl⟩) R482233
theorem R85935 : Reach 85935 := rs (se 1 (by rfl) ⟨64451, by rfl⟩) R128903
theorem R217019 : Reach 217019 := rs (se 1 (by rfl) ⟨162764, by rfl⟩) R325529
theorem R85959 : Reach 85959 := rs (se 1 (by rfl) ⟨64469, by rfl⟩) R128939
theorem R85979 : Reach 85979 := rs (se 1 (by rfl) ⟨64484, by rfl⟩) R128969
theorem R118793 : Reach 118793 := rs (se 2 (by rfl) ⟨44547, by rfl⟩) R89095
theorem R86055 : Reach 86055 := rs (se 1 (by rfl) ⟨64541, by rfl⟩) R129083
theorem R86095 : Reach 86095 := rs (se 1 (by rfl) ⟨64571, by rfl⟩) R129143
theorem R86111 : Reach 86111 := rs (se 1 (by rfl) ⟨64583, by rfl⟩) R129167
theorem R86139 : Reach 86139 := rs (se 1 (by rfl) ⟨64604, by rfl⟩) R129209
theorem R86191 : Reach 86191 := rs (se 1 (by rfl) ⟨64643, by rfl⟩) R129287
theorem R86215 : Reach 86215 := rs (se 1 (by rfl) ⟨64661, by rfl⟩) R129323
theorem R86235 : Reach 86235 := rs (se 1 (by rfl) ⟨64676, by rfl⟩) R129353
theorem R348407 : Reach 348407 := rs (se 1 (by rfl) ⟨261305, by rfl⟩) R522611
theorem R4837637 : Reach 4837637 := rs (se 4 (by rfl) ⟨453528, by rfl⟩) R907057
theorem R86311 : Reach 86311 := rs (se 1 (by rfl) ⟨64733, by rfl⟩) R129467
theorem R1986875 : Reach 1986875 := rs (se 1 (by rfl) ⟨1490156, by rfl⟩) R2980313
theorem R86351 : Reach 86351 := rs (se 1 (by rfl) ⟨64763, by rfl⟩) R129527
theorem R86367 : Reach 86367 := rs (se 1 (by rfl) ⟨64775, by rfl⟩) R129551
theorem R86395 : Reach 86395 := rs (se 1 (by rfl) ⟨64796, by rfl⟩) R129593
theorem R86447 : Reach 86447 := rs (se 1 (by rfl) ⟨64835, by rfl⟩) R129671
theorem R86471 : Reach 86471 := rs (se 1 (by rfl) ⟨64853, by rfl⟩) R129707
theorem R86491 : Reach 86491 := rs (se 1 (by rfl) ⟨64868, by rfl⟩) R129737
theorem R283175 : Reach 283175 := rs (se 1 (by rfl) ⟨212381, by rfl⟩) R424763
theorem R86567 : Reach 86567 := rs (se 1 (by rfl) ⟨64925, by rfl⟩) R129851
theorem R86607 : Reach 86607 := rs (se 1 (by rfl) ⟨64955, by rfl⟩) R129911
theorem R86623 : Reach 86623 := rs (se 1 (by rfl) ⟨64967, by rfl⟩) R129935
theorem R86651 : Reach 86651 := rs (se 1 (by rfl) ⟨64988, by rfl⟩) R129977
theorem R283283 : Reach 283283 := rs (se 1 (by rfl) ⟨212462, by rfl⟩) R424925
theorem R86703 : Reach 86703 := rs (se 1 (by rfl) ⟨65027, by rfl⟩) R130055
theorem R217799 : Reach 217799 := rs (se 1 (by rfl) ⟨163349, by rfl⟩) R326699
theorem R86727 : Reach 86727 := rs (se 1 (by rfl) ⟨65045, by rfl⟩) R130091
theorem R86747 : Reach 86747 := rs (se 1 (by rfl) ⟨65060, by rfl⟩) R130121
theorem R217849 : Reach 217849 := rs (se 2 (by rfl) ⟨81693, by rfl⟩) R163387
theorem R86823 : Reach 86823 := rs (se 1 (by rfl) ⟨65117, by rfl⟩) R130235
theorem R185161 : Reach 185161 := rs (se 2 (by rfl) ⟨69435, by rfl⟩) R138871
theorem R86863 : Reach 86863 := rs (se 1 (by rfl) ⟨65147, by rfl⟩) R130295
theorem R119647 : Reach 119647 := rs (se 1 (by rfl) ⟨89735, by rfl⟩) R179471
theorem R86879 : Reach 86879 := rs (se 1 (by rfl) ⟨65159, by rfl⟩) R130319
theorem R283499 : Reach 283499 := rs (se 1 (by rfl) ⟨212624, by rfl⟩) R425249
theorem R119659 : Reach 119659 := rs (se 1 (by rfl) ⟨89744, by rfl⟩) R179489
theorem R86907 : Reach 86907 := rs (se 1 (by rfl) ⟨65180, by rfl⟩) R130361
theorem R283553 : Reach 283553 := rs (se 2 (by rfl) ⟨106332, by rfl⟩) R212665
theorem R86959 : Reach 86959 := rs (se 1 (by rfl) ⟨65219, by rfl⟩) R130439
theorem R86983 : Reach 86983 := rs (se 1 (by rfl) ⟨65237, by rfl⟩) R130475
theorem R87003 : Reach 87003 := rs (se 1 (by rfl) ⟨65252, by rfl⟩) R130505
theorem R480275 : Reach 480275 := rs (se 1 (by rfl) ⟨360206, by rfl⟩) R720413
theorem R87079 : Reach 87079 := rs (se 1 (by rfl) ⟨65309, by rfl⟩) R130619
theorem R87119 : Reach 87119 := rs (se 1 (by rfl) ⟨65339, by rfl⟩) R130679
theorem R218497 : Reach 218497 := rs (se 2 (by rfl) ⟨81936, by rfl⟩) R163873
theorem R873929 : Reach 873929 := rs (se 2 (by rfl) ⟨327723, by rfl⟩) R655447
theorem R284147 : Reach 284147 := rs (se 1 (by rfl) ⟨213110, by rfl⟩) R426221
theorem R153505 : Reach 153505 := rs (se 2 (by rfl) ⟨57564, by rfl⟩) R115129
theorem R415751 : Reach 415751 := rs (se 1 (by rfl) ⟨311813, by rfl⟩) R623627
theorem R284687 : Reach 284687 := rs (se 1 (by rfl) ⟨213515, by rfl⟩) R427031
theorem R546905 : Reach 546905 := rs (se 2 (by rfl) ⟨205089, by rfl⟩) R410179
theorem R350365 : Reach 350365 := rs (se 3 (by rfl) ⟨65693, by rfl⟩) R131387
theorem R219307 : Reach 219307 := rs (se 1 (by rfl) ⟨164480, by rfl⟩) R328961
theorem R317783 : Reach 317783 := rs (se 1 (by rfl) ⟨238337, by rfl⟩) R476675
theorem R711017 : Reach 711017 := rs (se 2 (by rfl) ⟨266631, by rfl⟩) R533263
theorem R1628549 : Reach 1628549 := rs (se 4 (by rfl) ⟨152676, by rfl⟩) R305353
theorem R219611 : Reach 219611 := rs (se 1 (by rfl) ⟨164708, by rfl⟩) R329417
theorem R285281 : Reach 285281 := rs (se 2 (by rfl) ⟨106980, by rfl⟩) R213961
theorem R187091 : Reach 187091 := rs (se 1 (by rfl) ⟨140318, by rfl⟩) R280637
theorem R318163 : Reach 318163 := rs (se 1 (by rfl) ⟨238622, by rfl⟩) R477245
theorem R482051 : Reach 482051 := rs (se 1 (by rfl) ⟨361538, by rfl⟩) R723077
theorem R253007 : Reach 253007 := rs (se 1 (by rfl) ⟨189755, by rfl⟩) R379511
theorem R482507 : Reach 482507 := rs (se 1 (by rfl) ⟨361880, by rfl⟩) R723761
theorem R1105325 : Reach 1105325 := rs (se 3 (by rfl) ⟨207248, by rfl⟩) R414497
theorem R188027 : Reach 188027 := rs (se 1 (by rfl) ⟨141020, by rfl⟩) R282041
theorem R188153 : Reach 188153 := rs (se 2 (by rfl) ⟨70557, by rfl⟩) R141115
theorem R483191 : Reach 483191 := rs (se 1 (by rfl) ⟨362393, by rfl⟩) R724787
theorem R679873 : Reach 679873 := rs (se 2 (by rfl) ⟨254952, by rfl⟩) R509905
theorem R188423 : Reach 188423 := rs (se 1 (by rfl) ⟨141317, by rfl⟩) R282635
theorem R286739 : Reach 286739 := rs (se 1 (by rfl) ⟨215054, by rfl⟩) R430109
theorem R188495 : Reach 188495 := rs (se 1 (by rfl) ⟨141371, by rfl⟩) R282743
theorem R287063 : Reach 287063 := rs (se 1 (by rfl) ⟨215297, by rfl⟩) R430595
theorem R188891 : Reach 188891 := rs (se 1 (by rfl) ⟨141668, by rfl⟩) R283337
theorem R189359 : Reach 189359 := rs (se 1 (by rfl) ⟨142019, by rfl⟩) R284039
theorem R320669 : Reach 320669 := rs (se 3 (by rfl) ⟨60125, by rfl⟩) R120251
theorem R189611 : Reach 189611 := rs (se 1 (by rfl) ⟨142208, by rfl⟩) R284417
theorem R91487 : Reach 91487 := rs (se 1 (by rfl) ⟨68615, by rfl⟩) R137231
theorem R484733 : Reach 484733 := rs (se 3 (by rfl) ⟨90887, by rfl⟩) R181775
theorem R288143 : Reach 288143 := rs (se 1 (by rfl) ⟨216107, by rfl⟩) R432215
theorem R976373 : Reach 976373 := rs (se 5 (by rfl) ⟨45767, by rfl⟩) R91535
theorem R190151 : Reach 190151 := rs (se 1 (by rfl) ⟨142613, by rfl⟩) R285227
theorem R288467 : Reach 288467 := rs (se 1 (by rfl) ⟨216350, by rfl⟩) R432701
theorem R321353 : Reach 321353 := rs (se 2 (by rfl) ⟨120507, by rfl⟩) R241015
theorem R223049 : Reach 223049 := rs (se 2 (by rfl) ⟨83643, by rfl⟩) R167287
theorem R124847 : Reach 124847 := rs (se 1 (by rfl) ⟨93635, by rfl⟩) R187271
theorem R223163 : Reach 223163 := rs (se 1 (by rfl) ⟨167372, by rfl⟩) R334745
theorem R124937 : Reach 124937 := rs (se 2 (by rfl) ⟨46851, by rfl⟩) R93703
theorem R124967 : Reach 124967 := rs (se 1 (by rfl) ⟨93725, by rfl⟩) R187451
theorem R125051 : Reach 125051 := rs (se 1 (by rfl) ⟨93788, by rfl⟩) R187577
theorem R551069 : Reach 551069 := rs (se 3 (by rfl) ⟨103325, by rfl⟩) R206651
theorem R157943 : Reach 157943 := rs (se 1 (by rfl) ⟨118457, by rfl⟩) R236915
theorem R125177 : Reach 125177 := rs (se 2 (by rfl) ⟨46941, by rfl⟩) R93883
theorem R321853 : Reach 321853 := rs (se 3 (by rfl) ⟨60347, by rfl⟩) R120695
theorem R452951 : Reach 452951 := rs (se 1 (by rfl) ⟨339713, by rfl⟩) R679427
theorem R125279 : Reach 125279 := rs (se 1 (by rfl) ⟨93959, by rfl⟩) R187919
theorem R125291 : Reach 125291 := rs (se 1 (by rfl) ⟨93968, by rfl⟩) R187937
theorem R3631513 : Reach 3631513 := rs (se 2 (by rfl) ⟨1361817, by rfl⟩) R2723635
theorem R191015 : Reach 191015 := rs (se 1 (by rfl) ⟨143261, by rfl⟩) R286523
theorem R125519 : Reach 125519 := rs (se 1 (by rfl) ⟨94139, by rfl⟩) R188279
theorem R125639 : Reach 125639 := rs (se 1 (by rfl) ⟨94229, by rfl⟩) R188459
theorem R125801 : Reach 125801 := rs (se 2 (by rfl) ⟨47175, by rfl⟩) R94351
theorem R191339 : Reach 191339 := rs (se 1 (by rfl) ⟨143504, by rfl⟩) R287009
theorem R289655 : Reach 289655 := rs (se 1 (by rfl) ⟨217241, by rfl⟩) R434483
theorem R191393 : Reach 191393 := rs (se 2 (by rfl) ⟨71772, by rfl⟩) R143545
theorem R125879 : Reach 125879 := rs (se 1 (by rfl) ⟨94409, by rfl⟩) R188819
theorem R125915 : Reach 125915 := rs (se 1 (by rfl) ⟨94436, by rfl⟩) R188873
theorem R289871 : Reach 289871 := rs (se 1 (by rfl) ⟨217403, by rfl⟩) R434807
theorem R191735 : Reach 191735 := rs (se 1 (by rfl) ⟨143801, by rfl⟩) R287603
theorem R126383 : Reach 126383 := rs (se 1 (by rfl) ⟨94787, by rfl⟩) R189575
theorem R290249 : Reach 290249 := rs (se 2 (by rfl) ⟨108843, by rfl⟩) R217687
theorem R159241 : Reach 159241 := rs (se 2 (by rfl) ⟨59715, by rfl⟩) R119431
theorem R126473 : Reach 126473 := rs (se 2 (by rfl) ⟨47427, by rfl⟩) R94855
theorem R126503 : Reach 126503 := rs (se 1 (by rfl) ⟨94877, by rfl⟩) R189755
theorem R93775 : Reach 93775 := rs (se 1 (by rfl) ⟨70331, by rfl⟩) R140663
theorem R126587 : Reach 126587 := rs (se 1 (by rfl) ⟨94940, by rfl⟩) R189881
theorem R421523 : Reach 421523 := rs (se 1 (by rfl) ⟨316142, by rfl⟩) R632285
theorem R290519 : Reach 290519 := rs (se 1 (by rfl) ⟨217889, by rfl⟩) R435779
theorem R487133 : Reach 487133 := rs (se 3 (by rfl) ⟨91337, by rfl⟩) R182675
theorem R126713 : Reach 126713 := rs (se 2 (by rfl) ⟨47517, by rfl⟩) R95035
theorem R519929 : Reach 519929 := rs (se 2 (by rfl) ⟨194973, by rfl⟩) R389947
theorem R192329 : Reach 192329 := rs (se 2 (by rfl) ⟨72123, by rfl⟩) R144247
theorem R159583 : Reach 159583 := rs (se 1 (by rfl) ⟨119687, by rfl⟩) R239375
theorem R126815 : Reach 126815 := rs (se 1 (by rfl) ⟨95111, by rfl⟩) R190223
theorem R126827 : Reach 126827 := rs (se 1 (by rfl) ⟨95120, by rfl⟩) R190241
theorem R257899 : Reach 257899 := rs (se 1 (by rfl) ⟨193424, by rfl⟩) R386849
theorem R290735 : Reach 290735 := rs (se 1 (by rfl) ⟨218051, by rfl⟩) R436103
theorem R94171 : Reach 94171 := rs (se 1 (by rfl) ⟨70628, by rfl⟩) R141257
theorem R323585 : Reach 323585 := rs (se 2 (by rfl) ⟨121344, by rfl⟩) R242689
theorem R127055 : Reach 127055 := rs (se 1 (by rfl) ⟨95291, by rfl⟩) R190583
theorem R127175 : Reach 127175 := rs (se 1 (by rfl) ⟨95381, by rfl⟩) R190763
theorem R618839 : Reach 618839 := rs (se 1 (by rfl) ⟨464129, by rfl⟩) R928259
theorem R127337 : Reach 127337 := rs (se 2 (by rfl) ⟨47751, by rfl⟩) R95503
theorem R94639 : Reach 94639 := rs (se 1 (by rfl) ⟨70979, by rfl⟩) R141959
theorem R127415 : Reach 127415 := rs (se 1 (by rfl) ⟨95561, by rfl⟩) R191123
theorem R127451 : Reach 127451 := rs (se 1 (by rfl) ⟨95588, by rfl⟩) R191177
theorem R324155 : Reach 324155 := rs (se 1 (by rfl) ⟨243116, by rfl⟩) R486233
theorem R193121 : Reach 193121 := rs (se 2 (by rfl) ⟨72420, by rfl⟩) R144841
theorem R357149 : Reach 357149 := rs (se 3 (by rfl) ⟨66965, by rfl⟩) R133931
theorem R422729 : Reach 422729 := rs (se 2 (by rfl) ⟨158523, by rfl⟩) R317047
theorem R95071 : Reach 95071 := rs (se 1 (by rfl) ⟨71303, by rfl⟩) R142607
theorem R127919 : Reach 127919 := rs (se 1 (by rfl) ⟨95939, by rfl⟩) R191879
theorem R127927 : Reach 127927 := rs (se 1 (by rfl) ⟨95945, by rfl⟩) R191891
theorem R193463 : Reach 193463 := rs (se 1 (by rfl) ⟨145097, by rfl⟩) R290195
theorem R160699 : Reach 160699 := rs (se 1 (by rfl) ⟨120524, by rfl⟩) R241049
theorem R160775 : Reach 160775 := rs (se 1 (by rfl) ⟨120581, by rfl⟩) R241163
theorem R128009 : Reach 128009 := rs (se 2 (by rfl) ⟨48003, by rfl⟩) R96007
theorem R128039 : Reach 128039 := rs (se 1 (by rfl) ⟨96029, by rfl⟩) R192059
theorem R128123 : Reach 128123 := rs (se 1 (by rfl) ⟨96092, by rfl⟩) R192185
theorem R95431 : Reach 95431 := rs (se 1 (by rfl) ⟨71573, by rfl⟩) R143147
theorem R259319 : Reach 259319 := rs (se 1 (by rfl) ⟨194489, by rfl⟩) R388979
theorem R128249 : Reach 128249 := rs (se 2 (by rfl) ⟨48093, by rfl⟩) R96187
theorem R128351 : Reach 128351 := rs (se 1 (by rfl) ⟨96263, by rfl⟩) R192527
theorem R128363 : Reach 128363 := rs (se 1 (by rfl) ⟨96272, by rfl⟩) R192545
theorem R161185 : Reach 161185 := rs (se 2 (by rfl) ⟨60444, by rfl⟩) R120889
theorem R194057 : Reach 194057 := rs (se 2 (by rfl) ⟨72771, by rfl⟩) R145543
theorem R128591 : Reach 128591 := rs (se 1 (by rfl) ⟨96443, by rfl⟩) R192887
theorem R325255 : Reach 325255 := rs (se 1 (by rfl) ⟨243941, by rfl⟩) R487883
theorem R128711 : Reach 128711 := rs (se 1 (by rfl) ⟨96533, by rfl⟩) R193067
theorem R161527 : Reach 161527 := rs (se 1 (by rfl) ⟨121145, by rfl⟩) R242291
theorem R194399 : Reach 194399 := rs (se 1 (by rfl) ⟨145799, by rfl⟩) R291599
theorem R128873 : Reach 128873 := rs (se 2 (by rfl) ⟨48327, by rfl⟩) R96655
theorem R325559 : Reach 325559 := rs (se 1 (by rfl) ⟨244169, by rfl⟩) R488339
theorem R128951 : Reach 128951 := rs (se 1 (by rfl) ⟨96713, by rfl⟩) R193427
theorem R194491 : Reach 194491 := rs (se 1 (by rfl) ⟨145868, by rfl⟩) R291737
theorem R128987 : Reach 128987 := rs (se 1 (by rfl) ⟨96740, by rfl⟩) R193481
theorem R194579 : Reach 194579 := rs (se 1 (by rfl) ⟨145934, by rfl⟩) R291869
theorem R161831 : Reach 161831 := rs (se 1 (by rfl) ⟨121373, by rfl⟩) R242747
theorem R96295 : Reach 96295 := rs (se 1 (by rfl) ⟨72221, by rfl⟩) R144443
theorem R293111 : Reach 293111 := rs (se 1 (by rfl) ⟨219833, by rfl⟩) R439667
theorem R1407233 : Reach 1407233 := rs (se 2 (by rfl) ⟨527712, by rfl⟩) R1055425
theorem R522557 : Reach 522557 := rs (se 3 (by rfl) ⟨97979, by rfl⟩) R195959
theorem R194921 : Reach 194921 := rs (se 2 (by rfl) ⟨73095, by rfl⟩) R146191
theorem R1112453 : Reach 1112453 := rs (se 4 (by rfl) ⟨104292, by rfl⟩) R208585
theorem R129455 : Reach 129455 := rs (se 1 (by rfl) ⟨97091, by rfl⟩) R194183
theorem R129545 : Reach 129545 := rs (se 2 (by rfl) ⟨48579, by rfl⟩) R97159
theorem R129575 : Reach 129575 := rs (se 1 (by rfl) ⟨97181, by rfl⟩) R194363
theorem R293435 : Reach 293435 := rs (se 1 (by rfl) ⟨220076, by rfl⟩) R440153
theorem R129659 : Reach 129659 := rs (se 1 (by rfl) ⟨97244, by rfl⟩) R194489
theorem R621229 : Reach 621229 := rs (se 3 (by rfl) ⟨116480, by rfl⟩) R232961
theorem R129785 : Reach 129785 := rs (se 2 (by rfl) ⟨48669, by rfl⟩) R97339
theorem R293705 : Reach 293705 := rs (se 2 (by rfl) ⟨110139, by rfl⟩) R220279
theorem R129887 : Reach 129887 := rs (se 1 (by rfl) ⟨97415, by rfl⟩) R194831
theorem R129899 : Reach 129899 := rs (se 1 (by rfl) ⟨97424, by rfl⟩) R194849
theorem R195515 : Reach 195515 := rs (se 1 (by rfl) ⟨146636, by rfl⟩) R293273
theorem R326713 : Reach 326713 := rs (se 2 (by rfl) ⟨122517, by rfl⟩) R245035
theorem R195641 : Reach 195641 := rs (se 2 (by rfl) ⟨73365, by rfl⟩) R146731
theorem R130127 : Reach 130127 := rs (se 1 (by rfl) ⟨97595, by rfl⟩) R195191
theorem R130247 : Reach 130247 := rs (se 1 (by rfl) ⟨97685, by rfl⟩) R195371
theorem R327017 : Reach 327017 := rs (se 2 (by rfl) ⟨122631, by rfl⟩) R245263
theorem R130409 : Reach 130409 := rs (se 2 (by rfl) ⟨48903, by rfl⟩) R97807
theorem R195983 : Reach 195983 := rs (se 1 (by rfl) ⟨146987, by rfl⟩) R293975
theorem R130487 : Reach 130487 := rs (se 1 (by rfl) ⟨97865, by rfl⟩) R195731
theorem R7044569 : Reach 7044569 := rs (se 2 (by rfl) ⟨2641713, by rfl⟩) R5283427
theorem R130523 : Reach 130523 := rs (se 1 (by rfl) ⟨97892, by rfl⟩) R195785
theorem R97915 : Reach 97915 := rs (se 1 (by rfl) ⟨73436, by rfl⟩) R146873
theorem R163691 : Reach 163691 := rs (se 1 (by rfl) ⟨122768, by rfl⟩) R245537
theorem R164207 : Reach 164207 := rs (se 1 (by rfl) ⟨123155, by rfl⟩) R246311
theorem R98911 : Reach 98911 := rs (se 1 (by rfl) ⟨74183, by rfl⟩) R148367
theorem R393943 : Reach 393943 := rs (se 1 (by rfl) ⟨295457, by rfl⟩) R590915
theorem R131807 : Reach 131807 := rs (se 1 (by rfl) ⟨98855, by rfl⟩) R197711
theorem R328643 : Reach 328643 := rs (se 1 (by rfl) ⟨246482, by rfl⟩) R492965
theorem R132391 : Reach 132391 := rs (se 1 (by rfl) ⟨99293, by rfl⟩) R198587
theorem R395113 : Reach 395113 := rs (se 2 (by rfl) ⟨148167, by rfl⟩) R296335
theorem R1247183 : Reach 1247183 := rs (se 1 (by rfl) ⟨935387, by rfl⟩) R1870775
theorem R788773 : Reach 788773 := rs (se 4 (by rfl) ⟨73947, by rfl⟩) R147895
theorem R2230739 : Reach 2230739 := rs (se 1 (by rfl) ⟨1673054, by rfl⟩) R3346109
theorem R100927 : Reach 100927 := rs (se 1 (by rfl) ⟨75695, by rfl⟩) R151391
theorem R428651 : Reach 428651 := rs (se 1 (by rfl) ⟨321488, by rfl⟩) R642977
theorem R658043 : Reach 658043 := rs (se 1 (by rfl) ⟨493532, by rfl⟩) R987065
theorem R232271 : Reach 232271 := rs (se 1 (by rfl) ⟨174203, by rfl⟩) R348407
theorem R429137 : Reach 429137 := rs (se 2 (by rfl) ⟨160926, by rfl⟩) R321853
theorem R724139 : Reach 724139 := rs (se 1 (by rfl) ⟨543104, by rfl⟩) R1086209
theorem R691517 : Reach 691517 := rs (se 3 (by rfl) ⟨129659, by rfl⟩) R259319
theorem R1609085 : Reach 1609085 := rs (se 3 (by rfl) ⟨301703, by rfl⟩) R603407
theorem R593351 : Reach 593351 := rs (se 1 (by rfl) ⟨445013, by rfl⟩) R890027
theorem R462419 : Reach 462419 := rs (se 1 (by rfl) ⟨346814, by rfl⟩) R693629
theorem R2330477 : Reach 2330477 := rs (se 3 (by rfl) ⟨436964, by rfl⟩) R873929
theorem R364445 : Reach 364445 := rs (se 3 (by rfl) ⟨68333, by rfl⟩) R136667
theorem R364603 : Reach 364603 := rs (se 1 (by rfl) ⟨273452, by rfl⟩) R546905
theorem R1085699 : Reach 1085699 := rs (se 1 (by rfl) ⟨814274, by rfl⟩) R1628549
theorem R1249667 : Reach 1249667 := rs (se 1 (by rfl) ⟨937250, by rfl⟩) R1874501
theorem R659987 : Reach 659987 := rs (se 1 (by rfl) ⟨494990, by rfl⟩) R989981
theorem R168671 : Reach 168671 := rs (se 1 (by rfl) ⟨126503, by rfl⟩) R253007
theorem R398047 : Reach 398047 := rs (se 1 (by rfl) ⟨298535, by rfl⟩) R597071
theorem R4166417 : Reach 4166417 := rs (se 2 (by rfl) ⟨1562406, by rfl⟩) R3124813
theorem R398189 : Reach 398189 := rs (se 3 (by rfl) ⟨74660, by rfl⟩) R149321
theorem R463781 : Reach 463781 := rs (se 4 (by rfl) ⟨43479, by rfl⟩) R86959
theorem R267209 : Reach 267209 := rs (se 2 (by rfl) ⟨100203, by rfl⟩) R200407
theorem R201943 : Reach 201943 := rs (se 1 (by rfl) ⟨151457, by rfl⟩) R302915
theorem R464237 : Reach 464237 := rs (se 3 (by rfl) ⟨87044, by rfl⟩) R174089
theorem R268541 : Reach 268541 := rs (se 3 (by rfl) ⟨50351, by rfl⟩) R100703
theorem R170569 : Reach 170569 := rs (se 2 (by rfl) ⟨63963, by rfl⟩) R127927
theorem R367379 : Reach 367379 := rs (se 1 (by rfl) ⟨275534, by rfl⟩) R551069
theorem R105295 : Reach 105295 := rs (se 1 (by rfl) ⟨78971, by rfl⟩) R157943
theorem R301967 : Reach 301967 := rs (se 1 (by rfl) ⟨226475, by rfl⟩) R452951
theorem R400889 : Reach 400889 := rs (se 2 (by rfl) ⟨150333, by rfl⟩) R300667
theorem R433673 : Reach 433673 := rs (se 2 (by rfl) ⟨162627, by rfl⟩) R325255
theorem R139063 : Reach 139063 := rs (se 1 (by rfl) ⟨104297, by rfl⟩) R208595
theorem R204673 : Reach 204673 := rs (se 2 (by rfl) ⟨76752, by rfl⟩) R153505
theorem R1056887 : Reach 1056887 := rs (se 1 (by rfl) ⟨792665, by rfl⟩) R1585331
theorem R467153 : Reach 467153 := rs (se 2 (by rfl) ⟨175182, by rfl⟩) R350365
theorem R238099 : Reach 238099 := rs (se 1 (by rfl) ⟨178574, by rfl⟩) R357149
theorem R271001 : Reach 271001 := rs (se 2 (by rfl) ⟨101625, by rfl⟩) R203251
theorem R107183 : Reach 107183 := rs (se 1 (by rfl) ⟨80387, by rfl⟩) R160775
theorem R2138885 : Reach 2138885 := rs (se 4 (by rfl) ⟨200520, by rfl⟩) R401041
theorem R828305 : Reach 828305 := rs (se 2 (by rfl) ⟨310614, by rfl⟩) R621229
theorem R533441 : Reach 533441 := rs (se 2 (by rfl) ⟨200040, by rfl⟩) R400081
theorem R140521 : Reach 140521 := rs (se 2 (by rfl) ⟨52695, by rfl⟩) R105391
theorem R140575 : Reach 140575 := rs (se 1 (by rfl) ⟨105431, by rfl⟩) R210863
theorem R337247 : Reach 337247 := rs (se 1 (by rfl) ⟨252935, by rfl⟩) R505871
theorem R107887 : Reach 107887 := rs (se 1 (by rfl) ⟨80915, by rfl⟩) R161831
theorem R435617 : Reach 435617 := rs (se 2 (by rfl) ⟨163356, by rfl⟩) R326713
theorem R140987 : Reach 140987 := rs (se 1 (by rfl) ⟨105740, by rfl⟩) R211481
theorem R4696379 : Reach 4696379 := rs (se 1 (by rfl) ⟨3522284, by rfl⟩) R7044569
theorem R207211 : Reach 207211 := rs (se 1 (by rfl) ⟨155408, by rfl⟩) R310817
theorem R469415 : Reach 469415 := rs (se 1 (by rfl) ⟨352061, by rfl⟩) R704123
theorem R207287 : Reach 207287 := rs (se 1 (by rfl) ⟨155465, by rfl⟩) R310931
theorem R207355 : Reach 207355 := rs (se 1 (by rfl) ⟨155516, by rfl⟩) R311033
theorem R109127 : Reach 109127 := rs (se 1 (by rfl) ⟨81845, by rfl⟩) R163691
theorem R404041 : Reach 404041 := rs (se 2 (by rfl) ⟨151515, by rfl⟩) R303031
theorem R109279 : Reach 109279 := rs (se 1 (by rfl) ⟨81959, by rfl⟩) R163919
theorem R1321859 : Reach 1321859 := rs (se 1 (by rfl) ⟨991394, by rfl⟩) R1982789
theorem R273307 : Reach 273307 := rs (se 1 (by rfl) ⟨204980, by rfl⟩) R409961
theorem R306163 : Reach 306163 := rs (se 1 (by rfl) ⟨229622, by rfl⟩) R459245
theorem R1485863 : Reach 1485863 := rs (se 1 (by rfl) ⟨1114397, by rfl⟩) R2228795
theorem R142715 : Reach 142715 := rs (se 1 (by rfl) ⟨107036, by rfl⟩) R214073
theorem R143111 : Reach 143111 := rs (se 1 (by rfl) ⟨107333, by rfl⟩) R214667
theorem R438281 : Reach 438281 := rs (se 2 (by rfl) ⟨164355, by rfl⟩) R328711
theorem R274537 : Reach 274537 := rs (se 2 (by rfl) ⟨102951, by rfl⟩) R205903
theorem R438443 : Reach 438443 := rs (se 1 (by rfl) ⟨328832, by rfl⟩) R657665
theorem R602315 : Reach 602315 := rs (se 1 (by rfl) ⟨451736, by rfl⟩) R903473
theorem R143707 : Reach 143707 := rs (se 1 (by rfl) ⟨107780, by rfl⟩) R215561
theorem R242347 : Reach 242347 := rs (se 1 (by rfl) ⟨181760, by rfl⟩) R363521
theorem R570359 : Reach 570359 := rs (se 1 (by rfl) ⟨427769, by rfl⟩) R855539
theorem R144679 : Reach 144679 := rs (se 1 (by rfl) ⟨108509, by rfl⟩) R217019
theorem R3225091 : Reach 3225091 := rs (se 1 (by rfl) ⟨2418818, by rfl⟩) R4837637
theorem R1324583 : Reach 1324583 := rs (se 1 (by rfl) ⟨993437, by rfl⟩) R1986875
theorem R177967 : Reach 177967 := rs (se 1 (by rfl) ⟨133475, by rfl⟩) R266951
theorem R145199 : Reach 145199 := rs (se 1 (by rfl) ⟨108899, by rfl⟩) R217799
theorem R243965 : Reach 243965 := rs (se 3 (by rfl) ⟨45743, by rfl⟩) R91487
theorem R244079 : Reach 244079 := rs (se 1 (by rfl) ⟨183059, by rfl⟩) R366119
theorem R440749 : Reach 440749 := rs (se 3 (by rfl) ⟨82640, by rfl⟩) R165281
theorem R211855 : Reach 211855 := rs (se 1 (by rfl) ⟨158891, by rfl⟩) R317783
theorem R474011 : Reach 474011 := rs (se 1 (by rfl) ⟨355508, by rfl⟩) R711017
theorem R146407 : Reach 146407 := rs (se 1 (by rfl) ⟨109805, by rfl⟩) R219611
theorem R638117 : Reach 638117 := rs (se 4 (by rfl) ⟨59823, by rfl⟩) R119647
theorem R113929 : Reach 113929 := rs (se 2 (by rfl) ⟨42723, by rfl⟩) R85447
theorem R212321 : Reach 212321 := rs (se 2 (by rfl) ⟨79620, by rfl⟩) R159241
theorem R114043 : Reach 114043 := rs (se 1 (by rfl) ⟨85532, by rfl⟩) R171065
theorem R245207 : Reach 245207 := rs (se 1 (by rfl) ⟨183905, by rfl⟩) R367811
theorem R310879 : Reach 310879 := rs (se 1 (by rfl) ⟨233159, by rfl⟩) R466319
theorem R736883 : Reach 736883 := rs (se 1 (by rfl) ⟨552662, by rfl⟩) R1105325
theorem R212777 : Reach 212777 := rs (se 2 (by rfl) ⟨79791, by rfl⟩) R159583
theorem R343865 : Reach 343865 := rs (se 2 (by rfl) ⟨128949, by rfl⟩) R257899
theorem R213779 : Reach 213779 := rs (se 1 (by rfl) ⟨160334, by rfl⟩) R320669
theorem R246881 : Reach 246881 := rs (se 2 (by rfl) ⟨92580, by rfl⟩) R185161
theorem R836801 : Reach 836801 := rs (se 2 (by rfl) ⟨313800, by rfl⟩) R627601
theorem R214235 : Reach 214235 := rs (se 1 (by rfl) ⟨160676, by rfl⟩) R321353
theorem R148699 : Reach 148699 := rs (se 1 (by rfl) ⟨111524, by rfl⟩) R223049
theorem R214265 : Reach 214265 := rs (se 2 (by rfl) ⟨80349, by rfl⟩) R160699
theorem R83231 : Reach 83231 := rs (se 1 (by rfl) ⟨62423, by rfl⟩) R124847
theorem R148775 : Reach 148775 := rs (se 1 (by rfl) ⟨111581, by rfl⟩) R223163
theorem R83291 : Reach 83291 := rs (se 1 (by rfl) ⟨62468, by rfl⟩) R124937
theorem R83311 : Reach 83311 := rs (se 1 (by rfl) ⟨62483, by rfl⟩) R124967
theorem R83367 : Reach 83367 := rs (se 1 (by rfl) ⟨62525, by rfl⟩) R125051
theorem R2377133 : Reach 2377133 := rs (se 3 (by rfl) ⟨445712, by rfl⟩) R891425
theorem R116167 : Reach 116167 := rs (se 1 (by rfl) ⟨87125, by rfl⟩) R174251
theorem R83451 : Reach 83451 := rs (se 1 (by rfl) ⟨62588, by rfl⟩) R125177
theorem R83519 : Reach 83519 := rs (se 1 (by rfl) ⟨62639, by rfl⟩) R125279
theorem R83527 : Reach 83527 := rs (se 1 (by rfl) ⟨62645, by rfl⟩) R125291
theorem R181855 : Reach 181855 := rs (se 1 (by rfl) ⟨136391, by rfl⟩) R272783
theorem R83679 : Reach 83679 := rs (se 1 (by rfl) ⟨62759, by rfl⟩) R125519
theorem R83759 : Reach 83759 := rs (se 1 (by rfl) ⟨62819, by rfl⟩) R125639
theorem R214913 : Reach 214913 := rs (se 2 (by rfl) ⟨80592, by rfl⟩) R161185
theorem R83867 : Reach 83867 := rs (se 1 (by rfl) ⟨62900, by rfl⟩) R125801
theorem R1034167 : Reach 1034167 := rs (se 1 (by rfl) ⟨775625, by rfl⟩) R1551251
theorem R83919 : Reach 83919 := rs (se 1 (by rfl) ⟨62939, by rfl⟩) R125879
theorem R83943 : Reach 83943 := rs (se 1 (by rfl) ⟨62957, by rfl⟩) R125915
theorem R84255 : Reach 84255 := rs (se 1 (by rfl) ⟨63191, by rfl⟩) R126383
theorem R215369 : Reach 215369 := rs (se 2 (by rfl) ⟨80763, by rfl⟩) R161527
theorem R84315 : Reach 84315 := rs (se 1 (by rfl) ⟨63236, by rfl⟩) R126473
theorem R84335 : Reach 84335 := rs (se 1 (by rfl) ⟨63251, by rfl⟩) R126503
theorem R84391 : Reach 84391 := rs (se 1 (by rfl) ⟨63293, by rfl⟩) R126587
theorem R281015 : Reach 281015 := rs (se 1 (by rfl) ⟨210761, by rfl⟩) R421523
theorem R84475 : Reach 84475 := rs (se 1 (by rfl) ⟨63356, by rfl⟩) R126713
theorem R346619 : Reach 346619 := rs (se 1 (by rfl) ⟨259964, by rfl⟩) R519929
theorem R84543 : Reach 84543 := rs (se 1 (by rfl) ⟨63407, by rfl⟩) R126815
theorem R84551 : Reach 84551 := rs (se 1 (by rfl) ⟨63413, by rfl⟩) R126827
theorem R182857 : Reach 182857 := rs (se 2 (by rfl) ⟨68571, by rfl⟩) R137143
theorem R215723 : Reach 215723 := rs (se 1 (by rfl) ⟨161792, by rfl⟩) R323585
theorem R84703 : Reach 84703 := rs (se 1 (by rfl) ⟨63527, by rfl⟩) R127055
theorem R84783 : Reach 84783 := rs (se 1 (by rfl) ⟨63587, by rfl⟩) R127175
theorem R412559 : Reach 412559 := rs (se 1 (by rfl) ⟨309419, by rfl⟩) R618839
theorem R84891 : Reach 84891 := rs (se 1 (by rfl) ⟨63668, by rfl⟩) R127337
theorem R84943 : Reach 84943 := rs (se 1 (by rfl) ⟨63707, by rfl⟩) R127415
theorem R84967 : Reach 84967 := rs (se 1 (by rfl) ⟨63725, by rfl⟩) R127451
theorem R216103 : Reach 216103 := rs (se 1 (by rfl) ⟨162077, by rfl⟩) R324155
theorem R281819 : Reach 281819 := rs (se 1 (by rfl) ⟨211364, by rfl⟩) R422729
theorem R85279 : Reach 85279 := rs (se 1 (by rfl) ⟨63959, by rfl⟩) R127919
theorem R85339 : Reach 85339 := rs (se 1 (by rfl) ⟨64004, by rfl⟩) R128009
theorem R85359 : Reach 85359 := rs (se 1 (by rfl) ⟨64019, by rfl⟩) R128039
theorem R85415 : Reach 85415 := rs (se 1 (by rfl) ⟨64061, by rfl⟩) R128123
theorem R642491 : Reach 642491 := rs (se 1 (by rfl) ⟨481868, by rfl⟩) R963737
theorem R85499 : Reach 85499 := rs (se 1 (by rfl) ⟨64124, by rfl⟩) R128249
theorem R85567 : Reach 85567 := rs (se 1 (by rfl) ⟨64175, by rfl⟩) R128351
theorem R85575 : Reach 85575 := rs (se 1 (by rfl) ⟨64181, by rfl⟩) R128363
theorem R85727 : Reach 85727 := rs (se 1 (by rfl) ⟨64295, by rfl⟩) R128591
theorem R85807 : Reach 85807 := rs (se 1 (by rfl) ⟨64355, by rfl⟩) R128711
theorem R85915 : Reach 85915 := rs (se 1 (by rfl) ⟨64436, by rfl⟩) R128873
theorem R217039 : Reach 217039 := rs (se 1 (by rfl) ⟨162779, by rfl⟩) R325559
theorem R85967 : Reach 85967 := rs (se 1 (by rfl) ⟨64475, by rfl⟩) R128951
theorem R85991 : Reach 85991 := rs (se 1 (by rfl) ⟨64493, by rfl⟩) R128987
theorem R544769 : Reach 544769 := rs (se 2 (by rfl) ⟨204288, by rfl⟩) R408577
theorem R938155 : Reach 938155 := rs (se 1 (by rfl) ⟨703616, by rfl⟩) R1407233
theorem R348371 : Reach 348371 := rs (se 1 (by rfl) ⟨261278, by rfl⟩) R522557
theorem R741635 : Reach 741635 := rs (se 1 (by rfl) ⟨556226, by rfl⟩) R1112453
theorem R86303 : Reach 86303 := rs (se 1 (by rfl) ⟨64727, by rfl⟩) R129455
theorem R86363 : Reach 86363 := rs (se 1 (by rfl) ⟨64772, by rfl⟩) R129545
theorem R86383 : Reach 86383 := rs (se 1 (by rfl) ⟨64787, by rfl⟩) R129575
theorem R86439 : Reach 86439 := rs (se 1 (by rfl) ⟨64829, by rfl⟩) R129659
theorem R184751 : Reach 184751 := rs (se 1 (by rfl) ⟨138563, by rfl⟩) R277127
theorem R1102325 : Reach 1102325 := rs (se 5 (by rfl) ⟨51671, by rfl⟩) R103343
theorem R86523 : Reach 86523 := rs (se 1 (by rfl) ⟨64892, by rfl⟩) R129785
theorem R86591 : Reach 86591 := rs (se 1 (by rfl) ⟨64943, by rfl⟩) R129887
theorem R86599 : Reach 86599 := rs (se 1 (by rfl) ⟨64949, by rfl⟩) R129899
theorem R86751 : Reach 86751 := rs (se 1 (by rfl) ⟨65063, by rfl⟩) R130127
theorem R86831 : Reach 86831 := rs (se 1 (by rfl) ⟨65123, by rfl⟩) R130247
theorem R643949 : Reach 643949 := rs (se 3 (by rfl) ⟨120740, by rfl⟩) R241481
theorem R218011 : Reach 218011 := rs (se 1 (by rfl) ⟨163508, by rfl⟩) R327017
theorem R86939 : Reach 86939 := rs (se 1 (by rfl) ⟨65204, by rfl⟩) R130409
theorem R86991 : Reach 86991 := rs (se 1 (by rfl) ⟨65243, by rfl⟩) R130487
theorem R87015 : Reach 87015 := rs (se 1 (by rfl) ⟨65261, by rfl⟩) R130523
theorem R906497 : Reach 906497 := rs (se 2 (by rfl) ⟨339936, by rfl⟩) R679873
theorem R316781 : Reach 316781 := rs (se 3 (by rfl) ⟨59396, by rfl⟩) R118793
theorem R316811 : Reach 316811 := rs (se 1 (by rfl) ⟨237608, by rfl⟩) R475217
theorem R284093 : Reach 284093 := rs (se 3 (by rfl) ⟨53267, by rfl⟩) R106535
theorem R480775 : Reach 480775 := rs (se 1 (by rfl) ⟨360581, by rfl⟩) R721163
theorem R284471 : Reach 284471 := rs (se 1 (by rfl) ⟨213353, by rfl⟩) R426707
theorem R350057 : Reach 350057 := rs (se 2 (by rfl) ⟨131271, by rfl⟩) R262543
theorem R219145 : Reach 219145 := rs (se 2 (by rfl) ⟨82179, by rfl⟩) R164359
theorem R284957 : Reach 284957 := rs (se 3 (by rfl) ⟨53429, by rfl⟩) R106859
theorem R154081 : Reach 154081 := rs (se 2 (by rfl) ⟨57780, by rfl⟩) R115561
theorem R187055 : Reach 187055 := rs (se 1 (by rfl) ⟨140291, by rfl⟩) R280583
theorem R187127 : Reach 187127 := rs (se 1 (by rfl) ⟨140345, by rfl⟩) R280691
theorem R187307 : Reach 187307 := rs (se 1 (by rfl) ⟨140480, by rfl⟩) R280961
theorem R318451 : Reach 318451 := rs (se 1 (by rfl) ⟨238838, by rfl⟩) R477677
theorem R285983 : Reach 285983 := rs (se 1 (by rfl) ⟨214487, by rfl⟩) R428975
theorem R187847 : Reach 187847 := rs (se 1 (by rfl) ⟨140885, by rfl⟩) R281771
theorem R319211 : Reach 319211 := rs (se 1 (by rfl) ⟨239408, by rfl⟩) R478817
theorem R188207 : Reach 188207 := rs (se 1 (by rfl) ⟨141155, by rfl⟩) R282311
theorem R548669 : Reach 548669 := rs (se 3 (by rfl) ⟨102875, by rfl⟩) R205751
theorem R319697 : Reach 319697 := rs (se 2 (by rfl) ⟨119886, by rfl⟩) R239773
theorem R188783 : Reach 188783 := rs (se 1 (by rfl) ⟨141587, by rfl⟩) R283175
theorem R188855 : Reach 188855 := rs (se 1 (by rfl) ⟨141641, by rfl⟩) R283283
theorem R4842017 : Reach 4842017 := rs (se 2 (by rfl) ⟨1815756, by rfl⟩) R3631513
theorem R188999 : Reach 188999 := rs (se 1 (by rfl) ⟨141749, by rfl⟩) R283499
theorem R221767 : Reach 221767 := rs (se 1 (by rfl) ⟨166325, by rfl⟩) R332651
theorem R189035 : Reach 189035 := rs (se 1 (by rfl) ⟨141776, by rfl⟩) R283553
theorem R320183 : Reach 320183 := rs (se 1 (by rfl) ⟨240137, by rfl⟩) R480275
theorem R189431 : Reach 189431 := rs (se 1 (by rfl) ⟨142073, by rfl⟩) R284147
theorem R2450533 : Reach 2450533 := rs (se 4 (by rfl) ⟨229737, by rfl⟩) R459475
theorem R189791 : Reach 189791 := rs (se 1 (by rfl) ⟨142343, by rfl⟩) R284687
theorem R714329 : Reach 714329 := rs (se 2 (by rfl) ⟨267873, by rfl⟩) R535747
theorem R288413 : Reach 288413 := rs (se 3 (by rfl) ⟨54077, by rfl⟩) R108155
theorem R190187 : Reach 190187 := rs (se 1 (by rfl) ⟨142640, by rfl⟩) R285281
theorem R124727 : Reach 124727 := rs (se 1 (by rfl) ⟨93545, by rfl⟩) R187091
theorem R321367 : Reach 321367 := rs (se 1 (by rfl) ⟨241025, by rfl⟩) R482051
theorem R190313 : Reach 190313 := rs (se 2 (by rfl) ⟨71367, by rfl⟩) R142735
theorem R92059 : Reach 92059 := rs (se 1 (by rfl) ⟨69044, by rfl⟩) R138089
theorem R125033 : Reach 125033 := rs (se 2 (by rfl) ⟨46887, by rfl⟩) R93775
theorem R321671 : Reach 321671 := rs (se 1 (by rfl) ⟨241253, by rfl⟩) R482507
theorem R288953 : Reach 288953 := rs (se 2 (by rfl) ⟨108357, by rfl⟩) R216715
theorem R125351 : Reach 125351 := rs (se 1 (by rfl) ⟨94013, by rfl⟩) R188027
theorem R125435 : Reach 125435 := rs (se 1 (by rfl) ⟨94076, by rfl⟩) R188153
theorem R322127 : Reach 322127 := rs (se 1 (by rfl) ⟨241595, by rfl⟩) R483191
theorem R125561 : Reach 125561 := rs (se 2 (by rfl) ⟨47085, by rfl⟩) R94171
theorem R125615 : Reach 125615 := rs (se 1 (by rfl) ⟨94211, by rfl⟩) R188423
theorem R191159 : Reach 191159 := rs (se 1 (by rfl) ⟨143369, by rfl⟩) R286739
theorem R1108669 : Reach 1108669 := rs (se 3 (by rfl) ⟨207875, by rfl⟩) R415751
theorem R125663 : Reach 125663 := rs (se 1 (by rfl) ⟨94247, by rfl⟩) R188495
theorem R191375 : Reach 191375 := rs (se 1 (by rfl) ⟨143531, by rfl⟩) R287063
theorem R125927 : Reach 125927 := rs (se 1 (by rfl) ⟨94445, by rfl⟩) R188891
theorem R814157 : Reach 814157 := rs (se 3 (by rfl) ⟨152654, by rfl⟩) R305309
theorem R126185 : Reach 126185 := rs (se 2 (by rfl) ⟨47319, by rfl⟩) R94639
theorem R126239 : Reach 126239 := rs (se 1 (by rfl) ⟨94679, by rfl⟩) R189359
theorem R126407 : Reach 126407 := rs (se 1 (by rfl) ⟨94805, by rfl⟩) R189611
theorem R323155 : Reach 323155 := rs (se 1 (by rfl) ⟨242366, by rfl⟩) R484733
theorem R192095 : Reach 192095 := rs (se 1 (by rfl) ⟨144071, by rfl⟩) R288143
theorem R290465 : Reach 290465 := rs (se 2 (by rfl) ⟨108924, by rfl⟩) R217849
theorem R650915 : Reach 650915 := rs (se 1 (by rfl) ⟨488186, by rfl⟩) R976373
theorem R93919 : Reach 93919 := rs (se 1 (by rfl) ⟨70439, by rfl⟩) R140879
theorem R126761 : Reach 126761 := rs (se 2 (by rfl) ⟨47535, by rfl⟩) R95071
theorem R126767 : Reach 126767 := rs (se 1 (by rfl) ⟨95075, by rfl⟩) R190151
theorem R192311 : Reach 192311 := rs (se 1 (by rfl) ⟨144233, by rfl⟩) R288467
theorem R159545 : Reach 159545 := rs (se 2 (by rfl) ⟨59829, by rfl⟩) R119659
theorem R192617 : Reach 192617 := rs (se 2 (by rfl) ⟨72231, by rfl⟩) R144463
theorem R127241 : Reach 127241 := rs (se 2 (by rfl) ⟨47715, by rfl⟩) R95431
theorem R94495 : Reach 94495 := rs (se 1 (by rfl) ⟨70871, by rfl⟩) R141743
theorem R127343 : Reach 127343 := rs (se 1 (by rfl) ⟨95507, by rfl⟩) R191015
theorem R291329 : Reach 291329 := rs (se 2 (by rfl) ⟨109248, by rfl⟩) R218497
theorem R94783 : Reach 94783 := rs (se 1 (by rfl) ⟨71087, by rfl⟩) R142175
theorem R160319 : Reach 160319 := rs (se 1 (by rfl) ⟨120239, by rfl⟩) R240479
theorem R127559 : Reach 127559 := rs (se 1 (by rfl) ⟨95669, by rfl⟩) R191339
theorem R193103 : Reach 193103 := rs (se 1 (by rfl) ⟨144827, by rfl⟩) R289655
theorem R127595 : Reach 127595 := rs (se 1 (by rfl) ⟨95696, by rfl⟩) R191393
theorem R1798807 : Reach 1798807 := rs (se 1 (by rfl) ⟨1349105, by rfl⟩) R2698211
theorem R193247 : Reach 193247 := rs (se 1 (by rfl) ⟨144935, by rfl⟩) R289871
theorem R127823 : Reach 127823 := rs (se 1 (by rfl) ⟨95867, by rfl⟩) R191735
theorem R193499 : Reach 193499 := rs (se 1 (by rfl) ⟨145124, by rfl⟩) R290249
theorem R291815 : Reach 291815 := rs (se 1 (by rfl) ⟨218861, by rfl⟩) R437723
theorem R357473 : Reach 357473 := rs (se 2 (by rfl) ⟨134052, by rfl⟩) R268105
theorem R193679 : Reach 193679 := rs (se 1 (by rfl) ⟨145259, by rfl⟩) R290519
theorem R324755 : Reach 324755 := rs (se 1 (by rfl) ⟨243566, by rfl⟩) R487133
theorem R128219 : Reach 128219 := rs (se 1 (by rfl) ⟨96164, by rfl⟩) R192329
theorem R193769 : Reach 193769 := rs (se 2 (by rfl) ⟨72663, by rfl⟩) R145327
theorem R259321 : Reach 259321 := rs (se 2 (by rfl) ⟨97245, by rfl⟩) R194491
theorem R193823 : Reach 193823 := rs (se 1 (by rfl) ⟨145367, by rfl⟩) R290735
theorem R292139 : Reach 292139 := rs (se 1 (by rfl) ⟨219104, by rfl⟩) R438209
theorem R95611 : Reach 95611 := rs (se 1 (by rfl) ⟨71708, by rfl⟩) R143417
theorem R128393 : Reach 128393 := rs (se 2 (by rfl) ⟨48147, by rfl⟩) R96295
theorem R292409 : Reach 292409 := rs (se 2 (by rfl) ⟨109653, by rfl⟩) R219307
theorem R128747 : Reach 128747 := rs (se 1 (by rfl) ⟨96560, by rfl⟩) R193121
theorem R194345 : Reach 194345 := rs (se 2 (by rfl) ⟨72879, by rfl⟩) R145759
theorem R96079 : Reach 96079 := rs (se 1 (by rfl) ⟨72059, by rfl⟩) R144119
theorem R128975 : Reach 128975 := rs (se 1 (by rfl) ⟨96731, by rfl⟩) R193463
theorem R96475 : Reach 96475 := rs (se 1 (by rfl) ⟨72356, by rfl⟩) R144713
theorem R424217 : Reach 424217 := rs (se 2 (by rfl) ⟨159081, by rfl⟩) R318163
theorem R129371 : Reach 129371 := rs (se 1 (by rfl) ⟨97028, by rfl⟩) R194057
theorem R96763 : Reach 96763 := rs (se 1 (by rfl) ⟨72572, by rfl⟩) R145145
theorem R1243673 : Reach 1243673 := rs (se 2 (by rfl) ⟨466377, by rfl⟩) R932755
theorem R129599 : Reach 129599 := rs (se 1 (by rfl) ⟨97199, by rfl⟩) R194399
theorem R96943 : Reach 96943 := rs (se 1 (by rfl) ⟨72707, by rfl⟩) R145415
theorem R129719 : Reach 129719 := rs (se 1 (by rfl) ⟨97289, by rfl⟩) R194579
theorem R293651 : Reach 293651 := rs (se 1 (by rfl) ⟨220238, by rfl⟩) R440477
theorem R195407 : Reach 195407 := rs (se 1 (by rfl) ⟨146555, by rfl⟩) R293111
theorem R818075 : Reach 818075 := rs (se 1 (by rfl) ⟨613556, by rfl⟩) R1227113
theorem R129947 : Reach 129947 := rs (se 1 (by rfl) ⟨97460, by rfl⟩) R194921
theorem R97231 : Reach 97231 := rs (se 1 (by rfl) ⟨72923, by rfl⟩) R145847
theorem R195623 : Reach 195623 := rs (se 1 (by rfl) ⟨146717, by rfl⟩) R293435
theorem R228491 : Reach 228491 := rs (se 1 (by rfl) ⟨171368, by rfl⟩) R342737
theorem R195803 : Reach 195803 := rs (se 1 (by rfl) ⟨146852, by rfl⟩) R293705
theorem R130343 : Reach 130343 := rs (se 1 (by rfl) ⟨97757, by rfl⟩) R195515
theorem R359747 : Reach 359747 := rs (se 1 (by rfl) ⟨269810, by rfl⟩) R539621
theorem R97627 : Reach 97627 := rs (se 1 (by rfl) ⟨73220, by rfl⟩) R146441
theorem R130427 : Reach 130427 := rs (se 1 (by rfl) ⟨97820, by rfl⟩) R195641
theorem R196001 : Reach 196001 := rs (se 2 (by rfl) ⟨73500, by rfl⟩) R147001
theorem R97735 : Reach 97735 := rs (se 1 (by rfl) ⟨73301, by rfl⟩) R146603
theorem R130553 : Reach 130553 := rs (se 2 (by rfl) ⟨48957, by rfl⟩) R97915
theorem R130655 : Reach 130655 := rs (se 1 (by rfl) ⟨97991, by rfl⟩) R195983
theorem R425735 : Reach 425735 := rs (se 1 (by rfl) ⟨319301, by rfl⟩) R638603
theorem R1638305 : Reach 1638305 := rs (se 2 (by rfl) ⟨614364, by rfl⟩) R1228729
theorem R164587 : Reach 164587 := rs (se 1 (by rfl) ⟨123440, by rfl⟩) R246881
theorem R131881 : Reach 131881 := rs (se 2 (by rfl) ⟨49455, by rfl⟩) R98911
theorem R557867 : Reach 557867 := rs (se 1 (by rfl) ⟨418400, by rfl⟩) R836801
theorem R525257 : Reach 525257 := rs (se 2 (by rfl) ⟨196971, by rfl⟩) R393943
theorem R427517 : Reach 427517 := rs (se 3 (by rfl) ⟨80159, by rfl⟩) R160319
theorem R428327 : Reach 428327 := rs (se 1 (by rfl) ⟨321245, by rfl⟩) R642491
theorem R395567 : Reach 395567 := rs (se 1 (by rfl) ⟨296675, by rfl⟩) R593351
theorem R428489 : Reach 428489 := rs (se 2 (by rfl) ⟨160683, by rfl⟩) R321367
theorem R526817 : Reach 526817 := rs (se 2 (by rfl) ⟨197556, by rfl⟩) R395113
theorem R821765 : Reach 821765 := rs (se 4 (by rfl) ⟨77040, by rfl⟩) R154081
theorem R1378889 : Reach 1378889 := rs (se 2 (by rfl) ⟨517083, by rfl⟩) R1034167
theorem R363179 : Reach 363179 := rs (se 1 (by rfl) ⟨272384, by rfl⟩) R544769
theorem R232247 : Reach 232247 := rs (se 1 (by rfl) ⟨174185, by rfl⟩) R348371
theorem R723799 : Reach 723799 := rs (se 1 (by rfl) ⟨542849, by rfl⟩) R1085699
theorem R494423 : Reach 494423 := rs (se 1 (by rfl) ⟨370817, by rfl⟩) R741635
theorem R1182757 : Reach 1182757 := rs (se 4 (by rfl) ⟨110883, by rfl⟩) R221767
theorem R1051697 : Reach 1051697 := rs (se 2 (by rfl) ⟨394386, by rfl⟩) R788773
theorem R265459 : Reach 265459 := rs (se 1 (by rfl) ⟨199094, by rfl⟩) R398189
theorem R429299 : Reach 429299 := rs (se 1 (by rfl) ⟨321974, by rfl⟩) R643949
theorem R134569 : Reach 134569 := rs (se 2 (by rfl) ⟨50463, by rfl⟩) R100927
theorem R396733 : Reach 396733 := rs (se 3 (by rfl) ⟨74387, by rfl⟩) R148775
theorem R1478225 : Reach 1478225 := rs (se 2 (by rfl) ⟨554334, by rfl⟩) R1108669
theorem R364409 : Reach 364409 := rs (se 2 (by rfl) ⟨136653, by rfl⟩) R273307
theorem R233371 : Reach 233371 := rs (se 1 (by rfl) ⟨175028, by rfl⟩) R350057
theorem R201311 : Reach 201311 := rs (se 1 (by rfl) ⟨150983, by rfl⟩) R301967
theorem R267259 : Reach 267259 := rs (se 1 (by rfl) ⟨200444, by rfl⟩) R400889
theorem R365779 : Reach 365779 := rs (se 1 (by rfl) ⟨274334, by rfl⟩) R548669
theorem R366049 : Reach 366049 := rs (se 2 (by rfl) ⟨137268, by rfl⟩) R274537
theorem R1250873 : Reach 1250873 := rs (se 2 (by rfl) ⟨469077, by rfl⟩) R938155
theorem R2398409 : Reach 2398409 := rs (se 2 (by rfl) ⟨899403, by rfl⟩) R1798807
theorem R530729 : Reach 530729 := rs (se 2 (by rfl) ⟨199023, by rfl⟩) R398047
theorem R793061 : Reach 793061 := rs (se 4 (by rfl) ⟨74349, by rfl⟩) R148699
theorem R924317 : Reach 924317 := rs (se 3 (by rfl) ⟨173309, by rfl⟩) R346619
theorem R269257 : Reach 269257 := rs (se 2 (by rfl) ⟨100971, by rfl⟩) R201943
theorem R138191 : Reach 138191 := rs (se 1 (by rfl) ⟨103643, by rfl⟩) R207287
theorem R4300121 : Reach 4300121 := rs (se 2 (by rfl) ⟨1612545, by rfl⟩) R3225091
theorem R990575 : Reach 990575 := rs (se 1 (by rfl) ⟨742931, by rfl⟩) R1485863
theorem R433943 : Reach 433943 := rs (se 1 (by rfl) ⟨325457, by rfl⟩) R650915
theorem R106363 : Reach 106363 := rs (se 1 (by rfl) ⟨79772, by rfl⟩) R159545
theorem R401543 : Reach 401543 := rs (se 1 (by rfl) ⟨301157, by rfl⟩) R602315
theorem R238315 : Reach 238315 := rs (se 1 (by rfl) ⟨178736, by rfl⟩) R357473
theorem R1844045 : Reach 1844045 := rs (se 3 (by rfl) ⟨345758, by rfl⟩) R691517
theorem R140393 : Reach 140393 := rs (se 2 (by rfl) ⟨52647, by rfl⟩) R105295
theorem R829115 : Reach 829115 := rs (se 1 (by rfl) ⟨621836, by rfl⟩) R1243673
theorem R239831 : Reach 239831 := rs (se 1 (by rfl) ⟨179873, by rfl⟩) R359747
theorem R141547 : Reach 141547 := rs (se 1 (by rfl) ⟨106160, by rfl⟩) R212321
theorem R272897 : Reach 272897 := rs (se 2 (by rfl) ⟨102336, by rfl⟩) R204673
theorem R141851 : Reach 141851 := rs (se 1 (by rfl) ⟨106388, by rfl⟩) R212777
theorem R1092203 : Reach 1092203 := rs (se 1 (by rfl) ⟨819152, by rfl⟩) R1638305
theorem R142519 : Reach 142519 := rs (se 1 (by rfl) ⟨106889, by rfl⟩) R213779
theorem R142823 : Reach 142823 := rs (se 1 (by rfl) ⟨107117, by rfl⟩) R214235
theorem R142843 : Reach 142843 := rs (se 1 (by rfl) ⟨107132, by rfl⟩) R214265
theorem R1584755 : Reach 1584755 := rs (se 1 (by rfl) ⟨1188566, by rfl⟩) R2377133
theorem R437885 : Reach 437885 := rs (se 3 (by rfl) ⟨82103, by rfl⟩) R164207
theorem R143275 : Reach 143275 := rs (se 1 (by rfl) ⟨107456, by rfl⟩) R214913
theorem R831455 : Reach 831455 := rs (se 1 (by rfl) ⟨623591, by rfl⟩) R1247183
theorem R143579 : Reach 143579 := rs (se 1 (by rfl) ⟨107684, by rfl⟩) R215369
theorem R1487159 : Reach 1487159 := rs (se 1 (by rfl) ⟨1115369, by rfl⟩) R2230739
theorem R176521 : Reach 176521 := rs (se 2 (by rfl) ⟨66195, by rfl⟩) R132391
theorem R438695 : Reach 438695 := rs (se 1 (by rfl) ⟨329021, by rfl⟩) R658043
theorem R143815 : Reach 143815 := rs (se 1 (by rfl) ⟨107861, by rfl⟩) R215723
theorem R143849 : Reach 143849 := rs (se 2 (by rfl) ⟨53943, by rfl⟩) R107887
theorem R275039 : Reach 275039 := rs (se 1 (by rfl) ⟨206279, by rfl⟩) R412559
theorem R242473 : Reach 242473 := rs (se 2 (by rfl) ⟨90927, by rfl⟩) R181855
theorem R308279 : Reach 308279 := rs (se 1 (by rfl) ⟨231209, by rfl⟩) R462419
theorem R1553651 : Reach 1553651 := rs (se 1 (by rfl) ⟨1165238, by rfl⟩) R2330477
theorem R242963 : Reach 242963 := rs (se 1 (by rfl) ⟨182222, by rfl⟩) R364445
theorem R1520957 : Reach 1520957 := rs (se 3 (by rfl) ⟨285179, by rfl⟩) R570359
theorem R833111 : Reach 833111 := rs (se 1 (by rfl) ⟨624833, by rfl⟩) R1249667
theorem R439991 : Reach 439991 := rs (se 1 (by rfl) ⟨329993, by rfl⟩) R659987
theorem R276281 : Reach 276281 := rs (se 2 (by rfl) ⟨103605, by rfl⟩) R207211
theorem R112447 : Reach 112447 := rs (se 1 (by rfl) ⟨84335, by rfl⟩) R168671
theorem R309187 : Reach 309187 := rs (se 1 (by rfl) ⟨231890, by rfl⟩) R463781
theorem R178139 : Reach 178139 := rs (se 1 (by rfl) ⟨133604, by rfl⟩) R267209
theorem R276473 : Reach 276473 := rs (se 2 (by rfl) ⟨103677, by rfl⟩) R207355
theorem R538721 : Reach 538721 := rs (se 2 (by rfl) ⟨202020, by rfl⟩) R404041
theorem R243809 : Reach 243809 := rs (se 2 (by rfl) ⟨91428, by rfl⟩) R182857
theorem R604331 : Reach 604331 := rs (se 1 (by rfl) ⟨453248, by rfl⟩) R906497
theorem R211187 : Reach 211187 := rs (se 1 (by rfl) ⟨158390, by rfl⟩) R316781
theorem R309491 : Reach 309491 := rs (se 1 (by rfl) ⟨232118, by rfl⟩) R464237
theorem R211207 : Reach 211207 := rs (se 1 (by rfl) ⟨158405, by rfl⟩) R316811
theorem R145705 : Reach 145705 := rs (se 2 (by rfl) ⟨54639, by rfl⟩) R109279
theorem R179027 : Reach 179027 := rs (se 1 (by rfl) ⟨134270, by rfl⟩) R268541
theorem R244919 : Reach 244919 := rs (se 1 (by rfl) ⟨183689, by rfl⟩) R367379
theorem R212807 : Reach 212807 := rs (se 1 (by rfl) ⟨159605, by rfl⟩) R319211
theorem R704591 : Reach 704591 := rs (se 1 (by rfl) ⟨528443, by rfl⟩) R1056887
theorem R213131 : Reach 213131 := rs (se 1 (by rfl) ⟨159848, by rfl⟩) R319697
theorem R311435 : Reach 311435 := rs (se 1 (by rfl) ⟨233576, by rfl⟩) R467153
theorem R3228011 : Reach 3228011 := rs (se 1 (by rfl) ⟨2421008, by rfl⟩) R4842017
theorem R180667 : Reach 180667 := rs (se 1 (by rfl) ⟨135500, by rfl⟩) R271001
theorem R213455 : Reach 213455 := rs (se 1 (by rfl) ⟨160091, by rfl⟩) R320183
theorem R1425923 : Reach 1425923 := rs (se 1 (by rfl) ⟨1069442, by rfl⟩) R2138885
theorem R476219 : Reach 476219 := rs (se 1 (by rfl) ⟨357164, by rfl⟩) R714329
theorem R83151 : Reach 83151 := rs (se 1 (by rfl) ⟨62363, by rfl⟩) R124727
theorem R607621 : Reach 607621 := rs (se 4 (by rfl) ⟨56964, by rfl⟩) R113929
theorem R83355 : Reach 83355 := rs (se 1 (by rfl) ⟨62516, by rfl⟩) R125033
theorem R214447 : Reach 214447 := rs (se 1 (by rfl) ⟨160835, by rfl⟩) R321671
theorem R3130919 : Reach 3130919 := rs (se 1 (by rfl) ⟨2348189, by rfl⟩) R4696379
theorem R83567 : Reach 83567 := rs (se 1 (by rfl) ⟨62675, by rfl⟩) R125351
theorem R312943 : Reach 312943 := rs (se 1 (by rfl) ⟨234707, by rfl⟩) R469415
theorem R345761 : Reach 345761 := rs (se 2 (by rfl) ⟨129660, by rfl⟩) R259321
theorem R83623 : Reach 83623 := rs (se 1 (by rfl) ⟨62717, by rfl⟩) R125435
theorem R214751 : Reach 214751 := rs (se 1 (by rfl) ⟨161063, by rfl⟩) R322127
theorem R83707 : Reach 83707 := rs (se 1 (by rfl) ⟨62780, by rfl⟩) R125561
theorem R83743 : Reach 83743 := rs (se 1 (by rfl) ⟨62807, by rfl⟩) R125615
theorem R83775 : Reach 83775 := rs (se 1 (by rfl) ⟨62831, by rfl⟩) R125663
theorem R83951 : Reach 83951 := rs (se 1 (by rfl) ⟨62963, by rfl⟩) R125927
theorem R641033 : Reach 641033 := rs (se 2 (by rfl) ⟨240387, by rfl⟩) R480775
theorem R542771 : Reach 542771 := rs (se 1 (by rfl) ⟨407078, by rfl⟩) R814157
theorem R84123 : Reach 84123 := rs (se 1 (by rfl) ⟨63092, by rfl⟩) R126185
theorem R84159 : Reach 84159 := rs (se 1 (by rfl) ⟨63119, by rfl⟩) R126239
theorem R84271 : Reach 84271 := rs (se 1 (by rfl) ⟨63203, by rfl⟩) R126407
theorem R84507 : Reach 84507 := rs (se 1 (by rfl) ⟨63380, by rfl⟩) R126761
theorem R84511 : Reach 84511 := rs (se 1 (by rfl) ⟨63383, by rfl⟩) R126767
theorem R84827 : Reach 84827 := rs (se 1 (by rfl) ⟨63620, by rfl⟩) R127241
theorem R84895 : Reach 84895 := rs (se 1 (by rfl) ⟨63671, by rfl⟩) R127343
theorem R85039 : Reach 85039 := rs (se 1 (by rfl) ⟨63779, by rfl⟩) R127559
theorem R85063 : Reach 85063 := rs (se 1 (by rfl) ⟨63797, by rfl⟩) R127595
theorem R1723493 : Reach 1723493 := rs (se 4 (by rfl) ⟨161577, by rfl⟩) R323155
theorem R85215 : Reach 85215 := rs (se 1 (by rfl) ⟨63911, by rfl⟩) R127823
theorem R216503 : Reach 216503 := rs (se 1 (by rfl) ⟨162377, by rfl⟩) R324755
theorem R85479 : Reach 85479 := rs (se 1 (by rfl) ⟨64109, by rfl⟩) R128219
theorem R85595 : Reach 85595 := rs (se 1 (by rfl) ⟨64196, by rfl⟩) R128393
theorem R85831 : Reach 85831 := rs (se 1 (by rfl) ⟨64373, by rfl⟩) R128747
theorem R282473 : Reach 282473 := rs (se 2 (by rfl) ⟨105927, by rfl⟩) R211855
theorem R85983 : Reach 85983 := rs (se 1 (by rfl) ⟨64487, by rfl⟩) R128975
theorem R282811 : Reach 282811 := rs (se 1 (by rfl) ⟨212108, by rfl⟩) R424217
theorem R86247 : Reach 86247 := rs (se 1 (by rfl) ⟨64685, by rfl⟩) R129371
theorem R86399 : Reach 86399 := rs (se 1 (by rfl) ⟨64799, by rfl⟩) R129599
theorem R86479 : Reach 86479 := rs (se 1 (by rfl) ⟨64859, by rfl⟩) R129719
theorem R152057 : Reach 152057 := rs (se 2 (by rfl) ⟨57021, by rfl⟩) R114043
theorem R316007 : Reach 316007 := rs (se 1 (by rfl) ⟨237005, by rfl⟩) R474011
theorem R545383 : Reach 545383 := rs (se 1 (by rfl) ⟨409037, by rfl⟩) R818075
theorem R86631 : Reach 86631 := rs (se 1 (by rfl) ⟨64973, by rfl⟩) R129947
theorem R152327 : Reach 152327 := rs (se 1 (by rfl) ⟨114245, by rfl⟩) R228491
theorem R414505 : Reach 414505 := rs (se 2 (by rfl) ⟨155439, by rfl⟩) R310879
theorem R86895 : Reach 86895 := rs (se 1 (by rfl) ⟨65171, by rfl⟩) R130343
theorem R86951 : Reach 86951 := rs (se 1 (by rfl) ⟨65213, by rfl⟩) R130427
theorem R87035 : Reach 87035 := rs (se 1 (by rfl) ⟨65276, by rfl⟩) R130553
theorem R87103 : Reach 87103 := rs (se 1 (by rfl) ⟨65327, by rfl⟩) R130655
theorem R185417 : Reach 185417 := rs (se 2 (by rfl) ⟨69531, by rfl⟩) R139063
theorem R283823 : Reach 283823 := rs (se 1 (by rfl) ⟨212867, by rfl⟩) R425735
theorem R219095 : Reach 219095 := rs (se 1 (by rfl) ⟨164321, by rfl⟩) R328643
theorem R317465 : Reach 317465 := rs (se 2 (by rfl) ⟨119049, by rfl⟩) R238099
theorem R2939533 : Reach 2939533 := rs (se 3 (by rfl) ⟨551162, by rfl⟩) R1102325
theorem R3267377 : Reach 3267377 := rs (se 2 (by rfl) ⟨1225266, by rfl⟩) R2450533
theorem R187343 : Reach 187343 := rs (se 1 (by rfl) ⟨140507, by rfl⟩) R281015
theorem R187361 : Reach 187361 := rs (se 2 (by rfl) ⟨70260, by rfl⟩) R140521
theorem R187433 : Reach 187433 := rs (se 2 (by rfl) ⟨70287, by rfl⟩) R140575
theorem R285767 : Reach 285767 := rs (se 1 (by rfl) ⟨214325, by rfl⟩) R428651
theorem R285821 : Reach 285821 := rs (se 3 (by rfl) ⟨53591, by rfl⟩) R107183
theorem R154847 : Reach 154847 := rs (se 1 (by rfl) ⟨116135, by rfl⟩) R232271
theorem R351485 : Reach 351485 := rs (se 3 (by rfl) ⟨65903, by rfl⟩) R131807
theorem R154889 : Reach 154889 := rs (se 2 (by rfl) ⟨58083, by rfl⟩) R116167
theorem R286091 : Reach 286091 := rs (se 1 (by rfl) ⟨214568, by rfl⟩) R429137
theorem R482759 : Reach 482759 := rs (se 1 (by rfl) ⟨362069, by rfl⟩) R724139
theorem R187879 : Reach 187879 := rs (se 1 (by rfl) ⟨140909, by rfl⟩) R281819
theorem R1072723 : Reach 1072723 := rs (se 1 (by rfl) ⟨804542, by rfl⟩) R1609085
theorem R123167 : Reach 123167 := rs (se 1 (by rfl) ⟨92375, by rfl⟩) R184751
theorem R909701 : Reach 909701 := rs (se 4 (by rfl) ⟨85284, by rfl⟩) R170569
theorem R2777611 : Reach 2777611 := rs (se 1 (by rfl) ⟨2083208, by rfl⟩) R4166417
theorem R189395 : Reach 189395 := rs (se 1 (by rfl) ⟨142046, by rfl⟩) R284093
theorem R189647 : Reach 189647 := rs (se 1 (by rfl) ⟨142235, by rfl⟩) R284471
theorem R288137 : Reach 288137 := rs (se 2 (by rfl) ⟨108051, by rfl⟩) R216103
theorem R189971 : Reach 189971 := rs (se 1 (by rfl) ⟨142478, by rfl⟩) R284957
theorem R124703 : Reach 124703 := rs (se 1 (by rfl) ⟨93527, by rfl⟩) R187055
theorem R124751 : Reach 124751 := rs (se 1 (by rfl) ⟨93563, by rfl⟩) R187127
theorem R124871 : Reach 124871 := rs (se 1 (by rfl) ⟨93653, by rfl⟩) R187307
theorem R190655 : Reach 190655 := rs (se 1 (by rfl) ⟨142991, by rfl⟩) R285983
theorem R125225 : Reach 125225 := rs (se 2 (by rfl) ⟨46959, by rfl⟩) R93919
theorem R125231 : Reach 125231 := rs (se 1 (by rfl) ⟨93923, by rfl⟩) R187847
theorem R289115 : Reach 289115 := rs (se 1 (by rfl) ⟨216836, by rfl⟩) R433673
theorem R125471 : Reach 125471 := rs (se 1 (by rfl) ⟨94103, by rfl⟩) R188207
theorem R1632869 : Reach 1632869 := rs (se 4 (by rfl) ⟨153081, by rfl⟩) R306163
theorem R289385 : Reach 289385 := rs (se 2 (by rfl) ⟨108519, by rfl⟩) R217039
theorem R486137 : Reach 486137 := rs (se 2 (by rfl) ⟨182301, by rfl⟩) R364603
theorem R125855 : Reach 125855 := rs (se 1 (by rfl) ⟨94391, by rfl⟩) R188783
theorem R125903 : Reach 125903 := rs (se 1 (by rfl) ⟨94427, by rfl⟩) R188855
theorem R125993 : Reach 125993 := rs (se 2 (by rfl) ⟨47247, by rfl⟩) R94495
theorem R125999 : Reach 125999 := rs (se 1 (by rfl) ⟨94499, by rfl⟩) R188999
theorem R126023 : Reach 126023 := rs (se 1 (by rfl) ⟨94517, by rfl⟩) R189035
theorem R191609 : Reach 191609 := rs (se 2 (by rfl) ⟨71853, by rfl⟩) R143707
theorem R552203 : Reach 552203 := rs (se 1 (by rfl) ⟨414152, by rfl⟩) R828305
theorem R355627 : Reach 355627 := rs (se 1 (by rfl) ⟨266720, by rfl⟩) R533441
theorem R126287 : Reach 126287 := rs (se 1 (by rfl) ⟨94715, by rfl⟩) R189431
theorem R126377 : Reach 126377 := rs (se 2 (by rfl) ⟨47391, by rfl⟩) R94783
theorem R323129 : Reach 323129 := rs (se 2 (by rfl) ⟨121173, by rfl⟩) R242347
theorem R224831 : Reach 224831 := rs (se 1 (by rfl) ⟨168623, by rfl⟩) R337247
theorem R126527 : Reach 126527 := rs (se 1 (by rfl) ⟨94895, by rfl⟩) R189791
theorem R290411 : Reach 290411 := rs (se 1 (by rfl) ⟨217808, by rfl⟩) R435617
theorem R192275 : Reach 192275 := rs (se 1 (by rfl) ⟨144206, by rfl⟩) R288413
theorem R93991 : Reach 93991 := rs (se 1 (by rfl) ⟨70493, by rfl⟩) R140987
theorem R126791 : Reach 126791 := rs (se 1 (by rfl) ⟨95093, by rfl⟩) R190187
theorem R290681 : Reach 290681 := rs (se 2 (by rfl) ⟨109005, by rfl⟩) R218011
theorem R126875 : Reach 126875 := rs (se 1 (by rfl) ⟨95156, by rfl⟩) R190313
theorem R192635 : Reach 192635 := rs (se 1 (by rfl) ⟨144476, by rfl⟩) R288953
theorem R291005 : Reach 291005 := rs (se 3 (by rfl) ⟨54563, by rfl⟩) R109127
theorem R192905 : Reach 192905 := rs (se 2 (by rfl) ⟨72339, by rfl⟩) R144679
theorem R127439 : Reach 127439 := rs (se 1 (by rfl) ⟨95579, by rfl⟩) R191159
theorem R127481 : Reach 127481 := rs (se 2 (by rfl) ⟨47805, by rfl⟩) R95611
theorem R881239 : Reach 881239 := rs (se 1 (by rfl) ⟨660929, by rfl⟩) R1321859
theorem R127583 : Reach 127583 := rs (se 1 (by rfl) ⟨95687, by rfl⟩) R191375
theorem R95143 : Reach 95143 := rs (se 1 (by rfl) ⟨71357, by rfl⟩) R142715
theorem R128063 : Reach 128063 := rs (se 1 (by rfl) ⟨96047, by rfl⟩) R192095
theorem R128105 : Reach 128105 := rs (se 2 (by rfl) ⟨48039, by rfl⟩) R96079
theorem R193643 : Reach 193643 := rs (se 1 (by rfl) ⟨145232, by rfl⟩) R290465
theorem R95407 : Reach 95407 := rs (se 1 (by rfl) ⟨71555, by rfl⟩) R143111
theorem R128207 : Reach 128207 := rs (se 1 (by rfl) ⟨96155, by rfl⟩) R192311
theorem R292187 : Reach 292187 := rs (se 1 (by rfl) ⟨219140, by rfl⟩) R438281
theorem R292193 : Reach 292193 := rs (se 2 (by rfl) ⟨109572, by rfl⟩) R219145
theorem R128411 : Reach 128411 := rs (se 1 (by rfl) ⟨96308, by rfl⟩) R192617
theorem R292295 : Reach 292295 := rs (se 1 (by rfl) ⟨219221, by rfl⟩) R438443
theorem R128633 : Reach 128633 := rs (se 2 (by rfl) ⟨48237, by rfl⟩) R96475
theorem R194219 : Reach 194219 := rs (se 1 (by rfl) ⟨145664, by rfl⟩) R291329
theorem R128735 : Reach 128735 := rs (se 1 (by rfl) ⟨96551, by rfl⟩) R193103
theorem R128831 : Reach 128831 := rs (se 1 (by rfl) ⟨96623, by rfl⟩) R193247
theorem R587665 : Reach 587665 := rs (se 2 (by rfl) ⟨220374, by rfl⟩) R440749
theorem R128999 : Reach 128999 := rs (se 1 (by rfl) ⟨96749, by rfl⟩) R193499
theorem R194543 : Reach 194543 := rs (se 1 (by rfl) ⟨145907, by rfl⟩) R291815
theorem R129017 : Reach 129017 := rs (se 2 (by rfl) ⟨48381, by rfl⟩) R96763
theorem R129119 : Reach 129119 := rs (se 1 (by rfl) ⟨96839, by rfl⟩) R193679
theorem R129179 : Reach 129179 := rs (se 1 (by rfl) ⟨96884, by rfl⟩) R193769
theorem R129215 : Reach 129215 := rs (se 1 (by rfl) ⟨96911, by rfl⟩) R193823
theorem R194759 : Reach 194759 := rs (se 1 (by rfl) ⟨146069, by rfl⟩) R292139
theorem R129257 : Reach 129257 := rs (se 2 (by rfl) ⟨48471, by rfl⟩) R96943
theorem R883055 : Reach 883055 := rs (se 1 (by rfl) ⟨662291, by rfl⟩) R1324583
theorem R194939 : Reach 194939 := rs (se 1 (by rfl) ⟨146204, by rfl⟩) R292409
theorem R129563 : Reach 129563 := rs (se 1 (by rfl) ⟨97172, by rfl⟩) R194345
theorem R96799 : Reach 96799 := rs (se 1 (by rfl) ⟨72599, by rfl⟩) R145199
theorem R129641 : Reach 129641 := rs (se 2 (by rfl) ⟨48615, by rfl⟩) R97231
theorem R195209 : Reach 195209 := rs (se 2 (by rfl) ⟨73203, by rfl⟩) R146407
theorem R424601 : Reach 424601 := rs (se 2 (by rfl) ⟨159225, by rfl⟩) R318451
theorem R162643 : Reach 162643 := rs (se 1 (by rfl) ⟨121982, by rfl⟩) R243965
theorem R162719 : Reach 162719 := rs (se 1 (by rfl) ⟨122039, by rfl⟩) R244079
theorem R949157 : Reach 949157 := rs (se 4 (by rfl) ⟨88983, by rfl⟩) R177967
theorem R130169 : Reach 130169 := rs (se 2 (by rfl) ⟨48813, by rfl⟩) R97627
theorem R195767 : Reach 195767 := rs (se 1 (by rfl) ⟨146825, by rfl⟩) R293651
theorem R130271 : Reach 130271 := rs (se 1 (by rfl) ⟨97703, by rfl⟩) R195407
theorem R130313 : Reach 130313 := rs (se 2 (by rfl) ⟨48867, by rfl⟩) R97735
theorem R130415 : Reach 130415 := rs (se 1 (by rfl) ⟨97811, by rfl⟩) R195623
theorem R425411 : Reach 425411 := rs (se 1 (by rfl) ⟨319058, by rfl⟩) R638117
theorem R490981 : Reach 490981 := rs (se 4 (by rfl) ⟨46029, by rfl⟩) R92059
theorem R130535 : Reach 130535 := rs (se 1 (by rfl) ⟨97901, by rfl⟩) R195803
theorem R130667 : Reach 130667 := rs (se 1 (by rfl) ⟨98000, by rfl⟩) R196001
theorem R163471 : Reach 163471 := rs (se 1 (by rfl) ⟨122603, by rfl⟩) R245207
theorem R491255 : Reach 491255 := rs (se 1 (by rfl) ⟨368441, by rfl⟩) R736883
theorem R229243 : Reach 229243 := rs (se 1 (by rfl) ⟨171932, by rfl⟩) R343865
theorem R950615 : Reach 950615 := rs (se 1 (by rfl) ⟨712961, by rfl⟩) R1425923
theorem R3703481 : Reach 3703481 := rs (se 2 (by rfl) ⟨1388805, by rfl⟩) R2777611
theorem R328445 : Reach 328445 := rs (se 3 (by rfl) ⟨61583, by rfl⟩) R123167
theorem R230507 : Reach 230507 := rs (se 1 (by rfl) ⟨172880, by rfl⟩) R345761
theorem R427355 : Reach 427355 := rs (se 1 (by rfl) ⟨320516, by rfl⟩) R641033
theorem R361847 : Reach 361847 := rs (se 1 (by rfl) ⟨271385, by rfl⟩) R542771
theorem R263711 : Reach 263711 := rs (se 1 (by rfl) ⟨197783, by rfl⟩) R395567
theorem R919259 : Reach 919259 := rs (se 1 (by rfl) ⟨689444, by rfl⟩) R1378889
theorem R329615 : Reach 329615 := rs (se 1 (by rfl) ⟨247211, by rfl⟩) R494423
theorem R1148995 : Reach 1148995 := rs (se 1 (by rfl) ⟨861746, by rfl⟩) R1723493
theorem R985483 : Reach 985483 := rs (se 1 (by rfl) ⟨739112, by rfl⟩) R1478225
theorem R134207 : Reach 134207 := rs (se 1 (by rfl) ⟨100655, by rfl⟩) R201311
theorem R1577009 : Reach 1577009 := rs (se 2 (by rfl) ⟨591378, by rfl⟩) R1182757
theorem R528707 : Reach 528707 := rs (se 1 (by rfl) ⟨396530, by rfl⟩) R793061
theorem R528977 : Reach 528977 := rs (se 2 (by rfl) ⟨198366, by rfl⟩) R396733
theorem R103231 : Reach 103231 := rs (se 1 (by rfl) ⟨77423, by rfl⟩) R154847
theorem R234323 : Reach 234323 := rs (se 1 (by rfl) ⟨175742, by rfl⟩) R351485
theorem R103259 : Reach 103259 := rs (se 1 (by rfl) ⟨77444, by rfl⟩) R154889
theorem R660383 : Reach 660383 := rs (se 1 (by rfl) ⟨495287, by rfl⟩) R990575
theorem R267695 : Reach 267695 := rs (se 1 (by rfl) ⟨200771, by rfl⟩) R401543
theorem R235361 : Reach 235361 := rs (se 2 (by rfl) ⟨88260, by rfl⟩) R176521
theorem R727177 : Reach 727177 := rs (se 2 (by rfl) ⟨272691, by rfl⟩) R545383
theorem R1088579 : Reach 1088579 := rs (se 1 (by rfl) ⟨816434, by rfl⟩) R1632869
theorem R728135 : Reach 728135 := rs (se 1 (by rfl) ⟨546101, by rfl⟩) R1092203
theorem R368135 : Reach 368135 := rs (se 1 (by rfl) ⟨276101, by rfl⟩) R552203
theorem R1056503 : Reach 1056503 := rs (se 1 (by rfl) ⟨792377, by rfl⟩) R1584755
theorem R991439 : Reach 991439 := rs (se 1 (by rfl) ⟨743579, by rfl⟩) R1487159
theorem R205519 : Reach 205519 := rs (se 1 (by rfl) ⟨154139, by rfl⟩) R308279
theorem R402887 : Reach 402887 := rs (se 1 (by rfl) ⟨302165, by rfl⟩) R604331
theorem R140791 : Reach 140791 := rs (se 1 (by rfl) ⟨105593, by rfl⟩) R211187
theorem R206327 : Reach 206327 := rs (se 1 (by rfl) ⟨154745, by rfl⟩) R309491
theorem R599717 : Reach 599717 := rs (se 4 (by rfl) ⟨56223, by rfl⟩) R112447
theorem R108479 : Reach 108479 := rs (se 1 (by rfl) ⟨81359, by rfl⟩) R162719
theorem R632771 : Reach 632771 := rs (se 1 (by rfl) ⟨474578, by rfl⟩) R949157
theorem R1648997 : Reach 1648997 := rs (se 4 (by rfl) ⟨154593, by rfl⟩) R309187
theorem R141817 : Reach 141817 := rs (se 2 (by rfl) ⟨53181, by rfl⟩) R106363
theorem R305657 : Reach 305657 := rs (se 2 (by rfl) ⟨114621, by rfl⟩) R229243
theorem R141871 : Reach 141871 := rs (se 1 (by rfl) ⟨106403, by rfl⟩) R212807
theorem R469727 : Reach 469727 := rs (se 1 (by rfl) ⟨352295, by rfl⟩) R704591
theorem R142087 : Reach 142087 := rs (se 1 (by rfl) ⟨106565, by rfl⟩) R213131
theorem R207623 : Reach 207623 := rs (se 1 (by rfl) ⟨155717, by rfl⟩) R311435
theorem R142303 : Reach 142303 := rs (se 1 (by rfl) ⟨106727, by rfl⟩) R213455
theorem R371911 : Reach 371911 := rs (se 1 (by rfl) ⟨278933, by rfl⟩) R557867
theorem R240889 : Reach 240889 := rs (se 2 (by rfl) ⟨90333, by rfl⟩) R180667
theorem R175841 : Reach 175841 := rs (se 2 (by rfl) ⟨65940, by rfl⟩) R131881
theorem R143167 : Reach 143167 := rs (se 1 (by rfl) ⟨107375, by rfl⟩) R214751
theorem R405485 : Reach 405485 := rs (se 3 (by rfl) ⟨76028, by rfl⟩) R152057
theorem R242119 : Reach 242119 := rs (se 1 (by rfl) ⟨181589, by rfl⟩) R363179
theorem R406205 : Reach 406205 := rs (se 3 (by rfl) ⟨76163, by rfl⟩) R152327
theorem R701131 : Reach 701131 := rs (se 1 (by rfl) ⟨525848, by rfl⟩) R1051697
theorem R144335 : Reach 144335 := rs (se 1 (by rfl) ⟨108251, by rfl⟩) R216503
theorem R242939 : Reach 242939 := rs (se 1 (by rfl) ⟨182204, by rfl⟩) R364409
theorem R210671 : Reach 210671 := rs (se 1 (by rfl) ⟨158003, by rfl⟩) R316007
theorem R15677509 : Reach 15677509 := rs (se 4 (by rfl) ⟨1469766, by rfl⟩) R2939533
theorem R768365 : Reach 768365 := rs (se 3 (by rfl) ⟨144068, by rfl⟩) R288137
theorem R833915 : Reach 833915 := rs (se 1 (by rfl) ⟨625436, by rfl⟩) R1250873
theorem R146063 : Reach 146063 := rs (se 1 (by rfl) ⟨109547, by rfl⟩) R219095
theorem R211643 : Reach 211643 := rs (se 1 (by rfl) ⟨158732, by rfl⟩) R317465
theorem R474169 : Reach 474169 := rs (se 2 (by rfl) ⟨177813, by rfl⟩) R355627
theorem R2178251 : Reach 2178251 := rs (se 1 (by rfl) ⟨1633688, by rfl⟩) R3267377
theorem R179425 : Reach 179425 := rs (se 2 (by rfl) ⟨67284, by rfl⟩) R134569
theorem R2866747 : Reach 2866747 := rs (se 1 (by rfl) ⟨2150060, by rfl⟩) R4300121
theorem R737261 : Reach 737261 := rs (se 3 (by rfl) ⟨138236, by rfl⟩) R276473
theorem R377081 : Reach 377081 := rs (se 2 (by rfl) ⟨141405, by rfl⟩) R282811
theorem R606467 : Reach 606467 := rs (se 1 (by rfl) ⟨454850, by rfl⟩) R909701
theorem R1229363 : Reach 1229363 := rs (se 1 (by rfl) ⟨922022, by rfl⟩) R1844045
theorem R508837 : Reach 508837 := rs (se 4 (by rfl) ⟨47703, by rfl⟩) R95407
theorem R83135 : Reach 83135 := rs (se 1 (by rfl) ⟨62351, by rfl⟩) R124703
theorem R83167 : Reach 83167 := rs (se 1 (by rfl) ⟨62375, by rfl⟩) R124751
theorem R83247 : Reach 83247 := rs (se 1 (by rfl) ⟨62435, by rfl⟩) R124871
theorem R83483 : Reach 83483 := rs (se 1 (by rfl) ⟨62612, by rfl⟩) R125225
theorem R83487 : Reach 83487 := rs (se 1 (by rfl) ⟨62615, by rfl⟩) R125231
theorem R181931 : Reach 181931 := rs (se 1 (by rfl) ⟨136448, by rfl⟩) R272897
theorem R83647 : Reach 83647 := rs (se 1 (by rfl) ⟨62735, by rfl⟩) R125471
theorem R83903 : Reach 83903 := rs (se 1 (by rfl) ⟨62927, by rfl⟩) R125855
theorem R83935 : Reach 83935 := rs (se 1 (by rfl) ⟨62951, by rfl⟩) R125903
theorem R83995 : Reach 83995 := rs (se 1 (by rfl) ⟨62996, by rfl⟩) R125993
theorem R83999 : Reach 83999 := rs (se 1 (by rfl) ⟨62999, by rfl⟩) R125999
theorem R84015 : Reach 84015 := rs (se 1 (by rfl) ⟨63011, by rfl⟩) R126023
theorem R84191 : Reach 84191 := rs (se 1 (by rfl) ⟨63143, by rfl⟩) R126287
theorem R84251 : Reach 84251 := rs (se 1 (by rfl) ⟨63188, by rfl⟩) R126377
theorem R215419 : Reach 215419 := rs (se 1 (by rfl) ⟨161564, by rfl⟩) R323129
theorem R149887 : Reach 149887 := rs (se 1 (by rfl) ⟨112415, by rfl⟩) R224831
theorem R84351 : Reach 84351 := rs (se 1 (by rfl) ⟨63263, by rfl⟩) R126527
theorem R84527 : Reach 84527 := rs (se 1 (by rfl) ⟨63395, by rfl⟩) R126791
theorem R84583 : Reach 84583 := rs (se 1 (by rfl) ⟨63437, by rfl⟩) R126875
theorem R84959 : Reach 84959 := rs (se 1 (by rfl) ⟨63719, by rfl⟩) R127439
theorem R84987 : Reach 84987 := rs (se 1 (by rfl) ⟨63740, by rfl⟩) R127481
theorem R281609 : Reach 281609 := rs (se 2 (by rfl) ⟨105603, by rfl⟩) R211207
theorem R85055 : Reach 85055 := rs (se 1 (by rfl) ⟨63791, by rfl⟩) R127583
theorem R183359 : Reach 183359 := rs (se 1 (by rfl) ⟨137519, by rfl⟩) R275039
theorem R85375 : Reach 85375 := rs (se 1 (by rfl) ⟨64031, by rfl⟩) R128063
theorem R85403 : Reach 85403 := rs (se 1 (by rfl) ⟨64052, by rfl⟩) R128105
theorem R85471 : Reach 85471 := rs (se 1 (by rfl) ⟨64103, by rfl⟩) R128207
theorem R1035767 : Reach 1035767 := rs (se 1 (by rfl) ⟨776825, by rfl⟩) R1553651
theorem R85607 : Reach 85607 := rs (se 1 (by rfl) ⟨64205, by rfl⟩) R128411
theorem R85755 : Reach 85755 := rs (se 1 (by rfl) ⟨64316, by rfl⟩) R128633
theorem R216857 : Reach 216857 := rs (se 2 (by rfl) ⟨81321, by rfl⟩) R162643
theorem R85823 : Reach 85823 := rs (se 1 (by rfl) ⟨64367, by rfl⟩) R128735
theorem R184187 : Reach 184187 := rs (se 1 (by rfl) ⟨138140, by rfl⟩) R276281
theorem R85887 : Reach 85887 := rs (se 1 (by rfl) ⟨64415, by rfl⟩) R128831
theorem R118759 : Reach 118759 := rs (se 1 (by rfl) ⟨89069, by rfl⟩) R178139
theorem R85999 : Reach 85999 := rs (se 1 (by rfl) ⟨64499, by rfl⟩) R128999
theorem R86011 : Reach 86011 := rs (se 1 (by rfl) ⟨64508, by rfl⟩) R129017
theorem R86079 : Reach 86079 := rs (se 1 (by rfl) ⟨64559, by rfl⟩) R129119
theorem R86119 : Reach 86119 := rs (se 1 (by rfl) ⟨64589, by rfl⟩) R129179
theorem R86143 : Reach 86143 := rs (se 1 (by rfl) ⟨64607, by rfl⟩) R129215
theorem R86171 : Reach 86171 := rs (se 1 (by rfl) ⟨64628, by rfl⟩) R129257
theorem R86375 : Reach 86375 := rs (se 1 (by rfl) ⟨64781, by rfl⟩) R129563
theorem R86427 : Reach 86427 := rs (se 1 (by rfl) ⟨64820, by rfl⟩) R129641
theorem R283067 : Reach 283067 := rs (se 1 (by rfl) ⟨212300, by rfl⟩) R424601
theorem R119351 : Reach 119351 := rs (se 1 (by rfl) ⟨89513, by rfl⟩) R179027
theorem R250505 : Reach 250505 := rs (se 2 (by rfl) ⟨93939, by rfl⟩) R187879
theorem R86779 : Reach 86779 := rs (se 1 (by rfl) ⟨65084, by rfl⟩) R130169
theorem R3134213 : Reach 3134213 := rs (se 4 (by rfl) ⟨293832, by rfl⟩) R587665
theorem R1430297 : Reach 1430297 := rs (se 2 (by rfl) ⟨536361, by rfl⟩) R1072723
theorem R86847 : Reach 86847 := rs (se 1 (by rfl) ⟨65135, by rfl⟩) R130271
theorem R86875 : Reach 86875 := rs (se 1 (by rfl) ⟨65156, by rfl⟩) R130313
theorem R217961 : Reach 217961 := rs (se 2 (by rfl) ⟨81735, by rfl⟩) R163471
theorem R86943 : Reach 86943 := rs (se 1 (by rfl) ⟨65207, by rfl⟩) R130415
theorem R283607 : Reach 283607 := rs (se 1 (by rfl) ⟨212705, by rfl⟩) R425411
theorem R87023 : Reach 87023 := rs (se 1 (by rfl) ⟨65267, by rfl⟩) R130535
theorem R87111 : Reach 87111 := rs (se 1 (by rfl) ⟨65333, by rfl⟩) R130667
theorem R2152007 : Reach 2152007 := rs (se 1 (by rfl) ⟨1614005, by rfl⟩) R3228011
theorem R350171 : Reach 350171 := rs (se 1 (by rfl) ⟨262628, by rfl⟩) R525257
theorem R317479 : Reach 317479 := rs (se 1 (by rfl) ⟨238109, by rfl⟩) R476219
theorem R317753 : Reach 317753 := rs (se 2 (by rfl) ⟨119157, by rfl⟩) R238315
theorem R219449 : Reach 219449 := rs (se 2 (by rfl) ⟨82293, by rfl⟩) R164587
theorem R285011 : Reach 285011 := rs (se 1 (by rfl) ⟨213758, by rfl⟩) R427517
theorem R2087279 : Reach 2087279 := rs (se 1 (by rfl) ⟨1565459, by rfl⟩) R3130919
theorem R285551 : Reach 285551 := rs (se 1 (by rfl) ⟨214163, by rfl⟩) R428327
theorem R285659 : Reach 285659 := rs (se 1 (by rfl) ⟨214244, by rfl⟩) R428489
theorem R351211 : Reach 351211 := rs (se 1 (by rfl) ⟨263408, by rfl⟩) R526817
theorem R810161 : Reach 810161 := rs (se 2 (by rfl) ⟨303810, by rfl⟩) R607621
theorem R285929 : Reach 285929 := rs (se 2 (by rfl) ⟨107223, by rfl⟩) R214447
theorem R417257 : Reach 417257 := rs (se 2 (by rfl) ⟨156471, by rfl⟩) R312943
theorem R286199 : Reach 286199 := rs (se 1 (by rfl) ⟨214649, by rfl⟩) R429299
theorem R188315 : Reach 188315 := rs (se 1 (by rfl) ⟨141236, by rfl⟩) R282473
theorem R188729 : Reach 188729 := rs (se 2 (by rfl) ⟨70773, by rfl⟩) R141547
theorem R123611 : Reach 123611 := rs (se 1 (by rfl) ⟨92708, by rfl⟩) R185417
theorem R189215 : Reach 189215 := rs (se 1 (by rfl) ⟨141911, by rfl⟩) R283823
theorem R779165 : Reach 779165 := rs (se 3 (by rfl) ⟨146093, by rfl⟩) R292187
theorem R779453 : Reach 779453 := rs (se 3 (by rfl) ⟨146147, by rfl⟩) R292295
theorem R1598939 : Reach 1598939 := rs (se 1 (by rfl) ⟨1199204, by rfl⟩) R2398409
theorem R353819 : Reach 353819 := rs (se 1 (by rfl) ⟨265364, by rfl⟩) R530729
theorem R190025 : Reach 190025 := rs (se 2 (by rfl) ⟨71259, by rfl⟩) R142519
theorem R353945 : Reach 353945 := rs (se 2 (by rfl) ⟨132729, by rfl⟩) R265459
theorem R616211 : Reach 616211 := rs (se 1 (by rfl) ⟨462158, by rfl⟩) R924317
theorem R3860261 : Reach 3860261 := rs (se 4 (by rfl) ⟨361899, by rfl⟩) R723799
theorem R124895 : Reach 124895 := rs (se 1 (by rfl) ⟨93671, by rfl⟩) R187343
theorem R124907 : Reach 124907 := rs (se 1 (by rfl) ⟨93680, by rfl⟩) R187361
theorem R190457 : Reach 190457 := rs (se 2 (by rfl) ⟨71421, by rfl⟩) R142843
theorem R124955 : Reach 124955 := rs (se 1 (by rfl) ⟨93716, by rfl⟩) R187433
theorem R190511 : Reach 190511 := rs (se 1 (by rfl) ⟨142883, by rfl⟩) R285767
theorem R190547 : Reach 190547 := rs (se 1 (by rfl) ⟨142910, by rfl⟩) R285821
theorem R190727 : Reach 190727 := rs (se 1 (by rfl) ⟨143045, by rfl⟩) R286091
theorem R321839 : Reach 321839 := rs (se 1 (by rfl) ⟨241379, by rfl⟩) R482759
theorem R125321 : Reach 125321 := rs (se 2 (by rfl) ⟨46995, by rfl⟩) R93991
theorem R289295 : Reach 289295 := rs (se 1 (by rfl) ⟨216971, by rfl⟩) R433943
theorem R191033 : Reach 191033 := rs (se 2 (by rfl) ⟨71637, by rfl⟩) R143275
theorem R191753 : Reach 191753 := rs (se 2 (by rfl) ⟨71907, by rfl⟩) R143815
theorem R126263 : Reach 126263 := rs (se 1 (by rfl) ⟨94697, by rfl⟩) R189395
theorem R93595 : Reach 93595 := rs (se 1 (by rfl) ⟨70196, by rfl⟩) R140393
theorem R1174985 : Reach 1174985 := rs (se 2 (by rfl) ⟨440619, by rfl⟩) R881239
theorem R126431 : Reach 126431 := rs (se 1 (by rfl) ⟨94823, by rfl⟩) R189647
theorem R126647 : Reach 126647 := rs (se 1 (by rfl) ⟨94985, by rfl⟩) R189971
theorem R552673 : Reach 552673 := rs (se 2 (by rfl) ⟨207252, by rfl⟩) R414505
theorem R323297 : Reach 323297 := rs (se 2 (by rfl) ⟨121236, by rfl⟩) R242473
theorem R552743 : Reach 552743 := rs (se 1 (by rfl) ⟨414557, by rfl⟩) R829115
theorem R126857 : Reach 126857 := rs (se 2 (by rfl) ⟨47571, by rfl⟩) R95143
theorem R356345 : Reach 356345 := rs (se 2 (by rfl) ⟨133629, by rfl⟩) R267259
theorem R2191373 : Reach 2191373 := rs (se 3 (by rfl) ⟨410882, by rfl⟩) R821765
theorem R127103 : Reach 127103 := rs (se 1 (by rfl) ⟨95327, by rfl⟩) R190655
theorem R159887 : Reach 159887 := rs (se 1 (by rfl) ⟨119915, by rfl⟩) R239831
theorem R192743 : Reach 192743 := rs (se 1 (by rfl) ⟨144557, by rfl⟩) R289115
theorem R487705 : Reach 487705 := rs (se 2 (by rfl) ⟨182889, by rfl⟩) R365779
theorem R94567 : Reach 94567 := rs (se 1 (by rfl) ⟨70925, by rfl⟩) R141851
theorem R192923 : Reach 192923 := rs (se 1 (by rfl) ⟨144692, by rfl⟩) R289385
theorem R324091 : Reach 324091 := rs (se 1 (by rfl) ⟨243068, by rfl⟩) R486137
theorem R488065 : Reach 488065 := rs (se 2 (by rfl) ⟨183024, by rfl⟩) R366049
theorem R127739 : Reach 127739 := rs (se 1 (by rfl) ⟨95804, by rfl⟩) R191609
theorem R619325 : Reach 619325 := rs (se 3 (by rfl) ⟨116123, by rfl⟩) R232247
theorem R95215 : Reach 95215 := rs (se 1 (by rfl) ⟨71411, by rfl⟩) R142823
theorem R193607 : Reach 193607 := rs (se 1 (by rfl) ⟨145205, by rfl⟩) R290411
theorem R291923 : Reach 291923 := rs (se 1 (by rfl) ⟨218942, by rfl⟩) R437885
theorem R128183 : Reach 128183 := rs (se 1 (by rfl) ⟨96137, by rfl⟩) R192275
theorem R193787 : Reach 193787 := rs (se 1 (by rfl) ⟨145340, by rfl⟩) R290681
theorem R554303 : Reach 554303 := rs (se 1 (by rfl) ⟨415727, by rfl⟩) R831455
theorem R128423 : Reach 128423 := rs (se 1 (by rfl) ⟨96317, by rfl⟩) R192635
theorem R194003 : Reach 194003 := rs (se 1 (by rfl) ⟨145502, by rfl⟩) R291005
theorem R95719 : Reach 95719 := rs (se 1 (by rfl) ⟨71789, by rfl⟩) R143579
theorem R128603 : Reach 128603 := rs (se 1 (by rfl) ⟨96452, by rfl⟩) R192905
theorem R292463 : Reach 292463 := rs (se 1 (by rfl) ⟨219347, by rfl⟩) R438695
theorem R95899 : Reach 95899 := rs (se 1 (by rfl) ⟨71924, by rfl⟩) R143849
theorem R194273 : Reach 194273 := rs (se 2 (by rfl) ⟨72852, by rfl⟩) R145705
theorem R129065 : Reach 129065 := rs (se 2 (by rfl) ⟨48399, by rfl⟩) R96799
theorem R129095 : Reach 129095 := rs (se 1 (by rfl) ⟨96821, by rfl⟩) R193643
theorem R161975 : Reach 161975 := rs (se 1 (by rfl) ⟨121481, by rfl⟩) R242963
theorem R1013971 : Reach 1013971 := rs (se 1 (by rfl) ⟨760478, by rfl⟩) R1520957
theorem R194795 : Reach 194795 := rs (se 1 (by rfl) ⟨146096, by rfl⟩) R292193
theorem R555407 : Reach 555407 := rs (se 1 (by rfl) ⟨416555, by rfl⟩) R833111
theorem R129479 : Reach 129479 := rs (se 1 (by rfl) ⟨97109, by rfl⟩) R194219
theorem R293327 : Reach 293327 := rs (se 1 (by rfl) ⟨219995, by rfl⟩) R439991
theorem R359009 : Reach 359009 := rs (se 2 (by rfl) ⟨134628, by rfl⟩) R269257
theorem R129695 : Reach 129695 := rs (se 1 (by rfl) ⟨97271, by rfl⟩) R194543
theorem R359147 : Reach 359147 := rs (se 1 (by rfl) ⟨269360, by rfl⟩) R538721
theorem R162539 : Reach 162539 := rs (se 1 (by rfl) ⟨121904, by rfl⟩) R243809
theorem R129839 : Reach 129839 := rs (se 1 (by rfl) ⟨97379, by rfl⟩) R194759
theorem R588703 : Reach 588703 := rs (se 1 (by rfl) ⟨441527, by rfl⟩) R883055
theorem R129959 : Reach 129959 := rs (se 1 (by rfl) ⟨97469, by rfl⟩) R194939
theorem R130139 : Reach 130139 := rs (se 1 (by rfl) ⟨97604, by rfl⟩) R195209
theorem R654641 : Reach 654641 := rs (se 2 (by rfl) ⟨245490, by rfl⟩) R490981
theorem R163279 : Reach 163279 := rs (se 1 (by rfl) ⟨122459, by rfl⟩) R244919
theorem R130511 : Reach 130511 := rs (se 1 (by rfl) ⟨97883, by rfl⟩) R195767
theorem R1244645 : Reach 1244645 := rs (se 4 (by rfl) ⟨116685, by rfl⟩) R233371
theorem R1474037 : Reach 1474037 := rs (se 5 (by rfl) ⟨69095, by rfl⟩) R138191
theorem R327503 : Reach 327503 := rs (se 1 (by rfl) ⟨245627, by rfl⟩) R491255
theorem R819575 : Reach 819575 := rs (se 1 (by rfl) ⟨614681, by rfl⟩) R1229363
theorem R1410605 : Reach 1410605 := rs (se 3 (by rfl) ⟨264488, by rfl⟩) R528977
theorem R329629 : Reach 329629 := rs (se 3 (by rfl) ⟨61805, by rfl⟩) R123611
theorem R1051339 : Reach 1051339 := rs (se 1 (by rfl) ⟨788504, by rfl⟩) R1577009
theorem R167003 : Reach 167003 := rs (se 1 (by rfl) ⟨125252, by rfl⟩) R250505
theorem R199849 : Reach 199849 := rs (se 2 (by rfl) ⟨74943, by rfl⟩) R149887
theorem R1313977 : Reach 1313977 := rs (se 2 (by rfl) ⟨492741, by rfl⟩) R985483
theorem R953531 : Reach 953531 := rs (se 1 (by rfl) ⟨715148, by rfl⟩) R1430297
theorem R233447 : Reach 233447 := rs (se 1 (by rfl) ⟨175085, by rfl⟩) R350171
theorem R495881 : Reach 495881 := rs (se 2 (by rfl) ⟨185955, by rfl⟩) R371911
theorem R725719 : Reach 725719 := rs (se 1 (by rfl) ⟨544289, by rfl⟩) R1088579
theorem R660959 : Reach 660959 := rs (se 1 (by rfl) ⟨495719, by rfl⟩) R991439
theorem R432121 : Reach 432121 := rs (se 2 (by rfl) ⟨162045, by rfl⟩) R324091
theorem R268591 : Reach 268591 := rs (se 1 (by rfl) ⟨201443, by rfl⟩) R402887
theorem R137551 : Reach 137551 := rs (se 1 (by rfl) ⟨103163, by rfl⟩) R206327
theorem R235879 : Reach 235879 := rs (se 1 (by rfl) ⟨176909, by rfl⟩) R353819
theorem R137641 : Reach 137641 := rs (se 2 (by rfl) ⟨51615, by rfl⟩) R103231
theorem R235963 : Reach 235963 := rs (se 1 (by rfl) ⟨176972, by rfl⟩) R353945
theorem R399811 : Reach 399811 := rs (se 1 (by rfl) ⟨299858, by rfl⟩) R599717
theorem R203771 : Reach 203771 := rs (se 1 (by rfl) ⟨152828, by rfl⟩) R305657
theorem R368495 : Reach 368495 := rs (se 1 (by rfl) ⟨276371, by rfl⟩) R552743
theorem R270323 : Reach 270323 := rs (se 1 (by rfl) ⟨202742, by rfl⟩) R405485
theorem R237563 : Reach 237563 := rs (se 1 (by rfl) ⟨178172, by rfl⟩) R356345
theorem R106591 : Reach 106591 := rs (se 1 (by rfl) ⟨79943, by rfl⟩) R159887
theorem R1351961 : Reach 1351961 := rs (se 2 (by rfl) ⟨506985, by rfl⟩) R1013971
theorem R270803 : Reach 270803 := rs (se 1 (by rfl) ⟨203102, by rfl⟩) R406205
theorem R369535 : Reach 369535 := rs (se 1 (by rfl) ⟨277151, by rfl⟩) R554303
theorem R140447 : Reach 140447 := rs (se 1 (by rfl) ⟨105335, by rfl⟩) R210671
theorem R468281 : Reach 468281 := rs (se 2 (by rfl) ⟨175605, by rfl⟩) R351211
theorem R2762045 : Reach 2762045 := rs (se 3 (by rfl) ⟨517883, by rfl⟩) R1035767
theorem R632225 : Reach 632225 := rs (se 2 (by rfl) ⟨237084, by rfl⟩) R474169
theorem R107983 : Reach 107983 := rs (se 1 (by rfl) ⟨80987, by rfl⟩) R161975
theorem R370271 : Reach 370271 := rs (se 1 (by rfl) ⟨277703, by rfl⟩) R555407
theorem R239233 : Reach 239233 := rs (se 2 (by rfl) ⟨89712, by rfl⟩) R179425
theorem R239339 : Reach 239339 := rs (se 1 (by rfl) ⟨179504, by rfl⟩) R359009
theorem R141095 : Reach 141095 := rs (se 1 (by rfl) ⟨105821, by rfl⟩) R211643
theorem R239431 : Reach 239431 := rs (se 1 (by rfl) ⟨179573, by rfl⟩) R359147
theorem R108359 : Reach 108359 := rs (se 1 (by rfl) ⟨81269, by rfl⟩) R162539
theorem R1452167 : Reach 1452167 := rs (se 1 (by rfl) ⟨1089125, by rfl⟩) R2178251
theorem R436427 : Reach 436427 := rs (se 1 (by rfl) ⟨327320, by rfl⟩) R654641
theorem R829763 : Reach 829763 := rs (se 1 (by rfl) ⟨622322, by rfl⟩) R1244645
theorem R404311 : Reach 404311 := rs (se 1 (by rfl) ⟨303233, by rfl⟩) R606467
theorem R633743 : Reach 633743 := rs (se 1 (by rfl) ⟨475307, by rfl⟩) R950615
theorem R2468987 : Reach 2468987 := rs (se 1 (by rfl) ⟨1851740, by rfl⟩) R3703481
theorem R241231 : Reach 241231 := rs (se 1 (by rfl) ⟨180923, by rfl⟩) R361847
theorem R274025 : Reach 274025 := rs (se 2 (by rfl) ⟨102759, by rfl⟩) R205519
theorem R175807 : Reach 175807 := rs (se 1 (by rfl) ⟨131855, by rfl⟩) R263711
theorem R275357 : Reach 275357 := rs (se 3 (by rfl) ⟨51629, by rfl⟩) R103259
theorem R144571 : Reach 144571 := rs (se 1 (by rfl) ⟨108428, by rfl⟩) R216857
theorem R145307 : Reach 145307 := rs (se 1 (by rfl) ⟨108980, by rfl⟩) R217961
theorem R440255 : Reach 440255 := rs (se 1 (by rfl) ⟨330191, by rfl⟩) R660383
theorem R178463 : Reach 178463 := rs (se 1 (by rfl) ⟨133847, by rfl⟩) R267695
theorem R211835 : Reach 211835 := rs (se 1 (by rfl) ⟨158876, by rfl⟩) R317753
theorem R146299 : Reach 146299 := rs (se 1 (by rfl) ⟨109724, by rfl⟩) R219449
theorem R1391519 : Reach 1391519 := rs (se 1 (by rfl) ⟨1043639, by rfl⟩) R2087279
theorem R540107 : Reach 540107 := rs (se 1 (by rfl) ⟨405080, by rfl⟩) R810161
theorem R736897 : Reach 736897 := rs (se 2 (by rfl) ⟨276336, by rfl⟩) R552673
theorem R278171 : Reach 278171 := rs (se 1 (by rfl) ⟨208628, by rfl⟩) R417257
theorem R245423 : Reach 245423 := rs (se 1 (by rfl) ⟨184067, by rfl⟩) R368135
theorem R704335 : Reach 704335 := rs (se 1 (by rfl) ⟨528251, by rfl⟩) R1056503
theorem R934841 : Reach 934841 := rs (se 2 (by rfl) ⟨350565, by rfl⟩) R701131
theorem R1065959 : Reach 1065959 := rs (se 1 (by rfl) ⟨799469, by rfl⟩) R1598939
theorem R410807 : Reach 410807 := rs (se 1 (by rfl) ⟨308105, by rfl⟩) R616211
theorem R2573507 : Reach 2573507 := rs (se 1 (by rfl) ⟨1930130, by rfl⟩) R3860261
theorem R83263 : Reach 83263 := rs (se 1 (by rfl) ⟨62447, by rfl⟩) R124895
theorem R83271 : Reach 83271 := rs (se 1 (by rfl) ⟨62453, by rfl⟩) R124907
theorem R83303 : Reach 83303 := rs (se 1 (by rfl) ⟨62477, by rfl⟩) R124955
theorem R214559 : Reach 214559 := rs (se 1 (by rfl) ⟨160919, by rfl⟩) R321839
theorem R1099331 : Reach 1099331 := rs (se 1 (by rfl) ⟨824498, by rfl⟩) R1648997
theorem R83547 : Reach 83547 := rs (se 1 (by rfl) ⟨62660, by rfl⟩) R125321
theorem R313151 : Reach 313151 := rs (se 1 (by rfl) ⟨234863, by rfl⟩) R469727
theorem R84175 : Reach 84175 := rs (se 1 (by rfl) ⟨63131, by rfl⟩) R126263
theorem R84287 : Reach 84287 := rs (se 1 (by rfl) ⟨63215, by rfl⟩) R126431
theorem R870821 : Reach 870821 := rs (se 4 (by rfl) ⟨81639, by rfl⟩) R163279
theorem R84431 : Reach 84431 := rs (se 1 (by rfl) ⟨63323, by rfl⟩) R126647
theorem R215531 : Reach 215531 := rs (se 1 (by rfl) ⟨161648, by rfl⟩) R323297
theorem R117227 : Reach 117227 := rs (se 1 (by rfl) ⟨87920, by rfl⟩) R175841
theorem R84571 : Reach 84571 := rs (se 1 (by rfl) ⟨63428, by rfl⟩) R126857
theorem R1460915 : Reach 1460915 := rs (se 1 (by rfl) ⟨1095686, by rfl⟩) R2191373
theorem R84735 : Reach 84735 := rs (se 1 (by rfl) ⟨63551, by rfl⟩) R127103
theorem R969569 : Reach 969569 := rs (se 2 (by rfl) ⟨363588, by rfl⟩) R727177
theorem R85159 : Reach 85159 := rs (se 1 (by rfl) ⟨63869, by rfl⟩) R127739
theorem R412883 : Reach 412883 := rs (se 1 (by rfl) ⟨309662, by rfl⟩) R619325
theorem R85455 : Reach 85455 := rs (se 1 (by rfl) ⟨64091, by rfl⟩) R128183
theorem R85615 : Reach 85615 := rs (se 1 (by rfl) ⟨64211, by rfl⟩) R128423
theorem R85735 : Reach 85735 := rs (se 1 (by rfl) ⟨64301, by rfl⟩) R128603
theorem R86043 : Reach 86043 := rs (se 1 (by rfl) ⟨64532, by rfl⟩) R129065
theorem R86063 : Reach 86063 := rs (se 1 (by rfl) ⟨64547, by rfl⟩) R129095
theorem R512243 : Reach 512243 := rs (se 1 (by rfl) ⟨384182, by rfl⟩) R768365
theorem R86319 : Reach 86319 := rs (se 1 (by rfl) ⟨64739, by rfl⟩) R129479
theorem R86463 : Reach 86463 := rs (se 1 (by rfl) ⟨64847, by rfl⟩) R129695
theorem R86559 : Reach 86559 := rs (se 1 (by rfl) ⟨64919, by rfl⟩) R129839
theorem R86639 : Reach 86639 := rs (se 1 (by rfl) ⟨64979, by rfl⟩) R129959
theorem R86759 : Reach 86759 := rs (se 1 (by rfl) ⟨65069, by rfl⟩) R130139
theorem R3822329 : Reach 3822329 := rs (se 2 (by rfl) ⟨1433373, by rfl⟩) R2866747
theorem R87007 : Reach 87007 := rs (se 1 (by rfl) ⟨65255, by rfl⟩) R130511
theorem R218335 : Reach 218335 := rs (se 1 (by rfl) ⟨163751, by rfl⟩) R327503
theorem R251387 : Reach 251387 := rs (se 1 (by rfl) ⟨188540, by rfl⟩) R377081
theorem R218963 : Reach 218963 := rs (se 1 (by rfl) ⟨164222, by rfl⟩) R328445
theorem R153671 : Reach 153671 := rs (se 1 (by rfl) ⟨115253, by rfl⟩) R230507
theorem R284903 : Reach 284903 := rs (se 1 (by rfl) ⟨213677, by rfl⟩) R427355
theorem R612839 : Reach 612839 := rs (se 1 (by rfl) ⟨459629, by rfl⟩) R919259
theorem R678449 : Reach 678449 := rs (se 2 (by rfl) ⟨254418, by rfl⟩) R508837
theorem R219743 : Reach 219743 := rs (se 1 (by rfl) ⟨164807, by rfl⟩) R329615
theorem R318269 : Reach 318269 := rs (se 3 (by rfl) ⟨59675, by rfl⟩) R119351
theorem R187721 : Reach 187721 := rs (se 2 (by rfl) ⟨70395, by rfl⟩) R140791
theorem R187739 : Reach 187739 := rs (se 1 (by rfl) ⟨140804, by rfl⟩) R281609
theorem R89471 : Reach 89471 := rs (se 1 (by rfl) ⟨67103, by rfl⟩) R134207
theorem R122239 : Reach 122239 := rs (se 1 (by rfl) ⟨91679, by rfl⟩) R183359
theorem R122791 : Reach 122791 := rs (se 1 (by rfl) ⟨92093, by rfl⟩) R184187
theorem R1531993 : Reach 1531993 := rs (se 2 (by rfl) ⟨574497, by rfl⟩) R1148995
theorem R352471 : Reach 352471 := rs (se 1 (by rfl) ⟨264353, by rfl⟩) R528707
theorem R188711 : Reach 188711 := rs (se 1 (by rfl) ⟨141533, by rfl⟩) R283067
theorem R287225 : Reach 287225 := rs (se 2 (by rfl) ⟨107709, by rfl⟩) R215419
theorem R2089475 : Reach 2089475 := rs (se 1 (by rfl) ⟨1567106, by rfl⟩) R3134213
theorem R156215 : Reach 156215 := rs (se 1 (by rfl) ⟨117161, by rfl⟩) R234323
theorem R189071 : Reach 189071 := rs (se 1 (by rfl) ⟨141803, by rfl⟩) R283607
theorem R647837 : Reach 647837 := rs (se 3 (by rfl) ⟨121469, by rfl⟩) R242939
theorem R189089 : Reach 189089 := rs (se 2 (by rfl) ⟨70908, by rfl⟩) R141817
theorem R189161 : Reach 189161 := rs (se 2 (by rfl) ⟨70935, by rfl⟩) R141871
theorem R189449 : Reach 189449 := rs (se 2 (by rfl) ⟨71043, by rfl⟩) R142087
theorem R1434671 : Reach 1434671 := rs (se 1 (by rfl) ⟨1076003, by rfl⟩) R2152007
theorem R156907 : Reach 156907 := rs (se 1 (by rfl) ⟨117680, by rfl⟩) R235361
theorem R189737 : Reach 189737 := rs (se 2 (by rfl) ⟨71151, by rfl⟩) R142303
theorem R190007 : Reach 190007 := rs (se 1 (by rfl) ⟨142505, by rfl⟩) R285011
theorem R321185 : Reach 321185 := rs (se 2 (by rfl) ⟨120444, by rfl⟩) R240889
theorem R485149 : Reach 485149 := rs (se 3 (by rfl) ⟨90965, by rfl⟩) R181931
theorem R124793 : Reach 124793 := rs (se 2 (by rfl) ⟨46797, by rfl⟩) R93595
theorem R190367 : Reach 190367 := rs (se 1 (by rfl) ⟨142775, by rfl⟩) R285551
theorem R190439 : Reach 190439 := rs (se 1 (by rfl) ⟨142829, by rfl⟩) R285659
theorem R485423 : Reach 485423 := rs (se 1 (by rfl) ⟨364067, by rfl⟩) R728135
theorem R190619 : Reach 190619 := rs (se 1 (by rfl) ⟨142964, by rfl⟩) R285929
theorem R190799 : Reach 190799 := rs (se 1 (by rfl) ⟨143099, by rfl⟩) R286199
theorem R190889 : Reach 190889 := rs (se 2 (by rfl) ⟨71583, by rfl⟩) R143167
theorem R289277 : Reach 289277 := rs (se 3 (by rfl) ⟨54239, by rfl⟩) R108479
theorem R125543 : Reach 125543 := rs (se 1 (by rfl) ⟨94157, by rfl⟩) R188315
theorem R158345 : Reach 158345 := rs (se 2 (by rfl) ⟨59379, by rfl⟩) R118759
theorem R125819 : Reach 125819 := rs (se 1 (by rfl) ⟨94364, by rfl⟩) R188729
theorem R650273 : Reach 650273 := rs (se 2 (by rfl) ⟨243852, by rfl⟩) R487705
theorem R126089 : Reach 126089 := rs (se 2 (by rfl) ⟨47283, by rfl⟩) R94567
theorem R126143 : Reach 126143 := rs (se 1 (by rfl) ⟨94607, by rfl⟩) R189215
theorem R322825 : Reach 322825 := rs (se 2 (by rfl) ⟨121059, by rfl⟩) R242119
theorem R519443 : Reach 519443 := rs (se 1 (by rfl) ⟨389582, by rfl⟩) R779165
theorem R519635 : Reach 519635 := rs (se 1 (by rfl) ⟨389726, by rfl⟩) R779453
theorem R650753 : Reach 650753 := rs (se 2 (by rfl) ⟨244032, by rfl⟩) R488065
theorem R126683 : Reach 126683 := rs (se 1 (by rfl) ⟨95012, by rfl⟩) R190025
theorem R421847 : Reach 421847 := rs (se 1 (by rfl) ⟨316385, by rfl⟩) R632771
theorem R126953 : Reach 126953 := rs (se 2 (by rfl) ⟨47607, by rfl⟩) R95215
theorem R126971 : Reach 126971 := rs (se 1 (by rfl) ⟨95228, by rfl⟩) R190457
theorem R127007 : Reach 127007 := rs (se 1 (by rfl) ⟨95255, by rfl⟩) R190511
theorem R127031 : Reach 127031 := rs (se 1 (by rfl) ⟨95273, by rfl⟩) R190547
theorem R127151 : Reach 127151 := rs (se 1 (by rfl) ⟨95363, by rfl⟩) R190727
theorem R192863 : Reach 192863 := rs (se 1 (by rfl) ⟨144647, by rfl⟩) R289295
theorem R127355 : Reach 127355 := rs (se 1 (by rfl) ⟨95516, by rfl⟩) R191033
theorem R127625 : Reach 127625 := rs (se 2 (by rfl) ⟨47859, by rfl⟩) R95719
theorem R553661 : Reach 553661 := rs (se 3 (by rfl) ⟨103811, by rfl⟩) R207623
theorem R127835 : Reach 127835 := rs (se 1 (by rfl) ⟨95876, by rfl⟩) R191753
theorem R127865 : Reach 127865 := rs (se 2 (by rfl) ⟨47949, by rfl⟩) R95899
theorem R783323 : Reach 783323 := rs (se 1 (by rfl) ⟨587492, by rfl⟩) R1174985
theorem R423305 : Reach 423305 := rs (se 2 (by rfl) ⟨158739, by rfl⟩) R317479
theorem R20903345 : Reach 20903345 := rs (se 2 (by rfl) ⟨7838754, by rfl⟩) R15677509
theorem R128495 : Reach 128495 := rs (se 1 (by rfl) ⟨96371, by rfl⟩) R192743
theorem R128615 : Reach 128615 := rs (se 1 (by rfl) ⟨96461, by rfl⟩) R192923
theorem R96223 : Reach 96223 := rs (se 1 (by rfl) ⟨72167, by rfl⟩) R144335
theorem R129071 : Reach 129071 := rs (se 1 (by rfl) ⟨96803, by rfl⟩) R193607
theorem R194615 : Reach 194615 := rs (se 1 (by rfl) ⟨145961, by rfl⟩) R291923
theorem R129191 : Reach 129191 := rs (se 1 (by rfl) ⟨96893, by rfl⟩) R193787
theorem R129335 : Reach 129335 := rs (se 1 (by rfl) ⟨97001, by rfl⟩) R194003
theorem R194975 : Reach 194975 := rs (se 1 (by rfl) ⟨146231, by rfl⟩) R292463
theorem R129515 : Reach 129515 := rs (se 1 (by rfl) ⟨97136, by rfl⟩) R194273
theorem R784937 : Reach 784937 := rs (se 2 (by rfl) ⟨294351, by rfl⟩) R588703
theorem R129863 : Reach 129863 := rs (se 1 (by rfl) ⟨97397, by rfl⟩) R194795
theorem R555943 : Reach 555943 := rs (se 1 (by rfl) ⟨416957, by rfl⟩) R833915
theorem R195551 : Reach 195551 := rs (se 1 (by rfl) ⟨146663, by rfl⟩) R293327
theorem R97375 : Reach 97375 := rs (se 1 (by rfl) ⟨73031, by rfl⟩) R146063
theorem R982691 : Reach 982691 := rs (se 1 (by rfl) ⟨737018, by rfl⟩) R1474037
theorem R491507 : Reach 491507 := rs (se 1 (by rfl) ⟨368630, by rfl⟩) R737261
theorem R623227 : Reach 623227 := rs (se 1 (by rfl) ⟨467420, by rfl⟩) R934841
theorem R492713 : Reach 492713 := rs (se 2 (by rfl) ⟨184767, by rfl⟩) R369535
theorem R10192877 : Reach 10192877 := rs (se 3 (by rfl) ⟨1911164, by rfl⟩) R3822329
theorem R330587 : Reach 330587 := rs (se 1 (by rfl) ⟨247940, by rfl⟩) R495881
theorem R167591 : Reach 167591 := rs (se 1 (by rfl) ⟨125693, by rfl⟩) R251387
theorem R266465 : Reach 266465 := rs (se 2 (by rfl) ⟨99924, by rfl⟩) R199849
theorem R430433 : Reach 430433 := rs (se 2 (by rfl) ⟨161412, by rfl⟩) R322825
theorem R135847 : Reach 135847 := rs (se 1 (by rfl) ⟨101885, by rfl⟩) R203771
theorem R234409 : Reach 234409 := rs (se 2 (by rfl) ⟨87903, by rfl⟩) R175807
theorem R431891 : Reach 431891 := rs (se 1 (by rfl) ⟨323918, by rfl⟩) R647837
theorem R956447 : Reach 956447 := rs (se 1 (by rfl) ⟨717335, by rfl⟩) R1434671
theorem R1841363 : Reach 1841363 := rs (se 1 (by rfl) ⟨1381022, by rfl⟩) R2762045
theorem R105563 : Reach 105563 := rs (se 1 (by rfl) ⟨79172, by rfl⟩) R158345
theorem R1645991 : Reach 1645991 := rs (se 1 (by rfl) ⟨1234493, by rfl⟩) R2468987
theorem R433835 : Reach 433835 := rs (se 1 (by rfl) ⟨325376, by rfl⟩) R650753
theorem R369107 : Reach 369107 := rs (se 1 (by rfl) ⟨276830, by rfl⟩) R553661
theorem R533081 : Reach 533081 := rs (se 2 (by rfl) ⟨199905, by rfl⟩) R399811
theorem R1155829 : Reach 1155829 := rs (se 5 (by rfl) ⟨54179, by rfl⟩) R108359
theorem R13935563 : Reach 13935563 := rs (se 1 (by rfl) ⟨10451672, by rfl⟩) R20903345
theorem R238589 : Reach 238589 := rs (se 3 (by rfl) ⟨44735, by rfl⟩) R89471
theorem R1385693 : Reach 1385693 := rs (se 3 (by rfl) ⟨259817, by rfl⟩) R519635
theorem R141223 : Reach 141223 := rs (se 1 (by rfl) ⟨105917, by rfl⟩) R211835
theorem R927679 : Reach 927679 := rs (se 1 (by rfl) ⟨695759, by rfl⟩) R1391519
theorem R2042657 : Reach 2042657 := rs (se 2 (by rfl) ⟨765996, by rfl⟩) R1531993
theorem R142121 : Reach 142121 := rs (se 2 (by rfl) ⟨53295, by rfl⟩) R106591
theorem R469961 : Reach 469961 := rs (se 2 (by rfl) ⟨176235, by rfl⟩) R352471
theorem R273871 : Reach 273871 := rs (se 1 (by rfl) ⟨205403, by rfl⟩) R410807
theorem R1715671 : Reach 1715671 := rs (se 1 (by rfl) ⟨1286753, by rfl⟩) R2573507
theorem R143039 : Reach 143039 := rs (se 1 (by rfl) ⟨107279, by rfl⟩) R214559
theorem R732887 : Reach 732887 := rs (se 1 (by rfl) ⟨549665, by rfl⟩) R1099331
theorem R143687 : Reach 143687 := rs (se 1 (by rfl) ⟨107765, by rfl⟩) R215531
theorem R1258021 : Reach 1258021 := rs (se 4 (by rfl) ⟨117939, by rfl⟩) R235879
theorem R143977 : Reach 143977 := rs (se 2 (by rfl) ⟨53991, by rfl⟩) R107983
theorem R111335 : Reach 111335 := rs (se 1 (by rfl) ⟨83501, by rfl⟩) R167003
theorem R635687 : Reach 635687 := rs (se 1 (by rfl) ⟨476765, by rfl⟩) R953531
theorem R275255 : Reach 275255 := rs (se 1 (by rfl) ⟨206441, by rfl⟩) R412883
theorem R734285 : Reach 734285 := rs (se 3 (by rfl) ⟨137678, by rfl⟩) R275357
theorem R439505 : Reach 439505 := rs (se 2 (by rfl) ⟨164814, by rfl⟩) R329629
theorem R341495 : Reach 341495 := rs (se 1 (by rfl) ⟨256121, by rfl⟩) R512243
theorem R440639 : Reach 440639 := rs (se 1 (by rfl) ⟨330479, by rfl⟩) R660959
theorem R539081 : Reach 539081 := rs (se 2 (by rfl) ⟨202155, by rfl⟩) R404311
theorem R145975 : Reach 145975 := rs (se 1 (by rfl) ⟨109481, by rfl⟩) R218963
theorem R1751969 : Reach 1751969 := rs (se 2 (by rfl) ⟨656988, by rfl⟩) R1313977
theorem R408559 : Reach 408559 := rs (se 1 (by rfl) ⟨306419, by rfl⟩) R612839
theorem R146495 : Reach 146495 := rs (se 1 (by rfl) ⟨109871, by rfl⟩) R219743
theorem R212179 : Reach 212179 := rs (se 1 (by rfl) ⟨159134, by rfl⟩) R318269
theorem R638237 : Reach 638237 := rs (se 3 (by rfl) ⟨119669, by rfl⟩) R239339
theorem R835069 : Reach 835069 := rs (se 3 (by rfl) ⟨156575, by rfl⟩) R313151
theorem R245663 : Reach 245663 := rs (se 1 (by rfl) ⟨184247, by rfl⟩) R368495
theorem R180215 : Reach 180215 := rs (se 1 (by rfl) ⟨135161, by rfl⟩) R270323
theorem R901307 : Reach 901307 := rs (se 1 (by rfl) ⟨675980, by rfl⟩) R1351961
theorem R409789 : Reach 409789 := rs (se 3 (by rfl) ⟨76835, by rfl⟩) R153671
theorem R180535 : Reach 180535 := rs (se 1 (by rfl) ⟨135401, by rfl⟩) R270803
theorem R1392983 : Reach 1392983 := rs (se 1 (by rfl) ⟨1044737, by rfl⟩) R2089475
theorem R475901 : Reach 475901 := rs (se 3 (by rfl) ⟨89231, by rfl⟩) R178463
theorem R312187 : Reach 312187 := rs (se 1 (by rfl) ⟨234140, by rfl⟩) R468281
theorem R967625 : Reach 967625 := rs (se 2 (by rfl) ⟨362859, by rfl⟩) R725719
theorem R246847 : Reach 246847 := rs (se 1 (by rfl) ⟨185135, by rfl⟩) R370271
theorem R214123 : Reach 214123 := rs (se 1 (by rfl) ⟨160592, by rfl⟩) R321185
theorem R836837 : Reach 836837 := rs (se 4 (by rfl) ⟨78453, by rfl⟩) R156907
theorem R83195 : Reach 83195 := rs (se 1 (by rfl) ⟨62396, by rfl⟩) R124793
theorem R312605 : Reach 312605 := rs (se 3 (by rfl) ⟨58613, by rfl⟩) R117227
theorem R968111 : Reach 968111 := rs (se 1 (by rfl) ⟨726083, by rfl⟩) R1452167
theorem R83695 : Reach 83695 := rs (se 1 (by rfl) ⟨62771, by rfl⟩) R125543
theorem R83879 : Reach 83879 := rs (se 1 (by rfl) ⟨62909, by rfl⟩) R125819
theorem R84059 : Reach 84059 := rs (se 1 (by rfl) ⟨63044, by rfl⟩) R126089
theorem R84095 : Reach 84095 := rs (se 1 (by rfl) ⟨63071, by rfl⟩) R126143
theorem R346295 : Reach 346295 := rs (se 1 (by rfl) ⟨259721, by rfl⟩) R519443
theorem R182683 : Reach 182683 := rs (se 1 (by rfl) ⟨137012, by rfl⟩) R274025
theorem R84455 : Reach 84455 := rs (se 1 (by rfl) ⟨63341, by rfl⟩) R126683
theorem R281231 : Reach 281231 := rs (se 1 (by rfl) ⟨210923, by rfl⟩) R421847
theorem R84635 : Reach 84635 := rs (se 1 (by rfl) ⟨63476, by rfl⟩) R126953
theorem R576161 : Reach 576161 := rs (se 2 (by rfl) ⟨216060, by rfl⟩) R432121
theorem R84647 : Reach 84647 := rs (se 1 (by rfl) ⟨63485, by rfl⟩) R126971
theorem R84671 : Reach 84671 := rs (se 1 (by rfl) ⟨63503, by rfl⟩) R127007
theorem R84687 : Reach 84687 := rs (se 1 (by rfl) ⟨63515, by rfl⟩) R127031
theorem R84767 : Reach 84767 := rs (se 1 (by rfl) ⟨63575, by rfl⟩) R127151
theorem R84903 : Reach 84903 := rs (se 1 (by rfl) ⟨63677, by rfl⟩) R127355
theorem R85083 : Reach 85083 := rs (se 1 (by rfl) ⟨63812, by rfl⟩) R127625
theorem R183401 : Reach 183401 := rs (se 2 (by rfl) ⟨68775, by rfl⟩) R137551
theorem R183521 : Reach 183521 := rs (se 2 (by rfl) ⟨68820, by rfl⟩) R137641
theorem R85223 : Reach 85223 := rs (se 1 (by rfl) ⟨63917, by rfl⟩) R127835
theorem R314617 : Reach 314617 := rs (se 2 (by rfl) ⟨117981, by rfl⟩) R235963
theorem R85243 : Reach 85243 := rs (se 1 (by rfl) ⟨63932, by rfl⟩) R127865
theorem R282203 : Reach 282203 := rs (se 1 (by rfl) ⟨211652, by rfl⟩) R423305
theorem R85663 : Reach 85663 := rs (se 1 (by rfl) ⟨64247, by rfl⟩) R128495
theorem R85743 : Reach 85743 := rs (se 1 (by rfl) ⟨64307, by rfl⟩) R128615
theorem R741257 : Reach 741257 := rs (se 2 (by rfl) ⟨277971, by rfl⟩) R555943
theorem R86047 : Reach 86047 := rs (se 1 (by rfl) ⟨64535, by rfl⟩) R129071
theorem R86127 : Reach 86127 := rs (se 1 (by rfl) ⟨64595, by rfl⟩) R129191
theorem R86223 : Reach 86223 := rs (se 1 (by rfl) ⟨64667, by rfl⟩) R129335
theorem R86343 : Reach 86343 := rs (se 1 (by rfl) ⟨64757, by rfl⟩) R129515
theorem R86575 : Reach 86575 := rs (se 1 (by rfl) ⟨64931, by rfl⟩) R129863
theorem R185447 : Reach 185447 := rs (se 1 (by rfl) ⟨139085, by rfl⟩) R278171
theorem R939113 : Reach 939113 := rs (se 2 (by rfl) ⟨352167, by rfl⟩) R704335
theorem R546383 : Reach 546383 := rs (se 1 (by rfl) ⟨409787, by rfl⟩) R819575
theorem R710639 : Reach 710639 := rs (se 1 (by rfl) ⟨532979, by rfl⟩) R1065959
theorem R940403 : Reach 940403 := rs (se 1 (by rfl) ⟨705302, by rfl⟩) R1410605
theorem R416573 : Reach 416573 := rs (se 3 (by rfl) ⟨78107, by rfl⟩) R156215
theorem R580547 : Reach 580547 := rs (se 1 (by rfl) ⟨435410, by rfl⟩) R870821
theorem R973943 : Reach 973943 := rs (se 1 (by rfl) ⟨730457, by rfl⟩) R1460915
theorem R646379 : Reach 646379 := rs (se 1 (by rfl) ⟨484784, by rfl⟩) R969569
theorem R318977 : Reach 318977 := rs (se 2 (by rfl) ⟨119616, by rfl⟩) R239233
theorem R646865 : Reach 646865 := rs (se 2 (by rfl) ⟨242574, by rfl⟩) R485149
theorem R319241 : Reach 319241 := rs (se 2 (by rfl) ⟨119715, by rfl⟩) R239431
theorem R1401785 : Reach 1401785 := rs (se 2 (by rfl) ⟨525669, by rfl⟩) R1051339
theorem R189935 : Reach 189935 := rs (se 1 (by rfl) ⟨142451, by rfl⟩) R284903
theorem R452299 : Reach 452299 := rs (se 1 (by rfl) ⟨339224, by rfl⟩) R678449
theorem R321641 : Reach 321641 := rs (se 2 (by rfl) ⟨120615, by rfl⟩) R241231
theorem R125147 : Reach 125147 := rs (se 1 (by rfl) ⟨93860, by rfl⟩) R187721
theorem R125159 : Reach 125159 := rs (se 1 (by rfl) ⟨93869, by rfl⟩) R187739
theorem R158375 : Reach 158375 := rs (se 1 (by rfl) ⟨118781, by rfl⟩) R237563
theorem R125807 : Reach 125807 := rs (se 1 (by rfl) ⟨94355, by rfl⟩) R188711
theorem R191483 : Reach 191483 := rs (se 1 (by rfl) ⟨143612, by rfl⟩) R287225
theorem R126047 : Reach 126047 := rs (se 1 (by rfl) ⟨94535, by rfl⟩) R189071
theorem R126059 : Reach 126059 := rs (se 1 (by rfl) ⟨94544, by rfl⟩) R189089
theorem R126107 : Reach 126107 := rs (se 1 (by rfl) ⟨94580, by rfl⟩) R189161
theorem R126299 : Reach 126299 := rs (se 1 (by rfl) ⟨94724, by rfl⟩) R189449
theorem R93631 : Reach 93631 := rs (se 1 (by rfl) ⟨70223, by rfl⟩) R140447
theorem R126491 : Reach 126491 := rs (se 1 (by rfl) ⟨94868, by rfl⟩) R189737
theorem R421483 : Reach 421483 := rs (se 1 (by rfl) ⟨316112, by rfl⟩) R632225
theorem R126671 : Reach 126671 := rs (se 1 (by rfl) ⟨95003, by rfl⟩) R190007
theorem R94063 : Reach 94063 := rs (se 1 (by rfl) ⟨70547, by rfl⟩) R141095
theorem R126911 : Reach 126911 := rs (se 1 (by rfl) ⟨95183, by rfl⟩) R190367
theorem R126959 : Reach 126959 := rs (se 1 (by rfl) ⟨95219, by rfl⟩) R190439
theorem R323615 : Reach 323615 := rs (se 1 (by rfl) ⟨242711, by rfl⟩) R485423
theorem R127079 : Reach 127079 := rs (se 1 (by rfl) ⟨95309, by rfl⟩) R190619
theorem R2093165 : Reach 2093165 := rs (se 3 (by rfl) ⟨392468, by rfl⟩) R784937
theorem R290951 : Reach 290951 := rs (se 1 (by rfl) ⟨218213, by rfl⟩) R436427
theorem R553175 : Reach 553175 := rs (se 1 (by rfl) ⟨414881, by rfl⟩) R829763
theorem R127199 : Reach 127199 := rs (se 1 (by rfl) ⟨95399, by rfl⟩) R190799
theorem R192761 : Reach 192761 := rs (se 2 (by rfl) ⟨72285, by rfl⟩) R144571
theorem R127259 : Reach 127259 := rs (se 1 (by rfl) ⟨95444, by rfl⟩) R190889
theorem R291113 : Reach 291113 := rs (se 2 (by rfl) ⟨109167, by rfl⟩) R218335
theorem R192851 : Reach 192851 := rs (se 1 (by rfl) ⟨144638, by rfl⟩) R289277
theorem R422495 : Reach 422495 := rs (se 1 (by rfl) ⟨316871, by rfl⟩) R633743
theorem R128297 : Reach 128297 := rs (se 2 (by rfl) ⟨48111, by rfl⟩) R96223
theorem R1734061 : Reach 1734061 := rs (se 3 (by rfl) ⟨325136, by rfl⟩) R650273
theorem R128575 : Reach 128575 := rs (se 1 (by rfl) ⟨96431, by rfl⟩) R192863
theorem R358121 : Reach 358121 := rs (se 2 (by rfl) ⟨134295, by rfl⟩) R268591
theorem R522215 : Reach 522215 := rs (se 1 (by rfl) ⟨391661, by rfl⟩) R783323
theorem R195065 : Reach 195065 := rs (se 2 (by rfl) ⟨73149, by rfl⟩) R146299
theorem R96871 : Reach 96871 := rs (se 1 (by rfl) ⟨72653, by rfl⟩) R145307
theorem R293503 : Reach 293503 := rs (se 1 (by rfl) ⟨220127, by rfl⟩) R440255
theorem R129743 : Reach 129743 := rs (se 1 (by rfl) ⟨97307, by rfl⟩) R194615
theorem R129833 : Reach 129833 := rs (se 2 (by rfl) ⟨48687, by rfl⟩) R97375
theorem R129983 : Reach 129983 := rs (se 1 (by rfl) ⟨97487, by rfl⟩) R194975
theorem R162985 : Reach 162985 := rs (se 2 (by rfl) ⟨61119, by rfl⟩) R122239
theorem R130367 : Reach 130367 := rs (se 1 (by rfl) ⟨97775, by rfl⟩) R195551
theorem R982529 : Reach 982529 := rs (se 2 (by rfl) ⟨368448, by rfl⟩) R736897
theorem R360071 : Reach 360071 := rs (se 1 (by rfl) ⟨270053, by rfl⟩) R540107
theorem R655127 : Reach 655127 := rs (se 1 (by rfl) ⟨491345, by rfl⟩) R982691
theorem R163615 : Reach 163615 := rs (se 1 (by rfl) ⟨122711, by rfl⟩) R245423
theorem R163721 : Reach 163721 := rs (se 2 (by rfl) ⟨61395, by rfl⟩) R122791
theorem R622525 : Reach 622525 := rs (se 3 (by rfl) ⟨116723, by rfl⟩) R233447
theorem R327671 : Reach 327671 := rs (se 1 (by rfl) ⟨245753, by rfl⟩) R491507
theorem R328475 : Reach 328475 := rs (se 1 (by rfl) ⟨246356, by rfl⟩) R492713
theorem R557891 : Reach 557891 := rs (se 1 (by rfl) ⟨418418, by rfl⟩) R836837
theorem R1541105 : Reach 1541105 := rs (se 2 (by rfl) ⟨577914, by rfl⟩) R1155829
theorem R329129 : Reach 329129 := rs (se 2 (by rfl) ⟨123423, by rfl⟩) R246847
theorem R230863 : Reach 230863 := rs (se 1 (by rfl) ⟨173147, by rfl⟩) R346295
theorem R296893 : Reach 296893 := rs (se 3 (by rfl) ⟨55667, by rfl⟩) R111335
theorem R494171 : Reach 494171 := rs (se 1 (by rfl) ⟨370628, by rfl⟩) R741257
theorem R494525 : Reach 494525 := rs (se 3 (by rfl) ⟨92723, by rfl⟩) R185447
theorem R626075 : Reach 626075 := rs (se 1 (by rfl) ⟨469556, by rfl⟩) R939113
theorem R626935 : Reach 626935 := rs (se 1 (by rfl) ⟨470201, by rfl⟩) R940403
theorem R365161 : Reach 365161 := rs (se 2 (by rfl) ⟨136935, by rfl⟩) R273871
theorem R954989 : Reach 954989 := rs (se 3 (by rfl) ⟨179060, by rfl⟩) R358121
theorem R561977 : Reach 561977 := rs (se 2 (by rfl) ⟨210741, by rfl⟩) R421483
theorem R430919 : Reach 430919 := rs (se 1 (by rfl) ⟨323189, by rfl⟩) R646379
theorem R431243 : Reach 431243 := rs (se 1 (by rfl) ⟨323432, by rfl⟩) R646865
theorem R1677361 : Reach 1677361 := rs (se 2 (by rfl) ⟨629010, by rfl⟩) R1258021
theorem R923795 : Reach 923795 := rs (se 1 (by rfl) ⟨692846, by rfl⟩) R1385693
theorem R171433 : Reach 171433 := rs (se 2 (by rfl) ⟨64287, by rfl⟩) R128575
theorem R368783 : Reach 368783 := rs (se 1 (by rfl) ⟨276587, by rfl⟩) R553175
theorem R436589 : Reach 436589 := rs (se 3 (by rfl) ⟨81860, by rfl⟩) R163721
theorem R240047 : Reach 240047 := rs (se 1 (by rfl) ⟨180035, by rfl⟩) R360071
theorem R436751 : Reach 436751 := rs (se 1 (by rfl) ⟨327563, by rfl⟩) R655127
theorem R830033 : Reach 830033 := rs (se 2 (by rfl) ⟨311262, by rfl⟩) R622525
theorem R600871 : Reach 600871 := rs (se 1 (by rfl) ⟨450653, by rfl⟩) R901307
theorem R928655 : Reach 928655 := rs (se 1 (by rfl) ⟨696491, by rfl⟩) R1392983
theorem R240713 : Reach 240713 := rs (se 2 (by rfl) ⟨90267, by rfl⟩) R180535
theorem R830969 : Reach 830969 := rs (se 2 (by rfl) ⟨311613, by rfl⟩) R623227
theorem R208403 : Reach 208403 := rs (se 1 (by rfl) ⟨156302, by rfl⟩) R312605
theorem R6795251 : Reach 6795251 := rs (se 1 (by rfl) ⟨5096438, by rfl⟩) R10192877
theorem R1421549 : Reach 1421549 := rs (se 3 (by rfl) ⟨266540, by rfl⟩) R533081
theorem R603065 : Reach 603065 := rs (se 2 (by rfl) ⟨226149, by rfl⟩) R452299
theorem R111727 : Reach 111727 := rs (se 1 (by rfl) ⟨83795, by rfl⟩) R167591
theorem R177643 : Reach 177643 := rs (se 1 (by rfl) ⟨133232, by rfl⟩) R266465
theorem R243577 : Reach 243577 := rs (se 2 (by rfl) ⟨91341, by rfl⟩) R182683
theorem R473759 : Reach 473759 := rs (se 1 (by rfl) ⟨355319, by rfl⟩) R710639
theorem R637631 : Reach 637631 := rs (se 1 (by rfl) ⟨478223, by rfl⟩) R956447
theorem R1227575 : Reach 1227575 := rs (se 1 (by rfl) ⟨920681, by rfl⟩) R1841363
theorem R1457021 : Reach 1457021 := rs (se 3 (by rfl) ⟨273191, by rfl⟩) R546383
theorem R277715 : Reach 277715 := rs (se 1 (by rfl) ⟨208286, by rfl⟩) R416573
theorem R1097327 : Reach 1097327 := rs (se 1 (by rfl) ⟨822995, by rfl⟩) R1645991
theorem R212651 : Reach 212651 := rs (se 1 (by rfl) ⟨159488, by rfl⟩) R318977
theorem R212827 : Reach 212827 := rs (se 1 (by rfl) ⟨159620, by rfl⟩) R319241
theorem R246071 : Reach 246071 := rs (se 1 (by rfl) ⟨184553, by rfl⟩) R369107
theorem R934523 : Reach 934523 := rs (se 1 (by rfl) ⟨700892, by rfl⟩) R1401785
theorem R9290375 : Reach 9290375 := rs (se 1 (by rfl) ⟨6967781, by rfl⟩) R13935563
theorem R181129 : Reach 181129 := rs (se 2 (by rfl) ⟨67923, by rfl⟩) R135847
theorem R312545 : Reach 312545 := rs (se 2 (by rfl) ⟨117204, by rfl⟩) R234409
theorem R214427 : Reach 214427 := rs (se 1 (by rfl) ⟨160820, by rfl⟩) R321641
theorem R83431 : Reach 83431 := rs (se 1 (by rfl) ⟨62573, by rfl⟩) R125147
theorem R83439 : Reach 83439 := rs (se 1 (by rfl) ⟨62579, by rfl⟩) R125159
theorem R1361771 : Reach 1361771 := rs (se 1 (by rfl) ⟨1021328, by rfl⟩) R2042657
theorem R2312081 : Reach 2312081 := rs (se 2 (by rfl) ⟨867030, by rfl⟩) R1734061
theorem R83871 : Reach 83871 := rs (se 1 (by rfl) ⟨62903, by rfl⟩) R125807
theorem R313307 : Reach 313307 := rs (se 1 (by rfl) ⟨234980, by rfl⟩) R469961
theorem R84031 : Reach 84031 := rs (se 1 (by rfl) ⟨63023, by rfl⟩) R126047
theorem R84039 : Reach 84039 := rs (se 1 (by rfl) ⟨63029, by rfl⟩) R126059
theorem R84071 : Reach 84071 := rs (se 1 (by rfl) ⟨63053, by rfl⟩) R126107
theorem R84199 : Reach 84199 := rs (se 1 (by rfl) ⟨63149, by rfl⟩) R126299
theorem R84327 : Reach 84327 := rs (se 1 (by rfl) ⟨63245, by rfl⟩) R126491
theorem R84447 : Reach 84447 := rs (se 1 (by rfl) ⟨63335, by rfl⟩) R126671
theorem R84607 : Reach 84607 := rs (se 1 (by rfl) ⟨63455, by rfl⟩) R126911
theorem R84639 : Reach 84639 := rs (se 1 (by rfl) ⟨63479, by rfl⟩) R126959
theorem R215743 : Reach 215743 := rs (se 1 (by rfl) ⟨161807, by rfl⟩) R323615
theorem R84719 : Reach 84719 := rs (se 1 (by rfl) ⟨63539, by rfl⟩) R127079
theorem R1395443 : Reach 1395443 := rs (se 1 (by rfl) ⟨1046582, by rfl⟩) R2093165
theorem R84799 : Reach 84799 := rs (se 1 (by rfl) ⟨63599, by rfl⟩) R127199
theorem R84839 : Reach 84839 := rs (se 1 (by rfl) ⟨63629, by rfl⟩) R127259
theorem R281501 : Reach 281501 := rs (se 3 (by rfl) ⟨52781, by rfl⟩) R105563
theorem R281663 : Reach 281663 := rs (se 1 (by rfl) ⟨211247, by rfl⟩) R422495
theorem R183503 : Reach 183503 := rs (se 1 (by rfl) ⟨137627, by rfl⟩) R275255
theorem R85531 : Reach 85531 := rs (se 1 (by rfl) ⟨64148, by rfl⟩) R128297
theorem R544745 : Reach 544745 := rs (se 2 (by rfl) ⟨204279, by rfl⟩) R408559
theorem R348143 : Reach 348143 := rs (se 1 (by rfl) ⟨261107, by rfl⟩) R522215
theorem R217313 : Reach 217313 := rs (se 2 (by rfl) ⟨81492, by rfl⟩) R162985
theorem R282905 : Reach 282905 := rs (se 2 (by rfl) ⟨106089, by rfl⟩) R212179
theorem R86495 : Reach 86495 := rs (se 1 (by rfl) ⟨64871, by rfl⟩) R129743
theorem R86555 : Reach 86555 := rs (se 1 (by rfl) ⟨64916, by rfl⟩) R129833
theorem R1167979 : Reach 1167979 := rs (se 1 (by rfl) ⟨875984, by rfl⟩) R1751969
theorem R86655 : Reach 86655 := rs (se 1 (by rfl) ⟨64991, by rfl⟩) R129983
theorem R86911 : Reach 86911 := rs (se 1 (by rfl) ⟨65183, by rfl⟩) R130367
theorem R218153 : Reach 218153 := rs (se 2 (by rfl) ⟨81807, by rfl⟩) R163615
theorem R120143 : Reach 120143 := rs (se 1 (by rfl) ⟨90107, by rfl⟩) R180215
theorem R218447 : Reach 218447 := rs (se 1 (by rfl) ⟨163835, by rfl⟩) R327671
theorem R546385 : Reach 546385 := rs (se 2 (by rfl) ⟨204894, by rfl⟩) R409789
theorem R317267 : Reach 317267 := rs (se 1 (by rfl) ⟨237950, by rfl⟩) R475901
theorem R645083 : Reach 645083 := rs (se 1 (by rfl) ⟨483812, by rfl⟩) R967625
theorem R645407 : Reach 645407 := rs (se 1 (by rfl) ⟨484055, by rfl⟩) R968111
theorem R416249 : Reach 416249 := rs (se 2 (by rfl) ⟨156093, by rfl⟩) R312187
theorem R285497 : Reach 285497 := rs (se 2 (by rfl) ⟨107061, by rfl⟩) R214123
theorem R187487 : Reach 187487 := rs (se 1 (by rfl) ⟨140615, by rfl⟩) R281231
theorem R384107 : Reach 384107 := rs (se 1 (by rfl) ⟨288080, by rfl⟩) R576161
theorem R220391 : Reach 220391 := rs (se 1 (by rfl) ⟨165293, by rfl⟩) R330587
theorem R122267 : Reach 122267 := rs (se 1 (by rfl) ⟨91700, by rfl⟩) R183401
theorem R122347 : Reach 122347 := rs (se 1 (by rfl) ⟨91760, by rfl⟩) R183521
theorem R188135 : Reach 188135 := rs (se 1 (by rfl) ⟨141101, by rfl⟩) R282203
theorem R188297 : Reach 188297 := rs (se 2 (by rfl) ⟨70611, by rfl⟩) R141223
theorem R1236905 : Reach 1236905 := rs (se 2 (by rfl) ⟨463839, by rfl⟩) R927679
theorem R286955 : Reach 286955 := rs (se 1 (by rfl) ⟨215216, by rfl⟩) R430433
theorem R287927 : Reach 287927 := rs (se 1 (by rfl) ⟨215945, by rfl⟩) R431891
theorem R419489 : Reach 419489 := rs (se 2 (by rfl) ⟨157308, by rfl⟩) R314617
theorem R124841 : Reach 124841 := rs (se 2 (by rfl) ⟨46815, by rfl⟩) R93631
theorem R2287561 : Reach 2287561 := rs (se 2 (by rfl) ⟨857835, by rfl⟩) R1715671
theorem R387031 : Reach 387031 := rs (se 1 (by rfl) ⟨290273, by rfl⟩) R580547
theorem R649295 : Reach 649295 := rs (se 1 (by rfl) ⟨486971, by rfl⟩) R973943
theorem R289223 : Reach 289223 := rs (se 1 (by rfl) ⟨216917, by rfl⟩) R433835
theorem R125417 : Reach 125417 := rs (se 2 (by rfl) ⟨47031, by rfl⟩) R94063
theorem R159059 : Reach 159059 := rs (se 1 (by rfl) ⟨119294, by rfl⟩) R238589
theorem R191969 : Reach 191969 := rs (se 2 (by rfl) ⟨71988, by rfl⟩) R143977
theorem R126623 : Reach 126623 := rs (se 1 (by rfl) ⟨94967, by rfl⟩) R189935
theorem R422333 : Reach 422333 := rs (se 3 (by rfl) ⟨79187, by rfl⟩) R158375
theorem R94747 : Reach 94747 := rs (se 1 (by rfl) ⟨71060, by rfl⟩) R142121
theorem R127655 : Reach 127655 := rs (se 1 (by rfl) ⟨95741, by rfl⟩) R191483
theorem R95359 : Reach 95359 := rs (se 1 (by rfl) ⟨71519, by rfl⟩) R143039
theorem R488591 : Reach 488591 := rs (se 1 (by rfl) ⟨366443, by rfl⟩) R732887
theorem R193967 : Reach 193967 := rs (se 1 (by rfl) ⟨145475, by rfl⟩) R290951
theorem R128507 : Reach 128507 := rs (se 1 (by rfl) ⟨96380, by rfl⟩) R192761
theorem R194075 : Reach 194075 := rs (se 1 (by rfl) ⟨145556, by rfl⟩) R291113
theorem R95791 : Reach 95791 := rs (se 1 (by rfl) ⟨71843, by rfl⟩) R143687
theorem R128567 : Reach 128567 := rs (se 1 (by rfl) ⟨96425, by rfl⟩) R192851
theorem R423791 : Reach 423791 := rs (se 1 (by rfl) ⟨317843, by rfl⟩) R635687
theorem R489523 : Reach 489523 := rs (se 1 (by rfl) ⟨367142, by rfl⟩) R734285
theorem R194633 : Reach 194633 := rs (se 2 (by rfl) ⟨72987, by rfl⟩) R145975
theorem R1701965 : Reach 1701965 := rs (se 3 (by rfl) ⟨319118, by rfl⟩) R638237
theorem R129161 : Reach 129161 := rs (se 2 (by rfl) ⟨48435, by rfl⟩) R96871
theorem R293003 : Reach 293003 := rs (se 1 (by rfl) ⟨219752, by rfl⟩) R439505
theorem R391337 : Reach 391337 := rs (se 2 (by rfl) ⟨146751, by rfl⟩) R293503
theorem R227663 : Reach 227663 := rs (se 1 (by rfl) ⟨170747, by rfl⟩) R341495
theorem R293759 : Reach 293759 := rs (se 1 (by rfl) ⟨220319, by rfl⟩) R440639
theorem R359387 : Reach 359387 := rs (se 1 (by rfl) ⟨269540, by rfl⟩) R539081
theorem R130043 : Reach 130043 := rs (se 1 (by rfl) ⟨97532, by rfl⟩) R195065
theorem R1113425 : Reach 1113425 := rs (se 2 (by rfl) ⟨417534, by rfl⟩) R835069
theorem R97663 : Reach 97663 := rs (se 1 (by rfl) ⟨73247, by rfl⟩) R146495
theorem R655019 : Reach 655019 := rs (se 1 (by rfl) ⟨491264, by rfl⟩) R982529
theorem R163775 : Reach 163775 := rs (se 1 (by rfl) ⟨122831, by rfl⟩) R245663
theorem R164047 : Reach 164047 := rs (se 1 (by rfl) ⟨123035, by rfl⟩) R246071
theorem R623015 : Reach 623015 := rs (se 1 (by rfl) ⟨467261, by rfl⟩) R934523
theorem R6193583 : Reach 6193583 := rs (se 1 (by rfl) ⟨4645187, by rfl⟩) R9290375
theorem R4097141 : Reach 4097141 := rs (se 5 (by rfl) ⟨192053, by rfl⟩) R384107
theorem R1541387 : Reach 1541387 := rs (se 1 (by rfl) ⟨1156040, by rfl⟩) R2312081
theorem R329447 : Reach 329447 := rs (se 1 (by rfl) ⟨247085, by rfl⟩) R494171
theorem R329683 : Reach 329683 := rs (se 1 (by rfl) ⟨247262, by rfl⟩) R494525
theorem R395857 : Reach 395857 := rs (se 2 (by rfl) ⟨148446, by rfl⟩) R296893
theorem R3050081 : Reach 3050081 := rs (se 2 (by rfl) ⟨1143780, by rfl⟩) R2287561
theorem R363163 : Reach 363163 := rs (se 1 (by rfl) ⟨272372, by rfl⟩) R544745
theorem R430055 : Reach 430055 := rs (se 1 (by rfl) ⟨322541, by rfl⟩) R645083
theorem R430271 : Reach 430271 := rs (se 1 (by rfl) ⟨322703, by rfl⟩) R645407
theorem R824603 : Reach 824603 := rs (se 1 (by rfl) ⟨618452, by rfl⟩) R1236905
theorem R432863 : Reach 432863 := rs (se 1 (by rfl) ⟨324647, by rfl⟩) R649295
theorem R236857 : Reach 236857 := rs (se 2 (by rfl) ⟨88821, by rfl⟩) R177643
theorem R728513 : Reach 728513 := rs (se 2 (by rfl) ⟨273192, by rfl⟩) R546385
theorem R106039 : Reach 106039 := rs (se 1 (by rfl) ⟨79529, by rfl⟩) R159059
theorem R138935 : Reach 138935 := rs (se 1 (by rfl) ⟨104201, by rfl⟩) R208403
theorem R4530167 : Reach 4530167 := rs (se 1 (by rfl) ⟨3397625, by rfl⟩) R6795251
theorem R2236481 : Reach 2236481 := rs (se 2 (by rfl) ⟨838680, by rfl⟩) R1677361
theorem R402043 : Reach 402043 := rs (se 1 (by rfl) ⟨301532, by rfl⟩) R603065
theorem R239591 : Reach 239591 := rs (se 1 (by rfl) ⟨179693, by rfl⟩) R359387
theorem R731551 : Reach 731551 := rs (se 1 (by rfl) ⟨548663, by rfl⟩) R1097327
theorem R436679 : Reach 436679 := rs (se 1 (by rfl) ⟨327509, by rfl⟩) R655019
theorem R141767 : Reach 141767 := rs (se 1 (by rfl) ⟨106325, by rfl⟩) R212651
theorem R3713525 : Reach 3713525 := rs (se 5 (by rfl) ⟨174071, by rfl⟩) R348143
theorem R109183 : Reach 109183 := rs (se 1 (by rfl) ⟨81887, by rfl⟩) R163775
theorem R371927 : Reach 371927 := rs (se 1 (by rfl) ⟨278945, by rfl⟩) R557891
theorem R1027403 : Reach 1027403 := rs (se 1 (by rfl) ⟨770552, by rfl⟩) R1541105
theorem R208363 : Reach 208363 := rs (se 1 (by rfl) ⟨156272, by rfl⟩) R312545
theorem R142951 : Reach 142951 := rs (se 1 (by rfl) ⟨107213, by rfl⟩) R214427
theorem R241505 : Reach 241505 := rs (se 2 (by rfl) ⟨90564, by rfl⟩) R181129
theorem R208871 : Reach 208871 := rs (se 1 (by rfl) ⟨156653, by rfl⟩) R313307
theorem R930295 : Reach 930295 := rs (se 1 (by rfl) ⟨697721, by rfl⟩) R1395443
theorem R307817 : Reach 307817 := rs (se 2 (by rfl) ⟨115431, by rfl⟩) R230863
theorem R144875 : Reach 144875 := rs (se 1 (by rfl) ⟨108656, by rfl⟩) R217313
theorem R636659 : Reach 636659 := rs (se 1 (by rfl) ⟨477494, by rfl⟩) R954989
theorem R374651 : Reach 374651 := rs (se 1 (by rfl) ⟨280988, by rfl⟩) R561977
theorem R833453 : Reach 833453 := rs (se 3 (by rfl) ⟨156272, by rfl⟩) R312545
theorem R145435 : Reach 145435 := rs (se 1 (by rfl) ⟨109076, by rfl⟩) R218153
theorem R145631 : Reach 145631 := rs (se 1 (by rfl) ⟨109223, by rfl⟩) R218447
theorem R801161 : Reach 801161 := rs (se 2 (by rfl) ⟨300435, by rfl⟩) R600871
theorem R211511 : Reach 211511 := rs (se 1 (by rfl) ⟨158633, by rfl⟩) R317267
theorem R277499 : Reach 277499 := rs (se 1 (by rfl) ⟨208124, by rfl⟩) R416249
theorem R146927 : Reach 146927 := rs (se 1 (by rfl) ⟨110195, by rfl⟩) R220391
theorem R245855 : Reach 245855 := rs (se 1 (by rfl) ⟨184391, by rfl⟩) R368783
theorem R835913 : Reach 835913 := rs (se 2 (by rfl) ⟨313467, by rfl⟩) R626935
theorem R1557305 : Reach 1557305 := rs (se 2 (by rfl) ⟨583989, by rfl⟩) R1167979
theorem R279659 : Reach 279659 := rs (se 1 (by rfl) ⟨209744, by rfl⟩) R419489
theorem R83227 : Reach 83227 := rs (se 1 (by rfl) ⟨62420, by rfl⟩) R124841
theorem R148969 : Reach 148969 := rs (se 2 (by rfl) ⟨55863, by rfl⟩) R111727
theorem R83611 : Reach 83611 := rs (se 1 (by rfl) ⟨62708, by rfl⟩) R125417
theorem R84415 : Reach 84415 := rs (se 1 (by rfl) ⟨63311, by rfl⟩) R126623
theorem R281555 : Reach 281555 := rs (se 1 (by rfl) ⟨211166, by rfl⟩) R422333
theorem R85103 : Reach 85103 := rs (se 1 (by rfl) ⟨63827, by rfl⟩) R127655
theorem R740573 : Reach 740573 := rs (se 3 (by rfl) ⟨138857, by rfl⟩) R277715
theorem R85671 : Reach 85671 := rs (se 1 (by rfl) ⟨64253, by rfl⟩) R128507
theorem R85711 : Reach 85711 := rs (se 1 (by rfl) ⟨64283, by rfl⟩) R128567
theorem R282527 : Reach 282527 := rs (se 1 (by rfl) ⟨211895, by rfl⟩) R423791
theorem R1134643 : Reach 1134643 := rs (se 1 (by rfl) ⟨850982, by rfl⟩) R1701965
theorem R86107 : Reach 86107 := rs (se 1 (by rfl) ⟨64580, by rfl⟩) R129161
theorem R151775 : Reach 151775 := rs (se 1 (by rfl) ⟨113831, by rfl⟩) R227663
theorem R315839 : Reach 315839 := rs (se 1 (by rfl) ⟨236879, by rfl⟩) R473759
theorem R971347 : Reach 971347 := rs (se 1 (by rfl) ⟨728510, by rfl⟩) R1457021
theorem R86695 : Reach 86695 := rs (se 1 (by rfl) ⟨65021, by rfl⟩) R130043
theorem R742283 : Reach 742283 := rs (se 1 (by rfl) ⟨556712, by rfl⟩) R1113425
theorem R283769 : Reach 283769 := rs (se 2 (by rfl) ⟨106413, by rfl⟩) R212827
theorem R218983 : Reach 218983 := rs (se 1 (by rfl) ⟨164237, by rfl⟩) R328475
theorem R219419 : Reach 219419 := rs (se 1 (by rfl) ⟨164564, by rfl⟩) R329129
theorem R907847 : Reach 907847 := rs (se 1 (by rfl) ⟨680885, by rfl⟩) R1361771
theorem R187667 : Reach 187667 := rs (se 1 (by rfl) ⟨140750, by rfl⟩) R281501
theorem R187775 : Reach 187775 := rs (se 1 (by rfl) ⟨140831, by rfl⟩) R281663
theorem R417383 : Reach 417383 := rs (se 1 (by rfl) ⟨313037, by rfl⟩) R626075
theorem R516041 : Reach 516041 := rs (se 2 (by rfl) ⟨193515, by rfl⟩) R387031
theorem R188603 : Reach 188603 := rs (se 1 (by rfl) ⟨141452, by rfl⟩) R282905
theorem R287279 : Reach 287279 := rs (se 1 (by rfl) ⟨215459, by rfl⟩) R430919
theorem R287495 : Reach 287495 := rs (se 1 (by rfl) ⟨215621, by rfl⟩) R431243
theorem R320381 : Reach 320381 := rs (se 3 (by rfl) ⟨60071, by rfl⟩) R120143
theorem R287657 : Reach 287657 := rs (se 2 (by rfl) ⟨107871, by rfl⟩) R215743
theorem R615863 : Reach 615863 := rs (se 1 (by rfl) ⟨461897, by rfl⟩) R923795
theorem R190331 : Reach 190331 := rs (se 1 (by rfl) ⟨142748, by rfl⟩) R285497
theorem R124991 : Reach 124991 := rs (se 1 (by rfl) ⟨93743, by rfl⟩) R187487
theorem R125423 : Reach 125423 := rs (se 1 (by rfl) ⟨94067, by rfl⟩) R188135
theorem R125531 : Reach 125531 := rs (se 1 (by rfl) ⟨94148, by rfl⟩) R188297
theorem R191303 : Reach 191303 := rs (se 1 (by rfl) ⟨143477, by rfl⟩) R286955
theorem R126329 : Reach 126329 := rs (se 2 (by rfl) ⟨47373, by rfl⟩) R94747
theorem R191951 : Reach 191951 := rs (se 1 (by rfl) ⟨143963, by rfl⟩) R287927
theorem R486881 : Reach 486881 := rs (se 2 (by rfl) ⟨182580, by rfl⟩) R365161
theorem R127145 : Reach 127145 := rs (se 2 (by rfl) ⟨47679, by rfl⟩) R95359
theorem R291059 : Reach 291059 := rs (se 1 (by rfl) ⟨218294, by rfl⟩) R436589
theorem R160031 : Reach 160031 := rs (se 1 (by rfl) ⟨120023, by rfl⟩) R240047
theorem R192815 : Reach 192815 := rs (se 1 (by rfl) ⟨144611, by rfl⟩) R289223
theorem R291167 : Reach 291167 := rs (se 1 (by rfl) ⟨218375, by rfl⟩) R436751
theorem R553355 : Reach 553355 := rs (se 1 (by rfl) ⟨415016, by rfl⟩) R830033
theorem R619103 : Reach 619103 := rs (se 1 (by rfl) ⟨464327, by rfl⟩) R928655
theorem R160475 : Reach 160475 := rs (se 1 (by rfl) ⟨120356, by rfl⟩) R240713
theorem R127721 : Reach 127721 := rs (se 2 (by rfl) ⟨47895, by rfl⟩) R95791
theorem R127979 : Reach 127979 := rs (se 1 (by rfl) ⟨95984, by rfl⟩) R191969
theorem R553979 : Reach 553979 := rs (se 1 (by rfl) ⟨415484, by rfl⟩) R830969
theorem R324769 : Reach 324769 := rs (se 2 (by rfl) ⟨121788, by rfl⟩) R243577
theorem R652697 : Reach 652697 := rs (se 2 (by rfl) ⟨244761, by rfl⟩) R489523
theorem R947699 : Reach 947699 := rs (se 1 (by rfl) ⟨710774, by rfl⟩) R1421549
theorem R489341 : Reach 489341 := rs (se 3 (by rfl) ⟨91751, by rfl⟩) R183503
theorem R325727 : Reach 325727 := rs (se 1 (by rfl) ⟨244295, by rfl⟩) R488591
theorem R129311 : Reach 129311 := rs (se 1 (by rfl) ⟨96983, by rfl⟩) R193967
theorem R129383 : Reach 129383 := rs (se 1 (by rfl) ⟨97037, by rfl⟩) R194075
theorem R326045 : Reach 326045 := rs (se 3 (by rfl) ⟨61133, by rfl⟩) R122267
theorem R129755 : Reach 129755 := rs (se 1 (by rfl) ⟨97316, by rfl⟩) R194633
theorem R195335 : Reach 195335 := rs (se 1 (by rfl) ⟨146501, by rfl⟩) R293003
theorem R260891 : Reach 260891 := rs (se 1 (by rfl) ⟨195668, by rfl⟩) R391337
theorem R425087 : Reach 425087 := rs (se 1 (by rfl) ⟨318815, by rfl⟩) R637631
theorem R130217 : Reach 130217 := rs (se 2 (by rfl) ⟨48831, by rfl⟩) R97663
theorem R818383 : Reach 818383 := rs (se 1 (by rfl) ⟨613787, by rfl⟩) R1227575
theorem R228577 : Reach 228577 := rs (se 2 (by rfl) ⟨85716, by rfl⟩) R171433
theorem R195839 : Reach 195839 := rs (se 1 (by rfl) ⟨146879, by rfl⟩) R293759
theorem R163129 : Reach 163129 := rs (se 2 (by rfl) ⟨61173, by rfl⟩) R122347
theorem R557275 : Reach 557275 := rs (se 1 (by rfl) ⟨417956, by rfl⟩) R835913
theorem R655613 : Reach 655613 := rs (se 3 (by rfl) ⟨122927, by rfl⟩) R245855
theorem R4129055 : Reach 4129055 := rs (se 1 (by rfl) ⟨3096791, by rfl⟩) R6193583
theorem R2033387 : Reach 2033387 := rs (se 1 (by rfl) ⟨1525040, by rfl⟩) R3050081
theorem R427933 : Reach 427933 := rs (se 3 (by rfl) ⟨80237, by rfl⟩) R160475
theorem R198625 : Reach 198625 := rs (se 2 (by rfl) ⟨74484, by rfl⟩) R148969
theorem R493715 : Reach 493715 := rs (se 1 (by rfl) ⟨370286, by rfl⟩) R740573
theorem R101183 : Reach 101183 := rs (se 1 (by rfl) ⟨75887, by rfl⟩) R151775
theorem R494855 : Reach 494855 := rs (se 1 (by rfl) ⟨371141, by rfl⟩) R742283
theorem R527809 : Reach 527809 := rs (se 2 (by rfl) ⟨197928, by rfl⟩) R395857
theorem R1642301 : Reach 1642301 := rs (se 3 (by rfl) ⟨307931, by rfl⟩) R615863
theorem R3020111 : Reach 3020111 := rs (se 1 (by rfl) ⟨2265083, by rfl⟩) R4530167
theorem R1512857 : Reach 1512857 := rs (se 2 (by rfl) ⟨567321, by rfl⟩) R1134643
theorem R433025 : Reach 433025 := rs (se 2 (by rfl) ⟨162384, by rfl⟩) R324769
theorem R139247 : Reach 139247 := rs (se 1 (by rfl) ⟨104435, by rfl⟩) R208871
theorem R106687 : Reach 106687 := rs (se 1 (by rfl) ⟨80015, by rfl⟩) R160031
theorem R368903 : Reach 368903 := rs (se 1 (by rfl) ⟨276677, by rfl⟩) R553355
theorem R205211 : Reach 205211 := rs (se 1 (by rfl) ⟨153908, by rfl⟩) R307817
theorem R369319 : Reach 369319 := rs (se 1 (by rfl) ⟨276989, by rfl⟩) R553979
theorem R435131 : Reach 435131 := rs (se 1 (by rfl) ⟨326348, by rfl⟩) R652697
theorem R631799 : Reach 631799 := rs (se 1 (by rfl) ⟨473849, by rfl⟩) R947699
theorem R534107 : Reach 534107 := rs (se 1 (by rfl) ⟨400580, by rfl⟩) R801161
theorem R1091177 : Reach 1091177 := rs (se 2 (by rfl) ⟨409191, by rfl⟩) R818383
theorem R304769 : Reach 304769 := rs (se 2 (by rfl) ⟨114288, by rfl⟩) R228577
theorem R141007 : Reach 141007 := rs (se 1 (by rfl) ⟨105755, by rfl⟩) R211511
theorem R370493 : Reach 370493 := rs (se 3 (by rfl) ⟨69467, by rfl⟩) R138935
theorem R173927 : Reach 173927 := rs (se 1 (by rfl) ⟨130445, by rfl⟩) R260891
theorem R141385 : Reach 141385 := rs (se 2 (by rfl) ⟨53019, by rfl⟩) R106039
theorem R2731427 : Reach 2731427 := rs (se 1 (by rfl) ⟨2048570, by rfl⟩) R4097141
theorem R536057 : Reach 536057 := rs (se 2 (by rfl) ⟨201021, by rfl⟩) R402043
theorem R1650941 : Reach 1650941 := rs (se 3 (by rfl) ⟨309551, by rfl⟩) R619103
theorem R439577 : Reach 439577 := rs (se 2 (by rfl) ⟨164841, by rfl⟩) R329683
theorem R4961573 : Reach 4961573 := rs (se 4 (by rfl) ⟨465147, by rfl⟩) R930295
theorem R8795765 : Reach 8795765 := rs (se 5 (by rfl) ⟨412301, by rfl⟩) R824603
theorem R210559 : Reach 210559 := rs (se 1 (by rfl) ⟨157919, by rfl⟩) R315839
theorem R4110365 : Reach 4110365 := rs (se 3 (by rfl) ⟨770693, by rfl⟩) R1541387
theorem R145577 : Reach 145577 := rs (se 2 (by rfl) ⟨54591, by rfl⟩) R109183
theorem R146279 : Reach 146279 := rs (se 1 (by rfl) ⟨109709, by rfl⟩) R219419
theorem R605231 : Reach 605231 := rs (se 1 (by rfl) ⟨453923, by rfl⟩) R907847
theorem R278255 : Reach 278255 := rs (se 1 (by rfl) ⟨208691, by rfl⟩) R417383
theorem R344027 : Reach 344027 := rs (se 1 (by rfl) ⟨258020, by rfl⟩) R516041
theorem R1490987 : Reach 1490987 := rs (se 1 (by rfl) ⟨1118240, by rfl⟩) R2236481
theorem R213587 : Reach 213587 := rs (se 1 (by rfl) ⟨160190, by rfl⟩) R320381
theorem R1295129 : Reach 1295129 := rs (se 2 (by rfl) ⟨485673, by rfl⟩) R971347
theorem R83327 : Reach 83327 := rs (se 1 (by rfl) ⟨62495, by rfl⟩) R124991
theorem R83615 : Reach 83615 := rs (se 1 (by rfl) ⟨62711, by rfl⟩) R125423
theorem R2475683 : Reach 2475683 := rs (se 1 (by rfl) ⟨1856762, by rfl⟩) R3713525
theorem R83687 : Reach 83687 := rs (se 1 (by rfl) ⟨62765, by rfl⟩) R125531
theorem R247951 : Reach 247951 := rs (se 1 (by rfl) ⟨185963, by rfl⟩) R371927
theorem R84219 : Reach 84219 := rs (se 1 (by rfl) ⟨63164, by rfl⟩) R126329
theorem R84763 : Reach 84763 := rs (se 1 (by rfl) ⟨63572, by rfl⟩) R127145
theorem R85147 : Reach 85147 := rs (se 1 (by rfl) ⟨63860, by rfl⟩) R127721
theorem R85319 : Reach 85319 := rs (se 1 (by rfl) ⟨63989, by rfl⟩) R127979
theorem R249767 : Reach 249767 := rs (se 1 (by rfl) ⟨187325, by rfl⟩) R374651
theorem R217151 : Reach 217151 := rs (se 1 (by rfl) ⟨162863, by rfl⟩) R325727
theorem R86207 : Reach 86207 := rs (se 1 (by rfl) ⟨64655, by rfl⟩) R129311
theorem R86255 : Reach 86255 := rs (se 1 (by rfl) ⟨64691, by rfl⟩) R129383
theorem R217363 : Reach 217363 := rs (se 1 (by rfl) ⟨163022, by rfl⟩) R326045
theorem R315809 : Reach 315809 := rs (se 2 (by rfl) ⟨118428, by rfl⟩) R236857
theorem R217505 : Reach 217505 := rs (se 2 (by rfl) ⟨81564, by rfl⟩) R163129
theorem R86503 : Reach 86503 := rs (se 1 (by rfl) ⟨64877, by rfl⟩) R129755
theorem R184999 : Reach 184999 := rs (se 1 (by rfl) ⟨138749, by rfl⟩) R277499
theorem R283391 : Reach 283391 := rs (se 1 (by rfl) ⟨212543, by rfl⟩) R425087
theorem R86811 : Reach 86811 := rs (se 1 (by rfl) ⟨65108, by rfl⟩) R130217
theorem R4445077 : Reach 4445077 := rs (se 6 (by rfl) ⟨104181, by rfl⟩) R208363
theorem R218729 : Reach 218729 := rs (se 2 (by rfl) ⟨82023, by rfl⟩) R164047
theorem R415343 : Reach 415343 := rs (se 1 (by rfl) ⟨311507, by rfl⟩) R623015
theorem R1038203 : Reach 1038203 := rs (se 1 (by rfl) ⟨778652, by rfl⟩) R1557305
theorem R219631 : Reach 219631 := rs (se 1 (by rfl) ⟨164723, by rfl⟩) R329447
theorem R187703 : Reach 187703 := rs (se 1 (by rfl) ⟨140777, by rfl⟩) R281555
theorem R188351 : Reach 188351 := rs (se 1 (by rfl) ⟨141263, by rfl⟩) R282527
theorem R286703 : Reach 286703 := rs (se 1 (by rfl) ⟨215027, by rfl⟩) R430055
theorem R286847 : Reach 286847 := rs (se 1 (by rfl) ⟨215135, by rfl⟩) R430271
theorem R745757 : Reach 745757 := rs (se 3 (by rfl) ⟨139829, by rfl⟩) R279659
theorem R975401 : Reach 975401 := rs (se 2 (by rfl) ⟨365775, by rfl⟩) R731551
theorem R189179 : Reach 189179 := rs (se 1 (by rfl) ⟨141884, by rfl⟩) R283769
theorem R484217 : Reach 484217 := rs (se 2 (by rfl) ⟨181581, by rfl⟩) R363163
theorem R288575 : Reach 288575 := rs (se 1 (by rfl) ⟨216431, by rfl⟩) R432863
theorem R190601 : Reach 190601 := rs (se 2 (by rfl) ⟨71475, by rfl⟩) R142951
theorem R125111 : Reach 125111 := rs (se 1 (by rfl) ⟨93833, by rfl⟩) R187667
theorem R125183 : Reach 125183 := rs (se 1 (by rfl) ⟨93887, by rfl⟩) R187775
theorem R485675 : Reach 485675 := rs (se 1 (by rfl) ⟨364256, by rfl⟩) R728513
theorem R125735 : Reach 125735 := rs (se 1 (by rfl) ⟨94301, by rfl⟩) R188603
theorem R191519 : Reach 191519 := rs (se 1 (by rfl) ⟨143639, by rfl⟩) R287279
theorem R191663 : Reach 191663 := rs (se 1 (by rfl) ⟨143747, by rfl⟩) R287495
theorem R191771 : Reach 191771 := rs (se 1 (by rfl) ⟨143828, by rfl⟩) R287657
theorem R126887 : Reach 126887 := rs (se 1 (by rfl) ⟨95165, by rfl⟩) R190331
theorem R159727 : Reach 159727 := rs (se 1 (by rfl) ⟨119795, by rfl⟩) R239591
theorem R94511 : Reach 94511 := rs (se 1 (by rfl) ⟨70883, by rfl⟩) R141767
theorem R291119 : Reach 291119 := rs (se 1 (by rfl) ⟨218339, by rfl⟩) R436679
theorem R127535 : Reach 127535 := rs (se 1 (by rfl) ⟨95651, by rfl⟩) R191303
theorem R684935 : Reach 684935 := rs (se 1 (by rfl) ⟨513701, by rfl⟩) R1027403
theorem R127967 : Reach 127967 := rs (se 1 (by rfl) ⟨95975, by rfl⟩) R191951
theorem R324587 : Reach 324587 := rs (se 1 (by rfl) ⟨243440, by rfl⟩) R486881
theorem R291977 : Reach 291977 := rs (se 2 (by rfl) ⟨109491, by rfl⟩) R218983
theorem R161003 : Reach 161003 := rs (se 1 (by rfl) ⟨120752, by rfl⟩) R241505
theorem R193913 : Reach 193913 := rs (se 2 (by rfl) ⟨72717, by rfl⟩) R145435
theorem R194039 : Reach 194039 := rs (se 1 (by rfl) ⟨145529, by rfl⟩) R291059
theorem R128543 : Reach 128543 := rs (se 1 (by rfl) ⟨96407, by rfl⟩) R192815
theorem R194111 : Reach 194111 := rs (se 1 (by rfl) ⟨145583, by rfl⟩) R291167
theorem R96583 : Reach 96583 := rs (se 1 (by rfl) ⟨72437, by rfl⟩) R144875
theorem R424439 : Reach 424439 := rs (se 1 (by rfl) ⟨318329, by rfl⟩) R636659
theorem R326227 : Reach 326227 := rs (se 1 (by rfl) ⟨244670, by rfl⟩) R489341
theorem R555635 : Reach 555635 := rs (se 1 (by rfl) ⟨416726, by rfl⟩) R833453
theorem R97087 : Reach 97087 := rs (se 1 (by rfl) ⟨72815, by rfl⟩) R145631
theorem R130223 : Reach 130223 := rs (se 1 (by rfl) ⟨97667, by rfl⟩) R195335
theorem R130559 : Reach 130559 := rs (se 1 (by rfl) ⟨97919, by rfl⟩) R195839
theorem R97951 : Reach 97951 := rs (se 1 (by rfl) ⟨73463, by rfl⟩) R146927
theorem R2752703 : Reach 2752703 := rs (se 1 (by rfl) ⟨2064527, by rfl⟩) R4129055
theorem R492425 : Reach 492425 := rs (se 2 (by rfl) ⟨184659, by rfl⟩) R369319
theorem R329143 : Reach 329143 := rs (se 1 (by rfl) ⟨246857, by rfl⟩) R493715
theorem R329903 : Reach 329903 := rs (se 1 (by rfl) ⟨247427, by rfl⟩) R494855
theorem R166511 : Reach 166511 := rs (se 1 (by rfl) ⟨124883, by rfl⟩) R249767
theorem R264833 : Reach 264833 := rs (se 2 (by rfl) ⟨99312, by rfl⟩) R198625
theorem R330601 : Reach 330601 := rs (se 2 (by rfl) ⟨123975, by rfl⟩) R247951
theorem R4034285 : Reach 4034285 := rs (se 3 (by rfl) ⟨756428, by rfl⟩) R1512857
theorem R692135 : Reach 692135 := rs (se 1 (by rfl) ⟨519101, by rfl⟩) R1038203
theorem R463805 : Reach 463805 := rs (se 3 (by rfl) ⟨86963, by rfl⟩) R173927
theorem R497171 : Reach 497171 := rs (se 1 (by rfl) ⟨372878, by rfl⟩) R745757
theorem R727451 : Reach 727451 := rs (se 1 (by rfl) ⟨545588, by rfl⟩) R1091177
theorem R269821 : Reach 269821 := rs (se 3 (by rfl) ⟨50591, by rfl⟩) R101183
theorem R434969 : Reach 434969 := rs (se 2 (by rfl) ⟨163113, by rfl⟩) R326227
theorem R107335 : Reach 107335 := rs (se 1 (by rfl) ⟨80501, by rfl⟩) R161003
theorem R370423 : Reach 370423 := rs (se 1 (by rfl) ⟨277817, by rfl⟩) R555635
theorem R403487 : Reach 403487 := rs (se 1 (by rfl) ⟨302615, by rfl⟩) R605231
theorem R3975965 : Reach 3975965 := rs (se 3 (by rfl) ⟨745493, by rfl⟩) R1490987
theorem R437075 : Reach 437075 := rs (se 1 (by rfl) ⟨327806, by rfl⟩) R655613
theorem R142249 : Reach 142249 := rs (se 2 (by rfl) ⟨53343, by rfl⟩) R106687
theorem R142391 : Reach 142391 := rs (se 1 (by rfl) ⟨106793, by rfl⟩) R213587
theorem R1650455 : Reach 1650455 := rs (se 1 (by rfl) ⟨1237841, by rfl⟩) R2475683
theorem R1355591 : Reach 1355591 := rs (se 1 (by rfl) ⟨1016693, by rfl⟩) R2033387
theorem R3453677 : Reach 3453677 := rs (se 3 (by rfl) ⟨647564, by rfl⟩) R1295129
theorem R570577 : Reach 570577 := rs (se 2 (by rfl) ⟨213966, by rfl⟩) R427933
theorem R1094867 : Reach 1094867 := rs (se 1 (by rfl) ⟨821150, by rfl⟩) R1642301
theorem R144767 : Reach 144767 := rs (se 1 (by rfl) ⟨108575, by rfl⟩) R217151
theorem R210539 : Reach 210539 := rs (se 1 (by rfl) ⟨157904, by rfl⟩) R315809
theorem R145003 : Reach 145003 := rs (se 1 (by rfl) ⟨108752, by rfl⟩) R217505
theorem R2013407 : Reach 2013407 := rs (se 1 (by rfl) ⟨1510055, by rfl⟩) R3020111
theorem R145819 : Reach 145819 := rs (se 1 (by rfl) ⟨109364, by rfl⟩) R218729
theorem R276895 : Reach 276895 := rs (se 1 (by rfl) ⟨207671, by rfl⟩) R415343
theorem R703745 : Reach 703745 := rs (se 2 (by rfl) ⟨263904, by rfl⟩) R527809
theorem R212969 : Reach 212969 := rs (se 2 (by rfl) ⟨79863, by rfl⟩) R159727
theorem R245935 : Reach 245935 := rs (se 1 (by rfl) ⟨184451, by rfl⟩) R368903
theorem R246665 : Reach 246665 := rs (se 2 (by rfl) ⟨92499, by rfl⟩) R184999
theorem R246995 : Reach 246995 := rs (se 1 (by rfl) ⟨185246, by rfl⟩) R370493
theorem R83407 : Reach 83407 := rs (se 1 (by rfl) ⟨62555, by rfl⟩) R125111
theorem R83455 : Reach 83455 := rs (se 1 (by rfl) ⟨62591, by rfl⟩) R125183
theorem R83823 : Reach 83823 := rs (se 1 (by rfl) ⟨62867, by rfl⟩) R125735
theorem R280745 : Reach 280745 := rs (se 2 (by rfl) ⟨105279, by rfl⟩) R210559
theorem R1820951 : Reach 1820951 := rs (se 1 (by rfl) ⟨1365713, by rfl⟩) R2731427
theorem R84591 : Reach 84591 := rs (se 1 (by rfl) ⟨63443, by rfl⟩) R126887
theorem R1100627 : Reach 1100627 := rs (se 1 (by rfl) ⟨825470, by rfl⟩) R1650941
theorem R85023 : Reach 85023 := rs (se 1 (by rfl) ⟨63767, by rfl⟩) R127535
theorem R85311 : Reach 85311 := rs (se 1 (by rfl) ⟨63983, by rfl⟩) R127967
theorem R216391 : Reach 216391 := rs (se 1 (by rfl) ⟨162293, by rfl⟩) R324587
theorem R85695 : Reach 85695 := rs (se 1 (by rfl) ⟨64271, by rfl⟩) R128543
theorem R2740243 : Reach 2740243 := rs (se 1 (by rfl) ⟨2055182, by rfl⟩) R4110365
theorem R282959 : Reach 282959 := rs (se 1 (by rfl) ⟨212219, by rfl⟩) R424439
theorem R86815 : Reach 86815 := rs (se 1 (by rfl) ⟨65111, by rfl⟩) R130223
theorem R87039 : Reach 87039 := rs (se 1 (by rfl) ⟨65279, by rfl⟩) R130559
theorem R185503 : Reach 185503 := rs (se 1 (by rfl) ⟨139127, by rfl⟩) R278255
theorem R743033 : Reach 743033 := rs (se 2 (by rfl) ⟨278637, by rfl⟩) R557275
theorem R252029 : Reach 252029 := rs (se 3 (by rfl) ⟨47255, by rfl⟩) R94511
theorem R776317 : Reach 776317 := rs (se 3 (by rfl) ⟨145559, by rfl⟩) R291119
theorem R547229 : Reach 547229 := rs (se 3 (by rfl) ⟨102605, by rfl⟩) R205211
theorem R188009 : Reach 188009 := rs (se 2 (by rfl) ⟨70503, by rfl⟩) R141007
theorem R188513 : Reach 188513 := rs (se 2 (by rfl) ⟨70692, by rfl⟩) R141385
theorem R188927 : Reach 188927 := rs (se 1 (by rfl) ⟨141695, by rfl⟩) R283391
theorem R812717 : Reach 812717 := rs (se 3 (by rfl) ⟨152384, by rfl⟩) R304769
theorem R288683 : Reach 288683 := rs (se 1 (by rfl) ⟨216512, by rfl⟩) R433025
theorem R125135 : Reach 125135 := rs (se 1 (by rfl) ⟨93851, by rfl⟩) R187703
theorem R125567 : Reach 125567 := rs (se 1 (by rfl) ⟨94175, by rfl⟩) R188351
theorem R92831 : Reach 92831 := rs (se 1 (by rfl) ⟨69623, by rfl⟩) R139247
theorem R191135 : Reach 191135 := rs (se 1 (by rfl) ⟨143351, by rfl⟩) R286703
theorem R191231 : Reach 191231 := rs (se 1 (by rfl) ⟨143423, by rfl⟩) R286847
theorem R289817 : Reach 289817 := rs (se 2 (by rfl) ⟨108681, by rfl⟩) R217363
theorem R650267 : Reach 650267 := rs (se 1 (by rfl) ⟨487700, by rfl⟩) R975401
theorem R126119 : Reach 126119 := rs (se 1 (by rfl) ⟨94589, by rfl⟩) R189179
theorem R322811 : Reach 322811 := rs (se 1 (by rfl) ⟨242108, by rfl⟩) R484217
theorem R290087 : Reach 290087 := rs (se 1 (by rfl) ⟨217565, by rfl⟩) R435131
theorem R421199 : Reach 421199 := rs (se 1 (by rfl) ⟨315899, by rfl⟩) R631799
theorem R356071 : Reach 356071 := rs (se 1 (by rfl) ⟨267053, by rfl⟩) R534107
theorem R5926769 : Reach 5926769 := rs (se 2 (by rfl) ⟨2222538, by rfl⟩) R4445077
theorem R192383 : Reach 192383 := rs (se 1 (by rfl) ⟨144287, by rfl⟩) R288575
theorem R127067 : Reach 127067 := rs (se 1 (by rfl) ⟨95300, by rfl⟩) R190601
theorem R323783 : Reach 323783 := rs (se 1 (by rfl) ⟨242837, by rfl⟩) R485675
theorem R127679 : Reach 127679 := rs (se 1 (by rfl) ⟨95759, by rfl⟩) R191519
theorem R127775 : Reach 127775 := rs (se 1 (by rfl) ⟨95831, by rfl⟩) R191663
theorem R127847 : Reach 127847 := rs (se 1 (by rfl) ⟨95885, by rfl⟩) R191771
theorem R357371 : Reach 357371 := rs (se 1 (by rfl) ⟨268028, by rfl⟩) R536057
theorem R128777 : Reach 128777 := rs (se 2 (by rfl) ⟨48291, by rfl⟩) R96583
theorem R456623 : Reach 456623 := rs (se 1 (by rfl) ⟨342467, by rfl⟩) R684935
theorem R292841 : Reach 292841 := rs (se 2 (by rfl) ⟨109815, by rfl⟩) R219631
theorem R194651 : Reach 194651 := rs (se 1 (by rfl) ⟨145988, by rfl⟩) R291977
theorem R293051 : Reach 293051 := rs (se 1 (by rfl) ⟨219788, by rfl⟩) R439577
theorem R3307715 : Reach 3307715 := rs (se 1 (by rfl) ⟨2480786, by rfl⟩) R4961573
theorem R129275 : Reach 129275 := rs (se 1 (by rfl) ⟨96956, by rfl⟩) R193913
theorem R129359 : Reach 129359 := rs (se 1 (by rfl) ⟨97019, by rfl⟩) R194039
theorem R129407 : Reach 129407 := rs (se 1 (by rfl) ⟨97055, by rfl⟩) R194111
theorem R5863843 : Reach 5863843 := rs (se 1 (by rfl) ⟨4397882, by rfl⟩) R8795765
theorem R129449 : Reach 129449 := rs (se 2 (by rfl) ⟨48543, by rfl⟩) R97087
theorem R97051 : Reach 97051 := rs (se 1 (by rfl) ⟨72788, by rfl⟩) R145577
theorem R97519 : Reach 97519 := rs (se 1 (by rfl) ⟨73139, by rfl⟩) R146279
theorem R130601 : Reach 130601 := rs (se 2 (by rfl) ⟨48975, by rfl⟩) R97951
theorem R229351 : Reach 229351 := rs (se 1 (by rfl) ⟨172013, by rfl⟩) R344027
theorem R1835135 : Reach 1835135 := rs (se 1 (by rfl) ⟨1376351, by rfl⟩) R2752703
theorem R328283 : Reach 328283 := rs (se 1 (by rfl) ⟨246212, by rfl⟩) R492425
theorem R164443 : Reach 164443 := rs (se 1 (by rfl) ⟨123332, by rfl⟩) R246665
theorem R164663 : Reach 164663 := rs (se 1 (by rfl) ⟨123497, by rfl⟩) R246995
theorem R1311653 : Reach 1311653 := rs (se 4 (by rfl) ⟨122967, by rfl⟩) R245935
theorem R1213967 : Reach 1213967 := rs (se 1 (by rfl) ⟨910475, by rfl⟩) R1820951
theorem R493897 : Reach 493897 := rs (se 2 (by rfl) ⟨185211, by rfl⟩) R370423
theorem R2689523 : Reach 2689523 := rs (se 1 (by rfl) ⟨2017142, by rfl⟩) R4034285
theorem R461423 : Reach 461423 := rs (se 1 (by rfl) ⟨346067, by rfl⟩) R692135
theorem R331447 : Reach 331447 := rs (se 1 (by rfl) ⟨248585, by rfl⟩) R497171
theorem R495355 : Reach 495355 := rs (se 1 (by rfl) ⟨371516, by rfl⟩) R743033
theorem R364819 : Reach 364819 := rs (se 1 (by rfl) ⟨273614, by rfl⟩) R547229
theorem R268991 : Reach 268991 := rs (se 1 (by rfl) ⟨201743, by rfl⟩) R403487
theorem R760769 : Reach 760769 := rs (se 2 (by rfl) ⟨285288, by rfl⟩) R570577
theorem R433511 : Reach 433511 := rs (se 1 (by rfl) ⟨325133, by rfl⟩) R650267
theorem R2302451 : Reach 2302451 := rs (se 1 (by rfl) ⟨1726838, by rfl⟩) R3453677
theorem R369193 : Reach 369193 := rs (se 2 (by rfl) ⟨138447, by rfl⟩) R276895
theorem R238247 : Reach 238247 := rs (se 1 (by rfl) ⟨178685, by rfl⟩) R357371
theorem R729911 : Reach 729911 := rs (se 1 (by rfl) ⟨547433, by rfl⟩) R1094867
theorem R140359 : Reach 140359 := rs (se 1 (by rfl) ⟨105269, by rfl⟩) R210539
theorem R304415 : Reach 304415 := rs (se 1 (by rfl) ⟨228311, by rfl⟩) R456623
theorem R2205143 : Reach 2205143 := rs (se 1 (by rfl) ⟨1653857, by rfl⟩) R3307715
theorem R469163 : Reach 469163 := rs (se 1 (by rfl) ⟨351872, by rfl⟩) R703745
theorem R305801 : Reach 305801 := rs (se 2 (by rfl) ⟨114675, by rfl⟩) R229351
theorem R141979 : Reach 141979 := rs (se 1 (by rfl) ⟨106484, by rfl⟩) R212969
theorem R143113 : Reach 143113 := rs (se 2 (by rfl) ⟨53667, by rfl⟩) R107335
theorem R111007 : Reach 111007 := rs (se 1 (by rfl) ⟨83255, by rfl⟩) R166511
theorem R176555 : Reach 176555 := rs (se 1 (by rfl) ⟨132416, by rfl⟩) R264833
theorem R733751 : Reach 733751 := rs (se 1 (by rfl) ⟨550313, by rfl⟩) R1100627
theorem R438857 : Reach 438857 := rs (se 2 (by rfl) ⟨164571, by rfl⟩) R329143
theorem R309203 : Reach 309203 := rs (se 1 (by rfl) ⟨231902, by rfl⟩) R463805
theorem R440801 : Reach 440801 := rs (se 2 (by rfl) ⟨165300, by rfl⟩) R330601
theorem R474761 : Reach 474761 := rs (se 2 (by rfl) ⟨178035, by rfl⟩) R356071
theorem R3653657 : Reach 3653657 := rs (se 2 (by rfl) ⟨1370121, by rfl⟩) R2740243
theorem R672077 : Reach 672077 := rs (se 3 (by rfl) ⟨126014, by rfl⟩) R252029
theorem R541811 : Reach 541811 := rs (se 1 (by rfl) ⟨406358, by rfl⟩) R812717
theorem R83423 : Reach 83423 := rs (se 1 (by rfl) ⟨62567, by rfl⟩) R125135
theorem R247337 : Reach 247337 := rs (se 2 (by rfl) ⟨92751, by rfl⟩) R185503
theorem R247549 : Reach 247549 := rs (se 3 (by rfl) ⟨46415, by rfl⟩) R92831
theorem R83711 : Reach 83711 := rs (se 1 (by rfl) ⟨62783, by rfl⟩) R125567
theorem R84079 : Reach 84079 := rs (se 1 (by rfl) ⟨63059, by rfl⟩) R126119
theorem R215207 : Reach 215207 := rs (se 1 (by rfl) ⟨161405, by rfl⟩) R322811
theorem R280799 : Reach 280799 := rs (se 1 (by rfl) ⟨210599, by rfl⟩) R421199
theorem R1100303 : Reach 1100303 := rs (se 1 (by rfl) ⟨825227, by rfl⟩) R1650455
theorem R903727 : Reach 903727 := rs (se 1 (by rfl) ⟨677795, by rfl⟩) R1355591
theorem R3951179 : Reach 3951179 := rs (se 1 (by rfl) ⟨2963384, by rfl⟩) R5926769
theorem R84711 : Reach 84711 := rs (se 1 (by rfl) ⟨63533, by rfl⟩) R127067
theorem R215855 : Reach 215855 := rs (se 1 (by rfl) ⟨161891, by rfl⟩) R323783
theorem R1035089 : Reach 1035089 := rs (se 2 (by rfl) ⟨388158, by rfl⟩) R776317
theorem R85119 : Reach 85119 := rs (se 1 (by rfl) ⟨63839, by rfl⟩) R127679
theorem R85183 : Reach 85183 := rs (se 1 (by rfl) ⟨63887, by rfl⟩) R127775
theorem R7818457 : Reach 7818457 := rs (se 2 (by rfl) ⟨2931921, by rfl⟩) R5863843
theorem R85231 : Reach 85231 := rs (se 1 (by rfl) ⟨63923, by rfl⟩) R127847
theorem R85851 : Reach 85851 := rs (se 1 (by rfl) ⟨64388, by rfl⟩) R128777
theorem R86183 : Reach 86183 := rs (se 1 (by rfl) ⟨64637, by rfl⟩) R129275
theorem R86239 : Reach 86239 := rs (se 1 (by rfl) ⟨64679, by rfl⟩) R129359
theorem R86271 : Reach 86271 := rs (se 1 (by rfl) ⟨64703, by rfl⟩) R129407
theorem R86299 : Reach 86299 := rs (se 1 (by rfl) ⟨64724, by rfl⟩) R129449
theorem R87067 : Reach 87067 := rs (se 1 (by rfl) ⟨65300, by rfl⟩) R130601
theorem R187163 : Reach 187163 := rs (se 1 (by rfl) ⟨140372, by rfl⟩) R280745
theorem R219935 : Reach 219935 := rs (se 1 (by rfl) ⟨164951, by rfl⟩) R329903
theorem R777701 : Reach 777701 := rs (se 4 (by rfl) ⟨72909, by rfl⟩) R145819
theorem R188639 : Reach 188639 := rs (se 1 (by rfl) ⟨141479, by rfl⟩) R282959
theorem R189665 : Reach 189665 := rs (se 2 (by rfl) ⟨71124, by rfl⟩) R142249
theorem R484967 : Reach 484967 := rs (se 1 (by rfl) ⟨363725, by rfl⟩) R727451
theorem R288521 : Reach 288521 := rs (se 2 (by rfl) ⟨108195, by rfl⟩) R216391
theorem R125339 : Reach 125339 := rs (se 1 (by rfl) ⟨94004, by rfl⟩) R188009
theorem R125675 : Reach 125675 := rs (se 1 (by rfl) ⟨94256, by rfl⟩) R188513
theorem R125951 : Reach 125951 := rs (se 1 (by rfl) ⟨94463, by rfl⟩) R188927
theorem R289979 : Reach 289979 := rs (se 1 (by rfl) ⟨217484, by rfl⟩) R434969
theorem R192455 : Reach 192455 := rs (se 1 (by rfl) ⟨144341, by rfl⟩) R288683
theorem R127423 : Reach 127423 := rs (se 1 (by rfl) ⟨95567, by rfl⟩) R191135
theorem R127487 : Reach 127487 := rs (se 1 (by rfl) ⟨95615, by rfl⟩) R191231
theorem R2650643 : Reach 2650643 := rs (se 1 (by rfl) ⟨1987982, by rfl⟩) R3975965
theorem R291383 : Reach 291383 := rs (se 1 (by rfl) ⟨218537, by rfl⟩) R437075
theorem R193211 : Reach 193211 := rs (se 1 (by rfl) ⟨144908, by rfl⟩) R289817
theorem R94927 : Reach 94927 := rs (se 1 (by rfl) ⟨71195, by rfl⟩) R142391
theorem R193337 : Reach 193337 := rs (se 2 (by rfl) ⟨72501, by rfl⟩) R145003
theorem R193391 : Reach 193391 := rs (se 1 (by rfl) ⟨145043, by rfl⟩) R290087
theorem R128255 : Reach 128255 := rs (se 1 (by rfl) ⟨96191, by rfl⟩) R192383
theorem R1439045 : Reach 1439045 := rs (se 4 (by rfl) ⟨134910, by rfl⟩) R269821
theorem R96511 : Reach 96511 := rs (se 1 (by rfl) ⟨72383, by rfl⟩) R144767
theorem R129401 : Reach 129401 := rs (se 2 (by rfl) ⟨48525, by rfl⟩) R97051
theorem R195227 : Reach 195227 := rs (se 1 (by rfl) ⟨146420, by rfl⟩) R292841
theorem R129767 : Reach 129767 := rs (se 1 (by rfl) ⟨97325, by rfl⟩) R194651
theorem R195367 : Reach 195367 := rs (se 1 (by rfl) ⟨146525, by rfl⟩) R293051
theorem R1342271 : Reach 1342271 := rs (se 1 (by rfl) ⟨1006703, by rfl⟩) R2013407
theorem R130025 : Reach 130025 := rs (se 2 (by rfl) ⟨48759, by rfl⟩) R97519
theorem R492257 : Reach 492257 := rs (se 2 (by rfl) ⟨184596, by rfl⟩) R369193
theorem R361207 : Reach 361207 := rs (se 1 (by rfl) ⟨270905, by rfl⟩) R541811
theorem R164891 : Reach 164891 := rs (se 1 (by rfl) ⟨123668, by rfl⟩) R247337
theorem R690059 : Reach 690059 := rs (se 1 (by rfl) ⟨517544, by rfl⟩) R1035089
theorem R330065 : Reach 330065 := rs (se 2 (by rfl) ⟨123774, by rfl⟩) R247549
theorem R658529 : Reach 658529 := rs (se 2 (by rfl) ⟨246948, by rfl⟩) R493897
theorem R10424609 : Reach 10424609 := rs (se 2 (by rfl) ⟨3909228, by rfl⟩) R7818457
theorem R660473 : Reach 660473 := rs (se 2 (by rfl) ⟨247677, by rfl⟩) R495355
theorem R1251101 : Reach 1251101 := rs (se 3 (by rfl) ⟨234581, by rfl⟩) R469163
theorem R202943 : Reach 202943 := rs (se 1 (by rfl) ⟨152207, by rfl⟩) R304415
theorem R203867 : Reach 203867 := rs (se 1 (by rfl) ⟨152900, by rfl⟩) R305801
theorem R3579389 : Reach 3579389 := rs (se 3 (by rfl) ⟨671135, by rfl⟩) R1342271
theorem R959363 : Reach 959363 := rs (se 1 (by rfl) ⟨719522, by rfl⟩) R1439045
theorem R2073869 : Reach 2073869 := rs (se 3 (by rfl) ⟨388850, by rfl⟩) R777701
theorem R206135 : Reach 206135 := rs (se 1 (by rfl) ⟨154601, by rfl⟩) R309203
theorem R2435771 : Reach 2435771 := rs (se 1 (by rfl) ⟨1826828, by rfl⟩) R3653657
theorem R1223423 : Reach 1223423 := rs (se 1 (by rfl) ⟨917567, by rfl⟩) R1835135
theorem R109775 : Reach 109775 := rs (se 1 (by rfl) ⟨82331, by rfl⟩) R164663
theorem R143471 : Reach 143471 := rs (se 1 (by rfl) ⟨107603, by rfl⟩) R215207
theorem R733535 : Reach 733535 := rs (se 1 (by rfl) ⟨550151, by rfl⟩) R1100303
theorem R2634119 : Reach 2634119 := rs (se 1 (by rfl) ⟨1975589, by rfl⟩) R3951179
theorem R143903 : Reach 143903 := rs (se 1 (by rfl) ⟨107927, by rfl⟩) R215855
theorem R179327 : Reach 179327 := rs (se 1 (by rfl) ⟨134495, by rfl⟩) R268991
theorem R146623 : Reach 146623 := rs (se 1 (by rfl) ⟨109967, by rfl⟩) R219935
theorem R507179 : Reach 507179 := rs (se 1 (by rfl) ⟨380384, by rfl⟩) R760769
theorem R441929 : Reach 441929 := rs (se 2 (by rfl) ⟨165723, by rfl⟩) R331447
theorem R148009 : Reach 148009 := rs (se 2 (by rfl) ⟨55503, by rfl⟩) R111007
theorem R83559 : Reach 83559 := rs (se 1 (by rfl) ⟨62669, by rfl⟩) R125339
theorem R1230461 : Reach 1230461 := rs (se 3 (by rfl) ⟨230711, by rfl⟩) R461423
theorem R83783 : Reach 83783 := rs (se 1 (by rfl) ⟨62837, by rfl⟩) R125675
theorem R83967 : Reach 83967 := rs (se 1 (by rfl) ⟨62975, by rfl⟩) R125951
theorem R117703 : Reach 117703 := rs (se 1 (by rfl) ⟨88277, by rfl⟩) R176555
theorem R84991 : Reach 84991 := rs (se 1 (by rfl) ⟨63743, by rfl⟩) R127487
theorem R85503 : Reach 85503 := rs (se 1 (by rfl) ⟨64127, by rfl⟩) R128255
theorem R86267 : Reach 86267 := rs (se 1 (by rfl) ⟨64700, by rfl⟩) R129401
theorem R86511 : Reach 86511 := rs (se 1 (by rfl) ⟨64883, by rfl⟩) R129767
theorem R86683 : Reach 86683 := rs (se 1 (by rfl) ⟨65012, by rfl⟩) R130025
theorem R316507 : Reach 316507 := rs (se 1 (by rfl) ⟨237380, by rfl⟩) R474761
theorem R448051 : Reach 448051 := rs (se 1 (by rfl) ⟨336038, by rfl⟩) R672077
theorem R218855 : Reach 218855 := rs (se 1 (by rfl) ⟨164141, by rfl⟩) R328283
theorem R874435 : Reach 874435 := rs (se 1 (by rfl) ⟨655826, by rfl⟩) R1311653
theorem R219257 : Reach 219257 := rs (se 2 (by rfl) ⟨82221, by rfl⟩) R164443
theorem R809311 : Reach 809311 := rs (se 1 (by rfl) ⟨606983, by rfl⟩) R1213967
theorem R187145 : Reach 187145 := rs (se 2 (by rfl) ⟨70179, by rfl⟩) R140359
theorem R187199 : Reach 187199 := rs (se 1 (by rfl) ⟨140399, by rfl⟩) R280799
theorem R1793015 : Reach 1793015 := rs (se 1 (by rfl) ⟨1344761, by rfl⟩) R2689523
theorem R679589 : Reach 679589 := rs (se 4 (by rfl) ⟨63711, by rfl⟩) R127423
theorem R1204969 : Reach 1204969 := rs (se 2 (by rfl) ⟨451863, by rfl⟩) R903727
theorem R189305 : Reach 189305 := rs (se 2 (by rfl) ⟨70989, by rfl⟩) R141979
theorem R124775 : Reach 124775 := rs (se 1 (by rfl) ⟨93581, by rfl⟩) R187163
theorem R289007 : Reach 289007 := rs (se 1 (by rfl) ⟨216755, by rfl⟩) R433511
theorem R190817 : Reach 190817 := rs (se 2 (by rfl) ⟨71556, by rfl⟩) R143113
theorem R125759 : Reach 125759 := rs (se 1 (by rfl) ⟨94319, by rfl⟩) R188639
theorem R1534967 : Reach 1534967 := rs (se 1 (by rfl) ⟨1151225, by rfl⟩) R2302451
theorem R486425 : Reach 486425 := rs (se 2 (by rfl) ⟨182409, by rfl⟩) R364819
theorem R158831 : Reach 158831 := rs (se 1 (by rfl) ⟨119123, by rfl⟩) R238247
theorem R486607 : Reach 486607 := rs (se 1 (by rfl) ⟨364955, by rfl⟩) R729911
theorem R126443 : Reach 126443 := rs (se 1 (by rfl) ⟨94832, by rfl⟩) R189665
theorem R126569 : Reach 126569 := rs (se 2 (by rfl) ⟨47463, by rfl⟩) R94927
theorem R1470095 : Reach 1470095 := rs (se 1 (by rfl) ⟨1102571, by rfl⟩) R2205143
theorem R323311 : Reach 323311 := rs (se 1 (by rfl) ⟨242483, by rfl⟩) R484967
theorem R192347 : Reach 192347 := rs (se 1 (by rfl) ⟨144260, by rfl⟩) R288521
theorem R193319 : Reach 193319 := rs (se 1 (by rfl) ⟨144989, by rfl⟩) R289979
theorem R128303 : Reach 128303 := rs (se 1 (by rfl) ⟨96227, by rfl⟩) R192455
theorem R128681 : Reach 128681 := rs (se 2 (by rfl) ⟨48255, by rfl⟩) R96511
theorem R1767095 : Reach 1767095 := rs (se 1 (by rfl) ⟨1325321, by rfl⟩) R2650643
theorem R489167 : Reach 489167 := rs (se 1 (by rfl) ⟨366875, by rfl⟩) R733751
theorem R194255 : Reach 194255 := rs (se 1 (by rfl) ⟨145691, by rfl⟩) R291383
theorem R292571 : Reach 292571 := rs (se 1 (by rfl) ⟨219428, by rfl⟩) R438857
theorem R128807 : Reach 128807 := rs (se 1 (by rfl) ⟨96605, by rfl⟩) R193211
theorem R128891 : Reach 128891 := rs (se 1 (by rfl) ⟨96668, by rfl⟩) R193337
theorem R128927 : Reach 128927 := rs (se 1 (by rfl) ⟨96695, by rfl⟩) R193391
theorem R260489 : Reach 260489 := rs (se 2 (by rfl) ⟨97683, by rfl⟩) R195367
theorem R293867 : Reach 293867 := rs (se 1 (by rfl) ⟨220400, by rfl⟩) R440801
theorem R130151 : Reach 130151 := rs (se 1 (by rfl) ⟨97613, by rfl⟩) R195227
theorem R328171 : Reach 328171 := rs (se 1 (by rfl) ⟨246128, by rfl⟩) R492257
theorem R197345 : Reach 197345 := rs (se 2 (by rfl) ⟨74004, by rfl⟩) R148009
theorem R1606625 : Reach 1606625 := rs (se 2 (by rfl) ⟨602484, by rfl⟩) R1204969
theorem R820307 : Reach 820307 := rs (se 1 (by rfl) ⟨615230, by rfl⟩) R1230461
theorem R6949739 : Reach 6949739 := rs (se 1 (by rfl) ⟨5212304, by rfl⟩) R10424609
theorem R135911 : Reach 135911 := rs (se 1 (by rfl) ⟨101933, by rfl⟩) R203867
theorem R431081 : Reach 431081 := rs (se 2 (by rfl) ⟨161655, by rfl⟩) R323311
theorem R1840157 : Reach 1840157 := rs (se 3 (by rfl) ⟨345029, by rfl⟩) R690059
theorem R1382579 : Reach 1382579 := rs (se 1 (by rfl) ⟨1036934, by rfl⟩) R2073869
theorem R137423 : Reach 137423 := rs (se 1 (by rfl) ⟨103067, by rfl⟩) R206135
theorem R1023311 : Reach 1023311 := rs (se 1 (by rfl) ⟨767483, by rfl⟩) R1534967
theorem R597401 : Reach 597401 := rs (se 2 (by rfl) ⟨224025, by rfl⟩) R448051
theorem R105887 : Reach 105887 := rs (se 1 (by rfl) ⟨79415, by rfl⟩) R158831
theorem R1352477 : Reach 1352477 := rs (se 3 (by rfl) ⟨253589, by rfl⟩) R507179
theorem R173659 : Reach 173659 := rs (se 1 (by rfl) ⟨130244, by rfl⟩) R260489
theorem R109927 : Reach 109927 := rs (se 1 (by rfl) ⟨82445, by rfl⟩) R164891
theorem R439019 : Reach 439019 := rs (se 1 (by rfl) ⟨329264, by rfl⟩) R658529
theorem R440315 : Reach 440315 := rs (se 1 (by rfl) ⟨330236, by rfl⟩) R660473
theorem R145903 : Reach 145903 := rs (se 1 (by rfl) ⟨109427, by rfl⟩) R218855
theorem R834067 : Reach 834067 := rs (se 1 (by rfl) ⟨625550, by rfl⟩) R1251101
theorem R146171 : Reach 146171 := rs (se 1 (by rfl) ⟨109628, by rfl⟩) R219257
theorem R1195343 : Reach 1195343 := rs (se 1 (by rfl) ⟨896507, by rfl⟩) R1793015
theorem R541181 : Reach 541181 := rs (se 3 (by rfl) ⟨101471, by rfl⟩) R202943
theorem R639575 : Reach 639575 := rs (se 1 (by rfl) ⟨479681, by rfl⟩) R959363
theorem R83183 : Reach 83183 := rs (se 1 (by rfl) ⟨62387, by rfl⟩) R124775
theorem R1623847 : Reach 1623847 := rs (se 1 (by rfl) ⟨1217885, by rfl⟩) R2435771
theorem R83839 : Reach 83839 := rs (se 1 (by rfl) ⟨62879, by rfl⟩) R125759
theorem R84295 : Reach 84295 := rs (se 1 (by rfl) ⟨63221, by rfl⟩) R126443
theorem R84379 : Reach 84379 := rs (se 1 (by rfl) ⟨63284, by rfl⟩) R126569
theorem R1165913 : Reach 1165913 := rs (se 2 (by rfl) ⟨437217, by rfl⟩) R874435
theorem R1756079 : Reach 1756079 := rs (se 1 (by rfl) ⟨1317059, by rfl⟩) R2634119
theorem R85535 : Reach 85535 := rs (se 1 (by rfl) ⟨64151, by rfl⟩) R128303
theorem R85787 : Reach 85787 := rs (se 1 (by rfl) ⟨64340, by rfl⟩) R128681
theorem R85871 : Reach 85871 := rs (se 1 (by rfl) ⟨64403, by rfl⟩) R128807
theorem R85927 : Reach 85927 := rs (se 1 (by rfl) ⟨64445, by rfl⟩) R128891
theorem R85951 : Reach 85951 := rs (se 1 (by rfl) ⟨64463, by rfl⟩) R128927
theorem R86767 : Reach 86767 := rs (se 1 (by rfl) ⟨65075, by rfl⟩) R130151
theorem R119551 : Reach 119551 := rs (se 1 (by rfl) ⟨89663, by rfl⟩) R179327
theorem R481609 : Reach 481609 := rs (se 2 (by rfl) ⟨180603, by rfl⟩) R361207
theorem R220043 : Reach 220043 := rs (se 1 (by rfl) ⟨165032, by rfl⟩) R330065
theorem R156937 : Reach 156937 := rs (se 2 (by rfl) ⟨58851, by rfl⟩) R117703
theorem R648809 : Reach 648809 := rs (se 2 (by rfl) ⟨243303, by rfl⟩) R486607
theorem R124763 : Reach 124763 := rs (se 1 (by rfl) ⟨93572, by rfl⟩) R187145
theorem R124799 : Reach 124799 := rs (se 1 (by rfl) ⟨93599, by rfl⟩) R187199
theorem R2386259 : Reach 2386259 := rs (se 1 (by rfl) ⟨1789694, by rfl⟩) R3579389
theorem R453059 : Reach 453059 := rs (se 1 (by rfl) ⟨339794, by rfl⟩) R679589
theorem R126203 : Reach 126203 := rs (se 1 (by rfl) ⟨94652, by rfl⟩) R189305
theorem R422009 : Reach 422009 := rs (se 2 (by rfl) ⟨158253, by rfl⟩) R316507
theorem R192671 : Reach 192671 := rs (se 1 (by rfl) ⟨144503, by rfl⟩) R289007
theorem R127211 : Reach 127211 := rs (se 1 (by rfl) ⟨95408, by rfl⟩) R190817
theorem R815615 : Reach 815615 := rs (se 1 (by rfl) ⟨611711, by rfl⟩) R1223423
theorem R324283 : Reach 324283 := rs (se 1 (by rfl) ⟨243212, by rfl⟩) R486425
theorem R980063 : Reach 980063 := rs (se 1 (by rfl) ⟨735047, by rfl⟩) R1470095
theorem R128231 : Reach 128231 := rs (se 1 (by rfl) ⟨96173, by rfl⟩) R192347
theorem R95647 : Reach 95647 := rs (se 1 (by rfl) ⟨71735, by rfl⟩) R143471
theorem R489023 : Reach 489023 := rs (se 1 (by rfl) ⟨366767, by rfl⟩) R733535
theorem R95935 : Reach 95935 := rs (se 1 (by rfl) ⟨71951, by rfl⟩) R143903
theorem R1079081 : Reach 1079081 := rs (se 2 (by rfl) ⟨404655, by rfl⟩) R809311
theorem R128879 : Reach 128879 := rs (se 1 (by rfl) ⟨96659, by rfl⟩) R193319
theorem R292733 : Reach 292733 := rs (se 3 (by rfl) ⟨54887, by rfl⟩) R109775
theorem R1178063 : Reach 1178063 := rs (se 1 (by rfl) ⟨883547, by rfl⟩) R1767095
theorem R326111 : Reach 326111 := rs (se 1 (by rfl) ⟨244583, by rfl⟩) R489167
theorem R129503 : Reach 129503 := rs (se 1 (by rfl) ⟨97127, by rfl⟩) R194255
theorem R195047 : Reach 195047 := rs (se 1 (by rfl) ⟨146285, by rfl⟩) R292571
theorem R195497 : Reach 195497 := rs (se 2 (by rfl) ⟨73311, by rfl⟩) R146623
theorem R195911 : Reach 195911 := rs (se 1 (by rfl) ⟨146933, by rfl⟩) R293867
theorem R294619 : Reach 294619 := rs (se 1 (by rfl) ⟨220964, by rfl⟩) R441929
theorem R360787 : Reach 360787 := rs (se 1 (by rfl) ⟨270590, by rfl⟩) R541181
theorem R426383 : Reach 426383 := rs (se 1 (by rfl) ⟨319787, by rfl⟩) R639575
theorem R131563 : Reach 131563 := rs (se 1 (by rfl) ⟨98672, by rfl⟩) R197345
theorem R3606605 : Reach 3606605 := rs (se 3 (by rfl) ⟨676238, by rfl⟩) R1352477
theorem R231545 : Reach 231545 := rs (se 2 (by rfl) ⟨86829, by rfl⟩) R173659
theorem R2165129 : Reach 2165129 := rs (se 2 (by rfl) ⟨811923, by rfl⟩) R1623847
theorem R921719 : Reach 921719 := rs (se 1 (by rfl) ⟨691289, by rfl⟩) R1382579
theorem R398267 : Reach 398267 := rs (se 1 (by rfl) ⟨298700, by rfl⟩) R597401
theorem R432377 : Reach 432377 := rs (se 2 (by rfl) ⟨162141, by rfl⟩) R324283
theorem R432539 : Reach 432539 := rs (se 1 (by rfl) ⟨324404, by rfl⟩) R648809
theorem R302039 : Reach 302039 := rs (se 1 (by rfl) ⟨226529, by rfl⟩) R453059
theorem R2728829 : Reach 2728829 := rs (se 3 (by rfl) ⟨511655, by rfl⟩) R1023311
theorem R796895 : Reach 796895 := rs (se 1 (by rfl) ⟨597671, by rfl⟩) R1195343
theorem R437561 : Reach 437561 := rs (se 2 (by rfl) ⟨164085, by rfl⟩) R328171
theorem R209249 : Reach 209249 := rs (se 2 (by rfl) ⟨78468, by rfl⟩) R156937
theorem R2568581 : Reach 2568581 := rs (se 4 (by rfl) ⟨240804, by rfl⟩) R481609
theorem R4633159 : Reach 4633159 := rs (se 1 (by rfl) ⟨3474869, by rfl⟩) R6949739
theorem R1226771 : Reach 1226771 := rs (se 1 (by rfl) ⟨920078, by rfl⟩) R1840157
theorem R146569 : Reach 146569 := rs (se 2 (by rfl) ⟨54963, by rfl⟩) R109927
theorem R146695 : Reach 146695 := rs (se 1 (by rfl) ⟨110021, by rfl⟩) R220043
theorem R83175 : Reach 83175 := rs (se 1 (by rfl) ⟨62381, by rfl⟩) R124763
theorem R869629 : Reach 869629 := rs (se 3 (by rfl) ⟨163055, by rfl⟩) R326111
theorem R83199 : Reach 83199 := rs (se 1 (by rfl) ⟨62399, by rfl⟩) R124799
theorem R1590839 : Reach 1590839 := rs (se 1 (by rfl) ⟨1193129, by rfl⟩) R2386259
theorem R84135 : Reach 84135 := rs (se 1 (by rfl) ⟨63101, by rfl⟩) R126203
theorem R281339 : Reach 281339 := rs (se 1 (by rfl) ⟨211004, by rfl⟩) R422009
theorem R84807 : Reach 84807 := rs (se 1 (by rfl) ⟨63605, by rfl⟩) R127211
theorem R543743 : Reach 543743 := rs (se 1 (by rfl) ⟨407807, by rfl⟩) R815615
theorem R85487 : Reach 85487 := rs (se 1 (by rfl) ⟨64115, by rfl⟩) R128231
theorem R282365 : Reach 282365 := rs (se 3 (by rfl) ⟨52943, by rfl⟩) R105887
theorem R85919 : Reach 85919 := rs (se 1 (by rfl) ⟨64439, by rfl⟩) R128879
theorem R86335 : Reach 86335 := rs (se 1 (by rfl) ⟨64751, by rfl⟩) R129503
theorem R1071083 : Reach 1071083 := rs (se 1 (by rfl) ⟨803312, by rfl⟩) R1606625
theorem R546871 : Reach 546871 := rs (se 1 (by rfl) ⟨410153, by rfl⟩) R820307
theorem R777275 : Reach 777275 := rs (se 1 (by rfl) ⟨582956, by rfl⟩) R1165913
theorem R1170719 : Reach 1170719 := rs (se 1 (by rfl) ⟨878039, by rfl⟩) R1756079
theorem R90607 : Reach 90607 := rs (se 1 (by rfl) ⟨67955, by rfl⟩) R135911
theorem R287387 : Reach 287387 := rs (se 1 (by rfl) ⟨215540, by rfl⟩) R431081
theorem R91615 : Reach 91615 := rs (se 1 (by rfl) ⟨68711, by rfl⟩) R137423
theorem R159401 : Reach 159401 := rs (se 2 (by rfl) ⟨59775, by rfl⟩) R119551
theorem R127529 : Reach 127529 := rs (se 2 (by rfl) ⟨47823, by rfl⟩) R95647
theorem R127913 : Reach 127913 := rs (se 2 (by rfl) ⟨47967, by rfl⟩) R95935
theorem R128447 : Reach 128447 := rs (se 1 (by rfl) ⟨96335, by rfl⟩) R192671
theorem R292679 : Reach 292679 := rs (se 1 (by rfl) ⟨219509, by rfl⟩) R439019
theorem R194537 : Reach 194537 := rs (se 2 (by rfl) ⟨72951, by rfl⟩) R145903
theorem R1112089 : Reach 1112089 := rs (se 2 (by rfl) ⟨417033, by rfl⟩) R834067
theorem R653375 : Reach 653375 := rs (se 1 (by rfl) ⟨490031, by rfl⟩) R980063
theorem R326015 : Reach 326015 := rs (se 1 (by rfl) ⟨244511, by rfl⟩) R489023
theorem R719387 : Reach 719387 := rs (se 1 (by rfl) ⟨539540, by rfl⟩) R1079081
theorem R195155 : Reach 195155 := rs (se 1 (by rfl) ⟨146366, by rfl⟩) R292733
theorem R293543 : Reach 293543 := rs (se 1 (by rfl) ⟨220157, by rfl⟩) R440315
theorem R785375 : Reach 785375 := rs (se 1 (by rfl) ⟨589031, by rfl⟩) R1178063
theorem R130031 : Reach 130031 := rs (se 1 (by rfl) ⟨97523, by rfl⟩) R195047
theorem R97447 : Reach 97447 := rs (se 1 (by rfl) ⟨73085, by rfl⟩) R146171
theorem R130331 : Reach 130331 := rs (se 1 (by rfl) ⟨97748, by rfl⟩) R195497
theorem R130607 : Reach 130607 := rs (se 1 (by rfl) ⟨97955, by rfl⟩) R195911
theorem R392825 : Reach 392825 := rs (se 2 (by rfl) ⟨147309, by rfl⟩) R294619
theorem R1443419 : Reach 1443419 := rs (se 1 (by rfl) ⟨1082564, by rfl⟩) R2165129
theorem R362495 : Reach 362495 := rs (se 1 (by rfl) ⟨271871, by rfl⟩) R543743
theorem R265511 : Reach 265511 := rs (se 1 (by rfl) ⟨199133, by rfl⟩) R398267
theorem R201359 : Reach 201359 := rs (se 1 (by rfl) ⟨151019, by rfl⟩) R302039
theorem R531263 : Reach 531263 := rs (se 1 (by rfl) ⟨398447, by rfl⟩) R796895
theorem R106267 : Reach 106267 := rs (se 1 (by rfl) ⟨79700, by rfl⟩) R159401
theorem R1482785 : Reach 1482785 := rs (se 2 (by rfl) ⟨556044, by rfl⟩) R1112089
theorem R729161 : Reach 729161 := rs (se 2 (by rfl) ⟨273435, by rfl⟩) R546871
theorem R139499 : Reach 139499 := rs (se 1 (by rfl) ⟨104624, by rfl⟩) R209249
theorem R1712387 : Reach 1712387 := rs (se 1 (by rfl) ⟨1284290, by rfl⟩) R2568581
theorem R435583 : Reach 435583 := rs (se 1 (by rfl) ⟨326687, by rfl⟩) R653375
theorem R1060559 : Reach 1060559 := rs (se 1 (by rfl) ⟨795419, by rfl⟩) R1590839
theorem R2404403 : Reach 2404403 := rs (se 1 (by rfl) ⟨1803302, by rfl⟩) R3606605
theorem R1159505 : Reach 1159505 := rs (se 2 (by rfl) ⟨434814, by rfl⟩) R869629
theorem R701669 : Reach 701669 := rs (se 4 (by rfl) ⟨65781, by rfl⟩) R131563
theorem R1819219 : Reach 1819219 := rs (se 1 (by rfl) ⟨1364414, by rfl⟩) R2728829
theorem R6177545 : Reach 6177545 := rs (se 2 (by rfl) ⟨2316579, by rfl⟩) R4633159
theorem R85019 : Reach 85019 := rs (se 1 (by rfl) ⟨63764, by rfl⟩) R127529
theorem R85275 : Reach 85275 := rs (se 1 (by rfl) ⟨63956, by rfl⟩) R127913
theorem R85631 : Reach 85631 := rs (se 1 (by rfl) ⟨64223, by rfl⟩) R128447
theorem R217343 : Reach 217343 := rs (se 1 (by rfl) ⟨163007, by rfl⟩) R326015
theorem R479591 : Reach 479591 := rs (se 1 (by rfl) ⟨359693, by rfl⟩) R719387
theorem R86687 : Reach 86687 := rs (se 1 (by rfl) ⟨65015, by rfl⟩) R130031
theorem R86887 : Reach 86887 := rs (se 1 (by rfl) ⟨65165, by rfl⟩) R130331
theorem R87071 : Reach 87071 := rs (se 1 (by rfl) ⟨65303, by rfl⟩) R130607
theorem R284255 : Reach 284255 := rs (se 1 (by rfl) ⟨213191, by rfl⟩) R426383
theorem R481049 : Reach 481049 := rs (se 2 (by rfl) ⟨180393, by rfl⟩) R360787
theorem R120809 : Reach 120809 := rs (se 2 (by rfl) ⟨45303, by rfl⟩) R90607
theorem R187559 : Reach 187559 := rs (se 1 (by rfl) ⟨140669, by rfl⟩) R281339
theorem R122153 : Reach 122153 := rs (se 2 (by rfl) ⟨45807, by rfl⟩) R91615
theorem R188243 : Reach 188243 := rs (se 1 (by rfl) ⟨141182, by rfl⟩) R282365
theorem R614479 : Reach 614479 := rs (se 1 (by rfl) ⟨460859, by rfl⟩) R921719
theorem R714055 : Reach 714055 := rs (se 1 (by rfl) ⟨535541, by rfl⟩) R1071083
theorem R288251 : Reach 288251 := rs (se 1 (by rfl) ⟨216188, by rfl⟩) R432377
theorem R288359 : Reach 288359 := rs (se 1 (by rfl) ⟨216269, by rfl⟩) R432539
theorem R518183 : Reach 518183 := rs (se 1 (by rfl) ⟨388637, by rfl⟩) R777275
theorem R780479 : Reach 780479 := rs (se 1 (by rfl) ⟨585359, by rfl⟩) R1170719
theorem R617453 : Reach 617453 := rs (se 3 (by rfl) ⟨115772, by rfl⟩) R231545
theorem R191591 : Reach 191591 := rs (se 1 (by rfl) ⟨143693, by rfl⟩) R287387
theorem R291707 : Reach 291707 := rs (se 1 (by rfl) ⟨218780, by rfl⟩) R437561
theorem R195119 : Reach 195119 := rs (se 1 (by rfl) ⟨146339, by rfl⟩) R292679
theorem R129691 : Reach 129691 := rs (se 1 (by rfl) ⟨97268, by rfl⟩) R194537
theorem R817847 : Reach 817847 := rs (se 1 (by rfl) ⟨613385, by rfl⟩) R1226771
theorem R195425 : Reach 195425 := rs (se 2 (by rfl) ⟨73284, by rfl⟩) R146569
theorem R129929 : Reach 129929 := rs (se 2 (by rfl) ⟨48723, by rfl⟩) R97447
theorem R195593 : Reach 195593 := rs (se 2 (by rfl) ⟨73347, by rfl⟩) R146695
theorem R130103 : Reach 130103 := rs (se 1 (by rfl) ⟨97577, by rfl⟩) R195155
theorem R195695 : Reach 195695 := rs (se 1 (by rfl) ⟨146771, by rfl⟩) R293543
theorem R523583 : Reach 523583 := rs (se 1 (by rfl) ⟨392687, by rfl⟩) R785375
theorem R261883 : Reach 261883 := rs (se 1 (by rfl) ⟨196412, by rfl⟩) R392825
theorem R819305 : Reach 819305 := rs (se 2 (by rfl) ⟨307239, by rfl⟩) R614479
theorem R2425625 : Reach 2425625 := rs (se 2 (by rfl) ⟨909609, by rfl⟩) R1819219
theorem R952073 : Reach 952073 := rs (se 2 (by rfl) ⟨357027, by rfl⟩) R714055
theorem R134239 : Reach 134239 := rs (se 1 (by rfl) ⟨100679, by rfl⟩) R201359
theorem R691685 : Reach 691685 := rs (se 4 (by rfl) ⟨64845, by rfl⟩) R129691
theorem R988523 : Reach 988523 := rs (se 1 (by rfl) ⟨741392, by rfl⟩) R1482785
theorem R1416701 : Reach 1416701 := rs (se 3 (by rfl) ⟨265631, by rfl⟩) R531263
theorem R467779 : Reach 467779 := rs (se 1 (by rfl) ⟨350834, by rfl⟩) R701669
theorem R141689 : Reach 141689 := rs (se 2 (by rfl) ⟨53133, by rfl⟩) R106267
theorem R4566365 : Reach 4566365 := rs (se 3 (by rfl) ⟨856193, by rfl⟩) R1712387
theorem R962279 : Reach 962279 := rs (se 1 (by rfl) ⟨721709, by rfl⟩) R1443419
theorem R177007 : Reach 177007 := rs (se 1 (by rfl) ⟨132755, by rfl⟩) R265511
theorem R144895 : Reach 144895 := rs (se 1 (by rfl) ⟨108671, by rfl⟩) R217343
theorem R966653 : Reach 966653 := rs (se 3 (by rfl) ⟨181247, by rfl⟩) R362495
theorem R345455 : Reach 345455 := rs (se 1 (by rfl) ⟨259091, by rfl⟩) R518183
theorem R411635 : Reach 411635 := rs (se 1 (by rfl) ⟨308726, by rfl⟩) R617453
theorem R707039 : Reach 707039 := rs (se 1 (by rfl) ⟨530279, by rfl⟩) R1060559
theorem R773003 : Reach 773003 := rs (se 1 (by rfl) ⟨579752, by rfl⟩) R1159505
theorem R545231 : Reach 545231 := rs (se 1 (by rfl) ⟨408923, by rfl⟩) R817847
theorem R86619 : Reach 86619 := rs (se 1 (by rfl) ⟨64964, by rfl⟩) R129929
theorem R86735 : Reach 86735 := rs (se 1 (by rfl) ⟨65051, by rfl⟩) R130103
theorem R349055 : Reach 349055 := rs (se 1 (by rfl) ⟨261791, by rfl⟩) R523583
theorem R349177 : Reach 349177 := rs (se 2 (by rfl) ⟨130941, by rfl⟩) R261883
theorem R4118363 : Reach 4118363 := rs (se 1 (by rfl) ⟨3088772, by rfl⟩) R6177545
theorem R319727 : Reach 319727 := rs (se 1 (by rfl) ⟨239795, by rfl⟩) R479591
theorem R189503 : Reach 189503 := rs (se 1 (by rfl) ⟨142127, by rfl⟩) R284255
theorem R320699 : Reach 320699 := rs (se 1 (by rfl) ⟨240524, by rfl⟩) R481049
theorem R125039 : Reach 125039 := rs (se 1 (by rfl) ⟨93779, by rfl⟩) R187559
theorem R125495 : Reach 125495 := rs (se 1 (by rfl) ⟨94121, by rfl⟩) R188243
theorem R322157 : Reach 322157 := rs (se 3 (by rfl) ⟨60404, by rfl⟩) R120809
theorem R486107 : Reach 486107 := rs (se 1 (by rfl) ⟨364580, by rfl⟩) R729161
theorem R92999 : Reach 92999 := rs (se 1 (by rfl) ⟨69749, by rfl⟩) R139499
theorem R192167 : Reach 192167 := rs (se 1 (by rfl) ⟨144125, by rfl⟩) R288251
theorem R192239 : Reach 192239 := rs (se 1 (by rfl) ⟨144179, by rfl⟩) R288359
theorem R520319 : Reach 520319 := rs (se 1 (by rfl) ⟨390239, by rfl⟩) R780479
theorem R2323109 : Reach 2323109 := rs (se 4 (by rfl) ⟨217791, by rfl⟩) R435583
theorem R127727 : Reach 127727 := rs (se 1 (by rfl) ⟨95795, by rfl⟩) R191591
theorem R521581 : Reach 521581 := rs (se 3 (by rfl) ⟨97796, by rfl⟩) R195593
theorem R1602935 : Reach 1602935 := rs (se 1 (by rfl) ⟨1202201, by rfl⟩) R2404403
theorem R194471 : Reach 194471 := rs (se 1 (by rfl) ⟨145853, by rfl⟩) R291707
theorem R325741 : Reach 325741 := rs (se 3 (by rfl) ⟨61076, by rfl⟩) R122153
theorem R130079 : Reach 130079 := rs (se 1 (by rfl) ⟨97559, by rfl⟩) R195119
theorem R130283 : Reach 130283 := rs (se 1 (by rfl) ⟨97712, by rfl⟩) R195425
theorem R130463 : Reach 130463 := rs (se 1 (by rfl) ⟨97847, by rfl⟩) R195695
theorem R230303 : Reach 230303 := rs (se 1 (by rfl) ⟨172727, by rfl⟩) R345455
theorem R623705 : Reach 623705 := rs (se 2 (by rfl) ⟨233889, by rfl⟩) R467779
theorem R461123 : Reach 461123 := rs (se 1 (by rfl) ⟨345842, by rfl⟩) R691685
theorem R363487 : Reach 363487 := rs (se 1 (by rfl) ⟨272615, by rfl⟩) R545231
theorem R232703 : Reach 232703 := rs (se 1 (by rfl) ⟨174527, by rfl⟩) R349055
theorem R659015 : Reach 659015 := rs (se 1 (by rfl) ⟨494261, by rfl⟩) R988523
theorem R236009 : Reach 236009 := rs (se 2 (by rfl) ⟨88503, by rfl⟩) R177007
theorem R465569 : Reach 465569 := rs (se 2 (by rfl) ⟨174588, by rfl⟩) R349177
theorem R695441 : Reach 695441 := rs (se 2 (by rfl) ⟨260790, by rfl⟩) R521581
theorem R434321 : Reach 434321 := rs (se 2 (by rfl) ⟨162870, by rfl⟩) R325741
theorem R1548739 : Reach 1548739 := rs (se 1 (by rfl) ⟨1161554, by rfl⟩) R2323109
theorem R1617083 : Reach 1617083 := rs (se 1 (by rfl) ⟨1212812, by rfl⟩) R2425625
theorem R634715 : Reach 634715 := rs (se 1 (by rfl) ⟨476036, by rfl⟩) R952073
theorem R274423 : Reach 274423 := rs (se 1 (by rfl) ⟨205817, by rfl⟩) R411635
theorem R471359 : Reach 471359 := rs (se 1 (by rfl) ⟨353519, by rfl⟩) R707039
theorem R178985 : Reach 178985 := rs (se 2 (by rfl) ⟨67119, by rfl⟩) R134239
theorem R213151 : Reach 213151 := rs (se 1 (by rfl) ⟨159863, by rfl⟩) R319727
theorem R213799 : Reach 213799 := rs (se 1 (by rfl) ⟨160349, by rfl⟩) R320699
theorem R83359 : Reach 83359 := rs (se 1 (by rfl) ⟨62519, by rfl⟩) R125039
theorem R83663 : Reach 83663 := rs (se 1 (by rfl) ⟨62747, by rfl⟩) R125495
theorem R214771 : Reach 214771 := rs (se 1 (by rfl) ⟨161078, by rfl⟩) R322157
theorem R247997 : Reach 247997 := rs (se 3 (by rfl) ⟨46499, by rfl⟩) R92999
theorem R641519 : Reach 641519 := rs (se 1 (by rfl) ⟨481139, by rfl⟩) R962279
theorem R346879 : Reach 346879 := rs (se 1 (by rfl) ⟨260159, by rfl⟩) R520319
theorem R85151 : Reach 85151 := rs (se 1 (by rfl) ⟨63863, by rfl⟩) R127727
theorem R1068623 : Reach 1068623 := rs (se 1 (by rfl) ⟨801467, by rfl⟩) R1602935
theorem R86719 : Reach 86719 := rs (se 1 (by rfl) ⟨65039, by rfl⟩) R130079
theorem R86855 : Reach 86855 := rs (se 1 (by rfl) ⟨65141, by rfl⟩) R130283
theorem R86975 : Reach 86975 := rs (se 1 (by rfl) ⟨65231, by rfl⟩) R130463
theorem R644435 : Reach 644435 := rs (se 1 (by rfl) ⟨483326, by rfl⟩) R966653
theorem R546203 : Reach 546203 := rs (se 1 (by rfl) ⟨409652, by rfl⟩) R819305
theorem R515335 : Reach 515335 := rs (se 1 (by rfl) ⟨386501, by rfl⟩) R773003
theorem R2745575 : Reach 2745575 := rs (se 1 (by rfl) ⟨2059181, by rfl⟩) R4118363
theorem R944467 : Reach 944467 := rs (se 1 (by rfl) ⟨708350, by rfl⟩) R1416701
theorem R126335 : Reach 126335 := rs (se 1 (by rfl) ⟨94751, by rfl⟩) R189503
theorem R94459 : Reach 94459 := rs (se 1 (by rfl) ⟨70844, by rfl⟩) R141689
theorem R324071 : Reach 324071 := rs (se 1 (by rfl) ⟨243053, by rfl⟩) R486107
theorem R193193 : Reach 193193 := rs (se 2 (by rfl) ⟨72447, by rfl⟩) R144895
theorem R3044243 : Reach 3044243 := rs (se 1 (by rfl) ⟨2283182, by rfl⟩) R4566365
theorem R128111 : Reach 128111 := rs (se 1 (by rfl) ⟨96083, by rfl⟩) R192167
theorem R128159 : Reach 128159 := rs (se 1 (by rfl) ⟨96119, by rfl⟩) R192239
theorem R129647 : Reach 129647 := rs (se 1 (by rfl) ⟨97235, by rfl⟩) R194471
theorem R165331 : Reach 165331 := rs (se 1 (by rfl) ⟨123998, by rfl⟩) R247997
theorem R427679 : Reach 427679 := rs (se 1 (by rfl) ⟨320759, by rfl⟩) R641519
theorem R8259941 : Reach 8259941 := rs (se 4 (by rfl) ⟨774369, by rfl⟩) R1548739
theorem R429623 : Reach 429623 := rs (se 1 (by rfl) ⟨322217, by rfl⟩) R644435
theorem R462505 : Reach 462505 := rs (se 2 (by rfl) ⟨173439, by rfl⟩) R346879
theorem R463627 : Reach 463627 := rs (se 1 (by rfl) ⟨347720, by rfl⟩) R695441
theorem R365897 : Reach 365897 := rs (se 2 (by rfl) ⟨137211, by rfl⟩) R274423
theorem R1256957 : Reach 1256957 := rs (se 3 (by rfl) ⟨235679, by rfl⟩) R471359
theorem R307415 : Reach 307415 := rs (se 1 (by rfl) ⟨230561, by rfl⟩) R461123
theorem R439343 : Reach 439343 := rs (se 1 (by rfl) ⟨329507, by rfl⟩) R659015
theorem R1456541 : Reach 1456541 := rs (se 3 (by rfl) ⟨273101, by rfl⟩) R546203
theorem R4966069 : Reach 4966069 := rs (se 5 (by rfl) ⟨232784, by rfl⟩) R465569
theorem R84223 : Reach 84223 := rs (se 1 (by rfl) ⟨63167, by rfl⟩) R126335
theorem R216047 : Reach 216047 := rs (se 1 (by rfl) ⟨162035, by rfl⟩) R324071
theorem R85407 : Reach 85407 := rs (se 1 (by rfl) ⟨64055, by rfl⟩) R128111
theorem R85439 : Reach 85439 := rs (se 1 (by rfl) ⟨64079, by rfl⟩) R128159
theorem R86431 : Reach 86431 := rs (se 1 (by rfl) ⟨64823, by rfl⟩) R129647
theorem R119323 : Reach 119323 := rs (se 1 (by rfl) ⟨89492, by rfl⟩) R178985
theorem R284201 : Reach 284201 := rs (se 2 (by rfl) ⟨106575, by rfl⟩) R213151
theorem R153535 : Reach 153535 := rs (se 1 (by rfl) ⟨115151, by rfl⟩) R230303
theorem R285065 : Reach 285065 := rs (se 2 (by rfl) ⟨106899, by rfl⟩) R213799
theorem R5037157 : Reach 5037157 := rs (se 4 (by rfl) ⟨472233, by rfl⟩) R944467
theorem R155135 : Reach 155135 := rs (se 1 (by rfl) ⟨116351, by rfl⟩) R232703
theorem R286361 : Reach 286361 := rs (se 2 (by rfl) ⟨107385, by rfl⟩) R214771
theorem R712415 : Reach 712415 := rs (se 1 (by rfl) ⟨534311, by rfl⟩) R1068623
theorem R1663213 : Reach 1663213 := rs (se 3 (by rfl) ⟨311852, by rfl⟩) R623705
theorem R484649 : Reach 484649 := rs (se 2 (by rfl) ⟨181743, by rfl⟩) R363487
theorem R157339 : Reach 157339 := rs (se 1 (by rfl) ⟨118004, by rfl⟩) R236009
theorem R289547 : Reach 289547 := rs (se 1 (by rfl) ⟨217160, by rfl⟩) R434321
theorem R125945 : Reach 125945 := rs (se 2 (by rfl) ⟨47229, by rfl⟩) R94459
theorem R1830383 : Reach 1830383 := rs (se 1 (by rfl) ⟨1372787, by rfl⟩) R2745575
theorem R1078055 : Reach 1078055 := rs (se 1 (by rfl) ⟨808541, by rfl⟩) R1617083
theorem R423143 : Reach 423143 := rs (se 1 (by rfl) ⟨317357, by rfl⟩) R634715
theorem R128795 : Reach 128795 := rs (se 1 (by rfl) ⟨96596, by rfl⟩) R193193
theorem R2029495 : Reach 2029495 := rs (se 1 (by rfl) ⟨1522121, by rfl⟩) R3044243
theorem R687113 : Reach 687113 := rs (se 2 (by rfl) ⟨257667, by rfl⟩) R515335
theorem R5506627 : Reach 5506627 := rs (se 1 (by rfl) ⟨4129970, by rfl⟩) R8259941
theorem R6621425 : Reach 6621425 := rs (se 2 (by rfl) ⟨2483034, by rfl⟩) R4966069
theorem R1220255 : Reach 1220255 := rs (se 1 (by rfl) ⟨915191, by rfl⟩) R1830383
theorem R204713 : Reach 204713 := rs (se 2 (by rfl) ⟨76767, by rfl⟩) R153535
theorem R204943 : Reach 204943 := rs (se 1 (by rfl) ⟨153707, by rfl⟩) R307415
theorem R144031 : Reach 144031 := rs (se 1 (by rfl) ⟨108023, by rfl⟩) R216047
theorem R209785 : Reach 209785 := rs (se 2 (by rfl) ⟨78669, by rfl⟩) R157339
theorem R243931 : Reach 243931 := rs (se 1 (by rfl) ⟨182948, by rfl⟩) R365897
theorem R2472677 : Reach 2472677 := rs (se 4 (by rfl) ⟨231813, by rfl⟩) R463627
theorem R474943 : Reach 474943 := rs (se 1 (by rfl) ⟨356207, by rfl⟩) R712415
theorem R83963 : Reach 83963 := rs (se 1 (by rfl) ⟨62972, by rfl⟩) R125945
theorem R837971 : Reach 837971 := rs (se 1 (by rfl) ⟨628478, by rfl⟩) R1256957
theorem R2705993 : Reach 2705993 := rs (se 2 (by rfl) ⟨1014747, by rfl⟩) R2029495
theorem R282095 : Reach 282095 := rs (se 1 (by rfl) ⟨211571, by rfl⟩) R423143
theorem R85863 : Reach 85863 := rs (se 1 (by rfl) ⟨64397, by rfl⟩) R128795
theorem R413693 : Reach 413693 := rs (se 3 (by rfl) ⟨77567, by rfl⟩) R155135
theorem R971027 : Reach 971027 := rs (se 1 (by rfl) ⟨728270, by rfl⟩) R1456541
theorem R2217617 : Reach 2217617 := rs (se 2 (by rfl) ⟨831606, by rfl⟩) R1663213
theorem R285119 : Reach 285119 := rs (se 1 (by rfl) ⟨213839, by rfl⟩) R427679
theorem R220441 : Reach 220441 := rs (se 2 (by rfl) ⟨82665, by rfl⟩) R165331
theorem R286415 : Reach 286415 := rs (se 1 (by rfl) ⟨214811, by rfl⟩) R429623
theorem R189467 : Reach 189467 := rs (se 1 (by rfl) ⟨142100, by rfl⟩) R284201
theorem R190043 : Reach 190043 := rs (se 1 (by rfl) ⟨142532, by rfl⟩) R285065
theorem R616673 : Reach 616673 := rs (se 2 (by rfl) ⟨231252, by rfl⟩) R462505
theorem R190907 : Reach 190907 := rs (se 1 (by rfl) ⟨143180, by rfl⟩) R286361
theorem R159097 : Reach 159097 := rs (se 2 (by rfl) ⟨59661, by rfl⟩) R119323
theorem R323099 : Reach 323099 := rs (se 1 (by rfl) ⟨242324, by rfl⟩) R484649
theorem R193031 : Reach 193031 := rs (se 1 (by rfl) ⟨144773, by rfl⟩) R289547
theorem R718703 : Reach 718703 := rs (se 1 (by rfl) ⟨539027, by rfl⟩) R1078055
theorem R292895 : Reach 292895 := rs (se 1 (by rfl) ⟨219671, by rfl⟩) R439343
theorem R6716209 : Reach 6716209 := rs (se 2 (by rfl) ⟨2518578, by rfl⟩) R5037157
theorem R458075 : Reach 458075 := rs (se 1 (by rfl) ⟨343556, by rfl⟩) R687113
theorem R558647 : Reach 558647 := rs (se 1 (by rfl) ⟨418985, by rfl⟩) R837971
theorem R1803995 : Reach 1803995 := rs (se 1 (by rfl) ⟨1352996, by rfl⟩) R2705993
theorem R7342169 : Reach 7342169 := rs (se 2 (by rfl) ⟨2753313, by rfl⟩) R5506627
theorem R1478411 : Reach 1478411 := rs (se 1 (by rfl) ⟨1108808, by rfl⟩) R2217617
theorem R136475 : Reach 136475 := rs (se 1 (by rfl) ⟨102356, by rfl⟩) R204713
theorem R8954945 : Reach 8954945 := rs (se 2 (by rfl) ⟨3358104, by rfl⟩) R6716209
theorem R1648451 : Reach 1648451 := rs (se 1 (by rfl) ⟨1236338, by rfl⟩) R2472677
theorem R305383 : Reach 305383 := rs (se 1 (by rfl) ⟨229037, by rfl⟩) R458075
theorem R633257 : Reach 633257 := rs (se 2 (by rfl) ⟨237471, by rfl⟩) R474943
theorem R273257 : Reach 273257 := rs (se 2 (by rfl) ⟨102471, by rfl⟩) R204943
theorem R275795 : Reach 275795 := rs (se 1 (by rfl) ⟨206846, by rfl⟩) R413693
theorem R212129 : Reach 212129 := rs (se 2 (by rfl) ⟨79548, by rfl⟩) R159097
theorem R279713 : Reach 279713 := rs (se 2 (by rfl) ⟨104892, by rfl⟩) R209785
theorem R411115 : Reach 411115 := rs (se 1 (by rfl) ⟨308336, by rfl⟩) R616673
theorem R215399 : Reach 215399 := rs (se 1 (by rfl) ⟨161549, by rfl⟩) R323099
theorem R479135 : Reach 479135 := rs (se 1 (by rfl) ⟨359351, by rfl⟩) R718703
theorem R4414283 : Reach 4414283 := rs (se 1 (by rfl) ⟨3310712, by rfl⟩) R6621425
theorem R188063 : Reach 188063 := rs (se 1 (by rfl) ⟨141047, by rfl⟩) R282095
theorem R647351 : Reach 647351 := rs (se 1 (by rfl) ⟨485513, by rfl⟩) R971027
theorem R190079 : Reach 190079 := rs (se 1 (by rfl) ⟨142559, by rfl⟩) R285119
theorem R813503 : Reach 813503 := rs (se 1 (by rfl) ⟨610127, by rfl⟩) R1220255
theorem R190943 : Reach 190943 := rs (se 1 (by rfl) ⟨143207, by rfl⟩) R286415
theorem R126311 : Reach 126311 := rs (se 1 (by rfl) ⟨94733, by rfl⟩) R189467
theorem R192041 : Reach 192041 := rs (se 2 (by rfl) ⟨72015, by rfl⟩) R144031
theorem R126695 : Reach 126695 := rs (se 1 (by rfl) ⟨95021, by rfl⟩) R190043
theorem R127271 : Reach 127271 := rs (se 1 (by rfl) ⟨95453, by rfl⟩) R190907
theorem R325241 : Reach 325241 := rs (se 2 (by rfl) ⟨121965, by rfl⟩) R243931
theorem R128687 : Reach 128687 := rs (se 1 (by rfl) ⟨96515, by rfl⟩) R193031
theorem R195263 : Reach 195263 := rs (se 1 (by rfl) ⟨146447, by rfl⟩) R292895
theorem R293921 : Reach 293921 := rs (se 2 (by rfl) ⟨110220, by rfl⟩) R220441
theorem R985607 : Reach 985607 := rs (se 1 (by rfl) ⟨739205, by rfl⟩) R1478411
theorem R431567 : Reach 431567 := rs (se 1 (by rfl) ⟨323675, by rfl⟩) R647351
theorem R5969963 : Reach 5969963 := rs (se 1 (by rfl) ⟨4477472, by rfl⟩) R8954945
theorem R141419 : Reach 141419 := rs (se 1 (by rfl) ⟨106064, by rfl⟩) R212129
theorem R372431 : Reach 372431 := rs (se 1 (by rfl) ⟨279323, by rfl⟩) R558647
theorem R143599 : Reach 143599 := rs (se 1 (by rfl) ⟨107699, by rfl⟩) R215399
theorem R407177 : Reach 407177 := rs (se 2 (by rfl) ⟨152691, by rfl⟩) R305383
theorem R19579117 : Reach 19579117 := rs (se 3 (by rfl) ⟨3671084, by rfl⟩) R7342169
theorem R1098967 : Reach 1098967 := rs (se 1 (by rfl) ⟨824225, by rfl⟩) R1648451
theorem R542335 : Reach 542335 := rs (se 1 (by rfl) ⟨406751, by rfl⟩) R813503
theorem R182171 : Reach 182171 := rs (se 1 (by rfl) ⟨136628, by rfl⟩) R273257
theorem R84207 : Reach 84207 := rs (se 1 (by rfl) ⟨63155, by rfl⟩) R126311
theorem R84463 : Reach 84463 := rs (se 1 (by rfl) ⟨63347, by rfl⟩) R126695
theorem R84847 : Reach 84847 := rs (se 1 (by rfl) ⟨63635, by rfl⟩) R127271
theorem R183863 : Reach 183863 := rs (se 1 (by rfl) ⟨137897, by rfl⟩) R275795
theorem R216827 : Reach 216827 := rs (se 1 (by rfl) ⟨162620, by rfl⟩) R325241
theorem R85791 : Reach 85791 := rs (se 1 (by rfl) ⟨64343, by rfl⟩) R128687
theorem R186475 : Reach 186475 := rs (se 1 (by rfl) ⟨139856, by rfl⟩) R279713
theorem R1202663 : Reach 1202663 := rs (se 1 (by rfl) ⟨901997, by rfl⟩) R1803995
theorem R548153 : Reach 548153 := rs (se 2 (by rfl) ⟨205557, by rfl⟩) R411115
theorem R319423 : Reach 319423 := rs (se 1 (by rfl) ⟨239567, by rfl⟩) R479135
theorem R90983 : Reach 90983 := rs (se 1 (by rfl) ⟨68237, by rfl⟩) R136475
theorem R2942855 : Reach 2942855 := rs (se 1 (by rfl) ⟨2207141, by rfl⟩) R4414283
theorem R125375 : Reach 125375 := rs (se 1 (by rfl) ⟨94031, by rfl⟩) R188063
theorem R126719 : Reach 126719 := rs (se 1 (by rfl) ⟨95039, by rfl⟩) R190079
theorem R422171 : Reach 422171 := rs (se 1 (by rfl) ⟨316628, by rfl⟩) R633257
theorem R127295 : Reach 127295 := rs (se 1 (by rfl) ⟨95471, by rfl⟩) R190943
theorem R128027 : Reach 128027 := rs (se 1 (by rfl) ⟨96020, by rfl⟩) R192041
theorem R130175 : Reach 130175 := rs (se 1 (by rfl) ⟨97631, by rfl⟩) R195263
theorem R195947 : Reach 195947 := rs (se 1 (by rfl) ⟨146960, by rfl⟩) R293921
theorem R657071 : Reach 657071 := rs (se 1 (by rfl) ⟨492803, by rfl⟩) R985607
theorem R723113 : Reach 723113 := rs (se 2 (by rfl) ⟨271167, by rfl⟩) R542335
theorem R365435 : Reach 365435 := rs (se 1 (by rfl) ⟨274076, by rfl⟩) R548153
theorem R271451 : Reach 271451 := rs (se 1 (by rfl) ⟨203588, by rfl⟩) R407177
theorem R242621 : Reach 242621 := rs (se 3 (by rfl) ⟨45491, by rfl⟩) R90983
theorem R144551 : Reach 144551 := rs (se 1 (by rfl) ⟨108413, by rfl⟩) R216827
theorem R3979975 : Reach 3979975 := rs (se 1 (by rfl) ⟨2984981, by rfl⟩) R5969963
theorem R801775 : Reach 801775 := rs (se 1 (by rfl) ⟨601331, by rfl⟩) R1202663
theorem R83583 : Reach 83583 := rs (se 1 (by rfl) ⟨62687, by rfl⟩) R125375
theorem R248287 : Reach 248287 := rs (se 1 (by rfl) ⟨186215, by rfl⟩) R372431
theorem R84479 : Reach 84479 := rs (se 1 (by rfl) ⟨63359, by rfl⟩) R126719
theorem R248633 : Reach 248633 := rs (se 2 (by rfl) ⟨93237, by rfl⟩) R186475
theorem R281447 : Reach 281447 := rs (se 1 (by rfl) ⟨211085, by rfl⟩) R422171
theorem R84863 : Reach 84863 := rs (se 1 (by rfl) ⟨63647, by rfl⟩) R127295
theorem R85351 : Reach 85351 := rs (se 1 (by rfl) ⟨64013, by rfl⟩) R128027
theorem R86783 : Reach 86783 := rs (se 1 (by rfl) ⟨65087, by rfl⟩) R130175
theorem R26105489 : Reach 26105489 := rs (se 2 (by rfl) ⟨9789558, by rfl⟩) R19579117
theorem R121447 : Reach 121447 := rs (se 1 (by rfl) ⟨91085, by rfl⟩) R182171
theorem R1465289 : Reach 1465289 := rs (se 2 (by rfl) ⟨549483, by rfl⟩) R1098967
theorem R122575 : Reach 122575 := rs (se 1 (by rfl) ⟨91931, by rfl⟩) R183863
theorem R287711 : Reach 287711 := rs (se 1 (by rfl) ⟨215783, by rfl⟩) R431567
theorem R191465 : Reach 191465 := rs (se 2 (by rfl) ⟨71799, by rfl⟩) R143599
theorem R1961903 : Reach 1961903 := rs (se 1 (by rfl) ⟨1471427, by rfl⟩) R2942855
theorem R94279 : Reach 94279 := rs (se 1 (by rfl) ⟨70709, by rfl⟩) R141419
theorem R130631 : Reach 130631 := rs (se 1 (by rfl) ⟨97973, by rfl⟩) R195947
theorem R425897 : Reach 425897 := rs (se 2 (by rfl) ⟨159711, by rfl⟩) R319423
theorem R165755 : Reach 165755 := rs (se 1 (by rfl) ⟨124316, by rfl⟩) R248633
theorem R331049 : Reach 331049 := rs (se 2 (by rfl) ⟨124143, by rfl⟩) R248287
theorem R17403659 : Reach 17403659 := rs (se 1 (by rfl) ⟨13052744, by rfl⟩) R26105489
theorem R438047 : Reach 438047 := rs (se 1 (by rfl) ⟨328535, by rfl⟩) R657071
theorem R243623 : Reach 243623 := rs (se 1 (by rfl) ⟨182717, by rfl⟩) R365435
theorem R180967 : Reach 180967 := rs (se 1 (by rfl) ⟨135725, by rfl⟩) R271451
theorem R1069033 : Reach 1069033 := rs (se 2 (by rfl) ⟨400887, by rfl⟩) R801775
theorem R87087 : Reach 87087 := rs (se 1 (by rfl) ⟨65315, by rfl⟩) R130631
theorem R283931 : Reach 283931 := rs (se 1 (by rfl) ⟨212948, by rfl⟩) R425897
theorem R482075 : Reach 482075 := rs (se 1 (by rfl) ⟨361556, by rfl⟩) R723113
theorem R187631 : Reach 187631 := rs (se 1 (by rfl) ⟨140723, by rfl⟩) R281447
theorem R976859 : Reach 976859 := rs (se 1 (by rfl) ⟨732644, by rfl⟩) R1465289
theorem R125705 : Reach 125705 := rs (se 2 (by rfl) ⟨47139, by rfl⟩) R94279
theorem R191807 : Reach 191807 := rs (se 1 (by rfl) ⟨143855, by rfl⟩) R287711
theorem R127643 : Reach 127643 := rs (se 1 (by rfl) ⟨95732, by rfl⟩) R191465
theorem R1307935 : Reach 1307935 := rs (se 1 (by rfl) ⟨980951, by rfl⟩) R1961903
theorem R161747 : Reach 161747 := rs (se 1 (by rfl) ⟨121310, by rfl⟩) R242621
theorem R96367 : Reach 96367 := rs (se 1 (by rfl) ⟨72275, by rfl⟩) R144551
theorem R161929 : Reach 161929 := rs (se 2 (by rfl) ⟨60723, by rfl⟩) R121447
theorem R5306633 : Reach 5306633 := rs (se 2 (by rfl) ⟨1989987, by rfl⟩) R3979975
theorem R163433 : Reach 163433 := rs (se 2 (by rfl) ⟨61287, by rfl⟩) R122575
theorem R11602439 : Reach 11602439 := rs (se 1 (by rfl) ⟨8701829, by rfl⟩) R17403659
theorem R1743913 : Reach 1743913 := rs (se 2 (by rfl) ⟨653967, by rfl⟩) R1307935
theorem R107831 : Reach 107831 := rs (se 1 (by rfl) ⟨80873, by rfl⟩) R161747
theorem R108955 : Reach 108955 := rs (se 1 (by rfl) ⟨81716, by rfl⟩) R163433
theorem R241289 : Reach 241289 := rs (se 2 (by rfl) ⟨90483, by rfl⟩) R180967
theorem R442013 : Reach 442013 := rs (se 3 (by rfl) ⟨82877, by rfl⟩) R165755
theorem R1425377 : Reach 1425377 := rs (se 2 (by rfl) ⟨534516, by rfl⟩) R1069033
theorem R83803 : Reach 83803 := rs (se 1 (by rfl) ⟨62852, by rfl⟩) R125705
theorem R215905 : Reach 215905 := rs (se 2 (by rfl) ⟨80964, by rfl⟩) R161929
theorem R85095 : Reach 85095 := rs (se 1 (by rfl) ⟨63821, by rfl⟩) R127643
theorem R220699 : Reach 220699 := rs (se 1 (by rfl) ⟨165524, by rfl⟩) R331049
theorem R189287 : Reach 189287 := rs (se 1 (by rfl) ⟨141965, by rfl⟩) R283931
theorem R321383 : Reach 321383 := rs (se 1 (by rfl) ⟨241037, by rfl⟩) R482075
theorem R125087 : Reach 125087 := rs (se 1 (by rfl) ⟨93815, by rfl⟩) R187631
theorem R651239 : Reach 651239 := rs (se 1 (by rfl) ⟨488429, by rfl⟩) R976859
theorem R127871 : Reach 127871 := rs (se 1 (by rfl) ⟨95903, by rfl⟩) R191807
theorem R292031 : Reach 292031 := rs (se 1 (by rfl) ⟨219023, by rfl⟩) R438047
theorem R128489 : Reach 128489 := rs (se 2 (by rfl) ⟨48183, by rfl⟩) R96367
theorem R162415 : Reach 162415 := rs (se 1 (by rfl) ⟨121811, by rfl⟩) R243623
theorem R3537755 : Reach 3537755 := rs (se 1 (by rfl) ⟨2653316, by rfl⟩) R5306633
theorem R7734959 : Reach 7734959 := rs (se 1 (by rfl) ⟨5801219, by rfl⟩) R11602439
theorem R434159 : Reach 434159 := rs (se 1 (by rfl) ⟨325619, by rfl⟩) R651239
theorem R145273 : Reach 145273 := rs (se 2 (by rfl) ⟨54477, by rfl⟩) R108955
theorem R214255 : Reach 214255 := rs (se 1 (by rfl) ⟨160691, by rfl⟩) R321383
theorem R83391 : Reach 83391 := rs (se 1 (by rfl) ⟨62543, by rfl⟩) R125087
theorem R85247 : Reach 85247 := rs (se 1 (by rfl) ⟨63935, by rfl⟩) R127871
theorem R216553 : Reach 216553 := rs (se 2 (by rfl) ⟨81207, by rfl⟩) R162415
theorem R85659 : Reach 85659 := rs (se 1 (by rfl) ⟨64244, by rfl⟩) R128489
theorem R287549 : Reach 287549 := rs (se 3 (by rfl) ⟨53915, by rfl⟩) R107831
theorem R287873 : Reach 287873 := rs (se 2 (by rfl) ⟨107952, by rfl⟩) R215905
theorem R126191 : Reach 126191 := rs (se 1 (by rfl) ⟨94643, by rfl⟩) R189287
theorem R4714805 : Reach 4714805 := rs (se 5 (by rfl) ⟨221006, by rfl⟩) R442013
theorem R160859 : Reach 160859 := rs (se 1 (by rfl) ⟨120644, by rfl⟩) R241289
theorem R194687 : Reach 194687 := rs (se 1 (by rfl) ⟨146015, by rfl⟩) R292031
theorem R2325217 : Reach 2325217 := rs (se 2 (by rfl) ⟨871956, by rfl⟩) R1743913
theorem R2358503 : Reach 2358503 := rs (se 1 (by rfl) ⟨1768877, by rfl⟩) R3537755
theorem R294265 : Reach 294265 := rs (se 2 (by rfl) ⟨110349, by rfl⟩) R220699
theorem R3801005 : Reach 3801005 := rs (se 3 (by rfl) ⟨712688, by rfl⟩) R1425377
theorem R107239 : Reach 107239 := rs (se 1 (by rfl) ⟨80429, by rfl⟩) R160859
theorem R2534003 : Reach 2534003 := rs (se 1 (by rfl) ⟨1900502, by rfl⟩) R3801005
theorem R5156639 : Reach 5156639 := rs (se 1 (by rfl) ⟨3867479, by rfl⟩) R7734959
theorem R84127 : Reach 84127 := rs (se 1 (by rfl) ⟨63095, by rfl⟩) R126191
theorem R3100289 : Reach 3100289 := rs (se 2 (by rfl) ⟨1162608, by rfl⟩) R2325217
theorem R12572813 : Reach 12572813 := rs (se 3 (by rfl) ⟨2357402, by rfl⟩) R4714805
theorem R288737 : Reach 288737 := rs (se 2 (by rfl) ⟨108276, by rfl⟩) R216553
theorem R289439 : Reach 289439 := rs (se 1 (by rfl) ⟨217079, by rfl⟩) R434159
theorem R191699 : Reach 191699 := rs (se 1 (by rfl) ⟨143774, by rfl⟩) R287549
theorem R191915 : Reach 191915 := rs (se 1 (by rfl) ⟨143936, by rfl⟩) R287873
theorem R1142693 : Reach 1142693 := rs (se 4 (by rfl) ⟨107127, by rfl⟩) R214255
theorem R193697 : Reach 193697 := rs (se 2 (by rfl) ⟨72636, by rfl⟩) R145273
theorem R129791 : Reach 129791 := rs (se 1 (by rfl) ⟨97343, by rfl⟩) R194687
theorem R392353 : Reach 392353 := rs (se 2 (by rfl) ⟨147132, by rfl⟩) R294265
theorem R1572335 : Reach 1572335 := rs (se 1 (by rfl) ⟨1179251, by rfl⟩) R2358503
theorem R761795 : Reach 761795 := rs (se 1 (by rfl) ⟨571346, by rfl⟩) R1142693
theorem R8267437 : Reach 8267437 := rs (se 3 (by rfl) ⟨1550144, by rfl⟩) R3100289
theorem R142985 : Reach 142985 := rs (se 2 (by rfl) ⟨53619, by rfl⟩) R107239
theorem R1689335 : Reach 1689335 := rs (se 1 (by rfl) ⟨1267001, by rfl⟩) R2534003
theorem R86527 : Reach 86527 := rs (se 1 (by rfl) ⟨64895, by rfl⟩) R129791
theorem R8381875 : Reach 8381875 := rs (se 1 (by rfl) ⟨6286406, by rfl⟩) R12572813
theorem R2092549 : Reach 2092549 := rs (se 4 (by rfl) ⟨196176, by rfl⟩) R392353
theorem R192491 : Reach 192491 := rs (se 1 (by rfl) ⟨144368, by rfl⟩) R288737
theorem R192959 : Reach 192959 := rs (se 1 (by rfl) ⟨144719, by rfl⟩) R289439
theorem R127799 : Reach 127799 := rs (se 1 (by rfl) ⟨95849, by rfl⟩) R191699
theorem R127943 : Reach 127943 := rs (se 1 (by rfl) ⟨95957, by rfl⟩) R191915
theorem R3437759 : Reach 3437759 := rs (se 1 (by rfl) ⟨2578319, by rfl⟩) R5156639
theorem R129131 : Reach 129131 := rs (se 1 (by rfl) ⟨96848, by rfl⟩) R193697
theorem R1048223 : Reach 1048223 := rs (se 1 (by rfl) ⟨786167, by rfl⟩) R1572335
theorem R11175833 : Reach 11175833 := rs (se 2 (by rfl) ⟨4190937, by rfl⟩) R8381875
theorem R2790065 : Reach 2790065 := rs (se 2 (by rfl) ⟨1046274, by rfl⟩) R2092549
theorem R698815 : Reach 698815 := rs (se 1 (by rfl) ⟨524111, by rfl⟩) R1048223
theorem R1126223 : Reach 1126223 := rs (se 1 (by rfl) ⟨844667, by rfl⟩) R1689335
theorem R507863 : Reach 507863 := rs (se 1 (by rfl) ⟨380897, by rfl⟩) R761795
theorem R85199 : Reach 85199 := rs (se 1 (by rfl) ⟨63899, by rfl⟩) R127799
theorem R85295 : Reach 85295 := rs (se 1 (by rfl) ⟨63971, by rfl⟩) R127943
theorem R44092997 : Reach 44092997 := rs (se 4 (by rfl) ⟨4133718, by rfl⟩) R8267437
theorem R86087 : Reach 86087 := rs (se 1 (by rfl) ⟨64565, by rfl⟩) R129131
theorem R9167357 : Reach 9167357 := rs (se 3 (by rfl) ⟨1718879, by rfl⟩) R3437759
theorem R95323 : Reach 95323 := rs (se 1 (by rfl) ⟨71492, by rfl⟩) R142985
theorem R128327 : Reach 128327 := rs (se 1 (by rfl) ⟨96245, by rfl⟩) R192491
theorem R128639 : Reach 128639 := rs (se 1 (by rfl) ⟨96479, by rfl⟩) R192959
theorem R229565 : Reach 229565 := rs (se 3 (by rfl) ⟨43043, by rfl⟩) R86087
theorem R7440173 : Reach 7440173 := rs (se 3 (by rfl) ⟨1395032, by rfl⟩) R2790065
theorem R29395331 : Reach 29395331 := rs (se 1 (by rfl) ⟨22046498, by rfl⟩) R44092997
theorem R338575 : Reach 338575 := rs (se 1 (by rfl) ⟨253931, by rfl⟩) R507863
theorem R7450555 : Reach 7450555 := rs (se 1 (by rfl) ⟨5587916, by rfl⟩) R11175833
theorem R931753 : Reach 931753 := rs (se 2 (by rfl) ⟨349407, by rfl⟩) R698815
theorem R6111571 : Reach 6111571 := rs (se 1 (by rfl) ⟨4583678, by rfl⟩) R9167357
theorem R85551 : Reach 85551 := rs (se 1 (by rfl) ⟨64163, by rfl⟩) R128327
theorem R85759 : Reach 85759 := rs (se 1 (by rfl) ⟨64319, by rfl⟩) R128639
theorem R127097 : Reach 127097 := rs (se 2 (by rfl) ⟨47661, by rfl⟩) R95323
theorem R750815 : Reach 750815 := rs (se 1 (by rfl) ⟨563111, by rfl⟩) R1126223
theorem R19596887 : Reach 19596887 := rs (se 1 (by rfl) ⟨14697665, by rfl⟩) R29395331
theorem R9934073 : Reach 9934073 := rs (se 2 (by rfl) ⟨3725277, by rfl⟩) R7450555
theorem R500543 : Reach 500543 := rs (se 1 (by rfl) ⟨375407, by rfl⟩) R750815
theorem R4960115 : Reach 4960115 := rs (se 1 (by rfl) ⟨3720086, by rfl⟩) R7440173
theorem R84731 : Reach 84731 := rs (se 1 (by rfl) ⟨63548, by rfl⟩) R127097
theorem R8148761 : Reach 8148761 := rs (se 2 (by rfl) ⟨3055785, by rfl⟩) R6111571
theorem R612173 : Reach 612173 := rs (se 3 (by rfl) ⟨114782, by rfl⟩) R229565
theorem R451433 : Reach 451433 := rs (se 2 (by rfl) ⟨169287, by rfl⟩) R338575
theorem R1242337 : Reach 1242337 := rs (se 2 (by rfl) ⟨465876, by rfl⟩) R931753
theorem R6622715 : Reach 6622715 := rs (se 1 (by rfl) ⟨4967036, by rfl⟩) R9934073
theorem R333695 : Reach 333695 := rs (se 1 (by rfl) ⟨250271, by rfl⟩) R500543
theorem R408115 : Reach 408115 := rs (se 1 (by rfl) ⟨306086, by rfl⟩) R612173
theorem R1656449 : Reach 1656449 := rs (se 2 (by rfl) ⟨621168, by rfl⟩) R1242337
theorem R13064591 : Reach 13064591 := rs (se 1 (by rfl) ⟨9798443, by rfl⟩) R19596887
theorem R1203821 : Reach 1203821 := rs (se 3 (by rfl) ⟨225716, by rfl⟩) R451433
theorem R5432507 : Reach 5432507 := rs (se 1 (by rfl) ⟨4074380, by rfl⟩) R8148761
theorem R3306743 : Reach 3306743 := rs (se 1 (by rfl) ⟨2480057, by rfl⟩) R4960115
theorem R2204495 : Reach 2204495 := rs (se 1 (by rfl) ⟨1653371, by rfl⟩) R3306743
theorem R802547 : Reach 802547 := rs (se 1 (by rfl) ⟨601910, by rfl⟩) R1203821
theorem R3621671 : Reach 3621671 := rs (se 1 (by rfl) ⟨2716253, by rfl⟩) R5432507
theorem R544153 : Reach 544153 := rs (se 2 (by rfl) ⟨204057, by rfl⟩) R408115
theorem R1104299 : Reach 1104299 := rs (se 1 (by rfl) ⟨828224, by rfl⟩) R1656449
theorem R4415143 : Reach 4415143 := rs (se 1 (by rfl) ⟨3311357, by rfl⟩) R6622715
theorem R222463 : Reach 222463 := rs (se 1 (by rfl) ⟨166847, by rfl⟩) R333695
theorem R8709727 : Reach 8709727 := rs (se 1 (by rfl) ⟨6532295, by rfl⟩) R13064591
theorem R296617 : Reach 296617 := rs (se 2 (by rfl) ⟨111231, by rfl⟩) R222463
theorem R725537 : Reach 725537 := rs (se 2 (by rfl) ⟨272076, by rfl⟩) R544153
theorem R535031 : Reach 535031 := rs (se 1 (by rfl) ⟨401273, by rfl⟩) R802547
theorem R11612969 : Reach 11612969 := rs (se 2 (by rfl) ⟨4354863, by rfl⟩) R8709727
theorem R736199 : Reach 736199 := rs (se 1 (by rfl) ⟨552149, by rfl⟩) R1104299
theorem R5886857 : Reach 5886857 := rs (se 2 (by rfl) ⟨2207571, by rfl⟩) R4415143
theorem R2414447 : Reach 2414447 := rs (se 1 (by rfl) ⟨1810835, by rfl⟩) R3621671
theorem R1469663 : Reach 1469663 := rs (se 1 (by rfl) ⟨1102247, by rfl⟩) R2204495
theorem R395489 : Reach 395489 := rs (se 2 (by rfl) ⟨148308, by rfl⟩) R296617
theorem R1609631 : Reach 1609631 := rs (se 1 (by rfl) ⟨1207223, by rfl⟩) R2414447
theorem R7741979 : Reach 7741979 := rs (se 1 (by rfl) ⟨5806484, by rfl⟩) R11612969
theorem R483691 : Reach 483691 := rs (se 1 (by rfl) ⟨362768, by rfl⟩) R725537
theorem R3924571 : Reach 3924571 := rs (se 1 (by rfl) ⟨2943428, by rfl⟩) R5886857
theorem R356687 : Reach 356687 := rs (se 1 (by rfl) ⟨267515, by rfl⟩) R535031
theorem R979775 : Reach 979775 := rs (se 1 (by rfl) ⟨734831, by rfl⟩) R1469663
theorem R490799 : Reach 490799 := rs (se 1 (by rfl) ⟨368099, by rfl⟩) R736199
theorem R1054637 : Reach 1054637 := rs (se 3 (by rfl) ⟨197744, by rfl⟩) R395489
theorem R237791 : Reach 237791 := rs (se 1 (by rfl) ⟨178343, by rfl⟩) R356687
theorem R5161319 : Reach 5161319 := rs (se 1 (by rfl) ⟨3870989, by rfl⟩) R7741979
theorem R644921 : Reach 644921 := rs (se 2 (by rfl) ⟨241845, by rfl⟩) R483691
theorem R5232761 : Reach 5232761 := rs (se 2 (by rfl) ⟨1962285, by rfl⟩) R3924571
theorem R1073087 : Reach 1073087 := rs (se 1 (by rfl) ⟨804815, by rfl⟩) R1609631
theorem R653183 : Reach 653183 := rs (se 1 (by rfl) ⟨489887, by rfl⟩) R979775
theorem R327199 : Reach 327199 := rs (se 1 (by rfl) ⟨245399, by rfl⟩) R490799
theorem R3440879 : Reach 3440879 := rs (se 1 (by rfl) ⟨2580659, by rfl⟩) R5161319
theorem R429947 : Reach 429947 := rs (se 1 (by rfl) ⟨322460, by rfl⟩) R644921
theorem R435455 : Reach 435455 := rs (se 1 (by rfl) ⟨326591, by rfl⟩) R653183
theorem R436265 : Reach 436265 := rs (se 2 (by rfl) ⟨163599, by rfl⟩) R327199
theorem R703091 : Reach 703091 := rs (se 1 (by rfl) ⟨527318, by rfl⟩) R1054637
theorem R3488507 : Reach 3488507 := rs (se 1 (by rfl) ⟨2616380, by rfl⟩) R5232761
theorem R715391 : Reach 715391 := rs (se 1 (by rfl) ⟨536543, by rfl⟩) R1073087
theorem R158527 : Reach 158527 := rs (se 1 (by rfl) ⟨118895, by rfl⟩) R237791
theorem R2293919 : Reach 2293919 := rs (se 1 (by rfl) ⟨1720439, by rfl⟩) R3440879
theorem R1874909 : Reach 1874909 := rs (se 3 (by rfl) ⟨351545, by rfl⟩) R703091
theorem R211369 : Reach 211369 := rs (se 2 (by rfl) ⟨79263, by rfl⟩) R158527
theorem R476927 : Reach 476927 := rs (se 1 (by rfl) ⟨357695, by rfl⟩) R715391
theorem R286631 : Reach 286631 := rs (se 1 (by rfl) ⟨214973, by rfl⟩) R429947
theorem R290303 : Reach 290303 := rs (se 1 (by rfl) ⟨217727, by rfl⟩) R435455
theorem R290843 : Reach 290843 := rs (se 1 (by rfl) ⟨218132, by rfl⟩) R436265
theorem R2325671 : Reach 2325671 := rs (se 1 (by rfl) ⟨1744253, by rfl⟩) R3488507
theorem R1249939 : Reach 1249939 := rs (se 1 (by rfl) ⟨937454, by rfl⟩) R1874909
theorem R1550447 : Reach 1550447 := rs (se 1 (by rfl) ⟨1162835, by rfl⟩) R2325671
theorem R281825 : Reach 281825 := rs (se 2 (by rfl) ⟨105684, by rfl⟩) R211369
theorem R1529279 : Reach 1529279 := rs (se 1 (by rfl) ⟨1146959, by rfl⟩) R2293919
theorem R317951 : Reach 317951 := rs (se 1 (by rfl) ⟨238463, by rfl⟩) R476927
theorem R191087 : Reach 191087 := rs (se 1 (by rfl) ⟨143315, by rfl⟩) R286631
theorem R193535 : Reach 193535 := rs (se 1 (by rfl) ⟨145151, by rfl⟩) R290303
theorem R193895 : Reach 193895 := rs (se 1 (by rfl) ⟨145421, by rfl⟩) R290843
theorem R1019519 : Reach 1019519 := rs (se 1 (by rfl) ⟨764639, by rfl⟩) R1529279
theorem R211967 : Reach 211967 := rs (se 1 (by rfl) ⟨158975, by rfl⟩) R317951
theorem R1033631 : Reach 1033631 := rs (se 1 (by rfl) ⟨775223, by rfl⟩) R1550447
theorem R187883 : Reach 187883 := rs (se 1 (by rfl) ⟨140912, by rfl⟩) R281825
theorem R1666585 : Reach 1666585 := rs (se 2 (by rfl) ⟨624969, by rfl⟩) R1249939
theorem R127391 : Reach 127391 := rs (se 1 (by rfl) ⟨95543, by rfl⟩) R191087
theorem R129023 : Reach 129023 := rs (se 1 (by rfl) ⟨96767, by rfl⟩) R193535
theorem R129263 : Reach 129263 := rs (se 1 (by rfl) ⟨96947, by rfl⟩) R193895
theorem R689087 : Reach 689087 := rs (se 1 (by rfl) ⟨516815, by rfl⟩) R1033631
theorem R141311 : Reach 141311 := rs (se 1 (by rfl) ⟨105983, by rfl⟩) R211967
theorem R84927 : Reach 84927 := rs (se 1 (by rfl) ⟨63695, by rfl⟩) R127391
theorem R86015 : Reach 86015 := rs (se 1 (by rfl) ⟨64511, by rfl⟩) R129023
theorem R86175 : Reach 86175 := rs (se 1 (by rfl) ⟨64631, by rfl⟩) R129263
theorem R679679 : Reach 679679 := rs (se 1 (by rfl) ⟨509759, by rfl⟩) R1019519
theorem R2222113 : Reach 2222113 := rs (se 2 (by rfl) ⟨833292, by rfl⟩) R1666585
theorem R125255 : Reach 125255 := rs (se 1 (by rfl) ⟨93941, by rfl⟩) R187883
theorem R459391 : Reach 459391 := rs (se 1 (by rfl) ⟨344543, by rfl⟩) R689087
theorem R2962817 : Reach 2962817 := rs (se 2 (by rfl) ⟨1111056, by rfl⟩) R2222113
theorem R83503 : Reach 83503 := rs (se 1 (by rfl) ⟨62627, by rfl⟩) R125255
theorem R453119 : Reach 453119 := rs (se 1 (by rfl) ⟨339839, by rfl⟩) R679679
theorem R94207 : Reach 94207 := rs (se 1 (by rfl) ⟨70655, by rfl⟩) R141311
theorem R1975211 : Reach 1975211 := rs (se 1 (by rfl) ⟨1481408, by rfl⟩) R2962817
theorem R612521 : Reach 612521 := rs (se 2 (by rfl) ⟨229695, by rfl⟩) R459391
theorem R125609 : Reach 125609 := rs (se 2 (by rfl) ⟨47103, by rfl⟩) R94207
theorem R1208317 : Reach 1208317 := rs (se 3 (by rfl) ⟨226559, by rfl⟩) R453119
theorem R1611089 : Reach 1611089 := rs (se 2 (by rfl) ⟨604158, by rfl⟩) R1208317
theorem R1316807 : Reach 1316807 := rs (se 1 (by rfl) ⟨987605, by rfl⟩) R1975211
theorem R408347 : Reach 408347 := rs (se 1 (by rfl) ⟨306260, by rfl⟩) R612521
theorem R83739 : Reach 83739 := rs (se 1 (by rfl) ⟨62804, by rfl⟩) R125609
theorem R272231 : Reach 272231 := rs (se 1 (by rfl) ⟨204173, by rfl⟩) R408347
theorem R1074059 : Reach 1074059 := rs (se 1 (by rfl) ⟨805544, by rfl⟩) R1611089
theorem R877871 : Reach 877871 := rs (se 1 (by rfl) ⟨658403, by rfl⟩) R1316807
theorem R181487 : Reach 181487 := rs (se 1 (by rfl) ⟨136115, by rfl⟩) R272231
theorem R716039 : Reach 716039 := rs (se 1 (by rfl) ⟨537029, by rfl⟩) R1074059
theorem R585247 : Reach 585247 := rs (se 1 (by rfl) ⟨438935, by rfl⟩) R877871
theorem R477359 : Reach 477359 := rs (se 1 (by rfl) ⟨358019, by rfl⟩) R716039
theorem R483965 : Reach 483965 := rs (se 3 (by rfl) ⟨90743, by rfl⟩) R181487
theorem R780329 : Reach 780329 := rs (se 2 (by rfl) ⟨292623, by rfl⟩) R585247
theorem R318239 : Reach 318239 := rs (se 1 (by rfl) ⟨238679, by rfl⟩) R477359
theorem R322643 : Reach 322643 := rs (se 1 (by rfl) ⟨241982, by rfl⟩) R483965
theorem R520219 : Reach 520219 := rs (se 1 (by rfl) ⟨390164, by rfl⟩) R780329
theorem R693625 : Reach 693625 := rs (se 2 (by rfl) ⟨260109, by rfl⟩) R520219
theorem R212159 : Reach 212159 := rs (se 1 (by rfl) ⟨159119, by rfl⟩) R318239
theorem R215095 : Reach 215095 := rs (se 1 (by rfl) ⟨161321, by rfl⟩) R322643
theorem R924833 : Reach 924833 := rs (se 2 (by rfl) ⟨346812, by rfl⟩) R693625
theorem R141439 : Reach 141439 := rs (se 1 (by rfl) ⟨106079, by rfl⟩) R212159
theorem R286793 : Reach 286793 := rs (se 2 (by rfl) ⟨107547, by rfl⟩) R215095
theorem R188585 : Reach 188585 := rs (se 2 (by rfl) ⟨70719, by rfl⟩) R141439
theorem R616555 : Reach 616555 := rs (se 1 (by rfl) ⟨462416, by rfl⟩) R924833
theorem R191195 : Reach 191195 := rs (se 1 (by rfl) ⟨143396, by rfl⟩) R286793
theorem R822073 : Reach 822073 := rs (se 2 (by rfl) ⟨308277, by rfl⟩) R616555
theorem R125723 : Reach 125723 := rs (se 1 (by rfl) ⟨94292, by rfl⟩) R188585
theorem R127463 : Reach 127463 := rs (se 1 (by rfl) ⟨95597, by rfl⟩) R191195
theorem R1096097 : Reach 1096097 := rs (se 2 (by rfl) ⟨411036, by rfl⟩) R822073
theorem R83815 : Reach 83815 := rs (se 1 (by rfl) ⟨62861, by rfl⟩) R125723
theorem R84975 : Reach 84975 := rs (se 1 (by rfl) ⟨63731, by rfl⟩) R127463
theorem R11691701 : Reach 11691701 := rs (se 5 (by rfl) ⟨548048, by rfl⟩) R1096097
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
theorem R320395 : Reach 320395 := rs (se 1 (by rfl) ⟨240296, by rfl⟩) R480593
theorem R427193 : Reach 427193 := rs (se 2 (by rfl) ⟨160197, by rfl⟩) R320395
theorem R284795 : Reach 284795 := rs (se 1 (by rfl) ⟨213596, by rfl⟩) R427193
theorem R189863 : Reach 189863 := rs (se 1 (by rfl) ⟨142397, by rfl⟩) R284795
theorem R126575 : Reach 126575 := rs (se 1 (by rfl) ⟨94931, by rfl⟩) R189863
theorem R84383 : Reach 84383 := rs (se 1 (by rfl) ⟨63287, by rfl⟩) R126575

theorem C0 (j : ℕ) (h1 : 41564 ≤ j) (h2 : j ≤ 42263) : Reach (2 * j + 1) := by
  interval_cases j
  · exact R83129
  · exact R83131
  · exact R83133
  · exact R83135
  · exact R83137
  · exact R83139
  · exact R83141
  · exact R83143
  · exact R83145
  · exact R83147
  · exact R83149
  · exact R83151
  · exact R83153
  · exact R83155
  · exact R83157
  · exact R83159
  · exact R83161
  · exact R83163
  · exact R83165
  · exact R83167
  · exact R83169
  · exact R83171
  · exact R83173
  · exact R83175
  · exact R83177
  · exact R83179
  · exact R83181
  · exact R83183
  · exact R83185
  · exact R83187
  · exact R83189
  · exact R83191
  · exact R83193
  · exact R83195
  · exact R83197
  · exact R83199
  · exact R83201
  · exact R83203
  · exact R83205
  · exact R83207
  · exact R83209
  · exact R83211
  · exact R83213
  · exact R83215
  · exact R83217
  · exact R83219
  · exact R83221
  · exact R83223
  · exact R83225
  · exact R83227
  · exact R83229
  · exact R83231
  · exact R83233
  · exact R83235
  · exact R83237
  · exact R83239
  · exact R83241
  · exact R83243
  · exact R83245
  · exact R83247
  · exact R83249
  · exact R83251
  · exact R83253
  · exact R83255
  · exact R83257
  · exact R83259
  · exact R83261
  · exact R83263
  · exact R83265
  · exact R83267
  · exact R83269
  · exact R83271
  · exact R83273
  · exact R83275
  · exact R83277
  · exact R83279
  · exact R83281
  · exact R83283
  · exact R83285
  · exact R83287
  · exact R83289
  · exact R83291
  · exact R83293
  · exact R83295
  · exact R83297
  · exact R83299
  · exact R83301
  · exact R83303
  · exact R83305
  · exact R83307
  · exact R83309
  · exact R83311
  · exact R83313
  · exact R83315
  · exact R83317
  · exact R83319
  · exact R83321
  · exact R83323
  · exact R83325
  · exact R83327
  · exact R83329
  · exact R83331
  · exact R83333
  · exact R83335
  · exact R83337
  · exact R83339
  · exact R83341
  · exact R83343
  · exact R83345
  · exact R83347
  · exact R83349
  · exact R83351
  · exact R83353
  · exact R83355
  · exact R83357
  · exact R83359
  · exact R83361
  · exact R83363
  · exact R83365
  · exact R83367
  · exact R83369
  · exact R83371
  · exact R83373
  · exact R83375
  · exact R83377
  · exact R83379
  · exact R83381
  · exact R83383
  · exact R83385
  · exact R83387
  · exact R83389
  · exact R83391
  · exact R83393
  · exact R83395
  · exact R83397
  · exact R83399
  · exact R83401
  · exact R83403
  · exact R83405
  · exact R83407
  · exact R83409
  · exact R83411
  · exact R83413
  · exact R83415
  · exact R83417
  · exact R83419
  · exact R83421
  · exact R83423
  · exact R83425
  · exact R83427
  · exact R83429
  · exact R83431
  · exact R83433
  · exact R83435
  · exact R83437
  · exact R83439
  · exact R83441
  · exact R83443
  · exact R83445
  · exact R83447
  · exact R83449
  · exact R83451
  · exact R83453
  · exact R83455
  · exact R83457
  · exact R83459
  · exact R83461
  · exact R83463
  · exact R83465
  · exact R83467
  · exact R83469
  · exact R83471
  · exact R83473
  · exact R83475
  · exact R83477
  · exact R83479
  · exact R83481
  · exact R83483
  · exact R83485
  · exact R83487
  · exact R83489
  · exact R83491
  · exact R83493
  · exact R83495
  · exact R83497
  · exact R83499
  · exact R83501
  · exact R83503
  · exact R83505
  · exact R83507
  · exact R83509
  · exact R83511
  · exact R83513
  · exact R83515
  · exact R83517
  · exact R83519
  · exact R83521
  · exact R83523
  · exact R83525
  · exact R83527
  · exact R83529
  · exact R83531
  · exact R83533
  · exact R83535
  · exact R83537
  · exact R83539
  · exact R83541
  · exact R83543
  · exact R83545
  · exact R83547
  · exact R83549
  · exact R83551
  · exact R83553
  · exact R83555
  · exact R83557
  · exact R83559
  · exact R83561
  · exact R83563
  · exact R83565
  · exact R83567
  · exact R83569
  · exact R83571
  · exact R83573
  · exact R83575
  · exact R83577
  · exact R83579
  · exact R83581
  · exact R83583
  · exact R83585
  · exact R83587
  · exact R83589
  · exact R83591
  · exact R83593
  · exact R83595
  · exact R83597
  · exact R83599
  · exact R83601
  · exact R83603
  · exact R83605
  · exact R83607
  · exact R83609
  · exact R83611
  · exact R83613
  · exact R83615
  · exact R83617
  · exact R83619
  · exact R83621
  · exact R83623
  · exact R83625
  · exact R83627
  · exact R83629
  · exact R83631
  · exact R83633
  · exact R83635
  · exact R83637
  · exact R83639
  · exact R83641
  · exact R83643
  · exact R83645
  · exact R83647
  · exact R83649
  · exact R83651
  · exact R83653
  · exact R83655
  · exact R83657
  · exact R83659
  · exact R83661
  · exact R83663
  · exact R83665
  · exact R83667
  · exact R83669
  · exact R83671
  · exact R83673
  · exact R83675
  · exact R83677
  · exact R83679
  · exact R83681
  · exact R83683
  · exact R83685
  · exact R83687
  · exact R83689
  · exact R83691
  · exact R83693
  · exact R83695
  · exact R83697
  · exact R83699
  · exact R83701
  · exact R83703
  · exact R83705
  · exact R83707
  · exact R83709
  · exact R83711
  · exact R83713
  · exact R83715
  · exact R83717
  · exact R83719
  · exact R83721
  · exact R83723
  · exact R83725
  · exact R83727
  · exact R83729
  · exact R83731
  · exact R83733
  · exact R83735
  · exact R83737
  · exact R83739
  · exact R83741
  · exact R83743
  · exact R83745
  · exact R83747
  · exact R83749
  · exact R83751
  · exact R83753
  · exact R83755
  · exact R83757
  · exact R83759
  · exact R83761
  · exact R83763
  · exact R83765
  · exact R83767
  · exact R83769
  · exact R83771
  · exact R83773
  · exact R83775
  · exact R83777
  · exact R83779
  · exact R83781
  · exact R83783
  · exact R83785
  · exact R83787
  · exact R83789
  · exact R83791
  · exact R83793
  · exact R83795
  · exact R83797
  · exact R83799
  · exact R83801
  · exact R83803
  · exact R83805
  · exact R83807
  · exact R83809
  · exact R83811
  · exact R83813
  · exact R83815
  · exact R83817
  · exact R83819
  · exact R83821
  · exact R83823
  · exact R83825
  · exact R83827
  · exact R83829
  · exact R83831
  · exact R83833
  · exact R83835
  · exact R83837
  · exact R83839
  · exact R83841
  · exact R83843
  · exact R83845
  · exact R83847
  · exact R83849
  · exact R83851
  · exact R83853
  · exact R83855
  · exact R83857
  · exact R83859
  · exact R83861
  · exact R83863
  · exact R83865
  · exact R83867
  · exact R83869
  · exact R83871
  · exact R83873
  · exact R83875
  · exact R83877
  · exact R83879
  · exact R83881
  · exact R83883
  · exact R83885
  · exact R83887
  · exact R83889
  · exact R83891
  · exact R83893
  · exact R83895
  · exact R83897
  · exact R83899
  · exact R83901
  · exact R83903
  · exact R83905
  · exact R83907
  · exact R83909
  · exact R83911
  · exact R83913
  · exact R83915
  · exact R83917
  · exact R83919
  · exact R83921
  · exact R83923
  · exact R83925
  · exact R83927
  · exact R83929
  · exact R83931
  · exact R83933
  · exact R83935
  · exact R83937
  · exact R83939
  · exact R83941
  · exact R83943
  · exact R83945
  · exact R83947
  · exact R83949
  · exact R83951
  · exact R83953
  · exact R83955
  · exact R83957
  · exact R83959
  · exact R83961
  · exact R83963
  · exact R83965
  · exact R83967
  · exact R83969
  · exact R83971
  · exact R83973
  · exact R83975
  · exact R83977
  · exact R83979
  · exact R83981
  · exact R83983
  · exact R83985
  · exact R83987
  · exact R83989
  · exact R83991
  · exact R83993
  · exact R83995
  · exact R83997
  · exact R83999
  · exact R84001
  · exact R84003
  · exact R84005
  · exact R84007
  · exact R84009
  · exact R84011
  · exact R84013
  · exact R84015
  · exact R84017
  · exact R84019
  · exact R84021
  · exact R84023
  · exact R84025
  · exact R84027
  · exact R84029
  · exact R84031
  · exact R84033
  · exact R84035
  · exact R84037
  · exact R84039
  · exact R84041
  · exact R84043
  · exact R84045
  · exact R84047
  · exact R84049
  · exact R84051
  · exact R84053
  · exact R84055
  · exact R84057
  · exact R84059
  · exact R84061
  · exact R84063
  · exact R84065
  · exact R84067
  · exact R84069
  · exact R84071
  · exact R84073
  · exact R84075
  · exact R84077
  · exact R84079
  · exact R84081
  · exact R84083
  · exact R84085
  · exact R84087
  · exact R84089
  · exact R84091
  · exact R84093
  · exact R84095
  · exact R84097
  · exact R84099
  · exact R84101
  · exact R84103
  · exact R84105
  · exact R84107
  · exact R84109
  · exact R84111
  · exact R84113
  · exact R84115
  · exact R84117
  · exact R84119
  · exact R84121
  · exact R84123
  · exact R84125
  · exact R84127
  · exact R84129
  · exact R84131
  · exact R84133
  · exact R84135
  · exact R84137
  · exact R84139
  · exact R84141
  · exact R84143
  · exact R84145
  · exact R84147
  · exact R84149
  · exact R84151
  · exact R84153
  · exact R84155
  · exact R84157
  · exact R84159
  · exact R84161
  · exact R84163
  · exact R84165
  · exact R84167
  · exact R84169
  · exact R84171
  · exact R84173
  · exact R84175
  · exact R84177
  · exact R84179
  · exact R84181
  · exact R84183
  · exact R84185
  · exact R84187
  · exact R84189
  · exact R84191
  · exact R84193
  · exact R84195
  · exact R84197
  · exact R84199
  · exact R84201
  · exact R84203
  · exact R84205
  · exact R84207
  · exact R84209
  · exact R84211
  · exact R84213
  · exact R84215
  · exact R84217
  · exact R84219
  · exact R84221
  · exact R84223
  · exact R84225
  · exact R84227
  · exact R84229
  · exact R84231
  · exact R84233
  · exact R84235
  · exact R84237
  · exact R84239
  · exact R84241
  · exact R84243
  · exact R84245
  · exact R84247
  · exact R84249
  · exact R84251
  · exact R84253
  · exact R84255
  · exact R84257
  · exact R84259
  · exact R84261
  · exact R84263
  · exact R84265
  · exact R84267
  · exact R84269
  · exact R84271
  · exact R84273
  · exact R84275
  · exact R84277
  · exact R84279
  · exact R84281
  · exact R84283
  · exact R84285
  · exact R84287
  · exact R84289
  · exact R84291
  · exact R84293
  · exact R84295
  · exact R84297
  · exact R84299
  · exact R84301
  · exact R84303
  · exact R84305
  · exact R84307
  · exact R84309
  · exact R84311
  · exact R84313
  · exact R84315
  · exact R84317
  · exact R84319
  · exact R84321
  · exact R84323
  · exact R84325
  · exact R84327
  · exact R84329
  · exact R84331
  · exact R84333
  · exact R84335
  · exact R84337
  · exact R84339
  · exact R84341
  · exact R84343
  · exact R84345
  · exact R84347
  · exact R84349
  · exact R84351
  · exact R84353
  · exact R84355
  · exact R84357
  · exact R84359
  · exact R84361
  · exact R84363
  · exact R84365
  · exact R84367
  · exact R84369
  · exact R84371
  · exact R84373
  · exact R84375
  · exact R84377
  · exact R84379
  · exact R84381
  · exact R84383
  · exact R84385
  · exact R84387
  · exact R84389
  · exact R84391
  · exact R84393
  · exact R84395
  · exact R84397
  · exact R84399
  · exact R84401
  · exact R84403
  · exact R84405
  · exact R84407
  · exact R84409
  · exact R84411
  · exact R84413
  · exact R84415
  · exact R84417
  · exact R84419
  · exact R84421
  · exact R84423
  · exact R84425
  · exact R84427
  · exact R84429
  · exact R84431
  · exact R84433
  · exact R84435
  · exact R84437
  · exact R84439
  · exact R84441
  · exact R84443
  · exact R84445
  · exact R84447
  · exact R84449
  · exact R84451
  · exact R84453
  · exact R84455
  · exact R84457
  · exact R84459
  · exact R84461
  · exact R84463
  · exact R84465
  · exact R84467
  · exact R84469
  · exact R84471
  · exact R84473
  · exact R84475
  · exact R84477
  · exact R84479
  · exact R84481
  · exact R84483
  · exact R84485
  · exact R84487
  · exact R84489
  · exact R84491
  · exact R84493
  · exact R84495
  · exact R84497
  · exact R84499
  · exact R84501
  · exact R84503
  · exact R84505
  · exact R84507
  · exact R84509
  · exact R84511
  · exact R84513
  · exact R84515
  · exact R84517
  · exact R84519
  · exact R84521
  · exact R84523
  · exact R84525
  · exact R84527

theorem C1 (j : ℕ) (h1 : 42264 ≤ j) (h2 : j ≤ 42963) : Reach (2 * j + 1) := by
  interval_cases j
  · exact R84529
  · exact R84531
  · exact R84533
  · exact R84535
  · exact R84537
  · exact R84539
  · exact R84541
  · exact R84543
  · exact R84545
  · exact R84547
  · exact R84549
  · exact R84551
  · exact R84553
  · exact R84555
  · exact R84557
  · exact R84559
  · exact R84561
  · exact R84563
  · exact R84565
  · exact R84567
  · exact R84569
  · exact R84571
  · exact R84573
  · exact R84575
  · exact R84577
  · exact R84579
  · exact R84581
  · exact R84583
  · exact R84585
  · exact R84587
  · exact R84589
  · exact R84591
  · exact R84593
  · exact R84595
  · exact R84597
  · exact R84599
  · exact R84601
  · exact R84603
  · exact R84605
  · exact R84607
  · exact R84609
  · exact R84611
  · exact R84613
  · exact R84615
  · exact R84617
  · exact R84619
  · exact R84621
  · exact R84623
  · exact R84625
  · exact R84627
  · exact R84629
  · exact R84631
  · exact R84633
  · exact R84635
  · exact R84637
  · exact R84639
  · exact R84641
  · exact R84643
  · exact R84645
  · exact R84647
  · exact R84649
  · exact R84651
  · exact R84653
  · exact R84655
  · exact R84657
  · exact R84659
  · exact R84661
  · exact R84663
  · exact R84665
  · exact R84667
  · exact R84669
  · exact R84671
  · exact R84673
  · exact R84675
  · exact R84677
  · exact R84679
  · exact R84681
  · exact R84683
  · exact R84685
  · exact R84687
  · exact R84689
  · exact R84691
  · exact R84693
  · exact R84695
  · exact R84697
  · exact R84699
  · exact R84701
  · exact R84703
  · exact R84705
  · exact R84707
  · exact R84709
  · exact R84711
  · exact R84713
  · exact R84715
  · exact R84717
  · exact R84719
  · exact R84721
  · exact R84723
  · exact R84725
  · exact R84727
  · exact R84729
  · exact R84731
  · exact R84733
  · exact R84735
  · exact R84737
  · exact R84739
  · exact R84741
  · exact R84743
  · exact R84745
  · exact R84747
  · exact R84749
  · exact R84751
  · exact R84753
  · exact R84755
  · exact R84757
  · exact R84759
  · exact R84761
  · exact R84763
  · exact R84765
  · exact R84767
  · exact R84769
  · exact R84771
  · exact R84773
  · exact R84775
  · exact R84777
  · exact R84779
  · exact R84781
  · exact R84783
  · exact R84785
  · exact R84787
  · exact R84789
  · exact R84791
  · exact R84793
  · exact R84795
  · exact R84797
  · exact R84799
  · exact R84801
  · exact R84803
  · exact R84805
  · exact R84807
  · exact R84809
  · exact R84811
  · exact R84813
  · exact R84815
  · exact R84817
  · exact R84819
  · exact R84821
  · exact R84823
  · exact R84825
  · exact R84827
  · exact R84829
  · exact R84831
  · exact R84833
  · exact R84835
  · exact R84837
  · exact R84839
  · exact R84841
  · exact R84843
  · exact R84845
  · exact R84847
  · exact R84849
  · exact R84851
  · exact R84853
  · exact R84855
  · exact R84857
  · exact R84859
  · exact R84861
  · exact R84863
  · exact R84865
  · exact R84867
  · exact R84869
  · exact R84871
  · exact R84873
  · exact R84875
  · exact R84877
  · exact R84879
  · exact R84881
  · exact R84883
  · exact R84885
  · exact R84887
  · exact R84889
  · exact R84891
  · exact R84893
  · exact R84895
  · exact R84897
  · exact R84899
  · exact R84901
  · exact R84903
  · exact R84905
  · exact R84907
  · exact R84909
  · exact R84911
  · exact R84913
  · exact R84915
  · exact R84917
  · exact R84919
  · exact R84921
  · exact R84923
  · exact R84925
  · exact R84927
  · exact R84929
  · exact R84931
  · exact R84933
  · exact R84935
  · exact R84937
  · exact R84939
  · exact R84941
  · exact R84943
  · exact R84945
  · exact R84947
  · exact R84949
  · exact R84951
  · exact R84953
  · exact R84955
  · exact R84957
  · exact R84959
  · exact R84961
  · exact R84963
  · exact R84965
  · exact R84967
  · exact R84969
  · exact R84971
  · exact R84973
  · exact R84975
  · exact R84977
  · exact R84979
  · exact R84981
  · exact R84983
  · exact R84985
  · exact R84987
  · exact R84989
  · exact R84991
  · exact R84993
  · exact R84995
  · exact R84997
  · exact R84999
  · exact R85001
  · exact R85003
  · exact R85005
  · exact R85007
  · exact R85009
  · exact R85011
  · exact R85013
  · exact R85015
  · exact R85017
  · exact R85019
  · exact R85021
  · exact R85023
  · exact R85025
  · exact R85027
  · exact R85029
  · exact R85031
  · exact R85033
  · exact R85035
  · exact R85037
  · exact R85039
  · exact R85041
  · exact R85043
  · exact R85045
  · exact R85047
  · exact R85049
  · exact R85051
  · exact R85053
  · exact R85055
  · exact R85057
  · exact R85059
  · exact R85061
  · exact R85063
  · exact R85065
  · exact R85067
  · exact R85069
  · exact R85071
  · exact R85073
  · exact R85075
  · exact R85077
  · exact R85079
  · exact R85081
  · exact R85083
  · exact R85085
  · exact R85087
  · exact R85089
  · exact R85091
  · exact R85093
  · exact R85095
  · exact R85097
  · exact R85099
  · exact R85101
  · exact R85103
  · exact R85105
  · exact R85107
  · exact R85109
  · exact R85111
  · exact R85113
  · exact R85115
  · exact R85117
  · exact R85119
  · exact R85121
  · exact R85123
  · exact R85125
  · exact R85127
  · exact R85129
  · exact R85131
  · exact R85133
  · exact R85135
  · exact R85137
  · exact R85139
  · exact R85141
  · exact R85143
  · exact R85145
  · exact R85147
  · exact R85149
  · exact R85151
  · exact R85153
  · exact R85155
  · exact R85157
  · exact R85159
  · exact R85161
  · exact R85163
  · exact R85165
  · exact R85167
  · exact R85169
  · exact R85171
  · exact R85173
  · exact R85175
  · exact R85177
  · exact R85179
  · exact R85181
  · exact R85183
  · exact R85185
  · exact R85187
  · exact R85189
  · exact R85191
  · exact R85193
  · exact R85195
  · exact R85197
  · exact R85199
  · exact R85201
  · exact R85203
  · exact R85205
  · exact R85207
  · exact R85209
  · exact R85211
  · exact R85213
  · exact R85215
  · exact R85217
  · exact R85219
  · exact R85221
  · exact R85223
  · exact R85225
  · exact R85227
  · exact R85229
  · exact R85231
  · exact R85233
  · exact R85235
  · exact R85237
  · exact R85239
  · exact R85241
  · exact R85243
  · exact R85245
  · exact R85247
  · exact R85249
  · exact R85251
  · exact R85253
  · exact R85255
  · exact R85257
  · exact R85259
  · exact R85261
  · exact R85263
  · exact R85265
  · exact R85267
  · exact R85269
  · exact R85271
  · exact R85273
  · exact R85275
  · exact R85277
  · exact R85279
  · exact R85281
  · exact R85283
  · exact R85285
  · exact R85287
  · exact R85289
  · exact R85291
  · exact R85293
  · exact R85295
  · exact R85297
  · exact R85299
  · exact R85301
  · exact R85303
  · exact R85305
  · exact R85307
  · exact R85309
  · exact R85311
  · exact R85313
  · exact R85315
  · exact R85317
  · exact R85319
  · exact R85321
  · exact R85323
  · exact R85325
  · exact R85327
  · exact R85329
  · exact R85331
  · exact R85333
  · exact R85335
  · exact R85337
  · exact R85339
  · exact R85341
  · exact R85343
  · exact R85345
  · exact R85347
  · exact R85349
  · exact R85351
  · exact R85353
  · exact R85355
  · exact R85357
  · exact R85359
  · exact R85361
  · exact R85363
  · exact R85365
  · exact R85367
  · exact R85369
  · exact R85371
  · exact R85373
  · exact R85375
  · exact R85377
  · exact R85379
  · exact R85381
  · exact R85383
  · exact R85385
  · exact R85387
  · exact R85389
  · exact R85391
  · exact R85393
  · exact R85395
  · exact R85397
  · exact R85399
  · exact R85401
  · exact R85403
  · exact R85405
  · exact R85407
  · exact R85409
  · exact R85411
  · exact R85413
  · exact R85415
  · exact R85417
  · exact R85419
  · exact R85421
  · exact R85423
  · exact R85425
  · exact R85427
  · exact R85429
  · exact R85431
  · exact R85433
  · exact R85435
  · exact R85437
  · exact R85439
  · exact R85441
  · exact R85443
  · exact R85445
  · exact R85447
  · exact R85449
  · exact R85451
  · exact R85453
  · exact R85455
  · exact R85457
  · exact R85459
  · exact R85461
  · exact R85463
  · exact R85465
  · exact R85467
  · exact R85469
  · exact R85471
  · exact R85473
  · exact R85475
  · exact R85477
  · exact R85479
  · exact R85481
  · exact R85483
  · exact R85485
  · exact R85487
  · exact R85489
  · exact R85491
  · exact R85493
  · exact R85495
  · exact R85497
  · exact R85499
  · exact R85501
  · exact R85503
  · exact R85505
  · exact R85507
  · exact R85509
  · exact R85511
  · exact R85513
  · exact R85515
  · exact R85517
  · exact R85519
  · exact R85521
  · exact R85523
  · exact R85525
  · exact R85527
  · exact R85529
  · exact R85531
  · exact R85533
  · exact R85535
  · exact R85537
  · exact R85539
  · exact R85541
  · exact R85543
  · exact R85545
  · exact R85547
  · exact R85549
  · exact R85551
  · exact R85553
  · exact R85555
  · exact R85557
  · exact R85559
  · exact R85561
  · exact R85563
  · exact R85565
  · exact R85567
  · exact R85569
  · exact R85571
  · exact R85573
  · exact R85575
  · exact R85577
  · exact R85579
  · exact R85581
  · exact R85583
  · exact R85585
  · exact R85587
  · exact R85589
  · exact R85591
  · exact R85593
  · exact R85595
  · exact R85597
  · exact R85599
  · exact R85601
  · exact R85603
  · exact R85605
  · exact R85607
  · exact R85609
  · exact R85611
  · exact R85613
  · exact R85615
  · exact R85617
  · exact R85619
  · exact R85621
  · exact R85623
  · exact R85625
  · exact R85627
  · exact R85629
  · exact R85631
  · exact R85633
  · exact R85635
  · exact R85637
  · exact R85639
  · exact R85641
  · exact R85643
  · exact R85645
  · exact R85647
  · exact R85649
  · exact R85651
  · exact R85653
  · exact R85655
  · exact R85657
  · exact R85659
  · exact R85661
  · exact R85663
  · exact R85665
  · exact R85667
  · exact R85669
  · exact R85671
  · exact R85673
  · exact R85675
  · exact R85677
  · exact R85679
  · exact R85681
  · exact R85683
  · exact R85685
  · exact R85687
  · exact R85689
  · exact R85691
  · exact R85693
  · exact R85695
  · exact R85697
  · exact R85699
  · exact R85701
  · exact R85703
  · exact R85705
  · exact R85707
  · exact R85709
  · exact R85711
  · exact R85713
  · exact R85715
  · exact R85717
  · exact R85719
  · exact R85721
  · exact R85723
  · exact R85725
  · exact R85727
  · exact R85729
  · exact R85731
  · exact R85733
  · exact R85735
  · exact R85737
  · exact R85739
  · exact R85741
  · exact R85743
  · exact R85745
  · exact R85747
  · exact R85749
  · exact R85751
  · exact R85753
  · exact R85755
  · exact R85757
  · exact R85759
  · exact R85761
  · exact R85763
  · exact R85765
  · exact R85767
  · exact R85769
  · exact R85771
  · exact R85773
  · exact R85775
  · exact R85777
  · exact R85779
  · exact R85781
  · exact R85783
  · exact R85785
  · exact R85787
  · exact R85789
  · exact R85791
  · exact R85793
  · exact R85795
  · exact R85797
  · exact R85799
  · exact R85801
  · exact R85803
  · exact R85805
  · exact R85807
  · exact R85809
  · exact R85811
  · exact R85813
  · exact R85815
  · exact R85817
  · exact R85819
  · exact R85821
  · exact R85823
  · exact R85825
  · exact R85827
  · exact R85829
  · exact R85831
  · exact R85833
  · exact R85835
  · exact R85837
  · exact R85839
  · exact R85841
  · exact R85843
  · exact R85845
  · exact R85847
  · exact R85849
  · exact R85851
  · exact R85853
  · exact R85855
  · exact R85857
  · exact R85859
  · exact R85861
  · exact R85863
  · exact R85865
  · exact R85867
  · exact R85869
  · exact R85871
  · exact R85873
  · exact R85875
  · exact R85877
  · exact R85879
  · exact R85881
  · exact R85883
  · exact R85885
  · exact R85887
  · exact R85889
  · exact R85891
  · exact R85893
  · exact R85895
  · exact R85897
  · exact R85899
  · exact R85901
  · exact R85903
  · exact R85905
  · exact R85907
  · exact R85909
  · exact R85911
  · exact R85913
  · exact R85915
  · exact R85917
  · exact R85919
  · exact R85921
  · exact R85923
  · exact R85925
  · exact R85927

theorem C2 (j : ℕ) (h1 : 42964 ≤ j) (h2 : j ≤ 43563) : Reach (2 * j + 1) := by
  interval_cases j
  · exact R85929
  · exact R85931
  · exact R85933
  · exact R85935
  · exact R85937
  · exact R85939
  · exact R85941
  · exact R85943
  · exact R85945
  · exact R85947
  · exact R85949
  · exact R85951
  · exact R85953
  · exact R85955
  · exact R85957
  · exact R85959
  · exact R85961
  · exact R85963
  · exact R85965
  · exact R85967
  · exact R85969
  · exact R85971
  · exact R85973
  · exact R85975
  · exact R85977
  · exact R85979
  · exact R85981
  · exact R85983
  · exact R85985
  · exact R85987
  · exact R85989
  · exact R85991
  · exact R85993
  · exact R85995
  · exact R85997
  · exact R85999
  · exact R86001
  · exact R86003
  · exact R86005
  · exact R86007
  · exact R86009
  · exact R86011
  · exact R86013
  · exact R86015
  · exact R86017
  · exact R86019
  · exact R86021
  · exact R86023
  · exact R86025
  · exact R86027
  · exact R86029
  · exact R86031
  · exact R86033
  · exact R86035
  · exact R86037
  · exact R86039
  · exact R86041
  · exact R86043
  · exact R86045
  · exact R86047
  · exact R86049
  · exact R86051
  · exact R86053
  · exact R86055
  · exact R86057
  · exact R86059
  · exact R86061
  · exact R86063
  · exact R86065
  · exact R86067
  · exact R86069
  · exact R86071
  · exact R86073
  · exact R86075
  · exact R86077
  · exact R86079
  · exact R86081
  · exact R86083
  · exact R86085
  · exact R86087
  · exact R86089
  · exact R86091
  · exact R86093
  · exact R86095
  · exact R86097
  · exact R86099
  · exact R86101
  · exact R86103
  · exact R86105
  · exact R86107
  · exact R86109
  · exact R86111
  · exact R86113
  · exact R86115
  · exact R86117
  · exact R86119
  · exact R86121
  · exact R86123
  · exact R86125
  · exact R86127
  · exact R86129
  · exact R86131
  · exact R86133
  · exact R86135
  · exact R86137
  · exact R86139
  · exact R86141
  · exact R86143
  · exact R86145
  · exact R86147
  · exact R86149
  · exact R86151
  · exact R86153
  · exact R86155
  · exact R86157
  · exact R86159
  · exact R86161
  · exact R86163
  · exact R86165
  · exact R86167
  · exact R86169
  · exact R86171
  · exact R86173
  · exact R86175
  · exact R86177
  · exact R86179
  · exact R86181
  · exact R86183
  · exact R86185
  · exact R86187
  · exact R86189
  · exact R86191
  · exact R86193
  · exact R86195
  · exact R86197
  · exact R86199
  · exact R86201
  · exact R86203
  · exact R86205
  · exact R86207
  · exact R86209
  · exact R86211
  · exact R86213
  · exact R86215
  · exact R86217
  · exact R86219
  · exact R86221
  · exact R86223
  · exact R86225
  · exact R86227
  · exact R86229
  · exact R86231
  · exact R86233
  · exact R86235
  · exact R86237
  · exact R86239
  · exact R86241
  · exact R86243
  · exact R86245
  · exact R86247
  · exact R86249
  · exact R86251
  · exact R86253
  · exact R86255
  · exact R86257
  · exact R86259
  · exact R86261
  · exact R86263
  · exact R86265
  · exact R86267
  · exact R86269
  · exact R86271
  · exact R86273
  · exact R86275
  · exact R86277
  · exact R86279
  · exact R86281
  · exact R86283
  · exact R86285
  · exact R86287
  · exact R86289
  · exact R86291
  · exact R86293
  · exact R86295
  · exact R86297
  · exact R86299
  · exact R86301
  · exact R86303
  · exact R86305
  · exact R86307
  · exact R86309
  · exact R86311
  · exact R86313
  · exact R86315
  · exact R86317
  · exact R86319
  · exact R86321
  · exact R86323
  · exact R86325
  · exact R86327
  · exact R86329
  · exact R86331
  · exact R86333
  · exact R86335
  · exact R86337
  · exact R86339
  · exact R86341
  · exact R86343
  · exact R86345
  · exact R86347
  · exact R86349
  · exact R86351
  · exact R86353
  · exact R86355
  · exact R86357
  · exact R86359
  · exact R86361
  · exact R86363
  · exact R86365
  · exact R86367
  · exact R86369
  · exact R86371
  · exact R86373
  · exact R86375
  · exact R86377
  · exact R86379
  · exact R86381
  · exact R86383
  · exact R86385
  · exact R86387
  · exact R86389
  · exact R86391
  · exact R86393
  · exact R86395
  · exact R86397
  · exact R86399
  · exact R86401
  · exact R86403
  · exact R86405
  · exact R86407
  · exact R86409
  · exact R86411
  · exact R86413
  · exact R86415
  · exact R86417
  · exact R86419
  · exact R86421
  · exact R86423
  · exact R86425
  · exact R86427
  · exact R86429
  · exact R86431
  · exact R86433
  · exact R86435
  · exact R86437
  · exact R86439
  · exact R86441
  · exact R86443
  · exact R86445
  · exact R86447
  · exact R86449
  · exact R86451
  · exact R86453
  · exact R86455
  · exact R86457
  · exact R86459
  · exact R86461
  · exact R86463
  · exact R86465
  · exact R86467
  · exact R86469
  · exact R86471
  · exact R86473
  · exact R86475
  · exact R86477
  · exact R86479
  · exact R86481
  · exact R86483
  · exact R86485
  · exact R86487
  · exact R86489
  · exact R86491
  · exact R86493
  · exact R86495
  · exact R86497
  · exact R86499
  · exact R86501
  · exact R86503
  · exact R86505
  · exact R86507
  · exact R86509
  · exact R86511
  · exact R86513
  · exact R86515
  · exact R86517
  · exact R86519
  · exact R86521
  · exact R86523
  · exact R86525
  · exact R86527
  · exact R86529
  · exact R86531
  · exact R86533
  · exact R86535
  · exact R86537
  · exact R86539
  · exact R86541
  · exact R86543
  · exact R86545
  · exact R86547
  · exact R86549
  · exact R86551
  · exact R86553
  · exact R86555
  · exact R86557
  · exact R86559
  · exact R86561
  · exact R86563
  · exact R86565
  · exact R86567
  · exact R86569
  · exact R86571
  · exact R86573
  · exact R86575
  · exact R86577
  · exact R86579
  · exact R86581
  · exact R86583
  · exact R86585
  · exact R86587
  · exact R86589
  · exact R86591
  · exact R86593
  · exact R86595
  · exact R86597
  · exact R86599
  · exact R86601
  · exact R86603
  · exact R86605
  · exact R86607
  · exact R86609
  · exact R86611
  · exact R86613
  · exact R86615
  · exact R86617
  · exact R86619
  · exact R86621
  · exact R86623
  · exact R86625
  · exact R86627
  · exact R86629
  · exact R86631
  · exact R86633
  · exact R86635
  · exact R86637
  · exact R86639
  · exact R86641
  · exact R86643
  · exact R86645
  · exact R86647
  · exact R86649
  · exact R86651
  · exact R86653
  · exact R86655
  · exact R86657
  · exact R86659
  · exact R86661
  · exact R86663
  · exact R86665
  · exact R86667
  · exact R86669
  · exact R86671
  · exact R86673
  · exact R86675
  · exact R86677
  · exact R86679
  · exact R86681
  · exact R86683
  · exact R86685
  · exact R86687
  · exact R86689
  · exact R86691
  · exact R86693
  · exact R86695
  · exact R86697
  · exact R86699
  · exact R86701
  · exact R86703
  · exact R86705
  · exact R86707
  · exact R86709
  · exact R86711
  · exact R86713
  · exact R86715
  · exact R86717
  · exact R86719
  · exact R86721
  · exact R86723
  · exact R86725
  · exact R86727
  · exact R86729
  · exact R86731
  · exact R86733
  · exact R86735
  · exact R86737
  · exact R86739
  · exact R86741
  · exact R86743
  · exact R86745
  · exact R86747
  · exact R86749
  · exact R86751
  · exact R86753
  · exact R86755
  · exact R86757
  · exact R86759
  · exact R86761
  · exact R86763
  · exact R86765
  · exact R86767
  · exact R86769
  · exact R86771
  · exact R86773
  · exact R86775
  · exact R86777
  · exact R86779
  · exact R86781
  · exact R86783
  · exact R86785
  · exact R86787
  · exact R86789
  · exact R86791
  · exact R86793
  · exact R86795
  · exact R86797
  · exact R86799
  · exact R86801
  · exact R86803
  · exact R86805
  · exact R86807
  · exact R86809
  · exact R86811
  · exact R86813
  · exact R86815
  · exact R86817
  · exact R86819
  · exact R86821
  · exact R86823
  · exact R86825
  · exact R86827
  · exact R86829
  · exact R86831
  · exact R86833
  · exact R86835
  · exact R86837
  · exact R86839
  · exact R86841
  · exact R86843
  · exact R86845
  · exact R86847
  · exact R86849
  · exact R86851
  · exact R86853
  · exact R86855
  · exact R86857
  · exact R86859
  · exact R86861
  · exact R86863
  · exact R86865
  · exact R86867
  · exact R86869
  · exact R86871
  · exact R86873
  · exact R86875
  · exact R86877
  · exact R86879
  · exact R86881
  · exact R86883
  · exact R86885
  · exact R86887
  · exact R86889
  · exact R86891
  · exact R86893
  · exact R86895
  · exact R86897
  · exact R86899
  · exact R86901
  · exact R86903
  · exact R86905
  · exact R86907
  · exact R86909
  · exact R86911
  · exact R86913
  · exact R86915
  · exact R86917
  · exact R86919
  · exact R86921
  · exact R86923
  · exact R86925
  · exact R86927
  · exact R86929
  · exact R86931
  · exact R86933
  · exact R86935
  · exact R86937
  · exact R86939
  · exact R86941
  · exact R86943
  · exact R86945
  · exact R86947
  · exact R86949
  · exact R86951
  · exact R86953
  · exact R86955
  · exact R86957
  · exact R86959
  · exact R86961
  · exact R86963
  · exact R86965
  · exact R86967
  · exact R86969
  · exact R86971
  · exact R86973
  · exact R86975
  · exact R86977
  · exact R86979
  · exact R86981
  · exact R86983
  · exact R86985
  · exact R86987
  · exact R86989
  · exact R86991
  · exact R86993
  · exact R86995
  · exact R86997
  · exact R86999
  · exact R87001
  · exact R87003
  · exact R87005
  · exact R87007
  · exact R87009
  · exact R87011
  · exact R87013
  · exact R87015
  · exact R87017
  · exact R87019
  · exact R87021
  · exact R87023
  · exact R87025
  · exact R87027
  · exact R87029
  · exact R87031
  · exact R87033
  · exact R87035
  · exact R87037
  · exact R87039
  · exact R87041
  · exact R87043
  · exact R87045
  · exact R87047
  · exact R87049
  · exact R87051
  · exact R87053
  · exact R87055
  · exact R87057
  · exact R87059
  · exact R87061
  · exact R87063
  · exact R87065
  · exact R87067
  · exact R87069
  · exact R87071
  · exact R87073
  · exact R87075
  · exact R87077
  · exact R87079
  · exact R87081
  · exact R87083
  · exact R87085
  · exact R87087
  · exact R87089
  · exact R87091
  · exact R87093
  · exact R87095
  · exact R87097
  · exact R87099
  · exact R87101
  · exact R87103
  · exact R87105
  · exact R87107
  · exact R87109
  · exact R87111
  · exact R87113
  · exact R87115
  · exact R87117
  · exact R87119
  · exact R87121
  · exact R87123
  · exact R87125
  · exact R87127

theorem solution (m : ℕ) (hm : 0 < m) (hodd : Odd m) (hle : m ≤ 87128) :
    ∃ k : ℕ, syracuseStep^[k] m = 1 := by
  rcases Nat.lt_or_ge m 83128 with hlo | hlo
  · exact syracuse_reaches_one_below_83128 m hm hodd (by omega)
  obtain ⟨j, rfl⟩ : ∃ j, m = 2 * j + 1 := by obtain ⟨t, ht⟩ := hodd; exact ⟨t, by omega⟩
  rcases Nat.lt_or_ge j 42264 with h0 | h0
  · exact C0 j (by omega) (by omega)
  rcases Nat.lt_or_ge j 42964 with h1 | h1
  · exact C1 j (by omega) (by omega)
  exact C2 j (by omega) (by omega)
