-- Prove2me | solution 1 for syracuse_reaches_one_below_59122
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T06:01:15.962568+00:00
-- url     : https://prove2.me/submissions/37fb4746-c3fa-49e8-b511-98d1204cacd6

import Mathlib
import Definitions.Def_syracuseStep
import Theorems.Thm_syracuse_reaches_one_below_55121

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
theorem B (n : ℕ) (h1 : 0 < n) (h2 : Odd n) (h3 : n ≤ 55120) : Reach n :=
  syracuse_reaches_one_below_55121 n h1 h2 h3
theorem R98309 : Reach 98309 := rs (se 4 (by rfl) ⟨9216, by rfl⟩) (B 18433 (by norm_num) ⟨9216, by rfl⟩ (by norm_num))
theorem R196613 : Reach 196613 := rs (se 4 (by rfl) ⟨18432, by rfl⟩) (B 36865 (by norm_num) ⟨18432, by rfl⟩ (by norm_num))
theorem R131093 : Reach 131093 := rs (se 6 (by rfl) ⟨3072, by rfl⟩) (B 6145 (by norm_num) ⟨3072, by rfl⟩ (by norm_num))
theorem R65569 : Reach 65569 := rs (se 2 (by rfl) ⟨24588, by rfl⟩) (B 49177 (by norm_num) ⟨24588, by rfl⟩ (by norm_num))
theorem R65605 : Reach 65605 := rs (se 4 (by rfl) ⟨6150, by rfl⟩) (B 12301 (by norm_num) ⟨6150, by rfl⟩ (by norm_num))
theorem R98381 : Reach 98381 := rs (se 3 (by rfl) ⟨18446, by rfl⟩) (B 36893 (by norm_num) ⟨18446, by rfl⟩ (by norm_num))
theorem R131165 : Reach 131165 := rs (se 3 (by rfl) ⟨24593, by rfl⟩) (B 49187 (by norm_num) ⟨24593, by rfl⟩ (by norm_num))
theorem R65641 : Reach 65641 := rs (se 2 (by rfl) ⟨24615, by rfl⟩) (B 49231 (by norm_num) ⟨24615, by rfl⟩ (by norm_num))
theorem R163957 : Reach 163957 := rs (se 5 (by rfl) ⟨7685, by rfl⟩) (B 15371 (by norm_num) ⟨7685, by rfl⟩ (by norm_num))
theorem R65677 : Reach 65677 := rs (se 3 (by rfl) ⟨12314, by rfl⟩) (B 24629 (by norm_num) ⟨12314, by rfl⟩ (by norm_num))
theorem R131237 : Reach 131237 := rs (se 4 (by rfl) ⟨12303, by rfl⟩) (B 24607 (by norm_num) ⟨12303, by rfl⟩ (by norm_num))
theorem R65713 : Reach 65713 := rs (se 2 (by rfl) ⟨24642, by rfl⟩) (B 49285 (by norm_num) ⟨24642, by rfl⟩ (by norm_num))
theorem R98509 : Reach 98509 := rs (se 3 (by rfl) ⟨18470, by rfl⟩) (B 36941 (by norm_num) ⟨18470, by rfl⟩ (by norm_num))
theorem R65749 : Reach 65749 := rs (se 7 (by rfl) ⟨770, by rfl⟩) (B 1541 (by norm_num) ⟨770, by rfl⟩ (by norm_num))
theorem R131309 : Reach 131309 := rs (se 3 (by rfl) ⟨24620, by rfl⟩) (B 49241 (by norm_num) ⟨24620, by rfl⟩ (by norm_num))
theorem R65785 : Reach 65785 := rs (se 2 (by rfl) ⟨24669, by rfl⟩) (B 49339 (by norm_num) ⟨24669, by rfl⟩ (by norm_num))
theorem R65821 : Reach 65821 := rs (se 3 (by rfl) ⟨12341, by rfl⟩) (B 24683 (by norm_num) ⟨12341, by rfl⟩ (by norm_num))
theorem R98597 : Reach 98597 := rs (se 4 (by rfl) ⟨9243, by rfl⟩) (B 18487 (by norm_num) ⟨9243, by rfl⟩ (by norm_num))
theorem R131381 : Reach 131381 := rs (se 5 (by rfl) ⟨6158, by rfl⟩) (B 12317 (by norm_num) ⟨6158, by rfl⟩ (by norm_num))
theorem R65857 : Reach 65857 := rs (se 2 (by rfl) ⟨24696, by rfl⟩) (B 49393 (by norm_num) ⟨24696, by rfl⟩ (by norm_num))
theorem R65893 : Reach 65893 := rs (se 4 (by rfl) ⟨6177, by rfl⟩) (B 12355 (by norm_num) ⟨6177, by rfl⟩ (by norm_num))
theorem R131453 : Reach 131453 := rs (se 3 (by rfl) ⟨24647, by rfl⟩) (B 49295 (by norm_num) ⟨24647, by rfl⟩ (by norm_num))
theorem R65929 : Reach 65929 := rs (se 2 (by rfl) ⟨24723, by rfl⟩) (B 49447 (by norm_num) ⟨24723, by rfl⟩ (by norm_num))
theorem R98725 : Reach 98725 := rs (se 4 (by rfl) ⟨9255, by rfl⟩) (B 18511 (by norm_num) ⟨9255, by rfl⟩ (by norm_num))
theorem R65965 : Reach 65965 := rs (se 3 (by rfl) ⟨12368, by rfl⟩) (B 24737 (by norm_num) ⟨12368, by rfl⟩ (by norm_num))
theorem R197045 : Reach 197045 := rs (se 5 (by rfl) ⟨9236, by rfl⟩) (B 18473 (by norm_num) ⟨9236, by rfl⟩ (by norm_num))
theorem R131525 : Reach 131525 := rs (se 4 (by rfl) ⟨12330, by rfl⟩) (B 24661 (by norm_num) ⟨12330, by rfl⟩ (by norm_num))
theorem R66001 : Reach 66001 := rs (se 2 (by rfl) ⟨24750, by rfl⟩) (B 49501 (by norm_num) ⟨24750, by rfl⟩ (by norm_num))
theorem R66037 : Reach 66037 := rs (se 5 (by rfl) ⟨3095, by rfl⟩) (B 6191 (by norm_num) ⟨3095, by rfl⟩ (by norm_num))
theorem R98813 : Reach 98813 := rs (se 3 (by rfl) ⟨18527, by rfl⟩) (B 37055 (by norm_num) ⟨18527, by rfl⟩ (by norm_num))
theorem R131597 : Reach 131597 := rs (se 3 (by rfl) ⟨24674, by rfl⟩) (B 49349 (by norm_num) ⟨24674, by rfl⟩ (by norm_num))
theorem R66073 : Reach 66073 := rs (se 2 (by rfl) ⟨24777, by rfl⟩) (B 49555 (by norm_num) ⟨24777, by rfl⟩ (by norm_num))
theorem R393781 : Reach 393781 := rs (se 5 (by rfl) ⟨18458, by rfl⟩) (B 36917 (by norm_num) ⟨18458, by rfl⟩ (by norm_num))
theorem R66109 : Reach 66109 := rs (se 3 (by rfl) ⟨12395, by rfl⟩) (B 24791 (by norm_num) ⟨12395, by rfl⟩ (by norm_num))
theorem R131669 : Reach 131669 := rs (se 8 (by rfl) ⟨771, by rfl⟩) (B 1543 (by norm_num) ⟨771, by rfl⟩ (by norm_num))
theorem R66145 : Reach 66145 := rs (se 2 (by rfl) ⟨24804, by rfl⟩) (B 49609 (by norm_num) ⟨24804, by rfl⟩ (by norm_num))
theorem R98941 : Reach 98941 := rs (se 3 (by rfl) ⟨18551, by rfl⟩) (B 37103 (by norm_num) ⟨18551, by rfl⟩ (by norm_num))
theorem R66181 : Reach 66181 := rs (se 4 (by rfl) ⟨6204, by rfl⟩) (B 12409 (by norm_num) ⟨6204, by rfl⟩ (by norm_num))
theorem R164501 : Reach 164501 := rs (se 6 (by rfl) ⟨3855, by rfl⟩) (B 7711 (by norm_num) ⟨3855, by rfl⟩ (by norm_num))
theorem R131741 : Reach 131741 := rs (se 3 (by rfl) ⟨24701, by rfl⟩) (B 49403 (by norm_num) ⟨24701, by rfl⟩ (by norm_num))
theorem R66217 : Reach 66217 := rs (se 2 (by rfl) ⟨24831, by rfl⟩) (B 49663 (by norm_num) ⟨24831, by rfl⟩ (by norm_num))
theorem R66253 : Reach 66253 := rs (se 3 (by rfl) ⟨12422, by rfl⟩) (B 24845 (by norm_num) ⟨12422, by rfl⟩ (by norm_num))
theorem R99029 : Reach 99029 := rs (se 7 (by rfl) ⟨1160, by rfl⟩) (B 2321 (by norm_num) ⟨1160, by rfl⟩ (by norm_num))
theorem R131813 : Reach 131813 := rs (se 4 (by rfl) ⟨12357, by rfl⟩) (B 24715 (by norm_num) ⟨12357, by rfl⟩ (by norm_num))
theorem R66289 : Reach 66289 := rs (se 2 (by rfl) ⟨24858, by rfl⟩) (B 49717 (by norm_num) ⟨24858, by rfl⟩ (by norm_num))
theorem R66325 : Reach 66325 := rs (se 6 (by rfl) ⟨1554, by rfl⟩) (B 3109 (by norm_num) ⟨1554, by rfl⟩ (by norm_num))
theorem R131885 : Reach 131885 := rs (se 3 (by rfl) ⟨24728, by rfl⟩) (B 49457 (by norm_num) ⟨24728, by rfl⟩ (by norm_num))
theorem R66361 : Reach 66361 := rs (se 2 (by rfl) ⟨24885, by rfl⟩) (B 49771 (by norm_num) ⟨24885, by rfl⟩ (by norm_num))
theorem R99157 : Reach 99157 := rs (se 9 (by rfl) ⟨290, by rfl⟩) (B 581 (by norm_num) ⟨290, by rfl⟩ (by norm_num))
theorem R66397 : Reach 66397 := rs (se 3 (by rfl) ⟨12449, by rfl⟩) (B 24899 (by norm_num) ⟨12449, by rfl⟩ (by norm_num))
theorem R197477 : Reach 197477 := rs (se 4 (by rfl) ⟨18513, by rfl⟩) (B 37027 (by norm_num) ⟨18513, by rfl⟩ (by norm_num))
theorem R131957 : Reach 131957 := rs (se 5 (by rfl) ⟨6185, by rfl⟩) (B 12371 (by norm_num) ⟨6185, by rfl⟩ (by norm_num))
theorem R66433 : Reach 66433 := rs (se 2 (by rfl) ⟨24912, by rfl⟩) (B 49825 (by norm_num) ⟨24912, by rfl⟩ (by norm_num))
theorem R66469 : Reach 66469 := rs (se 4 (by rfl) ⟨6231, by rfl⟩) (B 12463 (by norm_num) ⟨6231, by rfl⟩ (by norm_num))
theorem R99245 : Reach 99245 := rs (se 3 (by rfl) ⟨18608, by rfl⟩) (B 37217 (by norm_num) ⟨18608, by rfl⟩ (by norm_num))
theorem R132029 : Reach 132029 := rs (se 3 (by rfl) ⟨24755, by rfl⟩) (B 49511 (by norm_num) ⟨24755, by rfl⟩ (by norm_num))
theorem R66505 : Reach 66505 := rs (se 2 (by rfl) ⟨24939, by rfl⟩) (B 49879 (by norm_num) ⟨24939, by rfl⟩ (by norm_num))
theorem R66565 : Reach 66565 := rs (se 4 (by rfl) ⟨6240, by rfl⟩) (B 12481 (by norm_num) ⟨6240, by rfl⟩ (by norm_num))
theorem R132101 : Reach 132101 := rs (se 4 (by rfl) ⟨12384, by rfl⟩) (B 24769 (by norm_num) ⟨12384, by rfl⟩ (by norm_num))
theorem R99373 : Reach 99373 := rs (se 3 (by rfl) ⟨18632, by rfl⟩) (B 37265 (by norm_num) ⟨18632, by rfl⟩ (by norm_num))
theorem R132173 : Reach 132173 := rs (se 3 (by rfl) ⟨24782, by rfl⟩) (B 49565 (by norm_num) ⟨24782, by rfl⟩ (by norm_num))
theorem R984149 : Reach 984149 := rs (se 8 (by rfl) ⟨5766, by rfl⟩) (B 11533 (by norm_num) ⟨5766, by rfl⟩ (by norm_num))
theorem R99461 : Reach 99461 := rs (se 4 (by rfl) ⟨9324, by rfl⟩) (B 18649 (by norm_num) ⟨9324, by rfl⟩ (by norm_num))
theorem R132245 : Reach 132245 := rs (se 6 (by rfl) ⟨3099, by rfl⟩) (B 6199 (by norm_num) ⟨3099, by rfl⟩ (by norm_num))
theorem R132317 : Reach 132317 := rs (se 3 (by rfl) ⟨24809, by rfl⟩) (B 49619 (by norm_num) ⟨24809, by rfl⟩ (by norm_num))
theorem R99589 : Reach 99589 := rs (se 4 (by rfl) ⟨9336, by rfl⟩) (B 18673 (by norm_num) ⟨9336, by rfl⟩ (by norm_num))
theorem R197909 : Reach 197909 := rs (se 6 (by rfl) ⟨4638, by rfl⟩) (B 9277 (by norm_num) ⟨4638, by rfl⟩ (by norm_num))
theorem R132389 : Reach 132389 := rs (se 4 (by rfl) ⟨12411, by rfl⟩) (B 24823 (by norm_num) ⟨12411, by rfl⟩ (by norm_num))
theorem R99677 : Reach 99677 := rs (se 3 (by rfl) ⟨18689, by rfl⟩) (B 37379 (by norm_num) ⟨18689, by rfl⟩ (by norm_num))
theorem R132461 : Reach 132461 := rs (se 3 (by rfl) ⟨24836, by rfl⟩) (B 49673 (by norm_num) ⟨24836, by rfl⟩ (by norm_num))
theorem R99733 : Reach 99733 := rs (se 6 (by rfl) ⟨2337, by rfl⟩) (B 4675 (by norm_num) ⟨2337, by rfl⟩ (by norm_num))
theorem R132533 : Reach 132533 := rs (se 5 (by rfl) ⟨6212, by rfl⟩) (B 12425 (by norm_num) ⟨6212, by rfl⟩ (by norm_num))
theorem R132605 : Reach 132605 := rs (se 3 (by rfl) ⟨24863, by rfl⟩) (B 49727 (by norm_num) ⟨24863, by rfl⟩ (by norm_num))
theorem R132677 : Reach 132677 := rs (se 4 (by rfl) ⟨12438, by rfl⟩) (B 24877 (by norm_num) ⟨12438, by rfl⟩ (by norm_num))
theorem R99949 : Reach 99949 := rs (se 3 (by rfl) ⟨18740, by rfl⟩) (B 37481 (by norm_num) ⟨18740, by rfl⟩ (by norm_num))
theorem R132749 : Reach 132749 := rs (se 3 (by rfl) ⟨24890, by rfl⟩) (B 49781 (by norm_num) ⟨24890, by rfl⟩ (by norm_num))
theorem R198341 : Reach 198341 := rs (se 4 (by rfl) ⟨18594, by rfl⟩) (B 37189 (by norm_num) ⟨18594, by rfl⟩ (by norm_num))
theorem R132821 : Reach 132821 := rs (se 7 (by rfl) ⟨1556, by rfl⟩) (B 3113 (by norm_num) ⟨1556, by rfl⟩ (by norm_num))
theorem R132853 : Reach 132853 := rs (se 5 (by rfl) ⟨6227, by rfl⟩) (B 12455 (by norm_num) ⟨6227, by rfl⟩ (by norm_num))
theorem R67349 : Reach 67349 := rs (se 6 (by rfl) ⟨1578, by rfl⟩) (B 3157 (by norm_num) ⟨1578, by rfl⟩ (by norm_num))
theorem R132893 : Reach 132893 := rs (se 3 (by rfl) ⟨24917, by rfl⟩) (B 49835 (by norm_num) ⟨24917, by rfl⟩ (by norm_num))
theorem R132949 : Reach 132949 := rs (se 9 (by rfl) ⟨389, by rfl⟩) (B 779 (by norm_num) ⟨389, by rfl⟩ (by norm_num))
theorem R132965 : Reach 132965 := rs (se 4 (by rfl) ⟨12465, by rfl⟩) (B 24931 (by norm_num) ⟨12465, by rfl⟩ (by norm_num))
theorem R755669 : Reach 755669 := rs (se 7 (by rfl) ⟨8855, by rfl⟩) (B 17711 (by norm_num) ⟨8855, by rfl⟩ (by norm_num))
theorem R65533 : Reach 65533 := rs (se 3 (by rfl) ⟨12287, by rfl⟩) (B 24575 (by norm_num) ⟨12287, by rfl⟩ (by norm_num))
theorem R67657 : Reach 67657 := rs (se 2 (by rfl) ⟨25371, by rfl⟩) (B 50743 (by norm_num) ⟨25371, by rfl⟩ (by norm_num))
theorem R165989 : Reach 165989 := rs (se 4 (by rfl) ⟨15561, by rfl⟩) (B 31123 (by norm_num) ⟨15561, by rfl⟩ (by norm_num))
theorem R198773 : Reach 198773 := rs (se 5 (by rfl) ⟨9317, by rfl⟩) (B 18635 (by norm_num) ⟨9317, by rfl⟩ (by norm_num))
theorem R657557 : Reach 657557 := rs (se 6 (by rfl) ⟨15411, by rfl⟩) (B 30823 (by norm_num) ⟨15411, by rfl⟩ (by norm_num))
theorem R362677 : Reach 362677 := rs (se 5 (by rfl) ⟨17000, by rfl⟩) (B 34001 (by norm_num) ⟨17000, by rfl⟩ (by norm_num))
theorem R297269 : Reach 297269 := rs (se 5 (by rfl) ⟨13934, by rfl⟩) (B 27869 (by norm_num) ⟨13934, by rfl⟩ (by norm_num))
theorem R330101 : Reach 330101 := rs (se 5 (by rfl) ⟨15473, by rfl⟩) (B 30947 (by norm_num) ⟨15473, by rfl⟩ (by norm_num))
theorem R199061 : Reach 199061 := rs (se 6 (by rfl) ⟨4665, by rfl⟩) (B 9331 (by norm_num) ⟨4665, by rfl⟩ (by norm_num))
theorem R100757 : Reach 100757 := rs (se 6 (by rfl) ⟨2361, by rfl⟩) (B 4723 (by norm_num) ⟨2361, by rfl⟩ (by norm_num))
theorem R68045 : Reach 68045 := rs (se 3 (by rfl) ⟨12758, by rfl⟩) (B 25517 (by norm_num) ⟨12758, by rfl⟩ (by norm_num))
theorem R68117 : Reach 68117 := rs (se 6 (by rfl) ⟨1596, by rfl⟩) (B 3193 (by norm_num) ⟨1596, by rfl⟩ (by norm_num))
theorem R199205 : Reach 199205 := rs (se 4 (by rfl) ⟨18675, by rfl⟩) (B 37351 (by norm_num) ⟨18675, by rfl⟩ (by norm_num))
theorem R68401 : Reach 68401 := rs (se 2 (by rfl) ⟨25650, by rfl⟩) (B 51301 (by norm_num) ⟨25650, by rfl⟩ (by norm_num))
theorem R166805 : Reach 166805 := rs (se 6 (by rfl) ⟨3909, by rfl⟩) (B 7819 (by norm_num) ⟨3909, by rfl⟩ (by norm_num))
theorem R265301 : Reach 265301 := rs (se 8 (by rfl) ⟨1554, by rfl⟩) (B 3109 (by norm_num) ⟨1554, by rfl⟩ (by norm_num))
theorem R68737 : Reach 68737 := rs (se 2 (by rfl) ⟨25776, by rfl⟩) (B 51553 (by norm_num) ⟨25776, by rfl⟩ (by norm_num))
theorem R101549 : Reach 101549 := rs (se 3 (by rfl) ⟨19040, by rfl⟩) (B 38081 (by norm_num) ⟨19040, by rfl⟩ (by norm_num))
theorem R101693 : Reach 101693 := rs (se 3 (by rfl) ⟨19067, by rfl⟩) (B 38135 (by norm_num) ⟨19067, by rfl⟩ (by norm_num))
theorem R101773 : Reach 101773 := rs (se 3 (by rfl) ⟨19082, by rfl⟩) (B 38165 (by norm_num) ⟨19082, by rfl⟩ (by norm_num))
theorem R101837 : Reach 101837 := rs (se 3 (by rfl) ⟨19094, by rfl⟩) (B 38189 (by norm_num) ⟨19094, by rfl⟩ (by norm_num))
theorem R69617 : Reach 69617 := rs (se 2 (by rfl) ⟨26106, by rfl⟩) (B 52213 (by norm_num) ⟨26106, by rfl⟩ (by norm_num))
theorem R167989 : Reach 167989 := rs (se 5 (by rfl) ⟨7874, by rfl⟩) (B 15749 (by norm_num) ⟨7874, by rfl⟩ (by norm_num))
theorem R135245 : Reach 135245 := rs (se 3 (by rfl) ⟨25358, by rfl⟩) (B 50717 (by norm_num) ⟨25358, by rfl⟩ (by norm_num))
theorem R69817 : Reach 69817 := rs (se 2 (by rfl) ⟨26181, by rfl⟩) (B 52363 (by norm_num) ⟨26181, by rfl⟩ (by norm_num))
theorem R168149 : Reach 168149 := rs (se 7 (by rfl) ⟨1970, by rfl⟩) (B 3941 (by norm_num) ⟨1970, by rfl⟩ (by norm_num))
theorem R135389 : Reach 135389 := rs (se 3 (by rfl) ⟨25385, by rfl⟩) (B 50771 (by norm_num) ⟨25385, by rfl⟩ (by norm_num))
theorem R299285 : Reach 299285 := rs (se 6 (by rfl) ⟨7014, by rfl⟩) (B 14029 (by norm_num) ⟨7014, by rfl⟩ (by norm_num))
theorem R69913 : Reach 69913 := rs (se 2 (by rfl) ⟨26217, by rfl⟩) (B 52435 (by norm_num) ⟨26217, by rfl⟩ (by norm_num))
theorem R69925 : Reach 69925 := rs (se 4 (by rfl) ⟨6555, by rfl⟩) (B 13111 (by norm_num) ⟨6555, by rfl⟩ (by norm_num))
theorem R70085 : Reach 70085 := rs (se 4 (by rfl) ⟨6570, by rfl⟩) (B 13141 (by norm_num) ⟨6570, by rfl⟩ (by norm_num))
theorem R70141 : Reach 70141 := rs (se 3 (by rfl) ⟨13151, by rfl⟩) (B 26303 (by norm_num) ⟨13151, by rfl⟩ (by norm_num))
theorem R135701 : Reach 135701 := rs (se 6 (by rfl) ⟨3180, by rfl⟩) (B 6361 (by norm_num) ⟨3180, by rfl⟩ (by norm_num))
theorem R70189 : Reach 70189 := rs (se 3 (by rfl) ⟨13160, by rfl⟩) (B 26321 (by norm_num) ⟨13160, by rfl⟩ (by norm_num))
theorem R70193 : Reach 70193 := rs (se 2 (by rfl) ⟨26322, by rfl⟩) (B 52645 (by norm_num) ⟨26322, by rfl⟩ (by norm_num))
theorem R70237 : Reach 70237 := rs (se 3 (by rfl) ⟨13169, by rfl⟩) (B 26339 (by norm_num) ⟨13169, by rfl⟩ (by norm_num))
theorem R135845 : Reach 135845 := rs (se 4 (by rfl) ⟨12735, by rfl⟩) (B 25471 (by norm_num) ⟨12735, by rfl⟩ (by norm_num))
theorem R70309 : Reach 70309 := rs (se 4 (by rfl) ⟨6591, by rfl⟩) (B 13183 (by norm_num) ⟨6591, by rfl⟩ (by norm_num))
theorem R70313 : Reach 70313 := rs (se 2 (by rfl) ⟨26367, by rfl⟩) (B 52735 (by norm_num) ⟨26367, by rfl⟩ (by norm_num))
theorem R70409 : Reach 70409 := rs (se 2 (by rfl) ⟨26403, by rfl⟩) (B 52807 (by norm_num) ⟨26403, by rfl⟩ (by norm_num))
theorem R70417 : Reach 70417 := rs (se 2 (by rfl) ⟨26406, by rfl⟩) (B 52813 (by norm_num) ⟨26406, by rfl⟩ (by norm_num))
theorem R1151765 : Reach 1151765 := rs (se 6 (by rfl) ⟨26994, by rfl⟩) (B 53989 (by norm_num) ⟨26994, by rfl⟩ (by norm_num))
theorem R70465 : Reach 70465 := rs (se 2 (by rfl) ⟨26424, by rfl⟩) (B 52849 (by norm_num) ⟨26424, by rfl⟩ (by norm_num))
theorem R201541 : Reach 201541 := rs (se 4 (by rfl) ⟨18894, by rfl⟩) (B 37789 (by norm_num) ⟨18894, by rfl⟩ (by norm_num))
theorem R70561 : Reach 70561 := rs (se 2 (by rfl) ⟨26460, by rfl⟩) (B 52921 (by norm_num) ⟨26460, by rfl⟩ (by norm_num))
theorem R70717 : Reach 70717 := rs (se 3 (by rfl) ⟨13259, by rfl⟩) (B 26519 (by norm_num) ⟨13259, by rfl⟩ (by norm_num))
theorem R70733 : Reach 70733 := rs (se 3 (by rfl) ⟨13262, by rfl⟩) (B 26525 (by norm_num) ⟨13262, by rfl⟩ (by norm_num))
theorem R70789 : Reach 70789 := rs (se 4 (by rfl) ⟨6636, by rfl⟩) (B 13273 (by norm_num) ⟨6636, by rfl⟩ (by norm_num))
theorem R70885 : Reach 70885 := rs (se 4 (by rfl) ⟨6645, by rfl⟩) (B 13291 (by norm_num) ⟨6645, by rfl⟩ (by norm_num))
theorem R267509 : Reach 267509 := rs (se 5 (by rfl) ⟨12539, by rfl⟩) (B 25079 (by norm_num) ⟨12539, by rfl⟩ (by norm_num))
theorem R71057 : Reach 71057 := rs (se 2 (by rfl) ⟨26646, by rfl⟩) (B 53293 (by norm_num) ⟨26646, by rfl⟩ (by norm_num))
theorem R71113 : Reach 71113 := rs (se 2 (by rfl) ⟨26667, by rfl⟩) (B 53335 (by norm_num) ⟨26667, by rfl⟩ (by norm_num))
theorem R71209 : Reach 71209 := rs (se 2 (by rfl) ⟨26703, by rfl⟩) (B 53407 (by norm_num) ⟨26703, by rfl⟩ (by norm_num))
theorem R104045 : Reach 104045 := rs (se 3 (by rfl) ⟨19508, by rfl⟩) (B 39017 (by norm_num) ⟨19508, by rfl⟩ (by norm_num))
theorem R71381 : Reach 71381 := rs (se 7 (by rfl) ⟨836, by rfl⟩) (B 1673 (by norm_num) ⟨836, by rfl⟩ (by norm_num))
theorem R71425 : Reach 71425 := rs (se 2 (by rfl) ⟨26784, by rfl⟩) (B 53569 (by norm_num) ⟨26784, by rfl⟩ (by norm_num))
theorem R71437 : Reach 71437 := rs (se 3 (by rfl) ⟨13394, by rfl⟩) (B 26789 (by norm_num) ⟨13394, by rfl⟩ (by norm_num))
theorem R71533 : Reach 71533 := rs (se 3 (by rfl) ⟨13412, by rfl⟩) (B 26825 (by norm_num) ⟨13412, by rfl⟩ (by norm_num))
theorem R432053 : Reach 432053 := rs (se 5 (by rfl) ⟨20252, by rfl⟩) (B 40505 (by norm_num) ⟨20252, by rfl⟩ (by norm_num))
theorem R71705 : Reach 71705 := rs (se 2 (by rfl) ⟨26889, by rfl⟩) (B 53779 (by norm_num) ⟨26889, by rfl⟩ (by norm_num))
theorem R71761 : Reach 71761 := rs (se 2 (by rfl) ⟨26910, by rfl⟩) (B 53821 (by norm_num) ⟨26910, by rfl⟩ (by norm_num))
theorem R137389 : Reach 137389 := rs (se 3 (by rfl) ⟨25760, by rfl⟩) (B 51521 (by norm_num) ⟨25760, by rfl⟩ (by norm_num))
theorem R71857 : Reach 71857 := rs (se 2 (by rfl) ⟨26946, by rfl⟩) (B 53893 (by norm_num) ⟨26946, by rfl⟩ (by norm_num))
theorem R72029 : Reach 72029 := rs (se 3 (by rfl) ⟨13505, by rfl⟩) (B 27011 (by norm_num) ⟨13505, by rfl⟩ (by norm_num))
theorem R72085 : Reach 72085 := rs (se 6 (by rfl) ⟨1689, by rfl⟩) (B 3379 (by norm_num) ⟨1689, by rfl⟩ (by norm_num))
theorem R104885 : Reach 104885 := rs (se 5 (by rfl) ⟨4916, by rfl⟩) (B 9833 (by norm_num) ⟨4916, by rfl⟩ (by norm_num))
theorem R72181 : Reach 72181 := rs (se 5 (by rfl) ⟨3383, by rfl⟩) (B 6767 (by norm_num) ⟨3383, by rfl⟩ (by norm_num))
theorem R268933 : Reach 268933 := rs (se 4 (by rfl) ⟨25212, by rfl⟩) (B 50425 (by norm_num) ⟨25212, by rfl⟩ (by norm_num))
theorem R72353 : Reach 72353 := rs (se 2 (by rfl) ⟨27132, by rfl⟩) (B 54265 (by norm_num) ⟨27132, by rfl⟩ (by norm_num))
theorem R400085 : Reach 400085 := rs (se 7 (by rfl) ⟨4688, by rfl⟩) (B 9377 (by norm_num) ⟨4688, by rfl⟩ (by norm_num))
theorem R72409 : Reach 72409 := rs (se 2 (by rfl) ⟨27153, by rfl⟩) (B 54307 (by norm_num) ⟨27153, by rfl⟩ (by norm_num))
theorem R105181 : Reach 105181 := rs (se 3 (by rfl) ⟨19721, by rfl⟩) (B 39443 (by norm_num) ⟨19721, by rfl⟩ (by norm_num))
theorem R72505 : Reach 72505 := rs (se 2 (by rfl) ⟨27189, by rfl⟩) (B 54379 (by norm_num) ⟨27189, by rfl⟩ (by norm_num))
theorem R72677 : Reach 72677 := rs (se 4 (by rfl) ⟨6813, by rfl⟩) (B 13627 (by norm_num) ⟨6813, by rfl⟩ (by norm_num))
theorem R72733 : Reach 72733 := rs (se 3 (by rfl) ⟨13637, by rfl⟩) (B 27275 (by norm_num) ⟨13637, by rfl⟩ (by norm_num))
theorem R72829 : Reach 72829 := rs (se 3 (by rfl) ⟨13655, by rfl⟩) (B 27311 (by norm_num) ⟨13655, by rfl⟩ (by norm_num))
theorem R105637 : Reach 105637 := rs (se 4 (by rfl) ⟨9903, by rfl⟩) (B 19807 (by norm_num) ⟨9903, by rfl⟩ (by norm_num))
theorem R236773 : Reach 236773 := rs (se 4 (by rfl) ⟨22197, by rfl⟩) (B 44395 (by norm_num) ⟨22197, by rfl⟩ (by norm_num))
theorem R73001 : Reach 73001 := rs (se 2 (by rfl) ⟨27375, by rfl⟩) (B 54751 (by norm_num) ⟨27375, by rfl⟩ (by norm_num))
theorem R105781 : Reach 105781 := rs (se 5 (by rfl) ⟨4958, by rfl⟩) (B 9917 (by norm_num) ⟨4958, by rfl⟩ (by norm_num))
theorem R73057 : Reach 73057 := rs (se 2 (by rfl) ⟨27396, by rfl⟩) (B 54793 (by norm_num) ⟨27396, by rfl⟩ (by norm_num))
theorem R73153 : Reach 73153 := rs (se 2 (by rfl) ⟨27432, by rfl⟩) (B 54865 (by norm_num) ⟨27432, by rfl⟩ (by norm_num))
theorem R105941 : Reach 105941 := rs (se 7 (by rfl) ⟨1241, by rfl⟩) (B 2483 (by norm_num) ⟨1241, by rfl⟩ (by norm_num))
theorem R73177 : Reach 73177 := rs (se 2 (by rfl) ⟨27441, by rfl⟩) (B 54883 (by norm_num) ⟨27441, by rfl⟩ (by norm_num))
theorem R138773 : Reach 138773 := rs (se 6 (by rfl) ⟨3252, by rfl⟩) (B 6505 (by norm_num) ⟨3252, by rfl⟩ (by norm_num))
theorem R138781 : Reach 138781 := rs (se 3 (by rfl) ⟨26021, by rfl⟩) (B 52043 (by norm_num) ⟨26021, by rfl⟩ (by norm_num))
theorem R106085 : Reach 106085 := rs (se 4 (by rfl) ⟨9945, by rfl⟩) (B 19891 (by norm_num) ⟨9945, by rfl⟩ (by norm_num))
theorem R73325 : Reach 73325 := rs (se 3 (by rfl) ⟨13748, by rfl⟩) (B 27497 (by norm_num) ⟨13748, by rfl⟩ (by norm_num))
theorem R73381 : Reach 73381 := rs (se 4 (by rfl) ⟨6879, by rfl⟩) (B 13759 (by norm_num) ⟨6879, by rfl⟩ (by norm_num))
theorem R73477 : Reach 73477 := rs (se 4 (by rfl) ⟨6888, by rfl⟩) (B 13777 (by norm_num) ⟨6888, by rfl⟩ (by norm_num))
theorem R106373 : Reach 106373 := rs (se 4 (by rfl) ⟨9972, by rfl⟩) (B 19945 (by norm_num) ⟨9972, by rfl⟩ (by norm_num))
theorem R434069 : Reach 434069 := rs (se 6 (by rfl) ⟨10173, by rfl⟩) (B 20347 (by norm_num) ⟨10173, by rfl⟩ (by norm_num))
theorem R106525 : Reach 106525 := rs (se 3 (by rfl) ⟨19973, by rfl⟩) (B 39947 (by norm_num) ⟨19973, by rfl⟩ (by norm_num))
theorem R106717 : Reach 106717 := rs (se 3 (by rfl) ⟨20009, by rfl⟩) (B 40019 (by norm_num) ⟨20009, by rfl⟩ (by norm_num))
theorem R73973 : Reach 73973 := rs (se 5 (by rfl) ⟨3467, by rfl⟩) (B 6935 (by norm_num) ⟨3467, by rfl⟩ (by norm_num))
theorem R74029 : Reach 74029 := rs (se 3 (by rfl) ⟨13880, by rfl⟩) (B 27761 (by norm_num) ⟨13880, by rfl⟩ (by norm_num))
theorem R106829 : Reach 106829 := rs (se 3 (by rfl) ⟨20030, by rfl⟩) (B 40061 (by norm_num) ⟨20030, by rfl⟩ (by norm_num))
theorem R74125 : Reach 74125 := rs (se 3 (by rfl) ⟨13898, by rfl⟩) (B 27797 (by norm_num) ⟨13898, by rfl⟩ (by norm_num))
theorem R237973 : Reach 237973 := rs (se 6 (by rfl) ⟨5577, by rfl⟩) (B 11155 (by norm_num) ⟨5577, by rfl⟩ (by norm_num))
theorem R139765 : Reach 139765 := rs (se 5 (by rfl) ⟨6551, by rfl⟩) (B 13103 (by norm_num) ⟨6551, by rfl⟩ (by norm_num))
theorem R139781 : Reach 139781 := rs (se 4 (by rfl) ⟨13104, by rfl⟩) (B 26209 (by norm_num) ⟨13104, by rfl⟩ (by norm_num))
theorem R139877 : Reach 139877 := rs (se 4 (by rfl) ⟨13113, by rfl⟩) (B 26227 (by norm_num) ⟨13113, by rfl⟩ (by norm_num))
theorem R140069 : Reach 140069 := rs (se 4 (by rfl) ⟨13131, by rfl⟩) (B 26263 (by norm_num) ⟨13131, by rfl⟩ (by norm_num))
theorem R107365 : Reach 107365 := rs (se 4 (by rfl) ⟨10065, by rfl⟩) (B 20131 (by norm_num) ⟨10065, by rfl⟩ (by norm_num))
theorem R74621 : Reach 74621 := rs (se 3 (by rfl) ⟨13991, by rfl⟩) (B 27983 (by norm_num) ⟨13991, by rfl⟩ (by norm_num))
theorem R74677 : Reach 74677 := rs (se 5 (by rfl) ⟨3500, by rfl⟩) (B 7001 (by norm_num) ⟨3500, by rfl⟩ (by norm_num))
theorem R74773 : Reach 74773 := rs (se 6 (by rfl) ⟨1752, by rfl⟩) (B 3505 (by norm_num) ⟨1752, by rfl⟩ (by norm_num))
theorem R107581 : Reach 107581 := rs (se 3 (by rfl) ⟨20171, by rfl⟩) (B 40343 (by norm_num) ⟨20171, by rfl⟩ (by norm_num))
theorem R140413 : Reach 140413 := rs (se 3 (by rfl) ⟨26327, by rfl⟩) (B 52655 (by norm_num) ⟨26327, by rfl⟩ (by norm_num))
theorem R107725 : Reach 107725 := rs (se 3 (by rfl) ⟨20198, by rfl⟩) (B 40397 (by norm_num) ⟨20198, by rfl⟩ (by norm_num))
theorem R140525 : Reach 140525 := rs (se 3 (by rfl) ⟨26348, by rfl⟩) (B 52697 (by norm_num) ⟨26348, by rfl⟩ (by norm_num))
theorem R533749 : Reach 533749 := rs (se 5 (by rfl) ⟨25019, by rfl⟩) (B 50039 (by norm_num) ⟨25019, by rfl⟩ (by norm_num))
theorem R140549 : Reach 140549 := rs (se 4 (by rfl) ⟨13176, by rfl⟩) (B 26353 (by norm_num) ⟨13176, by rfl⟩ (by norm_num))
theorem R107885 : Reach 107885 := rs (se 3 (by rfl) ⟨20228, by rfl⟩) (B 40457 (by norm_num) ⟨20228, by rfl⟩ (by norm_num))
theorem R140717 : Reach 140717 := rs (se 3 (by rfl) ⟨26384, by rfl⟩) (B 52769 (by norm_num) ⟨26384, by rfl⟩ (by norm_num))
theorem R108029 : Reach 108029 := rs (se 3 (by rfl) ⟨20255, by rfl⟩) (B 40511 (by norm_num) ⟨20255, by rfl⟩ (by norm_num))
theorem R141061 : Reach 141061 := rs (se 4 (by rfl) ⟨13224, by rfl⟩) (B 26449 (by norm_num) ⟨13224, by rfl⟩ (by norm_num))
theorem R108317 : Reach 108317 := rs (se 3 (by rfl) ⟨20309, by rfl⟩) (B 40619 (by norm_num) ⟨20309, by rfl⟩ (by norm_num))
theorem R141173 : Reach 141173 := rs (se 5 (by rfl) ⟨6617, by rfl⟩) (B 13235 (by norm_num) ⟨6617, by rfl⟩ (by norm_num))
theorem R141221 : Reach 141221 := rs (se 4 (by rfl) ⟨13239, by rfl⟩) (B 26479 (by norm_num) ⟨13239, by rfl⟩ (by norm_num))
theorem R108469 : Reach 108469 := rs (se 5 (by rfl) ⟨5084, by rfl⟩) (B 10169 (by norm_num) ⟨5084, by rfl⟩ (by norm_num))
theorem R141365 : Reach 141365 := rs (se 5 (by rfl) ⟨6626, by rfl⟩) (B 13253 (by norm_num) ⟨6626, by rfl⟩ (by norm_num))
theorem R108773 : Reach 108773 := rs (se 4 (by rfl) ⟨10197, by rfl⟩) (B 20395 (by norm_num) ⟨10197, by rfl⟩ (by norm_num))
theorem R698645 : Reach 698645 := rs (se 6 (by rfl) ⟨16374, by rfl⟩) (B 32749 (by norm_num) ⟨16374, by rfl⟩ (by norm_num))
theorem R141709 : Reach 141709 := rs (se 3 (by rfl) ⟨26570, by rfl⟩) (B 53141 (by norm_num) ⟨26570, by rfl⟩ (by norm_num))
theorem R141821 : Reach 141821 := rs (se 3 (by rfl) ⟨26591, by rfl⟩) (B 53183 (by norm_num) ⟨26591, by rfl⟩ (by norm_num))
theorem R404021 : Reach 404021 := rs (se 5 (by rfl) ⟨18938, by rfl⟩) (B 37877 (by norm_num) ⟨18938, by rfl⟩ (by norm_num))
theorem R404117 : Reach 404117 := rs (se 6 (by rfl) ⟨9471, by rfl⟩) (B 18943 (by norm_num) ⟨9471, by rfl⟩ (by norm_num))
theorem R142013 : Reach 142013 := rs (se 3 (by rfl) ⟨26627, by rfl⟩) (B 53255 (by norm_num) ⟨26627, by rfl⟩ (by norm_num))
theorem R109421 : Reach 109421 := rs (se 3 (by rfl) ⟨20516, by rfl⟩) (B 41033 (by norm_num) ⟨20516, by rfl⟩ (by norm_num))
theorem R109525 : Reach 109525 := rs (se 7 (by rfl) ⟨1283, by rfl⟩) (B 2567 (by norm_num) ⟨1283, by rfl⟩ (by norm_num))
theorem R76789 : Reach 76789 := rs (se 5 (by rfl) ⟨3599, by rfl⟩) (B 7199 (by norm_num) ⟨3599, by rfl⟩ (by norm_num))
theorem R142357 : Reach 142357 := rs (se 6 (by rfl) ⟨3336, by rfl⟩) (B 6673 (by norm_num) ⟨3336, by rfl⟩ (by norm_num))
theorem R339029 : Reach 339029 := rs (se 8 (by rfl) ⟨1986, by rfl⟩) (B 3973 (by norm_num) ⟨1986, by rfl⟩ (by norm_num))
theorem R109669 : Reach 109669 := rs (se 4 (by rfl) ⟨10281, by rfl⟩) (B 20563 (by norm_num) ⟨10281, by rfl⟩ (by norm_num))
theorem R142469 : Reach 142469 := rs (se 4 (by rfl) ⟨13356, by rfl⟩) (B 26713 (by norm_num) ⟨13356, by rfl⟩ (by norm_num))
theorem R797845 : Reach 797845 := rs (se 6 (by rfl) ⟨18699, by rfl⟩) (B 37399 (by norm_num) ⟨18699, by rfl⟩ (by norm_num))
theorem R109829 : Reach 109829 := rs (se 4 (by rfl) ⟨10296, by rfl⟩) (B 20593 (by norm_num) ⟨10296, by rfl⟩ (by norm_num))
theorem R109853 : Reach 109853 := rs (se 3 (by rfl) ⟨20597, by rfl⟩) (B 41195 (by norm_num) ⟨20597, by rfl⟩ (by norm_num))
theorem R142661 : Reach 142661 := rs (se 4 (by rfl) ⟨13374, by rfl⟩) (B 26749 (by norm_num) ⟨13374, by rfl⟩ (by norm_num))
theorem R240965 : Reach 240965 := rs (se 4 (by rfl) ⟨22590, by rfl⟩) (B 45181 (by norm_num) ⟨22590, by rfl⟩ (by norm_num))
theorem R109973 : Reach 109973 := rs (se 6 (by rfl) ⟨2577, by rfl⟩) (B 5155 (by norm_num) ⟨2577, by rfl⟩ (by norm_num))
theorem R142805 : Reach 142805 := rs (se 7 (by rfl) ⟨1673, by rfl⟩) (B 3347 (by norm_num) ⟨1673, by rfl⟩ (by norm_num))
theorem R143005 : Reach 143005 := rs (se 3 (by rfl) ⟨26813, by rfl⟩) (B 53627 (by norm_num) ⟨26813, by rfl⟩ (by norm_num))
theorem R110261 : Reach 110261 := rs (se 5 (by rfl) ⟨5168, by rfl⟩) (B 10337 (by norm_num) ⟨5168, by rfl⟩ (by norm_num))
theorem R143117 : Reach 143117 := rs (se 3 (by rfl) ⟨26834, by rfl⟩) (B 53669 (by norm_num) ⟨26834, by rfl⟩ (by norm_num))
theorem R306965 : Reach 306965 := rs (se 6 (by rfl) ⟨7194, by rfl⟩) (B 14389 (by norm_num) ⟨7194, by rfl⟩ (by norm_num))
theorem R110413 : Reach 110413 := rs (se 3 (by rfl) ⟨20702, by rfl⟩) (B 41405 (by norm_num) ⟨20702, by rfl⟩ (by norm_num))
theorem R143309 : Reach 143309 := rs (se 3 (by rfl) ⟨26870, by rfl⟩) (B 53741 (by norm_num) ⟨26870, by rfl⟩ (by norm_num))
theorem R143317 : Reach 143317 := rs (se 7 (by rfl) ⟨1679, by rfl⟩) (B 3359 (by norm_num) ⟨1679, by rfl⟩ (by norm_num))
theorem R110717 : Reach 110717 := rs (se 3 (by rfl) ⟨20759, by rfl⟩) (B 41519 (by norm_num) ⟨20759, by rfl⟩ (by norm_num))
theorem R307381 : Reach 307381 := rs (se 5 (by rfl) ⟨14408, by rfl⟩) (B 28817 (by norm_num) ⟨14408, by rfl⟩ (by norm_num))
theorem R110837 : Reach 110837 := rs (se 5 (by rfl) ⟨5195, by rfl⟩) (B 10391 (by norm_num) ⟨5195, by rfl⟩ (by norm_num))
theorem R143653 : Reach 143653 := rs (se 4 (by rfl) ⟨13467, by rfl⟩) (B 26935 (by norm_num) ⟨13467, by rfl⟩ (by norm_num))
theorem R241973 : Reach 241973 := rs (se 5 (by rfl) ⟨11342, by rfl⟩) (B 22685 (by norm_num) ⟨11342, by rfl⟩ (by norm_num))
theorem R143765 : Reach 143765 := rs (se 6 (by rfl) ⟨3369, by rfl⟩) (B 6739 (by norm_num) ⟨3369, by rfl⟩ (by norm_num))
theorem R209429 : Reach 209429 := rs (se 6 (by rfl) ⟨4908, by rfl⟩) (B 9817 (by norm_num) ⟨4908, by rfl⟩ (by norm_num))
theorem R78413 : Reach 78413 := rs (se 3 (by rfl) ⟨14702, by rfl⟩) (B 29405 (by norm_num) ⟨14702, by rfl⟩ (by norm_num))
theorem R143957 : Reach 143957 := rs (se 8 (by rfl) ⟨843, by rfl⟩) (B 1687 (by norm_num) ⟨843, by rfl⟩ (by norm_num))
theorem R78445 : Reach 78445 := rs (se 3 (by rfl) ⟨14708, by rfl⟩) (B 29417 (by norm_num) ⟨14708, by rfl⟩ (by norm_num))
theorem R209573 : Reach 209573 := rs (se 4 (by rfl) ⟨19647, by rfl⟩) (B 39295 (by norm_num) ⟨19647, by rfl⟩ (by norm_num))
theorem R111469 : Reach 111469 := rs (se 3 (by rfl) ⟨20900, by rfl⟩) (B 41801 (by norm_num) ⟨20900, by rfl⟩ (by norm_num))
theorem R144301 : Reach 144301 := rs (se 3 (by rfl) ⟨27056, by rfl⟩) (B 54113 (by norm_num) ⟨27056, by rfl⟩ (by norm_num))
theorem R209861 : Reach 209861 := rs (se 4 (by rfl) ⟨19674, by rfl⟩) (B 39349 (by norm_num) ⟨19674, by rfl⟩ (by norm_num))
theorem R111613 : Reach 111613 := rs (se 3 (by rfl) ⟨20927, by rfl⟩) (B 41855 (by norm_num) ⟨20927, by rfl⟩ (by norm_num))
theorem R472085 : Reach 472085 := rs (se 6 (by rfl) ⟨11064, by rfl⟩) (B 22129 (by norm_num) ⟨11064, by rfl⟩ (by norm_num))
theorem R144413 : Reach 144413 := rs (se 3 (by rfl) ⟨27077, by rfl⟩) (B 54155 (by norm_num) ⟨27077, by rfl⟩ (by norm_num))
theorem R111773 : Reach 111773 := rs (se 3 (by rfl) ⟨20957, by rfl⟩) (B 41915 (by norm_num) ⟨20957, by rfl⟩ (by norm_num))
theorem R144605 : Reach 144605 := rs (se 3 (by rfl) ⟨27113, by rfl⟩) (B 54227 (by norm_num) ⟨27113, by rfl⟩ (by norm_num))
theorem R275717 : Reach 275717 := rs (se 4 (by rfl) ⟨25848, by rfl⟩) (B 51697 (by norm_num) ⟨25848, by rfl⟩ (by norm_num))
theorem R111917 : Reach 111917 := rs (se 3 (by rfl) ⟨20984, by rfl⟩) (B 41969 (by norm_num) ⟨20984, by rfl⟩ (by norm_num))
theorem R79165 : Reach 79165 := rs (se 3 (by rfl) ⟨14843, by rfl⟩) (B 29687 (by norm_num) ⟨14843, by rfl⟩ (by norm_num))
theorem R177557 : Reach 177557 := rs (se 6 (by rfl) ⟨4161, by rfl⟩) (B 8323 (by norm_num) ⟨4161, by rfl⟩ (by norm_num))
theorem R79373 : Reach 79373 := rs (se 3 (by rfl) ⟨14882, by rfl⟩) (B 29765 (by norm_num) ⟨14882, by rfl⟩ (by norm_num))
theorem R439829 : Reach 439829 := rs (se 6 (by rfl) ⟨10308, by rfl⟩) (B 20617 (by norm_num) ⟨10308, by rfl⟩ (by norm_num))
theorem R144949 : Reach 144949 := rs (se 5 (by rfl) ⟨6794, by rfl⟩) (B 13589 (by norm_num) ⟨6794, by rfl⟩ (by norm_num))
theorem R112205 : Reach 112205 := rs (se 3 (by rfl) ⟨21038, by rfl⟩) (B 42077 (by norm_num) ⟨21038, by rfl⟩ (by norm_num))
theorem R112261 : Reach 112261 := rs (se 4 (by rfl) ⟨10524, by rfl⟩) (B 21049 (by norm_num) ⟨10524, by rfl⟩ (by norm_num))
theorem R145061 : Reach 145061 := rs (se 4 (by rfl) ⟨13599, by rfl⟩) (B 27199 (by norm_num) ⟨13599, by rfl⟩ (by norm_num))
theorem R145253 : Reach 145253 := rs (se 4 (by rfl) ⟨13617, by rfl⟩) (B 27235 (by norm_num) ⟨13617, by rfl⟩ (by norm_num))
theorem R374645 : Reach 374645 := rs (se 5 (by rfl) ⟨17561, by rfl⟩) (B 35123 (by norm_num) ⟨17561, by rfl⟩ (by norm_num))
theorem R538613 : Reach 538613 := rs (se 5 (by rfl) ⟨25247, by rfl⟩) (B 50495 (by norm_num) ⟨25247, by rfl⟩ (by norm_num))
theorem R276517 : Reach 276517 := rs (se 4 (by rfl) ⟨25923, by rfl⟩) (B 51847 (by norm_num) ⟨25923, by rfl⟩ (by norm_num))
theorem R243749 : Reach 243749 := rs (se 4 (by rfl) ⟨22851, by rfl⟩) (B 45703 (by norm_num) ⟨22851, by rfl⟩ (by norm_num))
theorem R79957 : Reach 79957 := rs (se 8 (by rfl) ⟨468, by rfl⟩) (B 937 (by norm_num) ⟨468, by rfl⟩ (by norm_num))
theorem R211045 : Reach 211045 := rs (se 4 (by rfl) ⟨19785, by rfl⟩) (B 39571 (by norm_num) ⟨19785, by rfl⟩ (by norm_num))
theorem R145597 : Reach 145597 := rs (se 3 (by rfl) ⟨27299, by rfl⟩) (B 54599 (by norm_num) ⟨27299, by rfl⟩ (by norm_num))
theorem R178469 : Reach 178469 := rs (se 4 (by rfl) ⟨16731, by rfl⟩) (B 33463 (by norm_num) ⟨16731, by rfl⟩ (by norm_num))
theorem R145709 : Reach 145709 := rs (se 3 (by rfl) ⟨27320, by rfl⟩) (B 54641 (by norm_num) ⟨27320, by rfl⟩ (by norm_num))
theorem R211285 : Reach 211285 := rs (se 10 (by rfl) ⟨309, by rfl⟩) (B 619 (by norm_num) ⟨309, by rfl⟩ (by norm_num))
theorem R211349 : Reach 211349 := rs (se 6 (by rfl) ⟨4953, by rfl⟩) (B 9907 (by norm_num) ⟨4953, by rfl⟩ (by norm_num))
theorem R80293 : Reach 80293 := rs (se 4 (by rfl) ⟨7527, by rfl⟩) (B 15055 (by norm_num) ⟨7527, by rfl⟩ (by norm_num))
theorem R145901 : Reach 145901 := rs (se 3 (by rfl) ⟨27356, by rfl⟩) (B 54713 (by norm_num) ⟨27356, by rfl⟩ (by norm_num))
theorem R80509 : Reach 80509 := rs (se 3 (by rfl) ⟨15095, by rfl⟩) (B 30191 (by norm_num) ⟨15095, by rfl⟩ (by norm_num))
theorem R277141 : Reach 277141 := rs (se 6 (by rfl) ⟨6495, by rfl⟩) (B 12991 (by norm_num) ⟨6495, by rfl⟩ (by norm_num))
theorem R146245 : Reach 146245 := rs (se 4 (by rfl) ⟨13710, by rfl⟩) (B 27421 (by norm_num) ⟨13710, by rfl⟩ (by norm_num))
theorem R113485 : Reach 113485 := rs (se 3 (by rfl) ⟨21278, by rfl⟩) (B 42557 (by norm_num) ⟨21278, by rfl⟩ (by norm_num))
theorem R146357 : Reach 146357 := rs (se 5 (by rfl) ⟨6860, by rfl⟩) (B 13721 (by norm_num) ⟨6860, by rfl⟩ (by norm_num))
theorem R80885 : Reach 80885 := rs (se 5 (by rfl) ⟨3791, by rfl⟩) (B 7583 (by norm_num) ⟨3791, by rfl⟩ (by norm_num))
theorem R146549 : Reach 146549 := rs (se 5 (by rfl) ⟨6869, by rfl⟩) (B 13739 (by norm_num) ⟨6869, by rfl⟩ (by norm_num))
theorem R540053 : Reach 540053 := rs (se 6 (by rfl) ⟨12657, by rfl⟩) (B 25315 (by norm_num) ⟨12657, by rfl⟩ (by norm_num))
theorem R146893 : Reach 146893 := rs (se 3 (by rfl) ⟨27542, by rfl⟩) (B 55085 (by norm_num) ⟨27542, by rfl⟩ (by norm_num))
theorem R179813 : Reach 179813 := rs (se 4 (by rfl) ⟨16857, by rfl⟩) (B 33715 (by norm_num) ⟨16857, by rfl⟩ (by norm_num))
theorem R245413 : Reach 245413 := rs (se 4 (by rfl) ⟨23007, by rfl⟩) (B 46015 (by norm_num) ⟨23007, by rfl⟩ (by norm_num))
theorem R114389 : Reach 114389 := rs (se 7 (by rfl) ⟨1340, by rfl⟩) (B 2681 (by norm_num) ⟨1340, by rfl⟩ (by norm_num))
theorem R114437 : Reach 114437 := rs (se 4 (by rfl) ⟨10728, by rfl⟩) (B 21457 (by norm_num) ⟨10728, by rfl⟩ (by norm_num))
theorem R540437 : Reach 540437 := rs (se 6 (by rfl) ⟨12666, by rfl⟩) (B 25333 (by norm_num) ⟨12666, by rfl⟩ (by norm_num))
theorem R147541 : Reach 147541 := rs (se 8 (by rfl) ⟨864, by rfl⟩) (B 1729 (by norm_num) ⟨864, by rfl⟩ (by norm_num))
theorem R147653 : Reach 147653 := rs (se 4 (by rfl) ⟨13842, by rfl⟩) (B 27685 (by norm_num) ⟨13842, by rfl⟩ (by norm_num))
theorem R115021 : Reach 115021 := rs (se 3 (by rfl) ⟨21566, by rfl⟩) (B 43133 (by norm_num) ⟨21566, by rfl⟩ (by norm_num))
theorem R82301 : Reach 82301 := rs (se 3 (by rfl) ⟨15431, by rfl⟩) (B 30863 (by norm_num) ⟨15431, by rfl⟩ (by norm_num))
theorem R82309 : Reach 82309 := rs (se 4 (by rfl) ⟨7716, by rfl⟩) (B 15433 (by norm_num) ⟨7716, by rfl⟩ (by norm_num))
theorem R147845 : Reach 147845 := rs (se 4 (by rfl) ⟨13860, by rfl⟩) (B 27721 (by norm_num) ⟨13860, by rfl⟩ (by norm_num))
theorem R213461 : Reach 213461 := rs (se 7 (by rfl) ⟨2501, by rfl⟩) (B 5003 (by norm_num) ⟨2501, by rfl⟩ (by norm_num))
theorem R279125 : Reach 279125 := rs (se 8 (by rfl) ⟨1635, by rfl⟩) (B 3271 (by norm_num) ⟨1635, by rfl⟩ (by norm_num))
theorem R311957 : Reach 311957 := rs (se 6 (by rfl) ⟨7311, by rfl⟩) (B 14623 (by norm_num) ⟨7311, by rfl⟩ (by norm_num))
theorem R213749 : Reach 213749 := rs (se 5 (by rfl) ⟨10019, by rfl⟩) (B 20039 (by norm_num) ⟨10019, by rfl⟩ (by norm_num))
theorem R82685 : Reach 82685 := rs (se 3 (by rfl) ⟨15503, by rfl⟩) (B 31007 (by norm_num) ⟨15503, by rfl⟩ (by norm_num))
theorem R82709 : Reach 82709 := rs (se 6 (by rfl) ⟨1938, by rfl⟩) (B 3877 (by norm_num) ⟨1938, by rfl⟩ (by norm_num))
theorem R82733 : Reach 82733 := rs (se 3 (by rfl) ⟨15512, by rfl⟩) (B 31025 (by norm_num) ⟨15512, by rfl⟩ (by norm_num))
theorem R82757 : Reach 82757 := rs (se 4 (by rfl) ⟨7758, by rfl⟩) (B 15517 (by norm_num) ⟨7758, by rfl⟩ (by norm_num))
theorem R82781 : Reach 82781 := rs (se 3 (by rfl) ⟨15521, by rfl⟩) (B 31043 (by norm_num) ⟨15521, by rfl⟩ (by norm_num))
theorem R82805 : Reach 82805 := rs (se 5 (by rfl) ⟨3881, by rfl⟩) (B 7763 (by norm_num) ⟨3881, by rfl⟩ (by norm_num))
theorem R82829 : Reach 82829 := rs (se 3 (by rfl) ⟨15530, by rfl⟩) (B 31061 (by norm_num) ⟨15530, by rfl⟩ (by norm_num))
theorem R82853 : Reach 82853 := rs (se 4 (by rfl) ⟨7767, by rfl⟩) (B 15535 (by norm_num) ⟨7767, by rfl⟩ (by norm_num))
theorem R82877 : Reach 82877 := rs (se 3 (by rfl) ⟨15539, by rfl⟩) (B 31079 (by norm_num) ⟨15539, by rfl⟩ (by norm_num))
theorem R82901 : Reach 82901 := rs (se 7 (by rfl) ⟨971, by rfl⟩) (B 1943 (by norm_num) ⟨971, by rfl⟩ (by norm_num))
theorem R82925 : Reach 82925 := rs (se 3 (by rfl) ⟨15548, by rfl⟩) (B 31097 (by norm_num) ⟨15548, by rfl⟩ (by norm_num))
theorem R181237 : Reach 181237 := rs (se 5 (by rfl) ⟨8495, by rfl⟩) (B 16991 (by norm_num) ⟨8495, by rfl⟩ (by norm_num))
theorem R82949 : Reach 82949 := rs (se 4 (by rfl) ⟨7776, by rfl⟩) (B 15553 (by norm_num) ⟨7776, by rfl⟩ (by norm_num))
theorem R82973 : Reach 82973 := rs (se 3 (by rfl) ⟨15557, by rfl⟩) (B 31115 (by norm_num) ⟨15557, by rfl⟩ (by norm_num))
theorem R82981 : Reach 82981 := rs (se 4 (by rfl) ⟨7779, by rfl⟩) (B 15559 (by norm_num) ⟨7779, by rfl⟩ (by norm_num))
theorem R82997 : Reach 82997 := rs (se 5 (by rfl) ⟨3890, by rfl⟩) (B 7781 (by norm_num) ⟨3890, by rfl⟩ (by norm_num))
theorem R83021 : Reach 83021 := rs (se 3 (by rfl) ⟨15566, by rfl⟩) (B 31133 (by norm_num) ⟨15566, by rfl⟩ (by norm_num))
theorem R83045 : Reach 83045 := rs (se 4 (by rfl) ⟨7785, by rfl⟩) (B 15571 (by norm_num) ⟨7785, by rfl⟩ (by norm_num))
theorem R83069 : Reach 83069 := rs (se 3 (by rfl) ⟨15575, by rfl⟩) (B 31151 (by norm_num) ⟨15575, by rfl⟩ (by norm_num))
theorem R83093 : Reach 83093 := rs (se 6 (by rfl) ⟨1947, by rfl⟩) (B 3895 (by norm_num) ⟨1947, by rfl⟩ (by norm_num))
theorem R181397 : Reach 181397 := rs (se 6 (by rfl) ⟨4251, by rfl⟩) (B 8503 (by norm_num) ⟨4251, by rfl⟩ (by norm_num))
theorem R83101 : Reach 83101 := rs (se 3 (by rfl) ⟨15581, by rfl⟩) (B 31163 (by norm_num) ⟨15581, by rfl⟩ (by norm_num))
theorem R83117 : Reach 83117 := rs (se 3 (by rfl) ⟨15584, by rfl⟩) (B 31169 (by norm_num) ⟨15584, by rfl⟩ (by norm_num))
theorem R83141 : Reach 83141 := rs (se 4 (by rfl) ⟨7794, by rfl⟩) (B 15589 (by norm_num) ⟨7794, by rfl⟩ (by norm_num))
theorem R83165 : Reach 83165 := rs (se 3 (by rfl) ⟨15593, by rfl⟩) (B 31187 (by norm_num) ⟨15593, by rfl⟩ (by norm_num))
theorem R83189 : Reach 83189 := rs (se 5 (by rfl) ⟨3899, by rfl⟩) (B 7799 (by norm_num) ⟨3899, by rfl⟩ (by norm_num))
theorem R83197 : Reach 83197 := rs (se 3 (by rfl) ⟨15599, by rfl⟩) (B 31199 (by norm_num) ⟨15599, by rfl⟩ (by norm_num))
theorem R83213 : Reach 83213 := rs (se 3 (by rfl) ⟨15602, by rfl⟩) (B 31205 (by norm_num) ⟨15602, by rfl⟩ (by norm_num))
theorem R83237 : Reach 83237 := rs (se 4 (by rfl) ⟨7803, by rfl⟩) (B 15607 (by norm_num) ⟨7803, by rfl⟩ (by norm_num))
theorem R83261 : Reach 83261 := rs (se 3 (by rfl) ⟨15611, by rfl⟩) (B 31223 (by norm_num) ⟨15611, by rfl⟩ (by norm_num))
theorem R83285 : Reach 83285 := rs (se 12 (by rfl) ⟨30, by rfl⟩) (B 61 (by norm_num) ⟨30, by rfl⟩ (by norm_num))
theorem R148837 : Reach 148837 := rs (se 4 (by rfl) ⟨13953, by rfl⟩) (B 27907 (by norm_num) ⟨13953, by rfl⟩ (by norm_num))
theorem R83309 : Reach 83309 := rs (se 3 (by rfl) ⟨15620, by rfl⟩) (B 31241 (by norm_num) ⟨15620, by rfl⟩ (by norm_num))
theorem R83333 : Reach 83333 := rs (se 4 (by rfl) ⟨7812, by rfl⟩) (B 15625 (by norm_num) ⟨7812, by rfl⟩ (by norm_num))
theorem R83357 : Reach 83357 := rs (se 3 (by rfl) ⟨15629, by rfl⟩) (B 31259 (by norm_num) ⟨15629, by rfl⟩ (by norm_num))
theorem R83381 : Reach 83381 := rs (se 5 (by rfl) ⟨3908, by rfl⟩) (B 7817 (by norm_num) ⟨3908, by rfl⟩ (by norm_num))
theorem R83405 : Reach 83405 := rs (se 3 (by rfl) ⟨15638, by rfl⟩) (B 31277 (by norm_num) ⟨15638, by rfl⟩ (by norm_num))
theorem R148949 : Reach 148949 := rs (se 7 (by rfl) ⟨1745, by rfl⟩) (B 3491 (by norm_num) ⟨1745, by rfl⟩ (by norm_num))
theorem R83429 : Reach 83429 := rs (se 4 (by rfl) ⟨7821, by rfl⟩) (B 15643 (by norm_num) ⟨7821, by rfl⟩ (by norm_num))
theorem R83453 : Reach 83453 := rs (se 3 (by rfl) ⟨15647, by rfl⟩) (B 31295 (by norm_num) ⟨15647, by rfl⟩ (by norm_num))
theorem R83477 : Reach 83477 := rs (se 6 (by rfl) ⟨1956, by rfl⟩) (B 3913 (by norm_num) ⟨1956, by rfl⟩ (by norm_num))
theorem R83501 : Reach 83501 := rs (se 3 (by rfl) ⟨15656, by rfl⟩) (B 31313 (by norm_num) ⟨15656, by rfl⟩ (by norm_num))
theorem R83525 : Reach 83525 := rs (se 4 (by rfl) ⟨7830, by rfl⟩) (B 15661 (by norm_num) ⟨7830, by rfl⟩ (by norm_num))
theorem R83549 : Reach 83549 := rs (se 3 (by rfl) ⟨15665, by rfl⟩) (B 31331 (by norm_num) ⟨15665, by rfl⟩ (by norm_num))
theorem R83573 : Reach 83573 := rs (se 5 (by rfl) ⟨3917, by rfl⟩) (B 7835 (by norm_num) ⟨3917, by rfl⟩ (by norm_num))
theorem R83597 : Reach 83597 := rs (se 3 (by rfl) ⟨15674, by rfl⟩) (B 31349 (by norm_num) ⟨15674, by rfl⟩ (by norm_num))
theorem R149141 : Reach 149141 := rs (se 6 (by rfl) ⟨3495, by rfl⟩) (B 6991 (by norm_num) ⟨3495, by rfl⟩ (by norm_num))
theorem R83621 : Reach 83621 := rs (se 4 (by rfl) ⟨7839, by rfl⟩) (B 15679 (by norm_num) ⟨7839, by rfl⟩ (by norm_num))
theorem R83645 : Reach 83645 := rs (se 3 (by rfl) ⟨15683, by rfl⟩) (B 31367 (by norm_num) ⟨15683, by rfl⟩ (by norm_num))
theorem R83669 : Reach 83669 := rs (se 7 (by rfl) ⟨980, by rfl⟩) (B 1961 (by norm_num) ⟨980, by rfl⟩ (by norm_num))
theorem R83693 : Reach 83693 := rs (se 3 (by rfl) ⟨15692, by rfl⟩) (B 31385 (by norm_num) ⟨15692, by rfl⟩ (by norm_num))
theorem R83717 : Reach 83717 := rs (se 4 (by rfl) ⟨7848, by rfl⟩) (B 15697 (by norm_num) ⟨7848, by rfl⟩ (by norm_num))
theorem R83741 : Reach 83741 := rs (se 3 (by rfl) ⟨15701, by rfl⟩) (B 31403 (by norm_num) ⟨15701, by rfl⟩ (by norm_num))
theorem R83765 : Reach 83765 := rs (se 5 (by rfl) ⟨3926, by rfl⟩) (B 7853 (by norm_num) ⟨3926, by rfl⟩ (by norm_num))
theorem R83789 : Reach 83789 := rs (se 3 (by rfl) ⟨15710, by rfl⟩) (B 31421 (by norm_num) ⟨15710, by rfl⟩ (by norm_num))
theorem R345941 : Reach 345941 := rs (se 9 (by rfl) ⟨1013, by rfl⟩) (B 2027 (by norm_num) ⟨1013, by rfl⟩ (by norm_num))
theorem R280421 : Reach 280421 := rs (se 4 (by rfl) ⟨26289, by rfl⟩) (B 52579 (by norm_num) ⟨26289, by rfl⟩ (by norm_num))
theorem R83813 : Reach 83813 := rs (se 4 (by rfl) ⟨7857, by rfl⟩) (B 15715 (by norm_num) ⟨7857, by rfl⟩ (by norm_num))
theorem R83837 : Reach 83837 := rs (se 3 (by rfl) ⟨15719, by rfl⟩) (B 31439 (by norm_num) ⟨15719, by rfl⟩ (by norm_num))
theorem R83861 : Reach 83861 := rs (se 6 (by rfl) ⟨1965, by rfl⟩) (B 3931 (by norm_num) ⟨1965, by rfl⟩ (by norm_num))
theorem R214933 : Reach 214933 := rs (se 6 (by rfl) ⟨5037, by rfl⟩) (B 10075 (by norm_num) ⟨5037, by rfl⟩ (by norm_num))
theorem R83885 : Reach 83885 := rs (se 3 (by rfl) ⟨15728, by rfl⟩) (B 31457 (by norm_num) ⟨15728, by rfl⟩ (by norm_num))
theorem R83909 : Reach 83909 := rs (se 4 (by rfl) ⟨7866, by rfl⟩) (B 15733 (by norm_num) ⟨7866, by rfl⟩ (by norm_num))
theorem R83933 : Reach 83933 := rs (se 3 (by rfl) ⟨15737, by rfl⟩) (B 31475 (by norm_num) ⟨15737, by rfl⟩ (by norm_num))
theorem R83957 : Reach 83957 := rs (se 5 (by rfl) ⟨3935, by rfl⟩) (B 7871 (by norm_num) ⟨3935, by rfl⟩ (by norm_num))
theorem R116741 : Reach 116741 := rs (se 4 (by rfl) ⟨10944, by rfl⟩) (B 21889 (by norm_num) ⟨10944, by rfl⟩ (by norm_num))
theorem R83981 : Reach 83981 := rs (se 3 (by rfl) ⟨15746, by rfl⟩) (B 31493 (by norm_num) ⟨15746, by rfl⟩ (by norm_num))
theorem R84005 : Reach 84005 := rs (se 4 (by rfl) ⟨7875, by rfl⟩) (B 15751 (by norm_num) ⟨7875, by rfl⟩ (by norm_num))
theorem R84029 : Reach 84029 := rs (se 3 (by rfl) ⟨15755, by rfl⟩) (B 31511 (by norm_num) ⟨15755, by rfl⟩ (by norm_num))
theorem R84053 : Reach 84053 := rs (se 8 (by rfl) ⟨492, by rfl⟩) (B 985 (by norm_num) ⟨492, by rfl⟩ (by norm_num))
theorem R84077 : Reach 84077 := rs (se 3 (by rfl) ⟨15764, by rfl⟩) (B 31529 (by norm_num) ⟨15764, by rfl⟩ (by norm_num))
theorem R84101 : Reach 84101 := rs (se 4 (by rfl) ⟨7884, by rfl⟩) (B 15769 (by norm_num) ⟨7884, by rfl⟩ (by norm_num))
theorem R84125 : Reach 84125 := rs (se 3 (by rfl) ⟨15773, by rfl⟩) (B 31547 (by norm_num) ⟨15773, by rfl⟩ (by norm_num))
theorem R84149 : Reach 84149 := rs (se 5 (by rfl) ⟨3944, by rfl⟩) (B 7889 (by norm_num) ⟨3944, by rfl⟩ (by norm_num))
theorem R215237 : Reach 215237 := rs (se 4 (by rfl) ⟨20178, by rfl⟩) (B 40357 (by norm_num) ⟨20178, by rfl⟩ (by norm_num))
theorem R84173 : Reach 84173 := rs (se 3 (by rfl) ⟨15782, by rfl⟩) (B 31565 (by norm_num) ⟨15782, by rfl⟩ (by norm_num))
theorem R248021 : Reach 248021 := rs (se 7 (by rfl) ⟨2906, by rfl⟩) (B 5813 (by norm_num) ⟨2906, by rfl⟩ (by norm_num))
theorem R84197 : Reach 84197 := rs (se 4 (by rfl) ⟨7893, by rfl⟩) (B 15787 (by norm_num) ⟨7893, by rfl⟩ (by norm_num))
theorem R84221 : Reach 84221 := rs (se 3 (by rfl) ⟨15791, by rfl⟩) (B 31583 (by norm_num) ⟨15791, by rfl⟩ (by norm_num))
theorem R84245 : Reach 84245 := rs (se 6 (by rfl) ⟨1974, by rfl⟩) (B 3949 (by norm_num) ⟨1974, by rfl⟩ (by norm_num))
theorem R84269 : Reach 84269 := rs (se 3 (by rfl) ⟨15800, by rfl⟩) (B 31601 (by norm_num) ⟨15800, by rfl⟩ (by norm_num))
theorem R84293 : Reach 84293 := rs (se 4 (by rfl) ⟨7902, by rfl⟩) (B 15805 (by norm_num) ⟨7902, by rfl⟩ (by norm_num))
theorem R84317 : Reach 84317 := rs (se 3 (by rfl) ⟨15809, by rfl⟩) (B 31619 (by norm_num) ⟨15809, by rfl⟩ (by norm_num))
theorem R84341 : Reach 84341 := rs (se 5 (by rfl) ⟨3953, by rfl⟩) (B 7907 (by norm_num) ⟨3953, by rfl⟩ (by norm_num))
theorem R84365 : Reach 84365 := rs (se 3 (by rfl) ⟨15818, by rfl⟩) (B 31637 (by norm_num) ⟨15818, by rfl⟩ (by norm_num))
theorem R84389 : Reach 84389 := rs (se 4 (by rfl) ⟨7911, by rfl⟩) (B 15823 (by norm_num) ⟨7911, by rfl⟩ (by norm_num))
theorem R84413 : Reach 84413 := rs (se 3 (by rfl) ⟨15827, by rfl⟩) (B 31655 (by norm_num) ⟨15827, by rfl⟩ (by norm_num))
theorem R84437 : Reach 84437 := rs (se 7 (by rfl) ⟨989, by rfl⟩) (B 1979 (by norm_num) ⟨989, by rfl⟩ (by norm_num))
theorem R84461 : Reach 84461 := rs (se 3 (by rfl) ⟨15836, by rfl⟩) (B 31673 (by norm_num) ⟨15836, by rfl⟩ (by norm_num))
theorem R84485 : Reach 84485 := rs (se 4 (by rfl) ⟨7920, by rfl⟩) (B 15841 (by norm_num) ⟨7920, by rfl⟩ (by norm_num))
theorem R84509 : Reach 84509 := rs (se 3 (by rfl) ⟨15845, by rfl⟩) (B 31691 (by norm_num) ⟨15845, by rfl⟩ (by norm_num))
theorem R84533 : Reach 84533 := rs (se 5 (by rfl) ⟨3962, by rfl⟩) (B 7925 (by norm_num) ⟨3962, by rfl⟩ (by norm_num))
theorem R182837 : Reach 182837 := rs (se 5 (by rfl) ⟨8570, by rfl⟩) (B 17141 (by norm_num) ⟨8570, by rfl⟩ (by norm_num))
theorem R84557 : Reach 84557 := rs (se 3 (by rfl) ⟨15854, by rfl⟩) (B 31709 (by norm_num) ⟨15854, by rfl⟩ (by norm_num))
theorem R84581 : Reach 84581 := rs (se 4 (by rfl) ⟨7929, by rfl⟩) (B 15859 (by norm_num) ⟨7929, by rfl⟩ (by norm_num))
theorem R84605 : Reach 84605 := rs (se 3 (by rfl) ⟨15863, by rfl⟩) (B 31727 (by norm_num) ⟨15863, by rfl⟩ (by norm_num))
theorem R84629 : Reach 84629 := rs (se 6 (by rfl) ⟨1983, by rfl⟩) (B 3967 (by norm_num) ⟨1983, by rfl⟩ (by norm_num))
theorem R84653 : Reach 84653 := rs (se 3 (by rfl) ⟨15872, by rfl⟩) (B 31745 (by norm_num) ⟨15872, by rfl⟩ (by norm_num))
theorem R84677 : Reach 84677 := rs (se 4 (by rfl) ⟨7938, by rfl⟩) (B 15877 (by norm_num) ⟨7938, by rfl⟩ (by norm_num))
theorem R84701 : Reach 84701 := rs (se 3 (by rfl) ⟨15881, by rfl⟩) (B 31763 (by norm_num) ⟨15881, by rfl⟩ (by norm_num))
theorem R84725 : Reach 84725 := rs (se 5 (by rfl) ⟨3971, by rfl⟩) (B 7943 (by norm_num) ⟨3971, by rfl⟩ (by norm_num))
theorem R84749 : Reach 84749 := rs (se 3 (by rfl) ⟨15890, by rfl⟩) (B 31781 (by norm_num) ⟨15890, by rfl⟩ (by norm_num))
theorem R84773 : Reach 84773 := rs (se 4 (by rfl) ⟨7947, by rfl⟩) (B 15895 (by norm_num) ⟨7947, by rfl⟩ (by norm_num))
theorem R84797 : Reach 84797 := rs (se 3 (by rfl) ⟨15899, by rfl⟩) (B 31799 (by norm_num) ⟨15899, by rfl⟩ (by norm_num))
theorem R84821 : Reach 84821 := rs (se 9 (by rfl) ⟨248, by rfl⟩) (B 497 (by norm_num) ⟨248, by rfl⟩ (by norm_num))
theorem R84845 : Reach 84845 := rs (se 3 (by rfl) ⟨15908, by rfl⟩) (B 31817 (by norm_num) ⟨15908, by rfl⟩ (by norm_num))
theorem R84869 : Reach 84869 := rs (se 4 (by rfl) ⟨7956, by rfl⟩) (B 15913 (by norm_num) ⟨7956, by rfl⟩ (by norm_num))
theorem R84893 : Reach 84893 := rs (se 3 (by rfl) ⟨15917, by rfl⟩) (B 31835 (by norm_num) ⟨15917, by rfl⟩ (by norm_num))
theorem R478133 : Reach 478133 := rs (se 5 (by rfl) ⟨22412, by rfl⟩) (B 44825 (by norm_num) ⟨22412, by rfl⟩ (by norm_num))
theorem R84917 : Reach 84917 := rs (se 5 (by rfl) ⟨3980, by rfl⟩) (B 7961 (by norm_num) ⟨3980, by rfl⟩ (by norm_num))
theorem R84941 : Reach 84941 := rs (se 3 (by rfl) ⟨15926, by rfl⟩) (B 31853 (by norm_num) ⟨15926, by rfl⟩ (by norm_num))
theorem R84965 : Reach 84965 := rs (se 4 (by rfl) ⟨7965, by rfl⟩) (B 15931 (by norm_num) ⟨7965, by rfl⟩ (by norm_num))
theorem R117749 : Reach 117749 := rs (se 5 (by rfl) ⟨5519, by rfl⟩) (B 11039 (by norm_num) ⟨5519, by rfl⟩ (by norm_num))
theorem R84989 : Reach 84989 := rs (se 3 (by rfl) ⟨15935, by rfl⟩) (B 31871 (by norm_num) ⟨15935, by rfl⟩ (by norm_num))
theorem R85013 : Reach 85013 := rs (se 6 (by rfl) ⟨1992, by rfl⟩) (B 3985 (by norm_num) ⟨1992, by rfl⟩ (by norm_num))
theorem R85037 : Reach 85037 := rs (se 3 (by rfl) ⟨15944, by rfl⟩) (B 31889 (by norm_num) ⟨15944, by rfl⟩ (by norm_num))
theorem R85061 : Reach 85061 := rs (se 4 (by rfl) ⟨7974, by rfl⟩) (B 15949 (by norm_num) ⟨7974, by rfl⟩ (by norm_num))
theorem R85085 : Reach 85085 := rs (se 3 (by rfl) ⟨15953, by rfl⟩) (B 31907 (by norm_num) ⟨15953, by rfl⟩ (by norm_num))
theorem R281717 : Reach 281717 := rs (se 5 (by rfl) ⟨13205, by rfl⟩) (B 26411 (by norm_num) ⟨13205, by rfl⟩ (by norm_num))
theorem R85109 : Reach 85109 := rs (se 5 (by rfl) ⟨3989, by rfl⟩) (B 7979 (by norm_num) ⟨3989, by rfl⟩ (by norm_num))
theorem R117893 : Reach 117893 := rs (se 4 (by rfl) ⟨11052, by rfl⟩) (B 22105 (by norm_num) ⟨11052, by rfl⟩ (by norm_num))
theorem R85133 : Reach 85133 := rs (se 3 (by rfl) ⟨15962, by rfl⟩) (B 31925 (by norm_num) ⟨15962, by rfl⟩ (by norm_num))
theorem R85157 : Reach 85157 := rs (se 4 (by rfl) ⟨7983, by rfl⟩) (B 15967 (by norm_num) ⟨7983, by rfl⟩ (by norm_num))
theorem R85181 : Reach 85181 := rs (se 3 (by rfl) ⟨15971, by rfl⟩) (B 31943 (by norm_num) ⟨15971, by rfl⟩ (by norm_num))
theorem R85205 : Reach 85205 := rs (se 7 (by rfl) ⟨998, by rfl⟩) (B 1997 (by norm_num) ⟨998, by rfl⟩ (by norm_num))
theorem R85229 : Reach 85229 := rs (se 3 (by rfl) ⟨15980, by rfl⟩) (B 31961 (by norm_num) ⟨15980, by rfl⟩ (by norm_num))
theorem R85253 : Reach 85253 := rs (se 4 (by rfl) ⟨7992, by rfl⟩) (B 15985 (by norm_num) ⟨7992, by rfl⟩ (by norm_num))
theorem R85277 : Reach 85277 := rs (se 3 (by rfl) ⟨15989, by rfl⟩) (B 31979 (by norm_num) ⟨15989, by rfl⟩ (by norm_num))
theorem R85301 : Reach 85301 := rs (se 5 (by rfl) ⟨3998, by rfl⟩) (B 7997 (by norm_num) ⟨3998, by rfl⟩ (by norm_num))
theorem R85325 : Reach 85325 := rs (se 3 (by rfl) ⟨15998, by rfl⟩) (B 31997 (by norm_num) ⟨15998, by rfl⟩ (by norm_num))
theorem R85349 : Reach 85349 := rs (se 4 (by rfl) ⟨8001, by rfl⟩) (B 16003 (by norm_num) ⟨8001, by rfl⟩ (by norm_num))
theorem R85373 : Reach 85373 := rs (se 3 (by rfl) ⟨16007, by rfl⟩) (B 32015 (by norm_num) ⟨16007, by rfl⟩ (by norm_num))
theorem R85397 : Reach 85397 := rs (se 6 (by rfl) ⟨2001, by rfl⟩) (B 4003 (by norm_num) ⟨2001, by rfl⟩ (by norm_num))
theorem R85421 : Reach 85421 := rs (se 3 (by rfl) ⟨16016, by rfl⟩) (B 32033 (by norm_num) ⟨16016, by rfl⟩ (by norm_num))
theorem R85445 : Reach 85445 := rs (se 4 (by rfl) ⟨8010, by rfl⟩) (B 16021 (by norm_num) ⟨8010, by rfl⟩ (by norm_num))
theorem R282053 : Reach 282053 := rs (se 4 (by rfl) ⟨26442, by rfl⟩) (B 52885 (by norm_num) ⟨26442, by rfl⟩ (by norm_num))
theorem R314837 : Reach 314837 := rs (se 7 (by rfl) ⟨3689, by rfl⟩) (B 7379 (by norm_num) ⟨3689, by rfl⟩ (by norm_num))
theorem R85469 : Reach 85469 := rs (se 3 (by rfl) ⟨16025, by rfl⟩) (B 32051 (by norm_num) ⟨16025, by rfl⟩ (by norm_num))
theorem R118253 : Reach 118253 := rs (se 3 (by rfl) ⟨22172, by rfl⟩) (B 44345 (by norm_num) ⟨22172, by rfl⟩ (by norm_num))
theorem R85493 : Reach 85493 := rs (se 5 (by rfl) ⟨4007, by rfl⟩) (B 8015 (by norm_num) ⟨4007, by rfl⟩ (by norm_num))
theorem R85517 : Reach 85517 := rs (se 3 (by rfl) ⟨16034, by rfl⟩) (B 32069 (by norm_num) ⟨16034, by rfl⟩ (by norm_num))
theorem R85541 : Reach 85541 := rs (se 4 (by rfl) ⟨8019, by rfl⟩) (B 16039 (by norm_num) ⟨8019, by rfl⟩ (by norm_num))
theorem R151093 : Reach 151093 := rs (se 5 (by rfl) ⟨7082, by rfl⟩) (B 14165 (by norm_num) ⟨7082, by rfl⟩ (by norm_num))
theorem R85565 : Reach 85565 := rs (se 3 (by rfl) ⟨16043, by rfl⟩) (B 32087 (by norm_num) ⟨16043, by rfl⟩ (by norm_num))
theorem R85589 : Reach 85589 := rs (se 8 (by rfl) ⟨501, by rfl⟩) (B 1003 (by norm_num) ⟨501, by rfl⟩ (by norm_num))
theorem R85613 : Reach 85613 := rs (se 3 (by rfl) ⟨16052, by rfl⟩) (B 32105 (by norm_num) ⟨16052, by rfl⟩ (by norm_num))
theorem R380533 : Reach 380533 := rs (se 5 (by rfl) ⟨17837, by rfl⟩) (B 35675 (by norm_num) ⟨17837, by rfl⟩ (by norm_num))
theorem R85637 : Reach 85637 := rs (se 4 (by rfl) ⟨8028, by rfl⟩) (B 16057 (by norm_num) ⟨8028, by rfl⟩ (by norm_num))
theorem R183941 : Reach 183941 := rs (se 4 (by rfl) ⟨17244, by rfl⟩) (B 34489 (by norm_num) ⟨17244, by rfl⟩ (by norm_num))
theorem R85661 : Reach 85661 := rs (se 3 (by rfl) ⟨16061, by rfl⟩) (B 32123 (by norm_num) ⟨16061, by rfl⟩ (by norm_num))
theorem R85685 : Reach 85685 := rs (se 5 (by rfl) ⟨4016, by rfl⟩) (B 8033 (by norm_num) ⟨4016, by rfl⟩ (by norm_num))
theorem R85709 : Reach 85709 := rs (se 3 (by rfl) ⟨16070, by rfl⟩) (B 32141 (by norm_num) ⟨16070, by rfl⟩ (by norm_num))
theorem R85733 : Reach 85733 := rs (se 4 (by rfl) ⟨8037, by rfl⟩) (B 16075 (by norm_num) ⟨8037, by rfl⟩ (by norm_num))
theorem R85757 : Reach 85757 := rs (se 3 (by rfl) ⟨16079, by rfl⟩) (B 32159 (by norm_num) ⟨16079, by rfl⟩ (by norm_num))
theorem R85781 : Reach 85781 := rs (se 6 (by rfl) ⟨2010, by rfl⟩) (B 4021 (by norm_num) ⟨2010, by rfl⟩ (by norm_num))
theorem R85805 : Reach 85805 := rs (se 3 (by rfl) ⟨16088, by rfl⟩) (B 32177 (by norm_num) ⟨16088, by rfl⟩ (by norm_num))
theorem R85829 : Reach 85829 := rs (se 4 (by rfl) ⟨8046, by rfl⟩) (B 16093 (by norm_num) ⟨8046, by rfl⟩ (by norm_num))
theorem R85853 : Reach 85853 := rs (se 3 (by rfl) ⟨16097, by rfl⟩) (B 32195 (by norm_num) ⟨16097, by rfl⟩ (by norm_num))
theorem R85877 : Reach 85877 := rs (se 5 (by rfl) ⟨4025, by rfl⟩) (B 8051 (by norm_num) ⟨4025, by rfl⟩ (by norm_num))
theorem R85901 : Reach 85901 := rs (se 3 (by rfl) ⟨16106, by rfl⟩) (B 32213 (by norm_num) ⟨16106, by rfl⟩ (by norm_num))
theorem R85925 : Reach 85925 := rs (se 4 (by rfl) ⟨8055, by rfl⟩) (B 16111 (by norm_num) ⟨8055, by rfl⟩ (by norm_num))
theorem R85949 : Reach 85949 := rs (se 3 (by rfl) ⟨16115, by rfl⟩) (B 32231 (by norm_num) ⟨16115, by rfl⟩ (by norm_num))
theorem R249797 : Reach 249797 := rs (se 4 (by rfl) ⟨23418, by rfl⟩) (B 46837 (by norm_num) ⟨23418, by rfl⟩ (by norm_num))
theorem R85973 : Reach 85973 := rs (se 7 (by rfl) ⟨1007, by rfl⟩) (B 2015 (by norm_num) ⟨1007, by rfl⟩ (by norm_num))
theorem R85997 : Reach 85997 := rs (se 3 (by rfl) ⟨16124, by rfl⟩) (B 32249 (by norm_num) ⟨16124, by rfl⟩ (by norm_num))
theorem R86021 : Reach 86021 := rs (se 4 (by rfl) ⟨8064, by rfl⟩) (B 16129 (by norm_num) ⟨8064, by rfl⟩ (by norm_num))
theorem R86045 : Reach 86045 := rs (se 3 (by rfl) ⟨16133, by rfl⟩) (B 32267 (by norm_num) ⟨16133, by rfl⟩ (by norm_num))
theorem R86069 : Reach 86069 := rs (se 5 (by rfl) ⟨4034, by rfl⟩) (B 8069 (by norm_num) ⟨4034, by rfl⟩ (by norm_num))
theorem R86093 : Reach 86093 := rs (se 3 (by rfl) ⟨16142, by rfl⟩) (B 32285 (by norm_num) ⟨16142, by rfl⟩ (by norm_num))
theorem R86117 : Reach 86117 := rs (se 4 (by rfl) ⟨8073, by rfl⟩) (B 16147 (by norm_num) ⟨8073, by rfl⟩ (by norm_num))
theorem R86141 : Reach 86141 := rs (se 3 (by rfl) ⟨16151, by rfl⟩) (B 32303 (by norm_num) ⟨16151, by rfl⟩ (by norm_num))
theorem R86165 : Reach 86165 := rs (se 6 (by rfl) ⟨2019, by rfl⟩) (B 4039 (by norm_num) ⟨2019, by rfl⟩ (by norm_num))
theorem R86189 : Reach 86189 := rs (se 3 (by rfl) ⟨16160, by rfl⟩) (B 32321 (by norm_num) ⟨16160, by rfl⟩ (by norm_num))
theorem R250037 : Reach 250037 := rs (se 5 (by rfl) ⟨11720, by rfl⟩) (B 23441 (by norm_num) ⟨11720, by rfl⟩ (by norm_num))
theorem R86213 : Reach 86213 := rs (se 4 (by rfl) ⟨8082, by rfl⟩) (B 16165 (by norm_num) ⟨8082, by rfl⟩ (by norm_num))
theorem R86237 : Reach 86237 := rs (se 3 (by rfl) ⟨16169, by rfl⟩) (B 32339 (by norm_num) ⟨16169, by rfl⟩ (by norm_num))
theorem R86261 : Reach 86261 := rs (se 5 (by rfl) ⟨4043, by rfl⟩) (B 8087 (by norm_num) ⟨4043, by rfl⟩ (by norm_num))
theorem R217349 : Reach 217349 := rs (se 4 (by rfl) ⟨20376, by rfl⟩) (B 40753 (by norm_num) ⟨20376, by rfl⟩ (by norm_num))
theorem R86285 : Reach 86285 := rs (se 3 (by rfl) ⟨16178, by rfl⟩) (B 32357 (by norm_num) ⟨16178, by rfl⟩ (by norm_num))
theorem R86309 : Reach 86309 := rs (se 4 (by rfl) ⟨8091, by rfl⟩) (B 16183 (by norm_num) ⟨8091, by rfl⟩ (by norm_num))
theorem R86333 : Reach 86333 := rs (se 3 (by rfl) ⟨16187, by rfl⟩) (B 32375 (by norm_num) ⟨16187, by rfl⟩ (by norm_num))
theorem R86357 : Reach 86357 := rs (se 10 (by rfl) ⟨126, by rfl⟩) (B 253 (by norm_num) ⟨126, by rfl⟩ (by norm_num))
theorem R119141 : Reach 119141 := rs (se 4 (by rfl) ⟨11169, by rfl⟩) (B 22339 (by norm_num) ⟨11169, by rfl⟩ (by norm_num))
theorem R86381 : Reach 86381 := rs (se 3 (by rfl) ⟨16196, by rfl⟩) (B 32393 (by norm_num) ⟨16196, by rfl⟩ (by norm_num))
theorem R250229 : Reach 250229 := rs (se 5 (by rfl) ⟨11729, by rfl⟩) (B 23459 (by norm_num) ⟨11729, by rfl⟩ (by norm_num))
theorem R283013 : Reach 283013 := rs (se 4 (by rfl) ⟨26532, by rfl⟩) (B 53065 (by norm_num) ⟨26532, by rfl⟩ (by norm_num))
theorem R86405 : Reach 86405 := rs (se 4 (by rfl) ⟨8100, by rfl⟩) (B 16201 (by norm_num) ⟨8100, by rfl⟩ (by norm_num))
theorem R119173 : Reach 119173 := rs (se 4 (by rfl) ⟨11172, by rfl⟩) (B 22345 (by norm_num) ⟨11172, by rfl⟩ (by norm_num))
theorem R86429 : Reach 86429 := rs (se 3 (by rfl) ⟨16205, by rfl⟩) (B 32411 (by norm_num) ⟨16205, by rfl⟩ (by norm_num))
theorem R86453 : Reach 86453 := rs (se 5 (by rfl) ⟨4052, by rfl⟩) (B 8105 (by norm_num) ⟨4052, by rfl⟩ (by norm_num))
theorem R86477 : Reach 86477 := rs (se 3 (by rfl) ⟨16214, by rfl⟩) (B 32429 (by norm_num) ⟨16214, by rfl⟩ (by norm_num))
theorem R86501 : Reach 86501 := rs (se 4 (by rfl) ⟨8109, by rfl⟩) (B 16219 (by norm_num) ⟨8109, by rfl⟩ (by norm_num))
theorem R86525 : Reach 86525 := rs (se 3 (by rfl) ⟨16223, by rfl⟩) (B 32447 (by norm_num) ⟨16223, by rfl⟩ (by norm_num))
theorem R86549 : Reach 86549 := rs (se 6 (by rfl) ⟨2028, by rfl⟩) (B 4057 (by norm_num) ⟨2028, by rfl⟩ (by norm_num))
theorem R217637 : Reach 217637 := rs (se 4 (by rfl) ⟨20403, by rfl⟩) (B 40807 (by norm_num) ⟨20403, by rfl⟩ (by norm_num))
theorem R86573 : Reach 86573 := rs (se 3 (by rfl) ⟨16232, by rfl⟩) (B 32465 (by norm_num) ⟨16232, by rfl⟩ (by norm_num))
theorem R86597 : Reach 86597 := rs (se 4 (by rfl) ⟨8118, by rfl⟩) (B 16237 (by norm_num) ⟨8118, by rfl⟩ (by norm_num))
theorem R119389 : Reach 119389 := rs (se 3 (by rfl) ⟨22385, by rfl⟩) (B 44771 (by norm_num) ⟨22385, by rfl⟩ (by norm_num))
theorem R86621 : Reach 86621 := rs (se 3 (by rfl) ⟨16241, by rfl⟩) (B 32483 (by norm_num) ⟨16241, by rfl⟩ (by norm_num))
theorem R316021 : Reach 316021 := rs (se 5 (by rfl) ⟨14813, by rfl⟩) (B 29627 (by norm_num) ⟨14813, by rfl⟩ (by norm_num))
theorem R86645 : Reach 86645 := rs (se 5 (by rfl) ⟨4061, by rfl⟩) (B 8123 (by norm_num) ⟨4061, by rfl⟩ (by norm_num))
theorem R86669 : Reach 86669 := rs (se 3 (by rfl) ⟨16250, by rfl⟩) (B 32501 (by norm_num) ⟨16250, by rfl⟩ (by norm_num))
theorem R86693 : Reach 86693 := rs (se 4 (by rfl) ⟨8127, by rfl⟩) (B 16255 (by norm_num) ⟨8127, by rfl⟩ (by norm_num))
theorem R86717 : Reach 86717 := rs (se 3 (by rfl) ⟨16259, by rfl⟩) (B 32519 (by norm_num) ⟨16259, by rfl⟩ (by norm_num))
theorem R86741 : Reach 86741 := rs (se 7 (by rfl) ⟨1016, by rfl⟩) (B 2033 (by norm_num) ⟨1016, by rfl⟩ (by norm_num))
theorem R86765 : Reach 86765 := rs (se 3 (by rfl) ⟨16268, by rfl⟩) (B 32537 (by norm_num) ⟨16268, by rfl⟩ (by norm_num))
theorem R86789 : Reach 86789 := rs (se 4 (by rfl) ⟨8136, by rfl⟩) (B 16273 (by norm_num) ⟨8136, by rfl⟩ (by norm_num))
theorem R86813 : Reach 86813 := rs (se 3 (by rfl) ⟨16277, by rfl⟩) (B 32555 (by norm_num) ⟨16277, by rfl⟩ (by norm_num))
theorem R86837 : Reach 86837 := rs (se 5 (by rfl) ⟨4070, by rfl⟩) (B 8141 (by norm_num) ⟨4070, by rfl⟩ (by norm_num))
theorem R283445 : Reach 283445 := rs (se 5 (by rfl) ⟨13286, by rfl⟩) (B 26573 (by norm_num) ⟨13286, by rfl⟩ (by norm_num))
theorem R86861 : Reach 86861 := rs (se 3 (by rfl) ⟨16286, by rfl⟩) (B 32573 (by norm_num) ⟨16286, by rfl⟩ (by norm_num))
theorem R86885 : Reach 86885 := rs (se 4 (by rfl) ⟨8145, by rfl⟩) (B 16291 (by norm_num) ⟨8145, by rfl⟩ (by norm_num))
theorem R86909 : Reach 86909 := rs (se 3 (by rfl) ⟨16295, by rfl⟩) (B 32591 (by norm_num) ⟨16295, by rfl⟩ (by norm_num))
theorem R86933 : Reach 86933 := rs (se 6 (by rfl) ⟨2037, by rfl⟩) (B 4075 (by norm_num) ⟨2037, by rfl⟩ (by norm_num))
theorem R86957 : Reach 86957 := rs (se 3 (by rfl) ⟨16304, by rfl⟩) (B 32609 (by norm_num) ⟨16304, by rfl⟩ (by norm_num))
theorem R86981 : Reach 86981 := rs (se 4 (by rfl) ⟨8154, by rfl⟩) (B 16309 (by norm_num) ⟨8154, by rfl⟩ (by norm_num))
theorem R807893 : Reach 807893 := rs (se 7 (by rfl) ⟨9467, by rfl⟩) (B 18935 (by norm_num) ⟨9467, by rfl⟩ (by norm_num))
theorem R87005 : Reach 87005 := rs (se 3 (by rfl) ⟨16313, by rfl⟩) (B 32627 (by norm_num) ⟨16313, by rfl⟩ (by norm_num))
theorem R87029 : Reach 87029 := rs (se 5 (by rfl) ⟨4079, by rfl⟩) (B 8159 (by norm_num) ⟨4079, by rfl⟩ (by norm_num))
theorem R87053 : Reach 87053 := rs (se 3 (by rfl) ⟨16322, by rfl⟩) (B 32645 (by norm_num) ⟨16322, by rfl⟩ (by norm_num))
theorem R87077 : Reach 87077 := rs (se 4 (by rfl) ⟨8163, by rfl⟩) (B 16327 (by norm_num) ⟨8163, by rfl⟩ (by norm_num))
theorem R87101 : Reach 87101 := rs (se 3 (by rfl) ⟨16331, by rfl⟩) (B 32663 (by norm_num) ⟨16331, by rfl⟩ (by norm_num))
theorem R119893 : Reach 119893 := rs (se 8 (by rfl) ⟨702, by rfl⟩) (B 1405 (by norm_num) ⟨702, by rfl⟩ (by norm_num))
theorem R87125 : Reach 87125 := rs (se 8 (by rfl) ⟨510, by rfl⟩) (B 1021 (by norm_num) ⟨510, by rfl⟩ (by norm_num))
theorem R87149 : Reach 87149 := rs (se 3 (by rfl) ⟨16340, by rfl⟩) (B 32681 (by norm_num) ⟨16340, by rfl⟩ (by norm_num))
theorem R447605 : Reach 447605 := rs (se 5 (by rfl) ⟨20981, by rfl⟩) (B 41963 (by norm_num) ⟨20981, by rfl⟩ (by norm_num))
theorem R87173 : Reach 87173 := rs (se 4 (by rfl) ⟨8172, by rfl⟩) (B 16345 (by norm_num) ⟨8172, by rfl⟩ (by norm_num))
theorem R87197 : Reach 87197 := rs (se 3 (by rfl) ⟨16349, by rfl⟩) (B 32699 (by norm_num) ⟨16349, by rfl⟩ (by norm_num))
theorem R87221 : Reach 87221 := rs (se 5 (by rfl) ⟨4088, by rfl⟩) (B 8177 (by norm_num) ⟨4088, by rfl⟩ (by norm_num))
theorem R87245 : Reach 87245 := rs (se 3 (by rfl) ⟨16358, by rfl⟩) (B 32717 (by norm_num) ⟨16358, by rfl⟩ (by norm_num))
theorem R87269 : Reach 87269 := rs (se 4 (by rfl) ⟨8181, by rfl⟩) (B 16363 (by norm_num) ⟨8181, by rfl⟩ (by norm_num))
theorem R87293 : Reach 87293 := rs (se 3 (by rfl) ⟨16367, by rfl⟩) (B 32735 (by norm_num) ⟨16367, by rfl⟩ (by norm_num))
theorem R87317 : Reach 87317 := rs (se 6 (by rfl) ⟨2046, by rfl⟩) (B 4093 (by norm_num) ⟨2046, by rfl⟩ (by norm_num))
theorem R87341 : Reach 87341 := rs (se 3 (by rfl) ⟨16376, by rfl⟩) (B 32753 (by norm_num) ⟨16376, by rfl⟩ (by norm_num))
theorem R152885 : Reach 152885 := rs (se 5 (by rfl) ⟨7166, by rfl⟩) (B 14333 (by norm_num) ⟨7166, by rfl⟩ (by norm_num))
theorem R87365 : Reach 87365 := rs (se 4 (by rfl) ⟨8190, by rfl⟩) (B 16381 (by norm_num) ⟨8190, by rfl⟩ (by norm_num))
theorem R87389 : Reach 87389 := rs (se 3 (by rfl) ⟨16385, by rfl⟩) (B 32771 (by norm_num) ⟨16385, by rfl⟩ (by norm_num))
theorem R87413 : Reach 87413 := rs (se 5 (by rfl) ⟨4097, by rfl⟩) (B 8195 (by norm_num) ⟨4097, by rfl⟩ (by norm_num))
theorem R87437 : Reach 87437 := rs (se 3 (by rfl) ⟨16394, by rfl⟩) (B 32789 (by norm_num) ⟨16394, by rfl⟩ (by norm_num))
theorem R87461 : Reach 87461 := rs (se 4 (by rfl) ⟨8199, by rfl⟩) (B 16399 (by norm_num) ⟨8199, by rfl⟩ (by norm_num))
theorem R87485 : Reach 87485 := rs (se 3 (by rfl) ⟨16403, by rfl⟩) (B 32807 (by norm_num) ⟨16403, by rfl⟩ (by norm_num))
theorem R87509 : Reach 87509 := rs (se 7 (by rfl) ⟨1025, by rfl⟩) (B 2051 (by norm_num) ⟨1025, by rfl⟩ (by norm_num))
theorem R87533 : Reach 87533 := rs (se 3 (by rfl) ⟨16412, by rfl⟩) (B 32825 (by norm_num) ⟨16412, by rfl⟩ (by norm_num))
theorem R185861 : Reach 185861 := rs (se 4 (by rfl) ⟨17424, by rfl⟩) (B 34849 (by norm_num) ⟨17424, by rfl⟩ (by norm_num))
theorem R87557 : Reach 87557 := rs (se 4 (by rfl) ⟨8208, by rfl⟩) (B 16417 (by norm_num) ⟨8208, by rfl⟩ (by norm_num))
theorem R87581 : Reach 87581 := rs (se 3 (by rfl) ⟨16421, by rfl⟩) (B 32843 (by norm_num) ⟨16421, by rfl⟩ (by norm_num))
theorem R87605 : Reach 87605 := rs (se 5 (by rfl) ⟨4106, by rfl⟩) (B 8213 (by norm_num) ⟨4106, by rfl⟩ (by norm_num))
theorem R87629 : Reach 87629 := rs (se 3 (by rfl) ⟨16430, by rfl⟩) (B 32861 (by norm_num) ⟨16430, by rfl⟩ (by norm_num))
theorem R87653 : Reach 87653 := rs (se 4 (by rfl) ⟨8217, by rfl⟩) (B 16435 (by norm_num) ⟨8217, by rfl⟩ (by norm_num))
theorem R87677 : Reach 87677 := rs (se 3 (by rfl) ⟨16439, by rfl⟩) (B 32879 (by norm_num) ⟨16439, by rfl⟩ (by norm_num))
theorem R284309 : Reach 284309 := rs (se 6 (by rfl) ⟨6663, by rfl⟩) (B 13327 (by norm_num) ⟨6663, by rfl⟩ (by norm_num))
theorem R87701 : Reach 87701 := rs (se 6 (by rfl) ⟨2055, by rfl⟩) (B 4111 (by norm_num) ⟨2055, by rfl⟩ (by norm_num))
theorem R87725 : Reach 87725 := rs (se 3 (by rfl) ⟨16448, by rfl⟩) (B 32897 (by norm_num) ⟨16448, by rfl⟩ (by norm_num))
theorem R218821 : Reach 218821 := rs (se 4 (by rfl) ⟨20514, by rfl⟩) (B 41029 (by norm_num) ⟨20514, by rfl⟩ (by norm_num))
theorem R87749 : Reach 87749 := rs (se 4 (by rfl) ⟨8226, by rfl⟩) (B 16453 (by norm_num) ⟨8226, by rfl⟩ (by norm_num))
theorem R87773 : Reach 87773 := rs (se 3 (by rfl) ⟨16457, by rfl⟩) (B 32915 (by norm_num) ⟨16457, by rfl⟩ (by norm_num))
theorem R87797 : Reach 87797 := rs (se 5 (by rfl) ⟨4115, by rfl⟩) (B 8231 (by norm_num) ⟨4115, by rfl⟩ (by norm_num))
theorem R87821 : Reach 87821 := rs (se 3 (by rfl) ⟨16466, by rfl⟩) (B 32933 (by norm_num) ⟨16466, by rfl⟩ (by norm_num))
theorem R87845 : Reach 87845 := rs (se 4 (by rfl) ⟨8235, by rfl⟩) (B 16471 (by norm_num) ⟨8235, by rfl⟩ (by norm_num))
theorem R87869 : Reach 87869 := rs (se 3 (by rfl) ⟨16475, by rfl⟩) (B 32951 (by norm_num) ⟨16475, by rfl⟩ (by norm_num))
theorem R55121 : Reach 55121 := rs (se 2 (by rfl) ⟨20670, by rfl⟩) (B 41341 (by norm_num) ⟨20670, by rfl⟩ (by norm_num))
theorem R55125 : Reach 55125 := rs (se 9 (by rfl) ⟨161, by rfl⟩) (B 323 (by norm_num) ⟨161, by rfl⟩ (by norm_num))
theorem R87893 : Reach 87893 := rs (se 9 (by rfl) ⟨257, by rfl⟩) (B 515 (by norm_num) ⟨257, by rfl⟩ (by norm_num))
theorem R55129 : Reach 55129 := rs (se 2 (by rfl) ⟨20673, by rfl⟩) (B 41347 (by norm_num) ⟨20673, by rfl⟩ (by norm_num))
theorem R55133 : Reach 55133 := rs (se 3 (by rfl) ⟨10337, by rfl⟩) (B 20675 (by norm_num) ⟨10337, by rfl⟩ (by norm_num))
theorem R55137 : Reach 55137 := rs (se 2 (by rfl) ⟨20676, by rfl⟩) (B 41353 (by norm_num) ⟨20676, by rfl⟩ (by norm_num))
theorem R55141 : Reach 55141 := rs (se 4 (by rfl) ⟨5169, by rfl⟩) (B 10339 (by norm_num) ⟨5169, by rfl⟩ (by norm_num))
theorem R55145 : Reach 55145 := rs (se 2 (by rfl) ⟨20679, by rfl⟩) (B 41359 (by norm_num) ⟨20679, by rfl⟩ (by norm_num))
theorem R55149 : Reach 55149 := rs (se 3 (by rfl) ⟨10340, by rfl⟩) (B 20681 (by norm_num) ⟨10340, by rfl⟩ (by norm_num))
theorem R87917 : Reach 87917 := rs (se 3 (by rfl) ⟨16484, by rfl⟩) (B 32969 (by norm_num) ⟨16484, by rfl⟩ (by norm_num))
theorem R55153 : Reach 55153 := rs (se 2 (by rfl) ⟨20682, by rfl⟩) (B 41365 (by norm_num) ⟨20682, by rfl⟩ (by norm_num))
theorem R55157 : Reach 55157 := rs (se 5 (by rfl) ⟨2585, by rfl⟩) (B 5171 (by norm_num) ⟨2585, by rfl⟩ (by norm_num))
theorem R55161 : Reach 55161 := rs (se 2 (by rfl) ⟨20685, by rfl⟩) (B 41371 (by norm_num) ⟨20685, by rfl⟩ (by norm_num))
theorem R55165 : Reach 55165 := rs (se 3 (by rfl) ⟨10343, by rfl⟩) (B 20687 (by norm_num) ⟨10343, by rfl⟩ (by norm_num))
theorem R55169 : Reach 55169 := rs (se 2 (by rfl) ⟨20688, by rfl⟩) (B 41377 (by norm_num) ⟨20688, by rfl⟩ (by norm_num))
theorem R55173 : Reach 55173 := rs (se 4 (by rfl) ⟨5172, by rfl⟩) (B 10345 (by norm_num) ⟨5172, by rfl⟩ (by norm_num))
theorem R186245 : Reach 186245 := rs (se 4 (by rfl) ⟨17460, by rfl⟩) (B 34921 (by norm_num) ⟨17460, by rfl⟩ (by norm_num))
theorem R87941 : Reach 87941 := rs (se 4 (by rfl) ⟨8244, by rfl⟩) (B 16489 (by norm_num) ⟨8244, by rfl⟩ (by norm_num))
theorem R55177 : Reach 55177 := rs (se 2 (by rfl) ⟨20691, by rfl⟩) (B 41383 (by norm_num) ⟨20691, by rfl⟩ (by norm_num))
theorem R55181 : Reach 55181 := rs (se 3 (by rfl) ⟨10346, by rfl⟩) (B 20693 (by norm_num) ⟨10346, by rfl⟩ (by norm_num))
theorem R55185 : Reach 55185 := rs (se 2 (by rfl) ⟨20694, by rfl⟩) (B 41389 (by norm_num) ⟨20694, by rfl⟩ (by norm_num))
theorem R55189 : Reach 55189 := rs (se 6 (by rfl) ⟨1293, by rfl⟩) (B 2587 (by norm_num) ⟨1293, by rfl⟩ (by norm_num))
theorem R55193 : Reach 55193 := rs (se 2 (by rfl) ⟨20697, by rfl⟩) (B 41395 (by norm_num) ⟨20697, by rfl⟩ (by norm_num))
theorem R55197 : Reach 55197 := rs (se 3 (by rfl) ⟨10349, by rfl⟩) (B 20699 (by norm_num) ⟨10349, by rfl⟩ (by norm_num))
theorem R87965 : Reach 87965 := rs (se 3 (by rfl) ⟨16493, by rfl⟩) (B 32987 (by norm_num) ⟨16493, by rfl⟩ (by norm_num))
theorem R55201 : Reach 55201 := rs (se 2 (by rfl) ⟨20700, by rfl⟩) (B 41401 (by norm_num) ⟨20700, by rfl⟩ (by norm_num))
theorem R55205 : Reach 55205 := rs (se 4 (by rfl) ⟨5175, by rfl⟩) (B 10351 (by norm_num) ⟨5175, by rfl⟩ (by norm_num))
theorem R55209 : Reach 55209 := rs (se 2 (by rfl) ⟨20703, by rfl⟩) (B 41407 (by norm_num) ⟨20703, by rfl⟩ (by norm_num))
theorem R55213 : Reach 55213 := rs (se 3 (by rfl) ⟨10352, by rfl⟩) (B 20705 (by norm_num) ⟨10352, by rfl⟩ (by norm_num))
theorem R55217 : Reach 55217 := rs (se 2 (by rfl) ⟨20706, by rfl⟩) (B 41413 (by norm_num) ⟨20706, by rfl⟩ (by norm_num))
theorem R55221 : Reach 55221 := rs (se 5 (by rfl) ⟨2588, by rfl⟩) (B 5177 (by norm_num) ⟨2588, by rfl⟩ (by norm_num))
theorem R87989 : Reach 87989 := rs (se 5 (by rfl) ⟨4124, by rfl⟩) (B 8249 (by norm_num) ⟨4124, by rfl⟩ (by norm_num))
theorem R55225 : Reach 55225 := rs (se 2 (by rfl) ⟨20709, by rfl⟩) (B 41419 (by norm_num) ⟨20709, by rfl⟩ (by norm_num))
theorem R55229 : Reach 55229 := rs (se 3 (by rfl) ⟨10355, by rfl⟩) (B 20711 (by norm_num) ⟨10355, by rfl⟩ (by norm_num))
theorem R55233 : Reach 55233 := rs (se 2 (by rfl) ⟨20712, by rfl⟩) (B 41425 (by norm_num) ⟨20712, by rfl⟩ (by norm_num))
theorem R55237 : Reach 55237 := rs (se 4 (by rfl) ⟨5178, by rfl⟩) (B 10357 (by norm_num) ⟨5178, by rfl⟩ (by norm_num))
theorem R55241 : Reach 55241 := rs (se 2 (by rfl) ⟨20715, by rfl⟩) (B 41431 (by norm_num) ⟨20715, by rfl⟩ (by norm_num))
theorem R55245 : Reach 55245 := rs (se 3 (by rfl) ⟨10358, by rfl⟩) (B 20717 (by norm_num) ⟨10358, by rfl⟩ (by norm_num))
theorem R120781 : Reach 120781 := rs (se 3 (by rfl) ⟨22646, by rfl⟩) (B 45293 (by norm_num) ⟨22646, by rfl⟩ (by norm_num))
theorem R88013 : Reach 88013 := rs (se 3 (by rfl) ⟨16502, by rfl⟩) (B 33005 (by norm_num) ⟨16502, by rfl⟩ (by norm_num))
theorem R55249 : Reach 55249 := rs (se 2 (by rfl) ⟨20718, by rfl⟩) (B 41437 (by norm_num) ⟨20718, by rfl⟩ (by norm_num))
theorem R55253 : Reach 55253 := rs (se 7 (by rfl) ⟨647, by rfl⟩) (B 1295 (by norm_num) ⟨647, by rfl⟩ (by norm_num))
theorem R55257 : Reach 55257 := rs (se 2 (by rfl) ⟨20721, by rfl⟩) (B 41443 (by norm_num) ⟨20721, by rfl⟩ (by norm_num))
theorem R55261 : Reach 55261 := rs (se 3 (by rfl) ⟨10361, by rfl⟩) (B 20723 (by norm_num) ⟨10361, by rfl⟩ (by norm_num))
theorem R55265 : Reach 55265 := rs (se 2 (by rfl) ⟨20724, by rfl⟩) (B 41449 (by norm_num) ⟨20724, by rfl⟩ (by norm_num))
theorem R55269 : Reach 55269 := rs (se 4 (by rfl) ⟨5181, by rfl⟩) (B 10363 (by norm_num) ⟨5181, by rfl⟩ (by norm_num))
theorem R88037 : Reach 88037 := rs (se 4 (by rfl) ⟨8253, by rfl⟩) (B 16507 (by norm_num) ⟨8253, by rfl⟩ (by norm_num))
theorem R55273 : Reach 55273 := rs (se 2 (by rfl) ⟨20727, by rfl⟩) (B 41455 (by norm_num) ⟨20727, by rfl⟩ (by norm_num))
theorem R55277 : Reach 55277 := rs (se 3 (by rfl) ⟨10364, by rfl⟩) (B 20729 (by norm_num) ⟨10364, by rfl⟩ (by norm_num))
theorem R55281 : Reach 55281 := rs (se 2 (by rfl) ⟨20730, by rfl⟩) (B 41461 (by norm_num) ⟨20730, by rfl⟩ (by norm_num))
theorem R55285 : Reach 55285 := rs (se 5 (by rfl) ⟨2591, by rfl⟩) (B 5183 (by norm_num) ⟨2591, by rfl⟩ (by norm_num))
theorem R219125 : Reach 219125 := rs (se 5 (by rfl) ⟨10271, by rfl⟩) (B 20543 (by norm_num) ⟨10271, by rfl⟩ (by norm_num))
theorem R55289 : Reach 55289 := rs (se 2 (by rfl) ⟨20733, by rfl⟩) (B 41467 (by norm_num) ⟨20733, by rfl⟩ (by norm_num))
theorem R55293 : Reach 55293 := rs (se 3 (by rfl) ⟨10367, by rfl⟩) (B 20735 (by norm_num) ⟨10367, by rfl⟩ (by norm_num))
theorem R88061 : Reach 88061 := rs (se 3 (by rfl) ⟨16511, by rfl⟩) (B 33023 (by norm_num) ⟨16511, by rfl⟩ (by norm_num))
theorem R55297 : Reach 55297 := rs (se 2 (by rfl) ⟨20736, by rfl⟩) (B 41473 (by norm_num) ⟨20736, by rfl⟩ (by norm_num))
theorem R55301 : Reach 55301 := rs (se 4 (by rfl) ⟨5184, by rfl⟩) (B 10369 (by norm_num) ⟨5184, by rfl⟩ (by norm_num))
theorem R55305 : Reach 55305 := rs (se 2 (by rfl) ⟨20739, by rfl⟩) (B 41479 (by norm_num) ⟨20739, by rfl⟩ (by norm_num))
theorem R55309 : Reach 55309 := rs (se 3 (by rfl) ⟨10370, by rfl⟩) (B 20741 (by norm_num) ⟨10370, by rfl⟩ (by norm_num))
theorem R55313 : Reach 55313 := rs (se 2 (by rfl) ⟨20742, by rfl⟩) (B 41485 (by norm_num) ⟨20742, by rfl⟩ (by norm_num))
theorem R55317 : Reach 55317 := rs (se 6 (by rfl) ⟨1296, by rfl⟩) (B 2593 (by norm_num) ⟨1296, by rfl⟩ (by norm_num))
theorem R88085 : Reach 88085 := rs (se 6 (by rfl) ⟨2064, by rfl⟩) (B 4129 (by norm_num) ⟨2064, by rfl⟩ (by norm_num))
theorem R55321 : Reach 55321 := rs (se 2 (by rfl) ⟨20745, by rfl⟩) (B 41491 (by norm_num) ⟨20745, by rfl⟩ (by norm_num))
theorem R55325 : Reach 55325 := rs (se 3 (by rfl) ⟨10373, by rfl⟩) (B 20747 (by norm_num) ⟨10373, by rfl⟩ (by norm_num))
theorem R55329 : Reach 55329 := rs (se 2 (by rfl) ⟨20748, by rfl⟩) (B 41497 (by norm_num) ⟨20748, by rfl⟩ (by norm_num))
theorem R55333 : Reach 55333 := rs (se 4 (by rfl) ⟨5187, by rfl⟩) (B 10375 (by norm_num) ⟨5187, by rfl⟩ (by norm_num))
theorem R55337 : Reach 55337 := rs (se 2 (by rfl) ⟨20751, by rfl⟩) (B 41503 (by norm_num) ⟨20751, by rfl⟩ (by norm_num))
theorem R55341 : Reach 55341 := rs (se 3 (by rfl) ⟨10376, by rfl⟩) (B 20753 (by norm_num) ⟨10376, by rfl⟩ (by norm_num))
theorem R88109 : Reach 88109 := rs (se 3 (by rfl) ⟨16520, by rfl⟩) (B 33041 (by norm_num) ⟨16520, by rfl⟩ (by norm_num))
theorem R55345 : Reach 55345 := rs (se 2 (by rfl) ⟨20754, by rfl⟩) (B 41509 (by norm_num) ⟨20754, by rfl⟩ (by norm_num))
theorem R55349 : Reach 55349 := rs (se 5 (by rfl) ⟨2594, by rfl⟩) (B 5189 (by norm_num) ⟨2594, by rfl⟩ (by norm_num))
theorem R55353 : Reach 55353 := rs (se 2 (by rfl) ⟨20757, by rfl⟩) (B 41515 (by norm_num) ⟨20757, by rfl⟩ (by norm_num))
theorem R55357 : Reach 55357 := rs (se 3 (by rfl) ⟨10379, by rfl⟩) (B 20759 (by norm_num) ⟨10379, by rfl⟩ (by norm_num))
theorem R55361 : Reach 55361 := rs (se 2 (by rfl) ⟨20760, by rfl⟩) (B 41521 (by norm_num) ⟨20760, by rfl⟩ (by norm_num))
theorem R55365 : Reach 55365 := rs (se 4 (by rfl) ⟨5190, by rfl⟩) (B 10381 (by norm_num) ⟨5190, by rfl⟩ (by norm_num))
theorem R88133 : Reach 88133 := rs (se 4 (by rfl) ⟨8262, by rfl⟩) (B 16525 (by norm_num) ⟨8262, by rfl⟩ (by norm_num))
theorem R55369 : Reach 55369 := rs (se 2 (by rfl) ⟨20763, by rfl⟩) (B 41527 (by norm_num) ⟨20763, by rfl⟩ (by norm_num))
theorem R55373 : Reach 55373 := rs (se 3 (by rfl) ⟨10382, by rfl⟩) (B 20765 (by norm_num) ⟨10382, by rfl⟩ (by norm_num))
theorem R55377 : Reach 55377 := rs (se 2 (by rfl) ⟨20766, by rfl⟩) (B 41533 (by norm_num) ⟨20766, by rfl⟩ (by norm_num))
theorem R55381 : Reach 55381 := rs (se 8 (by rfl) ⟨324, by rfl⟩) (B 649 (by norm_num) ⟨324, by rfl⟩ (by norm_num))
theorem R55385 : Reach 55385 := rs (se 2 (by rfl) ⟨20769, by rfl⟩) (B 41539 (by norm_num) ⟨20769, by rfl⟩ (by norm_num))
theorem R55389 : Reach 55389 := rs (se 3 (by rfl) ⟨10385, by rfl⟩) (B 20771 (by norm_num) ⟨10385, by rfl⟩ (by norm_num))
theorem R88157 : Reach 88157 := rs (se 3 (by rfl) ⟨16529, by rfl⟩) (B 33059 (by norm_num) ⟨16529, by rfl⟩ (by norm_num))
theorem R55393 : Reach 55393 := rs (se 2 (by rfl) ⟨20772, by rfl⟩) (B 41545 (by norm_num) ⟨20772, by rfl⟩ (by norm_num))
theorem R55397 : Reach 55397 := rs (se 4 (by rfl) ⟨5193, by rfl⟩) (B 10387 (by norm_num) ⟨5193, by rfl⟩ (by norm_num))
theorem R55401 : Reach 55401 := rs (se 2 (by rfl) ⟨20775, by rfl⟩) (B 41551 (by norm_num) ⟨20775, by rfl⟩ (by norm_num))
theorem R55405 : Reach 55405 := rs (se 3 (by rfl) ⟨10388, by rfl⟩) (B 20777 (by norm_num) ⟨10388, by rfl⟩ (by norm_num))
theorem R55409 : Reach 55409 := rs (se 2 (by rfl) ⟨20778, by rfl⟩) (B 41557 (by norm_num) ⟨20778, by rfl⟩ (by norm_num))
theorem R55413 : Reach 55413 := rs (se 5 (by rfl) ⟨2597, by rfl⟩) (B 5195 (by norm_num) ⟨2597, by rfl⟩ (by norm_num))
theorem R88181 : Reach 88181 := rs (se 5 (by rfl) ⟨4133, by rfl⟩) (B 8267 (by norm_num) ⟨4133, by rfl⟩ (by norm_num))
theorem R55417 : Reach 55417 := rs (se 2 (by rfl) ⟨20781, by rfl⟩) (B 41563 (by norm_num) ⟨20781, by rfl⟩ (by norm_num))
theorem R55421 : Reach 55421 := rs (se 3 (by rfl) ⟨10391, by rfl⟩) (B 20783 (by norm_num) ⟨10391, by rfl⟩ (by norm_num))
theorem R55425 : Reach 55425 := rs (se 2 (by rfl) ⟨20784, by rfl⟩) (B 41569 (by norm_num) ⟨20784, by rfl⟩ (by norm_num))
theorem R55429 : Reach 55429 := rs (se 4 (by rfl) ⟨5196, by rfl⟩) (B 10393 (by norm_num) ⟨5196, by rfl⟩ (by norm_num))
theorem R55433 : Reach 55433 := rs (se 2 (by rfl) ⟨20787, by rfl⟩) (B 41575 (by norm_num) ⟨20787, by rfl⟩ (by norm_num))
theorem R55437 : Reach 55437 := rs (se 3 (by rfl) ⟨10394, by rfl⟩) (B 20789 (by norm_num) ⟨10394, by rfl⟩ (by norm_num))
theorem R88205 : Reach 88205 := rs (se 3 (by rfl) ⟨16538, by rfl⟩) (B 33077 (by norm_num) ⟨16538, by rfl⟩ (by norm_num))
theorem R55441 : Reach 55441 := rs (se 2 (by rfl) ⟨20790, by rfl⟩) (B 41581 (by norm_num) ⟨20790, by rfl⟩ (by norm_num))
theorem R55445 : Reach 55445 := rs (se 6 (by rfl) ⟨1299, by rfl⟩) (B 2599 (by norm_num) ⟨1299, by rfl⟩ (by norm_num))
theorem R55449 : Reach 55449 := rs (se 2 (by rfl) ⟨20793, by rfl⟩) (B 41587 (by norm_num) ⟨20793, by rfl⟩ (by norm_num))
theorem R55453 : Reach 55453 := rs (se 3 (by rfl) ⟨10397, by rfl⟩) (B 20795 (by norm_num) ⟨10397, by rfl⟩ (by norm_num))
theorem R55457 : Reach 55457 := rs (se 2 (by rfl) ⟨20796, by rfl⟩) (B 41593 (by norm_num) ⟨20796, by rfl⟩ (by norm_num))
theorem R55461 : Reach 55461 := rs (se 4 (by rfl) ⟨5199, by rfl⟩) (B 10399 (by norm_num) ⟨5199, by rfl⟩ (by norm_num))
theorem R88229 : Reach 88229 := rs (se 4 (by rfl) ⟨8271, by rfl⟩) (B 16543 (by norm_num) ⟨8271, by rfl⟩ (by norm_num))
theorem R55465 : Reach 55465 := rs (se 2 (by rfl) ⟨20799, by rfl⟩) (B 41599 (by norm_num) ⟨20799, by rfl⟩ (by norm_num))
theorem R55469 : Reach 55469 := rs (se 3 (by rfl) ⟨10400, by rfl⟩) (B 20801 (by norm_num) ⟨10400, by rfl⟩ (by norm_num))
theorem R55473 : Reach 55473 := rs (se 2 (by rfl) ⟨20802, by rfl⟩) (B 41605 (by norm_num) ⟨20802, by rfl⟩ (by norm_num))
theorem R55477 : Reach 55477 := rs (se 5 (by rfl) ⟨2600, by rfl⟩) (B 5201 (by norm_num) ⟨2600, by rfl⟩ (by norm_num))
theorem R317621 : Reach 317621 := rs (se 5 (by rfl) ⟨14888, by rfl⟩) (B 29777 (by norm_num) ⟨14888, by rfl⟩ (by norm_num))
theorem R55481 : Reach 55481 := rs (se 2 (by rfl) ⟨20805, by rfl⟩) (B 41611 (by norm_num) ⟨20805, by rfl⟩ (by norm_num))
theorem R55485 : Reach 55485 := rs (se 3 (by rfl) ⟨10403, by rfl⟩) (B 20807 (by norm_num) ⟨10403, by rfl⟩ (by norm_num))
theorem R88253 : Reach 88253 := rs (se 3 (by rfl) ⟨16547, by rfl⟩) (B 33095 (by norm_num) ⟨16547, by rfl⟩ (by norm_num))
theorem R55489 : Reach 55489 := rs (se 2 (by rfl) ⟨20808, by rfl⟩) (B 41617 (by norm_num) ⟨20808, by rfl⟩ (by norm_num))
theorem R55493 : Reach 55493 := rs (se 4 (by rfl) ⟨5202, by rfl⟩) (B 10405 (by norm_num) ⟨5202, by rfl⟩ (by norm_num))
theorem R55497 : Reach 55497 := rs (se 2 (by rfl) ⟨20811, by rfl⟩) (B 41623 (by norm_num) ⟨20811, by rfl⟩ (by norm_num))
theorem R55501 : Reach 55501 := rs (se 3 (by rfl) ⟨10406, by rfl⟩) (B 20813 (by norm_num) ⟨10406, by rfl⟩ (by norm_num))
theorem R55505 : Reach 55505 := rs (se 2 (by rfl) ⟨20814, by rfl⟩) (B 41629 (by norm_num) ⟨20814, by rfl⟩ (by norm_num))
theorem R55509 : Reach 55509 := rs (se 7 (by rfl) ⟨650, by rfl⟩) (B 1301 (by norm_num) ⟨650, by rfl⟩ (by norm_num))
theorem R88277 : Reach 88277 := rs (se 7 (by rfl) ⟨1034, by rfl⟩) (B 2069 (by norm_num) ⟨1034, by rfl⟩ (by norm_num))
theorem R55513 : Reach 55513 := rs (se 2 (by rfl) ⟨20817, by rfl⟩) (B 41635 (by norm_num) ⟨20817, by rfl⟩ (by norm_num))
theorem R55517 : Reach 55517 := rs (se 3 (by rfl) ⟨10409, by rfl⟩) (B 20819 (by norm_num) ⟨10409, by rfl⟩ (by norm_num))
theorem R55521 : Reach 55521 := rs (se 2 (by rfl) ⟨20820, by rfl⟩) (B 41641 (by norm_num) ⟨20820, by rfl⟩ (by norm_num))
theorem R55525 : Reach 55525 := rs (se 4 (by rfl) ⟨5205, by rfl⟩) (B 10411 (by norm_num) ⟨5205, by rfl⟩ (by norm_num))
theorem R55529 : Reach 55529 := rs (se 2 (by rfl) ⟨20823, by rfl⟩) (B 41647 (by norm_num) ⟨20823, by rfl⟩ (by norm_num))
theorem R55533 : Reach 55533 := rs (se 3 (by rfl) ⟨10412, by rfl⟩) (B 20825 (by norm_num) ⟨10412, by rfl⟩ (by norm_num))
theorem R88301 : Reach 88301 := rs (se 3 (by rfl) ⟨16556, by rfl⟩) (B 33113 (by norm_num) ⟨16556, by rfl⟩ (by norm_num))
theorem R55537 : Reach 55537 := rs (se 2 (by rfl) ⟨20826, by rfl⟩) (B 41653 (by norm_num) ⟨20826, by rfl⟩ (by norm_num))
theorem R55541 : Reach 55541 := rs (se 5 (by rfl) ⟨2603, by rfl⟩) (B 5207 (by norm_num) ⟨2603, by rfl⟩ (by norm_num))
theorem R55545 : Reach 55545 := rs (se 2 (by rfl) ⟨20829, by rfl⟩) (B 41659 (by norm_num) ⟨20829, by rfl⟩ (by norm_num))
theorem R55549 : Reach 55549 := rs (se 3 (by rfl) ⟨10415, by rfl⟩) (B 20831 (by norm_num) ⟨10415, by rfl⟩ (by norm_num))
theorem R55553 : Reach 55553 := rs (se 2 (by rfl) ⟨20832, by rfl⟩) (B 41665 (by norm_num) ⟨20832, by rfl⟩ (by norm_num))
theorem R55557 : Reach 55557 := rs (se 4 (by rfl) ⟨5208, by rfl⟩) (B 10417 (by norm_num) ⟨5208, by rfl⟩ (by norm_num))
theorem R88325 : Reach 88325 := rs (se 4 (by rfl) ⟨8280, by rfl⟩) (B 16561 (by norm_num) ⟨8280, by rfl⟩ (by norm_num))
theorem R55561 : Reach 55561 := rs (se 2 (by rfl) ⟨20835, by rfl⟩) (B 41671 (by norm_num) ⟨20835, by rfl⟩ (by norm_num))
theorem R55565 : Reach 55565 := rs (se 3 (by rfl) ⟨10418, by rfl⟩) (B 20837 (by norm_num) ⟨10418, by rfl⟩ (by norm_num))
theorem R55569 : Reach 55569 := rs (se 2 (by rfl) ⟨20838, by rfl⟩) (B 41677 (by norm_num) ⟨20838, by rfl⟩ (by norm_num))
theorem R55573 : Reach 55573 := rs (se 6 (by rfl) ⟨1302, by rfl⟩) (B 2605 (by norm_num) ⟨1302, by rfl⟩ (by norm_num))
theorem R55577 : Reach 55577 := rs (se 2 (by rfl) ⟨20841, by rfl⟩) (B 41683 (by norm_num) ⟨20841, by rfl⟩ (by norm_num))
theorem R55581 : Reach 55581 := rs (se 3 (by rfl) ⟨10421, by rfl⟩) (B 20843 (by norm_num) ⟨10421, by rfl⟩ (by norm_num))
theorem R88349 : Reach 88349 := rs (se 3 (by rfl) ⟨16565, by rfl⟩) (B 33131 (by norm_num) ⟨16565, by rfl⟩ (by norm_num))
theorem R55585 : Reach 55585 := rs (se 2 (by rfl) ⟨20844, by rfl⟩) (B 41689 (by norm_num) ⟨20844, by rfl⟩ (by norm_num))
theorem R55589 : Reach 55589 := rs (se 4 (by rfl) ⟨5211, by rfl⟩) (B 10423 (by norm_num) ⟨5211, by rfl⟩ (by norm_num))
theorem R55593 : Reach 55593 := rs (se 2 (by rfl) ⟨20847, by rfl⟩) (B 41695 (by norm_num) ⟨20847, by rfl⟩ (by norm_num))
theorem R55597 : Reach 55597 := rs (se 3 (by rfl) ⟨10424, by rfl⟩) (B 20849 (by norm_num) ⟨10424, by rfl⟩ (by norm_num))
theorem R55601 : Reach 55601 := rs (se 2 (by rfl) ⟨20850, by rfl⟩) (B 41701 (by norm_num) ⟨20850, by rfl⟩ (by norm_num))
theorem R186677 : Reach 186677 := rs (se 5 (by rfl) ⟨8750, by rfl⟩) (B 17501 (by norm_num) ⟨8750, by rfl⟩ (by norm_num))
theorem R55605 : Reach 55605 := rs (se 5 (by rfl) ⟨2606, by rfl⟩) (B 5213 (by norm_num) ⟨2606, by rfl⟩ (by norm_num))
theorem R88373 : Reach 88373 := rs (se 5 (by rfl) ⟨4142, by rfl⟩) (B 8285 (by norm_num) ⟨4142, by rfl⟩ (by norm_num))
theorem R55609 : Reach 55609 := rs (se 2 (by rfl) ⟨20853, by rfl⟩) (B 41707 (by norm_num) ⟨20853, by rfl⟩ (by norm_num))
theorem R55613 : Reach 55613 := rs (se 3 (by rfl) ⟨10427, by rfl⟩) (B 20855 (by norm_num) ⟨10427, by rfl⟩ (by norm_num))
theorem R55617 : Reach 55617 := rs (se 2 (by rfl) ⟨20856, by rfl⟩) (B 41713 (by norm_num) ⟨20856, by rfl⟩ (by norm_num))
theorem R55621 : Reach 55621 := rs (se 4 (by rfl) ⟨5214, by rfl⟩) (B 10429 (by norm_num) ⟨5214, by rfl⟩ (by norm_num))
theorem R55625 : Reach 55625 := rs (se 2 (by rfl) ⟨20859, by rfl⟩) (B 41719 (by norm_num) ⟨20859, by rfl⟩ (by norm_num))
theorem R55629 : Reach 55629 := rs (se 3 (by rfl) ⟨10430, by rfl⟩) (B 20861 (by norm_num) ⟨10430, by rfl⟩ (by norm_num))
theorem R88397 : Reach 88397 := rs (se 3 (by rfl) ⟨16574, by rfl⟩) (B 33149 (by norm_num) ⟨16574, by rfl⟩ (by norm_num))
theorem R55633 : Reach 55633 := rs (se 2 (by rfl) ⟨20862, by rfl⟩) (B 41725 (by norm_num) ⟨20862, by rfl⟩ (by norm_num))
theorem R55637 : Reach 55637 := rs (se 10 (by rfl) ⟨81, by rfl⟩) (B 163 (by norm_num) ⟨81, by rfl⟩ (by norm_num))
theorem R55641 : Reach 55641 := rs (se 2 (by rfl) ⟨20865, by rfl⟩) (B 41731 (by norm_num) ⟨20865, by rfl⟩ (by norm_num))
theorem R55645 : Reach 55645 := rs (se 3 (by rfl) ⟨10433, by rfl⟩) (B 20867 (by norm_num) ⟨10433, by rfl⟩ (by norm_num))
theorem R55649 : Reach 55649 := rs (se 2 (by rfl) ⟨20868, by rfl⟩) (B 41737 (by norm_num) ⟨20868, by rfl⟩ (by norm_num))
theorem R55653 : Reach 55653 := rs (se 4 (by rfl) ⟨5217, by rfl⟩) (B 10435 (by norm_num) ⟨5217, by rfl⟩ (by norm_num))
theorem R88421 : Reach 88421 := rs (se 4 (by rfl) ⟨8289, by rfl⟩) (B 16579 (by norm_num) ⟨8289, by rfl⟩ (by norm_num))
theorem R55657 : Reach 55657 := rs (se 2 (by rfl) ⟨20871, by rfl⟩) (B 41743 (by norm_num) ⟨20871, by rfl⟩ (by norm_num))
theorem R55661 : Reach 55661 := rs (se 3 (by rfl) ⟨10436, by rfl⟩) (B 20873 (by norm_num) ⟨10436, by rfl⟩ (by norm_num))
theorem R55665 : Reach 55665 := rs (se 2 (by rfl) ⟨20874, by rfl⟩) (B 41749 (by norm_num) ⟨20874, by rfl⟩ (by norm_num))
theorem R55669 : Reach 55669 := rs (se 5 (by rfl) ⟨2609, by rfl⟩) (B 5219 (by norm_num) ⟨2609, by rfl⟩ (by norm_num))
theorem R55673 : Reach 55673 := rs (se 2 (by rfl) ⟨20877, by rfl⟩) (B 41755 (by norm_num) ⟨20877, by rfl⟩ (by norm_num))
theorem R55677 : Reach 55677 := rs (se 3 (by rfl) ⟨10439, by rfl⟩) (B 20879 (by norm_num) ⟨10439, by rfl⟩ (by norm_num))
theorem R88445 : Reach 88445 := rs (se 3 (by rfl) ⟨16583, by rfl⟩) (B 33167 (by norm_num) ⟨16583, by rfl⟩ (by norm_num))
theorem R55681 : Reach 55681 := rs (se 2 (by rfl) ⟨20880, by rfl⟩) (B 41761 (by norm_num) ⟨20880, by rfl⟩ (by norm_num))
theorem R55685 : Reach 55685 := rs (se 4 (by rfl) ⟨5220, by rfl⟩) (B 10441 (by norm_num) ⟨5220, by rfl⟩ (by norm_num))
theorem R55689 : Reach 55689 := rs (se 2 (by rfl) ⟨20883, by rfl⟩) (B 41767 (by norm_num) ⟨20883, by rfl⟩ (by norm_num))
theorem R55693 : Reach 55693 := rs (se 3 (by rfl) ⟨10442, by rfl⟩) (B 20885 (by norm_num) ⟨10442, by rfl⟩ (by norm_num))
theorem R55697 : Reach 55697 := rs (se 2 (by rfl) ⟨20886, by rfl⟩) (B 41773 (by norm_num) ⟨20886, by rfl⟩ (by norm_num))
theorem R55701 : Reach 55701 := rs (se 6 (by rfl) ⟨1305, by rfl⟩) (B 2611 (by norm_num) ⟨1305, by rfl⟩ (by norm_num))
theorem R88469 : Reach 88469 := rs (se 6 (by rfl) ⟨2073, by rfl⟩) (B 4147 (by norm_num) ⟨2073, by rfl⟩ (by norm_num))
theorem R55705 : Reach 55705 := rs (se 2 (by rfl) ⟨20889, by rfl⟩) (B 41779 (by norm_num) ⟨20889, by rfl⟩ (by norm_num))
theorem R55709 : Reach 55709 := rs (se 3 (by rfl) ⟨10445, by rfl⟩) (B 20891 (by norm_num) ⟨10445, by rfl⟩ (by norm_num))
theorem R55713 : Reach 55713 := rs (se 2 (by rfl) ⟨20892, by rfl⟩) (B 41785 (by norm_num) ⟨20892, by rfl⟩ (by norm_num))
theorem R55717 : Reach 55717 := rs (se 4 (by rfl) ⟨5223, by rfl⟩) (B 10447 (by norm_num) ⟨5223, by rfl⟩ (by norm_num))
theorem R252325 : Reach 252325 := rs (se 4 (by rfl) ⟨23655, by rfl⟩) (B 47311 (by norm_num) ⟨23655, by rfl⟩ (by norm_num))
theorem R55721 : Reach 55721 := rs (se 2 (by rfl) ⟨20895, by rfl⟩) (B 41791 (by norm_num) ⟨20895, by rfl⟩ (by norm_num))
theorem R55725 : Reach 55725 := rs (se 3 (by rfl) ⟨10448, by rfl⟩) (B 20897 (by norm_num) ⟨10448, by rfl⟩ (by norm_num))
theorem R88493 : Reach 88493 := rs (se 3 (by rfl) ⟨16592, by rfl⟩) (B 33185 (by norm_num) ⟨16592, by rfl⟩ (by norm_num))
theorem R55729 : Reach 55729 := rs (se 2 (by rfl) ⟨20898, by rfl⟩) (B 41797 (by norm_num) ⟨20898, by rfl⟩ (by norm_num))
theorem R55733 : Reach 55733 := rs (se 5 (by rfl) ⟨2612, by rfl⟩) (B 5225 (by norm_num) ⟨2612, by rfl⟩ (by norm_num))
theorem R55737 : Reach 55737 := rs (se 2 (by rfl) ⟨20901, by rfl⟩) (B 41803 (by norm_num) ⟨20901, by rfl⟩ (by norm_num))
theorem R55741 : Reach 55741 := rs (se 3 (by rfl) ⟨10451, by rfl⟩) (B 20903 (by norm_num) ⟨10451, by rfl⟩ (by norm_num))
theorem R121277 : Reach 121277 := rs (se 3 (by rfl) ⟨22739, by rfl⟩) (B 45479 (by norm_num) ⟨22739, by rfl⟩ (by norm_num))
theorem R55745 : Reach 55745 := rs (se 2 (by rfl) ⟨20904, by rfl⟩) (B 41809 (by norm_num) ⟨20904, by rfl⟩ (by norm_num))
theorem R55749 : Reach 55749 := rs (se 4 (by rfl) ⟨5226, by rfl⟩) (B 10453 (by norm_num) ⟨5226, by rfl⟩ (by norm_num))
theorem R88517 : Reach 88517 := rs (se 4 (by rfl) ⟨8298, by rfl⟩) (B 16597 (by norm_num) ⟨8298, by rfl⟩ (by norm_num))
theorem R55753 : Reach 55753 := rs (se 2 (by rfl) ⟨20907, by rfl⟩) (B 41815 (by norm_num) ⟨20907, by rfl⟩ (by norm_num))
theorem R55757 : Reach 55757 := rs (se 3 (by rfl) ⟨10454, by rfl⟩) (B 20909 (by norm_num) ⟨10454, by rfl⟩ (by norm_num))
theorem R55761 : Reach 55761 := rs (se 2 (by rfl) ⟨20910, by rfl⟩) (B 41821 (by norm_num) ⟨20910, by rfl⟩ (by norm_num))
theorem R55765 : Reach 55765 := rs (se 7 (by rfl) ⟨653, by rfl⟩) (B 1307 (by norm_num) ⟨653, by rfl⟩ (by norm_num))
theorem R55769 : Reach 55769 := rs (se 2 (by rfl) ⟨20913, by rfl⟩) (B 41827 (by norm_num) ⟨20913, by rfl⟩ (by norm_num))
theorem R55773 : Reach 55773 := rs (se 3 (by rfl) ⟨10457, by rfl⟩) (B 20915 (by norm_num) ⟨10457, by rfl⟩ (by norm_num))
theorem R88541 : Reach 88541 := rs (se 3 (by rfl) ⟨16601, by rfl⟩) (B 33203 (by norm_num) ⟨16601, by rfl⟩ (by norm_num))
theorem R55777 : Reach 55777 := rs (se 2 (by rfl) ⟨20916, by rfl⟩) (B 41833 (by norm_num) ⟨20916, by rfl⟩ (by norm_num))
theorem R55781 : Reach 55781 := rs (se 4 (by rfl) ⟨5229, by rfl⟩) (B 10459 (by norm_num) ⟨5229, by rfl⟩ (by norm_num))
theorem R55785 : Reach 55785 := rs (se 2 (by rfl) ⟨20919, by rfl⟩) (B 41839 (by norm_num) ⟨20919, by rfl⟩ (by norm_num))
theorem R55789 : Reach 55789 := rs (se 3 (by rfl) ⟨10460, by rfl⟩) (B 20921 (by norm_num) ⟨10460, by rfl⟩ (by norm_num))
theorem R55793 : Reach 55793 := rs (se 2 (by rfl) ⟨20922, by rfl⟩) (B 41845 (by norm_num) ⟨20922, by rfl⟩ (by norm_num))
theorem R55797 : Reach 55797 := rs (se 5 (by rfl) ⟨2615, by rfl⟩) (B 5231 (by norm_num) ⟨2615, by rfl⟩ (by norm_num))
theorem R88565 : Reach 88565 := rs (se 5 (by rfl) ⟨4151, by rfl⟩) (B 8303 (by norm_num) ⟨4151, by rfl⟩ (by norm_num))
theorem R55801 : Reach 55801 := rs (se 2 (by rfl) ⟨20925, by rfl⟩) (B 41851 (by norm_num) ⟨20925, by rfl⟩ (by norm_num))
theorem R55805 : Reach 55805 := rs (se 3 (by rfl) ⟨10463, by rfl⟩) (B 20927 (by norm_num) ⟨10463, by rfl⟩ (by norm_num))
theorem R55809 : Reach 55809 := rs (se 2 (by rfl) ⟨20928, by rfl⟩) (B 41857 (by norm_num) ⟨20928, by rfl⟩ (by norm_num))
theorem R55813 : Reach 55813 := rs (se 4 (by rfl) ⟨5232, by rfl⟩) (B 10465 (by norm_num) ⟨5232, by rfl⟩ (by norm_num))
theorem R55817 : Reach 55817 := rs (se 2 (by rfl) ⟨20931, by rfl⟩) (B 41863 (by norm_num) ⟨20931, by rfl⟩ (by norm_num))
theorem R55821 : Reach 55821 := rs (se 3 (by rfl) ⟨10466, by rfl⟩) (B 20933 (by norm_num) ⟨10466, by rfl⟩ (by norm_num))
theorem R88589 : Reach 88589 := rs (se 3 (by rfl) ⟨16610, by rfl⟩) (B 33221 (by norm_num) ⟨16610, by rfl⟩ (by norm_num))
theorem R55825 : Reach 55825 := rs (se 2 (by rfl) ⟨20934, by rfl⟩) (B 41869 (by norm_num) ⟨20934, by rfl⟩ (by norm_num))
theorem R55829 : Reach 55829 := rs (se 6 (by rfl) ⟨1308, by rfl⟩) (B 2617 (by norm_num) ⟨1308, by rfl⟩ (by norm_num))
theorem R55833 : Reach 55833 := rs (se 2 (by rfl) ⟨20937, by rfl⟩) (B 41875 (by norm_num) ⟨20937, by rfl⟩ (by norm_num))
theorem R55837 : Reach 55837 := rs (se 3 (by rfl) ⟨10469, by rfl⟩) (B 20939 (by norm_num) ⟨10469, by rfl⟩ (by norm_num))
theorem R55841 : Reach 55841 := rs (se 2 (by rfl) ⟨20940, by rfl⟩) (B 41881 (by norm_num) ⟨20940, by rfl⟩ (by norm_num))
theorem R55845 : Reach 55845 := rs (se 4 (by rfl) ⟨5235, by rfl⟩) (B 10471 (by norm_num) ⟨5235, by rfl⟩ (by norm_num))
theorem R88613 : Reach 88613 := rs (se 4 (by rfl) ⟨8307, by rfl⟩) (B 16615 (by norm_num) ⟨8307, by rfl⟩ (by norm_num))
theorem R55849 : Reach 55849 := rs (se 2 (by rfl) ⟨20943, by rfl⟩) (B 41887 (by norm_num) ⟨20943, by rfl⟩ (by norm_num))
theorem R55853 : Reach 55853 := rs (se 3 (by rfl) ⟨10472, by rfl⟩) (B 20945 (by norm_num) ⟨10472, by rfl⟩ (by norm_num))
theorem R55857 : Reach 55857 := rs (se 2 (by rfl) ⟨20946, by rfl⟩) (B 41893 (by norm_num) ⟨20946, by rfl⟩ (by norm_num))
theorem R318005 : Reach 318005 := rs (se 5 (by rfl) ⟨14906, by rfl⟩) (B 29813 (by norm_num) ⟨14906, by rfl⟩ (by norm_num))
theorem R55861 : Reach 55861 := rs (se 5 (by rfl) ⟨2618, by rfl⟩) (B 5237 (by norm_num) ⟨2618, by rfl⟩ (by norm_num))
theorem R55865 : Reach 55865 := rs (se 2 (by rfl) ⟨20949, by rfl⟩) (B 41899 (by norm_num) ⟨20949, by rfl⟩ (by norm_num))
theorem R55869 : Reach 55869 := rs (se 3 (by rfl) ⟨10475, by rfl⟩) (B 20951 (by norm_num) ⟨10475, by rfl⟩ (by norm_num))
theorem R88637 : Reach 88637 := rs (se 3 (by rfl) ⟨16619, by rfl⟩) (B 33239 (by norm_num) ⟨16619, by rfl⟩ (by norm_num))
theorem R55873 : Reach 55873 := rs (se 2 (by rfl) ⟨20952, by rfl⟩) (B 41905 (by norm_num) ⟨20952, by rfl⟩ (by norm_num))
theorem R55877 : Reach 55877 := rs (se 4 (by rfl) ⟨5238, by rfl⟩) (B 10477 (by norm_num) ⟨5238, by rfl⟩ (by norm_num))
theorem R55881 : Reach 55881 := rs (se 2 (by rfl) ⟨20955, by rfl⟩) (B 41911 (by norm_num) ⟨20955, by rfl⟩ (by norm_num))
theorem R55885 : Reach 55885 := rs (se 3 (by rfl) ⟨10478, by rfl⟩) (B 20957 (by norm_num) ⟨10478, by rfl⟩ (by norm_num))
theorem R55889 : Reach 55889 := rs (se 2 (by rfl) ⟨20958, by rfl⟩) (B 41917 (by norm_num) ⟨20958, by rfl⟩ (by norm_num))
theorem R55893 : Reach 55893 := rs (se 8 (by rfl) ⟨327, by rfl⟩) (B 655 (by norm_num) ⟨327, by rfl⟩ (by norm_num))
theorem R88661 : Reach 88661 := rs (se 8 (by rfl) ⟨519, by rfl⟩) (B 1039 (by norm_num) ⟨519, by rfl⟩ (by norm_num))
theorem R55897 : Reach 55897 := rs (se 2 (by rfl) ⟨20961, by rfl⟩) (B 41923 (by norm_num) ⟨20961, by rfl⟩ (by norm_num))
theorem R55901 : Reach 55901 := rs (se 3 (by rfl) ⟨10481, by rfl⟩) (B 20963 (by norm_num) ⟨10481, by rfl⟩ (by norm_num))
theorem R55905 : Reach 55905 := rs (se 2 (by rfl) ⟨20964, by rfl⟩) (B 41929 (by norm_num) ⟨20964, by rfl⟩ (by norm_num))
theorem R55909 : Reach 55909 := rs (se 4 (by rfl) ⟨5241, by rfl⟩) (B 10483 (by norm_num) ⟨5241, by rfl⟩ (by norm_num))
theorem R55913 : Reach 55913 := rs (se 2 (by rfl) ⟨20967, by rfl⟩) (B 41935 (by norm_num) ⟨20967, by rfl⟩ (by norm_num))
theorem R55917 : Reach 55917 := rs (se 3 (by rfl) ⟨10484, by rfl⟩) (B 20969 (by norm_num) ⟨10484, by rfl⟩ (by norm_num))
theorem R55921 : Reach 55921 := rs (se 2 (by rfl) ⟨20970, by rfl⟩) (B 41941 (by norm_num) ⟨20970, by rfl⟩ (by norm_num))
theorem R55925 : Reach 55925 := rs (se 5 (by rfl) ⟨2621, by rfl⟩) (B 5243 (by norm_num) ⟨2621, by rfl⟩ (by norm_num))
theorem R55929 : Reach 55929 := rs (se 2 (by rfl) ⟨20973, by rfl⟩) (B 41947 (by norm_num) ⟨20973, by rfl⟩ (by norm_num))
theorem R55933 : Reach 55933 := rs (se 3 (by rfl) ⟨10487, by rfl⟩) (B 20975 (by norm_num) ⟨10487, by rfl⟩ (by norm_num))
theorem R55937 : Reach 55937 := rs (se 2 (by rfl) ⟨20976, by rfl⟩) (B 41953 (by norm_num) ⟨20976, by rfl⟩ (by norm_num))
theorem R55941 : Reach 55941 := rs (se 4 (by rfl) ⟨5244, by rfl⟩) (B 10489 (by norm_num) ⟨5244, by rfl⟩ (by norm_num))
theorem R55945 : Reach 55945 := rs (se 2 (by rfl) ⟨20979, by rfl⟩) (B 41959 (by norm_num) ⟨20979, by rfl⟩ (by norm_num))
theorem R55949 : Reach 55949 := rs (se 3 (by rfl) ⟨10490, by rfl⟩) (B 20981 (by norm_num) ⟨10490, by rfl⟩ (by norm_num))
theorem R55953 : Reach 55953 := rs (se 2 (by rfl) ⟨20982, by rfl⟩) (B 41965 (by norm_num) ⟨20982, by rfl⟩ (by norm_num))
theorem R55957 : Reach 55957 := rs (se 6 (by rfl) ⟨1311, by rfl⟩) (B 2623 (by norm_num) ⟨1311, by rfl⟩ (by norm_num))
theorem R121493 : Reach 121493 := rs (se 6 (by rfl) ⟨2847, by rfl⟩) (B 5695 (by norm_num) ⟨2847, by rfl⟩ (by norm_num))
theorem R55961 : Reach 55961 := rs (se 2 (by rfl) ⟨20985, by rfl⟩) (B 41971 (by norm_num) ⟨20985, by rfl⟩ (by norm_num))
theorem R55965 : Reach 55965 := rs (se 3 (by rfl) ⟨10493, by rfl⟩) (B 20987 (by norm_num) ⟨10493, by rfl⟩ (by norm_num))
theorem R55969 : Reach 55969 := rs (se 2 (by rfl) ⟨20988, by rfl⟩) (B 41977 (by norm_num) ⟨20988, by rfl⟩ (by norm_num))
theorem R55973 : Reach 55973 := rs (se 4 (by rfl) ⟨5247, by rfl⟩) (B 10495 (by norm_num) ⟨5247, by rfl⟩ (by norm_num))
theorem R55977 : Reach 55977 := rs (se 2 (by rfl) ⟨20991, by rfl⟩) (B 41983 (by norm_num) ⟨20991, by rfl⟩ (by norm_num))
theorem R55981 : Reach 55981 := rs (se 3 (by rfl) ⟨10496, by rfl⟩) (B 20993 (by norm_num) ⟨10496, by rfl⟩ (by norm_num))
theorem R55985 : Reach 55985 := rs (se 2 (by rfl) ⟨20994, by rfl⟩) (B 41989 (by norm_num) ⟨20994, by rfl⟩ (by norm_num))
theorem R55989 : Reach 55989 := rs (se 5 (by rfl) ⟨2624, by rfl⟩) (B 5249 (by norm_num) ⟨2624, by rfl⟩ (by norm_num))
theorem R55993 : Reach 55993 := rs (se 2 (by rfl) ⟨20997, by rfl⟩) (B 41995 (by norm_num) ⟨20997, by rfl⟩ (by norm_num))
theorem R55997 : Reach 55997 := rs (se 3 (by rfl) ⟨10499, by rfl⟩) (B 20999 (by norm_num) ⟨10499, by rfl⟩ (by norm_num))
theorem R56001 : Reach 56001 := rs (se 2 (by rfl) ⟨21000, by rfl⟩) (B 42001 (by norm_num) ⟨21000, by rfl⟩ (by norm_num))
theorem R56005 : Reach 56005 := rs (se 4 (by rfl) ⟨5250, by rfl⟩) (B 10501 (by norm_num) ⟨5250, by rfl⟩ (by norm_num))
theorem R56009 : Reach 56009 := rs (se 2 (by rfl) ⟨21003, by rfl⟩) (B 42007 (by norm_num) ⟨21003, by rfl⟩ (by norm_num))
theorem R56013 : Reach 56013 := rs (se 3 (by rfl) ⟨10502, by rfl⟩) (B 21005 (by norm_num) ⟨10502, by rfl⟩ (by norm_num))
theorem R56017 : Reach 56017 := rs (se 2 (by rfl) ⟨21006, by rfl⟩) (B 42013 (by norm_num) ⟨21006, by rfl⟩ (by norm_num))
theorem R56021 : Reach 56021 := rs (se 7 (by rfl) ⟨656, by rfl⟩) (B 1313 (by norm_num) ⟨656, by rfl⟩ (by norm_num))
theorem R56025 : Reach 56025 := rs (se 2 (by rfl) ⟨21009, by rfl⟩) (B 42019 (by norm_num) ⟨21009, by rfl⟩ (by norm_num))
theorem R56029 : Reach 56029 := rs (se 3 (by rfl) ⟨10505, by rfl⟩) (B 21011 (by norm_num) ⟨10505, by rfl⟩ (by norm_num))
theorem R56033 : Reach 56033 := rs (se 2 (by rfl) ⟨21012, by rfl⟩) (B 42025 (by norm_num) ⟨21012, by rfl⟩ (by norm_num))
theorem R187109 : Reach 187109 := rs (se 4 (by rfl) ⟨17541, by rfl⟩) (B 35083 (by norm_num) ⟨17541, by rfl⟩ (by norm_num))
theorem R56037 : Reach 56037 := rs (se 4 (by rfl) ⟨5253, by rfl⟩) (B 10507 (by norm_num) ⟨5253, by rfl⟩ (by norm_num))
theorem R56041 : Reach 56041 := rs (se 2 (by rfl) ⟨21015, by rfl⟩) (B 42031 (by norm_num) ⟨21015, by rfl⟩ (by norm_num))
theorem R56045 : Reach 56045 := rs (se 3 (by rfl) ⟨10508, by rfl⟩) (B 21017 (by norm_num) ⟨10508, by rfl⟩ (by norm_num))
theorem R56049 : Reach 56049 := rs (se 2 (by rfl) ⟨21018, by rfl⟩) (B 42037 (by norm_num) ⟨21018, by rfl⟩ (by norm_num))
theorem R56053 : Reach 56053 := rs (se 5 (by rfl) ⟨2627, by rfl⟩) (B 5255 (by norm_num) ⟨2627, by rfl⟩ (by norm_num))
theorem R56057 : Reach 56057 := rs (se 2 (by rfl) ⟨21021, by rfl⟩) (B 42043 (by norm_num) ⟨21021, by rfl⟩ (by norm_num))
theorem R56061 : Reach 56061 := rs (se 3 (by rfl) ⟨10511, by rfl⟩) (B 21023 (by norm_num) ⟨10511, by rfl⟩ (by norm_num))
theorem R56065 : Reach 56065 := rs (se 2 (by rfl) ⟨21024, by rfl⟩) (B 42049 (by norm_num) ⟨21024, by rfl⟩ (by norm_num))
theorem R56069 : Reach 56069 := rs (se 4 (by rfl) ⟨5256, by rfl⟩) (B 10513 (by norm_num) ⟨5256, by rfl⟩ (by norm_num))
theorem R56073 : Reach 56073 := rs (se 2 (by rfl) ⟨21027, by rfl⟩) (B 42055 (by norm_num) ⟨21027, by rfl⟩ (by norm_num))
theorem R56077 : Reach 56077 := rs (se 3 (by rfl) ⟨10514, by rfl⟩) (B 21029 (by norm_num) ⟨10514, by rfl⟩ (by norm_num))
theorem R56081 : Reach 56081 := rs (se 2 (by rfl) ⟨21030, by rfl⟩) (B 42061 (by norm_num) ⟨21030, by rfl⟩ (by norm_num))
theorem R56085 : Reach 56085 := rs (se 6 (by rfl) ⟨1314, by rfl⟩) (B 2629 (by norm_num) ⟨1314, by rfl⟩ (by norm_num))
theorem R56089 : Reach 56089 := rs (se 2 (by rfl) ⟨21033, by rfl⟩) (B 42067 (by norm_num) ⟨21033, by rfl⟩ (by norm_num))
theorem R56093 : Reach 56093 := rs (se 3 (by rfl) ⟨10517, by rfl⟩) (B 21035 (by norm_num) ⟨10517, by rfl⟩ (by norm_num))
theorem R56097 : Reach 56097 := rs (se 2 (by rfl) ⟨21036, by rfl⟩) (B 42073 (by norm_num) ⟨21036, by rfl⟩ (by norm_num))
theorem R56101 : Reach 56101 := rs (se 4 (by rfl) ⟨5259, by rfl⟩) (B 10519 (by norm_num) ⟨5259, by rfl⟩ (by norm_num))
theorem R56105 : Reach 56105 := rs (se 2 (by rfl) ⟨21039, by rfl⟩) (B 42079 (by norm_num) ⟨21039, by rfl⟩ (by norm_num))
theorem R56109 : Reach 56109 := rs (se 3 (by rfl) ⟨10520, by rfl⟩) (B 21041 (by norm_num) ⟨10520, by rfl⟩ (by norm_num))
theorem R56113 : Reach 56113 := rs (se 2 (by rfl) ⟨21042, by rfl⟩) (B 42085 (by norm_num) ⟨21042, by rfl⟩ (by norm_num))
theorem R56117 : Reach 56117 := rs (se 5 (by rfl) ⟨2630, by rfl⟩) (B 5261 (by norm_num) ⟨2630, by rfl⟩ (by norm_num))
theorem R56121 : Reach 56121 := rs (se 2 (by rfl) ⟨21045, by rfl⟩) (B 42091 (by norm_num) ⟨21045, by rfl⟩ (by norm_num))
theorem R56125 : Reach 56125 := rs (se 3 (by rfl) ⟨10523, by rfl⟩) (B 21047 (by norm_num) ⟨10523, by rfl⟩ (by norm_num))
theorem R56129 : Reach 56129 := rs (se 2 (by rfl) ⟨21048, by rfl⟩) (B 42097 (by norm_num) ⟨21048, by rfl⟩ (by norm_num))
theorem R56133 : Reach 56133 := rs (se 4 (by rfl) ⟨5262, by rfl⟩) (B 10525 (by norm_num) ⟨5262, by rfl⟩ (by norm_num))
theorem R56137 : Reach 56137 := rs (se 2 (by rfl) ⟨21051, by rfl⟩) (B 42103 (by norm_num) ⟨21051, by rfl⟩ (by norm_num))
theorem R56141 : Reach 56141 := rs (se 3 (by rfl) ⟨10526, by rfl⟩) (B 21053 (by norm_num) ⟨10526, by rfl⟩ (by norm_num))
theorem R56145 : Reach 56145 := rs (se 2 (by rfl) ⟨21054, by rfl⟩) (B 42109 (by norm_num) ⟨21054, by rfl⟩ (by norm_num))
theorem R56149 : Reach 56149 := rs (se 9 (by rfl) ⟨164, by rfl⟩) (B 329 (by norm_num) ⟨164, by rfl⟩ (by norm_num))
theorem R56153 : Reach 56153 := rs (se 2 (by rfl) ⟨21057, by rfl⟩) (B 42115 (by norm_num) ⟨21057, by rfl⟩ (by norm_num))
theorem R56157 : Reach 56157 := rs (se 3 (by rfl) ⟨10529, by rfl⟩) (B 21059 (by norm_num) ⟨10529, by rfl⟩ (by norm_num))
theorem R56161 : Reach 56161 := rs (se 2 (by rfl) ⟨21060, by rfl⟩) (B 42121 (by norm_num) ⟨21060, by rfl⟩ (by norm_num))
theorem R88933 : Reach 88933 := rs (se 4 (by rfl) ⟨8337, by rfl⟩) (B 16675 (by norm_num) ⟨8337, by rfl⟩ (by norm_num))
theorem R56165 : Reach 56165 := rs (se 4 (by rfl) ⟨5265, by rfl⟩) (B 10531 (by norm_num) ⟨5265, by rfl⟩ (by norm_num))
theorem R56169 : Reach 56169 := rs (se 2 (by rfl) ⟨21063, by rfl⟩) (B 42127 (by norm_num) ⟨21063, by rfl⟩ (by norm_num))
theorem R56173 : Reach 56173 := rs (se 3 (by rfl) ⟨10532, by rfl⟩) (B 21065 (by norm_num) ⟨10532, by rfl⟩ (by norm_num))
theorem R56177 : Reach 56177 := rs (se 2 (by rfl) ⟨21066, by rfl⟩) (B 42133 (by norm_num) ⟨21066, by rfl⟩ (by norm_num))
theorem R56181 : Reach 56181 := rs (se 5 (by rfl) ⟨2633, by rfl⟩) (B 5267 (by norm_num) ⟨2633, by rfl⟩ (by norm_num))
theorem R56185 : Reach 56185 := rs (se 2 (by rfl) ⟨21069, by rfl⟩) (B 42139 (by norm_num) ⟨21069, by rfl⟩ (by norm_num))
theorem R56189 : Reach 56189 := rs (se 3 (by rfl) ⟨10535, by rfl⟩) (B 21071 (by norm_num) ⟨10535, by rfl⟩ (by norm_num))
theorem R56193 : Reach 56193 := rs (se 2 (by rfl) ⟨21072, by rfl⟩) (B 42145 (by norm_num) ⟨21072, by rfl⟩ (by norm_num))
theorem R56197 : Reach 56197 := rs (se 4 (by rfl) ⟨5268, by rfl⟩) (B 10537 (by norm_num) ⟨5268, by rfl⟩ (by norm_num))
theorem R56201 : Reach 56201 := rs (se 2 (by rfl) ⟨21075, by rfl⟩) (B 42151 (by norm_num) ⟨21075, by rfl⟩ (by norm_num))
theorem R56205 : Reach 56205 := rs (se 3 (by rfl) ⟨10538, by rfl⟩) (B 21077 (by norm_num) ⟨10538, by rfl⟩ (by norm_num))
theorem R56209 : Reach 56209 := rs (se 2 (by rfl) ⟨21078, by rfl⟩) (B 42157 (by norm_num) ⟨21078, by rfl⟩ (by norm_num))
theorem R56213 : Reach 56213 := rs (se 6 (by rfl) ⟨1317, by rfl⟩) (B 2635 (by norm_num) ⟨1317, by rfl⟩ (by norm_num))
theorem R187285 : Reach 187285 := rs (se 6 (by rfl) ⟨4389, by rfl⟩) (B 8779 (by norm_num) ⟨4389, by rfl⟩ (by norm_num))
theorem R56217 : Reach 56217 := rs (se 2 (by rfl) ⟨21081, by rfl⟩) (B 42163 (by norm_num) ⟨21081, by rfl⟩ (by norm_num))
theorem R56221 : Reach 56221 := rs (se 3 (by rfl) ⟨10541, by rfl⟩) (B 21083 (by norm_num) ⟨10541, by rfl⟩ (by norm_num))
theorem R56225 : Reach 56225 := rs (se 2 (by rfl) ⟨21084, by rfl⟩) (B 42169 (by norm_num) ⟨21084, by rfl⟩ (by norm_num))
theorem R56229 : Reach 56229 := rs (se 4 (by rfl) ⟨5271, by rfl⟩) (B 10543 (by norm_num) ⟨5271, by rfl⟩ (by norm_num))
theorem R285605 : Reach 285605 := rs (se 4 (by rfl) ⟨26775, by rfl⟩) (B 53551 (by norm_num) ⟨26775, by rfl⟩ (by norm_num))
theorem R56233 : Reach 56233 := rs (se 2 (by rfl) ⟨21087, by rfl⟩) (B 42175 (by norm_num) ⟨21087, by rfl⟩ (by norm_num))
theorem R56237 : Reach 56237 := rs (se 3 (by rfl) ⟨10544, by rfl⟩) (B 21089 (by norm_num) ⟨10544, by rfl⟩ (by norm_num))
theorem R56241 : Reach 56241 := rs (se 2 (by rfl) ⟨21090, by rfl⟩) (B 42181 (by norm_num) ⟨21090, by rfl⟩ (by norm_num))
theorem R56245 : Reach 56245 := rs (se 5 (by rfl) ⟨2636, by rfl⟩) (B 5273 (by norm_num) ⟨2636, by rfl⟩ (by norm_num))
theorem R56249 : Reach 56249 := rs (se 2 (by rfl) ⟨21093, by rfl⟩) (B 42187 (by norm_num) ⟨21093, by rfl⟩ (by norm_num))
theorem R56253 : Reach 56253 := rs (se 3 (by rfl) ⟨10547, by rfl⟩) (B 21095 (by norm_num) ⟨10547, by rfl⟩ (by norm_num))
theorem R56257 : Reach 56257 := rs (se 2 (by rfl) ⟨21096, by rfl⟩) (B 42193 (by norm_num) ⟨21096, by rfl⟩ (by norm_num))
theorem R89029 : Reach 89029 := rs (se 4 (by rfl) ⟨8346, by rfl⟩) (B 16693 (by norm_num) ⟨8346, by rfl⟩ (by norm_num))
theorem R56261 : Reach 56261 := rs (se 4 (by rfl) ⟨5274, by rfl⟩) (B 10549 (by norm_num) ⟨5274, by rfl⟩ (by norm_num))
theorem R56265 : Reach 56265 := rs (se 2 (by rfl) ⟨21099, by rfl⟩) (B 42199 (by norm_num) ⟨21099, by rfl⟩ (by norm_num))
theorem R56269 : Reach 56269 := rs (se 3 (by rfl) ⟨10550, by rfl⟩) (B 21101 (by norm_num) ⟨10550, by rfl⟩ (by norm_num))
theorem R56273 : Reach 56273 := rs (se 2 (by rfl) ⟨21102, by rfl⟩) (B 42205 (by norm_num) ⟨21102, by rfl⟩ (by norm_num))
theorem R56277 : Reach 56277 := rs (se 7 (by rfl) ⟨659, by rfl⟩) (B 1319 (by norm_num) ⟨659, by rfl⟩ (by norm_num))
theorem R220117 : Reach 220117 := rs (se 7 (by rfl) ⟨2579, by rfl⟩) (B 5159 (by norm_num) ⟨2579, by rfl⟩ (by norm_num))
theorem R56281 : Reach 56281 := rs (se 2 (by rfl) ⟨21105, by rfl⟩) (B 42211 (by norm_num) ⟨21105, by rfl⟩ (by norm_num))
theorem R56285 : Reach 56285 := rs (se 3 (by rfl) ⟨10553, by rfl⟩) (B 21107 (by norm_num) ⟨10553, by rfl⟩ (by norm_num))
theorem R56289 : Reach 56289 := rs (se 2 (by rfl) ⟨21108, by rfl⟩) (B 42217 (by norm_num) ⟨21108, by rfl⟩ (by norm_num))
theorem R56293 : Reach 56293 := rs (se 4 (by rfl) ⟨5277, by rfl⟩) (B 10555 (by norm_num) ⟨5277, by rfl⟩ (by norm_num))
theorem R56297 : Reach 56297 := rs (se 2 (by rfl) ⟨21111, by rfl⟩) (B 42223 (by norm_num) ⟨21111, by rfl⟩ (by norm_num))
theorem R56301 : Reach 56301 := rs (se 3 (by rfl) ⟨10556, by rfl⟩) (B 21113 (by norm_num) ⟨10556, by rfl⟩ (by norm_num))
theorem R56305 : Reach 56305 := rs (se 2 (by rfl) ⟨21114, by rfl⟩) (B 42229 (by norm_num) ⟨21114, by rfl⟩ (by norm_num))
theorem R56309 : Reach 56309 := rs (se 5 (by rfl) ⟨2639, by rfl⟩) (B 5279 (by norm_num) ⟨2639, by rfl⟩ (by norm_num))
theorem R56313 : Reach 56313 := rs (se 2 (by rfl) ⟨21117, by rfl⟩) (B 42235 (by norm_num) ⟨21117, by rfl⟩ (by norm_num))
theorem R56317 : Reach 56317 := rs (se 3 (by rfl) ⟨10559, by rfl⟩) (B 21119 (by norm_num) ⟨10559, by rfl⟩ (by norm_num))
theorem R56321 : Reach 56321 := rs (se 2 (by rfl) ⟨21120, by rfl⟩) (B 42241 (by norm_num) ⟨21120, by rfl⟩ (by norm_num))
theorem R56325 : Reach 56325 := rs (se 4 (by rfl) ⟨5280, by rfl⟩) (B 10561 (by norm_num) ⟨5280, by rfl⟩ (by norm_num))
theorem R56329 : Reach 56329 := rs (se 2 (by rfl) ⟨21123, by rfl⟩) (B 42247 (by norm_num) ⟨21123, by rfl⟩ (by norm_num))
theorem R56333 : Reach 56333 := rs (se 3 (by rfl) ⟨10562, by rfl⟩) (B 21125 (by norm_num) ⟨10562, by rfl⟩ (by norm_num))
theorem R56337 : Reach 56337 := rs (se 2 (by rfl) ⟨21126, by rfl⟩) (B 42253 (by norm_num) ⟨21126, by rfl⟩ (by norm_num))
theorem R56341 : Reach 56341 := rs (se 6 (by rfl) ⟨1320, by rfl⟩) (B 2641 (by norm_num) ⟨1320, by rfl⟩ (by norm_num))
theorem R56345 : Reach 56345 := rs (se 2 (by rfl) ⟨21129, by rfl⟩) (B 42259 (by norm_num) ⟨21129, by rfl⟩ (by norm_num))
theorem R56349 : Reach 56349 := rs (se 3 (by rfl) ⟨10565, by rfl⟩) (B 21131 (by norm_num) ⟨10565, by rfl⟩ (by norm_num))
theorem R56353 : Reach 56353 := rs (se 2 (by rfl) ⟨21132, by rfl⟩) (B 42265 (by norm_num) ⟨21132, by rfl⟩ (by norm_num))
theorem R56357 : Reach 56357 := rs (se 4 (by rfl) ⟨5283, by rfl⟩) (B 10567 (by norm_num) ⟨5283, by rfl⟩ (by norm_num))
theorem R56361 : Reach 56361 := rs (se 2 (by rfl) ⟨21135, by rfl⟩) (B 42271 (by norm_num) ⟨21135, by rfl⟩ (by norm_num))
theorem R56365 : Reach 56365 := rs (se 3 (by rfl) ⟨10568, by rfl⟩) (B 21137 (by norm_num) ⟨10568, by rfl⟩ (by norm_num))
theorem R56369 : Reach 56369 := rs (se 2 (by rfl) ⟨21138, by rfl⟩) (B 42277 (by norm_num) ⟨21138, by rfl⟩ (by norm_num))
theorem R56373 : Reach 56373 := rs (se 5 (by rfl) ⟨2642, by rfl⟩) (B 5285 (by norm_num) ⟨2642, by rfl⟩ (by norm_num))
theorem R56377 : Reach 56377 := rs (se 2 (by rfl) ⟨21141, by rfl⟩) (B 42283 (by norm_num) ⟨21141, by rfl⟩ (by norm_num))
theorem R56381 : Reach 56381 := rs (se 3 (by rfl) ⟨10571, by rfl⟩) (B 21143 (by norm_num) ⟨10571, by rfl⟩ (by norm_num))
theorem R56385 : Reach 56385 := rs (se 2 (by rfl) ⟨21144, by rfl⟩) (B 42289 (by norm_num) ⟨21144, by rfl⟩ (by norm_num))
theorem R56389 : Reach 56389 := rs (se 4 (by rfl) ⟨5286, by rfl⟩) (B 10573 (by norm_num) ⟨5286, by rfl⟩ (by norm_num))
theorem R56393 : Reach 56393 := rs (se 2 (by rfl) ⟨21147, by rfl⟩) (B 42295 (by norm_num) ⟨21147, by rfl⟩ (by norm_num))
theorem R56397 : Reach 56397 := rs (se 3 (by rfl) ⟨10574, by rfl⟩) (B 21149 (by norm_num) ⟨10574, by rfl⟩ (by norm_num))
theorem R56401 : Reach 56401 := rs (se 2 (by rfl) ⟨21150, by rfl⟩) (B 42301 (by norm_num) ⟨21150, by rfl⟩ (by norm_num))
theorem R56405 : Reach 56405 := rs (se 8 (by rfl) ⟨330, by rfl⟩) (B 661 (by norm_num) ⟨330, by rfl⟩ (by norm_num))
theorem R56409 : Reach 56409 := rs (se 2 (by rfl) ⟨21153, by rfl⟩) (B 42307 (by norm_num) ⟨21153, by rfl⟩ (by norm_num))
theorem R56413 : Reach 56413 := rs (se 3 (by rfl) ⟨10577, by rfl⟩) (B 21155 (by norm_num) ⟨10577, by rfl⟩ (by norm_num))
theorem R56417 : Reach 56417 := rs (se 2 (by rfl) ⟨21156, by rfl⟩) (B 42313 (by norm_num) ⟨21156, by rfl⟩ (by norm_num))
theorem R89189 : Reach 89189 := rs (se 4 (by rfl) ⟨8361, by rfl⟩) (B 16723 (by norm_num) ⟨8361, by rfl⟩ (by norm_num))
theorem R56421 : Reach 56421 := rs (se 4 (by rfl) ⟨5289, by rfl⟩) (B 10579 (by norm_num) ⟨5289, by rfl⟩ (by norm_num))
theorem R56425 : Reach 56425 := rs (se 2 (by rfl) ⟨21159, by rfl⟩) (B 42319 (by norm_num) ⟨21159, by rfl⟩ (by norm_num))
theorem R56429 : Reach 56429 := rs (se 3 (by rfl) ⟨10580, by rfl⟩) (B 21161 (by norm_num) ⟨10580, by rfl⟩ (by norm_num))
theorem R56433 : Reach 56433 := rs (se 2 (by rfl) ⟨21162, by rfl⟩) (B 42325 (by norm_num) ⟨21162, by rfl⟩ (by norm_num))
theorem R56437 : Reach 56437 := rs (se 5 (by rfl) ⟨2645, by rfl⟩) (B 5291 (by norm_num) ⟨2645, by rfl⟩ (by norm_num))
theorem R56441 : Reach 56441 := rs (se 2 (by rfl) ⟨21165, by rfl⟩) (B 42331 (by norm_num) ⟨21165, by rfl⟩ (by norm_num))
theorem R56445 : Reach 56445 := rs (se 3 (by rfl) ⟨10583, by rfl⟩) (B 21167 (by norm_num) ⟨10583, by rfl⟩ (by norm_num))
theorem R56449 : Reach 56449 := rs (se 2 (by rfl) ⟨21168, by rfl⟩) (B 42337 (by norm_num) ⟨21168, by rfl⟩ (by norm_num))
theorem R56453 : Reach 56453 := rs (se 4 (by rfl) ⟨5292, by rfl⟩) (B 10585 (by norm_num) ⟨5292, by rfl⟩ (by norm_num))
theorem R56457 : Reach 56457 := rs (se 2 (by rfl) ⟨21171, by rfl⟩) (B 42343 (by norm_num) ⟨21171, by rfl⟩ (by norm_num))
theorem R56461 : Reach 56461 := rs (se 3 (by rfl) ⟨10586, by rfl⟩) (B 21173 (by norm_num) ⟨10586, by rfl⟩ (by norm_num))
theorem R56465 : Reach 56465 := rs (se 2 (by rfl) ⟨21174, by rfl⟩) (B 42349 (by norm_num) ⟨21174, by rfl⟩ (by norm_num))
theorem R187541 : Reach 187541 := rs (se 6 (by rfl) ⟨4395, by rfl⟩) (B 8791 (by norm_num) ⟨4395, by rfl⟩ (by norm_num))
theorem R56469 : Reach 56469 := rs (se 6 (by rfl) ⟨1323, by rfl⟩) (B 2647 (by norm_num) ⟨1323, by rfl⟩ (by norm_num))
theorem R56473 : Reach 56473 := rs (se 2 (by rfl) ⟨21177, by rfl⟩) (B 42355 (by norm_num) ⟨21177, by rfl⟩ (by norm_num))
theorem R56477 : Reach 56477 := rs (se 3 (by rfl) ⟨10589, by rfl⟩) (B 21179 (by norm_num) ⟨10589, by rfl⟩ (by norm_num))
theorem R56481 : Reach 56481 := rs (se 2 (by rfl) ⟨21180, by rfl⟩) (B 42361 (by norm_num) ⟨21180, by rfl⟩ (by norm_num))
theorem R56485 : Reach 56485 := rs (se 4 (by rfl) ⟨5295, by rfl⟩) (B 10591 (by norm_num) ⟨5295, by rfl⟩ (by norm_num))
theorem R56489 : Reach 56489 := rs (se 2 (by rfl) ⟨21183, by rfl⟩) (B 42367 (by norm_num) ⟨21183, by rfl⟩ (by norm_num))
theorem R56493 : Reach 56493 := rs (se 3 (by rfl) ⟨10592, by rfl⟩) (B 21185 (by norm_num) ⟨10592, by rfl⟩ (by norm_num))
theorem R56497 : Reach 56497 := rs (se 2 (by rfl) ⟨21186, by rfl⟩) (B 42373 (by norm_num) ⟨21186, by rfl⟩ (by norm_num))
theorem R56501 : Reach 56501 := rs (se 5 (by rfl) ⟨2648, by rfl⟩) (B 5297 (by norm_num) ⟨2648, by rfl⟩ (by norm_num))
theorem R56505 : Reach 56505 := rs (se 2 (by rfl) ⟨21189, by rfl⟩) (B 42379 (by norm_num) ⟨21189, by rfl⟩ (by norm_num))
theorem R56509 : Reach 56509 := rs (se 3 (by rfl) ⟨10595, by rfl⟩) (B 21191 (by norm_num) ⟨10595, by rfl⟩ (by norm_num))
theorem R56513 : Reach 56513 := rs (se 2 (by rfl) ⟨21192, by rfl⟩) (B 42385 (by norm_num) ⟨21192, by rfl⟩ (by norm_num))
theorem R56517 : Reach 56517 := rs (se 4 (by rfl) ⟨5298, by rfl⟩) (B 10597 (by norm_num) ⟨5298, by rfl⟩ (by norm_num))
theorem R56521 : Reach 56521 := rs (se 2 (by rfl) ⟨21195, by rfl⟩) (B 42391 (by norm_num) ⟨21195, by rfl⟩ (by norm_num))
theorem R56525 : Reach 56525 := rs (se 3 (by rfl) ⟨10598, by rfl⟩) (B 21197 (by norm_num) ⟨10598, by rfl⟩ (by norm_num))
theorem R56529 : Reach 56529 := rs (se 2 (by rfl) ⟨21198, by rfl⟩) (B 42397 (by norm_num) ⟨21198, by rfl⟩ (by norm_num))
theorem R56533 : Reach 56533 := rs (se 7 (by rfl) ⟨662, by rfl⟩) (B 1325 (by norm_num) ⟨662, by rfl⟩ (by norm_num))
theorem R56537 : Reach 56537 := rs (se 2 (by rfl) ⟨21201, by rfl⟩) (B 42403 (by norm_num) ⟨21201, by rfl⟩ (by norm_num))
theorem R56541 : Reach 56541 := rs (se 3 (by rfl) ⟨10601, by rfl⟩) (B 21203 (by norm_num) ⟨10601, by rfl⟩ (by norm_num))
theorem R56545 : Reach 56545 := rs (se 2 (by rfl) ⟨21204, by rfl⟩) (B 42409 (by norm_num) ⟨21204, by rfl⟩ (by norm_num))
theorem R56549 : Reach 56549 := rs (se 4 (by rfl) ⟨5301, by rfl⟩) (B 10603 (by norm_num) ⟨5301, by rfl⟩ (by norm_num))
theorem R56553 : Reach 56553 := rs (se 2 (by rfl) ⟨21207, by rfl⟩) (B 42415 (by norm_num) ⟨21207, by rfl⟩ (by norm_num))
theorem R56557 : Reach 56557 := rs (se 3 (by rfl) ⟨10604, by rfl⟩) (B 21209 (by norm_num) ⟨10604, by rfl⟩ (by norm_num))
theorem R56561 : Reach 56561 := rs (se 2 (by rfl) ⟨21210, by rfl⟩) (B 42421 (by norm_num) ⟨21210, by rfl⟩ (by norm_num))
theorem R56565 : Reach 56565 := rs (se 5 (by rfl) ⟨2651, by rfl⟩) (B 5303 (by norm_num) ⟨2651, by rfl⟩ (by norm_num))
theorem R56569 : Reach 56569 := rs (se 2 (by rfl) ⟨21213, by rfl⟩) (B 42427 (by norm_num) ⟨21213, by rfl⟩ (by norm_num))
theorem R56573 : Reach 56573 := rs (se 3 (by rfl) ⟨10607, by rfl⟩) (B 21215 (by norm_num) ⟨10607, by rfl⟩ (by norm_num))
theorem R56577 : Reach 56577 := rs (se 2 (by rfl) ⟨21216, by rfl⟩) (B 42433 (by norm_num) ⟨21216, by rfl⟩ (by norm_num))
theorem R56581 : Reach 56581 := rs (se 4 (by rfl) ⟨5304, by rfl⟩) (B 10609 (by norm_num) ⟨5304, by rfl⟩ (by norm_num))
theorem R56585 : Reach 56585 := rs (se 2 (by rfl) ⟨21219, by rfl⟩) (B 42439 (by norm_num) ⟨21219, by rfl⟩ (by norm_num))
theorem R56589 : Reach 56589 := rs (se 3 (by rfl) ⟨10610, by rfl⟩) (B 21221 (by norm_num) ⟨10610, by rfl⟩ (by norm_num))
theorem R56593 : Reach 56593 := rs (se 2 (by rfl) ⟨21222, by rfl⟩) (B 42445 (by norm_num) ⟨21222, by rfl⟩ (by norm_num))
theorem R56597 : Reach 56597 := rs (se 6 (by rfl) ⟨1326, by rfl⟩) (B 2653 (by norm_num) ⟨1326, by rfl⟩ (by norm_num))
theorem R56601 : Reach 56601 := rs (se 2 (by rfl) ⟨21225, by rfl⟩) (B 42451 (by norm_num) ⟨21225, by rfl⟩ (by norm_num))
theorem R56605 : Reach 56605 := rs (se 3 (by rfl) ⟨10613, by rfl⟩) (B 21227 (by norm_num) ⟨10613, by rfl⟩ (by norm_num))
theorem R56609 : Reach 56609 := rs (se 2 (by rfl) ⟨21228, by rfl⟩) (B 42457 (by norm_num) ⟨21228, by rfl⟩ (by norm_num))
theorem R56613 : Reach 56613 := rs (se 4 (by rfl) ⟨5307, by rfl⟩) (B 10615 (by norm_num) ⟨5307, by rfl⟩ (by norm_num))
theorem R56617 : Reach 56617 := rs (se 2 (by rfl) ⟨21231, by rfl⟩) (B 42463 (by norm_num) ⟨21231, by rfl⟩ (by norm_num))
theorem R56621 : Reach 56621 := rs (se 3 (by rfl) ⟨10616, by rfl⟩) (B 21233 (by norm_num) ⟨10616, by rfl⟩ (by norm_num))
theorem R56625 : Reach 56625 := rs (se 2 (by rfl) ⟨21234, by rfl⟩) (B 42469 (by norm_num) ⟨21234, by rfl⟩ (by norm_num))
theorem R56629 : Reach 56629 := rs (se 5 (by rfl) ⟨2654, by rfl⟩) (B 5309 (by norm_num) ⟨2654, by rfl⟩ (by norm_num))
theorem R122165 : Reach 122165 := rs (se 5 (by rfl) ⟨5726, by rfl⟩) (B 11453 (by norm_num) ⟨5726, by rfl⟩ (by norm_num))
theorem R56633 : Reach 56633 := rs (se 2 (by rfl) ⟨21237, by rfl⟩) (B 42475 (by norm_num) ⟨21237, by rfl⟩ (by norm_num))
theorem R56637 : Reach 56637 := rs (se 3 (by rfl) ⟨10619, by rfl⟩) (B 21239 (by norm_num) ⟨10619, by rfl⟩ (by norm_num))
theorem R56641 : Reach 56641 := rs (se 2 (by rfl) ⟨21240, by rfl⟩) (B 42481 (by norm_num) ⟨21240, by rfl⟩ (by norm_num))
theorem R56645 : Reach 56645 := rs (se 4 (by rfl) ⟨5310, by rfl⟩) (B 10621 (by norm_num) ⟨5310, by rfl⟩ (by norm_num))
theorem R56649 : Reach 56649 := rs (se 2 (by rfl) ⟨21243, by rfl⟩) (B 42487 (by norm_num) ⟨21243, by rfl⟩ (by norm_num))
theorem R56653 : Reach 56653 := rs (se 3 (by rfl) ⟨10622, by rfl⟩) (B 21245 (by norm_num) ⟨10622, by rfl⟩ (by norm_num))
theorem R56657 : Reach 56657 := rs (se 2 (by rfl) ⟨21246, by rfl⟩) (B 42493 (by norm_num) ⟨21246, by rfl⟩ (by norm_num))
theorem R56661 : Reach 56661 := rs (se 11 (by rfl) ⟨41, by rfl⟩) (B 83 (by norm_num) ⟨41, by rfl⟩ (by norm_num))
theorem R187733 : Reach 187733 := rs (se 11 (by rfl) ⟨137, by rfl⟩) (B 275 (by norm_num) ⟨137, by rfl⟩ (by norm_num))
theorem R56665 : Reach 56665 := rs (se 2 (by rfl) ⟨21249, by rfl⟩) (B 42499 (by norm_num) ⟨21249, by rfl⟩ (by norm_num))
theorem R56669 : Reach 56669 := rs (se 3 (by rfl) ⟨10625, by rfl⟩) (B 21251 (by norm_num) ⟨10625, by rfl⟩ (by norm_num))
theorem R56673 : Reach 56673 := rs (se 2 (by rfl) ⟨21252, by rfl⟩) (B 42505 (by norm_num) ⟨21252, by rfl⟩ (by norm_num))
theorem R56677 : Reach 56677 := rs (se 4 (by rfl) ⟨5313, by rfl⟩) (B 10627 (by norm_num) ⟨5313, by rfl⟩ (by norm_num))
theorem R56681 : Reach 56681 := rs (se 2 (by rfl) ⟨21255, by rfl⟩) (B 42511 (by norm_num) ⟨21255, by rfl⟩ (by norm_num))
theorem R56685 : Reach 56685 := rs (se 3 (by rfl) ⟨10628, by rfl⟩) (B 21257 (by norm_num) ⟨10628, by rfl⟩ (by norm_num))
theorem R56689 : Reach 56689 := rs (se 2 (by rfl) ⟨21258, by rfl⟩) (B 42517 (by norm_num) ⟨21258, by rfl⟩ (by norm_num))
theorem R56693 : Reach 56693 := rs (se 5 (by rfl) ⟨2657, by rfl⟩) (B 5315 (by norm_num) ⟨2657, by rfl⟩ (by norm_num))
theorem R154997 : Reach 154997 := rs (se 5 (by rfl) ⟨7265, by rfl⟩) (B 14531 (by norm_num) ⟨7265, by rfl⟩ (by norm_num))
theorem R56697 : Reach 56697 := rs (se 2 (by rfl) ⟨21261, by rfl⟩) (B 42523 (by norm_num) ⟨21261, by rfl⟩ (by norm_num))
theorem R56701 : Reach 56701 := rs (se 3 (by rfl) ⟨10631, by rfl⟩) (B 21263 (by norm_num) ⟨10631, by rfl⟩ (by norm_num))
theorem R56705 : Reach 56705 := rs (se 2 (by rfl) ⟨21264, by rfl⟩) (B 42529 (by norm_num) ⟨21264, by rfl⟩ (by norm_num))
theorem R56709 : Reach 56709 := rs (se 4 (by rfl) ⟨5316, by rfl⟩) (B 10633 (by norm_num) ⟨5316, by rfl⟩ (by norm_num))
theorem R56713 : Reach 56713 := rs (se 2 (by rfl) ⟨21267, by rfl⟩) (B 42535 (by norm_num) ⟨21267, by rfl⟩ (by norm_num))
theorem R56717 : Reach 56717 := rs (se 3 (by rfl) ⟨10634, by rfl⟩) (B 21269 (by norm_num) ⟨10634, by rfl⟩ (by norm_num))
theorem R56721 : Reach 56721 := rs (se 2 (by rfl) ⟨21270, by rfl⟩) (B 42541 (by norm_num) ⟨21270, by rfl⟩ (by norm_num))
theorem R56725 : Reach 56725 := rs (se 6 (by rfl) ⟨1329, by rfl⟩) (B 2659 (by norm_num) ⟨1329, by rfl⟩ (by norm_num))
theorem R56729 : Reach 56729 := rs (se 2 (by rfl) ⟨21273, by rfl⟩) (B 42547 (by norm_num) ⟨21273, by rfl⟩ (by norm_num))
theorem R56733 : Reach 56733 := rs (se 3 (by rfl) ⟨10637, by rfl⟩) (B 21275 (by norm_num) ⟨10637, by rfl⟩ (by norm_num))
theorem R56737 : Reach 56737 := rs (se 2 (by rfl) ⟨21276, by rfl⟩) (B 42553 (by norm_num) ⟨21276, by rfl⟩ (by norm_num))
theorem R56741 : Reach 56741 := rs (se 4 (by rfl) ⟨5319, by rfl⟩) (B 10639 (by norm_num) ⟨5319, by rfl⟩ (by norm_num))
theorem R56745 : Reach 56745 := rs (se 2 (by rfl) ⟨21279, by rfl⟩) (B 42559 (by norm_num) ⟨21279, by rfl⟩ (by norm_num))
theorem R56749 : Reach 56749 := rs (se 3 (by rfl) ⟨10640, by rfl⟩) (B 21281 (by norm_num) ⟨10640, by rfl⟩ (by norm_num))
theorem R122285 : Reach 122285 := rs (se 3 (by rfl) ⟨22928, by rfl⟩) (B 45857 (by norm_num) ⟨22928, by rfl⟩ (by norm_num))
theorem R56753 : Reach 56753 := rs (se 2 (by rfl) ⟨21282, by rfl⟩) (B 42565 (by norm_num) ⟨21282, by rfl⟩ (by norm_num))
theorem R56757 : Reach 56757 := rs (se 5 (by rfl) ⟨2660, by rfl⟩) (B 5321 (by norm_num) ⟨2660, by rfl⟩ (by norm_num))
theorem R56761 : Reach 56761 := rs (se 2 (by rfl) ⟨21285, by rfl⟩) (B 42571 (by norm_num) ⟨21285, by rfl⟩ (by norm_num))
theorem R56765 : Reach 56765 := rs (se 3 (by rfl) ⟨10643, by rfl⟩) (B 21287 (by norm_num) ⟨10643, by rfl⟩ (by norm_num))
theorem R56769 : Reach 56769 := rs (se 2 (by rfl) ⟨21288, by rfl⟩) (B 42577 (by norm_num) ⟨21288, by rfl⟩ (by norm_num))
theorem R253381 : Reach 253381 := rs (se 4 (by rfl) ⟨23754, by rfl⟩) (B 47509 (by norm_num) ⟨23754, by rfl⟩ (by norm_num))
theorem R56773 : Reach 56773 := rs (se 4 (by rfl) ⟨5322, by rfl⟩) (B 10645 (by norm_num) ⟨5322, by rfl⟩ (by norm_num))
theorem R56777 : Reach 56777 := rs (se 2 (by rfl) ⟨21291, by rfl⟩) (B 42583 (by norm_num) ⟨21291, by rfl⟩ (by norm_num))
theorem R56781 : Reach 56781 := rs (se 3 (by rfl) ⟨10646, by rfl⟩) (B 21293 (by norm_num) ⟨10646, by rfl⟩ (by norm_num))
theorem R56785 : Reach 56785 := rs (se 2 (by rfl) ⟨21294, by rfl⟩) (B 42589 (by norm_num) ⟨21294, by rfl⟩ (by norm_num))
theorem R56789 : Reach 56789 := rs (se 7 (by rfl) ⟨665, by rfl⟩) (B 1331 (by norm_num) ⟨665, by rfl⟩ (by norm_num))
theorem R56793 : Reach 56793 := rs (se 2 (by rfl) ⟨21297, by rfl⟩) (B 42595 (by norm_num) ⟨21297, by rfl⟩ (by norm_num))
theorem R56797 : Reach 56797 := rs (se 3 (by rfl) ⟨10649, by rfl⟩) (B 21299 (by norm_num) ⟨10649, by rfl⟩ (by norm_num))
theorem R56801 : Reach 56801 := rs (se 2 (by rfl) ⟨21300, by rfl⟩) (B 42601 (by norm_num) ⟨21300, by rfl⟩ (by norm_num))
theorem R56805 : Reach 56805 := rs (se 4 (by rfl) ⟨5325, by rfl⟩) (B 10651 (by norm_num) ⟨5325, by rfl⟩ (by norm_num))
theorem R56809 : Reach 56809 := rs (se 2 (by rfl) ⟨21303, by rfl⟩) (B 42607 (by norm_num) ⟨21303, by rfl⟩ (by norm_num))
theorem R56813 : Reach 56813 := rs (se 3 (by rfl) ⟨10652, by rfl⟩) (B 21305 (by norm_num) ⟨10652, by rfl⟩ (by norm_num))
theorem R56817 : Reach 56817 := rs (se 2 (by rfl) ⟨21306, by rfl⟩) (B 42613 (by norm_num) ⟨21306, by rfl⟩ (by norm_num))
theorem R56821 : Reach 56821 := rs (se 5 (by rfl) ⟨2663, by rfl⟩) (B 5327 (by norm_num) ⟨2663, by rfl⟩ (by norm_num))
theorem R56825 : Reach 56825 := rs (se 2 (by rfl) ⟨21309, by rfl⟩) (B 42619 (by norm_num) ⟨21309, by rfl⟩ (by norm_num))
theorem R56829 : Reach 56829 := rs (se 3 (by rfl) ⟨10655, by rfl⟩) (B 21311 (by norm_num) ⟨10655, by rfl⟩ (by norm_num))
theorem R56833 : Reach 56833 := rs (se 2 (by rfl) ⟨21312, by rfl⟩) (B 42625 (by norm_num) ⟨21312, by rfl⟩ (by norm_num))
theorem R56837 : Reach 56837 := rs (se 4 (by rfl) ⟨5328, by rfl⟩) (B 10657 (by norm_num) ⟨5328, by rfl⟩ (by norm_num))
theorem R56841 : Reach 56841 := rs (se 2 (by rfl) ⟨21315, by rfl⟩) (B 42631 (by norm_num) ⟨21315, by rfl⟩ (by norm_num))
theorem R56845 : Reach 56845 := rs (se 3 (by rfl) ⟨10658, by rfl⟩) (B 21317 (by norm_num) ⟨10658, by rfl⟩ (by norm_num))
theorem R56849 : Reach 56849 := rs (se 2 (by rfl) ⟨21318, by rfl⟩) (B 42637 (by norm_num) ⟨21318, by rfl⟩ (by norm_num))
theorem R56853 : Reach 56853 := rs (se 6 (by rfl) ⟨1332, by rfl⟩) (B 2665 (by norm_num) ⟨1332, by rfl⟩ (by norm_num))
theorem R56857 : Reach 56857 := rs (se 2 (by rfl) ⟨21321, by rfl⟩) (B 42643 (by norm_num) ⟨21321, by rfl⟩ (by norm_num))
theorem R56861 : Reach 56861 := rs (se 3 (by rfl) ⟨10661, by rfl⟩) (B 21323 (by norm_num) ⟨10661, by rfl⟩ (by norm_num))
theorem R56865 : Reach 56865 := rs (se 2 (by rfl) ⟨21324, by rfl⟩) (B 42649 (by norm_num) ⟨21324, by rfl⟩ (by norm_num))
theorem R56869 : Reach 56869 := rs (se 4 (by rfl) ⟨5331, by rfl⟩) (B 10663 (by norm_num) ⟨5331, by rfl⟩ (by norm_num))
theorem R56873 : Reach 56873 := rs (se 2 (by rfl) ⟨21327, by rfl⟩) (B 42655 (by norm_num) ⟨21327, by rfl⟩ (by norm_num))
theorem R56877 : Reach 56877 := rs (se 3 (by rfl) ⟨10664, by rfl⟩) (B 21329 (by norm_num) ⟨10664, by rfl⟩ (by norm_num))
theorem R56881 : Reach 56881 := rs (se 2 (by rfl) ⟨21330, by rfl⟩) (B 42661 (by norm_num) ⟨21330, by rfl⟩ (by norm_num))
theorem R56885 : Reach 56885 := rs (se 5 (by rfl) ⟨2666, by rfl⟩) (B 5333 (by norm_num) ⟨2666, by rfl⟩ (by norm_num))
theorem R56889 : Reach 56889 := rs (se 2 (by rfl) ⟨21333, by rfl⟩) (B 42667 (by norm_num) ⟨21333, by rfl⟩ (by norm_num))
theorem R56893 : Reach 56893 := rs (se 3 (by rfl) ⟨10667, by rfl⟩) (B 21335 (by norm_num) ⟨10667, by rfl⟩ (by norm_num))
theorem R56897 : Reach 56897 := rs (se 2 (by rfl) ⟨21336, by rfl⟩) (B 42673 (by norm_num) ⟨21336, by rfl⟩ (by norm_num))
theorem R187973 : Reach 187973 := rs (se 4 (by rfl) ⟨17622, by rfl⟩) (B 35245 (by norm_num) ⟨17622, by rfl⟩ (by norm_num))
theorem R56901 : Reach 56901 := rs (se 4 (by rfl) ⟨5334, by rfl⟩) (B 10669 (by norm_num) ⟨5334, by rfl⟩ (by norm_num))
theorem R56905 : Reach 56905 := rs (se 2 (by rfl) ⟨21339, by rfl⟩) (B 42679 (by norm_num) ⟨21339, by rfl⟩ (by norm_num))
theorem R56909 : Reach 56909 := rs (se 3 (by rfl) ⟨10670, by rfl⟩) (B 21341 (by norm_num) ⟨10670, by rfl⟩ (by norm_num))
theorem R56913 : Reach 56913 := rs (se 2 (by rfl) ⟨21342, by rfl⟩) (B 42685 (by norm_num) ⟨21342, by rfl⟩ (by norm_num))
theorem R56917 : Reach 56917 := rs (se 8 (by rfl) ⟨333, by rfl⟩) (B 667 (by norm_num) ⟨333, by rfl⟩ (by norm_num))
theorem R56921 : Reach 56921 := rs (se 2 (by rfl) ⟨21345, by rfl⟩) (B 42691 (by norm_num) ⟨21345, by rfl⟩ (by norm_num))
theorem R56925 : Reach 56925 := rs (se 3 (by rfl) ⟨10673, by rfl⟩) (B 21347 (by norm_num) ⟨10673, by rfl⟩ (by norm_num))
theorem R56929 : Reach 56929 := rs (se 2 (by rfl) ⟨21348, by rfl⟩) (B 42697 (by norm_num) ⟨21348, by rfl⟩ (by norm_num))
theorem R56933 : Reach 56933 := rs (se 4 (by rfl) ⟨5337, by rfl⟩) (B 10675 (by norm_num) ⟨5337, by rfl⟩ (by norm_num))
theorem R56937 : Reach 56937 := rs (se 2 (by rfl) ⟨21351, by rfl⟩) (B 42703 (by norm_num) ⟨21351, by rfl⟩ (by norm_num))
theorem R56941 : Reach 56941 := rs (se 3 (by rfl) ⟨10676, by rfl⟩) (B 21353 (by norm_num) ⟨10676, by rfl⟩ (by norm_num))
theorem R56945 : Reach 56945 := rs (se 2 (by rfl) ⟨21354, by rfl⟩) (B 42709 (by norm_num) ⟨21354, by rfl⟩ (by norm_num))
theorem R56949 : Reach 56949 := rs (se 5 (by rfl) ⟨2669, by rfl⟩) (B 5339 (by norm_num) ⟨2669, by rfl⟩ (by norm_num))
theorem R56953 : Reach 56953 := rs (se 2 (by rfl) ⟨21357, by rfl⟩) (B 42715 (by norm_num) ⟨21357, by rfl⟩ (by norm_num))
theorem R56957 : Reach 56957 := rs (se 3 (by rfl) ⟨10679, by rfl⟩) (B 21359 (by norm_num) ⟨10679, by rfl⟩ (by norm_num))
theorem R56961 : Reach 56961 := rs (se 2 (by rfl) ⟨21360, by rfl⟩) (B 42721 (by norm_num) ⟨21360, by rfl⟩ (by norm_num))
theorem R56965 : Reach 56965 := rs (se 4 (by rfl) ⟨5340, by rfl⟩) (B 10681 (by norm_num) ⟨5340, by rfl⟩ (by norm_num))
theorem R56969 : Reach 56969 := rs (se 2 (by rfl) ⟨21363, by rfl⟩) (B 42727 (by norm_num) ⟨21363, by rfl⟩ (by norm_num))
theorem R56973 : Reach 56973 := rs (se 3 (by rfl) ⟨10682, by rfl⟩) (B 21365 (by norm_num) ⟨10682, by rfl⟩ (by norm_num))
theorem R56977 : Reach 56977 := rs (se 2 (by rfl) ⟨21366, by rfl⟩) (B 42733 (by norm_num) ⟨21366, by rfl⟩ (by norm_num))
theorem R56981 : Reach 56981 := rs (se 6 (by rfl) ⟨1335, by rfl⟩) (B 2671 (by norm_num) ⟨1335, by rfl⟩ (by norm_num))
theorem R56985 : Reach 56985 := rs (se 2 (by rfl) ⟨21369, by rfl⟩) (B 42739 (by norm_num) ⟨21369, by rfl⟩ (by norm_num))
theorem R56989 : Reach 56989 := rs (se 3 (by rfl) ⟨10685, by rfl⟩) (B 21371 (by norm_num) ⟨10685, by rfl⟩ (by norm_num))
theorem R56993 : Reach 56993 := rs (se 2 (by rfl) ⟨21372, by rfl⟩) (B 42745 (by norm_num) ⟨21372, by rfl⟩ (by norm_num))
theorem R56997 : Reach 56997 := rs (se 4 (by rfl) ⟨5343, by rfl⟩) (B 10687 (by norm_num) ⟨5343, by rfl⟩ (by norm_num))
theorem R57001 : Reach 57001 := rs (se 2 (by rfl) ⟨21375, by rfl⟩) (B 42751 (by norm_num) ⟨21375, by rfl⟩ (by norm_num))
theorem R57005 : Reach 57005 := rs (se 3 (by rfl) ⟨10688, by rfl⟩) (B 21377 (by norm_num) ⟨10688, by rfl⟩ (by norm_num))
theorem R57009 : Reach 57009 := rs (se 2 (by rfl) ⟨21378, by rfl⟩) (B 42757 (by norm_num) ⟨21378, by rfl⟩ (by norm_num))
theorem R57013 : Reach 57013 := rs (se 5 (by rfl) ⟨2672, by rfl⟩) (B 5345 (by norm_num) ⟨2672, by rfl⟩ (by norm_num))
theorem R57017 : Reach 57017 := rs (se 2 (by rfl) ⟨21381, by rfl⟩) (B 42763 (by norm_num) ⟨21381, by rfl⟩ (by norm_num))
theorem R57021 : Reach 57021 := rs (se 3 (by rfl) ⟨10691, by rfl⟩) (B 21383 (by norm_num) ⟨10691, by rfl⟩ (by norm_num))
theorem R57025 : Reach 57025 := rs (se 2 (by rfl) ⟨21384, by rfl⟩) (B 42769 (by norm_num) ⟨21384, by rfl⟩ (by norm_num))
theorem R57029 : Reach 57029 := rs (se 4 (by rfl) ⟨5346, by rfl⟩) (B 10693 (by norm_num) ⟨5346, by rfl⟩ (by norm_num))
theorem R57033 : Reach 57033 := rs (se 2 (by rfl) ⟨21387, by rfl⟩) (B 42775 (by norm_num) ⟨21387, by rfl⟩ (by norm_num))
theorem R57037 : Reach 57037 := rs (se 3 (by rfl) ⟨10694, by rfl⟩) (B 21389 (by norm_num) ⟨10694, by rfl⟩ (by norm_num))
theorem R57041 : Reach 57041 := rs (se 2 (by rfl) ⟨21390, by rfl⟩) (B 42781 (by norm_num) ⟨21390, by rfl⟩ (by norm_num))
theorem R57045 : Reach 57045 := rs (se 7 (by rfl) ⟨668, by rfl⟩) (B 1337 (by norm_num) ⟨668, by rfl⟩ (by norm_num))
theorem R57049 : Reach 57049 := rs (se 2 (by rfl) ⟨21393, by rfl⟩) (B 42787 (by norm_num) ⟨21393, by rfl⟩ (by norm_num))
theorem R57053 : Reach 57053 := rs (se 3 (by rfl) ⟨10697, by rfl⟩) (B 21395 (by norm_num) ⟨10697, by rfl⟩ (by norm_num))
theorem R57057 : Reach 57057 := rs (se 2 (by rfl) ⟨21396, by rfl⟩) (B 42793 (by norm_num) ⟨21396, by rfl⟩ (by norm_num))
theorem R57061 : Reach 57061 := rs (se 4 (by rfl) ⟨5349, by rfl⟩) (B 10699 (by norm_num) ⟨5349, by rfl⟩ (by norm_num))
theorem R57065 : Reach 57065 := rs (se 2 (by rfl) ⟨21399, by rfl⟩) (B 42799 (by norm_num) ⟨21399, by rfl⟩ (by norm_num))
theorem R57069 : Reach 57069 := rs (se 3 (by rfl) ⟨10700, by rfl⟩) (B 21401 (by norm_num) ⟨10700, by rfl⟩ (by norm_num))
theorem R57073 : Reach 57073 := rs (se 2 (by rfl) ⟨21402, by rfl⟩) (B 42805 (by norm_num) ⟨21402, by rfl⟩ (by norm_num))
theorem R57077 : Reach 57077 := rs (se 5 (by rfl) ⟨2675, by rfl⟩) (B 5351 (by norm_num) ⟨2675, by rfl⟩ (by norm_num))
theorem R57081 : Reach 57081 := rs (se 2 (by rfl) ⟨21405, by rfl⟩) (B 42811 (by norm_num) ⟨21405, by rfl⟩ (by norm_num))
theorem R57085 : Reach 57085 := rs (se 3 (by rfl) ⟨10703, by rfl⟩) (B 21407 (by norm_num) ⟨10703, by rfl⟩ (by norm_num))
theorem R57089 : Reach 57089 := rs (se 2 (by rfl) ⟨21408, by rfl⟩) (B 42817 (by norm_num) ⟨21408, by rfl⟩ (by norm_num))
theorem R57093 : Reach 57093 := rs (se 4 (by rfl) ⟨5352, by rfl⟩) (B 10705 (by norm_num) ⟨5352, by rfl⟩ (by norm_num))
theorem R57097 : Reach 57097 := rs (se 2 (by rfl) ⟨21411, by rfl⟩) (B 42823 (by norm_num) ⟨21411, by rfl⟩ (by norm_num))
theorem R57101 : Reach 57101 := rs (se 3 (by rfl) ⟨10706, by rfl⟩) (B 21413 (by norm_num) ⟨10706, by rfl⟩ (by norm_num))
theorem R57105 : Reach 57105 := rs (se 2 (by rfl) ⟨21414, by rfl⟩) (B 42829 (by norm_num) ⟨21414, by rfl⟩ (by norm_num))
theorem R57109 : Reach 57109 := rs (se 6 (by rfl) ⟨1338, by rfl⟩) (B 2677 (by norm_num) ⟨1338, by rfl⟩ (by norm_num))
theorem R57113 : Reach 57113 := rs (se 2 (by rfl) ⟨21417, by rfl⟩) (B 42835 (by norm_num) ⟨21417, by rfl⟩ (by norm_num))
theorem R57117 : Reach 57117 := rs (se 3 (by rfl) ⟨10709, by rfl⟩) (B 21419 (by norm_num) ⟨10709, by rfl⟩ (by norm_num))
theorem R57121 : Reach 57121 := rs (se 2 (by rfl) ⟨21420, by rfl⟩) (B 42841 (by norm_num) ⟨21420, by rfl⟩ (by norm_num))
theorem R57125 : Reach 57125 := rs (se 4 (by rfl) ⟨5355, by rfl⟩) (B 10711 (by norm_num) ⟨5355, by rfl⟩ (by norm_num))
theorem R155429 : Reach 155429 := rs (se 4 (by rfl) ⟨14571, by rfl⟩) (B 29143 (by norm_num) ⟨14571, by rfl⟩ (by norm_num))
theorem R57129 : Reach 57129 := rs (se 2 (by rfl) ⟨21423, by rfl⟩) (B 42847 (by norm_num) ⟨21423, by rfl⟩ (by norm_num))
theorem R57133 : Reach 57133 := rs (se 3 (by rfl) ⟨10712, by rfl⟩) (B 21425 (by norm_num) ⟨10712, by rfl⟩ (by norm_num))
theorem R57137 : Reach 57137 := rs (se 2 (by rfl) ⟨21426, by rfl⟩) (B 42853 (by norm_num) ⟨21426, by rfl⟩ (by norm_num))
theorem R57141 : Reach 57141 := rs (se 5 (by rfl) ⟨2678, by rfl⟩) (B 5357 (by norm_num) ⟨2678, by rfl⟩ (by norm_num))
theorem R57145 : Reach 57145 := rs (se 2 (by rfl) ⟨21429, by rfl⟩) (B 42859 (by norm_num) ⟨21429, by rfl⟩ (by norm_num))
theorem R57149 : Reach 57149 := rs (se 3 (by rfl) ⟨10715, by rfl⟩) (B 21431 (by norm_num) ⟨10715, by rfl⟩ (by norm_num))
theorem R57153 : Reach 57153 := rs (se 2 (by rfl) ⟨21432, by rfl⟩) (B 42865 (by norm_num) ⟨21432, by rfl⟩ (by norm_num))
theorem R57157 : Reach 57157 := rs (se 4 (by rfl) ⟨5358, by rfl⟩) (B 10717 (by norm_num) ⟨5358, by rfl⟩ (by norm_num))
theorem R57161 : Reach 57161 := rs (se 2 (by rfl) ⟨21435, by rfl⟩) (B 42871 (by norm_num) ⟨21435, by rfl⟩ (by norm_num))
theorem R57165 : Reach 57165 := rs (se 3 (by rfl) ⟨10718, by rfl⟩) (B 21437 (by norm_num) ⟨10718, by rfl⟩ (by norm_num))
theorem R57169 : Reach 57169 := rs (se 2 (by rfl) ⟨21438, by rfl⟩) (B 42877 (by norm_num) ⟨21438, by rfl⟩ (by norm_num))
theorem R57173 : Reach 57173 := rs (se 9 (by rfl) ⟨167, by rfl⟩) (B 335 (by norm_num) ⟨167, by rfl⟩ (by norm_num))
theorem R57177 : Reach 57177 := rs (se 2 (by rfl) ⟨21441, by rfl⟩) (B 42883 (by norm_num) ⟨21441, by rfl⟩ (by norm_num))
theorem R57181 : Reach 57181 := rs (se 3 (by rfl) ⟨10721, by rfl⟩) (B 21443 (by norm_num) ⟨10721, by rfl⟩ (by norm_num))
theorem R57185 : Reach 57185 := rs (se 2 (by rfl) ⟨21444, by rfl⟩) (B 42889 (by norm_num) ⟨21444, by rfl⟩ (by norm_num))
theorem R57189 : Reach 57189 := rs (se 4 (by rfl) ⟨5361, by rfl⟩) (B 10723 (by norm_num) ⟨5361, by rfl⟩ (by norm_num))
theorem R57193 : Reach 57193 := rs (se 2 (by rfl) ⟨21447, by rfl⟩) (B 42895 (by norm_num) ⟨21447, by rfl⟩ (by norm_num))
theorem R57197 : Reach 57197 := rs (se 3 (by rfl) ⟨10724, by rfl⟩) (B 21449 (by norm_num) ⟨10724, by rfl⟩ (by norm_num))
theorem R57201 : Reach 57201 := rs (se 2 (by rfl) ⟨21450, by rfl⟩) (B 42901 (by norm_num) ⟨21450, by rfl⟩ (by norm_num))
theorem R57205 : Reach 57205 := rs (se 5 (by rfl) ⟨2681, by rfl⟩) (B 5363 (by norm_num) ⟨2681, by rfl⟩ (by norm_num))
theorem R57209 : Reach 57209 := rs (se 2 (by rfl) ⟨21453, by rfl⟩) (B 42907 (by norm_num) ⟨21453, by rfl⟩ (by norm_num))
theorem R57213 : Reach 57213 := rs (se 3 (by rfl) ⟨10727, by rfl⟩) (B 21455 (by norm_num) ⟨10727, by rfl⟩ (by norm_num))
theorem R57217 : Reach 57217 := rs (se 2 (by rfl) ⟨21456, by rfl⟩) (B 42913 (by norm_num) ⟨21456, by rfl⟩ (by norm_num))
theorem R57221 : Reach 57221 := rs (se 4 (by rfl) ⟨5364, by rfl⟩) (B 10729 (by norm_num) ⟨5364, by rfl⟩ (by norm_num))
theorem R57225 : Reach 57225 := rs (se 2 (by rfl) ⟨21459, by rfl⟩) (B 42919 (by norm_num) ⟨21459, by rfl⟩ (by norm_num))
theorem R57229 : Reach 57229 := rs (se 3 (by rfl) ⟨10730, by rfl⟩) (B 21461 (by norm_num) ⟨10730, by rfl⟩ (by norm_num))
theorem R57233 : Reach 57233 := rs (se 2 (by rfl) ⟨21462, by rfl⟩) (B 42925 (by norm_num) ⟨21462, by rfl⟩ (by norm_num))
theorem R57237 : Reach 57237 := rs (se 6 (by rfl) ⟨1341, by rfl⟩) (B 2683 (by norm_num) ⟨1341, by rfl⟩ (by norm_num))
theorem R57241 : Reach 57241 := rs (se 2 (by rfl) ⟨21465, by rfl⟩) (B 42931 (by norm_num) ⟨21465, by rfl⟩ (by norm_num))
theorem R57245 : Reach 57245 := rs (se 3 (by rfl) ⟨10733, by rfl⟩) (B 21467 (by norm_num) ⟨10733, by rfl⟩ (by norm_num))
theorem R57249 : Reach 57249 := rs (se 2 (by rfl) ⟨21468, by rfl⟩) (B 42937 (by norm_num) ⟨21468, by rfl⟩ (by norm_num))
theorem R57253 : Reach 57253 := rs (se 4 (by rfl) ⟨5367, by rfl⟩) (B 10735 (by norm_num) ⟨5367, by rfl⟩ (by norm_num))
theorem R57257 : Reach 57257 := rs (se 2 (by rfl) ⟨21471, by rfl⟩) (B 42943 (by norm_num) ⟨21471, by rfl⟩ (by norm_num))
theorem R57261 : Reach 57261 := rs (se 3 (by rfl) ⟨10736, by rfl⟩) (B 21473 (by norm_num) ⟨10736, by rfl⟩ (by norm_num))
theorem R57265 : Reach 57265 := rs (se 2 (by rfl) ⟨21474, by rfl⟩) (B 42949 (by norm_num) ⟨21474, by rfl⟩ (by norm_num))
theorem R57269 : Reach 57269 := rs (se 5 (by rfl) ⟨2684, by rfl⟩) (B 5369 (by norm_num) ⟨2684, by rfl⟩ (by norm_num))
theorem R57273 : Reach 57273 := rs (se 2 (by rfl) ⟨21477, by rfl⟩) (B 42955 (by norm_num) ⟨21477, by rfl⟩ (by norm_num))
theorem R57277 : Reach 57277 := rs (se 3 (by rfl) ⟨10739, by rfl⟩) (B 21479 (by norm_num) ⟨10739, by rfl⟩ (by norm_num))
theorem R57281 : Reach 57281 := rs (se 2 (by rfl) ⟨21480, by rfl⟩) (B 42961 (by norm_num) ⟨21480, by rfl⟩ (by norm_num))
theorem R57285 : Reach 57285 := rs (se 4 (by rfl) ⟨5370, by rfl⟩) (B 10741 (by norm_num) ⟨5370, by rfl⟩ (by norm_num))
theorem R57289 : Reach 57289 := rs (se 2 (by rfl) ⟨21483, by rfl⟩) (B 42967 (by norm_num) ⟨21483, by rfl⟩ (by norm_num))
theorem R57293 : Reach 57293 := rs (se 3 (by rfl) ⟨10742, by rfl⟩) (B 21485 (by norm_num) ⟨10742, by rfl⟩ (by norm_num))
theorem R57297 : Reach 57297 := rs (se 2 (by rfl) ⟨21486, by rfl⟩) (B 42973 (by norm_num) ⟨21486, by rfl⟩ (by norm_num))
theorem R57301 : Reach 57301 := rs (se 7 (by rfl) ⟨671, by rfl⟩) (B 1343 (by norm_num) ⟨671, by rfl⟩ (by norm_num))
theorem R57305 : Reach 57305 := rs (se 2 (by rfl) ⟨21489, by rfl⟩) (B 42979 (by norm_num) ⟨21489, by rfl⟩ (by norm_num))
theorem R57309 : Reach 57309 := rs (se 3 (by rfl) ⟨10745, by rfl⟩) (B 21491 (by norm_num) ⟨10745, by rfl⟩ (by norm_num))
theorem R57313 : Reach 57313 := rs (se 2 (by rfl) ⟨21492, by rfl⟩) (B 42985 (by norm_num) ⟨21492, by rfl⟩ (by norm_num))
theorem R57317 : Reach 57317 := rs (se 4 (by rfl) ⟨5373, by rfl⟩) (B 10747 (by norm_num) ⟨5373, by rfl⟩ (by norm_num))
theorem R57321 : Reach 57321 := rs (se 2 (by rfl) ⟨21495, by rfl⟩) (B 42991 (by norm_num) ⟨21495, by rfl⟩ (by norm_num))
theorem R57325 : Reach 57325 := rs (se 3 (by rfl) ⟨10748, by rfl⟩) (B 21497 (by norm_num) ⟨10748, by rfl⟩ (by norm_num))
theorem R57329 : Reach 57329 := rs (se 2 (by rfl) ⟨21498, by rfl⟩) (B 42997 (by norm_num) ⟨21498, by rfl⟩ (by norm_num))
theorem R188405 : Reach 188405 := rs (se 5 (by rfl) ⟨8831, by rfl⟩) (B 17663 (by norm_num) ⟨8831, by rfl⟩ (by norm_num))
theorem R57333 : Reach 57333 := rs (se 5 (by rfl) ⟨2687, by rfl⟩) (B 5375 (by norm_num) ⟨2687, by rfl⟩ (by norm_num))
theorem R57337 : Reach 57337 := rs (se 2 (by rfl) ⟨21501, by rfl⟩) (B 43003 (by norm_num) ⟨21501, by rfl⟩ (by norm_num))
theorem R57341 : Reach 57341 := rs (se 3 (by rfl) ⟨10751, by rfl⟩) (B 21503 (by norm_num) ⟨10751, by rfl⟩ (by norm_num))
theorem R57345 : Reach 57345 := rs (se 2 (by rfl) ⟨21504, by rfl⟩) (B 43009 (by norm_num) ⟨21504, by rfl⟩ (by norm_num))
theorem R57349 : Reach 57349 := rs (se 4 (by rfl) ⟨5376, by rfl⟩) (B 10753 (by norm_num) ⟨5376, by rfl⟩ (by norm_num))
theorem R57353 : Reach 57353 := rs (se 2 (by rfl) ⟨21507, by rfl⟩) (B 43015 (by norm_num) ⟨21507, by rfl⟩ (by norm_num))
theorem R57357 : Reach 57357 := rs (se 3 (by rfl) ⟨10754, by rfl⟩) (B 21509 (by norm_num) ⟨10754, by rfl⟩ (by norm_num))
theorem R57361 : Reach 57361 := rs (se 2 (by rfl) ⟨21510, by rfl⟩) (B 43021 (by norm_num) ⟨21510, by rfl⟩ (by norm_num))
theorem R57365 : Reach 57365 := rs (se 6 (by rfl) ⟨1344, by rfl⟩) (B 2689 (by norm_num) ⟨1344, by rfl⟩ (by norm_num))
theorem R57369 : Reach 57369 := rs (se 2 (by rfl) ⟨21513, by rfl⟩) (B 43027 (by norm_num) ⟨21513, by rfl⟩ (by norm_num))
theorem R57373 : Reach 57373 := rs (se 3 (by rfl) ⟨10757, by rfl⟩) (B 21515 (by norm_num) ⟨10757, by rfl⟩ (by norm_num))
theorem R57377 : Reach 57377 := rs (se 2 (by rfl) ⟨21516, by rfl⟩) (B 43033 (by norm_num) ⟨21516, by rfl⟩ (by norm_num))
theorem R57381 : Reach 57381 := rs (se 4 (by rfl) ⟨5379, by rfl⟩) (B 10759 (by norm_num) ⟨5379, by rfl⟩ (by norm_num))
theorem R122917 : Reach 122917 := rs (se 4 (by rfl) ⟨11523, by rfl⟩) (B 23047 (by norm_num) ⟨11523, by rfl⟩ (by norm_num))
theorem R57385 : Reach 57385 := rs (se 2 (by rfl) ⟨21519, by rfl⟩) (B 43039 (by norm_num) ⟨21519, by rfl⟩ (by norm_num))
theorem R57389 : Reach 57389 := rs (se 3 (by rfl) ⟨10760, by rfl⟩) (B 21521 (by norm_num) ⟨10760, by rfl⟩ (by norm_num))
theorem R57393 : Reach 57393 := rs (se 2 (by rfl) ⟨21522, by rfl⟩) (B 43045 (by norm_num) ⟨21522, by rfl⟩ (by norm_num))
theorem R57397 : Reach 57397 := rs (se 5 (by rfl) ⟨2690, by rfl⟩) (B 5381 (by norm_num) ⟨2690, by rfl⟩ (by norm_num))
theorem R221237 : Reach 221237 := rs (se 5 (by rfl) ⟨10370, by rfl⟩) (B 20741 (by norm_num) ⟨10370, by rfl⟩ (by norm_num))
theorem R57401 : Reach 57401 := rs (se 2 (by rfl) ⟨21525, by rfl⟩) (B 43051 (by norm_num) ⟨21525, by rfl⟩ (by norm_num))
theorem R57405 : Reach 57405 := rs (se 3 (by rfl) ⟨10763, by rfl⟩) (B 21527 (by norm_num) ⟨10763, by rfl⟩ (by norm_num))
theorem R57409 : Reach 57409 := rs (se 2 (by rfl) ⟨21528, by rfl⟩) (B 43057 (by norm_num) ⟨21528, by rfl⟩ (by norm_num))
theorem R57413 : Reach 57413 := rs (se 4 (by rfl) ⟨5382, by rfl⟩) (B 10765 (by norm_num) ⟨5382, by rfl⟩ (by norm_num))
theorem R57417 : Reach 57417 := rs (se 2 (by rfl) ⟨21531, by rfl⟩) (B 43063 (by norm_num) ⟨21531, by rfl⟩ (by norm_num))
theorem R57421 : Reach 57421 := rs (se 3 (by rfl) ⟨10766, by rfl⟩) (B 21533 (by norm_num) ⟨10766, by rfl⟩ (by norm_num))
theorem R57425 : Reach 57425 := rs (se 2 (by rfl) ⟨21534, by rfl⟩) (B 43069 (by norm_num) ⟨21534, by rfl⟩ (by norm_num))
theorem R680021 : Reach 680021 := rs (se 8 (by rfl) ⟨3984, by rfl⟩) (B 7969 (by norm_num) ⟨3984, by rfl⟩ (by norm_num))
theorem R57429 : Reach 57429 := rs (se 8 (by rfl) ⟨336, by rfl⟩) (B 673 (by norm_num) ⟨336, by rfl⟩ (by norm_num))
theorem R286805 : Reach 286805 := rs (se 8 (by rfl) ⟨1680, by rfl⟩) (B 3361 (by norm_num) ⟨1680, by rfl⟩ (by norm_num))
theorem R57433 : Reach 57433 := rs (se 2 (by rfl) ⟨21537, by rfl⟩) (B 43075 (by norm_num) ⟨21537, by rfl⟩ (by norm_num))
theorem R57437 : Reach 57437 := rs (se 3 (by rfl) ⟨10769, by rfl⟩) (B 21539 (by norm_num) ⟨10769, by rfl⟩ (by norm_num))
theorem R57441 : Reach 57441 := rs (se 2 (by rfl) ⟨21540, by rfl⟩) (B 43081 (by norm_num) ⟨21540, by rfl⟩ (by norm_num))
theorem R57445 : Reach 57445 := rs (se 4 (by rfl) ⟨5385, by rfl⟩) (B 10771 (by norm_num) ⟨5385, by rfl⟩ (by norm_num))
theorem R57449 : Reach 57449 := rs (se 2 (by rfl) ⟨21543, by rfl⟩) (B 43087 (by norm_num) ⟨21543, by rfl⟩ (by norm_num))
theorem R57453 : Reach 57453 := rs (se 3 (by rfl) ⟨10772, by rfl⟩) (B 21545 (by norm_num) ⟨10772, by rfl⟩ (by norm_num))
theorem R57457 : Reach 57457 := rs (se 2 (by rfl) ⟨21546, by rfl⟩) (B 43093 (by norm_num) ⟨21546, by rfl⟩ (by norm_num))
theorem R57461 : Reach 57461 := rs (se 5 (by rfl) ⟨2693, by rfl⟩) (B 5387 (by norm_num) ⟨2693, by rfl⟩ (by norm_num))
theorem R57465 : Reach 57465 := rs (se 2 (by rfl) ⟨21549, by rfl⟩) (B 43099 (by norm_num) ⟨21549, by rfl⟩ (by norm_num))
theorem R57469 : Reach 57469 := rs (se 3 (by rfl) ⟨10775, by rfl⟩) (B 21551 (by norm_num) ⟨10775, by rfl⟩ (by norm_num))
theorem R57473 : Reach 57473 := rs (se 2 (by rfl) ⟨21552, by rfl⟩) (B 43105 (by norm_num) ⟨21552, by rfl⟩ (by norm_num))
theorem R57477 : Reach 57477 := rs (se 4 (by rfl) ⟨5388, by rfl⟩) (B 10777 (by norm_num) ⟨5388, by rfl⟩ (by norm_num))
theorem R57481 : Reach 57481 := rs (se 2 (by rfl) ⟨21555, by rfl⟩) (B 43111 (by norm_num) ⟨21555, by rfl⟩ (by norm_num))
theorem R57485 : Reach 57485 := rs (se 3 (by rfl) ⟨10778, by rfl⟩) (B 21557 (by norm_num) ⟨10778, by rfl⟩ (by norm_num))
theorem R57489 : Reach 57489 := rs (se 2 (by rfl) ⟨21558, by rfl⟩) (B 43117 (by norm_num) ⟨21558, by rfl⟩ (by norm_num))
theorem R57493 : Reach 57493 := rs (se 6 (by rfl) ⟨1347, by rfl⟩) (B 2695 (by norm_num) ⟨1347, by rfl⟩ (by norm_num))
theorem R57497 : Reach 57497 := rs (se 2 (by rfl) ⟨21561, by rfl⟩) (B 43123 (by norm_num) ⟨21561, by rfl⟩ (by norm_num))
theorem R57501 : Reach 57501 := rs (se 3 (by rfl) ⟨10781, by rfl⟩) (B 21563 (by norm_num) ⟨10781, by rfl⟩ (by norm_num))
theorem R57505 : Reach 57505 := rs (se 2 (by rfl) ⟨21564, by rfl⟩) (B 43129 (by norm_num) ⟨21564, by rfl⟩ (by norm_num))
theorem R57509 : Reach 57509 := rs (se 4 (by rfl) ⟨5391, by rfl⟩) (B 10783 (by norm_num) ⟨5391, by rfl⟩ (by norm_num))
theorem R57513 : Reach 57513 := rs (se 2 (by rfl) ⟨21567, by rfl⟩) (B 43135 (by norm_num) ⟨21567, by rfl⟩ (by norm_num))
theorem R57517 : Reach 57517 := rs (se 3 (by rfl) ⟨10784, by rfl⟩) (B 21569 (by norm_num) ⟨10784, by rfl⟩ (by norm_num))
theorem R57521 : Reach 57521 := rs (se 2 (by rfl) ⟨21570, by rfl⟩) (B 43141 (by norm_num) ⟨21570, by rfl⟩ (by norm_num))
theorem R286901 : Reach 286901 := rs (se 5 (by rfl) ⟨13448, by rfl⟩) (B 26897 (by norm_num) ⟨13448, by rfl⟩ (by norm_num))
theorem R57525 : Reach 57525 := rs (se 5 (by rfl) ⟨2696, by rfl⟩) (B 5393 (by norm_num) ⟨2696, by rfl⟩ (by norm_num))
theorem R57529 : Reach 57529 := rs (se 2 (by rfl) ⟨21573, by rfl⟩) (B 43147 (by norm_num) ⟨21573, by rfl⟩ (by norm_num))
theorem R57533 : Reach 57533 := rs (se 3 (by rfl) ⟨10787, by rfl⟩) (B 21575 (by norm_num) ⟨10787, by rfl⟩ (by norm_num))
theorem R57537 : Reach 57537 := rs (se 2 (by rfl) ⟨21576, by rfl⟩) (B 43153 (by norm_num) ⟨21576, by rfl⟩ (by norm_num))
theorem R57541 : Reach 57541 := rs (se 4 (by rfl) ⟨5394, by rfl⟩) (B 10789 (by norm_num) ⟨5394, by rfl⟩ (by norm_num))
theorem R57545 : Reach 57545 := rs (se 2 (by rfl) ⟨21579, by rfl⟩) (B 43159 (by norm_num) ⟨21579, by rfl⟩ (by norm_num))
theorem R90317 : Reach 90317 := rs (se 3 (by rfl) ⟨16934, by rfl⟩) (B 33869 (by norm_num) ⟨16934, by rfl⟩ (by norm_num))
theorem R57549 : Reach 57549 := rs (se 3 (by rfl) ⟨10790, by rfl⟩) (B 21581 (by norm_num) ⟨10790, by rfl⟩ (by norm_num))
theorem R57553 : Reach 57553 := rs (se 2 (by rfl) ⟨21582, by rfl⟩) (B 43165 (by norm_num) ⟨21582, by rfl⟩ (by norm_num))
theorem R57557 : Reach 57557 := rs (se 7 (by rfl) ⟨674, by rfl⟩) (B 1349 (by norm_num) ⟨674, by rfl⟩ (by norm_num))
theorem R57561 : Reach 57561 := rs (se 2 (by rfl) ⟨21585, by rfl⟩) (B 43171 (by norm_num) ⟨21585, by rfl⟩ (by norm_num))
theorem R57565 : Reach 57565 := rs (se 3 (by rfl) ⟨10793, by rfl⟩) (B 21587 (by norm_num) ⟨10793, by rfl⟩ (by norm_num))
theorem R57569 : Reach 57569 := rs (se 2 (by rfl) ⟨21588, by rfl⟩) (B 43177 (by norm_num) ⟨21588, by rfl⟩ (by norm_num))
theorem R57573 : Reach 57573 := rs (se 4 (by rfl) ⟨5397, by rfl⟩) (B 10795 (by norm_num) ⟨5397, by rfl⟩ (by norm_num))
theorem R57577 : Reach 57577 := rs (se 2 (by rfl) ⟨21591, by rfl⟩) (B 43183 (by norm_num) ⟨21591, by rfl⟩ (by norm_num))
theorem R57581 : Reach 57581 := rs (se 3 (by rfl) ⟨10796, by rfl⟩) (B 21593 (by norm_num) ⟨10796, by rfl⟩ (by norm_num))
theorem R57585 : Reach 57585 := rs (se 2 (by rfl) ⟨21594, by rfl⟩) (B 43189 (by norm_num) ⟨21594, by rfl⟩ (by norm_num))
theorem R57589 : Reach 57589 := rs (se 5 (by rfl) ⟨2699, by rfl⟩) (B 5399 (by norm_num) ⟨2699, by rfl⟩ (by norm_num))
theorem R57593 : Reach 57593 := rs (se 2 (by rfl) ⟨21597, by rfl⟩) (B 43195 (by norm_num) ⟨21597, by rfl⟩ (by norm_num))
theorem R57597 : Reach 57597 := rs (se 3 (by rfl) ⟨10799, by rfl⟩) (B 21599 (by norm_num) ⟨10799, by rfl⟩ (by norm_num))
theorem R57601 : Reach 57601 := rs (se 2 (by rfl) ⟨21600, by rfl⟩) (B 43201 (by norm_num) ⟨21600, by rfl⟩ (by norm_num))
theorem R57605 : Reach 57605 := rs (se 4 (by rfl) ⟨5400, by rfl⟩) (B 10801 (by norm_num) ⟨5400, by rfl⟩ (by norm_num))
theorem R57609 : Reach 57609 := rs (se 2 (by rfl) ⟨21603, by rfl⟩) (B 43207 (by norm_num) ⟨21603, by rfl⟩ (by norm_num))
theorem R57613 : Reach 57613 := rs (se 3 (by rfl) ⟨10802, by rfl⟩) (B 21605 (by norm_num) ⟨10802, by rfl⟩ (by norm_num))
theorem R57617 : Reach 57617 := rs (se 2 (by rfl) ⟨21606, by rfl⟩) (B 43213 (by norm_num) ⟨21606, by rfl⟩ (by norm_num))
theorem R57621 : Reach 57621 := rs (se 6 (by rfl) ⟨1350, by rfl⟩) (B 2701 (by norm_num) ⟨1350, by rfl⟩ (by norm_num))
theorem R57625 : Reach 57625 := rs (se 2 (by rfl) ⟨21609, by rfl⟩) (B 43219 (by norm_num) ⟨21609, by rfl⟩ (by norm_num))
theorem R57629 : Reach 57629 := rs (se 3 (by rfl) ⟨10805, by rfl⟩) (B 21611 (by norm_num) ⟨10805, by rfl⟩ (by norm_num))
theorem R57633 : Reach 57633 := rs (se 2 (by rfl) ⟨21612, by rfl⟩) (B 43225 (by norm_num) ⟨21612, by rfl⟩ (by norm_num))
theorem R57637 : Reach 57637 := rs (se 4 (by rfl) ⟨5403, by rfl⟩) (B 10807 (by norm_num) ⟨5403, by rfl⟩ (by norm_num))
theorem R57641 : Reach 57641 := rs (se 2 (by rfl) ⟨21615, by rfl⟩) (B 43231 (by norm_num) ⟨21615, by rfl⟩ (by norm_num))
theorem R57645 : Reach 57645 := rs (se 3 (by rfl) ⟨10808, by rfl⟩) (B 21617 (by norm_num) ⟨10808, by rfl⟩ (by norm_num))
theorem R57649 : Reach 57649 := rs (se 2 (by rfl) ⟨21618, by rfl⟩) (B 43237 (by norm_num) ⟨21618, by rfl⟩ (by norm_num))
theorem R57653 : Reach 57653 := rs (se 5 (by rfl) ⟨2702, by rfl⟩) (B 5405 (by norm_num) ⟨2702, by rfl⟩ (by norm_num))
theorem R57657 : Reach 57657 := rs (se 2 (by rfl) ⟨21621, by rfl⟩) (B 43243 (by norm_num) ⟨21621, by rfl⟩ (by norm_num))
theorem R57661 : Reach 57661 := rs (se 3 (by rfl) ⟨10811, by rfl⟩) (B 21623 (by norm_num) ⟨10811, by rfl⟩ (by norm_num))
theorem R57665 : Reach 57665 := rs (se 2 (by rfl) ⟨21624, by rfl⟩) (B 43249 (by norm_num) ⟨21624, by rfl⟩ (by norm_num))
theorem R57669 : Reach 57669 := rs (se 4 (by rfl) ⟨5406, by rfl⟩) (B 10813 (by norm_num) ⟨5406, by rfl⟩ (by norm_num))
theorem R57673 : Reach 57673 := rs (se 2 (by rfl) ⟨21627, by rfl⟩) (B 43255 (by norm_num) ⟨21627, by rfl⟩ (by norm_num))
theorem R57677 : Reach 57677 := rs (se 3 (by rfl) ⟨10814, by rfl⟩) (B 21629 (by norm_num) ⟨10814, by rfl⟩ (by norm_num))
theorem R57681 : Reach 57681 := rs (se 2 (by rfl) ⟨21630, by rfl⟩) (B 43261 (by norm_num) ⟨21630, by rfl⟩ (by norm_num))
theorem R57685 : Reach 57685 := rs (se 10 (by rfl) ⟨84, by rfl⟩) (B 169 (by norm_num) ⟨84, by rfl⟩ (by norm_num))
theorem R221525 : Reach 221525 := rs (se 10 (by rfl) ⟨324, by rfl⟩) (B 649 (by norm_num) ⟨324, by rfl⟩ (by norm_num))
theorem R57689 : Reach 57689 := rs (se 2 (by rfl) ⟨21633, by rfl⟩) (B 43267 (by norm_num) ⟨21633, by rfl⟩ (by norm_num))
theorem R57693 : Reach 57693 := rs (se 3 (by rfl) ⟨10817, by rfl⟩) (B 21635 (by norm_num) ⟨10817, by rfl⟩ (by norm_num))
theorem R57697 : Reach 57697 := rs (se 2 (by rfl) ⟨21636, by rfl⟩) (B 43273 (by norm_num) ⟨21636, by rfl⟩ (by norm_num))
theorem R57701 : Reach 57701 := rs (se 4 (by rfl) ⟨5409, by rfl⟩) (B 10819 (by norm_num) ⟨5409, by rfl⟩ (by norm_num))
theorem R57705 : Reach 57705 := rs (se 2 (by rfl) ⟨21639, by rfl⟩) (B 43279 (by norm_num) ⟨21639, by rfl⟩ (by norm_num))
theorem R57709 : Reach 57709 := rs (se 3 (by rfl) ⟨10820, by rfl⟩) (B 21641 (by norm_num) ⟨10820, by rfl⟩ (by norm_num))
theorem R57713 : Reach 57713 := rs (se 2 (by rfl) ⟨21642, by rfl⟩) (B 43285 (by norm_num) ⟨21642, by rfl⟩ (by norm_num))
theorem R57717 : Reach 57717 := rs (se 5 (by rfl) ⟨2705, by rfl⟩) (B 5411 (by norm_num) ⟨2705, by rfl⟩ (by norm_num))
theorem R57721 : Reach 57721 := rs (se 2 (by rfl) ⟨21645, by rfl⟩) (B 43291 (by norm_num) ⟨21645, by rfl⟩ (by norm_num))
theorem R57725 : Reach 57725 := rs (se 3 (by rfl) ⟨10823, by rfl⟩) (B 21647 (by norm_num) ⟨10823, by rfl⟩ (by norm_num))
theorem R57729 : Reach 57729 := rs (se 2 (by rfl) ⟨21648, by rfl⟩) (B 43297 (by norm_num) ⟨21648, by rfl⟩ (by norm_num))
theorem R57733 : Reach 57733 := rs (se 4 (by rfl) ⟨5412, by rfl⟩) (B 10825 (by norm_num) ⟨5412, by rfl⟩ (by norm_num))
theorem R57737 : Reach 57737 := rs (se 2 (by rfl) ⟨21651, by rfl⟩) (B 43303 (by norm_num) ⟨21651, by rfl⟩ (by norm_num))
theorem R57741 : Reach 57741 := rs (se 3 (by rfl) ⟨10826, by rfl⟩) (B 21653 (by norm_num) ⟨10826, by rfl⟩ (by norm_num))
theorem R57745 : Reach 57745 := rs (se 2 (by rfl) ⟨21654, by rfl⟩) (B 43309 (by norm_num) ⟨21654, by rfl⟩ (by norm_num))
theorem R57749 : Reach 57749 := rs (se 6 (by rfl) ⟨1353, by rfl⟩) (B 2707 (by norm_num) ⟨1353, by rfl⟩ (by norm_num))
theorem R57753 : Reach 57753 := rs (se 2 (by rfl) ⟨21657, by rfl⟩) (B 43315 (by norm_num) ⟨21657, by rfl⟩ (by norm_num))
theorem R57757 : Reach 57757 := rs (se 3 (by rfl) ⟨10829, by rfl⟩) (B 21659 (by norm_num) ⟨10829, by rfl⟩ (by norm_num))
theorem R57761 : Reach 57761 := rs (se 2 (by rfl) ⟨21660, by rfl⟩) (B 43321 (by norm_num) ⟨21660, by rfl⟩ (by norm_num))
theorem R188837 : Reach 188837 := rs (se 4 (by rfl) ⟨17703, by rfl⟩) (B 35407 (by norm_num) ⟨17703, by rfl⟩ (by norm_num))
theorem R57765 : Reach 57765 := rs (se 4 (by rfl) ⟨5415, by rfl⟩) (B 10831 (by norm_num) ⟨5415, by rfl⟩ (by norm_num))
theorem R57769 : Reach 57769 := rs (se 2 (by rfl) ⟨21663, by rfl⟩) (B 43327 (by norm_num) ⟨21663, by rfl⟩ (by norm_num))
theorem R57773 : Reach 57773 := rs (se 3 (by rfl) ⟨10832, by rfl⟩) (B 21665 (by norm_num) ⟨10832, by rfl⟩ (by norm_num))
theorem R57777 : Reach 57777 := rs (se 2 (by rfl) ⟨21666, by rfl⟩) (B 43333 (by norm_num) ⟨21666, by rfl⟩ (by norm_num))
theorem R57781 : Reach 57781 := rs (se 5 (by rfl) ⟨2708, by rfl⟩) (B 5417 (by norm_num) ⟨2708, by rfl⟩ (by norm_num))
theorem R57785 : Reach 57785 := rs (se 2 (by rfl) ⟨21669, by rfl⟩) (B 43339 (by norm_num) ⟨21669, by rfl⟩ (by norm_num))
theorem R57789 : Reach 57789 := rs (se 3 (by rfl) ⟨10835, by rfl⟩) (B 21671 (by norm_num) ⟨10835, by rfl⟩ (by norm_num))
theorem R57793 : Reach 57793 := rs (se 2 (by rfl) ⟨21672, by rfl⟩) (B 43345 (by norm_num) ⟨21672, by rfl⟩ (by norm_num))
theorem R57797 : Reach 57797 := rs (se 4 (by rfl) ⟨5418, by rfl⟩) (B 10837 (by norm_num) ⟨5418, by rfl⟩ (by norm_num))
theorem R57801 : Reach 57801 := rs (se 2 (by rfl) ⟨21675, by rfl⟩) (B 43351 (by norm_num) ⟨21675, by rfl⟩ (by norm_num))
theorem R57805 : Reach 57805 := rs (se 3 (by rfl) ⟨10838, by rfl⟩) (B 21677 (by norm_num) ⟨10838, by rfl⟩ (by norm_num))
theorem R57809 : Reach 57809 := rs (se 2 (by rfl) ⟨21678, by rfl⟩) (B 43357 (by norm_num) ⟨21678, by rfl⟩ (by norm_num))
theorem R57813 : Reach 57813 := rs (se 7 (by rfl) ⟨677, by rfl⟩) (B 1355 (by norm_num) ⟨677, by rfl⟩ (by norm_num))
theorem R57817 : Reach 57817 := rs (se 2 (by rfl) ⟨21681, by rfl⟩) (B 43363 (by norm_num) ⟨21681, by rfl⟩ (by norm_num))
theorem R57821 : Reach 57821 := rs (se 3 (by rfl) ⟨10841, by rfl⟩) (B 21683 (by norm_num) ⟨10841, by rfl⟩ (by norm_num))
theorem R57825 : Reach 57825 := rs (se 2 (by rfl) ⟨21684, by rfl⟩) (B 43369 (by norm_num) ⟨21684, by rfl⟩ (by norm_num))
theorem R57829 : Reach 57829 := rs (se 4 (by rfl) ⟨5421, by rfl⟩) (B 10843 (by norm_num) ⟨5421, by rfl⟩ (by norm_num))
theorem R57833 : Reach 57833 := rs (se 2 (by rfl) ⟨21687, by rfl⟩) (B 43375 (by norm_num) ⟨21687, by rfl⟩ (by norm_num))
theorem R57837 : Reach 57837 := rs (se 3 (by rfl) ⟨10844, by rfl⟩) (B 21689 (by norm_num) ⟨10844, by rfl⟩ (by norm_num))
theorem R57841 : Reach 57841 := rs (se 2 (by rfl) ⟨21690, by rfl⟩) (B 43381 (by norm_num) ⟨21690, by rfl⟩ (by norm_num))
theorem R57845 : Reach 57845 := rs (se 5 (by rfl) ⟨2711, by rfl⟩) (B 5423 (by norm_num) ⟨2711, by rfl⟩ (by norm_num))
theorem R57849 : Reach 57849 := rs (se 2 (by rfl) ⟨21693, by rfl⟩) (B 43387 (by norm_num) ⟨21693, by rfl⟩ (by norm_num))
theorem R57853 : Reach 57853 := rs (se 3 (by rfl) ⟨10847, by rfl⟩) (B 21695 (by norm_num) ⟨10847, by rfl⟩ (by norm_num))
theorem R57857 : Reach 57857 := rs (se 2 (by rfl) ⟨21696, by rfl⟩) (B 43393 (by norm_num) ⟨21696, by rfl⟩ (by norm_num))
theorem R57861 : Reach 57861 := rs (se 4 (by rfl) ⟨5424, by rfl⟩) (B 10849 (by norm_num) ⟨5424, by rfl⟩ (by norm_num))
theorem R57865 : Reach 57865 := rs (se 2 (by rfl) ⟨21699, by rfl⟩) (B 43399 (by norm_num) ⟨21699, by rfl⟩ (by norm_num))
theorem R57869 : Reach 57869 := rs (se 3 (by rfl) ⟨10850, by rfl⟩) (B 21701 (by norm_num) ⟨10850, by rfl⟩ (by norm_num))
theorem R57873 : Reach 57873 := rs (se 2 (by rfl) ⟨21702, by rfl⟩) (B 43405 (by norm_num) ⟨21702, by rfl⟩ (by norm_num))
theorem R221717 : Reach 221717 := rs (se 6 (by rfl) ⟨5196, by rfl⟩) (B 10393 (by norm_num) ⟨5196, by rfl⟩ (by norm_num))
theorem R57877 : Reach 57877 := rs (se 6 (by rfl) ⟨1356, by rfl⟩) (B 2713 (by norm_num) ⟨1356, by rfl⟩ (by norm_num))
theorem R57881 : Reach 57881 := rs (se 2 (by rfl) ⟨21705, by rfl⟩) (B 43411 (by norm_num) ⟨21705, by rfl⟩ (by norm_num))
theorem R57885 : Reach 57885 := rs (se 3 (by rfl) ⟨10853, by rfl⟩) (B 21707 (by norm_num) ⟨10853, by rfl⟩ (by norm_num))
theorem R57889 : Reach 57889 := rs (se 2 (by rfl) ⟨21708, by rfl⟩) (B 43417 (by norm_num) ⟨21708, by rfl⟩ (by norm_num))
theorem R57893 : Reach 57893 := rs (se 4 (by rfl) ⟨5427, by rfl⟩) (B 10855 (by norm_num) ⟨5427, by rfl⟩ (by norm_num))
theorem R57897 : Reach 57897 := rs (se 2 (by rfl) ⟨21711, by rfl⟩) (B 43423 (by norm_num) ⟨21711, by rfl⟩ (by norm_num))
theorem R57901 : Reach 57901 := rs (se 3 (by rfl) ⟨10856, by rfl⟩) (B 21713 (by norm_num) ⟨10856, by rfl⟩ (by norm_num))
theorem R57905 : Reach 57905 := rs (se 2 (by rfl) ⟨21714, by rfl⟩) (B 43429 (by norm_num) ⟨21714, by rfl⟩ (by norm_num))
theorem R57909 : Reach 57909 := rs (se 5 (by rfl) ⟨2714, by rfl⟩) (B 5429 (by norm_num) ⟨2714, by rfl⟩ (by norm_num))
theorem R57913 : Reach 57913 := rs (se 2 (by rfl) ⟨21717, by rfl⟩) (B 43435 (by norm_num) ⟨21717, by rfl⟩ (by norm_num))
theorem R57917 : Reach 57917 := rs (se 3 (by rfl) ⟨10859, by rfl⟩) (B 21719 (by norm_num) ⟨10859, by rfl⟩ (by norm_num))
theorem R57921 : Reach 57921 := rs (se 2 (by rfl) ⟨21720, by rfl⟩) (B 43441 (by norm_num) ⟨21720, by rfl⟩ (by norm_num))
theorem R57925 : Reach 57925 := rs (se 4 (by rfl) ⟨5430, by rfl⟩) (B 10861 (by norm_num) ⟨5430, by rfl⟩ (by norm_num))
theorem R57929 : Reach 57929 := rs (se 2 (by rfl) ⟨21723, by rfl⟩) (B 43447 (by norm_num) ⟨21723, by rfl⟩ (by norm_num))
theorem R57933 : Reach 57933 := rs (se 3 (by rfl) ⟨10862, by rfl⟩) (B 21725 (by norm_num) ⟨10862, by rfl⟩ (by norm_num))
theorem R57937 : Reach 57937 := rs (se 2 (by rfl) ⟨21726, by rfl⟩) (B 43453 (by norm_num) ⟨21726, by rfl⟩ (by norm_num))
theorem R57941 : Reach 57941 := rs (se 8 (by rfl) ⟨339, by rfl⟩) (B 679 (by norm_num) ⟨339, by rfl⟩ (by norm_num))
theorem R57945 : Reach 57945 := rs (se 2 (by rfl) ⟨21729, by rfl⟩) (B 43459 (by norm_num) ⟨21729, by rfl⟩ (by norm_num))
theorem R57949 : Reach 57949 := rs (se 3 (by rfl) ⟨10865, by rfl⟩) (B 21731 (by norm_num) ⟨10865, by rfl⟩ (by norm_num))
theorem R57953 : Reach 57953 := rs (se 2 (by rfl) ⟨21732, by rfl⟩) (B 43465 (by norm_num) ⟨21732, by rfl⟩ (by norm_num))
theorem R57957 : Reach 57957 := rs (se 4 (by rfl) ⟨5433, by rfl⟩) (B 10867 (by norm_num) ⟨5433, by rfl⟩ (by norm_num))
theorem R57961 : Reach 57961 := rs (se 2 (by rfl) ⟨21735, by rfl⟩) (B 43471 (by norm_num) ⟨21735, by rfl⟩ (by norm_num))
theorem R57965 : Reach 57965 := rs (se 3 (by rfl) ⟨10868, by rfl⟩) (B 21737 (by norm_num) ⟨10868, by rfl⟩ (by norm_num))
theorem R57969 : Reach 57969 := rs (se 2 (by rfl) ⟨21738, by rfl⟩) (B 43477 (by norm_num) ⟨21738, by rfl⟩ (by norm_num))
theorem R57973 : Reach 57973 := rs (se 5 (by rfl) ⟨2717, by rfl⟩) (B 5435 (by norm_num) ⟨2717, by rfl⟩ (by norm_num))
theorem R57977 : Reach 57977 := rs (se 2 (by rfl) ⟨21741, by rfl⟩) (B 43483 (by norm_num) ⟨21741, by rfl⟩ (by norm_num))
theorem R57981 : Reach 57981 := rs (se 3 (by rfl) ⟨10871, by rfl⟩) (B 21743 (by norm_num) ⟨10871, by rfl⟩ (by norm_num))
theorem R57985 : Reach 57985 := rs (se 2 (by rfl) ⟨21744, by rfl⟩) (B 43489 (by norm_num) ⟨21744, by rfl⟩ (by norm_num))
theorem R57989 : Reach 57989 := rs (se 4 (by rfl) ⟨5436, by rfl⟩) (B 10873 (by norm_num) ⟨5436, by rfl⟩ (by norm_num))
theorem R57993 : Reach 57993 := rs (se 2 (by rfl) ⟨21747, by rfl⟩) (B 43495 (by norm_num) ⟨21747, by rfl⟩ (by norm_num))
theorem R57997 : Reach 57997 := rs (se 3 (by rfl) ⟨10874, by rfl⟩) (B 21749 (by norm_num) ⟨10874, by rfl⟩ (by norm_num))
theorem R58001 : Reach 58001 := rs (se 2 (by rfl) ⟨21750, by rfl⟩) (B 43501 (by norm_num) ⟨21750, by rfl⟩ (by norm_num))
theorem R58005 : Reach 58005 := rs (se 6 (by rfl) ⟨1359, by rfl⟩) (B 2719 (by norm_num) ⟨1359, by rfl⟩ (by norm_num))
theorem R58009 : Reach 58009 := rs (se 2 (by rfl) ⟨21753, by rfl⟩) (B 43507 (by norm_num) ⟨21753, by rfl⟩ (by norm_num))
theorem R58013 : Reach 58013 := rs (se 3 (by rfl) ⟨10877, by rfl⟩) (B 21755 (by norm_num) ⟨10877, by rfl⟩ (by norm_num))
theorem R58017 : Reach 58017 := rs (se 2 (by rfl) ⟨21756, by rfl⟩) (B 43513 (by norm_num) ⟨21756, by rfl⟩ (by norm_num))
theorem R156325 : Reach 156325 := rs (se 4 (by rfl) ⟨14655, by rfl⟩) (B 29311 (by norm_num) ⟨14655, by rfl⟩ (by norm_num))
theorem R58021 : Reach 58021 := rs (se 4 (by rfl) ⟨5439, by rfl⟩) (B 10879 (by norm_num) ⟨5439, by rfl⟩ (by norm_num))
theorem R58025 : Reach 58025 := rs (se 2 (by rfl) ⟨21759, by rfl⟩) (B 43519 (by norm_num) ⟨21759, by rfl⟩ (by norm_num))
theorem R58029 : Reach 58029 := rs (se 3 (by rfl) ⟨10880, by rfl⟩) (B 21761 (by norm_num) ⟨10880, by rfl⟩ (by norm_num))
theorem R58033 : Reach 58033 := rs (se 2 (by rfl) ⟨21762, by rfl⟩) (B 43525 (by norm_num) ⟨21762, by rfl⟩ (by norm_num))
theorem R58037 : Reach 58037 := rs (se 5 (by rfl) ⟨2720, by rfl⟩) (B 5441 (by norm_num) ⟨2720, by rfl⟩ (by norm_num))
theorem R58041 : Reach 58041 := rs (se 2 (by rfl) ⟨21765, by rfl⟩) (B 43531 (by norm_num) ⟨21765, by rfl⟩ (by norm_num))
theorem R58045 : Reach 58045 := rs (se 3 (by rfl) ⟨10883, by rfl⟩) (B 21767 (by norm_num) ⟨10883, by rfl⟩ (by norm_num))
theorem R58049 : Reach 58049 := rs (se 2 (by rfl) ⟨21768, by rfl⟩) (B 43537 (by norm_num) ⟨21768, by rfl⟩ (by norm_num))
theorem R123589 : Reach 123589 := rs (se 4 (by rfl) ⟨11586, by rfl⟩) (B 23173 (by norm_num) ⟨11586, by rfl⟩ (by norm_num))
theorem R58053 : Reach 58053 := rs (se 4 (by rfl) ⟨5442, by rfl⟩) (B 10885 (by norm_num) ⟨5442, by rfl⟩ (by norm_num))
theorem R58057 : Reach 58057 := rs (se 2 (by rfl) ⟨21771, by rfl⟩) (B 43543 (by norm_num) ⟨21771, by rfl⟩ (by norm_num))
theorem R90829 : Reach 90829 := rs (se 3 (by rfl) ⟨17030, by rfl⟩) (B 34061 (by norm_num) ⟨17030, by rfl⟩ (by norm_num))
theorem R58061 : Reach 58061 := rs (se 3 (by rfl) ⟨10886, by rfl⟩) (B 21773 (by norm_num) ⟨10886, by rfl⟩ (by norm_num))
theorem R58065 : Reach 58065 := rs (se 2 (by rfl) ⟨21774, by rfl⟩) (B 43549 (by norm_num) ⟨21774, by rfl⟩ (by norm_num))
theorem R320213 : Reach 320213 := rs (se 7 (by rfl) ⟨3752, by rfl⟩) (B 7505 (by norm_num) ⟨3752, by rfl⟩ (by norm_num))
theorem R58069 : Reach 58069 := rs (se 7 (by rfl) ⟨680, by rfl⟩) (B 1361 (by norm_num) ⟨680, by rfl⟩ (by norm_num))
theorem R58073 : Reach 58073 := rs (se 2 (by rfl) ⟨21777, by rfl⟩) (B 43555 (by norm_num) ⟨21777, by rfl⟩ (by norm_num))
theorem R58077 : Reach 58077 := rs (se 3 (by rfl) ⟨10889, by rfl⟩) (B 21779 (by norm_num) ⟨10889, by rfl⟩ (by norm_num))
theorem R58081 : Reach 58081 := rs (se 2 (by rfl) ⟨21780, by rfl⟩) (B 43561 (by norm_num) ⟨21780, by rfl⟩ (by norm_num))
theorem R58085 : Reach 58085 := rs (se 4 (by rfl) ⟨5445, by rfl⟩) (B 10891 (by norm_num) ⟨5445, by rfl⟩ (by norm_num))
theorem R58089 : Reach 58089 := rs (se 2 (by rfl) ⟨21783, by rfl⟩) (B 43567 (by norm_num) ⟨21783, by rfl⟩ (by norm_num))
theorem R58093 : Reach 58093 := rs (se 3 (by rfl) ⟨10892, by rfl⟩) (B 21785 (by norm_num) ⟨10892, by rfl⟩ (by norm_num))
theorem R58097 : Reach 58097 := rs (se 2 (by rfl) ⟨21786, by rfl⟩) (B 43573 (by norm_num) ⟨21786, by rfl⟩ (by norm_num))
theorem R58101 : Reach 58101 := rs (se 5 (by rfl) ⟨2723, by rfl⟩) (B 5447 (by norm_num) ⟨2723, by rfl⟩ (by norm_num))
theorem R58105 : Reach 58105 := rs (se 2 (by rfl) ⟨21789, by rfl⟩) (B 43579 (by norm_num) ⟨21789, by rfl⟩ (by norm_num))
theorem R58109 : Reach 58109 := rs (se 3 (by rfl) ⟨10895, by rfl⟩) (B 21791 (by norm_num) ⟨10895, by rfl⟩ (by norm_num))
theorem R58113 : Reach 58113 := rs (se 2 (by rfl) ⟨21792, by rfl⟩) (B 43585 (by norm_num) ⟨21792, by rfl⟩ (by norm_num))
theorem R58117 : Reach 58117 := rs (se 4 (by rfl) ⟨5448, by rfl⟩) (B 10897 (by norm_num) ⟨5448, by rfl⟩ (by norm_num))
theorem R58121 : Reach 58121 := rs (se 2 (by rfl) ⟨21795, by rfl⟩) (B 43591 (by norm_num) ⟨21795, by rfl⟩ (by norm_num))
theorem R58125 : Reach 58125 := rs (se 3 (by rfl) ⟨10898, by rfl⟩) (B 21797 (by norm_num) ⟨10898, by rfl⟩ (by norm_num))
theorem R58129 : Reach 58129 := rs (se 2 (by rfl) ⟨21798, by rfl⟩) (B 43597 (by norm_num) ⟨21798, by rfl⟩ (by norm_num))
theorem R58133 : Reach 58133 := rs (se 6 (by rfl) ⟨1362, by rfl⟩) (B 2725 (by norm_num) ⟨1362, by rfl⟩ (by norm_num))
theorem R58137 : Reach 58137 := rs (se 2 (by rfl) ⟨21801, by rfl⟩) (B 43603 (by norm_num) ⟨21801, by rfl⟩ (by norm_num))
theorem R58141 : Reach 58141 := rs (se 3 (by rfl) ⟨10901, by rfl⟩) (B 21803 (by norm_num) ⟨10901, by rfl⟩ (by norm_num))
theorem R58145 : Reach 58145 := rs (se 2 (by rfl) ⟨21804, by rfl⟩) (B 43609 (by norm_num) ⟨21804, by rfl⟩ (by norm_num))
theorem R58149 : Reach 58149 := rs (se 4 (by rfl) ⟨5451, by rfl⟩) (B 10903 (by norm_num) ⟨5451, by rfl⟩ (by norm_num))
theorem R58153 : Reach 58153 := rs (se 2 (by rfl) ⟨21807, by rfl⟩) (B 43615 (by norm_num) ⟨21807, by rfl⟩ (by norm_num))
theorem R58157 : Reach 58157 := rs (se 3 (by rfl) ⟨10904, by rfl⟩) (B 21809 (by norm_num) ⟨10904, by rfl⟩ (by norm_num))
theorem R58161 : Reach 58161 := rs (se 2 (by rfl) ⟨21810, by rfl⟩) (B 43621 (by norm_num) ⟨21810, by rfl⟩ (by norm_num))
theorem R58165 : Reach 58165 := rs (se 5 (by rfl) ⟨2726, by rfl⟩) (B 5453 (by norm_num) ⟨2726, by rfl⟩ (by norm_num))
theorem R58169 : Reach 58169 := rs (se 2 (by rfl) ⟨21813, by rfl⟩) (B 43627 (by norm_num) ⟨21813, by rfl⟩ (by norm_num))
theorem R58173 : Reach 58173 := rs (se 3 (by rfl) ⟨10907, by rfl⟩) (B 21815 (by norm_num) ⟨10907, by rfl⟩ (by norm_num))
theorem R58177 : Reach 58177 := rs (se 2 (by rfl) ⟨21816, by rfl⟩) (B 43633 (by norm_num) ⟨21816, by rfl⟩ (by norm_num))
theorem R58181 : Reach 58181 := rs (se 4 (by rfl) ⟨5454, by rfl⟩) (B 10909 (by norm_num) ⟨5454, by rfl⟩ (by norm_num))
theorem R58185 : Reach 58185 := rs (se 2 (by rfl) ⟨21819, by rfl⟩) (B 43639 (by norm_num) ⟨21819, by rfl⟩ (by norm_num))
theorem R58189 : Reach 58189 := rs (se 3 (by rfl) ⟨10910, by rfl⟩) (B 21821 (by norm_num) ⟨10910, by rfl⟩ (by norm_num))
theorem R58193 : Reach 58193 := rs (se 2 (by rfl) ⟨21822, by rfl⟩) (B 43645 (by norm_num) ⟨21822, by rfl⟩ (by norm_num))
theorem R189269 : Reach 189269 := rs (se 9 (by rfl) ⟨554, by rfl⟩) (B 1109 (by norm_num) ⟨554, by rfl⟩ (by norm_num))
theorem R58197 : Reach 58197 := rs (se 9 (by rfl) ⟨170, by rfl⟩) (B 341 (by norm_num) ⟨170, by rfl⟩ (by norm_num))
theorem R58201 : Reach 58201 := rs (se 2 (by rfl) ⟨21825, by rfl⟩) (B 43651 (by norm_num) ⟨21825, by rfl⟩ (by norm_num))
theorem R58205 : Reach 58205 := rs (se 3 (by rfl) ⟨10913, by rfl⟩) (B 21827 (by norm_num) ⟨10913, by rfl⟩ (by norm_num))
theorem R58209 : Reach 58209 := rs (se 2 (by rfl) ⟨21828, by rfl⟩) (B 43657 (by norm_num) ⟨21828, by rfl⟩ (by norm_num))
theorem R58213 : Reach 58213 := rs (se 4 (by rfl) ⟨5457, by rfl⟩) (B 10915 (by norm_num) ⟨5457, by rfl⟩ (by norm_num))
theorem R58217 : Reach 58217 := rs (se 2 (by rfl) ⟨21831, by rfl⟩) (B 43663 (by norm_num) ⟨21831, by rfl⟩ (by norm_num))
theorem R58221 : Reach 58221 := rs (se 3 (by rfl) ⟨10916, by rfl⟩) (B 21833 (by norm_num) ⟨10916, by rfl⟩ (by norm_num))
theorem R58225 : Reach 58225 := rs (se 2 (by rfl) ⟨21834, by rfl⟩) (B 43669 (by norm_num) ⟨21834, by rfl⟩ (by norm_num))
theorem R58229 : Reach 58229 := rs (se 5 (by rfl) ⟨2729, by rfl⟩) (B 5459 (by norm_num) ⟨2729, by rfl⟩ (by norm_num))
theorem R58233 : Reach 58233 := rs (se 2 (by rfl) ⟨21837, by rfl⟩) (B 43675 (by norm_num) ⟨21837, by rfl⟩ (by norm_num))
theorem R58237 : Reach 58237 := rs (se 3 (by rfl) ⟨10919, by rfl⟩) (B 21839 (by norm_num) ⟨10919, by rfl⟩ (by norm_num))
theorem R58241 : Reach 58241 := rs (se 2 (by rfl) ⟨21840, by rfl⟩) (B 43681 (by norm_num) ⟨21840, by rfl⟩ (by norm_num))
theorem R58245 : Reach 58245 := rs (se 4 (by rfl) ⟨5460, by rfl⟩) (B 10921 (by norm_num) ⟨5460, by rfl⟩ (by norm_num))
theorem R58249 : Reach 58249 := rs (se 2 (by rfl) ⟨21843, by rfl⟩) (B 43687 (by norm_num) ⟨21843, by rfl⟩ (by norm_num))
theorem R58253 : Reach 58253 := rs (se 3 (by rfl) ⟨10922, by rfl⟩) (B 21845 (by norm_num) ⟨10922, by rfl⟩ (by norm_num))
theorem R58257 : Reach 58257 := rs (se 2 (by rfl) ⟨21846, by rfl⟩) (B 43693 (by norm_num) ⟨21846, by rfl⟩ (by norm_num))
theorem R418709 : Reach 418709 := rs (se 6 (by rfl) ⟨9813, by rfl⟩) (B 19627 (by norm_num) ⟨9813, by rfl⟩ (by norm_num))
theorem R58261 : Reach 58261 := rs (se 6 (by rfl) ⟨1365, by rfl⟩) (B 2731 (by norm_num) ⟨1365, by rfl⟩ (by norm_num))
theorem R58265 : Reach 58265 := rs (se 2 (by rfl) ⟨21849, by rfl⟩) (B 43699 (by norm_num) ⟨21849, by rfl⟩ (by norm_num))
theorem R123805 : Reach 123805 := rs (se 3 (by rfl) ⟨23213, by rfl⟩) (B 46427 (by norm_num) ⟨23213, by rfl⟩ (by norm_num))
theorem R58269 : Reach 58269 := rs (se 3 (by rfl) ⟨10925, by rfl⟩) (B 21851 (by norm_num) ⟨10925, by rfl⟩ (by norm_num))
theorem R58273 : Reach 58273 := rs (se 2 (by rfl) ⟨21852, by rfl⟩) (B 43705 (by norm_num) ⟨21852, by rfl⟩ (by norm_num))
theorem R58277 : Reach 58277 := rs (se 4 (by rfl) ⟨5463, by rfl⟩) (B 10927 (by norm_num) ⟨5463, by rfl⟩ (by norm_num))
theorem R58281 : Reach 58281 := rs (se 2 (by rfl) ⟨21855, by rfl⟩) (B 43711 (by norm_num) ⟨21855, by rfl⟩ (by norm_num))
theorem R58285 : Reach 58285 := rs (se 3 (by rfl) ⟨10928, by rfl⟩) (B 21857 (by norm_num) ⟨10928, by rfl⟩ (by norm_num))
theorem R58289 : Reach 58289 := rs (se 2 (by rfl) ⟨21858, by rfl⟩) (B 43717 (by norm_num) ⟨21858, by rfl⟩ (by norm_num))
theorem R58293 : Reach 58293 := rs (se 5 (by rfl) ⟨2732, by rfl⟩) (B 5465 (by norm_num) ⟨2732, by rfl⟩ (by norm_num))
theorem R58297 : Reach 58297 := rs (se 2 (by rfl) ⟨21861, by rfl⟩) (B 43723 (by norm_num) ⟨21861, by rfl⟩ (by norm_num))
theorem R58301 : Reach 58301 := rs (se 3 (by rfl) ⟨10931, by rfl⟩) (B 21863 (by norm_num) ⟨10931, by rfl⟩ (by norm_num))
theorem R58305 : Reach 58305 := rs (se 2 (by rfl) ⟨21864, by rfl⟩) (B 43729 (by norm_num) ⟨21864, by rfl⟩ (by norm_num))
theorem R58309 : Reach 58309 := rs (se 4 (by rfl) ⟨5466, by rfl⟩) (B 10933 (by norm_num) ⟨5466, by rfl⟩ (by norm_num))
theorem R58313 : Reach 58313 := rs (se 2 (by rfl) ⟨21867, by rfl⟩) (B 43735 (by norm_num) ⟨21867, by rfl⟩ (by norm_num))
theorem R58317 : Reach 58317 := rs (se 3 (by rfl) ⟨10934, by rfl⟩) (B 21869 (by norm_num) ⟨10934, by rfl⟩ (by norm_num))
theorem R58321 : Reach 58321 := rs (se 2 (by rfl) ⟨21870, by rfl⟩) (B 43741 (by norm_num) ⟨21870, by rfl⟩ (by norm_num))
theorem R58325 : Reach 58325 := rs (se 7 (by rfl) ⟨683, by rfl⟩) (B 1367 (by norm_num) ⟨683, by rfl⟩ (by norm_num))
theorem R58329 : Reach 58329 := rs (se 2 (by rfl) ⟨21873, by rfl⟩) (B 43747 (by norm_num) ⟨21873, by rfl⟩ (by norm_num))
theorem R58333 : Reach 58333 := rs (se 3 (by rfl) ⟨10937, by rfl⟩) (B 21875 (by norm_num) ⟨10937, by rfl⟩ (by norm_num))
theorem R58337 : Reach 58337 := rs (se 2 (by rfl) ⟨21876, by rfl⟩) (B 43753 (by norm_num) ⟨21876, by rfl⟩ (by norm_num))
theorem R58341 : Reach 58341 := rs (se 4 (by rfl) ⟨5469, by rfl⟩) (B 10939 (by norm_num) ⟨5469, by rfl⟩ (by norm_num))
theorem R58345 : Reach 58345 := rs (se 2 (by rfl) ⟨21879, by rfl⟩) (B 43759 (by norm_num) ⟨21879, by rfl⟩ (by norm_num))
theorem R58349 : Reach 58349 := rs (se 3 (by rfl) ⟨10940, by rfl⟩) (B 21881 (by norm_num) ⟨10940, by rfl⟩ (by norm_num))
theorem R58353 : Reach 58353 := rs (se 2 (by rfl) ⟨21882, by rfl⟩) (B 43765 (by norm_num) ⟨21882, by rfl⟩ (by norm_num))
theorem R58357 : Reach 58357 := rs (se 5 (by rfl) ⟨2735, by rfl⟩) (B 5471 (by norm_num) ⟨2735, by rfl⟩ (by norm_num))
theorem R58361 : Reach 58361 := rs (se 2 (by rfl) ⟨21885, by rfl⟩) (B 43771 (by norm_num) ⟨21885, by rfl⟩ (by norm_num))
theorem R58365 : Reach 58365 := rs (se 3 (by rfl) ⟨10943, by rfl⟩) (B 21887 (by norm_num) ⟨10943, by rfl⟩ (by norm_num))
theorem R58369 : Reach 58369 := rs (se 2 (by rfl) ⟨21888, by rfl⟩) (B 43777 (by norm_num) ⟨21888, by rfl⟩ (by norm_num))
theorem R58373 : Reach 58373 := rs (se 4 (by rfl) ⟨5472, by rfl⟩) (B 10945 (by norm_num) ⟨5472, by rfl⟩ (by norm_num))
theorem R58377 : Reach 58377 := rs (se 2 (by rfl) ⟨21891, by rfl⟩) (B 43783 (by norm_num) ⟨21891, by rfl⟩ (by norm_num))
theorem R58381 : Reach 58381 := rs (se 3 (by rfl) ⟨10946, by rfl⟩) (B 21893 (by norm_num) ⟨10946, by rfl⟩ (by norm_num))
theorem R58385 : Reach 58385 := rs (se 2 (by rfl) ⟨21894, by rfl⟩) (B 43789 (by norm_num) ⟨21894, by rfl⟩ (by norm_num))
theorem R123925 : Reach 123925 := rs (se 6 (by rfl) ⟨2904, by rfl⟩) (B 5809 (by norm_num) ⟨2904, by rfl⟩ (by norm_num))
theorem R58389 : Reach 58389 := rs (se 6 (by rfl) ⟨1368, by rfl⟩) (B 2737 (by norm_num) ⟨1368, by rfl⟩ (by norm_num))
theorem R58393 : Reach 58393 := rs (se 2 (by rfl) ⟨21897, by rfl⟩) (B 43795 (by norm_num) ⟨21897, by rfl⟩ (by norm_num))
theorem R58397 : Reach 58397 := rs (se 3 (by rfl) ⟨10949, by rfl⟩) (B 21899 (by norm_num) ⟨10949, by rfl⟩ (by norm_num))
theorem R58401 : Reach 58401 := rs (se 2 (by rfl) ⟨21900, by rfl⟩) (B 43801 (by norm_num) ⟨21900, by rfl⟩ (by norm_num))
theorem R58405 : Reach 58405 := rs (se 4 (by rfl) ⟨5475, by rfl⟩) (B 10951 (by norm_num) ⟨5475, by rfl⟩ (by norm_num))
theorem R58409 : Reach 58409 := rs (se 2 (by rfl) ⟨21903, by rfl⟩) (B 43807 (by norm_num) ⟨21903, by rfl⟩ (by norm_num))
theorem R58413 : Reach 58413 := rs (se 3 (by rfl) ⟨10952, by rfl⟩) (B 21905 (by norm_num) ⟨10952, by rfl⟩ (by norm_num))
theorem R58417 : Reach 58417 := rs (se 2 (by rfl) ⟨21906, by rfl⟩) (B 43813 (by norm_num) ⟨21906, by rfl⟩ (by norm_num))
theorem R58421 : Reach 58421 := rs (se 5 (by rfl) ⟨2738, by rfl⟩) (B 5477 (by norm_num) ⟨2738, by rfl⟩ (by norm_num))
theorem R58425 : Reach 58425 := rs (se 2 (by rfl) ⟨21909, by rfl⟩) (B 43819 (by norm_num) ⟨21909, by rfl⟩ (by norm_num))
theorem R58429 : Reach 58429 := rs (se 3 (by rfl) ⟨10955, by rfl⟩) (B 21911 (by norm_num) ⟨10955, by rfl⟩ (by norm_num))
theorem R58433 : Reach 58433 := rs (se 2 (by rfl) ⟨21912, by rfl⟩) (B 43825 (by norm_num) ⟨21912, by rfl⟩ (by norm_num))
theorem R58437 : Reach 58437 := rs (se 4 (by rfl) ⟨5478, by rfl⟩) (B 10957 (by norm_num) ⟨5478, by rfl⟩ (by norm_num))
theorem R58441 : Reach 58441 := rs (se 2 (by rfl) ⟨21915, by rfl⟩) (B 43831 (by norm_num) ⟨21915, by rfl⟩ (by norm_num))
theorem R58445 : Reach 58445 := rs (se 3 (by rfl) ⟨10958, by rfl⟩) (B 21917 (by norm_num) ⟨10958, by rfl⟩ (by norm_num))
theorem R58449 : Reach 58449 := rs (se 2 (by rfl) ⟨21918, by rfl⟩) (B 43837 (by norm_num) ⟨21918, by rfl⟩ (by norm_num))
theorem R58453 : Reach 58453 := rs (se 8 (by rfl) ⟨342, by rfl⟩) (B 685 (by norm_num) ⟨342, by rfl⟩ (by norm_num))
theorem R58457 : Reach 58457 := rs (se 2 (by rfl) ⟨21921, by rfl⟩) (B 43843 (by norm_num) ⟨21921, by rfl⟩ (by norm_num))
theorem R58461 : Reach 58461 := rs (se 3 (by rfl) ⟨10961, by rfl⟩) (B 21923 (by norm_num) ⟨10961, by rfl⟩ (by norm_num))
theorem R58465 : Reach 58465 := rs (se 2 (by rfl) ⟨21924, by rfl⟩) (B 43849 (by norm_num) ⟨21924, by rfl⟩ (by norm_num))
theorem R58469 : Reach 58469 := rs (se 4 (by rfl) ⟨5481, by rfl⟩) (B 10963 (by norm_num) ⟨5481, by rfl⟩ (by norm_num))
theorem R58473 : Reach 58473 := rs (se 2 (by rfl) ⟨21927, by rfl⟩) (B 43855 (by norm_num) ⟨21927, by rfl⟩ (by norm_num))
theorem R58477 : Reach 58477 := rs (se 3 (by rfl) ⟨10964, by rfl⟩) (B 21929 (by norm_num) ⟨10964, by rfl⟩ (by norm_num))
theorem R58481 : Reach 58481 := rs (se 2 (by rfl) ⟨21930, by rfl⟩) (B 43861 (by norm_num) ⟨21930, by rfl⟩ (by norm_num))
theorem R58485 : Reach 58485 := rs (se 5 (by rfl) ⟨2741, by rfl⟩) (B 5483 (by norm_num) ⟨2741, by rfl⟩ (by norm_num))
theorem R58489 : Reach 58489 := rs (se 2 (by rfl) ⟨21933, by rfl⟩) (B 43867 (by norm_num) ⟨21933, by rfl⟩ (by norm_num))
theorem R58493 : Reach 58493 := rs (se 3 (by rfl) ⟨10967, by rfl⟩) (B 21935 (by norm_num) ⟨10967, by rfl⟩ (by norm_num))
theorem R58497 : Reach 58497 := rs (se 2 (by rfl) ⟨21936, by rfl⟩) (B 43873 (by norm_num) ⟨21936, by rfl⟩ (by norm_num))
theorem R124037 : Reach 124037 := rs (se 4 (by rfl) ⟨11628, by rfl⟩) (B 23257 (by norm_num) ⟨11628, by rfl⟩ (by norm_num))
theorem R58501 : Reach 58501 := rs (se 4 (by rfl) ⟨5484, by rfl⟩) (B 10969 (by norm_num) ⟨5484, by rfl⟩ (by norm_num))
theorem R58505 : Reach 58505 := rs (se 2 (by rfl) ⟨21939, by rfl⟩) (B 43879 (by norm_num) ⟨21939, by rfl⟩ (by norm_num))
theorem R58509 : Reach 58509 := rs (se 3 (by rfl) ⟨10970, by rfl⟩) (B 21941 (by norm_num) ⟨10970, by rfl⟩ (by norm_num))
theorem R58513 : Reach 58513 := rs (se 2 (by rfl) ⟨21942, by rfl⟩) (B 43885 (by norm_num) ⟨21942, by rfl⟩ (by norm_num))
theorem R58517 : Reach 58517 := rs (se 6 (by rfl) ⟨1371, by rfl⟩) (B 2743 (by norm_num) ⟨1371, by rfl⟩ (by norm_num))
theorem R58521 : Reach 58521 := rs (se 2 (by rfl) ⟨21945, by rfl⟩) (B 43891 (by norm_num) ⟨21945, by rfl⟩ (by norm_num))
theorem R58525 : Reach 58525 := rs (se 3 (by rfl) ⟨10973, by rfl⟩) (B 21947 (by norm_num) ⟨10973, by rfl⟩ (by norm_num))
theorem R58529 : Reach 58529 := rs (se 2 (by rfl) ⟨21948, by rfl⟩) (B 43897 (by norm_num) ⟨21948, by rfl⟩ (by norm_num))
theorem R58533 : Reach 58533 := rs (se 4 (by rfl) ⟨5487, by rfl⟩) (B 10975 (by norm_num) ⟨5487, by rfl⟩ (by norm_num))
theorem R58537 : Reach 58537 := rs (se 2 (by rfl) ⟨21951, by rfl⟩) (B 43903 (by norm_num) ⟨21951, by rfl⟩ (by norm_num))
theorem R58541 : Reach 58541 := rs (se 3 (by rfl) ⟨10976, by rfl⟩) (B 21953 (by norm_num) ⟨10976, by rfl⟩ (by norm_num))
theorem R58545 : Reach 58545 := rs (se 2 (by rfl) ⟨21954, by rfl⟩) (B 43909 (by norm_num) ⟨21954, by rfl⟩ (by norm_num))
theorem R58549 : Reach 58549 := rs (se 5 (by rfl) ⟨2744, by rfl⟩) (B 5489 (by norm_num) ⟨2744, by rfl⟩ (by norm_num))
theorem R58553 : Reach 58553 := rs (se 2 (by rfl) ⟨21957, by rfl⟩) (B 43915 (by norm_num) ⟨21957, by rfl⟩ (by norm_num))
theorem R58557 : Reach 58557 := rs (se 3 (by rfl) ⟨10979, by rfl⟩) (B 21959 (by norm_num) ⟨10979, by rfl⟩ (by norm_num))
theorem R58561 : Reach 58561 := rs (se 2 (by rfl) ⟨21960, by rfl⟩) (B 43921 (by norm_num) ⟨21960, by rfl⟩ (by norm_num))
theorem R58565 : Reach 58565 := rs (se 4 (by rfl) ⟨5490, by rfl⟩) (B 10981 (by norm_num) ⟨5490, by rfl⟩ (by norm_num))
theorem R58569 : Reach 58569 := rs (se 2 (by rfl) ⟨21963, by rfl⟩) (B 43927 (by norm_num) ⟨21963, by rfl⟩ (by norm_num))
theorem R124109 : Reach 124109 := rs (se 3 (by rfl) ⟨23270, by rfl⟩) (B 46541 (by norm_num) ⟨23270, by rfl⟩ (by norm_num))
theorem R58573 : Reach 58573 := rs (se 3 (by rfl) ⟨10982, by rfl⟩) (B 21965 (by norm_num) ⟨10982, by rfl⟩ (by norm_num))
theorem R58577 : Reach 58577 := rs (se 2 (by rfl) ⟨21966, by rfl⟩) (B 43933 (by norm_num) ⟨21966, by rfl⟩ (by norm_num))
theorem R58581 : Reach 58581 := rs (se 7 (by rfl) ⟨686, by rfl⟩) (B 1373 (by norm_num) ⟨686, by rfl⟩ (by norm_num))
theorem R58585 : Reach 58585 := rs (se 2 (by rfl) ⟨21969, by rfl⟩) (B 43939 (by norm_num) ⟨21969, by rfl⟩ (by norm_num))
theorem R58589 : Reach 58589 := rs (se 3 (by rfl) ⟨10985, by rfl⟩) (B 21971 (by norm_num) ⟨10985, by rfl⟩ (by norm_num))
theorem R58593 : Reach 58593 := rs (se 2 (by rfl) ⟨21972, by rfl⟩) (B 43945 (by norm_num) ⟨21972, by rfl⟩ (by norm_num))
theorem R58597 : Reach 58597 := rs (se 4 (by rfl) ⟨5493, by rfl⟩) (B 10987 (by norm_num) ⟨5493, by rfl⟩ (by norm_num))
theorem R58601 : Reach 58601 := rs (se 2 (by rfl) ⟨21975, by rfl⟩) (B 43951 (by norm_num) ⟨21975, by rfl⟩ (by norm_num))
theorem R58605 : Reach 58605 := rs (se 3 (by rfl) ⟨10988, by rfl⟩) (B 21977 (by norm_num) ⟨10988, by rfl⟩ (by norm_num))
theorem R58609 : Reach 58609 := rs (se 2 (by rfl) ⟨21978, by rfl⟩) (B 43957 (by norm_num) ⟨21978, by rfl⟩ (by norm_num))
theorem R58613 : Reach 58613 := rs (se 5 (by rfl) ⟨2747, by rfl⟩) (B 5495 (by norm_num) ⟨2747, by rfl⟩ (by norm_num))
theorem R58617 : Reach 58617 := rs (se 2 (by rfl) ⟨21981, by rfl⟩) (B 43963 (by norm_num) ⟨21981, by rfl⟩ (by norm_num))
theorem R58621 : Reach 58621 := rs (se 3 (by rfl) ⟨10991, by rfl⟩) (B 21983 (by norm_num) ⟨10991, by rfl⟩ (by norm_num))
theorem R58625 : Reach 58625 := rs (se 2 (by rfl) ⟨21984, by rfl⟩) (B 43969 (by norm_num) ⟨21984, by rfl⟩ (by norm_num))
theorem R189701 : Reach 189701 := rs (se 4 (by rfl) ⟨17784, by rfl⟩) (B 35569 (by norm_num) ⟨17784, by rfl⟩ (by norm_num))
theorem R58629 : Reach 58629 := rs (se 4 (by rfl) ⟨5496, by rfl⟩) (B 10993 (by norm_num) ⟨5496, by rfl⟩ (by norm_num))
theorem R58633 : Reach 58633 := rs (se 2 (by rfl) ⟨21987, by rfl⟩) (B 43975 (by norm_num) ⟨21987, by rfl⟩ (by norm_num))
theorem R58637 : Reach 58637 := rs (se 3 (by rfl) ⟨10994, by rfl⟩) (B 21989 (by norm_num) ⟨10994, by rfl⟩ (by norm_num))
theorem R58641 : Reach 58641 := rs (se 2 (by rfl) ⟨21990, by rfl⟩) (B 43981 (by norm_num) ⟨21990, by rfl⟩ (by norm_num))
theorem R124181 : Reach 124181 := rs (se 6 (by rfl) ⟨2910, by rfl⟩) (B 5821 (by norm_num) ⟨2910, by rfl⟩ (by norm_num))
theorem R58645 : Reach 58645 := rs (se 6 (by rfl) ⟨1374, by rfl⟩) (B 2749 (by norm_num) ⟨1374, by rfl⟩ (by norm_num))
theorem R58649 : Reach 58649 := rs (se 2 (by rfl) ⟨21993, by rfl⟩) (B 43987 (by norm_num) ⟨21993, by rfl⟩ (by norm_num))
theorem R58653 : Reach 58653 := rs (se 3 (by rfl) ⟨10997, by rfl⟩) (B 21995 (by norm_num) ⟨10997, by rfl⟩ (by norm_num))
theorem R58657 : Reach 58657 := rs (se 2 (by rfl) ⟨21996, by rfl⟩) (B 43993 (by norm_num) ⟨21996, by rfl⟩ (by norm_num))
theorem R58661 : Reach 58661 := rs (se 4 (by rfl) ⟨5499, by rfl⟩) (B 10999 (by norm_num) ⟨5499, by rfl⟩ (by norm_num))
theorem R58665 : Reach 58665 := rs (se 2 (by rfl) ⟨21999, by rfl⟩) (B 43999 (by norm_num) ⟨21999, by rfl⟩ (by norm_num))
theorem R58669 : Reach 58669 := rs (se 3 (by rfl) ⟨11000, by rfl⟩) (B 22001 (by norm_num) ⟨11000, by rfl⟩ (by norm_num))
theorem R58673 : Reach 58673 := rs (se 2 (by rfl) ⟨22002, by rfl⟩) (B 44005 (by norm_num) ⟨22002, by rfl⟩ (by norm_num))
theorem R58677 : Reach 58677 := rs (se 5 (by rfl) ⟨2750, by rfl⟩) (B 5501 (by norm_num) ⟨2750, by rfl⟩ (by norm_num))
theorem R58681 : Reach 58681 := rs (se 2 (by rfl) ⟨22005, by rfl⟩) (B 44011 (by norm_num) ⟨22005, by rfl⟩ (by norm_num))
theorem R58685 : Reach 58685 := rs (se 3 (by rfl) ⟨11003, by rfl⟩) (B 22007 (by norm_num) ⟨11003, by rfl⟩ (by norm_num))
theorem R58689 : Reach 58689 := rs (se 2 (by rfl) ⟨22008, by rfl⟩) (B 44017 (by norm_num) ⟨22008, by rfl⟩ (by norm_num))
theorem R58693 : Reach 58693 := rs (se 4 (by rfl) ⟨5502, by rfl⟩) (B 11005 (by norm_num) ⟨5502, by rfl⟩ (by norm_num))
theorem R58697 : Reach 58697 := rs (se 2 (by rfl) ⟨22011, by rfl⟩) (B 44023 (by norm_num) ⟨22011, by rfl⟩ (by norm_num))
theorem R58701 : Reach 58701 := rs (se 3 (by rfl) ⟨11006, by rfl⟩) (B 22013 (by norm_num) ⟨11006, by rfl⟩ (by norm_num))
theorem R58705 : Reach 58705 := rs (se 2 (by rfl) ⟨22014, by rfl⟩) (B 44029 (by norm_num) ⟨22014, by rfl⟩ (by norm_num))
theorem R58709 : Reach 58709 := rs (se 12 (by rfl) ⟨21, by rfl⟩) (B 43 (by norm_num) ⟨21, by rfl⟩ (by norm_num))
theorem R58713 : Reach 58713 := rs (se 2 (by rfl) ⟨22017, by rfl⟩) (B 44035 (by norm_num) ⟨22017, by rfl⟩ (by norm_num))
theorem R124253 : Reach 124253 := rs (se 3 (by rfl) ⟨23297, by rfl⟩) (B 46595 (by norm_num) ⟨23297, by rfl⟩ (by norm_num))
theorem R58717 : Reach 58717 := rs (se 3 (by rfl) ⟨11009, by rfl⟩) (B 22019 (by norm_num) ⟨11009, by rfl⟩ (by norm_num))
theorem R58721 : Reach 58721 := rs (se 2 (by rfl) ⟨22020, by rfl⟩) (B 44041 (by norm_num) ⟨22020, by rfl⟩ (by norm_num))
theorem R58725 : Reach 58725 := rs (se 4 (by rfl) ⟨5505, by rfl⟩) (B 11011 (by norm_num) ⟨5505, by rfl⟩ (by norm_num))
theorem R58729 : Reach 58729 := rs (se 2 (by rfl) ⟨22023, by rfl⟩) (B 44047 (by norm_num) ⟨22023, by rfl⟩ (by norm_num))
theorem R58733 : Reach 58733 := rs (se 3 (by rfl) ⟨11012, by rfl⟩) (B 22025 (by norm_num) ⟨11012, by rfl⟩ (by norm_num))
theorem R58737 : Reach 58737 := rs (se 2 (by rfl) ⟨22026, by rfl⟩) (B 44053 (by norm_num) ⟨22026, by rfl⟩ (by norm_num))
theorem R58741 : Reach 58741 := rs (se 5 (by rfl) ⟨2753, by rfl⟩) (B 5507 (by norm_num) ⟨2753, by rfl⟩ (by norm_num))
theorem R58745 : Reach 58745 := rs (se 2 (by rfl) ⟨22029, by rfl⟩) (B 44059 (by norm_num) ⟨22029, by rfl⟩ (by norm_num))
theorem R58749 : Reach 58749 := rs (se 3 (by rfl) ⟨11015, by rfl⟩) (B 22031 (by norm_num) ⟨11015, by rfl⟩ (by norm_num))
theorem R58753 : Reach 58753 := rs (se 2 (by rfl) ⟨22032, by rfl⟩) (B 44065 (by norm_num) ⟨22032, by rfl⟩ (by norm_num))
theorem R58757 : Reach 58757 := rs (se 4 (by rfl) ⟨5508, by rfl⟩) (B 11017 (by norm_num) ⟨5508, by rfl⟩ (by norm_num))
theorem R58761 : Reach 58761 := rs (se 2 (by rfl) ⟨22035, by rfl⟩) (B 44071 (by norm_num) ⟨22035, by rfl⟩ (by norm_num))
theorem R58765 : Reach 58765 := rs (se 3 (by rfl) ⟨11018, by rfl⟩) (B 22037 (by norm_num) ⟨11018, by rfl⟩ (by norm_num))
theorem R58769 : Reach 58769 := rs (se 2 (by rfl) ⟨22038, by rfl⟩) (B 44077 (by norm_num) ⟨22038, by rfl⟩ (by norm_num))
theorem R58773 : Reach 58773 := rs (se 6 (by rfl) ⟨1377, by rfl⟩) (B 2755 (by norm_num) ⟨1377, by rfl⟩ (by norm_num))
theorem R58777 : Reach 58777 := rs (se 2 (by rfl) ⟨22041, by rfl⟩) (B 44083 (by norm_num) ⟨22041, by rfl⟩ (by norm_num))
theorem R58781 : Reach 58781 := rs (se 3 (by rfl) ⟨11021, by rfl⟩) (B 22043 (by norm_num) ⟨11021, by rfl⟩ (by norm_num))
theorem R58785 : Reach 58785 := rs (se 2 (by rfl) ⟨22044, by rfl⟩) (B 44089 (by norm_num) ⟨22044, by rfl⟩ (by norm_num))
theorem R124325 : Reach 124325 := rs (se 4 (by rfl) ⟨11655, by rfl⟩) (B 23311 (by norm_num) ⟨11655, by rfl⟩ (by norm_num))
theorem R58789 : Reach 58789 := rs (se 4 (by rfl) ⟨5511, by rfl⟩) (B 11023 (by norm_num) ⟨5511, by rfl⟩ (by norm_num))
theorem R58793 : Reach 58793 := rs (se 2 (by rfl) ⟨22047, by rfl⟩) (B 44095 (by norm_num) ⟨22047, by rfl⟩ (by norm_num))
theorem R58797 : Reach 58797 := rs (se 3 (by rfl) ⟨11024, by rfl⟩) (B 22049 (by norm_num) ⟨11024, by rfl⟩ (by norm_num))
theorem R58801 : Reach 58801 := rs (se 2 (by rfl) ⟨22050, by rfl⟩) (B 44101 (by norm_num) ⟨22050, by rfl⟩ (by norm_num))
theorem R58805 : Reach 58805 := rs (se 5 (by rfl) ⟨2756, by rfl⟩) (B 5513 (by norm_num) ⟨2756, by rfl⟩ (by norm_num))
theorem R58809 : Reach 58809 := rs (se 2 (by rfl) ⟨22053, by rfl⟩) (B 44107 (by norm_num) ⟨22053, by rfl⟩ (by norm_num))
theorem R58813 : Reach 58813 := rs (se 3 (by rfl) ⟨11027, by rfl⟩) (B 22055 (by norm_num) ⟨11027, by rfl⟩ (by norm_num))
theorem R58817 : Reach 58817 := rs (se 2 (by rfl) ⟨22056, by rfl⟩) (B 44113 (by norm_num) ⟨22056, by rfl⟩ (by norm_num))
theorem R288197 : Reach 288197 := rs (se 4 (by rfl) ⟨27018, by rfl⟩) (B 54037 (by norm_num) ⟨27018, by rfl⟩ (by norm_num))
theorem R58821 : Reach 58821 := rs (se 4 (by rfl) ⟨5514, by rfl⟩) (B 11029 (by norm_num) ⟨5514, by rfl⟩ (by norm_num))
theorem R58825 : Reach 58825 := rs (se 2 (by rfl) ⟨22059, by rfl⟩) (B 44119 (by norm_num) ⟨22059, by rfl⟩ (by norm_num))
theorem R58829 : Reach 58829 := rs (se 3 (by rfl) ⟨11030, by rfl⟩) (B 22061 (by norm_num) ⟨11030, by rfl⟩ (by norm_num))
theorem R58833 : Reach 58833 := rs (se 2 (by rfl) ⟨22062, by rfl⟩) (B 44125 (by norm_num) ⟨22062, by rfl⟩ (by norm_num))
theorem R58837 : Reach 58837 := rs (se 7 (by rfl) ⟨689, by rfl⟩) (B 1379 (by norm_num) ⟨689, by rfl⟩ (by norm_num))
theorem R58841 : Reach 58841 := rs (se 2 (by rfl) ⟨22065, by rfl⟩) (B 44131 (by norm_num) ⟨22065, by rfl⟩ (by norm_num))
theorem R58845 : Reach 58845 := rs (se 3 (by rfl) ⟨11033, by rfl⟩) (B 22067 (by norm_num) ⟨11033, by rfl⟩ (by norm_num))
theorem R58849 : Reach 58849 := rs (se 2 (by rfl) ⟨22068, by rfl⟩) (B 44137 (by norm_num) ⟨22068, by rfl⟩ (by norm_num))
theorem R157157 : Reach 157157 := rs (se 4 (by rfl) ⟨14733, by rfl⟩) (B 29467 (by norm_num) ⟨14733, by rfl⟩ (by norm_num))
theorem R58853 : Reach 58853 := rs (se 4 (by rfl) ⟨5517, by rfl⟩) (B 11035 (by norm_num) ⟨5517, by rfl⟩ (by norm_num))
theorem R58857 : Reach 58857 := rs (se 2 (by rfl) ⟨22071, by rfl⟩) (B 44143 (by norm_num) ⟨22071, by rfl⟩ (by norm_num))
theorem R124397 : Reach 124397 := rs (se 3 (by rfl) ⟨23324, by rfl⟩) (B 46649 (by norm_num) ⟨23324, by rfl⟩ (by norm_num))
theorem R58861 : Reach 58861 := rs (se 3 (by rfl) ⟨11036, by rfl⟩) (B 22073 (by norm_num) ⟨11036, by rfl⟩ (by norm_num))
theorem R58865 : Reach 58865 := rs (se 2 (by rfl) ⟨22074, by rfl⟩) (B 44149 (by norm_num) ⟨22074, by rfl⟩ (by norm_num))
theorem R222709 : Reach 222709 := rs (se 5 (by rfl) ⟨10439, by rfl⟩) (B 20879 (by norm_num) ⟨10439, by rfl⟩ (by norm_num))
theorem R58869 : Reach 58869 := rs (se 5 (by rfl) ⟨2759, by rfl⟩) (B 5519 (by norm_num) ⟨2759, by rfl⟩ (by norm_num))
theorem R58873 : Reach 58873 := rs (se 2 (by rfl) ⟨22077, by rfl⟩) (B 44155 (by norm_num) ⟨22077, by rfl⟩ (by norm_num))
theorem R58877 : Reach 58877 := rs (se 3 (by rfl) ⟨11039, by rfl⟩) (B 22079 (by norm_num) ⟨11039, by rfl⟩ (by norm_num))
theorem R58881 : Reach 58881 := rs (se 2 (by rfl) ⟨22080, by rfl⟩) (B 44161 (by norm_num) ⟨22080, by rfl⟩ (by norm_num))
theorem R58885 : Reach 58885 := rs (se 4 (by rfl) ⟨5520, by rfl⟩) (B 11041 (by norm_num) ⟨5520, by rfl⟩ (by norm_num))
theorem R58889 : Reach 58889 := rs (se 2 (by rfl) ⟨22083, by rfl⟩) (B 44167 (by norm_num) ⟨22083, by rfl⟩ (by norm_num))
theorem R58893 : Reach 58893 := rs (se 3 (by rfl) ⟨11042, by rfl⟩) (B 22085 (by norm_num) ⟨11042, by rfl⟩ (by norm_num))
theorem R58897 : Reach 58897 := rs (se 2 (by rfl) ⟨22086, by rfl⟩) (B 44173 (by norm_num) ⟨22086, by rfl⟩ (by norm_num))
theorem R58901 : Reach 58901 := rs (se 6 (by rfl) ⟨1380, by rfl⟩) (B 2761 (by norm_num) ⟨1380, by rfl⟩ (by norm_num))
theorem R58905 : Reach 58905 := rs (se 2 (by rfl) ⟨22089, by rfl⟩) (B 44179 (by norm_num) ⟨22089, by rfl⟩ (by norm_num))
theorem R58909 : Reach 58909 := rs (se 3 (by rfl) ⟨11045, by rfl⟩) (B 22091 (by norm_num) ⟨11045, by rfl⟩ (by norm_num))
theorem R58913 : Reach 58913 := rs (se 2 (by rfl) ⟨22092, by rfl⟩) (B 44185 (by norm_num) ⟨22092, by rfl⟩ (by norm_num))
theorem R58917 : Reach 58917 := rs (se 4 (by rfl) ⟨5523, by rfl⟩) (B 11047 (by norm_num) ⟨5523, by rfl⟩ (by norm_num))
theorem R58921 : Reach 58921 := rs (se 2 (by rfl) ⟨22095, by rfl⟩) (B 44191 (by norm_num) ⟨22095, by rfl⟩ (by norm_num))
theorem R58925 : Reach 58925 := rs (se 3 (by rfl) ⟨11048, by rfl⟩) (B 22097 (by norm_num) ⟨11048, by rfl⟩ (by norm_num))
theorem R58929 : Reach 58929 := rs (se 2 (by rfl) ⟨22098, by rfl⟩) (B 44197 (by norm_num) ⟨22098, by rfl⟩ (by norm_num))
theorem R124469 : Reach 124469 := rs (se 5 (by rfl) ⟨5834, by rfl⟩) (B 11669 (by norm_num) ⟨5834, by rfl⟩ (by norm_num))
theorem R58933 : Reach 58933 := rs (se 5 (by rfl) ⟨2762, by rfl⟩) (B 5525 (by norm_num) ⟨2762, by rfl⟩ (by norm_num))
theorem R58937 : Reach 58937 := rs (se 2 (by rfl) ⟨22101, by rfl⟩) (B 44203 (by norm_num) ⟨22101, by rfl⟩ (by norm_num))
theorem R58941 : Reach 58941 := rs (se 3 (by rfl) ⟨11051, by rfl⟩) (B 22103 (by norm_num) ⟨11051, by rfl⟩ (by norm_num))
theorem R58945 : Reach 58945 := rs (se 2 (by rfl) ⟨22104, by rfl⟩) (B 44209 (by norm_num) ⟨22104, by rfl⟩ (by norm_num))
theorem R58949 : Reach 58949 := rs (se 4 (by rfl) ⟨5526, by rfl⟩) (B 11053 (by norm_num) ⟨5526, by rfl⟩ (by norm_num))
theorem R58953 : Reach 58953 := rs (se 2 (by rfl) ⟨22107, by rfl⟩) (B 44215 (by norm_num) ⟨22107, by rfl⟩ (by norm_num))
theorem R58957 : Reach 58957 := rs (se 3 (by rfl) ⟨11054, by rfl⟩) (B 22109 (by norm_num) ⟨11054, by rfl⟩ (by norm_num))
theorem R58961 : Reach 58961 := rs (se 2 (by rfl) ⟨22110, by rfl⟩) (B 44221 (by norm_num) ⟨22110, by rfl⟩ (by norm_num))
theorem R58965 : Reach 58965 := rs (se 8 (by rfl) ⟨345, by rfl⟩) (B 691 (by norm_num) ⟨345, by rfl⟩ (by norm_num))
theorem R58969 : Reach 58969 := rs (se 2 (by rfl) ⟨22113, by rfl⟩) (B 44227 (by norm_num) ⟨22113, by rfl⟩ (by norm_num))
theorem R58973 : Reach 58973 := rs (se 3 (by rfl) ⟨11057, by rfl⟩) (B 22115 (by norm_num) ⟨11057, by rfl⟩ (by norm_num))
theorem R58977 : Reach 58977 := rs (se 2 (by rfl) ⟨22116, by rfl⟩) (B 44233 (by norm_num) ⟨22116, by rfl⟩ (by norm_num))
theorem R58981 : Reach 58981 := rs (se 4 (by rfl) ⟨5529, by rfl⟩) (B 11059 (by norm_num) ⟨5529, by rfl⟩ (by norm_num))
theorem R58985 : Reach 58985 := rs (se 2 (by rfl) ⟨22119, by rfl⟩) (B 44239 (by norm_num) ⟨22119, by rfl⟩ (by norm_num))
theorem R58989 : Reach 58989 := rs (se 3 (by rfl) ⟨11060, by rfl⟩) (B 22121 (by norm_num) ⟨11060, by rfl⟩ (by norm_num))
theorem R58993 : Reach 58993 := rs (se 2 (by rfl) ⟨22122, by rfl⟩) (B 44245 (by norm_num) ⟨22122, by rfl⟩ (by norm_num))
theorem R58997 : Reach 58997 := rs (se 5 (by rfl) ⟨2765, by rfl⟩) (B 5531 (by norm_num) ⟨2765, by rfl⟩ (by norm_num))
theorem R59001 : Reach 59001 := rs (se 2 (by rfl) ⟨22125, by rfl⟩) (B 44251 (by norm_num) ⟨22125, by rfl⟩ (by norm_num))
theorem R124541 : Reach 124541 := rs (se 3 (by rfl) ⟨23351, by rfl⟩) (B 46703 (by norm_num) ⟨23351, by rfl⟩ (by norm_num))
theorem R59005 : Reach 59005 := rs (se 3 (by rfl) ⟨11063, by rfl⟩) (B 22127 (by norm_num) ⟨11063, by rfl⟩ (by norm_num))
theorem R59009 : Reach 59009 := rs (se 2 (by rfl) ⟨22128, by rfl⟩) (B 44257 (by norm_num) ⟨22128, by rfl⟩ (by norm_num))
theorem R59013 : Reach 59013 := rs (se 4 (by rfl) ⟨5532, by rfl⟩) (B 11065 (by norm_num) ⟨5532, by rfl⟩ (by norm_num))
theorem R59017 : Reach 59017 := rs (se 2 (by rfl) ⟨22131, by rfl⟩) (B 44263 (by norm_num) ⟨22131, by rfl⟩ (by norm_num))
theorem R59021 : Reach 59021 := rs (se 3 (by rfl) ⟨11066, by rfl⟩) (B 22133 (by norm_num) ⟨11066, by rfl⟩ (by norm_num))
theorem R59025 : Reach 59025 := rs (se 2 (by rfl) ⟨22134, by rfl⟩) (B 44269 (by norm_num) ⟨22134, by rfl⟩ (by norm_num))
theorem R59029 : Reach 59029 := rs (se 6 (by rfl) ⟨1383, by rfl⟩) (B 2767 (by norm_num) ⟨1383, by rfl⟩ (by norm_num))
theorem R59033 : Reach 59033 := rs (se 2 (by rfl) ⟨22137, by rfl⟩) (B 44275 (by norm_num) ⟨22137, by rfl⟩ (by norm_num))
theorem R59037 : Reach 59037 := rs (se 3 (by rfl) ⟨11069, by rfl⟩) (B 22139 (by norm_num) ⟨11069, by rfl⟩ (by norm_num))
theorem R59041 : Reach 59041 := rs (se 2 (by rfl) ⟨22140, by rfl⟩) (B 44281 (by norm_num) ⟨22140, by rfl⟩ (by norm_num))
theorem R59045 : Reach 59045 := rs (se 4 (by rfl) ⟨5535, by rfl⟩) (B 11071 (by norm_num) ⟨5535, by rfl⟩ (by norm_num))
theorem R59049 : Reach 59049 := rs (se 2 (by rfl) ⟨22143, by rfl⟩) (B 44287 (by norm_num) ⟨22143, by rfl⟩ (by norm_num))
theorem R59053 : Reach 59053 := rs (se 3 (by rfl) ⟨11072, by rfl⟩) (B 22145 (by norm_num) ⟨11072, by rfl⟩ (by norm_num))
theorem R59057 : Reach 59057 := rs (se 2 (by rfl) ⟨22146, by rfl⟩) (B 44293 (by norm_num) ⟨22146, by rfl⟩ (by norm_num))
theorem R190133 : Reach 190133 := rs (se 5 (by rfl) ⟨8912, by rfl⟩) (B 17825 (by norm_num) ⟨8912, by rfl⟩ (by norm_num))
theorem R91829 : Reach 91829 := rs (se 5 (by rfl) ⟨4304, by rfl⟩) (B 8609 (by norm_num) ⟨4304, by rfl⟩ (by norm_num))
theorem R59061 : Reach 59061 := rs (se 5 (by rfl) ⟨2768, by rfl⟩) (B 5537 (by norm_num) ⟨2768, by rfl⟩ (by norm_num))
theorem R59065 : Reach 59065 := rs (se 2 (by rfl) ⟨22149, by rfl⟩) (B 44299 (by norm_num) ⟨22149, by rfl⟩ (by norm_num))
theorem R59069 : Reach 59069 := rs (se 3 (by rfl) ⟨11075, by rfl⟩) (B 22151 (by norm_num) ⟨11075, by rfl⟩ (by norm_num))
theorem R59073 : Reach 59073 := rs (se 2 (by rfl) ⟨22152, by rfl⟩) (B 44305 (by norm_num) ⟨22152, by rfl⟩ (by norm_num))
theorem R124613 : Reach 124613 := rs (se 4 (by rfl) ⟨11682, by rfl⟩) (B 23365 (by norm_num) ⟨11682, by rfl⟩ (by norm_num))
theorem R59077 : Reach 59077 := rs (se 4 (by rfl) ⟨5538, by rfl⟩) (B 11077 (by norm_num) ⟨5538, by rfl⟩ (by norm_num))
theorem R59081 : Reach 59081 := rs (se 2 (by rfl) ⟨22155, by rfl⟩) (B 44311 (by norm_num) ⟨22155, by rfl⟩ (by norm_num))
theorem R59085 : Reach 59085 := rs (se 3 (by rfl) ⟨11078, by rfl⟩) (B 22157 (by norm_num) ⟨11078, by rfl⟩ (by norm_num))
theorem R59089 : Reach 59089 := rs (se 2 (by rfl) ⟨22158, by rfl⟩) (B 44317 (by norm_num) ⟨22158, by rfl⟩ (by norm_num))
theorem R59093 : Reach 59093 := rs (se 7 (by rfl) ⟨692, by rfl⟩) (B 1385 (by norm_num) ⟨692, by rfl⟩ (by norm_num))
theorem R59097 : Reach 59097 := rs (se 2 (by rfl) ⟨22161, by rfl⟩) (B 44323 (by norm_num) ⟨22161, by rfl⟩ (by norm_num))
theorem R59101 : Reach 59101 := rs (se 3 (by rfl) ⟨11081, by rfl⟩) (B 22163 (by norm_num) ⟨11081, by rfl⟩ (by norm_num))
theorem R59105 : Reach 59105 := rs (se 2 (by rfl) ⟨22164, by rfl⟩) (B 44329 (by norm_num) ⟨22164, by rfl⟩ (by norm_num))
theorem R59109 : Reach 59109 := rs (se 4 (by rfl) ⟨5541, by rfl⟩) (B 11083 (by norm_num) ⟨5541, by rfl⟩ (by norm_num))
theorem R59113 : Reach 59113 := rs (se 2 (by rfl) ⟨22167, by rfl⟩) (B 44335 (by norm_num) ⟨22167, by rfl⟩ (by norm_num))
theorem R59117 : Reach 59117 := rs (se 3 (by rfl) ⟨11084, by rfl⟩) (B 22169 (by norm_num) ⟨11084, by rfl⟩ (by norm_num))
theorem R59121 : Reach 59121 := rs (se 2 (by rfl) ⟨22170, by rfl⟩) (B 44341 (by norm_num) ⟨22170, by rfl⟩ (by norm_num))
theorem R124685 : Reach 124685 := rs (se 3 (by rfl) ⟨23378, by rfl⟩) (B 46757 (by norm_num) ⟨23378, by rfl⟩ (by norm_num))
theorem R223013 : Reach 223013 := rs (se 4 (by rfl) ⟨20907, by rfl⟩) (B 41815 (by norm_num) ⟨20907, by rfl⟩ (by norm_num))
theorem R91957 : Reach 91957 := rs (se 5 (by rfl) ⟨4310, by rfl⟩) (B 8621 (by norm_num) ⟨4310, by rfl⟩ (by norm_num))
theorem R124757 : Reach 124757 := rs (se 9 (by rfl) ⟨365, by rfl⟩) (B 731 (by norm_num) ⟨365, by rfl⟩ (by norm_num))
theorem R92021 : Reach 92021 := rs (se 5 (by rfl) ⟨4313, by rfl⟩) (B 8627 (by norm_num) ⟨4313, by rfl⟩ (by norm_num))
theorem R124829 : Reach 124829 := rs (se 3 (by rfl) ⟨23405, by rfl⟩) (B 46811 (by norm_num) ⟨23405, by rfl⟩ (by norm_num))
theorem R59297 : Reach 59297 := rs (se 2 (by rfl) ⟨22236, by rfl⟩) (B 44473 (by norm_num) ⟨22236, by rfl⟩ (by norm_num))
theorem R124901 : Reach 124901 := rs (se 4 (by rfl) ⟨11709, by rfl⟩) (B 23419 (by norm_num) ⟨11709, by rfl⟩ (by norm_num))
theorem R124973 : Reach 124973 := rs (se 3 (by rfl) ⟨23432, by rfl⟩) (B 46865 (by norm_num) ⟨23432, by rfl⟩ (by norm_num))
theorem R190565 : Reach 190565 := rs (se 4 (by rfl) ⟨17865, by rfl⟩) (B 35731 (by norm_num) ⟨17865, by rfl⟩ (by norm_num))
theorem R125045 : Reach 125045 := rs (se 5 (by rfl) ⟨5861, by rfl⟩) (B 11723 (by norm_num) ⟨5861, by rfl⟩ (by norm_num))
theorem R256117 : Reach 256117 := rs (se 5 (by rfl) ⟨12005, by rfl⟩) (B 24011 (by norm_num) ⟨12005, by rfl⟩ (by norm_num))
theorem R125069 : Reach 125069 := rs (se 3 (by rfl) ⟨23450, by rfl⟩) (B 46901 (by norm_num) ⟨23450, by rfl⟩ (by norm_num))
theorem R59545 : Reach 59545 := rs (se 2 (by rfl) ⟨22329, by rfl⟩) (B 44659 (by norm_num) ⟨22329, by rfl⟩ (by norm_num))
theorem R125117 : Reach 125117 := rs (se 3 (by rfl) ⟨23459, by rfl⟩) (B 46919 (by norm_num) ⟨23459, by rfl⟩ (by norm_num))
theorem R157909 : Reach 157909 := rs (se 7 (by rfl) ⟨1850, by rfl⟩) (B 3701 (by norm_num) ⟨1850, by rfl⟩ (by norm_num))
theorem R125189 : Reach 125189 := rs (se 4 (by rfl) ⟨11736, by rfl⟩) (B 23473 (by norm_num) ⟨11736, by rfl⟩ (by norm_num))
theorem R125261 : Reach 125261 := rs (se 3 (by rfl) ⟨23486, by rfl⟩) (B 46973 (by norm_num) ⟨23486, by rfl⟩ (by norm_num))
theorem R125309 : Reach 125309 := rs (se 3 (by rfl) ⟨23495, by rfl⟩) (B 46991 (by norm_num) ⟨23495, by rfl⟩ (by norm_num))
theorem R125333 : Reach 125333 := rs (se 6 (by rfl) ⟨2937, by rfl⟩) (B 5875 (by norm_num) ⟨2937, by rfl⟩ (by norm_num))
theorem R223685 : Reach 223685 := rs (se 4 (by rfl) ⟨20970, by rfl⟩) (B 41941 (by norm_num) ⟨20970, by rfl⟩ (by norm_num))
theorem R125405 : Reach 125405 := rs (se 3 (by rfl) ⟨23513, by rfl⟩) (B 47027 (by norm_num) ⟨23513, by rfl⟩ (by norm_num))
theorem R190997 : Reach 190997 := rs (se 6 (by rfl) ⟨4476, by rfl⟩) (B 8953 (by norm_num) ⟨4476, by rfl⟩ (by norm_num))
theorem R125477 : Reach 125477 := rs (se 4 (by rfl) ⟨11763, by rfl⟩) (B 23527 (by norm_num) ⟨11763, by rfl⟩ (by norm_num))
theorem R59989 : Reach 59989 := rs (se 8 (by rfl) ⟨351, by rfl⟩) (B 703 (by norm_num) ⟨351, by rfl⟩ (by norm_num))
theorem R125549 : Reach 125549 := rs (se 3 (by rfl) ⟨23540, by rfl⟩) (B 47081 (by norm_num) ⟨23540, by rfl⟩ (by norm_num))
theorem R60049 : Reach 60049 := rs (se 2 (by rfl) ⟨22518, by rfl⟩) (B 45037 (by norm_num) ⟨22518, by rfl⟩ (by norm_num))
theorem R125621 : Reach 125621 := rs (se 5 (by rfl) ⟨5888, by rfl⟩) (B 11777 (by norm_num) ⟨5888, by rfl⟩ (by norm_num))
theorem R289493 : Reach 289493 := rs (se 7 (by rfl) ⟨3392, by rfl⟩) (B 6785 (by norm_num) ⟨3392, by rfl⟩ (by norm_num))
theorem R125669 : Reach 125669 := rs (se 4 (by rfl) ⟨11781, by rfl⟩) (B 23563 (by norm_num) ⟨11781, by rfl⟩ (by norm_num))
theorem R125693 : Reach 125693 := rs (se 3 (by rfl) ⟨23567, by rfl⟩) (B 47135 (by norm_num) ⟨23567, by rfl⟩ (by norm_num))
theorem R125765 : Reach 125765 := rs (se 4 (by rfl) ⟨11790, by rfl⟩) (B 23581 (by norm_num) ⟨11790, by rfl⟩ (by norm_num))
theorem R93005 : Reach 93005 := rs (se 3 (by rfl) ⟨17438, by rfl⟩) (B 34877 (by norm_num) ⟨17438, by rfl⟩ (by norm_num))
theorem R191333 : Reach 191333 := rs (se 4 (by rfl) ⟨17937, by rfl⟩) (B 35875 (by norm_num) ⟨17937, by rfl⟩ (by norm_num))
theorem R125813 : Reach 125813 := rs (se 5 (by rfl) ⟨5897, by rfl⟩) (B 11795 (by norm_num) ⟨5897, by rfl⟩ (by norm_num))
theorem R125821 : Reach 125821 := rs (se 3 (by rfl) ⟨23591, by rfl⟩) (B 47183 (by norm_num) ⟨23591, by rfl⟩ (by norm_num))
theorem R125837 : Reach 125837 := rs (se 3 (by rfl) ⟨23594, by rfl⟩) (B 47189 (by norm_num) ⟨23594, by rfl⟩ (by norm_num))
theorem R93109 : Reach 93109 := rs (se 5 (by rfl) ⟨4364, by rfl⟩) (B 8729 (by norm_num) ⟨4364, by rfl⟩ (by norm_num))
theorem R191429 : Reach 191429 := rs (se 4 (by rfl) ⟨17946, by rfl⟩) (B 35893 (by norm_num) ⟨17946, by rfl⟩ (by norm_num))
theorem R60365 : Reach 60365 := rs (se 3 (by rfl) ⟨11318, by rfl⟩) (B 22637 (by norm_num) ⟨11318, by rfl⟩ (by norm_num))
theorem R125909 : Reach 125909 := rs (se 7 (by rfl) ⟨1475, by rfl⟩) (B 2951 (by norm_num) ⟨1475, by rfl⟩ (by norm_num))
theorem R93197 : Reach 93197 := rs (se 3 (by rfl) ⟨17474, by rfl⟩) (B 34949 (by norm_num) ⟨17474, by rfl⟩ (by norm_num))
theorem R125981 : Reach 125981 := rs (se 3 (by rfl) ⟨23621, by rfl⟩) (B 47243 (by norm_num) ⟨23621, by rfl⟩ (by norm_num))
theorem R126053 : Reach 126053 := rs (se 4 (by rfl) ⟨11817, by rfl⟩) (B 23635 (by norm_num) ⟨11817, by rfl⟩ (by norm_num))
theorem R93325 : Reach 93325 := rs (se 3 (by rfl) ⟨17498, by rfl⟩) (B 34997 (by norm_num) ⟨17498, by rfl⟩ (by norm_num))
theorem R93341 : Reach 93341 := rs (se 3 (by rfl) ⟨17501, by rfl⟩) (B 35003 (by norm_num) ⟨17501, by rfl⟩ (by norm_num))
theorem R257189 : Reach 257189 := rs (se 4 (by rfl) ⟨24111, by rfl⟩) (B 48223 (by norm_num) ⟨24111, by rfl⟩ (by norm_num))
theorem R126125 : Reach 126125 := rs (se 3 (by rfl) ⟨23648, by rfl⟩) (B 47297 (by norm_num) ⟨23648, by rfl⟩ (by norm_num))
theorem R93413 : Reach 93413 := rs (se 4 (by rfl) ⟨8757, by rfl⟩) (B 17515 (by norm_num) ⟨8757, by rfl⟩ (by norm_num))
theorem R126197 : Reach 126197 := rs (se 5 (by rfl) ⟨5915, by rfl⟩) (B 11831 (by norm_num) ⟨5915, by rfl⟩ (by norm_num))
theorem R93469 : Reach 93469 := rs (se 3 (by rfl) ⟨17525, by rfl⟩) (B 35051 (by norm_num) ⟨17525, by rfl⟩ (by norm_num))
theorem R159013 : Reach 159013 := rs (se 4 (by rfl) ⟨14907, by rfl⟩) (B 29815 (by norm_num) ⟨14907, by rfl⟩ (by norm_num))
theorem R93485 : Reach 93485 := rs (se 3 (by rfl) ⟨17528, by rfl⟩) (B 35057 (by norm_num) ⟨17528, by rfl⟩ (by norm_num))
theorem R159029 : Reach 159029 := rs (se 5 (by rfl) ⟨7454, by rfl⟩) (B 14909 (by norm_num) ⟨7454, by rfl⟩ (by norm_num))
theorem R126269 : Reach 126269 := rs (se 3 (by rfl) ⟨23675, by rfl⟩) (B 47351 (by norm_num) ⟨23675, by rfl⟩ (by norm_num))
theorem R93541 : Reach 93541 := rs (se 4 (by rfl) ⟨8769, by rfl⟩) (B 17539 (by norm_num) ⟨8769, by rfl⟩ (by norm_num))
theorem R126325 : Reach 126325 := rs (se 5 (by rfl) ⟨5921, by rfl⟩) (B 11843 (by norm_num) ⟨5921, by rfl⟩ (by norm_num))
theorem R191861 : Reach 191861 := rs (se 5 (by rfl) ⟨8993, by rfl⟩) (B 17987 (by norm_num) ⟨8993, by rfl⟩ (by norm_num))
theorem R126341 : Reach 126341 := rs (se 4 (by rfl) ⟨11844, by rfl⟩) (B 23689 (by norm_num) ⟨11844, by rfl⟩ (by norm_num))
theorem R60809 : Reach 60809 := rs (se 2 (by rfl) ⟨22803, by rfl⟩) (B 45607 (by norm_num) ⟨22803, by rfl⟩ (by norm_num))
theorem R93629 : Reach 93629 := rs (se 3 (by rfl) ⟨17555, by rfl⟩) (B 35111 (by norm_num) ⟨17555, by rfl⟩ (by norm_num))
theorem R60869 : Reach 60869 := rs (se 4 (by rfl) ⟨5706, by rfl⟩) (B 11413 (by norm_num) ⟨5706, by rfl⟩ (by norm_num))
theorem R126413 : Reach 126413 := rs (se 3 (by rfl) ⟨23702, by rfl⟩) (B 47405 (by norm_num) ⟨23702, by rfl⟩ (by norm_num))
theorem R126485 : Reach 126485 := rs (se 6 (by rfl) ⟨2964, by rfl⟩) (B 5929 (by norm_num) ⟨2964, by rfl⟩ (by norm_num))
theorem R93757 : Reach 93757 := rs (se 3 (by rfl) ⟨17579, by rfl⟩) (B 35159 (by norm_num) ⟨17579, by rfl⟩ (by norm_num))
theorem R60997 : Reach 60997 := rs (se 4 (by rfl) ⟨5718, by rfl⟩) (B 11437 (by norm_num) ⟨5718, by rfl⟩ (by norm_num))
theorem R126557 : Reach 126557 := rs (se 3 (by rfl) ⟨23729, by rfl⟩) (B 47459 (by norm_num) ⟨23729, by rfl⟩ (by norm_num))
theorem R93845 : Reach 93845 := rs (se 6 (by rfl) ⟨2199, by rfl⟩) (B 4399 (by norm_num) ⟨2199, by rfl⟩ (by norm_num))
theorem R126629 : Reach 126629 := rs (se 4 (by rfl) ⟨11871, by rfl⟩) (B 23743 (by norm_num) ⟨11871, by rfl⟩ (by norm_num))
theorem R126701 : Reach 126701 := rs (se 3 (by rfl) ⟨23756, by rfl⟩) (B 47513 (by norm_num) ⟨23756, by rfl⟩ (by norm_num))
theorem R93973 : Reach 93973 := rs (se 6 (by rfl) ⟨2202, by rfl⟩) (B 4405 (by norm_num) ⟨2202, by rfl⟩ (by norm_num))
theorem R192293 : Reach 192293 := rs (se 4 (by rfl) ⟨18027, by rfl⟩) (B 36055 (by norm_num) ⟨18027, by rfl⟩ (by norm_num))
theorem R126773 : Reach 126773 := rs (se 5 (by rfl) ⟨5942, by rfl⟩) (B 11885 (by norm_num) ⟨5942, by rfl⟩ (by norm_num))
theorem R94061 : Reach 94061 := rs (se 3 (by rfl) ⟨17636, by rfl⟩) (B 35273 (by norm_num) ⟨17636, by rfl⟩ (by norm_num))
theorem R126845 : Reach 126845 := rs (se 3 (by rfl) ⟨23783, by rfl⟩) (B 47567 (by norm_num) ⟨23783, by rfl⟩ (by norm_num))
theorem R126917 : Reach 126917 := rs (se 4 (by rfl) ⟨11898, by rfl⟩) (B 23797 (by norm_num) ⟨11898, by rfl⟩ (by norm_num))
theorem R290789 : Reach 290789 := rs (se 4 (by rfl) ⟨27261, by rfl⟩) (B 54523 (by norm_num) ⟨27261, by rfl⟩ (by norm_num))
theorem R94189 : Reach 94189 := rs (se 3 (by rfl) ⟨17660, by rfl⟩) (B 35321 (by norm_num) ⟨17660, by rfl⟩ (by norm_num))
theorem R61441 : Reach 61441 := rs (se 2 (by rfl) ⟨23040, by rfl⟩) (B 46081 (by norm_num) ⟨23040, by rfl⟩ (by norm_num))
theorem R126989 : Reach 126989 := rs (se 3 (by rfl) ⟨23810, by rfl⟩) (B 47621 (by norm_num) ⟨23810, by rfl⟩ (by norm_num))
theorem R94277 : Reach 94277 := rs (se 4 (by rfl) ⟨8838, by rfl⟩) (B 17677 (by norm_num) ⟨8838, by rfl⟩ (by norm_num))
theorem R127061 : Reach 127061 := rs (se 8 (by rfl) ⟨744, by rfl⟩) (B 1489 (by norm_num) ⟨744, by rfl⟩ (by norm_num))
theorem R61561 : Reach 61561 := rs (se 2 (by rfl) ⟨23085, by rfl⟩) (B 46171 (by norm_num) ⟨23085, by rfl⟩ (by norm_num))
theorem R127133 : Reach 127133 := rs (se 3 (by rfl) ⟨23837, by rfl⟩) (B 47675 (by norm_num) ⟨23837, by rfl⟩ (by norm_num))
theorem R94405 : Reach 94405 := rs (se 4 (by rfl) ⟨8850, by rfl⟩) (B 17701 (by norm_num) ⟨8850, by rfl⟩ (by norm_num))
theorem R192725 : Reach 192725 := rs (se 7 (by rfl) ⟨2258, by rfl⟩) (B 4517 (by norm_num) ⟨2258, by rfl⟩ (by norm_num))
theorem R127205 : Reach 127205 := rs (se 4 (by rfl) ⟨11925, by rfl⟩) (B 23851 (by norm_num) ⟨11925, by rfl⟩ (by norm_num))
theorem R94493 : Reach 94493 := rs (se 3 (by rfl) ⟨17717, by rfl⟩) (B 35435 (by norm_num) ⟨17717, by rfl⟩ (by norm_num))
theorem R127277 : Reach 127277 := rs (se 3 (by rfl) ⟨23864, by rfl⟩) (B 47729 (by norm_num) ⟨23864, by rfl⟩ (by norm_num))
theorem R94565 : Reach 94565 := rs (se 4 (by rfl) ⟨8865, by rfl⟩) (B 17731 (by norm_num) ⟨8865, by rfl⟩ (by norm_num))
theorem R127349 : Reach 127349 := rs (se 5 (by rfl) ⟨5969, by rfl⟩) (B 11939 (by norm_num) ⟨5969, by rfl⟩ (by norm_num))
theorem R61813 : Reach 61813 := rs (se 5 (by rfl) ⟨2897, by rfl⟩) (B 5795 (by norm_num) ⟨2897, by rfl⟩ (by norm_num))
theorem R61817 : Reach 61817 := rs (se 2 (by rfl) ⟨23181, by rfl⟩) (B 46363 (by norm_num) ⟨23181, by rfl⟩ (by norm_num))
theorem R94621 : Reach 94621 := rs (se 3 (by rfl) ⟨17741, by rfl⟩) (B 35483 (by norm_num) ⟨17741, by rfl⟩ (by norm_num))
theorem R127421 : Reach 127421 := rs (se 3 (by rfl) ⟨23891, by rfl⟩) (B 47783 (by norm_num) ⟨23891, by rfl⟩ (by norm_num))
theorem R94709 : Reach 94709 := rs (se 5 (by rfl) ⟨4439, by rfl⟩) (B 8879 (by norm_num) ⟨4439, by rfl⟩ (by norm_num))
theorem R127493 : Reach 127493 := rs (se 4 (by rfl) ⟨11952, by rfl⟩) (B 23905 (by norm_num) ⟨11952, by rfl⟩ (by norm_num))
theorem R61969 : Reach 61969 := rs (se 2 (by rfl) ⟨23238, by rfl⟩) (B 46477 (by norm_num) ⟨23238, by rfl⟩ (by norm_num))
theorem R94765 : Reach 94765 := rs (se 3 (by rfl) ⟨17768, by rfl⟩) (B 35537 (by norm_num) ⟨17768, by rfl⟩ (by norm_num))
theorem R127565 : Reach 127565 := rs (se 3 (by rfl) ⟨23918, by rfl⟩) (B 47837 (by norm_num) ⟨23918, by rfl⟩ (by norm_num))
theorem R62041 : Reach 62041 := rs (se 2 (by rfl) ⟨23265, by rfl⟩) (B 46531 (by norm_num) ⟨23265, by rfl⟩ (by norm_num))
theorem R94837 : Reach 94837 := rs (se 5 (by rfl) ⟨4445, by rfl⟩) (B 8891 (by norm_num) ⟨4445, by rfl⟩ (by norm_num))
theorem R62077 : Reach 62077 := rs (se 3 (by rfl) ⟨11639, by rfl⟩) (B 23279 (by norm_num) ⟨11639, by rfl⟩ (by norm_num))
theorem R193157 : Reach 193157 := rs (se 4 (by rfl) ⟨18108, by rfl⟩) (B 36217 (by norm_num) ⟨18108, by rfl⟩ (by norm_num))
theorem R127637 : Reach 127637 := rs (se 6 (by rfl) ⟨2991, by rfl⟩) (B 5983 (by norm_num) ⟨2991, by rfl⟩ (by norm_num))
theorem R62113 : Reach 62113 := rs (se 2 (by rfl) ⟨23292, by rfl⟩) (B 46585 (by norm_num) ⟨23292, by rfl⟩ (by norm_num))
theorem R62149 : Reach 62149 := rs (se 4 (by rfl) ⟨5826, by rfl⟩) (B 11653 (by norm_num) ⟨5826, by rfl⟩ (by norm_num))
theorem R94925 : Reach 94925 := rs (se 3 (by rfl) ⟨17798, by rfl⟩) (B 35597 (by norm_num) ⟨17798, by rfl⟩ (by norm_num))
theorem R127709 : Reach 127709 := rs (se 3 (by rfl) ⟨23945, by rfl⟩) (B 47891 (by norm_num) ⟨23945, by rfl⟩ (by norm_num))
theorem R62185 : Reach 62185 := rs (se 2 (by rfl) ⟨23319, by rfl⟩) (B 46639 (by norm_num) ⟨23319, by rfl⟩ (by norm_num))
theorem R160517 : Reach 160517 := rs (se 4 (by rfl) ⟨15048, by rfl⟩) (B 30097 (by norm_num) ⟨15048, by rfl⟩ (by norm_num))
theorem R62221 : Reach 62221 := rs (se 3 (by rfl) ⟨11666, by rfl⟩) (B 23333 (by norm_num) ⟨11666, by rfl⟩ (by norm_num))
theorem R127781 : Reach 127781 := rs (se 4 (by rfl) ⟨11979, by rfl⟩) (B 23959 (by norm_num) ⟨11979, by rfl⟩ (by norm_num))
theorem R62257 : Reach 62257 := rs (se 2 (by rfl) ⟨23346, by rfl⟩) (B 46693 (by norm_num) ⟨23346, by rfl⟩ (by norm_num))
theorem R95053 : Reach 95053 := rs (se 3 (by rfl) ⟨17822, by rfl⟩) (B 35645 (by norm_num) ⟨17822, by rfl⟩ (by norm_num))
theorem R62293 : Reach 62293 := rs (se 9 (by rfl) ⟨182, by rfl⟩) (B 365 (by norm_num) ⟨182, by rfl⟩ (by norm_num))
theorem R127853 : Reach 127853 := rs (se 3 (by rfl) ⟨23972, by rfl⟩) (B 47945 (by norm_num) ⟨23972, by rfl⟩ (by norm_num))
theorem R62329 : Reach 62329 := rs (se 2 (by rfl) ⟨23373, by rfl⟩) (B 46747 (by norm_num) ⟨23373, by rfl⟩ (by norm_num))
theorem R62365 : Reach 62365 := rs (se 3 (by rfl) ⟨11693, by rfl⟩) (B 23387 (by norm_num) ⟨11693, by rfl⟩ (by norm_num))
theorem R95141 : Reach 95141 := rs (se 4 (by rfl) ⟨8919, by rfl⟩) (B 17839 (by norm_num) ⟨8919, by rfl⟩ (by norm_num))
theorem R62381 : Reach 62381 := rs (se 3 (by rfl) ⟨11696, by rfl⟩) (B 23393 (by norm_num) ⟨11696, by rfl⟩ (by norm_num))
theorem R127925 : Reach 127925 := rs (se 5 (by rfl) ⟨5996, by rfl⟩) (B 11993 (by norm_num) ⟨5996, by rfl⟩ (by norm_num))
theorem R62401 : Reach 62401 := rs (se 2 (by rfl) ⟨23400, by rfl⟩) (B 46801 (by norm_num) ⟨23400, by rfl⟩ (by norm_num))
theorem R62437 : Reach 62437 := rs (se 4 (by rfl) ⟨5853, by rfl⟩) (B 11707 (by norm_num) ⟨5853, by rfl⟩ (by norm_num))
theorem R127997 : Reach 127997 := rs (se 3 (by rfl) ⟨23999, by rfl⟩) (B 47999 (by norm_num) ⟨23999, by rfl⟩ (by norm_num))
theorem R62473 : Reach 62473 := rs (se 2 (by rfl) ⟨23427, by rfl⟩) (B 46855 (by norm_num) ⟨23427, by rfl⟩ (by norm_num))
theorem R95269 : Reach 95269 := rs (se 4 (by rfl) ⟨8931, by rfl⟩) (B 17863 (by norm_num) ⟨8931, by rfl⟩ (by norm_num))
theorem R62509 : Reach 62509 := rs (se 3 (by rfl) ⟨11720, by rfl⟩) (B 23441 (by norm_num) ⟨11720, by rfl⟩ (by norm_num))
theorem R193589 : Reach 193589 := rs (se 5 (by rfl) ⟨9074, by rfl⟩) (B 18149 (by norm_num) ⟨9074, by rfl⟩ (by norm_num))
theorem R128069 : Reach 128069 := rs (se 4 (by rfl) ⟨12006, by rfl⟩) (B 24013 (by norm_num) ⟨12006, by rfl⟩ (by norm_num))
theorem R62545 : Reach 62545 := rs (se 2 (by rfl) ⟨23454, by rfl⟩) (B 46909 (by norm_num) ⟨23454, by rfl⟩ (by norm_num))
theorem R62569 : Reach 62569 := rs (se 2 (by rfl) ⟨23463, by rfl⟩) (B 46927 (by norm_num) ⟨23463, by rfl⟩ (by norm_num))
theorem R62581 : Reach 62581 := rs (se 5 (by rfl) ⟨2933, by rfl⟩) (B 5867 (by norm_num) ⟨2933, by rfl⟩ (by norm_num))
theorem R95357 : Reach 95357 := rs (se 3 (by rfl) ⟨17879, by rfl⟩) (B 35759 (by norm_num) ⟨17879, by rfl⟩ (by norm_num))
theorem R128141 : Reach 128141 := rs (se 3 (by rfl) ⟨24026, by rfl⟩) (B 48053 (by norm_num) ⟨24026, by rfl⟩ (by norm_num))
theorem R62617 : Reach 62617 := rs (se 2 (by rfl) ⟨23481, by rfl⟩) (B 46963 (by norm_num) ⟨23481, by rfl⟩ (by norm_num))
theorem R62653 : Reach 62653 := rs (se 3 (by rfl) ⟨11747, by rfl⟩) (B 23495 (by norm_num) ⟨11747, by rfl⟩ (by norm_num))
theorem R128213 : Reach 128213 := rs (se 7 (by rfl) ⟨1502, by rfl⟩) (B 3005 (by norm_num) ⟨1502, by rfl⟩ (by norm_num))
theorem R62689 : Reach 62689 := rs (se 2 (by rfl) ⟨23508, by rfl⟩) (B 47017 (by norm_num) ⟨23508, by rfl⟩ (by norm_num))
theorem R95461 : Reach 95461 := rs (se 4 (by rfl) ⟨8949, by rfl⟩) (B 17899 (by norm_num) ⟨8949, by rfl⟩ (by norm_num))
theorem R292085 : Reach 292085 := rs (se 5 (by rfl) ⟨13691, by rfl⟩) (B 27383 (by norm_num) ⟨13691, by rfl⟩ (by norm_num))
theorem R95485 : Reach 95485 := rs (se 3 (by rfl) ⟨17903, by rfl⟩) (B 35807 (by norm_num) ⟨17903, by rfl⟩ (by norm_num))
theorem R62725 : Reach 62725 := rs (se 4 (by rfl) ⟨5880, by rfl⟩) (B 11761 (by norm_num) ⟨5880, by rfl⟩ (by norm_num))
theorem R128285 : Reach 128285 := rs (se 3 (by rfl) ⟨24053, by rfl⟩) (B 48107 (by norm_num) ⟨24053, by rfl⟩ (by norm_num))
theorem R62761 : Reach 62761 := rs (se 2 (by rfl) ⟨23535, by rfl⟩) (B 47071 (by norm_num) ⟨23535, by rfl⟩ (by norm_num))
theorem R62797 : Reach 62797 := rs (se 3 (by rfl) ⟨11774, by rfl⟩) (B 23549 (by norm_num) ⟨11774, by rfl⟩ (by norm_num))
theorem R95573 : Reach 95573 := rs (se 13 (by rfl) ⟨17, by rfl⟩) (B 35 (by norm_num) ⟨17, by rfl⟩ (by norm_num))
theorem R3437909 : Reach 3437909 := rs (se 13 (by rfl) ⟨629, by rfl⟩) (B 1259 (by norm_num) ⟨629, by rfl⟩ (by norm_num))
theorem R128357 : Reach 128357 := rs (se 4 (by rfl) ⟨12033, by rfl⟩) (B 24067 (by norm_num) ⟨12033, by rfl⟩ (by norm_num))
theorem R62833 : Reach 62833 := rs (se 2 (by rfl) ⟨23562, by rfl⟩) (B 47125 (by norm_num) ⟨23562, by rfl⟩ (by norm_num))
theorem R62869 : Reach 62869 := rs (se 6 (by rfl) ⟨1473, by rfl⟩) (B 2947 (by norm_num) ⟨1473, by rfl⟩ (by norm_num))
theorem R128429 : Reach 128429 := rs (se 3 (by rfl) ⟨24080, by rfl⟩) (B 48161 (by norm_num) ⟨24080, by rfl⟩ (by norm_num))
theorem R62905 : Reach 62905 := rs (se 2 (by rfl) ⟨23589, by rfl⟩) (B 47179 (by norm_num) ⟨23589, by rfl⟩ (by norm_num))
theorem R95701 : Reach 95701 := rs (se 7 (by rfl) ⟨1121, by rfl⟩) (B 2243 (by norm_num) ⟨1121, by rfl⟩ (by norm_num))
theorem R62941 : Reach 62941 := rs (se 3 (by rfl) ⟨11801, by rfl⟩) (B 23603 (by norm_num) ⟨11801, by rfl⟩ (by norm_num))
theorem R194021 : Reach 194021 := rs (se 4 (by rfl) ⟨18189, by rfl⟩) (B 36379 (by norm_num) ⟨18189, by rfl⟩ (by norm_num))
theorem R128501 : Reach 128501 := rs (se 5 (by rfl) ⟨6023, by rfl⟩) (B 12047 (by norm_num) ⟨6023, by rfl⟩ (by norm_num))
theorem R62977 : Reach 62977 := rs (se 2 (by rfl) ⟨23616, by rfl⟩) (B 47233 (by norm_num) ⟨23616, by rfl⟩ (by norm_num))
theorem R63013 : Reach 63013 := rs (se 4 (by rfl) ⟨5907, by rfl⟩) (B 11815 (by norm_num) ⟨5907, by rfl⟩ (by norm_num))
theorem R95789 : Reach 95789 := rs (se 3 (by rfl) ⟨17960, by rfl⟩) (B 35921 (by norm_num) ⟨17960, by rfl⟩ (by norm_num))
theorem R128573 : Reach 128573 := rs (se 3 (by rfl) ⟨24107, by rfl⟩) (B 48215 (by norm_num) ⟨24107, by rfl⟩ (by norm_num))
theorem R63049 : Reach 63049 := rs (se 2 (by rfl) ⟨23643, by rfl⟩) (B 47287 (by norm_num) ⟨23643, by rfl⟩ (by norm_num))
theorem R63085 : Reach 63085 := rs (se 3 (by rfl) ⟨11828, by rfl⟩) (B 23657 (by norm_num) ⟨11828, by rfl⟩ (by norm_num))
theorem R128645 : Reach 128645 := rs (se 4 (by rfl) ⟨12060, by rfl⟩) (B 24121 (by norm_num) ⟨12060, by rfl⟩ (by norm_num))
theorem R63121 : Reach 63121 := rs (se 2 (by rfl) ⟨23670, by rfl⟩) (B 47341 (by norm_num) ⟨23670, by rfl⟩ (by norm_num))
theorem R95917 : Reach 95917 := rs (se 3 (by rfl) ⟨17984, by rfl⟩) (B 35969 (by norm_num) ⟨17984, by rfl⟩ (by norm_num))
theorem R63157 : Reach 63157 := rs (se 5 (by rfl) ⟨2960, by rfl⟩) (B 5921 (by norm_num) ⟨2960, by rfl⟩ (by norm_num))
theorem R95941 : Reach 95941 := rs (se 4 (by rfl) ⟨8994, by rfl⟩) (B 17989 (by norm_num) ⟨8994, by rfl⟩ (by norm_num))
theorem R128717 : Reach 128717 := rs (se 3 (by rfl) ⟨24134, by rfl⟩) (B 48269 (by norm_num) ⟨24134, by rfl⟩ (by norm_num))
theorem R980693 : Reach 980693 := rs (se 7 (by rfl) ⟨11492, by rfl⟩) (B 22985 (by norm_num) ⟨11492, by rfl⟩ (by norm_num))
theorem R63193 : Reach 63193 := rs (se 2 (by rfl) ⟨23697, by rfl⟩) (B 47395 (by norm_num) ⟨23697, by rfl⟩ (by norm_num))
theorem R63229 : Reach 63229 := rs (se 3 (by rfl) ⟨11855, by rfl⟩) (B 23711 (by norm_num) ⟨11855, by rfl⟩ (by norm_num))
theorem R96005 : Reach 96005 := rs (se 4 (by rfl) ⟨9000, by rfl⟩) (B 18001 (by norm_num) ⟨9000, by rfl⟩ (by norm_num))
theorem R128789 : Reach 128789 := rs (se 6 (by rfl) ⟨3018, by rfl⟩) (B 6037 (by norm_num) ⟨3018, by rfl⟩ (by norm_num))
theorem R63265 : Reach 63265 := rs (se 2 (by rfl) ⟨23724, by rfl⟩) (B 47449 (by norm_num) ⟨23724, by rfl⟩ (by norm_num))
theorem R63301 : Reach 63301 := rs (se 4 (by rfl) ⟨5934, by rfl⟩) (B 11869 (by norm_num) ⟨5934, by rfl⟩ (by norm_num))
theorem R128861 : Reach 128861 := rs (se 3 (by rfl) ⟨24161, by rfl⟩) (B 48323 (by norm_num) ⟨24161, by rfl⟩ (by norm_num))
theorem R63337 : Reach 63337 := rs (se 2 (by rfl) ⟨23751, by rfl⟩) (B 47503 (by norm_num) ⟨23751, by rfl⟩ (by norm_num))
theorem R63349 : Reach 63349 := rs (se 5 (by rfl) ⟨2969, by rfl⟩) (B 5939 (by norm_num) ⟨2969, by rfl⟩ (by norm_num))
theorem R96133 : Reach 96133 := rs (se 4 (by rfl) ⟨9012, by rfl⟩) (B 18025 (by norm_num) ⟨9012, by rfl⟩ (by norm_num))
theorem R63373 : Reach 63373 := rs (se 3 (by rfl) ⟨11882, by rfl⟩) (B 23765 (by norm_num) ⟨11882, by rfl⟩ (by norm_num))
theorem R194453 : Reach 194453 := rs (se 6 (by rfl) ⟨4557, by rfl⟩) (B 9115 (by norm_num) ⟨4557, by rfl⟩ (by norm_num))
theorem R128933 : Reach 128933 := rs (se 4 (by rfl) ⟨12087, by rfl⟩) (B 24175 (by norm_num) ⟨12087, by rfl⟩ (by norm_num))
theorem R63409 : Reach 63409 := rs (se 2 (by rfl) ⟨23778, by rfl⟩) (B 47557 (by norm_num) ⟨23778, by rfl⟩ (by norm_num))
theorem R63445 : Reach 63445 := rs (se 7 (by rfl) ⟨743, by rfl⟩) (B 1487 (by norm_num) ⟨743, by rfl⟩ (by norm_num))
theorem R96221 : Reach 96221 := rs (se 3 (by rfl) ⟨18041, by rfl⟩) (B 36083 (by norm_num) ⟨18041, by rfl⟩ (by norm_num))
theorem R129005 : Reach 129005 := rs (se 3 (by rfl) ⟨24188, by rfl⟩) (B 48377 (by norm_num) ⟨24188, by rfl⟩ (by norm_num))
theorem R63481 : Reach 63481 := rs (se 2 (by rfl) ⟨23805, by rfl⟩) (B 47611 (by norm_num) ⟨23805, by rfl⟩ (by norm_num))
theorem R63517 : Reach 63517 := rs (se 3 (by rfl) ⟨11909, by rfl⟩) (B 23819 (by norm_num) ⟨11909, by rfl⟩ (by norm_num))
theorem R129077 : Reach 129077 := rs (se 5 (by rfl) ⟨6050, by rfl⟩) (B 12101 (by norm_num) ⟨6050, by rfl⟩ (by norm_num))
theorem R63553 : Reach 63553 := rs (se 2 (by rfl) ⟨23832, by rfl⟩) (B 47665 (by norm_num) ⟨23832, by rfl⟩ (by norm_num))
theorem R96349 : Reach 96349 := rs (se 3 (by rfl) ⟨18065, by rfl⟩) (B 36131 (by norm_num) ⟨18065, by rfl⟩ (by norm_num))
theorem R63589 : Reach 63589 := rs (se 4 (by rfl) ⟨5961, by rfl⟩) (B 11923 (by norm_num) ⟨5961, by rfl⟩ (by norm_num))
theorem R129149 : Reach 129149 := rs (se 3 (by rfl) ⟨24215, by rfl⟩) (B 48431 (by norm_num) ⟨24215, by rfl⟩ (by norm_num))
theorem R63625 : Reach 63625 := rs (se 2 (by rfl) ⟨23859, by rfl⟩) (B 47719 (by norm_num) ⟨23859, by rfl⟩ (by norm_num))
theorem R63661 : Reach 63661 := rs (se 3 (by rfl) ⟨11936, by rfl⟩) (B 23873 (by norm_num) ⟨11936, by rfl⟩ (by norm_num))
theorem R96437 : Reach 96437 := rs (se 5 (by rfl) ⟨4520, by rfl⟩) (B 9041 (by norm_num) ⟨4520, by rfl⟩ (by norm_num))
theorem R129221 : Reach 129221 := rs (se 4 (by rfl) ⟨12114, by rfl⟩) (B 24229 (by norm_num) ⟨12114, by rfl⟩ (by norm_num))
theorem R63697 : Reach 63697 := rs (se 2 (by rfl) ⟨23886, by rfl⟩) (B 47773 (by norm_num) ⟨23886, by rfl⟩ (by norm_num))
theorem R63733 : Reach 63733 := rs (se 5 (by rfl) ⟨2987, by rfl⟩) (B 5975 (by norm_num) ⟨2987, by rfl⟩ (by norm_num))
theorem R129293 : Reach 129293 := rs (se 3 (by rfl) ⟨24242, by rfl⟩) (B 48485 (by norm_num) ⟨24242, by rfl⟩ (by norm_num))
theorem R63769 : Reach 63769 := rs (se 2 (by rfl) ⟨23913, by rfl⟩) (B 47827 (by norm_num) ⟨23913, by rfl⟩ (by norm_num))
theorem R96565 : Reach 96565 := rs (se 5 (by rfl) ⟨4526, by rfl⟩) (B 9053 (by norm_num) ⟨4526, by rfl⟩ (by norm_num))
theorem R162101 : Reach 162101 := rs (se 5 (by rfl) ⟨7598, by rfl⟩) (B 15197 (by norm_num) ⟨7598, by rfl⟩ (by norm_num))
theorem R260405 : Reach 260405 := rs (se 5 (by rfl) ⟨12206, by rfl⟩) (B 24413 (by norm_num) ⟨12206, by rfl⟩ (by norm_num))
theorem R63805 : Reach 63805 := rs (se 3 (by rfl) ⟨11963, by rfl⟩) (B 23927 (by norm_num) ⟨11963, by rfl⟩ (by norm_num))
theorem R194885 : Reach 194885 := rs (se 4 (by rfl) ⟨18270, by rfl⟩) (B 36541 (by norm_num) ⟨18270, by rfl⟩ (by norm_num))
theorem R424277 : Reach 424277 := rs (se 10 (by rfl) ⟨621, by rfl⟩) (B 1243 (by norm_num) ⟨621, by rfl⟩ (by norm_num))
theorem R129365 : Reach 129365 := rs (se 10 (by rfl) ⟨189, by rfl⟩) (B 379 (by norm_num) ⟨189, by rfl⟩ (by norm_num))
theorem R63841 : Reach 63841 := rs (se 2 (by rfl) ⟨23940, by rfl⟩) (B 47881 (by norm_num) ⟨23940, by rfl⟩ (by norm_num))
theorem R63877 : Reach 63877 := rs (se 4 (by rfl) ⟨5988, by rfl⟩) (B 11977 (by norm_num) ⟨5988, by rfl⟩ (by norm_num))
theorem R96653 : Reach 96653 := rs (se 3 (by rfl) ⟨18122, by rfl⟩) (B 36245 (by norm_num) ⟨18122, by rfl⟩ (by norm_num))
theorem R358805 : Reach 358805 := rs (se 6 (by rfl) ⟨8409, by rfl⟩) (B 16819 (by norm_num) ⟨8409, by rfl⟩ (by norm_num))
theorem R129437 : Reach 129437 := rs (se 3 (by rfl) ⟨24269, by rfl⟩) (B 48539 (by norm_num) ⟨24269, by rfl⟩ (by norm_num))
theorem R63913 : Reach 63913 := rs (se 2 (by rfl) ⟨23967, by rfl⟩) (B 47935 (by norm_num) ⟨23967, by rfl⟩ (by norm_num))
theorem R63949 : Reach 63949 := rs (se 3 (by rfl) ⟨11990, by rfl⟩) (B 23981 (by norm_num) ⟨11990, by rfl⟩ (by norm_num))
theorem R129509 : Reach 129509 := rs (se 4 (by rfl) ⟨12141, by rfl⟩) (B 24283 (by norm_num) ⟨12141, by rfl⟩ (by norm_num))
theorem R63985 : Reach 63985 := rs (se 2 (by rfl) ⟨23994, by rfl⟩) (B 47989 (by norm_num) ⟨23994, by rfl⟩ (by norm_num))
theorem R293381 : Reach 293381 := rs (se 4 (by rfl) ⟨27504, by rfl⟩) (B 55009 (by norm_num) ⟨27504, by rfl⟩ (by norm_num))
theorem R96781 : Reach 96781 := rs (se 3 (by rfl) ⟨18146, by rfl⟩) (B 36293 (by norm_num) ⟨18146, by rfl⟩ (by norm_num))
theorem R64021 : Reach 64021 := rs (se 6 (by rfl) ⟨1500, by rfl⟩) (B 3001 (by norm_num) ⟨1500, by rfl⟩ (by norm_num))
theorem R129581 : Reach 129581 := rs (se 3 (by rfl) ⟨24296, by rfl⟩) (B 48593 (by norm_num) ⟨24296, by rfl⟩ (by norm_num))
theorem R64057 : Reach 64057 := rs (se 2 (by rfl) ⟨24021, by rfl⟩) (B 48043 (by norm_num) ⟨24021, by rfl⟩ (by norm_num))
theorem R64093 : Reach 64093 := rs (se 3 (by rfl) ⟨12017, by rfl⟩) (B 24035 (by norm_num) ⟨12017, by rfl⟩ (by norm_num))
theorem R96869 : Reach 96869 := rs (se 4 (by rfl) ⟨9081, by rfl⟩) (B 18163 (by norm_num) ⟨9081, by rfl⟩ (by norm_num))
theorem R129653 : Reach 129653 := rs (se 5 (by rfl) ⟨6077, by rfl⟩) (B 12155 (by norm_num) ⟨6077, by rfl⟩ (by norm_num))
theorem R64129 : Reach 64129 := rs (se 2 (by rfl) ⟨24048, by rfl⟩) (B 48097 (by norm_num) ⟨24048, by rfl⟩ (by norm_num))
theorem R424597 : Reach 424597 := rs (se 6 (by rfl) ⟨9951, by rfl⟩) (B 19903 (by norm_num) ⟨9951, by rfl⟩ (by norm_num))
theorem R64165 : Reach 64165 := rs (se 4 (by rfl) ⟨6015, by rfl⟩) (B 12031 (by norm_num) ⟨6015, by rfl⟩ (by norm_num))
theorem R129725 : Reach 129725 := rs (se 3 (by rfl) ⟨24323, by rfl⟩) (B 48647 (by norm_num) ⟨24323, by rfl⟩ (by norm_num))
theorem R64201 : Reach 64201 := rs (se 2 (by rfl) ⟨24075, by rfl⟩) (B 48151 (by norm_num) ⟨24075, by rfl⟩ (by norm_num))
theorem R96997 : Reach 96997 := rs (se 4 (by rfl) ⟨9093, by rfl⟩) (B 18187 (by norm_num) ⟨9093, by rfl⟩ (by norm_num))
theorem R64237 : Reach 64237 := rs (se 3 (by rfl) ⟨12044, by rfl⟩) (B 24089 (by norm_num) ⟨12044, by rfl⟩ (by norm_num))
theorem R195317 : Reach 195317 := rs (se 5 (by rfl) ⟨9155, by rfl⟩) (B 18311 (by norm_num) ⟨9155, by rfl⟩ (by norm_num))
theorem R129797 : Reach 129797 := rs (se 4 (by rfl) ⟨12168, by rfl⟩) (B 24337 (by norm_num) ⟨12168, by rfl⟩ (by norm_num))
theorem R64273 : Reach 64273 := rs (se 2 (by rfl) ⟨24102, by rfl⟩) (B 48205 (by norm_num) ⟨24102, by rfl⟩ (by norm_num))
theorem R64309 : Reach 64309 := rs (se 5 (by rfl) ⟨3014, by rfl⟩) (B 6029 (by norm_num) ⟨3014, by rfl⟩ (by norm_num))
theorem R97085 : Reach 97085 := rs (se 3 (by rfl) ⟨18203, by rfl⟩) (B 36407 (by norm_num) ⟨18203, by rfl⟩ (by norm_num))
theorem R129869 : Reach 129869 := rs (se 3 (by rfl) ⟨24350, by rfl⟩) (B 48701 (by norm_num) ⟨24350, by rfl⟩ (by norm_num))
theorem R64345 : Reach 64345 := rs (se 2 (by rfl) ⟨24129, by rfl⟩) (B 48259 (by norm_num) ⟨24129, by rfl⟩ (by norm_num))
theorem R555893 : Reach 555893 := rs (se 5 (by rfl) ⟨26057, by rfl⟩) (B 52115 (by norm_num) ⟨26057, by rfl⟩ (by norm_num))
theorem R64381 : Reach 64381 := rs (se 3 (by rfl) ⟨12071, by rfl⟩) (B 24143 (by norm_num) ⟨12071, by rfl⟩ (by norm_num))
theorem R719765 : Reach 719765 := rs (se 6 (by rfl) ⟨16869, by rfl⟩) (B 33739 (by norm_num) ⟨16869, by rfl⟩ (by norm_num))
theorem R129941 : Reach 129941 := rs (se 6 (by rfl) ⟨3045, by rfl⟩) (B 6091 (by norm_num) ⟨3045, by rfl⟩ (by norm_num))
theorem R64417 : Reach 64417 := rs (se 2 (by rfl) ⟨24156, by rfl⟩) (B 48313 (by norm_num) ⟨24156, by rfl⟩ (by norm_num))
theorem R97213 : Reach 97213 := rs (se 3 (by rfl) ⟨18227, by rfl⟩) (B 36455 (by norm_num) ⟨18227, by rfl⟩ (by norm_num))
theorem R64453 : Reach 64453 := rs (se 4 (by rfl) ⟨6042, by rfl⟩) (B 12085 (by norm_num) ⟨6042, by rfl⟩ (by norm_num))
theorem R162773 : Reach 162773 := rs (se 7 (by rfl) ⟨1907, by rfl⟩) (B 3815 (by norm_num) ⟨1907, by rfl⟩ (by norm_num))
theorem R130013 : Reach 130013 := rs (se 3 (by rfl) ⟨24377, by rfl⟩) (B 48755 (by norm_num) ⟨24377, by rfl⟩ (by norm_num))
theorem R64489 : Reach 64489 := rs (se 2 (by rfl) ⟨24183, by rfl⟩) (B 48367 (by norm_num) ⟨24183, by rfl⟩ (by norm_num))
theorem R64525 : Reach 64525 := rs (se 3 (by rfl) ⟨12098, by rfl⟩) (B 24197 (by norm_num) ⟨12098, by rfl⟩ (by norm_num))
theorem R97301 : Reach 97301 := rs (se 6 (by rfl) ⟨2280, by rfl⟩) (B 4561 (by norm_num) ⟨2280, by rfl⟩ (by norm_num))
theorem R130085 : Reach 130085 := rs (se 4 (by rfl) ⟨12195, by rfl⟩) (B 24391 (by norm_num) ⟨12195, by rfl⟩ (by norm_num))
theorem R64561 : Reach 64561 := rs (se 2 (by rfl) ⟨24210, by rfl⟩) (B 48421 (by norm_num) ⟨24210, by rfl⟩ (by norm_num))
theorem R64597 : Reach 64597 := rs (se 8 (by rfl) ⟨378, by rfl⟩) (B 757 (by norm_num) ⟨378, by rfl⟩ (by norm_num))
theorem R130157 : Reach 130157 := rs (se 3 (by rfl) ⟨24404, by rfl⟩) (B 48809 (by norm_num) ⟨24404, by rfl⟩ (by norm_num))
theorem R64633 : Reach 64633 := rs (se 2 (by rfl) ⟨24237, by rfl⟩) (B 48475 (by norm_num) ⟨24237, by rfl⟩ (by norm_num))
theorem R97429 : Reach 97429 := rs (se 6 (by rfl) ⟨2283, by rfl⟩) (B 4567 (by norm_num) ⟨2283, by rfl⟩ (by norm_num))
theorem R64669 : Reach 64669 := rs (se 3 (by rfl) ⟨12125, by rfl⟩) (B 24251 (by norm_num) ⟨12125, by rfl⟩ (by norm_num))
theorem R195749 : Reach 195749 := rs (se 4 (by rfl) ⟨18351, by rfl⟩) (B 36703 (by norm_num) ⟨18351, by rfl⟩ (by norm_num))
theorem R130229 : Reach 130229 := rs (se 5 (by rfl) ⟨6104, by rfl⟩) (B 12209 (by norm_num) ⟨6104, by rfl⟩ (by norm_num))
theorem R64705 : Reach 64705 := rs (se 2 (by rfl) ⟨24264, by rfl⟩) (B 48529 (by norm_num) ⟨24264, by rfl⟩ (by norm_num))
theorem R64741 : Reach 64741 := rs (se 4 (by rfl) ⟨6069, by rfl⟩) (B 12139 (by norm_num) ⟨6069, by rfl⟩ (by norm_num))
theorem R97517 : Reach 97517 := rs (se 3 (by rfl) ⟨18284, by rfl⟩) (B 36569 (by norm_num) ⟨18284, by rfl⟩ (by norm_num))
theorem R130301 : Reach 130301 := rs (se 3 (by rfl) ⟨24431, by rfl⟩) (B 48863 (by norm_num) ⟨24431, by rfl⟩ (by norm_num))
theorem R64777 : Reach 64777 := rs (se 2 (by rfl) ⟨24291, by rfl⟩) (B 48583 (by norm_num) ⟨24291, by rfl⟩ (by norm_num))
theorem R130349 : Reach 130349 := rs (se 3 (by rfl) ⟨24440, by rfl⟩) (B 48881 (by norm_num) ⟨24440, by rfl⟩ (by norm_num))
theorem R64813 : Reach 64813 := rs (se 3 (by rfl) ⟨12152, by rfl⟩) (B 24305 (by norm_num) ⟨12152, by rfl⟩ (by norm_num))
theorem R130373 : Reach 130373 := rs (se 4 (by rfl) ⟨12222, by rfl⟩) (B 24445 (by norm_num) ⟨12222, by rfl⟩ (by norm_num))
theorem R64849 : Reach 64849 := rs (se 2 (by rfl) ⟨24318, by rfl⟩) (B 48637 (by norm_num) ⟨24318, by rfl⟩ (by norm_num))
theorem R97645 : Reach 97645 := rs (se 3 (by rfl) ⟨18308, by rfl⟩) (B 36617 (by norm_num) ⟨18308, by rfl⟩ (by norm_num))
theorem R64885 : Reach 64885 := rs (se 5 (by rfl) ⟨3041, by rfl⟩) (B 6083 (by norm_num) ⟨3041, by rfl⟩ (by norm_num))
theorem R163205 : Reach 163205 := rs (se 4 (by rfl) ⟨15300, by rfl⟩) (B 30601 (by norm_num) ⟨15300, by rfl⟩ (by norm_num))
theorem R130445 : Reach 130445 := rs (se 3 (by rfl) ⟨24458, by rfl⟩) (B 48917 (by norm_num) ⟨24458, by rfl⟩ (by norm_num))
theorem R64921 : Reach 64921 := rs (se 2 (by rfl) ⟨24345, by rfl⟩) (B 48691 (by norm_num) ⟨24345, by rfl⟩ (by norm_num))
theorem R64957 : Reach 64957 := rs (se 3 (by rfl) ⟨12179, by rfl⟩) (B 24359 (by norm_num) ⟨12179, by rfl⟩ (by norm_num))
theorem R97733 : Reach 97733 := rs (se 4 (by rfl) ⟨9162, by rfl⟩) (B 18325 (by norm_num) ⟨9162, by rfl⟩ (by norm_num))
theorem R261589 : Reach 261589 := rs (se 7 (by rfl) ⟨3065, by rfl⟩) (B 6131 (by norm_num) ⟨3065, by rfl⟩ (by norm_num))
theorem R130517 : Reach 130517 := rs (se 7 (by rfl) ⟨1529, by rfl⟩) (B 3059 (by norm_num) ⟨1529, by rfl⟩ (by norm_num))
theorem R64993 : Reach 64993 := rs (se 2 (by rfl) ⟨24372, by rfl⟩) (B 48745 (by norm_num) ⟨24372, by rfl⟩ (by norm_num))
theorem R65029 : Reach 65029 := rs (se 4 (by rfl) ⟨6096, by rfl⟩) (B 12193 (by norm_num) ⟨6096, by rfl⟩ (by norm_num))
theorem R130589 : Reach 130589 := rs (se 3 (by rfl) ⟨24485, by rfl⟩) (B 48971 (by norm_num) ⟨24485, by rfl⟩ (by norm_num))
theorem R65065 : Reach 65065 := rs (se 2 (by rfl) ⟨24399, by rfl⟩) (B 48799 (by norm_num) ⟨24399, by rfl⟩ (by norm_num))
theorem R261701 : Reach 261701 := rs (se 4 (by rfl) ⟨24534, by rfl⟩) (B 49069 (by norm_num) ⟨24534, by rfl⟩ (by norm_num))
theorem R97861 : Reach 97861 := rs (se 4 (by rfl) ⟨9174, by rfl⟩) (B 18349 (by norm_num) ⟨9174, by rfl⟩ (by norm_num))
theorem R65101 : Reach 65101 := rs (se 3 (by rfl) ⟨12206, by rfl⟩) (B 24413 (by norm_num) ⟨12206, by rfl⟩ (by norm_num))
theorem R196181 : Reach 196181 := rs (se 8 (by rfl) ⟨1149, by rfl⟩) (B 2299 (by norm_num) ⟨1149, by rfl⟩ (by norm_num))
theorem R130661 : Reach 130661 := rs (se 4 (by rfl) ⟨12249, by rfl⟩) (B 24499 (by norm_num) ⟨12249, by rfl⟩ (by norm_num))
theorem R65137 : Reach 65137 := rs (se 2 (by rfl) ⟨24426, by rfl⟩) (B 48853 (by norm_num) ⟨24426, by rfl⟩ (by norm_num))
theorem R65173 : Reach 65173 := rs (se 6 (by rfl) ⟨1527, by rfl⟩) (B 3055 (by norm_num) ⟨1527, by rfl⟩ (by norm_num))
theorem R97949 : Reach 97949 := rs (se 3 (by rfl) ⟨18365, by rfl⟩) (B 36731 (by norm_num) ⟨18365, by rfl⟩ (by norm_num))
theorem R130733 : Reach 130733 := rs (se 3 (by rfl) ⟨24512, by rfl⟩) (B 49025 (by norm_num) ⟨24512, by rfl⟩ (by norm_num))
theorem R65209 : Reach 65209 := rs (se 2 (by rfl) ⟨24453, by rfl⟩) (B 48907 (by norm_num) ⟨24453, by rfl⟩ (by norm_num))
theorem R65245 : Reach 65245 := rs (se 3 (by rfl) ⟨12233, by rfl⟩) (B 24467 (by norm_num) ⟨12233, by rfl⟩ (by norm_num))
theorem R130805 : Reach 130805 := rs (se 5 (by rfl) ⟨6131, by rfl⟩) (B 12263 (by norm_num) ⟨6131, by rfl⟩ (by norm_num))
theorem R65281 : Reach 65281 := rs (se 2 (by rfl) ⟨24480, by rfl⟩) (B 48961 (by norm_num) ⟨24480, by rfl⟩ (by norm_num))
theorem R294677 : Reach 294677 := rs (se 6 (by rfl) ⟨6906, by rfl⟩) (B 13813 (by norm_num) ⟨6906, by rfl⟩ (by norm_num))
theorem R98077 : Reach 98077 := rs (se 3 (by rfl) ⟨18389, by rfl⟩) (B 36779 (by norm_num) ⟨18389, by rfl⟩ (by norm_num))
theorem R65317 : Reach 65317 := rs (se 4 (by rfl) ⟨6123, by rfl⟩) (B 12247 (by norm_num) ⟨6123, by rfl⟩ (by norm_num))
theorem R130877 : Reach 130877 := rs (se 3 (by rfl) ⟨24539, by rfl⟩) (B 49079 (by norm_num) ⟨24539, by rfl⟩ (by norm_num))
theorem R65353 : Reach 65353 := rs (se 2 (by rfl) ⟨24507, by rfl⟩) (B 49015 (by norm_num) ⟨24507, by rfl⟩ (by norm_num))
theorem R65389 : Reach 65389 := rs (se 3 (by rfl) ⟨12260, by rfl⟩) (B 24521 (by norm_num) ⟨12260, by rfl⟩ (by norm_num))
theorem R98165 : Reach 98165 := rs (se 5 (by rfl) ⟨4601, by rfl⟩) (B 9203 (by norm_num) ⟨4601, by rfl⟩ (by norm_num))
theorem R130949 : Reach 130949 := rs (se 4 (by rfl) ⟨12276, by rfl⟩) (B 24553 (by norm_num) ⟨12276, by rfl⟩ (by norm_num))
theorem R65425 : Reach 65425 := rs (se 2 (by rfl) ⟨24534, by rfl⟩) (B 49069 (by norm_num) ⟨24534, by rfl⟩ (by norm_num))
theorem R65461 : Reach 65461 := rs (se 5 (by rfl) ⟨3068, by rfl⟩) (B 6137 (by norm_num) ⟨3068, by rfl⟩ (by norm_num))
theorem R131021 : Reach 131021 := rs (se 3 (by rfl) ⟨24566, by rfl⟩) (B 49133 (by norm_num) ⟨24566, by rfl⟩ (by norm_num))
theorem R65497 : Reach 65497 := rs (se 2 (by rfl) ⟨24561, by rfl⟩) (B 49123 (by norm_num) ⟨24561, by rfl⟩ (by norm_num))
theorem R98293 : Reach 98293 := rs (se 5 (by rfl) ⟨4607, by rfl⟩) (B 9215 (by norm_num) ⟨4607, by rfl⟩ (by norm_num))
theorem R65539 : Reach 65539 := rs (se 1 (by rfl) ⟨49154, by rfl⟩) R98309
theorem R131075 : Reach 131075 := rs (se 1 (by rfl) ⟨98306, by rfl⟩) R196613
theorem R327685 : Reach 327685 := rs (se 4 (by rfl) ⟨30720, by rfl⟩) R61441
theorem R163889 : Reach 163889 := rs (se 2 (by rfl) ⟨61458, by rfl⟩) R122917
theorem R65587 : Reach 65587 := rs (se 1 (by rfl) ⟨49190, by rfl⟩) R98381
theorem R196721 : Reach 196721 := rs (se 2 (by rfl) ⟨73770, by rfl⟩) R147541
theorem R98435 : Reach 98435 := rs (se 1 (by rfl) ⟨73826, by rfl⟩) R147653
theorem R65731 : Reach 65731 := rs (se 1 (by rfl) ⟨49298, by rfl⟩) R98597
theorem R1474757 : Reach 1474757 := rs (se 4 (by rfl) ⟨138258, by rfl⟩) R276517
theorem R98563 : Reach 98563 := rs (se 1 (by rfl) ⟨73922, by rfl⟩) R147845
theorem R131345 : Reach 131345 := rs (se 2 (by rfl) ⟨49254, by rfl⟩) R98509
theorem R131363 : Reach 131363 := rs (se 1 (by rfl) ⟨98522, by rfl⟩) R197045
theorem R65875 : Reach 65875 := rs (se 1 (by rfl) ⟨49406, by rfl⟩) R98813
theorem R98705 : Reach 98705 := rs (se 2 (by rfl) ⟨37014, by rfl⟩) R74029
theorem R66019 : Reach 66019 := rs (se 1 (by rfl) ⟨49514, by rfl⟩) R99029
theorem R98833 : Reach 98833 := rs (se 2 (by rfl) ⟨37062, by rfl⟩) R74125
theorem R131633 : Reach 131633 := rs (se 2 (by rfl) ⟨49362, by rfl⟩) R98725
theorem R131651 : Reach 131651 := rs (se 1 (by rfl) ⟨98738, by rfl⟩) R197477
theorem R361037 : Reach 361037 := rs (se 3 (by rfl) ⟨67694, by rfl⟩) R135389
theorem R66163 : Reach 66163 := rs (se 1 (by rfl) ⟨49622, by rfl⟩) R99245
theorem R197261 : Reach 197261 := rs (se 3 (by rfl) ⟨36986, by rfl⟩) R73973
theorem R656099 : Reach 656099 := rs (se 1 (by rfl) ⟨492074, by rfl⟩) R984149
theorem R525041 : Reach 525041 := rs (se 2 (by rfl) ⟨196890, by rfl⟩) R393781
theorem R66307 : Reach 66307 := rs (se 1 (by rfl) ⟨49730, by rfl⟩) R99461
theorem R131921 : Reach 131921 := rs (se 2 (by rfl) ⟨49470, by rfl⟩) R98941
theorem R131939 : Reach 131939 := rs (se 1 (by rfl) ⟨98954, by rfl⟩) R197909
theorem R66451 : Reach 66451 := rs (se 1 (by rfl) ⟨49838, by rfl⟩) R99677
theorem R99299 : Reach 99299 := rs (se 1 (by rfl) ⟨74474, by rfl⟩) R148949
theorem R164845 : Reach 164845 := rs (se 3 (by rfl) ⟨30908, by rfl⟩) R61817
theorem R99427 : Reach 99427 := rs (se 1 (by rfl) ⟨74570, by rfl⟩) R149141
theorem R132209 : Reach 132209 := rs (se 2 (by rfl) ⟨49578, by rfl⟩) R99157
theorem R132227 : Reach 132227 := rs (se 1 (by rfl) ⟨99170, by rfl⟩) R198341
theorem R165073 : Reach 165073 := rs (se 2 (by rfl) ⟨61902, by rfl⟩) R123805
theorem R230627 : Reach 230627 := rs (se 1 (by rfl) ⟨172970, by rfl⟩) R345941
theorem R99569 : Reach 99569 := rs (se 2 (by rfl) ⟨37338, by rfl⟩) R74677
theorem R99697 : Reach 99697 := rs (se 2 (by rfl) ⟨37386, by rfl⟩) R74773
theorem R165233 : Reach 165233 := rs (se 2 (by rfl) ⟨61962, by rfl⟩) R123925
theorem R132497 : Reach 132497 := rs (se 2 (by rfl) ⟨49686, by rfl⟩) R99373
theorem R132515 : Reach 132515 := rs (se 1 (by rfl) ⟨99386, by rfl⟩) R198773
theorem R165347 : Reach 165347 := rs (se 1 (by rfl) ⟨124010, by rfl⟩) R248021
theorem R198179 : Reach 198179 := rs (se 1 (by rfl) ⟨148634, by rfl⟩) R297269
theorem R132707 : Reach 132707 := rs (se 1 (by rfl) ⟨99530, by rfl⟩) R199061
theorem R67171 : Reach 67171 := rs (se 1 (by rfl) ⟨50378, by rfl⟩) R100757
theorem R132785 : Reach 132785 := rs (se 2 (by rfl) ⟨49794, by rfl⟩) R99589
theorem R132803 : Reach 132803 := rs (se 1 (by rfl) ⟨99602, by rfl⟩) R199205
theorem R198449 : Reach 198449 := rs (se 2 (by rfl) ⟨74418, by rfl⟩) R148837
theorem R132977 : Reach 132977 := rs (se 2 (by rfl) ⟨49866, by rfl⟩) R99733
theorem R329669 : Reach 329669 := rs (se 4 (by rfl) ⟨30906, by rfl⟩) R61813
theorem R296945 : Reach 296945 := rs (se 2 (by rfl) ⟨111354, by rfl⟩) R222709
theorem R67699 : Reach 67699 := rs (se 1 (by rfl) ⟨50774, by rfl⟩) R101549
theorem R133265 : Reach 133265 := rs (se 2 (by rfl) ⟨49974, by rfl⟩) R99949
theorem R198989 : Reach 198989 := rs (se 3 (by rfl) ⟨37310, by rfl⟩) R74621
theorem R166349 : Reach 166349 := rs (se 3 (by rfl) ⟨31190, by rfl⟩) R62381
theorem R166531 : Reach 166531 := rs (se 1 (by rfl) ⟨124898, by rfl⟩) R249797
theorem R166691 : Reach 166691 := rs (se 1 (by rfl) ⟨125018, by rfl⟩) R250037
theorem R199523 : Reach 199523 := rs (se 1 (by rfl) ⟨149642, by rfl⟩) R299285
theorem R298403 : Reach 298403 := rs (se 1 (by rfl) ⟨223802, by rfl⟩) R447605
theorem R298565 : Reach 298565 := rs (se 4 (by rfl) ⟨27990, by rfl⟩) R55981
theorem R659141 : Reach 659141 := rs (se 4 (by rfl) ⟨61794, by rfl⟩) R123589
theorem R167761 : Reach 167761 := rs (se 2 (by rfl) ⟨62910, by rfl⟩) R125821
theorem R102385 : Reach 102385 := rs (se 2 (by rfl) ⟨38394, by rfl⟩) R76789
theorem R495629 : Reach 495629 := rs (se 3 (by rfl) ⟨92930, by rfl⟩) R185861
theorem R299213 : Reach 299213 := rs (se 3 (by rfl) ⟨56102, by rfl⟩) R112205
theorem R69923 : Reach 69923 := rs (se 1 (by rfl) ⟨52442, by rfl⟩) R104885
theorem R266723 : Reach 266723 := rs (se 1 (by rfl) ⟨200042, by rfl⟩) R400085
theorem R135697 : Reach 135697 := rs (se 2 (by rfl) ⟨50886, by rfl⟩) R101773
theorem R201457 : Reach 201457 := rs (se 2 (by rfl) ⟨75546, by rfl⟩) R151093
theorem R2036501 : Reach 2036501 := rs (se 6 (by rfl) ⟨47730, by rfl⟩) R95461
theorem R103331 : Reach 103331 := rs (se 1 (by rfl) ⟨77498, by rfl⟩) R154997
theorem R70627 : Reach 70627 := rs (se 1 (by rfl) ⟨52970, by rfl⟩) R105941
theorem R70723 : Reach 70723 := rs (se 1 (by rfl) ⟨53042, by rfl⟩) R106085
theorem R103619 : Reach 103619 := rs (se 1 (by rfl) ⟨77714, by rfl⟩) R155429
theorem R71219 : Reach 71219 := rs (se 1 (by rfl) ⟨53414, by rfl⟩) R106829
theorem R333517 : Reach 333517 := rs (se 3 (by rfl) ⟨62534, by rfl⟩) R125069
theorem R104593 : Reach 104593 := rs (se 2 (by rfl) ⟨39222, by rfl⟩) R78445
theorem R71923 : Reach 71923 := rs (se 1 (by rfl) ⟨53942, by rfl⟩) R107885
theorem R104771 : Reach 104771 := rs (se 1 (by rfl) ⟨78578, by rfl⟩) R157157
theorem R72019 : Reach 72019 := rs (se 1 (by rfl) ⟨54014, by rfl⟩) R108029
theorem R268721 : Reach 268721 := rs (se 2 (by rfl) ⟨100770, by rfl⟩) R201541
theorem R72515 : Reach 72515 := rs (se 1 (by rfl) ⟨54386, by rfl⟩) R108773
theorem R465763 : Reach 465763 := rs (se 1 (by rfl) ⟨349322, by rfl⟩) R698645
theorem R269347 : Reach 269347 := rs (se 1 (by rfl) ⟨202010, by rfl⟩) R404021
theorem R105553 : Reach 105553 := rs (se 2 (by rfl) ⟨39582, by rfl⟩) R79165
theorem R269411 : Reach 269411 := rs (se 1 (by rfl) ⟨202058, by rfl⟩) R404117
theorem R72947 : Reach 72947 := rs (se 1 (by rfl) ⟨54710, by rfl⟩) R109421
theorem R335117 : Reach 335117 := rs (se 3 (by rfl) ⟨62834, by rfl⟩) R125669
theorem R73219 : Reach 73219 := rs (se 1 (by rfl) ⟨54914, by rfl⟩) R109829
theorem R73235 : Reach 73235 := rs (se 1 (by rfl) ⟨54926, by rfl⟩) R109853
theorem R106019 : Reach 106019 := rs (se 1 (by rfl) ⟨79514, by rfl⟩) R159029
theorem R73315 : Reach 73315 := rs (se 1 (by rfl) ⟨54986, by rfl⟩) R109973
theorem R335501 : Reach 335501 := rs (se 3 (by rfl) ⟨62906, by rfl⟩) R125813
theorem R204643 : Reach 204643 := rs (se 1 (by rfl) ⟨153482, by rfl⟩) R306965
theorem R73649 : Reach 73649 := rs (se 2 (by rfl) ⟨27618, by rfl⟩) R55237
theorem R73811 : Reach 73811 := rs (se 1 (by rfl) ⟨55358, by rfl⟩) R110717
theorem R106609 : Reach 106609 := rs (se 2 (by rfl) ⟨39978, by rfl⟩) R79957
theorem R73891 : Reach 73891 := rs (se 1 (by rfl) ⟨55418, by rfl⟩) R110837
theorem R139619 : Reach 139619 := rs (se 1 (by rfl) ⟨104714, by rfl⟩) R209429
theorem R139715 : Reach 139715 := rs (se 1 (by rfl) ⟨104786, by rfl⟩) R209573
theorem R107011 : Reach 107011 := rs (se 1 (by rfl) ⟨80258, by rfl⟩) R160517
theorem R107057 : Reach 107057 := rs (se 2 (by rfl) ⟨40146, by rfl⟩) R80293
theorem R336433 : Reach 336433 := rs (se 2 (by rfl) ⟨126162, by rfl⟩) R252325
theorem R74353 : Reach 74353 := rs (se 2 (by rfl) ⟨27882, by rfl⟩) R55765
theorem R139907 : Reach 139907 := rs (se 1 (by rfl) ⟨104930, by rfl⟩) R209861
theorem R74449 : Reach 74449 := rs (se 2 (by rfl) ⟨27918, by rfl⟩) R55837
theorem R74515 : Reach 74515 := rs (se 1 (by rfl) ⟨55886, by rfl⟩) R111773
theorem R271181 : Reach 271181 := rs (se 3 (by rfl) ⟨50846, by rfl⟩) R101693
theorem R107345 : Reach 107345 := rs (se 2 (by rfl) ⟨40254, by rfl⟩) R80509
theorem R369521 : Reach 369521 := rs (se 2 (by rfl) ⟨138570, by rfl⟩) R277141
theorem R566129 : Reach 566129 := rs (se 2 (by rfl) ⟨212298, by rfl⟩) R424597
theorem R74611 : Reach 74611 := rs (se 1 (by rfl) ⟨55958, by rfl⟩) R111917
theorem R271565 : Reach 271565 := rs (se 3 (by rfl) ⟨50918, by rfl⟩) R101837
theorem R173603 : Reach 173603 := rs (se 1 (by rfl) ⟨130202, by rfl⟩) R260405
theorem R108067 : Reach 108067 := rs (se 1 (by rfl) ⟨81050, by rfl⟩) R162101
theorem R140849 : Reach 140849 := rs (se 2 (by rfl) ⟨52818, by rfl⟩) R105637
theorem R140899 : Reach 140899 := rs (se 1 (by rfl) ⟨105674, by rfl⟩) R211349
theorem R239203 : Reach 239203 := rs (se 1 (by rfl) ⟨179402, by rfl⟩) R358805
theorem R141041 : Reach 141041 := rs (se 2 (by rfl) ⟨52890, by rfl⟩) R105781
theorem R370595 : Reach 370595 := rs (se 1 (by rfl) ⟨277946, by rfl⟩) R555893
theorem R337841 : Reach 337841 := rs (se 2 (by rfl) ⟨126690, by rfl⟩) R253381
theorem R337861 : Reach 337861 := rs (se 4 (by rfl) ⟨31674, by rfl⟩) R63349
theorem R108515 : Reach 108515 := rs (se 1 (by rfl) ⟨81386, by rfl⟩) R162773
theorem R108803 : Reach 108803 := rs (se 1 (by rfl) ⟨81602, by rfl⟩) R163205
theorem R76097 : Reach 76097 := rs (se 2 (by rfl) ⟨28536, by rfl⟩) R57073
theorem R174467 : Reach 174467 := rs (se 1 (by rfl) ⟨130850, by rfl⟩) R261701
theorem R76259 : Reach 76259 := rs (se 1 (by rfl) ⟨57194, by rfl⟩) R114389
theorem R76291 : Reach 76291 := rs (se 1 (by rfl) ⟨57218, by rfl⟩) R114437
theorem R142033 : Reach 142033 := rs (se 2 (by rfl) ⟨53262, by rfl⟩) R106525
theorem R142289 : Reach 142289 := rs (se 2 (by rfl) ⟨53358, by rfl⟩) R106717
theorem R142307 : Reach 142307 := rs (se 1 (by rfl) ⟨106730, by rfl⟩) R213461
theorem R109667 : Reach 109667 := rs (se 1 (by rfl) ⟨82250, by rfl⟩) R164501
theorem R207971 : Reach 207971 := rs (se 1 (by rfl) ⟨155978, by rfl⟩) R311957
theorem R142499 : Reach 142499 := rs (se 1 (by rfl) ⟨106874, by rfl⟩) R213749
theorem R109745 : Reach 109745 := rs (se 2 (by rfl) ⟨41154, by rfl⟩) R82309
theorem R208433 : Reach 208433 := rs (se 2 (by rfl) ⟨78162, by rfl⟩) R156325
theorem R667277 : Reach 667277 := rs (se 3 (by rfl) ⟨125114, by rfl⟩) R250229
theorem R143153 : Reach 143153 := rs (se 2 (by rfl) ⟨53682, by rfl⟩) R107365
theorem R241649 : Reach 241649 := rs (se 2 (by rfl) ⟨90618, by rfl⟩) R181237
theorem R77827 : Reach 77827 := rs (se 1 (by rfl) ⟨58370, by rfl⟩) R116741
theorem R110641 : Reach 110641 := rs (se 2 (by rfl) ⟨41490, by rfl⟩) R82981
theorem R110659 : Reach 110659 := rs (se 1 (by rfl) ⟨82994, by rfl⟩) R165989
theorem R143441 : Reach 143441 := rs (se 2 (by rfl) ⟨53790, by rfl⟩) R107581
theorem R438371 : Reach 438371 := rs (se 1 (by rfl) ⟨328778, by rfl⟩) R657557
theorem R143491 : Reach 143491 := rs (se 1 (by rfl) ⟨107618, by rfl⟩) R215237
theorem R110801 : Reach 110801 := rs (se 2 (by rfl) ⟨41550, by rfl⟩) R83101
theorem R143633 : Reach 143633 := rs (se 2 (by rfl) ⟨53862, by rfl⟩) R107725
theorem R111203 : Reach 111203 := rs (se 1 (by rfl) ⟨83402, by rfl⟩) R166805
theorem R78499 : Reach 78499 := rs (se 1 (by rfl) ⟨58874, by rfl⟩) R117749
theorem R176867 : Reach 176867 := rs (se 1 (by rfl) ⟨132650, by rfl⟩) R265301
theorem R209891 : Reach 209891 := rs (se 1 (by rfl) ⟨157418, by rfl⟩) R314837
theorem R177137 : Reach 177137 := rs (se 2 (by rfl) ⟨66426, by rfl⟩) R132853
theorem R78835 : Reach 78835 := rs (se 1 (by rfl) ⟨59126, by rfl⟩) R118253
theorem R177265 : Reach 177265 := rs (se 2 (by rfl) ⟨66474, by rfl⟩) R132949
theorem R144625 : Reach 144625 := rs (se 2 (by rfl) ⟨54234, by rfl⟩) R108469
theorem R112099 : Reach 112099 := rs (se 1 (by rfl) ⟨84074, by rfl⟩) R168149
theorem R341489 : Reach 341489 := rs (se 2 (by rfl) ⟨128058, by rfl⟩) R256117
theorem R144899 : Reach 144899 := rs (se 1 (by rfl) ⟨108674, by rfl⟩) R217349
theorem R79393 : Reach 79393 := rs (se 2 (by rfl) ⟨29772, by rfl⟩) R59545
theorem R79427 : Reach 79427 := rs (se 1 (by rfl) ⟨59570, by rfl⟩) R119141
theorem R374341 : Reach 374341 := rs (se 4 (by rfl) ⟨35094, by rfl⟩) R70189
theorem R210545 : Reach 210545 := rs (se 2 (by rfl) ⟨78954, by rfl⟩) R157909
theorem R145091 : Reach 145091 := rs (se 1 (by rfl) ⟨108818, by rfl⟩) R217637
theorem R308933 : Reach 308933 := rs (se 4 (by rfl) ⟨28962, by rfl⟩) R57925
theorem R767843 : Reach 767843 := rs (se 1 (by rfl) ⟨575882, by rfl⟩) R1151765
theorem R538595 : Reach 538595 := rs (se 1 (by rfl) ⟨403946, by rfl⟩) R807893
theorem R374797 : Reach 374797 := rs (se 3 (by rfl) ⟨70274, by rfl⟩) R140549
theorem R79985 : Reach 79985 := rs (se 2 (by rfl) ⟨29994, by rfl⟩) R59989
theorem R407693 : Reach 407693 := rs (se 3 (by rfl) ⟨76442, by rfl⟩) R152885
theorem R80065 : Reach 80065 := rs (se 2 (by rfl) ⟨30024, by rfl⟩) R60049
theorem R473485 : Reach 473485 := rs (se 3 (by rfl) ⟨88778, by rfl⟩) R177557
theorem R146033 : Reach 146033 := rs (se 2 (by rfl) ⟨54762, by rfl⟩) R109525
theorem R146083 : Reach 146083 := rs (se 1 (by rfl) ⟨109562, by rfl⟩) R219125
theorem R211661 : Reach 211661 := rs (se 3 (by rfl) ⟨39686, by rfl⟩) R79373
theorem R211747 : Reach 211747 := rs (se 1 (by rfl) ⟨158810, by rfl⟩) R317621
theorem R146225 : Reach 146225 := rs (se 2 (by rfl) ⟨54834, by rfl⟩) R109669
theorem R1063793 : Reach 1063793 := rs (se 2 (by rfl) ⟨398922, by rfl⟩) R797845
theorem R277453 : Reach 277453 := rs (se 3 (by rfl) ⟨52022, by rfl⟩) R104045
theorem R80851 : Reach 80851 := rs (se 1 (by rfl) ⟨60638, by rfl⟩) R121277
theorem R212003 : Reach 212003 := rs (se 1 (by rfl) ⟨159002, by rfl⟩) R318005
theorem R212017 : Reach 212017 := rs (se 2 (by rfl) ⟨79506, by rfl⟩) R159013
theorem R80995 : Reach 80995 := rs (se 1 (by rfl) ⟨60746, by rfl⟩) R121493
theorem R2243861 : Reach 2243861 := rs (se 6 (by rfl) ⟨52590, by rfl⟩) R105181
theorem R179597 : Reach 179597 := rs (se 3 (by rfl) ⟨33674, by rfl⟩) R67349
theorem R81329 : Reach 81329 := rs (se 2 (by rfl) ⟨30498, by rfl⟩) R60997
theorem R507377 : Reach 507377 := rs (se 2 (by rfl) ⟨190266, by rfl⟩) R380533
theorem R81443 : Reach 81443 := rs (se 1 (by rfl) ⟨61082, by rfl⟩) R122165
theorem R81523 : Reach 81523 := rs (se 1 (by rfl) ⟨61142, by rfl⟩) R122285
theorem R245389 : Reach 245389 := rs (se 3 (by rfl) ⟨46010, by rfl⟩) R92021
theorem R474821 : Reach 474821 := rs (se 4 (by rfl) ⟨44514, by rfl⟩) R89029
theorem R376589 : Reach 376589 := rs (se 3 (by rfl) ⟨70610, by rfl⟩) R141221
theorem R147217 : Reach 147217 := rs (se 2 (by rfl) ⟨55206, by rfl⟩) R110413
theorem R606005 : Reach 606005 := rs (se 5 (by rfl) ⟨28406, by rfl⟩) R56813
theorem R2015117 : Reach 2015117 := rs (se 3 (by rfl) ⟨377834, by rfl⟩) R755669
theorem R147491 : Reach 147491 := rs (se 1 (by rfl) ⟨110618, by rfl⟩) R221237
theorem R147565 : Reach 147565 := rs (se 3 (by rfl) ⟨27668, by rfl⟩) R55337
theorem R82081 : Reach 82081 := rs (se 2 (by rfl) ⟨30780, by rfl⟩) R61561
theorem R147683 : Reach 147683 := rs (se 1 (by rfl) ⟨110762, by rfl⟩) R221525
theorem R409841 : Reach 409841 := rs (se 2 (by rfl) ⟨153690, by rfl⟩) R307381
theorem R147811 : Reach 147811 := rs (se 1 (by rfl) ⟨110858, by rfl⟩) R221717
theorem R213475 : Reach 213475 := rs (se 1 (by rfl) ⟨160106, by rfl⟩) R320213
theorem R279139 : Reach 279139 := rs (se 1 (by rfl) ⟨209354, by rfl⟩) R418709
theorem R82625 : Reach 82625 := rs (se 2 (by rfl) ⟨30984, by rfl⟩) R61969
theorem R82691 : Reach 82691 := rs (se 1 (by rfl) ⟨62018, by rfl⟩) R124037
theorem R82721 : Reach 82721 := rs (se 2 (by rfl) ⟨31020, by rfl⟩) R62041
theorem R82739 : Reach 82739 := rs (se 1 (by rfl) ⟨62054, by rfl⟩) R124109
theorem R836405 : Reach 836405 := rs (se 5 (by rfl) ⟨39206, by rfl⟩) R78413
theorem R148301 : Reach 148301 := rs (se 3 (by rfl) ⟨27806, by rfl⟩) R55613
theorem R82769 : Reach 82769 := rs (se 2 (by rfl) ⟨31038, by rfl⟩) R62077
theorem R82787 : Reach 82787 := rs (se 1 (by rfl) ⟨62090, by rfl⟩) R124181
theorem R82817 : Reach 82817 := rs (se 2 (by rfl) ⟨31056, by rfl⟩) R62113
theorem R82835 : Reach 82835 := rs (se 1 (by rfl) ⟨62126, by rfl⟩) R124253
theorem R82865 : Reach 82865 := rs (se 2 (by rfl) ⟨31074, by rfl⟩) R62149
theorem R82883 : Reach 82883 := rs (se 1 (by rfl) ⟨62162, by rfl⟩) R124325
theorem R82913 : Reach 82913 := rs (se 2 (by rfl) ⟨31092, by rfl⟩) R62185
theorem R82931 : Reach 82931 := rs (se 1 (by rfl) ⟨62198, by rfl⟩) R124397
theorem R148493 : Reach 148493 := rs (se 3 (by rfl) ⟨27842, by rfl⟩) R55685
theorem R82961 : Reach 82961 := rs (se 2 (by rfl) ⟨31110, by rfl⟩) R62221
theorem R82979 : Reach 82979 := rs (se 1 (by rfl) ⟨62234, by rfl⟩) R124469
theorem R83009 : Reach 83009 := rs (se 2 (by rfl) ⟨31128, by rfl⟩) R62257
theorem R83027 : Reach 83027 := rs (se 1 (by rfl) ⟨62270, by rfl⟩) R124541
theorem R83057 : Reach 83057 := rs (se 2 (by rfl) ⟨31146, by rfl⟩) R62293
theorem R83075 : Reach 83075 := rs (se 1 (by rfl) ⟨62306, by rfl⟩) R124613
theorem R148625 : Reach 148625 := rs (se 2 (by rfl) ⟨55734, by rfl⟩) R111469
theorem R83105 : Reach 83105 := rs (se 2 (by rfl) ⟨31164, by rfl⟩) R62329
theorem R83123 : Reach 83123 := rs (se 1 (by rfl) ⟨62342, by rfl⟩) R124685
theorem R148675 : Reach 148675 := rs (se 1 (by rfl) ⟨111506, by rfl⟩) R223013
theorem R1262789 : Reach 1262789 := rs (se 4 (by rfl) ⟨118386, by rfl⟩) R236773
theorem R181453 : Reach 181453 := rs (se 3 (by rfl) ⟨34022, by rfl⟩) R68045
theorem R83153 : Reach 83153 := rs (se 2 (by rfl) ⟨31182, by rfl⟩) R62365
theorem R83171 : Reach 83171 := rs (se 1 (by rfl) ⟨62378, by rfl⟩) R124757
theorem R83201 : Reach 83201 := rs (se 2 (by rfl) ⟨31200, by rfl⟩) R62401
theorem R83219 : Reach 83219 := rs (se 1 (by rfl) ⟨62414, by rfl⟩) R124829
theorem R83249 : Reach 83249 := rs (se 2 (by rfl) ⟨31218, by rfl⟩) R62437
theorem R83267 : Reach 83267 := rs (se 1 (by rfl) ⟨62450, by rfl⟩) R124901
theorem R443717 : Reach 443717 := rs (se 4 (by rfl) ⟨41598, by rfl⟩) R83197
theorem R148817 : Reach 148817 := rs (se 2 (by rfl) ⟨55806, by rfl⟩) R111613
theorem R83297 : Reach 83297 := rs (se 2 (by rfl) ⟨31236, by rfl⟩) R62473
theorem R83315 : Reach 83315 := rs (se 1 (by rfl) ⟨62486, by rfl⟩) R124973
theorem R181645 : Reach 181645 := rs (se 3 (by rfl) ⟨34058, by rfl⟩) R68117
theorem R83345 : Reach 83345 := rs (se 2 (by rfl) ⟨31254, by rfl⟩) R62509
theorem R83363 : Reach 83363 := rs (se 1 (by rfl) ⟨62522, by rfl⟩) R125045
theorem R83393 : Reach 83393 := rs (se 2 (by rfl) ⟨31272, by rfl⟩) R62545
theorem R83411 : Reach 83411 := rs (se 1 (by rfl) ⟨62558, by rfl⟩) R125117
theorem R83425 : Reach 83425 := rs (se 2 (by rfl) ⟨31284, by rfl⟩) R62569
theorem R83441 : Reach 83441 := rs (se 2 (by rfl) ⟨31290, by rfl⟩) R62581
theorem R83459 : Reach 83459 := rs (se 1 (by rfl) ⟨62594, by rfl⟩) R125189
theorem R83489 : Reach 83489 := rs (se 2 (by rfl) ⟨31308, by rfl⟩) R62617
theorem R83507 : Reach 83507 := rs (se 1 (by rfl) ⟨62630, by rfl⟩) R125261
theorem R83537 : Reach 83537 := rs (se 2 (by rfl) ⟨31326, by rfl⟩) R62653
theorem R83539 : Reach 83539 := rs (se 1 (by rfl) ⟨62654, by rfl⟩) R125309
theorem R83555 : Reach 83555 := rs (se 1 (by rfl) ⟨62666, by rfl⟩) R125333
theorem R83585 : Reach 83585 := rs (se 2 (by rfl) ⟨31344, by rfl⟩) R62689
theorem R149123 : Reach 149123 := rs (se 1 (by rfl) ⟨111842, by rfl⟩) R223685
theorem R83603 : Reach 83603 := rs (se 1 (by rfl) ⟨62702, by rfl⟩) R125405
theorem R83633 : Reach 83633 := rs (se 2 (by rfl) ⟨31362, by rfl⟩) R62725
theorem R83651 : Reach 83651 := rs (se 1 (by rfl) ⟨62738, by rfl⟩) R125477
theorem R83681 : Reach 83681 := rs (se 2 (by rfl) ⟨31380, by rfl⟩) R62761
theorem R83699 : Reach 83699 := rs (se 1 (by rfl) ⟨62774, by rfl⟩) R125549
theorem R83729 : Reach 83729 := rs (se 2 (by rfl) ⟨31398, by rfl⟩) R62797
theorem R83747 : Reach 83747 := rs (se 1 (by rfl) ⟨62810, by rfl⟩) R125621
theorem R83777 : Reach 83777 := rs (se 2 (by rfl) ⟨31416, by rfl⟩) R62833
theorem R83795 : Reach 83795 := rs (se 1 (by rfl) ⟨62846, by rfl⟩) R125693
theorem R83825 : Reach 83825 := rs (se 2 (by rfl) ⟨31434, by rfl⟩) R62869
theorem R83843 : Reach 83843 := rs (se 1 (by rfl) ⟨62882, by rfl⟩) R125765
theorem R83873 : Reach 83873 := rs (se 2 (by rfl) ⟨31452, by rfl⟩) R62905
theorem R83891 : Reach 83891 := rs (se 1 (by rfl) ⟨62918, by rfl⟩) R125837
theorem R673733 : Reach 673733 := rs (se 4 (by rfl) ⟨63162, by rfl⟩) R126325
theorem R83921 : Reach 83921 := rs (se 2 (by rfl) ⟨31470, by rfl⟩) R62941
theorem R83939 : Reach 83939 := rs (se 1 (by rfl) ⟨62954, by rfl⟩) R125909
theorem R149485 : Reach 149485 := rs (se 3 (by rfl) ⟨28028, by rfl⟩) R56057
theorem R83969 : Reach 83969 := rs (se 2 (by rfl) ⟨31488, by rfl⟩) R62977
theorem R83987 : Reach 83987 := rs (se 1 (by rfl) ⟨62990, by rfl⟩) R125981
theorem R84017 : Reach 84017 := rs (se 2 (by rfl) ⟨31506, by rfl⟩) R63013
theorem R84035 : Reach 84035 := rs (se 1 (by rfl) ⟨63026, by rfl⟩) R126053
theorem R84065 : Reach 84065 := rs (se 2 (by rfl) ⟨31524, by rfl⟩) R63049
theorem R84083 : Reach 84083 := rs (se 1 (by rfl) ⟨63062, by rfl⟩) R126125
theorem R84113 : Reach 84113 := rs (se 2 (by rfl) ⟨31542, by rfl⟩) R63085
theorem R84131 : Reach 84131 := rs (se 1 (by rfl) ⟨63098, by rfl⟩) R126197
theorem R149681 : Reach 149681 := rs (se 2 (by rfl) ⟨56130, by rfl⟩) R112261
theorem R84161 : Reach 84161 := rs (se 2 (by rfl) ⟨31560, by rfl⟩) R63121
theorem R84179 : Reach 84179 := rs (se 1 (by rfl) ⟨63134, by rfl⟩) R126269
theorem R84209 : Reach 84209 := rs (se 2 (by rfl) ⟨31578, by rfl⟩) R63157
theorem R84227 : Reach 84227 := rs (se 1 (by rfl) ⟨63170, by rfl⟩) R126341
theorem R84257 : Reach 84257 := rs (se 2 (by rfl) ⟨31596, by rfl⟩) R63193
theorem R84275 : Reach 84275 := rs (se 1 (by rfl) ⟨63206, by rfl⟩) R126413
theorem R84305 : Reach 84305 := rs (se 2 (by rfl) ⟨31614, by rfl⟩) R63229
theorem R84323 : Reach 84323 := rs (se 1 (by rfl) ⟨63242, by rfl⟩) R126485
theorem R84353 : Reach 84353 := rs (se 2 (by rfl) ⟨31632, by rfl⟩) R63265
theorem R84371 : Reach 84371 := rs (se 1 (by rfl) ⟨63278, by rfl⟩) R126557
theorem R84401 : Reach 84401 := rs (se 2 (by rfl) ⟨31650, by rfl⟩) R63301
theorem R84419 : Reach 84419 := rs (se 1 (by rfl) ⟨63314, by rfl⟩) R126629
theorem R84449 : Reach 84449 := rs (se 2 (by rfl) ⟨31668, by rfl⟩) R63337
theorem R84467 : Reach 84467 := rs (se 1 (by rfl) ⟨63350, by rfl⟩) R126701
theorem R84497 : Reach 84497 := rs (se 2 (by rfl) ⟨31686, by rfl⟩) R63373
theorem R84515 : Reach 84515 := rs (se 1 (by rfl) ⟨63386, by rfl⟩) R126773
theorem R84545 : Reach 84545 := rs (se 2 (by rfl) ⟨31704, by rfl⟩) R63409
theorem R84563 : Reach 84563 := rs (se 1 (by rfl) ⟨63422, by rfl⟩) R126845
theorem R84593 : Reach 84593 := rs (se 2 (by rfl) ⟨31722, by rfl⟩) R63445
theorem R84611 : Reach 84611 := rs (se 1 (by rfl) ⟨63458, by rfl⟩) R126917
theorem R215693 : Reach 215693 := rs (se 3 (by rfl) ⟨40442, by rfl⟩) R80885
theorem R84641 : Reach 84641 := rs (se 2 (by rfl) ⟨31740, by rfl⟩) R63481
theorem R84659 : Reach 84659 := rs (se 1 (by rfl) ⟨63494, by rfl⟩) R126989
theorem R84689 : Reach 84689 := rs (se 2 (by rfl) ⟨31758, by rfl⟩) R63517
theorem R84707 : Reach 84707 := rs (se 1 (by rfl) ⟨63530, by rfl⟩) R127061
theorem R84737 : Reach 84737 := rs (se 2 (by rfl) ⟨31776, by rfl⟩) R63553
theorem R84755 : Reach 84755 := rs (se 1 (by rfl) ⟨63566, by rfl⟩) R127133
theorem R281393 : Reach 281393 := rs (se 2 (by rfl) ⟨105522, by rfl⟩) R211045
theorem R84785 : Reach 84785 := rs (se 2 (by rfl) ⟨31794, by rfl⟩) R63589
theorem R84803 : Reach 84803 := rs (se 1 (by rfl) ⟨63602, by rfl⟩) R127205
theorem R84833 : Reach 84833 := rs (se 2 (by rfl) ⟨31812, by rfl⟩) R63625
theorem R84851 : Reach 84851 := rs (se 1 (by rfl) ⟨63638, by rfl⟩) R127277
theorem R84881 : Reach 84881 := rs (se 2 (by rfl) ⟨31830, by rfl⟩) R63661
theorem R183185 : Reach 183185 := rs (se 2 (by rfl) ⟨68694, by rfl⟩) R137389
theorem R84899 : Reach 84899 := rs (se 1 (by rfl) ⟨63674, by rfl⟩) R127349
theorem R84929 : Reach 84929 := rs (se 2 (by rfl) ⟨31848, by rfl⟩) R63697
theorem R84947 : Reach 84947 := rs (se 1 (by rfl) ⟨63710, by rfl⟩) R127421
theorem R84977 : Reach 84977 := rs (se 2 (by rfl) ⟨31866, by rfl⟩) R63733
theorem R84995 : Reach 84995 := rs (se 1 (by rfl) ⟨63746, by rfl⟩) R127493
theorem R314381 : Reach 314381 := rs (se 3 (by rfl) ⟨58946, by rfl⟩) R117893
theorem R85025 : Reach 85025 := rs (se 2 (by rfl) ⟨31884, by rfl⟩) R63769
theorem R85043 : Reach 85043 := rs (se 1 (by rfl) ⟨63782, by rfl⟩) R127565
theorem R85073 : Reach 85073 := rs (se 2 (by rfl) ⟨31902, by rfl⟩) R63805
theorem R85091 : Reach 85091 := rs (se 1 (by rfl) ⟨63818, by rfl⟩) R127637
theorem R281713 : Reach 281713 := rs (se 2 (by rfl) ⟨105642, by rfl⟩) R211285
theorem R85121 : Reach 85121 := rs (se 2 (by rfl) ⟨31920, by rfl⟩) R63841
theorem R85139 : Reach 85139 := rs (se 1 (by rfl) ⟨63854, by rfl⟩) R127709
theorem R85169 : Reach 85169 := rs (se 2 (by rfl) ⟨31938, by rfl⟩) R63877
theorem R85187 : Reach 85187 := rs (se 1 (by rfl) ⟨63890, by rfl⟩) R127781
theorem R85217 : Reach 85217 := rs (se 2 (by rfl) ⟨31956, by rfl⟩) R63913
theorem R85235 : Reach 85235 := rs (se 1 (by rfl) ⟨63926, by rfl⟩) R127853
theorem R85265 : Reach 85265 := rs (se 2 (by rfl) ⟨31974, by rfl⟩) R63949
theorem R85283 : Reach 85283 := rs (se 1 (by rfl) ⟨63962, by rfl⟩) R127925
theorem R85313 : Reach 85313 := rs (se 2 (by rfl) ⟨31992, by rfl⟩) R63985
theorem R85331 : Reach 85331 := rs (se 1 (by rfl) ⟨63998, by rfl⟩) R127997
theorem R314723 : Reach 314723 := rs (se 1 (by rfl) ⟨236042, by rfl⟩) R472085
theorem R85361 : Reach 85361 := rs (se 2 (by rfl) ⟨32010, by rfl⟩) R64021
theorem R85379 : Reach 85379 := rs (se 1 (by rfl) ⟨64034, by rfl⟩) R128069
theorem R85409 : Reach 85409 := rs (se 2 (by rfl) ⟨32028, by rfl⟩) R64057
theorem R85427 : Reach 85427 := rs (se 1 (by rfl) ⟨64070, by rfl⟩) R128141
theorem R249293 : Reach 249293 := rs (se 3 (by rfl) ⟨46742, by rfl⟩) R93485
theorem R347597 : Reach 347597 := rs (se 3 (by rfl) ⟨65174, by rfl⟩) R130349
theorem R85457 : Reach 85457 := rs (se 2 (by rfl) ⟨32046, by rfl⟩) R64093
theorem R85475 : Reach 85475 := rs (se 1 (by rfl) ⟨64106, by rfl⟩) R128213
theorem R85505 : Reach 85505 := rs (se 2 (by rfl) ⟨32064, by rfl⟩) R64129
theorem R183811 : Reach 183811 := rs (se 1 (by rfl) ⟨137858, by rfl⟩) R275717
theorem R85523 : Reach 85523 := rs (se 1 (by rfl) ⟨64142, by rfl⟩) R128285
theorem R85553 : Reach 85553 := rs (se 2 (by rfl) ⟨32082, by rfl⟩) R64165
theorem R85571 : Reach 85571 := rs (se 1 (by rfl) ⟨64178, by rfl⟩) R128357
theorem R85601 : Reach 85601 := rs (se 2 (by rfl) ⟨32100, by rfl⟩) R64201
theorem R85619 : Reach 85619 := rs (se 1 (by rfl) ⟨64214, by rfl⟩) R128429
theorem R85649 : Reach 85649 := rs (se 2 (by rfl) ⟨32118, by rfl⟩) R64237
theorem R85667 : Reach 85667 := rs (se 1 (by rfl) ⟨64250, by rfl⟩) R128501
theorem R85697 : Reach 85697 := rs (se 2 (by rfl) ⟨32136, by rfl⟩) R64273
theorem R85715 : Reach 85715 := rs (se 1 (by rfl) ⟨64286, by rfl⟩) R128573
theorem R85745 : Reach 85745 := rs (se 2 (by rfl) ⟨32154, by rfl⟩) R64309
theorem R85763 : Reach 85763 := rs (se 1 (by rfl) ⟨64322, by rfl⟩) R128645
theorem R151313 : Reach 151313 := rs (se 2 (by rfl) ⟨56742, by rfl⟩) R113485
theorem R85793 : Reach 85793 := rs (se 2 (by rfl) ⟨32172, by rfl⟩) R64345
theorem R118577 : Reach 118577 := rs (se 2 (by rfl) ⟨44466, by rfl⟩) R88933
theorem R85811 : Reach 85811 := rs (se 1 (by rfl) ⟨64358, by rfl⟩) R128717
theorem R85841 : Reach 85841 := rs (se 2 (by rfl) ⟨32190, by rfl⟩) R64381
theorem R85859 : Reach 85859 := rs (se 1 (by rfl) ⟨64394, by rfl⟩) R128789
theorem R249713 : Reach 249713 := rs (se 2 (by rfl) ⟨93642, by rfl⟩) R187285
theorem R85889 : Reach 85889 := rs (se 2 (by rfl) ⟨32208, by rfl⟩) R64417
theorem R85907 : Reach 85907 := rs (se 1 (by rfl) ⟨64430, by rfl⟩) R128861
theorem R249763 : Reach 249763 := rs (se 1 (by rfl) ⟨187322, by rfl⟩) R374645
theorem R85937 : Reach 85937 := rs (se 2 (by rfl) ⟨32226, by rfl⟩) R64453
theorem R85955 : Reach 85955 := rs (se 1 (by rfl) ⟨64466, by rfl⟩) R128933
theorem R85985 : Reach 85985 := rs (se 2 (by rfl) ⟨32244, by rfl⟩) R64489
theorem R86003 : Reach 86003 := rs (se 1 (by rfl) ⟨64502, by rfl⟩) R129005
theorem R380933 : Reach 380933 := rs (se 4 (by rfl) ⟨35712, by rfl⟩) R71425
theorem R86033 : Reach 86033 := rs (se 2 (by rfl) ⟨32262, by rfl⟩) R64525
theorem R86051 : Reach 86051 := rs (se 1 (by rfl) ⟨64538, by rfl⟩) R129077
theorem R86081 : Reach 86081 := rs (se 2 (by rfl) ⟨32280, by rfl⟩) R64561
theorem R86099 : Reach 86099 := rs (se 1 (by rfl) ⟨64574, by rfl⟩) R129149
theorem R86129 : Reach 86129 := rs (se 2 (by rfl) ⟨32298, by rfl⟩) R64597
theorem R86147 : Reach 86147 := rs (se 1 (by rfl) ⟨64610, by rfl⟩) R129221
theorem R86177 : Reach 86177 := rs (se 2 (by rfl) ⟨32316, by rfl⟩) R64633
theorem R86195 : Reach 86195 := rs (se 1 (by rfl) ⟨64646, by rfl⟩) R129293
theorem R118979 : Reach 118979 := rs (se 1 (by rfl) ⟨89234, by rfl⟩) R178469
theorem R86225 : Reach 86225 := rs (se 2 (by rfl) ⟨32334, by rfl⟩) R64669
theorem R282851 : Reach 282851 := rs (se 1 (by rfl) ⟨212138, by rfl⟩) R424277
theorem R86243 : Reach 86243 := rs (se 1 (by rfl) ⟨64682, by rfl⟩) R129365
theorem R86273 : Reach 86273 := rs (se 2 (by rfl) ⟨32352, by rfl⟩) R64705
theorem R86291 : Reach 86291 := rs (se 1 (by rfl) ⟨64718, by rfl⟩) R129437
theorem R86321 : Reach 86321 := rs (se 2 (by rfl) ⟨32370, by rfl⟩) R64741
theorem R86339 : Reach 86339 := rs (se 1 (by rfl) ⟨64754, by rfl⟩) R129509
theorem R86369 : Reach 86369 := rs (se 2 (by rfl) ⟨32388, by rfl⟩) R64777
theorem R86387 : Reach 86387 := rs (se 1 (by rfl) ⟨64790, by rfl⟩) R129581
theorem R86417 : Reach 86417 := rs (se 2 (by rfl) ⟨32406, by rfl⟩) R64813
theorem R86435 : Reach 86435 := rs (se 1 (by rfl) ⟨64826, by rfl⟩) R129653
theorem R86465 : Reach 86465 := rs (se 2 (by rfl) ⟨32424, by rfl⟩) R64849
theorem R86483 : Reach 86483 := rs (se 1 (by rfl) ⟨64862, by rfl⟩) R129725
theorem R86513 : Reach 86513 := rs (se 2 (by rfl) ⟨32442, by rfl⟩) R64885
theorem R86531 : Reach 86531 := rs (se 1 (by rfl) ⟨64898, by rfl⟩) R129797
theorem R86561 : Reach 86561 := rs (se 2 (by rfl) ⟨32460, by rfl⟩) R64921
theorem R86579 : Reach 86579 := rs (se 1 (by rfl) ⟨64934, by rfl⟩) R129869
theorem R86609 : Reach 86609 := rs (se 2 (by rfl) ⟨32478, by rfl⟩) R64957
theorem R479843 : Reach 479843 := rs (se 1 (by rfl) ⟨359882, by rfl⟩) R719765
theorem R86627 : Reach 86627 := rs (se 1 (by rfl) ⟨64970, by rfl⟩) R129941
theorem R348785 : Reach 348785 := rs (se 2 (by rfl) ⟨130794, by rfl⟩) R261589
theorem R86657 : Reach 86657 := rs (se 2 (by rfl) ⟨32496, by rfl⟩) R64993
theorem R86675 : Reach 86675 := rs (se 1 (by rfl) ⟨65006, by rfl⟩) R130013
theorem R86705 : Reach 86705 := rs (se 2 (by rfl) ⟨32514, by rfl⟩) R65029
theorem R86723 : Reach 86723 := rs (se 1 (by rfl) ⟨65042, by rfl⟩) R130085
theorem R185041 : Reach 185041 := rs (se 2 (by rfl) ⟨69390, by rfl⟩) R138781
theorem R86753 : Reach 86753 := rs (se 2 (by rfl) ⟨32532, by rfl⟩) R65065
theorem R86771 : Reach 86771 := rs (se 1 (by rfl) ⟨65078, by rfl⟩) R130157
theorem R86801 : Reach 86801 := rs (se 2 (by rfl) ⟨32550, by rfl⟩) R65101
theorem R86819 : Reach 86819 := rs (se 1 (by rfl) ⟨65114, by rfl⟩) R130229
theorem R86849 : Reach 86849 := rs (se 2 (by rfl) ⟨32568, by rfl⟩) R65137
theorem R86867 : Reach 86867 := rs (se 1 (by rfl) ⟨65150, by rfl⟩) R130301
theorem R86897 : Reach 86897 := rs (se 2 (by rfl) ⟨32586, by rfl⟩) R65173
theorem R86915 : Reach 86915 := rs (se 1 (by rfl) ⟨65186, by rfl⟩) R130373
theorem R86945 : Reach 86945 := rs (se 2 (by rfl) ⟨32604, by rfl⟩) R65209
theorem R86963 : Reach 86963 := rs (se 1 (by rfl) ⟨65222, by rfl⟩) R130445
theorem R86993 : Reach 86993 := rs (se 2 (by rfl) ⟨32622, by rfl⟩) R65245
theorem R87011 : Reach 87011 := rs (se 1 (by rfl) ⟨65258, by rfl⟩) R130517
theorem R87041 : Reach 87041 := rs (se 2 (by rfl) ⟨32640, by rfl⟩) R65281
theorem R283661 : Reach 283661 := rs (se 3 (by rfl) ⟨53186, by rfl⟩) R106373
theorem R87059 : Reach 87059 := rs (se 1 (by rfl) ⟨65294, by rfl⟩) R130589
theorem R87089 : Reach 87089 := rs (se 2 (by rfl) ⟨32658, by rfl⟩) R65317
theorem R119875 : Reach 119875 := rs (se 1 (by rfl) ⟨89906, by rfl⟩) R179813
theorem R87107 : Reach 87107 := rs (se 1 (by rfl) ⟨65330, by rfl⟩) R130661
theorem R87137 : Reach 87137 := rs (se 2 (by rfl) ⟨32676, by rfl⟩) R65353
theorem R87155 : Reach 87155 := rs (se 1 (by rfl) ⟨65366, by rfl⟩) R130733
theorem R87185 : Reach 87185 := rs (se 2 (by rfl) ⟨32694, by rfl⟩) R65389
theorem R87203 : Reach 87203 := rs (se 1 (by rfl) ⟨65402, by rfl⟩) R130805
theorem R87233 : Reach 87233 := rs (se 2 (by rfl) ⟨32712, by rfl⟩) R65425
theorem R87251 : Reach 87251 := rs (se 1 (by rfl) ⟨65438, by rfl⟩) R130877
theorem R87281 : Reach 87281 := rs (se 2 (by rfl) ⟨32730, by rfl⟩) R65461
theorem R87299 : Reach 87299 := rs (se 1 (by rfl) ⟨65474, by rfl⟩) R130949
theorem R87329 : Reach 87329 := rs (se 2 (by rfl) ⟨32748, by rfl⟩) R65497
theorem R185645 : Reach 185645 := rs (se 3 (by rfl) ⟨34808, by rfl⟩) R69617
theorem R87347 : Reach 87347 := rs (se 1 (by rfl) ⟨65510, by rfl⟩) R131021
theorem R87377 : Reach 87377 := rs (se 2 (by rfl) ⟨32766, by rfl⟩) R65533
theorem R87395 : Reach 87395 := rs (se 1 (by rfl) ⟨65546, by rfl⟩) R131093
theorem R87425 : Reach 87425 := rs (se 2 (by rfl) ⟨32784, by rfl⟩) R65569
theorem R87443 : Reach 87443 := rs (se 1 (by rfl) ⟨65582, by rfl⟩) R131165
theorem R87473 : Reach 87473 := rs (se 2 (by rfl) ⟨32802, by rfl⟩) R65605
theorem R87491 : Reach 87491 := rs (se 1 (by rfl) ⟨65618, by rfl⟩) R131237
theorem R87521 : Reach 87521 := rs (se 2 (by rfl) ⟨32820, by rfl⟩) R65641
theorem R218609 : Reach 218609 := rs (se 2 (by rfl) ⟨81978, by rfl⟩) R163957
theorem R87539 : Reach 87539 := rs (se 1 (by rfl) ⟨65654, by rfl⟩) R131309
theorem R87569 : Reach 87569 := rs (se 2 (by rfl) ⟨32838, by rfl⟩) R65677
theorem R87587 : Reach 87587 := rs (se 1 (by rfl) ⟨65690, by rfl⟩) R131381
theorem R87617 : Reach 87617 := rs (se 2 (by rfl) ⟨32856, by rfl⟩) R65713
theorem R87635 : Reach 87635 := rs (se 1 (by rfl) ⟨65726, by rfl⟩) R131453
theorem R87665 : Reach 87665 := rs (se 2 (by rfl) ⟨32874, by rfl⟩) R65749
theorem R87683 : Reach 87683 := rs (se 1 (by rfl) ⟨65762, by rfl⟩) R131525
theorem R87713 : Reach 87713 := rs (se 2 (by rfl) ⟨32892, by rfl⟩) R65785
theorem R87731 : Reach 87731 := rs (se 1 (by rfl) ⟨65798, by rfl⟩) R131597
theorem R87761 : Reach 87761 := rs (se 2 (by rfl) ⟨32910, by rfl⟩) R65821
theorem R186083 : Reach 186083 := rs (se 1 (by rfl) ⟨139562, by rfl⟩) R279125
theorem R87779 : Reach 87779 := rs (se 1 (by rfl) ⟨65834, by rfl⟩) R131669
theorem R87809 : Reach 87809 := rs (se 2 (by rfl) ⟨32928, by rfl⟩) R65857
theorem R153361 : Reach 153361 := rs (se 2 (by rfl) ⟨57510, by rfl⟩) R115021
theorem R87827 : Reach 87827 := rs (se 1 (by rfl) ⟨65870, by rfl⟩) R131741
theorem R87857 : Reach 87857 := rs (se 2 (by rfl) ⟨32946, by rfl⟩) R65893
theorem R87875 : Reach 87875 := rs (se 1 (by rfl) ⟨65906, by rfl⟩) R131813
theorem R55123 : Reach 55123 := rs (se 1 (by rfl) ⟨41342, by rfl⟩) R82685
theorem R87905 : Reach 87905 := rs (se 2 (by rfl) ⟨32964, by rfl⟩) R65929
theorem R55139 : Reach 55139 := rs (se 1 (by rfl) ⟨41354, by rfl⟩) R82709
theorem R317297 : Reach 317297 := rs (se 2 (by rfl) ⟨118986, by rfl⟩) R237973
theorem R55155 : Reach 55155 := rs (se 1 (by rfl) ⟨41366, by rfl⟩) R82733
theorem R87923 : Reach 87923 := rs (se 1 (by rfl) ⟨65942, by rfl⟩) R131885
theorem R55171 : Reach 55171 := rs (se 1 (by rfl) ⟨41378, by rfl⟩) R82757
theorem R87953 : Reach 87953 := rs (se 2 (by rfl) ⟨32982, by rfl⟩) R65965
theorem R55187 : Reach 55187 := rs (se 1 (by rfl) ⟨41390, by rfl⟩) R82781
theorem R55203 : Reach 55203 := rs (se 1 (by rfl) ⟨41402, by rfl⟩) R82805
theorem R87971 : Reach 87971 := rs (se 1 (by rfl) ⟨65978, by rfl⟩) R131957
theorem R55219 : Reach 55219 := rs (se 1 (by rfl) ⟨41414, by rfl⟩) R82829
theorem R88001 : Reach 88001 := rs (se 2 (by rfl) ⟨33000, by rfl⟩) R66001
theorem R55235 : Reach 55235 := rs (se 1 (by rfl) ⟨41426, by rfl⟩) R82853
theorem R55251 : Reach 55251 := rs (se 1 (by rfl) ⟨41438, by rfl⟩) R82877
theorem R88019 : Reach 88019 := rs (se 1 (by rfl) ⟨66014, by rfl⟩) R132029
theorem R55267 : Reach 55267 := rs (se 1 (by rfl) ⟨41450, by rfl⟩) R82901
theorem R186353 : Reach 186353 := rs (se 2 (by rfl) ⟨69882, by rfl⟩) R139765
theorem R55283 : Reach 55283 := rs (se 1 (by rfl) ⟨41462, by rfl⟩) R82925
theorem R88049 : Reach 88049 := rs (se 2 (by rfl) ⟨33018, by rfl⟩) R66037
theorem R55299 : Reach 55299 := rs (se 1 (by rfl) ⟨41474, by rfl⟩) R82949
theorem R88067 : Reach 88067 := rs (se 1 (by rfl) ⟨66050, by rfl⟩) R132101
theorem R55315 : Reach 55315 := rs (se 1 (by rfl) ⟨41486, by rfl⟩) R82973
theorem R55331 : Reach 55331 := rs (se 1 (by rfl) ⟨41498, by rfl⟩) R82997
theorem R88097 : Reach 88097 := rs (se 2 (by rfl) ⟨33036, by rfl⟩) R66073
theorem R55347 : Reach 55347 := rs (se 1 (by rfl) ⟨41510, by rfl⟩) R83021
theorem R88115 : Reach 88115 := rs (se 1 (by rfl) ⟨66086, by rfl⟩) R132173
theorem R55363 : Reach 55363 := rs (se 1 (by rfl) ⟨41522, by rfl⟩) R83045
theorem R88145 : Reach 88145 := rs (se 2 (by rfl) ⟨33054, by rfl⟩) R66109
theorem R55379 : Reach 55379 := rs (se 1 (by rfl) ⟨41534, by rfl⟩) R83069
theorem R55395 : Reach 55395 := rs (se 1 (by rfl) ⟨41546, by rfl⟩) R83093
theorem R88163 : Reach 88163 := rs (se 1 (by rfl) ⟨66122, by rfl⟩) R132245
theorem R55411 : Reach 55411 := rs (se 1 (by rfl) ⟨41558, by rfl⟩) R83117
theorem R88193 : Reach 88193 := rs (se 2 (by rfl) ⟨33072, by rfl⟩) R66145
theorem R55427 : Reach 55427 := rs (se 1 (by rfl) ⟨41570, by rfl⟩) R83141
theorem R55443 : Reach 55443 := rs (se 1 (by rfl) ⟨41582, by rfl⟩) R83165
theorem R88211 : Reach 88211 := rs (se 1 (by rfl) ⟨66158, by rfl⟩) R132317
theorem R55459 : Reach 55459 := rs (se 1 (by rfl) ⟨41594, by rfl⟩) R83189
theorem R88241 : Reach 88241 := rs (se 2 (by rfl) ⟨33090, by rfl⟩) R66181
theorem R55475 : Reach 55475 := rs (se 1 (by rfl) ⟨41606, by rfl⟩) R83213
theorem R55491 : Reach 55491 := rs (se 1 (by rfl) ⟨41618, by rfl⟩) R83237
theorem R88259 : Reach 88259 := rs (se 1 (by rfl) ⟨66194, by rfl⟩) R132389
theorem R55507 : Reach 55507 := rs (se 1 (by rfl) ⟨41630, by rfl⟩) R83261
theorem R88289 : Reach 88289 := rs (se 2 (by rfl) ⟨33108, by rfl⟩) R66217
theorem R55523 : Reach 55523 := rs (se 1 (by rfl) ⟨41642, by rfl⟩) R83285
theorem R55539 : Reach 55539 := rs (se 1 (by rfl) ⟨41654, by rfl⟩) R83309
theorem R88307 : Reach 88307 := rs (se 1 (by rfl) ⟨66230, by rfl⟩) R132461
theorem R55555 : Reach 55555 := rs (se 1 (by rfl) ⟨41666, by rfl⟩) R83333
theorem R252173 : Reach 252173 := rs (se 3 (by rfl) ⟨47282, by rfl⟩) R94565
theorem R121105 : Reach 121105 := rs (se 2 (by rfl) ⟨45414, by rfl⟩) R90829
theorem R55571 : Reach 55571 := rs (se 1 (by rfl) ⟨41678, by rfl⟩) R83357
theorem R88337 : Reach 88337 := rs (se 2 (by rfl) ⟨33126, by rfl⟩) R66253
theorem R55587 : Reach 55587 := rs (se 1 (by rfl) ⟨41690, by rfl⟩) R83381
theorem R88355 : Reach 88355 := rs (se 1 (by rfl) ⟨66266, by rfl⟩) R132533
theorem R55603 : Reach 55603 := rs (se 1 (by rfl) ⟨41702, by rfl⟩) R83405
theorem R88385 : Reach 88385 := rs (se 2 (by rfl) ⟨33144, by rfl⟩) R66289
theorem R55619 : Reach 55619 := rs (se 1 (by rfl) ⟨41714, by rfl⟩) R83429
theorem R55635 : Reach 55635 := rs (se 1 (by rfl) ⟨41726, by rfl⟩) R83453
theorem R88403 : Reach 88403 := rs (se 1 (by rfl) ⟨66302, by rfl⟩) R132605
theorem R55651 : Reach 55651 := rs (se 1 (by rfl) ⟨41738, by rfl⟩) R83477
theorem R88433 : Reach 88433 := rs (se 2 (by rfl) ⟨33162, by rfl⟩) R66325
theorem R55667 : Reach 55667 := rs (se 1 (by rfl) ⟨41750, by rfl⟩) R83501
theorem R55683 : Reach 55683 := rs (se 1 (by rfl) ⟨41762, by rfl⟩) R83525
theorem R88451 : Reach 88451 := rs (se 1 (by rfl) ⟨66338, by rfl⟩) R132677
theorem R55699 : Reach 55699 := rs (se 1 (by rfl) ⟨41774, by rfl⟩) R83549
theorem R55715 : Reach 55715 := rs (se 1 (by rfl) ⟨41786, by rfl⟩) R83573
theorem R88481 : Reach 88481 := rs (se 2 (by rfl) ⟨33180, by rfl⟩) R66361
theorem R55731 : Reach 55731 := rs (se 1 (by rfl) ⟨41798, by rfl⟩) R83597
theorem R88499 : Reach 88499 := rs (se 1 (by rfl) ⟨66374, by rfl⟩) R132749
theorem R55747 : Reach 55747 := rs (se 1 (by rfl) ⟨41810, by rfl⟩) R83621
theorem R88529 : Reach 88529 := rs (se 2 (by rfl) ⟨33198, by rfl⟩) R66397
theorem R55763 : Reach 55763 := rs (se 1 (by rfl) ⟨41822, by rfl⟩) R83645
theorem R55779 : Reach 55779 := rs (se 1 (by rfl) ⟨41834, by rfl⟩) R83669
theorem R88547 : Reach 88547 := rs (se 1 (by rfl) ⟨66410, by rfl⟩) R132821
theorem R55795 : Reach 55795 := rs (se 1 (by rfl) ⟨41846, by rfl⟩) R83693
theorem R88577 : Reach 88577 := rs (se 2 (by rfl) ⟨33216, by rfl⟩) R66433
theorem R55811 : Reach 55811 := rs (se 1 (by rfl) ⟨41858, by rfl⟩) R83717
theorem R186893 : Reach 186893 := rs (se 3 (by rfl) ⟨35042, by rfl⟩) R70085
theorem R55827 : Reach 55827 := rs (se 1 (by rfl) ⟨41870, by rfl⟩) R83741
theorem R88595 : Reach 88595 := rs (se 1 (by rfl) ⟨66446, by rfl⟩) R132893
theorem R55843 : Reach 55843 := rs (se 1 (by rfl) ⟨41882, by rfl⟩) R83765
theorem R88625 : Reach 88625 := rs (se 2 (by rfl) ⟨33234, by rfl⟩) R66469
theorem R55859 : Reach 55859 := rs (se 1 (by rfl) ⟨41894, by rfl⟩) R83789
theorem R186947 : Reach 186947 := rs (se 1 (by rfl) ⟨140210, by rfl⟩) R280421
theorem R55875 : Reach 55875 := rs (se 1 (by rfl) ⟨41906, by rfl⟩) R83813
theorem R88643 : Reach 88643 := rs (se 1 (by rfl) ⟨66482, by rfl⟩) R132965
theorem R55891 : Reach 55891 := rs (se 1 (by rfl) ⟨41918, by rfl⟩) R83837
theorem R55907 : Reach 55907 := rs (se 1 (by rfl) ⟨41930, by rfl⟩) R83861
theorem R88673 : Reach 88673 := rs (se 2 (by rfl) ⟨33252, by rfl⟩) R66505
theorem R55923 : Reach 55923 := rs (se 1 (by rfl) ⟨41942, by rfl⟩) R83885
theorem R55939 : Reach 55939 := rs (se 1 (by rfl) ⟨41954, by rfl⟩) R83909
theorem R55955 : Reach 55955 := rs (se 1 (by rfl) ⟨41966, by rfl⟩) R83933
theorem R55971 : Reach 55971 := rs (se 1 (by rfl) ⟨41978, by rfl⟩) R83957
theorem R55987 : Reach 55987 := rs (se 1 (by rfl) ⟨41990, by rfl⟩) R83981
theorem R56003 : Reach 56003 := rs (se 1 (by rfl) ⟨42002, by rfl⟩) R84005
theorem R56019 : Reach 56019 := rs (se 1 (by rfl) ⟨42014, by rfl⟩) R84029
theorem R56035 : Reach 56035 := rs (se 1 (by rfl) ⟨42026, by rfl⟩) R84053
theorem R56051 : Reach 56051 := rs (se 1 (by rfl) ⟨42038, by rfl⟩) R84077
theorem R56067 : Reach 56067 := rs (se 1 (by rfl) ⟨42050, by rfl⟩) R84101
theorem R56083 : Reach 56083 := rs (se 1 (by rfl) ⟨42062, by rfl⟩) R84125
theorem R56099 : Reach 56099 := rs (se 1 (by rfl) ⟨42074, by rfl⟩) R84149
theorem R187181 : Reach 187181 := rs (se 3 (by rfl) ⟨35096, by rfl⟩) R70193
theorem R56115 : Reach 56115 := rs (se 1 (by rfl) ⟨42086, by rfl⟩) R84173
theorem R1334069 : Reach 1334069 := rs (se 5 (by rfl) ⟨62534, by rfl⟩) R125069
theorem R56131 : Reach 56131 := rs (se 1 (by rfl) ⟨42098, by rfl⟩) R84197
theorem R187217 : Reach 187217 := rs (se 2 (by rfl) ⟨70206, by rfl⟩) R140413
theorem R56147 : Reach 56147 := rs (se 1 (by rfl) ⟨42110, by rfl⟩) R84221
theorem R56163 : Reach 56163 := rs (se 1 (by rfl) ⟨42122, by rfl⟩) R84245
theorem R56179 : Reach 56179 := rs (se 1 (by rfl) ⟨42134, by rfl⟩) R84269
theorem R56195 : Reach 56195 := rs (se 1 (by rfl) ⟨42146, by rfl⟩) R84293
theorem R56211 : Reach 56211 := rs (se 1 (by rfl) ⟨42158, by rfl⟩) R84317
theorem R56227 : Reach 56227 := rs (se 1 (by rfl) ⟨42170, by rfl⟩) R84341
theorem R220067 : Reach 220067 := rs (se 1 (by rfl) ⟨165050, by rfl⟩) R330101
theorem R56243 : Reach 56243 := rs (se 1 (by rfl) ⟨42182, by rfl⟩) R84365
theorem R56259 : Reach 56259 := rs (se 1 (by rfl) ⟨42194, by rfl⟩) R84389
theorem R56275 : Reach 56275 := rs (se 1 (by rfl) ⟨42206, by rfl⟩) R84413
theorem R56291 : Reach 56291 := rs (se 1 (by rfl) ⟨42218, by rfl⟩) R84437
theorem R711665 : Reach 711665 := rs (se 2 (by rfl) ⟨266874, by rfl⟩) R533749
theorem R56307 : Reach 56307 := rs (se 1 (by rfl) ⟨42230, by rfl⟩) R84461
theorem R56323 : Reach 56323 := rs (se 1 (by rfl) ⟨42242, by rfl⟩) R84485
theorem R56339 : Reach 56339 := rs (se 1 (by rfl) ⟨42254, by rfl⟩) R84509
theorem R56355 : Reach 56355 := rs (se 1 (by rfl) ⟨42266, by rfl⟩) R84533
theorem R56371 : Reach 56371 := rs (se 1 (by rfl) ⟨42278, by rfl⟩) R84557
theorem R56387 : Reach 56387 := rs (se 1 (by rfl) ⟨42290, by rfl⟩) R84581
theorem R56403 : Reach 56403 := rs (se 1 (by rfl) ⟨42302, by rfl⟩) R84605
theorem R56419 : Reach 56419 := rs (se 1 (by rfl) ⟨42314, by rfl⟩) R84629
theorem R56435 : Reach 56435 := rs (se 1 (by rfl) ⟨42326, by rfl⟩) R84653
theorem R56451 : Reach 56451 := rs (se 1 (by rfl) ⟨42338, by rfl⟩) R84677
theorem R56467 : Reach 56467 := rs (se 1 (by rfl) ⟨42350, by rfl⟩) R84701
theorem R56483 : Reach 56483 := rs (se 1 (by rfl) ⟨42362, by rfl⟩) R84725
theorem R56499 : Reach 56499 := rs (se 1 (by rfl) ⟨42374, by rfl⟩) R84749
theorem R56515 : Reach 56515 := rs (se 1 (by rfl) ⟨42386, by rfl⟩) R84773
theorem R56531 : Reach 56531 := rs (se 1 (by rfl) ⟨42398, by rfl⟩) R84797
theorem R56547 : Reach 56547 := rs (se 1 (by rfl) ⟨42410, by rfl⟩) R84821
theorem R56563 : Reach 56563 := rs (se 1 (by rfl) ⟨42422, by rfl⟩) R84845
theorem R56579 : Reach 56579 := rs (se 1 (by rfl) ⟨42434, by rfl⟩) R84869
theorem R56595 : Reach 56595 := rs (se 1 (by rfl) ⟨42446, by rfl⟩) R84893
theorem R318755 : Reach 318755 := rs (se 1 (by rfl) ⟨239066, by rfl⟩) R478133
theorem R56611 : Reach 56611 := rs (se 1 (by rfl) ⟨42458, by rfl⟩) R84917
theorem R56627 : Reach 56627 := rs (se 1 (by rfl) ⟨42470, by rfl⟩) R84941
theorem R56643 : Reach 56643 := rs (se 1 (by rfl) ⟨42482, by rfl⟩) R84965
theorem R56659 : Reach 56659 := rs (se 1 (by rfl) ⟨42494, by rfl⟩) R84989
theorem R56675 : Reach 56675 := rs (se 1 (by rfl) ⟨42506, by rfl⟩) R85013
theorem R187757 : Reach 187757 := rs (se 3 (by rfl) ⟨35204, by rfl⟩) R70409
theorem R56691 : Reach 56691 := rs (se 1 (by rfl) ⟨42518, by rfl⟩) R85037
theorem R56707 : Reach 56707 := rs (se 1 (by rfl) ⟨42530, by rfl⟩) R85061
theorem R56723 : Reach 56723 := rs (se 1 (by rfl) ⟨42542, by rfl⟩) R85085
theorem R187811 : Reach 187811 := rs (se 1 (by rfl) ⟨140858, by rfl⟩) R281717
theorem R56739 : Reach 56739 := rs (se 1 (by rfl) ⟨42554, by rfl⟩) R85109
theorem R56755 : Reach 56755 := rs (se 1 (by rfl) ⟨42566, by rfl⟩) R85133
theorem R56771 : Reach 56771 := rs (se 1 (by rfl) ⟨42578, by rfl⟩) R85157
theorem R56787 : Reach 56787 := rs (se 1 (by rfl) ⟨42590, by rfl⟩) R85181
theorem R56803 : Reach 56803 := rs (se 1 (by rfl) ⟨42602, by rfl⟩) R85205
theorem R56819 : Reach 56819 := rs (se 1 (by rfl) ⟨42614, by rfl⟩) R85229
theorem R56835 : Reach 56835 := rs (se 1 (by rfl) ⟨42626, by rfl⟩) R85253
theorem R56851 : Reach 56851 := rs (se 1 (by rfl) ⟨42638, by rfl⟩) R85277
theorem R56867 : Reach 56867 := rs (se 1 (by rfl) ⟨42650, by rfl⟩) R85301
theorem R56883 : Reach 56883 := rs (se 1 (by rfl) ⟨42662, by rfl⟩) R85325
theorem R56899 : Reach 56899 := rs (se 1 (by rfl) ⟨42674, by rfl⟩) R85349
theorem R56915 : Reach 56915 := rs (se 1 (by rfl) ⟨42686, by rfl⟩) R85373
theorem R56931 : Reach 56931 := rs (se 1 (by rfl) ⟨42698, by rfl⟩) R85397
theorem R56947 : Reach 56947 := rs (se 1 (by rfl) ⟨42710, by rfl⟩) R85421
theorem R56963 : Reach 56963 := rs (se 1 (by rfl) ⟨42722, by rfl⟩) R85445
theorem R56979 : Reach 56979 := rs (se 1 (by rfl) ⟨42734, by rfl⟩) R85469
theorem R56995 : Reach 56995 := rs (se 1 (by rfl) ⟨42746, by rfl⟩) R85493
theorem R188081 : Reach 188081 := rs (se 2 (by rfl) ⟨70530, by rfl⟩) R141061
theorem R57011 : Reach 57011 := rs (se 1 (by rfl) ⟨42758, by rfl⟩) R85517
theorem R57027 : Reach 57027 := rs (se 1 (by rfl) ⟨42770, by rfl⟩) R85541
theorem R57043 : Reach 57043 := rs (se 1 (by rfl) ⟨42782, by rfl⟩) R85565
theorem R57059 : Reach 57059 := rs (se 1 (by rfl) ⟨42794, by rfl⟩) R85589
theorem R122609 : Reach 122609 := rs (se 2 (by rfl) ⟨45978, by rfl⟩) R91957
theorem R57075 : Reach 57075 := rs (se 1 (by rfl) ⟨42806, by rfl⟩) R85613
theorem R57091 : Reach 57091 := rs (se 1 (by rfl) ⟨42818, by rfl⟩) R85637
theorem R122627 : Reach 122627 := rs (se 1 (by rfl) ⟨91970, by rfl⟩) R183941
theorem R57107 : Reach 57107 := rs (se 1 (by rfl) ⟨42830, by rfl⟩) R85661
theorem R57123 : Reach 57123 := rs (se 1 (by rfl) ⟨42842, by rfl⟩) R85685
theorem R57139 : Reach 57139 := rs (se 1 (by rfl) ⟨42854, by rfl⟩) R85709
theorem R57155 : Reach 57155 := rs (se 1 (by rfl) ⟨42866, by rfl⟩) R85733
theorem R57171 : Reach 57171 := rs (se 1 (by rfl) ⟨42878, by rfl⟩) R85757
theorem R57187 : Reach 57187 := rs (se 1 (by rfl) ⟨42890, by rfl⟩) R85781
theorem R286577 : Reach 286577 := rs (se 2 (by rfl) ⟨107466, by rfl⟩) R214933
theorem R57203 : Reach 57203 := rs (se 1 (by rfl) ⟨42902, by rfl⟩) R85805
theorem R57219 : Reach 57219 := rs (se 1 (by rfl) ⟨42914, by rfl⟩) R85829
theorem R221069 : Reach 221069 := rs (se 3 (by rfl) ⟨41450, by rfl⟩) R82901
theorem R57235 : Reach 57235 := rs (se 1 (by rfl) ⟨42926, by rfl⟩) R85853
theorem R57251 : Reach 57251 := rs (se 1 (by rfl) ⟨42938, by rfl⟩) R85877
theorem R57267 : Reach 57267 := rs (se 1 (by rfl) ⟨42950, by rfl⟩) R85901
theorem R57283 : Reach 57283 := rs (se 1 (by rfl) ⟨42962, by rfl⟩) R85925
theorem R57299 : Reach 57299 := rs (se 1 (by rfl) ⟨42974, by rfl⟩) R85949
theorem R57315 : Reach 57315 := rs (se 1 (by rfl) ⟨42986, by rfl⟩) R85973
theorem R57331 : Reach 57331 := rs (se 1 (by rfl) ⟨42998, by rfl⟩) R85997
theorem R57347 : Reach 57347 := rs (se 1 (by rfl) ⟨43010, by rfl⟩) R86021
theorem R57363 : Reach 57363 := rs (se 1 (by rfl) ⟨43022, by rfl⟩) R86045
theorem R57379 : Reach 57379 := rs (se 1 (by rfl) ⟨43034, by rfl⟩) R86069
theorem R90163 : Reach 90163 := rs (se 1 (by rfl) ⟨67622, by rfl⟩) R135245
theorem R57395 : Reach 57395 := rs (se 1 (by rfl) ⟨43046, by rfl⟩) R86093
theorem R57411 : Reach 57411 := rs (se 1 (by rfl) ⟨43058, by rfl⟩) R86117
theorem R57427 : Reach 57427 := rs (se 1 (by rfl) ⟨43070, by rfl⟩) R86141
theorem R90209 : Reach 90209 := rs (se 2 (by rfl) ⟨33828, by rfl⟩) R67657
theorem R57443 : Reach 57443 := rs (se 1 (by rfl) ⟨43082, by rfl⟩) R86165
theorem R57459 : Reach 57459 := rs (se 1 (by rfl) ⟨43094, by rfl⟩) R86189
theorem R57475 : Reach 57475 := rs (se 1 (by rfl) ⟨43106, by rfl⟩) R86213
theorem R57491 : Reach 57491 := rs (se 1 (by rfl) ⟨43118, by rfl⟩) R86237
theorem R57507 : Reach 57507 := rs (se 1 (by rfl) ⟨43130, by rfl⟩) R86261
theorem R57523 : Reach 57523 := rs (se 1 (by rfl) ⟨43142, by rfl⟩) R86285
theorem R57539 : Reach 57539 := rs (se 1 (by rfl) ⟨43154, by rfl⟩) R86309
theorem R188621 : Reach 188621 := rs (se 3 (by rfl) ⟨35366, by rfl⟩) R70733
theorem R57555 : Reach 57555 := rs (se 1 (by rfl) ⟨43166, by rfl⟩) R86333
theorem R57571 : Reach 57571 := rs (se 1 (by rfl) ⟨43178, by rfl⟩) R86357
theorem R483569 : Reach 483569 := rs (se 2 (by rfl) ⟨181338, by rfl⟩) R362677
theorem R57587 : Reach 57587 := rs (se 1 (by rfl) ⟨43190, by rfl⟩) R86381
theorem R188675 : Reach 188675 := rs (se 1 (by rfl) ⟨141506, by rfl⟩) R283013
theorem R57603 : Reach 57603 := rs (se 1 (by rfl) ⟨43202, by rfl⟩) R86405
theorem R57619 : Reach 57619 := rs (se 1 (by rfl) ⟨43214, by rfl⟩) R86429
theorem R57635 : Reach 57635 := rs (se 1 (by rfl) ⟨43226, by rfl⟩) R86453
theorem R57651 : Reach 57651 := rs (se 1 (by rfl) ⟨43238, by rfl⟩) R86477
theorem R57667 : Reach 57667 := rs (se 1 (by rfl) ⟨43250, by rfl⟩) R86501
theorem R57683 : Reach 57683 := rs (se 1 (by rfl) ⟨43262, by rfl⟩) R86525
theorem R57699 : Reach 57699 := rs (se 1 (by rfl) ⟨43274, by rfl⟩) R86549
theorem R90467 : Reach 90467 := rs (se 1 (by rfl) ⟨67850, by rfl⟩) R135701
theorem R57715 : Reach 57715 := rs (se 1 (by rfl) ⟨43286, by rfl⟩) R86573
theorem R57731 : Reach 57731 := rs (se 1 (by rfl) ⟨43298, by rfl⟩) R86597
theorem R483725 : Reach 483725 := rs (se 3 (by rfl) ⟨90698, by rfl⟩) R181397
theorem R57747 : Reach 57747 := rs (se 1 (by rfl) ⟨43310, by rfl⟩) R86621
theorem R57763 : Reach 57763 := rs (se 1 (by rfl) ⟨43322, by rfl⟩) R86645
theorem R57779 : Reach 57779 := rs (se 1 (by rfl) ⟨43334, by rfl⟩) R86669
theorem R90563 : Reach 90563 := rs (se 1 (by rfl) ⟨67922, by rfl⟩) R135845
theorem R57795 : Reach 57795 := rs (se 1 (by rfl) ⟨43346, by rfl⟩) R86693
theorem R57811 : Reach 57811 := rs (se 1 (by rfl) ⟨43358, by rfl⟩) R86717
theorem R57827 : Reach 57827 := rs (se 1 (by rfl) ⟨43370, by rfl⟩) R86741
theorem R57843 : Reach 57843 := rs (se 1 (by rfl) ⟨43382, by rfl⟩) R86765
theorem R57859 : Reach 57859 := rs (se 1 (by rfl) ⟨43394, by rfl⟩) R86789
theorem R188945 : Reach 188945 := rs (se 2 (by rfl) ⟨70854, by rfl⟩) R141709
theorem R57875 : Reach 57875 := rs (se 1 (by rfl) ⟨43406, by rfl⟩) R86813
theorem R57891 : Reach 57891 := rs (se 1 (by rfl) ⟨43418, by rfl⟩) R86837
theorem R188963 : Reach 188963 := rs (se 1 (by rfl) ⟨141722, by rfl⟩) R283445
theorem R57907 : Reach 57907 := rs (se 1 (by rfl) ⟨43430, by rfl⟩) R86861
theorem R57923 : Reach 57923 := rs (se 1 (by rfl) ⟨43442, by rfl⟩) R86885
theorem R57939 : Reach 57939 := rs (se 1 (by rfl) ⟨43454, by rfl⟩) R86909
theorem R57955 : Reach 57955 := rs (se 1 (by rfl) ⟨43466, by rfl⟩) R86933
theorem R57971 : Reach 57971 := rs (se 1 (by rfl) ⟨43478, by rfl⟩) R86957
theorem R57987 : Reach 57987 := rs (se 1 (by rfl) ⟨43490, by rfl⟩) R86981
theorem R713357 : Reach 713357 := rs (se 3 (by rfl) ⟨133754, by rfl⟩) R267509
theorem R58003 : Reach 58003 := rs (se 1 (by rfl) ⟨43502, by rfl⟩) R87005
theorem R58019 : Reach 58019 := rs (se 1 (by rfl) ⟨43514, by rfl⟩) R87029
theorem R58035 : Reach 58035 := rs (se 1 (by rfl) ⟨43526, by rfl⟩) R87053
theorem R58051 : Reach 58051 := rs (se 1 (by rfl) ⟨43538, by rfl⟩) R87077
theorem R58067 : Reach 58067 := rs (se 1 (by rfl) ⟨43550, by rfl⟩) R87101
theorem R58083 : Reach 58083 := rs (se 1 (by rfl) ⟨43562, by rfl⟩) R87125
theorem R58099 : Reach 58099 := rs (se 1 (by rfl) ⟨43574, by rfl⟩) R87149
theorem R58115 : Reach 58115 := rs (se 1 (by rfl) ⟨43586, by rfl⟩) R87173
theorem R58131 : Reach 58131 := rs (se 1 (by rfl) ⟨43598, by rfl⟩) R87197
theorem R58147 : Reach 58147 := rs (se 1 (by rfl) ⟨43610, by rfl⟩) R87221
theorem R58163 : Reach 58163 := rs (se 1 (by rfl) ⟨43622, by rfl⟩) R87245
theorem R58179 : Reach 58179 := rs (se 1 (by rfl) ⟨43634, by rfl⟩) R87269
theorem R58195 : Reach 58195 := rs (se 1 (by rfl) ⟨43646, by rfl⟩) R87293
theorem R58211 : Reach 58211 := rs (se 1 (by rfl) ⟨43658, by rfl⟩) R87317
theorem R58227 : Reach 58227 := rs (se 1 (by rfl) ⟨43670, by rfl⟩) R87341
theorem R58243 : Reach 58243 := rs (se 1 (by rfl) ⟨43682, by rfl⟩) R87365
theorem R58259 : Reach 58259 := rs (se 1 (by rfl) ⟨43694, by rfl⟩) R87389
theorem R58275 : Reach 58275 := rs (se 1 (by rfl) ⟨43706, by rfl⟩) R87413
theorem R58291 : Reach 58291 := rs (se 1 (by rfl) ⟨43718, by rfl⟩) R87437
theorem R58307 : Reach 58307 := rs (se 1 (by rfl) ⟨43730, by rfl⟩) R87461
theorem R58323 : Reach 58323 := rs (se 1 (by rfl) ⟨43742, by rfl⟩) R87485
theorem R58339 : Reach 58339 := rs (se 1 (by rfl) ⟨43754, by rfl⟩) R87509
theorem R58355 : Reach 58355 := rs (se 1 (by rfl) ⟨43766, by rfl⟩) R87533
theorem R58371 : Reach 58371 := rs (se 1 (by rfl) ⟨43778, by rfl⟩) R87557
theorem R58387 : Reach 58387 := rs (se 1 (by rfl) ⟨43790, by rfl⟩) R87581
theorem R58403 : Reach 58403 := rs (se 1 (by rfl) ⟨43802, by rfl⟩) R87605
theorem R189485 : Reach 189485 := rs (se 3 (by rfl) ⟨35528, by rfl⟩) R71057
theorem R58419 : Reach 58419 := rs (se 1 (by rfl) ⟨43814, by rfl⟩) R87629
theorem R91201 : Reach 91201 := rs (se 2 (by rfl) ⟨34200, by rfl⟩) R68401
theorem R58435 : Reach 58435 := rs (se 1 (by rfl) ⟨43826, by rfl⟩) R87653
theorem R58451 : Reach 58451 := rs (se 1 (by rfl) ⟨43838, by rfl⟩) R87677
theorem R189539 : Reach 189539 := rs (se 1 (by rfl) ⟨142154, by rfl⟩) R284309
theorem R58467 : Reach 58467 := rs (se 1 (by rfl) ⟨43850, by rfl⟩) R87701
theorem R58483 : Reach 58483 := rs (se 1 (by rfl) ⟨43862, by rfl⟩) R87725
theorem R58499 : Reach 58499 := rs (se 1 (by rfl) ⟨43874, by rfl⟩) R87749
theorem R58515 : Reach 58515 := rs (se 1 (by rfl) ⟨43886, by rfl⟩) R87773
theorem R58531 : Reach 58531 := rs (se 1 (by rfl) ⟨43898, by rfl⟩) R87797
theorem R58547 : Reach 58547 := rs (se 1 (by rfl) ⟨43910, by rfl⟩) R87821
theorem R58563 : Reach 58563 := rs (se 1 (by rfl) ⟨43922, by rfl⟩) R87845
theorem R58579 : Reach 58579 := rs (se 1 (by rfl) ⟨43934, by rfl⟩) R87869
theorem R58595 : Reach 58595 := rs (se 1 (by rfl) ⟨43946, by rfl⟩) R87893
theorem R124145 : Reach 124145 := rs (se 2 (by rfl) ⟨46554, by rfl⟩) R93109
theorem R58611 : Reach 58611 := rs (se 1 (by rfl) ⟨43958, by rfl⟩) R87917
theorem R124163 : Reach 124163 := rs (se 1 (by rfl) ⟨93122, by rfl⟩) R186245
theorem R58627 : Reach 58627 := rs (se 1 (by rfl) ⟨43970, by rfl⟩) R87941
theorem R58643 : Reach 58643 := rs (se 1 (by rfl) ⟨43982, by rfl⟩) R87965
theorem R288035 : Reach 288035 := rs (se 1 (by rfl) ⟨216026, by rfl⟩) R432053
theorem R58659 : Reach 58659 := rs (se 1 (by rfl) ⟨43994, by rfl⟩) R87989
theorem R58675 : Reach 58675 := rs (se 1 (by rfl) ⟨44006, by rfl⟩) R88013
theorem R877877 : Reach 877877 := rs (se 5 (by rfl) ⟨41150, by rfl⟩) R82301
theorem R58691 : Reach 58691 := rs (se 1 (by rfl) ⟨44018, by rfl⟩) R88037
theorem R58707 : Reach 58707 := rs (se 1 (by rfl) ⟨44030, by rfl⟩) R88061
theorem R58723 : Reach 58723 := rs (se 1 (by rfl) ⟨44042, by rfl⟩) R88085
theorem R157037 : Reach 157037 := rs (se 3 (by rfl) ⟨29444, by rfl⟩) R58889
theorem R189809 : Reach 189809 := rs (se 2 (by rfl) ⟨71178, by rfl⟩) R142357
theorem R58739 : Reach 58739 := rs (se 1 (by rfl) ⟨44054, by rfl⟩) R88109
theorem R58755 : Reach 58755 := rs (se 1 (by rfl) ⟨44066, by rfl⟩) R88133
theorem R58771 : Reach 58771 := rs (se 1 (by rfl) ⟨44078, by rfl⟩) R88157
theorem R58787 : Reach 58787 := rs (se 1 (by rfl) ⟨44090, by rfl⟩) R88181
theorem R58803 : Reach 58803 := rs (se 1 (by rfl) ⟨44102, by rfl⟩) R88205
theorem R58819 : Reach 58819 := rs (se 1 (by rfl) ⟨44114, by rfl⟩) R88229
theorem R58835 : Reach 58835 := rs (se 1 (by rfl) ⟨44126, by rfl⟩) R88253
theorem R58851 : Reach 58851 := rs (se 1 (by rfl) ⟨44138, by rfl⟩) R88277
theorem R58867 : Reach 58867 := rs (se 1 (by rfl) ⟨44150, by rfl⟩) R88301
theorem R91649 : Reach 91649 := rs (se 2 (by rfl) ⟨34368, by rfl⟩) R68737
theorem R58883 : Reach 58883 := rs (se 1 (by rfl) ⟨44162, by rfl⟩) R88325
theorem R124433 : Reach 124433 := rs (se 2 (by rfl) ⟨46662, by rfl⟩) R93325
theorem R58899 : Reach 58899 := rs (se 1 (by rfl) ⟨44174, by rfl⟩) R88349
theorem R124451 : Reach 124451 := rs (se 1 (by rfl) ⟨93338, by rfl⟩) R186677
theorem R58915 : Reach 58915 := rs (se 1 (by rfl) ⟨44186, by rfl⟩) R88373
theorem R58931 : Reach 58931 := rs (se 1 (by rfl) ⟨44198, by rfl⟩) R88397
theorem R58947 : Reach 58947 := rs (se 1 (by rfl) ⟨44210, by rfl⟩) R88421
theorem R58963 : Reach 58963 := rs (se 1 (by rfl) ⟨44222, by rfl⟩) R88445
theorem R58979 : Reach 58979 := rs (se 1 (by rfl) ⟨44234, by rfl⟩) R88469
theorem R58995 : Reach 58995 := rs (se 1 (by rfl) ⟨44246, by rfl⟩) R88493
theorem R59011 : Reach 59011 := rs (se 1 (by rfl) ⟨44258, by rfl⟩) R88517
theorem R59027 : Reach 59027 := rs (se 1 (by rfl) ⟨44270, by rfl⟩) R88541
theorem R59043 : Reach 59043 := rs (se 1 (by rfl) ⟨44282, by rfl⟩) R88565
theorem R59059 : Reach 59059 := rs (se 1 (by rfl) ⟨44294, by rfl⟩) R88589
theorem R59075 : Reach 59075 := rs (se 1 (by rfl) ⟨44306, by rfl⟩) R88613
theorem R124625 : Reach 124625 := rs (se 2 (by rfl) ⟨46734, by rfl⟩) R93469
theorem R59091 : Reach 59091 := rs (se 1 (by rfl) ⟨44318, by rfl⟩) R88637
theorem R59107 : Reach 59107 := rs (se 1 (by rfl) ⟨44330, by rfl⟩) R88661
theorem R124721 : Reach 124721 := rs (se 2 (by rfl) ⟨46770, by rfl⟩) R93541
theorem R124739 : Reach 124739 := rs (se 1 (by rfl) ⟨93554, by rfl⟩) R187109
theorem R190349 : Reach 190349 := rs (se 3 (by rfl) ⟨35690, by rfl⟩) R71381
theorem R190403 : Reach 190403 := rs (se 1 (by rfl) ⟨142802, by rfl⟩) R285605
theorem R223181 : Reach 223181 := rs (se 3 (by rfl) ⟨41846, by rfl⟩) R83693
theorem R59459 : Reach 59459 := rs (se 1 (by rfl) ⟨44594, by rfl⟩) R89189
theorem R288845 : Reach 288845 := rs (se 3 (by rfl) ⟨54158, by rfl⟩) R108317
theorem R125009 : Reach 125009 := rs (se 2 (by rfl) ⟨46878, by rfl⟩) R93757
theorem R125027 : Reach 125027 := rs (se 1 (by rfl) ⟨93770, by rfl⟩) R187541
theorem R190673 : Reach 190673 := rs (se 2 (by rfl) ⟨71502, by rfl⟩) R143005
theorem R125155 : Reach 125155 := rs (se 1 (by rfl) ⟨93866, by rfl⟩) R187733
theorem R92515 : Reach 92515 := rs (se 1 (by rfl) ⟨69386, by rfl⟩) R138773
theorem R125297 : Reach 125297 := rs (se 2 (by rfl) ⟨46986, by rfl⟩) R93973
theorem R125315 : Reach 125315 := rs (se 1 (by rfl) ⟨93986, by rfl⟩) R187973
theorem R158125 : Reach 158125 := rs (se 3 (by rfl) ⟨29648, by rfl⟩) R59297
theorem R289379 : Reach 289379 := rs (se 1 (by rfl) ⟨217034, by rfl⟩) R434069
theorem R191089 : Reach 191089 := rs (se 2 (by rfl) ⟨71658, by rfl⟩) R143317
theorem R125585 : Reach 125585 := rs (se 2 (by rfl) ⟨47094, by rfl⟩) R94189
theorem R125603 : Reach 125603 := rs (se 1 (by rfl) ⟨94202, by rfl⟩) R188405
theorem R355013 : Reach 355013 := rs (se 4 (by rfl) ⟨33282, by rfl⟩) R66565
theorem R453347 : Reach 453347 := rs (se 1 (by rfl) ⟨340010, by rfl⟩) R680021
theorem R191203 : Reach 191203 := rs (se 1 (by rfl) ⟨143402, by rfl⟩) R286805
theorem R191213 : Reach 191213 := rs (se 3 (by rfl) ⟨35852, by rfl⟩) R71705
theorem R223985 : Reach 223985 := rs (se 2 (by rfl) ⟨83994, by rfl⟩) R167989
theorem R191267 : Reach 191267 := rs (se 1 (by rfl) ⟨143450, by rfl⟩) R286901
theorem R60211 : Reach 60211 := rs (se 1 (by rfl) ⟨45158, by rfl⟩) R90317
theorem R93089 : Reach 93089 := rs (se 2 (by rfl) ⟨34908, by rfl⟩) R69817
theorem R125873 : Reach 125873 := rs (se 2 (by rfl) ⟨47202, by rfl⟩) R94405
theorem R125891 : Reach 125891 := rs (se 1 (by rfl) ⟨94418, by rfl⟩) R188837
theorem R93187 : Reach 93187 := rs (se 1 (by rfl) ⟨69890, by rfl⟩) R139781
theorem R93217 : Reach 93217 := rs (se 2 (by rfl) ⟨34956, by rfl⟩) R69913
theorem R191537 : Reach 191537 := rs (se 2 (by rfl) ⟨71826, by rfl⟩) R143653
theorem R93233 : Reach 93233 := rs (se 2 (by rfl) ⟨34962, by rfl⟩) R69925
theorem R93251 : Reach 93251 := rs (se 1 (by rfl) ⟨69938, by rfl⟩) R139877
theorem R158897 : Reach 158897 := rs (se 2 (by rfl) ⟨59586, by rfl⟩) R119173
theorem R93379 : Reach 93379 := rs (se 1 (by rfl) ⟨70034, by rfl⟩) R140069
theorem R126161 : Reach 126161 := rs (se 2 (by rfl) ⟨47310, by rfl⟩) R94621
theorem R126179 : Reach 126179 := rs (se 1 (by rfl) ⟨94634, by rfl⟩) R189269
theorem R93521 : Reach 93521 := rs (se 2 (by rfl) ⟨35070, by rfl⟩) R70141
theorem R126353 : Reach 126353 := rs (se 2 (by rfl) ⟨47382, by rfl⟩) R94765
theorem R93649 : Reach 93649 := rs (se 2 (by rfl) ⟨35118, by rfl⟩) R70237
theorem R159185 : Reach 159185 := rs (se 2 (by rfl) ⟨59694, by rfl⟩) R119389
theorem R421361 : Reach 421361 := rs (se 2 (by rfl) ⟨158010, by rfl⟩) R316021
theorem R126449 : Reach 126449 := rs (se 2 (by rfl) ⟨47418, by rfl⟩) R94837
theorem R93683 : Reach 93683 := rs (se 1 (by rfl) ⟨70262, by rfl⟩) R140525
theorem R126467 : Reach 126467 := rs (se 1 (by rfl) ⟨94850, by rfl⟩) R189701
theorem R93745 : Reach 93745 := rs (se 2 (by rfl) ⟨35154, by rfl⟩) R70309
theorem R192077 : Reach 192077 := rs (se 3 (by rfl) ⟨36014, by rfl⟩) R72029
theorem R93811 : Reach 93811 := rs (se 1 (by rfl) ⟨70358, by rfl⟩) R140717
theorem R192131 : Reach 192131 := rs (se 1 (by rfl) ⟨144098, by rfl⟩) R288197
theorem R93889 : Reach 93889 := rs (se 2 (by rfl) ⟨35208, by rfl⟩) R70417
theorem R93953 : Reach 93953 := rs (se 2 (by rfl) ⟨35232, by rfl⟩) R70465
theorem R126737 : Reach 126737 := rs (se 2 (by rfl) ⟨47526, by rfl⟩) R95053
theorem R126755 : Reach 126755 := rs (se 1 (by rfl) ⟨95066, by rfl⟩) R190133
theorem R61219 : Reach 61219 := rs (se 1 (by rfl) ⟨45914, by rfl⟩) R91829
theorem R94081 : Reach 94081 := rs (se 2 (by rfl) ⟨35280, by rfl⟩) R70561
theorem R192401 : Reach 192401 := rs (se 2 (by rfl) ⟨72150, by rfl⟩) R144301
theorem R94115 : Reach 94115 := rs (se 1 (by rfl) ⟨70586, by rfl⟩) R141173
theorem R94243 : Reach 94243 := rs (se 1 (by rfl) ⟨70682, by rfl⟩) R141365
theorem R127025 : Reach 127025 := rs (se 2 (by rfl) ⟨47634, by rfl⟩) R95269
theorem R127043 : Reach 127043 := rs (se 1 (by rfl) ⟨95282, by rfl⟩) R190565
theorem R94289 : Reach 94289 := rs (se 2 (by rfl) ⟨35358, by rfl⟩) R70717
theorem R159857 : Reach 159857 := rs (se 2 (by rfl) ⟨59946, by rfl⟩) R119893
theorem R487565 : Reach 487565 := rs (se 3 (by rfl) ⟨91418, by rfl⟩) R182837
theorem R94385 : Reach 94385 := rs (se 2 (by rfl) ⟨35394, by rfl⟩) R70789
theorem R94513 : Reach 94513 := rs (se 2 (by rfl) ⟨35442, by rfl⟩) R70885
theorem R127313 : Reach 127313 := rs (se 2 (by rfl) ⟨47742, by rfl⟩) R95485
theorem R94547 : Reach 94547 := rs (se 1 (by rfl) ⟨70910, by rfl⟩) R141821
theorem R127331 : Reach 127331 := rs (se 1 (by rfl) ⟨95498, by rfl⟩) R190997
theorem R192941 : Reach 192941 := rs (se 3 (by rfl) ⟨36176, by rfl⟩) R72353
theorem R750005 : Reach 750005 := rs (se 5 (by rfl) ⟨35156, by rfl⟩) R70313
theorem R94675 : Reach 94675 := rs (se 1 (by rfl) ⟨71006, by rfl⟩) R142013
theorem R192995 : Reach 192995 := rs (se 1 (by rfl) ⟨144746, by rfl⟩) R289493
theorem R62003 : Reach 62003 := rs (se 1 (by rfl) ⟨46502, by rfl⟩) R93005
theorem R127555 : Reach 127555 := rs (se 1 (by rfl) ⟨95666, by rfl⟩) R191333
theorem R94817 : Reach 94817 := rs (se 2 (by rfl) ⟨35556, by rfl⟩) R71113
theorem R127601 : Reach 127601 := rs (se 2 (by rfl) ⟨47850, by rfl⟩) R95701
theorem R127619 : Reach 127619 := rs (se 1 (by rfl) ⟨95714, by rfl⟩) R191429
theorem R62131 : Reach 62131 := rs (se 1 (by rfl) ⟨46598, by rfl⟩) R93197
theorem R94945 : Reach 94945 := rs (se 2 (by rfl) ⟨35604, by rfl⟩) R71209
theorem R226019 : Reach 226019 := rs (se 1 (by rfl) ⟨169514, by rfl⟩) R339029
theorem R193265 : Reach 193265 := rs (se 2 (by rfl) ⟨72474, by rfl⟩) R144949
theorem R94979 : Reach 94979 := rs (se 1 (by rfl) ⟨71234, by rfl⟩) R142469
theorem R62227 : Reach 62227 := rs (se 1 (by rfl) ⟨46670, by rfl⟩) R93341
theorem R62275 : Reach 62275 := rs (se 1 (by rfl) ⟨46706, by rfl⟩) R93413
theorem R95107 : Reach 95107 := rs (se 1 (by rfl) ⟨71330, by rfl⟩) R142661
theorem R160643 : Reach 160643 := rs (se 1 (by rfl) ⟨120482, by rfl⟩) R240965
theorem R127889 : Reach 127889 := rs (se 2 (by rfl) ⟨47958, by rfl⟩) R95917
theorem R127907 : Reach 127907 := rs (se 1 (by rfl) ⟨95930, by rfl⟩) R191861
theorem R291761 : Reach 291761 := rs (se 2 (by rfl) ⟨109410, by rfl⟩) R218821
theorem R127921 : Reach 127921 := rs (se 2 (by rfl) ⟨47970, by rfl⟩) R95941
theorem R62419 : Reach 62419 := rs (se 1 (by rfl) ⟨46814, by rfl⟩) R93629
theorem R95203 : Reach 95203 := rs (se 1 (by rfl) ⟨71402, by rfl⟩) R142805
theorem R95249 : Reach 95249 := rs (se 2 (by rfl) ⟨35718, by rfl⟩) R71437
theorem R62563 : Reach 62563 := rs (se 1 (by rfl) ⟨46922, by rfl⟩) R93845
theorem R390277 : Reach 390277 := rs (se 4 (by rfl) ⟨36588, by rfl⟩) R73177
theorem R95377 : Reach 95377 := rs (se 2 (by rfl) ⟨35766, by rfl⟩) R71533
theorem R128177 : Reach 128177 := rs (se 2 (by rfl) ⟨48066, by rfl⟩) R96133
theorem R95411 : Reach 95411 := rs (se 1 (by rfl) ⟨71558, by rfl⟩) R143117
theorem R128195 : Reach 128195 := rs (se 1 (by rfl) ⟨96146, by rfl⟩) R192293
theorem R160973 : Reach 160973 := rs (se 3 (by rfl) ⟨30182, by rfl⟩) R60365
theorem R62707 : Reach 62707 := rs (se 1 (by rfl) ⟨47030, by rfl⟩) R94061
theorem R193805 : Reach 193805 := rs (se 3 (by rfl) ⟨36338, by rfl⟩) R72677
theorem R161041 : Reach 161041 := rs (se 2 (by rfl) ⟨60390, by rfl⟩) R120781
theorem R95539 : Reach 95539 := rs (se 1 (by rfl) ⟨71654, by rfl⟩) R143309
theorem R193859 : Reach 193859 := rs (se 1 (by rfl) ⟨145394, by rfl⟩) R290789
theorem R62851 : Reach 62851 := rs (se 1 (by rfl) ⟨47138, by rfl⟩) R94277
theorem R95681 : Reach 95681 := rs (se 2 (by rfl) ⟨35880, by rfl⟩) R71761
theorem R128465 : Reach 128465 := rs (se 2 (by rfl) ⟨48174, by rfl⟩) R96349
theorem R128483 : Reach 128483 := rs (se 1 (by rfl) ⟨96362, by rfl⟩) R192725
theorem R62995 : Reach 62995 := rs (se 1 (by rfl) ⟨47246, by rfl⟩) R94493
theorem R161315 : Reach 161315 := rs (se 1 (by rfl) ⟨120986, by rfl⟩) R241973
theorem R95809 : Reach 95809 := rs (se 2 (by rfl) ⟨35928, by rfl⟩) R71857
theorem R194129 : Reach 194129 := rs (se 2 (by rfl) ⟨72798, by rfl⟩) R145597
theorem R95843 : Reach 95843 := rs (se 1 (by rfl) ⟨71882, by rfl⟩) R143765
theorem R63139 : Reach 63139 := rs (se 1 (by rfl) ⟨47354, by rfl⟩) R94709
theorem R95971 : Reach 95971 := rs (se 1 (by rfl) ⟨71978, by rfl⟩) R143957
theorem R128753 : Reach 128753 := rs (se 2 (by rfl) ⟨48282, by rfl⟩) R96565
theorem R128771 : Reach 128771 := rs (se 1 (by rfl) ⟨96578, by rfl⟩) R193157
theorem R685837 : Reach 685837 := rs (se 3 (by rfl) ⟨128594, by rfl⟩) R257189
theorem R63283 : Reach 63283 := rs (se 1 (by rfl) ⟨47462, by rfl⟩) R94925
theorem R96113 : Reach 96113 := rs (se 2 (by rfl) ⟨36042, by rfl⟩) R72085
theorem R63427 : Reach 63427 := rs (se 1 (by rfl) ⟨47570, by rfl⟩) R95141
theorem R96241 : Reach 96241 := rs (se 2 (by rfl) ⟨36090, by rfl⟩) R72181
theorem R129041 : Reach 129041 := rs (se 2 (by rfl) ⟨48390, by rfl⟩) R96781
theorem R96275 : Reach 96275 := rs (se 1 (by rfl) ⟨72206, by rfl⟩) R144413
theorem R129059 : Reach 129059 := rs (se 1 (by rfl) ⟨96794, by rfl⟩) R193589
theorem R63571 : Reach 63571 := rs (se 1 (by rfl) ⟨47678, by rfl⟩) R95357
theorem R194669 : Reach 194669 := rs (se 3 (by rfl) ⟨36500, by rfl⟩) R73001
theorem R96403 : Reach 96403 := rs (se 1 (by rfl) ⟨72302, by rfl⟩) R144605
theorem R194723 : Reach 194723 := rs (se 1 (by rfl) ⟨146042, by rfl⟩) R292085
theorem R358577 : Reach 358577 := rs (se 2 (by rfl) ⟨134466, by rfl⟩) R268933
theorem R1308869 : Reach 1308869 := rs (se 4 (by rfl) ⟨122706, by rfl⟩) R245413
theorem R63715 : Reach 63715 := rs (se 1 (by rfl) ⟨47786, by rfl⟩) R95573
theorem R2291939 : Reach 2291939 := rs (se 1 (by rfl) ⟨1718954, by rfl⟩) R3437909
theorem R96545 : Reach 96545 := rs (se 2 (by rfl) ⟨36204, by rfl⟩) R72409
theorem R129329 : Reach 129329 := rs (se 2 (by rfl) ⟨48498, by rfl⟩) R96997
theorem R129347 : Reach 129347 := rs (se 1 (by rfl) ⟨97010, by rfl⟩) R194021
theorem R293219 : Reach 293219 := rs (se 1 (by rfl) ⟨219914, by rfl⟩) R439829
theorem R162157 : Reach 162157 := rs (se 3 (by rfl) ⟨30404, by rfl⟩) R60809
theorem R63859 : Reach 63859 := rs (se 1 (by rfl) ⟨47894, by rfl⟩) R95789
theorem R96673 : Reach 96673 := rs (se 2 (by rfl) ⟨36252, by rfl⟩) R72505
theorem R194993 : Reach 194993 := rs (se 2 (by rfl) ⟨73122, by rfl⟩) R146245
theorem R96707 : Reach 96707 := rs (se 1 (by rfl) ⟨72530, by rfl⟩) R145061
theorem R653795 : Reach 653795 := rs (se 1 (by rfl) ⟨490346, by rfl⟩) R980693
theorem R64003 : Reach 64003 := rs (se 1 (by rfl) ⟨48002, by rfl⟩) R96005
theorem R162317 : Reach 162317 := rs (se 3 (by rfl) ⟨30434, by rfl⟩) R60869
theorem R752141 : Reach 752141 := rs (se 3 (by rfl) ⟨141026, by rfl⟩) R282053
theorem R96835 : Reach 96835 := rs (se 1 (by rfl) ⟨72626, by rfl⟩) R145253
theorem R129617 : Reach 129617 := rs (se 2 (by rfl) ⟨48606, by rfl⟩) R97213
theorem R129635 : Reach 129635 := rs (se 1 (by rfl) ⟨97226, by rfl⟩) R194453
theorem R293489 : Reach 293489 := rs (se 2 (by rfl) ⟨110058, by rfl⟩) R220117
theorem R64147 : Reach 64147 := rs (se 1 (by rfl) ⟨48110, by rfl⟩) R96221
theorem R359075 : Reach 359075 := rs (se 1 (by rfl) ⟨269306, by rfl⟩) R538613
theorem R162499 : Reach 162499 := rs (se 1 (by rfl) ⟨121874, by rfl⟩) R243749
theorem R96977 : Reach 96977 := rs (se 2 (by rfl) ⟨36366, by rfl⟩) R72733
theorem R64291 : Reach 64291 := rs (se 1 (by rfl) ⟨48218, by rfl⟩) R96437
theorem R97105 : Reach 97105 := rs (se 2 (by rfl) ⟨36414, by rfl⟩) R72829
theorem R129905 : Reach 129905 := rs (se 2 (by rfl) ⟨48714, by rfl⟩) R97429
theorem R97139 : Reach 97139 := rs (se 1 (by rfl) ⟨72854, by rfl⟩) R145709
theorem R129923 : Reach 129923 := rs (se 1 (by rfl) ⟨97442, by rfl⟩) R194885
theorem R64435 : Reach 64435 := rs (se 1 (by rfl) ⟨48326, by rfl⟩) R96653
theorem R195533 : Reach 195533 := rs (se 3 (by rfl) ⟨36662, by rfl⟩) R73325
theorem R97267 : Reach 97267 := rs (se 1 (by rfl) ⟨72950, by rfl⟩) R145901
theorem R195587 : Reach 195587 := rs (se 1 (by rfl) ⟨146690, by rfl⟩) R293381
theorem R64579 : Reach 64579 := rs (se 1 (by rfl) ⟨48434, by rfl⟩) R96869
theorem R97409 : Reach 97409 := rs (se 2 (by rfl) ⟨36528, by rfl⟩) R73057
theorem R294029 : Reach 294029 := rs (se 3 (by rfl) ⟨55130, by rfl⟩) R110261
theorem R130193 : Reach 130193 := rs (se 2 (by rfl) ⟨48822, by rfl⟩) R97645
theorem R130211 : Reach 130211 := rs (se 1 (by rfl) ⟨97658, by rfl⟩) R195317
theorem R64723 : Reach 64723 := rs (se 1 (by rfl) ⟨48542, by rfl⟩) R97085
theorem R97537 : Reach 97537 := rs (se 2 (by rfl) ⟨36576, by rfl⟩) R73153
theorem R195857 : Reach 195857 := rs (se 2 (by rfl) ⟨73446, by rfl⟩) R146893
theorem R97571 : Reach 97571 := rs (se 1 (by rfl) ⟨73178, by rfl⟩) R146357
theorem R64867 : Reach 64867 := rs (se 1 (by rfl) ⟨48650, by rfl⟩) R97301
theorem R1441165 : Reach 1441165 := rs (se 3 (by rfl) ⟨270218, by rfl⟩) R540437
theorem R97699 : Reach 97699 := rs (se 1 (by rfl) ⟨73274, by rfl⟩) R146549
theorem R130481 : Reach 130481 := rs (se 2 (by rfl) ⟨48930, by rfl⟩) R97861
theorem R130499 : Reach 130499 := rs (se 1 (by rfl) ⟨97874, by rfl⟩) R195749
theorem R65011 : Reach 65011 := rs (se 1 (by rfl) ⟨48758, by rfl⟩) R97517
theorem R97841 : Reach 97841 := rs (se 2 (by rfl) ⟨36690, by rfl⟩) R73381
theorem R360035 : Reach 360035 := rs (se 1 (by rfl) ⟨270026, by rfl⟩) R540053
theorem R65155 : Reach 65155 := rs (se 1 (by rfl) ⟨48866, by rfl⟩) R97733
theorem R97969 : Reach 97969 := rs (se 2 (by rfl) ⟨36738, by rfl⟩) R73477
theorem R130769 : Reach 130769 := rs (se 2 (by rfl) ⟨49038, by rfl⟩) R98077
theorem R130787 : Reach 130787 := rs (se 1 (by rfl) ⟨98090, by rfl⟩) R196181
theorem R65299 : Reach 65299 := rs (se 1 (by rfl) ⟨48974, by rfl⟩) R97949
theorem R196451 : Reach 196451 := rs (se 1 (by rfl) ⟨147338, by rfl⟩) R294677
theorem R65443 : Reach 65443 := rs (se 1 (by rfl) ⟨49082, by rfl⟩) R98165
theorem R131057 : Reach 131057 := rs (se 2 (by rfl) ⟨49146, by rfl⟩) R98293
theorem R98327 : Reach 98327 := rs (se 1 (by rfl) ⟨73745, by rfl⟩) R147491
theorem R131147 : Reach 131147 := rs (se 1 (by rfl) ⟨98360, by rfl⟩) R196721
theorem R65623 : Reach 65623 := rs (se 1 (by rfl) ⟨49217, by rfl⟩) R98435
theorem R983171 : Reach 983171 := rs (se 1 (by rfl) ⟨737378, by rfl⟩) R1474757
theorem R98455 : Reach 98455 := rs (se 1 (by rfl) ⟨73841, by rfl⟩) R147683
theorem R196829 : Reach 196829 := rs (se 3 (by rfl) ⟨36905, by rfl⟩) R73811
theorem R65803 : Reach 65803 := rs (se 1 (by rfl) ⟨49352, by rfl⟩) R98705
theorem R131417 : Reach 131417 := rs (se 2 (by rfl) ⟨49281, by rfl⟩) R98563
theorem R131507 : Reach 131507 := rs (se 1 (by rfl) ⟨98630, by rfl⟩) R197261
theorem R197081 : Reach 197081 := rs (se 2 (by rfl) ⟨73905, by rfl⟩) R147811
theorem R557603 : Reach 557603 := rs (se 1 (by rfl) ⟨418202, by rfl⟩) R836405
theorem R98867 : Reach 98867 := rs (se 1 (by rfl) ⟨74150, by rfl⟩) R148301
theorem R787013 : Reach 787013 := rs (se 4 (by rfl) ⟨73782, by rfl⟩) R147565
theorem R361061 : Reach 361061 := rs (se 4 (by rfl) ⟨33849, by rfl⟩) R67699
theorem R66199 : Reach 66199 := rs (se 1 (by rfl) ⟨49649, by rfl⟩) R99299
theorem R98995 : Reach 98995 := rs (se 1 (by rfl) ⟨74246, by rfl⟩) R148493
theorem R131777 : Reach 131777 := rs (se 2 (by rfl) ⟨49416, by rfl⟩) R98833
theorem R99083 : Reach 99083 := rs (se 1 (by rfl) ⟨74312, by rfl⟩) R148625
theorem R99137 : Reach 99137 := rs (se 2 (by rfl) ⟨37176, by rfl⟩) R74353
theorem R66379 : Reach 66379 := rs (se 1 (by rfl) ⟨49784, by rfl⟩) R99569
theorem R394085 : Reach 394085 := rs (se 4 (by rfl) ⟨36945, by rfl⟩) R73891
theorem R623477 : Reach 623477 := rs (se 5 (by rfl) ⟨29225, by rfl⟩) R58451
theorem R295811 : Reach 295811 := rs (se 1 (by rfl) ⟨221858, by rfl⟩) R443717
theorem R99211 : Reach 99211 := rs (se 1 (by rfl) ⟨74408, by rfl⟩) R148817
theorem R99265 : Reach 99265 := rs (se 2 (by rfl) ⟨37224, by rfl⟩) R74449
theorem R132119 : Reach 132119 := rs (se 1 (by rfl) ⟨99089, by rfl⟩) R198179
theorem R99353 : Reach 99353 := rs (se 2 (by rfl) ⟨37257, by rfl⟩) R74515
theorem R99415 : Reach 99415 := rs (se 1 (by rfl) ⟨74561, by rfl⟩) R149123
theorem R99481 : Reach 99481 := rs (se 2 (by rfl) ⟨37305, by rfl⟩) R74611
theorem R132299 : Reach 132299 := rs (se 1 (by rfl) ⟨99224, by rfl⟩) R198449
theorem R197963 : Reach 197963 := rs (se 1 (by rfl) ⟨148472, by rfl⟩) R296945
theorem R99787 : Reach 99787 := rs (se 1 (by rfl) ⟨74840, by rfl⟩) R149681
theorem R132569 : Reach 132569 := rs (se 2 (by rfl) ⟨49713, by rfl⟩) R99427
theorem R165341 : Reach 165341 := rs (se 3 (by rfl) ⟨31001, by rfl⟩) R62003
theorem R132659 : Reach 132659 := rs (se 1 (by rfl) ⟨99494, by rfl⟩) R198989
theorem R198233 : Reach 198233 := rs (se 2 (by rfl) ⟨74337, by rfl⟩) R148675
theorem R132929 : Reach 132929 := rs (se 2 (by rfl) ⟨49848, by rfl⟩) R99697
theorem R133015 : Reach 133015 := rs (se 1 (by rfl) ⟨99761, by rfl⟩) R199523
theorem R198935 : Reach 198935 := rs (se 1 (by rfl) ⟨149201, by rfl⟩) R298403
theorem R166195 : Reach 166195 := rs (se 1 (by rfl) ⟨124646, by rfl⟩) R249293
theorem R231731 : Reach 231731 := rs (se 1 (by rfl) ⟨173798, by rfl⟩) R347597
theorem R199043 : Reach 199043 := rs (se 1 (by rfl) ⟨149282, by rfl⟩) R298565
theorem R166475 : Reach 166475 := rs (se 1 (by rfl) ⟨124856, by rfl⟩) R249713
theorem R199313 : Reach 199313 := rs (se 2 (by rfl) ⟨74742, by rfl⟩) R149485
theorem R330419 : Reach 330419 := rs (se 1 (by rfl) ⟨247814, by rfl⟩) R495629
theorem R199475 : Reach 199475 := rs (se 1 (by rfl) ⟨149606, by rfl⟩) R299213
theorem R166873 : Reach 166873 := rs (se 2 (by rfl) ⟨62577, by rfl⟩) R125155
theorem R232523 : Reach 232523 := rs (se 1 (by rfl) ⟨174392, by rfl⟩) R348785
theorem R1019141 : Reach 1019141 := rs (se 4 (by rfl) ⟨95544, by rfl⟩) R191089
theorem R68887 : Reach 68887 := rs (se 1 (by rfl) ⟨51665, by rfl⟩) R103331
theorem R69079 : Reach 69079 := rs (se 1 (by rfl) ⟨51809, by rfl⟩) R103619
theorem R462941 : Reach 462941 := rs (se 3 (by rfl) ⟨86801, by rfl⟩) R173603
theorem R331877 : Reach 331877 := rs (se 4 (by rfl) ⟨31113, by rfl⟩) R62227
theorem R168115 : Reach 168115 := rs (se 1 (by rfl) ⟨126086, by rfl⟩) R252173
theorem R889379 : Reach 889379 := rs (se 1 (by rfl) ⟨667034, by rfl⟩) R1334069
theorem R332333 : Reach 332333 := rs (se 3 (by rfl) ⟨62312, by rfl⟩) R124625
theorem R70679 : Reach 70679 := rs (se 1 (by rfl) ⟨53009, by rfl⟩) R106019
theorem R333017 : Reach 333017 := rs (se 2 (by rfl) ⟨124881, by rfl⟩) R249763
theorem R136513 : Reach 136513 := rs (se 2 (by rfl) ⟨51192, by rfl⟩) R102385
theorem R103769 : Reach 103769 := rs (se 2 (by rfl) ⟨38913, by rfl⟩) R77827
theorem R71371 : Reach 71371 := rs (se 1 (by rfl) ⟨53528, by rfl⟩) R107057
theorem R1087181 : Reach 1087181 := rs (se 3 (by rfl) ⟨203846, by rfl⟩) R407693
theorem R202925 : Reach 202925 := rs (se 3 (by rfl) ⟨38048, by rfl⟩) R76097
theorem R104665 : Reach 104665 := rs (se 2 (by rfl) ⟨39249, by rfl⟩) R78499
theorem R268609 : Reach 268609 := rs (se 2 (by rfl) ⟨100728, by rfl⟩) R201457
theorem R170561 : Reach 170561 := rs (se 2 (by rfl) ⟨63960, by rfl⟩) R127921
theorem R203357 : Reach 203357 := rs (se 3 (by rfl) ⟨38129, by rfl⟩) R76259
theorem R72343 : Reach 72343 := rs (se 1 (by rfl) ⟨54257, by rfl⟩) R108515
theorem R105113 : Reach 105113 := rs (se 2 (by rfl) ⟨39417, by rfl⟩) R78835
theorem R236333 : Reach 236333 := rs (se 3 (by rfl) ⟨44312, by rfl⟩) R88625
theorem R236675 : Reach 236675 := rs (se 1 (by rfl) ⟨177506, by rfl⟩) R355013
theorem R302231 : Reach 302231 := rs (se 1 (by rfl) ⟨226673, by rfl⟩) R453347
theorem R105857 : Reach 105857 := rs (se 2 (by rfl) ⟨39696, by rfl⟩) R79393
theorem R73111 : Reach 73111 := rs (se 1 (by rfl) ⟨54833, by rfl⟩) R109667
theorem R138647 : Reach 138647 := rs (se 1 (by rfl) ⟨103985, by rfl⟩) R207971
theorem R499121 : Reach 499121 := rs (se 2 (by rfl) ⟨187170, by rfl⟩) R374341
theorem R73163 : Reach 73163 := rs (se 1 (by rfl) ⟨54872, by rfl⟩) R109745
theorem R105931 : Reach 105931 := rs (se 1 (by rfl) ⟨79448, by rfl⟩) R158897
theorem R106123 : Reach 106123 := rs (se 1 (by rfl) ⟨79592, by rfl⟩) R159185
theorem R204481 : Reach 204481 := rs (se 2 (by rfl) ⟨76680, by rfl⟩) R153361
theorem R138955 : Reach 138955 := rs (se 1 (by rfl) ⟨104216, by rfl⟩) R208433
theorem R499729 : Reach 499729 := rs (se 2 (by rfl) ⟨187398, by rfl⟩) R374797
theorem R106571 : Reach 106571 := rs (se 1 (by rfl) ⟨79928, by rfl⟩) R159857
theorem R73867 : Reach 73867 := rs (se 1 (by rfl) ⟨55400, by rfl⟩) R110801
theorem R1614005 : Reach 1614005 := rs (se 5 (by rfl) ⟨75656, by rfl⟩) R151313
theorem R139457 : Reach 139457 := rs (se 2 (by rfl) ⟨52296, by rfl⟩) R104593
theorem R106753 : Reach 106753 := rs (se 2 (by rfl) ⟨40032, by rfl⟩) R80065
theorem R500003 : Reach 500003 := rs (se 1 (by rfl) ⟨375002, by rfl⟩) R750005
theorem R74135 : Reach 74135 := rs (se 1 (by rfl) ⟨55601, by rfl⟩) R111203
theorem R631313 : Reach 631313 := rs (se 2 (by rfl) ⟨236742, by rfl⟩) R473485
theorem R107095 : Reach 107095 := rs (se 1 (by rfl) ⟨80321, by rfl⟩) R160643
theorem R139927 : Reach 139927 := rs (se 1 (by rfl) ⟨104945, by rfl⟩) R209891
theorem R107315 : Reach 107315 := rs (se 1 (by rfl) ⟨80486, by rfl⟩) R160973
theorem R500741 : Reach 500741 := rs (se 4 (by rfl) ⟨46944, by rfl⟩) R93889
theorem R107543 : Reach 107543 := rs (se 1 (by rfl) ⟨80657, by rfl⟩) R161315
theorem R140363 : Reach 140363 := rs (se 1 (by rfl) ⟨105272, by rfl⟩) R210545
theorem R205955 : Reach 205955 := rs (se 1 (by rfl) ⟨154466, by rfl⟩) R308933
theorem R369937 : Reach 369937 := rs (se 2 (by rfl) ⟨138726, by rfl⟩) R277453
theorem R107801 : Reach 107801 := rs (se 2 (by rfl) ⟨40425, by rfl⟩) R80851
theorem R140737 : Reach 140737 := rs (se 2 (by rfl) ⟨52776, by rfl⟩) R105553
theorem R239051 : Reach 239051 := rs (se 1 (by rfl) ⟨179288, by rfl⟩) R358577
theorem R107993 : Reach 107993 := rs (se 2 (by rfl) ⟨40497, by rfl⟩) R80995
theorem R435863 : Reach 435863 := rs (se 1 (by rfl) ⟨326897, by rfl⟩) R653795
theorem R108211 : Reach 108211 := rs (se 1 (by rfl) ⟨81158, by rfl⟩) R162317
theorem R501427 : Reach 501427 := rs (se 1 (by rfl) ⟨376070, by rfl⟩) R752141
theorem R239383 : Reach 239383 := rs (se 1 (by rfl) ⟨179537, by rfl⟩) R359075
theorem R141107 : Reach 141107 := rs (se 1 (by rfl) ⟨105830, by rfl⟩) R211661
theorem R141335 : Reach 141335 := rs (se 1 (by rfl) ⟨106001, by rfl⟩) R212003
theorem R108697 : Reach 108697 := rs (se 2 (by rfl) ⟨40761, by rfl⟩) R81523
theorem R338251 : Reach 338251 := rs (se 1 (by rfl) ⟨253688, by rfl⟩) R507377
theorem R240023 : Reach 240023 := rs (se 1 (by rfl) ⟨180017, by rfl⟩) R360035
theorem R272857 : Reach 272857 := rs (se 2 (by rfl) ⟨102321, by rfl⟩) R204643
theorem R404003 : Reach 404003 := rs (se 1 (by rfl) ⟨303002, by rfl⟩) R606005
theorem R436913 : Reach 436913 := rs (se 2 (by rfl) ⟨163842, by rfl⟩) R327685
theorem R109259 : Reach 109259 := rs (se 1 (by rfl) ⟨81944, by rfl⟩) R163889
theorem R142145 : Reach 142145 := rs (se 2 (by rfl) ⟨53304, by rfl⟩) R106609
theorem R273227 : Reach 273227 := rs (se 1 (by rfl) ⟨204920, by rfl⟩) R409841
theorem R109441 : Reach 109441 := rs (se 2 (by rfl) ⟨41040, by rfl⟩) R82081
theorem R240691 : Reach 240691 := rs (se 1 (by rfl) ⟨180518, by rfl⟩) R361037
theorem R437399 : Reach 437399 := rs (se 1 (by rfl) ⟨328049, by rfl⟩) R656099
theorem R142681 : Reach 142681 := rs (se 2 (by rfl) ⟨53505, by rfl⟩) R107011
theorem R634229 : Reach 634229 := rs (se 5 (by rfl) ⟨29729, by rfl⟩) R59459
theorem R372185 : Reach 372185 := rs (se 2 (by rfl) ⟨139569, by rfl⟩) R279139
theorem R110155 : Reach 110155 := rs (se 1 (by rfl) ⟨82616, by rfl⟩) R165233
theorem R110231 : Reach 110231 := rs (se 1 (by rfl) ⟨82673, by rfl⟩) R165347
theorem R241501 : Reach 241501 := rs (se 3 (by rfl) ⟨45281, by rfl⟩) R90563
theorem R241937 : Reach 241937 := rs (se 2 (by rfl) ⟨90726, by rfl⟩) R181453
theorem R110899 : Reach 110899 := rs (se 1 (by rfl) ⟨83174, by rfl⟩) R166349
theorem R143795 : Reach 143795 := rs (se 1 (by rfl) ⟨107846, by rfl⟩) R215693
theorem R111127 : Reach 111127 := rs (se 1 (by rfl) ⟨83345, by rfl⟩) R166691
theorem R111233 : Reach 111233 := rs (se 2 (by rfl) ⟨41712, by rfl⟩) R83425
theorem R209587 : Reach 209587 := rs (se 1 (by rfl) ⟨157190, by rfl⟩) R314381
theorem R144089 : Reach 144089 := rs (se 2 (by rfl) ⟨54033, by rfl⟩) R108067
theorem R111385 : Reach 111385 := rs (se 2 (by rfl) ⟨41769, by rfl⟩) R83539
theorem R439427 : Reach 439427 := rs (se 1 (by rfl) ⟨329570, by rfl⟩) R659141
theorem R79051 : Reach 79051 := rs (se 1 (by rfl) ⟨59288, by rfl⟩) R118577
theorem R406885 : Reach 406885 := rs (se 4 (by rfl) ⟨38145, by rfl⟩) R76291
theorem R79319 : Reach 79319 := rs (se 1 (by rfl) ⟨59489, by rfl⟩) R118979
theorem R177815 : Reach 177815 := rs (se 1 (by rfl) ⟨133361, by rfl⟩) R266723
theorem R1357667 : Reach 1357667 := rs (se 1 (by rfl) ⟨1018250, by rfl⟩) R2036501
theorem R210833 : Reach 210833 := rs (se 2 (by rfl) ⟨79062, by rfl⟩) R158125
theorem R145739 : Reach 145739 := rs (se 1 (by rfl) ⟨109304, by rfl⟩) R218609
theorem R80281 : Reach 80281 := rs (se 2 (by rfl) ⟨30105, by rfl⟩) R60211
theorem R211531 : Reach 211531 := rs (se 1 (by rfl) ⟨158648, by rfl⟩) R317297
theorem R244397 : Reach 244397 := rs (se 3 (by rfl) ⟨45824, by rfl⟩) R91649
theorem R375617 : Reach 375617 := rs (se 2 (by rfl) ⟨140856, by rfl⟩) R281713
theorem R211805 : Reach 211805 := rs (se 3 (by rfl) ⟨39713, by rfl⟩) R79427
theorem R179147 : Reach 179147 := rs (se 1 (by rfl) ⟨134360, by rfl⟩) R268721
theorem R146711 : Reach 146711 := rs (se 1 (by rfl) ⟨110033, by rfl⟩) R220067
theorem R474443 : Reach 474443 := rs (se 1 (by rfl) ⟨355832, by rfl⟩) R711665
theorem R245081 : Reach 245081 := rs (se 2 (by rfl) ⟨91905, by rfl⟩) R183811
theorem R4078997 : Reach 4078997 := rs (se 6 (by rfl) ⟨95601, by rfl⟩) R191203
theorem R212503 : Reach 212503 := rs (se 1 (by rfl) ⟨159377, by rfl⟩) R318755
theorem R81739 : Reach 81739 := rs (se 1 (by rfl) ⟨61304, by rfl⟩) R122609
theorem R81751 : Reach 81751 := rs (se 1 (by rfl) ⟨61313, by rfl⟩) R122627
theorem R147379 : Reach 147379 := rs (se 1 (by rfl) ⟨110534, by rfl⟩) R221069
theorem R147521 : Reach 147521 := rs (se 2 (by rfl) ⟨55320, by rfl⟩) R110641
theorem R147545 : Reach 147545 := rs (se 2 (by rfl) ⟨55329, by rfl⟩) R110659
theorem R213293 : Reach 213293 := rs (se 3 (by rfl) ⟨39992, by rfl⟩) R79985
theorem R475571 : Reach 475571 := rs (se 1 (by rfl) ⟨356678, by rfl⟩) R713357
theorem R180787 : Reach 180787 := rs (se 1 (by rfl) ⟨135590, by rfl⟩) R271181
theorem R246347 : Reach 246347 := rs (se 1 (by rfl) ⟨184760, by rfl⟩) R369521
theorem R377419 : Reach 377419 := rs (se 1 (by rfl) ⟨283064, by rfl⟩) R566129
theorem R180929 : Reach 180929 := rs (se 2 (by rfl) ⟨67848, by rfl⟩) R135697
theorem R2081477 : Reach 2081477 := rs (se 4 (by rfl) ⟨195138, by rfl⟩) R390277
theorem R148189 : Reach 148189 := rs (se 3 (by rfl) ⟨27785, by rfl⟩) R55571
theorem R181043 : Reach 181043 := rs (se 1 (by rfl) ⟨135782, by rfl⟩) R271565
theorem R82763 : Reach 82763 := rs (se 1 (by rfl) ⟨62072, by rfl⟩) R124145
theorem R82775 : Reach 82775 := rs (se 1 (by rfl) ⟨62081, by rfl⟩) R124163
theorem R279389 : Reach 279389 := rs (se 3 (by rfl) ⟨52385, by rfl⟩) R104771
theorem R82841 : Reach 82841 := rs (se 2 (by rfl) ⟨31065, by rfl⟩) R62131
theorem R246721 : Reach 246721 := rs (se 2 (by rfl) ⟨92520, by rfl⟩) R185041
theorem R82955 : Reach 82955 := rs (se 1 (by rfl) ⟨62216, by rfl⟩) R124433
theorem R82967 : Reach 82967 := rs (se 1 (by rfl) ⟨62225, by rfl⟩) R124451
theorem R83033 : Reach 83033 := rs (se 2 (by rfl) ⟨31137, by rfl⟩) R62275
theorem R83147 : Reach 83147 := rs (se 1 (by rfl) ⟨62360, by rfl⟩) R124721
theorem R83159 : Reach 83159 := rs (se 1 (by rfl) ⟨62369, by rfl⟩) R124739
theorem R247063 : Reach 247063 := rs (se 1 (by rfl) ⟨185297, by rfl⟩) R370595
theorem R83225 : Reach 83225 := rs (se 2 (by rfl) ⟨31209, by rfl⟩) R62419
theorem R148787 : Reach 148787 := rs (se 1 (by rfl) ⟨111590, by rfl⟩) R223181
theorem R83339 : Reach 83339 := rs (se 1 (by rfl) ⟨62504, by rfl⟩) R125009
theorem R83351 : Reach 83351 := rs (se 1 (by rfl) ⟨62513, by rfl⟩) R125027
theorem R83417 : Reach 83417 := rs (se 2 (by rfl) ⟨31281, by rfl⟩) R62563
theorem R83531 : Reach 83531 := rs (se 1 (by rfl) ⟨62648, by rfl⟩) R125297
theorem R83543 : Reach 83543 := rs (se 1 (by rfl) ⟨62657, by rfl⟩) R125315
theorem R116311 : Reach 116311 := rs (se 1 (by rfl) ⟨87233, by rfl⟩) R174467
theorem R771677 : Reach 771677 := rs (se 3 (by rfl) ⟨144689, by rfl⟩) R289379
theorem R83609 : Reach 83609 := rs (se 2 (by rfl) ⟨31353, by rfl⟩) R62707
theorem R214721 : Reach 214721 := rs (se 2 (by rfl) ⟨80520, by rfl⟩) R161041
theorem R83723 : Reach 83723 := rs (se 1 (by rfl) ⟨62792, by rfl⟩) R125585
theorem R83735 : Reach 83735 := rs (se 1 (by rfl) ⟨62801, by rfl⟩) R125603
theorem R149323 : Reach 149323 := rs (se 1 (by rfl) ⟨111992, by rfl⟩) R223985
theorem R83801 : Reach 83801 := rs (se 2 (by rfl) ⟨31425, by rfl⟩) R62851
theorem R83915 : Reach 83915 := rs (se 1 (by rfl) ⟨62936, by rfl⟩) R125873
theorem R83927 : Reach 83927 := rs (se 1 (by rfl) ⟨62945, by rfl⟩) R125891
theorem R149465 : Reach 149465 := rs (se 2 (by rfl) ⟨56049, by rfl⟩) R112099
theorem R83993 : Reach 83993 := rs (se 2 (by rfl) ⟨31497, by rfl⟩) R62995
theorem R968773 : Reach 968773 := rs (se 4 (by rfl) ⟨90822, by rfl⟩) R181645
theorem R149597 : Reach 149597 := rs (se 3 (by rfl) ⟨28049, by rfl⟩) R56099
theorem R84107 : Reach 84107 := rs (se 1 (by rfl) ⟨63080, by rfl⟩) R126161
theorem R84119 : Reach 84119 := rs (se 1 (by rfl) ⟨63089, by rfl⟩) R126179
theorem R84185 : Reach 84185 := rs (se 2 (by rfl) ⟨31569, by rfl⟩) R63139
theorem R84235 : Reach 84235 := rs (se 1 (by rfl) ⟨63176, by rfl⟩) R126353
theorem R444689 : Reach 444689 := rs (se 2 (by rfl) ⟨166758, by rfl⟩) R333517
theorem R2836781 : Reach 2836781 := rs (se 3 (by rfl) ⟨531896, by rfl⟩) R1063793
theorem R280907 : Reach 280907 := rs (se 1 (by rfl) ⟨210680, by rfl⟩) R421361
theorem R84299 : Reach 84299 := rs (se 1 (by rfl) ⟨63224, by rfl⟩) R126449
theorem R84311 : Reach 84311 := rs (se 1 (by rfl) ⟨63233, by rfl⟩) R126467
theorem R84377 : Reach 84377 := rs (se 2 (by rfl) ⟨31641, by rfl⟩) R63283
theorem R444851 : Reach 444851 := rs (se 1 (by rfl) ⟨333638, by rfl⟩) R667277
theorem R84491 : Reach 84491 := rs (se 1 (by rfl) ⟨63368, by rfl⟩) R126737
theorem R84503 : Reach 84503 := rs (se 1 (by rfl) ⟨63377, by rfl⟩) R126755
theorem R84569 : Reach 84569 := rs (se 2 (by rfl) ⟨31713, by rfl⟩) R63427
theorem R84683 : Reach 84683 := rs (se 1 (by rfl) ⟨63512, by rfl⟩) R127025
theorem R84695 : Reach 84695 := rs (se 1 (by rfl) ⟨63521, by rfl⟩) R127043
theorem R84761 : Reach 84761 := rs (se 2 (by rfl) ⟨31785, by rfl⟩) R63571
theorem R84875 : Reach 84875 := rs (se 1 (by rfl) ⟨63656, by rfl⟩) R127313
theorem R84887 : Reach 84887 := rs (se 1 (by rfl) ⟨63665, by rfl⟩) R127331
theorem R84953 : Reach 84953 := rs (se 2 (by rfl) ⟨31857, by rfl⟩) R63715
theorem R85067 : Reach 85067 := rs (se 1 (by rfl) ⟨63800, by rfl⟩) R127601
theorem R85079 : Reach 85079 := rs (se 1 (by rfl) ⟨63809, by rfl⟩) R127619
theorem R216209 : Reach 216209 := rs (se 2 (by rfl) ⟨81078, by rfl⟩) R162157
theorem R117911 : Reach 117911 := rs (se 1 (by rfl) ⟨88433, by rfl⟩) R176867
theorem R150679 : Reach 150679 := rs (se 1 (by rfl) ⟨113009, by rfl⟩) R226019
theorem R85145 : Reach 85145 := rs (se 2 (by rfl) ⟨31929, by rfl⟩) R63859
theorem R85259 : Reach 85259 := rs (se 1 (by rfl) ⟨63944, by rfl⟩) R127889
theorem R85271 : Reach 85271 := rs (se 1 (by rfl) ⟨63953, by rfl⟩) R127907
theorem R118091 : Reach 118091 := rs (se 1 (by rfl) ⟨88568, by rfl⟩) R177137
theorem R85337 : Reach 85337 := rs (se 2 (by rfl) ⟨32001, by rfl⟩) R64003
theorem R85451 : Reach 85451 := rs (se 1 (by rfl) ⟨64088, by rfl⟩) R128177
theorem R85463 : Reach 85463 := rs (se 1 (by rfl) ⟨64097, by rfl⟩) R128195
theorem R85529 : Reach 85529 := rs (se 2 (by rfl) ⟨32073, by rfl⟩) R64147
theorem R216665 : Reach 216665 := rs (se 2 (by rfl) ⟨81249, by rfl⟩) R162499
theorem R839261 : Reach 839261 := rs (se 3 (by rfl) ⟨157361, by rfl⟩) R314723
theorem R85643 : Reach 85643 := rs (se 1 (by rfl) ⟨64232, by rfl⟩) R128465
theorem R85655 : Reach 85655 := rs (se 1 (by rfl) ⟨64241, by rfl⟩) R128483
theorem R85721 : Reach 85721 := rs (se 2 (by rfl) ⟨32145, by rfl⟩) R64291
theorem R282329 : Reach 282329 := rs (se 2 (by rfl) ⟨105873, by rfl⟩) R211747
theorem R216877 : Reach 216877 := rs (se 3 (by rfl) ⟨40664, by rfl⟩) R81329
theorem R85835 : Reach 85835 := rs (se 1 (by rfl) ⟨64376, by rfl⟩) R128753
theorem R85847 : Reach 85847 := rs (se 1 (by rfl) ⟨64385, by rfl⟩) R128771
theorem R511895 : Reach 511895 := rs (se 1 (by rfl) ⟨383921, by rfl⟩) R767843
theorem R85913 : Reach 85913 := rs (se 2 (by rfl) ⟨32217, by rfl⟩) R64435
theorem R86027 : Reach 86027 := rs (se 1 (by rfl) ⟨64520, by rfl⟩) R129041
theorem R86039 : Reach 86039 := rs (se 1 (by rfl) ⟨64529, by rfl⟩) R129059
theorem R282689 : Reach 282689 := rs (se 2 (by rfl) ⟨106008, by rfl⟩) R212017
theorem R86105 : Reach 86105 := rs (se 2 (by rfl) ⟨32289, by rfl⟩) R64579
theorem R217181 : Reach 217181 := rs (se 3 (by rfl) ⟨40721, by rfl⟩) R81443
theorem R872579 : Reach 872579 := rs (se 1 (by rfl) ⟨654434, by rfl⟩) R1308869
theorem R1527959 : Reach 1527959 := rs (se 1 (by rfl) ⟨1145969, by rfl⟩) R2291939
theorem R86219 : Reach 86219 := rs (se 1 (by rfl) ⟨64664, by rfl⟩) R129329
theorem R86231 : Reach 86231 := rs (se 1 (by rfl) ⟨64673, by rfl⟩) R129347
theorem R86297 : Reach 86297 := rs (se 2 (by rfl) ⟨32361, by rfl⟩) R64723
theorem R86411 : Reach 86411 := rs (se 1 (by rfl) ⟨64808, by rfl⟩) R129617
theorem R86423 : Reach 86423 := rs (se 1 (by rfl) ⟨64817, by rfl⟩) R129635
theorem R86489 : Reach 86489 := rs (se 2 (by rfl) ⟨32433, by rfl⟩) R64867
theorem R1921553 : Reach 1921553 := rs (se 2 (by rfl) ⟨720582, by rfl⟩) R1441165
theorem R86603 : Reach 86603 := rs (se 1 (by rfl) ⟨64952, by rfl⟩) R129905
theorem R86615 : Reach 86615 := rs (se 1 (by rfl) ⟨64961, by rfl⟩) R129923
theorem R86681 : Reach 86681 := rs (se 2 (by rfl) ⟨32505, by rfl⟩) R65011
theorem R86795 : Reach 86795 := rs (se 1 (by rfl) ⟨65096, by rfl⟩) R130193
theorem R86807 : Reach 86807 := rs (se 1 (by rfl) ⟨65105, by rfl⟩) R130211
theorem R86873 : Reach 86873 := rs (se 2 (by rfl) ⟨32577, by rfl⟩) R65155
theorem R1495907 : Reach 1495907 := rs (se 1 (by rfl) ⟨1121930, by rfl⟩) R2243861
theorem R119731 : Reach 119731 := rs (se 1 (by rfl) ⟨89798, by rfl⟩) R179597
theorem R86987 : Reach 86987 := rs (se 1 (by rfl) ⟨65240, by rfl⟩) R130481
theorem R86999 : Reach 86999 := rs (se 1 (by rfl) ⟨65249, by rfl⟩) R130499
theorem R87065 : Reach 87065 := rs (se 2 (by rfl) ⟨32649, by rfl⟩) R65299
theorem R152669 : Reach 152669 := rs (se 3 (by rfl) ⟨28625, by rfl⟩) R57251
theorem R316547 : Reach 316547 := rs (se 1 (by rfl) ⟨237410, by rfl⟩) R474821
theorem R87179 : Reach 87179 := rs (se 1 (by rfl) ⟨65384, by rfl⟩) R130769
theorem R87191 : Reach 87191 := rs (se 1 (by rfl) ⟨65393, by rfl⟩) R130787
theorem R251059 : Reach 251059 := rs (se 1 (by rfl) ⟨188294, by rfl⟩) R376589
theorem R87257 : Reach 87257 := rs (se 2 (by rfl) ⟨32721, by rfl⟩) R65443
theorem R87371 : Reach 87371 := rs (se 1 (by rfl) ⟨65528, by rfl⟩) R131057
theorem R87383 : Reach 87383 := rs (se 1 (by rfl) ⟨65537, by rfl⟩) R131075
theorem R349541 : Reach 349541 := rs (se 4 (by rfl) ⟨32769, by rfl⟩) R65539
theorem R120217 : Reach 120217 := rs (se 2 (by rfl) ⟨45081, by rfl⟩) R90163
theorem R87449 : Reach 87449 := rs (se 2 (by rfl) ⟨32793, by rfl⟩) R65587
theorem R87563 : Reach 87563 := rs (se 1 (by rfl) ⟨65672, by rfl⟩) R131345
theorem R87575 : Reach 87575 := rs (se 1 (by rfl) ⟨65681, by rfl⟩) R131363
theorem R251437 : Reach 251437 := rs (se 3 (by rfl) ⟨47144, by rfl⟩) R94289
theorem R87641 : Reach 87641 := rs (se 2 (by rfl) ⟨32865, by rfl⟩) R65731
theorem R87755 : Reach 87755 := rs (se 1 (by rfl) ⟨65816, by rfl⟩) R131633
theorem R87767 : Reach 87767 := rs (se 1 (by rfl) ⟨65825, by rfl⟩) R131651
theorem R87833 : Reach 87833 := rs (se 2 (by rfl) ⟨32937, by rfl⟩) R65875
theorem R350027 : Reach 350027 := rs (se 1 (by rfl) ⟨262520, by rfl⟩) R525041
theorem R55127 : Reach 55127 := rs (se 1 (by rfl) ⟨41345, by rfl⟩) R82691
theorem R55147 : Reach 55147 := rs (se 1 (by rfl) ⟨41360, by rfl⟩) R82721
theorem R55159 : Reach 55159 := rs (se 1 (by rfl) ⟨41369, by rfl⟩) R82739
theorem R55179 : Reach 55179 := rs (se 1 (by rfl) ⟨41384, by rfl⟩) R82769
theorem R87947 : Reach 87947 := rs (se 1 (by rfl) ⟨65960, by rfl⟩) R131921
theorem R55191 : Reach 55191 := rs (se 1 (by rfl) ⟨41393, by rfl⟩) R82787
theorem R87959 : Reach 87959 := rs (se 1 (by rfl) ⟨65969, by rfl⟩) R131939
theorem R55211 : Reach 55211 := rs (se 1 (by rfl) ⟨41408, by rfl⟩) R82817
theorem R55223 : Reach 55223 := rs (se 1 (by rfl) ⟨41417, by rfl⟩) R82835
theorem R55243 : Reach 55243 := rs (se 1 (by rfl) ⟨41432, by rfl⟩) R82865
theorem R55255 : Reach 55255 := rs (se 1 (by rfl) ⟨41441, by rfl⟩) R82883
theorem R284633 : Reach 284633 := rs (se 2 (by rfl) ⟨106737, by rfl⟩) R213475
theorem R88025 : Reach 88025 := rs (se 2 (by rfl) ⟨33009, by rfl⟩) R66019
theorem R55275 : Reach 55275 := rs (se 1 (by rfl) ⟨41456, by rfl⟩) R82913
theorem R55287 : Reach 55287 := rs (se 1 (by rfl) ⟨41465, by rfl⟩) R82931
theorem R55307 : Reach 55307 := rs (se 1 (by rfl) ⟨41480, by rfl⟩) R82961
theorem R55319 : Reach 55319 := rs (se 1 (by rfl) ⟨41489, by rfl⟩) R82979
theorem R55339 : Reach 55339 := rs (se 1 (by rfl) ⟨41504, by rfl⟩) R83009
theorem R55351 : Reach 55351 := rs (se 1 (by rfl) ⟨41513, by rfl⟩) R83027
theorem R448577 : Reach 448577 := rs (se 2 (by rfl) ⟨168216, by rfl⟩) R336433
theorem R55371 : Reach 55371 := rs (se 1 (by rfl) ⟨41528, by rfl⟩) R83057
theorem R88139 : Reach 88139 := rs (se 1 (by rfl) ⟨66104, by rfl⟩) R132209
theorem R55383 : Reach 55383 := rs (se 1 (by rfl) ⟨41537, by rfl⟩) R83075
theorem R88151 : Reach 88151 := rs (se 1 (by rfl) ⟨66113, by rfl⟩) R132227
theorem R186461 : Reach 186461 := rs (se 3 (by rfl) ⟨34961, by rfl⟩) R69923
theorem R55403 : Reach 55403 := rs (se 1 (by rfl) ⟨41552, by rfl⟩) R83105
theorem R55415 : Reach 55415 := rs (se 1 (by rfl) ⟨41561, by rfl⟩) R83123
theorem R841859 : Reach 841859 := rs (se 1 (by rfl) ⟨631394, by rfl⟩) R1262789
theorem R55435 : Reach 55435 := rs (se 1 (by rfl) ⟨41576, by rfl⟩) R83153
theorem R55447 : Reach 55447 := rs (se 1 (by rfl) ⟨41585, by rfl⟩) R83171
theorem R153751 : Reach 153751 := rs (se 1 (by rfl) ⟨115313, by rfl⟩) R230627
theorem R88217 : Reach 88217 := rs (se 2 (by rfl) ⟨33081, by rfl⟩) R66163
theorem R55467 : Reach 55467 := rs (se 1 (by rfl) ⟨41600, by rfl⟩) R83201
theorem R55479 : Reach 55479 := rs (se 1 (by rfl) ⟨41609, by rfl⟩) R83219
theorem R55499 : Reach 55499 := rs (se 1 (by rfl) ⟨41624, by rfl⟩) R83249
theorem R55511 : Reach 55511 := rs (se 1 (by rfl) ⟨41633, by rfl⟩) R83267
theorem R55531 : Reach 55531 := rs (se 1 (by rfl) ⟨41648, by rfl⟩) R83297
theorem R55543 : Reach 55543 := rs (se 1 (by rfl) ⟨41657, by rfl⟩) R83315
theorem R55563 : Reach 55563 := rs (se 1 (by rfl) ⟨41672, by rfl⟩) R83345
theorem R88331 : Reach 88331 := rs (se 1 (by rfl) ⟨66248, by rfl⟩) R132497
theorem R55575 : Reach 55575 := rs (se 1 (by rfl) ⟨41681, by rfl⟩) R83363
theorem R88343 : Reach 88343 := rs (se 1 (by rfl) ⟨66257, by rfl⟩) R132515
theorem R55595 : Reach 55595 := rs (se 1 (by rfl) ⟨41696, by rfl⟩) R83393
theorem R55607 : Reach 55607 := rs (se 1 (by rfl) ⟨41705, by rfl⟩) R83411
theorem R55627 : Reach 55627 := rs (se 1 (by rfl) ⟨41720, by rfl⟩) R83441
theorem R55639 : Reach 55639 := rs (se 1 (by rfl) ⟨41729, by rfl⟩) R83459
theorem R88409 : Reach 88409 := rs (se 2 (by rfl) ⟨33153, by rfl⟩) R66307
theorem R55659 : Reach 55659 := rs (se 1 (by rfl) ⟨41744, by rfl⟩) R83489
theorem R55671 : Reach 55671 := rs (se 1 (by rfl) ⟨41753, by rfl⟩) R83507
theorem R55691 : Reach 55691 := rs (se 1 (by rfl) ⟨41768, by rfl⟩) R83537
theorem R88471 : Reach 88471 := rs (se 1 (by rfl) ⟨66353, by rfl⟩) R132707
theorem R55703 : Reach 55703 := rs (se 1 (by rfl) ⟨41777, by rfl⟩) R83555
theorem R55723 : Reach 55723 := rs (se 1 (by rfl) ⟨41792, by rfl⟩) R83585
theorem R55735 : Reach 55735 := rs (se 1 (by rfl) ⟨41801, by rfl⟩) R83603
theorem R88523 : Reach 88523 := rs (se 1 (by rfl) ⟨66392, by rfl⟩) R132785
theorem R55755 : Reach 55755 := rs (se 1 (by rfl) ⟨41816, by rfl⟩) R83633
theorem R55767 : Reach 55767 := rs (se 1 (by rfl) ⟨41825, by rfl⟩) R83651
theorem R88535 : Reach 88535 := rs (se 1 (by rfl) ⟨66401, by rfl⟩) R132803
theorem R55787 : Reach 55787 := rs (se 1 (by rfl) ⟨41840, by rfl⟩) R83681
theorem R55799 : Reach 55799 := rs (se 1 (by rfl) ⟨41849, by rfl⟩) R83699
theorem R55819 : Reach 55819 := rs (se 1 (by rfl) ⟨41864, by rfl⟩) R83729
theorem R55831 : Reach 55831 := rs (se 1 (by rfl) ⟨41873, by rfl⟩) R83747
theorem R88601 : Reach 88601 := rs (se 2 (by rfl) ⟨33225, by rfl⟩) R66451
theorem R55851 : Reach 55851 := rs (se 1 (by rfl) ⟨41888, by rfl⟩) R83777
theorem R55863 : Reach 55863 := rs (se 1 (by rfl) ⟨41897, by rfl⟩) R83795
theorem R88651 : Reach 88651 := rs (se 1 (by rfl) ⟨66488, by rfl⟩) R132977
theorem R55883 : Reach 55883 := rs (se 1 (by rfl) ⟨41912, by rfl⟩) R83825
theorem R55895 : Reach 55895 := rs (se 1 (by rfl) ⟨41921, by rfl⟩) R83843
theorem R55915 : Reach 55915 := rs (se 1 (by rfl) ⟨41936, by rfl⟩) R83873
theorem R55927 : Reach 55927 := rs (se 1 (by rfl) ⟨41945, by rfl⟩) R83891
theorem R449155 : Reach 449155 := rs (se 1 (by rfl) ⟨336866, by rfl⟩) R673733
theorem R219779 : Reach 219779 := rs (se 1 (by rfl) ⟨164834, by rfl⟩) R329669
theorem R55947 : Reach 55947 := rs (se 1 (by rfl) ⟨41960, by rfl⟩) R83921
theorem R219793 : Reach 219793 := rs (se 2 (by rfl) ⟨82422, by rfl⟩) R164845
theorem R55959 : Reach 55959 := rs (se 1 (by rfl) ⟨41969, by rfl⟩) R83939
theorem R55979 : Reach 55979 := rs (se 1 (by rfl) ⟨41984, by rfl⟩) R83969
theorem R55991 : Reach 55991 := rs (se 1 (by rfl) ⟨41993, by rfl⟩) R83987
theorem R56011 : Reach 56011 := rs (se 1 (by rfl) ⟨42008, by rfl⟩) R84017
theorem R56023 : Reach 56023 := rs (se 1 (by rfl) ⟨42017, by rfl⟩) R84035
theorem R56043 : Reach 56043 := rs (se 1 (by rfl) ⟨42032, by rfl⟩) R84065
theorem R56055 : Reach 56055 := rs (se 1 (by rfl) ⟨42041, by rfl⟩) R84083
theorem R121601 : Reach 121601 := rs (se 2 (by rfl) ⟨45600, by rfl⟩) R91201
theorem R645893 : Reach 645893 := rs (se 4 (by rfl) ⟨60552, by rfl⟩) R121105
theorem R56075 : Reach 56075 := rs (se 1 (by rfl) ⟨42056, by rfl⟩) R84113
theorem R56087 : Reach 56087 := rs (se 1 (by rfl) ⟨42065, by rfl⟩) R84131
theorem R56107 : Reach 56107 := rs (se 1 (by rfl) ⟨42080, by rfl⟩) R84161
theorem R56119 : Reach 56119 := rs (se 1 (by rfl) ⟨42089, by rfl⟩) R84179
theorem R56139 : Reach 56139 := rs (se 1 (by rfl) ⟨42104, by rfl⟩) R84209
theorem R56151 : Reach 56151 := rs (se 1 (by rfl) ⟨42113, by rfl⟩) R84227
theorem R56171 : Reach 56171 := rs (se 1 (by rfl) ⟨42128, by rfl⟩) R84257
theorem R56183 : Reach 56183 := rs (se 1 (by rfl) ⟨42137, by rfl⟩) R84275
theorem R56203 : Reach 56203 := rs (se 1 (by rfl) ⟨42152, by rfl⟩) R84305
theorem R56215 : Reach 56215 := rs (se 1 (by rfl) ⟨42161, by rfl⟩) R84323
theorem R56235 : Reach 56235 := rs (se 1 (by rfl) ⟨42176, by rfl⟩) R84353
theorem R56247 : Reach 56247 := rs (se 1 (by rfl) ⟨42185, by rfl⟩) R84371
theorem R220097 : Reach 220097 := rs (se 2 (by rfl) ⟨82536, by rfl⟩) R165073
theorem R56267 : Reach 56267 := rs (se 1 (by rfl) ⟨42200, by rfl⟩) R84401
theorem R56279 : Reach 56279 := rs (se 1 (by rfl) ⟨42209, by rfl⟩) R84419
theorem R56299 : Reach 56299 := rs (se 1 (by rfl) ⟨42224, by rfl⟩) R84449
theorem R56311 : Reach 56311 := rs (se 1 (by rfl) ⟨42233, by rfl⟩) R84467
theorem R56331 : Reach 56331 := rs (se 1 (by rfl) ⟨42248, by rfl⟩) R84497
theorem R56343 : Reach 56343 := rs (se 1 (by rfl) ⟨42257, by rfl⟩) R84515
theorem R56363 : Reach 56363 := rs (se 1 (by rfl) ⟨42272, by rfl⟩) R84545
theorem R56375 : Reach 56375 := rs (se 1 (by rfl) ⟨42281, by rfl⟩) R84563
theorem R56395 : Reach 56395 := rs (se 1 (by rfl) ⟨42296, by rfl⟩) R84593
theorem R56407 : Reach 56407 := rs (se 1 (by rfl) ⟨42305, by rfl⟩) R84611
theorem R56427 : Reach 56427 := rs (se 1 (by rfl) ⟨42320, by rfl⟩) R84641
theorem R56439 : Reach 56439 := rs (se 1 (by rfl) ⟨42329, by rfl⟩) R84659
theorem R56459 : Reach 56459 := rs (se 1 (by rfl) ⟨42344, by rfl⟩) R84689
theorem R56471 : Reach 56471 := rs (se 1 (by rfl) ⟨42353, by rfl⟩) R84707
theorem R56491 : Reach 56491 := rs (se 1 (by rfl) ⟨42368, by rfl⟩) R84737
theorem R220333 : Reach 220333 := rs (se 3 (by rfl) ⟨41312, by rfl⟩) R82625
theorem R56503 : Reach 56503 := rs (se 1 (by rfl) ⟨42377, by rfl⟩) R84755
theorem R187595 : Reach 187595 := rs (se 1 (by rfl) ⟨140696, by rfl⟩) R281393
theorem R56523 : Reach 56523 := rs (se 1 (by rfl) ⟨42392, by rfl⟩) R84785
theorem R56535 : Reach 56535 := rs (se 1 (by rfl) ⟨42401, by rfl⟩) R84803
theorem R56555 : Reach 56555 := rs (se 1 (by rfl) ⟨42416, by rfl⟩) R84833
theorem R56567 : Reach 56567 := rs (se 1 (by rfl) ⟨42425, by rfl⟩) R84851
theorem R56587 : Reach 56587 := rs (se 1 (by rfl) ⟨42440, by rfl⟩) R84881
theorem R122123 : Reach 122123 := rs (se 1 (by rfl) ⟨91592, by rfl⟩) R183185
theorem R56599 : Reach 56599 := rs (se 1 (by rfl) ⟨42449, by rfl⟩) R84899
theorem R56619 : Reach 56619 := rs (se 1 (by rfl) ⟨42464, by rfl⟩) R84929
theorem R56631 : Reach 56631 := rs (se 1 (by rfl) ⟨42473, by rfl⟩) R84947
theorem R56651 : Reach 56651 := rs (se 1 (by rfl) ⟨42488, by rfl⟩) R84977
theorem R56663 : Reach 56663 := rs (se 1 (by rfl) ⟨42497, by rfl⟩) R84995
theorem R56683 : Reach 56683 := rs (se 1 (by rfl) ⟨42512, by rfl⟩) R85025
theorem R56695 : Reach 56695 := rs (se 1 (by rfl) ⟨42521, by rfl⟩) R85043
theorem R56715 : Reach 56715 := rs (se 1 (by rfl) ⟨42536, by rfl⟩) R85073
theorem R56727 : Reach 56727 := rs (se 1 (by rfl) ⟨42545, by rfl⟩) R85091
theorem R56747 : Reach 56747 := rs (se 1 (by rfl) ⟨42560, by rfl⟩) R85121
theorem R56759 : Reach 56759 := rs (se 1 (by rfl) ⟨42569, by rfl⟩) R85139
theorem R56779 : Reach 56779 := rs (se 1 (by rfl) ⟨42584, by rfl⟩) R85169
theorem R56791 : Reach 56791 := rs (se 1 (by rfl) ⟨42593, by rfl⟩) R85187
theorem R187865 : Reach 187865 := rs (se 2 (by rfl) ⟨70449, by rfl⟩) R140899
theorem R89561 : Reach 89561 := rs (se 2 (by rfl) ⟨33585, by rfl⟩) R67171
theorem R318937 : Reach 318937 := rs (se 2 (by rfl) ⟨119601, by rfl⟩) R239203
theorem R56811 : Reach 56811 := rs (se 1 (by rfl) ⟨42608, by rfl⟩) R85217
theorem R56823 : Reach 56823 := rs (se 1 (by rfl) ⟨42617, by rfl⟩) R85235
theorem R56843 : Reach 56843 := rs (se 1 (by rfl) ⟨42632, by rfl⟩) R85265
theorem R56855 : Reach 56855 := rs (se 1 (by rfl) ⟨42641, by rfl⟩) R85283
theorem R56875 : Reach 56875 := rs (se 1 (by rfl) ⟨42656, by rfl⟩) R85313
theorem R286253 : Reach 286253 := rs (se 3 (by rfl) ⟨53672, by rfl⟩) R107345
theorem R56887 : Reach 56887 := rs (se 1 (by rfl) ⟨42665, by rfl⟩) R85331
theorem R56907 : Reach 56907 := rs (se 1 (by rfl) ⟨42680, by rfl⟩) R85361
theorem R56919 : Reach 56919 := rs (se 1 (by rfl) ⟨42689, by rfl⟩) R85379
theorem R220765 : Reach 220765 := rs (se 3 (by rfl) ⟨41393, by rfl⟩) R82787
theorem R56939 : Reach 56939 := rs (se 1 (by rfl) ⟨42704, by rfl⟩) R85409
theorem R56951 : Reach 56951 := rs (se 1 (by rfl) ⟨42713, by rfl⟩) R85427
theorem R56971 : Reach 56971 := rs (se 1 (by rfl) ⟨42728, by rfl⟩) R85457
theorem R56983 : Reach 56983 := rs (se 1 (by rfl) ⟨42737, by rfl⟩) R85475
theorem R57003 : Reach 57003 := rs (se 1 (by rfl) ⟨42752, by rfl⟩) R85505
theorem R57015 : Reach 57015 := rs (se 1 (by rfl) ⟨42761, by rfl⟩) R85523
theorem R57035 : Reach 57035 := rs (se 1 (by rfl) ⟨42776, by rfl⟩) R85553
theorem R57047 : Reach 57047 := rs (se 1 (by rfl) ⟨42785, by rfl⟩) R85571
theorem R57067 : Reach 57067 := rs (se 1 (by rfl) ⟨42800, by rfl⟩) R85601
theorem R57079 : Reach 57079 := rs (se 1 (by rfl) ⟨42809, by rfl⟩) R85619
theorem R57099 : Reach 57099 := rs (se 1 (by rfl) ⟨42824, by rfl⟩) R85649
theorem R57111 : Reach 57111 := rs (se 1 (by rfl) ⟨42833, by rfl⟩) R85667
theorem R57131 : Reach 57131 := rs (se 1 (by rfl) ⟨42848, by rfl⟩) R85697
theorem R57143 : Reach 57143 := rs (se 1 (by rfl) ⟨42857, by rfl⟩) R85715
theorem R57163 : Reach 57163 := rs (se 1 (by rfl) ⟨42872, by rfl⟩) R85745
theorem R57175 : Reach 57175 := rs (se 1 (by rfl) ⟨42881, by rfl⟩) R85763
theorem R57195 : Reach 57195 := rs (se 1 (by rfl) ⟨42896, by rfl⟩) R85793
theorem R57207 : Reach 57207 := rs (se 1 (by rfl) ⟨42905, by rfl⟩) R85811
theorem R57227 : Reach 57227 := rs (se 1 (by rfl) ⟨42920, by rfl⟩) R85841
theorem R57239 : Reach 57239 := rs (se 1 (by rfl) ⟨42929, by rfl⟩) R85859
theorem R57259 : Reach 57259 := rs (se 1 (by rfl) ⟨42944, by rfl⟩) R85889
theorem R450481 : Reach 450481 := rs (se 2 (by rfl) ⟨168930, by rfl⟩) R337861
theorem R57271 : Reach 57271 := rs (se 1 (by rfl) ⟨42953, by rfl⟩) R85907
theorem R57291 : Reach 57291 := rs (se 1 (by rfl) ⟨42968, by rfl⟩) R85937
theorem R57303 : Reach 57303 := rs (se 1 (by rfl) ⟨42977, by rfl⟩) R85955
theorem R57323 : Reach 57323 := rs (se 1 (by rfl) ⟨42992, by rfl⟩) R85985
theorem R57335 : Reach 57335 := rs (se 1 (by rfl) ⟨43001, by rfl⟩) R86003
theorem R253955 : Reach 253955 := rs (se 1 (by rfl) ⟨190466, by rfl⟩) R380933
theorem R57355 : Reach 57355 := rs (se 1 (by rfl) ⟨43016, by rfl⟩) R86033
theorem R57367 : Reach 57367 := rs (se 1 (by rfl) ⟨43025, by rfl⟩) R86051
theorem R57387 : Reach 57387 := rs (se 1 (by rfl) ⟨43040, by rfl⟩) R86081
theorem R57399 : Reach 57399 := rs (se 1 (by rfl) ⟨43049, by rfl⟩) R86099
theorem R57419 : Reach 57419 := rs (se 1 (by rfl) ⟨43064, by rfl⟩) R86129
theorem R57431 : Reach 57431 := rs (se 1 (by rfl) ⟨43073, by rfl⟩) R86147
theorem R57451 : Reach 57451 := rs (se 1 (by rfl) ⟨43088, by rfl⟩) R86177
theorem R57463 : Reach 57463 := rs (se 1 (by rfl) ⟨43097, by rfl⟩) R86195
theorem R57483 : Reach 57483 := rs (se 1 (by rfl) ⟨43112, by rfl⟩) R86225
theorem R188567 : Reach 188567 := rs (se 1 (by rfl) ⟨141425, by rfl⟩) R282851
theorem R57495 : Reach 57495 := rs (se 1 (by rfl) ⟨43121, by rfl⟩) R86243
theorem R57515 : Reach 57515 := rs (se 1 (by rfl) ⟨43136, by rfl⟩) R86273
theorem R57527 : Reach 57527 := rs (se 1 (by rfl) ⟨43145, by rfl⟩) R86291
theorem R57547 : Reach 57547 := rs (se 1 (by rfl) ⟨43160, by rfl⟩) R86321
theorem R57559 : Reach 57559 := rs (se 1 (by rfl) ⟨43169, by rfl⟩) R86339
theorem R57579 : Reach 57579 := rs (se 1 (by rfl) ⟨43184, by rfl⟩) R86369
theorem R57591 : Reach 57591 := rs (se 1 (by rfl) ⟨43193, by rfl⟩) R86387
theorem R57611 : Reach 57611 := rs (se 1 (by rfl) ⟨43208, by rfl⟩) R86417
theorem R57623 : Reach 57623 := rs (se 1 (by rfl) ⟨43217, by rfl⟩) R86435
theorem R57643 : Reach 57643 := rs (se 1 (by rfl) ⟨43232, by rfl⟩) R86465
theorem R57655 : Reach 57655 := rs (se 1 (by rfl) ⟨43241, by rfl⟩) R86483
theorem R57675 : Reach 57675 := rs (se 1 (by rfl) ⟨43256, by rfl⟩) R86513
theorem R57687 : Reach 57687 := rs (se 1 (by rfl) ⟨43265, by rfl⟩) R86531
theorem R680293 : Reach 680293 := rs (se 4 (by rfl) ⟨63777, by rfl⟩) R127555
theorem R57707 : Reach 57707 := rs (se 1 (by rfl) ⟨43280, by rfl⟩) R86561
theorem R57719 : Reach 57719 := rs (se 1 (by rfl) ⟨43289, by rfl⟩) R86579
theorem R57739 : Reach 57739 := rs (se 1 (by rfl) ⟨43304, by rfl⟩) R86609
theorem R319895 : Reach 319895 := rs (se 1 (by rfl) ⟨239921, by rfl⟩) R479843
theorem R57751 : Reach 57751 := rs (se 1 (by rfl) ⟨43313, by rfl⟩) R86627
theorem R57771 : Reach 57771 := rs (se 1 (by rfl) ⟨43328, by rfl⟩) R86657
theorem R57783 : Reach 57783 := rs (se 1 (by rfl) ⟨43337, by rfl⟩) R86675
theorem R57803 : Reach 57803 := rs (se 1 (by rfl) ⟨43352, by rfl⟩) R86705
theorem R57815 : Reach 57815 := rs (se 1 (by rfl) ⟨43361, by rfl⟩) R86723
theorem R123353 : Reach 123353 := rs (se 2 (by rfl) ⟨46257, by rfl⟩) R92515
theorem R57835 : Reach 57835 := rs (se 1 (by rfl) ⟨43376, by rfl⟩) R86753
theorem R57847 : Reach 57847 := rs (se 1 (by rfl) ⟨43385, by rfl⟩) R86771
theorem R57867 : Reach 57867 := rs (se 1 (by rfl) ⟨43400, by rfl⟩) R86801
theorem R57879 : Reach 57879 := rs (se 1 (by rfl) ⟨43409, by rfl⟩) R86819
theorem R57899 : Reach 57899 := rs (se 1 (by rfl) ⟨43424, by rfl⟩) R86849
theorem R57911 : Reach 57911 := rs (se 1 (by rfl) ⟨43433, by rfl⟩) R86867
theorem R57931 : Reach 57931 := rs (se 1 (by rfl) ⟨43448, by rfl⟩) R86897
theorem R57943 : Reach 57943 := rs (se 1 (by rfl) ⟨43457, by rfl⟩) R86915
theorem R57963 : Reach 57963 := rs (se 1 (by rfl) ⟨43472, by rfl⟩) R86945
theorem R57975 : Reach 57975 := rs (se 1 (by rfl) ⟨43481, by rfl⟩) R86963
theorem R57995 : Reach 57995 := rs (se 1 (by rfl) ⟨43496, by rfl⟩) R86993
theorem R58007 : Reach 58007 := rs (se 1 (by rfl) ⟨43505, by rfl⟩) R87011
theorem R58027 : Reach 58027 := rs (se 1 (by rfl) ⟨43520, by rfl⟩) R87041
theorem R189107 : Reach 189107 := rs (se 1 (by rfl) ⟨141830, by rfl⟩) R283661
theorem R58039 : Reach 58039 := rs (se 1 (by rfl) ⟨43529, by rfl⟩) R87059
theorem R58059 : Reach 58059 := rs (se 1 (by rfl) ⟨43544, by rfl⟩) R87089
theorem R58071 : Reach 58071 := rs (se 1 (by rfl) ⟨43553, by rfl⟩) R87107
theorem R58091 : Reach 58091 := rs (se 1 (by rfl) ⟨43568, by rfl⟩) R87137
theorem R58103 : Reach 58103 := rs (se 1 (by rfl) ⟨43577, by rfl⟩) R87155
theorem R58123 : Reach 58123 := rs (se 1 (by rfl) ⟨43592, by rfl⟩) R87185
theorem R58135 : Reach 58135 := rs (se 1 (by rfl) ⟨43601, by rfl⟩) R87203
theorem R58155 : Reach 58155 := rs (se 1 (by rfl) ⟨43616, by rfl⟩) R87233
theorem R58167 : Reach 58167 := rs (se 1 (by rfl) ⟨43625, by rfl⟩) R87251
theorem R58187 : Reach 58187 := rs (se 1 (by rfl) ⟨43640, by rfl⟩) R87281
theorem R58199 : Reach 58199 := rs (se 1 (by rfl) ⟨43649, by rfl⟩) R87299
theorem R222041 : Reach 222041 := rs (se 2 (by rfl) ⟨83265, by rfl⟩) R166531
theorem R58219 : Reach 58219 := rs (se 1 (by rfl) ⟨43664, by rfl⟩) R87329
theorem R123763 : Reach 123763 := rs (se 1 (by rfl) ⟨92822, by rfl⟩) R185645
theorem R58231 : Reach 58231 := rs (se 1 (by rfl) ⟨43673, by rfl⟩) R87347
theorem R58251 : Reach 58251 := rs (se 1 (by rfl) ⟨43688, by rfl⟩) R87377
theorem R58263 : Reach 58263 := rs (se 1 (by rfl) ⟨43697, by rfl⟩) R87395
theorem R58283 : Reach 58283 := rs (se 1 (by rfl) ⟨43712, by rfl⟩) R87425
theorem R58295 : Reach 58295 := rs (se 1 (by rfl) ⟨43721, by rfl⟩) R87443
theorem R189377 : Reach 189377 := rs (se 2 (by rfl) ⟨71016, by rfl⟩) R142033
theorem R58315 : Reach 58315 := rs (se 1 (by rfl) ⟨43736, by rfl⟩) R87473
theorem R418765 : Reach 418765 := rs (se 3 (by rfl) ⟨78518, by rfl⟩) R157037
theorem R58327 : Reach 58327 := rs (se 1 (by rfl) ⟨43745, by rfl⟩) R87491
theorem R58347 : Reach 58347 := rs (se 1 (by rfl) ⟨43760, by rfl⟩) R87521
theorem R58359 : Reach 58359 := rs (se 1 (by rfl) ⟨43769, by rfl⟩) R87539
theorem R58379 : Reach 58379 := rs (se 1 (by rfl) ⟨43784, by rfl⟩) R87569
theorem R58391 : Reach 58391 := rs (se 1 (by rfl) ⟨43793, by rfl⟩) R87587
theorem R58411 : Reach 58411 := rs (se 1 (by rfl) ⟨43808, by rfl⟩) R87617
theorem R58423 : Reach 58423 := rs (se 1 (by rfl) ⟨43817, by rfl⟩) R87635
theorem R58443 : Reach 58443 := rs (se 1 (by rfl) ⟨43832, by rfl⟩) R87665
theorem R58455 : Reach 58455 := rs (se 1 (by rfl) ⟨43841, by rfl⟩) R87683
theorem R58475 : Reach 58475 := rs (se 1 (by rfl) ⟨43856, by rfl⟩) R87713
theorem R58487 : Reach 58487 := rs (se 1 (by rfl) ⟨43865, by rfl⟩) R87731
theorem R58507 : Reach 58507 := rs (se 1 (by rfl) ⟨43880, by rfl⟩) R87761
theorem R124055 : Reach 124055 := rs (se 1 (by rfl) ⟨93041, by rfl⟩) R186083
theorem R58519 : Reach 58519 := rs (se 1 (by rfl) ⟨43889, by rfl⟩) R87779
theorem R58539 : Reach 58539 := rs (se 1 (by rfl) ⟨43904, by rfl⟩) R87809
theorem R58551 : Reach 58551 := rs (se 1 (by rfl) ⟨43913, by rfl⟩) R87827
theorem R58571 : Reach 58571 := rs (se 1 (by rfl) ⟨43928, by rfl⟩) R87857
theorem R58583 : Reach 58583 := rs (se 1 (by rfl) ⟨43937, by rfl⟩) R87875
theorem R58603 : Reach 58603 := rs (se 1 (by rfl) ⟨43952, by rfl⟩) R87905
theorem R58615 : Reach 58615 := rs (se 1 (by rfl) ⟨43961, by rfl⟩) R87923
theorem R58635 : Reach 58635 := rs (se 1 (by rfl) ⟨43976, by rfl⟩) R87953
theorem R58647 : Reach 58647 := rs (se 1 (by rfl) ⟨43985, by rfl⟩) R87971
theorem R58667 : Reach 58667 := rs (se 1 (by rfl) ⟨44000, by rfl⟩) R88001
theorem R58679 : Reach 58679 := rs (se 1 (by rfl) ⟨44009, by rfl⟩) R88019
theorem R124235 : Reach 124235 := rs (se 1 (by rfl) ⟨93176, by rfl⟩) R186353
theorem R58699 : Reach 58699 := rs (se 1 (by rfl) ⟨44024, by rfl⟩) R88049
theorem R58711 : Reach 58711 := rs (se 1 (by rfl) ⟨44033, by rfl⟩) R88067
theorem R124249 : Reach 124249 := rs (se 2 (by rfl) ⟨46593, by rfl⟩) R93187
theorem R58731 : Reach 58731 := rs (se 1 (by rfl) ⟨44048, by rfl⟩) R88097
theorem R58743 : Reach 58743 := rs (se 1 (by rfl) ⟨44057, by rfl⟩) R88115
theorem R124289 : Reach 124289 := rs (se 2 (by rfl) ⟨46608, by rfl⟩) R93217
theorem R58763 : Reach 58763 := rs (se 1 (by rfl) ⟨44072, by rfl⟩) R88145
theorem R58775 : Reach 58775 := rs (se 1 (by rfl) ⟨44081, by rfl⟩) R88163
theorem R58795 : Reach 58795 := rs (se 1 (by rfl) ⟨44096, by rfl⟩) R88193
theorem R58807 : Reach 58807 := rs (se 1 (by rfl) ⟨44105, by rfl⟩) R88211
theorem R58827 : Reach 58827 := rs (se 1 (by rfl) ⟨44120, by rfl⟩) R88241
theorem R58839 : Reach 58839 := rs (se 1 (by rfl) ⟨44129, by rfl⟩) R88259
theorem R189917 : Reach 189917 := rs (se 3 (by rfl) ⟨35609, by rfl⟩) R71219
theorem R58859 : Reach 58859 := rs (se 1 (by rfl) ⟨44144, by rfl⟩) R88289
theorem R58871 : Reach 58871 := rs (se 1 (by rfl) ⟨44153, by rfl⟩) R88307
theorem R58891 : Reach 58891 := rs (se 1 (by rfl) ⟨44168, by rfl⟩) R88337
theorem R58903 : Reach 58903 := rs (se 1 (by rfl) ⟨44177, by rfl⟩) R88355
theorem R58923 : Reach 58923 := rs (se 1 (by rfl) ⟨44192, by rfl⟩) R88385
theorem R58935 : Reach 58935 := rs (se 1 (by rfl) ⟨44201, by rfl⟩) R88403
theorem R58955 : Reach 58955 := rs (se 1 (by rfl) ⟨44216, by rfl⟩) R88433
theorem R58967 : Reach 58967 := rs (se 1 (by rfl) ⟨44225, by rfl⟩) R88451
theorem R124505 : Reach 124505 := rs (se 2 (by rfl) ⟨46689, by rfl⟩) R93379
theorem R157277 : Reach 157277 := rs (se 3 (by rfl) ⟨29489, by rfl⟩) R58979
theorem R58987 : Reach 58987 := rs (se 1 (by rfl) ⟨44240, by rfl⟩) R88481
theorem R58999 : Reach 58999 := rs (se 1 (by rfl) ⟨44249, by rfl⟩) R88499
theorem R59019 : Reach 59019 := rs (se 1 (by rfl) ⟨44264, by rfl⟩) R88529
theorem R59031 : Reach 59031 := rs (se 1 (by rfl) ⟨44273, by rfl⟩) R88547
theorem R59051 : Reach 59051 := rs (se 1 (by rfl) ⟨44288, by rfl⟩) R88577
theorem R124595 : Reach 124595 := rs (se 1 (by rfl) ⟨93446, by rfl⟩) R186893
theorem R59063 : Reach 59063 := rs (se 1 (by rfl) ⟨44297, by rfl⟩) R88595
theorem R59083 : Reach 59083 := rs (se 1 (by rfl) ⟨44312, by rfl⟩) R88625
theorem R124631 : Reach 124631 := rs (se 1 (by rfl) ⟨93473, by rfl⟩) R186947
theorem R59095 : Reach 59095 := rs (se 1 (by rfl) ⟨44321, by rfl⟩) R88643
theorem R59115 : Reach 59115 := rs (se 1 (by rfl) ⟨44336, by rfl⟩) R88673
theorem R124787 : Reach 124787 := rs (se 1 (by rfl) ⟨93590, by rfl⟩) R187181
theorem R124811 : Reach 124811 := rs (se 1 (by rfl) ⟨93608, by rfl⟩) R187217
theorem R124865 : Reach 124865 := rs (se 2 (by rfl) ⟨46824, by rfl⟩) R93649
theorem R124993 : Reach 124993 := rs (se 2 (by rfl) ⟨46872, by rfl⟩) R93745
theorem R125081 : Reach 125081 := rs (se 2 (by rfl) ⟨46905, by rfl⟩) R93811
theorem R223411 : Reach 223411 := rs (se 1 (by rfl) ⟨167558, by rfl⟩) R335117
theorem R125171 : Reach 125171 := rs (se 1 (by rfl) ⟨93878, by rfl⟩) R187757
theorem R125207 : Reach 125207 := rs (se 1 (by rfl) ⟨93905, by rfl⟩) R187811
theorem R223667 : Reach 223667 := rs (se 1 (by rfl) ⟨167750, by rfl⟩) R335501
theorem R223681 : Reach 223681 := rs (se 2 (by rfl) ⟨83880, by rfl⟩) R167761
theorem R125387 : Reach 125387 := rs (se 1 (by rfl) ⟨94040, by rfl⟩) R188081
theorem R125441 : Reach 125441 := rs (se 2 (by rfl) ⟨47040, by rfl⟩) R94081
theorem R191051 : Reach 191051 := rs (se 1 (by rfl) ⟨143288, by rfl⟩) R286577
theorem R125657 : Reach 125657 := rs (se 2 (by rfl) ⟨47121, by rfl⟩) R94243
theorem R60139 : Reach 60139 := rs (se 1 (by rfl) ⟨45104, by rfl⟩) R90209
theorem R125747 : Reach 125747 := rs (se 1 (by rfl) ⟨94310, by rfl⟩) R188621
theorem R322379 : Reach 322379 := rs (se 1 (by rfl) ⟨241784, by rfl⟩) R483569
theorem R125783 : Reach 125783 := rs (se 1 (by rfl) ⟨94337, by rfl⟩) R188675
theorem R191321 : Reach 191321 := rs (se 2 (by rfl) ⟨71745, by rfl⟩) R143491
theorem R93079 : Reach 93079 := rs (se 1 (by rfl) ⟨69809, by rfl⟩) R139619
theorem R60311 : Reach 60311 := rs (se 1 (by rfl) ⟨45233, by rfl⟩) R90467
theorem R322483 : Reach 322483 := rs (se 1 (by rfl) ⟨241862, by rfl⟩) R483725
theorem R93143 : Reach 93143 := rs (se 1 (by rfl) ⟨69857, by rfl⟩) R139715
theorem R125963 : Reach 125963 := rs (se 1 (by rfl) ⟨94472, by rfl⟩) R188945
theorem R125975 : Reach 125975 := rs (se 1 (by rfl) ⟨94481, by rfl⟩) R188963
theorem R355373 : Reach 355373 := rs (se 3 (by rfl) ⟨66632, by rfl⟩) R133265
theorem R126017 : Reach 126017 := rs (se 2 (by rfl) ⟨47256, by rfl⟩) R94513
theorem R93271 : Reach 93271 := rs (se 1 (by rfl) ⟨69953, by rfl⟩) R139907
theorem R945413 : Reach 945413 := rs (se 4 (by rfl) ⟨88632, by rfl⟩) R177265
theorem R126233 : Reach 126233 := rs (se 2 (by rfl) ⟨47337, by rfl⟩) R94675
theorem R290141 : Reach 290141 := rs (se 3 (by rfl) ⟨54401, by rfl⟩) R108803
theorem R126323 : Reach 126323 := rs (se 1 (by rfl) ⟨94742, by rfl⟩) R189485
theorem R126359 : Reach 126359 := rs (se 1 (by rfl) ⟨94769, by rfl⟩) R189539
theorem R192023 : Reach 192023 := rs (se 1 (by rfl) ⟨144017, by rfl⟩) R288035
theorem R585251 : Reach 585251 := rs (se 1 (by rfl) ⟨438938, by rfl⟩) R877877
theorem R126539 : Reach 126539 := rs (se 1 (by rfl) ⟨94904, by rfl⟩) R189809
theorem R126593 : Reach 126593 := rs (se 2 (by rfl) ⟨47472, by rfl⟩) R94945
theorem R93899 : Reach 93899 := rs (se 1 (by rfl) ⟨70424, by rfl⟩) R140849
theorem R94027 : Reach 94027 := rs (se 1 (by rfl) ⟨70520, by rfl⟩) R141041
theorem R126809 : Reach 126809 := rs (se 2 (by rfl) ⟨47553, by rfl⟩) R95107
theorem R126899 : Reach 126899 := rs (se 1 (by rfl) ⟨95174, by rfl⟩) R190349
theorem R225227 : Reach 225227 := rs (se 1 (by rfl) ⟨168920, by rfl⟩) R337841
theorem R126935 : Reach 126935 := rs (se 1 (by rfl) ⟨95201, by rfl⟩) R190403
theorem R126937 : Reach 126937 := rs (se 2 (by rfl) ⟨47601, by rfl⟩) R95203
theorem R94169 : Reach 94169 := rs (se 2 (by rfl) ⟨35313, by rfl⟩) R70627
theorem R192563 : Reach 192563 := rs (se 1 (by rfl) ⟨144422, by rfl⟩) R288845
theorem R94297 : Reach 94297 := rs (se 2 (by rfl) ⟨35361, by rfl⟩) R70723
theorem R159833 : Reach 159833 := rs (se 2 (by rfl) ⟨59937, by rfl⟩) R119875
theorem R127115 : Reach 127115 := rs (se 1 (by rfl) ⟨95336, by rfl⟩) R190673
theorem R127169 : Reach 127169 := rs (se 2 (by rfl) ⟨47688, by rfl⟩) R95377
theorem R192833 : Reach 192833 := rs (se 2 (by rfl) ⟨72312, by rfl⟩) R144625
theorem R127385 : Reach 127385 := rs (se 2 (by rfl) ⟨47769, by rfl⟩) R95539
theorem R127475 : Reach 127475 := rs (se 1 (by rfl) ⟨95606, by rfl⟩) R191213
theorem R127511 : Reach 127511 := rs (se 1 (by rfl) ⟨95633, by rfl⟩) R191267
theorem R62059 : Reach 62059 := rs (se 1 (by rfl) ⟨46544, by rfl⟩) R93089
theorem R94859 : Reach 94859 := rs (se 1 (by rfl) ⟨71144, by rfl⟩) R142289
theorem R94871 : Reach 94871 := rs (se 1 (by rfl) ⟨71153, by rfl⟩) R142307
theorem R127691 : Reach 127691 := rs (se 1 (by rfl) ⟨95768, by rfl⟩) R191537
theorem R62155 : Reach 62155 := rs (se 1 (by rfl) ⟨46616, by rfl⟩) R93233
theorem R62167 : Reach 62167 := rs (se 1 (by rfl) ⟨46625, by rfl⟩) R93251
theorem R127745 : Reach 127745 := rs (se 2 (by rfl) ⟨47904, by rfl⟩) R95809
theorem R94999 : Reach 94999 := rs (se 1 (by rfl) ⟨71249, by rfl⟩) R142499
theorem R193373 : Reach 193373 := rs (se 3 (by rfl) ⟨36257, by rfl⟩) R72515
theorem R62347 : Reach 62347 := rs (se 1 (by rfl) ⟨46760, by rfl⟩) R93521
theorem R127961 : Reach 127961 := rs (se 2 (by rfl) ⟨47985, by rfl⟩) R95971
theorem R62455 : Reach 62455 := rs (se 1 (by rfl) ⟨46841, by rfl⟩) R93683
theorem R914449 : Reach 914449 := rs (se 2 (by rfl) ⟨342918, by rfl⟩) R685837
theorem R128051 : Reach 128051 := rs (se 1 (by rfl) ⟨96038, by rfl⟩) R192077
theorem R128087 : Reach 128087 := rs (se 1 (by rfl) ⟨96065, by rfl⟩) R192131
theorem R62635 : Reach 62635 := rs (se 1 (by rfl) ⟨46976, by rfl⟩) R93953
theorem R95435 : Reach 95435 := rs (se 1 (by rfl) ⟨71576, by rfl⟩) R143153
theorem R128267 : Reach 128267 := rs (se 1 (by rfl) ⟨96200, by rfl⟩) R192401
theorem R62743 : Reach 62743 := rs (se 1 (by rfl) ⟨47057, by rfl⟩) R94115
theorem R128321 : Reach 128321 := rs (se 2 (by rfl) ⟨48120, by rfl⟩) R96241
theorem R161099 : Reach 161099 := rs (se 1 (by rfl) ⟨120824, by rfl⟩) R241649
theorem R95627 : Reach 95627 := rs (se 1 (by rfl) ⟨71720, by rfl⟩) R143441
theorem R292247 : Reach 292247 := rs (se 1 (by rfl) ⟨219185, by rfl⟩) R438371
theorem R325043 : Reach 325043 := rs (se 1 (by rfl) ⟨243782, by rfl⟩) R487565
theorem R62923 : Reach 62923 := rs (se 1 (by rfl) ⟨47192, by rfl⟩) R94385
theorem R95755 : Reach 95755 := rs (se 1 (by rfl) ⟨71816, by rfl⟩) R143633
theorem R128537 : Reach 128537 := rs (se 2 (by rfl) ⟨48201, by rfl⟩) R96403
theorem R63031 : Reach 63031 := rs (se 1 (by rfl) ⟨47273, by rfl⟩) R94547
theorem R718429 : Reach 718429 := rs (se 3 (by rfl) ⟨134705, by rfl⟩) R269411
theorem R128627 : Reach 128627 := rs (se 1 (by rfl) ⟨96470, by rfl⟩) R192941
theorem R128663 : Reach 128663 := rs (se 1 (by rfl) ⟨96497, by rfl⟩) R192995
theorem R95897 : Reach 95897 := rs (se 2 (by rfl) ⟨35961, by rfl⟩) R71923
theorem R63211 : Reach 63211 := rs (se 1 (by rfl) ⟨47408, by rfl⟩) R94817
theorem R96025 : Reach 96025 := rs (se 2 (by rfl) ⟨36009, by rfl⟩) R72019
theorem R128843 : Reach 128843 := rs (se 1 (by rfl) ⟨96632, by rfl⟩) R193265
theorem R63319 : Reach 63319 := rs (se 1 (by rfl) ⟨47489, by rfl⟩) R94979
theorem R128897 : Reach 128897 := rs (se 2 (by rfl) ⟨48336, by rfl⟩) R96673
theorem R194507 : Reach 194507 := rs (se 1 (by rfl) ⟨145880, by rfl⟩) R291761
theorem R194525 : Reach 194525 := rs (se 3 (by rfl) ⟨36473, by rfl⟩) R72947
theorem R63499 : Reach 63499 := rs (se 1 (by rfl) ⟨47624, by rfl⟩) R95249
theorem R129113 : Reach 129113 := rs (se 2 (by rfl) ⟨48417, by rfl⟩) R96835
theorem R63607 : Reach 63607 := rs (se 1 (by rfl) ⟨47705, by rfl⟩) R95411
theorem R129203 : Reach 129203 := rs (se 1 (by rfl) ⟨96902, by rfl⟩) R193805
theorem R129239 : Reach 129239 := rs (se 1 (by rfl) ⟨96929, by rfl⟩) R193859
theorem R194777 : Reach 194777 := rs (se 2 (by rfl) ⟨73041, by rfl⟩) R146083
theorem R63787 : Reach 63787 := rs (se 1 (by rfl) ⟨47840, by rfl⟩) R95681
theorem R227659 : Reach 227659 := rs (se 1 (by rfl) ⟨170744, by rfl⟩) R341489
theorem R96599 : Reach 96599 := rs (se 1 (by rfl) ⟨72449, by rfl⟩) R144899
theorem R129419 : Reach 129419 := rs (se 1 (by rfl) ⟨97064, by rfl⟩) R194129
theorem R63895 : Reach 63895 := rs (se 1 (by rfl) ⟨47921, by rfl⟩) R95843
theorem R129473 : Reach 129473 := rs (se 2 (by rfl) ⟨48552, by rfl⟩) R97105
theorem R96727 : Reach 96727 := rs (se 1 (by rfl) ⟨72545, by rfl⟩) R145091
theorem R621017 : Reach 621017 := rs (se 2 (by rfl) ⟨232881, by rfl⟩) R465763
theorem R64075 : Reach 64075 := rs (se 1 (by rfl) ⟨48056, by rfl⟩) R96113
theorem R359063 : Reach 359063 := rs (se 1 (by rfl) ⟨269297, by rfl⟩) R538595
theorem R129689 : Reach 129689 := rs (se 2 (by rfl) ⟨48633, by rfl⟩) R97267
theorem R64183 : Reach 64183 := rs (se 1 (by rfl) ⟨48137, by rfl⟩) R96275
theorem R359129 : Reach 359129 := rs (se 2 (by rfl) ⟨134673, by rfl⟩) R269347
theorem R195293 : Reach 195293 := rs (se 3 (by rfl) ⟨36617, by rfl⟩) R73235
theorem R129779 : Reach 129779 := rs (se 1 (by rfl) ⟨97334, by rfl⟩) R194669
theorem R129815 : Reach 129815 := rs (se 1 (by rfl) ⟨97361, by rfl⟩) R194723
theorem R326501 : Reach 326501 := rs (se 4 (by rfl) ⟨30609, by rfl⟩) R61219
theorem R64363 : Reach 64363 := rs (se 1 (by rfl) ⟨48272, by rfl⟩) R96545
theorem R195479 : Reach 195479 := rs (se 1 (by rfl) ⟨146609, by rfl⟩) R293219
theorem R129995 : Reach 129995 := rs (se 1 (by rfl) ⟨97496, by rfl⟩) R194993
theorem R64471 : Reach 64471 := rs (se 1 (by rfl) ⟨48353, by rfl⟩) R96707
theorem R130049 : Reach 130049 := rs (se 2 (by rfl) ⟨48768, by rfl⟩) R97537
theorem R195659 : Reach 195659 := rs (se 1 (by rfl) ⟨146744, by rfl⟩) R293489
theorem R97355 : Reach 97355 := rs (se 1 (by rfl) ⟨73016, by rfl⟩) R146033
theorem R64651 : Reach 64651 := rs (se 1 (by rfl) ⟨48488, by rfl⟩) R96977
theorem R97483 : Reach 97483 := rs (se 1 (by rfl) ⟨73112, by rfl⟩) R146225
theorem R130265 : Reach 130265 := rs (se 2 (by rfl) ⟨48849, by rfl⟩) R97699
theorem R64759 : Reach 64759 := rs (se 1 (by rfl) ⟨48569, by rfl⟩) R97139
theorem R130355 : Reach 130355 := rs (se 1 (by rfl) ⟨97766, by rfl⟩) R195533
theorem R130391 : Reach 130391 := rs (se 1 (by rfl) ⟨97793, by rfl⟩) R195587
theorem R97625 : Reach 97625 := rs (se 2 (by rfl) ⟨36609, by rfl⟩) R73219
theorem R64939 : Reach 64939 := rs (se 1 (by rfl) ⟨48704, by rfl⟩) R97409
theorem R196019 : Reach 196019 := rs (se 1 (by rfl) ⟨147014, by rfl⟩) R294029
theorem R97753 : Reach 97753 := rs (se 2 (by rfl) ⟨36657, by rfl⟩) R73315
theorem R130571 : Reach 130571 := rs (se 1 (by rfl) ⟨97928, by rfl⟩) R195857
theorem R327185 : Reach 327185 := rs (se 2 (by rfl) ⟨122694, by rfl⟩) R245389
theorem R65047 : Reach 65047 := rs (se 1 (by rfl) ⟨48785, by rfl⟩) R97571
theorem R130625 : Reach 130625 := rs (se 2 (by rfl) ⟨48984, by rfl⟩) R97969
theorem R196289 : Reach 196289 := rs (se 2 (by rfl) ⟨73608, by rfl⟩) R147217
theorem R65227 : Reach 65227 := rs (se 1 (by rfl) ⟨48920, by rfl⟩) R97841
theorem R196397 : Reach 196397 := rs (se 3 (by rfl) ⟨36824, by rfl⟩) R73649
theorem R130967 : Reach 130967 := rs (se 1 (by rfl) ⟨98225, by rfl⟩) R196451
theorem R1343411 : Reach 1343411 := rs (se 1 (by rfl) ⟨1007558, by rfl⟩) R2015117
theorem R65551 : Reach 65551 := rs (se 1 (by rfl) ⟨49163, by rfl⟩) R98327
theorem R98347 : Reach 98347 := rs (se 1 (by rfl) ⟨73760, by rfl⟩) R147521
theorem R98363 : Reach 98363 := rs (se 1 (by rfl) ⟨73772, by rfl⟩) R147545
theorem R655447 : Reach 655447 := rs (se 1 (by rfl) ⟨491585, by rfl⟩) R983171
theorem R131219 : Reach 131219 := rs (se 1 (by rfl) ⟨98414, by rfl⟩) R196829
theorem R98489 : Reach 98489 := rs (se 2 (by rfl) ⟨36933, by rfl⟩) R73867
theorem R131273 : Reach 131273 := rs (se 2 (by rfl) ⟨49227, by rfl⟩) R98455
theorem R40337621 : Reach 40337621 := rs (se 7 (by rfl) ⟨472706, by rfl⟩) R945413
theorem R426221 : Reach 426221 := rs (se 3 (by rfl) ⟨79916, by rfl⟩) R159833
theorem R131387 : Reach 131387 := rs (se 1 (by rfl) ⟨98540, by rfl⟩) R197081
theorem R2326877 : Reach 2326877 := rs (se 3 (by rfl) ⟨436289, by rfl⟩) R872579
theorem R65911 : Reach 65911 := rs (se 1 (by rfl) ⟨49433, by rfl⟩) R98867
theorem R524675 : Reach 524675 := rs (se 1 (by rfl) ⟨393506, by rfl⟩) R787013
theorem R164231 : Reach 164231 := rs (se 1 (by rfl) ⟨123173, by rfl⟩) R246347
theorem R66055 : Reach 66055 := rs (se 1 (by rfl) ⟨49541, by rfl⟩) R99083
theorem R66091 : Reach 66091 := rs (se 1 (by rfl) ⟨49568, by rfl⟩) R99137
theorem R262723 : Reach 262723 := rs (se 1 (by rfl) ⟨197042, by rfl⟩) R394085
theorem R197207 : Reach 197207 := rs (se 1 (by rfl) ⟨147905, by rfl⟩) R295811
theorem R66235 : Reach 66235 := rs (se 1 (by rfl) ⟨49676, by rfl⟩) R99353
theorem R99191 : Reach 99191 := rs (se 1 (by rfl) ⟨74393, by rfl⟩) R148787
theorem R131975 : Reach 131975 := rs (se 1 (by rfl) ⟨98981, by rfl⟩) R197963
theorem R131993 : Reach 131993 := rs (se 2 (by rfl) ⟨49497, by rfl⟩) R98995
theorem R197585 : Reach 197585 := rs (se 2 (by rfl) ⟨74094, by rfl⟩) R148189
theorem R132155 : Reach 132155 := rs (se 1 (by rfl) ⟨99116, by rfl⟩) R198233
theorem R197693 : Reach 197693 := rs (se 3 (by rfl) ⟨37067, by rfl⟩) R74135
theorem R165017 : Reach 165017 := rs (se 2 (by rfl) ⟨61881, by rfl⟩) R123763
theorem R132281 : Reach 132281 := rs (se 2 (by rfl) ⟨49605, by rfl⟩) R99211
theorem R328961 : Reach 328961 := rs (se 2 (by rfl) ⟨123360, by rfl⟩) R246721
theorem R132353 : Reach 132353 := rs (se 2 (by rfl) ⟨49632, by rfl⟩) R99265
theorem R558353 : Reach 558353 := rs (se 2 (by rfl) ⟨209382, by rfl⟩) R418765
theorem R99643 : Reach 99643 := rs (se 1 (by rfl) ⟨74732, by rfl⟩) R149465
theorem R99731 : Reach 99731 := rs (se 1 (by rfl) ⟨74798, by rfl⟩) R149597
theorem R132553 : Reach 132553 := rs (se 2 (by rfl) ⟨49707, by rfl⟩) R99415
theorem R296459 : Reach 296459 := rs (se 1 (by rfl) ⟨222344, by rfl⟩) R444689
theorem R132623 : Reach 132623 := rs (se 1 (by rfl) ⟨99467, by rfl⟩) R198935
theorem R132641 : Reach 132641 := rs (se 2 (by rfl) ⟨49740, by rfl⟩) R99481
theorem R132695 : Reach 132695 := rs (se 1 (by rfl) ⟨99521, by rfl⟩) R199043
theorem R886373 : Reach 886373 := rs (se 4 (by rfl) ⟨83097, by rfl⟩) R166195
theorem R296567 : Reach 296567 := rs (se 1 (by rfl) ⟨222425, by rfl⟩) R444851
theorem R296621 : Reach 296621 := rs (se 3 (by rfl) ⟨55616, by rfl⟩) R111233
theorem R493249 : Reach 493249 := rs (se 2 (by rfl) ⟨184968, by rfl⟩) R369937
theorem R329417 : Reach 329417 := rs (se 2 (by rfl) ⟨123531, by rfl⟩) R247063
theorem R132875 : Reach 132875 := rs (se 1 (by rfl) ⟨99656, by rfl⟩) R199313
theorem R165665 : Reach 165665 := rs (se 2 (by rfl) ⟨62124, by rfl⟩) R124249
theorem R132983 : Reach 132983 := rs (se 1 (by rfl) ⟨99737, by rfl⟩) R199475
theorem R133049 : Reach 133049 := rs (se 2 (by rfl) ⟨49893, by rfl⟩) R99787
theorem R428165 : Reach 428165 := rs (se 4 (by rfl) ⟨40140, by rfl⟩) R80281
theorem R559507 : Reach 559507 := rs (se 1 (by rfl) ⟨419630, by rfl⟩) R839261
theorem R199097 : Reach 199097 := rs (se 2 (by rfl) ⟨74661, by rfl⟩) R149323
theorem R166657 : Reach 166657 := rs (se 2 (by rfl) ⟨62496, by rfl⟩) R124993
theorem R1018639 : Reach 1018639 := rs (se 1 (by rfl) ⟨763979, by rfl⟩) R1527959
theorem R297881 : Reach 297881 := rs (se 2 (by rfl) ⟨111705, by rfl⟩) R223411
theorem R1281035 : Reach 1281035 := rs (se 1 (by rfl) ⟨960776, by rfl⟩) R1921553
theorem R592919 : Reach 592919 := rs (se 1 (by rfl) ⟨444689, by rfl⟩) R889379
theorem R298241 : Reach 298241 := rs (se 2 (by rfl) ⟨111840, by rfl⟩) R223681
theorem R363809 : Reach 363809 := rs (se 2 (by rfl) ⟨136428, by rfl⟩) R272857
theorem R101779 : Reach 101779 := rs (se 1 (by rfl) ⟨76334, by rfl⟩) R152669
theorem R69179 : Reach 69179 := rs (se 1 (by rfl) ⟨51884, by rfl⟩) R103769
theorem R233027 : Reach 233027 := rs (se 1 (by rfl) ⟨174770, by rfl⟩) R349541
theorem R724787 : Reach 724787 := rs (se 1 (by rfl) ⟨543590, by rfl⟩) R1087181
theorem R233351 : Reach 233351 := rs (se 1 (by rfl) ⟨175013, by rfl⟩) R350027
theorem R429977 : Reach 429977 := rs (se 2 (by rfl) ⟨161241, by rfl⟩) R322483
theorem R299051 : Reach 299051 := rs (se 1 (by rfl) ⟨224288, by rfl⟩) R448577
theorem R561239 : Reach 561239 := rs (se 1 (by rfl) ⟨420929, by rfl⟩) R841859
theorem R135283 : Reach 135283 := rs (se 1 (by rfl) ⟨101462, by rfl⟩) R202925
theorem R70075 : Reach 70075 := rs (se 1 (by rfl) ⟨52556, by rfl⟩) R105113
theorem R430595 : Reach 430595 := rs (se 1 (by rfl) ⟨322946, by rfl⟩) R645893
theorem R70571 : Reach 70571 := rs (se 1 (by rfl) ⟨52928, by rfl⟩) R105857
theorem R332747 : Reach 332747 := rs (se 1 (by rfl) ⟨249560, by rfl⟩) R499121
theorem R332765 : Reach 332765 := rs (se 3 (by rfl) ⟨62393, by rfl⟩) R124787
theorem R169249 : Reach 169249 := rs (se 2 (by rfl) ⟨63468, by rfl⟩) R126937
theorem R169303 : Reach 169303 := rs (se 1 (by rfl) ⟨126977, by rfl⟩) R253955
theorem R71047 : Reach 71047 := rs (se 1 (by rfl) ⟨53285, by rfl⟩) R106571
theorem R333335 : Reach 333335 := rs (se 1 (by rfl) ⟨250001, by rfl⟩) R500003
theorem R71543 : Reach 71543 := rs (se 1 (by rfl) ⟨53657, by rfl⟩) R107315
theorem R333827 : Reach 333827 := rs (se 1 (by rfl) ⟨250370, by rfl⟩) R500741
theorem R71695 : Reach 71695 := rs (se 1 (by rfl) ⟨53771, by rfl⟩) R107543
theorem R137303 : Reach 137303 := rs (se 1 (by rfl) ⟨102977, by rfl⟩) R205955
theorem R71867 : Reach 71867 := rs (se 1 (by rfl) ⟨53900, by rfl⟩) R107801
theorem R104851 : Reach 104851 := rs (se 1 (by rfl) ⟨78638, by rfl⟩) R157277
theorem R1219265 : Reach 1219265 := rs (se 2 (by rfl) ⟨457224, by rfl⟩) R914449
theorem R334745 : Reach 334745 := rs (se 2 (by rfl) ⟨125529, by rfl⟩) R251059
theorem R105401 : Reach 105401 := rs (se 2 (by rfl) ⟨39525, by rfl⟩) R79051
theorem R269335 : Reach 269335 := rs (se 1 (by rfl) ⟨202001, by rfl⟩) R404003
theorem R72839 : Reach 72839 := rs (se 1 (by rfl) ⟨54629, by rfl⟩) R109259
theorem R236915 : Reach 236915 := rs (se 1 (by rfl) ⟨177686, by rfl⟩) R355373
theorem R335249 : Reach 335249 := rs (se 2 (by rfl) ⟨125718, by rfl⟩) R251437
theorem R957905 : Reach 957905 := rs (se 2 (by rfl) ⟨359214, by rfl⟩) R718429
theorem R728605 : Reach 728605 := rs (se 3 (by rfl) ⟨136613, by rfl⟩) R273227
theorem R564965 : Reach 564965 := rs (se 4 (by rfl) ⟨52965, by rfl⟩) R105931
theorem R73487 : Reach 73487 := rs (se 1 (by rfl) ⟨55115, by rfl⟩) R110231
theorem R335933 : Reach 335933 := rs (se 3 (by rfl) ⟨62987, by rfl⟩) R125975
theorem R73801 : Reach 73801 := rs (se 2 (by rfl) ⟨27675, by rfl⟩) R55351
theorem R205001 : Reach 205001 := rs (se 2 (by rfl) ⟨76875, by rfl⟩) R153751
theorem R139553 : Reach 139553 := rs (se 2 (by rfl) ⟨52332, by rfl⟩) R104665
theorem R303545 : Reach 303545 := rs (se 2 (by rfl) ⟨113829, by rfl⟩) R227659
theorem R74297 : Reach 74297 := rs (se 2 (by rfl) ⟨27861, by rfl⟩) R55723
theorem R74425 : Reach 74425 := rs (se 2 (by rfl) ⟨27909, by rfl⟩) R55819
theorem R598873 : Reach 598873 := rs (se 2 (by rfl) ⟨224577, by rfl⟩) R449155
theorem R107399 : Reach 107399 := rs (se 1 (by rfl) ⟨80549, by rfl⟩) R161099
theorem R140555 : Reach 140555 := rs (se 1 (by rfl) ⟨105416, by rfl⟩) R210833
theorem R435941 : Reach 435941 := rs (se 4 (by rfl) ⟨40869, by rfl⟩) R81739
theorem R239375 : Reach 239375 := rs (se 1 (by rfl) ⟨179531, by rfl⟩) R359063
theorem R239419 : Reach 239419 := rs (se 1 (by rfl) ⟨179564, by rfl⟩) R359129
theorem R141203 : Reach 141203 := rs (se 1 (by rfl) ⟨105902, by rfl⟩) R211805
theorem R141497 : Reach 141497 := rs (se 2 (by rfl) ⟨53061, by rfl⟩) R106123
theorem R272641 : Reach 272641 := rs (se 2 (by rfl) ⟨102240, by rfl⟩) R204481
theorem R109001 : Reach 109001 := rs (se 2 (by rfl) ⟨40875, by rfl⟩) R81751
theorem R600605 : Reach 600605 := rs (se 3 (by rfl) ⟨112613, by rfl⟩) R225227
theorem R600641 : Reach 600641 := rs (se 2 (by rfl) ⟨225240, by rfl⟩) R450481
theorem R895607 : Reach 895607 := rs (se 1 (by rfl) ⟨671705, by rfl⟩) R1343411
theorem R666305 : Reach 666305 := rs (se 2 (by rfl) ⟨249864, by rfl⟩) R499729
theorem R142195 : Reach 142195 := rs (se 1 (by rfl) ⟨106646, by rfl⟩) R213293
theorem R142337 : Reach 142337 := rs (se 2 (by rfl) ⟨53376, by rfl⟩) R106753
theorem R371735 : Reach 371735 := rs (se 1 (by rfl) ⟨278801, by rfl⟩) R557603
theorem R240707 : Reach 240707 := rs (se 1 (by rfl) ⟨180530, by rfl⟩) R361061
theorem R1387651 : Reach 1387651 := rs (se 1 (by rfl) ⟨1040738, by rfl⟩) R2081477
theorem R241049 : Reach 241049 := rs (se 2 (by rfl) ⟨90393, by rfl⟩) R180787
theorem R503225 : Reach 503225 := rs (se 2 (by rfl) ⟨188709, by rfl⟩) R377419
theorem R142793 : Reach 142793 := rs (se 2 (by rfl) ⟨53547, by rfl⟩) R107095
theorem R143147 : Reach 143147 := rs (se 1 (by rfl) ⟨107360, by rfl⟩) R214721
theorem R110983 : Reach 110983 := rs (se 1 (by rfl) ⟨83237, by rfl⟩) R166475
theorem R144139 : Reach 144139 := rs (se 1 (by rfl) ⟨108104, by rfl⟩) R216209
theorem R78607 : Reach 78607 := rs (se 1 (by rfl) ⟨58955, by rfl⟩) R117911
theorem R471845 : Reach 471845 := rs (se 4 (by rfl) ⟨44235, by rfl⟩) R88471
theorem R78727 : Reach 78727 := rs (se 1 (by rfl) ⟨59045, by rfl⟩) R118091
theorem R144281 : Reach 144281 := rs (se 2 (by rfl) ⟨54105, by rfl⟩) R108211
theorem R668569 : Reach 668569 := rs (se 2 (by rfl) ⟨250713, by rfl⟩) R501427
theorem R144443 : Reach 144443 := rs (se 1 (by rfl) ⟨108332, by rfl⟩) R216665
theorem R177353 : Reach 177353 := rs (se 2 (by rfl) ⟨66507, by rfl⟩) R133015
theorem R341263 : Reach 341263 := rs (se 1 (by rfl) ⟨255947, by rfl⟩) R511895
theorem R308627 : Reach 308627 := rs (se 1 (by rfl) ⟨231470, by rfl⟩) R462941
theorem R144787 : Reach 144787 := rs (se 1 (by rfl) ⟨108590, by rfl⟩) R217181
theorem R1291697 : Reach 1291697 := rs (se 2 (by rfl) ⟨484386, by rfl⟩) R968773
theorem R144929 : Reach 144929 := rs (se 2 (by rfl) ⟨54348, by rfl⟩) R108697
theorem R112313 : Reach 112313 := rs (se 2 (by rfl) ⟨42117, by rfl⟩) R84235
theorem R997271 : Reach 997271 := rs (se 1 (by rfl) ⟨747953, by rfl⟩) R1495907
theorem R211031 : Reach 211031 := rs (se 1 (by rfl) ⟨158273, by rfl⟩) R316547
theorem R80185 : Reach 80185 := rs (se 2 (by rfl) ⟨30069, by rfl⟩) R60139
theorem R145921 : Reach 145921 := rs (se 2 (by rfl) ⟨54720, by rfl⟩) R109441
theorem R211517 : Reach 211517 := rs (se 3 (by rfl) ⟨39659, by rfl⟩) R79319
theorem R440909 : Reach 440909 := rs (se 3 (by rfl) ⟨82670, by rfl⟩) R165341
theorem R113707 : Reach 113707 := rs (se 1 (by rfl) ⟨85280, by rfl⟩) R170561
theorem R146519 : Reach 146519 := rs (se 1 (by rfl) ⟨109889, by rfl⟩) R219779
theorem R146731 : Reach 146731 := rs (se 1 (by rfl) ⟨110048, by rfl⟩) R220097
theorem R146873 : Reach 146873 := rs (se 2 (by rfl) ⟨55077, by rfl⟩) R110155
theorem R376285 : Reach 376285 := rs (se 3 (by rfl) ⟨70553, by rfl⟩) R141107
theorem R81415 : Reach 81415 := rs (se 1 (by rfl) ⟨61061, by rfl⟩) R122123
theorem R147005 : Reach 147005 := rs (se 3 (by rfl) ⟨27563, by rfl⟩) R55127
theorem R213263 : Reach 213263 := rs (se 1 (by rfl) ⟨159947, by rfl⟩) R319895
theorem R82235 : Reach 82235 := rs (se 1 (by rfl) ⟨61676, by rfl⟩) R123353
theorem R147865 : Reach 147865 := rs (se 2 (by rfl) ⟨55449, by rfl⟩) R110899
theorem R4047317 : Reach 4047317 := rs (se 7 (by rfl) ⟨47429, by rfl⟩) R94859
theorem R148027 : Reach 148027 := rs (se 1 (by rfl) ⟨111020, by rfl⟩) R222041
theorem R148169 : Reach 148169 := rs (se 2 (by rfl) ⟨55563, by rfl⟩) R111127
theorem R82703 : Reach 82703 := rs (se 1 (by rfl) ⟨62027, by rfl⟩) R124055
theorem R803621 : Reach 803621 := rs (se 4 (by rfl) ⟨75339, by rfl⟩) R150679
theorem R82745 : Reach 82745 := rs (se 2 (by rfl) ⟨31029, by rfl⟩) R62059
theorem R82823 : Reach 82823 := rs (se 1 (by rfl) ⟨62117, by rfl⟩) R124235
theorem R279449 : Reach 279449 := rs (se 2 (by rfl) ⟨104793, by rfl⟩) R209587
theorem R82859 : Reach 82859 := rs (se 1 (by rfl) ⟨62144, by rfl⟩) R124289
theorem R82873 : Reach 82873 := rs (se 2 (by rfl) ⟨31077, by rfl⟩) R62155
theorem R82889 : Reach 82889 := rs (se 2 (by rfl) ⟨31083, by rfl⟩) R62167
theorem R148513 : Reach 148513 := rs (se 2 (by rfl) ⟨55692, by rfl⟩) R111385
theorem R83003 : Reach 83003 := rs (se 1 (by rfl) ⟨62252, by rfl⟩) R124505
theorem R640061 : Reach 640061 := rs (se 3 (by rfl) ⟨120011, by rfl⟩) R240023
theorem R83063 : Reach 83063 := rs (se 1 (by rfl) ⟨62297, by rfl⟩) R124595
theorem R83087 : Reach 83087 := rs (se 1 (by rfl) ⟨62315, by rfl⟩) R124631
theorem R83129 : Reach 83129 := rs (se 2 (by rfl) ⟨31173, by rfl⟩) R62347
theorem R83207 : Reach 83207 := rs (se 1 (by rfl) ⟨62405, by rfl⟩) R124811
theorem R83243 : Reach 83243 := rs (se 1 (by rfl) ⟨62432, by rfl⟩) R124865
theorem R83273 : Reach 83273 := rs (se 2 (by rfl) ⟨31227, by rfl⟩) R62455
theorem R83387 : Reach 83387 := rs (se 1 (by rfl) ⟨62540, by rfl⟩) R125081
theorem R83447 : Reach 83447 := rs (se 1 (by rfl) ⟨62585, by rfl⟩) R125171
theorem R83471 : Reach 83471 := rs (se 1 (by rfl) ⟨62603, by rfl⟩) R125207
theorem R83513 : Reach 83513 := rs (se 2 (by rfl) ⟨31317, by rfl⟩) R62635
theorem R542285 : Reach 542285 := rs (se 3 (by rfl) ⟨101678, by rfl⟩) R203357
theorem R149111 : Reach 149111 := rs (se 1 (by rfl) ⟨111833, by rfl⟩) R223667
theorem R83591 : Reach 83591 := rs (se 1 (by rfl) ⟨62693, by rfl⟩) R125387
theorem R83627 : Reach 83627 := rs (se 1 (by rfl) ⟨62720, by rfl⟩) R125441
theorem R83657 : Reach 83657 := rs (se 2 (by rfl) ⟨31371, by rfl⟩) R62743
theorem R182017 : Reach 182017 := rs (se 2 (by rfl) ⟨68256, by rfl⟩) R136513
theorem R542513 : Reach 542513 := rs (se 2 (by rfl) ⟨203442, by rfl⟩) R406885
theorem R83771 : Reach 83771 := rs (se 1 (by rfl) ⟨62828, by rfl⟩) R125657
theorem R83831 : Reach 83831 := rs (se 1 (by rfl) ⟨62873, by rfl⟩) R125747
theorem R214919 : Reach 214919 := rs (se 1 (by rfl) ⟨161189, by rfl⟩) R322379
theorem R83855 : Reach 83855 := rs (se 1 (by rfl) ⟨62891, by rfl⟩) R125783
theorem R83897 : Reach 83897 := rs (se 2 (by rfl) ⟨31461, by rfl⟩) R62923
theorem R83975 : Reach 83975 := rs (se 1 (by rfl) ⟨62981, by rfl⟩) R125963
theorem R84011 : Reach 84011 := rs (se 1 (by rfl) ⟨63008, by rfl⟩) R126017
theorem R84041 : Reach 84041 := rs (se 2 (by rfl) ⟨31515, by rfl⟩) R63031
theorem R1001645 : Reach 1001645 := rs (se 3 (by rfl) ⟨187808, by rfl⟩) R375617
theorem R84155 : Reach 84155 := rs (se 1 (by rfl) ⟨63116, by rfl⟩) R126233
theorem R84215 : Reach 84215 := rs (se 1 (by rfl) ⟨63161, by rfl⟩) R126323
theorem R84239 : Reach 84239 := rs (se 1 (by rfl) ⟨63179, by rfl⟩) R126359
theorem R84281 : Reach 84281 := rs (se 2 (by rfl) ⟨31605, by rfl⟩) R63211
theorem R248123 : Reach 248123 := rs (se 1 (by rfl) ⟨186092, by rfl⟩) R372185
theorem R84359 : Reach 84359 := rs (se 1 (by rfl) ⟨63269, by rfl⟩) R126539
theorem R84395 : Reach 84395 := rs (se 1 (by rfl) ⟨63296, by rfl⟩) R126593
theorem R84425 : Reach 84425 := rs (se 2 (by rfl) ⟨31659, by rfl⟩) R63319
theorem R84539 : Reach 84539 := rs (se 1 (by rfl) ⟨63404, by rfl⟩) R126809
theorem R84599 : Reach 84599 := rs (se 1 (by rfl) ⟨63449, by rfl⟩) R126899
theorem R84623 : Reach 84623 := rs (se 1 (by rfl) ⟨63467, by rfl⟩) R126935
theorem R84665 : Reach 84665 := rs (se 2 (by rfl) ⟨31749, by rfl⟩) R63499
theorem R84743 : Reach 84743 := rs (se 1 (by rfl) ⟨63557, by rfl⟩) R127115
theorem R84779 : Reach 84779 := rs (se 1 (by rfl) ⟨63584, by rfl⟩) R127169
theorem R84809 : Reach 84809 := rs (se 2 (by rfl) ⟨31803, by rfl⟩) R63607
theorem R84923 : Reach 84923 := rs (se 1 (by rfl) ⟨63692, by rfl⟩) R127385
theorem R84983 : Reach 84983 := rs (se 1 (by rfl) ⟨63737, by rfl⟩) R127475
theorem R85007 : Reach 85007 := rs (se 1 (by rfl) ⟨63755, by rfl⟩) R127511
theorem R85049 : Reach 85049 := rs (se 2 (by rfl) ⟨31893, by rfl⟩) R63787
theorem R805949 : Reach 805949 := rs (se 3 (by rfl) ⟨151115, by rfl⟩) R302231
theorem R85127 : Reach 85127 := rs (se 1 (by rfl) ⟨63845, by rfl⟩) R127691
theorem R85163 : Reach 85163 := rs (se 1 (by rfl) ⟨63872, by rfl⟩) R127745
theorem R85193 : Reach 85193 := rs (se 2 (by rfl) ⟨31947, by rfl⟩) R63895
theorem R85307 : Reach 85307 := rs (se 1 (by rfl) ⟨63980, by rfl⟩) R127961
theorem R85367 : Reach 85367 := rs (se 1 (by rfl) ⟨64025, by rfl⟩) R128051
theorem R85391 : Reach 85391 := rs (se 1 (by rfl) ⟨64043, by rfl⟩) R128087
theorem R118201 : Reach 118201 := rs (se 2 (by rfl) ⟨44325, by rfl⟩) R88651
theorem R282041 : Reach 282041 := rs (se 2 (by rfl) ⟨105765, by rfl⟩) R211531
theorem R85433 : Reach 85433 := rs (se 2 (by rfl) ⟨32037, by rfl⟩) R64075
theorem R85511 : Reach 85511 := rs (se 1 (by rfl) ⟨64133, by rfl⟩) R128267
theorem R85547 : Reach 85547 := rs (se 1 (by rfl) ⟨64160, by rfl⟩) R128321
theorem R85577 : Reach 85577 := rs (se 2 (by rfl) ⟨32091, by rfl⟩) R64183
theorem R216695 : Reach 216695 := rs (se 1 (by rfl) ⟨162521, by rfl⟩) R325043
theorem R85691 : Reach 85691 := rs (se 1 (by rfl) ⟨64268, by rfl⟩) R128537
theorem R85751 : Reach 85751 := rs (se 1 (by rfl) ⟨64313, by rfl⟩) R128627
theorem R118543 : Reach 118543 := rs (se 1 (by rfl) ⟨88907, by rfl⟩) R177815
theorem R85775 : Reach 85775 := rs (se 1 (by rfl) ⟨64331, by rfl⟩) R128663
theorem R85817 : Reach 85817 := rs (se 2 (by rfl) ⟨32181, by rfl⟩) R64363
theorem R85895 : Reach 85895 := rs (se 1 (by rfl) ⟨64421, by rfl⟩) R128843
theorem R905111 : Reach 905111 := rs (se 1 (by rfl) ⟨678833, by rfl⟩) R1357667
theorem R85931 : Reach 85931 := rs (se 1 (by rfl) ⟨64448, by rfl⟩) R128897
theorem R85961 : Reach 85961 := rs (se 2 (by rfl) ⟨32235, by rfl⟩) R64471
theorem R86075 : Reach 86075 := rs (se 1 (by rfl) ⟨64556, by rfl⟩) R129113
theorem R86135 : Reach 86135 := rs (se 1 (by rfl) ⟨64601, by rfl⟩) R129203
theorem R86159 : Reach 86159 := rs (se 1 (by rfl) ⟨64619, by rfl⟩) R129239
theorem R86201 : Reach 86201 := rs (se 2 (by rfl) ⟨32325, by rfl⟩) R64651
theorem R86279 : Reach 86279 := rs (se 1 (by rfl) ⟨64709, by rfl⟩) R129419
theorem R86315 : Reach 86315 := rs (se 1 (by rfl) ⟨64736, by rfl⟩) R129473
theorem R414011 : Reach 414011 := rs (se 1 (by rfl) ⟨310508, by rfl⟩) R621017
theorem R86345 : Reach 86345 := rs (se 2 (by rfl) ⟨32379, by rfl⟩) R64759
theorem R86459 : Reach 86459 := rs (se 1 (by rfl) ⟨64844, by rfl⟩) R129689
theorem R86519 : Reach 86519 := rs (se 1 (by rfl) ⟨64889, by rfl⟩) R129779
theorem R86543 : Reach 86543 := rs (se 1 (by rfl) ⟨64907, by rfl⟩) R129815
theorem R250397 : Reach 250397 := rs (se 3 (by rfl) ⟨46949, by rfl⟩) R93899
theorem R86585 : Reach 86585 := rs (se 2 (by rfl) ⟨32469, by rfl⟩) R64939
theorem R217667 : Reach 217667 := rs (se 1 (by rfl) ⟨163250, by rfl⟩) R326501
theorem R119431 : Reach 119431 := rs (se 1 (by rfl) ⟨89573, by rfl⟩) R179147
theorem R86663 : Reach 86663 := rs (se 1 (by rfl) ⟨64997, by rfl⟩) R129995
theorem R86699 : Reach 86699 := rs (se 1 (by rfl) ⟨65024, by rfl⟩) R130049
theorem R283337 : Reach 283337 := rs (se 2 (by rfl) ⟨106251, by rfl⟩) R212503
theorem R86729 : Reach 86729 := rs (se 2 (by rfl) ⟨32523, by rfl⟩) R65047
theorem R86843 : Reach 86843 := rs (se 1 (by rfl) ⟨65132, by rfl⟩) R130265
theorem R86903 : Reach 86903 := rs (se 1 (by rfl) ⟨65177, by rfl⟩) R130355
theorem R316295 : Reach 316295 := rs (se 1 (by rfl) ⟨237221, by rfl⟩) R474443
theorem R86927 : Reach 86927 := rs (se 1 (by rfl) ⟨65195, by rfl⟩) R130391
theorem R185273 : Reach 185273 := rs (se 2 (by rfl) ⟨69477, by rfl⟩) R138955
theorem R86969 : Reach 86969 := rs (se 2 (by rfl) ⟨32613, by rfl⟩) R65227
theorem R87047 : Reach 87047 := rs (se 1 (by rfl) ⟨65285, by rfl⟩) R130571
theorem R218123 : Reach 218123 := rs (se 1 (by rfl) ⟨163592, by rfl⟩) R327185
theorem R87083 : Reach 87083 := rs (se 1 (by rfl) ⟨65312, by rfl⟩) R130625
theorem R87311 : Reach 87311 := rs (se 1 (by rfl) ⟨65483, by rfl⟩) R130967
theorem R87431 : Reach 87431 := rs (se 1 (by rfl) ⟨65573, by rfl⟩) R131147
theorem R87497 : Reach 87497 := rs (se 2 (by rfl) ⟨32811, by rfl⟩) R65623
theorem R87611 : Reach 87611 := rs (se 1 (by rfl) ⟨65708, by rfl⟩) R131417
theorem R317047 : Reach 317047 := rs (se 1 (by rfl) ⟨237785, by rfl⟩) R475571
theorem R87671 : Reach 87671 := rs (se 1 (by rfl) ⟨65753, by rfl⟩) R131507
theorem R87737 : Reach 87737 := rs (se 2 (by rfl) ⟨32901, by rfl⟩) R65803
theorem R120619 : Reach 120619 := rs (se 1 (by rfl) ⟨90464, by rfl⟩) R180929
theorem R87851 : Reach 87851 := rs (se 1 (by rfl) ⟨65888, by rfl⟩) R131777
theorem R907057 : Reach 907057 := rs (se 2 (by rfl) ⟨340146, by rfl⟩) R680293
theorem R120695 : Reach 120695 := rs (se 1 (by rfl) ⟨90521, by rfl⟩) R181043
theorem R55175 : Reach 55175 := rs (se 1 (by rfl) ⟨41381, by rfl⟩) R82763
theorem R55183 : Reach 55183 := rs (se 1 (by rfl) ⟨41387, by rfl⟩) R82775
theorem R415651 : Reach 415651 := rs (se 1 (by rfl) ⟨311738, by rfl⟩) R623477
theorem R55227 : Reach 55227 := rs (se 1 (by rfl) ⟨41420, by rfl⟩) R82841
theorem R55303 : Reach 55303 := rs (se 1 (by rfl) ⟨41477, by rfl⟩) R82955
theorem R55311 : Reach 55311 := rs (se 1 (by rfl) ⟨41483, by rfl⟩) R82967
theorem R88079 : Reach 88079 := rs (se 1 (by rfl) ⟨66059, by rfl⟩) R132119
theorem R55355 : Reach 55355 := rs (se 1 (by rfl) ⟨41516, by rfl⟩) R83033
theorem R55431 : Reach 55431 := rs (se 1 (by rfl) ⟨41573, by rfl⟩) R83147
theorem R88199 : Reach 88199 := rs (se 1 (by rfl) ⟨66149, by rfl⟩) R132299
theorem R55439 : Reach 55439 := rs (se 1 (by rfl) ⟨41579, by rfl⟩) R83159
theorem R55483 : Reach 55483 := rs (se 1 (by rfl) ⟨41612, by rfl⟩) R83225
theorem R186569 : Reach 186569 := rs (se 2 (by rfl) ⟨69963, by rfl⟩) R139927
theorem R88265 : Reach 88265 := rs (se 2 (by rfl) ⟨33099, by rfl⟩) R66199
theorem R55559 : Reach 55559 := rs (se 1 (by rfl) ⟨41669, by rfl⟩) R83339
theorem R55567 : Reach 55567 := rs (se 1 (by rfl) ⟨41675, by rfl⟩) R83351
theorem R55611 : Reach 55611 := rs (se 1 (by rfl) ⟨41708, by rfl⟩) R83417
theorem R88379 : Reach 88379 := rs (se 1 (by rfl) ⟨66284, by rfl⟩) R132569
theorem R88439 : Reach 88439 := rs (se 1 (by rfl) ⟨66329, by rfl⟩) R132659
theorem R55687 : Reach 55687 := rs (se 1 (by rfl) ⟨41765, by rfl⟩) R83531
theorem R55695 : Reach 55695 := rs (se 1 (by rfl) ⟨41771, by rfl⟩) R83543
theorem R514451 : Reach 514451 := rs (se 1 (by rfl) ⟨385838, by rfl⟩) R771677
theorem R88505 : Reach 88505 := rs (se 2 (by rfl) ⟨33189, by rfl⟩) R66379
theorem R55739 : Reach 55739 := rs (se 1 (by rfl) ⟨41804, by rfl⟩) R83609
theorem R55815 : Reach 55815 := rs (se 1 (by rfl) ⟨41861, by rfl⟩) R83723
theorem R55823 : Reach 55823 := rs (se 1 (by rfl) ⟨41867, by rfl⟩) R83735
theorem R88619 : Reach 88619 := rs (se 1 (by rfl) ⟨66464, by rfl⟩) R132929
theorem R55867 : Reach 55867 := rs (se 1 (by rfl) ⟨41900, by rfl⟩) R83801
theorem R55943 : Reach 55943 := rs (se 1 (by rfl) ⟨41957, by rfl⟩) R83915
theorem R55951 : Reach 55951 := rs (se 1 (by rfl) ⟨41963, by rfl⟩) R83927
theorem R55995 : Reach 55995 := rs (se 1 (by rfl) ⟨41996, by rfl⟩) R83993
theorem R56071 : Reach 56071 := rs (se 1 (by rfl) ⟨42053, by rfl⟩) R84107
theorem R56079 : Reach 56079 := rs (se 1 (by rfl) ⟨42059, by rfl⟩) R84119
theorem R56123 : Reach 56123 := rs (se 1 (by rfl) ⟨42092, by rfl⟩) R84185
theorem R1891187 : Reach 1891187 := rs (se 1 (by rfl) ⟨1418390, by rfl⟩) R2836781
theorem R154487 : Reach 154487 := rs (se 1 (by rfl) ⟨115865, by rfl⟩) R231731
theorem R187271 : Reach 187271 := rs (se 1 (by rfl) ⟨140453, by rfl⟩) R280907
theorem R56199 : Reach 56199 := rs (se 1 (by rfl) ⟨42149, by rfl⟩) R84299
theorem R56207 : Reach 56207 := rs (se 1 (by rfl) ⟨42155, by rfl⟩) R84311
theorem R56251 : Reach 56251 := rs (se 1 (by rfl) ⟨42188, by rfl⟩) R84377
theorem R56327 : Reach 56327 := rs (se 1 (by rfl) ⟨42245, by rfl⟩) R84491
theorem R56335 : Reach 56335 := rs (se 1 (by rfl) ⟨42251, by rfl⟩) R84503
theorem R56379 : Reach 56379 := rs (se 1 (by rfl) ⟨42284, by rfl⟩) R84569
theorem R613493 : Reach 613493 := rs (se 5 (by rfl) ⟨28757, by rfl⟩) R57515
theorem R220279 : Reach 220279 := rs (se 1 (by rfl) ⟨165209, by rfl⟩) R330419
theorem R56455 : Reach 56455 := rs (se 1 (by rfl) ⟨42341, by rfl⟩) R84683
theorem R56463 : Reach 56463 := rs (se 1 (by rfl) ⟨42347, by rfl⟩) R84695
theorem R56507 : Reach 56507 := rs (se 1 (by rfl) ⟨42380, by rfl⟩) R84761
theorem R187649 : Reach 187649 := rs (se 2 (by rfl) ⟨70368, by rfl⟩) R140737
theorem R56583 : Reach 56583 := rs (se 1 (by rfl) ⟨42437, by rfl⟩) R84875
theorem R56591 : Reach 56591 := rs (se 1 (by rfl) ⟨42443, by rfl⟩) R84887
theorem R56635 : Reach 56635 := rs (se 1 (by rfl) ⟨42476, by rfl⟩) R84953
theorem R155015 : Reach 155015 := rs (se 1 (by rfl) ⟨116261, by rfl⟩) R232523
theorem R56711 : Reach 56711 := rs (se 1 (by rfl) ⟨42533, by rfl⟩) R85067
theorem R56719 : Reach 56719 := rs (se 1 (by rfl) ⟨42539, by rfl⟩) R85079
theorem R56763 : Reach 56763 := rs (se 1 (by rfl) ⟨42572, by rfl⟩) R85145
theorem R155081 : Reach 155081 := rs (se 2 (by rfl) ⟨58155, by rfl⟩) R116311
theorem R679427 : Reach 679427 := rs (se 1 (by rfl) ⟨509570, by rfl⟩) R1019141
theorem R56839 : Reach 56839 := rs (se 1 (by rfl) ⟨42629, by rfl⟩) R85259
theorem R56847 : Reach 56847 := rs (se 1 (by rfl) ⟨42635, by rfl⟩) R85271
theorem R56891 : Reach 56891 := rs (se 1 (by rfl) ⟨42668, by rfl⟩) R85337
theorem R745037 : Reach 745037 := rs (se 3 (by rfl) ⟨139694, by rfl⟩) R279389
theorem R56967 : Reach 56967 := rs (se 1 (by rfl) ⟨42725, by rfl⟩) R85451
theorem R56975 : Reach 56975 := rs (se 1 (by rfl) ⟨42731, by rfl⟩) R85463
theorem R57019 : Reach 57019 := rs (se 1 (by rfl) ⟨42764, by rfl⟩) R85529
theorem R319177 : Reach 319177 := rs (se 2 (by rfl) ⟨119691, by rfl⟩) R239383
theorem R57095 : Reach 57095 := rs (se 1 (by rfl) ⟨42821, by rfl⟩) R85643
theorem R57103 : Reach 57103 := rs (se 1 (by rfl) ⟨42827, by rfl⟩) R85655
theorem R57147 : Reach 57147 := rs (se 1 (by rfl) ⟨42860, by rfl⟩) R85721
theorem R188219 : Reach 188219 := rs (se 1 (by rfl) ⟨141164, by rfl⟩) R282329
theorem R57223 : Reach 57223 := rs (se 1 (by rfl) ⟨42917, by rfl⟩) R85835
theorem R57231 : Reach 57231 := rs (se 1 (by rfl) ⟨42923, by rfl⟩) R85847
theorem R57275 : Reach 57275 := rs (se 1 (by rfl) ⟨42956, by rfl⟩) R85913
theorem R57351 : Reach 57351 := rs (se 1 (by rfl) ⟨43013, by rfl⟩) R86027
theorem R57359 : Reach 57359 := rs (se 1 (by rfl) ⟨43019, by rfl⟩) R86039
theorem R188459 : Reach 188459 := rs (se 1 (by rfl) ⟨141344, by rfl⟩) R282689
theorem R57403 : Reach 57403 := rs (se 1 (by rfl) ⟨43052, by rfl⟩) R86105
theorem R188477 : Reach 188477 := rs (se 3 (by rfl) ⟨35339, by rfl⟩) R70679
theorem R221251 : Reach 221251 := rs (se 1 (by rfl) ⟨165938, by rfl⟩) R331877
theorem R57479 : Reach 57479 := rs (se 1 (by rfl) ⟨43109, by rfl⟩) R86219
theorem R57487 : Reach 57487 := rs (se 1 (by rfl) ⟨43115, by rfl⟩) R86231
theorem R57531 : Reach 57531 := rs (se 1 (by rfl) ⟨43148, by rfl⟩) R86297
theorem R57607 : Reach 57607 := rs (se 1 (by rfl) ⟨43205, by rfl⟩) R86411
theorem R57615 : Reach 57615 := rs (se 1 (by rfl) ⟨43211, by rfl⟩) R86423
theorem R57659 : Reach 57659 := rs (se 1 (by rfl) ⟨43244, by rfl⟩) R86489
theorem R1171805 : Reach 1171805 := rs (se 3 (by rfl) ⟨219713, by rfl⟩) R439427
theorem R221555 : Reach 221555 := rs (se 1 (by rfl) ⟨166166, by rfl⟩) R332333
theorem R57735 : Reach 57735 := rs (se 1 (by rfl) ⟨43301, by rfl⟩) R86603
theorem R57743 : Reach 57743 := rs (se 1 (by rfl) ⟨43307, by rfl⟩) R86615
theorem R451001 : Reach 451001 := rs (se 2 (by rfl) ⟨169125, by rfl⟩) R338251
theorem R57787 : Reach 57787 := rs (se 1 (by rfl) ⟨43340, by rfl⟩) R86681
theorem R57863 : Reach 57863 := rs (se 1 (by rfl) ⟨43397, by rfl⟩) R86795
theorem R57871 : Reach 57871 := rs (se 1 (by rfl) ⟨43403, by rfl⟩) R86807
theorem R57915 : Reach 57915 := rs (se 1 (by rfl) ⟨43436, by rfl⟩) R86873
theorem R57991 : Reach 57991 := rs (se 1 (by rfl) ⟨43493, by rfl⟩) R86987
theorem R57999 : Reach 57999 := rs (se 1 (by rfl) ⟨43499, by rfl⟩) R86999
theorem R58043 : Reach 58043 := rs (se 1 (by rfl) ⟨43532, by rfl⟩) R87065
theorem R58119 : Reach 58119 := rs (se 1 (by rfl) ⟨43589, by rfl⟩) R87179
theorem R58127 : Reach 58127 := rs (se 1 (by rfl) ⟨43595, by rfl⟩) R87191
theorem R58171 : Reach 58171 := rs (se 1 (by rfl) ⟨43628, by rfl⟩) R87257
theorem R222011 : Reach 222011 := rs (se 1 (by rfl) ⟨166508, by rfl⟩) R333017
theorem R58247 : Reach 58247 := rs (se 1 (by rfl) ⟨43685, by rfl⟩) R87371
theorem R58255 : Reach 58255 := rs (se 1 (by rfl) ⟨43691, by rfl⟩) R87383
theorem R58299 : Reach 58299 := rs (se 1 (by rfl) ⟨43724, by rfl⟩) R87449
theorem R58375 : Reach 58375 := rs (se 1 (by rfl) ⟨43781, by rfl⟩) R87563
theorem R58383 : Reach 58383 := rs (se 1 (by rfl) ⟨43787, by rfl⟩) R87575
theorem R58427 : Reach 58427 := rs (se 1 (by rfl) ⟨43820, by rfl⟩) R87641
theorem R58503 : Reach 58503 := rs (se 1 (by rfl) ⟨43877, by rfl⟩) R87755
theorem R58511 : Reach 58511 := rs (se 1 (by rfl) ⟨43883, by rfl⟩) R87767
theorem R58555 : Reach 58555 := rs (se 1 (by rfl) ⟨43916, by rfl⟩) R87833
theorem R124105 : Reach 124105 := rs (se 2 (by rfl) ⟨46539, by rfl⟩) R93079
theorem R287981 : Reach 287981 := rs (se 3 (by rfl) ⟨53996, by rfl⟩) R107993
theorem R58631 : Reach 58631 := rs (se 1 (by rfl) ⟨43973, by rfl⟩) R87947
theorem R58639 : Reach 58639 := rs (se 1 (by rfl) ⟨43979, by rfl⟩) R87959
theorem R222497 : Reach 222497 := rs (se 2 (by rfl) ⟨83436, by rfl⟩) R166873
theorem R189755 : Reach 189755 := rs (se 1 (by rfl) ⟨142316, by rfl⟩) R284633
theorem R58683 : Reach 58683 := rs (se 1 (by rfl) ⟨44012, by rfl⟩) R88025
theorem R58759 : Reach 58759 := rs (se 1 (by rfl) ⟨44069, by rfl⟩) R88139
theorem R58767 : Reach 58767 := rs (se 1 (by rfl) ⟨44075, by rfl⟩) R88151
theorem R124307 : Reach 124307 := rs (se 1 (by rfl) ⟨93230, by rfl⟩) R186461
theorem R320921 : Reach 320921 := rs (se 2 (by rfl) ⟨120345, by rfl⟩) R240691
theorem R58811 : Reach 58811 := rs (se 1 (by rfl) ⟨44108, by rfl⟩) R88217
theorem R124361 : Reach 124361 := rs (se 2 (by rfl) ⟨46635, by rfl⟩) R93271
theorem R58887 : Reach 58887 := rs (se 1 (by rfl) ⟨44165, by rfl⟩) R88331
theorem R58895 : Reach 58895 := rs (se 1 (by rfl) ⟨44171, by rfl⟩) R88343
theorem R58939 : Reach 58939 := rs (se 1 (by rfl) ⟨44204, by rfl⟩) R88409
theorem R59015 : Reach 59015 := rs (se 1 (by rfl) ⟨44261, by rfl⟩) R88523
theorem R59023 : Reach 59023 := rs (se 1 (by rfl) ⟨44267, by rfl⟩) R88535
theorem R59067 : Reach 59067 := rs (se 1 (by rfl) ⟨44300, by rfl⟩) R88601
theorem R91849 : Reach 91849 := rs (se 2 (by rfl) ⟨34443, by rfl⟩) R68887
theorem R190241 : Reach 190241 := rs (se 2 (by rfl) ⟨71340, by rfl⟩) R142681
theorem R157555 : Reach 157555 := rs (se 1 (by rfl) ⟨118166, by rfl⟩) R236333
theorem R92105 : Reach 92105 := rs (se 2 (by rfl) ⟨34539, by rfl⟩) R69079
theorem R157783 : Reach 157783 := rs (se 1 (by rfl) ⟨118337, by rfl⟩) R236675
theorem R125063 : Reach 125063 := rs (se 1 (by rfl) ⟨93797, by rfl⟩) R187595
theorem R223469 : Reach 223469 := rs (se 3 (by rfl) ⟨41900, by rfl⟩) R83801
theorem R92431 : Reach 92431 := rs (se 1 (by rfl) ⟨69323, by rfl⟩) R138647
theorem R125243 : Reach 125243 := rs (se 1 (by rfl) ⟨93932, by rfl⟩) R187865
theorem R59707 : Reach 59707 := rs (se 1 (by rfl) ⟨44780, by rfl⟩) R89561
theorem R190835 : Reach 190835 := rs (se 1 (by rfl) ⟨143126, by rfl⟩) R286253
theorem R289169 : Reach 289169 := rs (se 2 (by rfl) ⟨108438, by rfl⟩) R216877
theorem R125369 : Reach 125369 := rs (se 2 (by rfl) ⟨47013, by rfl⟩) R94027
theorem R322001 : Reach 322001 := rs (se 2 (by rfl) ⟨120750, by rfl⟩) R241501
theorem R125711 : Reach 125711 := rs (se 1 (by rfl) ⟨94283, by rfl⟩) R188567
theorem R125729 : Reach 125729 := rs (se 2 (by rfl) ⟨47148, by rfl⟩) R94297
theorem R1076003 : Reach 1076003 := rs (se 1 (by rfl) ⟨807002, by rfl⟩) R1614005
theorem R92971 : Reach 92971 := rs (se 1 (by rfl) ⟨69728, by rfl⟩) R139457
theorem R224153 : Reach 224153 := rs (se 2 (by rfl) ⟨84057, by rfl⟩) R168115
theorem R420875 : Reach 420875 := rs (se 1 (by rfl) ⟨315656, by rfl⟩) R631313
theorem R126071 : Reach 126071 := rs (se 1 (by rfl) ⟨94553, by rfl⟩) R189107
theorem R126251 : Reach 126251 := rs (se 1 (by rfl) ⟨94688, by rfl⟩) R189377
theorem R93575 : Reach 93575 := rs (se 1 (by rfl) ⟨70181, by rfl⟩) R140363
theorem R159367 : Reach 159367 := rs (se 1 (by rfl) ⟨119525, by rfl⟩) R239051
theorem R126611 : Reach 126611 := rs (se 1 (by rfl) ⟨94958, by rfl⟩) R189917
theorem R126665 : Reach 126665 := rs (se 2 (by rfl) ⟨47499, by rfl⟩) R94999
theorem R290575 : Reach 290575 := rs (se 1 (by rfl) ⟨217931, by rfl⟩) R435863
theorem R159641 : Reach 159641 := rs (se 2 (by rfl) ⟨59865, by rfl⟩) R119731
theorem R94223 : Reach 94223 := rs (se 1 (by rfl) ⟨70667, by rfl⟩) R141335
theorem R127367 : Reach 127367 := rs (se 1 (by rfl) ⟨95525, by rfl⟩) R191051
theorem R291275 : Reach 291275 := rs (se 1 (by rfl) ⟨218456, by rfl⟩) R436913
theorem R651725 : Reach 651725 := rs (se 3 (by rfl) ⟨122198, by rfl⟩) R244397
theorem R160289 : Reach 160289 := rs (se 2 (by rfl) ⟨60108, by rfl⟩) R120217
theorem R94763 : Reach 94763 := rs (se 1 (by rfl) ⟨71072, by rfl⟩) R142145
theorem R127547 : Reach 127547 := rs (se 1 (by rfl) ⟨95660, by rfl⟩) R191321
theorem R62095 : Reach 62095 := rs (se 1 (by rfl) ⟨46571, by rfl⟩) R93143
theorem R324269 : Reach 324269 := rs (se 3 (by rfl) ⟨60800, by rfl⟩) R121601
theorem R127673 : Reach 127673 := rs (se 2 (by rfl) ⟨47877, by rfl⟩) R95755
theorem R291599 : Reach 291599 := rs (se 1 (by rfl) ⟨218699, by rfl⟩) R437399
theorem R193427 : Reach 193427 := rs (se 1 (by rfl) ⟨145070, by rfl⟩) R290141
theorem R422819 : Reach 422819 := rs (se 1 (by rfl) ⟨317114, by rfl⟩) R634229
theorem R95161 : Reach 95161 := rs (se 2 (by rfl) ⟨35685, by rfl⟩) R71371
theorem R128015 : Reach 128015 := rs (se 1 (by rfl) ⟨96011, by rfl⟩) R192023
theorem R390167 : Reach 390167 := rs (se 1 (by rfl) ⟨292625, by rfl⟩) R585251
theorem R128033 : Reach 128033 := rs (se 2 (by rfl) ⟨48012, by rfl⟩) R96025
theorem R160829 : Reach 160829 := rs (se 3 (by rfl) ⟨30155, by rfl⟩) R60311
theorem R62599 : Reach 62599 := rs (se 1 (by rfl) ⟨46949, by rfl⟩) R93899
theorem R62779 : Reach 62779 := rs (se 1 (by rfl) ⟨47084, by rfl⟩) R94169
theorem R128375 : Reach 128375 := rs (se 1 (by rfl) ⟨96281, by rfl⟩) R192563
theorem R161291 : Reach 161291 := rs (se 1 (by rfl) ⟨120968, by rfl⟩) R241937
theorem R128555 : Reach 128555 := rs (se 1 (by rfl) ⟨96416, by rfl⟩) R192833
theorem R95863 : Reach 95863 := rs (se 1 (by rfl) ⟨71897, by rfl⟩) R143795
theorem R358145 : Reach 358145 := rs (se 2 (by rfl) ⟨134304, by rfl⟩) R268609
theorem R63247 : Reach 63247 := rs (se 1 (by rfl) ⟨47435, by rfl⟩) R94871
theorem R96059 : Reach 96059 := rs (se 1 (by rfl) ⟨72044, by rfl⟩) R144089
theorem R128915 : Reach 128915 := rs (se 1 (by rfl) ⟨96686, by rfl⟩) R193373
theorem R128969 : Reach 128969 := rs (se 2 (by rfl) ⟨48363, by rfl⟩) R96727
theorem R63623 : Reach 63623 := rs (se 1 (by rfl) ⟨47717, by rfl⟩) R95435
theorem R293057 : Reach 293057 := rs (se 2 (by rfl) ⟨109896, by rfl⟩) R219793
theorem R96457 : Reach 96457 := rs (se 2 (by rfl) ⟨36171, by rfl⟩) R72343
theorem R63751 : Reach 63751 := rs (se 1 (by rfl) ⟨47813, by rfl⟩) R95627
theorem R194831 : Reach 194831 := rs (se 1 (by rfl) ⟨146123, by rfl⟩) R292247
theorem R63931 : Reach 63931 := rs (se 1 (by rfl) ⟨47948, by rfl⟩) R95897
theorem R195101 : Reach 195101 := rs (se 3 (by rfl) ⟨36581, by rfl⟩) R73163
theorem R129671 : Reach 129671 := rs (se 1 (by rfl) ⟨97253, by rfl⟩) R194507
theorem R129683 : Reach 129683 := rs (se 1 (by rfl) ⟨97262, by rfl⟩) R194525
theorem R129851 : Reach 129851 := rs (se 1 (by rfl) ⟨97388, by rfl⟩) R194777
theorem R97159 : Reach 97159 := rs (se 1 (by rfl) ⟨72869, by rfl⟩) R145739
theorem R64399 : Reach 64399 := rs (se 1 (by rfl) ⟨48299, by rfl⟩) R96599
theorem R293777 : Reach 293777 := rs (se 2 (by rfl) ⟨110166, by rfl⟩) R220333
theorem R129977 : Reach 129977 := rs (se 2 (by rfl) ⟨48741, by rfl⟩) R97483
theorem R130195 : Reach 130195 := rs (se 1 (by rfl) ⟨97646, by rfl⟩) R195293
theorem R97481 : Reach 97481 := rs (se 2 (by rfl) ⟨36555, by rfl⟩) R73111
theorem R130319 : Reach 130319 := rs (se 1 (by rfl) ⟨97739, by rfl⟩) R195479
theorem R425249 : Reach 425249 := rs (se 2 (by rfl) ⟨159468, by rfl⟩) R318937
theorem R130337 : Reach 130337 := rs (se 2 (by rfl) ⟨48876, by rfl⟩) R97753
theorem R64903 : Reach 64903 := rs (se 1 (by rfl) ⟨48677, by rfl⟩) R97355
theorem R130439 : Reach 130439 := rs (se 1 (by rfl) ⟨97829, by rfl⟩) R195659
theorem R294353 : Reach 294353 := rs (se 2 (by rfl) ⟨110382, by rfl⟩) R220765
theorem R97807 : Reach 97807 := rs (se 1 (by rfl) ⟨73355, by rfl⟩) R146711
theorem R163387 : Reach 163387 := rs (se 1 (by rfl) ⟨122540, by rfl⟩) R245081
theorem R65083 : Reach 65083 := rs (se 1 (by rfl) ⟨48812, by rfl⟩) R97625
theorem R2719331 : Reach 2719331 := rs (se 1 (by rfl) ⟨2039498, by rfl⟩) R4078997
theorem R130679 : Reach 130679 := rs (se 1 (by rfl) ⟨98009, by rfl⟩) R196019
theorem R130859 : Reach 130859 := rs (se 1 (by rfl) ⟨98144, by rfl⟩) R196289
theorem R130931 : Reach 130931 := rs (se 1 (by rfl) ⟨98198, by rfl⟩) R196397
theorem R196505 : Reach 196505 := rs (se 2 (by rfl) ⟨73689, by rfl⟩) R147379
theorem R65575 : Reach 65575 := rs (se 1 (by rfl) ⟨49181, by rfl⟩) R98363
theorem R131129 : Reach 131129 := rs (se 2 (by rfl) ⟨49173, by rfl⟩) R98347
theorem R295001 : Reach 295001 := rs (se 2 (by rfl) ⟨110625, by rfl⟩) R221251
theorem R98401 : Reach 98401 := rs (se 2 (by rfl) ⟨36900, by rfl⟩) R73801
theorem R65659 : Reach 65659 := rs (se 1 (by rfl) ⟨49244, by rfl⟩) R98489
theorem R131471 : Reach 131471 := rs (se 1 (by rfl) ⟨98603, by rfl⟩) R197207
theorem R98779 : Reach 98779 := rs (se 1 (by rfl) ⟨74084, by rfl⟩) R148169
theorem R197153 : Reach 197153 := rs (se 2 (by rfl) ⟨73932, by rfl⟩) R147865
theorem R66127 : Reach 66127 := rs (se 1 (by rfl) ⟨49595, by rfl⟩) R99191
theorem R131723 : Reach 131723 := rs (se 1 (by rfl) ⟨98792, by rfl⟩) R197585
theorem R426707 : Reach 426707 := rs (se 1 (by rfl) ⟨320030, by rfl⟩) R640061
theorem R131795 : Reach 131795 := rs (se 1 (by rfl) ⟨98846, by rfl⟩) R197693
theorem R197369 : Reach 197369 := rs (se 2 (by rfl) ⟨74013, by rfl⟩) R148027
theorem R99233 : Reach 99233 := rs (se 2 (by rfl) ⟨37212, by rfl⟩) R74425
theorem R66487 : Reach 66487 := rs (se 1 (by rfl) ⟨49865, by rfl⟩) R99731
theorem R197639 : Reach 197639 := rs (se 1 (by rfl) ⟨148229, by rfl⟩) R296459
theorem R361523 : Reach 361523 := rs (se 1 (by rfl) ⟨271142, by rfl⟩) R542285
theorem R590915 : Reach 590915 := rs (se 1 (by rfl) ⟨443186, by rfl⟩) R886373
theorem R197711 : Reach 197711 := rs (se 1 (by rfl) ⟨148283, by rfl⟩) R296567
theorem R99407 : Reach 99407 := rs (se 1 (by rfl) ⟨74555, by rfl⟩) R149111
theorem R197747 : Reach 197747 := rs (se 1 (by rfl) ⟨148310, by rfl⟩) R296621
theorem R361675 : Reach 361675 := rs (se 1 (by rfl) ⟨271256, by rfl⟩) R542513
theorem R198017 : Reach 198017 := rs (se 2 (by rfl) ⟨74256, by rfl⟩) R148513
theorem R492965 : Reach 492965 := rs (se 4 (by rfl) ⟨46215, by rfl⟩) R92431
theorem R198125 : Reach 198125 := rs (se 3 (by rfl) ⟨37148, by rfl⟩) R74297
theorem R165415 : Reach 165415 := rs (se 1 (by rfl) ⟨124061, by rfl⟩) R248123
theorem R165473 : Reach 165473 := rs (se 2 (by rfl) ⟨62052, by rfl⟩) R124105
theorem R132731 : Reach 132731 := rs (se 1 (by rfl) ⟨99548, by rfl⟩) R199097
theorem R132857 : Reach 132857 := rs (se 2 (by rfl) ⟨49821, by rfl⟩) R99643
theorem R198587 : Reach 198587 := rs (se 1 (by rfl) ⟨148940, by rfl⟩) R297881
theorem R854023 : Reach 854023 := rs (se 1 (by rfl) ⟨640517, by rfl⟩) R1281035
theorem R395279 : Reach 395279 := rs (se 1 (by rfl) ⟨296459, by rfl⟩) R592919
theorem R198827 : Reach 198827 := rs (se 1 (by rfl) ⟨149120, by rfl⟩) R298241
theorem R657665 : Reach 657665 := rs (se 2 (by rfl) ⟨246624, by rfl⟩) R493249
theorem R199367 : Reach 199367 := rs (se 1 (by rfl) ⟨149525, by rfl⟩) R299051
theorem R363521 : Reach 363521 := rs (se 2 (by rfl) ⟨136320, by rfl⟩) R272641
theorem R166931 : Reach 166931 := rs (se 1 (by rfl) ⟨125198, by rfl⟩) R250397
theorem R430109 : Reach 430109 := rs (se 3 (by rfl) ⟨80645, by rfl⟩) R161291
theorem R299501 : Reach 299501 := rs (se 3 (by rfl) ⟨56156, by rfl⟩) R112313
theorem R102991 : Reach 102991 := rs (se 1 (by rfl) ⟨77243, by rfl⟩) R154487
theorem R103343 : Reach 103343 := rs (se 1 (by rfl) ⟨77507, by rfl⟩) R155015
theorem R496691 : Reach 496691 := rs (se 1 (by rfl) ⟨372518, by rfl⟩) R745037
theorem R136667 : Reach 136667 := rs (se 1 (by rfl) ⟨102500, by rfl⟩) R205001
theorem R300667 : Reach 300667 := rs (se 1 (by rfl) ⟨225500, by rfl⟩) R451001
theorem R169661 : Reach 169661 := rs (se 3 (by rfl) ⟨31811, by rfl⟩) R63623
theorem R71599 : Reach 71599 := rs (se 1 (by rfl) ⟨53699, by rfl⟩) R107399
theorem R104809 : Reach 104809 := rs (se 2 (by rfl) ⟨39303, by rfl⟩) R78607
theorem R104969 : Reach 104969 := rs (se 2 (by rfl) ⟨39363, by rfl⟩) R78727
theorem R891425 : Reach 891425 := rs (se 2 (by rfl) ⟨334284, by rfl⟩) R668569
theorem R236317 : Reach 236317 := rs (se 3 (by rfl) ⟨44309, by rfl⟩) R88619
theorem R72667 : Reach 72667 := rs (se 1 (by rfl) ⟨54500, by rfl⟩) R109001
theorem R400403 : Reach 400403 := rs (se 1 (by rfl) ⟨300302, by rfl⟩) R600605
theorem R400427 : Reach 400427 := rs (se 1 (by rfl) ⟨300320, by rfl⟩) R600641
theorem R597071 : Reach 597071 := rs (se 1 (by rfl) ⟨447803, by rfl⟩) R895607
theorem R335483 : Reach 335483 := rs (se 1 (by rfl) ⟨251612, by rfl⟩) R503225
theorem R106427 : Reach 106427 := rs (se 1 (by rfl) ⟨79820, by rfl⟩) R159641
theorem R434483 : Reach 434483 := rs (se 1 (by rfl) ⟨325862, by rfl⟩) R651725
theorem R106859 : Reach 106859 := rs (se 1 (by rfl) ⟨80144, by rfl⟩) R160289
theorem R106913 : Reach 106913 := rs (se 2 (by rfl) ⟨40092, by rfl⟩) R80185
theorem R139801 : Reach 139801 := rs (se 2 (by rfl) ⟨52425, by rfl⟩) R104851
theorem R107219 : Reach 107219 := rs (se 1 (by rfl) ⟨80414, by rfl⟩) R160829
theorem R205751 : Reach 205751 := rs (se 1 (by rfl) ⟨154313, by rfl⟩) R308627
theorem R861131 : Reach 861131 := rs (se 1 (by rfl) ⟨645848, by rfl⟩) R1291697
theorem R238763 : Reach 238763 := rs (se 1 (by rfl) ⟨179072, by rfl⟩) R358145
theorem R664847 : Reach 664847 := rs (se 1 (by rfl) ⟨498635, by rfl⟩) R997271
theorem R140687 : Reach 140687 := rs (se 1 (by rfl) ⟨105515, by rfl⟩) R211031
theorem R173593 : Reach 173593 := rs (se 2 (by rfl) ⟨65097, by rfl⟩) R130195
theorem R141011 : Reach 141011 := rs (se 1 (by rfl) ⟨105758, by rfl⟩) R211517
theorem R501713 : Reach 501713 := rs (se 2 (by rfl) ⟨188142, by rfl⟩) R376285
theorem R108553 : Reach 108553 := rs (se 2 (by rfl) ⟨40707, by rfl⟩) R81415
theorem R1812887 : Reach 1812887 := rs (se 1 (by rfl) ⟨1359665, by rfl⟩) R2719331
theorem R142175 : Reach 142175 := rs (se 1 (by rfl) ⟨106631, by rfl⟩) R213263
theorem R1551251 : Reach 1551251 := rs (se 1 (by rfl) ⟨1163438, by rfl⟩) R2326877
theorem R109487 : Reach 109487 := rs (se 1 (by rfl) ⟨82115, by rfl⟩) R164231
theorem R2698211 : Reach 2698211 := rs (se 1 (by rfl) ⟨2023658, by rfl⟩) R4047317
theorem R535747 : Reach 535747 := rs (se 1 (by rfl) ⟨401810, by rfl⟩) R803621
theorem R110011 : Reach 110011 := rs (se 1 (by rfl) ⟨82508, by rfl⟩) R165017
theorem R372235 : Reach 372235 := rs (se 1 (by rfl) ⟨279176, by rfl⟩) R558353
theorem R3124813 : Reach 3124813 := rs (se 3 (by rfl) ⟨585902, by rfl⟩) R1171805
theorem R798497 : Reach 798497 := rs (se 2 (by rfl) ⟨299436, by rfl⟩) R598873
theorem R110497 : Reach 110497 := rs (se 2 (by rfl) ⟨41436, by rfl⟩) R82873
theorem R143279 : Reach 143279 := rs (se 1 (by rfl) ⟨107459, by rfl⟩) R214919
theorem R667763 : Reach 667763 := rs (se 1 (by rfl) ⟨500822, by rfl⟩) R1001645
theorem R176737 : Reach 176737 := rs (se 2 (by rfl) ⟨66276, by rfl⟩) R132553
theorem R537299 : Reach 537299 := rs (se 1 (by rfl) ⟨402974, by rfl⟩) R805949
theorem R242689 : Reach 242689 := rs (se 2 (by rfl) ⟨91008, by rfl⟩) R182017
theorem R144463 : Reach 144463 := rs (se 1 (by rfl) ⟨108347, by rfl⟩) R216695
theorem R210073 : Reach 210073 := rs (se 2 (by rfl) ⟨78777, by rfl⟩) R157555
theorem R603407 : Reach 603407 := rs (se 1 (by rfl) ⟨452555, by rfl⟩) R905111
theorem R374159 : Reach 374159 := rs (se 1 (by rfl) ⟨280619, by rfl⟩) R561239
theorem R210377 : Reach 210377 := rs (se 2 (by rfl) ⟨78891, by rfl⟩) R157783
theorem R276007 : Reach 276007 := rs (se 1 (by rfl) ⟨207005, by rfl⟩) R414011
theorem R145111 : Reach 145111 := rs (se 1 (by rfl) ⟨108833, by rfl⟩) R217667
theorem R210863 : Reach 210863 := rs (se 1 (by rfl) ⟨158147, by rfl⟩) R316295
theorem R145415 : Reach 145415 := rs (se 1 (by rfl) ⟨109061, by rfl⟩) R218123
theorem R1850201 : Reach 1850201 := rs (se 2 (by rfl) ⟨693825, by rfl⟩) R1387651
theorem R342967 : Reach 342967 := rs (se 1 (by rfl) ⟨257225, by rfl⟩) R514451
theorem R1260791 : Reach 1260791 := rs (se 1 (by rfl) ⟨945593, by rfl⟩) R1891187
theorem R408995 : Reach 408995 := rs (se 1 (by rfl) ⟨306746, by rfl⟩) R613493
theorem R441773 : Reach 441773 := rs (se 3 (by rfl) ⟨82832, by rfl⟩) R165665
theorem R212489 : Reach 212489 := rs (se 2 (by rfl) ⟨79683, by rfl⟩) R159367
theorem R638603 : Reach 638603 := rs (se 1 (by rfl) ⟨478952, by rfl⟩) R957905
theorem R376643 : Reach 376643 := rs (se 1 (by rfl) ⟨282482, by rfl⟩) R564965
theorem R180377 : Reach 180377 := rs (se 2 (by rfl) ⟨67641, by rfl⟩) R135283
theorem R606437 : Reach 606437 := rs (se 4 (by rfl) ⟨56853, by rfl⟩) R113707
theorem R147703 : Reach 147703 := rs (se 1 (by rfl) ⟨110777, by rfl⟩) R221555
theorem R147977 : Reach 147977 := rs (se 2 (by rfl) ⟨55491, by rfl⟩) R110983
theorem R148007 : Reach 148007 := rs (se 1 (by rfl) ⟨111005, by rfl⟩) R222011
theorem R737909 : Reach 737909 := rs (se 5 (by rfl) ⟨34589, by rfl⟩) R69179
theorem R82793 : Reach 82793 := rs (se 2 (by rfl) ⟨31047, by rfl⟩) R62095
theorem R148331 : Reach 148331 := rs (se 1 (by rfl) ⟨111248, by rfl⟩) R222497
theorem R82871 : Reach 82871 := rs (se 1 (by rfl) ⟨62153, by rfl⟩) R124307
theorem R213947 : Reach 213947 := rs (se 1 (by rfl) ⟨160460, by rfl⟩) R320921
theorem R82907 : Reach 82907 := rs (se 1 (by rfl) ⟨62180, by rfl⟩) R124361
theorem R83375 : Reach 83375 := rs (se 1 (by rfl) ⟨62531, by rfl⟩) R125063
theorem R148979 : Reach 148979 := rs (se 1 (by rfl) ⟨111734, by rfl⟩) R223469
theorem R83465 : Reach 83465 := rs (se 2 (by rfl) ⟨31299, by rfl⟩) R62599
theorem R83495 : Reach 83495 := rs (se 1 (by rfl) ⟨62621, by rfl⟩) R125243
theorem R83579 : Reach 83579 := rs (se 1 (by rfl) ⟨62684, by rfl⟩) R125369
theorem R214667 : Reach 214667 := rs (se 1 (by rfl) ⟨161000, by rfl⟩) R322001
theorem R83705 : Reach 83705 := rs (se 2 (by rfl) ⟨31389, by rfl⟩) R62779
theorem R444203 : Reach 444203 := rs (se 1 (by rfl) ⟨333152, by rfl⟩) R666305
theorem R83807 : Reach 83807 := rs (se 1 (by rfl) ⟨62855, by rfl⟩) R125711
theorem R83819 : Reach 83819 := rs (se 1 (by rfl) ⟨62864, by rfl⟩) R125729
theorem R149435 : Reach 149435 := rs (se 1 (by rfl) ⟨112076, by rfl⟩) R224153
theorem R280583 : Reach 280583 := rs (se 1 (by rfl) ⟨210437, by rfl⟩) R420875
theorem R247823 : Reach 247823 := rs (se 1 (by rfl) ⟨185867, by rfl⟩) R371735
theorem R84047 : Reach 84047 := rs (se 1 (by rfl) ⟨63035, by rfl⟩) R126071
theorem R542821 : Reach 542821 := rs (se 4 (by rfl) ⟨50889, by rfl⟩) R101779
theorem R84167 : Reach 84167 := rs (se 1 (by rfl) ⟨63125, by rfl⟩) R126251
theorem R84329 : Reach 84329 := rs (se 2 (by rfl) ⟨31623, by rfl⟩) R63247
theorem R84407 : Reach 84407 := rs (se 1 (by rfl) ⟨63305, by rfl⟩) R126611
theorem R84443 : Reach 84443 := rs (se 1 (by rfl) ⟨63332, by rfl⟩) R126665
theorem R281069 : Reach 281069 := rs (se 3 (by rfl) ⟨52700, by rfl⟩) R105401
theorem R84911 : Reach 84911 := rs (se 1 (by rfl) ⟨63683, by rfl⟩) R127367
theorem R85001 : Reach 85001 := rs (se 2 (by rfl) ⟨31875, by rfl⟩) R63751
theorem R85031 : Reach 85031 := rs (se 1 (by rfl) ⟨63773, by rfl⟩) R127547
theorem R216179 : Reach 216179 := rs (se 1 (by rfl) ⟨162134, by rfl⟩) R324269
theorem R85115 : Reach 85115 := rs (se 1 (by rfl) ⟨63836, by rfl⟩) R127673
theorem R314563 : Reach 314563 := rs (se 1 (by rfl) ⟨235922, by rfl⟩) R471845
theorem R85241 : Reach 85241 := rs (se 2 (by rfl) ⟨31965, by rfl⟩) R63931
theorem R281879 : Reach 281879 := rs (se 1 (by rfl) ⟨211409, by rfl⟩) R422819
theorem R85343 : Reach 85343 := rs (se 1 (by rfl) ⟨64007, by rfl⟩) R128015
theorem R85355 : Reach 85355 := rs (se 1 (by rfl) ⟨64016, by rfl⟩) R128033
theorem R970157 : Reach 970157 := rs (se 3 (by rfl) ⟨181904, by rfl⟩) R363809
theorem R118235 : Reach 118235 := rs (se 1 (by rfl) ⟨88676, by rfl⟩) R177353
theorem R85583 : Reach 85583 := rs (se 1 (by rfl) ⟨64187, by rfl⟩) R128375
theorem R85703 : Reach 85703 := rs (se 1 (by rfl) ⟨64277, by rfl⟩) R128555
theorem R85865 : Reach 85865 := rs (se 2 (by rfl) ⟨32199, by rfl⟩) R64399
theorem R413549 : Reach 413549 := rs (se 3 (by rfl) ⟨77540, by rfl⟩) R155081
theorem R85943 : Reach 85943 := rs (se 1 (by rfl) ⟨64457, by rfl⟩) R128915
theorem R85979 : Reach 85979 := rs (se 1 (by rfl) ⟨64484, by rfl⟩) R128969
theorem R4837637 : Reach 4837637 := rs (se 4 (by rfl) ⟨453528, by rfl⟩) R907057
theorem R86447 : Reach 86447 := rs (se 1 (by rfl) ⟨64835, by rfl⟩) R129671
theorem R86455 : Reach 86455 := rs (se 1 (by rfl) ⟨64841, by rfl⟩) R129683
theorem R86537 : Reach 86537 := rs (se 2 (by rfl) ⟨32451, by rfl⟩) R64903
theorem R86567 : Reach 86567 := rs (se 1 (by rfl) ⟨64925, by rfl⟩) R129851
theorem R86651 : Reach 86651 := rs (se 1 (by rfl) ⟨64988, by rfl⟩) R129977
theorem R971473 : Reach 971473 := rs (se 2 (by rfl) ⟨364302, by rfl⟩) R728605
theorem R217849 : Reach 217849 := rs (se 2 (by rfl) ⟨81693, by rfl⟩) R163387
theorem R86777 : Reach 86777 := rs (se 2 (by rfl) ⟨32541, by rfl⟩) R65083
theorem R86879 : Reach 86879 := rs (se 1 (by rfl) ⟨65159, by rfl⟩) R130319
theorem R283499 : Reach 283499 := rs (se 1 (by rfl) ⟨212624, by rfl⟩) R425249
theorem R86891 : Reach 86891 := rs (se 1 (by rfl) ⟨65168, by rfl⟩) R130337
theorem R86959 : Reach 86959 := rs (se 1 (by rfl) ⟨65219, by rfl⟩) R130439
theorem R87119 : Reach 87119 := rs (se 1 (by rfl) ⟨65339, by rfl⟩) R130679
theorem R87239 : Reach 87239 := rs (se 1 (by rfl) ⟨65429, by rfl⟩) R130859
theorem R87287 : Reach 87287 := rs (se 1 (by rfl) ⟨65465, by rfl⟩) R130931
theorem R87401 : Reach 87401 := rs (se 2 (by rfl) ⟨32775, by rfl⟩) R65551
theorem R87479 : Reach 87479 := rs (se 1 (by rfl) ⟨65609, by rfl⟩) R131219
theorem R873929 : Reach 873929 := rs (se 2 (by rfl) ⟨327723, by rfl⟩) R655447
theorem R87515 : Reach 87515 := rs (se 1 (by rfl) ⟨65636, by rfl⟩) R131273
theorem R26891747 : Reach 26891747 := rs (se 1 (by rfl) ⟨20168810, by rfl⟩) R40337621
theorem R284147 : Reach 284147 := rs (se 1 (by rfl) ⟨213110, by rfl⟩) R426221
theorem R87881 : Reach 87881 := rs (se 2 (by rfl) ⟨32955, by rfl⟩) R65911
theorem R55135 : Reach 55135 := rs (se 1 (by rfl) ⟨41351, by rfl⟩) R82703
theorem R55163 : Reach 55163 := rs (se 1 (by rfl) ⟨41372, by rfl⟩) R82745
theorem R55215 : Reach 55215 := rs (se 1 (by rfl) ⟨41411, by rfl⟩) R82823
theorem R87983 : Reach 87983 := rs (se 1 (by rfl) ⟨65987, by rfl⟩) R131975
theorem R186299 : Reach 186299 := rs (se 1 (by rfl) ⟨139724, by rfl⟩) R279449
theorem R87995 : Reach 87995 := rs (se 1 (by rfl) ⟨65996, by rfl⟩) R131993
theorem R55239 : Reach 55239 := rs (se 1 (by rfl) ⟨41429, by rfl⟩) R82859
theorem R55259 : Reach 55259 := rs (se 1 (by rfl) ⟨41444, by rfl⟩) R82889
theorem R88073 : Reach 88073 := rs (se 2 (by rfl) ⟨33027, by rfl⟩) R66055
theorem R55335 : Reach 55335 := rs (se 1 (by rfl) ⟨41501, by rfl⟩) R83003
theorem R88103 : Reach 88103 := rs (se 1 (by rfl) ⟨66077, by rfl⟩) R132155
theorem R88121 : Reach 88121 := rs (se 2 (by rfl) ⟨33045, by rfl⟩) R66091
theorem R55375 : Reach 55375 := rs (se 1 (by rfl) ⟨41531, by rfl⟩) R83063
theorem R350297 : Reach 350297 := rs (se 2 (by rfl) ⟨131361, by rfl⟩) R262723
theorem R55391 : Reach 55391 := rs (se 1 (by rfl) ⟨41543, by rfl⟩) R83087
theorem R55419 : Reach 55419 := rs (se 1 (by rfl) ⟨41564, by rfl⟩) R83129
theorem R88187 : Reach 88187 := rs (se 1 (by rfl) ⟨66140, by rfl⟩) R132281
theorem R219293 : Reach 219293 := rs (se 3 (by rfl) ⟨41117, by rfl⟩) R82235
theorem R350365 : Reach 350365 := rs (se 3 (by rfl) ⟨65693, by rfl⟩) R131387
theorem R219307 : Reach 219307 := rs (se 1 (by rfl) ⟨164480, by rfl⟩) R328961
theorem R88235 : Reach 88235 := rs (se 1 (by rfl) ⟨66176, by rfl⟩) R132353
theorem R55471 : Reach 55471 := rs (se 1 (by rfl) ⟨41603, by rfl⟩) R83207
theorem R55495 : Reach 55495 := rs (se 1 (by rfl) ⟨41621, by rfl⟩) R83243
theorem R55515 : Reach 55515 := rs (se 1 (by rfl) ⟨41636, by rfl⟩) R83273
theorem R88313 : Reach 88313 := rs (se 2 (by rfl) ⟨33117, by rfl⟩) R66235
theorem R55591 : Reach 55591 := rs (se 1 (by rfl) ⟨41693, by rfl⟩) R83387
theorem R55631 : Reach 55631 := rs (se 1 (by rfl) ⟨41723, by rfl⟩) R83447
theorem R1399133 : Reach 1399133 := rs (se 3 (by rfl) ⟨262337, by rfl⟩) R524675
theorem R55647 : Reach 55647 := rs (se 1 (by rfl) ⟨41735, by rfl⟩) R83471
theorem R88415 : Reach 88415 := rs (se 1 (by rfl) ⟨66311, by rfl⟩) R132623
theorem R88427 : Reach 88427 := rs (se 1 (by rfl) ⟨66320, by rfl⟩) R132641
theorem R55675 : Reach 55675 := rs (se 1 (by rfl) ⟨41756, by rfl⟩) R83513
theorem R88463 : Reach 88463 := rs (se 1 (by rfl) ⟨66347, by rfl⟩) R132695
theorem R55727 : Reach 55727 := rs (se 1 (by rfl) ⟨41795, by rfl⟩) R83591
theorem R55751 : Reach 55751 := rs (se 1 (by rfl) ⟨41813, by rfl⟩) R83627
theorem R55771 : Reach 55771 := rs (se 1 (by rfl) ⟨41828, by rfl⟩) R83657
theorem R219611 : Reach 219611 := rs (se 1 (by rfl) ⟨164708, by rfl⟩) R329417
theorem R809453 : Reach 809453 := rs (se 3 (by rfl) ⟨151772, by rfl⟩) R303545
theorem R88583 : Reach 88583 := rs (se 1 (by rfl) ⟨66437, by rfl⟩) R132875
theorem R55847 : Reach 55847 := rs (se 1 (by rfl) ⟨41885, by rfl⟩) R83771
theorem R55887 : Reach 55887 := rs (se 1 (by rfl) ⟨41915, by rfl⟩) R83831
theorem R88655 : Reach 88655 := rs (se 1 (by rfl) ⟨66491, by rfl⟩) R132983
theorem R55903 : Reach 55903 := rs (se 1 (by rfl) ⟨41927, by rfl⟩) R83855
theorem R55931 : Reach 55931 := rs (se 1 (by rfl) ⟨41948, by rfl⟩) R83897
theorem R88699 : Reach 88699 := rs (se 1 (by rfl) ⟨66524, by rfl⟩) R133049
theorem R55983 : Reach 55983 := rs (se 1 (by rfl) ⟨41987, by rfl⟩) R83975
theorem R56007 : Reach 56007 := rs (se 1 (by rfl) ⟨42005, by rfl⟩) R84011
theorem R56027 : Reach 56027 := rs (se 1 (by rfl) ⟨42020, by rfl⟩) R84041
theorem R285443 : Reach 285443 := rs (se 1 (by rfl) ⟨214082, by rfl⟩) R428165
theorem R56103 : Reach 56103 := rs (se 1 (by rfl) ⟨42077, by rfl⟩) R84155
theorem R56143 : Reach 56143 := rs (se 1 (by rfl) ⟨42107, by rfl⟩) R84215
theorem R56159 : Reach 56159 := rs (se 1 (by rfl) ⟨42119, by rfl⟩) R84239
theorem R56187 : Reach 56187 := rs (se 1 (by rfl) ⟨42140, by rfl⟩) R84281
theorem R56239 : Reach 56239 := rs (se 1 (by rfl) ⟨42179, by rfl⟩) R84359
theorem R56263 : Reach 56263 := rs (se 1 (by rfl) ⟨42197, by rfl⟩) R84395
theorem R56283 : Reach 56283 := rs (se 1 (by rfl) ⟨42212, by rfl⟩) R84425
theorem R318437 : Reach 318437 := rs (se 4 (by rfl) ⟨29853, by rfl⟩) R59707
theorem R56359 : Reach 56359 := rs (se 1 (by rfl) ⟨42269, by rfl⟩) R84539
theorem R56399 : Reach 56399 := rs (se 1 (by rfl) ⟨42299, by rfl⟩) R84599
theorem R56415 : Reach 56415 := rs (se 1 (by rfl) ⟨42311, by rfl⟩) R84623
theorem R56443 : Reach 56443 := rs (se 1 (by rfl) ⟨42332, by rfl⟩) R84665
theorem R56495 : Reach 56495 := rs (se 1 (by rfl) ⟨42371, by rfl⟩) R84743
theorem R56519 : Reach 56519 := rs (se 1 (by rfl) ⟨42389, by rfl⟩) R84779
theorem R56539 : Reach 56539 := rs (se 1 (by rfl) ⟨42404, by rfl⟩) R84809
theorem R56615 : Reach 56615 := rs (se 1 (by rfl) ⟨42461, by rfl⟩) R84923
theorem R56655 : Reach 56655 := rs (se 1 (by rfl) ⟨42491, by rfl⟩) R84983
theorem R56671 : Reach 56671 := rs (se 1 (by rfl) ⟨42503, by rfl⟩) R85007
theorem R56699 : Reach 56699 := rs (se 1 (by rfl) ⟨42524, by rfl⟩) R85049
theorem R56751 : Reach 56751 := rs (se 1 (by rfl) ⟨42563, by rfl⟩) R85127
theorem R56775 : Reach 56775 := rs (se 1 (by rfl) ⟨42581, by rfl⟩) R85163
theorem R56795 : Reach 56795 := rs (se 1 (by rfl) ⟨42596, by rfl⟩) R85193
theorem R56871 : Reach 56871 := rs (se 1 (by rfl) ⟨42653, by rfl⟩) R85307
theorem R56911 : Reach 56911 := rs (se 1 (by rfl) ⟨42683, by rfl⟩) R85367
theorem R56927 : Reach 56927 := rs (se 1 (by rfl) ⟨42695, by rfl⟩) R85391
theorem R122465 : Reach 122465 := rs (se 2 (by rfl) ⟨45924, by rfl⟩) R91849
theorem R188027 : Reach 188027 := rs (se 1 (by rfl) ⟨141020, by rfl⟩) R282041
theorem R56955 : Reach 56955 := rs (se 1 (by rfl) ⟨42716, by rfl⟩) R85433
theorem R57007 : Reach 57007 := rs (se 1 (by rfl) ⟨42755, by rfl⟩) R85511
theorem R57031 : Reach 57031 := rs (se 1 (by rfl) ⟨42773, by rfl⟩) R85547
theorem R155351 : Reach 155351 := rs (se 1 (by rfl) ⟨116513, by rfl⟩) R233027
theorem R57051 : Reach 57051 := rs (se 1 (by rfl) ⟨42788, by rfl⟩) R85577
theorem R188189 : Reach 188189 := rs (se 3 (by rfl) ⟨35285, by rfl⟩) R70571
theorem R57127 : Reach 57127 := rs (se 1 (by rfl) ⟨42845, by rfl⟩) R85691
theorem R57167 : Reach 57167 := rs (se 1 (by rfl) ⟨42875, by rfl⟩) R85751
theorem R57183 : Reach 57183 := rs (se 1 (by rfl) ⟨42887, by rfl⟩) R85775
theorem R483191 : Reach 483191 := rs (se 1 (by rfl) ⟨362393, by rfl⟩) R724787
theorem R57211 : Reach 57211 := rs (se 1 (by rfl) ⟨42908, by rfl⟩) R85817
theorem R57263 : Reach 57263 := rs (se 1 (by rfl) ⟨42947, by rfl⟩) R85895
theorem R155567 : Reach 155567 := rs (se 1 (by rfl) ⟨116675, by rfl⟩) R233351
theorem R286651 : Reach 286651 := rs (se 1 (by rfl) ⟨214988, by rfl⟩) R429977
theorem R57287 : Reach 57287 := rs (se 1 (by rfl) ⟨42965, by rfl⟩) R85931
theorem R57307 : Reach 57307 := rs (se 1 (by rfl) ⟨42980, by rfl⟩) R85961
theorem R57383 : Reach 57383 := rs (se 1 (by rfl) ⟨43037, by rfl⟩) R86075
theorem R57423 : Reach 57423 := rs (se 1 (by rfl) ⟨43067, by rfl⟩) R86135
theorem R57439 : Reach 57439 := rs (se 1 (by rfl) ⟨43079, by rfl⟩) R86159
theorem R57467 : Reach 57467 := rs (se 1 (by rfl) ⟨43100, by rfl⟩) R86201
theorem R57519 : Reach 57519 := rs (se 1 (by rfl) ⟨43139, by rfl⟩) R86279
theorem R57543 : Reach 57543 := rs (se 1 (by rfl) ⟨43157, by rfl⟩) R86315
theorem R57563 : Reach 57563 := rs (se 1 (by rfl) ⟨43172, by rfl⟩) R86345
theorem R57639 : Reach 57639 := rs (se 1 (by rfl) ⟨43229, by rfl⟩) R86459
theorem R57679 : Reach 57679 := rs (se 1 (by rfl) ⟨43259, by rfl⟩) R86519
theorem R287063 : Reach 287063 := rs (se 1 (by rfl) ⟨215297, by rfl⟩) R430595
theorem R57695 : Reach 57695 := rs (se 1 (by rfl) ⟨43271, by rfl⟩) R86543
theorem R57723 : Reach 57723 := rs (se 1 (by rfl) ⟨43292, by rfl⟩) R86585
theorem R57775 : Reach 57775 := rs (se 1 (by rfl) ⟨43331, by rfl⟩) R86663
theorem R57799 : Reach 57799 := rs (se 1 (by rfl) ⟨43349, by rfl⟩) R86699
theorem R188891 : Reach 188891 := rs (se 1 (by rfl) ⟨141668, by rfl⟩) R283337
theorem R57819 : Reach 57819 := rs (se 1 (by rfl) ⟨43364, by rfl⟩) R86729
theorem R746009 : Reach 746009 := rs (se 2 (by rfl) ⟨279753, by rfl⟩) R559507
theorem R57895 : Reach 57895 := rs (se 1 (by rfl) ⟨43421, by rfl⟩) R86843
theorem R57935 : Reach 57935 := rs (se 1 (by rfl) ⟨43451, by rfl⟩) R86903
theorem R57951 : Reach 57951 := rs (se 1 (by rfl) ⟨43463, by rfl⟩) R86927
theorem R123515 : Reach 123515 := rs (se 1 (by rfl) ⟨92636, by rfl⟩) R185273
theorem R57979 : Reach 57979 := rs (se 1 (by rfl) ⟨43484, by rfl⟩) R86969
theorem R221831 : Reach 221831 := rs (se 1 (by rfl) ⟨166373, by rfl⟩) R332747
theorem R221843 : Reach 221843 := rs (se 1 (by rfl) ⟨166382, by rfl⟩) R332765
theorem R58031 : Reach 58031 := rs (se 1 (by rfl) ⟨43523, by rfl⟩) R87047
theorem R58055 : Reach 58055 := rs (se 1 (by rfl) ⟨43541, by rfl⟩) R87083
theorem R58207 : Reach 58207 := rs (se 1 (by rfl) ⟨43655, by rfl⟩) R87311
theorem R58287 : Reach 58287 := rs (se 1 (by rfl) ⟨43715, by rfl⟩) R87431
theorem R58331 : Reach 58331 := rs (se 1 (by rfl) ⟨43748, by rfl⟩) R87497
theorem R222209 : Reach 222209 := rs (se 2 (by rfl) ⟨83328, by rfl⟩) R166657
theorem R222223 : Reach 222223 := rs (se 1 (by rfl) ⟨166667, by rfl⟩) R333335
theorem R58407 : Reach 58407 := rs (se 1 (by rfl) ⟨43805, by rfl⟩) R87611
theorem R123961 : Reach 123961 := rs (se 2 (by rfl) ⟨46485, by rfl⟩) R92971
theorem R58447 : Reach 58447 := rs (se 1 (by rfl) ⟨43835, by rfl⟩) R87671
theorem R58491 : Reach 58491 := rs (se 1 (by rfl) ⟨43868, by rfl⟩) R87737
theorem R189593 : Reach 189593 := rs (se 2 (by rfl) ⟨71097, by rfl⟩) R142195
theorem R58567 : Reach 58567 := rs (se 1 (by rfl) ⟨43925, by rfl⟩) R87851
theorem R222551 : Reach 222551 := rs (se 1 (by rfl) ⟨166913, by rfl⟩) R333827
theorem R58719 : Reach 58719 := rs (se 1 (by rfl) ⟨44039, by rfl⟩) R88079
theorem R91535 : Reach 91535 := rs (se 1 (by rfl) ⟨68651, by rfl⟩) R137303
theorem R5432741 : Reach 5432741 := rs (se 4 (by rfl) ⟨509319, by rfl⟩) R1018639
theorem R58799 : Reach 58799 := rs (se 1 (by rfl) ⟨44099, by rfl⟩) R88199
theorem R124379 : Reach 124379 := rs (se 1 (by rfl) ⟨93284, by rfl⟩) R186569
theorem R58843 : Reach 58843 := rs (se 1 (by rfl) ⟨44132, by rfl⟩) R88265
theorem R58919 : Reach 58919 := rs (se 1 (by rfl) ⟨44189, by rfl⟩) R88379
theorem R58959 : Reach 58959 := rs (se 1 (by rfl) ⟨44219, by rfl⟩) R88439
theorem R59003 : Reach 59003 := rs (se 1 (by rfl) ⟨44252, by rfl⟩) R88505
theorem R157373 : Reach 157373 := rs (se 3 (by rfl) ⟨29507, by rfl⟩) R59015
theorem R59079 : Reach 59079 := rs (se 1 (by rfl) ⟨44309, by rfl⟩) R88619
theorem R812843 : Reach 812843 := rs (se 1 (by rfl) ⟨609632, by rfl⟩) R1219265
theorem R157601 : Reach 157601 := rs (se 2 (by rfl) ⟨59100, by rfl⟩) R118201
theorem R124847 : Reach 124847 := rs (se 1 (by rfl) ⟨93635, by rfl⟩) R187271
theorem R223163 : Reach 223163 := rs (se 1 (by rfl) ⟨167372, by rfl⟩) R334745
theorem R125099 : Reach 125099 := rs (se 1 (by rfl) ⟨93824, by rfl⟩) R187649
theorem R157943 : Reach 157943 := rs (se 1 (by rfl) ⟨118457, by rfl⟩) R236915
theorem R223499 : Reach 223499 := rs (se 1 (by rfl) ⟨167624, by rfl⟩) R335249
theorem R321853 : Reach 321853 := rs (se 3 (by rfl) ⟨60347, by rfl⟩) R120695
theorem R190781 : Reach 190781 := rs (se 3 (by rfl) ⟨35771, by rfl⟩) R71543
theorem R452951 : Reach 452951 := rs (se 1 (by rfl) ⟨339713, by rfl⟩) R679427
theorem R158057 : Reach 158057 := rs (se 2 (by rfl) ⟨59271, by rfl⟩) R118543
theorem R387433 : Reach 387433 := rs (se 2 (by rfl) ⟨145287, by rfl⟩) R290575
theorem R125479 : Reach 125479 := rs (se 1 (by rfl) ⟨94109, by rfl⟩) R188219
theorem R125639 : Reach 125639 := rs (se 1 (by rfl) ⟨94229, by rfl⟩) R188459
theorem R125651 : Reach 125651 := rs (se 1 (by rfl) ⟨94238, by rfl⟩) R188477
theorem R223955 : Reach 223955 := rs (se 1 (by rfl) ⟨167966, by rfl⟩) R335933
theorem R93035 : Reach 93035 := rs (se 1 (by rfl) ⟨69776, by rfl⟩) R139553
theorem R191645 : Reach 191645 := rs (se 3 (by rfl) ⟨35933, by rfl⟩) R71867
theorem R93433 : Reach 93433 := rs (se 2 (by rfl) ⟨35037, by rfl⟩) R70075
theorem R191987 : Reach 191987 := rs (se 1 (by rfl) ⟨143990, by rfl⟩) R287981
theorem R93703 : Reach 93703 := rs (se 1 (by rfl) ⟨70277, by rfl⟩) R140555
theorem R159241 : Reach 159241 := rs (se 2 (by rfl) ⟨59715, by rfl⟩) R119431
theorem R126503 : Reach 126503 := rs (se 1 (by rfl) ⟨94877, by rfl⟩) R189755
theorem R192185 : Reach 192185 := rs (se 2 (by rfl) ⟨72069, by rfl⟩) R144139
theorem R290627 : Reach 290627 := rs (se 1 (by rfl) ⟨217970, by rfl⟩) R435941
theorem R159583 : Reach 159583 := rs (se 1 (by rfl) ⟨119687, by rfl⟩) R239375
theorem R126827 : Reach 126827 := rs (se 1 (by rfl) ⟨95120, by rfl⟩) R190241
theorem R126881 : Reach 126881 := rs (se 2 (by rfl) ⟨47580, by rfl⟩) R95161
theorem R94135 : Reach 94135 := rs (se 1 (by rfl) ⟨70601, by rfl⟩) R141203
theorem R61403 : Reach 61403 := rs (se 1 (by rfl) ⟨46052, by rfl⟩) R92105
theorem R94331 : Reach 94331 := rs (se 1 (by rfl) ⟨70748, by rfl⟩) R141497
theorem R127223 : Reach 127223 := rs (se 1 (by rfl) ⟨95417, by rfl⟩) R190835
theorem R192779 : Reach 192779 := rs (se 1 (by rfl) ⟨144584, by rfl⟩) R289169
theorem R455017 : Reach 455017 := rs (se 2 (by rfl) ⟨170631, by rfl⟩) R341263
theorem R225665 : Reach 225665 := rs (se 2 (by rfl) ⟨84624, by rfl⟩) R169249
theorem R225737 : Reach 225737 := rs (se 2 (by rfl) ⟨84651, by rfl⟩) R169303
theorem R94729 : Reach 94729 := rs (se 2 (by rfl) ⟨35523, by rfl⟩) R71047
theorem R717335 : Reach 717335 := rs (se 1 (by rfl) ⟨538001, by rfl⟩) R1076003
theorem R193049 : Reach 193049 := rs (se 2 (by rfl) ⟨72393, by rfl⟩) R144787
theorem R94891 : Reach 94891 := rs (se 1 (by rfl) ⟨71168, by rfl⟩) R142337
theorem R160471 : Reach 160471 := rs (se 1 (by rfl) ⟨120353, by rfl⟩) R240707
theorem R127817 : Reach 127817 := rs (se 2 (by rfl) ⟨47931, by rfl⟩) R95863
theorem R422729 : Reach 422729 := rs (se 2 (by rfl) ⟨158523, by rfl⟩) R317047
theorem R62383 : Reach 62383 := rs (se 1 (by rfl) ⟨46787, by rfl⟩) R93575
theorem R160699 : Reach 160699 := rs (se 1 (by rfl) ⟨120524, by rfl⟩) R241049
theorem R95195 : Reach 95195 := rs (se 1 (by rfl) ⟨71396, by rfl⟩) R142793
theorem R160825 : Reach 160825 := rs (se 2 (by rfl) ⟨60309, by rfl⟩) R120619
theorem R95431 : Reach 95431 := rs (se 1 (by rfl) ⟨71573, by rfl⟩) R143147
theorem R554201 : Reach 554201 := rs (se 2 (by rfl) ⟨207825, by rfl⟩) R415651
theorem R62815 : Reach 62815 := rs (se 1 (by rfl) ⟨47111, by rfl⟩) R94223
theorem R95593 : Reach 95593 := rs (se 2 (by rfl) ⟨35847, by rfl⟩) R71695
theorem R128609 : Reach 128609 := rs (se 2 (by rfl) ⟨48228, by rfl⟩) R96457
theorem R194183 : Reach 194183 := rs (se 1 (by rfl) ⟨145637, by rfl⟩) R291275
theorem R194237 : Reach 194237 := rs (se 3 (by rfl) ⟨36419, by rfl⟩) R72839
theorem R63175 : Reach 63175 := rs (se 1 (by rfl) ⟨47381, by rfl⟩) R94763
theorem R194399 : Reach 194399 := rs (se 1 (by rfl) ⟨145799, by rfl⟩) R291599
theorem R259949 : Reach 259949 := rs (se 3 (by rfl) ⟨48740, by rfl⟩) R97481
theorem R128951 : Reach 128951 := rs (se 1 (by rfl) ⟨96713, by rfl⟩) R193427
theorem R96187 : Reach 96187 := rs (se 1 (by rfl) ⟨72140, by rfl⟩) R144281
theorem R194561 : Reach 194561 := rs (se 2 (by rfl) ⟨72960, by rfl⟩) R145921
theorem R260111 : Reach 260111 := rs (se 1 (by rfl) ⟨195083, by rfl⟩) R390167
theorem R96295 : Reach 96295 := rs (se 1 (by rfl) ⟨72221, by rfl⟩) R144443
theorem R96619 : Reach 96619 := rs (se 1 (by rfl) ⟨72464, by rfl⟩) R144929
theorem R129545 : Reach 129545 := rs (se 2 (by rfl) ⟨48579, by rfl⟩) R97159
theorem R64039 : Reach 64039 := rs (se 1 (by rfl) ⟨48029, by rfl⟩) R96059
theorem R359113 : Reach 359113 := rs (se 2 (by rfl) ⟨134667, by rfl⟩) R269335
theorem R195371 : Reach 195371 := rs (se 1 (by rfl) ⟨146528, by rfl⟩) R293057
theorem R293705 : Reach 293705 := rs (se 2 (by rfl) ⟨110139, by rfl⟩) R220279
theorem R129887 : Reach 129887 := rs (se 1 (by rfl) ⟨97415, by rfl⟩) R194831
theorem R1276901 : Reach 1276901 := rs (se 4 (by rfl) ⟨119709, by rfl⟩) R239419
theorem R130067 : Reach 130067 := rs (se 1 (by rfl) ⟨97550, by rfl⟩) R195101
theorem R293939 : Reach 293939 := rs (se 1 (by rfl) ⟨220454, by rfl⟩) R440909
theorem R195641 : Reach 195641 := rs (se 2 (by rfl) ⟨73365, by rfl⟩) R146731
theorem R195851 : Reach 195851 := rs (se 1 (by rfl) ⟨146888, by rfl⟩) R293777
theorem R130409 : Reach 130409 := rs (se 2 (by rfl) ⟨48903, by rfl⟩) R97807
theorem R195965 : Reach 195965 := rs (se 3 (by rfl) ⟨36743, by rfl⟩) R73487
theorem R97679 : Reach 97679 := rs (se 1 (by rfl) ⟨73259, by rfl⟩) R146519
theorem R425569 : Reach 425569 := rs (se 2 (by rfl) ⟨159588, by rfl⟩) R319177
theorem R97915 : Reach 97915 := rs (se 1 (by rfl) ⟨73436, by rfl⟩) R146873
theorem R196235 : Reach 196235 := rs (se 1 (by rfl) ⟨147176, by rfl⟩) R294353
theorem R98003 : Reach 98003 := rs (se 1 (by rfl) ⟨73502, by rfl⟩) R147005
theorem R131003 : Reach 131003 := rs (se 1 (by rfl) ⟨98252, by rfl⟩) R196505
theorem R196667 : Reach 196667 := rs (se 1 (by rfl) ⟨147500, by rfl⟩) R295001
theorem R131201 : Reach 131201 := rs (se 2 (by rfl) ⟨49200, by rfl⟩) R98401
theorem R196937 : Reach 196937 := rs (se 2 (by rfl) ⟨73851, by rfl⟩) R147703
theorem R98651 : Reach 98651 := rs (se 1 (by rfl) ⟨73988, by rfl⟩) R147977
theorem R131435 : Reach 131435 := rs (se 1 (by rfl) ⟨98576, by rfl⟩) R197153
theorem R98671 : Reach 98671 := rs (se 1 (by rfl) ⟨74003, by rfl⟩) R148007
theorem R491939 : Reach 491939 := rs (se 1 (by rfl) ⟨368954, by rfl⟩) R737909
theorem R131579 : Reach 131579 := rs (se 1 (by rfl) ⟨98684, by rfl⟩) R197369
theorem R98887 : Reach 98887 := rs (se 1 (by rfl) ⟨74165, by rfl⟩) R148331
theorem R66155 : Reach 66155 := rs (se 1 (by rfl) ⟨49616, by rfl⟩) R99233
theorem R131705 : Reach 131705 := rs (se 2 (by rfl) ⟨49389, by rfl⟩) R98779
theorem R131759 : Reach 131759 := rs (se 1 (by rfl) ⟨98819, by rfl⟩) R197639
theorem R393943 : Reach 393943 := rs (se 1 (by rfl) ⟨295457, by rfl⟩) R590915
theorem R131807 : Reach 131807 := rs (se 1 (by rfl) ⟨98855, by rfl⟩) R197711
theorem R66271 : Reach 66271 := rs (se 1 (by rfl) ⟨49703, by rfl⟩) R99407
theorem R131831 : Reach 131831 := rs (se 1 (by rfl) ⟨98873, by rfl⟩) R197747
theorem R132011 : Reach 132011 := rs (se 1 (by rfl) ⟨99008, by rfl⟩) R198017
theorem R328643 : Reach 328643 := rs (se 1 (by rfl) ⟨246482, by rfl⟩) R492965
theorem R132083 : Reach 132083 := rs (se 1 (by rfl) ⟨99062, by rfl⟩) R198125
theorem R99319 : Reach 99319 := rs (se 1 (by rfl) ⟨74489, by rfl⟩) R148979
theorem R295973 : Reach 295973 := rs (se 4 (by rfl) ⟨27747, by rfl⟩) R55495
theorem R296135 : Reach 296135 := rs (se 1 (by rfl) ⟨222101, by rfl⟩) R444203
theorem R132391 : Reach 132391 := rs (se 1 (by rfl) ⟨99293, by rfl⟩) R198587
theorem R99623 : Reach 99623 := rs (se 1 (by rfl) ⟨74717, by rfl⟩) R149435
theorem R263519 : Reach 263519 := rs (se 1 (by rfl) ⟨197639, by rfl⟩) R395279
theorem R165215 : Reach 165215 := rs (se 1 (by rfl) ⟨123911, by rfl⟩) R247823
theorem R296297 : Reach 296297 := rs (se 2 (by rfl) ⟨111111, by rfl⟩) R222223
theorem R165281 : Reach 165281 := rs (se 2 (by rfl) ⟨61980, by rfl⟩) R123961
theorem R132551 : Reach 132551 := rs (se 1 (by rfl) ⟨99413, by rfl⟩) R198827
theorem R132911 : Reach 132911 := rs (se 1 (by rfl) ⟨99683, by rfl⟩) R199367
theorem R231457 : Reach 231457 := rs (se 2 (by rfl) ⟨86796, by rfl⟩) R173593
theorem R723761 : Reach 723761 := rs (se 2 (by rfl) ⟨271410, by rfl⟩) R542821
theorem R199667 : Reach 199667 := rs (se 1 (by rfl) ⟨149750, by rfl⟩) R299501
theorem R429137 : Reach 429137 := rs (se 2 (by rfl) ⟨160926, by rfl⟩) R321853
theorem R331127 : Reach 331127 := rs (se 1 (by rfl) ⟨248345, by rfl⟩) R496691
theorem R1609085 : Reach 1609085 := rs (se 3 (by rfl) ⟨301703, by rfl⟩) R603407
theorem R17927831 : Reach 17927831 := rs (se 1 (by rfl) ⟨13445873, by rfl⟩) R26891747
theorem R2330477 : Reach 2330477 := rs (se 3 (by rfl) ⟨436964, by rfl⟩) R873929
theorem R364445 : Reach 364445 := rs (se 3 (by rfl) ⟨68333, by rfl⟩) R136667
theorem R233531 : Reach 233531 := rs (se 1 (by rfl) ⟨175148, by rfl⟩) R350297
theorem R69979 : Reach 69979 := rs (se 1 (by rfl) ⟨52484, by rfl⟩) R104969
theorem R266935 : Reach 266935 := rs (se 1 (by rfl) ⟨200201, by rfl⟩) R400403
theorem R496313 : Reach 496313 := rs (se 2 (by rfl) ⟨186117, by rfl⟩) R372235
theorem R266951 : Reach 266951 := rs (se 1 (by rfl) ⟨200213, by rfl⟩) R400427
theorem R398047 : Reach 398047 := rs (se 1 (by rfl) ⟨298535, by rfl⟩) R597071
theorem R4166417 : Reach 4166417 := rs (se 2 (by rfl) ⟨1562406, by rfl⟩) R3124813
theorem R463781 : Reach 463781 := rs (se 4 (by rfl) ⟨43479, by rfl⟩) R86959
theorem R693197 : Reach 693197 := rs (se 3 (by rfl) ⟨129974, by rfl⟩) R259949
theorem R103567 : Reach 103567 := rs (se 1 (by rfl) ⟨77675, by rfl⟩) R155351
theorem R103711 : Reach 103711 := rs (se 1 (by rfl) ⟨77783, by rfl⟩) R155567
theorem R70951 : Reach 70951 := rs (se 1 (by rfl) ⟨53213, by rfl⟩) R106427
theorem R693629 : Reach 693629 := rs (se 3 (by rfl) ⟨130055, by rfl⟩) R260111
theorem R71275 : Reach 71275 := rs (se 1 (by rfl) ⟨53456, by rfl⟩) R106913
theorem R497339 : Reach 497339 := rs (se 1 (by rfl) ⟨373004, by rfl⟩) R746009
theorem R71479 : Reach 71479 := rs (se 1 (by rfl) ⟨53609, by rfl⟩) R107219
theorem R137321 : Reach 137321 := rs (se 2 (by rfl) ⟨51495, by rfl⟩) R102991
theorem R235649 : Reach 235649 := rs (se 2 (by rfl) ⟨88368, by rfl⟩) R176737
theorem R104915 : Reach 104915 := rs (se 1 (by rfl) ⟨78686, by rfl⟩) R157373
theorem R105067 : Reach 105067 := rs (se 1 (by rfl) ⟨78800, by rfl⟩) R157601
theorem R334475 : Reach 334475 := rs (se 1 (by rfl) ⟨250856, by rfl⟩) R501713
theorem R105295 : Reach 105295 := rs (se 1 (by rfl) ⟨78971, by rfl⟩) R157943
theorem R301967 : Reach 301967 := rs (se 1 (by rfl) ⟨226475, by rfl⟩) R452951
theorem R105371 : Reach 105371 := rs (se 1 (by rfl) ⟨79028, by rfl⟩) R158057
theorem R72991 : Reach 72991 := rs (se 1 (by rfl) ⟨54743, by rfl⟩) R109487
theorem R368009 : Reach 368009 := rs (se 2 (by rfl) ⟨138003, by rfl⟩) R276007
theorem R400889 : Reach 400889 := rs (se 2 (by rfl) ⟨150333, by rfl⟩) R300667
theorem R532331 : Reach 532331 := rs (se 1 (by rfl) ⟨399248, by rfl⟩) R798497
theorem R467153 : Reach 467153 := rs (se 2 (by rfl) ⟨175182, by rfl⟩) R350365
theorem R139745 : Reach 139745 := rs (se 2 (by rfl) ⟨52404, by rfl⟩) R104809
theorem R369467 : Reach 369467 := rs (se 1 (by rfl) ⟨277100, by rfl⟩) R554201
theorem R140251 : Reach 140251 := rs (se 1 (by rfl) ⟨105188, by rfl⟩) R210377
theorem R140575 : Reach 140575 := rs (se 1 (by rfl) ⟨105431, by rfl⟩) R210863
theorem R567425 : Reach 567425 := rs (se 2 (by rfl) ⟨212784, by rfl⟩) R425569
theorem R272663 : Reach 272663 := rs (se 1 (by rfl) ⟨204497, by rfl⟩) R408995
theorem R141659 : Reach 141659 := rs (se 1 (by rfl) ⟨106244, by rfl⟩) R212489
theorem R404291 : Reach 404291 := rs (se 1 (by rfl) ⟨303218, by rfl⟩) R606437
theorem R142631 : Reach 142631 := rs (se 1 (by rfl) ⟨106973, by rfl⟩) R213947
theorem R241015 : Reach 241015 := rs (se 1 (by rfl) ⟨180761, by rfl⟩) R361523
theorem R110315 : Reach 110315 := rs (se 1 (by rfl) ⟨82736, by rfl⟩) R165473
theorem R143111 : Reach 143111 := rs (se 1 (by rfl) ⟨107333, by rfl⟩) R214667
theorem R438443 : Reach 438443 := rs (se 1 (by rfl) ⟨328832, by rfl⟩) R657665
theorem R242347 : Reach 242347 := rs (se 1 (by rfl) ⟨181760, by rfl⟩) R363521
theorem R111287 : Reach 111287 := rs (se 1 (by rfl) ⟨83465, by rfl⟩) R166931
theorem R144119 : Reach 144119 := rs (se 1 (by rfl) ⟨108089, by rfl⟩) R216179
theorem R78823 : Reach 78823 := rs (se 1 (by rfl) ⟨59117, by rfl⟩) R118235
theorem R275699 : Reach 275699 := rs (se 1 (by rfl) ⟨206774, by rfl⟩) R413549
theorem R144737 : Reach 144737 := rs (se 2 (by rfl) ⟨54276, by rfl⟩) R108553
theorem R3225091 : Reach 3225091 := rs (se 1 (by rfl) ⟨2418818, by rfl⟩) R4837637
theorem R669221 : Reach 669221 := rs (se 4 (by rfl) ⟨62739, by rfl⟩) R125479
theorem R146195 : Reach 146195 := rs (se 1 (by rfl) ⟨109646, by rfl⟩) R219293
theorem R932755 : Reach 932755 := rs (se 1 (by rfl) ⟨699566, by rfl⟩) R1399133
theorem R146407 : Reach 146407 := rs (se 1 (by rfl) ⟨109805, by rfl⟩) R219611
theorem R539635 : Reach 539635 := rs (se 1 (by rfl) ⟨404726, by rfl⟩) R809453
theorem R146681 : Reach 146681 := rs (se 2 (by rfl) ⟨55005, by rfl⟩) R110011
theorem R212291 : Reach 212291 := rs (se 1 (by rfl) ⟨159218, by rfl⟩) R318437
theorem R212321 : Reach 212321 := rs (se 2 (by rfl) ⟨79620, by rfl⟩) R159241
theorem R81643 : Reach 81643 := rs (se 1 (by rfl) ⟨61232, by rfl⟩) R122465
theorem R212777 : Reach 212777 := rs (se 2 (by rfl) ⟨79791, by rfl⟩) R159583
theorem R147329 : Reach 147329 := rs (se 2 (by rfl) ⟨55248, by rfl⟩) R110497
theorem R82343 : Reach 82343 := rs (se 1 (by rfl) ⟨61757, by rfl⟩) R123515
theorem R147887 : Reach 147887 := rs (se 1 (by rfl) ⟨110915, by rfl⟩) R221831
theorem R147895 : Reach 147895 := rs (se 1 (by rfl) ⟨110921, by rfl⟩) R221843
theorem R606689 : Reach 606689 := rs (se 2 (by rfl) ⟨227508, by rfl⟩) R455017
theorem R115273 : Reach 115273 := rs (se 2 (by rfl) ⟨43227, by rfl⟩) R86455
theorem R574087 : Reach 574087 := rs (se 1 (by rfl) ⟨430565, by rfl⟩) R861131
theorem R148139 : Reach 148139 := rs (se 1 (by rfl) ⟨111104, by rfl⟩) R222209
theorem R443231 : Reach 443231 := rs (se 1 (by rfl) ⟨332423, by rfl⟩) R664847
theorem R148367 : Reach 148367 := rs (se 1 (by rfl) ⟨111275, by rfl⟩) R222551
theorem R1295297 : Reach 1295297 := rs (se 2 (by rfl) ⟨485736, by rfl⟩) R971473
theorem R3621827 : Reach 3621827 := rs (se 1 (by rfl) ⟨2716370, by rfl⟩) R5432741
theorem R213961 : Reach 213961 := rs (se 2 (by rfl) ⟨80235, by rfl⟩) R160471
theorem R82919 : Reach 82919 := rs (se 1 (by rfl) ⟨62189, by rfl⟩) R124379
theorem R541895 : Reach 541895 := rs (se 1 (by rfl) ⟨406421, by rfl⟩) R812843
theorem R83177 : Reach 83177 := rs (se 2 (by rfl) ⟨31191, by rfl⟩) R62383
theorem R214265 : Reach 214265 := rs (se 2 (by rfl) ⟨80349, by rfl⟩) R160699
theorem R83231 : Reach 83231 := rs (se 1 (by rfl) ⟨62423, by rfl⟩) R124847
theorem R148775 : Reach 148775 := rs (se 1 (by rfl) ⟨111581, by rfl⟩) R223163
theorem R214433 : Reach 214433 := rs (se 2 (by rfl) ⟨80412, by rfl⟩) R160825
theorem R2377133 : Reach 2377133 := rs (se 3 (by rfl) ⟨445712, by rfl⟩) R891425
theorem R83399 : Reach 83399 := rs (se 1 (by rfl) ⟨62549, by rfl⟩) R125099
theorem R148999 : Reach 148999 := rs (se 1 (by rfl) ⟨111749, by rfl⟩) R223499
theorem R280097 : Reach 280097 := rs (se 2 (by rfl) ⟨105036, by rfl⟩) R210073
theorem R83753 : Reach 83753 := rs (se 2 (by rfl) ⟨31407, by rfl⟩) R62815
theorem R83759 : Reach 83759 := rs (se 1 (by rfl) ⟨62819, by rfl⟩) R125639
theorem R83767 : Reach 83767 := rs (se 1 (by rfl) ⟨62825, by rfl⟩) R125651
theorem R149303 : Reach 149303 := rs (se 1 (by rfl) ⟨111977, by rfl⟩) R223955
theorem R1034167 : Reach 1034167 := rs (se 1 (by rfl) ⟨775625, by rfl⟩) R1551251
theorem R84233 : Reach 84233 := rs (se 2 (by rfl) ⟨31587, by rfl⟩) R63175
theorem R84335 : Reach 84335 := rs (se 1 (by rfl) ⟨63251, by rfl⟩) R126503
theorem R84551 : Reach 84551 := rs (se 1 (by rfl) ⟨63413, by rfl⟩) R126827
theorem R84587 : Reach 84587 := rs (se 1 (by rfl) ⟨63440, by rfl⟩) R126881
theorem R445175 : Reach 445175 := rs (se 1 (by rfl) ⟨333881, by rfl⟩) R667763
theorem R84815 : Reach 84815 := rs (se 1 (by rfl) ⟨63611, by rfl⟩) R127223
theorem R150443 : Reach 150443 := rs (se 1 (by rfl) ⟨112832, by rfl⟩) R225665
theorem R150491 : Reach 150491 := rs (se 1 (by rfl) ⟨112868, by rfl⟩) R225737
theorem R478223 : Reach 478223 := rs (se 1 (by rfl) ⟨358667, by rfl⟩) R717335
theorem R85211 : Reach 85211 := rs (se 1 (by rfl) ⟨63908, by rfl⟩) R127817
theorem R281819 : Reach 281819 := rs (se 1 (by rfl) ⟨211364, by rfl⟩) R422729
theorem R85385 : Reach 85385 := rs (se 2 (by rfl) ⟨32019, by rfl⟩) R64039
theorem R118265 : Reach 118265 := rs (se 2 (by rfl) ⟨44349, by rfl⟩) R88699
theorem R249439 : Reach 249439 := rs (se 1 (by rfl) ⟨187079, by rfl⟩) R374159
theorem R478817 : Reach 478817 := rs (se 2 (by rfl) ⟨179556, by rfl⟩) R359113
theorem R315089 : Reach 315089 := rs (se 2 (by rfl) ⟨118158, by rfl⟩) R236317
theorem R85739 : Reach 85739 := rs (se 1 (by rfl) ⟨64304, by rfl⟩) R128609
theorem R85967 : Reach 85967 := rs (se 1 (by rfl) ⟨64475, by rfl⟩) R128951
theorem R86363 : Reach 86363 := rs (se 1 (by rfl) ⟨64772, by rfl⟩) R129545
theorem R1102325 : Reach 1102325 := rs (se 5 (by rfl) ⟨51671, by rfl⟩) R103343
theorem R1233467 : Reach 1233467 := rs (se 1 (by rfl) ⟨925100, by rfl⟩) R1850201
theorem R86591 : Reach 86591 := rs (se 1 (by rfl) ⟨64943, by rfl⟩) R129887
theorem R86711 : Reach 86711 := rs (se 1 (by rfl) ⟨65033, by rfl⟩) R130067
theorem R840527 : Reach 840527 := rs (se 1 (by rfl) ⟨630395, by rfl⟩) R1260791
theorem R86939 : Reach 86939 := rs (se 1 (by rfl) ⟨65204, by rfl⟩) R130409
theorem R251095 : Reach 251095 := rs (se 1 (by rfl) ⟨188321, by rfl⟩) R376643
theorem R382201 : Reach 382201 := rs (se 2 (by rfl) ⟨143325, by rfl⟩) R286651
theorem R87335 : Reach 87335 := rs (se 1 (by rfl) ⟨65501, by rfl⟩) R131003
theorem R87419 : Reach 87419 := rs (se 1 (by rfl) ⟨65564, by rfl⟩) R131129
theorem R120251 : Reach 120251 := rs (se 1 (by rfl) ⟨90188, by rfl⟩) R180377
theorem R87545 : Reach 87545 := rs (se 2 (by rfl) ⟨32829, by rfl⟩) R65659
theorem R349733 : Reach 349733 := rs (se 4 (by rfl) ⟨32787, by rfl⟩) R65575
theorem R87647 : Reach 87647 := rs (se 1 (by rfl) ⟨65735, by rfl⟩) R131471
theorem R87815 : Reach 87815 := rs (se 1 (by rfl) ⟨65861, by rfl⟩) R131723
theorem R284471 : Reach 284471 := rs (se 1 (by rfl) ⟨213353, by rfl⟩) R426707
theorem R87863 : Reach 87863 := rs (se 1 (by rfl) ⟨65897, by rfl⟩) R131795
theorem R55195 : Reach 55195 := rs (se 1 (by rfl) ⟨41396, by rfl⟩) R82793
theorem R55247 : Reach 55247 := rs (se 1 (by rfl) ⟨41435, by rfl⟩) R82871
theorem R55271 : Reach 55271 := rs (se 1 (by rfl) ⟨41453, by rfl⟩) R82907
theorem R186401 : Reach 186401 := rs (se 2 (by rfl) ⟨69900, by rfl⟩) R139801
theorem R88169 : Reach 88169 := rs (se 2 (by rfl) ⟨33063, by rfl⟩) R66127
theorem R284957 : Reach 284957 := rs (se 3 (by rfl) ⟨53429, by rfl⟩) R106859
theorem R55583 : Reach 55583 := rs (se 1 (by rfl) ⟨41687, by rfl⟩) R83375
theorem R55643 : Reach 55643 := rs (se 1 (by rfl) ⟨41732, by rfl⟩) R83465
theorem R55663 : Reach 55663 := rs (se 1 (by rfl) ⟨41747, by rfl⟩) R83495
theorem R55719 : Reach 55719 := rs (se 1 (by rfl) ⟨41789, by rfl⟩) R83579
theorem R88487 : Reach 88487 := rs (se 1 (by rfl) ⟨66365, by rfl⟩) R132731
theorem R55803 : Reach 55803 := rs (se 1 (by rfl) ⟨41852, by rfl⟩) R83705
theorem R88571 : Reach 88571 := rs (se 1 (by rfl) ⟨66428, by rfl⟩) R132857
theorem R55871 : Reach 55871 := rs (se 1 (by rfl) ⟨41903, by rfl⟩) R83807
theorem R55879 : Reach 55879 := rs (se 1 (by rfl) ⟨41909, by rfl⟩) R83819
theorem R88649 : Reach 88649 := rs (se 2 (by rfl) ⟨33243, by rfl⟩) R66487
theorem R187055 : Reach 187055 := rs (se 1 (by rfl) ⟨140291, by rfl⟩) R280583
theorem R56031 : Reach 56031 := rs (se 1 (by rfl) ⟨42023, by rfl⟩) R84047
theorem R56111 : Reach 56111 := rs (se 1 (by rfl) ⟨42083, by rfl⟩) R84167
theorem R56219 : Reach 56219 := rs (se 1 (by rfl) ⟨42164, by rfl⟩) R84329
theorem R482233 : Reach 482233 := rs (se 2 (by rfl) ⟨180837, by rfl⟩) R361675
theorem R56271 : Reach 56271 := rs (se 1 (by rfl) ⟨42203, by rfl⟩) R84407
theorem R56295 : Reach 56295 := rs (se 1 (by rfl) ⟨42221, by rfl⟩) R84443
theorem R187379 : Reach 187379 := rs (se 1 (by rfl) ⟨140534, by rfl⟩) R281069
theorem R56607 : Reach 56607 := rs (se 1 (by rfl) ⟨42455, by rfl⟩) R84911
theorem R56667 : Reach 56667 := rs (se 1 (by rfl) ⟨42500, by rfl⟩) R85001
theorem R56687 : Reach 56687 := rs (se 1 (by rfl) ⟨42515, by rfl⟩) R85031
theorem R220553 : Reach 220553 := rs (se 2 (by rfl) ⟨82707, by rfl⟩) R165415
theorem R56743 : Reach 56743 := rs (se 1 (by rfl) ⟨42557, by rfl⟩) R85115
theorem R56827 : Reach 56827 := rs (se 1 (by rfl) ⟨42620, by rfl⟩) R85241
theorem R187919 : Reach 187919 := rs (se 1 (by rfl) ⟨140939, by rfl⟩) R281879
theorem R56895 : Reach 56895 := rs (se 1 (by rfl) ⟨42671, by rfl⟩) R85343
theorem R56903 : Reach 56903 := rs (se 1 (by rfl) ⟨42677, by rfl⟩) R85355
theorem R57055 : Reach 57055 := rs (se 1 (by rfl) ⟨42791, by rfl⟩) R85583
theorem R57135 : Reach 57135 := rs (se 1 (by rfl) ⟨42851, by rfl⟩) R85703
theorem R548669 : Reach 548669 := rs (se 3 (by rfl) ⟨102875, by rfl⟩) R205751
theorem R57243 : Reach 57243 := rs (se 1 (by rfl) ⟨42932, by rfl⟩) R85865
theorem R57295 : Reach 57295 := rs (se 1 (by rfl) ⟨42971, by rfl⟩) R85943
theorem R57319 : Reach 57319 := rs (se 1 (by rfl) ⟨42989, by rfl⟩) R85979
theorem R1138697 : Reach 1138697 := rs (se 2 (by rfl) ⟨427011, by rfl⟩) R854023
theorem R286739 : Reach 286739 := rs (se 1 (by rfl) ⟨215054, by rfl⟩) R430109
theorem R57631 : Reach 57631 := rs (se 1 (by rfl) ⟨43223, by rfl⟩) R86447
theorem R57691 : Reach 57691 := rs (se 1 (by rfl) ⟨43268, by rfl⟩) R86537
theorem R57711 : Reach 57711 := rs (se 1 (by rfl) ⟨43283, by rfl⟩) R86567
theorem R57767 : Reach 57767 := rs (se 1 (by rfl) ⟨43325, by rfl⟩) R86651
theorem R516577 : Reach 516577 := rs (se 2 (by rfl) ⟨193716, by rfl⟩) R387433
theorem R57851 : Reach 57851 := rs (se 1 (by rfl) ⟨43388, by rfl⟩) R86777
theorem R57919 : Reach 57919 := rs (se 1 (by rfl) ⟨43439, by rfl⟩) R86879
theorem R188999 : Reach 188999 := rs (se 1 (by rfl) ⟨141749, by rfl⟩) R283499
theorem R57927 : Reach 57927 := rs (se 1 (by rfl) ⟨43445, by rfl⟩) R86891
theorem R58079 : Reach 58079 := rs (se 1 (by rfl) ⟨43559, by rfl⟩) R87119
theorem R58159 : Reach 58159 := rs (se 1 (by rfl) ⟨43619, by rfl⟩) R87239
theorem R58191 : Reach 58191 := rs (se 1 (by rfl) ⟨43643, by rfl⟩) R87287
theorem R58267 : Reach 58267 := rs (se 1 (by rfl) ⟨43700, by rfl⟩) R87401
theorem R58319 : Reach 58319 := rs (se 1 (by rfl) ⟨43739, by rfl⟩) R87479
theorem R58343 : Reach 58343 := rs (se 1 (by rfl) ⟨43757, by rfl⟩) R87515
theorem R189431 : Reach 189431 := rs (se 1 (by rfl) ⟨142073, by rfl⟩) R284147
theorem R58587 : Reach 58587 := rs (se 1 (by rfl) ⟨43940, by rfl⟩) R87881
theorem R58655 : Reach 58655 := rs (se 1 (by rfl) ⟨43991, by rfl⟩) R87983
theorem R124199 : Reach 124199 := rs (se 1 (by rfl) ⟨93149, by rfl⟩) R186299
theorem R58663 : Reach 58663 := rs (se 1 (by rfl) ⟨43997, by rfl⟩) R87995
theorem R58715 : Reach 58715 := rs (se 1 (by rfl) ⟨44036, by rfl⟩) R88073
theorem R58735 : Reach 58735 := rs (se 1 (by rfl) ⟨44051, by rfl⟩) R88103
theorem R58747 : Reach 58747 := rs (se 1 (by rfl) ⟨44060, by rfl⟩) R88121
theorem R58791 : Reach 58791 := rs (se 1 (by rfl) ⟨44093, by rfl⟩) R88187
theorem R58823 : Reach 58823 := rs (se 1 (by rfl) ⟨44117, by rfl⟩) R88235
theorem R976373 : Reach 976373 := rs (se 5 (by rfl) ⟨45767, by rfl⟩) R91535
theorem R58875 : Reach 58875 := rs (se 1 (by rfl) ⟨44156, by rfl⟩) R88313
theorem R58943 : Reach 58943 := rs (se 1 (by rfl) ⟨44207, by rfl⟩) R88415
theorem R58951 : Reach 58951 := rs (se 1 (by rfl) ⟨44213, by rfl⟩) R88427
theorem R419417 : Reach 419417 := rs (se 2 (by rfl) ⟨157281, by rfl⟩) R314563
theorem R714329 : Reach 714329 := rs (se 2 (by rfl) ⟨267873, by rfl⟩) R535747
theorem R58975 : Reach 58975 := rs (se 1 (by rfl) ⟨44231, by rfl⟩) R88463
theorem R124577 : Reach 124577 := rs (se 2 (by rfl) ⟨46716, by rfl⟩) R93433
theorem R59055 : Reach 59055 := rs (se 1 (by rfl) ⟨44291, by rfl⟩) R88583
theorem R59103 : Reach 59103 := rs (se 1 (by rfl) ⟨44327, by rfl⟩) R88655
theorem R452429 : Reach 452429 := rs (se 3 (by rfl) ⟨84830, by rfl⟩) R169661
theorem R190295 : Reach 190295 := rs (se 1 (by rfl) ⟨142721, by rfl⟩) R285443
theorem R124937 : Reach 124937 := rs (se 2 (by rfl) ⟨46851, by rfl⟩) R93703
theorem R125351 : Reach 125351 := rs (se 1 (by rfl) ⟨94013, by rfl⟩) R188027
theorem R223655 : Reach 223655 := rs (se 1 (by rfl) ⟨167741, by rfl⟩) R335483
theorem R125459 : Reach 125459 := rs (se 1 (by rfl) ⟨94094, by rfl⟩) R188189
theorem R125513 : Reach 125513 := rs (se 2 (by rfl) ⟨47067, by rfl⟩) R94135
theorem R322127 : Reach 322127 := rs (se 1 (by rfl) ⟨241595, by rfl⟩) R483191
theorem R289655 : Reach 289655 := rs (se 1 (by rfl) ⟨217241, by rfl⟩) R434483
theorem R191375 : Reach 191375 := rs (se 1 (by rfl) ⟨143531, by rfl⟩) R287063
theorem R125927 : Reach 125927 := rs (se 1 (by rfl) ⟨94445, by rfl⟩) R188891
theorem R126305 : Reach 126305 := rs (se 2 (by rfl) ⟨47364, by rfl⟩) R94729
theorem R126395 : Reach 126395 := rs (se 1 (by rfl) ⟨94796, by rfl⟩) R189593
theorem R159175 : Reach 159175 := rs (se 1 (by rfl) ⟨119381, by rfl⟩) R238763
theorem R126521 : Reach 126521 := rs (se 2 (by rfl) ⟨47445, by rfl⟩) R94891
theorem R93791 : Reach 93791 := rs (se 1 (by rfl) ⟨70343, by rfl⟩) R140687
theorem R290465 : Reach 290465 := rs (se 2 (by rfl) ⟨108924, by rfl⟩) R217849
theorem R94007 : Reach 94007 := rs (se 1 (by rfl) ⟨70505, by rfl⟩) R141011
theorem R323585 : Reach 323585 := rs (se 2 (by rfl) ⟨121344, by rfl⟩) R242689
theorem R192617 : Reach 192617 := rs (se 2 (by rfl) ⟨72231, by rfl⟩) R144463
theorem R127187 : Reach 127187 := rs (se 1 (by rfl) ⟨95390, by rfl⟩) R190781
theorem R127241 : Reach 127241 := rs (se 2 (by rfl) ⟨47715, by rfl⟩) R95431
theorem R1208591 : Reach 1208591 := rs (se 1 (by rfl) ⟨906443, by rfl⟩) R1812887
theorem R127457 : Reach 127457 := rs (se 2 (by rfl) ⟨47796, by rfl⟩) R95593
theorem R94783 : Reach 94783 := rs (se 1 (by rfl) ⟨71087, by rfl⟩) R142175
theorem R62023 : Reach 62023 := rs (se 1 (by rfl) ⟨46517, by rfl⟩) R93035
theorem R1798807 : Reach 1798807 := rs (se 1 (by rfl) ⟨1349105, by rfl⟩) R2698211
theorem R127763 : Reach 127763 := rs (se 1 (by rfl) ⟨95822, by rfl⟩) R191645
theorem R193481 : Reach 193481 := rs (se 2 (by rfl) ⟨72555, by rfl⟩) R145111
theorem R127991 : Reach 127991 := rs (se 1 (by rfl) ⟨95993, by rfl⟩) R191987
theorem R128123 : Reach 128123 := rs (se 1 (by rfl) ⟨96092, by rfl⟩) R192185
theorem R193751 : Reach 193751 := rs (se 1 (by rfl) ⟨145313, by rfl⟩) R290627
theorem R95465 : Reach 95465 := rs (se 2 (by rfl) ⟨35799, by rfl⟩) R71599
theorem R128249 : Reach 128249 := rs (se 2 (by rfl) ⟨48093, by rfl⟩) R96187
theorem R95519 : Reach 95519 := rs (se 1 (by rfl) ⟨71639, by rfl⟩) R143279
theorem R128393 : Reach 128393 := rs (se 2 (by rfl) ⟨48147, by rfl⟩) R96295
theorem R62887 : Reach 62887 := rs (se 1 (by rfl) ⟨47165, by rfl⟩) R94331
theorem R128519 : Reach 128519 := rs (se 1 (by rfl) ⟨96389, by rfl⟩) R192779
theorem R292409 : Reach 292409 := rs (se 2 (by rfl) ⟨109653, by rfl⟩) R219307
theorem R128699 : Reach 128699 := rs (se 1 (by rfl) ⟨96524, by rfl⟩) R193049
theorem R358199 : Reach 358199 := rs (se 1 (by rfl) ⟨268649, by rfl⟩) R537299
theorem R128825 : Reach 128825 := rs (se 2 (by rfl) ⟨48309, by rfl⟩) R96619
theorem R63463 : Reach 63463 := rs (se 1 (by rfl) ⟨47597, by rfl⟩) R95195
theorem R129455 : Reach 129455 := rs (se 1 (by rfl) ⟨97091, by rfl⟩) R194183
theorem R2587085 : Reach 2587085 := rs (se 3 (by rfl) ⟨485078, by rfl⟩) R970157
theorem R129491 : Reach 129491 := rs (se 1 (by rfl) ⟨97118, by rfl⟩) R194237
theorem R129599 : Reach 129599 := rs (se 1 (by rfl) ⟨97199, by rfl⟩) R194399
theorem R457289 : Reach 457289 := rs (se 2 (by rfl) ⟨171483, by rfl⟩) R342967
theorem R96889 : Reach 96889 := rs (se 2 (by rfl) ⟨36333, by rfl⟩) R72667
theorem R129707 : Reach 129707 := rs (se 1 (by rfl) ⟨97280, by rfl⟩) R194561
theorem R96943 : Reach 96943 := rs (se 1 (by rfl) ⟨72707, by rfl⟩) R145415
theorem R130247 : Reach 130247 := rs (se 1 (by rfl) ⟨97685, by rfl⟩) R195371
theorem R195803 : Reach 195803 := rs (se 1 (by rfl) ⟨146852, by rfl⟩) R293705
theorem R851267 : Reach 851267 := rs (se 1 (by rfl) ⟨638450, by rfl⟩) R1276901
theorem R195959 : Reach 195959 := rs (se 1 (by rfl) ⟨146969, by rfl⟩) R293939
theorem R130427 : Reach 130427 := rs (se 1 (by rfl) ⟨97820, by rfl⟩) R195641
theorem R130553 : Reach 130553 := rs (se 2 (by rfl) ⟨48957, by rfl⟩) R97915
theorem R130567 : Reach 130567 := rs (se 1 (by rfl) ⟨97925, by rfl⟩) R195851
theorem R130643 : Reach 130643 := rs (se 1 (by rfl) ⟨97982, by rfl⟩) R195965
theorem R65119 : Reach 65119 := rs (se 1 (by rfl) ⟨48839, by rfl⟩) R97679
theorem R294515 : Reach 294515 := rs (se 1 (by rfl) ⟨220886, by rfl⟩) R441773
theorem R425735 : Reach 425735 := rs (se 1 (by rfl) ⟨319301, by rfl⟩) R638603
theorem R130823 : Reach 130823 := rs (se 1 (by rfl) ⟨98117, by rfl⟩) R196235
theorem R65335 : Reach 65335 := rs (se 1 (by rfl) ⟨49001, by rfl⟩) R98003
theorem R163741 : Reach 163741 := rs (se 3 (by rfl) ⟨30701, by rfl⟩) R61403
theorem R131111 : Reach 131111 := rs (se 1 (by rfl) ⟨98333, by rfl⟩) R196667
theorem R131291 : Reach 131291 := rs (se 1 (by rfl) ⟨98468, by rfl⟩) R196937
theorem R65767 : Reach 65767 := rs (se 1 (by rfl) ⟨49325, by rfl⟩) R98651
theorem R327959 : Reach 327959 := rs (se 1 (by rfl) ⟨245969, by rfl⟩) R491939
theorem R98591 : Reach 98591 := rs (se 1 (by rfl) ⟨73943, by rfl⟩) R147887
theorem R98759 : Reach 98759 := rs (se 1 (by rfl) ⟨74069, by rfl⟩) R148139
theorem R131561 : Reach 131561 := rs (se 2 (by rfl) ⟨49335, by rfl⟩) R98671
theorem R295487 : Reach 295487 := rs (se 1 (by rfl) ⟨221615, by rfl⟩) R443231
theorem R98911 : Reach 98911 := rs (se 1 (by rfl) ⟨74183, by rfl⟩) R148367
theorem R688769 : Reach 688769 := rs (se 2 (by rfl) ⟨258288, by rfl⟩) R516577
theorem R197315 : Reach 197315 := rs (se 1 (by rfl) ⟨147986, by rfl⟩) R295973
theorem R131849 : Reach 131849 := rs (se 2 (by rfl) ⟨49443, by rfl⟩) R98887
theorem R197423 : Reach 197423 := rs (se 1 (by rfl) ⟨148067, by rfl⟩) R296135
theorem R66415 : Reach 66415 := rs (se 1 (by rfl) ⟨49811, by rfl⟩) R99623
theorem R197531 : Reach 197531 := rs (se 1 (by rfl) ⟨148148, by rfl⟩) R296297
theorem R525257 : Reach 525257 := rs (se 2 (by rfl) ⟨196971, by rfl⟩) R393943
theorem R99535 : Reach 99535 := rs (se 1 (by rfl) ⟨74651, by rfl⟩) R149303
theorem R132425 : Reach 132425 := rs (se 2 (by rfl) ⟨49659, by rfl⟩) R99319
theorem R296783 : Reach 296783 := rs (se 1 (by rfl) ⟨222587, by rfl⟩) R445175
theorem R100295 : Reach 100295 := rs (se 1 (by rfl) ⟨75221, by rfl⟩) R150443
theorem R100327 : Reach 100327 := rs (se 1 (by rfl) ⟨75245, by rfl⟩) R150491
theorem R133111 : Reach 133111 := rs (se 1 (by rfl) ⟨99833, by rfl⟩) R199667
theorem R198665 : Reach 198665 := rs (se 2 (by rfl) ⟨74499, by rfl⟩) R148999
theorem R788773 : Reach 788773 := rs (se 4 (by rfl) ⟨73947, by rfl⟩) R147895
theorem R1378889 : Reach 1378889 := rs (se 2 (by rfl) ⟨517083, by rfl⟩) R1034167
theorem R822311 : Reach 822311 := rs (se 1 (by rfl) ⟨616733, by rfl⟩) R1233467
theorem R330875 : Reach 330875 := rs (se 1 (by rfl) ⟨248156, by rfl⟩) R496313
theorem R1445053 : Reach 1445053 := rs (se 3 (by rfl) ⟨270947, by rfl⟩) R541895
theorem R560351 : Reach 560351 := rs (se 1 (by rfl) ⟨420263, by rfl⟩) R840527
theorem R462131 : Reach 462131 := rs (se 1 (by rfl) ⟨346598, by rfl⟩) R693197
theorem R396733 : Reach 396733 := rs (se 3 (by rfl) ⟨74387, by rfl⟩) R148775
theorem R462419 : Reach 462419 := rs (se 1 (by rfl) ⟨346814, by rfl⟩) R693629
theorem R233155 : Reach 233155 := rs (se 1 (by rfl) ⟨174866, by rfl⟩) R349733
theorem R331559 : Reach 331559 := rs (se 1 (by rfl) ⟨248669, by rfl⟩) R497339
theorem R201311 : Reach 201311 := rs (se 1 (by rfl) ⟨150983, by rfl⟩) R301967
theorem R70247 : Reach 70247 := rs (se 1 (by rfl) ⟨52685, by rfl⟩) R105371
theorem R332585 : Reach 332585 := rs (se 2 (by rfl) ⟨124719, by rfl⟩) R249439
theorem R267259 : Reach 267259 := rs (se 1 (by rfl) ⟨200444, by rfl⟩) R400889
theorem R365779 : Reach 365779 := rs (se 1 (by rfl) ⟨274334, by rfl⟩) R548669
theorem R759131 : Reach 759131 := rs (se 1 (by rfl) ⟨569348, by rfl⟩) R1138697
theorem R628397 : Reach 628397 := rs (se 3 (by rfl) ⟨117824, by rfl⟩) R235649
theorem R2398409 : Reach 2398409 := rs (se 2 (by rfl) ⟨899403, by rfl⟩) R1798807
theorem R530729 : Reach 530729 := rs (se 2 (by rfl) ⟨199023, by rfl⟩) R398047
theorem R596413 : Reach 596413 := rs (se 3 (by rfl) ⟨111827, by rfl⟩) R223655
theorem R301619 : Reach 301619 := rs (se 1 (by rfl) ⟨226214, by rfl⟩) R452429
theorem R2038405 : Reach 2038405 := rs (se 4 (by rfl) ⟨191100, by rfl⟩) R382201
theorem R138089 : Reach 138089 := rs (se 2 (by rfl) ⟨51783, by rfl⟩) R103567
theorem R334793 : Reach 334793 := rs (se 2 (by rfl) ⟨125547, by rfl⟩) R251095
theorem R138281 : Reach 138281 := rs (se 2 (by rfl) ⟨51855, by rfl⟩) R103711
theorem R4300121 : Reach 4300121 := rs (se 2 (by rfl) ⟨1612545, by rfl⟩) R3225091
theorem R73543 : Reach 73543 := rs (se 1 (by rfl) ⟨55157, by rfl⟩) R110315
theorem R74191 : Reach 74191 := rs (se 1 (by rfl) ⟨55643, by rfl⟩) R111287
theorem R140089 : Reach 140089 := rs (se 2 (by rfl) ⟨52533, by rfl⟩) R105067
theorem R2270045 : Reach 2270045 := rs (se 3 (by rfl) ⟨425633, by rfl⟩) R851267
theorem R140393 : Reach 140393 := rs (se 2 (by rfl) ⟨52647, by rfl⟩) R105295
theorem R238799 : Reach 238799 := rs (se 1 (by rfl) ⟨179099, by rfl⟩) R358199
theorem R304859 : Reach 304859 := rs (se 1 (by rfl) ⟨228644, by rfl⟩) R457289
theorem R174089 : Reach 174089 := rs (se 2 (by rfl) ⟨65283, by rfl⟩) R130567
theorem R141527 : Reach 141527 := rs (se 1 (by rfl) ⟨106145, by rfl⟩) R212291
theorem R141547 : Reach 141547 := rs (se 1 (by rfl) ⟨106160, by rfl⟩) R212321
theorem R108857 : Reach 108857 := rs (se 2 (by rfl) ⟨40821, by rfl⟩) R81643
theorem R141851 : Reach 141851 := rs (se 1 (by rfl) ⟨106388, by rfl⟩) R212777
theorem R404459 : Reach 404459 := rs (se 1 (by rfl) ⟨303344, by rfl⟩) R606689
theorem R863531 : Reach 863531 := rs (se 1 (by rfl) ⟨647648, by rfl⟩) R1295297
theorem R142843 : Reach 142843 := rs (se 1 (by rfl) ⟨107132, by rfl⟩) R214265
theorem R765449 : Reach 765449 := rs (se 2 (by rfl) ⟨287043, by rfl⟩) R574087
theorem R175679 : Reach 175679 := rs (se 1 (by rfl) ⟨131759, by rfl⟩) R263519
theorem R110143 : Reach 110143 := rs (se 1 (by rfl) ⟨82607, by rfl⟩) R165215
theorem R142955 : Reach 142955 := rs (se 1 (by rfl) ⟨107216, by rfl⟩) R214433
theorem R1584755 : Reach 1584755 := rs (se 1 (by rfl) ⟨1188566, by rfl⟩) R2377133
theorem R176413 : Reach 176413 := rs (se 3 (by rfl) ⟨33077, by rfl⟩) R66155
theorem R176521 : Reach 176521 := rs (se 2 (by rfl) ⟨66195, by rfl⟩) R132391
theorem R111689 : Reach 111689 := rs (se 2 (by rfl) ⟨41883, by rfl⟩) R83767
theorem R210059 : Reach 210059 := rs (se 1 (by rfl) ⟨157544, by rfl⟩) R315089
theorem R1553651 : Reach 1553651 := rs (se 1 (by rfl) ⟨1165238, by rfl⟩) R2330477
theorem R242963 : Reach 242963 := rs (se 1 (by rfl) ⟨182222, by rfl⟩) R364445
theorem R341309 : Reach 341309 := rs (se 3 (by rfl) ⟨63995, by rfl⟩) R127991
theorem R308609 : Reach 308609 := rs (se 2 (by rfl) ⟨115728, by rfl⟩) R231457
theorem R177967 : Reach 177967 := rs (se 1 (by rfl) ⟨133475, by rfl⟩) R266951
theorem R309187 : Reach 309187 := rs (se 1 (by rfl) ⟨231890, by rfl⟩) R463781
theorem R440749 : Reach 440749 := rs (se 3 (by rfl) ⟨82640, by rfl⟩) R165281
theorem R245339 : Reach 245339 := rs (se 1 (by rfl) ⟨184004, by rfl⟩) R368009
theorem R147035 : Reach 147035 := rs (se 1 (by rfl) ⟨110276, by rfl⟩) R220553
theorem R311435 : Reach 311435 := rs (se 1 (by rfl) ⟨233576, by rfl⟩) R467153
theorem R246311 : Reach 246311 := rs (se 1 (by rfl) ⟨184733, by rfl⟩) R369467
theorem R82697 : Reach 82697 := rs (se 2 (by rfl) ⟨31011, by rfl⟩) R62023
theorem R82799 : Reach 82799 := rs (se 1 (by rfl) ⟨62099, by rfl⟩) R124199
theorem R279611 : Reach 279611 := rs (se 1 (by rfl) ⟨209708, by rfl⟩) R419417
theorem R476219 : Reach 476219 := rs (se 1 (by rfl) ⟨357164, by rfl⟩) R714329
theorem R83051 : Reach 83051 := rs (se 1 (by rfl) ⟨62288, by rfl⟩) R124577
theorem R279773 : Reach 279773 := rs (se 3 (by rfl) ⟨52457, by rfl⟩) R104915
theorem R83291 : Reach 83291 := rs (se 1 (by rfl) ⟨62468, by rfl⟩) R124937
theorem R378283 : Reach 378283 := rs (se 1 (by rfl) ⟨283712, by rfl⟩) R567425
theorem R181775 : Reach 181775 := rs (se 1 (by rfl) ⟨136331, by rfl⟩) R272663
theorem R83567 : Reach 83567 := rs (se 1 (by rfl) ⟨62675, by rfl⟩) R125351
theorem R83639 : Reach 83639 := rs (se 1 (by rfl) ⟨62729, by rfl⟩) R125459
theorem R83675 : Reach 83675 := rs (se 1 (by rfl) ⟨62756, by rfl⟩) R125513
theorem R214751 : Reach 214751 := rs (se 1 (by rfl) ⟨161063, by rfl⟩) R322127
theorem R83849 : Reach 83849 := rs (se 2 (by rfl) ⟨31443, by rfl⟩) R62887
theorem R83951 : Reach 83951 := rs (se 1 (by rfl) ⟨62963, by rfl⟩) R125927
theorem R84203 : Reach 84203 := rs (se 1 (by rfl) ⟨63152, by rfl⟩) R126305
theorem R84263 : Reach 84263 := rs (se 1 (by rfl) ⟨63197, by rfl⟩) R126395
theorem R84347 : Reach 84347 := rs (se 1 (by rfl) ⟨63260, by rfl⟩) R126521
theorem R84617 : Reach 84617 := rs (se 2 (by rfl) ⟨31731, by rfl⟩) R63463
theorem R215723 : Reach 215723 := rs (se 1 (by rfl) ⟨161792, by rfl⟩) R323585
theorem R84791 : Reach 84791 := rs (se 1 (by rfl) ⟨63593, by rfl⟩) R127187
theorem R84827 : Reach 84827 := rs (se 1 (by rfl) ⟨63620, by rfl⟩) R127241
theorem R805727 : Reach 805727 := rs (se 1 (by rfl) ⟨604295, by rfl⟩) R1208591
theorem R84971 : Reach 84971 := rs (se 1 (by rfl) ⟨63728, by rfl⟩) R127457
theorem R85175 : Reach 85175 := rs (se 1 (by rfl) ⟨63881, by rfl⟩) R127763
theorem R85415 : Reach 85415 := rs (se 1 (by rfl) ⟨64061, by rfl⟩) R128123
theorem R183799 : Reach 183799 := rs (se 1 (by rfl) ⟨137849, by rfl⟩) R275699
theorem R85499 : Reach 85499 := rs (se 1 (by rfl) ⟨64124, by rfl⟩) R128249
theorem R85595 : Reach 85595 := rs (se 1 (by rfl) ⟨64196, by rfl⟩) R128393
theorem R85679 : Reach 85679 := rs (se 1 (by rfl) ⟨64259, by rfl⟩) R128519
theorem R446147 : Reach 446147 := rs (se 1 (by rfl) ⟨334610, by rfl⟩) R669221
theorem R85799 : Reach 85799 := rs (se 1 (by rfl) ⟨64349, by rfl⟩) R128699
theorem R85883 : Reach 85883 := rs (se 1 (by rfl) ⟨64412, by rfl⟩) R128825
theorem R642977 : Reach 642977 := rs (se 2 (by rfl) ⟨241116, by rfl⟩) R482233
theorem R315373 : Reach 315373 := rs (se 3 (by rfl) ⟨59132, by rfl⟩) R118265
theorem R86303 : Reach 86303 := rs (se 1 (by rfl) ⟨64727, by rfl⟩) R129455
theorem R1724723 : Reach 1724723 := rs (se 1 (by rfl) ⟨1293542, by rfl⟩) R2587085
theorem R86327 : Reach 86327 := rs (se 1 (by rfl) ⟨64745, by rfl⟩) R129491
theorem R86399 : Reach 86399 := rs (se 1 (by rfl) ⟨64799, by rfl⟩) R129599
theorem R86471 : Reach 86471 := rs (se 1 (by rfl) ⟨64853, by rfl⟩) R129707
theorem R86825 : Reach 86825 := rs (se 2 (by rfl) ⟨32559, by rfl⟩) R65119
theorem R86831 : Reach 86831 := rs (se 1 (by rfl) ⟨65123, by rfl⟩) R130247
theorem R250685 : Reach 250685 := rs (se 3 (by rfl) ⟨47003, by rfl⟩) R94007
theorem R86951 : Reach 86951 := rs (se 1 (by rfl) ⟨65213, by rfl⟩) R130427
theorem R87035 : Reach 87035 := rs (se 1 (by rfl) ⟨65276, by rfl⟩) R130553
theorem R87095 : Reach 87095 := rs (se 1 (by rfl) ⟨65321, by rfl⟩) R130643
theorem R87113 : Reach 87113 := rs (se 2 (by rfl) ⟨32667, by rfl⟩) R65335
theorem R283823 : Reach 283823 := rs (se 1 (by rfl) ⟨212867, by rfl⟩) R425735
theorem R87215 : Reach 87215 := rs (se 1 (by rfl) ⟨65411, by rfl⟩) R130823
theorem R218321 : Reach 218321 := rs (se 2 (by rfl) ⟨81870, by rfl⟩) R163741
theorem R87467 : Reach 87467 := rs (se 1 (by rfl) ⟨65600, by rfl⟩) R131201
theorem R87623 : Reach 87623 := rs (se 1 (by rfl) ⟨65717, by rfl⟩) R131435
theorem R87719 : Reach 87719 := rs (se 1 (by rfl) ⟨65789, by rfl⟩) R131579
theorem R87803 : Reach 87803 := rs (se 1 (by rfl) ⟨65852, by rfl⟩) R131705
theorem R87839 : Reach 87839 := rs (se 1 (by rfl) ⟨65879, by rfl⟩) R131759
theorem R87887 : Reach 87887 := rs (se 1 (by rfl) ⟨65915, by rfl⟩) R131831
theorem R88007 : Reach 88007 := rs (se 1 (by rfl) ⟨66005, by rfl⟩) R132011
theorem R219095 : Reach 219095 := rs (se 1 (by rfl) ⟨164321, by rfl⟩) R328643
theorem R55279 : Reach 55279 := rs (se 1 (by rfl) ⟨41459, by rfl⟩) R82919
theorem R88055 : Reach 88055 := rs (se 1 (by rfl) ⟨66041, by rfl⟩) R132083
theorem R55451 : Reach 55451 := rs (se 1 (by rfl) ⟨41588, by rfl⟩) R83177
theorem R55487 : Reach 55487 := rs (se 1 (by rfl) ⟨41615, by rfl⟩) R83231
theorem R88361 : Reach 88361 := rs (se 2 (by rfl) ⟨33135, by rfl⟩) R66271
theorem R55599 : Reach 55599 := rs (se 1 (by rfl) ⟨41699, by rfl⟩) R83399
theorem R88367 : Reach 88367 := rs (se 1 (by rfl) ⟨66275, by rfl⟩) R132551
theorem R186731 : Reach 186731 := rs (se 1 (by rfl) ⟨140048, by rfl⟩) R280097
theorem R219581 : Reach 219581 := rs (se 3 (by rfl) ⟨41171, by rfl⟩) R82343
theorem R55835 : Reach 55835 := rs (se 1 (by rfl) ⟨41876, by rfl⟩) R83753
theorem R55839 : Reach 55839 := rs (se 1 (by rfl) ⟨41879, by rfl⟩) R83759
theorem R88607 : Reach 88607 := rs (se 1 (by rfl) ⟨66455, by rfl⟩) R132911
theorem R285281 : Reach 285281 := rs (se 2 (by rfl) ⟨106980, by rfl⟩) R213961
theorem R187001 : Reach 187001 := rs (se 2 (by rfl) ⟨70125, by rfl⟩) R140251
theorem R2939533 : Reach 2939533 := rs (se 3 (by rfl) ⟨551162, by rfl⟩) R1102325
theorem R56155 : Reach 56155 := rs (se 1 (by rfl) ⟨42116, by rfl⟩) R84233
theorem R56223 : Reach 56223 := rs (se 1 (by rfl) ⟨42167, by rfl⟩) R84335
theorem R187433 : Reach 187433 := rs (se 2 (by rfl) ⟨70287, by rfl⟩) R140575
theorem R56367 : Reach 56367 := rs (se 1 (by rfl) ⟨42275, by rfl⟩) R84551
theorem R56391 : Reach 56391 := rs (se 1 (by rfl) ⟨42293, by rfl⟩) R84587
theorem R482507 : Reach 482507 := rs (se 1 (by rfl) ⟨361880, by rfl⟩) R723761
theorem R56543 : Reach 56543 := rs (se 1 (by rfl) ⟨42407, by rfl⟩) R84815
theorem R351485 : Reach 351485 := rs (se 3 (by rfl) ⟨65903, by rfl⟩) R131807
theorem R318815 : Reach 318815 := rs (se 1 (by rfl) ⟨239111, by rfl⟩) R478223
theorem R286091 : Reach 286091 := rs (se 1 (by rfl) ⟨214568, by rfl⟩) R429137
theorem R56807 : Reach 56807 := rs (se 1 (by rfl) ⟨42605, by rfl⟩) R85211
theorem R187879 : Reach 187879 := rs (se 1 (by rfl) ⟨140909, by rfl⟩) R281819
theorem R2414551 : Reach 2414551 := rs (se 1 (by rfl) ⟨1810913, by rfl⟩) R3621827
theorem R220751 : Reach 220751 := rs (se 1 (by rfl) ⟨165563, by rfl⟩) R331127
theorem R1072723 : Reach 1072723 := rs (se 1 (by rfl) ⟨804542, by rfl⟩) R1609085
theorem R56923 : Reach 56923 := rs (se 1 (by rfl) ⟨42692, by rfl⟩) R85385
theorem R319211 : Reach 319211 := rs (se 1 (by rfl) ⟨239408, by rfl⟩) R478817
theorem R11951887 : Reach 11951887 := rs (se 1 (by rfl) ⟨8963915, by rfl⟩) R17927831
theorem R57159 : Reach 57159 := rs (se 1 (by rfl) ⟨42869, by rfl⟩) R85739
theorem R57311 : Reach 57311 := rs (se 1 (by rfl) ⟨42983, by rfl⟩) R85967
theorem R155687 : Reach 155687 := rs (se 1 (by rfl) ⟨116765, by rfl⟩) R233531
theorem R57575 : Reach 57575 := rs (se 1 (by rfl) ⟨43181, by rfl⟩) R86363
theorem R57727 : Reach 57727 := rs (se 1 (by rfl) ⟨43295, by rfl⟩) R86591
theorem R614789 : Reach 614789 := rs (se 4 (by rfl) ⟨57636, by rfl⟩) R115273
theorem R57807 : Reach 57807 := rs (se 1 (by rfl) ⟨43355, by rfl⟩) R86711
theorem R2777611 : Reach 2777611 := rs (se 1 (by rfl) ⟨2083208, by rfl⟩) R4166417
theorem R57959 : Reach 57959 := rs (se 1 (by rfl) ⟨43469, by rfl⟩) R86939
theorem R58223 : Reach 58223 := rs (se 1 (by rfl) ⟨43667, by rfl⟩) R87335
theorem R58279 : Reach 58279 := rs (se 1 (by rfl) ⟨43709, by rfl⟩) R87419
theorem R58363 : Reach 58363 := rs (se 1 (by rfl) ⟨43772, by rfl⟩) R87545
theorem R58431 : Reach 58431 := rs (se 1 (by rfl) ⟨43823, by rfl⟩) R87647
theorem R320669 : Reach 320669 := rs (se 3 (by rfl) ⟨60125, by rfl⟩) R120251
theorem R58543 : Reach 58543 := rs (se 1 (by rfl) ⟨43907, by rfl⟩) R87815
theorem R189647 : Reach 189647 := rs (se 1 (by rfl) ⟨142235, by rfl⟩) R284471
theorem R58575 : Reach 58575 := rs (se 1 (by rfl) ⟨43931, by rfl⟩) R87863
theorem R124267 : Reach 124267 := rs (se 1 (by rfl) ⟨93200, by rfl⟩) R186401
theorem R91547 : Reach 91547 := rs (se 1 (by rfl) ⟨68660, by rfl⟩) R137321
theorem R58779 : Reach 58779 := rs (se 1 (by rfl) ⟨44084, by rfl⟩) R88169
theorem R189971 : Reach 189971 := rs (se 1 (by rfl) ⟨142478, by rfl⟩) R284957
theorem R58991 : Reach 58991 := rs (se 1 (by rfl) ⟨44243, by rfl⟩) R88487
theorem R59047 : Reach 59047 := rs (se 1 (by rfl) ⟨44285, by rfl⟩) R88571
theorem R59099 : Reach 59099 := rs (se 1 (by rfl) ⟨44324, by rfl⟩) R88649
theorem R222983 : Reach 222983 := rs (se 1 (by rfl) ⟨167237, by rfl⟩) R334475
theorem R124703 : Reach 124703 := rs (se 1 (by rfl) ⟨93527, by rfl⟩) R187055
theorem R321353 : Reach 321353 := rs (se 2 (by rfl) ⟨120507, by rfl⟩) R241015
theorem R124919 : Reach 124919 := rs (se 1 (by rfl) ⟨93689, by rfl⟩) R187379
theorem R125279 : Reach 125279 := rs (se 1 (by rfl) ⟨93959, by rfl⟩) R187919
theorem R420389 : Reach 420389 := rs (se 4 (by rfl) ⟨39411, by rfl⟩) R78823
theorem R354887 : Reach 354887 := rs (se 1 (by rfl) ⟨266165, by rfl⟩) R532331
theorem R191159 : Reach 191159 := rs (se 1 (by rfl) ⟨143369, by rfl⟩) R286739
theorem R93163 : Reach 93163 := rs (se 1 (by rfl) ⟨69872, by rfl⟩) R139745
theorem R125999 : Reach 125999 := rs (se 1 (by rfl) ⟨94499, by rfl⟩) R188999
theorem R93305 : Reach 93305 := rs (se 2 (by rfl) ⟨34989, by rfl⟩) R69979
theorem R126287 : Reach 126287 := rs (se 1 (by rfl) ⟨94715, by rfl⟩) R189431
theorem R126377 : Reach 126377 := rs (se 2 (by rfl) ⟨47391, by rfl⟩) R94783
theorem R323129 : Reach 323129 := rs (se 2 (by rfl) ⟨121173, by rfl⟩) R242347
theorem R355913 : Reach 355913 := rs (se 2 (by rfl) ⟨133467, by rfl⟩) R266935
theorem R650915 : Reach 650915 := rs (se 1 (by rfl) ⟨488186, by rfl⟩) R976373
theorem R126863 : Reach 126863 := rs (se 1 (by rfl) ⟨95147, by rfl⟩) R190295
theorem R94439 : Reach 94439 := rs (se 1 (by rfl) ⟨70829, by rfl⟩) R141659
theorem R94601 : Reach 94601 := rs (se 2 (by rfl) ⟨35475, by rfl⟩) R70951
theorem R193103 : Reach 193103 := rs (se 1 (by rfl) ⟨144827, by rfl⟩) R289655
theorem R127583 : Reach 127583 := rs (se 1 (by rfl) ⟨95687, by rfl⟩) R191375
theorem R95033 : Reach 95033 := rs (se 2 (by rfl) ⟨35637, by rfl⟩) R71275
theorem R1078109 : Reach 1078109 := rs (se 3 (by rfl) ⟨202145, by rfl⟩) R404291
theorem R95087 : Reach 95087 := rs (se 1 (by rfl) ⟨71315, by rfl⟩) R142631
theorem R848933 : Reach 848933 := rs (se 4 (by rfl) ⟨79587, by rfl⟩) R159175
theorem R62527 : Reach 62527 := rs (se 1 (by rfl) ⟨46895, by rfl⟩) R93791
theorem R95305 : Reach 95305 := rs (se 2 (by rfl) ⟨35739, by rfl⟩) R71479
theorem R193643 : Reach 193643 := rs (se 1 (by rfl) ⟨145232, by rfl⟩) R290465
theorem R95407 : Reach 95407 := rs (se 1 (by rfl) ⟨71555, by rfl⟩) R143111
theorem R62671 : Reach 62671 := rs (se 1 (by rfl) ⟨47003, by rfl⟩) R94007
theorem R128411 : Reach 128411 := rs (se 1 (by rfl) ⟨96308, by rfl⟩) R192617
theorem R292295 : Reach 292295 := rs (se 1 (by rfl) ⟨219221, by rfl⟩) R438443
theorem R96079 : Reach 96079 := rs (se 1 (by rfl) ⟨72059, by rfl⟩) R144119
theorem R128987 : Reach 128987 := rs (se 1 (by rfl) ⟨96740, by rfl⟩) R193481
theorem R129167 : Reach 129167 := rs (se 1 (by rfl) ⟨96875, by rfl⟩) R193751
theorem R63643 : Reach 63643 := rs (se 1 (by rfl) ⟨47732, by rfl⟩) R95465
theorem R129185 : Reach 129185 := rs (se 2 (by rfl) ⟨48444, by rfl⟩) R96889
theorem R63679 : Reach 63679 := rs (se 1 (by rfl) ⟨47759, by rfl⟩) R95519
theorem R129257 : Reach 129257 := rs (se 2 (by rfl) ⟨48471, by rfl⟩) R96943
theorem R96491 : Reach 96491 := rs (se 1 (by rfl) ⟨72368, by rfl⟩) R144737
theorem R522557 : Reach 522557 := rs (se 3 (by rfl) ⟨97979, by rfl⟩) R195959
theorem R194939 : Reach 194939 := rs (se 1 (by rfl) ⟨146204, by rfl⟩) R292409
theorem R1243673 : Reach 1243673 := rs (se 2 (by rfl) ⟨466377, by rfl⟩) R932755
theorem R195209 : Reach 195209 := rs (se 2 (by rfl) ⟨73203, by rfl⟩) R146407
theorem R719513 : Reach 719513 := rs (se 2 (by rfl) ⟨269817, by rfl⟩) R539635
theorem R97321 : Reach 97321 := rs (se 2 (by rfl) ⟨36495, by rfl⟩) R72991
theorem R97463 : Reach 97463 := rs (se 1 (by rfl) ⟨73097, by rfl⟩) R146195
theorem R130535 : Reach 130535 := rs (se 1 (by rfl) ⟨97901, by rfl⟩) R195803
theorem R97787 : Reach 97787 := rs (se 1 (by rfl) ⟨73340, by rfl⟩) R146681
theorem R196343 : Reach 196343 := rs (se 1 (by rfl) ⟨147257, by rfl⟩) R294515
theorem R98219 : Reach 98219 := rs (se 1 (by rfl) ⟨73664, by rfl⟩) R147329
theorem R65839 : Reach 65839 := rs (se 1 (by rfl) ⟨49379, by rfl⟩) R98759
theorem R164207 : Reach 164207 := rs (se 1 (by rfl) ⟨123155, by rfl⟩) R246311
theorem R196991 : Reach 196991 := rs (se 1 (by rfl) ⟨147743, by rfl⟩) R295487
theorem R459179 : Reach 459179 := rs (se 1 (by rfl) ⟨344384, by rfl⟩) R688769
theorem R131543 : Reach 131543 := rs (se 1 (by rfl) ⟨98657, by rfl⟩) R197315
theorem R131615 : Reach 131615 := rs (se 1 (by rfl) ⟨98711, by rfl⟩) R197423
theorem R131687 : Reach 131687 := rs (se 1 (by rfl) ⟨98765, by rfl⟩) R197531
theorem R98921 : Reach 98921 := rs (se 2 (by rfl) ⟨37095, by rfl⟩) R74191
theorem R3703481 : Reach 3703481 := rs (se 2 (by rfl) ⟨1388805, by rfl⟩) R2777611
theorem R262909 : Reach 262909 := rs (se 3 (by rfl) ⟨49295, by rfl⟩) R98591
theorem R131881 : Reach 131881 := rs (se 2 (by rfl) ⟨49455, by rfl⟩) R98911
theorem R197855 : Reach 197855 := rs (se 1 (by rfl) ⟨148391, by rfl⟩) R296783
theorem R66863 : Reach 66863 := rs (se 1 (by rfl) ⟨50147, by rfl⟩) R100295
theorem R132443 : Reach 132443 := rs (se 1 (by rfl) ⟨99332, by rfl⟩) R198665
theorem R132713 : Reach 132713 := rs (se 2 (by rfl) ⟨49767, by rfl⟩) R99535
theorem R919259 : Reach 919259 := rs (se 1 (by rfl) ⟨689444, by rfl⟩) R1378889
theorem R165689 : Reach 165689 := rs (se 2 (by rfl) ⟨62133, by rfl⟩) R124267
theorem R3180869 : Reach 3180869 := rs (se 4 (by rfl) ⟨298206, by rfl⟩) R596413
theorem R297431 : Reach 297431 := rs (se 1 (by rfl) ⟨223073, by rfl⟩) R446147
theorem R428651 : Reach 428651 := rs (se 1 (by rfl) ⟨321488, by rfl⟩) R642977
theorem R133769 : Reach 133769 := rs (se 2 (by rfl) ⟨50163, by rfl⟩) R100327
theorem R1149815 : Reach 1149815 := rs (se 1 (by rfl) ⟨862361, by rfl⟩) R1724723
theorem R1051697 : Reach 1051697 := rs (se 2 (by rfl) ⟨394386, by rfl⟩) R788773
theorem R134207 : Reach 134207 := rs (se 1 (by rfl) ⟨100655, by rfl⟩) R201311
theorem R167123 : Reach 167123 := rs (se 1 (by rfl) ⟨125342, by rfl⟩) R250685
theorem R201079 : Reach 201079 := rs (se 1 (by rfl) ⟨150809, by rfl⟩) R301619
theorem R528977 : Reach 528977 := rs (se 2 (by rfl) ⟨198366, by rfl⟩) R396733
theorem R234323 : Reach 234323 := rs (se 1 (by rfl) ⟨175742, by rfl⟩) R351485
theorem R464237 : Reach 464237 := rs (se 3 (by rfl) ⟨87044, by rfl⟩) R174089
theorem R235217 : Reach 235217 := rs (se 2 (by rfl) ⟨88206, by rfl⟩) R176413
theorem R235361 : Reach 235361 := rs (se 2 (by rfl) ⟨88260, by rfl⟩) R176521
theorem R1513363 : Reach 1513363 := rs (se 1 (by rfl) ⟨1135022, by rfl⟩) R2270045
theorem R203239 : Reach 203239 := rs (se 1 (by rfl) ⟨152429, by rfl⟩) R304859
theorem R72571 : Reach 72571 := rs (se 1 (by rfl) ⟨54428, by rfl⟩) R108857
theorem R236591 : Reach 236591 := rs (se 1 (by rfl) ⟨177443, by rfl⟩) R354887
theorem R269639 : Reach 269639 := rs (se 1 (by rfl) ⟨202229, by rfl⟩) R404459
theorem R237275 : Reach 237275 := rs (se 1 (by rfl) ⟨177956, by rfl⟩) R355913
theorem R1056503 : Reach 1056503 := rs (se 1 (by rfl) ⟨792377, by rfl⟩) R1584755
theorem R433943 : Reach 433943 := rs (se 1 (by rfl) ⟨325457, by rfl⟩) R650915
theorem R3219401 : Reach 3219401 := rs (se 2 (by rfl) ⟨1207275, by rfl⟩) R2414551
theorem R73705 : Reach 73705 := rs (se 2 (by rfl) ⟨27639, by rfl⟩) R55279
theorem R368749 : Reach 368749 := rs (se 3 (by rfl) ⟨69140, by rfl⟩) R138281
theorem R565955 : Reach 565955 := rs (se 1 (by rfl) ⟨424466, by rfl⟩) R848933
theorem R74459 : Reach 74459 := rs (se 1 (by rfl) ⟨55844, by rfl⟩) R111689
theorem R140039 : Reach 140039 := rs (se 1 (by rfl) ⟨105029, by rfl⟩) R210059
theorem R205739 : Reach 205739 := rs (se 1 (by rfl) ⟨154304, by rfl⟩) R308609
theorem R829115 : Reach 829115 := rs (se 1 (by rfl) ⟨621836, by rfl⟩) R1243673
theorem R1648997 : Reach 1648997 := rs (se 4 (by rfl) ⟨154593, by rfl⟩) R309187
theorem R15935849 : Reach 15935849 := rs (se 2 (by rfl) ⟨5975943, by rfl⟩) R11951887
theorem R207623 : Reach 207623 := rs (se 1 (by rfl) ⟨155717, by rfl⟩) R311435
theorem R143167 : Reach 143167 := rs (se 1 (by rfl) ⟨107375, by rfl⟩) R214751
theorem R143815 : Reach 143815 := rs (se 1 (by rfl) ⟨107861, by rfl⟩) R215723
theorem R504377 : Reach 504377 := rs (se 2 (by rfl) ⟨189141, by rfl⟩) R378283
theorem R373567 : Reach 373567 := rs (se 1 (by rfl) ⟨280175, by rfl⟩) R560351
theorem R308087 : Reach 308087 := rs (se 1 (by rfl) ⟨231065, by rfl⟩) R462131
theorem R308279 : Reach 308279 := rs (se 1 (by rfl) ⟨231209, by rfl⟩) R462419
theorem R177481 : Reach 177481 := rs (se 2 (by rfl) ⟨66555, by rfl⟩) R133111
theorem R636797 : Reach 636797 := rs (se 3 (by rfl) ⟨119399, by rfl⟩) R238799
theorem R15677509 : Reach 15677509 := rs (se 4 (by rfl) ⟨1469766, by rfl⟩) R2939533
theorem R145547 : Reach 145547 := rs (se 1 (by rfl) ⟨109160, by rfl⟩) R218321
theorem R506087 : Reach 506087 := rs (se 1 (by rfl) ⟨379565, by rfl⟩) R759131
theorem R146063 : Reach 146063 := rs (se 1 (by rfl) ⟨109547, by rfl⟩) R219095
theorem R146387 : Reach 146387 := rs (se 1 (by rfl) ⟨109790, by rfl⟩) R219581
theorem R245065 : Reach 245065 := rs (se 2 (by rfl) ⟨91899, by rfl⟩) R183799
theorem R146857 : Reach 146857 := rs (se 2 (by rfl) ⟨55071, by rfl⟩) R110143
theorem R2866747 : Reach 2866747 := rs (se 1 (by rfl) ⟨2150060, by rfl⟩) R4300121
theorem R212543 : Reach 212543 := rs (se 1 (by rfl) ⟨159407, by rfl⟩) R318815
theorem R310873 : Reach 310873 := rs (se 2 (by rfl) ⟨116577, by rfl⟩) R233155
theorem R147167 : Reach 147167 := rs (se 1 (by rfl) ⟨110375, by rfl⟩) R220751
theorem R212807 : Reach 212807 := rs (se 1 (by rfl) ⟨159605, by rfl⟩) R319211
theorem R409859 : Reach 409859 := rs (se 1 (by rfl) ⟨307394, by rfl⟩) R614789
theorem R213779 : Reach 213779 := rs (se 1 (by rfl) ⟨160334, by rfl⟩) R320669
theorem R508837 : Reach 508837 := rs (se 4 (by rfl) ⟨47703, by rfl⟩) R95407
theorem R148655 : Reach 148655 := rs (se 1 (by rfl) ⟨111491, by rfl⟩) R222983
theorem R83135 : Reach 83135 := rs (se 1 (by rfl) ⟨62351, by rfl⟩) R124703
theorem R214235 : Reach 214235 := rs (se 1 (by rfl) ⟨160676, by rfl⟩) R321353
theorem R83279 : Reach 83279 := rs (se 1 (by rfl) ⟨62459, by rfl⟩) R124919
theorem R378269 : Reach 378269 := rs (se 3 (by rfl) ⟨70925, by rfl⟩) R141851
theorem R83369 : Reach 83369 := rs (se 2 (by rfl) ⟨31263, by rfl⟩) R62527
theorem R83519 : Reach 83519 := rs (se 1 (by rfl) ⟨62639, by rfl⟩) R125279
theorem R83561 : Reach 83561 := rs (se 2 (by rfl) ⟨31335, by rfl⟩) R62671
theorem R280259 : Reach 280259 := rs (se 1 (by rfl) ⟨210194, by rfl⟩) R420389
theorem R83999 : Reach 83999 := rs (se 1 (by rfl) ⟨62999, by rfl⟩) R125999
theorem R575687 : Reach 575687 := rs (se 1 (by rfl) ⟨431765, by rfl⟩) R863531
theorem R84191 : Reach 84191 := rs (se 1 (by rfl) ⟨63143, by rfl⟩) R126287
theorem R2148605 : Reach 2148605 := rs (se 3 (by rfl) ⟨402863, by rfl⟩) R805727
theorem R84251 : Reach 84251 := rs (se 1 (by rfl) ⟨63188, by rfl⟩) R126377
theorem R510299 : Reach 510299 := rs (se 1 (by rfl) ⟨382724, by rfl⟩) R765449
theorem R215419 : Reach 215419 := rs (se 1 (by rfl) ⟨161564, by rfl⟩) R323129
theorem R117119 : Reach 117119 := rs (se 1 (by rfl) ⟨87839, by rfl⟩) R175679
theorem R84575 : Reach 84575 := rs (se 1 (by rfl) ⟨63431, by rfl⟩) R126863
theorem R84857 : Reach 84857 := rs (se 2 (by rfl) ⟨31821, by rfl⟩) R63643
theorem R84905 : Reach 84905 := rs (se 2 (by rfl) ⟨31839, by rfl⟩) R63679
theorem R85055 : Reach 85055 := rs (se 1 (by rfl) ⟨63791, by rfl⟩) R127583
theorem R1035767 : Reach 1035767 := rs (se 1 (by rfl) ⟨776825, by rfl⟩) R1553651
theorem R85607 : Reach 85607 := rs (se 1 (by rfl) ⟨64205, by rfl⟩) R128411
theorem R85991 : Reach 85991 := rs (se 1 (by rfl) ⟨64493, by rfl⟩) R128987
theorem R86111 : Reach 86111 := rs (se 1 (by rfl) ⟨64583, by rfl⟩) R129167
theorem R86123 : Reach 86123 := rs (se 1 (by rfl) ⟨64592, by rfl⟩) R129185
theorem R86171 : Reach 86171 := rs (se 1 (by rfl) ⟨64628, by rfl⟩) R129257
theorem R348371 : Reach 348371 := rs (se 1 (by rfl) ⟨261278, by rfl⟩) R522557
theorem R479675 : Reach 479675 := rs (se 1 (by rfl) ⟨359756, by rfl⟩) R719513
theorem R250505 : Reach 250505 := rs (se 2 (by rfl) ⟨93939, by rfl⟩) R187879
theorem R1430297 : Reach 1430297 := rs (se 2 (by rfl) ⟨536361, by rfl⟩) R1072723
theorem R87023 : Reach 87023 := rs (se 1 (by rfl) ⟨65267, by rfl⟩) R130535
theorem R87407 : Reach 87407 := rs (se 1 (by rfl) ⟨65555, by rfl⟩) R131111
theorem R415165 : Reach 415165 := rs (se 3 (by rfl) ⟨77843, by rfl⟩) R155687
theorem R87527 : Reach 87527 := rs (se 1 (by rfl) ⟨65645, by rfl⟩) R131291
theorem R218639 : Reach 218639 := rs (se 1 (by rfl) ⟨163979, by rfl⟩) R327959
theorem R87689 : Reach 87689 := rs (se 2 (by rfl) ⟨32883, by rfl⟩) R65767
theorem R87707 : Reach 87707 := rs (se 1 (by rfl) ⟨65780, by rfl⟩) R131561
theorem R55131 : Reach 55131 := rs (se 1 (by rfl) ⟨41348, by rfl⟩) R82697
theorem R87899 : Reach 87899 := rs (se 1 (by rfl) ⟨65924, by rfl⟩) R131849
theorem R55199 : Reach 55199 := rs (se 1 (by rfl) ⟨41399, by rfl⟩) R82799
theorem R350171 : Reach 350171 := rs (se 1 (by rfl) ⟨262628, by rfl⟩) R525257
theorem R186407 : Reach 186407 := rs (se 1 (by rfl) ⟨139805, by rfl⟩) R279611
theorem R317479 : Reach 317479 := rs (se 1 (by rfl) ⟨238109, by rfl⟩) R476219
theorem R55367 : Reach 55367 := rs (se 1 (by rfl) ⟨41525, by rfl⟩) R83051
theorem R186515 : Reach 186515 := rs (se 1 (by rfl) ⟨139886, by rfl⟩) R279773
theorem R88283 : Reach 88283 := rs (se 1 (by rfl) ⟨66212, by rfl⟩) R132425
theorem R55527 : Reach 55527 := rs (se 1 (by rfl) ⟨41645, by rfl⟩) R83291
theorem R55711 : Reach 55711 := rs (se 1 (by rfl) ⟨41783, by rfl⟩) R83567
theorem R186785 : Reach 186785 := rs (se 2 (by rfl) ⟨70044, by rfl⟩) R140089
theorem R55759 : Reach 55759 := rs (se 1 (by rfl) ⟨41819, by rfl⟩) R83639
theorem R55783 : Reach 55783 := rs (se 1 (by rfl) ⟨41837, by rfl⟩) R83675
theorem R88553 : Reach 88553 := rs (se 2 (by rfl) ⟨33207, by rfl⟩) R66415
theorem R55899 : Reach 55899 := rs (se 1 (by rfl) ⟨41924, by rfl⟩) R83849
theorem R55967 : Reach 55967 := rs (se 1 (by rfl) ⟨41975, by rfl⟩) R83951
theorem R56135 : Reach 56135 := rs (se 1 (by rfl) ⟨42101, by rfl⟩) R84203
theorem R56175 : Reach 56175 := rs (se 1 (by rfl) ⟨42131, by rfl⟩) R84263
theorem R56231 : Reach 56231 := rs (se 1 (by rfl) ⟨42173, by rfl⟩) R84347
theorem R187325 : Reach 187325 := rs (se 3 (by rfl) ⟨35123, by rfl⟩) R70247
theorem R56411 : Reach 56411 := rs (se 1 (by rfl) ⟨42308, by rfl⟩) R84617
theorem R56527 : Reach 56527 := rs (se 1 (by rfl) ⟨42395, by rfl⟩) R84791
theorem R56551 : Reach 56551 := rs (se 1 (by rfl) ⟨42413, by rfl⟩) R84827
theorem R56647 : Reach 56647 := rs (se 1 (by rfl) ⟨42485, by rfl⟩) R84971
theorem R548207 : Reach 548207 := rs (se 1 (by rfl) ⟨411155, by rfl⟩) R822311
theorem R220583 : Reach 220583 := rs (se 1 (by rfl) ⟨165437, by rfl⟩) R330875
theorem R56783 : Reach 56783 := rs (se 1 (by rfl) ⟨42587, by rfl⟩) R85175
theorem R56943 : Reach 56943 := rs (se 1 (by rfl) ⟨42707, by rfl⟩) R85415
theorem R56999 : Reach 56999 := rs (se 1 (by rfl) ⟨42749, by rfl⟩) R85499
theorem R57063 : Reach 57063 := rs (se 1 (by rfl) ⟨42797, by rfl⟩) R85595
theorem R57119 : Reach 57119 := rs (se 1 (by rfl) ⟨42839, by rfl⟩) R85679
theorem R57199 : Reach 57199 := rs (se 1 (by rfl) ⟨42899, by rfl⟩) R85799
theorem R221039 : Reach 221039 := rs (se 1 (by rfl) ⟨165779, by rfl⟩) R331559
theorem R57255 : Reach 57255 := rs (se 1 (by rfl) ⟨42941, by rfl⟩) R85883
theorem R57535 : Reach 57535 := rs (se 1 (by rfl) ⟨43151, by rfl⟩) R86303
theorem R57551 : Reach 57551 := rs (se 1 (by rfl) ⟨43163, by rfl⟩) R86327
theorem R57599 : Reach 57599 := rs (se 1 (by rfl) ⟨43199, by rfl⟩) R86399
theorem R57647 : Reach 57647 := rs (se 1 (by rfl) ⟨43235, by rfl⟩) R86471
theorem R188729 : Reach 188729 := rs (se 2 (by rfl) ⟨70773, by rfl⟩) R141547
theorem R57883 : Reach 57883 := rs (se 1 (by rfl) ⟨43412, by rfl⟩) R86825
theorem R221723 : Reach 221723 := rs (se 1 (by rfl) ⟨166292, by rfl⟩) R332585
theorem R57887 : Reach 57887 := rs (se 1 (by rfl) ⟨43415, by rfl⟩) R86831
theorem R57967 : Reach 57967 := rs (se 1 (by rfl) ⟨43475, by rfl⟩) R86951
theorem R58023 : Reach 58023 := rs (se 1 (by rfl) ⟨43517, by rfl⟩) R87035
theorem R58063 : Reach 58063 := rs (se 1 (by rfl) ⟨43547, by rfl⟩) R87095
theorem R58075 : Reach 58075 := rs (se 1 (by rfl) ⟨43556, by rfl⟩) R87113
theorem R189215 : Reach 189215 := rs (se 1 (by rfl) ⟨141911, by rfl⟩) R283823
theorem R58143 : Reach 58143 := rs (se 1 (by rfl) ⟨43607, by rfl⟩) R87215
theorem R58311 : Reach 58311 := rs (se 1 (by rfl) ⟨43733, by rfl⟩) R87467
theorem R58415 : Reach 58415 := rs (se 1 (by rfl) ⟨43811, by rfl⟩) R87623
theorem R58479 : Reach 58479 := rs (se 1 (by rfl) ⟨43859, by rfl⟩) R87719
theorem R418931 : Reach 418931 := rs (se 1 (by rfl) ⟨314198, by rfl⟩) R628397
theorem R58535 : Reach 58535 := rs (se 1 (by rfl) ⟨43901, by rfl⟩) R87803
theorem R779453 : Reach 779453 := rs (se 3 (by rfl) ⟨146147, by rfl⟩) R292295
theorem R58559 : Reach 58559 := rs (se 1 (by rfl) ⟨43919, by rfl⟩) R87839
theorem R58591 : Reach 58591 := rs (se 1 (by rfl) ⟨43943, by rfl⟩) R87887
theorem R58671 : Reach 58671 := rs (se 1 (by rfl) ⟨44003, by rfl⟩) R88007
theorem R124217 : Reach 124217 := rs (se 2 (by rfl) ⟨46581, by rfl⟩) R93163
theorem R58703 : Reach 58703 := rs (se 1 (by rfl) ⟨44027, by rfl⟩) R88055
theorem R484733 : Reach 484733 := rs (se 3 (by rfl) ⟨90887, by rfl⟩) R181775
theorem R1598939 : Reach 1598939 := rs (se 1 (by rfl) ⟨1199204, by rfl⟩) R2398409
theorem R353819 : Reach 353819 := rs (se 1 (by rfl) ⟨265364, by rfl⟩) R530729
theorem R58907 : Reach 58907 := rs (se 1 (by rfl) ⟨44180, by rfl⟩) R88361
theorem R58911 : Reach 58911 := rs (se 1 (by rfl) ⟨44183, by rfl⟩) R88367
theorem R124487 : Reach 124487 := rs (se 1 (by rfl) ⟨93365, by rfl⟩) R186731
theorem R1926737 : Reach 1926737 := rs (se 2 (by rfl) ⟨722526, by rfl⟩) R1445053
theorem R59071 : Reach 59071 := rs (se 1 (by rfl) ⟨44303, by rfl⟩) R88607
theorem R190187 : Reach 190187 := rs (se 1 (by rfl) ⟨142640, by rfl⟩) R285281
theorem R124667 : Reach 124667 := rs (se 1 (by rfl) ⟨93500, by rfl⟩) R187001
theorem R92059 : Reach 92059 := rs (se 1 (by rfl) ⟨69044, by rfl⟩) R138089
theorem R223195 : Reach 223195 := rs (se 1 (by rfl) ⟨167396, by rfl⟩) R334793
theorem R190457 : Reach 190457 := rs (se 2 (by rfl) ⟨71421, by rfl⟩) R142843
theorem R124955 : Reach 124955 := rs (se 1 (by rfl) ⟨93716, by rfl⟩) R187433
theorem R321671 : Reach 321671 := rs (se 1 (by rfl) ⟨241253, by rfl⟩) R482507
theorem R190727 : Reach 190727 := rs (se 1 (by rfl) ⟨143045, by rfl⟩) R286091
theorem R420497 : Reach 420497 := rs (se 2 (by rfl) ⟨157686, by rfl⟩) R315373
theorem R93595 : Reach 93595 := rs (se 1 (by rfl) ⟨70196, by rfl⟩) R140393
theorem R126431 : Reach 126431 := rs (se 1 (by rfl) ⟨94823, by rfl⟩) R189647
theorem R61031 : Reach 61031 := rs (se 1 (by rfl) ⟨45773, by rfl⟩) R91547
theorem R126647 : Reach 126647 := rs (se 1 (by rfl) ⟨94985, by rfl⟩) R189971
theorem R356345 : Reach 356345 := rs (se 2 (by rfl) ⟨133629, by rfl⟩) R267259
theorem R127073 : Reach 127073 := rs (se 2 (by rfl) ⟨47652, by rfl⟩) R95305
theorem R94351 : Reach 94351 := rs (se 1 (by rfl) ⟨70763, by rfl⟩) R141527
theorem R487705 : Reach 487705 := rs (se 2 (by rfl) ⟨182889, by rfl⟩) R365779
theorem R94567 : Reach 94567 := rs (se 1 (by rfl) ⟨70925, by rfl⟩) R141851
theorem R127439 : Reach 127439 := rs (se 1 (by rfl) ⟨95579, by rfl⟩) R191159
theorem R62203 : Reach 62203 := rs (se 1 (by rfl) ⟨46652, by rfl⟩) R93305
theorem R95303 : Reach 95303 := rs (se 1 (by rfl) ⟨71477, by rfl⟩) R142955
theorem R128105 : Reach 128105 := rs (se 2 (by rfl) ⟨48039, by rfl⟩) R96079
theorem R62959 : Reach 62959 := rs (se 1 (by rfl) ⟨47219, by rfl⟩) R94439
theorem R63067 : Reach 63067 := rs (se 1 (by rfl) ⟨47300, by rfl⟩) R94601
theorem R128735 : Reach 128735 := rs (se 1 (by rfl) ⟨96551, by rfl⟩) R193103
theorem R63355 : Reach 63355 := rs (se 1 (by rfl) ⟨47516, by rfl⟩) R95033
theorem R587665 : Reach 587665 := rs (se 2 (by rfl) ⟨220374, by rfl⟩) R440749
theorem R718739 : Reach 718739 := rs (se 1 (by rfl) ⟨539054, by rfl⟩) R1078109
theorem R63391 : Reach 63391 := rs (se 1 (by rfl) ⟨47543, by rfl⟩) R95087
theorem R129095 : Reach 129095 := rs (se 1 (by rfl) ⟨96821, by rfl⟩) R193643
theorem R2717873 : Reach 2717873 := rs (se 2 (by rfl) ⟨1019202, by rfl⟩) R2038405
theorem R161975 : Reach 161975 := rs (se 1 (by rfl) ⟨121481, by rfl⟩) R242963
theorem R227539 : Reach 227539 := rs (se 1 (by rfl) ⟨170654, by rfl⟩) R341309
theorem R129761 : Reach 129761 := rs (se 2 (by rfl) ⟨48660, by rfl⟩) R97321
theorem R64327 : Reach 64327 := rs (se 1 (by rfl) ⟨48245, by rfl⟩) R96491
theorem R949157 : Reach 949157 := rs (se 4 (by rfl) ⟨88983, by rfl⟩) R177967
theorem R129959 : Reach 129959 := rs (se 1 (by rfl) ⟨97469, by rfl⟩) R194939
theorem R130139 : Reach 130139 := rs (se 1 (by rfl) ⟨97604, by rfl⟩) R195209
theorem R64975 : Reach 64975 := rs (se 1 (by rfl) ⟨48731, by rfl⟩) R97463
theorem R65191 : Reach 65191 := rs (se 1 (by rfl) ⟨48893, by rfl⟩) R97787
theorem R163559 : Reach 163559 := rs (se 1 (by rfl) ⟨122669, by rfl⟩) R245339
theorem R98023 : Reach 98023 := rs (se 1 (by rfl) ⟨73517, by rfl⟩) R147035
theorem R98057 : Reach 98057 := rs (se 2 (by rfl) ⟨36771, by rfl⟩) R73543
theorem R130895 : Reach 130895 := rs (se 1 (by rfl) ⟨98171, by rfl⟩) R196343
theorem R65479 : Reach 65479 := rs (se 1 (by rfl) ⟨49109, by rfl⟩) R98219
theorem R491665 : Reach 491665 := rs (se 2 (by rfl) ⟨184374, by rfl⟩) R368749
theorem R131327 : Reach 131327 := rs (se 1 (by rfl) ⟨98495, by rfl⟩) R196991
theorem R65947 : Reach 65947 := rs (se 1 (by rfl) ⟨49460, by rfl⟩) R98921
theorem R99103 : Reach 99103 := rs (se 1 (by rfl) ⟨74327, by rfl⟩) R148655
theorem R131903 : Reach 131903 := rs (se 1 (by rfl) ⟨98927, by rfl⟩) R197855
theorem R1410605 : Reach 1410605 := rs (se 3 (by rfl) ⟨264488, by rfl⟩) R528977
theorem R198287 : Reach 198287 := rs (se 1 (by rfl) ⟨148715, by rfl⟩) R297431
theorem R198557 : Reach 198557 := rs (se 3 (by rfl) ⟨37229, by rfl⟩) R74459
theorem R1083941 : Reach 1083941 := rs (se 4 (by rfl) ⟨101619, by rfl⟩) R203239
theorem R297593 : Reach 297593 := rs (se 2 (by rfl) ⟨111597, by rfl⟩) R223195
theorem R232247 : Reach 232247 := rs (se 1 (by rfl) ⟨174185, by rfl⟩) R348371
theorem R167003 : Reach 167003 := rs (se 1 (by rfl) ⟨125252, by rfl⟩) R250505
theorem R953531 : Reach 953531 := rs (se 1 (by rfl) ⟨715148, by rfl⟩) R1430297
theorem R233447 : Reach 233447 := rs (se 1 (by rfl) ⟨175085, by rfl⟩) R350171
theorem R365471 : Reach 365471 := rs (se 1 (by rfl) ⟨274103, by rfl⟩) R548207
theorem R268105 : Reach 268105 := rs (se 2 (by rfl) ⟨100539, by rfl⟩) R201079
theorem R137159 : Reach 137159 := rs (se 1 (by rfl) ⟨102869, by rfl⟩) R205739
theorem R235879 : Reach 235879 := rs (se 1 (by rfl) ⟨176909, by rfl⟩) R353819
theorem R1284491 : Reach 1284491 := rs (se 1 (by rfl) ⟨963368, by rfl⟩) R1926737
theorem R498089 : Reach 498089 := rs (se 2 (by rfl) ⟨186783, by rfl⟩) R373567
theorem R236141 : Reach 236141 := rs (se 3 (by rfl) ⟨44276, by rfl⟩) R88553
theorem R10623899 : Reach 10623899 := rs (se 1 (by rfl) ⟨7967924, by rfl⟩) R15935849
theorem R236641 : Reach 236641 := rs (se 2 (by rfl) ⟨88740, by rfl⟩) R177481
theorem R237563 : Reach 237563 := rs (se 1 (by rfl) ⟨178172, by rfl⟩) R356345
theorem R303385 : Reach 303385 := rs (se 2 (by rfl) ⟨113769, by rfl⟩) R227539
theorem R336251 : Reach 336251 := rs (se 1 (by rfl) ⟨252188, by rfl⟩) R504377
theorem R205391 : Reach 205391 := rs (se 1 (by rfl) ⟨154043, by rfl⟩) R308087
theorem R205519 : Reach 205519 := rs (se 1 (by rfl) ⟨154139, by rfl⟩) R308279
theorem R2762045 : Reach 2762045 := rs (se 3 (by rfl) ⟨517883, by rfl⟩) R1035767
theorem R1811915 : Reach 1811915 := rs (se 1 (by rfl) ⟨1358936, by rfl⟩) R2717873
theorem R107983 : Reach 107983 := rs (se 1 (by rfl) ⟨80987, by rfl⟩) R161975
theorem R337391 : Reach 337391 := rs (se 1 (by rfl) ⟨253043, by rfl⟩) R506087
theorem R632771 : Reach 632771 := rs (se 1 (by rfl) ⟨474578, by rfl⟩) R949157
theorem R141695 : Reach 141695 := rs (se 1 (by rfl) ⟨106271, by rfl⟩) R212543
theorem R109039 : Reach 109039 := rs (se 1 (by rfl) ⟨81779, by rfl⟩) R163559
theorem R141871 : Reach 141871 := rs (se 1 (by rfl) ⟨106403, by rfl⟩) R212807
theorem R273239 : Reach 273239 := rs (se 1 (by rfl) ⟨204929, by rfl⟩) R409859
theorem R306119 : Reach 306119 := rs (se 1 (by rfl) ⟨229589, by rfl⟩) R459179
theorem R2468987 : Reach 2468987 := rs (se 1 (by rfl) ⟨1851740, by rfl⟩) R3703481
theorem R142519 : Reach 142519 := rs (se 1 (by rfl) ⟨106889, by rfl⟩) R213779
theorem R142823 : Reach 142823 := rs (se 1 (by rfl) ⟨107117, by rfl⟩) R214235
theorem R437885 : Reach 437885 := rs (se 3 (by rfl) ⟨82103, by rfl⟩) R164207
theorem R175841 : Reach 175841 := rs (se 2 (by rfl) ⟨65940, by rfl⟩) R131881
theorem R110459 : Reach 110459 := rs (se 1 (by rfl) ⟨82844, by rfl⟩) R165689
theorem R340199 : Reach 340199 := rs (se 1 (by rfl) ⟨255149, by rfl⟩) R510299
theorem R78079 : Reach 78079 := rs (se 1 (by rfl) ⟨58559, by rfl⟩) R117119
theorem R701131 : Reach 701131 := rs (se 1 (by rfl) ⟨525848, by rfl⟩) R1051697
theorem R178301 : Reach 178301 := rs (se 3 (by rfl) ⟨33431, by rfl⟩) R66863
theorem R309491 : Reach 309491 := rs (se 1 (by rfl) ⟨232118, by rfl⟩) R464237
theorem R145759 : Reach 145759 := rs (se 1 (by rfl) ⟨109319, by rfl⟩) R218639
theorem R179759 : Reach 179759 := rs (se 1 (by rfl) ⟨134819, by rfl⟩) R269639
theorem R147055 : Reach 147055 := rs (se 1 (by rfl) ⟨110291, by rfl⟩) R220583
theorem R147197 : Reach 147197 := rs (se 3 (by rfl) ⟨27599, by rfl⟩) R55199
theorem R704335 : Reach 704335 := rs (se 1 (by rfl) ⟨528251, by rfl⟩) R1056503
theorem R147359 : Reach 147359 := rs (se 1 (by rfl) ⟨110519, by rfl⟩) R221039
theorem R2146267 : Reach 2146267 := rs (se 1 (by rfl) ⟨1609700, by rfl⟩) R3219401
theorem R147815 : Reach 147815 := rs (se 1 (by rfl) ⟨110861, by rfl⟩) R221723
theorem R377303 : Reach 377303 := rs (se 1 (by rfl) ⟨282977, by rfl⟩) R565955
theorem R279287 : Reach 279287 := rs (se 1 (by rfl) ⟨209465, by rfl⟩) R418931
theorem R82811 : Reach 82811 := rs (se 1 (by rfl) ⟨62108, by rfl⟩) R124217
theorem R1065959 : Reach 1065959 := rs (se 1 (by rfl) ⟨799469, by rfl⟩) R1598939
theorem R82937 : Reach 82937 := rs (se 2 (by rfl) ⟨31101, by rfl⟩) R62203
theorem R82991 : Reach 82991 := rs (se 1 (by rfl) ⟨62243, by rfl⟩) R124487
theorem R83111 : Reach 83111 := rs (se 1 (by rfl) ⟨62333, by rfl⟩) R124667
theorem R83303 : Reach 83303 := rs (se 1 (by rfl) ⟨62477, by rfl⟩) R124955
theorem R214447 : Reach 214447 := rs (se 1 (by rfl) ⟨160835, by rfl⟩) R321671
theorem R1099331 : Reach 1099331 := rs (se 1 (by rfl) ⟨824498, by rfl⟩) R1648997
theorem R280331 : Reach 280331 := rs (se 1 (by rfl) ⟨210248, by rfl⟩) R420497
theorem R83945 : Reach 83945 := rs (se 2 (by rfl) ⟨31479, by rfl⟩) R62959
theorem R84089 : Reach 84089 := rs (se 2 (by rfl) ⟨31533, by rfl⟩) R63067
theorem R3066173 : Reach 3066173 := rs (se 3 (by rfl) ⟨574907, by rfl⟩) R1149815
theorem R84287 : Reach 84287 := rs (se 1 (by rfl) ⟨63215, by rfl⟩) R126431
theorem R84431 : Reach 84431 := rs (se 1 (by rfl) ⟨63323, by rfl⟩) R126647
theorem R84473 : Reach 84473 := rs (se 2 (by rfl) ⟨31677, by rfl⟩) R63355
theorem R2017817 : Reach 2017817 := rs (se 2 (by rfl) ⟨756681, by rfl⟩) R1513363
theorem R84521 : Reach 84521 := rs (se 2 (by rfl) ⟨31695, by rfl⟩) R63391
theorem R84715 : Reach 84715 := rs (se 1 (by rfl) ⟨63536, by rfl⟩) R127073
theorem R84959 : Reach 84959 := rs (se 1 (by rfl) ⟨63719, by rfl⟩) R127439
theorem R445661 : Reach 445661 := rs (se 3 (by rfl) ⟨83561, by rfl⟩) R167123
theorem R85403 : Reach 85403 := rs (se 1 (by rfl) ⟨64052, by rfl⟩) R128105
theorem R85769 : Reach 85769 := rs (se 2 (by rfl) ⟨32163, by rfl⟩) R64327
theorem R85823 : Reach 85823 := rs (se 1 (by rfl) ⟨64367, by rfl⟩) R128735
theorem R479159 : Reach 479159 := rs (se 1 (by rfl) ⟨359369, by rfl⟩) R718739
theorem R86063 : Reach 86063 := rs (se 1 (by rfl) ⟨64547, by rfl⟩) R129095
theorem R86507 : Reach 86507 := rs (se 1 (by rfl) ⟨64880, by rfl⟩) R129761
theorem R86633 : Reach 86633 := rs (se 2 (by rfl) ⟨32487, by rfl⟩) R64975
theorem R86639 : Reach 86639 := rs (se 1 (by rfl) ⟨64979, by rfl⟩) R129959
theorem R86759 : Reach 86759 := rs (se 1 (by rfl) ⟨65069, by rfl⟩) R130139
theorem R3822329 : Reach 3822329 := rs (se 2 (by rfl) ⟨1433373, by rfl⟩) R2866747
theorem R3134213 : Reach 3134213 := rs (se 4 (by rfl) ⟨293832, by rfl⟩) R587665
theorem R414497 : Reach 414497 := rs (se 2 (by rfl) ⟨155436, by rfl⟩) R310873
theorem R86921 : Reach 86921 := rs (se 2 (by rfl) ⟨32595, by rfl⟩) R65191
theorem R87263 : Reach 87263 := rs (se 1 (by rfl) ⟨65447, by rfl⟩) R130895
theorem R87305 : Reach 87305 := rs (se 2 (by rfl) ⟨32739, by rfl⟩) R65479
theorem R87695 : Reach 87695 := rs (se 1 (by rfl) ⟨65771, by rfl⟩) R131543
theorem R87743 : Reach 87743 := rs (se 1 (by rfl) ⟨65807, by rfl⟩) R131615
theorem R87785 : Reach 87785 := rs (se 2 (by rfl) ⟨32919, by rfl⟩) R65839
theorem R87791 : Reach 87791 := rs (se 1 (by rfl) ⟨65843, by rfl⟩) R131687
theorem R55423 : Reach 55423 := rs (se 1 (by rfl) ⟨41567, by rfl⟩) R83135
theorem R55519 : Reach 55519 := rs (se 1 (by rfl) ⟨41639, by rfl⟩) R83279
theorem R88295 : Reach 88295 := rs (se 1 (by rfl) ⟨66221, by rfl⟩) R132443
theorem R252179 : Reach 252179 := rs (se 1 (by rfl) ⟨189134, by rfl⟩) R378269
theorem R55579 : Reach 55579 := rs (se 1 (by rfl) ⟨41684, by rfl⟩) R83369
theorem R55679 : Reach 55679 := rs (se 1 (by rfl) ⟨41759, by rfl⟩) R83519
theorem R55707 : Reach 55707 := rs (se 1 (by rfl) ⟨41780, by rfl⟩) R83561
theorem R88475 : Reach 88475 := rs (se 1 (by rfl) ⟨66356, by rfl⟩) R132713
theorem R186839 : Reach 186839 := rs (se 1 (by rfl) ⟨140129, by rfl⟩) R280259
theorem R612839 : Reach 612839 := rs (se 1 (by rfl) ⟨459629, by rfl⟩) R919259
theorem R678449 : Reach 678449 := rs (se 2 (by rfl) ⟨254418, by rfl⟩) R508837
theorem R55999 : Reach 55999 := rs (se 1 (by rfl) ⟨41999, by rfl⟩) R83999
theorem R383791 : Reach 383791 := rs (se 1 (by rfl) ⟨287843, by rfl⟩) R575687
theorem R56127 : Reach 56127 := rs (se 1 (by rfl) ⟨42095, by rfl⟩) R84191
theorem R1432403 : Reach 1432403 := rs (se 1 (by rfl) ⟨1074302, by rfl⟩) R2148605
theorem R56167 : Reach 56167 := rs (se 1 (by rfl) ⟨42125, by rfl⟩) R84251
theorem R2120579 : Reach 2120579 := rs (se 1 (by rfl) ⟨1590434, by rfl⟩) R3180869
theorem R56383 : Reach 56383 := rs (se 1 (by rfl) ⟨42287, by rfl⟩) R84575
theorem R285767 : Reach 285767 := rs (se 1 (by rfl) ⟨214325, by rfl⟩) R428651
theorem R56571 : Reach 56571 := rs (se 1 (by rfl) ⟨42428, by rfl⟩) R84857
theorem R56603 : Reach 56603 := rs (se 1 (by rfl) ⟨42452, by rfl⟩) R84905
theorem R89471 : Reach 89471 := rs (se 1 (by rfl) ⟨67103, by rfl⟩) R134207
theorem R56703 : Reach 56703 := rs (se 1 (by rfl) ⟨42527, by rfl⟩) R85055
theorem R57071 : Reach 57071 := rs (se 1 (by rfl) ⟨42803, by rfl⟩) R85607
theorem R57327 : Reach 57327 := rs (se 1 (by rfl) ⟨42995, by rfl⟩) R85991
theorem R57407 : Reach 57407 := rs (se 1 (by rfl) ⟨43055, by rfl⟩) R86111
theorem R57415 : Reach 57415 := rs (se 1 (by rfl) ⟨43061, by rfl⟩) R86123
theorem R57447 : Reach 57447 := rs (se 1 (by rfl) ⟨43085, by rfl⟩) R86171
theorem R155773 : Reach 155773 := rs (se 3 (by rfl) ⟨29207, by rfl⟩) R58415
theorem R319783 : Reach 319783 := rs (se 1 (by rfl) ⟨239837, by rfl⟩) R479675
theorem R287225 : Reach 287225 := rs (se 2 (by rfl) ⟨107709, by rfl⟩) R215419
theorem R156215 : Reach 156215 := rs (se 1 (by rfl) ⟨117161, by rfl⟩) R234323
theorem R58015 : Reach 58015 := rs (se 1 (by rfl) ⟨43511, by rfl⟩) R87023
theorem R58271 : Reach 58271 := rs (se 1 (by rfl) ⟨43703, by rfl⟩) R87407
theorem R58351 : Reach 58351 := rs (se 1 (by rfl) ⟨43763, by rfl⟩) R87527
theorem R58459 : Reach 58459 := rs (se 1 (by rfl) ⟨43844, by rfl⟩) R87689
theorem R58471 : Reach 58471 := rs (se 1 (by rfl) ⟨43853, by rfl⟩) R87707
theorem R156811 : Reach 156811 := rs (se 1 (by rfl) ⟨117608, by rfl⟩) R235217
theorem R58599 : Reach 58599 := rs (se 1 (by rfl) ⟨43949, by rfl⟩) R87899
theorem R156907 : Reach 156907 := rs (se 1 (by rfl) ⟨117680, by rfl⟩) R235361
theorem R1402181 : Reach 1402181 := rs (se 4 (by rfl) ⟨131454, by rfl⟩) R262909
theorem R124271 : Reach 124271 := rs (se 1 (by rfl) ⟨93203, by rfl⟩) R186407
theorem R124343 : Reach 124343 := rs (se 1 (by rfl) ⟨93257, by rfl⟩) R186515
theorem R58855 : Reach 58855 := rs (se 1 (by rfl) ⟨44141, by rfl⟩) R88283
theorem R124523 : Reach 124523 := rs (se 1 (by rfl) ⟨93392, by rfl⟩) R186785
theorem R59035 : Reach 59035 := rs (se 1 (by rfl) ⟨44276, by rfl⟩) R88553
theorem R124793 : Reach 124793 := rs (se 2 (by rfl) ⟨46797, by rfl⟩) R93595
theorem R124883 : Reach 124883 := rs (se 1 (by rfl) ⟨93662, by rfl⟩) R187325
theorem R157727 : Reach 157727 := rs (se 1 (by rfl) ⟨118295, by rfl⟩) R236591
theorem R190889 : Reach 190889 := rs (se 2 (by rfl) ⟨71583, by rfl⟩) R143167
theorem R158183 : Reach 158183 := rs (se 1 (by rfl) ⟨118637, by rfl⟩) R237275
theorem R289295 : Reach 289295 := rs (se 1 (by rfl) ⟨216971, by rfl⟩) R433943
theorem R125801 : Reach 125801 := rs (se 2 (by rfl) ⟨47175, by rfl⟩) R94351
theorem R125819 : Reach 125819 := rs (se 1 (by rfl) ⟨94364, by rfl⟩) R188729
theorem R650273 : Reach 650273 := rs (se 2 (by rfl) ⟨243852, by rfl⟩) R487705
theorem R126089 : Reach 126089 := rs (se 2 (by rfl) ⟨47283, by rfl⟩) R94567
theorem R93359 : Reach 93359 := rs (se 1 (by rfl) ⟨70019, by rfl⟩) R140039
theorem R126143 : Reach 126143 := rs (se 1 (by rfl) ⟨94607, by rfl⟩) R189215
theorem R191753 : Reach 191753 := rs (se 2 (by rfl) ⟨71907, by rfl⟩) R143815
theorem R519635 : Reach 519635 := rs (se 1 (by rfl) ⟨389726, by rfl⟩) R779453
theorem R323155 : Reach 323155 := rs (se 1 (by rfl) ⟨242366, by rfl⟩) R484733
theorem R552743 : Reach 552743 := rs (se 1 (by rfl) ⟨414557, by rfl⟩) R829115
theorem R126791 : Reach 126791 := rs (se 1 (by rfl) ⟨95093, by rfl⟩) R190187
theorem R126971 : Reach 126971 := rs (se 1 (by rfl) ⟨95228, by rfl⟩) R190457
theorem R127151 : Reach 127151 := rs (se 1 (by rfl) ⟨95363, by rfl⟩) R190727
theorem R356717 : Reach 356717 := rs (se 3 (by rfl) ⟨66884, by rfl⟩) R133769
theorem R553553 : Reach 553553 := rs (se 2 (by rfl) ⟨207582, by rfl⟩) R415165
theorem R553661 : Reach 553661 := rs (se 3 (by rfl) ⟨103811, by rfl⟩) R207623
theorem R423305 : Reach 423305 := rs (se 2 (by rfl) ⟨158739, by rfl⟩) R317479
theorem R20903345 : Reach 20903345 := rs (se 2 (by rfl) ⟨7838754, by rfl⟩) R15677509
theorem R63535 : Reach 63535 := rs (se 1 (by rfl) ⟨47651, by rfl⟩) R95303
theorem R96761 : Reach 96761 := rs (se 2 (by rfl) ⟨36285, by rfl⟩) R72571
theorem R424531 : Reach 424531 := rs (se 1 (by rfl) ⟨318398, by rfl⟩) R636797
theorem R97031 : Reach 97031 := rs (se 1 (by rfl) ⟨72773, by rfl⟩) R145547
theorem R162749 : Reach 162749 := rs (se 3 (by rfl) ⟨30515, by rfl⟩) R61031
theorem R97375 : Reach 97375 := rs (se 1 (by rfl) ⟨73031, by rfl⟩) R146063
theorem R326753 : Reach 326753 := rs (se 2 (by rfl) ⟨122532, by rfl⟩) R245065
theorem R195809 : Reach 195809 := rs (se 2 (by rfl) ⟨73428, by rfl⟩) R146857
theorem R97591 : Reach 97591 := rs (se 1 (by rfl) ⟨73193, by rfl⟩) R146387
theorem R490981 : Reach 490981 := rs (se 4 (by rfl) ⟨46029, by rfl⟩) R92059
theorem R130697 : Reach 130697 := rs (se 2 (by rfl) ⟨49011, by rfl⟩) R98023
theorem R98111 : Reach 98111 := rs (se 1 (by rfl) ⟨73583, by rfl⟩) R147167
theorem R65371 : Reach 65371 := rs (se 1 (by rfl) ⟨49028, by rfl⟩) R98057
theorem R98273 : Reach 98273 := rs (se 2 (by rfl) ⟨36852, by rfl⟩) R73705
theorem R655553 : Reach 655553 := rs (se 2 (by rfl) ⟨245832, by rfl⟩) R491665
theorem R98543 : Reach 98543 := rs (se 1 (by rfl) ⟨73907, by rfl⟩) R147815
theorem R426377 : Reach 426377 := rs (se 2 (by rfl) ⟨159891, by rfl⟩) R319783
theorem R132137 : Reach 132137 := rs (se 2 (by rfl) ⟨49551, by rfl⟩) R99103
theorem R132191 : Reach 132191 := rs (se 1 (by rfl) ⟨99143, by rfl⟩) R198287
theorem R132371 : Reach 132371 := rs (se 1 (by rfl) ⟨99278, by rfl⟩) R198557
theorem R1345211 : Reach 1345211 := rs (se 1 (by rfl) ⟨1008908, by rfl⟩) R2017817
theorem R722627 : Reach 722627 := rs (se 1 (by rfl) ⟨541970, by rfl⟩) R1083941
theorem R198395 : Reach 198395 := rs (se 1 (by rfl) ⟨148796, by rfl⟩) R297593
theorem R10192877 : Reach 10192877 := rs (se 3 (by rfl) ⟨1911164, by rfl⟩) R3822329
theorem R297107 : Reach 297107 := rs (se 1 (by rfl) ⟨222830, by rfl⟩) R445661
theorem R168119 : Reach 168119 := rs (se 1 (by rfl) ⟨126089, by rfl⟩) R252179
theorem R856327 : Reach 856327 := rs (se 1 (by rfl) ⟨642245, by rfl⟩) R1284491
theorem R332059 : Reach 332059 := rs (se 1 (by rfl) ⟨249044, by rfl⟩) R498089
theorem R954935 : Reach 954935 := rs (se 1 (by rfl) ⟨716201, by rfl⟩) R1432403
theorem R1413719 : Reach 1413719 := rs (se 1 (by rfl) ⟨1060289, by rfl⟩) R2120579
theorem R7082599 : Reach 7082599 := rs (se 1 (by rfl) ⟨5311949, by rfl⟩) R10623899
theorem R104105 : Reach 104105 := rs (se 2 (by rfl) ⟨39039, by rfl⟩) R78079
theorem R136927 : Reach 136927 := rs (se 1 (by rfl) ⟨102695, by rfl⟩) R205391
theorem R1841363 : Reach 1841363 := rs (se 1 (by rfl) ⟨1381022, by rfl⟩) R2762045
theorem R105151 : Reach 105151 := rs (se 1 (by rfl) ⟨78863, by rfl⟩) R157727
theorem R105455 : Reach 105455 := rs (se 1 (by rfl) ⟨79091, by rfl⟩) R158183
theorem R204079 : Reach 204079 := rs (se 1 (by rfl) ⟨153059, by rfl⟩) R306119
theorem R1645991 : Reach 1645991 := rs (se 1 (by rfl) ⟨1234493, by rfl⟩) R2468987
theorem R433997 : Reach 433997 := rs (se 3 (by rfl) ⟨81374, by rfl⟩) R162749
theorem R368495 : Reach 368495 := rs (se 1 (by rfl) ⟨276371, by rfl⟩) R552743
theorem R73639 : Reach 73639 := rs (se 1 (by rfl) ⟨55229, by rfl⟩) R110459
theorem R237811 : Reach 237811 := rs (se 1 (by rfl) ⟨178358, by rfl⟩) R356717
theorem R369035 : Reach 369035 := rs (se 1 (by rfl) ⟨276776, by rfl⟩) R553553
theorem R369107 : Reach 369107 := rs (se 1 (by rfl) ⟨276830, by rfl⟩) R553661
theorem R566041 : Reach 566041 := rs (se 2 (by rfl) ⟨212265, by rfl⟩) R424531
theorem R13935563 : Reach 13935563 := rs (se 1 (by rfl) ⟨10451672, by rfl⟩) R20903345
theorem R238589 : Reach 238589 := rs (se 3 (by rfl) ⟨44735, by rfl⟩) R89471
theorem R1385693 : Reach 1385693 := rs (se 3 (by rfl) ⟨259817, by rfl⟩) R519635
theorem R206327 : Reach 206327 := rs (se 1 (by rfl) ⟨154745, by rfl⟩) R309491
theorem R2861689 : Reach 2861689 := rs (se 2 (by rfl) ⟨1073133, by rfl⟩) R2146267
theorem R207697 : Reach 207697 := rs (se 2 (by rfl) ⟨77886, by rfl⟩) R155773
theorem R404513 : Reach 404513 := rs (se 2 (by rfl) ⟨151692, by rfl⟩) R303385
theorem R274025 : Reach 274025 := rs (se 2 (by rfl) ⟨102759, by rfl⟩) R205519
theorem R732887 : Reach 732887 := rs (se 1 (by rfl) ⟨549665, by rfl⟩) R1099331
theorem R209081 : Reach 209081 := rs (se 2 (by rfl) ⟨78405, by rfl⟩) R156811
theorem R2044115 : Reach 2044115 := rs (se 1 (by rfl) ⟨1533086, by rfl⟩) R3066173
theorem R1258021 : Reach 1258021 := rs (se 4 (by rfl) ⟨117939, by rfl⟩) R235879
theorem R143977 : Reach 143977 := rs (se 2 (by rfl) ⟨53991, by rfl⟩) R107983
theorem R111335 : Reach 111335 := rs (se 1 (by rfl) ⟨83501, by rfl⟩) R167003
theorem R635687 : Reach 635687 := rs (se 1 (by rfl) ⟨476765, by rfl⟩) R953531
theorem R243647 : Reach 243647 := rs (se 1 (by rfl) ⟨182735, by rfl⟩) R365471
theorem R145385 : Reach 145385 := rs (se 2 (by rfl) ⟨54519, by rfl⟩) R109039
theorem R14956597 : Reach 14956597 := rs (se 5 (by rfl) ⟨701090, by rfl⟩) R1402181
theorem R408559 : Reach 408559 := rs (se 1 (by rfl) ⟨306419, by rfl⟩) R612839
theorem R475469 : Reach 475469 := rs (se 3 (by rfl) ⟨89150, by rfl⟩) R178301
theorem R82847 : Reach 82847 := rs (se 1 (by rfl) ⟨62135, by rfl⟩) R124271
theorem R934841 : Reach 934841 := rs (se 2 (by rfl) ⟨350565, by rfl⟩) R701131
theorem R82895 : Reach 82895 := rs (se 1 (by rfl) ⟨62171, by rfl⟩) R124343
theorem R83015 : Reach 83015 := rs (se 1 (by rfl) ⟨62261, by rfl⟩) R124523
theorem R836837 : Reach 836837 := rs (se 4 (by rfl) ⟨78453, by rfl⟩) R156907
theorem R83195 : Reach 83195 := rs (se 1 (by rfl) ⟨62396, by rfl⟩) R124793
theorem R83255 : Reach 83255 := rs (se 1 (by rfl) ⟨62441, by rfl⟩) R124883
theorem R182159 : Reach 182159 := rs (se 1 (by rfl) ⟨136619, by rfl⟩) R273239
theorem R83867 : Reach 83867 := rs (se 1 (by rfl) ⟨62900, by rfl⟩) R125801
theorem R83879 : Reach 83879 := rs (se 1 (by rfl) ⟨62909, by rfl⟩) R125819
theorem R84059 : Reach 84059 := rs (se 1 (by rfl) ⟨63044, by rfl⟩) R126089
theorem R84095 : Reach 84095 := rs (se 1 (by rfl) ⟨63071, by rfl⟩) R126143
theorem R117227 : Reach 117227 := rs (se 1 (by rfl) ⟨87920, by rfl⟩) R175841
theorem R84527 : Reach 84527 := rs (se 1 (by rfl) ⟨63395, by rfl⟩) R126791
theorem R84647 : Reach 84647 := rs (se 1 (by rfl) ⟨63485, by rfl⟩) R126971
theorem R84713 : Reach 84713 := rs (se 2 (by rfl) ⟨31767, by rfl⟩) R63535
theorem R84767 : Reach 84767 := rs (se 1 (by rfl) ⟨63575, by rfl⟩) R127151
theorem R1723493 : Reach 1723493 := rs (se 4 (by rfl) ⟨161577, by rfl⟩) R323155
theorem R282203 : Reach 282203 := rs (se 1 (by rfl) ⟨211652, by rfl⟩) R423305
theorem R511721 : Reach 511721 := rs (se 2 (by rfl) ⟨191895, by rfl⟩) R383791
theorem R315521 : Reach 315521 := rs (se 2 (by rfl) ⟨118320, by rfl⟩) R236641
theorem R217835 : Reach 217835 := rs (se 1 (by rfl) ⟨163376, by rfl⟩) R326753
theorem R119839 : Reach 119839 := rs (se 1 (by rfl) ⟨89879, by rfl⟩) R179759
theorem R87131 : Reach 87131 := rs (se 1 (by rfl) ⟨65348, by rfl⟩) R130697
theorem R939113 : Reach 939113 := rs (se 2 (by rfl) ⟨352167, by rfl⟩) R704335
theorem R87161 : Reach 87161 := rs (se 2 (by rfl) ⟨32685, by rfl⟩) R65371
theorem R87551 : Reach 87551 := rs (se 1 (by rfl) ⟨65663, by rfl⟩) R131327
theorem R186191 : Reach 186191 := rs (se 1 (by rfl) ⟨139643, by rfl⟩) R279287
theorem R87929 : Reach 87929 := rs (se 2 (by rfl) ⟨32973, by rfl⟩) R65947
theorem R87935 : Reach 87935 := rs (se 1 (by rfl) ⟨65951, by rfl⟩) R131903
theorem R55207 : Reach 55207 := rs (se 1 (by rfl) ⟨41405, by rfl⟩) R82811
theorem R710639 : Reach 710639 := rs (se 1 (by rfl) ⟨532979, by rfl⟩) R1065959
theorem R55291 : Reach 55291 := rs (se 1 (by rfl) ⟨41468, by rfl⟩) R82937
theorem R55327 : Reach 55327 := rs (se 1 (by rfl) ⟨41495, by rfl⟩) R82991
theorem R55407 : Reach 55407 := rs (se 1 (by rfl) ⟨41555, by rfl⟩) R83111
theorem R55535 : Reach 55535 := rs (se 1 (by rfl) ⟨41651, by rfl⟩) R83303
theorem R940403 : Reach 940403 := rs (se 1 (by rfl) ⟨705302, by rfl⟩) R1410605
theorem R186887 : Reach 186887 := rs (se 1 (by rfl) ⟨140165, by rfl⟩) R280331
theorem R1006141 : Reach 1006141 := rs (se 3 (by rfl) ⟨188651, by rfl⟩) R377303
theorem R55963 : Reach 55963 := rs (se 1 (by rfl) ⟨41972, by rfl⟩) R83945
theorem R56059 : Reach 56059 := rs (se 1 (by rfl) ⟨42044, by rfl⟩) R84089
theorem R416573 : Reach 416573 := rs (se 3 (by rfl) ⟨78107, by rfl⟩) R156215
theorem R56191 : Reach 56191 := rs (se 1 (by rfl) ⟨42143, by rfl⟩) R84287
theorem R56287 : Reach 56287 := rs (se 1 (by rfl) ⟨42215, by rfl⟩) R84431
theorem R56315 : Reach 56315 := rs (se 1 (by rfl) ⟨42236, by rfl⟩) R84473
theorem R56347 : Reach 56347 := rs (se 1 (by rfl) ⟨42260, by rfl⟩) R84521
theorem R285929 : Reach 285929 := rs (se 2 (by rfl) ⟨107223, by rfl⟩) R214447
theorem R56639 : Reach 56639 := rs (se 1 (by rfl) ⟨42479, by rfl⟩) R84959
theorem R1105325 : Reach 1105325 := rs (se 3 (by rfl) ⟨207248, by rfl⟩) R414497
theorem R56935 : Reach 56935 := rs (se 1 (by rfl) ⟨42701, by rfl⟩) R85403
theorem R2088629 : Reach 2088629 := rs (se 5 (by rfl) ⟨97904, by rfl⟩) R195809
theorem R57179 : Reach 57179 := rs (se 1 (by rfl) ⟨42884, by rfl⟩) R85769
theorem R57215 : Reach 57215 := rs (se 1 (by rfl) ⟨42911, by rfl⟩) R85823
theorem R319439 : Reach 319439 := rs (se 1 (by rfl) ⟨239579, by rfl⟩) R479159
theorem R57375 : Reach 57375 := rs (se 1 (by rfl) ⟨43031, by rfl⟩) R86063
theorem R57671 : Reach 57671 := rs (se 1 (by rfl) ⟨43253, by rfl⟩) R86507
theorem R57755 : Reach 57755 := rs (se 1 (by rfl) ⟨43316, by rfl⟩) R86633
theorem R57759 : Reach 57759 := rs (se 1 (by rfl) ⟨43319, by rfl⟩) R86639
theorem R57839 : Reach 57839 := rs (se 1 (by rfl) ⟨43379, by rfl⟩) R86759
theorem R2089475 : Reach 2089475 := rs (se 1 (by rfl) ⟨1567106, by rfl⟩) R3134213
theorem R57947 : Reach 57947 := rs (se 1 (by rfl) ⟨43460, by rfl⟩) R86921
theorem R189161 : Reach 189161 := rs (se 2 (by rfl) ⟨70935, by rfl⟩) R141871
theorem R58175 : Reach 58175 := rs (se 1 (by rfl) ⟨43631, by rfl⟩) R87263
theorem R58203 : Reach 58203 := rs (se 1 (by rfl) ⟨43652, by rfl⟩) R87305
theorem R58463 : Reach 58463 := rs (se 1 (by rfl) ⟨43847, by rfl⟩) R87695
theorem R58495 : Reach 58495 := rs (se 1 (by rfl) ⟨43871, by rfl⟩) R87743
theorem R58523 : Reach 58523 := rs (se 1 (by rfl) ⟨43892, by rfl⟩) R87785
theorem R58527 : Reach 58527 := rs (se 1 (by rfl) ⟨43895, by rfl⟩) R87791
theorem R451813 : Reach 451813 := rs (se 4 (by rfl) ⟨42357, by rfl⟩) R84715
theorem R91439 : Reach 91439 := rs (se 1 (by rfl) ⟨68579, by rfl⟩) R137159
theorem R58863 : Reach 58863 := rs (se 1 (by rfl) ⟨44147, by rfl⟩) R88295
theorem R190025 : Reach 190025 := rs (se 2 (by rfl) ⟨71259, by rfl⟩) R142519
theorem R58983 : Reach 58983 := rs (se 1 (by rfl) ⟨44237, by rfl⟩) R88475
theorem R124559 : Reach 124559 := rs (se 1 (by rfl) ⟨93419, by rfl⟩) R186839
theorem R452299 : Reach 452299 := rs (se 1 (by rfl) ⟨339224, by rfl⟩) R678449
theorem R157427 : Reach 157427 := rs (se 1 (by rfl) ⟨118070, by rfl⟩) R236141
theorem R190511 : Reach 190511 := rs (se 1 (by rfl) ⟨142883, by rfl⟩) R285767
theorem R158375 : Reach 158375 := rs (se 1 (by rfl) ⟨118781, by rfl⟩) R237563
theorem R224167 : Reach 224167 := rs (se 1 (by rfl) ⟨168125, by rfl⟩) R336251
theorem R191483 : Reach 191483 := rs (se 1 (by rfl) ⟨143612, by rfl⟩) R287225
theorem R224765 : Reach 224765 := rs (se 3 (by rfl) ⟨42143, by rfl⟩) R84287
theorem R1207943 : Reach 1207943 := rs (se 1 (by rfl) ⟨905957, by rfl⟩) R1811915
theorem R224927 : Reach 224927 := rs (se 1 (by rfl) ⟨168695, by rfl⟩) R337391
theorem R421847 : Reach 421847 := rs (se 1 (by rfl) ⟨316385, by rfl⟩) R632771
theorem R94463 : Reach 94463 := rs (se 1 (by rfl) ⟨70847, by rfl⟩) R141695
theorem R127259 : Reach 127259 := rs (se 1 (by rfl) ⟨95444, by rfl⟩) R190889
theorem R192863 : Reach 192863 := rs (se 1 (by rfl) ⟨144647, by rfl⟩) R289295
theorem R62239 : Reach 62239 := rs (se 1 (by rfl) ⟨46679, by rfl⟩) R93359
theorem R619325 : Reach 619325 := rs (se 3 (by rfl) ⟨116123, by rfl⟩) R232247
theorem R127835 : Reach 127835 := rs (se 1 (by rfl) ⟨95876, by rfl⟩) R191753
theorem R95215 : Reach 95215 := rs (se 1 (by rfl) ⟨71411, by rfl⟩) R142823
theorem R291923 : Reach 291923 := rs (se 1 (by rfl) ⟨218942, by rfl⟩) R437885
theorem R357473 : Reach 357473 := rs (se 2 (by rfl) ⟨134052, by rfl⟩) R268105
theorem R1734061 : Reach 1734061 := rs (se 3 (by rfl) ⟨325136, by rfl⟩) R650273
theorem R226799 : Reach 226799 := rs (se 1 (by rfl) ⟨170099, by rfl⟩) R340199
theorem R194345 : Reach 194345 := rs (se 2 (by rfl) ⟨72879, by rfl⟩) R145759
theorem R129833 : Reach 129833 := rs (se 2 (by rfl) ⟨48687, by rfl⟩) R97375
theorem R64507 : Reach 64507 := rs (se 1 (by rfl) ⟨48380, by rfl⟩) R96761
theorem R130121 : Reach 130121 := rs (se 2 (by rfl) ⟨48795, by rfl⟩) R97591
theorem R64687 : Reach 64687 := rs (se 1 (by rfl) ⟨48515, by rfl⟩) R97031
theorem R654641 : Reach 654641 := rs (se 2 (by rfl) ⟨245490, by rfl⟩) R490981
theorem R196073 : Reach 196073 := rs (se 2 (by rfl) ⟨73527, by rfl⟩) R147055
theorem R98131 : Reach 98131 := rs (se 1 (by rfl) ⟨73598, by rfl⟩) R147197
theorem R65407 : Reach 65407 := rs (se 1 (by rfl) ⟨49055, by rfl⟩) R98111
theorem R622525 : Reach 622525 := rs (se 3 (by rfl) ⟨116723, by rfl⟩) R233447
theorem R98239 : Reach 98239 := rs (se 1 (by rfl) ⟨73679, by rfl⟩) R147359
theorem R65515 : Reach 65515 := rs (se 1 (by rfl) ⟨49136, by rfl⟩) R98273
theorem R65695 : Reach 65695 := rs (se 1 (by rfl) ⟨49271, by rfl⟩) R98543
theorem R557549 : Reach 557549 := rs (se 3 (by rfl) ⟨104540, by rfl⟩) R209081
theorem R623227 : Reach 623227 := rs (se 1 (by rfl) ⟨467420, by rfl⟩) R934841
theorem R557891 : Reach 557891 := rs (se 1 (by rfl) ⟨418418, by rfl⟩) R836837
theorem R754721 : Reach 754721 := rs (se 2 (by rfl) ⟨283020, by rfl⟩) R566041
theorem R132263 : Reach 132263 := rs (se 1 (by rfl) ⟨99197, by rfl⟩) R198395
theorem R198071 : Reach 198071 := rs (se 1 (by rfl) ⟨148553, by rfl⟩) R297107
theorem R296893 : Reach 296893 := rs (se 3 (by rfl) ⟨55667, by rfl⟩) R111335
theorem R1148995 : Reach 1148995 := rs (se 1 (by rfl) ⟨861746, by rfl⟩) R1723493
theorem R626075 : Reach 626075 := rs (se 1 (by rfl) ⟨469556, by rfl⟩) R939113
theorem R69403 : Reach 69403 := rs (se 1 (by rfl) ⟨52052, by rfl⟩) R104105
theorem R298889 : Reach 298889 := rs (se 2 (by rfl) ⟨112083, by rfl⟩) R224167
theorem R626935 : Reach 626935 := rs (se 1 (by rfl) ⟨470201, by rfl⟩) R940403
theorem R70303 : Reach 70303 := rs (se 1 (by rfl) ⟨52727, by rfl⟩) R105455
theorem R1677361 : Reach 1677361 := rs (se 2 (by rfl) ⟨629010, by rfl⟩) R1258021
theorem R9443465 : Reach 9443465 := rs (se 2 (by rfl) ⟨3541299, by rfl⟩) R7082599
theorem R923795 : Reach 923795 := rs (se 1 (by rfl) ⟨692846, by rfl⟩) R1385693
theorem R137551 : Reach 137551 := rs (se 1 (by rfl) ⟨103163, by rfl⟩) R206327
theorem R104951 : Reach 104951 := rs (se 1 (by rfl) ⟨78713, by rfl⟩) R157427
theorem R269675 : Reach 269675 := rs (se 1 (by rfl) ⟨202256, by rfl⟩) R404513
theorem R238315 : Reach 238315 := rs (se 1 (by rfl) ⟨178736, by rfl⟩) R357473
theorem R140201 : Reach 140201 := rs (se 2 (by rfl) ⟨52575, by rfl⟩) R105151
theorem R272105 : Reach 272105 := rs (se 2 (by rfl) ⟨102039, by rfl⟩) R204079
theorem R436427 : Reach 436427 := rs (se 1 (by rfl) ⟨327320, by rfl⟩) R654641
theorem R830033 : Reach 830033 := rs (se 2 (by rfl) ⟨311262, by rfl⟩) R622525
theorem R437035 : Reach 437035 := rs (se 1 (by rfl) ⟨327776, by rfl⟩) R655553
theorem R896807 : Reach 896807 := rs (se 1 (by rfl) ⟨672605, by rfl⟩) R1345211
theorem R6795251 : Reach 6795251 := rs (se 1 (by rfl) ⟨5096438, by rfl⟩) R10192877
theorem R602417 : Reach 602417 := rs (se 2 (by rfl) ⟨225906, by rfl⟩) R451813
theorem R603065 : Reach 603065 := rs (se 2 (by rfl) ⟨226149, by rfl⟩) R452299
theorem R341147 : Reach 341147 := rs (se 1 (by rfl) ⟨255860, by rfl⟩) R511721
theorem R210347 : Reach 210347 := rs (se 1 (by rfl) ⟨157760, by rfl⟩) R315521
theorem R112079 : Reach 112079 := rs (se 1 (by rfl) ⟨84059, by rfl⟩) R168119
theorem R636623 : Reach 636623 := rs (se 1 (by rfl) ⟨477467, by rfl⟩) R954935
theorem R145223 : Reach 145223 := rs (se 1 (by rfl) ⟨108917, by rfl⟩) R217835
theorem R3815585 : Reach 3815585 := rs (se 2 (by rfl) ⟨1430844, by rfl⟩) R2861689
theorem R276929 : Reach 276929 := rs (se 2 (by rfl) ⟨103848, by rfl⟩) R207697
theorem R473759 : Reach 473759 := rs (se 1 (by rfl) ⟨355319, by rfl⟩) R710639
theorem R1227575 : Reach 1227575 := rs (se 1 (by rfl) ⟨920681, by rfl⟩) R1841363
theorem R277715 : Reach 277715 := rs (se 1 (by rfl) ⟨208286, by rfl⟩) R416573
theorem R1097327 : Reach 1097327 := rs (se 1 (by rfl) ⟨822995, by rfl⟩) R1645991
theorem R736883 : Reach 736883 := rs (se 1 (by rfl) ⟨552662, by rfl⟩) R1105325
theorem R1392419 : Reach 1392419 := rs (se 1 (by rfl) ⟨1044314, by rfl⟩) R2088629
theorem R245663 : Reach 245663 := rs (se 1 (by rfl) ⟨184247, by rfl⟩) R368495
theorem R212959 : Reach 212959 := rs (se 1 (by rfl) ⟨159719, by rfl⟩) R319439
theorem R246023 : Reach 246023 := rs (se 1 (by rfl) ⟨184517, by rfl⟩) R369035
theorem R246071 : Reach 246071 := rs (se 1 (by rfl) ⟨184553, by rfl⟩) R369107
theorem R1392983 : Reach 1392983 := rs (se 1 (by rfl) ⟨1044737, by rfl⟩) R2089475
theorem R442745 : Reach 442745 := rs (se 2 (by rfl) ⟨166029, by rfl⟩) R332059
theorem R9290375 : Reach 9290375 := rs (se 1 (by rfl) ⟨6967781, by rfl⟩) R13935563
theorem R82985 : Reach 82985 := rs (se 2 (by rfl) ⟨31119, by rfl⟩) R62239
theorem R83039 : Reach 83039 := rs (se 1 (by rfl) ⟨62279, by rfl⟩) R124559
theorem R312605 : Reach 312605 := rs (se 3 (by rfl) ⟨58613, by rfl⟩) R117227
theorem R2312081 : Reach 2312081 := rs (se 2 (by rfl) ⟨867030, by rfl⟩) R1734061
theorem R182569 : Reach 182569 := rs (se 2 (by rfl) ⟨68463, by rfl⟩) R136927
theorem R149843 : Reach 149843 := rs (se 1 (by rfl) ⟨112382, by rfl⟩) R224765
theorem R182683 : Reach 182683 := rs (se 1 (by rfl) ⟨137012, by rfl⟩) R274025
theorem R805295 : Reach 805295 := rs (se 1 (by rfl) ⟨603971, by rfl⟩) R1207943
theorem R149951 : Reach 149951 := rs (se 1 (by rfl) ⟨112463, by rfl⟩) R224927
theorem R281231 : Reach 281231 := rs (se 1 (by rfl) ⟨210923, by rfl⟩) R421847
theorem R19942129 : Reach 19942129 := rs (se 2 (by rfl) ⟨7478298, by rfl⟩) R14956597
theorem R1362743 : Reach 1362743 := rs (se 1 (by rfl) ⟨1022057, by rfl⟩) R2044115
theorem R84839 : Reach 84839 := rs (se 1 (by rfl) ⟨63629, by rfl⟩) R127259
theorem R412883 : Reach 412883 := rs (se 1 (by rfl) ⟨309662, by rfl⟩) R619325
theorem R85223 : Reach 85223 := rs (se 1 (by rfl) ⟨63917, by rfl⟩) R127835
theorem R151199 : Reach 151199 := rs (se 1 (by rfl) ⟨113399, by rfl⟩) R226799
theorem R544745 : Reach 544745 := rs (se 2 (by rfl) ⟨204279, by rfl⟩) R408559
theorem R86009 : Reach 86009 := rs (se 2 (by rfl) ⟨32253, by rfl⟩) R64507
theorem R86249 : Reach 86249 := rs (se 2 (by rfl) ⟨32343, by rfl⟩) R64687
theorem R86555 : Reach 86555 := rs (se 1 (by rfl) ⟨64916, by rfl⟩) R129833
theorem R86747 : Reach 86747 := rs (se 1 (by rfl) ⟨65060, by rfl⟩) R130121
theorem R87209 : Reach 87209 := rs (se 2 (by rfl) ⟨32703, by rfl⟩) R65407
theorem R87353 : Reach 87353 := rs (se 2 (by rfl) ⟨32757, by rfl⟩) R65515
theorem R316979 : Reach 316979 := rs (se 1 (by rfl) ⟨237734, by rfl⟩) R475469
theorem R284251 : Reach 284251 := rs (se 1 (by rfl) ⟨213188, by rfl⟩) R426377
theorem R317081 : Reach 317081 := rs (se 2 (by rfl) ⟨118905, by rfl⟩) R237811
theorem R55231 : Reach 55231 := rs (se 1 (by rfl) ⟨41423, by rfl⟩) R82847
theorem R55263 : Reach 55263 := rs (se 1 (by rfl) ⟨41447, by rfl⟩) R82895
theorem R88091 : Reach 88091 := rs (se 1 (by rfl) ⟨66068, by rfl⟩) R132137
theorem R55343 : Reach 55343 := rs (se 1 (by rfl) ⟨41507, by rfl⟩) R83015
theorem R88127 : Reach 88127 := rs (se 1 (by rfl) ⟨66095, by rfl⟩) R132191
theorem R55463 : Reach 55463 := rs (se 1 (by rfl) ⟨41597, by rfl⟩) R83195
theorem R88247 : Reach 88247 := rs (se 1 (by rfl) ⟨66185, by rfl⟩) R132371
theorem R55503 : Reach 55503 := rs (se 1 (by rfl) ⟨41627, by rfl⟩) R83255
theorem R481751 : Reach 481751 := rs (se 1 (by rfl) ⟨361313, by rfl⟩) R722627
theorem R121439 : Reach 121439 := rs (se 1 (by rfl) ⟨91079, by rfl⟩) R182159
theorem R55911 : Reach 55911 := rs (se 1 (by rfl) ⟨41933, by rfl⟩) R83867
theorem R55919 : Reach 55919 := rs (se 1 (by rfl) ⟨41939, by rfl⟩) R83879
theorem R56039 : Reach 56039 := rs (se 1 (by rfl) ⟨42029, by rfl⟩) R84059
theorem R56063 : Reach 56063 := rs (se 1 (by rfl) ⟨42047, by rfl⟩) R84095
theorem R56351 : Reach 56351 := rs (se 1 (by rfl) ⟨42263, by rfl⟩) R84527
theorem R56431 : Reach 56431 := rs (se 1 (by rfl) ⟨42323, by rfl⟩) R84647
theorem R56475 : Reach 56475 := rs (se 1 (by rfl) ⟨42356, by rfl⟩) R84713
theorem R56511 : Reach 56511 := rs (se 1 (by rfl) ⟨42383, by rfl⟩) R84767
theorem R188135 : Reach 188135 := rs (se 1 (by rfl) ⟨141101, by rfl⟩) R282203
theorem R942479 : Reach 942479 := rs (se 1 (by rfl) ⟨706859, by rfl⟩) R1413719
theorem R58087 : Reach 58087 := rs (se 1 (by rfl) ⟨43565, by rfl⟩) R87131
theorem R58107 : Reach 58107 := rs (se 1 (by rfl) ⟨43580, by rfl⟩) R87161
theorem R58367 : Reach 58367 := rs (se 1 (by rfl) ⟨43775, by rfl⟩) R87551
theorem R124127 : Reach 124127 := rs (se 1 (by rfl) ⟨93095, by rfl⟩) R186191
theorem R58619 : Reach 58619 := rs (se 1 (by rfl) ⟨43964, by rfl⟩) R87929
theorem R58623 : Reach 58623 := rs (se 1 (by rfl) ⟨43967, by rfl⟩) R87935
theorem R124591 : Reach 124591 := rs (se 1 (by rfl) ⟨93443, by rfl⟩) R186887
theorem R190619 : Reach 190619 := rs (se 1 (by rfl) ⟨142964, by rfl⟩) R285929
theorem R289331 : Reach 289331 := rs (se 1 (by rfl) ⟨216998, by rfl⟩) R433997
theorem R1141769 : Reach 1141769 := rs (se 2 (by rfl) ⟨428163, by rfl⟩) R856327
theorem R126107 : Reach 126107 := rs (se 1 (by rfl) ⟨94580, by rfl⟩) R189161
theorem R159059 : Reach 159059 := rs (se 1 (by rfl) ⟨119294, by rfl⟩) R238589
theorem R191969 : Reach 191969 := rs (se 2 (by rfl) ⟨71988, by rfl⟩) R143977
theorem R60959 : Reach 60959 := rs (se 1 (by rfl) ⟨45719, by rfl⟩) R91439
theorem R126683 : Reach 126683 := rs (se 1 (by rfl) ⟨95012, by rfl⟩) R190025
theorem R126953 : Reach 126953 := rs (se 2 (by rfl) ⟨47607, by rfl⟩) R95215
theorem R127007 : Reach 127007 := rs (se 1 (by rfl) ⟨95255, by rfl⟩) R190511
theorem R159785 : Reach 159785 := rs (se 2 (by rfl) ⟨59919, by rfl⟩) R119839
theorem R422333 : Reach 422333 := rs (se 3 (by rfl) ⟨79187, by rfl⟩) R158375
theorem R127655 : Reach 127655 := rs (se 1 (by rfl) ⟨95741, by rfl⟩) R191483
theorem R488591 : Reach 488591 := rs (se 1 (by rfl) ⟨366443, by rfl⟩) R732887
theorem R62975 : Reach 62975 := rs (se 1 (by rfl) ⟨47231, by rfl⟩) R94463
theorem R128575 : Reach 128575 := rs (se 1 (by rfl) ⟨96431, by rfl⟩) R192863
theorem R423791 : Reach 423791 := rs (se 1 (by rfl) ⟨317843, by rfl⟩) R635687
theorem R194615 : Reach 194615 := rs (se 1 (by rfl) ⟨145961, by rfl⟩) R291923
theorem R1341521 : Reach 1341521 := rs (se 2 (by rfl) ⟨503070, by rfl⟩) R1006141
theorem R129563 : Reach 129563 := rs (se 1 (by rfl) ⟨97172, by rfl⟩) R194345
theorem R162431 : Reach 162431 := rs (se 1 (by rfl) ⟨121823, by rfl⟩) R243647
theorem R96923 : Reach 96923 := rs (se 1 (by rfl) ⟨72692, by rfl⟩) R145385
theorem R130715 : Reach 130715 := rs (se 1 (by rfl) ⟨98036, by rfl⟩) R196073
theorem R130841 : Reach 130841 := rs (se 2 (by rfl) ⟨49065, by rfl⟩) R98131
theorem R98185 : Reach 98185 := rs (se 2 (by rfl) ⟨36819, by rfl⟩) R73639
theorem R130985 : Reach 130985 := rs (se 2 (by rfl) ⟨49119, by rfl⟩) R98239
theorem R164015 : Reach 164015 := rs (se 1 (by rfl) ⟨123011, by rfl⟩) R246023
theorem R164047 : Reach 164047 := rs (se 1 (by rfl) ⟨123035, by rfl⟩) R246071
theorem R295163 : Reach 295163 := rs (se 1 (by rfl) ⟨221372, by rfl⟩) R442745
theorem R6193583 : Reach 6193583 := rs (se 1 (by rfl) ⟨4645187, by rfl⟩) R9290375
theorem R132047 : Reach 132047 := rs (se 1 (by rfl) ⟨99035, by rfl⟩) R198071
theorem R1541387 : Reach 1541387 := rs (se 1 (by rfl) ⟨1156040, by rfl⟩) R2312081
theorem R99967 : Reach 99967 := rs (se 1 (by rfl) ⟨74975, by rfl⟩) R149951
theorem R166121 : Reach 166121 := rs (se 2 (by rfl) ⟨62295, by rfl⟩) R124591
theorem R100799 : Reach 100799 := rs (se 1 (by rfl) ⟨75599, by rfl⟩) R151199
theorem R395857 : Reach 395857 := rs (se 2 (by rfl) ⟨148446, by rfl⟩) R296893
theorem R199259 : Reach 199259 := rs (se 1 (by rfl) ⟨149444, by rfl⟩) R298889
theorem R363163 : Reach 363163 := rs (se 1 (by rfl) ⟨272372, by rfl⟩) R544745
theorem R167933 : Reach 167933 := rs (se 3 (by rfl) ⟨31487, by rfl⟩) R62975
theorem R6295643 : Reach 6295643 := rs (se 1 (by rfl) ⟨4721732, by rfl⟩) R9443465
theorem R69967 : Reach 69967 := rs (se 1 (by rfl) ⟨52475, by rfl⟩) R104951
theorem R628319 : Reach 628319 := rs (se 1 (by rfl) ⟨471239, by rfl⟩) R942479
theorem R399581 : Reach 399581 := rs (se 3 (by rfl) ⟨74921, by rfl⟩) R149843
theorem R761179 : Reach 761179 := rs (se 1 (by rfl) ⟨570884, by rfl⟩) R1141769
theorem R171433 : Reach 171433 := rs (se 2 (by rfl) ⟨64287, by rfl⟩) R128575
theorem R106039 : Reach 106039 := rs (se 1 (by rfl) ⟨79529, by rfl⟩) R159059
theorem R597871 : Reach 597871 := rs (se 1 (by rfl) ⟨448403, by rfl⟩) R896807
theorem R4530167 : Reach 4530167 := rs (se 1 (by rfl) ⟨3397625, by rfl⟩) R6795251
theorem R106523 : Reach 106523 := rs (se 1 (by rfl) ⟨79892, by rfl⟩) R159785
theorem R2236481 : Reach 2236481 := rs (se 2 (by rfl) ⟨838680, by rfl⟩) R1677361
theorem R401611 : Reach 401611 := rs (se 1 (by rfl) ⟨301208, by rfl⟩) R602417
theorem R402043 : Reach 402043 := rs (se 1 (by rfl) ⟨301532, by rfl⟩) R603065
theorem R140231 : Reach 140231 := rs (se 1 (by rfl) ⟨105173, by rfl⟩) R210347
theorem R74719 : Reach 74719 := rs (se 1 (by rfl) ⟨56039, by rfl⟩) R112079
theorem R894347 : Reach 894347 := rs (se 1 (by rfl) ⟨670760, by rfl⟩) R1341521
theorem R108287 : Reach 108287 := rs (se 1 (by rfl) ⟨81215, by rfl⟩) R162431
theorem R731551 : Reach 731551 := rs (se 1 (by rfl) ⟨548663, by rfl⟩) R1097327
theorem R928279 : Reach 928279 := rs (se 1 (by rfl) ⟨696209, by rfl⟩) R1392419
theorem R928655 : Reach 928655 := rs (se 1 (by rfl) ⟨696491, by rfl⟩) R1392983
theorem R371699 : Reach 371699 := rs (se 1 (by rfl) ⟨278774, by rfl⟩) R557549
theorem R371927 : Reach 371927 := rs (se 1 (by rfl) ⟨278945, by rfl⟩) R557891
theorem R503147 : Reach 503147 := rs (se 1 (by rfl) ⟨377360, by rfl⟩) R754721
theorem R830969 : Reach 830969 := rs (se 2 (by rfl) ⟨311613, by rfl⟩) R623227
theorem R208403 : Reach 208403 := rs (se 1 (by rfl) ⟨156302, by rfl⟩) R312605
theorem R536863 : Reach 536863 := rs (se 1 (by rfl) ⟨402647, by rfl⟩) R805295
theorem R275255 : Reach 275255 := rs (se 1 (by rfl) ⟨206441, by rfl⟩) R412883
theorem R243425 : Reach 243425 := rs (se 2 (by rfl) ⟨91284, by rfl⟩) R182569
theorem R243577 : Reach 243577 := rs (se 2 (by rfl) ⟨91341, by rfl⟩) R182683
theorem R26589505 : Reach 26589505 := rs (se 2 (by rfl) ⟨9971064, by rfl⟩) R19942129
theorem R211319 : Reach 211319 := rs (se 1 (by rfl) ⟨158489, by rfl⟩) R316979
theorem R179783 : Reach 179783 := rs (se 1 (by rfl) ⟨134837, by rfl⟩) R269675
theorem R835913 : Reach 835913 := rs (se 2 (by rfl) ⟨313467, by rfl⟩) R626935
theorem R82751 : Reach 82751 := rs (se 1 (by rfl) ⟨62063, by rfl⟩) R124127
theorem R181403 : Reach 181403 := rs (se 1 (by rfl) ⟨136052, by rfl⟩) R272105
theorem R84071 : Reach 84071 := rs (se 1 (by rfl) ⟨63053, by rfl⟩) R126107
theorem R379001 : Reach 379001 := rs (se 2 (by rfl) ⟨142125, by rfl⟩) R284251
theorem R84455 : Reach 84455 := rs (se 1 (by rfl) ⟨63341, by rfl⟩) R126683
theorem R84635 : Reach 84635 := rs (se 1 (by rfl) ⟨63476, by rfl⟩) R126953
theorem R84671 : Reach 84671 := rs (se 1 (by rfl) ⟨63503, by rfl⟩) R127007
theorem R281555 : Reach 281555 := rs (se 1 (by rfl) ⟨211166, by rfl⟩) R422333
theorem R183401 : Reach 183401 := rs (se 2 (by rfl) ⟨68775, by rfl⟩) R137551
theorem R85103 : Reach 85103 := rs (se 1 (by rfl) ⟨63827, by rfl⟩) R127655
theorem R740573 : Reach 740573 := rs (se 3 (by rfl) ⟨138857, by rfl⟩) R277715
theorem R282527 : Reach 282527 := rs (se 1 (by rfl) ⟨211895, by rfl⟩) R423791
theorem R2543723 : Reach 2543723 := rs (se 1 (by rfl) ⟨1907792, by rfl⟩) R3815585
theorem R184619 : Reach 184619 := rs (se 1 (by rfl) ⟨138464, by rfl⟩) R276929
theorem R86375 : Reach 86375 := rs (se 1 (by rfl) ⟨64781, by rfl⟩) R129563
theorem R315839 : Reach 315839 := rs (se 1 (by rfl) ⟨236879, by rfl⟩) R473759
theorem R87143 : Reach 87143 := rs (se 1 (by rfl) ⟨65357, by rfl⟩) R130715
theorem R87227 : Reach 87227 := rs (se 1 (by rfl) ⟨65420, by rfl⟩) R130841
theorem R87323 : Reach 87323 := rs (se 1 (by rfl) ⟨65492, by rfl⟩) R130985
theorem R283945 : Reach 283945 := rs (se 2 (by rfl) ⟨106479, by rfl⟩) R212959
theorem R87593 : Reach 87593 := rs (se 2 (by rfl) ⟨32847, by rfl⟩) R65695
theorem R55323 : Reach 55323 := rs (se 1 (by rfl) ⟨41492, by rfl⟩) R82985
theorem R55359 : Reach 55359 := rs (se 1 (by rfl) ⟨41519, by rfl⟩) R83039
theorem R88175 : Reach 88175 := rs (se 1 (by rfl) ⟨66131, by rfl⟩) R132263
theorem R317753 : Reach 317753 := rs (se 2 (by rfl) ⟨119157, by rfl⟩) R238315
theorem R187487 : Reach 187487 := rs (se 1 (by rfl) ⟨140615, by rfl⟩) R281231
theorem R908495 : Reach 908495 := rs (se 1 (by rfl) ⟨681371, by rfl⟩) R1362743
theorem R56559 : Reach 56559 := rs (se 1 (by rfl) ⟨42419, by rfl⟩) R84839
theorem R56815 : Reach 56815 := rs (se 1 (by rfl) ⟨42611, by rfl⟩) R85223
theorem R417383 : Reach 417383 := rs (se 1 (by rfl) ⟨313037, by rfl⟩) R626075
theorem R57339 : Reach 57339 := rs (se 1 (by rfl) ⟨43004, by rfl⟩) R86009
theorem R1531993 : Reach 1531993 := rs (se 2 (by rfl) ⟨574497, by rfl⟩) R1148995
theorem R57499 : Reach 57499 := rs (se 1 (by rfl) ⟨43124, by rfl⟩) R86249
theorem R57703 : Reach 57703 := rs (se 1 (by rfl) ⟨43277, by rfl⟩) R86555
theorem R57831 : Reach 57831 := rs (se 1 (by rfl) ⟨43373, by rfl⟩) R86747
theorem R58139 : Reach 58139 := rs (se 1 (by rfl) ⟨43604, by rfl⟩) R87209
theorem R58235 : Reach 58235 := rs (se 1 (by rfl) ⟨43676, by rfl⟩) R87353
theorem R582713 : Reach 582713 := rs (se 2 (by rfl) ⟨218517, by rfl⟩) R437035
theorem R58727 : Reach 58727 := rs (se 1 (by rfl) ⟨44045, by rfl⟩) R88091
theorem R58751 : Reach 58751 := rs (se 1 (by rfl) ⟨44063, by rfl⟩) R88127
theorem R615863 : Reach 615863 := rs (se 1 (by rfl) ⟨461897, by rfl⟩) R923795
theorem R58831 : Reach 58831 := rs (se 1 (by rfl) ⟨44123, by rfl⟩) R88247
theorem R321167 : Reach 321167 := rs (se 1 (by rfl) ⟨240875, by rfl⟩) R481751
theorem R845549 : Reach 845549 := rs (se 3 (by rfl) ⟨158540, by rfl⟩) R317081
theorem R92537 : Reach 92537 := rs (se 2 (by rfl) ⟨34701, by rfl⟩) R69403
theorem R125423 : Reach 125423 := rs (se 1 (by rfl) ⟨94067, by rfl⟩) R188135
theorem R93467 : Reach 93467 := rs (se 1 (by rfl) ⟨70100, by rfl⟩) R140201
theorem R93737 : Reach 93737 := rs (se 2 (by rfl) ⟨35151, by rfl⟩) R70303
theorem R127079 : Reach 127079 := rs (se 1 (by rfl) ⟨95309, by rfl⟩) R190619
theorem R290951 : Reach 290951 := rs (se 1 (by rfl) ⟨218213, by rfl⟩) R436427
theorem R323837 : Reach 323837 := rs (se 3 (by rfl) ⟨60719, by rfl⟩) R121439
theorem R192887 : Reach 192887 := rs (se 1 (by rfl) ⟨144665, by rfl⟩) R289331
theorem R553355 : Reach 553355 := rs (se 1 (by rfl) ⟨415016, by rfl⟩) R830033
theorem R127979 : Reach 127979 := rs (se 1 (by rfl) ⟨95984, by rfl⟩) R191969
theorem R325727 : Reach 325727 := rs (se 1 (by rfl) ⟨244295, by rfl⟩) R488591
theorem R227431 : Reach 227431 := rs (se 1 (by rfl) ⟨170573, by rfl⟩) R341147
theorem R424415 : Reach 424415 := rs (se 1 (by rfl) ⟨318311, by rfl⟩) R636623
theorem R96815 : Reach 96815 := rs (se 1 (by rfl) ⟨72611, by rfl⟩) R145223
theorem R129743 : Reach 129743 := rs (se 1 (by rfl) ⟨97307, by rfl⟩) R194615
theorem R162557 : Reach 162557 := rs (se 3 (by rfl) ⟨30479, by rfl⟩) R60959
theorem R64615 : Reach 64615 := rs (se 1 (by rfl) ⟨48461, by rfl⟩) R96923
theorem R818383 : Reach 818383 := rs (se 1 (by rfl) ⟨613787, by rfl⟩) R1227575
theorem R491255 : Reach 491255 := rs (se 1 (by rfl) ⟨368441, by rfl⟩) R736883
theorem R130913 : Reach 130913 := rs (se 2 (by rfl) ⟨49092, by rfl⟩) R98185
theorem R163775 : Reach 163775 := rs (se 1 (by rfl) ⟨122831, by rfl⟩) R245663
theorem R196775 : Reach 196775 := rs (se 1 (by rfl) ⟨147581, by rfl⟩) R295163
theorem R557275 : Reach 557275 := rs (se 1 (by rfl) ⟨417956, by rfl⟩) R835913
theorem R4129055 : Reach 4129055 := rs (se 1 (by rfl) ⟨3096791, by rfl⟩) R6193583
theorem R1212965 : Reach 1212965 := rs (se 4 (by rfl) ⟨113715, by rfl⟩) R227431
theorem R492317 : Reach 492317 := rs (se 3 (by rfl) ⟨92309, by rfl⟩) R184619
theorem R99625 : Reach 99625 := rs (se 2 (by rfl) ⟨37359, by rfl⟩) R74719
theorem R67199 : Reach 67199 := rs (se 1 (by rfl) ⟨50399, by rfl⟩) R100799
theorem R132839 : Reach 132839 := rs (se 1 (by rfl) ⟨99629, by rfl⟩) R199259
theorem R493715 : Reach 493715 := rs (se 1 (by rfl) ⟨370286, by rfl⟩) R740573
theorem R133289 : Reach 133289 := rs (se 2 (by rfl) ⟨49983, by rfl⟩) R99967
theorem R4197095 : Reach 4197095 := rs (se 1 (by rfl) ⟨3147821, by rfl⟩) R6295643
theorem R4950821 : Reach 4950821 := rs (se 4 (by rfl) ⟨464139, by rfl⟩) R928279
theorem R527809 : Reach 527809 := rs (se 2 (by rfl) ⟨197928, by rfl⟩) R395857
theorem R1642301 : Reach 1642301 := rs (se 3 (by rfl) ⟨307931, by rfl⟩) R615863
theorem R266387 : Reach 266387 := rs (se 1 (by rfl) ⟨199790, by rfl⟩) R399581
theorem R3020111 : Reach 3020111 := rs (se 1 (by rfl) ⟨2265083, by rfl⟩) R4530167
theorem R71015 : Reach 71015 := rs (se 1 (by rfl) ⟨53261, by rfl⟩) R106523
theorem R596231 : Reach 596231 := rs (se 1 (by rfl) ⟨447173, by rfl⟩) R894347
theorem R563699 : Reach 563699 := rs (se 1 (by rfl) ⟨422774, by rfl⟩) R845549
theorem R72191 : Reach 72191 := rs (se 1 (by rfl) ⟨54143, by rfl⟩) R108287
theorem R335431 : Reach 335431 := rs (se 1 (by rfl) ⟨251573, by rfl⟩) R503147
theorem R138935 : Reach 138935 := rs (se 1 (by rfl) ⟨104201, by rfl⟩) R208403
theorem R368903 : Reach 368903 := rs (se 1 (by rfl) ⟨276677, by rfl⟩) R553355
theorem R140879 : Reach 140879 := rs (se 1 (by rfl) ⟨105659, by rfl⟩) R211319
theorem R1091177 : Reach 1091177 := rs (se 2 (by rfl) ⟨409191, by rfl⟩) R818383
theorem R108371 : Reach 108371 := rs (se 1 (by rfl) ⟨81278, by rfl⟩) R162557
theorem R3188645 : Reach 3188645 := rs (se 4 (by rfl) ⟨298935, by rfl⟩) R597871
theorem R141385 : Reach 141385 := rs (se 2 (by rfl) ⟨53019, by rfl⟩) R106039
theorem R109183 : Reach 109183 := rs (se 1 (by rfl) ⟨81887, by rfl⟩) R163775
theorem R109343 : Reach 109343 := rs (se 1 (by rfl) ⟨82007, by rfl⟩) R164015
theorem R2042657 : Reach 2042657 := rs (se 2 (by rfl) ⟨765996, by rfl⟩) R1531993
theorem R535481 : Reach 535481 := rs (se 2 (by rfl) ⟨200805, by rfl⟩) R401611
theorem R536057 : Reach 536057 := rs (se 2 (by rfl) ⟨201021, by rfl⟩) R402043
theorem R110747 : Reach 110747 := rs (se 1 (by rfl) ⟨83060, by rfl⟩) R166121
theorem R373157 : Reach 373157 := rs (se 4 (by rfl) ⟨34983, by rfl⟩) R69967
theorem R111955 : Reach 111955 := rs (se 1 (by rfl) ⟨83966, by rfl⟩) R167933
theorem R210559 : Reach 210559 := rs (se 1 (by rfl) ⟨157919, by rfl⟩) R315839
theorem R4110365 : Reach 4110365 := rs (se 3 (by rfl) ⟨770693, by rfl⟩) R1541387
theorem R211835 : Reach 211835 := rs (se 1 (by rfl) ⟨158876, by rfl⟩) R317753
theorem R605663 : Reach 605663 := rs (se 1 (by rfl) ⟨454247, by rfl⟩) R908495
theorem R278255 : Reach 278255 := rs (se 1 (by rfl) ⟨208691, by rfl⟩) R417383
theorem R1490987 : Reach 1490987 := rs (se 1 (by rfl) ⟨1118240, by rfl⟩) R2236481
theorem R214111 : Reach 214111 := rs (se 1 (by rfl) ⟨160583, by rfl⟩) R321167
theorem R83615 : Reach 83615 := rs (se 1 (by rfl) ⟨62711, by rfl⟩) R125423
theorem R378593 : Reach 378593 := rs (se 2 (by rfl) ⟨141972, by rfl⟩) R283945
theorem R247799 : Reach 247799 := rs (se 1 (by rfl) ⟨185849, by rfl⟩) R371699
theorem R247951 : Reach 247951 := rs (se 1 (by rfl) ⟨185963, by rfl⟩) R371927
theorem R84719 : Reach 84719 := rs (se 1 (by rfl) ⟨63539, by rfl⟩) R127079
theorem R215891 : Reach 215891 := rs (se 1 (by rfl) ⟨161918, by rfl⟩) R323837
theorem R183503 : Reach 183503 := rs (se 1 (by rfl) ⟨137627, by rfl⟩) R275255
theorem R85319 : Reach 85319 := rs (se 1 (by rfl) ⟨63989, by rfl⟩) R127979
theorem R217151 : Reach 217151 := rs (se 1 (by rfl) ⟨162863, by rfl⟩) R325727
theorem R86153 : Reach 86153 := rs (se 2 (by rfl) ⟨32307, by rfl⟩) R64615
theorem R282943 : Reach 282943 := rs (se 1 (by rfl) ⟨212207, by rfl⟩) R424415
theorem R86495 : Reach 86495 := rs (se 1 (by rfl) ⟨64871, by rfl⟩) R129743
theorem R119855 : Reach 119855 := rs (se 1 (by rfl) ⟨89891, by rfl⟩) R179783
theorem R87275 : Reach 87275 := rs (se 1 (by rfl) ⟨65456, by rfl⟩) R130913
theorem R218729 : Reach 218729 := rs (se 2 (by rfl) ⟨82023, by rfl⟩) R164047
theorem R55167 : Reach 55167 := rs (se 1 (by rfl) ⟨41375, by rfl⟩) R82751
theorem R88031 : Reach 88031 := rs (se 1 (by rfl) ⟨66023, by rfl⟩) R132047
theorem R120935 : Reach 120935 := rs (se 1 (by rfl) ⟨90701, by rfl⟩) R181403
theorem R56047 : Reach 56047 := rs (se 1 (by rfl) ⟨42035, by rfl⟩) R84071
theorem R252667 : Reach 252667 := rs (se 1 (by rfl) ⟨189500, by rfl⟩) R379001
theorem R56303 : Reach 56303 := rs (se 1 (by rfl) ⟨42227, by rfl⟩) R84455
theorem R56423 : Reach 56423 := rs (se 1 (by rfl) ⟨42317, by rfl⟩) R84635
theorem R56447 : Reach 56447 := rs (se 1 (by rfl) ⟨42335, by rfl⟩) R84671
theorem R187703 : Reach 187703 := rs (se 1 (by rfl) ⟨140777, by rfl⟩) R281555
theorem R122267 : Reach 122267 := rs (se 1 (by rfl) ⟨91700, by rfl⟩) R183401
theorem R56735 : Reach 56735 := rs (se 1 (by rfl) ⟨42551, by rfl⟩) R85103
theorem R188351 : Reach 188351 := rs (se 1 (by rfl) ⟨141263, by rfl⟩) R282527
theorem R1695815 : Reach 1695815 := rs (se 1 (by rfl) ⟨1271861, by rfl⟩) R2543723
theorem R57583 : Reach 57583 := rs (se 1 (by rfl) ⟨43187, by rfl⟩) R86375
theorem R975401 : Reach 975401 := rs (se 2 (by rfl) ⟨365775, by rfl⟩) R731551
theorem R58095 : Reach 58095 := rs (se 1 (by rfl) ⟨43571, by rfl⟩) R87143
theorem R58151 : Reach 58151 := rs (se 1 (by rfl) ⟨43613, by rfl⟩) R87227
theorem R58215 : Reach 58215 := rs (se 1 (by rfl) ⟨43661, by rfl⟩) R87323
theorem R484217 : Reach 484217 := rs (se 2 (by rfl) ⟨181581, by rfl⟩) R363163
theorem R58395 : Reach 58395 := rs (se 1 (by rfl) ⟨43796, by rfl⟩) R87593
theorem R418879 : Reach 418879 := rs (se 1 (by rfl) ⟨314159, by rfl⟩) R628319
theorem R58783 : Reach 58783 := rs (se 1 (by rfl) ⟨44087, by rfl⟩) R88175
theorem R124991 : Reach 124991 := rs (se 1 (by rfl) ⟨93743, by rfl⟩) R187487
theorem R715817 : Reach 715817 := rs (se 2 (by rfl) ⟨268431, by rfl⟩) R536863
theorem R93487 : Reach 93487 := rs (se 1 (by rfl) ⟨70115, by rfl⟩) R140231
theorem R388475 : Reach 388475 := rs (se 1 (by rfl) ⟨291356, by rfl⟩) R582713
theorem R61691 : Reach 61691 := rs (se 1 (by rfl) ⟨46268, by rfl⟩) R92537
theorem R619103 : Reach 619103 := rs (se 1 (by rfl) ⟨464327, by rfl⟩) R928655
theorem R62311 : Reach 62311 := rs (se 1 (by rfl) ⟨46733, by rfl⟩) R93467
theorem R553979 : Reach 553979 := rs (se 1 (by rfl) ⟨415484, by rfl⟩) R830969
theorem R62491 : Reach 62491 := rs (se 1 (by rfl) ⟨46868, by rfl⟩) R93737
theorem R324769 : Reach 324769 := rs (se 2 (by rfl) ⟨121788, by rfl⟩) R243577
theorem R193967 : Reach 193967 := rs (se 1 (by rfl) ⟨145475, by rfl⟩) R290951
theorem R128591 : Reach 128591 := rs (se 1 (by rfl) ⟨96443, by rfl⟩) R192887
theorem R35452673 : Reach 35452673 := rs (se 2 (by rfl) ⟨13294752, by rfl⟩) R26589505
theorem R162283 : Reach 162283 := rs (se 1 (by rfl) ⟨121712, by rfl⟩) R243425
theorem R64543 : Reach 64543 := rs (se 1 (by rfl) ⟨48407, by rfl⟩) R96815
theorem R1014905 : Reach 1014905 := rs (se 2 (by rfl) ⟨380589, by rfl⟩) R761179
theorem R228577 : Reach 228577 := rs (se 2 (by rfl) ⟨85716, by rfl⟩) R171433
theorem R327503 : Reach 327503 := rs (se 1 (by rfl) ⟨245627, by rfl⟩) R491255
theorem R131183 : Reach 131183 := rs (se 1 (by rfl) ⟨98387, by rfl⟩) R196775
theorem R2752703 : Reach 2752703 := rs (se 1 (by rfl) ⟨2064527, by rfl⟩) R4129055
theorem R295325 : Reach 295325 := rs (se 3 (by rfl) ⟨55373, by rfl⟩) R110747
theorem R328211 : Reach 328211 := rs (se 1 (by rfl) ⟨246158, by rfl⟩) R492317
theorem R165199 : Reach 165199 := rs (se 1 (by rfl) ⟨123899, by rfl⟩) R247799
theorem R558505 : Reach 558505 := rs (se 2 (by rfl) ⟨209439, by rfl⟩) R418879
theorem R329143 : Reach 329143 := rs (se 1 (by rfl) ⟨246857, by rfl⟩) R493715
theorem R1509029 : Reach 1509029 := rs (se 4 (by rfl) ⟨141471, by rfl⟩) R282943
theorem R132833 : Reach 132833 := rs (se 2 (by rfl) ⟨49812, by rfl⟩) R99625
theorem R658037 : Reach 658037 := rs (se 5 (by rfl) ⟨30845, by rfl⟩) R61691
theorem R330601 : Reach 330601 := rs (se 2 (by rfl) ⟨123975, by rfl⟩) R247951
theorem R397487 : Reach 397487 := rs (se 1 (by rfl) ⟨298115, by rfl⟩) R596231
theorem R727451 : Reach 727451 := rs (se 1 (by rfl) ⟨545588, by rfl⟩) R1091177
theorem R72247 : Reach 72247 := rs (se 1 (by rfl) ⟨54185, by rfl⟩) R108371
theorem R433025 : Reach 433025 := rs (se 2 (by rfl) ⟨162384, by rfl⟩) R324769
theorem R72895 : Reach 72895 := rs (se 1 (by rfl) ⟨54671, by rfl⟩) R109343
theorem R369319 : Reach 369319 := rs (se 1 (by rfl) ⟨276989, by rfl⟩) R553979
theorem R336889 : Reach 336889 := rs (se 2 (by rfl) ⟨126333, by rfl⟩) R252667
theorem R23635115 : Reach 23635115 := rs (se 1 (by rfl) ⟨17726336, by rfl⟩) R35452673
theorem R304769 : Reach 304769 := rs (se 2 (by rfl) ⟨114288, by rfl⟩) R228577
theorem R370493 : Reach 370493 := rs (se 3 (by rfl) ⟨69467, by rfl⟩) R138935
theorem R141223 : Reach 141223 := rs (se 1 (by rfl) ⟨105917, by rfl⟩) R211835
theorem R403775 : Reach 403775 := rs (se 1 (by rfl) ⟨302831, by rfl⟩) R605663
theorem R3975965 : Reach 3975965 := rs (se 3 (by rfl) ⟨745493, by rfl⟩) R1490987
theorem R1650941 : Reach 1650941 := rs (se 3 (by rfl) ⟨309551, by rfl⟩) R619103
theorem R2798063 : Reach 2798063 := rs (se 1 (by rfl) ⟨2098547, by rfl⟩) R4197095
theorem R143927 : Reach 143927 := rs (se 1 (by rfl) ⟨107945, by rfl⟩) R215891
theorem R1094867 : Reach 1094867 := rs (se 1 (by rfl) ⟨821150, by rfl⟩) R1642301
theorem R144767 : Reach 144767 := rs (se 1 (by rfl) ⟨108575, by rfl⟩) R217151
theorem R79903 : Reach 79903 := rs (se 1 (by rfl) ⟨59927, by rfl⟩) R119855
theorem R145577 : Reach 145577 := rs (se 2 (by rfl) ⟨54591, by rfl⟩) R109183
theorem R2013407 : Reach 2013407 := rs (se 1 (by rfl) ⟨1510055, by rfl⟩) R3020111
theorem R145819 : Reach 145819 := rs (se 1 (by rfl) ⟨109364, by rfl⟩) R218729
theorem R80623 : Reach 80623 := rs (se 1 (by rfl) ⟨60467, by rfl⟩) R120935
theorem R375799 : Reach 375799 := rs (se 1 (by rfl) ⟨281849, by rfl⟩) R563699
theorem R703745 : Reach 703745 := rs (se 2 (by rfl) ⟨263904, by rfl⟩) R527809
theorem R1130543 : Reach 1130543 := rs (se 1 (by rfl) ⟨847907, by rfl⟩) R1695815
theorem R245935 : Reach 245935 := rs (se 1 (by rfl) ⟨184451, by rfl⟩) R368903
theorem R83081 : Reach 83081 := rs (se 2 (by rfl) ⟨31155, by rfl⟩) R62311
theorem R83321 : Reach 83321 := rs (se 2 (by rfl) ⟨31245, by rfl⟩) R62491
theorem R83327 : Reach 83327 := rs (se 1 (by rfl) ⟨62495, by rfl⟩) R124991
theorem R149273 : Reach 149273 := rs (se 2 (by rfl) ⟨55977, by rfl⟩) R111955
theorem R1361771 : Reach 1361771 := rs (se 1 (by rfl) ⟨1021328, by rfl⟩) R2042657
theorem R477211 : Reach 477211 := rs (se 1 (by rfl) ⟨357908, by rfl⟩) R715817
theorem R280745 : Reach 280745 := rs (se 2 (by rfl) ⟨105279, by rfl⟩) R210559
theorem R248771 : Reach 248771 := rs (se 1 (by rfl) ⟨186578, by rfl⟩) R373157
theorem R216377 : Reach 216377 := rs (se 2 (by rfl) ⟨81141, by rfl⟩) R162283
theorem R85727 : Reach 85727 := rs (se 1 (by rfl) ⟨64295, by rfl⟩) R128591
theorem R2740243 : Reach 2740243 := rs (se 1 (by rfl) ⟨2055182, by rfl⟩) R4110365
theorem R86057 : Reach 86057 := rs (se 2 (by rfl) ⟨32271, by rfl⟩) R64543
theorem R676603 : Reach 676603 := rs (se 1 (by rfl) ⟨507452, by rfl⟩) R1014905
theorem R447241 : Reach 447241 := rs (se 2 (by rfl) ⟨167715, by rfl⟩) R335431
theorem R185503 : Reach 185503 := rs (se 1 (by rfl) ⟨139127, by rfl⟩) R278255
theorem R218335 : Reach 218335 := rs (se 1 (by rfl) ⟨163751, by rfl⟩) R327503
theorem R743033 : Reach 743033 := rs (se 2 (by rfl) ⟨278637, by rfl⟩) R557275
theorem R808643 : Reach 808643 := rs (se 1 (by rfl) ⟨606482, by rfl⟩) R1212965
theorem R710365 : Reach 710365 := rs (se 3 (by rfl) ⟨133193, by rfl⟩) R266387
theorem R55743 : Reach 55743 := rs (se 1 (by rfl) ⟨41807, by rfl⟩) R83615
theorem R88559 : Reach 88559 := rs (se 1 (by rfl) ⟨66419, by rfl⟩) R132839
theorem R252395 : Reach 252395 := rs (se 1 (by rfl) ⟨189296, by rfl⟩) R378593
theorem R88859 : Reach 88859 := rs (se 1 (by rfl) ⟨66644, by rfl⟩) R133289
theorem R285481 : Reach 285481 := rs (se 2 (by rfl) ⟨107055, by rfl⟩) R214111
theorem R56479 : Reach 56479 := rs (se 1 (by rfl) ⟨42359, by rfl⟩) R84719
theorem R56879 : Reach 56879 := rs (se 1 (by rfl) ⟨42659, by rfl⟩) R85319
theorem R57435 : Reach 57435 := rs (se 1 (by rfl) ⟨43076, by rfl⟩) R86153
theorem R188513 : Reach 188513 := rs (se 2 (by rfl) ⟨70692, by rfl⟩) R141385
theorem R57663 : Reach 57663 := rs (se 1 (by rfl) ⟨43247, by rfl⟩) R86495
theorem R58183 : Reach 58183 := rs (se 1 (by rfl) ⟨43637, by rfl⟩) R87275
theorem R189373 : Reach 189373 := rs (se 3 (by rfl) ⟨35507, by rfl⟩) R71015
theorem R58687 : Reach 58687 := rs (se 1 (by rfl) ⟨44015, by rfl⟩) R88031
theorem R124649 : Reach 124649 := rs (se 2 (by rfl) ⟨46743, by rfl⟩) R93487
theorem R125135 : Reach 125135 := rs (se 1 (by rfl) ⟨93851, by rfl⟩) R187703
theorem R125567 : Reach 125567 := rs (se 1 (by rfl) ⟨94175, by rfl⟩) R188351
theorem R650267 : Reach 650267 := rs (se 1 (by rfl) ⟨487700, by rfl⟩) R975401
theorem R322811 : Reach 322811 := rs (se 1 (by rfl) ⟨242108, by rfl⟩) R484217
theorem R93919 : Reach 93919 := rs (se 1 (by rfl) ⟨70439, by rfl⟩) R140879
theorem R2125763 : Reach 2125763 := rs (se 1 (by rfl) ⟨1594322, by rfl⟩) R3188645
theorem R716789 : Reach 716789 := rs (se 5 (by rfl) ⟨33599, by rfl⟩) R67199
theorem R192509 : Reach 192509 := rs (se 3 (by rfl) ⟨36095, by rfl⟩) R72191
theorem R356987 : Reach 356987 := rs (se 1 (by rfl) ⟨267740, by rfl⟩) R535481
theorem R13202189 : Reach 13202189 := rs (se 3 (by rfl) ⟨2475410, by rfl⟩) R4950821
theorem R258983 : Reach 258983 := rs (se 1 (by rfl) ⟨194237, by rfl⟩) R388475
theorem R357371 : Reach 357371 := rs (se 1 (by rfl) ⟨268028, by rfl⟩) R536057
theorem R489341 : Reach 489341 := rs (se 3 (by rfl) ⟨91751, by rfl⟩) R183503
theorem R129311 : Reach 129311 := rs (se 1 (by rfl) ⟨96983, by rfl⟩) R193967
theorem R326045 : Reach 326045 := rs (se 3 (by rfl) ⟨61133, by rfl⟩) R122267
theorem R753695 : Reach 753695 := rs (se 1 (by rfl) ⟨565271, by rfl⟩) R1130543
theorem R1835135 : Reach 1835135 := rs (se 1 (by rfl) ⟨1376351, by rfl⟩) R2752703
theorem R196883 : Reach 196883 := rs (se 1 (by rfl) ⟨147662, by rfl⟩) R295325
theorem R492425 : Reach 492425 := rs (se 2 (by rfl) ⟨184659, by rfl⟩) R369319
theorem R1311653 : Reach 1311653 := rs (se 4 (by rfl) ⟨122967, by rfl⟩) R245935
theorem R99515 : Reach 99515 := rs (se 1 (by rfl) ⟨74636, by rfl⟩) R149273
theorem R495355 : Reach 495355 := rs (se 1 (by rfl) ⟨371516, by rfl⟩) R743033
theorem R168263 : Reach 168263 := rs (se 1 (by rfl) ⟨126197, by rfl⟩) R252395
theorem R596321 : Reach 596321 := rs (se 2 (by rfl) ⟨223620, by rfl⟩) R447241
theorem R269183 : Reach 269183 := rs (se 1 (by rfl) ⟨201887, by rfl⟩) R403775
theorem R433511 : Reach 433511 := rs (se 1 (by rfl) ⟨325133, by rfl⟩) R650267
theorem R663389 : Reach 663389 := rs (se 3 (by rfl) ⟨124385, by rfl⟩) R248771
theorem R1417175 : Reach 1417175 := rs (se 1 (by rfl) ⟨1062881, by rfl⟩) R2125763
theorem R106537 : Reach 106537 := rs (se 2 (by rfl) ⟨39951, by rfl⟩) R79903
theorem R237991 : Reach 237991 := rs (se 1 (by rfl) ⟨178493, by rfl⟩) R356987
theorem R172655 : Reach 172655 := rs (se 1 (by rfl) ⟨129491, by rfl⟩) R258983
theorem R238247 : Reach 238247 := rs (se 1 (by rfl) ⟨178685, by rfl⟩) R357371
theorem R729911 : Reach 729911 := rs (se 1 (by rfl) ⟨547433, by rfl⟩) R1094867
theorem R107497 : Reach 107497 := rs (se 2 (by rfl) ⟨40311, by rfl⟩) R80623
theorem R501065 : Reach 501065 := rs (se 2 (by rfl) ⟨187899, by rfl⟩) R375799
theorem R469163 : Reach 469163 := rs (se 1 (by rfl) ⟨351872, by rfl⟩) R703745
theorem R1911437 : Reach 1911437 := rs (se 3 (by rfl) ⟨358394, by rfl⟩) R716789
theorem R1059965 : Reach 1059965 := rs (se 3 (by rfl) ⟨198743, by rfl⟩) R397487
theorem R438691 : Reach 438691 := rs (se 1 (by rfl) ⟨329018, by rfl⟩) R658037
theorem R438857 : Reach 438857 := rs (se 2 (by rfl) ⟨164571, by rfl⟩) R329143
theorem R144251 : Reach 144251 := rs (se 1 (by rfl) ⟨108188, by rfl⟩) R216377
theorem R636281 : Reach 636281 := rs (se 2 (by rfl) ⟨238605, by rfl⟩) R477211
theorem R539095 : Reach 539095 := rs (se 1 (by rfl) ⟨404321, by rfl⟩) R808643
theorem R440801 : Reach 440801 := rs (se 2 (by rfl) ⟨165300, by rfl⟩) R330601
theorem R3653657 : Reach 3653657 := rs (se 2 (by rfl) ⟨1370121, by rfl⟩) R2740243
theorem R902137 : Reach 902137 := rs (se 2 (by rfl) ⟨338301, by rfl⟩) R676603
theorem R83099 : Reach 83099 := rs (se 1 (by rfl) ⟨62324, by rfl⟩) R124649
theorem R246995 : Reach 246995 := rs (se 1 (by rfl) ⟨185246, by rfl⟩) R370493
theorem R83423 : Reach 83423 := rs (se 1 (by rfl) ⟨62567, by rfl⟩) R125135
theorem R247337 : Reach 247337 := rs (se 2 (by rfl) ⟨92751, by rfl⟩) R185503
theorem R83711 : Reach 83711 := rs (se 1 (by rfl) ⟨62783, by rfl⟩) R125567
theorem R215207 : Reach 215207 := rs (se 1 (by rfl) ⟨161405, by rfl⟩) R322811
theorem R477859 : Reach 477859 := rs (se 1 (by rfl) ⟨358394, by rfl⟩) R716789
theorem R1100627 : Reach 1100627 := rs (se 1 (by rfl) ⟨825470, by rfl⟩) R1650941
theorem R8801459 : Reach 8801459 := rs (se 1 (by rfl) ⟨6601094, by rfl⟩) R13202189
theorem R380641 : Reach 380641 := rs (se 2 (by rfl) ⟨142740, by rfl⟩) R285481
theorem R86207 : Reach 86207 := rs (se 1 (by rfl) ⟨64655, by rfl⟩) R129311
theorem R217363 : Reach 217363 := rs (se 1 (by rfl) ⟨163022, by rfl⟩) R326045
theorem R87455 : Reach 87455 := rs (se 1 (by rfl) ⟨65591, by rfl⟩) R131183
theorem R218807 : Reach 218807 := rs (se 1 (by rfl) ⟨164105, by rfl⟩) R328211
theorem R55387 : Reach 55387 := rs (se 1 (by rfl) ⟨41540, by rfl⟩) R83081
theorem R55547 : Reach 55547 := rs (se 1 (by rfl) ⟨41660, by rfl⟩) R83321
theorem R55551 : Reach 55551 := rs (se 1 (by rfl) ⟨41663, by rfl⟩) R83327
theorem R1006019 : Reach 1006019 := rs (se 1 (by rfl) ⟨754514, by rfl⟩) R1509029
theorem R88555 : Reach 88555 := rs (se 1 (by rfl) ⟨66416, by rfl⟩) R132833
theorem R907847 : Reach 907847 := rs (se 1 (by rfl) ⟨680885, by rfl⟩) R1361771
theorem R252497 : Reach 252497 := rs (se 2 (by rfl) ⟨94686, by rfl⟩) R189373
theorem R449185 : Reach 449185 := rs (se 2 (by rfl) ⟨168444, by rfl⟩) R336889
theorem R187163 : Reach 187163 := rs (se 1 (by rfl) ⟨140372, by rfl⟩) R280745
theorem R220265 : Reach 220265 := rs (se 2 (by rfl) ⟨82599, by rfl⟩) R165199
theorem R744673 : Reach 744673 := rs (se 2 (by rfl) ⟨279252, by rfl⟩) R558505
theorem R777701 : Reach 777701 := rs (se 4 (by rfl) ⟨72909, by rfl⟩) R145819
theorem R57151 : Reach 57151 := rs (se 1 (by rfl) ⟨42863, by rfl⟩) R85727
theorem R188297 : Reach 188297 := rs (se 2 (by rfl) ⟨70611, by rfl⟩) R141223
theorem R57371 : Reach 57371 := rs (se 1 (by rfl) ⟨43028, by rfl⟩) R86057
theorem R484967 : Reach 484967 := rs (se 1 (by rfl) ⟨363725, by rfl⟩) R727451
theorem R59039 : Reach 59039 := rs (se 1 (by rfl) ⟨44279, by rfl⟩) R88559
theorem R812717 : Reach 812717 := rs (se 3 (by rfl) ⟨152384, by rfl⟩) R304769
theorem R59239 : Reach 59239 := rs (se 1 (by rfl) ⟨44429, by rfl⟩) R88859
theorem R288683 : Reach 288683 := rs (se 1 (by rfl) ⟨216512, by rfl⟩) R433025
theorem R125225 : Reach 125225 := rs (se 2 (by rfl) ⟨46959, by rfl⟩) R93919
theorem R125675 : Reach 125675 := rs (se 1 (by rfl) ⟨94256, by rfl⟩) R188513
theorem R15756743 : Reach 15756743 := rs (se 1 (by rfl) ⟨11817557, by rfl⟩) R23635115
theorem R291113 : Reach 291113 := rs (se 2 (by rfl) ⟨109167, by rfl⟩) R218335
theorem R2650643 : Reach 2650643 := rs (se 1 (by rfl) ⟨1987982, by rfl⟩) R3975965
theorem R947153 : Reach 947153 := rs (se 2 (by rfl) ⟨355182, by rfl⟩) R710365
theorem R128339 : Reach 128339 := rs (se 1 (by rfl) ⟨96254, by rfl⟩) R192509
theorem R1865375 : Reach 1865375 := rs (se 1 (by rfl) ⟨1399031, by rfl⟩) R2798063
theorem R95951 : Reach 95951 := rs (se 1 (by rfl) ⟨71963, by rfl⟩) R143927
theorem R96329 : Reach 96329 := rs (se 2 (by rfl) ⟨36123, by rfl⟩) R72247
theorem R96511 : Reach 96511 := rs (se 1 (by rfl) ⟨72383, by rfl⟩) R144767
theorem R326227 : Reach 326227 := rs (se 1 (by rfl) ⟨244670, by rfl⟩) R489341
theorem R97051 : Reach 97051 := rs (se 1 (by rfl) ⟨72788, by rfl⟩) R145577
theorem R1342271 : Reach 1342271 := rs (se 1 (by rfl) ⟨1006703, by rfl⟩) R2013407
theorem R97193 : Reach 97193 := rs (se 2 (by rfl) ⟨36447, by rfl⟩) R72895
theorem R131255 : Reach 131255 := rs (se 1 (by rfl) ⟨98441, by rfl⟩) R196883
theorem R328283 : Reach 328283 := rs (se 1 (by rfl) ⟨246212, by rfl⟩) R492425
theorem R66343 : Reach 66343 := rs (se 1 (by rfl) ⟨49757, by rfl⟩) R99515
theorem R164663 : Reach 164663 := rs (se 1 (by rfl) ⟨123497, by rfl⟩) R246995
theorem R164891 : Reach 164891 := rs (se 1 (by rfl) ⟨123668, by rfl⟩) R247337
theorem R5867639 : Reach 5867639 := rs (se 1 (by rfl) ⟨4400729, by rfl⟩) R8801459
theorem R397547 : Reach 397547 := rs (se 1 (by rfl) ⟨298160, by rfl⟩) R596321
theorem R168331 : Reach 168331 := rs (se 1 (by rfl) ⟨126248, by rfl⟩) R252497
theorem R660473 : Reach 660473 := rs (se 2 (by rfl) ⟨247677, by rfl⟩) R495355
theorem R1251101 : Reach 1251101 := rs (se 3 (by rfl) ⟨234581, by rfl⟩) R469163
theorem R334043 : Reach 334043 := rs (se 1 (by rfl) ⟨250532, by rfl⟩) R501065
theorem R3579389 : Reach 3579389 := rs (se 3 (by rfl) ⟨671135, by rfl⟩) R1342271
theorem R631435 : Reach 631435 := rs (se 1 (by rfl) ⟨473576, by rfl⟩) R947153
theorem R434969 : Reach 434969 := rs (se 2 (by rfl) ⟨163113, by rfl⟩) R326227
theorem R598913 : Reach 598913 := rs (se 2 (by rfl) ⟨224592, by rfl⟩) R449185
theorem R2073869 : Reach 2073869 := rs (se 3 (by rfl) ⟨388850, by rfl⟩) R777701
theorem R992897 : Reach 992897 := rs (se 2 (by rfl) ⟨372336, by rfl⟩) R744673
theorem R2435771 : Reach 2435771 := rs (se 1 (by rfl) ⟨1826828, by rfl⟩) R3653657
theorem R502463 : Reach 502463 := rs (se 1 (by rfl) ⟨376847, by rfl⟩) R753695
theorem R142049 : Reach 142049 := rs (se 2 (by rfl) ⟨53268, by rfl⟩) R106537
theorem R1223423 : Reach 1223423 := rs (se 1 (by rfl) ⟨917567, by rfl⟩) R1835135
theorem R143329 : Reach 143329 := rs (se 2 (by rfl) ⟨53748, by rfl⟩) R107497
theorem R143471 : Reach 143471 := rs (se 1 (by rfl) ⟨107603, by rfl⟩) R215207
theorem R733751 : Reach 733751 := rs (se 1 (by rfl) ⟨550313, by rfl⟩) R1100627
theorem R78985 : Reach 78985 := rs (se 2 (by rfl) ⟨29619, by rfl⟩) R59239
theorem R112175 : Reach 112175 := rs (se 1 (by rfl) ⟨84131, by rfl⟩) R168263
theorem R637145 : Reach 637145 := rs (se 2 (by rfl) ⟨238929, by rfl⟩) R477859
theorem R145871 : Reach 145871 := rs (se 1 (by rfl) ⟨109403, by rfl⟩) R218807
theorem R670679 : Reach 670679 := rs (se 1 (by rfl) ⟨503009, by rfl⟩) R1006019
theorem R605231 : Reach 605231 := rs (se 1 (by rfl) ⟨453923, by rfl⟩) R907847
theorem R179455 : Reach 179455 := rs (se 1 (by rfl) ⟨134591, by rfl⟩) R269183
theorem R146843 : Reach 146843 := rs (se 1 (by rfl) ⟨110132, by rfl⟩) R220265
theorem R507521 : Reach 507521 := rs (se 2 (by rfl) ⟨190320, by rfl⟩) R380641
theorem R442259 : Reach 442259 := rs (se 1 (by rfl) ⟨331694, by rfl⟩) R663389
theorem R115103 : Reach 115103 := rs (se 1 (by rfl) ⟨86327, by rfl⟩) R172655
theorem R541811 : Reach 541811 := rs (se 1 (by rfl) ⟨406358, by rfl⟩) R812717
theorem R83483 : Reach 83483 := rs (se 1 (by rfl) ⟨62612, by rfl⟩) R125225
theorem R83783 : Reach 83783 := rs (se 1 (by rfl) ⟨62837, by rfl⟩) R125675
theorem R706643 : Reach 706643 := rs (se 1 (by rfl) ⟨529982, by rfl⟩) R1059965
theorem R10504495 : Reach 10504495 := rs (se 1 (by rfl) ⟨7878371, by rfl⟩) R15756743
theorem R118073 : Reach 118073 := rs (se 2 (by rfl) ⟨44277, by rfl⟩) R88555
theorem R85559 : Reach 85559 := rs (se 1 (by rfl) ⟨64169, by rfl⟩) R128339
theorem R317321 : Reach 317321 := rs (se 2 (by rfl) ⟨118995, by rfl⟩) R237991
theorem R874435 : Reach 874435 := rs (se 1 (by rfl) ⟨655826, by rfl⟩) R1311653
theorem R55399 : Reach 55399 := rs (se 1 (by rfl) ⟨41549, by rfl⟩) R83099
theorem R55615 : Reach 55615 := rs (se 1 (by rfl) ⟨41711, by rfl⟩) R83423
theorem R55807 : Reach 55807 := rs (se 1 (by rfl) ⟨41855, by rfl⟩) R83711
theorem R1202849 : Reach 1202849 := rs (se 2 (by rfl) ⟨451068, by rfl⟩) R902137
theorem R57471 : Reach 57471 := rs (se 1 (by rfl) ⟨43103, by rfl⟩) R86207
theorem R58303 : Reach 58303 := rs (se 1 (by rfl) ⟨43727, by rfl⟩) R87455
theorem R124775 : Reach 124775 := rs (se 1 (by rfl) ⟨93581, by rfl⟩) R187163
theorem R289007 : Reach 289007 := rs (se 1 (by rfl) ⟨216755, by rfl⟩) R433511
theorem R125531 : Reach 125531 := rs (se 1 (by rfl) ⟨94148, by rfl⟩) R188297
theorem R944783 : Reach 944783 := rs (se 1 (by rfl) ⟨708587, by rfl⟩) R1417175
theorem R289817 : Reach 289817 := rs (se 2 (by rfl) ⟨108681, by rfl⟩) R217363
theorem R158831 : Reach 158831 := rs (se 1 (by rfl) ⟨119123, by rfl⟩) R238247
theorem R486607 : Reach 486607 := rs (se 1 (by rfl) ⟨364955, by rfl⟩) R729911
theorem R584921 : Reach 584921 := rs (se 2 (by rfl) ⟨219345, by rfl⟩) R438691
theorem R323311 : Reach 323311 := rs (se 1 (by rfl) ⟨242483, by rfl⟩) R484967
theorem R192455 : Reach 192455 := rs (se 1 (by rfl) ⟨144341, by rfl⟩) R288683
theorem R1274291 : Reach 1274291 := rs (se 1 (by rfl) ⟨955718, by rfl⟩) R1911437
theorem R194075 : Reach 194075 := rs (se 1 (by rfl) ⟨145556, by rfl⟩) R291113
theorem R128681 : Reach 128681 := rs (se 2 (by rfl) ⟨48255, by rfl⟩) R96511
theorem R1767095 : Reach 1767095 := rs (se 1 (by rfl) ⟨1325321, by rfl⟩) R2650643
theorem R292571 : Reach 292571 := rs (se 1 (by rfl) ⟨219428, by rfl⟩) R438857
theorem R96167 : Reach 96167 := rs (se 1 (by rfl) ⟨72125, by rfl⟩) R144251
theorem R718793 : Reach 718793 := rs (se 2 (by rfl) ⟨269547, by rfl⟩) R539095
theorem R424187 : Reach 424187 := rs (se 1 (by rfl) ⟨318140, by rfl⟩) R636281
theorem R129401 : Reach 129401 := rs (se 2 (by rfl) ⟨48525, by rfl⟩) R97051
theorem R1243583 : Reach 1243583 := rs (se 1 (by rfl) ⟨932687, by rfl⟩) R1865375
theorem R63967 : Reach 63967 := rs (se 1 (by rfl) ⟨47975, by rfl⟩) R95951
theorem R64219 : Reach 64219 := rs (se 1 (by rfl) ⟨48164, by rfl⟩) R96329
theorem R293867 : Reach 293867 := rs (se 1 (by rfl) ⟨220400, by rfl⟩) R440801
theorem R64795 : Reach 64795 := rs (se 1 (by rfl) ⟨48596, by rfl⟩) R97193
theorem R361207 : Reach 361207 := rs (se 1 (by rfl) ⟨270905, by rfl⟩) R541811
theorem R265031 : Reach 265031 := rs (se 1 (by rfl) ⟨198773, by rfl⟩) R397547
theorem R431081 : Reach 431081 := rs (se 2 (by rfl) ⟨161655, by rfl⟩) R323311
theorem R399275 : Reach 399275 := rs (se 1 (by rfl) ⟨299456, by rfl⟩) R598913
theorem R1382579 : Reach 1382579 := rs (se 1 (by rfl) ⟨1036934, by rfl⟩) R2073869
theorem R661931 : Reach 661931 := rs (se 1 (by rfl) ⟨496448, by rfl⟩) R992897
theorem R105313 : Reach 105313 := rs (se 2 (by rfl) ⟨39492, by rfl⟩) R78985
theorem R629855 : Reach 629855 := rs (se 1 (by rfl) ⟨472391, by rfl⟩) R944783
theorem R334975 : Reach 334975 := rs (se 1 (by rfl) ⟨251231, by rfl⟩) R502463
theorem R105887 : Reach 105887 := rs (se 1 (by rfl) ⟨79415, by rfl⟩) R158831
theorem R74783 : Reach 74783 := rs (se 1 (by rfl) ⟨56087, by rfl⟩) R112175
theorem R829055 : Reach 829055 := rs (se 1 (by rfl) ⟨621791, by rfl⟩) R1243583
theorem R239273 : Reach 239273 := rs (se 2 (by rfl) ⟨89727, by rfl⟩) R179455
theorem R403487 : Reach 403487 := rs (se 1 (by rfl) ⟨302615, by rfl⟩) R605231
theorem R338347 : Reach 338347 := rs (se 1 (by rfl) ⟨253760, by rfl⟩) R507521
theorem R76735 : Reach 76735 := rs (se 1 (by rfl) ⟨57551, by rfl⟩) R115103
theorem R109775 : Reach 109775 := rs (se 1 (by rfl) ⟨82331, by rfl⟩) R164663
theorem R109927 : Reach 109927 := rs (se 1 (by rfl) ⟨82445, by rfl⟩) R164891
theorem R471095 : Reach 471095 := rs (se 1 (by rfl) ⟨353321, by rfl⟩) R706643
theorem R3911759 : Reach 3911759 := rs (se 1 (by rfl) ⟨2933819, by rfl⟩) R5867639
theorem R78715 : Reach 78715 := rs (se 1 (by rfl) ⟨59036, by rfl⟩) R118073
theorem R14005993 : Reach 14005993 := rs (se 2 (by rfl) ⟨5252247, by rfl⟩) R10504495
theorem R440315 : Reach 440315 := rs (se 1 (by rfl) ⟨330236, by rfl⟩) R660473
theorem R834067 : Reach 834067 := rs (se 1 (by rfl) ⟨625550, by rfl⟩) R1251101
theorem R211547 : Reach 211547 := rs (se 1 (by rfl) ⟨158660, by rfl⟩) R317321
theorem R801899 : Reach 801899 := rs (se 1 (by rfl) ⟨601424, by rfl⟩) R1202849
theorem R83183 : Reach 83183 := rs (se 1 (by rfl) ⟨62387, by rfl⟩) R124775
theorem R83687 : Reach 83687 := rs (se 1 (by rfl) ⟨62765, by rfl⟩) R125531
theorem R1623847 : Reach 1623847 := rs (se 1 (by rfl) ⟨1217885, by rfl⟩) R2435771
theorem R1165913 : Reach 1165913 := rs (se 2 (by rfl) ⟨437217, by rfl⟩) R874435
theorem R85289 : Reach 85289 := rs (se 2 (by rfl) ⟨31983, by rfl⟩) R63967
theorem R85625 : Reach 85625 := rs (se 2 (by rfl) ⟨32109, by rfl⟩) R64219
theorem R85787 : Reach 85787 := rs (se 1 (by rfl) ⟨64340, by rfl⟩) R128681
theorem R479195 : Reach 479195 := rs (se 1 (by rfl) ⟨359396, by rfl⟩) R718793
theorem R282791 : Reach 282791 := rs (se 1 (by rfl) ⟨212093, by rfl⟩) R424187
theorem R86267 : Reach 86267 := rs (se 1 (by rfl) ⟨64700, by rfl⟩) R129401
theorem R86393 : Reach 86393 := rs (se 2 (by rfl) ⟨32397, by rfl⟩) R64795
theorem R447119 : Reach 447119 := rs (se 1 (by rfl) ⟨335339, by rfl⟩) R670679
theorem R87503 : Reach 87503 := rs (se 1 (by rfl) ⟨65627, by rfl⟩) R131255
theorem R218855 : Reach 218855 := rs (se 1 (by rfl) ⟨164141, by rfl⟩) R328283
theorem R841913 : Reach 841913 := rs (se 2 (by rfl) ⟨315717, by rfl⟩) R631435
theorem R55655 : Reach 55655 := rs (se 1 (by rfl) ⟨41741, by rfl⟩) R83483
theorem R88457 : Reach 88457 := rs (se 2 (by rfl) ⟨33171, by rfl⟩) R66343
theorem R55855 : Reach 55855 := rs (se 1 (by rfl) ⟨41891, by rfl⟩) R83783
theorem R57039 : Reach 57039 := rs (se 1 (by rfl) ⟨42779, by rfl⟩) R85559
theorem R222695 : Reach 222695 := rs (se 1 (by rfl) ⟨167021, by rfl⟩) R334043
theorem R648809 : Reach 648809 := rs (se 2 (by rfl) ⟨243303, by rfl⟩) R486607
theorem R2386259 : Reach 2386259 := rs (se 1 (by rfl) ⟨1789694, by rfl⟩) R3579389
theorem R191105 : Reach 191105 := rs (se 2 (by rfl) ⟨71664, by rfl⟩) R143329
theorem R224441 : Reach 224441 := rs (se 2 (by rfl) ⟨84165, by rfl⟩) R168331
theorem R289979 : Reach 289979 := rs (se 1 (by rfl) ⟨217484, by rfl⟩) R434969
theorem R192671 : Reach 192671 := rs (se 1 (by rfl) ⟨144503, by rfl⟩) R289007
theorem R94699 : Reach 94699 := rs (se 1 (by rfl) ⟨71024, by rfl⟩) R142049
theorem R815615 : Reach 815615 := rs (se 1 (by rfl) ⟨611711, by rfl⟩) R1223423
theorem R193211 : Reach 193211 := rs (se 1 (by rfl) ⟨144908, by rfl⟩) R289817
theorem R389947 : Reach 389947 := rs (se 1 (by rfl) ⟨292460, by rfl⟩) R584921
theorem R128303 : Reach 128303 := rs (se 1 (by rfl) ⟨96227, by rfl⟩) R192455
theorem R95647 : Reach 95647 := rs (se 1 (by rfl) ⟨71735, by rfl⟩) R143471
theorem R849527 : Reach 849527 := rs (se 1 (by rfl) ⟨637145, by rfl⟩) R1274291
theorem R489167 : Reach 489167 := rs (se 1 (by rfl) ⟨366875, by rfl⟩) R733751
theorem R129383 : Reach 129383 := rs (se 1 (by rfl) ⟨97037, by rfl⟩) R194075
theorem R1178063 : Reach 1178063 := rs (se 1 (by rfl) ⟨883547, by rfl⟩) R1767095
theorem R195047 : Reach 195047 := rs (se 1 (by rfl) ⟨146285, by rfl⟩) R292571
theorem R64111 : Reach 64111 := rs (se 1 (by rfl) ⟨48083, by rfl⟩) R96167
theorem R424763 : Reach 424763 := rs (se 1 (by rfl) ⟨318572, by rfl⟩) R637145
theorem R97247 : Reach 97247 := rs (se 1 (by rfl) ⟨72935, by rfl⟩) R145871
theorem R195911 : Reach 195911 := rs (se 1 (by rfl) ⟨146933, by rfl⟩) R293867
theorem R97895 : Reach 97895 := rs (se 1 (by rfl) ⟨73421, by rfl⟩) R146843
theorem R294839 : Reach 294839 := rs (se 1 (by rfl) ⟨221129, by rfl⟩) R442259
theorem R1804517 : Reach 1804517 := rs (se 4 (by rfl) ⟨169173, by rfl⟩) R338347
theorem R2165129 : Reach 2165129 := rs (se 2 (by rfl) ⟨811923, by rfl⟩) R1623847
theorem R199421 : Reach 199421 := rs (se 3 (by rfl) ⟨37391, by rfl⟩) R74783
theorem R298079 : Reach 298079 := rs (se 1 (by rfl) ⟨223559, by rfl⟩) R447119
theorem R102313 : Reach 102313 := rs (se 2 (by rfl) ⟨38367, by rfl⟩) R76735
theorem R266183 : Reach 266183 := rs (se 1 (by rfl) ⟨199637, by rfl⟩) R399275
theorem R921719 : Reach 921719 := rs (se 1 (by rfl) ⟨691289, by rfl⟩) R1382579
theorem R561275 : Reach 561275 := rs (se 1 (by rfl) ⟨420956, by rfl⟩) R841913
theorem R432539 : Reach 432539 := rs (se 1 (by rfl) ⟨324404, by rfl⟩) R648809
theorem R268991 : Reach 268991 := rs (se 1 (by rfl) ⟨201743, by rfl⟩) R403487
theorem R566351 : Reach 566351 := rs (se 1 (by rfl) ⟨424763, by rfl⟩) R849527
theorem R140417 : Reach 140417 := rs (se 2 (by rfl) ⟨52656, by rfl⟩) R105313
theorem R141031 : Reach 141031 := rs (se 1 (by rfl) ⟨105773, by rfl⟩) R211547
theorem R534599 : Reach 534599 := rs (se 1 (by rfl) ⟨400949, by rfl⟩) R801899
theorem R176687 : Reach 176687 := rs (se 1 (by rfl) ⟨132515, by rfl⟩) R265031
theorem R505061 : Reach 505061 := rs (se 4 (by rfl) ⟨47349, by rfl⟩) R94699
theorem R145903 : Reach 145903 := rs (se 1 (by rfl) ⟨109427, by rfl⟩) R218855
theorem R441287 : Reach 441287 := rs (se 1 (by rfl) ⟨330965, by rfl⟩) R661931
theorem R146569 : Reach 146569 := rs (se 2 (by rfl) ⟨54963, by rfl⟩) R109927
theorem R148463 : Reach 148463 := rs (se 1 (by rfl) ⟨111347, by rfl⟩) R222695
theorem R1590839 : Reach 1590839 := rs (se 1 (by rfl) ⟨1193129, by rfl⟩) R2386259
theorem R149627 : Reach 149627 := rs (se 1 (by rfl) ⟨112220, by rfl⟩) R224441
theorem R314063 : Reach 314063 := rs (se 1 (by rfl) ⟨235547, by rfl⟩) R471095
theorem R2607839 : Reach 2607839 := rs (se 1 (by rfl) ⟨1955879, by rfl⟩) R3911759
theorem R543743 : Reach 543743 := rs (se 1 (by rfl) ⟨407807, by rfl⟩) R815615
theorem R85481 : Reach 85481 := rs (se 2 (by rfl) ⟨32055, by rfl⟩) R64111
theorem R85535 : Reach 85535 := rs (se 1 (by rfl) ⟨64151, by rfl⟩) R128303
theorem R282365 : Reach 282365 := rs (se 3 (by rfl) ⟨52943, by rfl⟩) R105887
theorem R446633 : Reach 446633 := rs (se 2 (by rfl) ⟨167487, by rfl⟩) R334975
theorem R86255 : Reach 86255 := rs (se 1 (by rfl) ⟨64691, by rfl⟩) R129383
theorem R283175 : Reach 283175 := rs (se 1 (by rfl) ⟨212381, by rfl⟩) R424763
theorem R55455 : Reach 55455 := rs (se 1 (by rfl) ⟨41591, by rfl⟩) R83183
theorem R481609 : Reach 481609 := rs (se 2 (by rfl) ⟨180603, by rfl⟩) R361207
theorem R55791 : Reach 55791 := rs (se 1 (by rfl) ⟨41843, by rfl⟩) R83687
theorem R777275 : Reach 777275 := rs (se 1 (by rfl) ⟨582956, by rfl⟩) R1165913
theorem R56859 : Reach 56859 := rs (se 1 (by rfl) ⟨42644, by rfl⟩) R85289
theorem R57083 : Reach 57083 := rs (se 1 (by rfl) ⟨42812, by rfl⟩) R85625
theorem R57191 : Reach 57191 := rs (se 1 (by rfl) ⟨42893, by rfl⟩) R85787
theorem R319463 : Reach 319463 := rs (se 1 (by rfl) ⟨239597, by rfl⟩) R479195
theorem R188527 : Reach 188527 := rs (se 1 (by rfl) ⟨141395, by rfl⟩) R282791
theorem R57511 : Reach 57511 := rs (se 1 (by rfl) ⟨43133, by rfl⟩) R86267
theorem R57595 : Reach 57595 := rs (se 1 (by rfl) ⟨43196, by rfl⟩) R86393
theorem R287387 : Reach 287387 := rs (se 1 (by rfl) ⟨215540, by rfl⟩) R431081
theorem R58335 : Reach 58335 := rs (se 1 (by rfl) ⟨43751, by rfl⟩) R87503
theorem R58971 : Reach 58971 := rs (se 1 (by rfl) ⟨44228, by rfl⟩) R88457
theorem R419813 : Reach 419813 := rs (se 4 (by rfl) ⟨39357, by rfl⟩) R78715
theorem R419903 : Reach 419903 := rs (se 1 (by rfl) ⟨314927, by rfl⟩) R629855
theorem R519929 : Reach 519929 := rs (se 2 (by rfl) ⟨194973, by rfl⟩) R389947
theorem R552703 : Reach 552703 := rs (se 1 (by rfl) ⟨414527, by rfl⟩) R829055
theorem R159515 : Reach 159515 := rs (se 1 (by rfl) ⟨119636, by rfl⟩) R239273
theorem R127403 : Reach 127403 := rs (se 1 (by rfl) ⟨95552, by rfl⟩) R191105
theorem R127529 : Reach 127529 := rs (se 2 (by rfl) ⟨47823, by rfl⟩) R95647
theorem R193319 : Reach 193319 := rs (se 1 (by rfl) ⟨144989, by rfl⟩) R289979
theorem R18674657 : Reach 18674657 := rs (se 2 (by rfl) ⟨7002996, by rfl⟩) R14005993
theorem R128447 : Reach 128447 := rs (se 1 (by rfl) ⟨96335, by rfl⟩) R192671
theorem R128807 : Reach 128807 := rs (se 1 (by rfl) ⟨96605, by rfl⟩) R193211
theorem R292733 : Reach 292733 := rs (se 3 (by rfl) ⟨54887, by rfl⟩) R109775
theorem R1112089 : Reach 1112089 := rs (se 2 (by rfl) ⟨417033, by rfl⟩) R834067
theorem R326111 : Reach 326111 := rs (se 1 (by rfl) ⟨244583, by rfl⟩) R489167
theorem R293543 : Reach 293543 := rs (se 1 (by rfl) ⟨220157, by rfl⟩) R440315
theorem R785375 : Reach 785375 := rs (se 1 (by rfl) ⟨589031, by rfl⟩) R1178063
theorem R130031 : Reach 130031 := rs (se 1 (by rfl) ⟨97523, by rfl⟩) R195047
theorem R64831 : Reach 64831 := rs (se 1 (by rfl) ⟨48623, by rfl⟩) R97247
theorem R130607 : Reach 130607 := rs (se 1 (by rfl) ⟨97955, by rfl⟩) R195911
theorem R65263 : Reach 65263 := rs (se 1 (by rfl) ⟨48947, by rfl⟩) R97895
theorem R196559 : Reach 196559 := rs (se 1 (by rfl) ⟨147419, by rfl⟩) R294839
theorem R98975 : Reach 98975 := rs (se 1 (by rfl) ⟨74231, by rfl⟩) R148463
theorem R99751 : Reach 99751 := rs (se 1 (by rfl) ⟨74813, by rfl⟩) R149627
theorem R1443419 : Reach 1443419 := rs (se 1 (by rfl) ⟨1082564, by rfl⟩) R2165129
theorem R1738559 : Reach 1738559 := rs (se 1 (by rfl) ⟨1303919, by rfl⟩) R2607839
theorem R132947 : Reach 132947 := rs (se 1 (by rfl) ⟨99710, by rfl⟩) R199421
theorem R362495 : Reach 362495 := rs (se 1 (by rfl) ⟨271871, by rfl⟩) R543743
theorem R198719 : Reach 198719 := rs (se 1 (by rfl) ⟨149039, by rfl⟩) R298079
theorem R297755 : Reach 297755 := rs (se 1 (by rfl) ⟨223316, by rfl⟩) R446633
theorem R136417 : Reach 136417 := rs (se 2 (by rfl) ⟨51156, by rfl⟩) R102313
theorem R106343 : Reach 106343 := rs (se 1 (by rfl) ⟨79757, by rfl⟩) R159515
theorem R1482785 : Reach 1482785 := rs (se 2 (by rfl) ⟨556044, by rfl⟩) R1112089
theorem R336707 : Reach 336707 := rs (se 1 (by rfl) ⟨252530, by rfl⟩) R505061
theorem R1060559 : Reach 1060559 := rs (se 1 (by rfl) ⟨795419, by rfl⟩) R1590839
theorem R2568581 : Reach 2568581 := rs (se 4 (by rfl) ⟨240804, by rfl⟩) R481609
theorem R209375 : Reach 209375 := rs (se 1 (by rfl) ⟨157031, by rfl⟩) R314063
theorem R177455 : Reach 177455 := rs (se 1 (by rfl) ⟨133091, by rfl⟩) R266183
theorem R374183 : Reach 374183 := rs (se 1 (by rfl) ⟨280637, by rfl⟩) R561275
theorem R179327 : Reach 179327 := rs (se 1 (by rfl) ⟨134495, by rfl⟩) R268991
theorem R736937 : Reach 736937 := rs (se 2 (by rfl) ⟨276351, by rfl⟩) R552703
theorem R212975 : Reach 212975 := rs (se 1 (by rfl) ⟨159731, by rfl⟩) R319463
theorem R377567 : Reach 377567 := rs (se 1 (by rfl) ⟨283175, by rfl⟩) R566351
theorem R869629 : Reach 869629 := rs (se 3 (by rfl) ⟨163055, by rfl⟩) R326111
theorem R279875 : Reach 279875 := rs (se 1 (by rfl) ⟨209906, by rfl⟩) R419813
theorem R279935 : Reach 279935 := rs (se 1 (by rfl) ⟨209951, by rfl⟩) R419903
theorem R346619 : Reach 346619 := rs (se 1 (by rfl) ⟨259964, by rfl⟩) R519929
theorem R84935 : Reach 84935 := rs (se 1 (by rfl) ⟨63701, by rfl⟩) R127403
theorem R85019 : Reach 85019 := rs (se 1 (by rfl) ⟨63764, by rfl⟩) R127529
theorem R117791 : Reach 117791 := rs (se 1 (by rfl) ⟨88343, by rfl⟩) R176687
theorem R85631 : Reach 85631 := rs (se 1 (by rfl) ⟨64223, by rfl⟩) R128447
theorem R85871 : Reach 85871 := rs (se 1 (by rfl) ⟨64403, by rfl⟩) R128807
theorem R86441 : Reach 86441 := rs (se 2 (by rfl) ⟨32415, by rfl⟩) R64831
theorem R86687 : Reach 86687 := rs (se 1 (by rfl) ⟨65015, by rfl⟩) R130031
theorem R87017 : Reach 87017 := rs (se 2 (by rfl) ⟨32631, by rfl⟩) R65263
theorem R87071 : Reach 87071 := rs (se 1 (by rfl) ⟨65303, by rfl⟩) R130607
theorem R251369 : Reach 251369 := rs (se 2 (by rfl) ⟨94263, by rfl⟩) R188527
theorem R1203011 : Reach 1203011 := rs (se 1 (by rfl) ⟨902258, by rfl⟩) R1804517
theorem R188041 : Reach 188041 := rs (se 2 (by rfl) ⟨70515, by rfl⟩) R141031
theorem R56987 : Reach 56987 := rs (se 1 (by rfl) ⟨42740, by rfl⟩) R85481
theorem R57023 : Reach 57023 := rs (se 1 (by rfl) ⟨42767, by rfl⟩) R85535
theorem R188243 : Reach 188243 := rs (se 1 (by rfl) ⟨141182, by rfl⟩) R282365
theorem R614479 : Reach 614479 := rs (se 1 (by rfl) ⟨460859, by rfl⟩) R921719
theorem R57503 : Reach 57503 := rs (se 1 (by rfl) ⟨43127, by rfl⟩) R86255
theorem R188783 : Reach 188783 := rs (se 1 (by rfl) ⟨141587, by rfl⟩) R283175
theorem R288359 : Reach 288359 := rs (se 1 (by rfl) ⟨216269, by rfl⟩) R432539
theorem R518183 : Reach 518183 := rs (se 1 (by rfl) ⟨388637, by rfl⟩) R777275
theorem R191591 : Reach 191591 := rs (se 1 (by rfl) ⟨143693, by rfl⟩) R287387
theorem R93611 : Reach 93611 := rs (se 1 (by rfl) ⟨70208, by rfl⟩) R140417
theorem R356399 : Reach 356399 := rs (se 1 (by rfl) ⟨267299, by rfl⟩) R534599
theorem R128879 : Reach 128879 := rs (se 1 (by rfl) ⟨96659, by rfl⟩) R193319
theorem R194537 : Reach 194537 := rs (se 2 (by rfl) ⟨72951, by rfl⟩) R145903
theorem R12449771 : Reach 12449771 := rs (se 1 (by rfl) ⟨9337328, by rfl⟩) R18674657
theorem R195155 : Reach 195155 := rs (se 1 (by rfl) ⟨146366, by rfl⟩) R292733
theorem R195425 : Reach 195425 := rs (se 2 (by rfl) ⟨73284, by rfl⟩) R146569
theorem R195695 : Reach 195695 := rs (se 1 (by rfl) ⟨146771, by rfl⟩) R293543
theorem R294191 : Reach 294191 := rs (se 1 (by rfl) ⟨220643, by rfl⟩) R441287
theorem R523583 : Reach 523583 := rs (se 1 (by rfl) ⟨392687, by rfl⟩) R785375
theorem R131039 : Reach 131039 := rs (se 1 (by rfl) ⟨98279, by rfl⟩) R196559
theorem R819305 : Reach 819305 := rs (se 2 (by rfl) ⟨307239, by rfl⟩) R614479
theorem R65983 : Reach 65983 := rs (se 1 (by rfl) ⟨49487, by rfl⟩) R98975
theorem R132479 : Reach 132479 := rs (se 1 (by rfl) ⟨99359, by rfl⟩) R198719
theorem R198503 : Reach 198503 := rs (se 1 (by rfl) ⟨148877, by rfl⟩) R297755
theorem R133001 : Reach 133001 := rs (se 2 (by rfl) ⟨49875, by rfl⟩) R99751
theorem R167579 : Reach 167579 := rs (se 1 (by rfl) ⟨125684, by rfl⟩) R251369
theorem R70895 : Reach 70895 := rs (se 1 (by rfl) ⟨53171, by rfl⟩) R106343
theorem R988523 : Reach 988523 := rs (se 1 (by rfl) ⟨741392, by rfl⟩) R1482785
theorem R924317 : Reach 924317 := rs (se 3 (by rfl) ⟨173309, by rfl⟩) R346619
theorem R237599 : Reach 237599 := rs (se 1 (by rfl) ⟨178199, by rfl⟩) R356399
theorem R1712387 : Reach 1712387 := rs (se 1 (by rfl) ⟨1284290, by rfl⟩) R2568581
theorem R139583 : Reach 139583 := rs (se 1 (by rfl) ⟨104687, by rfl⟩) R209375
theorem R8299847 : Reach 8299847 := rs (se 1 (by rfl) ⟨6224885, by rfl⟩) R12449771
theorem R141983 : Reach 141983 := rs (se 1 (by rfl) ⟨106487, by rfl⟩) R212975
theorem R962279 : Reach 962279 := rs (se 1 (by rfl) ⟨721709, by rfl⟩) R1443419
theorem R1159039 : Reach 1159039 := rs (se 1 (by rfl) ⟨869279, by rfl⟩) R1738559
theorem R1159505 : Reach 1159505 := rs (se 2 (by rfl) ⟨434814, by rfl⟩) R869629
theorem R78527 : Reach 78527 := rs (se 1 (by rfl) ⟨58895, by rfl⟩) R117791
theorem R802007 : Reach 802007 := rs (se 1 (by rfl) ⟨601505, by rfl⟩) R1203011
theorem R966653 : Reach 966653 := rs (se 3 (by rfl) ⟨181247, by rfl⟩) R362495
theorem R345455 : Reach 345455 := rs (se 1 (by rfl) ⟨259091, by rfl⟩) R518183
theorem R181889 : Reach 181889 := rs (se 2 (by rfl) ⟨68208, by rfl⟩) R136417
theorem R707039 : Reach 707039 := rs (se 1 (by rfl) ⟨530279, by rfl⟩) R1060559
theorem R118303 : Reach 118303 := rs (se 1 (by rfl) ⟨88727, by rfl⟩) R177455
theorem R249455 : Reach 249455 := rs (se 1 (by rfl) ⟨187091, by rfl⟩) R374183
theorem R85919 : Reach 85919 := rs (se 1 (by rfl) ⟨64439, by rfl⟩) R128879
theorem R119551 : Reach 119551 := rs (se 1 (by rfl) ⟨89663, by rfl⟩) R179327
theorem R250721 : Reach 250721 := rs (se 2 (by rfl) ⟨94020, by rfl⟩) R188041
theorem R349055 : Reach 349055 := rs (se 1 (by rfl) ⟨261791, by rfl⟩) R523583
theorem R87359 : Reach 87359 := rs (se 1 (by rfl) ⟨65519, by rfl⟩) R131039
theorem R251711 : Reach 251711 := rs (se 1 (by rfl) ⟨188783, by rfl⟩) R377567
theorem R186583 : Reach 186583 := rs (se 1 (by rfl) ⟨139937, by rfl⟩) R279875
theorem R186623 : Reach 186623 := rs (se 1 (by rfl) ⟨139967, by rfl⟩) R279935
theorem R88631 : Reach 88631 := rs (se 1 (by rfl) ⟨66473, by rfl⟩) R132947
theorem R56623 : Reach 56623 := rs (se 1 (by rfl) ⟨42467, by rfl⟩) R84935
theorem R56679 : Reach 56679 := rs (se 1 (by rfl) ⟨42509, by rfl⟩) R85019
theorem R57087 : Reach 57087 := rs (se 1 (by rfl) ⟨42815, by rfl⟩) R85631
theorem R57247 : Reach 57247 := rs (se 1 (by rfl) ⟨42935, by rfl⟩) R85871
theorem R57627 : Reach 57627 := rs (se 1 (by rfl) ⟨43220, by rfl⟩) R86441
theorem R57791 : Reach 57791 := rs (se 1 (by rfl) ⟨43343, by rfl⟩) R86687
theorem R58011 : Reach 58011 := rs (se 1 (by rfl) ⟨43508, by rfl⟩) R87017
theorem R58047 : Reach 58047 := rs (se 1 (by rfl) ⟨43535, by rfl⟩) R87071
theorem R125495 : Reach 125495 := rs (se 1 (by rfl) ⟨94121, by rfl⟩) R188243
theorem R125855 : Reach 125855 := rs (se 1 (by rfl) ⟨94391, by rfl⟩) R188783
theorem R224471 : Reach 224471 := rs (se 1 (by rfl) ⟨168353, by rfl⟩) R336707
theorem R192239 : Reach 192239 := rs (se 1 (by rfl) ⟨144179, by rfl⟩) R288359
theorem R127727 : Reach 127727 := rs (se 1 (by rfl) ⟨95795, by rfl⟩) R191591
theorem R62407 : Reach 62407 := rs (se 1 (by rfl) ⟨46805, by rfl⟩) R93611
theorem R129691 : Reach 129691 := rs (se 1 (by rfl) ⟨97268, by rfl⟩) R194537
theorem R130103 : Reach 130103 := rs (se 1 (by rfl) ⟨97577, by rfl⟩) R195155
theorem R130283 : Reach 130283 := rs (se 1 (by rfl) ⟨97712, by rfl⟩) R195425
theorem R130463 : Reach 130463 := rs (se 1 (by rfl) ⟨97847, by rfl⟩) R195695
theorem R196127 : Reach 196127 := rs (se 1 (by rfl) ⟨147095, by rfl⟩) R294191
theorem R491291 : Reach 491291 := rs (se 1 (by rfl) ⟨368468, by rfl⟩) R736937
theorem R230303 : Reach 230303 := rs (se 1 (by rfl) ⟨172727, by rfl⟩) R345455
theorem R132335 : Reach 132335 := rs (se 1 (by rfl) ⟨99251, by rfl⟩) R198503
theorem R166303 : Reach 166303 := rs (se 1 (by rfl) ⟨124727, by rfl⟩) R249455
theorem R167147 : Reach 167147 := rs (se 1 (by rfl) ⟨125360, by rfl⟩) R250721
theorem R232703 : Reach 232703 := rs (se 1 (by rfl) ⟨174527, by rfl⟩) R349055
theorem R691685 : Reach 691685 := rs (se 4 (by rfl) ⟨64845, by rfl⟩) R129691
theorem R659015 : Reach 659015 := rs (se 1 (by rfl) ⟨494261, by rfl⟩) R988523
theorem R167807 : Reach 167807 := rs (se 1 (by rfl) ⟨125855, by rfl⟩) R251711
theorem R630949 : Reach 630949 := rs (se 4 (by rfl) ⟨59151, by rfl⟩) R118303
theorem R534671 : Reach 534671 := rs (se 1 (by rfl) ⟨401003, by rfl⟩) R802007
theorem R4566365 : Reach 4566365 := rs (se 3 (by rfl) ⟨856193, by rfl⟩) R1712387
theorem R471359 : Reach 471359 := rs (se 1 (by rfl) ⟨353519, by rfl⟩) R707039
theorem R209405 : Reach 209405 := rs (se 3 (by rfl) ⟨39263, by rfl⟩) R78527
theorem R111719 : Reach 111719 := rs (se 1 (by rfl) ⟨83789, by rfl⟩) R167579
theorem R83209 : Reach 83209 := rs (se 2 (by rfl) ⟨31203, by rfl⟩) R62407
theorem R83663 : Reach 83663 := rs (se 1 (by rfl) ⟨62747, by rfl⟩) R125495
theorem R83903 : Reach 83903 := rs (se 1 (by rfl) ⟨62927, by rfl⟩) R125855
theorem R149647 : Reach 149647 := rs (se 1 (by rfl) ⟨112235, by rfl⟩) R224471
theorem R641519 : Reach 641519 := rs (se 1 (by rfl) ⟨481139, by rfl⟩) R962279
theorem R773003 : Reach 773003 := rs (se 1 (by rfl) ⟨579752, by rfl⟩) R1159505
theorem R248777 : Reach 248777 := rs (se 2 (by rfl) ⟨93291, by rfl⟩) R186583
theorem R85151 : Reach 85151 := rs (se 1 (by rfl) ⟨63863, by rfl⟩) R127727
theorem R6181541 : Reach 6181541 := rs (se 4 (by rfl) ⟨579519, by rfl⟩) R1159039
theorem R86735 : Reach 86735 := rs (se 1 (by rfl) ⟨65051, by rfl⟩) R130103
theorem R86855 : Reach 86855 := rs (se 1 (by rfl) ⟨65141, by rfl⟩) R130283
theorem R86975 : Reach 86975 := rs (se 1 (by rfl) ⟨65231, by rfl⟩) R130463
theorem R644435 : Reach 644435 := rs (se 1 (by rfl) ⟨483326, by rfl⟩) R966653
theorem R546203 : Reach 546203 := rs (se 1 (by rfl) ⟨409652, by rfl⟩) R819305
theorem R87977 : Reach 87977 := rs (se 2 (by rfl) ⟨32991, by rfl⟩) R65983
theorem R88319 : Reach 88319 := rs (se 1 (by rfl) ⟨66239, by rfl⟩) R132479
theorem R121259 : Reach 121259 := rs (se 1 (by rfl) ⟨90944, by rfl⟩) R181889
theorem R88667 : Reach 88667 := rs (se 1 (by rfl) ⟨66500, by rfl⟩) R133001
theorem R57279 : Reach 57279 := rs (se 1 (by rfl) ⟨42959, by rfl⟩) R85919
theorem R189053 : Reach 189053 := rs (se 3 (by rfl) ⟨35447, by rfl⟩) R70895
theorem R58239 : Reach 58239 := rs (se 1 (by rfl) ⟨43679, by rfl⟩) R87359
theorem R124415 : Reach 124415 := rs (se 1 (by rfl) ⟨93311, by rfl⟩) R186623
theorem R59087 : Reach 59087 := rs (se 1 (by rfl) ⟨44315, by rfl⟩) R88631
theorem R616211 : Reach 616211 := rs (se 1 (by rfl) ⟨462158, by rfl⟩) R924317
theorem R158399 : Reach 158399 := rs (se 1 (by rfl) ⟨118799, by rfl⟩) R237599
theorem R93055 : Reach 93055 := rs (se 1 (by rfl) ⟨69791, by rfl⟩) R139583
theorem R5533231 : Reach 5533231 := rs (se 1 (by rfl) ⟨4149923, by rfl⟩) R8299847
theorem R159401 : Reach 159401 := rs (se 2 (by rfl) ⟨59775, by rfl⟩) R119551
theorem R94655 : Reach 94655 := rs (se 1 (by rfl) ⟨70991, by rfl⟩) R141983
theorem R128159 : Reach 128159 := rs (se 1 (by rfl) ⟨96119, by rfl⟩) R192239
theorem R130751 : Reach 130751 := rs (se 1 (by rfl) ⟨98063, by rfl⟩) R196127
theorem R327527 : Reach 327527 := rs (se 1 (by rfl) ⟨245645, by rfl⟩) R491291
theorem R427679 : Reach 427679 := rs (se 1 (by rfl) ⟨320759, by rfl⟩) R641519
theorem R165851 : Reach 165851 := rs (se 1 (by rfl) ⟨124388, by rfl⟩) R248777
theorem R461123 : Reach 461123 := rs (se 1 (by rfl) ⟨345842, by rfl⟩) R691685
theorem R199529 : Reach 199529 := rs (se 2 (by rfl) ⟨74823, by rfl⟩) R149647
theorem R297917 : Reach 297917 := rs (se 3 (by rfl) ⟨55859, by rfl⟩) R111719
theorem R429623 : Reach 429623 := rs (se 1 (by rfl) ⟨322217, by rfl⟩) R644435
theorem R7377641 : Reach 7377641 := rs (se 2 (by rfl) ⟨2766615, by rfl⟩) R5533231
theorem R105599 : Reach 105599 := rs (se 1 (by rfl) ⟨79199, by rfl⟩) R158399
theorem R106267 : Reach 106267 := rs (se 1 (by rfl) ⟨79700, by rfl⟩) R159401
theorem R139603 : Reach 139603 := rs (se 1 (by rfl) ⟨104702, by rfl⟩) R209405
theorem R1256957 : Reach 1256957 := rs (se 3 (by rfl) ⟨235679, by rfl⟩) R471359
theorem R110945 : Reach 110945 := rs (se 2 (by rfl) ⟨41604, by rfl⟩) R83209
theorem R111431 : Reach 111431 := rs (se 1 (by rfl) ⟨83573, by rfl⟩) R167147
theorem R439343 : Reach 439343 := rs (se 1 (by rfl) ⟨329507, by rfl⟩) R659015
theorem R111871 : Reach 111871 := rs (se 1 (by rfl) ⟨83903, by rfl⟩) R167807
theorem R1456541 : Reach 1456541 := rs (se 3 (by rfl) ⟨273101, by rfl⟩) R546203
theorem R82943 : Reach 82943 := rs (se 1 (by rfl) ⟨62207, by rfl⟩) R124415
theorem R410807 : Reach 410807 := rs (se 1 (by rfl) ⟨308105, by rfl⟩) R616211
theorem R85439 : Reach 85439 := rs (se 1 (by rfl) ⟨64079, by rfl⟩) R128159
theorem R87167 : Reach 87167 := rs (se 1 (by rfl) ⟨65375, by rfl⟩) R130751
theorem R218351 : Reach 218351 := rs (se 1 (by rfl) ⟨163763, by rfl⟩) R327527
theorem R841265 : Reach 841265 := rs (se 2 (by rfl) ⟨315474, by rfl⟩) R630949
theorem R153535 : Reach 153535 := rs (se 1 (by rfl) ⟨115151, by rfl⟩) R230303
theorem R88223 : Reach 88223 := rs (se 1 (by rfl) ⟨66167, by rfl⟩) R132335
theorem R55775 : Reach 55775 := rs (se 1 (by rfl) ⟨41831, by rfl⟩) R83663
theorem R55935 : Reach 55935 := rs (se 1 (by rfl) ⟨41951, by rfl⟩) R83903
theorem R515335 : Reach 515335 := rs (se 1 (by rfl) ⟨386501, by rfl⟩) R773003
theorem R56767 : Reach 56767 := rs (se 1 (by rfl) ⟨42575, by rfl⟩) R85151
theorem R155135 : Reach 155135 := rs (se 1 (by rfl) ⟨116351, by rfl⟩) R232703
theorem R4121027 : Reach 4121027 := rs (se 1 (by rfl) ⟨3090770, by rfl⟩) R6181541
theorem R57823 : Reach 57823 := rs (se 1 (by rfl) ⟨43367, by rfl⟩) R86735
theorem R221737 : Reach 221737 := rs (se 2 (by rfl) ⟨83151, by rfl⟩) R166303
theorem R57903 : Reach 57903 := rs (se 1 (by rfl) ⟨43427, by rfl⟩) R86855
theorem R57983 : Reach 57983 := rs (se 1 (by rfl) ⟨43487, by rfl⟩) R86975
theorem R124073 : Reach 124073 := rs (se 2 (by rfl) ⟨46527, by rfl⟩) R93055
theorem R58651 : Reach 58651 := rs (se 1 (by rfl) ⟨43988, by rfl⟩) R87977
theorem R58879 : Reach 58879 := rs (se 1 (by rfl) ⟨44159, by rfl⟩) R88319
theorem R59111 : Reach 59111 := rs (se 1 (by rfl) ⟨44333, by rfl⟩) R88667
theorem R126035 : Reach 126035 := rs (se 1 (by rfl) ⟨94526, by rfl⟩) R189053
theorem R323357 : Reach 323357 := rs (se 3 (by rfl) ⟨60629, by rfl⟩) R121259
theorem R356447 : Reach 356447 := rs (se 1 (by rfl) ⟨267335, by rfl⟩) R534671
theorem R3044243 : Reach 3044243 := rs (se 1 (by rfl) ⟨2283182, by rfl⟩) R4566365
theorem R63103 : Reach 63103 := rs (se 1 (by rfl) ⟨47327, by rfl⟩) R94655
theorem R950525 : Reach 950525 := rs (se 3 (by rfl) ⟨178223, by rfl⟩) R356447
theorem R295649 : Reach 295649 := rs (se 2 (by rfl) ⟨110868, by rfl⟩) R221737
theorem R133019 : Reach 133019 := rs (se 1 (by rfl) ⟨99764, by rfl⟩) R199529
theorem R198611 : Reach 198611 := rs (se 1 (by rfl) ⟨148958, by rfl⟩) R297917
theorem R4918427 : Reach 4918427 := rs (se 1 (by rfl) ⟨3688820, by rfl⟩) R7377641
theorem R560843 : Reach 560843 := rs (se 1 (by rfl) ⟨420632, by rfl⟩) R841265
theorem R70399 : Reach 70399 := rs (se 1 (by rfl) ⟨52799, by rfl⟩) R105599
theorem R204713 : Reach 204713 := rs (se 2 (by rfl) ⟨76767, by rfl⟩) R153535
theorem R73963 : Reach 73963 := rs (se 1 (by rfl) ⟨55472, by rfl⟩) R110945
theorem R3449141 : Reach 3449141 := rs (se 5 (by rfl) ⟨161678, by rfl⟩) R323357
theorem R74287 : Reach 74287 := rs (se 1 (by rfl) ⟨55715, by rfl⟩) R111431
theorem R141689 : Reach 141689 := rs (se 2 (by rfl) ⟨53133, by rfl⟩) R106267
theorem R273871 : Reach 273871 := rs (se 1 (by rfl) ⟨205403, by rfl⟩) R410807
theorem R110567 : Reach 110567 := rs (se 1 (by rfl) ⟨82925, by rfl⟩) R165851
theorem R307415 : Reach 307415 := rs (se 1 (by rfl) ⟨230561, by rfl⟩) R461123
theorem R145567 : Reach 145567 := rs (se 1 (by rfl) ⟨109175, by rfl⟩) R218351
theorem R82715 : Reach 82715 := rs (se 1 (by rfl) ⟨62036, by rfl⟩) R124073
theorem R149161 : Reach 149161 := rs (se 2 (by rfl) ⟨55935, by rfl⟩) R111871
theorem R84023 : Reach 84023 := rs (se 1 (by rfl) ⟨63017, by rfl⟩) R126035
theorem R84137 : Reach 84137 := rs (se 2 (by rfl) ⟨31551, by rfl⟩) R63103
theorem R837971 : Reach 837971 := rs (se 1 (by rfl) ⟨628478, by rfl⟩) R1256957
theorem R413693 : Reach 413693 := rs (se 3 (by rfl) ⟨77567, by rfl⟩) R155135
theorem R971027 : Reach 971027 := rs (se 1 (by rfl) ⟨728270, by rfl⟩) R1456541
theorem R186137 : Reach 186137 := rs (se 2 (by rfl) ⟨69801, by rfl⟩) R139603
theorem R55295 : Reach 55295 := rs (se 1 (by rfl) ⟨41471, by rfl⟩) R82943
theorem R285119 : Reach 285119 := rs (se 1 (by rfl) ⟨213839, by rfl⟩) R427679
theorem R56959 : Reach 56959 := rs (se 1 (by rfl) ⟨42719, by rfl⟩) R85439
theorem R286415 : Reach 286415 := rs (se 1 (by rfl) ⟨214811, by rfl⟩) R429623
theorem R58111 : Reach 58111 := rs (se 1 (by rfl) ⟨43583, by rfl⟩) R87167
theorem R58815 : Reach 58815 := rs (se 1 (by rfl) ⟨44111, by rfl⟩) R88223
theorem R2747351 : Reach 2747351 := rs (se 1 (by rfl) ⟨2060513, by rfl⟩) R4121027
theorem R2029495 : Reach 2029495 := rs (se 1 (by rfl) ⟨1522121, by rfl⟩) R3044243
theorem R292895 : Reach 292895 := rs (se 1 (by rfl) ⟨219671, by rfl⟩) R439343
theorem R687113 : Reach 687113 := rs (se 2 (by rfl) ⟨257667, by rfl⟩) R515335
theorem R98617 : Reach 98617 := rs (se 2 (by rfl) ⟨36981, by rfl⟩) R73963
theorem R197099 : Reach 197099 := rs (se 1 (by rfl) ⟨147824, by rfl⟩) R295649
theorem R99049 : Reach 99049 := rs (se 2 (by rfl) ⟨37143, by rfl⟩) R74287
theorem R132407 : Reach 132407 := rs (se 1 (by rfl) ⟨99305, by rfl⟩) R198611
theorem R558647 : Reach 558647 := rs (se 1 (by rfl) ⟨418985, by rfl⟩) R837971
theorem R3278951 : Reach 3278951 := rs (se 1 (by rfl) ⟨2459213, by rfl⟩) R4918427
theorem R198881 : Reach 198881 := rs (se 2 (by rfl) ⟨74580, by rfl⟩) R149161
theorem R365161 : Reach 365161 := rs (se 2 (by rfl) ⟨136935, by rfl⟩) R273871
theorem R136475 : Reach 136475 := rs (se 1 (by rfl) ⟨102356, by rfl⟩) R204713
theorem R2299427 : Reach 2299427 := rs (se 1 (by rfl) ⟨1724570, by rfl⟩) R3449141
theorem R73711 : Reach 73711 := rs (se 1 (by rfl) ⟨55283, by rfl⟩) R110567
theorem R204943 : Reach 204943 := rs (se 1 (by rfl) ⟨153707, by rfl⟩) R307415
theorem R633683 : Reach 633683 := rs (se 1 (by rfl) ⟨475262, by rfl⟩) R950525
theorem R373895 : Reach 373895 := rs (se 1 (by rfl) ⟨280421, by rfl⟩) R560843
theorem R275795 : Reach 275795 := rs (se 1 (by rfl) ⟨206846, by rfl⟩) R413693
theorem R2705993 : Reach 2705993 := rs (se 2 (by rfl) ⟨1014747, by rfl⟩) R2029495
theorem R55143 : Reach 55143 := rs (se 1 (by rfl) ⟨41357, by rfl⟩) R82715
theorem R88679 : Reach 88679 := rs (se 1 (by rfl) ⟨66509, by rfl⟩) R133019
theorem R56015 : Reach 56015 := rs (se 1 (by rfl) ⟨42011, by rfl⟩) R84023
theorem R56091 : Reach 56091 := rs (se 1 (by rfl) ⟨42068, by rfl⟩) R84137
theorem R647351 : Reach 647351 := rs (se 1 (by rfl) ⟨485513, by rfl⟩) R971027
theorem R124091 : Reach 124091 := rs (se 1 (by rfl) ⟨93068, by rfl⟩) R186137
theorem R190079 : Reach 190079 := rs (se 1 (by rfl) ⟨142559, by rfl⟩) R285119
theorem R190943 : Reach 190943 := rs (se 1 (by rfl) ⟨143207, by rfl⟩) R286415
theorem R93865 : Reach 93865 := rs (se 2 (by rfl) ⟨35199, by rfl⟩) R70399
theorem R94459 : Reach 94459 := rs (se 1 (by rfl) ⟨70844, by rfl⟩) R141689
theorem R1831567 : Reach 1831567 := rs (se 1 (by rfl) ⟨1373675, by rfl⟩) R2747351
theorem R194089 : Reach 194089 := rs (se 2 (by rfl) ⟨72783, by rfl⟩) R145567
theorem R195263 : Reach 195263 := rs (se 1 (by rfl) ⟨146447, by rfl⟩) R292895
theorem R458075 : Reach 458075 := rs (se 1 (by rfl) ⟨343556, by rfl⟩) R687113
theorem R131399 : Reach 131399 := rs (se 1 (by rfl) ⟨98549, by rfl⟩) R197099
theorem R131489 : Reach 131489 := rs (se 2 (by rfl) ⟨49308, by rfl⟩) R98617
theorem R132065 : Reach 132065 := rs (se 2 (by rfl) ⟨49524, by rfl⟩) R99049
theorem R132587 : Reach 132587 := rs (se 1 (by rfl) ⟨99440, by rfl⟩) R198881
theorem R1803995 : Reach 1803995 := rs (se 1 (by rfl) ⟨1352996, by rfl⟩) R2705993
theorem R431567 : Reach 431567 := rs (se 1 (by rfl) ⟨323675, by rfl⟩) R647351
theorem R305383 : Reach 305383 := rs (se 1 (by rfl) ⟨229037, by rfl⟩) R458075
theorem R273257 : Reach 273257 := rs (se 2 (by rfl) ⟨102471, by rfl⟩) R204943
theorem R372431 : Reach 372431 := rs (se 1 (by rfl) ⟨279323, by rfl⟩) R558647
theorem R82727 : Reach 82727 := rs (se 1 (by rfl) ⟨62045, by rfl⟩) R124091
theorem R2442089 : Reach 2442089 := rs (se 2 (by rfl) ⟨915783, by rfl⟩) R1831567
theorem R1689821 : Reach 1689821 := rs (se 3 (by rfl) ⟨316841, by rfl⟩) R633683
theorem R249263 : Reach 249263 := rs (se 1 (by rfl) ⟨186947, by rfl⟩) R373895
theorem R183863 : Reach 183863 := rs (se 1 (by rfl) ⟨137897, by rfl⟩) R275795
theorem R88271 : Reach 88271 := rs (se 1 (by rfl) ⟨66203, by rfl⟩) R132407
theorem R2185967 : Reach 2185967 := rs (se 1 (by rfl) ⟨1639475, by rfl⟩) R3278951
theorem R90983 : Reach 90983 := rs (se 1 (by rfl) ⟨68237, by rfl⟩) R136475
theorem R1532951 : Reach 1532951 := rs (se 1 (by rfl) ⟨1149713, by rfl⟩) R2299427
theorem R59119 : Reach 59119 := rs (se 1 (by rfl) ⟨44339, by rfl⟩) R88679
theorem R125153 : Reach 125153 := rs (se 2 (by rfl) ⟨46932, by rfl⟩) R93865
theorem R125945 : Reach 125945 := rs (se 2 (by rfl) ⟨47229, by rfl⟩) R94459
theorem R486881 : Reach 486881 := rs (se 2 (by rfl) ⟨182580, by rfl⟩) R365161
theorem R126719 : Reach 126719 := rs (se 1 (by rfl) ⟨95039, by rfl⟩) R190079
theorem R127295 : Reach 127295 := rs (se 1 (by rfl) ⟨95471, by rfl⟩) R190943
theorem R258785 : Reach 258785 := rs (se 2 (by rfl) ⟨97044, by rfl⟩) R194089
theorem R130175 : Reach 130175 := rs (se 1 (by rfl) ⟨97631, by rfl⟩) R195263
theorem R98281 : Reach 98281 := rs (se 2 (by rfl) ⟨36855, by rfl⟩) R73711
theorem R166175 : Reach 166175 := rs (se 1 (by rfl) ⟨124631, by rfl⟩) R249263
theorem R1021967 : Reach 1021967 := rs (se 1 (by rfl) ⟨766475, by rfl⟩) R1532951
theorem R172523 : Reach 172523 := rs (se 1 (by rfl) ⟨129392, by rfl⟩) R258785
theorem R1126547 : Reach 1126547 := rs (se 1 (by rfl) ⟨844910, by rfl⟩) R1689821
theorem R242621 : Reach 242621 := rs (se 3 (by rfl) ⟨45491, by rfl⟩) R90983
theorem R407177 : Reach 407177 := rs (se 2 (by rfl) ⟨152691, by rfl⟩) R305383
theorem R83435 : Reach 83435 := rs (se 1 (by rfl) ⟨62576, by rfl⟩) R125153
theorem R182171 : Reach 182171 := rs (se 1 (by rfl) ⟨136628, by rfl⟩) R273257
theorem R83963 : Reach 83963 := rs (se 1 (by rfl) ⟨62972, by rfl⟩) R125945
theorem R248287 : Reach 248287 := rs (se 1 (by rfl) ⟨186215, by rfl⟩) R372431
theorem R84479 : Reach 84479 := rs (se 1 (by rfl) ⟨63359, by rfl⟩) R126719
theorem R84863 : Reach 84863 := rs (se 1 (by rfl) ⟨63647, by rfl⟩) R127295
theorem R86783 : Reach 86783 := rs (se 1 (by rfl) ⟨65087, by rfl⟩) R130175
theorem R87599 : Reach 87599 := rs (se 1 (by rfl) ⟨65699, by rfl⟩) R131399
theorem R87659 : Reach 87659 := rs (se 1 (by rfl) ⟨65744, by rfl⟩) R131489
theorem R55151 : Reach 55151 := rs (se 1 (by rfl) ⟨41363, by rfl⟩) R82727
theorem R1628059 : Reach 1628059 := rs (se 1 (by rfl) ⟨1221044, by rfl⟩) R2442089
theorem R88043 : Reach 88043 := rs (se 1 (by rfl) ⟨66032, by rfl⟩) R132065
theorem R88391 : Reach 88391 := rs (se 1 (by rfl) ⟨66293, by rfl⟩) R132587
theorem R1202663 : Reach 1202663 := rs (se 1 (by rfl) ⟨901997, by rfl⟩) R1803995
theorem R122575 : Reach 122575 := rs (se 1 (by rfl) ⟨91931, by rfl⟩) R183863
theorem R287711 : Reach 287711 := rs (se 1 (by rfl) ⟨215783, by rfl⟩) R431567
theorem R58847 : Reach 58847 := rs (se 1 (by rfl) ⟨44135, by rfl⟩) R88271
theorem R5829245 : Reach 5829245 := rs (se 3 (by rfl) ⟨1092983, by rfl⟩) R2185967
theorem R324587 : Reach 324587 := rs (se 1 (by rfl) ⟨243440, by rfl⟩) R486881
theorem R131041 : Reach 131041 := rs (se 2 (by rfl) ⟨49140, by rfl⟩) R98281
theorem R331049 : Reach 331049 := rs (se 2 (by rfl) ⟨124143, by rfl⟩) R248287
theorem R2170745 : Reach 2170745 := rs (se 2 (by rfl) ⟨814029, by rfl⟩) R1628059
theorem R271451 : Reach 271451 := rs (se 1 (by rfl) ⟨203588, by rfl⟩) R407177
theorem R174721 : Reach 174721 := rs (se 2 (by rfl) ⟨65520, by rfl⟩) R131041
theorem R110783 : Reach 110783 := rs (se 1 (by rfl) ⟨83087, by rfl⟩) R166175
theorem R801775 : Reach 801775 := rs (se 1 (by rfl) ⟨601331, by rfl⟩) R1202663
theorem R115015 : Reach 115015 := rs (se 1 (by rfl) ⟨86261, by rfl⟩) R172523
theorem R3886163 : Reach 3886163 := rs (se 1 (by rfl) ⟨2914622, by rfl⟩) R5829245
theorem R216391 : Reach 216391 := rs (se 1 (by rfl) ⟨162293, by rfl⟩) R324587
theorem R55623 : Reach 55623 := rs (se 1 (by rfl) ⟨41717, by rfl⟩) R83435
theorem R121447 : Reach 121447 := rs (se 1 (by rfl) ⟨91085, by rfl⟩) R182171
theorem R55975 : Reach 55975 := rs (se 1 (by rfl) ⟨41981, by rfl⟩) R83963
theorem R56319 : Reach 56319 := rs (se 1 (by rfl) ⟨42239, by rfl⟩) R84479
theorem R56575 : Reach 56575 := rs (se 1 (by rfl) ⟨42431, by rfl⟩) R84863
theorem R57855 : Reach 57855 := rs (se 1 (by rfl) ⟨43391, by rfl⟩) R86783
theorem R58399 : Reach 58399 := rs (se 1 (by rfl) ⟨43799, by rfl⟩) R87599
theorem R58439 : Reach 58439 := rs (se 1 (by rfl) ⟨43829, by rfl⟩) R87659
theorem R58695 : Reach 58695 := rs (se 1 (by rfl) ⟨44021, by rfl⟩) R88043
theorem R681311 : Reach 681311 := rs (se 1 (by rfl) ⟨510983, by rfl⟩) R1021967
theorem R58927 : Reach 58927 := rs (se 1 (by rfl) ⟨44195, by rfl⟩) R88391
theorem R191807 : Reach 191807 := rs (se 1 (by rfl) ⟨143855, by rfl⟩) R287711
theorem R751031 : Reach 751031 := rs (se 1 (by rfl) ⟨563273, by rfl⟩) R1126547
theorem R161747 : Reach 161747 := rs (se 1 (by rfl) ⟨121310, by rfl⟩) R242621
theorem R163433 : Reach 163433 := rs (se 2 (by rfl) ⟨61287, by rfl⟩) R122575
theorem R2590775 : Reach 2590775 := rs (se 1 (by rfl) ⟨1943081, by rfl⟩) R3886163
theorem R232961 : Reach 232961 := rs (se 2 (by rfl) ⟨87360, by rfl⟩) R174721
theorem R1447163 : Reach 1447163 := rs (se 1 (by rfl) ⟨1085372, by rfl⟩) R2170745
theorem R73855 : Reach 73855 := rs (se 1 (by rfl) ⟨55391, by rfl⟩) R110783
theorem R500687 : Reach 500687 := rs (se 1 (by rfl) ⟨375515, by rfl⟩) R751031
theorem R107831 : Reach 107831 := rs (se 1 (by rfl) ⟨80873, by rfl⟩) R161747
theorem R108955 : Reach 108955 := rs (se 1 (by rfl) ⟨81716, by rfl⟩) R163433
theorem R1816829 : Reach 1816829 := rs (se 3 (by rfl) ⟨340655, by rfl⟩) R681311
theorem R180967 : Reach 180967 := rs (se 1 (by rfl) ⟨135725, by rfl⟩) R271451
theorem R1069033 : Reach 1069033 := rs (se 2 (by rfl) ⟨400887, by rfl⟩) R801775
theorem R153353 : Reach 153353 := rs (se 2 (by rfl) ⟨57507, by rfl⟩) R115015
theorem R220699 : Reach 220699 := rs (se 1 (by rfl) ⟨165524, by rfl⟩) R331049
theorem R288521 : Reach 288521 := rs (se 2 (by rfl) ⟨108195, by rfl⟩) R216391
theorem R127871 : Reach 127871 := rs (se 1 (by rfl) ⟨95903, by rfl⟩) R191807
theorem R161929 : Reach 161929 := rs (se 2 (by rfl) ⟨60723, by rfl⟩) R121447
theorem R393893 : Reach 393893 := rs (se 4 (by rfl) ⟨36927, by rfl⟩) R73855
theorem R102235 : Reach 102235 := rs (se 1 (by rfl) ⟨76676, by rfl⟩) R153353
theorem R333791 : Reach 333791 := rs (se 1 (by rfl) ⟨250343, by rfl⟩) R500687
theorem R241289 : Reach 241289 := rs (se 2 (by rfl) ⟨90483, by rfl⟩) R180967
theorem R145273 : Reach 145273 := rs (se 2 (by rfl) ⟨54477, by rfl⟩) R108955
theorem R964775 : Reach 964775 := rs (se 1 (by rfl) ⟨723581, by rfl⟩) R1447163
theorem R1425377 : Reach 1425377 := rs (se 2 (by rfl) ⟨534516, by rfl⟩) R1069033
theorem R215905 : Reach 215905 := rs (se 2 (by rfl) ⟨80964, by rfl⟩) R161929
theorem R85247 : Reach 85247 := rs (se 1 (by rfl) ⟨63935, by rfl⟩) R127871
theorem R1727183 : Reach 1727183 := rs (se 1 (by rfl) ⟨1295387, by rfl⟩) R2590775
theorem R287549 : Reach 287549 := rs (se 3 (by rfl) ⟨53915, by rfl⟩) R107831
theorem R192347 : Reach 192347 := rs (se 1 (by rfl) ⟨144260, by rfl⟩) R288521
theorem R621229 : Reach 621229 := rs (se 3 (by rfl) ⟨116480, by rfl⟩) R232961
theorem R1211219 : Reach 1211219 := rs (se 1 (by rfl) ⟨908414, by rfl⟩) R1816829
theorem R294265 : Reach 294265 := rs (se 2 (by rfl) ⟨110349, by rfl⟩) R220699
theorem R262595 : Reach 262595 := rs (se 1 (by rfl) ⟨196946, by rfl⟩) R393893
theorem R136313 : Reach 136313 := rs (se 2 (by rfl) ⟨51117, by rfl⟩) R102235
theorem R828305 : Reach 828305 := rs (se 2 (by rfl) ⟨310614, by rfl⟩) R621229
theorem R4605821 : Reach 4605821 := rs (se 3 (by rfl) ⟨863591, by rfl⟩) R1727183
theorem R643183 : Reach 643183 := rs (se 1 (by rfl) ⟨482387, by rfl⟩) R964775
theorem R807479 : Reach 807479 := rs (se 1 (by rfl) ⟨605609, by rfl⟩) R1211219
theorem R56831 : Reach 56831 := rs (se 1 (by rfl) ⟨42623, by rfl⟩) R85247
theorem R287873 : Reach 287873 := rs (se 2 (by rfl) ⟨107952, by rfl⟩) R215905
theorem R222527 : Reach 222527 := rs (se 1 (by rfl) ⟨166895, by rfl⟩) R333791
theorem R191699 : Reach 191699 := rs (se 1 (by rfl) ⟨143774, by rfl⟩) R287549
theorem R160859 : Reach 160859 := rs (se 1 (by rfl) ⟨120644, by rfl⟩) R241289
theorem R193697 : Reach 193697 := rs (se 2 (by rfl) ⟨72636, by rfl⟩) R145273
theorem R128231 : Reach 128231 := rs (se 1 (by rfl) ⟨96173, by rfl⟩) R192347
theorem R392353 : Reach 392353 := rs (se 2 (by rfl) ⟨147132, by rfl⟩) R294265
theorem R3801005 : Reach 3801005 := rs (se 3 (by rfl) ⟨712688, by rfl⟩) R1425377
theorem R107239 : Reach 107239 := rs (se 1 (by rfl) ⟨80429, by rfl⟩) R160859
theorem R2534003 : Reach 2534003 := rs (se 1 (by rfl) ⟨1900502, by rfl⟩) R3801005
theorem R175063 : Reach 175063 := rs (se 1 (by rfl) ⟨131297, by rfl⟩) R262595
theorem R538319 : Reach 538319 := rs (se 1 (by rfl) ⟨403739, by rfl⟩) R807479
theorem R148351 : Reach 148351 := rs (se 1 (by rfl) ⟨111263, by rfl⟩) R222527
theorem R85487 : Reach 85487 := rs (se 1 (by rfl) ⟨64115, by rfl⟩) R128231
theorem R3070547 : Reach 3070547 := rs (se 1 (by rfl) ⟨2302910, by rfl⟩) R4605821
theorem R13721237 : Reach 13721237 := rs (se 6 (by rfl) ⟨321591, by rfl⟩) R643183
theorem R90875 : Reach 90875 := rs (se 1 (by rfl) ⟨68156, by rfl⟩) R136313
theorem R552203 : Reach 552203 := rs (se 1 (by rfl) ⟨414152, by rfl⟩) R828305
theorem R191915 : Reach 191915 := rs (se 1 (by rfl) ⟨143936, by rfl⟩) R287873
theorem R2092549 : Reach 2092549 := rs (se 4 (by rfl) ⟨196176, by rfl⟩) R392353
theorem R127799 : Reach 127799 := rs (se 1 (by rfl) ⟨95849, by rfl⟩) R191699
theorem R129131 : Reach 129131 := rs (se 1 (by rfl) ⟨96848, by rfl⟩) R193697
theorem R197801 : Reach 197801 := rs (se 2 (by rfl) ⟨74175, by rfl⟩) R148351
theorem R233417 : Reach 233417 := rs (se 2 (by rfl) ⟨87531, by rfl⟩) R175063
theorem R2790065 : Reach 2790065 := rs (se 2 (by rfl) ⟨1046274, by rfl⟩) R2092549
theorem R9147491 : Reach 9147491 := rs (se 1 (by rfl) ⟨6860618, by rfl⟩) R13721237
theorem R368135 : Reach 368135 := rs (se 1 (by rfl) ⟨276101, by rfl⟩) R552203
theorem R142985 : Reach 142985 := rs (se 2 (by rfl) ⟨53619, by rfl⟩) R107239
theorem R2047031 : Reach 2047031 := rs (se 1 (by rfl) ⟨1535273, by rfl⟩) R3070547
theorem R1689335 : Reach 1689335 := rs (se 1 (by rfl) ⟨1267001, by rfl⟩) R2534003
theorem R85199 : Reach 85199 := rs (se 1 (by rfl) ⟨63899, by rfl⟩) R127799
theorem R86087 : Reach 86087 := rs (se 1 (by rfl) ⟨64565, by rfl⟩) R129131
theorem R56991 : Reach 56991 := rs (se 1 (by rfl) ⟨42743, by rfl⟩) R85487
theorem R60583 : Reach 60583 := rs (se 1 (by rfl) ⟨45437, by rfl⟩) R90875
theorem R127943 : Reach 127943 := rs (se 1 (by rfl) ⟨95957, by rfl⟩) R191915
theorem R358879 : Reach 358879 := rs (se 1 (by rfl) ⟨269159, by rfl⟩) R538319
theorem R131867 : Reach 131867 := rs (se 1 (by rfl) ⟨98900, by rfl⟩) R197801
theorem R7440173 : Reach 7440173 := rs (se 3 (by rfl) ⟨1395032, by rfl⟩) R2790065
theorem R6098327 : Reach 6098327 := rs (se 1 (by rfl) ⟨4573745, by rfl⟩) R9147491
theorem R1126223 : Reach 1126223 := rs (se 1 (by rfl) ⟨844667, by rfl⟩) R1689335
theorem R80777 : Reach 80777 := rs (se 2 (by rfl) ⟨30291, by rfl⟩) R60583
theorem R245423 : Reach 245423 := rs (se 1 (by rfl) ⟨184067, by rfl⟩) R368135
theorem R478505 : Reach 478505 := rs (se 2 (by rfl) ⟨179439, by rfl⟩) R358879
theorem R85295 : Reach 85295 := rs (se 1 (by rfl) ⟨63971, by rfl⟩) R127943
theorem R1364687 : Reach 1364687 := rs (se 1 (by rfl) ⟨1023515, by rfl⟩) R2047031
theorem R56799 : Reach 56799 := rs (se 1 (by rfl) ⟨42599, by rfl⟩) R85199
theorem R155611 : Reach 155611 := rs (se 1 (by rfl) ⟨116708, by rfl⟩) R233417
theorem R57391 : Reach 57391 := rs (se 1 (by rfl) ⟨43043, by rfl⟩) R86087
theorem R95323 : Reach 95323 := rs (se 1 (by rfl) ⟨71492, by rfl⟩) R142985
theorem R4065551 : Reach 4065551 := rs (se 1 (by rfl) ⟨3049163, by rfl⟩) R6098327
theorem R207481 : Reach 207481 := rs (se 2 (by rfl) ⟨77805, by rfl⟩) R155611
theorem R4960115 : Reach 4960115 := rs (se 1 (by rfl) ⟨3720086, by rfl⟩) R7440173
theorem R215405 : Reach 215405 := rs (se 3 (by rfl) ⟨40388, by rfl⟩) R80777
theorem R87911 : Reach 87911 := rs (se 1 (by rfl) ⟨65933, by rfl⟩) R131867
theorem R56863 : Reach 56863 := rs (se 1 (by rfl) ⟨42647, by rfl⟩) R85295
theorem R909791 : Reach 909791 := rs (se 1 (by rfl) ⟨682343, by rfl⟩) R1364687
theorem R127097 : Reach 127097 := rs (se 2 (by rfl) ⟨47661, by rfl⟩) R95323
theorem R750815 : Reach 750815 := rs (se 1 (by rfl) ⟨563111, by rfl⟩) R1126223
theorem R1276013 : Reach 1276013 := rs (se 3 (by rfl) ⟨239252, by rfl⟩) R478505
theorem R163615 : Reach 163615 := rs (se 1 (by rfl) ⟨122711, by rfl⟩) R245423
theorem R500543 : Reach 500543 := rs (se 1 (by rfl) ⟨375407, by rfl⟩) R750815
theorem R143603 : Reach 143603 := rs (se 1 (by rfl) ⟨107702, by rfl⟩) R215405
theorem R276641 : Reach 276641 := rs (se 2 (by rfl) ⟨103740, by rfl⟩) R207481
theorem R606527 : Reach 606527 := rs (se 1 (by rfl) ⟨454895, by rfl⟩) R909791
theorem R84731 : Reach 84731 := rs (se 1 (by rfl) ⟨63548, by rfl⟩) R127097
theorem R218153 : Reach 218153 := rs (se 2 (by rfl) ⟨81807, by rfl⟩) R163615
theorem R2710367 : Reach 2710367 := rs (se 1 (by rfl) ⟨2032775, by rfl⟩) R4065551
theorem R58607 : Reach 58607 := rs (se 1 (by rfl) ⟨43955, by rfl⟩) R87911
theorem R3306743 : Reach 3306743 := rs (se 1 (by rfl) ⟨2480057, by rfl⟩) R4960115
theorem R850675 : Reach 850675 := rs (se 1 (by rfl) ⟨638006, by rfl⟩) R1276013
theorem R1806911 : Reach 1806911 := rs (se 1 (by rfl) ⟨1355183, by rfl⟩) R2710367
theorem R333695 : Reach 333695 := rs (se 1 (by rfl) ⟨250271, by rfl⟩) R500543
theorem R2204495 : Reach 2204495 := rs (se 1 (by rfl) ⟨1653371, by rfl⟩) R3306743
theorem R404351 : Reach 404351 := rs (se 1 (by rfl) ⟨303263, by rfl⟩) R606527
theorem R145435 : Reach 145435 := rs (se 1 (by rfl) ⟨109076, by rfl⟩) R218153
theorem R1134233 : Reach 1134233 := rs (se 2 (by rfl) ⟨425337, by rfl⟩) R850675
theorem R184427 : Reach 184427 := rs (se 1 (by rfl) ⟨138320, by rfl⟩) R276641
theorem R56487 : Reach 56487 := rs (se 1 (by rfl) ⟨42365, by rfl⟩) R84731
theorem R95735 : Reach 95735 := rs (se 1 (by rfl) ⟨71801, by rfl⟩) R143603
theorem R756155 : Reach 756155 := rs (se 1 (by rfl) ⟨567116, by rfl⟩) R1134233
theorem R269567 : Reach 269567 := rs (se 1 (by rfl) ⟨202175, by rfl⟩) R404351
theorem R122951 : Reach 122951 := rs (se 1 (by rfl) ⟨92213, by rfl⟩) R184427
theorem R1204607 : Reach 1204607 := rs (se 1 (by rfl) ⟨903455, by rfl⟩) R1806911
theorem R222463 : Reach 222463 := rs (se 1 (by rfl) ⟨166847, by rfl⟩) R333695
theorem R1469663 : Reach 1469663 := rs (se 1 (by rfl) ⟨1102247, by rfl⟩) R2204495
theorem R193913 : Reach 193913 := rs (se 2 (by rfl) ⟨72717, by rfl⟩) R145435
theorem R63823 : Reach 63823 := rs (se 1 (by rfl) ⟨47867, by rfl⟩) R95735
theorem R296617 : Reach 296617 := rs (se 2 (by rfl) ⟨111231, by rfl⟩) R222463
theorem R504103 : Reach 504103 := rs (se 1 (by rfl) ⟨378077, by rfl⟩) R756155
theorem R179711 : Reach 179711 := rs (se 1 (by rfl) ⟨134783, by rfl⟩) R269567
theorem R81967 : Reach 81967 := rs (se 1 (by rfl) ⟨61475, by rfl⟩) R122951
theorem R803071 : Reach 803071 := rs (se 1 (by rfl) ⟨602303, by rfl⟩) R1204607
theorem R85097 : Reach 85097 := rs (se 2 (by rfl) ⟨31911, by rfl⟩) R63823
theorem R979775 : Reach 979775 := rs (se 1 (by rfl) ⟨734831, by rfl⟩) R1469663
theorem R129275 : Reach 129275 := rs (se 1 (by rfl) ⟨96956, by rfl⟩) R193913
theorem R395489 : Reach 395489 := rs (se 2 (by rfl) ⟨148308, by rfl⟩) R296617
theorem R109289 : Reach 109289 := rs (se 2 (by rfl) ⟨40983, by rfl⟩) R81967
theorem R672137 : Reach 672137 := rs (se 2 (by rfl) ⟨252051, by rfl⟩) R504103
theorem R86183 : Reach 86183 := rs (se 1 (by rfl) ⟨64637, by rfl⟩) R129275
theorem R119807 : Reach 119807 := rs (se 1 (by rfl) ⟨89855, by rfl⟩) R179711
theorem R1070761 : Reach 1070761 := rs (se 2 (by rfl) ⟨401535, by rfl⟩) R803071
theorem R56731 : Reach 56731 := rs (se 1 (by rfl) ⟨42548, by rfl⟩) R85097
theorem R653183 : Reach 653183 := rs (se 1 (by rfl) ⟨489887, by rfl⟩) R979775
theorem R1054637 : Reach 1054637 := rs (se 3 (by rfl) ⟨197744, by rfl⟩) R395489
theorem R435455 : Reach 435455 := rs (se 1 (by rfl) ⟨326591, by rfl⟩) R653183
theorem R79871 : Reach 79871 := rs (se 1 (by rfl) ⟨59903, by rfl⟩) R119807
theorem R1427681 : Reach 1427681 := rs (se 2 (by rfl) ⟨535380, by rfl⟩) R1070761
theorem R448091 : Reach 448091 := rs (se 1 (by rfl) ⟨336068, by rfl⟩) R672137
theorem R57455 : Reach 57455 := rs (se 1 (by rfl) ⟨43091, by rfl⟩) R86183
theorem R291437 : Reach 291437 := rs (se 3 (by rfl) ⟨54644, by rfl⟩) R109289
theorem R951787 : Reach 951787 := rs (se 1 (by rfl) ⟨713840, by rfl⟩) R1427681
theorem R298727 : Reach 298727 := rs (se 1 (by rfl) ⟨224045, by rfl⟩) R448091
theorem R703091 : Reach 703091 := rs (se 1 (by rfl) ⟨527318, by rfl⟩) R1054637
theorem R212989 : Reach 212989 := rs (se 3 (by rfl) ⟨39935, by rfl⟩) R79871
theorem R290303 : Reach 290303 := rs (se 1 (by rfl) ⟨217727, by rfl⟩) R435455
theorem R194291 : Reach 194291 := rs (se 1 (by rfl) ⟨145718, by rfl⟩) R291437
theorem R199151 : Reach 199151 := rs (se 1 (by rfl) ⟨149363, by rfl⟩) R298727
theorem R1874909 : Reach 1874909 := rs (se 3 (by rfl) ⟨351545, by rfl⟩) R703091
theorem R283985 : Reach 283985 := rs (se 2 (by rfl) ⟨106494, by rfl⟩) R212989
theorem R1269049 : Reach 1269049 := rs (se 2 (by rfl) ⟨475893, by rfl⟩) R951787
theorem R193535 : Reach 193535 := rs (se 1 (by rfl) ⟨145151, by rfl⟩) R290303
theorem R129527 : Reach 129527 := rs (se 1 (by rfl) ⟨97145, by rfl⟩) R194291
theorem R132767 : Reach 132767 := rs (se 1 (by rfl) ⟨99575, by rfl⟩) R199151
theorem R1249939 : Reach 1249939 := rs (se 1 (by rfl) ⟨937454, by rfl⟩) R1874909
theorem R86351 : Reach 86351 := rs (se 1 (by rfl) ⟨64763, by rfl⟩) R129527
theorem R1692065 : Reach 1692065 := rs (se 2 (by rfl) ⟨634524, by rfl⟩) R1269049
theorem R189323 : Reach 189323 := rs (se 1 (by rfl) ⟨141992, by rfl⟩) R283985
theorem R129023 : Reach 129023 := rs (se 1 (by rfl) ⟨96767, by rfl⟩) R193535
theorem R1128043 : Reach 1128043 := rs (se 1 (by rfl) ⟨846032, by rfl⟩) R1692065
theorem R86015 : Reach 86015 := rs (se 1 (by rfl) ⟨64511, by rfl⟩) R129023
theorem R88511 : Reach 88511 := rs (se 1 (by rfl) ⟨66383, by rfl⟩) R132767
theorem R57567 : Reach 57567 := rs (se 1 (by rfl) ⟨43175, by rfl⟩) R86351
theorem R126215 : Reach 126215 := rs (se 1 (by rfl) ⟨94661, by rfl⟩) R189323
theorem R1666585 : Reach 1666585 := rs (se 2 (by rfl) ⟨624969, by rfl⟩) R1249939
theorem R84143 : Reach 84143 := rs (se 1 (by rfl) ⟨63107, by rfl⟩) R126215
theorem R57343 : Reach 57343 := rs (se 1 (by rfl) ⟨43007, by rfl⟩) R86015
theorem R59007 : Reach 59007 := rs (se 1 (by rfl) ⟨44255, by rfl⟩) R88511
theorem R2222113 : Reach 2222113 := rs (se 2 (by rfl) ⟨833292, by rfl⟩) R1666585
theorem R1504057 : Reach 1504057 := rs (se 2 (by rfl) ⟨564021, by rfl⟩) R1128043
theorem R2005409 : Reach 2005409 := rs (se 2 (by rfl) ⟨752028, by rfl⟩) R1504057
theorem R2962817 : Reach 2962817 := rs (se 2 (by rfl) ⟨1111056, by rfl⟩) R2222113
theorem R56095 : Reach 56095 := rs (se 1 (by rfl) ⟨42071, by rfl⟩) R84143
theorem R5347757 : Reach 5347757 := rs (se 3 (by rfl) ⟨1002704, by rfl⟩) R2005409
theorem R1975211 : Reach 1975211 := rs (se 1 (by rfl) ⟨1481408, by rfl⟩) R2962817
theorem R1316807 : Reach 1316807 := rs (se 1 (by rfl) ⟨987605, by rfl⟩) R1975211
theorem R3565171 : Reach 3565171 := rs (se 1 (by rfl) ⟨2673878, by rfl⟩) R5347757
theorem R4753561 : Reach 4753561 := rs (se 2 (by rfl) ⟨1782585, by rfl⟩) R3565171
theorem R877871 : Reach 877871 := rs (se 1 (by rfl) ⟨658403, by rfl⟩) R1316807
theorem R6338081 : Reach 6338081 := rs (se 2 (by rfl) ⟨2376780, by rfl⟩) R4753561
theorem R585247 : Reach 585247 := rs (se 1 (by rfl) ⟨438935, by rfl⟩) R877871
theorem R780329 : Reach 780329 := rs (se 2 (by rfl) ⟨292623, by rfl⟩) R585247
theorem R4225387 : Reach 4225387 := rs (se 1 (by rfl) ⟨3169040, by rfl⟩) R6338081
theorem R520219 : Reach 520219 := rs (se 1 (by rfl) ⟨390164, by rfl⟩) R780329
theorem R5633849 : Reach 5633849 := rs (se 2 (by rfl) ⟨2112693, by rfl⟩) R4225387
theorem R693625 : Reach 693625 := rs (se 2 (by rfl) ⟨260109, by rfl⟩) R520219
theorem R3755899 : Reach 3755899 := rs (se 1 (by rfl) ⟨2816924, by rfl⟩) R5633849
theorem R924833 : Reach 924833 := rs (se 2 (by rfl) ⟨346812, by rfl⟩) R693625
theorem R5007865 : Reach 5007865 := rs (se 2 (by rfl) ⟨1877949, by rfl⟩) R3755899
theorem R6677153 : Reach 6677153 := rs (se 2 (by rfl) ⟨2503932, by rfl⟩) R5007865
theorem R616555 : Reach 616555 := rs (se 1 (by rfl) ⟨462416, by rfl⟩) R924833
theorem R822073 : Reach 822073 := rs (se 2 (by rfl) ⟨308277, by rfl⟩) R616555
theorem R4451435 : Reach 4451435 := rs (se 1 (by rfl) ⟨3338576, by rfl⟩) R6677153
theorem R1096097 : Reach 1096097 := rs (se 2 (by rfl) ⟨411036, by rfl⟩) R822073
theorem R2967623 : Reach 2967623 := rs (se 1 (by rfl) ⟨2225717, by rfl⟩) R4451435
theorem R1978415 : Reach 1978415 := rs (se 1 (by rfl) ⟨1483811, by rfl⟩) R2967623
theorem R11691701 : Reach 11691701 := rs (se 5 (by rfl) ⟨548048, by rfl⟩) R1096097
theorem R1318943 : Reach 1318943 := rs (se 1 (by rfl) ⟨989207, by rfl⟩) R1978415
theorem R7794467 : Reach 7794467 := rs (se 1 (by rfl) ⟨5845850, by rfl⟩) R11691701
theorem R5196311 : Reach 5196311 := rs (se 1 (by rfl) ⟨3897233, by rfl⟩) R7794467
theorem R879295 : Reach 879295 := rs (se 1 (by rfl) ⟨659471, by rfl⟩) R1318943
theorem R3464207 : Reach 3464207 := rs (se 1 (by rfl) ⟨2598155, by rfl⟩) R5196311
theorem R1172393 : Reach 1172393 := rs (se 2 (by rfl) ⟨439647, by rfl⟩) R879295
theorem R2309471 : Reach 2309471 := rs (se 1 (by rfl) ⟨1732103, by rfl⟩) R3464207
theorem R781595 : Reach 781595 := rs (se 1 (by rfl) ⟨586196, by rfl⟩) R1172393
theorem R521063 : Reach 521063 := rs (se 1 (by rfl) ⟨390797, by rfl⟩) R781595
theorem R1539647 : Reach 1539647 := rs (se 1 (by rfl) ⟨1154735, by rfl⟩) R2309471
theorem R1026431 : Reach 1026431 := rs (se 1 (by rfl) ⟨769823, by rfl⟩) R1539647
theorem R347375 : Reach 347375 := rs (se 1 (by rfl) ⟨260531, by rfl⟩) R521063
theorem R231583 : Reach 231583 := rs (se 1 (by rfl) ⟨173687, by rfl⟩) R347375
theorem R684287 : Reach 684287 := rs (se 1 (by rfl) ⟨513215, by rfl⟩) R1026431
theorem R308777 : Reach 308777 := rs (se 2 (by rfl) ⟨115791, by rfl⟩) R231583
theorem R456191 : Reach 456191 := rs (se 1 (by rfl) ⟨342143, by rfl⟩) R684287
theorem R823405 : Reach 823405 := rs (se 3 (by rfl) ⟨154388, by rfl⟩) R308777
theorem R304127 : Reach 304127 := rs (se 1 (by rfl) ⟨228095, by rfl⟩) R456191
theorem R202751 : Reach 202751 := rs (se 1 (by rfl) ⟨152063, by rfl⟩) R304127
theorem R1097873 : Reach 1097873 := rs (se 2 (by rfl) ⟨411702, by rfl⟩) R823405
theorem R135167 : Reach 135167 := rs (se 1 (by rfl) ⟨101375, by rfl⟩) R202751
theorem R731915 : Reach 731915 := rs (se 1 (by rfl) ⟨548936, by rfl⟩) R1097873
theorem R487943 : Reach 487943 := rs (se 1 (by rfl) ⟨365957, by rfl⟩) R731915
theorem R360445 : Reach 360445 := rs (se 3 (by rfl) ⟨67583, by rfl⟩) R135167
theorem R480593 : Reach 480593 := rs (se 2 (by rfl) ⟨180222, by rfl⟩) R360445
theorem R325295 : Reach 325295 := rs (se 1 (by rfl) ⟨243971, by rfl⟩) R487943
theorem R216863 : Reach 216863 := rs (se 1 (by rfl) ⟨162647, by rfl⟩) R325295
theorem R320395 : Reach 320395 := rs (se 1 (by rfl) ⟨240296, by rfl⟩) R480593
theorem R427193 : Reach 427193 := rs (se 2 (by rfl) ⟨160197, by rfl⟩) R320395
theorem R144575 : Reach 144575 := rs (se 1 (by rfl) ⟨108431, by rfl⟩) R216863
theorem R284795 : Reach 284795 := rs (se 1 (by rfl) ⟨213596, by rfl⟩) R427193
theorem R96383 : Reach 96383 := rs (se 1 (by rfl) ⟨72287, by rfl⟩) R144575
theorem R189863 : Reach 189863 := rs (se 1 (by rfl) ⟨142397, by rfl⟩) R284795
theorem R64255 : Reach 64255 := rs (se 1 (by rfl) ⟨48191, by rfl⟩) R96383
theorem R85673 : Reach 85673 := rs (se 2 (by rfl) ⟨32127, by rfl⟩) R64255
theorem R126575 : Reach 126575 := rs (se 1 (by rfl) ⟨94931, by rfl⟩) R189863
theorem R84383 : Reach 84383 := rs (se 1 (by rfl) ⟨63287, by rfl⟩) R126575
theorem R57115 : Reach 57115 := rs (se 1 (by rfl) ⟨42836, by rfl⟩) R85673
theorem R56255 : Reach 56255 := rs (se 1 (by rfl) ⟨42191, by rfl⟩) R84383

theorem C0 (j : ℕ) (h1 : 27560 ≤ j) (h2 : j ≤ 28259) : Reach (2 * j + 1) := by
  interval_cases j
  · exact R55121
  · exact R55123
  · exact R55125
  · exact R55127
  · exact R55129
  · exact R55131
  · exact R55133
  · exact R55135
  · exact R55137
  · exact R55139
  · exact R55141
  · exact R55143
  · exact R55145
  · exact R55147
  · exact R55149
  · exact R55151
  · exact R55153
  · exact R55155
  · exact R55157
  · exact R55159
  · exact R55161
  · exact R55163
  · exact R55165
  · exact R55167
  · exact R55169
  · exact R55171
  · exact R55173
  · exact R55175
  · exact R55177
  · exact R55179
  · exact R55181
  · exact R55183
  · exact R55185
  · exact R55187
  · exact R55189
  · exact R55191
  · exact R55193
  · exact R55195
  · exact R55197
  · exact R55199
  · exact R55201
  · exact R55203
  · exact R55205
  · exact R55207
  · exact R55209
  · exact R55211
  · exact R55213
  · exact R55215
  · exact R55217
  · exact R55219
  · exact R55221
  · exact R55223
  · exact R55225
  · exact R55227
  · exact R55229
  · exact R55231
  · exact R55233
  · exact R55235
  · exact R55237
  · exact R55239
  · exact R55241
  · exact R55243
  · exact R55245
  · exact R55247
  · exact R55249
  · exact R55251
  · exact R55253
  · exact R55255
  · exact R55257
  · exact R55259
  · exact R55261
  · exact R55263
  · exact R55265
  · exact R55267
  · exact R55269
  · exact R55271
  · exact R55273
  · exact R55275
  · exact R55277
  · exact R55279
  · exact R55281
  · exact R55283
  · exact R55285
  · exact R55287
  · exact R55289
  · exact R55291
  · exact R55293
  · exact R55295
  · exact R55297
  · exact R55299
  · exact R55301
  · exact R55303
  · exact R55305
  · exact R55307
  · exact R55309
  · exact R55311
  · exact R55313
  · exact R55315
  · exact R55317
  · exact R55319
  · exact R55321
  · exact R55323
  · exact R55325
  · exact R55327
  · exact R55329
  · exact R55331
  · exact R55333
  · exact R55335
  · exact R55337
  · exact R55339
  · exact R55341
  · exact R55343
  · exact R55345
  · exact R55347
  · exact R55349
  · exact R55351
  · exact R55353
  · exact R55355
  · exact R55357
  · exact R55359
  · exact R55361
  · exact R55363
  · exact R55365
  · exact R55367
  · exact R55369
  · exact R55371
  · exact R55373
  · exact R55375
  · exact R55377
  · exact R55379
  · exact R55381
  · exact R55383
  · exact R55385
  · exact R55387
  · exact R55389
  · exact R55391
  · exact R55393
  · exact R55395
  · exact R55397
  · exact R55399
  · exact R55401
  · exact R55403
  · exact R55405
  · exact R55407
  · exact R55409
  · exact R55411
  · exact R55413
  · exact R55415
  · exact R55417
  · exact R55419
  · exact R55421
  · exact R55423
  · exact R55425
  · exact R55427
  · exact R55429
  · exact R55431
  · exact R55433
  · exact R55435
  · exact R55437
  · exact R55439
  · exact R55441
  · exact R55443
  · exact R55445
  · exact R55447
  · exact R55449
  · exact R55451
  · exact R55453
  · exact R55455
  · exact R55457
  · exact R55459
  · exact R55461
  · exact R55463
  · exact R55465
  · exact R55467
  · exact R55469
  · exact R55471
  · exact R55473
  · exact R55475
  · exact R55477
  · exact R55479
  · exact R55481
  · exact R55483
  · exact R55485
  · exact R55487
  · exact R55489
  · exact R55491
  · exact R55493
  · exact R55495
  · exact R55497
  · exact R55499
  · exact R55501
  · exact R55503
  · exact R55505
  · exact R55507
  · exact R55509
  · exact R55511
  · exact R55513
  · exact R55515
  · exact R55517
  · exact R55519
  · exact R55521
  · exact R55523
  · exact R55525
  · exact R55527
  · exact R55529
  · exact R55531
  · exact R55533
  · exact R55535
  · exact R55537
  · exact R55539
  · exact R55541
  · exact R55543
  · exact R55545
  · exact R55547
  · exact R55549
  · exact R55551
  · exact R55553
  · exact R55555
  · exact R55557
  · exact R55559
  · exact R55561
  · exact R55563
  · exact R55565
  · exact R55567
  · exact R55569
  · exact R55571
  · exact R55573
  · exact R55575
  · exact R55577
  · exact R55579
  · exact R55581
  · exact R55583
  · exact R55585
  · exact R55587
  · exact R55589
  · exact R55591
  · exact R55593
  · exact R55595
  · exact R55597
  · exact R55599
  · exact R55601
  · exact R55603
  · exact R55605
  · exact R55607
  · exact R55609
  · exact R55611
  · exact R55613
  · exact R55615
  · exact R55617
  · exact R55619
  · exact R55621
  · exact R55623
  · exact R55625
  · exact R55627
  · exact R55629
  · exact R55631
  · exact R55633
  · exact R55635
  · exact R55637
  · exact R55639
  · exact R55641
  · exact R55643
  · exact R55645
  · exact R55647
  · exact R55649
  · exact R55651
  · exact R55653
  · exact R55655
  · exact R55657
  · exact R55659
  · exact R55661
  · exact R55663
  · exact R55665
  · exact R55667
  · exact R55669
  · exact R55671
  · exact R55673
  · exact R55675
  · exact R55677
  · exact R55679
  · exact R55681
  · exact R55683
  · exact R55685
  · exact R55687
  · exact R55689
  · exact R55691
  · exact R55693
  · exact R55695
  · exact R55697
  · exact R55699
  · exact R55701
  · exact R55703
  · exact R55705
  · exact R55707
  · exact R55709
  · exact R55711
  · exact R55713
  · exact R55715
  · exact R55717
  · exact R55719
  · exact R55721
  · exact R55723
  · exact R55725
  · exact R55727
  · exact R55729
  · exact R55731
  · exact R55733
  · exact R55735
  · exact R55737
  · exact R55739
  · exact R55741
  · exact R55743
  · exact R55745
  · exact R55747
  · exact R55749
  · exact R55751
  · exact R55753
  · exact R55755
  · exact R55757
  · exact R55759
  · exact R55761
  · exact R55763
  · exact R55765
  · exact R55767
  · exact R55769
  · exact R55771
  · exact R55773
  · exact R55775
  · exact R55777
  · exact R55779
  · exact R55781
  · exact R55783
  · exact R55785
  · exact R55787
  · exact R55789
  · exact R55791
  · exact R55793
  · exact R55795
  · exact R55797
  · exact R55799
  · exact R55801
  · exact R55803
  · exact R55805
  · exact R55807
  · exact R55809
  · exact R55811
  · exact R55813
  · exact R55815
  · exact R55817
  · exact R55819
  · exact R55821
  · exact R55823
  · exact R55825
  · exact R55827
  · exact R55829
  · exact R55831
  · exact R55833
  · exact R55835
  · exact R55837
  · exact R55839
  · exact R55841
  · exact R55843
  · exact R55845
  · exact R55847
  · exact R55849
  · exact R55851
  · exact R55853
  · exact R55855
  · exact R55857
  · exact R55859
  · exact R55861
  · exact R55863
  · exact R55865
  · exact R55867
  · exact R55869
  · exact R55871
  · exact R55873
  · exact R55875
  · exact R55877
  · exact R55879
  · exact R55881
  · exact R55883
  · exact R55885
  · exact R55887
  · exact R55889
  · exact R55891
  · exact R55893
  · exact R55895
  · exact R55897
  · exact R55899
  · exact R55901
  · exact R55903
  · exact R55905
  · exact R55907
  · exact R55909
  · exact R55911
  · exact R55913
  · exact R55915
  · exact R55917
  · exact R55919
  · exact R55921
  · exact R55923
  · exact R55925
  · exact R55927
  · exact R55929
  · exact R55931
  · exact R55933
  · exact R55935
  · exact R55937
  · exact R55939
  · exact R55941
  · exact R55943
  · exact R55945
  · exact R55947
  · exact R55949
  · exact R55951
  · exact R55953
  · exact R55955
  · exact R55957
  · exact R55959
  · exact R55961
  · exact R55963
  · exact R55965
  · exact R55967
  · exact R55969
  · exact R55971
  · exact R55973
  · exact R55975
  · exact R55977
  · exact R55979
  · exact R55981
  · exact R55983
  · exact R55985
  · exact R55987
  · exact R55989
  · exact R55991
  · exact R55993
  · exact R55995
  · exact R55997
  · exact R55999
  · exact R56001
  · exact R56003
  · exact R56005
  · exact R56007
  · exact R56009
  · exact R56011
  · exact R56013
  · exact R56015
  · exact R56017
  · exact R56019
  · exact R56021
  · exact R56023
  · exact R56025
  · exact R56027
  · exact R56029
  · exact R56031
  · exact R56033
  · exact R56035
  · exact R56037
  · exact R56039
  · exact R56041
  · exact R56043
  · exact R56045
  · exact R56047
  · exact R56049
  · exact R56051
  · exact R56053
  · exact R56055
  · exact R56057
  · exact R56059
  · exact R56061
  · exact R56063
  · exact R56065
  · exact R56067
  · exact R56069
  · exact R56071
  · exact R56073
  · exact R56075
  · exact R56077
  · exact R56079
  · exact R56081
  · exact R56083
  · exact R56085
  · exact R56087
  · exact R56089
  · exact R56091
  · exact R56093
  · exact R56095
  · exact R56097
  · exact R56099
  · exact R56101
  · exact R56103
  · exact R56105
  · exact R56107
  · exact R56109
  · exact R56111
  · exact R56113
  · exact R56115
  · exact R56117
  · exact R56119
  · exact R56121
  · exact R56123
  · exact R56125
  · exact R56127
  · exact R56129
  · exact R56131
  · exact R56133
  · exact R56135
  · exact R56137
  · exact R56139
  · exact R56141
  · exact R56143
  · exact R56145
  · exact R56147
  · exact R56149
  · exact R56151
  · exact R56153
  · exact R56155
  · exact R56157
  · exact R56159
  · exact R56161
  · exact R56163
  · exact R56165
  · exact R56167
  · exact R56169
  · exact R56171
  · exact R56173
  · exact R56175
  · exact R56177
  · exact R56179
  · exact R56181
  · exact R56183
  · exact R56185
  · exact R56187
  · exact R56189
  · exact R56191
  · exact R56193
  · exact R56195
  · exact R56197
  · exact R56199
  · exact R56201
  · exact R56203
  · exact R56205
  · exact R56207
  · exact R56209
  · exact R56211
  · exact R56213
  · exact R56215
  · exact R56217
  · exact R56219
  · exact R56221
  · exact R56223
  · exact R56225
  · exact R56227
  · exact R56229
  · exact R56231
  · exact R56233
  · exact R56235
  · exact R56237
  · exact R56239
  · exact R56241
  · exact R56243
  · exact R56245
  · exact R56247
  · exact R56249
  · exact R56251
  · exact R56253
  · exact R56255
  · exact R56257
  · exact R56259
  · exact R56261
  · exact R56263
  · exact R56265
  · exact R56267
  · exact R56269
  · exact R56271
  · exact R56273
  · exact R56275
  · exact R56277
  · exact R56279
  · exact R56281
  · exact R56283
  · exact R56285
  · exact R56287
  · exact R56289
  · exact R56291
  · exact R56293
  · exact R56295
  · exact R56297
  · exact R56299
  · exact R56301
  · exact R56303
  · exact R56305
  · exact R56307
  · exact R56309
  · exact R56311
  · exact R56313
  · exact R56315
  · exact R56317
  · exact R56319
  · exact R56321
  · exact R56323
  · exact R56325
  · exact R56327
  · exact R56329
  · exact R56331
  · exact R56333
  · exact R56335
  · exact R56337
  · exact R56339
  · exact R56341
  · exact R56343
  · exact R56345
  · exact R56347
  · exact R56349
  · exact R56351
  · exact R56353
  · exact R56355
  · exact R56357
  · exact R56359
  · exact R56361
  · exact R56363
  · exact R56365
  · exact R56367
  · exact R56369
  · exact R56371
  · exact R56373
  · exact R56375
  · exact R56377
  · exact R56379
  · exact R56381
  · exact R56383
  · exact R56385
  · exact R56387
  · exact R56389
  · exact R56391
  · exact R56393
  · exact R56395
  · exact R56397
  · exact R56399
  · exact R56401
  · exact R56403
  · exact R56405
  · exact R56407
  · exact R56409
  · exact R56411
  · exact R56413
  · exact R56415
  · exact R56417
  · exact R56419
  · exact R56421
  · exact R56423
  · exact R56425
  · exact R56427
  · exact R56429
  · exact R56431
  · exact R56433
  · exact R56435
  · exact R56437
  · exact R56439
  · exact R56441
  · exact R56443
  · exact R56445
  · exact R56447
  · exact R56449
  · exact R56451
  · exact R56453
  · exact R56455
  · exact R56457
  · exact R56459
  · exact R56461
  · exact R56463
  · exact R56465
  · exact R56467
  · exact R56469
  · exact R56471
  · exact R56473
  · exact R56475
  · exact R56477
  · exact R56479
  · exact R56481
  · exact R56483
  · exact R56485
  · exact R56487
  · exact R56489
  · exact R56491
  · exact R56493
  · exact R56495
  · exact R56497
  · exact R56499
  · exact R56501
  · exact R56503
  · exact R56505
  · exact R56507
  · exact R56509
  · exact R56511
  · exact R56513
  · exact R56515
  · exact R56517
  · exact R56519

theorem C1 (j : ℕ) (h1 : 28260 ≤ j) (h2 : j ≤ 28959) : Reach (2 * j + 1) := by
  interval_cases j
  · exact R56521
  · exact R56523
  · exact R56525
  · exact R56527
  · exact R56529
  · exact R56531
  · exact R56533
  · exact R56535
  · exact R56537
  · exact R56539
  · exact R56541
  · exact R56543
  · exact R56545
  · exact R56547
  · exact R56549
  · exact R56551
  · exact R56553
  · exact R56555
  · exact R56557
  · exact R56559
  · exact R56561
  · exact R56563
  · exact R56565
  · exact R56567
  · exact R56569
  · exact R56571
  · exact R56573
  · exact R56575
  · exact R56577
  · exact R56579
  · exact R56581
  · exact R56583
  · exact R56585
  · exact R56587
  · exact R56589
  · exact R56591
  · exact R56593
  · exact R56595
  · exact R56597
  · exact R56599
  · exact R56601
  · exact R56603
  · exact R56605
  · exact R56607
  · exact R56609
  · exact R56611
  · exact R56613
  · exact R56615
  · exact R56617
  · exact R56619
  · exact R56621
  · exact R56623
  · exact R56625
  · exact R56627
  · exact R56629
  · exact R56631
  · exact R56633
  · exact R56635
  · exact R56637
  · exact R56639
  · exact R56641
  · exact R56643
  · exact R56645
  · exact R56647
  · exact R56649
  · exact R56651
  · exact R56653
  · exact R56655
  · exact R56657
  · exact R56659
  · exact R56661
  · exact R56663
  · exact R56665
  · exact R56667
  · exact R56669
  · exact R56671
  · exact R56673
  · exact R56675
  · exact R56677
  · exact R56679
  · exact R56681
  · exact R56683
  · exact R56685
  · exact R56687
  · exact R56689
  · exact R56691
  · exact R56693
  · exact R56695
  · exact R56697
  · exact R56699
  · exact R56701
  · exact R56703
  · exact R56705
  · exact R56707
  · exact R56709
  · exact R56711
  · exact R56713
  · exact R56715
  · exact R56717
  · exact R56719
  · exact R56721
  · exact R56723
  · exact R56725
  · exact R56727
  · exact R56729
  · exact R56731
  · exact R56733
  · exact R56735
  · exact R56737
  · exact R56739
  · exact R56741
  · exact R56743
  · exact R56745
  · exact R56747
  · exact R56749
  · exact R56751
  · exact R56753
  · exact R56755
  · exact R56757
  · exact R56759
  · exact R56761
  · exact R56763
  · exact R56765
  · exact R56767
  · exact R56769
  · exact R56771
  · exact R56773
  · exact R56775
  · exact R56777
  · exact R56779
  · exact R56781
  · exact R56783
  · exact R56785
  · exact R56787
  · exact R56789
  · exact R56791
  · exact R56793
  · exact R56795
  · exact R56797
  · exact R56799
  · exact R56801
  · exact R56803
  · exact R56805
  · exact R56807
  · exact R56809
  · exact R56811
  · exact R56813
  · exact R56815
  · exact R56817
  · exact R56819
  · exact R56821
  · exact R56823
  · exact R56825
  · exact R56827
  · exact R56829
  · exact R56831
  · exact R56833
  · exact R56835
  · exact R56837
  · exact R56839
  · exact R56841
  · exact R56843
  · exact R56845
  · exact R56847
  · exact R56849
  · exact R56851
  · exact R56853
  · exact R56855
  · exact R56857
  · exact R56859
  · exact R56861
  · exact R56863
  · exact R56865
  · exact R56867
  · exact R56869
  · exact R56871
  · exact R56873
  · exact R56875
  · exact R56877
  · exact R56879
  · exact R56881
  · exact R56883
  · exact R56885
  · exact R56887
  · exact R56889
  · exact R56891
  · exact R56893
  · exact R56895
  · exact R56897
  · exact R56899
  · exact R56901
  · exact R56903
  · exact R56905
  · exact R56907
  · exact R56909
  · exact R56911
  · exact R56913
  · exact R56915
  · exact R56917
  · exact R56919
  · exact R56921
  · exact R56923
  · exact R56925
  · exact R56927
  · exact R56929
  · exact R56931
  · exact R56933
  · exact R56935
  · exact R56937
  · exact R56939
  · exact R56941
  · exact R56943
  · exact R56945
  · exact R56947
  · exact R56949
  · exact R56951
  · exact R56953
  · exact R56955
  · exact R56957
  · exact R56959
  · exact R56961
  · exact R56963
  · exact R56965
  · exact R56967
  · exact R56969
  · exact R56971
  · exact R56973
  · exact R56975
  · exact R56977
  · exact R56979
  · exact R56981
  · exact R56983
  · exact R56985
  · exact R56987
  · exact R56989
  · exact R56991
  · exact R56993
  · exact R56995
  · exact R56997
  · exact R56999
  · exact R57001
  · exact R57003
  · exact R57005
  · exact R57007
  · exact R57009
  · exact R57011
  · exact R57013
  · exact R57015
  · exact R57017
  · exact R57019
  · exact R57021
  · exact R57023
  · exact R57025
  · exact R57027
  · exact R57029
  · exact R57031
  · exact R57033
  · exact R57035
  · exact R57037
  · exact R57039
  · exact R57041
  · exact R57043
  · exact R57045
  · exact R57047
  · exact R57049
  · exact R57051
  · exact R57053
  · exact R57055
  · exact R57057
  · exact R57059
  · exact R57061
  · exact R57063
  · exact R57065
  · exact R57067
  · exact R57069
  · exact R57071
  · exact R57073
  · exact R57075
  · exact R57077
  · exact R57079
  · exact R57081
  · exact R57083
  · exact R57085
  · exact R57087
  · exact R57089
  · exact R57091
  · exact R57093
  · exact R57095
  · exact R57097
  · exact R57099
  · exact R57101
  · exact R57103
  · exact R57105
  · exact R57107
  · exact R57109
  · exact R57111
  · exact R57113
  · exact R57115
  · exact R57117
  · exact R57119
  · exact R57121
  · exact R57123
  · exact R57125
  · exact R57127
  · exact R57129
  · exact R57131
  · exact R57133
  · exact R57135
  · exact R57137
  · exact R57139
  · exact R57141
  · exact R57143
  · exact R57145
  · exact R57147
  · exact R57149
  · exact R57151
  · exact R57153
  · exact R57155
  · exact R57157
  · exact R57159
  · exact R57161
  · exact R57163
  · exact R57165
  · exact R57167
  · exact R57169
  · exact R57171
  · exact R57173
  · exact R57175
  · exact R57177
  · exact R57179
  · exact R57181
  · exact R57183
  · exact R57185
  · exact R57187
  · exact R57189
  · exact R57191
  · exact R57193
  · exact R57195
  · exact R57197
  · exact R57199
  · exact R57201
  · exact R57203
  · exact R57205
  · exact R57207
  · exact R57209
  · exact R57211
  · exact R57213
  · exact R57215
  · exact R57217
  · exact R57219
  · exact R57221
  · exact R57223
  · exact R57225
  · exact R57227
  · exact R57229
  · exact R57231
  · exact R57233
  · exact R57235
  · exact R57237
  · exact R57239
  · exact R57241
  · exact R57243
  · exact R57245
  · exact R57247
  · exact R57249
  · exact R57251
  · exact R57253
  · exact R57255
  · exact R57257
  · exact R57259
  · exact R57261
  · exact R57263
  · exact R57265
  · exact R57267
  · exact R57269
  · exact R57271
  · exact R57273
  · exact R57275
  · exact R57277
  · exact R57279
  · exact R57281
  · exact R57283
  · exact R57285
  · exact R57287
  · exact R57289
  · exact R57291
  · exact R57293
  · exact R57295
  · exact R57297
  · exact R57299
  · exact R57301
  · exact R57303
  · exact R57305
  · exact R57307
  · exact R57309
  · exact R57311
  · exact R57313
  · exact R57315
  · exact R57317
  · exact R57319
  · exact R57321
  · exact R57323
  · exact R57325
  · exact R57327
  · exact R57329
  · exact R57331
  · exact R57333
  · exact R57335
  · exact R57337
  · exact R57339
  · exact R57341
  · exact R57343
  · exact R57345
  · exact R57347
  · exact R57349
  · exact R57351
  · exact R57353
  · exact R57355
  · exact R57357
  · exact R57359
  · exact R57361
  · exact R57363
  · exact R57365
  · exact R57367
  · exact R57369
  · exact R57371
  · exact R57373
  · exact R57375
  · exact R57377
  · exact R57379
  · exact R57381
  · exact R57383
  · exact R57385
  · exact R57387
  · exact R57389
  · exact R57391
  · exact R57393
  · exact R57395
  · exact R57397
  · exact R57399
  · exact R57401
  · exact R57403
  · exact R57405
  · exact R57407
  · exact R57409
  · exact R57411
  · exact R57413
  · exact R57415
  · exact R57417
  · exact R57419
  · exact R57421
  · exact R57423
  · exact R57425
  · exact R57427
  · exact R57429
  · exact R57431
  · exact R57433
  · exact R57435
  · exact R57437
  · exact R57439
  · exact R57441
  · exact R57443
  · exact R57445
  · exact R57447
  · exact R57449
  · exact R57451
  · exact R57453
  · exact R57455
  · exact R57457
  · exact R57459
  · exact R57461
  · exact R57463
  · exact R57465
  · exact R57467
  · exact R57469
  · exact R57471
  · exact R57473
  · exact R57475
  · exact R57477
  · exact R57479
  · exact R57481
  · exact R57483
  · exact R57485
  · exact R57487
  · exact R57489
  · exact R57491
  · exact R57493
  · exact R57495
  · exact R57497
  · exact R57499
  · exact R57501
  · exact R57503
  · exact R57505
  · exact R57507
  · exact R57509
  · exact R57511
  · exact R57513
  · exact R57515
  · exact R57517
  · exact R57519
  · exact R57521
  · exact R57523
  · exact R57525
  · exact R57527
  · exact R57529
  · exact R57531
  · exact R57533
  · exact R57535
  · exact R57537
  · exact R57539
  · exact R57541
  · exact R57543
  · exact R57545
  · exact R57547
  · exact R57549
  · exact R57551
  · exact R57553
  · exact R57555
  · exact R57557
  · exact R57559
  · exact R57561
  · exact R57563
  · exact R57565
  · exact R57567
  · exact R57569
  · exact R57571
  · exact R57573
  · exact R57575
  · exact R57577
  · exact R57579
  · exact R57581
  · exact R57583
  · exact R57585
  · exact R57587
  · exact R57589
  · exact R57591
  · exact R57593
  · exact R57595
  · exact R57597
  · exact R57599
  · exact R57601
  · exact R57603
  · exact R57605
  · exact R57607
  · exact R57609
  · exact R57611
  · exact R57613
  · exact R57615
  · exact R57617
  · exact R57619
  · exact R57621
  · exact R57623
  · exact R57625
  · exact R57627
  · exact R57629
  · exact R57631
  · exact R57633
  · exact R57635
  · exact R57637
  · exact R57639
  · exact R57641
  · exact R57643
  · exact R57645
  · exact R57647
  · exact R57649
  · exact R57651
  · exact R57653
  · exact R57655
  · exact R57657
  · exact R57659
  · exact R57661
  · exact R57663
  · exact R57665
  · exact R57667
  · exact R57669
  · exact R57671
  · exact R57673
  · exact R57675
  · exact R57677
  · exact R57679
  · exact R57681
  · exact R57683
  · exact R57685
  · exact R57687
  · exact R57689
  · exact R57691
  · exact R57693
  · exact R57695
  · exact R57697
  · exact R57699
  · exact R57701
  · exact R57703
  · exact R57705
  · exact R57707
  · exact R57709
  · exact R57711
  · exact R57713
  · exact R57715
  · exact R57717
  · exact R57719
  · exact R57721
  · exact R57723
  · exact R57725
  · exact R57727
  · exact R57729
  · exact R57731
  · exact R57733
  · exact R57735
  · exact R57737
  · exact R57739
  · exact R57741
  · exact R57743
  · exact R57745
  · exact R57747
  · exact R57749
  · exact R57751
  · exact R57753
  · exact R57755
  · exact R57757
  · exact R57759
  · exact R57761
  · exact R57763
  · exact R57765
  · exact R57767
  · exact R57769
  · exact R57771
  · exact R57773
  · exact R57775
  · exact R57777
  · exact R57779
  · exact R57781
  · exact R57783
  · exact R57785
  · exact R57787
  · exact R57789
  · exact R57791
  · exact R57793
  · exact R57795
  · exact R57797
  · exact R57799
  · exact R57801
  · exact R57803
  · exact R57805
  · exact R57807
  · exact R57809
  · exact R57811
  · exact R57813
  · exact R57815
  · exact R57817
  · exact R57819
  · exact R57821
  · exact R57823
  · exact R57825
  · exact R57827
  · exact R57829
  · exact R57831
  · exact R57833
  · exact R57835
  · exact R57837
  · exact R57839
  · exact R57841
  · exact R57843
  · exact R57845
  · exact R57847
  · exact R57849
  · exact R57851
  · exact R57853
  · exact R57855
  · exact R57857
  · exact R57859
  · exact R57861
  · exact R57863
  · exact R57865
  · exact R57867
  · exact R57869
  · exact R57871
  · exact R57873
  · exact R57875
  · exact R57877
  · exact R57879
  · exact R57881
  · exact R57883
  · exact R57885
  · exact R57887
  · exact R57889
  · exact R57891
  · exact R57893
  · exact R57895
  · exact R57897
  · exact R57899
  · exact R57901
  · exact R57903
  · exact R57905
  · exact R57907
  · exact R57909
  · exact R57911
  · exact R57913
  · exact R57915
  · exact R57917
  · exact R57919

theorem C2 (j : ℕ) (h1 : 28960 ≤ j) (h2 : j ≤ 29560) : Reach (2 * j + 1) := by
  interval_cases j
  · exact R57921
  · exact R57923
  · exact R57925
  · exact R57927
  · exact R57929
  · exact R57931
  · exact R57933
  · exact R57935
  · exact R57937
  · exact R57939
  · exact R57941
  · exact R57943
  · exact R57945
  · exact R57947
  · exact R57949
  · exact R57951
  · exact R57953
  · exact R57955
  · exact R57957
  · exact R57959
  · exact R57961
  · exact R57963
  · exact R57965
  · exact R57967
  · exact R57969
  · exact R57971
  · exact R57973
  · exact R57975
  · exact R57977
  · exact R57979
  · exact R57981
  · exact R57983
  · exact R57985
  · exact R57987
  · exact R57989
  · exact R57991
  · exact R57993
  · exact R57995
  · exact R57997
  · exact R57999
  · exact R58001
  · exact R58003
  · exact R58005
  · exact R58007
  · exact R58009
  · exact R58011
  · exact R58013
  · exact R58015
  · exact R58017
  · exact R58019
  · exact R58021
  · exact R58023
  · exact R58025
  · exact R58027
  · exact R58029
  · exact R58031
  · exact R58033
  · exact R58035
  · exact R58037
  · exact R58039
  · exact R58041
  · exact R58043
  · exact R58045
  · exact R58047
  · exact R58049
  · exact R58051
  · exact R58053
  · exact R58055
  · exact R58057
  · exact R58059
  · exact R58061
  · exact R58063
  · exact R58065
  · exact R58067
  · exact R58069
  · exact R58071
  · exact R58073
  · exact R58075
  · exact R58077
  · exact R58079
  · exact R58081
  · exact R58083
  · exact R58085
  · exact R58087
  · exact R58089
  · exact R58091
  · exact R58093
  · exact R58095
  · exact R58097
  · exact R58099
  · exact R58101
  · exact R58103
  · exact R58105
  · exact R58107
  · exact R58109
  · exact R58111
  · exact R58113
  · exact R58115
  · exact R58117
  · exact R58119
  · exact R58121
  · exact R58123
  · exact R58125
  · exact R58127
  · exact R58129
  · exact R58131
  · exact R58133
  · exact R58135
  · exact R58137
  · exact R58139
  · exact R58141
  · exact R58143
  · exact R58145
  · exact R58147
  · exact R58149
  · exact R58151
  · exact R58153
  · exact R58155
  · exact R58157
  · exact R58159
  · exact R58161
  · exact R58163
  · exact R58165
  · exact R58167
  · exact R58169
  · exact R58171
  · exact R58173
  · exact R58175
  · exact R58177
  · exact R58179
  · exact R58181
  · exact R58183
  · exact R58185
  · exact R58187
  · exact R58189
  · exact R58191
  · exact R58193
  · exact R58195
  · exact R58197
  · exact R58199
  · exact R58201
  · exact R58203
  · exact R58205
  · exact R58207
  · exact R58209
  · exact R58211
  · exact R58213
  · exact R58215
  · exact R58217
  · exact R58219
  · exact R58221
  · exact R58223
  · exact R58225
  · exact R58227
  · exact R58229
  · exact R58231
  · exact R58233
  · exact R58235
  · exact R58237
  · exact R58239
  · exact R58241
  · exact R58243
  · exact R58245
  · exact R58247
  · exact R58249
  · exact R58251
  · exact R58253
  · exact R58255
  · exact R58257
  · exact R58259
  · exact R58261
  · exact R58263
  · exact R58265
  · exact R58267
  · exact R58269
  · exact R58271
  · exact R58273
  · exact R58275
  · exact R58277
  · exact R58279
  · exact R58281
  · exact R58283
  · exact R58285
  · exact R58287
  · exact R58289
  · exact R58291
  · exact R58293
  · exact R58295
  · exact R58297
  · exact R58299
  · exact R58301
  · exact R58303
  · exact R58305
  · exact R58307
  · exact R58309
  · exact R58311
  · exact R58313
  · exact R58315
  · exact R58317
  · exact R58319
  · exact R58321
  · exact R58323
  · exact R58325
  · exact R58327
  · exact R58329
  · exact R58331
  · exact R58333
  · exact R58335
  · exact R58337
  · exact R58339
  · exact R58341
  · exact R58343
  · exact R58345
  · exact R58347
  · exact R58349
  · exact R58351
  · exact R58353
  · exact R58355
  · exact R58357
  · exact R58359
  · exact R58361
  · exact R58363
  · exact R58365
  · exact R58367
  · exact R58369
  · exact R58371
  · exact R58373
  · exact R58375
  · exact R58377
  · exact R58379
  · exact R58381
  · exact R58383
  · exact R58385
  · exact R58387
  · exact R58389
  · exact R58391
  · exact R58393
  · exact R58395
  · exact R58397
  · exact R58399
  · exact R58401
  · exact R58403
  · exact R58405
  · exact R58407
  · exact R58409
  · exact R58411
  · exact R58413
  · exact R58415
  · exact R58417
  · exact R58419
  · exact R58421
  · exact R58423
  · exact R58425
  · exact R58427
  · exact R58429
  · exact R58431
  · exact R58433
  · exact R58435
  · exact R58437
  · exact R58439
  · exact R58441
  · exact R58443
  · exact R58445
  · exact R58447
  · exact R58449
  · exact R58451
  · exact R58453
  · exact R58455
  · exact R58457
  · exact R58459
  · exact R58461
  · exact R58463
  · exact R58465
  · exact R58467
  · exact R58469
  · exact R58471
  · exact R58473
  · exact R58475
  · exact R58477
  · exact R58479
  · exact R58481
  · exact R58483
  · exact R58485
  · exact R58487
  · exact R58489
  · exact R58491
  · exact R58493
  · exact R58495
  · exact R58497
  · exact R58499
  · exact R58501
  · exact R58503
  · exact R58505
  · exact R58507
  · exact R58509
  · exact R58511
  · exact R58513
  · exact R58515
  · exact R58517
  · exact R58519
  · exact R58521
  · exact R58523
  · exact R58525
  · exact R58527
  · exact R58529
  · exact R58531
  · exact R58533
  · exact R58535
  · exact R58537
  · exact R58539
  · exact R58541
  · exact R58543
  · exact R58545
  · exact R58547
  · exact R58549
  · exact R58551
  · exact R58553
  · exact R58555
  · exact R58557
  · exact R58559
  · exact R58561
  · exact R58563
  · exact R58565
  · exact R58567
  · exact R58569
  · exact R58571
  · exact R58573
  · exact R58575
  · exact R58577
  · exact R58579
  · exact R58581
  · exact R58583
  · exact R58585
  · exact R58587
  · exact R58589
  · exact R58591
  · exact R58593
  · exact R58595
  · exact R58597
  · exact R58599
  · exact R58601
  · exact R58603
  · exact R58605
  · exact R58607
  · exact R58609
  · exact R58611
  · exact R58613
  · exact R58615
  · exact R58617
  · exact R58619
  · exact R58621
  · exact R58623
  · exact R58625
  · exact R58627
  · exact R58629
  · exact R58631
  · exact R58633
  · exact R58635
  · exact R58637
  · exact R58639
  · exact R58641
  · exact R58643
  · exact R58645
  · exact R58647
  · exact R58649
  · exact R58651
  · exact R58653
  · exact R58655
  · exact R58657
  · exact R58659
  · exact R58661
  · exact R58663
  · exact R58665
  · exact R58667
  · exact R58669
  · exact R58671
  · exact R58673
  · exact R58675
  · exact R58677
  · exact R58679
  · exact R58681
  · exact R58683
  · exact R58685
  · exact R58687
  · exact R58689
  · exact R58691
  · exact R58693
  · exact R58695
  · exact R58697
  · exact R58699
  · exact R58701
  · exact R58703
  · exact R58705
  · exact R58707
  · exact R58709
  · exact R58711
  · exact R58713
  · exact R58715
  · exact R58717
  · exact R58719
  · exact R58721
  · exact R58723
  · exact R58725
  · exact R58727
  · exact R58729
  · exact R58731
  · exact R58733
  · exact R58735
  · exact R58737
  · exact R58739
  · exact R58741
  · exact R58743
  · exact R58745
  · exact R58747
  · exact R58749
  · exact R58751
  · exact R58753
  · exact R58755
  · exact R58757
  · exact R58759
  · exact R58761
  · exact R58763
  · exact R58765
  · exact R58767
  · exact R58769
  · exact R58771
  · exact R58773
  · exact R58775
  · exact R58777
  · exact R58779
  · exact R58781
  · exact R58783
  · exact R58785
  · exact R58787
  · exact R58789
  · exact R58791
  · exact R58793
  · exact R58795
  · exact R58797
  · exact R58799
  · exact R58801
  · exact R58803
  · exact R58805
  · exact R58807
  · exact R58809
  · exact R58811
  · exact R58813
  · exact R58815
  · exact R58817
  · exact R58819
  · exact R58821
  · exact R58823
  · exact R58825
  · exact R58827
  · exact R58829
  · exact R58831
  · exact R58833
  · exact R58835
  · exact R58837
  · exact R58839
  · exact R58841
  · exact R58843
  · exact R58845
  · exact R58847
  · exact R58849
  · exact R58851
  · exact R58853
  · exact R58855
  · exact R58857
  · exact R58859
  · exact R58861
  · exact R58863
  · exact R58865
  · exact R58867
  · exact R58869
  · exact R58871
  · exact R58873
  · exact R58875
  · exact R58877
  · exact R58879
  · exact R58881
  · exact R58883
  · exact R58885
  · exact R58887
  · exact R58889
  · exact R58891
  · exact R58893
  · exact R58895
  · exact R58897
  · exact R58899
  · exact R58901
  · exact R58903
  · exact R58905
  · exact R58907
  · exact R58909
  · exact R58911
  · exact R58913
  · exact R58915
  · exact R58917
  · exact R58919
  · exact R58921
  · exact R58923
  · exact R58925
  · exact R58927
  · exact R58929
  · exact R58931
  · exact R58933
  · exact R58935
  · exact R58937
  · exact R58939
  · exact R58941
  · exact R58943
  · exact R58945
  · exact R58947
  · exact R58949
  · exact R58951
  · exact R58953
  · exact R58955
  · exact R58957
  · exact R58959
  · exact R58961
  · exact R58963
  · exact R58965
  · exact R58967
  · exact R58969
  · exact R58971
  · exact R58973
  · exact R58975
  · exact R58977
  · exact R58979
  · exact R58981
  · exact R58983
  · exact R58985
  · exact R58987
  · exact R58989
  · exact R58991
  · exact R58993
  · exact R58995
  · exact R58997
  · exact R58999
  · exact R59001
  · exact R59003
  · exact R59005
  · exact R59007
  · exact R59009
  · exact R59011
  · exact R59013
  · exact R59015
  · exact R59017
  · exact R59019
  · exact R59021
  · exact R59023
  · exact R59025
  · exact R59027
  · exact R59029
  · exact R59031
  · exact R59033
  · exact R59035
  · exact R59037
  · exact R59039
  · exact R59041
  · exact R59043
  · exact R59045
  · exact R59047
  · exact R59049
  · exact R59051
  · exact R59053
  · exact R59055
  · exact R59057
  · exact R59059
  · exact R59061
  · exact R59063
  · exact R59065
  · exact R59067
  · exact R59069
  · exact R59071
  · exact R59073
  · exact R59075
  · exact R59077
  · exact R59079
  · exact R59081
  · exact R59083
  · exact R59085
  · exact R59087
  · exact R59089
  · exact R59091
  · exact R59093
  · exact R59095
  · exact R59097
  · exact R59099
  · exact R59101
  · exact R59103
  · exact R59105
  · exact R59107
  · exact R59109
  · exact R59111
  · exact R59113
  · exact R59115
  · exact R59117
  · exact R59119
  · exact R59121

theorem solution (m : ℕ) (hm : 0 < m) (hodd : Odd m) (hle : m ≤ 59121) :
    ∃ k : ℕ, syracuseStep^[k] m = 1 := by
  rcases Nat.lt_or_ge m 55121 with hlo | hlo
  · exact syracuse_reaches_one_below_55121 m hm hodd (by omega)
  obtain ⟨j, rfl⟩ : ∃ j, m = 2 * j + 1 := by obtain ⟨t, ht⟩ := hodd; exact ⟨t, by omega⟩
  rcases Nat.lt_or_ge j 28260 with h0 | h0
  · exact C0 j (by omega) (by omega)
  rcases Nat.lt_or_ge j 28960 with h1 | h1
  · exact C1 j (by omega) (by omega)
  exact C2 j (by omega) (by omega)
