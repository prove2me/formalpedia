-- Prove2me | solution 1 for syracuse_descends_range_1224430_1226430
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T22:10:59.966158+00:00
-- url     : https://prove2.me/submissions/4b288317-9f83-4112-bb9e-7b965ac07ffe

import Mathlib
import Definitions.Def_syracuseStep

set_option maxHeartbeats 1000000

open Nat

/-- Half of all odd numbers descend in a single Syracuse step, uniformly. -/
theorem step_lt_of_one_mod_four (m : ℕ) (h1 : 1 < m) (h4 : m % 4 = 1) : syracuseStep m < m := by
  have hne : 3 * m + 1 ≠ 0 := by omega
  have hdvd : (2:ℕ) ^ 2 ∣ 3 * m + 1 := by
    have : (4:ℕ) ∣ 3 * m + 1 := by omega
    simpa using this
  have hle : 2 ≤ (3 * m + 1).factorization 2 :=
    (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hne).mp hdvd
  have hpow : (2:ℕ) ^ 2 ≤ 2 ^ ((3 * m + 1).factorization 2) :=
    Nat.pow_le_pow_right (by norm_num) hle
  have h1' : syracuseStep m ≤ (3 * m + 1) / 2 ^ 2 := by
    show ordCompl[2] (3 * m + 1) ≤ _
    exact Nat.div_le_div_left hpow (by positivity)
  have h2' : (3 * m + 1) / 2 ^ 2 < m := by
    apply Nat.div_lt_of_lt_mul
    omega
  omega

/-- `Blo L x` : some Syracuse iterate of `x` drops below `L`. -/
abbrev Blo (L x : ℕ) : Prop := ∃ t : ℕ, syracuseStep^[t] x < L

theorem bbase {L x y : ℕ} (h : syracuseStep x = y) (hy : y < L) : Blo L x :=
  ⟨1, by rw [Function.iterate_one, h]; exact hy⟩

theorem bstep {L x y : ℕ} (h : syracuseStep x = y) (hy : Blo L y) : Blo L x := by
  obtain ⟨t, ht⟩ := hy
  exact ⟨t + 1, by rw [Function.iterate_add_apply, Function.iterate_one, h]; exact ht⟩

theorem se (a : ℕ) {y z : ℕ} (h : 3 * y + 1 = 2 ^ a * z) (hz : Odd z) :
    syracuseStep y = z := by
  have hz0 : z ≠ 0 := by rintro rfl; simp [Nat.odd_iff] at hz
  have hfac : (3 * y + 1).factorization 2 = a := by
    rw [h, Nat.factorization_mul (by positivity) hz0]
    simp [Nat.prime_two,
      Nat.factorization_eq_zero_of_not_dvd (by rwa [Nat.two_dvd_ne_zero, ← Nat.odd_iff])]
  show ordCompl[2] (3 * y + 1) = z
  rw [hfac, h, Nat.mul_div_cancel_left _ (by positivity)]


theorem B1572869 : Blo 1224430 1572869 := bbase (se 4 (by rfl) ⟨147456, by rfl⟩ : syracuseStep 1572869 = 294913) (by norm_num)
theorem B2326573 : Blo 1224430 2326573 := bbase (se 3 (by rfl) ⟨436232, by rfl⟩ : syracuseStep 2326573 = 872465) (by norm_num)
theorem B1745021 : Blo 1224430 1745021 := bbase (se 3 (by rfl) ⟨327191, by rfl⟩ : syracuseStep 1745021 = 654383) (by norm_num)
theorem B11772053 : Blo 1224430 11772053 := bbase (se 6 (by rfl) ⟨275907, by rfl⟩ : syracuseStep 11772053 = 551815) (by norm_num)
theorem B1745101 : Blo 1224430 1745101 := bbase (se 3 (by rfl) ⟨327206, by rfl⟩ : syracuseStep 1745101 = 654413) (by norm_num)
theorem B1654997 : Blo 1224430 1654997 := bbase (se 7 (by rfl) ⟨19394, by rfl⟩ : syracuseStep 1654997 = 38789) (by norm_num)
theorem B3924197 : Blo 1224430 3924197 := bbase (se 4 (by rfl) ⟨367893, by rfl⟩ : syracuseStep 3924197 = 735787) (by norm_num)
theorem B1327385 : Blo 1224430 1327385 := bbase (se 2 (by rfl) ⟨497769, by rfl⟩ : syracuseStep 1327385 = 995539) (by norm_num)
theorem B1573177 : Blo 1224430 1573177 := bbase (se 2 (by rfl) ⟨589941, by rfl⟩ : syracuseStep 1573177 = 1179883) (by norm_num)
theorem B1745221 : Blo 1224430 1745221 := bbase (se 4 (by rfl) ⟨163614, by rfl⟩ : syracuseStep 1745221 = 327229) (by norm_num)
theorem B2326877 : Blo 1224430 2326877 := bbase (se 3 (by rfl) ⟨436289, by rfl⟩ : syracuseStep 2326877 = 872579) (by norm_num)
theorem B4137317 : Blo 1224430 4137317 := bbase (se 4 (by rfl) ⟨387873, by rfl⟩ : syracuseStep 4137317 = 775747) (by norm_num)
theorem B3981685 : Blo 1224430 3981685 := bbase (se 5 (by rfl) ⟨186641, by rfl⟩ : syracuseStep 3981685 = 373283) (by norm_num)
theorem B3023237 : Blo 1224430 3023237 := bbase (se 4 (by rfl) ⟨283428, by rfl⟩ : syracuseStep 3023237 = 566857) (by norm_num)
theorem B3924389 : Blo 1224430 3924389 := bbase (se 4 (by rfl) ⟨367911, by rfl⟩ : syracuseStep 3924389 = 735823) (by norm_num)
theorem B1745317 : Blo 1224430 1745317 := bbase (se 4 (by rfl) ⟨163623, by rfl⟩ : syracuseStep 1745317 = 327247) (by norm_num)
theorem B6201845 : Blo 1224430 6201845 := bbase (se 5 (by rfl) ⟨290711, by rfl⟩ : syracuseStep 6201845 = 581423) (by norm_num)
theorem B4653557 : Blo 1224430 4653557 := bbase (se 5 (by rfl) ⟨218135, by rfl⟩ : syracuseStep 4653557 = 436271) (by norm_num)
theorem B4194917 : Blo 1224430 4194917 := bbase (se 4 (by rfl) ⟨393273, by rfl⟩ : syracuseStep 4194917 = 786547) (by norm_num)
theorem B2654893 : Blo 1224430 2654893 := bbase (se 3 (by rfl) ⟨497792, by rfl⟩ : syracuseStep 2654893 = 995585) (by norm_num)
theorem B4653845 : Blo 1224430 4653845 := bbase (se 6 (by rfl) ⟨109074, by rfl⟩ : syracuseStep 4653845 = 218149) (by norm_num)
theorem B4137749 : Blo 1224430 4137749 := bbase (se 6 (by rfl) ⟨96978, by rfl⟩ : syracuseStep 4137749 = 193957) (by norm_num)
theorem B17662805 : Blo 1224430 17662805 := bbase (se 9 (by rfl) ⟨51746, by rfl⟩ : syracuseStep 17662805 = 103493) (by norm_num)
theorem B2982757 : Blo 1224430 2982757 := bbase (se 4 (by rfl) ⟨279633, by rfl⟩ : syracuseStep 2982757 = 559267) (by norm_num)
theorem B1745813 : Blo 1224430 1745813 := bbase (se 6 (by rfl) ⟨40917, by rfl⟩ : syracuseStep 1745813 = 81835) (by norm_num)
theorem B7070773 : Blo 1224430 7070773 := bbase (se 5 (by rfl) ⟨331442, by rfl⟩ : syracuseStep 7070773 = 662885) (by norm_num)
theorem B2327629 : Blo 1224430 2327629 := bbase (se 3 (by rfl) ⟨436430, by rfl⟩ : syracuseStep 2327629 = 872861) (by norm_num)
theorem B4138181 : Blo 1224430 4138181 := bbase (se 4 (by rfl) ⟨387954, by rfl⟩ : syracuseStep 4138181 = 775909) (by norm_num)
theorem B2327773 : Blo 1224430 2327773 := bbase (se 3 (by rfl) ⟨436457, by rfl⟩ : syracuseStep 2327773 = 872915) (by norm_num)
theorem B3491045 : Blo 1224430 3491045 := bbase (se 4 (by rfl) ⟨327285, by rfl⟩ : syracuseStep 3491045 = 654571) (by norm_num)
theorem B1377517 : Blo 1224430 1377517 := bbase (se 3 (by rfl) ⟨258284, by rfl⟩ : syracuseStep 1377517 = 516569) (by norm_num)
theorem B1377553 : Blo 1224430 1377553 := bbase (se 2 (by rfl) ⟨516582, by rfl⟩ : syracuseStep 1377553 = 1033165) (by norm_num)
theorem B1377589 : Blo 1224430 1377589 := bbase (se 5 (by rfl) ⟨64574, by rfl⟩ : syracuseStep 1377589 = 129149) (by norm_num)
theorem B1377625 : Blo 1224430 1377625 := bbase (se 2 (by rfl) ⟨516609, by rfl⟩ : syracuseStep 1377625 = 1033219) (by norm_num)
theorem B1377661 : Blo 1224430 1377661 := bbase (se 3 (by rfl) ⟨258311, by rfl⟩ : syracuseStep 1377661 = 516623) (by norm_num)
theorem B2327933 : Blo 1224430 2327933 := bbase (se 3 (by rfl) ⟨436487, by rfl⟩ : syracuseStep 2327933 = 872975) (by norm_num)
theorem B1377697 : Blo 1224430 1377697 := bbase (se 2 (by rfl) ⟨516636, by rfl⟩ : syracuseStep 1377697 = 1033273) (by norm_num)
theorem B1377733 : Blo 1224430 1377733 := bbase (se 4 (by rfl) ⟨129162, by rfl⟩ : syracuseStep 1377733 = 258325) (by norm_num)
theorem B1549793 : Blo 1224430 1549793 := bbase (se 2 (by rfl) ⟨581172, by rfl⟩ : syracuseStep 1549793 = 1162345) (by norm_num)
theorem B1377769 : Blo 1224430 1377769 := bbase (se 2 (by rfl) ⟨516663, by rfl⟩ : syracuseStep 1377769 = 1033327) (by norm_num)
theorem B1377805 : Blo 1224430 1377805 := bbase (se 3 (by rfl) ⟨258338, by rfl⟩ : syracuseStep 1377805 = 516677) (by norm_num)
theorem B2328077 : Blo 1224430 2328077 := bbase (se 3 (by rfl) ⟨436514, by rfl⟩ : syracuseStep 2328077 = 873029) (by norm_num)
theorem B1549849 : Blo 1224430 1549849 := bbase (se 2 (by rfl) ⟨581193, by rfl⟩ : syracuseStep 1549849 = 1162387) (by norm_num)
theorem B1377841 : Blo 1224430 1377841 := bbase (se 2 (by rfl) ⟨516690, by rfl⟩ : syracuseStep 1377841 = 1033381) (by norm_num)
theorem B1377877 : Blo 1224430 1377877 := bbase (se 8 (by rfl) ⟨8073, by rfl⟩ : syracuseStep 1377877 = 16147) (by norm_num)
theorem B1836653 : Blo 1224430 1836653 := bbase (se 3 (by rfl) ⟨344372, by rfl⟩ : syracuseStep 1836653 = 688745) (by norm_num)
theorem B4138613 : Blo 1224430 4138613 := bbase (se 5 (by rfl) ⟨193997, by rfl⟩ : syracuseStep 4138613 = 387995) (by norm_num)
theorem B1549945 : Blo 1224430 1549945 := bbase (se 2 (by rfl) ⟨581229, by rfl⟩ : syracuseStep 1549945 = 1162459) (by norm_num)
theorem B1377913 : Blo 1224430 1377913 := bbase (se 2 (by rfl) ⟨516717, by rfl⟩ : syracuseStep 1377913 = 1033435) (by norm_num)
theorem B1836677 : Blo 1224430 1836677 := bbase (se 4 (by rfl) ⟨172188, by rfl⟩ : syracuseStep 1836677 = 344377) (by norm_num)
theorem B5891717 : Blo 1224430 5891717 := bbase (se 4 (by rfl) ⟨552348, by rfl⟩ : syracuseStep 5891717 = 1104697) (by norm_num)
theorem B1836701 : Blo 1224430 1836701 := bbase (se 3 (by rfl) ⟨344381, by rfl⟩ : syracuseStep 1836701 = 688763) (by norm_num)
theorem B1377949 : Blo 1224430 1377949 := bbase (se 3 (by rfl) ⟨258365, by rfl⟩ : syracuseStep 1377949 = 516731) (by norm_num)
theorem B1836725 : Blo 1224430 1836725 := bbase (se 5 (by rfl) ⟨86096, by rfl⟩ : syracuseStep 1836725 = 172193) (by norm_num)
theorem B1377985 : Blo 1224430 1377985 := bbase (se 2 (by rfl) ⟨516744, by rfl⟩ : syracuseStep 1377985 = 1033489) (by norm_num)
theorem B1836749 : Blo 1224430 1836749 := bbase (se 3 (by rfl) ⟨344390, by rfl⟩ : syracuseStep 1836749 = 688781) (by norm_num)
theorem B2942677 : Blo 1224430 2942677 := bbase (se 7 (by rfl) ⟨34484, by rfl⟩ : syracuseStep 2942677 = 68969) (by norm_num)
theorem B2238173 : Blo 1224430 2238173 := bbase (se 3 (by rfl) ⟨419657, by rfl⟩ : syracuseStep 2238173 = 839315) (by norm_num)
theorem B1836773 : Blo 1224430 1836773 := bbase (se 4 (by rfl) ⟨172197, by rfl⟩ : syracuseStep 1836773 = 344395) (by norm_num)
theorem B1378021 : Blo 1224430 1378021 := bbase (se 4 (by rfl) ⟨129189, by rfl⟩ : syracuseStep 1378021 = 258379) (by norm_num)
theorem B1836797 : Blo 1224430 1836797 := bbase (se 3 (by rfl) ⟨344399, by rfl⟩ : syracuseStep 1836797 = 688799) (by norm_num)
theorem B2942725 : Blo 1224430 2942725 := bbase (se 4 (by rfl) ⟨275880, by rfl⟩ : syracuseStep 2942725 = 551761) (by norm_num)
theorem B6203141 : Blo 1224430 6203141 := bbase (se 4 (by rfl) ⟨581544, by rfl⟩ : syracuseStep 6203141 = 1163089) (by norm_num)
theorem B1378057 : Blo 1224430 1378057 := bbase (se 2 (by rfl) ⟨516771, by rfl⟩ : syracuseStep 1378057 = 1033543) (by norm_num)
theorem B1492753 : Blo 1224430 1492753 := bbase (se 2 (by rfl) ⟨559782, by rfl⟩ : syracuseStep 1492753 = 1119565) (by norm_num)
theorem B1836821 : Blo 1224430 1836821 := bbase (se 6 (by rfl) ⟨43050, by rfl⟩ : syracuseStep 1836821 = 86101) (by norm_num)
theorem B1550117 : Blo 1224430 1550117 := bbase (se 4 (by rfl) ⟨145323, by rfl⟩ : syracuseStep 1550117 = 290647) (by norm_num)
theorem B1836845 : Blo 1224430 1836845 := bbase (se 3 (by rfl) ⟨344408, by rfl⟩ : syracuseStep 1836845 = 688817) (by norm_num)
theorem B1378093 : Blo 1224430 1378093 := bbase (se 3 (by rfl) ⟨258392, by rfl⟩ : syracuseStep 1378093 = 516785) (by norm_num)
theorem B1836869 : Blo 1224430 1836869 := bbase (se 4 (by rfl) ⟨172206, by rfl⟩ : syracuseStep 1836869 = 344413) (by norm_num)
theorem B1378129 : Blo 1224430 1378129 := bbase (se 2 (by rfl) ⟨516798, by rfl⟩ : syracuseStep 1378129 = 1033597) (by norm_num)
theorem B2066269 : Blo 1224430 2066269 := bbase (se 3 (by rfl) ⟨387425, by rfl⟩ : syracuseStep 2066269 = 774851) (by norm_num)
theorem B1836893 : Blo 1224430 1836893 := bbase (se 3 (by rfl) ⟨344417, by rfl⟩ : syracuseStep 1836893 = 688835) (by norm_num)
theorem B1550173 : Blo 1224430 1550173 := bbase (se 3 (by rfl) ⟨290657, by rfl⟩ : syracuseStep 1550173 = 581315) (by norm_num)
theorem B1836917 : Blo 1224430 1836917 := bbase (se 5 (by rfl) ⟨86105, by rfl⟩ : syracuseStep 1836917 = 172211) (by norm_num)
theorem B1378165 : Blo 1224430 1378165 := bbase (se 5 (by rfl) ⟨64601, by rfl⟩ : syracuseStep 1378165 = 129203) (by norm_num)
theorem B3188605 : Blo 1224430 3188605 := bbase (se 3 (by rfl) ⟨597863, by rfl⟩ : syracuseStep 3188605 = 1195727) (by norm_num)
theorem B1836941 : Blo 1224430 1836941 := bbase (se 3 (by rfl) ⟨344426, by rfl⟩ : syracuseStep 1836941 = 688853) (by norm_num)
theorem B1378201 : Blo 1224430 1378201 := bbase (se 2 (by rfl) ⟨516825, by rfl⟩ : syracuseStep 1378201 = 1033651) (by norm_num)
theorem B1836965 : Blo 1224430 1836965 := bbase (se 4 (by rfl) ⟨172215, by rfl⟩ : syracuseStep 1836965 = 344431) (by norm_num)
theorem B2066357 : Blo 1224430 2066357 := bbase (se 5 (by rfl) ⟨96860, by rfl⟩ : syracuseStep 2066357 = 193721) (by norm_num)
theorem B4655029 : Blo 1224430 4655029 := bbase (se 5 (by rfl) ⟨218204, by rfl⟩ : syracuseStep 4655029 = 436409) (by norm_num)
theorem B1836989 : Blo 1224430 1836989 := bbase (se 3 (by rfl) ⟨344435, by rfl⟩ : syracuseStep 1836989 = 688871) (by norm_num)
theorem B1550269 : Blo 1224430 1550269 := bbase (se 3 (by rfl) ⟨290675, by rfl⟩ : syracuseStep 1550269 = 581351) (by norm_num)
theorem B1378237 : Blo 1224430 1378237 := bbase (se 3 (by rfl) ⟨258419, by rfl⟩ : syracuseStep 1378237 = 516839) (by norm_num)
theorem B2516933 : Blo 1224430 2516933 := bbase (se 4 (by rfl) ⟨235962, by rfl⟩ : syracuseStep 2516933 = 471925) (by norm_num)
theorem B1837013 : Blo 1224430 1837013 := bbase (se 7 (by rfl) ⟨21527, by rfl⟩ : syracuseStep 1837013 = 43055) (by norm_num)
theorem B16779221 : Blo 1224430 16779221 := bbase (se 7 (by rfl) ⟨196631, by rfl⟩ : syracuseStep 16779221 = 393263) (by norm_num)
theorem B1378273 : Blo 1224430 1378273 := bbase (se 2 (by rfl) ⟨516852, by rfl⟩ : syracuseStep 1378273 = 1033705) (by norm_num)
theorem B1837037 : Blo 1224430 1837037 := bbase (se 3 (by rfl) ⟨344444, by rfl⟩ : syracuseStep 1837037 = 688889) (by norm_num)
theorem B1837061 : Blo 1224430 1837061 := bbase (se 4 (by rfl) ⟨172224, by rfl⟩ : syracuseStep 1837061 = 344449) (by norm_num)
theorem B1378309 : Blo 1224430 1378309 := bbase (se 4 (by rfl) ⟨129216, by rfl⟩ : syracuseStep 1378309 = 258433) (by norm_num)
theorem B5236757 : Blo 1224430 5236757 := bbase (se 6 (by rfl) ⟨122736, by rfl⟩ : syracuseStep 5236757 = 245473) (by norm_num)
theorem B1837085 : Blo 1224430 1837085 := bbase (se 3 (by rfl) ⟨344453, by rfl⟩ : syracuseStep 1837085 = 688907) (by norm_num)
theorem B4139045 : Blo 1224430 4139045 := bbase (se 4 (by rfl) ⟨388035, by rfl⟩ : syracuseStep 4139045 = 776071) (by norm_num)
theorem B1378345 : Blo 1224430 1378345 := bbase (se 2 (by rfl) ⟨516879, by rfl⟩ : syracuseStep 1378345 = 1033759) (by norm_num)
theorem B2066485 : Blo 1224430 2066485 := bbase (se 5 (by rfl) ⟨96866, by rfl⟩ : syracuseStep 2066485 = 193733) (by norm_num)
theorem B1837109 : Blo 1224430 1837109 := bbase (se 5 (by rfl) ⟨86114, by rfl⟩ : syracuseStep 1837109 = 172229) (by norm_num)
theorem B1837133 : Blo 1224430 1837133 := bbase (se 3 (by rfl) ⟨344462, by rfl⟩ : syracuseStep 1837133 = 688925) (by norm_num)
theorem B1378381 : Blo 1224430 1378381 := bbase (se 3 (by rfl) ⟨258446, by rfl⟩ : syracuseStep 1378381 = 516893) (by norm_num)
theorem B1837157 : Blo 1224430 1837157 := bbase (se 4 (by rfl) ⟨172233, by rfl⟩ : syracuseStep 1837157 = 344467) (by norm_num)
theorem B1550441 : Blo 1224430 1550441 := bbase (se 2 (by rfl) ⟨581415, by rfl⟩ : syracuseStep 1550441 = 1162831) (by norm_num)
theorem B1378417 : Blo 1224430 1378417 := bbase (se 2 (by rfl) ⟨516906, by rfl⟩ : syracuseStep 1378417 = 1033813) (by norm_num)
theorem B12585077 : Blo 1224430 12585077 := bbase (se 5 (by rfl) ⟨589925, by rfl⟩ : syracuseStep 12585077 = 1179851) (by norm_num)
theorem B1837181 : Blo 1224430 1837181 := bbase (se 3 (by rfl) ⟨344471, by rfl⟩ : syracuseStep 1837181 = 688943) (by norm_num)
theorem B2066573 : Blo 1224430 2066573 := bbase (se 3 (by rfl) ⟨387482, by rfl⟩ : syracuseStep 2066573 = 774965) (by norm_num)
theorem B1837205 : Blo 1224430 1837205 := bbase (se 6 (by rfl) ⟨43059, by rfl⟩ : syracuseStep 1837205 = 86119) (by norm_num)
theorem B1378453 : Blo 1224430 1378453 := bbase (se 6 (by rfl) ⟨32307, by rfl⟩ : syracuseStep 1378453 = 64615) (by norm_num)
theorem B1550497 : Blo 1224430 1550497 := bbase (se 2 (by rfl) ⟨581436, by rfl⟩ : syracuseStep 1550497 = 1162873) (by norm_num)
theorem B1837229 : Blo 1224430 1837229 := bbase (se 3 (by rfl) ⟨344480, by rfl⟩ : syracuseStep 1837229 = 688961) (by norm_num)
theorem B1378489 : Blo 1224430 1378489 := bbase (se 2 (by rfl) ⟨516933, by rfl⟩ : syracuseStep 1378489 = 1033867) (by norm_num)
theorem B1837253 : Blo 1224430 1837253 := bbase (se 4 (by rfl) ⟨172242, by rfl⟩ : syracuseStep 1837253 = 344485) (by norm_num)
theorem B1837277 : Blo 1224430 1837277 := bbase (se 3 (by rfl) ⟨344489, by rfl⟩ : syracuseStep 1837277 = 688979) (by norm_num)
theorem B1378525 : Blo 1224430 1378525 := bbase (se 3 (by rfl) ⟨258473, by rfl⟩ : syracuseStep 1378525 = 516947) (by norm_num)
theorem B4655333 : Blo 1224430 4655333 := bbase (se 4 (by rfl) ⟨436437, by rfl⟩ : syracuseStep 4655333 = 872875) (by norm_num)
theorem B1837301 : Blo 1224430 1837301 := bbase (se 5 (by rfl) ⟨86123, by rfl⟩ : syracuseStep 1837301 = 172247) (by norm_num)
theorem B1550593 : Blo 1224430 1550593 := bbase (se 2 (by rfl) ⟨581472, by rfl⟩ : syracuseStep 1550593 = 1162945) (by norm_num)
theorem B1378561 : Blo 1224430 1378561 := bbase (se 2 (by rfl) ⟨516960, by rfl⟩ : syracuseStep 1378561 = 1033921) (by norm_num)
theorem B2066701 : Blo 1224430 2066701 := bbase (se 3 (by rfl) ⟨387506, by rfl⟩ : syracuseStep 2066701 = 775013) (by norm_num)
theorem B1837325 : Blo 1224430 1837325 := bbase (se 3 (by rfl) ⟨344498, by rfl⟩ : syracuseStep 1837325 = 688997) (by norm_num)
theorem B1837349 : Blo 1224430 1837349 := bbase (se 4 (by rfl) ⟨172251, by rfl⟩ : syracuseStep 1837349 = 344503) (by norm_num)
theorem B1378597 : Blo 1224430 1378597 := bbase (se 4 (by rfl) ⟨129243, by rfl⟩ : syracuseStep 1378597 = 258487) (by norm_num)
theorem B5237045 : Blo 1224430 5237045 := bbase (se 5 (by rfl) ⟨245486, by rfl⟩ : syracuseStep 5237045 = 490973) (by norm_num)
theorem B1837373 : Blo 1224430 1837373 := bbase (se 3 (by rfl) ⟨344507, by rfl⟩ : syracuseStep 1837373 = 689015) (by norm_num)
theorem B1378633 : Blo 1224430 1378633 := bbase (se 2 (by rfl) ⟨516987, by rfl⟩ : syracuseStep 1378633 = 1033975) (by norm_num)
theorem B1837397 : Blo 1224430 1837397 := bbase (se 10 (by rfl) ⟨2691, by rfl⟩ : syracuseStep 1837397 = 5383) (by norm_num)
theorem B7072085 : Blo 1224430 7072085 := bbase (se 10 (by rfl) ⟨10359, by rfl⟩ : syracuseStep 7072085 = 20719) (by norm_num)
theorem B2615645 : Blo 1224430 2615645 := bbase (se 3 (by rfl) ⟨490433, by rfl⟩ : syracuseStep 2615645 = 980867) (by norm_num)
theorem B2066789 : Blo 1224430 2066789 := bbase (se 4 (by rfl) ⟨193761, by rfl⟩ : syracuseStep 2066789 = 387523) (by norm_num)
theorem B1837421 : Blo 1224430 1837421 := bbase (se 3 (by rfl) ⟨344516, by rfl⟩ : syracuseStep 1837421 = 689033) (by norm_num)
theorem B2943341 : Blo 1224430 2943341 := bbase (se 3 (by rfl) ⟨551876, by rfl⟩ : syracuseStep 2943341 = 1103753) (by norm_num)
theorem B1378669 : Blo 1224430 1378669 := bbase (se 3 (by rfl) ⟨258500, by rfl⟩ : syracuseStep 1378669 = 517001) (by norm_num)
theorem B1837445 : Blo 1224430 1837445 := bbase (se 4 (by rfl) ⟨172260, by rfl⟩ : syracuseStep 1837445 = 344521) (by norm_num)
theorem B3492229 : Blo 1224430 3492229 := bbase (se 4 (by rfl) ⟨327396, by rfl⟩ : syracuseStep 3492229 = 654793) (by norm_num)
theorem B1378705 : Blo 1224430 1378705 := bbase (se 2 (by rfl) ⟨517014, by rfl⟩ : syracuseStep 1378705 = 1034029) (by norm_num)
theorem B1837469 : Blo 1224430 1837469 := bbase (se 3 (by rfl) ⟨344525, by rfl⟩ : syracuseStep 1837469 = 689051) (by norm_num)
theorem B2754989 : Blo 1224430 2754989 := bbase (se 3 (by rfl) ⟨516560, by rfl⟩ : syracuseStep 2754989 = 1033121) (by norm_num)
theorem B1550765 : Blo 1224430 1550765 := bbase (se 3 (by rfl) ⟨290768, by rfl⟩ : syracuseStep 1550765 = 581537) (by norm_num)
theorem B1837493 : Blo 1224430 1837493 := bbase (se 5 (by rfl) ⟨86132, by rfl⟩ : syracuseStep 1837493 = 172265) (by norm_num)
theorem B1378741 : Blo 1224430 1378741 := bbase (se 5 (by rfl) ⟨64628, by rfl⟩ : syracuseStep 1378741 = 129257) (by norm_num)
theorem B1837517 : Blo 1224430 1837517 := bbase (se 3 (by rfl) ⟨344534, by rfl⟩ : syracuseStep 1837517 = 689069) (by norm_num)
theorem B10463701 : Blo 1224430 10463701 := bbase (se 7 (by rfl) ⟨122621, by rfl⟩ : syracuseStep 10463701 = 245243) (by norm_num)
theorem B1378777 : Blo 1224430 1378777 := bbase (se 2 (by rfl) ⟨517041, by rfl⟩ : syracuseStep 1378777 = 1034083) (by norm_num)
theorem B2066917 : Blo 1224430 2066917 := bbase (se 4 (by rfl) ⟨193773, by rfl⟩ : syracuseStep 2066917 = 387547) (by norm_num)
theorem B1837541 : Blo 1224430 1837541 := bbase (se 4 (by rfl) ⟨172269, by rfl⟩ : syracuseStep 1837541 = 344539) (by norm_num)
theorem B1550821 : Blo 1224430 1550821 := bbase (se 4 (by rfl) ⟨145389, by rfl⟩ : syracuseStep 1550821 = 290779) (by norm_num)
theorem B2615789 : Blo 1224430 2615789 := bbase (se 3 (by rfl) ⟨490460, by rfl⟩ : syracuseStep 2615789 = 980921) (by norm_num)
theorem B2755061 : Blo 1224430 2755061 := bbase (se 5 (by rfl) ⟨129143, by rfl⟩ : syracuseStep 2755061 = 258287) (by norm_num)
theorem B1837565 : Blo 1224430 1837565 := bbase (se 3 (by rfl) ⟨344543, by rfl⟩ : syracuseStep 1837565 = 689087) (by norm_num)
theorem B1378813 : Blo 1224430 1378813 := bbase (se 3 (by rfl) ⟨258527, by rfl⟩ : syracuseStep 1378813 = 517055) (by norm_num)
theorem B2796029 : Blo 1224430 2796029 := bbase (se 3 (by rfl) ⟨524255, by rfl⟩ : syracuseStep 2796029 = 1048511) (by norm_num)
theorem B1837589 : Blo 1224430 1837589 := bbase (se 6 (by rfl) ⟨43068, by rfl⟩ : syracuseStep 1837589 = 86137) (by norm_num)
theorem B1378849 : Blo 1224430 1378849 := bbase (se 2 (by rfl) ⟨517068, by rfl⟩ : syracuseStep 1378849 = 1034137) (by norm_num)
theorem B2484773 : Blo 1224430 2484773 := bbase (se 4 (by rfl) ⟨232947, by rfl⟩ : syracuseStep 2484773 = 465895) (by norm_num)
theorem B3492389 : Blo 1224430 3492389 := bbase (se 4 (by rfl) ⟨327411, by rfl⟩ : syracuseStep 3492389 = 654823) (by norm_num)
theorem B1837613 : Blo 1224430 1837613 := bbase (se 3 (by rfl) ⟨344552, by rfl⟩ : syracuseStep 1837613 = 689105) (by norm_num)
theorem B2755133 : Blo 1224430 2755133 := bbase (se 3 (by rfl) ⟨516587, by rfl⟩ : syracuseStep 2755133 = 1033175) (by norm_num)
theorem B2067005 : Blo 1224430 2067005 := bbase (se 3 (by rfl) ⟨387563, by rfl⟩ : syracuseStep 2067005 = 775127) (by norm_num)
theorem B1837637 : Blo 1224430 1837637 := bbase (se 4 (by rfl) ⟨172278, by rfl⟩ : syracuseStep 1837637 = 344557) (by norm_num)
theorem B1550917 : Blo 1224430 1550917 := bbase (se 4 (by rfl) ⟨145398, by rfl⟩ : syracuseStep 1550917 = 290797) (by norm_num)
theorem B1378885 : Blo 1224430 1378885 := bbase (se 4 (by rfl) ⟨129270, by rfl⟩ : syracuseStep 1378885 = 258541) (by norm_num)
theorem B1837661 : Blo 1224430 1837661 := bbase (se 3 (by rfl) ⟨344561, by rfl⟩ : syracuseStep 1837661 = 689123) (by norm_num)
theorem B1378921 : Blo 1224430 1378921 := bbase (se 2 (by rfl) ⟨517095, by rfl⟩ : syracuseStep 1378921 = 1034191) (by norm_num)
theorem B1837685 : Blo 1224430 1837685 := bbase (se 5 (by rfl) ⟨86141, by rfl⟩ : syracuseStep 1837685 = 172283) (by norm_num)
theorem B2755205 : Blo 1224430 2755205 := bbase (se 4 (by rfl) ⟨258300, by rfl⟩ : syracuseStep 2755205 = 516601) (by norm_num)
theorem B1837709 : Blo 1224430 1837709 := bbase (se 3 (by rfl) ⟨344570, by rfl⟩ : syracuseStep 1837709 = 689141) (by norm_num)
theorem B1378957 : Blo 1224430 1378957 := bbase (se 3 (by rfl) ⟨258554, by rfl⟩ : syracuseStep 1378957 = 517109) (by norm_num)
theorem B1837733 : Blo 1224430 1837733 := bbase (se 4 (by rfl) ⟨172287, by rfl⟩ : syracuseStep 1837733 = 344575) (by norm_num)
theorem B1378993 : Blo 1224430 1378993 := bbase (se 2 (by rfl) ⟨517122, by rfl⟩ : syracuseStep 1378993 = 1034245) (by norm_num)
theorem B2067133 : Blo 1224430 2067133 := bbase (se 3 (by rfl) ⟨387587, by rfl⟩ : syracuseStep 2067133 = 775175) (by norm_num)
theorem B1837757 : Blo 1224430 1837757 := bbase (se 3 (by rfl) ⟨344579, by rfl⟩ : syracuseStep 1837757 = 689159) (by norm_num)
theorem B2943685 : Blo 1224430 2943685 := bbase (se 4 (by rfl) ⟨275970, by rfl⟩ : syracuseStep 2943685 = 551941) (by norm_num)
theorem B2755277 : Blo 1224430 2755277 := bbase (se 3 (by rfl) ⟨516614, by rfl⟩ : syracuseStep 2755277 = 1033229) (by norm_num)
theorem B1837781 : Blo 1224430 1837781 := bbase (se 7 (by rfl) ⟨21536, by rfl⟩ : syracuseStep 1837781 = 43073) (by norm_num)
theorem B1379029 : Blo 1224430 1379029 := bbase (se 7 (by rfl) ⟨16160, by rfl⟩ : syracuseStep 1379029 = 32321) (by norm_num)
theorem B1837805 : Blo 1224430 1837805 := bbase (se 3 (by rfl) ⟨344588, by rfl⟩ : syracuseStep 1837805 = 689177) (by norm_num)
theorem B1551089 : Blo 1224430 1551089 := bbase (se 2 (by rfl) ⟨581658, by rfl⟩ : syracuseStep 1551089 = 1163317) (by norm_num)
theorem B1379065 : Blo 1224430 1379065 := bbase (se 2 (by rfl) ⟨517149, by rfl⟩ : syracuseStep 1379065 = 1034299) (by norm_num)
theorem B1837829 : Blo 1224430 1837829 := bbase (se 4 (by rfl) ⟨172296, by rfl⟩ : syracuseStep 1837829 = 344593) (by norm_num)
theorem B2755349 : Blo 1224430 2755349 := bbase (se 6 (by rfl) ⟨64578, by rfl⟩ : syracuseStep 2755349 = 129157) (by norm_num)
theorem B2067221 : Blo 1224430 2067221 := bbase (se 6 (by rfl) ⟨48450, by rfl⟩ : syracuseStep 2067221 = 96901) (by norm_num)
theorem B1837853 : Blo 1224430 1837853 := bbase (se 3 (by rfl) ⟨344597, by rfl⟩ : syracuseStep 1837853 = 689195) (by norm_num)
theorem B1379101 : Blo 1224430 1379101 := bbase (se 3 (by rfl) ⟨258581, by rfl⟩ : syracuseStep 1379101 = 517163) (by norm_num)
theorem B1551145 : Blo 1224430 1551145 := bbase (se 2 (by rfl) ⟨581679, by rfl⟩ : syracuseStep 1551145 = 1163359) (by norm_num)
theorem B1837877 : Blo 1224430 1837877 := bbase (se 5 (by rfl) ⟨86150, by rfl⟩ : syracuseStep 1837877 = 172301) (by norm_num)
theorem B1379137 : Blo 1224430 1379137 := bbase (se 2 (by rfl) ⟨517176, by rfl⟩ : syracuseStep 1379137 = 1034353) (by norm_num)
theorem B1837901 : Blo 1224430 1837901 := bbase (se 3 (by rfl) ⟨344606, by rfl⟩ : syracuseStep 1837901 = 689213) (by norm_num)
theorem B5884757 : Blo 1224430 5884757 := bbase (se 9 (by rfl) ⟨17240, by rfl⟩ : syracuseStep 5884757 = 34481) (by norm_num)
theorem B3099485 : Blo 1224430 3099485 := bbase (se 3 (by rfl) ⟨581153, by rfl⟩ : syracuseStep 3099485 = 1162307) (by norm_num)
theorem B2755421 : Blo 1224430 2755421 := bbase (se 3 (by rfl) ⟨516641, by rfl⟩ : syracuseStep 2755421 = 1033283) (by norm_num)
theorem B1837925 : Blo 1224430 1837925 := bbase (se 4 (by rfl) ⟨172305, by rfl⟩ : syracuseStep 1837925 = 344611) (by norm_num)
theorem B1379173 : Blo 1224430 1379173 := bbase (se 4 (by rfl) ⟨129297, by rfl⟩ : syracuseStep 1379173 = 258595) (by norm_num)
theorem B1837949 : Blo 1224430 1837949 := bbase (se 3 (by rfl) ⟨344615, by rfl⟩ : syracuseStep 1837949 = 689231) (by norm_num)
theorem B1551241 : Blo 1224430 1551241 := bbase (se 2 (by rfl) ⟨581715, by rfl⟩ : syracuseStep 1551241 = 1163431) (by norm_num)
theorem B1379209 : Blo 1224430 1379209 := bbase (se 2 (by rfl) ⟨517203, by rfl⟩ : syracuseStep 1379209 = 1034407) (by norm_num)
theorem B15944597 : Blo 1224430 15944597 := bbase (se 6 (by rfl) ⟨373701, by rfl⟩ : syracuseStep 15944597 = 747403) (by norm_num)
theorem B2067349 : Blo 1224430 2067349 := bbase (se 6 (by rfl) ⟨48453, by rfl⟩ : syracuseStep 2067349 = 96907) (by norm_num)
theorem B1837973 : Blo 1224430 1837973 := bbase (se 6 (by rfl) ⟨43077, by rfl⟩ : syracuseStep 1837973 = 86155) (by norm_num)
theorem B2755493 : Blo 1224430 2755493 := bbase (se 4 (by rfl) ⟨258327, by rfl⟩ : syracuseStep 2755493 = 516655) (by norm_num)
theorem B2943917 : Blo 1224430 2943917 := bbase (se 3 (by rfl) ⟨551984, by rfl⟩ : syracuseStep 2943917 = 1103969) (by norm_num)
theorem B1837997 : Blo 1224430 1837997 := bbase (se 3 (by rfl) ⟨344624, by rfl⟩ : syracuseStep 1837997 = 689249) (by norm_num)
theorem B1379245 : Blo 1224430 1379245 := bbase (se 3 (by rfl) ⟨258608, by rfl⟩ : syracuseStep 1379245 = 517217) (by norm_num)
theorem B1838021 : Blo 1224430 1838021 := bbase (se 4 (by rfl) ⟨172314, by rfl⟩ : syracuseStep 1838021 = 344629) (by norm_num)
theorem B1379281 : Blo 1224430 1379281 := bbase (se 2 (by rfl) ⟨517230, by rfl⟩ : syracuseStep 1379281 = 1034461) (by norm_num)
theorem B1838045 : Blo 1224430 1838045 := bbase (se 3 (by rfl) ⟨344633, by rfl⟩ : syracuseStep 1838045 = 689267) (by norm_num)
theorem B2755565 : Blo 1224430 2755565 := bbase (se 3 (by rfl) ⟨516668, by rfl⟩ : syracuseStep 2755565 = 1033337) (by norm_num)
theorem B2067437 : Blo 1224430 2067437 := bbase (se 3 (by rfl) ⟨387644, by rfl⟩ : syracuseStep 2067437 = 775289) (by norm_num)
theorem B1838069 : Blo 1224430 1838069 := bbase (se 5 (by rfl) ⟨86159, by rfl⟩ : syracuseStep 1838069 = 172319) (by norm_num)
theorem B1379317 : Blo 1224430 1379317 := bbase (se 5 (by rfl) ⟨64655, by rfl⟩ : syracuseStep 1379317 = 129311) (by norm_num)
theorem B1838093 : Blo 1224430 1838093 := bbase (se 3 (by rfl) ⟨344642, by rfl⟩ : syracuseStep 1838093 = 689285) (by norm_num)
theorem B6204437 : Blo 1224430 6204437 := bbase (se 6 (by rfl) ⟨145416, by rfl⟩ : syracuseStep 6204437 = 290833) (by norm_num)
theorem B1379353 : Blo 1224430 1379353 := bbase (se 2 (by rfl) ⟨517257, by rfl⟩ : syracuseStep 1379353 = 1034515) (by norm_num)
theorem B1838117 : Blo 1224430 1838117 := bbase (se 4 (by rfl) ⟨172323, by rfl⟩ : syracuseStep 1838117 = 344647) (by norm_num)
theorem B5237797 : Blo 1224430 5237797 := bbase (se 4 (by rfl) ⟨491043, by rfl⟩ : syracuseStep 5237797 = 982087) (by norm_num)
theorem B2755637 : Blo 1224430 2755637 := bbase (se 5 (by rfl) ⟨129170, by rfl⟩ : syracuseStep 2755637 = 258341) (by norm_num)
theorem B1551413 : Blo 1224430 1551413 := bbase (se 5 (by rfl) ⟨72722, by rfl⟩ : syracuseStep 1551413 = 145445) (by norm_num)
theorem B1838141 : Blo 1224430 1838141 := bbase (se 3 (by rfl) ⟨344651, by rfl⟩ : syracuseStep 1838141 = 689303) (by norm_num)
theorem B1379389 : Blo 1224430 1379389 := bbase (se 3 (by rfl) ⟨258635, by rfl⟩ : syracuseStep 1379389 = 517271) (by norm_num)
theorem B1838165 : Blo 1224430 1838165 := bbase (se 8 (by rfl) ⟨10770, by rfl⟩ : syracuseStep 1838165 = 21541) (by norm_num)
theorem B1379425 : Blo 1224430 1379425 := bbase (se 2 (by rfl) ⟨517284, by rfl⟩ : syracuseStep 1379425 = 1034569) (by norm_num)
theorem B2067565 : Blo 1224430 2067565 := bbase (se 3 (by rfl) ⟨387668, by rfl⟩ : syracuseStep 2067565 = 775337) (by norm_num)
theorem B2944109 : Blo 1224430 2944109 := bbase (se 3 (by rfl) ⟨552020, by rfl⟩ : syracuseStep 2944109 = 1104041) (by norm_num)
theorem B1838189 : Blo 1224430 1838189 := bbase (se 3 (by rfl) ⟨344660, by rfl⟩ : syracuseStep 1838189 = 689321) (by norm_num)
theorem B1551469 : Blo 1224430 1551469 := bbase (se 3 (by rfl) ⟨290900, by rfl⟩ : syracuseStep 1551469 = 581801) (by norm_num)
theorem B2755709 : Blo 1224430 2755709 := bbase (se 3 (by rfl) ⟨516695, by rfl⟩ : syracuseStep 2755709 = 1033391) (by norm_num)
theorem B1838213 : Blo 1224430 1838213 := bbase (se 4 (by rfl) ⟨172332, by rfl⟩ : syracuseStep 1838213 = 344665) (by norm_num)
theorem B1379461 : Blo 1224430 1379461 := bbase (se 4 (by rfl) ⟨129324, by rfl⟩ : syracuseStep 1379461 = 258649) (by norm_num)
theorem B1838237 : Blo 1224430 1838237 := bbase (se 3 (by rfl) ⟨344669, by rfl⟩ : syracuseStep 1838237 = 689339) (by norm_num)
theorem B1379497 : Blo 1224430 1379497 := bbase (se 2 (by rfl) ⟨517311, by rfl⟩ : syracuseStep 1379497 = 1034623) (by norm_num)
theorem B3099829 : Blo 1224430 3099829 := bbase (se 5 (by rfl) ⟨145304, by rfl⟩ : syracuseStep 3099829 = 290609) (by norm_num)
theorem B1838261 : Blo 1224430 1838261 := bbase (se 5 (by rfl) ⟨86168, by rfl⟩ : syracuseStep 1838261 = 172337) (by norm_num)
theorem B2755781 : Blo 1224430 2755781 := bbase (se 4 (by rfl) ⟨258354, by rfl⟩ : syracuseStep 2755781 = 516709) (by norm_num)
theorem B2067653 : Blo 1224430 2067653 := bbase (se 4 (by rfl) ⟨193842, by rfl⟩ : syracuseStep 2067653 = 387685) (by norm_num)
theorem B1838285 : Blo 1224430 1838285 := bbase (se 3 (by rfl) ⟨344678, by rfl⟩ : syracuseStep 1838285 = 689357) (by norm_num)
theorem B1551565 : Blo 1224430 1551565 := bbase (se 3 (by rfl) ⟨290918, by rfl⟩ : syracuseStep 1551565 = 581837) (by norm_num)
theorem B1379533 : Blo 1224430 1379533 := bbase (se 3 (by rfl) ⟨258662, by rfl⟩ : syracuseStep 1379533 = 517325) (by norm_num)
theorem B2616533 : Blo 1224430 2616533 := bbase (se 7 (by rfl) ⟨30662, by rfl⟩ : syracuseStep 2616533 = 61325) (by norm_num)
theorem B1838309 : Blo 1224430 1838309 := bbase (se 4 (by rfl) ⟨172341, by rfl⟩ : syracuseStep 1838309 = 344683) (by norm_num)
theorem B1379569 : Blo 1224430 1379569 := bbase (se 2 (by rfl) ⟨517338, by rfl⟩ : syracuseStep 1379569 = 1034677) (by norm_num)
theorem B1838333 : Blo 1224430 1838333 := bbase (se 3 (by rfl) ⟨344687, by rfl⟩ : syracuseStep 1838333 = 689375) (by norm_num)
theorem B2755853 : Blo 1224430 2755853 := bbase (se 3 (by rfl) ⟨516722, by rfl⟩ : syracuseStep 2755853 = 1033445) (by norm_num)
theorem B1838357 : Blo 1224430 1838357 := bbase (se 6 (by rfl) ⟨43086, by rfl⟩ : syracuseStep 1838357 = 86173) (by norm_num)
theorem B1379605 : Blo 1224430 1379605 := bbase (se 6 (by rfl) ⟨32334, by rfl⟩ : syracuseStep 1379605 = 64669) (by norm_num)
theorem B3099941 : Blo 1224430 3099941 := bbase (se 4 (by rfl) ⟨290619, by rfl⟩ : syracuseStep 3099941 = 581239) (by norm_num)
theorem B3149093 : Blo 1224430 3149093 := bbase (se 4 (by rfl) ⟨295227, by rfl⟩ : syracuseStep 3149093 = 590455) (by norm_num)
theorem B1838381 : Blo 1224430 1838381 := bbase (se 3 (by rfl) ⟨344696, by rfl⟩ : syracuseStep 1838381 = 689393) (by norm_num)
theorem B1379641 : Blo 1224430 1379641 := bbase (se 2 (by rfl) ⟨517365, by rfl⟩ : syracuseStep 1379641 = 1034731) (by norm_num)
theorem B2067781 : Blo 1224430 2067781 := bbase (se 4 (by rfl) ⟨193854, by rfl⟩ : syracuseStep 2067781 = 387709) (by norm_num)
theorem B1838405 : Blo 1224430 1838405 := bbase (se 4 (by rfl) ⟨172350, by rfl⟩ : syracuseStep 1838405 = 344701) (by norm_num)
theorem B5107013 : Blo 1224430 5107013 := bbase (se 4 (by rfl) ⟨478782, by rfl⟩ : syracuseStep 5107013 = 957565) (by norm_num)
theorem B22646101 : Blo 1224430 22646101 := bbase (se 11 (by rfl) ⟨16586, by rfl⟩ : syracuseStep 22646101 = 33173) (by norm_num)
theorem B2755925 : Blo 1224430 2755925 := bbase (se 11 (by rfl) ⟨2018, by rfl⟩ : syracuseStep 2755925 = 4037) (by norm_num)
theorem B1838429 : Blo 1224430 1838429 := bbase (se 3 (by rfl) ⟨344705, by rfl⟩ : syracuseStep 1838429 = 689411) (by norm_num)
theorem B1379677 : Blo 1224430 1379677 := bbase (se 3 (by rfl) ⟨258689, by rfl⟩ : syracuseStep 1379677 = 517379) (by norm_num)
theorem B1838453 : Blo 1224430 1838453 := bbase (se 5 (by rfl) ⟨86177, by rfl⟩ : syracuseStep 1838453 = 172355) (by norm_num)
theorem B1551737 : Blo 1224430 1551737 := bbase (se 2 (by rfl) ⟨581901, by rfl⟩ : syracuseStep 1551737 = 1163803) (by norm_num)
theorem B1379713 : Blo 1224430 1379713 := bbase (se 2 (by rfl) ⟨517392, by rfl⟩ : syracuseStep 1379713 = 1034785) (by norm_num)
theorem B2944397 : Blo 1224430 2944397 := bbase (se 3 (by rfl) ⟨552074, by rfl⟩ : syracuseStep 2944397 = 1104149) (by norm_num)
theorem B1838477 : Blo 1224430 1838477 := bbase (se 3 (by rfl) ⟨344714, by rfl⟩ : syracuseStep 1838477 = 689429) (by norm_num)
theorem B2755997 : Blo 1224430 2755997 := bbase (se 3 (by rfl) ⟨516749, by rfl⟩ : syracuseStep 2755997 = 1033499) (by norm_num)
theorem B2067869 : Blo 1224430 2067869 := bbase (se 3 (by rfl) ⟨387725, by rfl⟩ : syracuseStep 2067869 = 775451) (by norm_num)
theorem B1961381 : Blo 1224430 1961381 := bbase (se 4 (by rfl) ⟨183879, by rfl⟩ : syracuseStep 1961381 = 367759) (by norm_num)
theorem B1838501 : Blo 1224430 1838501 := bbase (se 4 (by rfl) ⟨172359, by rfl⟩ : syracuseStep 1838501 = 344719) (by norm_num)
theorem B1551793 : Blo 1224430 1551793 := bbase (se 2 (by rfl) ⟨581922, by rfl⟩ : syracuseStep 1551793 = 1163845) (by norm_num)
theorem B1838525 : Blo 1224430 1838525 := bbase (se 3 (by rfl) ⟨344723, by rfl⟩ : syracuseStep 1838525 = 689447) (by norm_num)
theorem B13954517 : Blo 1224430 13954517 := bbase (se 7 (by rfl) ⟨163529, by rfl⟩ : syracuseStep 13954517 = 327059) (by norm_num)
theorem B1838549 : Blo 1224430 1838549 := bbase (se 7 (by rfl) ⟨21545, by rfl⟩ : syracuseStep 1838549 = 43091) (by norm_num)
theorem B3100133 : Blo 1224430 3100133 := bbase (se 4 (by rfl) ⟨290637, by rfl⟩ : syracuseStep 3100133 = 581275) (by norm_num)
theorem B2756069 : Blo 1224430 2756069 := bbase (se 4 (by rfl) ⟨258381, by rfl⟩ : syracuseStep 2756069 = 516763) (by norm_num)
theorem B1838573 : Blo 1224430 1838573 := bbase (se 3 (by rfl) ⟨344732, by rfl⟩ : syracuseStep 1838573 = 689465) (by norm_num)
theorem B1838597 : Blo 1224430 1838597 := bbase (se 4 (by rfl) ⟨172368, by rfl⟩ : syracuseStep 1838597 = 344737) (by norm_num)
theorem B1551889 : Blo 1224430 1551889 := bbase (se 2 (by rfl) ⟨581958, by rfl⟩ : syracuseStep 1551889 = 1163917) (by norm_num)
theorem B2067997 : Blo 1224430 2067997 := bbase (se 3 (by rfl) ⟨387749, by rfl⟩ : syracuseStep 2067997 = 775499) (by norm_num)
theorem B1838621 : Blo 1224430 1838621 := bbase (se 3 (by rfl) ⟨344741, by rfl⟩ : syracuseStep 1838621 = 689483) (by norm_num)
theorem B1961509 : Blo 1224430 1961509 := bbase (se 4 (by rfl) ⟨183891, by rfl⟩ : syracuseStep 1961509 = 367783) (by norm_num)
theorem B2756141 : Blo 1224430 2756141 := bbase (se 3 (by rfl) ⟨516776, by rfl⟩ : syracuseStep 2756141 = 1033553) (by norm_num)
theorem B1838645 : Blo 1224430 1838645 := bbase (se 5 (by rfl) ⟨86186, by rfl⟩ : syracuseStep 1838645 = 172373) (by norm_num)
theorem B1838669 : Blo 1224430 1838669 := bbase (se 3 (by rfl) ⟨344750, by rfl⟩ : syracuseStep 1838669 = 689501) (by norm_num)
theorem B2207333 : Blo 1224430 2207333 := bbase (se 4 (by rfl) ⟨206937, by rfl⟩ : syracuseStep 2207333 = 413875) (by norm_num)
theorem B1838693 : Blo 1224430 1838693 := bbase (se 4 (by rfl) ⟨172377, by rfl⟩ : syracuseStep 1838693 = 344755) (by norm_num)
theorem B2756213 : Blo 1224430 2756213 := bbase (se 5 (by rfl) ⟨129197, by rfl⟩ : syracuseStep 2756213 = 258395) (by norm_num)
theorem B2068085 : Blo 1224430 2068085 := bbase (se 5 (by rfl) ⟨96941, by rfl⟩ : syracuseStep 2068085 = 193883) (by norm_num)
theorem B1838717 : Blo 1224430 1838717 := bbase (se 3 (by rfl) ⟨344759, by rfl⟩ : syracuseStep 1838717 = 689519) (by norm_num)
theorem B1838741 : Blo 1224430 1838741 := bbase (se 6 (by rfl) ⟨43095, by rfl⟩ : syracuseStep 1838741 = 86191) (by norm_num)
theorem B2240165 : Blo 1224430 2240165 := bbase (se 4 (by rfl) ⟨210015, by rfl⟩ : syracuseStep 2240165 = 420031) (by norm_num)
theorem B1838765 : Blo 1224430 1838765 := bbase (se 3 (by rfl) ⟨344768, by rfl⟩ : syracuseStep 1838765 = 689537) (by norm_num)
theorem B2756285 : Blo 1224430 2756285 := bbase (se 3 (by rfl) ⟨516803, by rfl⟩ : syracuseStep 2756285 = 1033607) (by norm_num)
theorem B1552061 : Blo 1224430 1552061 := bbase (se 3 (by rfl) ⟨291011, by rfl⟩ : syracuseStep 1552061 = 582023) (by norm_num)
theorem B1838789 : Blo 1224430 1838789 := bbase (se 4 (by rfl) ⟨172386, by rfl⟩ : syracuseStep 1838789 = 344773) (by norm_num)
theorem B4132565 : Blo 1224430 4132565 := bbase (se 7 (by rfl) ⟨48428, by rfl⟩ : syracuseStep 4132565 = 96857) (by norm_num)
theorem B1838813 : Blo 1224430 1838813 := bbase (se 3 (by rfl) ⟨344777, by rfl⟩ : syracuseStep 1838813 = 689555) (by norm_num)
theorem B2068213 : Blo 1224430 2068213 := bbase (se 5 (by rfl) ⟨96947, by rfl⟩ : syracuseStep 2068213 = 193895) (by norm_num)
theorem B1838837 : Blo 1224430 1838837 := bbase (se 5 (by rfl) ⟨86195, by rfl⟩ : syracuseStep 1838837 = 172391) (by norm_num)
theorem B1552117 : Blo 1224430 1552117 := bbase (se 5 (by rfl) ⟨72755, by rfl⟩ : syracuseStep 1552117 = 145511) (by norm_num)
theorem B2756357 : Blo 1224430 2756357 := bbase (se 4 (by rfl) ⟨258408, by rfl⟩ : syracuseStep 2756357 = 516817) (by norm_num)
theorem B5238533 : Blo 1224430 5238533 := bbase (se 4 (by rfl) ⟨491112, by rfl⟩ : syracuseStep 5238533 = 982225) (by norm_num)
theorem B1838861 : Blo 1224430 1838861 := bbase (se 3 (by rfl) ⟨344786, by rfl⟩ : syracuseStep 1838861 = 689573) (by norm_num)
theorem B1838885 : Blo 1224430 1838885 := bbase (se 4 (by rfl) ⟨172395, by rfl⟩ : syracuseStep 1838885 = 344791) (by norm_num)
theorem B3100477 : Blo 1224430 3100477 := bbase (se 3 (by rfl) ⟨581339, by rfl⟩ : syracuseStep 3100477 = 1162679) (by norm_num)
theorem B2207549 : Blo 1224430 2207549 := bbase (se 3 (by rfl) ⟨413915, by rfl⟩ : syracuseStep 2207549 = 827831) (by norm_num)
theorem B1838909 : Blo 1224430 1838909 := bbase (se 3 (by rfl) ⟨344795, by rfl⟩ : syracuseStep 1838909 = 689591) (by norm_num)
theorem B2756429 : Blo 1224430 2756429 := bbase (se 3 (by rfl) ⟨516830, by rfl⟩ : syracuseStep 2756429 = 1033661) (by norm_num)
theorem B2068301 : Blo 1224430 2068301 := bbase (se 3 (by rfl) ⟨387806, by rfl⟩ : syracuseStep 2068301 = 775613) (by norm_num)
theorem B1838933 : Blo 1224430 1838933 := bbase (se 9 (by rfl) ⟨5387, by rfl⟩ : syracuseStep 1838933 = 10775) (by norm_num)
theorem B1838957 : Blo 1224430 1838957 := bbase (se 3 (by rfl) ⟨344804, by rfl⟩ : syracuseStep 1838957 = 689609) (by norm_num)
theorem B1838981 : Blo 1224430 1838981 := bbase (se 4 (by rfl) ⟨172404, by rfl⟩ : syracuseStep 1838981 = 344809) (by norm_num)
theorem B2756501 : Blo 1224430 2756501 := bbase (se 6 (by rfl) ⟨64605, by rfl⟩ : syracuseStep 2756501 = 129211) (by norm_num)
theorem B1839005 : Blo 1224430 1839005 := bbase (se 3 (by rfl) ⟨344813, by rfl⟩ : syracuseStep 1839005 = 689627) (by norm_num)
theorem B3100589 : Blo 1224430 3100589 := bbase (se 3 (by rfl) ⟨581360, by rfl⟩ : syracuseStep 3100589 = 1162721) (by norm_num)
theorem B1839029 : Blo 1224430 1839029 := bbase (se 5 (by rfl) ⟨86204, by rfl⟩ : syracuseStep 1839029 = 172409) (by norm_num)
theorem B3927989 : Blo 1224430 3927989 := bbase (se 5 (by rfl) ⟨184124, by rfl⟩ : syracuseStep 3927989 = 368249) (by norm_num)
theorem B2617285 : Blo 1224430 2617285 := bbase (se 4 (by rfl) ⟨245370, by rfl⟩ : syracuseStep 2617285 = 490741) (by norm_num)
theorem B2068429 : Blo 1224430 2068429 := bbase (se 3 (by rfl) ⟨387830, by rfl⟩ : syracuseStep 2068429 = 775661) (by norm_num)
theorem B1839053 : Blo 1224430 1839053 := bbase (se 3 (by rfl) ⟨344822, by rfl⟩ : syracuseStep 1839053 = 689645) (by norm_num)
theorem B2756573 : Blo 1224430 2756573 := bbase (se 3 (by rfl) ⟨516857, by rfl⟩ : syracuseStep 2756573 = 1033715) (by norm_num)
theorem B1839077 : Blo 1224430 1839077 := bbase (se 4 (by rfl) ⟨172413, by rfl⟩ : syracuseStep 1839077 = 344827) (by norm_num)
theorem B1863677 : Blo 1224430 1863677 := bbase (se 3 (by rfl) ⟨349439, by rfl⟩ : syracuseStep 1863677 = 698879) (by norm_num)
theorem B1839101 : Blo 1224430 1839101 := bbase (se 3 (by rfl) ⟨344831, by rfl⟩ : syracuseStep 1839101 = 689663) (by norm_num)
theorem B5451781 : Blo 1224430 5451781 := bbase (se 4 (by rfl) ⟨511104, by rfl⟩ : syracuseStep 5451781 = 1022209) (by norm_num)
theorem B1839125 : Blo 1224430 1839125 := bbase (se 6 (by rfl) ⟨43104, by rfl⟩ : syracuseStep 1839125 = 86209) (by norm_num)
theorem B2756645 : Blo 1224430 2756645 := bbase (se 4 (by rfl) ⟨258435, by rfl⟩ : syracuseStep 2756645 = 516871) (by norm_num)
theorem B2068517 : Blo 1224430 2068517 := bbase (se 4 (by rfl) ⟨193923, by rfl⟩ : syracuseStep 2068517 = 387847) (by norm_num)
theorem B1839149 : Blo 1224430 1839149 := bbase (se 3 (by rfl) ⟨344840, by rfl⟩ : syracuseStep 1839149 = 689681) (by norm_num)
theorem B1839173 : Blo 1224430 1839173 := bbase (se 4 (by rfl) ⟨172422, by rfl⟩ : syracuseStep 1839173 = 344845) (by norm_num)
theorem B2617429 : Blo 1224430 2617429 := bbase (se 8 (by rfl) ⟨15336, by rfl⟩ : syracuseStep 2617429 = 30673) (by norm_num)
theorem B2207837 : Blo 1224430 2207837 := bbase (se 3 (by rfl) ⟨413969, by rfl⟩ : syracuseStep 2207837 = 827939) (by norm_num)
theorem B1839197 : Blo 1224430 1839197 := bbase (se 3 (by rfl) ⟨344849, by rfl⟩ : syracuseStep 1839197 = 689699) (by norm_num)
theorem B3100781 : Blo 1224430 3100781 := bbase (se 3 (by rfl) ⟨581396, by rfl⟩ : syracuseStep 3100781 = 1162793) (by norm_num)
theorem B2756717 : Blo 1224430 2756717 := bbase (se 3 (by rfl) ⟨516884, by rfl⟩ : syracuseStep 2756717 = 1033769) (by norm_num)
theorem B1839221 : Blo 1224430 1839221 := bbase (se 5 (by rfl) ⟨86213, by rfl⟩ : syracuseStep 1839221 = 172427) (by norm_num)
theorem B4132997 : Blo 1224430 4132997 := bbase (se 4 (by rfl) ⟨387468, by rfl⟩ : syracuseStep 4132997 = 774937) (by norm_num)
theorem B1839245 : Blo 1224430 1839245 := bbase (se 3 (by rfl) ⟨344858, by rfl⟩ : syracuseStep 1839245 = 689717) (by norm_num)
theorem B3723413 : Blo 1224430 3723413 := bbase (se 6 (by rfl) ⟨87267, by rfl⟩ : syracuseStep 3723413 = 174535) (by norm_num)
theorem B5230757 : Blo 1224430 5230757 := bbase (se 4 (by rfl) ⟨490383, by rfl⟩ : syracuseStep 5230757 = 980767) (by norm_num)
theorem B1962149 : Blo 1224430 1962149 := bbase (se 4 (by rfl) ⟨183951, by rfl⟩ : syracuseStep 1962149 = 367903) (by norm_num)
theorem B2068645 : Blo 1224430 2068645 := bbase (se 4 (by rfl) ⟨193935, by rfl⟩ : syracuseStep 2068645 = 387871) (by norm_num)
theorem B1839269 : Blo 1224430 1839269 := bbase (se 4 (by rfl) ⟨172431, by rfl⟩ : syracuseStep 1839269 = 344863) (by norm_num)
theorem B2756789 : Blo 1224430 2756789 := bbase (se 5 (by rfl) ⟨129224, by rfl⟩ : syracuseStep 2756789 = 258449) (by norm_num)
theorem B1839293 : Blo 1224430 1839293 := bbase (se 3 (by rfl) ⟨344867, by rfl⟩ : syracuseStep 1839293 = 689735) (by norm_num)
theorem B3723461 : Blo 1224430 3723461 := bbase (se 4 (by rfl) ⟨349074, by rfl⟩ : syracuseStep 3723461 = 698149) (by norm_num)
theorem B1839317 : Blo 1224430 1839317 := bbase (se 7 (by rfl) ⟨21554, by rfl⟩ : syracuseStep 1839317 = 43109) (by norm_num)
theorem B1839341 : Blo 1224430 1839341 := bbase (se 3 (by rfl) ⟨344876, by rfl⟩ : syracuseStep 1839341 = 689753) (by norm_num)
theorem B2756861 : Blo 1224430 2756861 := bbase (se 3 (by rfl) ⟨516911, by rfl⟩ : syracuseStep 2756861 = 1033823) (by norm_num)
theorem B2068733 : Blo 1224430 2068733 := bbase (se 3 (by rfl) ⟨387887, by rfl⟩ : syracuseStep 2068733 = 775775) (by norm_num)
theorem B1839365 : Blo 1224430 1839365 := bbase (se 4 (by rfl) ⟨172440, by rfl⟩ : syracuseStep 1839365 = 344881) (by norm_num)
theorem B1839389 : Blo 1224430 1839389 := bbase (se 3 (by rfl) ⟨344885, by rfl⟩ : syracuseStep 1839389 = 689771) (by norm_num)
theorem B6205733 : Blo 1224430 6205733 := bbase (se 4 (by rfl) ⟨581787, by rfl⟩ : syracuseStep 6205733 = 1163575) (by norm_num)
theorem B1839413 : Blo 1224430 1839413 := bbase (se 5 (by rfl) ⟨86222, by rfl⟩ : syracuseStep 1839413 = 172445) (by norm_num)
theorem B2756933 : Blo 1224430 2756933 := bbase (se 4 (by rfl) ⟨258462, by rfl⟩ : syracuseStep 2756933 = 516925) (by norm_num)
theorem B1839437 : Blo 1224430 1839437 := bbase (se 3 (by rfl) ⟨344894, by rfl⟩ : syracuseStep 1839437 = 689789) (by norm_num)
theorem B1839461 : Blo 1224430 1839461 := bbase (se 4 (by rfl) ⟨172449, by rfl⟩ : syracuseStep 1839461 = 344899) (by norm_num)
theorem B2068861 : Blo 1224430 2068861 := bbase (se 3 (by rfl) ⟨387911, by rfl⟩ : syracuseStep 2068861 = 775823) (by norm_num)
theorem B1839485 : Blo 1224430 1839485 := bbase (se 3 (by rfl) ⟨344903, by rfl⟩ : syracuseStep 1839485 = 689807) (by norm_num)
theorem B2757005 : Blo 1224430 2757005 := bbase (se 3 (by rfl) ⟨516938, by rfl⟩ : syracuseStep 2757005 = 1033877) (by norm_num)
theorem B10465685 : Blo 1224430 10465685 := bbase (se 6 (by rfl) ⟨245289, by rfl⟩ : syracuseStep 10465685 = 490579) (by norm_num)
theorem B1839509 : Blo 1224430 1839509 := bbase (se 6 (by rfl) ⟨43113, by rfl⟩ : syracuseStep 1839509 = 86227) (by norm_num)
theorem B1839533 : Blo 1224430 1839533 := bbase (se 3 (by rfl) ⟨344912, by rfl⟩ : syracuseStep 1839533 = 689825) (by norm_num)
theorem B3101125 : Blo 1224430 3101125 := bbase (se 4 (by rfl) ⟨290730, by rfl⟩ : syracuseStep 3101125 = 581461) (by norm_num)
theorem B1839557 : Blo 1224430 1839557 := bbase (se 4 (by rfl) ⟨172458, by rfl⟩ : syracuseStep 1839557 = 344917) (by norm_num)
theorem B2617805 : Blo 1224430 2617805 := bbase (se 3 (by rfl) ⟨490838, by rfl⟩ : syracuseStep 2617805 = 981677) (by norm_num)
theorem B2757077 : Blo 1224430 2757077 := bbase (se 7 (by rfl) ⟨32309, by rfl⟩ : syracuseStep 2757077 = 64619) (by norm_num)
theorem B2068949 : Blo 1224430 2068949 := bbase (se 7 (by rfl) ⟨24245, by rfl⟩ : syracuseStep 2068949 = 48491) (by norm_num)
theorem B1839581 : Blo 1224430 1839581 := bbase (se 3 (by rfl) ⟨344921, by rfl⟩ : syracuseStep 1839581 = 689843) (by norm_num)
theorem B1839605 : Blo 1224430 1839605 := bbase (se 5 (by rfl) ⟨86231, by rfl⟩ : syracuseStep 1839605 = 172463) (by norm_num)
theorem B1839629 : Blo 1224430 1839629 := bbase (se 3 (by rfl) ⟨344930, by rfl⟩ : syracuseStep 1839629 = 689861) (by norm_num)
theorem B3142165 : Blo 1224430 3142165 := bbase (se 6 (by rfl) ⟨73644, by rfl⟩ : syracuseStep 3142165 = 147289) (by norm_num)
theorem B2757149 : Blo 1224430 2757149 := bbase (se 3 (by rfl) ⟨516965, by rfl⟩ : syracuseStep 2757149 = 1033931) (by norm_num)
theorem B4133429 : Blo 1224430 4133429 := bbase (se 5 (by rfl) ⟨193754, by rfl⟩ : syracuseStep 4133429 = 387509) (by norm_num)
theorem B3101237 : Blo 1224430 3101237 := bbase (se 5 (by rfl) ⟨145370, by rfl⟩ : syracuseStep 3101237 = 290741) (by norm_num)
theorem B2069077 : Blo 1224430 2069077 := bbase (se 8 (by rfl) ⟨12123, by rfl⟩ : syracuseStep 2069077 = 24247) (by norm_num)
theorem B2757221 : Blo 1224430 2757221 := bbase (se 4 (by rfl) ⟨258489, by rfl⟩ : syracuseStep 2757221 = 516979) (by norm_num)
theorem B1962605 : Blo 1224430 1962605 := bbase (se 3 (by rfl) ⟨367988, by rfl⟩ : syracuseStep 1962605 = 735977) (by norm_num)
theorem B2757293 : Blo 1224430 2757293 := bbase (se 3 (by rfl) ⟨516992, by rfl⟩ : syracuseStep 2757293 = 1033985) (by norm_num)
theorem B2069165 : Blo 1224430 2069165 := bbase (se 3 (by rfl) ⟨387968, by rfl⟩ : syracuseStep 2069165 = 775937) (by norm_num)
theorem B4649669 : Blo 1224430 4649669 := bbase (se 4 (by rfl) ⟨435906, by rfl⟩ : syracuseStep 4649669 = 871813) (by norm_num)
theorem B4969189 : Blo 1224430 4969189 := bbase (se 4 (by rfl) ⟨465861, by rfl⟩ : syracuseStep 4969189 = 931723) (by norm_num)
theorem B3101429 : Blo 1224430 3101429 := bbase (se 5 (by rfl) ⟨145379, by rfl⟩ : syracuseStep 3101429 = 290759) (by norm_num)
theorem B2757365 : Blo 1224430 2757365 := bbase (se 5 (by rfl) ⟨129251, by rfl⟩ : syracuseStep 2757365 = 258503) (by norm_num)
theorem B2069293 : Blo 1224430 2069293 := bbase (se 3 (by rfl) ⟨387992, by rfl⟩ : syracuseStep 2069293 = 775985) (by norm_num)
theorem B2757437 : Blo 1224430 2757437 := bbase (se 3 (by rfl) ⟨517019, by rfl⟩ : syracuseStep 2757437 = 1034039) (by norm_num)
theorem B2618173 : Blo 1224430 2618173 := bbase (se 3 (by rfl) ⟨490907, by rfl⟩ : syracuseStep 2618173 = 981815) (by norm_num)
theorem B1962829 : Blo 1224430 1962829 := bbase (se 3 (by rfl) ⟨368030, by rfl⟩ : syracuseStep 1962829 = 736061) (by norm_num)
theorem B5591909 : Blo 1224430 5591909 := bbase (se 4 (by rfl) ⟨524241, by rfl⟩ : syracuseStep 5591909 = 1048483) (by norm_num)
theorem B2757509 : Blo 1224430 2757509 := bbase (se 4 (by rfl) ⟨258516, by rfl⟩ : syracuseStep 2757509 = 517033) (by norm_num)
theorem B2069381 : Blo 1224430 2069381 := bbase (se 4 (by rfl) ⟨194004, by rfl⟩ : syracuseStep 2069381 = 388009) (by norm_num)
theorem B1962893 : Blo 1224430 1962893 := bbase (se 3 (by rfl) ⟨368042, by rfl⟩ : syracuseStep 1962893 = 736085) (by norm_num)
theorem B1307549 : Blo 1224430 1307549 := bbase (se 3 (by rfl) ⟨245165, by rfl⟩ : syracuseStep 1307549 = 490331) (by norm_num)
theorem B2757581 : Blo 1224430 2757581 := bbase (se 3 (by rfl) ⟨517046, by rfl⟩ : syracuseStep 2757581 = 1034093) (by norm_num)
theorem B1307621 : Blo 1224430 1307621 := bbase (se 4 (by rfl) ⟨122589, by rfl⟩ : syracuseStep 1307621 = 245179) (by norm_num)
theorem B4649957 : Blo 1224430 4649957 := bbase (se 4 (by rfl) ⟨435933, by rfl⟩ : syracuseStep 4649957 = 871867) (by norm_num)
theorem B4133861 : Blo 1224430 4133861 := bbase (se 4 (by rfl) ⟨387549, by rfl⟩ : syracuseStep 4133861 = 775099) (by norm_num)
theorem B2069509 : Blo 1224430 2069509 := bbase (se 4 (by rfl) ⟨194016, by rfl⟩ : syracuseStep 2069509 = 388033) (by norm_num)
theorem B1963021 : Blo 1224430 1963021 := bbase (se 3 (by rfl) ⟨368066, by rfl⟩ : syracuseStep 1963021 = 736133) (by norm_num)
theorem B2757653 : Blo 1224430 2757653 := bbase (se 6 (by rfl) ⟨64632, by rfl⟩ : syracuseStep 2757653 = 129265) (by norm_num)
theorem B3101773 : Blo 1224430 3101773 := bbase (se 3 (by rfl) ⟨581582, by rfl⟩ : syracuseStep 3101773 = 1163165) (by norm_num)
theorem B2208853 : Blo 1224430 2208853 := bbase (se 8 (by rfl) ⟨12942, by rfl⟩ : syracuseStep 2208853 = 25885) (by norm_num)
theorem B2757725 : Blo 1224430 2757725 := bbase (se 3 (by rfl) ⟨517073, by rfl⟩ : syracuseStep 2757725 = 1034147) (by norm_num)
theorem B2069597 : Blo 1224430 2069597 := bbase (se 3 (by rfl) ⟨388049, by rfl⟩ : syracuseStep 2069597 = 776099) (by norm_num)
theorem B5231749 : Blo 1224430 5231749 := bbase (se 4 (by rfl) ⟨490476, by rfl⟩ : syracuseStep 5231749 = 980953) (by norm_num)
theorem B1307809 : Blo 1224430 1307809 := bbase (se 2 (by rfl) ⟨490428, by rfl⟩ : syracuseStep 1307809 = 980857) (by norm_num)
theorem B2757797 : Blo 1224430 2757797 := bbase (se 4 (by rfl) ⟨258543, by rfl⟩ : syracuseStep 2757797 = 517087) (by norm_num)
theorem B3101885 : Blo 1224430 3101885 := bbase (se 3 (by rfl) ⟨581603, by rfl⟩ : syracuseStep 3101885 = 1163207) (by norm_num)
theorem B2757869 : Blo 1224430 2757869 := bbase (se 3 (by rfl) ⟨517100, by rfl⟩ : syracuseStep 2757869 = 1034201) (by norm_num)
theorem B3314933 : Blo 1224430 3314933 := bbase (se 5 (by rfl) ⟨155387, by rfl⟩ : syracuseStep 3314933 = 310775) (by norm_num)
theorem B3487013 : Blo 1224430 3487013 := bbase (se 4 (by rfl) ⟨326907, by rfl⟩ : syracuseStep 3487013 = 653815) (by norm_num)
theorem B2757941 : Blo 1224430 2757941 := bbase (se 5 (by rfl) ⟨129278, by rfl⟩ : syracuseStep 2757941 = 258557) (by norm_num)
theorem B1307993 : Blo 1224430 1307993 := bbase (se 2 (by rfl) ⟨490497, by rfl⟩ : syracuseStep 1307993 = 980995) (by norm_num)
theorem B3102077 : Blo 1224430 3102077 := bbase (se 3 (by rfl) ⟨581639, by rfl⟩ : syracuseStep 3102077 = 1163279) (by norm_num)
theorem B2758013 : Blo 1224430 2758013 := bbase (se 3 (by rfl) ⟨517127, by rfl⟩ : syracuseStep 2758013 = 1034255) (by norm_num)
theorem B4134293 : Blo 1224430 4134293 := bbase (se 6 (by rfl) ⟨96897, by rfl⟩ : syracuseStep 4134293 = 193795) (by norm_num)
theorem B1398169 : Blo 1224430 1398169 := bbase (se 2 (by rfl) ⟨524313, by rfl⟩ : syracuseStep 1398169 = 1048627) (by norm_num)
theorem B1242545 : Blo 1224430 1242545 := bbase (se 2 (by rfl) ⟨465954, by rfl⟩ : syracuseStep 1242545 = 931909) (by norm_num)
theorem B2758085 : Blo 1224430 2758085 := bbase (se 4 (by rfl) ⟨258570, by rfl⟩ : syracuseStep 2758085 = 517141) (by norm_num)
theorem B1242581 : Blo 1224430 1242581 := bbase (se 7 (by rfl) ⟨14561, by rfl⟩ : syracuseStep 1242581 = 29123) (by norm_num)
theorem B2758157 : Blo 1224430 2758157 := bbase (se 3 (by rfl) ⟨517154, by rfl⟩ : syracuseStep 2758157 = 1034309) (by norm_num)
theorem B5887525 : Blo 1224430 5887525 := bbase (se 4 (by rfl) ⟨551955, by rfl⟩ : syracuseStep 5887525 = 1103911) (by norm_num)
theorem B6207029 : Blo 1224430 6207029 := bbase (se 5 (by rfl) ⟨290954, by rfl⟩ : syracuseStep 6207029 = 581909) (by norm_num)
theorem B2758229 : Blo 1224430 2758229 := bbase (se 8 (by rfl) ⟨16161, by rfl⟩ : syracuseStep 2758229 = 32323) (by norm_num)
theorem B2758301 : Blo 1224430 2758301 := bbase (se 3 (by rfl) ⟨517181, by rfl⟩ : syracuseStep 2758301 = 1034363) (by norm_num)
theorem B3487445 : Blo 1224430 3487445 := bbase (se 7 (by rfl) ⟨40868, by rfl⟩ : syracuseStep 3487445 = 81737) (by norm_num)
theorem B3102421 : Blo 1224430 3102421 := bbase (se 7 (by rfl) ⟨36356, by rfl⟩ : syracuseStep 3102421 = 72713) (by norm_num)
theorem B2758373 : Blo 1224430 2758373 := bbase (se 4 (by rfl) ⟨258597, by rfl⟩ : syracuseStep 2758373 = 517195) (by norm_num)
theorem B1472261 : Blo 1224430 1472261 := bbase (se 4 (by rfl) ⟨138024, by rfl⟩ : syracuseStep 1472261 = 276049) (by norm_num)
theorem B4970261 : Blo 1224430 4970261 := bbase (se 6 (by rfl) ⟨116490, by rfl⟩ : syracuseStep 4970261 = 232981) (by norm_num)
theorem B1275685 : Blo 1224430 1275685 := bbase (se 4 (by rfl) ⟨119595, by rfl⟩ : syracuseStep 1275685 = 239191) (by norm_num)
theorem B2758445 : Blo 1224430 2758445 := bbase (se 3 (by rfl) ⟨517208, by rfl⟩ : syracuseStep 2758445 = 1034417) (by norm_num)
theorem B4134725 : Blo 1224430 4134725 := bbase (se 4 (by rfl) ⟨387630, by rfl⟩ : syracuseStep 4134725 = 775261) (by norm_num)
theorem B3102533 : Blo 1224430 3102533 := bbase (se 4 (by rfl) ⟨290862, by rfl⟩ : syracuseStep 3102533 = 581725) (by norm_num)
theorem B2094941 : Blo 1224430 2094941 := bbase (se 3 (by rfl) ⟨392801, by rfl⟩ : syracuseStep 2094941 = 785603) (by norm_num)
theorem B2758517 : Blo 1224430 2758517 := bbase (se 5 (by rfl) ⟨129305, by rfl⟩ : syracuseStep 2758517 = 258611) (by norm_num)
theorem B2357117 : Blo 1224430 2357117 := bbase (se 3 (by rfl) ⟨441959, by rfl⟩ : syracuseStep 2357117 = 883919) (by norm_num)
theorem B3880885 : Blo 1224430 3880885 := bbase (se 5 (by rfl) ⟨181916, by rfl⟩ : syracuseStep 3880885 = 363833) (by norm_num)
theorem B4192181 : Blo 1224430 4192181 := bbase (se 5 (by rfl) ⟨196508, by rfl⟩ : syracuseStep 4192181 = 393017) (by norm_num)
theorem B2758589 : Blo 1224430 2758589 := bbase (se 3 (by rfl) ⟨517235, by rfl⟩ : syracuseStep 2758589 = 1034471) (by norm_num)
theorem B6199253 : Blo 1224430 6199253 := bbase (se 7 (by rfl) ⟨72647, by rfl⟩ : syracuseStep 6199253 = 145295) (by norm_num)
theorem B9312245 : Blo 1224430 9312245 := bbase (se 5 (by rfl) ⟨436511, by rfl⟩ : syracuseStep 9312245 = 873023) (by norm_num)
theorem B3102725 : Blo 1224430 3102725 := bbase (se 4 (by rfl) ⟨290880, by rfl⟩ : syracuseStep 3102725 = 581761) (by norm_num)
theorem B2758661 : Blo 1224430 2758661 := bbase (se 4 (by rfl) ⟨258624, by rfl⟩ : syracuseStep 2758661 = 517249) (by norm_num)
theorem B1308745 : Blo 1224430 1308745 := bbase (se 2 (by rfl) ⟨490779, by rfl⟩ : syracuseStep 1308745 = 981559) (by norm_num)
theorem B2758733 : Blo 1224430 2758733 := bbase (se 3 (by rfl) ⟨517262, by rfl⟩ : syracuseStep 2758733 = 1034525) (by norm_num)
theorem B1472593 : Blo 1224430 1472593 := bbase (se 2 (by rfl) ⟨552222, by rfl⟩ : syracuseStep 1472593 = 1104445) (by norm_num)
theorem B4651141 : Blo 1224430 4651141 := bbase (se 4 (by rfl) ⟨436044, by rfl⟩ : syracuseStep 4651141 = 872089) (by norm_num)
theorem B5036165 : Blo 1224430 5036165 := bbase (se 4 (by rfl) ⟨472140, by rfl⟩ : syracuseStep 5036165 = 944281) (by norm_num)
theorem B1308817 : Blo 1224430 1308817 := bbase (se 2 (by rfl) ⟨490806, by rfl⟩ : syracuseStep 1308817 = 981613) (by norm_num)
theorem B2324629 : Blo 1224430 2324629 := bbase (se 6 (by rfl) ⟨54483, by rfl⟩ : syracuseStep 2324629 = 108967) (by norm_num)
theorem B2758805 : Blo 1224430 2758805 := bbase (se 6 (by rfl) ⟨64659, by rfl⟩ : syracuseStep 2758805 = 129319) (by norm_num)
theorem B3184805 : Blo 1224430 3184805 := bbase (se 4 (by rfl) ⟨298575, by rfl⟩ : syracuseStep 3184805 = 597151) (by norm_num)
theorem B1964245 : Blo 1224430 1964245 := bbase (se 7 (by rfl) ⟨23018, by rfl⟩ : syracuseStep 1964245 = 46037) (by norm_num)
theorem B2758877 : Blo 1224430 2758877 := bbase (se 3 (by rfl) ⟨517289, by rfl⟩ : syracuseStep 2758877 = 1034579) (by norm_num)
theorem B1472737 : Blo 1224430 1472737 := bbase (se 2 (by rfl) ⟨552276, by rfl⟩ : syracuseStep 1472737 = 1104553) (by norm_num)
theorem B4135157 : Blo 1224430 4135157 := bbase (se 5 (by rfl) ⟨193835, by rfl⟩ : syracuseStep 4135157 = 387671) (by norm_num)
theorem B2758949 : Blo 1224430 2758949 := bbase (se 4 (by rfl) ⟨258651, by rfl⟩ : syracuseStep 2758949 = 517303) (by norm_num)
theorem B1308997 : Blo 1224430 1308997 := bbase (se 4 (by rfl) ⟨122718, by rfl⟩ : syracuseStep 1308997 = 245437) (by norm_num)
theorem B3103069 : Blo 1224430 3103069 := bbase (se 3 (by rfl) ⟨581825, by rfl⟩ : syracuseStep 3103069 = 1163651) (by norm_num)
theorem B2759021 : Blo 1224430 2759021 := bbase (se 3 (by rfl) ⟨517316, by rfl⟩ : syracuseStep 2759021 = 1034633) (by norm_num)
theorem B9304469 : Blo 1224430 9304469 := bbase (se 6 (by rfl) ⟨218073, by rfl⟩ : syracuseStep 9304469 = 436147) (by norm_num)
theorem B4651445 : Blo 1224430 4651445 := bbase (se 5 (by rfl) ⟨218036, by rfl⟩ : syracuseStep 4651445 = 436073) (by norm_num)
theorem B2759093 : Blo 1224430 2759093 := bbase (se 5 (by rfl) ⟨129332, by rfl⟩ : syracuseStep 2759093 = 258665) (by norm_num)
theorem B2324933 : Blo 1224430 2324933 := bbase (se 4 (by rfl) ⟨217962, by rfl⟩ : syracuseStep 2324933 = 435925) (by norm_num)
theorem B3488197 : Blo 1224430 3488197 := bbase (se 4 (by rfl) ⟨327018, by rfl⟩ : syracuseStep 3488197 = 654037) (by norm_num)
theorem B3103181 : Blo 1224430 3103181 := bbase (se 3 (by rfl) ⟨581846, by rfl⟩ : syracuseStep 3103181 = 1163693) (by norm_num)
theorem B3725797 : Blo 1224430 3725797 := bbase (se 4 (by rfl) ⟨349293, by rfl⟩ : syracuseStep 3725797 = 698587) (by norm_num)
theorem B2759165 : Blo 1224430 2759165 := bbase (se 3 (by rfl) ⟨517343, by rfl⟩ : syracuseStep 2759165 = 1034687) (by norm_num)
theorem B2652725 : Blo 1224430 2652725 := bbase (se 5 (by rfl) ⟨124346, by rfl⟩ : syracuseStep 2652725 = 248693) (by norm_num)
theorem B2759237 : Blo 1224430 2759237 := bbase (se 4 (by rfl) ⟨258678, by rfl⟩ : syracuseStep 2759237 = 517357) (by norm_num)
theorem B8829557 : Blo 1224430 8829557 := bbase (se 5 (by rfl) ⟨413885, by rfl⟩ : syracuseStep 8829557 = 827771) (by norm_num)
theorem B3103373 : Blo 1224430 3103373 := bbase (se 3 (by rfl) ⟨581882, by rfl⟩ : syracuseStep 3103373 = 1163765) (by norm_num)
theorem B2759309 : Blo 1224430 2759309 := bbase (se 3 (by rfl) ⟨517370, by rfl⟩ : syracuseStep 2759309 = 1034741) (by norm_num)
theorem B4135589 : Blo 1224430 4135589 := bbase (se 4 (by rfl) ⟨387711, by rfl⟩ : syracuseStep 4135589 = 775423) (by norm_num)
theorem B2759381 : Blo 1224430 2759381 := bbase (se 7 (by rfl) ⟨32336, by rfl⟩ : syracuseStep 2759381 = 64673) (by norm_num)
theorem B1309441 : Blo 1224430 1309441 := bbase (se 2 (by rfl) ⟨491040, by rfl⟩ : syracuseStep 1309441 = 982081) (by norm_num)
theorem B2759453 : Blo 1224430 2759453 := bbase (se 3 (by rfl) ⟨517397, by rfl⟩ : syracuseStep 2759453 = 1034795) (by norm_num)
theorem B3144485 : Blo 1224430 3144485 := bbase (se 4 (by rfl) ⟨294795, by rfl⟩ : syracuseStep 3144485 = 589591) (by norm_num)
theorem B6208325 : Blo 1224430 6208325 := bbase (se 4 (by rfl) ⟨582030, by rfl⟩ : syracuseStep 6208325 = 1164061) (by norm_num)
theorem B23886677 : Blo 1224430 23886677 := bbase (se 9 (by rfl) ⟨69980, by rfl⟩ : syracuseStep 23886677 = 139961) (by norm_num)
theorem B1309565 : Blo 1224430 1309565 := bbase (se 3 (by rfl) ⟨245543, by rfl⟩ : syracuseStep 1309565 = 491087) (by norm_num)
theorem B3103717 : Blo 1224430 3103717 := bbase (se 4 (by rfl) ⟨290973, by rfl⟩ : syracuseStep 3103717 = 581947) (by norm_num)
theorem B6978581 : Blo 1224430 6978581 := bbase (se 6 (by rfl) ⟨163560, by rfl⟩ : syracuseStep 6978581 = 327121) (by norm_num)
theorem B7855157 : Blo 1224430 7855157 := bbase (se 5 (by rfl) ⟨368210, by rfl⟩ : syracuseStep 7855157 = 736421) (by norm_num)
theorem B4136021 : Blo 1224430 4136021 := bbase (se 8 (by rfl) ⟨24234, by rfl⟩ : syracuseStep 4136021 = 48469) (by norm_num)
theorem B3103829 : Blo 1224430 3103829 := bbase (se 8 (by rfl) ⟨18186, by rfl⟩ : syracuseStep 3103829 = 36373) (by norm_num)
theorem B1989725 : Blo 1224430 1989725 := bbase (se 3 (by rfl) ⟨373073, by rfl⟩ : syracuseStep 1989725 = 746147) (by norm_num)
theorem B2325685 : Blo 1224430 2325685 := bbase (se 5 (by rfl) ⟨109016, by rfl⟩ : syracuseStep 2325685 = 218033) (by norm_num)
theorem B1326277 : Blo 1224430 1326277 := bbase (se 4 (by rfl) ⟨124338, by rfl⟩ : syracuseStep 1326277 = 248677) (by norm_num)
theorem B6200549 : Blo 1224430 6200549 := bbase (se 4 (by rfl) ⟨581301, by rfl⟩ : syracuseStep 6200549 = 1162603) (by norm_num)
theorem B3104021 : Blo 1224430 3104021 := bbase (se 6 (by rfl) ⟨72750, by rfl⟩ : syracuseStep 3104021 = 145501) (by norm_num)
theorem B8502581 : Blo 1224430 8502581 := bbase (se 5 (by rfl) ⟨398558, by rfl⟩ : syracuseStep 8502581 = 797117) (by norm_num)
theorem B2325829 : Blo 1224430 2325829 := bbase (se 4 (by rfl) ⟨218046, by rfl⟩ : syracuseStep 2325829 = 436093) (by norm_num)
theorem B3145037 : Blo 1224430 3145037 := bbase (se 3 (by rfl) ⟨589694, by rfl⟩ : syracuseStep 3145037 = 1179389) (by norm_num)
theorem B2325989 : Blo 1224430 2325989 := bbase (se 4 (by rfl) ⟨218061, by rfl⟩ : syracuseStep 2325989 = 436123) (by norm_num)
theorem B1990117 : Blo 1224430 1990117 := bbase (se 4 (by rfl) ⟨186573, by rfl⟩ : syracuseStep 1990117 = 373147) (by norm_num)
theorem B4136453 : Blo 1224430 4136453 := bbase (se 4 (by rfl) ⟨387792, by rfl⟩ : syracuseStep 4136453 = 775585) (by norm_num)
theorem B1744429 : Blo 1224430 1744429 := bbase (se 3 (by rfl) ⟨327080, by rfl⟩ : syracuseStep 1744429 = 654161) (by norm_num)
theorem B3104365 : Blo 1224430 3104365 := bbase (se 3 (by rfl) ⟨582068, by rfl⟩ : syracuseStep 3104365 = 1164137) (by norm_num)
theorem B2326133 : Blo 1224430 2326133 := bbase (se 5 (by rfl) ⟨109037, by rfl⟩ : syracuseStep 2326133 = 218075) (by norm_num)
theorem B3726965 : Blo 1224430 3726965 := bbase (se 5 (by rfl) ⟨174701, by rfl⟩ : syracuseStep 3726965 = 349403) (by norm_num)
theorem B2391805 : Blo 1224430 2391805 := bbase (se 3 (by rfl) ⟨448463, by rfl⟩ : syracuseStep 2391805 = 896927) (by norm_num)
theorem B2326421 : Blo 1224430 2326421 := bbase (se 6 (by rfl) ⟨54525, by rfl⟩ : syracuseStep 2326421 = 109051) (by norm_num)
theorem B4415413 : Blo 1224430 4415413 := bbase (se 5 (by rfl) ⟨206972, by rfl⟩ : syracuseStep 4415413 = 413945) (by norm_num)
theorem B4136885 : Blo 1224430 4136885 := bbase (se 5 (by rfl) ⟨193916, by rfl⟩ : syracuseStep 4136885 = 387833) (by norm_num)
theorem B4194317 : Blo 1224430 4194317 := bstep (se 3 (by rfl) ⟨786434, by rfl⟩ : syracuseStep 4194317 = 1572869) B1572869
theorem B15704117 : Blo 1224430 15704117 := bstep (se 5 (by rfl) ⟨736130, by rfl⟩ : syracuseStep 15704117 = 1472261) B1472261
theorem B1744993 : Blo 1224430 1744993 := bstep (se 2 (by rfl) ⟨654372, by rfl⟩ : syracuseStep 1744993 = 1308745) B1308745
theorem B7848035 : Blo 1224430 7848035 := bstep (se 1 (by rfl) ⟨5886026, by rfl⟩ : syracuseStep 7848035 = 11772053) B11772053
theorem B3489905 : Blo 1224430 3489905 := bstep (se 2 (by rfl) ⟨1308714, by rfl⟩ : syracuseStep 3489905 = 2617429) B2617429
theorem B2482307 : Blo 1224430 2482307 := bstep (se 1 (by rfl) ⟨1861730, by rfl⟩ : syracuseStep 2482307 = 3723461) B3723461
theorem B4137101 : Blo 1224430 4137101 := bstep (se 3 (by rfl) ⟨775706, by rfl⟩ : syracuseStep 4137101 = 1551413) B1551413
theorem B20947085 : Blo 1224430 20947085 := bstep (se 3 (by rfl) ⟨3927578, by rfl⟩ : syracuseStep 20947085 = 7855157) B7855157
theorem B6201521 : Blo 1224430 6201521 := bstep (se 2 (by rfl) ⟨2325570, by rfl⟩ : syracuseStep 6201521 = 4651141) B4651141
theorem B4137155 : Blo 1224430 4137155 := bstep (se 1 (by rfl) ⟨3102866, by rfl⟩ : syracuseStep 4137155 = 6205733) B6205733
theorem B2015491 : Blo 1224430 2015491 := bstep (se 1 (by rfl) ⟨1511618, by rfl⟩ : syracuseStep 2015491 = 3023237) B3023237
theorem B2326801 : Blo 1224430 2326801 := bstep (se 2 (by rfl) ⟨872550, by rfl⟩ : syracuseStep 2326801 = 1745101) B1745101
theorem B4653389 : Blo 1224430 4653389 := bstep (se 3 (by rfl) ⟨872510, by rfl⟩ : syracuseStep 4653389 = 1745021) B1745021
theorem B9929101 : Blo 1224430 9929101 := bstep (se 3 (by rfl) ⟨1861706, by rfl⟩ : syracuseStep 9929101 = 3723413) B3723413
theorem B2097569 : Blo 1224430 2097569 := bstep (se 2 (by rfl) ⟨786588, by rfl⟩ : syracuseStep 2097569 = 1573177) B1573177
theorem B2326961 : Blo 1224430 2326961 := bstep (se 2 (by rfl) ⟨872610, by rfl⟩ : syracuseStep 2326961 = 1745221) B1745221
theorem B1745329 : Blo 1224430 1745329 := bstep (se 2 (by rfl) ⟨654498, by rfl⟩ : syracuseStep 1745329 = 1308997) B1308997
theorem B11780549 : Blo 1224430 11780549 := bstep (se 4 (by rfl) ⟨1104426, by rfl⟩ : syracuseStep 11780549 = 2208853) B2208853
theorem B4137425 : Blo 1224430 4137425 := bstep (se 2 (by rfl) ⟨1551534, by rfl⟩ : syracuseStep 4137425 = 3103069) B3103069
theorem B5308913 : Blo 1224430 5308913 := bstep (se 2 (by rfl) ⟨1990842, by rfl⟩ : syracuseStep 5308913 = 3981685) B3981685
theorem B3727939 : Blo 1224430 3727939 := bstep (se 1 (by rfl) ⟨2795954, by rfl⟩ : syracuseStep 3727939 = 5591909) B5591909
theorem B13951601 : Blo 1224430 13951601 := bstep (se 2 (by rfl) ⟨5231850, by rfl⟩ : syracuseStep 13951601 = 10463701) B10463701
theorem B3539693 : Blo 1224430 3539693 := bstep (se 3 (by rfl) ⟨663692, by rfl⟩ : syracuseStep 3539693 = 1327385) B1327385
theorem B6980357 : Blo 1224430 6980357 := bstep (se 4 (by rfl) ⟨654408, by rfl⟩ : syracuseStep 6980357 = 1308817) B1308817
theorem B27214613 : Blo 1224430 27214613 := bstep (se 6 (by rfl) ⟨637842, by rfl⟩ : syracuseStep 27214613 = 1275685) B1275685
theorem B33547061 : Blo 1224430 33547061 := bstep (se 5 (by rfl) ⟨1572518, by rfl⟩ : syracuseStep 33547061 = 3145037) B3145037
theorem B2327363 : Blo 1224430 2327363 := bstep (se 1 (by rfl) ⟨1745522, by rfl⟩ : syracuseStep 2327363 = 3491045) B3491045
theorem B3539857 : Blo 1224430 3539857 := bstep (se 2 (by rfl) ⟨1327446, by rfl⟩ : syracuseStep 3539857 = 2654893) B2654893
theorem B4137965 : Blo 1224430 4137965 := bstep (se 3 (by rfl) ⟨775868, by rfl⟩ : syracuseStep 4137965 = 1551737) B1551737
theorem B1745921 : Blo 1224430 1745921 := bstep (se 2 (by rfl) ⟨654720, by rfl⟩ : syracuseStep 1745921 = 1309441) B1309441
theorem B4138019 : Blo 1224430 4138019 := bstep (se 1 (by rfl) ⟨3103514, by rfl⟩ : syracuseStep 4138019 = 6207029) B6207029
theorem B3490897 : Blo 1224430 3490897 := bstep (se 2 (by rfl) ⟨1309086, by rfl⟩ : syracuseStep 3490897 = 2618173) B2618173
theorem B1492115 : Blo 1224430 1492115 := bstep (se 1 (by rfl) ⟨1119086, by rfl⟩ : syracuseStep 1492115 = 2238173) B2238173
theorem B6980813 : Blo 1224430 6980813 := bstep (se 3 (by rfl) ⟨1308902, by rfl⟩ : syracuseStep 6980813 = 2617805) B2617805
theorem B1377571 : Blo 1224430 1377571 := bstep (se 1 (by rfl) ⟨1033178, by rfl⟩ : syracuseStep 1377571 = 2066357) B2066357
theorem B2794787 : Blo 1224430 2794787 := bstep (se 1 (by rfl) ⟨2096090, by rfl⟩ : syracuseStep 2794787 = 4192181) B4192181
theorem B4138289 : Blo 1224430 4138289 := bstep (se 2 (by rfl) ⟨1551858, by rfl⟩ : syracuseStep 4138289 = 3103717) B3103717
theorem B3491171 : Blo 1224430 3491171 := bstep (se 1 (by rfl) ⟨2618378, by rfl⟩ : syracuseStep 3491171 = 5236757) B5236757
theorem B8390051 : Blo 1224430 8390051 := bstep (se 1 (by rfl) ⟨6292538, by rfl⟩ : syracuseStep 8390051 = 12585077) B12585077
theorem B1377715 : Blo 1224430 1377715 := bstep (se 1 (by rfl) ⟨1033286, by rfl⟩ : syracuseStep 1377715 = 2066573) B2066573
theorem B3491363 : Blo 1224430 3491363 := bstep (se 1 (by rfl) ⟨2618522, by rfl⟩ : syracuseStep 3491363 = 5237045) B5237045
theorem B1377859 : Blo 1224430 1377859 := bstep (se 1 (by rfl) ⟨1033394, by rfl⟩ : syracuseStep 1377859 = 2066789) B2066789
theorem B6202979 : Blo 1224430 6202979 := bstep (se 1 (by rfl) ⟨4652234, by rfl⟩ : syracuseStep 6202979 = 9304469) B9304469
theorem B1836659 : Blo 1224430 1836659 := bstep (se 1 (by rfl) ⟨1377494, by rfl⟩ : syracuseStep 1836659 = 2754989) B2754989
theorem B1549955 : Blo 1224430 1549955 := bstep (se 1 (by rfl) ⟨1162466, by rfl⟩ : syracuseStep 1549955 = 2324933) B2324933
theorem B1836689 : Blo 1224430 1836689 := bstep (se 2 (by rfl) ⟨688758, by rfl⟩ : syracuseStep 1836689 = 1377517) B1377517
theorem B1836707 : Blo 1224430 1836707 := bstep (se 1 (by rfl) ⟨1377530, by rfl⟩ : syracuseStep 1836707 = 2755061) B2755061
theorem B1836737 : Blo 1224430 1836737 := bstep (se 2 (by rfl) ⟨688776, by rfl⟩ : syracuseStep 1836737 = 1377553) B1377553
theorem B1656515 : Blo 1224430 1656515 := bstep (se 1 (by rfl) ⟨1242386, by rfl⟩ : syracuseStep 1656515 = 2484773) B2484773
theorem B2328259 : Blo 1224430 2328259 := bstep (se 1 (by rfl) ⟨1746194, by rfl⟩ : syracuseStep 2328259 = 3492389) B3492389
theorem B1836755 : Blo 1224430 1836755 := bstep (se 1 (by rfl) ⟨1377566, by rfl⟩ : syracuseStep 1836755 = 2755133) B2755133
theorem B1378003 : Blo 1224430 1378003 := bstep (se 1 (by rfl) ⟨1033502, by rfl⟩ : syracuseStep 1378003 = 2067005) B2067005
theorem B1836785 : Blo 1224430 1836785 := bstep (se 2 (by rfl) ⟨688794, by rfl⟩ : syracuseStep 1836785 = 1377589) B1377589
theorem B1836803 : Blo 1224430 1836803 := bstep (se 1 (by rfl) ⟨1377602, by rfl⟩ : syracuseStep 1836803 = 2755205) B2755205
theorem B5973773 : Blo 1224430 5973773 := bstep (se 3 (by rfl) ⟨1120082, by rfl⟩ : syracuseStep 5973773 = 2240165) B2240165
theorem B1836833 : Blo 1224430 1836833 := bstep (se 2 (by rfl) ⟨688812, by rfl⟩ : syracuseStep 1836833 = 1377625) B1377625
theorem B1836851 : Blo 1224430 1836851 := bstep (se 1 (by rfl) ⟨1377638, by rfl⟩ : syracuseStep 1836851 = 2755277) B2755277
theorem B4138829 : Blo 1224430 4138829 := bstep (se 3 (by rfl) ⟨776030, by rfl⟩ : syracuseStep 4138829 = 1552061) B1552061
theorem B1836881 : Blo 1224430 1836881 := bstep (se 2 (by rfl) ⟨688830, by rfl⟩ : syracuseStep 1836881 = 1377661) B1377661
theorem B1836899 : Blo 1224430 1836899 := bstep (se 1 (by rfl) ⟨1377674, by rfl⟩ : syracuseStep 1836899 = 2755349) B2755349
theorem B1378147 : Blo 1224430 1378147 := bstep (se 1 (by rfl) ⟨1033610, by rfl⟩ : syracuseStep 1378147 = 2067221) B2067221
theorem B1836929 : Blo 1224430 1836929 := bstep (se 2 (by rfl) ⟨688848, by rfl⟩ : syracuseStep 1836929 = 1377697) B1377697
theorem B4138883 : Blo 1224430 4138883 := bstep (se 1 (by rfl) ⟨3104162, by rfl⟩ : syracuseStep 4138883 = 6208325) B6208325
theorem B2066323 : Blo 1224430 2066323 := bstep (se 1 (by rfl) ⟨1549742, by rfl⟩ : syracuseStep 2066323 = 3099485) B3099485
theorem B1836947 : Blo 1224430 1836947 := bstep (se 1 (by rfl) ⟨1377710, by rfl⟩ : syracuseStep 1836947 = 2755421) B2755421
theorem B1836977 : Blo 1224430 1836977 := bstep (se 2 (by rfl) ⟨688866, by rfl⟩ : syracuseStep 1836977 = 1377733) B1377733
theorem B1836995 : Blo 1224430 1836995 := bstep (se 1 (by rfl) ⟨1377746, by rfl⟩ : syracuseStep 1836995 = 2755493) B2755493
theorem B1837025 : Blo 1224430 1837025 := bstep (se 2 (by rfl) ⟨688884, by rfl⟩ : syracuseStep 1837025 = 1377769) B1377769
theorem B1837043 : Blo 1224430 1837043 := bstep (se 1 (by rfl) ⟨1377782, by rfl⟩ : syracuseStep 1837043 = 2755565) B2755565
theorem B1378291 : Blo 1224430 1378291 := bstep (se 1 (by rfl) ⟨1033718, by rfl⟩ : syracuseStep 1378291 = 2067437) B2067437
theorem B1837073 : Blo 1224430 1837073 := bstep (se 2 (by rfl) ⟨688902, by rfl⟩ : syracuseStep 1837073 = 1377805) B1377805
theorem B2066465 : Blo 1224430 2066465 := bstep (se 2 (by rfl) ⟨774924, by rfl⟩ : syracuseStep 2066465 = 1549849) B1549849
theorem B1837091 : Blo 1224430 1837091 := bstep (se 1 (by rfl) ⟨1377818, by rfl⟩ : syracuseStep 1837091 = 2755637) B2755637
theorem B2615345 : Blo 1224430 2615345 := bstep (se 2 (by rfl) ⟨980754, by rfl⟩ : syracuseStep 2615345 = 1961509) B1961509
theorem B7850033 : Blo 1224430 7850033 := bstep (se 2 (by rfl) ⟨2943762, by rfl⟩ : syracuseStep 7850033 = 5887525) B5887525
theorem B1837121 : Blo 1224430 1837121 := bstep (se 2 (by rfl) ⟨688920, by rfl⟩ : syracuseStep 1837121 = 1377841) B1377841
theorem B1837139 : Blo 1224430 1837139 := bstep (se 1 (by rfl) ⟨1377854, by rfl⟩ : syracuseStep 1837139 = 2755709) B2755709
theorem B1837169 : Blo 1224430 1837169 := bstep (se 2 (by rfl) ⟨688938, by rfl⟩ : syracuseStep 1837169 = 1377877) B1377877
theorem B1837187 : Blo 1224430 1837187 := bstep (se 1 (by rfl) ⟨1377890, by rfl⟩ : syracuseStep 1837187 = 2755781) B2755781
theorem B1378435 : Blo 1224430 1378435 := bstep (se 1 (by rfl) ⟨1033826, by rfl⟩ : syracuseStep 1378435 = 2067653) B2067653
theorem B4139153 : Blo 1224430 4139153 := bstep (se 2 (by rfl) ⟨1552182, by rfl⟩ : syracuseStep 4139153 = 3104365) B3104365
theorem B2066593 : Blo 1224430 2066593 := bstep (se 2 (by rfl) ⟨774972, by rfl⟩ : syracuseStep 2066593 = 1549945) B1549945
theorem B1837217 : Blo 1224430 1837217 := bstep (se 2 (by rfl) ⟨688956, by rfl⟩ : syracuseStep 1837217 = 1377913) B1377913
theorem B1837235 : Blo 1224430 1837235 := bstep (se 1 (by rfl) ⟨1377926, by rfl⟩ : syracuseStep 1837235 = 2755853) B2755853
theorem B2066627 : Blo 1224430 2066627 := bstep (se 1 (by rfl) ⟨1549970, by rfl⟩ : syracuseStep 2066627 = 3099941) B3099941
theorem B2099395 : Blo 1224430 2099395 := bstep (se 1 (by rfl) ⟨1574546, by rfl⟩ : syracuseStep 2099395 = 3149093) B3149093
theorem B9308357 : Blo 1224430 9308357 := bstep (se 4 (by rfl) ⟨872658, by rfl⟩ : syracuseStep 9308357 = 1745317) B1745317
theorem B1837265 : Blo 1224430 1837265 := bstep (se 2 (by rfl) ⟨688974, by rfl⟩ : syracuseStep 1837265 = 1377949) B1377949
theorem B1837283 : Blo 1224430 1837283 := bstep (se 1 (by rfl) ⟨1377962, by rfl⟩ : syracuseStep 1837283 = 2755925) B2755925
theorem B1837313 : Blo 1224430 1837313 := bstep (se 2 (by rfl) ⟨688992, by rfl⟩ : syracuseStep 1837313 = 1377985) B1377985
theorem B1837331 : Blo 1224430 1837331 := bstep (se 1 (by rfl) ⟨1377998, by rfl⟩ : syracuseStep 1837331 = 2755997) B2755997
theorem B1378579 : Blo 1224430 1378579 := bstep (se 1 (by rfl) ⟨1033934, by rfl⟩ : syracuseStep 1378579 = 2067869) B2067869
theorem B1837361 : Blo 1224430 1837361 := bstep (se 2 (by rfl) ⟨689010, by rfl⟩ : syracuseStep 1837361 = 1378021) B1378021
theorem B2066755 : Blo 1224430 2066755 := bstep (se 1 (by rfl) ⟨1550066, by rfl⟩ : syracuseStep 2066755 = 3100133) B3100133
theorem B1837379 : Blo 1224430 1837379 := bstep (se 1 (by rfl) ⟨1378034, by rfl⟩ : syracuseStep 1837379 = 2756069) B2756069
theorem B1550659 : Blo 1224430 1550659 := bstep (se 1 (by rfl) ⟨1162994, by rfl⟩ : syracuseStep 1550659 = 2325989) B2325989
theorem B3492173 : Blo 1224430 3492173 := bstep (se 3 (by rfl) ⟨654782, by rfl⟩ : syracuseStep 3492173 = 1309565) B1309565
theorem B3189073 : Blo 1224430 3189073 := bstep (se 2 (by rfl) ⟨1195902, by rfl⟩ : syracuseStep 3189073 = 2391805) B2391805
theorem B1837409 : Blo 1224430 1837409 := bstep (se 2 (by rfl) ⟨689028, by rfl⟩ : syracuseStep 1837409 = 1378057) B1378057
theorem B1837427 : Blo 1224430 1837427 := bstep (se 1 (by rfl) ⟨1378070, by rfl⟩ : syracuseStep 1837427 = 2756141) B2756141
theorem B6203789 : Blo 1224430 6203789 := bstep (se 3 (by rfl) ⟨1163210, by rfl⟩ : syracuseStep 6203789 = 2326421) B2326421
theorem B4655501 : Blo 1224430 4655501 := bstep (se 3 (by rfl) ⟨872906, by rfl⟩ : syracuseStep 4655501 = 1745813) B1745813
theorem B1837457 : Blo 1224430 1837457 := bstep (se 2 (by rfl) ⟨689046, by rfl⟩ : syracuseStep 1837457 = 1378093) B1378093
theorem B1837475 : Blo 1224430 1837475 := bstep (se 1 (by rfl) ⟨1378106, by rfl⟩ : syracuseStep 1837475 = 2756213) B2756213
theorem B1550755 : Blo 1224430 1550755 := bstep (se 1 (by rfl) ⟨1163066, by rfl⟩ : syracuseStep 1550755 = 2326133) B2326133
theorem B1378723 : Blo 1224430 1378723 := bstep (se 1 (by rfl) ⟨1034042, by rfl⟩ : syracuseStep 1378723 = 2068085) B2068085
theorem B2484643 : Blo 1224430 2484643 := bstep (se 1 (by rfl) ⟨1863482, by rfl⟩ : syracuseStep 2484643 = 3726965) B3726965
theorem B1837505 : Blo 1224430 1837505 := bstep (se 2 (by rfl) ⟨689064, by rfl⟩ : syracuseStep 1837505 = 1378129) B1378129
theorem B2755025 : Blo 1224430 2755025 := bstep (se 2 (by rfl) ⟨1033134, by rfl⟩ : syracuseStep 2755025 = 2066269) B2066269
theorem B2066897 : Blo 1224430 2066897 := bstep (se 2 (by rfl) ⟨775086, by rfl⟩ : syracuseStep 2066897 = 1550173) B1550173
theorem B1837523 : Blo 1224430 1837523 := bstep (se 1 (by rfl) ⟨1378142, by rfl⟩ : syracuseStep 1837523 = 2756285) B2756285
theorem B2755043 : Blo 1224430 2755043 := bstep (se 1 (by rfl) ⟨2066282, by rfl⟩ : syracuseStep 2755043 = 4132565) B4132565
theorem B1837553 : Blo 1224430 1837553 := bstep (se 2 (by rfl) ⟨689082, by rfl⟩ : syracuseStep 1837553 = 1378165) B1378165
theorem B1837571 : Blo 1224430 1837571 := bstep (se 1 (by rfl) ⟨1378178, by rfl⟩ : syracuseStep 1837571 = 2756357) B2756357
theorem B3492355 : Blo 1224430 3492355 := bstep (se 1 (by rfl) ⟨2619266, by rfl⟩ : syracuseStep 3492355 = 5238533) B5238533
theorem B6711821 : Blo 1224430 6711821 := bstep (se 3 (by rfl) ⟨1258466, by rfl⟩ : syracuseStep 6711821 = 2516933) B2516933
theorem B1837601 : Blo 1224430 1837601 := bstep (se 2 (by rfl) ⟨689100, by rfl⟩ : syracuseStep 1837601 = 1378201) B1378201
theorem B1837619 : Blo 1224430 1837619 := bstep (se 1 (by rfl) ⟨1378214, by rfl⟩ : syracuseStep 1837619 = 2756429) B2756429
theorem B1378867 : Blo 1224430 1378867 := bstep (se 1 (by rfl) ⟨1034150, by rfl⟩ : syracuseStep 1378867 = 2068301) B2068301
theorem B2067025 : Blo 1224430 2067025 := bstep (se 2 (by rfl) ⟨775134, by rfl⟩ : syracuseStep 2067025 = 1550269) B1550269
theorem B1837649 : Blo 1224430 1837649 := bstep (se 2 (by rfl) ⟨689118, by rfl⟩ : syracuseStep 1837649 = 1378237) B1378237
theorem B1837667 : Blo 1224430 1837667 := bstep (se 1 (by rfl) ⟨1378250, by rfl⟩ : syracuseStep 1837667 = 2756501) B2756501
theorem B2067059 : Blo 1224430 2067059 := bstep (se 1 (by rfl) ⟨1550294, by rfl⟩ : syracuseStep 2067059 = 3100589) B3100589
theorem B1837697 : Blo 1224430 1837697 := bstep (se 2 (by rfl) ⟨689136, by rfl⟩ : syracuseStep 1837697 = 1378273) B1378273
theorem B1837715 : Blo 1224430 1837715 := bstep (se 1 (by rfl) ⟨1378286, by rfl⟩ : syracuseStep 1837715 = 2756573) B2756573
theorem B1837745 : Blo 1224430 1837745 := bstep (se 2 (by rfl) ⟨689154, by rfl⟩ : syracuseStep 1837745 = 1378309) B1378309
theorem B7269041 : Blo 1224430 7269041 := bstep (se 2 (by rfl) ⟨2725890, by rfl⟩ : syracuseStep 7269041 = 5451781) B5451781
theorem B1837763 : Blo 1224430 1837763 := bstep (se 1 (by rfl) ⟨1378322, by rfl⟩ : syracuseStep 1837763 = 2756645) B2756645
theorem B1379011 : Blo 1224430 1379011 := bstep (se 1 (by rfl) ⟨1034258, by rfl⟩ : syracuseStep 1379011 = 2068517) B2068517
theorem B1837793 : Blo 1224430 1837793 := bstep (se 2 (by rfl) ⟨689172, by rfl⟩ : syracuseStep 1837793 = 1378345) B1378345
theorem B2755313 : Blo 1224430 2755313 := bstep (se 2 (by rfl) ⟨1033242, by rfl⟩ : syracuseStep 2755313 = 2066485) B2066485
theorem B2067187 : Blo 1224430 2067187 := bstep (se 1 (by rfl) ⟨1550390, by rfl⟩ : syracuseStep 2067187 = 3100781) B3100781
theorem B1837811 : Blo 1224430 1837811 := bstep (se 1 (by rfl) ⟨1378358, by rfl⟩ : syracuseStep 1837811 = 2756717) B2756717
theorem B2755331 : Blo 1224430 2755331 := bstep (se 1 (by rfl) ⟨2066498, by rfl⟩ : syracuseStep 2755331 = 4132997) B4132997
theorem B1837841 : Blo 1224430 1837841 := bstep (se 2 (by rfl) ⟨689190, by rfl⟩ : syracuseStep 1837841 = 1378381) B1378381
theorem B1837859 : Blo 1224430 1837859 := bstep (se 1 (by rfl) ⟨1378394, by rfl⟩ : syracuseStep 1837859 = 2756789) B2756789
theorem B1837889 : Blo 1224430 1837889 := bstep (se 2 (by rfl) ⟨689208, by rfl⟩ : syracuseStep 1837889 = 1378417) B1378417
theorem B2616131 : Blo 1224430 2616131 := bstep (se 1 (by rfl) ⟨1962098, by rfl⟩ : syracuseStep 2616131 = 3924197) B3924197
theorem B1837907 : Blo 1224430 1837907 := bstep (se 1 (by rfl) ⟨1378430, by rfl⟩ : syracuseStep 1837907 = 2756861) B2756861
theorem B1379155 : Blo 1224430 1379155 := bstep (se 1 (by rfl) ⟨1034366, by rfl⟩ : syracuseStep 1379155 = 2068733) B2068733
theorem B3099505 : Blo 1224430 3099505 := bstep (se 2 (by rfl) ⟨1162314, by rfl⟩ : syracuseStep 3099505 = 2324629) B2324629
theorem B1837937 : Blo 1224430 1837937 := bstep (se 2 (by rfl) ⟨689226, by rfl⟩ : syracuseStep 1837937 = 1378453) B1378453
theorem B2067329 : Blo 1224430 2067329 := bstep (se 2 (by rfl) ⟨775248, by rfl⟩ : syracuseStep 2067329 = 1550497) B1550497
theorem B1837955 : Blo 1224430 1837955 := bstep (se 1 (by rfl) ⟨1378466, by rfl⟩ : syracuseStep 1837955 = 2756933) B2756933
theorem B1551251 : Blo 1224430 1551251 := bstep (se 1 (by rfl) ⟨1163438, by rfl⟩ : syracuseStep 1551251 = 2326877) B2326877
theorem B1837985 : Blo 1224430 1837985 := bstep (se 2 (by rfl) ⟨689244, by rfl⟩ : syracuseStep 1837985 = 1378489) B1378489
theorem B1838003 : Blo 1224430 1838003 := bstep (se 1 (by rfl) ⟨1378502, by rfl⟩ : syracuseStep 1838003 = 2757005) B2757005
theorem B1838033 : Blo 1224430 1838033 := bstep (se 2 (by rfl) ⟨689262, by rfl⟩ : syracuseStep 1838033 = 1378525) B1378525
theorem B1838051 : Blo 1224430 1838051 := bstep (se 1 (by rfl) ⟨1378538, by rfl⟩ : syracuseStep 1838051 = 2757077) B2757077
theorem B1379299 : Blo 1224430 1379299 := bstep (se 1 (by rfl) ⟨1034474, by rfl⟩ : syracuseStep 1379299 = 2068949) B2068949
theorem B2067457 : Blo 1224430 2067457 := bstep (se 2 (by rfl) ⟨775296, by rfl⟩ : syracuseStep 2067457 = 1550593) B1550593
theorem B1838081 : Blo 1224430 1838081 := bstep (se 2 (by rfl) ⟨689280, by rfl⟩ : syracuseStep 1838081 = 1378561) B1378561
theorem B2755601 : Blo 1224430 2755601 := bstep (se 2 (by rfl) ⟨1033350, by rfl⟩ : syracuseStep 2755601 = 2066701) B2066701
theorem B1838099 : Blo 1224430 1838099 := bstep (se 1 (by rfl) ⟨1378574, by rfl⟩ : syracuseStep 1838099 = 2757149) B2757149
theorem B2755619 : Blo 1224430 2755619 := bstep (se 1 (by rfl) ⟨2066714, by rfl⟩ : syracuseStep 2755619 = 4133429) B4133429
theorem B2067491 : Blo 1224430 2067491 := bstep (se 1 (by rfl) ⟨1550618, by rfl⟩ : syracuseStep 2067491 = 3101237) B3101237
theorem B1838129 : Blo 1224430 1838129 := bstep (se 2 (by rfl) ⟨689298, by rfl⟩ : syracuseStep 1838129 = 1378597) B1378597
theorem B1838147 : Blo 1224430 1838147 := bstep (se 1 (by rfl) ⟨1378610, by rfl⟩ : syracuseStep 1838147 = 2757221) B2757221
theorem B2796611 : Blo 1224430 2796611 := bstep (se 1 (by rfl) ⟨2097458, by rfl⟩ : syracuseStep 2796611 = 4194917) B4194917
theorem B1838177 : Blo 1224430 1838177 := bstep (se 2 (by rfl) ⟨689316, by rfl⟩ : syracuseStep 1838177 = 1378633) B1378633
theorem B1838195 : Blo 1224430 1838195 := bstep (se 1 (by rfl) ⟨1378646, by rfl⟩ : syracuseStep 1838195 = 2757293) B2757293
theorem B1379443 : Blo 1224430 1379443 := bstep (se 1 (by rfl) ⟨1034582, by rfl⟩ : syracuseStep 1379443 = 2069165) B2069165
theorem B3099779 : Blo 1224430 3099779 := bstep (se 1 (by rfl) ⟨2324834, by rfl⟩ : syracuseStep 3099779 = 4649669) B4649669
theorem B1838225 : Blo 1224430 1838225 := bstep (se 2 (by rfl) ⟨689334, by rfl⟩ : syracuseStep 1838225 = 1378669) B1378669
theorem B2067619 : Blo 1224430 2067619 := bstep (se 1 (by rfl) ⟨1550714, by rfl⟩ : syracuseStep 2067619 = 3101429) B3101429
theorem B1838243 : Blo 1224430 1838243 := bstep (se 1 (by rfl) ⟨1378682, by rfl⟩ : syracuseStep 1838243 = 2757365) B2757365
theorem B4656305 : Blo 1224430 4656305 := bstep (se 2 (by rfl) ⟨1746114, by rfl⟩ : syracuseStep 4656305 = 3492229) B3492229
theorem B1838273 : Blo 1224430 1838273 := bstep (se 2 (by rfl) ⟨689352, by rfl⟩ : syracuseStep 1838273 = 1378705) B1378705
theorem B1838291 : Blo 1224430 1838291 := bstep (se 1 (by rfl) ⟨1378718, by rfl⟩ : syracuseStep 1838291 = 2757437) B2757437
theorem B11775203 : Blo 1224430 11775203 := bstep (se 1 (by rfl) ⟨8831402, by rfl⟩ : syracuseStep 11775203 = 17662805) B17662805
theorem B1838321 : Blo 1224430 1838321 := bstep (se 2 (by rfl) ⟨689370, by rfl⟩ : syracuseStep 1838321 = 1378741) B1378741
theorem B1838339 : Blo 1224430 1838339 := bstep (se 1 (by rfl) ⟨1378754, by rfl⟩ : syracuseStep 1838339 = 2757509) B2757509
theorem B1379587 : Blo 1224430 1379587 := bstep (se 1 (by rfl) ⟨1034690, by rfl⟩ : syracuseStep 1379587 = 2069381) B2069381
theorem B1838369 : Blo 1224430 1838369 := bstep (se 2 (by rfl) ⟨689388, by rfl⟩ : syracuseStep 1838369 = 1378777) B1378777
theorem B2755889 : Blo 1224430 2755889 := bstep (se 2 (by rfl) ⟨1033458, by rfl⟩ : syracuseStep 2755889 = 2066917) B2066917
theorem B4967729 : Blo 1224430 4967729 := bstep (se 2 (by rfl) ⟨1862898, by rfl⟩ : syracuseStep 4967729 = 3725797) B3725797
theorem B2067761 : Blo 1224430 2067761 := bstep (se 2 (by rfl) ⟨775410, by rfl⟩ : syracuseStep 2067761 = 1550821) B1550821
theorem B1838387 : Blo 1224430 1838387 := bstep (se 1 (by rfl) ⟨1378790, by rfl⟩ : syracuseStep 1838387 = 2757581) B2757581
theorem B3099971 : Blo 1224430 3099971 := bstep (se 1 (by rfl) ⟨2324978, by rfl⟩ : syracuseStep 3099971 = 4649957) B4649957
theorem B2755907 : Blo 1224430 2755907 := bstep (se 1 (by rfl) ⟨2066930, by rfl⟩ : syracuseStep 2755907 = 4133861) B4133861
theorem B1838417 : Blo 1224430 1838417 := bstep (se 2 (by rfl) ⟨689406, by rfl⟩ : syracuseStep 1838417 = 1378813) B1378813
theorem B1838435 : Blo 1224430 1838435 := bstep (se 1 (by rfl) ⟨1378826, by rfl⟩ : syracuseStep 1838435 = 2757653) B2757653
theorem B4189553 : Blo 1224430 4189553 := bstep (se 2 (by rfl) ⟨1571082, by rfl⟩ : syracuseStep 4189553 = 3142165) B3142165
theorem B1838465 : Blo 1224430 1838465 := bstep (se 2 (by rfl) ⟨689424, by rfl⟩ : syracuseStep 1838465 = 1378849) B1378849
theorem B1838483 : Blo 1224430 1838483 := bstep (se 1 (by rfl) ⟨1378862, by rfl⟩ : syracuseStep 1838483 = 2757725) B2757725
theorem B1379731 : Blo 1224430 1379731 := bstep (se 1 (by rfl) ⟨1034798, by rfl⟩ : syracuseStep 1379731 = 2069597) B2069597
theorem B2067889 : Blo 1224430 2067889 := bstep (se 2 (by rfl) ⟨775458, by rfl⟩ : syracuseStep 2067889 = 1550917) B1550917
theorem B1838513 : Blo 1224430 1838513 := bstep (se 2 (by rfl) ⟨689442, by rfl⟩ : syracuseStep 1838513 = 1378885) B1378885
theorem B1838531 : Blo 1224430 1838531 := bstep (se 1 (by rfl) ⟨1378898, by rfl⟩ : syracuseStep 1838531 = 2757797) B2757797
theorem B2067923 : Blo 1224430 2067923 := bstep (se 1 (by rfl) ⟨1550942, by rfl⟩ : syracuseStep 2067923 = 3101885) B3101885
theorem B1838561 : Blo 1224430 1838561 := bstep (se 2 (by rfl) ⟨689460, by rfl⟩ : syracuseStep 1838561 = 1378921) B1378921
theorem B1838579 : Blo 1224430 1838579 := bstep (se 1 (by rfl) ⟨1378934, by rfl⟩ : syracuseStep 1838579 = 2757869) B2757869
theorem B6974981 : Blo 1224430 6974981 := bstep (se 4 (by rfl) ⟨653904, by rfl⟩ : syracuseStep 6974981 = 1307809) B1307809
theorem B1838609 : Blo 1224430 1838609 := bstep (se 2 (by rfl) ⟨689478, by rfl⟩ : syracuseStep 1838609 = 1378957) B1378957
theorem B1838627 : Blo 1224430 1838627 := bstep (se 1 (by rfl) ⟨1378970, by rfl⟩ : syracuseStep 1838627 = 2757941) B2757941
theorem B1838657 : Blo 1224430 1838657 := bstep (se 2 (by rfl) ⟨689496, by rfl⟩ : syracuseStep 1838657 = 1378993) B1378993
theorem B2756177 : Blo 1224430 2756177 := bstep (se 2 (by rfl) ⟨1033566, by rfl⟩ : syracuseStep 2756177 = 2067133) B2067133
theorem B2068051 : Blo 1224430 2068051 := bstep (se 1 (by rfl) ⟨1551038, by rfl⟩ : syracuseStep 2068051 = 3102077) B3102077
theorem B1838675 : Blo 1224430 1838675 := bstep (se 1 (by rfl) ⟨1379006, by rfl⟩ : syracuseStep 1838675 = 2758013) B2758013
theorem B1551955 : Blo 1224430 1551955 := bstep (se 1 (by rfl) ⟨1163966, by rfl⟩ : syracuseStep 1551955 = 2327933) B2327933
theorem B2756195 : Blo 1224430 2756195 := bstep (se 1 (by rfl) ⟨2067146, by rfl⟩ : syracuseStep 2756195 = 4134293) B4134293
theorem B1838705 : Blo 1224430 1838705 := bstep (se 2 (by rfl) ⟨689514, by rfl⟩ : syracuseStep 1838705 = 1379029) B1379029
theorem B1838723 : Blo 1224430 1838723 := bstep (se 1 (by rfl) ⟨1379042, by rfl⟩ : syracuseStep 1838723 = 2758085) B2758085
theorem B1838753 : Blo 1224430 1838753 := bstep (se 2 (by rfl) ⟨689532, by rfl⟩ : syracuseStep 1838753 = 1379065) B1379065
theorem B1838771 : Blo 1224430 1838771 := bstep (se 1 (by rfl) ⟨1379078, by rfl⟩ : syracuseStep 1838771 = 2758157) B2758157
theorem B1552051 : Blo 1224430 1552051 := bstep (se 1 (by rfl) ⟨1164038, by rfl⟩ : syracuseStep 1552051 = 2328077) B2328077
theorem B15699653 : Blo 1224430 15699653 := bstep (se 4 (by rfl) ⟨1471842, by rfl⟩ : syracuseStep 15699653 = 2943685) B2943685
theorem B7073477 : Blo 1224430 7073477 := bstep (se 4 (by rfl) ⟨663138, by rfl⟩ : syracuseStep 7073477 = 1326277) B1326277
theorem B7851725 : Blo 1224430 7851725 := bstep (se 3 (by rfl) ⟨1472198, by rfl⟩ : syracuseStep 7851725 = 2944397) B2944397
theorem B1838801 : Blo 1224430 1838801 := bstep (se 2 (by rfl) ⟨689550, by rfl⟩ : syracuseStep 1838801 = 1379101) B1379101
theorem B2068193 : Blo 1224430 2068193 := bstep (se 2 (by rfl) ⟨775572, by rfl⟩ : syracuseStep 2068193 = 1551145) B1551145
theorem B1838819 : Blo 1224430 1838819 := bstep (se 1 (by rfl) ⟨1379114, by rfl⟩ : syracuseStep 1838819 = 2758229) B2758229
theorem B1224435 : Blo 1224430 1224435 := bstep (se 1 (by rfl) ⟨918326, by rfl⟩ : syracuseStep 1224435 = 1836653) B1836653
theorem B1838849 : Blo 1224430 1838849 := bstep (se 2 (by rfl) ⟨689568, by rfl⟩ : syracuseStep 1838849 = 1379137) B1379137
theorem B1224451 : Blo 1224430 1224451 := bstep (se 1 (by rfl) ⟨918338, by rfl⟩ : syracuseStep 1224451 = 1836677) B1836677
theorem B3927811 : Blo 1224430 3927811 := bstep (se 1 (by rfl) ⟨2945858, by rfl⟩ : syracuseStep 3927811 = 5891717) B5891717
theorem B10465037 : Blo 1224430 10465037 := bstep (se 3 (by rfl) ⟨1962194, by rfl⟩ : syracuseStep 10465037 = 3924389) B3924389
theorem B2617105 : Blo 1224430 2617105 := bstep (se 2 (by rfl) ⟨981414, by rfl⟩ : syracuseStep 2617105 = 1962829) B1962829
theorem B1224467 : Blo 1224430 1224467 := bstep (se 1 (by rfl) ⟨918350, by rfl⟩ : syracuseStep 1224467 = 1836701) B1836701
theorem B1838867 : Blo 1224430 1838867 := bstep (se 1 (by rfl) ⟨1379150, by rfl⟩ : syracuseStep 1838867 = 2758301) B2758301
theorem B1224483 : Blo 1224430 1224483 := bstep (se 1 (by rfl) ⟨918362, by rfl⟩ : syracuseStep 1224483 = 1836725) B1836725
theorem B3977009 : Blo 1224430 3977009 := bstep (se 2 (by rfl) ⟨1491378, by rfl⟩ : syracuseStep 3977009 = 2982757) B2982757
theorem B1838897 : Blo 1224430 1838897 := bstep (se 2 (by rfl) ⟨689586, by rfl⟩ : syracuseStep 1838897 = 1379173) B1379173
theorem B1224499 : Blo 1224430 1224499 := bstep (se 1 (by rfl) ⟨918374, by rfl⟩ : syracuseStep 1224499 = 1836749) B1836749
theorem B1224515 : Blo 1224430 1224515 := bstep (se 1 (by rfl) ⟨918386, by rfl⟩ : syracuseStep 1224515 = 1836773) B1836773
theorem B1838915 : Blo 1224430 1838915 := bstep (se 1 (by rfl) ⟨1379186, by rfl⟩ : syracuseStep 1838915 = 2758373) B2758373
theorem B1224531 : Blo 1224430 1224531 := bstep (se 1 (by rfl) ⟨918398, by rfl⟩ : syracuseStep 1224531 = 1836797) B1836797
theorem B2068321 : Blo 1224430 2068321 := bstep (se 2 (by rfl) ⟨775620, by rfl⟩ : syracuseStep 2068321 = 1551241) B1551241
theorem B1838945 : Blo 1224430 1838945 := bstep (se 2 (by rfl) ⟨689604, by rfl⟩ : syracuseStep 1838945 = 1379209) B1379209
theorem B1224547 : Blo 1224430 1224547 := bstep (se 1 (by rfl) ⟨918410, by rfl⟩ : syracuseStep 1224547 = 1836821) B1836821
theorem B3313507 : Blo 1224430 3313507 := bstep (se 1 (by rfl) ⟨2485130, by rfl⟩ : syracuseStep 3313507 = 4970261) B4970261
theorem B2756465 : Blo 1224430 2756465 := bstep (se 2 (by rfl) ⟨1033674, by rfl⟩ : syracuseStep 2756465 = 2067349) B2067349
theorem B1224563 : Blo 1224430 1224563 := bstep (se 1 (by rfl) ⟨918422, by rfl⟩ : syracuseStep 1224563 = 1836845) B1836845
theorem B1838963 : Blo 1224430 1838963 := bstep (se 1 (by rfl) ⟨1379222, by rfl⟩ : syracuseStep 1838963 = 2758445) B2758445
theorem B1224579 : Blo 1224430 1224579 := bstep (se 1 (by rfl) ⟨918434, by rfl⟩ : syracuseStep 1224579 = 1836869) B1836869
theorem B2756483 : Blo 1224430 2756483 := bstep (se 1 (by rfl) ⟨2067362, by rfl⟩ : syracuseStep 2756483 = 4134725) B4134725
theorem B2068355 : Blo 1224430 2068355 := bstep (se 1 (by rfl) ⟨1551266, by rfl⟩ : syracuseStep 2068355 = 3102533) B3102533
theorem B3313549 : Blo 1224430 3313549 := bstep (se 3 (by rfl) ⟨621290, by rfl⟩ : syracuseStep 3313549 = 1242581) B1242581
theorem B1838993 : Blo 1224430 1838993 := bstep (se 2 (by rfl) ⟨689622, by rfl⟩ : syracuseStep 1838993 = 1379245) B1379245
theorem B1224595 : Blo 1224430 1224595 := bstep (se 1 (by rfl) ⟨918446, by rfl⟩ : syracuseStep 1224595 = 1836893) B1836893
theorem B1224611 : Blo 1224430 1224611 := bstep (se 1 (by rfl) ⟨918458, by rfl⟩ : syracuseStep 1224611 = 1836917) B1836917
theorem B1839011 : Blo 1224430 1839011 := bstep (se 1 (by rfl) ⟨1379258, by rfl⟩ : syracuseStep 1839011 = 2758517) B2758517
theorem B4132781 : Blo 1224430 4132781 := bstep (se 3 (by rfl) ⟨774896, by rfl⟩ : syracuseStep 4132781 = 1549793) B1549793
theorem B1224627 : Blo 1224430 1224627 := bstep (se 1 (by rfl) ⟨918470, by rfl⟩ : syracuseStep 1224627 = 1836941) B1836941
theorem B1839041 : Blo 1224430 1839041 := bstep (se 2 (by rfl) ⟨689640, by rfl⟩ : syracuseStep 1839041 = 1379281) B1379281
theorem B1224643 : Blo 1224430 1224643 := bstep (se 1 (by rfl) ⟨918482, by rfl⟩ : syracuseStep 1224643 = 1836965) B1836965
theorem B1224659 : Blo 1224430 1224659 := bstep (se 1 (by rfl) ⟨918494, by rfl⟩ : syracuseStep 1224659 = 1836989) B1836989
theorem B1839059 : Blo 1224430 1839059 := bstep (se 1 (by rfl) ⟨1379294, by rfl⟩ : syracuseStep 1839059 = 2758589) B2758589
theorem B4132835 : Blo 1224430 4132835 := bstep (se 1 (by rfl) ⟨3099626, by rfl⟩ : syracuseStep 4132835 = 6199253) B6199253
theorem B1224675 : Blo 1224430 1224675 := bstep (se 1 (by rfl) ⟨918506, by rfl⟩ : syracuseStep 1224675 = 1837013) B1837013
theorem B11186147 : Blo 1224430 11186147 := bstep (se 1 (by rfl) ⟨8389610, by rfl⟩ : syracuseStep 11186147 = 16779221) B16779221
theorem B1839089 : Blo 1224430 1839089 := bstep (se 2 (by rfl) ⟨689658, by rfl⟩ : syracuseStep 1839089 = 1379317) B1379317
theorem B1224691 : Blo 1224430 1224691 := bstep (se 1 (by rfl) ⟨918518, by rfl⟩ : syracuseStep 1224691 = 1837037) B1837037
theorem B1224707 : Blo 1224430 1224707 := bstep (se 1 (by rfl) ⟨918530, by rfl⟩ : syracuseStep 1224707 = 1837061) B1837061
theorem B2068483 : Blo 1224430 2068483 := bstep (se 1 (by rfl) ⟨1551362, by rfl⟩ : syracuseStep 2068483 = 3102725) B3102725
theorem B1839107 : Blo 1224430 1839107 := bstep (se 1 (by rfl) ⟨1379330, by rfl⟩ : syracuseStep 1839107 = 2758661) B2758661
theorem B2617361 : Blo 1224430 2617361 := bstep (se 2 (by rfl) ⟨981510, by rfl⟩ : syracuseStep 2617361 = 1963021) B1963021
theorem B1224723 : Blo 1224430 1224723 := bstep (se 1 (by rfl) ⟨918542, by rfl⟩ : syracuseStep 1224723 = 1837085) B1837085
theorem B1839137 : Blo 1224430 1839137 := bstep (se 2 (by rfl) ⟨689676, by rfl⟩ : syracuseStep 1839137 = 1379353) B1379353
theorem B1224739 : Blo 1224430 1224739 := bstep (se 1 (by rfl) ⟨918554, by rfl⟩ : syracuseStep 1224739 = 1837109) B1837109
theorem B6983729 : Blo 1224430 6983729 := bstep (se 2 (by rfl) ⟨2618898, by rfl⟩ : syracuseStep 6983729 = 5237797) B5237797
theorem B1224755 : Blo 1224430 1224755 := bstep (se 1 (by rfl) ⟨918566, by rfl⟩ : syracuseStep 1224755 = 1837133) B1837133
theorem B1839155 : Blo 1224430 1839155 := bstep (se 1 (by rfl) ⟨1379366, by rfl⟩ : syracuseStep 1839155 = 2758733) B2758733
theorem B1224771 : Blo 1224430 1224771 := bstep (se 1 (by rfl) ⟨918578, by rfl⟩ : syracuseStep 1224771 = 1837157) B1837157
theorem B1839185 : Blo 1224430 1839185 := bstep (se 2 (by rfl) ⟨689694, by rfl⟩ : syracuseStep 1839185 = 1379389) B1379389
theorem B1224787 : Blo 1224430 1224787 := bstep (se 1 (by rfl) ⟨918590, by rfl⟩ : syracuseStep 1224787 = 1837181) B1837181
theorem B1224803 : Blo 1224430 1224803 := bstep (se 1 (by rfl) ⟨918602, by rfl⟩ : syracuseStep 1224803 = 1837205) B1837205
theorem B1839203 : Blo 1224430 1839203 := bstep (se 1 (by rfl) ⟨1379402, by rfl⟩ : syracuseStep 1839203 = 2758805) B2758805
theorem B1224819 : Blo 1224430 1224819 := bstep (se 1 (by rfl) ⟨918614, by rfl⟩ : syracuseStep 1224819 = 1837229) B1837229
theorem B1839233 : Blo 1224430 1839233 := bstep (se 2 (by rfl) ⟨689712, by rfl⟩ : syracuseStep 1839233 = 1379425) B1379425
theorem B1224835 : Blo 1224430 1224835 := bstep (se 1 (by rfl) ⟨918626, by rfl⟩ : syracuseStep 1224835 = 1837253) B1837253
theorem B2756753 : Blo 1224430 2756753 := bstep (se 2 (by rfl) ⟨1033782, by rfl⟩ : syracuseStep 2756753 = 2067565) B2067565
theorem B2068625 : Blo 1224430 2068625 := bstep (se 2 (by rfl) ⟨775734, by rfl⟩ : syracuseStep 2068625 = 1551469) B1551469
theorem B1224851 : Blo 1224430 1224851 := bstep (se 1 (by rfl) ⟨918638, by rfl⟩ : syracuseStep 1224851 = 1837277) B1837277
theorem B1839251 : Blo 1224430 1839251 := bstep (se 1 (by rfl) ⟨1379438, by rfl⟩ : syracuseStep 1839251 = 2758877) B2758877
theorem B1224867 : Blo 1224430 1224867 := bstep (se 1 (by rfl) ⟨918650, by rfl⟩ : syracuseStep 1224867 = 1837301) B1837301
theorem B2756771 : Blo 1224430 2756771 := bstep (se 1 (by rfl) ⟨2067578, by rfl⟩ : syracuseStep 2756771 = 4135157) B4135157
theorem B6975665 : Blo 1224430 6975665 := bstep (se 2 (by rfl) ⟨2615874, by rfl⟩ : syracuseStep 6975665 = 5231749) B5231749
theorem B1839281 : Blo 1224430 1839281 := bstep (se 2 (by rfl) ⟨689730, by rfl⟩ : syracuseStep 1839281 = 1379461) B1379461
theorem B1224883 : Blo 1224430 1224883 := bstep (se 1 (by rfl) ⟨918662, by rfl⟩ : syracuseStep 1224883 = 1837325) B1837325
theorem B1224899 : Blo 1224430 1224899 := bstep (se 1 (by rfl) ⟨918674, by rfl⟩ : syracuseStep 1224899 = 1837349) B1837349
theorem B1839299 : Blo 1224430 1839299 := bstep (se 1 (by rfl) ⟨1379474, by rfl⟩ : syracuseStep 1839299 = 2758949) B2758949
theorem B1224915 : Blo 1224430 1224915 := bstep (se 1 (by rfl) ⟨918686, by rfl⟩ : syracuseStep 1224915 = 1837373) B1837373
theorem B1839329 : Blo 1224430 1839329 := bstep (se 2 (by rfl) ⟨689748, by rfl⟩ : syracuseStep 1839329 = 1379497) B1379497
theorem B1224931 : Blo 1224430 1224931 := bstep (se 1 (by rfl) ⟨918698, by rfl⟩ : syracuseStep 1224931 = 1837397) B1837397
theorem B4714723 : Blo 1224430 4714723 := bstep (se 1 (by rfl) ⟨3536042, by rfl⟩ : syracuseStep 4714723 = 7072085) B7072085
theorem B4133105 : Blo 1224430 4133105 := bstep (se 2 (by rfl) ⟨1549914, by rfl⟩ : syracuseStep 4133105 = 3099829) B3099829
theorem B3100913 : Blo 1224430 3100913 := bstep (se 2 (by rfl) ⟨1162842, by rfl⟩ : syracuseStep 3100913 = 2325685) B2325685
theorem B1224947 : Blo 1224430 1224947 := bstep (se 1 (by rfl) ⟨918710, by rfl⟩ : syracuseStep 1224947 = 1837421) B1837421
theorem B1962227 : Blo 1224430 1962227 := bstep (se 1 (by rfl) ⟨1471670, by rfl⟩ : syracuseStep 1962227 = 2943341) B2943341
theorem B1839347 : Blo 1224430 1839347 := bstep (se 1 (by rfl) ⟨1379510, by rfl⟩ : syracuseStep 1839347 = 2759021) B2759021
theorem B1224963 : Blo 1224430 1224963 := bstep (se 1 (by rfl) ⟨918722, by rfl⟩ : syracuseStep 1224963 = 1837445) B1837445
theorem B2068753 : Blo 1224430 2068753 := bstep (se 2 (by rfl) ⟨775782, by rfl⟩ : syracuseStep 2068753 = 1551565) B1551565
theorem B1224979 : Blo 1224430 1224979 := bstep (se 1 (by rfl) ⟨918734, by rfl⟩ : syracuseStep 1224979 = 1837469) B1837469
theorem B1839377 : Blo 1224430 1839377 := bstep (se 2 (by rfl) ⟨689766, by rfl⟩ : syracuseStep 1839377 = 1379533) B1379533
theorem B1224995 : Blo 1224430 1224995 := bstep (se 1 (by rfl) ⟨918746, by rfl⟩ : syracuseStep 1224995 = 1837493) B1837493
theorem B3100963 : Blo 1224430 3100963 := bstep (se 1 (by rfl) ⟨2325722, by rfl⟩ : syracuseStep 3100963 = 4651445) B4651445
theorem B1839395 : Blo 1224430 1839395 := bstep (se 1 (by rfl) ⟨1379546, by rfl⟩ : syracuseStep 1839395 = 2759093) B2759093
theorem B1225011 : Blo 1224430 1225011 := bstep (se 1 (by rfl) ⟨918758, by rfl⟩ : syracuseStep 1225011 = 1837517) B1837517
theorem B2068787 : Blo 1224430 2068787 := bstep (se 1 (by rfl) ⟨1551590, by rfl⟩ : syracuseStep 2068787 = 3103181) B3103181
theorem B1839425 : Blo 1224430 1839425 := bstep (se 2 (by rfl) ⟨689784, by rfl⟩ : syracuseStep 1839425 = 1379569) B1379569
theorem B1225027 : Blo 1224430 1225027 := bstep (se 1 (by rfl) ⟨918770, by rfl⟩ : syracuseStep 1225027 = 1837541) B1837541
theorem B1225043 : Blo 1224430 1225043 := bstep (se 1 (by rfl) ⟨918782, by rfl⟩ : syracuseStep 1225043 = 1837565) B1837565
theorem B1864019 : Blo 1224430 1864019 := bstep (se 1 (by rfl) ⟨1398014, by rfl⟩ : syracuseStep 1864019 = 2796029) B2796029
theorem B1839443 : Blo 1224430 1839443 := bstep (se 1 (by rfl) ⟨1379582, by rfl⟩ : syracuseStep 1839443 = 2759165) B2759165
theorem B1225059 : Blo 1224430 1225059 := bstep (se 1 (by rfl) ⟨918794, by rfl⟩ : syracuseStep 1225059 = 1837589) B1837589
theorem B1839473 : Blo 1224430 1839473 := bstep (se 2 (by rfl) ⟨689802, by rfl⟩ : syracuseStep 1839473 = 1379605) B1379605
theorem B1225075 : Blo 1224430 1225075 := bstep (se 1 (by rfl) ⟨918806, by rfl⟩ : syracuseStep 1225075 = 1837613) B1837613
theorem B1225091 : Blo 1224430 1225091 := bstep (se 1 (by rfl) ⟨918818, by rfl⟩ : syracuseStep 1225091 = 1837637) B1837637
theorem B1839491 : Blo 1224430 1839491 := bstep (se 1 (by rfl) ⟨1379618, by rfl⟩ : syracuseStep 1839491 = 2759237) B2759237
theorem B1225107 : Blo 1224430 1225107 := bstep (se 1 (by rfl) ⟨918830, by rfl⟩ : syracuseStep 1225107 = 1837661) B1837661
theorem B1839521 : Blo 1224430 1839521 := bstep (se 2 (by rfl) ⟨689820, by rfl⟩ : syracuseStep 1839521 = 1379641) B1379641
theorem B5886371 : Blo 1224430 5886371 := bstep (se 1 (by rfl) ⟨4414778, by rfl⟩ : syracuseStep 5886371 = 8829557) B8829557
theorem B1225123 : Blo 1224430 1225123 := bstep (se 1 (by rfl) ⟨918842, by rfl⟩ : syracuseStep 1225123 = 1837685) B1837685
theorem B3101105 : Blo 1224430 3101105 := bstep (se 2 (by rfl) ⟨1162914, by rfl⟩ : syracuseStep 3101105 = 2325829) B2325829
theorem B1225139 : Blo 1224430 1225139 := bstep (se 1 (by rfl) ⟨918854, by rfl⟩ : syracuseStep 1225139 = 1837709) B1837709
theorem B2757041 : Blo 1224430 2757041 := bstep (se 2 (by rfl) ⟨1033890, by rfl⟩ : syracuseStep 2757041 = 2067781) B2067781
theorem B2068915 : Blo 1224430 2068915 := bstep (se 1 (by rfl) ⟨1551686, by rfl⟩ : syracuseStep 2068915 = 3103373) B3103373
theorem B1839539 : Blo 1224430 1839539 := bstep (se 1 (by rfl) ⟨1379654, by rfl⟩ : syracuseStep 1839539 = 2759309) B2759309
theorem B1225155 : Blo 1224430 1225155 := bstep (se 1 (by rfl) ⟨918866, by rfl⟩ : syracuseStep 1225155 = 1837733) B1837733
theorem B2757059 : Blo 1224430 2757059 := bstep (se 1 (by rfl) ⟨2067794, by rfl⟩ : syracuseStep 2757059 = 4135589) B4135589
theorem B1839569 : Blo 1224430 1839569 := bstep (se 2 (by rfl) ⟨689838, by rfl⟩ : syracuseStep 1839569 = 1379677) B1379677
theorem B1225171 : Blo 1224430 1225171 := bstep (se 1 (by rfl) ⟨918878, by rfl⟩ : syracuseStep 1225171 = 1837757) B1837757
theorem B1225187 : Blo 1224430 1225187 := bstep (se 1 (by rfl) ⟨918890, by rfl⟩ : syracuseStep 1225187 = 1837781) B1837781
theorem B1839587 : Blo 1224430 1839587 := bstep (se 1 (by rfl) ⟨1379690, by rfl⟩ : syracuseStep 1839587 = 2759381) B2759381
theorem B1225203 : Blo 1224430 1225203 := bstep (se 1 (by rfl) ⟨918902, by rfl⟩ : syracuseStep 1225203 = 1837805) B1837805
theorem B1225219 : Blo 1224430 1225219 := bstep (se 1 (by rfl) ⟨918914, by rfl⟩ : syracuseStep 1225219 = 1837829) B1837829
theorem B1839617 : Blo 1224430 1839617 := bstep (se 2 (by rfl) ⟨689856, by rfl⟩ : syracuseStep 1839617 = 1379713) B1379713
theorem B1225235 : Blo 1224430 1225235 := bstep (se 1 (by rfl) ⟨918926, by rfl⟩ : syracuseStep 1225235 = 1837853) B1837853
theorem B1839635 : Blo 1224430 1839635 := bstep (se 1 (by rfl) ⟨1379726, by rfl⟩ : syracuseStep 1839635 = 2759453) B2759453
theorem B1864225 : Blo 1224430 1864225 := bstep (se 2 (by rfl) ⟨699084, by rfl⟩ : syracuseStep 1864225 = 1398169) B1398169
theorem B1225251 : Blo 1224430 1225251 := bstep (se 1 (by rfl) ⟨918938, by rfl⟩ : syracuseStep 1225251 = 1837877) B1837877
theorem B1225267 : Blo 1224430 1225267 := bstep (se 1 (by rfl) ⟨918950, by rfl⟩ : syracuseStep 1225267 = 1837901) B1837901
theorem B2069057 : Blo 1224430 2069057 := bstep (se 2 (by rfl) ⟨775896, by rfl⟩ : syracuseStep 2069057 = 1551793) B1551793
theorem B1225283 : Blo 1224430 1225283 := bstep (se 1 (by rfl) ⟨918962, by rfl⟩ : syracuseStep 1225283 = 1837925) B1837925
theorem B1225299 : Blo 1224430 1225299 := bstep (se 1 (by rfl) ⟨918974, by rfl⟩ : syracuseStep 1225299 = 1837949) B1837949
theorem B10629731 : Blo 1224430 10629731 := bstep (se 1 (by rfl) ⟨7972298, by rfl⟩ : syracuseStep 10629731 = 15944597) B15944597
theorem B1225315 : Blo 1224430 1225315 := bstep (se 1 (by rfl) ⟨918986, by rfl⟩ : syracuseStep 1225315 = 1837973) B1837973
theorem B1962611 : Blo 1224430 1962611 := bstep (se 1 (by rfl) ⟨1471958, by rfl⟩ : syracuseStep 1962611 = 2943917) B2943917
theorem B1225331 : Blo 1224430 1225331 := bstep (se 1 (by rfl) ⟨918998, by rfl⟩ : syracuseStep 1225331 = 1837997) B1837997
theorem B1225347 : Blo 1224430 1225347 := bstep (se 1 (by rfl) ⟨919010, by rfl⟩ : syracuseStep 1225347 = 1838021) B1838021
theorem B1225363 : Blo 1224430 1225363 := bstep (se 1 (by rfl) ⟨919022, by rfl⟩ : syracuseStep 1225363 = 1838045) B1838045
theorem B1225379 : Blo 1224430 1225379 := bstep (se 1 (by rfl) ⟨919034, by rfl⟩ : syracuseStep 1225379 = 1838069) B1838069
theorem B1225395 : Blo 1224430 1225395 := bstep (se 1 (by rfl) ⟨919046, by rfl⟩ : syracuseStep 1225395 = 1838093) B1838093
theorem B2069185 : Blo 1224430 2069185 := bstep (se 2 (by rfl) ⟨775944, by rfl⟩ : syracuseStep 2069185 = 1551889) B1551889
theorem B1225411 : Blo 1224430 1225411 := bstep (se 1 (by rfl) ⟨919058, by rfl⟩ : syracuseStep 1225411 = 1838117) B1838117
theorem B2757329 : Blo 1224430 2757329 := bstep (se 2 (by rfl) ⟨1033998, by rfl⟩ : syracuseStep 2757329 = 2067997) B2067997
theorem B1225427 : Blo 1224430 1225427 := bstep (se 1 (by rfl) ⟨919070, by rfl⟩ : syracuseStep 1225427 = 1838141) B1838141
theorem B1225443 : Blo 1224430 1225443 := bstep (se 1 (by rfl) ⟨919082, by rfl⟩ : syracuseStep 1225443 = 1838165) B1838165
theorem B2757347 : Blo 1224430 2757347 := bstep (se 1 (by rfl) ⟨2068010, by rfl⟩ : syracuseStep 2757347 = 4136021) B4136021
theorem B2069219 : Blo 1224430 2069219 := bstep (se 1 (by rfl) ⟨1551914, by rfl⟩ : syracuseStep 2069219 = 3103829) B3103829
theorem B1962739 : Blo 1224430 1962739 := bstep (se 1 (by rfl) ⟨1472054, by rfl⟩ : syracuseStep 1962739 = 2944109) B2944109
theorem B1225459 : Blo 1224430 1225459 := bstep (se 1 (by rfl) ⟨919094, by rfl⟩ : syracuseStep 1225459 = 1838189) B1838189
theorem B1225475 : Blo 1224430 1225475 := bstep (se 1 (by rfl) ⟨919106, by rfl⟩ : syracuseStep 1225475 = 1838213) B1838213
theorem B4133645 : Blo 1224430 4133645 := bstep (se 3 (by rfl) ⟨775058, by rfl⟩ : syracuseStep 4133645 = 1550117) B1550117
theorem B1225491 : Blo 1224430 1225491 := bstep (se 1 (by rfl) ⟨919118, by rfl⟩ : syracuseStep 1225491 = 1838237) B1838237
theorem B1225507 : Blo 1224430 1225507 := bstep (se 1 (by rfl) ⟨919130, by rfl⟩ : syracuseStep 1225507 = 1838261) B1838261
theorem B1225523 : Blo 1224430 1225523 := bstep (se 1 (by rfl) ⟨919142, by rfl⟩ : syracuseStep 1225523 = 1838285) B1838285
theorem B4133699 : Blo 1224430 4133699 := bstep (se 1 (by rfl) ⟨3100274, by rfl⟩ : syracuseStep 4133699 = 6200549) B6200549
theorem B1225539 : Blo 1224430 1225539 := bstep (se 1 (by rfl) ⟨919154, by rfl⟩ : syracuseStep 1225539 = 1838309) B1838309
theorem B1225555 : Blo 1224430 1225555 := bstep (se 1 (by rfl) ⟨919166, by rfl⟩ : syracuseStep 1225555 = 1838333) B1838333
theorem B1225571 : Blo 1224430 1225571 := bstep (se 1 (by rfl) ⟨919178, by rfl⟩ : syracuseStep 1225571 = 1838357) B1838357
theorem B2069347 : Blo 1224430 2069347 := bstep (se 1 (by rfl) ⟨1552010, by rfl⟩ : syracuseStep 2069347 = 3104021) B3104021
theorem B1225587 : Blo 1224430 1225587 := bstep (se 1 (by rfl) ⟨919190, by rfl⟩ : syracuseStep 1225587 = 1838381) B1838381
theorem B1225603 : Blo 1224430 1225603 := bstep (se 1 (by rfl) ⟨919202, by rfl⟩ : syracuseStep 1225603 = 1838405) B1838405
theorem B3404675 : Blo 1224430 3404675 := bstep (se 1 (by rfl) ⟨2553506, by rfl⟩ : syracuseStep 3404675 = 5107013) B5107013
theorem B1225619 : Blo 1224430 1225619 := bstep (se 1 (by rfl) ⟨919214, by rfl⟩ : syracuseStep 1225619 = 1838429) B1838429
theorem B1225635 : Blo 1224430 1225635 := bstep (se 1 (by rfl) ⟨919226, by rfl⟩ : syracuseStep 1225635 = 1838453) B1838453
theorem B1225651 : Blo 1224430 1225651 := bstep (se 1 (by rfl) ⟨919238, by rfl⟩ : syracuseStep 1225651 = 1838477) B1838477
theorem B1307587 : Blo 1224430 1307587 := bstep (se 1 (by rfl) ⟨980690, by rfl⟩ : syracuseStep 1307587 = 1961381) B1961381
theorem B1225667 : Blo 1224430 1225667 := bstep (se 1 (by rfl) ⟨919250, by rfl⟩ : syracuseStep 1225667 = 1838501) B1838501
theorem B1225683 : Blo 1224430 1225683 := bstep (se 1 (by rfl) ⟨919262, by rfl⟩ : syracuseStep 1225683 = 1838525) B1838525
theorem B9303011 : Blo 1224430 9303011 := bstep (se 1 (by rfl) ⟨6977258, by rfl⟩ : syracuseStep 9303011 = 13954517) B13954517
theorem B1225699 : Blo 1224430 1225699 := bstep (se 1 (by rfl) ⟨919274, by rfl⟩ : syracuseStep 1225699 = 1838549) B1838549
theorem B2757617 : Blo 1224430 2757617 := bstep (se 2 (by rfl) ⟨1034106, by rfl⟩ : syracuseStep 2757617 = 2068213) B2068213
theorem B2069489 : Blo 1224430 2069489 := bstep (se 2 (by rfl) ⟨776058, by rfl⟩ : syracuseStep 2069489 = 1552117) B1552117
theorem B1225715 : Blo 1224430 1225715 := bstep (se 1 (by rfl) ⟨919286, by rfl⟩ : syracuseStep 1225715 = 1838573) B1838573
theorem B2757635 : Blo 1224430 2757635 := bstep (se 1 (by rfl) ⟨2068226, by rfl⟩ : syracuseStep 2757635 = 4136453) B4136453
theorem B1225731 : Blo 1224430 1225731 := bstep (se 1 (by rfl) ⟨919298, by rfl⟩ : syracuseStep 1225731 = 1838597) B1838597
theorem B1225747 : Blo 1224430 1225747 := bstep (se 1 (by rfl) ⟨919310, by rfl⟩ : syracuseStep 1225747 = 1838621) B1838621
theorem B1225763 : Blo 1224430 1225763 := bstep (se 1 (by rfl) ⟨919322, by rfl⟩ : syracuseStep 1225763 = 1838645) B1838645
theorem B1225779 : Blo 1224430 1225779 := bstep (se 1 (by rfl) ⟨919334, by rfl⟩ : syracuseStep 1225779 = 1838669) B1838669
theorem B1471555 : Blo 1224430 1471555 := bstep (se 1 (by rfl) ⟨1103666, by rfl⟩ : syracuseStep 1471555 = 2207333) B2207333
theorem B1225795 : Blo 1224430 1225795 := bstep (se 1 (by rfl) ⟨919346, by rfl⟩ : syracuseStep 1225795 = 1838693) B1838693
theorem B3486797 : Blo 1224430 3486797 := bstep (se 3 (by rfl) ⟨653774, by rfl⟩ : syracuseStep 3486797 = 1307549) B1307549
theorem B4133969 : Blo 1224430 4133969 := bstep (se 2 (by rfl) ⟨1550238, by rfl⟩ : syracuseStep 4133969 = 3100477) B3100477
theorem B1225811 : Blo 1224430 1225811 := bstep (se 1 (by rfl) ⟨919358, by rfl⟩ : syracuseStep 1225811 = 1838717) B1838717
theorem B1225827 : Blo 1224430 1225827 := bstep (se 1 (by rfl) ⟨919370, by rfl⟩ : syracuseStep 1225827 = 1838741) B1838741
theorem B1225843 : Blo 1224430 1225843 := bstep (se 1 (by rfl) ⟨919382, by rfl⟩ : syracuseStep 1225843 = 1838765) B1838765
theorem B1225859 : Blo 1224430 1225859 := bstep (se 1 (by rfl) ⟨919394, by rfl⟩ : syracuseStep 1225859 = 1838789) B1838789
theorem B1225875 : Blo 1224430 1225875 := bstep (se 1 (by rfl) ⟨919406, by rfl⟩ : syracuseStep 1225875 = 1838813) B1838813
theorem B1225891 : Blo 1224430 1225891 := bstep (se 1 (by rfl) ⟨919418, by rfl⟩ : syracuseStep 1225891 = 1838837) B1838837
theorem B1225907 : Blo 1224430 1225907 := bstep (se 1 (by rfl) ⟨919430, by rfl⟩ : syracuseStep 1225907 = 1838861) B1838861
theorem B1225923 : Blo 1224430 1225923 := bstep (se 1 (by rfl) ⟨919442, by rfl⟩ : syracuseStep 1225923 = 1838885) B1838885
theorem B1471699 : Blo 1224430 1471699 := bstep (se 1 (by rfl) ⟨1103774, by rfl⟩ : syracuseStep 1471699 = 2207549) B2207549
theorem B1225939 : Blo 1224430 1225939 := bstep (se 1 (by rfl) ⟨919454, by rfl⟩ : syracuseStep 1225939 = 1838909) B1838909
theorem B1225955 : Blo 1224430 1225955 := bstep (se 1 (by rfl) ⟨919466, by rfl⟩ : syracuseStep 1225955 = 1838933) B1838933
theorem B5887217 : Blo 1224430 5887217 := bstep (se 2 (by rfl) ⟨2207706, by rfl⟩ : syracuseStep 5887217 = 4415413) B4415413
theorem B5174513 : Blo 1224430 5174513 := bstep (se 2 (by rfl) ⟨1940442, by rfl⟩ : syracuseStep 5174513 = 3880885) B3880885
theorem B1225971 : Blo 1224430 1225971 := bstep (se 1 (by rfl) ⟨919478, by rfl⟩ : syracuseStep 1225971 = 1838957) B1838957
theorem B6206705 : Blo 1224430 6206705 := bstep (se 2 (by rfl) ⟨2327514, by rfl⟩ : syracuseStep 6206705 = 4655029) B4655029
theorem B1225987 : Blo 1224430 1225987 := bstep (se 1 (by rfl) ⟨919490, by rfl⟩ : syracuseStep 1225987 = 1838981) B1838981
theorem B3486989 : Blo 1224430 3486989 := bstep (se 3 (by rfl) ⟨653810, by rfl⟩ : syracuseStep 3486989 = 1307621) B1307621
theorem B2757905 : Blo 1224430 2757905 := bstep (se 2 (by rfl) ⟨1034214, by rfl⟩ : syracuseStep 2757905 = 2068429) B2068429
theorem B1226003 : Blo 1224430 1226003 := bstep (se 1 (by rfl) ⟨919502, by rfl⟩ : syracuseStep 1226003 = 1839005) B1839005
theorem B2757923 : Blo 1224430 2757923 := bstep (se 1 (by rfl) ⟨2068442, by rfl⟩ : syracuseStep 2757923 = 4136885) B4136885
theorem B1226019 : Blo 1224430 1226019 := bstep (se 1 (by rfl) ⟨919514, by rfl⟩ : syracuseStep 1226019 = 1839029) B1839029
theorem B2618659 : Blo 1224430 2618659 := bstep (se 1 (by rfl) ⟨1963994, by rfl⟩ : syracuseStep 2618659 = 3927989) B3927989
theorem B1226035 : Blo 1224430 1226035 := bstep (se 1 (by rfl) ⟨919526, by rfl⟩ : syracuseStep 1226035 = 1839053) B1839053
theorem B1226051 : Blo 1224430 1226051 := bstep (se 1 (by rfl) ⟨919538, by rfl⟩ : syracuseStep 1226051 = 1839077) B1839077
theorem B1242451 : Blo 1224430 1242451 := bstep (se 1 (by rfl) ⟨931838, by rfl⟩ : syracuseStep 1242451 = 1863677) B1863677
theorem B1226067 : Blo 1224430 1226067 := bstep (se 1 (by rfl) ⟨919550, by rfl⟩ : syracuseStep 1226067 = 1839101) B1839101
theorem B1226083 : Blo 1224430 1226083 := bstep (se 1 (by rfl) ⟨919562, by rfl⟩ : syracuseStep 1226083 = 1839125) B1839125
theorem B1226099 : Blo 1224430 1226099 := bstep (se 1 (by rfl) ⟨919574, by rfl⟩ : syracuseStep 1226099 = 1839149) B1839149
theorem B1226115 : Blo 1224430 1226115 := bstep (se 1 (by rfl) ⟨919586, by rfl⟩ : syracuseStep 1226115 = 1839173) B1839173
theorem B3102097 : Blo 1224430 3102097 := bstep (se 2 (by rfl) ⟨1163286, by rfl⟩ : syracuseStep 3102097 = 2326573) B2326573
theorem B1226131 : Blo 1224430 1226131 := bstep (se 1 (by rfl) ⟨919598, by rfl⟩ : syracuseStep 1226131 = 1839197) B1839197
theorem B1226147 : Blo 1224430 1226147 := bstep (se 1 (by rfl) ⟨919610, by rfl⟩ : syracuseStep 1226147 = 1839221) B1839221
theorem B1226163 : Blo 1224430 1226163 := bstep (se 1 (by rfl) ⟨919622, by rfl⟩ : syracuseStep 1226163 = 1839245) B1839245
theorem B1963457 : Blo 1224430 1963457 := bstep (se 2 (by rfl) ⟨736296, by rfl⟩ : syracuseStep 1963457 = 1472593) B1472593
theorem B1226179 : Blo 1224430 1226179 := bstep (se 1 (by rfl) ⟨919634, by rfl⟩ : syracuseStep 1226179 = 1839269) B1839269
theorem B1226195 : Blo 1224430 1226195 := bstep (se 1 (by rfl) ⟨919646, by rfl⟩ : syracuseStep 1226195 = 1839293) B1839293
theorem B1226211 : Blo 1224430 1226211 := bstep (se 1 (by rfl) ⟨919658, by rfl⟩ : syracuseStep 1226211 = 1839317) B1839317
theorem B1226227 : Blo 1224430 1226227 := bstep (se 1 (by rfl) ⟨919670, by rfl⟩ : syracuseStep 1226227 = 1839341) B1839341
theorem B1226243 : Blo 1224430 1226243 := bstep (se 1 (by rfl) ⟨919682, by rfl⟩ : syracuseStep 1226243 = 1839365) B1839365
theorem B1226259 : Blo 1224430 1226259 := bstep (se 1 (by rfl) ⟨919694, by rfl⟩ : syracuseStep 1226259 = 1839389) B1839389
theorem B1226275 : Blo 1224430 1226275 := bstep (se 1 (by rfl) ⟨919706, by rfl⟩ : syracuseStep 1226275 = 1839413) B1839413
theorem B2758193 : Blo 1224430 2758193 := bstep (se 2 (by rfl) ⟨1034322, by rfl⟩ : syracuseStep 2758193 = 2068645) B2068645
theorem B1226291 : Blo 1224430 1226291 := bstep (se 1 (by rfl) ⟨919718, by rfl⟩ : syracuseStep 1226291 = 1839437) B1839437
theorem B2758211 : Blo 1224430 2758211 := bstep (se 1 (by rfl) ⟨2068658, by rfl⟩ : syracuseStep 2758211 = 4137317) B4137317
theorem B1226307 : Blo 1224430 1226307 := bstep (se 1 (by rfl) ⟨919730, by rfl⟩ : syracuseStep 1226307 = 1839461) B1839461
theorem B5887565 : Blo 1224430 5887565 := bstep (se 3 (by rfl) ⟨1103918, by rfl⟩ : syracuseStep 5887565 = 2207837) B2207837
theorem B1226323 : Blo 1224430 1226323 := bstep (se 1 (by rfl) ⟨919742, by rfl⟩ : syracuseStep 1226323 = 1839485) B1839485
theorem B6977123 : Blo 1224430 6977123 := bstep (se 1 (by rfl) ⟨5232842, by rfl⟩ : syracuseStep 6977123 = 10465685) B10465685
theorem B1226339 : Blo 1224430 1226339 := bstep (se 1 (by rfl) ⟨919754, by rfl⟩ : syracuseStep 1226339 = 1839509) B1839509
theorem B4134509 : Blo 1224430 4134509 := bstep (se 3 (by rfl) ⟨775220, by rfl⟩ : syracuseStep 4134509 = 1550441) B1550441
theorem B2618993 : Blo 1224430 2618993 := bstep (se 2 (by rfl) ⟨982122, by rfl⟩ : syracuseStep 2618993 = 1964245) B1964245
theorem B1226355 : Blo 1224430 1226355 := bstep (se 1 (by rfl) ⟨919766, by rfl⟩ : syracuseStep 1226355 = 1839533) B1839533
theorem B1963649 : Blo 1224430 1963649 := bstep (se 2 (by rfl) ⟨736368, by rfl⟩ : syracuseStep 1963649 = 1472737) B1472737
theorem B1226371 : Blo 1224430 1226371 := bstep (se 1 (by rfl) ⟨919778, by rfl⟩ : syracuseStep 1226371 = 1839557) B1839557
theorem B1226387 : Blo 1224430 1226387 := bstep (se 1 (by rfl) ⟨919790, by rfl⟩ : syracuseStep 1226387 = 1839581) B1839581
theorem B4134563 : Blo 1224430 4134563 := bstep (se 1 (by rfl) ⟨3100922, by rfl⟩ : syracuseStep 4134563 = 6201845) B6201845
theorem B3102371 : Blo 1224430 3102371 := bstep (se 1 (by rfl) ⟨2326778, by rfl⟩ : syracuseStep 3102371 = 4653557) B4653557
theorem B1226403 : Blo 1224430 1226403 := bstep (se 1 (by rfl) ⟨919802, by rfl⟩ : syracuseStep 1226403 = 1839605) B1839605
theorem B1226419 : Blo 1224430 1226419 := bstep (se 1 (by rfl) ⟨919814, by rfl⟩ : syracuseStep 1226419 = 1839629) B1839629
theorem B1308403 : Blo 1224430 1308403 := bstep (se 1 (by rfl) ⟨981302, by rfl⟩ : syracuseStep 1308403 = 1962605) B1962605
theorem B8492813 : Blo 1224430 8492813 := bstep (se 3 (by rfl) ⟨1592402, by rfl⟩ : syracuseStep 8492813 = 3184805) B3184805
theorem B13948685 : Blo 1224430 13948685 := bstep (se 3 (by rfl) ⟨2615378, by rfl⟩ : syracuseStep 13948685 = 5230757) B5230757
theorem B2758481 : Blo 1224430 2758481 := bstep (se 2 (by rfl) ⟨1034430, by rfl⟩ : syracuseStep 2758481 = 2068861) B2068861
theorem B3102563 : Blo 1224430 3102563 := bstep (se 1 (by rfl) ⟨2326922, by rfl⟩ : syracuseStep 3102563 = 4653845) B4653845
theorem B2758499 : Blo 1224430 2758499 := bstep (se 1 (by rfl) ⟨2068874, by rfl⟩ : syracuseStep 2758499 = 4137749) B4137749
theorem B4413325 : Blo 1224430 4413325 := bstep (se 3 (by rfl) ⟨827498, by rfl⟩ : syracuseStep 4413325 = 1654997) B1654997
theorem B4650929 : Blo 1224430 4650929 := bstep (se 2 (by rfl) ⟨1744098, by rfl⟩ : syracuseStep 4650929 = 3488197) B3488197
theorem B4134833 : Blo 1224430 4134833 := bstep (se 2 (by rfl) ⟨1550562, by rfl⟩ : syracuseStep 4134833 = 3101125) B3101125
theorem B2758769 : Blo 1224430 2758769 := bstep (se 2 (by rfl) ⟨1034538, by rfl⟩ : syracuseStep 2758769 = 2069077) B2069077
theorem B2758787 : Blo 1224430 2758787 := bstep (se 1 (by rfl) ⟨2069090, by rfl⟩ : syracuseStep 2758787 = 4138181) B4138181
theorem B2209955 : Blo 1224430 2209955 := bstep (se 1 (by rfl) ⟨1657466, by rfl⟩ : syracuseStep 2209955 = 3314933) B3314933
theorem B2324675 : Blo 1224430 2324675 := bstep (se 1 (by rfl) ⟨1743506, by rfl⟩ : syracuseStep 2324675 = 3487013) B3487013
theorem B3487981 : Blo 1224430 3487981 := bstep (se 3 (by rfl) ⟨653996, by rfl⟩ : syracuseStep 3487981 = 1307993) B1307993
theorem B6625585 : Blo 1224430 6625585 := bstep (se 2 (by rfl) ⟨2484594, by rfl⟩ : syracuseStep 6625585 = 4969189) B4969189
theorem B21223733 : Blo 1224430 21223733 := bstep (se 5 (by rfl) ⟨994862, by rfl⟩ : syracuseStep 21223733 = 1989725) B1989725
theorem B2759057 : Blo 1224430 2759057 := bstep (se 2 (by rfl) ⟨1034646, by rfl⟩ : syracuseStep 2759057 = 2069293) B2069293
theorem B2759075 : Blo 1224430 2759075 := bstep (se 1 (by rfl) ⟨2069306, by rfl⟩ : syracuseStep 2759075 = 4138613) B4138613
theorem B4135373 : Blo 1224430 4135373 := bstep (se 3 (by rfl) ⟨775382, by rfl⟩ : syracuseStep 4135373 = 1550765) B1550765
theorem B2324963 : Blo 1224430 2324963 := bstep (se 1 (by rfl) ⟨1743722, by rfl⟩ : syracuseStep 2324963 = 3487445) B3487445
theorem B4135427 : Blo 1224430 4135427 := bstep (se 1 (by rfl) ⟨3101570, by rfl⟩ : syracuseStep 4135427 = 6203141) B6203141
theorem B1571411 : Blo 1224430 1571411 := bstep (se 1 (by rfl) ⟨1178558, by rfl⟩ : syracuseStep 1571411 = 2357117) B2357117
theorem B6208163 : Blo 1224430 6208163 := bstep (se 1 (by rfl) ⟨4656122, by rfl⟩ : syracuseStep 6208163 = 9312245) B9312245
theorem B2759345 : Blo 1224430 2759345 := bstep (se 2 (by rfl) ⟨1034754, by rfl⟩ : syracuseStep 2759345 = 2069509) B2069509
theorem B2759363 : Blo 1224430 2759363 := bstep (se 1 (by rfl) ⟨2069522, by rfl⟩ : syracuseStep 2759363 = 4139045) B4139045
theorem B9427697 : Blo 1224430 9427697 := bstep (se 2 (by rfl) ⟨3535386, by rfl⟩ : syracuseStep 9427697 = 7070773) B7070773
theorem B3357443 : Blo 1224430 3357443 := bstep (se 1 (by rfl) ⟨2518082, by rfl⟩ : syracuseStep 3357443 = 5036165) B5036165
theorem B4135697 : Blo 1224430 4135697 := bstep (se 2 (by rfl) ⟨1550886, by rfl⟩ : syracuseStep 4135697 = 3101773) B3101773
theorem B3103505 : Blo 1224430 3103505 := bstep (se 2 (by rfl) ⟨1163814, by rfl⟩ : syracuseStep 3103505 = 2327629) B2327629
theorem B3103555 : Blo 1224430 3103555 := bstep (se 1 (by rfl) ⟨2327666, by rfl⟩ : syracuseStep 3103555 = 4655333) B4655333
theorem B1743763 : Blo 1224430 1743763 := bstep (se 1 (by rfl) ⟨1307822, by rfl⟩ : syracuseStep 1743763 = 2615645) B2615645
theorem B3103697 : Blo 1224430 3103697 := bstep (se 2 (by rfl) ⟨1163886, by rfl⟩ : syracuseStep 3103697 = 2327773) B2327773
theorem B1743859 : Blo 1224430 1743859 := bstep (se 1 (by rfl) ⟨1307894, by rfl⟩ : syracuseStep 1743859 = 2615789) B2615789
theorem B1768483 : Blo 1224430 1768483 := bstep (se 1 (by rfl) ⟨1326362, by rfl⟩ : syracuseStep 1768483 = 2652725) B2652725
theorem B20929589 : Blo 1224430 20929589 := bstep (se 5 (by rfl) ⟨981074, by rfl⟩ : syracuseStep 20929589 = 1962149) B1962149
theorem B30194801 : Blo 1224430 30194801 := bstep (se 2 (by rfl) ⟨11323050, by rfl⟩ : syracuseStep 30194801 = 22646101) B22646101
theorem B13253813 : Blo 1224430 13253813 := bstep (se 5 (by rfl) ⟨621272, by rfl⟩ : syracuseStep 13253813 = 1242545) B1242545
theorem B2096323 : Blo 1224430 2096323 := bstep (se 1 (by rfl) ⟨1572242, by rfl⟩ : syracuseStep 2096323 = 3144485) B3144485
theorem B3923171 : Blo 1224430 3923171 := bstep (se 1 (by rfl) ⟨2942378, by rfl⟩ : syracuseStep 3923171 = 5884757) B5884757
theorem B15924451 : Blo 1224430 15924451 := bstep (se 1 (by rfl) ⟨11943338, by rfl⟩ : syracuseStep 15924451 = 23886677) B23886677
theorem B4136237 : Blo 1224430 4136237 := bstep (se 3 (by rfl) ⟨775544, by rfl⟩ : syracuseStep 4136237 = 1551089) B1551089
theorem B2653489 : Blo 1224430 2653489 := bstep (se 2 (by rfl) ⟨995058, by rfl⟩ : syracuseStep 2653489 = 1990117) B1990117
theorem B4652387 : Blo 1224430 4652387 := bstep (se 1 (by rfl) ⟨3489290, by rfl⟩ : syracuseStep 4652387 = 6978581) B6978581
theorem B4136291 : Blo 1224430 4136291 := bstep (se 1 (by rfl) ⟨3102218, by rfl⟩ : syracuseStep 4136291 = 6204437) B6204437
theorem B2325905 : Blo 1224430 2325905 := bstep (se 2 (by rfl) ⟨872214, by rfl⟩ : syracuseStep 2325905 = 1744429) B1744429
theorem B1744355 : Blo 1224430 1744355 := bstep (se 1 (by rfl) ⟨1308266, by rfl⟩ : syracuseStep 1744355 = 2616533) B2616533
theorem B5668387 : Blo 1224430 5668387 := bstep (se 1 (by rfl) ⟨4251290, by rfl⟩ : syracuseStep 5668387 = 8502581) B8502581
theorem B5586509 : Blo 1224430 5586509 := bstep (se 3 (by rfl) ⟨1047470, by rfl⟩ : syracuseStep 5586509 = 2094941) B2094941
theorem B3923569 : Blo 1224430 3923569 := bstep (se 2 (by rfl) ⟨1471338, by rfl⟩ : syracuseStep 3923569 = 2942677) B2942677
theorem B4136561 : Blo 1224430 4136561 := bstep (se 2 (by rfl) ⟨1551210, by rfl⟩ : syracuseStep 4136561 = 3102421) B3102421
theorem B3923633 : Blo 1224430 3923633 := bstep (se 2 (by rfl) ⟨1471362, by rfl⟩ : syracuseStep 3923633 = 2942725) B2942725
theorem B1990337 : Blo 1224430 1990337 := bstep (se 2 (by rfl) ⟨746376, by rfl⟩ : syracuseStep 1990337 = 1492753) B1492753
theorem B5234381 : Blo 1224430 5234381 := bstep (se 3 (by rfl) ⟨981446, by rfl⟩ : syracuseStep 5234381 = 1962893) B1962893
theorem B4251473 : Blo 1224430 4251473 := bstep (se 2 (by rfl) ⟨1594302, by rfl⟩ : syracuseStep 4251473 = 3188605) B3188605
theorem B3489713 : Blo 1224430 3489713 := bstep (se 2 (by rfl) ⟨1308642, by rfl⟩ : syracuseStep 3489713 = 2617285) B2617285
theorem B1744907 : Blo 1224430 1744907 := bstep (se 1 (by rfl) ⟨1308680, by rfl⟩ : syracuseStep 1744907 = 2617361) B2617361
theorem B10469411 : Blo 1224430 10469411 := bstep (se 1 (by rfl) ⟨7852058, by rfl⟩ : syracuseStep 10469411 = 15704117) B15704117
theorem B2326657 : Blo 1224430 2326657 := bstep (se 2 (by rfl) ⟨872496, by rfl⟩ : syracuseStep 2326657 = 1744993) B1744993
theorem B9306413 : Blo 1224430 9306413 := bstep (se 3 (by rfl) ⟨1744952, by rfl⟩ : syracuseStep 9306413 = 3489905) B3489905
theorem B2687321 : Blo 1224430 2687321 := bstep (se 2 (by rfl) ⟨1007745, by rfl⟩ : syracuseStep 2687321 = 2015491) B2015491
theorem B4252097 : Blo 1224430 4252097 := bstep (se 2 (by rfl) ⟨1594536, by rfl⟩ : syracuseStep 4252097 = 3189073) B3189073
theorem B2359795 : Blo 1224430 2359795 := bstep (se 1 (by rfl) ⟨1769846, by rfl⟩ : syracuseStep 2359795 = 3539693) B3539693
theorem B4653571 : Blo 1224430 4653571 := bstep (se 1 (by rfl) ⟨3490178, by rfl⟩ : syracuseStep 4653571 = 6980357) B6980357
theorem B13238801 : Blo 1224430 13238801 := bstep (se 2 (by rfl) ⟨4964550, by rfl⟩ : syracuseStep 13238801 = 9929101) B9929101
theorem B22364707 : Blo 1224430 22364707 := bstep (se 1 (by rfl) ⟨16773530, by rfl⟩ : syracuseStep 22364707 = 33547061) B33547061
theorem B226386485 : Blo 1224430 226386485 := bstep (se 5 (by rfl) ⟨10611866, by rfl⟩ : syracuseStep 226386485 = 21223733) B21223733
theorem B2327105 : Blo 1224430 2327105 := bstep (se 2 (by rfl) ⟨872664, by rfl⟩ : syracuseStep 2327105 = 1745329) B1745329
theorem B2269783 : Blo 1224430 2269783 := bstep (se 1 (by rfl) ⟨1702337, by rfl⟩ : syracuseStep 2269783 = 3404675) B3404675
theorem B6202007 : Blo 1224430 6202007 := bstep (se 1 (by rfl) ⟨4651505, by rfl⟩ : syracuseStep 6202007 = 9303011) B9303011
theorem B9298637 : Blo 1224430 9298637 := bstep (se 3 (by rfl) ⟨1743494, by rfl⟩ : syracuseStep 9298637 = 3486989) B3486989
theorem B4653875 : Blo 1224430 4653875 := bstep (se 1 (by rfl) ⟨3490406, by rfl⟩ : syracuseStep 4653875 = 6980813) B6980813
theorem B3924811 : Blo 1224430 3924811 := bstep (se 1 (by rfl) ⟨2943608, by rfl⟩ : syracuseStep 3924811 = 5887217) B5887217
theorem B3449675 : Blo 1224430 3449675 := bstep (se 1 (by rfl) ⟨2587256, by rfl⟩ : syracuseStep 3449675 = 5174513) B5174513
theorem B4137803 : Blo 1224430 4137803 := bstep (se 1 (by rfl) ⟨3103352, by rfl⟩ : syracuseStep 4137803 = 6206705) B6206705
theorem B2327447 : Blo 1224430 2327447 := bstep (se 1 (by rfl) ⟨1745585, by rfl⟩ : syracuseStep 2327447 = 3491171) B3491171
theorem B3925043 : Blo 1224430 3925043 := bstep (se 1 (by rfl) ⟨2943782, by rfl⟩ : syracuseStep 3925043 = 5887565) B5887565
theorem B4138073 : Blo 1224430 4138073 := bstep (se 2 (by rfl) ⟨1551777, by rfl⟩ : syracuseStep 4138073 = 3103555) B3103555
theorem B15696989 : Blo 1224430 15696989 := bstep (se 3 (by rfl) ⟨2943185, by rfl⟩ : syracuseStep 15696989 = 5886371) B5886371
theorem B7849061 : Blo 1224430 7849061 := bstep (se 4 (by rfl) ⟨735849, by rfl⟩ : syracuseStep 7849061 = 1471699) B1471699
theorem B5661875 : Blo 1224430 5661875 := bstep (se 1 (by rfl) ⟨4246406, by rfl⟩ : syracuseStep 5661875 = 8492813) B8492813
theorem B9299123 : Blo 1224430 9299123 := bstep (se 1 (by rfl) ⟨6974342, by rfl⟩ : syracuseStep 9299123 = 13948685) B13948685
theorem B4719809 : Blo 1224430 4719809 := bstep (se 2 (by rfl) ⟨1769928, by rfl⟩ : syracuseStep 4719809 = 3539857) B3539857
theorem B14157101 : Blo 1224430 14157101 := bstep (se 3 (by rfl) ⟨2654456, by rfl⟩ : syracuseStep 14157101 = 5308913) B5308913
theorem B1377643 : Blo 1224430 1377643 := bstep (se 1 (by rfl) ⟨1033232, by rfl⟩ : syracuseStep 1377643 = 2066465) B2066465
theorem B26477941 : Blo 1224430 26477941 := bstep (se 5 (by rfl) ⟨1241153, by rfl⟩ : syracuseStep 26477941 = 2482307) B2482307
theorem B4654529 : Blo 1224430 4654529 := bstep (se 2 (by rfl) ⟨1745448, by rfl⟩ : syracuseStep 4654529 = 3490897) B3490897
theorem B1549783 : Blo 1224430 1549783 := bstep (se 1 (by rfl) ⟨1162337, by rfl⟩ : syracuseStep 1549783 = 2324675) B2324675
theorem B1377751 : Blo 1224430 1377751 := bstep (se 1 (by rfl) ⟨1033313, by rfl⟩ : syracuseStep 1377751 = 2066627) B2066627
theorem B2328115 : Blo 1224430 2328115 := bstep (se 1 (by rfl) ⟨1746086, by rfl⟩ : syracuseStep 2328115 = 3492173) B3492173
theorem B28345949 : Blo 1224430 28345949 := bstep (se 3 (by rfl) ⟨5314865, by rfl⟩ : syracuseStep 28345949 = 10629731) B10629731
theorem B1836683 : Blo 1224430 1836683 := bstep (se 1 (by rfl) ⟨1377512, by rfl⟩ : syracuseStep 1836683 = 2755025) B2755025
theorem B1377931 : Blo 1224430 1377931 := bstep (se 1 (by rfl) ⟨1033448, by rfl⟩ : syracuseStep 1377931 = 2066897) B2066897
theorem B1836695 : Blo 1224430 1836695 := bstep (se 1 (by rfl) ⟨1377521, by rfl⟩ : syracuseStep 1836695 = 2755043) B2755043
theorem B5236397 : Blo 1224430 5236397 := bstep (se 3 (by rfl) ⟨981824, by rfl⟩ : syracuseStep 5236397 = 1963649) B1963649
theorem B4474547 : Blo 1224430 4474547 := bstep (se 1 (by rfl) ⟨3355910, by rfl⟩ : syracuseStep 4474547 = 6711821) B6711821
theorem B1836761 : Blo 1224430 1836761 := bstep (se 2 (by rfl) ⟨688785, by rfl⟩ : syracuseStep 1836761 = 1377571) B1377571
theorem B1378039 : Blo 1224430 1378039 := bstep (se 1 (by rfl) ⟨1033529, by rfl⟩ : syracuseStep 1378039 = 2067059) B2067059
theorem B4138775 : Blo 1224430 4138775 := bstep (se 1 (by rfl) ⟨3104081, by rfl⟩ : syracuseStep 4138775 = 6208163) B6208163
theorem B19384109 : Blo 1224430 19384109 := bstep (se 3 (by rfl) ⟨3634520, by rfl⟩ : syracuseStep 19384109 = 7269041) B7269041
theorem B1836875 : Blo 1224430 1836875 := bstep (se 1 (by rfl) ⟨1377656, by rfl⟩ : syracuseStep 1836875 = 2755313) B2755313
theorem B6285131 : Blo 1224430 6285131 := bstep (se 1 (by rfl) ⟨4713848, by rfl⟩ : syracuseStep 6285131 = 9427697) B9427697
theorem B1836887 : Blo 1224430 1836887 := bstep (se 1 (by rfl) ⟨1377665, by rfl⟩ : syracuseStep 1836887 = 2755331) B2755331
theorem B2238295 : Blo 1224430 2238295 := bstep (se 1 (by rfl) ⟨1678721, by rfl⟩ : syracuseStep 2238295 = 3357443) B3357443
theorem B4417373 : Blo 1224430 4417373 := bstep (se 3 (by rfl) ⟨828257, by rfl⟩ : syracuseStep 4417373 = 1656515) B1656515
theorem B1836953 : Blo 1224430 1836953 := bstep (se 2 (by rfl) ⟨688857, by rfl⟩ : syracuseStep 1836953 = 1377715) B1377715
theorem B1378219 : Blo 1224430 1378219 := bstep (se 1 (by rfl) ⟨1033664, by rfl⟩ : syracuseStep 1378219 = 2067329) B2067329
theorem B1837067 : Blo 1224430 1837067 := bstep (se 1 (by rfl) ⟨1377800, by rfl⟩ : syracuseStep 1837067 = 2755601) B2755601
theorem B1837079 : Blo 1224430 1837079 := bstep (se 1 (by rfl) ⟨1377809, by rfl⟩ : syracuseStep 1837079 = 2755619) B2755619
theorem B1378327 : Blo 1224430 1378327 := bstep (se 1 (by rfl) ⟨1033745, by rfl⟩ : syracuseStep 1378327 = 2067491) B2067491
theorem B13953059 : Blo 1224430 13953059 := bstep (se 1 (by rfl) ⟨10464794, by rfl⟩ : syracuseStep 13953059 = 20929589) B20929589
theorem B20129867 : Blo 1224430 20129867 := bstep (se 1 (by rfl) ⟨15097400, by rfl⟩ : syracuseStep 20129867 = 30194801) B30194801
theorem B2066519 : Blo 1224430 2066519 := bstep (se 1 (by rfl) ⟨1549889, by rfl⟩ : syracuseStep 2066519 = 3099779) B3099779
theorem B1837145 : Blo 1224430 1837145 := bstep (se 2 (by rfl) ⟨688929, by rfl⟩ : syracuseStep 1837145 = 1377859) B1377859
theorem B2615447 : Blo 1224430 2615447 := bstep (se 1 (by rfl) ⟨1961585, by rfl⟩ : syracuseStep 2615447 = 3923171) B3923171
theorem B7850135 : Blo 1224430 7850135 := bstep (se 1 (by rfl) ⟨5887601, by rfl⟩ : syracuseStep 7850135 = 11775203) B11775203
theorem B1837259 : Blo 1224430 1837259 := bstep (se 1 (by rfl) ⟨1377944, by rfl⟩ : syracuseStep 1837259 = 2755889) B2755889
theorem B3311819 : Blo 1224430 3311819 := bstep (se 1 (by rfl) ⟨2483864, by rfl⟩ : syracuseStep 3311819 = 4967729) B4967729
theorem B1378507 : Blo 1224430 1378507 := bstep (se 1 (by rfl) ⟨1033880, by rfl⟩ : syracuseStep 1378507 = 2067761) B2067761
theorem B2066647 : Blo 1224430 2066647 := bstep (se 1 (by rfl) ⟨1549985, by rfl⟩ : syracuseStep 2066647 = 3099971) B3099971
theorem B1837271 : Blo 1224430 1837271 := bstep (se 1 (by rfl) ⟨1377953, by rfl⟩ : syracuseStep 1837271 = 2755907) B2755907
theorem B1550603 : Blo 1224430 1550603 := bstep (se 1 (by rfl) ⟨1162952, by rfl⟩ : syracuseStep 1550603 = 2325905) B2325905
theorem B1837337 : Blo 1224430 1837337 := bstep (se 2 (by rfl) ⟨689001, by rfl⟩ : syracuseStep 1837337 = 1378003) B1378003
theorem B1378615 : Blo 1224430 1378615 := bstep (se 1 (by rfl) ⟨1033961, by rfl⟩ : syracuseStep 1378615 = 2067923) B2067923
theorem B5237081 : Blo 1224430 5237081 := bstep (se 2 (by rfl) ⟨1963905, by rfl⟩ : syracuseStep 5237081 = 3927811) B3927811
theorem B1837451 : Blo 1224430 1837451 := bstep (se 1 (by rfl) ⟨1378088, by rfl⟩ : syracuseStep 1837451 = 2756177) B2756177
theorem B1837463 : Blo 1224430 1837463 := bstep (se 1 (by rfl) ⟨1378097, by rfl⟩ : syracuseStep 1837463 = 2756195) B2756195
theorem B2615755 : Blo 1224430 2615755 := bstep (se 1 (by rfl) ⟨1961816, by rfl⟩ : syracuseStep 2615755 = 3923633) B3923633
theorem B1837529 : Blo 1224430 1837529 := bstep (se 2 (by rfl) ⟨689073, by rfl⟩ : syracuseStep 1837529 = 1378147) B1378147
theorem B4418009 : Blo 1224430 4418009 := bstep (se 2 (by rfl) ⟨1656753, by rfl⟩ : syracuseStep 4418009 = 3313507) B3313507
theorem B1378795 : Blo 1224430 1378795 := bstep (se 1 (by rfl) ⟨1034096, by rfl⟩ : syracuseStep 1378795 = 2068193) B2068193
theorem B5884433 : Blo 1224430 5884433 := bstep (se 2 (by rfl) ⟨2206662, by rfl⟩ : syracuseStep 5884433 = 4413325) B4413325
theorem B4418065 : Blo 1224430 4418065 := bstep (se 2 (by rfl) ⟨1656774, by rfl⟩ : syracuseStep 4418065 = 3313549) B3313549
theorem B2755097 : Blo 1224430 2755097 := bstep (se 2 (by rfl) ⟨1033161, by rfl⟩ : syracuseStep 2755097 = 2066323) B2066323
theorem B1837643 : Blo 1224430 1837643 := bstep (se 1 (by rfl) ⟨1378232, by rfl⟩ : syracuseStep 1837643 = 2756465) B2756465
theorem B1837655 : Blo 1224430 1837655 := bstep (se 1 (by rfl) ⟨1378241, by rfl⟩ : syracuseStep 1837655 = 2756483) B2756483
theorem B1378903 : Blo 1224430 1378903 := bstep (se 1 (by rfl) ⟨1034177, by rfl⟩ : syracuseStep 1378903 = 2068355) B2068355
theorem B9300581 : Blo 1224430 9300581 := bstep (se 4 (by rfl) ⟨871929, by rfl⟩ : syracuseStep 9300581 = 1743859) B1743859
theorem B2755187 : Blo 1224430 2755187 := bstep (se 1 (by rfl) ⟨2066390, by rfl⟩ : syracuseStep 2755187 = 4132781) B4132781
theorem B2755223 : Blo 1224430 2755223 := bstep (se 1 (by rfl) ⟨2066417, by rfl⟩ : syracuseStep 2755223 = 4132835) B4132835
theorem B7457431 : Blo 1224430 7457431 := bstep (se 1 (by rfl) ⟨5593073, by rfl⟩ : syracuseStep 7457431 = 11186147) B11186147
theorem B1837721 : Blo 1224430 1837721 := bstep (se 2 (by rfl) ⟨689145, by rfl⟩ : syracuseStep 1837721 = 1378291) B1378291
theorem B4655789 : Blo 1224430 4655789 := bstep (se 3 (by rfl) ⟨872960, by rfl⟩ : syracuseStep 4655789 = 1745921) B1745921
theorem B2796211 : Blo 1224430 2796211 := bstep (se 1 (by rfl) ⟨2097158, by rfl⟩ : syracuseStep 2796211 = 4194317) B4194317
theorem B4655819 : Blo 1224430 4655819 := bstep (se 1 (by rfl) ⟨3491864, by rfl⟩ : syracuseStep 4655819 = 6983729) B6983729
theorem B1837835 : Blo 1224430 1837835 := bstep (se 1 (by rfl) ⟨1378376, by rfl⟩ : syracuseStep 1837835 = 2756753) B2756753
theorem B1379083 : Blo 1224430 1379083 := bstep (se 1 (by rfl) ⟨1034312, by rfl⟩ : syracuseStep 1379083 = 2068625) B2068625
theorem B1837847 : Blo 1224430 1837847 := bstep (se 1 (by rfl) ⟨1378385, by rfl⟩ : syracuseStep 1837847 = 2756771) B2756771
theorem B63720245 : Blo 1224430 63720245 := bstep (se 5 (by rfl) ⟨2986886, by rfl⟩ : syracuseStep 63720245 = 5973773) B5973773
theorem B2755403 : Blo 1224430 2755403 := bstep (se 1 (by rfl) ⟨2066552, by rfl⟩ : syracuseStep 2755403 = 4133105) B4133105
theorem B2067275 : Blo 1224430 2067275 := bstep (se 1 (by rfl) ⟨1550456, by rfl⟩ : syracuseStep 2067275 = 3100913) B3100913
theorem B1837913 : Blo 1224430 1837913 := bstep (se 2 (by rfl) ⟨689217, by rfl⟩ : syracuseStep 1837913 = 1378435) B1378435
theorem B7457629 : Blo 1224430 7457629 := bstep (se 3 (by rfl) ⟨1398305, by rfl⟩ : syracuseStep 7457629 = 2796611) B2796611
theorem B9431909 : Blo 1224430 9431909 := bstep (se 4 (by rfl) ⟨884241, by rfl⟩ : syracuseStep 9431909 = 1768483) B1768483
theorem B30231397 : Blo 1224430 30231397 := bstep (se 4 (by rfl) ⟨2834193, by rfl⟩ : syracuseStep 30231397 = 5668387) B5668387
theorem B1379191 : Blo 1224430 1379191 := bstep (se 1 (by rfl) ⟨1034393, by rfl⟩ : syracuseStep 1379191 = 2068787) B2068787
theorem B2755457 : Blo 1224430 2755457 := bstep (se 2 (by rfl) ⟨1033296, by rfl⟩ : syracuseStep 2755457 = 2066593) B2066593
theorem B2067403 : Blo 1224430 2067403 := bstep (se 1 (by rfl) ⟨1550552, by rfl⟩ : syracuseStep 2067403 = 3101105) B3101105
theorem B1838027 : Blo 1224430 1838027 := bstep (se 1 (by rfl) ⟨1378520, by rfl⟩ : syracuseStep 1838027 = 2757041) B2757041
theorem B1551307 : Blo 1224430 1551307 := bstep (se 1 (by rfl) ⟨1163480, by rfl⟩ : syracuseStep 1551307 = 2326961) B2326961
theorem B1838039 : Blo 1224430 1838039 := bstep (se 1 (by rfl) ⟨1378529, by rfl⟩ : syracuseStep 1838039 = 2757059) B2757059
theorem B6286297 : Blo 1224430 6286297 := bstep (se 2 (by rfl) ⟨2357361, by rfl⟩ : syracuseStep 6286297 = 4714723) B4714723
theorem B1838105 : Blo 1224430 1838105 := bstep (se 2 (by rfl) ⟨689289, by rfl⟩ : syracuseStep 1838105 = 1378579) B1378579
theorem B1379371 : Blo 1224430 1379371 := bstep (se 1 (by rfl) ⟨1034528, by rfl⟩ : syracuseStep 1379371 = 2069057) B2069057
theorem B8834113 : Blo 1224430 8834113 := bstep (se 2 (by rfl) ⟨3312792, by rfl⟩ : syracuseStep 8834113 = 6625585) B6625585
theorem B9301067 : Blo 1224430 9301067 := bstep (se 1 (by rfl) ⟨6975800, by rfl⟩ : syracuseStep 9301067 = 13951601) B13951601
theorem B2755673 : Blo 1224430 2755673 := bstep (se 2 (by rfl) ⟨1033377, by rfl⟩ : syracuseStep 2755673 = 2066755) B2066755
theorem B2067545 : Blo 1224430 2067545 := bstep (se 2 (by rfl) ⟨775329, by rfl⟩ : syracuseStep 2067545 = 1550659) B1550659
theorem B1838219 : Blo 1224430 1838219 := bstep (se 1 (by rfl) ⟨1378664, by rfl⟩ : syracuseStep 1838219 = 2757329) B2757329
theorem B1838231 : Blo 1224430 1838231 := bstep (se 1 (by rfl) ⟨1378673, by rfl⟩ : syracuseStep 1838231 = 2757347) B2757347
theorem B1379479 : Blo 1224430 1379479 := bstep (se 1 (by rfl) ⟨1034609, by rfl⟩ : syracuseStep 1379479 = 2069219) B2069219
theorem B2755763 : Blo 1224430 2755763 := bstep (se 1 (by rfl) ⟨2066822, by rfl⟩ : syracuseStep 2755763 = 4133645) B4133645
theorem B2755799 : Blo 1224430 2755799 := bstep (se 1 (by rfl) ⟨2066849, by rfl⟩ : syracuseStep 2755799 = 4133699) B4133699
theorem B1551575 : Blo 1224430 1551575 := bstep (se 1 (by rfl) ⟨1163681, by rfl⟩ : syracuseStep 1551575 = 2327363) B2327363
theorem B2067673 : Blo 1224430 2067673 := bstep (se 2 (by rfl) ⟨775377, by rfl⟩ : syracuseStep 2067673 = 1550755) B1550755
theorem B1838297 : Blo 1224430 1838297 := bstep (se 2 (by rfl) ⟨689361, by rfl⟩ : syracuseStep 1838297 = 1378723) B1378723
theorem B3312857 : Blo 1224430 3312857 := bstep (se 2 (by rfl) ⟨1242321, by rfl⟩ : syracuseStep 3312857 = 2484643) B2484643
theorem B1838411 : Blo 1224430 1838411 := bstep (se 1 (by rfl) ⟨1378808, by rfl⟩ : syracuseStep 1838411 = 2757617) B2757617
theorem B1379659 : Blo 1224430 1379659 := bstep (se 1 (by rfl) ⟨1034744, by rfl⟩ : syracuseStep 1379659 = 2069489) B2069489
theorem B1838423 : Blo 1224430 1838423 := bstep (se 1 (by rfl) ⟨1378817, by rfl⟩ : syracuseStep 1838423 = 2757635) B2757635
theorem B4656473 : Blo 1224430 4656473 := bstep (se 2 (by rfl) ⟨1746177, by rfl⟩ : syracuseStep 4656473 = 3492355) B3492355
theorem B2485633 : Blo 1224430 2485633 := bstep (se 2 (by rfl) ⟨932112, by rfl⟩ : syracuseStep 2485633 = 1864225) B1864225
theorem B2755979 : Blo 1224430 2755979 := bstep (se 1 (by rfl) ⟨2066984, by rfl⟩ : syracuseStep 2755979 = 4133969) B4133969
theorem B1838489 : Blo 1224430 1838489 := bstep (se 2 (by rfl) ⟨689433, by rfl⟩ : syracuseStep 1838489 = 1378867) B1378867
theorem B2756033 : Blo 1224430 2756033 := bstep (se 2 (by rfl) ⟨1033512, by rfl⟩ : syracuseStep 2756033 = 2067025) B2067025
theorem B1838603 : Blo 1224430 1838603 := bstep (se 1 (by rfl) ⟨1378952, by rfl⟩ : syracuseStep 1838603 = 2757905) B2757905
theorem B1863191 : Blo 1224430 1863191 := bstep (se 1 (by rfl) ⟨1397393, by rfl⟩ : syracuseStep 1863191 = 2794787) B2794787
theorem B1838615 : Blo 1224430 1838615 := bstep (se 1 (by rfl) ⟨1378961, by rfl⟩ : syracuseStep 1838615 = 2757923) B2757923
theorem B1838681 : Blo 1224430 1838681 := bstep (se 2 (by rfl) ⟨689505, by rfl⟩ : syracuseStep 1838681 = 1379011) B1379011
theorem B2756249 : Blo 1224430 2756249 := bstep (se 2 (by rfl) ⟨1033593, by rfl⟩ : syracuseStep 2756249 = 2067187) B2067187
theorem B2616985 : Blo 1224430 2616985 := bstep (se 2 (by rfl) ⟨981369, by rfl⟩ : syracuseStep 2616985 = 1962739) B1962739
theorem B1838795 : Blo 1224430 1838795 := bstep (se 1 (by rfl) ⟨1379096, by rfl⟩ : syracuseStep 1838795 = 2758193) B2758193
theorem B1838807 : Blo 1224430 1838807 := bstep (se 1 (by rfl) ⟨1379105, by rfl⟩ : syracuseStep 1838807 = 2758211) B2758211
theorem B2756339 : Blo 1224430 2756339 := bstep (se 1 (by rfl) ⟨2067254, by rfl⟩ : syracuseStep 2756339 = 4134509) B4134509
theorem B1224439 : Blo 1224430 1224439 := bstep (se 1 (by rfl) ⟨918329, by rfl⟩ : syracuseStep 1224439 = 1836659) B1836659
theorem B1224459 : Blo 1224430 1224459 := bstep (se 1 (by rfl) ⟨918344, by rfl⟩ : syracuseStep 1224459 = 1836689) B1836689
theorem B1224471 : Blo 1224430 1224471 := bstep (se 1 (by rfl) ⟨918353, by rfl⟩ : syracuseStep 1224471 = 1836707) B1836707
theorem B2756375 : Blo 1224430 2756375 := bstep (se 1 (by rfl) ⟨2067281, by rfl⟩ : syracuseStep 2756375 = 4134563) B4134563
theorem B2068247 : Blo 1224430 2068247 := bstep (se 1 (by rfl) ⟨1551185, by rfl⟩ : syracuseStep 2068247 = 3102371) B3102371
theorem B1838873 : Blo 1224430 1838873 := bstep (se 2 (by rfl) ⟨689577, by rfl⟩ : syracuseStep 1838873 = 1379155) B1379155
theorem B1224491 : Blo 1224430 1224491 := bstep (se 1 (by rfl) ⟨918368, by rfl⟩ : syracuseStep 1224491 = 1836737) B1836737
theorem B1224503 : Blo 1224430 1224503 := bstep (se 1 (by rfl) ⟨918377, by rfl⟩ : syracuseStep 1224503 = 1836755) B1836755
theorem B4132673 : Blo 1224430 4132673 := bstep (se 2 (by rfl) ⟨1549752, by rfl⟩ : syracuseStep 4132673 = 3099505) B3099505
theorem B1224523 : Blo 1224430 1224523 := bstep (se 1 (by rfl) ⟨918392, by rfl⟩ : syracuseStep 1224523 = 1836785) B1836785
theorem B1224535 : Blo 1224430 1224535 := bstep (se 1 (by rfl) ⟨918401, by rfl⟩ : syracuseStep 1224535 = 1836803) B1836803
theorem B1224555 : Blo 1224430 1224555 := bstep (se 1 (by rfl) ⟨918416, by rfl⟩ : syracuseStep 1224555 = 1836833) B1836833
theorem B1224567 : Blo 1224430 1224567 := bstep (se 1 (by rfl) ⟨918425, by rfl⟩ : syracuseStep 1224567 = 1836851) B1836851
theorem B1224587 : Blo 1224430 1224587 := bstep (se 1 (by rfl) ⟨918440, by rfl⟩ : syracuseStep 1224587 = 1836881) B1836881
theorem B1838987 : Blo 1224430 1838987 := bstep (se 1 (by rfl) ⟨1379240, by rfl⟩ : syracuseStep 1838987 = 2758481) B2758481
theorem B1224599 : Blo 1224430 1224599 := bstep (se 1 (by rfl) ⟨918449, by rfl⟩ : syracuseStep 1224599 = 1836899) B1836899
theorem B2068375 : Blo 1224430 2068375 := bstep (se 1 (by rfl) ⟨1551281, by rfl⟩ : syracuseStep 2068375 = 3102563) B3102563
theorem B1838999 : Blo 1224430 1838999 := bstep (se 1 (by rfl) ⟨1379249, by rfl⟩ : syracuseStep 1838999 = 2758499) B2758499
theorem B1224619 : Blo 1224430 1224619 := bstep (se 1 (by rfl) ⟨918464, by rfl⟩ : syracuseStep 1224619 = 1836929) B1836929
theorem B1224631 : Blo 1224430 1224631 := bstep (se 1 (by rfl) ⟨918473, by rfl⟩ : syracuseStep 1224631 = 1836947) B1836947
theorem B1224651 : Blo 1224430 1224651 := bstep (se 1 (by rfl) ⟨918488, by rfl⟩ : syracuseStep 1224651 = 1836977) B1836977
theorem B3100619 : Blo 1224430 3100619 := bstep (se 1 (by rfl) ⟨2325464, by rfl⟩ : syracuseStep 3100619 = 4650929) B4650929
theorem B2756555 : Blo 1224430 2756555 := bstep (se 1 (by rfl) ⟨2067416, by rfl⟩ : syracuseStep 2756555 = 4134833) B4134833
theorem B1224663 : Blo 1224430 1224663 := bstep (se 1 (by rfl) ⟨918497, by rfl⟩ : syracuseStep 1224663 = 1836995) B1836995
theorem B1839065 : Blo 1224430 1839065 := bstep (se 2 (by rfl) ⟨689649, by rfl⟩ : syracuseStep 1839065 = 1379299) B1379299
theorem B1224683 : Blo 1224430 1224683 := bstep (se 1 (by rfl) ⟨918512, by rfl⟩ : syracuseStep 1224683 = 1837025) B1837025
theorem B1224695 : Blo 1224430 1224695 := bstep (se 1 (by rfl) ⟨918521, by rfl⟩ : syracuseStep 1224695 = 1837043) B1837043
theorem B2756609 : Blo 1224430 2756609 := bstep (se 2 (by rfl) ⟨1033728, by rfl⟩ : syracuseStep 2756609 = 2067457) B2067457
theorem B1224715 : Blo 1224430 1224715 := bstep (se 1 (by rfl) ⟨918536, by rfl⟩ : syracuseStep 1224715 = 1837073) B1837073
theorem B1224727 : Blo 1224430 1224727 := bstep (se 1 (by rfl) ⟨918545, by rfl⟩ : syracuseStep 1224727 = 1837091) B1837091
theorem B1224747 : Blo 1224430 1224747 := bstep (se 1 (by rfl) ⟨918560, by rfl⟩ : syracuseStep 1224747 = 1837121) B1837121
theorem B1224759 : Blo 1224430 1224759 := bstep (se 1 (by rfl) ⟨918569, by rfl⟩ : syracuseStep 1224759 = 1837139) B1837139
theorem B1224779 : Blo 1224430 1224779 := bstep (se 1 (by rfl) ⟨918584, by rfl⟩ : syracuseStep 1224779 = 1837169) B1837169
theorem B1839179 : Blo 1224430 1839179 := bstep (se 1 (by rfl) ⟨1379384, by rfl⟩ : syracuseStep 1839179 = 2758769) B2758769
theorem B1224791 : Blo 1224430 1224791 := bstep (se 1 (by rfl) ⟨918593, by rfl⟩ : syracuseStep 1224791 = 1837187) B1837187
theorem B1839191 : Blo 1224430 1839191 := bstep (se 1 (by rfl) ⟨1379393, by rfl⟩ : syracuseStep 1839191 = 2758787) B2758787
theorem B1962073 : Blo 1224430 1962073 := bstep (se 2 (by rfl) ⟨735777, by rfl⟩ : syracuseStep 1962073 = 1471555) B1471555
theorem B9310301 : Blo 1224430 9310301 := bstep (se 3 (by rfl) ⟨1745681, by rfl⟩ : syracuseStep 9310301 = 3491363) B3491363
theorem B1224811 : Blo 1224430 1224811 := bstep (se 1 (by rfl) ⟨918608, by rfl⟩ : syracuseStep 1224811 = 1837217) B1837217
theorem B1224823 : Blo 1224430 1224823 := bstep (se 1 (by rfl) ⟨918617, by rfl⟩ : syracuseStep 1224823 = 1837235) B1837235
theorem B6205571 : Blo 1224430 6205571 := bstep (se 1 (by rfl) ⟨4654178, by rfl⟩ : syracuseStep 6205571 = 9308357) B9308357
theorem B1224843 : Blo 1224430 1224843 := bstep (se 1 (by rfl) ⟨918632, by rfl⟩ : syracuseStep 1224843 = 1837265) B1837265
theorem B1224855 : Blo 1224430 1224855 := bstep (se 1 (by rfl) ⟨918641, by rfl⟩ : syracuseStep 1224855 = 1837283) B1837283
theorem B1839257 : Blo 1224430 1839257 := bstep (se 2 (by rfl) ⟨689721, by rfl⟩ : syracuseStep 1839257 = 1379443) B1379443
theorem B1224875 : Blo 1224430 1224875 := bstep (se 1 (by rfl) ⟨918656, by rfl⟩ : syracuseStep 1224875 = 1837313) B1837313
theorem B1224887 : Blo 1224430 1224887 := bstep (se 1 (by rfl) ⟨918665, by rfl⟩ : syracuseStep 1224887 = 1837331) B1837331
theorem B1224907 : Blo 1224430 1224907 := bstep (se 1 (by rfl) ⟨918680, by rfl⟩ : syracuseStep 1224907 = 1837361) B1837361
theorem B1224919 : Blo 1224430 1224919 := bstep (se 1 (by rfl) ⟨918689, by rfl⟩ : syracuseStep 1224919 = 1837379) B1837379
theorem B2756825 : Blo 1224430 2756825 := bstep (se 2 (by rfl) ⟨1033809, by rfl⟩ : syracuseStep 2756825 = 2067619) B2067619
theorem B4190429 : Blo 1224430 4190429 := bstep (se 3 (by rfl) ⟨785705, by rfl⟩ : syracuseStep 4190429 = 1571411) B1571411
theorem B1224939 : Blo 1224430 1224939 := bstep (se 1 (by rfl) ⟨918704, by rfl⟩ : syracuseStep 1224939 = 1837409) B1837409
theorem B1224951 : Blo 1224430 1224951 := bstep (se 1 (by rfl) ⟨918713, by rfl⟩ : syracuseStep 1224951 = 1837427) B1837427
theorem B14151941 : Blo 1224430 14151941 := bstep (se 4 (by rfl) ⟨1326744, by rfl⟩ : syracuseStep 14151941 = 2653489) B2653489
theorem B1224971 : Blo 1224430 1224971 := bstep (se 1 (by rfl) ⟨918728, by rfl⟩ : syracuseStep 1224971 = 1837457) B1837457
theorem B1839371 : Blo 1224430 1839371 := bstep (se 1 (by rfl) ⟨1379528, by rfl⟩ : syracuseStep 1839371 = 2759057) B2759057
theorem B1224983 : Blo 1224430 1224983 := bstep (se 1 (by rfl) ⟨918737, by rfl⟩ : syracuseStep 1224983 = 1837475) B1837475
theorem B1839383 : Blo 1224430 1839383 := bstep (se 1 (by rfl) ⟨1379537, by rfl⟩ : syracuseStep 1839383 = 2759075) B2759075
theorem B1225003 : Blo 1224430 1225003 := bstep (se 1 (by rfl) ⟨918752, by rfl⟩ : syracuseStep 1225003 = 1837505) B1837505
theorem B6983981 : Blo 1224430 6983981 := bstep (se 3 (by rfl) ⟨1309496, by rfl⟩ : syracuseStep 6983981 = 2618993) B2618993
theorem B2756915 : Blo 1224430 2756915 := bstep (se 1 (by rfl) ⟨2067686, by rfl⟩ : syracuseStep 2756915 = 4135373) B4135373
theorem B1225015 : Blo 1224430 1225015 := bstep (se 1 (by rfl) ⟨918761, by rfl⟩ : syracuseStep 1225015 = 1837523) B1837523
theorem B1225035 : Blo 1224430 1225035 := bstep (se 1 (by rfl) ⟨918776, by rfl⟩ : syracuseStep 1225035 = 1837553) B1837553
theorem B1225047 : Blo 1224430 1225047 := bstep (se 1 (by rfl) ⟨918785, by rfl⟩ : syracuseStep 1225047 = 1837571) B1837571
theorem B2756951 : Blo 1224430 2756951 := bstep (se 1 (by rfl) ⟨2067713, by rfl⟩ : syracuseStep 2756951 = 4135427) B4135427
theorem B1839449 : Blo 1224430 1839449 := bstep (se 2 (by rfl) ⟨689793, by rfl⟩ : syracuseStep 1839449 = 1379587) B1379587
theorem B4133213 : Blo 1224430 4133213 := bstep (se 3 (by rfl) ⟨774977, by rfl⟩ : syracuseStep 4133213 = 1549955) B1549955
theorem B1225067 : Blo 1224430 1225067 := bstep (se 1 (by rfl) ⟨918800, by rfl⟩ : syracuseStep 1225067 = 1837601) B1837601
theorem B23572853 : Blo 1224430 23572853 := bstep (se 5 (by rfl) ⟨1104977, by rfl⟩ : syracuseStep 23572853 = 2209955) B2209955
theorem B1225079 : Blo 1224430 1225079 := bstep (se 1 (by rfl) ⟨918809, by rfl⟩ : syracuseStep 1225079 = 1837619) B1837619
theorem B1225099 : Blo 1224430 1225099 := bstep (se 1 (by rfl) ⟨918824, by rfl⟩ : syracuseStep 1225099 = 1837649) B1837649
theorem B1225111 : Blo 1224430 1225111 := bstep (se 1 (by rfl) ⟨918833, by rfl⟩ : syracuseStep 1225111 = 1837667) B1837667
theorem B1225131 : Blo 1224430 1225131 := bstep (se 1 (by rfl) ⟨918848, by rfl⟩ : syracuseStep 1225131 = 1837697) B1837697
theorem B1225143 : Blo 1224430 1225143 := bstep (se 1 (by rfl) ⟨918857, by rfl⟩ : syracuseStep 1225143 = 1837715) B1837715
theorem B1225163 : Blo 1224430 1225163 := bstep (se 1 (by rfl) ⟨918872, by rfl⟩ : syracuseStep 1225163 = 1837745) B1837745
theorem B1839563 : Blo 1224430 1839563 := bstep (se 1 (by rfl) ⟨1379672, by rfl⟩ : syracuseStep 1839563 = 2759345) B2759345
theorem B1225175 : Blo 1224430 1225175 := bstep (se 1 (by rfl) ⟨918881, by rfl⟩ : syracuseStep 1225175 = 1837763) B1837763
theorem B1839575 : Blo 1224430 1839575 := bstep (se 1 (by rfl) ⟨1379681, by rfl⟩ : syracuseStep 1839575 = 2759363) B2759363
theorem B1225195 : Blo 1224430 1225195 := bstep (se 1 (by rfl) ⟨918896, by rfl⟩ : syracuseStep 1225195 = 1837793) B1837793
theorem B1225207 : Blo 1224430 1225207 := bstep (se 1 (by rfl) ⟨918905, by rfl⟩ : syracuseStep 1225207 = 1837811) B1837811
theorem B1225227 : Blo 1224430 1225227 := bstep (se 1 (by rfl) ⟨918920, by rfl⟩ : syracuseStep 1225227 = 1837841) B1837841
theorem B2757131 : Blo 1224430 2757131 := bstep (se 1 (by rfl) ⟨2067848, by rfl⟩ : syracuseStep 2757131 = 4135697) B4135697
theorem B2069003 : Blo 1224430 2069003 := bstep (se 1 (by rfl) ⟨1551752, by rfl⟩ : syracuseStep 2069003 = 3103505) B3103505
theorem B1225239 : Blo 1224430 1225239 := bstep (se 1 (by rfl) ⟨918929, by rfl⟩ : syracuseStep 1225239 = 1837859) B1837859
theorem B1839641 : Blo 1224430 1839641 := bstep (se 2 (by rfl) ⟨689865, by rfl⟩ : syracuseStep 1839641 = 1379731) B1379731
theorem B1225259 : Blo 1224430 1225259 := bstep (se 1 (by rfl) ⟨918944, by rfl⟩ : syracuseStep 1225259 = 1837889) B1837889
theorem B1225271 : Blo 1224430 1225271 := bstep (se 1 (by rfl) ⟨918953, by rfl⟩ : syracuseStep 1225271 = 1837907) B1837907
theorem B2757185 : Blo 1224430 2757185 := bstep (se 2 (by rfl) ⟨1033944, by rfl⟩ : syracuseStep 2757185 = 2067889) B2067889
theorem B1225291 : Blo 1224430 1225291 := bstep (se 1 (by rfl) ⟨918968, by rfl⟩ : syracuseStep 1225291 = 1837937) B1837937
theorem B1225303 : Blo 1224430 1225303 := bstep (se 1 (by rfl) ⟨918977, by rfl⟩ : syracuseStep 1225303 = 1837955) B1837955
theorem B1225323 : Blo 1224430 1225323 := bstep (se 1 (by rfl) ⟨918992, by rfl⟩ : syracuseStep 1225323 = 1837985) B1837985
theorem B1225335 : Blo 1224430 1225335 := bstep (se 1 (by rfl) ⟨919001, by rfl⟩ : syracuseStep 1225335 = 1838003) B1838003
theorem B1225355 : Blo 1224430 1225355 := bstep (se 1 (by rfl) ⟨919016, by rfl⟩ : syracuseStep 1225355 = 1838033) B1838033
theorem B2069131 : Blo 1224430 2069131 := bstep (se 1 (by rfl) ⟨1551848, by rfl⟩ : syracuseStep 2069131 = 3103697) B3103697
theorem B1225367 : Blo 1224430 1225367 := bstep (se 1 (by rfl) ⟨919025, by rfl⟩ : syracuseStep 1225367 = 1838051) B1838051
theorem B1225387 : Blo 1224430 1225387 := bstep (se 1 (by rfl) ⟨919040, by rfl⟩ : syracuseStep 1225387 = 1838081) B1838081
theorem B1225399 : Blo 1224430 1225399 := bstep (se 1 (by rfl) ⟨919049, by rfl⟩ : syracuseStep 1225399 = 1838099) B1838099
theorem B1225419 : Blo 1224430 1225419 := bstep (se 1 (by rfl) ⟨919064, by rfl⟩ : syracuseStep 1225419 = 1838129) B1838129
theorem B1225431 : Blo 1224430 1225431 := bstep (se 1 (by rfl) ⟨919073, by rfl⟩ : syracuseStep 1225431 = 1838147) B1838147
theorem B1225451 : Blo 1224430 1225451 := bstep (se 1 (by rfl) ⟨919088, by rfl⟩ : syracuseStep 1225451 = 1838177) B1838177
theorem B1225463 : Blo 1224430 1225463 := bstep (se 1 (by rfl) ⟨919097, by rfl⟩ : syracuseStep 1225463 = 1838195) B1838195
theorem B1225483 : Blo 1224430 1225483 := bstep (se 1 (by rfl) ⟨919112, by rfl⟩ : syracuseStep 1225483 = 1838225) B1838225
theorem B1225495 : Blo 1224430 1225495 := bstep (se 1 (by rfl) ⟨919121, by rfl⟩ : syracuseStep 1225495 = 1838243) B1838243
theorem B2757401 : Blo 1224430 2757401 := bstep (se 2 (by rfl) ⟨1034025, by rfl⟩ : syracuseStep 2757401 = 2068051) B2068051
theorem B2069273 : Blo 1224430 2069273 := bstep (se 2 (by rfl) ⟨775977, by rfl⟩ : syracuseStep 2069273 = 1551955) B1551955
theorem B8835875 : Blo 1224430 8835875 := bstep (se 1 (by rfl) ⟨6626906, by rfl⟩ : syracuseStep 8835875 = 13253813) B13253813
theorem B1225515 : Blo 1224430 1225515 := bstep (se 1 (by rfl) ⟨919136, by rfl⟩ : syracuseStep 1225515 = 1838273) B1838273
theorem B1225527 : Blo 1224430 1225527 := bstep (se 1 (by rfl) ⟨919145, by rfl⟩ : syracuseStep 1225527 = 1838291) B1838291
theorem B5231425 : Blo 1224430 5231425 := bstep (se 2 (by rfl) ⟨1961784, by rfl⟩ : syracuseStep 5231425 = 3923569) B3923569
theorem B1225547 : Blo 1224430 1225547 := bstep (se 1 (by rfl) ⟨919160, by rfl⟩ : syracuseStep 1225547 = 1838321) B1838321
theorem B1225559 : Blo 1224430 1225559 := bstep (se 1 (by rfl) ⟨919169, by rfl⟩ : syracuseStep 1225559 = 1838339) B1838339
theorem B1225579 : Blo 1224430 1225579 := bstep (se 1 (by rfl) ⟨919184, by rfl⟩ : syracuseStep 1225579 = 1838369) B1838369
theorem B2757491 : Blo 1224430 2757491 := bstep (se 1 (by rfl) ⟨2068118, by rfl⟩ : syracuseStep 2757491 = 4136237) B4136237
theorem B1225591 : Blo 1224430 1225591 := bstep (se 1 (by rfl) ⟨919193, by rfl⟩ : syracuseStep 1225591 = 1838387) B1838387
theorem B1225611 : Blo 1224430 1225611 := bstep (se 1 (by rfl) ⟨919208, by rfl⟩ : syracuseStep 1225611 = 1838417) B1838417
theorem B3101591 : Blo 1224430 3101591 := bstep (se 1 (by rfl) ⟨2326193, by rfl⟩ : syracuseStep 3101591 = 4652387) B4652387
theorem B2757527 : Blo 1224430 2757527 := bstep (se 1 (by rfl) ⟨2068145, by rfl⟩ : syracuseStep 2757527 = 4136291) B4136291
theorem B1225623 : Blo 1224430 1225623 := bstep (se 1 (by rfl) ⟨919217, by rfl⟩ : syracuseStep 1225623 = 1838435) B1838435
theorem B2069401 : Blo 1224430 2069401 := bstep (se 2 (by rfl) ⟨776025, by rfl⟩ : syracuseStep 2069401 = 1552051) B1552051
theorem B1225643 : Blo 1224430 1225643 := bstep (se 1 (by rfl) ⟨919232, by rfl⟩ : syracuseStep 1225643 = 1838465) B1838465
theorem B1225655 : Blo 1224430 1225655 := bstep (se 1 (by rfl) ⟨919241, by rfl⟩ : syracuseStep 1225655 = 1838483) B1838483
theorem B1225675 : Blo 1224430 1225675 := bstep (se 1 (by rfl) ⟨919256, by rfl⟩ : syracuseStep 1225675 = 1838513) B1838513
theorem B1225687 : Blo 1224430 1225687 := bstep (se 1 (by rfl) ⟨919265, by rfl⟩ : syracuseStep 1225687 = 1838531) B1838531
theorem B1225707 : Blo 1224430 1225707 := bstep (se 1 (by rfl) ⟨919280, by rfl⟩ : syracuseStep 1225707 = 1838561) B1838561
theorem B1225719 : Blo 1224430 1225719 := bstep (se 1 (by rfl) ⟨919289, by rfl⟩ : syracuseStep 1225719 = 1838579) B1838579
theorem B4649987 : Blo 1224430 4649987 := bstep (se 1 (by rfl) ⟨3487490, by rfl⟩ : syracuseStep 4649987 = 6974981) B6974981
theorem B1225739 : Blo 1224430 1225739 := bstep (se 1 (by rfl) ⟨919304, by rfl⟩ : syracuseStep 1225739 = 1838609) B1838609
theorem B1225751 : Blo 1224430 1225751 := bstep (se 1 (by rfl) ⟨919313, by rfl⟩ : syracuseStep 1225751 = 1838627) B1838627
theorem B1225771 : Blo 1224430 1225771 := bstep (se 1 (by rfl) ⟨919328, by rfl⟩ : syracuseStep 1225771 = 1838657) B1838657
theorem B3724339 : Blo 1224430 3724339 := bstep (se 1 (by rfl) ⟨2793254, by rfl⟩ : syracuseStep 3724339 = 5586509) B5586509
theorem B1225783 : Blo 1224430 1225783 := bstep (se 1 (by rfl) ⟨919337, by rfl⟩ : syracuseStep 1225783 = 1838675) B1838675
theorem B2757707 : Blo 1224430 2757707 := bstep (se 1 (by rfl) ⟨2068280, by rfl⟩ : syracuseStep 2757707 = 4136561) B4136561
theorem B1225803 : Blo 1224430 1225803 := bstep (se 1 (by rfl) ⟨919352, by rfl⟩ : syracuseStep 1225803 = 1838705) B1838705
theorem B1225815 : Blo 1224430 1225815 := bstep (se 1 (by rfl) ⟨919361, by rfl⟩ : syracuseStep 1225815 = 1838723) B1838723
theorem B1225835 : Blo 1224430 1225835 := bstep (se 1 (by rfl) ⟨919376, by rfl⟩ : syracuseStep 1225835 = 1838753) B1838753
theorem B1225847 : Blo 1224430 1225847 := bstep (se 1 (by rfl) ⟨919385, by rfl⟩ : syracuseStep 1225847 = 1838771) B1838771
theorem B2757761 : Blo 1224430 2757761 := bstep (se 2 (by rfl) ⟨1034160, by rfl⟩ : syracuseStep 2757761 = 2068321) B2068321
theorem B10466435 : Blo 1224430 10466435 := bstep (se 1 (by rfl) ⟨7849826, by rfl⟩ : syracuseStep 10466435 = 15699653) B15699653
theorem B4715651 : Blo 1224430 4715651 := bstep (se 1 (by rfl) ⟨3536738, by rfl⟩ : syracuseStep 4715651 = 7073477) B7073477
theorem B1225867 : Blo 1224430 1225867 := bstep (se 1 (by rfl) ⟨919400, by rfl⟩ : syracuseStep 1225867 = 1838801) B1838801
theorem B1225879 : Blo 1224430 1225879 := bstep (se 1 (by rfl) ⟨919409, by rfl⟩ : syracuseStep 1225879 = 1838819) B1838819
theorem B1225899 : Blo 1224430 1225899 := bstep (se 1 (by rfl) ⟨919424, by rfl⟩ : syracuseStep 1225899 = 1838849) B1838849
theorem B6976691 : Blo 1224430 6976691 := bstep (se 1 (by rfl) ⟨5232518, by rfl⟩ : syracuseStep 6976691 = 10465037) B10465037
theorem B1225911 : Blo 1224430 1225911 := bstep (se 1 (by rfl) ⟨919433, by rfl⟩ : syracuseStep 1225911 = 1838867) B1838867
theorem B2651339 : Blo 1224430 2651339 := bstep (se 1 (by rfl) ⟨1988504, by rfl⟩ : syracuseStep 2651339 = 3977009) B3977009
theorem B1225931 : Blo 1224430 1225931 := bstep (se 1 (by rfl) ⟨919448, by rfl⟩ : syracuseStep 1225931 = 1838897) B1838897
theorem B1225943 : Blo 1224430 1225943 := bstep (se 1 (by rfl) ⟨919457, by rfl⟩ : syracuseStep 1225943 = 1838915) B1838915
theorem B1225963 : Blo 1224430 1225963 := bstep (se 1 (by rfl) ⟨919472, by rfl⟩ : syracuseStep 1225963 = 1838945) B1838945
theorem B1225975 : Blo 1224430 1225975 := bstep (se 1 (by rfl) ⟨919481, by rfl⟩ : syracuseStep 1225975 = 1838963) B1838963
theorem B1225995 : Blo 1224430 1225995 := bstep (se 1 (by rfl) ⟨919496, by rfl⟩ : syracuseStep 1225995 = 1838993) B1838993
theorem B1226007 : Blo 1224430 1226007 := bstep (se 1 (by rfl) ⟨919505, by rfl⟩ : syracuseStep 1226007 = 1839011) B1839011
theorem B1226027 : Blo 1224430 1226027 := bstep (se 1 (by rfl) ⟨919520, by rfl⟩ : syracuseStep 1226027 = 1839041) B1839041
theorem B1226039 : Blo 1224430 1226039 := bstep (se 1 (by rfl) ⟨919529, by rfl⟩ : syracuseStep 1226039 = 1839059) B1839059
theorem B1226059 : Blo 1224430 1226059 := bstep (se 1 (by rfl) ⟨919544, by rfl⟩ : syracuseStep 1226059 = 1839089) B1839089
theorem B1226071 : Blo 1224430 1226071 := bstep (se 1 (by rfl) ⟨919553, by rfl⟩ : syracuseStep 1226071 = 1839107) B1839107
theorem B2757977 : Blo 1224430 2757977 := bstep (se 2 (by rfl) ⟨1034241, by rfl⟩ : syracuseStep 2757977 = 2068483) B2068483
theorem B1226091 : Blo 1224430 1226091 := bstep (se 1 (by rfl) ⟨919568, by rfl⟩ : syracuseStep 1226091 = 1839137) B1839137
theorem B1226103 : Blo 1224430 1226103 := bstep (se 1 (by rfl) ⟨919577, by rfl⟩ : syracuseStep 1226103 = 1839155) B1839155
theorem B1226123 : Blo 1224430 1226123 := bstep (se 1 (by rfl) ⟨919592, by rfl⟩ : syracuseStep 1226123 = 1839185) B1839185
theorem B5232023 : Blo 1224430 5232023 := bstep (se 1 (by rfl) ⟨3924017, by rfl⟩ : syracuseStep 5232023 = 7848035) B7848035
theorem B1226135 : Blo 1224430 1226135 := bstep (se 1 (by rfl) ⟨919601, by rfl⟩ : syracuseStep 1226135 = 1839203) B1839203
theorem B1226155 : Blo 1224430 1226155 := bstep (se 1 (by rfl) ⟨919616, by rfl⟩ : syracuseStep 1226155 = 1839233) B1839233
theorem B2758067 : Blo 1224430 2758067 := bstep (se 1 (by rfl) ⟨2068550, by rfl⟩ : syracuseStep 2758067 = 4137101) B4137101
theorem B13964723 : Blo 1224430 13964723 := bstep (se 1 (by rfl) ⟨10473542, by rfl⟩ : syracuseStep 13964723 = 20947085) B20947085
theorem B1226167 : Blo 1224430 1226167 := bstep (se 1 (by rfl) ⟨919625, by rfl⟩ : syracuseStep 1226167 = 1839251) B1839251
theorem B4650443 : Blo 1224430 4650443 := bstep (se 1 (by rfl) ⟨3487832, by rfl⟩ : syracuseStep 4650443 = 6975665) B6975665
theorem B4134347 : Blo 1224430 4134347 := bstep (se 1 (by rfl) ⟨3100760, by rfl⟩ : syracuseStep 4134347 = 6201521) B6201521
theorem B1226187 : Blo 1224430 1226187 := bstep (se 1 (by rfl) ⟨919640, by rfl⟩ : syracuseStep 1226187 = 1839281) B1839281
theorem B2758103 : Blo 1224430 2758103 := bstep (se 1 (by rfl) ⟨2068577, by rfl⟩ : syracuseStep 2758103 = 4137155) B4137155
theorem B1226199 : Blo 1224430 1226199 := bstep (se 1 (by rfl) ⟨919649, by rfl⟩ : syracuseStep 1226199 = 1839299) B1839299
theorem B1226219 : Blo 1224430 1226219 := bstep (se 1 (by rfl) ⟨919664, by rfl⟩ : syracuseStep 1226219 = 1839329) B1839329
theorem B1308151 : Blo 1224430 1308151 := bstep (se 1 (by rfl) ⟨981113, by rfl⟩ : syracuseStep 1308151 = 1962227) B1962227
theorem B1226231 : Blo 1224430 1226231 := bstep (se 1 (by rfl) ⟨919673, by rfl⟩ : syracuseStep 1226231 = 1839347) B1839347
theorem B1226251 : Blo 1224430 1226251 := bstep (se 1 (by rfl) ⟨919688, by rfl⟩ : syracuseStep 1226251 = 1839377) B1839377
theorem B1226263 : Blo 1224430 1226263 := bstep (se 1 (by rfl) ⟨919697, by rfl⟩ : syracuseStep 1226263 = 1839395) B1839395
theorem B1226283 : Blo 1224430 1226283 := bstep (se 1 (by rfl) ⟨919712, by rfl⟩ : syracuseStep 1226283 = 1839425) B1839425
theorem B3102259 : Blo 1224430 3102259 := bstep (se 1 (by rfl) ⟨2326694, by rfl⟩ : syracuseStep 3102259 = 4653389) B4653389
theorem B1226295 : Blo 1224430 1226295 := bstep (se 1 (by rfl) ⟨919721, by rfl⟩ : syracuseStep 1226295 = 1839443) B1839443
theorem B1226315 : Blo 1224430 1226315 := bstep (se 1 (by rfl) ⟨919736, by rfl⟩ : syracuseStep 1226315 = 1839473) B1839473
theorem B1226327 : Blo 1224430 1226327 := bstep (se 1 (by rfl) ⟨919745, by rfl⟩ : syracuseStep 1226327 = 1839491) B1839491
theorem B2799193 : Blo 1224430 2799193 := bstep (se 2 (by rfl) ⟨1049697, by rfl⟩ : syracuseStep 2799193 = 2099395) B2099395
theorem B1398379 : Blo 1224430 1398379 := bstep (se 1 (by rfl) ⟨1048784, by rfl⟩ : syracuseStep 1398379 = 2097569) B2097569
theorem B1226347 : Blo 1224430 1226347 := bstep (se 1 (by rfl) ⟨919760, by rfl⟩ : syracuseStep 1226347 = 1839521) B1839521
theorem B1226359 : Blo 1224430 1226359 := bstep (se 1 (by rfl) ⟨919769, by rfl⟩ : syracuseStep 1226359 = 1839539) B1839539
theorem B7853699 : Blo 1224430 7853699 := bstep (se 1 (by rfl) ⟨5890274, by rfl⟩ : syracuseStep 7853699 = 11780549) B11780549
theorem B2758283 : Blo 1224430 2758283 := bstep (se 1 (by rfl) ⟨2068712, by rfl⟩ : syracuseStep 2758283 = 4137425) B4137425
theorem B1226379 : Blo 1224430 1226379 := bstep (se 1 (by rfl) ⟨919784, by rfl⟩ : syracuseStep 1226379 = 1839569) B1839569
theorem B4650641 : Blo 1224430 4650641 := bstep (se 2 (by rfl) ⟨1743990, by rfl⟩ : syracuseStep 4650641 = 3487981) B3487981
theorem B1226391 : Blo 1224430 1226391 := bstep (se 1 (by rfl) ⟨919793, by rfl⟩ : syracuseStep 1226391 = 1839587) B1839587
theorem B1226411 : Blo 1224430 1226411 := bstep (se 1 (by rfl) ⟨919808, by rfl⟩ : syracuseStep 1226411 = 1839617) B1839617
theorem B1226423 : Blo 1224430 1226423 := bstep (se 1 (by rfl) ⟨919817, by rfl⟩ : syracuseStep 1226423 = 1839635) B1839635
theorem B3102401 : Blo 1224430 3102401 := bstep (se 2 (by rfl) ⟨1163400, by rfl⟩ : syracuseStep 3102401 = 2326801) B2326801
theorem B2758337 : Blo 1224430 2758337 := bstep (se 2 (by rfl) ⟨1034376, by rfl⟩ : syracuseStep 2758337 = 2068753) B2068753
theorem B4134617 : Blo 1224430 4134617 := bstep (se 2 (by rfl) ⟨1550481, by rfl⟩ : syracuseStep 4134617 = 3100963) B3100963
theorem B3978973 : Blo 1224430 3978973 := bstep (se 3 (by rfl) ⟨746057, by rfl⟩ : syracuseStep 3978973 = 1492115) B1492115
theorem B1308407 : Blo 1224430 1308407 := bstep (se 1 (by rfl) ⟨981305, by rfl⟩ : syracuseStep 1308407 = 1962611) B1962611
theorem B18143075 : Blo 1224430 18143075 := bstep (se 1 (by rfl) ⟨13607306, by rfl⟩ : syracuseStep 18143075 = 27214613) B27214613
theorem B2758553 : Blo 1224430 2758553 := bstep (se 2 (by rfl) ⟨1034457, by rfl⟩ : syracuseStep 2758553 = 2068915) B2068915
theorem B2758643 : Blo 1224430 2758643 := bstep (se 1 (by rfl) ⟨2068982, by rfl⟩ : syracuseStep 2758643 = 4137965) B4137965
theorem B2758679 : Blo 1224430 2758679 := bstep (se 1 (by rfl) ⟨2069009, by rfl⟩ : syracuseStep 2758679 = 4138019) B4138019
theorem B2324531 : Blo 1224430 2324531 := bstep (se 1 (by rfl) ⟨1743398, by rfl⟩ : syracuseStep 2324531 = 3486797) B3486797
theorem B4970585 : Blo 1224430 4970585 := bstep (se 2 (by rfl) ⟨1863969, by rfl⟩ : syracuseStep 4970585 = 3727939) B3727939
theorem B2758859 : Blo 1224430 2758859 := bstep (se 1 (by rfl) ⟨2069144, by rfl⟩ : syracuseStep 2758859 = 4138289) B4138289
theorem B4970717 : Blo 1224430 4970717 := bstep (se 3 (by rfl) ⟨932009, by rfl⟩ : syracuseStep 4970717 = 1864019) B1864019
theorem B2758913 : Blo 1224430 2758913 := bstep (se 2 (by rfl) ⟨1034592, by rfl⟩ : syracuseStep 2758913 = 2069185) B2069185
theorem B5593367 : Blo 1224430 5593367 := bstep (se 1 (by rfl) ⟨4195025, by rfl⟩ : syracuseStep 5593367 = 8390051) B8390051
theorem B1308971 : Blo 1224430 1308971 := bstep (se 1 (by rfl) ⟨981728, by rfl⟩ : syracuseStep 1308971 = 1963457) B1963457
theorem B11180389 : Blo 1224430 11180389 := bstep (se 4 (by rfl) ⟨1048161, by rfl⟩ : syracuseStep 11180389 = 2096323) B2096323
theorem B4651415 : Blo 1224430 4651415 := bstep (se 1 (by rfl) ⟨3488561, by rfl⟩ : syracuseStep 4651415 = 6977123) B6977123
theorem B4135319 : Blo 1224430 4135319 := bstep (se 1 (by rfl) ⟨3101489, by rfl⟩ : syracuseStep 4135319 = 6202979) B6202979
theorem B2759129 : Blo 1224430 2759129 := bstep (se 2 (by rfl) ⟨1034673, by rfl⟩ : syracuseStep 2759129 = 2069347) B2069347
theorem B2325017 : Blo 1224430 2325017 := bstep (se 2 (by rfl) ⟨871881, by rfl⟩ : syracuseStep 2325017 = 1743763) B1743763
theorem B2759219 : Blo 1224430 2759219 := bstep (se 1 (by rfl) ⟨2069414, by rfl⟩ : syracuseStep 2759219 = 4138829) B4138829
theorem B2759255 : Blo 1224430 2759255 := bstep (se 1 (by rfl) ⟨2069441, by rfl⟩ : syracuseStep 2759255 = 4138883) B4138883
theorem B1743449 : Blo 1224430 1743449 := bstep (se 2 (by rfl) ⟨653793, by rfl⟩ : syracuseStep 1743449 = 1307587) B1307587
theorem B6199901 : Blo 1224430 6199901 := bstep (se 3 (by rfl) ⟨1162481, by rfl⟩ : syracuseStep 6199901 = 2324963) B2324963
theorem B4651613 : Blo 1224430 4651613 := bstep (se 3 (by rfl) ⟨872177, by rfl⟩ : syracuseStep 4651613 = 1744355) B1744355
theorem B6978149 : Blo 1224430 6978149 := bstep (se 4 (by rfl) ⟨654201, by rfl⟩ : syracuseStep 6978149 = 1308403) B1308403
theorem B1743563 : Blo 1224430 1743563 := bstep (se 1 (by rfl) ⟨1307672, by rfl⟩ : syracuseStep 1743563 = 2615345) B2615345
theorem B5233355 : Blo 1224430 5233355 := bstep (se 1 (by rfl) ⟨3925016, by rfl⟩ : syracuseStep 5233355 = 7850033) B7850033
theorem B2759435 : Blo 1224430 2759435 := bstep (se 1 (by rfl) ⟨2069576, by rfl⟩ : syracuseStep 2759435 = 4139153) B4139153
theorem B13966181 : Blo 1224430 13966181 := bstep (se 4 (by rfl) ⟨1309329, by rfl⟩ : syracuseStep 13966181 = 2618659) B2618659
theorem B4135859 : Blo 1224430 4135859 := bstep (se 1 (by rfl) ⟨3101894, by rfl⟩ : syracuseStep 4135859 = 6203789) B6203789
theorem B3103667 : Blo 1224430 3103667 := bstep (se 1 (by rfl) ⟨2327750, by rfl⟩ : syracuseStep 3103667 = 4655501) B4655501
theorem B21232601 : Blo 1224430 21232601 := bstep (se 2 (by rfl) ⟨7962225, by rfl⟩ : syracuseStep 21232601 = 15924451) B15924451
theorem B6626405 : Blo 1224430 6626405 := bstep (se 4 (by rfl) ⟨621225, by rfl⟩ : syracuseStep 6626405 = 1242451) B1242451
theorem B5307565 : Blo 1224430 5307565 := bstep (se 3 (by rfl) ⟨995168, by rfl⟩ : syracuseStep 5307565 = 1990337) B1990337
theorem B4136129 : Blo 1224430 4136129 := bstep (se 2 (by rfl) ⟨1551048, by rfl⟩ : syracuseStep 4136129 = 3102097) B3102097
theorem B1744087 : Blo 1224430 1744087 := bstep (se 1 (by rfl) ⟨1308065, by rfl⟩ : syracuseStep 1744087 = 2616131) B2616131
theorem B3104203 : Blo 1224430 3104203 := bstep (se 1 (by rfl) ⟨2328152, by rfl⟩ : syracuseStep 3104203 = 4656305) B4656305
theorem B2793035 : Blo 1224430 2793035 := bstep (se 1 (by rfl) ⟨2094776, by rfl⟩ : syracuseStep 2793035 = 4189553) B4189553
theorem B3104345 : Blo 1224430 3104345 := bstep (se 2 (by rfl) ⟨1164129, by rfl⟩ : syracuseStep 3104345 = 2328259) B2328259
theorem B3489473 : Blo 1224430 3489473 := bstep (se 2 (by rfl) ⟨1308552, by rfl⟩ : syracuseStep 3489473 = 2617105) B2617105
theorem B4136669 : Blo 1224430 4136669 := bstep (se 3 (by rfl) ⟨775625, by rfl⟩ : syracuseStep 4136669 = 1551251) B1551251
theorem B3489587 : Blo 1224430 3489587 := bstep (se 1 (by rfl) ⟨2617190, by rfl⟩ : syracuseStep 3489587 = 5234381) B5234381
theorem B5234483 : Blo 1224430 5234483 := bstep (se 1 (by rfl) ⟨3925862, by rfl⟩ : syracuseStep 5234483 = 7851725) B7851725
theorem B2834315 : Blo 1224430 2834315 := bstep (se 1 (by rfl) ⟨2125736, by rfl⟩ : syracuseStep 2834315 = 4251473) B4251473
theorem B2326475 : Blo 1224430 2326475 := bstep (se 1 (by rfl) ⟨1744856, by rfl⟩ : syracuseStep 2326475 = 3489713) B3489713
theorem B6979607 : Blo 1224430 6979607 := bstep (se 1 (by rfl) ⟨5234705, by rfl⟩ : syracuseStep 6979607 = 10469411) B10469411
theorem B4653085 : Blo 1224430 4653085 := bstep (se 3 (by rfl) ⟨872453, by rfl⟩ : syracuseStep 4653085 = 1744907) B1744907
theorem B4137047 : Blo 1224430 4137047 := bstep (se 1 (by rfl) ⟨3102785, by rfl⟩ : syracuseStep 4137047 = 6205571) B6205571
theorem B2793619 : Blo 1224430 2793619 := bstep (se 1 (by rfl) ⟨2095214, by rfl⟩ : syracuseStep 2793619 = 4190429) B4190429
theorem B17670413 : Blo 1224430 17670413 := bstep (se 3 (by rfl) ⟨3313202, by rfl⟩ : syracuseStep 17670413 = 6626405) B6626405
theorem B2834731 : Blo 1224430 2834731 := bstep (se 1 (by rfl) ⟨2126048, by rfl⟩ : syracuseStep 2834731 = 4252097) B4252097
theorem B5890583 : Blo 1224430 5890583 := bstep (se 1 (by rfl) ⟨4417937, by rfl⟩ : syracuseStep 5890583 = 8835875) B8835875
theorem B4137533 : Blo 1224430 4137533 := bstep (se 3 (by rfl) ⟨775787, by rfl⟩ : syracuseStep 4137533 = 1551575) B1551575
theorem B3146393 : Blo 1224430 3146393 := bstep (se 2 (by rfl) ⟨1179897, by rfl⟩ : syracuseStep 3146393 = 2359795) B2359795
theorem B5890753 : Blo 1224430 5890753 := bstep (se 2 (by rfl) ⟨2209032, by rfl⟩ : syracuseStep 5890753 = 4418065) B4418065
theorem B29819609 : Blo 1224430 29819609 := bstep (se 2 (by rfl) ⟨11182353, by rfl⟩ : syracuseStep 29819609 = 22364707) B22364707
theorem B3490589 : Blo 1224430 3490589 := bstep (se 3 (by rfl) ⟨654485, by rfl⟩ : syracuseStep 3490589 = 1308971) B1308971
theorem B3146539 : Blo 1224430 3146539 := bstep (se 1 (by rfl) ⟨2359904, by rfl⟩ : syracuseStep 3146539 = 4719809) B4719809
theorem B9438067 : Blo 1224430 9438067 := bstep (se 1 (by rfl) ⟨7078550, by rfl⟩ : syracuseStep 9438067 = 14157101) B14157101
theorem B3728281 : Blo 1224430 3728281 := bstep (se 2 (by rfl) ⟨1398105, by rfl⟩ : syracuseStep 3728281 = 2796211) B2796211
theorem B5235799 : Blo 1224430 5235799 := bstep (se 1 (by rfl) ⟨3926849, by rfl⟩ : syracuseStep 5235799 = 7853699) B7853699
theorem B3490931 : Blo 1224430 3490931 := bstep (se 1 (by rfl) ⟨2618198, by rfl⟩ : syracuseStep 3490931 = 5236397) B5236397
theorem B2983031 : Blo 1224430 2983031 := bstep (se 1 (by rfl) ⟨2237273, by rfl⟩ : syracuseStep 2983031 = 4474547) B4474547
theorem B8381729 : Blo 1224430 8381729 := bstep (se 2 (by rfl) ⟨3143148, by rfl⟩ : syracuseStep 8381729 = 6286297) B6286297
theorem B1549687 : Blo 1224430 1549687 := bstep (se 1 (by rfl) ⟨1162265, by rfl⟩ : syracuseStep 1549687 = 2324531) B2324531
theorem B13419911 : Blo 1224430 13419911 := bstep (se 1 (by rfl) ⟨10064933, by rfl⟩ : syracuseStep 13419911 = 20129867) B20129867
theorem B1377679 : Blo 1224430 1377679 := bstep (se 1 (by rfl) ⟨1033259, by rfl⟩ : syracuseStep 1377679 = 2066519) B2066519
theorem B4965785 : Blo 1224430 4965785 := bstep (se 2 (by rfl) ⟨1862169, by rfl⟩ : syracuseStep 4965785 = 3724339) B3724339
theorem B3728911 : Blo 1224430 3728911 := bstep (se 1 (by rfl) ⟨2796683, by rfl⟩ : syracuseStep 3728911 = 5593367) B5593367
theorem B3491387 : Blo 1224430 3491387 := bstep (se 1 (by rfl) ⟨2618540, by rfl⟩ : syracuseStep 3491387 = 5237081) B5237081
theorem B1836731 : Blo 1224430 1836731 := bstep (se 1 (by rfl) ⟨1377548, by rfl⟩ : syracuseStep 1836731 = 2755097) B2755097
theorem B1550011 : Blo 1224430 1550011 := bstep (se 1 (by rfl) ⟨1162508, by rfl⟩ : syracuseStep 1550011 = 2325017) B2325017
theorem B1836791 : Blo 1224430 1836791 := bstep (se 1 (by rfl) ⟨1377593, by rfl⟩ : syracuseStep 1836791 = 2755187) B2755187
theorem B1836815 : Blo 1224430 1836815 := bstep (se 1 (by rfl) ⟨1377611, by rfl⟩ : syracuseStep 1836815 = 2755223) B2755223
theorem B1836857 : Blo 1224430 1836857 := bstep (se 2 (by rfl) ⟨688821, by rfl⟩ : syracuseStep 1836857 = 1377643) B1377643
theorem B1836935 : Blo 1224430 1836935 := bstep (se 1 (by rfl) ⟨1377701, by rfl⟩ : syracuseStep 1836935 = 2755403) B2755403
theorem B1378183 : Blo 1224430 1378183 := bstep (se 1 (by rfl) ⟨1033637, by rfl⟩ : syracuseStep 1378183 = 2067275) B2067275
theorem B1836971 : Blo 1224430 1836971 := bstep (se 1 (by rfl) ⟨1377728, by rfl⟩ : syracuseStep 1836971 = 2755457) B2755457
theorem B4138937 : Blo 1224430 4138937 := bstep (se 2 (by rfl) ⟨1552101, by rfl⟩ : syracuseStep 4138937 = 3104203) B3104203
theorem B2066377 : Blo 1224430 2066377 := bstep (se 2 (by rfl) ⟨774891, by rfl⟩ : syracuseStep 2066377 = 1549783) B1549783
theorem B1837001 : Blo 1224430 1837001 := bstep (se 2 (by rfl) ⟨688875, by rfl⟩ : syracuseStep 1837001 = 1377751) B1377751
theorem B1837115 : Blo 1224430 1837115 := bstep (se 1 (by rfl) ⟨1377836, by rfl⟩ : syracuseStep 1837115 = 2755673) B2755673
theorem B1378363 : Blo 1224430 1378363 := bstep (se 1 (by rfl) ⟨1033772, by rfl⟩ : syracuseStep 1378363 = 2067545) B2067545
theorem B1837175 : Blo 1224430 1837175 := bstep (se 1 (by rfl) ⟨1377881, by rfl⟩ : syracuseStep 1837175 = 2755763) B2755763
theorem B1837199 : Blo 1224430 1837199 := bstep (se 1 (by rfl) ⟨1377899, by rfl⟩ : syracuseStep 1837199 = 2755799) B2755799
theorem B1837241 : Blo 1224430 1837241 := bstep (se 2 (by rfl) ⟨688965, by rfl⟩ : syracuseStep 1837241 = 1377931) B1377931
theorem B1837319 : Blo 1224430 1837319 := bstep (se 1 (by rfl) ⟨1377989, by rfl⟩ : syracuseStep 1837319 = 2755979) B2755979
theorem B1837355 : Blo 1224430 1837355 := bstep (se 1 (by rfl) ⟨1378016, by rfl⟩ : syracuseStep 1837355 = 2756033) B2756033
theorem B1837385 : Blo 1224430 1837385 := bstep (se 2 (by rfl) ⟨689019, by rfl⟩ : syracuseStep 1837385 = 1378039) B1378039
theorem B1862023 : Blo 1224430 1862023 := bstep (se 1 (by rfl) ⟨1396517, by rfl⟩ : syracuseStep 1862023 = 2793035) B2793035
theorem B1837499 : Blo 1224430 1837499 := bstep (se 1 (by rfl) ⟨1378124, by rfl⟩ : syracuseStep 1837499 = 2756249) B2756249
theorem B2984393 : Blo 1224430 2984393 := bstep (se 2 (by rfl) ⟨1119147, by rfl⟩ : syracuseStep 2984393 = 2238295) B2238295
theorem B1837559 : Blo 1224430 1837559 := bstep (se 1 (by rfl) ⟨1378169, by rfl⟩ : syracuseStep 1837559 = 2756339) B2756339
theorem B1837583 : Blo 1224430 1837583 := bstep (se 1 (by rfl) ⟨1378187, by rfl⟩ : syracuseStep 1837583 = 2756375) B2756375
theorem B1378831 : Blo 1224430 1378831 := bstep (se 1 (by rfl) ⟨1034123, by rfl⟩ : syracuseStep 1378831 = 2068247) B2068247
theorem B2755115 : Blo 1224430 2755115 := bstep (se 1 (by rfl) ⟨2066336, by rfl⟩ : syracuseStep 2755115 = 4132673) B4132673
theorem B1837625 : Blo 1224430 1837625 := bstep (se 2 (by rfl) ⟨689109, by rfl⟩ : syracuseStep 1837625 = 1378219) B1378219
theorem B2067079 : Blo 1224430 2067079 := bstep (se 1 (by rfl) ⟨1550309, by rfl⟩ : syracuseStep 2067079 = 3100619) B3100619
theorem B1837703 : Blo 1224430 1837703 := bstep (se 1 (by rfl) ⟨1378277, by rfl⟩ : syracuseStep 1837703 = 2756555) B2756555
theorem B1550983 : Blo 1224430 1550983 := bstep (se 1 (by rfl) ⟨1163237, by rfl⟩ : syracuseStep 1550983 = 2326475) B2326475
theorem B1837739 : Blo 1224430 1837739 := bstep (se 1 (by rfl) ⟨1378304, by rfl⟩ : syracuseStep 1837739 = 2756609) B2756609
theorem B1837769 : Blo 1224430 1837769 := bstep (se 2 (by rfl) ⟨689163, by rfl⟩ : syracuseStep 1837769 = 1378327) B1378327
theorem B2616097 : Blo 1224430 2616097 := bstep (se 2 (by rfl) ⟨981036, by rfl⟩ : syracuseStep 2616097 = 1962073) B1962073
theorem B1837883 : Blo 1224430 1837883 := bstep (se 1 (by rfl) ⟨1378412, by rfl⟩ : syracuseStep 1837883 = 2756825) B2756825
theorem B6204275 : Blo 1224430 6204275 := bstep (se 1 (by rfl) ⟨4653206, by rfl⟩ : syracuseStep 6204275 = 9306413) B9306413
theorem B4655987 : Blo 1224430 4655987 := bstep (se 1 (by rfl) ⟨3491990, by rfl⟩ : syracuseStep 4655987 = 6983981) B6983981
theorem B1837943 : Blo 1224430 1837943 := bstep (se 1 (by rfl) ⟨1378457, by rfl⟩ : syracuseStep 1837943 = 2756915) B2756915
theorem B1837967 : Blo 1224430 1837967 := bstep (se 1 (by rfl) ⟨1378475, by rfl⟩ : syracuseStep 1837967 = 2756951) B2756951
theorem B2755475 : Blo 1224430 2755475 := bstep (se 1 (by rfl) ⟨2066606, by rfl⟩ : syracuseStep 2755475 = 4133213) B4133213
theorem B15715235 : Blo 1224430 15715235 := bstep (se 1 (by rfl) ⟨11786426, by rfl⟩ : syracuseStep 15715235 = 23572853) B23572853
theorem B1838009 : Blo 1224430 1838009 := bstep (se 2 (by rfl) ⟨689253, by rfl⟩ : syracuseStep 1838009 = 1378507) B1378507
theorem B2755529 : Blo 1224430 2755529 := bstep (se 2 (by rfl) ⟨1033323, by rfl⟩ : syracuseStep 2755529 = 2066647) B2066647
theorem B1838087 : Blo 1224430 1838087 := bstep (se 1 (by rfl) ⟨1378565, by rfl⟩ : syracuseStep 1838087 = 2757131) B2757131
theorem B1379335 : Blo 1224430 1379335 := bstep (se 1 (by rfl) ⟨1034501, by rfl⟩ : syracuseStep 1379335 = 2069003) B2069003
theorem B8825867 : Blo 1224430 8825867 := bstep (se 1 (by rfl) ⟨6619400, by rfl⟩ : syracuseStep 8825867 = 13238801) B13238801
theorem B150924323 : Blo 1224430 150924323 := bstep (se 1 (by rfl) ⟨113193242, by rfl⟩ : syracuseStep 150924323 = 226386485) B226386485
theorem B1838123 : Blo 1224430 1838123 := bstep (se 1 (by rfl) ⟨1378592, by rfl⟩ : syracuseStep 1838123 = 2757185) B2757185
theorem B1551403 : Blo 1224430 1551403 := bstep (se 1 (by rfl) ⟨1163552, by rfl⟩ : syracuseStep 1551403 = 2327105) B2327105
theorem B6974525 : Blo 1224430 6974525 := bstep (se 3 (by rfl) ⟨1307723, by rfl⟩ : syracuseStep 6974525 = 2615447) B2615447
theorem B1838153 : Blo 1224430 1838153 := bstep (se 2 (by rfl) ⟨689307, by rfl⟩ : syracuseStep 1838153 = 1378615) B1378615
theorem B1838267 : Blo 1224430 1838267 := bstep (se 1 (by rfl) ⟨1378700, by rfl⟩ : syracuseStep 1838267 = 2757401) B2757401
theorem B1379515 : Blo 1224430 1379515 := bstep (se 1 (by rfl) ⟨1034636, by rfl⟩ : syracuseStep 1379515 = 2069273) B2069273
theorem B8834285 : Blo 1224430 8834285 := bstep (se 3 (by rfl) ⟨1656428, by rfl⟩ : syracuseStep 8834285 = 3312857) B3312857
theorem B1838327 : Blo 1224430 1838327 := bstep (se 1 (by rfl) ⟨1378745, by rfl⟩ : syracuseStep 1838327 = 2757491) B2757491
theorem B2067727 : Blo 1224430 2067727 := bstep (se 1 (by rfl) ⟨1550795, by rfl⟩ : syracuseStep 2067727 = 3101591) B3101591
theorem B1838351 : Blo 1224430 1838351 := bstep (se 1 (by rfl) ⟨1378763, by rfl⟩ : syracuseStep 1838351 = 2757527) B2757527
theorem B1551631 : Blo 1224430 1551631 := bstep (se 1 (by rfl) ⟨1163723, by rfl⟩ : syracuseStep 1551631 = 2327447) B2327447
theorem B1838393 : Blo 1224430 1838393 := bstep (se 2 (by rfl) ⟨689397, by rfl⟩ : syracuseStep 1838393 = 1378795) B1378795
theorem B3099991 : Blo 1224430 3099991 := bstep (se 1 (by rfl) ⟨2324993, by rfl⟩ : syracuseStep 3099991 = 4649987) B4649987
theorem B6204761 : Blo 1224430 6204761 := bstep (se 2 (by rfl) ⟨2326785, by rfl⟩ : syracuseStep 6204761 = 4653571) B4653571
theorem B2616695 : Blo 1224430 2616695 := bstep (se 1 (by rfl) ⟨1962521, by rfl⟩ : syracuseStep 2616695 = 3925043) B3925043
theorem B1838471 : Blo 1224430 1838471 := bstep (se 1 (by rfl) ⟨1378853, by rfl⟩ : syracuseStep 1838471 = 2757707) B2757707
theorem B10464659 : Blo 1224430 10464659 := bstep (se 1 (by rfl) ⟨7848494, by rfl⟩ : syracuseStep 10464659 = 15696989) B15696989
theorem B1838507 : Blo 1224430 1838507 := bstep (se 1 (by rfl) ⟨1378880, by rfl⟩ : syracuseStep 1838507 = 2757761) B2757761
theorem B1838537 : Blo 1224430 1838537 := bstep (se 2 (by rfl) ⟨689451, by rfl⟩ : syracuseStep 1838537 = 1378903) B1378903
theorem B3026377 : Blo 1224430 3026377 := bstep (se 2 (by rfl) ⟨1134891, by rfl⟩ : syracuseStep 3026377 = 2269783) B2269783
theorem B1838651 : Blo 1224430 1838651 := bstep (se 1 (by rfl) ⟨1378988, by rfl⟩ : syracuseStep 1838651 = 2757977) B2757977
theorem B1838711 : Blo 1224430 1838711 := bstep (se 1 (by rfl) ⟨1379033, by rfl⟩ : syracuseStep 1838711 = 2758067) B2758067
theorem B9309815 : Blo 1224430 9309815 := bstep (se 1 (by rfl) ⟨6982361, by rfl⟩ : syracuseStep 9309815 = 13964723) B13964723
theorem B3100295 : Blo 1224430 3100295 := bstep (se 1 (by rfl) ⟨2325221, by rfl⟩ : syracuseStep 3100295 = 4650443) B4650443
theorem B2756231 : Blo 1224430 2756231 := bstep (se 1 (by rfl) ⟨2067173, by rfl⟩ : syracuseStep 2756231 = 4134347) B4134347
theorem B1838735 : Blo 1224430 1838735 := bstep (se 1 (by rfl) ⟨1379051, by rfl⟩ : syracuseStep 1838735 = 2758103) B2758103
theorem B1838777 : Blo 1224430 1838777 := bstep (se 2 (by rfl) ⟨689541, by rfl⟩ : syracuseStep 1838777 = 1379083) B1379083
theorem B6975233 : Blo 1224430 6975233 := bstep (se 2 (by rfl) ⟨2615712, by rfl⟩ : syracuseStep 6975233 = 5231425) B5231425
theorem B1224455 : Blo 1224430 1224455 := bstep (se 1 (by rfl) ⟨918341, by rfl⟩ : syracuseStep 1224455 = 1836683) B1836683
theorem B1838855 : Blo 1224430 1838855 := bstep (se 1 (by rfl) ⟨1379141, by rfl⟩ : syracuseStep 1838855 = 2758283) B2758283
theorem B3100427 : Blo 1224430 3100427 := bstep (se 1 (by rfl) ⟨2325320, by rfl⟩ : syracuseStep 3100427 = 4650641) B4650641
theorem B1224463 : Blo 1224430 1224463 := bstep (se 1 (by rfl) ⟨918347, by rfl⟩ : syracuseStep 1224463 = 1836695) B1836695
theorem B2068267 : Blo 1224430 2068267 := bstep (se 1 (by rfl) ⟨1551200, by rfl⟩ : syracuseStep 2068267 = 3102401) B3102401
theorem B1838891 : Blo 1224430 1838891 := bstep (se 1 (by rfl) ⟨1379168, by rfl⟩ : syracuseStep 1838891 = 2758337) B2758337
theorem B40308529 : Blo 1224430 40308529 := bstep (se 2 (by rfl) ⟨15115698, by rfl⟩ : syracuseStep 40308529 = 30231397) B30231397
theorem B1224507 : Blo 1224430 1224507 := bstep (se 1 (by rfl) ⟨918380, by rfl⟩ : syracuseStep 1224507 = 1836761) B1836761
theorem B2756411 : Blo 1224430 2756411 := bstep (se 1 (by rfl) ⟨2067308, by rfl⟩ : syracuseStep 2756411 = 4134617) B4134617
theorem B21221189 : Blo 1224430 21221189 := bstep (se 4 (by rfl) ⟨1989486, by rfl⟩ : syracuseStep 21221189 = 3978973) B3978973
theorem B1838921 : Blo 1224430 1838921 := bstep (se 2 (by rfl) ⟨689595, by rfl⟩ : syracuseStep 1838921 = 1379191) B1379191
theorem B12922739 : Blo 1224430 12922739 := bstep (se 1 (by rfl) ⟨9692054, by rfl⟩ : syracuseStep 12922739 = 19384109) B19384109
theorem B1224583 : Blo 1224430 1224583 := bstep (se 1 (by rfl) ⟨918437, by rfl⟩ : syracuseStep 1224583 = 1836875) B1836875
theorem B4190087 : Blo 1224430 4190087 := bstep (se 1 (by rfl) ⟨3142565, by rfl⟩ : syracuseStep 4190087 = 6285131) B6285131
theorem B1224591 : Blo 1224430 1224591 := bstep (se 1 (by rfl) ⟨918443, by rfl⟩ : syracuseStep 1224591 = 1836887) B1836887
theorem B2756537 : Blo 1224430 2756537 := bstep (se 2 (by rfl) ⟨1033701, by rfl⟩ : syracuseStep 2756537 = 2067403) B2067403
theorem B2068409 : Blo 1224430 2068409 := bstep (se 2 (by rfl) ⟨775653, by rfl⟩ : syracuseStep 2068409 = 1551307) B1551307
theorem B1224635 : Blo 1224430 1224635 := bstep (se 1 (by rfl) ⟨918476, by rfl⟩ : syracuseStep 1224635 = 1836953) B1836953
theorem B1839035 : Blo 1224430 1839035 := bstep (se 1 (by rfl) ⟨1379276, by rfl⟩ : syracuseStep 1839035 = 2758553) B2758553
theorem B1839095 : Blo 1224430 1839095 := bstep (se 1 (by rfl) ⟨1379321, by rfl⟩ : syracuseStep 1839095 = 2758643) B2758643
theorem B1224711 : Blo 1224430 1224711 := bstep (se 1 (by rfl) ⟨918533, by rfl⟩ : syracuseStep 1224711 = 1837067) B1837067
theorem B1224719 : Blo 1224430 1224719 := bstep (se 1 (by rfl) ⟨918539, by rfl⟩ : syracuseStep 1224719 = 1837079) B1837079
theorem B1839119 : Blo 1224430 1839119 := bstep (se 1 (by rfl) ⟨1379339, by rfl⟩ : syracuseStep 1839119 = 2758679) B2758679
theorem B9302039 : Blo 1224430 9302039 := bstep (se 1 (by rfl) ⟨6976529, by rfl⟩ : syracuseStep 9302039 = 13953059) B13953059
theorem B1224763 : Blo 1224430 1224763 := bstep (se 1 (by rfl) ⟨918572, by rfl⟩ : syracuseStep 1224763 = 1837145) B1837145
theorem B3313723 : Blo 1224430 3313723 := bstep (se 1 (by rfl) ⟨2485292, by rfl⟩ : syracuseStep 3313723 = 4970585) B4970585
theorem B1839161 : Blo 1224430 1839161 := bstep (se 2 (by rfl) ⟨689685, by rfl⟩ : syracuseStep 1839161 = 1379371) B1379371
theorem B1224839 : Blo 1224430 1224839 := bstep (se 1 (by rfl) ⟨918629, by rfl⟩ : syracuseStep 1224839 = 1837259) B1837259
theorem B2207879 : Blo 1224430 2207879 := bstep (se 1 (by rfl) ⟨1655909, by rfl⟩ : syracuseStep 2207879 = 3311819) B3311819
theorem B1839239 : Blo 1224430 1839239 := bstep (se 1 (by rfl) ⟨1379429, by rfl⟩ : syracuseStep 1839239 = 2758859) B2758859
theorem B1224847 : Blo 1224430 1224847 := bstep (se 1 (by rfl) ⟨918635, by rfl⟩ : syracuseStep 1224847 = 1837271) B1837271
theorem B3313811 : Blo 1224430 3313811 := bstep (se 1 (by rfl) ⟨2485358, by rfl⟩ : syracuseStep 3313811 = 4970717) B4970717
theorem B1839275 : Blo 1224430 1839275 := bstep (se 1 (by rfl) ⟨1379456, by rfl⟩ : syracuseStep 1839275 = 2758913) B2758913
theorem B1224891 : Blo 1224430 1224891 := bstep (se 1 (by rfl) ⟨918668, by rfl⟩ : syracuseStep 1224891 = 1837337) B1837337
theorem B1839305 : Blo 1224430 1839305 := bstep (se 2 (by rfl) ⟨689739, by rfl⟩ : syracuseStep 1839305 = 1379479) B1379479
theorem B4649197 : Blo 1224430 4649197 := bstep (se 3 (by rfl) ⟨871724, by rfl⟩ : syracuseStep 4649197 = 1743449) B1743449
theorem B1224967 : Blo 1224430 1224967 := bstep (se 1 (by rfl) ⟨918725, by rfl⟩ : syracuseStep 1224967 = 1837451) B1837451
theorem B1224975 : Blo 1224430 1224975 := bstep (se 1 (by rfl) ⟨918731, by rfl⟩ : syracuseStep 1224975 = 1837463) B1837463
theorem B3100943 : Blo 1224430 3100943 := bstep (se 1 (by rfl) ⟨2325707, by rfl⟩ : syracuseStep 3100943 = 4651415) B4651415
theorem B2756879 : Blo 1224430 2756879 := bstep (se 1 (by rfl) ⟨2067659, by rfl⟩ : syracuseStep 2756879 = 4135319) B4135319
theorem B2756897 : Blo 1224430 2756897 := bstep (se 2 (by rfl) ⟨1033836, by rfl⟩ : syracuseStep 2756897 = 2067673) B2067673
theorem B1225019 : Blo 1224430 1225019 := bstep (se 1 (by rfl) ⟨918764, by rfl⟩ : syracuseStep 1225019 = 1837529) B1837529
theorem B2945339 : Blo 1224430 2945339 := bstep (se 1 (by rfl) ⟨2209004, by rfl⟩ : syracuseStep 2945339 = 4418009) B4418009
theorem B1839419 : Blo 1224430 1839419 := bstep (se 1 (by rfl) ⟨1379564, by rfl⟩ : syracuseStep 1839419 = 2759129) B2759129
theorem B1839479 : Blo 1224430 1839479 := bstep (se 1 (by rfl) ⟨1379609, by rfl⟩ : syracuseStep 1839479 = 2759219) B2759219
theorem B1225095 : Blo 1224430 1225095 := bstep (se 1 (by rfl) ⟨918821, by rfl⟩ : syracuseStep 1225095 = 1837643) B1837643
theorem B1225103 : Blo 1224430 1225103 := bstep (se 1 (by rfl) ⟨918827, by rfl⟩ : syracuseStep 1225103 = 1837655) B1837655
theorem B1839503 : Blo 1224430 1839503 := bstep (se 1 (by rfl) ⟨1379627, by rfl⟩ : syracuseStep 1839503 = 2759255) B2759255
theorem B4133267 : Blo 1224430 4133267 := bstep (se 1 (by rfl) ⟨3099950, by rfl⟩ : syracuseStep 4133267 = 6199901) B6199901
theorem B3101075 : Blo 1224430 3101075 := bstep (se 1 (by rfl) ⟨2325806, by rfl⟩ : syracuseStep 3101075 = 4651613) B4651613
theorem B1839545 : Blo 1224430 1839545 := bstep (se 2 (by rfl) ⟨689829, by rfl⟩ : syracuseStep 1839545 = 1379659) B1379659
theorem B1225147 : Blo 1224430 1225147 := bstep (se 1 (by rfl) ⟨918860, by rfl⟩ : syracuseStep 1225147 = 1837721) B1837721
theorem B35303921 : Blo 1224430 35303921 := bstep (se 2 (by rfl) ⟨13238970, by rfl⟩ : syracuseStep 35303921 = 26477941) B26477941
theorem B3314177 : Blo 1224430 3314177 := bstep (se 2 (by rfl) ⟨1242816, by rfl⟩ : syracuseStep 3314177 = 2485633) B2485633
theorem B1225223 : Blo 1224430 1225223 := bstep (se 1 (by rfl) ⟨918917, by rfl⟩ : syracuseStep 1225223 = 1837835) B1837835
theorem B1839623 : Blo 1224430 1839623 := bstep (se 1 (by rfl) ⟨1379717, by rfl⟩ : syracuseStep 1839623 = 2759435) B2759435
theorem B1225231 : Blo 1224430 1225231 := bstep (se 1 (by rfl) ⟨918923, by rfl⟩ : syracuseStep 1225231 = 1837847) B1837847
theorem B4649501 : Blo 1224430 4649501 := bstep (se 3 (by rfl) ⟨871781, by rfl⟩ : syracuseStep 4649501 = 1743563) B1743563
theorem B42480163 : Blo 1224430 42480163 := bstep (se 1 (by rfl) ⟨31860122, by rfl⟩ : syracuseStep 42480163 = 63720245) B63720245
theorem B1225275 : Blo 1224430 1225275 := bstep (se 1 (by rfl) ⟨918956, by rfl⟩ : syracuseStep 1225275 = 1837913) B1837913
theorem B6287939 : Blo 1224430 6287939 := bstep (se 1 (by rfl) ⟨4715954, by rfl⟩ : syracuseStep 6287939 = 9431909) B9431909
theorem B9310787 : Blo 1224430 9310787 := bstep (se 1 (by rfl) ⟨6983090, by rfl⟩ : syracuseStep 9310787 = 13966181) B13966181
theorem B2757239 : Blo 1224430 2757239 := bstep (se 1 (by rfl) ⟨2067929, by rfl⟩ : syracuseStep 2757239 = 4135859) B4135859
theorem B2069111 : Blo 1224430 2069111 := bstep (se 1 (by rfl) ⟨1551833, by rfl⟩ : syracuseStep 2069111 = 3103667) B3103667
theorem B1225351 : Blo 1224430 1225351 := bstep (se 1 (by rfl) ⟨919013, by rfl⟩ : syracuseStep 1225351 = 1838027) B1838027
theorem B1225359 : Blo 1224430 1225359 := bstep (se 1 (by rfl) ⟨919019, by rfl⟩ : syracuseStep 1225359 = 1838039) B1838039
theorem B1225403 : Blo 1224430 1225403 := bstep (se 1 (by rfl) ⟨919052, by rfl⟩ : syracuseStep 1225403 = 1838105) B1838105
theorem B1225479 : Blo 1224430 1225479 := bstep (se 1 (by rfl) ⟨919109, by rfl⟩ : syracuseStep 1225479 = 1838219) B1838219
theorem B1225487 : Blo 1224430 1225487 := bstep (se 1 (by rfl) ⟨919115, by rfl⟩ : syracuseStep 1225487 = 1838231) B1838231
theorem B3732257 : Blo 1224430 3732257 := bstep (se 2 (by rfl) ⟨1399596, by rfl⟩ : syracuseStep 3732257 = 2799193) B2799193
theorem B2757419 : Blo 1224430 2757419 := bstep (se 1 (by rfl) ⟨2068064, by rfl⟩ : syracuseStep 2757419 = 4136129) B4136129
theorem B1864505 : Blo 1224430 1864505 := bstep (se 2 (by rfl) ⟨699189, by rfl⟩ : syracuseStep 1864505 = 1398379) B1398379
theorem B1225531 : Blo 1224430 1225531 := bstep (se 1 (by rfl) ⟨919148, by rfl⟩ : syracuseStep 1225531 = 1838297) B1838297
theorem B1225607 : Blo 1224430 1225607 := bstep (se 1 (by rfl) ⟨919205, by rfl⟩ : syracuseStep 1225607 = 1838411) B1838411
theorem B1225615 : Blo 1224430 1225615 := bstep (se 1 (by rfl) ⟨919211, by rfl⟩ : syracuseStep 1225615 = 1838423) B1838423
theorem B1225659 : Blo 1224430 1225659 := bstep (se 1 (by rfl) ⟨919244, by rfl⟩ : syracuseStep 1225659 = 1838489) B1838489
theorem B1225735 : Blo 1224430 1225735 := bstep (se 1 (by rfl) ⟨919301, by rfl⟩ : syracuseStep 1225735 = 1838603) B1838603
theorem B1242127 : Blo 1224430 1242127 := bstep (se 1 (by rfl) ⟨931595, by rfl⟩ : syracuseStep 1242127 = 1863191) B1863191
theorem B1225743 : Blo 1224430 1225743 := bstep (se 1 (by rfl) ⟨919307, by rfl⟩ : syracuseStep 1225743 = 1838615) B1838615
theorem B1225787 : Blo 1224430 1225787 := bstep (se 1 (by rfl) ⟨919340, by rfl⟩ : syracuseStep 1225787 = 1838681) B1838681
theorem B2069563 : Blo 1224430 2069563 := bstep (se 1 (by rfl) ⟨1552172, by rfl⟩ : syracuseStep 2069563 = 3104345) B3104345
theorem B1225863 : Blo 1224430 1225863 := bstep (se 1 (by rfl) ⟨919397, by rfl⟩ : syracuseStep 1225863 = 1838795) B1838795
theorem B1225871 : Blo 1224430 1225871 := bstep (se 1 (by rfl) ⟨919403, by rfl⟩ : syracuseStep 1225871 = 1838807) B1838807
theorem B2757779 : Blo 1224430 2757779 := bstep (se 1 (by rfl) ⟨2068334, by rfl⟩ : syracuseStep 2757779 = 4136669) B4136669
theorem B1225915 : Blo 1224430 1225915 := bstep (se 1 (by rfl) ⟨919436, by rfl⟩ : syracuseStep 1225915 = 1838873) B1838873
theorem B2757833 : Blo 1224430 2757833 := bstep (se 2 (by rfl) ⟨1034187, by rfl⟩ : syracuseStep 2757833 = 2068375) B2068375
theorem B1225991 : Blo 1224430 1225991 := bstep (se 1 (by rfl) ⟨919493, by rfl⟩ : syracuseStep 1225991 = 1838987) B1838987
theorem B1889543 : Blo 1224430 1889543 := bstep (se 1 (by rfl) ⟨1417157, by rfl⟩ : syracuseStep 1889543 = 2834315) B2834315
theorem B1225999 : Blo 1224430 1225999 := bstep (se 1 (by rfl) ⟨919499, by rfl⟩ : syracuseStep 1225999 = 1838999) B1838999
theorem B1226043 : Blo 1224430 1226043 := bstep (se 1 (by rfl) ⟨919532, by rfl⟩ : syracuseStep 1226043 = 1839065) B1839065
theorem B1226119 : Blo 1224430 1226119 := bstep (se 1 (by rfl) ⟨919589, by rfl⟩ : syracuseStep 1226119 = 1839179) B1839179
theorem B1226127 : Blo 1224430 1226127 := bstep (se 1 (by rfl) ⟨919595, by rfl⟩ : syracuseStep 1226127 = 1839191) B1839191
theorem B6206867 : Blo 1224430 6206867 := bstep (se 1 (by rfl) ⟨4655150, by rfl⟩ : syracuseStep 6206867 = 9310301) B9310301
theorem B1226171 : Blo 1224430 1226171 := bstep (se 1 (by rfl) ⟨919628, by rfl⟩ : syracuseStep 1226171 = 1839257) B1839257
theorem B3102209 : Blo 1224430 3102209 := bstep (se 2 (by rfl) ⟨1163328, by rfl⟩ : syracuseStep 3102209 = 2326657) B2326657
theorem B9434627 : Blo 1224430 9434627 := bstep (se 1 (by rfl) ⟨7075970, by rfl⟩ : syracuseStep 9434627 = 14151941) B14151941
theorem B1226247 : Blo 1224430 1226247 := bstep (se 1 (by rfl) ⟨919685, by rfl⟩ : syracuseStep 1226247 = 1839371) B1839371
theorem B1226255 : Blo 1224430 1226255 := bstep (se 1 (by rfl) ⟨919691, by rfl⟩ : syracuseStep 1226255 = 1839383) B1839383
theorem B1226299 : Blo 1224430 1226299 := bstep (se 1 (by rfl) ⟨919724, by rfl⟩ : syracuseStep 1226299 = 1839449) B1839449
theorem B1226375 : Blo 1224430 1226375 := bstep (se 1 (by rfl) ⟨919781, by rfl⟩ : syracuseStep 1226375 = 1839563) B1839563
theorem B1226383 : Blo 1224430 1226383 := bstep (se 1 (by rfl) ⟨919787, by rfl⟩ : syracuseStep 1226383 = 1839575) B1839575
theorem B1226427 : Blo 1224430 1226427 := bstep (se 1 (by rfl) ⟨919820, by rfl⟩ : syracuseStep 1226427 = 1839641) B1839641
theorem B4134671 : Blo 1224430 4134671 := bstep (se 1 (by rfl) ⟨3101003, by rfl⟩ : syracuseStep 4134671 = 6202007) B6202007
theorem B14907185 : Blo 1224430 14907185 := bstep (se 2 (by rfl) ⟨5590194, by rfl⟩ : syracuseStep 14907185 = 11180389) B11180389
theorem B6199091 : Blo 1224430 6199091 := bstep (se 1 (by rfl) ⟨4649318, by rfl⟩ : syracuseStep 6199091 = 9298637) B9298637
theorem B3102583 : Blo 1224430 3102583 := bstep (se 1 (by rfl) ⟨2326937, by rfl⟩ : syracuseStep 3102583 = 4653875) B4653875
theorem B2758535 : Blo 1224430 2758535 := bstep (se 1 (by rfl) ⟨2068901, by rfl⟩ : syracuseStep 2758535 = 4137803) B4137803
theorem B3487673 : Blo 1224430 3487673 := bstep (se 2 (by rfl) ⟨1307877, by rfl⟩ : syracuseStep 3487673 = 2615755) B2615755
theorem B4134941 : Blo 1224430 4134941 := bstep (se 3 (by rfl) ⟨775301, by rfl⟩ : syracuseStep 4134941 = 1550603) B1550603
theorem B2758715 : Blo 1224430 2758715 := bstep (se 1 (by rfl) ⟨2069036, by rfl⟩ : syracuseStep 2758715 = 4138073) B4138073
theorem B5232707 : Blo 1224430 5232707 := bstep (se 1 (by rfl) ⟨3924530, by rfl⟩ : syracuseStep 5232707 = 7849061) B7849061
theorem B6977623 : Blo 1224430 6977623 := bstep (se 1 (by rfl) ⟨5233217, by rfl⟩ : syracuseStep 6977623 = 10466435) B10466435
theorem B3143767 : Blo 1224430 3143767 := bstep (se 1 (by rfl) ⟨2357825, by rfl⟩ : syracuseStep 3143767 = 4715651) B4715651
theorem B3774583 : Blo 1224430 3774583 := bstep (se 1 (by rfl) ⟨2830937, by rfl⟩ : syracuseStep 3774583 = 5661875) B5661875
theorem B6199415 : Blo 1224430 6199415 := bstep (se 1 (by rfl) ⟨4649561, by rfl⟩ : syracuseStep 6199415 = 9299123) B9299123
theorem B4651127 : Blo 1224430 4651127 := bstep (se 1 (by rfl) ⟨3488345, by rfl⟩ : syracuseStep 4651127 = 6976691) B6976691
theorem B1767559 : Blo 1224430 1767559 := bstep (se 1 (by rfl) ⟨1325669, by rfl⟩ : syracuseStep 1767559 = 2651339) B2651339
theorem B2758841 : Blo 1224430 2758841 := bstep (se 2 (by rfl) ⟨1034565, by rfl⟩ : syracuseStep 2758841 = 2069131) B2069131
theorem B9943241 : Blo 1224430 9943241 := bstep (se 2 (by rfl) ⟨3728715, by rfl⟩ : syracuseStep 9943241 = 7457431) B7457431
theorem B7166189 : Blo 1224430 7166189 := bstep (se 3 (by rfl) ⟨1343660, by rfl⟩ : syracuseStep 7166189 = 2687321) B2687321
theorem B3488015 : Blo 1224430 3488015 := bstep (se 1 (by rfl) ⟨2616011, by rfl⟩ : syracuseStep 3488015 = 5232023) B5232023
theorem B3103019 : Blo 1224430 3103019 := bstep (se 1 (by rfl) ⟨2327264, by rfl⟩ : syracuseStep 3103019 = 4654529) B4654529
theorem B18897299 : Blo 1224430 18897299 := bstep (se 1 (by rfl) ⟨14172974, by rfl⟩ : syracuseStep 18897299 = 28345949) B28345949
theorem B5233081 : Blo 1224430 5233081 := bstep (se 2 (by rfl) ⟨1962405, by rfl⟩ : syracuseStep 5233081 = 3924811) B3924811
theorem B9943505 : Blo 1224430 9943505 := bstep (se 2 (by rfl) ⟨3728814, by rfl⟩ : syracuseStep 9943505 = 7457629) B7457629
theorem B2759183 : Blo 1224430 2759183 := bstep (se 1 (by rfl) ⟨2069387, by rfl⟩ : syracuseStep 2759183 = 4138775) B4138775
theorem B2759201 : Blo 1224430 2759201 := bstep (se 2 (by rfl) ⟨1034700, by rfl⟩ : syracuseStep 2759201 = 2069401) B2069401
theorem B11778817 : Blo 1224430 11778817 := bstep (se 2 (by rfl) ⟨4417056, by rfl⟩ : syracuseStep 11778817 = 8834113) B8834113
theorem B5233423 : Blo 1224430 5233423 := bstep (se 1 (by rfl) ⟨3925067, by rfl⟩ : syracuseStep 5233423 = 7850135) B7850135
theorem B7076753 : Blo 1224430 7076753 := bstep (se 2 (by rfl) ⟨2653782, by rfl⟩ : syracuseStep 7076753 = 5307565) B5307565
theorem B2325449 : Blo 1224430 2325449 := bstep (se 2 (by rfl) ⟨872043, by rfl⟩ : syracuseStep 2325449 = 1744087) B1744087
theorem B3922955 : Blo 1224430 3922955 := bstep (se 1 (by rfl) ⟨2942216, by rfl⟩ : syracuseStep 3922955 = 5884433) B5884433
theorem B6200387 : Blo 1224430 6200387 := bstep (se 1 (by rfl) ⟨4650290, by rfl⟩ : syracuseStep 6200387 = 9300581) B9300581
theorem B4652099 : Blo 1224430 4652099 := bstep (se 1 (by rfl) ⟨3489074, by rfl⟩ : syracuseStep 4652099 = 6978149) B6978149
theorem B3103859 : Blo 1224430 3103859 := bstep (se 1 (by rfl) ⟨2327894, by rfl⟩ : syracuseStep 3103859 = 4655789) B4655789
theorem B3488903 : Blo 1224430 3488903 := bstep (se 1 (by rfl) ⟨2616677, by rfl⟩ : syracuseStep 3488903 = 5233355) B5233355
theorem B3103879 : Blo 1224430 3103879 := bstep (se 1 (by rfl) ⟨2327909, by rfl⟩ : syracuseStep 3103879 = 4655819) B4655819
theorem B14155067 : Blo 1224430 14155067 := bstep (se 1 (by rfl) ⟨10616300, by rfl⟩ : syracuseStep 14155067 = 21232601) B21232601
theorem B3489085 : Blo 1224430 3489085 := bstep (se 3 (by rfl) ⟨654203, by rfl⟩ : syracuseStep 3489085 = 1308407) B1308407
theorem B1744201 : Blo 1224430 1744201 := bstep (se 2 (by rfl) ⟨654075, by rfl⟩ : syracuseStep 1744201 = 1308151) B1308151
theorem B6200711 : Blo 1224430 6200711 := bstep (se 1 (by rfl) ⟨4650533, by rfl⟩ : syracuseStep 6200711 = 9301067) B9301067
theorem B4136345 : Blo 1224430 4136345 := bstep (se 2 (by rfl) ⟨1551129, by rfl⟩ : syracuseStep 4136345 = 3102259) B3102259
theorem B3104153 : Blo 1224430 3104153 := bstep (se 2 (by rfl) ⟨1164057, by rfl⟩ : syracuseStep 3104153 = 2328115) B2328115
theorem B9199133 : Blo 1224430 9199133 := bstep (se 3 (by rfl) ⟨1724837, by rfl⟩ : syracuseStep 9199133 = 3449675) B3449675
theorem B3489313 : Blo 1224430 3489313 := bstep (se 2 (by rfl) ⟨1308492, by rfl⟩ : syracuseStep 3489313 = 2616985) B2616985
theorem B3104315 : Blo 1224430 3104315 := bstep (se 1 (by rfl) ⟨2328236, by rfl⟩ : syracuseStep 3104315 = 4656473) B4656473
theorem B11779661 : Blo 1224430 11779661 := bstep (se 3 (by rfl) ⟨2208686, by rfl⟩ : syracuseStep 11779661 = 4417373) B4417373
theorem B48381533 : Blo 1224430 48381533 := bstep (se 3 (by rfl) ⟨9071537, by rfl⟩ : syracuseStep 48381533 = 18143075) B18143075
theorem B2326315 : Blo 1224430 2326315 := bstep (se 1 (by rfl) ⟨1744736, by rfl⟩ : syracuseStep 2326315 = 3489473) B3489473
theorem B2326391 : Blo 1224430 2326391 := bstep (se 1 (by rfl) ⟨1744793, by rfl⟩ : syracuseStep 2326391 = 3489587) B3489587
theorem B3489655 : Blo 1224430 3489655 := bstep (se 1 (by rfl) ⟨2617241, by rfl⟩ : syracuseStep 3489655 = 5234483) B5234483
theorem B6201359 : Blo 1224430 6201359 := bstep (se 1 (by rfl) ⟨4651019, by rfl⟩ : syracuseStep 6201359 = 9302039) B9302039
theorem B4653071 : Blo 1224430 4653071 := bstep (se 1 (by rfl) ⟨3489803, by rfl⟩ : syracuseStep 4653071 = 6979607) B6979607
theorem B23535947 : Blo 1224430 23535947 := bstep (se 1 (by rfl) ⟨17651960, by rfl⟩ : syracuseStep 23535947 = 35303921) B35303921
theorem B2097595 : Blo 1224430 2097595 := bstep (se 1 (by rfl) ⟨1573196, by rfl⟩ : syracuseStep 2097595 = 3146393) B3146393
theorem B2482697 : Blo 1224430 2482697 := bstep (se 2 (by rfl) ⟨931011, by rfl⟩ : syracuseStep 2482697 = 1862023) B1862023
theorem B2327059 : Blo 1224430 2327059 := bstep (se 1 (by rfl) ⟨1745294, by rfl⟩ : syracuseStep 2327059 = 3490589) B3490589
theorem B47121101 : Blo 1224430 47121101 := bstep (se 3 (by rfl) ⟨8835206, by rfl⟩ : syracuseStep 47121101 = 17670413) B17670413
theorem B56640217 : Blo 1224430 56640217 := bstep (se 2 (by rfl) ⟨21240081, by rfl⟩ : syracuseStep 56640217 = 42480163) B42480163
theorem B2327287 : Blo 1224430 2327287 := bstep (se 1 (by rfl) ⟨1745465, by rfl⟩ : syracuseStep 2327287 = 3490931) B3490931
theorem B8946607 : Blo 1224430 8946607 := bstep (se 1 (by rfl) ⟨6709955, by rfl⟩ : syracuseStep 8946607 = 13419911) B13419911
theorem B4137911 : Blo 1224430 4137911 := bstep (se 1 (by rfl) ⟨3103433, by rfl⟩ : syracuseStep 4137911 = 6206867) B6206867
theorem B3310523 : Blo 1224430 3310523 := bstep (se 1 (by rfl) ⟨2482892, by rfl⟩ : syracuseStep 3310523 = 4965785) B4965785
theorem B15705089 : Blo 1224430 15705089 := bstep (se 2 (by rfl) ⟨5889408, by rfl⟩ : syracuseStep 15705089 = 11778817) B11778817
theorem B2327591 : Blo 1224430 2327591 := bstep (se 1 (by rfl) ⟨1745693, by rfl⟩ : syracuseStep 2327591 = 3491387) B3491387
theorem B4195385 : Blo 1224430 4195385 := bstep (se 2 (by rfl) ⟨1573269, by rfl⟩ : syracuseStep 4195385 = 3146539) B3146539
theorem B12584089 : Blo 1224430 12584089 := bstep (se 2 (by rfl) ⟨4719033, by rfl⟩ : syracuseStep 12584089 = 9438067) B9438067
theorem B9938123 : Blo 1224430 9938123 := bstep (se 1 (by rfl) ⟨7453592, by rfl⟩ : syracuseStep 9938123 = 14907185) B14907185
theorem B1656169 : Blo 1224430 1656169 := bstep (se 2 (by rfl) ⟨621063, by rfl⟩ : syracuseStep 1656169 = 1242127) B1242127
theorem B6981065 : Blo 1224430 6981065 := bstep (se 2 (by rfl) ⟨2617899, by rfl⟩ : syracuseStep 6981065 = 5235799) B5235799
theorem B4138505 : Blo 1224430 4138505 := bstep (se 2 (by rfl) ⟨1551939, by rfl⟩ : syracuseStep 4138505 = 3103879) B3103879
theorem B6629003 : Blo 1224430 6629003 := bstep (se 1 (by rfl) ⟨4971752, by rfl⟩ : syracuseStep 6629003 = 9943505) B9943505
theorem B1836743 : Blo 1224430 1836743 := bstep (se 1 (by rfl) ⟨1377557, by rfl⟩ : syracuseStep 1836743 = 2755115) B2755115
theorem B2066249 : Blo 1224430 2066249 := bstep (se 2 (by rfl) ⟨774843, by rfl⟩ : syracuseStep 2066249 = 1549687) B1549687
theorem B1836905 : Blo 1224430 1836905 := bstep (se 2 (by rfl) ⟨688839, by rfl⟩ : syracuseStep 1836905 = 1377679) B1377679
theorem B1836983 : Blo 1224430 1836983 := bstep (se 1 (by rfl) ⟨1377737, by rfl⟩ : syracuseStep 1836983 = 2755475) B2755475
theorem B1837019 : Blo 1224430 1837019 := bstep (se 1 (by rfl) ⟨1377764, by rfl⟩ : syracuseStep 1837019 = 2755529) B2755529
theorem B5883911 : Blo 1224430 5883911 := bstep (se 1 (by rfl) ⟨4412933, by rfl⟩ : syracuseStep 5883911 = 8825867) B8825867
theorem B2615303 : Blo 1224430 2615303 := bstep (se 1 (by rfl) ⟨1961477, by rfl⟩ : syracuseStep 2615303 = 3922955) B3922955
theorem B100616215 : Blo 1224430 100616215 := bstep (se 1 (by rfl) ⟨75462161, by rfl⟩ : syracuseStep 100616215 = 150924323) B150924323
theorem B2066681 : Blo 1224430 2066681 := bstep (se 2 (by rfl) ⟨775005, by rfl⟩ : syracuseStep 2066681 = 1550011) B1550011
theorem B32254355 : Blo 1224430 32254355 := bstep (se 1 (by rfl) ⟨24190766, by rfl⟩ : syracuseStep 32254355 = 48381533) B48381533
theorem B2066863 : Blo 1224430 2066863 := bstep (se 1 (by rfl) ⟨1550147, by rfl⟩ : syracuseStep 2066863 = 3100295) B3100295
theorem B1837487 : Blo 1224430 1837487 := bstep (se 1 (by rfl) ⟨1378115, by rfl⟩ : syracuseStep 1837487 = 2756231) B2756231
theorem B2066951 : Blo 1224430 2066951 := bstep (se 1 (by rfl) ⟨1550213, by rfl⟩ : syracuseStep 2066951 = 3100427) B3100427
theorem B1837577 : Blo 1224430 1837577 := bstep (se 2 (by rfl) ⟨689091, by rfl⟩ : syracuseStep 1837577 = 1378183) B1378183
theorem B1837607 : Blo 1224430 1837607 := bstep (se 1 (by rfl) ⟨1378205, by rfl⟩ : syracuseStep 1837607 = 2756411) B2756411
theorem B1550927 : Blo 1224430 1550927 := bstep (se 1 (by rfl) ⟨1163195, by rfl⟩ : syracuseStep 1550927 = 2326391) B2326391
theorem B2755169 : Blo 1224430 2755169 := bstep (se 2 (by rfl) ⟨1033188, by rfl⟩ : syracuseStep 2755169 = 2066377) B2066377
theorem B1837691 : Blo 1224430 1837691 := bstep (se 1 (by rfl) ⟨1378268, by rfl⟩ : syracuseStep 1837691 = 2756537) B2756537
theorem B1378939 : Blo 1224430 1378939 := bstep (se 1 (by rfl) ⟨1034204, by rfl⟩ : syracuseStep 1378939 = 2068409) B2068409
theorem B6204113 : Blo 1224430 6204113 := bstep (se 2 (by rfl) ⟨2326542, by rfl⟩ : syracuseStep 6204113 = 4653085) B4653085
theorem B1837817 : Blo 1224430 1837817 := bstep (se 2 (by rfl) ⟨689181, by rfl⟩ : syracuseStep 1837817 = 1378363) B1378363
theorem B4418297 : Blo 1224430 4418297 := bstep (se 2 (by rfl) ⟨1656861, by rfl⟩ : syracuseStep 4418297 = 3313723) B3313723
theorem B5032777 : Blo 1224430 5032777 := bstep (se 2 (by rfl) ⟨1887291, by rfl⟩ : syracuseStep 5032777 = 3774583) B3774583
theorem B2067295 : Blo 1224430 2067295 := bstep (se 1 (by rfl) ⟨1550471, by rfl⟩ : syracuseStep 2067295 = 3100943) B3100943
theorem B1837919 : Blo 1224430 1837919 := bstep (se 1 (by rfl) ⟨1378439, by rfl⟩ : syracuseStep 1837919 = 2756879) B2756879
theorem B1837931 : Blo 1224430 1837931 := bstep (se 1 (by rfl) ⟨1378448, by rfl⟩ : syracuseStep 1837931 = 2756897) B2756897
theorem B2755511 : Blo 1224430 2755511 := bstep (se 1 (by rfl) ⟨2066633, by rfl⟩ : syracuseStep 2755511 = 4133267) B4133267
theorem B2067383 : Blo 1224430 2067383 := bstep (se 1 (by rfl) ⟨1550537, by rfl⟩ : syracuseStep 2067383 = 3101075) B3101075
theorem B3927055 : Blo 1224430 3927055 := bstep (se 1 (by rfl) ⟨2945291, by rfl⟩ : syracuseStep 3927055 = 5890583) B5890583
theorem B3099667 : Blo 1224430 3099667 := bstep (se 1 (by rfl) ⟨2324750, by rfl⟩ : syracuseStep 3099667 = 4649501) B4649501
theorem B3779641 : Blo 1224430 3779641 := bstep (se 2 (by rfl) ⟨1417365, by rfl⟩ : syracuseStep 3779641 = 2834731) B2834731
theorem B1838159 : Blo 1224430 1838159 := bstep (se 1 (by rfl) ⟨1378619, by rfl⟩ : syracuseStep 1838159 = 2757239) B2757239
theorem B1379407 : Blo 1224430 1379407 := bstep (se 1 (by rfl) ⟨1034555, by rfl⟩ : syracuseStep 1379407 = 2069111) B2069111
theorem B1838279 : Blo 1224430 1838279 := bstep (se 1 (by rfl) ⟨1378709, by rfl⟩ : syracuseStep 1838279 = 2757419) B2757419
theorem B1838441 : Blo 1224430 1838441 := bstep (se 2 (by rfl) ⟨689415, by rfl⟩ : syracuseStep 1838441 = 1378831) B1378831
theorem B22351277 : Blo 1224430 22351277 := bstep (se 3 (by rfl) ⟨4190864, by rfl⟩ : syracuseStep 22351277 = 8381729) B8381729
theorem B1838519 : Blo 1224430 1838519 := bstep (se 1 (by rfl) ⟨1378889, by rfl⟩ : syracuseStep 1838519 = 2757779) B2757779
theorem B1838555 : Blo 1224430 1838555 := bstep (se 1 (by rfl) ⟨1378916, by rfl⟩ : syracuseStep 1838555 = 2757833) B2757833
theorem B2756105 : Blo 1224430 2756105 := bstep (se 2 (by rfl) ⟨1033539, by rfl⟩ : syracuseStep 2756105 = 2067079) B2067079
theorem B2067977 : Blo 1224430 2067977 := bstep (se 2 (by rfl) ⟨775491, by rfl⟩ : syracuseStep 2067977 = 1550983) B1550983
theorem B2068139 : Blo 1224430 2068139 := bstep (se 1 (by rfl) ⟨1551104, by rfl⟩ : syracuseStep 2068139 = 3102209) B3102209
theorem B1224487 : Blo 1224430 1224487 := bstep (se 1 (by rfl) ⟨918365, by rfl⟩ : syracuseStep 1224487 = 1836731) B1836731
theorem B1224527 : Blo 1224430 1224527 := bstep (se 1 (by rfl) ⟨918395, by rfl⟩ : syracuseStep 1224527 = 1836791) B1836791
theorem B2756447 : Blo 1224430 2756447 := bstep (se 1 (by rfl) ⟨2067335, by rfl⟩ : syracuseStep 2756447 = 4134671) B4134671
theorem B1224543 : Blo 1224430 1224543 := bstep (se 1 (by rfl) ⟨918407, by rfl⟩ : syracuseStep 1224543 = 1836815) B1836815
theorem B7958381 : Blo 1224430 7958381 := bstep (se 3 (by rfl) ⟨1492196, by rfl⟩ : syracuseStep 7958381 = 2984393) B2984393
theorem B4132727 : Blo 1224430 4132727 := bstep (se 1 (by rfl) ⟨3099545, by rfl⟩ : syracuseStep 4132727 = 6199091) B6199091
theorem B1224571 : Blo 1224430 1224571 := bstep (se 1 (by rfl) ⟨918428, by rfl⟩ : syracuseStep 1224571 = 1836857) B1836857
theorem B1224623 : Blo 1224430 1224623 := bstep (se 1 (by rfl) ⟨918467, by rfl⟩ : syracuseStep 1224623 = 1836935) B1836935
theorem B1839023 : Blo 1224430 1839023 := bstep (se 1 (by rfl) ⟨1379267, by rfl⟩ : syracuseStep 1839023 = 2758535) B2758535
theorem B1224647 : Blo 1224430 1224647 := bstep (se 1 (by rfl) ⟨918485, by rfl⟩ : syracuseStep 1224647 = 1836971) B1836971
theorem B1224667 : Blo 1224430 1224667 := bstep (se 1 (by rfl) ⟨918500, by rfl⟩ : syracuseStep 1224667 = 1837001) B1837001
theorem B1839113 : Blo 1224430 1839113 := bstep (se 2 (by rfl) ⟨689667, by rfl⟩ : syracuseStep 1839113 = 1379335) B1379335
theorem B2756627 : Blo 1224430 2756627 := bstep (se 1 (by rfl) ⟨2067470, by rfl⟩ : syracuseStep 2756627 = 4134941) B4134941
theorem B1224743 : Blo 1224430 1224743 := bstep (se 1 (by rfl) ⟨918557, by rfl⟩ : syracuseStep 1224743 = 1837115) B1837115
theorem B1839143 : Blo 1224430 1839143 := bstep (se 1 (by rfl) ⟨1379357, by rfl⟩ : syracuseStep 1839143 = 2758715) B2758715
theorem B2068537 : Blo 1224430 2068537 := bstep (se 2 (by rfl) ⟨775701, by rfl⟩ : syracuseStep 2068537 = 1551403) B1551403
theorem B4132943 : Blo 1224430 4132943 := bstep (se 1 (by rfl) ⟨3099707, by rfl⟩ : syracuseStep 4132943 = 6199415) B6199415
theorem B1224783 : Blo 1224430 1224783 := bstep (se 1 (by rfl) ⟨918587, by rfl⟩ : syracuseStep 1224783 = 1837175) B1837175
theorem B3100751 : Blo 1224430 3100751 := bstep (se 1 (by rfl) ⟨2325563, by rfl⟩ : syracuseStep 3100751 = 4651127) B4651127
theorem B1224799 : Blo 1224430 1224799 := bstep (se 1 (by rfl) ⟨918599, by rfl⟩ : syracuseStep 1224799 = 1837199) B1837199
theorem B1224827 : Blo 1224430 1224827 := bstep (se 1 (by rfl) ⟨918620, by rfl⟩ : syracuseStep 1224827 = 1837241) B1837241
theorem B1839227 : Blo 1224430 1839227 := bstep (se 1 (by rfl) ⟨1379420, by rfl⟩ : syracuseStep 1839227 = 2758841) B2758841
theorem B1224879 : Blo 1224430 1224879 := bstep (se 1 (by rfl) ⟨918659, by rfl⟩ : syracuseStep 1224879 = 1837319) B1837319
theorem B1224903 : Blo 1224430 1224903 := bstep (se 1 (by rfl) ⟨918677, by rfl⟩ : syracuseStep 1224903 = 1837355) B1837355
theorem B2068679 : Blo 1224430 2068679 := bstep (se 1 (by rfl) ⟨1551509, by rfl⟩ : syracuseStep 2068679 = 3103019) B3103019
theorem B1224923 : Blo 1224430 1224923 := bstep (se 1 (by rfl) ⟨918692, by rfl⟩ : syracuseStep 1224923 = 1837385) B1837385
theorem B1839353 : Blo 1224430 1839353 := bstep (se 2 (by rfl) ⟨689757, by rfl⟩ : syracuseStep 1839353 = 1379515) B1379515
theorem B1224999 : Blo 1224430 1224999 := bstep (se 1 (by rfl) ⟨918749, by rfl⟩ : syracuseStep 1224999 = 1837499) B1837499
theorem B1225039 : Blo 1224430 1225039 := bstep (se 1 (by rfl) ⟨918779, by rfl⟩ : syracuseStep 1225039 = 1837559) B1837559
theorem B1225055 : Blo 1224430 1225055 := bstep (se 1 (by rfl) ⟨918791, by rfl⟩ : syracuseStep 1225055 = 1837583) B1837583
theorem B1839455 : Blo 1224430 1839455 := bstep (se 1 (by rfl) ⟨1379591, by rfl⟩ : syracuseStep 1839455 = 2759183) B2759183
theorem B2756969 : Blo 1224430 2756969 := bstep (se 2 (by rfl) ⟨1033863, by rfl⟩ : syracuseStep 2756969 = 2067727) B2067727
theorem B2068841 : Blo 1224430 2068841 := bstep (se 2 (by rfl) ⟨775815, by rfl⟩ : syracuseStep 2068841 = 1551631) B1551631
theorem B1839467 : Blo 1224430 1839467 := bstep (se 1 (by rfl) ⟨1379600, by rfl⟩ : syracuseStep 1839467 = 2759201) B2759201
theorem B1225083 : Blo 1224430 1225083 := bstep (se 1 (by rfl) ⟨918812, by rfl⟩ : syracuseStep 1225083 = 1837625) B1837625
theorem B1225135 : Blo 1224430 1225135 := bstep (se 1 (by rfl) ⟨918851, by rfl⟩ : syracuseStep 1225135 = 1837703) B1837703
theorem B1225159 : Blo 1224430 1225159 := bstep (se 1 (by rfl) ⟨918869, by rfl⟩ : syracuseStep 1225159 = 1837739) B1837739
theorem B4133321 : Blo 1224430 4133321 := bstep (se 2 (by rfl) ⟨1549995, by rfl⟩ : syracuseStep 4133321 = 3099991) B3099991
theorem B1225179 : Blo 1224430 1225179 := bstep (se 1 (by rfl) ⟨918884, by rfl⟩ : syracuseStep 1225179 = 1837769) B1837769
theorem B1225255 : Blo 1224430 1225255 := bstep (se 1 (by rfl) ⟨918941, by rfl⟩ : syracuseStep 1225255 = 1837883) B1837883
theorem B1225295 : Blo 1224430 1225295 := bstep (se 1 (by rfl) ⟨918971, by rfl⟩ : syracuseStep 1225295 = 1837943) B1837943
theorem B1225311 : Blo 1224430 1225311 := bstep (se 1 (by rfl) ⟨918983, by rfl⟩ : syracuseStep 1225311 = 1837967) B1837967
theorem B4035169 : Blo 1224430 4035169 := bstep (se 2 (by rfl) ⟨1513188, by rfl⟩ : syracuseStep 4035169 = 3026377) B3026377
theorem B1225339 : Blo 1224430 1225339 := bstep (se 1 (by rfl) ⟨919004, by rfl⟩ : syracuseStep 1225339 = 1838009) B1838009
theorem B1225391 : Blo 1224430 1225391 := bstep (se 1 (by rfl) ⟨919043, by rfl⟩ : syracuseStep 1225391 = 1838087) B1838087
theorem B1225415 : Blo 1224430 1225415 := bstep (se 1 (by rfl) ⟨919061, by rfl⟩ : syracuseStep 1225415 = 1838123) B1838123
theorem B4649683 : Blo 1224430 4649683 := bstep (se 1 (by rfl) ⟨3487262, by rfl⟩ : syracuseStep 4649683 = 6974525) B6974525
theorem B4133591 : Blo 1224430 4133591 := bstep (se 1 (by rfl) ⟨3100193, by rfl⟩ : syracuseStep 4133591 = 6200387) B6200387
theorem B3101399 : Blo 1224430 3101399 := bstep (se 1 (by rfl) ⟨2326049, by rfl⟩ : syracuseStep 3101399 = 4652099) B4652099
theorem B1225435 : Blo 1224430 1225435 := bstep (se 1 (by rfl) ⟨919076, by rfl⟩ : syracuseStep 1225435 = 1838153) B1838153
theorem B2069239 : Blo 1224430 2069239 := bstep (se 1 (by rfl) ⟨1551929, by rfl⟩ : syracuseStep 2069239 = 3103859) B3103859
theorem B1225511 : Blo 1224430 1225511 := bstep (se 1 (by rfl) ⟨919133, by rfl⟩ : syracuseStep 1225511 = 1838267) B1838267
theorem B1225551 : Blo 1224430 1225551 := bstep (se 1 (by rfl) ⟨919163, by rfl⟩ : syracuseStep 1225551 = 1838327) B1838327
theorem B1225567 : Blo 1224430 1225567 := bstep (se 1 (by rfl) ⟨919175, by rfl⟩ : syracuseStep 1225567 = 1838351) B1838351
theorem B1225595 : Blo 1224430 1225595 := bstep (se 1 (by rfl) ⟨919196, by rfl⟩ : syracuseStep 1225595 = 1838393) B1838393
theorem B4133807 : Blo 1224430 4133807 := bstep (se 1 (by rfl) ⟨3100355, by rfl⟩ : syracuseStep 4133807 = 6200711) B6200711
theorem B1225647 : Blo 1224430 1225647 := bstep (se 1 (by rfl) ⟨919235, by rfl⟩ : syracuseStep 1225647 = 1838471) B1838471
theorem B6976439 : Blo 1224430 6976439 := bstep (se 1 (by rfl) ⟨5232329, by rfl⟩ : syracuseStep 6976439 = 10464659) B10464659
theorem B2757563 : Blo 1224430 2757563 := bstep (se 1 (by rfl) ⟨2068172, by rfl⟩ : syracuseStep 2757563 = 4136345) B4136345
theorem B2069435 : Blo 1224430 2069435 := bstep (se 1 (by rfl) ⟨1552076, by rfl⟩ : syracuseStep 2069435 = 3104153) B3104153
theorem B1225671 : Blo 1224430 1225671 := bstep (se 1 (by rfl) ⟨919253, by rfl⟩ : syracuseStep 1225671 = 1838507) B1838507
theorem B1225691 : Blo 1224430 1225691 := bstep (se 1 (by rfl) ⟨919268, by rfl⟩ : syracuseStep 1225691 = 1838537) B1838537
theorem B6132755 : Blo 1224430 6132755 := bstep (se 1 (by rfl) ⟨4599566, by rfl⟩ : syracuseStep 6132755 = 9199133) B9199133
theorem B1225767 : Blo 1224430 1225767 := bstep (se 1 (by rfl) ⟨919325, by rfl⟩ : syracuseStep 1225767 = 1838651) B1838651
theorem B2069543 : Blo 1224430 2069543 := bstep (se 1 (by rfl) ⟨1552157, by rfl⟩ : syracuseStep 2069543 = 3104315) B3104315
theorem B7853107 : Blo 1224430 7853107 := bstep (se 1 (by rfl) ⟨5889830, by rfl⟩ : syracuseStep 7853107 = 11779661) B11779661
theorem B3101753 : Blo 1224430 3101753 := bstep (se 2 (by rfl) ⟨1163157, by rfl⟩ : syracuseStep 3101753 = 2326315) B2326315
theorem B2757689 : Blo 1224430 2757689 := bstep (se 2 (by rfl) ⟨1034133, by rfl⟩ : syracuseStep 2757689 = 2068267) B2068267
theorem B53744705 : Blo 1224430 53744705 := bstep (se 2 (by rfl) ⟨20154264, by rfl⟩ : syracuseStep 53744705 = 40308529) B40308529
theorem B1225807 : Blo 1224430 1225807 := bstep (se 1 (by rfl) ⟨919355, by rfl⟩ : syracuseStep 1225807 = 1838711) B1838711
theorem B6206543 : Blo 1224430 6206543 := bstep (se 1 (by rfl) ⟨4654907, by rfl⟩ : syracuseStep 6206543 = 9309815) B9309815
theorem B1225823 : Blo 1224430 1225823 := bstep (se 1 (by rfl) ⟨919367, by rfl⟩ : syracuseStep 1225823 = 1838735) B1838735
theorem B1225851 : Blo 1224430 1225851 := bstep (se 1 (by rfl) ⟨919388, by rfl⟩ : syracuseStep 1225851 = 1838777) B1838777
theorem B4650155 : Blo 1224430 4650155 := bstep (se 1 (by rfl) ⟨3487616, by rfl⟩ : syracuseStep 4650155 = 6975233) B6975233
theorem B1225903 : Blo 1224430 1225903 := bstep (se 1 (by rfl) ⟨919427, by rfl⟩ : syracuseStep 1225903 = 1838855) B1838855
theorem B1225927 : Blo 1224430 1225927 := bstep (se 1 (by rfl) ⟨919445, by rfl⟩ : syracuseStep 1225927 = 1838891) B1838891
theorem B1225947 : Blo 1224430 1225947 := bstep (se 1 (by rfl) ⟨919460, by rfl⟩ : syracuseStep 1225947 = 1838921) B1838921
theorem B8615159 : Blo 1224430 8615159 := bstep (se 1 (by rfl) ⟨6461369, by rfl⟩ : syracuseStep 8615159 = 12922739) B12922739
theorem B1226023 : Blo 1224430 1226023 := bstep (se 1 (by rfl) ⟨919517, by rfl⟩ : syracuseStep 1226023 = 1839035) B1839035
theorem B1226063 : Blo 1224430 1226063 := bstep (se 1 (by rfl) ⟨919547, by rfl⟩ : syracuseStep 1226063 = 1839095) B1839095
theorem B1226079 : Blo 1224430 1226079 := bstep (se 1 (by rfl) ⟨919559, by rfl⟩ : syracuseStep 1226079 = 1839119) B1839119
theorem B1226107 : Blo 1224430 1226107 := bstep (se 1 (by rfl) ⟨919580, by rfl⟩ : syracuseStep 1226107 = 1839161) B1839161
theorem B2758031 : Blo 1224430 2758031 := bstep (se 1 (by rfl) ⟨2068523, by rfl⟩ : syracuseStep 2758031 = 4137047) B4137047
theorem B1226159 : Blo 1224430 1226159 := bstep (se 1 (by rfl) ⟨919619, by rfl⟩ : syracuseStep 1226159 = 1839239) B1839239
theorem B2209207 : Blo 1224430 2209207 := bstep (se 1 (by rfl) ⟨1656905, by rfl⟩ : syracuseStep 2209207 = 3313811) B3313811
theorem B1226183 : Blo 1224430 1226183 := bstep (se 1 (by rfl) ⟨919637, by rfl⟩ : syracuseStep 1226183 = 1839275) B1839275
theorem B9303497 : Blo 1224430 9303497 := bstep (se 2 (by rfl) ⟨3488811, by rfl⟩ : syracuseStep 9303497 = 6977623) B6977623
theorem B4191689 : Blo 1224430 4191689 := bstep (se 2 (by rfl) ⟨1571883, by rfl⟩ : syracuseStep 4191689 = 3143767) B3143767
theorem B1226203 : Blo 1224430 1226203 := bstep (se 1 (by rfl) ⟨919652, by rfl⟩ : syracuseStep 1226203 = 1839305) B1839305
theorem B2356745 : Blo 1224430 2356745 := bstep (se 2 (by rfl) ⟨883779, by rfl⟩ : syracuseStep 2356745 = 1767559) B1767559
theorem B1963559 : Blo 1224430 1963559 := bstep (se 1 (by rfl) ⟨1472669, by rfl⟩ : syracuseStep 1963559 = 2945339) B2945339
theorem B1226279 : Blo 1224430 1226279 := bstep (se 1 (by rfl) ⟨919709, by rfl⟩ : syracuseStep 1226279 = 1839419) B1839419
theorem B1226319 : Blo 1224430 1226319 := bstep (se 1 (by rfl) ⟨919739, by rfl⟩ : syracuseStep 1226319 = 1839479) B1839479
theorem B1226335 : Blo 1224430 1226335 := bstep (se 1 (by rfl) ⟨919751, by rfl⟩ : syracuseStep 1226335 = 1839503) B1839503
theorem B1226363 : Blo 1224430 1226363 := bstep (se 1 (by rfl) ⟨919772, by rfl⟩ : syracuseStep 1226363 = 1839545) B1839545
theorem B6198929 : Blo 1224430 6198929 := bstep (se 2 (by rfl) ⟨2324598, by rfl⟩ : syracuseStep 6198929 = 4649197) B4649197
theorem B2209451 : Blo 1224430 2209451 := bstep (se 1 (by rfl) ⟨1657088, by rfl⟩ : syracuseStep 2209451 = 3314177) B3314177
theorem B1226415 : Blo 1224430 1226415 := bstep (se 1 (by rfl) ⟨919811, by rfl⟩ : syracuseStep 1226415 = 1839623) B1839623
theorem B2758355 : Blo 1224430 2758355 := bstep (se 1 (by rfl) ⟨2068766, by rfl⟩ : syracuseStep 2758355 = 4137533) B4137533
theorem B4191959 : Blo 1224430 4191959 := bstep (se 1 (by rfl) ⟨3143969, by rfl⟩ : syracuseStep 4191959 = 6287939) B6287939
theorem B6207191 : Blo 1224430 6207191 := bstep (se 1 (by rfl) ⟨4655393, by rfl⟩ : syracuseStep 6207191 = 9310787) B9310787
theorem B19879739 : Blo 1224430 19879739 := bstep (se 1 (by rfl) ⟨14909804, by rfl⟩ : syracuseStep 19879739 = 29819609) B29819609
theorem B2488171 : Blo 1224430 2488171 := bstep (se 1 (by rfl) ⟨1866128, by rfl⟩ : syracuseStep 2488171 = 3732257) B3732257
theorem B26515309 : Blo 1224430 26515309 := bstep (se 3 (by rfl) ⟨4971620, by rfl⟩ : syracuseStep 26515309 = 9943241) B9943241
theorem B6977441 : Blo 1224430 6977441 := bstep (se 2 (by rfl) ⟨2616540, by rfl⟩ : syracuseStep 6977441 = 5233081) B5233081
theorem B19109837 : Blo 1224430 19109837 := bstep (se 3 (by rfl) ⟨3583094, by rfl⟩ : syracuseStep 19109837 = 7166189) B7166189
theorem B1988687 : Blo 1224430 1988687 := bstep (se 1 (by rfl) ⟨1491515, by rfl⟩ : syracuseStep 1988687 = 2983031) B2983031
theorem B14899301 : Blo 1224430 14899301 := bstep (se 4 (by rfl) ⟨1396809, by rfl⟩ : syracuseStep 14899301 = 2793619) B2793619
theorem B1259695 : Blo 1224430 1259695 := bstep (se 1 (by rfl) ⟨944771, by rfl⟩ : syracuseStep 1259695 = 1889543) B1889543
theorem B7854337 : Blo 1224430 7854337 := bstep (se 2 (by rfl) ⟨2945376, by rfl⟩ : syracuseStep 7854337 = 5890753) B5890753
theorem B6289751 : Blo 1224430 6289751 := bstep (se 1 (by rfl) ⟨4717313, by rfl⟩ : syracuseStep 6289751 = 9434627) B9434627
theorem B6977897 : Blo 1224430 6977897 := bstep (se 2 (by rfl) ⟨2616711, by rfl⟩ : syracuseStep 6977897 = 5233423) B5233423
theorem B3488129 : Blo 1224430 3488129 := bstep (se 2 (by rfl) ⟨1308048, by rfl⟩ : syracuseStep 3488129 = 2616097) B2616097
theorem B4971041 : Blo 1224430 4971041 := bstep (se 2 (by rfl) ⟨1864140, by rfl⟩ : syracuseStep 4971041 = 3728281) B3728281
theorem B2325115 : Blo 1224430 2325115 := bstep (se 1 (by rfl) ⟨1743836, by rfl⟩ : syracuseStep 2325115 = 3487673) B3487673
theorem B2759291 : Blo 1224430 2759291 := bstep (se 1 (by rfl) ⟨2069468, by rfl⟩ : syracuseStep 2759291 = 4138937) B4138937
theorem B3488471 : Blo 1224430 3488471 := bstep (se 1 (by rfl) ⟨2616353, by rfl⟩ : syracuseStep 3488471 = 5232707) B5232707
theorem B23550709 : Blo 1224430 23550709 := bstep (se 5 (by rfl) ⟨1103939, by rfl⟩ : syracuseStep 23550709 = 2207879) B2207879
theorem B2759417 : Blo 1224430 2759417 := bstep (se 2 (by rfl) ⟨1034781, by rfl⟩ : syracuseStep 2759417 = 2069563) B2069563
theorem B2325343 : Blo 1224430 2325343 := bstep (se 1 (by rfl) ⟨1744007, by rfl⟩ : syracuseStep 2325343 = 3488015) B3488015
theorem B12598199 : Blo 1224430 12598199 := bstep (se 1 (by rfl) ⟨9448649, by rfl⟩ : syracuseStep 12598199 = 18897299) B18897299
theorem B4652113 : Blo 1224430 4652113 := bstep (se 2 (by rfl) ⟨1744542, by rfl⟩ : syracuseStep 4652113 = 3489085) B3489085
theorem B2325601 : Blo 1224430 2325601 := bstep (se 2 (by rfl) ⟨872100, by rfl⟩ : syracuseStep 2325601 = 1744201) B1744201
theorem B4136183 : Blo 1224430 4136183 := bstep (se 1 (by rfl) ⟨3102137, by rfl⟩ : syracuseStep 4136183 = 6204275) B6204275
theorem B3103991 : Blo 1224430 3103991 := bstep (se 1 (by rfl) ⟨2327993, by rfl⟩ : syracuseStep 3103991 = 4655987) B4655987
theorem B4717835 : Blo 1224430 4717835 := bstep (se 1 (by rfl) ⟨3538376, by rfl⟩ : syracuseStep 4717835 = 7076753) B7076753
theorem B10476823 : Blo 1224430 10476823 := bstep (se 1 (by rfl) ⟨7857617, by rfl⟩ : syracuseStep 10476823 = 15715235) B15715235
theorem B4971881 : Blo 1224430 4971881 := bstep (se 2 (by rfl) ⟨1864455, by rfl⟩ : syracuseStep 4971881 = 3728911) B3728911
theorem B4652417 : Blo 1224430 4652417 := bstep (se 2 (by rfl) ⟨1744656, by rfl⟩ : syracuseStep 4652417 = 3489313) B3489313
theorem B2325935 : Blo 1224430 2325935 := bstep (se 1 (by rfl) ⟨1744451, by rfl⟩ : syracuseStep 2325935 = 3488903) B3488903
theorem B4972013 : Blo 1224430 4972013 := bstep (se 3 (by rfl) ⟨932252, by rfl⟩ : syracuseStep 4972013 = 1864505) B1864505
theorem B5889523 : Blo 1224430 5889523 := bstep (se 1 (by rfl) ⟨4417142, by rfl⟩ : syracuseStep 5889523 = 8834285) B8834285
theorem B9436711 : Blo 1224430 9436711 := bstep (se 1 (by rfl) ⟨7077533, by rfl⟩ : syracuseStep 9436711 = 14155067) B14155067
theorem B4136507 : Blo 1224430 4136507 := bstep (se 1 (by rfl) ⟨3102380, by rfl⟩ : syracuseStep 4136507 = 6204761) B6204761
theorem B1744463 : Blo 1224430 1744463 := bstep (se 1 (by rfl) ⟨1308347, by rfl⟩ : syracuseStep 1744463 = 2616695) B2616695
theorem B11173565 : Blo 1224430 11173565 := bstep (se 3 (by rfl) ⟨2095043, by rfl⟩ : syracuseStep 11173565 = 4190087) B4190087
theorem B4652873 : Blo 1224430 4652873 := bstep (se 2 (by rfl) ⟨1744827, by rfl⟩ : syracuseStep 4652873 = 3489655) B3489655
theorem B4136777 : Blo 1224430 4136777 := bstep (se 2 (by rfl) ⟨1551291, by rfl⟩ : syracuseStep 4136777 = 3102583) B3102583
theorem B6201197 : Blo 1224430 6201197 := bstep (se 3 (by rfl) ⟨1162724, by rfl⟩ : syracuseStep 6201197 = 2325449) B2325449
theorem B14147459 : Blo 1224430 14147459 := bstep (se 1 (by rfl) ⟨10610594, by rfl⟩ : syracuseStep 14147459 = 21221189) B21221189
theorem B10470059 : Blo 1224430 10470059 := bstep (se 1 (by rfl) ⟨7852544, by rfl⟩ : syracuseStep 10470059 = 15705089) B15705089
theorem B4088503 : Blo 1224430 4088503 := bstep (se 1 (by rfl) ⟨3066377, by rfl⟩ : syracuseStep 4088503 = 6132755) B6132755
theorem B4137695 : Blo 1224430 4137695 := bstep (se 1 (by rfl) ⟨3103271, by rfl⟩ : syracuseStep 4137695 = 6206543) B6206543
theorem B5743439 : Blo 1224430 5743439 := bstep (se 1 (by rfl) ⟨4307579, by rfl⟩ : syracuseStep 5743439 = 8615159) B8615159
theorem B6718373 : Blo 1224430 6718373 := bstep (se 4 (by rfl) ⟨629847, by rfl⟩ : syracuseStep 6718373 = 1259695) B1259695
theorem B6202331 : Blo 1224430 6202331 := bstep (se 1 (by rfl) ⟨4651748, by rfl⟩ : syracuseStep 6202331 = 9303497) B9303497
theorem B2794459 : Blo 1224430 2794459 := bstep (se 1 (by rfl) ⟨2095844, by rfl⟩ : syracuseStep 2794459 = 4191689) B4191689
theorem B4654043 : Blo 1224430 4654043 := bstep (se 1 (by rfl) ⟨3490532, by rfl⟩ : syracuseStep 4654043 = 6981065) B6981065
theorem B31400945 : Blo 1224430 31400945 := bstep (se 2 (by rfl) ⟨11775354, by rfl⟩ : syracuseStep 31400945 = 23550709) B23550709
theorem B6710369 : Blo 1224430 6710369 := bstep (se 2 (by rfl) ⟨2516388, by rfl⟩ : syracuseStep 6710369 = 5032777) B5032777
theorem B6202493 : Blo 1224430 6202493 := bstep (se 3 (by rfl) ⟨1162967, by rfl⟩ : syracuseStep 6202493 = 2325935) B2325935
theorem B4138127 : Blo 1224430 4138127 := bstep (se 1 (by rfl) ⟨3103595, by rfl⟩ : syracuseStep 4138127 = 6207191) B6207191
theorem B1377499 : Blo 1224430 1377499 := bstep (se 1 (by rfl) ⟨1033124, by rfl⟩ : syracuseStep 1377499 = 2066249) B2066249
theorem B11928809 : Blo 1224430 11928809 := bstep (se 2 (by rfl) ⟨4473303, by rfl⟩ : syracuseStep 11928809 = 8946607) B8946607
theorem B12739891 : Blo 1224430 12739891 := bstep (se 1 (by rfl) ⟨9554918, by rfl⟩ : syracuseStep 12739891 = 19109837) B19109837
theorem B5236073 : Blo 1224430 5236073 := bstep (se 2 (by rfl) ⟨1963527, by rfl⟩ : syracuseStep 5236073 = 3927055) B3927055
theorem B6620525 : Blo 1224430 6620525 := bstep (se 3 (by rfl) ⟨1241348, by rfl⟩ : syracuseStep 6620525 = 2482697) B2482697
theorem B10470809 : Blo 1224430 10470809 := bstep (se 2 (by rfl) ⟨3926553, by rfl⟩ : syracuseStep 10470809 = 7853107) B7853107
theorem B5236157 : Blo 1224430 5236157 := bstep (se 3 (by rfl) ⟨981779, by rfl⟩ : syracuseStep 5236157 = 1963559) B1963559
theorem B6202817 : Blo 1224430 6202817 := bstep (se 2 (by rfl) ⟨2326056, by rfl⟩ : syracuseStep 6202817 = 4652113) B4652113
theorem B1377787 : Blo 1224430 1377787 := bstep (se 1 (by rfl) ⟨1033340, by rfl⟩ : syracuseStep 1377787 = 2066681) B2066681
theorem B16778785 : Blo 1224430 16778785 := bstep (se 2 (by rfl) ⟨6292044, by rfl⟩ : syracuseStep 16778785 = 12584089) B12584089
theorem B1377967 : Blo 1224430 1377967 := bstep (se 1 (by rfl) ⟨1033475, by rfl⟩ : syracuseStep 1377967 = 2066951) B2066951
theorem B13969097 : Blo 1224430 13969097 := bstep (se 2 (by rfl) ⟨5238411, by rfl⟩ : syracuseStep 13969097 = 10476823) B10476823
theorem B1836779 : Blo 1224430 1836779 := bstep (se 1 (by rfl) ⟨1377584, by rfl⟩ : syracuseStep 1836779 = 2755169) B2755169
theorem B5891869 : Blo 1224430 5891869 := bstep (se 3 (by rfl) ⟨1104725, by rfl⟩ : syracuseStep 5891869 = 2209451) B2209451
theorem B8832901 : Blo 1224430 8832901 := bstep (se 4 (by rfl) ⟨828084, by rfl⟩ : syracuseStep 8832901 = 1656169) B1656169
theorem B1837007 : Blo 1224430 1837007 := bstep (se 1 (by rfl) ⟨1377755, by rfl⟩ : syracuseStep 1837007 = 2755511) B2755511
theorem B8398799 : Blo 1224430 8398799 := bstep (se 1 (by rfl) ⟨6299099, by rfl⟩ : syracuseStep 8398799 = 12598199) B12598199
theorem B1378255 : Blo 1224430 1378255 := bstep (se 1 (by rfl) ⟨1033691, by rfl⟩ : syracuseStep 1378255 = 2067383) B2067383
theorem B1837403 : Blo 1224430 1837403 := bstep (se 1 (by rfl) ⟨1378052, by rfl⟩ : syracuseStep 1837403 = 2756105) B2756105
theorem B1378651 : Blo 1224430 1378651 := bstep (se 1 (by rfl) ⟨1033988, by rfl⟩ : syracuseStep 1378651 = 2067977) B2067977
theorem B1378759 : Blo 1224430 1378759 := bstep (se 1 (by rfl) ⟨1034069, by rfl⟩ : syracuseStep 1378759 = 2068139) B2068139
theorem B7449043 : Blo 1224430 7449043 := bstep (se 1 (by rfl) ⟨5586782, by rfl⟩ : syracuseStep 7449043 = 11173565) B11173565
theorem B1837631 : Blo 1224430 1837631 := bstep (se 1 (by rfl) ⟨1378223, by rfl⟩ : syracuseStep 1837631 = 2756447) B2756447
theorem B2755151 : Blo 1224430 2755151 := bstep (se 1 (by rfl) ⟨2066363, by rfl⟩ : syracuseStep 2755151 = 4132727) B4132727
theorem B9431639 : Blo 1224430 9431639 := bstep (se 1 (by rfl) ⟨7073729, by rfl⟩ : syracuseStep 9431639 = 14147459) B14147459
theorem B1837751 : Blo 1224430 1837751 := bstep (se 1 (by rfl) ⟨1378313, by rfl⟩ : syracuseStep 1837751 = 2756627) B2756627
theorem B134154953 : Blo 1224430 134154953 := bstep (se 2 (by rfl) ⟨50308107, by rfl⟩ : syracuseStep 134154953 = 100616215) B100616215
theorem B2755295 : Blo 1224430 2755295 := bstep (se 1 (by rfl) ⟨2066471, by rfl⟩ : syracuseStep 2755295 = 4132943) B4132943
theorem B2067167 : Blo 1224430 2067167 := bstep (se 1 (by rfl) ⟨1550375, by rfl⟩ : syracuseStep 2067167 = 3100751) B3100751
theorem B1379119 : Blo 1224430 1379119 := bstep (se 1 (by rfl) ⟨1034339, by rfl⟩ : syracuseStep 1379119 = 2068679) B2068679
theorem B15690631 : Blo 1224430 15690631 := bstep (se 1 (by rfl) ⟨11767973, by rfl⟩ : syracuseStep 15690631 = 23535947) B23535947
theorem B1837979 : Blo 1224430 1837979 := bstep (se 1 (by rfl) ⟨1378484, by rfl⟩ : syracuseStep 1837979 = 2756969) B2756969
theorem B1379227 : Blo 1224430 1379227 := bstep (se 1 (by rfl) ⟨1034420, by rfl⟩ : syracuseStep 1379227 = 2068841) B2068841
theorem B2755547 : Blo 1224430 2755547 := bstep (se 1 (by rfl) ⟨2066660, by rfl⟩ : syracuseStep 2755547 = 4133321) B4133321
theorem B10472449 : Blo 1224430 10472449 := bstep (se 2 (by rfl) ⟨3927168, by rfl⟩ : syracuseStep 10472449 = 7854337) B7854337
theorem B2755727 : Blo 1224430 2755727 := bstep (se 1 (by rfl) ⟨2066795, by rfl⟩ : syracuseStep 2755727 = 4133591) B4133591
theorem B2067599 : Blo 1224430 2067599 := bstep (se 1 (by rfl) ⟨1550699, by rfl⟩ : syracuseStep 2067599 = 3101399) B3101399
theorem B2755817 : Blo 1224430 2755817 := bstep (se 2 (by rfl) ⟨1033431, by rfl⟩ : syracuseStep 2755817 = 2066863) B2066863
theorem B2755871 : Blo 1224430 2755871 := bstep (se 1 (by rfl) ⟨2066903, by rfl⟩ : syracuseStep 2755871 = 4133807) B4133807
theorem B2207015 : Blo 1224430 2207015 := bstep (se 1 (by rfl) ⟨1655261, by rfl⟩ : syracuseStep 2207015 = 3310523) B3310523
theorem B1838375 : Blo 1224430 1838375 := bstep (se 1 (by rfl) ⟨1378781, by rfl⟩ : syracuseStep 1838375 = 2757563) B2757563
theorem B1379623 : Blo 1224430 1379623 := bstep (se 1 (by rfl) ⟨1034717, by rfl⟩ : syracuseStep 1379623 = 2069435) B2069435
theorem B1551727 : Blo 1224430 1551727 := bstep (se 1 (by rfl) ⟨1163795, by rfl⟩ : syracuseStep 1551727 = 2327591) B2327591
theorem B1379695 : Blo 1224430 1379695 := bstep (se 1 (by rfl) ⟨1034771, by rfl⟩ : syracuseStep 1379695 = 2069543) B2069543
theorem B2067835 : Blo 1224430 2067835 := bstep (se 1 (by rfl) ⟨1550876, by rfl⟩ : syracuseStep 2067835 = 3101753) B3101753
theorem B1838459 : Blo 1224430 1838459 := bstep (se 1 (by rfl) ⟨1378844, by rfl⟩ : syracuseStep 1838459 = 2757689) B2757689
theorem B2796923 : Blo 1224430 2796923 := bstep (se 1 (by rfl) ⟨2097692, by rfl⟩ : syracuseStep 2796923 = 4195385) B4195385
theorem B3100103 : Blo 1224430 3100103 := bstep (se 1 (by rfl) ⟨2325077, by rfl⟩ : syracuseStep 3100103 = 4650155) B4650155
theorem B3100153 : Blo 1224430 3100153 := bstep (se 2 (by rfl) ⟨1162557, by rfl⟩ : syracuseStep 3100153 = 2325115) B2325115
theorem B1838585 : Blo 1224430 1838585 := bstep (se 2 (by rfl) ⟨689469, by rfl⟩ : syracuseStep 1838585 = 1378939) B1378939
theorem B1838687 : Blo 1224430 1838687 := bstep (se 1 (by rfl) ⟨1379015, by rfl⟩ : syracuseStep 1838687 = 2758031) B2758031
theorem B4419335 : Blo 1224430 4419335 := bstep (se 1 (by rfl) ⟨3314501, by rfl⟩ : syracuseStep 4419335 = 6629003) B6629003
theorem B4132619 : Blo 1224430 4132619 := bstep (se 1 (by rfl) ⟨3099464, by rfl⟩ : syracuseStep 4132619 = 6198929) B6198929
theorem B3100457 : Blo 1224430 3100457 := bstep (se 2 (by rfl) ⟨1162671, by rfl⟩ : syracuseStep 3100457 = 2325343) B2325343
theorem B2756393 : Blo 1224430 2756393 := bstep (se 2 (by rfl) ⟨1033647, by rfl⟩ : syracuseStep 2756393 = 2067295) B2067295
theorem B1224495 : Blo 1224430 1224495 := bstep (se 1 (by rfl) ⟨918371, by rfl⟩ : syracuseStep 1224495 = 1836743) B1836743
theorem B84889397 : Blo 1224430 84889397 := bstep (se 5 (by rfl) ⟨3979190, by rfl⟩ : syracuseStep 84889397 = 7958381) B7958381
theorem B1838903 : Blo 1224430 1838903 := bstep (se 1 (by rfl) ⟨1379177, by rfl⟩ : syracuseStep 1838903 = 2758355) B2758355
theorem B1224603 : Blo 1224430 1224603 := bstep (se 1 (by rfl) ⟨918452, by rfl⟩ : syracuseStep 1224603 = 1836905) B1836905
theorem B1224655 : Blo 1224430 1224655 := bstep (se 1 (by rfl) ⟨918491, by rfl⟩ : syracuseStep 1224655 = 1836983) B1836983
theorem B1224679 : Blo 1224430 1224679 := bstep (se 1 (by rfl) ⟨918509, by rfl⟩ : syracuseStep 1224679 = 1837019) B1837019
theorem B4132889 : Blo 1224430 4132889 := bstep (se 2 (by rfl) ⟨1549833, by rfl⟩ : syracuseStep 4132889 = 3099667) B3099667
theorem B9932867 : Blo 1224430 9932867 := bstep (se 1 (by rfl) ⟨7449650, by rfl⟩ : syracuseStep 9932867 = 14899301) B14899301
theorem B1839209 : Blo 1224430 1839209 := bstep (se 2 (by rfl) ⟨689703, by rfl⟩ : syracuseStep 1839209 = 1379407) B1379407
theorem B3100801 : Blo 1224430 3100801 := bstep (se 2 (by rfl) ⟨1162800, by rfl⟩ : syracuseStep 3100801 = 2325601) B2325601
theorem B1224991 : Blo 1224430 1224991 := bstep (se 1 (by rfl) ⟨918743, by rfl⟩ : syracuseStep 1224991 = 1837487) B1837487
theorem B1225051 : Blo 1224430 1225051 := bstep (se 1 (by rfl) ⟨918788, by rfl⟩ : syracuseStep 1225051 = 1837577) B1837577
theorem B3314027 : Blo 1224430 3314027 := bstep (se 1 (by rfl) ⟨2485520, by rfl⟩ : syracuseStep 3314027 = 4971041) B4971041
theorem B1225071 : Blo 1224430 1225071 := bstep (se 1 (by rfl) ⟨918803, by rfl⟩ : syracuseStep 1225071 = 1837607) B1837607
theorem B1225127 : Blo 1224430 1225127 := bstep (se 1 (by rfl) ⟨918845, by rfl⟩ : syracuseStep 1225127 = 1837691) B1837691
theorem B1839527 : Blo 1224430 1839527 := bstep (se 1 (by rfl) ⟨1379645, by rfl⟩ : syracuseStep 1839527 = 2759291) B2759291
theorem B1225211 : Blo 1224430 1225211 := bstep (se 1 (by rfl) ⟨918908, by rfl⟩ : syracuseStep 1225211 = 1837817) B1837817
theorem B2945531 : Blo 1224430 2945531 := bstep (se 1 (by rfl) ⟨2209148, by rfl⟩ : syracuseStep 2945531 = 4418297) B4418297
theorem B1839611 : Blo 1224430 1839611 := bstep (se 1 (by rfl) ⟨1379708, by rfl⟩ : syracuseStep 1839611 = 2759417) B2759417
theorem B11178557 : Blo 1224430 11178557 := bstep (se 3 (by rfl) ⟨2095979, by rfl⟩ : syracuseStep 11178557 = 4191959) B4191959
theorem B1225279 : Blo 1224430 1225279 := bstep (se 1 (by rfl) ⟨918959, by rfl⟩ : syracuseStep 1225279 = 1837919) B1837919
theorem B1225287 : Blo 1224430 1225287 := bstep (se 1 (by rfl) ⟨918965, by rfl⟩ : syracuseStep 1225287 = 1837931) B1837931
theorem B2945609 : Blo 1224430 2945609 := bstep (se 2 (by rfl) ⟨1104603, by rfl⟩ : syracuseStep 2945609 = 2209207) B2209207
theorem B7852697 : Blo 1224430 7852697 := bstep (se 2 (by rfl) ⟨2944761, by rfl⟩ : syracuseStep 7852697 = 5889523) B5889523
theorem B1225439 : Blo 1224430 1225439 := bstep (se 1 (by rfl) ⟨919079, by rfl⟩ : syracuseStep 1225439 = 1838159) B1838159
theorem B1225519 : Blo 1224430 1225519 := bstep (se 1 (by rfl) ⟨919139, by rfl⟩ : syracuseStep 1225519 = 1838279) B1838279
theorem B2757455 : Blo 1224430 2757455 := bstep (se 1 (by rfl) ⟨2068091, by rfl⟩ : syracuseStep 2757455 = 4136183) B4136183
theorem B2069327 : Blo 1224430 2069327 := bstep (se 1 (by rfl) ⟨1551995, by rfl⟩ : syracuseStep 2069327 = 3103991) B3103991
theorem B1225627 : Blo 1224430 1225627 := bstep (se 1 (by rfl) ⟨919220, by rfl⟩ : syracuseStep 1225627 = 1838441) B1838441
theorem B3314587 : Blo 1224430 3314587 := bstep (se 1 (by rfl) ⟨2485940, by rfl⟩ : syracuseStep 3314587 = 4971881) B4971881
theorem B3101611 : Blo 1224430 3101611 := bstep (se 1 (by rfl) ⟨2326208, by rfl⟩ : syracuseStep 3101611 = 4652417) B4652417
theorem B1225679 : Blo 1224430 1225679 := bstep (se 1 (by rfl) ⟨919259, by rfl⟩ : syracuseStep 1225679 = 1838519) B1838519
theorem B1225703 : Blo 1224430 1225703 := bstep (se 1 (by rfl) ⟨919277, by rfl⟩ : syracuseStep 1225703 = 1838555) B1838555
theorem B11187173 : Blo 1224430 11187173 := bstep (se 4 (by rfl) ⟨1048797, by rfl⟩ : syracuseStep 11187173 = 2097595) B2097595
theorem B3314675 : Blo 1224430 3314675 := bstep (se 1 (by rfl) ⟨2486006, by rfl⟩ : syracuseStep 3314675 = 4972013) B4972013
theorem B2757671 : Blo 1224430 2757671 := bstep (se 1 (by rfl) ⟨2068253, by rfl⟩ : syracuseStep 2757671 = 4136507) B4136507
theorem B35353745 : Blo 1224430 35353745 := bstep (se 2 (by rfl) ⟨13257654, by rfl⟩ : syracuseStep 35353745 = 26515309) B26515309
theorem B3101915 : Blo 1224430 3101915 := bstep (se 1 (by rfl) ⟨2326436, by rfl⟩ : syracuseStep 3101915 = 4652873) B4652873
theorem B2757851 : Blo 1224430 2757851 := bstep (se 1 (by rfl) ⟨2068388, by rfl⟩ : syracuseStep 2757851 = 4136777) B4136777
theorem B4134131 : Blo 1224430 4134131 := bstep (se 1 (by rfl) ⟨3100598, by rfl⟩ : syracuseStep 4134131 = 6201197) B6201197
theorem B1226015 : Blo 1224430 1226015 := bstep (se 1 (by rfl) ⟨919511, by rfl⟩ : syracuseStep 1226015 = 1839023) B1839023
theorem B1226075 : Blo 1224430 1226075 := bstep (se 1 (by rfl) ⟨919556, by rfl⟩ : syracuseStep 1226075 = 1839113) B1839113
theorem B4134239 : Blo 1224430 4134239 := bstep (se 1 (by rfl) ⟨3100679, by rfl⟩ : syracuseStep 4134239 = 6201359) B6201359
theorem B3102047 : Blo 1224430 3102047 := bstep (se 1 (by rfl) ⟨2326535, by rfl⟩ : syracuseStep 3102047 = 4653071) B4653071
theorem B1226095 : Blo 1224430 1226095 := bstep (se 1 (by rfl) ⟨919571, by rfl⟩ : syracuseStep 1226095 = 1839143) B1839143
theorem B2758049 : Blo 1224430 2758049 := bstep (se 2 (by rfl) ⟨1034268, by rfl⟩ : syracuseStep 2758049 = 2068537) B2068537
theorem B1226151 : Blo 1224430 1226151 := bstep (se 1 (by rfl) ⟨919613, by rfl⟩ : syracuseStep 1226151 = 1839227) B1839227
theorem B25138613 : Blo 1224430 25138613 := bstep (se 5 (by rfl) ⟨1178372, by rfl⟩ : syracuseStep 25138613 = 2356745) B2356745
theorem B1226235 : Blo 1224430 1226235 := bstep (se 1 (by rfl) ⟨919676, by rfl⟩ : syracuseStep 1226235 = 1839353) B1839353
theorem B1226303 : Blo 1224430 1226303 := bstep (se 1 (by rfl) ⟨919727, by rfl⟩ : syracuseStep 1226303 = 1839455) B1839455
theorem B1226311 : Blo 1224430 1226311 := bstep (se 1 (by rfl) ⟨919733, by rfl⟩ : syracuseStep 1226311 = 1839467) B1839467
theorem B20158085 : Blo 1224430 20158085 := bstep (se 4 (by rfl) ⟨1889820, by rfl⟩ : syracuseStep 20158085 = 3779641) B3779641
theorem B31414067 : Blo 1224430 31414067 := bstep (se 1 (by rfl) ⟨23560550, by rfl⟩ : syracuseStep 31414067 = 47121101) B47121101
theorem B4650959 : Blo 1224430 4650959 := bstep (se 1 (by rfl) ⟨3488219, by rfl⟩ : syracuseStep 4650959 = 6976439) B6976439
theorem B2758607 : Blo 1224430 2758607 := bstep (se 1 (by rfl) ⟨2068955, by rfl⟩ : syracuseStep 2758607 = 4137911) B4137911
theorem B3102745 : Blo 1224430 3102745 := bstep (se 2 (by rfl) ⟨1163529, by rfl⟩ : syracuseStep 3102745 = 2327059) B2327059
theorem B35829803 : Blo 1224430 35829803 := bstep (se 1 (by rfl) ⟨26872352, by rfl⟩ : syracuseStep 35829803 = 53744705) B53744705
theorem B5380225 : Blo 1224430 5380225 := bstep (se 2 (by rfl) ⟨2017584, by rfl⟩ : syracuseStep 5380225 = 4035169) B4035169
theorem B6625415 : Blo 1224430 6625415 := bstep (se 1 (by rfl) ⟨4969061, by rfl⟩ : syracuseStep 6625415 = 9938123) B9938123
theorem B6199577 : Blo 1224430 6199577 := bstep (se 2 (by rfl) ⟨2324841, by rfl⟩ : syracuseStep 6199577 = 4649683) B4649683
theorem B75520289 : Blo 1224430 75520289 := bstep (se 2 (by rfl) ⟨28320108, by rfl⟩ : syracuseStep 75520289 = 56640217) B56640217
theorem B3103049 : Blo 1224430 3103049 := bstep (se 2 (by rfl) ⟨1163643, by rfl⟩ : syracuseStep 3103049 = 2327287) B2327287
theorem B2758985 : Blo 1224430 2758985 := bstep (se 2 (by rfl) ⟨1034619, by rfl⟩ : syracuseStep 2758985 = 2069239) B2069239
theorem B2759003 : Blo 1224430 2759003 := bstep (se 1 (by rfl) ⟨2069252, by rfl⟩ : syracuseStep 2759003 = 4138505) B4138505
theorem B13253159 : Blo 1224430 13253159 := bstep (se 1 (by rfl) ⟨9939869, by rfl⟩ : syracuseStep 13253159 = 19879739) B19879739
theorem B4651627 : Blo 1224430 4651627 := bstep (se 1 (by rfl) ⟨3488720, by rfl⟩ : syracuseStep 4651627 = 6977441) B6977441
theorem B3922607 : Blo 1224430 3922607 := bstep (se 1 (by rfl) ⟨2941955, by rfl⟩ : syracuseStep 3922607 = 5883911) B5883911
theorem B1743535 : Blo 1224430 1743535 := bstep (se 1 (by rfl) ⟨1307651, by rfl⟩ : syracuseStep 1743535 = 2615303) B2615303
theorem B1325791 : Blo 1224430 1325791 := bstep (se 1 (by rfl) ⟨994343, by rfl⟩ : syracuseStep 1325791 = 1988687) B1988687
theorem B4651901 : Blo 1224430 4651901 := bstep (se 3 (by rfl) ⟨872231, by rfl⟩ : syracuseStep 4651901 = 1744463) B1744463
theorem B4135805 : Blo 1224430 4135805 := bstep (se 3 (by rfl) ⟨775463, by rfl⟩ : syracuseStep 4135805 = 1550927) B1550927
theorem B4193167 : Blo 1224430 4193167 := bstep (se 1 (by rfl) ⟨3144875, by rfl⟩ : syracuseStep 4193167 = 6289751) B6289751
theorem B4651931 : Blo 1224430 4651931 := bstep (se 1 (by rfl) ⟨3488948, by rfl⟩ : syracuseStep 4651931 = 6977897) B6977897
theorem B2325419 : Blo 1224430 2325419 := bstep (se 1 (by rfl) ⟨1744064, by rfl⟩ : syracuseStep 2325419 = 3488129) B3488129
theorem B21502903 : Blo 1224430 21502903 := bstep (se 1 (by rfl) ⟨16127177, by rfl⟩ : syracuseStep 21502903 = 32254355) B32254355
theorem B4136075 : Blo 1224430 4136075 := bstep (se 1 (by rfl) ⟨3102056, by rfl⟩ : syracuseStep 4136075 = 6204113) B6204113
theorem B2325647 : Blo 1224430 2325647 := bstep (se 1 (by rfl) ⟨1744235, by rfl⟩ : syracuseStep 2325647 = 3488471) B3488471
theorem B12582281 : Blo 1224430 12582281 := bstep (se 2 (by rfl) ⟨4718355, by rfl⟩ : syracuseStep 12582281 = 9436711) B9436711
theorem B3145223 : Blo 1224430 3145223 := bstep (se 1 (by rfl) ⟨2358917, by rfl⟩ : syracuseStep 3145223 = 4717835) B4717835
theorem B14900851 : Blo 1224430 14900851 := bstep (se 1 (by rfl) ⟨11175638, by rfl⟩ : syracuseStep 14900851 = 22351277) B22351277
theorem B3317561 : Blo 1224430 3317561 := bstep (se 2 (by rfl) ⟨1244085, by rfl⟩ : syracuseStep 3317561 = 2488171) B2488171
theorem B4136993 : Blo 1224430 4136993 := bstep (se 2 (by rfl) ⟨1551372, by rfl⟩ : syracuseStep 4136993 = 3102745) B3102745
theorem B5235131 : Blo 1224430 5235131 := bstep (se 1 (by rfl) ⟨3926348, by rfl⟩ : syracuseStep 5235131 = 7852697) B7852697
theorem B6980039 : Blo 1224430 6980039 := bstep (se 1 (by rfl) ⟨5235029, by rfl⟩ : syracuseStep 6980039 = 10470059) B10470059
theorem B31810157 : Blo 1224430 31810157 := bstep (se 3 (by rfl) ⟨5964404, by rfl⟩ : syracuseStep 31810157 = 11928809) B11928809
theorem B23569163 : Blo 1224430 23569163 := bstep (se 1 (by rfl) ⟨17676872, by rfl⟩ : syracuseStep 23569163 = 35353745) B35353745
theorem B6202169 : Blo 1224430 6202169 := bstep (se 2 (by rfl) ⟨2325813, by rfl⟩ : syracuseStep 6202169 = 4651627) B4651627
theorem B3490715 : Blo 1224430 3490715 := bstep (se 1 (by rfl) ⟨2618036, by rfl⟩ : syracuseStep 3490715 = 5236073) B5236073
theorem B6980539 : Blo 1224430 6980539 := bstep (se 1 (by rfl) ⟨5235404, by rfl⟩ : syracuseStep 6980539 = 10470809) B10470809
theorem B3490771 : Blo 1224430 3490771 := bstep (se 1 (by rfl) ⟨2618078, by rfl⟩ : syracuseStep 3490771 = 5236157) B5236157
theorem B67036301 : Blo 1224430 67036301 := bstep (se 3 (by rfl) ⟨12569306, by rfl⟩ : syracuseStep 67036301 = 25138613) B25138613
theorem B7070885 : Blo 1224430 7070885 := bstep (se 4 (by rfl) ⟨662895, by rfl⟩ : syracuseStep 7070885 = 1325791) B1325791
theorem B4416943 : Blo 1224430 4416943 := bstep (se 1 (by rfl) ⟨3312707, by rfl⟩ : syracuseStep 4416943 = 6625415) B6625415
theorem B1836665 : Blo 1224430 1836665 := bstep (se 2 (by rfl) ⟨688749, by rfl⟩ : syracuseStep 1836665 = 1377499) B1377499
theorem B1836767 : Blo 1224430 1836767 := bstep (se 1 (by rfl) ⟨1377575, by rfl⟩ : syracuseStep 1836767 = 2755151) B2755151
theorem B1836863 : Blo 1224430 1836863 := bstep (se 1 (by rfl) ⟨1377647, by rfl⟩ : syracuseStep 1836863 = 2755295) B2755295
theorem B1378111 : Blo 1224430 1378111 := bstep (se 1 (by rfl) ⟨1033583, by rfl⟩ : syracuseStep 1378111 = 2067167) B2067167
theorem B1550279 : Blo 1224430 1550279 := bstep (se 1 (by rfl) ⟨1162709, by rfl⟩ : syracuseStep 1550279 = 2325419) B2325419
theorem B1837031 : Blo 1224430 1837031 := bstep (se 1 (by rfl) ⟨1377773, by rfl⟩ : syracuseStep 1837031 = 2755547) B2755547
theorem B1837049 : Blo 1224430 1837049 := bstep (se 2 (by rfl) ⟨688893, by rfl⟩ : syracuseStep 1837049 = 1377787) B1377787
theorem B1837151 : Blo 1224430 1837151 := bstep (se 1 (by rfl) ⟨1377863, by rfl⟩ : syracuseStep 1837151 = 2755727) B2755727
theorem B1550431 : Blo 1224430 1550431 := bstep (se 1 (by rfl) ⟨1162823, by rfl⟩ : syracuseStep 1550431 = 2325647) B2325647
theorem B1378399 : Blo 1224430 1378399 := bstep (se 1 (by rfl) ⟨1033799, by rfl⟩ : syracuseStep 1378399 = 2067599) B2067599
theorem B19867801 : Blo 1224430 19867801 := bstep (se 2 (by rfl) ⟨7450425, by rfl⟩ : syracuseStep 19867801 = 14900851) B14900851
theorem B1837211 : Blo 1224430 1837211 := bstep (se 1 (by rfl) ⟨1377908, by rfl⟩ : syracuseStep 1837211 = 2755817) B2755817
theorem B1837247 : Blo 1224430 1837247 := bstep (se 1 (by rfl) ⟨1377935, by rfl⟩ : syracuseStep 1837247 = 2755871) B2755871
theorem B1837289 : Blo 1224430 1837289 := bstep (se 2 (by rfl) ⟨688983, by rfl⟩ : syracuseStep 1837289 = 1377967) B1377967
theorem B2066735 : Blo 1224430 2066735 := bstep (se 1 (by rfl) ⟨1550051, by rfl⟩ : syracuseStep 2066735 = 3100103) B3100103
theorem B2755079 : Blo 1224430 2755079 := bstep (se 1 (by rfl) ⟨2066309, by rfl⟩ : syracuseStep 2755079 = 4132619) B4132619
theorem B2066971 : Blo 1224430 2066971 := bstep (se 1 (by rfl) ⟨1550228, by rfl⟩ : syracuseStep 2066971 = 3100457) B3100457
theorem B1837595 : Blo 1224430 1837595 := bstep (se 1 (by rfl) ⟨1378196, by rfl⟩ : syracuseStep 1837595 = 2756393) B2756393
theorem B56592931 : Blo 1224430 56592931 := bstep (se 1 (by rfl) ⟨42444698, by rfl⟩ : syracuseStep 56592931 = 84889397) B84889397
theorem B1837673 : Blo 1224430 1837673 := bstep (se 2 (by rfl) ⟨689127, by rfl⟩ : syracuseStep 1837673 = 1378255) B1378255
theorem B2755259 : Blo 1224430 2755259 := bstep (se 1 (by rfl) ⟨2066444, by rfl⟩ : syracuseStep 2755259 = 4132889) B4132889
theorem B6621911 : Blo 1224430 6621911 := bstep (se 1 (by rfl) ⟨4966433, by rfl⟩ : syracuseStep 6621911 = 9932867) B9932867
theorem B17894317 : Blo 1224430 17894317 := bstep (se 3 (by rfl) ⟨3355184, by rfl⟩ : syracuseStep 17894317 = 6710369) B6710369
theorem B1838201 : Blo 1224430 1838201 := bstep (se 2 (by rfl) ⟨689325, by rfl⟩ : syracuseStep 1838201 = 1378651) B1378651
theorem B3828959 : Blo 1224430 3828959 := bstep (se 1 (by rfl) ⟨2871719, by rfl⟩ : syracuseStep 3828959 = 5743439) B5743439
theorem B1838303 : Blo 1224430 1838303 := bstep (se 1 (by rfl) ⟨1378727, by rfl⟩ : syracuseStep 1838303 = 2757455) B2757455
theorem B1379551 : Blo 1224430 1379551 := bstep (se 1 (by rfl) ⟨1034663, by rfl⟩ : syracuseStep 1379551 = 2069327) B2069327
theorem B1838345 : Blo 1224430 1838345 := bstep (se 2 (by rfl) ⟨689379, by rfl⟩ : syracuseStep 1838345 = 1378759) B1378759
theorem B9932057 : Blo 1224430 9932057 := bstep (se 2 (by rfl) ⟨3724521, by rfl⟩ : syracuseStep 9932057 = 7449043) B7449043
theorem B7458115 : Blo 1224430 7458115 := bstep (se 1 (by rfl) ⟨5593586, by rfl⟩ : syracuseStep 7458115 = 11187173) B11187173
theorem B20933963 : Blo 1224430 20933963 := bstep (se 1 (by rfl) ⟨15700472, by rfl⟩ : syracuseStep 20933963 = 31400945) B31400945
theorem B1838447 : Blo 1224430 1838447 := bstep (se 1 (by rfl) ⟨1378835, by rfl⟩ : syracuseStep 1838447 = 2757671) B2757671
theorem B2067943 : Blo 1224430 2067943 := bstep (se 1 (by rfl) ⟨1550957, by rfl⟩ : syracuseStep 2067943 = 3101915) B3101915
theorem B1838567 : Blo 1224430 1838567 := bstep (se 1 (by rfl) ⟨1378925, by rfl⟩ : syracuseStep 1838567 = 2757851) B2757851
theorem B2756087 : Blo 1224430 2756087 := bstep (se 1 (by rfl) ⟨2067065, by rfl⟩ : syracuseStep 2756087 = 4134131) B4134131
theorem B2756159 : Blo 1224430 2756159 := bstep (se 1 (by rfl) ⟨2067119, by rfl⟩ : syracuseStep 2756159 = 4134239) B4134239
theorem B2068031 : Blo 1224430 2068031 := bstep (se 1 (by rfl) ⟨1551023, by rfl⟩ : syracuseStep 2068031 = 3102047) B3102047
theorem B5451337 : Blo 1224430 5451337 := bstep (se 2 (by rfl) ⟨2044251, by rfl⟩ : syracuseStep 5451337 = 4088503) B4088503
theorem B1838699 : Blo 1224430 1838699 := bstep (se 1 (by rfl) ⟨1379024, by rfl⟩ : syracuseStep 1838699 = 2758049) B2758049
theorem B1838825 : Blo 1224430 1838825 := bstep (se 2 (by rfl) ⟨689559, by rfl⟩ : syracuseStep 1838825 = 1379119) B1379119
theorem B13438723 : Blo 1224430 13438723 := bstep (se 1 (by rfl) ⟨10079042, by rfl⟩ : syracuseStep 13438723 = 20158085) B20158085
theorem B1224519 : Blo 1224430 1224519 := bstep (se 1 (by rfl) ⟨918389, by rfl⟩ : syracuseStep 1224519 = 1836779) B1836779
theorem B5590889 : Blo 1224430 5590889 := bstep (se 2 (by rfl) ⟨2096583, by rfl⟩ : syracuseStep 5590889 = 4193167) B4193167
theorem B20942711 : Blo 1224430 20942711 := bstep (se 1 (by rfl) ⟨15707033, by rfl⟩ : syracuseStep 20942711 = 31414067) B31414067
theorem B1838969 : Blo 1224430 1838969 := bstep (se 2 (by rfl) ⟨689613, by rfl⟩ : syracuseStep 1838969 = 1379227) B1379227
theorem B4419449 : Blo 1224430 4419449 := bstep (se 2 (by rfl) ⟨1657293, by rfl⟩ : syracuseStep 4419449 = 3314587) B3314587
theorem B1224671 : Blo 1224430 1224671 := bstep (se 1 (by rfl) ⟨918503, by rfl⟩ : syracuseStep 1224671 = 1837007) B1837007
theorem B3100639 : Blo 1224430 3100639 := bstep (se 1 (by rfl) ⟨2325479, by rfl⟩ : syracuseStep 3100639 = 4650959) B4650959
theorem B5599199 : Blo 1224430 5599199 := bstep (se 1 (by rfl) ⟨4199399, by rfl⟩ : syracuseStep 5599199 = 8398799) B8398799
theorem B1839071 : Blo 1224430 1839071 := bstep (se 1 (by rfl) ⟨1379303, by rfl⟩ : syracuseStep 1839071 = 2758607) B2758607
theorem B13963265 : Blo 1224430 13963265 := bstep (se 2 (by rfl) ⟨5236224, by rfl⟩ : syracuseStep 13963265 = 10472449) B10472449
theorem B4133051 : Blo 1224430 4133051 := bstep (se 1 (by rfl) ⟨3099788, by rfl⟩ : syracuseStep 4133051 = 6199577) B6199577
theorem B2068699 : Blo 1224430 2068699 := bstep (se 1 (by rfl) ⟨1551524, by rfl⟩ : syracuseStep 2068699 = 3103049) B3103049
theorem B1839323 : Blo 1224430 1839323 := bstep (se 1 (by rfl) ⟨1379492, by rfl⟩ : syracuseStep 1839323 = 2758985) B2758985
theorem B1224935 : Blo 1224430 1224935 := bstep (se 1 (by rfl) ⟨918701, by rfl⟩ : syracuseStep 1224935 = 1837403) B1837403
theorem B1839335 : Blo 1224430 1839335 := bstep (se 1 (by rfl) ⟨1379501, by rfl⟩ : syracuseStep 1839335 = 2759003) B2759003
theorem B8835439 : Blo 1224430 8835439 := bstep (se 1 (by rfl) ⟨6626579, by rfl⟩ : syracuseStep 8835439 = 13253159) B13253159
theorem B1225087 : Blo 1224430 1225087 := bstep (se 1 (by rfl) ⟨918815, by rfl⟩ : syracuseStep 1225087 = 1837631) B1837631
theorem B1839497 : Blo 1224430 1839497 := bstep (se 2 (by rfl) ⟨689811, by rfl⟩ : syracuseStep 1839497 = 1379623) B1379623
theorem B6287759 : Blo 1224430 6287759 := bstep (se 1 (by rfl) ⟨4715819, by rfl⟩ : syracuseStep 6287759 = 9431639) B9431639
theorem B16986521 : Blo 1224430 16986521 := bstep (se 2 (by rfl) ⟨6369945, by rfl⟩ : syracuseStep 16986521 = 12739891) B12739891
theorem B1225167 : Blo 1224430 1225167 := bstep (se 1 (by rfl) ⟨918875, by rfl⟩ : syracuseStep 1225167 = 1837751) B1837751
theorem B89436635 : Blo 1224430 89436635 := bstep (se 1 (by rfl) ⟨67077476, by rfl⟩ : syracuseStep 89436635 = 134154953) B134154953
theorem B2068969 : Blo 1224430 2068969 := bstep (se 2 (by rfl) ⟨775863, by rfl⟩ : syracuseStep 2068969 = 1551727) B1551727
theorem B1839593 : Blo 1224430 1839593 := bstep (se 2 (by rfl) ⟨689847, by rfl⟩ : syracuseStep 1839593 = 1379695) B1379695
theorem B2757113 : Blo 1224430 2757113 := bstep (se 2 (by rfl) ⟨1033917, by rfl⟩ : syracuseStep 2757113 = 2067835) B2067835
theorem B3101267 : Blo 1224430 3101267 := bstep (se 1 (by rfl) ⟨2325950, by rfl⟩ : syracuseStep 3101267 = 4651901) B4651901
theorem B2757203 : Blo 1224430 2757203 := bstep (se 1 (by rfl) ⟨2067902, by rfl⟩ : syracuseStep 2757203 = 4135805) B4135805
theorem B3101287 : Blo 1224430 3101287 := bstep (se 1 (by rfl) ⟨2325965, by rfl⟩ : syracuseStep 3101287 = 4651931) B4651931
theorem B1225319 : Blo 1224430 1225319 := bstep (se 1 (by rfl) ⟨918989, by rfl⟩ : syracuseStep 1225319 = 1837979) B1837979
theorem B4133537 : Blo 1224430 4133537 := bstep (se 2 (by rfl) ⟨1550076, by rfl⟩ : syracuseStep 4133537 = 3100153) B3100153
theorem B2757383 : Blo 1224430 2757383 := bstep (se 1 (by rfl) ⟨2068037, by rfl⟩ : syracuseStep 2757383 = 4136075) B4136075
theorem B1471343 : Blo 1224430 1471343 := bstep (se 1 (by rfl) ⟨1103507, by rfl⟩ : syracuseStep 1471343 = 2207015) B2207015
theorem B1225583 : Blo 1224430 1225583 := bstep (se 1 (by rfl) ⟨919187, by rfl⟩ : syracuseStep 1225583 = 1838375) B1838375
theorem B1225639 : Blo 1224430 1225639 := bstep (se 1 (by rfl) ⟨919229, by rfl⟩ : syracuseStep 1225639 = 1838459) B1838459
theorem B1864615 : Blo 1224430 1864615 := bstep (se 1 (by rfl) ⟨1398461, by rfl⟩ : syracuseStep 1864615 = 2796923) B2796923
theorem B1225723 : Blo 1224430 1225723 := bstep (se 1 (by rfl) ⟨919292, by rfl⟩ : syracuseStep 1225723 = 1838585) B1838585
theorem B1225791 : Blo 1224430 1225791 := bstep (se 1 (by rfl) ⟨919343, by rfl⟩ : syracuseStep 1225791 = 1838687) B1838687
theorem B2946223 : Blo 1224430 2946223 := bstep (se 1 (by rfl) ⟨2209667, by rfl⟩ : syracuseStep 2946223 = 4419335) B4419335
theorem B11777201 : Blo 1224430 11777201 := bstep (se 2 (by rfl) ⟨4416450, by rfl⟩ : syracuseStep 11777201 = 8832901) B8832901
theorem B1225935 : Blo 1224430 1225935 := bstep (se 1 (by rfl) ⟨919451, by rfl⟩ : syracuseStep 1225935 = 1838903) B1838903
theorem B1226139 : Blo 1224430 1226139 := bstep (se 1 (by rfl) ⟨919604, by rfl⟩ : syracuseStep 1226139 = 1839209) B1839209
theorem B4134401 : Blo 1224430 4134401 := bstep (se 2 (by rfl) ⟨1550400, by rfl⟩ : syracuseStep 4134401 = 3100801) B3100801
theorem B2209351 : Blo 1224430 2209351 := bstep (se 1 (by rfl) ⟨1657013, by rfl⟩ : syracuseStep 2209351 = 3314027) B3314027
theorem B1226351 : Blo 1224430 1226351 := bstep (se 1 (by rfl) ⟨919763, by rfl⟩ : syracuseStep 1226351 = 1839527) B1839527
theorem B1963687 : Blo 1224430 1963687 := bstep (se 1 (by rfl) ⟨1472765, by rfl⟩ : syracuseStep 1963687 = 2945531) B2945531
theorem B1226407 : Blo 1224430 1226407 := bstep (se 1 (by rfl) ⟨919805, by rfl⟩ : syracuseStep 1226407 = 1839611) B1839611
theorem B7452371 : Blo 1224430 7452371 := bstep (se 1 (by rfl) ⟨5589278, by rfl⟩ : syracuseStep 7452371 = 11178557) B11178557
theorem B1963739 : Blo 1224430 1963739 := bstep (se 1 (by rfl) ⟨1472804, by rfl⟩ : syracuseStep 1963739 = 2945609) B2945609
theorem B2758463 : Blo 1224430 2758463 := bstep (se 1 (by rfl) ⟨2068847, by rfl⟩ : syracuseStep 2758463 = 4137695) B4137695
theorem B4478915 : Blo 1224430 4478915 := bstep (se 1 (by rfl) ⟨3359186, by rfl⟩ : syracuseStep 4478915 = 6718373) B6718373
theorem B4134887 : Blo 1224430 4134887 := bstep (se 1 (by rfl) ⟨3101165, by rfl⟩ : syracuseStep 4134887 = 6202331) B6202331
theorem B3102695 : Blo 1224430 3102695 := bstep (se 1 (by rfl) ⟨2327021, by rfl⟩ : syracuseStep 3102695 = 4654043) B4654043
theorem B2209783 : Blo 1224430 2209783 := bstep (se 1 (by rfl) ⟨1657337, by rfl⟩ : syracuseStep 2209783 = 3314675) B3314675
theorem B28694533 : Blo 1224430 28694533 := bstep (se 4 (by rfl) ⟨2690112, by rfl⟩ : syracuseStep 28694533 = 5380225) B5380225
theorem B4134995 : Blo 1224430 4134995 := bstep (se 1 (by rfl) ⟨3101246, by rfl⟩ : syracuseStep 4134995 = 6202493) B6202493
theorem B2758751 : Blo 1224430 2758751 := bstep (se 1 (by rfl) ⟨2069063, by rfl⟩ : syracuseStep 2758751 = 4138127) B4138127
theorem B2324713 : Blo 1224430 2324713 := bstep (se 2 (by rfl) ⟨871767, by rfl⟩ : syracuseStep 2324713 = 1743535) B1743535
theorem B4413683 : Blo 1224430 4413683 := bstep (se 1 (by rfl) ⟨3310262, by rfl⟩ : syracuseStep 4413683 = 6620525) B6620525
theorem B4135211 : Blo 1224430 4135211 := bstep (se 1 (by rfl) ⟨3101408, by rfl⟩ : syracuseStep 4135211 = 6202817) B6202817
theorem B33552749 : Blo 1224430 33552749 := bstep (se 3 (by rfl) ⟨6291140, by rfl⟩ : syracuseStep 33552749 = 12582281) B12582281
theorem B9312731 : Blo 1224430 9312731 := bstep (se 1 (by rfl) ⟨6984548, by rfl⟩ : syracuseStep 9312731 = 13969097) B13969097
theorem B20920841 : Blo 1224430 20920841 := bstep (se 2 (by rfl) ⟨7845315, by rfl⟩ : syracuseStep 20920841 = 15690631) B15690631
theorem B4135481 : Blo 1224430 4135481 := bstep (se 2 (by rfl) ⟨1550805, by rfl⟩ : syracuseStep 4135481 = 3101611) B3101611
theorem B28670537 : Blo 1224430 28670537 := bstep (se 2 (by rfl) ⟨10751451, by rfl⟩ : syracuseStep 28670537 = 21502903) B21502903
theorem B3725945 : Blo 1224430 3725945 := bstep (se 2 (by rfl) ⟨1397229, by rfl⟩ : syracuseStep 3725945 = 2794459) B2794459
theorem B23886535 : Blo 1224430 23886535 := bstep (se 1 (by rfl) ⟨17914901, by rfl⟩ : syracuseStep 23886535 = 35829803) B35829803
theorem B50346859 : Blo 1224430 50346859 := bstep (se 1 (by rfl) ⟨37760144, by rfl⟩ : syracuseStep 50346859 = 75520289) B75520289
theorem B10460285 : Blo 1224430 10460285 := bstep (se 3 (by rfl) ⟨1961303, by rfl⟩ : syracuseStep 10460285 = 3922607) B3922607
theorem B22371713 : Blo 1224430 22371713 := bstep (se 2 (by rfl) ⟨8389392, by rfl⟩ : syracuseStep 22371713 = 16778785) B16778785
theorem B2096815 : Blo 1224430 2096815 := bstep (se 1 (by rfl) ⟨1572611, by rfl⟩ : syracuseStep 2096815 = 3145223) B3145223
theorem B7855825 : Blo 1224430 7855825 := bstep (se 2 (by rfl) ⟨2945934, by rfl⟩ : syracuseStep 7855825 = 5891869) B5891869
theorem B2211707 : Blo 1224430 2211707 := bstep (se 1 (by rfl) ⟨1658780, by rfl⟩ : syracuseStep 2211707 = 3317561) B3317561
theorem B4653359 : Blo 1224430 4653359 := bstep (se 1 (by rfl) ⟨3490019, by rfl⟩ : syracuseStep 4653359 = 6980039) B6980039
theorem B11780585 : Blo 1224430 11780585 := bstep (se 2 (by rfl) ⟨4417719, by rfl⟩ : syracuseStep 11780585 = 8835439) B8835439
theorem B15712775 : Blo 1224430 15712775 := bstep (se 1 (by rfl) ⟨11784581, by rfl⟩ : syracuseStep 15712775 = 23569163) B23569163
theorem B2327143 : Blo 1224430 2327143 := bstep (se 1 (by rfl) ⟨1745357, by rfl⟩ : syracuseStep 2327143 = 3490715) B3490715
theorem B75457241 : Blo 1224430 75457241 := bstep (se 2 (by rfl) ⟨28296465, by rfl⟩ : syracuseStep 75457241 = 56592931) B56592931
theorem B89473997 : Blo 1224430 89473997 := bstep (se 3 (by rfl) ⟨16776374, by rfl⟩ : syracuseStep 89473997 = 33552749) B33552749
theorem B13960349 : Blo 1224430 13960349 := bstep (se 3 (by rfl) ⟨2617565, by rfl⟩ : syracuseStep 13960349 = 5235131) B5235131
theorem B9307385 : Blo 1224430 9307385 := bstep (se 2 (by rfl) ⟨3490269, by rfl⟩ : syracuseStep 9307385 = 6980539) B6980539
theorem B4654361 : Blo 1224430 4654361 := bstep (se 2 (by rfl) ⟨1745385, by rfl⟩ : syracuseStep 4654361 = 3490771) B3490771
theorem B2942455 : Blo 1224430 2942455 := bstep (se 1 (by rfl) ⟨2206841, by rfl⟩ : syracuseStep 2942455 = 4413683) B4413683
theorem B1377823 : Blo 1224430 1377823 := bstep (se 1 (by rfl) ⟨1033367, by rfl⟩ : syracuseStep 1377823 = 2066735) B2066735
theorem B1836719 : Blo 1224430 1836719 := bstep (se 1 (by rfl) ⟨1377539, by rfl⟩ : syracuseStep 1836719 = 2755079) B2755079
theorem B2483963 : Blo 1224430 2483963 := bstep (se 1 (by rfl) ⟨1862972, by rfl⟩ : syracuseStep 2483963 = 3725945) B3725945
theorem B1836839 : Blo 1224430 1836839 := bstep (se 1 (by rfl) ⟨1377629, by rfl⟩ : syracuseStep 1836839 = 2755259) B2755259
theorem B6973523 : Blo 1224430 6973523 := bstep (se 1 (by rfl) ⟨5230142, by rfl⟩ : syracuseStep 6973523 = 10460285) B10460285
theorem B7268449 : Blo 1224430 7268449 := bstep (se 2 (by rfl) ⟨2725668, by rfl⟩ : syracuseStep 7268449 = 5451337) B5451337
theorem B6621371 : Blo 1224430 6621371 := bstep (se 1 (by rfl) ⟨4966028, by rfl⟩ : syracuseStep 6621371 = 9932057) B9932057
theorem B2795753 : Blo 1224430 2795753 := bstep (se 2 (by rfl) ⟨1048407, by rfl⟩ : syracuseStep 2795753 = 2096815) B2096815
theorem B1837391 : Blo 1224430 1837391 := bstep (se 1 (by rfl) ⟨1378043, by rfl⟩ : syracuseStep 1837391 = 2756087) B2756087
theorem B17918297 : Blo 1224430 17918297 := bstep (se 2 (by rfl) ⟨6719361, by rfl⟩ : syracuseStep 17918297 = 13438723) B13438723
theorem B1837439 : Blo 1224430 1837439 := bstep (se 1 (by rfl) ⟨1378079, by rfl⟩ : syracuseStep 1837439 = 2756159) B2756159
theorem B1378687 : Blo 1224430 1378687 := bstep (se 1 (by rfl) ⟨1034015, by rfl⟩ : syracuseStep 1378687 = 2068031) B2068031
theorem B1837481 : Blo 1224430 1837481 := bstep (se 2 (by rfl) ⟨689055, by rfl⟩ : syracuseStep 1837481 = 1378111) B1378111
theorem B13961807 : Blo 1224430 13961807 := bstep (se 1 (by rfl) ⟨10471355, by rfl⟩ : syracuseStep 13961807 = 20942711) B20942711
theorem B9308843 : Blo 1224430 9308843 := bstep (se 1 (by rfl) ⟨6981632, by rfl⟩ : syracuseStep 9308843 = 13963265) B13963265
theorem B38259377 : Blo 1224430 38259377 := bstep (se 2 (by rfl) ⟨14347266, by rfl⟩ : syracuseStep 38259377 = 28694533) B28694533
theorem B2755367 : Blo 1224430 2755367 := bstep (se 1 (by rfl) ⟨2066525, by rfl⟩ : syracuseStep 2755367 = 4133051) B4133051
theorem B2067241 : Blo 1224430 2067241 := bstep (se 2 (by rfl) ⟨775215, by rfl⟩ : syracuseStep 2067241 = 1550431) B1550431
theorem B1837865 : Blo 1224430 1837865 := bstep (se 2 (by rfl) ⟨689199, by rfl⟩ : syracuseStep 1837865 = 1378399) B1378399
theorem B11324347 : Blo 1224430 11324347 := bstep (se 1 (by rfl) ⟨8493260, by rfl⟩ : syracuseStep 11324347 = 16986521) B16986521
theorem B3099617 : Blo 1224430 3099617 := bstep (se 2 (by rfl) ⟨1162356, by rfl⟩ : syracuseStep 3099617 = 2324713) B2324713
theorem B59624423 : Blo 1224430 59624423 := bstep (se 1 (by rfl) ⟨44718317, by rfl⟩ : syracuseStep 59624423 = 89436635) B89436635
theorem B1838075 : Blo 1224430 1838075 := bstep (se 1 (by rfl) ⟨1378556, by rfl⟩ : syracuseStep 1838075 = 2757113) B2757113
theorem B2067511 : Blo 1224430 2067511 := bstep (se 1 (by rfl) ⟨1550633, by rfl⟩ : syracuseStep 2067511 = 3101267) B3101267
theorem B1838135 : Blo 1224430 1838135 := bstep (se 1 (by rfl) ⟨1378601, by rfl⟩ : syracuseStep 1838135 = 2757203) B2757203
theorem B2755691 : Blo 1224430 2755691 := bstep (se 1 (by rfl) ⟨2066768, by rfl⟩ : syracuseStep 2755691 = 4133537) B4133537
theorem B1838255 : Blo 1224430 1838255 := bstep (se 1 (by rfl) ⟨1378691, by rfl⟩ : syracuseStep 1838255 = 2757383) B2757383
theorem B2755961 : Blo 1224430 2755961 := bstep (se 2 (by rfl) ⟨1033485, by rfl⟩ : syracuseStep 2755961 = 2066971) B2066971
theorem B44690867 : Blo 1224430 44690867 := bstep (se 1 (by rfl) ⟨33518150, by rfl⟩ : syracuseStep 44690867 = 67036301) B67036301
theorem B4713923 : Blo 1224430 4713923 := bstep (se 1 (by rfl) ⟨3535442, by rfl⟩ : syracuseStep 4713923 = 7070885) B7070885
theorem B7851467 : Blo 1224430 7851467 := bstep (se 1 (by rfl) ⟨5888600, by rfl⟩ : syracuseStep 7851467 = 11777201) B11777201
theorem B2756267 : Blo 1224430 2756267 := bstep (se 1 (by rfl) ⟨2067200, by rfl⟩ : syracuseStep 2756267 = 4134401) B4134401
theorem B1224443 : Blo 1224430 1224443 := bstep (se 1 (by rfl) ⟨918332, by rfl⟩ : syracuseStep 1224443 = 1836665) B1836665
theorem B67129145 : Blo 1224430 67129145 := bstep (se 2 (by rfl) ⟨25173429, by rfl⟩ : syracuseStep 67129145 = 50346859) B50346859
theorem B1224511 : Blo 1224430 1224511 := bstep (se 1 (by rfl) ⟨918383, by rfl⟩ : syracuseStep 1224511 = 1836767) B1836767
theorem B1224575 : Blo 1224430 1224575 := bstep (se 1 (by rfl) ⟨918431, by rfl⟩ : syracuseStep 1224575 = 1836863) B1836863
theorem B1838975 : Blo 1224430 1838975 := bstep (se 1 (by rfl) ⟨1379231, by rfl⟩ : syracuseStep 1838975 = 2758463) B2758463
theorem B2486153 : Blo 1224430 2486153 := bstep (se 2 (by rfl) ⟨932307, by rfl⟩ : syracuseStep 2486153 = 1864615) B1864615
theorem B23859089 : Blo 1224430 23859089 := bstep (se 2 (by rfl) ⟨8947158, by rfl⟩ : syracuseStep 23859089 = 17894317) B17894317
theorem B1224687 : Blo 1224430 1224687 := bstep (se 1 (by rfl) ⟨918515, by rfl⟩ : syracuseStep 1224687 = 1837031) B1837031
theorem B2756591 : Blo 1224430 2756591 := bstep (se 1 (by rfl) ⟨2067443, by rfl⟩ : syracuseStep 2756591 = 4134887) B4134887
theorem B2068463 : Blo 1224430 2068463 := bstep (se 1 (by rfl) ⟨1551347, by rfl⟩ : syracuseStep 2068463 = 3102695) B3102695
theorem B1224699 : Blo 1224430 1224699 := bstep (se 1 (by rfl) ⟨918524, by rfl⟩ : syracuseStep 1224699 = 1837049) B1837049
theorem B2756663 : Blo 1224430 2756663 := bstep (se 1 (by rfl) ⟨2067497, by rfl⟩ : syracuseStep 2756663 = 4134995) B4134995
theorem B1224767 : Blo 1224430 1224767 := bstep (se 1 (by rfl) ⟨918575, by rfl⟩ : syracuseStep 1224767 = 1837151) B1837151
theorem B1839167 : Blo 1224430 1839167 := bstep (se 1 (by rfl) ⟨1379375, by rfl⟩ : syracuseStep 1839167 = 2758751) B2758751
theorem B1224807 : Blo 1224430 1224807 := bstep (se 1 (by rfl) ⟨918605, by rfl⟩ : syracuseStep 1224807 = 1837211) B1837211
theorem B1224831 : Blo 1224430 1224831 := bstep (se 1 (by rfl) ⟨918623, by rfl⟩ : syracuseStep 1224831 = 1837247) B1837247
theorem B1224859 : Blo 1224430 1224859 := bstep (se 1 (by rfl) ⟨918644, by rfl⟩ : syracuseStep 1224859 = 1837289) B1837289
theorem B2756807 : Blo 1224430 2756807 := bstep (se 1 (by rfl) ⟨2067605, by rfl⟩ : syracuseStep 2756807 = 4135211) B4135211
theorem B3928297 : Blo 1224430 3928297 := bstep (se 2 (by rfl) ⟨1473111, by rfl⟩ : syracuseStep 3928297 = 2946223) B2946223
theorem B1839401 : Blo 1224430 1839401 := bstep (se 2 (by rfl) ⟨689775, by rfl⟩ : syracuseStep 1839401 = 1379551) B1379551
theorem B13947227 : Blo 1224430 13947227 := bstep (se 1 (by rfl) ⟨10460420, by rfl⟩ : syracuseStep 13947227 = 20920841) B20920841
theorem B1225063 : Blo 1224430 1225063 := bstep (se 1 (by rfl) ⟨918797, by rfl⟩ : syracuseStep 1225063 = 1837595) B1837595
theorem B2756987 : Blo 1224430 2756987 := bstep (se 1 (by rfl) ⟨2067740, by rfl⟩ : syracuseStep 2756987 = 4135481) B4135481
theorem B1225115 : Blo 1224430 1225115 := bstep (se 1 (by rfl) ⟨918836, by rfl⟩ : syracuseStep 1225115 = 1837673) B1837673
theorem B2757257 : Blo 1224430 2757257 := bstep (se 2 (by rfl) ⟨1033971, by rfl⟩ : syracuseStep 2757257 = 2067943) B2067943
theorem B1225467 : Blo 1224430 1225467 := bstep (se 1 (by rfl) ⟨919100, by rfl⟩ : syracuseStep 1225467 = 1838201) B1838201
theorem B2945801 : Blo 1224430 2945801 := bstep (se 2 (by rfl) ⟨1104675, by rfl⟩ : syracuseStep 2945801 = 2209351) B2209351
theorem B2552639 : Blo 1224430 2552639 := bstep (se 1 (by rfl) ⟨1914479, by rfl⟩ : syracuseStep 2552639 = 3828959) B3828959
theorem B1225535 : Blo 1224430 1225535 := bstep (se 1 (by rfl) ⟨919151, by rfl⟩ : syracuseStep 1225535 = 1838303) B1838303
theorem B1225563 : Blo 1224430 1225563 := bstep (se 1 (by rfl) ⟨919172, by rfl⟩ : syracuseStep 1225563 = 1838345) B1838345
theorem B13955975 : Blo 1224430 13955975 := bstep (se 1 (by rfl) ⟨10466981, by rfl⟩ : syracuseStep 13955975 = 20933963) B20933963
theorem B2618249 : Blo 1224430 2618249 := bstep (se 2 (by rfl) ⟨981843, by rfl⟩ : syracuseStep 2618249 = 1963687) B1963687
theorem B1225631 : Blo 1224430 1225631 := bstep (se 1 (by rfl) ⟨919223, by rfl⟩ : syracuseStep 1225631 = 1838447) B1838447
theorem B14914475 : Blo 1224430 14914475 := bstep (se 1 (by rfl) ⟨11185856, by rfl⟩ : syracuseStep 14914475 = 22371713) B22371713
theorem B10474433 : Blo 1224430 10474433 := bstep (se 2 (by rfl) ⟨3927912, by rfl⟩ : syracuseStep 10474433 = 7855825) B7855825
theorem B1225711 : Blo 1224430 1225711 := bstep (se 1 (by rfl) ⟨919283, by rfl⟩ : syracuseStep 1225711 = 1838567) B1838567
theorem B1225799 : Blo 1224430 1225799 := bstep (se 1 (by rfl) ⟨919349, by rfl⟩ : syracuseStep 1225799 = 1838699) B1838699
theorem B1225883 : Blo 1224430 1225883 := bstep (se 1 (by rfl) ⟨919412, by rfl⟩ : syracuseStep 1225883 = 1838825) B1838825
theorem B4134077 : Blo 1224430 4134077 := bstep (se 3 (by rfl) ⟨775139, by rfl⟩ : syracuseStep 4134077 = 1550279) B1550279
theorem B1225979 : Blo 1224430 1225979 := bstep (se 1 (by rfl) ⟨919484, by rfl⟩ : syracuseStep 1225979 = 1838969) B1838969
theorem B2946299 : Blo 1224430 2946299 := bstep (se 1 (by rfl) ⟨2209724, by rfl⟩ : syracuseStep 2946299 = 4419449) B4419449
theorem B4134185 : Blo 1224430 4134185 := bstep (se 2 (by rfl) ⟨1550319, by rfl⟩ : syracuseStep 4134185 = 3100639) B3100639
theorem B3732799 : Blo 1224430 3732799 := bstep (se 1 (by rfl) ⟨2799599, by rfl⟩ : syracuseStep 3732799 = 5599199) B5599199
theorem B1226047 : Blo 1224430 1226047 := bstep (se 1 (by rfl) ⟨919535, by rfl⟩ : syracuseStep 1226047 = 1839071) B1839071
theorem B2946377 : Blo 1224430 2946377 := bstep (se 2 (by rfl) ⟨1104891, by rfl⟩ : syracuseStep 2946377 = 2209783) B2209783
theorem B2757995 : Blo 1224430 2757995 := bstep (se 1 (by rfl) ⟨2068496, by rfl⟩ : syracuseStep 2757995 = 4136993) B4136993
theorem B1226215 : Blo 1224430 1226215 := bstep (se 1 (by rfl) ⟨919661, by rfl⟩ : syracuseStep 1226215 = 1839323) B1839323
theorem B1226223 : Blo 1224430 1226223 := bstep (se 1 (by rfl) ⟨919667, by rfl⟩ : syracuseStep 1226223 = 1839335) B1839335
theorem B26490401 : Blo 1224430 26490401 := bstep (se 2 (by rfl) ⟨9933900, by rfl⟩ : syracuseStep 26490401 = 19867801) B19867801
theorem B1226331 : Blo 1224430 1226331 := bstep (se 1 (by rfl) ⟨919748, by rfl⟩ : syracuseStep 1226331 = 1839497) B1839497
theorem B4191839 : Blo 1224430 4191839 := bstep (se 1 (by rfl) ⟨3143879, by rfl⟩ : syracuseStep 4191839 = 6287759) B6287759
theorem B2758265 : Blo 1224430 2758265 := bstep (se 2 (by rfl) ⟨1034349, by rfl⟩ : syracuseStep 2758265 = 2068699) B2068699
theorem B1226395 : Blo 1224430 1226395 := bstep (se 1 (by rfl) ⟨919796, by rfl⟩ : syracuseStep 1226395 = 1839593) B1839593
theorem B21206771 : Blo 1224430 21206771 := bstep (se 1 (by rfl) ⟨15905078, by rfl⟩ : syracuseStep 21206771 = 31810157) B31810157
theorem B4134779 : Blo 1224430 4134779 := bstep (se 1 (by rfl) ⟨3101084, by rfl⟩ : syracuseStep 4134779 = 6202169) B6202169
theorem B2758625 : Blo 1224430 2758625 := bstep (se 2 (by rfl) ⟨1034484, by rfl⟩ : syracuseStep 2758625 = 2068969) B2068969
theorem B4135049 : Blo 1224430 4135049 := bstep (se 2 (by rfl) ⟨1550643, by rfl⟩ : syracuseStep 4135049 = 3101287) B3101287
theorem B31848713 : Blo 1224430 31848713 := bstep (se 2 (by rfl) ⟨11943267, by rfl⟩ : syracuseStep 31848713 = 23886535) B23886535
theorem B1309159 : Blo 1224430 1309159 := bstep (se 1 (by rfl) ⟨981869, by rfl⟩ : syracuseStep 1309159 = 1963739) B1963739
theorem B76454765 : Blo 1224430 76454765 := bstep (se 3 (by rfl) ⟨14335268, by rfl⟩ : syracuseStep 76454765 = 28670537) B28670537
theorem B6208487 : Blo 1224430 6208487 := bstep (se 1 (by rfl) ⟨4656365, by rfl⟩ : syracuseStep 6208487 = 9312731) B9312731
theorem B9944153 : Blo 1224430 9944153 := bstep (se 2 (by rfl) ⟨3729057, by rfl⟩ : syracuseStep 9944153 = 7458115) B7458115
theorem B4414607 : Blo 1224430 4414607 := bstep (se 1 (by rfl) ⟨3310955, by rfl⟩ : syracuseStep 4414607 = 6621911) B6621911
theorem B19872989 : Blo 1224430 19872989 := bstep (se 3 (by rfl) ⟨3726185, by rfl⟩ : syracuseStep 19872989 = 7452371) B7452371
theorem B5889257 : Blo 1224430 5889257 := bstep (se 2 (by rfl) ⟨2208471, by rfl⟩ : syracuseStep 5889257 = 4416943) B4416943
theorem B3923581 : Blo 1224430 3923581 := bstep (se 3 (by rfl) ⟨735671, by rfl⟩ : syracuseStep 3923581 = 1471343) B1471343
theorem B11943773 : Blo 1224430 11943773 := bstep (se 3 (by rfl) ⟨2239457, by rfl⟩ : syracuseStep 11943773 = 4478915) B4478915
theorem B3727259 : Blo 1224430 3727259 := bstep (se 1 (by rfl) ⟨2795444, by rfl⟩ : syracuseStep 3727259 = 5590889) B5590889
theorem B1474471 : Blo 1224430 1474471 := bstep (se 1 (by rfl) ⟨1105853, by rfl⟩ : syracuseStep 1474471 = 2211707) B2211707
theorem B9691265 : Blo 1224430 9691265 := bstep (se 2 (by rfl) ⟨3634224, by rfl⟩ : syracuseStep 9691265 = 7268449) B7268449
theorem B9298151 : Blo 1224430 9298151 := bstep (se 1 (by rfl) ⟨6973613, by rfl⟩ : syracuseStep 9298151 = 13947227) B13947227
theorem B7455341 : Blo 1224430 7455341 := bstep (se 3 (by rfl) ⟨1397876, by rfl⟩ : syracuseStep 7455341 = 2795753) B2795753
theorem B1745545 : Blo 1224430 1745545 := bstep (se 2 (by rfl) ⟨654579, by rfl⟩ : syracuseStep 1745545 = 1309159) B1309159
theorem B9306899 : Blo 1224430 9306899 := bstep (se 1 (by rfl) ⟨6980174, by rfl⟩ : syracuseStep 9306899 = 13960349) B13960349
theorem B2794559 : Blo 1224430 2794559 := bstep (se 1 (by rfl) ⟨2095919, by rfl⟩ : syracuseStep 2794559 = 4191839) B4191839
theorem B1655975 : Blo 1224430 1655975 := bstep (se 1 (by rfl) ⟨1241981, by rfl⟩ : syracuseStep 1655975 = 2483963) B2483963
theorem B11945531 : Blo 1224430 11945531 := bstep (se 1 (by rfl) ⟨8959148, by rfl⟩ : syracuseStep 11945531 = 17918297) B17918297
theorem B9307871 : Blo 1224430 9307871 := bstep (se 1 (by rfl) ⟨6980903, by rfl⟩ : syracuseStep 9307871 = 13961807) B13961807
theorem B1836911 : Blo 1224430 1836911 := bstep (se 1 (by rfl) ⟨1377683, by rfl⟩ : syracuseStep 1836911 = 2755367) B2755367
theorem B2066411 : Blo 1224430 2066411 := bstep (se 1 (by rfl) ⟨1549808, by rfl⟩ : syracuseStep 2066411 = 3099617) B3099617
theorem B39749615 : Blo 1224430 39749615 := bstep (se 1 (by rfl) ⟨29812211, by rfl⟩ : syracuseStep 39749615 = 59624423) B59624423
theorem B4138991 : Blo 1224430 4138991 := bstep (se 1 (by rfl) ⟨3104243, by rfl⟩ : syracuseStep 4138991 = 6208487) B6208487
theorem B1837097 : Blo 1224430 1837097 := bstep (se 2 (by rfl) ⟨688911, by rfl⟩ : syracuseStep 1837097 = 1377823) B1377823
theorem B6629435 : Blo 1224430 6629435 := bstep (se 1 (by rfl) ⟨4972076, by rfl⟩ : syracuseStep 6629435 = 9944153) B9944153
theorem B1837127 : Blo 1224430 1837127 := bstep (se 1 (by rfl) ⟨1377845, by rfl⟩ : syracuseStep 1837127 = 2755691) B2755691
theorem B2943071 : Blo 1224430 2943071 := bstep (se 1 (by rfl) ⟨2207303, by rfl⟩ : syracuseStep 2943071 = 4414607) B4414607
theorem B13248659 : Blo 1224430 13248659 := bstep (se 1 (by rfl) ⟨9936494, by rfl⟩ : syracuseStep 13248659 = 19872989) B19872989
theorem B3926171 : Blo 1224430 3926171 := bstep (se 1 (by rfl) ⟨2944628, by rfl⟩ : syracuseStep 3926171 = 5889257) B5889257
theorem B1837307 : Blo 1224430 1837307 := bstep (se 1 (by rfl) ⟨1377980, by rfl⟩ : syracuseStep 1837307 = 2755961) B2755961
theorem B6981997 : Blo 1224430 6981997 := bstep (se 3 (by rfl) ⟨1309124, by rfl⟩ : syracuseStep 6981997 = 2618249) B2618249
theorem B1837511 : Blo 1224430 1837511 := bstep (se 1 (by rfl) ⟨1378133, by rfl⟩ : syracuseStep 1837511 = 2756267) B2756267
theorem B1657435 : Blo 1224430 1657435 := bstep (se 1 (by rfl) ⟨1243076, by rfl⟩ : syracuseStep 1657435 = 2486153) B2486153
theorem B2484839 : Blo 1224430 2484839 := bstep (se 1 (by rfl) ⟨1863629, by rfl⟩ : syracuseStep 2484839 = 3727259) B3727259
theorem B31427189 : Blo 1224430 31427189 := bstep (se 5 (by rfl) ⟨1473149, by rfl⟩ : syracuseStep 31427189 = 2946299) B2946299
theorem B1837727 : Blo 1224430 1837727 := bstep (se 1 (by rfl) ⟨1378295, by rfl⟩ : syracuseStep 1837727 = 2756591) B2756591
theorem B1378975 : Blo 1224430 1378975 := bstep (se 1 (by rfl) ⟨1034231, by rfl⟩ : syracuseStep 1378975 = 2068463) B2068463
theorem B1837775 : Blo 1224430 1837775 := bstep (se 1 (by rfl) ⟨1378331, by rfl⟩ : syracuseStep 1837775 = 2756663) B2756663
theorem B1837871 : Blo 1224430 1837871 := bstep (se 1 (by rfl) ⟨1378403, by rfl⟩ : syracuseStep 1837871 = 2756807) B2756807
theorem B1837991 : Blo 1224430 1837991 := bstep (se 1 (by rfl) ⟨1378493, by rfl⟩ : syracuseStep 1837991 = 2756987) B2756987
theorem B5237729 : Blo 1224430 5237729 := bstep (se 2 (by rfl) ⟨1964148, by rfl⟩ : syracuseStep 5237729 = 3928297) B3928297
theorem B1838171 : Blo 1224430 1838171 := bstep (se 1 (by rfl) ⟨1378628, by rfl⟩ : syracuseStep 1838171 = 2757257) B2757257
theorem B1838249 : Blo 1224430 1838249 := bstep (se 2 (by rfl) ⟨689343, by rfl⟩ : syracuseStep 1838249 = 1378687) B1378687
theorem B6982955 : Blo 1224430 6982955 := bstep (se 1 (by rfl) ⟨5237216, by rfl⟩ : syracuseStep 6982955 = 10474433) B10474433
theorem B59649331 : Blo 1224430 59649331 := bstep (se 1 (by rfl) ⟨44736998, by rfl⟩ : syracuseStep 59649331 = 89473997) B89473997
theorem B2756051 : Blo 1224430 2756051 := bstep (se 1 (by rfl) ⟨2067038, by rfl⟩ : syracuseStep 2756051 = 4134077) B4134077
theorem B6204923 : Blo 1224430 6204923 := bstep (se 1 (by rfl) ⟨4653692, by rfl⟩ : syracuseStep 6204923 = 9307385) B9307385
theorem B2756123 : Blo 1224430 2756123 := bstep (se 1 (by rfl) ⟨2067092, by rfl⟩ : syracuseStep 2756123 = 4134185) B4134185
theorem B1838663 : Blo 1224430 1838663 := bstep (se 1 (by rfl) ⟨1378997, by rfl⟩ : syracuseStep 1838663 = 2757995) B2757995
theorem B2756321 : Blo 1224430 2756321 := bstep (se 2 (by rfl) ⟨1033620, by rfl⟩ : syracuseStep 2756321 = 2067241) B2067241
theorem B1838843 : Blo 1224430 1838843 := bstep (se 1 (by rfl) ⟨1379132, by rfl⟩ : syracuseStep 1838843 = 2758265) B2758265
theorem B1224479 : Blo 1224430 1224479 := bstep (se 1 (by rfl) ⟨918359, by rfl⟩ : syracuseStep 1224479 = 1836719) B1836719
theorem B12570461 : Blo 1224430 12570461 := bstep (se 3 (by rfl) ⟨2356961, by rfl⟩ : syracuseStep 12570461 = 4713923) B4713923
theorem B1224559 : Blo 1224430 1224559 := bstep (se 1 (by rfl) ⟨918419, by rfl⟩ : syracuseStep 1224559 = 1836839) B1836839
theorem B2756519 : Blo 1224430 2756519 := bstep (se 1 (by rfl) ⟨2067389, by rfl⟩ : syracuseStep 2756519 = 4134779) B4134779
theorem B1839083 : Blo 1224430 1839083 := bstep (se 1 (by rfl) ⟨1379312, by rfl⟩ : syracuseStep 1839083 = 2758625) B2758625
theorem B4649015 : Blo 1224430 4649015 := bstep (se 1 (by rfl) ⟨3486761, by rfl⟩ : syracuseStep 4649015 = 6973523) B6973523
theorem B2756681 : Blo 1224430 2756681 := bstep (se 2 (by rfl) ⟨1033755, by rfl⟩ : syracuseStep 2756681 = 2067511) B2067511
theorem B2756699 : Blo 1224430 2756699 := bstep (se 1 (by rfl) ⟨2067524, by rfl⟩ : syracuseStep 2756699 = 4135049) B4135049
theorem B1224927 : Blo 1224430 1224927 := bstep (se 1 (by rfl) ⟨918695, by rfl⟩ : syracuseStep 1224927 = 1837391) B1837391
theorem B1224959 : Blo 1224430 1224959 := bstep (se 1 (by rfl) ⟨918719, by rfl⟩ : syracuseStep 1224959 = 1837439) B1837439
theorem B1224987 : Blo 1224430 1224987 := bstep (se 1 (by rfl) ⟨918740, by rfl⟩ : syracuseStep 1224987 = 1837481) B1837481
theorem B4977065 : Blo 1224430 4977065 := bstep (se 2 (by rfl) ⟨1866399, by rfl⟩ : syracuseStep 4977065 = 3732799) B3732799
theorem B6205895 : Blo 1224430 6205895 := bstep (se 1 (by rfl) ⟨4654421, by rfl⟩ : syracuseStep 6205895 = 9308843) B9308843
theorem B25506251 : Blo 1224430 25506251 := bstep (se 1 (by rfl) ⟨19129688, by rfl⟩ : syracuseStep 25506251 = 38259377) B38259377
theorem B1225243 : Blo 1224430 1225243 := bstep (se 1 (by rfl) ⟨918932, by rfl⟩ : syracuseStep 1225243 = 1837865) B1837865
theorem B1225383 : Blo 1224430 1225383 := bstep (se 1 (by rfl) ⟨919037, by rfl⟩ : syracuseStep 1225383 = 1838075) B1838075
theorem B1225423 : Blo 1224430 1225423 := bstep (se 1 (by rfl) ⟨919067, by rfl⟩ : syracuseStep 1225423 = 1838135) B1838135
theorem B1225503 : Blo 1224430 1225503 := bstep (se 1 (by rfl) ⟨919127, by rfl⟩ : syracuseStep 1225503 = 1838255) B1838255
theorem B5231441 : Blo 1224430 5231441 := bstep (se 2 (by rfl) ⟨1961790, by rfl⟩ : syracuseStep 5231441 = 3923581) B3923581
theorem B60396517 : Blo 1224430 60396517 := bstep (se 4 (by rfl) ⟨5662173, by rfl⟩ : syracuseStep 60396517 = 11324347) B11324347
theorem B1225983 : Blo 1224430 1225983 := bstep (se 1 (by rfl) ⟨919487, by rfl⟩ : syracuseStep 1225983 = 1838975) B1838975
theorem B15906059 : Blo 1224430 15906059 := bstep (se 1 (by rfl) ⟨11929544, by rfl⟩ : syracuseStep 15906059 = 23859089) B23859089
theorem B1226111 : Blo 1224430 1226111 := bstep (se 1 (by rfl) ⟨919583, by rfl⟩ : syracuseStep 1226111 = 1839167) B1839167
theorem B1226267 : Blo 1224430 1226267 := bstep (se 1 (by rfl) ⟨919700, by rfl⟩ : syracuseStep 1226267 = 1839401) B1839401
theorem B3102239 : Blo 1224430 3102239 := bstep (se 1 (by rfl) ⟨2326679, by rfl⟩ : syracuseStep 3102239 = 4653359) B4653359
theorem B7853723 : Blo 1224430 7853723 := bstep (se 1 (by rfl) ⟨5890292, by rfl⟩ : syracuseStep 7853723 = 11780585) B11780585
theorem B10475183 : Blo 1224430 10475183 := bstep (se 1 (by rfl) ⟨7856387, by rfl⟩ : syracuseStep 10475183 = 15712775) B15712775
theorem B50304827 : Blo 1224430 50304827 := bstep (se 1 (by rfl) ⟨37728620, by rfl⟩ : syracuseStep 50304827 = 75457241) B75457241
theorem B1963867 : Blo 1224430 1963867 := bstep (se 1 (by rfl) ⟨1472900, by rfl⟩ : syracuseStep 1963867 = 2945801) B2945801
theorem B9303983 : Blo 1224430 9303983 := bstep (se 1 (by rfl) ⟨6977987, by rfl⟩ : syracuseStep 9303983 = 13955975) B13955975
theorem B9942983 : Blo 1224430 9942983 := bstep (se 1 (by rfl) ⟨7457237, by rfl⟩ : syracuseStep 9942983 = 14914475) B14914475
theorem B27228149 : Blo 1224430 27228149 := bstep (se 5 (by rfl) ⟨1276319, by rfl⟩ : syracuseStep 27228149 = 2552639) B2552639
theorem B3102857 : Blo 1224430 3102857 := bstep (se 2 (by rfl) ⟨1163571, by rfl⟩ : syracuseStep 3102857 = 2327143) B2327143
theorem B3102907 : Blo 1224430 3102907 := bstep (se 1 (by rfl) ⟨2327180, by rfl⟩ : syracuseStep 3102907 = 4654361) B4654361
theorem B1964251 : Blo 1224430 1964251 := bstep (se 1 (by rfl) ⟨1473188, by rfl⟩ : syracuseStep 1964251 = 2946377) B2946377
theorem B17660267 : Blo 1224430 17660267 := bstep (se 1 (by rfl) ⟨13245200, by rfl⟩ : syracuseStep 17660267 = 26490401) B26490401
theorem B14137847 : Blo 1224430 14137847 := bstep (se 1 (by rfl) ⟨10603385, by rfl⟩ : syracuseStep 14137847 = 21206771) B21206771
theorem B4414247 : Blo 1224430 4414247 := bstep (se 1 (by rfl) ⟨3310685, by rfl⟩ : syracuseStep 4414247 = 6621371) B6621371
theorem B21232475 : Blo 1224430 21232475 := bstep (se 1 (by rfl) ⟨15924356, by rfl⟩ : syracuseStep 21232475 = 31848713) B31848713
theorem B50969843 : Blo 1224430 50969843 := bstep (se 1 (by rfl) ⟨38227382, by rfl⟩ : syracuseStep 50969843 = 76454765) B76454765
theorem B3923273 : Blo 1224430 3923273 := bstep (se 2 (by rfl) ⟨1471227, by rfl⟩ : syracuseStep 3923273 = 2942455) B2942455
theorem B29793911 : Blo 1224430 29793911 := bstep (se 1 (by rfl) ⟨22345433, by rfl⟩ : syracuseStep 29793911 = 44690867) B44690867
theorem B5234311 : Blo 1224430 5234311 := bstep (se 1 (by rfl) ⟨3925733, by rfl⟩ : syracuseStep 5234311 = 7851467) B7851467
theorem B44752763 : Blo 1224430 44752763 := bstep (se 1 (by rfl) ⟨33564572, by rfl⟩ : syracuseStep 44752763 = 67129145) B67129145
theorem B1965961 : Blo 1224430 1965961 := bstep (se 2 (by rfl) ⟨737235, by rfl⟩ : syracuseStep 1965961 = 1474471) B1474471
theorem B7962515 : Blo 1224430 7962515 := bstep (se 1 (by rfl) ⟨5971886, by rfl⟩ : syracuseStep 7962515 = 11943773) B11943773
theorem B4137209 : Blo 1224430 4137209 := bstep (se 2 (by rfl) ⟨1551453, by rfl⟩ : syracuseStep 4137209 = 3102907) B3102907
theorem B4137263 : Blo 1224430 4137263 := bstep (se 1 (by rfl) ⟨3102947, by rfl⟩ : syracuseStep 4137263 = 6205895) B6205895
theorem B4415933 : Blo 1224430 4415933 := bstep (se 3 (by rfl) ⟨827987, by rfl⟩ : syracuseStep 4415933 = 1655975) B1655975
theorem B2327393 : Blo 1224430 2327393 := bstep (se 2 (by rfl) ⟨872772, by rfl⟩ : syracuseStep 2327393 = 1745545) B1745545
theorem B10462061 : Blo 1224430 10462061 := bstep (se 3 (by rfl) ⟨1961636, by rfl⟩ : syracuseStep 10462061 = 3923273) B3923273
theorem B7963687 : Blo 1224430 7963687 := bstep (se 1 (by rfl) ⟨5972765, by rfl⟩ : syracuseStep 7963687 = 11945531) B11945531
theorem B5235815 : Blo 1224430 5235815 := bstep (se 1 (by rfl) ⟨3926861, by rfl⟩ : syracuseStep 5235815 = 7853723) B7853723
theorem B13272173 : Blo 1224430 13272173 := bstep (se 3 (by rfl) ⟨2488532, by rfl⟩ : syracuseStep 13272173 = 4977065) B4977065
theorem B6202655 : Blo 1224430 6202655 := bstep (se 1 (by rfl) ⟨4651991, by rfl⟩ : syracuseStep 6202655 = 9303983) B9303983
theorem B6628655 : Blo 1224430 6628655 := bstep (se 1 (by rfl) ⟨4971491, by rfl⟩ : syracuseStep 6628655 = 9942983) B9942983
theorem B80528689 : Blo 1224430 80528689 := bstep (se 2 (by rfl) ⟨30198258, by rfl⟩ : syracuseStep 80528689 = 60396517) B60396517
theorem B1377607 : Blo 1224430 1377607 := bstep (se 1 (by rfl) ⟨1033205, by rfl⟩ : syracuseStep 1377607 = 2066411) B2066411
theorem B8832439 : Blo 1224430 8832439 := bstep (se 1 (by rfl) ⟨6624329, by rfl⟩ : syracuseStep 8832439 = 13248659) B13248659
theorem B11773511 : Blo 1224430 11773511 := bstep (se 1 (by rfl) ⟨8830133, by rfl⟩ : syracuseStep 11773511 = 17660267) B17660267
theorem B1656559 : Blo 1224430 1656559 := bstep (se 1 (by rfl) ⟨1242419, by rfl⟩ : syracuseStep 1656559 = 2484839) B2484839
theorem B2942831 : Blo 1224430 2942831 := bstep (se 1 (by rfl) ⟨2207123, by rfl⟩ : syracuseStep 2942831 = 4414247) B4414247
theorem B3491819 : Blo 1224430 3491819 := bstep (se 1 (by rfl) ⟨2618864, by rfl⟩ : syracuseStep 3491819 = 5237729) B5237729
theorem B4655303 : Blo 1224430 4655303 := bstep (se 1 (by rfl) ⟨3491477, by rfl⟩ : syracuseStep 4655303 = 6982955) B6982955
theorem B1837367 : Blo 1224430 1837367 := bstep (se 1 (by rfl) ⟨1378025, by rfl⟩ : syracuseStep 1837367 = 2756051) B2756051
theorem B1837415 : Blo 1224430 1837415 := bstep (se 1 (by rfl) ⟨1378061, by rfl⟩ : syracuseStep 1837415 = 2756123) B2756123
theorem B1837547 : Blo 1224430 1837547 := bstep (se 1 (by rfl) ⟨1378160, by rfl⟩ : syracuseStep 1837547 = 2756321) B2756321
theorem B1837679 : Blo 1224430 1837679 := bstep (se 1 (by rfl) ⟨1378259, by rfl⟩ : syracuseStep 1837679 = 2756519) B2756519
theorem B3099343 : Blo 1224430 3099343 := bstep (se 1 (by rfl) ⟨2324507, by rfl⟩ : syracuseStep 3099343 = 4649015) B4649015
theorem B1837787 : Blo 1224430 1837787 := bstep (se 1 (by rfl) ⟨1378340, by rfl⟩ : syracuseStep 1837787 = 2756681) B2756681
theorem B1837799 : Blo 1224430 1837799 := bstep (se 1 (by rfl) ⟨1378349, by rfl⟩ : syracuseStep 1837799 = 2756699) B2756699
theorem B9309329 : Blo 1224430 9309329 := bstep (se 2 (by rfl) ⟨3490998, by rfl⟩ : syracuseStep 9309329 = 6981997) B6981997
theorem B6204599 : Blo 1224430 6204599 := bstep (se 1 (by rfl) ⟨4653449, by rfl⟩ : syracuseStep 6204599 = 9306899) B9306899
theorem B10604039 : Blo 1224430 10604039 := bstep (se 1 (by rfl) ⟨7953029, by rfl⟩ : syracuseStep 10604039 = 15906059) B15906059
theorem B1838633 : Blo 1224430 1838633 := bstep (se 2 (by rfl) ⟨689487, by rfl⟩ : syracuseStep 1838633 = 1378975) B1378975
theorem B2068159 : Blo 1224430 2068159 := bstep (se 1 (by rfl) ⟨1551119, by rfl⟩ : syracuseStep 2068159 = 3102239) B3102239
theorem B6983455 : Blo 1224430 6983455 := bstep (se 1 (by rfl) ⟨5237591, by rfl⟩ : syracuseStep 6983455 = 10475183) B10475183
theorem B6205247 : Blo 1224430 6205247 := bstep (se 1 (by rfl) ⟨4653935, by rfl⟩ : syracuseStep 6205247 = 9307871) B9307871
theorem B1224607 : Blo 1224430 1224607 := bstep (se 1 (by rfl) ⟨918455, by rfl⟩ : syracuseStep 1224607 = 1836911) B1836911
theorem B1224731 : Blo 1224430 1224731 := bstep (se 1 (by rfl) ⟨918548, by rfl⟩ : syracuseStep 1224731 = 1837097) B1837097
theorem B4419623 : Blo 1224430 4419623 := bstep (se 1 (by rfl) ⟨3314717, by rfl⟩ : syracuseStep 4419623 = 6629435) B6629435
theorem B1224751 : Blo 1224430 1224751 := bstep (se 1 (by rfl) ⟨918563, by rfl⟩ : syracuseStep 1224751 = 1837127) B1837127
theorem B1962047 : Blo 1224430 1962047 := bstep (se 1 (by rfl) ⟨1471535, by rfl⟩ : syracuseStep 1962047 = 2943071) B2943071
theorem B2068571 : Blo 1224430 2068571 := bstep (se 1 (by rfl) ⟨1551428, by rfl⟩ : syracuseStep 2068571 = 3102857) B3102857
theorem B2617447 : Blo 1224430 2617447 := bstep (se 1 (by rfl) ⟨1963085, by rfl⟩ : syracuseStep 2617447 = 3926171) B3926171
theorem B1224871 : Blo 1224430 1224871 := bstep (se 1 (by rfl) ⟨918653, by rfl⟩ : syracuseStep 1224871 = 1837307) B1837307
theorem B1225007 : Blo 1224430 1225007 := bstep (se 1 (by rfl) ⟨918755, by rfl⟩ : syracuseStep 1225007 = 1837511) B1837511
theorem B79450429 : Blo 1224430 79450429 := bstep (se 3 (by rfl) ⟨14896955, by rfl⟩ : syracuseStep 79450429 = 29793911) B29793911
theorem B9425231 : Blo 1224430 9425231 := bstep (se 1 (by rfl) ⟨7068923, by rfl⟩ : syracuseStep 9425231 = 14137847) B14137847
theorem B79532441 : Blo 1224430 79532441 := bstep (se 2 (by rfl) ⟨29824665, by rfl⟩ : syracuseStep 79532441 = 59649331) B59649331
theorem B20951459 : Blo 1224430 20951459 := bstep (se 1 (by rfl) ⟨15713594, by rfl⟩ : syracuseStep 20951459 = 31427189) B31427189
theorem B1225151 : Blo 1224430 1225151 := bstep (se 1 (by rfl) ⟨918863, by rfl⟩ : syracuseStep 1225151 = 1837727) B1837727
theorem B1225183 : Blo 1224430 1225183 := bstep (se 1 (by rfl) ⟨918887, by rfl⟩ : syracuseStep 1225183 = 1837775) B1837775
theorem B1225247 : Blo 1224430 1225247 := bstep (se 1 (by rfl) ⟨918935, by rfl⟩ : syracuseStep 1225247 = 1837871) B1837871
theorem B1225327 : Blo 1224430 1225327 := bstep (se 1 (by rfl) ⟨918995, by rfl⟩ : syracuseStep 1225327 = 1837991) B1837991
theorem B1225447 : Blo 1224430 1225447 := bstep (se 1 (by rfl) ⟨919085, by rfl⟩ : syracuseStep 1225447 = 1838171) B1838171
theorem B1225499 : Blo 1224430 1225499 := bstep (se 1 (by rfl) ⟨919124, by rfl⟩ : syracuseStep 1225499 = 1838249) B1838249
theorem B1225775 : Blo 1224430 1225775 := bstep (se 1 (by rfl) ⟨919331, by rfl⟩ : syracuseStep 1225775 = 1838663) B1838663
theorem B2618489 : Blo 1224430 2618489 := bstep (se 2 (by rfl) ⟨981933, by rfl⟩ : syracuseStep 2618489 = 1963867) B1963867
theorem B1225895 : Blo 1224430 1225895 := bstep (se 1 (by rfl) ⟨919421, by rfl⟩ : syracuseStep 1225895 = 1838843) B1838843
theorem B1226055 : Blo 1224430 1226055 := bstep (se 1 (by rfl) ⟨919541, by rfl⟩ : syracuseStep 1226055 = 1839083) B1839083
theorem B6460843 : Blo 1224430 6460843 := bstep (se 1 (by rfl) ⟨4845632, by rfl⟩ : syracuseStep 6460843 = 9691265) B9691265
theorem B6198767 : Blo 1224430 6198767 := bstep (se 1 (by rfl) ⟨4649075, by rfl⟩ : syracuseStep 6198767 = 9298151) B9298151
theorem B7452157 : Blo 1224430 7452157 := bstep (se 3 (by rfl) ⟨1397279, by rfl⟩ : syracuseStep 7452157 = 2794559) B2794559
theorem B2619001 : Blo 1224430 2619001 := bstep (se 2 (by rfl) ⟨982125, by rfl⟩ : syracuseStep 2619001 = 1964251) B1964251
theorem B17004167 : Blo 1224430 17004167 := bstep (se 1 (by rfl) ⟨12753125, by rfl⟩ : syracuseStep 17004167 = 25506251) B25506251
theorem B3487627 : Blo 1224430 3487627 := bstep (se 1 (by rfl) ⟨2615720, by rfl⟩ : syracuseStep 3487627 = 5231441) B5231441
theorem B2209913 : Blo 1224430 2209913 := bstep (se 2 (by rfl) ⟨828717, by rfl⟩ : syracuseStep 2209913 = 1657435) B1657435
theorem B33536551 : Blo 1224430 33536551 := bstep (se 1 (by rfl) ⟨25152413, by rfl⟩ : syracuseStep 33536551 = 50304827) B50304827
theorem B26499743 : Blo 1224430 26499743 := bstep (se 1 (by rfl) ⟨19874807, by rfl⟩ : syracuseStep 26499743 = 39749615) B39749615
theorem B2759327 : Blo 1224430 2759327 := bstep (se 1 (by rfl) ⟨2069495, by rfl⟩ : syracuseStep 2759327 = 4138991) B4138991
theorem B18152099 : Blo 1224430 18152099 := bstep (se 1 (by rfl) ⟨13614074, by rfl⟩ : syracuseStep 18152099 = 27228149) B27228149
theorem B19880909 : Blo 1224430 19880909 := bstep (se 3 (by rfl) ⟨3727670, by rfl⟩ : syracuseStep 19880909 = 7455341) B7455341
theorem B14154983 : Blo 1224430 14154983 := bstep (se 1 (by rfl) ⟨10616237, by rfl⟩ : syracuseStep 14154983 = 21232475) B21232475
theorem B33979895 : Blo 1224430 33979895 := bstep (se 1 (by rfl) ⟨25484921, by rfl⟩ : syracuseStep 33979895 = 50969843) B50969843
theorem B6979081 : Blo 1224430 6979081 := bstep (se 2 (by rfl) ⟨2617155, by rfl⟩ : syracuseStep 6979081 = 5234311) B5234311
theorem B4136615 : Blo 1224430 4136615 := bstep (se 1 (by rfl) ⟨3102461, by rfl⟩ : syracuseStep 4136615 = 6204923) B6204923
theorem B2621281 : Blo 1224430 2621281 := bstep (se 2 (by rfl) ⟨982980, by rfl⟩ : syracuseStep 2621281 = 1965961) B1965961
theorem B8380307 : Blo 1224430 8380307 := bstep (se 1 (by rfl) ⟨6285230, by rfl⟩ : syracuseStep 8380307 = 12570461) B12570461
theorem B29835175 : Blo 1224430 29835175 := bstep (se 1 (by rfl) ⟨22376381, by rfl⟩ : syracuseStep 29835175 = 44752763) B44752763
theorem B5308343 : Blo 1224430 5308343 := bstep (se 1 (by rfl) ⟨3981257, by rfl⟩ : syracuseStep 5308343 = 7962515) B7962515
theorem B3489929 : Blo 1224430 3489929 := bstep (se 2 (by rfl) ⟨1308723, by rfl⟩ : syracuseStep 3489929 = 2617447) B2617447
theorem B6283487 : Blo 1224430 6283487 := bstep (se 1 (by rfl) ⟨4712615, by rfl⟩ : syracuseStep 6283487 = 9425231) B9425231
theorem B13967639 : Blo 1224430 13967639 := bstep (se 1 (by rfl) ⟨10475729, by rfl⟩ : syracuseStep 13967639 = 20951459) B20951459
theorem B3490543 : Blo 1224430 3490543 := bstep (se 1 (by rfl) ⟨2617907, by rfl⟩ : syracuseStep 3490543 = 5235815) B5235815
theorem B8848115 : Blo 1224430 8848115 := bstep (se 1 (by rfl) ⟨6636086, by rfl⟩ : syracuseStep 8848115 = 13272173) B13272173
theorem B1745659 : Blo 1224430 1745659 := bstep (se 1 (by rfl) ⟨1309244, by rfl⟩ : syracuseStep 1745659 = 2618489) B2618489
theorem B7849007 : Blo 1224430 7849007 := bstep (se 1 (by rfl) ⟨5886755, by rfl⟩ : syracuseStep 7849007 = 11773511) B11773511
theorem B2327879 : Blo 1224430 2327879 := bstep (se 1 (by rfl) ⟨1745909, by rfl⟩ : syracuseStep 2327879 = 3491819) B3491819
theorem B1836809 : Blo 1224430 1836809 := bstep (se 2 (by rfl) ⟨688803, by rfl⟩ : syracuseStep 1836809 = 1377607) B1377607
theorem B12101399 : Blo 1224430 12101399 := bstep (se 1 (by rfl) ⟨9076049, by rfl⟩ : syracuseStep 12101399 = 18152099) B18152099
theorem B3492001 : Blo 1224430 3492001 := bstep (se 2 (by rfl) ⟨1309500, by rfl⟩ : syracuseStep 3492001 = 2619001) B2619001
theorem B22653263 : Blo 1224430 22653263 := bstep (se 1 (by rfl) ⟨16989947, by rfl⟩ : syracuseStep 22653263 = 33979895) B33979895
theorem B1379047 : Blo 1224430 1379047 := bstep (se 1 (by rfl) ⟨1034285, by rfl⟩ : syracuseStep 1379047 = 2068571) B2068571
theorem B53021627 : Blo 1224430 53021627 := bstep (se 1 (by rfl) ⟨39766220, by rfl⟩ : syracuseStep 53021627 = 79532441) B79532441
theorem B2943955 : Blo 1224430 2943955 := bstep (se 1 (by rfl) ⟨2207966, by rfl⟩ : syracuseStep 2943955 = 4415933) B4415933
theorem B105933905 : Blo 1224430 105933905 := bstep (se 2 (by rfl) ⟨39725214, by rfl⟩ : syracuseStep 105933905 = 79450429) B79450429
theorem B6974707 : Blo 1224430 6974707 := bstep (se 1 (by rfl) ⟨5231030, by rfl⟩ : syracuseStep 6974707 = 10462061) B10462061
theorem B44715401 : Blo 1224430 44715401 := bstep (se 2 (by rfl) ⟨16768275, by rfl⟩ : syracuseStep 44715401 = 33536551) B33536551
theorem B4132457 : Blo 1224430 4132457 := bstep (se 2 (by rfl) ⟨1549671, by rfl⟩ : syracuseStep 4132457 = 3099343) B3099343
theorem B4132511 : Blo 1224430 4132511 := bstep (se 1 (by rfl) ⟨3099383, by rfl⟩ : syracuseStep 4132511 = 6198767) B6198767
theorem B1224911 : Blo 1224430 1224911 := bstep (se 1 (by rfl) ⟨918683, by rfl⟩ : syracuseStep 1224911 = 1837367) B1837367
theorem B1224943 : Blo 1224430 1224943 := bstep (se 1 (by rfl) ⟨918707, by rfl⟩ : syracuseStep 1224943 = 1837415) B1837415
theorem B1225031 : Blo 1224430 1225031 := bstep (se 1 (by rfl) ⟨918773, by rfl⟩ : syracuseStep 1225031 = 1837547) B1837547
theorem B1225119 : Blo 1224430 1225119 := bstep (se 1 (by rfl) ⟨918839, by rfl⟩ : syracuseStep 1225119 = 1837679) B1837679
theorem B17666495 : Blo 1224430 17666495 := bstep (se 1 (by rfl) ⟨13249871, by rfl⟩ : syracuseStep 17666495 = 26499743) B26499743
theorem B1839551 : Blo 1224430 1839551 := bstep (se 1 (by rfl) ⟨1379663, by rfl⟩ : syracuseStep 1839551 = 2759327) B2759327
theorem B1225191 : Blo 1224430 1225191 := bstep (se 1 (by rfl) ⟨918893, by rfl⟩ : syracuseStep 1225191 = 1837787) B1837787
theorem B1225199 : Blo 1224430 1225199 := bstep (se 1 (by rfl) ⟨918899, by rfl⟩ : syracuseStep 1225199 = 1837799) B1837799
theorem B8614457 : Blo 1224430 8614457 := bstep (se 2 (by rfl) ⟨3230421, by rfl⟩ : syracuseStep 8614457 = 6460843) B6460843
theorem B11776585 : Blo 1224430 11776585 := bstep (se 2 (by rfl) ⟨4416219, by rfl⟩ : syracuseStep 11776585 = 8832439) B8832439
theorem B6206219 : Blo 1224430 6206219 := bstep (se 1 (by rfl) ⟨4654664, by rfl⟩ : syracuseStep 6206219 = 9309329) B9309329
theorem B2757545 : Blo 1224430 2757545 := bstep (se 2 (by rfl) ⟨1034079, by rfl⟩ : syracuseStep 2757545 = 2068159) B2068159
theorem B6206381 : Blo 1224430 6206381 := bstep (se 3 (by rfl) ⟨1163696, by rfl⟩ : syracuseStep 6206381 = 2327393) B2327393
theorem B2208745 : Blo 1224430 2208745 := bstep (se 2 (by rfl) ⟨828279, by rfl⟩ : syracuseStep 2208745 = 1656559) B1656559
theorem B1225755 : Blo 1224430 1225755 := bstep (se 1 (by rfl) ⟨919316, by rfl⟩ : syracuseStep 1225755 = 1838633) B1838633
theorem B9311273 : Blo 1224430 9311273 := bstep (se 2 (by rfl) ⟨3491727, by rfl⟩ : syracuseStep 9311273 = 6983455) B6983455
theorem B2757743 : Blo 1224430 2757743 := bstep (se 1 (by rfl) ⟨2068307, by rfl⟩ : syracuseStep 2757743 = 4136615) B4136615
theorem B3495041 : Blo 1224430 3495041 := bstep (se 2 (by rfl) ⟨1310640, by rfl⟩ : syracuseStep 3495041 = 2621281) B2621281
theorem B4650169 : Blo 1224430 4650169 := bstep (se 2 (by rfl) ⟨1743813, by rfl⟩ : syracuseStep 4650169 = 3487627) B3487627
theorem B1308031 : Blo 1224430 1308031 := bstep (se 1 (by rfl) ⟨981023, by rfl⟩ : syracuseStep 1308031 = 1962047) B1962047
theorem B11785661 : Blo 1224430 11785661 := bstep (se 3 (by rfl) ⟨2209811, by rfl⟩ : syracuseStep 11785661 = 4419623) B4419623
theorem B2758139 : Blo 1224430 2758139 := bstep (se 1 (by rfl) ⟨2068604, by rfl⟩ : syracuseStep 2758139 = 4137209) B4137209
theorem B2758175 : Blo 1224430 2758175 := bstep (se 1 (by rfl) ⟨2068631, by rfl⟩ : syracuseStep 2758175 = 4137263) B4137263
theorem B42472997 : Blo 1224430 42472997 := bstep (se 4 (by rfl) ⟨3981843, by rfl⟩ : syracuseStep 42472997 = 7963687) B7963687
theorem B17676413 : Blo 1224430 17676413 := bstep (se 3 (by rfl) ⟨3314327, by rfl⟩ : syracuseStep 17676413 = 6628655) B6628655
theorem B4135103 : Blo 1224430 4135103 := bstep (se 1 (by rfl) ⟨3101327, by rfl⟩ : syracuseStep 4135103 = 6202655) B6202655
theorem B11336111 : Blo 1224430 11336111 := bstep (se 1 (by rfl) ⟨8502083, by rfl⟩ : syracuseStep 11336111 = 17004167) B17004167
theorem B28277437 : Blo 1224430 28277437 := bstep (se 3 (by rfl) ⟨5302019, by rfl⟩ : syracuseStep 28277437 = 10604039) B10604039
theorem B1473275 : Blo 1224430 1473275 := bstep (se 1 (by rfl) ⟨1104956, by rfl⟩ : syracuseStep 1473275 = 2209913) B2209913
theorem B3103535 : Blo 1224430 3103535 := bstep (se 1 (by rfl) ⟨2327651, by rfl⟩ : syracuseStep 3103535 = 4655303) B4655303
theorem B107371585 : Blo 1224430 107371585 := bstep (se 2 (by rfl) ⟨40264344, by rfl⟩ : syracuseStep 107371585 = 80528689) B80528689
theorem B13253939 : Blo 1224430 13253939 := bstep (se 1 (by rfl) ⟨9940454, by rfl⟩ : syracuseStep 13253939 = 19880909) B19880909
theorem B9936209 : Blo 1224430 9936209 := bstep (se 2 (by rfl) ⟨3726078, by rfl⟩ : syracuseStep 9936209 = 7452157) B7452157
theorem B9305441 : Blo 1224430 9305441 := bstep (se 2 (by rfl) ⟨3489540, by rfl⟩ : syracuseStep 9305441 = 6979081) B6979081
theorem B4136399 : Blo 1224430 4136399 := bstep (se 1 (by rfl) ⟨3102299, by rfl⟩ : syracuseStep 4136399 = 6204599) B6204599
theorem B9436655 : Blo 1224430 9436655 := bstep (se 1 (by rfl) ⟨7077491, by rfl⟩ : syracuseStep 9436655 = 14154983) B14154983
theorem B7847549 : Blo 1224430 7847549 := bstep (se 3 (by rfl) ⟨1471415, by rfl⟩ : syracuseStep 7847549 = 2942831) B2942831
theorem B22347485 : Blo 1224430 22347485 := bstep (se 3 (by rfl) ⟨4190153, by rfl⟩ : syracuseStep 22347485 = 8380307) B8380307
theorem B4136831 : Blo 1224430 4136831 := bstep (se 1 (by rfl) ⟨3102623, by rfl⟩ : syracuseStep 4136831 = 6205247) B6205247
theorem B39780233 : Blo 1224430 39780233 := bstep (se 2 (by rfl) ⟨14917587, by rfl⟩ : syracuseStep 39780233 = 29835175) B29835175
theorem B3538895 : Blo 1224430 3538895 := bstep (se 1 (by rfl) ⟨2654171, by rfl⟩ : syracuseStep 3538895 = 5308343) B5308343
theorem B2326619 : Blo 1224430 2326619 := bstep (se 1 (by rfl) ⟨1744964, by rfl⟩ : syracuseStep 2326619 = 3489929) B3489929
theorem B5742971 : Blo 1224430 5742971 := bstep (se 1 (by rfl) ⟨4307228, by rfl⟩ : syracuseStep 5742971 = 8614457) B8614457
theorem B5898743 : Blo 1224430 5898743 := bstep (se 1 (by rfl) ⟨4424057, by rfl⟩ : syracuseStep 5898743 = 8848115) B8848115
theorem B4137479 : Blo 1224430 4137479 := bstep (se 1 (by rfl) ⟨3103109, by rfl⟩ : syracuseStep 4137479 = 6206219) B6206219
theorem B4137587 : Blo 1224430 4137587 := bstep (se 1 (by rfl) ⟨3103190, by rfl⟩ : syracuseStep 4137587 = 6206381) B6206381
theorem B7857107 : Blo 1224430 7857107 := bstep (se 1 (by rfl) ⟨5892830, by rfl⟩ : syracuseStep 7857107 = 11785661) B11785661
theorem B4654057 : Blo 1224430 4654057 := bstep (se 2 (by rfl) ⟨1745271, by rfl⟩ : syracuseStep 4654057 = 3490543) B3490543
theorem B2327545 : Blo 1224430 2327545 := bstep (se 2 (by rfl) ⟨872829, by rfl⟩ : syracuseStep 2327545 = 1745659) B1745659
theorem B3925273 : Blo 1224430 3925273 := bstep (se 2 (by rfl) ⟨1471977, by rfl⟩ : syracuseStep 3925273 = 2943955) B2943955
theorem B9299609 : Blo 1224430 9299609 := bstep (se 2 (by rfl) ⟨3487353, by rfl⟩ : syracuseStep 9299609 = 6974707) B6974707
theorem B6203627 : Blo 1224430 6203627 := bstep (se 1 (by rfl) ⟨4652720, by rfl⟩ : syracuseStep 6203627 = 9305441) B9305441
theorem B2754971 : Blo 1224430 2754971 := bstep (se 1 (by rfl) ⟨2066228, by rfl⟩ : syracuseStep 2754971 = 4132457) B4132457
theorem B2755007 : Blo 1224430 2755007 := bstep (se 1 (by rfl) ⟨2066255, by rfl⟩ : syracuseStep 2755007 = 4132511) B4132511
theorem B26520155 : Blo 1224430 26520155 := bstep (se 1 (by rfl) ⟨19890116, by rfl⟩ : syracuseStep 26520155 = 39780233) B39780233
theorem B4188991 : Blo 1224430 4188991 := bstep (se 1 (by rfl) ⟨3141743, by rfl⟩ : syracuseStep 4188991 = 6283487) B6283487
theorem B4656001 : Blo 1224430 4656001 := bstep (se 2 (by rfl) ⟨1746000, by rfl⟩ : syracuseStep 4656001 = 3492001) B3492001
theorem B1838363 : Blo 1224430 1838363 := bstep (se 1 (by rfl) ⟨1378772, by rfl⟩ : syracuseStep 1838363 = 2757545) B2757545
theorem B1838495 : Blo 1224430 1838495 := bstep (se 1 (by rfl) ⟨1378871, by rfl⟩ : syracuseStep 1838495 = 2757743) B2757743
theorem B2330027 : Blo 1224430 2330027 := bstep (se 1 (by rfl) ⟨1747520, by rfl⟩ : syracuseStep 2330027 = 3495041) B3495041
theorem B37703249 : Blo 1224430 37703249 := bstep (se 2 (by rfl) ⟨14138718, by rfl⟩ : syracuseStep 37703249 = 28277437) B28277437
theorem B1838729 : Blo 1224430 1838729 := bstep (se 2 (by rfl) ⟨689523, by rfl⟩ : syracuseStep 1838729 = 1379047) B1379047
theorem B1838759 : Blo 1224430 1838759 := bstep (se 1 (by rfl) ⟨1379069, by rfl⟩ : syracuseStep 1838759 = 2758139) B2758139
theorem B1838783 : Blo 1224430 1838783 := bstep (se 1 (by rfl) ⟨1379087, by rfl⟩ : syracuseStep 1838783 = 2758175) B2758175
theorem B28315331 : Blo 1224430 28315331 := bstep (se 1 (by rfl) ⟨21236498, by rfl⟩ : syracuseStep 28315331 = 42472997) B42472997
theorem B1224539 : Blo 1224430 1224539 := bstep (se 1 (by rfl) ⟨918404, by rfl⟩ : syracuseStep 1224539 = 1836809) B1836809
theorem B2944993 : Blo 1224430 2944993 := bstep (se 2 (by rfl) ⟨1104372, by rfl⟩ : syracuseStep 2944993 = 2208745) B2208745
theorem B11784275 : Blo 1224430 11784275 := bstep (se 1 (by rfl) ⟨8838206, by rfl⟩ : syracuseStep 11784275 = 17676413) B17676413
theorem B2756735 : Blo 1224430 2756735 := bstep (se 1 (by rfl) ⟨2067551, by rfl⟩ : syracuseStep 2756735 = 4135103) B4135103
theorem B15102175 : Blo 1224430 15102175 := bstep (se 1 (by rfl) ⟨11326631, by rfl⟩ : syracuseStep 15102175 = 22653263) B22653263
theorem B7557407 : Blo 1224430 7557407 := bstep (se 1 (by rfl) ⟨5668055, by rfl⟩ : syracuseStep 7557407 = 11336111) B11336111
theorem B2069023 : Blo 1224430 2069023 := bstep (se 1 (by rfl) ⟨1551767, by rfl⟩ : syracuseStep 2069023 = 3103535) B3103535
theorem B3928733 : Blo 1224430 3928733 := bstep (se 3 (by rfl) ⟨736637, by rfl⟩ : syracuseStep 3928733 = 1473275) B1473275
theorem B6976165 : Blo 1224430 6976165 := bstep (se 4 (by rfl) ⟨654015, by rfl⟩ : syracuseStep 6976165 = 1308031) B1308031
theorem B8835959 : Blo 1224430 8835959 := bstep (se 1 (by rfl) ⟨6626969, by rfl⟩ : syracuseStep 8835959 = 13253939) B13253939
theorem B6624139 : Blo 1224430 6624139 := bstep (se 1 (by rfl) ⟨4968104, by rfl⟩ : syracuseStep 6624139 = 9936209) B9936209
theorem B2757599 : Blo 1224430 2757599 := bstep (se 1 (by rfl) ⟨2068199, by rfl⟩ : syracuseStep 2757599 = 4136399) B4136399
theorem B5231699 : Blo 1224430 5231699 := bstep (se 1 (by rfl) ⟨3923774, by rfl⟩ : syracuseStep 5231699 = 7847549) B7847549
theorem B14898323 : Blo 1224430 14898323 := bstep (se 1 (by rfl) ⟨11173742, by rfl⟩ : syracuseStep 14898323 = 22347485) B22347485
theorem B2757887 : Blo 1224430 2757887 := bstep (se 1 (by rfl) ⟨2068415, by rfl⟩ : syracuseStep 2757887 = 4136831) B4136831
theorem B9311759 : Blo 1224430 9311759 := bstep (se 1 (by rfl) ⟨6983819, by rfl⟩ : syracuseStep 9311759 = 13967639) B13967639
theorem B11777663 : Blo 1224430 11777663 := bstep (se 1 (by rfl) ⟨8833247, by rfl⟩ : syracuseStep 11777663 = 17666495) B17666495
theorem B1226367 : Blo 1224430 1226367 := bstep (se 1 (by rfl) ⟨919775, by rfl⟩ : syracuseStep 1226367 = 1839551) B1839551
theorem B6207515 : Blo 1224430 6207515 := bstep (se 1 (by rfl) ⟨4655636, by rfl⟩ : syracuseStep 6207515 = 9311273) B9311273
theorem B5232671 : Blo 1224430 5232671 := bstep (se 1 (by rfl) ⟨3924503, by rfl⟩ : syracuseStep 5232671 = 7849007) B7849007
theorem B15702113 : Blo 1224430 15702113 := bstep (se 2 (by rfl) ⟨5888292, by rfl⟩ : syracuseStep 15702113 = 11776585) B11776585
theorem B6207677 : Blo 1224430 6207677 := bstep (se 3 (by rfl) ⟨1163939, by rfl⟩ : syracuseStep 6207677 = 2327879) B2327879
theorem B8067599 : Blo 1224430 8067599 := bstep (se 1 (by rfl) ⟨6050699, by rfl⟩ : syracuseStep 8067599 = 12101399) B12101399
theorem B143162113 : Blo 1224430 143162113 := bstep (se 2 (by rfl) ⟨53685792, by rfl⟩ : syracuseStep 143162113 = 107371585) B107371585
theorem B6200225 : Blo 1224430 6200225 := bstep (se 2 (by rfl) ⟨2325084, by rfl⟩ : syracuseStep 6200225 = 4650169) B4650169
theorem B35347751 : Blo 1224430 35347751 := bstep (se 1 (by rfl) ⟨26510813, by rfl⟩ : syracuseStep 35347751 = 53021627) B53021627
theorem B70622603 : Blo 1224430 70622603 := bstep (se 1 (by rfl) ⟨52966952, by rfl⟩ : syracuseStep 70622603 = 105933905) B105933905
theorem B37748213 : Blo 1224430 37748213 := bstep (se 5 (by rfl) ⟨1769447, by rfl⟩ : syracuseStep 37748213 = 3538895) B3538895
theorem B29810267 : Blo 1224430 29810267 := bstep (se 1 (by rfl) ⟨22357700, by rfl⟩ : syracuseStep 29810267 = 44715401) B44715401
theorem B6291103 : Blo 1224430 6291103 := bstep (se 1 (by rfl) ⟨4718327, by rfl⟩ : syracuseStep 6291103 = 9436655) B9436655
theorem B7856183 : Blo 1224430 7856183 := bstep (se 1 (by rfl) ⟨5892137, by rfl⟩ : syracuseStep 7856183 = 11784275) B11784275
theorem B5038271 : Blo 1224430 5038271 := bstep (se 1 (by rfl) ⟨3778703, by rfl⟩ : syracuseStep 5038271 = 7557407) B7557407
theorem B20136233 : Blo 1224430 20136233 := bstep (se 2 (by rfl) ⟨7551087, by rfl⟩ : syracuseStep 20136233 = 15102175) B15102175
theorem B3932495 : Blo 1224430 3932495 := bstep (se 1 (by rfl) ⟨2949371, by rfl⟩ : syracuseStep 3932495 = 5898743) B5898743
theorem B5890639 : Blo 1224430 5890639 := bstep (se 1 (by rfl) ⟨4417979, by rfl⟩ : syracuseStep 5890639 = 8835959) B8835959
theorem B190882817 : Blo 1224430 190882817 := bstep (se 2 (by rfl) ⟨71581056, by rfl⟩ : syracuseStep 190882817 = 143162113) B143162113
theorem B8832185 : Blo 1224430 8832185 := bstep (se 2 (by rfl) ⟨3312069, by rfl⟩ : syracuseStep 8832185 = 6624139) B6624139
theorem B4138343 : Blo 1224430 4138343 := bstep (se 1 (by rfl) ⟨3103757, by rfl⟩ : syracuseStep 4138343 = 6207515) B6207515
theorem B4138451 : Blo 1224430 4138451 := bstep (se 1 (by rfl) ⟨3103838, by rfl⟩ : syracuseStep 4138451 = 6207677) B6207677
theorem B1836647 : Blo 1224430 1836647 := bstep (se 1 (by rfl) ⟨1377485, by rfl⟩ : syracuseStep 1836647 = 2754971) B2754971
theorem B1836671 : Blo 1224430 1836671 := bstep (se 1 (by rfl) ⟨1377503, by rfl⟩ : syracuseStep 1836671 = 2755007) B2755007
theorem B17680103 : Blo 1224430 17680103 := bstep (se 1 (by rfl) ⟨13260077, by rfl⟩ : syracuseStep 17680103 = 26520155) B26520155
theorem B47081735 : Blo 1224430 47081735 := bstep (se 1 (by rfl) ⟨35311301, by rfl⟩ : syracuseStep 47081735 = 70622603) B70622603
theorem B25135499 : Blo 1224430 25135499 := bstep (se 1 (by rfl) ⟨18851624, by rfl⟩ : syracuseStep 25135499 = 37703249) B37703249
theorem B18876887 : Blo 1224430 18876887 := bstep (se 1 (by rfl) ⟨14157665, by rfl⟩ : syracuseStep 18876887 = 28315331) B28315331
theorem B3926657 : Blo 1224430 3926657 := bstep (se 2 (by rfl) ⟨1472496, by rfl⟩ : syracuseStep 3926657 = 2944993) B2944993
theorem B1551079 : Blo 1224430 1551079 := bstep (se 1 (by rfl) ⟨1163309, by rfl⟩ : syracuseStep 1551079 = 2326619) B2326619
theorem B1837823 : Blo 1224430 1837823 := bstep (se 1 (by rfl) ⟨1378367, by rfl⟩ : syracuseStep 1837823 = 2756735) B2756735
theorem B3828647 : Blo 1224430 3828647 := bstep (se 1 (by rfl) ⟨2871485, by rfl⟩ : syracuseStep 3828647 = 5742971) B5742971
theorem B5238071 : Blo 1224430 5238071 := bstep (se 1 (by rfl) ⟨3928553, by rfl⟩ : syracuseStep 5238071 = 7857107) B7857107
theorem B1838399 : Blo 1224430 1838399 := bstep (se 1 (by rfl) ⟨1378799, by rfl⟩ : syracuseStep 1838399 = 2757599) B2757599
theorem B9932215 : Blo 1224430 9932215 := bstep (se 1 (by rfl) ⟨7449161, by rfl⟩ : syracuseStep 9932215 = 14898323) B14898323
theorem B1838591 : Blo 1224430 1838591 := bstep (se 1 (by rfl) ⟨1378943, by rfl⟩ : syracuseStep 1838591 = 2757887) B2757887
theorem B9301553 : Blo 1224430 9301553 := bstep (se 2 (by rfl) ⟨3488082, by rfl⟩ : syracuseStep 9301553 = 6976165) B6976165
theorem B7851775 : Blo 1224430 7851775 := bstep (se 1 (by rfl) ⟨5888831, by rfl⟩ : syracuseStep 7851775 = 11777663) B11777663
theorem B6205409 : Blo 1224430 6205409 := bstep (se 2 (by rfl) ⟨2327028, by rfl⟩ : syracuseStep 6205409 = 4654057) B4654057
theorem B5378399 : Blo 1224430 5378399 := bstep (se 1 (by rfl) ⟨4033799, by rfl⟩ : syracuseStep 5378399 = 8067599) B8067599
theorem B4133483 : Blo 1224430 4133483 := bstep (se 1 (by rfl) ⟨3100112, by rfl⟩ : syracuseStep 4133483 = 6200225) B6200225
theorem B1225575 : Blo 1224430 1225575 := bstep (se 1 (by rfl) ⟨919181, by rfl⟩ : syracuseStep 1225575 = 1838363) B1838363
theorem B23565167 : Blo 1224430 23565167 := bstep (se 1 (by rfl) ⟨17673875, by rfl⟩ : syracuseStep 23565167 = 35347751) B35347751
theorem B1225663 : Blo 1224430 1225663 := bstep (se 1 (by rfl) ⟨919247, by rfl⟩ : syracuseStep 1225663 = 1838495) B1838495
theorem B1553351 : Blo 1224430 1553351 := bstep (se 1 (by rfl) ⟨1165013, by rfl⟩ : syracuseStep 1553351 = 2330027) B2330027
theorem B1225819 : Blo 1224430 1225819 := bstep (se 1 (by rfl) ⟨919364, by rfl⟩ : syracuseStep 1225819 = 1838729) B1838729
theorem B1225839 : Blo 1224430 1225839 := bstep (se 1 (by rfl) ⟨919379, by rfl⟩ : syracuseStep 1225839 = 1838759) B1838759
theorem B1225855 : Blo 1224430 1225855 := bstep (se 1 (by rfl) ⟨919391, by rfl⟩ : syracuseStep 1225855 = 1838783) B1838783
theorem B2758319 : Blo 1224430 2758319 := bstep (se 1 (by rfl) ⟨2068739, by rfl⟩ : syracuseStep 2758319 = 4137479) B4137479
theorem B2758391 : Blo 1224430 2758391 := bstep (se 1 (by rfl) ⟨2068793, by rfl⟩ : syracuseStep 2758391 = 4137587) B4137587
theorem B2619155 : Blo 1224430 2619155 := bstep (se 1 (by rfl) ⟨1964366, by rfl⟩ : syracuseStep 2619155 = 3928733) B3928733
theorem B2758697 : Blo 1224430 2758697 := bstep (se 2 (by rfl) ⟨1034511, by rfl⟩ : syracuseStep 2758697 = 2069023) B2069023
theorem B3487799 : Blo 1224430 3487799 := bstep (se 1 (by rfl) ⟨2615849, by rfl⟩ : syracuseStep 3487799 = 5231699) B5231699
theorem B6207839 : Blo 1224430 6207839 := bstep (se 1 (by rfl) ⟨4655879, by rfl⟩ : syracuseStep 6207839 = 9311759) B9311759
theorem B5585321 : Blo 1224430 5585321 := bstep (se 2 (by rfl) ⟨2094495, by rfl⟩ : syracuseStep 5585321 = 4188991) B4188991
theorem B6199739 : Blo 1224430 6199739 := bstep (se 1 (by rfl) ⟨4649804, by rfl⟩ : syracuseStep 6199739 = 9299609) B9299609
theorem B6208001 : Blo 1224430 6208001 := bstep (se 2 (by rfl) ⟨2328000, by rfl⟩ : syracuseStep 6208001 = 4656001) B4656001
theorem B3103393 : Blo 1224430 3103393 := bstep (se 2 (by rfl) ⟨1163772, by rfl⟩ : syracuseStep 3103393 = 2327545) B2327545
theorem B3488447 : Blo 1224430 3488447 := bstep (se 1 (by rfl) ⟨2616335, by rfl⟩ : syracuseStep 3488447 = 5232671) B5232671
theorem B10468075 : Blo 1224430 10468075 := bstep (se 1 (by rfl) ⟨7851056, by rfl⟩ : syracuseStep 10468075 = 15702113) B15702113
theorem B4135751 : Blo 1224430 4135751 := bstep (se 1 (by rfl) ⟨3101813, by rfl⟩ : syracuseStep 4135751 = 6203627) B6203627
theorem B5233697 : Blo 1224430 5233697 := bstep (se 2 (by rfl) ⟨1962636, by rfl⟩ : syracuseStep 5233697 = 3925273) B3925273
theorem B8388137 : Blo 1224430 8388137 := bstep (se 2 (by rfl) ⟨3145551, by rfl⟩ : syracuseStep 8388137 = 6291103) B6291103
theorem B25165475 : Blo 1224430 25165475 := bstep (se 1 (by rfl) ⟨18874106, by rfl⟩ : syracuseStep 25165475 = 37748213) B37748213
theorem B19873511 : Blo 1224430 19873511 := bstep (se 1 (by rfl) ⟨14905133, by rfl⟩ : syracuseStep 19873511 = 29810267) B29810267
theorem B3358847 : Blo 1224430 3358847 := bstep (se 1 (by rfl) ⟨2519135, by rfl⟩ : syracuseStep 3358847 = 5038271) B5038271
theorem B2621663 : Blo 1224430 2621663 := bstep (se 1 (by rfl) ⟨1966247, by rfl⟩ : syracuseStep 2621663 = 3932495) B3932495
theorem B127255211 : Blo 1224430 127255211 := bstep (se 1 (by rfl) ⟨95441408, by rfl⟩ : syracuseStep 127255211 = 190882817) B190882817
theorem B4137857 : Blo 1224430 4137857 := bstep (se 2 (by rfl) ⟨1551696, by rfl⟩ : syracuseStep 4137857 = 3103393) B3103393
theorem B14894189 : Blo 1224430 14894189 := bstep (se 3 (by rfl) ⟨2792660, by rfl⟩ : syracuseStep 14894189 = 5585321) B5585321
theorem B4138559 : Blo 1224430 4138559 := bstep (se 1 (by rfl) ⟨3103919, by rfl⟩ : syracuseStep 4138559 = 6207839) B6207839
theorem B12584591 : Blo 1224430 12584591 := bstep (se 1 (by rfl) ⟨9438443, by rfl⟩ : syracuseStep 12584591 = 18876887) B18876887
theorem B4138667 : Blo 1224430 4138667 := bstep (se 1 (by rfl) ⟨3104000, by rfl⟩ : syracuseStep 4138667 = 6208001) B6208001
theorem B3492047 : Blo 1224430 3492047 := bstep (se 1 (by rfl) ⟨2619035, by rfl⟩ : syracuseStep 3492047 = 5238071) B5238071
theorem B13249007 : Blo 1224430 13249007 := bstep (se 1 (by rfl) ⟨9936755, by rfl⟩ : syracuseStep 13249007 = 19873511) B19873511
theorem B5237455 : Blo 1224430 5237455 := bstep (se 1 (by rfl) ⟨3928091, by rfl⟩ : syracuseStep 5237455 = 7856183) B7856183
theorem B2755655 : Blo 1224430 2755655 := bstep (se 1 (by rfl) ⟨2066741, by rfl⟩ : syracuseStep 2755655 = 4133483) B4133483
theorem B2068105 : Blo 1224430 2068105 := bstep (se 2 (by rfl) ⟨775539, by rfl⟩ : syracuseStep 2068105 = 1551079) B1551079
theorem B1224431 : Blo 1224430 1224431 := bstep (se 1 (by rfl) ⟨918323, by rfl⟩ : syracuseStep 1224431 = 1836647) B1836647
theorem B1224447 : Blo 1224430 1224447 := bstep (se 1 (by rfl) ⟨918335, by rfl⟩ : syracuseStep 1224447 = 1836671) B1836671
theorem B1838879 : Blo 1224430 1838879 := bstep (se 1 (by rfl) ⟨1379159, by rfl⟩ : syracuseStep 1838879 = 2758319) B2758319
theorem B1838927 : Blo 1224430 1838927 := bstep (se 1 (by rfl) ⟨1379195, by rfl⟩ : syracuseStep 1838927 = 2758391) B2758391
theorem B1839131 : Blo 1224430 1839131 := bstep (se 1 (by rfl) ⟨1379348, by rfl⟩ : syracuseStep 1839131 = 2758697) B2758697
theorem B31387823 : Blo 1224430 31387823 := bstep (se 1 (by rfl) ⟨23540867, by rfl⟩ : syracuseStep 31387823 = 47081735) B47081735
theorem B16756999 : Blo 1224430 16756999 := bstep (se 1 (by rfl) ⟨12567749, by rfl⟩ : syracuseStep 16756999 = 25135499) B25135499
theorem B4133159 : Blo 1224430 4133159 := bstep (se 1 (by rfl) ⟨3099869, by rfl⟩ : syracuseStep 4133159 = 6199739) B6199739
theorem B2617771 : Blo 1224430 2617771 := bstep (se 1 (by rfl) ⟨1963328, by rfl⟩ : syracuseStep 2617771 = 3926657) B3926657
theorem B9302525 : Blo 1224430 9302525 := bstep (se 3 (by rfl) ⟨1744223, by rfl⟩ : syracuseStep 9302525 = 3488447) B3488447
theorem B1225215 : Blo 1224430 1225215 := bstep (se 1 (by rfl) ⟨918911, by rfl⟩ : syracuseStep 1225215 = 1837823) B1837823
theorem B2757167 : Blo 1224430 2757167 := bstep (se 1 (by rfl) ⟨2067875, by rfl⟩ : syracuseStep 2757167 = 4135751) B4135751
theorem B13242953 : Blo 1224430 13242953 := bstep (se 2 (by rfl) ⟨4966107, by rfl⟩ : syracuseStep 13242953 = 9932215) B9932215
theorem B2552431 : Blo 1224430 2552431 := bstep (se 1 (by rfl) ⟨1914323, by rfl⟩ : syracuseStep 2552431 = 3828647) B3828647
theorem B6984413 : Blo 1224430 6984413 := bstep (se 3 (by rfl) ⟨1309577, by rfl⟩ : syracuseStep 6984413 = 2619155) B2619155
theorem B1225599 : Blo 1224430 1225599 := bstep (se 1 (by rfl) ⟨919199, by rfl⟩ : syracuseStep 1225599 = 1838399) B1838399
theorem B1225727 : Blo 1224430 1225727 := bstep (se 1 (by rfl) ⟨919295, by rfl⟩ : syracuseStep 1225727 = 1838591) B1838591
theorem B5592091 : Blo 1224430 5592091 := bstep (se 1 (by rfl) ⟨4194068, by rfl⟩ : syracuseStep 5592091 = 8388137) B8388137
theorem B4142269 : Blo 1224430 4142269 := bstep (se 3 (by rfl) ⟨776675, by rfl⟩ : syracuseStep 4142269 = 1553351) B1553351
theorem B3585599 : Blo 1224430 3585599 := bstep (se 1 (by rfl) ⟨2689199, by rfl⟩ : syracuseStep 3585599 = 5378399) B5378399
theorem B15710111 : Blo 1224430 15710111 := bstep (se 1 (by rfl) ⟨11782583, by rfl⟩ : syracuseStep 15710111 = 23565167) B23565167
theorem B7854185 : Blo 1224430 7854185 := bstep (se 2 (by rfl) ⟨2945319, by rfl⟩ : syracuseStep 7854185 = 5890639) B5890639
theorem B53696621 : Blo 1224430 53696621 := bstep (se 3 (by rfl) ⟨10068116, by rfl⟩ : syracuseStep 53696621 = 20136233) B20136233
theorem B5888123 : Blo 1224430 5888123 := bstep (se 1 (by rfl) ⟨4416092, by rfl⟩ : syracuseStep 5888123 = 8832185) B8832185
theorem B2758895 : Blo 1224430 2758895 := bstep (se 1 (by rfl) ⟨2069171, by rfl⟩ : syracuseStep 2758895 = 4138343) B4138343
theorem B2758967 : Blo 1224430 2758967 := bstep (se 1 (by rfl) ⟨2069225, by rfl⟩ : syracuseStep 2758967 = 4138451) B4138451
theorem B13957433 : Blo 1224430 13957433 := bstep (se 2 (by rfl) ⟨5234037, by rfl⟩ : syracuseStep 13957433 = 10468075) B10468075
theorem B11786735 : Blo 1224430 11786735 := bstep (se 1 (by rfl) ⟨8840051, by rfl⟩ : syracuseStep 11786735 = 17680103) B17680103
theorem B2325199 : Blo 1224430 2325199 := bstep (se 1 (by rfl) ⟨1743899, by rfl⟩ : syracuseStep 2325199 = 3487799) B3487799
theorem B3489131 : Blo 1224430 3489131 := bstep (se 1 (by rfl) ⟨2616848, by rfl⟩ : syracuseStep 3489131 = 5233697) B5233697
theorem B10469033 : Blo 1224430 10469033 := bstep (se 2 (by rfl) ⟨3925887, by rfl⟩ : syracuseStep 10469033 = 7851775) B7851775
theorem B6201035 : Blo 1224430 6201035 := bstep (se 1 (by rfl) ⟨4650776, by rfl⟩ : syracuseStep 6201035 = 9301553) B9301553
theorem B16776983 : Blo 1224430 16776983 := bstep (se 1 (by rfl) ⟨12582737, by rfl⟩ : syracuseStep 16776983 = 25165475) B25165475
theorem B4136939 : Blo 1224430 4136939 := bstep (se 1 (by rfl) ⟨3102704, by rfl⟩ : syracuseStep 4136939 = 6205409) B6205409
theorem B6201683 : Blo 1224430 6201683 := bstep (se 1 (by rfl) ⟨4651262, by rfl⟩ : syracuseStep 6201683 = 9302525) B9302525
theorem B84836807 : Blo 1224430 84836807 := bstep (se 1 (by rfl) ⟨63627605, by rfl⟩ : syracuseStep 84836807 = 127255211) B127255211
theorem B3490361 : Blo 1224430 3490361 := bstep (se 2 (by rfl) ⟨1308885, by rfl⟩ : syracuseStep 3490361 = 2617771) B2617771
theorem B9929459 : Blo 1224430 9929459 := bstep (se 1 (by rfl) ⟨7447094, by rfl⟩ : syracuseStep 9929459 = 14894189) B14894189
theorem B8389727 : Blo 1224430 8389727 := bstep (se 1 (by rfl) ⟨6292295, by rfl⟩ : syracuseStep 8389727 = 12584591) B12584591
theorem B7456121 : Blo 1224430 7456121 := bstep (se 2 (by rfl) ⟨2796045, by rfl⟩ : syracuseStep 7456121 = 5592091) B5592091
theorem B5236123 : Blo 1224430 5236123 := bstep (se 1 (by rfl) ⟨3927092, by rfl⟩ : syracuseStep 5236123 = 7854185) B7854185
theorem B3925415 : Blo 1224430 3925415 := bstep (se 1 (by rfl) ⟨2944061, by rfl⟩ : syracuseStep 3925415 = 5888123) B5888123
theorem B2328031 : Blo 1224430 2328031 := bstep (se 1 (by rfl) ⟨1746023, by rfl⟩ : syracuseStep 2328031 = 3492047) B3492047
theorem B5523025 : Blo 1224430 5523025 := bstep (se 2 (by rfl) ⟨2071134, by rfl⟩ : syracuseStep 5523025 = 4142269) B4142269
theorem B8832671 : Blo 1224430 8832671 := bstep (se 1 (by rfl) ⟨6624503, by rfl⟩ : syracuseStep 8832671 = 13249007) B13249007
theorem B7857823 : Blo 1224430 7857823 := bstep (se 1 (by rfl) ⟨5893367, by rfl⟩ : syracuseStep 7857823 = 11786735) B11786735
theorem B1837103 : Blo 1224430 1837103 := bstep (se 1 (by rfl) ⟨1377827, by rfl⟩ : syracuseStep 1837103 = 2755655) B2755655
theorem B11184655 : Blo 1224430 11184655 := bstep (se 1 (by rfl) ⟨8388491, by rfl⟩ : syracuseStep 11184655 = 16776983) B16776983
theorem B2239231 : Blo 1224430 2239231 := bstep (se 1 (by rfl) ⟨1679423, by rfl⟩ : syracuseStep 2239231 = 3358847) B3358847
theorem B20925215 : Blo 1224430 20925215 := bstep (se 1 (by rfl) ⟨15693911, by rfl⟩ : syracuseStep 20925215 = 31387823) B31387823
theorem B1747775 : Blo 1224430 1747775 := bstep (se 1 (by rfl) ⟨1310831, by rfl⟩ : syracuseStep 1747775 = 2621663) B2621663
theorem B2755439 : Blo 1224430 2755439 := bstep (se 1 (by rfl) ⟨2066579, by rfl⟩ : syracuseStep 2755439 = 4133159) B4133159
theorem B1838111 : Blo 1224430 1838111 := bstep (se 1 (by rfl) ⟨1378583, by rfl⟩ : syracuseStep 1838111 = 2757167) B2757167
theorem B4656275 : Blo 1224430 4656275 := bstep (se 1 (by rfl) ⟨3492206, by rfl⟩ : syracuseStep 4656275 = 6984413) B6984413
theorem B3403241 : Blo 1224430 3403241 := bstep (se 2 (by rfl) ⟨1276215, by rfl⟩ : syracuseStep 3403241 = 2552431) B2552431
theorem B3100265 : Blo 1224430 3100265 := bstep (se 2 (by rfl) ⟨1162599, by rfl⟩ : syracuseStep 3100265 = 2325199) B2325199
theorem B6983273 : Blo 1224430 6983273 := bstep (se 2 (by rfl) ⟨2618727, by rfl⟩ : syracuseStep 6983273 = 5237455) B5237455
theorem B10473407 : Blo 1224430 10473407 := bstep (se 1 (by rfl) ⟨7855055, by rfl⟩ : syracuseStep 10473407 = 15710111) B15710111
theorem B89370661 : Blo 1224430 89370661 := bstep (se 4 (by rfl) ⟨8378499, by rfl⟩ : syracuseStep 89370661 = 16756999) B16756999
theorem B1839263 : Blo 1224430 1839263 := bstep (se 1 (by rfl) ⟨1379447, by rfl⟩ : syracuseStep 1839263 = 2758895) B2758895
theorem B1839311 : Blo 1224430 1839311 := bstep (se 1 (by rfl) ⟨1379483, by rfl⟩ : syracuseStep 1839311 = 2758967) B2758967
theorem B2757473 : Blo 1224430 2757473 := bstep (se 2 (by rfl) ⟨1034052, by rfl⟩ : syracuseStep 2757473 = 2068105) B2068105
theorem B4134023 : Blo 1224430 4134023 := bstep (se 1 (by rfl) ⟨3100517, by rfl⟩ : syracuseStep 4134023 = 6201035) B6201035
theorem B1225919 : Blo 1224430 1225919 := bstep (se 1 (by rfl) ⟨919439, by rfl⟩ : syracuseStep 1225919 = 1838879) B1838879
theorem B1225951 : Blo 1224430 1225951 := bstep (se 1 (by rfl) ⟨919463, by rfl⟩ : syracuseStep 1225951 = 1838927) B1838927
theorem B2757959 : Blo 1224430 2757959 := bstep (se 1 (by rfl) ⟨2068469, by rfl⟩ : syracuseStep 2757959 = 4136939) B4136939
theorem B1226087 : Blo 1224430 1226087 := bstep (se 1 (by rfl) ⟨919565, by rfl⟩ : syracuseStep 1226087 = 1839131) B1839131
theorem B8828635 : Blo 1224430 8828635 := bstep (se 1 (by rfl) ⟨6621476, by rfl⟩ : syracuseStep 8828635 = 13242953) B13242953
theorem B2758571 : Blo 1224430 2758571 := bstep (se 1 (by rfl) ⟨2068928, by rfl⟩ : syracuseStep 2758571 = 4137857) B4137857
theorem B2390399 : Blo 1224430 2390399 := bstep (se 1 (by rfl) ⟨1792799, by rfl⟩ : syracuseStep 2390399 = 3585599) B3585599
theorem B2759039 : Blo 1224430 2759039 := bstep (se 1 (by rfl) ⟨2069279, by rfl⟩ : syracuseStep 2759039 = 4138559) B4138559
theorem B2759111 : Blo 1224430 2759111 := bstep (se 1 (by rfl) ⟨2069333, by rfl⟩ : syracuseStep 2759111 = 4138667) B4138667
theorem B35797747 : Blo 1224430 35797747 := bstep (se 1 (by rfl) ⟨26848310, by rfl⟩ : syracuseStep 35797747 = 53696621) B53696621
theorem B9304955 : Blo 1224430 9304955 := bstep (se 1 (by rfl) ⟨6978716, by rfl⟩ : syracuseStep 9304955 = 13957433) B13957433
theorem B2326087 : Blo 1224430 2326087 := bstep (se 1 (by rfl) ⟨1744565, by rfl⟩ : syracuseStep 2326087 = 3489131) B3489131
theorem B6979355 : Blo 1224430 6979355 := bstep (se 1 (by rfl) ⟨5234516, by rfl⟩ : syracuseStep 6979355 = 10469033) B10469033
theorem B119160881 : Blo 1224430 119160881 := bstep (se 2 (by rfl) ⟨44685330, by rfl⟩ : syracuseStep 119160881 = 89370661) B89370661
theorem B56557871 : Blo 1224430 56557871 := bstep (se 1 (by rfl) ⟨42418403, by rfl⟩ : syracuseStep 56557871 = 84836807) B84836807
theorem B2326907 : Blo 1224430 2326907 := bstep (se 1 (by rfl) ⟨1745180, by rfl⟩ : syracuseStep 2326907 = 3490361) B3490361
theorem B6619639 : Blo 1224430 6619639 := bstep (se 1 (by rfl) ⟨4964729, by rfl⟩ : syracuseStep 6619639 = 9929459) B9929459
theorem B6981497 : Blo 1224430 6981497 := bstep (se 2 (by rfl) ⟨2618061, by rfl⟩ : syracuseStep 6981497 = 5236123) B5236123
theorem B1836959 : Blo 1224430 1836959 := bstep (se 1 (by rfl) ⟨1377719, by rfl⟩ : syracuseStep 1836959 = 2755439) B2755439
theorem B6203303 : Blo 1224430 6203303 := bstep (se 1 (by rfl) ⟨4652477, by rfl⟩ : syracuseStep 6203303 = 9304955) B9304955
theorem B2066843 : Blo 1224430 2066843 := bstep (se 1 (by rfl) ⟨1550132, by rfl⟩ : syracuseStep 2066843 = 3100265) B3100265
theorem B4655515 : Blo 1224430 4655515 := bstep (se 1 (by rfl) ⟨3491636, by rfl⟩ : syracuseStep 4655515 = 6983273) B6983273
theorem B6982271 : Blo 1224430 6982271 := bstep (se 1 (by rfl) ⟨5236703, by rfl⟩ : syracuseStep 6982271 = 10473407) B10473407
theorem B1838315 : Blo 1224430 1838315 := bstep (se 1 (by rfl) ⟨1378736, by rfl⟩ : syracuseStep 1838315 = 2757473) B2757473
theorem B14912873 : Blo 1224430 14912873 := bstep (se 2 (by rfl) ⟨5592327, by rfl⟩ : syracuseStep 14912873 = 11184655) B11184655
theorem B2756015 : Blo 1224430 2756015 := bstep (se 1 (by rfl) ⟨2067011, by rfl⟩ : syracuseStep 2756015 = 4134023) B4134023
theorem B1838639 : Blo 1224430 1838639 := bstep (se 1 (by rfl) ⟨1378979, by rfl⟩ : syracuseStep 1838639 = 2757959) B2757959
theorem B2616943 : Blo 1224430 2616943 := bstep (se 1 (by rfl) ⟨1962707, by rfl⟩ : syracuseStep 2616943 = 3925415) B3925415
theorem B47730329 : Blo 1224430 47730329 := bstep (se 2 (by rfl) ⟨17898873, by rfl⟩ : syracuseStep 47730329 = 35797747) B35797747
theorem B2985641 : Blo 1224430 2985641 := bstep (se 2 (by rfl) ⟨1119615, by rfl⟩ : syracuseStep 2985641 = 2239231) B2239231
theorem B1839047 : Blo 1224430 1839047 := bstep (se 1 (by rfl) ⟨1379285, by rfl⟩ : syracuseStep 1839047 = 2758571) B2758571
theorem B1224735 : Blo 1224430 1224735 := bstep (se 1 (by rfl) ⟨918551, by rfl⟩ : syracuseStep 1224735 = 1837103) B1837103
theorem B1593599 : Blo 1224430 1593599 := bstep (se 1 (by rfl) ⟨1195199, by rfl⟩ : syracuseStep 1593599 = 2390399) B2390399
theorem B1839359 : Blo 1224430 1839359 := bstep (se 1 (by rfl) ⟨1379519, by rfl⟩ : syracuseStep 1839359 = 2759039) B2759039
theorem B1839407 : Blo 1224430 1839407 := bstep (se 1 (by rfl) ⟨1379555, by rfl⟩ : syracuseStep 1839407 = 2759111) B2759111
theorem B1225407 : Blo 1224430 1225407 := bstep (se 1 (by rfl) ⟨919055, by rfl⟩ : syracuseStep 1225407 = 1838111) B1838111
theorem B3101449 : Blo 1224430 3101449 := bstep (se 2 (by rfl) ⟨1163043, by rfl⟩ : syracuseStep 3101449 = 2326087) B2326087
theorem B1226175 : Blo 1224430 1226175 := bstep (se 1 (by rfl) ⟨919631, by rfl⟩ : syracuseStep 1226175 = 1839263) B1839263
theorem B1226207 : Blo 1224430 1226207 := bstep (se 1 (by rfl) ⟨919655, by rfl⟩ : syracuseStep 1226207 = 1839311) B1839311
theorem B4134455 : Blo 1224430 4134455 := bstep (se 1 (by rfl) ⟨3100841, by rfl⟩ : syracuseStep 4134455 = 6201683) B6201683
theorem B5593151 : Blo 1224430 5593151 := bstep (se 1 (by rfl) ⟨4194863, by rfl⟩ : syracuseStep 5593151 = 8389727) B8389727
theorem B4970747 : Blo 1224430 4970747 := bstep (se 1 (by rfl) ⟨3728060, by rfl⟩ : syracuseStep 4970747 = 7456121) B7456121
theorem B5888447 : Blo 1224430 5888447 := bstep (se 1 (by rfl) ⟨4416335, by rfl⟩ : syracuseStep 5888447 = 8832671) B8832671
theorem B13950143 : Blo 1224430 13950143 := bstep (se 1 (by rfl) ⟨10462607, by rfl⟩ : syracuseStep 13950143 = 20925215) B20925215
theorem B3104041 : Blo 1224430 3104041 := bstep (se 2 (by rfl) ⟨1164015, by rfl⟩ : syracuseStep 3104041 = 2328031) B2328031
theorem B3104183 : Blo 1224430 3104183 := bstep (se 1 (by rfl) ⟨2328137, by rfl⟩ : syracuseStep 3104183 = 4656275) B4656275
theorem B7364033 : Blo 1224430 7364033 := bstep (se 2 (by rfl) ⟨2761512, by rfl⟩ : syracuseStep 7364033 = 5523025) B5523025
theorem B4660733 : Blo 1224430 4660733 := bstep (se 3 (by rfl) ⟨873887, by rfl⟩ : syracuseStep 4660733 = 1747775) B1747775
theorem B10477097 : Blo 1224430 10477097 := bstep (se 2 (by rfl) ⟨3928911, by rfl⟩ : syracuseStep 10477097 = 7857823) B7857823
theorem B11771513 : Blo 1224430 11771513 := bstep (se 2 (by rfl) ⟨4414317, by rfl⟩ : syracuseStep 11771513 = 8828635) B8828635
theorem B2268827 : Blo 1224430 2268827 := bstep (se 1 (by rfl) ⟨1701620, by rfl⟩ : syracuseStep 2268827 = 3403241) B3403241
theorem B4652903 : Blo 1224430 4652903 := bstep (se 1 (by rfl) ⟨3489677, by rfl⟩ : syracuseStep 4652903 = 6979355) B6979355
theorem B13255325 : Blo 1224430 13255325 := bstep (se 3 (by rfl) ⟨2485373, by rfl⟩ : syracuseStep 13255325 = 4970747) B4970747
theorem B4654331 : Blo 1224430 4654331 := bstep (se 1 (by rfl) ⟨3490748, by rfl⟩ : syracuseStep 4654331 = 6981497) B6981497
theorem B3728767 : Blo 1224430 3728767 := bstep (se 1 (by rfl) ⟨2796575, by rfl⟩ : syracuseStep 3728767 = 5593151) B5593151
theorem B1377895 : Blo 1224430 1377895 := bstep (se 1 (by rfl) ⟨1033421, by rfl⟩ : syracuseStep 1377895 = 2066843) B2066843
theorem B3925631 : Blo 1224430 3925631 := bstep (se 1 (by rfl) ⟨2944223, by rfl⟩ : syracuseStep 3925631 = 5888447) B5888447
theorem B4138721 : Blo 1224430 4138721 := bstep (se 2 (by rfl) ⟨1552020, by rfl⟩ : syracuseStep 4138721 = 3104041) B3104041
theorem B4654847 : Blo 1224430 4654847 := bstep (se 1 (by rfl) ⟨3491135, by rfl⟩ : syracuseStep 4654847 = 6982271) B6982271
theorem B9300095 : Blo 1224430 9300095 := bstep (se 1 (by rfl) ⟨6975071, by rfl⟩ : syracuseStep 9300095 = 13950143) B13950143
theorem B1837343 : Blo 1224430 1837343 := bstep (se 1 (by rfl) ⟨1378007, by rfl⟩ : syracuseStep 1837343 = 2756015) B2756015
theorem B4909355 : Blo 1224430 4909355 := bstep (se 1 (by rfl) ⟨3682016, by rfl⟩ : syracuseStep 4909355 = 7364033) B7364033
theorem B3107155 : Blo 1224430 3107155 := bstep (se 1 (by rfl) ⟨2330366, by rfl⟩ : syracuseStep 3107155 = 4660733) B4660733
theorem B31820219 : Blo 1224430 31820219 := bstep (se 1 (by rfl) ⟨23865164, by rfl⟩ : syracuseStep 31820219 = 47730329) B47730329
theorem B79440587 : Blo 1224430 79440587 := bstep (se 1 (by rfl) ⟨59580440, by rfl⟩ : syracuseStep 79440587 = 119160881) B119160881
theorem B8826185 : Blo 1224430 8826185 := bstep (se 2 (by rfl) ⟨3309819, by rfl⟩ : syracuseStep 8826185 = 6619639) B6619639
theorem B6205085 : Blo 1224430 6205085 := bstep (se 3 (by rfl) ⟨1163453, by rfl⟩ : syracuseStep 6205085 = 2326907) B2326907
theorem B2756303 : Blo 1224430 2756303 := bstep (se 1 (by rfl) ⟨2067227, by rfl⟩ : syracuseStep 2756303 = 4134455) B4134455
theorem B1224639 : Blo 1224430 1224639 := bstep (se 1 (by rfl) ⟨918479, by rfl⟩ : syracuseStep 1224639 = 1836959) B1836959
theorem B1225543 : Blo 1224430 1225543 := bstep (se 1 (by rfl) ⟨919157, by rfl⟩ : syracuseStep 1225543 = 1838315) B1838315
theorem B9941915 : Blo 1224430 9941915 := bstep (se 1 (by rfl) ⟨7456436, by rfl⟩ : syracuseStep 9941915 = 14912873) B14912873
theorem B2069455 : Blo 1224430 2069455 := bstep (se 1 (by rfl) ⟨1552091, by rfl⟩ : syracuseStep 2069455 = 3104183) B3104183
theorem B1225759 : Blo 1224430 1225759 := bstep (se 1 (by rfl) ⟨919319, by rfl⟩ : syracuseStep 1225759 = 1838639) B1838639
theorem B6984731 : Blo 1224430 6984731 := bstep (se 1 (by rfl) ⟨5238548, by rfl⟩ : syracuseStep 6984731 = 10477097) B10477097
theorem B1512551 : Blo 1224430 1512551 := bstep (se 1 (by rfl) ⟨1134413, by rfl⟩ : syracuseStep 1512551 = 2268827) B2268827
theorem B3101935 : Blo 1224430 3101935 := bstep (se 1 (by rfl) ⟨2326451, by rfl⟩ : syracuseStep 3101935 = 4652903) B4652903
theorem B1226031 : Blo 1224430 1226031 := bstep (se 1 (by rfl) ⟨919523, by rfl⟩ : syracuseStep 1226031 = 1839047) B1839047
theorem B1226239 : Blo 1224430 1226239 := bstep (se 1 (by rfl) ⟨919679, by rfl⟩ : syracuseStep 1226239 = 1839359) B1839359
theorem B37705247 : Blo 1224430 37705247 := bstep (se 1 (by rfl) ⟨28278935, by rfl⟩ : syracuseStep 37705247 = 56557871) B56557871
theorem B1226271 : Blo 1224430 1226271 := bstep (se 1 (by rfl) ⟨919703, by rfl⟩ : syracuseStep 1226271 = 1839407) B1839407
theorem B6207353 : Blo 1224430 6207353 := bstep (se 2 (by rfl) ⟨2327757, by rfl⟩ : syracuseStep 6207353 = 4655515) B4655515
theorem B4249597 : Blo 1224430 4249597 := bstep (se 3 (by rfl) ⟨796799, by rfl⟩ : syracuseStep 4249597 = 1593599) B1593599
theorem B4135265 : Blo 1224430 4135265 := bstep (se 2 (by rfl) ⟨1550724, by rfl⟩ : syracuseStep 4135265 = 3101449) B3101449
theorem B4135535 : Blo 1224430 4135535 := bstep (se 1 (by rfl) ⟨3101651, by rfl⟩ : syracuseStep 4135535 = 6203303) B6203303
theorem B3489257 : Blo 1224430 3489257 := bstep (se 2 (by rfl) ⟨1308471, by rfl⟩ : syracuseStep 3489257 = 2616943) B2616943
theorem B7847675 : Blo 1224430 7847675 := bstep (se 1 (by rfl) ⟨5885756, by rfl⟩ : syracuseStep 7847675 = 11771513) B11771513
theorem B1990427 : Blo 1224430 1990427 := bstep (se 1 (by rfl) ⟨1492820, by rfl⟩ : syracuseStep 1990427 = 2985641) B2985641
theorem B6627943 : Blo 1224430 6627943 := bstep (se 1 (by rfl) ⟨4970957, by rfl⟩ : syracuseStep 6627943 = 9941915) B9941915
theorem B23536493 : Blo 1224430 23536493 := bstep (se 3 (by rfl) ⟨4413092, by rfl⟩ : syracuseStep 23536493 = 8826185) B8826185
theorem B4138235 : Blo 1224430 4138235 := bstep (se 1 (by rfl) ⟨3103676, by rfl⟩ : syracuseStep 4138235 = 6207353) B6207353
theorem B1837193 : Blo 1224430 1837193 := bstep (se 2 (by rfl) ⟨688947, by rfl⟩ : syracuseStep 1837193 = 1377895) B1377895
theorem B1837535 : Blo 1224430 1837535 := bstep (se 1 (by rfl) ⟨1378151, by rfl⟩ : syracuseStep 1837535 = 2756303) B2756303
theorem B4033469 : Blo 1224430 4033469 := bstep (se 3 (by rfl) ⟨756275, by rfl⟩ : syracuseStep 4033469 = 1512551) B1512551
theorem B4656487 : Blo 1224430 4656487 := bstep (se 1 (by rfl) ⟨3492365, by rfl⟩ : syracuseStep 4656487 = 6984731) B6984731
theorem B25136831 : Blo 1224430 25136831 := bstep (se 1 (by rfl) ⟨18852623, by rfl⟩ : syracuseStep 25136831 = 37705247) B37705247
theorem B1224895 : Blo 1224430 1224895 := bstep (se 1 (by rfl) ⟨918671, by rfl⟩ : syracuseStep 1224895 = 1837343) B1837343
theorem B3272903 : Blo 1224430 3272903 := bstep (se 1 (by rfl) ⟨2454677, by rfl⟩ : syracuseStep 3272903 = 4909355) B4909355
theorem B2756843 : Blo 1224430 2756843 := bstep (se 1 (by rfl) ⟨2067632, by rfl⟩ : syracuseStep 2756843 = 4135265) B4135265
theorem B21213479 : Blo 1224430 21213479 := bstep (se 1 (by rfl) ⟨15910109, by rfl⟩ : syracuseStep 21213479 = 31820219) B31820219
theorem B2757023 : Blo 1224430 2757023 := bstep (se 1 (by rfl) ⟨2067767, by rfl⟩ : syracuseStep 2757023 = 4135535) B4135535
theorem B5231783 : Blo 1224430 5231783 := bstep (se 1 (by rfl) ⟨3923837, by rfl⟩ : syracuseStep 5231783 = 7847675) B7847675
theorem B5666129 : Blo 1224430 5666129 := bstep (se 2 (by rfl) ⟨2124798, by rfl⟩ : syracuseStep 5666129 = 4249597) B4249597
theorem B8836883 : Blo 1224430 8836883 := bstep (se 1 (by rfl) ⟨6627662, by rfl⟩ : syracuseStep 8836883 = 13255325) B13255325
theorem B4142873 : Blo 1224430 4142873 := bstep (se 2 (by rfl) ⟨1553577, by rfl⟩ : syracuseStep 4142873 = 3107155) B3107155
theorem B3102887 : Blo 1224430 3102887 := bstep (se 1 (by rfl) ⟨2327165, by rfl⟩ : syracuseStep 3102887 = 4654331) B4654331
theorem B2759147 : Blo 1224430 2759147 := bstep (se 1 (by rfl) ⟨2069360, by rfl⟩ : syracuseStep 2759147 = 4138721) B4138721
theorem B3103231 : Blo 1224430 3103231 := bstep (se 1 (by rfl) ⟨2327423, by rfl⟩ : syracuseStep 3103231 = 4654847) B4654847
theorem B2759273 : Blo 1224430 2759273 := bstep (se 2 (by rfl) ⟨1034727, by rfl⟩ : syracuseStep 2759273 = 2069455) B2069455
theorem B6200063 : Blo 1224430 6200063 := bstep (se 1 (by rfl) ⟨4650047, by rfl⟩ : syracuseStep 6200063 = 9300095) B9300095
theorem B4135913 : Blo 1224430 4135913 := bstep (se 2 (by rfl) ⟨1550967, by rfl⟩ : syracuseStep 4135913 = 3101935) B3101935
theorem B10468349 : Blo 1224430 10468349 := bstep (se 3 (by rfl) ⟨1962815, by rfl⟩ : syracuseStep 10468349 = 3925631) B3925631
theorem B52960391 : Blo 1224430 52960391 := bstep (se 1 (by rfl) ⟨39720293, by rfl⟩ : syracuseStep 52960391 = 79440587) B79440587
theorem B4971689 : Blo 1224430 4971689 := bstep (se 2 (by rfl) ⟨1864383, by rfl⟩ : syracuseStep 4971689 = 3728767) B3728767
theorem B5307805 : Blo 1224430 5307805 := bstep (se 3 (by rfl) ⟨995213, by rfl⟩ : syracuseStep 5307805 = 1990427) B1990427
theorem B2326171 : Blo 1224430 2326171 := bstep (se 1 (by rfl) ⟨1744628, by rfl⟩ : syracuseStep 2326171 = 3489257) B3489257
theorem B4136723 : Blo 1224430 4136723 := bstep (se 1 (by rfl) ⟨3102542, by rfl⟩ : syracuseStep 4136723 = 6205085) B6205085
theorem B4137641 : Blo 1224430 4137641 := bstep (se 2 (by rfl) ⟨1551615, by rfl⟩ : syracuseStep 4137641 = 3103231) B3103231
theorem B3777419 : Blo 1224430 3777419 := bstep (se 1 (by rfl) ⟨2833064, by rfl⟩ : syracuseStep 3777419 = 5666129) B5666129
theorem B5891255 : Blo 1224430 5891255 := bstep (se 1 (by rfl) ⟨4418441, by rfl⟩ : syracuseStep 5891255 = 8836883) B8836883
theorem B2181935 : Blo 1224430 2181935 := bstep (se 1 (by rfl) ⟨1636451, by rfl⟩ : syracuseStep 2181935 = 3272903) B3272903
theorem B1837895 : Blo 1224430 1837895 := bstep (se 1 (by rfl) ⟨1378421, by rfl⟩ : syracuseStep 1837895 = 2756843) B2756843
theorem B14142319 : Blo 1224430 14142319 := bstep (se 1 (by rfl) ⟨10606739, by rfl⟩ : syracuseStep 14142319 = 21213479) B21213479
theorem B1838015 : Blo 1224430 1838015 := bstep (se 1 (by rfl) ⟨1378511, by rfl⟩ : syracuseStep 1838015 = 2757023) B2757023
theorem B15690995 : Blo 1224430 15690995 := bstep (se 1 (by rfl) ⟨11768246, by rfl⟩ : syracuseStep 15690995 = 23536493) B23536493
theorem B1224795 : Blo 1224430 1224795 := bstep (se 1 (by rfl) ⟨918596, by rfl⟩ : syracuseStep 1224795 = 1837193) B1837193
theorem B2068591 : Blo 1224430 2068591 := bstep (se 1 (by rfl) ⟨1551443, by rfl⟩ : syracuseStep 2068591 = 3102887) B3102887
theorem B1225023 : Blo 1224430 1225023 := bstep (se 1 (by rfl) ⟨918767, by rfl⟩ : syracuseStep 1225023 = 1837535) B1837535
theorem B1839431 : Blo 1224430 1839431 := bstep (se 1 (by rfl) ⟨1379573, by rfl⟩ : syracuseStep 1839431 = 2759147) B2759147
theorem B1839515 : Blo 1224430 1839515 := bstep (se 1 (by rfl) ⟨1379636, by rfl⟩ : syracuseStep 1839515 = 2759273) B2759273
theorem B4133375 : Blo 1224430 4133375 := bstep (se 1 (by rfl) ⟨3100031, by rfl⟩ : syracuseStep 4133375 = 6200063) B6200063
theorem B2757275 : Blo 1224430 2757275 := bstep (se 1 (by rfl) ⟨2067956, by rfl⟩ : syracuseStep 2757275 = 4135913) B4135913
theorem B11047661 : Blo 1224430 11047661 := bstep (se 3 (by rfl) ⟨2071436, by rfl⟩ : syracuseStep 11047661 = 4142873) B4142873
theorem B3314459 : Blo 1224430 3314459 := bstep (se 1 (by rfl) ⟨2485844, by rfl⟩ : syracuseStep 3314459 = 4971689) B4971689
theorem B3101561 : Blo 1224430 3101561 := bstep (se 2 (by rfl) ⟨1163085, by rfl⟩ : syracuseStep 3101561 = 2326171) B2326171
theorem B16757887 : Blo 1224430 16757887 := bstep (se 1 (by rfl) ⟨12568415, by rfl⟩ : syracuseStep 16757887 = 25136831) B25136831
theorem B2757815 : Blo 1224430 2757815 := bstep (se 1 (by rfl) ⟨2068361, by rfl⟩ : syracuseStep 2757815 = 4136723) B4136723
theorem B3487855 : Blo 1224430 3487855 := bstep (se 1 (by rfl) ⟨2615891, by rfl⟩ : syracuseStep 3487855 = 5231783) B5231783
theorem B8837257 : Blo 1224430 8837257 := bstep (se 2 (by rfl) ⟨3313971, by rfl⟩ : syracuseStep 8837257 = 6627943) B6627943
theorem B2758823 : Blo 1224430 2758823 := bstep (se 1 (by rfl) ⟨2069117, by rfl⟩ : syracuseStep 2758823 = 4138235) B4138235
theorem B6208649 : Blo 1224430 6208649 := bstep (se 2 (by rfl) ⟨2328243, by rfl⟩ : syracuseStep 6208649 = 4656487) B4656487
theorem B7077073 : Blo 1224430 7077073 := bstep (se 2 (by rfl) ⟨2653902, by rfl⟩ : syracuseStep 7077073 = 5307805) B5307805
theorem B6978899 : Blo 1224430 6978899 := bstep (se 1 (by rfl) ⟨5234174, by rfl⟩ : syracuseStep 6978899 = 10468349) B10468349
theorem B35306927 : Blo 1224430 35306927 := bstep (se 1 (by rfl) ⟨26480195, by rfl⟩ : syracuseStep 35306927 = 52960391) B52960391
theorem B10755917 : Blo 1224430 10755917 := bstep (se 3 (by rfl) ⟨2016734, by rfl⟩ : syracuseStep 10755917 = 4033469) B4033469
theorem B7365107 : Blo 1224430 7365107 := bstep (se 1 (by rfl) ⟨5523830, by rfl⟩ : syracuseStep 7365107 = 11047661) B11047661
theorem B75425701 : Blo 1224430 75425701 := bstep (se 4 (by rfl) ⟨7071159, by rfl⟩ : syracuseStep 75425701 = 14142319) B14142319
theorem B4139099 : Blo 1224430 4139099 := bstep (se 1 (by rfl) ⟨3104324, by rfl⟩ : syracuseStep 4139099 = 6208649) B6208649
theorem B5818493 : Blo 1224430 5818493 := bstep (se 3 (by rfl) ⟨1090967, by rfl⟩ : syracuseStep 5818493 = 2181935) B2181935
theorem B23537951 : Blo 1224430 23537951 := bstep (se 1 (by rfl) ⟨17653463, by rfl⟩ : syracuseStep 23537951 = 35306927) B35306927
theorem B7170611 : Blo 1224430 7170611 := bstep (se 1 (by rfl) ⟨5377958, by rfl⟩ : syracuseStep 7170611 = 10755917) B10755917
theorem B11783009 : Blo 1224430 11783009 := bstep (se 2 (by rfl) ⟨4418628, by rfl⟩ : syracuseStep 11783009 = 8837257) B8837257
theorem B2755583 : Blo 1224430 2755583 := bstep (se 1 (by rfl) ⟨2066687, by rfl⟩ : syracuseStep 2755583 = 4133375) B4133375
theorem B1838183 : Blo 1224430 1838183 := bstep (se 1 (by rfl) ⟨1378637, by rfl⟩ : syracuseStep 1838183 = 2757275) B2757275
theorem B2067707 : Blo 1224430 2067707 := bstep (se 1 (by rfl) ⟨1550780, by rfl⟩ : syracuseStep 2067707 = 3101561) B3101561
theorem B1838543 : Blo 1224430 1838543 := bstep (se 1 (by rfl) ⟨1378907, by rfl⟩ : syracuseStep 1838543 = 2757815) B2757815
theorem B3927503 : Blo 1224430 3927503 := bstep (se 1 (by rfl) ⟨2945627, by rfl⟩ : syracuseStep 3927503 = 5891255) B5891255
theorem B1839215 : Blo 1224430 1839215 := bstep (se 1 (by rfl) ⟨1379411, by rfl⟩ : syracuseStep 1839215 = 2758823) B2758823
theorem B22343849 : Blo 1224430 22343849 := bstep (se 2 (by rfl) ⟨8378943, by rfl⟩ : syracuseStep 22343849 = 16757887) B16757887
theorem B1225263 : Blo 1224430 1225263 := bstep (se 1 (by rfl) ⟨918947, by rfl⟩ : syracuseStep 1225263 = 1837895) B1837895
theorem B1225343 : Blo 1224430 1225343 := bstep (se 1 (by rfl) ⟨919007, by rfl⟩ : syracuseStep 1225343 = 1838015) B1838015
theorem B10073117 : Blo 1224430 10073117 := bstep (se 3 (by rfl) ⟨1888709, by rfl⟩ : syracuseStep 10073117 = 3777419) B3777419
theorem B4650473 : Blo 1224430 4650473 := bstep (se 2 (by rfl) ⟨1743927, by rfl⟩ : syracuseStep 4650473 = 3487855) B3487855
theorem B2758121 : Blo 1224430 2758121 := bstep (se 2 (by rfl) ⟨1034295, by rfl⟩ : syracuseStep 2758121 = 2068591) B2068591
theorem B1226287 : Blo 1224430 1226287 := bstep (se 1 (by rfl) ⟨919715, by rfl⟩ : syracuseStep 1226287 = 1839431) B1839431
theorem B1226343 : Blo 1224430 1226343 := bstep (se 1 (by rfl) ⟨919757, by rfl⟩ : syracuseStep 1226343 = 1839515) B1839515
theorem B2758427 : Blo 1224430 2758427 := bstep (se 1 (by rfl) ⟨2068820, by rfl⟩ : syracuseStep 2758427 = 4137641) B4137641
theorem B9436097 : Blo 1224430 9436097 := bstep (se 2 (by rfl) ⟨3538536, by rfl⟩ : syracuseStep 9436097 = 7077073) B7077073
theorem B8838557 : Blo 1224430 8838557 := bstep (se 3 (by rfl) ⟨1657229, by rfl⟩ : syracuseStep 8838557 = 3314459) B3314459
theorem B10460663 : Blo 1224430 10460663 := bstep (se 1 (by rfl) ⟨7845497, by rfl⟩ : syracuseStep 10460663 = 15690995) B15690995
theorem B4652599 : Blo 1224430 4652599 := bstep (se 1 (by rfl) ⟨3489449, by rfl⟩ : syracuseStep 4652599 = 6978899) B6978899
theorem B26861645 : Blo 1224430 26861645 := bstep (se 3 (by rfl) ⟨5036558, by rfl⟩ : syracuseStep 26861645 = 10073117) B10073117
theorem B15515981 : Blo 1224430 15515981 := bstep (se 3 (by rfl) ⟨2909246, by rfl⟩ : syracuseStep 15515981 = 5818493) B5818493
theorem B19121629 : Blo 1224430 19121629 := bstep (se 3 (by rfl) ⟨3585305, by rfl⟩ : syracuseStep 19121629 = 7170611) B7170611
theorem B1837055 : Blo 1224430 1837055 := bstep (se 1 (by rfl) ⟨1377791, by rfl⟩ : syracuseStep 1837055 = 2755583) B2755583
theorem B6203465 : Blo 1224430 6203465 := bstep (se 2 (by rfl) ⟨2326299, by rfl⟩ : syracuseStep 6203465 = 4652599) B4652599
theorem B1378471 : Blo 1224430 1378471 := bstep (se 1 (by rfl) ⟨1033853, by rfl⟩ : syracuseStep 1378471 = 2067707) B2067707
theorem B5892371 : Blo 1224430 5892371 := bstep (se 1 (by rfl) ⟨4419278, by rfl⟩ : syracuseStep 5892371 = 8838557) B8838557
theorem B6973775 : Blo 1224430 6973775 := bstep (se 1 (by rfl) ⟨5230331, by rfl⟩ : syracuseStep 6973775 = 10460663) B10460663
theorem B100567601 : Blo 1224430 100567601 := bstep (se 2 (by rfl) ⟨37712850, by rfl⟩ : syracuseStep 100567601 = 75425701) B75425701
theorem B14895899 : Blo 1224430 14895899 := bstep (se 1 (by rfl) ⟨11171924, by rfl⟩ : syracuseStep 14895899 = 22343849) B22343849
theorem B4910071 : Blo 1224430 4910071 := bstep (se 1 (by rfl) ⟨3682553, by rfl⟩ : syracuseStep 4910071 = 7365107) B7365107
theorem B3100315 : Blo 1224430 3100315 := bstep (se 1 (by rfl) ⟨2325236, by rfl⟩ : syracuseStep 3100315 = 4650473) B4650473
theorem B1838747 : Blo 1224430 1838747 := bstep (se 1 (by rfl) ⟨1379060, by rfl⟩ : syracuseStep 1838747 = 2758121) B2758121
theorem B1838951 : Blo 1224430 1838951 := bstep (se 1 (by rfl) ⟨1379213, by rfl⟩ : syracuseStep 1838951 = 2758427) B2758427
theorem B15691967 : Blo 1224430 15691967 := bstep (se 1 (by rfl) ⟨11768975, by rfl⟩ : syracuseStep 15691967 = 23537951) B23537951
theorem B1225455 : Blo 1224430 1225455 := bstep (se 1 (by rfl) ⟨919091, by rfl⟩ : syracuseStep 1225455 = 1838183) B1838183
theorem B1225695 : Blo 1224430 1225695 := bstep (se 1 (by rfl) ⟨919271, by rfl⟩ : syracuseStep 1225695 = 1838543) B1838543
theorem B2618335 : Blo 1224430 2618335 := bstep (se 1 (by rfl) ⟨1963751, by rfl⟩ : syracuseStep 2618335 = 3927503) B3927503
theorem B1226143 : Blo 1224430 1226143 := bstep (se 1 (by rfl) ⟨919607, by rfl⟩ : syracuseStep 1226143 = 1839215) B1839215
theorem B2759399 : Blo 1224430 2759399 := bstep (se 1 (by rfl) ⟨2069549, by rfl⟩ : syracuseStep 2759399 = 4139099) B4139099
theorem B7855339 : Blo 1224430 7855339 := bstep (se 1 (by rfl) ⟨5891504, by rfl⟩ : syracuseStep 7855339 = 11783009) B11783009
theorem B6290731 : Blo 1224430 6290731 := bstep (se 1 (by rfl) ⟨4718048, by rfl⟩ : syracuseStep 6290731 = 9436097) B9436097
theorem B10461311 : Blo 1224430 10461311 := bstep (se 1 (by rfl) ⟨7845983, by rfl⟩ : syracuseStep 10461311 = 15691967) B15691967
theorem B71631053 : Blo 1224430 71631053 := bstep (se 3 (by rfl) ⟨13430822, by rfl⟩ : syracuseStep 71631053 = 26861645) B26861645
theorem B3491113 : Blo 1224430 3491113 := bstep (se 2 (by rfl) ⟨1309167, by rfl⟩ : syracuseStep 3491113 = 2618335) B2618335
theorem B6546761 : Blo 1224430 6546761 := bstep (se 2 (by rfl) ⟨2455035, by rfl⟩ : syracuseStep 6546761 = 4910071) B4910071
theorem B67045067 : Blo 1224430 67045067 := bstep (se 1 (by rfl) ⟨50283800, by rfl⟩ : syracuseStep 67045067 = 100567601) B100567601
theorem B9930599 : Blo 1224430 9930599 := bstep (se 1 (by rfl) ⟨7447949, by rfl⟩ : syracuseStep 9930599 = 14895899) B14895899
theorem B25495505 : Blo 1224430 25495505 := bstep (se 2 (by rfl) ⟨9560814, by rfl⟩ : syracuseStep 25495505 = 19121629) B19121629
theorem B1837961 : Blo 1224430 1837961 := bstep (se 2 (by rfl) ⟨689235, by rfl⟩ : syracuseStep 1837961 = 1378471) B1378471
theorem B1224703 : Blo 1224430 1224703 := bstep (se 1 (by rfl) ⟨918527, by rfl⟩ : syracuseStep 1224703 = 1837055) B1837055
theorem B3928247 : Blo 1224430 3928247 := bstep (se 1 (by rfl) ⟨2946185, by rfl⟩ : syracuseStep 3928247 = 5892371) B5892371
theorem B4649183 : Blo 1224430 4649183 := bstep (se 1 (by rfl) ⟨3486887, by rfl⟩ : syracuseStep 4649183 = 6973775) B6973775
theorem B10473785 : Blo 1224430 10473785 := bstep (se 2 (by rfl) ⟨3927669, by rfl⟩ : syracuseStep 10473785 = 7855339) B7855339
theorem B1839599 : Blo 1224430 1839599 := bstep (se 1 (by rfl) ⟨1379699, by rfl⟩ : syracuseStep 1839599 = 2759399) B2759399
theorem B4133753 : Blo 1224430 4133753 := bstep (se 2 (by rfl) ⟨1550157, by rfl⟩ : syracuseStep 4133753 = 3100315) B3100315
theorem B1225831 : Blo 1224430 1225831 := bstep (se 1 (by rfl) ⟨919373, by rfl⟩ : syracuseStep 1225831 = 1838747) B1838747
theorem B1225967 : Blo 1224430 1225967 := bstep (se 1 (by rfl) ⟨919475, by rfl⟩ : syracuseStep 1225967 = 1838951) B1838951
theorem B10343987 : Blo 1224430 10343987 := bstep (se 1 (by rfl) ⟨7757990, by rfl⟩ : syracuseStep 10343987 = 15515981) B15515981
theorem B4135643 : Blo 1224430 4135643 := bstep (se 1 (by rfl) ⟨3101732, by rfl⟩ : syracuseStep 4135643 = 6203465) B6203465
theorem B8387641 : Blo 1224430 8387641 := bstep (se 2 (by rfl) ⟨3145365, by rfl⟩ : syracuseStep 8387641 = 6290731) B6290731
theorem B44696711 : Blo 1224430 44696711 := bstep (se 1 (by rfl) ⟨33522533, by rfl⟩ : syracuseStep 44696711 = 67045067) B67045067
theorem B6620399 : Blo 1224430 6620399 := bstep (se 1 (by rfl) ⟨4965299, by rfl⟩ : syracuseStep 6620399 = 9930599) B9930599
theorem B11183521 : Blo 1224430 11183521 := bstep (se 2 (by rfl) ⟨4193820, by rfl⟩ : syracuseStep 11183521 = 8387641) B8387641
theorem B4654817 : Blo 1224430 4654817 := bstep (se 2 (by rfl) ⟨1745556, by rfl⟩ : syracuseStep 4654817 = 3491113) B3491113
theorem B6974207 : Blo 1224430 6974207 := bstep (se 1 (by rfl) ⟨5230655, by rfl⟩ : syracuseStep 6974207 = 10461311) B10461311
theorem B47754035 : Blo 1224430 47754035 := bstep (se 1 (by rfl) ⟨35815526, by rfl⟩ : syracuseStep 47754035 = 71631053) B71631053
theorem B3099455 : Blo 1224430 3099455 := bstep (se 1 (by rfl) ⟨2324591, by rfl⟩ : syracuseStep 3099455 = 4649183) B4649183
theorem B6982523 : Blo 1224430 6982523 := bstep (se 1 (by rfl) ⟨5236892, by rfl⟩ : syracuseStep 6982523 = 10473785) B10473785
theorem B2755835 : Blo 1224430 2755835 := bstep (se 1 (by rfl) ⟨2066876, by rfl⟩ : syracuseStep 2755835 = 4133753) B4133753
theorem B2757095 : Blo 1224430 2757095 := bstep (se 1 (by rfl) ⟨2067821, by rfl⟩ : syracuseStep 2757095 = 4135643) B4135643
theorem B1225307 : Blo 1224430 1225307 := bstep (se 1 (by rfl) ⟨918980, by rfl⟩ : syracuseStep 1225307 = 1837961) B1837961
theorem B2618831 : Blo 1224430 2618831 := bstep (se 1 (by rfl) ⟨1964123, by rfl⟩ : syracuseStep 2618831 = 3928247) B3928247
theorem B1226399 : Blo 1224430 1226399 := bstep (se 1 (by rfl) ⟨919799, by rfl⟩ : syracuseStep 1226399 = 1839599) B1839599
theorem B4364507 : Blo 1224430 4364507 := bstep (se 1 (by rfl) ⟨3273380, by rfl⟩ : syracuseStep 4364507 = 6546761) B6546761
theorem B6895991 : Blo 1224430 6895991 := bstep (se 1 (by rfl) ⟨5171993, by rfl⟩ : syracuseStep 6895991 = 10343987) B10343987
theorem B16997003 : Blo 1224430 16997003 := bstep (se 1 (by rfl) ⟨12747752, by rfl⟩ : syracuseStep 16997003 = 25495505) B25495505
theorem B1745887 : Blo 1224430 1745887 := bstep (se 1 (by rfl) ⟨1309415, by rfl⟩ : syracuseStep 1745887 = 2618831) B2618831
theorem B4597327 : Blo 1224430 4597327 := bstep (se 1 (by rfl) ⟨3447995, by rfl⟩ : syracuseStep 4597327 = 6895991) B6895991
theorem B11331335 : Blo 1224430 11331335 := bstep (se 1 (by rfl) ⟨8498501, by rfl⟩ : syracuseStep 11331335 = 16997003) B16997003
theorem B31836023 : Blo 1224430 31836023 := bstep (se 1 (by rfl) ⟨23877017, by rfl⟩ : syracuseStep 31836023 = 47754035) B47754035
theorem B2066303 : Blo 1224430 2066303 := bstep (se 1 (by rfl) ⟨1549727, by rfl⟩ : syracuseStep 2066303 = 3099455) B3099455
theorem B14911361 : Blo 1224430 14911361 := bstep (se 2 (by rfl) ⟨5591760, by rfl⟩ : syracuseStep 14911361 = 11183521) B11183521
theorem B4655015 : Blo 1224430 4655015 := bstep (se 1 (by rfl) ⟨3491261, by rfl⟩ : syracuseStep 4655015 = 6982523) B6982523
theorem B1837223 : Blo 1224430 1837223 := bstep (se 1 (by rfl) ⟨1377917, by rfl⟩ : syracuseStep 1837223 = 2755835) B2755835
theorem B1838063 : Blo 1224430 1838063 := bstep (se 1 (by rfl) ⟨1378547, by rfl⟩ : syracuseStep 1838063 = 2757095) B2757095
theorem B29797807 : Blo 1224430 29797807 := bstep (se 1 (by rfl) ⟨22348355, by rfl⟩ : syracuseStep 29797807 = 44696711) B44696711
theorem B4649471 : Blo 1224430 4649471 := bstep (se 1 (by rfl) ⟨3487103, by rfl⟩ : syracuseStep 4649471 = 6974207) B6974207
theorem B11638685 : Blo 1224430 11638685 := bstep (se 3 (by rfl) ⟨2182253, by rfl⟩ : syracuseStep 11638685 = 4364507) B4364507
theorem B4413599 : Blo 1224430 4413599 := bstep (se 1 (by rfl) ⟨3310199, by rfl⟩ : syracuseStep 4413599 = 6620399) B6620399
theorem B3103211 : Blo 1224430 3103211 := bstep (se 1 (by rfl) ⟨2327408, by rfl⟩ : syracuseStep 3103211 = 4654817) B4654817
theorem B7554223 : Blo 1224430 7554223 := bstep (se 1 (by rfl) ⟨5665667, by rfl⟩ : syracuseStep 7554223 = 11331335) B11331335
theorem B1377535 : Blo 1224430 1377535 := bstep (se 1 (by rfl) ⟨1033151, by rfl⟩ : syracuseStep 1377535 = 2066303) B2066303
theorem B7759123 : Blo 1224430 7759123 := bstep (se 1 (by rfl) ⟨5819342, by rfl⟩ : syracuseStep 7759123 = 11638685) B11638685
theorem B2327849 : Blo 1224430 2327849 := bstep (se 2 (by rfl) ⟨872943, by rfl⟩ : syracuseStep 2327849 = 1745887) B1745887
theorem B2942399 : Blo 1224430 2942399 := bstep (se 1 (by rfl) ⟨2206799, by rfl⟩ : syracuseStep 2942399 = 4413599) B4413599
theorem B6129769 : Blo 1224430 6129769 := bstep (se 2 (by rfl) ⟨2298663, by rfl⟩ : syracuseStep 6129769 = 4597327) B4597327
theorem B3099647 : Blo 1224430 3099647 := bstep (se 1 (by rfl) ⟨2324735, by rfl⟩ : syracuseStep 3099647 = 4649471) B4649471
theorem B9940907 : Blo 1224430 9940907 := bstep (se 1 (by rfl) ⟨7455680, by rfl⟩ : syracuseStep 9940907 = 14911361) B14911361
theorem B1224815 : Blo 1224430 1224815 := bstep (se 1 (by rfl) ⟨918611, by rfl⟩ : syracuseStep 1224815 = 1837223) B1837223
theorem B2068807 : Blo 1224430 2068807 := bstep (se 1 (by rfl) ⟨1551605, by rfl⟩ : syracuseStep 2068807 = 3103211) B3103211
theorem B1225375 : Blo 1224430 1225375 := bstep (se 1 (by rfl) ⟨919031, by rfl⟩ : syracuseStep 1225375 = 1838063) B1838063
theorem B21224015 : Blo 1224430 21224015 := bstep (se 1 (by rfl) ⟨15918011, by rfl⟩ : syracuseStep 21224015 = 31836023) B31836023
theorem B3103343 : Blo 1224430 3103343 := bstep (se 1 (by rfl) ⟨2327507, by rfl⟩ : syracuseStep 3103343 = 4655015) B4655015
theorem B39730409 : Blo 1224430 39730409 := bstep (se 2 (by rfl) ⟨14898903, by rfl⟩ : syracuseStep 39730409 = 29797807) B29797807
theorem B1836713 : Blo 1224430 1836713 := bstep (se 2 (by rfl) ⟨688767, by rfl⟩ : syracuseStep 1836713 = 1377535) B1377535
theorem B14149343 : Blo 1224430 14149343 := bstep (se 1 (by rfl) ⟨10612007, by rfl⟩ : syracuseStep 14149343 = 21224015) B21224015
theorem B2066431 : Blo 1224430 2066431 := bstep (se 1 (by rfl) ⟨1549823, by rfl⟩ : syracuseStep 2066431 = 3099647) B3099647
theorem B26486939 : Blo 1224430 26486939 := bstep (se 1 (by rfl) ⟨19865204, by rfl⟩ : syracuseStep 26486939 = 39730409) B39730409
theorem B1551899 : Blo 1224430 1551899 := bstep (se 1 (by rfl) ⟨1163924, by rfl⟩ : syracuseStep 1551899 = 2327849) B2327849
theorem B1961599 : Blo 1224430 1961599 := bstep (se 1 (by rfl) ⟨1471199, by rfl⟩ : syracuseStep 1961599 = 2942399) B2942399
theorem B41381989 : Blo 1224430 41381989 := bstep (se 4 (by rfl) ⟨3879561, by rfl⟩ : syracuseStep 41381989 = 7759123) B7759123
theorem B10072297 : Blo 1224430 10072297 := bstep (se 2 (by rfl) ⟨3777111, by rfl⟩ : syracuseStep 10072297 = 7554223) B7554223
theorem B2068895 : Blo 1224430 2068895 := bstep (se 1 (by rfl) ⟨1551671, by rfl⟩ : syracuseStep 2068895 = 3103343) B3103343
theorem B8173025 : Blo 1224430 8173025 := bstep (se 2 (by rfl) ⟨3064884, by rfl⟩ : syracuseStep 8173025 = 6129769) B6129769
theorem B2758409 : Blo 1224430 2758409 := bstep (se 2 (by rfl) ⟨1034403, by rfl⟩ : syracuseStep 2758409 = 2068807) B2068807
theorem B6627271 : Blo 1224430 6627271 := bstep (se 1 (by rfl) ⟨4970453, by rfl⟩ : syracuseStep 6627271 = 9940907) B9940907
theorem B5448683 : Blo 1224430 5448683 := bstep (se 1 (by rfl) ⟨4086512, by rfl⟩ : syracuseStep 5448683 = 8173025) B8173025
theorem B4138397 : Blo 1224430 4138397 := bstep (se 3 (by rfl) ⟨775949, by rfl⟩ : syracuseStep 4138397 = 1551899) B1551899
theorem B2615465 : Blo 1224430 2615465 := bstep (se 2 (by rfl) ⟨980799, by rfl⟩ : syracuseStep 2615465 = 1961599) B1961599
theorem B2755241 : Blo 1224430 2755241 := bstep (se 2 (by rfl) ⟨1033215, by rfl⟩ : syracuseStep 2755241 = 2066431) B2066431
theorem B1379263 : Blo 1224430 1379263 := bstep (se 1 (by rfl) ⟨1034447, by rfl⟩ : syracuseStep 1379263 = 2068895) B2068895
theorem B13429729 : Blo 1224430 13429729 := bstep (se 2 (by rfl) ⟨5036148, by rfl⟩ : syracuseStep 13429729 = 10072297) B10072297
theorem B1224475 : Blo 1224430 1224475 := bstep (se 1 (by rfl) ⟨918356, by rfl⟩ : syracuseStep 1224475 = 1836713) B1836713
theorem B9432895 : Blo 1224430 9432895 := bstep (se 1 (by rfl) ⟨7074671, by rfl⟩ : syracuseStep 9432895 = 14149343) B14149343
theorem B1838939 : Blo 1224430 1838939 := bstep (se 1 (by rfl) ⟨1379204, by rfl⟩ : syracuseStep 1838939 = 2758409) B2758409
theorem B17657959 : Blo 1224430 17657959 := bstep (se 1 (by rfl) ⟨13243469, by rfl⟩ : syracuseStep 17657959 = 26486939) B26486939
theorem B882815765 : Blo 1224430 882815765 := bstep (se 6 (by rfl) ⟨20690994, by rfl⟩ : syracuseStep 882815765 = 41381989) B41381989
theorem B8836361 : Blo 1224430 8836361 := bstep (se 2 (by rfl) ⟨3313635, by rfl⟩ : syracuseStep 8836361 = 6627271) B6627271
theorem B23543945 : Blo 1224430 23543945 := bstep (se 2 (by rfl) ⟨8828979, by rfl⟩ : syracuseStep 23543945 = 17657959) B17657959
theorem B5890907 : Blo 1224430 5890907 := bstep (se 1 (by rfl) ⟨4418180, by rfl⟩ : syracuseStep 5890907 = 8836361) B8836361
theorem B1836827 : Blo 1224430 1836827 := bstep (se 1 (by rfl) ⟨1377620, by rfl⟩ : syracuseStep 1836827 = 2755241) B2755241
theorem B12577193 : Blo 1224430 12577193 := bstep (se 2 (by rfl) ⟨4716447, by rfl⟩ : syracuseStep 12577193 = 9432895) B9432895
theorem B71625221 : Blo 1224430 71625221 := bstep (se 4 (by rfl) ⟨6714864, by rfl⟩ : syracuseStep 71625221 = 13429729) B13429729
theorem B3632455 : Blo 1224430 3632455 := bstep (se 1 (by rfl) ⟨2724341, by rfl⟩ : syracuseStep 3632455 = 5448683) B5448683
theorem B1839017 : Blo 1224430 1839017 := bstep (se 2 (by rfl) ⟨689631, by rfl⟩ : syracuseStep 1839017 = 1379263) B1379263
theorem B1225959 : Blo 1224430 1225959 := bstep (se 1 (by rfl) ⟨919469, by rfl⟩ : syracuseStep 1225959 = 1838939) B1838939
theorem B2758931 : Blo 1224430 2758931 := bstep (se 1 (by rfl) ⟨2069198, by rfl⟩ : syracuseStep 2758931 = 4138397) B4138397
theorem B1743643 : Blo 1224430 1743643 := bstep (se 1 (by rfl) ⟨1307732, by rfl⟩ : syracuseStep 1743643 = 2615465) B2615465
theorem B2354175373 : Blo 1224430 2354175373 := bstep (se 3 (by rfl) ⟨441407882, by rfl⟩ : syracuseStep 2354175373 = 882815765) B882815765
theorem B15695963 : Blo 1224430 15695963 := bstep (se 1 (by rfl) ⟨11771972, by rfl⟩ : syracuseStep 15695963 = 23543945) B23543945
theorem B4843273 : Blo 1224430 4843273 := bstep (se 2 (by rfl) ⟨1816227, by rfl⟩ : syracuseStep 4843273 = 3632455) B3632455
theorem B1224551 : Blo 1224430 1224551 := bstep (se 1 (by rfl) ⟨918413, by rfl⟩ : syracuseStep 1224551 = 1836827) B1836827
theorem B1839287 : Blo 1224430 1839287 := bstep (se 1 (by rfl) ⟨1379465, by rfl⟩ : syracuseStep 1839287 = 2758931) B2758931
theorem B8384795 : Blo 1224430 8384795 := bstep (se 1 (by rfl) ⟨6288596, by rfl⟩ : syracuseStep 8384795 = 12577193) B12577193
theorem B3138900497 : Blo 1224430 3138900497 := bstep (se 2 (by rfl) ⟨1177087686, by rfl⟩ : syracuseStep 3138900497 = 2354175373) B2354175373
theorem B15709085 : Blo 1224430 15709085 := bstep (se 3 (by rfl) ⟨2945453, by rfl⟩ : syracuseStep 15709085 = 5890907) B5890907
theorem B1226011 : Blo 1224430 1226011 := bstep (se 1 (by rfl) ⟨919508, by rfl⟩ : syracuseStep 1226011 = 1839017) B1839017
theorem B2324857 : Blo 1224430 2324857 := bstep (se 2 (by rfl) ⟨871821, by rfl⟩ : syracuseStep 2324857 = 1743643) B1743643
theorem B47750147 : Blo 1224430 47750147 := bstep (se 1 (by rfl) ⟨35812610, by rfl⟩ : syracuseStep 47750147 = 71625221) B71625221
theorem B6457697 : Blo 1224430 6457697 := bstep (se 2 (by rfl) ⟨2421636, by rfl⟩ : syracuseStep 6457697 = 4843273) B4843273
theorem B10463975 : Blo 1224430 10463975 := bstep (se 1 (by rfl) ⟨7847981, by rfl⟩ : syracuseStep 10463975 = 15695963) B15695963
theorem B5589863 : Blo 1224430 5589863 := bstep (se 1 (by rfl) ⟨4192397, by rfl⟩ : syracuseStep 5589863 = 8384795) B8384795
theorem B2092600331 : Blo 1224430 2092600331 := bstep (se 1 (by rfl) ⟨1569450248, by rfl⟩ : syracuseStep 2092600331 = 3138900497) B3138900497
theorem B3099809 : Blo 1224430 3099809 := bstep (se 2 (by rfl) ⟨1162428, by rfl⟩ : syracuseStep 3099809 = 2324857) B2324857
theorem B10472723 : Blo 1224430 10472723 := bstep (se 1 (by rfl) ⟨7854542, by rfl⟩ : syracuseStep 10472723 = 15709085) B15709085
theorem B1226191 : Blo 1224430 1226191 := bstep (se 1 (by rfl) ⟨919643, by rfl⟩ : syracuseStep 1226191 = 1839287) B1839287
theorem B31833431 : Blo 1224430 31833431 := bstep (se 1 (by rfl) ⟨23875073, by rfl⟩ : syracuseStep 31833431 = 47750147) B47750147
theorem B1395066887 : Blo 1224430 1395066887 := bstep (se 1 (by rfl) ⟨1046300165, by rfl⟩ : syracuseStep 1395066887 = 2092600331) B2092600331
theorem B2066539 : Blo 1224430 2066539 := bstep (se 1 (by rfl) ⟨1549904, by rfl⟩ : syracuseStep 2066539 = 3099809) B3099809
theorem B6981815 : Blo 1224430 6981815 := bstep (se 1 (by rfl) ⟨5236361, by rfl⟩ : syracuseStep 6981815 = 10472723) B10472723
theorem B4305131 : Blo 1224430 4305131 := bstep (se 1 (by rfl) ⟨3228848, by rfl⟩ : syracuseStep 4305131 = 6457697) B6457697
theorem B6975983 : Blo 1224430 6975983 := bstep (se 1 (by rfl) ⟨5231987, by rfl⟩ : syracuseStep 6975983 = 10463975) B10463975
theorem B21222287 : Blo 1224430 21222287 := bstep (se 1 (by rfl) ⟨15916715, by rfl⟩ : syracuseStep 21222287 = 31833431) B31833431
theorem B3726575 : Blo 1224430 3726575 := bstep (se 1 (by rfl) ⟨2794931, by rfl⟩ : syracuseStep 3726575 = 5589863) B5589863
theorem B14148191 : Blo 1224430 14148191 := bstep (se 1 (by rfl) ⟨10611143, by rfl⟩ : syracuseStep 14148191 = 21222287) B21222287
theorem B4654543 : Blo 1224430 4654543 := bstep (se 1 (by rfl) ⟨3490907, by rfl⟩ : syracuseStep 4654543 = 6981815) B6981815
theorem B2484383 : Blo 1224430 2484383 := bstep (se 1 (by rfl) ⟨1863287, by rfl⟩ : syracuseStep 2484383 = 3726575) B3726575
theorem B2755385 : Blo 1224430 2755385 := bstep (se 2 (by rfl) ⟨1033269, by rfl⟩ : syracuseStep 2755385 = 2066539) B2066539
theorem B2870087 : Blo 1224430 2870087 := bstep (se 1 (by rfl) ⟨2152565, by rfl⟩ : syracuseStep 2870087 = 4305131) B4305131
theorem B4650655 : Blo 1224430 4650655 := bstep (se 1 (by rfl) ⟨3487991, by rfl⟩ : syracuseStep 4650655 = 6975983) B6975983
theorem B930044591 : Blo 1224430 930044591 := bstep (se 1 (by rfl) ⟨697533443, by rfl⟩ : syracuseStep 930044591 = 1395066887) B1395066887
theorem B620029727 : Blo 1224430 620029727 := bstep (se 1 (by rfl) ⟨465022295, by rfl⟩ : syracuseStep 620029727 = 930044591) B930044591
theorem B1836923 : Blo 1224430 1836923 := bstep (se 1 (by rfl) ⟨1377692, by rfl⟩ : syracuseStep 1836923 = 2755385) B2755385
theorem B7653565 : Blo 1224430 7653565 := bstep (se 3 (by rfl) ⟨1435043, by rfl⟩ : syracuseStep 7653565 = 2870087) B2870087
theorem B9432127 : Blo 1224430 9432127 := bstep (se 1 (by rfl) ⟨7074095, by rfl⟩ : syracuseStep 9432127 = 14148191) B14148191
theorem B6206057 : Blo 1224430 6206057 := bstep (se 2 (by rfl) ⟨2327271, by rfl⟩ : syracuseStep 6206057 = 4654543) B4654543
theorem B26500085 : Blo 1224430 26500085 := bstep (se 5 (by rfl) ⟨1242191, by rfl⟩ : syracuseStep 26500085 = 2484383) B2484383
theorem B6200873 : Blo 1224430 6200873 := bstep (se 2 (by rfl) ⟨2325327, by rfl⟩ : syracuseStep 6200873 = 4650655) B4650655
theorem B4137371 : Blo 1224430 4137371 := bstep (se 1 (by rfl) ⟨3103028, by rfl⟩ : syracuseStep 4137371 = 6206057) B6206057
theorem B413353151 : Blo 1224430 413353151 := bstep (se 1 (by rfl) ⟨310014863, by rfl⟩ : syracuseStep 413353151 = 620029727) B620029727
theorem B12576169 : Blo 1224430 12576169 := bstep (se 2 (by rfl) ⟨4716063, by rfl⟩ : syracuseStep 12576169 = 9432127) B9432127
theorem B1224615 : Blo 1224430 1224615 := bstep (se 1 (by rfl) ⟨918461, by rfl⟩ : syracuseStep 1224615 = 1836923) B1836923
theorem B17666723 : Blo 1224430 17666723 := bstep (se 1 (by rfl) ⟨13250042, by rfl⟩ : syracuseStep 17666723 = 26500085) B26500085
theorem B4133915 : Blo 1224430 4133915 := bstep (se 1 (by rfl) ⟨3100436, by rfl⟩ : syracuseStep 4133915 = 6200873) B6200873
theorem B10204753 : Blo 1224430 10204753 := bstep (se 2 (by rfl) ⟨3826782, by rfl⟩ : syracuseStep 10204753 = 7653565) B7653565
theorem B2755943 : Blo 1224430 2755943 := bstep (se 1 (by rfl) ⟨2066957, by rfl⟩ : syracuseStep 2755943 = 4133915) B4133915
theorem B2758247 : Blo 1224430 2758247 := bstep (se 1 (by rfl) ⟨2068685, by rfl⟩ : syracuseStep 2758247 = 4137371) B4137371
theorem B11777815 : Blo 1224430 11777815 := bstep (se 1 (by rfl) ⟨8833361, by rfl⟩ : syracuseStep 11777815 = 17666723) B17666723
theorem B275568767 : Blo 1224430 275568767 := bstep (se 1 (by rfl) ⟨206676575, by rfl⟩ : syracuseStep 275568767 = 413353151) B413353151
theorem B16768225 : Blo 1224430 16768225 := bstep (se 2 (by rfl) ⟨6288084, by rfl⟩ : syracuseStep 16768225 = 12576169) B12576169
theorem B13606337 : Blo 1224430 13606337 := bstep (se 2 (by rfl) ⟨5102376, by rfl⟩ : syracuseStep 13606337 = 10204753) B10204753
theorem B36283565 : Blo 1224430 36283565 := bstep (se 3 (by rfl) ⟨6803168, by rfl⟩ : syracuseStep 36283565 = 13606337) B13606337
theorem B22357633 : Blo 1224430 22357633 := bstep (se 2 (by rfl) ⟨8384112, by rfl⟩ : syracuseStep 22357633 = 16768225) B16768225
theorem B1837295 : Blo 1224430 1837295 := bstep (se 1 (by rfl) ⟨1377971, by rfl⟩ : syracuseStep 1837295 = 2755943) B2755943
theorem B1838831 : Blo 1224430 1838831 := bstep (se 1 (by rfl) ⟨1379123, by rfl⟩ : syracuseStep 1838831 = 2758247) B2758247
theorem B183712511 : Blo 1224430 183712511 := bstep (se 1 (by rfl) ⟨137784383, by rfl⟩ : syracuseStep 183712511 = 275568767) B275568767
theorem B15703753 : Blo 1224430 15703753 := bstep (se 2 (by rfl) ⟨5888907, by rfl⟩ : syracuseStep 15703753 = 11777815) B11777815
theorem B1224863 : Blo 1224430 1224863 := bstep (se 1 (by rfl) ⟨918647, by rfl⟩ : syracuseStep 1224863 = 1837295) B1837295
theorem B122475007 : Blo 1224430 122475007 := bstep (se 1 (by rfl) ⟨91856255, by rfl⟩ : syracuseStep 122475007 = 183712511) B183712511
theorem B1225887 : Blo 1224430 1225887 := bstep (se 1 (by rfl) ⟨919415, by rfl⟩ : syracuseStep 1225887 = 1838831) B1838831
theorem B24189043 : Blo 1224430 24189043 := bstep (se 1 (by rfl) ⟨18141782, by rfl⟩ : syracuseStep 24189043 = 36283565) B36283565
theorem B29810177 : Blo 1224430 29810177 := bstep (se 2 (by rfl) ⟨11178816, by rfl⟩ : syracuseStep 29810177 = 22357633) B22357633
theorem B20938337 : Blo 1224430 20938337 := bstep (se 2 (by rfl) ⟨7851876, by rfl⟩ : syracuseStep 20938337 = 15703753) B15703753
theorem B32252057 : Blo 1224430 32252057 := bstep (se 2 (by rfl) ⟨12094521, by rfl⟩ : syracuseStep 32252057 = 24189043) B24189043
theorem B653200037 : Blo 1224430 653200037 := bstep (se 4 (by rfl) ⟨61237503, by rfl⟩ : syracuseStep 653200037 = 122475007) B122475007
theorem B19873451 : Blo 1224430 19873451 := bstep (se 1 (by rfl) ⟨14905088, by rfl⟩ : syracuseStep 19873451 = 29810177) B29810177
theorem B13958891 : Blo 1224430 13958891 := bstep (se 1 (by rfl) ⟨10469168, by rfl⟩ : syracuseStep 13958891 = 20938337) B20938337
theorem B13248967 : Blo 1224430 13248967 := bstep (se 1 (by rfl) ⟨9936725, by rfl⟩ : syracuseStep 13248967 = 19873451) B19873451
theorem B435466691 : Blo 1224430 435466691 := bstep (se 1 (by rfl) ⟨326600018, by rfl⟩ : syracuseStep 435466691 = 653200037) B653200037
theorem B21501371 : Blo 1224430 21501371 := bstep (se 1 (by rfl) ⟨16126028, by rfl⟩ : syracuseStep 21501371 = 32252057) B32252057
theorem B9305927 : Blo 1224430 9305927 := bstep (se 1 (by rfl) ⟨6979445, by rfl⟩ : syracuseStep 9305927 = 13958891) B13958891
theorem B57336989 : Blo 1224430 57336989 := bstep (se 3 (by rfl) ⟨10750685, by rfl⟩ : syracuseStep 57336989 = 21501371) B21501371
theorem B6203951 : Blo 1224430 6203951 := bstep (se 1 (by rfl) ⟨4652963, by rfl⟩ : syracuseStep 6203951 = 9305927) B9305927
theorem B290311127 : Blo 1224430 290311127 := bstep (se 1 (by rfl) ⟨217733345, by rfl⟩ : syracuseStep 290311127 = 435466691) B435466691
theorem B17665289 : Blo 1224430 17665289 := bstep (se 2 (by rfl) ⟨6624483, by rfl⟩ : syracuseStep 17665289 = 13248967) B13248967
theorem B152898637 : Blo 1224430 152898637 := bstep (se 3 (by rfl) ⟨28668494, by rfl⟩ : syracuseStep 152898637 = 57336989) B57336989
theorem B193540751 : Blo 1224430 193540751 := bstep (se 1 (by rfl) ⟨145155563, by rfl⟩ : syracuseStep 193540751 = 290311127) B290311127
theorem B11776859 : Blo 1224430 11776859 := bstep (se 1 (by rfl) ⟨8832644, by rfl⟩ : syracuseStep 11776859 = 17665289) B17665289
theorem B4135967 : Blo 1224430 4135967 := bstep (se 1 (by rfl) ⟨3101975, by rfl⟩ : syracuseStep 4135967 = 6203951) B6203951
theorem B129027167 : Blo 1224430 129027167 := bstep (se 1 (by rfl) ⟨96770375, by rfl⟩ : syracuseStep 129027167 = 193540751) B193540751
theorem B7851239 : Blo 1224430 7851239 := bstep (se 1 (by rfl) ⟨5888429, by rfl⟩ : syracuseStep 7851239 = 11776859) B11776859
theorem B2757311 : Blo 1224430 2757311 := bstep (se 1 (by rfl) ⟨2067983, by rfl⟩ : syracuseStep 2757311 = 4135967) B4135967
theorem B203864849 : Blo 1224430 203864849 := bstep (se 2 (by rfl) ⟨76449318, by rfl⟩ : syracuseStep 203864849 = 152898637) B152898637
theorem B86018111 : Blo 1224430 86018111 := bstep (se 1 (by rfl) ⟨64513583, by rfl⟩ : syracuseStep 86018111 = 129027167) B129027167
theorem B1838207 : Blo 1224430 1838207 := bstep (se 1 (by rfl) ⟨1378655, by rfl⟩ : syracuseStep 1838207 = 2757311) B2757311
theorem B135909899 : Blo 1224430 135909899 := bstep (se 1 (by rfl) ⟨101932424, by rfl⟩ : syracuseStep 135909899 = 203864849) B203864849
theorem B5234159 : Blo 1224430 5234159 := bstep (se 1 (by rfl) ⟨3925619, by rfl⟩ : syracuseStep 5234159 = 7851239) B7851239
theorem B57345407 : Blo 1224430 57345407 := bstep (se 1 (by rfl) ⟨43009055, by rfl⟩ : syracuseStep 57345407 = 86018111) B86018111
theorem B90606599 : Blo 1224430 90606599 := bstep (se 1 (by rfl) ⟨67954949, by rfl⟩ : syracuseStep 90606599 = 135909899) B135909899
theorem B1225471 : Blo 1224430 1225471 := bstep (se 1 (by rfl) ⟨919103, by rfl⟩ : syracuseStep 1225471 = 1838207) B1838207
theorem B3489439 : Blo 1224430 3489439 := bstep (se 1 (by rfl) ⟨2617079, by rfl⟩ : syracuseStep 3489439 = 5234159) B5234159
theorem B60404399 : Blo 1224430 60404399 := bstep (se 1 (by rfl) ⟨45303299, by rfl⟩ : syracuseStep 60404399 = 90606599) B90606599
theorem B38230271 : Blo 1224430 38230271 := bstep (se 1 (by rfl) ⟨28672703, by rfl⟩ : syracuseStep 38230271 = 57345407) B57345407
theorem B4652585 : Blo 1224430 4652585 := bstep (se 2 (by rfl) ⟨1744719, by rfl⟩ : syracuseStep 4652585 = 3489439) B3489439
theorem B25486847 : Blo 1224430 25486847 := bstep (se 1 (by rfl) ⟨19115135, by rfl⟩ : syracuseStep 25486847 = 38230271) B38230271
theorem B3101723 : Blo 1224430 3101723 := bstep (se 1 (by rfl) ⟨2326292, by rfl⟩ : syracuseStep 3101723 = 4652585) B4652585
theorem B40269599 : Blo 1224430 40269599 := bstep (se 1 (by rfl) ⟨30202199, by rfl⟩ : syracuseStep 40269599 = 60404399) B60404399
theorem B16991231 : Blo 1224430 16991231 := bstep (se 1 (by rfl) ⟨12743423, by rfl⟩ : syracuseStep 16991231 = 25486847) B25486847
theorem B26846399 : Blo 1224430 26846399 := bstep (se 1 (by rfl) ⟨20134799, by rfl⟩ : syracuseStep 26846399 = 40269599) B40269599
theorem B2067815 : Blo 1224430 2067815 := bstep (se 1 (by rfl) ⟨1550861, by rfl⟩ : syracuseStep 2067815 = 3101723) B3101723
theorem B71590397 : Blo 1224430 71590397 := bstep (se 3 (by rfl) ⟨13423199, by rfl⟩ : syracuseStep 71590397 = 26846399) B26846399
theorem B1378543 : Blo 1224430 1378543 := bstep (se 1 (by rfl) ⟨1033907, by rfl⟩ : syracuseStep 1378543 = 2067815) B2067815
theorem B45309949 : Blo 1224430 45309949 := bstep (se 3 (by rfl) ⟨8495615, by rfl⟩ : syracuseStep 45309949 = 16991231) B16991231
theorem B190907725 : Blo 1224430 190907725 := bstep (se 3 (by rfl) ⟨35795198, by rfl⟩ : syracuseStep 190907725 = 71590397) B71590397
theorem B1838057 : Blo 1224430 1838057 := bstep (se 2 (by rfl) ⟨689271, by rfl⟩ : syracuseStep 1838057 = 1378543) B1378543
theorem B241653061 : Blo 1224430 241653061 := bstep (se 4 (by rfl) ⟨22654974, by rfl⟩ : syracuseStep 241653061 = 45309949) B45309949
theorem B254543633 : Blo 1224430 254543633 := bstep (se 2 (by rfl) ⟨95453862, by rfl⟩ : syracuseStep 254543633 = 190907725) B190907725
theorem B322204081 : Blo 1224430 322204081 := bstep (se 2 (by rfl) ⟨120826530, by rfl⟩ : syracuseStep 322204081 = 241653061) B241653061
theorem B1225371 : Blo 1224430 1225371 := bstep (se 1 (by rfl) ⟨919028, by rfl⟩ : syracuseStep 1225371 = 1838057) B1838057
theorem B429605441 : Blo 1224430 429605441 := bstep (se 2 (by rfl) ⟨161102040, by rfl⟩ : syracuseStep 429605441 = 322204081) B322204081
theorem B169695755 : Blo 1224430 169695755 := bstep (se 1 (by rfl) ⟨127271816, by rfl⟩ : syracuseStep 169695755 = 254543633) B254543633
theorem B286403627 : Blo 1224430 286403627 := bstep (se 1 (by rfl) ⟨214802720, by rfl⟩ : syracuseStep 286403627 = 429605441) B429605441
theorem B113130503 : Blo 1224430 113130503 := bstep (se 1 (by rfl) ⟨84847877, by rfl⟩ : syracuseStep 113130503 = 169695755) B169695755
theorem B75420335 : Blo 1224430 75420335 := bstep (se 1 (by rfl) ⟨56565251, by rfl⟩ : syracuseStep 75420335 = 113130503) B113130503
theorem B190935751 : Blo 1224430 190935751 := bstep (se 1 (by rfl) ⟨143201813, by rfl⟩ : syracuseStep 190935751 = 286403627) B286403627
theorem B50280223 : Blo 1224430 50280223 := bstep (se 1 (by rfl) ⟨37710167, by rfl⟩ : syracuseStep 50280223 = 75420335) B75420335
theorem B254581001 : Blo 1224430 254581001 := bstep (se 2 (by rfl) ⟨95467875, by rfl⟩ : syracuseStep 254581001 = 190935751) B190935751
theorem B67040297 : Blo 1224430 67040297 := bstep (se 2 (by rfl) ⟨25140111, by rfl⟩ : syracuseStep 67040297 = 50280223) B50280223
theorem B169720667 : Blo 1224430 169720667 := bstep (se 1 (by rfl) ⟨127290500, by rfl⟩ : syracuseStep 169720667 = 254581001) B254581001
theorem B44693531 : Blo 1224430 44693531 := bstep (se 1 (by rfl) ⟨33520148, by rfl⟩ : syracuseStep 44693531 = 67040297) B67040297
theorem B113147111 : Blo 1224430 113147111 := bstep (se 1 (by rfl) ⟨84860333, by rfl⟩ : syracuseStep 113147111 = 169720667) B169720667
theorem B29795687 : Blo 1224430 29795687 := bstep (se 1 (by rfl) ⟨22346765, by rfl⟩ : syracuseStep 29795687 = 44693531) B44693531
theorem B75431407 : Blo 1224430 75431407 := bstep (se 1 (by rfl) ⟨56573555, by rfl⟩ : syracuseStep 75431407 = 113147111) B113147111
theorem B100575209 : Blo 1224430 100575209 := bstep (se 2 (by rfl) ⟨37715703, by rfl⟩ : syracuseStep 100575209 = 75431407) B75431407
theorem B19863791 : Blo 1224430 19863791 := bstep (se 1 (by rfl) ⟨14897843, by rfl⟩ : syracuseStep 19863791 = 29795687) B29795687
theorem B13242527 : Blo 1224430 13242527 := bstep (se 1 (by rfl) ⟨9931895, by rfl⟩ : syracuseStep 13242527 = 19863791) B19863791
theorem B67050139 : Blo 1224430 67050139 := bstep (se 1 (by rfl) ⟨50287604, by rfl⟩ : syracuseStep 67050139 = 100575209) B100575209
theorem B89400185 : Blo 1224430 89400185 := bstep (se 2 (by rfl) ⟨33525069, by rfl⟩ : syracuseStep 89400185 = 67050139) B67050139
theorem B8828351 : Blo 1224430 8828351 := bstep (se 1 (by rfl) ⟨6621263, by rfl⟩ : syracuseStep 8828351 = 13242527) B13242527
theorem B59600123 : Blo 1224430 59600123 := bstep (se 1 (by rfl) ⟨44700092, by rfl⟩ : syracuseStep 59600123 = 89400185) B89400185
theorem B5885567 : Blo 1224430 5885567 := bstep (se 1 (by rfl) ⟨4414175, by rfl⟩ : syracuseStep 5885567 = 8828351) B8828351
theorem B39733415 : Blo 1224430 39733415 := bstep (se 1 (by rfl) ⟨29800061, by rfl⟩ : syracuseStep 39733415 = 59600123) B59600123
theorem B3923711 : Blo 1224430 3923711 := bstep (se 1 (by rfl) ⟨2942783, by rfl⟩ : syracuseStep 3923711 = 5885567) B5885567
theorem B2615807 : Blo 1224430 2615807 := bstep (se 1 (by rfl) ⟨1961855, by rfl⟩ : syracuseStep 2615807 = 3923711) B3923711
theorem B26488943 : Blo 1224430 26488943 := bstep (se 1 (by rfl) ⟨19866707, by rfl⟩ : syracuseStep 26488943 = 39733415) B39733415
theorem B17659295 : Blo 1224430 17659295 := bstep (se 1 (by rfl) ⟨13244471, by rfl⟩ : syracuseStep 17659295 = 26488943) B26488943
theorem B1743871 : Blo 1224430 1743871 := bstep (se 1 (by rfl) ⟨1307903, by rfl⟩ : syracuseStep 1743871 = 2615807) B2615807
theorem B11772863 : Blo 1224430 11772863 := bstep (se 1 (by rfl) ⟨8829647, by rfl⟩ : syracuseStep 11772863 = 17659295) B17659295
theorem B2325161 : Blo 1224430 2325161 := bstep (se 2 (by rfl) ⟨871935, by rfl⟩ : syracuseStep 2325161 = 1743871) B1743871
theorem B7848575 : Blo 1224430 7848575 := bstep (se 1 (by rfl) ⟨5886431, by rfl⟩ : syracuseStep 7848575 = 11772863) B11772863
theorem B1550107 : Blo 1224430 1550107 := bstep (se 1 (by rfl) ⟨1162580, by rfl⟩ : syracuseStep 1550107 = 2325161) B2325161
theorem B2066809 : Blo 1224430 2066809 := bstep (se 2 (by rfl) ⟨775053, by rfl⟩ : syracuseStep 2066809 = 1550107) B1550107
theorem B5232383 : Blo 1224430 5232383 := bstep (se 1 (by rfl) ⟨3924287, by rfl⟩ : syracuseStep 5232383 = 7848575) B7848575
theorem B2755745 : Blo 1224430 2755745 := bstep (se 2 (by rfl) ⟨1033404, by rfl⟩ : syracuseStep 2755745 = 2066809) B2066809
theorem B3488255 : Blo 1224430 3488255 := bstep (se 1 (by rfl) ⟨2616191, by rfl⟩ : syracuseStep 3488255 = 5232383) B5232383
theorem B1837163 : Blo 1224430 1837163 := bstep (se 1 (by rfl) ⟨1377872, by rfl⟩ : syracuseStep 1837163 = 2755745) B2755745
theorem B2325503 : Blo 1224430 2325503 := bstep (se 1 (by rfl) ⟨1744127, by rfl⟩ : syracuseStep 2325503 = 3488255) B3488255
theorem B1550335 : Blo 1224430 1550335 := bstep (se 1 (by rfl) ⟨1162751, by rfl⟩ : syracuseStep 1550335 = 2325503) B2325503
theorem B1224775 : Blo 1224430 1224775 := bstep (se 1 (by rfl) ⟨918581, by rfl⟩ : syracuseStep 1224775 = 1837163) B1837163
theorem B2067113 : Blo 1224430 2067113 := bstep (se 2 (by rfl) ⟨775167, by rfl⟩ : syracuseStep 2067113 = 1550335) B1550335
theorem B1378075 : Blo 1224430 1378075 := bstep (se 1 (by rfl) ⟨1033556, by rfl⟩ : syracuseStep 1378075 = 2067113) B2067113
theorem B1837433 : Blo 1224430 1837433 := bstep (se 2 (by rfl) ⟨689037, by rfl⟩ : syracuseStep 1837433 = 1378075) B1378075
theorem B1224955 : Blo 1224430 1224955 := bstep (se 1 (by rfl) ⟨918716, by rfl⟩ : syracuseStep 1224955 = 1837433) B1837433

theorem C0 (j : ℕ) (h1 : 306107 ≤ j) (h2 : j ≤ 306606) : Blo 1224430 (4 * j + 3) := by
  interval_cases j
  · exact B1224431
  · exact B1224435
  · exact B1224439
  · exact B1224443
  · exact B1224447
  · exact B1224451
  · exact B1224455
  · exact B1224459
  · exact B1224463
  · exact B1224467
  · exact B1224471
  · exact B1224475
  · exact B1224479
  · exact B1224483
  · exact B1224487
  · exact B1224491
  · exact B1224495
  · exact B1224499
  · exact B1224503
  · exact B1224507
  · exact B1224511
  · exact B1224515
  · exact B1224519
  · exact B1224523
  · exact B1224527
  · exact B1224531
  · exact B1224535
  · exact B1224539
  · exact B1224543
  · exact B1224547
  · exact B1224551
  · exact B1224555
  · exact B1224559
  · exact B1224563
  · exact B1224567
  · exact B1224571
  · exact B1224575
  · exact B1224579
  · exact B1224583
  · exact B1224587
  · exact B1224591
  · exact B1224595
  · exact B1224599
  · exact B1224603
  · exact B1224607
  · exact B1224611
  · exact B1224615
  · exact B1224619
  · exact B1224623
  · exact B1224627
  · exact B1224631
  · exact B1224635
  · exact B1224639
  · exact B1224643
  · exact B1224647
  · exact B1224651
  · exact B1224655
  · exact B1224659
  · exact B1224663
  · exact B1224667
  · exact B1224671
  · exact B1224675
  · exact B1224679
  · exact B1224683
  · exact B1224687
  · exact B1224691
  · exact B1224695
  · exact B1224699
  · exact B1224703
  · exact B1224707
  · exact B1224711
  · exact B1224715
  · exact B1224719
  · exact B1224723
  · exact B1224727
  · exact B1224731
  · exact B1224735
  · exact B1224739
  · exact B1224743
  · exact B1224747
  · exact B1224751
  · exact B1224755
  · exact B1224759
  · exact B1224763
  · exact B1224767
  · exact B1224771
  · exact B1224775
  · exact B1224779
  · exact B1224783
  · exact B1224787
  · exact B1224791
  · exact B1224795
  · exact B1224799
  · exact B1224803
  · exact B1224807
  · exact B1224811
  · exact B1224815
  · exact B1224819
  · exact B1224823
  · exact B1224827
  · exact B1224831
  · exact B1224835
  · exact B1224839
  · exact B1224843
  · exact B1224847
  · exact B1224851
  · exact B1224855
  · exact B1224859
  · exact B1224863
  · exact B1224867
  · exact B1224871
  · exact B1224875
  · exact B1224879
  · exact B1224883
  · exact B1224887
  · exact B1224891
  · exact B1224895
  · exact B1224899
  · exact B1224903
  · exact B1224907
  · exact B1224911
  · exact B1224915
  · exact B1224919
  · exact B1224923
  · exact B1224927
  · exact B1224931
  · exact B1224935
  · exact B1224939
  · exact B1224943
  · exact B1224947
  · exact B1224951
  · exact B1224955
  · exact B1224959
  · exact B1224963
  · exact B1224967
  · exact B1224971
  · exact B1224975
  · exact B1224979
  · exact B1224983
  · exact B1224987
  · exact B1224991
  · exact B1224995
  · exact B1224999
  · exact B1225003
  · exact B1225007
  · exact B1225011
  · exact B1225015
  · exact B1225019
  · exact B1225023
  · exact B1225027
  · exact B1225031
  · exact B1225035
  · exact B1225039
  · exact B1225043
  · exact B1225047
  · exact B1225051
  · exact B1225055
  · exact B1225059
  · exact B1225063
  · exact B1225067
  · exact B1225071
  · exact B1225075
  · exact B1225079
  · exact B1225083
  · exact B1225087
  · exact B1225091
  · exact B1225095
  · exact B1225099
  · exact B1225103
  · exact B1225107
  · exact B1225111
  · exact B1225115
  · exact B1225119
  · exact B1225123
  · exact B1225127
  · exact B1225131
  · exact B1225135
  · exact B1225139
  · exact B1225143
  · exact B1225147
  · exact B1225151
  · exact B1225155
  · exact B1225159
  · exact B1225163
  · exact B1225167
  · exact B1225171
  · exact B1225175
  · exact B1225179
  · exact B1225183
  · exact B1225187
  · exact B1225191
  · exact B1225195
  · exact B1225199
  · exact B1225203
  · exact B1225207
  · exact B1225211
  · exact B1225215
  · exact B1225219
  · exact B1225223
  · exact B1225227
  · exact B1225231
  · exact B1225235
  · exact B1225239
  · exact B1225243
  · exact B1225247
  · exact B1225251
  · exact B1225255
  · exact B1225259
  · exact B1225263
  · exact B1225267
  · exact B1225271
  · exact B1225275
  · exact B1225279
  · exact B1225283
  · exact B1225287
  · exact B1225291
  · exact B1225295
  · exact B1225299
  · exact B1225303
  · exact B1225307
  · exact B1225311
  · exact B1225315
  · exact B1225319
  · exact B1225323
  · exact B1225327
  · exact B1225331
  · exact B1225335
  · exact B1225339
  · exact B1225343
  · exact B1225347
  · exact B1225351
  · exact B1225355
  · exact B1225359
  · exact B1225363
  · exact B1225367
  · exact B1225371
  · exact B1225375
  · exact B1225379
  · exact B1225383
  · exact B1225387
  · exact B1225391
  · exact B1225395
  · exact B1225399
  · exact B1225403
  · exact B1225407
  · exact B1225411
  · exact B1225415
  · exact B1225419
  · exact B1225423
  · exact B1225427
  · exact B1225431
  · exact B1225435
  · exact B1225439
  · exact B1225443
  · exact B1225447
  · exact B1225451
  · exact B1225455
  · exact B1225459
  · exact B1225463
  · exact B1225467
  · exact B1225471
  · exact B1225475
  · exact B1225479
  · exact B1225483
  · exact B1225487
  · exact B1225491
  · exact B1225495
  · exact B1225499
  · exact B1225503
  · exact B1225507
  · exact B1225511
  · exact B1225515
  · exact B1225519
  · exact B1225523
  · exact B1225527
  · exact B1225531
  · exact B1225535
  · exact B1225539
  · exact B1225543
  · exact B1225547
  · exact B1225551
  · exact B1225555
  · exact B1225559
  · exact B1225563
  · exact B1225567
  · exact B1225571
  · exact B1225575
  · exact B1225579
  · exact B1225583
  · exact B1225587
  · exact B1225591
  · exact B1225595
  · exact B1225599
  · exact B1225603
  · exact B1225607
  · exact B1225611
  · exact B1225615
  · exact B1225619
  · exact B1225623
  · exact B1225627
  · exact B1225631
  · exact B1225635
  · exact B1225639
  · exact B1225643
  · exact B1225647
  · exact B1225651
  · exact B1225655
  · exact B1225659
  · exact B1225663
  · exact B1225667
  · exact B1225671
  · exact B1225675
  · exact B1225679
  · exact B1225683
  · exact B1225687
  · exact B1225691
  · exact B1225695
  · exact B1225699
  · exact B1225703
  · exact B1225707
  · exact B1225711
  · exact B1225715
  · exact B1225719
  · exact B1225723
  · exact B1225727
  · exact B1225731
  · exact B1225735
  · exact B1225739
  · exact B1225743
  · exact B1225747
  · exact B1225751
  · exact B1225755
  · exact B1225759
  · exact B1225763
  · exact B1225767
  · exact B1225771
  · exact B1225775
  · exact B1225779
  · exact B1225783
  · exact B1225787
  · exact B1225791
  · exact B1225795
  · exact B1225799
  · exact B1225803
  · exact B1225807
  · exact B1225811
  · exact B1225815
  · exact B1225819
  · exact B1225823
  · exact B1225827
  · exact B1225831
  · exact B1225835
  · exact B1225839
  · exact B1225843
  · exact B1225847
  · exact B1225851
  · exact B1225855
  · exact B1225859
  · exact B1225863
  · exact B1225867
  · exact B1225871
  · exact B1225875
  · exact B1225879
  · exact B1225883
  · exact B1225887
  · exact B1225891
  · exact B1225895
  · exact B1225899
  · exact B1225903
  · exact B1225907
  · exact B1225911
  · exact B1225915
  · exact B1225919
  · exact B1225923
  · exact B1225927
  · exact B1225931
  · exact B1225935
  · exact B1225939
  · exact B1225943
  · exact B1225947
  · exact B1225951
  · exact B1225955
  · exact B1225959
  · exact B1225963
  · exact B1225967
  · exact B1225971
  · exact B1225975
  · exact B1225979
  · exact B1225983
  · exact B1225987
  · exact B1225991
  · exact B1225995
  · exact B1225999
  · exact B1226003
  · exact B1226007
  · exact B1226011
  · exact B1226015
  · exact B1226019
  · exact B1226023
  · exact B1226027
  · exact B1226031
  · exact B1226035
  · exact B1226039
  · exact B1226043
  · exact B1226047
  · exact B1226051
  · exact B1226055
  · exact B1226059
  · exact B1226063
  · exact B1226067
  · exact B1226071
  · exact B1226075
  · exact B1226079
  · exact B1226083
  · exact B1226087
  · exact B1226091
  · exact B1226095
  · exact B1226099
  · exact B1226103
  · exact B1226107
  · exact B1226111
  · exact B1226115
  · exact B1226119
  · exact B1226123
  · exact B1226127
  · exact B1226131
  · exact B1226135
  · exact B1226139
  · exact B1226143
  · exact B1226147
  · exact B1226151
  · exact B1226155
  · exact B1226159
  · exact B1226163
  · exact B1226167
  · exact B1226171
  · exact B1226175
  · exact B1226179
  · exact B1226183
  · exact B1226187
  · exact B1226191
  · exact B1226195
  · exact B1226199
  · exact B1226203
  · exact B1226207
  · exact B1226211
  · exact B1226215
  · exact B1226219
  · exact B1226223
  · exact B1226227
  · exact B1226231
  · exact B1226235
  · exact B1226239
  · exact B1226243
  · exact B1226247
  · exact B1226251
  · exact B1226255
  · exact B1226259
  · exact B1226263
  · exact B1226267
  · exact B1226271
  · exact B1226275
  · exact B1226279
  · exact B1226283
  · exact B1226287
  · exact B1226291
  · exact B1226295
  · exact B1226299
  · exact B1226303
  · exact B1226307
  · exact B1226311
  · exact B1226315
  · exact B1226319
  · exact B1226323
  · exact B1226327
  · exact B1226331
  · exact B1226335
  · exact B1226339
  · exact B1226343
  · exact B1226347
  · exact B1226351
  · exact B1226355
  · exact B1226359
  · exact B1226363
  · exact B1226367
  · exact B1226371
  · exact B1226375
  · exact B1226379
  · exact B1226383
  · exact B1226387
  · exact B1226391
  · exact B1226395
  · exact B1226399
  · exact B1226403
  · exact B1226407
  · exact B1226411
  · exact B1226415
  · exact B1226419
  · exact B1226423
  · exact B1226427

theorem solution (m : ℕ) (hlo : 1224430 ≤ m) (hhi : m ≤ 1226430) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 306107 ≤ j := by omega
    have hj2 : j ≤ 306606 := by omega
    have hb : Blo 1224430 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
