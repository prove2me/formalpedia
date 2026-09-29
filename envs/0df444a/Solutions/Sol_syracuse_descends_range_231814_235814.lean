-- Prove2me | solution 1 for syracuse_descends_range_231814_235814
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T16:43:58.758935+00:00
-- url     : https://prove2.me/submissions/41696f17-b9cb-4a24-8673-2b9f1bfb77b7

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


theorem B393221 : Blo 231814 393221 := bbase (se 4 (by rfl) ⟨36864, by rfl⟩ : syracuseStep 393221 = 73729) (by norm_num)
theorem B262165 : Blo 231814 262165 := bbase (se 6 (by rfl) ⟨6144, by rfl⟩ : syracuseStep 262165 = 12289) (by norm_num)
theorem B294941 : Blo 231814 294941 := bbase (se 3 (by rfl) ⟨55301, by rfl⟩ : syracuseStep 294941 = 110603) (by norm_num)
theorem B1769525 : Blo 231814 1769525 := bbase (se 5 (by rfl) ⟨82946, by rfl⟩ : syracuseStep 1769525 = 165893) (by norm_num)
theorem B262201 : Blo 231814 262201 := bbase (se 2 (by rfl) ⟨98325, by rfl⟩ : syracuseStep 262201 = 196651) (by norm_num)
theorem B524357 : Blo 231814 524357 := bbase (se 4 (by rfl) ⟨49158, by rfl⟩ : syracuseStep 524357 = 98317) (by norm_num)
theorem B294997 : Blo 231814 294997 := bbase (se 8 (by rfl) ⟨1728, by rfl⟩ : syracuseStep 294997 = 3457) (by norm_num)
theorem B262237 : Blo 231814 262237 := bbase (se 3 (by rfl) ⟨49169, by rfl⟩ : syracuseStep 262237 = 98339) (by norm_num)
theorem B262273 : Blo 231814 262273 := bbase (se 2 (by rfl) ⟨98352, by rfl⟩ : syracuseStep 262273 = 196705) (by norm_num)
theorem B393349 : Blo 231814 393349 := bbase (se 4 (by rfl) ⟨36876, by rfl⟩ : syracuseStep 393349 = 73753) (by norm_num)
theorem B524429 : Blo 231814 524429 := bbase (se 3 (by rfl) ⟨98330, by rfl⟩ : syracuseStep 524429 = 196661) (by norm_num)
theorem B262309 : Blo 231814 262309 := bbase (se 4 (by rfl) ⟨24591, by rfl⟩ : syracuseStep 262309 = 49183) (by norm_num)
theorem B557237 : Blo 231814 557237 := bbase (se 5 (by rfl) ⟨26120, by rfl⟩ : syracuseStep 557237 = 52241) (by norm_num)
theorem B295093 : Blo 231814 295093 := bbase (se 5 (by rfl) ⟨13832, by rfl⟩ : syracuseStep 295093 = 27665) (by norm_num)
theorem B1179845 : Blo 231814 1179845 := bbase (se 4 (by rfl) ⟨110610, by rfl⟩ : syracuseStep 1179845 = 221221) (by norm_num)
theorem B262345 : Blo 231814 262345 := bbase (se 2 (by rfl) ⟨98379, by rfl⟩ : syracuseStep 262345 = 196759) (by norm_num)
theorem B524501 : Blo 231814 524501 := bbase (se 7 (by rfl) ⟨6146, by rfl⟩ : syracuseStep 524501 = 12293) (by norm_num)
theorem B393437 : Blo 231814 393437 := bbase (se 3 (by rfl) ⟨73769, by rfl⟩ : syracuseStep 393437 = 147539) (by norm_num)
theorem B262381 : Blo 231814 262381 := bbase (se 3 (by rfl) ⟨49196, by rfl⟩ : syracuseStep 262381 = 98393) (by norm_num)
theorem B295169 : Blo 231814 295169 := bbase (se 2 (by rfl) ⟨110688, by rfl⟩ : syracuseStep 295169 = 221377) (by norm_num)
theorem B262417 : Blo 231814 262417 := bbase (se 2 (by rfl) ⟨98406, by rfl⟩ : syracuseStep 262417 = 196813) (by norm_num)
theorem B524573 : Blo 231814 524573 := bbase (se 3 (by rfl) ⟨98357, by rfl⟩ : syracuseStep 524573 = 196715) (by norm_num)
theorem B786725 : Blo 231814 786725 := bbase (se 4 (by rfl) ⟨73755, by rfl⟩ : syracuseStep 786725 = 147511) (by norm_num)
theorem B590125 : Blo 231814 590125 := bbase (se 3 (by rfl) ⟨110648, by rfl⟩ : syracuseStep 590125 = 221297) (by norm_num)
theorem B262453 : Blo 231814 262453 := bbase (se 5 (by rfl) ⟨12302, by rfl⟩ : syracuseStep 262453 = 24605) (by norm_num)
theorem B262489 : Blo 231814 262489 := bbase (se 2 (by rfl) ⟨98433, by rfl⟩ : syracuseStep 262489 = 196867) (by norm_num)
theorem B393565 : Blo 231814 393565 := bbase (se 3 (by rfl) ⟨73793, by rfl⟩ : syracuseStep 393565 = 147587) (by norm_num)
theorem B295265 : Blo 231814 295265 := bbase (se 2 (by rfl) ⟨110724, by rfl⟩ : syracuseStep 295265 = 221449) (by norm_num)
theorem B524645 : Blo 231814 524645 := bbase (se 4 (by rfl) ⟨49185, by rfl⟩ : syracuseStep 524645 = 98371) (by norm_num)
theorem B262525 : Blo 231814 262525 := bbase (se 3 (by rfl) ⟨49223, by rfl⟩ : syracuseStep 262525 = 98447) (by norm_num)
theorem B295321 : Blo 231814 295321 := bbase (se 2 (by rfl) ⟨110745, by rfl⟩ : syracuseStep 295321 = 221491) (by norm_num)
theorem B590237 : Blo 231814 590237 := bbase (se 3 (by rfl) ⟨110669, by rfl⟩ : syracuseStep 590237 = 221339) (by norm_num)
theorem B262561 : Blo 231814 262561 := bbase (se 2 (by rfl) ⟨98460, by rfl⟩ : syracuseStep 262561 = 196921) (by norm_num)
theorem B524717 : Blo 231814 524717 := bbase (se 3 (by rfl) ⟨98384, by rfl⟩ : syracuseStep 524717 = 196769) (by norm_num)
theorem B393653 : Blo 231814 393653 := bbase (se 5 (by rfl) ⟨18452, by rfl⟩ : syracuseStep 393653 = 36905) (by norm_num)
theorem B262597 : Blo 231814 262597 := bbase (se 4 (by rfl) ⟨24618, by rfl⟩ : syracuseStep 262597 = 49237) (by norm_num)
theorem B262633 : Blo 231814 262633 := bbase (se 2 (by rfl) ⟨98487, by rfl⟩ : syracuseStep 262633 = 196975) (by norm_num)
theorem B524789 : Blo 231814 524789 := bbase (se 5 (by rfl) ⟨24599, by rfl⟩ : syracuseStep 524789 = 49199) (by norm_num)
theorem B1901045 : Blo 231814 1901045 := bbase (se 5 (by rfl) ⟨89111, by rfl⟩ : syracuseStep 1901045 = 178223) (by norm_num)
theorem B295417 : Blo 231814 295417 := bbase (se 2 (by rfl) ⟨110781, by rfl⟩ : syracuseStep 295417 = 221563) (by norm_num)
theorem B262669 : Blo 231814 262669 := bbase (se 3 (by rfl) ⟨49250, by rfl⟩ : syracuseStep 262669 = 98501) (by norm_num)
theorem B262705 : Blo 231814 262705 := bbase (se 2 (by rfl) ⟨98514, by rfl⟩ : syracuseStep 262705 = 197029) (by norm_num)
theorem B393781 : Blo 231814 393781 := bbase (se 5 (by rfl) ⟨18458, by rfl⟩ : syracuseStep 393781 = 36917) (by norm_num)
theorem B524861 : Blo 231814 524861 := bbase (se 3 (by rfl) ⟨98411, by rfl⟩ : syracuseStep 524861 = 196823) (by norm_num)
theorem B262741 : Blo 231814 262741 := bbase (se 8 (by rfl) ⟨1539, by rfl⟩ : syracuseStep 262741 = 3079) (by norm_num)
theorem B590429 : Blo 231814 590429 := bbase (se 3 (by rfl) ⟨110705, by rfl⟩ : syracuseStep 590429 = 221411) (by norm_num)
theorem B262777 : Blo 231814 262777 := bbase (se 2 (by rfl) ⟨98541, by rfl⟩ : syracuseStep 262777 = 197083) (by norm_num)
theorem B524933 : Blo 231814 524933 := bbase (se 4 (by rfl) ⟨49212, by rfl⟩ : syracuseStep 524933 = 98425) (by norm_num)
theorem B393869 : Blo 231814 393869 := bbase (se 3 (by rfl) ⟨73850, by rfl⟩ : syracuseStep 393869 = 147701) (by norm_num)
theorem B262813 : Blo 231814 262813 := bbase (se 3 (by rfl) ⟨49277, by rfl⟩ : syracuseStep 262813 = 98555) (by norm_num)
theorem B295589 : Blo 231814 295589 := bbase (se 4 (by rfl) ⟨27711, by rfl⟩ : syracuseStep 295589 = 55423) (by norm_num)
theorem B262849 : Blo 231814 262849 := bbase (se 2 (by rfl) ⟨98568, by rfl⟩ : syracuseStep 262849 = 197137) (by norm_num)
theorem B525005 : Blo 231814 525005 := bbase (se 3 (by rfl) ⟨98438, by rfl⟩ : syracuseStep 525005 = 196877) (by norm_num)
theorem B787157 : Blo 231814 787157 := bbase (se 7 (by rfl) ⟨9224, by rfl⟩ : syracuseStep 787157 = 18449) (by norm_num)
theorem B295645 : Blo 231814 295645 := bbase (se 3 (by rfl) ⟨55433, by rfl⟩ : syracuseStep 295645 = 110867) (by norm_num)
theorem B262885 : Blo 231814 262885 := bbase (se 4 (by rfl) ⟨24645, by rfl⟩ : syracuseStep 262885 = 49291) (by norm_num)
theorem B262921 : Blo 231814 262921 := bbase (se 2 (by rfl) ⟨98595, by rfl⟩ : syracuseStep 262921 = 197191) (by norm_num)
theorem B393997 : Blo 231814 393997 := bbase (se 3 (by rfl) ⟨73874, by rfl⟩ : syracuseStep 393997 = 147749) (by norm_num)
theorem B525077 : Blo 231814 525077 := bbase (se 6 (by rfl) ⟨12306, by rfl⟩ : syracuseStep 525077 = 24613) (by norm_num)
theorem B262957 : Blo 231814 262957 := bbase (se 3 (by rfl) ⟨49304, by rfl⟩ : syracuseStep 262957 = 98609) (by norm_num)
theorem B295741 : Blo 231814 295741 := bbase (se 3 (by rfl) ⟨55451, by rfl⟩ : syracuseStep 295741 = 110903) (by norm_num)
theorem B262993 : Blo 231814 262993 := bbase (se 2 (by rfl) ⟨98622, by rfl⟩ : syracuseStep 262993 = 197245) (by norm_num)
theorem B525149 : Blo 231814 525149 := bbase (se 3 (by rfl) ⟨98465, by rfl⟩ : syracuseStep 525149 = 196931) (by norm_num)
theorem B394085 : Blo 231814 394085 := bbase (se 4 (by rfl) ⟨36945, by rfl⟩ : syracuseStep 394085 = 73891) (by norm_num)
theorem B263029 : Blo 231814 263029 := bbase (se 5 (by rfl) ⟨12329, by rfl⟩ : syracuseStep 263029 = 24659) (by norm_num)
theorem B263065 : Blo 231814 263065 := bbase (se 2 (by rfl) ⟨98649, by rfl⟩ : syracuseStep 263065 = 197299) (by norm_num)
theorem B525221 : Blo 231814 525221 := bbase (se 4 (by rfl) ⟨49239, by rfl⟩ : syracuseStep 525221 = 98479) (by norm_num)
theorem B951205 : Blo 231814 951205 := bbase (se 4 (by rfl) ⟨89175, by rfl⟩ : syracuseStep 951205 = 178351) (by norm_num)
theorem B590773 : Blo 231814 590773 := bbase (se 5 (by rfl) ⟨27692, by rfl⟩ : syracuseStep 590773 = 55385) (by norm_num)
theorem B263101 : Blo 231814 263101 := bbase (se 3 (by rfl) ⟨49331, by rfl⟩ : syracuseStep 263101 = 98663) (by norm_num)
theorem B263137 : Blo 231814 263137 := bbase (se 2 (by rfl) ⟨98676, by rfl⟩ : syracuseStep 263137 = 197353) (by norm_num)
theorem B394213 : Blo 231814 394213 := bbase (se 4 (by rfl) ⟨36957, by rfl⟩ : syracuseStep 394213 = 73915) (by norm_num)
theorem B295913 : Blo 231814 295913 := bbase (se 2 (by rfl) ⟨110967, by rfl⟩ : syracuseStep 295913 = 221935) (by norm_num)
theorem B525293 : Blo 231814 525293 := bbase (se 3 (by rfl) ⟨98492, by rfl⟩ : syracuseStep 525293 = 196985) (by norm_num)
theorem B263173 : Blo 231814 263173 := bbase (se 4 (by rfl) ⟨24672, by rfl⟩ : syracuseStep 263173 = 49345) (by norm_num)
theorem B951301 : Blo 231814 951301 := bbase (se 4 (by rfl) ⟨89184, by rfl⟩ : syracuseStep 951301 = 178369) (by norm_num)
theorem B295969 : Blo 231814 295969 := bbase (se 2 (by rfl) ⟨110988, by rfl⟩ : syracuseStep 295969 = 221977) (by norm_num)
theorem B590885 : Blo 231814 590885 := bbase (se 4 (by rfl) ⟨55395, by rfl⟩ : syracuseStep 590885 = 110791) (by norm_num)
theorem B263209 : Blo 231814 263209 := bbase (se 2 (by rfl) ⟨98703, by rfl⟩ : syracuseStep 263209 = 197407) (by norm_num)
theorem B525365 : Blo 231814 525365 := bbase (se 5 (by rfl) ⟨24626, by rfl⟩ : syracuseStep 525365 = 49253) (by norm_num)
theorem B394301 : Blo 231814 394301 := bbase (se 3 (by rfl) ⟨73931, by rfl⟩ : syracuseStep 394301 = 147863) (by norm_num)
theorem B263245 : Blo 231814 263245 := bbase (se 3 (by rfl) ⟨49358, by rfl⟩ : syracuseStep 263245 = 98717) (by norm_num)
theorem B263281 : Blo 231814 263281 := bbase (se 2 (by rfl) ⟨98730, by rfl⟩ : syracuseStep 263281 = 197461) (by norm_num)
theorem B525437 : Blo 231814 525437 := bbase (se 3 (by rfl) ⟨98519, by rfl⟩ : syracuseStep 525437 = 197039) (by norm_num)
theorem B296065 : Blo 231814 296065 := bbase (se 2 (by rfl) ⟨111024, by rfl⟩ : syracuseStep 296065 = 222049) (by norm_num)
theorem B787589 : Blo 231814 787589 := bbase (se 4 (by rfl) ⟨73836, by rfl⟩ : syracuseStep 787589 = 147673) (by norm_num)
theorem B263317 : Blo 231814 263317 := bbase (se 6 (by rfl) ⟨6171, by rfl⟩ : syracuseStep 263317 = 12343) (by norm_num)
theorem B263353 : Blo 231814 263353 := bbase (se 2 (by rfl) ⟨98757, by rfl⟩ : syracuseStep 263353 = 197515) (by norm_num)
theorem B394429 : Blo 231814 394429 := bbase (se 3 (by rfl) ⟨73955, by rfl⟩ : syracuseStep 394429 = 147911) (by norm_num)
theorem B525509 : Blo 231814 525509 := bbase (se 4 (by rfl) ⟨49266, by rfl⟩ : syracuseStep 525509 = 98533) (by norm_num)
theorem B722117 : Blo 231814 722117 := bbase (se 4 (by rfl) ⟨67698, by rfl⟩ : syracuseStep 722117 = 135397) (by norm_num)
theorem B263389 : Blo 231814 263389 := bbase (se 3 (by rfl) ⟨49385, by rfl⟩ : syracuseStep 263389 = 98771) (by norm_num)
theorem B591077 : Blo 231814 591077 := bbase (se 4 (by rfl) ⟨55413, by rfl⟩ : syracuseStep 591077 = 110827) (by norm_num)
theorem B263425 : Blo 231814 263425 := bbase (se 2 (by rfl) ⟨98784, by rfl⟩ : syracuseStep 263425 = 197569) (by norm_num)
theorem B525581 : Blo 231814 525581 := bbase (se 3 (by rfl) ⟨98546, by rfl⟩ : syracuseStep 525581 = 197093) (by norm_num)
theorem B394517 : Blo 231814 394517 := bbase (se 6 (by rfl) ⟨9246, by rfl⟩ : syracuseStep 394517 = 18493) (by norm_num)
theorem B263461 : Blo 231814 263461 := bbase (se 4 (by rfl) ⟨24699, by rfl⟩ : syracuseStep 263461 = 49399) (by norm_num)
theorem B296237 : Blo 231814 296237 := bbase (se 3 (by rfl) ⟨55544, by rfl⟩ : syracuseStep 296237 = 111089) (by norm_num)
theorem B886085 : Blo 231814 886085 := bbase (se 4 (by rfl) ⟨83070, by rfl⟩ : syracuseStep 886085 = 166141) (by norm_num)
theorem B263497 : Blo 231814 263497 := bbase (se 2 (by rfl) ⟨98811, by rfl⟩ : syracuseStep 263497 = 197623) (by norm_num)
theorem B525653 : Blo 231814 525653 := bbase (se 12 (by rfl) ⟨192, by rfl⟩ : syracuseStep 525653 = 385) (by norm_num)
theorem B296293 : Blo 231814 296293 := bbase (se 4 (by rfl) ⟨27777, by rfl⟩ : syracuseStep 296293 = 55555) (by norm_num)
theorem B427373 : Blo 231814 427373 := bbase (se 3 (by rfl) ⟨80132, by rfl⟩ : syracuseStep 427373 = 160265) (by norm_num)
theorem B263533 : Blo 231814 263533 := bbase (se 3 (by rfl) ⟨49412, by rfl⟩ : syracuseStep 263533 = 98825) (by norm_num)
theorem B263569 : Blo 231814 263569 := bbase (se 2 (by rfl) ⟨98838, by rfl⟩ : syracuseStep 263569 = 197677) (by norm_num)
theorem B394645 : Blo 231814 394645 := bbase (se 6 (by rfl) ⟨9249, by rfl⟩ : syracuseStep 394645 = 18499) (by norm_num)
theorem B525725 : Blo 231814 525725 := bbase (se 3 (by rfl) ⟨98573, by rfl⟩ : syracuseStep 525725 = 197147) (by norm_num)
theorem B263605 : Blo 231814 263605 := bbase (se 5 (by rfl) ⟨12356, by rfl⟩ : syracuseStep 263605 = 24713) (by norm_num)
theorem B296389 : Blo 231814 296389 := bbase (se 4 (by rfl) ⟨27786, by rfl⟩ : syracuseStep 296389 = 55573) (by norm_num)
theorem B3179989 : Blo 231814 3179989 := bbase (se 7 (by rfl) ⟨37265, by rfl⟩ : syracuseStep 3179989 = 74531) (by norm_num)
theorem B1181141 : Blo 231814 1181141 := bbase (se 7 (by rfl) ⟨13841, by rfl⟩ : syracuseStep 1181141 = 27683) (by norm_num)
theorem B263641 : Blo 231814 263641 := bbase (se 2 (by rfl) ⟨98865, by rfl⟩ : syracuseStep 263641 = 197731) (by norm_num)
theorem B755173 : Blo 231814 755173 := bbase (se 4 (by rfl) ⟨70797, by rfl⟩ : syracuseStep 755173 = 141595) (by norm_num)
theorem B525797 : Blo 231814 525797 := bbase (se 4 (by rfl) ⟨49293, by rfl⟩ : syracuseStep 525797 = 98587) (by norm_num)
theorem B394733 : Blo 231814 394733 := bbase (se 3 (by rfl) ⟨74012, by rfl⟩ : syracuseStep 394733 = 148025) (by norm_num)
theorem B263677 : Blo 231814 263677 := bbase (se 3 (by rfl) ⟨49439, by rfl⟩ : syracuseStep 263677 = 98879) (by norm_num)
theorem B263713 : Blo 231814 263713 := bbase (se 2 (by rfl) ⟨98892, by rfl⟩ : syracuseStep 263713 = 197785) (by norm_num)
theorem B525869 : Blo 231814 525869 := bbase (se 3 (by rfl) ⟨98600, by rfl⟩ : syracuseStep 525869 = 197201) (by norm_num)
theorem B788021 : Blo 231814 788021 := bbase (se 5 (by rfl) ⟨36938, by rfl⟩ : syracuseStep 788021 = 73877) (by norm_num)
theorem B591421 : Blo 231814 591421 := bbase (se 3 (by rfl) ⟨110891, by rfl⟩ : syracuseStep 591421 = 221783) (by norm_num)
theorem B263749 : Blo 231814 263749 := bbase (se 4 (by rfl) ⟨24726, by rfl⟩ : syracuseStep 263749 = 49453) (by norm_num)
theorem B886373 : Blo 231814 886373 := bbase (se 4 (by rfl) ⟨83097, by rfl⟩ : syracuseStep 886373 = 166195) (by norm_num)
theorem B263785 : Blo 231814 263785 := bbase (se 2 (by rfl) ⟨98919, by rfl⟩ : syracuseStep 263785 = 197839) (by norm_num)
theorem B394861 : Blo 231814 394861 := bbase (se 3 (by rfl) ⟨74036, by rfl⟩ : syracuseStep 394861 = 148073) (by norm_num)
theorem B296561 : Blo 231814 296561 := bbase (se 2 (by rfl) ⟨111210, by rfl⟩ : syracuseStep 296561 = 222421) (by norm_num)
theorem B1115765 : Blo 231814 1115765 := bbase (se 5 (by rfl) ⟨52301, by rfl⟩ : syracuseStep 1115765 = 104603) (by norm_num)
theorem B525941 : Blo 231814 525941 := bbase (se 5 (by rfl) ⟨24653, by rfl⟩ : syracuseStep 525941 = 49307) (by norm_num)
theorem B263821 : Blo 231814 263821 := bbase (se 3 (by rfl) ⟨49466, by rfl⟩ : syracuseStep 263821 = 98933) (by norm_num)
theorem B296617 : Blo 231814 296617 := bbase (se 2 (by rfl) ⟨111231, by rfl⟩ : syracuseStep 296617 = 222463) (by norm_num)
theorem B591533 : Blo 231814 591533 := bbase (se 3 (by rfl) ⟨110912, by rfl⟩ : syracuseStep 591533 = 221825) (by norm_num)
theorem B263857 : Blo 231814 263857 := bbase (se 2 (by rfl) ⟨98946, by rfl⟩ : syracuseStep 263857 = 197893) (by norm_num)
theorem B526013 : Blo 231814 526013 := bbase (se 3 (by rfl) ⟨98627, by rfl⟩ : syracuseStep 526013 = 197255) (by norm_num)
theorem B394949 : Blo 231814 394949 := bbase (se 4 (by rfl) ⟨37026, by rfl⟩ : syracuseStep 394949 = 74053) (by norm_num)
theorem B263893 : Blo 231814 263893 := bbase (se 7 (by rfl) ⟨3092, by rfl⟩ : syracuseStep 263893 = 6185) (by norm_num)
theorem B263929 : Blo 231814 263929 := bbase (se 2 (by rfl) ⟨98973, by rfl⟩ : syracuseStep 263929 = 197947) (by norm_num)
theorem B526085 : Blo 231814 526085 := bbase (se 4 (by rfl) ⟨49320, by rfl⟩ : syracuseStep 526085 = 98641) (by norm_num)
theorem B296713 : Blo 231814 296713 := bbase (se 2 (by rfl) ⟨111267, by rfl⟩ : syracuseStep 296713 = 222535) (by norm_num)
theorem B263965 : Blo 231814 263965 := bbase (se 3 (by rfl) ⟨49493, by rfl⟩ : syracuseStep 263965 = 98987) (by norm_num)
theorem B264001 : Blo 231814 264001 := bbase (se 2 (by rfl) ⟨99000, by rfl⟩ : syracuseStep 264001 = 198001) (by norm_num)
theorem B395077 : Blo 231814 395077 := bbase (se 4 (by rfl) ⟨37038, by rfl⟩ : syracuseStep 395077 = 74077) (by norm_num)
theorem B526157 : Blo 231814 526157 := bbase (se 3 (by rfl) ⟨98654, by rfl⟩ : syracuseStep 526157 = 197309) (by norm_num)
theorem B264037 : Blo 231814 264037 := bbase (se 4 (by rfl) ⟨24753, by rfl⟩ : syracuseStep 264037 = 49507) (by norm_num)
theorem B591725 : Blo 231814 591725 := bbase (se 3 (by rfl) ⟨110948, by rfl⟩ : syracuseStep 591725 = 221897) (by norm_num)
theorem B264073 : Blo 231814 264073 := bbase (se 2 (by rfl) ⟨99027, by rfl⟩ : syracuseStep 264073 = 198055) (by norm_num)
theorem B526229 : Blo 231814 526229 := bbase (se 6 (by rfl) ⟨12333, by rfl⟩ : syracuseStep 526229 = 24667) (by norm_num)
theorem B395165 : Blo 231814 395165 := bbase (se 3 (by rfl) ⟨74093, by rfl⟩ : syracuseStep 395165 = 148187) (by norm_num)
theorem B264109 : Blo 231814 264109 := bbase (se 3 (by rfl) ⟨49520, by rfl⟩ : syracuseStep 264109 = 99041) (by norm_num)
theorem B296885 : Blo 231814 296885 := bbase (se 5 (by rfl) ⟨13916, by rfl⟩ : syracuseStep 296885 = 27833) (by norm_num)
theorem B264145 : Blo 231814 264145 := bbase (se 2 (by rfl) ⟨99054, by rfl⟩ : syracuseStep 264145 = 198109) (by norm_num)
theorem B755669 : Blo 231814 755669 := bbase (se 7 (by rfl) ⟨8855, by rfl⟩ : syracuseStep 755669 = 17711) (by norm_num)
theorem B526301 : Blo 231814 526301 := bbase (se 3 (by rfl) ⟨98681, by rfl⟩ : syracuseStep 526301 = 197363) (by norm_num)
theorem B788453 : Blo 231814 788453 := bbase (se 4 (by rfl) ⟨73917, by rfl⟩ : syracuseStep 788453 = 147835) (by norm_num)
theorem B296941 : Blo 231814 296941 := bbase (se 3 (by rfl) ⟨55676, by rfl⟩ : syracuseStep 296941 = 111353) (by norm_num)
theorem B264181 : Blo 231814 264181 := bbase (se 5 (by rfl) ⟨12383, by rfl⟩ : syracuseStep 264181 = 24767) (by norm_num)
theorem B264217 : Blo 231814 264217 := bbase (se 2 (by rfl) ⟨99081, by rfl⟩ : syracuseStep 264217 = 198163) (by norm_num)
theorem B395293 : Blo 231814 395293 := bbase (se 3 (by rfl) ⟨74117, by rfl⟩ : syracuseStep 395293 = 148235) (by norm_num)
theorem B526373 : Blo 231814 526373 := bbase (se 4 (by rfl) ⟨49347, by rfl⟩ : syracuseStep 526373 = 98695) (by norm_num)
theorem B264253 : Blo 231814 264253 := bbase (se 3 (by rfl) ⟨49547, by rfl⟩ : syracuseStep 264253 = 99095) (by norm_num)
theorem B297037 : Blo 231814 297037 := bbase (se 3 (by rfl) ⟨55694, by rfl⟩ : syracuseStep 297037 = 111389) (by norm_num)
theorem B264289 : Blo 231814 264289 := bbase (se 2 (by rfl) ⟨99108, by rfl⟩ : syracuseStep 264289 = 198217) (by norm_num)
theorem B526445 : Blo 231814 526445 := bbase (se 3 (by rfl) ⟨98708, by rfl⟩ : syracuseStep 526445 = 197417) (by norm_num)
theorem B395381 : Blo 231814 395381 := bbase (se 5 (by rfl) ⟨18533, by rfl⟩ : syracuseStep 395381 = 37067) (by norm_num)
theorem B559237 : Blo 231814 559237 := bbase (se 4 (by rfl) ⟨52428, by rfl⟩ : syracuseStep 559237 = 104857) (by norm_num)
theorem B264325 : Blo 231814 264325 := bbase (se 4 (by rfl) ⟨24780, by rfl⟩ : syracuseStep 264325 = 49561) (by norm_num)
theorem B264361 : Blo 231814 264361 := bbase (se 2 (by rfl) ⟨99135, by rfl⟩ : syracuseStep 264361 = 198271) (by norm_num)
theorem B526517 : Blo 231814 526517 := bbase (se 5 (by rfl) ⟨24680, by rfl⟩ : syracuseStep 526517 = 49361) (by norm_num)
theorem B592069 : Blo 231814 592069 := bbase (se 4 (by rfl) ⟨55506, by rfl⟩ : syracuseStep 592069 = 111013) (by norm_num)
theorem B264397 : Blo 231814 264397 := bbase (se 3 (by rfl) ⟨49574, by rfl⟩ : syracuseStep 264397 = 99149) (by norm_num)
theorem B264433 : Blo 231814 264433 := bbase (se 2 (by rfl) ⟨99162, by rfl⟩ : syracuseStep 264433 = 198325) (by norm_num)
theorem B395509 : Blo 231814 395509 := bbase (se 5 (by rfl) ⟨18539, by rfl⟩ : syracuseStep 395509 = 37079) (by norm_num)
theorem B297209 : Blo 231814 297209 := bbase (se 2 (by rfl) ⟨111453, by rfl⟩ : syracuseStep 297209 = 222907) (by norm_num)
theorem B526589 : Blo 231814 526589 := bbase (se 3 (by rfl) ⟨98735, by rfl⟩ : syracuseStep 526589 = 197471) (by norm_num)
theorem B264469 : Blo 231814 264469 := bbase (se 6 (by rfl) ⟨6198, by rfl⟩ : syracuseStep 264469 = 12397) (by norm_num)
theorem B297265 : Blo 231814 297265 := bbase (se 2 (by rfl) ⟨111474, by rfl⟩ : syracuseStep 297265 = 222949) (by norm_num)
theorem B592181 : Blo 231814 592181 := bbase (se 5 (by rfl) ⟨27758, by rfl⟩ : syracuseStep 592181 = 55517) (by norm_num)
theorem B264505 : Blo 231814 264505 := bbase (se 2 (by rfl) ⟨99189, by rfl⟩ : syracuseStep 264505 = 198379) (by norm_num)
theorem B526661 : Blo 231814 526661 := bbase (se 4 (by rfl) ⟨49374, by rfl⟩ : syracuseStep 526661 = 98749) (by norm_num)
theorem B395597 : Blo 231814 395597 := bbase (se 3 (by rfl) ⟨74174, by rfl⟩ : syracuseStep 395597 = 148349) (by norm_num)
theorem B264541 : Blo 231814 264541 := bbase (se 3 (by rfl) ⟨49601, by rfl⟩ : syracuseStep 264541 = 99203) (by norm_num)
theorem B2394485 : Blo 231814 2394485 := bbase (se 5 (by rfl) ⟨112241, by rfl⟩ : syracuseStep 2394485 = 224483) (by norm_num)
theorem B1509749 : Blo 231814 1509749 := bbase (se 5 (by rfl) ⟨70769, by rfl⟩ : syracuseStep 1509749 = 141539) (by norm_num)
theorem B264577 : Blo 231814 264577 := bbase (se 2 (by rfl) ⟨99216, by rfl⟩ : syracuseStep 264577 = 198433) (by norm_num)
theorem B526733 : Blo 231814 526733 := bbase (se 3 (by rfl) ⟨98762, by rfl⟩ : syracuseStep 526733 = 197525) (by norm_num)
theorem B297361 : Blo 231814 297361 := bbase (se 2 (by rfl) ⟨111510, by rfl⟩ : syracuseStep 297361 = 223021) (by norm_num)
theorem B788885 : Blo 231814 788885 := bbase (se 6 (by rfl) ⟨18489, by rfl⟩ : syracuseStep 788885 = 36979) (by norm_num)
theorem B264613 : Blo 231814 264613 := bbase (se 4 (by rfl) ⟨24807, by rfl⟩ : syracuseStep 264613 = 49615) (by norm_num)
theorem B264649 : Blo 231814 264649 := bbase (se 2 (by rfl) ⟨99243, by rfl⟩ : syracuseStep 264649 = 198487) (by norm_num)
theorem B395725 : Blo 231814 395725 := bbase (se 3 (by rfl) ⟨74198, by rfl⟩ : syracuseStep 395725 = 148397) (by norm_num)
theorem B526805 : Blo 231814 526805 := bbase (se 7 (by rfl) ⟨6173, by rfl⟩ : syracuseStep 526805 = 12347) (by norm_num)
theorem B264685 : Blo 231814 264685 := bbase (se 3 (by rfl) ⟨49628, by rfl⟩ : syracuseStep 264685 = 99257) (by norm_num)
theorem B592373 : Blo 231814 592373 := bbase (se 5 (by rfl) ⟨27767, by rfl⟩ : syracuseStep 592373 = 55535) (by norm_num)
theorem B264721 : Blo 231814 264721 := bbase (se 2 (by rfl) ⟨99270, by rfl⟩ : syracuseStep 264721 = 198541) (by norm_num)
theorem B526877 : Blo 231814 526877 := bbase (se 3 (by rfl) ⟨98789, by rfl⟩ : syracuseStep 526877 = 197579) (by norm_num)
theorem B395813 : Blo 231814 395813 := bbase (se 4 (by rfl) ⟨37107, by rfl⟩ : syracuseStep 395813 = 74215) (by norm_num)
theorem B2034229 : Blo 231814 2034229 := bbase (se 5 (by rfl) ⟨95354, by rfl⟩ : syracuseStep 2034229 = 190709) (by norm_num)
theorem B264757 : Blo 231814 264757 := bbase (se 5 (by rfl) ⟨12410, by rfl⟩ : syracuseStep 264757 = 24821) (by norm_num)
theorem B297533 : Blo 231814 297533 := bbase (se 3 (by rfl) ⟨55787, by rfl⟩ : syracuseStep 297533 = 111575) (by norm_num)
theorem B264793 : Blo 231814 264793 := bbase (se 2 (by rfl) ⟨99297, by rfl⟩ : syracuseStep 264793 = 198595) (by norm_num)
theorem B526949 : Blo 231814 526949 := bbase (se 4 (by rfl) ⟨49401, by rfl⟩ : syracuseStep 526949 = 98803) (by norm_num)
theorem B297589 : Blo 231814 297589 := bbase (se 5 (by rfl) ⟨13949, by rfl⟩ : syracuseStep 297589 = 27899) (by norm_num)
theorem B264829 : Blo 231814 264829 := bbase (se 3 (by rfl) ⟨49655, by rfl⟩ : syracuseStep 264829 = 99311) (by norm_num)
theorem B264865 : Blo 231814 264865 := bbase (se 2 (by rfl) ⟨99324, by rfl⟩ : syracuseStep 264865 = 198649) (by norm_num)
theorem B395941 : Blo 231814 395941 := bbase (se 4 (by rfl) ⟨37119, by rfl⟩ : syracuseStep 395941 = 74239) (by norm_num)
theorem B527021 : Blo 231814 527021 := bbase (se 3 (by rfl) ⟨98816, by rfl⟩ : syracuseStep 527021 = 197633) (by norm_num)
theorem B559813 : Blo 231814 559813 := bbase (se 4 (by rfl) ⟨52482, by rfl⟩ : syracuseStep 559813 = 104965) (by norm_num)
theorem B264901 : Blo 231814 264901 := bbase (se 4 (by rfl) ⟨24834, by rfl⟩ : syracuseStep 264901 = 49669) (by norm_num)
theorem B297685 : Blo 231814 297685 := bbase (se 7 (by rfl) ⟨3488, by rfl⟩ : syracuseStep 297685 = 6977) (by norm_num)
theorem B1182437 : Blo 231814 1182437 := bbase (se 4 (by rfl) ⟨110853, by rfl⟩ : syracuseStep 1182437 = 221707) (by norm_num)
theorem B264937 : Blo 231814 264937 := bbase (se 2 (by rfl) ⟨99351, by rfl⟩ : syracuseStep 264937 = 198703) (by norm_num)
theorem B527093 : Blo 231814 527093 := bbase (se 5 (by rfl) ⟨24707, by rfl⟩ : syracuseStep 527093 = 49415) (by norm_num)
theorem B396029 : Blo 231814 396029 := bbase (se 3 (by rfl) ⟨74255, by rfl⟩ : syracuseStep 396029 = 148511) (by norm_num)
theorem B887557 : Blo 231814 887557 := bbase (se 4 (by rfl) ⟨83208, by rfl⟩ : syracuseStep 887557 = 166417) (by norm_num)
theorem B264973 : Blo 231814 264973 := bbase (se 3 (by rfl) ⟨49682, by rfl⟩ : syracuseStep 264973 = 99365) (by norm_num)
theorem B265009 : Blo 231814 265009 := bbase (se 2 (by rfl) ⟨99378, by rfl⟩ : syracuseStep 265009 = 198757) (by norm_num)
theorem B527165 : Blo 231814 527165 := bbase (se 3 (by rfl) ⟨98843, by rfl⟩ : syracuseStep 527165 = 197687) (by norm_num)
theorem B789317 : Blo 231814 789317 := bbase (se 4 (by rfl) ⟨73998, by rfl⟩ : syracuseStep 789317 = 147997) (by norm_num)
theorem B1084229 : Blo 231814 1084229 := bbase (se 4 (by rfl) ⟨101646, by rfl⟩ : syracuseStep 1084229 = 203293) (by norm_num)
theorem B592717 : Blo 231814 592717 := bbase (se 3 (by rfl) ⟨111134, by rfl⟩ : syracuseStep 592717 = 222269) (by norm_num)
theorem B265045 : Blo 231814 265045 := bbase (se 9 (by rfl) ⟨776, by rfl⟩ : syracuseStep 265045 = 1553) (by norm_num)
theorem B265081 : Blo 231814 265081 := bbase (se 2 (by rfl) ⟨99405, by rfl⟩ : syracuseStep 265081 = 198811) (by norm_num)
theorem B396157 : Blo 231814 396157 := bbase (se 3 (by rfl) ⟨74279, by rfl⟩ : syracuseStep 396157 = 148559) (by norm_num)
theorem B297857 : Blo 231814 297857 := bbase (se 2 (by rfl) ⟨111696, by rfl⟩ : syracuseStep 297857 = 223393) (by norm_num)
theorem B527237 : Blo 231814 527237 := bbase (se 4 (by rfl) ⟨49428, by rfl⟩ : syracuseStep 527237 = 98857) (by norm_num)
theorem B265117 : Blo 231814 265117 := bbase (se 3 (by rfl) ⟨49709, by rfl⟩ : syracuseStep 265117 = 99419) (by norm_num)
theorem B297913 : Blo 231814 297913 := bbase (se 2 (by rfl) ⟨111717, by rfl⟩ : syracuseStep 297913 = 223435) (by norm_num)
theorem B592829 : Blo 231814 592829 := bbase (se 3 (by rfl) ⟨111155, by rfl⟩ : syracuseStep 592829 = 222311) (by norm_num)
theorem B265153 : Blo 231814 265153 := bbase (se 2 (by rfl) ⟨99432, by rfl⟩ : syracuseStep 265153 = 198865) (by norm_num)
theorem B527309 : Blo 231814 527309 := bbase (se 3 (by rfl) ⟨98870, by rfl⟩ : syracuseStep 527309 = 197741) (by norm_num)
theorem B396245 : Blo 231814 396245 := bbase (se 7 (by rfl) ⟨4643, by rfl⟩ : syracuseStep 396245 = 9287) (by norm_num)
theorem B265189 : Blo 231814 265189 := bbase (se 4 (by rfl) ⟨24861, by rfl⟩ : syracuseStep 265189 = 49723) (by norm_num)
theorem B330733 : Blo 231814 330733 := bbase (se 3 (by rfl) ⟨62012, by rfl⟩ : syracuseStep 330733 = 124025) (by norm_num)
theorem B265225 : Blo 231814 265225 := bbase (se 2 (by rfl) ⟨99459, by rfl⟩ : syracuseStep 265225 = 198919) (by norm_num)
theorem B560141 : Blo 231814 560141 := bbase (se 3 (by rfl) ⟨105026, by rfl⟩ : syracuseStep 560141 = 210053) (by norm_num)
theorem B527381 : Blo 231814 527381 := bbase (se 6 (by rfl) ⟨12360, by rfl⟩ : syracuseStep 527381 = 24721) (by norm_num)
theorem B298009 : Blo 231814 298009 := bbase (se 2 (by rfl) ⟨111753, by rfl⟩ : syracuseStep 298009 = 223507) (by norm_num)
theorem B265261 : Blo 231814 265261 := bbase (se 3 (by rfl) ⟨49736, by rfl⟩ : syracuseStep 265261 = 99473) (by norm_num)
theorem B887861 : Blo 231814 887861 := bbase (se 5 (by rfl) ⟨41618, by rfl⟩ : syracuseStep 887861 = 83237) (by norm_num)
theorem B560197 : Blo 231814 560197 := bbase (se 4 (by rfl) ⟨52518, by rfl⟩ : syracuseStep 560197 = 105037) (by norm_num)
theorem B2821205 : Blo 231814 2821205 := bbase (se 8 (by rfl) ⟨16530, by rfl⟩ : syracuseStep 2821205 = 33061) (by norm_num)
theorem B396373 : Blo 231814 396373 := bbase (se 8 (by rfl) ⟨2322, by rfl⟩ : syracuseStep 396373 = 4645) (by norm_num)
theorem B527453 : Blo 231814 527453 := bbase (se 3 (by rfl) ⟨98897, by rfl⟩ : syracuseStep 527453 = 197795) (by norm_num)
theorem B593021 : Blo 231814 593021 := bbase (se 3 (by rfl) ⟨111191, by rfl⟩ : syracuseStep 593021 = 222383) (by norm_num)
theorem B527525 : Blo 231814 527525 := bbase (se 4 (by rfl) ⟨49455, by rfl⟩ : syracuseStep 527525 = 98911) (by norm_num)
theorem B396461 : Blo 231814 396461 := bbase (se 3 (by rfl) ⟨74336, by rfl⟩ : syracuseStep 396461 = 148673) (by norm_num)
theorem B298181 : Blo 231814 298181 := bbase (se 4 (by rfl) ⟨27954, by rfl⟩ : syracuseStep 298181 = 55909) (by norm_num)
theorem B527597 : Blo 231814 527597 := bbase (se 3 (by rfl) ⟨98924, by rfl⟩ : syracuseStep 527597 = 197849) (by norm_num)
theorem B789749 : Blo 231814 789749 := bbase (se 5 (by rfl) ⟨37019, by rfl⟩ : syracuseStep 789749 = 74039) (by norm_num)
theorem B298237 : Blo 231814 298237 := bbase (se 3 (by rfl) ⟨55919, by rfl⟩ : syracuseStep 298237 = 111839) (by norm_num)
theorem B560429 : Blo 231814 560429 := bbase (se 3 (by rfl) ⟨105080, by rfl⟩ : syracuseStep 560429 = 210161) (by norm_num)
theorem B396589 : Blo 231814 396589 := bbase (se 3 (by rfl) ⟨74360, by rfl⟩ : syracuseStep 396589 = 148721) (by norm_num)
theorem B527669 : Blo 231814 527669 := bbase (se 5 (by rfl) ⟨24734, by rfl⟩ : syracuseStep 527669 = 49469) (by norm_num)
theorem B331069 : Blo 231814 331069 := bbase (se 3 (by rfl) ⟨62075, by rfl⟩ : syracuseStep 331069 = 124151) (by norm_num)
theorem B298333 : Blo 231814 298333 := bbase (se 3 (by rfl) ⟨55937, by rfl⟩ : syracuseStep 298333 = 111875) (by norm_num)
theorem B527741 : Blo 231814 527741 := bbase (se 3 (by rfl) ⟨98951, by rfl⟩ : syracuseStep 527741 = 197903) (by norm_num)
theorem B396677 : Blo 231814 396677 := bbase (se 4 (by rfl) ⟨37188, by rfl⟩ : syracuseStep 396677 = 74377) (by norm_num)
theorem B527813 : Blo 231814 527813 := bbase (se 4 (by rfl) ⟨49482, by rfl⟩ : syracuseStep 527813 = 98965) (by norm_num)
theorem B593365 : Blo 231814 593365 := bbase (se 7 (by rfl) ⟨6953, by rfl⟩ : syracuseStep 593365 = 13907) (by norm_num)
theorem B560621 : Blo 231814 560621 := bbase (se 3 (by rfl) ⟨105116, by rfl⟩ : syracuseStep 560621 = 210233) (by norm_num)
theorem B396805 : Blo 231814 396805 := bbase (se 4 (by rfl) ⟨37200, by rfl⟩ : syracuseStep 396805 = 74401) (by norm_num)
theorem B527885 : Blo 231814 527885 := bbase (se 3 (by rfl) ⟨98978, by rfl⟩ : syracuseStep 527885 = 197957) (by norm_num)
theorem B331285 : Blo 231814 331285 := bbase (se 6 (by rfl) ⟨7764, by rfl⟩ : syracuseStep 331285 = 15529) (by norm_num)
theorem B593477 : Blo 231814 593477 := bbase (se 4 (by rfl) ⟨55638, by rfl⟩ : syracuseStep 593477 = 111277) (by norm_num)
theorem B527957 : Blo 231814 527957 := bbase (se 8 (by rfl) ⟨3093, by rfl⟩ : syracuseStep 527957 = 6187) (by norm_num)
theorem B396893 : Blo 231814 396893 := bbase (se 3 (by rfl) ⟨74417, by rfl⟩ : syracuseStep 396893 = 148835) (by norm_num)
theorem B822917 : Blo 231814 822917 := bbase (se 4 (by rfl) ⟨77148, by rfl⟩ : syracuseStep 822917 = 154297) (by norm_num)
theorem B528029 : Blo 231814 528029 := bbase (se 3 (by rfl) ⟨99005, by rfl⟩ : syracuseStep 528029 = 198011) (by norm_num)
theorem B790181 : Blo 231814 790181 := bbase (se 4 (by rfl) ⟨74079, by rfl⟩ : syracuseStep 790181 = 148159) (by norm_num)
theorem B298669 : Blo 231814 298669 := bbase (se 3 (by rfl) ⟨56000, by rfl⟩ : syracuseStep 298669 = 112001) (by norm_num)
theorem B397021 : Blo 231814 397021 := bbase (se 3 (by rfl) ⟨74441, by rfl⟩ : syracuseStep 397021 = 148883) (by norm_num)
theorem B528101 : Blo 231814 528101 := bbase (se 4 (by rfl) ⟨49509, by rfl⟩ : syracuseStep 528101 = 99019) (by norm_num)
theorem B593669 : Blo 231814 593669 := bbase (se 4 (by rfl) ⟨55656, by rfl⟩ : syracuseStep 593669 = 111313) (by norm_num)
theorem B528173 : Blo 231814 528173 := bbase (se 3 (by rfl) ⟨99032, by rfl⟩ : syracuseStep 528173 = 198065) (by norm_num)
theorem B397109 : Blo 231814 397109 := bbase (se 5 (by rfl) ⟨18614, by rfl⟩ : syracuseStep 397109 = 37229) (by norm_num)
theorem B528245 : Blo 231814 528245 := bbase (se 5 (by rfl) ⟨24761, by rfl⟩ : syracuseStep 528245 = 49523) (by norm_num)
theorem B331661 : Blo 231814 331661 := bbase (se 3 (by rfl) ⟨62186, by rfl⟩ : syracuseStep 331661 = 124373) (by norm_num)
theorem B397237 : Blo 231814 397237 := bbase (se 5 (by rfl) ⟨18620, by rfl⟩ : syracuseStep 397237 = 37241) (by norm_num)
theorem B528317 : Blo 231814 528317 := bbase (se 3 (by rfl) ⟨99059, by rfl⟩ : syracuseStep 528317 = 198119) (by norm_num)
theorem B1183733 : Blo 231814 1183733 := bbase (se 5 (by rfl) ⟨55487, by rfl⟩ : syracuseStep 1183733 = 110975) (by norm_num)
theorem B528389 : Blo 231814 528389 := bbase (se 4 (by rfl) ⟨49536, by rfl⟩ : syracuseStep 528389 = 99073) (by norm_num)
theorem B397325 : Blo 231814 397325 := bbase (se 3 (by rfl) ⟨74498, by rfl⟩ : syracuseStep 397325 = 148997) (by norm_num)
theorem B528461 : Blo 231814 528461 := bbase (se 3 (by rfl) ⟨99086, by rfl⟩ : syracuseStep 528461 = 198173) (by norm_num)
theorem B790613 : Blo 231814 790613 := bbase (se 8 (by rfl) ⟨4632, by rfl⟩ : syracuseStep 790613 = 9265) (by norm_num)
theorem B594013 : Blo 231814 594013 := bbase (se 3 (by rfl) ⟨111377, by rfl⟩ : syracuseStep 594013 = 222755) (by norm_num)
theorem B397453 : Blo 231814 397453 := bbase (se 3 (by rfl) ⟨74522, by rfl⟩ : syracuseStep 397453 = 149045) (by norm_num)
theorem B528533 : Blo 231814 528533 := bbase (se 6 (by rfl) ⟨12387, by rfl⟩ : syracuseStep 528533 = 24775) (by norm_num)
theorem B594125 : Blo 231814 594125 := bbase (se 3 (by rfl) ⟨111398, by rfl⟩ : syracuseStep 594125 = 222797) (by norm_num)
theorem B528605 : Blo 231814 528605 := bbase (se 3 (by rfl) ⟨99113, by rfl⟩ : syracuseStep 528605 = 198227) (by norm_num)
theorem B397541 : Blo 231814 397541 := bbase (se 4 (by rfl) ⟨37269, by rfl⟩ : syracuseStep 397541 = 74539) (by norm_num)
theorem B528677 : Blo 231814 528677 := bbase (se 4 (by rfl) ⟨49563, by rfl⟩ : syracuseStep 528677 = 99127) (by norm_num)
theorem B1118549 : Blo 231814 1118549 := bbase (se 10 (by rfl) ⟨1638, by rfl⟩ : syracuseStep 1118549 = 3277) (by norm_num)
theorem B397669 : Blo 231814 397669 := bbase (se 4 (by rfl) ⟨37281, by rfl⟩ : syracuseStep 397669 = 74563) (by norm_num)
theorem B528749 : Blo 231814 528749 := bbase (se 3 (by rfl) ⟨99140, by rfl⟩ : syracuseStep 528749 = 198281) (by norm_num)
theorem B594317 : Blo 231814 594317 := bbase (se 3 (by rfl) ⟨111434, by rfl⟩ : syracuseStep 594317 = 222869) (by norm_num)
theorem B561581 : Blo 231814 561581 := bbase (se 3 (by rfl) ⟨105296, by rfl⟩ : syracuseStep 561581 = 210593) (by norm_num)
theorem B528821 : Blo 231814 528821 := bbase (se 5 (by rfl) ⟨24788, by rfl⟩ : syracuseStep 528821 = 49577) (by norm_num)
theorem B397757 : Blo 231814 397757 := bbase (se 3 (by rfl) ⟨74579, by rfl⟩ : syracuseStep 397757 = 149159) (by norm_num)
theorem B528893 : Blo 231814 528893 := bbase (se 3 (by rfl) ⟨99167, by rfl⟩ : syracuseStep 528893 = 198335) (by norm_num)
theorem B791045 : Blo 231814 791045 := bbase (se 4 (by rfl) ⟨74160, by rfl⟩ : syracuseStep 791045 = 148321) (by norm_num)
theorem B266797 : Blo 231814 266797 := bbase (se 3 (by rfl) ⟨50024, by rfl⟩ : syracuseStep 266797 = 100049) (by norm_num)
theorem B397885 : Blo 231814 397885 := bbase (se 3 (by rfl) ⟨74603, by rfl⟩ : syracuseStep 397885 = 149207) (by norm_num)
theorem B528965 : Blo 231814 528965 := bbase (se 4 (by rfl) ⟨49590, by rfl⟩ : syracuseStep 528965 = 99181) (by norm_num)
theorem B529037 : Blo 231814 529037 := bbase (se 3 (by rfl) ⟨99194, by rfl⟩ : syracuseStep 529037 = 198389) (by norm_num)
theorem B529109 : Blo 231814 529109 := bbase (se 7 (by rfl) ⟨6200, by rfl⟩ : syracuseStep 529109 = 12401) (by norm_num)
theorem B594661 : Blo 231814 594661 := bbase (se 4 (by rfl) ⟨55749, by rfl⟩ : syracuseStep 594661 = 111499) (by norm_num)
theorem B496381 : Blo 231814 496381 := bbase (se 3 (by rfl) ⟨93071, by rfl⟩ : syracuseStep 496381 = 186143) (by norm_num)
theorem B529181 : Blo 231814 529181 := bbase (se 3 (by rfl) ⟨99221, by rfl⟩ : syracuseStep 529181 = 198443) (by norm_num)
theorem B299809 : Blo 231814 299809 := bbase (se 2 (by rfl) ⟨112428, by rfl⟩ : syracuseStep 299809 = 224857) (by norm_num)
theorem B594773 : Blo 231814 594773 := bbase (se 9 (by rfl) ⟨1742, by rfl⟩ : syracuseStep 594773 = 3485) (by norm_num)
theorem B529253 : Blo 231814 529253 := bbase (se 4 (by rfl) ⟨49617, by rfl⟩ : syracuseStep 529253 = 99235) (by norm_num)
theorem B529325 : Blo 231814 529325 := bbase (se 3 (by rfl) ⟨99248, by rfl⟩ : syracuseStep 529325 = 198497) (by norm_num)
theorem B791477 : Blo 231814 791477 := bbase (se 5 (by rfl) ⟨37100, by rfl⟩ : syracuseStep 791477 = 74201) (by norm_num)
theorem B529397 : Blo 231814 529397 := bbase (se 5 (by rfl) ⟨24815, by rfl⟩ : syracuseStep 529397 = 49631) (by norm_num)
theorem B594965 : Blo 231814 594965 := bbase (se 6 (by rfl) ⟨13944, by rfl⟩ : syracuseStep 594965 = 27889) (by norm_num)
theorem B529469 : Blo 231814 529469 := bbase (se 3 (by rfl) ⟨99275, by rfl⟩ : syracuseStep 529469 = 198551) (by norm_num)
theorem B660565 : Blo 231814 660565 := bbase (se 8 (by rfl) ⟨3870, by rfl⟩ : syracuseStep 660565 = 7741) (by norm_num)
theorem B889973 : Blo 231814 889973 := bbase (se 5 (by rfl) ⟨41717, by rfl⟩ : syracuseStep 889973 = 83435) (by norm_num)
theorem B529541 : Blo 231814 529541 := bbase (se 4 (by rfl) ⟨49644, by rfl⟩ : syracuseStep 529541 = 99289) (by norm_num)
theorem B529613 : Blo 231814 529613 := bbase (se 3 (by rfl) ⟨99302, by rfl⟩ : syracuseStep 529613 = 198605) (by norm_num)
theorem B1185029 : Blo 231814 1185029 := bbase (se 4 (by rfl) ⟨111096, by rfl⟩ : syracuseStep 1185029 = 222193) (by norm_num)
theorem B529685 : Blo 231814 529685 := bbase (se 6 (by rfl) ⟨12414, by rfl⟩ : syracuseStep 529685 = 24829) (by norm_num)
theorem B333085 : Blo 231814 333085 := bbase (se 3 (by rfl) ⟨62453, by rfl⟩ : syracuseStep 333085 = 124907) (by norm_num)
theorem B529757 : Blo 231814 529757 := bbase (se 3 (by rfl) ⟨99329, by rfl⟩ : syracuseStep 529757 = 198659) (by norm_num)
theorem B791909 : Blo 231814 791909 := bbase (se 4 (by rfl) ⟨74241, by rfl⟩ : syracuseStep 791909 = 148483) (by norm_num)
theorem B1086821 : Blo 231814 1086821 := bbase (se 4 (by rfl) ⟨101889, by rfl⟩ : syracuseStep 1086821 = 203779) (by norm_num)
theorem B595309 : Blo 231814 595309 := bbase (se 3 (by rfl) ⟨111620, by rfl⟩ : syracuseStep 595309 = 223241) (by norm_num)
theorem B890261 : Blo 231814 890261 := bbase (se 6 (by rfl) ⟨20865, by rfl⟩ : syracuseStep 890261 = 41731) (by norm_num)
theorem B267673 : Blo 231814 267673 := bbase (se 2 (by rfl) ⟨100377, by rfl⟩ : syracuseStep 267673 = 200755) (by norm_num)
theorem B529829 : Blo 231814 529829 := bbase (se 4 (by rfl) ⟨49671, by rfl⟩ : syracuseStep 529829 = 99343) (by norm_num)
theorem B595421 : Blo 231814 595421 := bbase (se 3 (by rfl) ⟨111641, by rfl⟩ : syracuseStep 595421 = 223283) (by norm_num)
theorem B529901 : Blo 231814 529901 := bbase (se 3 (by rfl) ⟨99356, by rfl⟩ : syracuseStep 529901 = 198713) (by norm_num)
theorem B529973 : Blo 231814 529973 := bbase (se 5 (by rfl) ⟨24842, by rfl⟩ : syracuseStep 529973 = 49685) (by norm_num)
theorem B497269 : Blo 231814 497269 := bbase (se 5 (by rfl) ⟨23309, by rfl⟩ : syracuseStep 497269 = 46619) (by norm_num)
theorem B530045 : Blo 231814 530045 := bbase (se 3 (by rfl) ⟨99383, by rfl⟩ : syracuseStep 530045 = 198767) (by norm_num)
theorem B595613 : Blo 231814 595613 := bbase (se 3 (by rfl) ⟨111677, by rfl⟩ : syracuseStep 595613 = 223355) (by norm_num)
theorem B530117 : Blo 231814 530117 := bbase (se 4 (by rfl) ⟨49698, by rfl⟩ : syracuseStep 530117 = 99397) (by norm_num)
theorem B530189 : Blo 231814 530189 := bbase (se 3 (by rfl) ⟨99410, by rfl⟩ : syracuseStep 530189 = 198821) (by norm_num)
theorem B792341 : Blo 231814 792341 := bbase (se 6 (by rfl) ⟨18570, by rfl⟩ : syracuseStep 792341 = 37141) (by norm_num)
theorem B530261 : Blo 231814 530261 := bbase (se 9 (by rfl) ⟨1553, by rfl⟩ : syracuseStep 530261 = 3107) (by norm_num)
theorem B333677 : Blo 231814 333677 := bbase (se 3 (by rfl) ⟨62564, by rfl⟩ : syracuseStep 333677 = 125129) (by norm_num)
theorem B595829 : Blo 231814 595829 := bbase (se 5 (by rfl) ⟨27929, by rfl⟩ : syracuseStep 595829 = 55859) (by norm_num)
theorem B300953 : Blo 231814 300953 := bbase (se 2 (by rfl) ⟨112857, by rfl⟩ : syracuseStep 300953 = 225715) (by norm_num)
theorem B530333 : Blo 231814 530333 := bbase (se 3 (by rfl) ⟨99437, by rfl⟩ : syracuseStep 530333 = 198875) (by norm_num)
theorem B333757 : Blo 231814 333757 := bbase (se 3 (by rfl) ⟨62579, by rfl⟩ : syracuseStep 333757 = 125159) (by norm_num)
theorem B530405 : Blo 231814 530405 := bbase (se 4 (by rfl) ⟨49725, by rfl⟩ : syracuseStep 530405 = 99451) (by norm_num)
theorem B595957 : Blo 231814 595957 := bbase (se 5 (by rfl) ⟨27935, by rfl⟩ : syracuseStep 595957 = 55871) (by norm_num)
theorem B530477 : Blo 231814 530477 := bbase (se 3 (by rfl) ⟨99464, by rfl⟩ : syracuseStep 530477 = 198929) (by norm_num)
theorem B333877 : Blo 231814 333877 := bbase (se 5 (by rfl) ⟨15650, by rfl⟩ : syracuseStep 333877 = 31301) (by norm_num)
theorem B497765 : Blo 231814 497765 := bbase (se 4 (by rfl) ⟨46665, by rfl⟩ : syracuseStep 497765 = 93331) (by norm_num)
theorem B596069 : Blo 231814 596069 := bbase (se 4 (by rfl) ⟨55881, by rfl⟩ : syracuseStep 596069 = 111763) (by norm_num)
theorem B530549 : Blo 231814 530549 := bbase (se 5 (by rfl) ⟨24869, by rfl⟩ : syracuseStep 530549 = 49739) (by norm_num)
theorem B333973 : Blo 231814 333973 := bbase (se 6 (by rfl) ⟨7827, by rfl⟩ : syracuseStep 333973 = 15655) (by norm_num)
theorem B792773 : Blo 231814 792773 := bbase (se 4 (by rfl) ⟨74322, by rfl⟩ : syracuseStep 792773 = 148645) (by norm_num)
theorem B5445845 : Blo 231814 5445845 := bbase (se 7 (by rfl) ⟨63818, by rfl⟩ : syracuseStep 5445845 = 127637) (by norm_num)
theorem B596261 : Blo 231814 596261 := bbase (se 4 (by rfl) ⟨55899, by rfl⟩ : syracuseStep 596261 = 111799) (by norm_num)
theorem B268681 : Blo 231814 268681 := bbase (se 2 (by rfl) ⟨100755, by rfl⟩ : syracuseStep 268681 = 201511) (by norm_num)
theorem B1186325 : Blo 231814 1186325 := bbase (se 6 (by rfl) ⟨27804, by rfl⟩ : syracuseStep 1186325 = 55609) (by norm_num)
theorem B662069 : Blo 231814 662069 := bbase (se 5 (by rfl) ⟨31034, by rfl⟩ : syracuseStep 662069 = 62069) (by norm_num)
theorem B760373 : Blo 231814 760373 := bbase (se 5 (by rfl) ⟨35642, by rfl⟩ : syracuseStep 760373 = 71285) (by norm_num)
theorem B891445 : Blo 231814 891445 := bbase (se 5 (by rfl) ⟨41786, by rfl⟩ : syracuseStep 891445 = 83573) (by norm_num)
theorem B793205 : Blo 231814 793205 := bbase (se 5 (by rfl) ⟨37181, by rfl⟩ : syracuseStep 793205 = 74363) (by norm_num)
theorem B596605 : Blo 231814 596605 := bbase (se 3 (by rfl) ⟨111863, by rfl⟩ : syracuseStep 596605 = 223727) (by norm_num)
theorem B334469 : Blo 231814 334469 := bbase (se 4 (by rfl) ⟨31356, by rfl⟩ : syracuseStep 334469 = 62713) (by norm_num)
theorem B3185365 : Blo 231814 3185365 := bbase (se 7 (by rfl) ⟨37328, by rfl⟩ : syracuseStep 3185365 = 74657) (by norm_num)
theorem B301789 : Blo 231814 301789 := bbase (se 3 (by rfl) ⟨56585, by rfl⟩ : syracuseStep 301789 = 113171) (by norm_num)
theorem B596717 : Blo 231814 596717 := bbase (se 3 (by rfl) ⟨111884, by rfl⟩ : syracuseStep 596717 = 223769) (by norm_num)
theorem B891749 : Blo 231814 891749 := bbase (se 4 (by rfl) ⟨83601, by rfl⟩ : syracuseStep 891749 = 167203) (by norm_num)
theorem B498629 : Blo 231814 498629 := bbase (se 4 (by rfl) ⟨46746, by rfl⟩ : syracuseStep 498629 = 93493) (by norm_num)
theorem B793637 : Blo 231814 793637 := bbase (se 4 (by rfl) ⟨74403, by rfl⟩ : syracuseStep 793637 = 148807) (by norm_num)
theorem B498773 : Blo 231814 498773 := bbase (se 8 (by rfl) ⟨2922, by rfl⟩ : syracuseStep 498773 = 5845) (by norm_num)
theorem B1055861 : Blo 231814 1055861 := bbase (se 5 (by rfl) ⟨49493, by rfl⟩ : syracuseStep 1055861 = 98987) (by norm_num)
theorem B564349 : Blo 231814 564349 := bbase (se 3 (by rfl) ⟨105815, by rfl⟩ : syracuseStep 564349 = 211631) (by norm_num)
theorem B335021 : Blo 231814 335021 := bbase (se 3 (by rfl) ⟨62816, by rfl⟩ : syracuseStep 335021 = 125633) (by norm_num)
theorem B400565 : Blo 231814 400565 := bbase (se 5 (by rfl) ⟨18776, by rfl⟩ : syracuseStep 400565 = 37553) (by norm_num)
theorem B794069 : Blo 231814 794069 := bbase (se 7 (by rfl) ⟨9305, by rfl⟩ : syracuseStep 794069 = 18611) (by norm_num)
theorem B2137589 : Blo 231814 2137589 := bbase (se 5 (by rfl) ⟨100199, by rfl⟩ : syracuseStep 2137589 = 200399) (by norm_num)
theorem B564725 : Blo 231814 564725 := bbase (se 5 (by rfl) ⟨26471, by rfl⟩ : syracuseStep 564725 = 52943) (by norm_num)
theorem B794261 : Blo 231814 794261 := bbase (se 6 (by rfl) ⟨18615, by rfl⟩ : syracuseStep 794261 = 37231) (by norm_num)
theorem B1777301 : Blo 231814 1777301 := bbase (se 6 (by rfl) ⟨41655, by rfl⟩ : syracuseStep 1777301 = 83311) (by norm_num)
theorem B532133 : Blo 231814 532133 := bbase (se 4 (by rfl) ⟨49887, by rfl⟩ : syracuseStep 532133 = 99775) (by norm_num)
theorem B990917 : Blo 231814 990917 := bbase (se 4 (by rfl) ⟨92898, by rfl⟩ : syracuseStep 990917 = 185797) (by norm_num)
theorem B1679093 : Blo 231814 1679093 := bbase (se 5 (by rfl) ⟨78707, by rfl⟩ : syracuseStep 1679093 = 157415) (by norm_num)
theorem B1187621 : Blo 231814 1187621 := bbase (se 4 (by rfl) ⟨111339, by rfl⟩ : syracuseStep 1187621 = 222679) (by norm_num)
theorem B499517 : Blo 231814 499517 := bbase (se 3 (by rfl) ⟨93659, by rfl⟩ : syracuseStep 499517 = 187319) (by norm_num)
theorem B794501 : Blo 231814 794501 := bbase (se 4 (by rfl) ⟨74484, by rfl⟩ : syracuseStep 794501 = 148969) (by norm_num)
theorem B303005 : Blo 231814 303005 := bbase (se 3 (by rfl) ⟨56813, by rfl⟩ : syracuseStep 303005 = 113627) (by norm_num)
theorem B565157 : Blo 231814 565157 := bbase (se 4 (by rfl) ⟨52983, by rfl⟩ : syracuseStep 565157 = 105967) (by norm_num)
theorem B1089445 : Blo 231814 1089445 := bbase (se 4 (by rfl) ⟨102135, by rfl⟩ : syracuseStep 1089445 = 204271) (by norm_num)
theorem B1253333 : Blo 231814 1253333 := bbase (se 7 (by rfl) ⟨14687, by rfl⟩ : syracuseStep 1253333 = 29375) (by norm_num)
theorem B663653 : Blo 231814 663653 := bbase (se 4 (by rfl) ⟨62217, by rfl⟩ : syracuseStep 663653 = 124435) (by norm_num)
theorem B237745 : Blo 231814 237745 := bbase (se 2 (by rfl) ⟨89154, by rfl⟩ : syracuseStep 237745 = 178309) (by norm_num)
theorem B794933 : Blo 231814 794933 := bbase (se 5 (by rfl) ⟨37262, by rfl⟩ : syracuseStep 794933 = 74525) (by norm_num)
theorem B565733 : Blo 231814 565733 := bbase (se 4 (by rfl) ⟨53037, by rfl⟩ : syracuseStep 565733 = 106075) (by norm_num)
theorem B500269 : Blo 231814 500269 := bbase (se 3 (by rfl) ⟨93800, by rfl⟩ : syracuseStep 500269 = 187601) (by norm_num)
theorem B500413 : Blo 231814 500413 := bbase (se 3 (by rfl) ⟨93827, by rfl⟩ : syracuseStep 500413 = 187655) (by norm_num)
theorem B795365 : Blo 231814 795365 := bbase (se 4 (by rfl) ⟨74565, by rfl⟩ : syracuseStep 795365 = 149131) (by norm_num)
theorem B664325 : Blo 231814 664325 := bbase (se 4 (by rfl) ⟨62280, by rfl⟩ : syracuseStep 664325 = 124561) (by norm_num)
theorem B893861 : Blo 231814 893861 := bbase (se 4 (by rfl) ⟨83799, by rfl⟩ : syracuseStep 893861 = 167599) (by norm_num)
theorem B500789 : Blo 231814 500789 := bbase (se 5 (by rfl) ⟨23474, by rfl⟩ : syracuseStep 500789 = 46949) (by norm_num)
theorem B1188917 : Blo 231814 1188917 := bbase (se 5 (by rfl) ⟨55730, by rfl⟩ : syracuseStep 1188917 = 111461) (by norm_num)
theorem B238645 : Blo 231814 238645 := bbase (se 5 (by rfl) ⟨11186, by rfl⟩ : syracuseStep 238645 = 22373) (by norm_num)
theorem B795797 : Blo 231814 795797 := bbase (se 6 (by rfl) ⟨18651, by rfl⟩ : syracuseStep 795797 = 37303) (by norm_num)
theorem B664757 : Blo 231814 664757 := bbase (se 5 (by rfl) ⟨31160, by rfl⟩ : syracuseStep 664757 = 62321) (by norm_num)
theorem B894149 : Blo 231814 894149 := bbase (se 4 (by rfl) ⟨83826, by rfl⟩ : syracuseStep 894149 = 167653) (by norm_num)
theorem B2663765 : Blo 231814 2663765 := bbase (se 12 (by rfl) ⟨975, by rfl⟩ : syracuseStep 2663765 = 1951) (by norm_num)
theorem B238993 : Blo 231814 238993 := bbase (se 2 (by rfl) ⟨89622, by rfl⟩ : syracuseStep 238993 = 179245) (by norm_num)
theorem B501157 : Blo 231814 501157 := bbase (se 4 (by rfl) ⟨46983, by rfl⟩ : syracuseStep 501157 = 93967) (by norm_num)
theorem B4793813 : Blo 231814 4793813 := bbase (se 7 (by rfl) ⟨56177, by rfl⟩ : syracuseStep 4793813 = 112355) (by norm_num)
theorem B2041301 : Blo 231814 2041301 := bbase (se 7 (by rfl) ⟨23921, by rfl⟩ : syracuseStep 2041301 = 47843) (by norm_num)
theorem B632549 : Blo 231814 632549 := bbase (se 4 (by rfl) ⟨59301, by rfl⟩ : syracuseStep 632549 = 118603) (by norm_num)
theorem B665509 : Blo 231814 665509 := bbase (se 4 (by rfl) ⟨62391, by rfl⟩ : syracuseStep 665509 = 124783) (by norm_num)
theorem B1321109 : Blo 231814 1321109 := bbase (se 6 (by rfl) ⟨30963, by rfl⟩ : syracuseStep 1321109 = 61927) (by norm_num)
theorem B1190213 : Blo 231814 1190213 := bbase (se 4 (by rfl) ⟨111582, by rfl⟩ : syracuseStep 1190213 = 223165) (by norm_num)
theorem B895333 : Blo 231814 895333 := bbase (se 4 (by rfl) ⟨83937, by rfl⟩ : syracuseStep 895333 = 167875) (by norm_num)
theorem B567685 : Blo 231814 567685 := bbase (se 4 (by rfl) ⟨53220, by rfl⟩ : syracuseStep 567685 = 106441) (by norm_num)
theorem B1124837 : Blo 231814 1124837 := bbase (se 4 (by rfl) ⟨105453, by rfl⟩ : syracuseStep 1124837 = 210907) (by norm_num)
theorem B338485 : Blo 231814 338485 := bbase (se 5 (by rfl) ⟨15866, by rfl⟩ : syracuseStep 338485 = 31733) (by norm_num)
theorem B2009717 : Blo 231814 2009717 := bbase (se 5 (by rfl) ⟨94205, by rfl⟩ : syracuseStep 2009717 = 188411) (by norm_num)
theorem B633509 : Blo 231814 633509 := bbase (se 4 (by rfl) ⟨59391, by rfl⟩ : syracuseStep 633509 = 118783) (by norm_num)
theorem B502661 : Blo 231814 502661 := bbase (se 4 (by rfl) ⟨47124, by rfl⟩ : syracuseStep 502661 = 94249) (by norm_num)
theorem B502805 : Blo 231814 502805 := bbase (se 6 (by rfl) ⟨11784, by rfl⟩ : syracuseStep 502805 = 23569) (by norm_num)
theorem B371773 : Blo 231814 371773 := bbase (se 3 (by rfl) ⟨69707, by rfl⟩ : syracuseStep 371773 = 139415) (by norm_num)
theorem B535637 : Blo 231814 535637 := bbase (se 8 (by rfl) ⟨3138, by rfl⟩ : syracuseStep 535637 = 6277) (by norm_num)
theorem B339109 : Blo 231814 339109 := bbase (se 4 (by rfl) ⟨31791, by rfl⟩ : syracuseStep 339109 = 63583) (by norm_num)
theorem B535837 : Blo 231814 535837 := bbase (se 3 (by rfl) ⟨100469, by rfl⟩ : syracuseStep 535837 = 200939) (by norm_num)
theorem B503165 : Blo 231814 503165 := bbase (se 3 (by rfl) ⟨94343, by rfl⟩ : syracuseStep 503165 = 188687) (by norm_num)
theorem B470461 : Blo 231814 470461 := bbase (se 3 (by rfl) ⟨88211, by rfl⟩ : syracuseStep 470461 = 176423) (by norm_num)
theorem B372197 : Blo 231814 372197 := bbase (se 4 (by rfl) ⟨34893, by rfl⟩ : syracuseStep 372197 = 69787) (by norm_num)
theorem B1191509 : Blo 231814 1191509 := bbase (se 8 (by rfl) ⟨6981, by rfl⟩ : syracuseStep 1191509 = 13963) (by norm_num)
theorem B994949 : Blo 231814 994949 := bbase (se 4 (by rfl) ⟨93276, by rfl⟩ : syracuseStep 994949 = 186553) (by norm_num)
theorem B372485 : Blo 231814 372485 := bbase (se 4 (by rfl) ⟨34920, by rfl⟩ : syracuseStep 372485 = 69841) (by norm_num)
theorem B372709 : Blo 231814 372709 := bbase (se 4 (by rfl) ⟨34941, by rfl⟩ : syracuseStep 372709 = 69883) (by norm_num)
theorem B602245 : Blo 231814 602245 := bbase (se 4 (by rfl) ⟨56460, by rfl⟩ : syracuseStep 602245 = 112921) (by norm_num)
theorem B2699477 : Blo 231814 2699477 := bbase (se 7 (by rfl) ⟨31634, by rfl⟩ : syracuseStep 2699477 = 63269) (by norm_num)
theorem B1323317 : Blo 231814 1323317 := bbase (se 5 (by rfl) ⟨62030, by rfl⟩ : syracuseStep 1323317 = 124061) (by norm_num)
theorem B471557 : Blo 231814 471557 := bbase (se 4 (by rfl) ⟨44208, by rfl⟩ : syracuseStep 471557 = 88417) (by norm_num)
theorem B471629 : Blo 231814 471629 := bbase (se 3 (by rfl) ⟨88430, by rfl⟩ : syracuseStep 471629 = 176861) (by norm_num)
theorem B668357 : Blo 231814 668357 := bbase (se 4 (by rfl) ⟨62658, by rfl⟩ : syracuseStep 668357 = 125317) (by norm_num)
theorem B1487605 : Blo 231814 1487605 := bbase (se 5 (by rfl) ⟨69731, by rfl⟩ : syracuseStep 1487605 = 139463) (by norm_num)
theorem B1192805 : Blo 231814 1192805 := bbase (se 4 (by rfl) ⟨111825, by rfl⟩ : syracuseStep 1192805 = 223651) (by norm_num)
theorem B373837 : Blo 231814 373837 := bbase (se 3 (by rfl) ⟨70094, by rfl⟩ : syracuseStep 373837 = 140189) (by norm_num)
theorem B275581 : Blo 231814 275581 := bbase (se 3 (by rfl) ⟨51671, by rfl⟩ : syracuseStep 275581 = 103343) (by norm_num)
theorem B537749 : Blo 231814 537749 := bbase (se 6 (by rfl) ⟨12603, by rfl⟩ : syracuseStep 537749 = 25207) (by norm_num)
theorem B1127621 : Blo 231814 1127621 := bbase (se 4 (by rfl) ⟨105714, by rfl⟩ : syracuseStep 1127621 = 211429) (by norm_num)
theorem B472277 : Blo 231814 472277 := bbase (se 7 (by rfl) ⟨5534, by rfl⟩ : syracuseStep 472277 = 11069) (by norm_num)
theorem B996725 : Blo 231814 996725 := bbase (se 5 (by rfl) ⟨46721, by rfl⟩ : syracuseStep 996725 = 93443) (by norm_num)
theorem B636277 : Blo 231814 636277 := bbase (se 5 (by rfl) ⟨29825, by rfl⟩ : syracuseStep 636277 = 59651) (by norm_num)
theorem B308741 : Blo 231814 308741 := bbase (se 4 (by rfl) ⟨28944, by rfl⟩ : syracuseStep 308741 = 57889) (by norm_num)
theorem B374285 : Blo 231814 374285 := bbase (se 3 (by rfl) ⟨70178, by rfl⟩ : syracuseStep 374285 = 140357) (by norm_num)
theorem B440149 : Blo 231814 440149 := bbase (se 9 (by rfl) ⟨1289, by rfl⟩ : syracuseStep 440149 = 2579) (by norm_num)
theorem B505685 : Blo 231814 505685 := bbase (se 9 (by rfl) ⟨1481, by rfl⟩ : syracuseStep 505685 = 2963) (by norm_num)
theorem B669541 : Blo 231814 669541 := bbase (se 4 (by rfl) ⟨62769, by rfl⟩ : syracuseStep 669541 = 125539) (by norm_num)
theorem B440309 : Blo 231814 440309 := bbase (se 5 (by rfl) ⟨20639, by rfl⟩ : syracuseStep 440309 = 41279) (by norm_num)
theorem B604157 : Blo 231814 604157 := bbase (se 3 (by rfl) ⟨113279, by rfl⟩ : syracuseStep 604157 = 226559) (by norm_num)
theorem B669701 : Blo 231814 669701 := bbase (se 4 (by rfl) ⟨62784, by rfl⟩ : syracuseStep 669701 = 125569) (by norm_num)
theorem B4110421 : Blo 231814 4110421 := bbase (se 8 (by rfl) ⟨24084, by rfl⟩ : syracuseStep 4110421 = 48169) (by norm_num)
theorem B440453 : Blo 231814 440453 := bbase (se 4 (by rfl) ⟨41292, by rfl⟩ : syracuseStep 440453 = 82585) (by norm_num)
theorem B669941 : Blo 231814 669941 := bbase (se 5 (by rfl) ⟨31403, by rfl⟩ : syracuseStep 669941 = 62807) (by norm_num)
theorem B473381 : Blo 231814 473381 := bbase (se 4 (by rfl) ⟨44379, by rfl⟩ : syracuseStep 473381 = 88759) (by norm_num)
theorem B997717 : Blo 231814 997717 := bbase (se 10 (by rfl) ⟨1461, by rfl⟩ : syracuseStep 997717 = 2923) (by norm_num)
theorem B440741 : Blo 231814 440741 := bbase (se 4 (by rfl) ⟨41319, by rfl⟩ : syracuseStep 440741 = 82639) (by norm_num)
theorem B670133 : Blo 231814 670133 := bbase (se 5 (by rfl) ⟨31412, by rfl⟩ : syracuseStep 670133 = 62825) (by norm_num)
theorem B506341 : Blo 231814 506341 := bbase (se 4 (by rfl) ⟨47469, by rfl⟩ : syracuseStep 506341 = 94939) (by norm_num)
theorem B1587701 : Blo 231814 1587701 := bbase (se 5 (by rfl) ⟨74423, by rfl⟩ : syracuseStep 1587701 = 148847) (by norm_num)
theorem B440893 : Blo 231814 440893 := bbase (se 3 (by rfl) ⟨82667, by rfl⟩ : syracuseStep 440893 = 165335) (by norm_num)
theorem B506549 : Blo 231814 506549 := bbase (se 5 (by rfl) ⟨23744, by rfl⟩ : syracuseStep 506549 = 47489) (by norm_num)
theorem B441197 : Blo 231814 441197 := bbase (se 3 (by rfl) ⟨82724, by rfl⟩ : syracuseStep 441197 = 165449) (by norm_num)
theorem B375797 : Blo 231814 375797 := bbase (se 5 (by rfl) ⟨17615, by rfl⟩ : syracuseStep 375797 = 35231) (by norm_num)
theorem B375925 : Blo 231814 375925 := bbase (se 5 (by rfl) ⟨17621, by rfl⟩ : syracuseStep 375925 = 35243) (by norm_num)
theorem B1785077 : Blo 231814 1785077 := bbase (se 5 (by rfl) ⟨83675, by rfl⟩ : syracuseStep 1785077 = 167351) (by norm_num)
theorem B4078997 : Blo 231814 4078997 := bbase (se 6 (by rfl) ⟨95601, by rfl⟩ : syracuseStep 4078997 = 191203) (by norm_num)
theorem B671125 : Blo 231814 671125 := bbase (se 6 (by rfl) ⟨15729, by rfl⟩ : syracuseStep 671125 = 31459) (by norm_num)
theorem B441949 : Blo 231814 441949 := bbase (se 3 (by rfl) ⟨82865, by rfl⟩ : syracuseStep 441949 = 165731) (by norm_num)
theorem B573053 : Blo 231814 573053 := bbase (se 3 (by rfl) ⟨107447, by rfl⟩ : syracuseStep 573053 = 214895) (by norm_num)
theorem B442093 : Blo 231814 442093 := bbase (se 3 (by rfl) ⟨82892, by rfl⟩ : syracuseStep 442093 = 165785) (by norm_num)
theorem B442253 : Blo 231814 442253 := bbase (se 3 (by rfl) ⟨82922, by rfl⟩ : syracuseStep 442253 = 165845) (by norm_num)
theorem B442397 : Blo 231814 442397 := bbase (se 3 (by rfl) ⟨82949, by rfl⟩ : syracuseStep 442397 = 165899) (by norm_num)
theorem B278581 : Blo 231814 278581 := bbase (se 5 (by rfl) ⟨13058, by rfl⟩ : syracuseStep 278581 = 26117) (by norm_num)
theorem B278749 : Blo 231814 278749 := bbase (se 3 (by rfl) ⟨52265, by rfl⟩ : syracuseStep 278749 = 104531) (by norm_num)
theorem B835829 : Blo 231814 835829 := bbase (se 5 (by rfl) ⟨39179, by rfl⟩ : syracuseStep 835829 = 78359) (by norm_num)
theorem B1589557 : Blo 231814 1589557 := bbase (se 5 (by rfl) ⟨74510, by rfl⟩ : syracuseStep 1589557 = 149021) (by norm_num)
theorem B442685 : Blo 231814 442685 := bbase (se 3 (by rfl) ⟨83003, by rfl⟩ : syracuseStep 442685 = 166007) (by norm_num)
theorem B278945 : Blo 231814 278945 := bbase (se 2 (by rfl) ⟨104604, by rfl⟩ : syracuseStep 278945 = 209209) (by norm_num)
theorem B442837 : Blo 231814 442837 := bbase (se 7 (by rfl) ⟨5189, by rfl⟩ : syracuseStep 442837 = 10379) (by norm_num)
theorem B377309 : Blo 231814 377309 := bbase (se 3 (by rfl) ⟨70745, by rfl⟩ : syracuseStep 377309 = 141491) (by norm_num)
theorem B475733 : Blo 231814 475733 := bbase (se 8 (by rfl) ⟨2787, by rfl⟩ : syracuseStep 475733 = 5575) (by norm_num)
theorem B705205 : Blo 231814 705205 := bbase (se 5 (by rfl) ⟨33056, by rfl⟩ : syracuseStep 705205 = 66113) (by norm_num)
theorem B443141 : Blo 231814 443141 := bbase (se 4 (by rfl) ⟨41544, by rfl⟩ : syracuseStep 443141 = 83089) (by norm_num)
theorem B377693 : Blo 231814 377693 := bbase (se 3 (by rfl) ⟨70817, by rfl⟩ : syracuseStep 377693 = 141635) (by norm_num)
theorem B443893 : Blo 231814 443893 := bbase (se 5 (by rfl) ⟨20807, by rfl⟩ : syracuseStep 443893 = 41615) (by norm_num)
theorem B444037 : Blo 231814 444037 := bbase (se 4 (by rfl) ⟨41628, by rfl⟩ : syracuseStep 444037 = 83257) (by norm_num)
theorem B3786517 : Blo 231814 3786517 := bbase (se 6 (by rfl) ⟨88746, by rfl⟩ : syracuseStep 3786517 = 177493) (by norm_num)
theorem B444197 : Blo 231814 444197 := bbase (se 4 (by rfl) ⟨41643, by rfl⟩ : syracuseStep 444197 = 83287) (by norm_num)
theorem B444341 : Blo 231814 444341 := bbase (se 5 (by rfl) ⟨20828, by rfl⟩ : syracuseStep 444341 = 41657) (by norm_num)
theorem B280517 : Blo 231814 280517 := bbase (se 4 (by rfl) ⟨26298, by rfl⟩ : syracuseStep 280517 = 52597) (by norm_num)
theorem B280541 : Blo 231814 280541 := bbase (se 3 (by rfl) ⟨52601, by rfl⟩ : syracuseStep 280541 = 105203) (by norm_num)
theorem B247789 : Blo 231814 247789 := bbase (se 3 (by rfl) ⟨46460, by rfl⟩ : syracuseStep 247789 = 92921) (by norm_num)
theorem B509981 : Blo 231814 509981 := bbase (se 3 (by rfl) ⟨95621, by rfl⟩ : syracuseStep 509981 = 191243) (by norm_num)
theorem B313381 : Blo 231814 313381 := bbase (se 4 (by rfl) ⟨29379, by rfl⟩ : syracuseStep 313381 = 58759) (by norm_num)
theorem B444629 : Blo 231814 444629 := bbase (se 7 (by rfl) ⟨5210, by rfl⟩ : syracuseStep 444629 = 10421) (by norm_num)
theorem B1132805 : Blo 231814 1132805 := bbase (se 4 (by rfl) ⟨106200, by rfl⟩ : syracuseStep 1132805 = 212401) (by norm_num)
theorem B280849 : Blo 231814 280849 := bbase (se 2 (by rfl) ⟨105318, by rfl⟩ : syracuseStep 280849 = 210637) (by norm_num)
theorem B477461 : Blo 231814 477461 := bbase (se 6 (by rfl) ⟨11190, by rfl⟩ : syracuseStep 477461 = 22381) (by norm_num)
theorem B444781 : Blo 231814 444781 := bbase (se 3 (by rfl) ⟨83396, by rfl⟩ : syracuseStep 444781 = 166793) (by norm_num)
theorem B248221 : Blo 231814 248221 := bbase (se 3 (by rfl) ⟨46541, by rfl⟩ : syracuseStep 248221 = 93083) (by norm_num)
theorem B281021 : Blo 231814 281021 := bbase (se 3 (by rfl) ⟨52691, by rfl⟩ : syracuseStep 281021 = 105383) (by norm_num)
theorem B248293 : Blo 231814 248293 := bbase (se 4 (by rfl) ⟨23277, by rfl⟩ : syracuseStep 248293 = 46555) (by norm_num)
theorem B281137 : Blo 231814 281137 := bbase (se 2 (by rfl) ⟨105426, by rfl⟩ : syracuseStep 281137 = 210853) (by norm_num)
theorem B281233 : Blo 231814 281233 := bbase (se 2 (by rfl) ⟨105462, by rfl⟩ : syracuseStep 281233 = 210925) (by norm_num)
theorem B1493653 : Blo 231814 1493653 := bbase (se 6 (by rfl) ⟨35007, by rfl⟩ : syracuseStep 1493653 = 70015) (by norm_num)
theorem B445085 : Blo 231814 445085 := bbase (se 3 (by rfl) ⟨83453, by rfl⟩ : syracuseStep 445085 = 166907) (by norm_num)
theorem B281377 : Blo 231814 281377 := bbase (se 2 (by rfl) ⟨105516, by rfl⟩ : syracuseStep 281377 = 211033) (by norm_num)
theorem B1198901 : Blo 231814 1198901 := bbase (se 5 (by rfl) ⟨56198, by rfl⟩ : syracuseStep 1198901 = 112397) (by norm_num)
theorem B248665 : Blo 231814 248665 := bbase (se 2 (by rfl) ⟨93249, by rfl⟩ : syracuseStep 248665 = 186499) (by norm_num)
theorem B314501 : Blo 231814 314501 := bbase (se 4 (by rfl) ⟨29484, by rfl⟩ : syracuseStep 314501 = 58969) (by norm_num)
theorem B249041 : Blo 231814 249041 := bbase (se 2 (by rfl) ⟨93390, by rfl⟩ : syracuseStep 249041 = 186781) (by norm_num)
theorem B1002725 : Blo 231814 1002725 := bbase (se 4 (by rfl) ⟨94005, by rfl⟩ : syracuseStep 1002725 = 188011) (by norm_num)
theorem B249113 : Blo 231814 249113 := bbase (se 2 (by rfl) ⟨93417, by rfl⟩ : syracuseStep 249113 = 186835) (by norm_num)
theorem B445837 : Blo 231814 445837 := bbase (se 3 (by rfl) ⟨83594, by rfl⟩ : syracuseStep 445837 = 167189) (by norm_num)
theorem B249301 : Blo 231814 249301 := bbase (se 7 (by rfl) ⟨2921, by rfl⟩ : syracuseStep 249301 = 5843) (by norm_num)
theorem B1003013 : Blo 231814 1003013 := bbase (se 4 (by rfl) ⟨94032, by rfl⟩ : syracuseStep 1003013 = 188065) (by norm_num)
theorem B445981 : Blo 231814 445981 := bbase (se 3 (by rfl) ⟨83621, by rfl⟩ : syracuseStep 445981 = 167243) (by norm_num)
theorem B347741 : Blo 231814 347741 := bbase (se 3 (by rfl) ⟨65201, by rfl⟩ : syracuseStep 347741 = 130403) (by norm_num)
theorem B347765 : Blo 231814 347765 := bbase (se 5 (by rfl) ⟨16301, by rfl⟩ : syracuseStep 347765 = 32603) (by norm_num)
theorem B347789 : Blo 231814 347789 := bbase (se 3 (by rfl) ⟨65210, by rfl⟩ : syracuseStep 347789 = 130421) (by norm_num)
theorem B249485 : Blo 231814 249485 := bbase (se 3 (by rfl) ⟨46778, by rfl⟩ : syracuseStep 249485 = 93557) (by norm_num)
theorem B347813 : Blo 231814 347813 := bbase (se 4 (by rfl) ⟨32607, by rfl⟩ : syracuseStep 347813 = 65215) (by norm_num)
theorem B347837 : Blo 231814 347837 := bbase (se 3 (by rfl) ⟨65219, by rfl⟩ : syracuseStep 347837 = 130439) (by norm_num)
theorem B446141 : Blo 231814 446141 := bbase (se 3 (by rfl) ⟨83651, by rfl⟩ : syracuseStep 446141 = 167303) (by norm_num)
theorem B347861 : Blo 231814 347861 := bbase (se 7 (by rfl) ⟨4076, by rfl⟩ : syracuseStep 347861 = 8153) (by norm_num)
theorem B347885 : Blo 231814 347885 := bbase (se 3 (by rfl) ⟨65228, by rfl⟩ : syracuseStep 347885 = 130457) (by norm_num)
theorem B315133 : Blo 231814 315133 := bbase (se 3 (by rfl) ⟨59087, by rfl⟩ : syracuseStep 315133 = 118175) (by norm_num)
theorem B347909 : Blo 231814 347909 := bbase (se 4 (by rfl) ⟨32616, by rfl⟩ : syracuseStep 347909 = 65233) (by norm_num)
theorem B347933 : Blo 231814 347933 := bbase (se 3 (by rfl) ⟨65237, by rfl⟩ : syracuseStep 347933 = 130475) (by norm_num)
theorem B347957 : Blo 231814 347957 := bbase (se 5 (by rfl) ⟨16310, by rfl⟩ : syracuseStep 347957 = 32621) (by norm_num)
theorem B347981 : Blo 231814 347981 := bbase (se 3 (by rfl) ⟨65246, by rfl⟩ : syracuseStep 347981 = 130493) (by norm_num)
theorem B446285 : Blo 231814 446285 := bbase (se 3 (by rfl) ⟨83678, by rfl⟩ : syracuseStep 446285 = 167357) (by norm_num)
theorem B348005 : Blo 231814 348005 := bbase (se 4 (by rfl) ⟨32625, by rfl⟩ : syracuseStep 348005 = 65251) (by norm_num)
theorem B348029 : Blo 231814 348029 := bbase (se 3 (by rfl) ⟨65255, by rfl⟩ : syracuseStep 348029 = 130511) (by norm_num)
theorem B348053 : Blo 231814 348053 := bbase (se 6 (by rfl) ⟨8157, by rfl⟩ : syracuseStep 348053 = 16315) (by norm_num)
theorem B348077 : Blo 231814 348077 := bbase (se 3 (by rfl) ⟨65264, by rfl⟩ : syracuseStep 348077 = 130529) (by norm_num)
theorem B348101 : Blo 231814 348101 := bbase (se 4 (by rfl) ⟨32634, by rfl⟩ : syracuseStep 348101 = 65269) (by norm_num)
theorem B348125 : Blo 231814 348125 := bbase (se 3 (by rfl) ⟨65273, by rfl⟩ : syracuseStep 348125 = 130547) (by norm_num)
theorem B348149 : Blo 231814 348149 := bbase (se 5 (by rfl) ⟨16319, by rfl⟩ : syracuseStep 348149 = 32639) (by norm_num)
theorem B348173 : Blo 231814 348173 := bbase (se 3 (by rfl) ⟨65282, by rfl⟩ : syracuseStep 348173 = 130565) (by norm_num)
theorem B348197 : Blo 231814 348197 := bbase (se 4 (by rfl) ⟨32643, by rfl⟩ : syracuseStep 348197 = 65287) (by norm_num)
theorem B348221 : Blo 231814 348221 := bbase (se 3 (by rfl) ⟨65291, by rfl⟩ : syracuseStep 348221 = 130583) (by norm_num)
theorem B348245 : Blo 231814 348245 := bbase (se 8 (by rfl) ⟨2040, by rfl⟩ : syracuseStep 348245 = 4081) (by norm_num)
theorem B348269 : Blo 231814 348269 := bbase (se 3 (by rfl) ⟨65300, by rfl⟩ : syracuseStep 348269 = 130601) (by norm_num)
theorem B446573 : Blo 231814 446573 := bbase (se 3 (by rfl) ⟨83732, by rfl⟩ : syracuseStep 446573 = 167465) (by norm_num)
theorem B348293 : Blo 231814 348293 := bbase (se 4 (by rfl) ⟨32652, by rfl⟩ : syracuseStep 348293 = 65305) (by norm_num)
theorem B348317 : Blo 231814 348317 := bbase (se 3 (by rfl) ⟨65309, by rfl⟩ : syracuseStep 348317 = 130619) (by norm_num)
theorem B348341 : Blo 231814 348341 := bbase (se 5 (by rfl) ⟨16328, by rfl⟩ : syracuseStep 348341 = 32657) (by norm_num)
theorem B348365 : Blo 231814 348365 := bbase (se 3 (by rfl) ⟨65318, by rfl⟩ : syracuseStep 348365 = 130637) (by norm_num)
theorem B2019541 : Blo 231814 2019541 := bbase (se 7 (by rfl) ⟨23666, by rfl⟩ : syracuseStep 2019541 = 47333) (by norm_num)
theorem B348389 : Blo 231814 348389 := bbase (se 4 (by rfl) ⟨32661, by rfl⟩ : syracuseStep 348389 = 65323) (by norm_num)
theorem B1003765 : Blo 231814 1003765 := bbase (se 5 (by rfl) ⟨47051, by rfl⟩ : syracuseStep 1003765 = 94103) (by norm_num)
theorem B348413 : Blo 231814 348413 := bbase (se 3 (by rfl) ⟨65327, by rfl⟩ : syracuseStep 348413 = 130655) (by norm_num)
theorem B446725 : Blo 231814 446725 := bbase (se 4 (by rfl) ⟨41880, by rfl⟩ : syracuseStep 446725 = 83761) (by norm_num)
theorem B348437 : Blo 231814 348437 := bbase (se 6 (by rfl) ⟨8166, by rfl⟩ : syracuseStep 348437 = 16333) (by norm_num)
theorem B348461 : Blo 231814 348461 := bbase (se 3 (by rfl) ⟨65336, by rfl⟩ : syracuseStep 348461 = 130673) (by norm_num)
theorem B348485 : Blo 231814 348485 := bbase (se 4 (by rfl) ⟨32670, by rfl⟩ : syracuseStep 348485 = 65341) (by norm_num)
theorem B348509 : Blo 231814 348509 := bbase (se 3 (by rfl) ⟨65345, by rfl⟩ : syracuseStep 348509 = 130691) (by norm_num)
theorem B381277 : Blo 231814 381277 := bbase (se 3 (by rfl) ⟨71489, by rfl⟩ : syracuseStep 381277 = 142979) (by norm_num)
theorem B348533 : Blo 231814 348533 := bbase (se 5 (by rfl) ⟨16337, by rfl⟩ : syracuseStep 348533 = 32675) (by norm_num)
theorem B250237 : Blo 231814 250237 := bbase (se 3 (by rfl) ⟨46919, by rfl⟩ : syracuseStep 250237 = 93839) (by norm_num)
theorem B348557 : Blo 231814 348557 := bbase (se 3 (by rfl) ⟨65354, by rfl⟩ : syracuseStep 348557 = 130709) (by norm_num)
theorem B348581 : Blo 231814 348581 := bbase (se 4 (by rfl) ⟨32679, by rfl⟩ : syracuseStep 348581 = 65359) (by norm_num)
theorem B348605 : Blo 231814 348605 := bbase (se 3 (by rfl) ⟨65363, by rfl⟩ : syracuseStep 348605 = 130727) (by norm_num)
theorem B250309 : Blo 231814 250309 := bbase (se 4 (by rfl) ⟨23466, by rfl⟩ : syracuseStep 250309 = 46933) (by norm_num)
theorem B348629 : Blo 231814 348629 := bbase (se 7 (by rfl) ⟨4085, by rfl⟩ : syracuseStep 348629 = 8171) (by norm_num)
theorem B283097 : Blo 231814 283097 := bbase (se 2 (by rfl) ⟨106161, by rfl⟩ : syracuseStep 283097 = 212323) (by norm_num)
theorem B348653 : Blo 231814 348653 := bbase (se 3 (by rfl) ⟨65372, by rfl⟩ : syracuseStep 348653 = 130745) (by norm_num)
theorem B348677 : Blo 231814 348677 := bbase (se 4 (by rfl) ⟨32688, by rfl⟩ : syracuseStep 348677 = 65377) (by norm_num)
theorem B348701 : Blo 231814 348701 := bbase (se 3 (by rfl) ⟨65381, by rfl⟩ : syracuseStep 348701 = 130763) (by norm_num)
theorem B348725 : Blo 231814 348725 := bbase (se 5 (by rfl) ⟨16346, by rfl⟩ : syracuseStep 348725 = 32693) (by norm_num)
theorem B447029 : Blo 231814 447029 := bbase (se 5 (by rfl) ⟨20954, by rfl⟩ : syracuseStep 447029 = 41909) (by norm_num)
theorem B348749 : Blo 231814 348749 := bbase (se 3 (by rfl) ⟨65390, by rfl⟩ : syracuseStep 348749 = 130781) (by norm_num)
theorem B283213 : Blo 231814 283213 := bbase (se 3 (by rfl) ⟨53102, by rfl⟩ : syracuseStep 283213 = 106205) (by norm_num)
theorem B348773 : Blo 231814 348773 := bbase (se 4 (by rfl) ⟨32697, by rfl⟩ : syracuseStep 348773 = 65395) (by norm_num)
theorem B250489 : Blo 231814 250489 := bbase (se 2 (by rfl) ⟨93933, by rfl⟩ : syracuseStep 250489 = 187867) (by norm_num)
theorem B348797 : Blo 231814 348797 := bbase (se 3 (by rfl) ⟨65399, by rfl⟩ : syracuseStep 348797 = 130799) (by norm_num)
theorem B348821 : Blo 231814 348821 := bbase (se 6 (by rfl) ⟨8175, by rfl⟩ : syracuseStep 348821 = 16351) (by norm_num)
theorem B283285 : Blo 231814 283285 := bbase (se 6 (by rfl) ⟨6639, by rfl⟩ : syracuseStep 283285 = 13279) (by norm_num)
theorem B348845 : Blo 231814 348845 := bbase (se 3 (by rfl) ⟨65408, by rfl⟩ : syracuseStep 348845 = 130817) (by norm_num)
theorem B348869 : Blo 231814 348869 := bbase (se 4 (by rfl) ⟨32706, by rfl⟩ : syracuseStep 348869 = 65413) (by norm_num)
theorem B348893 : Blo 231814 348893 := bbase (se 3 (by rfl) ⟨65417, by rfl⟩ : syracuseStep 348893 = 130835) (by norm_num)
theorem B348917 : Blo 231814 348917 := bbase (se 5 (by rfl) ⟨16355, by rfl⟩ : syracuseStep 348917 = 32711) (by norm_num)
theorem B1430261 : Blo 231814 1430261 := bbase (se 5 (by rfl) ⟨67043, by rfl⟩ : syracuseStep 1430261 = 134087) (by norm_num)
theorem B348941 : Blo 231814 348941 := bbase (se 3 (by rfl) ⟨65426, by rfl⟩ : syracuseStep 348941 = 130853) (by norm_num)
theorem B840469 : Blo 231814 840469 := bbase (se 6 (by rfl) ⟨19698, by rfl⟩ : syracuseStep 840469 = 39397) (by norm_num)
theorem B348965 : Blo 231814 348965 := bbase (se 4 (by rfl) ⟨32715, by rfl⟩ : syracuseStep 348965 = 65431) (by norm_num)
theorem B348989 : Blo 231814 348989 := bbase (se 3 (by rfl) ⟨65435, by rfl⟩ : syracuseStep 348989 = 130871) (by norm_num)
theorem B349013 : Blo 231814 349013 := bbase (se 9 (by rfl) ⟨1022, by rfl⟩ : syracuseStep 349013 = 2045) (by norm_num)
theorem B349037 : Blo 231814 349037 := bbase (se 3 (by rfl) ⟨65444, by rfl⟩ : syracuseStep 349037 = 130889) (by norm_num)
theorem B447365 : Blo 231814 447365 := bbase (se 4 (by rfl) ⟨41940, by rfl⟩ : syracuseStep 447365 = 83881) (by norm_num)
theorem B349061 : Blo 231814 349061 := bbase (se 4 (by rfl) ⟨32724, by rfl⟩ : syracuseStep 349061 = 65449) (by norm_num)
theorem B447373 : Blo 231814 447373 := bbase (se 3 (by rfl) ⟨83882, by rfl⟩ : syracuseStep 447373 = 167765) (by norm_num)
theorem B349085 : Blo 231814 349085 := bbase (se 3 (by rfl) ⟨65453, by rfl⟩ : syracuseStep 349085 = 130907) (by norm_num)
theorem B349109 : Blo 231814 349109 := bbase (se 5 (by rfl) ⟨16364, by rfl⟩ : syracuseStep 349109 = 32729) (by norm_num)
theorem B349133 : Blo 231814 349133 := bbase (se 3 (by rfl) ⟨65462, by rfl⟩ : syracuseStep 349133 = 130925) (by norm_num)
theorem B1004501 : Blo 231814 1004501 := bbase (se 7 (by rfl) ⟨11771, by rfl⟩ : syracuseStep 1004501 = 23543) (by norm_num)
theorem B349157 : Blo 231814 349157 := bbase (se 4 (by rfl) ⟨32733, by rfl⟩ : syracuseStep 349157 = 65467) (by norm_num)
theorem B349181 : Blo 231814 349181 := bbase (se 3 (by rfl) ⟨65471, by rfl⟩ : syracuseStep 349181 = 130943) (by norm_num)
theorem B349205 : Blo 231814 349205 := bbase (se 6 (by rfl) ⟨8184, by rfl⟩ : syracuseStep 349205 = 16369) (by norm_num)
theorem B349229 : Blo 231814 349229 := bbase (se 3 (by rfl) ⟨65480, by rfl⟩ : syracuseStep 349229 = 130961) (by norm_num)
theorem B250933 : Blo 231814 250933 := bbase (se 5 (by rfl) ⟨11762, by rfl⟩ : syracuseStep 250933 = 23525) (by norm_num)
theorem B349253 : Blo 231814 349253 := bbase (se 4 (by rfl) ⟨32742, by rfl⟩ : syracuseStep 349253 = 65485) (by norm_num)
theorem B349277 : Blo 231814 349277 := bbase (se 3 (by rfl) ⟨65489, by rfl⟩ : syracuseStep 349277 = 130979) (by norm_num)
theorem B349301 : Blo 231814 349301 := bbase (se 5 (by rfl) ⟨16373, by rfl⟩ : syracuseStep 349301 = 32747) (by norm_num)
theorem B349325 : Blo 231814 349325 := bbase (se 3 (by rfl) ⟨65498, by rfl⟩ : syracuseStep 349325 = 130997) (by norm_num)
theorem B349349 : Blo 231814 349349 := bbase (se 4 (by rfl) ⟨32751, by rfl⟩ : syracuseStep 349349 = 65503) (by norm_num)
theorem B251057 : Blo 231814 251057 := bbase (se 2 (by rfl) ⟨94146, by rfl⟩ : syracuseStep 251057 = 188293) (by norm_num)
theorem B349373 : Blo 231814 349373 := bbase (se 3 (by rfl) ⟨65507, by rfl⟩ : syracuseStep 349373 = 131015) (by norm_num)
theorem B349397 : Blo 231814 349397 := bbase (se 7 (by rfl) ⟨4094, by rfl⟩ : syracuseStep 349397 = 8189) (by norm_num)
theorem B349421 : Blo 231814 349421 := bbase (se 3 (by rfl) ⟨65516, by rfl⟩ : syracuseStep 349421 = 131033) (by norm_num)
theorem B349445 : Blo 231814 349445 := bbase (se 4 (by rfl) ⟨32760, by rfl⟩ : syracuseStep 349445 = 65521) (by norm_num)
theorem B349469 : Blo 231814 349469 := bbase (se 3 (by rfl) ⟨65525, by rfl⟩ : syracuseStep 349469 = 131051) (by norm_num)
theorem B349493 : Blo 231814 349493 := bbase (se 5 (by rfl) ⟨16382, by rfl⟩ : syracuseStep 349493 = 32765) (by norm_num)
theorem B349517 : Blo 231814 349517 := bbase (se 3 (by rfl) ⟨65534, by rfl⟩ : syracuseStep 349517 = 131069) (by norm_num)
theorem B349541 : Blo 231814 349541 := bbase (se 4 (by rfl) ⟨32769, by rfl⟩ : syracuseStep 349541 = 65539) (by norm_num)
theorem B349565 : Blo 231814 349565 := bbase (se 3 (by rfl) ⟨65543, by rfl⟩ : syracuseStep 349565 = 131087) (by norm_num)
theorem B349589 : Blo 231814 349589 := bbase (se 6 (by rfl) ⟨8193, by rfl⟩ : syracuseStep 349589 = 16387) (by norm_num)
theorem B349613 : Blo 231814 349613 := bbase (se 3 (by rfl) ⟨65552, by rfl⟩ : syracuseStep 349613 = 131105) (by norm_num)
theorem B251309 : Blo 231814 251309 := bbase (se 3 (by rfl) ⟨47120, by rfl⟩ : syracuseStep 251309 = 94241) (by norm_num)
theorem B1496501 : Blo 231814 1496501 := bbase (se 5 (by rfl) ⟨70148, by rfl⟩ : syracuseStep 1496501 = 140297) (by norm_num)
theorem B349637 : Blo 231814 349637 := bbase (se 4 (by rfl) ⟨32778, by rfl⟩ : syracuseStep 349637 = 65557) (by norm_num)
theorem B316885 : Blo 231814 316885 := bbase (se 7 (by rfl) ⟨3713, by rfl⟩ : syracuseStep 316885 = 7427) (by norm_num)
theorem B349661 : Blo 231814 349661 := bbase (se 3 (by rfl) ⟨65561, by rfl⟩ : syracuseStep 349661 = 131123) (by norm_num)
theorem B349685 : Blo 231814 349685 := bbase (se 5 (by rfl) ⟨16391, by rfl⟩ : syracuseStep 349685 = 32783) (by norm_num)
theorem B349709 : Blo 231814 349709 := bbase (se 3 (by rfl) ⟨65570, by rfl⟩ : syracuseStep 349709 = 131141) (by norm_num)
theorem B349733 : Blo 231814 349733 := bbase (se 4 (by rfl) ⟨32787, by rfl⟩ : syracuseStep 349733 = 65575) (by norm_num)
theorem B349757 : Blo 231814 349757 := bbase (se 3 (by rfl) ⟨65579, by rfl⟩ : syracuseStep 349757 = 131159) (by norm_num)
theorem B349781 : Blo 231814 349781 := bbase (se 8 (by rfl) ⟨2049, by rfl⟩ : syracuseStep 349781 = 4099) (by norm_num)
theorem B349805 : Blo 231814 349805 := bbase (se 3 (by rfl) ⟨65588, by rfl⟩ : syracuseStep 349805 = 131177) (by norm_num)
theorem B349829 : Blo 231814 349829 := bbase (se 4 (by rfl) ⟨32796, by rfl⟩ : syracuseStep 349829 = 65593) (by norm_num)
theorem B1070725 : Blo 231814 1070725 := bbase (se 4 (by rfl) ⟨100380, by rfl⟩ : syracuseStep 1070725 = 200761) (by norm_num)
theorem B349853 : Blo 231814 349853 := bbase (se 3 (by rfl) ⟨65597, by rfl⟩ : syracuseStep 349853 = 131195) (by norm_num)
theorem B349877 : Blo 231814 349877 := bbase (se 5 (by rfl) ⟨16400, by rfl⟩ : syracuseStep 349877 = 32801) (by norm_num)
theorem B349901 : Blo 231814 349901 := bbase (se 3 (by rfl) ⟨65606, by rfl⟩ : syracuseStep 349901 = 131213) (by norm_num)
theorem B349925 : Blo 231814 349925 := bbase (se 4 (by rfl) ⟨32805, by rfl⟩ : syracuseStep 349925 = 65611) (by norm_num)
theorem B349949 : Blo 231814 349949 := bbase (se 3 (by rfl) ⟨65615, by rfl⟩ : syracuseStep 349949 = 131231) (by norm_num)
theorem B349973 : Blo 231814 349973 := bbase (se 6 (by rfl) ⟨8202, by rfl⟩ : syracuseStep 349973 = 16405) (by norm_num)
theorem B349997 : Blo 231814 349997 := bbase (se 3 (by rfl) ⟨65624, by rfl⟩ : syracuseStep 349997 = 131249) (by norm_num)
theorem B350021 : Blo 231814 350021 := bbase (se 4 (by rfl) ⟨32814, by rfl⟩ : syracuseStep 350021 = 65629) (by norm_num)
theorem B350045 : Blo 231814 350045 := bbase (se 3 (by rfl) ⟨65633, by rfl⟩ : syracuseStep 350045 = 131267) (by norm_num)
theorem B251753 : Blo 231814 251753 := bbase (se 2 (by rfl) ⟨94407, by rfl⟩ : syracuseStep 251753 = 188815) (by norm_num)
theorem B350069 : Blo 231814 350069 := bbase (se 5 (by rfl) ⟨16409, by rfl⟩ : syracuseStep 350069 = 32819) (by norm_num)
theorem B350093 : Blo 231814 350093 := bbase (se 3 (by rfl) ⟨65642, by rfl⟩ : syracuseStep 350093 = 131285) (by norm_num)
theorem B350117 : Blo 231814 350117 := bbase (se 4 (by rfl) ⟨32823, by rfl⟩ : syracuseStep 350117 = 65647) (by norm_num)
theorem B350141 : Blo 231814 350141 := bbase (se 3 (by rfl) ⟨65651, by rfl⟩ : syracuseStep 350141 = 131303) (by norm_num)
theorem B350165 : Blo 231814 350165 := bbase (se 7 (by rfl) ⟨4103, by rfl⟩ : syracuseStep 350165 = 8207) (by norm_num)
theorem B1333205 : Blo 231814 1333205 := bbase (se 7 (by rfl) ⟨15623, by rfl⟩ : syracuseStep 1333205 = 31247) (by norm_num)
theorem B2414549 : Blo 231814 2414549 := bbase (se 7 (by rfl) ⟨28295, by rfl⟩ : syracuseStep 2414549 = 56591) (by norm_num)
theorem B350189 : Blo 231814 350189 := bbase (se 3 (by rfl) ⟨65660, by rfl⟩ : syracuseStep 350189 = 131321) (by norm_num)
theorem B350213 : Blo 231814 350213 := bbase (se 4 (by rfl) ⟨32832, by rfl⟩ : syracuseStep 350213 = 65665) (by norm_num)
theorem B350237 : Blo 231814 350237 := bbase (se 3 (by rfl) ⟨65669, by rfl⟩ : syracuseStep 350237 = 131339) (by norm_num)
theorem B350261 : Blo 231814 350261 := bbase (se 5 (by rfl) ⟨16418, by rfl⟩ : syracuseStep 350261 = 32837) (by norm_num)
theorem B350285 : Blo 231814 350285 := bbase (se 3 (by rfl) ⟨65678, by rfl⟩ : syracuseStep 350285 = 131357) (by norm_num)
theorem B710741 : Blo 231814 710741 := bbase (se 8 (by rfl) ⟨4164, by rfl⟩ : syracuseStep 710741 = 8329) (by norm_num)
theorem B350309 : Blo 231814 350309 := bbase (se 4 (by rfl) ⟨32841, by rfl⟩ : syracuseStep 350309 = 65683) (by norm_num)
theorem B350333 : Blo 231814 350333 := bbase (se 3 (by rfl) ⟨65687, by rfl⟩ : syracuseStep 350333 = 131375) (by norm_num)
theorem B1136773 : Blo 231814 1136773 := bbase (se 4 (by rfl) ⟨106572, by rfl⟩ : syracuseStep 1136773 = 213145) (by norm_num)
theorem B743573 : Blo 231814 743573 := bbase (se 6 (by rfl) ⟨17427, by rfl⟩ : syracuseStep 743573 = 34855) (by norm_num)
theorem B350357 : Blo 231814 350357 := bbase (se 6 (by rfl) ⟨8211, by rfl⟩ : syracuseStep 350357 = 16423) (by norm_num)
theorem B350381 : Blo 231814 350381 := bbase (se 3 (by rfl) ⟨65696, by rfl⟩ : syracuseStep 350381 = 131393) (by norm_num)
theorem B350405 : Blo 231814 350405 := bbase (se 4 (by rfl) ⟨32850, by rfl⟩ : syracuseStep 350405 = 65701) (by norm_num)
theorem B350429 : Blo 231814 350429 := bbase (se 3 (by rfl) ⟨65705, by rfl⟩ : syracuseStep 350429 = 131411) (by norm_num)
theorem B350453 : Blo 231814 350453 := bbase (se 5 (by rfl) ⟨16427, by rfl⟩ : syracuseStep 350453 = 32855) (by norm_num)
theorem B350477 : Blo 231814 350477 := bbase (se 3 (by rfl) ⟨65714, by rfl⟩ : syracuseStep 350477 = 131429) (by norm_num)
theorem B743701 : Blo 231814 743701 := bbase (se 6 (by rfl) ⟨17430, by rfl⟩ : syracuseStep 743701 = 34861) (by norm_num)
theorem B350501 : Blo 231814 350501 := bbase (se 4 (by rfl) ⟨32859, by rfl⟩ : syracuseStep 350501 = 65719) (by norm_num)
theorem B350525 : Blo 231814 350525 := bbase (se 3 (by rfl) ⟨65723, by rfl⟩ : syracuseStep 350525 = 131447) (by norm_num)
theorem B350549 : Blo 231814 350549 := bbase (se 10 (by rfl) ⟨513, by rfl⟩ : syracuseStep 350549 = 1027) (by norm_num)
theorem B350573 : Blo 231814 350573 := bbase (se 3 (by rfl) ⟨65732, by rfl⟩ : syracuseStep 350573 = 131465) (by norm_num)
theorem B350597 : Blo 231814 350597 := bbase (se 4 (by rfl) ⟨32868, by rfl⟩ : syracuseStep 350597 = 65737) (by norm_num)
theorem B350621 : Blo 231814 350621 := bbase (se 3 (by rfl) ⟨65741, by rfl⟩ : syracuseStep 350621 = 131483) (by norm_num)
theorem B350645 : Blo 231814 350645 := bbase (se 5 (by rfl) ⟨16436, by rfl⟩ : syracuseStep 350645 = 32873) (by norm_num)
theorem B350669 : Blo 231814 350669 := bbase (se 3 (by rfl) ⟨65750, by rfl⟩ : syracuseStep 350669 = 131501) (by norm_num)
theorem B350693 : Blo 231814 350693 := bbase (se 4 (by rfl) ⟨32877, by rfl⟩ : syracuseStep 350693 = 65755) (by norm_num)
theorem B350717 : Blo 231814 350717 := bbase (se 3 (by rfl) ⟨65759, by rfl⟩ : syracuseStep 350717 = 131519) (by norm_num)
theorem B743957 : Blo 231814 743957 := bbase (se 6 (by rfl) ⟨17436, by rfl⟩ : syracuseStep 743957 = 34873) (by norm_num)
theorem B350741 : Blo 231814 350741 := bbase (se 6 (by rfl) ⟨8220, by rfl⟩ : syracuseStep 350741 = 16441) (by norm_num)
theorem B350765 : Blo 231814 350765 := bbase (se 3 (by rfl) ⟨65768, by rfl⟩ : syracuseStep 350765 = 131537) (by norm_num)
theorem B285245 : Blo 231814 285245 := bbase (se 3 (by rfl) ⟨53483, by rfl⟩ : syracuseStep 285245 = 106967) (by norm_num)
theorem B350789 : Blo 231814 350789 := bbase (se 4 (by rfl) ⟨32886, by rfl⟩ : syracuseStep 350789 = 65773) (by norm_num)
theorem B350813 : Blo 231814 350813 := bbase (se 3 (by rfl) ⟨65777, by rfl⟩ : syracuseStep 350813 = 131555) (by norm_num)
theorem B350837 : Blo 231814 350837 := bbase (se 5 (by rfl) ⟨16445, by rfl⟩ : syracuseStep 350837 = 32891) (by norm_num)
theorem B350861 : Blo 231814 350861 := bbase (se 3 (by rfl) ⟨65786, by rfl⟩ : syracuseStep 350861 = 131573) (by norm_num)
theorem B350885 : Blo 231814 350885 := bbase (se 4 (by rfl) ⟨32895, by rfl⟩ : syracuseStep 350885 = 65791) (by norm_num)
theorem B350909 : Blo 231814 350909 := bbase (se 3 (by rfl) ⟨65795, by rfl⟩ : syracuseStep 350909 = 131591) (by norm_num)
theorem B350933 : Blo 231814 350933 := bbase (se 7 (by rfl) ⟨4112, by rfl⟩ : syracuseStep 350933 = 8225) (by norm_num)
theorem B350957 : Blo 231814 350957 := bbase (se 3 (by rfl) ⟨65804, by rfl⟩ : syracuseStep 350957 = 131609) (by norm_num)
theorem B350981 : Blo 231814 350981 := bbase (se 4 (by rfl) ⟨32904, by rfl⟩ : syracuseStep 350981 = 65809) (by norm_num)
theorem B351005 : Blo 231814 351005 := bbase (se 3 (by rfl) ⟨65813, by rfl⟩ : syracuseStep 351005 = 131627) (by norm_num)
theorem B351029 : Blo 231814 351029 := bbase (se 5 (by rfl) ⟨16454, by rfl⟩ : syracuseStep 351029 = 32909) (by norm_num)
theorem B318269 : Blo 231814 318269 := bbase (se 3 (by rfl) ⟨59675, by rfl⟩ : syracuseStep 318269 = 119351) (by norm_num)
theorem B351053 : Blo 231814 351053 := bbase (se 3 (by rfl) ⟨65822, by rfl⟩ : syracuseStep 351053 = 131645) (by norm_num)
theorem B351077 : Blo 231814 351077 := bbase (se 4 (by rfl) ⟨32913, by rfl⟩ : syracuseStep 351077 = 65827) (by norm_num)
theorem B351101 : Blo 231814 351101 := bbase (se 3 (by rfl) ⟨65831, by rfl⟩ : syracuseStep 351101 = 131663) (by norm_num)
theorem B351125 : Blo 231814 351125 := bbase (se 6 (by rfl) ⟨8229, by rfl⟩ : syracuseStep 351125 = 16459) (by norm_num)
theorem B351149 : Blo 231814 351149 := bbase (se 3 (by rfl) ⟨65840, by rfl⟩ : syracuseStep 351149 = 131681) (by norm_num)
theorem B351173 : Blo 231814 351173 := bbase (se 4 (by rfl) ⟨32922, by rfl⟩ : syracuseStep 351173 = 65845) (by norm_num)
theorem B351197 : Blo 231814 351197 := bbase (se 3 (by rfl) ⟨65849, by rfl⟩ : syracuseStep 351197 = 131699) (by norm_num)
theorem B351221 : Blo 231814 351221 := bbase (se 5 (by rfl) ⟨16463, by rfl⟩ : syracuseStep 351221 = 32927) (by norm_num)
theorem B351245 : Blo 231814 351245 := bbase (se 3 (by rfl) ⟨65858, by rfl⟩ : syracuseStep 351245 = 131717) (by norm_num)
theorem B351269 : Blo 231814 351269 := bbase (se 4 (by rfl) ⟨32931, by rfl⟩ : syracuseStep 351269 = 65863) (by norm_num)
theorem B351293 : Blo 231814 351293 := bbase (se 3 (by rfl) ⟨65867, by rfl⟩ : syracuseStep 351293 = 131735) (by norm_num)
theorem B351317 : Blo 231814 351317 := bbase (se 8 (by rfl) ⟨2058, by rfl⟩ : syracuseStep 351317 = 4117) (by norm_num)
theorem B351341 : Blo 231814 351341 := bbase (se 3 (by rfl) ⟨65876, by rfl⟩ : syracuseStep 351341 = 131753) (by norm_num)
theorem B351365 : Blo 231814 351365 := bbase (se 4 (by rfl) ⟨32940, by rfl⟩ : syracuseStep 351365 = 65881) (by norm_num)
theorem B973973 : Blo 231814 973973 := bbase (se 6 (by rfl) ⟨22827, by rfl⟩ : syracuseStep 973973 = 45655) (by norm_num)
theorem B351389 : Blo 231814 351389 := bbase (se 3 (by rfl) ⟨65885, by rfl⟩ : syracuseStep 351389 = 131771) (by norm_num)
theorem B351413 : Blo 231814 351413 := bbase (se 5 (by rfl) ⟨16472, by rfl⟩ : syracuseStep 351413 = 32945) (by norm_num)
theorem B351437 : Blo 231814 351437 := bbase (se 3 (by rfl) ⟨65894, by rfl⟩ : syracuseStep 351437 = 131789) (by norm_num)
theorem B351461 : Blo 231814 351461 := bbase (se 4 (by rfl) ⟨32949, by rfl⟩ : syracuseStep 351461 = 65899) (by norm_num)
theorem B351485 : Blo 231814 351485 := bbase (se 3 (by rfl) ⟨65903, by rfl⟩ : syracuseStep 351485 = 131807) (by norm_num)
theorem B351509 : Blo 231814 351509 := bbase (se 6 (by rfl) ⟨8238, by rfl⟩ : syracuseStep 351509 = 16477) (by norm_num)
theorem B351533 : Blo 231814 351533 := bbase (se 3 (by rfl) ⟨65912, by rfl⟩ : syracuseStep 351533 = 131825) (by norm_num)
theorem B351557 : Blo 231814 351557 := bbase (se 4 (by rfl) ⟨32958, by rfl⟩ : syracuseStep 351557 = 65917) (by norm_num)
theorem B351581 : Blo 231814 351581 := bbase (se 3 (by rfl) ⟨65921, by rfl⟩ : syracuseStep 351581 = 131843) (by norm_num)
theorem B351605 : Blo 231814 351605 := bbase (se 5 (by rfl) ⟨16481, by rfl⟩ : syracuseStep 351605 = 32963) (by norm_num)
theorem B351629 : Blo 231814 351629 := bbase (se 3 (by rfl) ⟨65930, by rfl⟩ : syracuseStep 351629 = 131861) (by norm_num)
theorem B351653 : Blo 231814 351653 := bbase (se 4 (by rfl) ⟨32967, by rfl⟩ : syracuseStep 351653 = 65935) (by norm_num)
theorem B1072549 : Blo 231814 1072549 := bbase (se 4 (by rfl) ⟨100551, by rfl⟩ : syracuseStep 1072549 = 201103) (by norm_num)
theorem B351677 : Blo 231814 351677 := bbase (se 3 (by rfl) ⟨65939, by rfl⟩ : syracuseStep 351677 = 131879) (by norm_num)
theorem B2252245 : Blo 231814 2252245 := bbase (se 7 (by rfl) ⟨26393, by rfl⟩ : syracuseStep 2252245 = 52787) (by norm_num)
theorem B351701 : Blo 231814 351701 := bbase (se 7 (by rfl) ⟨4121, by rfl⟩ : syracuseStep 351701 = 8243) (by norm_num)
theorem B712165 : Blo 231814 712165 := bbase (se 4 (by rfl) ⟨66765, by rfl⟩ : syracuseStep 712165 = 133531) (by norm_num)
theorem B351725 : Blo 231814 351725 := bbase (se 3 (by rfl) ⟨65948, by rfl⟩ : syracuseStep 351725 = 131897) (by norm_num)
theorem B351749 : Blo 231814 351749 := bbase (se 4 (by rfl) ⟨32976, by rfl⟩ : syracuseStep 351749 = 65953) (by norm_num)
theorem B351773 : Blo 231814 351773 := bbase (se 3 (by rfl) ⟨65957, by rfl⟩ : syracuseStep 351773 = 131915) (by norm_num)
theorem B351797 : Blo 231814 351797 := bbase (se 5 (by rfl) ⟨16490, by rfl⟩ : syracuseStep 351797 = 32981) (by norm_num)
theorem B351821 : Blo 231814 351821 := bbase (se 3 (by rfl) ⟨65966, by rfl⟩ : syracuseStep 351821 = 131933) (by norm_num)
theorem B351845 : Blo 231814 351845 := bbase (se 4 (by rfl) ⟨32985, by rfl⟩ : syracuseStep 351845 = 65971) (by norm_num)
theorem B351869 : Blo 231814 351869 := bbase (se 3 (by rfl) ⟨65975, by rfl⟩ : syracuseStep 351869 = 131951) (by norm_num)
theorem B941701 : Blo 231814 941701 := bbase (se 4 (by rfl) ⟨88284, by rfl⟩ : syracuseStep 941701 = 176569) (by norm_num)
theorem B351893 : Blo 231814 351893 := bbase (se 6 (by rfl) ⟨8247, by rfl⟩ : syracuseStep 351893 = 16495) (by norm_num)
theorem B351917 : Blo 231814 351917 := bbase (se 3 (by rfl) ⟨65984, by rfl⟩ : syracuseStep 351917 = 131969) (by norm_num)
theorem B351941 : Blo 231814 351941 := bbase (se 4 (by rfl) ⟨32994, by rfl⟩ : syracuseStep 351941 = 65989) (by norm_num)
theorem B351965 : Blo 231814 351965 := bbase (se 3 (by rfl) ⟨65993, by rfl⟩ : syracuseStep 351965 = 131987) (by norm_num)
theorem B351989 : Blo 231814 351989 := bbase (se 5 (by rfl) ⟨16499, by rfl⟩ : syracuseStep 351989 = 32999) (by norm_num)
theorem B352013 : Blo 231814 352013 := bbase (se 3 (by rfl) ⟨66002, by rfl⟩ : syracuseStep 352013 = 132005) (by norm_num)
theorem B352037 : Blo 231814 352037 := bbase (se 4 (by rfl) ⟨33003, by rfl⟩ : syracuseStep 352037 = 66007) (by norm_num)
theorem B352061 : Blo 231814 352061 := bbase (se 3 (by rfl) ⟨66011, by rfl⟩ : syracuseStep 352061 = 132023) (by norm_num)
theorem B352085 : Blo 231814 352085 := bbase (se 9 (by rfl) ⟨1031, by rfl⟩ : syracuseStep 352085 = 2063) (by norm_num)
theorem B352109 : Blo 231814 352109 := bbase (se 3 (by rfl) ⟨66020, by rfl⟩ : syracuseStep 352109 = 132041) (by norm_num)
theorem B352133 : Blo 231814 352133 := bbase (se 4 (by rfl) ⟨33012, by rfl⟩ : syracuseStep 352133 = 66025) (by norm_num)
theorem B352157 : Blo 231814 352157 := bbase (se 3 (by rfl) ⟨66029, by rfl⟩ : syracuseStep 352157 = 132059) (by norm_num)
theorem B352181 : Blo 231814 352181 := bbase (se 5 (by rfl) ⟨16508, by rfl⟩ : syracuseStep 352181 = 33017) (by norm_num)
theorem B352205 : Blo 231814 352205 := bbase (se 3 (by rfl) ⟨66038, by rfl⟩ : syracuseStep 352205 = 132077) (by norm_num)
theorem B352229 : Blo 231814 352229 := bbase (se 4 (by rfl) ⟨33021, by rfl⟩ : syracuseStep 352229 = 66043) (by norm_num)
theorem B352253 : Blo 231814 352253 := bbase (se 3 (by rfl) ⟨66047, by rfl⟩ : syracuseStep 352253 = 132095) (by norm_num)
theorem B352277 : Blo 231814 352277 := bbase (se 6 (by rfl) ⟨8256, by rfl⟩ : syracuseStep 352277 = 16513) (by norm_num)
theorem B352301 : Blo 231814 352301 := bbase (se 3 (by rfl) ⟨66056, by rfl⟩ : syracuseStep 352301 = 132113) (by norm_num)
theorem B352325 : Blo 231814 352325 := bbase (se 4 (by rfl) ⟨33030, by rfl⟩ : syracuseStep 352325 = 66061) (by norm_num)
theorem B680021 : Blo 231814 680021 := bbase (se 8 (by rfl) ⟨3984, by rfl⟩ : syracuseStep 680021 = 7969) (by norm_num)
theorem B352349 : Blo 231814 352349 := bbase (se 3 (by rfl) ⟨66065, by rfl⟩ : syracuseStep 352349 = 132131) (by norm_num)
theorem B352373 : Blo 231814 352373 := bbase (se 5 (by rfl) ⟨16517, by rfl⟩ : syracuseStep 352373 = 33035) (by norm_num)
theorem B352397 : Blo 231814 352397 := bbase (se 3 (by rfl) ⟨66074, by rfl⟩ : syracuseStep 352397 = 132149) (by norm_num)
theorem B352421 : Blo 231814 352421 := bbase (se 4 (by rfl) ⟨33039, by rfl⟩ : syracuseStep 352421 = 66079) (by norm_num)
theorem B352445 : Blo 231814 352445 := bbase (se 3 (by rfl) ⟨66083, by rfl⟩ : syracuseStep 352445 = 132167) (by norm_num)
theorem B352469 : Blo 231814 352469 := bbase (se 7 (by rfl) ⟨4130, by rfl⟩ : syracuseStep 352469 = 8261) (by norm_num)
theorem B352493 : Blo 231814 352493 := bbase (se 3 (by rfl) ⟨66092, by rfl⟩ : syracuseStep 352493 = 132185) (by norm_num)
theorem B352517 : Blo 231814 352517 := bbase (se 4 (by rfl) ⟨33048, by rfl⟩ : syracuseStep 352517 = 66097) (by norm_num)
theorem B352541 : Blo 231814 352541 := bbase (se 3 (by rfl) ⟨66101, by rfl⟩ : syracuseStep 352541 = 132203) (by norm_num)
theorem B352565 : Blo 231814 352565 := bbase (se 5 (by rfl) ⟨16526, by rfl⟩ : syracuseStep 352565 = 33053) (by norm_num)
theorem B352589 : Blo 231814 352589 := bbase (se 3 (by rfl) ⟨66110, by rfl⟩ : syracuseStep 352589 = 132221) (by norm_num)
theorem B352613 : Blo 231814 352613 := bbase (se 4 (by rfl) ⟨33057, by rfl⟩ : syracuseStep 352613 = 66115) (by norm_num)
theorem B680293 : Blo 231814 680293 := bbase (se 4 (by rfl) ⟨63777, by rfl⟩ : syracuseStep 680293 = 127555) (by norm_num)
theorem B352637 : Blo 231814 352637 := bbase (se 3 (by rfl) ⟨66119, by rfl⟩ : syracuseStep 352637 = 132239) (by norm_num)
theorem B352661 : Blo 231814 352661 := bbase (se 6 (by rfl) ⟨8265, by rfl⟩ : syracuseStep 352661 = 16531) (by norm_num)
theorem B352685 : Blo 231814 352685 := bbase (se 3 (by rfl) ⟨66128, by rfl⟩ : syracuseStep 352685 = 132257) (by norm_num)
theorem B582061 : Blo 231814 582061 := bbase (se 3 (by rfl) ⟨109136, by rfl⟩ : syracuseStep 582061 = 218273) (by norm_num)
theorem B352709 : Blo 231814 352709 := bbase (se 4 (by rfl) ⟨33066, by rfl⟩ : syracuseStep 352709 = 66133) (by norm_num)
theorem B1761749 : Blo 231814 1761749 := bbase (se 7 (by rfl) ⟨20645, by rfl⟩ : syracuseStep 1761749 = 41291) (by norm_num)
theorem B713173 : Blo 231814 713173 := bbase (se 7 (by rfl) ⟨8357, by rfl⟩ : syracuseStep 713173 = 16715) (by norm_num)
theorem B352733 : Blo 231814 352733 := bbase (se 3 (by rfl) ⟨66137, by rfl⟩ : syracuseStep 352733 = 132275) (by norm_num)
theorem B352757 : Blo 231814 352757 := bbase (se 5 (by rfl) ⟨16535, by rfl⟩ : syracuseStep 352757 = 33071) (by norm_num)
theorem B352781 : Blo 231814 352781 := bbase (se 3 (by rfl) ⟨66146, by rfl⟩ : syracuseStep 352781 = 132293) (by norm_num)
theorem B254497 : Blo 231814 254497 := bbase (se 2 (by rfl) ⟨95436, by rfl⟩ : syracuseStep 254497 = 190873) (by norm_num)
theorem B352805 : Blo 231814 352805 := bbase (se 4 (by rfl) ⟨33075, by rfl⟩ : syracuseStep 352805 = 66151) (by norm_num)
theorem B352829 : Blo 231814 352829 := bbase (se 3 (by rfl) ⟨66155, by rfl⟩ : syracuseStep 352829 = 132311) (by norm_num)
theorem B352853 : Blo 231814 352853 := bbase (se 8 (by rfl) ⟨2067, by rfl⟩ : syracuseStep 352853 = 4135) (by norm_num)
theorem B352877 : Blo 231814 352877 := bbase (se 3 (by rfl) ⟨66164, by rfl⟩ : syracuseStep 352877 = 132329) (by norm_num)
theorem B352901 : Blo 231814 352901 := bbase (se 4 (by rfl) ⟨33084, by rfl⟩ : syracuseStep 352901 = 66169) (by norm_num)
theorem B352925 : Blo 231814 352925 := bbase (se 3 (by rfl) ⟨66173, by rfl⟩ : syracuseStep 352925 = 132347) (by norm_num)
theorem B1204901 : Blo 231814 1204901 := bbase (se 4 (by rfl) ⟨112959, by rfl⟩ : syracuseStep 1204901 = 225919) (by norm_num)
theorem B352949 : Blo 231814 352949 := bbase (se 5 (by rfl) ⟨16544, by rfl⟩ : syracuseStep 352949 = 33089) (by norm_num)
theorem B352973 : Blo 231814 352973 := bbase (se 3 (by rfl) ⟨66182, by rfl⟩ : syracuseStep 352973 = 132365) (by norm_num)
theorem B352997 : Blo 231814 352997 := bbase (se 4 (by rfl) ⟨33093, by rfl⟩ : syracuseStep 352997 = 66187) (by norm_num)
theorem B418549 : Blo 231814 418549 := bbase (se 5 (by rfl) ⟨19619, by rfl⟩ : syracuseStep 418549 = 39239) (by norm_num)
theorem B353021 : Blo 231814 353021 := bbase (se 3 (by rfl) ⟨66191, by rfl⟩ : syracuseStep 353021 = 132383) (by norm_num)
theorem B1008389 : Blo 231814 1008389 := bbase (se 4 (by rfl) ⟨94536, by rfl⟩ : syracuseStep 1008389 = 189073) (by norm_num)
theorem B353045 : Blo 231814 353045 := bbase (se 6 (by rfl) ⟨8274, by rfl⟩ : syracuseStep 353045 = 16549) (by norm_num)
theorem B353069 : Blo 231814 353069 := bbase (se 3 (by rfl) ⟨66200, by rfl⟩ : syracuseStep 353069 = 132401) (by norm_num)
theorem B1696565 : Blo 231814 1696565 := bbase (se 5 (by rfl) ⟨79526, by rfl⟩ : syracuseStep 1696565 = 159053) (by norm_num)
theorem B418621 : Blo 231814 418621 := bbase (se 3 (by rfl) ⟨78491, by rfl⟩ : syracuseStep 418621 = 156983) (by norm_num)
theorem B353093 : Blo 231814 353093 := bbase (se 4 (by rfl) ⟨33102, by rfl⟩ : syracuseStep 353093 = 66205) (by norm_num)
theorem B353117 : Blo 231814 353117 := bbase (se 3 (by rfl) ⟨66209, by rfl⟩ : syracuseStep 353117 = 132419) (by norm_num)
theorem B353141 : Blo 231814 353141 := bbase (se 5 (by rfl) ⟨16553, by rfl⟩ : syracuseStep 353141 = 33107) (by norm_num)
theorem B353165 : Blo 231814 353165 := bbase (se 3 (by rfl) ⟨66218, by rfl⟩ : syracuseStep 353165 = 132437) (by norm_num)
theorem B942997 : Blo 231814 942997 := bbase (se 6 (by rfl) ⟨22101, by rfl⟩ : syracuseStep 942997 = 44203) (by norm_num)
theorem B746405 : Blo 231814 746405 := bbase (se 4 (by rfl) ⟨69975, by rfl⟩ : syracuseStep 746405 = 139951) (by norm_num)
theorem B353189 : Blo 231814 353189 := bbase (se 4 (by rfl) ⟨33111, by rfl⟩ : syracuseStep 353189 = 66223) (by norm_num)
theorem B353213 : Blo 231814 353213 := bbase (se 3 (by rfl) ⟨66227, by rfl⟩ : syracuseStep 353213 = 132455) (by norm_num)
theorem B1369045 : Blo 231814 1369045 := bbase (se 7 (by rfl) ⟨16043, by rfl⟩ : syracuseStep 1369045 = 32087) (by norm_num)
theorem B353237 : Blo 231814 353237 := bbase (se 7 (by rfl) ⟨4139, by rfl⟩ : syracuseStep 353237 = 8279) (by norm_num)
theorem B353261 : Blo 231814 353261 := bbase (se 3 (by rfl) ⟨66236, by rfl⟩ : syracuseStep 353261 = 132473) (by norm_num)
theorem B353285 : Blo 231814 353285 := bbase (se 4 (by rfl) ⟨33120, by rfl⟩ : syracuseStep 353285 = 66241) (by norm_num)
theorem B353309 : Blo 231814 353309 := bbase (se 3 (by rfl) ⟨66245, by rfl⟩ : syracuseStep 353309 = 132491) (by norm_num)
theorem B353333 : Blo 231814 353333 := bbase (se 5 (by rfl) ⟨16562, by rfl⟩ : syracuseStep 353333 = 33125) (by norm_num)
theorem B353357 : Blo 231814 353357 := bbase (se 3 (by rfl) ⟨66254, by rfl⟩ : syracuseStep 353357 = 132509) (by norm_num)
theorem B353381 : Blo 231814 353381 := bbase (se 4 (by rfl) ⟨33129, by rfl⟩ : syracuseStep 353381 = 66259) (by norm_num)
theorem B353405 : Blo 231814 353405 := bbase (se 3 (by rfl) ⟨66263, by rfl⟩ : syracuseStep 353405 = 132527) (by norm_num)
theorem B353429 : Blo 231814 353429 := bbase (se 6 (by rfl) ⟨8283, by rfl⟩ : syracuseStep 353429 = 16567) (by norm_num)
theorem B353453 : Blo 231814 353453 := bbase (se 3 (by rfl) ⟨66272, by rfl⟩ : syracuseStep 353453 = 132545) (by norm_num)
theorem B353477 : Blo 231814 353477 := bbase (se 4 (by rfl) ⟨33138, by rfl⟩ : syracuseStep 353477 = 66277) (by norm_num)
theorem B353501 : Blo 231814 353501 := bbase (se 3 (by rfl) ⟨66281, by rfl⟩ : syracuseStep 353501 = 132563) (by norm_num)
theorem B255197 : Blo 231814 255197 := bbase (se 3 (by rfl) ⟨47849, by rfl⟩ : syracuseStep 255197 = 95699) (by norm_num)
theorem B353525 : Blo 231814 353525 := bbase (se 5 (by rfl) ⟨16571, by rfl⟩ : syracuseStep 353525 = 33143) (by norm_num)
theorem B353549 : Blo 231814 353549 := bbase (se 3 (by rfl) ⟨66290, by rfl⟩ : syracuseStep 353549 = 132581) (by norm_num)
theorem B353573 : Blo 231814 353573 := bbase (se 4 (by rfl) ⟨33147, by rfl⟩ : syracuseStep 353573 = 66295) (by norm_num)
theorem B353597 : Blo 231814 353597 := bbase (se 3 (by rfl) ⟨66299, by rfl⟩ : syracuseStep 353597 = 132599) (by norm_num)
theorem B353621 : Blo 231814 353621 := bbase (se 12 (by rfl) ⟨129, by rfl⟩ : syracuseStep 353621 = 259) (by norm_num)
theorem B353645 : Blo 231814 353645 := bbase (se 3 (by rfl) ⟨66308, by rfl⟩ : syracuseStep 353645 = 132617) (by norm_num)
theorem B353669 : Blo 231814 353669 := bbase (se 4 (by rfl) ⟨33156, by rfl⟩ : syracuseStep 353669 = 66313) (by norm_num)
theorem B353693 : Blo 231814 353693 := bbase (se 3 (by rfl) ⟨66317, by rfl⟩ : syracuseStep 353693 = 132635) (by norm_num)
theorem B353717 : Blo 231814 353717 := bbase (se 5 (by rfl) ⟨16580, by rfl⟩ : syracuseStep 353717 = 33161) (by norm_num)
theorem B419629 : Blo 231814 419629 := bbase (se 3 (by rfl) ⟨78680, by rfl⟩ : syracuseStep 419629 = 157361) (by norm_num)
theorem B6022997 : Blo 231814 6022997 := bbase (se 9 (by rfl) ⟨17645, by rfl⟩ : syracuseStep 6022997 = 35291) (by norm_num)
theorem B419717 : Blo 231814 419717 := bbase (se 4 (by rfl) ⟨39348, by rfl⟩ : syracuseStep 419717 = 78697) (by norm_num)
theorem B911477 : Blo 231814 911477 := bbase (se 5 (by rfl) ⟨42725, by rfl⟩ : syracuseStep 911477 = 85451) (by norm_num)
theorem B420005 : Blo 231814 420005 := bbase (se 4 (by rfl) ⟨39375, by rfl⟩ : syracuseStep 420005 = 78751) (by norm_num)
theorem B747749 : Blo 231814 747749 := bbase (se 4 (by rfl) ⟨70101, by rfl⟩ : syracuseStep 747749 = 140203) (by norm_num)
theorem B4483349 : Blo 231814 4483349 := bbase (se 6 (by rfl) ⟨105078, by rfl⟩ : syracuseStep 4483349 = 210157) (by norm_num)
theorem B420221 : Blo 231814 420221 := bbase (se 3 (by rfl) ⟨78791, by rfl⟩ : syracuseStep 420221 = 157583) (by norm_num)
theorem B1272469 : Blo 231814 1272469 := bbase (se 6 (by rfl) ⟨29823, by rfl⟩ : syracuseStep 1272469 = 59647) (by norm_num)
theorem B453413 : Blo 231814 453413 := bbase (se 4 (by rfl) ⟨42507, by rfl⟩ : syracuseStep 453413 = 85015) (by norm_num)
theorem B1174661 : Blo 231814 1174661 := bbase (se 4 (by rfl) ⟨110124, by rfl⟩ : syracuseStep 1174661 = 220249) (by norm_num)
theorem B421157 : Blo 231814 421157 := bbase (se 4 (by rfl) ⟨39483, by rfl⟩ : syracuseStep 421157 = 78967) (by norm_num)
theorem B421237 : Blo 231814 421237 := bbase (se 5 (by rfl) ⟨19745, by rfl⟩ : syracuseStep 421237 = 39491) (by norm_num)
theorem B323125 : Blo 231814 323125 := bbase (se 5 (by rfl) ⟨15146, by rfl⟩ : syracuseStep 323125 = 30293) (by norm_num)
theorem B2256437 : Blo 231814 2256437 := bbase (se 5 (by rfl) ⟨105770, by rfl⟩ : syracuseStep 2256437 = 211541) (by norm_num)
theorem B454717 : Blo 231814 454717 := bbase (se 3 (by rfl) ⟨85259, by rfl⟩ : syracuseStep 454717 = 170519) (by norm_num)
theorem B782405 : Blo 231814 782405 := bbase (se 4 (by rfl) ⟨73350, by rfl⟩ : syracuseStep 782405 = 146701) (by norm_num)
theorem B749749 : Blo 231814 749749 := bbase (se 5 (by rfl) ⟨35144, by rfl⟩ : syracuseStep 749749 = 70289) (by norm_num)
theorem B1175957 : Blo 231814 1175957 := bbase (se 6 (by rfl) ⟨27561, by rfl⟩ : syracuseStep 1175957 = 55123) (by norm_num)
theorem B782837 : Blo 231814 782837 := bbase (se 5 (by rfl) ⟨36695, by rfl⟩ : syracuseStep 782837 = 73391) (by norm_num)
theorem B356933 : Blo 231814 356933 := bbase (se 4 (by rfl) ⟨33462, by rfl⟩ : syracuseStep 356933 = 66925) (by norm_num)
theorem B1995637 : Blo 231814 1995637 := bbase (se 5 (by rfl) ⟨93545, by rfl⟩ : syracuseStep 1995637 = 187091) (by norm_num)
theorem B783269 : Blo 231814 783269 := bbase (se 4 (by rfl) ⟨73431, by rfl⟩ : syracuseStep 783269 = 146863) (by norm_num)
theorem B848933 : Blo 231814 848933 := bbase (se 4 (by rfl) ⟨79587, by rfl⟩ : syracuseStep 848933 = 159175) (by norm_num)
theorem B586885 : Blo 231814 586885 := bbase (se 4 (by rfl) ⟨55020, by rfl⟩ : syracuseStep 586885 = 110041) (by norm_num)
theorem B586997 : Blo 231814 586997 := bbase (se 5 (by rfl) ⟨27515, by rfl⟩ : syracuseStep 586997 = 55031) (by norm_num)
theorem B947477 : Blo 231814 947477 := bbase (se 6 (by rfl) ⟨22206, by rfl⟩ : syracuseStep 947477 = 44413) (by norm_num)
theorem B783701 : Blo 231814 783701 := bbase (se 13 (by rfl) ⟨143, by rfl⟩ : syracuseStep 783701 = 287) (by norm_num)
theorem B521621 : Blo 231814 521621 := bbase (se 6 (by rfl) ⟨12225, by rfl⟩ : syracuseStep 521621 = 24451) (by norm_num)
theorem B587189 : Blo 231814 587189 := bbase (se 5 (by rfl) ⟨27524, by rfl⟩ : syracuseStep 587189 = 55049) (by norm_num)
theorem B521693 : Blo 231814 521693 := bbase (se 3 (by rfl) ⟨97817, by rfl⟩ : syracuseStep 521693 = 195635) (by norm_num)
theorem B652789 : Blo 231814 652789 := bbase (se 5 (by rfl) ⟨30599, by rfl⟩ : syracuseStep 652789 = 61199) (by norm_num)
theorem B882197 : Blo 231814 882197 := bbase (se 6 (by rfl) ⟨20676, by rfl⟩ : syracuseStep 882197 = 41353) (by norm_num)
theorem B521765 : Blo 231814 521765 := bbase (se 4 (by rfl) ⟨48915, by rfl⟩ : syracuseStep 521765 = 97831) (by norm_num)
theorem B521837 : Blo 231814 521837 := bbase (se 3 (by rfl) ⟨97844, by rfl⟩ : syracuseStep 521837 = 195689) (by norm_num)
theorem B1177253 : Blo 231814 1177253 := bbase (se 4 (by rfl) ⟨110367, by rfl⟩ : syracuseStep 1177253 = 220735) (by norm_num)
theorem B521909 : Blo 231814 521909 := bbase (se 5 (by rfl) ⟨24464, by rfl⟩ : syracuseStep 521909 = 48929) (by norm_num)
theorem B521981 : Blo 231814 521981 := bbase (se 3 (by rfl) ⟨97871, by rfl⟩ : syracuseStep 521981 = 195743) (by norm_num)
theorem B784133 : Blo 231814 784133 := bbase (se 4 (by rfl) ⟨73512, by rfl⟩ : syracuseStep 784133 = 147025) (by norm_num)
theorem B587533 : Blo 231814 587533 := bbase (se 3 (by rfl) ⟨110162, by rfl⟩ : syracuseStep 587533 = 220325) (by norm_num)
theorem B882485 : Blo 231814 882485 := bbase (se 5 (by rfl) ⟨41366, by rfl⟩ : syracuseStep 882485 = 82733) (by norm_num)
theorem B522053 : Blo 231814 522053 := bbase (se 4 (by rfl) ⟨48942, by rfl⟩ : syracuseStep 522053 = 97885) (by norm_num)
theorem B358229 : Blo 231814 358229 := bbase (se 9 (by rfl) ⟨1049, by rfl⟩ : syracuseStep 358229 = 2099) (by norm_num)
theorem B1341269 : Blo 231814 1341269 := bbase (se 9 (by rfl) ⟨3929, by rfl⟩ : syracuseStep 1341269 = 7859) (by norm_num)
theorem B587645 : Blo 231814 587645 := bbase (se 3 (by rfl) ⟨110183, by rfl⟩ : syracuseStep 587645 = 220367) (by norm_num)
theorem B522125 : Blo 231814 522125 := bbase (se 3 (by rfl) ⟨97898, by rfl⟩ : syracuseStep 522125 = 195797) (by norm_num)
theorem B522197 : Blo 231814 522197 := bbase (se 7 (by rfl) ⟨6119, by rfl⟩ : syracuseStep 522197 = 12239) (by norm_num)
theorem B358357 : Blo 231814 358357 := bbase (se 7 (by rfl) ⟨4199, by rfl⟩ : syracuseStep 358357 = 8399) (by norm_num)
theorem B391189 : Blo 231814 391189 := bbase (se 6 (by rfl) ⟨9168, by rfl⟩ : syracuseStep 391189 = 18337) (by norm_num)
theorem B522269 : Blo 231814 522269 := bbase (se 3 (by rfl) ⟨97925, by rfl⟩ : syracuseStep 522269 = 195851) (by norm_num)
theorem B587837 : Blo 231814 587837 := bbase (se 3 (by rfl) ⟨110219, by rfl⟩ : syracuseStep 587837 = 220439) (by norm_num)
theorem B522341 : Blo 231814 522341 := bbase (se 4 (by rfl) ⟨48969, by rfl⟩ : syracuseStep 522341 = 97939) (by norm_num)
theorem B391277 : Blo 231814 391277 := bbase (se 3 (by rfl) ⟨73364, by rfl⟩ : syracuseStep 391277 = 146729) (by norm_num)
theorem B522413 : Blo 231814 522413 := bbase (se 3 (by rfl) ⟨97952, by rfl⟩ : syracuseStep 522413 = 195905) (by norm_num)
theorem B784565 : Blo 231814 784565 := bbase (se 5 (by rfl) ⟨36776, by rfl⟩ : syracuseStep 784565 = 73553) (by norm_num)
theorem B391405 : Blo 231814 391405 := bbase (se 3 (by rfl) ⟨73388, by rfl⟩ : syracuseStep 391405 = 146777) (by norm_num)
theorem B522485 : Blo 231814 522485 := bbase (se 5 (by rfl) ⟨24491, by rfl⟩ : syracuseStep 522485 = 48983) (by norm_num)
theorem B522557 : Blo 231814 522557 := bbase (se 3 (by rfl) ⟨97979, by rfl⟩ : syracuseStep 522557 = 195959) (by norm_num)
theorem B391493 : Blo 231814 391493 := bbase (se 4 (by rfl) ⟨36702, by rfl⟩ : syracuseStep 391493 = 73405) (by norm_num)
theorem B522629 : Blo 231814 522629 := bbase (se 4 (by rfl) ⟨48996, by rfl⟩ : syracuseStep 522629 = 97993) (by norm_num)
theorem B588181 : Blo 231814 588181 := bbase (se 6 (by rfl) ⟨13785, by rfl⟩ : syracuseStep 588181 = 27571) (by norm_num)
theorem B391621 : Blo 231814 391621 := bbase (se 4 (by rfl) ⟨36714, by rfl⟩ : syracuseStep 391621 = 73429) (by norm_num)
theorem B522701 : Blo 231814 522701 := bbase (se 3 (by rfl) ⟨98006, by rfl⟩ : syracuseStep 522701 = 196013) (by norm_num)
theorem B588293 : Blo 231814 588293 := bbase (se 4 (by rfl) ⟨55152, by rfl⟩ : syracuseStep 588293 = 110305) (by norm_num)
theorem B522773 : Blo 231814 522773 := bbase (se 6 (by rfl) ⟨12252, by rfl⟩ : syracuseStep 522773 = 24505) (by norm_num)
theorem B391709 : Blo 231814 391709 := bbase (se 3 (by rfl) ⟨73445, by rfl⟩ : syracuseStep 391709 = 146891) (by norm_num)
theorem B522845 : Blo 231814 522845 := bbase (se 3 (by rfl) ⟨98033, by rfl⟩ : syracuseStep 522845 = 196067) (by norm_num)
theorem B293473 : Blo 231814 293473 := bbase (se 2 (by rfl) ⟨110052, by rfl⟩ : syracuseStep 293473 = 220105) (by norm_num)
theorem B784997 : Blo 231814 784997 := bbase (se 4 (by rfl) ⟨73593, by rfl⟩ : syracuseStep 784997 = 147187) (by norm_num)
theorem B391837 : Blo 231814 391837 := bbase (se 3 (by rfl) ⟨73469, by rfl⟩ : syracuseStep 391837 = 146939) (by norm_num)
theorem B522917 : Blo 231814 522917 := bbase (se 4 (by rfl) ⟨49023, by rfl⟩ : syracuseStep 522917 = 98047) (by norm_num)
theorem B260797 : Blo 231814 260797 := bbase (se 3 (by rfl) ⟨48899, by rfl⟩ : syracuseStep 260797 = 97799) (by norm_num)
theorem B588485 : Blo 231814 588485 := bbase (se 4 (by rfl) ⟨55170, by rfl⟩ : syracuseStep 588485 = 110341) (by norm_num)
theorem B260833 : Blo 231814 260833 := bbase (se 2 (by rfl) ⟨97812, by rfl⟩ : syracuseStep 260833 = 195625) (by norm_num)
theorem B522989 : Blo 231814 522989 := bbase (se 3 (by rfl) ⟨98060, by rfl⟩ : syracuseStep 522989 = 196121) (by norm_num)
theorem B391925 : Blo 231814 391925 := bbase (se 5 (by rfl) ⟨18371, by rfl⟩ : syracuseStep 391925 = 36743) (by norm_num)
theorem B260869 : Blo 231814 260869 := bbase (se 4 (by rfl) ⟨24456, by rfl⟩ : syracuseStep 260869 = 48913) (by norm_num)
theorem B293645 : Blo 231814 293645 := bbase (se 3 (by rfl) ⟨55058, by rfl⟩ : syracuseStep 293645 = 110117) (by norm_num)
theorem B260905 : Blo 231814 260905 := bbase (se 2 (by rfl) ⟨97839, by rfl⟩ : syracuseStep 260905 = 195679) (by norm_num)
theorem B523061 : Blo 231814 523061 := bbase (se 5 (by rfl) ⟨24518, by rfl⟩ : syracuseStep 523061 = 49037) (by norm_num)
theorem B1997621 : Blo 231814 1997621 := bbase (se 5 (by rfl) ⟨93638, by rfl⟩ : syracuseStep 1997621 = 187277) (by norm_num)
theorem B293701 : Blo 231814 293701 := bbase (se 4 (by rfl) ⟨27534, by rfl⟩ : syracuseStep 293701 = 55069) (by norm_num)
theorem B260941 : Blo 231814 260941 := bbase (se 3 (by rfl) ⟨48926, by rfl⟩ : syracuseStep 260941 = 97853) (by norm_num)
theorem B260977 : Blo 231814 260977 := bbase (se 2 (by rfl) ⟨97866, by rfl⟩ : syracuseStep 260977 = 195733) (by norm_num)
theorem B392053 : Blo 231814 392053 := bbase (se 5 (by rfl) ⟨18377, by rfl⟩ : syracuseStep 392053 = 36755) (by norm_num)
theorem B523133 : Blo 231814 523133 := bbase (se 3 (by rfl) ⟨98087, by rfl⟩ : syracuseStep 523133 = 196175) (by norm_num)
theorem B261013 : Blo 231814 261013 := bbase (se 6 (by rfl) ⟨6117, by rfl⟩ : syracuseStep 261013 = 12235) (by norm_num)
theorem B293797 : Blo 231814 293797 := bbase (se 4 (by rfl) ⟨27543, by rfl⟩ : syracuseStep 293797 = 55087) (by norm_num)
theorem B1178549 : Blo 231814 1178549 := bbase (se 5 (by rfl) ⟨55244, by rfl⟩ : syracuseStep 1178549 = 110489) (by norm_num)
theorem B261049 : Blo 231814 261049 := bbase (se 2 (by rfl) ⟨97893, by rfl⟩ : syracuseStep 261049 = 195787) (by norm_num)
theorem B523205 : Blo 231814 523205 := bbase (se 4 (by rfl) ⟨49050, by rfl⟩ : syracuseStep 523205 = 98101) (by norm_num)
theorem B392141 : Blo 231814 392141 := bbase (se 3 (by rfl) ⟨73526, by rfl⟩ : syracuseStep 392141 = 147053) (by norm_num)
theorem B883669 : Blo 231814 883669 := bbase (se 7 (by rfl) ⟨10355, by rfl⟩ : syracuseStep 883669 = 20711) (by norm_num)
theorem B261085 : Blo 231814 261085 := bbase (se 3 (by rfl) ⟨48953, by rfl⟩ : syracuseStep 261085 = 97907) (by norm_num)
theorem B1342453 : Blo 231814 1342453 := bbase (se 5 (by rfl) ⟨62927, by rfl⟩ : syracuseStep 1342453 = 125855) (by norm_num)
theorem B261121 : Blo 231814 261121 := bbase (se 2 (by rfl) ⟨97920, by rfl⟩ : syracuseStep 261121 = 195841) (by norm_num)
theorem B523277 : Blo 231814 523277 := bbase (se 3 (by rfl) ⟨98114, by rfl⟩ : syracuseStep 523277 = 196229) (by norm_num)
theorem B785429 : Blo 231814 785429 := bbase (se 6 (by rfl) ⟨18408, by rfl⟩ : syracuseStep 785429 = 36817) (by norm_num)
theorem B588829 : Blo 231814 588829 := bbase (se 3 (by rfl) ⟨110405, by rfl⟩ : syracuseStep 588829 = 220811) (by norm_num)
theorem B261157 : Blo 231814 261157 := bbase (se 4 (by rfl) ⟨24483, by rfl⟩ : syracuseStep 261157 = 48967) (by norm_num)
theorem B261193 : Blo 231814 261193 := bbase (se 2 (by rfl) ⟨97947, by rfl⟩ : syracuseStep 261193 = 195895) (by norm_num)
theorem B392269 : Blo 231814 392269 := bbase (se 3 (by rfl) ⟨73550, by rfl⟩ : syracuseStep 392269 = 147101) (by norm_num)
theorem B293969 : Blo 231814 293969 := bbase (se 2 (by rfl) ⟨110238, by rfl⟩ : syracuseStep 293969 = 220477) (by norm_num)
theorem B523349 : Blo 231814 523349 := bbase (se 8 (by rfl) ⟨3066, by rfl⟩ : syracuseStep 523349 = 6133) (by norm_num)
theorem B261229 : Blo 231814 261229 := bbase (se 3 (by rfl) ⟨48980, by rfl⟩ : syracuseStep 261229 = 97961) (by norm_num)
theorem B752773 : Blo 231814 752773 := bbase (se 4 (by rfl) ⟨70572, by rfl⟩ : syracuseStep 752773 = 141145) (by norm_num)
theorem B294025 : Blo 231814 294025 := bbase (se 2 (by rfl) ⟨110259, by rfl⟩ : syracuseStep 294025 = 220519) (by norm_num)
theorem B588941 : Blo 231814 588941 := bbase (se 3 (by rfl) ⟨110426, by rfl⟩ : syracuseStep 588941 = 220853) (by norm_num)
theorem B261265 : Blo 231814 261265 := bbase (se 2 (by rfl) ⟨97974, by rfl⟩ : syracuseStep 261265 = 195949) (by norm_num)
theorem B523421 : Blo 231814 523421 := bbase (se 3 (by rfl) ⟨98141, by rfl⟩ : syracuseStep 523421 = 196283) (by norm_num)
theorem B392357 : Blo 231814 392357 := bbase (se 4 (by rfl) ⟨36783, by rfl⟩ : syracuseStep 392357 = 73567) (by norm_num)
theorem B261301 : Blo 231814 261301 := bbase (se 5 (by rfl) ⟨12248, by rfl⟩ : syracuseStep 261301 = 24497) (by norm_num)
theorem B261337 : Blo 231814 261337 := bbase (se 2 (by rfl) ⟨98001, by rfl⟩ : syracuseStep 261337 = 196003) (by norm_num)
theorem B523493 : Blo 231814 523493 := bbase (se 4 (by rfl) ⟨49077, by rfl⟩ : syracuseStep 523493 = 98155) (by norm_num)
theorem B294121 : Blo 231814 294121 := bbase (se 2 (by rfl) ⟨110295, by rfl⟩ : syracuseStep 294121 = 220591) (by norm_num)
theorem B261373 : Blo 231814 261373 := bbase (se 3 (by rfl) ⟨49007, by rfl⟩ : syracuseStep 261373 = 98015) (by norm_num)
theorem B883973 : Blo 231814 883973 := bbase (se 4 (by rfl) ⟨82872, by rfl⟩ : syracuseStep 883973 = 165745) (by norm_num)
theorem B261409 : Blo 231814 261409 := bbase (se 2 (by rfl) ⟨98028, by rfl⟩ : syracuseStep 261409 = 196057) (by norm_num)
theorem B392485 : Blo 231814 392485 := bbase (se 4 (by rfl) ⟨36795, by rfl⟩ : syracuseStep 392485 = 73591) (by norm_num)
theorem B523565 : Blo 231814 523565 := bbase (se 3 (by rfl) ⟨98168, by rfl⟩ : syracuseStep 523565 = 196337) (by norm_num)
theorem B261445 : Blo 231814 261445 := bbase (se 4 (by rfl) ⟨24510, by rfl⟩ : syracuseStep 261445 = 49021) (by norm_num)
theorem B589133 : Blo 231814 589133 := bbase (se 3 (by rfl) ⟨110462, by rfl⟩ : syracuseStep 589133 = 220925) (by norm_num)
theorem B261481 : Blo 231814 261481 := bbase (se 2 (by rfl) ⟨98055, by rfl⟩ : syracuseStep 261481 = 196111) (by norm_num)
theorem B523637 : Blo 231814 523637 := bbase (se 5 (by rfl) ⟨24545, by rfl⟩ : syracuseStep 523637 = 49091) (by norm_num)
theorem B392573 : Blo 231814 392573 := bbase (se 3 (by rfl) ⟨73607, by rfl⟩ : syracuseStep 392573 = 147215) (by norm_num)
theorem B261517 : Blo 231814 261517 := bbase (se 3 (by rfl) ⟨49034, by rfl⟩ : syracuseStep 261517 = 98069) (by norm_num)
theorem B294293 : Blo 231814 294293 := bbase (se 6 (by rfl) ⟨6897, by rfl⟩ : syracuseStep 294293 = 13795) (by norm_num)
theorem B261553 : Blo 231814 261553 := bbase (se 2 (by rfl) ⟨98082, by rfl⟩ : syracuseStep 261553 = 196165) (by norm_num)
theorem B523709 : Blo 231814 523709 := bbase (se 3 (by rfl) ⟨98195, by rfl⟩ : syracuseStep 523709 = 196391) (by norm_num)
theorem B785861 : Blo 231814 785861 := bbase (se 4 (by rfl) ⟨73674, by rfl⟩ : syracuseStep 785861 = 147349) (by norm_num)
theorem B294349 : Blo 231814 294349 := bbase (se 3 (by rfl) ⟨55190, by rfl⟩ : syracuseStep 294349 = 110381) (by norm_num)
theorem B261589 : Blo 231814 261589 := bbase (se 7 (by rfl) ⟨3065, by rfl⟩ : syracuseStep 261589 = 6131) (by norm_num)
theorem B261625 : Blo 231814 261625 := bbase (se 2 (by rfl) ⟨98109, by rfl⟩ : syracuseStep 261625 = 196219) (by norm_num)
theorem B392701 : Blo 231814 392701 := bbase (se 3 (by rfl) ⟨73631, by rfl⟩ : syracuseStep 392701 = 147263) (by norm_num)
theorem B523781 : Blo 231814 523781 := bbase (se 4 (by rfl) ⟨49104, by rfl⟩ : syracuseStep 523781 = 98209) (by norm_num)
theorem B261661 : Blo 231814 261661 := bbase (se 3 (by rfl) ⟨49061, by rfl⟩ : syracuseStep 261661 = 98123) (by norm_num)
theorem B294445 : Blo 231814 294445 := bbase (se 3 (by rfl) ⟨55208, by rfl⟩ : syracuseStep 294445 = 110417) (by norm_num)
theorem B261697 : Blo 231814 261697 := bbase (se 2 (by rfl) ⟨98136, by rfl⟩ : syracuseStep 261697 = 196273) (by norm_num)
theorem B523853 : Blo 231814 523853 := bbase (se 3 (by rfl) ⟨98222, by rfl⟩ : syracuseStep 523853 = 196445) (by norm_num)
theorem B392789 : Blo 231814 392789 := bbase (se 8 (by rfl) ⟨2301, by rfl⟩ : syracuseStep 392789 = 4603) (by norm_num)
theorem B261733 : Blo 231814 261733 := bbase (se 4 (by rfl) ⟨24537, by rfl⟩ : syracuseStep 261733 = 49075) (by norm_num)
theorem B949877 : Blo 231814 949877 := bbase (se 5 (by rfl) ⟨44525, by rfl⟩ : syracuseStep 949877 = 89051) (by norm_num)
theorem B261769 : Blo 231814 261769 := bbase (se 2 (by rfl) ⟨98163, by rfl⟩ : syracuseStep 261769 = 196327) (by norm_num)
theorem B523925 : Blo 231814 523925 := bbase (se 6 (by rfl) ⟨12279, by rfl⟩ : syracuseStep 523925 = 24559) (by norm_num)
theorem B589477 : Blo 231814 589477 := bbase (se 4 (by rfl) ⟨55263, by rfl⟩ : syracuseStep 589477 = 110527) (by norm_num)
theorem B261805 : Blo 231814 261805 := bbase (se 3 (by rfl) ⟨49088, by rfl⟩ : syracuseStep 261805 = 98177) (by norm_num)
theorem B261841 : Blo 231814 261841 := bbase (se 2 (by rfl) ⟨98190, by rfl⟩ : syracuseStep 261841 = 196381) (by norm_num)
theorem B392917 : Blo 231814 392917 := bbase (se 7 (by rfl) ⟨4604, by rfl⟩ : syracuseStep 392917 = 9209) (by norm_num)
theorem B294617 : Blo 231814 294617 := bbase (se 2 (by rfl) ⟨110481, by rfl⟩ : syracuseStep 294617 = 220963) (by norm_num)
theorem B523997 : Blo 231814 523997 := bbase (se 3 (by rfl) ⟨98249, by rfl⟩ : syracuseStep 523997 = 196499) (by norm_num)
theorem B261877 : Blo 231814 261877 := bbase (se 5 (by rfl) ⟨12275, by rfl⟩ : syracuseStep 261877 = 24551) (by norm_num)
theorem B294673 : Blo 231814 294673 := bbase (se 2 (by rfl) ⟨110502, by rfl⟩ : syracuseStep 294673 = 221005) (by norm_num)
theorem B589589 : Blo 231814 589589 := bbase (se 6 (by rfl) ⟨13818, by rfl⟩ : syracuseStep 589589 = 27637) (by norm_num)
theorem B261913 : Blo 231814 261913 := bbase (se 2 (by rfl) ⟨98217, by rfl⟩ : syracuseStep 261913 = 196435) (by norm_num)
theorem B524069 : Blo 231814 524069 := bbase (se 4 (by rfl) ⟨49131, by rfl⟩ : syracuseStep 524069 = 98263) (by norm_num)
theorem B393005 : Blo 231814 393005 := bbase (se 3 (by rfl) ⟨73688, by rfl⟩ : syracuseStep 393005 = 147377) (by norm_num)
theorem B261949 : Blo 231814 261949 := bbase (se 3 (by rfl) ⟨49115, by rfl⟩ : syracuseStep 261949 = 98231) (by norm_num)
theorem B261985 : Blo 231814 261985 := bbase (se 2 (by rfl) ⟨98244, by rfl⟩ : syracuseStep 261985 = 196489) (by norm_num)
theorem B524141 : Blo 231814 524141 := bbase (se 3 (by rfl) ⟨98276, by rfl⟩ : syracuseStep 524141 = 196553) (by norm_num)
theorem B294769 : Blo 231814 294769 := bbase (se 2 (by rfl) ⟨110538, by rfl⟩ : syracuseStep 294769 = 221077) (by norm_num)
theorem B786293 : Blo 231814 786293 := bbase (se 5 (by rfl) ⟨36857, by rfl⟩ : syracuseStep 786293 = 73715) (by norm_num)
theorem B262021 : Blo 231814 262021 := bbase (se 4 (by rfl) ⟨24564, by rfl⟩ : syracuseStep 262021 = 49129) (by norm_num)
theorem B262057 : Blo 231814 262057 := bbase (se 2 (by rfl) ⟨98271, by rfl⟩ : syracuseStep 262057 = 196543) (by norm_num)
theorem B393133 : Blo 231814 393133 := bbase (se 3 (by rfl) ⟨73712, by rfl⟩ : syracuseStep 393133 = 147425) (by norm_num)
theorem B524213 : Blo 231814 524213 := bbase (se 5 (by rfl) ⟨24572, by rfl⟩ : syracuseStep 524213 = 49145) (by norm_num)
theorem B262093 : Blo 231814 262093 := bbase (se 3 (by rfl) ⟨49142, by rfl⟩ : syracuseStep 262093 = 98285) (by norm_num)
theorem B589781 : Blo 231814 589781 := bbase (se 7 (by rfl) ⟨6911, by rfl⟩ : syracuseStep 589781 = 13823) (by norm_num)
theorem B262129 : Blo 231814 262129 := bbase (se 2 (by rfl) ⟨98298, by rfl⟩ : syracuseStep 262129 = 196597) (by norm_num)
theorem B557045 : Blo 231814 557045 := bbase (se 5 (by rfl) ⟨26111, by rfl⟩ : syracuseStep 557045 = 52223) (by norm_num)
theorem B524285 : Blo 231814 524285 := bbase (se 3 (by rfl) ⟨98303, by rfl⟩ : syracuseStep 524285 = 196607) (by norm_num)
theorem B262147 : Blo 231814 262147 := bstep (se 1 (by rfl) ⟨196610, by rfl⟩ : syracuseStep 262147 = 393221) B393221
theorem B294931 : Blo 231814 294931 := bstep (se 1 (by rfl) ⟨221198, by rfl⟩ : syracuseStep 294931 = 442397) B442397
theorem B1179683 : Blo 231814 1179683 := bstep (se 1 (by rfl) ⟨884762, by rfl⟩ : syracuseStep 1179683 = 1769525) B1769525
theorem B786509 : Blo 231814 786509 := bstep (se 3 (by rfl) ⟨147470, by rfl⟩ : syracuseStep 786509 = 294941) B294941
theorem B393329 : Blo 231814 393329 := bstep (se 2 (by rfl) ⟨147498, by rfl⟩ : syracuseStep 393329 = 294997) B294997
theorem B786563 : Blo 231814 786563 := bstep (se 1 (by rfl) ⟨589922, by rfl⟩ : syracuseStep 786563 = 1179845) B1179845
theorem B262291 : Blo 231814 262291 := bstep (se 1 (by rfl) ⟨196718, by rfl⟩ : syracuseStep 262291 = 393437) B393437
theorem B557219 : Blo 231814 557219 := bstep (se 1 (by rfl) ⟨417914, by rfl⟩ : syracuseStep 557219 = 835829) B835829
theorem B524465 : Blo 231814 524465 := bstep (se 2 (by rfl) ⟨196674, by rfl⟩ : syracuseStep 524465 = 393349) B393349
theorem B524483 : Blo 231814 524483 := bstep (se 1 (by rfl) ⟨393362, by rfl⟩ : syracuseStep 524483 = 786725) B786725
theorem B393457 : Blo 231814 393457 := bstep (se 2 (by rfl) ⟨147546, by rfl⟩ : syracuseStep 393457 = 295093) B295093
theorem B393491 : Blo 231814 393491 := bstep (se 1 (by rfl) ⟨295118, by rfl⟩ : syracuseStep 393491 = 590237) B590237
theorem B262435 : Blo 231814 262435 := bstep (se 1 (by rfl) ⟨196826, by rfl⟩ : syracuseStep 262435 = 393653) B393653
theorem B786833 : Blo 231814 786833 := bstep (se 2 (by rfl) ⟨295062, by rfl⟩ : syracuseStep 786833 = 590125) B590125
theorem B393619 : Blo 231814 393619 := bstep (se 1 (by rfl) ⟨295214, by rfl⟩ : syracuseStep 393619 = 590429) B590429
theorem B262579 : Blo 231814 262579 := bstep (se 1 (by rfl) ⟨196934, by rfl⟩ : syracuseStep 262579 = 393869) B393869
theorem B524753 : Blo 231814 524753 := bstep (se 2 (by rfl) ⟨196782, by rfl⟩ : syracuseStep 524753 = 393565) B393565
theorem B524771 : Blo 231814 524771 := bstep (se 1 (by rfl) ⟨393578, by rfl⟩ : syracuseStep 524771 = 787157) B787157
theorem B295427 : Blo 231814 295427 := bstep (se 1 (by rfl) ⟨221570, by rfl⟩ : syracuseStep 295427 = 443141) B443141
theorem B393761 : Blo 231814 393761 := bstep (se 2 (by rfl) ⟨147660, by rfl⟩ : syracuseStep 393761 = 295321) B295321
theorem B262723 : Blo 231814 262723 := bstep (se 1 (by rfl) ⟨197042, by rfl⟩ : syracuseStep 262723 = 394085) B394085
theorem B590449 : Blo 231814 590449 := bstep (se 2 (by rfl) ⟨221418, by rfl⟩ : syracuseStep 590449 = 442837) B442837
theorem B950897 : Blo 231814 950897 := bstep (se 2 (by rfl) ⟨356586, by rfl⟩ : syracuseStep 950897 = 713173) B713173
theorem B393889 : Blo 231814 393889 := bstep (se 2 (by rfl) ⟨147708, by rfl⟩ : syracuseStep 393889 = 295417) B295417
theorem B393923 : Blo 231814 393923 := bstep (se 1 (by rfl) ⟨295442, by rfl⟩ : syracuseStep 393923 = 590885) B590885
theorem B6062789 : Blo 231814 6062789 := bstep (se 4 (by rfl) ⟨568386, by rfl⟩ : syracuseStep 6062789 = 1136773) B1136773
theorem B3211973 : Blo 231814 3211973 := bstep (se 4 (by rfl) ⟨301122, by rfl⟩ : syracuseStep 3211973 = 602245) B602245
theorem B262867 : Blo 231814 262867 := bstep (se 1 (by rfl) ⟨197150, by rfl⟩ : syracuseStep 262867 = 394301) B394301
theorem B525041 : Blo 231814 525041 := bstep (se 2 (by rfl) ⟨196890, by rfl⟩ : syracuseStep 525041 = 393781) B393781
theorem B525059 : Blo 231814 525059 := bstep (se 1 (by rfl) ⟨393794, by rfl⟩ : syracuseStep 525059 = 787589) B787589
theorem B394051 : Blo 231814 394051 := bstep (se 1 (by rfl) ⟨295538, by rfl⟩ : syracuseStep 394051 = 591077) B591077
theorem B1180493 : Blo 231814 1180493 := bstep (se 3 (by rfl) ⟨221342, by rfl⟩ : syracuseStep 1180493 = 442685) B442685
theorem B263011 : Blo 231814 263011 := bstep (se 1 (by rfl) ⟨197258, by rfl⟩ : syracuseStep 263011 = 394517) B394517
theorem B590723 : Blo 231814 590723 := bstep (se 1 (by rfl) ⟨443042, by rfl⟩ : syracuseStep 590723 = 886085) B886085
theorem B787373 : Blo 231814 787373 := bstep (se 3 (by rfl) ⟨147632, by rfl⟩ : syracuseStep 787373 = 295265) B295265
theorem B394193 : Blo 231814 394193 := bstep (se 2 (by rfl) ⟨147822, by rfl⟩ : syracuseStep 394193 = 295645) B295645
theorem B787427 : Blo 231814 787427 := bstep (se 1 (by rfl) ⟨590570, by rfl⟩ : syracuseStep 787427 = 1181141) B1181141
theorem B558065 : Blo 231814 558065 := bstep (se 2 (by rfl) ⟨209274, by rfl⟩ : syracuseStep 558065 = 418549) B418549
theorem B263155 : Blo 231814 263155 := bstep (se 1 (by rfl) ⟨197366, by rfl⟩ : syracuseStep 263155 = 394733) B394733
theorem B525329 : Blo 231814 525329 := bstep (se 2 (by rfl) ⟨196998, by rfl⟩ : syracuseStep 525329 = 393997) B393997
theorem B525347 : Blo 231814 525347 := bstep (se 1 (by rfl) ⟨394010, by rfl⟩ : syracuseStep 525347 = 788021) B788021
theorem B590915 : Blo 231814 590915 := bstep (se 1 (by rfl) ⟨443186, by rfl⟩ : syracuseStep 590915 = 886373) B886373
theorem B558161 : Blo 231814 558161 := bstep (se 2 (by rfl) ⟨209310, by rfl⟩ : syracuseStep 558161 = 418621) B418621
theorem B394321 : Blo 231814 394321 := bstep (se 2 (by rfl) ⟨147870, by rfl⟩ : syracuseStep 394321 = 295741) B295741
theorem B394355 : Blo 231814 394355 := bstep (se 1 (by rfl) ⟨295766, by rfl⟩ : syracuseStep 394355 = 591533) B591533
theorem B263299 : Blo 231814 263299 := bstep (se 1 (by rfl) ⟨197474, by rfl⟩ : syracuseStep 263299 = 394949) B394949
theorem B296131 : Blo 231814 296131 := bstep (se 1 (by rfl) ⟨222098, by rfl⟩ : syracuseStep 296131 = 444197) B444197
theorem B754925 : Blo 231814 754925 := bstep (se 3 (by rfl) ⟨141548, by rfl⟩ : syracuseStep 754925 = 283097) B283097
theorem B787697 : Blo 231814 787697 := bstep (se 2 (by rfl) ⟨295386, by rfl⟩ : syracuseStep 787697 = 590773) B590773
theorem B394483 : Blo 231814 394483 := bstep (se 1 (by rfl) ⟨295862, by rfl⟩ : syracuseStep 394483 = 591725) B591725
theorem B263443 : Blo 231814 263443 := bstep (se 1 (by rfl) ⟨197582, by rfl⟩ : syracuseStep 263443 = 395165) B395165
theorem B296227 : Blo 231814 296227 := bstep (se 1 (by rfl) ⟨222170, by rfl⟩ : syracuseStep 296227 = 444341) B444341
theorem B525617 : Blo 231814 525617 := bstep (se 2 (by rfl) ⟨197106, by rfl⟩ : syracuseStep 525617 = 394213) B394213
theorem B525635 : Blo 231814 525635 := bstep (se 1 (by rfl) ⟨394226, by rfl⟩ : syracuseStep 525635 = 788453) B788453
theorem B394625 : Blo 231814 394625 := bstep (se 2 (by rfl) ⟨147984, by rfl⟩ : syracuseStep 394625 = 295969) B295969
theorem B263587 : Blo 231814 263587 := bstep (se 1 (by rfl) ⟨197690, by rfl⟩ : syracuseStep 263587 = 395381) B395381
theorem B394753 : Blo 231814 394753 := bstep (se 2 (by rfl) ⟨148032, by rfl⟩ : syracuseStep 394753 = 296065) B296065
theorem B755203 : Blo 231814 755203 := bstep (se 1 (by rfl) ⟨566402, by rfl⟩ : syracuseStep 755203 = 1132805) B1132805
theorem B951821 : Blo 231814 951821 := bstep (se 3 (by rfl) ⟨178466, by rfl⟩ : syracuseStep 951821 = 356933) B356933
theorem B394787 : Blo 231814 394787 := bstep (se 1 (by rfl) ⟨296090, by rfl⟩ : syracuseStep 394787 = 592181) B592181
theorem B263731 : Blo 231814 263731 := bstep (se 1 (by rfl) ⟨197798, by rfl⟩ : syracuseStep 263731 = 395597) B395597
theorem B525905 : Blo 231814 525905 := bstep (se 2 (by rfl) ⟨197214, by rfl⟩ : syracuseStep 525905 = 394429) B394429
theorem B525923 : Blo 231814 525923 := bstep (se 1 (by rfl) ⟨394442, by rfl⟩ : syracuseStep 525923 = 788885) B788885
theorem B394915 : Blo 231814 394915 := bstep (se 1 (by rfl) ⟨296186, by rfl⟩ : syracuseStep 394915 = 592373) B592373
theorem B263875 : Blo 231814 263875 := bstep (se 1 (by rfl) ⟨197906, by rfl⟩ : syracuseStep 263875 = 395813) B395813
theorem B788237 : Blo 231814 788237 := bstep (se 3 (by rfl) ⟨147794, by rfl⟩ : syracuseStep 788237 = 295589) B295589
theorem B296723 : Blo 231814 296723 := bstep (se 1 (by rfl) ⟨222542, by rfl⟩ : syracuseStep 296723 = 445085) B445085
theorem B395057 : Blo 231814 395057 := bstep (se 2 (by rfl) ⟨148146, by rfl⟩ : syracuseStep 395057 = 296293) B296293
theorem B3573557 : Blo 231814 3573557 := bstep (se 5 (by rfl) ⟨167510, by rfl⟩ : syracuseStep 3573557 = 335021) B335021
theorem B788291 : Blo 231814 788291 := bstep (se 1 (by rfl) ⟨591218, by rfl⟩ : syracuseStep 788291 = 1182437) B1182437
theorem B264019 : Blo 231814 264019 := bstep (se 1 (by rfl) ⟨198014, by rfl⟩ : syracuseStep 264019 = 396029) B396029
theorem B526193 : Blo 231814 526193 := bstep (se 2 (by rfl) ⟨197322, by rfl⟩ : syracuseStep 526193 = 394645) B394645
theorem B526211 : Blo 231814 526211 := bstep (se 1 (by rfl) ⟨394658, by rfl⟩ : syracuseStep 526211 = 789317) B789317
theorem B722819 : Blo 231814 722819 := bstep (se 1 (by rfl) ⟨542114, by rfl⟩ : syracuseStep 722819 = 1084229) B1084229
theorem B395185 : Blo 231814 395185 := bstep (se 2 (by rfl) ⟨148194, by rfl⟩ : syracuseStep 395185 = 296389) B296389
theorem B395219 : Blo 231814 395219 := bstep (se 1 (by rfl) ⟨296414, by rfl⟩ : syracuseStep 395219 = 592829) B592829
theorem B264163 : Blo 231814 264163 := bstep (se 1 (by rfl) ⟨198122, by rfl⟩ : syracuseStep 264163 = 396245) B396245
theorem B591857 : Blo 231814 591857 := bstep (se 2 (by rfl) ⟨221946, by rfl⟩ : syracuseStep 591857 = 443893) B443893
theorem B591907 : Blo 231814 591907 := bstep (se 1 (by rfl) ⟨443930, by rfl⟩ : syracuseStep 591907 = 887861) B887861
theorem B788561 : Blo 231814 788561 := bstep (se 2 (by rfl) ⟨295710, by rfl⟩ : syracuseStep 788561 = 591421) B591421
theorem B395347 : Blo 231814 395347 := bstep (se 1 (by rfl) ⟨296510, by rfl⟩ : syracuseStep 395347 = 593021) B593021
theorem B264307 : Blo 231814 264307 := bstep (se 1 (by rfl) ⟨198230, by rfl⟩ : syracuseStep 264307 = 396461) B396461
theorem B4524173 : Blo 231814 4524173 := bstep (se 3 (by rfl) ⟨848282, by rfl⟩ : syracuseStep 4524173 = 1696565) B1696565
theorem B526481 : Blo 231814 526481 := bstep (se 2 (by rfl) ⟨197430, by rfl⟩ : syracuseStep 526481 = 394861) B394861
theorem B526499 : Blo 231814 526499 := bstep (se 1 (by rfl) ⟨394874, by rfl⟩ : syracuseStep 526499 = 789749) B789749
theorem B592049 : Blo 231814 592049 := bstep (se 2 (by rfl) ⟨222018, by rfl⟩ : syracuseStep 592049 = 444037) B444037
theorem B395489 : Blo 231814 395489 := bstep (se 2 (by rfl) ⟨148308, by rfl⟩ : syracuseStep 395489 = 296617) B296617
theorem B264451 : Blo 231814 264451 := bstep (se 1 (by rfl) ⟨198338, by rfl⟩ : syracuseStep 264451 = 396677) B396677
theorem B395617 : Blo 231814 395617 := bstep (se 2 (by rfl) ⟨148356, by rfl⟩ : syracuseStep 395617 = 296713) B296713
theorem B395651 : Blo 231814 395651 := bstep (se 1 (by rfl) ⟨296738, by rfl⟩ : syracuseStep 395651 = 593477) B593477
theorem B559505 : Blo 231814 559505 := bstep (se 2 (by rfl) ⟨209814, by rfl⟩ : syracuseStep 559505 = 419629) B419629
theorem B231827 : Blo 231814 231827 := bstep (se 1 (by rfl) ⟨173870, by rfl⟩ : syracuseStep 231827 = 347741) B347741
theorem B264595 : Blo 231814 264595 := bstep (se 1 (by rfl) ⟨198446, by rfl⟩ : syracuseStep 264595 = 396893) B396893
theorem B231843 : Blo 231814 231843 := bstep (se 1 (by rfl) ⟨173882, by rfl⟩ : syracuseStep 231843 = 347765) B347765
theorem B526769 : Blo 231814 526769 := bstep (se 2 (by rfl) ⟨197538, by rfl⟩ : syracuseStep 526769 = 395077) B395077
theorem B231859 : Blo 231814 231859 := bstep (se 1 (by rfl) ⟨173894, by rfl⟩ : syracuseStep 231859 = 347789) B347789
theorem B231875 : Blo 231814 231875 := bstep (se 1 (by rfl) ⟨173906, by rfl⟩ : syracuseStep 231875 = 347813) B347813
theorem B526787 : Blo 231814 526787 := bstep (se 1 (by rfl) ⟨395090, by rfl⟩ : syracuseStep 526787 = 790181) B790181
theorem B231891 : Blo 231814 231891 := bstep (se 1 (by rfl) ⟨173918, by rfl⟩ : syracuseStep 231891 = 347837) B347837
theorem B297427 : Blo 231814 297427 := bstep (se 1 (by rfl) ⟨223070, by rfl⟩ : syracuseStep 297427 = 446141) B446141
theorem B231907 : Blo 231814 231907 := bstep (se 1 (by rfl) ⟨173930, by rfl⟩ : syracuseStep 231907 = 347861) B347861
theorem B231923 : Blo 231814 231923 := bstep (se 1 (by rfl) ⟨173942, by rfl⟩ : syracuseStep 231923 = 347885) B347885
theorem B231939 : Blo 231814 231939 := bstep (se 1 (by rfl) ⟨173954, by rfl⟩ : syracuseStep 231939 = 347909) B347909
theorem B395779 : Blo 231814 395779 := bstep (se 1 (by rfl) ⟨296834, by rfl⟩ : syracuseStep 395779 = 593669) B593669
theorem B231955 : Blo 231814 231955 := bstep (se 1 (by rfl) ⟨173966, by rfl⟩ : syracuseStep 231955 = 347933) B347933
theorem B231971 : Blo 231814 231971 := bstep (se 1 (by rfl) ⟨173978, by rfl⟩ : syracuseStep 231971 = 347957) B347957
theorem B264739 : Blo 231814 264739 := bstep (se 1 (by rfl) ⟨198554, by rfl⟩ : syracuseStep 264739 = 397109) B397109
theorem B887345 : Blo 231814 887345 := bstep (se 2 (by rfl) ⟨332754, by rfl⟩ : syracuseStep 887345 = 665509) B665509
theorem B231987 : Blo 231814 231987 := bstep (se 1 (by rfl) ⟨173990, by rfl⟩ : syracuseStep 231987 = 347981) B347981
theorem B297523 : Blo 231814 297523 := bstep (se 1 (by rfl) ⟨223142, by rfl⟩ : syracuseStep 297523 = 446285) B446285
theorem B232003 : Blo 231814 232003 := bstep (se 1 (by rfl) ⟨174002, by rfl⟩ : syracuseStep 232003 = 348005) B348005
theorem B232019 : Blo 231814 232019 := bstep (se 1 (by rfl) ⟨174014, by rfl⟩ : syracuseStep 232019 = 348029) B348029
theorem B232035 : Blo 231814 232035 := bstep (se 1 (by rfl) ⟨174026, by rfl⟩ : syracuseStep 232035 = 348053) B348053
theorem B789101 : Blo 231814 789101 := bstep (se 3 (by rfl) ⟨147956, by rfl⟩ : syracuseStep 789101 = 295913) B295913
theorem B232051 : Blo 231814 232051 := bstep (se 1 (by rfl) ⟨174038, by rfl⟩ : syracuseStep 232051 = 348077) B348077
theorem B232067 : Blo 231814 232067 := bstep (se 1 (by rfl) ⟨174050, by rfl⟩ : syracuseStep 232067 = 348101) B348101
theorem B395921 : Blo 231814 395921 := bstep (se 2 (by rfl) ⟨148470, by rfl⟩ : syracuseStep 395921 = 296941) B296941
theorem B232083 : Blo 231814 232083 := bstep (se 1 (by rfl) ⟨174062, by rfl⟩ : syracuseStep 232083 = 348125) B348125
theorem B232099 : Blo 231814 232099 := bstep (se 1 (by rfl) ⟨174074, by rfl⟩ : syracuseStep 232099 = 348149) B348149
theorem B789155 : Blo 231814 789155 := bstep (se 1 (by rfl) ⟨591866, by rfl⟩ : syracuseStep 789155 = 1183733) B1183733
theorem B232115 : Blo 231814 232115 := bstep (se 1 (by rfl) ⟨174086, by rfl⟩ : syracuseStep 232115 = 348173) B348173
theorem B264883 : Blo 231814 264883 := bstep (se 1 (by rfl) ⟨198662, by rfl⟩ : syracuseStep 264883 = 397325) B397325
theorem B3148469 : Blo 231814 3148469 := bstep (se 5 (by rfl) ⟨147584, by rfl⟩ : syracuseStep 3148469 = 295169) B295169
theorem B232131 : Blo 231814 232131 := bstep (se 1 (by rfl) ⟨174098, by rfl⟩ : syracuseStep 232131 = 348197) B348197
theorem B527057 : Blo 231814 527057 := bstep (se 2 (by rfl) ⟨197646, by rfl⟩ : syracuseStep 527057 = 395293) B395293
theorem B232147 : Blo 231814 232147 := bstep (se 1 (by rfl) ⟨174110, by rfl⟩ : syracuseStep 232147 = 348221) B348221
theorem B232163 : Blo 231814 232163 := bstep (se 1 (by rfl) ⟨174122, by rfl⟩ : syracuseStep 232163 = 348245) B348245
theorem B527075 : Blo 231814 527075 := bstep (se 1 (by rfl) ⟨395306, by rfl⟩ : syracuseStep 527075 = 790613) B790613
theorem B232179 : Blo 231814 232179 := bstep (se 1 (by rfl) ⟨174134, by rfl⟩ : syracuseStep 232179 = 348269) B348269
theorem B232195 : Blo 231814 232195 := bstep (se 1 (by rfl) ⟨174146, by rfl⟩ : syracuseStep 232195 = 348293) B348293
theorem B396049 : Blo 231814 396049 := bstep (se 2 (by rfl) ⟨148518, by rfl⟩ : syracuseStep 396049 = 297037) B297037
theorem B232211 : Blo 231814 232211 := bstep (se 1 (by rfl) ⟨174158, by rfl⟩ : syracuseStep 232211 = 348317) B348317
theorem B232227 : Blo 231814 232227 := bstep (se 1 (by rfl) ⟨174170, by rfl⟩ : syracuseStep 232227 = 348341) B348341
theorem B232243 : Blo 231814 232243 := bstep (se 1 (by rfl) ⟨174182, by rfl⟩ : syracuseStep 232243 = 348365) B348365
theorem B396083 : Blo 231814 396083 := bstep (se 1 (by rfl) ⟨297062, by rfl⟩ : syracuseStep 396083 = 594125) B594125
theorem B232259 : Blo 231814 232259 := bstep (se 1 (by rfl) ⟨174194, by rfl⟩ : syracuseStep 232259 = 348389) B348389
theorem B265027 : Blo 231814 265027 := bstep (se 1 (by rfl) ⟨198770, by rfl⟩ : syracuseStep 265027 = 397541) B397541
theorem B232275 : Blo 231814 232275 := bstep (se 1 (by rfl) ⟨174206, by rfl⟩ : syracuseStep 232275 = 348413) B348413
theorem B232291 : Blo 231814 232291 := bstep (se 1 (by rfl) ⟨174218, by rfl⟩ : syracuseStep 232291 = 348437) B348437
theorem B232307 : Blo 231814 232307 := bstep (se 1 (by rfl) ⟨174230, by rfl⟩ : syracuseStep 232307 = 348461) B348461
theorem B232323 : Blo 231814 232323 := bstep (se 1 (by rfl) ⟨174242, by rfl⟩ : syracuseStep 232323 = 348485) B348485
theorem B232339 : Blo 231814 232339 := bstep (se 1 (by rfl) ⟨174254, by rfl⟩ : syracuseStep 232339 = 348509) B348509
theorem B232355 : Blo 231814 232355 := bstep (se 1 (by rfl) ⟨174266, by rfl⟩ : syracuseStep 232355 = 348533) B348533
theorem B789425 : Blo 231814 789425 := bstep (se 2 (by rfl) ⟨296034, by rfl⟩ : syracuseStep 789425 = 592069) B592069
theorem B232371 : Blo 231814 232371 := bstep (se 1 (by rfl) ⟨174278, by rfl⟩ : syracuseStep 232371 = 348557) B348557
theorem B396211 : Blo 231814 396211 := bstep (se 1 (by rfl) ⟨297158, by rfl⟩ : syracuseStep 396211 = 594317) B594317
theorem B232387 : Blo 231814 232387 := bstep (se 1 (by rfl) ⟨174290, by rfl⟩ : syracuseStep 232387 = 348581) B348581
theorem B232403 : Blo 231814 232403 := bstep (se 1 (by rfl) ⟨174302, by rfl⟩ : syracuseStep 232403 = 348605) B348605
theorem B265171 : Blo 231814 265171 := bstep (se 1 (by rfl) ⟨198878, by rfl⟩ : syracuseStep 265171 = 397757) B397757
theorem B232419 : Blo 231814 232419 := bstep (se 1 (by rfl) ⟨174314, by rfl⟩ : syracuseStep 232419 = 348629) B348629
theorem B527345 : Blo 231814 527345 := bstep (se 2 (by rfl) ⟨197754, by rfl⟩ : syracuseStep 527345 = 395509) B395509
theorem B232435 : Blo 231814 232435 := bstep (se 1 (by rfl) ⟨174326, by rfl⟩ : syracuseStep 232435 = 348653) B348653
theorem B232451 : Blo 231814 232451 := bstep (se 1 (by rfl) ⟨174338, by rfl⟩ : syracuseStep 232451 = 348677) B348677
theorem B527363 : Blo 231814 527363 := bstep (se 1 (by rfl) ⟨395522, by rfl⟩ : syracuseStep 527363 = 791045) B791045
theorem B232467 : Blo 231814 232467 := bstep (se 1 (by rfl) ⟨174350, by rfl⟩ : syracuseStep 232467 = 348701) B348701
theorem B232483 : Blo 231814 232483 := bstep (se 1 (by rfl) ⟨174362, by rfl⟩ : syracuseStep 232483 = 348725) B348725
theorem B298019 : Blo 231814 298019 := bstep (se 1 (by rfl) ⟨223514, by rfl⟩ : syracuseStep 298019 = 447029) B447029
theorem B232499 : Blo 231814 232499 := bstep (se 1 (by rfl) ⟨174374, by rfl⟩ : syracuseStep 232499 = 348749) B348749
theorem B396353 : Blo 231814 396353 := bstep (se 2 (by rfl) ⟨148632, by rfl⟩ : syracuseStep 396353 = 297265) B297265
theorem B232515 : Blo 231814 232515 := bstep (se 1 (by rfl) ⟨174386, by rfl⟩ : syracuseStep 232515 = 348773) B348773
theorem B232531 : Blo 231814 232531 := bstep (se 1 (by rfl) ⟨174398, by rfl⟩ : syracuseStep 232531 = 348797) B348797
theorem B232547 : Blo 231814 232547 := bstep (se 1 (by rfl) ⟨174410, by rfl⟩ : syracuseStep 232547 = 348821) B348821
theorem B232563 : Blo 231814 232563 := bstep (se 1 (by rfl) ⟨174422, by rfl⟩ : syracuseStep 232563 = 348845) B348845
theorem B232579 : Blo 231814 232579 := bstep (se 1 (by rfl) ⟨174434, by rfl⟩ : syracuseStep 232579 = 348869) B348869
theorem B593041 : Blo 231814 593041 := bstep (se 2 (by rfl) ⟨222390, by rfl⟩ : syracuseStep 593041 = 444781) B444781
theorem B232595 : Blo 231814 232595 := bstep (se 1 (by rfl) ⟨174446, by rfl⟩ : syracuseStep 232595 = 348893) B348893
theorem B232611 : Blo 231814 232611 := bstep (se 1 (by rfl) ⟨174458, by rfl⟩ : syracuseStep 232611 = 348917) B348917
theorem B953507 : Blo 231814 953507 := bstep (se 1 (by rfl) ⟨715130, by rfl⟩ : syracuseStep 953507 = 1430261) B1430261
theorem B756913 : Blo 231814 756913 := bstep (se 2 (by rfl) ⟨283842, by rfl⟩ : syracuseStep 756913 = 567685) B567685
theorem B232627 : Blo 231814 232627 := bstep (se 1 (by rfl) ⟨174470, by rfl⟩ : syracuseStep 232627 = 348941) B348941
theorem B396481 : Blo 231814 396481 := bstep (se 2 (by rfl) ⟨148680, by rfl⟩ : syracuseStep 396481 = 297361) B297361
theorem B232643 : Blo 231814 232643 := bstep (se 1 (by rfl) ⟨174482, by rfl⟩ : syracuseStep 232643 = 348965) B348965
theorem B330961 : Blo 231814 330961 := bstep (se 2 (by rfl) ⟨124110, by rfl⟩ : syracuseStep 330961 = 248221) B248221
theorem B232659 : Blo 231814 232659 := bstep (se 1 (by rfl) ⟨174494, by rfl⟩ : syracuseStep 232659 = 348989) B348989
theorem B232675 : Blo 231814 232675 := bstep (se 1 (by rfl) ⟨174506, by rfl⟩ : syracuseStep 232675 = 349013) B349013
theorem B396515 : Blo 231814 396515 := bstep (se 1 (by rfl) ⟨297386, by rfl⟩ : syracuseStep 396515 = 594773) B594773
theorem B232691 : Blo 231814 232691 := bstep (se 1 (by rfl) ⟨174518, by rfl⟩ : syracuseStep 232691 = 349037) B349037
theorem B298243 : Blo 231814 298243 := bstep (se 1 (by rfl) ⟨223682, by rfl⟩ : syracuseStep 298243 = 447365) B447365
theorem B232707 : Blo 231814 232707 := bstep (se 1 (by rfl) ⟨174530, by rfl⟩ : syracuseStep 232707 = 349061) B349061
theorem B527633 : Blo 231814 527633 := bstep (se 2 (by rfl) ⟨197862, by rfl⟩ : syracuseStep 527633 = 395725) B395725
theorem B232723 : Blo 231814 232723 := bstep (se 1 (by rfl) ⟨174542, by rfl⟩ : syracuseStep 232723 = 349085) B349085
theorem B232739 : Blo 231814 232739 := bstep (se 1 (by rfl) ⟨174554, by rfl⟩ : syracuseStep 232739 = 349109) B349109
theorem B527651 : Blo 231814 527651 := bstep (se 1 (by rfl) ⟨395738, by rfl⟩ : syracuseStep 527651 = 791477) B791477
theorem B331057 : Blo 231814 331057 := bstep (se 2 (by rfl) ⟨124146, by rfl⟩ : syracuseStep 331057 = 248293) B248293
theorem B232755 : Blo 231814 232755 := bstep (se 1 (by rfl) ⟨174566, by rfl⟩ : syracuseStep 232755 = 349133) B349133
theorem B232771 : Blo 231814 232771 := bstep (se 1 (by rfl) ⟨174578, by rfl⟩ : syracuseStep 232771 = 349157) B349157
theorem B232787 : Blo 231814 232787 := bstep (se 1 (by rfl) ⟨174590, by rfl⟩ : syracuseStep 232787 = 349181) B349181
theorem B232803 : Blo 231814 232803 := bstep (se 1 (by rfl) ⟨174602, by rfl⟩ : syracuseStep 232803 = 349205) B349205
theorem B396643 : Blo 231814 396643 := bstep (se 1 (by rfl) ⟨297482, by rfl⟩ : syracuseStep 396643 = 594965) B594965
theorem B232819 : Blo 231814 232819 := bstep (se 1 (by rfl) ⟨174614, by rfl⟩ : syracuseStep 232819 = 349229) B349229
theorem B232835 : Blo 231814 232835 := bstep (se 1 (by rfl) ⟨174626, by rfl⟩ : syracuseStep 232835 = 349253) B349253
theorem B232851 : Blo 231814 232851 := bstep (se 1 (by rfl) ⟨174638, by rfl⟩ : syracuseStep 232851 = 349277) B349277
theorem B232867 : Blo 231814 232867 := bstep (se 1 (by rfl) ⟨174650, by rfl⟩ : syracuseStep 232867 = 349301) B349301
theorem B593315 : Blo 231814 593315 := bstep (se 1 (by rfl) ⟨444986, by rfl⟩ : syracuseStep 593315 = 889973) B889973
theorem B232883 : Blo 231814 232883 := bstep (se 1 (by rfl) ⟨174662, by rfl⟩ : syracuseStep 232883 = 349325) B349325
theorem B232899 : Blo 231814 232899 := bstep (se 1 (by rfl) ⟨174674, by rfl⟩ : syracuseStep 232899 = 349349) B349349
theorem B789965 : Blo 231814 789965 := bstep (se 3 (by rfl) ⟨148118, by rfl⟩ : syracuseStep 789965 = 296237) B296237
theorem B232915 : Blo 231814 232915 := bstep (se 1 (by rfl) ⟨174686, by rfl⟩ : syracuseStep 232915 = 349373) B349373
theorem B232931 : Blo 231814 232931 := bstep (se 1 (by rfl) ⟨174698, by rfl⟩ : syracuseStep 232931 = 349397) B349397
theorem B396785 : Blo 231814 396785 := bstep (se 2 (by rfl) ⟨148794, by rfl⟩ : syracuseStep 396785 = 297589) B297589
theorem B232947 : Blo 231814 232947 := bstep (se 1 (by rfl) ⟨174710, by rfl⟩ : syracuseStep 232947 = 349421) B349421
theorem B232963 : Blo 231814 232963 := bstep (se 1 (by rfl) ⟨174722, by rfl⟩ : syracuseStep 232963 = 349445) B349445
theorem B790019 : Blo 231814 790019 := bstep (se 1 (by rfl) ⟨592514, by rfl⟩ : syracuseStep 790019 = 1185029) B1185029
theorem B232979 : Blo 231814 232979 := bstep (se 1 (by rfl) ⟨174734, by rfl⟩ : syracuseStep 232979 = 349469) B349469
theorem B232995 : Blo 231814 232995 := bstep (se 1 (by rfl) ⟨174746, by rfl⟩ : syracuseStep 232995 = 349493) B349493
theorem B527921 : Blo 231814 527921 := bstep (se 2 (by rfl) ⟨197970, by rfl⟩ : syracuseStep 527921 = 395941) B395941
theorem B233011 : Blo 231814 233011 := bstep (se 1 (by rfl) ⟨174758, by rfl⟩ : syracuseStep 233011 = 349517) B349517
theorem B233027 : Blo 231814 233027 := bstep (se 1 (by rfl) ⟨174770, by rfl⟩ : syracuseStep 233027 = 349541) B349541
theorem B527939 : Blo 231814 527939 := bstep (se 1 (by rfl) ⟨395954, by rfl⟩ : syracuseStep 527939 = 791909) B791909
theorem B724547 : Blo 231814 724547 := bstep (se 1 (by rfl) ⟨543410, by rfl⟩ : syracuseStep 724547 = 1086821) B1086821
theorem B233043 : Blo 231814 233043 := bstep (se 1 (by rfl) ⟨174782, by rfl⟩ : syracuseStep 233043 = 349565) B349565
theorem B233059 : Blo 231814 233059 := bstep (se 1 (by rfl) ⟨174794, by rfl⟩ : syracuseStep 233059 = 349589) B349589
theorem B593507 : Blo 231814 593507 := bstep (se 1 (by rfl) ⟨445130, by rfl⟩ : syracuseStep 593507 = 890261) B890261
theorem B396913 : Blo 231814 396913 := bstep (se 2 (by rfl) ⟨148842, by rfl⟩ : syracuseStep 396913 = 297685) B297685
theorem B233075 : Blo 231814 233075 := bstep (se 1 (by rfl) ⟨174806, by rfl⟩ : syracuseStep 233075 = 349613) B349613
theorem B233091 : Blo 231814 233091 := bstep (se 1 (by rfl) ⟨174818, by rfl⟩ : syracuseStep 233091 = 349637) B349637
theorem B2657933 : Blo 231814 2657933 := bstep (se 3 (by rfl) ⟨498362, by rfl⟩ : syracuseStep 2657933 = 996725) B996725
theorem B233107 : Blo 231814 233107 := bstep (se 1 (by rfl) ⟨174830, by rfl⟩ : syracuseStep 233107 = 349661) B349661
theorem B396947 : Blo 231814 396947 := bstep (se 1 (by rfl) ⟨297710, by rfl⟩ : syracuseStep 396947 = 595421) B595421
theorem B233123 : Blo 231814 233123 := bstep (se 1 (by rfl) ⟨174842, by rfl⟩ : syracuseStep 233123 = 349685) B349685
theorem B1183409 : Blo 231814 1183409 := bstep (se 2 (by rfl) ⟨443778, by rfl⟩ : syracuseStep 1183409 = 887557) B887557
theorem B233139 : Blo 231814 233139 := bstep (se 1 (by rfl) ⟨174854, by rfl⟩ : syracuseStep 233139 = 349709) B349709
theorem B233155 : Blo 231814 233155 := bstep (se 1 (by rfl) ⟨174866, by rfl⟩ : syracuseStep 233155 = 349733) B349733
theorem B233171 : Blo 231814 233171 := bstep (se 1 (by rfl) ⟨174878, by rfl⟩ : syracuseStep 233171 = 349757) B349757
theorem B233187 : Blo 231814 233187 := bstep (se 1 (by rfl) ⟨174890, by rfl⟩ : syracuseStep 233187 = 349781) B349781
theorem B233203 : Blo 231814 233203 := bstep (se 1 (by rfl) ⟨174902, by rfl⟩ : syracuseStep 233203 = 349805) B349805
theorem B233219 : Blo 231814 233219 := bstep (se 1 (by rfl) ⟨174914, by rfl⟩ : syracuseStep 233219 = 349829) B349829
theorem B790289 : Blo 231814 790289 := bstep (se 2 (by rfl) ⟨296358, by rfl⟩ : syracuseStep 790289 = 592717) B592717
theorem B233235 : Blo 231814 233235 := bstep (se 1 (by rfl) ⟨174926, by rfl⟩ : syracuseStep 233235 = 349853) B349853
theorem B397075 : Blo 231814 397075 := bstep (se 1 (by rfl) ⟨297806, by rfl⟩ : syracuseStep 397075 = 595613) B595613
theorem B331553 : Blo 231814 331553 := bstep (se 2 (by rfl) ⟨124332, by rfl⟩ : syracuseStep 331553 = 248665) B248665
theorem B233251 : Blo 231814 233251 := bstep (se 1 (by rfl) ⟨174938, by rfl⟩ : syracuseStep 233251 = 349877) B349877
theorem B233267 : Blo 231814 233267 := bstep (se 1 (by rfl) ⟨174950, by rfl⟩ : syracuseStep 233267 = 349901) B349901
theorem B233283 : Blo 231814 233283 := bstep (se 1 (by rfl) ⟨174962, by rfl⟩ : syracuseStep 233283 = 349925) B349925
theorem B1609541 : Blo 231814 1609541 := bstep (se 4 (by rfl) ⟨150894, by rfl⟩ : syracuseStep 1609541 = 301789) B301789
theorem B528209 : Blo 231814 528209 := bstep (se 2 (by rfl) ⟨198078, by rfl⟩ : syracuseStep 528209 = 396157) B396157
theorem B233299 : Blo 231814 233299 := bstep (se 1 (by rfl) ⟨174974, by rfl⟩ : syracuseStep 233299 = 349949) B349949
theorem B233315 : Blo 231814 233315 := bstep (se 1 (by rfl) ⟨174986, by rfl⟩ : syracuseStep 233315 = 349973) B349973
theorem B528227 : Blo 231814 528227 := bstep (se 1 (by rfl) ⟨396170, by rfl⟩ : syracuseStep 528227 = 792341) B792341
theorem B233331 : Blo 231814 233331 := bstep (se 1 (by rfl) ⟨174998, by rfl⟩ : syracuseStep 233331 = 349997) B349997
theorem B233347 : Blo 231814 233347 := bstep (se 1 (by rfl) ⟨175010, by rfl⟩ : syracuseStep 233347 = 350021) B350021
theorem B233363 : Blo 231814 233363 := bstep (se 1 (by rfl) ⟨175022, by rfl⟩ : syracuseStep 233363 = 350045) B350045
theorem B397217 : Blo 231814 397217 := bstep (se 2 (by rfl) ⟨148956, by rfl⟩ : syracuseStep 397217 = 297913) B297913
theorem B397219 : Blo 231814 397219 := bstep (se 1 (by rfl) ⟨297914, by rfl⟩ : syracuseStep 397219 = 595829) B595829
theorem B233379 : Blo 231814 233379 := bstep (se 1 (by rfl) ⟨175034, by rfl⟩ : syracuseStep 233379 = 350069) B350069
theorem B233395 : Blo 231814 233395 := bstep (se 1 (by rfl) ⟨175046, by rfl⟩ : syracuseStep 233395 = 350093) B350093
theorem B233411 : Blo 231814 233411 := bstep (se 1 (by rfl) ⟨175058, by rfl⟩ : syracuseStep 233411 = 350117) B350117
theorem B233427 : Blo 231814 233427 := bstep (se 1 (by rfl) ⟨175070, by rfl⟩ : syracuseStep 233427 = 350141) B350141
theorem B233443 : Blo 231814 233443 := bstep (se 1 (by rfl) ⟨175082, by rfl⟩ : syracuseStep 233443 = 350165) B350165
theorem B888803 : Blo 231814 888803 := bstep (se 1 (by rfl) ⟨666602, by rfl⟩ : syracuseStep 888803 = 1333205) B1333205
theorem B1609699 : Blo 231814 1609699 := bstep (se 1 (by rfl) ⟨1207274, by rfl⟩ : syracuseStep 1609699 = 2414549) B2414549
theorem B233459 : Blo 231814 233459 := bstep (se 1 (by rfl) ⟨175094, by rfl⟩ : syracuseStep 233459 = 350189) B350189
theorem B233475 : Blo 231814 233475 := bstep (se 1 (by rfl) ⟨175106, by rfl⟩ : syracuseStep 233475 = 350213) B350213
theorem B233491 : Blo 231814 233491 := bstep (se 1 (by rfl) ⟨175118, by rfl⟩ : syracuseStep 233491 = 350237) B350237
theorem B397345 : Blo 231814 397345 := bstep (se 2 (by rfl) ⟨149004, by rfl⟩ : syracuseStep 397345 = 298009) B298009
theorem B233507 : Blo 231814 233507 := bstep (se 1 (by rfl) ⟨175130, by rfl⟩ : syracuseStep 233507 = 350261) B350261
theorem B233523 : Blo 231814 233523 := bstep (se 1 (by rfl) ⟨175142, by rfl⟩ : syracuseStep 233523 = 350285) B350285
theorem B233539 : Blo 231814 233539 := bstep (se 1 (by rfl) ⟨175154, by rfl⟩ : syracuseStep 233539 = 350309) B350309
theorem B397379 : Blo 231814 397379 := bstep (se 1 (by rfl) ⟨298034, by rfl⟩ : syracuseStep 397379 = 596069) B596069
theorem B233555 : Blo 231814 233555 := bstep (se 1 (by rfl) ⟨175166, by rfl⟩ : syracuseStep 233555 = 350333) B350333
theorem B495715 : Blo 231814 495715 := bstep (se 1 (by rfl) ⟨371786, by rfl⟩ : syracuseStep 495715 = 743573) B743573
theorem B233571 : Blo 231814 233571 := bstep (se 1 (by rfl) ⟨175178, by rfl⟩ : syracuseStep 233571 = 350357) B350357
theorem B528497 : Blo 231814 528497 := bstep (se 2 (by rfl) ⟨198186, by rfl⟩ : syracuseStep 528497 = 396373) B396373
theorem B233587 : Blo 231814 233587 := bstep (se 1 (by rfl) ⟨175190, by rfl⟩ : syracuseStep 233587 = 350381) B350381
theorem B233603 : Blo 231814 233603 := bstep (se 1 (by rfl) ⟨175202, by rfl⟩ : syracuseStep 233603 = 350405) B350405
theorem B528515 : Blo 231814 528515 := bstep (se 1 (by rfl) ⟨396386, by rfl⟩ : syracuseStep 528515 = 792773) B792773
theorem B233619 : Blo 231814 233619 := bstep (se 1 (by rfl) ⟨175214, by rfl⟩ : syracuseStep 233619 = 350429) B350429
theorem B233635 : Blo 231814 233635 := bstep (se 1 (by rfl) ⟨175226, by rfl⟩ : syracuseStep 233635 = 350453) B350453
theorem B233651 : Blo 231814 233651 := bstep (se 1 (by rfl) ⟨175238, by rfl⟩ : syracuseStep 233651 = 350477) B350477
theorem B233667 : Blo 231814 233667 := bstep (se 1 (by rfl) ⟨175250, by rfl⟩ : syracuseStep 233667 = 350501) B350501
theorem B397507 : Blo 231814 397507 := bstep (se 1 (by rfl) ⟨298130, by rfl⟩ : syracuseStep 397507 = 596261) B596261
theorem B233683 : Blo 231814 233683 := bstep (se 1 (by rfl) ⟨175262, by rfl⟩ : syracuseStep 233683 = 350525) B350525
theorem B233699 : Blo 231814 233699 := bstep (se 1 (by rfl) ⟨175274, by rfl⟩ : syracuseStep 233699 = 350549) B350549
theorem B233715 : Blo 231814 233715 := bstep (se 1 (by rfl) ⟨175286, by rfl⟩ : syracuseStep 233715 = 350573) B350573
theorem B233731 : Blo 231814 233731 := bstep (se 1 (by rfl) ⟨175298, by rfl⟩ : syracuseStep 233731 = 350597) B350597
theorem B233747 : Blo 231814 233747 := bstep (se 1 (by rfl) ⟨175310, by rfl⟩ : syracuseStep 233747 = 350621) B350621
theorem B233763 : Blo 231814 233763 := bstep (se 1 (by rfl) ⟨175322, by rfl⟩ : syracuseStep 233763 = 350645) B350645
theorem B790829 : Blo 231814 790829 := bstep (se 3 (by rfl) ⟨148280, by rfl⟩ : syracuseStep 790829 = 296561) B296561
theorem B233779 : Blo 231814 233779 := bstep (se 1 (by rfl) ⟨175334, by rfl⟩ : syracuseStep 233779 = 350669) B350669
theorem B233795 : Blo 231814 233795 := bstep (se 1 (by rfl) ⟨175346, by rfl⟩ : syracuseStep 233795 = 350693) B350693
theorem B397649 : Blo 231814 397649 := bstep (se 2 (by rfl) ⟨149118, by rfl⟩ : syracuseStep 397649 = 298237) B298237
theorem B233811 : Blo 231814 233811 := bstep (se 1 (by rfl) ⟨175358, by rfl⟩ : syracuseStep 233811 = 350717) B350717
theorem B495971 : Blo 231814 495971 := bstep (se 1 (by rfl) ⟨371978, by rfl⟩ : syracuseStep 495971 = 743957) B743957
theorem B233827 : Blo 231814 233827 := bstep (se 1 (by rfl) ⟨175370, by rfl⟩ : syracuseStep 233827 = 350741) B350741
theorem B790883 : Blo 231814 790883 := bstep (se 1 (by rfl) ⟨593162, by rfl⟩ : syracuseStep 790883 = 1186325) B1186325
theorem B233843 : Blo 231814 233843 := bstep (se 1 (by rfl) ⟨175382, by rfl⟩ : syracuseStep 233843 = 350765) B350765
theorem B233859 : Blo 231814 233859 := bstep (se 1 (by rfl) ⟨175394, by rfl⟩ : syracuseStep 233859 = 350789) B350789
theorem B528785 : Blo 231814 528785 := bstep (se 2 (by rfl) ⟨198294, by rfl⟩ : syracuseStep 528785 = 396589) B396589
theorem B233875 : Blo 231814 233875 := bstep (se 1 (by rfl) ⟨175406, by rfl⟩ : syracuseStep 233875 = 350813) B350813
theorem B233891 : Blo 231814 233891 := bstep (se 1 (by rfl) ⟨175418, by rfl⟩ : syracuseStep 233891 = 350837) B350837
theorem B528803 : Blo 231814 528803 := bstep (se 1 (by rfl) ⟨396602, by rfl⟩ : syracuseStep 528803 = 793205) B793205
theorem B233907 : Blo 231814 233907 := bstep (se 1 (by rfl) ⟨175430, by rfl⟩ : syracuseStep 233907 = 350861) B350861
theorem B233923 : Blo 231814 233923 := bstep (se 1 (by rfl) ⟨175442, by rfl⟩ : syracuseStep 233923 = 350885) B350885
theorem B397777 : Blo 231814 397777 := bstep (se 2 (by rfl) ⟨149166, by rfl⟩ : syracuseStep 397777 = 298333) B298333
theorem B233939 : Blo 231814 233939 := bstep (se 1 (by rfl) ⟨175454, by rfl⟩ : syracuseStep 233939 = 350909) B350909
theorem B233955 : Blo 231814 233955 := bstep (se 1 (by rfl) ⟨175466, by rfl⟩ : syracuseStep 233955 = 350933) B350933
theorem B561649 : Blo 231814 561649 := bstep (se 2 (by rfl) ⟨210618, by rfl⟩ : syracuseStep 561649 = 421237) B421237
theorem B233971 : Blo 231814 233971 := bstep (se 1 (by rfl) ⟨175478, by rfl⟩ : syracuseStep 233971 = 350957) B350957
theorem B397811 : Blo 231814 397811 := bstep (se 1 (by rfl) ⟨298358, by rfl⟩ : syracuseStep 397811 = 596717) B596717
theorem B233987 : Blo 231814 233987 := bstep (se 1 (by rfl) ⟨175490, by rfl⟩ : syracuseStep 233987 = 350981) B350981
theorem B594449 : Blo 231814 594449 := bstep (se 2 (by rfl) ⟨222918, by rfl⟩ : syracuseStep 594449 = 445837) B445837
theorem B234003 : Blo 231814 234003 := bstep (se 1 (by rfl) ⟨175502, by rfl⟩ : syracuseStep 234003 = 351005) B351005
theorem B234019 : Blo 231814 234019 := bstep (se 1 (by rfl) ⟨175514, by rfl⟩ : syracuseStep 234019 = 351029) B351029
theorem B234035 : Blo 231814 234035 := bstep (se 1 (by rfl) ⟨175526, by rfl⟩ : syracuseStep 234035 = 351053) B351053
theorem B234051 : Blo 231814 234051 := bstep (se 1 (by rfl) ⟨175538, by rfl⟩ : syracuseStep 234051 = 351077) B351077
theorem B594499 : Blo 231814 594499 := bstep (se 1 (by rfl) ⟨445874, by rfl⟩ : syracuseStep 594499 = 891749) B891749
theorem B627281 : Blo 231814 627281 := bstep (se 2 (by rfl) ⟨235230, by rfl⟩ : syracuseStep 627281 = 470461) B470461
theorem B234067 : Blo 231814 234067 := bstep (se 1 (by rfl) ⟨175550, by rfl⟩ : syracuseStep 234067 = 351101) B351101
theorem B234083 : Blo 231814 234083 := bstep (se 1 (by rfl) ⟨175562, by rfl⟩ : syracuseStep 234083 = 351125) B351125
theorem B791153 : Blo 231814 791153 := bstep (se 2 (by rfl) ⟨296682, by rfl⟩ : syracuseStep 791153 = 593365) B593365
theorem B234099 : Blo 231814 234099 := bstep (se 1 (by rfl) ⟨175574, by rfl⟩ : syracuseStep 234099 = 351149) B351149
theorem B332419 : Blo 231814 332419 := bstep (se 1 (by rfl) ⟨249314, by rfl⟩ : syracuseStep 332419 = 498629) B498629
theorem B234115 : Blo 231814 234115 := bstep (se 1 (by rfl) ⟨175586, by rfl⟩ : syracuseStep 234115 = 351173) B351173
theorem B234131 : Blo 231814 234131 := bstep (se 1 (by rfl) ⟨175598, by rfl⟩ : syracuseStep 234131 = 351197) B351197
theorem B234147 : Blo 231814 234147 := bstep (se 1 (by rfl) ⟨175610, by rfl⟩ : syracuseStep 234147 = 351221) B351221
theorem B529073 : Blo 231814 529073 := bstep (se 2 (by rfl) ⟨198402, by rfl⟩ : syracuseStep 529073 = 396805) B396805
theorem B234163 : Blo 231814 234163 := bstep (se 1 (by rfl) ⟨175622, by rfl⟩ : syracuseStep 234163 = 351245) B351245
theorem B234179 : Blo 231814 234179 := bstep (se 1 (by rfl) ⟨175634, by rfl⟩ : syracuseStep 234179 = 351269) B351269
theorem B529091 : Blo 231814 529091 := bstep (se 1 (by rfl) ⟨396818, by rfl⟩ : syracuseStep 529091 = 793637) B793637
theorem B594641 : Blo 231814 594641 := bstep (se 2 (by rfl) ⟨222990, by rfl⟩ : syracuseStep 594641 = 445981) B445981
theorem B234195 : Blo 231814 234195 := bstep (se 1 (by rfl) ⟨175646, by rfl⟩ : syracuseStep 234195 = 351293) B351293
theorem B332515 : Blo 231814 332515 := bstep (se 1 (by rfl) ⟨249386, by rfl⟩ : syracuseStep 332515 = 498773) B498773
theorem B234211 : Blo 231814 234211 := bstep (se 1 (by rfl) ⟨175658, by rfl⟩ : syracuseStep 234211 = 351317) B351317
theorem B234227 : Blo 231814 234227 := bstep (se 1 (by rfl) ⟨175670, by rfl⟩ : syracuseStep 234227 = 351341) B351341
theorem B234243 : Blo 231814 234243 := bstep (se 1 (by rfl) ⟨175682, by rfl⟩ : syracuseStep 234243 = 351365) B351365
theorem B234259 : Blo 231814 234259 := bstep (se 1 (by rfl) ⟨175694, by rfl⟩ : syracuseStep 234259 = 351389) B351389
theorem B234275 : Blo 231814 234275 := bstep (se 1 (by rfl) ⟨175706, by rfl⟩ : syracuseStep 234275 = 351413) B351413
theorem B234291 : Blo 231814 234291 := bstep (se 1 (by rfl) ⟨175718, by rfl⟩ : syracuseStep 234291 = 351437) B351437
theorem B234307 : Blo 231814 234307 := bstep (se 1 (by rfl) ⟨175730, by rfl⟩ : syracuseStep 234307 = 351461) B351461
theorem B234323 : Blo 231814 234323 := bstep (se 1 (by rfl) ⟨175742, by rfl⟩ : syracuseStep 234323 = 351485) B351485
theorem B234339 : Blo 231814 234339 := bstep (se 1 (by rfl) ⟨175754, by rfl⟩ : syracuseStep 234339 = 351509) B351509
theorem B234355 : Blo 231814 234355 := bstep (se 1 (by rfl) ⟨175766, by rfl⟩ : syracuseStep 234355 = 351533) B351533
theorem B234371 : Blo 231814 234371 := bstep (se 1 (by rfl) ⟨175778, by rfl⟩ : syracuseStep 234371 = 351557) B351557
theorem B398225 : Blo 231814 398225 := bstep (se 2 (by rfl) ⟨149334, by rfl⟩ : syracuseStep 398225 = 298669) B298669
theorem B234387 : Blo 231814 234387 := bstep (se 1 (by rfl) ⟨175790, by rfl⟩ : syracuseStep 234387 = 351581) B351581
theorem B234403 : Blo 231814 234403 := bstep (se 1 (by rfl) ⟨175802, by rfl⟩ : syracuseStep 234403 = 351605) B351605
theorem B234419 : Blo 231814 234419 := bstep (se 1 (by rfl) ⟨175814, by rfl⟩ : syracuseStep 234419 = 351629) B351629
theorem B234435 : Blo 231814 234435 := bstep (se 1 (by rfl) ⟨175826, by rfl⟩ : syracuseStep 234435 = 351653) B351653
theorem B889805 : Blo 231814 889805 := bstep (se 3 (by rfl) ⟨166838, by rfl⟩ : syracuseStep 889805 = 333677) B333677
theorem B529361 : Blo 231814 529361 := bstep (se 2 (by rfl) ⟨198510, by rfl⟩ : syracuseStep 529361 = 397021) B397021
theorem B234451 : Blo 231814 234451 := bstep (se 1 (by rfl) ⟨175838, by rfl⟩ : syracuseStep 234451 = 351677) B351677
theorem B234467 : Blo 231814 234467 := bstep (se 1 (by rfl) ⟨175850, by rfl⟩ : syracuseStep 234467 = 351701) B351701
theorem B529379 : Blo 231814 529379 := bstep (se 1 (by rfl) ⟨397034, by rfl⟩ : syracuseStep 529379 = 794069) B794069
theorem B234483 : Blo 231814 234483 := bstep (se 1 (by rfl) ⟨175862, by rfl⟩ : syracuseStep 234483 = 351725) B351725
theorem B234499 : Blo 231814 234499 := bstep (se 1 (by rfl) ⟨175874, by rfl⟩ : syracuseStep 234499 = 351749) B351749
theorem B234515 : Blo 231814 234515 := bstep (se 1 (by rfl) ⟨175886, by rfl⟩ : syracuseStep 234515 = 351773) B351773
theorem B234531 : Blo 231814 234531 := bstep (se 1 (by rfl) ⟨175898, by rfl⟩ : syracuseStep 234531 = 351797) B351797
theorem B234547 : Blo 231814 234547 := bstep (se 1 (by rfl) ⟨175910, by rfl⟩ : syracuseStep 234547 = 351821) B351821
theorem B234563 : Blo 231814 234563 := bstep (se 1 (by rfl) ⟨175922, by rfl⟩ : syracuseStep 234563 = 351845) B351845
theorem B234579 : Blo 231814 234579 := bstep (se 1 (by rfl) ⟨175934, by rfl⟩ : syracuseStep 234579 = 351869) B351869
theorem B529507 : Blo 231814 529507 := bstep (se 1 (by rfl) ⟨397130, by rfl⟩ : syracuseStep 529507 = 794261) B794261
theorem B1184867 : Blo 231814 1184867 := bstep (se 1 (by rfl) ⟨888650, by rfl⟩ : syracuseStep 1184867 = 1777301) B1777301
theorem B234595 : Blo 231814 234595 := bstep (se 1 (by rfl) ⟨175946, by rfl⟩ : syracuseStep 234595 = 351893) B351893
theorem B234611 : Blo 231814 234611 := bstep (se 1 (by rfl) ⟨175958, by rfl⟩ : syracuseStep 234611 = 351917) B351917
theorem B660611 : Blo 231814 660611 := bstep (se 1 (by rfl) ⟨495458, by rfl⟩ : syracuseStep 660611 = 990917) B990917
theorem B234627 : Blo 231814 234627 := bstep (se 1 (by rfl) ⟨175970, by rfl⟩ : syracuseStep 234627 = 351941) B351941
theorem B791693 : Blo 231814 791693 := bstep (se 3 (by rfl) ⟨148442, by rfl⟩ : syracuseStep 791693 = 296885) B296885
theorem B234643 : Blo 231814 234643 := bstep (se 1 (by rfl) ⟨175982, by rfl⟩ : syracuseStep 234643 = 351965) B351965
theorem B1119395 : Blo 231814 1119395 := bstep (se 1 (by rfl) ⟨839546, by rfl⟩ : syracuseStep 1119395 = 1679093) B1679093
theorem B234659 : Blo 231814 234659 := bstep (se 1 (by rfl) ⟨175994, by rfl⟩ : syracuseStep 234659 = 351989) B351989
theorem B234675 : Blo 231814 234675 := bstep (se 1 (by rfl) ⟨176006, by rfl⟩ : syracuseStep 234675 = 352013) B352013
theorem B791747 : Blo 231814 791747 := bstep (se 1 (by rfl) ⟨593810, by rfl⟩ : syracuseStep 791747 = 1187621) B1187621
theorem B234691 : Blo 231814 234691 := bstep (se 1 (by rfl) ⟨176018, by rfl⟩ : syracuseStep 234691 = 352037) B352037
theorem B333011 : Blo 231814 333011 := bstep (se 1 (by rfl) ⟨249758, by rfl⟩ : syracuseStep 333011 = 499517) B499517
theorem B234707 : Blo 231814 234707 := bstep (se 1 (by rfl) ⟨176030, by rfl⟩ : syracuseStep 234707 = 352061) B352061
theorem B234723 : Blo 231814 234723 := bstep (se 1 (by rfl) ⟨176042, by rfl⟩ : syracuseStep 234723 = 352085) B352085
theorem B529649 : Blo 231814 529649 := bstep (se 2 (by rfl) ⟨198618, by rfl⟩ : syracuseStep 529649 = 397237) B397237
theorem B234739 : Blo 231814 234739 := bstep (se 1 (by rfl) ⟨176054, by rfl⟩ : syracuseStep 234739 = 352109) B352109
theorem B234755 : Blo 231814 234755 := bstep (se 1 (by rfl) ⟨176066, by rfl⟩ : syracuseStep 234755 = 352133) B352133
theorem B529667 : Blo 231814 529667 := bstep (se 1 (by rfl) ⟨397250, by rfl⟩ : syracuseStep 529667 = 794501) B794501
theorem B234771 : Blo 231814 234771 := bstep (se 1 (by rfl) ⟨176078, by rfl⟩ : syracuseStep 234771 = 352157) B352157
theorem B234787 : Blo 231814 234787 := bstep (se 1 (by rfl) ⟨176090, by rfl⟩ : syracuseStep 234787 = 352181) B352181
theorem B496945 : Blo 231814 496945 := bstep (se 2 (by rfl) ⟨186354, by rfl⟩ : syracuseStep 496945 = 372709) B372709
theorem B234803 : Blo 231814 234803 := bstep (se 1 (by rfl) ⟨176102, by rfl⟩ : syracuseStep 234803 = 352205) B352205
theorem B234819 : Blo 231814 234819 := bstep (se 1 (by rfl) ⟨176114, by rfl⟩ : syracuseStep 234819 = 352229) B352229
theorem B1611085 : Blo 231814 1611085 := bstep (se 3 (by rfl) ⟨302078, by rfl⟩ : syracuseStep 1611085 = 604157) B604157
theorem B234835 : Blo 231814 234835 := bstep (se 1 (by rfl) ⟨176126, by rfl⟩ : syracuseStep 234835 = 352253) B352253
theorem B234851 : Blo 231814 234851 := bstep (se 1 (by rfl) ⟨176138, by rfl⟩ : syracuseStep 234851 = 352277) B352277
theorem B234867 : Blo 231814 234867 := bstep (se 1 (by rfl) ⟨176150, by rfl⟩ : syracuseStep 234867 = 352301) B352301
theorem B234883 : Blo 231814 234883 := bstep (se 1 (by rfl) ⟨176162, by rfl⟩ : syracuseStep 234883 = 352325) B352325
theorem B234899 : Blo 231814 234899 := bstep (se 1 (by rfl) ⟨176174, by rfl⟩ : syracuseStep 234899 = 352349) B352349
theorem B234915 : Blo 231814 234915 := bstep (se 1 (by rfl) ⟨176186, by rfl⟩ : syracuseStep 234915 = 352373) B352373
theorem B234931 : Blo 231814 234931 := bstep (se 1 (by rfl) ⟨176198, by rfl⟩ : syracuseStep 234931 = 352397) B352397
theorem B234947 : Blo 231814 234947 := bstep (se 1 (by rfl) ⟨176210, by rfl⟩ : syracuseStep 234947 = 352421) B352421
theorem B792017 : Blo 231814 792017 := bstep (se 2 (by rfl) ⟨297006, by rfl⟩ : syracuseStep 792017 = 594013) B594013
theorem B234963 : Blo 231814 234963 := bstep (se 1 (by rfl) ⟨176222, by rfl⟩ : syracuseStep 234963 = 352445) B352445
theorem B234979 : Blo 231814 234979 := bstep (se 1 (by rfl) ⟨176234, by rfl⟩ : syracuseStep 234979 = 352469) B352469
theorem B234995 : Blo 231814 234995 := bstep (se 1 (by rfl) ⟨176246, by rfl⟩ : syracuseStep 234995 = 352493) B352493
theorem B235011 : Blo 231814 235011 := bstep (se 1 (by rfl) ⟨176258, by rfl⟩ : syracuseStep 235011 = 352517) B352517
theorem B529937 : Blo 231814 529937 := bstep (se 2 (by rfl) ⟨198726, by rfl⟩ : syracuseStep 529937 = 397453) B397453
theorem B235027 : Blo 231814 235027 := bstep (se 1 (by rfl) ⟨176270, by rfl⟩ : syracuseStep 235027 = 352541) B352541
theorem B235043 : Blo 231814 235043 := bstep (se 1 (by rfl) ⟨176282, by rfl⟩ : syracuseStep 235043 = 352565) B352565
theorem B529955 : Blo 231814 529955 := bstep (se 1 (by rfl) ⟨397466, by rfl⟩ : syracuseStep 529955 = 794933) B794933
theorem B235059 : Blo 231814 235059 := bstep (se 1 (by rfl) ⟨176294, by rfl⟩ : syracuseStep 235059 = 352589) B352589
theorem B235075 : Blo 231814 235075 := bstep (se 1 (by rfl) ⟨176306, by rfl⟩ : syracuseStep 235075 = 352613) B352613
theorem B235091 : Blo 231814 235091 := bstep (se 1 (by rfl) ⟨176318, by rfl⟩ : syracuseStep 235091 = 352637) B352637
theorem B235107 : Blo 231814 235107 := bstep (se 1 (by rfl) ⟨176330, by rfl⟩ : syracuseStep 235107 = 352661) B352661
theorem B2692721 : Blo 231814 2692721 := bstep (se 2 (by rfl) ⟨1009770, by rfl⟩ : syracuseStep 2692721 = 2019541) B2019541
theorem B235123 : Blo 231814 235123 := bstep (se 1 (by rfl) ⟨176342, by rfl⟩ : syracuseStep 235123 = 352685) B352685
theorem B235139 : Blo 231814 235139 := bstep (se 1 (by rfl) ⟨176354, by rfl⟩ : syracuseStep 235139 = 352709) B352709
theorem B235155 : Blo 231814 235155 := bstep (se 1 (by rfl) ⟨176366, by rfl⟩ : syracuseStep 235155 = 352733) B352733
theorem B235171 : Blo 231814 235171 := bstep (se 1 (by rfl) ⟨176378, by rfl⟩ : syracuseStep 235171 = 352757) B352757
theorem B595633 : Blo 231814 595633 := bstep (se 2 (by rfl) ⟨223362, by rfl⟩ : syracuseStep 595633 = 446725) B446725
theorem B235187 : Blo 231814 235187 := bstep (se 1 (by rfl) ⟨176390, by rfl⟩ : syracuseStep 235187 = 352781) B352781
theorem B235203 : Blo 231814 235203 := bstep (se 1 (by rfl) ⟨176402, by rfl⟩ : syracuseStep 235203 = 352805) B352805
theorem B235219 : Blo 231814 235219 := bstep (se 1 (by rfl) ⟨176414, by rfl⟩ : syracuseStep 235219 = 352829) B352829
theorem B235235 : Blo 231814 235235 := bstep (se 1 (by rfl) ⟨176426, by rfl⟩ : syracuseStep 235235 = 352853) B352853
theorem B235251 : Blo 231814 235251 := bstep (se 1 (by rfl) ⟨176438, by rfl⟩ : syracuseStep 235251 = 352877) B352877
theorem B235267 : Blo 231814 235267 := bstep (se 1 (by rfl) ⟨176450, by rfl⟩ : syracuseStep 235267 = 352901) B352901
theorem B235283 : Blo 231814 235283 := bstep (se 1 (by rfl) ⟨176462, by rfl⟩ : syracuseStep 235283 = 352925) B352925
theorem B235299 : Blo 231814 235299 := bstep (se 1 (by rfl) ⟨176474, by rfl⟩ : syracuseStep 235299 = 352949) B352949
theorem B530225 : Blo 231814 530225 := bstep (se 2 (by rfl) ⟨198834, by rfl⟩ : syracuseStep 530225 = 397669) B397669
theorem B235315 : Blo 231814 235315 := bstep (se 1 (by rfl) ⟨176486, by rfl⟩ : syracuseStep 235315 = 352973) B352973
theorem B235331 : Blo 231814 235331 := bstep (se 1 (by rfl) ⟨176498, by rfl⟩ : syracuseStep 235331 = 352997) B352997
theorem B530243 : Blo 231814 530243 := bstep (se 1 (by rfl) ⟨397682, by rfl⟩ : syracuseStep 530243 = 795365) B795365
theorem B333649 : Blo 231814 333649 := bstep (se 2 (by rfl) ⟨125118, by rfl⟩ : syracuseStep 333649 = 250237) B250237
theorem B235347 : Blo 231814 235347 := bstep (se 1 (by rfl) ⟨176510, by rfl⟩ : syracuseStep 235347 = 353021) B353021
theorem B235363 : Blo 231814 235363 := bstep (se 1 (by rfl) ⟨176522, by rfl⟩ : syracuseStep 235363 = 353045) B353045
theorem B235379 : Blo 231814 235379 := bstep (se 1 (by rfl) ⟨176534, by rfl⟩ : syracuseStep 235379 = 353069) B353069
theorem B235395 : Blo 231814 235395 := bstep (se 1 (by rfl) ⟨176546, by rfl⟩ : syracuseStep 235395 = 353093) B353093
theorem B1185677 : Blo 231814 1185677 := bstep (se 3 (by rfl) ⟨222314, by rfl⟩ : syracuseStep 1185677 = 444629) B444629
theorem B235411 : Blo 231814 235411 := bstep (se 1 (by rfl) ⟨176558, by rfl⟩ : syracuseStep 235411 = 353117) B353117
theorem B235427 : Blo 231814 235427 := bstep (se 1 (by rfl) ⟨176570, by rfl⟩ : syracuseStep 235427 = 353141) B353141
theorem B235443 : Blo 231814 235443 := bstep (se 1 (by rfl) ⟨176582, by rfl⟩ : syracuseStep 235443 = 353165) B353165
theorem B497603 : Blo 231814 497603 := bstep (se 1 (by rfl) ⟨373202, by rfl⟩ : syracuseStep 497603 = 746405) B746405
theorem B595907 : Blo 231814 595907 := bstep (se 1 (by rfl) ⟨446930, by rfl⟩ : syracuseStep 595907 = 893861) B893861
theorem B235459 : Blo 231814 235459 := bstep (se 1 (by rfl) ⟨176594, by rfl⟩ : syracuseStep 235459 = 353189) B353189
theorem B235475 : Blo 231814 235475 := bstep (se 1 (by rfl) ⟨176606, by rfl⟩ : syracuseStep 235475 = 353213) B353213
theorem B235491 : Blo 231814 235491 := bstep (se 1 (by rfl) ⟨176618, by rfl⟩ : syracuseStep 235491 = 353237) B353237
theorem B792557 : Blo 231814 792557 := bstep (se 3 (by rfl) ⟨148604, by rfl⟩ : syracuseStep 792557 = 297209) B297209
theorem B235507 : Blo 231814 235507 := bstep (se 1 (by rfl) ⟨176630, by rfl⟩ : syracuseStep 235507 = 353261) B353261
theorem B235523 : Blo 231814 235523 := bstep (se 1 (by rfl) ⟨176642, by rfl⟩ : syracuseStep 235523 = 353285) B353285
theorem B235539 : Blo 231814 235539 := bstep (se 1 (by rfl) ⟨176654, by rfl⟩ : syracuseStep 235539 = 353309) B353309
theorem B792611 : Blo 231814 792611 := bstep (se 1 (by rfl) ⟨594458, by rfl⟩ : syracuseStep 792611 = 1188917) B1188917
theorem B235555 : Blo 231814 235555 := bstep (se 1 (by rfl) ⟨176666, by rfl⟩ : syracuseStep 235555 = 353333) B353333
theorem B235571 : Blo 231814 235571 := bstep (se 1 (by rfl) ⟨176678, by rfl⟩ : syracuseStep 235571 = 353357) B353357
theorem B235587 : Blo 231814 235587 := bstep (se 1 (by rfl) ⟨176690, by rfl⟩ : syracuseStep 235587 = 353381) B353381
theorem B530513 : Blo 231814 530513 := bstep (se 2 (by rfl) ⟨198942, by rfl⟩ : syracuseStep 530513 = 397885) B397885
theorem B235603 : Blo 231814 235603 := bstep (se 1 (by rfl) ⟨176702, by rfl⟩ : syracuseStep 235603 = 353405) B353405
theorem B235619 : Blo 231814 235619 := bstep (se 1 (by rfl) ⟨176714, by rfl⟩ : syracuseStep 235619 = 353429) B353429
theorem B530531 : Blo 231814 530531 := bstep (se 1 (by rfl) ⟨397898, by rfl⟩ : syracuseStep 530531 = 795797) B795797
theorem B235635 : Blo 231814 235635 := bstep (se 1 (by rfl) ⟨176726, by rfl⟩ : syracuseStep 235635 = 353453) B353453
theorem B596099 : Blo 231814 596099 := bstep (se 1 (by rfl) ⟨447074, by rfl⟩ : syracuseStep 596099 = 894149) B894149
theorem B235651 : Blo 231814 235651 := bstep (se 1 (by rfl) ⟨176738, by rfl⟩ : syracuseStep 235651 = 353477) B353477
theorem B235667 : Blo 231814 235667 := bstep (se 1 (by rfl) ⟨176750, by rfl⟩ : syracuseStep 235667 = 353501) B353501
theorem B333985 : Blo 231814 333985 := bstep (se 2 (by rfl) ⟨125244, by rfl⟩ : syracuseStep 333985 = 250489) B250489
theorem B235683 : Blo 231814 235683 := bstep (se 1 (by rfl) ⟨176762, by rfl⟩ : syracuseStep 235683 = 353525) B353525
theorem B235699 : Blo 231814 235699 := bstep (se 1 (by rfl) ⟨176774, by rfl⟩ : syracuseStep 235699 = 353549) B353549
theorem B235715 : Blo 231814 235715 := bstep (se 1 (by rfl) ⟨176786, by rfl⟩ : syracuseStep 235715 = 353573) B353573
theorem B1808581 : Blo 231814 1808581 := bstep (se 4 (by rfl) ⟨169554, by rfl⟩ : syracuseStep 1808581 = 339109) B339109
theorem B235731 : Blo 231814 235731 := bstep (se 1 (by rfl) ⟨176798, by rfl⟩ : syracuseStep 235731 = 353597) B353597
theorem B1775843 : Blo 231814 1775843 := bstep (se 1 (by rfl) ⟨1331882, by rfl⟩ : syracuseStep 1775843 = 2663765) B2663765
theorem B235747 : Blo 231814 235747 := bstep (se 1 (by rfl) ⟨176810, by rfl⟩ : syracuseStep 235747 = 353621) B353621
theorem B235763 : Blo 231814 235763 := bstep (se 1 (by rfl) ⟨176822, by rfl⟩ : syracuseStep 235763 = 353645) B353645
theorem B235779 : Blo 231814 235779 := bstep (se 1 (by rfl) ⟨176834, by rfl⟩ : syracuseStep 235779 = 353669) B353669
theorem B235795 : Blo 231814 235795 := bstep (se 1 (by rfl) ⟨176846, by rfl⟩ : syracuseStep 235795 = 353693) B353693
theorem B235811 : Blo 231814 235811 := bstep (se 1 (by rfl) ⟨176858, by rfl⟩ : syracuseStep 235811 = 353717) B353717
theorem B792881 : Blo 231814 792881 := bstep (se 2 (by rfl) ⟨297330, by rfl⟩ : syracuseStep 792881 = 594661) B594661
theorem B661841 : Blo 231814 661841 := bstep (se 2 (by rfl) ⟨248190, by rfl⟩ : syracuseStep 661841 = 496381) B496381
theorem B1120625 : Blo 231814 1120625 := bstep (se 2 (by rfl) ⟨420234, by rfl⟩ : syracuseStep 1120625 = 840469) B840469
theorem B399745 : Blo 231814 399745 := bstep (se 2 (by rfl) ⟨149904, by rfl⟩ : syracuseStep 399745 = 299809) B299809
theorem B2660849 : Blo 231814 2660849 := bstep (se 2 (by rfl) ⟨997818, by rfl⟩ : syracuseStep 2660849 = 1995637) B1995637
theorem B596497 : Blo 231814 596497 := bstep (se 2 (by rfl) ⟨223686, by rfl⟩ : syracuseStep 596497 = 447373) B447373
theorem B334577 : Blo 231814 334577 := bstep (se 2 (by rfl) ⟨125466, by rfl⟩ : syracuseStep 334577 = 250933) B250933
theorem B498449 : Blo 231814 498449 := bstep (se 2 (by rfl) ⟨186918, by rfl⟩ : syracuseStep 498449 = 373837) B373837
theorem B793421 : Blo 231814 793421 := bstep (se 3 (by rfl) ⟨148766, by rfl⟩ : syracuseStep 793421 = 297533) B297533
theorem B2988899 : Blo 231814 2988899 := bstep (se 1 (by rfl) ⟨2241674, by rfl⟩ : syracuseStep 2988899 = 4483349) B4483349
theorem B793475 : Blo 231814 793475 := bstep (se 1 (by rfl) ⟨595106, by rfl⟩ : syracuseStep 793475 = 1190213) B1190213
theorem B891917 : Blo 231814 891917 := bstep (se 3 (by rfl) ⟨167234, by rfl⟩ : syracuseStep 891917 = 334469) B334469
theorem B5676085 : Blo 231814 5676085 := bstep (se 5 (by rfl) ⟨266066, by rfl⟩ : syracuseStep 5676085 = 532133) B532133
theorem B793745 : Blo 231814 793745 := bstep (se 2 (by rfl) ⟨297654, by rfl⟩ : syracuseStep 793745 = 595309) B595309
theorem B302275 : Blo 231814 302275 := bstep (se 1 (by rfl) ⟨226706, by rfl⟩ : syracuseStep 302275 = 453413) B453413
theorem B335107 : Blo 231814 335107 := bstep (se 1 (by rfl) ⟨251330, by rfl⟩ : syracuseStep 335107 = 502661) B502661
theorem B335443 : Blo 231814 335443 := bstep (se 1 (by rfl) ⟨251582, by rfl⟩ : syracuseStep 335443 = 503165) B503165
theorem B794285 : Blo 231814 794285 := bstep (se 3 (by rfl) ⟨148928, by rfl⟩ : syracuseStep 794285 = 297857) B297857
theorem B794339 : Blo 231814 794339 := bstep (se 1 (by rfl) ⟨595754, by rfl⟩ : syracuseStep 794339 = 1191509) B1191509
theorem B663299 : Blo 231814 663299 := bstep (se 1 (by rfl) ⟨497474, by rfl⟩ : syracuseStep 663299 = 994949) B994949
theorem B892721 : Blo 231814 892721 := bstep (se 2 (by rfl) ⟨334770, by rfl⟩ : syracuseStep 892721 = 669541) B669541
theorem B794609 : Blo 231814 794609 := bstep (se 2 (by rfl) ⟨297978, by rfl⟩ : syracuseStep 794609 = 595957) B595957
theorem B5480561 : Blo 231814 5480561 := bstep (se 2 (by rfl) ⟨2055210, by rfl⟩ : syracuseStep 5480561 = 4110421) B4110421
theorem B991601 : Blo 231814 991601 := bstep (se 2 (by rfl) ⟨371850, by rfl⟩ : syracuseStep 991601 = 743701) B743701
theorem B893389 : Blo 231814 893389 := bstep (se 3 (by rfl) ⟨167510, by rfl⟩ : syracuseStep 893389 = 335021) B335021
theorem B795149 : Blo 231814 795149 := bstep (se 3 (by rfl) ⟨149090, by rfl⟩ : syracuseStep 795149 = 298181) B298181
theorem B664109 : Blo 231814 664109 := bstep (se 3 (by rfl) ⟨124520, by rfl⟩ : syracuseStep 664109 = 249041) B249041
theorem B795203 : Blo 231814 795203 := bstep (se 1 (by rfl) ⟨596402, by rfl⟩ : syracuseStep 795203 = 1192805) B1192805
theorem B565955 : Blo 231814 565955 := bstep (se 1 (by rfl) ⟨424466, by rfl⟩ : syracuseStep 565955 = 848933) B848933
theorem B664301 : Blo 231814 664301 := bstep (se 3 (by rfl) ⟨124556, by rfl⟩ : syracuseStep 664301 = 249113) B249113
theorem B1188593 : Blo 231814 1188593 := bstep (se 2 (by rfl) ⟨445722, by rfl⟩ : syracuseStep 1188593 = 891445) B891445
theorem B1123085 : Blo 231814 1123085 := bstep (se 3 (by rfl) ⟨210578, by rfl⟩ : syracuseStep 1123085 = 421157) B421157
theorem B795473 : Blo 231814 795473 := bstep (se 2 (by rfl) ⟨298302, by rfl⟩ : syracuseStep 795473 = 596605) B596605
theorem B631651 : Blo 231814 631651 := bstep (se 1 (by rfl) ⟨473738, by rfl⟩ : syracuseStep 631651 = 947477) B947477
theorem B238819 : Blo 231814 238819 := bstep (se 1 (by rfl) ⟨179114, by rfl⟩ : syracuseStep 238819 = 358229) B358229
theorem B337123 : Blo 231814 337123 := bstep (se 1 (by rfl) ⟨252842, by rfl⟩ : syracuseStep 337123 = 505685) B505685
theorem B894179 : Blo 231814 894179 := bstep (se 1 (by rfl) ⟨670634, by rfl⟩ : syracuseStep 894179 = 1341269) B1341269
theorem B1680709 : Blo 231814 1680709 := bstep (se 4 (by rfl) ⟨157566, by rfl⟩ : syracuseStep 1680709 = 315133) B315133
theorem B20194757 : Blo 231814 20194757 := bstep (se 4 (by rfl) ⟨1893258, by rfl⟩ : syracuseStep 20194757 = 3786517) B3786517
theorem B501233 : Blo 231814 501233 := bstep (se 2 (by rfl) ⟨187962, by rfl⟩ : syracuseStep 501233 = 375925) B375925
theorem B1058467 : Blo 231814 1058467 := bstep (se 1 (by rfl) ⟨793850, by rfl⟩ : syracuseStep 1058467 = 1587701) B1587701
theorem B665293 : Blo 231814 665293 := bstep (se 3 (by rfl) ⟨124742, by rfl⟩ : syracuseStep 665293 = 249485) B249485
theorem B337699 : Blo 231814 337699 := bstep (se 1 (by rfl) ⟨253274, by rfl⟩ : syracuseStep 337699 = 506549) B506549
theorem B894833 : Blo 231814 894833 := bstep (se 2 (by rfl) ⟨335562, by rfl⟩ : syracuseStep 894833 = 671125) B671125
theorem B993293 : Blo 231814 993293 := bstep (se 3 (by rfl) ⟨186242, by rfl⟩ : syracuseStep 993293 = 372485) B372485
theorem B1190051 : Blo 231814 1190051 := bstep (se 1 (by rfl) ⟨892538, by rfl⟩ : syracuseStep 1190051 = 1785077) B1785077
theorem B1255601 : Blo 231814 1255601 := bstep (se 2 (by rfl) ⟨470850, by rfl⟩ : syracuseStep 1255601 = 941701) B941701
theorem B633251 : Blo 231814 633251 := bstep (se 1 (by rfl) ⟨474938, by rfl⟩ : syracuseStep 633251 = 949877) B949877
theorem B1452593 : Blo 231814 1452593 := bstep (se 2 (by rfl) ⟨544722, by rfl⟩ : syracuseStep 1452593 = 1089445) B1089445
theorem B1321541 : Blo 231814 1321541 := bstep (se 4 (by rfl) ⟨123894, by rfl⟩ : syracuseStep 1321541 = 247789) B247789
theorem B371363 : Blo 231814 371363 := bstep (se 1 (by rfl) ⟨278522, by rfl⟩ : syracuseStep 371363 = 557045) B557045
theorem B371441 : Blo 231814 371441 := bstep (se 2 (by rfl) ⟨139290, by rfl⟩ : syracuseStep 371441 = 278581) B278581
theorem B1190861 : Blo 231814 1190861 := bstep (se 3 (by rfl) ⟨223286, by rfl⟩ : syracuseStep 1190861 = 446573) B446573
theorem B371665 : Blo 231814 371665 := bstep (se 2 (by rfl) ⟨139374, by rfl⟩ : syracuseStep 371665 = 278749) B278749
theorem B1485965 : Blo 231814 1485965 := bstep (se 3 (by rfl) ⟨278618, by rfl⟩ : syracuseStep 1485965 = 557237) B557237
theorem B339329 : Blo 231814 339329 := bstep (se 2 (by rfl) ⟨127248, by rfl⟩ : syracuseStep 339329 = 254497) B254497
theorem B667025 : Blo 231814 667025 := bstep (se 2 (by rfl) ⟨250134, by rfl⟩ : syracuseStep 667025 = 500269) B500269
theorem B1781189 : Blo 231814 1781189 := bstep (se 4 (by rfl) ⟨166986, by rfl⟩ : syracuseStep 1781189 = 333973) B333973
theorem B667217 : Blo 231814 667217 := bstep (se 2 (by rfl) ⟨250206, by rfl⟩ : syracuseStep 667217 = 500413) B500413
theorem B6893333 : Blo 231814 6893333 := bstep (se 6 (by rfl) ⟨161562, by rfl⟩ : syracuseStep 6893333 = 323125) B323125
theorem B1257329 : Blo 231814 1257329 := bstep (se 2 (by rfl) ⟨471498, by rfl⟩ : syracuseStep 1257329 = 942997) B942997
theorem B1257677 : Blo 231814 1257677 := bstep (se 3 (by rfl) ⟨235814, by rfl⟩ : syracuseStep 1257677 = 471629) B471629
theorem B668209 : Blo 231814 668209 := bstep (se 2 (by rfl) ⟨250578, by rfl⟩ : syracuseStep 668209 = 501157) B501157
theorem B4239985 : Blo 231814 4239985 := bstep (se 2 (by rfl) ⟨1589994, by rfl⟩ : syracuseStep 4239985 = 3179989) B3179989
theorem B373427 : Blo 231814 373427 := bstep (se 1 (by rfl) ⟨280070, by rfl⟩ : syracuseStep 373427 = 560141) B560141
theorem B1880803 : Blo 231814 1880803 := bstep (se 1 (by rfl) ⟨1410602, by rfl⟩ : syracuseStep 1880803 = 2821205) B2821205
theorem B668483 : Blo 231814 668483 := bstep (se 1 (by rfl) ⟨501362, by rfl⟩ : syracuseStep 668483 = 1002725) B1002725
theorem B373619 : Blo 231814 373619 := bstep (se 1 (by rfl) ⟨280214, by rfl⟩ : syracuseStep 373619 = 560429) B560429
theorem B373747 : Blo 231814 373747 := bstep (se 1 (by rfl) ⟨280310, by rfl⟩ : syracuseStep 373747 = 560621) B560621
theorem B668675 : Blo 231814 668675 := bstep (se 1 (by rfl) ⟨501506, by rfl⟩ : syracuseStep 668675 = 1003013) B1003013
theorem B2700485 : Blo 231814 2700485 := bstep (se 4 (by rfl) ⟨253170, by rfl⟩ : syracuseStep 2700485 = 506341) B506341
theorem B1422917 : Blo 231814 1422917 := bstep (se 4 (by rfl) ⟨133398, by rfl⟩ : syracuseStep 1422917 = 266797) B266797
theorem B374387 : Blo 231814 374387 := bstep (se 1 (by rfl) ⟨280790, by rfl⟩ : syracuseStep 374387 = 561581) B561581
theorem B374465 : Blo 231814 374465 := bstep (se 2 (by rfl) ⟨140424, by rfl⟩ : syracuseStep 374465 = 280849) B280849
theorem B669485 : Blo 231814 669485 := bstep (se 3 (by rfl) ⟨125528, by rfl⟩ : syracuseStep 669485 = 251057) B251057
theorem B1193777 : Blo 231814 1193777 := bstep (se 2 (by rfl) ⟨447666, by rfl⟩ : syracuseStep 1193777 = 895333) B895333
theorem B1259405 : Blo 231814 1259405 := bstep (se 3 (by rfl) ⟨236138, by rfl⟩ : syracuseStep 1259405 = 472277) B472277
theorem B669667 : Blo 231814 669667 := bstep (se 1 (by rfl) ⟨502250, by rfl⟩ : syracuseStep 669667 = 1004501) B1004501
theorem B374849 : Blo 231814 374849 := bstep (se 2 (by rfl) ⟨140568, by rfl⟩ : syracuseStep 374849 = 281137) B281137
theorem B374977 : Blo 231814 374977 := bstep (se 2 (by rfl) ⟨140616, by rfl⟩ : syracuseStep 374977 = 281233) B281233
theorem B997667 : Blo 231814 997667 := bstep (se 1 (by rfl) ⟨748250, by rfl⟩ : syracuseStep 997667 = 1496501) B1496501
theorem B670157 : Blo 231814 670157 := bstep (se 3 (by rfl) ⟨125654, by rfl⟩ : syracuseStep 670157 = 251309) B251309
theorem B440977 : Blo 231814 440977 := bstep (se 2 (by rfl) ⟨165366, by rfl⟩ : syracuseStep 440977 = 330733) B330733
theorem B441379 : Blo 231814 441379 := bstep (se 1 (by rfl) ⟨331034, by rfl⟩ : syracuseStep 441379 = 662069) B662069
theorem B506915 : Blo 231814 506915 := bstep (se 1 (by rfl) ⟨380186, by rfl⟩ : syracuseStep 506915 = 760373) B760373
theorem B441425 : Blo 231814 441425 := bstep (se 2 (by rfl) ⟨165534, by rfl⟩ : syracuseStep 441425 = 331069) B331069
theorem B2997557 : Blo 231814 2997557 := bstep (se 5 (by rfl) ⟨140510, by rfl⟩ : syracuseStep 2997557 = 281021) B281021
theorem B441713 : Blo 231814 441713 := bstep (se 2 (by rfl) ⟨165642, by rfl⟩ : syracuseStep 441713 = 331285) B331285
theorem B703907 : Blo 231814 703907 := bstep (se 1 (by rfl) ⟨527930, by rfl⟩ : syracuseStep 703907 = 1055861) B1055861
theorem B671341 : Blo 231814 671341 := bstep (se 3 (by rfl) ⟨125876, by rfl⟩ : syracuseStep 671341 = 251753) B251753
theorem B1425059 : Blo 231814 1425059 := bstep (se 1 (by rfl) ⟨1068794, by rfl⟩ : syracuseStep 1425059 = 2137589) B2137589
theorem B376483 : Blo 231814 376483 := bstep (se 1 (by rfl) ⟨282362, by rfl⟩ : syracuseStep 376483 = 564725) B564725
theorem B802541 : Blo 231814 802541 := bstep (se 3 (by rfl) ⟨150476, by rfl⟩ : syracuseStep 802541 = 300953) B300953
theorem B2015117 : Blo 231814 2015117 := bstep (se 3 (by rfl) ⟨377834, by rfl⟩ : syracuseStep 2015117 = 755669) B755669
theorem B835555 : Blo 231814 835555 := bstep (se 1 (by rfl) ⟨626666, by rfl⟩ : syracuseStep 835555 = 1253333) B1253333
theorem B3293237 : Blo 231814 3293237 := bstep (se 5 (by rfl) ⟨154370, by rfl⟩ : syracuseStep 3293237 = 308741) B308741
theorem B442435 : Blo 231814 442435 := bstep (se 1 (by rfl) ⟨331826, by rfl⟩ : syracuseStep 442435 = 663653) B663653
theorem B1359949 : Blo 231814 1359949 := bstep (se 3 (by rfl) ⟨254990, by rfl⟩ : syracuseStep 1359949 = 509981) B509981
theorem B606289 : Blo 231814 606289 := bstep (se 2 (by rfl) ⟨227358, by rfl⟩ : syracuseStep 606289 = 454717) B454717
theorem B999665 : Blo 231814 999665 := bstep (se 2 (by rfl) ⟨374874, by rfl⟩ : syracuseStep 999665 = 749749) B749749
theorem B1327373 : Blo 231814 1327373 := bstep (se 3 (by rfl) ⟨248882, by rfl⟩ : syracuseStep 1327373 = 497765) B497765
theorem B377155 : Blo 231814 377155 := bstep (se 1 (by rfl) ⟨282866, by rfl⟩ : syracuseStep 377155 = 565733) B565733
theorem B1982789 : Blo 231814 1982789 := bstep (se 4 (by rfl) ⟨185886, by rfl⟩ : syracuseStep 1982789 = 371773) B371773
theorem B803267 : Blo 231814 803267 := bstep (se 1 (by rfl) ⟨602450, by rfl⟩ : syracuseStep 803267 = 1204901) B1204901
theorem B508369 : Blo 231814 508369 := bstep (se 2 (by rfl) ⟨190638, by rfl⟩ : syracuseStep 508369 = 381277) B381277
theorem B672259 : Blo 231814 672259 := bstep (se 1 (by rfl) ⟨504194, by rfl⟩ : syracuseStep 672259 = 1008389) B1008389
theorem B442883 : Blo 231814 442883 := bstep (se 1 (by rfl) ⟨332162, by rfl⟩ : syracuseStep 442883 = 664325) B664325
theorem B377617 : Blo 231814 377617 := bstep (se 2 (by rfl) ⟨141606, by rfl⟩ : syracuseStep 377617 = 283213) B283213
theorem B443171 : Blo 231814 443171 := bstep (se 1 (by rfl) ⟨332378, by rfl⟩ : syracuseStep 443171 = 664757) B664757
theorem B377713 : Blo 231814 377713 := bstep (se 2 (by rfl) ⟨141642, by rfl⟩ : syracuseStep 377713 = 283285) B283285
theorem B3195875 : Blo 231814 3195875 := bstep (se 1 (by rfl) ⟨2396906, by rfl⟩ : syracuseStep 3195875 = 4793813) B4793813
theorem B1360867 : Blo 231814 1360867 := bstep (se 1 (by rfl) ⟨1020650, by rfl⟩ : syracuseStep 1360867 = 2041301) B2041301
theorem B1983473 : Blo 231814 1983473 := bstep (se 2 (by rfl) ⟨743802, by rfl⟩ : syracuseStep 1983473 = 1487605) B1487605
theorem B1787021 : Blo 231814 1787021 := bstep (se 3 (by rfl) ⟨335066, by rfl⟩ : syracuseStep 1787021 = 670133) B670133
theorem B4015331 : Blo 231814 4015331 := bstep (se 1 (by rfl) ⟨3011498, by rfl⟩ : syracuseStep 4015331 = 6022997) B6022997
theorem B279811 : Blo 231814 279811 := bstep (se 1 (by rfl) ⟨209858, by rfl⟩ : syracuseStep 279811 = 419717) B419717
theorem B607651 : Blo 231814 607651 := bstep (se 1 (by rfl) ⟨455738, by rfl⟩ : syracuseStep 607651 = 911477) B911477
theorem B280003 : Blo 231814 280003 := bstep (se 1 (by rfl) ⟨210002, by rfl⟩ : syracuseStep 280003 = 420005) B420005
theorem B280147 : Blo 231814 280147 := bstep (se 1 (by rfl) ⟨210110, by rfl⟩ : syracuseStep 280147 = 420221) B420221
theorem B444113 : Blo 231814 444113 := bstep (se 2 (by rfl) ⟨166542, by rfl⟩ : syracuseStep 444113 = 333085) B333085
theorem B870385 : Blo 231814 870385 := bstep (se 2 (by rfl) ⟨326394, by rfl⟩ : syracuseStep 870385 = 652789) B652789
theorem B3197069 : Blo 231814 3197069 := bstep (se 3 (by rfl) ⟨599450, by rfl⟩ : syracuseStep 3197069 = 1198901) B1198901
theorem B1427633 : Blo 231814 1427633 := bstep (se 2 (by rfl) ⟨535362, by rfl⟩ : syracuseStep 1427633 = 1070725) B1070725
theorem B248131 : Blo 231814 248131 := bstep (se 1 (by rfl) ⟨186098, by rfl⟩ : syracuseStep 248131 = 372197) B372197
theorem B1329605 : Blo 231814 1329605 := bstep (se 4 (by rfl) ⟨124650, by rfl⟩ : syracuseStep 1329605 = 249301) B249301
theorem B445009 : Blo 231814 445009 := bstep (se 2 (by rfl) ⟨166878, by rfl⟩ : syracuseStep 445009 = 333757) B333757
theorem B477809 : Blo 231814 477809 := bstep (se 2 (by rfl) ⟨179178, by rfl⟩ : syracuseStep 477809 = 358357) B358357
theorem B1002125 : Blo 231814 1002125 := bstep (se 3 (by rfl) ⟨187898, by rfl⟩ : syracuseStep 1002125 = 375797) B375797
theorem B445169 : Blo 231814 445169 := bstep (se 2 (by rfl) ⟨166938, by rfl⟩ : syracuseStep 445169 = 333877) B333877
theorem B314371 : Blo 231814 314371 := bstep (se 1 (by rfl) ⟨235778, by rfl⟩ : syracuseStep 314371 = 471557) B471557
theorem B838669 : Blo 231814 838669 := bstep (se 3 (by rfl) ⟨157250, by rfl⟩ : syracuseStep 838669 = 314501) B314501
theorem B1330289 : Blo 231814 1330289 := bstep (se 2 (by rfl) ⟨498858, by rfl⟩ : syracuseStep 1330289 = 997717) B997717
theorem B445571 : Blo 231814 445571 := bstep (se 1 (by rfl) ⟨334178, by rfl⟩ : syracuseStep 445571 = 668357) B668357
theorem B1068173 : Blo 231814 1068173 := bstep (se 3 (by rfl) ⟨200282, by rfl⟩ : syracuseStep 1068173 = 400565) B400565
theorem B347729 : Blo 231814 347729 := bstep (se 2 (by rfl) ⟨130398, by rfl⟩ : syracuseStep 347729 = 260797) B260797
theorem B347747 : Blo 231814 347747 := bstep (se 1 (by rfl) ⟨260810, by rfl⟩ : syracuseStep 347747 = 521621) B521621
theorem B4247153 : Blo 231814 4247153 := bstep (se 2 (by rfl) ⟨1592682, by rfl⟩ : syracuseStep 4247153 = 3185365) B3185365
theorem B347777 : Blo 231814 347777 := bstep (se 2 (by rfl) ⟨130416, by rfl⟩ : syracuseStep 347777 = 260833) B260833
theorem B347795 : Blo 231814 347795 := bstep (se 1 (by rfl) ⟨260846, by rfl⟩ : syracuseStep 347795 = 521693) B521693
theorem B347825 : Blo 231814 347825 := bstep (se 2 (by rfl) ⟨130434, by rfl⟩ : syracuseStep 347825 = 260869) B260869
theorem B249523 : Blo 231814 249523 := bstep (se 1 (by rfl) ⟨187142, by rfl⟩ : syracuseStep 249523 = 374285) B374285
theorem B347843 : Blo 231814 347843 := bstep (se 1 (by rfl) ⟨260882, by rfl⟩ : syracuseStep 347843 = 521765) B521765
theorem B347873 : Blo 231814 347873 := bstep (se 2 (by rfl) ⟨130452, by rfl⟩ : syracuseStep 347873 = 260905) B260905
theorem B347891 : Blo 231814 347891 := bstep (se 1 (by rfl) ⟨260918, by rfl⟩ : syracuseStep 347891 = 521837) B521837
theorem B347921 : Blo 231814 347921 := bstep (se 2 (by rfl) ⟨130470, by rfl⟩ : syracuseStep 347921 = 260941) B260941
theorem B347939 : Blo 231814 347939 := bstep (se 1 (by rfl) ⟨260954, by rfl⟩ : syracuseStep 347939 = 521909) B521909
theorem B347969 : Blo 231814 347969 := bstep (se 2 (by rfl) ⟨130488, by rfl⟩ : syracuseStep 347969 = 260977) B260977
theorem B347987 : Blo 231814 347987 := bstep (se 1 (by rfl) ⟨260990, by rfl⟩ : syracuseStep 347987 = 521981) B521981
theorem B348017 : Blo 231814 348017 := bstep (se 2 (by rfl) ⟨130506, by rfl⟩ : syracuseStep 348017 = 261013) B261013
theorem B348035 : Blo 231814 348035 := bstep (se 1 (by rfl) ⟨261026, by rfl⟩ : syracuseStep 348035 = 522053) B522053
theorem B348065 : Blo 231814 348065 := bstep (se 2 (by rfl) ⟨130524, by rfl⟩ : syracuseStep 348065 = 261049) B261049
theorem B348083 : Blo 231814 348083 := bstep (se 1 (by rfl) ⟨261062, by rfl⟩ : syracuseStep 348083 = 522125) B522125
theorem B348113 : Blo 231814 348113 := bstep (se 2 (by rfl) ⟨130542, by rfl⟩ : syracuseStep 348113 = 261085) B261085
theorem B348131 : Blo 231814 348131 := bstep (se 1 (by rfl) ⟨261098, by rfl⟩ : syracuseStep 348131 = 522197) B522197
theorem B1789937 : Blo 231814 1789937 := bstep (se 2 (by rfl) ⟨671226, by rfl⟩ : syracuseStep 1789937 = 1342453) B1342453
theorem B348161 : Blo 231814 348161 := bstep (se 2 (by rfl) ⟨130560, by rfl⟩ : syracuseStep 348161 = 261121) B261121
theorem B446467 : Blo 231814 446467 := bstep (se 1 (by rfl) ⟨334850, by rfl⟩ : syracuseStep 446467 = 669701) B669701
theorem B348179 : Blo 231814 348179 := bstep (se 1 (by rfl) ⟨261134, by rfl⟩ : syracuseStep 348179 = 522269) B522269
theorem B348209 : Blo 231814 348209 := bstep (se 2 (by rfl) ⟨130578, by rfl⟩ : syracuseStep 348209 = 261157) B261157
theorem B348227 : Blo 231814 348227 := bstep (se 1 (by rfl) ⟨261170, by rfl⟩ : syracuseStep 348227 = 522341) B522341
theorem B348257 : Blo 231814 348257 := bstep (se 2 (by rfl) ⟨130596, by rfl⟩ : syracuseStep 348257 = 261193) B261193
theorem B348275 : Blo 231814 348275 := bstep (se 1 (by rfl) ⟨261206, by rfl⟩ : syracuseStep 348275 = 522413) B522413
theorem B348305 : Blo 231814 348305 := bstep (se 2 (by rfl) ⟨130614, by rfl⟩ : syracuseStep 348305 = 261229) B261229
theorem B446627 : Blo 231814 446627 := bstep (se 1 (by rfl) ⟨334970, by rfl⟩ : syracuseStep 446627 = 669941) B669941
theorem B348323 : Blo 231814 348323 := bstep (se 1 (by rfl) ⟨261242, by rfl⟩ : syracuseStep 348323 = 522485) B522485
theorem B1003697 : Blo 231814 1003697 := bstep (se 2 (by rfl) ⟨376386, by rfl⟩ : syracuseStep 1003697 = 752773) B752773
theorem B348353 : Blo 231814 348353 := bstep (se 2 (by rfl) ⟨130632, by rfl⟩ : syracuseStep 348353 = 261265) B261265
theorem B315587 : Blo 231814 315587 := bstep (se 1 (by rfl) ⟨236690, by rfl⟩ : syracuseStep 315587 = 473381) B473381
theorem B348371 : Blo 231814 348371 := bstep (se 1 (by rfl) ⟨261278, by rfl⟩ : syracuseStep 348371 = 522557) B522557
theorem B348401 : Blo 231814 348401 := bstep (se 2 (by rfl) ⟨130650, by rfl⟩ : syracuseStep 348401 = 261301) B261301
theorem B348419 : Blo 231814 348419 := bstep (se 1 (by rfl) ⟨261314, by rfl⟩ : syracuseStep 348419 = 522629) B522629
theorem B348449 : Blo 231814 348449 := bstep (se 2 (by rfl) ⟨130668, by rfl⟩ : syracuseStep 348449 = 261337) B261337
theorem B348467 : Blo 231814 348467 := bstep (se 1 (by rfl) ⟨261350, by rfl⟩ : syracuseStep 348467 = 522701) B522701
theorem B1528141 : Blo 231814 1528141 := bstep (se 3 (by rfl) ⟨286526, by rfl⟩ : syracuseStep 1528141 = 573053) B573053
theorem B348497 : Blo 231814 348497 := bstep (se 2 (by rfl) ⟨130686, by rfl⟩ : syracuseStep 348497 = 261373) B261373
theorem B348515 : Blo 231814 348515 := bstep (se 1 (by rfl) ⟨261386, by rfl⟩ : syracuseStep 348515 = 522773) B522773
theorem B348545 : Blo 231814 348545 := bstep (se 2 (by rfl) ⟨130704, by rfl⟩ : syracuseStep 348545 = 261409) B261409
theorem B348563 : Blo 231814 348563 := bstep (se 1 (by rfl) ⟨261422, by rfl⟩ : syracuseStep 348563 = 522845) B522845
theorem B348593 : Blo 231814 348593 := bstep (se 2 (by rfl) ⟨130722, by rfl⟩ : syracuseStep 348593 = 261445) B261445
theorem B348611 : Blo 231814 348611 := bstep (se 1 (by rfl) ⟨261458, by rfl⟩ : syracuseStep 348611 = 522917) B522917
theorem B348641 : Blo 231814 348641 := bstep (se 2 (by rfl) ⟨130740, by rfl⟩ : syracuseStep 348641 = 261481) B261481
theorem B348659 : Blo 231814 348659 := bstep (se 1 (by rfl) ⟨261494, by rfl⟩ : syracuseStep 348659 = 522989) B522989
theorem B348689 : Blo 231814 348689 := bstep (se 2 (by rfl) ⟨130758, by rfl⟩ : syracuseStep 348689 = 261517) B261517
theorem B348707 : Blo 231814 348707 := bstep (se 1 (by rfl) ⟨261530, by rfl⟩ : syracuseStep 348707 = 523061) B523061
theorem B1331747 : Blo 231814 1331747 := bstep (se 1 (by rfl) ⟨998810, by rfl⟩ : syracuseStep 1331747 = 1997621) B1997621
theorem B1430065 : Blo 231814 1430065 := bstep (se 2 (by rfl) ⟨536274, by rfl⟩ : syracuseStep 1430065 = 1072549) B1072549
theorem B348737 : Blo 231814 348737 := bstep (se 2 (by rfl) ⟨130776, by rfl⟩ : syracuseStep 348737 = 261553) B261553
theorem B348755 : Blo 231814 348755 := bstep (se 1 (by rfl) ⟨261566, by rfl⟩ : syracuseStep 348755 = 523133) B523133
theorem B348785 : Blo 231814 348785 := bstep (se 2 (by rfl) ⟨130794, by rfl⟩ : syracuseStep 348785 = 261589) B261589
theorem B3002993 : Blo 231814 3002993 := bstep (se 2 (by rfl) ⟨1126122, by rfl⟩ : syracuseStep 3002993 = 2252245) B2252245
theorem B348803 : Blo 231814 348803 := bstep (se 1 (by rfl) ⟨261602, by rfl⟩ : syracuseStep 348803 = 523205) B523205
theorem B348833 : Blo 231814 348833 := bstep (se 2 (by rfl) ⟨130812, by rfl⟩ : syracuseStep 348833 = 261625) B261625
theorem B348851 : Blo 231814 348851 := bstep (se 1 (by rfl) ⟨261638, by rfl⟩ : syracuseStep 348851 = 523277) B523277
theorem B348881 : Blo 231814 348881 := bstep (se 2 (by rfl) ⟨130830, by rfl⟩ : syracuseStep 348881 = 261661) B261661
theorem B348899 : Blo 231814 348899 := bstep (se 1 (by rfl) ⟨261674, by rfl⟩ : syracuseStep 348899 = 523349) B523349
theorem B348929 : Blo 231814 348929 := bstep (se 2 (by rfl) ⟨130848, by rfl⟩ : syracuseStep 348929 = 261697) B261697
theorem B348947 : Blo 231814 348947 := bstep (se 1 (by rfl) ⟨261710, by rfl⟩ : syracuseStep 348947 = 523421) B523421
theorem B348977 : Blo 231814 348977 := bstep (se 2 (by rfl) ⟨130866, by rfl⟩ : syracuseStep 348977 = 261733) B261733
theorem B348995 : Blo 231814 348995 := bstep (se 1 (by rfl) ⟨261746, by rfl⟩ : syracuseStep 348995 = 523493) B523493
theorem B349025 : Blo 231814 349025 := bstep (se 2 (by rfl) ⟨130884, by rfl⟩ : syracuseStep 349025 = 261769) B261769
theorem B349043 : Blo 231814 349043 := bstep (se 1 (by rfl) ⟨261782, by rfl⟩ : syracuseStep 349043 = 523565) B523565
theorem B349073 : Blo 231814 349073 := bstep (se 2 (by rfl) ⟨130902, by rfl⟩ : syracuseStep 349073 = 261805) B261805
theorem B349091 : Blo 231814 349091 := bstep (se 1 (by rfl) ⟨261818, by rfl⟩ : syracuseStep 349091 = 523637) B523637
theorem B349121 : Blo 231814 349121 := bstep (se 2 (by rfl) ⟨130920, by rfl⟩ : syracuseStep 349121 = 261841) B261841
theorem B349139 : Blo 231814 349139 := bstep (se 1 (by rfl) ⟨261854, by rfl⟩ : syracuseStep 349139 = 523709) B523709
theorem B349169 : Blo 231814 349169 := bstep (se 2 (by rfl) ⟨130938, by rfl⟩ : syracuseStep 349169 = 261877) B261877
theorem B349187 : Blo 231814 349187 := bstep (se 1 (by rfl) ⟨261890, by rfl⟩ : syracuseStep 349187 = 523781) B523781
theorem B349217 : Blo 231814 349217 := bstep (se 2 (by rfl) ⟨130956, by rfl⟩ : syracuseStep 349217 = 261913) B261913
theorem B349235 : Blo 231814 349235 := bstep (se 1 (by rfl) ⟨261926, by rfl⟩ : syracuseStep 349235 = 523853) B523853
theorem B808013 : Blo 231814 808013 := bstep (se 3 (by rfl) ⟨151502, by rfl⟩ : syracuseStep 808013 = 303005) B303005
theorem B349265 : Blo 231814 349265 := bstep (se 2 (by rfl) ⟨130974, by rfl⟩ : syracuseStep 349265 = 261949) B261949
theorem B349283 : Blo 231814 349283 := bstep (se 1 (by rfl) ⟨261962, by rfl⟩ : syracuseStep 349283 = 523925) B523925
theorem B349313 : Blo 231814 349313 := bstep (se 2 (by rfl) ⟨130992, by rfl⟩ : syracuseStep 349313 = 261985) B261985
theorem B349331 : Blo 231814 349331 := bstep (se 1 (by rfl) ⟨261998, by rfl⟩ : syracuseStep 349331 = 523997) B523997
theorem B349361 : Blo 231814 349361 := bstep (se 2 (by rfl) ⟨131010, by rfl⟩ : syracuseStep 349361 = 262021) B262021
theorem B349379 : Blo 231814 349379 := bstep (se 1 (by rfl) ⟨262034, by rfl⟩ : syracuseStep 349379 = 524069) B524069
theorem B349409 : Blo 231814 349409 := bstep (se 2 (by rfl) ⟨131028, by rfl⟩ : syracuseStep 349409 = 262057) B262057
theorem B349427 : Blo 231814 349427 := bstep (se 1 (by rfl) ⟨262070, by rfl⟩ : syracuseStep 349427 = 524141) B524141
theorem B349457 : Blo 231814 349457 := bstep (se 2 (by rfl) ⟨131046, by rfl⟩ : syracuseStep 349457 = 262093) B262093
theorem B349475 : Blo 231814 349475 := bstep (se 1 (by rfl) ⟨262106, by rfl⟩ : syracuseStep 349475 = 524213) B524213
theorem B349505 : Blo 231814 349505 := bstep (se 2 (by rfl) ⟨131064, by rfl⟩ : syracuseStep 349505 = 262129) B262129
theorem B349523 : Blo 231814 349523 := bstep (se 1 (by rfl) ⟨262142, by rfl⟩ : syracuseStep 349523 = 524285) B524285
theorem B349553 : Blo 231814 349553 := bstep (se 2 (by rfl) ⟨131082, by rfl⟩ : syracuseStep 349553 = 262165) B262165
theorem B349571 : Blo 231814 349571 := bstep (se 1 (by rfl) ⟨262178, by rfl⟩ : syracuseStep 349571 = 524357) B524357
theorem B349601 : Blo 231814 349601 := bstep (se 2 (by rfl) ⟨131100, by rfl⟩ : syracuseStep 349601 = 262201) B262201
theorem B349619 : Blo 231814 349619 := bstep (se 1 (by rfl) ⟨262214, by rfl⟩ : syracuseStep 349619 = 524429) B524429
theorem B349649 : Blo 231814 349649 := bstep (se 2 (by rfl) ⟨131118, by rfl⟩ : syracuseStep 349649 = 262237) B262237
theorem B349667 : Blo 231814 349667 := bstep (se 1 (by rfl) ⟨262250, by rfl⟩ : syracuseStep 349667 = 524501) B524501
theorem B349697 : Blo 231814 349697 := bstep (se 2 (by rfl) ⟨131136, by rfl⟩ : syracuseStep 349697 = 262273) B262273
theorem B349715 : Blo 231814 349715 := bstep (se 1 (by rfl) ⟨262286, by rfl⟩ : syracuseStep 349715 = 524573) B524573
theorem B349745 : Blo 231814 349745 := bstep (se 2 (by rfl) ⟨131154, by rfl⟩ : syracuseStep 349745 = 262309) B262309
theorem B349763 : Blo 231814 349763 := bstep (se 1 (by rfl) ⟨262322, by rfl⟩ : syracuseStep 349763 = 524645) B524645
theorem B349793 : Blo 231814 349793 := bstep (se 2 (by rfl) ⟨131172, by rfl⟩ : syracuseStep 349793 = 262345) B262345
theorem B349811 : Blo 231814 349811 := bstep (se 1 (by rfl) ⟨262358, by rfl⟩ : syracuseStep 349811 = 524717) B524717
theorem B349841 : Blo 231814 349841 := bstep (se 2 (by rfl) ⟨131190, by rfl⟩ : syracuseStep 349841 = 262381) B262381
theorem B349859 : Blo 231814 349859 := bstep (se 1 (by rfl) ⟨262394, by rfl⟩ : syracuseStep 349859 = 524789) B524789
theorem B1267363 : Blo 231814 1267363 := bstep (se 1 (by rfl) ⟨950522, by rfl⟩ : syracuseStep 1267363 = 1901045) B1901045
theorem B349889 : Blo 231814 349889 := bstep (se 2 (by rfl) ⟨131208, by rfl⟩ : syracuseStep 349889 = 262417) B262417
theorem B349907 : Blo 231814 349907 := bstep (se 1 (by rfl) ⟨262430, by rfl⟩ : syracuseStep 349907 = 524861) B524861
theorem B2119409 : Blo 231814 2119409 := bstep (se 2 (by rfl) ⟨794778, by rfl⟩ : syracuseStep 2119409 = 1589557) B1589557
theorem B349937 : Blo 231814 349937 := bstep (se 2 (by rfl) ⟨131226, by rfl⟩ : syracuseStep 349937 = 262453) B262453
theorem B349955 : Blo 231814 349955 := bstep (se 1 (by rfl) ⟨262466, by rfl⟩ : syracuseStep 349955 = 524933) B524933
theorem B349985 : Blo 231814 349985 := bstep (se 2 (by rfl) ⟨131244, by rfl⟩ : syracuseStep 349985 = 262489) B262489
theorem B907057 : Blo 231814 907057 := bstep (se 2 (by rfl) ⟨340146, by rfl⟩ : syracuseStep 907057 = 680293) B680293
theorem B350003 : Blo 231814 350003 := bstep (se 1 (by rfl) ⟨262502, by rfl⟩ : syracuseStep 350003 = 525005) B525005
theorem B350033 : Blo 231814 350033 := bstep (se 2 (by rfl) ⟨131262, by rfl⟩ : syracuseStep 350033 = 262525) B262525
theorem B350051 : Blo 231814 350051 := bstep (se 1 (by rfl) ⟨262538, by rfl⟩ : syracuseStep 350051 = 525077) B525077
theorem B350081 : Blo 231814 350081 := bstep (se 2 (by rfl) ⟨131280, by rfl⟩ : syracuseStep 350081 = 262561) B262561
theorem B776081 : Blo 231814 776081 := bstep (se 2 (by rfl) ⟨291030, by rfl⟩ : syracuseStep 776081 = 582061) B582061
theorem B251795 : Blo 231814 251795 := bstep (se 1 (by rfl) ⟨188846, by rfl⟩ : syracuseStep 251795 = 377693) B377693
theorem B350099 : Blo 231814 350099 := bstep (se 1 (by rfl) ⟨262574, by rfl⟩ : syracuseStep 350099 = 525149) B525149
theorem B350129 : Blo 231814 350129 := bstep (se 2 (by rfl) ⟨131298, by rfl⟩ : syracuseStep 350129 = 262597) B262597
theorem B350147 : Blo 231814 350147 := bstep (se 1 (by rfl) ⟨262610, by rfl⟩ : syracuseStep 350147 = 525221) B525221
theorem B350177 : Blo 231814 350177 := bstep (se 2 (by rfl) ⟨131316, by rfl⟩ : syracuseStep 350177 = 262633) B262633
theorem B350195 : Blo 231814 350195 := bstep (se 1 (by rfl) ⟨262646, by rfl⟩ : syracuseStep 350195 = 525293) B525293
theorem B350225 : Blo 231814 350225 := bstep (se 2 (by rfl) ⟨131334, by rfl⟩ : syracuseStep 350225 = 262669) B262669
theorem B350243 : Blo 231814 350243 := bstep (se 1 (by rfl) ⟨262682, by rfl⟩ : syracuseStep 350243 = 525365) B525365
theorem B350273 : Blo 231814 350273 := bstep (se 2 (by rfl) ⟨131352, by rfl⟩ : syracuseStep 350273 = 262705) B262705
theorem B350291 : Blo 231814 350291 := bstep (se 1 (by rfl) ⟨262718, by rfl⟩ : syracuseStep 350291 = 525437) B525437
theorem B350321 : Blo 231814 350321 := bstep (se 2 (by rfl) ⟨131370, by rfl⟩ : syracuseStep 350321 = 262741) B262741
theorem B350339 : Blo 231814 350339 := bstep (se 1 (by rfl) ⟨262754, by rfl⟩ : syracuseStep 350339 = 525509) B525509
theorem B481411 : Blo 231814 481411 := bstep (se 1 (by rfl) ⟨361058, by rfl⟩ : syracuseStep 481411 = 722117) B722117
theorem B350369 : Blo 231814 350369 := bstep (se 2 (by rfl) ⟨131388, by rfl⟩ : syracuseStep 350369 = 262777) B262777
theorem B350387 : Blo 231814 350387 := bstep (se 1 (by rfl) ⟨262790, by rfl⟩ : syracuseStep 350387 = 525581) B525581
theorem B350417 : Blo 231814 350417 := bstep (se 2 (by rfl) ⟨131406, by rfl⟩ : syracuseStep 350417 = 262813) B262813
theorem B350435 : Blo 231814 350435 := bstep (se 1 (by rfl) ⟨262826, by rfl⟩ : syracuseStep 350435 = 525653) B525653
theorem B284915 : Blo 231814 284915 := bstep (se 1 (by rfl) ⟨213686, by rfl⟩ : syracuseStep 284915 = 427373) B427373
theorem B350465 : Blo 231814 350465 := bstep (se 2 (by rfl) ⟨131424, by rfl⟩ : syracuseStep 350465 = 262849) B262849
theorem B1267973 : Blo 231814 1267973 := bstep (se 4 (by rfl) ⟨118872, by rfl⟩ : syracuseStep 1267973 = 237745) B237745
theorem B350483 : Blo 231814 350483 := bstep (se 1 (by rfl) ⟨262862, by rfl⟩ : syracuseStep 350483 = 525725) B525725
theorem B350513 : Blo 231814 350513 := bstep (se 2 (by rfl) ⟨131442, by rfl⟩ : syracuseStep 350513 = 262885) B262885
theorem B350531 : Blo 231814 350531 := bstep (se 1 (by rfl) ⟨262898, by rfl⟩ : syracuseStep 350531 = 525797) B525797
theorem B350561 : Blo 231814 350561 := bstep (se 2 (by rfl) ⟨131460, by rfl⟩ : syracuseStep 350561 = 262921) B262921
theorem B350579 : Blo 231814 350579 := bstep (se 1 (by rfl) ⟨262934, by rfl⟩ : syracuseStep 350579 = 525869) B525869
theorem B350609 : Blo 231814 350609 := bstep (se 2 (by rfl) ⟨131478, by rfl⟩ : syracuseStep 350609 = 262957) B262957
theorem B743843 : Blo 231814 743843 := bstep (se 1 (by rfl) ⟨557882, by rfl⟩ : syracuseStep 743843 = 1115765) B1115765
theorem B350627 : Blo 231814 350627 := bstep (se 1 (by rfl) ⟨262970, by rfl⟩ : syracuseStep 350627 = 525941) B525941
theorem B350657 : Blo 231814 350657 := bstep (se 2 (by rfl) ⟨131496, by rfl⟩ : syracuseStep 350657 = 262993) B262993
theorem B350675 : Blo 231814 350675 := bstep (se 1 (by rfl) ⟨263006, by rfl⟩ : syracuseStep 350675 = 526013) B526013
theorem B350705 : Blo 231814 350705 := bstep (se 2 (by rfl) ⟨131514, by rfl⟩ : syracuseStep 350705 = 263029) B263029
theorem B350723 : Blo 231814 350723 := bstep (se 1 (by rfl) ⟨263042, by rfl⟩ : syracuseStep 350723 = 526085) B526085
theorem B350753 : Blo 231814 350753 := bstep (se 2 (by rfl) ⟨131532, by rfl⟩ : syracuseStep 350753 = 263065) B263065
theorem B1268273 : Blo 231814 1268273 := bstep (se 2 (by rfl) ⟨475602, by rfl⟩ : syracuseStep 1268273 = 951205) B951205
theorem B350771 : Blo 231814 350771 := bstep (se 1 (by rfl) ⟨263078, by rfl⟩ : syracuseStep 350771 = 526157) B526157
theorem B1006157 : Blo 231814 1006157 := bstep (se 3 (by rfl) ⟨188654, by rfl⟩ : syracuseStep 1006157 = 377309) B377309
theorem B350801 : Blo 231814 350801 := bstep (se 2 (by rfl) ⟨131550, by rfl⟩ : syracuseStep 350801 = 263101) B263101
theorem B350819 : Blo 231814 350819 := bstep (se 1 (by rfl) ⟨263114, by rfl⟩ : syracuseStep 350819 = 526229) B526229
theorem B350849 : Blo 231814 350849 := bstep (se 2 (by rfl) ⟨131568, by rfl⟩ : syracuseStep 350849 = 263137) B263137
theorem B350867 : Blo 231814 350867 := bstep (se 1 (by rfl) ⟨263150, by rfl⟩ : syracuseStep 350867 = 526301) B526301
theorem B350897 : Blo 231814 350897 := bstep (se 2 (by rfl) ⟨131586, by rfl⟩ : syracuseStep 350897 = 263173) B263173
theorem B1268401 : Blo 231814 1268401 := bstep (se 2 (by rfl) ⟨475650, by rfl⟩ : syracuseStep 1268401 = 951301) B951301
theorem B350915 : Blo 231814 350915 := bstep (se 1 (by rfl) ⟨263186, by rfl⟩ : syracuseStep 350915 = 526373) B526373
theorem B350945 : Blo 231814 350945 := bstep (se 2 (by rfl) ⟨131604, by rfl⟩ : syracuseStep 350945 = 263209) B263209
theorem B350963 : Blo 231814 350963 := bstep (se 1 (by rfl) ⟨263222, by rfl⟩ : syracuseStep 350963 = 526445) B526445
theorem B350993 : Blo 231814 350993 := bstep (se 2 (by rfl) ⟨131622, by rfl⟩ : syracuseStep 350993 = 263245) B263245
theorem B351011 : Blo 231814 351011 := bstep (se 1 (by rfl) ⟨263258, by rfl⟩ : syracuseStep 351011 = 526517) B526517
theorem B351041 : Blo 231814 351041 := bstep (se 2 (by rfl) ⟨131640, by rfl⟩ : syracuseStep 351041 = 263281) B263281
theorem B351059 : Blo 231814 351059 := bstep (se 1 (by rfl) ⟨263294, by rfl⟩ : syracuseStep 351059 = 526589) B526589
theorem B351089 : Blo 231814 351089 := bstep (se 2 (by rfl) ⟨131658, by rfl⟩ : syracuseStep 351089 = 263317) B263317
theorem B351107 : Blo 231814 351107 := bstep (se 1 (by rfl) ⟨263330, by rfl⟩ : syracuseStep 351107 = 526661) B526661
theorem B1268621 : Blo 231814 1268621 := bstep (se 3 (by rfl) ⟨237866, by rfl⟩ : syracuseStep 1268621 = 475733) B475733
theorem B351137 : Blo 231814 351137 := bstep (se 2 (by rfl) ⟨131676, by rfl⟩ : syracuseStep 351137 = 263353) B263353
theorem B1596323 : Blo 231814 1596323 := bstep (se 1 (by rfl) ⟨1197242, by rfl⟩ : syracuseStep 1596323 = 2394485) B2394485
theorem B1006499 : Blo 231814 1006499 := bstep (se 1 (by rfl) ⟨754874, by rfl⟩ : syracuseStep 1006499 = 1509749) B1509749
theorem B351155 : Blo 231814 351155 := bstep (se 1 (by rfl) ⟨263366, by rfl⟩ : syracuseStep 351155 = 526733) B526733
theorem B351185 : Blo 231814 351185 := bstep (se 2 (by rfl) ⟨131694, by rfl⟩ : syracuseStep 351185 = 263389) B263389
theorem B351203 : Blo 231814 351203 := bstep (se 1 (by rfl) ⟨263402, by rfl⟩ : syracuseStep 351203 = 526805) B526805
theorem B351233 : Blo 231814 351233 := bstep (se 2 (by rfl) ⟨131712, by rfl⟩ : syracuseStep 351233 = 263425) B263425
theorem B351251 : Blo 231814 351251 := bstep (se 1 (by rfl) ⟨263438, by rfl⟩ : syracuseStep 351251 = 526877) B526877
theorem B351281 : Blo 231814 351281 := bstep (se 2 (by rfl) ⟨131730, by rfl⟩ : syracuseStep 351281 = 263461) B263461
theorem B351299 : Blo 231814 351299 := bstep (se 1 (by rfl) ⟨263474, by rfl⟩ : syracuseStep 351299 = 526949) B526949
theorem B351329 : Blo 231814 351329 := bstep (se 2 (by rfl) ⟨131748, by rfl⟩ : syracuseStep 351329 = 263497) B263497
theorem B351347 : Blo 231814 351347 := bstep (se 1 (by rfl) ⟨263510, by rfl⟩ : syracuseStep 351347 = 527021) B527021
theorem B351377 : Blo 231814 351377 := bstep (se 2 (by rfl) ⟨131766, by rfl⟩ : syracuseStep 351377 = 263533) B263533
theorem B351395 : Blo 231814 351395 := bstep (se 1 (by rfl) ⟨263546, by rfl⟩ : syracuseStep 351395 = 527093) B527093
theorem B351425 : Blo 231814 351425 := bstep (se 2 (by rfl) ⟨131784, by rfl⟩ : syracuseStep 351425 = 263569) B263569
theorem B351443 : Blo 231814 351443 := bstep (se 1 (by rfl) ⟨263582, by rfl⟩ : syracuseStep 351443 = 527165) B527165
theorem B351473 : Blo 231814 351473 := bstep (se 2 (by rfl) ⟨131802, by rfl⟩ : syracuseStep 351473 = 263605) B263605
theorem B351491 : Blo 231814 351491 := bstep (se 1 (by rfl) ⟨263618, by rfl⟩ : syracuseStep 351491 = 527237) B527237
theorem B351521 : Blo 231814 351521 := bstep (se 2 (by rfl) ⟨131820, by rfl⟩ : syracuseStep 351521 = 263641) B263641
theorem B351539 : Blo 231814 351539 := bstep (se 1 (by rfl) ⟨263654, by rfl⟩ : syracuseStep 351539 = 527309) B527309
theorem B351569 : Blo 231814 351569 := bstep (se 2 (by rfl) ⟨131838, by rfl⟩ : syracuseStep 351569 = 263677) B263677
theorem B351587 : Blo 231814 351587 := bstep (se 1 (by rfl) ⟨263690, by rfl⟩ : syracuseStep 351587 = 527381) B527381
theorem B351617 : Blo 231814 351617 := bstep (se 2 (by rfl) ⟨131856, by rfl⟩ : syracuseStep 351617 = 263713) B263713
theorem B351635 : Blo 231814 351635 := bstep (se 1 (by rfl) ⟨263726, by rfl⟩ : syracuseStep 351635 = 527453) B527453
theorem B351665 : Blo 231814 351665 := bstep (se 2 (by rfl) ⟨131874, by rfl⟩ : syracuseStep 351665 = 263749) B263749
theorem B351683 : Blo 231814 351683 := bstep (se 1 (by rfl) ⟨263762, by rfl⟩ : syracuseStep 351683 = 527525) B527525
theorem B351713 : Blo 231814 351713 := bstep (se 2 (by rfl) ⟨131892, by rfl⟩ : syracuseStep 351713 = 263785) B263785
theorem B351731 : Blo 231814 351731 := bstep (se 1 (by rfl) ⟨263798, by rfl⟩ : syracuseStep 351731 = 527597) B527597
theorem B351761 : Blo 231814 351761 := bstep (se 2 (by rfl) ⟨131910, by rfl⟩ : syracuseStep 351761 = 263821) B263821
theorem B351779 : Blo 231814 351779 := bstep (se 1 (by rfl) ⟨263834, by rfl⟩ : syracuseStep 351779 = 527669) B527669
theorem B351809 : Blo 231814 351809 := bstep (se 2 (by rfl) ⟨131928, by rfl⟩ : syracuseStep 351809 = 263857) B263857
theorem B351827 : Blo 231814 351827 := bstep (se 1 (by rfl) ⟨263870, by rfl⟩ : syracuseStep 351827 = 527741) B527741
theorem B351857 : Blo 231814 351857 := bstep (se 2 (by rfl) ⟨131946, by rfl⟩ : syracuseStep 351857 = 263893) B263893
theorem B351875 : Blo 231814 351875 := bstep (se 1 (by rfl) ⟨263906, by rfl⟩ : syracuseStep 351875 = 527813) B527813
theorem B351905 : Blo 231814 351905 := bstep (se 2 (by rfl) ⟨131964, by rfl⟩ : syracuseStep 351905 = 263929) B263929
theorem B351923 : Blo 231814 351923 := bstep (se 1 (by rfl) ⟨263942, by rfl⟩ : syracuseStep 351923 = 527885) B527885
theorem B1334981 : Blo 231814 1334981 := bstep (se 4 (by rfl) ⟨125154, by rfl⟩ : syracuseStep 1334981 = 250309) B250309
theorem B351953 : Blo 231814 351953 := bstep (se 2 (by rfl) ⟨131982, by rfl⟩ : syracuseStep 351953 = 263965) B263965
theorem B351971 : Blo 231814 351971 := bstep (se 1 (by rfl) ⟨263978, by rfl⟩ : syracuseStep 351971 = 527957) B527957
theorem B352001 : Blo 231814 352001 := bstep (se 2 (by rfl) ⟨132000, by rfl⟩ : syracuseStep 352001 = 264001) B264001
theorem B352019 : Blo 231814 352019 := bstep (se 1 (by rfl) ⟨264014, by rfl⟩ : syracuseStep 352019 = 528029) B528029
theorem B352049 : Blo 231814 352049 := bstep (se 2 (by rfl) ⟨132018, by rfl⟩ : syracuseStep 352049 = 264037) B264037
theorem B352067 : Blo 231814 352067 := bstep (se 1 (by rfl) ⟨264050, by rfl⟩ : syracuseStep 352067 = 528101) B528101
theorem B352097 : Blo 231814 352097 := bstep (se 2 (by rfl) ⟨132036, by rfl⟩ : syracuseStep 352097 = 264073) B264073
theorem B352115 : Blo 231814 352115 := bstep (se 1 (by rfl) ⟨264086, by rfl⟩ : syracuseStep 352115 = 528173) B528173
theorem B352145 : Blo 231814 352145 := bstep (se 2 (by rfl) ⟨132054, by rfl⟩ : syracuseStep 352145 = 264109) B264109
theorem B352163 : Blo 231814 352163 := bstep (se 1 (by rfl) ⟨264122, by rfl⟩ : syracuseStep 352163 = 528245) B528245
theorem B352193 : Blo 231814 352193 := bstep (se 2 (by rfl) ⟨132072, by rfl⟩ : syracuseStep 352193 = 264145) B264145
theorem B352211 : Blo 231814 352211 := bstep (se 1 (by rfl) ⟨264158, by rfl⟩ : syracuseStep 352211 = 528317) B528317
theorem B352241 : Blo 231814 352241 := bstep (se 2 (by rfl) ⟨132090, by rfl⟩ : syracuseStep 352241 = 264181) B264181
theorem B352259 : Blo 231814 352259 := bstep (se 1 (by rfl) ⟨264194, by rfl⟩ : syracuseStep 352259 = 528389) B528389
theorem B352289 : Blo 231814 352289 := bstep (se 2 (by rfl) ⟨132108, by rfl⟩ : syracuseStep 352289 = 264217) B264217
theorem B417841 : Blo 231814 417841 := bstep (se 2 (by rfl) ⟨156690, by rfl⟩ : syracuseStep 417841 = 313381) B313381
theorem B352307 : Blo 231814 352307 := bstep (se 1 (by rfl) ⟨264230, by rfl⟩ : syracuseStep 352307 = 528461) B528461
theorem B352337 : Blo 231814 352337 := bstep (se 2 (by rfl) ⟨132126, by rfl⟩ : syracuseStep 352337 = 264253) B264253
theorem B352355 : Blo 231814 352355 := bstep (se 1 (by rfl) ⟨264266, by rfl⟩ : syracuseStep 352355 = 528533) B528533
theorem B352385 : Blo 231814 352385 := bstep (se 2 (by rfl) ⟨132144, by rfl⟩ : syracuseStep 352385 = 264289) B264289
theorem B1335437 : Blo 231814 1335437 := bstep (se 3 (by rfl) ⟨250394, by rfl⟩ : syracuseStep 1335437 = 500789) B500789
theorem B352403 : Blo 231814 352403 := bstep (se 1 (by rfl) ⟨264302, by rfl⟩ : syracuseStep 352403 = 528605) B528605
theorem B745649 : Blo 231814 745649 := bstep (se 2 (by rfl) ⟨279618, by rfl⟩ : syracuseStep 745649 = 559237) B559237
theorem B352433 : Blo 231814 352433 := bstep (se 2 (by rfl) ⟨132162, by rfl⟩ : syracuseStep 352433 = 264325) B264325
theorem B352451 : Blo 231814 352451 := bstep (se 1 (by rfl) ⟨264338, by rfl⟩ : syracuseStep 352451 = 528677) B528677
theorem B352481 : Blo 231814 352481 := bstep (se 2 (by rfl) ⟨132180, by rfl⟩ : syracuseStep 352481 = 264361) B264361
theorem B745699 : Blo 231814 745699 := bstep (se 1 (by rfl) ⟨559274, by rfl⟩ : syracuseStep 745699 = 1118549) B1118549
theorem B352499 : Blo 231814 352499 := bstep (se 1 (by rfl) ⟨264374, by rfl⟩ : syracuseStep 352499 = 528749) B528749
theorem B352529 : Blo 231814 352529 := bstep (se 2 (by rfl) ⟨132198, by rfl⟩ : syracuseStep 352529 = 264397) B264397
theorem B352547 : Blo 231814 352547 := bstep (se 1 (by rfl) ⟨264410, by rfl⟩ : syracuseStep 352547 = 528821) B528821
theorem B352577 : Blo 231814 352577 := bstep (se 2 (by rfl) ⟨132216, by rfl⟩ : syracuseStep 352577 = 264433) B264433
theorem B352595 : Blo 231814 352595 := bstep (se 1 (by rfl) ⟨264446, by rfl⟩ : syracuseStep 352595 = 528893) B528893
theorem B352625 : Blo 231814 352625 := bstep (se 2 (by rfl) ⟨132234, by rfl⟩ : syracuseStep 352625 = 264469) B264469
theorem B352643 : Blo 231814 352643 := bstep (se 1 (by rfl) ⟨264482, by rfl⟩ : syracuseStep 352643 = 528965) B528965
theorem B352673 : Blo 231814 352673 := bstep (se 2 (by rfl) ⟨132252, by rfl⟩ : syracuseStep 352673 = 264505) B264505
theorem B352691 : Blo 231814 352691 := bstep (se 1 (by rfl) ⟨264518, by rfl⟩ : syracuseStep 352691 = 529037) B529037
theorem B352721 : Blo 231814 352721 := bstep (se 2 (by rfl) ⟨132270, by rfl⟩ : syracuseStep 352721 = 264541) B264541
theorem B352739 : Blo 231814 352739 := bstep (se 1 (by rfl) ⟨264554, by rfl⟩ : syracuseStep 352739 = 529109) B529109
theorem B352769 : Blo 231814 352769 := bstep (se 2 (by rfl) ⟨132288, by rfl⟩ : syracuseStep 352769 = 264577) B264577
theorem B3006989 : Blo 231814 3006989 := bstep (se 3 (by rfl) ⟨563810, by rfl⟩ : syracuseStep 3006989 = 1127621) B1127621
theorem B352787 : Blo 231814 352787 := bstep (se 1 (by rfl) ⟨264590, by rfl⟩ : syracuseStep 352787 = 529181) B529181
theorem B352817 : Blo 231814 352817 := bstep (se 2 (by rfl) ⟨132306, by rfl⟩ : syracuseStep 352817 = 264613) B264613
theorem B352835 : Blo 231814 352835 := bstep (se 1 (by rfl) ⟨264626, by rfl⟩ : syracuseStep 352835 = 529253) B529253
theorem B680525 : Blo 231814 680525 := bstep (se 3 (by rfl) ⟨127598, by rfl⟩ : syracuseStep 680525 = 255197) B255197
theorem B352865 : Blo 231814 352865 := bstep (se 2 (by rfl) ⟨132324, by rfl⟩ : syracuseStep 352865 = 264649) B264649
theorem B352883 : Blo 231814 352883 := bstep (se 1 (by rfl) ⟨264662, by rfl⟩ : syracuseStep 352883 = 529325) B529325
theorem B352913 : Blo 231814 352913 := bstep (se 2 (by rfl) ⟨132342, by rfl⟩ : syracuseStep 352913 = 264685) B264685
theorem B352931 : Blo 231814 352931 := bstep (se 1 (by rfl) ⟨264698, by rfl⟩ : syracuseStep 352931 = 529397) B529397
theorem B352961 : Blo 231814 352961 := bstep (se 2 (by rfl) ⟨132360, by rfl⟩ : syracuseStep 352961 = 264721) B264721
theorem B352979 : Blo 231814 352979 := bstep (se 1 (by rfl) ⟨264734, by rfl⟩ : syracuseStep 352979 = 529469) B529469
theorem B451313 : Blo 231814 451313 := bstep (se 2 (by rfl) ⟨169242, by rfl⟩ : syracuseStep 451313 = 338485) B338485
theorem B2712305 : Blo 231814 2712305 := bstep (se 2 (by rfl) ⟨1017114, by rfl⟩ : syracuseStep 2712305 = 2034229) B2034229
theorem B353009 : Blo 231814 353009 := bstep (se 2 (by rfl) ⟨132378, by rfl⟩ : syracuseStep 353009 = 264757) B264757
theorem B353027 : Blo 231814 353027 := bstep (se 1 (by rfl) ⟨264770, by rfl⟩ : syracuseStep 353027 = 529541) B529541
theorem B353057 : Blo 231814 353057 := bstep (se 2 (by rfl) ⟨132396, by rfl⟩ : syracuseStep 353057 = 264793) B264793
theorem B353075 : Blo 231814 353075 := bstep (se 1 (by rfl) ⟨264806, by rfl⟩ : syracuseStep 353075 = 529613) B529613
theorem B353105 : Blo 231814 353105 := bstep (se 2 (by rfl) ⟨132414, by rfl⟩ : syracuseStep 353105 = 264829) B264829
theorem B353123 : Blo 231814 353123 := bstep (se 1 (by rfl) ⟨264842, by rfl⟩ : syracuseStep 353123 = 529685) B529685
theorem B1991537 : Blo 231814 1991537 := bstep (se 2 (by rfl) ⟨746826, by rfl⟩ : syracuseStep 1991537 = 1493653) B1493653
theorem B1696625 : Blo 231814 1696625 := bstep (se 2 (by rfl) ⟨636234, by rfl⟩ : syracuseStep 1696625 = 1272469) B1272469
theorem B353153 : Blo 231814 353153 := bstep (se 2 (by rfl) ⟨132432, by rfl⟩ : syracuseStep 353153 = 264865) B264865
theorem B353171 : Blo 231814 353171 := bstep (se 1 (by rfl) ⟨264878, by rfl⟩ : syracuseStep 353171 = 529757) B529757
theorem B746417 : Blo 231814 746417 := bstep (se 2 (by rfl) ⟨279906, by rfl⟩ : syracuseStep 746417 = 559813) B559813
theorem B353201 : Blo 231814 353201 := bstep (se 2 (by rfl) ⟨132450, by rfl⟩ : syracuseStep 353201 = 264901) B264901
theorem B353219 : Blo 231814 353219 := bstep (se 1 (by rfl) ⟨264914, by rfl⟩ : syracuseStep 353219 = 529829) B529829
theorem B3761093 : Blo 231814 3761093 := bstep (se 4 (by rfl) ⟨352602, by rfl⟩ : syracuseStep 3761093 = 705205) B705205
theorem B353249 : Blo 231814 353249 := bstep (se 2 (by rfl) ⟨132468, by rfl⟩ : syracuseStep 353249 = 264937) B264937
theorem B353267 : Blo 231814 353267 := bstep (se 1 (by rfl) ⟨264950, by rfl⟩ : syracuseStep 353267 = 529901) B529901
theorem B353297 : Blo 231814 353297 := bstep (se 2 (by rfl) ⟨132486, by rfl⟩ : syracuseStep 353297 = 264973) B264973
theorem B353315 : Blo 231814 353315 := bstep (se 1 (by rfl) ⟨264986, by rfl⟩ : syracuseStep 353315 = 529973) B529973
theorem B353345 : Blo 231814 353345 := bstep (se 2 (by rfl) ⟨132504, by rfl⟩ : syracuseStep 353345 = 265009) B265009
theorem B353363 : Blo 231814 353363 := bstep (se 1 (by rfl) ⟨265022, by rfl⟩ : syracuseStep 353363 = 530045) B530045
theorem B353393 : Blo 231814 353393 := bstep (se 2 (by rfl) ⟨132522, by rfl⟩ : syracuseStep 353393 = 265045) B265045
theorem B353411 : Blo 231814 353411 := bstep (se 1 (by rfl) ⟨265058, by rfl⟩ : syracuseStep 353411 = 530117) B530117
theorem B353441 : Blo 231814 353441 := bstep (se 2 (by rfl) ⟨132540, by rfl⟩ : syracuseStep 353441 = 265081) B265081
theorem B353459 : Blo 231814 353459 := bstep (se 1 (by rfl) ⟨265094, by rfl⟩ : syracuseStep 353459 = 530189) B530189
theorem B353489 : Blo 231814 353489 := bstep (se 2 (by rfl) ⟨132558, by rfl⟩ : syracuseStep 353489 = 265117) B265117
theorem B353507 : Blo 231814 353507 := bstep (se 1 (by rfl) ⟨265130, by rfl⟩ : syracuseStep 353507 = 530261) B530261
theorem B353537 : Blo 231814 353537 := bstep (se 2 (by rfl) ⟨132576, by rfl⟩ : syracuseStep 353537 = 265153) B265153
theorem B353555 : Blo 231814 353555 := bstep (se 1 (by rfl) ⟨265166, by rfl⟩ : syracuseStep 353555 = 530333) B530333
theorem B353585 : Blo 231814 353585 := bstep (se 2 (by rfl) ⟨132594, by rfl⟩ : syracuseStep 353585 = 265189) B265189
theorem B353603 : Blo 231814 353603 := bstep (se 1 (by rfl) ⟨265202, by rfl⟩ : syracuseStep 353603 = 530405) B530405
theorem B353633 : Blo 231814 353633 := bstep (se 2 (by rfl) ⟨132612, by rfl⟩ : syracuseStep 353633 = 265225) B265225
theorem B353651 : Blo 231814 353651 := bstep (se 1 (by rfl) ⟨265238, by rfl⟩ : syracuseStep 353651 = 530477) B530477
theorem B353681 : Blo 231814 353681 := bstep (se 2 (by rfl) ⟨132630, by rfl⟩ : syracuseStep 353681 = 265261) B265261
theorem B353699 : Blo 231814 353699 := bstep (se 1 (by rfl) ⟨265274, by rfl⟩ : syracuseStep 353699 = 530549) B530549
theorem B746929 : Blo 231814 746929 := bstep (se 2 (by rfl) ⟨280098, by rfl⟩ : syracuseStep 746929 = 560197) B560197
theorem B3630563 : Blo 231814 3630563 := bstep (se 1 (by rfl) ⟨2722922, by rfl⟩ : syracuseStep 3630563 = 5445845) B5445845
theorem B1500677 : Blo 231814 1500677 := bstep (se 4 (by rfl) ⟨140688, by rfl⟩ : syracuseStep 1500677 = 281377) B281377
theorem B2975413 : Blo 231814 2975413 := bstep (se 5 (by rfl) ⟨139472, by rfl⟩ : syracuseStep 2975413 = 278945) B278945
theorem B714449 : Blo 231814 714449 := bstep (se 2 (by rfl) ⟨267918, by rfl⟩ : syracuseStep 714449 = 535837) B535837
theorem B649315 : Blo 231814 649315 := bstep (se 1 (by rfl) ⟨486986, by rfl⟩ : syracuseStep 649315 = 973973) B973973
theorem B7301573 : Blo 231814 7301573 := bstep (se 4 (by rfl) ⟨684522, by rfl⟩ : syracuseStep 7301573 = 1369045) B1369045
theorem B748045 : Blo 231814 748045 := bstep (se 3 (by rfl) ⟨140258, by rfl⟩ : syracuseStep 748045 = 280517) B280517
theorem B748109 : Blo 231814 748109 := bstep (se 3 (by rfl) ⟨140270, by rfl⟩ : syracuseStep 748109 = 280541) B280541
theorem B453347 : Blo 231814 453347 := bstep (se 1 (by rfl) ⟨340010, by rfl⟩ : syracuseStep 453347 = 680021) B680021
theorem B1895309 : Blo 231814 1895309 := bstep (se 3 (by rfl) ⟨355370, by rfl⟩ : syracuseStep 1895309 = 710741) B710741
theorem B1272773 : Blo 231814 1272773 := bstep (se 4 (by rfl) ⟨119322, by rfl⟩ : syracuseStep 1272773 = 238645) B238645
theorem B1174499 : Blo 231814 1174499 := bstep (se 1 (by rfl) ⟨880874, by rfl⟩ : syracuseStep 1174499 = 1761749) B1761749
theorem B1338353 : Blo 231814 1338353 := bstep (se 2 (by rfl) ⟨501882, by rfl⟩ : syracuseStep 1338353 = 1003765) B1003765
theorem B1993997 : Blo 231814 1993997 := bstep (se 3 (by rfl) ⟨373874, by rfl⟩ : syracuseStep 1993997 = 747749) B747749
theorem B3042613 : Blo 231814 3042613 := bstep (se 5 (by rfl) ⟨142622, by rfl⟩ : syracuseStep 3042613 = 285245) B285245
theorem B1469765 : Blo 231814 1469765 := bstep (se 4 (by rfl) ⟨137790, by rfl⟩ : syracuseStep 1469765 = 275581) B275581
theorem B1273229 : Blo 231814 1273229 := bstep (se 3 (by rfl) ⟨238730, by rfl⟩ : syracuseStep 1273229 = 477461) B477461
theorem B1175309 : Blo 231814 1175309 := bstep (se 3 (by rfl) ⟨220370, by rfl⟩ : syracuseStep 1175309 = 440741) B440741
theorem B421699 : Blo 231814 421699 := bstep (se 1 (by rfl) ⟨316274, by rfl⟩ : syracuseStep 421699 = 632549) B632549
theorem B880739 : Blo 231814 880739 := bstep (se 1 (by rfl) ⟨660554, by rfl⟩ : syracuseStep 880739 = 1321109) B1321109
theorem B880753 : Blo 231814 880753 := bstep (se 2 (by rfl) ⟨330282, by rfl⟩ : syracuseStep 880753 = 660565) B660565
theorem B782513 : Blo 231814 782513 := bstep (se 2 (by rfl) ⟨293442, by rfl⟩ : syracuseStep 782513 = 586885) B586885
theorem B749891 : Blo 231814 749891 := bstep (se 1 (by rfl) ⟨562418, by rfl⟩ : syracuseStep 749891 = 1124837) B1124837
theorem B1339811 : Blo 231814 1339811 := bstep (se 1 (by rfl) ⟨1004858, by rfl⟩ : syracuseStep 1339811 = 2009717) B2009717
theorem B422339 : Blo 231814 422339 := bstep (se 1 (by rfl) ⟨316754, by rfl⟩ : syracuseStep 422339 = 633509) B633509
theorem B848369 : Blo 231814 848369 := bstep (se 2 (by rfl) ⟨318138, by rfl⟩ : syracuseStep 848369 = 636277) B636277
theorem B356897 : Blo 231814 356897 := bstep (se 2 (by rfl) ⟨133836, by rfl⟩ : syracuseStep 356897 = 267673) B267673
theorem B422513 : Blo 231814 422513 := bstep (se 2 (by rfl) ⟨158442, by rfl⟩ : syracuseStep 422513 = 316885) B316885
theorem B783053 : Blo 231814 783053 := bstep (se 3 (by rfl) ⟨146822, by rfl⟩ : syracuseStep 783053 = 293645) B293645
theorem B357091 : Blo 231814 357091 := bstep (se 1 (by rfl) ⟨267818, by rfl⟩ : syracuseStep 357091 = 535637) B535637
theorem B783107 : Blo 231814 783107 := bstep (se 1 (by rfl) ⟨587330, by rfl⟩ : syracuseStep 783107 = 1174661) B1174661
theorem B1274629 : Blo 231814 1274629 := bstep (se 4 (by rfl) ⟨119496, by rfl⟩ : syracuseStep 1274629 = 238993) B238993
theorem B848717 : Blo 231814 848717 := bstep (se 3 (by rfl) ⟨159134, by rfl⟩ : syracuseStep 848717 = 318269) B318269
theorem B783377 : Blo 231814 783377 := bstep (se 2 (by rfl) ⟨293766, by rfl⟩ : syracuseStep 783377 = 587533) B587533
theorem B1504291 : Blo 231814 1504291 := bstep (se 1 (by rfl) ⟨1128218, by rfl⟩ : syracuseStep 1504291 = 2256437) B2256437
theorem B586865 : Blo 231814 586865 := bstep (se 2 (by rfl) ⟨220074, by rfl⟩ : syracuseStep 586865 = 440149) B440149
theorem B4027589 : Blo 231814 4027589 := bstep (se 4 (by rfl) ⟨377586, by rfl⟩ : syracuseStep 4027589 = 755173) B755173
theorem B521585 : Blo 231814 521585 := bstep (se 2 (by rfl) ⟨195594, by rfl⟩ : syracuseStep 521585 = 391189) B391189
theorem B521603 : Blo 231814 521603 := bstep (se 1 (by rfl) ⟨391202, by rfl⟩ : syracuseStep 521603 = 782405) B782405
theorem B1340813 : Blo 231814 1340813 := bstep (se 3 (by rfl) ⟨251402, by rfl⟩ : syracuseStep 1340813 = 502805) B502805
theorem B1799651 : Blo 231814 1799651 := bstep (se 1 (by rfl) ⟨1349738, by rfl⟩ : syracuseStep 1799651 = 2699477) B2699477
theorem B882211 : Blo 231814 882211 := bstep (se 1 (by rfl) ⟨661658, by rfl⟩ : syracuseStep 882211 = 1323317) B1323317
theorem B783917 : Blo 231814 783917 := bstep (se 3 (by rfl) ⟨146984, by rfl⟩ : syracuseStep 783917 = 293969) B293969
theorem B783971 : Blo 231814 783971 := bstep (se 1 (by rfl) ⟨587978, by rfl⟩ : syracuseStep 783971 = 1175957) B1175957
theorem B521873 : Blo 231814 521873 := bstep (se 2 (by rfl) ⟨195702, by rfl⟩ : syracuseStep 521873 = 391405) B391405
theorem B521891 : Blo 231814 521891 := bstep (se 1 (by rfl) ⟨391418, by rfl⟩ : syracuseStep 521891 = 782837) B782837
theorem B358241 : Blo 231814 358241 := bstep (se 2 (by rfl) ⟨134340, by rfl⟩ : syracuseStep 358241 = 268681) B268681
theorem B784241 : Blo 231814 784241 := bstep (se 2 (by rfl) ⟨294090, by rfl⟩ : syracuseStep 784241 = 588181) B588181
theorem B522161 : Blo 231814 522161 := bstep (se 2 (by rfl) ⟨195810, by rfl⟩ : syracuseStep 522161 = 391621) B391621
theorem B522179 : Blo 231814 522179 := bstep (se 1 (by rfl) ⟨391634, by rfl⟩ : syracuseStep 522179 = 783269) B783269
theorem B2652101 : Blo 231814 2652101 := bstep (se 4 (by rfl) ⟨248634, by rfl⟩ : syracuseStep 2652101 = 497269) B497269
theorem B587857 : Blo 231814 587857 := bstep (se 2 (by rfl) ⟨220446, by rfl⟩ : syracuseStep 587857 = 440893) B440893
theorem B358499 : Blo 231814 358499 := bstep (se 1 (by rfl) ⟨268874, by rfl⟩ : syracuseStep 358499 = 537749) B537749
theorem B391297 : Blo 231814 391297 := bstep (se 2 (by rfl) ⟨146736, by rfl⟩ : syracuseStep 391297 = 293473) B293473
theorem B391331 : Blo 231814 391331 := bstep (se 1 (by rfl) ⟨293498, by rfl⟩ : syracuseStep 391331 = 586997) B586997
theorem B522449 : Blo 231814 522449 := bstep (se 2 (by rfl) ⟨195918, by rfl⟩ : syracuseStep 522449 = 391837) B391837
theorem B522467 : Blo 231814 522467 := bstep (se 1 (by rfl) ⟨391850, by rfl⟩ : syracuseStep 522467 = 783701) B783701
theorem B391459 : Blo 231814 391459 := bstep (se 1 (by rfl) ⟨293594, by rfl⟩ : syracuseStep 391459 = 587189) B587189
theorem B588131 : Blo 231814 588131 := bstep (se 1 (by rfl) ⟨441098, by rfl⟩ : syracuseStep 588131 = 882197) B882197
theorem B784781 : Blo 231814 784781 := bstep (se 3 (by rfl) ⟨147146, by rfl⟩ : syracuseStep 784781 = 294293) B294293
theorem B391601 : Blo 231814 391601 := bstep (se 2 (by rfl) ⟨146850, by rfl⟩ : syracuseStep 391601 = 293701) B293701
theorem B784835 : Blo 231814 784835 := bstep (se 1 (by rfl) ⟨588626, by rfl⟩ : syracuseStep 784835 = 1177253) B1177253
theorem B522737 : Blo 231814 522737 := bstep (se 2 (by rfl) ⟨196026, by rfl⟩ : syracuseStep 522737 = 392053) B392053
theorem B522755 : Blo 231814 522755 := bstep (se 1 (by rfl) ⟨392066, by rfl⟩ : syracuseStep 522755 = 784133) B784133
theorem B588323 : Blo 231814 588323 := bstep (se 1 (by rfl) ⟨441242, by rfl⟩ : syracuseStep 588323 = 882485) B882485
theorem B391729 : Blo 231814 391729 := bstep (se 2 (by rfl) ⟨146898, by rfl⟩ : syracuseStep 391729 = 293797) B293797
theorem B391763 : Blo 231814 391763 := bstep (se 1 (by rfl) ⟨293822, by rfl⟩ : syracuseStep 391763 = 587645) B587645
theorem B1178225 : Blo 231814 1178225 := bstep (se 2 (by rfl) ⟨441834, by rfl⟩ : syracuseStep 1178225 = 883669) B883669
theorem B293539 : Blo 231814 293539 := bstep (se 1 (by rfl) ⟨220154, by rfl⟩ : syracuseStep 293539 = 440309) B440309
theorem B785105 : Blo 231814 785105 := bstep (se 2 (by rfl) ⟨294414, by rfl⟩ : syracuseStep 785105 = 588829) B588829
theorem B391891 : Blo 231814 391891 := bstep (se 1 (by rfl) ⟨293918, by rfl⟩ : syracuseStep 391891 = 587837) B587837
theorem B260851 : Blo 231814 260851 := bstep (se 1 (by rfl) ⟨195638, by rfl⟩ : syracuseStep 260851 = 391277) B391277
theorem B293635 : Blo 231814 293635 := bstep (se 1 (by rfl) ⟨220226, by rfl⟩ : syracuseStep 293635 = 440453) B440453
theorem B523025 : Blo 231814 523025 := bstep (se 2 (by rfl) ⟨196134, by rfl⟩ : syracuseStep 523025 = 392269) B392269
theorem B523043 : Blo 231814 523043 := bstep (se 1 (by rfl) ⟨392282, by rfl⟩ : syracuseStep 523043 = 784565) B784565
theorem B752465 : Blo 231814 752465 := bstep (se 2 (by rfl) ⟨282174, by rfl⟩ : syracuseStep 752465 = 564349) B564349
theorem B392033 : Blo 231814 392033 := bstep (se 2 (by rfl) ⟨147012, by rfl⟩ : syracuseStep 392033 = 294025) B294025
theorem B260995 : Blo 231814 260995 := bstep (se 1 (by rfl) ⟨195746, by rfl⟩ : syracuseStep 260995 = 391493) B391493
theorem B392161 : Blo 231814 392161 := bstep (se 2 (by rfl) ⟨147060, by rfl⟩ : syracuseStep 392161 = 294121) B294121
theorem B392195 : Blo 231814 392195 := bstep (se 1 (by rfl) ⟨294146, by rfl⟩ : syracuseStep 392195 = 588293) B588293
theorem B2194445 : Blo 231814 2194445 := bstep (se 3 (by rfl) ⟨411458, by rfl⟩ : syracuseStep 2194445 = 822917) B822917
theorem B261139 : Blo 231814 261139 := bstep (se 1 (by rfl) ⟨195854, by rfl⟩ : syracuseStep 261139 = 391709) B391709
theorem B523313 : Blo 231814 523313 := bstep (se 2 (by rfl) ⟨196242, by rfl⟩ : syracuseStep 523313 = 392485) B392485
theorem B523331 : Blo 231814 523331 := bstep (se 1 (by rfl) ⟨392498, by rfl⟩ : syracuseStep 523331 = 784997) B784997
theorem B392323 : Blo 231814 392323 := bstep (se 1 (by rfl) ⟨294242, by rfl⟩ : syracuseStep 392323 = 588485) B588485
theorem B261283 : Blo 231814 261283 := bstep (se 1 (by rfl) ⟨195962, by rfl⟩ : syracuseStep 261283 = 391925) B391925
theorem B785645 : Blo 231814 785645 := bstep (se 3 (by rfl) ⟨147308, by rfl⟩ : syracuseStep 785645 = 294617) B294617
theorem B294131 : Blo 231814 294131 := bstep (se 1 (by rfl) ⟨220598, by rfl⟩ : syracuseStep 294131 = 441197) B441197
theorem B392465 : Blo 231814 392465 := bstep (se 2 (by rfl) ⟨147174, by rfl⟩ : syracuseStep 392465 = 294349) B294349
theorem B785699 : Blo 231814 785699 := bstep (se 1 (by rfl) ⟨589274, by rfl⟩ : syracuseStep 785699 = 1178549) B1178549
theorem B949553 : Blo 231814 949553 := bstep (se 2 (by rfl) ⟨356082, by rfl⟩ : syracuseStep 949553 = 712165) B712165
theorem B261427 : Blo 231814 261427 := bstep (se 1 (by rfl) ⟨196070, by rfl⟩ : syracuseStep 261427 = 392141) B392141
theorem B523601 : Blo 231814 523601 := bstep (se 2 (by rfl) ⟨196350, by rfl⟩ : syracuseStep 523601 = 392701) B392701
theorem B523619 : Blo 231814 523619 := bstep (se 1 (by rfl) ⟨392714, by rfl⟩ : syracuseStep 523619 = 785429) B785429
theorem B392593 : Blo 231814 392593 := bstep (se 2 (by rfl) ⟨147222, by rfl⟩ : syracuseStep 392593 = 294445) B294445
theorem B392627 : Blo 231814 392627 := bstep (se 1 (by rfl) ⟨294470, by rfl⟩ : syracuseStep 392627 = 588941) B588941
theorem B261571 : Blo 231814 261571 := bstep (se 1 (by rfl) ⟨196178, by rfl⟩ : syracuseStep 261571 = 392357) B392357
theorem B589265 : Blo 231814 589265 := bstep (se 2 (by rfl) ⟨220974, by rfl⟩ : syracuseStep 589265 = 441949) B441949
theorem B589315 : Blo 231814 589315 := bstep (se 1 (by rfl) ⟨441986, by rfl⟩ : syracuseStep 589315 = 883973) B883973
theorem B785969 : Blo 231814 785969 := bstep (se 2 (by rfl) ⟨294738, by rfl⟩ : syracuseStep 785969 = 589477) B589477
theorem B392755 : Blo 231814 392755 := bstep (se 1 (by rfl) ⟨294566, by rfl⟩ : syracuseStep 392755 = 589133) B589133
theorem B261715 : Blo 231814 261715 := bstep (se 1 (by rfl) ⟨196286, by rfl⟩ : syracuseStep 261715 = 392573) B392573
theorem B2719331 : Blo 231814 2719331 := bstep (se 1 (by rfl) ⟨2039498, by rfl⟩ : syracuseStep 2719331 = 4078997) B4078997
theorem B523889 : Blo 231814 523889 := bstep (se 2 (by rfl) ⟨196458, by rfl⟩ : syracuseStep 523889 = 392917) B392917
theorem B523907 : Blo 231814 523907 := bstep (se 1 (by rfl) ⟨392930, by rfl⟩ : syracuseStep 523907 = 785861) B785861
theorem B589457 : Blo 231814 589457 := bstep (se 2 (by rfl) ⟨221046, by rfl⟩ : syracuseStep 589457 = 442093) B442093
theorem B392897 : Blo 231814 392897 := bstep (se 2 (by rfl) ⟨147336, by rfl⟩ : syracuseStep 392897 = 294673) B294673
theorem B884429 : Blo 231814 884429 := bstep (se 3 (by rfl) ⟨165830, by rfl⟩ : syracuseStep 884429 = 331661) B331661
theorem B261859 : Blo 231814 261859 := bstep (se 1 (by rfl) ⟨196394, by rfl⟩ : syracuseStep 261859 = 392789) B392789
theorem B1507085 : Blo 231814 1507085 := bstep (se 3 (by rfl) ⟨282578, by rfl⟩ : syracuseStep 1507085 = 565157) B565157
theorem B393025 : Blo 231814 393025 := bstep (se 2 (by rfl) ⟨147384, by rfl⟩ : syracuseStep 393025 = 294769) B294769
theorem B393059 : Blo 231814 393059 := bstep (se 1 (by rfl) ⟨294794, by rfl⟩ : syracuseStep 393059 = 589589) B589589
theorem B262003 : Blo 231814 262003 := bstep (se 1 (by rfl) ⟨196502, by rfl⟩ : syracuseStep 262003 = 393005) B393005
theorem B524177 : Blo 231814 524177 := bstep (se 2 (by rfl) ⟨196566, by rfl⟩ : syracuseStep 524177 = 393133) B393133
theorem B524195 : Blo 231814 524195 := bstep (se 1 (by rfl) ⟨393146, by rfl⟩ : syracuseStep 524195 = 786293) B786293
theorem B294835 : Blo 231814 294835 := bstep (se 1 (by rfl) ⟨221126, by rfl⟩ : syracuseStep 294835 = 442253) B442253
theorem B393187 : Blo 231814 393187 := bstep (se 1 (by rfl) ⟨294890, by rfl⟩ : syracuseStep 393187 = 589781) B589781
theorem B786455 : Blo 231814 786455 := bstep (se 1 (by rfl) ⟨589841, by rfl⟩ : syracuseStep 786455 = 1179683) B1179683
theorem B393241 : Blo 231814 393241 := bstep (se 2 (by rfl) ⟨147465, by rfl⟩ : syracuseStep 393241 = 294931) B294931
theorem B524339 : Blo 231814 524339 := bstep (se 1 (by rfl) ⟨393254, by rfl⟩ : syracuseStep 524339 = 786509) B786509
theorem B262219 : Blo 231814 262219 := bstep (se 1 (by rfl) ⟨196664, by rfl⟩ : syracuseStep 262219 = 393329) B393329
theorem B524375 : Blo 231814 524375 := bstep (se 1 (by rfl) ⟨393281, by rfl⟩ : syracuseStep 524375 = 786563) B786563
theorem B589913 : Blo 231814 589913 := bstep (se 2 (by rfl) ⟨221217, by rfl⟩ : syracuseStep 589913 = 442435) B442435
theorem B8781965 : Blo 231814 8781965 := bstep (se 3 (by rfl) ⟨1646618, by rfl⟩ : syracuseStep 8781965 = 3293237) B3293237
theorem B884915 : Blo 231814 884915 := bstep (se 1 (by rfl) ⟨663686, by rfl⟩ : syracuseStep 884915 = 1327373) B1327373
theorem B262327 : Blo 231814 262327 := bstep (se 1 (by rfl) ⟨196745, by rfl⟩ : syracuseStep 262327 = 393491) B393491
theorem B2228485 : Blo 231814 2228485 := bstep (se 4 (by rfl) ⟨208920, by rfl⟩ : syracuseStep 2228485 = 417841) B417841
theorem B524555 : Blo 231814 524555 := bstep (se 1 (by rfl) ⟨393416, by rfl⟩ : syracuseStep 524555 = 786833) B786833
theorem B524609 : Blo 231814 524609 := bstep (se 2 (by rfl) ⟨196728, by rfl⟩ : syracuseStep 524609 = 393457) B393457
theorem B295255 : Blo 231814 295255 := bstep (se 1 (by rfl) ⟨221441, by rfl⟩ : syracuseStep 295255 = 442883) B442883
theorem B262507 : Blo 231814 262507 := bstep (se 1 (by rfl) ⟨196880, by rfl⟩ : syracuseStep 262507 = 393761) B393761
theorem B262615 : Blo 231814 262615 := bstep (se 1 (by rfl) ⟨196961, by rfl⟩ : syracuseStep 262615 = 393923) B393923
theorem B524825 : Blo 231814 524825 := bstep (se 2 (by rfl) ⟨196809, by rfl⟩ : syracuseStep 524825 = 393619) B393619
theorem B786995 : Blo 231814 786995 := bstep (se 1 (by rfl) ⟨590246, by rfl⟩ : syracuseStep 786995 = 1180493) B1180493
theorem B393815 : Blo 231814 393815 := bstep (se 1 (by rfl) ⟨295361, by rfl⟩ : syracuseStep 393815 = 590723) B590723
theorem B524915 : Blo 231814 524915 := bstep (se 1 (by rfl) ⟨393686, by rfl⟩ : syracuseStep 524915 = 787373) B787373
theorem B262795 : Blo 231814 262795 := bstep (se 1 (by rfl) ⟨197096, by rfl⟩ : syracuseStep 262795 = 394193) B394193
theorem B524951 : Blo 231814 524951 := bstep (se 1 (by rfl) ⟨393713, by rfl⟩ : syracuseStep 524951 = 787427) B787427
theorem B2130583 : Blo 231814 2130583 := bstep (se 1 (by rfl) ⟨1597937, by rfl⟩ : syracuseStep 2130583 = 3195875) B3195875
theorem B393943 : Blo 231814 393943 := bstep (se 1 (by rfl) ⟨295457, by rfl⟩ : syracuseStep 393943 = 590915) B590915
theorem B262903 : Blo 231814 262903 := bstep (se 1 (by rfl) ⟨197177, by rfl⟩ : syracuseStep 262903 = 394355) B394355
theorem B787265 : Blo 231814 787265 := bstep (se 2 (by rfl) ⟨295224, by rfl⟩ : syracuseStep 787265 = 590449) B590449
theorem B525131 : Blo 231814 525131 := bstep (se 1 (by rfl) ⟨393848, by rfl⟩ : syracuseStep 525131 = 787697) B787697
theorem B525185 : Blo 231814 525185 := bstep (se 2 (by rfl) ⟨196944, by rfl⟩ : syracuseStep 525185 = 393889) B393889
theorem B263083 : Blo 231814 263083 := bstep (se 1 (by rfl) ⟨197312, by rfl⟩ : syracuseStep 263083 = 394625) B394625
theorem B263191 : Blo 231814 263191 := bstep (se 1 (by rfl) ⟨197393, by rfl⟩ : syracuseStep 263191 = 394787) B394787
theorem B525401 : Blo 231814 525401 := bstep (se 2 (by rfl) ⟨197025, by rfl⟩ : syracuseStep 525401 = 394051) B394051
theorem B296075 : Blo 231814 296075 := bstep (se 1 (by rfl) ⟨222056, by rfl⟩ : syracuseStep 296075 = 444113) B444113
theorem B525491 : Blo 231814 525491 := bstep (se 1 (by rfl) ⟨394118, by rfl⟩ : syracuseStep 525491 = 788237) B788237
theorem B263371 : Blo 231814 263371 := bstep (se 1 (by rfl) ⟨197528, by rfl⟩ : syracuseStep 263371 = 395057) B395057
theorem B525527 : Blo 231814 525527 := bstep (se 1 (by rfl) ⟨394145, by rfl⟩ : syracuseStep 525527 = 788291) B788291
theorem B263479 : Blo 231814 263479 := bstep (se 1 (by rfl) ⟨197609, by rfl⟩ : syracuseStep 263479 = 395219) B395219
theorem B394571 : Blo 231814 394571 := bstep (se 1 (by rfl) ⟨295928, by rfl⟩ : syracuseStep 394571 = 591857) B591857
theorem B787805 : Blo 231814 787805 := bstep (se 3 (by rfl) ⟨147713, by rfl⟩ : syracuseStep 787805 = 295427) B295427
theorem B525707 : Blo 231814 525707 := bstep (se 1 (by rfl) ⟨394280, by rfl⟩ : syracuseStep 525707 = 788561) B788561
theorem B951725 : Blo 231814 951725 := bstep (se 3 (by rfl) ⟨178448, by rfl⟩ : syracuseStep 951725 = 356897) B356897
theorem B2131379 : Blo 231814 2131379 := bstep (se 1 (by rfl) ⟨1598534, by rfl⟩ : syracuseStep 2131379 = 3197069) B3197069
theorem B3016115 : Blo 231814 3016115 := bstep (se 1 (by rfl) ⟨2262086, by rfl⟩ : syracuseStep 3016115 = 4524173) B4524173
theorem B525761 : Blo 231814 525761 := bstep (se 2 (by rfl) ⟨197160, by rfl⟩ : syracuseStep 525761 = 394321) B394321
theorem B394699 : Blo 231814 394699 := bstep (se 1 (by rfl) ⟨296024, by rfl⟩ : syracuseStep 394699 = 592049) B592049
theorem B951755 : Blo 231814 951755 := bstep (se 1 (by rfl) ⟨713816, by rfl⟩ : syracuseStep 951755 = 1427633) B1427633
theorem B263659 : Blo 231814 263659 := bstep (se 1 (by rfl) ⟨197744, by rfl⟩ : syracuseStep 263659 = 395489) B395489
theorem B263767 : Blo 231814 263767 := bstep (se 1 (by rfl) ⟨197825, by rfl⟩ : syracuseStep 263767 = 395651) B395651
theorem B394841 : Blo 231814 394841 := bstep (se 2 (by rfl) ⟨148065, by rfl⟩ : syracuseStep 394841 = 296131) B296131
theorem B886403 : Blo 231814 886403 := bstep (se 1 (by rfl) ⟨664802, by rfl⟩ : syracuseStep 886403 = 1329605) B1329605
theorem B525977 : Blo 231814 525977 := bstep (se 2 (by rfl) ⟨197241, by rfl⟩ : syracuseStep 525977 = 394483) B394483
theorem B591563 : Blo 231814 591563 := bstep (se 1 (by rfl) ⟨443672, by rfl⟩ : syracuseStep 591563 = 887345) B887345
theorem B394969 : Blo 231814 394969 := bstep (se 2 (by rfl) ⟨148113, by rfl⟩ : syracuseStep 394969 = 296227) B296227
theorem B526067 : Blo 231814 526067 := bstep (se 1 (by rfl) ⟨394550, by rfl⟩ : syracuseStep 526067 = 789101) B789101
theorem B263947 : Blo 231814 263947 := bstep (se 1 (by rfl) ⟨197960, by rfl⟩ : syracuseStep 263947 = 395921) B395921
theorem B526103 : Blo 231814 526103 := bstep (se 1 (by rfl) ⟨394577, by rfl⟩ : syracuseStep 526103 = 789155) B789155
theorem B2098979 : Blo 231814 2098979 := bstep (se 1 (by rfl) ⟨1574234, by rfl⟩ : syracuseStep 2098979 = 3148469) B3148469
theorem B296779 : Blo 231814 296779 := bstep (se 1 (by rfl) ⟨222584, by rfl⟩ : syracuseStep 296779 = 445169) B445169
theorem B264055 : Blo 231814 264055 := bstep (se 1 (by rfl) ⟨198041, by rfl⟩ : syracuseStep 264055 = 396083) B396083
theorem B526283 : Blo 231814 526283 := bstep (se 1 (by rfl) ⟨394712, by rfl⟩ : syracuseStep 526283 = 789425) B789425
theorem B1771469 : Blo 231814 1771469 := bstep (se 3 (by rfl) ⟨332150, by rfl⟩ : syracuseStep 1771469 = 664301) B664301
theorem B526337 : Blo 231814 526337 := bstep (se 2 (by rfl) ⟨197376, by rfl⟩ : syracuseStep 526337 = 394753) B394753
theorem B264235 : Blo 231814 264235 := bstep (se 1 (by rfl) ⟨198176, by rfl⟩ : syracuseStep 264235 = 396353) B396353
theorem B886859 : Blo 231814 886859 := bstep (se 1 (by rfl) ⟨665144, by rfl⟩ : syracuseStep 886859 = 1330289) B1330289
theorem B297047 : Blo 231814 297047 := bstep (se 1 (by rfl) ⟨222785, by rfl⟩ : syracuseStep 297047 = 445571) B445571
theorem B1181789 : Blo 231814 1181789 := bstep (se 3 (by rfl) ⟨221585, by rfl⟩ : syracuseStep 1181789 = 443171) B443171
theorem B264343 : Blo 231814 264343 := bstep (se 1 (by rfl) ⟨198257, by rfl⟩ : syracuseStep 264343 = 396515) B396515
theorem B1411289 : Blo 231814 1411289 := bstep (se 2 (by rfl) ⟨529233, by rfl⟩ : syracuseStep 1411289 = 1058467) B1058467
theorem B526553 : Blo 231814 526553 := bstep (se 2 (by rfl) ⟨197457, by rfl⟩ : syracuseStep 526553 = 394915) B394915
theorem B3967217 : Blo 231814 3967217 := bstep (se 2 (by rfl) ⟨1487706, by rfl⟩ : syracuseStep 3967217 = 2975413) B2975413
theorem B887057 : Blo 231814 887057 := bstep (se 2 (by rfl) ⟨332646, by rfl⟩ : syracuseStep 887057 = 665293) B665293
theorem B395543 : Blo 231814 395543 := bstep (se 1 (by rfl) ⟨296657, by rfl⟩ : syracuseStep 395543 = 593315) B593315
theorem B526643 : Blo 231814 526643 := bstep (se 1 (by rfl) ⟨394982, by rfl⟩ : syracuseStep 526643 = 789965) B789965
theorem B264523 : Blo 231814 264523 := bstep (se 1 (by rfl) ⟨198392, by rfl⟩ : syracuseStep 264523 = 396785) B396785
theorem B526679 : Blo 231814 526679 := bstep (se 1 (by rfl) ⟨395009, by rfl⟩ : syracuseStep 526679 = 790019) B790019
theorem B231819 : Blo 231814 231819 := bstep (se 1 (by rfl) ⟨173864, by rfl⟩ : syracuseStep 231819 = 347729) B347729
theorem B231831 : Blo 231814 231831 := bstep (se 1 (by rfl) ⟨173873, by rfl⟩ : syracuseStep 231831 = 347747) B347747
theorem B395671 : Blo 231814 395671 := bstep (se 1 (by rfl) ⟨296753, by rfl⟩ : syracuseStep 395671 = 593507) B593507
theorem B231851 : Blo 231814 231851 := bstep (se 1 (by rfl) ⟨173888, by rfl⟩ : syracuseStep 231851 = 347777) B347777
theorem B1771955 : Blo 231814 1771955 := bstep (se 1 (by rfl) ⟨1328966, by rfl⟩ : syracuseStep 1771955 = 2657933) B2657933
theorem B231863 : Blo 231814 231863 := bstep (se 1 (by rfl) ⟨173897, by rfl⟩ : syracuseStep 231863 = 347795) B347795
theorem B264631 : Blo 231814 264631 := bstep (se 1 (by rfl) ⟨198473, by rfl⟩ : syracuseStep 264631 = 396947) B396947
theorem B231883 : Blo 231814 231883 := bstep (se 1 (by rfl) ⟨173912, by rfl⟩ : syracuseStep 231883 = 347825) B347825
theorem B788939 : Blo 231814 788939 := bstep (se 1 (by rfl) ⟨591704, by rfl⟩ : syracuseStep 788939 = 1183409) B1183409
theorem B231895 : Blo 231814 231895 := bstep (se 1 (by rfl) ⟨173921, by rfl⟩ : syracuseStep 231895 = 347843) B347843
theorem B231915 : Blo 231814 231915 := bstep (se 1 (by rfl) ⟨173936, by rfl⟩ : syracuseStep 231915 = 347873) B347873
theorem B231927 : Blo 231814 231927 := bstep (se 1 (by rfl) ⟨173945, by rfl⟩ : syracuseStep 231927 = 347891) B347891
theorem B231947 : Blo 231814 231947 := bstep (se 1 (by rfl) ⟨173960, by rfl⟩ : syracuseStep 231947 = 347921) B347921
theorem B526859 : Blo 231814 526859 := bstep (se 1 (by rfl) ⟨395144, by rfl⟩ : syracuseStep 526859 = 790289) B790289
theorem B231959 : Blo 231814 231959 := bstep (se 1 (by rfl) ⟨173969, by rfl⟩ : syracuseStep 231959 = 347939) B347939
theorem B231979 : Blo 231814 231979 := bstep (se 1 (by rfl) ⟨173984, by rfl⟩ : syracuseStep 231979 = 347969) B347969
theorem B231991 : Blo 231814 231991 := bstep (se 1 (by rfl) ⟨173993, by rfl⟩ : syracuseStep 231991 = 347987) B347987
theorem B526913 : Blo 231814 526913 := bstep (se 2 (by rfl) ⟨197592, by rfl⟩ : syracuseStep 526913 = 395185) B395185
theorem B232011 : Blo 231814 232011 := bstep (se 1 (by rfl) ⟨174008, by rfl⟩ : syracuseStep 232011 = 348017) B348017
theorem B232023 : Blo 231814 232023 := bstep (se 1 (by rfl) ⟨174017, by rfl⟩ : syracuseStep 232023 = 348035) B348035
theorem B232043 : Blo 231814 232043 := bstep (se 1 (by rfl) ⟨174032, by rfl⟩ : syracuseStep 232043 = 348065) B348065
theorem B264811 : Blo 231814 264811 := bstep (se 1 (by rfl) ⟨198608, by rfl⟩ : syracuseStep 264811 = 397217) B397217
theorem B232055 : Blo 231814 232055 := bstep (se 1 (by rfl) ⟨174041, by rfl⟩ : syracuseStep 232055 = 348083) B348083
theorem B232075 : Blo 231814 232075 := bstep (se 1 (by rfl) ⟨174056, by rfl⟩ : syracuseStep 232075 = 348113) B348113
theorem B232087 : Blo 231814 232087 := bstep (se 1 (by rfl) ⟨174065, by rfl⟩ : syracuseStep 232087 = 348131) B348131
theorem B592535 : Blo 231814 592535 := bstep (se 1 (by rfl) ⟨444401, by rfl⟩ : syracuseStep 592535 = 888803) B888803
theorem B232107 : Blo 231814 232107 := bstep (se 1 (by rfl) ⟨174080, by rfl⟩ : syracuseStep 232107 = 348161) B348161
theorem B232119 : Blo 231814 232119 := bstep (se 1 (by rfl) ⟨174089, by rfl⟩ : syracuseStep 232119 = 348179) B348179
theorem B232139 : Blo 231814 232139 := bstep (se 1 (by rfl) ⟨174104, by rfl⟩ : syracuseStep 232139 = 348209) B348209
theorem B232151 : Blo 231814 232151 := bstep (se 1 (by rfl) ⟨174113, by rfl⟩ : syracuseStep 232151 = 348227) B348227
theorem B264919 : Blo 231814 264919 := bstep (se 1 (by rfl) ⟨198689, by rfl⟩ : syracuseStep 264919 = 397379) B397379
theorem B789209 : Blo 231814 789209 := bstep (se 2 (by rfl) ⟨295953, by rfl⟩ : syracuseStep 789209 = 591907) B591907
theorem B232171 : Blo 231814 232171 := bstep (se 1 (by rfl) ⟨174128, by rfl⟩ : syracuseStep 232171 = 348257) B348257
theorem B232183 : Blo 231814 232183 := bstep (se 1 (by rfl) ⟨174137, by rfl⟩ : syracuseStep 232183 = 348275) B348275
theorem B232203 : Blo 231814 232203 := bstep (se 1 (by rfl) ⟨174152, by rfl⟩ : syracuseStep 232203 = 348305) B348305
theorem B297751 : Blo 231814 297751 := bstep (se 1 (by rfl) ⟨223313, by rfl⟩ : syracuseStep 297751 = 446627) B446627
theorem B232215 : Blo 231814 232215 := bstep (se 1 (by rfl) ⟨174161, by rfl⟩ : syracuseStep 232215 = 348323) B348323
theorem B527129 : Blo 231814 527129 := bstep (se 2 (by rfl) ⟨197673, by rfl⟩ : syracuseStep 527129 = 395347) B395347
theorem B232235 : Blo 231814 232235 := bstep (se 1 (by rfl) ⟨174176, by rfl⟩ : syracuseStep 232235 = 348353) B348353
theorem B232247 : Blo 231814 232247 := bstep (se 1 (by rfl) ⟨174185, by rfl⟩ : syracuseStep 232247 = 348371) B348371
theorem B232267 : Blo 231814 232267 := bstep (se 1 (by rfl) ⟨174200, by rfl⟩ : syracuseStep 232267 = 348401) B348401
theorem B232279 : Blo 231814 232279 := bstep (se 1 (by rfl) ⟨174209, by rfl⟩ : syracuseStep 232279 = 348419) B348419
theorem B232299 : Blo 231814 232299 := bstep (se 1 (by rfl) ⟨174224, by rfl⟩ : syracuseStep 232299 = 348449) B348449
theorem B527219 : Blo 231814 527219 := bstep (se 1 (by rfl) ⟨395414, by rfl⟩ : syracuseStep 527219 = 790829) B790829
theorem B232311 : Blo 231814 232311 := bstep (se 1 (by rfl) ⟨174233, by rfl⟩ : syracuseStep 232311 = 348467) B348467
theorem B232331 : Blo 231814 232331 := bstep (se 1 (by rfl) ⟨174248, by rfl⟩ : syracuseStep 232331 = 348497) B348497
theorem B265099 : Blo 231814 265099 := bstep (se 1 (by rfl) ⟨198824, by rfl⟩ : syracuseStep 265099 = 397649) B397649
theorem B330647 : Blo 231814 330647 := bstep (se 1 (by rfl) ⟨247985, by rfl⟩ : syracuseStep 330647 = 495971) B495971
theorem B232343 : Blo 231814 232343 := bstep (se 1 (by rfl) ⟨174257, by rfl⟩ : syracuseStep 232343 = 348515) B348515
theorem B527255 : Blo 231814 527255 := bstep (se 1 (by rfl) ⟨395441, by rfl⟩ : syracuseStep 527255 = 790883) B790883
theorem B232363 : Blo 231814 232363 := bstep (se 1 (by rfl) ⟨174272, by rfl⟩ : syracuseStep 232363 = 348545) B348545
theorem B232375 : Blo 231814 232375 := bstep (se 1 (by rfl) ⟨174281, by rfl⟩ : syracuseStep 232375 = 348563) B348563
theorem B232395 : Blo 231814 232395 := bstep (se 1 (by rfl) ⟨174296, by rfl⟩ : syracuseStep 232395 = 348593) B348593
theorem B232407 : Blo 231814 232407 := bstep (se 1 (by rfl) ⟨174305, by rfl⟩ : syracuseStep 232407 = 348611) B348611
theorem B232427 : Blo 231814 232427 := bstep (se 1 (by rfl) ⟨174320, by rfl⟩ : syracuseStep 232427 = 348641) B348641
theorem B232439 : Blo 231814 232439 := bstep (se 1 (by rfl) ⟨174329, by rfl⟩ : syracuseStep 232439 = 348659) B348659
theorem B265207 : Blo 231814 265207 := bstep (se 1 (by rfl) ⟨198905, by rfl⟩ : syracuseStep 265207 = 397811) B397811
theorem B232459 : Blo 231814 232459 := bstep (se 1 (by rfl) ⟨174344, by rfl⟩ : syracuseStep 232459 = 348689) B348689
theorem B396299 : Blo 231814 396299 := bstep (se 1 (by rfl) ⟨297224, by rfl⟩ : syracuseStep 396299 = 594449) B594449
theorem B232471 : Blo 231814 232471 := bstep (se 1 (by rfl) ⟨174353, by rfl⟩ : syracuseStep 232471 = 348707) B348707
theorem B887831 : Blo 231814 887831 := bstep (se 1 (by rfl) ⟨665873, by rfl⟩ : syracuseStep 887831 = 1331747) B1331747
theorem B232491 : Blo 231814 232491 := bstep (se 1 (by rfl) ⟨174368, by rfl⟩ : syracuseStep 232491 = 348737) B348737
theorem B232503 : Blo 231814 232503 := bstep (se 1 (by rfl) ⟨174377, by rfl⟩ : syracuseStep 232503 = 348755) B348755
theorem B232523 : Blo 231814 232523 := bstep (se 1 (by rfl) ⟨174392, by rfl⟩ : syracuseStep 232523 = 348785) B348785
theorem B2001995 : Blo 231814 2001995 := bstep (se 1 (by rfl) ⟨1501496, by rfl⟩ : syracuseStep 2001995 = 3002993) B3002993
theorem B527435 : Blo 231814 527435 := bstep (se 1 (by rfl) ⟨395576, by rfl⟩ : syracuseStep 527435 = 791153) B791153
theorem B232535 : Blo 231814 232535 := bstep (se 1 (by rfl) ⟨174401, by rfl⟩ : syracuseStep 232535 = 348803) B348803
theorem B330841 : Blo 231814 330841 := bstep (se 2 (by rfl) ⟨124065, by rfl⟩ : syracuseStep 330841 = 248131) B248131
theorem B232555 : Blo 231814 232555 := bstep (se 1 (by rfl) ⟨174416, by rfl⟩ : syracuseStep 232555 = 348833) B348833
theorem B232567 : Blo 231814 232567 := bstep (se 1 (by rfl) ⟨174425, by rfl⟩ : syracuseStep 232567 = 348851) B348851
theorem B527489 : Blo 231814 527489 := bstep (se 2 (by rfl) ⟨197808, by rfl⟩ : syracuseStep 527489 = 395617) B395617
theorem B232587 : Blo 231814 232587 := bstep (se 1 (by rfl) ⟨174440, by rfl⟩ : syracuseStep 232587 = 348881) B348881
theorem B396427 : Blo 231814 396427 := bstep (se 1 (by rfl) ⟨297320, by rfl⟩ : syracuseStep 396427 = 594641) B594641
theorem B232599 : Blo 231814 232599 := bstep (se 1 (by rfl) ⟨174449, by rfl⟩ : syracuseStep 232599 = 348899) B348899
theorem B232619 : Blo 231814 232619 := bstep (se 1 (by rfl) ⟨174464, by rfl⟩ : syracuseStep 232619 = 348929) B348929
theorem B232631 : Blo 231814 232631 := bstep (se 1 (by rfl) ⟨174473, by rfl⟩ : syracuseStep 232631 = 348947) B348947
theorem B232651 : Blo 231814 232651 := bstep (se 1 (by rfl) ⟨174488, by rfl⟩ : syracuseStep 232651 = 348977) B348977
theorem B232663 : Blo 231814 232663 := bstep (se 1 (by rfl) ⟨174497, by rfl⟩ : syracuseStep 232663 = 348995) B348995
theorem B888029 : Blo 231814 888029 := bstep (se 3 (by rfl) ⟨166505, by rfl⟩ : syracuseStep 888029 = 333011) B333011
theorem B232683 : Blo 231814 232683 := bstep (se 1 (by rfl) ⟨174512, by rfl⟩ : syracuseStep 232683 = 349025) B349025
theorem B232695 : Blo 231814 232695 := bstep (se 1 (by rfl) ⟨174521, by rfl⟩ : syracuseStep 232695 = 349043) B349043
theorem B232715 : Blo 231814 232715 := bstep (se 1 (by rfl) ⟨174536, by rfl⟩ : syracuseStep 232715 = 349073) B349073
theorem B265483 : Blo 231814 265483 := bstep (se 1 (by rfl) ⟨199112, by rfl⟩ : syracuseStep 265483 = 398225) B398225
theorem B232727 : Blo 231814 232727 := bstep (se 1 (by rfl) ⟨174545, by rfl⟩ : syracuseStep 232727 = 349091) B349091
theorem B396569 : Blo 231814 396569 := bstep (se 2 (by rfl) ⟨148713, by rfl⟩ : syracuseStep 396569 = 297427) B297427
theorem B232747 : Blo 231814 232747 := bstep (se 1 (by rfl) ⟨174560, by rfl⟩ : syracuseStep 232747 = 349121) B349121
theorem B593203 : Blo 231814 593203 := bstep (se 1 (by rfl) ⟨444902, by rfl⟩ : syracuseStep 593203 = 889805) B889805
theorem B232759 : Blo 231814 232759 := bstep (se 1 (by rfl) ⟨174569, by rfl⟩ : syracuseStep 232759 = 349139) B349139
theorem B232779 : Blo 231814 232779 := bstep (se 1 (by rfl) ⟨174584, by rfl⟩ : syracuseStep 232779 = 349169) B349169
theorem B232791 : Blo 231814 232791 := bstep (se 1 (by rfl) ⟨174593, by rfl⟩ : syracuseStep 232791 = 349187) B349187
theorem B527705 : Blo 231814 527705 := bstep (se 2 (by rfl) ⟨197889, by rfl⟩ : syracuseStep 527705 = 395779) B395779
theorem B232811 : Blo 231814 232811 := bstep (se 1 (by rfl) ⟨174608, by rfl⟩ : syracuseStep 232811 = 349217) B349217
theorem B232823 : Blo 231814 232823 := bstep (se 1 (by rfl) ⟨174617, by rfl⟩ : syracuseStep 232823 = 349235) B349235
theorem B232843 : Blo 231814 232843 := bstep (se 1 (by rfl) ⟨174632, by rfl⟩ : syracuseStep 232843 = 349265) B349265
theorem B232855 : Blo 231814 232855 := bstep (se 1 (by rfl) ⟨174641, by rfl⟩ : syracuseStep 232855 = 349283) B349283
theorem B789911 : Blo 231814 789911 := bstep (se 1 (by rfl) ⟨592433, by rfl⟩ : syracuseStep 789911 = 1184867) B1184867
theorem B396697 : Blo 231814 396697 := bstep (se 2 (by rfl) ⟨148761, by rfl⟩ : syracuseStep 396697 = 297523) B297523
theorem B232875 : Blo 231814 232875 := bstep (se 1 (by rfl) ⟨174656, by rfl⟩ : syracuseStep 232875 = 349313) B349313
theorem B527795 : Blo 231814 527795 := bstep (se 1 (by rfl) ⟨395846, by rfl⟩ : syracuseStep 527795 = 791693) B791693
theorem B232887 : Blo 231814 232887 := bstep (se 1 (by rfl) ⟨174665, by rfl⟩ : syracuseStep 232887 = 349331) B349331
theorem B593345 : Blo 231814 593345 := bstep (se 2 (by rfl) ⟨222504, by rfl⟩ : syracuseStep 593345 = 445009) B445009
theorem B232907 : Blo 231814 232907 := bstep (se 1 (by rfl) ⟨174680, by rfl⟩ : syracuseStep 232907 = 349361) B349361
theorem B232919 : Blo 231814 232919 := bstep (se 1 (by rfl) ⟨174689, by rfl⟩ : syracuseStep 232919 = 349379) B349379
theorem B527831 : Blo 231814 527831 := bstep (se 1 (by rfl) ⟨395873, by rfl⟩ : syracuseStep 527831 = 791747) B791747
theorem B232939 : Blo 231814 232939 := bstep (se 1 (by rfl) ⟨174704, by rfl⟩ : syracuseStep 232939 = 349409) B349409
theorem B232951 : Blo 231814 232951 := bstep (se 1 (by rfl) ⟨174713, by rfl⟩ : syracuseStep 232951 = 349427) B349427
theorem B232971 : Blo 231814 232971 := bstep (se 1 (by rfl) ⟨174728, by rfl⟩ : syracuseStep 232971 = 349457) B349457
theorem B232983 : Blo 231814 232983 := bstep (se 1 (by rfl) ⟨174737, by rfl⟩ : syracuseStep 232983 = 349475) B349475
theorem B233003 : Blo 231814 233003 := bstep (se 1 (by rfl) ⟨174752, by rfl⟩ : syracuseStep 233003 = 349505) B349505
theorem B233015 : Blo 231814 233015 := bstep (se 1 (by rfl) ⟨174761, by rfl⟩ : syracuseStep 233015 = 349523) B349523
theorem B233035 : Blo 231814 233035 := bstep (se 1 (by rfl) ⟨174776, by rfl⟩ : syracuseStep 233035 = 349553) B349553
theorem B233047 : Blo 231814 233047 := bstep (se 1 (by rfl) ⟨174785, by rfl⟩ : syracuseStep 233047 = 349571) B349571
theorem B233067 : Blo 231814 233067 := bstep (se 1 (by rfl) ⟨174800, by rfl⟩ : syracuseStep 233067 = 349601) B349601
theorem B233079 : Blo 231814 233079 := bstep (se 1 (by rfl) ⟨174809, by rfl⟩ : syracuseStep 233079 = 349619) B349619
theorem B233099 : Blo 231814 233099 := bstep (se 1 (by rfl) ⟨174824, by rfl⟩ : syracuseStep 233099 = 349649) B349649
theorem B528011 : Blo 231814 528011 := bstep (se 1 (by rfl) ⟨396008, by rfl⟩ : syracuseStep 528011 = 792017) B792017
theorem B233111 : Blo 231814 233111 := bstep (se 1 (by rfl) ⟨174833, by rfl⟩ : syracuseStep 233111 = 349667) B349667
theorem B233131 : Blo 231814 233131 := bstep (se 1 (by rfl) ⟨174848, by rfl⟩ : syracuseStep 233131 = 349697) B349697
theorem B233143 : Blo 231814 233143 := bstep (se 1 (by rfl) ⟨174857, by rfl⟩ : syracuseStep 233143 = 349715) B349715
theorem B528065 : Blo 231814 528065 := bstep (se 2 (by rfl) ⟨198024, by rfl⟩ : syracuseStep 528065 = 396049) B396049
theorem B233163 : Blo 231814 233163 := bstep (se 1 (by rfl) ⟨174872, by rfl⟩ : syracuseStep 233163 = 349745) B349745
theorem B233175 : Blo 231814 233175 := bstep (se 1 (by rfl) ⟨174881, by rfl⟩ : syracuseStep 233175 = 349763) B349763
theorem B233195 : Blo 231814 233195 := bstep (se 1 (by rfl) ⟨174896, by rfl⟩ : syracuseStep 233195 = 349793) B349793
theorem B233207 : Blo 231814 233207 := bstep (se 1 (by rfl) ⟨174905, by rfl⟩ : syracuseStep 233207 = 349811) B349811
theorem B233227 : Blo 231814 233227 := bstep (se 1 (by rfl) ⟨174920, by rfl⟩ : syracuseStep 233227 = 349841) B349841
theorem B233239 : Blo 231814 233239 := bstep (se 1 (by rfl) ⟨174929, by rfl⟩ : syracuseStep 233239 = 349859) B349859
theorem B233259 : Blo 231814 233259 := bstep (se 1 (by rfl) ⟨174944, by rfl⟩ : syracuseStep 233259 = 349889) B349889
theorem B233271 : Blo 231814 233271 := bstep (se 1 (by rfl) ⟨174953, by rfl⟩ : syracuseStep 233271 = 349907) B349907
theorem B1412939 : Blo 231814 1412939 := bstep (se 1 (by rfl) ⟨1059704, by rfl⟩ : syracuseStep 1412939 = 2119409) B2119409
theorem B233291 : Blo 231814 233291 := bstep (se 1 (by rfl) ⟨174968, by rfl⟩ : syracuseStep 233291 = 349937) B349937
theorem B233303 : Blo 231814 233303 := bstep (se 1 (by rfl) ⟨174977, by rfl⟩ : syracuseStep 233303 = 349955) B349955
theorem B10030949 : Blo 231814 10030949 := bstep (se 4 (by rfl) ⟨940401, by rfl⟩ : syracuseStep 10030949 = 1880803) B1880803
theorem B1773413 : Blo 231814 1773413 := bstep (se 4 (by rfl) ⟨166257, by rfl⟩ : syracuseStep 1773413 = 332515) B332515
theorem B1904485 : Blo 231814 1904485 := bstep (se 4 (by rfl) ⟨178545, by rfl⟩ : syracuseStep 1904485 = 357091) B357091
theorem B233323 : Blo 231814 233323 := bstep (se 1 (by rfl) ⟨174992, by rfl⟩ : syracuseStep 233323 = 349985) B349985
theorem B233335 : Blo 231814 233335 := bstep (se 1 (by rfl) ⟨175001, by rfl⟩ : syracuseStep 233335 = 350003) B350003
theorem B233355 : Blo 231814 233355 := bstep (se 1 (by rfl) ⟨175016, by rfl⟩ : syracuseStep 233355 = 350033) B350033
theorem B233367 : Blo 231814 233367 := bstep (se 1 (by rfl) ⟨175025, by rfl⟩ : syracuseStep 233367 = 350051) B350051
theorem B528281 : Blo 231814 528281 := bstep (se 2 (by rfl) ⟨198105, by rfl⟩ : syracuseStep 528281 = 396211) B396211
theorem B233387 : Blo 231814 233387 := bstep (se 1 (by rfl) ⟨175040, by rfl⟩ : syracuseStep 233387 = 350081) B350081
theorem B790451 : Blo 231814 790451 := bstep (se 1 (by rfl) ⟨592838, by rfl⟩ : syracuseStep 790451 = 1185677) B1185677
theorem B233399 : Blo 231814 233399 := bstep (se 1 (by rfl) ⟨175049, by rfl⟩ : syracuseStep 233399 = 350099) B350099
theorem B495553 : Blo 231814 495553 := bstep (se 2 (by rfl) ⟨185832, by rfl⟩ : syracuseStep 495553 = 371665) B371665
theorem B233419 : Blo 231814 233419 := bstep (se 1 (by rfl) ⟨175064, by rfl⟩ : syracuseStep 233419 = 350129) B350129
theorem B233431 : Blo 231814 233431 := bstep (se 1 (by rfl) ⟨175073, by rfl⟩ : syracuseStep 233431 = 350147) B350147
theorem B397271 : Blo 231814 397271 := bstep (se 1 (by rfl) ⟨297953, by rfl⟩ : syracuseStep 397271 = 595907) B595907
theorem B233451 : Blo 231814 233451 := bstep (se 1 (by rfl) ⟨175088, by rfl⟩ : syracuseStep 233451 = 350177) B350177
theorem B528371 : Blo 231814 528371 := bstep (se 1 (by rfl) ⟨396278, by rfl⟩ : syracuseStep 528371 = 792557) B792557
theorem B233463 : Blo 231814 233463 := bstep (se 1 (by rfl) ⟨175097, by rfl⟩ : syracuseStep 233463 = 350195) B350195
theorem B233483 : Blo 231814 233483 := bstep (se 1 (by rfl) ⟨175112, by rfl⟩ : syracuseStep 233483 = 350225) B350225
theorem B1118225 : Blo 231814 1118225 := bstep (se 2 (by rfl) ⟨419334, by rfl⟩ : syracuseStep 1118225 = 838669) B838669
theorem B233495 : Blo 231814 233495 := bstep (se 1 (by rfl) ⟨175121, by rfl⟩ : syracuseStep 233495 = 350243) B350243
theorem B528407 : Blo 231814 528407 := bstep (se 1 (by rfl) ⟨396305, by rfl⟩ : syracuseStep 528407 = 792611) B792611
theorem B233515 : Blo 231814 233515 := bstep (se 1 (by rfl) ⟨175136, by rfl⟩ : syracuseStep 233515 = 350273) B350273
theorem B233527 : Blo 231814 233527 := bstep (se 1 (by rfl) ⟨175145, by rfl⟩ : syracuseStep 233527 = 350291) B350291
theorem B233547 : Blo 231814 233547 := bstep (se 1 (by rfl) ⟨175160, by rfl⟩ : syracuseStep 233547 = 350321) B350321
theorem B233559 : Blo 231814 233559 := bstep (se 1 (by rfl) ⟨175169, by rfl⟩ : syracuseStep 233559 = 350339) B350339
theorem B397399 : Blo 231814 397399 := bstep (se 1 (by rfl) ⟨298049, by rfl⟩ : syracuseStep 397399 = 596099) B596099
theorem B233579 : Blo 231814 233579 := bstep (se 1 (by rfl) ⟨175184, by rfl⟩ : syracuseStep 233579 = 350369) B350369
theorem B233591 : Blo 231814 233591 := bstep (se 1 (by rfl) ⟨175193, by rfl⟩ : syracuseStep 233591 = 350387) B350387
theorem B233611 : Blo 231814 233611 := bstep (se 1 (by rfl) ⟨175208, by rfl⟩ : syracuseStep 233611 = 350417) B350417
theorem B233623 : Blo 231814 233623 := bstep (se 1 (by rfl) ⟨175217, by rfl⟩ : syracuseStep 233623 = 350435) B350435
theorem B1183895 : Blo 231814 1183895 := bstep (se 1 (by rfl) ⟨887921, by rfl⟩ : syracuseStep 1183895 = 1775843) B1775843
theorem B233643 : Blo 231814 233643 := bstep (se 1 (by rfl) ⟨175232, by rfl⟩ : syracuseStep 233643 = 350465) B350465
theorem B233655 : Blo 231814 233655 := bstep (se 1 (by rfl) ⟨175241, by rfl⟩ : syracuseStep 233655 = 350483) B350483
theorem B790721 : Blo 231814 790721 := bstep (se 2 (by rfl) ⟨296520, by rfl⟩ : syracuseStep 790721 = 593041) B593041
theorem B233675 : Blo 231814 233675 := bstep (se 1 (by rfl) ⟨175256, by rfl⟩ : syracuseStep 233675 = 350513) B350513
theorem B528587 : Blo 231814 528587 := bstep (se 1 (by rfl) ⟨396440, by rfl⟩ : syracuseStep 528587 = 792881) B792881
theorem B233687 : Blo 231814 233687 := bstep (se 1 (by rfl) ⟨175265, by rfl⟩ : syracuseStep 233687 = 350531) B350531
theorem B233707 : Blo 231814 233707 := bstep (se 1 (by rfl) ⟨175280, by rfl⟩ : syracuseStep 233707 = 350561) B350561
theorem B233719 : Blo 231814 233719 := bstep (se 1 (by rfl) ⟨175289, by rfl⟩ : syracuseStep 233719 = 350579) B350579
theorem B528641 : Blo 231814 528641 := bstep (se 2 (by rfl) ⟨198240, by rfl⟩ : syracuseStep 528641 = 396481) B396481
theorem B233739 : Blo 231814 233739 := bstep (se 1 (by rfl) ⟨175304, by rfl⟩ : syracuseStep 233739 = 350609) B350609
theorem B495895 : Blo 231814 495895 := bstep (se 1 (by rfl) ⟨371921, by rfl⟩ : syracuseStep 495895 = 743843) B743843
theorem B233751 : Blo 231814 233751 := bstep (se 1 (by rfl) ⟨175313, by rfl⟩ : syracuseStep 233751 = 350627) B350627
theorem B233771 : Blo 231814 233771 := bstep (se 1 (by rfl) ⟨175328, by rfl⟩ : syracuseStep 233771 = 350657) B350657
theorem B7180589 : Blo 231814 7180589 := bstep (se 3 (by rfl) ⟨1346360, by rfl⟩ : syracuseStep 7180589 = 2692721) B2692721
theorem B233783 : Blo 231814 233783 := bstep (se 1 (by rfl) ⟨175337, by rfl⟩ : syracuseStep 233783 = 350675) B350675
theorem B1773899 : Blo 231814 1773899 := bstep (se 1 (by rfl) ⟨1330424, by rfl⟩ : syracuseStep 1773899 = 2660849) B2660849
theorem B233803 : Blo 231814 233803 := bstep (se 1 (by rfl) ⟨175352, by rfl⟩ : syracuseStep 233803 = 350705) B350705
theorem B233815 : Blo 231814 233815 := bstep (se 1 (by rfl) ⟨175361, by rfl⟩ : syracuseStep 233815 = 350723) B350723
theorem B397657 : Blo 231814 397657 := bstep (se 2 (by rfl) ⟨149121, by rfl⟩ : syracuseStep 397657 = 298243) B298243
theorem B233835 : Blo 231814 233835 := bstep (se 1 (by rfl) ⟨175376, by rfl⟩ : syracuseStep 233835 = 350753) B350753
theorem B233847 : Blo 231814 233847 := bstep (se 1 (by rfl) ⟨175385, by rfl⟩ : syracuseStep 233847 = 350771) B350771
theorem B233867 : Blo 231814 233867 := bstep (se 1 (by rfl) ⟨175400, by rfl⟩ : syracuseStep 233867 = 350801) B350801
theorem B233879 : Blo 231814 233879 := bstep (se 1 (by rfl) ⟨175409, by rfl⟩ : syracuseStep 233879 = 350819) B350819
theorem B233899 : Blo 231814 233899 := bstep (se 1 (by rfl) ⟨175424, by rfl⟩ : syracuseStep 233899 = 350849) B350849
theorem B233911 : Blo 231814 233911 := bstep (se 1 (by rfl) ⟨175433, by rfl⟩ : syracuseStep 233911 = 350867) B350867
theorem B233931 : Blo 231814 233931 := bstep (se 1 (by rfl) ⟨175448, by rfl⟩ : syracuseStep 233931 = 350897) B350897
theorem B233943 : Blo 231814 233943 := bstep (se 1 (by rfl) ⟨175457, by rfl⟩ : syracuseStep 233943 = 350915) B350915
theorem B528857 : Blo 231814 528857 := bstep (se 2 (by rfl) ⟨198321, by rfl⟩ : syracuseStep 528857 = 396643) B396643
theorem B233963 : Blo 231814 233963 := bstep (se 1 (by rfl) ⟨175472, by rfl⟩ : syracuseStep 233963 = 350945) B350945
theorem B233975 : Blo 231814 233975 := bstep (se 1 (by rfl) ⟨175481, by rfl⟩ : syracuseStep 233975 = 350963) B350963
theorem B332299 : Blo 231814 332299 := bstep (se 1 (by rfl) ⟨249224, by rfl⟩ : syracuseStep 332299 = 498449) B498449
theorem B233995 : Blo 231814 233995 := bstep (se 1 (by rfl) ⟨175496, by rfl⟩ : syracuseStep 233995 = 350993) B350993
theorem B234007 : Blo 231814 234007 := bstep (se 1 (by rfl) ⟨175505, by rfl⟩ : syracuseStep 234007 = 351011) B351011
theorem B234027 : Blo 231814 234027 := bstep (se 1 (by rfl) ⟨175520, by rfl⟩ : syracuseStep 234027 = 351041) B351041
theorem B528947 : Blo 231814 528947 := bstep (se 1 (by rfl) ⟨396710, by rfl⟩ : syracuseStep 528947 = 793421) B793421
theorem B234039 : Blo 231814 234039 := bstep (se 1 (by rfl) ⟨175529, by rfl⟩ : syracuseStep 234039 = 351059) B351059
theorem B234059 : Blo 231814 234059 := bstep (se 1 (by rfl) ⟨175544, by rfl⟩ : syracuseStep 234059 = 351089) B351089
theorem B234071 : Blo 231814 234071 := bstep (se 1 (by rfl) ⟨175553, by rfl⟩ : syracuseStep 234071 = 351107) B351107
theorem B528983 : Blo 231814 528983 := bstep (se 1 (by rfl) ⟨396737, by rfl⟩ : syracuseStep 528983 = 793475) B793475
theorem B234091 : Blo 231814 234091 := bstep (se 1 (by rfl) ⟨175568, by rfl⟩ : syracuseStep 234091 = 351137) B351137
theorem B234103 : Blo 231814 234103 := bstep (se 1 (by rfl) ⟨175577, by rfl⟩ : syracuseStep 234103 = 351155) B351155
theorem B234123 : Blo 231814 234123 := bstep (se 1 (by rfl) ⟨175592, by rfl⟩ : syracuseStep 234123 = 351185) B351185
theorem B234135 : Blo 231814 234135 := bstep (se 1 (by rfl) ⟨175601, by rfl⟩ : syracuseStep 234135 = 351203) B351203
theorem B234155 : Blo 231814 234155 := bstep (se 1 (by rfl) ⟨175616, by rfl⟩ : syracuseStep 234155 = 351233) B351233
theorem B594611 : Blo 231814 594611 := bstep (se 1 (by rfl) ⟨445958, by rfl⟩ : syracuseStep 594611 = 891917) B891917
theorem B234167 : Blo 231814 234167 := bstep (se 1 (by rfl) ⟨175625, by rfl⟩ : syracuseStep 234167 = 351251) B351251
theorem B234187 : Blo 231814 234187 := bstep (se 1 (by rfl) ⟨175640, by rfl⟩ : syracuseStep 234187 = 351281) B351281
theorem B234199 : Blo 231814 234199 := bstep (se 1 (by rfl) ⟨175649, by rfl⟩ : syracuseStep 234199 = 351299) B351299
theorem B791261 : Blo 231814 791261 := bstep (se 3 (by rfl) ⟨148361, by rfl⟩ : syracuseStep 791261 = 296723) B296723
theorem B234219 : Blo 231814 234219 := bstep (se 1 (by rfl) ⟨175664, by rfl⟩ : syracuseStep 234219 = 351329) B351329
theorem B234231 : Blo 231814 234231 := bstep (se 1 (by rfl) ⟨175673, by rfl⟩ : syracuseStep 234231 = 351347) B351347
theorem B234251 : Blo 231814 234251 := bstep (se 1 (by rfl) ⟨175688, by rfl⟩ : syracuseStep 234251 = 351377) B351377
theorem B529163 : Blo 231814 529163 := bstep (se 1 (by rfl) ⟨396872, by rfl⟩ : syracuseStep 529163 = 793745) B793745
theorem B234263 : Blo 231814 234263 := bstep (se 1 (by rfl) ⟨175697, by rfl⟩ : syracuseStep 234263 = 351395) B351395
theorem B234283 : Blo 231814 234283 := bstep (se 1 (by rfl) ⟨175712, by rfl⟩ : syracuseStep 234283 = 351425) B351425
theorem B234295 : Blo 231814 234295 := bstep (se 1 (by rfl) ⟨175721, by rfl⟩ : syracuseStep 234295 = 351443) B351443
theorem B529217 : Blo 231814 529217 := bstep (se 2 (by rfl) ⟨198456, by rfl⟩ : syracuseStep 529217 = 396913) B396913
theorem B234315 : Blo 231814 234315 := bstep (se 1 (by rfl) ⟨175736, by rfl⟩ : syracuseStep 234315 = 351473) B351473
theorem B234327 : Blo 231814 234327 := bstep (se 1 (by rfl) ⟨175745, by rfl⟩ : syracuseStep 234327 = 351491) B351491
theorem B234347 : Blo 231814 234347 := bstep (se 1 (by rfl) ⟨175760, by rfl⟩ : syracuseStep 234347 = 351521) B351521
theorem B234359 : Blo 231814 234359 := bstep (se 1 (by rfl) ⟨175769, by rfl⟩ : syracuseStep 234359 = 351539) B351539
theorem B234379 : Blo 231814 234379 := bstep (se 1 (by rfl) ⟨175784, by rfl⟩ : syracuseStep 234379 = 351569) B351569
theorem B234391 : Blo 231814 234391 := bstep (se 1 (by rfl) ⟨175793, by rfl⟩ : syracuseStep 234391 = 351587) B351587
theorem B234411 : Blo 231814 234411 := bstep (se 1 (by rfl) ⟨175808, by rfl⟩ : syracuseStep 234411 = 351617) B351617
theorem B955309 : Blo 231814 955309 := bstep (se 3 (by rfl) ⟨179120, by rfl⟩ : syracuseStep 955309 = 358241) B358241
theorem B234423 : Blo 231814 234423 := bstep (se 1 (by rfl) ⟨175817, by rfl⟩ : syracuseStep 234423 = 351635) B351635
theorem B234443 : Blo 231814 234443 := bstep (se 1 (by rfl) ⟨175832, by rfl⟩ : syracuseStep 234443 = 351665) B351665
theorem B234455 : Blo 231814 234455 := bstep (se 1 (by rfl) ⟨175841, by rfl⟩ : syracuseStep 234455 = 351683) B351683
theorem B234475 : Blo 231814 234475 := bstep (se 1 (by rfl) ⟨175856, by rfl⟩ : syracuseStep 234475 = 351713) B351713
theorem B234487 : Blo 231814 234487 := bstep (se 1 (by rfl) ⟨175865, by rfl⟩ : syracuseStep 234487 = 351731) B351731
theorem B234507 : Blo 231814 234507 := bstep (se 1 (by rfl) ⟨175880, by rfl⟩ : syracuseStep 234507 = 351761) B351761
theorem B234519 : Blo 231814 234519 := bstep (se 1 (by rfl) ⟨175889, by rfl⟩ : syracuseStep 234519 = 351779) B351779
theorem B529433 : Blo 231814 529433 := bstep (se 2 (by rfl) ⟨198537, by rfl⟩ : syracuseStep 529433 = 397075) B397075
theorem B234539 : Blo 231814 234539 := bstep (se 1 (by rfl) ⟨175904, by rfl⟩ : syracuseStep 234539 = 351809) B351809
theorem B234551 : Blo 231814 234551 := bstep (se 1 (by rfl) ⟨175913, by rfl⟩ : syracuseStep 234551 = 351827) B351827
theorem B234571 : Blo 231814 234571 := bstep (se 1 (by rfl) ⟨175928, by rfl⟩ : syracuseStep 234571 = 351857) B351857
theorem B234583 : Blo 231814 234583 := bstep (se 1 (by rfl) ⟨175937, by rfl⟩ : syracuseStep 234583 = 351875) B351875
theorem B562265 : Blo 231814 562265 := bstep (se 2 (by rfl) ⟨210849, by rfl⟩ : syracuseStep 562265 = 421699) B421699
theorem B234603 : Blo 231814 234603 := bstep (se 1 (by rfl) ⟨175952, by rfl⟩ : syracuseStep 234603 = 351905) B351905
theorem B529523 : Blo 231814 529523 := bstep (se 1 (by rfl) ⟨397142, by rfl⟩ : syracuseStep 529523 = 794285) B794285
theorem B234615 : Blo 231814 234615 := bstep (se 1 (by rfl) ⟨175961, by rfl⟩ : syracuseStep 234615 = 351923) B351923
theorem B889987 : Blo 231814 889987 := bstep (se 1 (by rfl) ⟨667490, by rfl⟩ : syracuseStep 889987 = 1334981) B1334981
theorem B234635 : Blo 231814 234635 := bstep (se 1 (by rfl) ⟨175976, by rfl⟩ : syracuseStep 234635 = 351953) B351953
theorem B234647 : Blo 231814 234647 := bstep (se 1 (by rfl) ⟨175985, by rfl⟩ : syracuseStep 234647 = 351971) B351971
theorem B529559 : Blo 231814 529559 := bstep (se 1 (by rfl) ⟨397169, by rfl⟩ : syracuseStep 529559 = 794339) B794339
theorem B234667 : Blo 231814 234667 := bstep (se 1 (by rfl) ⟨176000, by rfl⟩ : syracuseStep 234667 = 352001) B352001
theorem B234679 : Blo 231814 234679 := bstep (se 1 (by rfl) ⟨176009, by rfl⟩ : syracuseStep 234679 = 352019) B352019
theorem B595147 : Blo 231814 595147 := bstep (se 1 (by rfl) ⟨446360, by rfl⟩ : syracuseStep 595147 = 892721) B892721
theorem B234699 : Blo 231814 234699 := bstep (se 1 (by rfl) ⟨176024, by rfl⟩ : syracuseStep 234699 = 352049) B352049
theorem B234711 : Blo 231814 234711 := bstep (se 1 (by rfl) ⟨176033, by rfl⟩ : syracuseStep 234711 = 352067) B352067
theorem B529625 : Blo 231814 529625 := bstep (se 2 (by rfl) ⟨198609, by rfl⟩ : syracuseStep 529625 = 397219) B397219
theorem B234731 : Blo 231814 234731 := bstep (se 1 (by rfl) ⟨176048, by rfl⟩ : syracuseStep 234731 = 352097) B352097
theorem B234743 : Blo 231814 234743 := bstep (se 1 (by rfl) ⟨176057, by rfl⟩ : syracuseStep 234743 = 352115) B352115
theorem B234763 : Blo 231814 234763 := bstep (se 1 (by rfl) ⟨176072, by rfl⟩ : syracuseStep 234763 = 352145) B352145
theorem B234775 : Blo 231814 234775 := bstep (se 1 (by rfl) ⟨176081, by rfl⟩ : syracuseStep 234775 = 352163) B352163
theorem B234795 : Blo 231814 234795 := bstep (se 1 (by rfl) ⟨176096, by rfl⟩ : syracuseStep 234795 = 352193) B352193
theorem B234807 : Blo 231814 234807 := bstep (se 1 (by rfl) ⟨176105, by rfl⟩ : syracuseStep 234807 = 352211) B352211
theorem B234827 : Blo 231814 234827 := bstep (se 1 (by rfl) ⟨176120, by rfl⟩ : syracuseStep 234827 = 352241) B352241
theorem B529739 : Blo 231814 529739 := bstep (se 1 (by rfl) ⟨397304, by rfl⟩ : syracuseStep 529739 = 794609) B794609
theorem B234839 : Blo 231814 234839 := bstep (se 1 (by rfl) ⟨176129, by rfl⟩ : syracuseStep 234839 = 352259) B352259
theorem B595289 : Blo 231814 595289 := bstep (se 2 (by rfl) ⟨223233, by rfl⟩ : syracuseStep 595289 = 446467) B446467
theorem B1676645 : Blo 231814 1676645 := bstep (se 4 (by rfl) ⟨157185, by rfl⟩ : syracuseStep 1676645 = 314371) B314371
theorem B234859 : Blo 231814 234859 := bstep (se 1 (by rfl) ⟨176144, by rfl⟩ : syracuseStep 234859 = 352289) B352289
theorem B234871 : Blo 231814 234871 := bstep (se 1 (by rfl) ⟨176153, by rfl⟩ : syracuseStep 234871 = 352307) B352307
theorem B529793 : Blo 231814 529793 := bstep (se 2 (by rfl) ⟨198672, by rfl⟩ : syracuseStep 529793 = 397345) B397345
theorem B234891 : Blo 231814 234891 := bstep (se 1 (by rfl) ⟨176168, by rfl⟩ : syracuseStep 234891 = 352337) B352337
theorem B234903 : Blo 231814 234903 := bstep (se 1 (by rfl) ⟨176177, by rfl⟩ : syracuseStep 234903 = 352355) B352355
theorem B234923 : Blo 231814 234923 := bstep (se 1 (by rfl) ⟨176192, by rfl⟩ : syracuseStep 234923 = 352385) B352385
theorem B890291 : Blo 231814 890291 := bstep (se 1 (by rfl) ⟨667718, by rfl⟩ : syracuseStep 890291 = 1335437) B1335437
theorem B234935 : Blo 231814 234935 := bstep (se 1 (by rfl) ⟨176201, by rfl⟩ : syracuseStep 234935 = 352403) B352403
theorem B497099 : Blo 231814 497099 := bstep (se 1 (by rfl) ⟨372824, by rfl⟩ : syracuseStep 497099 = 745649) B745649
theorem B234955 : Blo 231814 234955 := bstep (se 1 (by rfl) ⟨176216, by rfl⟩ : syracuseStep 234955 = 352433) B352433
theorem B234967 : Blo 231814 234967 := bstep (se 1 (by rfl) ⟨176225, by rfl⟩ : syracuseStep 234967 = 352451) B352451
theorem B660953 : Blo 231814 660953 := bstep (se 2 (by rfl) ⟨247857, by rfl⟩ : syracuseStep 660953 = 495715) B495715
theorem B234987 : Blo 231814 234987 := bstep (se 1 (by rfl) ⟨176240, by rfl⟩ : syracuseStep 234987 = 352481) B352481
theorem B234999 : Blo 231814 234999 := bstep (se 1 (by rfl) ⟨176249, by rfl⟩ : syracuseStep 234999 = 352499) B352499
theorem B235019 : Blo 231814 235019 := bstep (se 1 (by rfl) ⟨176264, by rfl⟩ : syracuseStep 235019 = 352529) B352529
theorem B235031 : Blo 231814 235031 := bstep (se 1 (by rfl) ⟨176273, by rfl⟩ : syracuseStep 235031 = 352547) B352547
theorem B235051 : Blo 231814 235051 := bstep (se 1 (by rfl) ⟨176288, by rfl⟩ : syracuseStep 235051 = 352577) B352577
theorem B235063 : Blo 231814 235063 := bstep (se 1 (by rfl) ⟨176297, by rfl⟩ : syracuseStep 235063 = 352595) B352595
theorem B661067 : Blo 231814 661067 := bstep (se 1 (by rfl) ⟨495800, by rfl⟩ : syracuseStep 661067 = 991601) B991601
theorem B235083 : Blo 231814 235083 := bstep (se 1 (by rfl) ⟨176312, by rfl⟩ : syracuseStep 235083 = 352625) B352625
theorem B235095 : Blo 231814 235095 := bstep (se 1 (by rfl) ⟨176321, by rfl⟩ : syracuseStep 235095 = 352643) B352643
theorem B530009 : Blo 231814 530009 := bstep (se 2 (by rfl) ⟨198753, by rfl⟩ : syracuseStep 530009 = 397507) B397507
theorem B235115 : Blo 231814 235115 := bstep (se 1 (by rfl) ⟨176336, by rfl⟩ : syracuseStep 235115 = 352673) B352673
theorem B235127 : Blo 231814 235127 := bstep (se 1 (by rfl) ⟨176345, by rfl⟩ : syracuseStep 235127 = 352691) B352691
theorem B235147 : Blo 231814 235147 := bstep (se 1 (by rfl) ⟨176360, by rfl⟩ : syracuseStep 235147 = 352721) B352721
theorem B235159 : Blo 231814 235159 := bstep (se 1 (by rfl) ⟨176369, by rfl⟩ : syracuseStep 235159 = 352739) B352739
theorem B235179 : Blo 231814 235179 := bstep (se 1 (by rfl) ⟨176384, by rfl⟩ : syracuseStep 235179 = 352769) B352769
theorem B2004659 : Blo 231814 2004659 := bstep (se 1 (by rfl) ⟨1503494, by rfl⟩ : syracuseStep 2004659 = 3006989) B3006989
theorem B530099 : Blo 231814 530099 := bstep (se 1 (by rfl) ⟨397574, by rfl⟩ : syracuseStep 530099 = 795149) B795149
theorem B235191 : Blo 231814 235191 := bstep (se 1 (by rfl) ⟨176393, by rfl⟩ : syracuseStep 235191 = 352787) B352787
theorem B235211 : Blo 231814 235211 := bstep (se 1 (by rfl) ⟨176408, by rfl⟩ : syracuseStep 235211 = 352817) B352817
theorem B235223 : Blo 231814 235223 := bstep (se 1 (by rfl) ⟨176417, by rfl⟩ : syracuseStep 235223 = 352835) B352835
theorem B530135 : Blo 231814 530135 := bstep (se 1 (by rfl) ⟨397601, by rfl⟩ : syracuseStep 530135 = 795203) B795203
theorem B235243 : Blo 231814 235243 := bstep (se 1 (by rfl) ⟨176432, by rfl⟩ : syracuseStep 235243 = 352865) B352865
theorem B235255 : Blo 231814 235255 := bstep (se 1 (by rfl) ⟨176441, by rfl⟩ : syracuseStep 235255 = 352883) B352883
theorem B235275 : Blo 231814 235275 := bstep (se 1 (by rfl) ⟨176456, by rfl⟩ : syracuseStep 235275 = 352913) B352913
theorem B2037521 : Blo 231814 2037521 := bstep (se 2 (by rfl) ⟨764070, by rfl⟩ : syracuseStep 2037521 = 1528141) B1528141
theorem B235287 : Blo 231814 235287 := bstep (se 1 (by rfl) ⟨176465, by rfl⟩ : syracuseStep 235287 = 352931) B352931
theorem B235307 : Blo 231814 235307 := bstep (se 1 (by rfl) ⟨176480, by rfl⟩ : syracuseStep 235307 = 352961) B352961
theorem B235319 : Blo 231814 235319 := bstep (se 1 (by rfl) ⟨176489, by rfl⟩ : syracuseStep 235319 = 352979) B352979
theorem B300875 : Blo 231814 300875 := bstep (se 1 (by rfl) ⟨225656, by rfl⟩ : syracuseStep 300875 = 451313) B451313
theorem B792395 : Blo 231814 792395 := bstep (se 1 (by rfl) ⟨594296, by rfl⟩ : syracuseStep 792395 = 1188593) B1188593
theorem B235339 : Blo 231814 235339 := bstep (se 1 (by rfl) ⟨176504, by rfl⟩ : syracuseStep 235339 = 353009) B353009
theorem B235351 : Blo 231814 235351 := bstep (se 1 (by rfl) ⟨176513, by rfl⟩ : syracuseStep 235351 = 353027) B353027
theorem B235371 : Blo 231814 235371 := bstep (se 1 (by rfl) ⟨176528, by rfl⟩ : syracuseStep 235371 = 353057) B353057
theorem B235383 : Blo 231814 235383 := bstep (se 1 (by rfl) ⟨176537, by rfl⟩ : syracuseStep 235383 = 353075) B353075
theorem B235403 : Blo 231814 235403 := bstep (se 1 (by rfl) ⟨176552, by rfl⟩ : syracuseStep 235403 = 353105) B353105
theorem B530315 : Blo 231814 530315 := bstep (se 1 (by rfl) ⟨397736, by rfl⟩ : syracuseStep 530315 = 795473) B795473
theorem B235415 : Blo 231814 235415 := bstep (se 1 (by rfl) ⟨176561, by rfl⟩ : syracuseStep 235415 = 353123) B353123
theorem B235435 : Blo 231814 235435 := bstep (se 1 (by rfl) ⟨176576, by rfl⟩ : syracuseStep 235435 = 353153) B353153
theorem B235447 : Blo 231814 235447 := bstep (se 1 (by rfl) ⟨176585, by rfl⟩ : syracuseStep 235447 = 353171) B353171
theorem B530369 : Blo 231814 530369 := bstep (se 2 (by rfl) ⟨198888, by rfl⟩ : syracuseStep 530369 = 397777) B397777
theorem B497611 : Blo 231814 497611 := bstep (se 1 (by rfl) ⟨373208, by rfl⟩ : syracuseStep 497611 = 746417) B746417
theorem B235467 : Blo 231814 235467 := bstep (se 1 (by rfl) ⟨176600, by rfl⟩ : syracuseStep 235467 = 353201) B353201
theorem B235479 : Blo 231814 235479 := bstep (se 1 (by rfl) ⟨176609, by rfl⟩ : syracuseStep 235479 = 353219) B353219
theorem B759773 : Blo 231814 759773 := bstep (se 3 (by rfl) ⟨142457, by rfl⟩ : syracuseStep 759773 = 284915) B284915
theorem B235499 : Blo 231814 235499 := bstep (se 1 (by rfl) ⟨176624, by rfl⟩ : syracuseStep 235499 = 353249) B353249
theorem B235511 : Blo 231814 235511 := bstep (se 1 (by rfl) ⟨176633, by rfl⟩ : syracuseStep 235511 = 353267) B353267
theorem B235531 : Blo 231814 235531 := bstep (se 1 (by rfl) ⟨176648, by rfl⟩ : syracuseStep 235531 = 353297) B353297
theorem B235543 : Blo 231814 235543 := bstep (se 1 (by rfl) ⟨176657, by rfl⟩ : syracuseStep 235543 = 353315) B353315
theorem B235563 : Blo 231814 235563 := bstep (se 1 (by rfl) ⟨176672, by rfl⟩ : syracuseStep 235563 = 353345) B353345
theorem B235575 : Blo 231814 235575 := bstep (se 1 (by rfl) ⟨176681, by rfl⟩ : syracuseStep 235575 = 353363) B353363
theorem B890945 : Blo 231814 890945 := bstep (se 2 (by rfl) ⟨334104, by rfl⟩ : syracuseStep 890945 = 668209) B668209
theorem B1906753 : Blo 231814 1906753 := bstep (se 2 (by rfl) ⟨715032, by rfl⟩ : syracuseStep 1906753 = 1430065) B1430065
theorem B235595 : Blo 231814 235595 := bstep (se 1 (by rfl) ⟨176696, by rfl⟩ : syracuseStep 235595 = 353393) B353393
theorem B235607 : Blo 231814 235607 := bstep (se 1 (by rfl) ⟨176705, by rfl⟩ : syracuseStep 235607 = 353411) B353411
theorem B792665 : Blo 231814 792665 := bstep (se 2 (by rfl) ⟨297249, by rfl⟩ : syracuseStep 792665 = 594499) B594499
theorem B235627 : Blo 231814 235627 := bstep (se 1 (by rfl) ⟨176720, by rfl⟩ : syracuseStep 235627 = 353441) B353441
theorem B235639 : Blo 231814 235639 := bstep (se 1 (by rfl) ⟨176729, by rfl⟩ : syracuseStep 235639 = 353459) B353459
theorem B235659 : Blo 231814 235659 := bstep (se 1 (by rfl) ⟨176744, by rfl⟩ : syracuseStep 235659 = 353489) B353489
theorem B596119 : Blo 231814 596119 := bstep (se 1 (by rfl) ⟨447089, by rfl⟩ : syracuseStep 596119 = 894179) B894179
theorem B235671 : Blo 231814 235671 := bstep (se 1 (by rfl) ⟨176753, by rfl⟩ : syracuseStep 235671 = 353507) B353507
theorem B235691 : Blo 231814 235691 := bstep (se 1 (by rfl) ⟨176768, by rfl⟩ : syracuseStep 235691 = 353537) B353537
theorem B235703 : Blo 231814 235703 := bstep (se 1 (by rfl) ⟨176777, by rfl⟩ : syracuseStep 235703 = 353555) B353555
theorem B235723 : Blo 231814 235723 := bstep (se 1 (by rfl) ⟨176792, by rfl⟩ : syracuseStep 235723 = 353585) B353585
theorem B235735 : Blo 231814 235735 := bstep (se 1 (by rfl) ⟨176801, by rfl⟩ : syracuseStep 235735 = 353603) B353603
theorem B235755 : Blo 231814 235755 := bstep (se 1 (by rfl) ⟨176816, by rfl⟩ : syracuseStep 235755 = 353633) B353633
theorem B235767 : Blo 231814 235767 := bstep (se 1 (by rfl) ⟨176825, by rfl⟩ : syracuseStep 235767 = 353651) B353651
theorem B235787 : Blo 231814 235787 := bstep (se 1 (by rfl) ⟨176840, by rfl⟩ : syracuseStep 235787 = 353681) B353681
theorem B235799 : Blo 231814 235799 := bstep (se 1 (by rfl) ⟨176849, by rfl⟩ : syracuseStep 235799 = 353699) B353699
theorem B596555 : Blo 231814 596555 := bstep (se 1 (by rfl) ⟨447416, by rfl⟩ : syracuseStep 596555 = 894833) B894833
theorem B498329 : Blo 231814 498329 := bstep (se 2 (by rfl) ⟨186873, by rfl⟩ : syracuseStep 498329 = 373747) B373747
theorem B662195 : Blo 231814 662195 := bstep (se 1 (by rfl) ⟨496646, by rfl⟩ : syracuseStep 662195 = 993293) B993293
theorem B2005721 : Blo 231814 2005721 := bstep (se 2 (by rfl) ⟨752145, by rfl⟩ : syracuseStep 2005721 = 1504291) B1504291
theorem B793367 : Blo 231814 793367 := bstep (se 1 (by rfl) ⟨595025, by rfl⟩ : syracuseStep 793367 = 1190051) B1190051
theorem B3873581 : Blo 231814 3873581 := bstep (se 3 (by rfl) ⟨726296, by rfl⟩ : syracuseStep 3873581 = 1452593) B1452593
theorem B498739 : Blo 231814 498739 := bstep (se 1 (by rfl) ⟨374054, by rfl⟩ : syracuseStep 498739 = 748109) B748109
theorem B662593 : Blo 231814 662593 := bstep (se 2 (by rfl) ⟨248472, by rfl⟩ : syracuseStep 662593 = 496945) B496945
theorem B990301 : Blo 231814 990301 := bstep (se 3 (by rfl) ⟨185681, by rfl⟩ : syracuseStep 990301 = 371363) B371363
theorem B302231 : Blo 231814 302231 := bstep (se 1 (by rfl) ⟨226673, by rfl⟩ : syracuseStep 302231 = 453347) B453347
theorem B892205 : Blo 231814 892205 := bstep (se 3 (by rfl) ⟨167288, by rfl⟩ : syracuseStep 892205 = 334577) B334577
theorem B793907 : Blo 231814 793907 := bstep (se 1 (by rfl) ⟨595430, by rfl⟩ : syracuseStep 793907 = 1190861) B1190861
theorem B892235 : Blo 231814 892235 := bstep (se 1 (by rfl) ⟨669176, by rfl⟩ : syracuseStep 892235 = 1338353) B1338353
theorem B990643 : Blo 231814 990643 := bstep (se 1 (by rfl) ⟨742982, by rfl⟩ : syracuseStep 990643 = 1485965) B1485965
theorem B794177 : Blo 231814 794177 := bstep (se 2 (by rfl) ⟨297816, by rfl⟩ : syracuseStep 794177 = 595633) B595633
theorem B1187459 : Blo 231814 1187459 := bstep (se 1 (by rfl) ⟨890594, by rfl⟩ : syracuseStep 1187459 = 1781189) B1781189
theorem B4595555 : Blo 231814 4595555 := bstep (se 1 (by rfl) ⟨3446666, by rfl⟩ : syracuseStep 4595555 = 6893333) B6893333
theorem B892889 : Blo 231814 892889 := bstep (se 2 (by rfl) ⟨334833, by rfl⟩ : syracuseStep 892889 = 669667) B669667
theorem B794717 : Blo 231814 794717 := bstep (se 3 (by rfl) ⟨149009, by rfl⟩ : syracuseStep 794717 = 298019) B298019
theorem B499927 : Blo 231814 499927 := bstep (se 1 (by rfl) ⟨374945, by rfl⟩ : syracuseStep 499927 = 749891) B749891
theorem B499969 : Blo 231814 499969 := bstep (se 2 (by rfl) ⟨187488, by rfl⟩ : syracuseStep 499969 = 374977) B374977
theorem B893207 : Blo 231814 893207 := bstep (se 1 (by rfl) ⟨669905, by rfl⟩ : syracuseStep 893207 = 1339811) B1339811
theorem B565579 : Blo 231814 565579 := bstep (se 1 (by rfl) ⟨424184, by rfl⟩ : syracuseStep 565579 = 848369) B848369
theorem B532993 : Blo 231814 532993 := bstep (se 2 (by rfl) ⟨199872, by rfl⟩ : syracuseStep 532993 = 399745) B399745
theorem B565811 : Blo 231814 565811 := bstep (se 1 (by rfl) ⟨424358, by rfl⟩ : syracuseStep 565811 = 848717) B848717
theorem B795329 : Blo 231814 795329 := bstep (se 2 (by rfl) ⟨298248, by rfl⟩ : syracuseStep 795329 = 596497) B596497
theorem B893875 : Blo 231814 893875 := bstep (se 1 (by rfl) ⟨670406, by rfl⟩ : syracuseStep 893875 = 1340813) B1340813
theorem B795851 : Blo 231814 795851 := bstep (se 1 (by rfl) ⟨596888, by rfl⟩ : syracuseStep 795851 = 1193777) B1193777
theorem B238999 : Blo 231814 238999 := bstep (se 1 (by rfl) ⟨179249, by rfl⟩ : syracuseStep 238999 = 358499) B358499
theorem B665111 : Blo 231814 665111 := bstep (se 1 (by rfl) ⟨498833, by rfl⟩ : syracuseStep 665111 = 997667) B997667
theorem B1779245 : Blo 231814 1779245 := bstep (se 3 (by rfl) ⟨333608, by rfl⟩ : syracuseStep 1779245 = 667217) B667217
theorem B403033 : Blo 231814 403033 := bstep (se 2 (by rfl) ⟨151137, by rfl⟩ : syracuseStep 403033 = 302275) B302275
theorem B501643 : Blo 231814 501643 := bstep (se 1 (by rfl) ⟨376232, by rfl⟩ : syracuseStep 501643 = 752465) B752465
theorem B337943 : Blo 231814 337943 := bstep (se 1 (by rfl) ⟨253457, by rfl⟩ : syracuseStep 337943 = 506915) B506915
theorem B895121 : Blo 231814 895121 := bstep (se 2 (by rfl) ⟨335670, by rfl⟩ : syracuseStep 895121 = 671341) B671341
theorem B633035 : Blo 231814 633035 := bstep (se 1 (by rfl) ⟨474776, by rfl⟩ : syracuseStep 633035 = 949553) B949553
theorem B501977 : Blo 231814 501977 := bstep (se 2 (by rfl) ⟨188241, by rfl⟩ : syracuseStep 501977 = 376483) B376483
theorem B469271 : Blo 231814 469271 := bstep (se 1 (by rfl) ⟨351953, by rfl⟩ : syracuseStep 469271 = 703907) B703907
theorem B3352877 : Blo 231814 3352877 := bstep (se 3 (by rfl) ⟨628664, by rfl⟩ : syracuseStep 3352877 = 1257329) B1257329
theorem B1812887 : Blo 231814 1812887 := bstep (se 1 (by rfl) ⟨1359665, by rfl⟩ : syracuseStep 1812887 = 2719331) B2719331
theorem B535027 : Blo 231814 535027 := bstep (se 1 (by rfl) ⟨401270, by rfl⟩ : syracuseStep 535027 = 802541) B802541
theorem B1813265 : Blo 231814 1813265 := bstep (se 2 (by rfl) ⟨679974, by rfl⟩ : syracuseStep 1813265 = 1359949) B1359949
theorem B371479 : Blo 231814 371479 := bstep (se 1 (by rfl) ⟨278609, by rfl⟩ : syracuseStep 371479 = 557219) B557219
theorem B666443 : Blo 231814 666443 := bstep (se 1 (by rfl) ⟨499832, by rfl⟩ : syracuseStep 666443 = 999665) B999665
theorem B1321859 : Blo 231814 1321859 := bstep (se 1 (by rfl) ⟨991394, by rfl⟩ : syracuseStep 1321859 = 1982789) B1982789
theorem B535511 : Blo 231814 535511 := bstep (se 1 (by rfl) ⟨401633, by rfl⟩ : syracuseStep 535511 = 803267) B803267
theorem B994265 : Blo 231814 994265 := bstep (se 2 (by rfl) ⟨372849, by rfl⟩ : syracuseStep 994265 = 745699) B745699
theorem B4041859 : Blo 231814 4041859 := bstep (se 1 (by rfl) ⟨3031394, by rfl⟩ : syracuseStep 4041859 = 6062789) B6062789
theorem B2141315 : Blo 231814 2141315 := bstep (se 1 (by rfl) ⟨1605986, by rfl⟩ : syracuseStep 2141315 = 3211973) B3211973
theorem B1191185 : Blo 231814 1191185 := bstep (se 2 (by rfl) ⟨446694, by rfl⟩ : syracuseStep 1191185 = 893389) B893389
theorem B1322315 : Blo 231814 1322315 := bstep (se 1 (by rfl) ⟨991736, by rfl⟩ : syracuseStep 1322315 = 1983473) B1983473
theorem B372043 : Blo 231814 372043 := bstep (se 1 (by rfl) ⟨279032, by rfl⟩ : syracuseStep 372043 = 558065) B558065
theorem B896345 : Blo 231814 896345 := bstep (se 2 (by rfl) ⟨336129, by rfl⟩ : syracuseStep 896345 = 672259) B672259
theorem B372107 : Blo 231814 372107 := bstep (se 1 (by rfl) ⟨279080, by rfl⟩ : syracuseStep 372107 = 558161) B558161
theorem B1191347 : Blo 231814 1191347 := bstep (se 1 (by rfl) ⟨893510, by rfl⟩ : syracuseStep 1191347 = 1787021) B1787021
theorem B634547 : Blo 231814 634547 := bstep (se 1 (by rfl) ⟨475910, by rfl⟩ : syracuseStep 634547 = 951821) B951821
theorem B503489 : Blo 231814 503489 := bstep (se 2 (by rfl) ⟨188808, by rfl⟩ : syracuseStep 503489 = 377617) B377617
theorem B1126237 : Blo 231814 1126237 := bstep (se 3 (by rfl) ⟨211169, by rfl⟩ : syracuseStep 1126237 = 422339) B422339
theorem B1814489 : Blo 231814 1814489 := bstep (se 2 (by rfl) ⟨680433, by rfl⟩ : syracuseStep 1814489 = 1360867) B1360867
theorem B2535725 : Blo 231814 2535725 := bstep (se 3 (by rfl) ⟨475448, by rfl⟩ : syracuseStep 2535725 = 950897) B950897
theorem B373081 : Blo 231814 373081 := bstep (se 2 (by rfl) ⟨139905, by rfl⟩ : syracuseStep 373081 = 279811) B279811
theorem B2011493 : Blo 231814 2011493 := bstep (se 4 (by rfl) ⟨188577, by rfl⟩ : syracuseStep 2011493 = 377155) B377155
theorem B2240945 : Blo 231814 2240945 := bstep (se 2 (by rfl) ⟨840354, by rfl⟩ : syracuseStep 2240945 = 1680709) B1680709
theorem B668083 : Blo 231814 668083 := bstep (se 1 (by rfl) ⟨501062, by rfl⟩ : syracuseStep 668083 = 1002125) B1002125
theorem B995905 : Blo 231814 995905 := bstep (se 2 (by rfl) ⟨373464, by rfl⟩ : syracuseStep 995905 = 746929) B746929
theorem B373337 : Blo 231814 373337 := bstep (se 2 (by rfl) ⟨140001, by rfl⟩ : syracuseStep 373337 = 280003) B280003
theorem B2994893 : Blo 231814 2994893 := bstep (se 3 (by rfl) ⟨561542, by rfl⟩ : syracuseStep 2994893 = 1123085) B1123085
theorem B635671 : Blo 231814 635671 := bstep (se 1 (by rfl) ⟨476753, by rfl⟩ : syracuseStep 635671 = 953507) B953507
theorem B373529 : Blo 231814 373529 := bstep (se 2 (by rfl) ⟨140073, by rfl⟩ : syracuseStep 373529 = 280147) B280147
theorem B2831435 : Blo 231814 2831435 := bstep (se 1 (by rfl) ⟨2123576, by rfl⟩ : syracuseStep 2831435 = 4247153) B4247153
theorem B1160513 : Blo 231814 1160513 := bstep (se 2 (by rfl) ⟨435192, by rfl⟩ : syracuseStep 1160513 = 870385) B870385
theorem B1193291 : Blo 231814 1193291 := bstep (se 1 (by rfl) ⟨894968, by rfl⟩ : syracuseStep 1193291 = 1789937) B1789937
theorem B1783133 : Blo 231814 1783133 := bstep (se 3 (by rfl) ⟨334337, by rfl⟩ : syracuseStep 1783133 = 668675) B668675
theorem B669131 : Blo 231814 669131 := bstep (se 1 (by rfl) ⟨501848, by rfl⟩ : syracuseStep 669131 = 1003697) B1003697
theorem B865753 : Blo 231814 865753 := bstep (se 2 (by rfl) ⟨324657, by rfl⟩ : syracuseStep 865753 = 649315) B649315
theorem B2013133 : Blo 231814 2013133 := bstep (se 3 (by rfl) ⟨377462, by rfl⟩ : syracuseStep 2013133 = 754925) B754925
theorem B997393 : Blo 231814 997393 := bstep (se 2 (by rfl) ⟨374022, by rfl⟩ : syracuseStep 997393 = 748045) B748045
theorem B440407 : Blo 231814 440407 := bstep (se 1 (by rfl) ⟨330305, by rfl⟩ : syracuseStep 440407 = 660611) B660611
theorem B441227 : Blo 231814 441227 := bstep (se 1 (by rfl) ⟨330920, by rfl⟩ : syracuseStep 441227 = 661841) B661841
theorem B441281 : Blo 231814 441281 := bstep (se 2 (by rfl) ⟨165480, by rfl⟩ : syracuseStep 441281 = 330961) B330961
theorem B670771 : Blo 231814 670771 := bstep (se 1 (by rfl) ⟨503078, by rfl⟩ : syracuseStep 670771 = 1006157) B1006157
theorem B2014469 : Blo 231814 2014469 := bstep (se 4 (by rfl) ⟨188856, by rfl⟩ : syracuseStep 2014469 = 377713) B377713
theorem B1064215 : Blo 231814 1064215 := bstep (se 1 (by rfl) ⟨798161, by rfl⟩ : syracuseStep 1064215 = 1596323) B1596323
theorem B670999 : Blo 231814 670999 := bstep (se 1 (by rfl) ⟨503249, by rfl⟩ : syracuseStep 670999 = 1006499) B1006499
theorem B671453 : Blo 231814 671453 := bstep (se 3 (by rfl) ⟨125897, by rfl⟩ : syracuseStep 671453 = 251795) B251795
theorem B442199 : Blo 231814 442199 := bstep (se 1 (by rfl) ⟨331649, by rfl⟩ : syracuseStep 442199 = 663299) B663299
theorem B1326941 : Blo 231814 1326941 := bstep (se 3 (by rfl) ⟨248801, by rfl⟩ : syracuseStep 1326941 = 497603) B497603
theorem B2146265 : Blo 231814 2146265 := bstep (se 2 (by rfl) ⟨804849, by rfl⟩ : syracuseStep 2146265 = 1609699) B1609699
theorem B3653707 : Blo 231814 3653707 := bstep (se 1 (by rfl) ⟨2740280, by rfl⟩ : syracuseStep 3653707 = 5480561) B5480561
theorem B442739 : Blo 231814 442739 := bstep (se 1 (by rfl) ⟨332054, by rfl⟩ : syracuseStep 442739 = 664109) B664109
theorem B377303 : Blo 231814 377303 := bstep (se 1 (by rfl) ⟨282977, by rfl⟩ : syracuseStep 377303 = 565955) B565955
theorem B1327691 : Blo 231814 1327691 := bstep (se 1 (by rfl) ⟨995768, by rfl⟩ : syracuseStep 1327691 = 1991537) B1991537
theorem B1131083 : Blo 231814 1131083 := bstep (se 1 (by rfl) ⟨848312, by rfl⟩ : syracuseStep 1131083 = 1696625) B1696625
theorem B2507395 : Blo 231814 2507395 := bstep (se 1 (by rfl) ⟨1880546, by rfl⟩ : syracuseStep 2507395 = 3761093) B3761093
theorem B5653313 : Blo 231814 5653313 := bstep (se 2 (by rfl) ⟨2119992, by rfl⟩ : syracuseStep 5653313 = 4239985) B4239985
theorem B443225 : Blo 231814 443225 := bstep (se 2 (by rfl) ⟨166209, by rfl⟩ : syracuseStep 443225 = 332419) B332419
theorem B1000451 : Blo 231814 1000451 := bstep (se 1 (by rfl) ⟨750338, by rfl⟩ : syracuseStep 1000451 = 1500677) B1500677
theorem B1492013 : Blo 231814 1492013 := bstep (se 3 (by rfl) ⟨279752, by rfl⟩ : syracuseStep 1492013 = 559505) B559505
theorem B476299 : Blo 231814 476299 := bstep (se 1 (by rfl) ⟨357224, by rfl⟩ : syracuseStep 476299 = 714449) B714449
theorem B837067 : Blo 231814 837067 := bstep (se 1 (by rfl) ⟨627800, by rfl⟩ : syracuseStep 837067 = 1255601) B1255601
theorem B706009 : Blo 231814 706009 := bstep (se 2 (by rfl) ⟨264753, by rfl⟩ : syracuseStep 706009 = 529507) B529507
theorem B4867715 : Blo 231814 4867715 := bstep (se 1 (by rfl) ⟨3650786, by rfl⟩ : syracuseStep 4867715 = 7301573) B7301573
theorem B2148113 : Blo 231814 2148113 := bstep (se 2 (by rfl) ⟨805542, by rfl⟩ : syracuseStep 2148113 = 1611085) B1611085
theorem B247627 : Blo 231814 247627 := bstep (se 1 (by rfl) ⟨185720, by rfl⟩ : syracuseStep 247627 = 371441) B371441
theorem B1263539 : Blo 231814 1263539 := bstep (se 1 (by rfl) ⟨947654, by rfl⟩ : syracuseStep 1263539 = 1895309) B1895309
theorem B1329331 : Blo 231814 1329331 := bstep (se 1 (by rfl) ⟨996998, by rfl⟩ : syracuseStep 1329331 = 1993997) B1993997
theorem B1689817 : Blo 231814 1689817 := bstep (se 2 (by rfl) ⟨633681, by rfl⟩ : syracuseStep 1689817 = 1267363) B1267363
theorem B444683 : Blo 231814 444683 := bstep (se 1 (by rfl) ⟨333512, by rfl⟩ : syracuseStep 444683 = 667025) B667025
theorem B444865 : Blo 231814 444865 := bstep (se 2 (by rfl) ⟨166824, by rfl⟩ : syracuseStep 444865 = 333649) B333649
theorem B838451 : Blo 231814 838451 := bstep (se 1 (by rfl) ⟨628838, by rfl⟩ : syracuseStep 838451 = 1257677) B1257677
theorem B641881 : Blo 231814 641881 := bstep (se 2 (by rfl) ⟨240705, by rfl⟩ : syracuseStep 641881 = 481411) B481411
theorem B445313 : Blo 231814 445313 := bstep (se 2 (by rfl) ⟨166992, by rfl⟩ : syracuseStep 445313 = 333985) B333985
theorem B2411441 : Blo 231814 2411441 := bstep (se 2 (by rfl) ⟨904290, by rfl⟩ : syracuseStep 2411441 = 1808581) B1808581
theorem B281675 : Blo 231814 281675 := bstep (se 1 (by rfl) ⟨211256, by rfl⟩ : syracuseStep 281675 = 422513) B422513
theorem B248951 : Blo 231814 248951 := bstep (se 1 (by rfl) ⟨186713, by rfl⟩ : syracuseStep 248951 = 373427) B373427
theorem B445655 : Blo 231814 445655 := bstep (se 1 (by rfl) ⟨334241, by rfl⟩ : syracuseStep 445655 = 668483) B668483
theorem B249079 : Blo 231814 249079 := bstep (se 1 (by rfl) ⟨186809, by rfl⟩ : syracuseStep 249079 = 373619) B373619
theorem B3919373 : Blo 231814 3919373 := bstep (se 3 (by rfl) ⟨734882, by rfl⟩ : syracuseStep 3919373 = 1469765) B1469765
theorem B1691201 : Blo 231814 1691201 := bstep (se 2 (by rfl) ⟨634200, by rfl⟩ : syracuseStep 1691201 = 1268401) B1268401
theorem B347723 : Blo 231814 347723 := bstep (se 1 (by rfl) ⟨260792, by rfl⟩ : syracuseStep 347723 = 521585) B521585
theorem B347735 : Blo 231814 347735 := bstep (se 1 (by rfl) ⟨260801, by rfl⟩ : syracuseStep 347735 = 521603) B521603
theorem B1330789 : Blo 231814 1330789 := bstep (se 4 (by rfl) ⟨124761, by rfl⟩ : syracuseStep 1330789 = 249523) B249523
theorem B1199767 : Blo 231814 1199767 := bstep (se 1 (by rfl) ⟨899825, by rfl⟩ : syracuseStep 1199767 = 1799651) B1799651
theorem B347801 : Blo 231814 347801 := bstep (se 2 (by rfl) ⟨130425, by rfl⟩ : syracuseStep 347801 = 260851) B260851
theorem B904877 : Blo 231814 904877 := bstep (se 3 (by rfl) ⟨169664, by rfl⟩ : syracuseStep 904877 = 339329) B339329
theorem B347915 : Blo 231814 347915 := bstep (se 1 (by rfl) ⟨260936, by rfl⟩ : syracuseStep 347915 = 521873) B521873
theorem B347927 : Blo 231814 347927 := bstep (se 1 (by rfl) ⟨260945, by rfl⟩ : syracuseStep 347927 = 521891) B521891
theorem B249643 : Blo 231814 249643 := bstep (se 1 (by rfl) ⟨187232, by rfl⟩ : syracuseStep 249643 = 374465) B374465
theorem B347993 : Blo 231814 347993 := bstep (se 2 (by rfl) ⟨130497, by rfl⟩ : syracuseStep 347993 = 260995) B260995
theorem B446323 : Blo 231814 446323 := bstep (se 1 (by rfl) ⟨334742, by rfl⟩ : syracuseStep 446323 = 669485) B669485
theorem B839603 : Blo 231814 839603 := bstep (se 1 (by rfl) ⟨629702, by rfl⟩ : syracuseStep 839603 = 1259405) B1259405
theorem B348107 : Blo 231814 348107 := bstep (se 1 (by rfl) ⟨261080, by rfl⟩ : syracuseStep 348107 = 522161) B522161
theorem B348119 : Blo 231814 348119 := bstep (se 1 (by rfl) ⟨261089, by rfl⟩ : syracuseStep 348119 = 522179) B522179
theorem B348185 : Blo 231814 348185 := bstep (se 2 (by rfl) ⟨130569, by rfl⟩ : syracuseStep 348185 = 261139) B261139
theorem B249899 : Blo 231814 249899 := bstep (se 1 (by rfl) ⟨187424, by rfl⟩ : syracuseStep 249899 = 374849) B374849
theorem B348299 : Blo 231814 348299 := bstep (se 1 (by rfl) ⟨261224, by rfl⟩ : syracuseStep 348299 = 522449) B522449
theorem B348311 : Blo 231814 348311 := bstep (se 1 (by rfl) ⟨261233, by rfl⟩ : syracuseStep 348311 = 522467) B522467
theorem B348377 : Blo 231814 348377 := bstep (se 2 (by rfl) ⟨130641, by rfl⟩ : syracuseStep 348377 = 261283) B261283
theorem B4837637 : Blo 231814 4837637 := bstep (se 4 (by rfl) ⟨453528, by rfl⟩ : syracuseStep 4837637 = 907057) B907057
theorem B446771 : Blo 231814 446771 := bstep (se 1 (by rfl) ⟨335078, by rfl⟩ : syracuseStep 446771 = 670157) B670157
theorem B348491 : Blo 231814 348491 := bstep (se 1 (by rfl) ⟨261368, by rfl⟩ : syracuseStep 348491 = 522737) B522737
theorem B348503 : Blo 231814 348503 := bstep (se 1 (by rfl) ⟨261377, by rfl⟩ : syracuseStep 348503 = 522755) B522755
theorem B446809 : Blo 231814 446809 := bstep (se 2 (by rfl) ⟨167553, by rfl⟩ : syracuseStep 446809 = 335107) B335107
theorem B348569 : Blo 231814 348569 := bstep (se 2 (by rfl) ⟨130713, by rfl⟩ : syracuseStep 348569 = 261427) B261427
theorem B348683 : Blo 231814 348683 := bstep (se 1 (by rfl) ⟨261512, by rfl⟩ : syracuseStep 348683 = 523025) B523025
theorem B348695 : Blo 231814 348695 := bstep (se 1 (by rfl) ⟨261521, by rfl⟩ : syracuseStep 348695 = 523043) B523043
theorem B348761 : Blo 231814 348761 := bstep (se 2 (by rfl) ⟨130785, by rfl⟩ : syracuseStep 348761 = 261571) B261571
theorem B1462963 : Blo 231814 1462963 := bstep (se 1 (by rfl) ⟨1097222, by rfl⟩ : syracuseStep 1462963 = 2194445) B2194445
theorem B348875 : Blo 231814 348875 := bstep (se 1 (by rfl) ⟨261656, by rfl⟩ : syracuseStep 348875 = 523313) B523313
theorem B348887 : Blo 231814 348887 := bstep (se 1 (by rfl) ⟨261665, by rfl⟩ : syracuseStep 348887 = 523331) B523331
theorem B348953 : Blo 231814 348953 := bstep (se 2 (by rfl) ⟨130857, by rfl⟩ : syracuseStep 348953 = 261715) B261715
theorem B447257 : Blo 231814 447257 := bstep (se 2 (by rfl) ⟨167721, by rfl⟩ : syracuseStep 447257 = 335443) B335443
theorem B349067 : Blo 231814 349067 := bstep (se 1 (by rfl) ⟨261800, by rfl⟩ : syracuseStep 349067 = 523601) B523601
theorem B349079 : Blo 231814 349079 := bstep (se 1 (by rfl) ⟨261809, by rfl⟩ : syracuseStep 349079 = 523619) B523619
theorem B349145 : Blo 231814 349145 := bstep (se 2 (by rfl) ⟨130929, by rfl⟩ : syracuseStep 349145 = 261859) B261859
theorem B349259 : Blo 231814 349259 := bstep (se 1 (by rfl) ⟨261944, by rfl⟩ : syracuseStep 349259 = 523889) B523889
theorem B349271 : Blo 231814 349271 := bstep (se 1 (by rfl) ⟨261953, by rfl⟩ : syracuseStep 349271 = 523907) B523907
theorem B349337 : Blo 231814 349337 := bstep (se 2 (by rfl) ⟨131001, by rfl⟩ : syracuseStep 349337 = 262003) B262003
theorem B1004723 : Blo 231814 1004723 := bstep (se 1 (by rfl) ⟨753542, by rfl⟩ : syracuseStep 1004723 = 1507085) B1507085
theorem B349451 : Blo 231814 349451 := bstep (se 1 (by rfl) ⟨262088, by rfl⟩ : syracuseStep 349451 = 524177) B524177
theorem B349463 : Blo 231814 349463 := bstep (se 1 (by rfl) ⟨262097, by rfl⟩ : syracuseStep 349463 = 524195) B524195
theorem B349529 : Blo 231814 349529 := bstep (se 2 (by rfl) ⟨131073, by rfl⟩ : syracuseStep 349529 = 262147) B262147
theorem B808385 : Blo 231814 808385 := bstep (se 2 (by rfl) ⟨303144, by rfl⟩ : syracuseStep 808385 = 606289) B606289
theorem B349643 : Blo 231814 349643 := bstep (se 1 (by rfl) ⟨262232, by rfl⟩ : syracuseStep 349643 = 524465) B524465
theorem B349655 : Blo 231814 349655 := bstep (se 1 (by rfl) ⟨262241, by rfl⟩ : syracuseStep 349655 = 524483) B524483
theorem B349721 : Blo 231814 349721 := bstep (se 2 (by rfl) ⟨131145, by rfl⟩ : syracuseStep 349721 = 262291) B262291
theorem B349835 : Blo 231814 349835 := bstep (se 1 (by rfl) ⟨262376, by rfl⟩ : syracuseStep 349835 = 524753) B524753
theorem B349847 : Blo 231814 349847 := bstep (se 1 (by rfl) ⟨262385, by rfl⟩ : syracuseStep 349847 = 524771) B524771
theorem B349913 : Blo 231814 349913 := bstep (se 2 (by rfl) ⟨131217, by rfl⟩ : syracuseStep 349913 = 262435) B262435
theorem B350027 : Blo 231814 350027 := bstep (se 1 (by rfl) ⟨262520, by rfl⟩ : syracuseStep 350027 = 525041) B525041
theorem B350039 : Blo 231814 350039 := bstep (se 1 (by rfl) ⟨262529, by rfl⟩ : syracuseStep 350039 = 525059) B525059
theorem B841565 : Blo 231814 841565 := bstep (se 3 (by rfl) ⟨157793, by rfl⟩ : syracuseStep 841565 = 315587) B315587
theorem B350105 : Blo 231814 350105 := bstep (se 2 (by rfl) ⟨131289, by rfl⟩ : syracuseStep 350105 = 262579) B262579
theorem B677825 : Blo 231814 677825 := bstep (se 2 (by rfl) ⟨254184, by rfl⟩ : syracuseStep 677825 = 508369) B508369
theorem B350219 : Blo 231814 350219 := bstep (se 1 (by rfl) ⟨262664, by rfl⟩ : syracuseStep 350219 = 525329) B525329
theorem B350231 : Blo 231814 350231 := bstep (se 1 (by rfl) ⟨262673, by rfl⟩ : syracuseStep 350231 = 525347) B525347
theorem B350297 : Blo 231814 350297 := bstep (se 2 (by rfl) ⟨131361, by rfl⟩ : syracuseStep 350297 = 262723) B262723
theorem B2676887 : Blo 231814 2676887 := bstep (se 1 (by rfl) ⟨2007665, by rfl⟩ : syracuseStep 2676887 = 4015331) B4015331
theorem B350411 : Blo 231814 350411 := bstep (se 1 (by rfl) ⟨262808, by rfl⟩ : syracuseStep 350411 = 525617) B525617
theorem B350423 : Blo 231814 350423 := bstep (se 1 (by rfl) ⟨262817, by rfl⟩ : syracuseStep 350423 = 525635) B525635
theorem B350489 : Blo 231814 350489 := bstep (se 2 (by rfl) ⟨131433, by rfl⟩ : syracuseStep 350489 = 262867) B262867
theorem B350603 : Blo 231814 350603 := bstep (se 1 (by rfl) ⟨262952, by rfl⟩ : syracuseStep 350603 = 525905) B525905
theorem B350615 : Blo 231814 350615 := bstep (se 1 (by rfl) ⟨262961, by rfl⟩ : syracuseStep 350615 = 525923) B525923
theorem B842201 : Blo 231814 842201 := bstep (se 2 (by rfl) ⟨315825, by rfl⟩ : syracuseStep 842201 = 631651) B631651
theorem B350681 : Blo 231814 350681 := bstep (se 2 (by rfl) ⟨131505, by rfl⟩ : syracuseStep 350681 = 263011) B263011
theorem B2382371 : Blo 231814 2382371 := bstep (se 1 (by rfl) ⟨1786778, by rfl⟩ : syracuseStep 2382371 = 3573557) B3573557
theorem B350795 : Blo 231814 350795 := bstep (se 1 (by rfl) ⟨263096, by rfl⟩ : syracuseStep 350795 = 526193) B526193
theorem B350807 : Blo 231814 350807 := bstep (se 1 (by rfl) ⟨263105, by rfl⟩ : syracuseStep 350807 = 526211) B526211
theorem B481879 : Blo 231814 481879 := bstep (se 1 (by rfl) ⟨361409, by rfl⟩ : syracuseStep 481879 = 722819) B722819
theorem B350873 : Blo 231814 350873 := bstep (se 2 (by rfl) ⟨131577, by rfl⟩ : syracuseStep 350873 = 263155) B263155
theorem B350987 : Blo 231814 350987 := bstep (se 1 (by rfl) ⟨263240, by rfl⟩ : syracuseStep 350987 = 526481) B526481
theorem B350999 : Blo 231814 350999 := bstep (se 1 (by rfl) ⟨263249, by rfl⟩ : syracuseStep 350999 = 526499) B526499
theorem B351065 : Blo 231814 351065 := bstep (se 2 (by rfl) ⟨131649, by rfl⟩ : syracuseStep 351065 = 263299) B263299
theorem B351179 : Blo 231814 351179 := bstep (se 1 (by rfl) ⟨263384, by rfl⟩ : syracuseStep 351179 = 526769) B526769
theorem B351191 : Blo 231814 351191 := bstep (se 1 (by rfl) ⟨263393, by rfl⟩ : syracuseStep 351191 = 526787) B526787
theorem B318425 : Blo 231814 318425 := bstep (se 2 (by rfl) ⟨119409, by rfl⟩ : syracuseStep 318425 = 238819) B238819
theorem B449497 : Blo 231814 449497 := bstep (se 2 (by rfl) ⟨168561, by rfl⟩ : syracuseStep 449497 = 337123) B337123
theorem B351257 : Blo 231814 351257 := bstep (se 2 (by rfl) ⟨131721, by rfl⟩ : syracuseStep 351257 = 263443) B263443
theorem B318539 : Blo 231814 318539 := bstep (se 1 (by rfl) ⟨238904, by rfl⟩ : syracuseStep 318539 = 477809) B477809
theorem B351371 : Blo 231814 351371 := bstep (se 1 (by rfl) ⟨263528, by rfl⟩ : syracuseStep 351371 = 527057) B527057
theorem B351383 : Blo 231814 351383 := bstep (se 1 (by rfl) ⟨263537, by rfl⟩ : syracuseStep 351383 = 527075) B527075
theorem B351449 : Blo 231814 351449 := bstep (se 2 (by rfl) ⟨131793, by rfl⟩ : syracuseStep 351449 = 263587) B263587
theorem B7232813 : Blo 231814 7232813 := bstep (se 3 (by rfl) ⟨1356152, by rfl⟩ : syracuseStep 7232813 = 2712305) B2712305
theorem B351563 : Blo 231814 351563 := bstep (se 1 (by rfl) ⟨263672, by rfl⟩ : syracuseStep 351563 = 527345) B527345
theorem B351575 : Blo 231814 351575 := bstep (se 1 (by rfl) ⟨263681, by rfl⟩ : syracuseStep 351575 = 527363) B527363
theorem B1006937 : Blo 231814 1006937 := bstep (se 2 (by rfl) ⟨377601, by rfl⟩ : syracuseStep 1006937 = 755203) B755203
theorem B351641 : Blo 231814 351641 := bstep (se 2 (by rfl) ⟨131865, by rfl⟩ : syracuseStep 351641 = 263731) B263731
theorem B712115 : Blo 231814 712115 := bstep (se 1 (by rfl) ⟨534086, by rfl⟩ : syracuseStep 712115 = 1068173) B1068173
theorem B351755 : Blo 231814 351755 := bstep (se 1 (by rfl) ⟨263816, by rfl⟩ : syracuseStep 351755 = 527633) B527633
theorem B351767 : Blo 231814 351767 := bstep (se 1 (by rfl) ⟨263825, by rfl⟩ : syracuseStep 351767 = 527651) B527651
theorem B351833 : Blo 231814 351833 := bstep (se 2 (by rfl) ⟨131937, by rfl⟩ : syracuseStep 351833 = 263875) B263875
theorem B351947 : Blo 231814 351947 := bstep (se 1 (by rfl) ⟨263960, by rfl⟩ : syracuseStep 351947 = 527921) B527921
theorem B351959 : Blo 231814 351959 := bstep (se 1 (by rfl) ⟨263969, by rfl⟩ : syracuseStep 351959 = 527939) B527939
theorem B483031 : Blo 231814 483031 := bstep (se 1 (by rfl) ⟨362273, by rfl⟩ : syracuseStep 483031 = 724547) B724547
theorem B352025 : Blo 231814 352025 := bstep (se 2 (by rfl) ⟨132009, by rfl⟩ : syracuseStep 352025 = 264019) B264019
theorem B1073027 : Blo 231814 1073027 := bstep (se 1 (by rfl) ⟨804770, by rfl⟩ : syracuseStep 1073027 = 1609541) B1609541
theorem B352139 : Blo 231814 352139 := bstep (se 1 (by rfl) ⟨264104, by rfl⟩ : syracuseStep 352139 = 528209) B528209
theorem B352151 : Blo 231814 352151 := bstep (se 1 (by rfl) ⟨264113, by rfl⟩ : syracuseStep 352151 = 528227) B528227
theorem B352217 : Blo 231814 352217 := bstep (se 2 (by rfl) ⟨132081, by rfl⟩ : syracuseStep 352217 = 264163) B264163
theorem B352331 : Blo 231814 352331 := bstep (se 1 (by rfl) ⟨264248, by rfl⟩ : syracuseStep 352331 = 528497) B528497
theorem B352343 : Blo 231814 352343 := bstep (se 1 (by rfl) ⟨264257, by rfl⟩ : syracuseStep 352343 = 528515) B528515
theorem B352409 : Blo 231814 352409 := bstep (se 2 (by rfl) ⟨132153, by rfl⟩ : syracuseStep 352409 = 264307) B264307
theorem B2154701 : Blo 231814 2154701 := bstep (se 3 (by rfl) ⟨404006, by rfl⟩ : syracuseStep 2154701 = 808013) B808013
theorem B352523 : Blo 231814 352523 := bstep (se 1 (by rfl) ⟨264392, by rfl⟩ : syracuseStep 352523 = 528785) B528785
theorem B352535 : Blo 231814 352535 := bstep (se 1 (by rfl) ⟨264401, by rfl⟩ : syracuseStep 352535 = 528803) B528803
theorem B352601 : Blo 231814 352601 := bstep (se 2 (by rfl) ⟨132225, by rfl⟩ : syracuseStep 352601 = 264451) B264451
theorem B418187 : Blo 231814 418187 := bstep (se 1 (by rfl) ⟨313640, by rfl⟩ : syracuseStep 418187 = 627281) B627281
theorem B352715 : Blo 231814 352715 := bstep (se 1 (by rfl) ⟨264536, by rfl⟩ : syracuseStep 352715 = 529073) B529073
theorem B352727 : Blo 231814 352727 := bstep (se 1 (by rfl) ⟨264545, by rfl⟩ : syracuseStep 352727 = 529091) B529091
theorem B352793 : Blo 231814 352793 := bstep (se 2 (by rfl) ⟨132297, by rfl⟩ : syracuseStep 352793 = 264595) B264595
theorem B352907 : Blo 231814 352907 := bstep (se 1 (by rfl) ⟨264680, by rfl⟩ : syracuseStep 352907 = 529361) B529361
theorem B352919 : Blo 231814 352919 := bstep (se 1 (by rfl) ⟨264689, by rfl⟩ : syracuseStep 352919 = 529379) B529379
theorem B352985 : Blo 231814 352985 := bstep (se 2 (by rfl) ⟨132369, by rfl⟩ : syracuseStep 352985 = 264739) B264739
theorem B746263 : Blo 231814 746263 := bstep (se 1 (by rfl) ⟨559697, by rfl⟩ : syracuseStep 746263 = 1119395) B1119395
theorem B353099 : Blo 231814 353099 := bstep (se 1 (by rfl) ⟨264824, by rfl⟩ : syracuseStep 353099 = 529649) B529649
theorem B353111 : Blo 231814 353111 := bstep (se 1 (by rfl) ⟨264833, by rfl⟩ : syracuseStep 353111 = 529667) B529667
theorem B353177 : Blo 231814 353177 := bstep (se 2 (by rfl) ⟨132441, by rfl⟩ : syracuseStep 353177 = 264883) B264883
theorem B353291 : Blo 231814 353291 := bstep (se 1 (by rfl) ⟨264968, by rfl⟩ : syracuseStep 353291 = 529937) B529937
theorem B353303 : Blo 231814 353303 := bstep (se 1 (by rfl) ⟨264977, by rfl⟩ : syracuseStep 353303 = 529955) B529955
theorem B353369 : Blo 231814 353369 := bstep (se 2 (by rfl) ⟨132513, by rfl⟩ : syracuseStep 353369 = 265027) B265027
theorem B353483 : Blo 231814 353483 := bstep (se 1 (by rfl) ⟨265112, by rfl⟩ : syracuseStep 353483 = 530225) B530225
theorem B353495 : Blo 231814 353495 := bstep (se 1 (by rfl) ⟨265121, by rfl⟩ : syracuseStep 353495 = 530243) B530243
theorem B517387 : Blo 231814 517387 := bstep (se 1 (by rfl) ⟨388040, by rfl⟩ : syracuseStep 517387 = 776081) B776081
theorem B353561 : Blo 231814 353561 := bstep (se 2 (by rfl) ⟨132585, by rfl⟩ : syracuseStep 353561 = 265171) B265171
theorem B1336621 : Blo 231814 1336621 := bstep (se 3 (by rfl) ⟨250616, by rfl⟩ : syracuseStep 1336621 = 501233) B501233
theorem B353675 : Blo 231814 353675 := bstep (se 1 (by rfl) ⟨265256, by rfl⟩ : syracuseStep 353675 = 530513) B530513
theorem B353687 : Blo 231814 353687 := bstep (se 1 (by rfl) ⟨265265, by rfl⟩ : syracuseStep 353687 = 530531) B530531
theorem B845315 : Blo 231814 845315 := bstep (se 1 (by rfl) ⟨633986, by rfl⟩ : syracuseStep 845315 = 1267973) B1267973
theorem B1009217 : Blo 231814 1009217 := bstep (se 2 (by rfl) ⟨378456, by rfl⟩ : syracuseStep 1009217 = 756913) B756913
theorem B747083 : Blo 231814 747083 := bstep (se 1 (by rfl) ⟨560312, by rfl⟩ : syracuseStep 747083 = 1120625) B1120625
theorem B845515 : Blo 231814 845515 := bstep (se 1 (by rfl) ⟨634136, by rfl⟩ : syracuseStep 845515 = 1268273) B1268273
theorem B4056817 : Blo 231814 4056817 := bstep (se 2 (by rfl) ⟨1521306, by rfl⟩ : syracuseStep 4056817 = 3042613) B3042613
theorem B1992599 : Blo 231814 1992599 := bstep (se 1 (by rfl) ⟨1494449, by rfl⟩ : syracuseStep 1992599 = 2988899) B2988899
theorem B845747 : Blo 231814 845747 := bstep (se 1 (by rfl) ⟨634310, by rfl⟩ : syracuseStep 845747 = 1268621) B1268621
theorem B1174337 : Blo 231814 1174337 := bstep (se 2 (by rfl) ⟨440376, by rfl⟩ : syracuseStep 1174337 = 880753) B880753
theorem B453683 : Blo 231814 453683 := bstep (se 1 (by rfl) ⟨340262, by rfl⟩ : syracuseStep 453683 = 680525) B680525
theorem B748865 : Blo 231814 748865 := bstep (se 2 (by rfl) ⟨280824, by rfl⟩ : syracuseStep 748865 = 561649) B561649
theorem B13463171 : Blo 231814 13463171 := bstep (se 1 (by rfl) ⟨10097378, by rfl⟩ : syracuseStep 13463171 = 20194757) B20194757
theorem B2420375 : Blo 231814 2420375 := bstep (se 1 (by rfl) ⟨1815281, by rfl⟩ : syracuseStep 2420375 = 3630563) B3630563
theorem B1699505 : Blo 231814 1699505 := bstep (se 2 (by rfl) ⟨637314, by rfl⟩ : syracuseStep 1699505 = 1274629) B1274629
theorem B3993461 : Blo 231814 3993461 := bstep (se 5 (by rfl) ⟨187193, by rfl⟩ : syracuseStep 3993461 = 374387) B374387
theorem B1765637 : Blo 231814 1765637 := bstep (se 4 (by rfl) ⟨165528, by rfl⟩ : syracuseStep 1765637 = 331057) B331057
theorem B422167 : Blo 231814 422167 := bstep (se 1 (by rfl) ⟨316625, by rfl⟩ : syracuseStep 422167 = 633251) B633251
theorem B881027 : Blo 231814 881027 := bstep (se 1 (by rfl) ⟨660770, by rfl⟩ : syracuseStep 881027 = 1321541) B1321541
theorem B848515 : Blo 231814 848515 := bstep (se 1 (by rfl) ⟨636386, by rfl⟩ : syracuseStep 848515 = 1272773) B1272773
theorem B782999 : Blo 231814 782999 := bstep (se 1 (by rfl) ⟨587249, by rfl⟩ : syracuseStep 782999 = 1174499) B1174499
theorem B1176281 : Blo 231814 1176281 := bstep (se 2 (by rfl) ⟨441105, by rfl⟩ : syracuseStep 1176281 = 882211) B882211
theorem B3240805 : Blo 231814 3240805 := bstep (se 4 (by rfl) ⟨303825, by rfl⟩ : syracuseStep 3240805 = 607651) B607651
theorem B848819 : Blo 231814 848819 := bstep (se 1 (by rfl) ⟨636614, by rfl⟩ : syracuseStep 848819 = 1273229) B1273229
theorem B783539 : Blo 231814 783539 := bstep (se 1 (by rfl) ⟨587654, by rfl⟩ : syracuseStep 783539 = 1175309) B1175309
theorem B587159 : Blo 231814 587159 := bstep (se 1 (by rfl) ⟨440369, by rfl⟩ : syracuseStep 587159 = 880739) B880739
theorem B783809 : Blo 231814 783809 := bstep (se 2 (by rfl) ⟨293928, by rfl⟩ : syracuseStep 783809 = 587857) B587857
theorem B521675 : Blo 231814 521675 := bstep (se 1 (by rfl) ⟨391256, by rfl⟩ : syracuseStep 521675 = 782513) B782513
theorem B521729 : Blo 231814 521729 := bstep (se 2 (by rfl) ⟨195648, by rfl⟩ : syracuseStep 521729 = 391297) B391297
theorem B521945 : Blo 231814 521945 := bstep (se 2 (by rfl) ⟨195729, by rfl⟩ : syracuseStep 521945 = 391459) B391459
theorem B522035 : Blo 231814 522035 := bstep (se 1 (by rfl) ⟨391526, by rfl⟩ : syracuseStep 522035 = 783053) B783053
theorem B522071 : Blo 231814 522071 := bstep (se 1 (by rfl) ⟨391553, by rfl⟩ : syracuseStep 522071 = 783107) B783107
theorem B784349 : Blo 231814 784349 := bstep (se 3 (by rfl) ⟨147065, by rfl⟩ : syracuseStep 784349 = 294131) B294131
theorem B522251 : Blo 231814 522251 := bstep (se 1 (by rfl) ⟨391688, by rfl⟩ : syracuseStep 522251 = 783377) B783377
theorem B522305 : Blo 231814 522305 := bstep (se 2 (by rfl) ⟨195864, by rfl⟩ : syracuseStep 522305 = 391729) B391729
theorem B391243 : Blo 231814 391243 := bstep (se 1 (by rfl) ⟨293432, by rfl⟩ : syracuseStep 391243 = 586865) B586865
theorem B2685059 : Blo 231814 2685059 := bstep (se 1 (by rfl) ⟨2013794, by rfl⟩ : syracuseStep 2685059 = 4027589) B4027589
theorem B1800323 : Blo 231814 1800323 := bstep (se 1 (by rfl) ⟨1350242, by rfl⟩ : syracuseStep 1800323 = 2700485) B2700485
theorem B587969 : Blo 231814 587969 := bstep (se 2 (by rfl) ⟨220488, by rfl⟩ : syracuseStep 587969 = 440977) B440977
theorem B391385 : Blo 231814 391385 := bstep (se 2 (by rfl) ⟨146769, by rfl⟩ : syracuseStep 391385 = 293539) B293539
theorem B522521 : Blo 231814 522521 := bstep (se 2 (by rfl) ⟨195945, by rfl⟩ : syracuseStep 522521 = 391891) B391891
theorem B1177901 : Blo 231814 1177901 := bstep (se 3 (by rfl) ⟨220856, by rfl⟩ : syracuseStep 1177901 = 441713) B441713
theorem B391513 : Blo 231814 391513 := bstep (se 2 (by rfl) ⟨146817, by rfl⟩ : syracuseStep 391513 = 293635) B293635
theorem B522611 : Blo 231814 522611 := bstep (se 1 (by rfl) ⟨391958, by rfl⟩ : syracuseStep 522611 = 783917) B783917
theorem B948611 : Blo 231814 948611 := bstep (se 1 (by rfl) ⟨711458, by rfl⟩ : syracuseStep 948611 = 1422917) B1422917
theorem B522647 : Blo 231814 522647 := bstep (se 1 (by rfl) ⟨391985, by rfl⟩ : syracuseStep 522647 = 783971) B783971
theorem B522827 : Blo 231814 522827 := bstep (se 1 (by rfl) ⟨392120, by rfl⟩ : syracuseStep 522827 = 784241) B784241
theorem B522881 : Blo 231814 522881 := bstep (se 2 (by rfl) ⟨196080, by rfl⟩ : syracuseStep 522881 = 392161) B392161
theorem B1768067 : Blo 231814 1768067 := bstep (se 1 (by rfl) ⟨1326050, by rfl⟩ : syracuseStep 1768067 = 2652101) B2652101
theorem B588505 : Blo 231814 588505 := bstep (se 2 (by rfl) ⟨220689, by rfl⟩ : syracuseStep 588505 = 441379) B441379
theorem B7568113 : Blo 231814 7568113 := bstep (se 2 (by rfl) ⟨2838042, by rfl⟩ : syracuseStep 7568113 = 5676085) B5676085
theorem B260887 : Blo 231814 260887 := bstep (se 1 (by rfl) ⟨195665, by rfl⟩ : syracuseStep 260887 = 391331) B391331
theorem B523097 : Blo 231814 523097 := bstep (se 2 (by rfl) ⟨196161, by rfl⟩ : syracuseStep 523097 = 392323) B392323
theorem B1801061 : Blo 231814 1801061 := bstep (se 4 (by rfl) ⟨168849, by rfl⟩ : syracuseStep 1801061 = 337699) B337699
theorem B392087 : Blo 231814 392087 := bstep (se 1 (by rfl) ⟨294065, by rfl⟩ : syracuseStep 392087 = 588131) B588131
theorem B523187 : Blo 231814 523187 := bstep (se 1 (by rfl) ⟨392390, by rfl⟩ : syracuseStep 523187 = 784781) B784781
theorem B261067 : Blo 231814 261067 := bstep (se 1 (by rfl) ⟨195800, by rfl⟩ : syracuseStep 261067 = 391601) B391601
theorem B523223 : Blo 231814 523223 := bstep (se 1 (by rfl) ⟨392417, by rfl⟩ : syracuseStep 523223 = 784835) B784835
theorem B392215 : Blo 231814 392215 := bstep (se 1 (by rfl) ⟨294161, by rfl⟩ : syracuseStep 392215 = 588323) B588323
theorem B261175 : Blo 231814 261175 := bstep (se 1 (by rfl) ⟨195881, by rfl⟩ : syracuseStep 261175 = 391763) B391763
theorem B785483 : Blo 231814 785483 := bstep (se 1 (by rfl) ⟨589112, by rfl⟩ : syracuseStep 785483 = 1178225) B1178225
theorem B523403 : Blo 231814 523403 := bstep (se 1 (by rfl) ⟨392552, by rfl⟩ : syracuseStep 523403 = 785105) B785105
theorem B523457 : Blo 231814 523457 := bstep (se 2 (by rfl) ⟨196296, by rfl⟩ : syracuseStep 523457 = 392593) B392593
theorem B261355 : Blo 231814 261355 := bstep (se 1 (by rfl) ⟨196016, by rfl⟩ : syracuseStep 261355 = 392033) B392033
theorem B261463 : Blo 231814 261463 := bstep (se 1 (by rfl) ⟨196097, by rfl⟩ : syracuseStep 261463 = 392195) B392195
theorem B785753 : Blo 231814 785753 := bstep (se 2 (by rfl) ⟨294657, by rfl⟩ : syracuseStep 785753 = 589315) B589315
theorem B294283 : Blo 231814 294283 := bstep (se 1 (by rfl) ⟨220712, by rfl⟩ : syracuseStep 294283 = 441425) B441425
theorem B523673 : Blo 231814 523673 := bstep (se 2 (by rfl) ⟨196377, by rfl⟩ : syracuseStep 523673 = 392755) B392755
theorem B884141 : Blo 231814 884141 := bstep (se 3 (by rfl) ⟨165776, by rfl⟩ : syracuseStep 884141 = 331553) B331553
theorem B523763 : Blo 231814 523763 := bstep (se 1 (by rfl) ⟨392822, by rfl⟩ : syracuseStep 523763 = 785645) B785645
theorem B261643 : Blo 231814 261643 := bstep (se 1 (by rfl) ⟨196232, by rfl⟩ : syracuseStep 261643 = 392465) B392465
theorem B523799 : Blo 231814 523799 := bstep (se 1 (by rfl) ⟨392849, by rfl⟩ : syracuseStep 523799 = 785699) B785699
theorem B1998371 : Blo 231814 1998371 := bstep (se 1 (by rfl) ⟨1498778, by rfl⟩ : syracuseStep 1998371 = 2997557) B2997557
theorem B261751 : Blo 231814 261751 := bstep (se 1 (by rfl) ⟨196313, by rfl⟩ : syracuseStep 261751 = 392627) B392627
theorem B392843 : Blo 231814 392843 := bstep (se 1 (by rfl) ⟨294632, by rfl⟩ : syracuseStep 392843 = 589265) B589265
theorem B523979 : Blo 231814 523979 := bstep (se 1 (by rfl) ⟨392984, by rfl⟩ : syracuseStep 523979 = 785969) B785969
theorem B524033 : Blo 231814 524033 := bstep (se 2 (by rfl) ⟨196512, by rfl⟩ : syracuseStep 524033 = 393025) B393025
theorem B392971 : Blo 231814 392971 := bstep (se 1 (by rfl) ⟨294728, by rfl⟩ : syracuseStep 392971 = 589457) B589457
theorem B950039 : Blo 231814 950039 := bstep (se 1 (by rfl) ⟨712529, by rfl⟩ : syracuseStep 950039 = 1425059) B1425059
theorem B261931 : Blo 231814 261931 := bstep (se 1 (by rfl) ⟨196448, by rfl⟩ : syracuseStep 261931 = 392897) B392897
theorem B589619 : Blo 231814 589619 := bstep (se 1 (by rfl) ⟨442214, by rfl⟩ : syracuseStep 589619 = 884429) B884429
theorem B262039 : Blo 231814 262039 := bstep (se 1 (by rfl) ⟨196529, by rfl⟩ : syracuseStep 262039 = 393059) B393059
theorem B393113 : Blo 231814 393113 := bstep (se 2 (by rfl) ⟨147417, by rfl⟩ : syracuseStep 393113 = 294835) B294835
theorem B1343411 : Blo 231814 1343411 := bstep (se 1 (by rfl) ⟨1007558, by rfl⟩ : syracuseStep 1343411 = 2015117) B2015117
theorem B1114073 : Blo 231814 1114073 := bstep (se 2 (by rfl) ⟨417777, by rfl⟩ : syracuseStep 1114073 = 835555) B835555
theorem B524249 : Blo 231814 524249 := bstep (se 2 (by rfl) ⟨196593, by rfl⟩ : syracuseStep 524249 = 393187) B393187
theorem B524303 : Blo 231814 524303 := bstep (se 1 (by rfl) ⟨393227, by rfl⟩ : syracuseStep 524303 = 786455) B786455
theorem B524321 : Blo 231814 524321 := bstep (se 2 (by rfl) ⟨196620, by rfl⟩ : syracuseStep 524321 = 393241) B393241
theorem B393275 : Blo 231814 393275 := bstep (se 1 (by rfl) ⟨294956, by rfl⟩ : syracuseStep 393275 = 589913) B589913
theorem B589943 : Blo 231814 589943 := bstep (se 1 (by rfl) ⟨442457, by rfl⟩ : syracuseStep 589943 = 884915) B884915
theorem B295159 : Blo 231814 295159 := bstep (se 1 (by rfl) ⟨221369, by rfl⟩ : syracuseStep 295159 = 442739) B442739
theorem B524663 : Blo 231814 524663 := bstep (se 1 (by rfl) ⟨393497, by rfl⟩ : syracuseStep 524663 = 786995) B786995
theorem B885127 : Blo 231814 885127 := bstep (se 1 (by rfl) ⟨663845, by rfl⟩ : syracuseStep 885127 = 1327691) B1327691
theorem B754055 : Blo 231814 754055 := bstep (se 1 (by rfl) ⟨565541, by rfl⟩ : syracuseStep 754055 = 1131083) B1131083
theorem B262543 : Blo 231814 262543 := bstep (se 1 (by rfl) ⟨196907, by rfl⟩ : syracuseStep 262543 = 393815) B393815
theorem B754105 : Blo 231814 754105 := bstep (se 2 (by rfl) ⟨282789, by rfl⟩ : syracuseStep 754105 = 565579) B565579
theorem B393673 : Blo 231814 393673 := bstep (se 2 (by rfl) ⟨147627, by rfl⟩ : syracuseStep 393673 = 295255) B295255
theorem B3768875 : Blo 231814 3768875 := bstep (se 1 (by rfl) ⟨2826656, by rfl⟩ : syracuseStep 3768875 = 5653313) B5653313
theorem B524843 : Blo 231814 524843 := bstep (se 1 (by rfl) ⟨393632, by rfl⟩ : syracuseStep 524843 = 787265) B787265
theorem B295483 : Blo 231814 295483 := bstep (se 1 (by rfl) ⟨221612, by rfl⟩ : syracuseStep 295483 = 443225) B443225
theorem B3343193 : Blo 231814 3343193 := bstep (se 2 (by rfl) ⟨1253697, by rfl⟩ : syracuseStep 3343193 = 2507395) B2507395
theorem B263047 : Blo 231814 263047 := bstep (se 1 (by rfl) ⟨197285, by rfl⟩ : syracuseStep 263047 = 394571) B394571
theorem B525203 : Blo 231814 525203 := bstep (se 1 (by rfl) ⟨393902, by rfl⟩ : syracuseStep 525203 = 787805) B787805
theorem B525257 : Blo 231814 525257 := bstep (se 2 (by rfl) ⟨196971, by rfl⟩ : syracuseStep 525257 = 393943) B393943
theorem B1115165 : Blo 231814 1115165 := bstep (se 3 (by rfl) ⟨209093, by rfl⟩ : syracuseStep 1115165 = 418187) B418187
theorem B263227 : Blo 231814 263227 := bstep (se 1 (by rfl) ⟨197420, by rfl⟩ : syracuseStep 263227 = 394841) B394841
theorem B590935 : Blo 231814 590935 := bstep (se 1 (by rfl) ⟨443201, by rfl⟩ : syracuseStep 590935 = 886403) B886403
theorem B3245143 : Blo 231814 3245143 := bstep (se 1 (by rfl) ⟨2433857, by rfl⟩ : syracuseStep 3245143 = 4867715) B4867715
theorem B394375 : Blo 231814 394375 := bstep (se 1 (by rfl) ⟨295781, by rfl⟩ : syracuseStep 394375 = 591563) B591563
theorem B1180979 : Blo 231814 1180979 := bstep (se 1 (by rfl) ⟨885734, by rfl⟩ : syracuseStep 1180979 = 1771469) B1771469
theorem B591239 : Blo 231814 591239 := bstep (se 1 (by rfl) ⟨443429, by rfl⟩ : syracuseStep 591239 = 886859) B886859
theorem B787859 : Blo 231814 787859 := bstep (se 1 (by rfl) ⟨590894, by rfl⟩ : syracuseStep 787859 = 1181789) B1181789
theorem B296455 : Blo 231814 296455 := bstep (se 1 (by rfl) ⟨222341, by rfl⟩ : syracuseStep 296455 = 444683) B444683
theorem B591371 : Blo 231814 591371 := bstep (se 1 (by rfl) ⟨443528, by rfl⟩ : syracuseStep 591371 = 887057) B887057
theorem B263695 : Blo 231814 263695 := bstep (se 1 (by rfl) ⟨197771, by rfl⟩ : syracuseStep 263695 = 395543) B395543
theorem B1181303 : Blo 231814 1181303 := bstep (se 1 (by rfl) ⟨885977, by rfl⟩ : syracuseStep 1181303 = 1771955) B1771955
theorem B525959 : Blo 231814 525959 := bstep (se 1 (by rfl) ⟨394469, by rfl⟩ : syracuseStep 525959 = 788939) B788939
theorem B689849 : Blo 231814 689849 := bstep (se 2 (by rfl) ⟨258693, by rfl⟩ : syracuseStep 689849 = 517387) B517387
theorem B395023 : Blo 231814 395023 := bstep (se 1 (by rfl) ⟨296267, by rfl⟩ : syracuseStep 395023 = 592535) B592535
theorem B526139 : Blo 231814 526139 := bstep (se 1 (by rfl) ⟨394604, by rfl⟩ : syracuseStep 526139 = 789209) B789209
theorem B558967 : Blo 231814 558967 := bstep (se 1 (by rfl) ⟨419225, by rfl⟩ : syracuseStep 558967 = 838451) B838451
theorem B296875 : Blo 231814 296875 := bstep (se 1 (by rfl) ⟨222656, by rfl⟩ : syracuseStep 296875 = 445313) B445313
theorem B1116089 : Blo 231814 1116089 := bstep (se 2 (by rfl) ⟨418533, by rfl⟩ : syracuseStep 1116089 = 837067) B837067
theorem B526265 : Blo 231814 526265 := bstep (se 2 (by rfl) ⟨197349, by rfl⟩ : syracuseStep 526265 = 394699) B394699
theorem B1607627 : Blo 231814 1607627 := bstep (se 1 (by rfl) ⟨1205720, by rfl⟩ : syracuseStep 1607627 = 2411441) B2411441
theorem B264199 : Blo 231814 264199 := bstep (se 1 (by rfl) ⟨198149, by rfl⟩ : syracuseStep 264199 = 396299) B396299
theorem B591887 : Blo 231814 591887 := bstep (se 1 (by rfl) ⟨443915, by rfl⟩ : syracuseStep 591887 = 887831) B887831
theorem B297103 : Blo 231814 297103 := bstep (se 1 (by rfl) ⟨222827, by rfl⟩ : syracuseStep 297103 = 445655) B445655
theorem B592019 : Blo 231814 592019 := bstep (se 1 (by rfl) ⟨444014, by rfl⟩ : syracuseStep 592019 = 888029) B888029
theorem B264379 : Blo 231814 264379 := bstep (se 1 (by rfl) ⟨198284, by rfl⟩ : syracuseStep 264379 = 396569) B396569
theorem B526607 : Blo 231814 526607 := bstep (se 1 (by rfl) ⟨394955, by rfl⟩ : syracuseStep 526607 = 789911) B789911
theorem B526625 : Blo 231814 526625 := bstep (se 2 (by rfl) ⟨197484, by rfl⟩ : syracuseStep 526625 = 394969) B394969
theorem B395563 : Blo 231814 395563 := bstep (se 1 (by rfl) ⟨296672, by rfl⟩ : syracuseStep 395563 = 593345) B593345
theorem B5409089 : Blo 231814 5409089 := bstep (se 2 (by rfl) ⟨2028408, by rfl⟩ : syracuseStep 5409089 = 4056817) B4056817
theorem B231815 : Blo 231814 231815 := bstep (se 1 (by rfl) ⟨173861, by rfl⟩ : syracuseStep 231815 = 347723) B347723
theorem B231823 : Blo 231814 231823 := bstep (se 1 (by rfl) ⟨173867, by rfl⟩ : syracuseStep 231823 = 347735) B347735
theorem B330169 : Blo 231814 330169 := bstep (se 2 (by rfl) ⟨123813, by rfl⟩ : syracuseStep 330169 = 247627) B247627
theorem B395705 : Blo 231814 395705 := bstep (se 2 (by rfl) ⟨148389, by rfl⟩ : syracuseStep 395705 = 296779) B296779
theorem B231867 : Blo 231814 231867 := bstep (se 1 (by rfl) ⟨173900, by rfl⟩ : syracuseStep 231867 = 347801) B347801
theorem B231943 : Blo 231814 231943 := bstep (se 1 (by rfl) ⟨173957, by rfl⟩ : syracuseStep 231943 = 347915) B347915
theorem B231951 : Blo 231814 231951 := bstep (se 1 (by rfl) ⟨173963, by rfl⟩ : syracuseStep 231951 = 347927) B347927
theorem B231995 : Blo 231814 231995 := bstep (se 1 (by rfl) ⟨173996, by rfl⟩ : syracuseStep 231995 = 347993) B347993
theorem B6687299 : Blo 231814 6687299 := bstep (se 1 (by rfl) ⟨5015474, by rfl⟩ : syracuseStep 6687299 = 10030949) B10030949
theorem B1182275 : Blo 231814 1182275 := bstep (se 1 (by rfl) ⟨886706, by rfl⟩ : syracuseStep 1182275 = 1773413) B1773413
theorem B526967 : Blo 231814 526967 := bstep (se 1 (by rfl) ⟨395225, by rfl⟩ : syracuseStep 526967 = 790451) B790451
theorem B232071 : Blo 231814 232071 := bstep (se 1 (by rfl) ⟨174053, by rfl⟩ : syracuseStep 232071 = 348107) B348107
theorem B232079 : Blo 231814 232079 := bstep (se 1 (by rfl) ⟨174059, by rfl⟩ : syracuseStep 232079 = 348119) B348119
theorem B264847 : Blo 231814 264847 := bstep (se 1 (by rfl) ⟨198635, by rfl⟩ : syracuseStep 264847 = 397271) B397271
theorem B232123 : Blo 231814 232123 := bstep (se 1 (by rfl) ⟨174092, by rfl⟩ : syracuseStep 232123 = 348185) B348185
theorem B232199 : Blo 231814 232199 := bstep (se 1 (by rfl) ⟨174149, by rfl⟩ : syracuseStep 232199 = 348299) B348299
theorem B232207 : Blo 231814 232207 := bstep (se 1 (by rfl) ⟨174155, by rfl⟩ : syracuseStep 232207 = 348311) B348311
theorem B789263 : Blo 231814 789263 := bstep (se 1 (by rfl) ⟨591947, by rfl⟩ : syracuseStep 789263 = 1183895) B1183895
theorem B527147 : Blo 231814 527147 := bstep (se 1 (by rfl) ⟨395360, by rfl⟩ : syracuseStep 527147 = 790721) B790721
theorem B232251 : Blo 231814 232251 := bstep (se 1 (by rfl) ⟨174188, by rfl⟩ : syracuseStep 232251 = 348377) B348377
theorem B4787059 : Blo 231814 4787059 := bstep (se 1 (by rfl) ⟨3590294, by rfl⟩ : syracuseStep 4787059 = 7180589) B7180589
theorem B297847 : Blo 231814 297847 := bstep (se 1 (by rfl) ⟨223385, by rfl⟩ : syracuseStep 297847 = 446771) B446771
theorem B232327 : Blo 231814 232327 := bstep (se 1 (by rfl) ⟨174245, by rfl⟩ : syracuseStep 232327 = 348491) B348491
theorem B1182599 : Blo 231814 1182599 := bstep (se 1 (by rfl) ⟨886949, by rfl⟩ : syracuseStep 1182599 = 1773899) B1773899
theorem B232335 : Blo 231814 232335 := bstep (se 1 (by rfl) ⟨174251, by rfl⟩ : syracuseStep 232335 = 348503) B348503
theorem B1772441 : Blo 231814 1772441 := bstep (se 2 (by rfl) ⟨664665, by rfl⟩ : syracuseStep 1772441 = 1329331) B1329331
theorem B232379 : Blo 231814 232379 := bstep (se 1 (by rfl) ⟨174284, by rfl⟩ : syracuseStep 232379 = 348569) B348569
theorem B232455 : Blo 231814 232455 := bstep (se 1 (by rfl) ⟨174341, by rfl⟩ : syracuseStep 232455 = 348683) B348683
theorem B232463 : Blo 231814 232463 := bstep (se 1 (by rfl) ⟨174347, by rfl⟩ : syracuseStep 232463 = 348695) B348695
theorem B789533 : Blo 231814 789533 := bstep (se 3 (by rfl) ⟨148037, by rfl⟩ : syracuseStep 789533 = 296075) B296075
theorem B232507 : Blo 231814 232507 := bstep (se 1 (by rfl) ⟨174380, by rfl⟩ : syracuseStep 232507 = 348761) B348761
theorem B396407 : Blo 231814 396407 := bstep (se 1 (by rfl) ⟨297305, by rfl⟩ : syracuseStep 396407 = 594611) B594611
theorem B232583 : Blo 231814 232583 := bstep (se 1 (by rfl) ⟨174437, by rfl⟩ : syracuseStep 232583 = 348875) B348875
theorem B232591 : Blo 231814 232591 := bstep (se 1 (by rfl) ⟨174443, by rfl⟩ : syracuseStep 232591 = 348887) B348887
theorem B527507 : Blo 231814 527507 := bstep (se 1 (by rfl) ⟨395630, by rfl⟩ : syracuseStep 527507 = 791261) B791261
theorem B232635 : Blo 231814 232635 := bstep (se 1 (by rfl) ⟨174476, by rfl⟩ : syracuseStep 232635 = 348953) B348953
theorem B298171 : Blo 231814 298171 := bstep (se 1 (by rfl) ⟨223628, by rfl⟩ : syracuseStep 298171 = 447257) B447257
theorem B527561 : Blo 231814 527561 := bstep (se 2 (by rfl) ⟨197835, by rfl⟩ : syracuseStep 527561 = 395671) B395671
theorem B1412333 : Blo 231814 1412333 := bstep (se 3 (by rfl) ⟨264812, by rfl⟩ : syracuseStep 1412333 = 529625) B529625
theorem B593153 : Blo 231814 593153 := bstep (se 2 (by rfl) ⟨222432, by rfl⟩ : syracuseStep 593153 = 444865) B444865
theorem B232711 : Blo 231814 232711 := bstep (se 1 (by rfl) ⟨174533, by rfl⟩ : syracuseStep 232711 = 349067) B349067
theorem B232719 : Blo 231814 232719 := bstep (se 1 (by rfl) ⟨174539, by rfl⟩ : syracuseStep 232719 = 349079) B349079
theorem B232763 : Blo 231814 232763 := bstep (se 1 (by rfl) ⟨174572, by rfl⟩ : syracuseStep 232763 = 349145) B349145
theorem B232839 : Blo 231814 232839 := bstep (se 1 (by rfl) ⟨174629, by rfl⟩ : syracuseStep 232839 = 349259) B349259
theorem B232847 : Blo 231814 232847 := bstep (se 1 (by rfl) ⟨174635, by rfl⟩ : syracuseStep 232847 = 349271) B349271
theorem B232891 : Blo 231814 232891 := bstep (se 1 (by rfl) ⟨174668, by rfl⟩ : syracuseStep 232891 = 349337) B349337
theorem B232967 : Blo 231814 232967 := bstep (se 1 (by rfl) ⟨174725, by rfl⟩ : syracuseStep 232967 = 349451) B349451
theorem B232975 : Blo 231814 232975 := bstep (se 1 (by rfl) ⟨174731, by rfl⟩ : syracuseStep 232975 = 349463) B349463
theorem B233019 : Blo 231814 233019 := bstep (se 1 (by rfl) ⟨174764, by rfl⟩ : syracuseStep 233019 = 349529) B349529
theorem B396859 : Blo 231814 396859 := bstep (se 1 (by rfl) ⟨297644, by rfl⟩ : syracuseStep 396859 = 595289) B595289
theorem B1117763 : Blo 231814 1117763 := bstep (se 1 (by rfl) ⟨838322, by rfl⟩ : syracuseStep 1117763 = 1676645) B1676645
theorem B593527 : Blo 231814 593527 := bstep (se 1 (by rfl) ⟨445145, by rfl⟩ : syracuseStep 593527 = 890291) B890291
theorem B331399 : Blo 231814 331399 := bstep (se 1 (by rfl) ⟨248549, by rfl⟩ : syracuseStep 331399 = 497099) B497099
theorem B233095 : Blo 231814 233095 := bstep (se 1 (by rfl) ⟨174821, by rfl⟩ : syracuseStep 233095 = 349643) B349643
theorem B233103 : Blo 231814 233103 := bstep (se 1 (by rfl) ⟨174827, by rfl⟩ : syracuseStep 233103 = 349655) B349655
theorem B233147 : Blo 231814 233147 := bstep (se 1 (by rfl) ⟨174860, by rfl⟩ : syracuseStep 233147 = 349721) B349721
theorem B495305 : Blo 231814 495305 := bstep (se 2 (by rfl) ⟨185739, by rfl⟩ : syracuseStep 495305 = 371479) B371479
theorem B397001 : Blo 231814 397001 := bstep (se 2 (by rfl) ⟨148875, by rfl⟩ : syracuseStep 397001 = 297751) B297751
theorem B233223 : Blo 231814 233223 := bstep (se 1 (by rfl) ⟨174917, by rfl⟩ : syracuseStep 233223 = 349835) B349835
theorem B233231 : Blo 231814 233231 := bstep (se 1 (by rfl) ⟨174923, by rfl⟩ : syracuseStep 233231 = 349847) B349847
theorem B855841 : Blo 231814 855841 := bstep (se 2 (by rfl) ⟨320940, by rfl⟩ : syracuseStep 855841 = 641881) B641881
theorem B233275 : Blo 231814 233275 := bstep (se 1 (by rfl) ⟨174956, by rfl⟩ : syracuseStep 233275 = 349913) B349913
theorem B233351 : Blo 231814 233351 := bstep (se 1 (by rfl) ⟨175013, by rfl⟩ : syracuseStep 233351 = 350027) B350027
theorem B528263 : Blo 231814 528263 := bstep (se 1 (by rfl) ⟨396197, by rfl⟩ : syracuseStep 528263 = 792395) B792395
theorem B233359 : Blo 231814 233359 := bstep (se 1 (by rfl) ⟨175019, by rfl⟩ : syracuseStep 233359 = 350039) B350039
theorem B561043 : Blo 231814 561043 := bstep (se 1 (by rfl) ⟨420782, by rfl⟩ : syracuseStep 561043 = 841565) B841565
theorem B233403 : Blo 231814 233403 := bstep (se 1 (by rfl) ⟨175052, by rfl⟩ : syracuseStep 233403 = 350105) B350105
theorem B233479 : Blo 231814 233479 := bstep (se 1 (by rfl) ⟨175109, by rfl⟩ : syracuseStep 233479 = 350219) B350219
theorem B233487 : Blo 231814 233487 := bstep (se 1 (by rfl) ⟨175115, by rfl⟩ : syracuseStep 233487 = 350231) B350231
theorem B593963 : Blo 231814 593963 := bstep (se 1 (by rfl) ⟨445472, by rfl⟩ : syracuseStep 593963 = 890945) B890945
theorem B233531 : Blo 231814 233531 := bstep (se 1 (by rfl) ⟨175148, by rfl⟩ : syracuseStep 233531 = 350297) B350297
theorem B528443 : Blo 231814 528443 := bstep (se 1 (by rfl) ⟨396332, by rfl⟩ : syracuseStep 528443 = 792665) B792665
theorem B233607 : Blo 231814 233607 := bstep (se 1 (by rfl) ⟨175205, by rfl⟩ : syracuseStep 233607 = 350411) B350411
theorem B233615 : Blo 231814 233615 := bstep (se 1 (by rfl) ⟨175211, by rfl⟩ : syracuseStep 233615 = 350423) B350423
theorem B2691245 : Blo 231814 2691245 := bstep (se 3 (by rfl) ⟨504608, by rfl⟩ : syracuseStep 2691245 = 1009217) B1009217
theorem B528569 : Blo 231814 528569 := bstep (se 2 (by rfl) ⟨198213, by rfl⟩ : syracuseStep 528569 = 396427) B396427
theorem B233659 : Blo 231814 233659 := bstep (se 1 (by rfl) ⟨175244, by rfl⟩ : syracuseStep 233659 = 350489) B350489
theorem B233735 : Blo 231814 233735 := bstep (se 1 (by rfl) ⟨175301, by rfl⟩ : syracuseStep 233735 = 350603) B350603
theorem B233743 : Blo 231814 233743 := bstep (se 1 (by rfl) ⟨175307, by rfl⟩ : syracuseStep 233743 = 350615) B350615
theorem B561467 : Blo 231814 561467 := bstep (se 1 (by rfl) ⟨421100, by rfl⟩ : syracuseStep 561467 = 842201) B842201
theorem B233787 : Blo 231814 233787 := bstep (se 1 (by rfl) ⟨175340, by rfl⟩ : syracuseStep 233787 = 350681) B350681
theorem B332105 : Blo 231814 332105 := bstep (se 2 (by rfl) ⟨124539, by rfl⟩ : syracuseStep 332105 = 249079) B249079
theorem B233863 : Blo 231814 233863 := bstep (se 1 (by rfl) ⟨175397, by rfl⟩ : syracuseStep 233863 = 350795) B350795
theorem B397703 : Blo 231814 397703 := bstep (se 1 (by rfl) ⟨298277, by rfl⟩ : syracuseStep 397703 = 596555) B596555
theorem B233871 : Blo 231814 233871 := bstep (se 1 (by rfl) ⟨175403, by rfl⟩ : syracuseStep 233871 = 350807) B350807
theorem B790937 : Blo 231814 790937 := bstep (se 2 (by rfl) ⟨296601, by rfl⟩ : syracuseStep 790937 = 593203) B593203
theorem B496057 : Blo 231814 496057 := bstep (se 2 (by rfl) ⟨186021, by rfl⟩ : syracuseStep 496057 = 372043) B372043
theorem B332219 : Blo 231814 332219 := bstep (se 1 (by rfl) ⟨249164, by rfl⟩ : syracuseStep 332219 = 498329) B498329
theorem B233915 : Blo 231814 233915 := bstep (se 1 (by rfl) ⟨175436, by rfl⟩ : syracuseStep 233915 = 350873) B350873
theorem B233991 : Blo 231814 233991 := bstep (se 1 (by rfl) ⟨175493, by rfl⟩ : syracuseStep 233991 = 350987) B350987
theorem B233999 : Blo 231814 233999 := bstep (se 1 (by rfl) ⟨175499, by rfl⟩ : syracuseStep 233999 = 350999) B350999
theorem B528911 : Blo 231814 528911 := bstep (se 1 (by rfl) ⟨396683, by rfl⟩ : syracuseStep 528911 = 793367) B793367
theorem B528929 : Blo 231814 528929 := bstep (se 2 (by rfl) ⟨198348, by rfl⟩ : syracuseStep 528929 = 396697) B396697
theorem B234043 : Blo 231814 234043 := bstep (se 1 (by rfl) ⟨175532, by rfl⟩ : syracuseStep 234043 = 351065) B351065
theorem B234119 : Blo 231814 234119 := bstep (se 1 (by rfl) ⟨175589, by rfl⟩ : syracuseStep 234119 = 351179) B351179
theorem B234127 : Blo 231814 234127 := bstep (se 1 (by rfl) ⟨175595, by rfl⟩ : syracuseStep 234127 = 351191) B351191
theorem B8622773 : Blo 231814 8622773 := bstep (se 5 (by rfl) ⟨404192, by rfl⟩ : syracuseStep 8622773 = 808385) B808385
theorem B234171 : Blo 231814 234171 := bstep (se 1 (by rfl) ⟨175628, by rfl⟩ : syracuseStep 234171 = 351257) B351257
theorem B234247 : Blo 231814 234247 := bstep (se 1 (by rfl) ⟨175685, by rfl⟩ : syracuseStep 234247 = 351371) B351371
theorem B234255 : Blo 231814 234255 := bstep (se 1 (by rfl) ⟨175691, by rfl⟩ : syracuseStep 234255 = 351383) B351383
theorem B1774385 : Blo 231814 1774385 := bstep (se 2 (by rfl) ⟨665394, by rfl⟩ : syracuseStep 1774385 = 1330789) B1330789
theorem B234299 : Blo 231814 234299 := bstep (se 1 (by rfl) ⟨175724, by rfl⟩ : syracuseStep 234299 = 351449) B351449
theorem B594803 : Blo 231814 594803 := bstep (se 1 (by rfl) ⟨446102, by rfl⟩ : syracuseStep 594803 = 892205) B892205
theorem B4821875 : Blo 231814 4821875 := bstep (se 1 (by rfl) ⟨3616406, by rfl⟩ : syracuseStep 4821875 = 7232813) B7232813
theorem B529271 : Blo 231814 529271 := bstep (se 1 (by rfl) ⟨396953, by rfl⟩ : syracuseStep 529271 = 793907) B793907
theorem B234375 : Blo 231814 234375 := bstep (se 1 (by rfl) ⟨175781, by rfl⟩ : syracuseStep 234375 = 351563) B351563
theorem B594823 : Blo 231814 594823 := bstep (se 1 (by rfl) ⟨446117, by rfl⟩ : syracuseStep 594823 = 892235) B892235
theorem B234383 : Blo 231814 234383 := bstep (se 1 (by rfl) ⟨175787, by rfl⟩ : syracuseStep 234383 = 351575) B351575
theorem B234427 : Blo 231814 234427 := bstep (se 1 (by rfl) ⟨175820, by rfl⟩ : syracuseStep 234427 = 351641) B351641
theorem B234503 : Blo 231814 234503 := bstep (se 1 (by rfl) ⟨175877, by rfl⟩ : syracuseStep 234503 = 351755) B351755
theorem B234511 : Blo 231814 234511 := bstep (se 1 (by rfl) ⟨175883, by rfl⟩ : syracuseStep 234511 = 351767) B351767
theorem B529451 : Blo 231814 529451 := bstep (se 1 (by rfl) ⟨397088, by rfl⟩ : syracuseStep 529451 = 794177) B794177
theorem B332857 : Blo 231814 332857 := bstep (se 2 (by rfl) ⟨124821, by rfl⟩ : syracuseStep 332857 = 249643) B249643
theorem B234555 : Blo 231814 234555 := bstep (se 1 (by rfl) ⟨175916, by rfl⟩ : syracuseStep 234555 = 351833) B351833
theorem B791639 : Blo 231814 791639 := bstep (se 1 (by rfl) ⟨593729, by rfl⟩ : syracuseStep 791639 = 1187459) B1187459
theorem B234631 : Blo 231814 234631 := bstep (se 1 (by rfl) ⟨175973, by rfl⟩ : syracuseStep 234631 = 351947) B351947
theorem B234639 : Blo 231814 234639 := bstep (se 1 (by rfl) ⟨175979, by rfl⟩ : syracuseStep 234639 = 351959) B351959
theorem B595097 : Blo 231814 595097 := bstep (se 2 (by rfl) ⟨223161, by rfl⟩ : syracuseStep 595097 = 446323) B446323
theorem B234683 : Blo 231814 234683 := bstep (se 1 (by rfl) ⟨176012, by rfl⟩ : syracuseStep 234683 = 352025) B352025
theorem B660737 : Blo 231814 660737 := bstep (se 2 (by rfl) ⟨247776, by rfl⟩ : syracuseStep 660737 = 495553) B495553
theorem B234759 : Blo 231814 234759 := bstep (se 1 (by rfl) ⟨176069, by rfl⟩ : syracuseStep 234759 = 352139) B352139
theorem B234767 : Blo 231814 234767 := bstep (se 1 (by rfl) ⟨176075, by rfl⟩ : syracuseStep 234767 = 352151) B352151
theorem B234811 : Blo 231814 234811 := bstep (se 1 (by rfl) ⟨176108, by rfl⟩ : syracuseStep 234811 = 352217) B352217
theorem B595259 : Blo 231814 595259 := bstep (se 1 (by rfl) ⟨446444, by rfl⟩ : syracuseStep 595259 = 892889) B892889
theorem B234887 : Blo 231814 234887 := bstep (se 1 (by rfl) ⟨176165, by rfl⟩ : syracuseStep 234887 = 352331) B352331
theorem B234895 : Blo 231814 234895 := bstep (se 1 (by rfl) ⟨176171, by rfl⟩ : syracuseStep 234895 = 352343) B352343
theorem B529811 : Blo 231814 529811 := bstep (se 1 (by rfl) ⟨397358, by rfl⟩ : syracuseStep 529811 = 794717) B794717
theorem B234939 : Blo 231814 234939 := bstep (se 1 (by rfl) ⟨176204, by rfl⟩ : syracuseStep 234939 = 352409) B352409
theorem B529865 : Blo 231814 529865 := bstep (se 2 (by rfl) ⟨198699, by rfl⟩ : syracuseStep 529865 = 397399) B397399
theorem B235015 : Blo 231814 235015 := bstep (se 1 (by rfl) ⟨176261, by rfl⟩ : syracuseStep 235015 = 352523) B352523
theorem B235023 : Blo 231814 235023 := bstep (se 1 (by rfl) ⟨176267, by rfl⟩ : syracuseStep 235023 = 352535) B352535
theorem B595471 : Blo 231814 595471 := bstep (se 1 (by rfl) ⟨446603, by rfl⟩ : syracuseStep 595471 = 893207) B893207
theorem B235067 : Blo 231814 235067 := bstep (se 1 (by rfl) ⟨176300, by rfl⟩ : syracuseStep 235067 = 352601) B352601
theorem B792125 : Blo 231814 792125 := bstep (se 3 (by rfl) ⟨148523, by rfl⟩ : syracuseStep 792125 = 297047) B297047
theorem B235143 : Blo 231814 235143 := bstep (se 1 (by rfl) ⟨176357, by rfl⟩ : syracuseStep 235143 = 352715) B352715
theorem B235151 : Blo 231814 235151 := bstep (se 1 (by rfl) ⟨176363, by rfl⟩ : syracuseStep 235151 = 352727) B352727
theorem B235195 : Blo 231814 235195 := bstep (se 1 (by rfl) ⟨176396, by rfl⟩ : syracuseStep 235195 = 352793) B352793
theorem B661193 : Blo 231814 661193 := bstep (se 2 (by rfl) ⟨247947, by rfl⟩ : syracuseStep 661193 = 495895) B495895
theorem B562889 : Blo 231814 562889 := bstep (se 2 (by rfl) ⟨211083, by rfl⟩ : syracuseStep 562889 = 422167) B422167
theorem B235271 : Blo 231814 235271 := bstep (se 1 (by rfl) ⟨176453, by rfl⟩ : syracuseStep 235271 = 352907) B352907
theorem B235279 : Blo 231814 235279 := bstep (se 1 (by rfl) ⟨176459, by rfl⟩ : syracuseStep 235279 = 352919) B352919
theorem B530209 : Blo 231814 530209 := bstep (se 2 (by rfl) ⟨198828, by rfl⟩ : syracuseStep 530209 = 397657) B397657
theorem B497441 : Blo 231814 497441 := bstep (se 2 (by rfl) ⟨186540, by rfl⟩ : syracuseStep 497441 = 373081) B373081
theorem B595745 : Blo 231814 595745 := bstep (se 2 (by rfl) ⟨223404, by rfl⟩ : syracuseStep 595745 = 446809) B446809
theorem B530219 : Blo 231814 530219 := bstep (se 1 (by rfl) ⟨397664, by rfl⟩ : syracuseStep 530219 = 795329) B795329
theorem B235323 : Blo 231814 235323 := bstep (se 1 (by rfl) ⟨176492, by rfl⟩ : syracuseStep 235323 = 352985) B352985
theorem B235399 : Blo 231814 235399 := bstep (se 1 (by rfl) ⟨176549, by rfl⟩ : syracuseStep 235399 = 353099) B353099
theorem B235407 : Blo 231814 235407 := bstep (se 1 (by rfl) ⟨176555, by rfl⟩ : syracuseStep 235407 = 353111) B353111
theorem B890777 : Blo 231814 890777 := bstep (se 2 (by rfl) ⟨334041, by rfl⟩ : syracuseStep 890777 = 668083) B668083
theorem B235451 : Blo 231814 235451 := bstep (se 1 (by rfl) ⟨176588, by rfl⟩ : syracuseStep 235451 = 353177) B353177
theorem B235527 : Blo 231814 235527 := bstep (se 1 (by rfl) ⟨176645, by rfl⟩ : syracuseStep 235527 = 353291) B353291
theorem B235535 : Blo 231814 235535 := bstep (se 1 (by rfl) ⟨176651, by rfl⟩ : syracuseStep 235535 = 353303) B353303
theorem B235579 : Blo 231814 235579 := bstep (se 1 (by rfl) ⟨176684, by rfl⟩ : syracuseStep 235579 = 353369) B353369
theorem B1251389 : Blo 231814 1251389 := bstep (se 3 (by rfl) ⟨234635, by rfl⟩ : syracuseStep 1251389 = 469271) B469271
theorem B235655 : Blo 231814 235655 := bstep (se 1 (by rfl) ⟨176741, by rfl⟩ : syracuseStep 235655 = 353483) B353483
theorem B530567 : Blo 231814 530567 := bstep (se 1 (by rfl) ⟨397925, by rfl⟩ : syracuseStep 530567 = 795851) B795851
theorem B235663 : Blo 231814 235663 := bstep (se 1 (by rfl) ⟨176747, by rfl⟩ : syracuseStep 235663 = 353495) B353495
theorem B235707 : Blo 231814 235707 := bstep (se 1 (by rfl) ⟨176780, by rfl⟩ : syracuseStep 235707 = 353561) B353561
theorem B235783 : Blo 231814 235783 := bstep (se 1 (by rfl) ⟨176837, by rfl⟩ : syracuseStep 235783 = 353675) B353675
theorem B235791 : Blo 231814 235791 := bstep (se 1 (by rfl) ⟨176843, by rfl⟩ : syracuseStep 235791 = 353687) B353687
theorem B563543 : Blo 231814 563543 := bstep (se 1 (by rfl) ⟨422657, by rfl⟩ : syracuseStep 563543 = 845315) B845315
theorem B2529629 : Blo 231814 2529629 := bstep (se 3 (by rfl) ⟨474305, by rfl⟩ : syracuseStep 2529629 = 948611) B948611
theorem B1186163 : Blo 231814 1186163 := bstep (se 1 (by rfl) ⟨889622, by rfl⟩ : syracuseStep 1186163 = 1779245) B1779245
theorem B563831 : Blo 231814 563831 := bstep (se 1 (by rfl) ⟨422873, by rfl⟩ : syracuseStep 563831 = 845747) B845747
theorem B596747 : Blo 231814 596747 := bstep (se 1 (by rfl) ⟨447560, by rfl⟩ : syracuseStep 596747 = 895121) B895121
theorem B1186649 : Blo 231814 1186649 := bstep (se 2 (by rfl) ⟨444993, by rfl⟩ : syracuseStep 1186649 = 889987) B889987
theorem B2235251 : Blo 231814 2235251 := bstep (se 1 (by rfl) ⟨1676438, by rfl⟩ : syracuseStep 2235251 = 3352877) B3352877
theorem B793529 : Blo 231814 793529 := bstep (se 2 (by rfl) ⟨297573, by rfl⟩ : syracuseStep 793529 = 595147) B595147
theorem B662843 : Blo 231814 662843 := bstep (se 1 (by rfl) ⟨497132, by rfl⟩ : syracuseStep 662843 = 994265) B994265
theorem B794123 : Blo 231814 794123 := bstep (se 1 (by rfl) ⟨595592, by rfl⟩ : syracuseStep 794123 = 1191185) B1191185
theorem B597563 : Blo 231814 597563 := bstep (se 1 (by rfl) ⟨448172, by rfl⟩ : syracuseStep 597563 = 896345) B896345
theorem B794231 : Blo 231814 794231 := bstep (se 1 (by rfl) ⟨595673, by rfl⟩ : syracuseStep 794231 = 1191347) B1191347
theorem B335659 : Blo 231814 335659 := bstep (se 1 (by rfl) ⟨251744, by rfl⟩ : syracuseStep 335659 = 503489) B503489
theorem B2662307 : Blo 231814 2662307 := bstep (se 1 (by rfl) ⟨1996730, by rfl⟩ : syracuseStep 2662307 = 3993461) B3993461
theorem B663481 : Blo 231814 663481 := bstep (se 2 (by rfl) ⟨248805, by rfl⟩ : syracuseStep 663481 = 497611) B497611
theorem B794825 : Blo 231814 794825 := bstep (se 2 (by rfl) ⟨298059, by rfl⟩ : syracuseStep 794825 = 596119) B596119
theorem B663869 : Blo 231814 663869 := bstep (se 3 (by rfl) ⟨124475, by rfl⟩ : syracuseStep 663869 = 248951) B248951
theorem B565879 : Blo 231814 565879 := bstep (se 1 (by rfl) ⟨424409, by rfl⟩ : syracuseStep 565879 = 848819) B848819
theorem B795527 : Blo 231814 795527 := bstep (se 1 (by rfl) ⟨596645, by rfl⟩ : syracuseStep 795527 = 1193291) B1193291
theorem B1188755 : Blo 231814 1188755 := bstep (se 1 (by rfl) ⟨891566, by rfl⟩ : syracuseStep 1188755 = 1783133) B1783133
theorem B599329 : Blo 231814 599329 := bstep (se 2 (by rfl) ⟨224748, by rfl⟩ : syracuseStep 599329 = 449497) B449497
theorem B664985 : Blo 231814 664985 := bstep (se 2 (by rfl) ⟨249369, by rfl⟩ : syracuseStep 664985 = 498739) B498739
theorem B894361 : Blo 231814 894361 := bstep (se 2 (by rfl) ⟨335385, by rfl⟩ : syracuseStep 894361 = 670771) B670771
theorem B1320401 : Blo 231814 1320401 := bstep (se 2 (by rfl) ⟨495150, by rfl⟩ : syracuseStep 1320401 = 990301) B990301
theorem B1418953 : Blo 231814 1418953 := bstep (se 2 (by rfl) ⟨532107, by rfl⟩ : syracuseStep 1418953 = 1064215) B1064215
theorem B894665 : Blo 231814 894665 := bstep (se 2 (by rfl) ⟨335499, by rfl⟩ : syracuseStep 894665 = 670999) B670999
theorem B1320857 : Blo 231814 1320857 := bstep (se 2 (by rfl) ⟨495321, by rfl⟩ : syracuseStep 1320857 = 990643) B990643
theorem B2238941 : Blo 231814 2238941 := bstep (se 3 (by rfl) ⟨419801, by rfl⟩ : syracuseStep 2238941 = 839603) B839603
theorem B633359 : Blo 231814 633359 := bstep (se 1 (by rfl) ⟨475019, by rfl⟩ : syracuseStep 633359 = 950039) B950039
theorem B895607 : Blo 231814 895607 := bstep (se 1 (by rfl) ⟨671705, by rfl⟩ : syracuseStep 895607 = 1343411) B1343411
theorem B666397 : Blo 231814 666397 := bstep (se 3 (by rfl) ⟨124949, by rfl⟩ : syracuseStep 666397 = 249899) B249899
theorem B666569 : Blo 231814 666569 := bstep (se 2 (by rfl) ⟨249963, by rfl⟩ : syracuseStep 666569 = 499927) B499927
theorem B666625 : Blo 231814 666625 := bstep (se 2 (by rfl) ⟨249984, by rfl⟩ : syracuseStep 666625 = 499969) B499969
theorem B666967 : Blo 231814 666967 := bstep (se 1 (by rfl) ⟨500225, by rfl⟩ : syracuseStep 666967 = 1000451) B1000451
theorem B994675 : Blo 231814 994675 := bstep (se 1 (by rfl) ⟨746006, by rfl⟩ : syracuseStep 994675 = 1492013) B1492013
theorem B634483 : Blo 231814 634483 := bstep (se 1 (by rfl) ⟨475862, by rfl⟩ : syracuseStep 634483 = 951725) B951725
theorem B1420919 : Blo 231814 1420919 := bstep (se 1 (by rfl) ⟨1065689, by rfl⟩ : syracuseStep 1420919 = 2131379) B2131379
theorem B2010743 : Blo 231814 2010743 := bstep (se 1 (by rfl) ⟨1508057, by rfl⟩ : syracuseStep 2010743 = 3016115) B3016115
theorem B995017 : Blo 231814 995017 := bstep (se 2 (by rfl) ⟨373131, by rfl⟩ : syracuseStep 995017 = 746263) B746263
theorem B1191833 : Blo 231814 1191833 := bstep (se 2 (by rfl) ⟨446937, by rfl⟩ : syracuseStep 1191833 = 893875) B893875
theorem B1782161 : Blo 231814 1782161 := bstep (se 2 (by rfl) ⟨668310, by rfl⟩ : syracuseStep 1782161 = 1336621) B1336621
theorem B996077 : Blo 231814 996077 := bstep (se 3 (by rfl) ⟨186764, by rfl⟩ : syracuseStep 996077 = 373529) B373529
theorem B537377 : Blo 231814 537377 := bstep (se 2 (by rfl) ⟨201516, by rfl⟩ : syracuseStep 537377 = 403033) B403033
theorem B1127353 : Blo 231814 1127353 := bstep (se 2 (by rfl) ⟨422757, by rfl⟩ : syracuseStep 1127353 = 845515) B845515
theorem B1127467 : Blo 231814 1127467 := bstep (se 1 (by rfl) ⟨845600, by rfl⟩ : syracuseStep 1127467 = 1691201) B1691201
theorem B603251 : Blo 231814 603251 := bstep (se 1 (by rfl) ⟨452438, by rfl⟩ : syracuseStep 603251 = 904877) B904877
theorem B3225091 : Blo 231814 3225091 := bstep (se 1 (by rfl) ⟨2418818, by rfl⟩ : syracuseStep 3225091 = 4837637) B4837637
theorem B374843 : Blo 231814 374843 := bstep (se 1 (by rfl) ⟨281132, by rfl⟩ : syracuseStep 374843 = 562265) B562265
theorem B669815 : Blo 231814 669815 := bstep (se 1 (by rfl) ⟨502361, by rfl⟩ : syracuseStep 669815 = 1004723) B1004723
theorem B440635 : Blo 231814 440635 := bstep (se 1 (by rfl) ⟨330476, by rfl⟩ : syracuseStep 440635 = 660953) B660953
theorem B440711 : Blo 231814 440711 := bstep (se 1 (by rfl) ⟨330533, by rfl⟩ : syracuseStep 440711 = 661067) B661067
theorem B506515 : Blo 231814 506515 := bstep (se 1 (by rfl) ⟨379886, by rfl⟩ : syracuseStep 506515 = 759773) B759773
theorem B1784591 : Blo 231814 1784591 := bstep (se 1 (by rfl) ⟨1338443, by rfl⟩ : syracuseStep 1784591 = 2676887) B2676887
theorem B441121 : Blo 231814 441121 := bstep (se 2 (by rfl) ⟨165420, by rfl⟩ : syracuseStep 441121 = 330841) B330841
theorem B3390245 : Blo 231814 3390245 := bstep (se 4 (by rfl) ⟨317835, by rfl⟩ : syracuseStep 3390245 = 635671) B635671
theorem B5389145 : Blo 231814 5389145 := bstep (se 2 (by rfl) ⟨2020929, by rfl⟩ : syracuseStep 5389145 = 4041859) B4041859
theorem B1588247 : Blo 231814 1588247 := bstep (se 1 (by rfl) ⟨1191185, by rfl⟩ : syracuseStep 1588247 = 2382371) B2382371
theorem B441463 : Blo 231814 441463 := bstep (se 1 (by rfl) ⟨331097, by rfl⟩ : syracuseStep 441463 = 662195) B662195
theorem B802333 : Blo 231814 802333 := bstep (se 3 (by rfl) ⟨150437, by rfl⟩ : syracuseStep 802333 = 300875) B300875
theorem B671291 : Blo 231814 671291 := bstep (se 1 (by rfl) ⟨503468, by rfl⟩ : syracuseStep 671291 = 1006937) B1006937
theorem B474743 : Blo 231814 474743 := bstep (se 1 (by rfl) ⟨356057, by rfl⟩ : syracuseStep 474743 = 712115) B712115
theorem B2539313 : Blo 231814 2539313 := bstep (se 2 (by rfl) ⟨952242, by rfl⟩ : syracuseStep 2539313 = 1904485) B1904485
theorem B3063703 : Blo 231814 3063703 := bstep (se 1 (by rfl) ⟨2297777, by rfl⟩ : syracuseStep 3063703 = 4595555) B4595555
theorem B901181 : Blo 231814 901181 := bstep (se 3 (by rfl) ⟨168971, by rfl⟩ : syracuseStep 901181 = 337943) B337943
theorem B377207 : Blo 231814 377207 := bstep (se 1 (by rfl) ⟨282905, by rfl⟩ : syracuseStep 377207 = 565811) B565811
theorem B443065 : Blo 231814 443065 := bstep (se 2 (by rfl) ⟨166149, by rfl⟩ : syracuseStep 443065 = 332299) B332299
theorem B2540261 : Blo 231814 2540261 := bstep (se 4 (by rfl) ⟨238149, by rfl⟩ : syracuseStep 2540261 = 476299) B476299
theorem B1327873 : Blo 231814 1327873 := bstep (se 2 (by rfl) ⟨497952, by rfl⟩ : syracuseStep 1327873 = 995905) B995905
theorem B1131353 : Blo 231814 1131353 := bstep (se 2 (by rfl) ⟨424257, by rfl⟩ : syracuseStep 1131353 = 848515) B848515
theorem B1950617 : Blo 231814 1950617 := bstep (se 2 (by rfl) ⟨731481, by rfl⟩ : syracuseStep 1950617 = 1462963) B1462963
theorem B443407 : Blo 231814 443407 := bstep (se 1 (by rfl) ⟨332555, by rfl⟩ : syracuseStep 443407 = 665111) B665111
theorem B1328399 : Blo 231814 1328399 := bstep (se 1 (by rfl) ⟨996299, by rfl⟩ : syracuseStep 1328399 = 1992599) B1992599
theorem B444295 : Blo 231814 444295 := bstep (se 1 (by rfl) ⟨333221, by rfl⟩ : syracuseStep 444295 = 666443) B666443
theorem B1427543 : Blo 231814 1427543 := bstep (se 1 (by rfl) ⟨1070657, by rfl⟩ : syracuseStep 1427543 = 2141315) B2141315
theorem B248071 : Blo 231814 248071 := bstep (se 1 (by rfl) ⟨186053, by rfl⟩ : syracuseStep 248071 = 372107) B372107
theorem B1133003 : Blo 231814 1133003 := bstep (se 1 (by rfl) ⟨849752, by rfl⟩ : syracuseStep 1133003 = 1699505) B1699505
theorem B1428029 : Blo 231814 1428029 := bstep (se 3 (by rfl) ⟨267755, by rfl⟩ : syracuseStep 1428029 = 535511) B535511
theorem B1329857 : Blo 231814 1329857 := bstep (se 2 (by rfl) ⟨498696, by rfl⟩ : syracuseStep 1329857 = 997393) B997393
theorem B2542337 : Blo 231814 2542337 := bstep (se 2 (by rfl) ⟨953376, by rfl⟩ : syracuseStep 2542337 = 1906753) B1906753
theorem B1690483 : Blo 231814 1690483 := bstep (se 1 (by rfl) ⟨1267862, by rfl⟩ : syracuseStep 1690483 = 2535725) B2535725
theorem B1493963 : Blo 231814 1493963 := bstep (se 1 (by rfl) ⟨1120472, by rfl⟩ : syracuseStep 1493963 = 2240945) B2240945
theorem B248891 : Blo 231814 248891 := bstep (se 1 (by rfl) ⟨186668, by rfl⟩ : syracuseStep 248891 = 373337) B373337
theorem B805949 : Blo 231814 805949 := bstep (se 3 (by rfl) ⟨151115, by rfl⟩ : syracuseStep 805949 = 302231) B302231
theorem B1887623 : Blo 231814 1887623 := bstep (se 1 (by rfl) ⟨1415717, by rfl⟩ : syracuseStep 1887623 = 2831435) B2831435
theorem B642505 : Blo 231814 642505 := bstep (se 2 (by rfl) ⟨240939, by rfl⟩ : syracuseStep 642505 = 481879) B481879
theorem B773675 : Blo 231814 773675 := bstep (se 1 (by rfl) ⟨580256, by rfl⟩ : syracuseStep 773675 = 1160513) B1160513
theorem B347783 : Blo 231814 347783 := bstep (se 1 (by rfl) ⟨260837, by rfl⟩ : syracuseStep 347783 = 521675) B521675
theorem B446087 : Blo 231814 446087 := bstep (se 1 (by rfl) ⟨334565, by rfl⟩ : syracuseStep 446087 = 669131) B669131
theorem B347819 : Blo 231814 347819 := bstep (se 1 (by rfl) ⟨260864, by rfl⟩ : syracuseStep 347819 = 521729) B521729
theorem B347849 : Blo 231814 347849 := bstep (se 2 (by rfl) ⟨130443, by rfl⟩ : syracuseStep 347849 = 260887) B260887
theorem B347963 : Blo 231814 347963 := bstep (se 1 (by rfl) ⟨260972, by rfl⟩ : syracuseStep 347963 = 521945) B521945
theorem B348023 : Blo 231814 348023 := bstep (se 1 (by rfl) ⟨261017, by rfl⟩ : syracuseStep 348023 = 522035) B522035
theorem B348047 : Blo 231814 348047 := bstep (se 1 (by rfl) ⟨261035, by rfl⟩ : syracuseStep 348047 = 522071) B522071
theorem B348089 : Blo 231814 348089 := bstep (se 2 (by rfl) ⟨130533, by rfl⟩ : syracuseStep 348089 = 261067) B261067
theorem B348167 : Blo 231814 348167 := bstep (se 1 (by rfl) ⟨261125, by rfl⟩ : syracuseStep 348167 = 522251) B522251
theorem B348203 : Blo 231814 348203 := bstep (se 1 (by rfl) ⟨261152, by rfl⟩ : syracuseStep 348203 = 522305) B522305
theorem B348233 : Blo 231814 348233 := bstep (se 2 (by rfl) ⟨130587, by rfl⟩ : syracuseStep 348233 = 261175) B261175
theorem B1790039 : Blo 231814 1790039 := bstep (se 1 (by rfl) ⟨1342529, by rfl⟩ : syracuseStep 1790039 = 2685059) B2685059
theorem B1200215 : Blo 231814 1200215 := bstep (se 1 (by rfl) ⟨900161, by rfl⟩ : syracuseStep 1200215 = 1800323) B1800323
theorem B348347 : Blo 231814 348347 := bstep (se 1 (by rfl) ⟨261260, by rfl⟩ : syracuseStep 348347 = 522521) B522521
theorem B348407 : Blo 231814 348407 := bstep (se 1 (by rfl) ⟨261305, by rfl⟩ : syracuseStep 348407 = 522611) B522611
theorem B348431 : Blo 231814 348431 := bstep (se 1 (by rfl) ⟨261323, by rfl⟩ : syracuseStep 348431 = 522647) B522647
theorem B348473 : Blo 231814 348473 := bstep (se 2 (by rfl) ⟨130677, by rfl⟩ : syracuseStep 348473 = 261355) B261355
theorem B348551 : Blo 231814 348551 := bstep (se 1 (by rfl) ⟨261413, by rfl⟩ : syracuseStep 348551 = 522827) B522827
theorem B348587 : Blo 231814 348587 := bstep (se 1 (by rfl) ⟨261440, by rfl⟩ : syracuseStep 348587 = 522881) B522881
theorem B348617 : Blo 231814 348617 := bstep (se 2 (by rfl) ⟨130731, by rfl⟩ : syracuseStep 348617 = 261463) B261463
theorem B18469397 : Blo 231814 18469397 := bstep (se 6 (by rfl) ⟨432876, by rfl⟩ : syracuseStep 18469397 = 865753) B865753
theorem B348731 : Blo 231814 348731 := bstep (se 1 (by rfl) ⟨261548, by rfl⟩ : syracuseStep 348731 = 523097) B523097
theorem B1200707 : Blo 231814 1200707 := bstep (se 1 (by rfl) ⟨900530, by rfl⟩ : syracuseStep 1200707 = 1801061) B1801061
theorem B348791 : Blo 231814 348791 := bstep (se 1 (by rfl) ⟨261593, by rfl⟩ : syracuseStep 348791 = 523187) B523187
theorem B348815 : Blo 231814 348815 := bstep (se 1 (by rfl) ⟨261611, by rfl⟩ : syracuseStep 348815 = 523223) B523223
theorem B348857 : Blo 231814 348857 := bstep (se 2 (by rfl) ⟨130821, by rfl⟩ : syracuseStep 348857 = 261643) B261643
theorem B2675429 : Blo 231814 2675429 := bstep (se 4 (by rfl) ⟨250821, by rfl⟩ : syracuseStep 2675429 = 501643) B501643
theorem B348935 : Blo 231814 348935 := bstep (se 1 (by rfl) ⟨261701, by rfl⟩ : syracuseStep 348935 = 523403) B523403
theorem B348971 : Blo 231814 348971 := bstep (se 1 (by rfl) ⟨261728, by rfl⟩ : syracuseStep 348971 = 523457) B523457
theorem B349001 : Blo 231814 349001 := bstep (se 2 (by rfl) ⟨130875, by rfl⟩ : syracuseStep 349001 = 261751) B261751
theorem B349115 : Blo 231814 349115 := bstep (se 1 (by rfl) ⟨261836, by rfl⟩ : syracuseStep 349115 = 523673) B523673
theorem B644041 : Blo 231814 644041 := bstep (se 2 (by rfl) ⟨241515, by rfl⟩ : syracuseStep 644041 = 483031) B483031
theorem B349175 : Blo 231814 349175 := bstep (se 1 (by rfl) ⟨261881, by rfl⟩ : syracuseStep 349175 = 523763) B523763
theorem B349199 : Blo 231814 349199 := bstep (se 1 (by rfl) ⟨261899, by rfl⟩ : syracuseStep 349199 = 523799) B523799
theorem B1332247 : Blo 231814 1332247 := bstep (se 1 (by rfl) ⟨999185, by rfl⟩ : syracuseStep 1332247 = 1998371) B1998371
theorem B349241 : Blo 231814 349241 := bstep (se 2 (by rfl) ⟨130965, by rfl⟩ : syracuseStep 349241 = 261931) B261931
theorem B349319 : Blo 231814 349319 := bstep (se 1 (by rfl) ⟨261989, by rfl⟩ : syracuseStep 349319 = 523979) B523979
theorem B447635 : Blo 231814 447635 := bstep (se 1 (by rfl) ⟨335726, by rfl⟩ : syracuseStep 447635 = 671453) B671453
theorem B349355 : Blo 231814 349355 := bstep (se 1 (by rfl) ⟨262016, by rfl⟩ : syracuseStep 349355 = 524033) B524033
theorem B349385 : Blo 231814 349385 := bstep (se 2 (by rfl) ⟨131019, by rfl⟩ : syracuseStep 349385 = 262039) B262039
theorem B742715 : Blo 231814 742715 := bstep (se 1 (by rfl) ⟨557036, by rfl⟩ : syracuseStep 742715 = 1114073) B1114073
theorem B349499 : Blo 231814 349499 := bstep (se 1 (by rfl) ⟨262124, by rfl⟩ : syracuseStep 349499 = 524249) B524249
theorem B1430843 : Blo 231814 1430843 := bstep (se 1 (by rfl) ⟨1073132, by rfl⟩ : syracuseStep 1430843 = 2146265) B2146265
theorem B349559 : Blo 231814 349559 := bstep (se 1 (by rfl) ⟨262169, by rfl⟩ : syracuseStep 349559 = 524339) B524339
theorem B349583 : Blo 231814 349583 := bstep (se 1 (by rfl) ⟨262187, by rfl⟩ : syracuseStep 349583 = 524375) B524375
theorem B5854643 : Blo 231814 5854643 := bstep (se 1 (by rfl) ⟨4390982, by rfl⟩ : syracuseStep 5854643 = 8781965) B8781965
theorem B349625 : Blo 231814 349625 := bstep (se 2 (by rfl) ⟨131109, by rfl⟩ : syracuseStep 349625 = 262219) B262219
theorem B4871609 : Blo 231814 4871609 := bstep (se 2 (by rfl) ⟨1826853, by rfl⟩ : syracuseStep 4871609 = 3653707) B3653707
theorem B349703 : Blo 231814 349703 := bstep (se 1 (by rfl) ⟨262277, by rfl⟩ : syracuseStep 349703 = 524555) B524555
theorem B349739 : Blo 231814 349739 := bstep (se 1 (by rfl) ⟨262304, by rfl⟩ : syracuseStep 349739 = 524609) B524609
theorem B349769 : Blo 231814 349769 := bstep (se 2 (by rfl) ⟨131163, by rfl⟩ : syracuseStep 349769 = 262327) B262327
theorem B2971313 : Blo 231814 2971313 := bstep (se 2 (by rfl) ⟨1114242, by rfl⟩ : syracuseStep 2971313 = 2228485) B2228485
theorem B349883 : Blo 231814 349883 := bstep (se 1 (by rfl) ⟨262412, by rfl⟩ : syracuseStep 349883 = 524825) B524825
theorem B349943 : Blo 231814 349943 := bstep (se 1 (by rfl) ⟨262457, by rfl⟩ : syracuseStep 349943 = 524915) B524915
theorem B349967 : Blo 231814 349967 := bstep (se 1 (by rfl) ⟨262475, by rfl⟩ : syracuseStep 349967 = 524951) B524951
theorem B350009 : Blo 231814 350009 := bstep (se 2 (by rfl) ⟨131253, by rfl⟩ : syracuseStep 350009 = 262507) B262507
theorem B350087 : Blo 231814 350087 := bstep (se 1 (by rfl) ⟨262565, by rfl⟩ : syracuseStep 350087 = 525131) B525131
theorem B350123 : Blo 231814 350123 := bstep (se 1 (by rfl) ⟨262592, by rfl⟩ : syracuseStep 350123 = 525185) B525185
theorem B350153 : Blo 231814 350153 := bstep (se 2 (by rfl) ⟨131307, by rfl⟩ : syracuseStep 350153 = 262615) B262615
theorem B710657 : Blo 231814 710657 := bstep (se 2 (by rfl) ⟨266496, by rfl⟩ : syracuseStep 710657 = 532993) B532993
theorem B350267 : Blo 231814 350267 := bstep (se 1 (by rfl) ⟨262700, by rfl⟩ : syracuseStep 350267 = 525401) B525401
theorem B350327 : Blo 231814 350327 := bstep (se 1 (by rfl) ⟨262745, by rfl⟩ : syracuseStep 350327 = 525491) B525491
theorem B350351 : Blo 231814 350351 := bstep (se 1 (by rfl) ⟨262763, by rfl⟩ : syracuseStep 350351 = 525527) B525527
theorem B350393 : Blo 231814 350393 := bstep (se 2 (by rfl) ⟨131397, by rfl⟩ : syracuseStep 350393 = 262795) B262795
theorem B2840777 : Blo 231814 2840777 := bstep (se 2 (by rfl) ⟨1065291, by rfl⟩ : syracuseStep 2840777 = 2130583) B2130583
theorem B350471 : Blo 231814 350471 := bstep (se 1 (by rfl) ⟨262853, by rfl⟩ : syracuseStep 350471 = 525707) B525707
theorem B350507 : Blo 231814 350507 := bstep (se 1 (by rfl) ⟨262880, by rfl⟩ : syracuseStep 350507 = 525761) B525761
theorem B350537 : Blo 231814 350537 := bstep (se 2 (by rfl) ⟨131451, by rfl⟩ : syracuseStep 350537 = 262903) B262903
theorem B350651 : Blo 231814 350651 := bstep (se 1 (by rfl) ⟨262988, by rfl⟩ : syracuseStep 350651 = 525977) B525977
theorem B350711 : Blo 231814 350711 := bstep (se 1 (by rfl) ⟨263033, by rfl⟩ : syracuseStep 350711 = 526067) B526067
theorem B1432075 : Blo 231814 1432075 := bstep (se 1 (by rfl) ⟨1074056, by rfl⟩ : syracuseStep 1432075 = 2148113) B2148113
theorem B350735 : Blo 231814 350735 := bstep (se 1 (by rfl) ⟨263051, by rfl⟩ : syracuseStep 350735 = 526103) B526103
theorem B1399319 : Blo 231814 1399319 := bstep (se 1 (by rfl) ⟨1049489, by rfl⟩ : syracuseStep 1399319 = 2098979) B2098979
theorem B350777 : Blo 231814 350777 := bstep (se 2 (by rfl) ⟨131541, by rfl⟩ : syracuseStep 350777 = 263083) B263083
theorem B1006141 : Blo 231814 1006141 := bstep (se 3 (by rfl) ⟨188651, by rfl⟩ : syracuseStep 1006141 = 377303) B377303
theorem B350855 : Blo 231814 350855 := bstep (se 1 (by rfl) ⟨263141, by rfl⟩ : syracuseStep 350855 = 526283) B526283
theorem B350891 : Blo 231814 350891 := bstep (se 1 (by rfl) ⟨263168, by rfl⟩ : syracuseStep 350891 = 526337) B526337
theorem B350921 : Blo 231814 350921 := bstep (se 2 (by rfl) ⟨131595, by rfl⟩ : syracuseStep 350921 = 263191) B263191
theorem B940859 : Blo 231814 940859 := bstep (se 1 (by rfl) ⟨705644, by rfl⟩ : syracuseStep 940859 = 1411289) B1411289
theorem B351035 : Blo 231814 351035 := bstep (se 1 (by rfl) ⟨263276, by rfl⟩ : syracuseStep 351035 = 526553) B526553
theorem B2644811 : Blo 231814 2644811 := bstep (se 1 (by rfl) ⟨1983608, by rfl⟩ : syracuseStep 2644811 = 3967217) B3967217
theorem B351095 : Blo 231814 351095 := bstep (se 1 (by rfl) ⟨263321, by rfl⟩ : syracuseStep 351095 = 526643) B526643
theorem B351119 : Blo 231814 351119 := bstep (se 1 (by rfl) ⟨263339, by rfl⟩ : syracuseStep 351119 = 526679) B526679
theorem B351161 : Blo 231814 351161 := bstep (se 2 (by rfl) ⟨131685, by rfl⟩ : syracuseStep 351161 = 263371) B263371
theorem B351239 : Blo 231814 351239 := bstep (se 1 (by rfl) ⟨263429, by rfl⟩ : syracuseStep 351239 = 526859) B526859
theorem B351275 : Blo 231814 351275 := bstep (se 1 (by rfl) ⟨263456, by rfl⟩ : syracuseStep 351275 = 526913) B526913
theorem B351305 : Blo 231814 351305 := bstep (se 2 (by rfl) ⟨131739, by rfl⟩ : syracuseStep 351305 = 263479) B263479
theorem B351419 : Blo 231814 351419 := bstep (se 1 (by rfl) ⟨263564, by rfl⟩ : syracuseStep 351419 = 527129) B527129
theorem B318665 : Blo 231814 318665 := bstep (se 2 (by rfl) ⟨119499, by rfl⟩ : syracuseStep 318665 = 238999) B238999
theorem B351479 : Blo 231814 351479 := bstep (se 1 (by rfl) ⟨263609, by rfl⟩ : syracuseStep 351479 = 527219) B527219
theorem B351503 : Blo 231814 351503 := bstep (se 1 (by rfl) ⟨263627, by rfl⟩ : syracuseStep 351503 = 527255) B527255
theorem B941345 : Blo 231814 941345 := bstep (se 2 (by rfl) ⟨353004, by rfl⟩ : syracuseStep 941345 = 706009) B706009
theorem B351545 : Blo 231814 351545 := bstep (se 2 (by rfl) ⟨131829, by rfl⟩ : syracuseStep 351545 = 263659) B263659
theorem B1334663 : Blo 231814 1334663 := bstep (se 1 (by rfl) ⟨1000997, by rfl⟩ : syracuseStep 1334663 = 2001995) B2001995
theorem B351623 : Blo 231814 351623 := bstep (se 1 (by rfl) ⟨263717, by rfl⟩ : syracuseStep 351623 = 527435) B527435
theorem B351659 : Blo 231814 351659 := bstep (se 1 (by rfl) ⟨263744, by rfl⟩ : syracuseStep 351659 = 527489) B527489
theorem B351689 : Blo 231814 351689 := bstep (se 2 (by rfl) ⟨131883, by rfl⟩ : syracuseStep 351689 = 263767) B263767
theorem B351803 : Blo 231814 351803 := bstep (se 1 (by rfl) ⟨263852, by rfl⟩ : syracuseStep 351803 = 527705) B527705
theorem B351863 : Blo 231814 351863 := bstep (se 1 (by rfl) ⟨263897, by rfl⟩ : syracuseStep 351863 = 527795) B527795
theorem B351887 : Blo 231814 351887 := bstep (se 1 (by rfl) ⟨263915, by rfl⟩ : syracuseStep 351887 = 527831) B527831
theorem B2612915 : Blo 231814 2612915 := bstep (se 1 (by rfl) ⟨1959686, by rfl⟩ : syracuseStep 2612915 = 3919373) B3919373
theorem B351929 : Blo 231814 351929 := bstep (se 2 (by rfl) ⟨131973, by rfl⟩ : syracuseStep 351929 = 263947) B263947
theorem B352007 : Blo 231814 352007 := bstep (se 1 (by rfl) ⟨264005, by rfl⟩ : syracuseStep 352007 = 528011) B528011
theorem B352043 : Blo 231814 352043 := bstep (se 1 (by rfl) ⟨264032, by rfl⟩ : syracuseStep 352043 = 528065) B528065
theorem B352073 : Blo 231814 352073 := bstep (se 2 (by rfl) ⟨132027, by rfl⟩ : syracuseStep 352073 = 264055) B264055
theorem B941959 : Blo 231814 941959 := bstep (se 1 (by rfl) ⟨706469, by rfl⟩ : syracuseStep 941959 = 1412939) B1412939
theorem B352187 : Blo 231814 352187 := bstep (se 1 (by rfl) ⟨264140, by rfl⟩ : syracuseStep 352187 = 528281) B528281
theorem B352247 : Blo 231814 352247 := bstep (se 1 (by rfl) ⟨264185, by rfl⟩ : syracuseStep 352247 = 528371) B528371
theorem B745483 : Blo 231814 745483 := bstep (se 1 (by rfl) ⟨559112, by rfl⟩ : syracuseStep 745483 = 1118225) B1118225
theorem B352271 : Blo 231814 352271 := bstep (se 1 (by rfl) ⟨264203, by rfl⟩ : syracuseStep 352271 = 528407) B528407
theorem B352313 : Blo 231814 352313 := bstep (se 2 (by rfl) ⟨132117, by rfl⟩ : syracuseStep 352313 = 264235) B264235
theorem B352391 : Blo 231814 352391 := bstep (se 1 (by rfl) ⟨264293, by rfl⟩ : syracuseStep 352391 = 528587) B528587
theorem B352427 : Blo 231814 352427 := bstep (se 1 (by rfl) ⟨264320, by rfl⟩ : syracuseStep 352427 = 528641) B528641
theorem B352457 : Blo 231814 352457 := bstep (se 2 (by rfl) ⟨132171, by rfl⟩ : syracuseStep 352457 = 264343) B264343
theorem B2253089 : Blo 231814 2253089 := bstep (se 2 (by rfl) ⟨844908, by rfl⟩ : syracuseStep 2253089 = 1689817) B1689817
theorem B352571 : Blo 231814 352571 := bstep (se 1 (by rfl) ⟨264428, by rfl⟩ : syracuseStep 352571 = 528857) B528857
theorem B352631 : Blo 231814 352631 := bstep (se 1 (by rfl) ⟨264473, by rfl⟩ : syracuseStep 352631 = 528947) B528947
theorem B352655 : Blo 231814 352655 := bstep (se 1 (by rfl) ⟨264491, by rfl⟩ : syracuseStep 352655 = 528983) B528983
theorem B352697 : Blo 231814 352697 := bstep (se 2 (by rfl) ⟨132261, by rfl⟩ : syracuseStep 352697 = 264523) B264523
theorem B352775 : Blo 231814 352775 := bstep (se 1 (by rfl) ⟨264581, by rfl⟩ : syracuseStep 352775 = 529163) B529163
theorem B352811 : Blo 231814 352811 := bstep (se 1 (by rfl) ⟨264608, by rfl⟩ : syracuseStep 352811 = 529217) B529217
theorem B352841 : Blo 231814 352841 := bstep (se 2 (by rfl) ⟨132315, by rfl⟩ : syracuseStep 352841 = 264631) B264631
theorem B713369 : Blo 231814 713369 := bstep (se 2 (by rfl) ⟨267513, by rfl⟩ : syracuseStep 713369 = 535027) B535027
theorem B352955 : Blo 231814 352955 := bstep (se 1 (by rfl) ⟨264716, by rfl⟩ : syracuseStep 352955 = 529433) B529433
theorem B353015 : Blo 231814 353015 := bstep (se 1 (by rfl) ⟨264761, by rfl⟩ : syracuseStep 353015 = 529523) B529523
theorem B353039 : Blo 231814 353039 := bstep (se 1 (by rfl) ⟨264779, by rfl⟩ : syracuseStep 353039 = 529559) B529559
theorem B353081 : Blo 231814 353081 := bstep (se 2 (by rfl) ⟨132405, by rfl⟩ : syracuseStep 353081 = 264811) B264811
theorem B353159 : Blo 231814 353159 := bstep (se 1 (by rfl) ⟨264869, by rfl⟩ : syracuseStep 353159 = 529739) B529739
theorem B353195 : Blo 231814 353195 := bstep (se 1 (by rfl) ⟨264896, by rfl⟩ : syracuseStep 353195 = 529793) B529793
theorem B353225 : Blo 231814 353225 := bstep (se 2 (by rfl) ⟨132459, by rfl⟩ : syracuseStep 353225 = 264919) B264919
theorem B353339 : Blo 231814 353339 := bstep (se 1 (by rfl) ⟨265004, by rfl⟩ : syracuseStep 353339 = 530009) B530009
theorem B1336439 : Blo 231814 1336439 := bstep (se 1 (by rfl) ⟨1002329, by rfl⟩ : syracuseStep 1336439 = 2004659) B2004659
theorem B353399 : Blo 231814 353399 := bstep (se 1 (by rfl) ⟨265049, by rfl⟩ : syracuseStep 353399 = 530099) B530099
theorem B353423 : Blo 231814 353423 := bstep (se 1 (by rfl) ⟨265067, by rfl⟩ : syracuseStep 353423 = 530135) B530135
theorem B353465 : Blo 231814 353465 := bstep (se 2 (by rfl) ⟨132549, by rfl⟩ : syracuseStep 353465 = 265099) B265099
theorem B353543 : Blo 231814 353543 := bstep (se 1 (by rfl) ⟨265157, by rfl⟩ : syracuseStep 353543 = 530315) B530315
theorem B451883 : Blo 231814 451883 := bstep (se 1 (by rfl) ⟨338912, by rfl⟩ : syracuseStep 451883 = 677825) B677825
theorem B353579 : Blo 231814 353579 := bstep (se 1 (by rfl) ⟨265184, by rfl⟩ : syracuseStep 353579 = 530369) B530369
theorem B353609 : Blo 231814 353609 := bstep (se 2 (by rfl) ⟨132603, by rfl⟩ : syracuseStep 353609 = 265207) B265207
theorem B1992221 : Blo 231814 1992221 := bstep (se 3 (by rfl) ⟨373541, by rfl⟩ : syracuseStep 1992221 = 747083) B747083
theorem B353977 : Blo 231814 353977 := bstep (se 2 (by rfl) ⟨132741, by rfl⟩ : syracuseStep 353977 = 265483) B265483
theorem B1337147 : Blo 231814 1337147 := bstep (se 1 (by rfl) ⟨1002860, by rfl⟩ : syracuseStep 1337147 = 2005721) B2005721
theorem B2582387 : Blo 231814 2582387 := bstep (se 1 (by rfl) ⟨1936790, by rfl⟩ : syracuseStep 2582387 = 3873581) B3873581
theorem B5433389 : Blo 231814 5433389 := bstep (se 3 (by rfl) ⟨1018760, by rfl⟩ : syracuseStep 5433389 = 2037521) B2037521
theorem B10152053 : Blo 231814 10152053 := bstep (se 5 (by rfl) ⟨475877, by rfl⟩ : syracuseStep 10152053 = 951755) B951755
theorem B1599689 : Blo 231814 1599689 := bstep (se 2 (by rfl) ⟨599883, by rfl⟩ : syracuseStep 1599689 = 1199767) B1199767
theorem B1501649 : Blo 231814 1501649 := bstep (se 2 (by rfl) ⟨563118, by rfl⟩ : syracuseStep 1501649 = 1126237) B1126237
theorem B3369437 : Blo 231814 3369437 := bstep (se 3 (by rfl) ⟨631769, by rfl⟩ : syracuseStep 3369437 = 1263539) B1263539
theorem B715351 : Blo 231814 715351 := bstep (se 1 (by rfl) ⟨536513, by rfl⟩ : syracuseStep 715351 = 1073027) B1073027
theorem B1436467 : Blo 231814 1436467 := bstep (se 1 (by rfl) ⟨1077350, by rfl⟩ : syracuseStep 1436467 = 2154701) B2154701
theorem B1338605 : Blo 231814 1338605 := bstep (se 3 (by rfl) ⟨250988, by rfl⟩ : syracuseStep 1338605 = 501977) B501977
theorem B4321073 : Blo 231814 4321073 := bstep (se 2 (by rfl) ⟨1620402, by rfl⟩ : syracuseStep 4321073 = 3240805) B3240805
theorem B1273745 : Blo 231814 1273745 := bstep (se 2 (by rfl) ⟨477654, by rfl⟩ : syracuseStep 1273745 = 955309) B955309
theorem B422023 : Blo 231814 422023 := bstep (se 1 (by rfl) ⟨316517, by rfl⟩ : syracuseStep 422023 = 633035) B633035
theorem B1208591 : Blo 231814 1208591 := bstep (se 1 (by rfl) ⟨906443, by rfl⟩ : syracuseStep 1208591 = 1812887) B1812887
theorem B1208843 : Blo 231814 1208843 := bstep (se 1 (by rfl) ⟨906632, by rfl⟩ : syracuseStep 1208843 = 1813265) B1813265
theorem B782891 : Blo 231814 782891 := bstep (se 1 (by rfl) ⟨587168, by rfl⟩ : syracuseStep 782891 = 1174337) B1174337
theorem B881239 : Blo 231814 881239 := bstep (se 1 (by rfl) ⟨660929, by rfl⟩ : syracuseStep 881239 = 1321859) B1321859
theorem B881543 : Blo 231814 881543 := bstep (se 1 (by rfl) ⟨661157, by rfl⟩ : syracuseStep 881543 = 1322315) B1322315
theorem B1176605 : Blo 231814 1176605 := bstep (se 3 (by rfl) ⟨220613, by rfl⟩ : syracuseStep 1176605 = 441227) B441227
theorem B881725 : Blo 231814 881725 := bstep (se 3 (by rfl) ⟨165323, by rfl⟩ : syracuseStep 881725 = 330647) B330647
theorem B8975447 : Blo 231814 8975447 := bstep (se 1 (by rfl) ⟨6731585, by rfl⟩ : syracuseStep 8975447 = 13463171) B13463171
theorem B423031 : Blo 231814 423031 := bstep (se 1 (by rfl) ⟨317273, by rfl⟩ : syracuseStep 423031 = 634547) B634547
theorem B849133 : Blo 231814 849133 := bstep (se 3 (by rfl) ⟨159212, by rfl⟩ : syracuseStep 849133 = 318425) B318425
theorem B2684177 : Blo 231814 2684177 := bstep (se 2 (by rfl) ⟨1006566, by rfl⟩ : syracuseStep 2684177 = 2013133) B2013133
theorem B1209659 : Blo 231814 1209659 := bstep (se 1 (by rfl) ⟨907244, by rfl⟩ : syracuseStep 1209659 = 1814489) B1814489
theorem B521657 : Blo 231814 521657 := bstep (se 2 (by rfl) ⟨195621, by rfl⟩ : syracuseStep 521657 = 391243) B391243
theorem B587209 : Blo 231814 587209 := bstep (se 2 (by rfl) ⟨220203, by rfl⟩ : syracuseStep 587209 = 440407) B440407
theorem B1209821 : Blo 231814 1209821 := bstep (se 3 (by rfl) ⟨226841, by rfl⟩ : syracuseStep 1209821 = 453683) B453683
theorem B1177091 : Blo 231814 1177091 := bstep (se 1 (by rfl) ⟨882818, by rfl⟩ : syracuseStep 1177091 = 1765637) B1765637
theorem B751133 : Blo 231814 751133 := bstep (se 3 (by rfl) ⟨140837, by rfl⟩ : syracuseStep 751133 = 281675) B281675
theorem B849437 : Blo 231814 849437 := bstep (se 3 (by rfl) ⟨159269, by rfl⟩ : syracuseStep 849437 = 318539) B318539
theorem B1340995 : Blo 231814 1340995 := bstep (se 1 (by rfl) ⟨1005746, by rfl⟩ : syracuseStep 1340995 = 2011493) B2011493
theorem B587351 : Blo 231814 587351 := bstep (se 1 (by rfl) ⟨440513, by rfl⟩ : syracuseStep 587351 = 881027) B881027
theorem B521999 : Blo 231814 521999 := bstep (se 1 (by rfl) ⟨391499, by rfl⟩ : syracuseStep 521999 = 782999) B782999
theorem B522017 : Blo 231814 522017 := bstep (se 2 (by rfl) ⟨195756, by rfl⟩ : syracuseStep 522017 = 391513) B391513
theorem B1996595 : Blo 231814 1996595 := bstep (se 1 (by rfl) ⟨1497446, by rfl⟩ : syracuseStep 1996595 = 2994893) B2994893
theorem B784187 : Blo 231814 784187 := bstep (se 1 (by rfl) ⟨588140, by rfl⟩ : syracuseStep 784187 = 1176281) B1176281
theorem B522359 : Blo 231814 522359 := bstep (se 1 (by rfl) ⟨391769, by rfl⟩ : syracuseStep 522359 = 783539) B783539
theorem B1996973 : Blo 231814 1996973 := bstep (se 3 (by rfl) ⟨374432, by rfl⟩ : syracuseStep 1996973 = 748865) B748865
theorem B391439 : Blo 231814 391439 := bstep (se 1 (by rfl) ⟨293579, by rfl⟩ : syracuseStep 391439 = 587159) B587159
theorem B784673 : Blo 231814 784673 := bstep (se 2 (by rfl) ⟨294252, by rfl⟩ : syracuseStep 784673 = 588505) B588505
theorem B522539 : Blo 231814 522539 := bstep (se 1 (by rfl) ⟨391904, by rfl⟩ : syracuseStep 522539 = 783809) B783809
theorem B10090817 : Blo 231814 10090817 := bstep (se 2 (by rfl) ⟨3784056, by rfl⟩ : syracuseStep 10090817 = 7568113) B7568113
theorem B522899 : Blo 231814 522899 := bstep (se 1 (by rfl) ⟨392174, by rfl⟩ : syracuseStep 522899 = 784349) B784349
theorem B522953 : Blo 231814 522953 := bstep (se 2 (by rfl) ⟨196107, by rfl⟩ : syracuseStep 522953 = 392215) B392215
theorem B883457 : Blo 231814 883457 := bstep (se 2 (by rfl) ⟨331296, by rfl⟩ : syracuseStep 883457 = 662593) B662593
theorem B391979 : Blo 231814 391979 := bstep (se 1 (by rfl) ⟨293984, by rfl⟩ : syracuseStep 391979 = 587969) B587969
theorem B260923 : Blo 231814 260923 := bstep (se 1 (by rfl) ⟨195692, by rfl⟩ : syracuseStep 260923 = 391385) B391385
theorem B785267 : Blo 231814 785267 := bstep (se 1 (by rfl) ⟨588950, by rfl⟩ : syracuseStep 785267 = 1177901) B1177901
theorem B6454333 : Blo 231814 6454333 := bstep (se 3 (by rfl) ⟨1210187, by rfl⟩ : syracuseStep 6454333 = 2420375) B2420375
theorem B1178711 : Blo 231814 1178711 := bstep (se 1 (by rfl) ⟨884033, by rfl⟩ : syracuseStep 1178711 = 1768067) B1768067
theorem B392377 : Blo 231814 392377 := bstep (se 2 (by rfl) ⟨147141, by rfl⟩ : syracuseStep 392377 = 294283) B294283
theorem B261391 : Blo 231814 261391 := bstep (se 1 (by rfl) ⟨196043, by rfl⟩ : syracuseStep 261391 = 392087) B392087
theorem B294187 : Blo 231814 294187 := bstep (se 1 (by rfl) ⟨220640, by rfl⟩ : syracuseStep 294187 = 441281) B441281
theorem B523655 : Blo 231814 523655 := bstep (se 1 (by rfl) ⟨392741, by rfl⟩ : syracuseStep 523655 = 785483) B785483
theorem B1342979 : Blo 231814 1342979 := bstep (se 1 (by rfl) ⟨1007234, by rfl⟩ : syracuseStep 1342979 = 2014469) B2014469
theorem B523835 : Blo 231814 523835 := bstep (se 1 (by rfl) ⟨392876, by rfl⟩ : syracuseStep 523835 = 785753) B785753
theorem B1179197 : Blo 231814 1179197 := bstep (se 3 (by rfl) ⟨221099, by rfl⟩ : syracuseStep 1179197 = 442199) B442199
theorem B589427 : Blo 231814 589427 := bstep (se 1 (by rfl) ⟨442070, by rfl⟩ : syracuseStep 589427 = 884141) B884141
theorem B523961 : Blo 231814 523961 := bstep (se 2 (by rfl) ⟨196485, by rfl⟩ : syracuseStep 523961 = 392971) B392971
theorem B261895 : Blo 231814 261895 := bstep (se 1 (by rfl) ⟨196421, by rfl⟩ : syracuseStep 261895 = 392843) B392843
theorem B393079 : Blo 231814 393079 := bstep (se 1 (by rfl) ⟨294809, by rfl⟩ : syracuseStep 393079 = 589619) B589619
theorem B884627 : Blo 231814 884627 := bstep (se 1 (by rfl) ⟨663470, by rfl⟩ : syracuseStep 884627 = 1326941) B1326941
theorem B262075 : Blo 231814 262075 := bstep (se 1 (by rfl) ⟨196556, by rfl⟩ : syracuseStep 262075 = 393113) B393113
theorem B262183 : Blo 231814 262183 := bstep (se 1 (by rfl) ⟨196637, by rfl⟩ : syracuseStep 262183 = 393275) B393275
theorem B393295 : Blo 231814 393295 := bstep (se 1 (by rfl) ⟨294971, by rfl⟩ : syracuseStep 393295 = 589943) B589943
theorem B393545 : Blo 231814 393545 := bstep (se 2 (by rfl) ⟨147579, by rfl⟩ : syracuseStep 393545 = 295159) B295159
theorem B1180169 : Blo 231814 1180169 := bstep (se 2 (by rfl) ⟨442563, by rfl⟩ : syracuseStep 1180169 = 885127) B885127
theorem B2228795 : Blo 231814 2228795 := bstep (se 1 (by rfl) ⟨1671596, by rfl⟩ : syracuseStep 2228795 = 3343193) B3343193
theorem B754235 : Blo 231814 754235 := bstep (se 1 (by rfl) ⟨565676, by rfl⟩ : syracuseStep 754235 = 1131353) B1131353
theorem B524897 : Blo 231814 524897 := bstep (se 2 (by rfl) ⟨196836, by rfl⟩ : syracuseStep 524897 = 393673) B393673
theorem B393977 : Blo 231814 393977 := bstep (se 2 (by rfl) ⟨147741, by rfl⟩ : syracuseStep 393977 = 295483) B295483
theorem B754505 : Blo 231814 754505 := bstep (se 2 (by rfl) ⟨282939, by rfl⟩ : syracuseStep 754505 = 565879) B565879
theorem B885599 : Blo 231814 885599 := bstep (se 1 (by rfl) ⟨664199, by rfl⟩ : syracuseStep 885599 = 1328399) B1328399
theorem B885613 : Blo 231814 885613 := bstep (se 3 (by rfl) ⟨166052, by rfl⟩ : syracuseStep 885613 = 332105) B332105
theorem B787319 : Blo 231814 787319 := bstep (se 1 (by rfl) ⟨590489, by rfl⟩ : syracuseStep 787319 = 1180979) B1180979
theorem B590753 : Blo 231814 590753 := bstep (se 2 (by rfl) ⟨221532, by rfl⟩ : syracuseStep 590753 = 443065) B443065
theorem B394159 : Blo 231814 394159 := bstep (se 1 (by rfl) ⟨295619, by rfl⟩ : syracuseStep 394159 = 591239) B591239
theorem B525239 : Blo 231814 525239 := bstep (se 1 (by rfl) ⟨393929, by rfl⟩ : syracuseStep 525239 = 787859) B787859
theorem B1770497 : Blo 231814 1770497 := bstep (se 2 (by rfl) ⟨663936, by rfl⟩ : syracuseStep 1770497 = 1327873) B1327873
theorem B394247 : Blo 231814 394247 := bstep (se 1 (by rfl) ⟨295685, by rfl⟩ : syracuseStep 394247 = 591371) B591371
theorem B787535 : Blo 231814 787535 := bstep (se 1 (by rfl) ⟨590651, by rfl⟩ : syracuseStep 787535 = 1181303) B1181303
theorem B459899 : Blo 231814 459899 := bstep (se 1 (by rfl) ⟨344924, by rfl⟩ : syracuseStep 459899 = 689849) B689849
theorem B885917 : Blo 231814 885917 := bstep (se 3 (by rfl) ⟨166109, by rfl⟩ : syracuseStep 885917 = 332219) B332219
theorem B394591 : Blo 231814 394591 := bstep (se 1 (by rfl) ⟨295943, by rfl⟩ : syracuseStep 394591 = 591887) B591887
theorem B591209 : Blo 231814 591209 := bstep (se 2 (by rfl) ⟨221703, by rfl⟩ : syracuseStep 591209 = 443407) B443407
theorem B951695 : Blo 231814 951695 := bstep (se 1 (by rfl) ⟨713771, by rfl⟩ : syracuseStep 951695 = 1427543) B1427543
theorem B394679 : Blo 231814 394679 := bstep (se 1 (by rfl) ⟨296009, by rfl⟩ : syracuseStep 394679 = 592019) B592019
theorem B787913 : Blo 231814 787913 := bstep (se 2 (by rfl) ⟨295467, by rfl⟩ : syracuseStep 787913 = 590935) B590935
theorem B4326857 : Blo 231814 4326857 := bstep (se 2 (by rfl) ⟨1622571, by rfl⟩ : syracuseStep 4326857 = 3245143) B3245143
theorem B525833 : Blo 231814 525833 := bstep (se 2 (by rfl) ⟨197187, by rfl⟩ : syracuseStep 525833 = 394375) B394375
theorem B3606059 : Blo 231814 3606059 := bstep (se 1 (by rfl) ⟨2704544, by rfl⟩ : syracuseStep 3606059 = 5409089) B5409089
theorem B263803 : Blo 231814 263803 := bstep (se 1 (by rfl) ⟨197852, by rfl⟩ : syracuseStep 263803 = 395705) B395705
theorem B755335 : Blo 231814 755335 := bstep (se 1 (by rfl) ⟨566501, by rfl⟩ : syracuseStep 755335 = 1133003) B1133003
theorem B952019 : Blo 231814 952019 := bstep (se 1 (by rfl) ⟨714014, by rfl⟩ : syracuseStep 952019 = 1428029) B1428029
theorem B4458199 : Blo 231814 4458199 := bstep (se 1 (by rfl) ⟨3343649, by rfl⟩ : syracuseStep 4458199 = 6687299) B6687299
theorem B788183 : Blo 231814 788183 := bstep (se 1 (by rfl) ⟨591137, by rfl⟩ : syracuseStep 788183 = 1182275) B1182275
theorem B886571 : Blo 231814 886571 := bstep (se 1 (by rfl) ⟨664928, by rfl⟩ : syracuseStep 886571 = 1329857) B1329857
theorem B526175 : Blo 231814 526175 := bstep (se 1 (by rfl) ⟨394631, by rfl⟩ : syracuseStep 526175 = 789263) B789263
theorem B788399 : Blo 231814 788399 := bstep (se 1 (by rfl) ⟨591299, by rfl⟩ : syracuseStep 788399 = 1182599) B1182599
theorem B1181627 : Blo 231814 1181627 := bstep (se 1 (by rfl) ⟨886220, by rfl⟩ : syracuseStep 1181627 = 1772441) B1772441
theorem B395273 : Blo 231814 395273 := bstep (se 2 (by rfl) ⟨148227, by rfl⟩ : syracuseStep 395273 = 296455) B296455
theorem B526355 : Blo 231814 526355 := bstep (se 1 (by rfl) ⟨394766, by rfl⟩ : syracuseStep 526355 = 789533) B789533
theorem B264271 : Blo 231814 264271 := bstep (se 1 (by rfl) ⟨198203, by rfl⟩ : syracuseStep 264271 = 396407) B396407
theorem B395435 : Blo 231814 395435 := bstep (se 1 (by rfl) ⟨296576, by rfl⟩ : syracuseStep 395435 = 593153) B593153
theorem B526697 : Blo 231814 526697 := bstep (se 2 (by rfl) ⟨197511, by rfl⟩ : syracuseStep 526697 = 395023) B395023
theorem B231855 : Blo 231814 231855 := bstep (se 1 (by rfl) ⟨173891, by rfl⟩ : syracuseStep 231855 = 347783) B347783
theorem B231879 : Blo 231814 231879 := bstep (se 1 (by rfl) ⟨173909, by rfl⟩ : syracuseStep 231879 = 347819) B347819
theorem B231899 : Blo 231814 231899 := bstep (se 1 (by rfl) ⟨173924, by rfl⟩ : syracuseStep 231899 = 347849) B347849
theorem B330203 : Blo 231814 330203 := bstep (se 1 (by rfl) ⟨247652, by rfl⟩ : syracuseStep 330203 = 495305) B495305
theorem B264667 : Blo 231814 264667 := bstep (se 1 (by rfl) ⟨198500, by rfl⟩ : syracuseStep 264667 = 397001) B397001
theorem B592393 : Blo 231814 592393 := bstep (se 2 (by rfl) ⟨222147, by rfl⟩ : syracuseStep 592393 = 444295) B444295
theorem B231975 : Blo 231814 231975 := bstep (se 1 (by rfl) ⟨173981, by rfl⟩ : syracuseStep 231975 = 347963) B347963
theorem B395833 : Blo 231814 395833 := bstep (se 2 (by rfl) ⟨148437, by rfl⟩ : syracuseStep 395833 = 296875) B296875
theorem B232015 : Blo 231814 232015 := bstep (se 1 (by rfl) ⟨174011, by rfl⟩ : syracuseStep 232015 = 348023) B348023
theorem B232031 : Blo 231814 232031 := bstep (se 1 (by rfl) ⟨174023, by rfl⟩ : syracuseStep 232031 = 348047) B348047
theorem B232059 : Blo 231814 232059 := bstep (se 1 (by rfl) ⟨174044, by rfl⟩ : syracuseStep 232059 = 348089) B348089
theorem B232111 : Blo 231814 232111 := bstep (se 1 (by rfl) ⟨174083, by rfl⟩ : syracuseStep 232111 = 348167) B348167
theorem B232135 : Blo 231814 232135 := bstep (se 1 (by rfl) ⟨174101, by rfl⟩ : syracuseStep 232135 = 348203) B348203
theorem B395975 : Blo 231814 395975 := bstep (se 1 (by rfl) ⟨296981, by rfl⟩ : syracuseStep 395975 = 593963) B593963
theorem B232155 : Blo 231814 232155 := bstep (se 1 (by rfl) ⟨174116, by rfl⟩ : syracuseStep 232155 = 348233) B348233
theorem B232231 : Blo 231814 232231 := bstep (se 1 (by rfl) ⟨174173, by rfl⟩ : syracuseStep 232231 = 348347) B348347
theorem B232271 : Blo 231814 232271 := bstep (se 1 (by rfl) ⟨174203, by rfl⟩ : syracuseStep 232271 = 348407) B348407
theorem B232287 : Blo 231814 232287 := bstep (se 1 (by rfl) ⟨174215, by rfl⟩ : syracuseStep 232287 = 348431) B348431
theorem B396137 : Blo 231814 396137 := bstep (se 2 (by rfl) ⟨148551, by rfl⟩ : syracuseStep 396137 = 297103) B297103
theorem B232315 : Blo 231814 232315 := bstep (se 1 (by rfl) ⟨174236, by rfl⟩ : syracuseStep 232315 = 348473) B348473
theorem B232367 : Blo 231814 232367 := bstep (se 1 (by rfl) ⟨174275, by rfl⟩ : syracuseStep 232367 = 348551) B348551
theorem B265135 : Blo 231814 265135 := bstep (se 1 (by rfl) ⟨198851, by rfl⟩ : syracuseStep 265135 = 397703) B397703
theorem B527291 : Blo 231814 527291 := bstep (se 1 (by rfl) ⟨395468, by rfl⟩ : syracuseStep 527291 = 790937) B790937
theorem B232391 : Blo 231814 232391 := bstep (se 1 (by rfl) ⟨174293, by rfl⟩ : syracuseStep 232391 = 348587) B348587
theorem B232411 : Blo 231814 232411 := bstep (se 1 (by rfl) ⟨174308, by rfl⟩ : syracuseStep 232411 = 348617) B348617
theorem B330761 : Blo 231814 330761 := bstep (se 2 (by rfl) ⟨124035, by rfl⟩ : syracuseStep 330761 = 248071) B248071
theorem B232487 : Blo 231814 232487 := bstep (se 1 (by rfl) ⟨174365, by rfl⟩ : syracuseStep 232487 = 348731) B348731
theorem B527417 : Blo 231814 527417 := bstep (se 2 (by rfl) ⟨197781, by rfl⟩ : syracuseStep 527417 = 395563) B395563
theorem B232527 : Blo 231814 232527 := bstep (se 1 (by rfl) ⟨174395, by rfl⟩ : syracuseStep 232527 = 348791) B348791
theorem B232543 : Blo 231814 232543 := bstep (se 1 (by rfl) ⟨174407, by rfl⟩ : syracuseStep 232543 = 348815) B348815
theorem B232571 : Blo 231814 232571 := bstep (se 1 (by rfl) ⟨174428, by rfl⟩ : syracuseStep 232571 = 348857) B348857
theorem B232623 : Blo 231814 232623 := bstep (se 1 (by rfl) ⟨174467, by rfl⟩ : syracuseStep 232623 = 348935) B348935
theorem B232647 : Blo 231814 232647 := bstep (se 1 (by rfl) ⟨174485, by rfl⟩ : syracuseStep 232647 = 348971) B348971
theorem B1182923 : Blo 231814 1182923 := bstep (se 1 (by rfl) ⟨887192, by rfl⟩ : syracuseStep 1182923 = 1774385) B1774385
theorem B232667 : Blo 231814 232667 := bstep (se 1 (by rfl) ⟨174500, by rfl⟩ : syracuseStep 232667 = 349001) B349001
theorem B3214583 : Blo 231814 3214583 := bstep (se 1 (by rfl) ⟨2410937, by rfl⟩ : syracuseStep 3214583 = 4821875) B4821875
theorem B396535 : Blo 231814 396535 := bstep (se 1 (by rfl) ⟨297401, by rfl⟩ : syracuseStep 396535 = 594803) B594803
theorem B232743 : Blo 231814 232743 := bstep (se 1 (by rfl) ⟨174557, by rfl⟩ : syracuseStep 232743 = 349115) B349115
theorem B232783 : Blo 231814 232783 := bstep (se 1 (by rfl) ⟨174587, by rfl⟩ : syracuseStep 232783 = 349175) B349175
theorem B232799 : Blo 231814 232799 := bstep (se 1 (by rfl) ⟨174599, by rfl⟩ : syracuseStep 232799 = 349199) B349199
theorem B232827 : Blo 231814 232827 := bstep (se 1 (by rfl) ⟨174620, by rfl⟩ : syracuseStep 232827 = 349241) B349241
theorem B527759 : Blo 231814 527759 := bstep (se 1 (by rfl) ⟨395819, by rfl⟩ : syracuseStep 527759 = 791639) B791639
theorem B232879 : Blo 231814 232879 := bstep (se 1 (by rfl) ⟨174659, by rfl⟩ : syracuseStep 232879 = 349319) B349319
theorem B298423 : Blo 231814 298423 := bstep (se 1 (by rfl) ⟨223817, by rfl⟩ : syracuseStep 298423 = 447635) B447635
theorem B396731 : Blo 231814 396731 := bstep (se 1 (by rfl) ⟨297548, by rfl⟩ : syracuseStep 396731 = 595097) B595097
theorem B232903 : Blo 231814 232903 := bstep (se 1 (by rfl) ⟨174677, by rfl⟩ : syracuseStep 232903 = 349355) B349355
theorem B953801 : Blo 231814 953801 := bstep (se 2 (by rfl) ⟨357675, by rfl⟩ : syracuseStep 953801 = 715351) B715351
theorem B232923 : Blo 231814 232923 := bstep (se 1 (by rfl) ⟨174692, by rfl⟩ : syracuseStep 232923 = 349385) B349385
theorem B495143 : Blo 231814 495143 := bstep (se 1 (by rfl) ⟨371357, by rfl⟩ : syracuseStep 495143 = 742715) B742715
theorem B232999 : Blo 231814 232999 := bstep (se 1 (by rfl) ⟨174749, by rfl⟩ : syracuseStep 232999 = 349499) B349499
theorem B396839 : Blo 231814 396839 := bstep (se 1 (by rfl) ⟨297629, by rfl⟩ : syracuseStep 396839 = 595259) B595259
theorem B233039 : Blo 231814 233039 := bstep (se 1 (by rfl) ⟨174779, by rfl⟩ : syracuseStep 233039 = 349559) B349559
theorem B233055 : Blo 231814 233055 := bstep (se 1 (by rfl) ⟨174791, by rfl⟩ : syracuseStep 233055 = 349583) B349583
theorem B3903095 : Blo 231814 3903095 := bstep (se 1 (by rfl) ⟨2927321, by rfl⟩ : syracuseStep 3903095 = 5854643) B5854643
theorem B233083 : Blo 231814 233083 := bstep (se 1 (by rfl) ⟨174812, by rfl⟩ : syracuseStep 233083 = 349625) B349625
theorem B3247739 : Blo 231814 3247739 := bstep (se 1 (by rfl) ⟨2435804, by rfl⟩ : syracuseStep 3247739 = 4871609) B4871609
theorem B233135 : Blo 231814 233135 := bstep (se 1 (by rfl) ⟨174851, by rfl⟩ : syracuseStep 233135 = 349703) B349703
theorem B233159 : Blo 231814 233159 := bstep (se 1 (by rfl) ⟨174869, by rfl⟩ : syracuseStep 233159 = 349739) B349739
theorem B888529 : Blo 231814 888529 := bstep (se 2 (by rfl) ⟨333198, by rfl⟩ : syracuseStep 888529 = 666397) B666397
theorem B528083 : Blo 231814 528083 := bstep (se 1 (by rfl) ⟨396062, by rfl⟩ : syracuseStep 528083 = 792125) B792125
theorem B233179 : Blo 231814 233179 := bstep (se 1 (by rfl) ⟨174884, by rfl⟩ : syracuseStep 233179 = 349769) B349769
theorem B233255 : Blo 231814 233255 := bstep (se 1 (by rfl) ⟨174941, by rfl⟩ : syracuseStep 233255 = 349883) B349883
theorem B397129 : Blo 231814 397129 := bstep (se 2 (by rfl) ⟨148923, by rfl⟩ : syracuseStep 397129 = 297847) B297847
theorem B233295 : Blo 231814 233295 := bstep (se 1 (by rfl) ⟨174971, by rfl⟩ : syracuseStep 233295 = 349943) B349943
theorem B233311 : Blo 231814 233311 := bstep (se 1 (by rfl) ⟨174983, by rfl⟩ : syracuseStep 233311 = 349967) B349967
theorem B331627 : Blo 231814 331627 := bstep (se 1 (by rfl) ⟨248720, by rfl⟩ : syracuseStep 331627 = 497441) B497441
theorem B397163 : Blo 231814 397163 := bstep (se 1 (by rfl) ⟨297872, by rfl⟩ : syracuseStep 397163 = 595745) B595745
theorem B233339 : Blo 231814 233339 := bstep (se 1 (by rfl) ⟨175004, by rfl⟩ : syracuseStep 233339 = 350009) B350009
theorem B233391 : Blo 231814 233391 := bstep (se 1 (by rfl) ⟨175043, by rfl⟩ : syracuseStep 233391 = 350087) B350087
theorem B593851 : Blo 231814 593851 := bstep (se 1 (by rfl) ⟨445388, by rfl⟩ : syracuseStep 593851 = 890777) B890777
theorem B233415 : Blo 231814 233415 := bstep (se 1 (by rfl) ⟨175061, by rfl⟩ : syracuseStep 233415 = 350123) B350123
theorem B233435 : Blo 231814 233435 := bstep (se 1 (by rfl) ⟨175076, by rfl⟩ : syracuseStep 233435 = 350153) B350153
theorem B888833 : Blo 231814 888833 := bstep (se 2 (by rfl) ⟨333312, by rfl⟩ : syracuseStep 888833 = 666625) B666625
theorem B233511 : Blo 231814 233511 := bstep (se 1 (by rfl) ⟨175133, by rfl⟩ : syracuseStep 233511 = 350267) B350267
theorem B233551 : Blo 231814 233551 := bstep (se 1 (by rfl) ⟨175163, by rfl⟩ : syracuseStep 233551 = 350327) B350327
theorem B233567 : Blo 231814 233567 := bstep (se 1 (by rfl) ⟨175175, by rfl⟩ : syracuseStep 233567 = 350351) B350351
theorem B233595 : Blo 231814 233595 := bstep (se 1 (by rfl) ⟨175196, by rfl⟩ : syracuseStep 233595 = 350393) B350393
theorem B233647 : Blo 231814 233647 := bstep (se 1 (by rfl) ⟨175235, by rfl⟩ : syracuseStep 233647 = 350471) B350471
theorem B233671 : Blo 231814 233671 := bstep (se 1 (by rfl) ⟨175253, by rfl⟩ : syracuseStep 233671 = 350507) B350507
theorem B233691 : Blo 231814 233691 := bstep (se 1 (by rfl) ⟨175268, by rfl⟩ : syracuseStep 233691 = 350537) B350537
theorem B790775 : Blo 231814 790775 := bstep (se 1 (by rfl) ⟨593081, by rfl⟩ : syracuseStep 790775 = 1186163) B1186163
theorem B397561 : Blo 231814 397561 := bstep (se 2 (by rfl) ⟨149085, by rfl⟩ : syracuseStep 397561 = 298171) B298171
theorem B233767 : Blo 231814 233767 := bstep (se 1 (by rfl) ⟨175325, by rfl⟩ : syracuseStep 233767 = 350651) B350651
theorem B233807 : Blo 231814 233807 := bstep (se 1 (by rfl) ⟨175355, by rfl⟩ : syracuseStep 233807 = 350711) B350711
theorem B233823 : Blo 231814 233823 := bstep (se 1 (by rfl) ⟨175367, by rfl⟩ : syracuseStep 233823 = 350735) B350735
theorem B233851 : Blo 231814 233851 := bstep (se 1 (by rfl) ⟨175388, by rfl⟩ : syracuseStep 233851 = 350777) B350777
theorem B233903 : Blo 231814 233903 := bstep (se 1 (by rfl) ⟨175427, by rfl⟩ : syracuseStep 233903 = 350855) B350855
theorem B233927 : Blo 231814 233927 := bstep (se 1 (by rfl) ⟨175445, by rfl⟩ : syracuseStep 233927 = 350891) B350891
theorem B889289 : Blo 231814 889289 := bstep (se 2 (by rfl) ⟨333483, by rfl⟩ : syracuseStep 889289 = 666967) B666967
theorem B233947 : Blo 231814 233947 := bstep (se 1 (by rfl) ⟨175460, by rfl⟩ : syracuseStep 233947 = 350921) B350921
theorem B397831 : Blo 231814 397831 := bstep (se 1 (by rfl) ⟨298373, by rfl⟩ : syracuseStep 397831 = 596747) B596747
theorem B627239 : Blo 231814 627239 := bstep (se 1 (by rfl) ⟨470429, by rfl⟩ : syracuseStep 627239 = 940859) B940859
theorem B234023 : Blo 231814 234023 := bstep (se 1 (by rfl) ⟨175517, by rfl⟩ : syracuseStep 234023 = 351035) B351035
theorem B791099 : Blo 231814 791099 := bstep (se 1 (by rfl) ⟨593324, by rfl⟩ : syracuseStep 791099 = 1186649) B1186649
theorem B234063 : Blo 231814 234063 := bstep (se 1 (by rfl) ⟨175547, by rfl⟩ : syracuseStep 234063 = 351095) B351095
theorem B234079 : Blo 231814 234079 := bstep (se 1 (by rfl) ⟨175559, by rfl⟩ : syracuseStep 234079 = 351119) B351119
theorem B856673 : Blo 231814 856673 := bstep (se 2 (by rfl) ⟨321252, by rfl⟩ : syracuseStep 856673 = 642505) B642505
theorem B234107 : Blo 231814 234107 := bstep (se 1 (by rfl) ⟨175580, by rfl⟩ : syracuseStep 234107 = 351161) B351161
theorem B529019 : Blo 231814 529019 := bstep (se 1 (by rfl) ⟨396764, by rfl⟩ : syracuseStep 529019 = 793529) B793529
theorem B234159 : Blo 231814 234159 := bstep (se 1 (by rfl) ⟨175619, by rfl⟩ : syracuseStep 234159 = 351239) B351239
theorem B234183 : Blo 231814 234183 := bstep (se 1 (by rfl) ⟨175637, by rfl⟩ : syracuseStep 234183 = 351275) B351275
theorem B234203 : Blo 231814 234203 := bstep (se 1 (by rfl) ⟨175652, by rfl⟩ : syracuseStep 234203 = 351305) B351305
theorem B529145 : Blo 231814 529145 := bstep (se 2 (by rfl) ⟨198429, by rfl⟩ : syracuseStep 529145 = 396859) B396859
theorem B234279 : Blo 231814 234279 := bstep (se 1 (by rfl) ⟨175709, by rfl⟩ : syracuseStep 234279 = 351419) B351419
theorem B791369 : Blo 231814 791369 := bstep (se 2 (by rfl) ⟨296763, by rfl⟩ : syracuseStep 791369 = 593527) B593527
theorem B234319 : Blo 231814 234319 := bstep (se 1 (by rfl) ⟨175739, by rfl⟩ : syracuseStep 234319 = 351479) B351479
theorem B234335 : Blo 231814 234335 := bstep (se 1 (by rfl) ⟨175751, by rfl⟩ : syracuseStep 234335 = 351503) B351503
theorem B627563 : Blo 231814 627563 := bstep (se 1 (by rfl) ⟨470672, by rfl⟩ : syracuseStep 627563 = 941345) B941345
theorem B234363 : Blo 231814 234363 := bstep (se 1 (by rfl) ⟨175772, by rfl⟩ : syracuseStep 234363 = 351545) B351545
theorem B889775 : Blo 231814 889775 := bstep (se 1 (by rfl) ⟨667331, by rfl⟩ : syracuseStep 889775 = 1334663) B1334663
theorem B234415 : Blo 231814 234415 := bstep (se 1 (by rfl) ⟨175811, by rfl⟩ : syracuseStep 234415 = 351623) B351623
theorem B234439 : Blo 231814 234439 := bstep (se 1 (by rfl) ⟨175829, by rfl⟩ : syracuseStep 234439 = 351659) B351659
theorem B234459 : Blo 231814 234459 := bstep (se 1 (by rfl) ⟨175844, by rfl⟩ : syracuseStep 234459 = 351689) B351689
theorem B529415 : Blo 231814 529415 := bstep (se 1 (by rfl) ⟨397061, by rfl⟩ : syracuseStep 529415 = 794123) B794123
theorem B398375 : Blo 231814 398375 := bstep (se 1 (by rfl) ⟨298781, by rfl⟩ : syracuseStep 398375 = 597563) B597563
theorem B234535 : Blo 231814 234535 := bstep (se 1 (by rfl) ⟨175901, by rfl⟩ : syracuseStep 234535 = 351803) B351803
theorem B234575 : Blo 231814 234575 := bstep (se 1 (by rfl) ⟨175931, by rfl⟩ : syracuseStep 234575 = 351863) B351863
theorem B529487 : Blo 231814 529487 := bstep (se 1 (by rfl) ⟨397115, by rfl⟩ : syracuseStep 529487 = 794231) B794231
theorem B234591 : Blo 231814 234591 := bstep (se 1 (by rfl) ⟨175943, by rfl⟩ : syracuseStep 234591 = 351887) B351887
theorem B1741943 : Blo 231814 1741943 := bstep (se 1 (by rfl) ⟨1306457, by rfl⟩ : syracuseStep 1741943 = 2612915) B2612915
theorem B234619 : Blo 231814 234619 := bstep (se 1 (by rfl) ⟨175964, by rfl⟩ : syracuseStep 234619 = 351929) B351929
theorem B234671 : Blo 231814 234671 := bstep (se 1 (by rfl) ⟨176003, by rfl⟩ : syracuseStep 234671 = 352007) B352007
theorem B234695 : Blo 231814 234695 := bstep (se 1 (by rfl) ⟨176021, by rfl⟩ : syracuseStep 234695 = 352043) B352043
theorem B234715 : Blo 231814 234715 := bstep (se 1 (by rfl) ⟨176036, by rfl⟩ : syracuseStep 234715 = 352073) B352073
theorem B1774871 : Blo 231814 1774871 := bstep (se 1 (by rfl) ⟨1331153, by rfl⟩ : syracuseStep 1774871 = 2662307) B2662307
theorem B234791 : Blo 231814 234791 := bstep (se 1 (by rfl) ⟨176093, by rfl⟩ : syracuseStep 234791 = 352187) B352187
theorem B234831 : Blo 231814 234831 := bstep (se 1 (by rfl) ⟨176123, by rfl⟩ : syracuseStep 234831 = 352247) B352247
theorem B234847 : Blo 231814 234847 := bstep (se 1 (by rfl) ⟨176135, by rfl⟩ : syracuseStep 234847 = 352271) B352271
theorem B234875 : Blo 231814 234875 := bstep (se 1 (by rfl) ⟨176156, by rfl⟩ : syracuseStep 234875 = 352313) B352313
theorem B234927 : Blo 231814 234927 := bstep (se 1 (by rfl) ⟨176195, by rfl⟩ : syracuseStep 234927 = 352391) B352391
theorem B234951 : Blo 231814 234951 := bstep (se 1 (by rfl) ⟨176213, by rfl⟩ : syracuseStep 234951 = 352427) B352427
theorem B234971 : Blo 231814 234971 := bstep (se 1 (by rfl) ⟨176228, by rfl⟩ : syracuseStep 234971 = 352457) B352457
theorem B529883 : Blo 231814 529883 := bstep (se 1 (by rfl) ⟨397412, by rfl⟩ : syracuseStep 529883 = 794825) B794825
theorem B562697 : Blo 231814 562697 := bstep (se 2 (by rfl) ⟨211011, by rfl⟩ : syracuseStep 562697 = 422023) B422023
theorem B235047 : Blo 231814 235047 := bstep (se 1 (by rfl) ⟨176285, by rfl⟩ : syracuseStep 235047 = 352571) B352571
theorem B235087 : Blo 231814 235087 := bstep (se 1 (by rfl) ⟨176315, by rfl⟩ : syracuseStep 235087 = 352631) B352631
theorem B235103 : Blo 231814 235103 := bstep (se 1 (by rfl) ⟨176327, by rfl⟩ : syracuseStep 235103 = 352655) B352655
theorem B235131 : Blo 231814 235131 := bstep (se 1 (by rfl) ⟨176348, by rfl⟩ : syracuseStep 235131 = 352697) B352697
theorem B235183 : Blo 231814 235183 := bstep (se 1 (by rfl) ⟨176387, by rfl⟩ : syracuseStep 235183 = 352775) B352775
theorem B235207 : Blo 231814 235207 := bstep (se 1 (by rfl) ⟨176405, by rfl⟩ : syracuseStep 235207 = 352811) B352811
theorem B235227 : Blo 231814 235227 := bstep (se 1 (by rfl) ⟨176420, by rfl⟩ : syracuseStep 235227 = 352841) B352841
theorem B235303 : Blo 231814 235303 := bstep (se 1 (by rfl) ⟨176477, by rfl⟩ : syracuseStep 235303 = 352955) B352955
theorem B235343 : Blo 231814 235343 := bstep (se 1 (by rfl) ⟨176507, by rfl⟩ : syracuseStep 235343 = 353015) B353015
theorem B235359 : Blo 231814 235359 := bstep (se 1 (by rfl) ⟨176519, by rfl⟩ : syracuseStep 235359 = 353039) B353039
theorem B235387 : Blo 231814 235387 := bstep (se 1 (by rfl) ⟨176540, by rfl⟩ : syracuseStep 235387 = 353081) B353081
theorem B661409 : Blo 231814 661409 := bstep (se 2 (by rfl) ⟨248028, by rfl⟩ : syracuseStep 661409 = 496057) B496057
theorem B235439 : Blo 231814 235439 := bstep (se 1 (by rfl) ⟨176579, by rfl⟩ : syracuseStep 235439 = 353159) B353159
theorem B530351 : Blo 231814 530351 := bstep (se 1 (by rfl) ⟨397763, by rfl⟩ : syracuseStep 530351 = 795527) B795527
theorem B792503 : Blo 231814 792503 := bstep (se 1 (by rfl) ⟨594377, by rfl⟩ : syracuseStep 792503 = 1188755) B1188755
theorem B235463 : Blo 231814 235463 := bstep (se 1 (by rfl) ⟨176597, by rfl⟩ : syracuseStep 235463 = 353195) B353195
theorem B235483 : Blo 231814 235483 := bstep (se 1 (by rfl) ⟨176612, by rfl⟩ : syracuseStep 235483 = 353225) B353225
theorem B235559 : Blo 231814 235559 := bstep (se 1 (by rfl) ⟨176669, by rfl⟩ : syracuseStep 235559 = 353339) B353339
theorem B890959 : Blo 231814 890959 := bstep (se 1 (by rfl) ⟨668219, by rfl⟩ : syracuseStep 890959 = 1336439) B1336439
theorem B235599 : Blo 231814 235599 := bstep (se 1 (by rfl) ⟨176699, by rfl⟩ : syracuseStep 235599 = 353399) B353399
theorem B235615 : Blo 231814 235615 := bstep (se 1 (by rfl) ⟨176711, by rfl⟩ : syracuseStep 235615 = 353423) B353423
theorem B235643 : Blo 231814 235643 := bstep (se 1 (by rfl) ⟨176732, by rfl⟩ : syracuseStep 235643 = 353465) B353465
theorem B235695 : Blo 231814 235695 := bstep (se 1 (by rfl) ⟨176771, by rfl⟩ : syracuseStep 235695 = 353543) B353543
theorem B301255 : Blo 231814 301255 := bstep (se 1 (by rfl) ⟨225941, by rfl⟩ : syracuseStep 301255 = 451883) B451883
theorem B235719 : Blo 231814 235719 := bstep (se 1 (by rfl) ⟨176789, by rfl⟩ : syracuseStep 235719 = 353579) B353579
theorem B235739 : Blo 231814 235739 := bstep (se 1 (by rfl) ⟨176804, by rfl⟩ : syracuseStep 235739 = 353609) B353609
theorem B596443 : Blo 231814 596443 := bstep (se 1 (by rfl) ⟨447332, by rfl⟩ : syracuseStep 596443 = 894665) B894665
theorem B793097 : Blo 231814 793097 := bstep (se 2 (by rfl) ⟨297411, by rfl⟩ : syracuseStep 793097 = 594823) B594823
theorem B891431 : Blo 231814 891431 := bstep (se 1 (by rfl) ⟨668573, by rfl⟩ : syracuseStep 891431 = 1337147) B1337147
theorem B4528709 : Blo 231814 4528709 := bstep (se 4 (by rfl) ⟨424566, by rfl⟩ : syracuseStep 4528709 = 849133) B849133
theorem B5970509 : Blo 231814 5970509 := bstep (se 3 (by rfl) ⟨1119470, by rfl⟩ : syracuseStep 5970509 = 2238941) B2238941
theorem B858721 : Blo 231814 858721 := bstep (se 2 (by rfl) ⟨322020, by rfl⟩ : syracuseStep 858721 = 644041) B644041
theorem B1776329 : Blo 231814 1776329 := bstep (se 2 (by rfl) ⟨666123, by rfl⟩ : syracuseStep 1776329 = 1332247) B1332247
theorem B564041 : Blo 231814 564041 := bstep (se 2 (by rfl) ⟨211515, by rfl⟩ : syracuseStep 564041 = 423031) B423031
theorem B597071 : Blo 231814 597071 := bstep (se 1 (by rfl) ⟨447803, by rfl⟩ : syracuseStep 597071 = 895607) B895607
theorem B4300121 : Blo 231814 4300121 := bstep (se 2 (by rfl) ⟨1612545, by rfl⟩ : syracuseStep 4300121 = 3225091) B3225091
theorem B793961 : Blo 231814 793961 := bstep (se 2 (by rfl) ⟨297735, by rfl⟩ : syracuseStep 793961 = 595471) B595471
theorem B892403 : Blo 231814 892403 := bstep (se 1 (by rfl) ⟨669302, by rfl⟩ : syracuseStep 892403 = 1338605) B1338605
theorem B794555 : Blo 231814 794555 := bstep (se 1 (by rfl) ⟨595916, by rfl⟩ : syracuseStep 794555 = 1191833) B1191833
theorem B663709 : Blo 231814 663709 := bstep (se 3 (by rfl) ⟨124445, by rfl⟩ : syracuseStep 663709 = 248891) B248891
theorem B1188107 : Blo 231814 1188107 := bstep (se 1 (by rfl) ⟨891080, by rfl⟩ : syracuseStep 1188107 = 1782161) B1782161
theorem B664051 : Blo 231814 664051 := bstep (se 1 (by rfl) ⟨498038, by rfl⟩ : syracuseStep 664051 = 996077) B996077
theorem B1909433 : Blo 231814 1909433 := bstep (se 2 (by rfl) ⟨716037, by rfl⟩ : syracuseStep 1909433 = 1432075) B1432075
theorem B402167 : Blo 231814 402167 := bstep (se 1 (by rfl) ⟨301625, by rfl⟩ : syracuseStep 402167 = 603251) B603251
theorem B500755 : Blo 231814 500755 := bstep (se 1 (by rfl) ⟨375566, by rfl⟩ : syracuseStep 500755 = 751133) B751133
theorem B566291 : Blo 231814 566291 := bstep (se 1 (by rfl) ⟨424718, by rfl⟩ : syracuseStep 566291 = 849437) B849437
theorem B2827781 : Blo 231814 2827781 := bstep (se 4 (by rfl) ⟨265104, by rfl⟩ : syracuseStep 2827781 = 530209) B530209
theorem B6727211 : Blo 231814 6727211 := bstep (se 1 (by rfl) ⟨5045408, by rfl⟩ : syracuseStep 6727211 = 10090817) B10090817
theorem B1189565 : Blo 231814 1189565 := bstep (se 3 (by rfl) ⟨223043, by rfl⟩ : syracuseStep 1189565 = 446087) B446087
theorem B1189727 : Blo 231814 1189727 := bstep (se 1 (by rfl) ⟨892295, by rfl⟩ : syracuseStep 1189727 = 1784591) B1784591
theorem B1058669 : Blo 231814 1058669 := bstep (se 3 (by rfl) ⟨198500, by rfl⟩ : syracuseStep 1058669 = 397001) B397001
theorem B1058831 : Blo 231814 1058831 := bstep (se 1 (by rfl) ⟨794123, by rfl⟩ : syracuseStep 1058831 = 1588247) B1588247
theorem B5023781 : Blo 231814 5023781 := bstep (se 4 (by rfl) ⟨470979, by rfl⟩ : syracuseStep 5023781 = 941959) B941959
theorem B895319 : Blo 231814 895319 := bstep (se 1 (by rfl) ⟨671489, by rfl⟩ : syracuseStep 895319 = 1342979) B1342979
theorem B993977 : Blo 231814 993977 := bstep (se 2 (by rfl) ⟨372741, by rfl⟩ : syracuseStep 993977 = 745483) B745483
theorem B600787 : Blo 231814 600787 := bstep (se 1 (by rfl) ⟨450590, by rfl⟩ : syracuseStep 600787 = 901181) B901181
theorem B502703 : Blo 231814 502703 := bstep (se 1 (by rfl) ⟨377027, by rfl⟩ : syracuseStep 502703 = 754055) B754055
theorem B799105 : Blo 231814 799105 := bstep (se 2 (by rfl) ⟨299664, by rfl⟩ : syracuseStep 799105 = 599329) B599329
theorem B1192481 : Blo 231814 1192481 := bstep (se 2 (by rfl) ⟨447180, by rfl⟩ : syracuseStep 1192481 = 894361) B894361
theorem B995975 : Blo 231814 995975 := bstep (se 1 (by rfl) ⟨746981, by rfl⟩ : syracuseStep 995975 = 1493963) B1493963
theorem B537299 : Blo 231814 537299 := bstep (se 1 (by rfl) ⟨402974, by rfl⟩ : syracuseStep 537299 = 805949) B805949
theorem B1258415 : Blo 231814 1258415 := bstep (se 1 (by rfl) ⟨943811, by rfl⟩ : syracuseStep 1258415 = 1887623) B1887623
theorem B374311 : Blo 231814 374311 := bstep (se 1 (by rfl) ⟨280733, by rfl⟩ : syracuseStep 374311 = 561467) B561467
theorem B800471 : Blo 231814 800471 := bstep (se 1 (by rfl) ⟨600353, by rfl⟩ : syracuseStep 800471 = 1200707) B1200707
theorem B5748515 : Blo 231814 5748515 := bstep (se 1 (by rfl) ⟨4311386, by rfl⟩ : syracuseStep 5748515 = 8622773) B8622773
theorem B1783619 : Blo 231814 1783619 := bstep (se 1 (by rfl) ⟨1337714, by rfl⟩ : syracuseStep 1783619 = 2675429) B2675429
theorem B440225 : Blo 231814 440225 := bstep (se 2 (by rfl) ⟨165084, by rfl⟩ : syracuseStep 440225 = 330169) B330169
theorem B3815581 : Blo 231814 3815581 := bstep (se 3 (by rfl) ⟨715421, by rfl⟩ : syracuseStep 3815581 = 1430843) B1430843
theorem B3225757 : Blo 231814 3225757 := bstep (se 3 (by rfl) ⟨604829, by rfl⟩ : syracuseStep 3225757 = 1209659) B1209659
theorem B440491 : Blo 231814 440491 := bstep (se 1 (by rfl) ⟨330368, by rfl⟩ : syracuseStep 440491 = 660737) B660737
theorem B1915289 : Blo 231814 1915289 := bstep (se 2 (by rfl) ⟨718233, by rfl⟩ : syracuseStep 1915289 = 1436467) B1436467
theorem B1980875 : Blo 231814 1980875 := bstep (se 1 (by rfl) ⟨1485656, by rfl⟩ : syracuseStep 1980875 = 2971313) B2971313
theorem B440795 : Blo 231814 440795 := bstep (se 1 (by rfl) ⟨330596, by rfl⟩ : syracuseStep 440795 = 661193) B661193
theorem B375259 : Blo 231814 375259 := bstep (se 1 (by rfl) ⟨281444, by rfl⟩ : syracuseStep 375259 = 562889) B562889
theorem B3226189 : Blo 231814 3226189 := bstep (se 3 (by rfl) ⟨604910, by rfl⟩ : syracuseStep 3226189 = 1209821) B1209821
theorem B473771 : Blo 231814 473771 := bstep (se 1 (by rfl) ⟨355328, by rfl⟩ : syracuseStep 473771 = 710657) B710657
theorem B375695 : Blo 231814 375695 := bstep (se 1 (by rfl) ⟨281771, by rfl⟩ : syracuseStep 375695 = 563543) B563543
theorem B1686419 : Blo 231814 1686419 := bstep (se 1 (by rfl) ⟨1264814, by rfl⟩ : syracuseStep 1686419 = 2529629) B2529629
theorem B932879 : Blo 231814 932879 := bstep (se 1 (by rfl) ⟨699659, by rfl⟩ : syracuseStep 932879 = 1399319) B1399319
theorem B375887 : Blo 231814 375887 := bstep (se 1 (by rfl) ⟨281915, by rfl⟩ : syracuseStep 375887 = 563831) B563831
theorem B1326233 : Blo 231814 1326233 := bstep (se 2 (by rfl) ⟨497337, by rfl⟩ : syracuseStep 1326233 = 994675) B994675
theorem B1490167 : Blo 231814 1490167 := bstep (se 1 (by rfl) ⟨1117625, by rfl⟩ : syracuseStep 1490167 = 2235251) B2235251
theorem B441865 : Blo 231814 441865 := bstep (se 2 (by rfl) ⟨165699, by rfl⟩ : syracuseStep 441865 = 331399) B331399
theorem B1326689 : Blo 231814 1326689 := bstep (se 2 (by rfl) ⟨497508, by rfl⟩ : syracuseStep 1326689 = 995017) B995017
theorem B442579 : Blo 231814 442579 := bstep (se 1 (by rfl) ⟨331934, by rfl⟩ : syracuseStep 442579 = 663869) B663869
theorem B475579 : Blo 231814 475579 := bstep (se 1 (by rfl) ⟨356684, by rfl⟩ : syracuseStep 475579 = 713369) B713369
theorem B443323 : Blo 231814 443323 := bstep (se 1 (by rfl) ⟨332492, by rfl⟩ : syracuseStep 443323 = 664985) B664985
theorem B1328147 : Blo 231814 1328147 := bstep (se 1 (by rfl) ⟨996110, by rfl⟩ : syracuseStep 1328147 = 1992221) B1992221
theorem B1721591 : Blo 231814 1721591 := bstep (se 1 (by rfl) ⟨1291193, by rfl⟩ : syracuseStep 1721591 = 2582387) B2582387
theorem B3622259 : Blo 231814 3622259 := bstep (se 1 (by rfl) ⟨2716694, by rfl⟩ : syracuseStep 3622259 = 5433389) B5433389
theorem B1688957 : Blo 231814 1688957 := bstep (se 3 (by rfl) ⟨316679, by rfl⟩ : syracuseStep 1688957 = 633359) B633359
theorem B443809 : Blo 231814 443809 := bstep (se 2 (by rfl) ⟨166428, by rfl⟩ : syracuseStep 443809 = 332857) B332857
theorem B6768035 : Blo 231814 6768035 := bstep (se 1 (by rfl) ⟨5076026, by rfl⟩ : syracuseStep 6768035 = 10152053) B10152053
theorem B1066459 : Blo 231814 1066459 := bstep (se 1 (by rfl) ⟨799844, by rfl⟩ : syracuseStep 1066459 = 1599689) B1599689
theorem B1001099 : Blo 231814 1001099 := bstep (se 1 (by rfl) ⟨750824, by rfl⟩ : syracuseStep 1001099 = 1501649) B1501649
theorem B2246291 : Blo 231814 2246291 := bstep (se 1 (by rfl) ⟨1684718, by rfl⟩ : syracuseStep 2246291 = 3369437) B3369437
theorem B444379 : Blo 231814 444379 := bstep (se 1 (by rfl) ⟨333284, by rfl⟩ : syracuseStep 444379 = 666569) B666569
theorem B1787993 : Blo 231814 1787993 := bstep (se 2 (by rfl) ⟨670497, by rfl⟩ : syracuseStep 1787993 = 1340995) B1340995
theorem B805727 : Blo 231814 805727 := bstep (se 1 (by rfl) ⟨604295, by rfl⟩ : syracuseStep 805727 = 1208591) B1208591
theorem B805895 : Blo 231814 805895 := bstep (se 1 (by rfl) ⟨604421, by rfl⟩ : syracuseStep 805895 = 1208843) B1208843
theorem B5983631 : Blo 231814 5983631 := bstep (se 1 (by rfl) ⟨4487723, by rfl⟩ : syracuseStep 5983631 = 8975447) B8975447
theorem B1789451 : Blo 231814 1789451 := bstep (se 1 (by rfl) ⟨1342088, by rfl⟩ : syracuseStep 1789451 = 2684177) B2684177
theorem B675353 : Blo 231814 675353 := bstep (se 2 (by rfl) ⟨253257, by rfl⟩ : syracuseStep 675353 = 506515) B506515
theorem B347771 : Blo 231814 347771 := bstep (se 1 (by rfl) ⟨260828, by rfl⟩ : syracuseStep 347771 = 521657) B521657
theorem B1887877 : Blo 231814 1887877 := bstep (se 4 (by rfl) ⟨176988, by rfl⟩ : syracuseStep 1887877 = 353977) B353977
theorem B347897 : Blo 231814 347897 := bstep (se 2 (by rfl) ⟨130461, by rfl⟩ : syracuseStep 347897 = 260923) B260923
theorem B347999 : Blo 231814 347999 := bstep (se 1 (by rfl) ⟨260999, by rfl⟩ : syracuseStep 347999 = 521999) B521999
theorem B348011 : Blo 231814 348011 := bstep (se 1 (by rfl) ⟨261008, by rfl⟩ : syracuseStep 348011 = 522017) B522017
theorem B1331063 : Blo 231814 1331063 := bstep (se 1 (by rfl) ⟨998297, by rfl⟩ : syracuseStep 1331063 = 1996595) B1996595
theorem B249895 : Blo 231814 249895 := bstep (se 1 (by rfl) ⟨187421, by rfl⟩ : syracuseStep 249895 = 374843) B374843
theorem B348239 : Blo 231814 348239 := bstep (se 1 (by rfl) ⟨261179, by rfl⟩ : syracuseStep 348239 = 522359) B522359
theorem B8605777 : Blo 231814 8605777 := bstep (se 2 (by rfl) ⟨3227166, by rfl⟩ : syracuseStep 8605777 = 6454333) B6454333
theorem B446543 : Blo 231814 446543 := bstep (se 1 (by rfl) ⟨334907, by rfl⟩ : syracuseStep 446543 = 669815) B669815
theorem B1331315 : Blo 231814 1331315 := bstep (se 1 (by rfl) ⟨998486, by rfl⟩ : syracuseStep 1331315 = 1996973) B1996973
theorem B348359 : Blo 231814 348359 := bstep (se 1 (by rfl) ⟨261269, by rfl⟩ : syracuseStep 348359 = 522539) B522539
theorem B348521 : Blo 231814 348521 := bstep (se 2 (by rfl) ⟨130695, by rfl⟩ : syracuseStep 348521 = 261391) B261391
theorem B348599 : Blo 231814 348599 := bstep (se 1 (by rfl) ⟨261449, by rfl⟩ : syracuseStep 348599 = 522899) B522899
theorem B348635 : Blo 231814 348635 := bstep (se 1 (by rfl) ⟨261476, by rfl⟩ : syracuseStep 348635 = 522953) B522953
theorem B3592763 : Blo 231814 3592763 := bstep (se 1 (by rfl) ⟨2694572, by rfl⟩ : syracuseStep 3592763 = 5389145) B5389145
theorem B1069777 : Blo 231814 1069777 := bstep (se 2 (by rfl) ⟨401166, by rfl⟩ : syracuseStep 1069777 = 802333) B802333
theorem B349103 : Blo 231814 349103 := bstep (se 1 (by rfl) ⟨261827, by rfl⟩ : syracuseStep 349103 = 523655) B523655
theorem B349193 : Blo 231814 349193 := bstep (se 2 (by rfl) ⟨130947, by rfl⟩ : syracuseStep 349193 = 261895) B261895
theorem B447527 : Blo 231814 447527 := bstep (se 1 (by rfl) ⟨335645, by rfl⟩ : syracuseStep 447527 = 671291) B671291
theorem B349223 : Blo 231814 349223 := bstep (se 1 (by rfl) ⟨261917, by rfl⟩ : syracuseStep 349223 = 523835) B523835
theorem B3396653 : Blo 231814 3396653 := bstep (se 3 (by rfl) ⟨636872, by rfl⟩ : syracuseStep 3396653 = 1273745) B1273745
theorem B447545 : Blo 231814 447545 := bstep (se 2 (by rfl) ⟨167829, by rfl⟩ : syracuseStep 447545 = 335659) B335659
theorem B316495 : Blo 231814 316495 := bstep (se 1 (by rfl) ⟨237371, by rfl⟩ : syracuseStep 316495 = 474743) B474743
theorem B349307 : Blo 231814 349307 := bstep (se 1 (by rfl) ⟨261980, by rfl⟩ : syracuseStep 349307 = 523961) B523961
theorem B4084937 : Blo 231814 4084937 := bstep (se 2 (by rfl) ⟨1531851, by rfl⟩ : syracuseStep 4084937 = 3063703) B3063703
theorem B1692875 : Blo 231814 1692875 := bstep (se 1 (by rfl) ⟨1269656, by rfl⟩ : syracuseStep 1692875 = 2539313) B2539313
theorem B349433 : Blo 231814 349433 := bstep (se 2 (by rfl) ⟨131037, by rfl⟩ : syracuseStep 349433 = 262075) B262075
theorem B349535 : Blo 231814 349535 := bstep (se 1 (by rfl) ⟨262151, by rfl⟩ : syracuseStep 349535 = 524303) B524303
theorem B349547 : Blo 231814 349547 := bstep (se 1 (by rfl) ⟨262160, by rfl⟩ : syracuseStep 349547 = 524321) B524321
theorem B4773437 : Blo 231814 4773437 := bstep (se 3 (by rfl) ⟨895019, by rfl⟩ : syracuseStep 4773437 = 1790039) B1790039
theorem B3200573 : Blo 231814 3200573 := bstep (se 3 (by rfl) ⟨600107, by rfl⟩ : syracuseStep 3200573 = 1200215) B1200215
theorem B349775 : Blo 231814 349775 := bstep (se 1 (by rfl) ⟨262331, by rfl⟩ : syracuseStep 349775 = 524663) B524663
theorem B251471 : Blo 231814 251471 := bstep (se 1 (by rfl) ⟨188603, by rfl⟩ : syracuseStep 251471 = 377207) B377207
theorem B2512583 : Blo 231814 2512583 := bstep (se 1 (by rfl) ⟨1884437, by rfl⟩ : syracuseStep 2512583 = 3768875) B3768875
theorem B349895 : Blo 231814 349895 := bstep (se 1 (by rfl) ⟨262421, by rfl⟩ : syracuseStep 349895 = 524843) B524843
theorem B350057 : Blo 231814 350057 := bstep (se 2 (by rfl) ⟨131271, by rfl⟩ : syracuseStep 350057 = 262543) B262543
theorem B1005473 : Blo 231814 1005473 := bstep (se 2 (by rfl) ⟨377052, by rfl⟩ : syracuseStep 1005473 = 754105) B754105
theorem B350135 : Blo 231814 350135 := bstep (se 1 (by rfl) ⟨262601, by rfl⟩ : syracuseStep 350135 = 525203) B525203
theorem B1300411 : Blo 231814 1300411 := bstep (se 1 (by rfl) ⟨975308, by rfl⟩ : syracuseStep 1300411 = 1950617) B1950617
theorem B350171 : Blo 231814 350171 := bstep (se 1 (by rfl) ⟨262628, by rfl⟩ : syracuseStep 350171 = 525257) B525257
theorem B350639 : Blo 231814 350639 := bstep (se 1 (by rfl) ⟨262979, by rfl⟩ : syracuseStep 350639 = 525959) B525959
theorem B350729 : Blo 231814 350729 := bstep (se 2 (by rfl) ⟨131523, by rfl⟩ : syracuseStep 350729 = 263047) B263047
theorem B350759 : Blo 231814 350759 := bstep (se 1 (by rfl) ⟨263069, by rfl⟩ : syracuseStep 350759 = 526139) B526139
theorem B744059 : Blo 231814 744059 := bstep (se 1 (by rfl) ⟨558044, by rfl⟩ : syracuseStep 744059 = 1116089) B1116089
theorem B350843 : Blo 231814 350843 := bstep (se 1 (by rfl) ⟨263132, by rfl⟩ : syracuseStep 350843 = 526265) B526265
theorem B1071751 : Blo 231814 1071751 := bstep (se 1 (by rfl) ⟨803813, by rfl⟩ : syracuseStep 1071751 = 1607627) B1607627
theorem B350969 : Blo 231814 350969 := bstep (se 2 (by rfl) ⟨131613, by rfl⟩ : syracuseStep 350969 = 263227) B263227
theorem B351071 : Blo 231814 351071 := bstep (se 1 (by rfl) ⟨263303, by rfl⟩ : syracuseStep 351071 = 526607) B526607
theorem B351083 : Blo 231814 351083 := bstep (se 1 (by rfl) ⟨263312, by rfl⟩ : syracuseStep 351083 = 526625) B526625
theorem B351311 : Blo 231814 351311 := bstep (se 1 (by rfl) ⟨263483, by rfl⟩ : syracuseStep 351311 = 526967) B526967
theorem B1694891 : Blo 231814 1694891 := bstep (se 1 (by rfl) ⟨1271168, by rfl⟩ : syracuseStep 1694891 = 2542337) B2542337
theorem B351431 : Blo 231814 351431 := bstep (se 1 (by rfl) ⟨263573, by rfl⟩ : syracuseStep 351431 = 527147) B527147
theorem B6774029 : Blo 231814 6774029 := bstep (se 3 (by rfl) ⟨1270130, by rfl⟩ : syracuseStep 6774029 = 2540261) B2540261
theorem B351593 : Blo 231814 351593 := bstep (se 2 (by rfl) ⟨131847, by rfl⟩ : syracuseStep 351593 = 263695) B263695
theorem B351671 : Blo 231814 351671 := bstep (se 1 (by rfl) ⟨263753, by rfl⟩ : syracuseStep 351671 = 527507) B527507
theorem B351707 : Blo 231814 351707 := bstep (se 1 (by rfl) ⟨263780, by rfl⟩ : syracuseStep 351707 = 527561) B527561
theorem B941555 : Blo 231814 941555 := bstep (se 1 (by rfl) ⟨706166, by rfl⟩ : syracuseStep 941555 = 1412333) B1412333
theorem B1891937 : Blo 231814 1891937 := bstep (se 2 (by rfl) ⟨709476, by rfl⟩ : syracuseStep 1891937 = 1418953) B1418953
theorem B515783 : Blo 231814 515783 := bstep (se 1 (by rfl) ⟨386837, by rfl⟩ : syracuseStep 515783 = 773675) B773675
theorem B745175 : Blo 231814 745175 := bstep (se 1 (by rfl) ⟨558881, by rfl⟩ : syracuseStep 745175 = 1117763) B1117763
theorem B745289 : Blo 231814 745289 := bstep (se 2 (by rfl) ⟨279483, by rfl⟩ : syracuseStep 745289 = 558967) B558967
theorem B352175 : Blo 231814 352175 := bstep (se 1 (by rfl) ⟨264131, by rfl⟩ : syracuseStep 352175 = 528263) B528263
theorem B352265 : Blo 231814 352265 := bstep (se 2 (by rfl) ⟨132099, by rfl⟩ : syracuseStep 352265 = 264199) B264199
theorem B352295 : Blo 231814 352295 := bstep (se 1 (by rfl) ⟨264221, by rfl⟩ : syracuseStep 352295 = 528443) B528443
theorem B2973773 : Blo 231814 2973773 := bstep (se 3 (by rfl) ⟨557582, by rfl⟩ : syracuseStep 2973773 = 1115165) B1115165
theorem B1794163 : Blo 231814 1794163 := bstep (se 1 (by rfl) ⟨1345622, by rfl⟩ : syracuseStep 1794163 = 2691245) B2691245
theorem B352379 : Blo 231814 352379 := bstep (se 1 (by rfl) ⟨264284, by rfl⟩ : syracuseStep 352379 = 528569) B528569
theorem B352505 : Blo 231814 352505 := bstep (se 2 (by rfl) ⟨132189, by rfl⟩ : syracuseStep 352505 = 264379) B264379
theorem B352607 : Blo 231814 352607 := bstep (se 1 (by rfl) ⟨264455, by rfl⟩ : syracuseStep 352607 = 528911) B528911
theorem B12312931 : Blo 231814 12312931 := bstep (se 1 (by rfl) ⟨9234698, by rfl⟩ : syracuseStep 12312931 = 18469397) B18469397
theorem B352619 : Blo 231814 352619 := bstep (se 1 (by rfl) ⟨264464, by rfl⟩ : syracuseStep 352619 = 528929) B528929
theorem B352847 : Blo 231814 352847 := bstep (se 1 (by rfl) ⟨264635, by rfl⟩ : syracuseStep 352847 = 529271) B529271
theorem B352967 : Blo 231814 352967 := bstep (se 1 (by rfl) ⟨264725, by rfl⟩ : syracuseStep 352967 = 529451) B529451
theorem B353129 : Blo 231814 353129 := bstep (se 2 (by rfl) ⟨132423, by rfl⟩ : syracuseStep 353129 = 264847) B264847
theorem B353207 : Blo 231814 353207 := bstep (se 1 (by rfl) ⟨264905, by rfl⟩ : syracuseStep 353207 = 529811) B529811
theorem B353243 : Blo 231814 353243 := bstep (se 1 (by rfl) ⟨264932, by rfl⟩ : syracuseStep 353243 = 529865) B529865
theorem B6382745 : Blo 231814 6382745 := bstep (se 2 (by rfl) ⟨2393529, by rfl⟩ : syracuseStep 6382745 = 4787059) B4787059
theorem B2253977 : Blo 231814 2253977 := bstep (se 2 (by rfl) ⟨845241, by rfl⟩ : syracuseStep 2253977 = 1690483) B1690483
theorem B353479 : Blo 231814 353479 := bstep (se 1 (by rfl) ⟨265109, by rfl⟩ : syracuseStep 353479 = 530219) B530219
theorem B353711 : Blo 231814 353711 := bstep (se 1 (by rfl) ⟨265283, by rfl⟩ : syracuseStep 353711 = 530567) B530567
theorem B1893851 : Blo 231814 1893851 := bstep (se 1 (by rfl) ⟨1420388, by rfl⟩ : syracuseStep 1893851 = 2840777) B2840777
theorem B1763207 : Blo 231814 1763207 := bstep (se 1 (by rfl) ⟨1322405, by rfl⟩ : syracuseStep 1763207 = 2644811) B2644811
theorem B845977 : Blo 231814 845977 := bstep (se 2 (by rfl) ⟨317241, by rfl⟩ : syracuseStep 845977 = 634483) B634483
theorem B1141121 : Blo 231814 1141121 := bstep (se 2 (by rfl) ⟨427920, by rfl⟩ : syracuseStep 1141121 = 855841) B855841
theorem B748057 : Blo 231814 748057 := bstep (se 2 (by rfl) ⟨280521, by rfl⟩ : syracuseStep 748057 = 561043) B561043
theorem B3337037 : Blo 231814 3337037 := bstep (se 3 (by rfl) ⟨625694, by rfl⟩ : syracuseStep 3337037 = 1251389) B1251389
theorem B1502059 : Blo 231814 1502059 := bstep (se 1 (by rfl) ⟨1126544, by rfl⟩ : syracuseStep 1502059 = 2253089) B2253089
theorem B1174985 : Blo 231814 1174985 := bstep (se 2 (by rfl) ⟨440619, by rfl⟩ : syracuseStep 1174985 = 881239) B881239
theorem B880267 : Blo 231814 880267 := bstep (se 1 (by rfl) ⟨660200, by rfl⟩ : syracuseStep 880267 = 1320401) B1320401
theorem B1503137 : Blo 231814 1503137 := bstep (se 2 (by rfl) ⟨563676, by rfl⟩ : syracuseStep 1503137 = 1127353) B1127353
theorem B880571 : Blo 231814 880571 := bstep (se 1 (by rfl) ⟨660428, by rfl⟩ : syracuseStep 880571 = 1320857) B1320857
theorem B1503289 : Blo 231814 1503289 := bstep (se 2 (by rfl) ⟨563733, by rfl⟩ : syracuseStep 1503289 = 1127467) B1127467
theorem B1175633 : Blo 231814 1175633 := bstep (se 2 (by rfl) ⟨440862, by rfl⟩ : syracuseStep 1175633 = 881725) B881725
theorem B782945 : Blo 231814 782945 := bstep (se 2 (by rfl) ⟨293604, by rfl⟩ : syracuseStep 782945 = 587209) B587209
theorem B947279 : Blo 231814 947279 := bstep (se 1 (by rfl) ⟨710459, by rfl⟩ : syracuseStep 947279 = 1420919) B1420919
theorem B1340495 : Blo 231814 1340495 := bstep (se 1 (by rfl) ⟨1005371, by rfl⟩ : syracuseStep 1340495 = 2010743) B2010743
theorem B2880715 : Blo 231814 2880715 := bstep (se 1 (by rfl) ⟨2160536, by rfl⟩ : syracuseStep 2880715 = 4321073) B4321073
theorem B5732021 : Blo 231814 5732021 := bstep (se 5 (by rfl) ⟨268688, by rfl⟩ : syracuseStep 5732021 = 537377) B537377
theorem B521927 : Blo 231814 521927 := bstep (se 1 (by rfl) ⟨391445, by rfl⟩ : syracuseStep 521927 = 782891) B782891
theorem B587513 : Blo 231814 587513 := bstep (se 2 (by rfl) ⟨220317, by rfl⟩ : syracuseStep 587513 = 440635) B440635
theorem B849773 : Blo 231814 849773 := bstep (se 3 (by rfl) ⟨159332, by rfl⟩ : syracuseStep 849773 = 318665) B318665
theorem B587695 : Blo 231814 587695 := bstep (se 1 (by rfl) ⟨440771, by rfl⟩ : syracuseStep 587695 = 881543) B881543
theorem B784403 : Blo 231814 784403 := bstep (se 1 (by rfl) ⟨588302, by rfl⟩ : syracuseStep 784403 = 1176605) B1176605
theorem B1341521 : Blo 231814 1341521 := bstep (se 2 (by rfl) ⟨503070, by rfl⟩ : syracuseStep 1341521 = 1006141) B1006141
theorem B1767581 : Blo 231814 1767581 := bstep (se 3 (by rfl) ⟨331421, by rfl⟩ : syracuseStep 1767581 = 662843) B662843
theorem B784727 : Blo 231814 784727 := bstep (se 1 (by rfl) ⟨588545, by rfl⟩ : syracuseStep 784727 = 1177091) B1177091
theorem B588161 : Blo 231814 588161 := bstep (se 2 (by rfl) ⟨220560, by rfl⟩ : syracuseStep 588161 = 441121) B441121
theorem B391567 : Blo 231814 391567 := bstep (se 1 (by rfl) ⟨293675, by rfl⟩ : syracuseStep 391567 = 587351) B587351
theorem B522791 : Blo 231814 522791 := bstep (se 1 (by rfl) ⟨392093, by rfl⟩ : syracuseStep 522791 = 784187) B784187
theorem B588617 : Blo 231814 588617 := bstep (se 2 (by rfl) ⟨220731, by rfl⟩ : syracuseStep 588617 = 441463) B441463
theorem B260959 : Blo 231814 260959 := bstep (se 1 (by rfl) ⟨195719, by rfl⟩ : syracuseStep 260959 = 391439) B391439
theorem B523115 : Blo 231814 523115 := bstep (se 1 (by rfl) ⟨392336, by rfl⟩ : syracuseStep 523115 = 784673) B784673
theorem B523169 : Blo 231814 523169 := bstep (se 2 (by rfl) ⟨196188, by rfl⟩ : syracuseStep 523169 = 392377) B392377
theorem B293807 : Blo 231814 293807 := bstep (se 1 (by rfl) ⟨220355, by rfl⟩ : syracuseStep 293807 = 440711) B440711
theorem B392249 : Blo 231814 392249 := bstep (se 2 (by rfl) ⟨147093, by rfl⟩ : syracuseStep 392249 = 294187) B294187
theorem B588971 : Blo 231814 588971 := bstep (se 1 (by rfl) ⟨441728, by rfl⟩ : syracuseStep 588971 = 883457) B883457
theorem B2260163 : Blo 231814 2260163 := bstep (se 1 (by rfl) ⟨1695122, by rfl⟩ : syracuseStep 2260163 = 3390245) B3390245
theorem B261319 : Blo 231814 261319 := bstep (se 1 (by rfl) ⟨195989, by rfl⟩ : syracuseStep 261319 = 391979) B391979
theorem B523511 : Blo 231814 523511 := bstep (se 1 (by rfl) ⟨392633, by rfl⟩ : syracuseStep 523511 = 785267) B785267
theorem B785807 : Blo 231814 785807 := bstep (se 1 (by rfl) ⟨589355, by rfl⟩ : syracuseStep 785807 = 1178711) B1178711
theorem B786131 : Blo 231814 786131 := bstep (se 1 (by rfl) ⟨589598, by rfl⟩ : syracuseStep 786131 = 1179197) B1179197
theorem B392951 : Blo 231814 392951 := bstep (se 1 (by rfl) ⟨294713, by rfl⟩ : syracuseStep 392951 = 589427) B589427
theorem B524105 : Blo 231814 524105 := bstep (se 2 (by rfl) ⟨196539, by rfl⟩ : syracuseStep 524105 = 393079) B393079
theorem B884641 : Blo 231814 884641 := bstep (se 2 (by rfl) ⟨331740, by rfl⟩ : syracuseStep 884641 = 663481) B663481
theorem B589751 : Blo 231814 589751 := bstep (se 1 (by rfl) ⟨442313, by rfl⟩ : syracuseStep 589751 = 884627) B884627
theorem B524393 : Blo 231814 524393 := bstep (se 2 (by rfl) ⟨196647, by rfl⟩ : syracuseStep 524393 = 393295) B393295
theorem B2392217 : Blo 231814 2392217 := bstep (se 2 (by rfl) ⟨897081, by rfl⟩ : syracuseStep 2392217 = 1794163) B1794163
theorem B884945 : Blo 231814 884945 := bstep (se 2 (by rfl) ⟨331854, by rfl⟩ : syracuseStep 884945 = 663709) B663709
theorem B262363 : Blo 231814 262363 := bstep (se 1 (by rfl) ⟨196772, by rfl⟩ : syracuseStep 262363 = 393545) B393545
theorem B590105 : Blo 231814 590105 := bstep (se 2 (by rfl) ⟨221289, by rfl⟩ : syracuseStep 590105 = 442579) B442579
theorem B786779 : Blo 231814 786779 := bstep (se 1 (by rfl) ⟨590084, by rfl⟩ : syracuseStep 786779 = 1180169) B1180169
theorem B16417241 : Blo 231814 16417241 := bstep (se 2 (by rfl) ⟨6156465, by rfl⟩ : syracuseStep 16417241 = 12312931) B12312931
theorem B262651 : Blo 231814 262651 := bstep (se 1 (by rfl) ⟨196988, by rfl⟩ : syracuseStep 262651 = 393977) B393977
theorem B590399 : Blo 231814 590399 := bstep (se 1 (by rfl) ⟨442799, by rfl⟩ : syracuseStep 590399 = 885599) B885599
theorem B524879 : Blo 231814 524879 := bstep (se 1 (by rfl) ⟨393659, by rfl⟩ : syracuseStep 524879 = 787319) B787319
theorem B393835 : Blo 231814 393835 := bstep (se 1 (by rfl) ⟨295376, by rfl⟩ : syracuseStep 393835 = 590753) B590753
theorem B885401 : Blo 231814 885401 := bstep (se 2 (by rfl) ⟨332025, by rfl⟩ : syracuseStep 885401 = 664051) B664051
theorem B1180331 : Blo 231814 1180331 := bstep (se 1 (by rfl) ⟨885248, by rfl⟩ : syracuseStep 1180331 = 1770497) B1770497
theorem B262831 : Blo 231814 262831 := bstep (se 1 (by rfl) ⟨197123, by rfl⟩ : syracuseStep 262831 = 394247) B394247
theorem B885431 : Blo 231814 885431 := bstep (se 1 (by rfl) ⟨664073, by rfl⟩ : syracuseStep 885431 = 1328147) B1328147
theorem B525023 : Blo 231814 525023 := bstep (se 1 (by rfl) ⟨393767, by rfl⟩ : syracuseStep 525023 = 787535) B787535
theorem B590611 : Blo 231814 590611 := bstep (se 1 (by rfl) ⟨442958, by rfl⟩ : syracuseStep 590611 = 885917) B885917
theorem B1147727 : Blo 231814 1147727 := bstep (se 1 (by rfl) ⟨860795, by rfl⟩ : syracuseStep 1147727 = 1721591) B1721591
theorem B394139 : Blo 231814 394139 := bstep (se 1 (by rfl) ⟨295604, by rfl⟩ : syracuseStep 394139 = 591209) B591209
theorem B263119 : Blo 231814 263119 := bstep (se 1 (by rfl) ⟨197339, by rfl⟩ : syracuseStep 263119 = 394679) B394679
theorem B525275 : Blo 231814 525275 := bstep (se 1 (by rfl) ⟨393956, by rfl⟩ : syracuseStep 525275 = 787913) B787913
theorem B2884571 : Blo 231814 2884571 := bstep (se 1 (by rfl) ⟨2163428, by rfl⟩ : syracuseStep 2884571 = 4326857) B4326857
theorem B525455 : Blo 231814 525455 := bstep (se 1 (by rfl) ⟨394091, by rfl⟩ : syracuseStep 525455 = 788183) B788183
theorem B1180817 : Blo 231814 1180817 := bstep (se 2 (by rfl) ⟨442806, by rfl⟩ : syracuseStep 1180817 = 885613) B885613
theorem B591047 : Blo 231814 591047 := bstep (se 1 (by rfl) ⟨443285, by rfl⟩ : syracuseStep 591047 = 886571) B886571
theorem B525545 : Blo 231814 525545 := bstep (se 2 (by rfl) ⟨197079, by rfl⟩ : syracuseStep 525545 = 394159) B394159
theorem B591097 : Blo 231814 591097 := bstep (se 2 (by rfl) ⟨221661, by rfl⟩ : syracuseStep 591097 = 443323) B443323
theorem B525599 : Blo 231814 525599 := bstep (se 1 (by rfl) ⟨394199, by rfl⟩ : syracuseStep 525599 = 788399) B788399
theorem B787751 : Blo 231814 787751 := bstep (se 1 (by rfl) ⟨590813, by rfl⟩ : syracuseStep 787751 = 1181627) B1181627
theorem B263515 : Blo 231814 263515 := bstep (se 1 (by rfl) ⟨197636, by rfl⟩ : syracuseStep 263515 = 395273) B395273
theorem B263623 : Blo 231814 263623 := bstep (se 1 (by rfl) ⟨197717, by rfl⟩ : syracuseStep 263623 = 395435) B395435
theorem B526121 : Blo 231814 526121 := bstep (se 2 (by rfl) ⟨197295, by rfl⟩ : syracuseStep 526121 = 394591) B394591
theorem B263983 : Blo 231814 263983 := bstep (se 1 (by rfl) ⟨197987, by rfl⟩ : syracuseStep 263983 = 395975) B395975
theorem B591745 : Blo 231814 591745 := bstep (se 2 (by rfl) ⟨221904, by rfl⟩ : syracuseStep 591745 = 443809) B443809
theorem B264091 : Blo 231814 264091 := bstep (se 1 (by rfl) ⟨198068, by rfl⟩ : syracuseStep 264091 = 396137) B396137
theorem B788615 : Blo 231814 788615 := bstep (se 1 (by rfl) ⟨591461, by rfl⟩ : syracuseStep 788615 = 1182923) B1182923
theorem B264487 : Blo 231814 264487 := bstep (se 1 (by rfl) ⟨198365, by rfl⟩ : syracuseStep 264487 = 396731) B396731
theorem B330095 : Blo 231814 330095 := bstep (se 1 (by rfl) ⟨247571, by rfl⟩ : syracuseStep 330095 = 495143) B495143
theorem B264559 : Blo 231814 264559 := bstep (se 1 (by rfl) ⟨198419, by rfl⟩ : syracuseStep 264559 = 396839) B396839
theorem B231847 : Blo 231814 231847 := bstep (se 1 (by rfl) ⟨173885, by rfl⟩ : syracuseStep 231847 = 347771) B347771
theorem B2165159 : Blo 231814 2165159 := bstep (se 1 (by rfl) ⟨1623869, by rfl⟩ : syracuseStep 2165159 = 3247739) B3247739
theorem B231931 : Blo 231814 231931 := bstep (se 1 (by rfl) ⟨173948, by rfl⟩ : syracuseStep 231931 = 347897) B347897
theorem B231999 : Blo 231814 231999 := bstep (se 1 (by rfl) ⟨173999, by rfl⟩ : syracuseStep 231999 = 347999) B347999
theorem B232007 : Blo 231814 232007 := bstep (se 1 (by rfl) ⟨174005, by rfl⟩ : syracuseStep 232007 = 348011) B348011
theorem B264775 : Blo 231814 264775 := bstep (se 1 (by rfl) ⟨198581, by rfl⟩ : syracuseStep 264775 = 397163) B397163
theorem B887375 : Blo 231814 887375 := bstep (se 1 (by rfl) ⟨665531, by rfl⟩ : syracuseStep 887375 = 1331063) B1331063
theorem B592505 : Blo 231814 592505 := bstep (se 2 (by rfl) ⟨222189, by rfl⟩ : syracuseStep 592505 = 444379) B444379
theorem B592555 : Blo 231814 592555 := bstep (se 1 (by rfl) ⟨444416, by rfl⟩ : syracuseStep 592555 = 888833) B888833
theorem B1510109 : Blo 231814 1510109 := bstep (se 3 (by rfl) ⟨283145, by rfl⟩ : syracuseStep 1510109 = 566291) B566291
theorem B232159 : Blo 231814 232159 := bstep (se 1 (by rfl) ⟨174119, by rfl⟩ : syracuseStep 232159 = 348239) B348239
theorem B297695 : Blo 231814 297695 := bstep (se 1 (by rfl) ⟨223271, by rfl⟩ : syracuseStep 297695 = 446543) B446543
theorem B887543 : Blo 231814 887543 := bstep (se 1 (by rfl) ⟨665657, by rfl⟩ : syracuseStep 887543 = 1331315) B1331315
theorem B232239 : Blo 231814 232239 := bstep (se 1 (by rfl) ⟨174179, by rfl⟩ : syracuseStep 232239 = 348359) B348359
theorem B527183 : Blo 231814 527183 := bstep (se 1 (by rfl) ⟨395387, by rfl⟩ : syracuseStep 527183 = 790775) B790775
theorem B232347 : Blo 231814 232347 := bstep (se 1 (by rfl) ⟨174260, by rfl⟩ : syracuseStep 232347 = 348521) B348521
theorem B232399 : Blo 231814 232399 := bstep (se 1 (by rfl) ⟨174299, by rfl⟩ : syracuseStep 232399 = 348599) B348599
theorem B592859 : Blo 231814 592859 := bstep (se 1 (by rfl) ⟨444644, by rfl⟩ : syracuseStep 592859 = 889289) B889289
theorem B232423 : Blo 231814 232423 := bstep (se 1 (by rfl) ⟨174317, by rfl⟩ : syracuseStep 232423 = 348635) B348635
theorem B2395175 : Blo 231814 2395175 := bstep (se 1 (by rfl) ⟨1796381, by rfl⟩ : syracuseStep 2395175 = 3592763) B3592763
theorem B527399 : Blo 231814 527399 := bstep (se 1 (by rfl) ⟨395549, by rfl⟩ : syracuseStep 527399 = 791099) B791099
theorem B527579 : Blo 231814 527579 := bstep (se 1 (by rfl) ⟨395684, by rfl⟩ : syracuseStep 527579 = 791369) B791369
theorem B232735 : Blo 231814 232735 := bstep (se 1 (by rfl) ⟨174551, by rfl⟩ : syracuseStep 232735 = 349103) B349103
theorem B593183 : Blo 231814 593183 := bstep (se 1 (by rfl) ⟨444887, by rfl⟩ : syracuseStep 593183 = 889775) B889775
theorem B232795 : Blo 231814 232795 := bstep (se 1 (by rfl) ⟨174596, by rfl⟩ : syracuseStep 232795 = 349193) B349193
theorem B789857 : Blo 231814 789857 := bstep (se 2 (by rfl) ⟨296196, by rfl⟩ : syracuseStep 789857 = 592393) B592393
theorem B298351 : Blo 231814 298351 := bstep (se 1 (by rfl) ⟨223763, by rfl⟩ : syracuseStep 298351 = 447527) B447527
theorem B232815 : Blo 231814 232815 := bstep (se 1 (by rfl) ⟨174611, by rfl⟩ : syracuseStep 232815 = 349223) B349223
theorem B265583 : Blo 231814 265583 := bstep (se 1 (by rfl) ⟨199187, by rfl⟩ : syracuseStep 265583 = 398375) B398375
theorem B2264435 : Blo 231814 2264435 := bstep (se 1 (by rfl) ⟨1698326, by rfl⟩ : syracuseStep 2264435 = 3396653) B3396653
theorem B527777 : Blo 231814 527777 := bstep (se 2 (by rfl) ⟨197916, by rfl⟩ : syracuseStep 527777 = 395833) B395833
theorem B232871 : Blo 231814 232871 := bstep (se 1 (by rfl) ⟨174653, by rfl⟩ : syracuseStep 232871 = 349307) B349307
theorem B2723291 : Blo 231814 2723291 := bstep (se 1 (by rfl) ⟨2042468, by rfl⟩ : syracuseStep 2723291 = 4084937) B4084937
theorem B232955 : Blo 231814 232955 := bstep (se 1 (by rfl) ⟨174716, by rfl⟩ : syracuseStep 232955 = 349433) B349433
theorem B1183247 : Blo 231814 1183247 := bstep (se 1 (by rfl) ⟨887435, by rfl⟩ : syracuseStep 1183247 = 1774871) B1774871
theorem B233023 : Blo 231814 233023 := bstep (se 1 (by rfl) ⟨174767, by rfl⟩ : syracuseStep 233023 = 349535) B349535
theorem B233031 : Blo 231814 233031 := bstep (se 1 (by rfl) ⟨174773, by rfl⟩ : syracuseStep 233031 = 349547) B349547
theorem B3182291 : Blo 231814 3182291 := bstep (se 1 (by rfl) ⟨2386718, by rfl⟩ : syracuseStep 3182291 = 4773437) B4773437
theorem B2133715 : Blo 231814 2133715 := bstep (se 1 (by rfl) ⟨1600286, by rfl⟩ : syracuseStep 2133715 = 3200573) B3200573
theorem B233183 : Blo 231814 233183 := bstep (se 1 (by rfl) ⟨174887, by rfl⟩ : syracuseStep 233183 = 349775) B349775
theorem B1675055 : Blo 231814 1675055 := bstep (se 1 (by rfl) ⟨1256291, by rfl⟩ : syracuseStep 1675055 = 2512583) B2512583
theorem B233263 : Blo 231814 233263 := bstep (se 1 (by rfl) ⟨174947, by rfl⟩ : syracuseStep 233263 = 349895) B349895
theorem B2002745 : Blo 231814 2002745 := bstep (se 2 (by rfl) ⟨751029, by rfl⟩ : syracuseStep 2002745 = 1502059) B1502059
theorem B233371 : Blo 231814 233371 := bstep (se 1 (by rfl) ⟨175028, by rfl⟩ : syracuseStep 233371 = 350057) B350057
theorem B233423 : Blo 231814 233423 := bstep (se 1 (by rfl) ⟨175067, by rfl⟩ : syracuseStep 233423 = 350135) B350135
theorem B528335 : Blo 231814 528335 := bstep (se 1 (by rfl) ⟨396251, by rfl⟩ : syracuseStep 528335 = 792503) B792503
theorem B233447 : Blo 231814 233447 := bstep (se 1 (by rfl) ⟨175085, by rfl⟩ : syracuseStep 233447 = 350171) B350171
theorem B6426773 : Blo 231814 6426773 := bstep (se 6 (by rfl) ⟨150627, by rfl⟩ : syracuseStep 6426773 = 301255) B301255
theorem B233759 : Blo 231814 233759 := bstep (se 1 (by rfl) ⟨175319, by rfl⟩ : syracuseStep 233759 = 350639) B350639
theorem B528713 : Blo 231814 528713 := bstep (se 2 (by rfl) ⟨198267, by rfl⟩ : syracuseStep 528713 = 396535) B396535
theorem B233819 : Blo 231814 233819 := bstep (se 1 (by rfl) ⟨175364, by rfl⟩ : syracuseStep 233819 = 350729) B350729
theorem B528731 : Blo 231814 528731 := bstep (se 1 (by rfl) ⟨396548, by rfl⟩ : syracuseStep 528731 = 793097) B793097
theorem B233839 : Blo 231814 233839 := bstep (se 1 (by rfl) ⟨175379, by rfl⟩ : syracuseStep 233839 = 350759) B350759
theorem B594287 : Blo 231814 594287 := bstep (se 1 (by rfl) ⟨445715, by rfl⟩ : syracuseStep 594287 = 891431) B891431
theorem B3019139 : Blo 231814 3019139 := bstep (se 1 (by rfl) ⟨2264354, by rfl⟩ : syracuseStep 3019139 = 4528709) B4528709
theorem B496039 : Blo 231814 496039 := bstep (se 1 (by rfl) ⟨372029, by rfl⟩ : syracuseStep 496039 = 744059) B744059
theorem B233895 : Blo 231814 233895 := bstep (se 1 (by rfl) ⟨175421, by rfl⟩ : syracuseStep 233895 = 350843) B350843
theorem B1184219 : Blo 231814 1184219 := bstep (se 1 (by rfl) ⟨888164, by rfl⟩ : syracuseStep 1184219 = 1776329) B1776329
theorem B233979 : Blo 231814 233979 := bstep (se 1 (by rfl) ⟨175484, by rfl⟩ : syracuseStep 233979 = 350969) B350969
theorem B234047 : Blo 231814 234047 := bstep (se 1 (by rfl) ⟨175535, by rfl⟩ : syracuseStep 234047 = 351071) B351071
theorem B234055 : Blo 231814 234055 := bstep (se 1 (by rfl) ⟨175541, by rfl⟩ : syracuseStep 234055 = 351083) B351083
theorem B398047 : Blo 231814 398047 := bstep (se 1 (by rfl) ⟨298535, by rfl⟩ : syracuseStep 398047 = 597071) B597071
theorem B234207 : Blo 231814 234207 := bstep (se 1 (by rfl) ⟨175655, by rfl⟩ : syracuseStep 234207 = 351311) B351311
theorem B234287 : Blo 231814 234287 := bstep (se 1 (by rfl) ⟨175715, by rfl⟩ : syracuseStep 234287 = 351431) B351431
theorem B234395 : Blo 231814 234395 := bstep (se 1 (by rfl) ⟨175796, by rfl⟩ : syracuseStep 234395 = 351593) B351593
theorem B529307 : Blo 231814 529307 := bstep (se 1 (by rfl) ⟨396980, by rfl⟩ : syracuseStep 529307 = 793961) B793961
theorem B1184705 : Blo 231814 1184705 := bstep (se 2 (by rfl) ⟨444264, by rfl⟩ : syracuseStep 1184705 = 888529) B888529
theorem B2266061 : Blo 231814 2266061 := bstep (se 3 (by rfl) ⟨424886, by rfl⟩ : syracuseStep 2266061 = 849773) B849773
theorem B234447 : Blo 231814 234447 := bstep (se 1 (by rfl) ⟨175835, by rfl⟩ : syracuseStep 234447 = 351671) B351671
theorem B234471 : Blo 231814 234471 := bstep (se 1 (by rfl) ⟨175853, by rfl⟩ : syracuseStep 234471 = 351707) B351707
theorem B594935 : Blo 231814 594935 := bstep (se 1 (by rfl) ⟨446201, by rfl⟩ : syracuseStep 594935 = 892403) B892403
theorem B529505 : Blo 231814 529505 := bstep (se 2 (by rfl) ⟨198564, by rfl⟩ : syracuseStep 529505 = 397129) B397129
theorem B496783 : Blo 231814 496783 := bstep (se 1 (by rfl) ⟨372587, by rfl⟩ : syracuseStep 496783 = 745175) B745175
theorem B496859 : Blo 231814 496859 := bstep (se 1 (by rfl) ⟨372644, by rfl⟩ : syracuseStep 496859 = 745289) B745289
theorem B791801 : Blo 231814 791801 := bstep (se 2 (by rfl) ⟨296925, by rfl⟩ : syracuseStep 791801 = 593851) B593851
theorem B234783 : Blo 231814 234783 := bstep (se 1 (by rfl) ⟨176087, by rfl⟩ : syracuseStep 234783 = 352175) B352175
theorem B529703 : Blo 231814 529703 := bstep (se 1 (by rfl) ⟨397277, by rfl⟩ : syracuseStep 529703 = 794555) B794555
theorem B234843 : Blo 231814 234843 := bstep (se 1 (by rfl) ⟨176132, by rfl⟩ : syracuseStep 234843 = 352265) B352265
theorem B234863 : Blo 231814 234863 := bstep (se 1 (by rfl) ⟨176147, by rfl⟩ : syracuseStep 234863 = 352295) B352295
theorem B2004385 : Blo 231814 2004385 := bstep (se 2 (by rfl) ⟨751644, by rfl⟩ : syracuseStep 2004385 = 1503289) B1503289
theorem B234919 : Blo 231814 234919 := bstep (se 1 (by rfl) ⟨176189, by rfl⟩ : syracuseStep 234919 = 352379) B352379
theorem B11474369 : Blo 231814 11474369 := bstep (se 2 (by rfl) ⟨4302888, by rfl⟩ : syracuseStep 11474369 = 8605777) B8605777
theorem B235003 : Blo 231814 235003 := bstep (se 1 (by rfl) ⟨176252, by rfl⟩ : syracuseStep 235003 = 352505) B352505
theorem B792071 : Blo 231814 792071 := bstep (se 1 (by rfl) ⟨594053, by rfl⟩ : syracuseStep 792071 = 1188107) B1188107
theorem B235071 : Blo 231814 235071 := bstep (se 1 (by rfl) ⟨176303, by rfl⟩ : syracuseStep 235071 = 352607) B352607
theorem B235079 : Blo 231814 235079 := bstep (se 1 (by rfl) ⟨176309, by rfl⟩ : syracuseStep 235079 = 352619) B352619
theorem B530081 : Blo 231814 530081 := bstep (se 2 (by rfl) ⟨198780, by rfl⟩ : syracuseStep 530081 = 397561) B397561
theorem B235231 : Blo 231814 235231 := bstep (se 1 (by rfl) ⟨176423, by rfl⟩ : syracuseStep 235231 = 352847) B352847
theorem B235311 : Blo 231814 235311 := bstep (se 1 (by rfl) ⟨176483, by rfl⟩ : syracuseStep 235311 = 352967) B352967
theorem B268111 : Blo 231814 268111 := bstep (se 1 (by rfl) ⟨201083, by rfl⟩ : syracuseStep 268111 = 402167) B402167
theorem B235419 : Blo 231814 235419 := bstep (se 1 (by rfl) ⟨176564, by rfl⟩ : syracuseStep 235419 = 353129) B353129
theorem B235471 : Blo 231814 235471 := bstep (se 1 (by rfl) ⟨176603, by rfl⟩ : syracuseStep 235471 = 353207) B353207
theorem B235495 : Blo 231814 235495 := bstep (se 1 (by rfl) ⟨176621, by rfl⟩ : syracuseStep 235495 = 353243) B353243
theorem B530441 : Blo 231814 530441 := bstep (se 2 (by rfl) ⟨198915, by rfl⟩ : syracuseStep 530441 = 397831) B397831
theorem B235807 : Blo 231814 235807 := bstep (se 1 (by rfl) ⟨176855, by rfl⟩ : syracuseStep 235807 = 353711) B353711
theorem B793043 : Blo 231814 793043 := bstep (se 1 (by rfl) ⟨594782, by rfl⟩ : syracuseStep 793043 = 1189565) B1189565
theorem B793151 : Blo 231814 793151 := bstep (se 1 (by rfl) ⟨594863, by rfl⟩ : syracuseStep 793151 = 1189727) B1189727
theorem B3349187 : Blo 231814 3349187 := bstep (se 1 (by rfl) ⟨2511890, by rfl⟩ : syracuseStep 3349187 = 5023781) B5023781
theorem B596879 : Blo 231814 596879 := bstep (se 1 (by rfl) ⟨447659, by rfl⟩ : syracuseStep 596879 = 895319) B895319
theorem B760747 : Blo 231814 760747 := bstep (se 1 (by rfl) ⟨570560, by rfl⟩ : syracuseStep 760747 = 1141121) B1141121
theorem B3840953 : Blo 231814 3840953 := bstep (se 2 (by rfl) ⟨1440357, by rfl⟩ : syracuseStep 3840953 = 2880715) B2880715
theorem B662651 : Blo 231814 662651 := bstep (se 1 (by rfl) ⟨496988, by rfl⟩ : syracuseStep 662651 = 993977) B993977
theorem B335135 : Blo 231814 335135 := bstep (se 1 (by rfl) ⟨251351, by rfl⟩ : syracuseStep 335135 = 502703) B502703
theorem B499081 : Blo 231814 499081 := bstep (se 2 (by rfl) ⟨187155, by rfl⟩ : syracuseStep 499081 = 374311) B374311
theorem B1187945 : Blo 231814 1187945 := bstep (se 2 (by rfl) ⟨445479, by rfl⟩ : syracuseStep 1187945 = 890959) B890959
theorem B5087441 : Blo 231814 5087441 := bstep (se 2 (by rfl) ⟨1907790, by rfl⟩ : syracuseStep 5087441 = 3815581) B3815581
theorem B4301009 : Blo 231814 4301009 := bstep (se 2 (by rfl) ⟨1612878, by rfl⟩ : syracuseStep 4301009 = 3225757) B3225757
theorem B794987 : Blo 231814 794987 := bstep (se 1 (by rfl) ⟨596240, by rfl⟩ : syracuseStep 794987 = 1192481) B1192481
theorem B663983 : Blo 231814 663983 := bstep (se 1 (by rfl) ⟨497987, by rfl⟩ : syracuseStep 663983 = 995975) B995975
theorem B500345 : Blo 231814 500345 := bstep (se 2 (by rfl) ⟨187629, by rfl⟩ : syracuseStep 500345 = 375259) B375259
theorem B795257 : Blo 231814 795257 := bstep (se 2 (by rfl) ⟨298221, by rfl⟩ : syracuseStep 795257 = 596443) B596443
theorem B631519 : Blo 231814 631519 := bstep (se 1 (by rfl) ⟨473639, by rfl⟩ : syracuseStep 631519 = 947279) B947279
theorem B893663 : Blo 231814 893663 := bstep (se 1 (by rfl) ⟨670247, by rfl⟩ : syracuseStep 893663 = 1340495) B1340495
theorem B4301585 : Blo 231814 4301585 := bstep (se 2 (by rfl) ⟨1613094, by rfl⟩ : syracuseStep 4301585 = 3226189) B3226189
theorem B533647 : Blo 231814 533647 := bstep (se 1 (by rfl) ⟨400235, by rfl⟩ : syracuseStep 533647 = 800471) B800471
theorem B1189079 : Blo 231814 1189079 := bstep (se 1 (by rfl) ⟨891809, by rfl⟩ : syracuseStep 1189079 = 1783619) B1783619
theorem B894347 : Blo 231814 894347 := bstep (se 1 (by rfl) ⟨670760, by rfl⟩ : syracuseStep 894347 = 1341521) B1341521
theorem B1320583 : Blo 231814 1320583 := bstep (se 1 (by rfl) ⟨990437, by rfl⟩ : syracuseStep 1320583 = 1980875) B1980875
theorem B1124279 : Blo 231814 1124279 := bstep (se 1 (by rfl) ⟨843209, by rfl⟩ : syracuseStep 1124279 = 1686419) B1686419
theorem B1485863 : Blo 231814 1485863 := bstep (se 1 (by rfl) ⟨1114397, by rfl⟩ : syracuseStep 1485863 = 2228795) B2228795
theorem B502823 : Blo 231814 502823 := bstep (se 1 (by rfl) ⟨377117, by rfl⟩ : syracuseStep 502823 = 754235) B754235
theorem B503003 : Blo 231814 503003 := bstep (se 1 (by rfl) ⟨377252, by rfl⟩ : syracuseStep 503003 = 754505) B754505
theorem B634105 : Blo 231814 634105 := bstep (se 2 (by rfl) ⟨237789, by rfl⟩ : syracuseStep 634105 = 475579) B475579
theorem B306599 : Blo 231814 306599 := bstep (se 1 (by rfl) ⟨229949, by rfl⟩ : syracuseStep 306599 = 459899) B459899
theorem B1125971 : Blo 231814 1125971 := bstep (se 1 (by rfl) ⟨844478, by rfl⟩ : syracuseStep 1125971 = 1688957) B1688957
theorem B634463 : Blo 231814 634463 := bstep (se 1 (by rfl) ⟨475847, by rfl⟩ : syracuseStep 634463 = 951695) B951695
theorem B634679 : Blo 231814 634679 := bstep (se 1 (by rfl) ⟨476009, by rfl⟩ : syracuseStep 634679 = 952019) B952019
theorem B667673 : Blo 231814 667673 := bstep (se 2 (by rfl) ⟨250377, by rfl⟩ : syracuseStep 667673 = 500755) B500755
theorem B1191995 : Blo 231814 1191995 := bstep (se 1 (by rfl) ⟨893996, by rfl⟩ : syracuseStep 1191995 = 1787993) B1787993
theorem B471305 : Blo 231814 471305 := bstep (se 2 (by rfl) ⟨176739, by rfl⟩ : syracuseStep 471305 = 353479) B353479
theorem B537151 : Blo 231814 537151 := bstep (se 1 (by rfl) ⟨402863, by rfl⟩ : syracuseStep 537151 = 805727) B805727
theorem B1421945 : Blo 231814 1421945 := bstep (se 2 (by rfl) ⟨533229, by rfl⟩ : syracuseStep 1421945 = 1066459) B1066459
theorem B537263 : Blo 231814 537263 := bstep (se 1 (by rfl) ⟨402947, by rfl⟩ : syracuseStep 537263 = 805895) B805895
theorem B2143055 : Blo 231814 2143055 := bstep (se 1 (by rfl) ⟨1607291, by rfl⟩ : syracuseStep 2143055 = 3214583) B3214583
theorem B5944265 : Blo 231814 5944265 := bstep (se 2 (by rfl) ⟨2229099, by rfl⟩ : syracuseStep 5944265 = 4458199) B4458199
theorem B635867 : Blo 231814 635867 := bstep (se 1 (by rfl) ⟨476900, by rfl⟩ : syracuseStep 635867 = 953801) B953801
theorem B1192967 : Blo 231814 1192967 := bstep (se 1 (by rfl) ⟨894725, by rfl⟩ : syracuseStep 1192967 = 1789451) B1789451
theorem B2602063 : Blo 231814 2602063 := bstep (se 1 (by rfl) ⟨1951547, by rfl⟩ : syracuseStep 2602063 = 3903095) B3903095
theorem B1193453 : Blo 231814 1193453 := bstep (se 3 (by rfl) ⟨223772, by rfl⟩ : syracuseStep 1193453 = 447545) B447545
theorem B1127969 : Blo 231814 1127969 := bstep (se 2 (by rfl) ⟨422988, by rfl⟩ : syracuseStep 1127969 = 845977) B845977
theorem B571115 : Blo 231814 571115 := bstep (se 1 (by rfl) ⟨428336, by rfl⟩ : syracuseStep 571115 = 856673) B856673
theorem B997409 : Blo 231814 997409 := bstep (se 2 (by rfl) ⟨374028, by rfl⟩ : syracuseStep 997409 = 748057) B748057
theorem B1128583 : Blo 231814 1128583 := bstep (se 1 (by rfl) ⟨846437, by rfl⟩ : syracuseStep 1128583 = 1692875) B1692875
theorem B375131 : Blo 231814 375131 := bstep (se 1 (by rfl) ⟨281348, by rfl⟩ : syracuseStep 375131 = 562697) B562697
theorem B440939 : Blo 231814 440939 := bstep (se 1 (by rfl) ⟨330704, by rfl⟩ : syracuseStep 440939 = 661409) B661409
theorem B9616157 : Blo 231814 9616157 := bstep (se 3 (by rfl) ⟨1803029, by rfl⟩ : syracuseStep 9616157 = 3606059) B3606059
theorem B670589 : Blo 231814 670589 := bstep (se 3 (by rfl) ⟨125735, by rfl⟩ : syracuseStep 670589 = 251471) B251471
theorem B2669597 : Blo 231814 2669597 := bstep (se 3 (by rfl) ⟨500549, by rfl⟩ : syracuseStep 2669597 = 1001099) B1001099
theorem B3980339 : Blo 231814 3980339 := bstep (se 1 (by rfl) ⟨2985254, by rfl⟩ : syracuseStep 3980339 = 5970509) B5970509
theorem B2866747 : Blo 231814 2866747 := bstep (se 1 (by rfl) ⟨2150060, by rfl⟩ : syracuseStep 2866747 = 4300121) B4300121
theorem B1261291 : Blo 231814 1261291 := bstep (se 1 (by rfl) ⟨945968, by rfl⟩ : syracuseStep 1261291 = 1891937) B1891937
theorem B343855 : Blo 231814 343855 := bstep (se 1 (by rfl) ⟨257891, by rfl⟩ : syracuseStep 343855 = 515783) B515783
theorem B442169 : Blo 231814 442169 := bstep (se 2 (by rfl) ⟨165813, by rfl⟩ : syracuseStep 442169 = 331627) B331627
theorem B1982515 : Blo 231814 1982515 := bstep (se 1 (by rfl) ⟨1486886, by rfl⟩ : syracuseStep 1982515 = 2973773) B2973773
theorem B1065473 : Blo 231814 1065473 := bstep (se 2 (by rfl) ⟨399552, by rfl⟩ : syracuseStep 1065473 = 799105) B799105
theorem B1426369 : Blo 231814 1426369 := bstep (se 2 (by rfl) ⟨534888, by rfl⟩ : syracuseStep 1426369 = 1069777) B1069777
theorem B1262567 : Blo 231814 1262567 := bstep (se 1 (by rfl) ⟨946925, by rfl⟩ : syracuseStep 1262567 = 1893851) B1893851
theorem B1885187 : Blo 231814 1885187 := bstep (se 1 (by rfl) ⟨1413890, by rfl⟩ : syracuseStep 1885187 = 2827781) B2827781
theorem B705779 : Blo 231814 705779 := bstep (se 1 (by rfl) ⟨529334, by rfl⟩ : syracuseStep 705779 = 1058669) B1058669
theorem B705887 : Blo 231814 705887 := bstep (se 1 (by rfl) ⟨529415, by rfl⟩ : syracuseStep 705887 = 1058831) B1058831
theorem B1591589 : Blo 231814 1591589 := bstep (se 4 (by rfl) ⟨149211, by rfl⟩ : syracuseStep 1591589 = 298423) B298423
theorem B1002091 : Blo 231814 1002091 := bstep (se 1 (by rfl) ⟨751568, by rfl⟩ : syracuseStep 1002091 = 1503137) B1503137
theorem B1002365 : Blo 231814 1002365 := bstep (se 3 (by rfl) ⟨187943, by rfl⟩ : syracuseStep 1002365 = 375887) B375887
theorem B838943 : Blo 231814 838943 := bstep (se 1 (by rfl) ⟨629207, by rfl⟩ : syracuseStep 838943 = 1258415) B1258415
theorem B1429001 : Blo 231814 1429001 := bstep (se 2 (by rfl) ⟨535875, by rfl⟩ : syracuseStep 1429001 = 1071751) B1071751
theorem B3821347 : Blo 231814 3821347 := bstep (se 1 (by rfl) ⟨2866010, by rfl⟩ : syracuseStep 3821347 = 5732021) B5732021
theorem B347945 : Blo 231814 347945 := bstep (se 2 (by rfl) ⟨130479, by rfl⟩ : syracuseStep 347945 = 260959) B260959
theorem B347951 : Blo 231814 347951 := bstep (se 1 (by rfl) ⟨260963, by rfl⟩ : syracuseStep 347951 = 521927) B521927
theorem B2510813 : Blo 231814 2510813 := bstep (se 3 (by rfl) ⟨470777, by rfl⟩ : syracuseStep 2510813 = 941555) B941555
theorem B348425 : Blo 231814 348425 := bstep (se 2 (by rfl) ⟨130659, by rfl⟩ : syracuseStep 348425 = 261319) B261319
theorem B1986889 : Blo 231814 1986889 := bstep (se 2 (by rfl) ⟨745083, by rfl⟩ : syracuseStep 1986889 = 1490167) B1490167
theorem B348527 : Blo 231814 348527 := bstep (se 1 (by rfl) ⟨261395, by rfl⟩ : syracuseStep 348527 = 522791) B522791
theorem B315847 : Blo 231814 315847 := bstep (se 1 (by rfl) ⟨236885, by rfl⟩ : syracuseStep 315847 = 473771) B473771
theorem B348743 : Blo 231814 348743 := bstep (se 1 (by rfl) ⟨261557, by rfl⟩ : syracuseStep 348743 = 523115) B523115
theorem B250463 : Blo 231814 250463 := bstep (se 1 (by rfl) ⟨187847, by rfl⟩ : syracuseStep 250463 = 375695) B375695
theorem B348779 : Blo 231814 348779 := bstep (se 1 (by rfl) ⟨261584, by rfl⟩ : syracuseStep 348779 = 523169) B523169
theorem B349007 : Blo 231814 349007 := bstep (se 1 (by rfl) ⟨261755, by rfl⟩ : syracuseStep 349007 = 523511) B523511
theorem B349403 : Blo 231814 349403 := bstep (se 1 (by rfl) ⟨262052, by rfl⟩ : syracuseStep 349403 = 524105) B524105
theorem B349577 : Blo 231814 349577 := bstep (se 2 (by rfl) ⟨131091, by rfl⟩ : syracuseStep 349577 = 262183) B262183
theorem B1332773 : Blo 231814 1332773 := bstep (se 4 (by rfl) ⟨124947, by rfl⟩ : syracuseStep 1332773 = 249895) B249895
theorem B349931 : Blo 231814 349931 := bstep (se 1 (by rfl) ⟨262448, by rfl⟩ : syracuseStep 349931 = 524897) B524897
theorem B350159 : Blo 231814 350159 := bstep (se 1 (by rfl) ⟨262619, by rfl⟩ : syracuseStep 350159 = 525239) B525239
theorem B4512023 : Blo 231814 4512023 := bstep (se 1 (by rfl) ⟨3384017, by rfl⟩ : syracuseStep 4512023 = 6768035) B6768035
theorem B350555 : Blo 231814 350555 := bstep (se 1 (by rfl) ⟨262916, by rfl⟩ : syracuseStep 350555 = 525833) B525833
theorem B1497527 : Blo 231814 1497527 := bstep (se 1 (by rfl) ⟨1123145, by rfl⟩ : syracuseStep 1497527 = 2246291) B2246291
theorem B350783 : Blo 231814 350783 := bstep (se 1 (by rfl) ⟨263087, by rfl⟩ : syracuseStep 350783 = 526175) B526175
theorem B350903 : Blo 231814 350903 := bstep (se 1 (by rfl) ⟨263177, by rfl⟩ : syracuseStep 350903 = 526355) B526355
theorem B351131 : Blo 231814 351131 := bstep (se 1 (by rfl) ⟨263348, by rfl⟩ : syracuseStep 351131 = 526697) B526697
theorem B351527 : Blo 231814 351527 := bstep (se 1 (by rfl) ⟨263645, by rfl⟩ : syracuseStep 351527 = 527291) B527291
theorem B351611 : Blo 231814 351611 := bstep (se 1 (by rfl) ⟨263708, by rfl⟩ : syracuseStep 351611 = 527417) B527417
theorem B351737 : Blo 231814 351737 := bstep (se 2 (by rfl) ⟨131901, by rfl⟩ : syracuseStep 351737 = 263803) B263803
theorem B3989087 : Blo 231814 3989087 := bstep (se 1 (by rfl) ⟨2991815, by rfl⟩ : syracuseStep 3989087 = 5983631) B5983631
theorem B351839 : Blo 231814 351839 := bstep (se 1 (by rfl) ⟨263879, by rfl⟩ : syracuseStep 351839 = 527759) B527759
theorem B450235 : Blo 231814 450235 := bstep (se 1 (by rfl) ⟨337676, by rfl⟩ : syracuseStep 450235 = 675353) B675353
theorem B352055 : Blo 231814 352055 := bstep (se 1 (by rfl) ⟨264041, by rfl⟩ : syracuseStep 352055 = 528083) B528083
theorem B352361 : Blo 231814 352361 := bstep (se 2 (by rfl) ⟨132135, by rfl⟩ : syracuseStep 352361 = 264271) B264271
theorem B4645181 : Blo 231814 4645181 := bstep (se 3 (by rfl) ⟨870971, by rfl⟩ : syracuseStep 4645181 = 1741943) B1741943
theorem B418159 : Blo 231814 418159 := bstep (se 1 (by rfl) ⟨313619, by rfl⟩ : syracuseStep 418159 = 627239) B627239
theorem B352679 : Blo 231814 352679 := bstep (se 1 (by rfl) ⟨264509, by rfl⟩ : syracuseStep 352679 = 529019) B529019
theorem B352763 : Blo 231814 352763 := bstep (se 1 (by rfl) ⟨264572, by rfl⟩ : syracuseStep 352763 = 529145) B529145
theorem B418375 : Blo 231814 418375 := bstep (se 1 (by rfl) ⟨313781, by rfl⟩ : syracuseStep 418375 = 627563) B627563
theorem B352889 : Blo 231814 352889 := bstep (se 2 (by rfl) ⟨132333, by rfl⟩ : syracuseStep 352889 = 264667) B264667
theorem B352943 : Blo 231814 352943 := bstep (se 1 (by rfl) ⟨264707, by rfl⟩ : syracuseStep 352943 = 529415) B529415
theorem B352991 : Blo 231814 352991 := bstep (se 1 (by rfl) ⟨264743, by rfl⟩ : syracuseStep 352991 = 529487) B529487
theorem B9659357 : Blo 231814 9659357 := bstep (se 3 (by rfl) ⟨1811129, by rfl⟩ : syracuseStep 9659357 = 3622259) B3622259
theorem B353255 : Blo 231814 353255 := bstep (se 1 (by rfl) ⟨264941, by rfl⟩ : syracuseStep 353255 = 529883) B529883
theorem B3204197 : Blo 231814 3204197 := bstep (se 4 (by rfl) ⟨300393, by rfl⟩ : syracuseStep 3204197 = 600787) B600787
theorem B353513 : Blo 231814 353513 := bstep (se 2 (by rfl) ⟨132567, by rfl⟩ : syracuseStep 353513 = 265135) B265135
theorem B353567 : Blo 231814 353567 := bstep (se 1 (by rfl) ⟨265175, by rfl⟩ : syracuseStep 353567 = 530351) B530351
theorem B2517169 : Blo 231814 2517169 := bstep (se 2 (by rfl) ⟨943938, by rfl⟩ : syracuseStep 2517169 = 1887877) B1887877
theorem B4516019 : Blo 231814 4516019 := bstep (se 1 (by rfl) ⟨3387014, by rfl⟩ : syracuseStep 4516019 = 6774029) B6774029
theorem B1173689 : Blo 231814 1173689 := bstep (se 2 (by rfl) ⟨440133, by rfl⟩ : syracuseStep 1173689 = 880267) B880267
theorem B2681261 : Blo 231814 2681261 := bstep (se 3 (by rfl) ⟨502736, by rfl⟩ : syracuseStep 2681261 = 1005473) B1005473
theorem B1272955 : Blo 231814 1272955 := bstep (se 1 (by rfl) ⟨954716, by rfl⟩ : syracuseStep 1272955 = 1909433) B1909433
theorem B4255163 : Blo 231814 4255163 := bstep (se 1 (by rfl) ⟨3191372, by rfl⟩ : syracuseStep 4255163 = 6382745) B6382745
theorem B1502651 : Blo 231814 1502651 := bstep (se 1 (by rfl) ⟨1126988, by rfl⟩ : syracuseStep 1502651 = 2253977) B2253977
theorem B4484807 : Blo 231814 4484807 := bstep (se 1 (by rfl) ⟨3363605, by rfl⟩ : syracuseStep 4484807 = 6727211) B6727211
theorem B880541 : Blo 231814 880541 := bstep (se 3 (by rfl) ⟨165101, by rfl⟩ : syracuseStep 880541 = 330203) B330203
theorem B1175471 : Blo 231814 1175471 := bstep (se 1 (by rfl) ⟨881603, by rfl⟩ : syracuseStep 1175471 = 1763207) B1763207
theorem B421993 : Blo 231814 421993 := bstep (se 2 (by rfl) ⟨158247, by rfl⟩ : syracuseStep 421993 = 316495) B316495
theorem B2224691 : Blo 231814 2224691 := bstep (se 1 (by rfl) ⟨1668518, by rfl⟩ : syracuseStep 2224691 = 3337037) B3337037
theorem B1504109 : Blo 231814 1504109 := bstep (se 3 (by rfl) ⟨282020, by rfl⟩ : syracuseStep 1504109 = 564041) B564041
theorem B783323 : Blo 231814 783323 := bstep (se 1 (by rfl) ⟨587492, by rfl⟩ : syracuseStep 783323 = 1174985) B1174985
theorem B783485 : Blo 231814 783485 := bstep (se 3 (by rfl) ⟨146903, by rfl⟩ : syracuseStep 783485 = 293807) B293807
theorem B783593 : Blo 231814 783593 := bstep (se 2 (by rfl) ⟨293847, by rfl⟩ : syracuseStep 783593 = 587695) B587695
theorem B1733881 : Blo 231814 1733881 := bstep (se 2 (by rfl) ⟨650205, by rfl⟩ : syracuseStep 1733881 = 1300411) B1300411
theorem B587047 : Blo 231814 587047 := bstep (se 1 (by rfl) ⟨440285, by rfl⟩ : syracuseStep 587047 = 880571) B880571
theorem B882029 : Blo 231814 882029 := bstep (se 3 (by rfl) ⟨165380, by rfl⟩ : syracuseStep 882029 = 330761) B330761
theorem B783755 : Blo 231814 783755 := bstep (se 1 (by rfl) ⟨587816, by rfl⟩ : syracuseStep 783755 = 1175633) B1175633
theorem B587321 : Blo 231814 587321 := bstep (se 2 (by rfl) ⟨220245, by rfl⟩ : syracuseStep 587321 = 440491) B440491
theorem B521963 : Blo 231814 521963 := bstep (se 1 (by rfl) ⟨391472, by rfl⟩ : syracuseStep 521963 = 782945) B782945
theorem B4519709 : Blo 231814 4519709 := bstep (se 3 (by rfl) ⟨847445, by rfl⟩ : syracuseStep 4519709 = 1694891) B1694891
theorem B358199 : Blo 231814 358199 := bstep (se 1 (by rfl) ⟨268649, by rfl⟩ : syracuseStep 358199 = 537299) B537299
theorem B522089 : Blo 231814 522089 := bstep (se 2 (by rfl) ⟨195783, by rfl⟩ : syracuseStep 522089 = 391567) B391567
theorem B4028453 : Blo 231814 4028453 := bstep (se 4 (by rfl) ⟨377667, by rfl⟩ : syracuseStep 4028453 = 755335) B755335
theorem B1144961 : Blo 231814 1144961 := bstep (se 2 (by rfl) ⟨429360, by rfl⟩ : syracuseStep 1144961 = 858721) B858721
theorem B391675 : Blo 231814 391675 := bstep (se 1 (by rfl) ⟨293756, by rfl⟩ : syracuseStep 391675 = 587513) B587513
theorem B3832343 : Blo 231814 3832343 := bstep (se 1 (by rfl) ⟨2874257, by rfl⟩ : syracuseStep 3832343 = 5748515) B5748515
theorem B293483 : Blo 231814 293483 := bstep (se 1 (by rfl) ⟨220112, by rfl⟩ : syracuseStep 293483 = 440225) B440225
theorem B522935 : Blo 231814 522935 := bstep (se 1 (by rfl) ⟨392201, by rfl⟩ : syracuseStep 522935 = 784403) B784403
theorem B1178387 : Blo 231814 1178387 := bstep (se 1 (by rfl) ⟨883790, by rfl⟩ : syracuseStep 1178387 = 1767581) B1767581
theorem B523151 : Blo 231814 523151 := bstep (se 1 (by rfl) ⟨392363, by rfl⟩ : syracuseStep 523151 = 784727) B784727
theorem B392107 : Blo 231814 392107 := bstep (se 1 (by rfl) ⟨294080, by rfl⟩ : syracuseStep 392107 = 588161) B588161
theorem B1276859 : Blo 231814 1276859 := bstep (se 1 (by rfl) ⟨957644, by rfl⟩ : syracuseStep 1276859 = 1915289) B1915289
theorem B293863 : Blo 231814 293863 := bstep (se 1 (by rfl) ⟨220397, by rfl⟩ : syracuseStep 293863 = 440795) B440795
theorem B392411 : Blo 231814 392411 := bstep (se 1 (by rfl) ⟨294308, by rfl⟩ : syracuseStep 392411 = 588617) B588617
theorem B621919 : Blo 231814 621919 := bstep (se 1 (by rfl) ⟨466439, by rfl⟩ : syracuseStep 621919 = 932879) B932879
theorem B589153 : Blo 231814 589153 := bstep (se 2 (by rfl) ⟨220932, by rfl⟩ : syracuseStep 589153 = 441865) B441865
theorem B261499 : Blo 231814 261499 := bstep (se 1 (by rfl) ⟨196124, by rfl⟩ : syracuseStep 261499 = 392249) B392249
theorem B884155 : Blo 231814 884155 := bstep (se 1 (by rfl) ⟨663116, by rfl⟩ : syracuseStep 884155 = 1326233) B1326233
theorem B392647 : Blo 231814 392647 := bstep (se 1 (by rfl) ⟨294485, by rfl⟩ : syracuseStep 392647 = 588971) B588971
theorem B1506775 : Blo 231814 1506775 := bstep (se 1 (by rfl) ⟨1130081, by rfl⟩ : syracuseStep 1506775 = 2260163) B2260163
theorem B523871 : Blo 231814 523871 := bstep (se 1 (by rfl) ⟨392903, by rfl⟩ : syracuseStep 523871 = 785807) B785807
theorem B884459 : Blo 231814 884459 := bstep (se 1 (by rfl) ⟨663344, by rfl⟩ : syracuseStep 884459 = 1326689) B1326689
theorem B524087 : Blo 231814 524087 := bstep (se 1 (by rfl) ⟨393065, by rfl⟩ : syracuseStep 524087 = 786131) B786131
theorem B261967 : Blo 231814 261967 := bstep (se 1 (by rfl) ⟨196475, by rfl⟩ : syracuseStep 261967 = 392951) B392951
theorem B1179521 : Blo 231814 1179521 := bstep (se 2 (by rfl) ⟨442320, by rfl⟩ : syracuseStep 1179521 = 884641) B884641
theorem B393167 : Blo 231814 393167 := bstep (se 1 (by rfl) ⟨294875, by rfl⟩ : syracuseStep 393167 = 589751) B589751
theorem B589963 : Blo 231814 589963 := bstep (se 1 (by rfl) ⟨442472, by rfl⟩ : syracuseStep 589963 = 884945) B884945
theorem B393403 : Blo 231814 393403 := bstep (se 1 (by rfl) ⟨295052, by rfl⟩ : syracuseStep 393403 = 590105) B590105
theorem B524519 : Blo 231814 524519 := bstep (se 1 (by rfl) ⟨393389, by rfl⟩ : syracuseStep 524519 = 786779) B786779
theorem B10944827 : Blo 231814 10944827 := bstep (se 1 (by rfl) ⟨8208620, by rfl⟩ : syracuseStep 10944827 = 16417241) B16417241
theorem B393599 : Blo 231814 393599 := bstep (se 1 (by rfl) ⟨295199, by rfl⟩ : syracuseStep 393599 = 590399) B590399
theorem B590267 : Blo 231814 590267 := bstep (se 1 (by rfl) ⟨442700, by rfl⟩ : syracuseStep 590267 = 885401) B885401
theorem B786887 : Blo 231814 786887 := bstep (se 1 (by rfl) ⟨590165, by rfl⟩ : syracuseStep 786887 = 1180331) B1180331
theorem B590287 : Blo 231814 590287 := bstep (se 1 (by rfl) ⟨442715, by rfl⟩ : syracuseStep 590287 = 885431) B885431
theorem B557545 : Blo 231814 557545 := bstep (se 2 (by rfl) ⟨209079, by rfl⟩ : syracuseStep 557545 = 418159) B418159
theorem B262759 : Blo 231814 262759 := bstep (se 1 (by rfl) ⟨197069, by rfl⟩ : syracuseStep 262759 = 394139) B394139
theorem B787211 : Blo 231814 787211 := bstep (se 1 (by rfl) ⟨590408, by rfl⟩ : syracuseStep 787211 = 1180817) B1180817
theorem B394031 : Blo 231814 394031 := bstep (se 1 (by rfl) ⟨295523, by rfl⟩ : syracuseStep 394031 = 591047) B591047
theorem B525113 : Blo 231814 525113 := bstep (se 2 (by rfl) ⟨196917, by rfl⟩ : syracuseStep 525113 = 393835) B393835
theorem B525167 : Blo 231814 525167 := bstep (se 1 (by rfl) ⟨393875, by rfl⟩ : syracuseStep 525167 = 787751) B787751
theorem B787481 : Blo 231814 787481 := bstep (se 2 (by rfl) ⟨295305, by rfl⟩ : syracuseStep 787481 = 590611) B590611
theorem B1901825 : Blo 231814 1901825 := bstep (se 2 (by rfl) ⟨713184, by rfl⟩ : syracuseStep 1901825 = 1426369) B1426369
theorem B525743 : Blo 231814 525743 := bstep (se 1 (by rfl) ⟨394307, by rfl⟩ : syracuseStep 525743 = 788615) B788615
theorem B1443439 : Blo 231814 1443439 := bstep (se 1 (by rfl) ⟨1082579, by rfl⟩ : syracuseStep 1443439 = 2165159) B2165159
theorem B788129 : Blo 231814 788129 := bstep (se 2 (by rfl) ⟨295548, by rfl⟩ : syracuseStep 788129 = 591097) B591097
theorem B591583 : Blo 231814 591583 := bstep (se 1 (by rfl) ⟨443687, by rfl⟩ : syracuseStep 591583 = 887375) B887375
theorem B395003 : Blo 231814 395003 := bstep (se 1 (by rfl) ⟨296252, by rfl⟩ : syracuseStep 395003 = 592505) B592505
theorem B591695 : Blo 231814 591695 := bstep (se 1 (by rfl) ⟨443771, by rfl⟩ : syracuseStep 591695 = 887543) B887543
theorem B395239 : Blo 231814 395239 := bstep (se 1 (by rfl) ⟨296429, by rfl⟩ : syracuseStep 395239 = 592859) B592859
theorem B559295 : Blo 231814 559295 := bstep (se 1 (by rfl) ⟨419471, by rfl⟩ : syracuseStep 559295 = 838943) B838943
theorem B395455 : Blo 231814 395455 := bstep (se 1 (by rfl) ⟨296591, by rfl⟩ : syracuseStep 395455 = 593183) B593183
theorem B526571 : Blo 231814 526571 := bstep (se 1 (by rfl) ⟨394928, by rfl⟩ : syracuseStep 526571 = 789857) B789857
theorem B1509623 : Blo 231814 1509623 := bstep (se 1 (by rfl) ⟨1132217, by rfl⟩ : syracuseStep 1509623 = 2264435) B2264435
theorem B952667 : Blo 231814 952667 := bstep (se 1 (by rfl) ⟨714500, by rfl⟩ : syracuseStep 952667 = 1429001) B1429001
theorem B788831 : Blo 231814 788831 := bstep (se 1 (by rfl) ⟨591623, by rfl⟩ : syracuseStep 788831 = 1183247) B1183247
theorem B788993 : Blo 231814 788993 := bstep (se 2 (by rfl) ⟨295872, by rfl⟩ : syracuseStep 788993 = 591745) B591745
theorem B231963 : Blo 231814 231963 := bstep (se 1 (by rfl) ⟨173972, by rfl⟩ : syracuseStep 231963 = 347945) B347945
theorem B231967 : Blo 231814 231967 := bstep (se 1 (by rfl) ⟨173975, by rfl⟩ : syracuseStep 231967 = 347951) B347951
theorem B1116703 : Blo 231814 1116703 := bstep (se 1 (by rfl) ⟨837527, by rfl⟩ : syracuseStep 1116703 = 1675055) B1675055
theorem B1673875 : Blo 231814 1673875 := bstep (se 1 (by rfl) ⟨1255406, by rfl⟩ : syracuseStep 1673875 = 2510813) B2510813
theorem B232283 : Blo 231814 232283 := bstep (se 1 (by rfl) ⟨174212, by rfl⟩ : syracuseStep 232283 = 348425) B348425
theorem B232351 : Blo 231814 232351 := bstep (se 1 (by rfl) ⟨174263, by rfl⟩ : syracuseStep 232351 = 348527) B348527
theorem B396191 : Blo 231814 396191 := bstep (se 1 (by rfl) ⟨297143, by rfl⟩ : syracuseStep 396191 = 594287) B594287
theorem B789479 : Blo 231814 789479 := bstep (se 1 (by rfl) ⟨592109, by rfl⟩ : syracuseStep 789479 = 1184219) B1184219
theorem B2231333 : Blo 231814 2231333 := bstep (se 4 (by rfl) ⟨209187, by rfl⟩ : syracuseStep 2231333 = 418375) B418375
theorem B232495 : Blo 231814 232495 := bstep (se 1 (by rfl) ⟨174371, by rfl⟩ : syracuseStep 232495 = 348743) B348743
theorem B232519 : Blo 231814 232519 := bstep (se 1 (by rfl) ⟨174389, by rfl⟩ : syracuseStep 232519 = 348779) B348779
theorem B232671 : Blo 231814 232671 := bstep (se 1 (by rfl) ⟨174503, by rfl⟩ : syracuseStep 232671 = 349007) B349007
theorem B789803 : Blo 231814 789803 := bstep (se 1 (by rfl) ⟨592352, by rfl⟩ : syracuseStep 789803 = 1184705) B1184705
theorem B396623 : Blo 231814 396623 := bstep (se 1 (by rfl) ⟨297467, by rfl⟩ : syracuseStep 396623 = 594935) B594935
theorem B232935 : Blo 231814 232935 := bstep (se 1 (by rfl) ⟨174701, by rfl⟩ : syracuseStep 232935 = 349403) B349403
theorem B527867 : Blo 231814 527867 := bstep (se 1 (by rfl) ⟨395900, by rfl⟩ : syracuseStep 527867 = 791801) B791801
theorem B790073 : Blo 231814 790073 := bstep (se 2 (by rfl) ⟨296277, by rfl⟩ : syracuseStep 790073 = 592555) B592555
theorem B233051 : Blo 231814 233051 := bstep (se 1 (by rfl) ⟨174788, by rfl⟩ : syracuseStep 233051 = 349577) B349577
theorem B528047 : Blo 231814 528047 := bstep (se 1 (by rfl) ⟨396035, by rfl⟩ : syracuseStep 528047 = 792071) B792071
theorem B888515 : Blo 231814 888515 := bstep (se 1 (by rfl) ⟨666386, by rfl⟩ : syracuseStep 888515 = 1332773) B1332773
theorem B233287 : Blo 231814 233287 := bstep (se 1 (by rfl) ⟨174965, by rfl⟩ : syracuseStep 233287 = 349931) B349931
theorem B233439 : Blo 231814 233439 := bstep (se 1 (by rfl) ⟨175079, by rfl⟩ : syracuseStep 233439 = 350159) B350159
theorem B233703 : Blo 231814 233703 := bstep (se 1 (by rfl) ⟨175277, by rfl⟩ : syracuseStep 233703 = 350555) B350555
theorem B528695 : Blo 231814 528695 := bstep (se 1 (by rfl) ⟨396521, by rfl⟩ : syracuseStep 528695 = 793043) B793043
theorem B233855 : Blo 231814 233855 := bstep (se 1 (by rfl) ⟨175391, by rfl⟩ : syracuseStep 233855 = 350783) B350783
theorem B528767 : Blo 231814 528767 := bstep (se 1 (by rfl) ⟨396575, by rfl⟩ : syracuseStep 528767 = 793151) B793151
theorem B233935 : Blo 231814 233935 := bstep (se 1 (by rfl) ⟨175451, by rfl⟩ : syracuseStep 233935 = 350903) B350903
theorem B2232791 : Blo 231814 2232791 := bstep (se 1 (by rfl) ⟨1674593, by rfl⟩ : syracuseStep 2232791 = 3349187) B3349187
theorem B397801 : Blo 231814 397801 := bstep (se 2 (by rfl) ⟨149175, by rfl⟩ : syracuseStep 397801 = 298351) B298351
theorem B397919 : Blo 231814 397919 := bstep (se 1 (by rfl) ⟨298439, by rfl⟩ : syracuseStep 397919 = 596879) B596879
theorem B234087 : Blo 231814 234087 := bstep (se 1 (by rfl) ⟨175565, by rfl⟩ : syracuseStep 234087 = 351131) B351131
theorem B234351 : Blo 231814 234351 := bstep (se 1 (by rfl) ⟨175763, by rfl⟩ : syracuseStep 234351 = 351527) B351527
theorem B234407 : Blo 231814 234407 := bstep (se 1 (by rfl) ⟨175805, by rfl⟩ : syracuseStep 234407 = 351611) B351611
theorem B234491 : Blo 231814 234491 := bstep (se 1 (by rfl) ⟨175868, by rfl⟩ : syracuseStep 234491 = 351737) B351737
theorem B2659391 : Blo 231814 2659391 := bstep (se 1 (by rfl) ⟨1994543, by rfl⟩ : syracuseStep 2659391 = 3989087) B3989087
theorem B234559 : Blo 231814 234559 := bstep (se 1 (by rfl) ⟨175919, by rfl⟩ : syracuseStep 234559 = 351839) B351839
theorem B234703 : Blo 231814 234703 := bstep (se 1 (by rfl) ⟨176027, by rfl⟩ : syracuseStep 234703 = 352055) B352055
theorem B791963 : Blo 231814 791963 := bstep (se 1 (by rfl) ⟨593972, by rfl⟩ : syracuseStep 791963 = 1187945) B1187945
theorem B234907 : Blo 231814 234907 := bstep (se 1 (by rfl) ⟨176180, by rfl⟩ : syracuseStep 234907 = 352361) B352361
theorem B529991 : Blo 231814 529991 := bstep (se 1 (by rfl) ⟨397493, by rfl⟩ : syracuseStep 529991 = 794987) B794987
theorem B235119 : Blo 231814 235119 := bstep (se 1 (by rfl) ⟨176339, by rfl⟩ : syracuseStep 235119 = 352679) B352679
theorem B235175 : Blo 231814 235175 := bstep (se 1 (by rfl) ⟨176381, by rfl⟩ : syracuseStep 235175 = 352763) B352763
theorem B333563 : Blo 231814 333563 := bstep (se 1 (by rfl) ⟨250172, by rfl⟩ : syracuseStep 333563 = 500345) B500345
theorem B235259 : Blo 231814 235259 := bstep (se 1 (by rfl) ⟨176444, by rfl⟩ : syracuseStep 235259 = 352889) B352889
theorem B530171 : Blo 231814 530171 := bstep (se 1 (by rfl) ⟨397628, by rfl⟩ : syracuseStep 530171 = 795257) B795257
theorem B235295 : Blo 231814 235295 := bstep (se 1 (by rfl) ⟨176471, by rfl⟩ : syracuseStep 235295 = 352943) B352943
theorem B235327 : Blo 231814 235327 := bstep (se 1 (by rfl) ⟨176495, by rfl⟩ : syracuseStep 235327 = 352991) B352991
theorem B595775 : Blo 231814 595775 := bstep (se 1 (by rfl) ⟨446831, by rfl⟩ : syracuseStep 595775 = 893663) B893663
theorem B661385 : Blo 231814 661385 := bstep (se 2 (by rfl) ⟨248019, by rfl⟩ : syracuseStep 661385 = 496039) B496039
theorem B235503 : Blo 231814 235503 := bstep (se 1 (by rfl) ⟨176627, by rfl⟩ : syracuseStep 235503 = 353255) B353255
theorem B2136131 : Blo 231814 2136131 := bstep (se 1 (by rfl) ⟨1602098, by rfl⟩ : syracuseStep 2136131 = 3204197) B3204197
theorem B792719 : Blo 231814 792719 := bstep (se 1 (by rfl) ⟨594539, by rfl⟩ : syracuseStep 792719 = 1189079) B1189079
theorem B235675 : Blo 231814 235675 := bstep (se 1 (by rfl) ⟨176756, by rfl⟩ : syracuseStep 235675 = 353513) B353513
theorem B235711 : Blo 231814 235711 := bstep (se 1 (by rfl) ⟨176783, by rfl⟩ : syracuseStep 235711 = 353567) B353567
theorem B596231 : Blo 231814 596231 := bstep (se 1 (by rfl) ⟨447173, by rfl⟩ : syracuseStep 596231 = 894347) B894347
theorem B530729 : Blo 231814 530729 := bstep (se 2 (by rfl) ⟨199023, by rfl⟩ : syracuseStep 530729 = 398047) B398047
theorem B662377 : Blo 231814 662377 := bstep (se 2 (by rfl) ⟨248391, by rfl⟩ : syracuseStep 662377 = 496783) B496783
theorem B793853 : Blo 231814 793853 := bstep (se 3 (by rfl) ⟨148847, by rfl⟩ : syracuseStep 793853 = 297695) B297695
theorem B990575 : Blo 231814 990575 := bstep (se 1 (by rfl) ⟨742931, by rfl⟩ : syracuseStep 990575 = 1485863) B1485863
theorem B335215 : Blo 231814 335215 := bstep (se 1 (by rfl) ⟨251411, by rfl⟩ : syracuseStep 335215 = 502823) B502823
theorem B335335 : Blo 231814 335335 := bstep (se 1 (by rfl) ⟨251501, by rfl⟩ : syracuseStep 335335 = 503003) B503003
theorem B2989871 : Blo 231814 2989871 := bstep (se 1 (by rfl) ⟨2242403, by rfl⟩ : syracuseStep 2989871 = 4484807) B4484807
theorem B794663 : Blo 231814 794663 := bstep (se 1 (by rfl) ⟨595997, by rfl⟩ : syracuseStep 794663 = 1191995) B1191995
theorem B1483127 : Blo 231814 1483127 := bstep (se 1 (by rfl) ⟨1112345, by rfl⟩ : syracuseStep 1483127 = 2224691) B2224691
theorem B795311 : Blo 231814 795311 := bstep (se 1 (by rfl) ⟨596483, by rfl⟩ : syracuseStep 795311 = 1192967) B1192967
theorem B893693 : Blo 231814 893693 := bstep (se 3 (by rfl) ⟨167567, by rfl⟩ : syracuseStep 893693 = 335135) B335135
theorem B795635 : Blo 231814 795635 := bstep (se 1 (by rfl) ⟨596726, by rfl⟩ : syracuseStep 795635 = 1193453) B1193453
theorem B238799 : Blo 231814 238799 := bstep (se 1 (by rfl) ⟨179099, by rfl⟩ : syracuseStep 238799 = 358199) B358199
theorem B664939 : Blo 231814 664939 := bstep (se 1 (by rfl) ⟨498704, by rfl⟩ : syracuseStep 664939 = 997409) B997409
theorem B763307 : Blo 231814 763307 := bstep (se 1 (by rfl) ⟨572480, by rfl⟩ : syracuseStep 763307 = 1144961) B1144961
theorem B829225 : Blo 231814 829225 := bstep (se 2 (by rfl) ⟨310959, by rfl⟩ : syracuseStep 829225 = 621919) B621919
theorem B665441 : Blo 231814 665441 := bstep (se 2 (by rfl) ⟨249540, by rfl⟩ : syracuseStep 665441 = 499081) B499081
theorem B2009033 : Blo 231814 2009033 := bstep (se 2 (by rfl) ⟨753387, by rfl⟩ : syracuseStep 2009033 = 1506775) B1506775
theorem B1779731 : Blo 231814 1779731 := bstep (se 1 (by rfl) ⟨1334798, by rfl⟩ : syracuseStep 1779731 = 2669597) B2669597
theorem B600313 : Blo 231814 600313 := bstep (se 2 (by rfl) ⟨225117, by rfl⟩ : syracuseStep 600313 = 450235) B450235
theorem B1681721 : Blo 231814 1681721 := bstep (se 2 (by rfl) ⟨630645, by rfl⟩ : syracuseStep 1681721 = 1261291) B1261291
theorem B1256791 : Blo 231814 1256791 := bstep (se 1 (by rfl) ⟨942593, by rfl⟩ : syracuseStep 1256791 = 1885187) B1885187
theorem B470519 : Blo 231814 470519 := bstep (se 1 (by rfl) ⟨352889, by rfl⟩ : syracuseStep 470519 = 705779) B705779
theorem B470591 : Blo 231814 470591 := bstep (se 1 (by rfl) ⟨352943, by rfl⟩ : syracuseStep 470591 = 705887) B705887
theorem B1061059 : Blo 231814 1061059 := bstep (se 1 (by rfl) ⟨795794, by rfl⟩ : syracuseStep 1061059 = 1591589) B1591589
theorem B667901 : Blo 231814 667901 := bstep (se 3 (by rfl) ⟨125231, by rfl⟩ : syracuseStep 667901 = 250463) B250463
theorem B668243 : Blo 231814 668243 := bstep (se 1 (by rfl) ⟨501182, by rfl⟩ : syracuseStep 668243 = 1002365) B1002365
theorem B5714813 : Blo 231814 5714813 := bstep (se 3 (by rfl) ⟨1071527, by rfl⟩ : syracuseStep 5714813 = 2143055) B2143055
theorem B3060605 : Blo 231814 3060605 := bstep (se 3 (by rfl) ⟨573863, by rfl⟩ : syracuseStep 3060605 = 1147727) B1147727
theorem B4010957 : Blo 231814 4010957 := bstep (se 3 (by rfl) ⟨752054, by rfl⟩ : syracuseStep 4010957 = 1504109) B1504109
theorem B1815527 : Blo 231814 1815527 := bstep (se 1 (by rfl) ⟨1361645, by rfl⟩ : syracuseStep 1815527 = 2723291) B2723291
theorem B3356225 : Blo 231814 3356225 := bstep (se 2 (by rfl) ⟨1258584, by rfl⟩ : syracuseStep 3356225 = 2517169) B2517169
theorem B2012759 : Blo 231814 2012759 := bstep (se 1 (by rfl) ⟨1509569, by rfl⟩ : syracuseStep 2012759 = 3019139) B3019139
theorem B1324957 : Blo 231814 1324957 := bstep (se 3 (by rfl) ⟨248429, by rfl⟩ : syracuseStep 1324957 = 496859) B496859
theorem B7649579 : Blo 231814 7649579 := bstep (se 1 (by rfl) ⟨5737184, by rfl⟩ : syracuseStep 7649579 = 11474369) B11474369
theorem B998351 : Blo 231814 998351 := bstep (se 1 (by rfl) ⟨748763, by rfl⟩ : syracuseStep 998351 = 1497527) B1497527
theorem B441767 : Blo 231814 441767 := bstep (se 1 (by rfl) ⟨331325, by rfl⟩ : syracuseStep 441767 = 662651) B662651
theorem B3391627 : Blo 231814 3391627 := bstep (se 1 (by rfl) ⟨2543720, by rfl⟩ : syracuseStep 3391627 = 5087441) B5087441
theorem B2867339 : Blo 231814 2867339 := bstep (se 1 (by rfl) ⟨2150504, by rfl⟩ : syracuseStep 2867339 = 4301009) B4301009
theorem B3096787 : Blo 231814 3096787 := bstep (se 1 (by rfl) ⟨2322590, by rfl⟩ : syracuseStep 3096787 = 4645181) B4645181
theorem B442655 : Blo 231814 442655 := bstep (se 1 (by rfl) ⟨331991, by rfl⟩ : syracuseStep 442655 = 663983) B663983
theorem B13877669 : Blo 231814 13877669 := bstep (se 4 (by rfl) ⟨1301031, by rfl⟩ : syracuseStep 13877669 = 2602063) B2602063
theorem B2867723 : Blo 231814 2867723 := bstep (se 1 (by rfl) ⟨2150792, by rfl⟩ : syracuseStep 2867723 = 4301585) B4301585
theorem B6439571 : Blo 231814 6439571 := bstep (se 1 (by rfl) ⟨4829678, by rfl⟩ : syracuseStep 6439571 = 9659357) B9659357
theorem B1000349 : Blo 231814 1000349 := bstep (se 3 (by rfl) ⟨187565, by rfl⟩ : syracuseStep 1000349 = 375131) B375131
theorem B1787507 : Blo 231814 1787507 := bstep (se 1 (by rfl) ⟨1340630, by rfl⟩ : syracuseStep 1787507 = 2681261) B2681261
theorem B2311841 : Blo 231814 2311841 := bstep (se 2 (by rfl) ⟨866940, by rfl⟩ : syracuseStep 2311841 = 1733881) B1733881
theorem B2672513 : Blo 231814 2672513 := bstep (se 2 (by rfl) ⟨1002192, by rfl⟩ : syracuseStep 2672513 = 2004385) B2004385
theorem B2836775 : Blo 231814 2836775 := bstep (se 1 (by rfl) ⟨2127581, by rfl⟩ : syracuseStep 2836775 = 4255163) B4255163
theorem B1001767 : Blo 231814 1001767 := bstep (se 1 (by rfl) ⟨751325, by rfl⟩ : syracuseStep 1001767 = 1502651) B1502651
theorem B10242541 : Blo 231814 10242541 := bstep (se 3 (by rfl) ⟨1920476, by rfl⟩ : syracuseStep 10242541 = 3840953) B3840953
theorem B445115 : Blo 231814 445115 := bstep (se 1 (by rfl) ⟨333836, by rfl⟩ : syracuseStep 445115 = 667673) B667673
theorem B314203 : Blo 231814 314203 := bstep (se 1 (by rfl) ⟨235652, by rfl⟩ : syracuseStep 314203 = 471305) B471305
theorem B708221 : Blo 231814 708221 := bstep (se 3 (by rfl) ⟨132791, by rfl⟩ : syracuseStep 708221 = 265583) B265583
theorem B347975 : Blo 231814 347975 := bstep (se 1 (by rfl) ⟨260981, by rfl⟩ : syracuseStep 347975 = 521963) B521963
theorem B380743 : Blo 231814 380743 := bstep (se 1 (by rfl) ⟨285557, by rfl⟩ : syracuseStep 380743 = 571115) B571115
theorem B348059 : Blo 231814 348059 := bstep (se 1 (by rfl) ⟨261044, by rfl⟩ : syracuseStep 348059 = 522089) B522089
theorem B348623 : Blo 231814 348623 := bstep (se 1 (by rfl) ⟨261467, by rfl⟩ : syracuseStep 348623 = 522935) B522935
theorem B348665 : Blo 231814 348665 := bstep (se 2 (by rfl) ⟨130749, by rfl⟩ : syracuseStep 348665 = 261499) B261499
theorem B6410771 : Blo 231814 6410771 := bstep (se 1 (by rfl) ⟨4808078, by rfl⟩ : syracuseStep 6410771 = 9616157) B9616157
theorem B447059 : Blo 231814 447059 := bstep (se 1 (by rfl) ⟨335294, by rfl⟩ : syracuseStep 447059 = 670589) B670589
theorem B348767 : Blo 231814 348767 := bstep (se 1 (by rfl) ⟨261575, by rfl⟩ : syracuseStep 348767 = 523151) B523151
theorem B3822329 : Blo 231814 3822329 := bstep (se 2 (by rfl) ⟨1433373, by rfl⟩ : syracuseStep 3822329 = 2866747) B2866747
theorem B24171317 : Blo 231814 24171317 := bstep (se 5 (by rfl) ⟨1133030, by rfl⟩ : syracuseStep 24171317 = 2266061) B2266061
theorem B349247 : Blo 231814 349247 := bstep (se 1 (by rfl) ⟨261935, by rfl⟩ : syracuseStep 349247 = 523871) B523871
theorem B349289 : Blo 231814 349289 := bstep (se 2 (by rfl) ⟨130983, by rfl⟩ : syracuseStep 349289 = 261967) B261967
theorem B349391 : Blo 231814 349391 := bstep (se 1 (by rfl) ⟨262043, by rfl⟩ : syracuseStep 349391 = 524087) B524087
theorem B2643353 : Blo 231814 2643353 := bstep (se 2 (by rfl) ⟨991257, by rfl⟩ : syracuseStep 2643353 = 1982515) B1982515
theorem B349595 : Blo 231814 349595 := bstep (se 1 (by rfl) ⟨262196, by rfl⟩ : syracuseStep 349595 = 524393) B524393
theorem B1594811 : Blo 231814 1594811 := bstep (se 1 (by rfl) ⟨1196108, by rfl⟩ : syracuseStep 1594811 = 2392217) B2392217
theorem B349817 : Blo 231814 349817 := bstep (se 2 (by rfl) ⟨131181, by rfl⟩ : syracuseStep 349817 = 262363) B262363
theorem B710315 : Blo 231814 710315 := bstep (se 1 (by rfl) ⟨532736, by rfl⟩ : syracuseStep 710315 = 1065473) B1065473
theorem B349919 : Blo 231814 349919 := bstep (se 1 (by rfl) ⟨262439, by rfl⟩ : syracuseStep 349919 = 524879) B524879
theorem B350015 : Blo 231814 350015 := bstep (se 1 (by rfl) ⟨262511, by rfl⟩ : syracuseStep 350015 = 525023) B525023
theorem B2250629 : Blo 231814 2250629 := bstep (se 4 (by rfl) ⟨210996, by rfl⟩ : syracuseStep 2250629 = 421993) B421993
theorem B350183 : Blo 231814 350183 := bstep (se 1 (by rfl) ⟨262637, by rfl⟩ : syracuseStep 350183 = 525275) B525275
theorem B1923047 : Blo 231814 1923047 := bstep (se 1 (by rfl) ⟨1442285, by rfl⟩ : syracuseStep 1923047 = 2884571) B2884571
theorem B841711 : Blo 231814 841711 := bstep (se 1 (by rfl) ⟨631283, by rfl⟩ : syracuseStep 841711 = 1262567) B1262567
theorem B350201 : Blo 231814 350201 := bstep (se 2 (by rfl) ⟨131325, by rfl⟩ : syracuseStep 350201 = 262651) B262651
theorem B350303 : Blo 231814 350303 := bstep (se 1 (by rfl) ⟨262727, by rfl⟩ : syracuseStep 350303 = 525455) B525455
theorem B350363 : Blo 231814 350363 := bstep (se 1 (by rfl) ⟨262772, by rfl⟩ : syracuseStep 350363 = 525545) B525545
theorem B350399 : Blo 231814 350399 := bstep (se 1 (by rfl) ⟨262799, by rfl⟩ : syracuseStep 350399 = 525599) B525599
theorem B350441 : Blo 231814 350441 := bstep (se 2 (by rfl) ⟨131415, by rfl⟩ : syracuseStep 350441 = 262831) B262831
theorem B350747 : Blo 231814 350747 := bstep (se 1 (by rfl) ⟨263060, by rfl⟩ : syracuseStep 350747 = 526121) B526121
theorem B350825 : Blo 231814 350825 := bstep (se 2 (by rfl) ⟨131559, by rfl⟩ : syracuseStep 350825 = 263119) B263119
theorem B351353 : Blo 231814 351353 := bstep (se 2 (by rfl) ⟨131757, by rfl⟩ : syracuseStep 351353 = 263515) B263515
theorem B1006739 : Blo 231814 1006739 := bstep (se 1 (by rfl) ⟨755054, by rfl⟩ : syracuseStep 1006739 = 1510109) B1510109
theorem B351455 : Blo 231814 351455 := bstep (se 1 (by rfl) ⟨263591, by rfl⟩ : syracuseStep 351455 = 527183) B527183
theorem B351497 : Blo 231814 351497 := bstep (se 2 (by rfl) ⟨131811, by rfl⟩ : syracuseStep 351497 = 263623) B263623
theorem B351599 : Blo 231814 351599 := bstep (se 1 (by rfl) ⟨263699, by rfl⟩ : syracuseStep 351599 = 527399) B527399
theorem B351719 : Blo 231814 351719 := bstep (se 1 (by rfl) ⟨263789, by rfl⟩ : syracuseStep 351719 = 527579) B527579
theorem B1760777 : Blo 231814 1760777 := bstep (se 2 (by rfl) ⟨660291, by rfl⟩ : syracuseStep 1760777 = 1320583) B1320583
theorem B351851 : Blo 231814 351851 := bstep (se 1 (by rfl) ⟨263888, by rfl⟩ : syracuseStep 351851 = 527777) B527777
theorem B351977 : Blo 231814 351977 := bstep (se 2 (by rfl) ⟨131991, by rfl⟩ : syracuseStep 351977 = 263983) B263983
theorem B2121527 : Blo 231814 2121527 := bstep (se 1 (by rfl) ⟨1591145, by rfl⟩ : syracuseStep 2121527 = 3182291) B3182291
theorem B352121 : Blo 231814 352121 := bstep (se 2 (by rfl) ⟨132045, by rfl⟩ : syracuseStep 352121 = 264091) B264091
theorem B1335163 : Blo 231814 1335163 := bstep (se 1 (by rfl) ⟨1001372, by rfl⟩ : syracuseStep 1335163 = 2002745) B2002745
theorem B352223 : Blo 231814 352223 := bstep (se 1 (by rfl) ⟨264167, by rfl⟩ : syracuseStep 352223 = 528335) B528335
theorem B4284515 : Blo 231814 4284515 := bstep (se 1 (by rfl) ⟨3213386, by rfl⟩ : syracuseStep 4284515 = 6426773) B6426773
theorem B352475 : Blo 231814 352475 := bstep (se 1 (by rfl) ⟨264356, by rfl⟩ : syracuseStep 352475 = 528713) B528713
theorem B352487 : Blo 231814 352487 := bstep (se 1 (by rfl) ⟨264365, by rfl⟩ : syracuseStep 352487 = 528731) B528731
theorem B352649 : Blo 231814 352649 := bstep (se 2 (by rfl) ⟨132243, by rfl⟩ : syracuseStep 352649 = 264487) B264487
theorem B352745 : Blo 231814 352745 := bstep (se 2 (by rfl) ⟨132279, by rfl⟩ : syracuseStep 352745 = 264559) B264559
theorem B352871 : Blo 231814 352871 := bstep (se 1 (by rfl) ⟨264653, by rfl⟩ : syracuseStep 352871 = 529307) B529307
theorem B353003 : Blo 231814 353003 := bstep (se 1 (by rfl) ⟨264752, by rfl⟩ : syracuseStep 353003 = 529505) B529505
theorem B353033 : Blo 231814 353033 := bstep (se 2 (by rfl) ⟨132387, by rfl⟩ : syracuseStep 353033 = 264775) B264775
theorem B1336121 : Blo 231814 1336121 := bstep (se 2 (by rfl) ⟨501045, by rfl⟩ : syracuseStep 1336121 = 1002091) B1002091
theorem B353135 : Blo 231814 353135 := bstep (se 1 (by rfl) ⟨264851, by rfl⟩ : syracuseStep 353135 = 529703) B529703
theorem B353387 : Blo 231814 353387 := bstep (se 1 (by rfl) ⟨265040, by rfl⟩ : syracuseStep 353387 = 530081) B530081
theorem B3368101 : Blo 231814 3368101 := bstep (se 4 (by rfl) ⟨315759, by rfl⟩ : syracuseStep 3368101 = 631519) B631519
theorem B353627 : Blo 231814 353627 := bstep (se 1 (by rfl) ⟨265220, by rfl⟩ : syracuseStep 353627 = 530441) B530441
theorem B1697273 : Blo 231814 1697273 := bstep (se 2 (by rfl) ⟨636477, by rfl⟩ : syracuseStep 1697273 = 1272955) B1272955
theorem B3008015 : Blo 231814 3008015 := bstep (se 1 (by rfl) ⟨2256011, by rfl⟩ : syracuseStep 3008015 = 4512023) B4512023
theorem B845473 : Blo 231814 845473 := bstep (se 2 (by rfl) ⟨317052, by rfl⟩ : syracuseStep 845473 = 634105) B634105
theorem B2844953 : Blo 231814 2844953 := bstep (se 2 (by rfl) ⟨1066857, by rfl⟩ : syracuseStep 2844953 = 2133715) B2133715
theorem B2649185 : Blo 231814 2649185 := bstep (se 2 (by rfl) ⟨993444, by rfl⟩ : syracuseStep 2649185 = 1986889) B1986889
theorem B421129 : Blo 231814 421129 := bstep (se 2 (by rfl) ⟨157923, by rfl⟩ : syracuseStep 421129 = 315847) B315847
theorem B2846117 : Blo 231814 2846117 := bstep (se 4 (by rfl) ⟨266823, by rfl⟩ : syracuseStep 2846117 = 533647) B533647
theorem B716201 : Blo 231814 716201 := bstep (se 2 (by rfl) ⟨268575, by rfl⟩ : syracuseStep 716201 = 537151) B537151
theorem B880253 : Blo 231814 880253 := bstep (se 3 (by rfl) ⟨165047, by rfl⟩ : syracuseStep 880253 = 330095) B330095
theorem B749519 : Blo 231814 749519 := bstep (se 1 (by rfl) ⟨562139, by rfl⟩ : syracuseStep 749519 = 1124279) B1124279
theorem B3010679 : Blo 231814 3010679 := bstep (se 1 (by rfl) ⟨2258009, by rfl⟩ : syracuseStep 3010679 = 4516019) B4516019
theorem B782459 : Blo 231814 782459 := bstep (se 1 (by rfl) ⟨586844, by rfl⟩ : syracuseStep 782459 = 1173689) B1173689
theorem B782621 : Blo 231814 782621 := bstep (se 3 (by rfl) ⟨146741, by rfl⟩ : syracuseStep 782621 = 293483) B293483
theorem B782729 : Blo 231814 782729 := bstep (se 2 (by rfl) ⟨293523, by rfl⟩ : syracuseStep 782729 = 587047) B587047
theorem B750647 : Blo 231814 750647 := bstep (se 1 (by rfl) ⟨562985, by rfl⟩ : syracuseStep 750647 = 1125971) B1125971
theorem B422975 : Blo 231814 422975 := bstep (se 1 (by rfl) ⟨317231, by rfl⟩ : syracuseStep 422975 = 634463) B634463
theorem B357481 : Blo 231814 357481 := bstep (se 2 (by rfl) ⟨134055, by rfl⟩ : syracuseStep 357481 = 268111) B268111
theorem B423119 : Blo 231814 423119 := bstep (se 1 (by rfl) ⟨317339, by rfl⟩ : syracuseStep 423119 = 634679) B634679
theorem B587027 : Blo 231814 587027 := bstep (se 1 (by rfl) ⟨440270, by rfl⟩ : syracuseStep 587027 = 880541) B880541
theorem B783647 : Blo 231814 783647 := bstep (se 1 (by rfl) ⟨587735, by rfl⟩ : syracuseStep 783647 = 1175471) B1175471
theorem B6387133 : Blo 231814 6387133 := bstep (se 3 (by rfl) ⟨1197587, by rfl⟩ : syracuseStep 6387133 = 2395175) B2395175
theorem B1504777 : Blo 231814 1504777 := bstep (se 2 (by rfl) ⟨564291, by rfl⟩ : syracuseStep 1504777 = 1128583) B1128583
theorem B947963 : Blo 231814 947963 := bstep (se 1 (by rfl) ⟨710972, by rfl⟩ : syracuseStep 947963 = 1421945) B1421945
theorem B358175 : Blo 231814 358175 := bstep (se 1 (by rfl) ⟨268631, by rfl⟩ : syracuseStep 358175 = 537263) B537263
theorem B3962843 : Blo 231814 3962843 := bstep (se 1 (by rfl) ⟨2972132, by rfl⟩ : syracuseStep 3962843 = 5944265) B5944265
theorem B522215 : Blo 231814 522215 := bstep (se 1 (by rfl) ⟨391661, by rfl⟩ : syracuseStep 522215 = 783323) B783323
theorem B423911 : Blo 231814 423911 := bstep (se 1 (by rfl) ⟨317933, by rfl⟩ : syracuseStep 423911 = 635867) B635867
theorem B522233 : Blo 231814 522233 := bstep (se 2 (by rfl) ⟨195837, by rfl⟩ : syracuseStep 522233 = 391675) B391675
theorem B522323 : Blo 231814 522323 := bstep (se 1 (by rfl) ⟨391742, by rfl⟩ : syracuseStep 522323 = 783485) B783485
theorem B522395 : Blo 231814 522395 := bstep (se 1 (by rfl) ⟨391796, by rfl⟩ : syracuseStep 522395 = 783593) B783593
theorem B588019 : Blo 231814 588019 := bstep (se 1 (by rfl) ⟨441014, by rfl⟩ : syracuseStep 588019 = 882029) B882029
theorem B522503 : Blo 231814 522503 := bstep (se 1 (by rfl) ⟨391877, by rfl⟩ : syracuseStep 522503 = 783755) B783755
theorem B751979 : Blo 231814 751979 := bstep (se 1 (by rfl) ⟨563984, by rfl⟩ : syracuseStep 751979 = 1127969) B1127969
theorem B391547 : Blo 231814 391547 := bstep (se 1 (by rfl) ⟨293660, by rfl⟩ : syracuseStep 391547 = 587321) B587321
theorem B817597 : Blo 231814 817597 := bstep (se 3 (by rfl) ⟨153299, by rfl⟩ : syracuseStep 817597 = 306599) B306599
theorem B3013139 : Blo 231814 3013139 := bstep (se 1 (by rfl) ⟨2259854, by rfl⟩ : syracuseStep 3013139 = 4519709) B4519709
theorem B522809 : Blo 231814 522809 := bstep (se 2 (by rfl) ⟨196053, by rfl⟩ : syracuseStep 522809 = 392107) B392107
theorem B1014329 : Blo 231814 1014329 := bstep (se 2 (by rfl) ⟨380373, by rfl⟩ : syracuseStep 1014329 = 760747) B760747
theorem B391817 : Blo 231814 391817 := bstep (se 2 (by rfl) ⟨146931, by rfl⟩ : syracuseStep 391817 = 293863) B293863
theorem B2685635 : Blo 231814 2685635 := bstep (se 1 (by rfl) ⟨2014226, by rfl⟩ : syracuseStep 2685635 = 4028453) B4028453
theorem B20380517 : Blo 231814 20380517 := bstep (se 4 (by rfl) ⟨1910673, by rfl⟩ : syracuseStep 20380517 = 3821347) B3821347
theorem B2554895 : Blo 231814 2554895 := bstep (se 1 (by rfl) ⟨1916171, by rfl⟩ : syracuseStep 2554895 = 3832343) B3832343
theorem B293959 : Blo 231814 293959 := bstep (se 1 (by rfl) ⟨220469, by rfl⟩ : syracuseStep 293959 = 440939) B440939
theorem B785537 : Blo 231814 785537 := bstep (se 2 (by rfl) ⟨294576, by rfl⟩ : syracuseStep 785537 = 589153) B589153
theorem B785591 : Blo 231814 785591 := bstep (se 1 (by rfl) ⟨589193, by rfl⟩ : syracuseStep 785591 = 1178387) B1178387
theorem B1178873 : Blo 231814 1178873 := bstep (se 2 (by rfl) ⟨442077, by rfl⟩ : syracuseStep 1178873 = 884155) B884155
theorem B523529 : Blo 231814 523529 := bstep (se 2 (by rfl) ⟨196323, by rfl⟩ : syracuseStep 523529 = 392647) B392647
theorem B851239 : Blo 231814 851239 := bstep (se 1 (by rfl) ⟨638429, by rfl⟩ : syracuseStep 851239 = 1276859) B1276859
theorem B2653559 : Blo 231814 2653559 := bstep (se 1 (by rfl) ⟨1990169, by rfl⟩ : syracuseStep 2653559 = 3980339) B3980339
theorem B261607 : Blo 231814 261607 := bstep (se 1 (by rfl) ⟨196205, by rfl⟩ : syracuseStep 261607 = 392411) B392411
theorem B458473 : Blo 231814 458473 := bstep (se 2 (by rfl) ⟨171927, by rfl⟩ : syracuseStep 458473 = 343855) B343855
theorem B589639 : Blo 231814 589639 := bstep (se 1 (by rfl) ⟨442229, by rfl⟩ : syracuseStep 589639 = 884459) B884459
theorem B294779 : Blo 231814 294779 := bstep (se 1 (by rfl) ⟨221084, by rfl⟩ : syracuseStep 294779 = 442169) B442169
theorem B786347 : Blo 231814 786347 := bstep (se 1 (by rfl) ⟨589760, by rfl⟩ : syracuseStep 786347 = 1179521) B1179521
theorem B262111 : Blo 231814 262111 := bstep (se 1 (by rfl) ⟨196583, by rfl⟩ : syracuseStep 262111 = 393167) B393167
theorem B786617 : Blo 231814 786617 := bstep (se 2 (by rfl) ⟨294981, by rfl⟩ : syracuseStep 786617 = 589963) B589963
theorem B4522169 : Blo 231814 4522169 := bstep (se 2 (by rfl) ⟨1695813, by rfl⟩ : syracuseStep 4522169 = 3391627) B3391627
theorem B295103 : Blo 231814 295103 := bstep (se 1 (by rfl) ⟨221327, by rfl⟩ : syracuseStep 295103 = 442655) B442655
theorem B524537 : Blo 231814 524537 := bstep (se 2 (by rfl) ⟨196701, by rfl⟩ : syracuseStep 524537 = 393403) B393403
theorem B262399 : Blo 231814 262399 := bstep (se 1 (by rfl) ⟨196799, by rfl⟩ : syracuseStep 262399 = 393599) B393599
theorem B4129049 : Blo 231814 4129049 := bstep (se 2 (by rfl) ⟨1548393, by rfl⟩ : syracuseStep 4129049 = 3096787) B3096787
theorem B393511 : Blo 231814 393511 := bstep (se 1 (by rfl) ⟨295133, by rfl⟩ : syracuseStep 393511 = 590267) B590267
theorem B524591 : Blo 231814 524591 := bstep (se 1 (by rfl) ⟨393443, by rfl⟩ : syracuseStep 524591 = 786887) B786887
theorem B4293047 : Blo 231814 4293047 := bstep (se 1 (by rfl) ⟨3219785, by rfl⟩ : syracuseStep 4293047 = 6439571) B6439571
theorem B524807 : Blo 231814 524807 := bstep (se 1 (by rfl) ⟨393605, by rfl⟩ : syracuseStep 524807 = 787211) B787211
theorem B262687 : Blo 231814 262687 := bstep (se 1 (by rfl) ⟨197015, by rfl⟩ : syracuseStep 262687 = 394031) B394031
theorem B787049 : Blo 231814 787049 := bstep (se 2 (by rfl) ⟨295143, by rfl⟩ : syracuseStep 787049 = 590287) B590287
theorem B524987 : Blo 231814 524987 := bstep (se 1 (by rfl) ⟨393740, by rfl⟩ : syracuseStep 524987 = 787481) B787481
theorem B525419 : Blo 231814 525419 := bstep (se 1 (by rfl) ⟨394064, by rfl⟩ : syracuseStep 525419 = 788129) B788129
theorem B1541227 : Blo 231814 1541227 := bstep (se 1 (by rfl) ⟨1155920, by rfl⟩ : syracuseStep 1541227 = 2311841) B2311841
theorem B263335 : Blo 231814 263335 := bstep (se 1 (by rfl) ⟨197501, by rfl⟩ : syracuseStep 263335 = 395003) B395003
theorem B394463 : Blo 231814 394463 := bstep (se 1 (by rfl) ⟨295847, by rfl⟩ : syracuseStep 394463 = 591695) B591695
theorem B4490801 : Blo 231814 4490801 := bstep (se 2 (by rfl) ⟨1684050, by rfl⟩ : syracuseStep 4490801 = 3368101) B3368101
theorem B525887 : Blo 231814 525887 := bstep (se 1 (by rfl) ⟨394415, by rfl⟩ : syracuseStep 525887 = 788831) B788831
theorem B525995 : Blo 231814 525995 := bstep (se 1 (by rfl) ⟨394496, by rfl⟩ : syracuseStep 525995 = 788993) B788993
theorem B886585 : Blo 231814 886585 := bstep (se 2 (by rfl) ⟨332469, by rfl⟩ : syracuseStep 886585 = 664939) B664939
theorem B264127 : Blo 231814 264127 := bstep (se 1 (by rfl) ⟨198095, by rfl⟩ : syracuseStep 264127 = 396191) B396191
theorem B10192877 : Blo 231814 10192877 := bstep (se 3 (by rfl) ⟨1911164, by rfl⟩ : syracuseStep 10192877 = 3822329) B3822329
theorem B526319 : Blo 231814 526319 := bstep (se 1 (by rfl) ⟨394739, by rfl⟩ : syracuseStep 526319 = 789479) B789479
theorem B526535 : Blo 231814 526535 := bstep (se 1 (by rfl) ⟨394901, by rfl⟩ : syracuseStep 526535 = 789803) B789803
theorem B264415 : Blo 231814 264415 := bstep (se 1 (by rfl) ⟨198311, by rfl⟩ : syracuseStep 264415 = 396623) B396623
theorem B788777 : Blo 231814 788777 := bstep (se 2 (by rfl) ⟨295791, by rfl⟩ : syracuseStep 788777 = 591583) B591583
theorem B4360517 : Blo 231814 4360517 := bstep (se 4 (by rfl) ⟨408798, by rfl⟩ : syracuseStep 4360517 = 817597) B817597
theorem B526715 : Blo 231814 526715 := bstep (se 1 (by rfl) ⟨395036, by rfl⟩ : syracuseStep 526715 = 790073) B790073
theorem B592343 : Blo 231814 592343 := bstep (se 1 (by rfl) ⟨444257, by rfl⟩ : syracuseStep 592343 = 888515) B888515
theorem B231983 : Blo 231814 231983 := bstep (se 1 (by rfl) ⟨173987, by rfl⟩ : syracuseStep 231983 = 347975) B347975
theorem B232039 : Blo 231814 232039 := bstep (se 1 (by rfl) ⟨174029, by rfl⟩ : syracuseStep 232039 = 348059) B348059
theorem B526985 : Blo 231814 526985 := bstep (se 2 (by rfl) ⟨197619, by rfl⟩ : syracuseStep 526985 = 395239) B395239
theorem B527273 : Blo 231814 527273 := bstep (se 2 (by rfl) ⟨197727, by rfl⟩ : syracuseStep 527273 = 395455) B395455
theorem B232415 : Blo 231814 232415 := bstep (se 1 (by rfl) ⟨174311, by rfl⟩ : syracuseStep 232415 = 348623) B348623
theorem B232443 : Blo 231814 232443 := bstep (se 1 (by rfl) ⟨174332, by rfl⟩ : syracuseStep 232443 = 348665) B348665
theorem B232511 : Blo 231814 232511 := bstep (se 1 (by rfl) ⟨174383, by rfl⟩ : syracuseStep 232511 = 348767) B348767
theorem B265279 : Blo 231814 265279 := bstep (se 1 (by rfl) ⟨198959, by rfl⟩ : syracuseStep 265279 = 397919) B397919
theorem B232831 : Blo 231814 232831 := bstep (se 1 (by rfl) ⟨174623, by rfl⟩ : syracuseStep 232831 = 349247) B349247
theorem B1772927 : Blo 231814 1772927 := bstep (se 1 (by rfl) ⟨1329695, by rfl⟩ : syracuseStep 1772927 = 2659391) B2659391
theorem B232859 : Blo 231814 232859 := bstep (se 1 (by rfl) ⟨174644, by rfl⟩ : syracuseStep 232859 = 349289) B349289
theorem B232927 : Blo 231814 232927 := bstep (se 1 (by rfl) ⟨174695, by rfl⟩ : syracuseStep 232927 = 349391) B349391
theorem B2231833 : Blo 231814 2231833 := bstep (se 2 (by rfl) ⟨836937, by rfl⟩ : syracuseStep 2231833 = 1673875) B1673875
theorem B233063 : Blo 231814 233063 := bstep (se 1 (by rfl) ⟨174797, by rfl⟩ : syracuseStep 233063 = 349595) B349595
theorem B527975 : Blo 231814 527975 := bstep (se 1 (by rfl) ⟨395981, by rfl⟩ : syracuseStep 527975 = 791963) B791963
theorem B233211 : Blo 231814 233211 := bstep (se 1 (by rfl) ⟨174908, by rfl⟩ : syracuseStep 233211 = 349817) B349817
theorem B233279 : Blo 231814 233279 := bstep (se 1 (by rfl) ⟨174959, by rfl⟩ : syracuseStep 233279 = 349919) B349919
theorem B233343 : Blo 231814 233343 := bstep (se 1 (by rfl) ⟨175007, by rfl⟩ : syracuseStep 233343 = 350015) B350015
theorem B397183 : Blo 231814 397183 := bstep (se 1 (by rfl) ⟨297887, by rfl⟩ : syracuseStep 397183 = 595775) B595775
theorem B233455 : Blo 231814 233455 := bstep (se 1 (by rfl) ⟨175091, by rfl⟩ : syracuseStep 233455 = 350183) B350183
theorem B1282031 : Blo 231814 1282031 := bstep (se 1 (by rfl) ⟨961523, by rfl⟩ : syracuseStep 1282031 = 1923047) B1923047
theorem B233467 : Blo 231814 233467 := bstep (se 1 (by rfl) ⟨175100, by rfl⟩ : syracuseStep 233467 = 350201) B350201
theorem B233535 : Blo 231814 233535 := bstep (se 1 (by rfl) ⟨175151, by rfl⟩ : syracuseStep 233535 = 350303) B350303
theorem B528479 : Blo 231814 528479 := bstep (se 1 (by rfl) ⟨396359, by rfl⟩ : syracuseStep 528479 = 792719) B792719
theorem B233575 : Blo 231814 233575 := bstep (se 1 (by rfl) ⟨175181, by rfl⟩ : syracuseStep 233575 = 350363) B350363
theorem B233599 : Blo 231814 233599 := bstep (se 1 (by rfl) ⟨175199, by rfl⟩ : syracuseStep 233599 = 350399) B350399
theorem B233627 : Blo 231814 233627 := bstep (se 1 (by rfl) ⟨175220, by rfl⟩ : syracuseStep 233627 = 350441) B350441
theorem B397487 : Blo 231814 397487 := bstep (se 1 (by rfl) ⟨298115, by rfl⟩ : syracuseStep 397487 = 596231) B596231
theorem B561505 : Blo 231814 561505 := bstep (se 2 (by rfl) ⟨210564, by rfl⟩ : syracuseStep 561505 = 421129) B421129
theorem B233831 : Blo 231814 233831 := bstep (se 1 (by rfl) ⟨175373, by rfl⟩ : syracuseStep 233831 = 350747) B350747
theorem B233883 : Blo 231814 233883 := bstep (se 1 (by rfl) ⟨175412, by rfl⟩ : syracuseStep 233883 = 350825) B350825
theorem B1675721 : Blo 231814 1675721 := bstep (se 2 (by rfl) ⟨628395, by rfl⟩ : syracuseStep 1675721 = 1256791) B1256791
theorem B889501 : Blo 231814 889501 := bstep (se 3 (by rfl) ⟨166781, by rfl⟩ : syracuseStep 889501 = 333563) B333563
theorem B234235 : Blo 231814 234235 := bstep (se 1 (by rfl) ⟨175676, by rfl⟩ : syracuseStep 234235 = 351353) B351353
theorem B234303 : Blo 231814 234303 := bstep (se 1 (by rfl) ⟨175727, by rfl⟩ : syracuseStep 234303 = 351455) B351455
theorem B529235 : Blo 231814 529235 := bstep (se 1 (by rfl) ⟨396926, by rfl⟩ : syracuseStep 529235 = 793853) B793853
theorem B234331 : Blo 231814 234331 := bstep (se 1 (by rfl) ⟨175748, by rfl⟩ : syracuseStep 234331 = 351497) B351497
theorem B660383 : Blo 231814 660383 := bstep (se 1 (by rfl) ⟨495287, by rfl⟩ : syracuseStep 660383 = 990575) B990575
theorem B234399 : Blo 231814 234399 := bstep (se 1 (by rfl) ⟨175799, by rfl⟩ : syracuseStep 234399 = 351599) B351599
theorem B234479 : Blo 231814 234479 := bstep (se 1 (by rfl) ⟨175859, by rfl⟩ : syracuseStep 234479 = 351719) B351719
theorem B234567 : Blo 231814 234567 := bstep (se 1 (by rfl) ⟨175925, by rfl⟩ : syracuseStep 234567 = 351851) B351851
theorem B234651 : Blo 231814 234651 := bstep (se 1 (by rfl) ⟨175988, by rfl⟩ : syracuseStep 234651 = 351977) B351977
theorem B1414351 : Blo 231814 1414351 := bstep (se 1 (by rfl) ⟨1060763, by rfl⟩ : syracuseStep 1414351 = 2121527) B2121527
theorem B234747 : Blo 231814 234747 := bstep (se 1 (by rfl) ⟨176060, by rfl⟩ : syracuseStep 234747 = 352121) B352121
theorem B234815 : Blo 231814 234815 := bstep (se 1 (by rfl) ⟨176111, by rfl⟩ : syracuseStep 234815 = 352223) B352223
theorem B529775 : Blo 231814 529775 := bstep (se 1 (by rfl) ⟨397331, by rfl⟩ : syracuseStep 529775 = 794663) B794663
theorem B2856343 : Blo 231814 2856343 := bstep (se 1 (by rfl) ⟨2142257, by rfl⟩ : syracuseStep 2856343 = 4284515) B4284515
theorem B234983 : Blo 231814 234983 := bstep (se 1 (by rfl) ⟨176237, by rfl⟩ : syracuseStep 234983 = 352475) B352475
theorem B234991 : Blo 231814 234991 := bstep (se 1 (by rfl) ⟨176243, by rfl⟩ : syracuseStep 234991 = 352487) B352487
theorem B988751 : Blo 231814 988751 := bstep (se 1 (by rfl) ⟨741563, by rfl⟩ : syracuseStep 988751 = 1483127) B1483127
theorem B1414745 : Blo 231814 1414745 := bstep (se 2 (by rfl) ⟨530529, by rfl⟩ : syracuseStep 1414745 = 1061059) B1061059
theorem B235099 : Blo 231814 235099 := bstep (se 1 (by rfl) ⟨176324, by rfl⟩ : syracuseStep 235099 = 352649) B352649
theorem B235163 : Blo 231814 235163 := bstep (se 1 (by rfl) ⟨176372, by rfl⟩ : syracuseStep 235163 = 352745) B352745
theorem B235247 : Blo 231814 235247 := bstep (se 1 (by rfl) ⟨176435, by rfl⟩ : syracuseStep 235247 = 352871) B352871
theorem B530207 : Blo 231814 530207 := bstep (se 1 (by rfl) ⟨397655, by rfl⟩ : syracuseStep 530207 = 795311) B795311
theorem B235335 : Blo 231814 235335 := bstep (se 1 (by rfl) ⟨176501, by rfl⟩ : syracuseStep 235335 = 353003) B353003
theorem B595795 : Blo 231814 595795 := bstep (se 1 (by rfl) ⟨446846, by rfl⟩ : syracuseStep 595795 = 893693) B893693
theorem B235355 : Blo 231814 235355 := bstep (se 1 (by rfl) ⟨176516, by rfl⟩ : syracuseStep 235355 = 353033) B353033
theorem B890747 : Blo 231814 890747 := bstep (se 1 (by rfl) ⟨668060, by rfl⟩ : syracuseStep 890747 = 1336121) B1336121
theorem B235423 : Blo 231814 235423 := bstep (se 1 (by rfl) ⟨176567, by rfl⟩ : syracuseStep 235423 = 353135) B353135
theorem B530401 : Blo 231814 530401 := bstep (se 2 (by rfl) ⟨198900, by rfl⟩ : syracuseStep 530401 = 397801) B397801
theorem B530423 : Blo 231814 530423 := bstep (se 1 (by rfl) ⟨397817, by rfl⟩ : syracuseStep 530423 = 795635) B795635
theorem B235591 : Blo 231814 235591 := bstep (se 1 (by rfl) ⟨176693, by rfl⟩ : syracuseStep 235591 = 353387) B353387
theorem B235751 : Blo 231814 235751 := bstep (se 1 (by rfl) ⟨176813, by rfl⟩ : syracuseStep 235751 = 353627) B353627
theorem B2005343 : Blo 231814 2005343 := bstep (se 1 (by rfl) ⟨1504007, by rfl⟩ : syracuseStep 2005343 = 3008015) B3008015
theorem B1186487 : Blo 231814 1186487 := bstep (se 1 (by rfl) ⟨889865, by rfl⟩ : syracuseStep 1186487 = 1779731) B1779731
theorem B1121147 : Blo 231814 1121147 := bstep (se 1 (by rfl) ⟨840860, by rfl⟩ : syracuseStep 1121147 = 1681721) B1681721
theorem B1186973 : Blo 231814 1186973 := bstep (se 3 (by rfl) ⟨222557, by rfl⟩ : syracuseStep 1186973 = 445115) B445115
theorem B2006369 : Blo 231814 2006369 := bstep (se 2 (by rfl) ⟨752388, by rfl⟩ : syracuseStep 2006369 = 1504777) B1504777
theorem B499679 : Blo 231814 499679 := bstep (se 1 (by rfl) ⟨374759, by rfl⟩ : syracuseStep 499679 = 749519) B749519
theorem B1122281 : Blo 231814 1122281 := bstep (se 2 (by rfl) ⟨420855, by rfl⟩ : syracuseStep 1122281 = 841711) B841711
theorem B2007119 : Blo 231814 2007119 := bstep (se 1 (by rfl) ⟨1505339, by rfl⟩ : syracuseStep 2007119 = 3010679) B3010679
theorem B3809875 : Blo 231814 3809875 := bstep (se 1 (by rfl) ⟨2857406, by rfl⟩ : syracuseStep 3809875 = 5714813) B5714813
theorem B2040403 : Blo 231814 2040403 := bstep (se 1 (by rfl) ⟨1530302, by rfl⟩ : syracuseStep 2040403 = 3060605) B3060605
theorem B500431 : Blo 231814 500431 := bstep (se 1 (by rfl) ⟨375323, by rfl⟩ : syracuseStep 500431 = 750647) B750647
theorem B2237483 : Blo 231814 2237483 := bstep (se 1 (by rfl) ⟨1678112, by rfl⟩ : syracuseStep 2237483 = 3356225) B3356225
theorem B631975 : Blo 231814 631975 := bstep (se 1 (by rfl) ⟨473981, by rfl⟩ : syracuseStep 631975 = 947963) B947963
theorem B238783 : Blo 231814 238783 := bstep (se 1 (by rfl) ⟨179087, by rfl⟩ : syracuseStep 238783 = 358175) B358175
theorem B501319 : Blo 231814 501319 := bstep (se 1 (by rfl) ⟨375989, by rfl⟩ : syracuseStep 501319 = 751979) B751979
theorem B2008759 : Blo 231814 2008759 := bstep (se 1 (by rfl) ⟨1506569, by rfl⟩ : syracuseStep 2008759 = 3013139) B3013139
theorem B665567 : Blo 231814 665567 := bstep (se 1 (by rfl) ⟨499175, by rfl⟩ : syracuseStep 665567 = 998351) B998351
theorem B1780217 : Blo 231814 1780217 := bstep (se 2 (by rfl) ⟨667581, by rfl⟩ : syracuseStep 1780217 = 1335163) B1335163
theorem B1911559 : Blo 231814 1911559 := bstep (se 1 (by rfl) ⟨1433669, by rfl⟩ : syracuseStep 1911559 = 2867339) B2867339
theorem B1911815 : Blo 231814 1911815 := bstep (se 1 (by rfl) ⟨1433861, by rfl⟩ : syracuseStep 1911815 = 2867723) B2867723
theorem B666899 : Blo 231814 666899 := bstep (se 1 (by rfl) ⟨500174, by rfl⟩ : syracuseStep 666899 = 1000349) B1000349
theorem B1191671 : Blo 231814 1191671 := bstep (se 1 (by rfl) ⟨893753, by rfl⟩ : syracuseStep 1191671 = 1787507) B1787507
theorem B37007117 : Blo 231814 37007117 := bstep (se 3 (by rfl) ⟨6938834, by rfl⟩ : syracuseStep 37007117 = 13877669) B13877669
theorem B1781675 : Blo 231814 1781675 := bstep (se 1 (by rfl) ⟨1336256, by rfl⟩ : syracuseStep 1781675 = 2672513) B2672513
theorem B372863 : Blo 231814 372863 := bstep (se 1 (by rfl) ⟨279647, by rfl⟩ : syracuseStep 372863 = 559295) B559295
theorem B1192157 : Blo 231814 1192157 := bstep (se 3 (by rfl) ⟨223529, by rfl⟩ : syracuseStep 1192157 = 447059) B447059
theorem B635111 : Blo 231814 635111 := bstep (se 1 (by rfl) ⟨476333, by rfl⟩ : syracuseStep 635111 = 952667) B952667
theorem B1487555 : Blo 231814 1487555 := bstep (se 1 (by rfl) ⟨1115666, by rfl⟩ : syracuseStep 1487555 = 2231333) B2231333
theorem B1127297 : Blo 231814 1127297 := bstep (se 2 (by rfl) ⟨422736, by rfl⟩ : syracuseStep 1127297 = 845473) B845473
theorem B1488527 : Blo 231814 1488527 := bstep (se 1 (by rfl) ⟨1116395, by rfl⟩ : syracuseStep 1488527 = 2232791) B2232791
theorem B800417 : Blo 231814 800417 := bstep (se 2 (by rfl) ⟨300156, by rfl⟩ : syracuseStep 800417 = 600313) B600313
theorem B4273847 : Blo 231814 4273847 := bstep (se 1 (by rfl) ⟨3205385, by rfl⟩ : syracuseStep 4273847 = 6410771) B6410771
theorem B636797 : Blo 231814 636797 := bstep (se 3 (by rfl) ⟨119399, by rfl⟩ : syracuseStep 636797 = 238799) B238799
theorem B1488937 : Blo 231814 1488937 := bstep (se 2 (by rfl) ⟨558351, by rfl⟩ : syracuseStep 1488937 = 1116703) B1116703
theorem B1063207 : Blo 231814 1063207 := bstep (se 1 (by rfl) ⟨797405, by rfl⟩ : syracuseStep 1063207 = 1594811) B1594811
theorem B473543 : Blo 231814 473543 := bstep (se 1 (by rfl) ⟨355157, by rfl⟩ : syracuseStep 473543 = 710315) B710315
theorem B1424087 : Blo 231814 1424087 := bstep (se 1 (by rfl) ⟨1068065, by rfl⟩ : syracuseStep 1424087 = 2136131) B2136131
theorem B671159 : Blo 231814 671159 := bstep (se 1 (by rfl) ⟨503369, by rfl⟩ : syracuseStep 671159 = 1006739) B1006739
theorem B1130429 : Blo 231814 1130429 := bstep (se 3 (by rfl) ⟨211955, by rfl⟩ : syracuseStep 1130429 = 423911) B423911
theorem B508871 : Blo 231814 508871 := bstep (se 1 (by rfl) ⟨381653, by rfl⟩ : syracuseStep 508871 = 763307) B763307
theorem B1131515 : Blo 231814 1131515 := bstep (se 1 (by rfl) ⟨848636, by rfl⟩ : syracuseStep 1131515 = 1697273) B1697273
theorem B443627 : Blo 231814 443627 := bstep (se 1 (by rfl) ⟨332720, by rfl⟩ : syracuseStep 443627 = 665441) B665441
theorem B476641 : Blo 231814 476641 := bstep (se 2 (by rfl) ⟨178740, by rfl⟩ : syracuseStep 476641 = 357481) B357481
theorem B477467 : Blo 231814 477467 := bstep (se 1 (by rfl) ⟨358100, by rfl⟩ : syracuseStep 477467 = 716201) B716201
theorem B313679 : Blo 231814 313679 := bstep (se 1 (by rfl) ⟨235259, by rfl⟩ : syracuseStep 313679 = 470519) B470519
theorem B313727 : Blo 231814 313727 := bstep (se 1 (by rfl) ⟨235295, by rfl⟩ : syracuseStep 313727 = 470591) B470591
theorem B445267 : Blo 231814 445267 := bstep (se 1 (by rfl) ⟨333950, by rfl⟩ : syracuseStep 445267 = 667901) B667901
theorem B445495 : Blo 231814 445495 := bstep (se 1 (by rfl) ⟨334121, by rfl⟩ : syracuseStep 445495 = 668243) B668243
theorem B2673971 : Blo 231814 2673971 := bstep (se 1 (by rfl) ⟨2005478, by rfl⟩ : syracuseStep 2673971 = 4010957) B4010957
theorem B281983 : Blo 231814 281983 := bstep (se 1 (by rfl) ⟨211487, by rfl⟩ : syracuseStep 281983 = 422975) B422975
theorem B282079 : Blo 231814 282079 := bstep (se 1 (by rfl) ⟨211559, by rfl⟩ : syracuseStep 282079 = 423119) B423119
theorem B2641895 : Blo 231814 2641895 := bstep (se 1 (by rfl) ⟨1981421, by rfl⟩ : syracuseStep 2641895 = 3962843) B3962843
theorem B348143 : Blo 231814 348143 := bstep (se 1 (by rfl) ⟨261107, by rfl⟩ : syracuseStep 348143 = 522215) B522215
theorem B348155 : Blo 231814 348155 := bstep (se 1 (by rfl) ⟨261116, by rfl⟩ : syracuseStep 348155 = 522233) B522233
theorem B348215 : Blo 231814 348215 := bstep (se 1 (by rfl) ⟨261161, by rfl⟩ : syracuseStep 348215 = 522323) B522323
theorem B348263 : Blo 231814 348263 := bstep (se 1 (by rfl) ⟨261197, by rfl⟩ : syracuseStep 348263 = 522395) B522395
theorem B348335 : Blo 231814 348335 := bstep (se 1 (by rfl) ⟨261251, by rfl⟩ : syracuseStep 348335 = 522503) B522503
theorem B5099719 : Blo 231814 5099719 := bstep (se 1 (by rfl) ⟨3824789, by rfl⟩ : syracuseStep 5099719 = 7649579) B7649579
theorem B1888589 : Blo 231814 1888589 := bstep (se 3 (by rfl) ⟨354110, by rfl⟩ : syracuseStep 1888589 = 708221) B708221
theorem B348539 : Blo 231814 348539 := bstep (se 1 (by rfl) ⟨261404, by rfl⟩ : syracuseStep 348539 = 522809) B522809
theorem B676219 : Blo 231814 676219 := bstep (se 1 (by rfl) ⟨507164, by rfl⟩ : syracuseStep 676219 = 1014329) B1014329
theorem B1134985 : Blo 231814 1134985 := bstep (se 2 (by rfl) ⟨425619, by rfl⟩ : syracuseStep 1134985 = 851239) B851239
theorem B1790423 : Blo 231814 1790423 := bstep (se 1 (by rfl) ⟨1342817, by rfl⟩ : syracuseStep 1790423 = 2685635) B2685635
theorem B446953 : Blo 231814 446953 := bstep (se 2 (by rfl) ⟨167607, by rfl⟩ : syracuseStep 446953 = 335215) B335215
theorem B13587011 : Blo 231814 13587011 := bstep (se 1 (by rfl) ⟨10190258, by rfl⟩ : syracuseStep 13587011 = 20380517) B20380517
theorem B348809 : Blo 231814 348809 := bstep (se 2 (by rfl) ⟨130803, by rfl⟩ : syracuseStep 348809 = 261607) B261607
theorem B447113 : Blo 231814 447113 := bstep (se 2 (by rfl) ⟨167667, by rfl⟩ : syracuseStep 447113 = 335335) B335335
theorem B349019 : Blo 231814 349019 := bstep (se 1 (by rfl) ⟨261764, by rfl⟩ : syracuseStep 349019 = 523529) B523529
theorem B611297 : Blo 231814 611297 := bstep (se 2 (by rfl) ⟨229236, by rfl⟩ : syracuseStep 611297 = 458473) B458473
theorem B349481 : Blo 231814 349481 := bstep (se 2 (by rfl) ⟨131055, by rfl⟩ : syracuseStep 349481 = 262111) B262111
theorem B349679 : Blo 231814 349679 := bstep (se 1 (by rfl) ⟨262259, by rfl⟩ : syracuseStep 349679 = 524519) B524519
theorem B7296551 : Blo 231814 7296551 := bstep (se 1 (by rfl) ⟨5472413, by rfl⟩ : syracuseStep 7296551 = 10944827) B10944827
theorem B350075 : Blo 231814 350075 := bstep (se 1 (by rfl) ⟨262556, by rfl⟩ : syracuseStep 350075 = 525113) B525113
theorem B350111 : Blo 231814 350111 := bstep (se 1 (by rfl) ⟨262583, by rfl⟩ : syracuseStep 350111 = 525167) B525167
theorem B743393 : Blo 231814 743393 := bstep (se 2 (by rfl) ⟨278772, by rfl⟩ : syracuseStep 743393 = 557545) B557545
theorem B350345 : Blo 231814 350345 := bstep (se 2 (by rfl) ⟨131379, by rfl⟩ : syracuseStep 350345 = 262759) B262759
theorem B1267883 : Blo 231814 1267883 := bstep (se 1 (by rfl) ⟨950912, by rfl⟩ : syracuseStep 1267883 = 1901825) B1901825
theorem B350495 : Blo 231814 350495 := bstep (se 1 (by rfl) ⟨262871, by rfl⟩ : syracuseStep 350495 = 525743) B525743
theorem B351047 : Blo 231814 351047 := bstep (se 1 (by rfl) ⟨263285, by rfl⟩ : syracuseStep 351047 = 526571) B526571
theorem B1006415 : Blo 231814 1006415 := bstep (se 1 (by rfl) ⟨754811, by rfl⟩ : syracuseStep 1006415 = 1509623) B1509623
theorem B1891183 : Blo 231814 1891183 := bstep (se 1 (by rfl) ⟨1418387, by rfl⟩ : syracuseStep 1891183 = 2836775) B2836775
theorem B351911 : Blo 231814 351911 := bstep (se 1 (by rfl) ⟨263933, by rfl⟩ : syracuseStep 351911 = 527867) B527867
theorem B1105633 : Blo 231814 1105633 := bstep (se 2 (by rfl) ⟨414612, by rfl⟩ : syracuseStep 1105633 = 829225) B829225
theorem B352031 : Blo 231814 352031 := bstep (se 1 (by rfl) ⟨264023, by rfl⟩ : syracuseStep 352031 = 528047) B528047
theorem B352463 : Blo 231814 352463 := bstep (se 1 (by rfl) ⟨264347, by rfl⟩ : syracuseStep 352463 = 528695) B528695
theorem B352511 : Blo 231814 352511 := bstep (se 1 (by rfl) ⟨264383, by rfl⟩ : syracuseStep 352511 = 528767) B528767
theorem B1335689 : Blo 231814 1335689 := bstep (se 2 (by rfl) ⟨500883, by rfl⟩ : syracuseStep 1335689 = 1001767) B1001767
theorem B16114211 : Blo 231814 16114211 := bstep (se 1 (by rfl) ⟨12085658, by rfl⟩ : syracuseStep 16114211 = 24171317) B24171317
theorem B13656721 : Blo 231814 13656721 := bstep (se 2 (by rfl) ⟨5121270, by rfl⟩ : syracuseStep 13656721 = 10242541) B10242541
theorem B1762235 : Blo 231814 1762235 := bstep (se 1 (by rfl) ⟨1321676, by rfl⟩ : syracuseStep 1762235 = 2643353) B2643353
theorem B353327 : Blo 231814 353327 := bstep (se 1 (by rfl) ⟨264995, by rfl⟩ : syracuseStep 353327 = 529991) B529991
theorem B418937 : Blo 231814 418937 := bstep (se 2 (by rfl) ⟨157101, by rfl⟩ : syracuseStep 418937 = 314203) B314203
theorem B353447 : Blo 231814 353447 := bstep (se 1 (by rfl) ⟨265085, by rfl⟩ : syracuseStep 353447 = 530171) B530171
theorem B1500419 : Blo 231814 1500419 := bstep (se 1 (by rfl) ⟨1125314, by rfl⟩ : syracuseStep 1500419 = 2250629) B2250629
theorem B353819 : Blo 231814 353819 := bstep (se 1 (by rfl) ⟨265364, by rfl⟩ : syracuseStep 353819 = 530729) B530729
theorem B1173851 : Blo 231814 1173851 := bstep (se 1 (by rfl) ⟨880388, by rfl⟩ : syracuseStep 1173851 = 1760777) B1760777
theorem B1763693 : Blo 231814 1763693 := bstep (se 3 (by rfl) ⟨330692, by rfl⟩ : syracuseStep 1763693 = 661385) B661385
theorem B1993247 : Blo 231814 1993247 := bstep (se 1 (by rfl) ⟨1494935, by rfl⟩ : syracuseStep 1993247 = 2989871) B2989871
theorem B1339355 : Blo 231814 1339355 := bstep (se 1 (by rfl) ⟨1004516, by rfl⟩ : syracuseStep 1339355 = 2009033) B2009033
theorem B1896635 : Blo 231814 1896635 := bstep (se 1 (by rfl) ⟨1422476, by rfl⟩ : syracuseStep 1896635 = 2844953) B2844953
theorem B8516177 : Blo 231814 8516177 := bstep (se 2 (by rfl) ⟨3193566, by rfl⟩ : syracuseStep 8516177 = 6387133) B6387133
theorem B1766123 : Blo 231814 1766123 := bstep (se 1 (by rfl) ⟨1324592, by rfl⟩ : syracuseStep 1766123 = 2649185) B2649185
theorem B1897411 : Blo 231814 1897411 := bstep (se 1 (by rfl) ⟨1423058, by rfl⟩ : syracuseStep 1897411 = 2846117) B2846117
theorem B586835 : Blo 231814 586835 := bstep (se 1 (by rfl) ⟨440126, by rfl⟩ : syracuseStep 586835 = 880253) B880253
theorem B1766609 : Blo 231814 1766609 := bstep (se 2 (by rfl) ⟨662478, by rfl⟩ : syracuseStep 1766609 = 1324957) B1324957
theorem B521639 : Blo 231814 521639 := bstep (se 1 (by rfl) ⟨391229, by rfl⟩ : syracuseStep 521639 = 782459) B782459
theorem B521747 : Blo 231814 521747 := bstep (se 1 (by rfl) ⟨391310, by rfl⟩ : syracuseStep 521747 = 782621) B782621
theorem B521819 : Blo 231814 521819 := bstep (se 1 (by rfl) ⟨391364, by rfl⟩ : syracuseStep 521819 = 782729) B782729
theorem B784025 : Blo 231814 784025 := bstep (se 2 (by rfl) ⟨294009, by rfl⟩ : syracuseStep 784025 = 588019) B588019
theorem B7698341 : Blo 231814 7698341 := bstep (se 4 (by rfl) ⟨721719, by rfl⟩ : syracuseStep 7698341 = 1443439) B1443439
theorem B1210351 : Blo 231814 1210351 := bstep (se 1 (by rfl) ⟨907763, by rfl⟩ : syracuseStep 1210351 = 1815527) B1815527
theorem B391351 : Blo 231814 391351 := bstep (se 1 (by rfl) ⟨293513, by rfl⟩ : syracuseStep 391351 = 587027) B587027
theorem B522431 : Blo 231814 522431 := bstep (se 1 (by rfl) ⟨391823, by rfl⟩ : syracuseStep 522431 = 783647) B783647
theorem B1341839 : Blo 231814 1341839 := bstep (se 1 (by rfl) ⟨1006379, by rfl⟩ : syracuseStep 1341839 = 2012759) B2012759
theorem B883169 : Blo 231814 883169 := bstep (se 2 (by rfl) ⟨331188, by rfl⟩ : syracuseStep 883169 = 662377) B662377
theorem B391945 : Blo 231814 391945 := bstep (se 2 (by rfl) ⟨146979, by rfl⟩ : syracuseStep 391945 = 293959) B293959
theorem B261031 : Blo 231814 261031 := bstep (se 1 (by rfl) ⟨195773, by rfl⟩ : syracuseStep 261031 = 391547) B391547
theorem B2030629 : Blo 231814 2030629 := bstep (se 4 (by rfl) ⟨190371, by rfl⟩ : syracuseStep 2030629 = 380743) B380743
theorem B261211 : Blo 231814 261211 := bstep (se 1 (by rfl) ⟨195908, by rfl⟩ : syracuseStep 261211 = 391817) B391817
theorem B1703263 : Blo 231814 1703263 := bstep (se 1 (by rfl) ⟨1277447, by rfl⟩ : syracuseStep 1703263 = 2554895) B2554895
theorem B523691 : Blo 231814 523691 := bstep (se 1 (by rfl) ⟨392768, by rfl⟩ : syracuseStep 523691 = 785537) B785537
theorem B523727 : Blo 231814 523727 := bstep (se 1 (by rfl) ⟨392795, by rfl⟩ : syracuseStep 523727 = 785591) B785591
theorem B785915 : Blo 231814 785915 := bstep (se 1 (by rfl) ⟨589436, by rfl⟩ : syracuseStep 785915 = 1178873) B1178873
theorem B1769039 : Blo 231814 1769039 := bstep (se 1 (by rfl) ⟨1326779, by rfl⟩ : syracuseStep 1769039 = 2653559) B2653559
theorem B294511 : Blo 231814 294511 := bstep (se 1 (by rfl) ⟨220883, by rfl⟩ : syracuseStep 294511 = 441767) B441767
theorem B786077 : Blo 231814 786077 := bstep (se 3 (by rfl) ⟨147389, by rfl⟩ : syracuseStep 786077 = 294779) B294779
theorem B786185 : Blo 231814 786185 := bstep (se 2 (by rfl) ⟨294819, by rfl⟩ : syracuseStep 786185 = 589639) B589639
theorem B524231 : Blo 231814 524231 := bstep (se 1 (by rfl) ⟨393173, by rfl⟩ : syracuseStep 524231 = 786347) B786347
theorem B524411 : Blo 231814 524411 := bstep (se 1 (by rfl) ⟨393308, by rfl⟩ : syracuseStep 524411 = 786617) B786617
theorem B3014779 : Blo 231814 3014779 := bstep (se 1 (by rfl) ⟨2261084, by rfl⟩ : syracuseStep 3014779 = 4522169) B4522169
theorem B2752699 : Blo 231814 2752699 := bstep (se 1 (by rfl) ⟨2064524, by rfl⟩ : syracuseStep 2752699 = 4129049) B4129049
theorem B524681 : Blo 231814 524681 := bstep (se 2 (by rfl) ⟨196755, by rfl⟩ : syracuseStep 524681 = 393511) B393511
theorem B524699 : Blo 231814 524699 := bstep (se 1 (by rfl) ⟨393524, by rfl⟩ : syracuseStep 524699 = 787049) B787049
theorem B786941 : Blo 231814 786941 := bstep (se 3 (by rfl) ⟨147551, by rfl⟩ : syracuseStep 786941 = 295103) B295103
theorem B754343 : Blo 231814 754343 := bstep (se 1 (by rfl) ⟨565757, by rfl⟩ : syracuseStep 754343 = 1131515) B1131515
theorem B5079833 : Blo 231814 5079833 := bstep (se 2 (by rfl) ⟨1904937, by rfl⟩ : syracuseStep 5079833 = 3809875) B3809875
theorem B2720537 : Blo 231814 2720537 := bstep (se 2 (by rfl) ⟨1020201, by rfl⟩ : syracuseStep 2720537 = 2040403) B2040403
theorem B262975 : Blo 231814 262975 := bstep (se 1 (by rfl) ⟨197231, by rfl⟩ : syracuseStep 262975 = 394463) B394463
theorem B295751 : Blo 231814 295751 := bstep (se 1 (by rfl) ⟨221813, by rfl⟩ : syracuseStep 295751 = 443627) B443627
theorem B525851 : Blo 231814 525851 := bstep (se 1 (by rfl) ⟨394388, by rfl⟩ : syracuseStep 525851 = 788777) B788777
theorem B394895 : Blo 231814 394895 := bstep (se 1 (by rfl) ⟨296171, by rfl⟩ : syracuseStep 394895 = 592343) B592343
theorem B1181951 : Blo 231814 1181951 := bstep (se 1 (by rfl) ⟨886463, by rfl⟩ : syracuseStep 1181951 = 1772927) B1772927
theorem B1182113 : Blo 231814 1182113 := bstep (se 2 (by rfl) ⟨443292, by rfl⟩ : syracuseStep 1182113 = 886585) B886585
theorem B232095 : Blo 231814 232095 := bstep (se 1 (by rfl) ⟨174071, by rfl⟩ : syracuseStep 232095 = 348143) B348143
theorem B854687 : Blo 231814 854687 := bstep (se 1 (by rfl) ⟨641015, by rfl⟩ : syracuseStep 854687 = 1282031) B1282031
theorem B232103 : Blo 231814 232103 := bstep (se 1 (by rfl) ⟨174077, by rfl⟩ : syracuseStep 232103 = 348155) B348155
theorem B232143 : Blo 231814 232143 := bstep (se 1 (by rfl) ⟨174107, by rfl⟩ : syracuseStep 232143 = 348215) B348215
theorem B232175 : Blo 231814 232175 := bstep (se 1 (by rfl) ⟨174131, by rfl⟩ : syracuseStep 232175 = 348263) B348263
theorem B232223 : Blo 231814 232223 := bstep (se 1 (by rfl) ⟨174167, by rfl⟩ : syracuseStep 232223 = 348335) B348335
theorem B264991 : Blo 231814 264991 := bstep (se 1 (by rfl) ⟨198743, by rfl⟩ : syracuseStep 264991 = 397487) B397487
theorem B232359 : Blo 231814 232359 := bstep (se 1 (by rfl) ⟨174269, by rfl⟩ : syracuseStep 232359 = 348539) B348539
theorem B1117147 : Blo 231814 1117147 := bstep (se 1 (by rfl) ⟨837860, by rfl⟩ : syracuseStep 1117147 = 1675721) B1675721
theorem B1117165 : Blo 231814 1117165 := bstep (se 3 (by rfl) ⟨209468, by rfl⟩ : syracuseStep 1117165 = 418937) B418937
theorem B232539 : Blo 231814 232539 := bstep (se 1 (by rfl) ⟨174404, by rfl⟩ : syracuseStep 232539 = 348809) B348809
theorem B298075 : Blo 231814 298075 := bstep (se 1 (by rfl) ⟨223556, by rfl⟩ : syracuseStep 298075 = 447113) B447113
theorem B232679 : Blo 231814 232679 := bstep (se 1 (by rfl) ⟨174509, by rfl⟩ : syracuseStep 232679 = 349019) B349019
theorem B232987 : Blo 231814 232987 := bstep (se 1 (by rfl) ⟨174740, by rfl⟩ : syracuseStep 232987 = 349481) B349481
theorem B233119 : Blo 231814 233119 := bstep (se 1 (by rfl) ⟨174839, by rfl⟩ : syracuseStep 233119 = 349679) B349679
theorem B659167 : Blo 231814 659167 := bstep (se 1 (by rfl) ⟨494375, by rfl⟩ : syracuseStep 659167 = 988751) B988751
theorem B593689 : Blo 231814 593689 := bstep (se 2 (by rfl) ⟨222633, by rfl⟩ : syracuseStep 593689 = 445267) B445267
theorem B233383 : Blo 231814 233383 := bstep (se 1 (by rfl) ⟨175037, by rfl⟩ : syracuseStep 233383 = 350075) B350075
theorem B593831 : Blo 231814 593831 := bstep (se 1 (by rfl) ⟨445373, by rfl⟩ : syracuseStep 593831 = 890747) B890747
theorem B233407 : Blo 231814 233407 := bstep (se 1 (by rfl) ⟨175055, by rfl⟩ : syracuseStep 233407 = 350111) B350111
theorem B495595 : Blo 231814 495595 := bstep (se 1 (by rfl) ⟨371696, by rfl⟩ : syracuseStep 495595 = 743393) B743393
theorem B593993 : Blo 231814 593993 := bstep (se 2 (by rfl) ⟨222747, by rfl⟩ : syracuseStep 593993 = 445495) B445495
theorem B233563 : Blo 231814 233563 := bstep (se 1 (by rfl) ⟨175172, by rfl⟩ : syracuseStep 233563 = 350345) B350345
theorem B233663 : Blo 231814 233663 := bstep (se 1 (by rfl) ⟨175247, by rfl⟩ : syracuseStep 233663 = 350495) B350495
theorem B790991 : Blo 231814 790991 := bstep (se 1 (by rfl) ⟨593243, by rfl⟩ : syracuseStep 790991 = 1186487) B1186487
theorem B234031 : Blo 231814 234031 := bstep (se 1 (by rfl) ⟨175523, by rfl⟩ : syracuseStep 234031 = 351047) B351047
theorem B791315 : Blo 231814 791315 := bstep (se 1 (by rfl) ⟨593486, by rfl⟩ : syracuseStep 791315 = 1186973) B1186973
theorem B234607 : Blo 231814 234607 := bstep (se 1 (by rfl) ⟨175955, by rfl⟩ : syracuseStep 234607 = 351911) B351911
theorem B529577 : Blo 231814 529577 := bstep (se 2 (by rfl) ⟨198591, by rfl⟩ : syracuseStep 529577 = 397183) B397183
theorem B234687 : Blo 231814 234687 := bstep (se 1 (by rfl) ⟨176015, by rfl⟩ : syracuseStep 234687 = 352031) B352031
theorem B333119 : Blo 231814 333119 := bstep (se 1 (by rfl) ⟨249839, by rfl⟩ : syracuseStep 333119 = 499679) B499679
theorem B234975 : Blo 231814 234975 := bstep (se 1 (by rfl) ⟨176231, by rfl⟩ : syracuseStep 234975 = 352463) B352463
theorem B235007 : Blo 231814 235007 := bstep (se 1 (by rfl) ⟨176255, by rfl⟩ : syracuseStep 235007 = 352511) B352511
theorem B890459 : Blo 231814 890459 := bstep (se 1 (by rfl) ⟨667844, by rfl⟩ : syracuseStep 890459 = 1335689) B1335689
theorem B1513313 : Blo 231814 1513313 := bstep (se 2 (by rfl) ⟨567492, by rfl⟩ : syracuseStep 1513313 = 1134985) B1134985
theorem B595937 : Blo 231814 595937 := bstep (se 2 (by rfl) ⟨223476, by rfl⟩ : syracuseStep 595937 = 446953) B446953
theorem B235551 : Blo 231814 235551 := bstep (se 1 (by rfl) ⟨176663, by rfl⟩ : syracuseStep 235551 = 353327) B353327
theorem B235631 : Blo 231814 235631 := bstep (se 1 (by rfl) ⟨176723, by rfl⟩ : syracuseStep 235631 = 353447) B353447
theorem B1186001 : Blo 231814 1186001 := bstep (se 2 (by rfl) ⟨444750, by rfl⟩ : syracuseStep 1186001 = 889501) B889501
theorem B235879 : Blo 231814 235879 := bstep (se 1 (by rfl) ⟨176909, by rfl⟩ : syracuseStep 235879 = 353819) B353819
theorem B7543205 : Blo 231814 7543205 := bstep (se 4 (by rfl) ⟨707175, by rfl⟩ : syracuseStep 7543205 = 1414351) B1414351
theorem B2529881 : Blo 231814 2529881 := bstep (se 2 (by rfl) ⟨948705, by rfl⟩ : syracuseStep 2529881 = 1897411) B1897411
theorem B1186811 : Blo 231814 1186811 := bstep (se 1 (by rfl) ⟨890108, by rfl⟩ : syracuseStep 1186811 = 1780217) B1780217
theorem B3808457 : Blo 231814 3808457 := bstep (se 2 (by rfl) ⟨1428171, by rfl⟩ : syracuseStep 3808457 = 2856343) B2856343
theorem B794393 : Blo 231814 794393 := bstep (se 2 (by rfl) ⟨297897, by rfl⟩ : syracuseStep 794393 = 595795) B595795
theorem B794447 : Blo 231814 794447 := bstep (se 1 (by rfl) ⟨595835, by rfl⟩ : syracuseStep 794447 = 1191671) B1191671
theorem B1187783 : Blo 231814 1187783 := bstep (se 1 (by rfl) ⟨890837, by rfl⟩ : syracuseStep 1187783 = 1781675) B1781675
theorem B892903 : Blo 231814 892903 := bstep (se 1 (by rfl) ⟨669677, by rfl⟩ : syracuseStep 892903 = 1339355) B1339355
theorem B1613801 : Blo 231814 1613801 := bstep (se 2 (by rfl) ⟨605175, by rfl⟩ : syracuseStep 1613801 = 1210351) B1210351
theorem B794771 : Blo 231814 794771 := bstep (se 1 (by rfl) ⟨596078, by rfl⟩ : syracuseStep 794771 = 1192157) B1192157
theorem B1417609 : Blo 231814 1417609 := bstep (se 2 (by rfl) ⟨531603, by rfl⟩ : syracuseStep 1417609 = 1063207) B1063207
theorem B5677451 : Blo 231814 5677451 := bstep (se 1 (by rfl) ⟨4258088, by rfl⟩ : syracuseStep 5677451 = 8516177) B8516177
theorem B991703 : Blo 231814 991703 := bstep (se 1 (by rfl) ⟨743777, by rfl⟩ : syracuseStep 991703 = 1487555) B1487555
theorem B992351 : Blo 231814 992351 := bstep (se 1 (by rfl) ⟨744263, by rfl⟩ : syracuseStep 992351 = 1488527) B1488527
theorem B533611 : Blo 231814 533611 := bstep (se 1 (by rfl) ⟨400208, by rfl⟩ : syracuseStep 533611 = 800417) B800417
theorem B894559 : Blo 231814 894559 := bstep (se 1 (by rfl) ⟨670919, by rfl⟩ : syracuseStep 894559 = 1341839) B1341839
theorem B2271017 : Blo 231814 2271017 := bstep (se 2 (by rfl) ⟨851631, by rfl⟩ : syracuseStep 2271017 = 1703263) B1703263
theorem B994301 : Blo 231814 994301 := bstep (se 3 (by rfl) ⟨186431, by rfl⟩ : syracuseStep 994301 = 372863) B372863
theorem B339247 : Blo 231814 339247 := bstep (se 1 (by rfl) ⟨254435, by rfl⟩ : syracuseStep 339247 = 508871) B508871
theorem B667241 : Blo 231814 667241 := bstep (se 2 (by rfl) ⟨250215, by rfl⟩ : syracuseStep 667241 = 500431) B500431
theorem B2993867 : Blo 231814 2993867 := bstep (se 1 (by rfl) ⟨2245400, by rfl⟩ : syracuseStep 2993867 = 4490801) B4490801
theorem B11448125 : Blo 231814 11448125 := bstep (se 3 (by rfl) ⟨2146523, by rfl⟩ : syracuseStep 11448125 = 4293047) B4293047
theorem B6795251 : Blo 231814 6795251 := bstep (se 1 (by rfl) ⟨5096438, by rfl⟩ : syracuseStep 6795251 = 10192877) B10192877
theorem B635521 : Blo 231814 635521 := bstep (se 2 (by rfl) ⟨238320, by rfl⟩ : syracuseStep 635521 = 476641) B476641
theorem B668425 : Blo 231814 668425 := bstep (se 2 (by rfl) ⟨250659, by rfl⟩ : syracuseStep 668425 = 501319) B501319
theorem B1782647 : Blo 231814 1782647 := bstep (se 1 (by rfl) ⟨1336985, by rfl⟩ : syracuseStep 1782647 = 2673971) B2673971
theorem B1259059 : Blo 231814 1259059 := bstep (se 1 (by rfl) ⟨944294, by rfl⟩ : syracuseStep 1259059 = 1888589) B1888589
theorem B1193615 : Blo 231814 1193615 := bstep (se 1 (by rfl) ⟨895211, by rfl⟩ : syracuseStep 1193615 = 1790423) B1790423
theorem B9058007 : Blo 231814 9058007 := bstep (se 1 (by rfl) ⟨6793505, by rfl⟩ : syracuseStep 9058007 = 13587011) B13587011
theorem B440255 : Blo 231814 440255 := bstep (se 1 (by rfl) ⟨330191, by rfl⟩ : syracuseStep 440255 = 660383) B660383
theorem B407531 : Blo 231814 407531 := bstep (se 1 (by rfl) ⟨305648, by rfl⟩ : syracuseStep 407531 = 611297) B611297
theorem B4864367 : Blo 231814 4864367 := bstep (se 1 (by rfl) ⟨3648275, by rfl⟩ : syracuseStep 4864367 = 7296551) B7296551
theorem B375977 : Blo 231814 375977 := bstep (se 2 (by rfl) ⟨140991, by rfl⟩ : syracuseStep 375977 = 281983) B281983
theorem B670943 : Blo 231814 670943 := bstep (se 1 (by rfl) ⟨503207, by rfl⟩ : syracuseStep 670943 = 1006415) B1006415
theorem B376105 : Blo 231814 376105 := bstep (se 2 (by rfl) ⟨141039, by rfl⟩ : syracuseStep 376105 = 282079) B282079
theorem B20528909 : Blo 231814 20528909 := bstep (se 3 (by rfl) ⟨3849170, by rfl⟩ : syracuseStep 20528909 = 7698341) B7698341
theorem B6799625 : Blo 231814 6799625 := bstep (se 2 (by rfl) ⟨2549859, by rfl⟩ : syracuseStep 6799625 = 5099719) B5099719
theorem B901625 : Blo 231814 901625 := bstep (se 2 (by rfl) ⟨338109, by rfl⟩ : syracuseStep 901625 = 676219) B676219
theorem B1491655 : Blo 231814 1491655 := bstep (se 1 (by rfl) ⟨1118741, by rfl⟩ : syracuseStep 1491655 = 2237483) B2237483
theorem B1000279 : Blo 231814 1000279 := bstep (se 1 (by rfl) ⟨750209, by rfl⟩ : syracuseStep 1000279 = 1500419) B1500419
theorem B836477 : Blo 231814 836477 := bstep (se 3 (by rfl) ⟨156839, by rfl⟩ : syracuseStep 836477 = 313679) B313679
theorem B836605 : Blo 231814 836605 := bstep (se 3 (by rfl) ⟨156863, by rfl⟩ : syracuseStep 836605 = 313727) B313727
theorem B443711 : Blo 231814 443711 := bstep (se 1 (by rfl) ⟨332783, by rfl⟩ : syracuseStep 443711 = 665567) B665567
theorem B1328831 : Blo 231814 1328831 := bstep (se 1 (by rfl) ⟨996623, by rfl⟩ : syracuseStep 1328831 = 1993247) B1993247
theorem B444599 : Blo 231814 444599 := bstep (se 1 (by rfl) ⟨333449, by rfl⟩ : syracuseStep 444599 = 666899) B666899
theorem B707201 : Blo 231814 707201 := bstep (se 2 (by rfl) ⟨265200, by rfl⟩ : syracuseStep 707201 = 530401) B530401
theorem B1985249 : Blo 231814 1985249 := bstep (se 2 (by rfl) ⟨744468, by rfl⟩ : syracuseStep 1985249 = 1488937) B1488937
theorem B1264423 : Blo 231814 1264423 := bstep (se 1 (by rfl) ⟨948317, by rfl⟩ : syracuseStep 1264423 = 1896635) B1896635
theorem B347759 : Blo 231814 347759 := bstep (se 1 (by rfl) ⟨260819, by rfl⟩ : syracuseStep 347759 = 521639) B521639
theorem B347831 : Blo 231814 347831 := bstep (se 1 (by rfl) ⟨260873, by rfl⟩ : syracuseStep 347831 = 521747) B521747
theorem B347879 : Blo 231814 347879 := bstep (se 1 (by rfl) ⟨260909, by rfl⟩ : syracuseStep 347879 = 521819) B521819
theorem B348041 : Blo 231814 348041 := bstep (se 2 (by rfl) ⟨130515, by rfl⟩ : syracuseStep 348041 = 261031) B261031
theorem B2707505 : Blo 231814 2707505 := bstep (se 2 (by rfl) ⟨1015314, by rfl⟩ : syracuseStep 2707505 = 2030629) B2030629
theorem B348281 : Blo 231814 348281 := bstep (se 2 (by rfl) ⟨130605, by rfl⟩ : syracuseStep 348281 = 261211) B261211
theorem B348287 : Blo 231814 348287 := bstep (se 1 (by rfl) ⟨261215, by rfl⟩ : syracuseStep 348287 = 522431) B522431
theorem B315695 : Blo 231814 315695 := bstep (se 1 (by rfl) ⟨236771, by rfl⟩ : syracuseStep 315695 = 473543) B473543
theorem B349127 : Blo 231814 349127 := bstep (se 1 (by rfl) ⟨261845, by rfl⟩ : syracuseStep 349127 = 523691) B523691
theorem B447439 : Blo 231814 447439 := bstep (se 1 (by rfl) ⟨335579, by rfl⟩ : syracuseStep 447439 = 671159) B671159
theorem B349151 : Blo 231814 349151 := bstep (se 1 (by rfl) ⟨261863, by rfl⟩ : syracuseStep 349151 = 523727) B523727
theorem B349487 : Blo 231814 349487 := bstep (se 1 (by rfl) ⟨262115, by rfl⟩ : syracuseStep 349487 = 524231) B524231
theorem B349691 : Blo 231814 349691 := bstep (se 1 (by rfl) ⟨262268, by rfl⟩ : syracuseStep 349691 = 524537) B524537
theorem B349727 : Blo 231814 349727 := bstep (se 1 (by rfl) ⟨262295, by rfl⟩ : syracuseStep 349727 = 524591) B524591
theorem B349865 : Blo 231814 349865 := bstep (se 2 (by rfl) ⟨131199, by rfl⟩ : syracuseStep 349865 = 262399) B262399
theorem B349871 : Blo 231814 349871 := bstep (se 1 (by rfl) ⟨262403, by rfl⟩ : syracuseStep 349871 = 524807) B524807
theorem B349991 : Blo 231814 349991 := bstep (se 1 (by rfl) ⟨262493, by rfl⟩ : syracuseStep 349991 = 524987) B524987
theorem B350249 : Blo 231814 350249 := bstep (se 2 (by rfl) ⟨131343, by rfl⟩ : syracuseStep 350249 = 262687) B262687
theorem B350279 : Blo 231814 350279 := bstep (se 1 (by rfl) ⟨262709, by rfl⟩ : syracuseStep 350279 = 525419) B525419
theorem B18208961 : Blo 231814 18208961 := bstep (se 2 (by rfl) ⟨6828360, by rfl⟩ : syracuseStep 18208961 = 13656721) B13656721
theorem B350591 : Blo 231814 350591 := bstep (se 1 (by rfl) ⟨262943, by rfl⟩ : syracuseStep 350591 = 525887) B525887
theorem B350663 : Blo 231814 350663 := bstep (se 1 (by rfl) ⟨262997, by rfl⟩ : syracuseStep 350663 = 525995) B525995
theorem B350879 : Blo 231814 350879 := bstep (se 1 (by rfl) ⟨263159, by rfl⟩ : syracuseStep 350879 = 526319) B526319
theorem B351023 : Blo 231814 351023 := bstep (se 1 (by rfl) ⟨263267, by rfl⟩ : syracuseStep 351023 = 526535) B526535
theorem B2054969 : Blo 231814 2054969 := bstep (se 2 (by rfl) ⟨770613, by rfl⟩ : syracuseStep 2054969 = 1541227) B1541227
theorem B318311 : Blo 231814 318311 := bstep (se 1 (by rfl) ⟨238733, by rfl⟩ : syracuseStep 318311 = 477467) B477467
theorem B2907011 : Blo 231814 2907011 := bstep (se 1 (by rfl) ⟨2180258, by rfl⟩ : syracuseStep 2907011 = 4360517) B4360517
theorem B842633 : Blo 231814 842633 := bstep (se 2 (by rfl) ⟨315987, by rfl⟩ : syracuseStep 842633 = 631975) B631975
theorem B351113 : Blo 231814 351113 := bstep (se 2 (by rfl) ⟨131667, by rfl⟩ : syracuseStep 351113 = 263335) B263335
theorem B351143 : Blo 231814 351143 := bstep (se 1 (by rfl) ⟨263357, by rfl⟩ : syracuseStep 351143 = 526715) B526715
theorem B318377 : Blo 231814 318377 := bstep (se 2 (by rfl) ⟨119391, by rfl⟩ : syracuseStep 318377 = 238783) B238783
theorem B351323 : Blo 231814 351323 := bstep (se 1 (by rfl) ⟨263492, by rfl⟩ : syracuseStep 351323 = 526985) B526985
theorem B351515 : Blo 231814 351515 := bstep (se 1 (by rfl) ⟨263636, by rfl⟩ : syracuseStep 351515 = 527273) B527273
theorem B2678345 : Blo 231814 2678345 := bstep (se 2 (by rfl) ⟨1004379, by rfl⟩ : syracuseStep 2678345 = 2008759) B2008759
theorem B351983 : Blo 231814 351983 := bstep (se 1 (by rfl) ⟨263987, by rfl⟩ : syracuseStep 351983 = 527975) B527975
theorem B352169 : Blo 231814 352169 := bstep (se 2 (by rfl) ⟨132063, by rfl⟩ : syracuseStep 352169 = 264127) B264127
theorem B1761263 : Blo 231814 1761263 := bstep (se 1 (by rfl) ⟨1320947, by rfl⟩ : syracuseStep 1761263 = 2641895) B2641895
theorem B352319 : Blo 231814 352319 := bstep (se 1 (by rfl) ⟨264239, by rfl⟩ : syracuseStep 352319 = 528479) B528479
theorem B352553 : Blo 231814 352553 := bstep (se 2 (by rfl) ⟨132207, by rfl⟩ : syracuseStep 352553 = 264415) B264415
theorem B352823 : Blo 231814 352823 := bstep (se 1 (by rfl) ⟨264617, by rfl⟩ : syracuseStep 352823 = 529235) B529235
theorem B353183 : Blo 231814 353183 := bstep (se 1 (by rfl) ⟨264887, by rfl⟩ : syracuseStep 353183 = 529775) B529775
theorem B2548745 : Blo 231814 2548745 := bstep (se 2 (by rfl) ⟨955779, by rfl⟩ : syracuseStep 2548745 = 1911559) B1911559
theorem B943163 : Blo 231814 943163 := bstep (se 1 (by rfl) ⟨707372, by rfl⟩ : syracuseStep 943163 = 1414745) B1414745
theorem B353471 : Blo 231814 353471 := bstep (se 1 (by rfl) ⟨265103, by rfl⟩ : syracuseStep 353471 = 530207) B530207
theorem B353615 : Blo 231814 353615 := bstep (se 1 (by rfl) ⟨265211, by rfl⟩ : syracuseStep 353615 = 530423) B530423
theorem B353705 : Blo 231814 353705 := bstep (se 2 (by rfl) ⟨132639, by rfl⟩ : syracuseStep 353705 = 265279) B265279
theorem B845255 : Blo 231814 845255 := bstep (se 1 (by rfl) ⟨633941, by rfl⟩ : syracuseStep 845255 = 1267883) B1267883
theorem B1336895 : Blo 231814 1336895 := bstep (se 1 (by rfl) ⟨1002671, by rfl⟩ : syracuseStep 1336895 = 2005343) B2005343
theorem B747431 : Blo 231814 747431 := bstep (se 1 (by rfl) ⟨560573, by rfl⟩ : syracuseStep 747431 = 1121147) B1121147
theorem B2975777 : Blo 231814 2975777 := bstep (se 2 (by rfl) ⟨1115916, by rfl⟩ : syracuseStep 2975777 = 2231833) B2231833
theorem B1337579 : Blo 231814 1337579 := bstep (se 1 (by rfl) ⟨1003184, by rfl⟩ : syracuseStep 1337579 = 2006369) B2006369
theorem B748187 : Blo 231814 748187 := bstep (se 1 (by rfl) ⟨561140, by rfl⟩ : syracuseStep 748187 = 1122281) B1122281
theorem B1338079 : Blo 231814 1338079 := bstep (se 1 (by rfl) ⟨1003559, by rfl⟩ : syracuseStep 1338079 = 2007119) B2007119
theorem B10742807 : Blo 231814 10742807 := bstep (se 1 (by rfl) ⟨8057105, by rfl⟩ : syracuseStep 10742807 = 16114211) B16114211
theorem B748673 : Blo 231814 748673 := bstep (se 2 (by rfl) ⟨280752, by rfl⟩ : syracuseStep 748673 = 561505) B561505
theorem B1174823 : Blo 231814 1174823 := bstep (se 1 (by rfl) ⟨881117, by rfl⟩ : syracuseStep 1174823 = 1762235) B1762235
theorem B782567 : Blo 231814 782567 := bstep (se 1 (by rfl) ⟨586925, by rfl⟩ : syracuseStep 782567 = 1173851) B1173851
theorem B1175795 : Blo 231814 1175795 := bstep (se 1 (by rfl) ⟨881846, by rfl⟩ : syracuseStep 1175795 = 1763693) B1763693
theorem B1274543 : Blo 231814 1274543 := bstep (se 1 (by rfl) ⟨955907, by rfl⟩ : syracuseStep 1274543 = 1911815) B1911815
theorem B24671411 : Blo 231814 24671411 := bstep (se 1 (by rfl) ⟨18503558, by rfl⟩ : syracuseStep 24671411 = 37007117) B37007117
theorem B423407 : Blo 231814 423407 := bstep (se 1 (by rfl) ⟨317555, by rfl⟩ : syracuseStep 423407 = 635111) B635111
theorem B521801 : Blo 231814 521801 := bstep (se 2 (by rfl) ⟨195675, by rfl⟩ : syracuseStep 521801 = 391351) B391351
theorem B1177415 : Blo 231814 1177415 := bstep (se 1 (by rfl) ⟨883061, by rfl⟩ : syracuseStep 1177415 = 1766123) B1766123
theorem B751531 : Blo 231814 751531 := bstep (se 1 (by rfl) ⟨563648, by rfl⟩ : syracuseStep 751531 = 1127297) B1127297
theorem B391223 : Blo 231814 391223 := bstep (se 1 (by rfl) ⟨293417, by rfl⟩ : syracuseStep 391223 = 586835) B586835
theorem B1177739 : Blo 231814 1177739 := bstep (se 1 (by rfl) ⟨883304, by rfl⟩ : syracuseStep 1177739 = 1766609) B1766609
theorem B522593 : Blo 231814 522593 := bstep (se 2 (by rfl) ⟨195972, by rfl⟩ : syracuseStep 522593 = 391945) B391945
theorem B522683 : Blo 231814 522683 := bstep (se 1 (by rfl) ⟨392012, by rfl⟩ : syracuseStep 522683 = 784025) B784025
theorem B2849231 : Blo 231814 2849231 := bstep (se 1 (by rfl) ⟨2136923, by rfl⟩ : syracuseStep 2849231 = 4273847) B4273847
theorem B2521577 : Blo 231814 2521577 := bstep (se 2 (by rfl) ⟨945591, by rfl⟩ : syracuseStep 2521577 = 1891183) B1891183
theorem B5896709 : Blo 231814 5896709 := bstep (se 4 (by rfl) ⟨552816, by rfl⟩ : syracuseStep 5896709 = 1105633) B1105633
theorem B424531 : Blo 231814 424531 := bstep (se 1 (by rfl) ⟨318398, by rfl⟩ : syracuseStep 424531 = 636797) B636797
theorem B588779 : Blo 231814 588779 := bstep (se 1 (by rfl) ⟨441584, by rfl⟩ : syracuseStep 588779 = 883169) B883169
theorem B949391 : Blo 231814 949391 := bstep (se 1 (by rfl) ⟨712043, by rfl⟩ : syracuseStep 949391 = 1424087) B1424087
theorem B392681 : Blo 231814 392681 := bstep (se 2 (by rfl) ⟨147255, by rfl⟩ : syracuseStep 392681 = 294511) B294511
theorem B523943 : Blo 231814 523943 := bstep (se 1 (by rfl) ⟨392957, by rfl⟩ : syracuseStep 523943 = 785915) B785915
theorem B1179359 : Blo 231814 1179359 := bstep (se 1 (by rfl) ⟨884519, by rfl⟩ : syracuseStep 1179359 = 1769039) B1769039
theorem B524051 : Blo 231814 524051 := bstep (se 1 (by rfl) ⟨393038, by rfl⟩ : syracuseStep 524051 = 786077) B786077
theorem B524123 : Blo 231814 524123 := bstep (se 1 (by rfl) ⟨393092, by rfl⟩ : syracuseStep 524123 = 786185) B786185
theorem B753619 : Blo 231814 753619 := bstep (se 1 (by rfl) ⟨565214, by rfl⟩ : syracuseStep 753619 = 1130429) B1130429
theorem B3670265 : Blo 231814 3670265 := bstep (se 2 (by rfl) ⟨1376349, by rfl⟩ : syracuseStep 3670265 = 2752699) B2752699
theorem B524627 : Blo 231814 524627 := bstep (se 1 (by rfl) ⟨393470, by rfl⟩ : syracuseStep 524627 = 786941) B786941
theorem B557651 : Blo 231814 557651 := bstep (se 1 (by rfl) ⟨418238, by rfl⟩ : syracuseStep 557651 = 836477) B836477
theorem B295807 : Blo 231814 295807 := bstep (se 1 (by rfl) ⟨221855, by rfl⟩ : syracuseStep 295807 = 443711) B443711
theorem B263263 : Blo 231814 263263 := bstep (se 1 (by rfl) ⟨197447, by rfl⟩ : syracuseStep 263263 = 394895) B394895
theorem B885887 : Blo 231814 885887 := bstep (se 1 (by rfl) ⟨664415, by rfl⟩ : syracuseStep 885887 = 1328831) B1328831
theorem B1115473 : Blo 231814 1115473 := bstep (se 2 (by rfl) ⟨418302, by rfl⟩ : syracuseStep 1115473 = 836605) B836605
theorem B296399 : Blo 231814 296399 := bstep (se 1 (by rfl) ⟨222299, by rfl⟩ : syracuseStep 296399 = 444599) B444599
theorem B787967 : Blo 231814 787967 := bstep (se 1 (by rfl) ⟨590975, by rfl⟩ : syracuseStep 787967 = 1181951) B1181951
theorem B788075 : Blo 231814 788075 := bstep (se 1 (by rfl) ⟨591056, by rfl⟩ : syracuseStep 788075 = 1182113) B1182113
theorem B788669 : Blo 231814 788669 := bstep (se 3 (by rfl) ⟨147875, by rfl⟩ : syracuseStep 788669 = 295751) B295751
theorem B231839 : Blo 231814 231839 := bstep (se 1 (by rfl) ⟨173879, by rfl⟩ : syracuseStep 231839 = 347759) B347759
theorem B231887 : Blo 231814 231887 := bstep (se 1 (by rfl) ⟨173915, by rfl⟩ : syracuseStep 231887 = 347831) B347831
theorem B231919 : Blo 231814 231919 := bstep (se 1 (by rfl) ⟨173939, by rfl⟩ : syracuseStep 231919 = 347879) B347879
theorem B232027 : Blo 231814 232027 := bstep (se 1 (by rfl) ⟨174020, by rfl⟩ : syracuseStep 232027 = 348041) B348041
theorem B395887 : Blo 231814 395887 := bstep (se 1 (by rfl) ⟨296915, by rfl⟩ : syracuseStep 395887 = 593831) B593831
theorem B1805003 : Blo 231814 1805003 := bstep (se 1 (by rfl) ⟨1353752, by rfl⟩ : syracuseStep 1805003 = 2707505) B2707505
theorem B395995 : Blo 231814 395995 := bstep (se 1 (by rfl) ⟨296996, by rfl⟩ : syracuseStep 395995 = 593993) B593993
theorem B232187 : Blo 231814 232187 := bstep (se 1 (by rfl) ⟨174140, by rfl⟩ : syracuseStep 232187 = 348281) B348281
theorem B232191 : Blo 231814 232191 := bstep (se 1 (by rfl) ⟨174143, by rfl⟩ : syracuseStep 232191 = 348287) B348287
theorem B527327 : Blo 231814 527327 := bstep (se 1 (by rfl) ⟨395495, by rfl⟩ : syracuseStep 527327 = 790991) B790991
theorem B527543 : Blo 231814 527543 := bstep (se 1 (by rfl) ⟨395657, by rfl⟩ : syracuseStep 527543 = 791315) B791315
theorem B232751 : Blo 231814 232751 := bstep (se 1 (by rfl) ⟨174563, by rfl⟩ : syracuseStep 232751 = 349127) B349127
theorem B232767 : Blo 231814 232767 := bstep (se 1 (by rfl) ⟨174575, by rfl⟩ : syracuseStep 232767 = 349151) B349151
theorem B888317 : Blo 231814 888317 := bstep (se 3 (by rfl) ⟨166559, by rfl⟩ : syracuseStep 888317 = 333119) B333119
theorem B232991 : Blo 231814 232991 := bstep (se 1 (by rfl) ⟨174743, by rfl⟩ : syracuseStep 232991 = 349487) B349487
theorem B233127 : Blo 231814 233127 := bstep (se 1 (by rfl) ⟨174845, by rfl⟩ : syracuseStep 233127 = 349691) B349691
theorem B233151 : Blo 231814 233151 := bstep (se 1 (by rfl) ⟨174863, by rfl⟩ : syracuseStep 233151 = 349727) B349727
theorem B593639 : Blo 231814 593639 := bstep (se 1 (by rfl) ⟨445229, by rfl⟩ : syracuseStep 593639 = 890459) B890459
theorem B233243 : Blo 231814 233243 := bstep (se 1 (by rfl) ⟨174932, by rfl⟩ : syracuseStep 233243 = 349865) B349865
theorem B233247 : Blo 231814 233247 := bstep (se 1 (by rfl) ⟨174935, by rfl⟩ : syracuseStep 233247 = 349871) B349871
theorem B233327 : Blo 231814 233327 := bstep (se 1 (by rfl) ⟨174995, by rfl⟩ : syracuseStep 233327 = 349991) B349991
theorem B397291 : Blo 231814 397291 := bstep (se 1 (by rfl) ⟨297968, by rfl⟩ : syracuseStep 397291 = 595937) B595937
theorem B233499 : Blo 231814 233499 := bstep (se 1 (by rfl) ⟨175124, by rfl⟩ : syracuseStep 233499 = 350249) B350249
theorem B233519 : Blo 231814 233519 := bstep (se 1 (by rfl) ⟨175139, by rfl⟩ : syracuseStep 233519 = 350279) B350279
theorem B397433 : Blo 231814 397433 := bstep (se 2 (by rfl) ⟨149037, by rfl⟩ : syracuseStep 397433 = 298075) B298075
theorem B790667 : Blo 231814 790667 := bstep (se 1 (by rfl) ⟨593000, by rfl⟩ : syracuseStep 790667 = 1186001) B1186001
theorem B233727 : Blo 231814 233727 := bstep (se 1 (by rfl) ⟨175295, by rfl⟩ : syracuseStep 233727 = 350591) B350591
theorem B233775 : Blo 231814 233775 := bstep (se 1 (by rfl) ⟨175331, by rfl⟩ : syracuseStep 233775 = 350663) B350663
theorem B233919 : Blo 231814 233919 := bstep (se 1 (by rfl) ⟨175439, by rfl⟩ : syracuseStep 233919 = 350879) B350879
theorem B234015 : Blo 231814 234015 := bstep (se 1 (by rfl) ⟨175511, by rfl⟩ : syracuseStep 234015 = 351023) B351023
theorem B24154685 : Blo 231814 24154685 := bstep (se 3 (by rfl) ⟨4529003, by rfl⟩ : syracuseStep 24154685 = 9058007) B9058007
theorem B1938007 : Blo 231814 1938007 := bstep (se 1 (by rfl) ⟨1453505, by rfl⟩ : syracuseStep 1938007 = 2907011) B2907011
theorem B561755 : Blo 231814 561755 := bstep (se 1 (by rfl) ⟨421316, by rfl⟩ : syracuseStep 561755 = 842633) B842633
theorem B234075 : Blo 231814 234075 := bstep (se 1 (by rfl) ⟨175556, by rfl⟩ : syracuseStep 234075 = 351113) B351113
theorem B234095 : Blo 231814 234095 := bstep (se 1 (by rfl) ⟨175571, by rfl⟩ : syracuseStep 234095 = 351143) B351143
theorem B791207 : Blo 231814 791207 := bstep (se 1 (by rfl) ⟨593405, by rfl⟩ : syracuseStep 791207 = 1186811) B1186811
theorem B234215 : Blo 231814 234215 := bstep (se 1 (by rfl) ⟨175661, by rfl⟩ : syracuseStep 234215 = 351323) B351323
theorem B234343 : Blo 231814 234343 := bstep (se 1 (by rfl) ⟨175757, by rfl⟩ : syracuseStep 234343 = 351515) B351515
theorem B791585 : Blo 231814 791585 := bstep (se 2 (by rfl) ⟨296844, by rfl⟩ : syracuseStep 791585 = 593689) B593689
theorem B234655 : Blo 231814 234655 := bstep (se 1 (by rfl) ⟨175991, by rfl⟩ : syracuseStep 234655 = 351983) B351983
theorem B529595 : Blo 231814 529595 := bstep (se 1 (by rfl) ⟨397196, by rfl⟩ : syracuseStep 529595 = 794393) B794393
theorem B529631 : Blo 231814 529631 := bstep (se 1 (by rfl) ⟨397223, by rfl⟩ : syracuseStep 529631 = 794447) B794447
theorem B234779 : Blo 231814 234779 := bstep (se 1 (by rfl) ⟨176084, by rfl⟩ : syracuseStep 234779 = 352169) B352169
theorem B791855 : Blo 231814 791855 := bstep (se 1 (by rfl) ⟨593891, by rfl⟩ : syracuseStep 791855 = 1187783) B1187783
theorem B660793 : Blo 231814 660793 := bstep (se 2 (by rfl) ⟨247797, by rfl⟩ : syracuseStep 660793 = 495595) B495595
theorem B234879 : Blo 231814 234879 := bstep (se 1 (by rfl) ⟨176159, by rfl⟩ : syracuseStep 234879 = 352319) B352319
theorem B529847 : Blo 231814 529847 := bstep (se 1 (by rfl) ⟨397385, by rfl⟩ : syracuseStep 529847 = 794771) B794771
theorem B235035 : Blo 231814 235035 := bstep (se 1 (by rfl) ⟨176276, by rfl⟩ : syracuseStep 235035 = 352553) B352553
theorem B661135 : Blo 231814 661135 := bstep (se 1 (by rfl) ⟨495851, by rfl⟩ : syracuseStep 661135 = 991703) B991703
theorem B235215 : Blo 231814 235215 := bstep (se 1 (by rfl) ⟨176411, by rfl⟩ : syracuseStep 235215 = 352823) B352823
theorem B235455 : Blo 231814 235455 := bstep (se 1 (by rfl) ⟨176591, by rfl⟩ : syracuseStep 235455 = 353183) B353183
theorem B628775 : Blo 231814 628775 := bstep (se 1 (by rfl) ⟨471581, by rfl⟩ : syracuseStep 628775 = 943163) B943163
theorem B235647 : Blo 231814 235647 := bstep (se 1 (by rfl) ⟨176735, by rfl⟩ : syracuseStep 235647 = 353471) B353471
theorem B235743 : Blo 231814 235743 := bstep (se 1 (by rfl) ⟨176807, by rfl⟩ : syracuseStep 235743 = 353615) B353615
theorem B235803 : Blo 231814 235803 := bstep (se 1 (by rfl) ⟨176852, by rfl⟩ : syracuseStep 235803 = 353705) B353705
theorem B891233 : Blo 231814 891233 := bstep (se 2 (by rfl) ⟨334212, by rfl⟩ : syracuseStep 891233 = 668425) B668425
theorem B891263 : Blo 231814 891263 := bstep (se 1 (by rfl) ⟨668447, by rfl⟩ : syracuseStep 891263 = 1336895) B1336895
theorem B596585 : Blo 231814 596585 := bstep (se 2 (by rfl) ⟨223719, by rfl⟩ : syracuseStep 596585 = 447439) B447439
theorem B6724205 : Blo 231814 6724205 := bstep (se 3 (by rfl) ⟨1260788, by rfl⟩ : syracuseStep 6724205 = 2521577) B2521577
theorem B498287 : Blo 231814 498287 := bstep (se 1 (by rfl) ⟨373715, by rfl⟩ : syracuseStep 498287 = 747431) B747431
theorem B891719 : Blo 231814 891719 := bstep (se 1 (by rfl) ⟨668789, by rfl⟩ : syracuseStep 891719 = 1337579) B1337579
theorem B1809317 : Blo 231814 1809317 := bstep (se 4 (by rfl) ⟨169623, by rfl⟩ : syracuseStep 1809317 = 339247) B339247
theorem B498791 : Blo 231814 498791 := bstep (se 1 (by rfl) ⟨374093, by rfl⟩ : syracuseStep 498791 = 748187) B748187
theorem B662867 : Blo 231814 662867 := bstep (se 1 (by rfl) ⟨497150, by rfl⟩ : syracuseStep 662867 = 994301) B994301
theorem B1678745 : Blo 231814 1678745 := bstep (se 2 (by rfl) ⟨629529, by rfl⟩ : syracuseStep 1678745 = 1259059) B1259059
theorem B499115 : Blo 231814 499115 := bstep (se 1 (by rfl) ⟨374336, by rfl⟩ : syracuseStep 499115 = 748673) B748673
theorem B4530167 : Blo 231814 4530167 := bstep (se 1 (by rfl) ⟨3397625, by rfl⟩ : syracuseStep 4530167 = 6795251) B6795251
theorem B1188431 : Blo 231814 1188431 := bstep (se 1 (by rfl) ⟨891323, by rfl⟩ : syracuseStep 1188431 = 1782647) B1782647
theorem B566041 : Blo 231814 566041 := bstep (se 2 (by rfl) ⟨212265, by rfl⟩ : syracuseStep 566041 = 424531) B424531
theorem B795743 : Blo 231814 795743 := bstep (se 1 (by rfl) ⟨596807, by rfl⟩ : syracuseStep 795743 = 1193615) B1193615
theorem B3515557 : Blo 231814 3515557 := bstep (se 4 (by rfl) ⟨329583, by rfl⟩ : syracuseStep 3515557 = 659167) B659167
theorem B271687 : Blo 231814 271687 := bstep (se 1 (by rfl) ⟨203765, by rfl⟩ : syracuseStep 271687 = 407531) B407531
theorem B501473 : Blo 231814 501473 := bstep (se 2 (by rfl) ⟨188052, by rfl⟩ : syracuseStep 501473 = 376105) B376105
theorem B632927 : Blo 231814 632927 := bstep (se 1 (by rfl) ⟨474695, by rfl⟩ : syracuseStep 632927 = 949391) B949391
theorem B4303469 : Blo 231814 4303469 := bstep (se 3 (by rfl) ⟨806900, by rfl⟩ : syracuseStep 4303469 = 1613801) B1613801
theorem B1190537 : Blo 231814 1190537 := bstep (se 2 (by rfl) ⟨446451, by rfl⟩ : syracuseStep 1190537 = 892903) B892903
theorem B4533083 : Blo 231814 4533083 := bstep (se 1 (by rfl) ⟨3399812, by rfl⟩ : syracuseStep 4533083 = 6799625) B6799625
theorem B502895 : Blo 231814 502895 := bstep (se 1 (by rfl) ⟨377171, by rfl⟩ : syracuseStep 502895 = 754343) B754343
theorem B3386555 : Blo 231814 3386555 := bstep (se 1 (by rfl) ⟨2539916, by rfl⟩ : syracuseStep 3386555 = 5079833) B5079833
theorem B1813691 : Blo 231814 1813691 := bstep (se 1 (by rfl) ⟨1360268, by rfl⟩ : syracuseStep 1813691 = 2720537) B2720537
theorem B2404333 : Blo 231814 2404333 := bstep (se 3 (by rfl) ⟨450812, by rfl⟩ : syracuseStep 2404333 = 901625) B901625
theorem B471467 : Blo 231814 471467 := bstep (se 1 (by rfl) ⟨353600, by rfl⟩ : syracuseStep 471467 = 707201) B707201
theorem B569791 : Blo 231814 569791 := bstep (se 1 (by rfl) ⟨427343, by rfl⟩ : syracuseStep 569791 = 854687) B854687
theorem B1323499 : Blo 231814 1323499 := bstep (se 1 (by rfl) ⟨992624, by rfl⟩ : syracuseStep 1323499 = 1985249) B1985249
theorem B1258021 : Blo 231814 1258021 := bstep (se 4 (by rfl) ⟨117939, by rfl⟩ : syracuseStep 1258021 = 235879) B235879
theorem B1192745 : Blo 231814 1192745 := bstep (se 2 (by rfl) ⟨447279, by rfl⟩ : syracuseStep 1192745 = 894559) B894559
theorem B1784105 : Blo 231814 1784105 := bstep (se 2 (by rfl) ⟨669039, by rfl⟩ : syracuseStep 1784105 = 1338079) B1338079
theorem B1685897 : Blo 231814 1685897 := bstep (se 2 (by rfl) ⟨632211, by rfl⟩ : syracuseStep 1685897 = 1264423) B1264423
theorem B1489529 : Blo 231814 1489529 := bstep (se 2 (by rfl) ⟨558573, by rfl⟩ : syracuseStep 1489529 = 1117147) B1117147
theorem B1129085 : Blo 231814 1129085 := bstep (se 3 (by rfl) ⟨211703, by rfl⟩ : syracuseStep 1129085 = 423407) B423407
theorem B1489553 : Blo 231814 1489553 := bstep (se 2 (by rfl) ⟨558582, by rfl⟩ : syracuseStep 1489553 = 1117165) B1117165
theorem B12139307 : Blo 231814 12139307 := bstep (se 1 (by rfl) ⟨9104480, by rfl⟩ : syracuseStep 12139307 = 18208961) B18208961
theorem B5028803 : Blo 231814 5028803 := bstep (se 1 (by rfl) ⟨3771602, by rfl⟩ : syracuseStep 5028803 = 7543205) B7543205
theorem B13581269 : Blo 231814 13581269 := bstep (se 7 (by rfl) ⟨159155, by rfl⟩ : syracuseStep 13581269 = 318311) B318311
theorem B1686587 : Blo 231814 1686587 := bstep (se 1 (by rfl) ⟨1264940, by rfl⟩ : syracuseStep 1686587 = 2529881) B2529881
theorem B2538971 : Blo 231814 2538971 := bstep (se 1 (by rfl) ⟨1904228, by rfl⟩ : syracuseStep 2538971 = 3808457) B3808457
theorem B1785563 : Blo 231814 1785563 := bstep (se 1 (by rfl) ⟨1339172, by rfl⟩ : syracuseStep 1785563 = 2678345) B2678345
theorem B3784967 : Blo 231814 3784967 := bstep (se 1 (by rfl) ⟨2838725, by rfl⟩ : syracuseStep 3784967 = 5677451) B5677451
theorem B1983851 : Blo 231814 1983851 := bstep (se 1 (by rfl) ⟨1487888, by rfl⟩ : syracuseStep 1983851 = 2975777) B2975777
theorem B7161871 : Blo 231814 7161871 := bstep (se 1 (by rfl) ⟨5371403, by rfl⟩ : syracuseStep 7161871 = 10742807) B10742807
theorem B444827 : Blo 231814 444827 := bstep (se 1 (by rfl) ⟨333620, by rfl⟩ : syracuseStep 444827 = 667241) B667241
theorem B1002041 : Blo 231814 1002041 := bstep (se 2 (by rfl) ⟨375765, by rfl⟩ : syracuseStep 1002041 = 751531) B751531
theorem B347867 : Blo 231814 347867 := bstep (se 1 (by rfl) ⟨260900, by rfl⟩ : syracuseStep 347867 = 521801) B521801
theorem B348395 : Blo 231814 348395 := bstep (se 1 (by rfl) ⟨261296, by rfl⟩ : syracuseStep 348395 = 522593) B522593
theorem B348455 : Blo 231814 348455 := bstep (se 1 (by rfl) ⟨261341, by rfl⟩ : syracuseStep 348455 = 522683) B522683
theorem B250651 : Blo 231814 250651 := bstep (se 1 (by rfl) ⟨187988, by rfl⟩ : syracuseStep 250651 = 375977) B375977
theorem B447295 : Blo 231814 447295 := bstep (se 1 (by rfl) ⟨335471, by rfl⟩ : syracuseStep 447295 = 670943) B670943
theorem B349295 : Blo 231814 349295 := bstep (se 1 (by rfl) ⟨261971, by rfl⟩ : syracuseStep 349295 = 523943) B523943
theorem B13685939 : Blo 231814 13685939 := bstep (se 1 (by rfl) ⟨10264454, by rfl⟩ : syracuseStep 13685939 = 20528909) B20528909
theorem B349367 : Blo 231814 349367 := bstep (se 1 (by rfl) ⟨262025, by rfl⟩ : syracuseStep 349367 = 524051) B524051
theorem B349415 : Blo 231814 349415 := bstep (se 1 (by rfl) ⟨262061, by rfl⟩ : syracuseStep 349415 = 524123) B524123
theorem B1004825 : Blo 231814 1004825 := bstep (se 2 (by rfl) ⟨376809, by rfl⟩ : syracuseStep 1004825 = 753619) B753619
theorem B349607 : Blo 231814 349607 := bstep (se 1 (by rfl) ⟨262205, by rfl⟩ : syracuseStep 349607 = 524411) B524411
theorem B4019705 : Blo 231814 4019705 := bstep (se 2 (by rfl) ⟨1507389, by rfl⟩ : syracuseStep 4019705 = 3014779) B3014779
theorem B349787 : Blo 231814 349787 := bstep (se 1 (by rfl) ⟨262340, by rfl⟩ : syracuseStep 349787 = 524681) B524681
theorem B349799 : Blo 231814 349799 := bstep (se 1 (by rfl) ⟨262349, by rfl⟩ : syracuseStep 349799 = 524699) B524699
theorem B1890145 : Blo 231814 1890145 := bstep (se 2 (by rfl) ⟨708804, by rfl⟩ : syracuseStep 1890145 = 1417609) B1417609
theorem B841853 : Blo 231814 841853 := bstep (se 3 (by rfl) ⟨157847, by rfl⟩ : syracuseStep 841853 = 315695) B315695
theorem B1988873 : Blo 231814 1988873 := bstep (se 2 (by rfl) ⟨745827, by rfl⟩ : syracuseStep 1988873 = 1491655) B1491655
theorem B350567 : Blo 231814 350567 := bstep (se 1 (by rfl) ⟨262925, by rfl⟩ : syracuseStep 350567 = 525851) B525851
theorem B350633 : Blo 231814 350633 := bstep (se 2 (by rfl) ⟨131487, by rfl⟩ : syracuseStep 350633 = 262975) B262975
theorem B1333705 : Blo 231814 1333705 := bstep (se 2 (by rfl) ⟨500139, by rfl⟩ : syracuseStep 1333705 = 1000279) B1000279
theorem B2646269 : Blo 231814 2646269 := bstep (se 3 (by rfl) ⟨496175, by rfl⟩ : syracuseStep 2646269 = 992351) B992351
theorem B353051 : Blo 231814 353051 := bstep (se 1 (by rfl) ⟨264788, by rfl⟩ : syracuseStep 353051 = 529577) B529577
theorem B353321 : Blo 231814 353321 := bstep (se 2 (by rfl) ⟨132495, by rfl⟩ : syracuseStep 353321 = 264991) B264991
theorem B2254013 : Blo 231814 2254013 := bstep (se 3 (by rfl) ⟨422627, by rfl⟩ : syracuseStep 2254013 = 845255) B845255
theorem B1008875 : Blo 231814 1008875 := bstep (se 1 (by rfl) ⟨756656, by rfl⟩ : syracuseStep 1008875 = 1513313) B1513313
theorem B1369979 : Blo 231814 1369979 := bstep (se 1 (by rfl) ⟨1027484, by rfl⟩ : syracuseStep 1369979 = 2054969) B2054969
theorem B6056045 : Blo 231814 6056045 := bstep (se 3 (by rfl) ⟨1135508, by rfl⟩ : syracuseStep 6056045 = 2271017) B2271017
theorem B1174013 : Blo 231814 1174013 := bstep (se 3 (by rfl) ⟨220127, by rfl⟩ : syracuseStep 1174013 = 440255) B440255
theorem B1174175 : Blo 231814 1174175 := bstep (se 1 (by rfl) ⟨880631, by rfl⟩ : syracuseStep 1174175 = 1761263) B1761263
theorem B2845925 : Blo 231814 2845925 := bstep (se 4 (by rfl) ⟨266805, by rfl⟩ : syracuseStep 2845925 = 533611) B533611
theorem B1699163 : Blo 231814 1699163 := bstep (se 1 (by rfl) ⟨1274372, by rfl⟩ : syracuseStep 1699163 = 2548745) B2548745
theorem B847361 : Blo 231814 847361 := bstep (se 2 (by rfl) ⟨317760, by rfl⟩ : syracuseStep 847361 = 635521) B635521
theorem B783215 : Blo 231814 783215 := bstep (se 1 (by rfl) ⟨587411, by rfl⟩ : syracuseStep 783215 = 1174823) B1174823
theorem B849005 : Blo 231814 849005 := bstep (se 3 (by rfl) ⟨159188, by rfl⟩ : syracuseStep 849005 = 318377) B318377
theorem B1995911 : Blo 231814 1995911 := bstep (se 1 (by rfl) ⟨1496933, by rfl⟩ : syracuseStep 1995911 = 2993867) B2993867
theorem B7632083 : Blo 231814 7632083 := bstep (se 1 (by rfl) ⟨5724062, by rfl⟩ : syracuseStep 7632083 = 11448125) B11448125
theorem B521711 : Blo 231814 521711 := bstep (se 1 (by rfl) ⟨391283, by rfl⟩ : syracuseStep 521711 = 782567) B782567
theorem B783863 : Blo 231814 783863 := bstep (se 1 (by rfl) ⟨587897, by rfl⟩ : syracuseStep 783863 = 1175795) B1175795
theorem B849695 : Blo 231814 849695 := bstep (se 1 (by rfl) ⟨637271, by rfl⟩ : syracuseStep 849695 = 1274543) B1274543
theorem B16447607 : Blo 231814 16447607 := bstep (se 1 (by rfl) ⟨12335705, by rfl⟩ : syracuseStep 16447607 = 24671411) B24671411
theorem B784943 : Blo 231814 784943 := bstep (se 1 (by rfl) ⟨588707, by rfl⟩ : syracuseStep 784943 = 1177415) B1177415
theorem B260815 : Blo 231814 260815 := bstep (se 1 (by rfl) ⟨195611, by rfl⟩ : syracuseStep 260815 = 391223) B391223
theorem B785159 : Blo 231814 785159 := bstep (se 1 (by rfl) ⟨588869, by rfl⟩ : syracuseStep 785159 = 1177739) B1177739
theorem B3242911 : Blo 231814 3242911 := bstep (se 1 (by rfl) ⟨2432183, by rfl⟩ : syracuseStep 3242911 = 4864367) B4864367
theorem B1899487 : Blo 231814 1899487 := bstep (se 1 (by rfl) ⟨1424615, by rfl⟩ : syracuseStep 1899487 = 2849231) B2849231
theorem B3931139 : Blo 231814 3931139 := bstep (se 1 (by rfl) ⟨2948354, by rfl⟩ : syracuseStep 3931139 = 5896709) B5896709
theorem B392519 : Blo 231814 392519 := bstep (se 1 (by rfl) ⟨294389, by rfl⟩ : syracuseStep 392519 = 588779) B588779
theorem B261787 : Blo 231814 261787 := bstep (se 1 (by rfl) ⟨196340, by rfl⟩ : syracuseStep 261787 = 392681) B392681
theorem B786239 : Blo 231814 786239 := bstep (se 1 (by rfl) ⟨589679, by rfl⟩ : syracuseStep 786239 = 1179359) B1179359
theorem B2523311 : Blo 231814 2523311 := bstep (se 1 (by rfl) ⟨1892483, by rfl⟩ : syracuseStep 2523311 = 3784967) B3784967
theorem B590591 : Blo 231814 590591 := bstep (se 1 (by rfl) ⟨442943, by rfl⟩ : syracuseStep 590591 = 885887) B885887
theorem B525311 : Blo 231814 525311 := bstep (se 1 (by rfl) ⟨393983, by rfl⟩ : syracuseStep 525311 = 787967) B787967
theorem B754721 : Blo 231814 754721 := bstep (se 2 (by rfl) ⟨283020, by rfl⟩ : syracuseStep 754721 = 566041) B566041
theorem B525383 : Blo 231814 525383 := bstep (se 1 (by rfl) ⟨394037, by rfl⟩ : syracuseStep 525383 = 788075) B788075
theorem B394409 : Blo 231814 394409 := bstep (se 2 (by rfl) ⟨147903, by rfl⟩ : syracuseStep 394409 = 295807) B295807
theorem B525779 : Blo 231814 525779 := bstep (se 1 (by rfl) ⟨394334, by rfl⟩ : syracuseStep 525779 = 788669) B788669
theorem B4687409 : Blo 231814 4687409 := bstep (se 2 (by rfl) ⟨1757778, by rfl⟩ : syracuseStep 4687409 = 3515557) B3515557
theorem B296551 : Blo 231814 296551 := bstep (se 1 (by rfl) ⟨222413, by rfl⟩ : syracuseStep 296551 = 444827) B444827
theorem B362249 : Blo 231814 362249 := bstep (se 2 (by rfl) ⟨135843, by rfl⟩ : syracuseStep 362249 = 271687) B271687
theorem B592211 : Blo 231814 592211 := bstep (se 1 (by rfl) ⟨444158, by rfl⟩ : syracuseStep 592211 = 888317) B888317
theorem B231911 : Blo 231814 231911 := bstep (se 1 (by rfl) ⟨173933, by rfl⟩ : syracuseStep 231911 = 347867) B347867
theorem B395759 : Blo 231814 395759 := bstep (se 1 (by rfl) ⟨296819, by rfl⟩ : syracuseStep 395759 = 593639) B593639
theorem B264955 : Blo 231814 264955 := bstep (se 1 (by rfl) ⟨198716, by rfl⟩ : syracuseStep 264955 = 397433) B397433
theorem B527111 : Blo 231814 527111 := bstep (se 1 (by rfl) ⟨395333, by rfl⟩ : syracuseStep 527111 = 790667) B790667
theorem B232263 : Blo 231814 232263 := bstep (se 1 (by rfl) ⟨174197, by rfl⟩ : syracuseStep 232263 = 348395) B348395
theorem B232303 : Blo 231814 232303 := bstep (se 1 (by rfl) ⟨174227, by rfl⟩ : syracuseStep 232303 = 348455) B348455
theorem B527471 : Blo 231814 527471 := bstep (se 1 (by rfl) ⟨395603, by rfl⟩ : syracuseStep 527471 = 791207) B791207
theorem B527723 : Blo 231814 527723 := bstep (se 1 (by rfl) ⟨395792, by rfl⟩ : syracuseStep 527723 = 791585) B791585
theorem B232863 : Blo 231814 232863 := bstep (se 1 (by rfl) ⟨174647, by rfl⟩ : syracuseStep 232863 = 349295) B349295
theorem B232911 : Blo 231814 232911 := bstep (se 1 (by rfl) ⟨174683, by rfl⟩ : syracuseStep 232911 = 349367) B349367
theorem B527849 : Blo 231814 527849 := bstep (se 2 (by rfl) ⟨197943, by rfl⟩ : syracuseStep 527849 = 395887) B395887
theorem B232943 : Blo 231814 232943 := bstep (se 1 (by rfl) ⟨174707, by rfl⟩ : syracuseStep 232943 = 349415) B349415
theorem B527903 : Blo 231814 527903 := bstep (se 1 (by rfl) ⟨395927, by rfl⟩ : syracuseStep 527903 = 791855) B791855
theorem B233071 : Blo 231814 233071 := bstep (se 1 (by rfl) ⟨174803, by rfl⟩ : syracuseStep 233071 = 349607) B349607
theorem B527993 : Blo 231814 527993 := bstep (se 2 (by rfl) ⟨197997, by rfl⟩ : syracuseStep 527993 = 395995) B395995
theorem B233191 : Blo 231814 233191 := bstep (se 1 (by rfl) ⟨174893, by rfl⟩ : syracuseStep 233191 = 349787) B349787
theorem B233199 : Blo 231814 233199 := bstep (se 1 (by rfl) ⟨174899, by rfl⟩ : syracuseStep 233199 = 349799) B349799
theorem B790397 : Blo 231814 790397 := bstep (se 3 (by rfl) ⟨148199, by rfl⟩ : syracuseStep 790397 = 296399) B296399
theorem B594155 : Blo 231814 594155 := bstep (se 1 (by rfl) ⟨445616, by rfl⟩ : syracuseStep 594155 = 891233) B891233
theorem B233711 : Blo 231814 233711 := bstep (se 1 (by rfl) ⟨175283, by rfl⟩ : syracuseStep 233711 = 350567) B350567
theorem B594175 : Blo 231814 594175 := bstep (se 1 (by rfl) ⟨445631, by rfl⟩ : syracuseStep 594175 = 891263) B891263
theorem B233755 : Blo 231814 233755 := bstep (se 1 (by rfl) ⟨175316, by rfl⟩ : syracuseStep 233755 = 350633) B350633
theorem B397723 : Blo 231814 397723 := bstep (se 1 (by rfl) ⟨298292, by rfl⟩ : syracuseStep 397723 = 596585) B596585
theorem B332191 : Blo 231814 332191 := bstep (se 1 (by rfl) ⟨249143, by rfl⟩ : syracuseStep 332191 = 498287) B498287
theorem B594479 : Blo 231814 594479 := bstep (se 1 (by rfl) ⟨445859, by rfl⟩ : syracuseStep 594479 = 891719) B891719
theorem B332527 : Blo 231814 332527 := bstep (se 1 (by rfl) ⟨249395, by rfl⟩ : syracuseStep 332527 = 498791) B498791
theorem B2265853 : Blo 231814 2265853 := bstep (se 3 (by rfl) ⟨424847, by rfl⟩ : syracuseStep 2265853 = 849695) B849695
theorem B332743 : Blo 231814 332743 := bstep (se 1 (by rfl) ⟨249557, by rfl⟩ : syracuseStep 332743 = 499115) B499115
theorem B529721 : Blo 231814 529721 := bstep (se 2 (by rfl) ⟨198645, by rfl⟩ : syracuseStep 529721 = 397291) B397291
theorem B3020111 : Blo 231814 3020111 := bstep (se 1 (by rfl) ⟨2265083, by rfl⟩ : syracuseStep 3020111 = 4530167) B4530167
theorem B792287 : Blo 231814 792287 := bstep (se 1 (by rfl) ⟨594215, by rfl⟩ : syracuseStep 792287 = 1188431) B1188431
theorem B235367 : Blo 231814 235367 := bstep (se 1 (by rfl) ⟨176525, by rfl⟩ : syracuseStep 235367 = 353051) B353051
theorem B759721 : Blo 231814 759721 := bstep (se 2 (by rfl) ⟨284895, by rfl⟩ : syracuseStep 759721 = 569791) B569791
theorem B235547 : Blo 231814 235547 := bstep (se 1 (by rfl) ⟨176660, by rfl⟩ : syracuseStep 235547 = 353321) B353321
theorem B1677361 : Blo 231814 1677361 := bstep (se 2 (by rfl) ⟨629010, by rfl⟩ : syracuseStep 1677361 = 1258021) B1258021
theorem B530495 : Blo 231814 530495 := bstep (se 1 (by rfl) ⟨397871, by rfl⟩ : syracuseStep 530495 = 795743) B795743
theorem B334201 : Blo 231814 334201 := bstep (se 2 (by rfl) ⟨125325, by rfl⟩ : syracuseStep 334201 = 250651) B250651
theorem B596393 : Blo 231814 596393 := bstep (se 2 (by rfl) ⟨223647, by rfl⟩ : syracuseStep 596393 = 447295) B447295
theorem B334315 : Blo 231814 334315 := bstep (se 1 (by rfl) ⟨250736, by rfl⟩ : syracuseStep 334315 = 501473) B501473
theorem B4037363 : Blo 231814 4037363 := bstep (se 1 (by rfl) ⟨3028022, by rfl⟩ : syracuseStep 4037363 = 6056045) B6056045
theorem B793691 : Blo 231814 793691 := bstep (se 1 (by rfl) ⟨595268, by rfl⟩ : syracuseStep 793691 = 1190537) B1190537
theorem B3022055 : Blo 231814 3022055 := bstep (se 1 (by rfl) ⟨2266541, by rfl⟩ : syracuseStep 3022055 = 4533083) B4533083
theorem B564907 : Blo 231814 564907 := bstep (se 1 (by rfl) ⟨423680, by rfl⟩ : syracuseStep 564907 = 847361) B847361
theorem B4497565 : Blo 231814 4497565 := bstep (se 3 (by rfl) ⟨843293, by rfl⟩ : syracuseStep 4497565 = 1686587) B1686587
theorem B795163 : Blo 231814 795163 := bstep (se 1 (by rfl) ⟨596372, by rfl⟩ : syracuseStep 795163 = 1192745) B1192745
theorem B1778273 : Blo 231814 1778273 := bstep (se 2 (by rfl) ⟨666852, by rfl⟩ : syracuseStep 1778273 = 1333705) B1333705
theorem B566003 : Blo 231814 566003 := bstep (se 1 (by rfl) ⟨424502, by rfl⟩ : syracuseStep 566003 = 849005) B849005
theorem B5088055 : Blo 231814 5088055 := bstep (se 1 (by rfl) ⟨3816041, by rfl⟩ : syracuseStep 5088055 = 7632083) B7632083
theorem B2532649 : Blo 231814 2532649 := bstep (se 2 (by rfl) ⟨949743, by rfl⟩ : syracuseStep 2532649 = 1899487) B1899487
theorem B1189403 : Blo 231814 1189403 := bstep (se 1 (by rfl) ⟨892052, by rfl⟩ : syracuseStep 1189403 = 1784105) B1784105
theorem B1123931 : Blo 231814 1123931 := bstep (se 1 (by rfl) ⟨842948, by rfl⟩ : syracuseStep 1123931 = 1685897) B1685897
theorem B993019 : Blo 231814 993019 := bstep (se 1 (by rfl) ⟨744764, by rfl⟩ : syracuseStep 993019 = 1489529) B1489529
theorem B993035 : Blo 231814 993035 := bstep (se 1 (by rfl) ⟨744776, by rfl⟩ : syracuseStep 993035 = 1489553) B1489553
theorem B3352535 : Blo 231814 3352535 := bstep (se 1 (by rfl) ⟨2514401, by rfl⟩ : syracuseStep 3352535 = 5028803) B5028803
theorem B9054179 : Blo 231814 9054179 := bstep (se 1 (by rfl) ⟨6790634, by rfl⟩ : syracuseStep 9054179 = 13581269) B13581269
theorem B1190375 : Blo 231814 1190375 := bstep (se 1 (by rfl) ⟨892781, by rfl⟩ : syracuseStep 1190375 = 1785563) B1785563
theorem B1322567 : Blo 231814 1322567 := bstep (se 1 (by rfl) ⟨991925, by rfl⟩ : syracuseStep 1322567 = 1983851) B1983851
theorem B1257245 : Blo 231814 1257245 := bstep (se 3 (by rfl) ⟨235733, by rfl⟩ : syracuseStep 1257245 = 471467) B471467
theorem B1487069 : Blo 231814 1487069 := bstep (se 3 (by rfl) ⟨278825, by rfl⟩ : syracuseStep 1487069 = 557651) B557651
theorem B668027 : Blo 231814 668027 := bstep (se 1 (by rfl) ⟨501020, by rfl⟩ : syracuseStep 668027 = 1002041) B1002041
theorem B1487297 : Blo 231814 1487297 := bstep (se 2 (by rfl) ⟨557736, by rfl⟩ : syracuseStep 1487297 = 1115473) B1115473
theorem B9549161 : Blo 231814 9549161 := bstep (se 2 (by rfl) ⟨3580935, by rfl⟩ : syracuseStep 9549161 = 7161871) B7161871
theorem B16103123 : Blo 231814 16103123 := bstep (se 1 (by rfl) ⟨12077342, by rfl⟩ : syracuseStep 16103123 = 24154685) B24154685
theorem B9123959 : Blo 231814 9123959 := bstep (se 1 (by rfl) ⟨6842969, by rfl⟩ : syracuseStep 9123959 = 13685939) B13685939
theorem B669883 : Blo 231814 669883 := bstep (se 1 (by rfl) ⟨502412, by rfl⟩ : syracuseStep 669883 = 1004825) B1004825
theorem B1325915 : Blo 231814 1325915 := bstep (se 1 (by rfl) ⟨994436, by rfl⟩ : syracuseStep 1325915 = 1988873) B1988873
theorem B441911 : Blo 231814 441911 := bstep (se 1 (by rfl) ⟨331433, by rfl⟩ : syracuseStep 441911 = 662867) B662867
theorem B2244941 : Blo 231814 2244941 := bstep (se 3 (by rfl) ⟨420926, by rfl⟩ : syracuseStep 2244941 = 841853) B841853
theorem B672583 : Blo 231814 672583 := bstep (se 1 (by rfl) ⟨504437, by rfl⟩ : syracuseStep 672583 = 1008875) B1008875
theorem B2868979 : Blo 231814 2868979 := bstep (se 1 (by rfl) ⟨2151734, by rfl⟩ : syracuseStep 2868979 = 4303469) B4303469
theorem B1132775 : Blo 231814 1132775 := bstep (se 1 (by rfl) ⟨849581, by rfl⟩ : syracuseStep 1132775 = 1699163) B1699163
theorem B1330607 : Blo 231814 1330607 := bstep (se 1 (by rfl) ⟨997955, by rfl⟩ : syracuseStep 1330607 = 1995911) B1995911
theorem B347753 : Blo 231814 347753 := bstep (se 2 (by rfl) ⟨130407, by rfl⟩ : syracuseStep 347753 = 260815) B260815
theorem B347807 : Blo 231814 347807 := bstep (se 1 (by rfl) ⟨260855, by rfl⟩ : syracuseStep 347807 = 521711) B521711
theorem B4476653 : Blo 231814 4476653 := bstep (se 3 (by rfl) ⟨839372, by rfl⟩ : syracuseStep 4476653 = 1678745) B1678745
theorem B10965071 : Blo 231814 10965071 := bstep (se 1 (by rfl) ⟨8223803, by rfl⟩ : syracuseStep 10965071 = 16447607) B16447607
theorem B10080773 : Blo 231814 10080773 := bstep (se 4 (by rfl) ⟨945072, by rfl⟩ : syracuseStep 10080773 = 1890145) B1890145
theorem B349049 : Blo 231814 349049 := bstep (se 2 (by rfl) ⟨130893, by rfl⟩ : syracuseStep 349049 = 261787) B261787
theorem B1692647 : Blo 231814 1692647 := bstep (se 1 (by rfl) ⟨1269485, by rfl⟩ : syracuseStep 1692647 = 2538971) B2538971
theorem B2446843 : Blo 231814 2446843 := bstep (se 1 (by rfl) ⟨1835132, by rfl⟩ : syracuseStep 2446843 = 3670265) B3670265
theorem B349751 : Blo 231814 349751 := bstep (se 1 (by rfl) ⟨262313, by rfl⟩ : syracuseStep 349751 = 524627) B524627
theorem B351017 : Blo 231814 351017 := bstep (se 2 (by rfl) ⟨131631, by rfl⟩ : syracuseStep 351017 = 263263) B263263
theorem B1498013 : Blo 231814 1498013 := bstep (se 3 (by rfl) ⟨280877, by rfl⟩ : syracuseStep 1498013 = 561755) B561755
theorem B1203335 : Blo 231814 1203335 := bstep (se 1 (by rfl) ⟨902501, by rfl⟩ : syracuseStep 1203335 = 1805003) B1805003
theorem B351551 : Blo 231814 351551 := bstep (se 1 (by rfl) ⟨263663, by rfl⟩ : syracuseStep 351551 = 527327) B527327
theorem B351695 : Blo 231814 351695 := bstep (se 1 (by rfl) ⟨263771, by rfl⟩ : syracuseStep 351695 = 527543) B527543
theorem B353063 : Blo 231814 353063 := bstep (se 1 (by rfl) ⟨264797, by rfl⟩ : syracuseStep 353063 = 529595) B529595
theorem B353087 : Blo 231814 353087 := bstep (se 1 (by rfl) ⟨264815, by rfl⟩ : syracuseStep 353087 = 529631) B529631
theorem B353231 : Blo 231814 353231 := bstep (se 1 (by rfl) ⟨264923, by rfl⟩ : syracuseStep 353231 = 529847) B529847
theorem B2679803 : Blo 231814 2679803 := bstep (se 1 (by rfl) ⟨2009852, by rfl⟩ : syracuseStep 2679803 = 4019705) B4019705
theorem B419183 : Blo 231814 419183 := bstep (se 1 (by rfl) ⟨314387, by rfl⟩ : syracuseStep 419183 = 628775) B628775
theorem B4482803 : Blo 231814 4482803 := bstep (se 1 (by rfl) ⟨3362102, by rfl⟩ : syracuseStep 4482803 = 6724205) B6724205
theorem B1206211 : Blo 231814 1206211 := bstep (se 1 (by rfl) ⟨904658, by rfl⟩ : syracuseStep 1206211 = 1809317) B1809317
theorem B3205777 : Blo 231814 3205777 := bstep (se 2 (by rfl) ⟨1202166, by rfl⟩ : syracuseStep 3205777 = 2404333) B2404333
theorem B1764179 : Blo 231814 1764179 := bstep (se 1 (by rfl) ⟨1323134, by rfl⟩ : syracuseStep 1764179 = 2646269) B2646269
theorem B1764665 : Blo 231814 1764665 := bstep (se 2 (by rfl) ⟨661749, by rfl⟩ : syracuseStep 1764665 = 1323499) B1323499
theorem B2584009 : Blo 231814 2584009 := bstep (se 2 (by rfl) ⟨969003, by rfl⟩ : syracuseStep 2584009 = 1938007) B1938007
theorem B1502675 : Blo 231814 1502675 := bstep (se 1 (by rfl) ⟨1127006, by rfl⟩ : syracuseStep 1502675 = 2254013) B2254013
theorem B913319 : Blo 231814 913319 := bstep (se 1 (by rfl) ⟨684989, by rfl⟩ : syracuseStep 913319 = 1369979) B1369979
theorem B421951 : Blo 231814 421951 := bstep (se 1 (by rfl) ⟨316463, by rfl⟩ : syracuseStep 421951 = 632927) B632927
theorem B782675 : Blo 231814 782675 := bstep (se 1 (by rfl) ⟨587006, by rfl⟩ : syracuseStep 782675 = 1174013) B1174013
theorem B881057 : Blo 231814 881057 := bstep (se 2 (by rfl) ⟨330396, by rfl⟩ : syracuseStep 881057 = 660793) B660793
theorem B782783 : Blo 231814 782783 := bstep (se 1 (by rfl) ⟨587087, by rfl⟩ : syracuseStep 782783 = 1174175) B1174175
theorem B2257703 : Blo 231814 2257703 := bstep (se 1 (by rfl) ⟨1693277, by rfl⟩ : syracuseStep 2257703 = 3386555) B3386555
theorem B1209127 : Blo 231814 1209127 := bstep (se 1 (by rfl) ⟨906845, by rfl⟩ : syracuseStep 1209127 = 1813691) B1813691
theorem B1897283 : Blo 231814 1897283 := bstep (se 1 (by rfl) ⟨1422962, by rfl⟩ : syracuseStep 1897283 = 2845925) B2845925
theorem B881513 : Blo 231814 881513 := bstep (se 2 (by rfl) ⟨330567, by rfl⟩ : syracuseStep 881513 = 661135) B661135
theorem B1341053 : Blo 231814 1341053 := bstep (se 3 (by rfl) ⟨251447, by rfl⟩ : syracuseStep 1341053 = 502895) B502895
theorem B522143 : Blo 231814 522143 := bstep (se 1 (by rfl) ⟨391607, by rfl⟩ : syracuseStep 522143 = 783215) B783215
theorem B522575 : Blo 231814 522575 := bstep (se 1 (by rfl) ⟨391931, by rfl⟩ : syracuseStep 522575 = 783863) B783863
theorem B4323881 : Blo 231814 4323881 := bstep (se 2 (by rfl) ⟨1621455, by rfl⟩ : syracuseStep 4323881 = 3242911) B3242911
theorem B523295 : Blo 231814 523295 := bstep (se 1 (by rfl) ⟨392471, by rfl⟩ : syracuseStep 523295 = 784943) B784943
theorem B752723 : Blo 231814 752723 := bstep (se 1 (by rfl) ⟨564542, by rfl⟩ : syracuseStep 752723 = 1129085) B1129085
theorem B523439 : Blo 231814 523439 := bstep (se 1 (by rfl) ⟨392579, by rfl⟩ : syracuseStep 523439 = 785159) B785159
theorem B8092871 : Blo 231814 8092871 := bstep (se 1 (by rfl) ⟨6069653, by rfl⟩ : syracuseStep 8092871 = 12139307) B12139307
theorem B2620759 : Blo 231814 2620759 := bstep (se 1 (by rfl) ⟨1965569, by rfl⟩ : syracuseStep 2620759 = 3931139) B3931139
theorem B261679 : Blo 231814 261679 := bstep (se 1 (by rfl) ⟨196259, by rfl⟩ : syracuseStep 261679 = 392519) B392519
theorem B524159 : Blo 231814 524159 := bstep (se 1 (by rfl) ⟨393119, by rfl⟩ : syracuseStep 524159 = 786239) B786239
theorem B5996753 : Blo 231814 5996753 := bstep (se 2 (by rfl) ⟨2248782, by rfl⟩ : syracuseStep 5996753 = 4497565) B4497565
theorem B393727 : Blo 231814 393727 := bstep (se 1 (by rfl) ⟨295295, by rfl⟩ : syracuseStep 393727 = 590591) B590591
theorem B262939 : Blo 231814 262939 := bstep (se 1 (by rfl) ⟨197204, by rfl⟩ : syracuseStep 262939 = 394409) B394409
theorem B6784073 : Blo 231814 6784073 := bstep (se 2 (by rfl) ⟨2544027, by rfl⟩ : syracuseStep 6784073 = 5088055) B5088055
theorem B755183 : Blo 231814 755183 := bstep (se 1 (by rfl) ⟨566387, by rfl⟩ : syracuseStep 755183 = 1132775) B1132775
theorem B394807 : Blo 231814 394807 := bstep (se 1 (by rfl) ⟨296105, by rfl⟩ : syracuseStep 394807 = 592211) B592211
theorem B263839 : Blo 231814 263839 := bstep (se 1 (by rfl) ⟨197879, by rfl⟩ : syracuseStep 263839 = 395759) B395759
theorem B3376865 : Blo 231814 3376865 := bstep (se 2 (by rfl) ⟨1266324, by rfl⟩ : syracuseStep 3376865 = 2532649) B2532649
theorem B395401 : Blo 231814 395401 := bstep (se 2 (by rfl) ⟨148275, by rfl⟩ : syracuseStep 395401 = 296551) B296551
theorem B887071 : Blo 231814 887071 := bstep (se 1 (by rfl) ⟨665303, by rfl⟩ : syracuseStep 887071 = 1330607) B1330607
theorem B231835 : Blo 231814 231835 := bstep (se 1 (by rfl) ⟨173876, by rfl⟩ : syracuseStep 231835 = 347753) B347753
theorem B231871 : Blo 231814 231871 := bstep (se 1 (by rfl) ⟨173903, by rfl⟩ : syracuseStep 231871 = 347807) B347807
theorem B2984435 : Blo 231814 2984435 := bstep (se 1 (by rfl) ⟨2238326, by rfl⟩ : syracuseStep 2984435 = 4476653) B4476653
theorem B526931 : Blo 231814 526931 := bstep (se 1 (by rfl) ⟨395198, by rfl⟩ : syracuseStep 526931 = 790397) B790397
theorem B1608281 : Blo 231814 1608281 := bstep (se 2 (by rfl) ⟨603105, by rfl⟩ : syracuseStep 1608281 = 1206211) B1206211
theorem B7310047 : Blo 231814 7310047 := bstep (se 1 (by rfl) ⟨5482535, by rfl⟩ : syracuseStep 7310047 = 10965071) B10965071
theorem B396103 : Blo 231814 396103 := bstep (se 1 (by rfl) ⟨297077, by rfl⟩ : syracuseStep 396103 = 594155) B594155
theorem B6720515 : Blo 231814 6720515 := bstep (se 1 (by rfl) ⟨5040386, by rfl⟩ : syracuseStep 6720515 = 10080773) B10080773
theorem B396319 : Blo 231814 396319 := bstep (se 1 (by rfl) ⟨297239, by rfl⟩ : syracuseStep 396319 = 594479) B594479
theorem B232699 : Blo 231814 232699 := bstep (se 1 (by rfl) ⟨174524, by rfl⟩ : syracuseStep 232699 = 349049) B349049
theorem B233167 : Blo 231814 233167 := bstep (se 1 (by rfl) ⟨174875, by rfl⟩ : syracuseStep 233167 = 349751) B349751
theorem B528191 : Blo 231814 528191 := bstep (se 1 (by rfl) ⟨396143, by rfl⟩ : syracuseStep 528191 = 792287) B792287
theorem B397595 : Blo 231814 397595 := bstep (se 1 (by rfl) ⟨298196, by rfl⟩ : syracuseStep 397595 = 596393) B596393
theorem B2691575 : Blo 231814 2691575 := bstep (se 1 (by rfl) ⟨2018681, by rfl⟩ : syracuseStep 2691575 = 4037363) B4037363
theorem B234011 : Blo 231814 234011 := bstep (se 1 (by rfl) ⟨175508, by rfl⟩ : syracuseStep 234011 = 351017) B351017
theorem B3445345 : Blo 231814 3445345 := bstep (se 2 (by rfl) ⟨1292004, by rfl⟩ : syracuseStep 3445345 = 2584009) B2584009
theorem B529127 : Blo 231814 529127 := bstep (se 1 (by rfl) ⟨396845, by rfl⟩ : syracuseStep 529127 = 793691) B793691
theorem B234367 : Blo 231814 234367 := bstep (se 1 (by rfl) ⟨175775, by rfl⟩ : syracuseStep 234367 = 351551) B351551
theorem B234463 : Blo 231814 234463 := bstep (se 1 (by rfl) ⟨175847, by rfl⟩ : syracuseStep 234463 = 351695) B351695
theorem B562601 : Blo 231814 562601 := bstep (se 2 (by rfl) ⟨210975, by rfl⟩ : syracuseStep 562601 = 421951) B421951
theorem B792233 : Blo 231814 792233 := bstep (se 2 (by rfl) ⟨297087, by rfl⟩ : syracuseStep 792233 = 594175) B594175
theorem B1185515 : Blo 231814 1185515 := bstep (se 1 (by rfl) ⟨889136, by rfl⟩ : syracuseStep 1185515 = 1778273) B1778273
theorem B235375 : Blo 231814 235375 := bstep (se 1 (by rfl) ⟨176531, by rfl⟩ : syracuseStep 235375 = 353063) B353063
theorem B530297 : Blo 231814 530297 := bstep (se 2 (by rfl) ⟨198861, by rfl⟩ : syracuseStep 530297 = 397723) B397723
theorem B235391 : Blo 231814 235391 := bstep (se 1 (by rfl) ⟨176543, by rfl⟩ : syracuseStep 235391 = 353087) B353087
theorem B235487 : Blo 231814 235487 := bstep (se 1 (by rfl) ⟨176615, by rfl⟩ : syracuseStep 235487 = 353231) B353231
theorem B3021137 : Blo 231814 3021137 := bstep (se 2 (by rfl) ⟨1132926, by rfl⟩ : syracuseStep 3021137 = 2265853) B2265853
theorem B792935 : Blo 231814 792935 := bstep (se 1 (by rfl) ⟨594701, by rfl⟩ : syracuseStep 792935 = 1189403) B1189403
theorem B1612169 : Blo 231814 1612169 := bstep (se 2 (by rfl) ⟨604563, by rfl⟩ : syracuseStep 1612169 = 1209127) B1209127
theorem B2988535 : Blo 231814 2988535 := bstep (se 1 (by rfl) ⟨2241401, by rfl⟩ : syracuseStep 2988535 = 4482803) B4482803
theorem B662023 : Blo 231814 662023 := bstep (se 1 (by rfl) ⟨496517, by rfl⟩ : syracuseStep 662023 = 993035) B993035
theorem B2235023 : Blo 231814 2235023 := bstep (se 1 (by rfl) ⟨1676267, by rfl⟩ : syracuseStep 2235023 = 3352535) B3352535
theorem B6036119 : Blo 231814 6036119 := bstep (se 1 (by rfl) ⟨4527089, by rfl⟩ : syracuseStep 6036119 = 9054179) B9054179
theorem B793583 : Blo 231814 793583 := bstep (se 1 (by rfl) ⟨595187, by rfl⟩ : syracuseStep 793583 = 1190375) B1190375
theorem B2236481 : Blo 231814 2236481 := bstep (se 2 (by rfl) ⟨838680, by rfl⟩ : syracuseStep 2236481 = 1677361) B1677361
theorem B991379 : Blo 231814 991379 := bstep (se 1 (by rfl) ⟨743534, by rfl⟩ : syracuseStep 991379 = 1487069) B1487069
theorem B893177 : Blo 231814 893177 := bstep (se 2 (by rfl) ⟨334941, by rfl⟩ : syracuseStep 893177 = 669883) B669883
theorem B991531 : Blo 231814 991531 := bstep (se 1 (by rfl) ⟨743648, by rfl⟩ : syracuseStep 991531 = 1487297) B1487297
theorem B6366107 : Blo 231814 6366107 := bstep (se 1 (by rfl) ⟨4774580, by rfl⟩ : syracuseStep 6366107 = 9549161) B9549161
theorem B894035 : Blo 231814 894035 := bstep (se 1 (by rfl) ⟨670526, by rfl⟩ : syracuseStep 894035 = 1341053) B1341053
theorem B501815 : Blo 231814 501815 := bstep (se 1 (by rfl) ⟨376361, by rfl⟩ : syracuseStep 501815 = 752723) B752723
theorem B1682207 : Blo 231814 1682207 := bstep (se 1 (by rfl) ⟨1261655, by rfl⟩ : syracuseStep 1682207 = 2523311) B2523311
theorem B503147 : Blo 231814 503147 := bstep (se 1 (by rfl) ⟨377360, by rfl⟩ : syracuseStep 503147 = 754721) B754721
theorem B1060217 : Blo 231814 1060217 := bstep (se 2 (by rfl) ⟨397581, by rfl⟩ : syracuseStep 1060217 = 795163) B795163
theorem B3124939 : Blo 231814 3124939 := bstep (se 1 (by rfl) ⟨2343704, by rfl⟩ : syracuseStep 3124939 = 4687409) B4687409
theorem B896777 : Blo 231814 896777 := bstep (se 2 (by rfl) ⟨336291, by rfl⟩ : syracuseStep 896777 = 672583) B672583
theorem B241499 : Blo 231814 241499 := bstep (se 1 (by rfl) ⟨181124, by rfl⟩ : syracuseStep 241499 = 362249) B362249
theorem B5059421 : Blo 231814 5059421 := bstep (se 3 (by rfl) ⟨948641, by rfl⟩ : syracuseStep 5059421 = 1897283) B1897283
theorem B1324025 : Blo 231814 1324025 := bstep (se 2 (by rfl) ⟨496509, by rfl⟩ : syracuseStep 1324025 = 993019) B993019
theorem B1128431 : Blo 231814 1128431 := bstep (se 1 (by rfl) ⟨846323, by rfl⟩ : syracuseStep 1128431 = 1692647) B1692647
theorem B4274369 : Blo 231814 4274369 := bstep (se 2 (by rfl) ⟨1602888, by rfl⟩ : syracuseStep 4274369 = 3205777) B3205777
theorem B2013407 : Blo 231814 2013407 := bstep (se 1 (by rfl) ⟨1510055, by rfl⟩ : syracuseStep 2013407 = 3020111) B3020111
theorem B998675 : Blo 231814 998675 := bstep (se 1 (by rfl) ⟨749006, by rfl⟩ : syracuseStep 998675 = 1498013) B1498013
theorem B802223 : Blo 231814 802223 := bstep (se 1 (by rfl) ⟨601667, by rfl⟩ : syracuseStep 802223 = 1203335) B1203335
theorem B2014703 : Blo 231814 2014703 := bstep (se 1 (by rfl) ⟨1511027, by rfl⟩ : syracuseStep 2014703 = 3022055) B3022055
theorem B24330557 : Blo 231814 24330557 := bstep (se 3 (by rfl) ⟨4561979, by rfl⟩ : syracuseStep 24330557 = 9123959) B9123959
theorem B377335 : Blo 231814 377335 := bstep (se 1 (by rfl) ⟨283001, by rfl⟩ : syracuseStep 377335 = 566003) B566003
theorem B442921 : Blo 231814 442921 := bstep (se 2 (by rfl) ⟨166095, by rfl⟩ : syracuseStep 442921 = 332191) B332191
theorem B1786535 : Blo 231814 1786535 := bstep (se 1 (by rfl) ⟨1339901, by rfl⟩ : syracuseStep 1786535 = 2679803) B2679803
theorem B279455 : Blo 231814 279455 := bstep (se 1 (by rfl) ⟨209591, by rfl⟩ : syracuseStep 279455 = 419183) B419183
theorem B443369 : Blo 231814 443369 := bstep (se 2 (by rfl) ⟨166263, by rfl⟩ : syracuseStep 443369 = 332527) B332527
theorem B443657 : Blo 231814 443657 := bstep (se 2 (by rfl) ⟨166371, by rfl⟩ : syracuseStep 443657 = 332743) B332743
theorem B3262457 : Blo 231814 3262457 := bstep (se 2 (by rfl) ⟨1223421, by rfl⟩ : syracuseStep 3262457 = 2446843) B2446843
theorem B1001783 : Blo 231814 1001783 := bstep (se 1 (by rfl) ⟨751337, by rfl⟩ : syracuseStep 1001783 = 1502675) B1502675
theorem B838163 : Blo 231814 838163 := bstep (se 1 (by rfl) ⟨628622, by rfl⟩ : syracuseStep 838163 = 1257245) B1257245
theorem B608879 : Blo 231814 608879 := bstep (se 1 (by rfl) ⟨456659, by rfl⟩ : syracuseStep 608879 = 913319) B913319
theorem B445351 : Blo 231814 445351 := bstep (se 1 (by rfl) ⟨334013, by rfl⟩ : syracuseStep 445351 = 668027) B668027
theorem B445601 : Blo 231814 445601 := bstep (se 2 (by rfl) ⟨167100, by rfl⟩ : syracuseStep 445601 = 334201) B334201
theorem B445753 : Blo 231814 445753 := bstep (se 2 (by rfl) ⟨167157, by rfl⟩ : syracuseStep 445753 = 334315) B334315
theorem B10735415 : Blo 231814 10735415 := bstep (se 1 (by rfl) ⟨8051561, by rfl⟩ : syracuseStep 10735415 = 16103123) B16103123
theorem B348095 : Blo 231814 348095 := bstep (se 1 (by rfl) ⟨261071, by rfl⟩ : syracuseStep 348095 = 522143) B522143
theorem B348383 : Blo 231814 348383 := bstep (se 1 (by rfl) ⟨261287, by rfl⟩ : syracuseStep 348383 = 522575) B522575
theorem B3494345 : Blo 231814 3494345 := bstep (se 2 (by rfl) ⟨1310379, by rfl⟩ : syracuseStep 3494345 = 2620759) B2620759
theorem B348863 : Blo 231814 348863 := bstep (se 1 (by rfl) ⟨261647, by rfl⟩ : syracuseStep 348863 = 523295) B523295
theorem B348905 : Blo 231814 348905 := bstep (se 2 (by rfl) ⟨130839, by rfl⟩ : syracuseStep 348905 = 261679) B261679
theorem B348959 : Blo 231814 348959 := bstep (se 1 (by rfl) ⟨261719, by rfl⟩ : syracuseStep 348959 = 523439) B523439
theorem B5395247 : Blo 231814 5395247 := bstep (se 1 (by rfl) ⟨4046435, by rfl⟩ : syracuseStep 5395247 = 8092871) B8092871
theorem B349439 : Blo 231814 349439 := bstep (se 1 (by rfl) ⟨262079, by rfl⟩ : syracuseStep 349439 = 524159) B524159
theorem B1496627 : Blo 231814 1496627 := bstep (se 1 (by rfl) ⟨1122470, by rfl⟩ : syracuseStep 1496627 = 2244941) B2244941
theorem B350207 : Blo 231814 350207 := bstep (se 1 (by rfl) ⟨262655, by rfl⟩ : syracuseStep 350207 = 525311) B525311
theorem B350255 : Blo 231814 350255 := bstep (se 1 (by rfl) ⟨262691, by rfl⟩ : syracuseStep 350255 = 525383) B525383
theorem B350519 : Blo 231814 350519 := bstep (se 1 (by rfl) ⟨262889, by rfl⟩ : syracuseStep 350519 = 525779) B525779
theorem B351407 : Blo 231814 351407 := bstep (se 1 (by rfl) ⟨263555, by rfl⟩ : syracuseStep 351407 = 527111) B527111
theorem B351647 : Blo 231814 351647 := bstep (se 1 (by rfl) ⟨263735, by rfl⟩ : syracuseStep 351647 = 527471) B527471
theorem B351815 : Blo 231814 351815 := bstep (se 1 (by rfl) ⟨263861, by rfl⟩ : syracuseStep 351815 = 527723) B527723
theorem B3825305 : Blo 231814 3825305 := bstep (se 2 (by rfl) ⟨1434489, by rfl⟩ : syracuseStep 3825305 = 2868979) B2868979
theorem B351899 : Blo 231814 351899 := bstep (se 1 (by rfl) ⟨263924, by rfl⟩ : syracuseStep 351899 = 527849) B527849
theorem B351935 : Blo 231814 351935 := bstep (se 1 (by rfl) ⟨263951, by rfl⟩ : syracuseStep 351935 = 527903) B527903
theorem B351995 : Blo 231814 351995 := bstep (se 1 (by rfl) ⟨263996, by rfl⟩ : syracuseStep 351995 = 527993) B527993
theorem B353147 : Blo 231814 353147 := bstep (se 1 (by rfl) ⟨264860, by rfl⟩ : syracuseStep 353147 = 529721) B529721
theorem B353273 : Blo 231814 353273 := bstep (se 2 (by rfl) ⟨132477, by rfl⟩ : syracuseStep 353273 = 264955) B264955
theorem B353663 : Blo 231814 353663 := bstep (se 1 (by rfl) ⟨265247, by rfl⟩ : syracuseStep 353663 = 530495) B530495
theorem B749287 : Blo 231814 749287 := bstep (se 1 (by rfl) ⟨561965, by rfl⟩ : syracuseStep 749287 = 1123931) B1123931
theorem B1176119 : Blo 231814 1176119 := bstep (se 1 (by rfl) ⟨882089, by rfl⟩ : syracuseStep 1176119 = 1764179) B1764179
theorem B1176443 : Blo 231814 1176443 := bstep (se 1 (by rfl) ⟨882332, by rfl⟩ : syracuseStep 1176443 = 1764665) B1764665
theorem B881711 : Blo 231814 881711 := bstep (se 1 (by rfl) ⟨661283, by rfl⟩ : syracuseStep 881711 = 1322567) B1322567
theorem B1012961 : Blo 231814 1012961 := bstep (se 2 (by rfl) ⟨379860, by rfl⟩ : syracuseStep 1012961 = 759721) B759721
theorem B521783 : Blo 231814 521783 := bstep (se 1 (by rfl) ⟨391337, by rfl⟩ : syracuseStep 521783 = 782675) B782675
theorem B587371 : Blo 231814 587371 := bstep (se 1 (by rfl) ⟨440528, by rfl⟩ : syracuseStep 587371 = 881057) B881057
theorem B521855 : Blo 231814 521855 := bstep (se 1 (by rfl) ⟨391391, by rfl⟩ : syracuseStep 521855 = 782783) B782783
theorem B1505135 : Blo 231814 1505135 := bstep (se 1 (by rfl) ⟨1128851, by rfl⟩ : syracuseStep 1505135 = 2257703) B2257703
theorem B587675 : Blo 231814 587675 := bstep (se 1 (by rfl) ⟨440756, by rfl⟩ : syracuseStep 587675 = 881513) B881513
theorem B2882587 : Blo 231814 2882587 := bstep (se 1 (by rfl) ⟨2161940, by rfl⟩ : syracuseStep 2882587 = 4323881) B4323881
theorem B883943 : Blo 231814 883943 := bstep (se 1 (by rfl) ⟨662957, by rfl⟩ : syracuseStep 883943 = 1325915) B1325915
theorem B753209 : Blo 231814 753209 := bstep (se 2 (by rfl) ⟨282453, by rfl⟩ : syracuseStep 753209 = 564907) B564907
theorem B294607 : Blo 231814 294607 := bstep (se 1 (by rfl) ⟨220955, by rfl⟩ : syracuseStep 294607 = 441911) B441911
theorem B3997835 : Blo 231814 3997835 := bstep (se 1 (by rfl) ⟨2998376, by rfl⟩ : syracuseStep 3997835 = 5996753) B5996753
theorem B16220371 : Blo 231814 16220371 := bstep (se 1 (by rfl) ⟨12165278, by rfl⟩ : syracuseStep 16220371 = 24330557) B24330557
theorem B295579 : Blo 231814 295579 := bstep (se 1 (by rfl) ⟨221684, by rfl⟩ : syracuseStep 295579 = 443369) B443369
theorem B524969 : Blo 231814 524969 := bstep (se 2 (by rfl) ⟨196863, by rfl⟩ : syracuseStep 524969 = 393727) B393727
theorem B4522715 : Blo 231814 4522715 := bstep (se 1 (by rfl) ⟨3392036, by rfl⟩ : syracuseStep 4522715 = 6784073) B6784073
theorem B590561 : Blo 231814 590561 := bstep (se 2 (by rfl) ⟨221460, by rfl⟩ : syracuseStep 590561 = 442921) B442921
theorem B558775 : Blo 231814 558775 := bstep (se 1 (by rfl) ⟨419081, by rfl⟩ : syracuseStep 558775 = 838163) B838163
theorem B526409 : Blo 231814 526409 := bstep (se 2 (by rfl) ⟨197403, by rfl⟩ : syracuseStep 526409 = 394807) B394807
theorem B232063 : Blo 231814 232063 := bstep (se 1 (by rfl) ⟨174047, by rfl⟩ : syracuseStep 232063 = 348095) B348095
theorem B232255 : Blo 231814 232255 := bstep (se 1 (by rfl) ⟨174191, by rfl⟩ : syracuseStep 232255 = 348383) B348383
theorem B527201 : Blo 231814 527201 := bstep (se 2 (by rfl) ⟨197700, by rfl⟩ : syracuseStep 527201 = 395401) B395401
theorem B265063 : Blo 231814 265063 := bstep (se 1 (by rfl) ⟨198797, by rfl⟩ : syracuseStep 265063 = 397595) B397595
theorem B1182761 : Blo 231814 1182761 := bstep (se 2 (by rfl) ⟨443535, by rfl⟩ : syracuseStep 1182761 = 887071) B887071
theorem B232575 : Blo 231814 232575 := bstep (se 1 (by rfl) ⟨174431, by rfl⟩ : syracuseStep 232575 = 348863) B348863
theorem B232603 : Blo 231814 232603 := bstep (se 1 (by rfl) ⟨174452, by rfl⟩ : syracuseStep 232603 = 348905) B348905
theorem B232639 : Blo 231814 232639 := bstep (se 1 (by rfl) ⟨174479, by rfl⟩ : syracuseStep 232639 = 348959) B348959
theorem B1183085 : Blo 231814 1183085 := bstep (se 3 (by rfl) ⟨221828, by rfl⟩ : syracuseStep 1183085 = 443657) B443657
theorem B232959 : Blo 231814 232959 := bstep (se 1 (by rfl) ⟨174719, by rfl⟩ : syracuseStep 232959 = 349439) B349439
theorem B528137 : Blo 231814 528137 := bstep (se 2 (by rfl) ⟨198051, by rfl⟩ : syracuseStep 528137 = 396103) B396103
theorem B528155 : Blo 231814 528155 := bstep (se 1 (by rfl) ⟨396116, by rfl⟩ : syracuseStep 528155 = 792233) B792233
theorem B790343 : Blo 231814 790343 := bstep (se 1 (by rfl) ⟨592757, by rfl⟩ : syracuseStep 790343 = 1185515) B1185515
theorem B593801 : Blo 231814 593801 := bstep (se 2 (by rfl) ⟨222675, by rfl⟩ : syracuseStep 593801 = 445351) B445351
theorem B233471 : Blo 231814 233471 := bstep (se 1 (by rfl) ⟨175103, by rfl⟩ : syracuseStep 233471 = 350207) B350207
theorem B233503 : Blo 231814 233503 := bstep (se 1 (by rfl) ⟨175127, by rfl⟩ : syracuseStep 233503 = 350255) B350255
theorem B528425 : Blo 231814 528425 := bstep (se 2 (by rfl) ⟨198159, by rfl⟩ : syracuseStep 528425 = 396319) B396319
theorem B233679 : Blo 231814 233679 := bstep (se 1 (by rfl) ⟨175259, by rfl⟩ : syracuseStep 233679 = 350519) B350519
theorem B528623 : Blo 231814 528623 := bstep (se 1 (by rfl) ⟨396467, by rfl⟩ : syracuseStep 528623 = 792935) B792935
theorem B594337 : Blo 231814 594337 := bstep (se 2 (by rfl) ⟨222876, by rfl⟩ : syracuseStep 594337 = 445753) B445753
theorem B529055 : Blo 231814 529055 := bstep (se 1 (by rfl) ⟨396791, by rfl⟩ : syracuseStep 529055 = 793583) B793583
theorem B234271 : Blo 231814 234271 := bstep (se 1 (by rfl) ⟨175703, by rfl⟩ : syracuseStep 234271 = 351407) B351407
theorem B4166585 : Blo 231814 4166585 := bstep (se 2 (by rfl) ⟨1562469, by rfl⟩ : syracuseStep 4166585 = 3124939) B3124939
theorem B234431 : Blo 231814 234431 := bstep (se 1 (by rfl) ⟨175823, by rfl⟩ : syracuseStep 234431 = 351647) B351647
theorem B234543 : Blo 231814 234543 := bstep (se 1 (by rfl) ⟨175907, by rfl⟩ : syracuseStep 234543 = 351815) B351815
theorem B234599 : Blo 231814 234599 := bstep (se 1 (by rfl) ⟨175949, by rfl⟩ : syracuseStep 234599 = 351899) B351899
theorem B234623 : Blo 231814 234623 := bstep (se 1 (by rfl) ⟨175967, by rfl⟩ : syracuseStep 234623 = 351935) B351935
theorem B234663 : Blo 231814 234663 := bstep (se 1 (by rfl) ⟨175997, by rfl⟩ : syracuseStep 234663 = 351995) B351995
theorem B660919 : Blo 231814 660919 := bstep (se 1 (by rfl) ⟨495689, by rfl⟩ : syracuseStep 660919 = 991379) B991379
theorem B595451 : Blo 231814 595451 := bstep (se 1 (by rfl) ⟨446588, by rfl⟩ : syracuseStep 595451 = 893177) B893177
theorem B235431 : Blo 231814 235431 := bstep (se 1 (by rfl) ⟨176573, by rfl⟩ : syracuseStep 235431 = 353147) B353147
theorem B235515 : Blo 231814 235515 := bstep (se 1 (by rfl) ⟨176636, by rfl⟩ : syracuseStep 235515 = 353273) B353273
theorem B4593793 : Blo 231814 4593793 := bstep (se 2 (by rfl) ⟨1722672, by rfl⟩ : syracuseStep 4593793 = 3445345) B3445345
theorem B235775 : Blo 231814 235775 := bstep (se 1 (by rfl) ⟨176831, by rfl⟩ : syracuseStep 235775 = 353663) B353663
theorem B334543 : Blo 231814 334543 := bstep (se 1 (by rfl) ⟨250907, by rfl⟩ : syracuseStep 334543 = 501815) B501815
theorem B1121471 : Blo 231814 1121471 := bstep (se 1 (by rfl) ⟨841103, by rfl⟩ : syracuseStep 1121471 = 1682207) B1682207
theorem B335431 : Blo 231814 335431 := bstep (se 1 (by rfl) ⟨251573, by rfl⟩ : syracuseStep 335431 = 503147) B503147
theorem B597851 : Blo 231814 597851 := bstep (se 1 (by rfl) ⟨448388, by rfl⟩ : syracuseStep 597851 = 896777) B896777
theorem B1188269 : Blo 231814 1188269 := bstep (se 3 (by rfl) ⟨222800, by rfl⟩ : syracuseStep 1188269 = 445601) B445601
theorem B3843449 : Blo 231814 3843449 := bstep (se 2 (by rfl) ⟨1441293, by rfl⟩ : syracuseStep 3843449 = 2882587) B2882587
theorem B665783 : Blo 231814 665783 := bstep (se 1 (by rfl) ⟨499337, by rfl⟩ : syracuseStep 665783 = 998675) B998675
theorem B534815 : Blo 231814 534815 := bstep (se 1 (by rfl) ⟨401111, by rfl⟩ : syracuseStep 534815 = 802223) B802223
theorem B502139 : Blo 231814 502139 := bstep (se 1 (by rfl) ⟨376604, by rfl⟩ : syracuseStep 502139 = 753209) B753209
theorem B1322041 : Blo 231814 1322041 := bstep (se 2 (by rfl) ⟨495765, by rfl⟩ : syracuseStep 1322041 = 991531) B991531
theorem B1191023 : Blo 231814 1191023 := bstep (se 1 (by rfl) ⟨893267, by rfl⟩ : syracuseStep 1191023 = 1786535) B1786535
theorem B503113 : Blo 231814 503113 := bstep (se 2 (by rfl) ⟨188667, by rfl⟩ : syracuseStep 503113 = 377335) B377335
theorem B503455 : Blo 231814 503455 := bstep (se 1 (by rfl) ⟨377591, by rfl⟩ : syracuseStep 503455 = 755183) B755183
theorem B9318253 : Blo 231814 9318253 := bstep (se 3 (by rfl) ⟨1747172, by rfl⟩ : syracuseStep 9318253 = 3494345) B3494345
theorem B667855 : Blo 231814 667855 := bstep (se 1 (by rfl) ⟨500891, by rfl⟩ : syracuseStep 667855 = 1001783) B1001783
theorem B405919 : Blo 231814 405919 := bstep (se 1 (by rfl) ⟨304439, by rfl⟩ : syracuseStep 405919 = 608879) B608879
theorem B7156943 : Blo 231814 7156943 := bstep (se 1 (by rfl) ⟨5367707, by rfl⟩ : syracuseStep 7156943 = 10735415) B10735415
theorem B375067 : Blo 231814 375067 := bstep (se 1 (by rfl) ⟨281300, by rfl⟩ : syracuseStep 375067 = 562601) B562601
theorem B9746729 : Blo 231814 9746729 := bstep (se 2 (by rfl) ⟨3655023, by rfl⟩ : syracuseStep 9746729 = 7310047) B7310047
theorem B997751 : Blo 231814 997751 := bstep (se 1 (by rfl) ⟨748313, by rfl⟩ : syracuseStep 997751 = 1496627) B1496627
theorem B2014091 : Blo 231814 2014091 := bstep (se 1 (by rfl) ⟨1510568, by rfl⟩ : syracuseStep 2014091 = 3021137) B3021137
theorem B1490015 : Blo 231814 1490015 := bstep (se 1 (by rfl) ⟨1117511, by rfl⟩ : syracuseStep 1490015 = 2235023) B2235023
theorem B999049 : Blo 231814 999049 := bstep (se 2 (by rfl) ⟨374643, by rfl⟩ : syracuseStep 999049 = 749287) B749287
theorem B8699885 : Blo 231814 8699885 := bstep (se 3 (by rfl) ⟨1631228, by rfl⟩ : syracuseStep 8699885 = 3262457) B3262457
theorem B1490987 : Blo 231814 1490987 := bstep (se 1 (by rfl) ⟨1118240, by rfl⟩ : syracuseStep 1490987 = 2236481) B2236481
theorem B4244071 : Blo 231814 4244071 := bstep (se 1 (by rfl) ⟨3183053, by rfl⟩ : syracuseStep 4244071 = 6366107) B6366107
theorem B706811 : Blo 231814 706811 := bstep (se 1 (by rfl) ⟨530108, by rfl⟩ : syracuseStep 706811 = 1060217) B1060217
theorem B3984713 : Blo 231814 3984713 := bstep (se 2 (by rfl) ⟨1494267, by rfl⟩ : syracuseStep 3984713 = 2988535) B2988535
theorem B675307 : Blo 231814 675307 := bstep (se 1 (by rfl) ⟨506480, by rfl⟩ : syracuseStep 675307 = 1012961) B1012961
theorem B347855 : Blo 231814 347855 := bstep (se 1 (by rfl) ⟨260891, by rfl⟩ : syracuseStep 347855 = 521783) B521783
theorem B347903 : Blo 231814 347903 := bstep (se 1 (by rfl) ⟨260927, by rfl⟩ : syracuseStep 347903 = 521855) B521855
theorem B1003423 : Blo 231814 1003423 := bstep (se 1 (by rfl) ⟨752567, by rfl⟩ : syracuseStep 1003423 = 1505135) B1505135
theorem B643997 : Blo 231814 643997 := bstep (se 3 (by rfl) ⟨120749, by rfl⟩ : syracuseStep 643997 = 241499) B241499
theorem B350585 : Blo 231814 350585 := bstep (se 2 (by rfl) ⟨131469, by rfl⟩ : syracuseStep 350585 = 262939) B262939
theorem B2251243 : Blo 231814 2251243 := bstep (se 1 (by rfl) ⟨1688432, by rfl⟩ : syracuseStep 2251243 = 3376865) B3376865
theorem B1989623 : Blo 231814 1989623 := bstep (se 1 (by rfl) ⟨1492217, by rfl⟩ : syracuseStep 1989623 = 2984435) B2984435
theorem B351287 : Blo 231814 351287 := bstep (se 1 (by rfl) ⟨263465, by rfl⟩ : syracuseStep 351287 = 526931) B526931
theorem B1072187 : Blo 231814 1072187 := bstep (se 1 (by rfl) ⟨804140, by rfl⟩ : syracuseStep 1072187 = 1608281) B1608281
theorem B4480343 : Blo 231814 4480343 := bstep (se 1 (by rfl) ⟨3360257, by rfl⟩ : syracuseStep 4480343 = 6720515) B6720515
theorem B351785 : Blo 231814 351785 := bstep (se 2 (by rfl) ⟨131919, by rfl⟩ : syracuseStep 351785 = 263839) B263839
theorem B745213 : Blo 231814 745213 := bstep (se 3 (by rfl) ⟨139727, by rfl⟩ : syracuseStep 745213 = 279455) B279455
theorem B352127 : Blo 231814 352127 := bstep (se 1 (by rfl) ⟨264095, by rfl⟩ : syracuseStep 352127 = 528191) B528191
theorem B2384093 : Blo 231814 2384093 := bstep (se 3 (by rfl) ⟨447017, by rfl⟩ : syracuseStep 2384093 = 894035) B894035
theorem B1794383 : Blo 231814 1794383 := bstep (se 1 (by rfl) ⟨1345787, by rfl⟩ : syracuseStep 1794383 = 2691575) B2691575
theorem B352751 : Blo 231814 352751 := bstep (se 1 (by rfl) ⟨264563, by rfl⟩ : syracuseStep 352751 = 529127) B529127
theorem B3596831 : Blo 231814 3596831 := bstep (se 1 (by rfl) ⟨2697623, by rfl⟩ : syracuseStep 3596831 = 5395247) B5395247
theorem B353531 : Blo 231814 353531 := bstep (se 1 (by rfl) ⟨265148, by rfl⟩ : syracuseStep 353531 = 530297) B530297
theorem B1074779 : Blo 231814 1074779 := bstep (se 1 (by rfl) ⟨806084, by rfl⟩ : syracuseStep 1074779 = 1612169) B1612169
theorem B4024079 : Blo 231814 4024079 := bstep (se 1 (by rfl) ⟨3018059, by rfl⟩ : syracuseStep 4024079 = 6036119) B6036119
theorem B2550203 : Blo 231814 2550203 := bstep (se 1 (by rfl) ⟨1912652, by rfl⟩ : syracuseStep 2550203 = 3825305) B3825305
theorem B783161 : Blo 231814 783161 := bstep (se 2 (by rfl) ⟨293685, by rfl⟩ : syracuseStep 783161 = 587371) B587371
theorem B784079 : Blo 231814 784079 := bstep (se 1 (by rfl) ⟨588059, by rfl⟩ : syracuseStep 784079 = 1176119) B1176119
theorem B3372947 : Blo 231814 3372947 := bstep (se 1 (by rfl) ⟨2529710, by rfl⟩ : syracuseStep 3372947 = 5059421) B5059421
theorem B784295 : Blo 231814 784295 := bstep (se 1 (by rfl) ⟨588221, by rfl⟩ : syracuseStep 784295 = 1176443) B1176443
theorem B882683 : Blo 231814 882683 := bstep (se 1 (by rfl) ⟨662012, by rfl⟩ : syracuseStep 882683 = 1324025) B1324025
theorem B882697 : Blo 231814 882697 := bstep (se 2 (by rfl) ⟨331011, by rfl⟩ : syracuseStep 882697 = 662023) B662023
theorem B587807 : Blo 231814 587807 := bstep (se 1 (by rfl) ⟨440855, by rfl⟩ : syracuseStep 587807 = 881711) B881711
theorem B391783 : Blo 231814 391783 := bstep (se 1 (by rfl) ⟨293837, by rfl⟩ : syracuseStep 391783 = 587675) B587675
theorem B752287 : Blo 231814 752287 := bstep (se 1 (by rfl) ⟨564215, by rfl⟩ : syracuseStep 752287 = 1128431) B1128431
theorem B2849579 : Blo 231814 2849579 := bstep (se 1 (by rfl) ⟨2137184, by rfl⟩ : syracuseStep 2849579 = 4274369) B4274369
theorem B1342271 : Blo 231814 1342271 := bstep (se 1 (by rfl) ⟨1006703, by rfl⟩ : syracuseStep 1342271 = 2013407) B2013407
theorem B589295 : Blo 231814 589295 := bstep (se 1 (by rfl) ⟨441971, by rfl⟩ : syracuseStep 589295 = 883943) B883943
theorem B392809 : Blo 231814 392809 := bstep (se 2 (by rfl) ⟨147303, by rfl⟩ : syracuseStep 392809 = 294607) B294607
theorem B1343135 : Blo 231814 1343135 := bstep (se 1 (by rfl) ⟨1007351, by rfl⟩ : syracuseStep 1343135 = 2014703) B2014703
theorem B21627161 : Blo 231814 21627161 := bstep (se 2 (by rfl) ⟨8110185, by rfl⟩ : syracuseStep 21627161 = 16220371) B16220371
theorem B3015143 : Blo 231814 3015143 := bstep (se 1 (by rfl) ⟨2261357, by rfl⟩ : syracuseStep 3015143 = 4522715) B4522715
theorem B393707 : Blo 231814 393707 := bstep (se 1 (by rfl) ⟨295280, by rfl⟩ : syracuseStep 393707 = 590561) B590561
theorem B394105 : Blo 231814 394105 := bstep (se 2 (by rfl) ⟨147789, by rfl⟩ : syracuseStep 394105 = 295579) B295579
theorem B788507 : Blo 231814 788507 := bstep (se 1 (by rfl) ⟨591380, by rfl⟩ : syracuseStep 788507 = 1182761) B1182761
theorem B2656475 : Blo 231814 2656475 := bstep (se 1 (by rfl) ⟨1992356, by rfl⟩ : syracuseStep 2656475 = 3984713) B3984713
theorem B788723 : Blo 231814 788723 := bstep (se 1 (by rfl) ⟨591542, by rfl⟩ : syracuseStep 788723 = 1183085) B1183085
theorem B231903 : Blo 231814 231903 := bstep (se 1 (by rfl) ⟨173927, by rfl⟩ : syracuseStep 231903 = 347855) B347855
theorem B231935 : Blo 231814 231935 := bstep (se 1 (by rfl) ⟨173951, by rfl⟩ : syracuseStep 231935 = 347903) B347903
theorem B526895 : Blo 231814 526895 := bstep (se 1 (by rfl) ⟨395171, by rfl⟩ : syracuseStep 526895 = 790343) B790343
theorem B395867 : Blo 231814 395867 := bstep (se 1 (by rfl) ⟨296900, by rfl⟩ : syracuseStep 395867 = 593801) B593801
theorem B429331 : Blo 231814 429331 := bstep (se 1 (by rfl) ⟨321998, by rfl⟩ : syracuseStep 429331 = 643997) B643997
theorem B396967 : Blo 231814 396967 := bstep (se 1 (by rfl) ⟨297725, by rfl⟩ : syracuseStep 396967 = 595451) B595451
theorem B233723 : Blo 231814 233723 := bstep (se 1 (by rfl) ⟨175292, by rfl⟩ : syracuseStep 233723 = 350585) B350585
theorem B234191 : Blo 231814 234191 := bstep (se 1 (by rfl) ⟨175643, by rfl⟩ : syracuseStep 234191 = 351287) B351287
theorem B2986895 : Blo 231814 2986895 := bstep (se 1 (by rfl) ⟨2240171, by rfl⟩ : syracuseStep 2986895 = 4480343) B4480343
theorem B234523 : Blo 231814 234523 := bstep (se 1 (by rfl) ⟨175892, by rfl⟩ : syracuseStep 234523 = 351785) B351785
theorem B12424337 : Blo 231814 12424337 := bstep (se 2 (by rfl) ⟨4659126, by rfl⟩ : syracuseStep 12424337 = 9318253) B9318253
theorem B398567 : Blo 231814 398567 := bstep (se 1 (by rfl) ⟨298925, by rfl⟩ : syracuseStep 398567 = 597851) B597851
theorem B234751 : Blo 231814 234751 := bstep (se 1 (by rfl) ⟨176063, by rfl⟩ : syracuseStep 234751 = 352127) B352127
theorem B890473 : Blo 231814 890473 := bstep (se 2 (by rfl) ⟨333927, by rfl⟩ : syracuseStep 890473 = 667855) B667855
theorem B792179 : Blo 231814 792179 := bstep (se 1 (by rfl) ⟨594134, by rfl⟩ : syracuseStep 792179 = 1188269) B1188269
theorem B235167 : Blo 231814 235167 := bstep (se 1 (by rfl) ⟨176375, by rfl⟩ : syracuseStep 235167 = 352751) B352751
theorem B2397887 : Blo 231814 2397887 := bstep (se 1 (by rfl) ⟨1798415, by rfl⟩ : syracuseStep 2397887 = 3596831) B3596831
theorem B792449 : Blo 231814 792449 := bstep (se 2 (by rfl) ⟨297168, by rfl⟩ : syracuseStep 792449 = 594337) B594337
theorem B235687 : Blo 231814 235687 := bstep (se 1 (by rfl) ⟨176765, by rfl⟩ : syracuseStep 235687 = 353531) B353531
theorem B2562299 : Blo 231814 2562299 := bstep (se 1 (by rfl) ⟨1921724, by rfl⟩ : syracuseStep 2562299 = 3843449) B3843449
theorem B794015 : Blo 231814 794015 := bstep (se 1 (by rfl) ⟨595511, by rfl⟩ : syracuseStep 794015 = 1191023) B1191023
theorem B500089 : Blo 231814 500089 := bstep (se 2 (by rfl) ⟨187533, by rfl⟩ : syracuseStep 500089 = 375067) B375067
theorem B6497819 : Blo 231814 6497819 := bstep (se 1 (by rfl) ⟨4873364, by rfl⟩ : syracuseStep 6497819 = 9746729) B9746729
theorem B665167 : Blo 231814 665167 := bstep (se 1 (by rfl) ⟨498875, by rfl⟩ : syracuseStep 665167 = 997751) B997751
theorem B894847 : Blo 231814 894847 := bstep (se 1 (by rfl) ⟨671135, by rfl⟩ : syracuseStep 894847 = 1342271) B1342271
theorem B993343 : Blo 231814 993343 := bstep (se 1 (by rfl) ⟨745007, by rfl⟩ : syracuseStep 993343 = 1490015) B1490015
theorem B993617 : Blo 231814 993617 := bstep (se 2 (by rfl) ⟨372606, by rfl⟩ : syracuseStep 993617 = 745213) B745213
theorem B895423 : Blo 231814 895423 := bstep (se 1 (by rfl) ⟨671567, by rfl⟩ : syracuseStep 895423 = 1343135) B1343135
theorem B2665223 : Blo 231814 2665223 := bstep (se 1 (by rfl) ⟨1998917, by rfl⟩ : syracuseStep 2665223 = 3997835) B3997835
theorem B3975965 : Blo 231814 3975965 := bstep (se 3 (by rfl) ⟨745493, by rfl⟩ : syracuseStep 3975965 = 1490987) B1490987
theorem B670817 : Blo 231814 670817 := bstep (se 2 (by rfl) ⟨251556, by rfl⟩ : syracuseStep 670817 = 503113) B503113
theorem B900409 : Blo 231814 900409 := bstep (se 2 (by rfl) ⟨337653, by rfl⟩ : syracuseStep 900409 = 675307) B675307
theorem B1326415 : Blo 231814 1326415 := bstep (se 1 (by rfl) ⟨994811, by rfl⟩ : syracuseStep 1326415 = 1989623) B1989623
theorem B671273 : Blo 231814 671273 := bstep (se 2 (by rfl) ⟨251727, by rfl⟩ : syracuseStep 671273 = 503455) B503455
theorem B1589395 : Blo 231814 1589395 := bstep (se 1 (by rfl) ⟨1192046, by rfl⟩ : syracuseStep 1589395 = 2384093) B2384093
theorem B1196255 : Blo 231814 1196255 := bstep (se 1 (by rfl) ⟨897191, by rfl⟩ : syracuseStep 1196255 = 1794383) B1794383
theorem B541225 : Blo 231814 541225 := bstep (se 2 (by rfl) ⟨202959, by rfl⟩ : syracuseStep 541225 = 405919) B405919
theorem B1884829 : Blo 231814 1884829 := bstep (se 3 (by rfl) ⟨353405, by rfl⟩ : syracuseStep 1884829 = 706811) B706811
theorem B443855 : Blo 231814 443855 := bstep (se 1 (by rfl) ⟨332891, by rfl⟩ : syracuseStep 443855 = 665783) B665783
theorem B1788965 : Blo 231814 1788965 := bstep (se 4 (by rfl) ⟨167715, by rfl⟩ : syracuseStep 1788965 = 335431) B335431
theorem B3001657 : Blo 231814 3001657 := bstep (se 2 (by rfl) ⟨1125621, by rfl⟩ : syracuseStep 3001657 = 2251243) B2251243
theorem B4771295 : Blo 231814 4771295 := bstep (se 1 (by rfl) ⟨3578471, by rfl⟩ : syracuseStep 4771295 = 7156943) B7156943
theorem B1003049 : Blo 231814 1003049 := bstep (se 2 (by rfl) ⟨376143, by rfl⟩ : syracuseStep 1003049 = 752287) B752287
theorem B446057 : Blo 231814 446057 := bstep (se 2 (by rfl) ⟨167271, by rfl⟩ : syracuseStep 446057 = 334543) B334543
theorem B2248631 : Blo 231814 2248631 := bstep (se 1 (by rfl) ⟨1686473, by rfl⟩ : syracuseStep 2248631 = 3372947) B3372947
theorem B1332065 : Blo 231814 1332065 := bstep (se 2 (by rfl) ⟨499524, by rfl⟩ : syracuseStep 1332065 = 999049) B999049
theorem B349979 : Blo 231814 349979 := bstep (se 1 (by rfl) ⟨262484, by rfl⟩ : syracuseStep 349979 = 524969) B524969
theorem B5658761 : Blo 231814 5658761 := bstep (se 2 (by rfl) ⟨2122035, by rfl⟩ : syracuseStep 5658761 = 4244071) B4244071
theorem B350939 : Blo 231814 350939 := bstep (se 1 (by rfl) ⟨263204, by rfl⟩ : syracuseStep 350939 = 526409) B526409
theorem B351467 : Blo 231814 351467 := bstep (se 1 (by rfl) ⟨263600, by rfl⟩ : syracuseStep 351467 = 527201) B527201
theorem B745033 : Blo 231814 745033 := bstep (se 2 (by rfl) ⟨279387, by rfl⟩ : syracuseStep 745033 = 558775) B558775
theorem B352091 : Blo 231814 352091 := bstep (se 1 (by rfl) ⟨264068, by rfl⟩ : syracuseStep 352091 = 528137) B528137
theorem B352103 : Blo 231814 352103 := bstep (se 1 (by rfl) ⟨264077, by rfl⟩ : syracuseStep 352103 = 528155) B528155
theorem B352283 : Blo 231814 352283 := bstep (se 1 (by rfl) ⟨264212, by rfl⟩ : syracuseStep 352283 = 528425) B528425
theorem B352415 : Blo 231814 352415 := bstep (se 1 (by rfl) ⟨264311, by rfl⟩ : syracuseStep 352415 = 528623) B528623
theorem B352703 : Blo 231814 352703 := bstep (se 1 (by rfl) ⟨264527, by rfl⟩ : syracuseStep 352703 = 529055) B529055
theorem B2777723 : Blo 231814 2777723 := bstep (se 1 (by rfl) ⟨2083292, by rfl⟩ : syracuseStep 2777723 = 4166585) B4166585
theorem B353417 : Blo 231814 353417 := bstep (se 2 (by rfl) ⟨132531, by rfl⟩ : syracuseStep 353417 = 265063) B265063
theorem B1762721 : Blo 231814 1762721 := bstep (se 2 (by rfl) ⟨661020, by rfl⟩ : syracuseStep 1762721 = 1322041) B1322041
theorem B714791 : Blo 231814 714791 := bstep (se 1 (by rfl) ⟨536093, by rfl⟩ : syracuseStep 714791 = 1072187) B1072187
theorem B747647 : Blo 231814 747647 := bstep (se 1 (by rfl) ⟨560735, by rfl⟩ : syracuseStep 747647 = 1121471) B1121471
theorem B1337897 : Blo 231814 1337897 := bstep (se 2 (by rfl) ⟨501711, by rfl⟩ : syracuseStep 1337897 = 1003423) B1003423
theorem B1339037 : Blo 231814 1339037 := bstep (se 3 (by rfl) ⟨251069, by rfl⟩ : syracuseStep 1339037 = 502139) B502139
theorem B716519 : Blo 231814 716519 := bstep (se 1 (by rfl) ⟨537389, by rfl⟩ : syracuseStep 716519 = 1074779) B1074779
theorem B2682719 : Blo 231814 2682719 := bstep (se 1 (by rfl) ⟨2012039, by rfl⟩ : syracuseStep 2682719 = 4024079) B4024079
theorem B356543 : Blo 231814 356543 := bstep (se 1 (by rfl) ⟨267407, by rfl⟩ : syracuseStep 356543 = 534815) B534815
theorem B1700135 : Blo 231814 1700135 := bstep (se 1 (by rfl) ⟨1275101, by rfl⟩ : syracuseStep 1700135 = 2550203) B2550203
theorem B881225 : Blo 231814 881225 := bstep (se 2 (by rfl) ⟨330459, by rfl⟩ : syracuseStep 881225 = 660919) B660919
theorem B1176929 : Blo 231814 1176929 := bstep (se 2 (by rfl) ⟨441348, by rfl⟩ : syracuseStep 1176929 = 882697) B882697
theorem B6125057 : Blo 231814 6125057 := bstep (se 2 (by rfl) ⟨2296896, by rfl⟩ : syracuseStep 6125057 = 4593793) B4593793
theorem B522107 : Blo 231814 522107 := bstep (se 1 (by rfl) ⟨391580, by rfl⟩ : syracuseStep 522107 = 783161) B783161
theorem B522377 : Blo 231814 522377 := bstep (se 2 (by rfl) ⟨195891, by rfl⟩ : syracuseStep 522377 = 391783) B391783
theorem B522719 : Blo 231814 522719 := bstep (se 1 (by rfl) ⟨392039, by rfl⟩ : syracuseStep 522719 = 784079) B784079
theorem B522863 : Blo 231814 522863 := bstep (se 1 (by rfl) ⟨392147, by rfl⟩ : syracuseStep 522863 = 784295) B784295
theorem B588455 : Blo 231814 588455 := bstep (se 1 (by rfl) ⟨441341, by rfl⟩ : syracuseStep 588455 = 882683) B882683
theorem B391871 : Blo 231814 391871 := bstep (se 1 (by rfl) ⟨293903, by rfl⟩ : syracuseStep 391871 = 587807) B587807
theorem B1899719 : Blo 231814 1899719 := bstep (se 1 (by rfl) ⟨1424789, by rfl⟩ : syracuseStep 1899719 = 2849579) B2849579
theorem B1342727 : Blo 231814 1342727 := bstep (se 1 (by rfl) ⟨1007045, by rfl⟩ : syracuseStep 1342727 = 2014091) B2014091
theorem B523745 : Blo 231814 523745 := bstep (se 2 (by rfl) ⟨196404, by rfl⟩ : syracuseStep 523745 = 392809) B392809
theorem B392863 : Blo 231814 392863 := bstep (se 1 (by rfl) ⟨294647, by rfl⟩ : syracuseStep 392863 = 589295) B589295
theorem B5799923 : Blo 231814 5799923 := bstep (se 1 (by rfl) ⟨4349942, by rfl⟩ : syracuseStep 5799923 = 8699885) B8699885
theorem B14418107 : Blo 231814 14418107 := bstep (se 1 (by rfl) ⟨10813580, by rfl⟩ : syracuseStep 14418107 = 21627161) B21627161
theorem B262471 : Blo 231814 262471 := bstep (se 1 (by rfl) ⟨196853, by rfl⟩ : syracuseStep 262471 = 393707) B393707
theorem B295903 : Blo 231814 295903 := bstep (se 1 (by rfl) ⟨221927, by rfl⟩ : syracuseStep 295903 = 443855) B443855
theorem B525473 : Blo 231814 525473 := bstep (se 2 (by rfl) ⟨197052, by rfl⟩ : syracuseStep 525473 = 394105) B394105
theorem B525671 : Blo 231814 525671 := bstep (se 1 (by rfl) ⟨394253, by rfl⟩ : syracuseStep 525671 = 788507) B788507
theorem B1770983 : Blo 231814 1770983 := bstep (se 1 (by rfl) ⟨1328237, by rfl⟩ : syracuseStep 1770983 = 2656475) B2656475
theorem B525815 : Blo 231814 525815 := bstep (se 1 (by rfl) ⟨394361, by rfl⟩ : syracuseStep 525815 = 788723) B788723
theorem B263911 : Blo 231814 263911 := bstep (se 1 (by rfl) ⟨197933, by rfl⟩ : syracuseStep 263911 = 395867) B395867
theorem B3803125 : Blo 231814 3803125 := bstep (se 5 (by rfl) ⟨178271, by rfl⟩ : syracuseStep 3803125 = 356543) B356543
theorem B886889 : Blo 231814 886889 := bstep (se 2 (by rfl) ⟨332583, by rfl⟩ : syracuseStep 886889 = 665167) B665167
theorem B3180863 : Blo 231814 3180863 := bstep (se 1 (by rfl) ⟨2385647, by rfl⟩ : syracuseStep 3180863 = 4771295) B4771295
theorem B297371 : Blo 231814 297371 := bstep (se 1 (by rfl) ⟨223028, by rfl⟩ : syracuseStep 297371 = 446057) B446057
theorem B2886533 : Blo 231814 2886533 := bstep (se 4 (by rfl) ⟨270612, by rfl⟩ : syracuseStep 2886533 = 541225) B541225
theorem B888043 : Blo 231814 888043 := bstep (se 1 (by rfl) ⟨666032, by rfl⟩ : syracuseStep 888043 = 1332065) B1332065
theorem B528119 : Blo 231814 528119 := bstep (se 1 (by rfl) ⟨396089, by rfl⟩ : syracuseStep 528119 = 792179) B792179
theorem B233319 : Blo 231814 233319 := bstep (se 1 (by rfl) ⟨174989, by rfl⟩ : syracuseStep 233319 = 349979) B349979
theorem B528299 : Blo 231814 528299 := bstep (se 1 (by rfl) ⟨396224, by rfl⟩ : syracuseStep 528299 = 792449) B792449
theorem B3772507 : Blo 231814 3772507 := bstep (se 1 (by rfl) ⟨2829380, by rfl⟩ : syracuseStep 3772507 = 5658761) B5658761
theorem B1708199 : Blo 231814 1708199 := bstep (se 1 (by rfl) ⟨1281149, by rfl⟩ : syracuseStep 1708199 = 2562299) B2562299
theorem B4002209 : Blo 231814 4002209 := bstep (se 2 (by rfl) ⟨1500828, by rfl⟩ : syracuseStep 4002209 = 3001657) B3001657
theorem B233959 : Blo 231814 233959 := bstep (se 1 (by rfl) ⟨175469, by rfl⟩ : syracuseStep 233959 = 350939) B350939
theorem B234311 : Blo 231814 234311 := bstep (se 1 (by rfl) ⟨175733, by rfl⟩ : syracuseStep 234311 = 351467) B351467
theorem B529289 : Blo 231814 529289 := bstep (se 2 (by rfl) ⟨198483, by rfl⟩ : syracuseStep 529289 = 396967) B396967
theorem B529343 : Blo 231814 529343 := bstep (se 1 (by rfl) ⟨397007, by rfl⟩ : syracuseStep 529343 = 794015) B794015
theorem B234727 : Blo 231814 234727 := bstep (se 1 (by rfl) ⟨176045, by rfl⟩ : syracuseStep 234727 = 352091) B352091
theorem B234735 : Blo 231814 234735 := bstep (se 1 (by rfl) ⟨176051, by rfl⟩ : syracuseStep 234735 = 352103) B352103
theorem B234855 : Blo 231814 234855 := bstep (se 1 (by rfl) ⟨176141, by rfl⟩ : syracuseStep 234855 = 352283) B352283
theorem B234943 : Blo 231814 234943 := bstep (se 1 (by rfl) ⟨176207, by rfl⟩ : syracuseStep 234943 = 352415) B352415
theorem B235135 : Blo 231814 235135 := bstep (se 1 (by rfl) ⟨176351, by rfl⟩ : syracuseStep 235135 = 352703) B352703
theorem B235611 : Blo 231814 235611 := bstep (se 1 (by rfl) ⟨176708, by rfl⟩ : syracuseStep 235611 = 353417) B353417
theorem B4331879 : Blo 231814 4331879 := bstep (se 1 (by rfl) ⟨3248909, by rfl⟩ : syracuseStep 4331879 = 6497819) B6497819
theorem B498431 : Blo 231814 498431 := bstep (se 1 (by rfl) ⟨373823, by rfl⟩ : syracuseStep 498431 = 747647) B747647
theorem B662411 : Blo 231814 662411 := bstep (se 1 (by rfl) ⟨496808, by rfl⟩ : syracuseStep 662411 = 993617) B993617
theorem B891931 : Blo 231814 891931 := bstep (se 1 (by rfl) ⟨668948, by rfl⟩ : syracuseStep 891931 = 1337897) B1337897
theorem B1776815 : Blo 231814 1776815 := bstep (se 1 (by rfl) ⟨1332611, by rfl⟩ : syracuseStep 1776815 = 2665223) B2665223
theorem B1187297 : Blo 231814 1187297 := bstep (se 2 (by rfl) ⟨445236, by rfl⟩ : syracuseStep 1187297 = 890473) B890473
theorem B892691 : Blo 231814 892691 := bstep (se 1 (by rfl) ⟨669518, by rfl⟩ : syracuseStep 892691 = 1339037) B1339037
theorem B993377 : Blo 231814 993377 := bstep (se 2 (by rfl) ⟨372516, by rfl⟩ : syracuseStep 993377 = 745033) B745033
theorem B895151 : Blo 231814 895151 := bstep (se 1 (by rfl) ⟨671363, by rfl⟩ : syracuseStep 895151 = 1342727) B1342727
theorem B2010095 : Blo 231814 2010095 := bstep (se 1 (by rfl) ⟨1507571, by rfl⟩ : syracuseStep 2010095 = 3015143) B3015143
theorem B666785 : Blo 231814 666785 := bstep (se 2 (by rfl) ⟨250044, by rfl⟩ : syracuseStep 666785 = 500089) B500089
theorem B3190013 : Blo 231814 3190013 := bstep (se 3 (by rfl) ⟨598127, by rfl⟩ : syracuseStep 3190013 = 1196255) B1196255
theorem B1192643 : Blo 231814 1192643 := bstep (se 1 (by rfl) ⟨894482, by rfl⟩ : syracuseStep 1192643 = 1788965) B1788965
theorem B668699 : Blo 231814 668699 := bstep (se 1 (by rfl) ⟨501524, by rfl⟩ : syracuseStep 668699 = 1003049) B1003049
theorem B1193129 : Blo 231814 1193129 := bstep (se 2 (by rfl) ⟨447423, by rfl⟩ : syracuseStep 1193129 = 894847) B894847
theorem B1324457 : Blo 231814 1324457 := bstep (se 2 (by rfl) ⟨496671, by rfl⟩ : syracuseStep 1324457 = 993343) B993343
theorem B1193897 : Blo 231814 1193897 := bstep (se 2 (by rfl) ⟨447711, by rfl⟩ : syracuseStep 1193897 = 895423) B895423
theorem B1062845 : Blo 231814 1062845 := bstep (se 3 (by rfl) ⟨199283, by rfl⟩ : syracuseStep 1062845 = 398567) B398567
theorem B572441 : Blo 231814 572441 := bstep (se 2 (by rfl) ⟨214665, by rfl⟩ : syracuseStep 572441 = 429331) B429331
theorem B1851815 : Blo 231814 1851815 := bstep (se 1 (by rfl) ⟨1388861, by rfl⟩ : syracuseStep 1851815 = 2777723) B2777723
theorem B476527 : Blo 231814 476527 := bstep (se 1 (by rfl) ⟨357395, by rfl⟩ : syracuseStep 476527 = 714791) B714791
theorem B477679 : Blo 231814 477679 := bstep (se 1 (by rfl) ⟨358259, by rfl⟩ : syracuseStep 477679 = 716519) B716519
theorem B1788479 : Blo 231814 1788479 := bstep (se 1 (by rfl) ⟨1341359, by rfl⟩ : syracuseStep 1788479 = 2682719) B2682719
theorem B1133423 : Blo 231814 1133423 := bstep (se 1 (by rfl) ⟨850067, by rfl⟩ : syracuseStep 1133423 = 1700135) B1700135
theorem B4083371 : Blo 231814 4083371 := bstep (se 1 (by rfl) ⟨3062528, by rfl⟩ : syracuseStep 4083371 = 6125057) B6125057
theorem B348071 : Blo 231814 348071 := bstep (se 1 (by rfl) ⟨261053, by rfl⟩ : syracuseStep 348071 = 522107) B522107
theorem B348251 : Blo 231814 348251 := bstep (se 1 (by rfl) ⟨261188, by rfl⟩ : syracuseStep 348251 = 522377) B522377
theorem B348479 : Blo 231814 348479 := bstep (se 1 (by rfl) ⟨261359, by rfl⟩ : syracuseStep 348479 = 522719) B522719
theorem B348575 : Blo 231814 348575 := bstep (se 1 (by rfl) ⟨261431, by rfl⟩ : syracuseStep 348575 = 522863) B522863
theorem B1200545 : Blo 231814 1200545 := bstep (se 2 (by rfl) ⟨450204, by rfl⟩ : syracuseStep 1200545 = 900409) B900409
theorem B447211 : Blo 231814 447211 := bstep (se 1 (by rfl) ⟨335408, by rfl⟩ : syracuseStep 447211 = 670817) B670817
theorem B1266479 : Blo 231814 1266479 := bstep (se 1 (by rfl) ⟨949859, by rfl⟩ : syracuseStep 1266479 = 1899719) B1899719
theorem B349163 : Blo 231814 349163 := bstep (se 1 (by rfl) ⟨261872, by rfl⟩ : syracuseStep 349163 = 523745) B523745
theorem B447515 : Blo 231814 447515 := bstep (se 1 (by rfl) ⟨335636, by rfl⟩ : syracuseStep 447515 = 671273) B671273
theorem B2119193 : Blo 231814 2119193 := bstep (se 2 (by rfl) ⟨794697, by rfl⟩ : syracuseStep 2119193 = 1589395) B1589395
theorem B2513105 : Blo 231814 2513105 := bstep (se 2 (by rfl) ⟨942414, by rfl⟩ : syracuseStep 2513105 = 1884829) B1884829
theorem B351263 : Blo 231814 351263 := bstep (se 1 (by rfl) ⟨263447, by rfl⟩ : syracuseStep 351263 = 526895) B526895
theorem B1499087 : Blo 231814 1499087 := bstep (se 1 (by rfl) ⟨1124315, by rfl⟩ : syracuseStep 1499087 = 2248631) B2248631
theorem B1991263 : Blo 231814 1991263 := bstep (se 1 (by rfl) ⟨1493447, by rfl⟩ : syracuseStep 1991263 = 2986895) B2986895
theorem B8282891 : Blo 231814 8282891 := bstep (se 1 (by rfl) ⟨6212168, by rfl⟩ : syracuseStep 8282891 = 12424337) B12424337
theorem B1598591 : Blo 231814 1598591 := bstep (se 1 (by rfl) ⟨1198943, by rfl⟩ : syracuseStep 1598591 = 2397887) B2397887
theorem B1175147 : Blo 231814 1175147 := bstep (se 1 (by rfl) ⟨881360, by rfl⟩ : syracuseStep 1175147 = 1762721) B1762721
theorem B2650643 : Blo 231814 2650643 := bstep (se 1 (by rfl) ⟨1987982, by rfl⟩ : syracuseStep 2650643 = 3975965) B3975965
theorem B587483 : Blo 231814 587483 := bstep (se 1 (by rfl) ⟨440612, by rfl⟩ : syracuseStep 587483 = 881225) B881225
theorem B784619 : Blo 231814 784619 := bstep (se 1 (by rfl) ⟨588464, by rfl⟩ : syracuseStep 784619 = 1176929) B1176929
theorem B1768553 : Blo 231814 1768553 := bstep (se 2 (by rfl) ⟨663207, by rfl⟩ : syracuseStep 1768553 = 1326415) B1326415
theorem B392303 : Blo 231814 392303 := bstep (se 1 (by rfl) ⟨294227, by rfl⟩ : syracuseStep 392303 = 588455) B588455
theorem B261247 : Blo 231814 261247 := bstep (se 1 (by rfl) ⟨195935, by rfl⟩ : syracuseStep 261247 = 391871) B391871
theorem B523817 : Blo 231814 523817 := bstep (se 2 (by rfl) ⟨196431, by rfl⟩ : syracuseStep 523817 = 392863) B392863
theorem B3866615 : Blo 231814 3866615 := bstep (se 1 (by rfl) ⟨2899961, by rfl⟩ : syracuseStep 3866615 = 5799923) B5799923
theorem B2655017 : Blo 231814 2655017 := bstep (se 2 (by rfl) ⟨995631, by rfl⟩ : syracuseStep 2655017 = 1991263) B1991263
theorem B1180655 : Blo 231814 1180655 := bstep (se 1 (by rfl) ⟨885491, by rfl⟩ : syracuseStep 1180655 = 1770983) B1770983
theorem B394537 : Blo 231814 394537 := bstep (se 2 (by rfl) ⟨147951, by rfl⟩ : syracuseStep 394537 = 295903) B295903
theorem B591259 : Blo 231814 591259 := bstep (se 1 (by rfl) ⟨443444, by rfl⟩ : syracuseStep 591259 = 886889) B886889
theorem B755615 : Blo 231814 755615 := bstep (se 1 (by rfl) ⟨566711, by rfl⟩ : syracuseStep 755615 = 1133423) B1133423
theorem B22087709 : Blo 231814 22087709 := bstep (se 3 (by rfl) ⟨4141445, by rfl⟩ : syracuseStep 22087709 = 8282891) B8282891
theorem B2722247 : Blo 231814 2722247 := bstep (se 1 (by rfl) ⟨2041685, by rfl⟩ : syracuseStep 2722247 = 4083371) B4083371
theorem B232047 : Blo 231814 232047 := bstep (se 1 (by rfl) ⟨174035, by rfl⟩ : syracuseStep 232047 = 348071) B348071
theorem B232167 : Blo 231814 232167 := bstep (se 1 (by rfl) ⟨174125, by rfl⟩ : syracuseStep 232167 = 348251) B348251
theorem B232319 : Blo 231814 232319 := bstep (se 1 (by rfl) ⟨174239, by rfl⟩ : syracuseStep 232319 = 348479) B348479
theorem B232383 : Blo 231814 232383 := bstep (se 1 (by rfl) ⟨174287, by rfl⟩ : syracuseStep 232383 = 348575) B348575
theorem B232775 : Blo 231814 232775 := bstep (se 1 (by rfl) ⟨174581, by rfl⟩ : syracuseStep 232775 = 349163) B349163
theorem B298343 : Blo 231814 298343 := bstep (se 1 (by rfl) ⟨223757, by rfl⟩ : syracuseStep 298343 = 447515) B447515
theorem B1412795 : Blo 231814 1412795 := bstep (se 1 (by rfl) ⟨1059596, by rfl⟩ : syracuseStep 1412795 = 2119193) B2119193
theorem B1675403 : Blo 231814 1675403 := bstep (se 1 (by rfl) ⟨1256552, by rfl⟩ : syracuseStep 1675403 = 2513105) B2513105
theorem B2887919 : Blo 231814 2887919 := bstep (se 1 (by rfl) ⟨2165939, by rfl⟩ : syracuseStep 2887919 = 4331879) B4331879
theorem B1184057 : Blo 231814 1184057 := bstep (se 2 (by rfl) ⟨444021, by rfl⟩ : syracuseStep 1184057 = 888043) B888043
theorem B234175 : Blo 231814 234175 := bstep (se 1 (by rfl) ⟨175631, by rfl⟩ : syracuseStep 234175 = 351263) B351263
theorem B1184543 : Blo 231814 1184543 := bstep (se 1 (by rfl) ⟨888407, by rfl⟩ : syracuseStep 1184543 = 1776815) B1776815
theorem B791531 : Blo 231814 791531 := bstep (se 1 (by rfl) ⟨593648, by rfl⟩ : syracuseStep 791531 = 1187297) B1187297
theorem B3183725 : Blo 231814 3183725 := bstep (se 3 (by rfl) ⟨596948, by rfl⟩ : syracuseStep 3183725 = 1193897) B1193897
theorem B595127 : Blo 231814 595127 := bstep (se 1 (by rfl) ⟨446345, by rfl⟩ : syracuseStep 595127 = 892691) B892691
theorem B596281 : Blo 231814 596281 := bstep (se 2 (by rfl) ⟨223605, by rfl⟩ : syracuseStep 596281 = 447211) B447211
theorem B792989 : Blo 231814 792989 := bstep (se 3 (by rfl) ⟨148685, by rfl⟩ : syracuseStep 792989 = 297371) B297371
theorem B662251 : Blo 231814 662251 := bstep (se 1 (by rfl) ⟨496688, by rfl⟩ : syracuseStep 662251 = 993377) B993377
theorem B596767 : Blo 231814 596767 := bstep (se 1 (by rfl) ⟨447575, by rfl⟩ : syracuseStep 596767 = 895151) B895151
theorem B795095 : Blo 231814 795095 := bstep (se 1 (by rfl) ⟨596321, by rfl⟩ : syracuseStep 795095 = 1192643) B1192643
theorem B795419 : Blo 231814 795419 := bstep (se 1 (by rfl) ⟨596564, by rfl⟩ : syracuseStep 795419 = 1193129) B1193129
theorem B1189241 : Blo 231814 1189241 := bstep (se 2 (by rfl) ⟨445965, by rfl⟩ : syracuseStep 1189241 = 891931) B891931
theorem B9612071 : Blo 231814 9612071 := bstep (se 1 (by rfl) ⟨7209053, by rfl⟩ : syracuseStep 9612071 = 14418107) B14418107
theorem B1192319 : Blo 231814 1192319 := bstep (se 1 (by rfl) ⟨894239, by rfl⟩ : syracuseStep 1192319 = 1788479) B1788479
theorem B635369 : Blo 231814 635369 := bstep (se 2 (by rfl) ⟨238263, by rfl⟩ : syracuseStep 635369 = 476527) B476527
theorem B800363 : Blo 231814 800363 := bstep (se 1 (by rfl) ⟨600272, by rfl⟩ : syracuseStep 800363 = 1200545) B1200545
theorem B2668139 : Blo 231814 2668139 := bstep (se 1 (by rfl) ⟨2001104, by rfl⟩ : syracuseStep 2668139 = 4002209) B4002209
theorem B636905 : Blo 231814 636905 := bstep (se 2 (by rfl) ⟨238839, by rfl⟩ : syracuseStep 636905 = 477679) B477679
theorem B441607 : Blo 231814 441607 := bstep (se 1 (by rfl) ⟨331205, by rfl⟩ : syracuseStep 441607 = 662411) B662411
theorem B999391 : Blo 231814 999391 := bstep (se 1 (by rfl) ⟨749543, by rfl⟩ : syracuseStep 999391 = 1499087) B1499087
theorem B5030009 : Blo 231814 5030009 := bstep (se 2 (by rfl) ⟨1886253, by rfl⟩ : syracuseStep 5030009 = 3772507) B3772507
theorem B1065727 : Blo 231814 1065727 := bstep (se 1 (by rfl) ⟨799295, by rfl⟩ : syracuseStep 1065727 = 1598591) B1598591
theorem B1329149 : Blo 231814 1329149 := bstep (se 3 (by rfl) ⟨249215, by rfl⟩ : syracuseStep 1329149 = 498431) B498431
theorem B444523 : Blo 231814 444523 := bstep (se 1 (by rfl) ⟨333392, by rfl⟩ : syracuseStep 444523 = 666785) B666785
theorem B1526509 : Blo 231814 1526509 := bstep (se 3 (by rfl) ⟨286220, by rfl⟩ : syracuseStep 1526509 = 572441) B572441
theorem B445799 : Blo 231814 445799 := bstep (se 1 (by rfl) ⟨334349, by rfl⟩ : syracuseStep 445799 = 668699) B668699
theorem B708563 : Blo 231814 708563 := bstep (se 1 (by rfl) ⟨531422, by rfl⟩ : syracuseStep 708563 = 1062845) B1062845
theorem B348329 : Blo 231814 348329 := bstep (se 2 (by rfl) ⟨130623, by rfl⟩ : syracuseStep 348329 = 261247) B261247
theorem B349211 : Blo 231814 349211 := bstep (se 1 (by rfl) ⟨261908, by rfl⟩ : syracuseStep 349211 = 523817) B523817
theorem B2577743 : Blo 231814 2577743 := bstep (se 1 (by rfl) ⟨1933307, by rfl⟩ : syracuseStep 2577743 = 3866615) B3866615
theorem B1234543 : Blo 231814 1234543 := bstep (se 1 (by rfl) ⟨925907, by rfl⟩ : syracuseStep 1234543 = 1851815) B1851815
theorem B349961 : Blo 231814 349961 := bstep (se 2 (by rfl) ⟨131235, by rfl⟩ : syracuseStep 349961 = 262471) B262471
theorem B350315 : Blo 231814 350315 := bstep (se 1 (by rfl) ⟨262736, by rfl⟩ : syracuseStep 350315 = 525473) B525473
theorem B350447 : Blo 231814 350447 := bstep (se 1 (by rfl) ⟨262835, by rfl⟩ : syracuseStep 350447 = 525671) B525671
theorem B350543 : Blo 231814 350543 := bstep (se 1 (by rfl) ⟨262907, by rfl⟩ : syracuseStep 350543 = 525815) B525815
theorem B2120575 : Blo 231814 2120575 := bstep (se 1 (by rfl) ⟨1590431, by rfl⟩ : syracuseStep 2120575 = 3180863) B3180863
theorem B1924355 : Blo 231814 1924355 := bstep (se 1 (by rfl) ⟨1443266, by rfl⟩ : syracuseStep 1924355 = 2886533) B2886533
theorem B351881 : Blo 231814 351881 := bstep (se 2 (by rfl) ⟨131955, by rfl⟩ : syracuseStep 351881 = 263911) B263911
theorem B352079 : Blo 231814 352079 := bstep (se 1 (by rfl) ⟨264059, by rfl⟩ : syracuseStep 352079 = 528119) B528119
theorem B352199 : Blo 231814 352199 := bstep (se 1 (by rfl) ⟨264149, by rfl⟩ : syracuseStep 352199 = 528299) B528299
theorem B5070833 : Blo 231814 5070833 := bstep (se 2 (by rfl) ⟨1901562, by rfl⟩ : syracuseStep 5070833 = 3803125) B3803125
theorem B1138799 : Blo 231814 1138799 := bstep (se 1 (by rfl) ⟨854099, by rfl⟩ : syracuseStep 1138799 = 1708199) B1708199
theorem B844319 : Blo 231814 844319 := bstep (se 1 (by rfl) ⟨633239, by rfl⟩ : syracuseStep 844319 = 1266479) B1266479
theorem B352859 : Blo 231814 352859 := bstep (se 1 (by rfl) ⟨264644, by rfl⟩ : syracuseStep 352859 = 529289) B529289
theorem B352895 : Blo 231814 352895 := bstep (se 1 (by rfl) ⟨264671, by rfl⟩ : syracuseStep 352895 = 529343) B529343
theorem B1340063 : Blo 231814 1340063 := bstep (se 1 (by rfl) ⟨1005047, by rfl⟩ : syracuseStep 1340063 = 2010095) B2010095
theorem B2126675 : Blo 231814 2126675 := bstep (se 1 (by rfl) ⟨1595006, by rfl⟩ : syracuseStep 2126675 = 3190013) B3190013
theorem B783431 : Blo 231814 783431 := bstep (se 1 (by rfl) ⟨587573, by rfl⟩ : syracuseStep 783431 = 1175147) B1175147
theorem B1767095 : Blo 231814 1767095 := bstep (se 1 (by rfl) ⟨1325321, by rfl⟩ : syracuseStep 1767095 = 2650643) B2650643
theorem B882971 : Blo 231814 882971 := bstep (se 1 (by rfl) ⟨662228, by rfl⟩ : syracuseStep 882971 = 1324457) B1324457
theorem B391655 : Blo 231814 391655 := bstep (se 1 (by rfl) ⟨293741, by rfl⟩ : syracuseStep 391655 = 587483) B587483
theorem B523079 : Blo 231814 523079 := bstep (se 1 (by rfl) ⟨392309, by rfl⟩ : syracuseStep 523079 = 784619) B784619
theorem B1179035 : Blo 231814 1179035 := bstep (se 1 (by rfl) ⟨884276, by rfl⟩ : syracuseStep 1179035 = 1768553) B1768553
theorem B261535 : Blo 231814 261535 := bstep (se 1 (by rfl) ⟨196151, by rfl⟩ : syracuseStep 261535 = 392303) B392303
theorem B235602229 : Blo 231814 235602229 := bstep (se 5 (by rfl) ⟨11043854, by rfl⟩ : syracuseStep 235602229 = 22087709) B22087709
theorem B1770011 : Blo 231814 1770011 := bstep (se 1 (by rfl) ⟨1327508, by rfl⟩ : syracuseStep 1770011 = 2655017) B2655017
theorem B787103 : Blo 231814 787103 := bstep (se 1 (by rfl) ⟨590327, by rfl⟩ : syracuseStep 787103 = 1180655) B1180655
theorem B886099 : Blo 231814 886099 := bstep (se 1 (by rfl) ⟨664574, by rfl⟩ : syracuseStep 886099 = 1329149) B1329149
theorem B526049 : Blo 231814 526049 := bstep (se 2 (by rfl) ⟨197268, by rfl⟩ : syracuseStep 526049 = 394537) B394537
theorem B788345 : Blo 231814 788345 := bstep (se 2 (by rfl) ⟨295629, by rfl⟩ : syracuseStep 788345 = 591259) B591259
theorem B5671133 : Blo 231814 5671133 := bstep (se 3 (by rfl) ⟨1063337, by rfl⟩ : syracuseStep 5671133 = 2126675) B2126675
theorem B297199 : Blo 231814 297199 := bstep (se 1 (by rfl) ⟨222899, by rfl⟩ : syracuseStep 297199 = 445799) B445799
theorem B1116935 : Blo 231814 1116935 := bstep (se 1 (by rfl) ⟨837701, by rfl⟩ : syracuseStep 1116935 = 1675403) B1675403
theorem B232219 : Blo 231814 232219 := bstep (se 1 (by rfl) ⟨174164, by rfl⟩ : syracuseStep 232219 = 348329) B348329
theorem B592697 : Blo 231814 592697 := bstep (se 2 (by rfl) ⟨222261, by rfl⟩ : syracuseStep 592697 = 444523) B444523
theorem B789371 : Blo 231814 789371 := bstep (se 1 (by rfl) ⟨592028, by rfl⟩ : syracuseStep 789371 = 1184057) B1184057
theorem B789695 : Blo 231814 789695 := bstep (se 1 (by rfl) ⟨592271, by rfl⟩ : syracuseStep 789695 = 1184543) B1184543
theorem B527687 : Blo 231814 527687 := bstep (se 1 (by rfl) ⟨395765, by rfl⟩ : syracuseStep 527687 = 791531) B791531
theorem B232807 : Blo 231814 232807 := bstep (se 1 (by rfl) ⟨174605, by rfl⟩ : syracuseStep 232807 = 349211) B349211
theorem B396751 : Blo 231814 396751 := bstep (se 1 (by rfl) ⟨297563, by rfl⟩ : syracuseStep 396751 = 595127) B595127
theorem B233307 : Blo 231814 233307 := bstep (se 1 (by rfl) ⟨174980, by rfl⟩ : syracuseStep 233307 = 349961) B349961
theorem B233543 : Blo 231814 233543 := bstep (se 1 (by rfl) ⟨175157, by rfl⟩ : syracuseStep 233543 = 350315) B350315
theorem B233631 : Blo 231814 233631 := bstep (se 1 (by rfl) ⟨175223, by rfl⟩ : syracuseStep 233631 = 350447) B350447
theorem B233695 : Blo 231814 233695 := bstep (se 1 (by rfl) ⟨175271, by rfl⟩ : syracuseStep 233695 = 350543) B350543
theorem B528659 : Blo 231814 528659 := bstep (se 1 (by rfl) ⟨396494, by rfl⟩ : syracuseStep 528659 = 792989) B792989
theorem B234587 : Blo 231814 234587 := bstep (se 1 (by rfl) ⟨175940, by rfl⟩ : syracuseStep 234587 = 351881) B351881
theorem B234719 : Blo 231814 234719 := bstep (se 1 (by rfl) ⟨176039, by rfl⟩ : syracuseStep 234719 = 352079) B352079
theorem B234799 : Blo 231814 234799 := bstep (se 1 (by rfl) ⟨176099, by rfl⟩ : syracuseStep 234799 = 352199) B352199
theorem B3380555 : Blo 231814 3380555 := bstep (se 1 (by rfl) ⟨2535416, by rfl⟩ : syracuseStep 3380555 = 5070833) B5070833
theorem B530063 : Blo 231814 530063 := bstep (se 1 (by rfl) ⟨397547, by rfl⟩ : syracuseStep 530063 = 795095) B795095
theorem B562879 : Blo 231814 562879 := bstep (se 1 (by rfl) ⟨422159, by rfl⟩ : syracuseStep 562879 = 844319) B844319
theorem B235239 : Blo 231814 235239 := bstep (se 1 (by rfl) ⟨176429, by rfl⟩ : syracuseStep 235239 = 352859) B352859
theorem B235263 : Blo 231814 235263 := bstep (se 1 (by rfl) ⟨176447, by rfl⟩ : syracuseStep 235263 = 352895) B352895
theorem B530279 : Blo 231814 530279 := bstep (se 1 (by rfl) ⟨397709, by rfl⟩ : syracuseStep 530279 = 795419) B795419
theorem B792827 : Blo 231814 792827 := bstep (se 1 (by rfl) ⟨594620, by rfl⟩ : syracuseStep 792827 = 1189241) B1189241
theorem B1646057 : Blo 231814 1646057 := bstep (se 2 (by rfl) ⟨617271, by rfl⟩ : syracuseStep 1646057 = 1234543) B1234543
theorem B794879 : Blo 231814 794879 := bstep (se 1 (by rfl) ⟨596159, by rfl⟩ : syracuseStep 794879 = 1192319) B1192319
theorem B795041 : Blo 231814 795041 := bstep (se 2 (by rfl) ⟨298140, by rfl⟩ : syracuseStep 795041 = 596281) B596281
theorem B893375 : Blo 231814 893375 := bstep (se 1 (by rfl) ⟨670031, by rfl⟩ : syracuseStep 893375 = 1340063) B1340063
theorem B795581 : Blo 231814 795581 := bstep (se 3 (by rfl) ⟨149171, by rfl⟩ : syracuseStep 795581 = 298343) B298343
theorem B795689 : Blo 231814 795689 := bstep (se 2 (by rfl) ⟨298383, by rfl⟩ : syracuseStep 795689 = 596767) B596767
theorem B533575 : Blo 231814 533575 := bstep (se 1 (by rfl) ⟨400181, by rfl⟩ : syracuseStep 533575 = 800363) B800363
theorem B1778759 : Blo 231814 1778759 := bstep (se 1 (by rfl) ⟨1334069, by rfl⟩ : syracuseStep 1778759 = 2668139) B2668139
theorem B2827433 : Blo 231814 2827433 := bstep (se 2 (by rfl) ⟨1060287, by rfl⟩ : syracuseStep 2827433 = 2120575) B2120575
theorem B3353339 : Blo 231814 3353339 := bstep (se 1 (by rfl) ⟨2515004, by rfl⟩ : syracuseStep 3353339 = 5030009) B5030009
theorem B503743 : Blo 231814 503743 := bstep (se 1 (by rfl) ⟨377807, by rfl⟩ : syracuseStep 503743 = 755615) B755615
theorem B1814831 : Blo 231814 1814831 := bstep (se 1 (by rfl) ⟨1361123, by rfl⟩ : syracuseStep 1814831 = 2722247) B2722247
theorem B472375 : Blo 231814 472375 := bstep (se 1 (by rfl) ⟨354281, by rfl⟩ : syracuseStep 472375 = 708563) B708563
theorem B1718495 : Blo 231814 1718495 := bstep (se 1 (by rfl) ⟨1288871, by rfl⟩ : syracuseStep 1718495 = 2577743) B2577743
theorem B8141381 : Blo 231814 8141381 := bstep (se 4 (by rfl) ⟨763254, by rfl⟩ : syracuseStep 8141381 = 1526509) B1526509
theorem B5683877 : Blo 231814 5683877 := bstep (se 4 (by rfl) ⟨532863, by rfl⟩ : syracuseStep 5683877 = 1065727) B1065727
theorem B6408047 : Blo 231814 6408047 := bstep (se 1 (by rfl) ⟨4806035, by rfl⟩ : syracuseStep 6408047 = 9612071) B9612071
theorem B5131613 : Blo 231814 5131613 := bstep (se 3 (by rfl) ⟨962177, by rfl⟩ : syracuseStep 5131613 = 1924355) B1924355
theorem B348713 : Blo 231814 348713 := bstep (se 2 (by rfl) ⟨130767, by rfl⟩ : syracuseStep 348713 = 261535) B261535
theorem B348719 : Blo 231814 348719 := bstep (se 1 (by rfl) ⟨261539, by rfl⟩ : syracuseStep 348719 = 523079) B523079
theorem B1332521 : Blo 231814 1332521 := bstep (se 2 (by rfl) ⟨499695, by rfl⟩ : syracuseStep 1332521 = 999391) B999391
theorem B3036797 : Blo 231814 3036797 := bstep (se 3 (by rfl) ⟨569399, by rfl⟩ : syracuseStep 3036797 = 1138799) B1138799
theorem B1694317 : Blo 231814 1694317 := bstep (se 3 (by rfl) ⟨317684, by rfl⟩ : syracuseStep 1694317 = 635369) B635369
theorem B941863 : Blo 231814 941863 := bstep (se 1 (by rfl) ⟨706397, by rfl⟩ : syracuseStep 941863 = 1412795) B1412795
theorem B1925279 : Blo 231814 1925279 := bstep (se 1 (by rfl) ⟨1443959, by rfl⟩ : syracuseStep 1925279 = 2887919) B2887919
theorem B2122483 : Blo 231814 2122483 := bstep (se 1 (by rfl) ⟨1591862, by rfl⟩ : syracuseStep 2122483 = 3183725) B3183725
theorem B522287 : Blo 231814 522287 := bstep (se 1 (by rfl) ⟨391715, by rfl⟩ : syracuseStep 522287 = 783431) B783431
theorem B883001 : Blo 231814 883001 := bstep (se 2 (by rfl) ⟨331125, by rfl⟩ : syracuseStep 883001 = 662251) B662251
theorem B1178063 : Blo 231814 1178063 := bstep (se 1 (by rfl) ⟨883547, by rfl⟩ : syracuseStep 1178063 = 1767095) B1767095
theorem B424603 : Blo 231814 424603 := bstep (se 1 (by rfl) ⟨318452, by rfl⟩ : syracuseStep 424603 = 636905) B636905
theorem B588647 : Blo 231814 588647 := bstep (se 1 (by rfl) ⟨441485, by rfl⟩ : syracuseStep 588647 = 882971) B882971
theorem B261103 : Blo 231814 261103 := bstep (se 1 (by rfl) ⟨195827, by rfl⟩ : syracuseStep 261103 = 391655) B391655
theorem B588809 : Blo 231814 588809 := bstep (se 2 (by rfl) ⟨220803, by rfl⟩ : syracuseStep 588809 = 441607) B441607
theorem B786023 : Blo 231814 786023 := bstep (se 1 (by rfl) ⟨589517, by rfl⟩ : syracuseStep 786023 = 1179035) B1179035
theorem B1180007 : Blo 231814 1180007 := bstep (se 1 (by rfl) ⟨885005, by rfl⟩ : syracuseStep 1180007 = 1770011) B1770011
theorem B524735 : Blo 231814 524735 := bstep (se 1 (by rfl) ⟨393551, by rfl⟩ : syracuseStep 524735 = 787103) B787103
theorem B525563 : Blo 231814 525563 := bstep (se 1 (by rfl) ⟨394172, by rfl⟩ : syracuseStep 525563 = 788345) B788345
theorem B1181465 : Blo 231814 1181465 := bstep (se 2 (by rfl) ⟨443049, by rfl⟩ : syracuseStep 1181465 = 886099) B886099
theorem B395131 : Blo 231814 395131 := bstep (se 1 (by rfl) ⟨296348, by rfl⟩ : syracuseStep 395131 = 592697) B592697
theorem B526247 : Blo 231814 526247 := bstep (se 1 (by rfl) ⟨394685, by rfl⟩ : syracuseStep 526247 = 789371) B789371
theorem B526463 : Blo 231814 526463 := bstep (se 1 (by rfl) ⟨394847, by rfl⟩ : syracuseStep 526463 = 789695) B789695
theorem B396265 : Blo 231814 396265 := bstep (se 2 (by rfl) ⟨148599, by rfl⟩ : syracuseStep 396265 = 297199) B297199
theorem B232475 : Blo 231814 232475 := bstep (se 1 (by rfl) ⟨174356, by rfl⟩ : syracuseStep 232475 = 348713) B348713
theorem B232479 : Blo 231814 232479 := bstep (se 1 (by rfl) ⟨174359, by rfl⟩ : syracuseStep 232479 = 348719) B348719
theorem B888347 : Blo 231814 888347 := bstep (se 1 (by rfl) ⟨666260, by rfl⟩ : syracuseStep 888347 = 1332521) B1332521
theorem B9014813 : Blo 231814 9014813 := bstep (se 3 (by rfl) ⟨1690277, by rfl⟩ : syracuseStep 9014813 = 3380555) B3380555
theorem B528551 : Blo 231814 528551 := bstep (se 1 (by rfl) ⟨396413, by rfl⟩ : syracuseStep 528551 = 792827) B792827
theorem B529001 : Blo 231814 529001 := bstep (se 2 (by rfl) ⟨198375, by rfl⟩ : syracuseStep 529001 = 396751) B396751
theorem B1283519 : Blo 231814 1283519 := bstep (se 1 (by rfl) ⟨962639, by rfl⟩ : syracuseStep 1283519 = 1925279) B1925279
theorem B529919 : Blo 231814 529919 := bstep (se 1 (by rfl) ⟨397439, by rfl⟩ : syracuseStep 529919 = 794879) B794879
theorem B530027 : Blo 231814 530027 := bstep (se 1 (by rfl) ⟨397520, by rfl⟩ : syracuseStep 530027 = 795041) B795041
theorem B595583 : Blo 231814 595583 := bstep (se 1 (by rfl) ⟨446687, by rfl⟩ : syracuseStep 595583 = 893375) B893375
theorem B530387 : Blo 231814 530387 := bstep (se 1 (by rfl) ⟨397790, by rfl⟩ : syracuseStep 530387 = 795581) B795581
theorem B530459 : Blo 231814 530459 := bstep (se 1 (by rfl) ⟨397844, by rfl⟩ : syracuseStep 530459 = 795689) B795689
theorem B1185839 : Blo 231814 1185839 := bstep (se 1 (by rfl) ⟨889379, by rfl⟩ : syracuseStep 1185839 = 1778759) B1778759
theorem B2235559 : Blo 231814 2235559 := bstep (se 1 (by rfl) ⟨1676669, by rfl⟩ : syracuseStep 2235559 = 3353339) B3353339
theorem B566137 : Blo 231814 566137 := bstep (se 2 (by rfl) ⟨212301, by rfl⟩ : syracuseStep 566137 = 424603) B424603
theorem B1255817 : Blo 231814 1255817 := bstep (se 2 (by rfl) ⟨470931, by rfl⟩ : syracuseStep 1255817 = 941863) B941863
theorem B2829977 : Blo 231814 2829977 := bstep (se 2 (by rfl) ⟨1061241, by rfl⟩ : syracuseStep 2829977 = 2122483) B2122483
theorem B4272031 : Blo 231814 4272031 := bstep (se 1 (by rfl) ⟨3204023, by rfl⟩ : syracuseStep 4272031 = 6408047) B6408047
theorem B3780755 : Blo 231814 3780755 := bstep (se 1 (by rfl) ⟨2835566, by rfl⟩ : syracuseStep 3780755 = 5671133) B5671133
theorem B1097371 : Blo 231814 1097371 := bstep (se 1 (by rfl) ⟨823028, by rfl⟩ : syracuseStep 1097371 = 1646057) B1646057
theorem B671657 : Blo 231814 671657 := bstep (se 2 (by rfl) ⟨251871, by rfl⟩ : syracuseStep 671657 = 503743) B503743
theorem B1884955 : Blo 231814 1884955 := bstep (se 1 (by rfl) ⟨1413716, by rfl⟩ : syracuseStep 1884955 = 2827433) B2827433
theorem B13684301 : Blo 231814 13684301 := bstep (se 3 (by rfl) ⟨2565806, by rfl⟩ : syracuseStep 13684301 = 5131613) B5131613
theorem B3002021 : Blo 231814 3002021 := bstep (se 4 (by rfl) ⟨281439, by rfl⟩ : syracuseStep 3002021 = 562879) B562879
theorem B348137 : Blo 231814 348137 := bstep (se 2 (by rfl) ⟨130551, by rfl⟩ : syracuseStep 348137 = 261103) B261103
theorem B348191 : Blo 231814 348191 := bstep (se 1 (by rfl) ⟨261143, by rfl⟩ : syracuseStep 348191 = 522287) B522287
theorem B5427587 : Blo 231814 5427587 := bstep (se 1 (by rfl) ⟨4070690, by rfl⟩ : syracuseStep 5427587 = 8141381) B8141381
theorem B3789251 : Blo 231814 3789251 := bstep (se 1 (by rfl) ⟨2841938, by rfl⟩ : syracuseStep 3789251 = 5683877) B5683877
theorem B314136305 : Blo 231814 314136305 := bstep (se 2 (by rfl) ⟨117801114, by rfl⟩ : syracuseStep 314136305 = 235602229) B235602229
theorem B350699 : Blo 231814 350699 := bstep (se 1 (by rfl) ⟨263024, by rfl⟩ : syracuseStep 350699 = 526049) B526049
theorem B711433 : Blo 231814 711433 := bstep (se 2 (by rfl) ⟨266787, by rfl⟩ : syracuseStep 711433 = 533575) B533575
theorem B744623 : Blo 231814 744623 := bstep (se 1 (by rfl) ⟨558467, by rfl⟩ : syracuseStep 744623 = 1116935) B1116935
theorem B351791 : Blo 231814 351791 := bstep (se 1 (by rfl) ⟨263843, by rfl⟩ : syracuseStep 351791 = 527687) B527687
theorem B352439 : Blo 231814 352439 := bstep (se 1 (by rfl) ⟨264329, by rfl⟩ : syracuseStep 352439 = 528659) B528659
theorem B2024531 : Blo 231814 2024531 := bstep (se 1 (by rfl) ⟨1518398, by rfl⟩ : syracuseStep 2024531 = 3036797) B3036797
theorem B353375 : Blo 231814 353375 := bstep (se 1 (by rfl) ⟨265031, by rfl⟩ : syracuseStep 353375 = 530063) B530063
theorem B353519 : Blo 231814 353519 := bstep (se 1 (by rfl) ⟨265139, by rfl⟩ : syracuseStep 353519 = 530279) B530279
theorem B2519333 : Blo 231814 2519333 := bstep (se 4 (by rfl) ⟨236187, by rfl⟩ : syracuseStep 2519333 = 472375) B472375
theorem B1209887 : Blo 231814 1209887 := bstep (se 1 (by rfl) ⟨907415, by rfl⟩ : syracuseStep 1209887 = 1814831) B1814831
theorem B2259089 : Blo 231814 2259089 := bstep (se 2 (by rfl) ⟨847158, by rfl⟩ : syracuseStep 2259089 = 1694317) B1694317
theorem B1145663 : Blo 231814 1145663 := bstep (se 1 (by rfl) ⟨859247, by rfl⟩ : syracuseStep 1145663 = 1718495) B1718495
theorem B588667 : Blo 231814 588667 := bstep (se 1 (by rfl) ⟨441500, by rfl⟩ : syracuseStep 588667 = 883001) B883001
theorem B785375 : Blo 231814 785375 := bstep (se 1 (by rfl) ⟨589031, by rfl⟩ : syracuseStep 785375 = 1178063) B1178063
theorem B392431 : Blo 231814 392431 := bstep (se 1 (by rfl) ⟨294323, by rfl⟩ : syracuseStep 392431 = 588647) B588647
theorem B392539 : Blo 231814 392539 := bstep (se 1 (by rfl) ⟨294404, by rfl⟩ : syracuseStep 392539 = 588809) B588809
theorem B524015 : Blo 231814 524015 := bstep (se 1 (by rfl) ⟨393011, by rfl⟩ : syracuseStep 524015 = 786023) B786023
theorem B786671 : Blo 231814 786671 := bstep (se 1 (by rfl) ⟨590003, by rfl⟩ : syracuseStep 786671 = 1180007) B1180007
theorem B754849 : Blo 231814 754849 := bstep (se 2 (by rfl) ⟨283068, by rfl⟩ : syracuseStep 754849 = 566137) B566137
theorem B787643 : Blo 231814 787643 := bstep (se 1 (by rfl) ⟨590732, by rfl⟩ : syracuseStep 787643 = 1181465) B1181465
theorem B592231 : Blo 231814 592231 := bstep (se 1 (by rfl) ⟨444173, by rfl⟩ : syracuseStep 592231 = 888347) B888347
theorem B2001347 : Blo 231814 2001347 := bstep (se 1 (by rfl) ⟨1501010, by rfl⟩ : syracuseStep 2001347 = 3002021) B3002021
theorem B526841 : Blo 231814 526841 := bstep (se 2 (by rfl) ⟨197565, by rfl⟩ : syracuseStep 526841 = 395131) B395131
theorem B232091 : Blo 231814 232091 := bstep (se 1 (by rfl) ⟨174068, by rfl⟩ : syracuseStep 232091 = 348137) B348137
theorem B232127 : Blo 231814 232127 := bstep (se 1 (by rfl) ⟨174095, by rfl⟩ : syracuseStep 232127 = 348191) B348191
theorem B2526167 : Blo 231814 2526167 := bstep (se 1 (by rfl) ⟨1894625, by rfl⟩ : syracuseStep 2526167 = 3789251) B3789251
theorem B855679 : Blo 231814 855679 := bstep (se 1 (by rfl) ⟨641759, by rfl⟩ : syracuseStep 855679 = 1283519) B1283519
theorem B397055 : Blo 231814 397055 := bstep (se 1 (by rfl) ⟨297791, by rfl⟩ : syracuseStep 397055 = 595583) B595583
theorem B209424203 : Blo 231814 209424203 := bstep (se 1 (by rfl) ⟨157068152, by rfl⟩ : syracuseStep 209424203 = 314136305) B314136305
theorem B528353 : Blo 231814 528353 := bstep (se 2 (by rfl) ⟨198132, by rfl⟩ : syracuseStep 528353 = 396265) B396265
theorem B790559 : Blo 231814 790559 := bstep (se 1 (by rfl) ⟨592919, by rfl⟩ : syracuseStep 790559 = 1185839) B1185839
theorem B233799 : Blo 231814 233799 := bstep (se 1 (by rfl) ⟨175349, by rfl⟩ : syracuseStep 233799 = 350699) B350699
theorem B496415 : Blo 231814 496415 := bstep (se 1 (by rfl) ⟨372311, by rfl⟩ : syracuseStep 496415 = 744623) B744623
theorem B234527 : Blo 231814 234527 := bstep (se 1 (by rfl) ⟨175895, by rfl⟩ : syracuseStep 234527 = 351791) B351791
theorem B234959 : Blo 231814 234959 := bstep (se 1 (by rfl) ⟨176219, by rfl⟩ : syracuseStep 234959 = 352439) B352439
theorem B1349687 : Blo 231814 1349687 := bstep (se 1 (by rfl) ⟨1012265, by rfl⟩ : syracuseStep 1349687 = 2024531) B2024531
theorem B235583 : Blo 231814 235583 := bstep (se 1 (by rfl) ⟨176687, by rfl⟩ : syracuseStep 235583 = 353375) B353375
theorem B235679 : Blo 231814 235679 := bstep (se 1 (by rfl) ⟨176759, by rfl⟩ : syracuseStep 235679 = 353519) B353519
theorem B1679555 : Blo 231814 1679555 := bstep (se 1 (by rfl) ⟨1259666, by rfl⟩ : syracuseStep 1679555 = 2519333) B2519333
theorem B763775 : Blo 231814 763775 := bstep (se 1 (by rfl) ⟨572831, by rfl⟩ : syracuseStep 763775 = 1145663) B1145663
theorem B6009875 : Blo 231814 6009875 := bstep (se 1 (by rfl) ⟨4507406, by rfl⟩ : syracuseStep 6009875 = 9014813) B9014813
theorem B9122867 : Blo 231814 9122867 := bstep (se 1 (by rfl) ⟨6842150, by rfl⟩ : syracuseStep 9122867 = 13684301) B13684301
theorem B3618391 : Blo 231814 3618391 := bstep (se 1 (by rfl) ⟨2713793, by rfl⟩ : syracuseStep 3618391 = 5427587) B5427587
theorem B837211 : Blo 231814 837211 := bstep (se 1 (by rfl) ⟨627908, by rfl⟩ : syracuseStep 837211 = 1255817) B1255817
theorem B1886651 : Blo 231814 1886651 := bstep (se 1 (by rfl) ⟨1414988, by rfl⟩ : syracuseStep 1886651 = 2829977) B2829977
theorem B5852645 : Blo 231814 5852645 := bstep (se 4 (by rfl) ⟨548685, by rfl⟩ : syracuseStep 5852645 = 1097371) B1097371
theorem B806591 : Blo 231814 806591 := bstep (se 1 (by rfl) ⟨604943, by rfl⟩ : syracuseStep 806591 = 1209887) B1209887
theorem B1791085 : Blo 231814 1791085 := bstep (se 3 (by rfl) ⟨335828, by rfl⟩ : syracuseStep 1791085 = 671657) B671657
theorem B349343 : Blo 231814 349343 := bstep (se 1 (by rfl) ⟨262007, by rfl⟩ : syracuseStep 349343 = 524015) B524015
theorem B349823 : Blo 231814 349823 := bstep (se 1 (by rfl) ⟨262367, by rfl⟩ : syracuseStep 349823 = 524735) B524735
theorem B350375 : Blo 231814 350375 := bstep (se 1 (by rfl) ⟨262781, by rfl⟩ : syracuseStep 350375 = 525563) B525563
theorem B2513273 : Blo 231814 2513273 := bstep (se 2 (by rfl) ⟨942477, by rfl⟩ : syracuseStep 2513273 = 1884955) B1884955
theorem B350831 : Blo 231814 350831 := bstep (se 1 (by rfl) ⟨263123, by rfl⟩ : syracuseStep 350831 = 526247) B526247
theorem B350975 : Blo 231814 350975 := bstep (se 1 (by rfl) ⟨263231, by rfl⟩ : syracuseStep 350975 = 526463) B526463
theorem B352367 : Blo 231814 352367 := bstep (se 1 (by rfl) ⟨264275, by rfl⟩ : syracuseStep 352367 = 528551) B528551
theorem B352667 : Blo 231814 352667 := bstep (se 1 (by rfl) ⟨264500, by rfl⟩ : syracuseStep 352667 = 529001) B529001
theorem B353279 : Blo 231814 353279 := bstep (se 1 (by rfl) ⟨264959, by rfl⟩ : syracuseStep 353279 = 529919) B529919
theorem B353351 : Blo 231814 353351 := bstep (se 1 (by rfl) ⟨265013, by rfl⟩ : syracuseStep 353351 = 530027) B530027
theorem B353591 : Blo 231814 353591 := bstep (se 1 (by rfl) ⟨265193, by rfl⟩ : syracuseStep 353591 = 530387) B530387
theorem B353639 : Blo 231814 353639 := bstep (se 1 (by rfl) ⟨265229, by rfl⟩ : syracuseStep 353639 = 530459) B530459
theorem B3794309 : Blo 231814 3794309 := bstep (se 4 (by rfl) ⟨355716, by rfl⟩ : syracuseStep 3794309 = 711433) B711433
theorem B5696041 : Blo 231814 5696041 := bstep (se 2 (by rfl) ⟨2136015, by rfl⟩ : syracuseStep 5696041 = 4272031) B4272031
theorem B2520503 : Blo 231814 2520503 := bstep (se 1 (by rfl) ⟨1890377, by rfl⟩ : syracuseStep 2520503 = 3780755) B3780755
theorem B784889 : Blo 231814 784889 := bstep (se 2 (by rfl) ⟨294333, by rfl⟩ : syracuseStep 784889 = 588667) B588667
theorem B1506059 : Blo 231814 1506059 := bstep (se 1 (by rfl) ⟨1129544, by rfl⟩ : syracuseStep 1506059 = 2259089) B2259089
theorem B2980745 : Blo 231814 2980745 := bstep (se 2 (by rfl) ⟨1117779, by rfl⟩ : syracuseStep 2980745 = 2235559) B2235559
theorem B523241 : Blo 231814 523241 := bstep (se 2 (by rfl) ⟨196215, by rfl⟩ : syracuseStep 523241 = 392431) B392431
theorem B523385 : Blo 231814 523385 := bstep (se 2 (by rfl) ⟨196269, by rfl⟩ : syracuseStep 523385 = 392539) B392539
theorem B523583 : Blo 231814 523583 := bstep (se 1 (by rfl) ⟨392687, by rfl⟩ : syracuseStep 523583 = 785375) B785375
theorem B524447 : Blo 231814 524447 := bstep (se 1 (by rfl) ⟨393335, by rfl⟩ : syracuseStep 524447 = 786671) B786671
theorem B525095 : Blo 231814 525095 := bstep (se 1 (by rfl) ⟨393821, by rfl⟩ : syracuseStep 525095 = 787643) B787643
theorem B1116281 : Blo 231814 1116281 := bstep (se 2 (by rfl) ⟨418605, by rfl⟩ : syracuseStep 1116281 = 837211) B837211
theorem B3901763 : Blo 231814 3901763 := bstep (se 1 (by rfl) ⟨2926322, by rfl⟩ : syracuseStep 3901763 = 5852645) B5852645
theorem B264703 : Blo 231814 264703 := bstep (se 1 (by rfl) ⟨198527, by rfl⟩ : syracuseStep 264703 = 397055) B397055
theorem B527039 : Blo 231814 527039 := bstep (se 1 (by rfl) ⟨395279, by rfl⟩ : syracuseStep 527039 = 790559) B790559
theorem B789641 : Blo 231814 789641 := bstep (se 2 (by rfl) ⟨296115, by rfl⟩ : syracuseStep 789641 = 592231) B592231
theorem B232895 : Blo 231814 232895 := bstep (se 1 (by rfl) ⟨174671, by rfl⟩ : syracuseStep 232895 = 349343) B349343
theorem B233215 : Blo 231814 233215 := bstep (se 1 (by rfl) ⟨174911, by rfl⟩ : syracuseStep 233215 = 349823) B349823
theorem B233583 : Blo 231814 233583 := bstep (se 1 (by rfl) ⟨175187, by rfl⟩ : syracuseStep 233583 = 350375) B350375
theorem B233887 : Blo 231814 233887 := bstep (se 1 (by rfl) ⟨175415, by rfl⟩ : syracuseStep 233887 = 350831) B350831
theorem B233983 : Blo 231814 233983 := bstep (se 1 (by rfl) ⟨175487, by rfl⟩ : syracuseStep 233983 = 350975) B350975
theorem B234911 : Blo 231814 234911 := bstep (se 1 (by rfl) ⟨176183, by rfl⟩ : syracuseStep 234911 = 352367) B352367
theorem B1119703 : Blo 231814 1119703 := bstep (se 1 (by rfl) ⟨839777, by rfl⟩ : syracuseStep 1119703 = 1679555) B1679555
theorem B235111 : Blo 231814 235111 := bstep (se 1 (by rfl) ⟨176333, by rfl⟩ : syracuseStep 235111 = 352667) B352667
theorem B235519 : Blo 231814 235519 := bstep (se 1 (by rfl) ⟨176639, by rfl⟩ : syracuseStep 235519 = 353279) B353279
theorem B235567 : Blo 231814 235567 := bstep (se 1 (by rfl) ⟨176675, by rfl⟩ : syracuseStep 235567 = 353351) B353351
theorem B235727 : Blo 231814 235727 := bstep (se 1 (by rfl) ⟨176795, by rfl⟩ : syracuseStep 235727 = 353591) B353591
theorem B235759 : Blo 231814 235759 := bstep (se 1 (by rfl) ⟨176819, by rfl⟩ : syracuseStep 235759 = 353639) B353639
theorem B2529539 : Blo 231814 2529539 := bstep (se 1 (by rfl) ⟨1897154, by rfl⟩ : syracuseStep 2529539 = 3794309) B3794309
theorem B4824521 : Blo 231814 4824521 := bstep (se 2 (by rfl) ⟨1809195, by rfl⟩ : syracuseStep 4824521 = 3618391) B3618391
theorem B4006583 : Blo 231814 4006583 := bstep (se 1 (by rfl) ⟨3004937, by rfl⟩ : syracuseStep 4006583 = 6009875) B6009875
theorem B1680335 : Blo 231814 1680335 := bstep (se 1 (by rfl) ⟨1260251, by rfl⟩ : syracuseStep 1680335 = 2520503) B2520503
theorem B1257767 : Blo 231814 1257767 := bstep (se 1 (by rfl) ⟨943325, by rfl⟩ : syracuseStep 1257767 = 1886651) B1886651
theorem B1684111 : Blo 231814 1684111 := bstep (se 1 (by rfl) ⟨1263083, by rfl⟩ : syracuseStep 1684111 = 2526167) B2526167
theorem B1323773 : Blo 231814 1323773 := bstep (se 3 (by rfl) ⟨248207, by rfl⟩ : syracuseStep 1323773 = 496415) B496415
theorem B537727 : Blo 231814 537727 := bstep (se 1 (by rfl) ⟨403295, by rfl⟩ : syracuseStep 537727 = 806591) B806591
theorem B899791 : Blo 231814 899791 := bstep (se 1 (by rfl) ⟨674843, by rfl⟩ : syracuseStep 899791 = 1349687) B1349687
theorem B6702061 : Blo 231814 6702061 := bstep (se 3 (by rfl) ⟨1256636, by rfl⟩ : syracuseStep 6702061 = 2513273) B2513273
theorem B509183 : Blo 231814 509183 := bstep (se 1 (by rfl) ⟨381887, by rfl⟩ : syracuseStep 509183 = 763775) B763775
theorem B6081911 : Blo 231814 6081911 := bstep (se 1 (by rfl) ⟨4561433, by rfl⟩ : syracuseStep 6081911 = 9122867) B9122867
theorem B1004039 : Blo 231814 1004039 := bstep (se 1 (by rfl) ⟨753029, by rfl⟩ : syracuseStep 1004039 = 1506059) B1506059
theorem B1987163 : Blo 231814 1987163 := bstep (se 1 (by rfl) ⟨1490372, by rfl⟩ : syracuseStep 1987163 = 2980745) B2980745
theorem B348827 : Blo 231814 348827 := bstep (se 1 (by rfl) ⟨261620, by rfl⟩ : syracuseStep 348827 = 523241) B523241
theorem B348923 : Blo 231814 348923 := bstep (se 1 (by rfl) ⟨261692, by rfl⟩ : syracuseStep 348923 = 523385) B523385
theorem B349055 : Blo 231814 349055 := bstep (se 1 (by rfl) ⟨261791, by rfl⟩ : syracuseStep 349055 = 523583) B523583
theorem B1006465 : Blo 231814 1006465 := bstep (se 2 (by rfl) ⟨377424, by rfl⟩ : syracuseStep 1006465 = 754849) B754849
theorem B1334231 : Blo 231814 1334231 := bstep (se 1 (by rfl) ⟨1000673, by rfl⟩ : syracuseStep 1334231 = 2001347) B2001347
theorem B351227 : Blo 231814 351227 := bstep (se 1 (by rfl) ⟨263420, by rfl⟩ : syracuseStep 351227 = 526841) B526841
theorem B139616135 : Blo 231814 139616135 := bstep (se 1 (by rfl) ⟨104712101, by rfl⟩ : syracuseStep 139616135 = 209424203) B209424203
theorem B352235 : Blo 231814 352235 := bstep (se 1 (by rfl) ⟨264176, by rfl⟩ : syracuseStep 352235 = 528353) B528353
theorem B7594721 : Blo 231814 7594721 := bstep (se 2 (by rfl) ⟨2848020, by rfl⟩ : syracuseStep 7594721 = 5696041) B5696041
theorem B1140905 : Blo 231814 1140905 := bstep (se 2 (by rfl) ⟨427839, by rfl⟩ : syracuseStep 1140905 = 855679) B855679
theorem B2388113 : Blo 231814 2388113 := bstep (se 2 (by rfl) ⟨895542, by rfl⟩ : syracuseStep 2388113 = 1791085) B1791085
theorem B523259 : Blo 231814 523259 := bstep (se 1 (by rfl) ⟨392444, by rfl⟩ : syracuseStep 523259 = 784889) B784889
theorem B526427 : Blo 231814 526427 := bstep (se 1 (by rfl) ⟨394820, by rfl⟩ : syracuseStep 526427 = 789641) B789641
theorem B232551 : Blo 231814 232551 := bstep (se 1 (by rfl) ⟨174413, by rfl⟩ : syracuseStep 232551 = 348827) B348827
theorem B232615 : Blo 231814 232615 := bstep (se 1 (by rfl) ⟨174461, by rfl⟩ : syracuseStep 232615 = 348923) B348923
theorem B232703 : Blo 231814 232703 := bstep (se 1 (by rfl) ⟨174527, by rfl⟩ : syracuseStep 232703 = 349055) B349055
theorem B889487 : Blo 231814 889487 := bstep (se 1 (by rfl) ⟨667115, by rfl⟩ : syracuseStep 889487 = 1334231) B1334231
theorem B234151 : Blo 231814 234151 := bstep (se 1 (by rfl) ⟨175613, by rfl⟩ : syracuseStep 234151 = 351227) B351227
theorem B3216347 : Blo 231814 3216347 := bstep (se 1 (by rfl) ⟨2412260, by rfl⟩ : syracuseStep 3216347 = 4824521) B4824521
theorem B234823 : Blo 231814 234823 := bstep (se 1 (by rfl) ⟨176117, by rfl⟩ : syracuseStep 234823 = 352235) B352235
theorem B1120223 : Blo 231814 1120223 := bstep (se 1 (by rfl) ⟨840167, by rfl⟩ : syracuseStep 1120223 = 1680335) B1680335
theorem B760603 : Blo 231814 760603 := bstep (se 1 (by rfl) ⟨570452, by rfl⟩ : syracuseStep 760603 = 1140905) B1140905
theorem B339455 : Blo 231814 339455 := bstep (se 1 (by rfl) ⟨254591, by rfl⟩ : syracuseStep 339455 = 509183) B509183
theorem B2601175 : Blo 231814 2601175 := bstep (se 1 (by rfl) ⟨1950881, by rfl⟩ : syracuseStep 2601175 = 3901763) B3901763
theorem B669359 : Blo 231814 669359 := bstep (se 1 (by rfl) ⟨502019, by rfl⟩ : syracuseStep 669359 = 1004039) B1004039
theorem B1324775 : Blo 231814 1324775 := bstep (se 1 (by rfl) ⟨993581, by rfl⟩ : syracuseStep 1324775 = 1987163) B1987163
theorem B1686359 : Blo 231814 1686359 := bstep (se 1 (by rfl) ⟨1264769, by rfl⟩ : syracuseStep 1686359 = 2529539) B2529539
theorem B93077423 : Blo 231814 93077423 := bstep (se 1 (by rfl) ⟨69808067, by rfl⟩ : syracuseStep 93077423 = 139616135) B139616135
theorem B2671055 : Blo 231814 2671055 := bstep (se 1 (by rfl) ⟨2003291, by rfl⟩ : syracuseStep 2671055 = 4006583) B4006583
theorem B5063147 : Blo 231814 5063147 := bstep (se 1 (by rfl) ⟨3797360, by rfl⟩ : syracuseStep 5063147 = 7594721) B7594721
theorem B2245481 : Blo 231814 2245481 := bstep (se 2 (by rfl) ⟨842055, by rfl⟩ : syracuseStep 2245481 = 1684111) B1684111
theorem B1492937 : Blo 231814 1492937 := bstep (se 2 (by rfl) ⟨559851, by rfl⟩ : syracuseStep 1492937 = 1119703) B1119703
theorem B1592075 : Blo 231814 1592075 := bstep (se 1 (by rfl) ⟨1194056, by rfl⟩ : syracuseStep 1592075 = 2388113) B2388113
theorem B838511 : Blo 231814 838511 := bstep (se 1 (by rfl) ⟨628883, by rfl⟩ : syracuseStep 838511 = 1257767) B1257767
theorem B348839 : Blo 231814 348839 := bstep (se 1 (by rfl) ⟨261629, by rfl⟩ : syracuseStep 348839 = 523259) B523259
theorem B349631 : Blo 231814 349631 := bstep (se 1 (by rfl) ⟨262223, by rfl⟩ : syracuseStep 349631 = 524447) B524447
theorem B350063 : Blo 231814 350063 := bstep (se 1 (by rfl) ⟨262547, by rfl⟩ : syracuseStep 350063 = 525095) B525095
theorem B8936081 : Blo 231814 8936081 := bstep (se 2 (by rfl) ⟨3351030, by rfl⟩ : syracuseStep 8936081 = 6702061) B6702061
theorem B351359 : Blo 231814 351359 := bstep (se 1 (by rfl) ⟨263519, by rfl⟩ : syracuseStep 351359 = 527039) B527039
theorem B4054607 : Blo 231814 4054607 := bstep (se 1 (by rfl) ⟨3040955, by rfl⟩ : syracuseStep 4054607 = 6081911) B6081911
theorem B352937 : Blo 231814 352937 := bstep (se 2 (by rfl) ⟨132351, by rfl⟩ : syracuseStep 352937 = 264703) B264703
theorem B19195541 : Blo 231814 19195541 := bstep (se 6 (by rfl) ⟨449895, by rfl⟩ : syracuseStep 19195541 = 899791) B899791
theorem B2976749 : Blo 231814 2976749 := bstep (se 3 (by rfl) ⟨558140, by rfl⟩ : syracuseStep 2976749 = 1116281) B1116281
theorem B716969 : Blo 231814 716969 := bstep (se 2 (by rfl) ⟨268863, by rfl⟩ : syracuseStep 716969 = 537727) B537727
theorem B882515 : Blo 231814 882515 := bstep (se 1 (by rfl) ⟨661886, by rfl⟩ : syracuseStep 882515 = 1323773) B1323773
theorem B1341953 : Blo 231814 1341953 := bstep (se 2 (by rfl) ⟨503232, by rfl⟩ : syracuseStep 1341953 = 1006465) B1006465
theorem B3375431 : Blo 231814 3375431 := bstep (se 1 (by rfl) ⟨2531573, by rfl⟩ : syracuseStep 3375431 = 5063147) B5063147
theorem B559007 : Blo 231814 559007 := bstep (se 1 (by rfl) ⟨419255, by rfl⟩ : syracuseStep 559007 = 838511) B838511
theorem B592991 : Blo 231814 592991 := bstep (se 1 (by rfl) ⟨444743, by rfl⟩ : syracuseStep 592991 = 889487) B889487
theorem B232559 : Blo 231814 232559 := bstep (se 1 (by rfl) ⟨174419, by rfl⟩ : syracuseStep 232559 = 348839) B348839
theorem B233087 : Blo 231814 233087 := bstep (se 1 (by rfl) ⟨174815, by rfl⟩ : syracuseStep 233087 = 349631) B349631
theorem B233375 : Blo 231814 233375 := bstep (se 1 (by rfl) ⟨175031, by rfl⟩ : syracuseStep 233375 = 350063) B350063
theorem B234239 : Blo 231814 234239 := bstep (se 1 (by rfl) ⟨175679, by rfl⟩ : syracuseStep 234239 = 351359) B351359
theorem B235291 : Blo 231814 235291 := bstep (se 1 (by rfl) ⟨176468, by rfl⟩ : syracuseStep 235291 = 352937) B352937
theorem B894635 : Blo 231814 894635 := bstep (se 1 (by rfl) ⟨670976, by rfl⟩ : syracuseStep 894635 = 1341953) B1341953
theorem B1124239 : Blo 231814 1124239 := bstep (se 1 (by rfl) ⟨843179, by rfl⟩ : syracuseStep 1124239 = 1686359) B1686359
theorem B1780703 : Blo 231814 1780703 := bstep (se 1 (by rfl) ⟨1335527, by rfl⟩ : syracuseStep 1780703 = 2671055) B2671055
theorem B1911917 : Blo 231814 1911917 := bstep (se 3 (by rfl) ⟨358484, by rfl⟩ : syracuseStep 1911917 = 716969) B716969
theorem B995291 : Blo 231814 995291 := bstep (se 1 (by rfl) ⟨746468, by rfl⟩ : syracuseStep 995291 = 1492937) B1492937
theorem B2144231 : Blo 231814 2144231 := bstep (se 1 (by rfl) ⟨1608173, by rfl⟩ : syracuseStep 2144231 = 3216347) B3216347
theorem B2703071 : Blo 231814 2703071 := bstep (se 1 (by rfl) ⟨2027303, by rfl⟩ : syracuseStep 2703071 = 4054607) B4054607
theorem B12797027 : Blo 231814 12797027 := bstep (se 1 (by rfl) ⟨9597770, by rfl⟩ : syracuseStep 12797027 = 19195541) B19195541
theorem B1984499 : Blo 231814 1984499 := bstep (se 1 (by rfl) ⟨1488374, by rfl⟩ : syracuseStep 1984499 = 2976749) B2976749
theorem B4245533 : Blo 231814 4245533 := bstep (se 3 (by rfl) ⟨796037, by rfl⟩ : syracuseStep 4245533 = 1592075) B1592075
theorem B446239 : Blo 231814 446239 := bstep (se 1 (by rfl) ⟨334679, by rfl⟩ : syracuseStep 446239 = 669359) B669359
theorem B905213 : Blo 231814 905213 := bstep (se 3 (by rfl) ⟨169727, by rfl⟩ : syracuseStep 905213 = 339455) B339455
theorem B62051615 : Blo 231814 62051615 := bstep (se 1 (by rfl) ⟨46538711, by rfl⟩ : syracuseStep 62051615 = 93077423) B93077423
theorem B1496987 : Blo 231814 1496987 := bstep (se 1 (by rfl) ⟨1122740, by rfl⟩ : syracuseStep 1496987 = 2245481) B2245481
theorem B350951 : Blo 231814 350951 := bstep (se 1 (by rfl) ⟨263213, by rfl⟩ : syracuseStep 350951 = 526427) B526427
theorem B746815 : Blo 231814 746815 := bstep (se 1 (by rfl) ⟨560111, by rfl⟩ : syracuseStep 746815 = 1120223) B1120223
theorem B5957387 : Blo 231814 5957387 := bstep (se 1 (by rfl) ⟨4468040, by rfl⟩ : syracuseStep 5957387 = 8936081) B8936081
theorem B3468233 : Blo 231814 3468233 := bstep (se 2 (by rfl) ⟨1300587, by rfl⟩ : syracuseStep 3468233 = 2601175) B2601175
theorem B1014137 : Blo 231814 1014137 := bstep (se 2 (by rfl) ⟨380301, by rfl⟩ : syracuseStep 1014137 = 760603) B760603
theorem B883183 : Blo 231814 883183 := bstep (se 1 (by rfl) ⟨662387, by rfl⟩ : syracuseStep 883183 = 1324775) B1324775
theorem B588343 : Blo 231814 588343 := bstep (se 1 (by rfl) ⟨441257, by rfl⟩ : syracuseStep 588343 = 882515) B882515
theorem B395327 : Blo 231814 395327 := bstep (se 1 (by rfl) ⟨296495, by rfl⟩ : syracuseStep 395327 = 592991) B592991
theorem B233967 : Blo 231814 233967 := bstep (se 1 (by rfl) ⟨175475, by rfl⟩ : syracuseStep 233967 = 350951) B350951
theorem B594985 : Blo 231814 594985 := bstep (se 2 (by rfl) ⟨223119, by rfl⟩ : syracuseStep 594985 = 446239) B446239
theorem B596423 : Blo 231814 596423 := bstep (se 1 (by rfl) ⟨447317, by rfl⟩ : syracuseStep 596423 = 894635) B894635
theorem B3971591 : Blo 231814 3971591 := bstep (se 1 (by rfl) ⟨2978693, by rfl⟩ : syracuseStep 3971591 = 5957387) B5957387
theorem B1187135 : Blo 231814 1187135 := bstep (se 1 (by rfl) ⟨890351, by rfl⟩ : syracuseStep 1187135 = 1780703) B1780703
theorem B663527 : Blo 231814 663527 := bstep (se 1 (by rfl) ⟨497645, by rfl⟩ : syracuseStep 663527 = 995291) B995291
theorem B8531351 : Blo 231814 8531351 := bstep (se 1 (by rfl) ⟨6398513, by rfl⟩ : syracuseStep 8531351 = 12797027) B12797027
theorem B372671 : Blo 231814 372671 := bstep (se 1 (by rfl) ⟨279503, by rfl⟩ : syracuseStep 372671 = 559007) B559007
theorem B1322999 : Blo 231814 1322999 := bstep (se 1 (by rfl) ⟨992249, by rfl⟩ : syracuseStep 1322999 = 1984499) B1984499
theorem B2830355 : Blo 231814 2830355 := bstep (se 1 (by rfl) ⟨2122766, by rfl⟩ : syracuseStep 2830355 = 4245533) B4245533
theorem B995753 : Blo 231814 995753 := bstep (se 2 (by rfl) ⟨373407, by rfl⟩ : syracuseStep 995753 = 746815) B746815
theorem B41367743 : Blo 231814 41367743 := bstep (se 1 (by rfl) ⟨31025807, by rfl⟩ : syracuseStep 41367743 = 62051615) B62051615
theorem B997991 : Blo 231814 997991 := bstep (se 1 (by rfl) ⟨748493, by rfl⟩ : syracuseStep 997991 = 1496987) B1496987
theorem B2312155 : Blo 231814 2312155 := bstep (se 1 (by rfl) ⟨1734116, by rfl⟩ : syracuseStep 2312155 = 3468233) B3468233
theorem B1429487 : Blo 231814 1429487 := bstep (se 1 (by rfl) ⟨1072115, by rfl⟩ : syracuseStep 1429487 = 2144231) B2144231
theorem B676091 : Blo 231814 676091 := bstep (se 1 (by rfl) ⟨507068, by rfl⟩ : syracuseStep 676091 = 1014137) B1014137
theorem B2413901 : Blo 231814 2413901 := bstep (se 3 (by rfl) ⟨452606, by rfl⟩ : syracuseStep 2413901 = 905213) B905213
theorem B2250287 : Blo 231814 2250287 := bstep (se 1 (by rfl) ⟨1687715, by rfl⟩ : syracuseStep 2250287 = 3375431) B3375431
theorem B1498985 : Blo 231814 1498985 := bstep (se 2 (by rfl) ⟨562119, by rfl⟩ : syracuseStep 1498985 = 1124239) B1124239
theorem B1274611 : Blo 231814 1274611 := bstep (se 1 (by rfl) ⟨955958, by rfl⟩ : syracuseStep 1274611 = 1911917) B1911917
theorem B1177577 : Blo 231814 1177577 := bstep (se 2 (by rfl) ⟨441591, by rfl⟩ : syracuseStep 1177577 = 883183) B883183
theorem B784457 : Blo 231814 784457 := bstep (se 2 (by rfl) ⟨294171, by rfl⟩ : syracuseStep 784457 = 588343) B588343
theorem B1802047 : Blo 231814 1802047 := bstep (se 1 (by rfl) ⟨1351535, by rfl⟩ : syracuseStep 1802047 = 2703071) B2703071
theorem B263551 : Blo 231814 263551 := bstep (se 1 (by rfl) ⟨197663, by rfl⟩ : syracuseStep 263551 = 395327) B395327
theorem B3082873 : Blo 231814 3082873 := bstep (se 2 (by rfl) ⟨1156077, by rfl⟩ : syracuseStep 3082873 = 2312155) B2312155
theorem B952991 : Blo 231814 952991 := bstep (se 1 (by rfl) ⟨714743, by rfl⟩ : syracuseStep 952991 = 1429487) B1429487
theorem B1609267 : Blo 231814 1609267 := bstep (se 1 (by rfl) ⟨1206950, by rfl⟩ : syracuseStep 1609267 = 2413901) B2413901
theorem B397615 : Blo 231814 397615 := bstep (se 1 (by rfl) ⟨298211, by rfl⟩ : syracuseStep 397615 = 596423) B596423
theorem B791423 : Blo 231814 791423 := bstep (se 1 (by rfl) ⟨593567, by rfl⟩ : syracuseStep 791423 = 1187135) B1187135
theorem B793313 : Blo 231814 793313 := bstep (se 2 (by rfl) ⟨297492, by rfl⟩ : syracuseStep 793313 = 594985) B594985
theorem B663835 : Blo 231814 663835 := bstep (se 1 (by rfl) ⟨497876, by rfl⟩ : syracuseStep 663835 = 995753) B995753
theorem B665327 : Blo 231814 665327 := bstep (se 1 (by rfl) ⟨498995, by rfl⟩ : syracuseStep 665327 = 997991) B997991
theorem B2402729 : Blo 231814 2402729 := bstep (se 2 (by rfl) ⟨901023, by rfl⟩ : syracuseStep 2402729 = 1802047) B1802047
theorem B999323 : Blo 231814 999323 := bstep (se 1 (by rfl) ⟨749492, by rfl⟩ : syracuseStep 999323 = 1498985) B1498985
theorem B442351 : Blo 231814 442351 := bstep (se 1 (by rfl) ⟨331763, by rfl⟩ : syracuseStep 442351 = 663527) B663527
theorem B5687567 : Blo 231814 5687567 := bstep (se 1 (by rfl) ⟨4265675, by rfl⟩ : syracuseStep 5687567 = 8531351) B8531351
theorem B248447 : Blo 231814 248447 := bstep (se 1 (by rfl) ⟨186335, by rfl⟩ : syracuseStep 248447 = 372671) B372671
theorem B1886903 : Blo 231814 1886903 := bstep (se 1 (by rfl) ⟨1415177, by rfl⟩ : syracuseStep 1886903 = 2830355) B2830355
theorem B27578495 : Blo 231814 27578495 := bstep (se 1 (by rfl) ⟨20683871, by rfl⟩ : syracuseStep 27578495 = 41367743) B41367743
theorem B450727 : Blo 231814 450727 := bstep (se 1 (by rfl) ⟨338045, by rfl⟩ : syracuseStep 450727 = 676091) B676091
theorem B1500191 : Blo 231814 1500191 := bstep (se 1 (by rfl) ⟨1125143, by rfl⟩ : syracuseStep 1500191 = 2250287) B2250287
theorem B2647727 : Blo 231814 2647727 := bstep (se 1 (by rfl) ⟨1985795, by rfl⟩ : syracuseStep 2647727 = 3971591) B3971591
theorem B1699481 : Blo 231814 1699481 := bstep (se 2 (by rfl) ⟨637305, by rfl⟩ : syracuseStep 1699481 = 1274611) B1274611
theorem B881999 : Blo 231814 881999 := bstep (se 1 (by rfl) ⟨661499, by rfl⟩ : syracuseStep 881999 = 1322999) B1322999
theorem B785051 : Blo 231814 785051 := bstep (se 1 (by rfl) ⟨588788, by rfl⟩ : syracuseStep 785051 = 1177577) B1177577
theorem B522971 : Blo 231814 522971 := bstep (se 1 (by rfl) ⟨392228, by rfl⟩ : syracuseStep 522971 = 784457) B784457
theorem B885113 : Blo 231814 885113 := bstep (se 2 (by rfl) ⟨331917, by rfl⟩ : syracuseStep 885113 = 663835) B663835
theorem B18385663 : Blo 231814 18385663 := bstep (se 1 (by rfl) ⟨13789247, by rfl⟩ : syracuseStep 18385663 = 27578495) B27578495
theorem B527615 : Blo 231814 527615 := bstep (se 1 (by rfl) ⟨395711, by rfl⟩ : syracuseStep 527615 = 791423) B791423
theorem B528875 : Blo 231814 528875 := bstep (se 1 (by rfl) ⟨396656, by rfl⟩ : syracuseStep 528875 = 793313) B793313
theorem B530153 : Blo 231814 530153 := bstep (se 2 (by rfl) ⟨198807, by rfl⟩ : syracuseStep 530153 = 397615) B397615
theorem B662525 : Blo 231814 662525 := bstep (se 3 (by rfl) ⟨124223, by rfl⟩ : syracuseStep 662525 = 248447) B248447
theorem B666215 : Blo 231814 666215 := bstep (se 1 (by rfl) ⟨499661, by rfl⟩ : syracuseStep 666215 = 999323) B999323
theorem B635327 : Blo 231814 635327 := bstep (se 1 (by rfl) ⟨476495, by rfl⟩ : syracuseStep 635327 = 952991) B952991
theorem B1257935 : Blo 231814 1257935 := bstep (se 1 (by rfl) ⟨943451, by rfl⟩ : syracuseStep 1257935 = 1886903) B1886903
theorem B9615509 : Blo 231814 9615509 := bstep (se 6 (by rfl) ⟨225363, by rfl⟩ : syracuseStep 9615509 = 450727) B450727
theorem B4110497 : Blo 231814 4110497 := bstep (se 2 (by rfl) ⟨1541436, by rfl⟩ : syracuseStep 4110497 = 3082873) B3082873
theorem B2145689 : Blo 231814 2145689 := bstep (se 2 (by rfl) ⟨804633, by rfl⟩ : syracuseStep 2145689 = 1609267) B1609267
theorem B1000127 : Blo 231814 1000127 := bstep (se 1 (by rfl) ⟨750095, by rfl⟩ : syracuseStep 1000127 = 1500191) B1500191
theorem B443551 : Blo 231814 443551 := bstep (se 1 (by rfl) ⟨332663, by rfl⟩ : syracuseStep 443551 = 665327) B665327
theorem B1132987 : Blo 231814 1132987 := bstep (se 1 (by rfl) ⟨849740, by rfl⟩ : syracuseStep 1132987 = 1699481) B1699481
theorem B348647 : Blo 231814 348647 := bstep (se 1 (by rfl) ⟨261485, by rfl⟩ : syracuseStep 348647 = 522971) B522971
theorem B3791711 : Blo 231814 3791711 := bstep (se 1 (by rfl) ⟨2843783, by rfl⟩ : syracuseStep 3791711 = 5687567) B5687567
theorem B351401 : Blo 231814 351401 := bstep (se 2 (by rfl) ⟨131775, by rfl⟩ : syracuseStep 351401 = 263551) B263551
theorem B1765151 : Blo 231814 1765151 := bstep (se 1 (by rfl) ⟨1323863, by rfl⟩ : syracuseStep 1765151 = 2647727) B2647727
theorem B1601819 : Blo 231814 1601819 := bstep (se 1 (by rfl) ⟨1201364, by rfl⟩ : syracuseStep 1601819 = 2402729) B2402729
theorem B587999 : Blo 231814 587999 := bstep (se 1 (by rfl) ⟨440999, by rfl⟩ : syracuseStep 587999 = 881999) B881999
theorem B523367 : Blo 231814 523367 := bstep (se 1 (by rfl) ⟨392525, by rfl⟩ : syracuseStep 523367 = 785051) B785051
theorem B589801 : Blo 231814 589801 := bstep (se 2 (by rfl) ⟨221175, by rfl⟩ : syracuseStep 589801 = 442351) B442351
theorem B590075 : Blo 231814 590075 := bstep (se 1 (by rfl) ⟨442556, by rfl⟩ : syracuseStep 590075 = 885113) B885113
theorem B591401 : Blo 231814 591401 := bstep (se 2 (by rfl) ⟨221775, by rfl⟩ : syracuseStep 591401 = 443551) B443551
theorem B232431 : Blo 231814 232431 := bstep (se 1 (by rfl) ⟨174323, by rfl⟩ : syracuseStep 232431 = 348647) B348647
theorem B1510649 : Blo 231814 1510649 := bstep (se 2 (by rfl) ⟨566493, by rfl⟩ : syracuseStep 1510649 = 1132987) B1132987
theorem B24514217 : Blo 231814 24514217 := bstep (se 2 (by rfl) ⟨9192831, by rfl⟩ : syracuseStep 24514217 = 18385663) B18385663
theorem B2527807 : Blo 231814 2527807 := bstep (se 1 (by rfl) ⟨1895855, by rfl⟩ : syracuseStep 2527807 = 3791711) B3791711
theorem B234267 : Blo 231814 234267 := bstep (se 1 (by rfl) ⟨175700, by rfl⟩ : syracuseStep 234267 = 351401) B351401
theorem B666751 : Blo 231814 666751 := bstep (se 1 (by rfl) ⟨500063, by rfl⟩ : syracuseStep 666751 = 1000127) B1000127
theorem B3354493 : Blo 231814 3354493 := bstep (se 3 (by rfl) ⟨628967, by rfl⟩ : syracuseStep 3354493 = 1257935) B1257935
theorem B441683 : Blo 231814 441683 := bstep (se 1 (by rfl) ⟨331262, by rfl⟩ : syracuseStep 441683 = 662525) B662525
theorem B444143 : Blo 231814 444143 := bstep (se 1 (by rfl) ⟨333107, by rfl⟩ : syracuseStep 444143 = 666215) B666215
theorem B1067879 : Blo 231814 1067879 := bstep (se 1 (by rfl) ⟨800909, by rfl⟩ : syracuseStep 1067879 = 1601819) B1601819
theorem B6410339 : Blo 231814 6410339 := bstep (se 1 (by rfl) ⟨4807754, by rfl⟩ : syracuseStep 6410339 = 9615509) B9615509
theorem B2740331 : Blo 231814 2740331 := bstep (se 1 (by rfl) ⟨2055248, by rfl⟩ : syracuseStep 2740331 = 4110497) B4110497
theorem B348911 : Blo 231814 348911 := bstep (se 1 (by rfl) ⟨261683, by rfl⟩ : syracuseStep 348911 = 523367) B523367
theorem B1430459 : Blo 231814 1430459 := bstep (se 1 (by rfl) ⟨1072844, by rfl⟩ : syracuseStep 1430459 = 2145689) B2145689
theorem B351743 : Blo 231814 351743 := bstep (se 1 (by rfl) ⟨263807, by rfl⟩ : syracuseStep 351743 = 527615) B527615
theorem B352583 : Blo 231814 352583 := bstep (se 1 (by rfl) ⟨264437, by rfl⟩ : syracuseStep 352583 = 528875) B528875
theorem B353435 : Blo 231814 353435 := bstep (se 1 (by rfl) ⟨265076, by rfl⟩ : syracuseStep 353435 = 530153) B530153
theorem B1176767 : Blo 231814 1176767 := bstep (se 1 (by rfl) ⟨882575, by rfl⟩ : syracuseStep 1176767 = 1765151) B1765151
theorem B423551 : Blo 231814 423551 := bstep (se 1 (by rfl) ⟨317663, by rfl⟩ : syracuseStep 423551 = 635327) B635327
theorem B391999 : Blo 231814 391999 := bstep (se 1 (by rfl) ⟨293999, by rfl⟩ : syracuseStep 391999 = 587999) B587999
theorem B786401 : Blo 231814 786401 := bstep (se 2 (by rfl) ⟨294900, by rfl⟩ : syracuseStep 786401 = 589801) B589801
theorem B393383 : Blo 231814 393383 := bstep (se 1 (by rfl) ⟨295037, by rfl⟩ : syracuseStep 393383 = 590075) B590075
theorem B394267 : Blo 231814 394267 := bstep (se 1 (by rfl) ⟨295700, by rfl⟩ : syracuseStep 394267 = 591401) B591401
theorem B232607 : Blo 231814 232607 := bstep (se 1 (by rfl) ⟨174455, by rfl⟩ : syracuseStep 232607 = 348911) B348911
theorem B953639 : Blo 231814 953639 := bstep (se 1 (by rfl) ⟨715229, by rfl⟩ : syracuseStep 953639 = 1430459) B1430459
theorem B889001 : Blo 231814 889001 := bstep (se 2 (by rfl) ⟨333375, by rfl⟩ : syracuseStep 889001 = 666751) B666751
theorem B1184381 : Blo 231814 1184381 := bstep (se 3 (by rfl) ⟨222071, by rfl⟩ : syracuseStep 1184381 = 444143) B444143
theorem B234495 : Blo 231814 234495 := bstep (se 1 (by rfl) ⟨175871, by rfl⟩ : syracuseStep 234495 = 351743) B351743
theorem B235055 : Blo 231814 235055 := bstep (se 1 (by rfl) ⟨176291, by rfl⟩ : syracuseStep 235055 = 352583) B352583
theorem B235623 : Blo 231814 235623 := bstep (se 1 (by rfl) ⟨176717, by rfl⟩ : syracuseStep 235623 = 353435) B353435
theorem B4273559 : Blo 231814 4273559 := bstep (se 1 (by rfl) ⟨3205169, by rfl⟩ : syracuseStep 4273559 = 6410339) B6410339
theorem B4472657 : Blo 231814 4472657 := bstep (se 2 (by rfl) ⟨1677246, by rfl⟩ : syracuseStep 4472657 = 3354493) B3354493
theorem B282367 : Blo 231814 282367 := bstep (se 1 (by rfl) ⟨211775, by rfl⟩ : syracuseStep 282367 = 423551) B423551
theorem B711919 : Blo 231814 711919 := bstep (se 1 (by rfl) ⟨533939, by rfl⟩ : syracuseStep 711919 = 1067879) B1067879
theorem B1007099 : Blo 231814 1007099 := bstep (se 1 (by rfl) ⟨755324, by rfl⟩ : syracuseStep 1007099 = 1510649) B1510649
theorem B16342811 : Blo 231814 16342811 := bstep (se 1 (by rfl) ⟨12257108, by rfl⟩ : syracuseStep 16342811 = 24514217) B24514217
theorem B1826887 : Blo 231814 1826887 := bstep (se 1 (by rfl) ⟨1370165, by rfl⟩ : syracuseStep 1826887 = 2740331) B2740331
theorem B3370409 : Blo 231814 3370409 := bstep (se 2 (by rfl) ⟨1263903, by rfl⟩ : syracuseStep 3370409 = 2527807) B2527807
theorem B784511 : Blo 231814 784511 := bstep (se 1 (by rfl) ⟨588383, by rfl⟩ : syracuseStep 784511 = 1176767) B1176767
theorem B522665 : Blo 231814 522665 := bstep (se 2 (by rfl) ⟨195999, by rfl⟩ : syracuseStep 522665 = 391999) B391999
theorem B294455 : Blo 231814 294455 := bstep (se 1 (by rfl) ⟨220841, by rfl⟩ : syracuseStep 294455 = 441683) B441683
theorem B524267 : Blo 231814 524267 := bstep (se 1 (by rfl) ⟨393200, by rfl⟩ : syracuseStep 524267 = 786401) B786401
theorem B262255 : Blo 231814 262255 := bstep (se 1 (by rfl) ⟨196691, by rfl⟩ : syracuseStep 262255 = 393383) B393383
theorem B525689 : Blo 231814 525689 := bstep (se 2 (by rfl) ⟨197133, by rfl⟩ : syracuseStep 525689 = 394267) B394267
theorem B592667 : Blo 231814 592667 := bstep (se 1 (by rfl) ⟨444500, by rfl⟩ : syracuseStep 592667 = 889001) B889001
theorem B789587 : Blo 231814 789587 := bstep (se 1 (by rfl) ⟨592190, by rfl⟩ : syracuseStep 789587 = 1184381) B1184381
theorem B2435849 : Blo 231814 2435849 := bstep (se 2 (by rfl) ⟨913443, by rfl⟩ : syracuseStep 2435849 = 1826887) B1826887
theorem B635759 : Blo 231814 635759 := bstep (se 1 (by rfl) ⟨476819, by rfl⟩ : syracuseStep 635759 = 953639) B953639
theorem B671399 : Blo 231814 671399 := bstep (se 1 (by rfl) ⟨503549, by rfl⟩ : syracuseStep 671399 = 1007099) B1007099
theorem B376489 : Blo 231814 376489 := bstep (se 2 (by rfl) ⟨141183, by rfl⟩ : syracuseStep 376489 = 282367) B282367
theorem B10895207 : Blo 231814 10895207 := bstep (se 1 (by rfl) ⟨8171405, by rfl⟩ : syracuseStep 10895207 = 16342811) B16342811
theorem B2246939 : Blo 231814 2246939 := bstep (se 1 (by rfl) ⟨1685204, by rfl⟩ : syracuseStep 2246939 = 3370409) B3370409
theorem B348443 : Blo 231814 348443 := bstep (se 1 (by rfl) ⟨261332, by rfl⟩ : syracuseStep 348443 = 522665) B522665
theorem B349511 : Blo 231814 349511 := bstep (se 1 (by rfl) ⟨262133, by rfl⟩ : syracuseStep 349511 = 524267) B524267
theorem B2849039 : Blo 231814 2849039 := bstep (se 1 (by rfl) ⟨2136779, by rfl⟩ : syracuseStep 2849039 = 4273559) B4273559
theorem B523007 : Blo 231814 523007 := bstep (se 1 (by rfl) ⟨392255, by rfl⟩ : syracuseStep 523007 = 784511) B784511
theorem B785213 : Blo 231814 785213 := bstep (se 3 (by rfl) ⟨147227, by rfl⟩ : syracuseStep 785213 = 294455) B294455
theorem B949225 : Blo 231814 949225 := bstep (se 2 (by rfl) ⟨355959, by rfl⟩ : syracuseStep 949225 = 711919) B711919
theorem B2981771 : Blo 231814 2981771 := bstep (se 1 (by rfl) ⟨2236328, by rfl⟩ : syracuseStep 2981771 = 4472657) B4472657
theorem B395111 : Blo 231814 395111 := bstep (se 1 (by rfl) ⟨296333, by rfl⟩ : syracuseStep 395111 = 592667) B592667
theorem B526391 : Blo 231814 526391 := bstep (se 1 (by rfl) ⟨394793, by rfl⟩ : syracuseStep 526391 = 789587) B789587
theorem B232295 : Blo 231814 232295 := bstep (se 1 (by rfl) ⟨174221, by rfl⟩ : syracuseStep 232295 = 348443) B348443
theorem B233007 : Blo 231814 233007 := bstep (se 1 (by rfl) ⟨174755, by rfl⟩ : syracuseStep 233007 = 349511) B349511
theorem B501985 : Blo 231814 501985 := bstep (se 2 (by rfl) ⟨188244, by rfl⟩ : syracuseStep 501985 = 376489) B376489
theorem B1623899 : Blo 231814 1623899 := bstep (se 1 (by rfl) ⟨1217924, by rfl⟩ : syracuseStep 1623899 = 2435849) B2435849
theorem B1265633 : Blo 231814 1265633 := bstep (se 2 (by rfl) ⟨474612, by rfl⟩ : syracuseStep 1265633 = 949225) B949225
theorem B348671 : Blo 231814 348671 := bstep (se 1 (by rfl) ⟨261503, by rfl⟩ : syracuseStep 348671 = 523007) B523007
theorem B29053885 : Blo 231814 29053885 := bstep (se 3 (by rfl) ⟨5447603, by rfl⟩ : syracuseStep 29053885 = 10895207) B10895207
theorem B447599 : Blo 231814 447599 := bstep (se 1 (by rfl) ⟨335699, by rfl⟩ : syracuseStep 447599 = 671399) B671399
theorem B1987847 : Blo 231814 1987847 := bstep (se 1 (by rfl) ⟨1490885, by rfl⟩ : syracuseStep 1987847 = 2981771) B2981771
theorem B349673 : Blo 231814 349673 := bstep (se 2 (by rfl) ⟨131127, by rfl⟩ : syracuseStep 349673 = 262255) B262255
theorem B350459 : Blo 231814 350459 := bstep (se 1 (by rfl) ⟨262844, by rfl⟩ : syracuseStep 350459 = 525689) B525689
theorem B1497959 : Blo 231814 1497959 := bstep (se 1 (by rfl) ⟨1123469, by rfl⟩ : syracuseStep 1497959 = 2246939) B2246939
theorem B423839 : Blo 231814 423839 := bstep (se 1 (by rfl) ⟨317879, by rfl⟩ : syracuseStep 423839 = 635759) B635759
theorem B1899359 : Blo 231814 1899359 := bstep (se 1 (by rfl) ⟨1424519, by rfl⟩ : syracuseStep 1899359 = 2849039) B2849039
theorem B523475 : Blo 231814 523475 := bstep (se 1 (by rfl) ⟨392606, by rfl⟩ : syracuseStep 523475 = 785213) B785213
theorem B263407 : Blo 231814 263407 := bstep (se 1 (by rfl) ⟨197555, by rfl⟩ : syracuseStep 263407 = 395111) B395111
theorem B232447 : Blo 231814 232447 := bstep (se 1 (by rfl) ⟨174335, by rfl⟩ : syracuseStep 232447 = 348671) B348671
theorem B298399 : Blo 231814 298399 := bstep (se 1 (by rfl) ⟨223799, by rfl⟩ : syracuseStep 298399 = 447599) B447599
theorem B233115 : Blo 231814 233115 := bstep (se 1 (by rfl) ⟨174836, by rfl⟩ : syracuseStep 233115 = 349673) B349673
theorem B233639 : Blo 231814 233639 := bstep (se 1 (by rfl) ⟨175229, by rfl⟩ : syracuseStep 233639 = 350459) B350459
theorem B4330397 : Blo 231814 4330397 := bstep (se 3 (by rfl) ⟨811949, by rfl⟩ : syracuseStep 4330397 = 1623899) B1623899
theorem B38738513 : Blo 231814 38738513 := bstep (se 2 (by rfl) ⟨14526942, by rfl⟩ : syracuseStep 38738513 = 29053885) B29053885
theorem B669313 : Blo 231814 669313 := bstep (se 2 (by rfl) ⟨250992, by rfl⟩ : syracuseStep 669313 = 501985) B501985
theorem B1325231 : Blo 231814 1325231 := bstep (se 1 (by rfl) ⟨993923, by rfl⟩ : syracuseStep 1325231 = 1987847) B1987847
theorem B998639 : Blo 231814 998639 := bstep (se 1 (by rfl) ⟨748979, by rfl⟩ : syracuseStep 998639 = 1497959) B1497959
theorem B282559 : Blo 231814 282559 := bstep (se 1 (by rfl) ⟨211919, by rfl⟩ : syracuseStep 282559 = 423839) B423839
theorem B1266239 : Blo 231814 1266239 := bstep (se 1 (by rfl) ⟨949679, by rfl⟩ : syracuseStep 1266239 = 1899359) B1899359
theorem B348983 : Blo 231814 348983 := bstep (se 1 (by rfl) ⟨261737, by rfl⟩ : syracuseStep 348983 = 523475) B523475
theorem B350927 : Blo 231814 350927 := bstep (se 1 (by rfl) ⟨263195, by rfl⟩ : syracuseStep 350927 = 526391) B526391
theorem B843755 : Blo 231814 843755 := bstep (se 1 (by rfl) ⟨632816, by rfl⟩ : syracuseStep 843755 = 1265633) B1265633
theorem B3376637 : Blo 231814 3376637 := bstep (se 3 (by rfl) ⟨633119, by rfl⟩ : syracuseStep 3376637 = 1266239) B1266239
theorem B232655 : Blo 231814 232655 := bstep (se 1 (by rfl) ⟨174491, by rfl⟩ : syracuseStep 232655 = 348983) B348983
theorem B2886931 : Blo 231814 2886931 := bstep (se 1 (by rfl) ⟨2165198, by rfl⟩ : syracuseStep 2886931 = 4330397) B4330397
theorem B25825675 : Blo 231814 25825675 := bstep (se 1 (by rfl) ⟨19369256, by rfl⟩ : syracuseStep 25825675 = 38738513) B38738513
theorem B233951 : Blo 231814 233951 := bstep (se 1 (by rfl) ⟨175463, by rfl⟩ : syracuseStep 233951 = 350927) B350927
theorem B397865 : Blo 231814 397865 := bstep (se 2 (by rfl) ⟨149199, by rfl⟩ : syracuseStep 397865 = 298399) B298399
theorem B892417 : Blo 231814 892417 := bstep (se 2 (by rfl) ⟨334656, by rfl⟩ : syracuseStep 892417 = 669313) B669313
theorem B665759 : Blo 231814 665759 := bstep (se 1 (by rfl) ⟨499319, by rfl⟩ : syracuseStep 665759 = 998639) B998639
theorem B376745 : Blo 231814 376745 := bstep (se 2 (by rfl) ⟨141279, by rfl⟩ : syracuseStep 376745 = 282559) B282559
theorem B2250013 : Blo 231814 2250013 := bstep (se 3 (by rfl) ⟨421877, by rfl⟩ : syracuseStep 2250013 = 843755) B843755
theorem B351209 : Blo 231814 351209 := bstep (se 2 (by rfl) ⟨131703, by rfl⟩ : syracuseStep 351209 = 263407) B263407
theorem B883487 : Blo 231814 883487 := bstep (se 1 (by rfl) ⟨662615, by rfl⟩ : syracuseStep 883487 = 1325231) B1325231
theorem B265243 : Blo 231814 265243 := bstep (se 1 (by rfl) ⟨198932, by rfl⟩ : syracuseStep 265243 = 397865) B397865
theorem B234139 : Blo 231814 234139 := bstep (se 1 (by rfl) ⟨175604, by rfl⟩ : syracuseStep 234139 = 351209) B351209
theorem B1775357 : Blo 231814 1775357 := bstep (se 3 (by rfl) ⟨332879, by rfl⟩ : syracuseStep 1775357 = 665759) B665759
theorem B1189889 : Blo 231814 1189889 := bstep (se 2 (by rfl) ⟨446208, by rfl⟩ : syracuseStep 1189889 = 892417) B892417
theorem B3849241 : Blo 231814 3849241 := bstep (se 2 (by rfl) ⟨1443465, by rfl⟩ : syracuseStep 3849241 = 2886931) B2886931
theorem B3000017 : Blo 231814 3000017 := bstep (se 2 (by rfl) ⟨1125006, by rfl⟩ : syracuseStep 3000017 = 2250013) B2250013
theorem B1004653 : Blo 231814 1004653 := bstep (se 3 (by rfl) ⟨188372, by rfl⟩ : syracuseStep 1004653 = 376745) B376745
theorem B2251091 : Blo 231814 2251091 := bstep (se 1 (by rfl) ⟨1688318, by rfl⟩ : syracuseStep 2251091 = 3376637) B3376637
theorem B34434233 : Blo 231814 34434233 := bstep (se 2 (by rfl) ⟨12912837, by rfl⟩ : syracuseStep 34434233 = 25825675) B25825675
theorem B588991 : Blo 231814 588991 := bstep (se 1 (by rfl) ⟨441743, by rfl⟩ : syracuseStep 588991 = 883487) B883487
theorem B2000011 : Blo 231814 2000011 := bstep (se 1 (by rfl) ⟨1500008, by rfl⟩ : syracuseStep 2000011 = 3000017) B3000017
theorem B1183571 : Blo 231814 1183571 := bstep (se 1 (by rfl) ⟨887678, by rfl⟩ : syracuseStep 1183571 = 1775357) B1775357
theorem B793259 : Blo 231814 793259 := bstep (se 1 (by rfl) ⟨594944, by rfl⟩ : syracuseStep 793259 = 1189889) B1189889
theorem B22956155 : Blo 231814 22956155 := bstep (se 1 (by rfl) ⟨17217116, by rfl⟩ : syracuseStep 22956155 = 34434233) B34434233
theorem B5132321 : Blo 231814 5132321 := bstep (se 2 (by rfl) ⟨1924620, by rfl⟩ : syracuseStep 5132321 = 3849241) B3849241
theorem B353657 : Blo 231814 353657 := bstep (se 2 (by rfl) ⟨132621, by rfl⟩ : syracuseStep 353657 = 265243) B265243
theorem B1500727 : Blo 231814 1500727 := bstep (se 1 (by rfl) ⟨1125545, by rfl⟩ : syracuseStep 1500727 = 2251091) B2251091
theorem B1339537 : Blo 231814 1339537 := bstep (se 2 (by rfl) ⟨502326, by rfl⟩ : syracuseStep 1339537 = 1004653) B1004653
theorem B785321 : Blo 231814 785321 := bstep (se 2 (by rfl) ⟨294495, by rfl⟩ : syracuseStep 785321 = 588991) B588991
theorem B15304103 : Blo 231814 15304103 := bstep (se 1 (by rfl) ⟨11478077, by rfl⟩ : syracuseStep 15304103 = 22956155) B22956155
theorem B2000969 : Blo 231814 2000969 := bstep (se 2 (by rfl) ⟨750363, by rfl⟩ : syracuseStep 2000969 = 1500727) B1500727
theorem B789047 : Blo 231814 789047 := bstep (se 1 (by rfl) ⟨591785, by rfl⟩ : syracuseStep 789047 = 1183571) B1183571
theorem B528839 : Blo 231814 528839 := bstep (se 1 (by rfl) ⟨396629, by rfl⟩ : syracuseStep 528839 = 793259) B793259
theorem B235771 : Blo 231814 235771 := bstep (se 1 (by rfl) ⟨176828, by rfl⟩ : syracuseStep 235771 = 353657) B353657
theorem B2666681 : Blo 231814 2666681 := bstep (se 2 (by rfl) ⟨1000005, by rfl⟩ : syracuseStep 2666681 = 2000011) B2000011
theorem B3421547 : Blo 231814 3421547 := bstep (se 1 (by rfl) ⟨2566160, by rfl⟩ : syracuseStep 3421547 = 5132321) B5132321
theorem B1786049 : Blo 231814 1786049 := bstep (se 2 (by rfl) ⟨669768, by rfl⟩ : syracuseStep 1786049 = 1339537) B1339537
theorem B523547 : Blo 231814 523547 := bstep (se 1 (by rfl) ⟨392660, by rfl⟩ : syracuseStep 523547 = 785321) B785321
theorem B526031 : Blo 231814 526031 := bstep (se 1 (by rfl) ⟨394523, by rfl⟩ : syracuseStep 526031 = 789047) B789047
theorem B1777787 : Blo 231814 1777787 := bstep (se 1 (by rfl) ⟨1333340, by rfl⟩ : syracuseStep 1777787 = 2666681) B2666681
theorem B1190699 : Blo 231814 1190699 := bstep (se 1 (by rfl) ⟨893024, by rfl⟩ : syracuseStep 1190699 = 1786049) B1786049
theorem B10202735 : Blo 231814 10202735 := bstep (se 1 (by rfl) ⟨7652051, by rfl⟩ : syracuseStep 10202735 = 15304103) B15304103
theorem B2281031 : Blo 231814 2281031 := bstep (se 1 (by rfl) ⟨1710773, by rfl⟩ : syracuseStep 2281031 = 3421547) B3421547
theorem B349031 : Blo 231814 349031 := bstep (se 1 (by rfl) ⟨261773, by rfl⟩ : syracuseStep 349031 = 523547) B523547
theorem B1333979 : Blo 231814 1333979 := bstep (se 1 (by rfl) ⟨1000484, by rfl⟩ : syracuseStep 1333979 = 2000969) B2000969
theorem B352559 : Blo 231814 352559 := bstep (se 1 (by rfl) ⟨264419, by rfl⟩ : syracuseStep 352559 = 528839) B528839
theorem B232687 : Blo 231814 232687 := bstep (se 1 (by rfl) ⟨174515, by rfl⟩ : syracuseStep 232687 = 349031) B349031
theorem B889319 : Blo 231814 889319 := bstep (se 1 (by rfl) ⟨666989, by rfl⟩ : syracuseStep 889319 = 1333979) B1333979
theorem B1185191 : Blo 231814 1185191 := bstep (se 1 (by rfl) ⟨888893, by rfl⟩ : syracuseStep 1185191 = 1777787) B1777787
theorem B235039 : Blo 231814 235039 := bstep (se 1 (by rfl) ⟨176279, by rfl⟩ : syracuseStep 235039 = 352559) B352559
theorem B793799 : Blo 231814 793799 := bstep (se 1 (by rfl) ⟨595349, by rfl⟩ : syracuseStep 793799 = 1190699) B1190699
theorem B1520687 : Blo 231814 1520687 := bstep (se 1 (by rfl) ⟨1140515, by rfl⟩ : syracuseStep 1520687 = 2281031) B2281031
theorem B6801823 : Blo 231814 6801823 := bstep (se 1 (by rfl) ⟨5101367, by rfl⟩ : syracuseStep 6801823 = 10202735) B10202735
theorem B350687 : Blo 231814 350687 := bstep (se 1 (by rfl) ⟨263015, by rfl⟩ : syracuseStep 350687 = 526031) B526031
theorem B592879 : Blo 231814 592879 := bstep (se 1 (by rfl) ⟨444659, by rfl⟩ : syracuseStep 592879 = 889319) B889319
theorem B790127 : Blo 231814 790127 := bstep (se 1 (by rfl) ⟨592595, by rfl⟩ : syracuseStep 790127 = 1185191) B1185191
theorem B233791 : Blo 231814 233791 := bstep (se 1 (by rfl) ⟨175343, by rfl⟩ : syracuseStep 233791 = 350687) B350687
theorem B529199 : Blo 231814 529199 := bstep (se 1 (by rfl) ⟨396899, by rfl⟩ : syracuseStep 529199 = 793799) B793799
theorem B9069097 : Blo 231814 9069097 := bstep (se 2 (by rfl) ⟨3400911, by rfl⟩ : syracuseStep 9069097 = 6801823) B6801823
theorem B1013791 : Blo 231814 1013791 := bstep (se 1 (by rfl) ⟨760343, by rfl⟩ : syracuseStep 1013791 = 1520687) B1520687
theorem B12092129 : Blo 231814 12092129 := bstep (se 2 (by rfl) ⟨4534548, by rfl⟩ : syracuseStep 12092129 = 9069097) B9069097
theorem B526751 : Blo 231814 526751 := bstep (se 1 (by rfl) ⟨395063, by rfl⟩ : syracuseStep 526751 = 790127) B790127
theorem B790505 : Blo 231814 790505 := bstep (se 2 (by rfl) ⟨296439, by rfl⟩ : syracuseStep 790505 = 592879) B592879
theorem B1351721 : Blo 231814 1351721 := bstep (se 2 (by rfl) ⟨506895, by rfl⟩ : syracuseStep 1351721 = 1013791) B1013791
theorem B352799 : Blo 231814 352799 := bstep (se 1 (by rfl) ⟨264599, by rfl⟩ : syracuseStep 352799 = 529199) B529199
theorem B8061419 : Blo 231814 8061419 := bstep (se 1 (by rfl) ⟨6046064, by rfl⟩ : syracuseStep 8061419 = 12092129) B12092129
theorem B527003 : Blo 231814 527003 := bstep (se 1 (by rfl) ⟨395252, by rfl⟩ : syracuseStep 527003 = 790505) B790505
theorem B235199 : Blo 231814 235199 := bstep (se 1 (by rfl) ⟨176399, by rfl⟩ : syracuseStep 235199 = 352799) B352799
theorem B901147 : Blo 231814 901147 := bstep (se 1 (by rfl) ⟨675860, by rfl⟩ : syracuseStep 901147 = 1351721) B1351721
theorem B351167 : Blo 231814 351167 := bstep (se 1 (by rfl) ⟨263375, by rfl⟩ : syracuseStep 351167 = 526751) B526751
theorem B5374279 : Blo 231814 5374279 := bstep (se 1 (by rfl) ⟨4030709, by rfl⟩ : syracuseStep 5374279 = 8061419) B8061419
theorem B234111 : Blo 231814 234111 := bstep (se 1 (by rfl) ⟨175583, by rfl⟩ : syracuseStep 234111 = 351167) B351167
theorem B1201529 : Blo 231814 1201529 := bstep (se 2 (by rfl) ⟨450573, by rfl⟩ : syracuseStep 1201529 = 901147) B901147
theorem B351335 : Blo 231814 351335 := bstep (se 1 (by rfl) ⟨263501, by rfl⟩ : syracuseStep 351335 = 527003) B527003
theorem B234223 : Blo 231814 234223 := bstep (se 1 (by rfl) ⟨175667, by rfl⟩ : syracuseStep 234223 = 351335) B351335
theorem B801019 : Blo 231814 801019 := bstep (se 1 (by rfl) ⟨600764, by rfl⟩ : syracuseStep 801019 = 1201529) B1201529
theorem B7165705 : Blo 231814 7165705 := bstep (se 2 (by rfl) ⟨2687139, by rfl⟩ : syracuseStep 7165705 = 5374279) B5374279
theorem B4272101 : Blo 231814 4272101 := bstep (se 4 (by rfl) ⟨400509, by rfl⟩ : syracuseStep 4272101 = 801019) B801019
theorem B9554273 : Blo 231814 9554273 := bstep (se 2 (by rfl) ⟨3582852, by rfl⟩ : syracuseStep 9554273 = 7165705) B7165705
theorem B6369515 : Blo 231814 6369515 := bstep (se 1 (by rfl) ⟨4777136, by rfl⟩ : syracuseStep 6369515 = 9554273) B9554273
theorem B2848067 : Blo 231814 2848067 := bstep (se 1 (by rfl) ⟨2136050, by rfl⟩ : syracuseStep 2848067 = 4272101) B4272101
theorem B4246343 : Blo 231814 4246343 := bstep (se 1 (by rfl) ⟨3184757, by rfl⟩ : syracuseStep 4246343 = 6369515) B6369515
theorem B1898711 : Blo 231814 1898711 := bstep (se 1 (by rfl) ⟨1424033, by rfl⟩ : syracuseStep 1898711 = 2848067) B2848067
theorem B2830895 : Blo 231814 2830895 := bstep (se 1 (by rfl) ⟨2123171, by rfl⟩ : syracuseStep 2830895 = 4246343) B4246343
theorem B1265807 : Blo 231814 1265807 := bstep (se 1 (by rfl) ⟨949355, by rfl⟩ : syracuseStep 1265807 = 1898711) B1898711
theorem B1887263 : Blo 231814 1887263 := bstep (se 1 (by rfl) ⟨1415447, by rfl⟩ : syracuseStep 1887263 = 2830895) B2830895
theorem B843871 : Blo 231814 843871 := bstep (se 1 (by rfl) ⟨632903, by rfl⟩ : syracuseStep 843871 = 1265807) B1265807
theorem B1125161 : Blo 231814 1125161 := bstep (se 2 (by rfl) ⟨421935, by rfl⟩ : syracuseStep 1125161 = 843871) B843871
theorem B1258175 : Blo 231814 1258175 := bstep (se 1 (by rfl) ⟨943631, by rfl⟩ : syracuseStep 1258175 = 1887263) B1887263
theorem B838783 : Blo 231814 838783 := bstep (se 1 (by rfl) ⟨629087, by rfl⟩ : syracuseStep 838783 = 1258175) B1258175
theorem B750107 : Blo 231814 750107 := bstep (se 1 (by rfl) ⟨562580, by rfl⟩ : syracuseStep 750107 = 1125161) B1125161
theorem B2000285 : Blo 231814 2000285 := bstep (se 3 (by rfl) ⟨375053, by rfl⟩ : syracuseStep 2000285 = 750107) B750107
theorem B1118377 : Blo 231814 1118377 := bstep (se 2 (by rfl) ⟨419391, by rfl⟩ : syracuseStep 1118377 = 838783) B838783
theorem B1491169 : Blo 231814 1491169 := bstep (se 2 (by rfl) ⟨559188, by rfl⟩ : syracuseStep 1491169 = 1118377) B1118377
theorem B1333523 : Blo 231814 1333523 := bstep (se 1 (by rfl) ⟨1000142, by rfl⟩ : syracuseStep 1333523 = 2000285) B2000285
theorem B889015 : Blo 231814 889015 := bstep (se 1 (by rfl) ⟨666761, by rfl⟩ : syracuseStep 889015 = 1333523) B1333523
theorem B1988225 : Blo 231814 1988225 := bstep (se 2 (by rfl) ⟨745584, by rfl⟩ : syracuseStep 1988225 = 1491169) B1491169
theorem B1185353 : Blo 231814 1185353 := bstep (se 2 (by rfl) ⟨444507, by rfl⟩ : syracuseStep 1185353 = 889015) B889015
theorem B1325483 : Blo 231814 1325483 := bstep (se 1 (by rfl) ⟨994112, by rfl⟩ : syracuseStep 1325483 = 1988225) B1988225
theorem B790235 : Blo 231814 790235 := bstep (se 1 (by rfl) ⟨592676, by rfl⟩ : syracuseStep 790235 = 1185353) B1185353
theorem B883655 : Blo 231814 883655 := bstep (se 1 (by rfl) ⟨662741, by rfl⟩ : syracuseStep 883655 = 1325483) B1325483
theorem B526823 : Blo 231814 526823 := bstep (se 1 (by rfl) ⟨395117, by rfl⟩ : syracuseStep 526823 = 790235) B790235
theorem B589103 : Blo 231814 589103 := bstep (se 1 (by rfl) ⟨441827, by rfl⟩ : syracuseStep 589103 = 883655) B883655
theorem B351215 : Blo 231814 351215 := bstep (se 1 (by rfl) ⟨263411, by rfl⟩ : syracuseStep 351215 = 526823) B526823
theorem B392735 : Blo 231814 392735 := bstep (se 1 (by rfl) ⟨294551, by rfl⟩ : syracuseStep 392735 = 589103) B589103
theorem B234143 : Blo 231814 234143 := bstep (se 1 (by rfl) ⟨175607, by rfl⟩ : syracuseStep 234143 = 351215) B351215
theorem B261823 : Blo 231814 261823 := bstep (se 1 (by rfl) ⟨196367, by rfl⟩ : syracuseStep 261823 = 392735) B392735
theorem B349097 : Blo 231814 349097 := bstep (se 2 (by rfl) ⟨130911, by rfl⟩ : syracuseStep 349097 = 261823) B261823
theorem B232731 : Blo 231814 232731 := bstep (se 1 (by rfl) ⟨174548, by rfl⟩ : syracuseStep 232731 = 349097) B349097

theorem C0 (j : ℕ) (h1 : 57953 ≤ j) (h2 : j ≤ 58652) : Blo 231814 (4 * j + 3) := by
  interval_cases j
  · exact B231815
  · exact B231819
  · exact B231823
  · exact B231827
  · exact B231831
  · exact B231835
  · exact B231839
  · exact B231843
  · exact B231847
  · exact B231851
  · exact B231855
  · exact B231859
  · exact B231863
  · exact B231867
  · exact B231871
  · exact B231875
  · exact B231879
  · exact B231883
  · exact B231887
  · exact B231891
  · exact B231895
  · exact B231899
  · exact B231903
  · exact B231907
  · exact B231911
  · exact B231915
  · exact B231919
  · exact B231923
  · exact B231927
  · exact B231931
  · exact B231935
  · exact B231939
  · exact B231943
  · exact B231947
  · exact B231951
  · exact B231955
  · exact B231959
  · exact B231963
  · exact B231967
  · exact B231971
  · exact B231975
  · exact B231979
  · exact B231983
  · exact B231987
  · exact B231991
  · exact B231995
  · exact B231999
  · exact B232003
  · exact B232007
  · exact B232011
  · exact B232015
  · exact B232019
  · exact B232023
  · exact B232027
  · exact B232031
  · exact B232035
  · exact B232039
  · exact B232043
  · exact B232047
  · exact B232051
  · exact B232055
  · exact B232059
  · exact B232063
  · exact B232067
  · exact B232071
  · exact B232075
  · exact B232079
  · exact B232083
  · exact B232087
  · exact B232091
  · exact B232095
  · exact B232099
  · exact B232103
  · exact B232107
  · exact B232111
  · exact B232115
  · exact B232119
  · exact B232123
  · exact B232127
  · exact B232131
  · exact B232135
  · exact B232139
  · exact B232143
  · exact B232147
  · exact B232151
  · exact B232155
  · exact B232159
  · exact B232163
  · exact B232167
  · exact B232171
  · exact B232175
  · exact B232179
  · exact B232183
  · exact B232187
  · exact B232191
  · exact B232195
  · exact B232199
  · exact B232203
  · exact B232207
  · exact B232211
  · exact B232215
  · exact B232219
  · exact B232223
  · exact B232227
  · exact B232231
  · exact B232235
  · exact B232239
  · exact B232243
  · exact B232247
  · exact B232251
  · exact B232255
  · exact B232259
  · exact B232263
  · exact B232267
  · exact B232271
  · exact B232275
  · exact B232279
  · exact B232283
  · exact B232287
  · exact B232291
  · exact B232295
  · exact B232299
  · exact B232303
  · exact B232307
  · exact B232311
  · exact B232315
  · exact B232319
  · exact B232323
  · exact B232327
  · exact B232331
  · exact B232335
  · exact B232339
  · exact B232343
  · exact B232347
  · exact B232351
  · exact B232355
  · exact B232359
  · exact B232363
  · exact B232367
  · exact B232371
  · exact B232375
  · exact B232379
  · exact B232383
  · exact B232387
  · exact B232391
  · exact B232395
  · exact B232399
  · exact B232403
  · exact B232407
  · exact B232411
  · exact B232415
  · exact B232419
  · exact B232423
  · exact B232427
  · exact B232431
  · exact B232435
  · exact B232439
  · exact B232443
  · exact B232447
  · exact B232451
  · exact B232455
  · exact B232459
  · exact B232463
  · exact B232467
  · exact B232471
  · exact B232475
  · exact B232479
  · exact B232483
  · exact B232487
  · exact B232491
  · exact B232495
  · exact B232499
  · exact B232503
  · exact B232507
  · exact B232511
  · exact B232515
  · exact B232519
  · exact B232523
  · exact B232527
  · exact B232531
  · exact B232535
  · exact B232539
  · exact B232543
  · exact B232547
  · exact B232551
  · exact B232555
  · exact B232559
  · exact B232563
  · exact B232567
  · exact B232571
  · exact B232575
  · exact B232579
  · exact B232583
  · exact B232587
  · exact B232591
  · exact B232595
  · exact B232599
  · exact B232603
  · exact B232607
  · exact B232611
  · exact B232615
  · exact B232619
  · exact B232623
  · exact B232627
  · exact B232631
  · exact B232635
  · exact B232639
  · exact B232643
  · exact B232647
  · exact B232651
  · exact B232655
  · exact B232659
  · exact B232663
  · exact B232667
  · exact B232671
  · exact B232675
  · exact B232679
  · exact B232683
  · exact B232687
  · exact B232691
  · exact B232695
  · exact B232699
  · exact B232703
  · exact B232707
  · exact B232711
  · exact B232715
  · exact B232719
  · exact B232723
  · exact B232727
  · exact B232731
  · exact B232735
  · exact B232739
  · exact B232743
  · exact B232747
  · exact B232751
  · exact B232755
  · exact B232759
  · exact B232763
  · exact B232767
  · exact B232771
  · exact B232775
  · exact B232779
  · exact B232783
  · exact B232787
  · exact B232791
  · exact B232795
  · exact B232799
  · exact B232803
  · exact B232807
  · exact B232811
  · exact B232815
  · exact B232819
  · exact B232823
  · exact B232827
  · exact B232831
  · exact B232835
  · exact B232839
  · exact B232843
  · exact B232847
  · exact B232851
  · exact B232855
  · exact B232859
  · exact B232863
  · exact B232867
  · exact B232871
  · exact B232875
  · exact B232879
  · exact B232883
  · exact B232887
  · exact B232891
  · exact B232895
  · exact B232899
  · exact B232903
  · exact B232907
  · exact B232911
  · exact B232915
  · exact B232919
  · exact B232923
  · exact B232927
  · exact B232931
  · exact B232935
  · exact B232939
  · exact B232943
  · exact B232947
  · exact B232951
  · exact B232955
  · exact B232959
  · exact B232963
  · exact B232967
  · exact B232971
  · exact B232975
  · exact B232979
  · exact B232983
  · exact B232987
  · exact B232991
  · exact B232995
  · exact B232999
  · exact B233003
  · exact B233007
  · exact B233011
  · exact B233015
  · exact B233019
  · exact B233023
  · exact B233027
  · exact B233031
  · exact B233035
  · exact B233039
  · exact B233043
  · exact B233047
  · exact B233051
  · exact B233055
  · exact B233059
  · exact B233063
  · exact B233067
  · exact B233071
  · exact B233075
  · exact B233079
  · exact B233083
  · exact B233087
  · exact B233091
  · exact B233095
  · exact B233099
  · exact B233103
  · exact B233107
  · exact B233111
  · exact B233115
  · exact B233119
  · exact B233123
  · exact B233127
  · exact B233131
  · exact B233135
  · exact B233139
  · exact B233143
  · exact B233147
  · exact B233151
  · exact B233155
  · exact B233159
  · exact B233163
  · exact B233167
  · exact B233171
  · exact B233175
  · exact B233179
  · exact B233183
  · exact B233187
  · exact B233191
  · exact B233195
  · exact B233199
  · exact B233203
  · exact B233207
  · exact B233211
  · exact B233215
  · exact B233219
  · exact B233223
  · exact B233227
  · exact B233231
  · exact B233235
  · exact B233239
  · exact B233243
  · exact B233247
  · exact B233251
  · exact B233255
  · exact B233259
  · exact B233263
  · exact B233267
  · exact B233271
  · exact B233275
  · exact B233279
  · exact B233283
  · exact B233287
  · exact B233291
  · exact B233295
  · exact B233299
  · exact B233303
  · exact B233307
  · exact B233311
  · exact B233315
  · exact B233319
  · exact B233323
  · exact B233327
  · exact B233331
  · exact B233335
  · exact B233339
  · exact B233343
  · exact B233347
  · exact B233351
  · exact B233355
  · exact B233359
  · exact B233363
  · exact B233367
  · exact B233371
  · exact B233375
  · exact B233379
  · exact B233383
  · exact B233387
  · exact B233391
  · exact B233395
  · exact B233399
  · exact B233403
  · exact B233407
  · exact B233411
  · exact B233415
  · exact B233419
  · exact B233423
  · exact B233427
  · exact B233431
  · exact B233435
  · exact B233439
  · exact B233443
  · exact B233447
  · exact B233451
  · exact B233455
  · exact B233459
  · exact B233463
  · exact B233467
  · exact B233471
  · exact B233475
  · exact B233479
  · exact B233483
  · exact B233487
  · exact B233491
  · exact B233495
  · exact B233499
  · exact B233503
  · exact B233507
  · exact B233511
  · exact B233515
  · exact B233519
  · exact B233523
  · exact B233527
  · exact B233531
  · exact B233535
  · exact B233539
  · exact B233543
  · exact B233547
  · exact B233551
  · exact B233555
  · exact B233559
  · exact B233563
  · exact B233567
  · exact B233571
  · exact B233575
  · exact B233579
  · exact B233583
  · exact B233587
  · exact B233591
  · exact B233595
  · exact B233599
  · exact B233603
  · exact B233607
  · exact B233611
  · exact B233615
  · exact B233619
  · exact B233623
  · exact B233627
  · exact B233631
  · exact B233635
  · exact B233639
  · exact B233643
  · exact B233647
  · exact B233651
  · exact B233655
  · exact B233659
  · exact B233663
  · exact B233667
  · exact B233671
  · exact B233675
  · exact B233679
  · exact B233683
  · exact B233687
  · exact B233691
  · exact B233695
  · exact B233699
  · exact B233703
  · exact B233707
  · exact B233711
  · exact B233715
  · exact B233719
  · exact B233723
  · exact B233727
  · exact B233731
  · exact B233735
  · exact B233739
  · exact B233743
  · exact B233747
  · exact B233751
  · exact B233755
  · exact B233759
  · exact B233763
  · exact B233767
  · exact B233771
  · exact B233775
  · exact B233779
  · exact B233783
  · exact B233787
  · exact B233791
  · exact B233795
  · exact B233799
  · exact B233803
  · exact B233807
  · exact B233811
  · exact B233815
  · exact B233819
  · exact B233823
  · exact B233827
  · exact B233831
  · exact B233835
  · exact B233839
  · exact B233843
  · exact B233847
  · exact B233851
  · exact B233855
  · exact B233859
  · exact B233863
  · exact B233867
  · exact B233871
  · exact B233875
  · exact B233879
  · exact B233883
  · exact B233887
  · exact B233891
  · exact B233895
  · exact B233899
  · exact B233903
  · exact B233907
  · exact B233911
  · exact B233915
  · exact B233919
  · exact B233923
  · exact B233927
  · exact B233931
  · exact B233935
  · exact B233939
  · exact B233943
  · exact B233947
  · exact B233951
  · exact B233955
  · exact B233959
  · exact B233963
  · exact B233967
  · exact B233971
  · exact B233975
  · exact B233979
  · exact B233983
  · exact B233987
  · exact B233991
  · exact B233995
  · exact B233999
  · exact B234003
  · exact B234007
  · exact B234011
  · exact B234015
  · exact B234019
  · exact B234023
  · exact B234027
  · exact B234031
  · exact B234035
  · exact B234039
  · exact B234043
  · exact B234047
  · exact B234051
  · exact B234055
  · exact B234059
  · exact B234063
  · exact B234067
  · exact B234071
  · exact B234075
  · exact B234079
  · exact B234083
  · exact B234087
  · exact B234091
  · exact B234095
  · exact B234099
  · exact B234103
  · exact B234107
  · exact B234111
  · exact B234115
  · exact B234119
  · exact B234123
  · exact B234127
  · exact B234131
  · exact B234135
  · exact B234139
  · exact B234143
  · exact B234147
  · exact B234151
  · exact B234155
  · exact B234159
  · exact B234163
  · exact B234167
  · exact B234171
  · exact B234175
  · exact B234179
  · exact B234183
  · exact B234187
  · exact B234191
  · exact B234195
  · exact B234199
  · exact B234203
  · exact B234207
  · exact B234211
  · exact B234215
  · exact B234219
  · exact B234223
  · exact B234227
  · exact B234231
  · exact B234235
  · exact B234239
  · exact B234243
  · exact B234247
  · exact B234251
  · exact B234255
  · exact B234259
  · exact B234263
  · exact B234267
  · exact B234271
  · exact B234275
  · exact B234279
  · exact B234283
  · exact B234287
  · exact B234291
  · exact B234295
  · exact B234299
  · exact B234303
  · exact B234307
  · exact B234311
  · exact B234315
  · exact B234319
  · exact B234323
  · exact B234327
  · exact B234331
  · exact B234335
  · exact B234339
  · exact B234343
  · exact B234347
  · exact B234351
  · exact B234355
  · exact B234359
  · exact B234363
  · exact B234367
  · exact B234371
  · exact B234375
  · exact B234379
  · exact B234383
  · exact B234387
  · exact B234391
  · exact B234395
  · exact B234399
  · exact B234403
  · exact B234407
  · exact B234411
  · exact B234415
  · exact B234419
  · exact B234423
  · exact B234427
  · exact B234431
  · exact B234435
  · exact B234439
  · exact B234443
  · exact B234447
  · exact B234451
  · exact B234455
  · exact B234459
  · exact B234463
  · exact B234467
  · exact B234471
  · exact B234475
  · exact B234479
  · exact B234483
  · exact B234487
  · exact B234491
  · exact B234495
  · exact B234499
  · exact B234503
  · exact B234507
  · exact B234511
  · exact B234515
  · exact B234519
  · exact B234523
  · exact B234527
  · exact B234531
  · exact B234535
  · exact B234539
  · exact B234543
  · exact B234547
  · exact B234551
  · exact B234555
  · exact B234559
  · exact B234563
  · exact B234567
  · exact B234571
  · exact B234575
  · exact B234579
  · exact B234583
  · exact B234587
  · exact B234591
  · exact B234595
  · exact B234599
  · exact B234603
  · exact B234607
  · exact B234611

theorem C1 (j : ℕ) (h1 : 58653 ≤ j) (h2 : j ≤ 58952) : Blo 231814 (4 * j + 3) := by
  interval_cases j
  · exact B234615
  · exact B234619
  · exact B234623
  · exact B234627
  · exact B234631
  · exact B234635
  · exact B234639
  · exact B234643
  · exact B234647
  · exact B234651
  · exact B234655
  · exact B234659
  · exact B234663
  · exact B234667
  · exact B234671
  · exact B234675
  · exact B234679
  · exact B234683
  · exact B234687
  · exact B234691
  · exact B234695
  · exact B234699
  · exact B234703
  · exact B234707
  · exact B234711
  · exact B234715
  · exact B234719
  · exact B234723
  · exact B234727
  · exact B234731
  · exact B234735
  · exact B234739
  · exact B234743
  · exact B234747
  · exact B234751
  · exact B234755
  · exact B234759
  · exact B234763
  · exact B234767
  · exact B234771
  · exact B234775
  · exact B234779
  · exact B234783
  · exact B234787
  · exact B234791
  · exact B234795
  · exact B234799
  · exact B234803
  · exact B234807
  · exact B234811
  · exact B234815
  · exact B234819
  · exact B234823
  · exact B234827
  · exact B234831
  · exact B234835
  · exact B234839
  · exact B234843
  · exact B234847
  · exact B234851
  · exact B234855
  · exact B234859
  · exact B234863
  · exact B234867
  · exact B234871
  · exact B234875
  · exact B234879
  · exact B234883
  · exact B234887
  · exact B234891
  · exact B234895
  · exact B234899
  · exact B234903
  · exact B234907
  · exact B234911
  · exact B234915
  · exact B234919
  · exact B234923
  · exact B234927
  · exact B234931
  · exact B234935
  · exact B234939
  · exact B234943
  · exact B234947
  · exact B234951
  · exact B234955
  · exact B234959
  · exact B234963
  · exact B234967
  · exact B234971
  · exact B234975
  · exact B234979
  · exact B234983
  · exact B234987
  · exact B234991
  · exact B234995
  · exact B234999
  · exact B235003
  · exact B235007
  · exact B235011
  · exact B235015
  · exact B235019
  · exact B235023
  · exact B235027
  · exact B235031
  · exact B235035
  · exact B235039
  · exact B235043
  · exact B235047
  · exact B235051
  · exact B235055
  · exact B235059
  · exact B235063
  · exact B235067
  · exact B235071
  · exact B235075
  · exact B235079
  · exact B235083
  · exact B235087
  · exact B235091
  · exact B235095
  · exact B235099
  · exact B235103
  · exact B235107
  · exact B235111
  · exact B235115
  · exact B235119
  · exact B235123
  · exact B235127
  · exact B235131
  · exact B235135
  · exact B235139
  · exact B235143
  · exact B235147
  · exact B235151
  · exact B235155
  · exact B235159
  · exact B235163
  · exact B235167
  · exact B235171
  · exact B235175
  · exact B235179
  · exact B235183
  · exact B235187
  · exact B235191
  · exact B235195
  · exact B235199
  · exact B235203
  · exact B235207
  · exact B235211
  · exact B235215
  · exact B235219
  · exact B235223
  · exact B235227
  · exact B235231
  · exact B235235
  · exact B235239
  · exact B235243
  · exact B235247
  · exact B235251
  · exact B235255
  · exact B235259
  · exact B235263
  · exact B235267
  · exact B235271
  · exact B235275
  · exact B235279
  · exact B235283
  · exact B235287
  · exact B235291
  · exact B235295
  · exact B235299
  · exact B235303
  · exact B235307
  · exact B235311
  · exact B235315
  · exact B235319
  · exact B235323
  · exact B235327
  · exact B235331
  · exact B235335
  · exact B235339
  · exact B235343
  · exact B235347
  · exact B235351
  · exact B235355
  · exact B235359
  · exact B235363
  · exact B235367
  · exact B235371
  · exact B235375
  · exact B235379
  · exact B235383
  · exact B235387
  · exact B235391
  · exact B235395
  · exact B235399
  · exact B235403
  · exact B235407
  · exact B235411
  · exact B235415
  · exact B235419
  · exact B235423
  · exact B235427
  · exact B235431
  · exact B235435
  · exact B235439
  · exact B235443
  · exact B235447
  · exact B235451
  · exact B235455
  · exact B235459
  · exact B235463
  · exact B235467
  · exact B235471
  · exact B235475
  · exact B235479
  · exact B235483
  · exact B235487
  · exact B235491
  · exact B235495
  · exact B235499
  · exact B235503
  · exact B235507
  · exact B235511
  · exact B235515
  · exact B235519
  · exact B235523
  · exact B235527
  · exact B235531
  · exact B235535
  · exact B235539
  · exact B235543
  · exact B235547
  · exact B235551
  · exact B235555
  · exact B235559
  · exact B235563
  · exact B235567
  · exact B235571
  · exact B235575
  · exact B235579
  · exact B235583
  · exact B235587
  · exact B235591
  · exact B235595
  · exact B235599
  · exact B235603
  · exact B235607
  · exact B235611
  · exact B235615
  · exact B235619
  · exact B235623
  · exact B235627
  · exact B235631
  · exact B235635
  · exact B235639
  · exact B235643
  · exact B235647
  · exact B235651
  · exact B235655
  · exact B235659
  · exact B235663
  · exact B235667
  · exact B235671
  · exact B235675
  · exact B235679
  · exact B235683
  · exact B235687
  · exact B235691
  · exact B235695
  · exact B235699
  · exact B235703
  · exact B235707
  · exact B235711
  · exact B235715
  · exact B235719
  · exact B235723
  · exact B235727
  · exact B235731
  · exact B235735
  · exact B235739
  · exact B235743
  · exact B235747
  · exact B235751
  · exact B235755
  · exact B235759
  · exact B235763
  · exact B235767
  · exact B235771
  · exact B235775
  · exact B235779
  · exact B235783
  · exact B235787
  · exact B235791
  · exact B235795
  · exact B235799
  · exact B235803
  · exact B235807
  · exact B235811

theorem solution (m : ℕ) (hlo : 231814 ≤ m) (hhi : m ≤ 235814) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 57953 ≤ j := by omega
    have hj2 : j ≤ 58952 := by omega
    have hb : Blo 231814 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 58653 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
