-- Prove2me | solution 1 for syracuse_descends_range_1528461_1530461
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-10T00:04:39.690407+00:00
-- url     : https://prove2.me/submissions/55a05a02-7ca4-4c09-bed6-e0ead2e03d67

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


theorem B3440645 : Blo 1528461 3440645 := bbase (se 4 (by rfl) ⟨322560, by rfl⟩ : syracuseStep 3440645 = 645121) (by norm_num)
theorem B2293781 : Blo 1528461 2293781 := bbase (se 6 (by rfl) ⟨53760, by rfl⟩ : syracuseStep 2293781 = 107521) (by norm_num)
theorem B1720345 : Blo 1528461 1720345 := bbase (se 2 (by rfl) ⟨645129, by rfl⟩ : syracuseStep 1720345 = 1290259) (by norm_num)
theorem B2293805 : Blo 1528461 2293805 := bbase (se 3 (by rfl) ⟨430088, by rfl⟩ : syracuseStep 2293805 = 860177) (by norm_num)
theorem B7741493 : Blo 1528461 7741493 := bbase (se 5 (by rfl) ⟨362882, by rfl⟩ : syracuseStep 7741493 = 725765) (by norm_num)
theorem B1720381 : Blo 1528461 1720381 := bbase (se 3 (by rfl) ⟨322571, by rfl⟩ : syracuseStep 1720381 = 645143) (by norm_num)
theorem B3268669 : Blo 1528461 3268669 := bbase (se 3 (by rfl) ⟨612875, by rfl⟩ : syracuseStep 3268669 = 1225751) (by norm_num)
theorem B2293829 : Blo 1528461 2293829 := bbase (se 4 (by rfl) ⟨215046, by rfl⟩ : syracuseStep 2293829 = 430093) (by norm_num)
theorem B3440717 : Blo 1528461 3440717 := bbase (se 3 (by rfl) ⟨645134, by rfl⟩ : syracuseStep 3440717 = 1290269) (by norm_num)
theorem B2580565 : Blo 1528461 2580565 := bbase (se 8 (by rfl) ⟨15120, by rfl⟩ : syracuseStep 2580565 = 30241) (by norm_num)
theorem B2293853 : Blo 1528461 2293853 := bbase (se 3 (by rfl) ⟨430097, by rfl⟩ : syracuseStep 2293853 = 860195) (by norm_num)
theorem B1720417 : Blo 1528461 1720417 := bbase (se 2 (by rfl) ⟨645156, by rfl⟩ : syracuseStep 1720417 = 1290313) (by norm_num)
theorem B2293877 : Blo 1528461 2293877 := bbase (se 5 (by rfl) ⟨107525, by rfl⟩ : syracuseStep 2293877 = 215051) (by norm_num)
theorem B1720453 : Blo 1528461 1720453 := bbase (se 4 (by rfl) ⟨161292, by rfl⟩ : syracuseStep 1720453 = 322585) (by norm_num)
theorem B2293901 : Blo 1528461 2293901 := bbase (se 3 (by rfl) ⟨430106, by rfl⟩ : syracuseStep 2293901 = 860213) (by norm_num)
theorem B3440789 : Blo 1528461 3440789 := bbase (se 6 (by rfl) ⟨80643, by rfl⟩ : syracuseStep 3440789 = 161287) (by norm_num)
theorem B2293925 : Blo 1528461 2293925 := bbase (se 4 (by rfl) ⟨215055, by rfl⟩ : syracuseStep 2293925 = 430111) (by norm_num)
theorem B5808293 : Blo 1528461 5808293 := bbase (se 4 (by rfl) ⟨544527, by rfl⟩ : syracuseStep 5808293 = 1089055) (by norm_num)
theorem B1720489 : Blo 1528461 1720489 := bbase (se 2 (by rfl) ⟨645183, by rfl⟩ : syracuseStep 1720489 = 1290367) (by norm_num)
theorem B2580653 : Blo 1528461 2580653 := bbase (se 3 (by rfl) ⟨483872, by rfl⟩ : syracuseStep 2580653 = 967745) (by norm_num)
theorem B2293949 : Blo 1528461 2293949 := bbase (se 3 (by rfl) ⟨430115, by rfl⟩ : syracuseStep 2293949 = 860231) (by norm_num)
theorem B5161157 : Blo 1528461 5161157 := bbase (se 4 (by rfl) ⟨483858, by rfl⟩ : syracuseStep 5161157 = 967717) (by norm_num)
theorem B1720525 : Blo 1528461 1720525 := bbase (se 3 (by rfl) ⟨322598, by rfl⟩ : syracuseStep 1720525 = 645197) (by norm_num)
theorem B2293973 : Blo 1528461 2293973 := bbase (se 7 (by rfl) ⟨26882, by rfl⟩ : syracuseStep 2293973 = 53765) (by norm_num)
theorem B3440861 : Blo 1528461 3440861 := bbase (se 3 (by rfl) ⟨645161, by rfl⟩ : syracuseStep 3440861 = 1290323) (by norm_num)
theorem B2293997 : Blo 1528461 2293997 := bbase (se 3 (by rfl) ⟨430124, by rfl⟩ : syracuseStep 2293997 = 860249) (by norm_num)
theorem B1720561 : Blo 1528461 1720561 := bbase (se 2 (by rfl) ⟨645210, by rfl⟩ : syracuseStep 1720561 = 1290421) (by norm_num)
theorem B2294021 : Blo 1528461 2294021 := bbase (se 4 (by rfl) ⟨215064, by rfl⟩ : syracuseStep 2294021 = 430129) (by norm_num)
theorem B1720597 : Blo 1528461 1720597 := bbase (se 6 (by rfl) ⟨40326, by rfl⟩ : syracuseStep 1720597 = 80653) (by norm_num)
theorem B2294045 : Blo 1528461 2294045 := bbase (se 3 (by rfl) ⟨430133, by rfl⟩ : syracuseStep 2294045 = 860267) (by norm_num)
theorem B3440933 : Blo 1528461 3440933 := bbase (se 4 (by rfl) ⟨322587, by rfl⟩ : syracuseStep 3440933 = 645175) (by norm_num)
theorem B2580781 : Blo 1528461 2580781 := bbase (se 3 (by rfl) ⟨483896, by rfl⟩ : syracuseStep 2580781 = 967793) (by norm_num)
theorem B15687989 : Blo 1528461 15687989 := bbase (se 5 (by rfl) ⟨735374, by rfl⟩ : syracuseStep 15687989 = 1470749) (by norm_num)
theorem B2294069 : Blo 1528461 2294069 := bbase (se 5 (by rfl) ⟨107534, by rfl⟩ : syracuseStep 2294069 = 215069) (by norm_num)
theorem B1720633 : Blo 1528461 1720633 := bbase (se 2 (by rfl) ⟨645237, by rfl⟩ : syracuseStep 1720633 = 1290475) (by norm_num)
theorem B1745209 : Blo 1528461 1745209 := bbase (se 2 (by rfl) ⟨654453, by rfl⟩ : syracuseStep 1745209 = 1308907) (by norm_num)
theorem B4538693 : Blo 1528461 4538693 := bbase (se 4 (by rfl) ⟨425502, by rfl⟩ : syracuseStep 4538693 = 851005) (by norm_num)
theorem B2294093 : Blo 1528461 2294093 := bbase (se 3 (by rfl) ⟨430142, by rfl⟩ : syracuseStep 2294093 = 860285) (by norm_num)
theorem B1720669 : Blo 1528461 1720669 := bbase (se 3 (by rfl) ⟨322625, by rfl⟩ : syracuseStep 1720669 = 645251) (by norm_num)
theorem B2449765 : Blo 1528461 2449765 := bbase (se 4 (by rfl) ⟨229665, by rfl⟩ : syracuseStep 2449765 = 459331) (by norm_num)
theorem B2294117 : Blo 1528461 2294117 := bbase (se 4 (by rfl) ⟨215073, by rfl⟩ : syracuseStep 2294117 = 430147) (by norm_num)
theorem B3441005 : Blo 1528461 3441005 := bbase (se 3 (by rfl) ⟨645188, by rfl⟩ : syracuseStep 3441005 = 1290377) (by norm_num)
theorem B2294141 : Blo 1528461 2294141 := bbase (se 3 (by rfl) ⟨430151, by rfl⟩ : syracuseStep 2294141 = 860303) (by norm_num)
theorem B1720705 : Blo 1528461 1720705 := bbase (se 2 (by rfl) ⟨645264, by rfl⟩ : syracuseStep 1720705 = 1290529) (by norm_num)
theorem B2580869 : Blo 1528461 2580869 := bbase (se 4 (by rfl) ⟨241956, by rfl⟩ : syracuseStep 2580869 = 483913) (by norm_num)
theorem B2294165 : Blo 1528461 2294165 := bbase (se 6 (by rfl) ⟨53769, by rfl⟩ : syracuseStep 2294165 = 107539) (by norm_num)
theorem B1720741 : Blo 1528461 1720741 := bbase (se 4 (by rfl) ⟨161319, by rfl⟩ : syracuseStep 1720741 = 322639) (by norm_num)
theorem B2294189 : Blo 1528461 2294189 := bbase (se 3 (by rfl) ⟨430160, by rfl⟩ : syracuseStep 2294189 = 860321) (by norm_num)
theorem B3441077 : Blo 1528461 3441077 := bbase (se 5 (by rfl) ⟨161300, by rfl⟩ : syracuseStep 3441077 = 322601) (by norm_num)
theorem B2294213 : Blo 1528461 2294213 := bbase (se 4 (by rfl) ⟨215082, by rfl⟩ : syracuseStep 2294213 = 430165) (by norm_num)
theorem B5808581 : Blo 1528461 5808581 := bbase (se 4 (by rfl) ⟨544554, by rfl⟩ : syracuseStep 5808581 = 1089109) (by norm_num)
theorem B1720777 : Blo 1528461 1720777 := bbase (se 2 (by rfl) ⟨645291, by rfl⟩ : syracuseStep 1720777 = 1290583) (by norm_num)
theorem B2294237 : Blo 1528461 2294237 := bbase (se 3 (by rfl) ⟨430169, by rfl⟩ : syracuseStep 2294237 = 860339) (by norm_num)
theorem B1720813 : Blo 1528461 1720813 := bbase (se 3 (by rfl) ⟨322652, by rfl⟩ : syracuseStep 1720813 = 645305) (by norm_num)
theorem B2294261 : Blo 1528461 2294261 := bbase (se 5 (by rfl) ⟨107543, by rfl⟩ : syracuseStep 2294261 = 215087) (by norm_num)
theorem B3441149 : Blo 1528461 3441149 := bbase (se 3 (by rfl) ⟨645215, by rfl⟩ : syracuseStep 3441149 = 1290431) (by norm_num)
theorem B2580997 : Blo 1528461 2580997 := bbase (se 4 (by rfl) ⟨241968, by rfl⟩ : syracuseStep 2580997 = 483937) (by norm_num)
theorem B2294285 : Blo 1528461 2294285 := bbase (se 3 (by rfl) ⟨430178, by rfl⟩ : syracuseStep 2294285 = 860357) (by norm_num)
theorem B1720849 : Blo 1528461 1720849 := bbase (se 2 (by rfl) ⟨645318, by rfl⟩ : syracuseStep 1720849 = 1290637) (by norm_num)
theorem B2294309 : Blo 1528461 2294309 := bbase (se 4 (by rfl) ⟨215091, by rfl⟩ : syracuseStep 2294309 = 430183) (by norm_num)
theorem B1720885 : Blo 1528461 1720885 := bbase (se 5 (by rfl) ⟨80666, by rfl⟩ : syracuseStep 1720885 = 161333) (by norm_num)
theorem B2294333 : Blo 1528461 2294333 := bbase (se 3 (by rfl) ⟨430187, by rfl⟩ : syracuseStep 2294333 = 860375) (by norm_num)
theorem B3441221 : Blo 1528461 3441221 := bbase (se 4 (by rfl) ⟨322614, by rfl⟩ : syracuseStep 3441221 = 645229) (by norm_num)
theorem B2294357 : Blo 1528461 2294357 := bbase (se 8 (by rfl) ⟨13443, by rfl⟩ : syracuseStep 2294357 = 26887) (by norm_num)
theorem B1720921 : Blo 1528461 1720921 := bbase (se 2 (by rfl) ⟨645345, by rfl⟩ : syracuseStep 1720921 = 1290691) (by norm_num)
theorem B2581085 : Blo 1528461 2581085 := bbase (se 3 (by rfl) ⟨483953, by rfl⟩ : syracuseStep 2581085 = 967907) (by norm_num)
theorem B2450021 : Blo 1528461 2450021 := bbase (se 4 (by rfl) ⟨229689, by rfl⟩ : syracuseStep 2450021 = 459379) (by norm_num)
theorem B2294381 : Blo 1528461 2294381 := bbase (se 3 (by rfl) ⟨430196, by rfl⟩ : syracuseStep 2294381 = 860393) (by norm_num)
theorem B5161589 : Blo 1528461 5161589 := bbase (se 5 (by rfl) ⟨241949, by rfl⟩ : syracuseStep 5161589 = 483899) (by norm_num)
theorem B1720957 : Blo 1528461 1720957 := bbase (se 3 (by rfl) ⟨322679, by rfl⟩ : syracuseStep 1720957 = 645359) (by norm_num)
theorem B2294405 : Blo 1528461 2294405 := bbase (se 4 (by rfl) ⟨215100, by rfl⟩ : syracuseStep 2294405 = 430201) (by norm_num)
theorem B3441293 : Blo 1528461 3441293 := bbase (se 3 (by rfl) ⟨645242, by rfl⟩ : syracuseStep 3441293 = 1290485) (by norm_num)
theorem B2294429 : Blo 1528461 2294429 := bbase (se 3 (by rfl) ⟨430205, by rfl⟩ : syracuseStep 2294429 = 860411) (by norm_num)
theorem B1720993 : Blo 1528461 1720993 := bbase (se 2 (by rfl) ⟨645372, by rfl⟩ : syracuseStep 1720993 = 1290745) (by norm_num)
theorem B2294453 : Blo 1528461 2294453 := bbase (se 5 (by rfl) ⟨107552, by rfl⟩ : syracuseStep 2294453 = 215105) (by norm_num)
theorem B1721029 : Blo 1528461 1721029 := bbase (se 4 (by rfl) ⟨161346, by rfl⟩ : syracuseStep 1721029 = 322693) (by norm_num)
theorem B2294477 : Blo 1528461 2294477 := bbase (se 3 (by rfl) ⟨430214, by rfl⟩ : syracuseStep 2294477 = 860429) (by norm_num)
theorem B3441365 : Blo 1528461 3441365 := bbase (se 7 (by rfl) ⟨40328, by rfl⟩ : syracuseStep 3441365 = 80657) (by norm_num)
theorem B2581213 : Blo 1528461 2581213 := bbase (se 3 (by rfl) ⟨483977, by rfl⟩ : syracuseStep 2581213 = 967955) (by norm_num)
theorem B2294501 : Blo 1528461 2294501 := bbase (se 4 (by rfl) ⟨215109, by rfl⟩ : syracuseStep 2294501 = 430219) (by norm_num)
theorem B1721065 : Blo 1528461 1721065 := bbase (se 2 (by rfl) ⟨645399, by rfl⟩ : syracuseStep 1721065 = 1290799) (by norm_num)
theorem B6972149 : Blo 1528461 6972149 := bbase (se 5 (by rfl) ⟨326819, by rfl⟩ : syracuseStep 6972149 = 653639) (by norm_num)
theorem B2294525 : Blo 1528461 2294525 := bbase (se 3 (by rfl) ⟨430223, by rfl⟩ : syracuseStep 2294525 = 860447) (by norm_num)
theorem B5235461 : Blo 1528461 5235461 := bbase (se 4 (by rfl) ⟨490824, by rfl⟩ : syracuseStep 5235461 = 981649) (by norm_num)
theorem B1721101 : Blo 1528461 1721101 := bbase (se 3 (by rfl) ⟨322706, by rfl⟩ : syracuseStep 1721101 = 645413) (by norm_num)
theorem B2294549 : Blo 1528461 2294549 := bbase (se 6 (by rfl) ⟨53778, by rfl⟩ : syracuseStep 2294549 = 107557) (by norm_num)
theorem B3441437 : Blo 1528461 3441437 := bbase (se 3 (by rfl) ⟨645269, by rfl⟩ : syracuseStep 3441437 = 1290539) (by norm_num)
theorem B2294573 : Blo 1528461 2294573 := bbase (se 3 (by rfl) ⟨430232, by rfl⟩ : syracuseStep 2294573 = 860465) (by norm_num)
theorem B1721137 : Blo 1528461 1721137 := bbase (se 2 (by rfl) ⟨645426, by rfl⟩ : syracuseStep 1721137 = 1290853) (by norm_num)
theorem B2581301 : Blo 1528461 2581301 := bbase (se 5 (by rfl) ⟨120998, by rfl⟩ : syracuseStep 2581301 = 241997) (by norm_num)
theorem B2294597 : Blo 1528461 2294597 := bbase (se 4 (by rfl) ⟨215118, by rfl⟩ : syracuseStep 2294597 = 430237) (by norm_num)
theorem B1721173 : Blo 1528461 1721173 := bbase (se 9 (by rfl) ⟨5042, by rfl⟩ : syracuseStep 1721173 = 10085) (by norm_num)
theorem B2294621 : Blo 1528461 2294621 := bbase (se 3 (by rfl) ⟨430241, by rfl⟩ : syracuseStep 2294621 = 860483) (by norm_num)
theorem B3441509 : Blo 1528461 3441509 := bbase (se 4 (by rfl) ⟨322641, by rfl⟩ : syracuseStep 3441509 = 645283) (by norm_num)
theorem B2294645 : Blo 1528461 2294645 := bbase (se 5 (by rfl) ⟨107561, by rfl⟩ : syracuseStep 2294645 = 215123) (by norm_num)
theorem B1721209 : Blo 1528461 1721209 := bbase (se 2 (by rfl) ⟨645453, by rfl⟩ : syracuseStep 1721209 = 1290907) (by norm_num)
theorem B2294669 : Blo 1528461 2294669 := bbase (se 3 (by rfl) ⟨430250, by rfl⟩ : syracuseStep 2294669 = 860501) (by norm_num)
theorem B1655701 : Blo 1528461 1655701 := bbase (se 6 (by rfl) ⟨38805, by rfl⟩ : syracuseStep 1655701 = 77611) (by norm_num)
theorem B1721245 : Blo 1528461 1721245 := bbase (se 3 (by rfl) ⟨322733, by rfl⟩ : syracuseStep 1721245 = 645467) (by norm_num)
theorem B2294693 : Blo 1528461 2294693 := bbase (se 4 (by rfl) ⟨215127, by rfl⟩ : syracuseStep 2294693 = 430255) (by norm_num)
theorem B3441581 : Blo 1528461 3441581 := bbase (se 3 (by rfl) ⟨645296, by rfl⟩ : syracuseStep 3441581 = 1290593) (by norm_num)
theorem B13067189 : Blo 1528461 13067189 := bbase (se 5 (by rfl) ⟨612524, by rfl⟩ : syracuseStep 13067189 = 1225049) (by norm_num)
theorem B2581429 : Blo 1528461 2581429 := bbase (se 5 (by rfl) ⟨121004, by rfl⟩ : syracuseStep 2581429 = 242009) (by norm_num)
theorem B2294717 : Blo 1528461 2294717 := bbase (se 3 (by rfl) ⟨430259, by rfl⟩ : syracuseStep 2294717 = 860519) (by norm_num)
theorem B1721281 : Blo 1528461 1721281 := bbase (se 2 (by rfl) ⟨645480, by rfl⟩ : syracuseStep 1721281 = 1290961) (by norm_num)
theorem B2294741 : Blo 1528461 2294741 := bbase (se 7 (by rfl) ⟨26891, by rfl⟩ : syracuseStep 2294741 = 53783) (by norm_num)
theorem B1721317 : Blo 1528461 1721317 := bbase (se 4 (by rfl) ⟨161373, by rfl⟩ : syracuseStep 1721317 = 322747) (by norm_num)
theorem B2294765 : Blo 1528461 2294765 := bbase (se 3 (by rfl) ⟨430268, by rfl⟩ : syracuseStep 2294765 = 860537) (by norm_num)
theorem B3441653 : Blo 1528461 3441653 := bbase (se 5 (by rfl) ⟨161327, by rfl⟩ : syracuseStep 3441653 = 322655) (by norm_num)
theorem B2294789 : Blo 1528461 2294789 := bbase (se 4 (by rfl) ⟨215136, by rfl⟩ : syracuseStep 2294789 = 430273) (by norm_num)
theorem B1721353 : Blo 1528461 1721353 := bbase (se 2 (by rfl) ⟨645507, by rfl⟩ : syracuseStep 1721353 = 1291015) (by norm_num)
theorem B2581517 : Blo 1528461 2581517 := bbase (se 3 (by rfl) ⟨484034, by rfl⟩ : syracuseStep 2581517 = 968069) (by norm_num)
theorem B2294813 : Blo 1528461 2294813 := bbase (se 3 (by rfl) ⟨430277, by rfl⟩ : syracuseStep 2294813 = 860555) (by norm_num)
theorem B5162021 : Blo 1528461 5162021 := bbase (se 4 (by rfl) ⟨483939, by rfl⟩ : syracuseStep 5162021 = 967879) (by norm_num)
theorem B1721389 : Blo 1528461 1721389 := bbase (se 3 (by rfl) ⟨322760, by rfl⟩ : syracuseStep 1721389 = 645521) (by norm_num)
theorem B2294837 : Blo 1528461 2294837 := bbase (se 5 (by rfl) ⟨107570, by rfl⟩ : syracuseStep 2294837 = 215141) (by norm_num)
theorem B3441725 : Blo 1528461 3441725 := bbase (se 3 (by rfl) ⟨645323, by rfl⟩ : syracuseStep 3441725 = 1290647) (by norm_num)
theorem B2294861 : Blo 1528461 2294861 := bbase (se 3 (by rfl) ⟨430286, by rfl⟩ : syracuseStep 2294861 = 860573) (by norm_num)
theorem B1721425 : Blo 1528461 1721425 := bbase (se 2 (by rfl) ⟨645534, by rfl⟩ : syracuseStep 1721425 = 1291069) (by norm_num)
theorem B2294885 : Blo 1528461 2294885 := bbase (se 4 (by rfl) ⟨215145, by rfl⟩ : syracuseStep 2294885 = 430291) (by norm_num)
theorem B1721461 : Blo 1528461 1721461 := bbase (se 5 (by rfl) ⟨80693, by rfl⟩ : syracuseStep 1721461 = 161387) (by norm_num)
theorem B2294909 : Blo 1528461 2294909 := bbase (se 3 (by rfl) ⟨430295, by rfl⟩ : syracuseStep 2294909 = 860591) (by norm_num)
theorem B3441797 : Blo 1528461 3441797 := bbase (se 4 (by rfl) ⟨322668, by rfl⟩ : syracuseStep 3441797 = 645337) (by norm_num)
theorem B2581645 : Blo 1528461 2581645 := bbase (se 3 (by rfl) ⟨484058, by rfl⟩ : syracuseStep 2581645 = 968117) (by norm_num)
theorem B2294933 : Blo 1528461 2294933 := bbase (se 6 (by rfl) ⟨53787, by rfl⟩ : syracuseStep 2294933 = 107575) (by norm_num)
theorem B1721497 : Blo 1528461 1721497 := bbase (se 2 (by rfl) ⟨645561, by rfl⟩ : syracuseStep 1721497 = 1291123) (by norm_num)
theorem B2294957 : Blo 1528461 2294957 := bbase (se 3 (by rfl) ⟨430304, by rfl⟩ : syracuseStep 2294957 = 860609) (by norm_num)
theorem B1721533 : Blo 1528461 1721533 := bbase (se 3 (by rfl) ⟨322787, by rfl⟩ : syracuseStep 1721533 = 645575) (by norm_num)
theorem B1934533 : Blo 1528461 1934533 := bbase (se 4 (by rfl) ⟨181362, by rfl⟩ : syracuseStep 1934533 = 362725) (by norm_num)
theorem B2294981 : Blo 1528461 2294981 := bbase (se 4 (by rfl) ⟨215154, by rfl⟩ : syracuseStep 2294981 = 430309) (by norm_num)
theorem B3441869 : Blo 1528461 3441869 := bbase (se 3 (by rfl) ⟨645350, by rfl⟩ : syracuseStep 3441869 = 1290701) (by norm_num)
theorem B2295005 : Blo 1528461 2295005 := bbase (se 3 (by rfl) ⟨430313, by rfl⟩ : syracuseStep 2295005 = 860627) (by norm_num)
theorem B1721569 : Blo 1528461 1721569 := bbase (se 2 (by rfl) ⟨645588, by rfl⟩ : syracuseStep 1721569 = 1291177) (by norm_num)
theorem B2581733 : Blo 1528461 2581733 := bbase (se 4 (by rfl) ⟨242037, by rfl⟩ : syracuseStep 2581733 = 484075) (by norm_num)
theorem B2295029 : Blo 1528461 2295029 := bbase (se 5 (by rfl) ⟨107579, by rfl⟩ : syracuseStep 2295029 = 215159) (by norm_num)
theorem B1549561 : Blo 1528461 1549561 := bbase (se 2 (by rfl) ⟨581085, by rfl⟩ : syracuseStep 1549561 = 1162171) (by norm_num)
theorem B1721605 : Blo 1528461 1721605 := bbase (se 4 (by rfl) ⟨161400, by rfl⟩ : syracuseStep 1721605 = 322801) (by norm_num)
theorem B2295053 : Blo 1528461 2295053 := bbase (se 3 (by rfl) ⟨430322, by rfl⟩ : syracuseStep 2295053 = 860645) (by norm_num)
theorem B3441941 : Blo 1528461 3441941 := bbase (se 6 (by rfl) ⟨80670, by rfl⟩ : syracuseStep 3441941 = 161341) (by norm_num)
theorem B2295077 : Blo 1528461 2295077 := bbase (se 4 (by rfl) ⟨215163, by rfl⟩ : syracuseStep 2295077 = 430327) (by norm_num)
theorem B1721641 : Blo 1528461 1721641 := bbase (se 2 (by rfl) ⟨645615, by rfl⟩ : syracuseStep 1721641 = 1291231) (by norm_num)
theorem B2295101 : Blo 1528461 2295101 := bbase (se 3 (by rfl) ⟨430331, by rfl⟩ : syracuseStep 2295101 = 860663) (by norm_num)
theorem B7742789 : Blo 1528461 7742789 := bbase (se 4 (by rfl) ⟨725886, by rfl⟩ : syracuseStep 7742789 = 1451773) (by norm_num)
theorem B1721677 : Blo 1528461 1721677 := bbase (se 3 (by rfl) ⟨322814, by rfl⟩ : syracuseStep 1721677 = 645629) (by norm_num)
theorem B8267093 : Blo 1528461 8267093 := bbase (se 12 (by rfl) ⟨3027, by rfl⟩ : syracuseStep 8267093 = 6055) (by norm_num)
theorem B2295125 : Blo 1528461 2295125 := bbase (se 12 (by rfl) ⟨840, by rfl⟩ : syracuseStep 2295125 = 1681) (by norm_num)
theorem B3442013 : Blo 1528461 3442013 := bbase (se 3 (by rfl) ⟨645377, by rfl⟩ : syracuseStep 3442013 = 1290755) (by norm_num)
theorem B2581861 : Blo 1528461 2581861 := bbase (se 4 (by rfl) ⟨242049, by rfl⟩ : syracuseStep 2581861 = 484099) (by norm_num)
theorem B2295149 : Blo 1528461 2295149 := bbase (se 3 (by rfl) ⟨430340, by rfl⟩ : syracuseStep 2295149 = 860681) (by norm_num)
theorem B1934705 : Blo 1528461 1934705 := bbase (se 2 (by rfl) ⟨725514, by rfl⟩ : syracuseStep 1934705 = 1451029) (by norm_num)
theorem B1721713 : Blo 1528461 1721713 := bbase (se 2 (by rfl) ⟨645642, by rfl⟩ : syracuseStep 1721713 = 1291285) (by norm_num)
theorem B2295173 : Blo 1528461 2295173 := bbase (se 4 (by rfl) ⟨215172, by rfl⟩ : syracuseStep 2295173 = 430345) (by norm_num)
theorem B4965781 : Blo 1528461 4965781 := bbase (se 6 (by rfl) ⟨116385, by rfl⟩ : syracuseStep 4965781 = 232771) (by norm_num)
theorem B1721749 : Blo 1528461 1721749 := bbase (se 6 (by rfl) ⟨40353, by rfl⟩ : syracuseStep 1721749 = 80707) (by norm_num)
theorem B2295197 : Blo 1528461 2295197 := bbase (se 3 (by rfl) ⟨430349, by rfl⟩ : syracuseStep 2295197 = 860699) (by norm_num)
theorem B3442085 : Blo 1528461 3442085 := bbase (se 4 (by rfl) ⟨322695, by rfl⟩ : syracuseStep 3442085 = 645391) (by norm_num)
theorem B1934761 : Blo 1528461 1934761 := bbase (se 2 (by rfl) ⟨725535, by rfl⟩ : syracuseStep 1934761 = 1451071) (by norm_num)
theorem B2295221 : Blo 1528461 2295221 := bbase (se 5 (by rfl) ⟨107588, by rfl⟩ : syracuseStep 2295221 = 215177) (by norm_num)
theorem B2581949 : Blo 1528461 2581949 := bbase (se 3 (by rfl) ⟨484115, by rfl⟩ : syracuseStep 2581949 = 968231) (by norm_num)
theorem B2450893 : Blo 1528461 2450893 := bbase (se 3 (by rfl) ⟨459542, by rfl⟩ : syracuseStep 2450893 = 919085) (by norm_num)
theorem B2295245 : Blo 1528461 2295245 := bbase (se 3 (by rfl) ⟨430358, by rfl⟩ : syracuseStep 2295245 = 860717) (by norm_num)
theorem B5162453 : Blo 1528461 5162453 := bbase (se 7 (by rfl) ⟨60497, by rfl⟩ : syracuseStep 5162453 = 120995) (by norm_num)
theorem B2295269 : Blo 1528461 2295269 := bbase (se 4 (by rfl) ⟨215181, by rfl⟩ : syracuseStep 2295269 = 430363) (by norm_num)
theorem B3442157 : Blo 1528461 3442157 := bbase (se 3 (by rfl) ⟨645404, by rfl⟩ : syracuseStep 3442157 = 1290809) (by norm_num)
theorem B2295293 : Blo 1528461 2295293 := bbase (se 3 (by rfl) ⟨430367, by rfl⟩ : syracuseStep 2295293 = 860735) (by norm_num)
theorem B1934857 : Blo 1528461 1934857 := bbase (se 2 (by rfl) ⟨725571, by rfl⟩ : syracuseStep 1934857 = 1451143) (by norm_num)
theorem B2295317 : Blo 1528461 2295317 := bbase (se 6 (by rfl) ⟨53796, by rfl⟩ : syracuseStep 2295317 = 107593) (by norm_num)
theorem B2450989 : Blo 1528461 2450989 := bbase (se 3 (by rfl) ⟨459560, by rfl⟩ : syracuseStep 2450989 = 919121) (by norm_num)
theorem B2295341 : Blo 1528461 2295341 := bbase (se 3 (by rfl) ⟨430376, by rfl⟩ : syracuseStep 2295341 = 860753) (by norm_num)
theorem B3442229 : Blo 1528461 3442229 := bbase (se 5 (by rfl) ⟨161354, by rfl⟩ : syracuseStep 3442229 = 322709) (by norm_num)
theorem B2582077 : Blo 1528461 2582077 := bbase (se 3 (by rfl) ⟨484139, by rfl⟩ : syracuseStep 2582077 = 968279) (by norm_num)
theorem B2295365 : Blo 1528461 2295365 := bbase (se 4 (by rfl) ⟨215190, by rfl⟩ : syracuseStep 2295365 = 430381) (by norm_num)
theorem B2295389 : Blo 1528461 2295389 := bbase (se 3 (by rfl) ⟨430385, by rfl⟩ : syracuseStep 2295389 = 860771) (by norm_num)
theorem B5809765 : Blo 1528461 5809765 := bbase (se 4 (by rfl) ⟨544665, by rfl⟩ : syracuseStep 5809765 = 1089331) (by norm_num)
theorem B2295413 : Blo 1528461 2295413 := bbase (se 5 (by rfl) ⟨107597, by rfl⟩ : syracuseStep 2295413 = 215195) (by norm_num)
theorem B3442301 : Blo 1528461 3442301 := bbase (se 3 (by rfl) ⟨645431, by rfl⟩ : syracuseStep 3442301 = 1290863) (by norm_num)
theorem B2295437 : Blo 1528461 2295437 := bbase (se 3 (by rfl) ⟨430394, by rfl⟩ : syracuseStep 2295437 = 860789) (by norm_num)
theorem B2582165 : Blo 1528461 2582165 := bbase (se 6 (by rfl) ⟨60519, by rfl⟩ : syracuseStep 2582165 = 121039) (by norm_num)
theorem B2295461 : Blo 1528461 2295461 := bbase (se 4 (by rfl) ⟨215199, by rfl⟩ : syracuseStep 2295461 = 430399) (by norm_num)
theorem B1935029 : Blo 1528461 1935029 := bbase (se 5 (by rfl) ⟨90704, by rfl⟩ : syracuseStep 1935029 = 181409) (by norm_num)
theorem B2295485 : Blo 1528461 2295485 := bbase (se 3 (by rfl) ⟨430403, by rfl⟩ : syracuseStep 2295485 = 860807) (by norm_num)
theorem B3442373 : Blo 1528461 3442373 := bbase (se 4 (by rfl) ⟨322722, by rfl⟩ : syracuseStep 3442373 = 645445) (by norm_num)
theorem B2451149 : Blo 1528461 2451149 := bbase (se 3 (by rfl) ⟨459590, by rfl⟩ : syracuseStep 2451149 = 919181) (by norm_num)
theorem B11175637 : Blo 1528461 11175637 := bbase (se 7 (by rfl) ⟨130964, by rfl⟩ : syracuseStep 11175637 = 261929) (by norm_num)
theorem B2295509 : Blo 1528461 2295509 := bbase (se 7 (by rfl) ⟨26900, by rfl⟩ : syracuseStep 2295509 = 53801) (by norm_num)
theorem B1935085 : Blo 1528461 1935085 := bbase (se 3 (by rfl) ⟨362828, by rfl⟩ : syracuseStep 1935085 = 725657) (by norm_num)
theorem B2295533 : Blo 1528461 2295533 := bbase (se 3 (by rfl) ⟨430412, by rfl⟩ : syracuseStep 2295533 = 860825) (by norm_num)
theorem B1836805 : Blo 1528461 1836805 := bbase (se 4 (by rfl) ⟨172200, by rfl⟩ : syracuseStep 1836805 = 344401) (by norm_num)
theorem B2295557 : Blo 1528461 2295557 := bbase (se 4 (by rfl) ⟨215208, by rfl⟩ : syracuseStep 2295557 = 430417) (by norm_num)
theorem B3442445 : Blo 1528461 3442445 := bbase (se 3 (by rfl) ⟨645458, by rfl⟩ : syracuseStep 3442445 = 1290917) (by norm_num)
theorem B2582293 : Blo 1528461 2582293 := bbase (se 6 (by rfl) ⟨60522, by rfl⟩ : syracuseStep 2582293 = 121045) (by norm_num)
theorem B2295581 : Blo 1528461 2295581 := bbase (se 3 (by rfl) ⟨430421, by rfl⟩ : syracuseStep 2295581 = 860843) (by norm_num)
theorem B2295605 : Blo 1528461 2295605 := bbase (se 5 (by rfl) ⟨107606, by rfl⟩ : syracuseStep 2295605 = 215213) (by norm_num)
theorem B1935181 : Blo 1528461 1935181 := bbase (se 3 (by rfl) ⟨362846, by rfl⟩ : syracuseStep 1935181 = 725693) (by norm_num)
theorem B2295629 : Blo 1528461 2295629 := bbase (se 3 (by rfl) ⟨430430, by rfl⟩ : syracuseStep 2295629 = 860861) (by norm_num)
theorem B2901845 : Blo 1528461 2901845 := bbase (se 9 (by rfl) ⟨8501, by rfl⟩ : syracuseStep 2901845 = 17003) (by norm_num)
theorem B3442517 : Blo 1528461 3442517 := bbase (se 9 (by rfl) ⟨10085, by rfl⟩ : syracuseStep 3442517 = 20171) (by norm_num)
theorem B1836901 : Blo 1528461 1836901 := bbase (se 4 (by rfl) ⟨172209, by rfl⟩ : syracuseStep 1836901 = 344419) (by norm_num)
theorem B2295653 : Blo 1528461 2295653 := bbase (se 4 (by rfl) ⟨215217, by rfl⟩ : syracuseStep 2295653 = 430435) (by norm_num)
theorem B2582381 : Blo 1528461 2582381 := bbase (se 3 (by rfl) ⟨484196, by rfl⟩ : syracuseStep 2582381 = 968393) (by norm_num)
theorem B2295677 : Blo 1528461 2295677 := bbase (se 3 (by rfl) ⟨430439, by rfl⟩ : syracuseStep 2295677 = 860879) (by norm_num)
theorem B5162885 : Blo 1528461 5162885 := bbase (se 4 (by rfl) ⟨484020, by rfl⟩ : syracuseStep 5162885 = 968041) (by norm_num)
theorem B5810069 : Blo 1528461 5810069 := bbase (se 6 (by rfl) ⟨136173, by rfl⟩ : syracuseStep 5810069 = 272347) (by norm_num)
theorem B3442589 : Blo 1528461 3442589 := bbase (se 3 (by rfl) ⟨645485, by rfl⟩ : syracuseStep 3442589 = 1290971) (by norm_num)
theorem B3442661 : Blo 1528461 3442661 := bbase (se 4 (by rfl) ⟨322749, by rfl⟩ : syracuseStep 3442661 = 645499) (by norm_num)
theorem B2901997 : Blo 1528461 2901997 := bbase (se 3 (by rfl) ⟨544124, by rfl⟩ : syracuseStep 2901997 = 1088249) (by norm_num)
theorem B2582509 : Blo 1528461 2582509 := bbase (se 3 (by rfl) ⟨484220, by rfl⟩ : syracuseStep 2582509 = 968441) (by norm_num)
theorem B1935353 : Blo 1528461 1935353 := bbase (se 2 (by rfl) ⟨725757, by rfl⟩ : syracuseStep 1935353 = 1451515) (by norm_num)
theorem B3442733 : Blo 1528461 3442733 := bbase (se 3 (by rfl) ⟨645512, by rfl⟩ : syracuseStep 3442733 = 1291025) (by norm_num)
theorem B1935409 : Blo 1528461 1935409 := bbase (se 2 (by rfl) ⟨725778, by rfl⟩ : syracuseStep 1935409 = 1451557) (by norm_num)
theorem B2582597 : Blo 1528461 2582597 := bbase (se 4 (by rfl) ⟨242118, by rfl⟩ : syracuseStep 2582597 = 484237) (by norm_num)
theorem B3442805 : Blo 1528461 3442805 := bbase (se 5 (by rfl) ⟨161381, by rfl⟩ : syracuseStep 3442805 = 322763) (by norm_num)
theorem B1935505 : Blo 1528461 1935505 := bbase (se 2 (by rfl) ⟨725814, by rfl⟩ : syracuseStep 1935505 = 1451629) (by norm_num)
theorem B1632421 : Blo 1528461 1632421 := bbase (se 4 (by rfl) ⟨153039, by rfl⟩ : syracuseStep 1632421 = 306079) (by norm_num)
theorem B3442877 : Blo 1528461 3442877 := bbase (se 3 (by rfl) ⟨645539, by rfl⟩ : syracuseStep 3442877 = 1291079) (by norm_num)
theorem B1837285 : Blo 1528461 1837285 := bbase (se 4 (by rfl) ⟨172245, by rfl⟩ : syracuseStep 1837285 = 344491) (by norm_num)
theorem B1632493 : Blo 1528461 1632493 := bbase (se 3 (by rfl) ⟨306092, by rfl⟩ : syracuseStep 1632493 = 612185) (by norm_num)
theorem B3442949 : Blo 1528461 3442949 := bbase (se 4 (by rfl) ⟨322776, by rfl⟩ : syracuseStep 3442949 = 645553) (by norm_num)
theorem B2902301 : Blo 1528461 2902301 := bbase (se 3 (by rfl) ⟨544181, by rfl⟩ : syracuseStep 2902301 = 1088363) (by norm_num)
theorem B5163317 : Blo 1528461 5163317 := bbase (se 5 (by rfl) ⟨242030, by rfl⟩ : syracuseStep 5163317 = 484061) (by norm_num)
theorem B1935677 : Blo 1528461 1935677 := bbase (se 3 (by rfl) ⟨362939, by rfl⟩ : syracuseStep 1935677 = 725879) (by norm_num)
theorem B3869005 : Blo 1528461 3869005 := bbase (se 3 (by rfl) ⟨725438, by rfl⟩ : syracuseStep 3869005 = 1450877) (by norm_num)
theorem B3443021 : Blo 1528461 3443021 := bbase (se 3 (by rfl) ⟨645566, by rfl⟩ : syracuseStep 3443021 = 1291133) (by norm_num)
theorem B1935733 : Blo 1528461 1935733 := bbase (se 5 (by rfl) ⟨90737, by rfl⟩ : syracuseStep 1935733 = 181475) (by norm_num)
theorem B1862021 : Blo 1528461 1862021 := bbase (se 4 (by rfl) ⟨174564, by rfl⟩ : syracuseStep 1862021 = 349129) (by norm_num)
theorem B6531461 : Blo 1528461 6531461 := bbase (se 4 (by rfl) ⟨612324, by rfl⟩ : syracuseStep 6531461 = 1224649) (by norm_num)
theorem B3443093 : Blo 1528461 3443093 := bbase (se 6 (by rfl) ⟨80697, by rfl⟩ : syracuseStep 3443093 = 161395) (by norm_num)
theorem B1632673 : Blo 1528461 1632673 := bbase (se 2 (by rfl) ⟨612252, by rfl⟩ : syracuseStep 1632673 = 1224505) (by norm_num)
theorem B3869117 : Blo 1528461 3869117 := bbase (se 3 (by rfl) ⟨725459, by rfl⟩ : syracuseStep 3869117 = 1450919) (by norm_num)
theorem B10463701 : Blo 1528461 10463701 := bbase (se 7 (by rfl) ⟨122621, by rfl⟩ : syracuseStep 10463701 = 245243) (by norm_num)
theorem B1935829 : Blo 1528461 1935829 := bbase (se 7 (by rfl) ⟨22685, by rfl⟩ : syracuseStep 1935829 = 45371) (by norm_num)
theorem B3443165 : Blo 1528461 3443165 := bbase (se 3 (by rfl) ⟨645593, by rfl⟩ : syracuseStep 3443165 = 1291187) (by norm_num)
theorem B2755093 : Blo 1528461 2755093 := bbase (se 6 (by rfl) ⟨64572, by rfl⟩ : syracuseStep 2755093 = 129145) (by norm_num)
theorem B3443237 : Blo 1528461 3443237 := bbase (se 4 (by rfl) ⟨322803, by rfl⟩ : syracuseStep 3443237 = 645607) (by norm_num)
theorem B7744085 : Blo 1528461 7744085 := bbase (se 8 (by rfl) ⟨45375, by rfl⟩ : syracuseStep 7744085 = 90751) (by norm_num)
theorem B4901477 : Blo 1528461 4901477 := bbase (se 4 (by rfl) ⟨459513, by rfl⟩ : syracuseStep 4901477 = 919027) (by norm_num)
theorem B3443309 : Blo 1528461 3443309 := bbase (se 3 (by rfl) ⟨645620, by rfl⟩ : syracuseStep 3443309 = 1291241) (by norm_num)
theorem B3869309 : Blo 1528461 3869309 := bbase (se 3 (by rfl) ⟨725495, by rfl⟩ : syracuseStep 3869309 = 1450991) (by norm_num)
theorem B1936001 : Blo 1528461 1936001 := bbase (se 2 (by rfl) ⟨726000, by rfl⟩ : syracuseStep 1936001 = 1452001) (by norm_num)
theorem B6531749 : Blo 1528461 6531749 := bbase (se 4 (by rfl) ⟨612351, by rfl⟩ : syracuseStep 6531749 = 1224703) (by norm_num)
theorem B3443381 : Blo 1528461 3443381 := bbase (se 5 (by rfl) ⟨161408, by rfl⟩ : syracuseStep 3443381 = 322817) (by norm_num)
theorem B1936057 : Blo 1528461 1936057 := bbase (se 2 (by rfl) ⟨726021, by rfl⟩ : syracuseStep 1936057 = 1452043) (by norm_num)
theorem B1551053 : Blo 1528461 1551053 := bbase (se 3 (by rfl) ⟨290822, by rfl⟩ : syracuseStep 1551053 = 581645) (by norm_num)
theorem B4131557 : Blo 1528461 4131557 := bbase (se 4 (by rfl) ⟨387333, by rfl⟩ : syracuseStep 4131557 = 774667) (by norm_num)
theorem B5163749 : Blo 1528461 5163749 := bbase (se 4 (by rfl) ⟨484101, by rfl⟩ : syracuseStep 5163749 = 968203) (by norm_num)
theorem B2755309 : Blo 1528461 2755309 := bbase (se 3 (by rfl) ⟨516620, by rfl⟩ : syracuseStep 2755309 = 1033241) (by norm_num)
theorem B8833781 : Blo 1528461 8833781 := bbase (se 5 (by rfl) ⟨414083, by rfl⟩ : syracuseStep 8833781 = 828167) (by norm_num)
theorem B3443453 : Blo 1528461 3443453 := bbase (se 3 (by rfl) ⟨645647, by rfl⟩ : syracuseStep 3443453 = 1291295) (by norm_num)
theorem B1936153 : Blo 1528461 1936153 := bbase (se 2 (by rfl) ⟨726057, by rfl⟩ : syracuseStep 1936153 = 1452115) (by norm_num)
theorem B3443525 : Blo 1528461 3443525 := bbase (se 4 (by rfl) ⟨322830, by rfl⟩ : syracuseStep 3443525 = 645661) (by norm_num)
theorem B2206541 : Blo 1528461 2206541 := bbase (se 3 (by rfl) ⟨413726, by rfl⟩ : syracuseStep 2206541 = 827453) (by norm_num)
theorem B23554901 : Blo 1528461 23554901 := bbase (se 9 (by rfl) ⟨69008, by rfl⟩ : syracuseStep 23554901 = 138017) (by norm_num)
theorem B1633117 : Blo 1528461 1633117 := bbase (se 3 (by rfl) ⟨306209, by rfl⟩ : syracuseStep 1633117 = 612419) (by norm_num)
theorem B1862509 : Blo 1528461 1862509 := bbase (se 3 (by rfl) ⟨349220, by rfl⟩ : syracuseStep 1862509 = 698441) (by norm_num)
theorem B1936325 : Blo 1528461 1936325 := bbase (se 4 (by rfl) ⟨181530, by rfl⟩ : syracuseStep 1936325 = 363061) (by norm_num)
theorem B3869653 : Blo 1528461 3869653 := bbase (se 7 (by rfl) ⟨45347, by rfl⟩ : syracuseStep 3869653 = 90695) (by norm_num)
theorem B9563093 : Blo 1528461 9563093 := bbase (se 7 (by rfl) ⟨112067, by rfl⟩ : syracuseStep 9563093 = 224135) (by norm_num)
theorem B1633241 : Blo 1528461 1633241 := bbase (se 2 (by rfl) ⟨612465, by rfl⟩ : syracuseStep 1633241 = 1224931) (by norm_num)
theorem B10464245 : Blo 1528461 10464245 := bbase (se 5 (by rfl) ⟨490511, by rfl⟩ : syracuseStep 10464245 = 981023) (by norm_num)
theorem B1936381 : Blo 1528461 1936381 := bbase (se 3 (by rfl) ⟨363071, by rfl⟩ : syracuseStep 1936381 = 726143) (by norm_num)
theorem B2903053 : Blo 1528461 2903053 := bbase (se 3 (by rfl) ⟨544322, by rfl⟩ : syracuseStep 2903053 = 1088645) (by norm_num)
theorem B5966885 : Blo 1528461 5966885 := bbase (se 4 (by rfl) ⟨559395, by rfl⟩ : syracuseStep 5966885 = 1118791) (by norm_num)
theorem B4131893 : Blo 1528461 4131893 := bbase (se 5 (by rfl) ⟨193682, by rfl⟩ : syracuseStep 4131893 = 387365) (by norm_num)
theorem B3869765 : Blo 1528461 3869765 := bbase (se 4 (by rfl) ⟨362790, by rfl⟩ : syracuseStep 3869765 = 725581) (by norm_num)
theorem B1936477 : Blo 1528461 1936477 := bbase (se 3 (by rfl) ⟨363089, by rfl⟩ : syracuseStep 1936477 = 726179) (by norm_num)
theorem B5885077 : Blo 1528461 5885077 := bbase (se 6 (by rfl) ⟨137931, by rfl⟩ : syracuseStep 5885077 = 275863) (by norm_num)
theorem B5164181 : Blo 1528461 5164181 := bbase (se 6 (by rfl) ⟨121035, by rfl⟩ : syracuseStep 5164181 = 242071) (by norm_num)
theorem B2903197 : Blo 1528461 2903197 := bbase (se 3 (by rfl) ⟨544349, by rfl⟩ : syracuseStep 2903197 = 1088699) (by norm_num)
theorem B1633493 : Blo 1528461 1633493 := bbase (se 7 (by rfl) ⟨19142, by rfl⟩ : syracuseStep 1633493 = 38285) (by norm_num)
theorem B1838333 : Blo 1528461 1838333 := bbase (se 3 (by rfl) ⟨344687, by rfl⟩ : syracuseStep 1838333 = 689375) (by norm_num)
theorem B3869957 : Blo 1528461 3869957 := bbase (se 4 (by rfl) ⟨362808, by rfl⟩ : syracuseStep 3869957 = 725617) (by norm_num)
theorem B1936649 : Blo 1528461 1936649 := bbase (se 2 (by rfl) ⟨726243, by rfl⟩ : syracuseStep 1936649 = 1452487) (by norm_num)
theorem B2067725 : Blo 1528461 2067725 := bbase (se 3 (by rfl) ⟨387698, by rfl⟩ : syracuseStep 2067725 = 775397) (by norm_num)
theorem B1961245 : Blo 1528461 1961245 := bbase (se 3 (by rfl) ⟨367733, by rfl⟩ : syracuseStep 1961245 = 735467) (by norm_num)
theorem B2903357 : Blo 1528461 2903357 := bbase (se 3 (by rfl) ⟨544379, by rfl⟩ : syracuseStep 2903357 = 1088759) (by norm_num)
theorem B1936705 : Blo 1528461 1936705 := bbase (se 2 (by rfl) ⟨726264, by rfl⟩ : syracuseStep 1936705 = 1452529) (by norm_num)
theorem B6532501 : Blo 1528461 6532501 := bbase (se 6 (by rfl) ⟨153105, by rfl⟩ : syracuseStep 6532501 = 306211) (by norm_num)
theorem B1936801 : Blo 1528461 1936801 := bbase (se 2 (by rfl) ⟨726300, by rfl⟩ : syracuseStep 1936801 = 1452601) (by norm_num)
theorem B2903501 : Blo 1528461 2903501 := bbase (se 3 (by rfl) ⟨544406, by rfl⟩ : syracuseStep 2903501 = 1088813) (by norm_num)
theorem B3141109 : Blo 1528461 3141109 := bbase (se 5 (by rfl) ⟨147239, by rfl⟩ : syracuseStep 3141109 = 294479) (by norm_num)
theorem B4902389 : Blo 1528461 4902389 := bbase (se 5 (by rfl) ⟨229799, by rfl⟩ : syracuseStep 4902389 = 459599) (by norm_num)
theorem B3403301 : Blo 1528461 3403301 := bbase (se 4 (by rfl) ⟨319059, by rfl⟩ : syracuseStep 3403301 = 638119) (by norm_num)
theorem B1961533 : Blo 1528461 1961533 := bbase (se 3 (by rfl) ⟨367787, by rfl⟩ : syracuseStep 1961533 = 735575) (by norm_num)
theorem B5164613 : Blo 1528461 5164613 := bbase (se 4 (by rfl) ⟨484182, by rfl⟩ : syracuseStep 5164613 = 968365) (by norm_num)
theorem B1936973 : Blo 1528461 1936973 := bbase (se 3 (by rfl) ⟨363182, by rfl⟩ : syracuseStep 1936973 = 726365) (by norm_num)
theorem B3870301 : Blo 1528461 3870301 := bbase (se 3 (by rfl) ⟨725681, by rfl⟩ : syracuseStep 3870301 = 1451363) (by norm_num)
theorem B1633937 : Blo 1528461 1633937 := bbase (se 2 (by rfl) ⟨612726, by rfl⟩ : syracuseStep 1633937 = 1225453) (by norm_num)
theorem B5508773 : Blo 1528461 5508773 := bbase (se 4 (by rfl) ⟨516447, by rfl⟩ : syracuseStep 5508773 = 1032895) (by norm_num)
theorem B2617013 : Blo 1528461 2617013 := bbase (se 5 (by rfl) ⟨122672, by rfl⟩ : syracuseStep 2617013 = 245345) (by norm_num)
theorem B3870413 : Blo 1528461 3870413 := bbase (se 3 (by rfl) ⟨725702, by rfl⟩ : syracuseStep 3870413 = 1451405) (by norm_num)
theorem B2903789 : Blo 1528461 2903789 := bbase (se 3 (by rfl) ⟨544460, by rfl⟩ : syracuseStep 2903789 = 1088921) (by norm_num)
theorem B5508917 : Blo 1528461 5508917 := bbase (se 5 (by rfl) ⟨258230, by rfl⟩ : syracuseStep 5508917 = 516461) (by norm_num)
theorem B7745381 : Blo 1528461 7745381 := bbase (se 4 (by rfl) ⟨726129, by rfl⟩ : syracuseStep 7745381 = 1452259) (by norm_num)
theorem B1961861 : Blo 1528461 1961861 := bbase (se 4 (by rfl) ⟨183924, by rfl⟩ : syracuseStep 1961861 = 367849) (by norm_num)
theorem B2903941 : Blo 1528461 2903941 := bbase (se 4 (by rfl) ⟨272244, by rfl⟩ : syracuseStep 2903941 = 544489) (by norm_num)
theorem B1634185 : Blo 1528461 1634185 := bbase (se 2 (by rfl) ⟨612819, by rfl⟩ : syracuseStep 1634185 = 1225639) (by norm_num)
theorem B3870605 : Blo 1528461 3870605 := bbase (se 3 (by rfl) ⟨725738, by rfl⟩ : syracuseStep 3870605 = 1451477) (by norm_num)
theorem B5230565 : Blo 1528461 5230565 := bbase (se 4 (by rfl) ⟨490365, by rfl⟩ : syracuseStep 5230565 = 980731) (by norm_num)
theorem B5165045 : Blo 1528461 5165045 := bbase (se 5 (by rfl) ⟨242111, by rfl⟩ : syracuseStep 5165045 = 484223) (by norm_num)
theorem B5451781 : Blo 1528461 5451781 := bbase (se 4 (by rfl) ⟨511104, by rfl⟩ : syracuseStep 5451781 = 1022209) (by norm_num)
theorem B11022389 : Blo 1528461 11022389 := bbase (se 5 (by rfl) ⟨516674, by rfl⟩ : syracuseStep 11022389 = 1033349) (by norm_num)
theorem B5509205 : Blo 1528461 5509205 := bbase (se 8 (by rfl) ⟨32280, by rfl⟩ : syracuseStep 5509205 = 64561) (by norm_num)
theorem B2756693 : Blo 1528461 2756693 := bbase (se 8 (by rfl) ⟨16152, by rfl⟩ : syracuseStep 2756693 = 32305) (by norm_num)
theorem B6533237 : Blo 1528461 6533237 := bbase (se 5 (by rfl) ⟨306245, by rfl⟩ : syracuseStep 6533237 = 612491) (by norm_num)
theorem B3264637 : Blo 1528461 3264637 := bbase (se 3 (by rfl) ⟨612119, by rfl⟩ : syracuseStep 3264637 = 1224239) (by norm_num)
theorem B4354181 : Blo 1528461 4354181 := bbase (se 4 (by rfl) ⟨408204, by rfl⟩ : syracuseStep 4354181 = 816409) (by norm_num)
theorem B2904245 : Blo 1528461 2904245 := bbase (se 5 (by rfl) ⟨136136, by rfl⟩ : syracuseStep 2904245 = 272273) (by norm_num)
theorem B3870949 : Blo 1528461 3870949 := bbase (se 4 (by rfl) ⟨362901, by rfl⟩ : syracuseStep 3870949 = 725803) (by norm_num)
theorem B2756845 : Blo 1528461 2756845 := bbase (se 3 (by rfl) ⟨516908, by rfl⟩ : syracuseStep 2756845 = 1033817) (by norm_num)
theorem B9793781 : Blo 1528461 9793781 := bbase (se 5 (by rfl) ⟨459083, by rfl⟩ : syracuseStep 9793781 = 918167) (by norm_num)
theorem B3264781 : Blo 1528461 3264781 := bbase (se 3 (by rfl) ⟨612146, by rfl⟩ : syracuseStep 3264781 = 1224293) (by norm_num)
theorem B2756909 : Blo 1528461 2756909 := bbase (se 3 (by rfl) ⟨516920, by rfl⟩ : syracuseStep 2756909 = 1033841) (by norm_num)
theorem B3871061 : Blo 1528461 3871061 := bbase (se 10 (by rfl) ⟨5670, by rfl⟩ : syracuseStep 3871061 = 11341) (by norm_num)
theorem B5804405 : Blo 1528461 5804405 := bbase (se 5 (by rfl) ⟨272081, by rfl⟩ : syracuseStep 5804405 = 544163) (by norm_num)
theorem B2757053 : Blo 1528461 2757053 := bbase (se 3 (by rfl) ⟨516947, by rfl⟩ : syracuseStep 2757053 = 1033895) (by norm_num)
theorem B3101149 : Blo 1528461 3101149 := bbase (se 3 (by rfl) ⟨581465, by rfl⟩ : syracuseStep 3101149 = 1162931) (by norm_num)
theorem B3871253 : Blo 1528461 3871253 := bbase (se 6 (by rfl) ⟨90732, by rfl⟩ : syracuseStep 3871253 = 181465) (by norm_num)
theorem B3265157 : Blo 1528461 3265157 := bbase (se 4 (by rfl) ⟨306108, by rfl⟩ : syracuseStep 3265157 = 612217) (by norm_num)
theorem B1962641 : Blo 1528461 1962641 := bbase (se 2 (by rfl) ⟨735990, by rfl⟩ : syracuseStep 1962641 = 1471981) (by norm_num)
theorem B5804693 : Blo 1528461 5804693 := bbase (se 6 (by rfl) ⟨136047, by rfl⟩ : syracuseStep 5804693 = 272095) (by norm_num)
theorem B3674821 : Blo 1528461 3674821 := bbase (se 4 (by rfl) ⟨344514, by rfl⟩ : syracuseStep 3674821 = 689029) (by norm_num)
theorem B8712917 : Blo 1528461 8712917 := bbase (se 7 (by rfl) ⟨102104, by rfl⟩ : syracuseStep 8712917 = 204209) (by norm_num)
theorem B3871597 : Blo 1528461 3871597 := bbase (se 3 (by rfl) ⟨725924, by rfl⟩ : syracuseStep 3871597 = 1451849) (by norm_num)
theorem B2904997 : Blo 1528461 2904997 := bbase (se 4 (by rfl) ⟨272343, by rfl⟩ : syracuseStep 2904997 = 544687) (by norm_num)
theorem B3871709 : Blo 1528461 3871709 := bbase (se 3 (by rfl) ⟨725945, by rfl⟩ : syracuseStep 3871709 = 1451891) (by norm_num)
theorem B3101669 : Blo 1528461 3101669 := bbase (se 4 (by rfl) ⟨290781, by rfl⟩ : syracuseStep 3101669 = 581563) (by norm_num)
theorem B3265525 : Blo 1528461 3265525 := bbase (se 5 (by rfl) ⟨153071, by rfl⟩ : syracuseStep 3265525 = 306143) (by norm_num)
theorem B2905141 : Blo 1528461 2905141 := bbase (se 5 (by rfl) ⟨136178, by rfl⟩ : syracuseStep 2905141 = 272357) (by norm_num)
theorem B7746677 : Blo 1528461 7746677 := bbase (se 5 (by rfl) ⟨363125, by rfl⟩ : syracuseStep 7746677 = 726251) (by norm_num)
theorem B3486869 : Blo 1528461 3486869 := bbase (se 6 (by rfl) ⟨81723, by rfl⟩ : syracuseStep 3486869 = 163447) (by norm_num)
theorem B3871901 : Blo 1528461 3871901 := bbase (se 3 (by rfl) ⟨725981, by rfl⟩ : syracuseStep 3871901 = 1451963) (by norm_num)
theorem B6288581 : Blo 1528461 6288581 := bbase (se 4 (by rfl) ⟨589554, by rfl⟩ : syracuseStep 6288581 = 1179109) (by norm_num)
theorem B2905301 : Blo 1528461 2905301 := bbase (se 7 (by rfl) ⟨34046, by rfl⟩ : syracuseStep 2905301 = 68093) (by norm_num)
theorem B4355365 : Blo 1528461 4355365 := bbase (se 4 (by rfl) ⟨408315, by rfl⟩ : syracuseStep 4355365 = 816631) (by norm_num)
theorem B11621717 : Blo 1528461 11621717 := bbase (se 18 (by rfl) ⟨66, by rfl⟩ : syracuseStep 11621717 = 133) (by norm_num)
theorem B3675493 : Blo 1528461 3675493 := bbase (se 4 (by rfl) ⟨344577, by rfl⟩ : syracuseStep 3675493 = 689155) (by norm_num)
theorem B2905445 : Blo 1528461 2905445 := bbase (se 4 (by rfl) ⟨272385, by rfl⟩ : syracuseStep 2905445 = 544771) (by norm_num)
theorem B2094445 : Blo 1528461 2094445 := bbase (se 3 (by rfl) ⟨392708, by rfl⟩ : syracuseStep 2094445 = 785417) (by norm_num)
theorem B4355525 : Blo 1528461 4355525 := bbase (se 4 (by rfl) ⟨408330, by rfl⟩ : syracuseStep 4355525 = 816661) (by norm_num)
theorem B3872245 : Blo 1528461 3872245 := bbase (se 5 (by rfl) ⟨181511, by rfl⟩ : syracuseStep 3872245 = 363023) (by norm_num)
theorem B7738901 : Blo 1528461 7738901 := bbase (se 6 (by rfl) ⟨181380, by rfl⟩ : syracuseStep 7738901 = 362761) (by norm_num)
theorem B2176589 : Blo 1528461 2176589 := bbase (se 3 (by rfl) ⟨408110, by rfl⟩ : syracuseStep 2176589 = 816221) (by norm_num)
theorem B3675725 : Blo 1528461 3675725 := bbase (se 3 (by rfl) ⟨689198, by rfl⟩ : syracuseStep 3675725 = 1378397) (by norm_num)
theorem B3872357 : Blo 1528461 3872357 := bbase (se 4 (by rfl) ⟨363033, by rfl⟩ : syracuseStep 3872357 = 726067) (by norm_num)
theorem B2176669 : Blo 1528461 2176669 := bbase (se 3 (by rfl) ⟨408125, by rfl⟩ : syracuseStep 2176669 = 816251) (by norm_num)
theorem B3102365 : Blo 1528461 3102365 := bbase (se 3 (by rfl) ⟨581693, by rfl⟩ : syracuseStep 3102365 = 1163387) (by norm_num)
theorem B5158565 : Blo 1528461 5158565 := bbase (se 4 (by rfl) ⟨483615, by rfl⟩ : syracuseStep 5158565 = 967231) (by norm_num)
theorem B4355765 : Blo 1528461 4355765 := bbase (se 5 (by rfl) ⟨204176, by rfl⟩ : syracuseStep 4355765 = 408353) (by norm_num)
theorem B33052373 : Blo 1528461 33052373 := bbase (se 7 (by rfl) ⟨387332, by rfl⟩ : syracuseStep 33052373 = 774665) (by norm_num)
theorem B3675869 : Blo 1528461 3675869 := bbase (se 3 (by rfl) ⟨689225, by rfl⟩ : syracuseStep 3675869 = 1378451) (by norm_num)
theorem B11613941 : Blo 1528461 11613941 := bbase (se 5 (by rfl) ⟨544403, by rfl⟩ : syracuseStep 11613941 = 1088807) (by norm_num)
theorem B3675917 : Blo 1528461 3675917 := bbase (se 3 (by rfl) ⟨689234, by rfl⟩ : syracuseStep 3675917 = 1378469) (by norm_num)
theorem B2176789 : Blo 1528461 2176789 := bbase (se 6 (by rfl) ⟨51018, by rfl⟩ : syracuseStep 2176789 = 102037) (by norm_num)
theorem B5510933 : Blo 1528461 5510933 := bbase (se 6 (by rfl) ⟨129162, by rfl⟩ : syracuseStep 5510933 = 258325) (by norm_num)
theorem B3872549 : Blo 1528461 3872549 := bbase (se 4 (by rfl) ⟨363051, by rfl⟩ : syracuseStep 3872549 = 726103) (by norm_num)
theorem B5805877 : Blo 1528461 5805877 := bbase (se 5 (by rfl) ⟨272150, by rfl⟩ : syracuseStep 5805877 = 544301) (by norm_num)
theorem B3143477 : Blo 1528461 3143477 := bbase (se 5 (by rfl) ⟨147350, by rfl⟩ : syracuseStep 3143477 = 294701) (by norm_num)
theorem B2176885 : Blo 1528461 2176885 := bbase (se 5 (by rfl) ⟨102041, by rfl⟩ : syracuseStep 2176885 = 204083) (by norm_num)
theorem B4355957 : Blo 1528461 4355957 := bbase (se 5 (by rfl) ⟨204185, by rfl⟩ : syracuseStep 4355957 = 408371) (by norm_num)
theorem B8714101 : Blo 1528461 8714101 := bbase (se 5 (by rfl) ⟨408473, by rfl⟩ : syracuseStep 8714101 = 816947) (by norm_num)
theorem B3676205 : Blo 1528461 3676205 := bbase (se 3 (by rfl) ⟨689288, by rfl⟩ : syracuseStep 3676205 = 1378577) (by norm_num)
theorem B5158997 : Blo 1528461 5158997 := bbase (se 8 (by rfl) ⟨30228, by rfl⟩ : syracuseStep 5158997 = 60457) (by norm_num)
theorem B5806181 : Blo 1528461 5806181 := bbase (se 4 (by rfl) ⟨544329, by rfl⟩ : syracuseStep 5806181 = 1088659) (by norm_num)
theorem B3872893 : Blo 1528461 3872893 := bbase (se 3 (by rfl) ⟨726167, by rfl⟩ : syracuseStep 3872893 = 1452335) (by norm_num)
theorem B3873005 : Blo 1528461 3873005 := bbase (se 3 (by rfl) ⟨726188, by rfl⟩ : syracuseStep 3873005 = 1452377) (by norm_num)
theorem B1743193 : Blo 1528461 1743193 := bbase (se 2 (by rfl) ⟨653697, by rfl⟩ : syracuseStep 1743193 = 1307395) (by norm_num)
theorem B2177381 : Blo 1528461 2177381 := bbase (se 4 (by rfl) ⟨204129, by rfl⟩ : syracuseStep 2177381 = 408259) (by norm_num)
theorem B1743229 : Blo 1528461 1743229 := bbase (se 3 (by rfl) ⟨326855, by rfl⟩ : syracuseStep 1743229 = 653711) (by norm_num)
theorem B3873197 : Blo 1528461 3873197 := bbase (se 3 (by rfl) ⟨726224, by rfl⟩ : syracuseStep 3873197 = 1452449) (by norm_num)
theorem B3439061 : Blo 1528461 3439061 := bbase (se 7 (by rfl) ⟨40301, by rfl⟩ : syracuseStep 3439061 = 80603) (by norm_num)
theorem B3267029 : Blo 1528461 3267029 := bbase (se 7 (by rfl) ⟨38285, by rfl⟩ : syracuseStep 3267029 = 76571) (by norm_num)
theorem B3725797 : Blo 1528461 3725797 := bbase (se 4 (by rfl) ⟨349293, by rfl⟩ : syracuseStep 3725797 = 698587) (by norm_num)
theorem B5159429 : Blo 1528461 5159429 := bbase (se 4 (by rfl) ⟨483696, by rfl⟩ : syracuseStep 5159429 = 967393) (by norm_num)
theorem B5511685 : Blo 1528461 5511685 := bbase (se 4 (by rfl) ⟨516720, by rfl⟩ : syracuseStep 5511685 = 1033441) (by norm_num)
theorem B3439133 : Blo 1528461 3439133 := bbase (se 3 (by rfl) ⟨644837, by rfl⟩ : syracuseStep 3439133 = 1289675) (by norm_num)
theorem B3439205 : Blo 1528461 3439205 := bbase (se 4 (by rfl) ⟨322425, by rfl⟩ : syracuseStep 3439205 = 644851) (by norm_num)
theorem B3267173 : Blo 1528461 3267173 := bbase (se 4 (by rfl) ⟨306297, by rfl⟩ : syracuseStep 3267173 = 612595) (by norm_num)
theorem B3439277 : Blo 1528461 3439277 := bbase (se 3 (by rfl) ⟨644864, by rfl⟩ : syracuseStep 3439277 = 1289729) (by norm_num)
theorem B3439349 : Blo 1528461 3439349 := bbase (se 5 (by rfl) ⟨161219, by rfl⟩ : syracuseStep 3439349 = 322439) (by norm_num)
theorem B3873541 : Blo 1528461 3873541 := bbase (se 4 (by rfl) ⟨363144, by rfl⟩ : syracuseStep 3873541 = 726289) (by norm_num)
theorem B7740197 : Blo 1528461 7740197 := bbase (se 4 (by rfl) ⟨725643, by rfl⟩ : syracuseStep 7740197 = 1451287) (by norm_num)
theorem B3439421 : Blo 1528461 3439421 := bbase (se 3 (by rfl) ⟨644891, by rfl⟩ : syracuseStep 3439421 = 1289783) (by norm_num)
theorem B4356949 : Blo 1528461 4356949 := bbase (se 9 (by rfl) ⟨12764, by rfl⟩ : syracuseStep 4356949 = 25529) (by norm_num)
theorem B3873653 : Blo 1528461 3873653 := bbase (se 5 (by rfl) ⟨181577, by rfl⟩ : syracuseStep 3873653 = 363155) (by norm_num)
theorem B3439493 : Blo 1528461 3439493 := bbase (se 4 (by rfl) ⟨322452, by rfl⟩ : syracuseStep 3439493 = 644905) (by norm_num)
theorem B2177933 : Blo 1528461 2177933 := bbase (se 3 (by rfl) ⟨408362, by rfl⟩ : syracuseStep 2177933 = 816725) (by norm_num)
theorem B4897685 : Blo 1528461 4897685 := bbase (se 6 (by rfl) ⟨114789, by rfl⟩ : syracuseStep 4897685 = 229579) (by norm_num)
theorem B2579357 : Blo 1528461 2579357 := bbase (se 3 (by rfl) ⟨483629, by rfl⟩ : syracuseStep 2579357 = 967259) (by norm_num)
theorem B5159861 : Blo 1528461 5159861 := bbase (se 5 (by rfl) ⟨241868, by rfl⟩ : syracuseStep 5159861 = 483737) (by norm_num)
theorem B7347125 : Blo 1528461 7347125 := bbase (se 5 (by rfl) ⟨344396, by rfl⟩ : syracuseStep 7347125 = 688793) (by norm_num)
theorem B3439565 : Blo 1528461 3439565 := bbase (se 3 (by rfl) ⟨644918, by rfl⟩ : syracuseStep 3439565 = 1289837) (by norm_num)
theorem B3267533 : Blo 1528461 3267533 := bbase (se 3 (by rfl) ⟨612662, by rfl⟩ : syracuseStep 3267533 = 1225325) (by norm_num)
theorem B2292701 : Blo 1528461 2292701 := bbase (se 3 (by rfl) ⟨429881, by rfl⟩ : syracuseStep 2292701 = 859763) (by norm_num)
theorem B2292725 : Blo 1528461 2292725 := bbase (se 5 (by rfl) ⟨107471, by rfl⟩ : syracuseStep 2292725 = 214943) (by norm_num)
theorem B4135925 : Blo 1528461 4135925 := bbase (se 5 (by rfl) ⟨193871, by rfl⟩ : syracuseStep 4135925 = 387743) (by norm_num)
theorem B2292749 : Blo 1528461 2292749 := bbase (se 3 (by rfl) ⟨429890, by rfl⟩ : syracuseStep 2292749 = 859781) (by norm_num)
theorem B3439637 : Blo 1528461 3439637 := bbase (se 6 (by rfl) ⟨80616, by rfl⟩ : syracuseStep 3439637 = 161233) (by norm_num)
theorem B2579485 : Blo 1528461 2579485 := bbase (se 3 (by rfl) ⟨483653, by rfl⟩ : syracuseStep 2579485 = 967307) (by norm_num)
theorem B2292773 : Blo 1528461 2292773 := bbase (se 4 (by rfl) ⟨214947, by rfl⟩ : syracuseStep 2292773 = 429895) (by norm_num)
theorem B1743913 : Blo 1528461 1743913 := bbase (se 2 (by rfl) ⟨653967, by rfl⟩ : syracuseStep 1743913 = 1307935) (by norm_num)
theorem B3873845 : Blo 1528461 3873845 := bbase (se 5 (by rfl) ⟨181586, by rfl⟩ : syracuseStep 3873845 = 363173) (by norm_num)
theorem B2292797 : Blo 1528461 2292797 := bbase (se 3 (by rfl) ⟨429899, by rfl⟩ : syracuseStep 2292797 = 859799) (by norm_num)
theorem B2292821 : Blo 1528461 2292821 := bbase (se 8 (by rfl) ⟨13434, by rfl⟩ : syracuseStep 2292821 = 26869) (by norm_num)
theorem B3439709 : Blo 1528461 3439709 := bbase (se 3 (by rfl) ⟨644945, by rfl⟩ : syracuseStep 3439709 = 1289891) (by norm_num)
theorem B2292845 : Blo 1528461 2292845 := bbase (se 3 (by rfl) ⟨429908, by rfl⟩ : syracuseStep 2292845 = 859817) (by norm_num)
theorem B2579573 : Blo 1528461 2579573 := bbase (se 5 (by rfl) ⟨120917, by rfl⟩ : syracuseStep 2579573 = 241835) (by norm_num)
theorem B2292869 : Blo 1528461 2292869 := bbase (se 4 (by rfl) ⟨214956, by rfl⟩ : syracuseStep 2292869 = 429913) (by norm_num)
theorem B2292893 : Blo 1528461 2292893 := bbase (se 3 (by rfl) ⟨429917, by rfl⟩ : syracuseStep 2292893 = 859835) (by norm_num)
theorem B3439781 : Blo 1528461 3439781 := bbase (se 4 (by rfl) ⟨322479, by rfl⟩ : syracuseStep 3439781 = 644959) (by norm_num)
theorem B2292917 : Blo 1528461 2292917 := bbase (se 5 (by rfl) ⟨107480, by rfl⟩ : syracuseStep 2292917 = 214961) (by norm_num)
theorem B2292941 : Blo 1528461 2292941 := bbase (se 3 (by rfl) ⟨429926, by rfl⟩ : syracuseStep 2292941 = 859853) (by norm_num)
theorem B2292965 : Blo 1528461 2292965 := bbase (se 4 (by rfl) ⟨214965, by rfl⟩ : syracuseStep 2292965 = 429931) (by norm_num)
theorem B3439853 : Blo 1528461 3439853 := bbase (se 3 (by rfl) ⟨644972, by rfl⟩ : syracuseStep 3439853 = 1289945) (by norm_num)
theorem B2579701 : Blo 1528461 2579701 := bbase (se 5 (by rfl) ⟨120923, by rfl⟩ : syracuseStep 2579701 = 241847) (by norm_num)
theorem B12401909 : Blo 1528461 12401909 := bbase (se 5 (by rfl) ⟨581339, by rfl⟩ : syracuseStep 12401909 = 1162679) (by norm_num)
theorem B2292989 : Blo 1528461 2292989 := bbase (se 3 (by rfl) ⟨429935, by rfl⟩ : syracuseStep 2292989 = 859871) (by norm_num)
theorem B1719553 : Blo 1528461 1719553 := bbase (se 2 (by rfl) ⟨644832, by rfl⟩ : syracuseStep 1719553 = 1289665) (by norm_num)
theorem B2293013 : Blo 1528461 2293013 := bbase (se 6 (by rfl) ⟨53742, by rfl⟩ : syracuseStep 2293013 = 107485) (by norm_num)
theorem B1719589 : Blo 1528461 1719589 := bbase (se 4 (by rfl) ⟨161211, by rfl⟩ : syracuseStep 1719589 = 322423) (by norm_num)
theorem B2293037 : Blo 1528461 2293037 := bbase (se 3 (by rfl) ⟨429944, by rfl⟩ : syracuseStep 2293037 = 859889) (by norm_num)
theorem B3439925 : Blo 1528461 3439925 := bbase (se 5 (by rfl) ⟨161246, by rfl⟩ : syracuseStep 3439925 = 322493) (by norm_num)
theorem B2293061 : Blo 1528461 2293061 := bbase (se 4 (by rfl) ⟨214974, by rfl⟩ : syracuseStep 2293061 = 429949) (by norm_num)
theorem B1719625 : Blo 1528461 1719625 := bbase (se 2 (by rfl) ⟨644859, by rfl⟩ : syracuseStep 1719625 = 1289719) (by norm_num)
theorem B2579789 : Blo 1528461 2579789 := bbase (se 3 (by rfl) ⟨483710, by rfl⟩ : syracuseStep 2579789 = 967421) (by norm_num)
theorem B6536533 : Blo 1528461 6536533 := bbase (se 11 (by rfl) ⟨4787, by rfl⟩ : syracuseStep 6536533 = 9575) (by norm_num)
theorem B2293085 : Blo 1528461 2293085 := bbase (se 3 (by rfl) ⟨429953, by rfl⟩ : syracuseStep 2293085 = 859907) (by norm_num)
theorem B5160293 : Blo 1528461 5160293 := bbase (se 4 (by rfl) ⟨483777, by rfl⟩ : syracuseStep 5160293 = 967555) (by norm_num)
theorem B1719661 : Blo 1528461 1719661 := bbase (se 3 (by rfl) ⟨322436, by rfl⟩ : syracuseStep 1719661 = 644873) (by norm_num)
theorem B2293109 : Blo 1528461 2293109 := bbase (se 5 (by rfl) ⟨107489, by rfl⟩ : syracuseStep 2293109 = 214979) (by norm_num)
theorem B3439997 : Blo 1528461 3439997 := bbase (se 3 (by rfl) ⟨644999, by rfl⟩ : syracuseStep 3439997 = 1289999) (by norm_num)
theorem B2293133 : Blo 1528461 2293133 := bbase (se 3 (by rfl) ⟨429962, by rfl⟩ : syracuseStep 2293133 = 859925) (by norm_num)
theorem B1719697 : Blo 1528461 1719697 := bbase (se 2 (by rfl) ⟨644886, by rfl⟩ : syracuseStep 1719697 = 1289773) (by norm_num)
theorem B2293157 : Blo 1528461 2293157 := bbase (se 4 (by rfl) ⟨214983, by rfl⟩ : syracuseStep 2293157 = 429967) (by norm_num)
theorem B1719733 : Blo 1528461 1719733 := bbase (se 5 (by rfl) ⟨80612, by rfl⟩ : syracuseStep 1719733 = 161225) (by norm_num)
theorem B2293181 : Blo 1528461 2293181 := bbase (se 3 (by rfl) ⟨429971, by rfl⟩ : syracuseStep 2293181 = 859943) (by norm_num)
theorem B3440069 : Blo 1528461 3440069 := bbase (se 4 (by rfl) ⟨322506, by rfl⟩ : syracuseStep 3440069 = 645013) (by norm_num)
theorem B2579917 : Blo 1528461 2579917 := bbase (se 3 (by rfl) ⟨483734, by rfl⟩ : syracuseStep 2579917 = 967469) (by norm_num)
theorem B2293205 : Blo 1528461 2293205 := bbase (se 7 (by rfl) ⟨26873, by rfl⟩ : syracuseStep 2293205 = 53747) (by norm_num)
theorem B1719769 : Blo 1528461 1719769 := bbase (se 2 (by rfl) ⟨644913, by rfl⟩ : syracuseStep 1719769 = 1289827) (by norm_num)
theorem B2293229 : Blo 1528461 2293229 := bbase (se 3 (by rfl) ⟨429980, by rfl⟩ : syracuseStep 2293229 = 859961) (by norm_num)
theorem B5512693 : Blo 1528461 5512693 := bbase (se 5 (by rfl) ⟨258407, by rfl⟩ : syracuseStep 5512693 = 516815) (by norm_num)
theorem B1719805 : Blo 1528461 1719805 := bbase (se 3 (by rfl) ⟨322463, by rfl⟩ : syracuseStep 1719805 = 644927) (by norm_num)
theorem B2293253 : Blo 1528461 2293253 := bbase (se 4 (by rfl) ⟨214992, by rfl⟩ : syracuseStep 2293253 = 429985) (by norm_num)
theorem B3440141 : Blo 1528461 3440141 := bbase (se 3 (by rfl) ⟨645026, by rfl⟩ : syracuseStep 3440141 = 1290053) (by norm_num)
theorem B2293277 : Blo 1528461 2293277 := bbase (se 3 (by rfl) ⟨429989, by rfl⟩ : syracuseStep 2293277 = 859979) (by norm_num)
theorem B1719841 : Blo 1528461 1719841 := bbase (se 2 (by rfl) ⟨644940, by rfl⟩ : syracuseStep 1719841 = 1289881) (by norm_num)
theorem B2580005 : Blo 1528461 2580005 := bbase (se 4 (by rfl) ⟨241875, by rfl⟩ : syracuseStep 2580005 = 483751) (by norm_num)
theorem B2293301 : Blo 1528461 2293301 := bbase (se 5 (by rfl) ⟨107498, by rfl⟩ : syracuseStep 2293301 = 214997) (by norm_num)
theorem B1719877 : Blo 1528461 1719877 := bbase (se 4 (by rfl) ⟨161238, by rfl⟩ : syracuseStep 1719877 = 322477) (by norm_num)
theorem B2293325 : Blo 1528461 2293325 := bbase (se 3 (by rfl) ⟨429998, by rfl⟩ : syracuseStep 2293325 = 859997) (by norm_num)
theorem B3440213 : Blo 1528461 3440213 := bbase (se 8 (by rfl) ⟨20157, by rfl⟩ : syracuseStep 3440213 = 40315) (by norm_num)
theorem B7347797 : Blo 1528461 7347797 := bbase (se 8 (by rfl) ⟨43053, by rfl⟩ : syracuseStep 7347797 = 86107) (by norm_num)
theorem B2293349 : Blo 1528461 2293349 := bbase (se 4 (by rfl) ⟨215001, by rfl⟩ : syracuseStep 2293349 = 430003) (by norm_num)
theorem B1719913 : Blo 1528461 1719913 := bbase (se 2 (by rfl) ⟨644967, by rfl⟩ : syracuseStep 1719913 = 1289935) (by norm_num)
theorem B2293373 : Blo 1528461 2293373 := bbase (se 3 (by rfl) ⟨430007, by rfl⟩ : syracuseStep 2293373 = 860015) (by norm_num)
theorem B2178685 : Blo 1528461 2178685 := bbase (se 3 (by rfl) ⟨408503, by rfl⟩ : syracuseStep 2178685 = 817007) (by norm_num)
theorem B1719949 : Blo 1528461 1719949 := bbase (se 3 (by rfl) ⟨322490, by rfl⟩ : syracuseStep 1719949 = 644981) (by norm_num)
theorem B2293397 : Blo 1528461 2293397 := bbase (se 6 (by rfl) ⟨53751, by rfl⟩ : syracuseStep 2293397 = 107503) (by norm_num)
theorem B3440285 : Blo 1528461 3440285 := bbase (se 3 (by rfl) ⟨645053, by rfl⟩ : syracuseStep 3440285 = 1290107) (by norm_num)
theorem B2580133 : Blo 1528461 2580133 := bbase (se 4 (by rfl) ⟨241887, by rfl⟩ : syracuseStep 2580133 = 483775) (by norm_num)
theorem B2293421 : Blo 1528461 2293421 := bbase (se 3 (by rfl) ⟨430016, by rfl⟩ : syracuseStep 2293421 = 860033) (by norm_num)
theorem B1719985 : Blo 1528461 1719985 := bbase (se 2 (by rfl) ⟨644994, by rfl⟩ : syracuseStep 1719985 = 1289989) (by norm_num)
theorem B2293445 : Blo 1528461 2293445 := bbase (se 4 (by rfl) ⟨215010, by rfl⟩ : syracuseStep 2293445 = 430021) (by norm_num)
theorem B1720021 : Blo 1528461 1720021 := bbase (se 7 (by rfl) ⟨20156, by rfl⟩ : syracuseStep 1720021 = 40313) (by norm_num)
theorem B2293469 : Blo 1528461 2293469 := bbase (se 3 (by rfl) ⟨430025, by rfl⟩ : syracuseStep 2293469 = 860051) (by norm_num)
theorem B3440357 : Blo 1528461 3440357 := bbase (se 4 (by rfl) ⟨322533, by rfl⟩ : syracuseStep 3440357 = 645067) (by norm_num)
theorem B2293493 : Blo 1528461 2293493 := bbase (se 5 (by rfl) ⟨107507, by rfl⟩ : syracuseStep 2293493 = 215015) (by norm_num)
theorem B1720057 : Blo 1528461 1720057 := bbase (se 2 (by rfl) ⟨645021, by rfl⟩ : syracuseStep 1720057 = 1290043) (by norm_num)
theorem B2580221 : Blo 1528461 2580221 := bbase (se 3 (by rfl) ⟨483791, by rfl⟩ : syracuseStep 2580221 = 967583) (by norm_num)
theorem B2293517 : Blo 1528461 2293517 := bbase (se 3 (by rfl) ⟨430034, by rfl⟩ : syracuseStep 2293517 = 860069) (by norm_num)
theorem B5160725 : Blo 1528461 5160725 := bbase (se 6 (by rfl) ⟨120954, by rfl⟩ : syracuseStep 5160725 = 241909) (by norm_num)
theorem B1720093 : Blo 1528461 1720093 := bbase (se 3 (by rfl) ⟨322517, by rfl⟩ : syracuseStep 1720093 = 645035) (by norm_num)
theorem B2293541 : Blo 1528461 2293541 := bbase (se 4 (by rfl) ⟨215019, by rfl⟩ : syracuseStep 2293541 = 430039) (by norm_num)
theorem B3440429 : Blo 1528461 3440429 := bbase (se 3 (by rfl) ⟨645080, by rfl⟩ : syracuseStep 3440429 = 1290161) (by norm_num)
theorem B4415285 : Blo 1528461 4415285 := bbase (se 5 (by rfl) ⟨206966, by rfl⟩ : syracuseStep 4415285 = 413933) (by norm_num)
theorem B8716085 : Blo 1528461 8716085 := bbase (se 5 (by rfl) ⟨408566, by rfl⟩ : syracuseStep 8716085 = 817133) (by norm_num)
theorem B2293565 : Blo 1528461 2293565 := bbase (se 3 (by rfl) ⟨430043, by rfl⟩ : syracuseStep 2293565 = 860087) (by norm_num)
theorem B1720129 : Blo 1528461 1720129 := bbase (se 2 (by rfl) ⟨645048, by rfl⟩ : syracuseStep 1720129 = 1290097) (by norm_num)
theorem B3268421 : Blo 1528461 3268421 := bbase (se 4 (by rfl) ⟨306414, by rfl⟩ : syracuseStep 3268421 = 612829) (by norm_num)
theorem B2293589 : Blo 1528461 2293589 := bbase (se 9 (by rfl) ⟨6719, by rfl⟩ : syracuseStep 2293589 = 13439) (by norm_num)
theorem B1720165 : Blo 1528461 1720165 := bbase (se 4 (by rfl) ⟨161265, by rfl⟩ : syracuseStep 1720165 = 322531) (by norm_num)
theorem B2449253 : Blo 1528461 2449253 := bbase (se 4 (by rfl) ⟨229617, by rfl⟩ : syracuseStep 2449253 = 459235) (by norm_num)
theorem B2293613 : Blo 1528461 2293613 := bbase (se 3 (by rfl) ⟨430052, by rfl⟩ : syracuseStep 2293613 = 860105) (by norm_num)
theorem B3440501 : Blo 1528461 3440501 := bbase (se 5 (by rfl) ⟨161273, by rfl⟩ : syracuseStep 3440501 = 322547) (by norm_num)
theorem B2580349 : Blo 1528461 2580349 := bbase (se 3 (by rfl) ⟨483815, by rfl⟩ : syracuseStep 2580349 = 967631) (by norm_num)
theorem B2293637 : Blo 1528461 2293637 := bbase (se 4 (by rfl) ⟨215028, by rfl⟩ : syracuseStep 2293637 = 430057) (by norm_num)
theorem B1720201 : Blo 1528461 1720201 := bbase (se 2 (by rfl) ⟨645075, by rfl⟩ : syracuseStep 1720201 = 1290151) (by norm_num)
theorem B2293661 : Blo 1528461 2293661 := bbase (se 3 (by rfl) ⟨430061, by rfl⟩ : syracuseStep 2293661 = 860123) (by norm_num)
theorem B4358053 : Blo 1528461 4358053 := bbase (se 4 (by rfl) ⟨408567, by rfl⟩ : syracuseStep 4358053 = 817135) (by norm_num)
theorem B1720237 : Blo 1528461 1720237 := bbase (se 3 (by rfl) ⟨322544, by rfl⟩ : syracuseStep 1720237 = 645089) (by norm_num)
theorem B2293685 : Blo 1528461 2293685 := bbase (se 5 (by rfl) ⟨107516, by rfl⟩ : syracuseStep 2293685 = 215033) (by norm_num)
theorem B3440573 : Blo 1528461 3440573 := bbase (se 3 (by rfl) ⟨645107, by rfl⟩ : syracuseStep 3440573 = 1290215) (by norm_num)
theorem B2293709 : Blo 1528461 2293709 := bbase (se 3 (by rfl) ⟨430070, by rfl⟩ : syracuseStep 2293709 = 860141) (by norm_num)
theorem B1720273 : Blo 1528461 1720273 := bbase (se 2 (by rfl) ⟨645102, by rfl⟩ : syracuseStep 1720273 = 1290205) (by norm_num)
theorem B2580437 : Blo 1528461 2580437 := bbase (se 7 (by rfl) ⟨30239, by rfl⟩ : syracuseStep 2580437 = 60479) (by norm_num)
theorem B2449381 : Blo 1528461 2449381 := bbase (se 4 (by rfl) ⟨229629, by rfl⟩ : syracuseStep 2449381 = 459259) (by norm_num)
theorem B2293733 : Blo 1528461 2293733 := bbase (se 4 (by rfl) ⟨215037, by rfl⟩ : syracuseStep 2293733 = 430075) (by norm_num)
theorem B5447669 : Blo 1528461 5447669 := bbase (se 5 (by rfl) ⟨255359, by rfl⟩ : syracuseStep 5447669 = 510719) (by norm_num)
theorem B1720309 : Blo 1528461 1720309 := bbase (se 5 (by rfl) ⟨80639, by rfl⟩ : syracuseStep 1720309 = 161279) (by norm_num)
theorem B2293757 : Blo 1528461 2293757 := bbase (se 3 (by rfl) ⟨430079, by rfl⟩ : syracuseStep 2293757 = 860159) (by norm_num)
theorem B2293763 : Blo 1528461 2293763 := bstep (se 1 (by rfl) ⟨1720322, by rfl⟩ : syracuseStep 2293763 = 3440645) B3440645
theorem B2293793 : Blo 1528461 2293793 := bstep (se 2 (by rfl) ⟨860172, by rfl⟩ : syracuseStep 2293793 = 1720345) B1720345
theorem B7348259 : Blo 1528461 7348259 := bstep (se 1 (by rfl) ⟨5511194, by rfl⟩ : syracuseStep 7348259 = 11022389) B11022389
theorem B5160995 : Blo 1528461 5160995 := bstep (se 1 (by rfl) ⟨3870746, by rfl⟩ : syracuseStep 5160995 = 7741493) B7741493
theorem B2293811 : Blo 1528461 2293811 := bstep (se 1 (by rfl) ⟨1720358, by rfl⟩ : syracuseStep 2293811 = 3440717) B3440717
theorem B2580545 : Blo 1528461 2580545 := bstep (se 2 (by rfl) ⟨967704, by rfl⟩ : syracuseStep 2580545 = 1935409) B1935409
theorem B2293841 : Blo 1528461 2293841 := bstep (se 2 (by rfl) ⟨860190, by rfl⟩ : syracuseStep 2293841 = 1720381) B1720381
theorem B4358225 : Blo 1528461 4358225 := bstep (se 2 (by rfl) ⟨1634334, by rfl⟩ : syracuseStep 4358225 = 3268669) B3268669
theorem B2293859 : Blo 1528461 2293859 := bstep (se 1 (by rfl) ⟨1720394, by rfl⟩ : syracuseStep 2293859 = 3440789) B3440789
theorem B3440753 : Blo 1528461 3440753 := bstep (se 2 (by rfl) ⟨1290282, by rfl⟩ : syracuseStep 3440753 = 2580565) B2580565
theorem B1720435 : Blo 1528461 1720435 := bstep (se 1 (by rfl) ⟨1290326, by rfl⟩ : syracuseStep 1720435 = 2580653) B2580653
theorem B2293889 : Blo 1528461 2293889 := bstep (se 2 (by rfl) ⟨860208, by rfl⟩ : syracuseStep 2293889 = 1720417) B1720417
theorem B3440771 : Blo 1528461 3440771 := bstep (se 1 (by rfl) ⟨2580578, by rfl⟩ : syracuseStep 3440771 = 5161157) B5161157
theorem B2293907 : Blo 1528461 2293907 := bstep (se 1 (by rfl) ⟨1720430, by rfl⟩ : syracuseStep 2293907 = 3440861) B3440861
theorem B6529187 : Blo 1528461 6529187 := bstep (se 1 (by rfl) ⟨4896890, by rfl⟩ : syracuseStep 6529187 = 9793781) B9793781
theorem B2293937 : Blo 1528461 2293937 := bstep (se 2 (by rfl) ⟨860226, by rfl⟩ : syracuseStep 2293937 = 1720453) B1720453
theorem B2580673 : Blo 1528461 2580673 := bstep (se 2 (by rfl) ⟨967752, by rfl⟩ : syracuseStep 2580673 = 1935505) B1935505
theorem B2293955 : Blo 1528461 2293955 := bstep (se 1 (by rfl) ⟨1720466, by rfl⟩ : syracuseStep 2293955 = 3440933) B3440933
theorem B2293985 : Blo 1528461 2293985 := bstep (se 2 (by rfl) ⟨860244, by rfl⟩ : syracuseStep 2293985 = 1720489) B1720489
theorem B2580707 : Blo 1528461 2580707 := bstep (se 1 (by rfl) ⟨1935530, by rfl⟩ : syracuseStep 2580707 = 3871061) B3871061
theorem B2294003 : Blo 1528461 2294003 := bstep (se 1 (by rfl) ⟨1720502, by rfl⟩ : syracuseStep 2294003 = 3441005) B3441005
theorem B1720579 : Blo 1528461 1720579 := bstep (se 1 (by rfl) ⟨1290434, by rfl⟩ : syracuseStep 1720579 = 2580869) B2580869
theorem B2294033 : Blo 1528461 2294033 := bstep (se 2 (by rfl) ⟨860262, by rfl⟩ : syracuseStep 2294033 = 1720525) B1720525
theorem B2294051 : Blo 1528461 2294051 := bstep (se 1 (by rfl) ⟨1720538, by rfl⟩ : syracuseStep 2294051 = 3441077) B3441077
theorem B5161265 : Blo 1528461 5161265 := bstep (se 2 (by rfl) ⟨1935474, by rfl⟩ : syracuseStep 5161265 = 3870949) B3870949
theorem B2294081 : Blo 1528461 2294081 := bstep (se 2 (by rfl) ⟨860280, by rfl⟩ : syracuseStep 2294081 = 1720561) B1720561
theorem B2294099 : Blo 1528461 2294099 := bstep (se 1 (by rfl) ⟨1720574, by rfl⟩ : syracuseStep 2294099 = 3441149) B3441149
theorem B2580835 : Blo 1528461 2580835 := bstep (se 1 (by rfl) ⟨1935626, by rfl⟩ : syracuseStep 2580835 = 3871253) B3871253
theorem B2294129 : Blo 1528461 2294129 := bstep (se 2 (by rfl) ⟨860298, by rfl⟩ : syracuseStep 2294129 = 1720597) B1720597
theorem B2294147 : Blo 1528461 2294147 := bstep (se 1 (by rfl) ⟨1720610, by rfl⟩ : syracuseStep 2294147 = 3441221) B3441221
theorem B3441041 : Blo 1528461 3441041 := bstep (se 2 (by rfl) ⟨1290390, by rfl⟩ : syracuseStep 3441041 = 2580781) B2580781
theorem B1720723 : Blo 1528461 1720723 := bstep (se 1 (by rfl) ⟨1290542, by rfl⟩ : syracuseStep 1720723 = 2581085) B2581085
theorem B2294177 : Blo 1528461 2294177 := bstep (se 2 (by rfl) ⟨860316, by rfl⟩ : syracuseStep 2294177 = 1720633) B1720633
theorem B3441059 : Blo 1528461 3441059 := bstep (se 1 (by rfl) ⟨2580794, by rfl⟩ : syracuseStep 3441059 = 5161589) B5161589
theorem B2294195 : Blo 1528461 2294195 := bstep (se 1 (by rfl) ⟨1720646, by rfl⟩ : syracuseStep 2294195 = 3441293) B3441293
theorem B2294225 : Blo 1528461 2294225 := bstep (se 2 (by rfl) ⟨860334, by rfl⟩ : syracuseStep 2294225 = 1720669) B1720669
theorem B2294243 : Blo 1528461 2294243 := bstep (se 1 (by rfl) ⟨1720682, by rfl⟩ : syracuseStep 2294243 = 3441365) B3441365
theorem B5808611 : Blo 1528461 5808611 := bstep (se 1 (by rfl) ⟨4356458, by rfl⟩ : syracuseStep 5808611 = 8712917) B8712917
theorem B2580977 : Blo 1528461 2580977 := bstep (se 2 (by rfl) ⟨967866, by rfl⟩ : syracuseStep 2580977 = 1935733) B1935733
theorem B2294273 : Blo 1528461 2294273 := bstep (se 2 (by rfl) ⟨860352, by rfl⟩ : syracuseStep 2294273 = 1720705) B1720705
theorem B3490307 : Blo 1528461 3490307 := bstep (se 1 (by rfl) ⟨2617730, by rfl⟩ : syracuseStep 3490307 = 5235461) B5235461
theorem B16769549 : Blo 1528461 16769549 := bstep (se 3 (by rfl) ⟨3144290, by rfl⟩ : syracuseStep 16769549 = 6288581) B6288581
theorem B2294291 : Blo 1528461 2294291 := bstep (se 1 (by rfl) ⟨1720718, by rfl⟩ : syracuseStep 2294291 = 3441437) B3441437
theorem B1720867 : Blo 1528461 1720867 := bstep (se 1 (by rfl) ⟨1290650, by rfl⟩ : syracuseStep 1720867 = 2581301) B2581301
theorem B2294321 : Blo 1528461 2294321 := bstep (se 2 (by rfl) ⟨860370, by rfl⟩ : syracuseStep 2294321 = 1720741) B1720741
theorem B2294339 : Blo 1528461 2294339 := bstep (se 1 (by rfl) ⟨1720754, by rfl⟩ : syracuseStep 2294339 = 3441509) B3441509
theorem B2294369 : Blo 1528461 2294369 := bstep (se 2 (by rfl) ⟨860388, by rfl⟩ : syracuseStep 2294369 = 1720777) B1720777
theorem B13951601 : Blo 1528461 13951601 := bstep (se 2 (by rfl) ⟨5231850, by rfl⟩ : syracuseStep 13951601 = 10463701) B10463701
theorem B2581105 : Blo 1528461 2581105 := bstep (se 2 (by rfl) ⟨967914, by rfl⟩ : syracuseStep 2581105 = 1935829) B1935829
theorem B2294387 : Blo 1528461 2294387 := bstep (se 1 (by rfl) ⟨1720790, by rfl⟩ : syracuseStep 2294387 = 3441581) B3441581
theorem B2294417 : Blo 1528461 2294417 := bstep (se 2 (by rfl) ⟨860406, by rfl⟩ : syracuseStep 2294417 = 1720813) B1720813
theorem B2581139 : Blo 1528461 2581139 := bstep (se 1 (by rfl) ⟨1935854, by rfl⟩ : syracuseStep 2581139 = 3871709) B3871709
theorem B2294435 : Blo 1528461 2294435 := bstep (se 1 (by rfl) ⟨1720826, by rfl⟩ : syracuseStep 2294435 = 3441653) B3441653
theorem B7348913 : Blo 1528461 7348913 := bstep (se 2 (by rfl) ⟨2755842, by rfl⟩ : syracuseStep 7348913 = 5511685) B5511685
theorem B3441329 : Blo 1528461 3441329 := bstep (se 2 (by rfl) ⟨1290498, by rfl⟩ : syracuseStep 3441329 = 2580997) B2580997
theorem B1721011 : Blo 1528461 1721011 := bstep (se 1 (by rfl) ⟨1290758, by rfl⟩ : syracuseStep 1721011 = 2581517) B2581517
theorem B2294465 : Blo 1528461 2294465 := bstep (se 2 (by rfl) ⟨860424, by rfl⟩ : syracuseStep 2294465 = 1720849) B1720849
theorem B3441347 : Blo 1528461 3441347 := bstep (se 1 (by rfl) ⟨2581010, by rfl⟩ : syracuseStep 3441347 = 5162021) B5162021
theorem B5513933 : Blo 1528461 5513933 := bstep (se 3 (by rfl) ⟨1033862, by rfl⟩ : syracuseStep 5513933 = 2067725) B2067725
theorem B2294483 : Blo 1528461 2294483 := bstep (se 1 (by rfl) ⟨1720862, by rfl⟩ : syracuseStep 2294483 = 3441725) B3441725
theorem B2294513 : Blo 1528461 2294513 := bstep (se 2 (by rfl) ⟨860442, by rfl⟩ : syracuseStep 2294513 = 1720885) B1720885
theorem B2294531 : Blo 1528461 2294531 := bstep (se 1 (by rfl) ⟨1720898, by rfl⟩ : syracuseStep 2294531 = 3441797) B3441797
theorem B2581267 : Blo 1528461 2581267 := bstep (se 1 (by rfl) ⟨1935950, by rfl⟩ : syracuseStep 2581267 = 3871901) B3871901
theorem B2294561 : Blo 1528461 2294561 := bstep (se 2 (by rfl) ⟨860460, by rfl⟩ : syracuseStep 2294561 = 1720921) B1720921
theorem B2294579 : Blo 1528461 2294579 := bstep (se 1 (by rfl) ⟨1720934, by rfl⟩ : syracuseStep 2294579 = 3441869) B3441869
theorem B1721155 : Blo 1528461 1721155 := bstep (se 1 (by rfl) ⟨1290866, by rfl⟩ : syracuseStep 1721155 = 2581733) B2581733
theorem B5161805 : Blo 1528461 5161805 := bstep (se 3 (by rfl) ⟨967838, by rfl⟩ : syracuseStep 5161805 = 1935677) B1935677
theorem B2294609 : Blo 1528461 2294609 := bstep (se 2 (by rfl) ⟨860478, by rfl⟩ : syracuseStep 2294609 = 1720957) B1720957
theorem B2294627 : Blo 1528461 2294627 := bstep (se 1 (by rfl) ⟨1720970, by rfl⟩ : syracuseStep 2294627 = 3441941) B3441941
theorem B2294657 : Blo 1528461 2294657 := bstep (se 2 (by rfl) ⟨860496, by rfl⟩ : syracuseStep 2294657 = 1720993) B1720993
theorem B5161859 : Blo 1528461 5161859 := bstep (se 1 (by rfl) ⟨3871394, by rfl⟩ : syracuseStep 5161859 = 7742789) B7742789
theorem B2294675 : Blo 1528461 2294675 := bstep (se 1 (by rfl) ⟨1721006, by rfl⟩ : syracuseStep 2294675 = 3442013) B3442013
theorem B2581409 : Blo 1528461 2581409 := bstep (se 2 (by rfl) ⟨968028, by rfl⟩ : syracuseStep 2581409 = 1936057) B1936057
theorem B4899761 : Blo 1528461 4899761 := bstep (se 2 (by rfl) ⟨1837410, by rfl⟩ : syracuseStep 4899761 = 3674821) B3674821
theorem B2294705 : Blo 1528461 2294705 := bstep (se 2 (by rfl) ⟨860514, by rfl⟩ : syracuseStep 2294705 = 1721029) B1721029
theorem B2294723 : Blo 1528461 2294723 := bstep (se 1 (by rfl) ⟨1721042, by rfl⟩ : syracuseStep 2294723 = 3442085) B3442085
theorem B3441617 : Blo 1528461 3441617 := bstep (se 2 (by rfl) ⟨1290606, by rfl⟩ : syracuseStep 3441617 = 2581213) B2581213
theorem B1721299 : Blo 1528461 1721299 := bstep (se 1 (by rfl) ⟨1290974, by rfl⟩ : syracuseStep 1721299 = 2581949) B2581949
theorem B2294753 : Blo 1528461 2294753 := bstep (se 2 (by rfl) ⟨860532, by rfl⟩ : syracuseStep 2294753 = 1721065) B1721065
theorem B3441635 : Blo 1528461 3441635 := bstep (se 1 (by rfl) ⟨2581226, by rfl⟩ : syracuseStep 3441635 = 5162453) B5162453
theorem B2294771 : Blo 1528461 2294771 := bstep (se 1 (by rfl) ⟨1721078, by rfl⟩ : syracuseStep 2294771 = 3442157) B3442157
theorem B4965389 : Blo 1528461 4965389 := bstep (se 3 (by rfl) ⟨931010, by rfl⟩ : syracuseStep 4965389 = 1862021) B1862021
theorem B2294801 : Blo 1528461 2294801 := bstep (se 2 (by rfl) ⟨860550, by rfl⟩ : syracuseStep 2294801 = 1721101) B1721101
theorem B2581537 : Blo 1528461 2581537 := bstep (se 2 (by rfl) ⟨968076, by rfl⟩ : syracuseStep 2581537 = 1936153) B1936153
theorem B2294819 : Blo 1528461 2294819 := bstep (se 1 (by rfl) ⟨1721114, by rfl⟩ : syracuseStep 2294819 = 3442229) B3442229
theorem B2450483 : Blo 1528461 2450483 := bstep (se 1 (by rfl) ⟨1837862, by rfl⟩ : syracuseStep 2450483 = 3675725) B3675725
theorem B2294849 : Blo 1528461 2294849 := bstep (se 2 (by rfl) ⟨860568, by rfl⟩ : syracuseStep 2294849 = 1721137) B1721137
theorem B2581571 : Blo 1528461 2581571 := bstep (se 1 (by rfl) ⟨1936178, by rfl⟩ : syracuseStep 2581571 = 3872357) B3872357
theorem B2294867 : Blo 1528461 2294867 := bstep (se 1 (by rfl) ⟨1721150, by rfl⟩ : syracuseStep 2294867 = 3442301) B3442301
theorem B1721443 : Blo 1528461 1721443 := bstep (se 1 (by rfl) ⟨1291082, by rfl⟩ : syracuseStep 1721443 = 2582165) B2582165
theorem B2294897 : Blo 1528461 2294897 := bstep (se 2 (by rfl) ⟨860586, by rfl⟩ : syracuseStep 2294897 = 1721173) B1721173
theorem B5809265 : Blo 1528461 5809265 := bstep (se 2 (by rfl) ⟨2178474, by rfl⟩ : syracuseStep 5809265 = 4356949) B4356949
theorem B2294915 : Blo 1528461 2294915 := bstep (se 1 (by rfl) ⟨1721186, by rfl⟩ : syracuseStep 2294915 = 3442373) B3442373
theorem B2483345 : Blo 1528461 2483345 := bstep (se 2 (by rfl) ⟨931254, by rfl⟩ : syracuseStep 2483345 = 1862509) B1862509
theorem B5162129 : Blo 1528461 5162129 := bstep (se 2 (by rfl) ⟨1935798, by rfl⟩ : syracuseStep 5162129 = 3871597) B3871597
theorem B2450579 : Blo 1528461 2450579 := bstep (se 1 (by rfl) ⟨1837934, by rfl⟩ : syracuseStep 2450579 = 3675869) B3675869
theorem B2294945 : Blo 1528461 2294945 := bstep (se 2 (by rfl) ⟨860604, by rfl⟩ : syracuseStep 2294945 = 1721209) B1721209
theorem B7742627 : Blo 1528461 7742627 := bstep (se 1 (by rfl) ⟨5806970, by rfl⟩ : syracuseStep 7742627 = 11613941) B11613941
theorem B2450611 : Blo 1528461 2450611 := bstep (se 1 (by rfl) ⟨1837958, by rfl⟩ : syracuseStep 2450611 = 3675917) B3675917
theorem B2294963 : Blo 1528461 2294963 := bstep (se 1 (by rfl) ⟨1721222, by rfl⟩ : syracuseStep 2294963 = 3442445) B3442445
theorem B2581699 : Blo 1528461 2581699 := bstep (se 1 (by rfl) ⟨1936274, by rfl⟩ : syracuseStep 2581699 = 3872549) B3872549
theorem B2294993 : Blo 1528461 2294993 := bstep (se 2 (by rfl) ⟨860622, by rfl⟩ : syracuseStep 2294993 = 1721245) B1721245
theorem B2295011 : Blo 1528461 2295011 := bstep (se 1 (by rfl) ⟨1721258, by rfl⟩ : syracuseStep 2295011 = 3442517) B3442517
theorem B3441905 : Blo 1528461 3441905 := bstep (se 2 (by rfl) ⟨1290714, by rfl⟩ : syracuseStep 3441905 = 2581429) B2581429
theorem B1721587 : Blo 1528461 1721587 := bstep (se 1 (by rfl) ⟨1291190, by rfl⟩ : syracuseStep 1721587 = 2582381) B2582381
theorem B2295041 : Blo 1528461 2295041 := bstep (se 2 (by rfl) ⟨860640, by rfl⟩ : syracuseStep 2295041 = 1721281) B1721281
theorem B3441923 : Blo 1528461 3441923 := bstep (se 1 (by rfl) ⟨2581442, by rfl⟩ : syracuseStep 3441923 = 5162885) B5162885
theorem B2295059 : Blo 1528461 2295059 := bstep (se 1 (by rfl) ⟨1721294, by rfl⟩ : syracuseStep 2295059 = 3442589) B3442589
theorem B2295089 : Blo 1528461 2295089 := bstep (se 2 (by rfl) ⟨860658, by rfl⟩ : syracuseStep 2295089 = 1721317) B1721317
theorem B2295107 : Blo 1528461 2295107 := bstep (se 1 (by rfl) ⟨1721330, by rfl⟩ : syracuseStep 2295107 = 3442661) B3442661
theorem B2581841 : Blo 1528461 2581841 := bstep (se 2 (by rfl) ⟨968190, by rfl⟩ : syracuseStep 2581841 = 1936381) B1936381
theorem B2295137 : Blo 1528461 2295137 := bstep (se 2 (by rfl) ⟨860676, by rfl⟩ : syracuseStep 2295137 = 1721353) B1721353
theorem B2295155 : Blo 1528461 2295155 := bstep (se 1 (by rfl) ⟨1721366, by rfl⟩ : syracuseStep 2295155 = 3442733) B3442733
theorem B1721731 : Blo 1528461 1721731 := bstep (se 1 (by rfl) ⟨1291298, by rfl⟩ : syracuseStep 1721731 = 2582597) B2582597
theorem B2295185 : Blo 1528461 2295185 := bstep (se 2 (by rfl) ⟨860694, by rfl⟩ : syracuseStep 2295185 = 1721389) B1721389
theorem B2295203 : Blo 1528461 2295203 := bstep (se 1 (by rfl) ⟨1721402, by rfl⟩ : syracuseStep 2295203 = 3442805) B3442805
theorem B2295233 : Blo 1528461 2295233 := bstep (se 2 (by rfl) ⟨860712, by rfl⟩ : syracuseStep 2295233 = 1721425) B1721425
theorem B2581969 : Blo 1528461 2581969 := bstep (se 2 (by rfl) ⟨968238, by rfl⟩ : syracuseStep 2581969 = 1936477) B1936477
theorem B2295251 : Blo 1528461 2295251 := bstep (se 1 (by rfl) ⟨1721438, by rfl⟩ : syracuseStep 2295251 = 3442877) B3442877
theorem B2295281 : Blo 1528461 2295281 := bstep (se 2 (by rfl) ⟨860730, by rfl⟩ : syracuseStep 2295281 = 1721461) B1721461
theorem B2582003 : Blo 1528461 2582003 := bstep (se 1 (by rfl) ⟨1936502, by rfl⟩ : syracuseStep 2582003 = 3873005) B3873005
theorem B2295299 : Blo 1528461 2295299 := bstep (se 1 (by rfl) ⟨1721474, by rfl⟩ : syracuseStep 2295299 = 3442949) B3442949
theorem B3442193 : Blo 1528461 3442193 := bstep (se 2 (by rfl) ⟨1290822, by rfl⟩ : syracuseStep 3442193 = 2581645) B2581645
theorem B1934867 : Blo 1528461 1934867 := bstep (se 1 (by rfl) ⟨1451150, by rfl⟩ : syracuseStep 1934867 = 2902301) B2902301
theorem B2295329 : Blo 1528461 2295329 := bstep (se 2 (by rfl) ⟨860748, by rfl⟩ : syracuseStep 2295329 = 1721497) B1721497
theorem B3442211 : Blo 1528461 3442211 := bstep (se 1 (by rfl) ⟨2581658, by rfl⟩ : syracuseStep 3442211 = 5163317) B5163317
theorem B2295347 : Blo 1528461 2295347 := bstep (se 1 (by rfl) ⟨1721510, by rfl⟩ : syracuseStep 2295347 = 3443021) B3443021
theorem B2295377 : Blo 1528461 2295377 := bstep (se 2 (by rfl) ⟨860766, by rfl⟩ : syracuseStep 2295377 = 1721533) B1721533
theorem B2295395 : Blo 1528461 2295395 := bstep (se 1 (by rfl) ⟨1721546, by rfl⟩ : syracuseStep 2295395 = 3443093) B3443093
theorem B2582131 : Blo 1528461 2582131 := bstep (se 1 (by rfl) ⟨1936598, by rfl⟩ : syracuseStep 2582131 = 3873197) B3873197
theorem B2295425 : Blo 1528461 2295425 := bstep (se 2 (by rfl) ⟨860784, by rfl⟩ : syracuseStep 2295425 = 1721569) B1721569
theorem B9307781 : Blo 1528461 9307781 := bstep (se 4 (by rfl) ⟨872604, by rfl⟩ : syracuseStep 9307781 = 1745209) B1745209
theorem B2295443 : Blo 1528461 2295443 := bstep (se 1 (by rfl) ⟨1721582, by rfl⟩ : syracuseStep 2295443 = 3443165) B3443165
theorem B2066081 : Blo 1528461 2066081 := bstep (se 2 (by rfl) ⟨774780, by rfl⟩ : syracuseStep 2066081 = 1549561) B1549561
theorem B5162669 : Blo 1528461 5162669 := bstep (se 3 (by rfl) ⟨968000, by rfl⟩ : syracuseStep 5162669 = 1936001) B1936001
theorem B2295473 : Blo 1528461 2295473 := bstep (se 2 (by rfl) ⟨860802, by rfl⟩ : syracuseStep 2295473 = 1721605) B1721605
theorem B2295491 : Blo 1528461 2295491 := bstep (se 1 (by rfl) ⟨1721618, by rfl⟩ : syracuseStep 2295491 = 3443237) B3443237
theorem B2295521 : Blo 1528461 2295521 := bstep (se 2 (by rfl) ⟨860820, by rfl⟩ : syracuseStep 2295521 = 1721641) B1721641
theorem B5162723 : Blo 1528461 5162723 := bstep (se 1 (by rfl) ⟨3872042, by rfl⟩ : syracuseStep 5162723 = 7744085) B7744085
theorem B2295539 : Blo 1528461 2295539 := bstep (se 1 (by rfl) ⟨1721654, by rfl⟩ : syracuseStep 2295539 = 3443309) B3443309
theorem B2582273 : Blo 1528461 2582273 := bstep (se 2 (by rfl) ⟨968352, by rfl⟩ : syracuseStep 2582273 = 1936705) B1936705
theorem B2295569 : Blo 1528461 2295569 := bstep (se 2 (by rfl) ⟨860838, by rfl⟩ : syracuseStep 2295569 = 1721677) B1721677
theorem B2295587 : Blo 1528461 2295587 := bstep (se 1 (by rfl) ⟨1721690, by rfl⟩ : syracuseStep 2295587 = 3443381) B3443381
theorem B4900657 : Blo 1528461 4900657 := bstep (se 2 (by rfl) ⟨1837746, by rfl⟩ : syracuseStep 4900657 = 3675493) B3675493
theorem B3442481 : Blo 1528461 3442481 := bstep (se 2 (by rfl) ⟨1290930, by rfl⟩ : syracuseStep 3442481 = 2581861) B2581861
theorem B2295617 : Blo 1528461 2295617 := bstep (se 2 (by rfl) ⟨860856, by rfl⟩ : syracuseStep 2295617 = 1721713) B1721713
theorem B2754371 : Blo 1528461 2754371 := bstep (se 1 (by rfl) ⟨2065778, by rfl⟩ : syracuseStep 2754371 = 4131557) B4131557
theorem B3442499 : Blo 1528461 3442499 := bstep (se 1 (by rfl) ⟨2581874, by rfl⟩ : syracuseStep 3442499 = 5163749) B5163749
theorem B2295635 : Blo 1528461 2295635 := bstep (se 1 (by rfl) ⟨1721726, by rfl⟩ : syracuseStep 2295635 = 3443453) B3443453
theorem B6621041 : Blo 1528461 6621041 := bstep (se 2 (by rfl) ⟨2482890, by rfl⟩ : syracuseStep 6621041 = 4965781) B4965781
theorem B8710001 : Blo 1528461 8710001 := bstep (se 2 (by rfl) ⟨3266250, by rfl⟩ : syracuseStep 8710001 = 6532501) B6532501
theorem B2295665 : Blo 1528461 2295665 := bstep (se 2 (by rfl) ⟨860874, by rfl⟩ : syracuseStep 2295665 = 1721749) B1721749
theorem B2582401 : Blo 1528461 2582401 := bstep (se 2 (by rfl) ⟨968400, by rfl⟩ : syracuseStep 2582401 = 1936801) B1936801
theorem B2295683 : Blo 1528461 2295683 := bstep (se 1 (by rfl) ⟨1721762, by rfl⟩ : syracuseStep 2295683 = 3443525) B3443525
theorem B2582435 : Blo 1528461 2582435 := bstep (se 1 (by rfl) ⟨1936826, by rfl⟩ : syracuseStep 2582435 = 3873653) B3873653
theorem B11610053 : Blo 1528461 11610053 := bstep (se 4 (by rfl) ⟨1088442, by rfl⟩ : syracuseStep 11610053 = 2176885) B2176885
theorem B7743437 : Blo 1528461 7743437 := bstep (se 3 (by rfl) ⟨1451894, by rfl⟩ : syracuseStep 7743437 = 2903789) B2903789
theorem B6375395 : Blo 1528461 6375395 := bstep (se 1 (by rfl) ⟨4781546, by rfl⟩ : syracuseStep 6375395 = 9563093) B9563093
theorem B7350257 : Blo 1528461 7350257 := bstep (se 2 (by rfl) ⟨2756346, by rfl⟩ : syracuseStep 7350257 = 5512693) B5512693
theorem B5162993 : Blo 1528461 5162993 := bstep (se 2 (by rfl) ⟨1936122, by rfl⟩ : syracuseStep 5162993 = 3872245) B3872245
theorem B2754595 : Blo 1528461 2754595 := bstep (se 1 (by rfl) ⟨2065946, by rfl⟩ : syracuseStep 2754595 = 4131893) B4131893
theorem B2582563 : Blo 1528461 2582563 := bstep (se 1 (by rfl) ⟨1936922, by rfl⟩ : syracuseStep 2582563 = 3873845) B3873845
theorem B2615377 : Blo 1528461 2615377 := bstep (se 2 (by rfl) ⟨980766, by rfl⟩ : syracuseStep 2615377 = 1961533) B1961533
theorem B3442769 : Blo 1528461 3442769 := bstep (se 2 (by rfl) ⟨1291038, by rfl⟩ : syracuseStep 3442769 = 2582077) B2582077
theorem B3442787 : Blo 1528461 3442787 := bstep (se 1 (by rfl) ⟨2582090, by rfl⟩ : syracuseStep 3442787 = 5164181) B5164181
theorem B8267939 : Blo 1528461 8267939 := bstep (se 1 (by rfl) ⟨6200954, by rfl⟩ : syracuseStep 8267939 = 12401909) B12401909
theorem B5884109 : Blo 1528461 5884109 := bstep (se 3 (by rfl) ⟨1103270, by rfl⟩ : syracuseStep 5884109 = 2206541) B2206541
theorem B2902225 : Blo 1528461 2902225 := bstep (se 2 (by rfl) ⟨1088334, by rfl⟩ : syracuseStep 2902225 = 2176669) B2176669
theorem B1935571 : Blo 1528461 1935571 := bstep (se 1 (by rfl) ⟨1451678, by rfl⟩ : syracuseStep 1935571 = 2903357) B2903357
theorem B1935667 : Blo 1528461 1935667 := bstep (se 1 (by rfl) ⟨1451750, by rfl⟩ : syracuseStep 1935667 = 2903501) B2903501
theorem B2902385 : Blo 1528461 2902385 := bstep (se 2 (by rfl) ⟨1088394, by rfl⟩ : syracuseStep 2902385 = 2176789) B2176789
theorem B3443057 : Blo 1528461 3443057 := bstep (se 2 (by rfl) ⟨1291146, by rfl⟩ : syracuseStep 3443057 = 2582293) B2582293
theorem B3443075 : Blo 1528461 3443075 := bstep (se 1 (by rfl) ⟨2582306, by rfl⟩ : syracuseStep 3443075 = 5164613) B5164613
theorem B3672515 : Blo 1528461 3672515 := bstep (se 1 (by rfl) ⟨2754386, by rfl⟩ : syracuseStep 3672515 = 5508773) B5508773
theorem B11618801 : Blo 1528461 11618801 := bstep (se 2 (by rfl) ⟨4357050, by rfl⟩ : syracuseStep 11618801 = 8714101) B8714101
theorem B5163533 : Blo 1528461 5163533 := bstep (se 3 (by rfl) ⟨968162, by rfl⟩ : syracuseStep 5163533 = 1936325) B1936325
theorem B3672611 : Blo 1528461 3672611 := bstep (se 1 (by rfl) ⟨2754458, by rfl⟩ : syracuseStep 3672611 = 5508917) B5508917
theorem B2943523 : Blo 1528461 2943523 := bstep (se 1 (by rfl) ⟨2207642, by rfl⟩ : syracuseStep 2943523 = 4415285) B4415285
theorem B5810723 : Blo 1528461 5810723 := bstep (se 1 (by rfl) ⟨4358042, by rfl⟩ : syracuseStep 5810723 = 8716085) B8716085
theorem B5810737 : Blo 1528461 5810737 := bstep (se 2 (by rfl) ⟨2179026, by rfl⟩ : syracuseStep 5810737 = 4358053) B4358053
theorem B1632835 : Blo 1528461 1632835 := bstep (se 1 (by rfl) ⟨1224626, by rfl⟩ : syracuseStep 1632835 = 2449253) B2449253
theorem B5163587 : Blo 1528461 5163587 := bstep (se 1 (by rfl) ⟨3872690, by rfl⟩ : syracuseStep 5163587 = 7745381) B7745381
theorem B14527117 : Blo 1528461 14527117 := bstep (se 3 (by rfl) ⟨2723834, by rfl⟩ : syracuseStep 14527117 = 5447669) B5447669
theorem B3869329 : Blo 1528461 3869329 := bstep (se 2 (by rfl) ⟨1450998, by rfl⟩ : syracuseStep 3869329 = 2901997) B2901997
theorem B3443345 : Blo 1528461 3443345 := bstep (se 2 (by rfl) ⟨1291254, by rfl⟩ : syracuseStep 3443345 = 2582509) B2582509
theorem B3443363 : Blo 1528461 3443363 := bstep (se 1 (by rfl) ⟨2582522, by rfl⟩ : syracuseStep 3443363 = 5165045) B5165045
theorem B7269041 : Blo 1528461 7269041 := bstep (se 2 (by rfl) ⟨2725890, by rfl⟩ : syracuseStep 7269041 = 5451781) B5451781
theorem B3672803 : Blo 1528461 3672803 := bstep (se 1 (by rfl) ⟨2754602, by rfl⟩ : syracuseStep 3672803 = 5509205) B5509205
theorem B2902787 : Blo 1528461 2902787 := bstep (se 1 (by rfl) ⟨2177090, by rfl⟩ : syracuseStep 2902787 = 4354181) B4354181
theorem B1936163 : Blo 1528461 1936163 := bstep (se 1 (by rfl) ⟨1452122, by rfl⟩ : syracuseStep 1936163 = 2904245) B2904245
theorem B4352849 : Blo 1528461 4352849 := bstep (se 2 (by rfl) ⟨1632318, by rfl⟩ : syracuseStep 4352849 = 3264637) B3264637
theorem B5163857 : Blo 1528461 5163857 := bstep (se 2 (by rfl) ⟨1936446, by rfl⟩ : syracuseStep 5163857 = 3872893) B3872893
theorem B1837939 : Blo 1528461 1837939 := bstep (se 1 (by rfl) ⟨1378454, by rfl⟩ : syracuseStep 1837939 = 2756909) B2756909
theorem B3025795 : Blo 1528461 3025795 := bstep (se 1 (by rfl) ⟨2269346, by rfl⟩ : syracuseStep 3025795 = 4538693) B4538693
theorem B7351181 : Blo 1528461 7351181 := bstep (se 3 (by rfl) ⟨1378346, by rfl⟩ : syracuseStep 7351181 = 2756693) B2756693
theorem B3869603 : Blo 1528461 3869603 := bstep (se 1 (by rfl) ⟨2902202, by rfl⟩ : syracuseStep 3869603 = 5804405) B5804405
theorem B1838035 : Blo 1528461 1838035 := bstep (se 1 (by rfl) ⟨1378526, by rfl⟩ : syracuseStep 1838035 = 2757053) B2757053
theorem B4353041 : Blo 1528461 4353041 := bstep (se 2 (by rfl) ⟨1632390, by rfl⟩ : syracuseStep 4353041 = 3264781) B3264781
theorem B3869795 : Blo 1528461 3869795 := bstep (se 1 (by rfl) ⟨2902346, by rfl⟩ : syracuseStep 3869795 = 5804693) B5804693
theorem B4648099 : Blo 1528461 4648099 := bstep (se 1 (by rfl) ⟨3486074, by rfl⟩ : syracuseStep 4648099 = 6972149) B6972149
theorem B8711459 : Blo 1528461 8711459 := bstep (se 1 (by rfl) ⟨6533594, by rfl⟩ : syracuseStep 8711459 = 13067189) B13067189
theorem B4967729 : Blo 1528461 4967729 := bstep (se 2 (by rfl) ⟨1862898, by rfl⟩ : syracuseStep 4967729 = 3725797) B3725797
theorem B2067779 : Blo 1528461 2067779 := bstep (se 1 (by rfl) ⟨1550834, by rfl⟩ : syracuseStep 2067779 = 3101669) B3101669
theorem B4902221 : Blo 1528461 4902221 := bstep (se 3 (by rfl) ⟨919166, by rfl⟩ : syracuseStep 4902221 = 1838333) B1838333
theorem B5164397 : Blo 1528461 5164397 := bstep (se 3 (by rfl) ⟨968324, by rfl⟩ : syracuseStep 5164397 = 1936649) B1936649
theorem B3673457 : Blo 1528461 3673457 := bstep (se 2 (by rfl) ⟨1377546, by rfl⟩ : syracuseStep 3673457 = 2755093) B2755093
theorem B5164451 : Blo 1528461 5164451 := bstep (se 1 (by rfl) ⟨3873338, by rfl⟩ : syracuseStep 5164451 = 7746677) B7746677
theorem B1936867 : Blo 1528461 1936867 := bstep (se 1 (by rfl) ⟨1452650, by rfl⟩ : syracuseStep 1936867 = 2905301) B2905301
theorem B1936963 : Blo 1528461 1936963 := bstep (se 1 (by rfl) ⟨1452722, by rfl⟩ : syracuseStep 1936963 = 2905445) B2905445
theorem B2903683 : Blo 1528461 2903683 := bstep (se 1 (by rfl) ⟨2177762, by rfl⟩ : syracuseStep 2903683 = 4355525) B4355525
theorem B3673745 : Blo 1528461 3673745 := bstep (se 2 (by rfl) ⟨1377654, by rfl⟩ : syracuseStep 3673745 = 2755309) B2755309
theorem B5164721 : Blo 1528461 5164721 := bstep (se 2 (by rfl) ⟨1936770, by rfl⟩ : syracuseStep 5164721 = 3873541) B3873541
theorem B2903843 : Blo 1528461 2903843 := bstep (se 1 (by rfl) ⟨2177882, by rfl⟩ : syracuseStep 2903843 = 4355765) B4355765
theorem B1634099 : Blo 1528461 1634099 := bstep (se 1 (by rfl) ⟨1225574, by rfl⟩ : syracuseStep 1634099 = 2451149) B2451149
theorem B3673955 : Blo 1528461 3673955 := bstep (se 1 (by rfl) ⟨2755466, by rfl⟩ : syracuseStep 3673955 = 5510933) B5510933
theorem B4354033 : Blo 1528461 4354033 := bstep (se 2 (by rfl) ⟨1632762, by rfl⟩ : syracuseStep 4354033 = 3265525) B3265525
theorem B3870737 : Blo 1528461 3870737 := bstep (se 2 (by rfl) ⟨1451526, by rfl⟩ : syracuseStep 3870737 = 2903053) B2903053
theorem B3870787 : Blo 1528461 3870787 := bstep (se 1 (by rfl) ⟨2903090, by rfl⟩ : syracuseStep 3870787 = 5806181) B5806181
theorem B5804237 : Blo 1528461 5804237 := bstep (se 3 (by rfl) ⟨1088294, by rfl⟩ : syracuseStep 5804237 = 2176589) B2176589
theorem B5165261 : Blo 1528461 5165261 := bstep (se 3 (by rfl) ⟨968486, by rfl⟩ : syracuseStep 5165261 = 1936973) B1936973
theorem B3870929 : Blo 1528461 3870929 := bstep (se 2 (by rfl) ⟨1451598, by rfl⟩ : syracuseStep 3870929 = 2903197) B2903197
theorem B4354307 : Blo 1528461 4354307 := bstep (se 1 (by rfl) ⟨3265730, by rfl⟩ : syracuseStep 4354307 = 6531461) B6531461
theorem B6533389 : Blo 1528461 6533389 := bstep (se 3 (by rfl) ⟨1225010, by rfl⟩ : syracuseStep 6533389 = 2450021) B2450021
theorem B8712461 : Blo 1528461 8712461 := bstep (se 3 (by rfl) ⟨1633586, by rfl⟩ : syracuseStep 8712461 = 3267173) B3267173
theorem B13070605 : Blo 1528461 13070605 := bstep (se 3 (by rfl) ⟨2450738, by rfl⟩ : syracuseStep 13070605 = 4901477) B4901477
theorem B4354499 : Blo 1528461 4354499 := bstep (se 1 (by rfl) ⟨3265874, by rfl⟩ : syracuseStep 4354499 = 6531749) B6531749
theorem B3265123 : Blo 1528461 3265123 := bstep (se 1 (by rfl) ⟨2448842, by rfl⟩ : syracuseStep 3265123 = 4897685) B4897685
theorem B1528467 : Blo 1528461 1528467 := bstep (se 1 (by rfl) ⟨1146350, by rfl⟩ : syracuseStep 1528467 = 2292701) B2292701
theorem B1528483 : Blo 1528461 1528483 := bstep (se 1 (by rfl) ⟨1146362, by rfl⟩ : syracuseStep 1528483 = 2292725) B2292725
theorem B6976163 : Blo 1528461 6976163 := bstep (se 1 (by rfl) ⟨5232122, by rfl⟩ : syracuseStep 6976163 = 10464245) B10464245
theorem B2757283 : Blo 1528461 2757283 := bstep (se 1 (by rfl) ⟨2067962, by rfl⟩ : syracuseStep 2757283 = 4135925) B4135925
theorem B1528499 : Blo 1528461 1528499 := bstep (se 1 (by rfl) ⟨1146374, by rfl⟩ : syracuseStep 1528499 = 2292749) B2292749
theorem B1528515 : Blo 1528461 1528515 := bstep (se 1 (by rfl) ⟨1146386, by rfl⟩ : syracuseStep 1528515 = 2292773) B2292773
theorem B3977923 : Blo 1528461 3977923 := bstep (se 1 (by rfl) ⟨2983442, by rfl⟩ : syracuseStep 3977923 = 5966885) B5966885
theorem B1528531 : Blo 1528461 1528531 := bstep (se 1 (by rfl) ⟨1146398, by rfl⟩ : syracuseStep 1528531 = 2292797) B2292797
theorem B1528547 : Blo 1528461 1528547 := bstep (se 1 (by rfl) ⟨1146410, by rfl⟩ : syracuseStep 1528547 = 2292821) B2292821
theorem B1528563 : Blo 1528461 1528563 := bstep (se 1 (by rfl) ⟨1146422, by rfl⟩ : syracuseStep 1528563 = 2292845) B2292845
theorem B1528579 : Blo 1528461 1528579 := bstep (se 1 (by rfl) ⟨1146434, by rfl⟩ : syracuseStep 1528579 = 2292869) B2292869
theorem B1528595 : Blo 1528461 1528595 := bstep (se 1 (by rfl) ⟨1146446, by rfl⟩ : syracuseStep 1528595 = 2292893) B2292893
theorem B39195413 : Blo 1528461 39195413 := bstep (se 6 (by rfl) ⟨918642, by rfl⟩ : syracuseStep 39195413 = 1837285) B1837285
theorem B1528611 : Blo 1528461 1528611 := bstep (se 1 (by rfl) ⟨1146458, by rfl⟩ : syracuseStep 1528611 = 2292917) B2292917
theorem B7746353 : Blo 1528461 7746353 := bstep (se 2 (by rfl) ⟨2904882, by rfl⟩ : syracuseStep 7746353 = 5809765) B5809765
theorem B1528627 : Blo 1528461 1528627 := bstep (se 1 (by rfl) ⟨1146470, by rfl⟩ : syracuseStep 1528627 = 2292941) B2292941
theorem B1528643 : Blo 1528461 1528643 := bstep (se 1 (by rfl) ⟨1146482, by rfl⟩ : syracuseStep 1528643 = 2292965) B2292965
theorem B2904913 : Blo 1528461 2904913 := bstep (se 2 (by rfl) ⟨1089342, by rfl⟩ : syracuseStep 2904913 = 2178685) B2178685
theorem B1528659 : Blo 1528461 1528659 := bstep (se 1 (by rfl) ⟨1146494, by rfl⟩ : syracuseStep 1528659 = 2292989) B2292989
theorem B1528675 : Blo 1528461 1528675 := bstep (se 1 (by rfl) ⟨1146506, by rfl⟩ : syracuseStep 1528675 = 2293013) B2293013
theorem B1528691 : Blo 1528461 1528691 := bstep (se 1 (by rfl) ⟨1146518, by rfl⟩ : syracuseStep 1528691 = 2293037) B2293037
theorem B1528707 : Blo 1528461 1528707 := bstep (se 1 (by rfl) ⟨1146530, by rfl⟩ : syracuseStep 1528707 = 2293061) B2293061
theorem B7738253 : Blo 1528461 7738253 := bstep (se 3 (by rfl) ⟨1450922, by rfl⟩ : syracuseStep 7738253 = 2901845) B2901845
theorem B62813069 : Blo 1528461 62813069 := bstep (se 3 (by rfl) ⟨11777450, by rfl⟩ : syracuseStep 62813069 = 23554901) B23554901
theorem B1528723 : Blo 1528461 1528723 := bstep (se 1 (by rfl) ⟨1146542, by rfl⟩ : syracuseStep 1528723 = 2293085) B2293085
theorem B1528739 : Blo 1528461 1528739 := bstep (se 1 (by rfl) ⟨1146554, by rfl⟩ : syracuseStep 1528739 = 2293109) B2293109
theorem B1528755 : Blo 1528461 1528755 := bstep (se 1 (by rfl) ⟨1146566, by rfl⟩ : syracuseStep 1528755 = 2293133) B2293133
theorem B1528771 : Blo 1528461 1528771 := bstep (se 1 (by rfl) ⟨1146578, by rfl⟩ : syracuseStep 1528771 = 2293157) B2293157
theorem B1528787 : Blo 1528461 1528787 := bstep (se 1 (by rfl) ⟨1146590, by rfl⟩ : syracuseStep 1528787 = 2293181) B2293181
theorem B1528803 : Blo 1528461 1528803 := bstep (se 1 (by rfl) ⟨1146602, by rfl⟩ : syracuseStep 1528803 = 2293205) B2293205
theorem B1528819 : Blo 1528461 1528819 := bstep (se 1 (by rfl) ⟨1146614, by rfl⟩ : syracuseStep 1528819 = 2293229) B2293229
theorem B1528835 : Blo 1528461 1528835 := bstep (se 1 (by rfl) ⟨1146626, by rfl⟩ : syracuseStep 1528835 = 2293253) B2293253
theorem B5231629 : Blo 1528461 5231629 := bstep (se 3 (by rfl) ⟨980930, by rfl⟩ : syracuseStep 5231629 = 1961861) B1961861
theorem B1528851 : Blo 1528461 1528851 := bstep (se 1 (by rfl) ⟨1146638, by rfl⟩ : syracuseStep 1528851 = 2293277) B2293277
theorem B1528867 : Blo 1528461 1528867 := bstep (se 1 (by rfl) ⟨1146650, by rfl⟩ : syracuseStep 1528867 = 2293301) B2293301
theorem B1528883 : Blo 1528461 1528883 := bstep (se 1 (by rfl) ⟨1146662, by rfl⟩ : syracuseStep 1528883 = 2293325) B2293325
theorem B1528899 : Blo 1528461 1528899 := bstep (se 1 (by rfl) ⟨1146674, by rfl⟩ : syracuseStep 1528899 = 2293349) B2293349
theorem B1528915 : Blo 1528461 1528915 := bstep (se 1 (by rfl) ⟨1146686, by rfl⟩ : syracuseStep 1528915 = 2293373) B2293373
theorem B1528931 : Blo 1528461 1528931 := bstep (se 1 (by rfl) ⟨1146698, by rfl⟩ : syracuseStep 1528931 = 2293397) B2293397
theorem B1528947 : Blo 1528461 1528947 := bstep (se 1 (by rfl) ⟨1146710, by rfl⟩ : syracuseStep 1528947 = 2293421) B2293421
theorem B1528963 : Blo 1528461 1528963 := bstep (se 1 (by rfl) ⟨1146722, by rfl⟩ : syracuseStep 1528963 = 2293445) B2293445
theorem B1528979 : Blo 1528461 1528979 := bstep (se 1 (by rfl) ⟨1146734, by rfl⟩ : syracuseStep 1528979 = 2293469) B2293469
theorem B1528995 : Blo 1528461 1528995 := bstep (se 1 (by rfl) ⟨1146746, by rfl⟩ : syracuseStep 1528995 = 2293493) B2293493
theorem B3871921 : Blo 1528461 3871921 := bstep (se 2 (by rfl) ⟨1451970, by rfl⟩ : syracuseStep 3871921 = 2903941) B2903941
theorem B1529011 : Blo 1528461 1529011 := bstep (se 1 (by rfl) ⟨1146758, by rfl⟩ : syracuseStep 1529011 = 2293517) B2293517
theorem B1529027 : Blo 1528461 1529027 := bstep (se 1 (by rfl) ⟨1146770, by rfl⟩ : syracuseStep 1529027 = 2293541) B2293541
theorem B1529043 : Blo 1528461 1529043 := bstep (se 1 (by rfl) ⟨1146782, by rfl⟩ : syracuseStep 1529043 = 2293565) B2293565
theorem B1529059 : Blo 1528461 1529059 := bstep (se 1 (by rfl) ⟨1146794, by rfl⟩ : syracuseStep 1529059 = 2293589) B2293589
theorem B4355309 : Blo 1528461 4355309 := bstep (se 3 (by rfl) ⟨816620, by rfl⟩ : syracuseStep 4355309 = 1633241) B1633241
theorem B1529075 : Blo 1528461 1529075 := bstep (se 1 (by rfl) ⟨1146806, by rfl⟩ : syracuseStep 1529075 = 2293613) B2293613
theorem B1529091 : Blo 1528461 1529091 := bstep (se 1 (by rfl) ⟨1146818, by rfl⟩ : syracuseStep 1529091 = 2293637) B2293637
theorem B1529107 : Blo 1528461 1529107 := bstep (se 1 (by rfl) ⟨1146830, by rfl⟩ : syracuseStep 1529107 = 2293661) B2293661
theorem B1529123 : Blo 1528461 1529123 := bstep (se 1 (by rfl) ⟨1146842, by rfl⟩ : syracuseStep 1529123 = 2293685) B2293685
theorem B3265841 : Blo 1528461 3265841 := bstep (se 2 (by rfl) ⟨1224690, by rfl⟩ : syracuseStep 3265841 = 2449381) B2449381
theorem B1529139 : Blo 1528461 1529139 := bstep (se 1 (by rfl) ⟨1146854, by rfl⟩ : syracuseStep 1529139 = 2293709) B2293709
theorem B3487043 : Blo 1528461 3487043 := bstep (se 1 (by rfl) ⟨2615282, by rfl⟩ : syracuseStep 3487043 = 5230565) B5230565
theorem B1529155 : Blo 1528461 1529155 := bstep (se 1 (by rfl) ⟨1146866, by rfl⟩ : syracuseStep 1529155 = 2293733) B2293733
theorem B1529171 : Blo 1528461 1529171 := bstep (se 1 (by rfl) ⟨1146878, by rfl⟩ : syracuseStep 1529171 = 2293757) B2293757
theorem B1529187 : Blo 1528461 1529187 := bstep (se 1 (by rfl) ⟨1146890, by rfl⟩ : syracuseStep 1529187 = 2293781) B2293781
theorem B1529203 : Blo 1528461 1529203 := bstep (se 1 (by rfl) ⟨1146902, by rfl⟩ : syracuseStep 1529203 = 2293805) B2293805
theorem B1529219 : Blo 1528461 1529219 := bstep (se 1 (by rfl) ⟨1146914, by rfl⟩ : syracuseStep 1529219 = 2293829) B2293829
theorem B1529235 : Blo 1528461 1529235 := bstep (se 1 (by rfl) ⟨1146926, by rfl⟩ : syracuseStep 1529235 = 2293853) B2293853
theorem B1529251 : Blo 1528461 1529251 := bstep (se 1 (by rfl) ⟨1146938, by rfl⟩ : syracuseStep 1529251 = 2293877) B2293877
theorem B4355491 : Blo 1528461 4355491 := bstep (se 1 (by rfl) ⟨3266618, by rfl⟩ : syracuseStep 4355491 = 6533237) B6533237
theorem B1529267 : Blo 1528461 1529267 := bstep (se 1 (by rfl) ⟨1146950, by rfl⟩ : syracuseStep 1529267 = 2293901) B2293901
theorem B1529283 : Blo 1528461 1529283 := bstep (se 1 (by rfl) ⟨1146962, by rfl⟩ : syracuseStep 1529283 = 2293925) B2293925
theorem B3872195 : Blo 1528461 3872195 := bstep (se 1 (by rfl) ⟨2904146, by rfl⟩ : syracuseStep 3872195 = 5808293) B5808293
theorem B9803213 : Blo 1528461 9803213 := bstep (se 3 (by rfl) ⟨1838102, by rfl⟩ : syracuseStep 9803213 = 3676205) B3676205
theorem B1529299 : Blo 1528461 1529299 := bstep (se 1 (by rfl) ⟨1146974, by rfl⟩ : syracuseStep 1529299 = 2293949) B2293949
theorem B1529315 : Blo 1528461 1529315 := bstep (se 1 (by rfl) ⟨1146986, by rfl⟩ : syracuseStep 1529315 = 2293973) B2293973
theorem B1529331 : Blo 1528461 1529331 := bstep (se 1 (by rfl) ⟨1146998, by rfl⟩ : syracuseStep 1529331 = 2293997) B2293997
theorem B1529347 : Blo 1528461 1529347 := bstep (se 1 (by rfl) ⟨1147010, by rfl⟩ : syracuseStep 1529347 = 2294021) B2294021
theorem B1529363 : Blo 1528461 1529363 := bstep (se 1 (by rfl) ⟨1147022, by rfl⟩ : syracuseStep 1529363 = 2294045) B2294045
theorem B10458659 : Blo 1528461 10458659 := bstep (se 1 (by rfl) ⟨7843994, by rfl⟩ : syracuseStep 10458659 = 15687989) B15687989
theorem B1529379 : Blo 1528461 1529379 := bstep (se 1 (by rfl) ⟨1147034, by rfl⟩ : syracuseStep 1529379 = 2294069) B2294069
theorem B2176561 : Blo 1528461 2176561 := bstep (se 2 (by rfl) ⟨816210, by rfl⟩ : syracuseStep 2176561 = 1632421) B1632421
theorem B1529395 : Blo 1528461 1529395 := bstep (se 1 (by rfl) ⟨1147046, by rfl⟩ : syracuseStep 1529395 = 2294093) B2294093
theorem B1529411 : Blo 1528461 1529411 := bstep (se 1 (by rfl) ⟨1147058, by rfl⟩ : syracuseStep 1529411 = 2294117) B2294117
theorem B13071941 : Blo 1528461 13071941 := bstep (se 4 (by rfl) ⟨1225494, by rfl⟩ : syracuseStep 13071941 = 2450989) B2450989
theorem B1529427 : Blo 1528461 1529427 := bstep (se 1 (by rfl) ⟨1147070, by rfl⟩ : syracuseStep 1529427 = 2294141) B2294141
theorem B1529443 : Blo 1528461 1529443 := bstep (se 1 (by rfl) ⟨1147082, by rfl⟩ : syracuseStep 1529443 = 2294165) B2294165
theorem B1529459 : Blo 1528461 1529459 := bstep (se 1 (by rfl) ⟨1147094, by rfl⟩ : syracuseStep 1529459 = 2294189) B2294189
theorem B1529475 : Blo 1528461 1529475 := bstep (se 1 (by rfl) ⟨1147106, by rfl⟩ : syracuseStep 1529475 = 2294213) B2294213
theorem B3872387 : Blo 1528461 3872387 := bstep (se 1 (by rfl) ⟨2904290, by rfl⟩ : syracuseStep 3872387 = 5808581) B5808581
theorem B3675793 : Blo 1528461 3675793 := bstep (se 2 (by rfl) ⟨1378422, by rfl⟩ : syracuseStep 3675793 = 2756845) B2756845
theorem B1529491 : Blo 1528461 1529491 := bstep (se 1 (by rfl) ⟨1147118, by rfl⟩ : syracuseStep 1529491 = 2294237) B2294237
theorem B1529507 : Blo 1528461 1529507 := bstep (se 1 (by rfl) ⟨1147130, by rfl⟩ : syracuseStep 1529507 = 2294261) B2294261
theorem B1529523 : Blo 1528461 1529523 := bstep (se 1 (by rfl) ⟨1147142, by rfl⟩ : syracuseStep 1529523 = 2294285) B2294285
theorem B1529539 : Blo 1528461 1529539 := bstep (se 1 (by rfl) ⟨1147154, by rfl⟩ : syracuseStep 1529539 = 2294309) B2294309
theorem B1529555 : Blo 1528461 1529555 := bstep (se 1 (by rfl) ⟨1147166, by rfl⟩ : syracuseStep 1529555 = 2294333) B2294333
theorem B1529571 : Blo 1528461 1529571 := bstep (se 1 (by rfl) ⟨1147178, by rfl⟩ : syracuseStep 1529571 = 2294357) B2294357
theorem B1529587 : Blo 1528461 1529587 := bstep (se 1 (by rfl) ⟨1147190, by rfl⟩ : syracuseStep 1529587 = 2294381) B2294381
theorem B1529603 : Blo 1528461 1529603 := bstep (se 1 (by rfl) ⟨1147202, by rfl⟩ : syracuseStep 1529603 = 2294405) B2294405
theorem B5158673 : Blo 1528461 5158673 := bstep (se 2 (by rfl) ⟨1934502, by rfl⟩ : syracuseStep 5158673 = 3869005) B3869005
theorem B1529619 : Blo 1528461 1529619 := bstep (se 1 (by rfl) ⟨1147214, by rfl⟩ : syracuseStep 1529619 = 2294429) B2294429
theorem B2324257 : Blo 1528461 2324257 := bstep (se 2 (by rfl) ⟨871596, by rfl⟩ : syracuseStep 2324257 = 1743193) B1743193
theorem B1529635 : Blo 1528461 1529635 := bstep (se 1 (by rfl) ⟨1147226, by rfl⟩ : syracuseStep 1529635 = 2294453) B2294453
theorem B3266353 : Blo 1528461 3266353 := bstep (se 2 (by rfl) ⟨1224882, by rfl⟩ : syracuseStep 3266353 = 2449765) B2449765
theorem B1529651 : Blo 1528461 1529651 := bstep (se 1 (by rfl) ⟨1147238, by rfl⟩ : syracuseStep 1529651 = 2294477) B2294477
theorem B1529667 : Blo 1528461 1529667 := bstep (se 1 (by rfl) ⟨1147250, by rfl⟩ : syracuseStep 1529667 = 2294501) B2294501
theorem B2324305 : Blo 1528461 2324305 := bstep (se 2 (by rfl) ⟨871614, by rfl⟩ : syracuseStep 2324305 = 1743229) B1743229
theorem B1529683 : Blo 1528461 1529683 := bstep (se 1 (by rfl) ⟨1147262, by rfl⟩ : syracuseStep 1529683 = 2294525) B2294525
theorem B1529699 : Blo 1528461 1529699 := bstep (se 1 (by rfl) ⟨1147274, by rfl⟩ : syracuseStep 1529699 = 2294549) B2294549
theorem B1529715 : Blo 1528461 1529715 := bstep (se 1 (by rfl) ⟨1147286, by rfl⟩ : syracuseStep 1529715 = 2294573) B2294573
theorem B2176897 : Blo 1528461 2176897 := bstep (se 2 (by rfl) ⟨816336, by rfl⟩ : syracuseStep 2176897 = 1632673) B1632673
theorem B1529731 : Blo 1528461 1529731 := bstep (se 1 (by rfl) ⟨1147298, by rfl⟩ : syracuseStep 1529731 = 2294597) B2294597
theorem B4355981 : Blo 1528461 4355981 := bstep (se 3 (by rfl) ⟨816746, by rfl⟩ : syracuseStep 4355981 = 1633493) B1633493
theorem B1529747 : Blo 1528461 1529747 := bstep (se 1 (by rfl) ⟨1147310, by rfl⟩ : syracuseStep 1529747 = 2294621) B2294621
theorem B1529763 : Blo 1528461 1529763 := bstep (se 1 (by rfl) ⟨1147322, by rfl⟩ : syracuseStep 1529763 = 2294645) B2294645
theorem B1529779 : Blo 1528461 1529779 := bstep (se 1 (by rfl) ⟨1147334, by rfl⟩ : syracuseStep 1529779 = 2294669) B2294669
theorem B1529795 : Blo 1528461 1529795 := bstep (se 1 (by rfl) ⟨1147346, by rfl⟩ : syracuseStep 1529795 = 2294693) B2294693
theorem B1529811 : Blo 1528461 1529811 := bstep (se 1 (by rfl) ⟨1147358, by rfl⟩ : syracuseStep 1529811 = 2294717) B2294717
theorem B1529827 : Blo 1528461 1529827 := bstep (se 1 (by rfl) ⟨1147370, by rfl⟩ : syracuseStep 1529827 = 2294741) B2294741
theorem B1529843 : Blo 1528461 1529843 := bstep (se 1 (by rfl) ⟨1147382, by rfl⟩ : syracuseStep 1529843 = 2294765) B2294765
theorem B1529859 : Blo 1528461 1529859 := bstep (se 1 (by rfl) ⟨1147394, by rfl⟩ : syracuseStep 1529859 = 2294789) B2294789
theorem B1529875 : Blo 1528461 1529875 := bstep (se 1 (by rfl) ⟨1147406, by rfl⟩ : syracuseStep 1529875 = 2294813) B2294813
theorem B1529891 : Blo 1528461 1529891 := bstep (se 1 (by rfl) ⟨1147418, by rfl⟩ : syracuseStep 1529891 = 2294837) B2294837
theorem B1529907 : Blo 1528461 1529907 := bstep (se 1 (by rfl) ⟨1147430, by rfl⟩ : syracuseStep 1529907 = 2294861) B2294861
theorem B1529923 : Blo 1528461 1529923 := bstep (se 1 (by rfl) ⟨1147442, by rfl⟩ : syracuseStep 1529923 = 2294885) B2294885
theorem B1529939 : Blo 1528461 1529939 := bstep (se 1 (by rfl) ⟨1147454, by rfl⟩ : syracuseStep 1529939 = 2294909) B2294909
theorem B2324579 : Blo 1528461 2324579 := bstep (se 1 (by rfl) ⟨1743434, by rfl⟩ : syracuseStep 2324579 = 3486869) B3486869
theorem B1529955 : Blo 1528461 1529955 := bstep (se 1 (by rfl) ⟨1147466, by rfl⟩ : syracuseStep 1529955 = 2294933) B2294933
theorem B1529971 : Blo 1528461 1529971 := bstep (se 1 (by rfl) ⟨1147478, by rfl⟩ : syracuseStep 1529971 = 2294957) B2294957
theorem B1529987 : Blo 1528461 1529987 := bstep (se 1 (by rfl) ⟨1147490, by rfl⟩ : syracuseStep 1529987 = 2294981) B2294981
theorem B1530003 : Blo 1528461 1530003 := bstep (se 1 (by rfl) ⟨1147502, by rfl⟩ : syracuseStep 1530003 = 2295005) B2295005
theorem B1530019 : Blo 1528461 1530019 := bstep (se 1 (by rfl) ⟨1147514, by rfl⟩ : syracuseStep 1530019 = 2295029) B2295029
theorem B1530035 : Blo 1528461 1530035 := bstep (se 1 (by rfl) ⟨1147526, by rfl⟩ : syracuseStep 1530035 = 2295053) B2295053
theorem B1530051 : Blo 1528461 1530051 := bstep (se 1 (by rfl) ⟨1147538, by rfl⟩ : syracuseStep 1530051 = 2295077) B2295077
theorem B1530067 : Blo 1528461 1530067 := bstep (se 1 (by rfl) ⟨1147550, by rfl⟩ : syracuseStep 1530067 = 2295101) B2295101
theorem B5511395 : Blo 1528461 5511395 := bstep (se 1 (by rfl) ⟨4133546, by rfl⟩ : syracuseStep 5511395 = 8267093) B8267093
theorem B1530083 : Blo 1528461 1530083 := bstep (se 1 (by rfl) ⟨1147562, by rfl⟩ : syracuseStep 1530083 = 2295125) B2295125
theorem B7747811 : Blo 1528461 7747811 := bstep (se 1 (by rfl) ⟨5810858, by rfl⟩ : syracuseStep 7747811 = 11621717) B11621717
theorem B1530099 : Blo 1528461 1530099 := bstep (se 1 (by rfl) ⟨1147574, by rfl⟩ : syracuseStep 1530099 = 2295149) B2295149
theorem B1530115 : Blo 1528461 1530115 := bstep (se 1 (by rfl) ⟨1147586, by rfl⟩ : syracuseStep 1530115 = 2295173) B2295173
theorem B5806349 : Blo 1528461 5806349 := bstep (se 3 (by rfl) ⟨1088690, by rfl⟩ : syracuseStep 5806349 = 2177381) B2177381
theorem B1530131 : Blo 1528461 1530131 := bstep (se 1 (by rfl) ⟨1147598, by rfl⟩ : syracuseStep 1530131 = 2295197) B2295197
theorem B1530147 : Blo 1528461 1530147 := bstep (se 1 (by rfl) ⟨1147610, by rfl⟩ : syracuseStep 1530147 = 2295221) B2295221
theorem B5159213 : Blo 1528461 5159213 := bstep (se 3 (by rfl) ⟨967352, by rfl⟩ : syracuseStep 5159213 = 1934705) B1934705
theorem B1530163 : Blo 1528461 1530163 := bstep (se 1 (by rfl) ⟨1147622, by rfl⟩ : syracuseStep 1530163 = 2295245) B2295245
theorem B1530179 : Blo 1528461 1530179 := bstep (se 1 (by rfl) ⟨1147634, by rfl⟩ : syracuseStep 1530179 = 2295269) B2295269
theorem B1530195 : Blo 1528461 1530195 := bstep (se 1 (by rfl) ⟨1147646, by rfl⟩ : syracuseStep 1530195 = 2295293) B2295293
theorem B5159267 : Blo 1528461 5159267 := bstep (se 1 (by rfl) ⟨3869450, by rfl⟩ : syracuseStep 5159267 = 7738901) B7738901
theorem B1530211 : Blo 1528461 1530211 := bstep (se 1 (by rfl) ⟨1147658, by rfl⟩ : syracuseStep 1530211 = 2295317) B2295317
theorem B1530227 : Blo 1528461 1530227 := bstep (se 1 (by rfl) ⟨1147670, by rfl⟩ : syracuseStep 1530227 = 2295341) B2295341
theorem B1530243 : Blo 1528461 1530243 := bstep (se 1 (by rfl) ⟨1147682, by rfl⟩ : syracuseStep 1530243 = 2295365) B2295365
theorem B1530259 : Blo 1528461 1530259 := bstep (se 1 (by rfl) ⟨1147694, by rfl⟩ : syracuseStep 1530259 = 2295389) B2295389
theorem B1530275 : Blo 1528461 1530275 := bstep (se 1 (by rfl) ⟨1147706, by rfl⟩ : syracuseStep 1530275 = 2295413) B2295413
theorem B1530291 : Blo 1528461 1530291 := bstep (se 1 (by rfl) ⟨1147718, by rfl⟩ : syracuseStep 1530291 = 2295437) B2295437
theorem B3439043 : Blo 1528461 3439043 := bstep (se 1 (by rfl) ⟨2579282, by rfl⟩ : syracuseStep 3439043 = 5158565) B5158565
theorem B1530307 : Blo 1528461 1530307 := bstep (se 1 (by rfl) ⟨1147730, by rfl⟩ : syracuseStep 1530307 = 2295461) B2295461
theorem B2177489 : Blo 1528461 2177489 := bstep (se 2 (by rfl) ⟨816558, by rfl⟩ : syracuseStep 2177489 = 1633117) B1633117
theorem B1530323 : Blo 1528461 1530323 := bstep (se 1 (by rfl) ⟨1147742, by rfl⟩ : syracuseStep 1530323 = 2295485) B2295485
theorem B22034915 : Blo 1528461 22034915 := bstep (se 1 (by rfl) ⟨16526186, by rfl⟩ : syracuseStep 22034915 = 33052373) B33052373
theorem B1530339 : Blo 1528461 1530339 := bstep (se 1 (by rfl) ⟨1147754, by rfl⟩ : syracuseStep 1530339 = 2295509) B2295509
theorem B1530355 : Blo 1528461 1530355 := bstep (se 1 (by rfl) ⟨1147766, by rfl⟩ : syracuseStep 1530355 = 2295533) B2295533
theorem B1530371 : Blo 1528461 1530371 := bstep (se 1 (by rfl) ⟨1147778, by rfl⟩ : syracuseStep 1530371 = 2295557) B2295557
theorem B1530387 : Blo 1528461 1530387 := bstep (se 1 (by rfl) ⟨1147790, by rfl⟩ : syracuseStep 1530387 = 2295581) B2295581
theorem B2095651 : Blo 1528461 2095651 := bstep (se 1 (by rfl) ⟨1571738, by rfl⟩ : syracuseStep 2095651 = 3143477) B3143477
theorem B1530403 : Blo 1528461 1530403 := bstep (se 1 (by rfl) ⟨1147802, by rfl⟩ : syracuseStep 1530403 = 2295605) B2295605
theorem B3873329 : Blo 1528461 3873329 := bstep (se 2 (by rfl) ⟨1452498, by rfl⟩ : syracuseStep 3873329 = 2904997) B2904997
theorem B1530419 : Blo 1528461 1530419 := bstep (se 1 (by rfl) ⟨1147814, by rfl⟩ : syracuseStep 1530419 = 2295629) B2295629
theorem B1530435 : Blo 1528461 1530435 := bstep (se 1 (by rfl) ⟨1147826, by rfl⟩ : syracuseStep 1530435 = 2295653) B2295653
theorem B8706629 : Blo 1528461 8706629 := bstep (se 4 (by rfl) ⟨816246, by rfl⟩ : syracuseStep 8706629 = 1632493) B1632493
theorem B1530451 : Blo 1528461 1530451 := bstep (se 1 (by rfl) ⟨1147838, by rfl⟩ : syracuseStep 1530451 = 2295677) B2295677
theorem B3873379 : Blo 1528461 3873379 := bstep (se 1 (by rfl) ⟨2905034, by rfl⟩ : syracuseStep 3873379 = 5810069) B5810069
theorem B5159537 : Blo 1528461 5159537 := bstep (se 2 (by rfl) ⟨1934826, by rfl⟩ : syracuseStep 5159537 = 3869653) B3869653
theorem B3439313 : Blo 1528461 3439313 := bstep (se 2 (by rfl) ⟨1289742, by rfl⟩ : syracuseStep 3439313 = 2579485) B2579485
theorem B2325217 : Blo 1528461 2325217 := bstep (se 2 (by rfl) ⟨871956, by rfl⟩ : syracuseStep 2325217 = 1743913) B1743913
theorem B3439331 : Blo 1528461 3439331 := bstep (se 1 (by rfl) ⟨2579498, by rfl⟩ : syracuseStep 3439331 = 5158997) B5158997
theorem B3873521 : Blo 1528461 3873521 := bstep (se 2 (by rfl) ⟨1452570, by rfl⟩ : syracuseStep 3873521 = 2905141) B2905141
theorem B9075469 : Blo 1528461 9075469 := bstep (se 3 (by rfl) ⟨1701650, by rfl⟩ : syracuseStep 9075469 = 3403301) B3403301
theorem B10459973 : Blo 1528461 10459973 := bstep (se 4 (by rfl) ⟨980622, by rfl⟩ : syracuseStep 10459973 = 1961245) B1961245
theorem B7846769 : Blo 1528461 7846769 := bstep (se 2 (by rfl) ⟨2942538, by rfl⟩ : syracuseStep 7846769 = 5885077) B5885077
theorem B2579377 : Blo 1528461 2579377 := bstep (se 2 (by rfl) ⟨967266, by rfl⟩ : syracuseStep 2579377 = 1934533) B1934533
theorem B2579411 : Blo 1528461 2579411 := bstep (se 1 (by rfl) ⟨1934558, by rfl⟩ : syracuseStep 2579411 = 3869117) B3869117
theorem B2292707 : Blo 1528461 2292707 := bstep (se 1 (by rfl) ⟨1719530, by rfl⟩ : syracuseStep 2292707 = 3439061) B3439061
theorem B2178019 : Blo 1528461 2178019 := bstep (se 1 (by rfl) ⟨1633514, by rfl⟩ : syracuseStep 2178019 = 3267029) B3267029
theorem B3439601 : Blo 1528461 3439601 := bstep (se 2 (by rfl) ⟨1289850, by rfl⟩ : syracuseStep 3439601 = 2579701) B2579701
theorem B2292737 : Blo 1528461 2292737 := bstep (se 2 (by rfl) ⟨859776, by rfl⟩ : syracuseStep 2292737 = 1719553) B1719553
theorem B3439619 : Blo 1528461 3439619 := bstep (se 1 (by rfl) ⟨2579714, by rfl⟩ : syracuseStep 3439619 = 5159429) B5159429
theorem B8707085 : Blo 1528461 8707085 := bstep (se 3 (by rfl) ⟨1632578, by rfl⟩ : syracuseStep 8707085 = 3265157) B3265157
theorem B2292755 : Blo 1528461 2292755 := bstep (se 1 (by rfl) ⟨1719566, by rfl⟩ : syracuseStep 2292755 = 3439133) B3439133
theorem B5233709 : Blo 1528461 5233709 := bstep (se 3 (by rfl) ⟨981320, by rfl⟩ : syracuseStep 5233709 = 1962641) B1962641
theorem B4357165 : Blo 1528461 4357165 := bstep (se 3 (by rfl) ⟨816968, by rfl⟩ : syracuseStep 4357165 = 1633937) B1633937
theorem B2292785 : Blo 1528461 2292785 := bstep (se 2 (by rfl) ⟨859794, by rfl⟩ : syracuseStep 2292785 = 1719589) B1719589
theorem B5807153 : Blo 1528461 5807153 := bstep (se 2 (by rfl) ⟨2177682, by rfl⟩ : syracuseStep 5807153 = 4355365) B4355365
theorem B2292803 : Blo 1528461 2292803 := bstep (se 1 (by rfl) ⟨1719602, by rfl⟩ : syracuseStep 2292803 = 3439205) B3439205
theorem B8272973 : Blo 1528461 8272973 := bstep (se 3 (by rfl) ⟨1551182, by rfl⟩ : syracuseStep 8272973 = 3102365) B3102365
theorem B2579539 : Blo 1528461 2579539 := bstep (se 1 (by rfl) ⟨1934654, by rfl⟩ : syracuseStep 2579539 = 3869309) B3869309
theorem B2292833 : Blo 1528461 2292833 := bstep (se 2 (by rfl) ⟨859812, by rfl⟩ : syracuseStep 2292833 = 1719625) B1719625
theorem B8715377 : Blo 1528461 8715377 := bstep (se 2 (by rfl) ⟨3268266, by rfl⟩ : syracuseStep 8715377 = 6536533) B6536533
theorem B2292851 : Blo 1528461 2292851 := bstep (se 1 (by rfl) ⟨1719638, by rfl⟩ : syracuseStep 2292851 = 3439277) B3439277
theorem B5160077 : Blo 1528461 5160077 := bstep (se 3 (by rfl) ⟨967514, by rfl⟩ : syracuseStep 5160077 = 1935029) B1935029
theorem B2292881 : Blo 1528461 2292881 := bstep (se 2 (by rfl) ⟨859830, by rfl⟩ : syracuseStep 2292881 = 1719661) B1719661
theorem B2792593 : Blo 1528461 2792593 := bstep (se 2 (by rfl) ⟨1047222, by rfl⟩ : syracuseStep 2792593 = 2094445) B2094445
theorem B2292899 : Blo 1528461 2292899 := bstep (se 1 (by rfl) ⟨1719674, by rfl⟩ : syracuseStep 2292899 = 3439349) B3439349
theorem B5889187 : Blo 1528461 5889187 := bstep (se 1 (by rfl) ⟨4416890, by rfl⟩ : syracuseStep 5889187 = 8833781) B8833781
theorem B2292929 : Blo 1528461 2292929 := bstep (se 2 (by rfl) ⟨859848, by rfl⟩ : syracuseStep 2292929 = 1719697) B1719697
theorem B5160131 : Blo 1528461 5160131 := bstep (se 1 (by rfl) ⟨3870098, by rfl⟩ : syracuseStep 5160131 = 7740197) B7740197
theorem B4136141 : Blo 1528461 4136141 := bstep (se 3 (by rfl) ⟨775526, by rfl⟩ : syracuseStep 4136141 = 1551053) B1551053
theorem B2292947 : Blo 1528461 2292947 := bstep (se 1 (by rfl) ⟨1719710, by rfl⟩ : syracuseStep 2292947 = 3439421) B3439421
theorem B2579681 : Blo 1528461 2579681 := bstep (se 2 (by rfl) ⟨967380, by rfl⟩ : syracuseStep 2579681 = 1934761) B1934761
theorem B2292977 : Blo 1528461 2292977 := bstep (se 2 (by rfl) ⟨859866, by rfl⟩ : syracuseStep 2292977 = 1719733) B1719733
theorem B2292995 : Blo 1528461 2292995 := bstep (se 1 (by rfl) ⟨1719746, by rfl⟩ : syracuseStep 2292995 = 3439493) B3439493
theorem B3439889 : Blo 1528461 3439889 := bstep (se 2 (by rfl) ⟨1289958, by rfl⟩ : syracuseStep 3439889 = 2579917) B2579917
theorem B3267857 : Blo 1528461 3267857 := bstep (se 2 (by rfl) ⟨1225446, by rfl⟩ : syracuseStep 3267857 = 2450893) B2450893
theorem B1719571 : Blo 1528461 1719571 := bstep (se 1 (by rfl) ⟨1289678, by rfl⟩ : syracuseStep 1719571 = 2579357) B2579357
theorem B2293025 : Blo 1528461 2293025 := bstep (se 2 (by rfl) ⟨859884, by rfl⟩ : syracuseStep 2293025 = 1719769) B1719769
theorem B3439907 : Blo 1528461 3439907 := bstep (se 1 (by rfl) ⟨2579930, by rfl⟩ : syracuseStep 3439907 = 5159861) B5159861
theorem B4898083 : Blo 1528461 4898083 := bstep (se 1 (by rfl) ⟨3673562, by rfl⟩ : syracuseStep 4898083 = 7347125) B7347125
theorem B2293043 : Blo 1528461 2293043 := bstep (se 1 (by rfl) ⟨1719782, by rfl⟩ : syracuseStep 2293043 = 3439565) B3439565
theorem B2178355 : Blo 1528461 2178355 := bstep (se 1 (by rfl) ⟨1633766, by rfl⟩ : syracuseStep 2178355 = 3267533) B3267533
theorem B2293073 : Blo 1528461 2293073 := bstep (se 2 (by rfl) ⟨859902, by rfl⟩ : syracuseStep 2293073 = 1719805) B1719805
theorem B2579809 : Blo 1528461 2579809 := bstep (se 2 (by rfl) ⟨967428, by rfl⟩ : syracuseStep 2579809 = 1934857) B1934857
theorem B2293091 : Blo 1528461 2293091 := bstep (se 1 (by rfl) ⟨1719818, by rfl⟩ : syracuseStep 2293091 = 3439637) B3439637
theorem B2293121 : Blo 1528461 2293121 := bstep (se 2 (by rfl) ⟨859920, by rfl⟩ : syracuseStep 2293121 = 1719841) B1719841
theorem B2579843 : Blo 1528461 2579843 := bstep (se 1 (by rfl) ⟨1934882, by rfl⟩ : syracuseStep 2579843 = 3869765) B3869765
theorem B2293139 : Blo 1528461 2293139 := bstep (se 1 (by rfl) ⟨1719854, by rfl⟩ : syracuseStep 2293139 = 3439709) B3439709
theorem B1719715 : Blo 1528461 1719715 := bstep (se 1 (by rfl) ⟨1289786, by rfl⟩ : syracuseStep 1719715 = 2579573) B2579573
theorem B2293169 : Blo 1528461 2293169 := bstep (se 2 (by rfl) ⟨859938, by rfl⟩ : syracuseStep 2293169 = 1719877) B1719877
theorem B2293187 : Blo 1528461 2293187 := bstep (se 1 (by rfl) ⟨1719890, by rfl⟩ : syracuseStep 2293187 = 3439781) B3439781
theorem B8830405 : Blo 1528461 8830405 := bstep (se 4 (by rfl) ⟨827850, by rfl⟩ : syracuseStep 8830405 = 1655701) B1655701
theorem B5160401 : Blo 1528461 5160401 := bstep (se 2 (by rfl) ⟨1935150, by rfl⟩ : syracuseStep 5160401 = 3870301) B3870301
theorem B2293217 : Blo 1528461 2293217 := bstep (se 2 (by rfl) ⟨859956, by rfl⟩ : syracuseStep 2293217 = 1719913) B1719913
theorem B2293235 : Blo 1528461 2293235 := bstep (se 1 (by rfl) ⟨1719926, by rfl⟩ : syracuseStep 2293235 = 3439853) B3439853
theorem B2579971 : Blo 1528461 2579971 := bstep (se 1 (by rfl) ⟨1934978, by rfl⟩ : syracuseStep 2579971 = 3869957) B3869957
theorem B2293265 : Blo 1528461 2293265 := bstep (se 2 (by rfl) ⟨859974, by rfl⟩ : syracuseStep 2293265 = 1719949) B1719949
theorem B2293283 : Blo 1528461 2293283 := bstep (se 1 (by rfl) ⟨1719962, by rfl⟩ : syracuseStep 2293283 = 3439925) B3439925
theorem B3440177 : Blo 1528461 3440177 := bstep (se 2 (by rfl) ⟨1290066, by rfl⟩ : syracuseStep 3440177 = 2580133) B2580133
theorem B1719859 : Blo 1528461 1719859 := bstep (se 1 (by rfl) ⟨1289894, by rfl⟩ : syracuseStep 1719859 = 2579789) B2579789
theorem B2293313 : Blo 1528461 2293313 := bstep (se 2 (by rfl) ⟨859992, by rfl⟩ : syracuseStep 2293313 = 1719985) B1719985
theorem B3440195 : Blo 1528461 3440195 := bstep (se 1 (by rfl) ⟨2580146, by rfl⟩ : syracuseStep 3440195 = 5160293) B5160293
theorem B2293331 : Blo 1528461 2293331 := bstep (se 1 (by rfl) ⟨1719998, by rfl⟩ : syracuseStep 2293331 = 3439997) B3439997
theorem B2293361 : Blo 1528461 2293361 := bstep (se 2 (by rfl) ⟨860010, by rfl⟩ : syracuseStep 2293361 = 1720021) B1720021
theorem B14900849 : Blo 1528461 14900849 := bstep (se 2 (by rfl) ⟨5587818, by rfl⟩ : syracuseStep 14900849 = 11175637) B11175637
theorem B2293379 : Blo 1528461 2293379 := bstep (se 1 (by rfl) ⟨1720034, by rfl⟩ : syracuseStep 2293379 = 3440069) B3440069
theorem B11615885 : Blo 1528461 11615885 := bstep (se 3 (by rfl) ⟨2177978, by rfl⟩ : syracuseStep 11615885 = 4355957) B4355957
theorem B2580113 : Blo 1528461 2580113 := bstep (se 2 (by rfl) ⟨967542, by rfl⟩ : syracuseStep 2580113 = 1935085) B1935085
theorem B2293409 : Blo 1528461 2293409 := bstep (se 2 (by rfl) ⟨860028, by rfl⟩ : syracuseStep 2293409 = 1720057) B1720057
theorem B3268259 : Blo 1528461 3268259 := bstep (se 1 (by rfl) ⟨2451194, by rfl⟩ : syracuseStep 3268259 = 4902389) B4902389
theorem B2449073 : Blo 1528461 2449073 := bstep (se 2 (by rfl) ⟨918402, by rfl⟩ : syracuseStep 2449073 = 1836805) B1836805
theorem B2293427 : Blo 1528461 2293427 := bstep (se 1 (by rfl) ⟨1720070, by rfl⟩ : syracuseStep 2293427 = 3440141) B3440141
theorem B1720003 : Blo 1528461 1720003 := bstep (se 1 (by rfl) ⟨1290002, by rfl⟩ : syracuseStep 1720003 = 2580005) B2580005
theorem B5807821 : Blo 1528461 5807821 := bstep (se 3 (by rfl) ⟨1088966, by rfl⟩ : syracuseStep 5807821 = 2177933) B2177933
theorem B2293457 : Blo 1528461 2293457 := bstep (se 2 (by rfl) ⟨860046, by rfl⟩ : syracuseStep 2293457 = 1720093) B1720093
theorem B2293475 : Blo 1528461 2293475 := bstep (se 1 (by rfl) ⟨1720106, by rfl⟩ : syracuseStep 2293475 = 3440213) B3440213
theorem B4898531 : Blo 1528461 4898531 := bstep (se 1 (by rfl) ⟨3673898, by rfl⟩ : syracuseStep 4898531 = 7347797) B7347797
theorem B7741169 : Blo 1528461 7741169 := bstep (se 2 (by rfl) ⟨2902938, by rfl⟩ : syracuseStep 7741169 = 5805877) B5805877
theorem B2293505 : Blo 1528461 2293505 := bstep (se 2 (by rfl) ⟨860064, by rfl⟩ : syracuseStep 2293505 = 1720129) B1720129
theorem B2580241 : Blo 1528461 2580241 := bstep (se 2 (by rfl) ⟨967590, by rfl⟩ : syracuseStep 2580241 = 1935181) B1935181
theorem B2293523 : Blo 1528461 2293523 := bstep (se 1 (by rfl) ⟨1720142, by rfl⟩ : syracuseStep 2293523 = 3440285) B3440285
theorem B1744675 : Blo 1528461 1744675 := bstep (se 1 (by rfl) ⟨1308506, by rfl⟩ : syracuseStep 1744675 = 2617013) B2617013
theorem B2449201 : Blo 1528461 2449201 := bstep (se 2 (by rfl) ⟨918450, by rfl⟩ : syracuseStep 2449201 = 1836901) B1836901
theorem B2293553 : Blo 1528461 2293553 := bstep (se 2 (by rfl) ⟨860082, by rfl⟩ : syracuseStep 2293553 = 1720165) B1720165
theorem B2580275 : Blo 1528461 2580275 := bstep (se 1 (by rfl) ⟨1935206, by rfl⟩ : syracuseStep 2580275 = 3870413) B3870413
theorem B2293571 : Blo 1528461 2293571 := bstep (se 1 (by rfl) ⟨1720178, by rfl⟩ : syracuseStep 2293571 = 3440357) B3440357
theorem B16539461 : Blo 1528461 16539461 := bstep (se 4 (by rfl) ⟨1550574, by rfl⟩ : syracuseStep 16539461 = 3101149) B3101149
theorem B3440465 : Blo 1528461 3440465 := bstep (se 2 (by rfl) ⟨1290174, by rfl⟩ : syracuseStep 3440465 = 2580349) B2580349
theorem B1720147 : Blo 1528461 1720147 := bstep (se 1 (by rfl) ⟨1290110, by rfl⟩ : syracuseStep 1720147 = 2580221) B2580221
theorem B2293601 : Blo 1528461 2293601 := bstep (se 2 (by rfl) ⟨860100, by rfl⟩ : syracuseStep 2293601 = 1720201) B1720201
theorem B2178913 : Blo 1528461 2178913 := bstep (se 2 (by rfl) ⟨817092, by rfl⟩ : syracuseStep 2178913 = 1634185) B1634185
theorem B3440483 : Blo 1528461 3440483 := bstep (se 1 (by rfl) ⟨2580362, by rfl⟩ : syracuseStep 3440483 = 5160725) B5160725
theorem B2293619 : Blo 1528461 2293619 := bstep (se 1 (by rfl) ⟨1720214, by rfl⟩ : syracuseStep 2293619 = 3440429) B3440429
theorem B2178947 : Blo 1528461 2178947 := bstep (se 1 (by rfl) ⟨1634210, by rfl⟩ : syracuseStep 2178947 = 3268421) B3268421
theorem B2293649 : Blo 1528461 2293649 := bstep (se 2 (by rfl) ⟨860118, by rfl⟩ : syracuseStep 2293649 = 1720237) B1720237
theorem B2293667 : Blo 1528461 2293667 := bstep (se 1 (by rfl) ⟨1720250, by rfl⟩ : syracuseStep 2293667 = 3440501) B3440501
theorem B2580403 : Blo 1528461 2580403 := bstep (se 1 (by rfl) ⟨1935302, by rfl⟩ : syracuseStep 2580403 = 3870605) B3870605
theorem B2293697 : Blo 1528461 2293697 := bstep (se 2 (by rfl) ⟨860136, by rfl⟩ : syracuseStep 2293697 = 1720273) B1720273
theorem B16752581 : Blo 1528461 16752581 := bstep (se 4 (by rfl) ⟨1570554, by rfl⟩ : syracuseStep 16752581 = 3141109) B3141109
theorem B2293715 : Blo 1528461 2293715 := bstep (se 1 (by rfl) ⟨1720286, by rfl⟩ : syracuseStep 2293715 = 3440573) B3440573
theorem B1720291 : Blo 1528461 1720291 := bstep (se 1 (by rfl) ⟨1290218, by rfl⟩ : syracuseStep 1720291 = 2580437) B2580437
theorem B5160941 : Blo 1528461 5160941 := bstep (se 3 (by rfl) ⟨967676, by rfl⟩ : syracuseStep 5160941 = 1935353) B1935353
theorem B2293745 : Blo 1528461 2293745 := bstep (se 2 (by rfl) ⟨860154, by rfl⟩ : syracuseStep 2293745 = 1720309) B1720309
theorem B2580491 : Blo 1528461 2580491 := bstep (se 1 (by rfl) ⟨1935368, by rfl⟩ : syracuseStep 2580491 = 3870737) B3870737
theorem B4898839 : Blo 1528461 4898839 := bstep (se 1 (by rfl) ⟨3674129, by rfl⟩ : syracuseStep 4898839 = 7348259) B7348259
theorem B3440663 : Blo 1528461 3440663 := bstep (se 1 (by rfl) ⟨2580497, by rfl⟩ : syracuseStep 3440663 = 5160995) B5160995
theorem B1720363 : Blo 1528461 1720363 := bstep (se 1 (by rfl) ⟨1290272, by rfl⟩ : syracuseStep 1720363 = 2580545) B2580545
theorem B11608109 : Blo 1528461 11608109 := bstep (se 3 (by rfl) ⟨2176520, by rfl⟩ : syracuseStep 11608109 = 4353041) B4353041
theorem B2293835 : Blo 1528461 2293835 := bstep (se 1 (by rfl) ⟨1720376, by rfl⟩ : syracuseStep 2293835 = 3440753) B3440753
theorem B2293847 : Blo 1528461 2293847 := bstep (se 1 (by rfl) ⟨1720385, by rfl⟩ : syracuseStep 2293847 = 3440771) B3440771
theorem B5161049 : Blo 1528461 5161049 := bstep (se 2 (by rfl) ⟨1935393, by rfl⟩ : syracuseStep 5161049 = 3870787) B3870787
theorem B2580619 : Blo 1528461 2580619 := bstep (se 1 (by rfl) ⟨1935464, by rfl⟩ : syracuseStep 2580619 = 3870929) B3870929
theorem B1720471 : Blo 1528461 1720471 := bstep (se 1 (by rfl) ⟨1290353, by rfl⟩ : syracuseStep 1720471 = 2580707) B2580707
theorem B2293913 : Blo 1528461 2293913 := bstep (se 2 (by rfl) ⟨860217, by rfl⟩ : syracuseStep 2293913 = 1720435) B1720435
theorem B5808307 : Blo 1528461 5808307 := bstep (se 1 (by rfl) ⟨4356230, by rfl⟩ : syracuseStep 5808307 = 8712461) B8712461
theorem B3440843 : Blo 1528461 3440843 := bstep (se 1 (by rfl) ⟨2580632, by rfl⟩ : syracuseStep 3440843 = 5161265) B5161265
theorem B22061261 : Blo 1528461 22061261 := bstep (se 3 (by rfl) ⟨4136486, by rfl⟩ : syracuseStep 22061261 = 8272973) B8272973
theorem B3440897 : Blo 1528461 3440897 := bstep (se 2 (by rfl) ⟨1290336, by rfl⟩ : syracuseStep 3440897 = 2580673) B2580673
theorem B2294027 : Blo 1528461 2294027 := bstep (se 1 (by rfl) ⟨1720520, by rfl⟩ : syracuseStep 2294027 = 3441041) B3441041
theorem B2294039 : Blo 1528461 2294039 := bstep (se 1 (by rfl) ⟨1720529, by rfl⟩ : syracuseStep 2294039 = 3441059) B3441059
theorem B2580761 : Blo 1528461 2580761 := bstep (se 2 (by rfl) ⟨967785, by rfl⟩ : syracuseStep 2580761 = 1935571) B1935571
theorem B1720651 : Blo 1528461 1720651 := bstep (se 1 (by rfl) ⟨1290488, by rfl⟩ : syracuseStep 1720651 = 2580977) B2580977
theorem B2326871 : Blo 1528461 2326871 := bstep (se 1 (by rfl) ⟨1745153, by rfl⟩ : syracuseStep 2326871 = 3490307) B3490307
theorem B2294105 : Blo 1528461 2294105 := bstep (se 2 (by rfl) ⟨860289, by rfl⟩ : syracuseStep 2294105 = 1720579) B1720579
theorem B2580889 : Blo 1528461 2580889 := bstep (se 2 (by rfl) ⟨967833, by rfl⟩ : syracuseStep 2580889 = 1935667) B1935667
theorem B1720759 : Blo 1528461 1720759 := bstep (se 1 (by rfl) ⟨1290569, by rfl⟩ : syracuseStep 1720759 = 2581139) B2581139
theorem B4899275 : Blo 1528461 4899275 := bstep (se 1 (by rfl) ⟨3674456, by rfl⟩ : syracuseStep 4899275 = 7348913) B7348913
theorem B2294219 : Blo 1528461 2294219 := bstep (se 1 (by rfl) ⟨1720664, by rfl⟩ : syracuseStep 2294219 = 3441329) B3441329
theorem B2294231 : Blo 1528461 2294231 := bstep (se 1 (by rfl) ⟨1720673, by rfl⟩ : syracuseStep 2294231 = 3441347) B3441347
theorem B3441113 : Blo 1528461 3441113 := bstep (se 2 (by rfl) ⟨1290417, by rfl⟩ : syracuseStep 3441113 = 2580835) B2580835
theorem B2294297 : Blo 1528461 2294297 := bstep (se 2 (by rfl) ⟨860361, by rfl⟩ : syracuseStep 2294297 = 1720723) B1720723
theorem B3441203 : Blo 1528461 3441203 := bstep (se 1 (by rfl) ⟨2580902, by rfl⟩ : syracuseStep 3441203 = 5161805) B5161805
theorem B3441239 : Blo 1528461 3441239 := bstep (se 1 (by rfl) ⟨2580929, by rfl⟩ : syracuseStep 3441239 = 5161859) B5161859
theorem B1720939 : Blo 1528461 1720939 := bstep (se 1 (by rfl) ⟨1290704, by rfl⟩ : syracuseStep 1720939 = 2581409) B2581409
theorem B2294411 : Blo 1528461 2294411 := bstep (se 1 (by rfl) ⟨1720808, by rfl⟩ : syracuseStep 2294411 = 3441617) B3441617
theorem B2294423 : Blo 1528461 2294423 := bstep (se 1 (by rfl) ⟨1720817, by rfl⟩ : syracuseStep 2294423 = 3441635) B3441635
theorem B3310259 : Blo 1528461 3310259 := bstep (se 1 (by rfl) ⟨2482694, by rfl⟩ : syracuseStep 3310259 = 4965389) B4965389
theorem B1721047 : Blo 1528461 1721047 := bstep (se 1 (by rfl) ⟨1290785, by rfl⟩ : syracuseStep 1721047 = 2581571) B2581571
theorem B2294489 : Blo 1528461 2294489 := bstep (se 2 (by rfl) ⟨860433, by rfl⟩ : syracuseStep 2294489 = 1720867) B1720867
theorem B2794201 : Blo 1528461 2794201 := bstep (se 2 (by rfl) ⟨1047825, by rfl⟩ : syracuseStep 2794201 = 2095651) B2095651
theorem B1655563 : Blo 1528461 1655563 := bstep (se 1 (by rfl) ⟨1241672, by rfl⟩ : syracuseStep 1655563 = 2483345) B2483345
theorem B3441419 : Blo 1528461 3441419 := bstep (se 1 (by rfl) ⟨2581064, by rfl⟩ : syracuseStep 3441419 = 5162129) B5162129
theorem B5161751 : Blo 1528461 5161751 := bstep (se 1 (by rfl) ⟨3871313, by rfl⟩ : syracuseStep 5161751 = 7742627) B7742627
theorem B3441473 : Blo 1528461 3441473 := bstep (se 2 (by rfl) ⟨1290552, by rfl⟩ : syracuseStep 3441473 = 2581105) B2581105
theorem B2294603 : Blo 1528461 2294603 := bstep (se 1 (by rfl) ⟨1720952, by rfl⟩ : syracuseStep 2294603 = 3441905) B3441905
theorem B2294615 : Blo 1528461 2294615 := bstep (se 1 (by rfl) ⟨1720961, by rfl⟩ : syracuseStep 2294615 = 3441923) B3441923
theorem B5514077 : Blo 1528461 5514077 := bstep (se 3 (by rfl) ⟨1033889, by rfl⟩ : syracuseStep 5514077 = 2067779) B2067779
theorem B14705509 : Blo 1528461 14705509 := bstep (se 4 (by rfl) ⟨1378641, by rfl⟩ : syracuseStep 14705509 = 2757283) B2757283
theorem B1721227 : Blo 1528461 1721227 := bstep (se 1 (by rfl) ⟨1290920, by rfl⟩ : syracuseStep 1721227 = 2581841) B2581841
theorem B2294681 : Blo 1528461 2294681 := bstep (se 2 (by rfl) ⟨860505, by rfl⟩ : syracuseStep 2294681 = 1721011) B1721011
theorem B2581463 : Blo 1528461 2581463 := bstep (se 1 (by rfl) ⟨1936097, by rfl⟩ : syracuseStep 2581463 = 3872195) B3872195
theorem B1721335 : Blo 1528461 1721335 := bstep (se 1 (by rfl) ⟨1291001, by rfl⟩ : syracuseStep 1721335 = 2582003) B2582003
theorem B2294795 : Blo 1528461 2294795 := bstep (se 1 (by rfl) ⟨1721096, by rfl⟩ : syracuseStep 2294795 = 3442193) B3442193
theorem B12100625 : Blo 1528461 12100625 := bstep (se 2 (by rfl) ⟨4537734, by rfl⟩ : syracuseStep 12100625 = 9075469) B9075469
theorem B2294807 : Blo 1528461 2294807 := bstep (se 1 (by rfl) ⟨1721105, by rfl⟩ : syracuseStep 2294807 = 3442211) B3442211
theorem B3441689 : Blo 1528461 3441689 := bstep (se 2 (by rfl) ⟨1290633, by rfl⟩ : syracuseStep 3441689 = 2581267) B2581267
theorem B2581591 : Blo 1528461 2581591 := bstep (se 1 (by rfl) ⟨1936193, by rfl⟩ : syracuseStep 2581591 = 3872387) B3872387
theorem B2294873 : Blo 1528461 2294873 := bstep (se 2 (by rfl) ⟨860577, by rfl⟩ : syracuseStep 2294873 = 1721155) B1721155
theorem B3441779 : Blo 1528461 3441779 := bstep (se 1 (by rfl) ⟨2581334, by rfl⟩ : syracuseStep 3441779 = 5162669) B5162669
theorem B3441815 : Blo 1528461 3441815 := bstep (se 1 (by rfl) ⟨2581361, by rfl⟩ : syracuseStep 3441815 = 5162723) B5162723
theorem B2450585 : Blo 1528461 2450585 := bstep (se 2 (by rfl) ⟨918969, by rfl⟩ : syracuseStep 2450585 = 1837939) B1837939
theorem B1721515 : Blo 1528461 1721515 := bstep (se 1 (by rfl) ⟨1291136, by rfl⟩ : syracuseStep 1721515 = 2582273) B2582273
theorem B2294987 : Blo 1528461 2294987 := bstep (se 1 (by rfl) ⟨1721240, by rfl⟩ : syracuseStep 2294987 = 3442481) B3442481
theorem B2294999 : Blo 1528461 2294999 := bstep (se 1 (by rfl) ⟨1721249, by rfl⟩ : syracuseStep 2294999 = 3442499) B3442499
theorem B1721623 : Blo 1528461 1721623 := bstep (se 1 (by rfl) ⟨1291217, by rfl⟩ : syracuseStep 1721623 = 2582435) B2582435
theorem B2295065 : Blo 1528461 2295065 := bstep (se 2 (by rfl) ⟨860649, by rfl⟩ : syracuseStep 2295065 = 1721299) B1721299
theorem B5162291 : Blo 1528461 5162291 := bstep (se 1 (by rfl) ⟨3871718, by rfl⟩ : syracuseStep 5162291 = 7743437) B7743437
theorem B4900171 : Blo 1528461 4900171 := bstep (se 1 (by rfl) ⟨3675128, by rfl⟩ : syracuseStep 4900171 = 7350257) B7350257
theorem B3441995 : Blo 1528461 3441995 := bstep (se 1 (by rfl) ⟨2581496, by rfl⟩ : syracuseStep 3441995 = 5162993) B5162993
theorem B3442049 : Blo 1528461 3442049 := bstep (se 2 (by rfl) ⟨1290768, by rfl⟩ : syracuseStep 3442049 = 2581537) B2581537
theorem B2295179 : Blo 1528461 2295179 := bstep (se 1 (by rfl) ⟨1721384, by rfl⟩ : syracuseStep 2295179 = 3442769) B3442769
theorem B5809553 : Blo 1528461 5809553 := bstep (se 2 (by rfl) ⟨2178582, by rfl⟩ : syracuseStep 5809553 = 4357165) B4357165
theorem B2295191 : Blo 1528461 2295191 := bstep (se 1 (by rfl) ⟨1721393, by rfl⟩ : syracuseStep 2295191 = 3442787) B3442787
theorem B2295257 : Blo 1528461 2295257 := bstep (se 2 (by rfl) ⟨860721, by rfl⟩ : syracuseStep 2295257 = 1721443) B1721443
theorem B12396037 : Blo 1528461 12396037 := bstep (se 4 (by rfl) ⟨1162128, by rfl⟩ : syracuseStep 12396037 = 2324257) B2324257
theorem B5162561 : Blo 1528461 5162561 := bstep (se 2 (by rfl) ⟨1935960, by rfl⟩ : syracuseStep 5162561 = 3871921) B3871921
theorem B1934923 : Blo 1528461 1934923 := bstep (se 1 (by rfl) ⟨1451192, by rfl⟩ : syracuseStep 1934923 = 2902385) B2902385
theorem B2295371 : Blo 1528461 2295371 := bstep (se 1 (by rfl) ⟨1721528, by rfl⟩ : syracuseStep 2295371 = 3443057) B3443057
theorem B3442265 : Blo 1528461 3442265 := bstep (se 2 (by rfl) ⟨1290849, by rfl⟩ : syracuseStep 3442265 = 2581699) B2581699
theorem B2295383 : Blo 1528461 2295383 := bstep (se 1 (by rfl) ⟨1721537, by rfl⟩ : syracuseStep 2295383 = 3443075) B3443075
theorem B14689943 : Blo 1528461 14689943 := bstep (se 1 (by rfl) ⟨11017457, by rfl⟩ : syracuseStep 14689943 = 22034915) B22034915
theorem B2295449 : Blo 1528461 2295449 := bstep (se 2 (by rfl) ⟨860793, by rfl⟩ : syracuseStep 2295449 = 1721587) B1721587
theorem B3442355 : Blo 1528461 3442355 := bstep (se 1 (by rfl) ⟨2581766, by rfl⟩ : syracuseStep 3442355 = 5163533) B5163533
theorem B2582219 : Blo 1528461 2582219 := bstep (se 1 (by rfl) ⟨1936664, by rfl⟩ : syracuseStep 2582219 = 3873329) B3873329
theorem B3442391 : Blo 1528461 3442391 := bstep (se 1 (by rfl) ⟨2581793, by rfl⟩ : syracuseStep 3442391 = 5163587) B5163587
theorem B6530777 : Blo 1528461 6530777 := bstep (se 2 (by rfl) ⟨2449041, by rfl⟩ : syracuseStep 6530777 = 4898083) B4898083
theorem B12396293 : Blo 1528461 12396293 := bstep (se 4 (by rfl) ⟨1162152, by rfl⟩ : syracuseStep 12396293 = 2324305) B2324305
theorem B2295563 : Blo 1528461 2295563 := bstep (se 1 (by rfl) ⟨1721672, by rfl⟩ : syracuseStep 2295563 = 3443345) B3443345
theorem B2295575 : Blo 1528461 2295575 := bstep (se 1 (by rfl) ⟨1721681, by rfl⟩ : syracuseStep 2295575 = 3443363) B3443363
theorem B6530861 : Blo 1528461 6530861 := bstep (se 3 (by rfl) ⟨1224536, by rfl⟩ : syracuseStep 6530861 = 2449073) B2449073
theorem B19384109 : Blo 1528461 19384109 := bstep (se 3 (by rfl) ⟨3634520, by rfl⟩ : syracuseStep 19384109 = 7269041) B7269041
theorem B2582347 : Blo 1528461 2582347 := bstep (se 1 (by rfl) ⟨1936760, by rfl⟩ : syracuseStep 2582347 = 3873521) B3873521
theorem B1935191 : Blo 1528461 1935191 := bstep (se 1 (by rfl) ⟨1451393, by rfl⟩ : syracuseStep 1935191 = 2902787) B2902787
theorem B2295641 : Blo 1528461 2295641 := bstep (se 2 (by rfl) ⟨860865, by rfl⟩ : syracuseStep 2295641 = 1721731) B1721731
theorem B2901899 : Blo 1528461 2901899 := bstep (se 1 (by rfl) ⟨2176424, by rfl⟩ : syracuseStep 2901899 = 4352849) B4352849
theorem B3442571 : Blo 1528461 3442571 := bstep (se 1 (by rfl) ⟨2581928, by rfl⟩ : syracuseStep 3442571 = 5163857) B5163857
theorem B11773873 : Blo 1528461 11773873 := bstep (se 2 (by rfl) ⟨4415202, by rfl⟩ : syracuseStep 11773873 = 8830405) B8830405
theorem B4900787 : Blo 1528461 4900787 := bstep (se 1 (by rfl) ⟨3675590, by rfl⟩ : syracuseStep 4900787 = 7351181) B7351181
theorem B3442625 : Blo 1528461 3442625 := bstep (se 2 (by rfl) ⟨1290984, by rfl⟩ : syracuseStep 3442625 = 2581969) B2581969
theorem B2582489 : Blo 1528461 2582489 := bstep (se 2 (by rfl) ⟨968433, by rfl⟩ : syracuseStep 2582489 = 1936867) B1936867
theorem B2902081 : Blo 1528461 2902081 := bstep (se 2 (by rfl) ⟨1088280, by rfl⟩ : syracuseStep 2902081 = 2176561) B2176561
theorem B5810251 : Blo 1528461 5810251 := bstep (se 1 (by rfl) ⟨4357688, by rfl⟩ : syracuseStep 5810251 = 8715377) B8715377
theorem B2582617 : Blo 1528461 2582617 := bstep (se 2 (by rfl) ⟨968481, by rfl⟩ : syracuseStep 2582617 = 1936963) B1936963
theorem B5163101 : Blo 1528461 5163101 := bstep (se 3 (by rfl) ⟨968081, by rfl⟩ : syracuseStep 5163101 = 1936163) B1936163
theorem B3442841 : Blo 1528461 3442841 := bstep (se 2 (by rfl) ⟨1291065, by rfl⟩ : syracuseStep 3442841 = 2582131) B2582131
theorem B4901057 : Blo 1528461 4901057 := bstep (se 2 (by rfl) ⟨1837896, by rfl⟩ : syracuseStep 4901057 = 3675793) B3675793
theorem B3311819 : Blo 1528461 3311819 := bstep (se 1 (by rfl) ⟨2483864, by rfl⟩ : syracuseStep 3311819 = 4967729) B4967729
theorem B3442931 : Blo 1528461 3442931 := bstep (se 1 (by rfl) ⟨2582198, by rfl⟩ : syracuseStep 3442931 = 5164397) B5164397
theorem B7743761 : Blo 1528461 7743761 := bstep (se 2 (by rfl) ⟨2903910, by rfl⟩ : syracuseStep 7743761 = 5807821) B5807821
theorem B3442967 : Blo 1528461 3442967 := bstep (se 1 (by rfl) ⟨2582225, by rfl⟩ : syracuseStep 3442967 = 5164451) B5164451
theorem B5810525 : Blo 1528461 5810525 := bstep (se 3 (by rfl) ⟨1089473, by rfl⟩ : syracuseStep 5810525 = 2178947) B2178947
theorem B7743923 : Blo 1528461 7743923 := bstep (se 1 (by rfl) ⟨5807942, by rfl⟩ : syracuseStep 7743923 = 11615885) B11615885
theorem B3443147 : Blo 1528461 3443147 := bstep (se 1 (by rfl) ⟨2582360, by rfl⟩ : syracuseStep 3443147 = 5164721) B5164721
theorem B2902529 : Blo 1528461 2902529 := bstep (se 2 (by rfl) ⟨1088448, by rfl⟩ : syracuseStep 2902529 = 2176897) B2176897
theorem B3443201 : Blo 1528461 3443201 := bstep (se 2 (by rfl) ⟨1291200, by rfl⟩ : syracuseStep 3443201 = 2582401) B2582401
theorem B1935895 : Blo 1528461 1935895 := bstep (se 1 (by rfl) ⟨1451921, by rfl⟩ : syracuseStep 1935895 = 2903843) B2903843
theorem B17001053 : Blo 1528461 17001053 := bstep (se 3 (by rfl) ⟨3187697, by rfl⟩ : syracuseStep 17001053 = 6375395) B6375395
theorem B11168387 : Blo 1528461 11168387 := bstep (se 1 (by rfl) ⟨8376290, by rfl⟩ : syracuseStep 11168387 = 16752581) B16752581
theorem B3672793 : Blo 1528461 3672793 := bstep (se 2 (by rfl) ⟨1377297, by rfl⟩ : syracuseStep 3672793 = 2754595) B2754595
theorem B3443417 : Blo 1528461 3443417 := bstep (se 2 (by rfl) ⟨1291281, by rfl⟩ : syracuseStep 3443417 = 2582563) B2582563
theorem B4352791 : Blo 1528461 4352791 := bstep (se 1 (by rfl) ⟨3264593, by rfl⟩ : syracuseStep 4352791 = 6529187) B6529187
theorem B3869491 : Blo 1528461 3869491 := bstep (se 1 (by rfl) ⟨2902118, by rfl⟩ : syracuseStep 3869491 = 5804237) B5804237
theorem B3443507 : Blo 1528461 3443507 := bstep (se 1 (by rfl) ⟨2582630, by rfl⟩ : syracuseStep 3443507 = 5165261) B5165261
theorem B2902871 : Blo 1528461 2902871 := bstep (se 1 (by rfl) ⟨2177153, by rfl⟩ : syracuseStep 2902871 = 4354307) B4354307
theorem B15698789 : Blo 1528461 15698789 := bstep (se 4 (by rfl) ⟨1471761, by rfl⟩ : syracuseStep 15698789 = 2943523) B2943523
theorem B3869633 : Blo 1528461 3869633 := bstep (se 2 (by rfl) ⟨1451112, by rfl⟩ : syracuseStep 3869633 = 2902225) B2902225
theorem B8711185 : Blo 1528461 8711185 := bstep (se 2 (by rfl) ⟨3266694, by rfl⟩ : syracuseStep 8711185 = 6533389) B6533389
theorem B17427473 : Blo 1528461 17427473 := bstep (se 2 (by rfl) ⟨6535302, by rfl⟩ : syracuseStep 17427473 = 13070605) B13070605
theorem B9301067 : Blo 1528461 9301067 := bstep (se 1 (by rfl) ⟨6975800, by rfl⟩ : syracuseStep 9301067 = 13951601) B13951601
theorem B5164235 : Blo 1528461 5164235 := bstep (se 1 (by rfl) ⟨3873176, by rfl⟩ : syracuseStep 5164235 = 7746353) B7746353
theorem B11029709 : Blo 1528461 11029709 := bstep (se 3 (by rfl) ⟨2068070, by rfl⟩ : syracuseStep 11029709 = 4136141) B4136141
theorem B1633655 : Blo 1528461 1633655 := bstep (se 1 (by rfl) ⟨1225241, by rfl⟩ : syracuseStep 1633655 = 2450483) B2450483
theorem B37219733 : Blo 1528461 37219733 := bstep (se 6 (by rfl) ⟨872337, by rfl⟩ : syracuseStep 37219733 = 1744675) B1744675
theorem B4353497 : Blo 1528461 4353497 := bstep (se 2 (by rfl) ⟨1632561, by rfl⟩ : syracuseStep 4353497 = 3265123) B3265123
theorem B5164505 : Blo 1528461 5164505 := bstep (se 2 (by rfl) ⟨1936689, by rfl⟩ : syracuseStep 5164505 = 3873379) B3873379
theorem B2903539 : Blo 1528461 2903539 := bstep (se 1 (by rfl) ⟨2177654, by rfl⟩ : syracuseStep 2903539 = 4355309) B4355309
theorem B5303897 : Blo 1528461 5303897 := bstep (se 2 (by rfl) ⟨1988961, by rfl⟩ : syracuseStep 5303897 = 3977923) B3977923
theorem B3100289 : Blo 1528461 3100289 := bstep (se 2 (by rfl) ⟨1162608, by rfl⟩ : syracuseStep 3100289 = 2325217) B2325217
theorem B6205187 : Blo 1528461 6205187 := bstep (se 1 (by rfl) ⟨4653890, by rfl⟩ : syracuseStep 6205187 = 9307781) B9307781
theorem B4034393 : Blo 1528461 4034393 := bstep (se 2 (by rfl) ⟨1512897, by rfl⟩ : syracuseStep 4034393 = 3025795) B3025795
theorem B11611997 : Blo 1528461 11611997 := bstep (se 3 (by rfl) ⟨2177249, by rfl⟩ : syracuseStep 11611997 = 4354499) B4354499
theorem B2903987 : Blo 1528461 2903987 := bstep (se 1 (by rfl) ⟨2177990, by rfl⟩ : syracuseStep 2903987 = 4355981) B4355981
theorem B2904025 : Blo 1528461 2904025 := bstep (se 2 (by rfl) ⟨1089009, by rfl⟩ : syracuseStep 2904025 = 2178019) B2178019
theorem B6975505 : Blo 1528461 6975505 := bstep (se 2 (by rfl) ⟨2615814, by rfl⟩ : syracuseStep 6975505 = 5231629) B5231629
theorem B27889757 : Blo 1528461 27889757 := bstep (se 3 (by rfl) ⟨5229329, by rfl⟩ : syracuseStep 27889757 = 10458659) B10458659
theorem B3674263 : Blo 1528461 3674263 := bstep (se 1 (by rfl) ⟨2755697, by rfl⟩ : syracuseStep 3674263 = 5511395) B5511395
theorem B5165207 : Blo 1528461 5165207 := bstep (se 1 (by rfl) ⟨3873905, by rfl⟩ : syracuseStep 5165207 = 7747811) B7747811
theorem B3870899 : Blo 1528461 3870899 := bstep (se 1 (by rfl) ⟨2903174, by rfl⟩ : syracuseStep 3870899 = 5806349) B5806349
theorem B3723457 : Blo 1528461 3723457 := bstep (se 2 (by rfl) ⟨1396296, by rfl⟩ : syracuseStep 3723457 = 2792593) B2792593
theorem B6197465 : Blo 1528461 6197465 := bstep (se 2 (by rfl) ⟨2324049, by rfl⟩ : syracuseStep 6197465 = 4648099) B4648099
theorem B7852249 : Blo 1528461 7852249 := bstep (se 2 (by rfl) ⟨2944593, by rfl⟩ : syracuseStep 7852249 = 5889187) B5889187
theorem B7745867 : Blo 1528461 7745867 := bstep (se 1 (by rfl) ⟨5809400, by rfl⟩ : syracuseStep 7745867 = 11618801) B11618801
theorem B5804419 : Blo 1528461 5804419 := bstep (se 1 (by rfl) ⟨4353314, by rfl⟩ : syracuseStep 5804419 = 8706629) B8706629
theorem B2904473 : Blo 1528461 2904473 := bstep (se 2 (by rfl) ⟨1089177, by rfl⟩ : syracuseStep 2904473 = 2178355) B2178355
theorem B5509549 : Blo 1528461 5509549 := bstep (se 3 (by rfl) ⟨1033040, by rfl⟩ : syracuseStep 5509549 = 2066081) B2066081
theorem B5231179 : Blo 1528461 5231179 := bstep (se 1 (by rfl) ⟨3923384, by rfl⟩ : syracuseStep 5231179 = 7846769) B7846769
theorem B1528471 : Blo 1528461 1528471 := bstep (se 1 (by rfl) ⟨1146353, by rfl⟩ : syracuseStep 1528471 = 2292707) B2292707
theorem B1528491 : Blo 1528461 1528491 := bstep (se 1 (by rfl) ⟨1146368, by rfl⟩ : syracuseStep 1528491 = 2292737) B2292737
theorem B5804723 : Blo 1528461 5804723 := bstep (se 1 (by rfl) ⟨4353542, by rfl⟩ : syracuseStep 5804723 = 8707085) B8707085
theorem B1528503 : Blo 1528461 1528503 := bstep (se 1 (by rfl) ⟨1146377, by rfl⟩ : syracuseStep 1528503 = 2292755) B2292755
theorem B1528523 : Blo 1528461 1528523 := bstep (se 1 (by rfl) ⟨1146392, by rfl⟩ : syracuseStep 1528523 = 2292785) B2292785
theorem B3871435 : Blo 1528461 3871435 := bstep (se 1 (by rfl) ⟨2903576, by rfl⟩ : syracuseStep 3871435 = 5807153) B5807153
theorem B1528535 : Blo 1528461 1528535 := bstep (se 1 (by rfl) ⟨1146401, by rfl⟩ : syracuseStep 1528535 = 2292803) B2292803
theorem B1528555 : Blo 1528461 1528555 := bstep (se 1 (by rfl) ⟨1146416, by rfl⟩ : syracuseStep 1528555 = 2292833) B2292833
theorem B1528567 : Blo 1528461 1528567 := bstep (se 1 (by rfl) ⟨1146425, by rfl⟩ : syracuseStep 1528567 = 2292851) B2292851
theorem B1528587 : Blo 1528461 1528587 := bstep (se 1 (by rfl) ⟨1146440, by rfl⟩ : syracuseStep 1528587 = 2292881) B2292881
theorem B1528599 : Blo 1528461 1528599 := bstep (se 1 (by rfl) ⟨1146449, by rfl⟩ : syracuseStep 1528599 = 2292899) B2292899
theorem B1528619 : Blo 1528461 1528619 := bstep (se 1 (by rfl) ⟨1146464, by rfl⟩ : syracuseStep 1528619 = 2292929) B2292929
theorem B1528631 : Blo 1528461 1528631 := bstep (se 1 (by rfl) ⟨1146473, by rfl⟩ : syracuseStep 1528631 = 2292947) B2292947
theorem B1528651 : Blo 1528461 1528651 := bstep (se 1 (by rfl) ⟨1146488, by rfl⟩ : syracuseStep 1528651 = 2292977) B2292977
theorem B1528663 : Blo 1528461 1528663 := bstep (se 1 (by rfl) ⟨1146497, by rfl⟩ : syracuseStep 1528663 = 2292995) B2292995
theorem B3871577 : Blo 1528461 3871577 := bstep (se 2 (by rfl) ⟨1451841, by rfl⟩ : syracuseStep 3871577 = 2903683) B2903683
theorem B7344989 : Blo 1528461 7344989 := bstep (se 3 (by rfl) ⟨1377185, by rfl⟩ : syracuseStep 7344989 = 2754371) B2754371
theorem B1528683 : Blo 1528461 1528683 := bstep (se 1 (by rfl) ⟨1146512, by rfl⟩ : syracuseStep 1528683 = 2293025) B2293025
theorem B1528695 : Blo 1528461 1528695 := bstep (se 1 (by rfl) ⟨1146521, by rfl⟩ : syracuseStep 1528695 = 2293043) B2293043
theorem B1528715 : Blo 1528461 1528715 := bstep (se 1 (by rfl) ⟨1146536, by rfl⟩ : syracuseStep 1528715 = 2293073) B2293073
theorem B1528727 : Blo 1528461 1528727 := bstep (se 1 (by rfl) ⟨1146545, by rfl⟩ : syracuseStep 1528727 = 2293091) B2293091
theorem B1528747 : Blo 1528461 1528747 := bstep (se 1 (by rfl) ⟨1146560, by rfl⟩ : syracuseStep 1528747 = 2293121) B2293121
theorem B1528759 : Blo 1528461 1528759 := bstep (se 1 (by rfl) ⟨1146569, by rfl⟩ : syracuseStep 1528759 = 2293139) B2293139
theorem B1528779 : Blo 1528461 1528779 := bstep (se 1 (by rfl) ⟨1146584, by rfl⟩ : syracuseStep 1528779 = 2293169) B2293169
theorem B1528791 : Blo 1528461 1528791 := bstep (se 1 (by rfl) ⟨1146593, by rfl⟩ : syracuseStep 1528791 = 2293187) B2293187
theorem B1528811 : Blo 1528461 1528811 := bstep (se 1 (by rfl) ⟨1146608, by rfl⟩ : syracuseStep 1528811 = 2293217) B2293217
theorem B1528823 : Blo 1528461 1528823 := bstep (se 1 (by rfl) ⟨1146617, by rfl⟩ : syracuseStep 1528823 = 2293235) B2293235
theorem B1528843 : Blo 1528461 1528843 := bstep (se 1 (by rfl) ⟨1146632, by rfl⟩ : syracuseStep 1528843 = 2293265) B2293265
theorem B1528855 : Blo 1528461 1528855 := bstep (se 1 (by rfl) ⟨1146641, by rfl⟩ : syracuseStep 1528855 = 2293283) B2293283
theorem B1528875 : Blo 1528461 1528875 := bstep (se 1 (by rfl) ⟨1146656, by rfl⟩ : syracuseStep 1528875 = 2293313) B2293313
theorem B1528887 : Blo 1528461 1528887 := bstep (se 1 (by rfl) ⟨1146665, by rfl⟩ : syracuseStep 1528887 = 2293331) B2293331
theorem B3265601 : Blo 1528461 3265601 := bstep (se 2 (by rfl) ⟨1224600, by rfl⟩ : syracuseStep 3265601 = 2449201) B2449201
theorem B4355137 : Blo 1528461 4355137 := bstep (se 2 (by rfl) ⟨1633176, by rfl⟩ : syracuseStep 4355137 = 3266353) B3266353
theorem B6534209 : Blo 1528461 6534209 := bstep (se 2 (by rfl) ⟨2450328, by rfl⟩ : syracuseStep 6534209 = 4900657) B4900657
theorem B1528907 : Blo 1528461 1528907 := bstep (se 1 (by rfl) ⟨1146680, by rfl⟩ : syracuseStep 1528907 = 2293361) B2293361
theorem B9933899 : Blo 1528461 9933899 := bstep (se 1 (by rfl) ⟨7450424, by rfl⟩ : syracuseStep 9933899 = 14900849) B14900849
theorem B1528919 : Blo 1528461 1528919 := bstep (se 1 (by rfl) ⟨1146689, by rfl⟩ : syracuseStep 1528919 = 2293379) B2293379
theorem B9802853 : Blo 1528461 9802853 := bstep (se 4 (by rfl) ⟨919017, by rfl⟩ : syracuseStep 9802853 = 1838035) B1838035
theorem B1528939 : Blo 1528461 1528939 := bstep (se 1 (by rfl) ⟨1146704, by rfl⟩ : syracuseStep 1528939 = 2293409) B2293409
theorem B1528951 : Blo 1528461 1528951 := bstep (se 1 (by rfl) ⟨1146713, by rfl⟩ : syracuseStep 1528951 = 2293427) B2293427
theorem B2905217 : Blo 1528461 2905217 := bstep (se 2 (by rfl) ⟨1089456, by rfl⟩ : syracuseStep 2905217 = 2178913) B2178913
theorem B1528971 : Blo 1528461 1528971 := bstep (se 1 (by rfl) ⟨1146728, by rfl⟩ : syracuseStep 1528971 = 2293457) B2293457
theorem B1528983 : Blo 1528461 1528983 := bstep (se 1 (by rfl) ⟨1146737, by rfl⟩ : syracuseStep 1528983 = 2293475) B2293475
theorem B3265687 : Blo 1528461 3265687 := bstep (se 1 (by rfl) ⟨2449265, by rfl⟩ : syracuseStep 3265687 = 4898531) B4898531
theorem B1529003 : Blo 1528461 1529003 := bstep (se 1 (by rfl) ⟨1146752, by rfl⟩ : syracuseStep 1529003 = 2293505) B2293505
theorem B1529015 : Blo 1528461 1529015 := bstep (se 1 (by rfl) ⟨1146761, by rfl⟩ : syracuseStep 1529015 = 2293523) B2293523
theorem B1529035 : Blo 1528461 1529035 := bstep (se 1 (by rfl) ⟨1146776, by rfl⟩ : syracuseStep 1529035 = 2293553) B2293553
theorem B1529047 : Blo 1528461 1529047 := bstep (se 1 (by rfl) ⟨1146785, by rfl⟩ : syracuseStep 1529047 = 2293571) B2293571
theorem B1529067 : Blo 1528461 1529067 := bstep (se 1 (by rfl) ⟨1146800, by rfl⟩ : syracuseStep 1529067 = 2293601) B2293601
theorem B1529079 : Blo 1528461 1529079 := bstep (se 1 (by rfl) ⟨1146809, by rfl⟩ : syracuseStep 1529079 = 2293619) B2293619
theorem B1529099 : Blo 1528461 1529099 := bstep (se 1 (by rfl) ⟨1146824, by rfl⟩ : syracuseStep 1529099 = 2293649) B2293649
theorem B1529111 : Blo 1528461 1529111 := bstep (se 1 (by rfl) ⟨1146833, by rfl⟩ : syracuseStep 1529111 = 2293667) B2293667
theorem B1529131 : Blo 1528461 1529131 := bstep (se 1 (by rfl) ⟨1146848, by rfl⟩ : syracuseStep 1529131 = 2293697) B2293697
theorem B1529143 : Blo 1528461 1529143 := bstep (se 1 (by rfl) ⟨1146857, by rfl⟩ : syracuseStep 1529143 = 2293715) B2293715
theorem B5805377 : Blo 1528461 5805377 := bstep (se 2 (by rfl) ⟨2177016, by rfl⟩ : syracuseStep 5805377 = 4354033) B4354033
theorem B1529163 : Blo 1528461 1529163 := bstep (se 1 (by rfl) ⟨1146872, by rfl⟩ : syracuseStep 1529163 = 2293745) B2293745
theorem B1529175 : Blo 1528461 1529175 := bstep (se 1 (by rfl) ⟨1146881, by rfl⟩ : syracuseStep 1529175 = 2293763) B2293763
theorem B1529195 : Blo 1528461 1529195 := bstep (se 1 (by rfl) ⟨1146896, by rfl⟩ : syracuseStep 1529195 = 2293793) B2293793
theorem B1529207 : Blo 1528461 1529207 := bstep (se 1 (by rfl) ⟨1146905, by rfl⟩ : syracuseStep 1529207 = 2293811) B2293811
theorem B1529227 : Blo 1528461 1529227 := bstep (se 1 (by rfl) ⟨1146920, by rfl⟩ : syracuseStep 1529227 = 2293841) B2293841
theorem B2905483 : Blo 1528461 2905483 := bstep (se 1 (by rfl) ⟨2179112, by rfl⟩ : syracuseStep 2905483 = 4358225) B4358225
theorem B1529239 : Blo 1528461 1529239 := bstep (se 1 (by rfl) ⟨1146929, by rfl⟩ : syracuseStep 1529239 = 2293859) B2293859
theorem B1529259 : Blo 1528461 1529259 := bstep (se 1 (by rfl) ⟨1146944, by rfl⟩ : syracuseStep 1529259 = 2293889) B2293889
theorem B1529271 : Blo 1528461 1529271 := bstep (se 1 (by rfl) ⟨1146953, by rfl⟩ : syracuseStep 1529271 = 2293907) B2293907
theorem B3487169 : Blo 1528461 3487169 := bstep (se 2 (by rfl) ⟨1307688, by rfl⟩ : syracuseStep 3487169 = 2615377) B2615377
theorem B1529291 : Blo 1528461 1529291 := bstep (se 1 (by rfl) ⟨1146968, by rfl⟩ : syracuseStep 1529291 = 2293937) B2293937
theorem B1529303 : Blo 1528461 1529303 := bstep (se 1 (by rfl) ⟨1146977, by rfl⟩ : syracuseStep 1529303 = 2293955) B2293955
theorem B1529323 : Blo 1528461 1529323 := bstep (se 1 (by rfl) ⟨1146992, by rfl⟩ : syracuseStep 1529323 = 2293985) B2293985
theorem B1529335 : Blo 1528461 1529335 := bstep (se 1 (by rfl) ⟨1147001, by rfl⟩ : syracuseStep 1529335 = 2294003) B2294003
theorem B1529355 : Blo 1528461 1529355 := bstep (se 1 (by rfl) ⟨1147016, by rfl⟩ : syracuseStep 1529355 = 2294033) B2294033
theorem B1529367 : Blo 1528461 1529367 := bstep (se 1 (by rfl) ⟨1147025, by rfl⟩ : syracuseStep 1529367 = 2294051) B2294051
theorem B1529387 : Blo 1528461 1529387 := bstep (se 1 (by rfl) ⟨1147040, by rfl⟩ : syracuseStep 1529387 = 2294081) B2294081
theorem B1529399 : Blo 1528461 1529399 := bstep (se 1 (by rfl) ⟨1147049, by rfl⟩ : syracuseStep 1529399 = 2294099) B2294099
theorem B1529419 : Blo 1528461 1529419 := bstep (se 1 (by rfl) ⟨1147064, by rfl⟩ : syracuseStep 1529419 = 2294129) B2294129
theorem B1529431 : Blo 1528461 1529431 := bstep (se 1 (by rfl) ⟨1147073, by rfl⟩ : syracuseStep 1529431 = 2294147) B2294147
theorem B6198877 : Blo 1528461 6198877 := bstep (se 3 (by rfl) ⟨1162289, by rfl⟩ : syracuseStep 6198877 = 2324579) B2324579
theorem B1529451 : Blo 1528461 1529451 := bstep (se 1 (by rfl) ⟨1147088, by rfl⟩ : syracuseStep 1529451 = 2294177) B2294177
theorem B1529463 : Blo 1528461 1529463 := bstep (se 1 (by rfl) ⟨1147097, by rfl⟩ : syracuseStep 1529463 = 2294195) B2294195
theorem B1529483 : Blo 1528461 1529483 := bstep (se 1 (by rfl) ⟨1147112, by rfl⟩ : syracuseStep 1529483 = 2294225) B2294225
theorem B1529495 : Blo 1528461 1529495 := bstep (se 1 (by rfl) ⟨1147121, by rfl⟩ : syracuseStep 1529495 = 2294243) B2294243
theorem B3872407 : Blo 1528461 3872407 := bstep (se 1 (by rfl) ⟨2904305, by rfl⟩ : syracuseStep 3872407 = 5808611) B5808611
theorem B1529515 : Blo 1528461 1529515 := bstep (se 1 (by rfl) ⟨1147136, by rfl⟩ : syracuseStep 1529515 = 2294273) B2294273
theorem B1529527 : Blo 1528461 1529527 := bstep (se 1 (by rfl) ⟨1147145, by rfl⟩ : syracuseStep 1529527 = 2294291) B2294291
theorem B1529547 : Blo 1528461 1529547 := bstep (se 1 (by rfl) ⟨1147160, by rfl⟩ : syracuseStep 1529547 = 2294321) B2294321
theorem B1529559 : Blo 1528461 1529559 := bstep (se 1 (by rfl) ⟨1147169, by rfl⟩ : syracuseStep 1529559 = 2294339) B2294339
theorem B6534877 : Blo 1528461 6534877 := bstep (se 3 (by rfl) ⟨1225289, by rfl⟩ : syracuseStep 6534877 = 2450579) B2450579
theorem B1529579 : Blo 1528461 1529579 := bstep (se 1 (by rfl) ⟨1147184, by rfl⟩ : syracuseStep 1529579 = 2294369) B2294369
theorem B1529591 : Blo 1528461 1529591 := bstep (se 1 (by rfl) ⟨1147193, by rfl⟩ : syracuseStep 1529591 = 2294387) B2294387
theorem B1529611 : Blo 1528461 1529611 := bstep (se 1 (by rfl) ⟨1147208, by rfl⟩ : syracuseStep 1529611 = 2294417) B2294417
theorem B1529623 : Blo 1528461 1529623 := bstep (se 1 (by rfl) ⟨1147217, by rfl⟩ : syracuseStep 1529623 = 2294435) B2294435
theorem B1529643 : Blo 1528461 1529643 := bstep (se 1 (by rfl) ⟨1147232, by rfl⟩ : syracuseStep 1529643 = 2294465) B2294465
theorem B3675955 : Blo 1528461 3675955 := bstep (se 1 (by rfl) ⟨2756966, by rfl⟩ : syracuseStep 3675955 = 5513933) B5513933
theorem B1529655 : Blo 1528461 1529655 := bstep (se 1 (by rfl) ⟨1147241, by rfl⟩ : syracuseStep 1529655 = 2294483) B2294483
theorem B1529675 : Blo 1528461 1529675 := bstep (se 1 (by rfl) ⟨1147256, by rfl⟩ : syracuseStep 1529675 = 2294513) B2294513
theorem B1529687 : Blo 1528461 1529687 := bstep (se 1 (by rfl) ⟨1147265, by rfl⟩ : syracuseStep 1529687 = 2294531) B2294531
theorem B26130275 : Blo 1528461 26130275 := bstep (se 1 (by rfl) ⟨19597706, by rfl⟩ : syracuseStep 26130275 = 39195413) B39195413
theorem B1529707 : Blo 1528461 1529707 := bstep (se 1 (by rfl) ⟨1147280, by rfl⟩ : syracuseStep 1529707 = 2294561) B2294561
theorem B1529719 : Blo 1528461 1529719 := bstep (se 1 (by rfl) ⟨1147289, by rfl⟩ : syracuseStep 1529719 = 2294579) B2294579
theorem B17430389 : Blo 1528461 17430389 := bstep (se 5 (by rfl) ⟨817049, by rfl⟩ : syracuseStep 17430389 = 1634099) B1634099
theorem B1529739 : Blo 1528461 1529739 := bstep (se 1 (by rfl) ⟨1147304, by rfl⟩ : syracuseStep 1529739 = 2294609) B2294609
theorem B1529751 : Blo 1528461 1529751 := bstep (se 1 (by rfl) ⟨1147313, by rfl⟩ : syracuseStep 1529751 = 2294627) B2294627
theorem B1529771 : Blo 1528461 1529771 := bstep (se 1 (by rfl) ⟨1147328, by rfl⟩ : syracuseStep 1529771 = 2294657) B2294657
theorem B5158835 : Blo 1528461 5158835 := bstep (se 1 (by rfl) ⟨3869126, by rfl⟩ : syracuseStep 5158835 = 7738253) B7738253
theorem B41875379 : Blo 1528461 41875379 := bstep (se 1 (by rfl) ⟨31406534, by rfl⟩ : syracuseStep 41875379 = 62813069) B62813069
theorem B1529783 : Blo 1528461 1529783 := bstep (se 1 (by rfl) ⟨1147337, by rfl⟩ : syracuseStep 1529783 = 2294675) B2294675
theorem B3266507 : Blo 1528461 3266507 := bstep (se 1 (by rfl) ⟨2449880, by rfl⟩ : syracuseStep 3266507 = 4899761) B4899761
theorem B1529803 : Blo 1528461 1529803 := bstep (se 1 (by rfl) ⟨1147352, by rfl⟩ : syracuseStep 1529803 = 2294705) B2294705
theorem B1529815 : Blo 1528461 1529815 := bstep (se 1 (by rfl) ⟨1147361, by rfl⟩ : syracuseStep 1529815 = 2294723) B2294723
theorem B1529835 : Blo 1528461 1529835 := bstep (se 1 (by rfl) ⟨1147376, by rfl⟩ : syracuseStep 1529835 = 2294753) B2294753
theorem B1529847 : Blo 1528461 1529847 := bstep (se 1 (by rfl) ⟨1147385, by rfl⟩ : syracuseStep 1529847 = 2294771) B2294771
theorem B1529867 : Blo 1528461 1529867 := bstep (se 1 (by rfl) ⟨1147400, by rfl⟩ : syracuseStep 1529867 = 2294801) B2294801
theorem B1529879 : Blo 1528461 1529879 := bstep (se 1 (by rfl) ⟨1147409, by rfl⟩ : syracuseStep 1529879 = 2294819) B2294819
theorem B1529899 : Blo 1528461 1529899 := bstep (se 1 (by rfl) ⟨1147424, by rfl⟩ : syracuseStep 1529899 = 2294849) B2294849
theorem B1529911 : Blo 1528461 1529911 := bstep (se 1 (by rfl) ⟨1147433, by rfl⟩ : syracuseStep 1529911 = 2294867) B2294867
theorem B7747649 : Blo 1528461 7747649 := bstep (se 2 (by rfl) ⟨2905368, by rfl⟩ : syracuseStep 7747649 = 5810737) B5810737
theorem B77477957 : Blo 1528461 77477957 := bstep (se 4 (by rfl) ⟨7263558, by rfl⟩ : syracuseStep 77477957 = 14527117) B14527117
theorem B1529931 : Blo 1528461 1529931 := bstep (se 1 (by rfl) ⟨1147448, by rfl⟩ : syracuseStep 1529931 = 2294897) B2294897
theorem B3872843 : Blo 1528461 3872843 := bstep (se 1 (by rfl) ⟨2904632, by rfl⟩ : syracuseStep 3872843 = 5809265) B5809265
theorem B1529943 : Blo 1528461 1529943 := bstep (se 1 (by rfl) ⟨1147457, by rfl⟩ : syracuseStep 1529943 = 2294915) B2294915
theorem B2177113 : Blo 1528461 2177113 := bstep (se 2 (by rfl) ⟨816417, by rfl⟩ : syracuseStep 2177113 = 1632835) B1632835
theorem B1529963 : Blo 1528461 1529963 := bstep (se 1 (by rfl) ⟨1147472, by rfl⟩ : syracuseStep 1529963 = 2294945) B2294945
theorem B1529975 : Blo 1528461 1529975 := bstep (se 1 (by rfl) ⟨1147481, by rfl⟩ : syracuseStep 1529975 = 2294963) B2294963
theorem B1529995 : Blo 1528461 1529995 := bstep (se 1 (by rfl) ⟨1147496, by rfl⟩ : syracuseStep 1529995 = 2294993) B2294993
theorem B1530007 : Blo 1528461 1530007 := bstep (se 1 (by rfl) ⟨1147505, by rfl⟩ : syracuseStep 1530007 = 2295011) B2295011
theorem B1530027 : Blo 1528461 1530027 := bstep (se 1 (by rfl) ⟨1147520, by rfl⟩ : syracuseStep 1530027 = 2295041) B2295041
theorem B1530039 : Blo 1528461 1530039 := bstep (se 1 (by rfl) ⟨1147529, by rfl⟩ : syracuseStep 1530039 = 2295059) B2295059
theorem B5159105 : Blo 1528461 5159105 := bstep (se 2 (by rfl) ⟨1934664, by rfl⟩ : syracuseStep 5159105 = 3869329) B3869329
theorem B2177227 : Blo 1528461 2177227 := bstep (se 1 (by rfl) ⟨1632920, by rfl⟩ : syracuseStep 2177227 = 3265841) B3265841
theorem B1530059 : Blo 1528461 1530059 := bstep (se 1 (by rfl) ⟨1147544, by rfl⟩ : syracuseStep 1530059 = 2295089) B2295089
theorem B13072589 : Blo 1528461 13072589 := bstep (se 3 (by rfl) ⟨2451110, by rfl⟩ : syracuseStep 13072589 = 4902221) B4902221
theorem B2324695 : Blo 1528461 2324695 := bstep (se 1 (by rfl) ⟨1743521, by rfl⟩ : syracuseStep 2324695 = 3487043) B3487043
theorem B1530071 : Blo 1528461 1530071 := bstep (se 1 (by rfl) ⟨1147553, by rfl⟩ : syracuseStep 1530071 = 2295107) B2295107
theorem B1530091 : Blo 1528461 1530091 := bstep (se 1 (by rfl) ⟨1147568, by rfl⟩ : syracuseStep 1530091 = 2295137) B2295137
theorem B1530103 : Blo 1528461 1530103 := bstep (se 1 (by rfl) ⟨1147577, by rfl⟩ : syracuseStep 1530103 = 2295155) B2295155
theorem B1530123 : Blo 1528461 1530123 := bstep (se 1 (by rfl) ⟨1147592, by rfl⟩ : syracuseStep 1530123 = 2295185) B2295185
theorem B1530135 : Blo 1528461 1530135 := bstep (se 1 (by rfl) ⟨1147601, by rfl⟩ : syracuseStep 1530135 = 2295203) B2295203
theorem B1530155 : Blo 1528461 1530155 := bstep (se 1 (by rfl) ⟨1147616, by rfl⟩ : syracuseStep 1530155 = 2295233) B2295233
theorem B6535475 : Blo 1528461 6535475 := bstep (se 1 (by rfl) ⟨4901606, by rfl⟩ : syracuseStep 6535475 = 9803213) B9803213
theorem B1530167 : Blo 1528461 1530167 := bstep (se 1 (by rfl) ⟨1147625, by rfl⟩ : syracuseStep 1530167 = 2295251) B2295251
theorem B1530187 : Blo 1528461 1530187 := bstep (se 1 (by rfl) ⟨1147640, by rfl⟩ : syracuseStep 1530187 = 2295281) B2295281
theorem B1530199 : Blo 1528461 1530199 := bstep (se 1 (by rfl) ⟨1147649, by rfl⟩ : syracuseStep 1530199 = 2295299) B2295299
theorem B1530219 : Blo 1528461 1530219 := bstep (se 1 (by rfl) ⟨1147664, by rfl⟩ : syracuseStep 1530219 = 2295329) B2295329
theorem B1530231 : Blo 1528461 1530231 := bstep (se 1 (by rfl) ⟨1147673, by rfl⟩ : syracuseStep 1530231 = 2295347) B2295347
theorem B8714627 : Blo 1528461 8714627 := bstep (se 1 (by rfl) ⟨6535970, by rfl⟩ : syracuseStep 8714627 = 13071941) B13071941
theorem B1530251 : Blo 1528461 1530251 := bstep (se 1 (by rfl) ⟨1147688, by rfl⟩ : syracuseStep 1530251 = 2295377) B2295377
theorem B1530263 : Blo 1528461 1530263 := bstep (se 1 (by rfl) ⟨1147697, by rfl⟩ : syracuseStep 1530263 = 2295395) B2295395
theorem B1530283 : Blo 1528461 1530283 := bstep (se 1 (by rfl) ⟨1147712, by rfl⟩ : syracuseStep 1530283 = 2295425) B2295425
theorem B1530295 : Blo 1528461 1530295 := bstep (se 1 (by rfl) ⟨1147721, by rfl⟩ : syracuseStep 1530295 = 2295443) B2295443
theorem B3873217 : Blo 1528461 3873217 := bstep (se 2 (by rfl) ⟨1452456, by rfl⟩ : syracuseStep 3873217 = 2904913) B2904913
theorem B1530315 : Blo 1528461 1530315 := bstep (se 1 (by rfl) ⟨1147736, by rfl⟩ : syracuseStep 1530315 = 2295473) B2295473
theorem B1530327 : Blo 1528461 1530327 := bstep (se 1 (by rfl) ⟨1147745, by rfl⟩ : syracuseStep 1530327 = 2295491) B2295491
theorem B1530347 : Blo 1528461 1530347 := bstep (se 1 (by rfl) ⟨1147760, by rfl⟩ : syracuseStep 1530347 = 2295521) B2295521
theorem B1530359 : Blo 1528461 1530359 := bstep (se 1 (by rfl) ⟨1147769, by rfl⟩ : syracuseStep 1530359 = 2295539) B2295539
theorem B3439115 : Blo 1528461 3439115 := bstep (se 1 (by rfl) ⟨2579336, by rfl⟩ : syracuseStep 3439115 = 5158673) B5158673
theorem B1530379 : Blo 1528461 1530379 := bstep (se 1 (by rfl) ⟨1147784, by rfl⟩ : syracuseStep 1530379 = 2295569) B2295569
theorem B1530391 : Blo 1528461 1530391 := bstep (se 1 (by rfl) ⟨1147793, by rfl⟩ : syracuseStep 1530391 = 2295587) B2295587
theorem B1530411 : Blo 1528461 1530411 := bstep (se 1 (by rfl) ⟨1147808, by rfl⟩ : syracuseStep 1530411 = 2295617) B2295617
theorem B5806637 : Blo 1528461 5806637 := bstep (se 3 (by rfl) ⟨1088744, by rfl⟩ : syracuseStep 5806637 = 2177489) B2177489
theorem B1530423 : Blo 1528461 1530423 := bstep (se 1 (by rfl) ⟨1147817, by rfl⟩ : syracuseStep 1530423 = 2295635) B2295635
theorem B3439169 : Blo 1528461 3439169 := bstep (se 2 (by rfl) ⟨1289688, by rfl⟩ : syracuseStep 3439169 = 2579377) B2579377
theorem B4414027 : Blo 1528461 4414027 := bstep (se 1 (by rfl) ⟨3310520, by rfl⟩ : syracuseStep 4414027 = 6621041) B6621041
theorem B5806667 : Blo 1528461 5806667 := bstep (se 1 (by rfl) ⟨4355000, by rfl⟩ : syracuseStep 5806667 = 8710001) B8710001
theorem B1530443 : Blo 1528461 1530443 := bstep (se 1 (by rfl) ⟨1147832, by rfl⟩ : syracuseStep 1530443 = 2295665) B2295665
theorem B1530455 : Blo 1528461 1530455 := bstep (se 1 (by rfl) ⟨1147841, by rfl⟩ : syracuseStep 1530455 = 2295683) B2295683
theorem B7740035 : Blo 1528461 7740035 := bstep (se 1 (by rfl) ⟨5805026, by rfl⟩ : syracuseStep 7740035 = 11610053) B11610053
theorem B44718797 : Blo 1528461 44718797 := bstep (se 3 (by rfl) ⟨8384774, by rfl⟩ : syracuseStep 44718797 = 16769549) B16769549
theorem B5159645 : Blo 1528461 5159645 := bstep (se 3 (by rfl) ⟨967433, by rfl⟩ : syracuseStep 5159645 = 1934867) B1934867
theorem B5511959 : Blo 1528461 5511959 := bstep (se 1 (by rfl) ⟨4133969, by rfl⟩ : syracuseStep 5511959 = 8267939) B8267939
theorem B3439385 : Blo 1528461 3439385 := bstep (se 2 (by rfl) ⟨1289769, by rfl⟩ : syracuseStep 3439385 = 2579539) B2579539
theorem B3922739 : Blo 1528461 3922739 := bstep (se 1 (by rfl) ⟨2942054, by rfl⟩ : syracuseStep 3922739 = 5884109) B5884109
theorem B3439475 : Blo 1528461 3439475 := bstep (se 1 (by rfl) ⟨2579606, by rfl⟩ : syracuseStep 3439475 = 5159213) B5159213
theorem B3439511 : Blo 1528461 3439511 := bstep (se 1 (by rfl) ⟨2579633, by rfl⟩ : syracuseStep 3439511 = 5159267) B5159267
theorem B3267481 : Blo 1528461 3267481 := bstep (se 2 (by rfl) ⟨1225305, by rfl⟩ : syracuseStep 3267481 = 2450611) B2450611
theorem B2292695 : Blo 1528461 2292695 := bstep (se 1 (by rfl) ⟨1719521, by rfl⟩ : syracuseStep 2292695 = 3439043) B3439043
theorem B2448343 : Blo 1528461 2448343 := bstep (se 1 (by rfl) ⟨1836257, by rfl⟩ : syracuseStep 2448343 = 3672515) B3672515
theorem B2448407 : Blo 1528461 2448407 := bstep (se 1 (by rfl) ⟨1836305, by rfl⟩ : syracuseStep 2448407 = 3672611) B3672611
theorem B3873815 : Blo 1528461 3873815 := bstep (se 1 (by rfl) ⟨2905361, by rfl⟩ : syracuseStep 3873815 = 5810723) B5810723
theorem B2292761 : Blo 1528461 2292761 := bstep (se 2 (by rfl) ⟨859785, by rfl⟩ : syracuseStep 2292761 = 1719571) B1719571
theorem B3439691 : Blo 1528461 3439691 := bstep (se 1 (by rfl) ⟨2579768, by rfl⟩ : syracuseStep 3439691 = 5159537) B5159537
theorem B18603101 : Blo 1528461 18603101 := bstep (se 3 (by rfl) ⟨3488081, by rfl⟩ : syracuseStep 18603101 = 6976163) B6976163
theorem B3439745 : Blo 1528461 3439745 := bstep (se 2 (by rfl) ⟨1289904, by rfl⟩ : syracuseStep 3439745 = 2579809) B2579809
theorem B2292875 : Blo 1528461 2292875 := bstep (se 1 (by rfl) ⟨1719656, by rfl⟩ : syracuseStep 2292875 = 3439313) B3439313
theorem B2292887 : Blo 1528461 2292887 := bstep (se 1 (by rfl) ⟨1719665, by rfl⟩ : syracuseStep 2292887 = 3439331) B3439331
theorem B2448535 : Blo 1528461 2448535 := bstep (se 1 (by rfl) ⟨1836401, by rfl⟩ : syracuseStep 2448535 = 3672803) B3672803
theorem B2292953 : Blo 1528461 2292953 := bstep (se 2 (by rfl) ⟨859857, by rfl⟩ : syracuseStep 2292953 = 1719715) B1719715
theorem B5807321 : Blo 1528461 5807321 := bstep (se 2 (by rfl) ⟨2177745, by rfl⟩ : syracuseStep 5807321 = 4355491) B4355491
theorem B2579735 : Blo 1528461 2579735 := bstep (se 1 (by rfl) ⟨1934801, by rfl⟩ : syracuseStep 2579735 = 3869603) B3869603
theorem B1719607 : Blo 1528461 1719607 := bstep (se 1 (by rfl) ⟨1289705, by rfl⟩ : syracuseStep 1719607 = 2579411) B2579411
theorem B2293067 : Blo 1528461 2293067 := bstep (se 1 (by rfl) ⟨1719800, by rfl⟩ : syracuseStep 2293067 = 3439601) B3439601
theorem B2293079 : Blo 1528461 2293079 := bstep (se 1 (by rfl) ⟨1719809, by rfl⟩ : syracuseStep 2293079 = 3439619) B3439619
theorem B3439961 : Blo 1528461 3439961 := bstep (se 2 (by rfl) ⟨1289985, by rfl⟩ : syracuseStep 3439961 = 2579971) B2579971
theorem B3489139 : Blo 1528461 3489139 := bstep (se 1 (by rfl) ⟨2616854, by rfl⟩ : syracuseStep 3489139 = 5233709) B5233709
theorem B2579863 : Blo 1528461 2579863 := bstep (se 1 (by rfl) ⟨1934897, by rfl⟩ : syracuseStep 2579863 = 3869795) B3869795
theorem B2293145 : Blo 1528461 2293145 := bstep (se 2 (by rfl) ⟨859929, by rfl⟩ : syracuseStep 2293145 = 1719859) B1719859
theorem B3440051 : Blo 1528461 3440051 := bstep (se 1 (by rfl) ⟨2580038, by rfl⟩ : syracuseStep 3440051 = 5160077) B5160077
theorem B3440087 : Blo 1528461 3440087 := bstep (se 1 (by rfl) ⟨2580065, by rfl⟩ : syracuseStep 3440087 = 5160131) B5160131
theorem B1719787 : Blo 1528461 1719787 := bstep (se 1 (by rfl) ⟨1289840, by rfl⟩ : syracuseStep 1719787 = 2579681) B2579681
theorem B2293259 : Blo 1528461 2293259 := bstep (se 1 (by rfl) ⟨1719944, by rfl⟩ : syracuseStep 2293259 = 3439889) B3439889
theorem B2178571 : Blo 1528461 2178571 := bstep (se 1 (by rfl) ⟨1633928, by rfl⟩ : syracuseStep 2178571 = 3267857) B3267857
theorem B27893261 : Blo 1528461 27893261 := bstep (se 3 (by rfl) ⟨5229986, by rfl⟩ : syracuseStep 27893261 = 10459973) B10459973
theorem B2293271 : Blo 1528461 2293271 := bstep (se 1 (by rfl) ⟨1719953, by rfl⟩ : syracuseStep 2293271 = 3439907) B3439907
theorem B5807639 : Blo 1528461 5807639 := bstep (se 1 (by rfl) ⟨4355729, by rfl⟩ : syracuseStep 5807639 = 8711459) B8711459
theorem B2448971 : Blo 1528461 2448971 := bstep (se 1 (by rfl) ⟨1836728, by rfl⟩ : syracuseStep 2448971 = 3673457) B3673457
theorem B1719895 : Blo 1528461 1719895 := bstep (se 1 (by rfl) ⟨1289921, by rfl⟩ : syracuseStep 1719895 = 2579843) B2579843
theorem B2293337 : Blo 1528461 2293337 := bstep (se 2 (by rfl) ⟨860001, by rfl⟩ : syracuseStep 2293337 = 1720003) B1720003
theorem B9797213 : Blo 1528461 9797213 := bstep (se 3 (by rfl) ⟨1836977, by rfl⟩ : syracuseStep 9797213 = 3673955) B3673955
theorem B3440267 : Blo 1528461 3440267 := bstep (se 1 (by rfl) ⟨2580200, by rfl⟩ : syracuseStep 3440267 = 5160401) B5160401
theorem B3440321 : Blo 1528461 3440321 := bstep (se 2 (by rfl) ⟨1290120, by rfl⟩ : syracuseStep 3440321 = 2580241) B2580241
theorem B2293451 : Blo 1528461 2293451 := bstep (se 1 (by rfl) ⟨1720088, by rfl⟩ : syracuseStep 2293451 = 3440177) B3440177
theorem B2293463 : Blo 1528461 2293463 := bstep (se 1 (by rfl) ⟨1720097, by rfl⟩ : syracuseStep 2293463 = 3440195) B3440195
theorem B1720075 : Blo 1528461 1720075 := bstep (se 1 (by rfl) ⟨1290056, by rfl⟩ : syracuseStep 1720075 = 2580113) B2580113
theorem B2449163 : Blo 1528461 2449163 := bstep (se 1 (by rfl) ⟨1836872, by rfl⟩ : syracuseStep 2449163 = 3673745) B3673745
theorem B2178839 : Blo 1528461 2178839 := bstep (se 1 (by rfl) ⟨1634129, by rfl⟩ : syracuseStep 2178839 = 3268259) B3268259
theorem B2293529 : Blo 1528461 2293529 := bstep (se 2 (by rfl) ⟨860073, by rfl⟩ : syracuseStep 2293529 = 1720147) B1720147
theorem B5160779 : Blo 1528461 5160779 := bstep (se 1 (by rfl) ⟨3870584, by rfl⟩ : syracuseStep 5160779 = 7741169) B7741169
theorem B1720183 : Blo 1528461 1720183 := bstep (se 1 (by rfl) ⟨1290137, by rfl⟩ : syracuseStep 1720183 = 2580275) B2580275
theorem B11026307 : Blo 1528461 11026307 := bstep (se 1 (by rfl) ⟨8269730, by rfl⟩ : syracuseStep 11026307 = 16539461) B16539461
theorem B2293643 : Blo 1528461 2293643 := bstep (se 1 (by rfl) ⟨1720232, by rfl⟩ : syracuseStep 2293643 = 3440465) B3440465
theorem B2293655 : Blo 1528461 2293655 := bstep (se 1 (by rfl) ⟨1720241, by rfl⟩ : syracuseStep 2293655 = 3440483) B3440483
theorem B3440537 : Blo 1528461 3440537 := bstep (se 2 (by rfl) ⟨1290201, by rfl⟩ : syracuseStep 3440537 = 2580403) B2580403
theorem B2293721 : Blo 1528461 2293721 := bstep (se 2 (by rfl) ⟨860145, by rfl⟩ : syracuseStep 2293721 = 1720291) B1720291
theorem B3440627 : Blo 1528461 3440627 := bstep (se 1 (by rfl) ⟨2580470, by rfl⟩ : syracuseStep 3440627 = 5160941) B5160941
theorem B1720327 : Blo 1528461 1720327 := bstep (se 1 (by rfl) ⟨1290245, by rfl⟩ : syracuseStep 1720327 = 2580491) B2580491
theorem B2293775 : Blo 1528461 2293775 := bstep (se 1 (by rfl) ⟨1720331, by rfl⟩ : syracuseStep 2293775 = 3440663) B3440663
theorem B2293817 : Blo 1528461 2293817 := bstep (se 2 (by rfl) ⟨860181, by rfl⟩ : syracuseStep 2293817 = 1720363) B1720363
theorem B3440699 : Blo 1528461 3440699 := bstep (se 1 (by rfl) ⟨2580524, by rfl⟩ : syracuseStep 3440699 = 5161049) B5161049
theorem B6529085 : Blo 1528461 6529085 := bstep (se 3 (by rfl) ⟨1224203, by rfl⟩ : syracuseStep 6529085 = 2448407) B2448407
theorem B2580599 : Blo 1528461 2580599 := bstep (se 1 (by rfl) ⟨1935449, by rfl⟩ : syracuseStep 2580599 = 3870899) B3870899
theorem B2293895 : Blo 1528461 2293895 := bstep (se 1 (by rfl) ⟨1720421, by rfl⟩ : syracuseStep 2293895 = 3440843) B3440843
theorem B2293931 : Blo 1528461 2293931 := bstep (se 1 (by rfl) ⟨1720448, by rfl⟩ : syracuseStep 2293931 = 3440897) B3440897
theorem B8708269 : Blo 1528461 8708269 := bstep (se 3 (by rfl) ⟨1632800, by rfl⟩ : syracuseStep 8708269 = 3265601) B3265601
theorem B17424557 : Blo 1528461 17424557 := bstep (se 3 (by rfl) ⟨3267104, by rfl⟩ : syracuseStep 17424557 = 6534209) B6534209
theorem B3440825 : Blo 1528461 3440825 := bstep (se 2 (by rfl) ⟨1290309, by rfl⟩ : syracuseStep 3440825 = 2580619) B2580619
theorem B1720507 : Blo 1528461 1720507 := bstep (se 1 (by rfl) ⟨1290380, by rfl⟩ : syracuseStep 1720507 = 2580761) B2580761
theorem B4899017 : Blo 1528461 4899017 := bstep (se 2 (by rfl) ⟨1837131, by rfl⟩ : syracuseStep 4899017 = 3674263) B3674263
theorem B2293961 : Blo 1528461 2293961 := bstep (se 2 (by rfl) ⟨860235, by rfl⟩ : syracuseStep 2293961 = 1720471) B1720471
theorem B4964609 : Blo 1528461 4964609 := bstep (se 2 (by rfl) ⟨1861728, by rfl⟩ : syracuseStep 4964609 = 3723457) B3723457
theorem B10469665 : Blo 1528461 10469665 := bstep (se 2 (by rfl) ⟨3926124, by rfl⟩ : syracuseStep 10469665 = 7852249) B7852249
theorem B2294075 : Blo 1528461 2294075 := bstep (se 1 (by rfl) ⟨1720556, by rfl⟩ : syracuseStep 2294075 = 3441113) B3441113
theorem B2294135 : Blo 1528461 2294135 := bstep (se 1 (by rfl) ⟨1720601, by rfl⟩ : syracuseStep 2294135 = 3441203) B3441203
theorem B2294159 : Blo 1528461 2294159 := bstep (se 1 (by rfl) ⟨1720619, by rfl⟩ : syracuseStep 2294159 = 3441239) B3441239
theorem B2294201 : Blo 1528461 2294201 := bstep (se 2 (by rfl) ⟨860325, by rfl⟩ : syracuseStep 2294201 = 1720651) B1720651
theorem B2294279 : Blo 1528461 2294279 := bstep (se 1 (by rfl) ⟨1720709, by rfl⟩ : syracuseStep 2294279 = 3441419) B3441419
theorem B3441167 : Blo 1528461 3441167 := bstep (se 1 (by rfl) ⟨2580875, by rfl⟩ : syracuseStep 3441167 = 5161751) B5161751
theorem B3441185 : Blo 1528461 3441185 := bstep (se 2 (by rfl) ⟨1290444, by rfl⟩ : syracuseStep 3441185 = 2580889) B2580889
theorem B2294315 : Blo 1528461 2294315 := bstep (se 1 (by rfl) ⟨1720736, by rfl⟩ : syracuseStep 2294315 = 3441473) B3441473
theorem B2581051 : Blo 1528461 2581051 := bstep (se 1 (by rfl) ⟨1935788, by rfl⟩ : syracuseStep 2581051 = 3871577) B3871577
theorem B2294345 : Blo 1528461 2294345 := bstep (se 2 (by rfl) ⟨860379, by rfl⟩ : syracuseStep 2294345 = 1720759) B1720759
theorem B1720975 : Blo 1528461 1720975 := bstep (se 1 (by rfl) ⟨1290731, by rfl⟩ : syracuseStep 1720975 = 2581463) B2581463
theorem B2294459 : Blo 1528461 2294459 := bstep (se 1 (by rfl) ⟨1720844, by rfl⟩ : syracuseStep 2294459 = 3441689) B3441689
theorem B2581193 : Blo 1528461 2581193 := bstep (se 2 (by rfl) ⟨967947, by rfl⟩ : syracuseStep 2581193 = 1935895) B1935895
theorem B2294519 : Blo 1528461 2294519 := bstep (se 1 (by rfl) ⟨1720889, by rfl⟩ : syracuseStep 2294519 = 3441779) B3441779
theorem B2294543 : Blo 1528461 2294543 := bstep (se 1 (by rfl) ⟨1720907, by rfl⟩ : syracuseStep 2294543 = 3441815) B3441815
theorem B2294585 : Blo 1528461 2294585 := bstep (se 2 (by rfl) ⟨860469, by rfl⟩ : syracuseStep 2294585 = 1720939) B1720939
theorem B3441527 : Blo 1528461 3441527 := bstep (se 1 (by rfl) ⟨2581145, by rfl⟩ : syracuseStep 3441527 = 5162291) B5162291
theorem B2294663 : Blo 1528461 2294663 := bstep (se 1 (by rfl) ⟨1720997, by rfl⟩ : syracuseStep 2294663 = 3441995) B3441995
theorem B2294699 : Blo 1528461 2294699 := bstep (se 1 (by rfl) ⟨1721024, by rfl⟩ : syracuseStep 2294699 = 3442049) B3442049
theorem B5161913 : Blo 1528461 5161913 := bstep (se 2 (by rfl) ⟨1935717, by rfl⟩ : syracuseStep 5161913 = 3871435) B3871435
theorem B2294729 : Blo 1528461 2294729 := bstep (se 2 (by rfl) ⟨860523, by rfl⟩ : syracuseStep 2294729 = 1721047) B1721047
theorem B3441707 : Blo 1528461 3441707 := bstep (se 1 (by rfl) ⟨2581280, by rfl⟩ : syracuseStep 3441707 = 5162561) B5162561
theorem B2294843 : Blo 1528461 2294843 := bstep (se 1 (by rfl) ⟨1721132, by rfl⟩ : syracuseStep 2294843 = 3442265) B3442265
theorem B2294903 : Blo 1528461 2294903 := bstep (se 1 (by rfl) ⟨1721177, by rfl⟩ : syracuseStep 2294903 = 3442355) B3442355
theorem B19588229 : Blo 1528461 19588229 := bstep (se 4 (by rfl) ⟨1836396, by rfl⟩ : syracuseStep 19588229 = 3672793) B3672793
theorem B1721479 : Blo 1528461 1721479 := bstep (se 1 (by rfl) ⟨1291109, by rfl⟩ : syracuseStep 1721479 = 2582219) B2582219
theorem B2294927 : Blo 1528461 2294927 := bstep (se 1 (by rfl) ⟨1721195, by rfl⟩ : syracuseStep 2294927 = 3442391) B3442391
theorem B9299117 : Blo 1528461 9299117 := bstep (se 3 (by rfl) ⟨1743584, by rfl⟩ : syracuseStep 9299117 = 3487169) B3487169
theorem B2294969 : Blo 1528461 2294969 := bstep (se 2 (by rfl) ⟨860613, by rfl⟩ : syracuseStep 2294969 = 1721227) B1721227
theorem B1934599 : Blo 1528461 1934599 := bstep (se 1 (by rfl) ⟨1450949, by rfl⟩ : syracuseStep 1934599 = 2901899) B2901899
theorem B2295047 : Blo 1528461 2295047 := bstep (se 1 (by rfl) ⟨1721285, by rfl⟩ : syracuseStep 2295047 = 3442571) B3442571
theorem B2295083 : Blo 1528461 2295083 := bstep (se 1 (by rfl) ⟨1721312, by rfl⟩ : syracuseStep 2295083 = 3442625) B3442625
theorem B1721659 : Blo 1528461 1721659 := bstep (se 1 (by rfl) ⟨1291244, by rfl⟩ : syracuseStep 1721659 = 2582489) B2582489
theorem B2295113 : Blo 1528461 2295113 := bstep (se 2 (by rfl) ⟨860667, by rfl⟩ : syracuseStep 2295113 = 1721335) B1721335
theorem B51651971 : Blo 1528461 51651971 := bstep (se 1 (by rfl) ⟨38738978, by rfl⟩ : syracuseStep 51651971 = 77477957) B77477957
theorem B2581895 : Blo 1528461 2581895 := bstep (se 1 (by rfl) ⟨1936421, by rfl⟩ : syracuseStep 2581895 = 3872843) B3872843
theorem B3442067 : Blo 1528461 3442067 := bstep (se 1 (by rfl) ⟨2581550, by rfl⟩ : syracuseStep 3442067 = 5163101) B5163101
theorem B2295227 : Blo 1528461 2295227 := bstep (se 1 (by rfl) ⟨1721420, by rfl⟩ : syracuseStep 2295227 = 3442841) B3442841
theorem B3442121 : Blo 1528461 3442121 := bstep (se 2 (by rfl) ⟨1290795, by rfl⟩ : syracuseStep 3442121 = 2581591) B2581591
theorem B2295287 : Blo 1528461 2295287 := bstep (se 1 (by rfl) ⟨1721465, by rfl⟩ : syracuseStep 2295287 = 3442931) B3442931
theorem B5162507 : Blo 1528461 5162507 := bstep (se 1 (by rfl) ⟨3871880, by rfl⟩ : syracuseStep 5162507 = 7743761) B7743761
theorem B2295311 : Blo 1528461 2295311 := bstep (se 1 (by rfl) ⟨1721483, by rfl⟩ : syracuseStep 2295311 = 3442967) B3442967
theorem B2295353 : Blo 1528461 2295353 := bstep (se 2 (by rfl) ⟨860757, by rfl⟩ : syracuseStep 2295353 = 1721515) B1721515
theorem B26125901 : Blo 1528461 26125901 := bstep (se 3 (by rfl) ⟨4898606, by rfl⟩ : syracuseStep 26125901 = 9797213) B9797213
theorem B5809751 : Blo 1528461 5809751 := bstep (se 1 (by rfl) ⟨4357313, by rfl⟩ : syracuseStep 5809751 = 8714627) B8714627
theorem B5162615 : Blo 1528461 5162615 := bstep (se 1 (by rfl) ⟨3871961, by rfl⟩ : syracuseStep 5162615 = 7743923) B7743923
theorem B2295431 : Blo 1528461 2295431 := bstep (se 1 (by rfl) ⟨1721573, by rfl⟩ : syracuseStep 2295431 = 3443147) B3443147
theorem B1935019 : Blo 1528461 1935019 := bstep (se 1 (by rfl) ⟨1451264, by rfl⟩ : syracuseStep 1935019 = 2902529) B2902529
theorem B8267437 : Blo 1528461 8267437 := bstep (se 3 (by rfl) ⟨1550144, by rfl⟩ : syracuseStep 8267437 = 3100289) B3100289
theorem B2295467 : Blo 1528461 2295467 := bstep (se 1 (by rfl) ⟨1721600, by rfl⟩ : syracuseStep 2295467 = 3443201) B3443201
theorem B2295497 : Blo 1528461 2295497 := bstep (se 2 (by rfl) ⟨860811, by rfl⟩ : syracuseStep 2295497 = 1721623) B1721623
theorem B29812531 : Blo 1528461 29812531 := bstep (se 1 (by rfl) ⟨22359398, by rfl⟩ : syracuseStep 29812531 = 44718797) B44718797
theorem B2295611 : Blo 1528461 2295611 := bstep (se 1 (by rfl) ⟨1721708, by rfl⟩ : syracuseStep 2295611 = 3443417) B3443417
theorem B35309429 : Blo 1528461 35309429 := bstep (se 5 (by rfl) ⟨1655129, by rfl⟩ : syracuseStep 35309429 = 3310259) B3310259
theorem B2615159 : Blo 1528461 2615159 := bstep (se 1 (by rfl) ⟨1961369, by rfl⟩ : syracuseStep 2615159 = 3922739) B3922739
theorem B2295671 : Blo 1528461 2295671 := bstep (se 1 (by rfl) ⟨1721753, by rfl⟩ : syracuseStep 2295671 = 3443507) B3443507
theorem B1935247 : Blo 1528461 1935247 := bstep (se 1 (by rfl) ⟨1451435, by rfl⟩ : syracuseStep 1935247 = 2902871) B2902871
theorem B11618315 : Blo 1528461 11618315 := bstep (se 1 (by rfl) ⟨8713736, by rfl⟩ : syracuseStep 11618315 = 17427473) B17427473
theorem B2582543 : Blo 1528461 2582543 := bstep (se 1 (by rfl) ⟨1936907, by rfl⟩ : syracuseStep 2582543 = 3873815) B3873815
theorem B6531101 : Blo 1528461 6531101 := bstep (se 3 (by rfl) ⟨1224581, by rfl⟩ : syracuseStep 6531101 = 2449163) B2449163
theorem B5810237 : Blo 1528461 5810237 := bstep (se 3 (by rfl) ⟨1089419, by rfl⟩ : syracuseStep 5810237 = 2178839) B2178839
theorem B3442823 : Blo 1528461 3442823 := bstep (se 1 (by rfl) ⟨2582117, by rfl⟩ : syracuseStep 3442823 = 5164235) B5164235
theorem B5163209 : Blo 1528461 5163209 := bstep (se 2 (by rfl) ⟨1936203, by rfl⟩ : syracuseStep 5163209 = 3872407) B3872407
theorem B2902331 : Blo 1528461 2902331 := bstep (se 1 (by rfl) ⟨2176748, by rfl⟩ : syracuseStep 2902331 = 4353497) B4353497
theorem B3443003 : Blo 1528461 3443003 := bstep (se 1 (by rfl) ⟨2582252, by rfl⟩ : syracuseStep 3443003 = 5164505) B5164505
theorem B29403485 : Blo 1528461 29403485 := bstep (se 3 (by rfl) ⟨5513153, by rfl⟩ : syracuseStep 29403485 = 11026307) B11026307
theorem B1632647 : Blo 1528461 1632647 := bstep (se 1 (by rfl) ⟨1224485, by rfl⟩ : syracuseStep 1632647 = 2448971) B2448971
theorem B4901273 : Blo 1528461 4901273 := bstep (se 2 (by rfl) ⟨1837977, by rfl⟩ : syracuseStep 4901273 = 3675955) B3675955
theorem B3443129 : Blo 1528461 3443129 := bstep (se 2 (by rfl) ⟨1291173, by rfl⟩ : syracuseStep 3443129 = 2582347) B2582347
theorem B8710685 : Blo 1528461 8710685 := bstep (se 3 (by rfl) ⟨1633253, by rfl⟩ : syracuseStep 8710685 = 3266507) B3266507
theorem B2689595 : Blo 1528461 2689595 := bstep (se 1 (by rfl) ⟨2017196, by rfl⟩ : syracuseStep 2689595 = 4034393) B4034393
theorem B15698497 : Blo 1528461 15698497 := bstep (se 2 (by rfl) ⟨5886936, by rfl⟩ : syracuseStep 15698497 = 11773873) B11773873
theorem B1935991 : Blo 1528461 1935991 := bstep (se 1 (by rfl) ⟨1451993, by rfl⟩ : syracuseStep 1935991 = 2903987) B2903987
theorem B9300673 : Blo 1528461 9300673 := bstep (se 2 (by rfl) ⟨3487752, by rfl⟩ : syracuseStep 9300673 = 6975505) B6975505
theorem B6531785 : Blo 1528461 6531785 := bstep (se 2 (by rfl) ⟨2449419, by rfl⟩ : syracuseStep 6531785 = 4898839) B4898839
theorem B3869441 : Blo 1528461 3869441 := bstep (se 2 (by rfl) ⟨1451040, by rfl⟩ : syracuseStep 3869441 = 2902081) B2902081
theorem B3443471 : Blo 1528461 3443471 := bstep (se 1 (by rfl) ⟨2582603, by rfl⟩ : syracuseStep 3443471 = 5165207) B5165207
theorem B2902817 : Blo 1528461 2902817 := bstep (se 2 (by rfl) ⟨1088556, by rfl⟩ : syracuseStep 2902817 = 2177113) B2177113
theorem B3443489 : Blo 1528461 3443489 := bstep (se 2 (by rfl) ⟨1291308, by rfl⟩ : syracuseStep 3443489 = 2582617) B2582617
theorem B14707507 : Blo 1528461 14707507 := bstep (se 1 (by rfl) ⟨11030630, by rfl⟩ : syracuseStep 14707507 = 22061261) B22061261
theorem B4131643 : Blo 1528461 4131643 := bstep (se 1 (by rfl) ⟨3098732, by rfl⟩ : syracuseStep 4131643 = 6197465) B6197465
theorem B5163911 : Blo 1528461 5163911 := bstep (se 1 (by rfl) ⟨3872933, by rfl⟩ : syracuseStep 5163911 = 7745867) B7745867
theorem B7744409 : Blo 1528461 7744409 := bstep (se 2 (by rfl) ⟨2904153, by rfl⟩ : syracuseStep 7744409 = 5808307) B5808307
theorem B2902969 : Blo 1528461 2902969 := bstep (se 2 (by rfl) ⟨1088613, by rfl⟩ : syracuseStep 2902969 = 2177227) B2177227
theorem B1936315 : Blo 1528461 1936315 := bstep (se 1 (by rfl) ⟨1452236, by rfl⟩ : syracuseStep 1936315 = 2904473) B2904473
theorem B3099593 : Blo 1528461 3099593 := bstep (se 2 (by rfl) ⟨1162347, by rfl⟩ : syracuseStep 3099593 = 2324695) B2324695
theorem B3869815 : Blo 1528461 3869815 := bstep (se 1 (by rfl) ⟨2902361, by rfl⟩ : syracuseStep 3869815 = 5804723) B5804723
theorem B5164289 : Blo 1528461 5164289 := bstep (se 2 (by rfl) ⟨1936608, by rfl⟩ : syracuseStep 5164289 = 3873217) B3873217
theorem B1936811 : Blo 1528461 1936811 := bstep (se 1 (by rfl) ⟨1452608, by rfl⟩ : syracuseStep 1936811 = 2905217) B2905217
theorem B6974905 : Blo 1528461 6974905 := bstep (se 2 (by rfl) ⟨2615589, by rfl⟩ : syracuseStep 6974905 = 5231179) B5231179
theorem B5885369 : Blo 1528461 5885369 := bstep (se 2 (by rfl) ⟨2207013, by rfl⟩ : syracuseStep 5885369 = 4414027) B4414027
theorem B3870251 : Blo 1528461 3870251 := bstep (se 1 (by rfl) ⟨2902688, by rfl⟩ : syracuseStep 3870251 = 5805377) B5805377
theorem B6204989 : Blo 1528461 6204989 := bstep (se 3 (by rfl) ⟨1163435, by rfl⟩ : syracuseStep 6204989 = 2326871) B2326871
theorem B2207417 : Blo 1528461 2207417 := bstep (se 2 (by rfl) ⟨827781, by rfl⟩ : syracuseStep 2207417 = 1655563) B1655563
theorem B5803721 : Blo 1528461 5803721 := bstep (se 2 (by rfl) ⟨2176395, by rfl⟩ : syracuseStep 5803721 = 4352791) B4352791
theorem B9793295 : Blo 1528461 9793295 := bstep (se 1 (by rfl) ⟨7344971, by rfl⟩ : syracuseStep 9793295 = 14689943) B14689943
theorem B19607345 : Blo 1528461 19607345 := bstep (se 2 (by rfl) ⟨7352754, by rfl⟩ : syracuseStep 19607345 = 14705509) B14705509
theorem B4353851 : Blo 1528461 4353851 := bstep (se 1 (by rfl) ⟨3265388, by rfl⟩ : syracuseStep 4353851 = 6530777) B6530777
theorem B4353907 : Blo 1528461 4353907 := bstep (se 1 (by rfl) ⟨3265430, by rfl⟩ : syracuseStep 4353907 = 6530861) B6530861
theorem B12922739 : Blo 1528461 12922739 := bstep (se 1 (by rfl) ⟨9692054, by rfl⟩ : syracuseStep 12922739 = 19384109) B19384109
theorem B17420183 : Blo 1528461 17420183 := bstep (se 1 (by rfl) ⟨13065137, by rfl⟩ : syracuseStep 17420183 = 26130275) B26130275
theorem B11620259 : Blo 1528461 11620259 := bstep (se 1 (by rfl) ⟨8715194, by rfl⟩ : syracuseStep 11620259 = 17430389) B17430389
theorem B3264457 : Blo 1528461 3264457 := bstep (se 2 (by rfl) ⟨1224171, by rfl⟩ : syracuseStep 3264457 = 2448343) B2448343
theorem B5165099 : Blo 1528461 5165099 := bstep (se 1 (by rfl) ⟨3873824, by rfl⟩ : syracuseStep 5165099 = 7747649) B7747649
theorem B2207879 : Blo 1528461 2207879 := bstep (se 1 (by rfl) ⟨1655909, by rfl⟩ : syracuseStep 2207879 = 3311819) B3311819
theorem B3264713 : Blo 1528461 3264713 := bstep (se 2 (by rfl) ⟨1224267, by rfl⟩ : syracuseStep 3264713 = 2448535) B2448535
theorem B4354249 : Blo 1528461 4354249 := bstep (se 2 (by rfl) ⟨1632843, by rfl⟩ : syracuseStep 4354249 = 3265687) B3265687
theorem B3871091 : Blo 1528461 3871091 := bstep (se 1 (by rfl) ⟨2903318, by rfl⟩ : syracuseStep 3871091 = 5806637) B5806637
theorem B3871111 : Blo 1528461 3871111 := bstep (se 1 (by rfl) ⟨2903333, by rfl⟩ : syracuseStep 3871111 = 5806667) B5806667
theorem B11334035 : Blo 1528461 11334035 := bstep (se 1 (by rfl) ⟨8500526, by rfl⟩ : syracuseStep 11334035 = 17001053) B17001053
theorem B6533561 : Blo 1528461 6533561 := bstep (se 2 (by rfl) ⟨2450085, by rfl⟩ : syracuseStep 6533561 = 4900171) B4900171
theorem B3674639 : Blo 1528461 3674639 := bstep (se 1 (by rfl) ⟨2755979, by rfl⟩ : syracuseStep 3674639 = 5511959) B5511959
theorem B59609621 : Blo 1528461 59609621 := bstep (se 6 (by rfl) ⟨1397100, by rfl⟩ : syracuseStep 59609621 = 2794201) B2794201
theorem B10465859 : Blo 1528461 10465859 := bstep (se 1 (by rfl) ⟨7849394, by rfl⟩ : syracuseStep 10465859 = 15698789) B15698789
theorem B1528463 : Blo 1528461 1528463 := bstep (se 1 (by rfl) ⟨1146347, by rfl⟩ : syracuseStep 1528463 = 2292695) B2292695
theorem B3871385 : Blo 1528461 3871385 := bstep (se 2 (by rfl) ⟨1451769, by rfl⟩ : syracuseStep 3871385 = 2903539) B2903539
theorem B16528049 : Blo 1528461 16528049 := bstep (se 2 (by rfl) ⟨6198018, by rfl⟩ : syracuseStep 16528049 = 12396037) B12396037
theorem B2904761 : Blo 1528461 2904761 := bstep (se 2 (by rfl) ⟨1089285, by rfl⟩ : syracuseStep 2904761 = 2178571) B2178571
theorem B1528507 : Blo 1528461 1528507 := bstep (se 1 (by rfl) ⟨1146380, by rfl⟩ : syracuseStep 1528507 = 2292761) B2292761
theorem B1528583 : Blo 1528461 1528583 := bstep (se 1 (by rfl) ⟨1146437, by rfl⟩ : syracuseStep 1528583 = 2292875) B2292875
theorem B1528591 : Blo 1528461 1528591 := bstep (se 1 (by rfl) ⟨1146443, by rfl⟩ : syracuseStep 1528591 = 2292887) B2292887
theorem B7353139 : Blo 1528461 7353139 := bstep (se 1 (by rfl) ⟨5514854, by rfl⟩ : syracuseStep 7353139 = 11029709) B11029709
theorem B1528635 : Blo 1528461 1528635 := bstep (se 1 (by rfl) ⟨1146476, by rfl⟩ : syracuseStep 1528635 = 2292953) B2292953
theorem B3871547 : Blo 1528461 3871547 := bstep (se 1 (by rfl) ⟨2903660, by rfl⟩ : syracuseStep 3871547 = 5807321) B5807321
theorem B1528711 : Blo 1528461 1528711 := bstep (se 1 (by rfl) ⟨1146533, by rfl⟩ : syracuseStep 1528711 = 2293067) B2293067
theorem B1528719 : Blo 1528461 1528719 := bstep (se 1 (by rfl) ⟨1146539, by rfl⟩ : syracuseStep 1528719 = 2293079) B2293079
theorem B1528763 : Blo 1528461 1528763 := bstep (se 1 (by rfl) ⟨1146572, by rfl⟩ : syracuseStep 1528763 = 2293145) B2293145
theorem B8713169 : Blo 1528461 8713169 := bstep (se 2 (by rfl) ⟨3267438, by rfl⟩ : syracuseStep 8713169 = 6534877) B6534877
theorem B1528839 : Blo 1528461 1528839 := bstep (se 1 (by rfl) ⟨1146629, by rfl⟩ : syracuseStep 1528839 = 2293259) B2293259
theorem B1528847 : Blo 1528461 1528847 := bstep (se 1 (by rfl) ⟨1146635, by rfl⟩ : syracuseStep 1528847 = 2293271) B2293271
theorem B3871759 : Blo 1528461 3871759 := bstep (se 1 (by rfl) ⟨2903819, by rfl⟩ : syracuseStep 3871759 = 5807639) B5807639
theorem B1528891 : Blo 1528461 1528891 := bstep (se 1 (by rfl) ⟨1146668, by rfl⟩ : syracuseStep 1528891 = 2293337) B2293337
theorem B3535931 : Blo 1528461 3535931 := bstep (se 1 (by rfl) ⟨2651948, by rfl⟩ : syracuseStep 3535931 = 5303897) B5303897
theorem B1528967 : Blo 1528461 1528967 := bstep (se 1 (by rfl) ⟨1146725, by rfl⟩ : syracuseStep 1528967 = 2293451) B2293451
theorem B1528975 : Blo 1528461 1528975 := bstep (se 1 (by rfl) ⟨1146731, by rfl⟩ : syracuseStep 1528975 = 2293463) B2293463
theorem B1529019 : Blo 1528461 1529019 := bstep (se 1 (by rfl) ⟨1146764, by rfl⟩ : syracuseStep 1529019 = 2293529) B2293529
theorem B1529095 : Blo 1528461 1529095 := bstep (se 1 (by rfl) ⟨1146821, by rfl⟩ : syracuseStep 1529095 = 2293643) B2293643
theorem B1529103 : Blo 1528461 1529103 := bstep (se 1 (by rfl) ⟨1146827, by rfl⟩ : syracuseStep 1529103 = 2293655) B2293655
theorem B3872033 : Blo 1528461 3872033 := bstep (se 2 (by rfl) ⟨1452012, by rfl⟩ : syracuseStep 3872033 = 2904025) B2904025
theorem B1529147 : Blo 1528461 1529147 := bstep (se 1 (by rfl) ⟨1146860, by rfl⟩ : syracuseStep 1529147 = 2293721) B2293721
theorem B7738739 : Blo 1528461 7738739 := bstep (se 1 (by rfl) ⟨5804054, by rfl⟩ : syracuseStep 7738739 = 11608109) B11608109
theorem B1529223 : Blo 1528461 1529223 := bstep (se 1 (by rfl) ⟨1146917, by rfl⟩ : syracuseStep 1529223 = 2293835) B2293835
theorem B1529231 : Blo 1528461 1529231 := bstep (se 1 (by rfl) ⟨1146923, by rfl⟩ : syracuseStep 1529231 = 2293847) B2293847
theorem B18593171 : Blo 1528461 18593171 := bstep (se 1 (by rfl) ⟨13944878, by rfl⟩ : syracuseStep 18593171 = 27889757) B27889757
theorem B7747001 : Blo 1528461 7747001 := bstep (se 2 (by rfl) ⟨2905125, by rfl⟩ : syracuseStep 7747001 = 5810251) B5810251
theorem B1529275 : Blo 1528461 1529275 := bstep (se 1 (by rfl) ⟨1146956, by rfl⟩ : syracuseStep 1529275 = 2293913) B2293913
theorem B1529351 : Blo 1528461 1529351 := bstep (se 1 (by rfl) ⟨1147013, by rfl⟩ : syracuseStep 1529351 = 2294027) B2294027
theorem B1529359 : Blo 1528461 1529359 := bstep (se 1 (by rfl) ⟨1147019, by rfl⟩ : syracuseStep 1529359 = 2294039) B2294039
theorem B26490397 : Blo 1528461 26490397 := bstep (se 3 (by rfl) ⟨4966949, by rfl⟩ : syracuseStep 26490397 = 9933899) B9933899
theorem B1529403 : Blo 1528461 1529403 := bstep (se 1 (by rfl) ⟨1147052, by rfl⟩ : syracuseStep 1529403 = 2294105) B2294105
theorem B3266183 : Blo 1528461 3266183 := bstep (se 1 (by rfl) ⟨2449637, by rfl⟩ : syracuseStep 3266183 = 4899275) B4899275
theorem B1529479 : Blo 1528461 1529479 := bstep (se 1 (by rfl) ⟨1147109, by rfl⟩ : syracuseStep 1529479 = 2294219) B2294219
theorem B1529487 : Blo 1528461 1529487 := bstep (se 1 (by rfl) ⟨1147115, by rfl⟩ : syracuseStep 1529487 = 2294231) B2294231
theorem B1529531 : Blo 1528461 1529531 := bstep (se 1 (by rfl) ⟨1147148, by rfl⟩ : syracuseStep 1529531 = 2294297) B2294297
theorem B6534893 : Blo 1528461 6534893 := bstep (se 3 (by rfl) ⟨1225292, by rfl⟩ : syracuseStep 6534893 = 2450585) B2450585
theorem B1529607 : Blo 1528461 1529607 := bstep (se 1 (by rfl) ⟨1147205, by rfl⟩ : syracuseStep 1529607 = 2294411) B2294411
theorem B1529615 : Blo 1528461 1529615 := bstep (se 1 (by rfl) ⟨1147211, by rfl⟩ : syracuseStep 1529615 = 2294423) B2294423
theorem B1529659 : Blo 1528461 1529659 := bstep (se 1 (by rfl) ⟨1147244, by rfl⟩ : syracuseStep 1529659 = 2294489) B2294489
theorem B7739225 : Blo 1528461 7739225 := bstep (se 2 (by rfl) ⟨2902209, by rfl⟩ : syracuseStep 7739225 = 5804419) B5804419
theorem B1529735 : Blo 1528461 1529735 := bstep (se 1 (by rfl) ⟨1147301, by rfl⟩ : syracuseStep 1529735 = 2294603) B2294603
theorem B1529743 : Blo 1528461 1529743 := bstep (se 1 (by rfl) ⟨1147307, by rfl⟩ : syracuseStep 1529743 = 2294615) B2294615
theorem B7346065 : Blo 1528461 7346065 := bstep (se 2 (by rfl) ⟨2754774, by rfl⟩ : syracuseStep 7346065 = 5509549) B5509549
theorem B4896659 : Blo 1528461 4896659 := bstep (se 1 (by rfl) ⟨3672494, by rfl⟩ : syracuseStep 4896659 = 7344989) B7344989
theorem B3676051 : Blo 1528461 3676051 := bstep (se 1 (by rfl) ⟨2757038, by rfl⟩ : syracuseStep 3676051 = 5514077) B5514077
theorem B1529787 : Blo 1528461 1529787 := bstep (se 1 (by rfl) ⟨1147340, by rfl⟩ : syracuseStep 1529787 = 2294681) B2294681
theorem B2293751 : Blo 1528461 2293751 := bstep (se 1 (by rfl) ⟨1720313, by rfl⟩ : syracuseStep 2293751 = 3440627) B3440627
theorem B1529863 : Blo 1528461 1529863 := bstep (se 1 (by rfl) ⟨1147397, by rfl⟩ : syracuseStep 1529863 = 2294795) B2294795
theorem B8067083 : Blo 1528461 8067083 := bstep (se 1 (by rfl) ⟨6050312, by rfl⟩ : syracuseStep 8067083 = 12100625) B12100625
theorem B1529871 : Blo 1528461 1529871 := bstep (se 1 (by rfl) ⟨1147403, by rfl⟩ : syracuseStep 1529871 = 2294807) B2294807
theorem B1529915 : Blo 1528461 1529915 := bstep (se 1 (by rfl) ⟨1147436, by rfl⟩ : syracuseStep 1529915 = 2294873) B2294873
theorem B6535235 : Blo 1528461 6535235 := bstep (se 1 (by rfl) ⟨4901426, by rfl⟩ : syracuseStep 6535235 = 9802853) B9802853
theorem B1529991 : Blo 1528461 1529991 := bstep (se 1 (by rfl) ⟨1147493, by rfl⟩ : syracuseStep 1529991 = 2294987) B2294987
theorem B1529999 : Blo 1528461 1529999 := bstep (se 1 (by rfl) ⟨1147499, by rfl⟩ : syracuseStep 1529999 = 2294999) B2294999
theorem B1530043 : Blo 1528461 1530043 := bstep (se 1 (by rfl) ⟨1147532, by rfl⟩ : syracuseStep 1530043 = 2295065) B2295065
theorem B1530119 : Blo 1528461 1530119 := bstep (se 1 (by rfl) ⟨1147589, by rfl⟩ : syracuseStep 1530119 = 2295179) B2295179
theorem B3873035 : Blo 1528461 3873035 := bstep (se 1 (by rfl) ⟨2904776, by rfl⟩ : syracuseStep 3873035 = 5809553) B5809553
theorem B1530127 : Blo 1528461 1530127 := bstep (se 1 (by rfl) ⟨1147595, by rfl⟩ : syracuseStep 1530127 = 2295191) B2295191
theorem B1530171 : Blo 1528461 1530171 := bstep (se 1 (by rfl) ⟨1147628, by rfl⟩ : syracuseStep 1530171 = 2295257) B2295257
theorem B4356413 : Blo 1528461 4356413 := bstep (se 3 (by rfl) ⟨816827, by rfl⟩ : syracuseStep 4356413 = 1633655) B1633655
theorem B1530247 : Blo 1528461 1530247 := bstep (se 1 (by rfl) ⟨1147685, by rfl⟩ : syracuseStep 1530247 = 2295371) B2295371
theorem B1530255 : Blo 1528461 1530255 := bstep (se 1 (by rfl) ⟨1147691, by rfl⟩ : syracuseStep 1530255 = 2295383) B2295383
theorem B5159321 : Blo 1528461 5159321 := bstep (se 2 (by rfl) ⟨1934745, by rfl⟩ : syracuseStep 5159321 = 3869491) B3869491
theorem B1530299 : Blo 1528461 1530299 := bstep (se 1 (by rfl) ⟨1147724, by rfl⟩ : syracuseStep 1530299 = 2295449) B2295449
theorem B8264195 : Blo 1528461 8264195 := bstep (se 1 (by rfl) ⟨6198146, by rfl⟩ : syracuseStep 8264195 = 12396293) B12396293
theorem B1530375 : Blo 1528461 1530375 := bstep (se 1 (by rfl) ⟨1147781, by rfl⟩ : syracuseStep 1530375 = 2295563) B2295563
theorem B1530383 : Blo 1528461 1530383 := bstep (se 1 (by rfl) ⟨1147787, by rfl⟩ : syracuseStep 1530383 = 2295575) B2295575
theorem B4356641 : Blo 1528461 4356641 := bstep (se 2 (by rfl) ⟨1633740, by rfl⟩ : syracuseStep 4356641 = 3267481) B3267481
theorem B1530427 : Blo 1528461 1530427 := bstep (se 1 (by rfl) ⟨1147820, by rfl⟩ : syracuseStep 1530427 = 2295641) B2295641
theorem B3439223 : Blo 1528461 3439223 := bstep (se 1 (by rfl) ⟨2579417, by rfl⟩ : syracuseStep 3439223 = 5158835) B5158835
theorem B3267191 : Blo 1528461 3267191 := bstep (se 1 (by rfl) ⟨2450393, by rfl⟩ : syracuseStep 3267191 = 4900787) B4900787
theorem B27916919 : Blo 1528461 27916919 := bstep (se 1 (by rfl) ⟨20937689, by rfl⟩ : syracuseStep 27916919 = 41875379) B41875379
theorem B11614913 : Blo 1528461 11614913 := bstep (se 2 (by rfl) ⟨4355592, by rfl⟩ : syracuseStep 11614913 = 8711185) B8711185
theorem B5806849 : Blo 1528461 5806849 := bstep (se 2 (by rfl) ⟨2177568, by rfl⟩ : syracuseStep 5806849 = 4355137) B4355137
theorem B3439403 : Blo 1528461 3439403 := bstep (se 1 (by rfl) ⟨2579552, by rfl⟩ : syracuseStep 3439403 = 5159105) B5159105
theorem B3267371 : Blo 1528461 3267371 := bstep (se 1 (by rfl) ⟨2450528, by rfl⟩ : syracuseStep 3267371 = 4901057) B4901057
theorem B8715059 : Blo 1528461 8715059 := bstep (se 1 (by rfl) ⟨6536294, by rfl⟩ : syracuseStep 8715059 = 13072589) B13072589
theorem B4356983 : Blo 1528461 4356983 := bstep (se 1 (by rfl) ⟨3267737, by rfl⟩ : syracuseStep 4356983 = 6535475) B6535475
theorem B3873683 : Blo 1528461 3873683 := bstep (se 1 (by rfl) ⟨2905262, by rfl⟩ : syracuseStep 3873683 = 5810525) B5810525
theorem B2292743 : Blo 1528461 2292743 := bstep (se 1 (by rfl) ⟨1719557, by rfl⟩ : syracuseStep 2292743 = 3439115) B3439115
theorem B2292779 : Blo 1528461 2292779 := bstep (se 1 (by rfl) ⟨1719584, by rfl⟩ : syracuseStep 2292779 = 3439169) B3439169
theorem B2292809 : Blo 1528461 2292809 := bstep (se 2 (by rfl) ⟨859803, by rfl⟩ : syracuseStep 2292809 = 1719607) B1719607
theorem B7445591 : Blo 1528461 7445591 := bstep (se 1 (by rfl) ⟨5584193, by rfl⟩ : syracuseStep 7445591 = 11168387) B11168387
theorem B5160023 : Blo 1528461 5160023 := bstep (se 1 (by rfl) ⟨3870017, by rfl⟩ : syracuseStep 5160023 = 7740035) B7740035
theorem B3439763 : Blo 1528461 3439763 := bstep (se 1 (by rfl) ⟨2579822, by rfl⟩ : syracuseStep 3439763 = 5159645) B5159645
theorem B4652185 : Blo 1528461 4652185 := bstep (se 2 (by rfl) ⟨1744569, by rfl⟩ : syracuseStep 4652185 = 3489139) B3489139
theorem B3873977 : Blo 1528461 3873977 := bstep (se 2 (by rfl) ⟨1452741, by rfl⟩ : syracuseStep 3873977 = 2905483) B2905483
theorem B2292923 : Blo 1528461 2292923 := bstep (se 1 (by rfl) ⟨1719692, by rfl⟩ : syracuseStep 2292923 = 3439385) B3439385
theorem B3439817 : Blo 1528461 3439817 := bstep (se 2 (by rfl) ⟨1289931, by rfl⟩ : syracuseStep 3439817 = 2579863) B2579863
theorem B2292983 : Blo 1528461 2292983 := bstep (se 1 (by rfl) ⟨1719737, by rfl⟩ : syracuseStep 2292983 = 3439475) B3439475
theorem B2293007 : Blo 1528461 2293007 := bstep (se 1 (by rfl) ⟨1719755, by rfl⟩ : syracuseStep 2293007 = 3439511) B3439511
theorem B2579755 : Blo 1528461 2579755 := bstep (se 1 (by rfl) ⟨1934816, by rfl⟩ : syracuseStep 2579755 = 3869633) B3869633
theorem B2293049 : Blo 1528461 2293049 := bstep (se 2 (by rfl) ⟨859893, by rfl⟩ : syracuseStep 2293049 = 1719787) B1719787
theorem B2293127 : Blo 1528461 2293127 := bstep (se 1 (by rfl) ⟨1719845, by rfl⟩ : syracuseStep 2293127 = 3439691) B3439691
theorem B6200711 : Blo 1528461 6200711 := bstep (se 1 (by rfl) ⟨4650533, by rfl⟩ : syracuseStep 6200711 = 9301067) B9301067
theorem B12402067 : Blo 1528461 12402067 := bstep (se 1 (by rfl) ⟨9301550, by rfl⟩ : syracuseStep 12402067 = 18603101) B18603101
theorem B2293163 : Blo 1528461 2293163 := bstep (se 1 (by rfl) ⟨1719872, by rfl⟩ : syracuseStep 2293163 = 3439745) B3439745
theorem B2579897 : Blo 1528461 2579897 := bstep (se 2 (by rfl) ⟨967461, by rfl⟩ : syracuseStep 2579897 = 1934923) B1934923
theorem B2293193 : Blo 1528461 2293193 := bstep (se 2 (by rfl) ⟨859947, by rfl⟩ : syracuseStep 2293193 = 1719895) B1719895
theorem B8265169 : Blo 1528461 8265169 := bstep (se 2 (by rfl) ⟨3099438, by rfl⟩ : syracuseStep 8265169 = 6198877) B6198877
theorem B1719823 : Blo 1528461 1719823 := bstep (se 1 (by rfl) ⟨1289867, by rfl⟩ : syracuseStep 1719823 = 2579735) B2579735
theorem B2293307 : Blo 1528461 2293307 := bstep (se 1 (by rfl) ⟨1719980, by rfl⟩ : syracuseStep 2293307 = 3439961) B3439961
theorem B5160509 : Blo 1528461 5160509 := bstep (se 3 (by rfl) ⟨967595, by rfl⟩ : syracuseStep 5160509 = 1935191) B1935191
theorem B24813155 : Blo 1528461 24813155 := bstep (se 1 (by rfl) ⟨18609866, by rfl⟩ : syracuseStep 24813155 = 37219733) B37219733
theorem B2293367 : Blo 1528461 2293367 := bstep (se 1 (by rfl) ⟨1720025, by rfl⟩ : syracuseStep 2293367 = 3440051) B3440051
theorem B2293391 : Blo 1528461 2293391 := bstep (se 1 (by rfl) ⟨1720043, by rfl⟩ : syracuseStep 2293391 = 3440087) B3440087
theorem B18595507 : Blo 1528461 18595507 := bstep (se 1 (by rfl) ⟨13946630, by rfl⟩ : syracuseStep 18595507 = 27893261) B27893261
theorem B2293433 : Blo 1528461 2293433 := bstep (se 2 (by rfl) ⟨860037, by rfl⟩ : syracuseStep 2293433 = 1720075) B1720075
theorem B2293511 : Blo 1528461 2293511 := bstep (se 1 (by rfl) ⟨1720133, by rfl⟩ : syracuseStep 2293511 = 3440267) B3440267
theorem B2293547 : Blo 1528461 2293547 := bstep (se 1 (by rfl) ⟨1720160, by rfl⟩ : syracuseStep 2293547 = 3440321) B3440321
theorem B2293577 : Blo 1528461 2293577 := bstep (se 2 (by rfl) ⟨860091, by rfl⟩ : syracuseStep 2293577 = 1720183) B1720183
theorem B4136791 : Blo 1528461 4136791 := bstep (se 1 (by rfl) ⟨3102593, by rfl⟩ : syracuseStep 4136791 = 6205187) B6205187
theorem B3440519 : Blo 1528461 3440519 := bstep (se 1 (by rfl) ⟨2580389, by rfl⟩ : syracuseStep 3440519 = 5160779) B5160779
theorem B7741331 : Blo 1528461 7741331 := bstep (se 1 (by rfl) ⟨5805998, by rfl⟩ : syracuseStep 7741331 = 11611997) B11611997
theorem B2293691 : Blo 1528461 2293691 := bstep (se 1 (by rfl) ⟨1720268, by rfl⟩ : syracuseStep 2293691 = 3440537) B3440537
theorem B2293769 : Blo 1528461 2293769 := bstep (se 2 (by rfl) ⟨860163, by rfl⟩ : syracuseStep 2293769 = 1720327) B1720327
theorem B2293799 : Blo 1528461 2293799 := bstep (se 1 (by rfl) ⟨1720349, by rfl⟩ : syracuseStep 2293799 = 3440699) B3440699
theorem B1720399 : Blo 1528461 1720399 := bstep (se 1 (by rfl) ⟨1290299, by rfl⟩ : syracuseStep 1720399 = 2580599) B2580599
theorem B11616371 : Blo 1528461 11616371 := bstep (se 1 (by rfl) ⟨8712278, by rfl⟩ : syracuseStep 11616371 = 17424557) B17424557
theorem B86048885 : Blo 1528461 86048885 := bstep (se 5 (by rfl) ⟨4033541, by rfl⟩ : syracuseStep 86048885 = 8067083) B8067083
theorem B2293883 : Blo 1528461 2293883 := bstep (se 1 (by rfl) ⟨1720412, by rfl⟩ : syracuseStep 2293883 = 3440825) B3440825
theorem B9429149 : Blo 1528461 9429149 := bstep (se 3 (by rfl) ⟨1767965, by rfl⟩ : syracuseStep 9429149 = 3535931) B3535931
theorem B2580727 : Blo 1528461 2580727 := bstep (se 1 (by rfl) ⟨1935545, by rfl⟩ : syracuseStep 2580727 = 3871091) B3871091
theorem B2294009 : Blo 1528461 2294009 := bstep (se 2 (by rfl) ⟨860253, by rfl⟩ : syracuseStep 2294009 = 1720507) B1720507
theorem B2449759 : Blo 1528461 2449759 := bstep (se 1 (by rfl) ⟨1837319, by rfl⟩ : syracuseStep 2449759 = 3674639) B3674639
theorem B2294111 : Blo 1528461 2294111 := bstep (se 1 (by rfl) ⟨1720583, by rfl⟩ : syracuseStep 2294111 = 3441167) B3441167
theorem B39739747 : Blo 1528461 39739747 := bstep (se 1 (by rfl) ⟨29804810, by rfl⟩ : syracuseStep 39739747 = 59609621) B59609621
theorem B2294123 : Blo 1528461 2294123 := bstep (se 1 (by rfl) ⟨1720592, by rfl⟩ : syracuseStep 2294123 = 3441185) B3441185
theorem B13959553 : Blo 1528461 13959553 := bstep (se 2 (by rfl) ⟨5234832, by rfl⟩ : syracuseStep 13959553 = 10469665) B10469665
theorem B2580923 : Blo 1528461 2580923 := bstep (se 1 (by rfl) ⟨1935692, by rfl⟩ : syracuseStep 2580923 = 3871385) B3871385
theorem B11018699 : Blo 1528461 11018699 := bstep (se 1 (by rfl) ⟨8264024, by rfl⟩ : syracuseStep 11018699 = 16528049) B16528049
theorem B1720795 : Blo 1528461 1720795 := bstep (se 1 (by rfl) ⟨1290596, by rfl⟩ : syracuseStep 1720795 = 2581193) B2581193
theorem B5161481 : Blo 1528461 5161481 := bstep (se 2 (by rfl) ⟨1935555, by rfl⟩ : syracuseStep 5161481 = 3871111) B3871111
theorem B2581031 : Blo 1528461 2581031 := bstep (se 1 (by rfl) ⟨1935773, by rfl⟩ : syracuseStep 2581031 = 3871547) B3871547
theorem B2294351 : Blo 1528461 2294351 := bstep (se 1 (by rfl) ⟨1720763, by rfl⟩ : syracuseStep 2294351 = 3441527) B3441527
theorem B3441275 : Blo 1528461 3441275 := bstep (se 1 (by rfl) ⟨2580956, by rfl⟩ : syracuseStep 3441275 = 5161913) B5161913
theorem B5808779 : Blo 1528461 5808779 := bstep (se 1 (by rfl) ⟨4356584, by rfl⟩ : syracuseStep 5808779 = 8713169) B8713169
theorem B13238957 : Blo 1528461 13238957 := bstep (se 3 (by rfl) ⟨2482304, by rfl⟩ : syracuseStep 13238957 = 4964609) B4964609
theorem B2294471 : Blo 1528461 2294471 := bstep (se 1 (by rfl) ⟨1720853, by rfl⟩ : syracuseStep 2294471 = 3441707) B3441707
theorem B3441401 : Blo 1528461 3441401 := bstep (se 2 (by rfl) ⟨1290525, by rfl⟩ : syracuseStep 3441401 = 2581051) B2581051
theorem B20931329 : Blo 1528461 20931329 := bstep (se 2 (by rfl) ⟨7849248, by rfl⟩ : syracuseStep 20931329 = 15698497) B15698497
theorem B13058819 : Blo 1528461 13058819 := bstep (se 1 (by rfl) ⟨9794114, by rfl⟩ : syracuseStep 13058819 = 19588229) B19588229
theorem B2581321 : Blo 1528461 2581321 := bstep (se 2 (by rfl) ⟨967995, by rfl⟩ : syracuseStep 2581321 = 1935991) B1935991
theorem B2294633 : Blo 1528461 2294633 := bstep (se 2 (by rfl) ⟨860487, by rfl⟩ : syracuseStep 2294633 = 1720975) B1720975
theorem B2581355 : Blo 1528461 2581355 := bstep (se 1 (by rfl) ⟨1936016, by rfl⟩ : syracuseStep 2581355 = 3872033) B3872033
theorem B1721263 : Blo 1528461 1721263 := bstep (se 1 (by rfl) ⟨1290947, by rfl⟩ : syracuseStep 1721263 = 2581895) B2581895
theorem B12395447 : Blo 1528461 12395447 := bstep (se 1 (by rfl) ⟨9296585, by rfl⟩ : syracuseStep 12395447 = 18593171) B18593171
theorem B2294711 : Blo 1528461 2294711 := bstep (se 1 (by rfl) ⟨1721033, by rfl⟩ : syracuseStep 2294711 = 3442067) B3442067
theorem B2294747 : Blo 1528461 2294747 := bstep (se 1 (by rfl) ⟨1721060, by rfl⟩ : syracuseStep 2294747 = 3442121) B3442121
theorem B7742465 : Blo 1528461 7742465 := bstep (se 2 (by rfl) ⟨2903424, by rfl⟩ : syracuseStep 7742465 = 5806849) B5806849
theorem B49603589 : Blo 1528461 49603589 := bstep (se 4 (by rfl) ⟨4650336, by rfl⟩ : syracuseStep 49603589 = 9300673) B9300673
theorem B3441671 : Blo 1528461 3441671 := bstep (se 1 (by rfl) ⟨2581253, by rfl⟩ : syracuseStep 3441671 = 5162507) B5162507
theorem B17417267 : Blo 1528461 17417267 := bstep (se 1 (by rfl) ⟨13062950, by rfl⟩ : syracuseStep 17417267 = 26125901) B26125901
theorem B3441743 : Blo 1528461 3441743 := bstep (se 1 (by rfl) ⟨2581307, by rfl⟩ : syracuseStep 3441743 = 5162615) B5162615
theorem B2581753 : Blo 1528461 2581753 := bstep (se 2 (by rfl) ⟨968157, by rfl⟩ : syracuseStep 2581753 = 1936315) B1936315
theorem B1721695 : Blo 1528461 1721695 := bstep (se 1 (by rfl) ⟨1291271, by rfl⟩ : syracuseStep 1721695 = 2582543) B2582543
theorem B5162345 : Blo 1528461 5162345 := bstep (se 2 (by rfl) ⟨1935879, by rfl⟩ : syracuseStep 5162345 = 3871759) B3871759
theorem B2295215 : Blo 1528461 2295215 := bstep (se 1 (by rfl) ⟨1721411, by rfl⟩ : syracuseStep 2295215 = 3442823) B3442823
theorem B3442139 : Blo 1528461 3442139 := bstep (se 1 (by rfl) ⟨2581604, by rfl⟩ : syracuseStep 3442139 = 5163209) B5163209
theorem B2582023 : Blo 1528461 2582023 := bstep (se 1 (by rfl) ⟨1936517, by rfl⟩ : syracuseStep 2582023 = 3873035) B3873035
theorem B2295305 : Blo 1528461 2295305 := bstep (se 2 (by rfl) ⟨860739, by rfl⟩ : syracuseStep 2295305 = 1721479) B1721479
theorem B6202913 : Blo 1528461 6202913 := bstep (se 2 (by rfl) ⟨2326092, by rfl⟩ : syracuseStep 6202913 = 4652185) B4652185
theorem B2295335 : Blo 1528461 2295335 := bstep (se 1 (by rfl) ⟨1721501, by rfl⟩ : syracuseStep 2295335 = 3443003) B3443003
theorem B2295419 : Blo 1528461 2295419 := bstep (se 1 (by rfl) ⟨1721564, by rfl⟩ : syracuseStep 2295419 = 3443129) B3443129
theorem B2295545 : Blo 1528461 2295545 := bstep (se 2 (by rfl) ⟨860829, by rfl⟩ : syracuseStep 2295545 = 1721659) B1721659
theorem B7743275 : Blo 1528461 7743275 := bstep (se 1 (by rfl) ⟨5807456, by rfl⟩ : syracuseStep 7743275 = 11614913) B11614913
theorem B2295647 : Blo 1528461 2295647 := bstep (se 1 (by rfl) ⟨1721735, by rfl⟩ : syracuseStep 2295647 = 3443471) B3443471
theorem B2295659 : Blo 1528461 2295659 := bstep (se 1 (by rfl) ⟨1721744, by rfl⟩ : syracuseStep 2295659 = 3443489) B3443489
theorem B5810039 : Blo 1528461 5810039 := bstep (se 1 (by rfl) ⟨4357529, by rfl⟩ : syracuseStep 5810039 = 8715059) B8715059
theorem B9299873 : Blo 1528461 9299873 := bstep (se 2 (by rfl) ⟨3487452, by rfl⟩ : syracuseStep 9299873 = 6974905) B6974905
theorem B3442607 : Blo 1528461 3442607 := bstep (se 1 (by rfl) ⟨2581955, by rfl⟩ : syracuseStep 3442607 = 5163911) B5163911
theorem B2582455 : Blo 1528461 2582455 := bstep (se 1 (by rfl) ⟨1936841, by rfl⟩ : syracuseStep 2582455 = 3873683) B3873683
theorem B5162939 : Blo 1528461 5162939 := bstep (se 1 (by rfl) ⟨3872204, by rfl⟩ : syracuseStep 5162939 = 7744409) B7744409
theorem B11020225 : Blo 1528461 11020225 := bstep (se 2 (by rfl) ⟨4132584, by rfl⟩ : syracuseStep 11020225 = 8265169) B8265169
theorem B2066395 : Blo 1528461 2066395 := bstep (se 1 (by rfl) ⟨1549796, by rfl⟩ : syracuseStep 2066395 = 3099593) B3099593
theorem B2582651 : Blo 1528461 2582651 := bstep (se 1 (by rfl) ⟨1936988, by rfl⟩ : syracuseStep 2582651 = 3873977) B3873977
theorem B3442859 : Blo 1528461 3442859 := bstep (se 1 (by rfl) ⟨2582144, by rfl⟩ : syracuseStep 3442859 = 5164289) B5164289
theorem B16542103 : Blo 1528461 16542103 := bstep (se 1 (by rfl) ⟨12406577, by rfl⟩ : syracuseStep 16542103 = 24813155) B24813155
theorem B39750041 : Blo 1528461 39750041 := bstep (se 2 (by rfl) ⟨14906265, by rfl⟩ : syracuseStep 39750041 = 29812531) B29812531
theorem B5515721 : Blo 1528461 5515721 := bstep (se 2 (by rfl) ⟨2068395, by rfl⟩ : syracuseStep 5515721 = 4136791) B4136791
theorem B3869147 : Blo 1528461 3869147 := bstep (se 1 (by rfl) ⟨2901860, by rfl⟩ : syracuseStep 3869147 = 5803721) B5803721
theorem B4901401 : Blo 1528461 4901401 := bstep (se 2 (by rfl) ⟨1838025, by rfl⟩ : syracuseStep 4901401 = 3676051) B3676051
theorem B2902567 : Blo 1528461 2902567 := bstep (se 1 (by rfl) ⟨2176925, by rfl⟩ : syracuseStep 2902567 = 4353851) B4353851
theorem B4352609 : Blo 1528461 4352609 := bstep (se 2 (by rfl) ⟨1632228, by rfl⟩ : syracuseStep 4352609 = 3264457) B3264457
theorem B3443399 : Blo 1528461 3443399 := bstep (se 1 (by rfl) ⟨2582549, by rfl⟩ : syracuseStep 3443399 = 5165099) B5165099
theorem B4352723 : Blo 1528461 4352723 := bstep (se 1 (by rfl) ⟨3264542, by rfl⟩ : syracuseStep 4352723 = 6529085) B6529085
theorem B11611025 : Blo 1528461 11611025 := bstep (se 2 (by rfl) ⟨4354134, by rfl⟩ : syracuseStep 11611025 = 8708269) B8708269
theorem B7556023 : Blo 1528461 7556023 := bstep (se 1 (by rfl) ⟨5667017, by rfl⟩ : syracuseStep 7556023 = 11334035) B11334035
theorem B94202837 : Blo 1528461 94202837 := bstep (se 7 (by rfl) ⟨1103939, by rfl⟩ : syracuseStep 94202837 = 2207879) B2207879
theorem B44092997 : Blo 1528461 44092997 := bstep (se 4 (by rfl) ⟨4133718, by rfl⟩ : syracuseStep 44092997 = 8267437) B8267437
theorem B34434647 : Blo 1528461 34434647 := bstep (se 1 (by rfl) ⟨25825985, by rfl⟩ : syracuseStep 34434647 = 51651971) B51651971
theorem B5164667 : Blo 1528461 5164667 := bstep (se 1 (by rfl) ⟨3873500, by rfl⟩ : syracuseStep 5164667 = 7747001) B7747001
theorem B4353725 : Blo 1528461 4353725 := bstep (se 3 (by rfl) ⟨816323, by rfl⟩ : syracuseStep 4353725 = 1632647) B1632647
theorem B5508857 : Blo 1528461 5508857 := bstep (se 2 (by rfl) ⟨2065821, by rfl⟩ : syracuseStep 5508857 = 4131643) B4131643
theorem B5164829 : Blo 1528461 5164829 := bstep (se 3 (by rfl) ⟨968405, by rfl⟩ : syracuseStep 5164829 = 1936811) B1936811
theorem B3870625 : Blo 1528461 3870625 := bstep (se 2 (by rfl) ⟨1451484, by rfl⟩ : syracuseStep 3870625 = 2902969) B2902969
theorem B23539619 : Blo 1528461 23539619 := bstep (se 1 (by rfl) ⟨17654714, by rfl⟩ : syracuseStep 23539619 = 35309429) B35309429
theorem B7745543 : Blo 1528461 7745543 := bstep (se 1 (by rfl) ⟨5809157, by rfl⟩ : syracuseStep 7745543 = 11618315) B11618315
theorem B4354067 : Blo 1528461 4354067 := bstep (se 1 (by rfl) ⟨3265550, by rfl⟩ : syracuseStep 4354067 = 6531101) B6531101
theorem B2904275 : Blo 1528461 2904275 := bstep (se 1 (by rfl) ⟨2178206, by rfl⟩ : syracuseStep 2904275 = 4356413) B4356413
theorem B5509463 : Blo 1528461 5509463 := bstep (se 1 (by rfl) ⟨4132097, by rfl⟩ : syracuseStep 5509463 = 8264195) B8264195
theorem B2904427 : Blo 1528461 2904427 := bstep (se 1 (by rfl) ⟨2178320, by rfl⟩ : syracuseStep 2904427 = 4356641) B4356641
theorem B4354523 : Blo 1528461 4354523 := bstep (se 1 (by rfl) ⟨3265892, by rfl⟩ : syracuseStep 4354523 = 6531785) B6531785
theorem B5886445 : Blo 1528461 5886445 := bstep (se 3 (by rfl) ⟨1103708, by rfl⟩ : syracuseStep 5886445 = 2207417) B2207417
theorem B7746029 : Blo 1528461 7746029 := bstep (se 3 (by rfl) ⟨1452380, by rfl⟩ : syracuseStep 7746029 = 2904761) B2904761
theorem B16536089 : Blo 1528461 16536089 := bstep (se 2 (by rfl) ⟨6201033, by rfl⟩ : syracuseStep 16536089 = 12402067) B12402067
theorem B2904655 : Blo 1528461 2904655 := bstep (se 1 (by rfl) ⟨2178491, by rfl⟩ : syracuseStep 2904655 = 4356983) B4356983
theorem B1528495 : Blo 1528461 1528495 := bstep (se 1 (by rfl) ⟨1146371, by rfl⟩ : syracuseStep 1528495 = 2292743) B2292743
theorem B1528519 : Blo 1528461 1528519 := bstep (se 1 (by rfl) ⟨1146389, by rfl⟩ : syracuseStep 1528519 = 2292779) B2292779
theorem B35320529 : Blo 1528461 35320529 := bstep (se 2 (by rfl) ⟨13245198, by rfl⟩ : syracuseStep 35320529 = 26490397) B26490397
theorem B1528539 : Blo 1528461 1528539 := bstep (se 1 (by rfl) ⟨1146404, by rfl⟩ : syracuseStep 1528539 = 2292809) B2292809
theorem B1528615 : Blo 1528461 1528615 := bstep (se 1 (by rfl) ⟨1146461, by rfl⟩ : syracuseStep 1528615 = 2292923) B2292923
theorem B1528655 : Blo 1528461 1528655 := bstep (se 1 (by rfl) ⟨1146491, by rfl⟩ : syracuseStep 1528655 = 2292983) B2292983
theorem B1528671 : Blo 1528461 1528671 := bstep (se 1 (by rfl) ⟨1146503, by rfl⟩ : syracuseStep 1528671 = 2293007) B2293007
theorem B1528699 : Blo 1528461 1528699 := bstep (se 1 (by rfl) ⟨1146524, by rfl⟩ : syracuseStep 1528699 = 2293049) B2293049
theorem B24794009 : Blo 1528461 24794009 := bstep (se 2 (by rfl) ⟨9297753, by rfl⟩ : syracuseStep 24794009 = 18595507) B18595507
theorem B1528751 : Blo 1528461 1528751 := bstep (se 1 (by rfl) ⟨1146563, by rfl⟩ : syracuseStep 1528751 = 2293127) B2293127
theorem B4133807 : Blo 1528461 4133807 := bstep (se 1 (by rfl) ⟨3100355, by rfl⟩ : syracuseStep 4133807 = 6200711) B6200711
theorem B1528775 : Blo 1528461 1528775 := bstep (se 1 (by rfl) ⟨1146581, by rfl⟩ : syracuseStep 1528775 = 2293163) B2293163
theorem B1528795 : Blo 1528461 1528795 := bstep (se 1 (by rfl) ⟨1146596, by rfl⟩ : syracuseStep 1528795 = 2293193) B2293193
theorem B1528871 : Blo 1528461 1528871 := bstep (se 1 (by rfl) ⟨1146653, by rfl⟩ : syracuseStep 1528871 = 2293307) B2293307
theorem B1528911 : Blo 1528461 1528911 := bstep (se 1 (by rfl) ⟨1146683, by rfl⟩ : syracuseStep 1528911 = 2293367) B2293367
theorem B1528927 : Blo 1528461 1528927 := bstep (se 1 (by rfl) ⟨1146695, by rfl⟩ : syracuseStep 1528927 = 2293391) B2293391
theorem B1528955 : Blo 1528461 1528955 := bstep (se 1 (by rfl) ⟨1146716, by rfl⟩ : syracuseStep 1528955 = 2293433) B2293433
theorem B5805209 : Blo 1528461 5805209 := bstep (se 2 (by rfl) ⟨2176953, by rfl⟩ : syracuseStep 5805209 = 4353907) B4353907
theorem B1529007 : Blo 1528461 1529007 := bstep (se 1 (by rfl) ⟨1146755, by rfl⟩ : syracuseStep 1529007 = 2293511) B2293511
theorem B9794753 : Blo 1528461 9794753 := bstep (se 2 (by rfl) ⟨3673032, by rfl⟩ : syracuseStep 9794753 = 7346065) B7346065
theorem B1529031 : Blo 1528461 1529031 := bstep (se 1 (by rfl) ⟨1146773, by rfl⟩ : syracuseStep 1529031 = 2293547) B2293547
theorem B13071563 : Blo 1528461 13071563 := bstep (se 1 (by rfl) ⟨9803672, by rfl⟩ : syracuseStep 13071563 = 19607345) B19607345
theorem B1529051 : Blo 1528461 1529051 := bstep (se 1 (by rfl) ⟨1146788, by rfl⟩ : syracuseStep 1529051 = 2293577) B2293577
theorem B8615159 : Blo 1528461 8615159 := bstep (se 1 (by rfl) ⟨6461369, by rfl⟩ : syracuseStep 8615159 = 12922739) B12922739
theorem B11613455 : Blo 1528461 11613455 := bstep (se 1 (by rfl) ⟨8710091, by rfl⟩ : syracuseStep 11613455 = 17420183) B17420183
theorem B7746839 : Blo 1528461 7746839 := bstep (se 1 (by rfl) ⟨5810129, by rfl⟩ : syracuseStep 7746839 = 11620259) B11620259
theorem B1529127 : Blo 1528461 1529127 := bstep (se 1 (by rfl) ⟨1146845, by rfl⟩ : syracuseStep 1529127 = 2293691) B2293691
theorem B1529167 : Blo 1528461 1529167 := bstep (se 1 (by rfl) ⟨1146875, by rfl⟩ : syracuseStep 1529167 = 2293751) B2293751
theorem B1529183 : Blo 1528461 1529183 := bstep (se 1 (by rfl) ⟨1146887, by rfl⟩ : syracuseStep 1529183 = 2293775) B2293775
theorem B1529211 : Blo 1528461 1529211 := bstep (se 1 (by rfl) ⟨1146908, by rfl⟩ : syracuseStep 1529211 = 2293817) B2293817
theorem B1529263 : Blo 1528461 1529263 := bstep (se 1 (by rfl) ⟨1146947, by rfl⟩ : syracuseStep 1529263 = 2293895) B2293895
theorem B1529287 : Blo 1528461 1529287 := bstep (se 1 (by rfl) ⟨1146965, by rfl⟩ : syracuseStep 1529287 = 2293931) B2293931
theorem B2176475 : Blo 1528461 2176475 := bstep (se 1 (by rfl) ⟨1632356, by rfl⟩ : syracuseStep 2176475 = 3264713) B3264713
theorem B3266011 : Blo 1528461 3266011 := bstep (se 1 (by rfl) ⟨2449508, by rfl⟩ : syracuseStep 3266011 = 4899017) B4899017
theorem B1529307 : Blo 1528461 1529307 := bstep (se 1 (by rfl) ⟨1146980, by rfl⟩ : syracuseStep 1529307 = 2293961) B2293961
theorem B1529383 : Blo 1528461 1529383 := bstep (se 1 (by rfl) ⟨1147037, by rfl⟩ : syracuseStep 1529383 = 2294075) B2294075
theorem B1529423 : Blo 1528461 1529423 := bstep (se 1 (by rfl) ⟨1147067, by rfl⟩ : syracuseStep 1529423 = 2294135) B2294135
theorem B1529439 : Blo 1528461 1529439 := bstep (se 1 (by rfl) ⟨1147079, by rfl⟩ : syracuseStep 1529439 = 2294159) B2294159
theorem B5805665 : Blo 1528461 5805665 := bstep (se 2 (by rfl) ⟨2177124, by rfl⟩ : syracuseStep 5805665 = 4354249) B4354249
theorem B1529467 : Blo 1528461 1529467 := bstep (se 1 (by rfl) ⟨1147100, by rfl⟩ : syracuseStep 1529467 = 2294201) B2294201
theorem B4355707 : Blo 1528461 4355707 := bstep (se 1 (by rfl) ⟨3266780, by rfl⟩ : syracuseStep 4355707 = 6533561) B6533561
theorem B1529519 : Blo 1528461 1529519 := bstep (se 1 (by rfl) ⟨1147139, by rfl⟩ : syracuseStep 1529519 = 2294279) B2294279
theorem B1529543 : Blo 1528461 1529543 := bstep (se 1 (by rfl) ⟨1147157, by rfl⟩ : syracuseStep 1529543 = 2294315) B2294315
theorem B1529563 : Blo 1528461 1529563 := bstep (se 1 (by rfl) ⟨1147172, by rfl⟩ : syracuseStep 1529563 = 2294345) B2294345
theorem B1529639 : Blo 1528461 1529639 := bstep (se 1 (by rfl) ⟨1147229, by rfl⟩ : syracuseStep 1529639 = 2294459) B2294459
theorem B1529679 : Blo 1528461 1529679 := bstep (se 1 (by rfl) ⟨1147259, by rfl⟩ : syracuseStep 1529679 = 2294519) B2294519
theorem B1529695 : Blo 1528461 1529695 := bstep (se 1 (by rfl) ⟨1147271, by rfl⟩ : syracuseStep 1529695 = 2294543) B2294543
theorem B1529723 : Blo 1528461 1529723 := bstep (se 1 (by rfl) ⟨1147292, by rfl⟩ : syracuseStep 1529723 = 2294585) B2294585
theorem B1529775 : Blo 1528461 1529775 := bstep (se 1 (by rfl) ⟨1147331, by rfl⟩ : syracuseStep 1529775 = 2294663) B2294663
theorem B1529799 : Blo 1528461 1529799 := bstep (se 1 (by rfl) ⟨1147349, by rfl⟩ : syracuseStep 1529799 = 2294699) B2294699
theorem B1529819 : Blo 1528461 1529819 := bstep (se 1 (by rfl) ⟨1147364, by rfl⟩ : syracuseStep 1529819 = 2294729) B2294729
theorem B1529895 : Blo 1528461 1529895 := bstep (se 1 (by rfl) ⟨1147421, by rfl⟩ : syracuseStep 1529895 = 2294843) B2294843
theorem B1529935 : Blo 1528461 1529935 := bstep (se 1 (by rfl) ⟨1147451, by rfl⟩ : syracuseStep 1529935 = 2294903) B2294903
theorem B1529951 : Blo 1528461 1529951 := bstep (se 1 (by rfl) ⟨1147463, by rfl⟩ : syracuseStep 1529951 = 2294927) B2294927
theorem B6199411 : Blo 1528461 6199411 := bstep (se 1 (by rfl) ⟨4649558, by rfl⟩ : syracuseStep 6199411 = 9299117) B9299117
theorem B1529979 : Blo 1528461 1529979 := bstep (se 1 (by rfl) ⟨1147484, by rfl⟩ : syracuseStep 1529979 = 2294969) B2294969
theorem B7739549 : Blo 1528461 7739549 := bstep (se 3 (by rfl) ⟨1451165, by rfl⟩ : syracuseStep 7739549 = 2902331) B2902331
theorem B1530031 : Blo 1528461 1530031 := bstep (se 1 (by rfl) ⟨1147523, by rfl⟩ : syracuseStep 1530031 = 2295047) B2295047
theorem B1530055 : Blo 1528461 1530055 := bstep (se 1 (by rfl) ⟨1147541, by rfl⟩ : syracuseStep 1530055 = 2295083) B2295083
theorem B1530075 : Blo 1528461 1530075 := bstep (se 1 (by rfl) ⟨1147556, by rfl⟩ : syracuseStep 1530075 = 2295113) B2295113
theorem B5159159 : Blo 1528461 5159159 := bstep (se 1 (by rfl) ⟨3869369, by rfl⟩ : syracuseStep 5159159 = 7738739) B7738739
theorem B1530151 : Blo 1528461 1530151 := bstep (se 1 (by rfl) ⟨1147613, by rfl⟩ : syracuseStep 1530151 = 2295227) B2295227
theorem B1530191 : Blo 1528461 1530191 := bstep (se 1 (by rfl) ⟨1147643, by rfl⟩ : syracuseStep 1530191 = 2295287) B2295287
theorem B1530207 : Blo 1528461 1530207 := bstep (se 1 (by rfl) ⟨1147655, by rfl⟩ : syracuseStep 1530207 = 2295311) B2295311
theorem B1530235 : Blo 1528461 1530235 := bstep (se 1 (by rfl) ⟨1147676, by rfl⟩ : syracuseStep 1530235 = 2295353) B2295353
theorem B3873167 : Blo 1528461 3873167 := bstep (se 1 (by rfl) ⟨2904875, by rfl⟩ : syracuseStep 3873167 = 5809751) B5809751
theorem B9804185 : Blo 1528461 9804185 := bstep (se 2 (by rfl) ⟨3676569, by rfl⟩ : syracuseStep 9804185 = 7353139) B7353139
theorem B19610009 : Blo 1528461 19610009 := bstep (se 2 (by rfl) ⟨7353753, by rfl⟩ : syracuseStep 19610009 = 14707507) B14707507
theorem B2177455 : Blo 1528461 2177455 := bstep (se 1 (by rfl) ⟨1633091, by rfl⟩ : syracuseStep 2177455 = 3266183) B3266183
theorem B1530287 : Blo 1528461 1530287 := bstep (se 1 (by rfl) ⟨1147715, by rfl⟩ : syracuseStep 1530287 = 2295431) B2295431
theorem B1530311 : Blo 1528461 1530311 := bstep (se 1 (by rfl) ⟨1147733, by rfl⟩ : syracuseStep 1530311 = 2295467) B2295467
theorem B1530331 : Blo 1528461 1530331 := bstep (se 1 (by rfl) ⟨1147748, by rfl⟩ : syracuseStep 1530331 = 2295497) B2295497
theorem B4356595 : Blo 1528461 4356595 := bstep (se 1 (by rfl) ⟨3267446, by rfl⟩ : syracuseStep 4356595 = 6534893) B6534893
theorem B1530407 : Blo 1528461 1530407 := bstep (se 1 (by rfl) ⟨1147805, by rfl⟩ : syracuseStep 1530407 = 2295611) B2295611
theorem B5159483 : Blo 1528461 5159483 := bstep (se 1 (by rfl) ⟨3869612, by rfl⟩ : syracuseStep 5159483 = 7739225) B7739225
theorem B1743439 : Blo 1528461 1743439 := bstep (se 1 (by rfl) ⟨1307579, by rfl⟩ : syracuseStep 1743439 = 2615159) B2615159
theorem B1530447 : Blo 1528461 1530447 := bstep (se 1 (by rfl) ⟨1147835, by rfl⟩ : syracuseStep 1530447 = 2295671) B2295671
theorem B3873491 : Blo 1528461 3873491 := bstep (se 1 (by rfl) ⟨2905118, by rfl⟩ : syracuseStep 3873491 = 5810237) B5810237
theorem B4356823 : Blo 1528461 4356823 := bstep (se 1 (by rfl) ⟨3267617, by rfl⟩ : syracuseStep 4356823 = 6535235) B6535235
theorem B5159753 : Blo 1528461 5159753 := bstep (se 2 (by rfl) ⟨1934907, by rfl⟩ : syracuseStep 5159753 = 3869815) B3869815
theorem B16546637 : Blo 1528461 16546637 := bstep (se 3 (by rfl) ⟨3102494, by rfl⟩ : syracuseStep 16546637 = 6204989) B6204989
theorem B27908957 : Blo 1528461 27908957 := bstep (se 3 (by rfl) ⟨5232929, by rfl⟩ : syracuseStep 27908957 = 10465859) B10465859
theorem B19602323 : Blo 1528461 19602323 := bstep (se 1 (by rfl) ⟨14701742, by rfl⟩ : syracuseStep 19602323 = 29403485) B29403485
theorem B3439547 : Blo 1528461 3439547 := bstep (se 1 (by rfl) ⟨2579660, by rfl⟩ : syracuseStep 3439547 = 5159321) B5159321
theorem B3267515 : Blo 1528461 3267515 := bstep (se 1 (by rfl) ⟨2450636, by rfl⟩ : syracuseStep 3267515 = 4901273) B4901273
theorem B2579465 : Blo 1528461 2579465 := bstep (se 2 (by rfl) ⟨967299, by rfl⟩ : syracuseStep 2579465 = 1934599) B1934599
theorem B5807123 : Blo 1528461 5807123 := bstep (se 1 (by rfl) ⟨4355342, by rfl⟩ : syracuseStep 5807123 = 8710685) B8710685
theorem B1793063 : Blo 1528461 1793063 := bstep (se 1 (by rfl) ⟨1344797, by rfl⟩ : syracuseStep 1793063 = 2689595) B2689595
theorem B3439673 : Blo 1528461 3439673 := bstep (se 2 (by rfl) ⟨1289877, by rfl⟩ : syracuseStep 3439673 = 2579755) B2579755
theorem B2292815 : Blo 1528461 2292815 := bstep (se 1 (by rfl) ⟨1719611, by rfl⟩ : syracuseStep 2292815 = 3439223) B3439223
theorem B2178127 : Blo 1528461 2178127 := bstep (se 1 (by rfl) ⟨1633595, by rfl⟩ : syracuseStep 2178127 = 3267191) B3267191
theorem B18611279 : Blo 1528461 18611279 := bstep (se 1 (by rfl) ⟨13958459, by rfl⟩ : syracuseStep 18611279 = 27916919) B27916919
theorem B2579627 : Blo 1528461 2579627 := bstep (se 1 (by rfl) ⟨1934720, by rfl⟩ : syracuseStep 2579627 = 3869441) B3869441
theorem B2292935 : Blo 1528461 2292935 := bstep (se 1 (by rfl) ⟨1719701, by rfl⟩ : syracuseStep 2292935 = 3439403) B3439403
theorem B2178247 : Blo 1528461 2178247 := bstep (se 1 (by rfl) ⟨1633685, by rfl⟩ : syracuseStep 2178247 = 3267371) B3267371
theorem B2293097 : Blo 1528461 2293097 := bstep (se 2 (by rfl) ⟨859911, by rfl⟩ : syracuseStep 2293097 = 1719823) B1719823
theorem B4963727 : Blo 1528461 4963727 := bstep (se 1 (by rfl) ⟨3722795, by rfl⟩ : syracuseStep 4963727 = 7445591) B7445591
theorem B3440015 : Blo 1528461 3440015 := bstep (se 1 (by rfl) ⟨2580011, by rfl⟩ : syracuseStep 3440015 = 5160023) B5160023
theorem B7740845 : Blo 1528461 7740845 := bstep (se 3 (by rfl) ⟨1451408, by rfl⟩ : syracuseStep 7740845 = 2902817) B2902817
theorem B2293175 : Blo 1528461 2293175 := bstep (se 1 (by rfl) ⟨1719881, by rfl⟩ : syracuseStep 2293175 = 3439763) B3439763
theorem B2293211 : Blo 1528461 2293211 := bstep (se 1 (by rfl) ⟨1719908, by rfl⟩ : syracuseStep 2293211 = 3439817) B3439817
theorem B2580025 : Blo 1528461 2580025 := bstep (se 2 (by rfl) ⟨967509, by rfl⟩ : syracuseStep 2580025 = 1935019) B1935019
theorem B1719931 : Blo 1528461 1719931 := bstep (se 1 (by rfl) ⟨1289948, by rfl⟩ : syracuseStep 1719931 = 2579897) B2579897
theorem B3923579 : Blo 1528461 3923579 := bstep (se 1 (by rfl) ⟨2942684, by rfl⟩ : syracuseStep 3923579 = 5885369) B5885369
theorem B2580167 : Blo 1528461 2580167 := bstep (se 1 (by rfl) ⟨1935125, by rfl⟩ : syracuseStep 2580167 = 3870251) B3870251
theorem B3440339 : Blo 1528461 3440339 := bstep (se 1 (by rfl) ⟨2580254, by rfl⟩ : syracuseStep 3440339 = 5160509) B5160509
theorem B13057757 : Blo 1528461 13057757 := bstep (se 3 (by rfl) ⟨2448329, by rfl⟩ : syracuseStep 13057757 = 4896659) B4896659
theorem B6528863 : Blo 1528461 6528863 := bstep (se 1 (by rfl) ⟨4896647, by rfl⟩ : syracuseStep 6528863 = 9793295) B9793295
theorem B2580329 : Blo 1528461 2580329 := bstep (se 2 (by rfl) ⟨967623, by rfl⟩ : syracuseStep 2580329 = 1935247) B1935247
theorem B2293679 : Blo 1528461 2293679 := bstep (se 1 (by rfl) ⟨1720259, by rfl⟩ : syracuseStep 2293679 = 3440519) B3440519
theorem B5160887 : Blo 1528461 5160887 := bstep (se 1 (by rfl) ⟨3870665, by rfl⟩ : syracuseStep 5160887 = 7741331) B7741331
theorem B2293865 : Blo 1528461 2293865 := bstep (se 2 (by rfl) ⟨860199, by rfl⟩ : syracuseStep 2293865 = 1720399) B1720399
theorem B8265881 : Blo 1528461 8265881 := bstep (se 2 (by rfl) ⟨3099705, by rfl⟩ : syracuseStep 8265881 = 6199411) B6199411
theorem B1720615 : Blo 1528461 1720615 := bstep (se 1 (by rfl) ⟨1290461, by rfl⟩ : syracuseStep 1720615 = 2580923) B2580923
theorem B3440969 : Blo 1528461 3440969 := bstep (se 2 (by rfl) ⟨1290363, by rfl⟩ : syracuseStep 3440969 = 2580727) B2580727
theorem B3440987 : Blo 1528461 3440987 := bstep (se 1 (by rfl) ⟨2580740, by rfl⟩ : syracuseStep 3440987 = 5161481) B5161481
theorem B1720687 : Blo 1528461 1720687 := bstep (se 1 (by rfl) ⟨1290515, by rfl⟩ : syracuseStep 1720687 = 2581031) B2581031
theorem B2294183 : Blo 1528461 2294183 := bstep (se 1 (by rfl) ⟨1720637, by rfl⟩ : syracuseStep 2294183 = 3441275) B3441275
theorem B52986329 : Blo 1528461 52986329 := bstep (se 2 (by rfl) ⟨19869873, by rfl⟩ : syracuseStep 52986329 = 39739747) B39739747
theorem B2294267 : Blo 1528461 2294267 := bstep (se 1 (by rfl) ⟨1720700, by rfl⟩ : syracuseStep 2294267 = 3441401) B3441401
theorem B18612737 : Blo 1528461 18612737 := bstep (se 2 (by rfl) ⟨6979776, by rfl⟩ : syracuseStep 18612737 = 13959553) B13959553
theorem B1720903 : Blo 1528461 1720903 := bstep (se 1 (by rfl) ⟨1290677, by rfl⟩ : syracuseStep 1720903 = 2581355) B2581355
theorem B2294393 : Blo 1528461 2294393 := bstep (se 2 (by rfl) ⟨860397, by rfl⟩ : syracuseStep 2294393 = 1720795) B1720795
theorem B7848593 : Blo 1528461 7848593 := bstep (se 2 (by rfl) ⟨2943222, by rfl⟩ : syracuseStep 7848593 = 5886445) B5886445
theorem B5808793 : Blo 1528461 5808793 := bstep (se 2 (by rfl) ⟨2178297, by rfl⟩ : syracuseStep 5808793 = 4356595) B4356595
theorem B5161643 : Blo 1528461 5161643 := bstep (se 1 (by rfl) ⟨3871232, by rfl⟩ : syracuseStep 5161643 = 7742465) B7742465
theorem B2294447 : Blo 1528461 2294447 := bstep (se 1 (by rfl) ⟨1720835, by rfl⟩ : syracuseStep 2294447 = 3441671) B3441671
theorem B2294495 : Blo 1528461 2294495 := bstep (se 1 (by rfl) ⟨1720871, by rfl⟩ : syracuseStep 2294495 = 3441743) B3441743
theorem B6529835 : Blo 1528461 6529835 := bstep (se 1 (by rfl) ⟨4897376, by rfl⟩ : syracuseStep 6529835 = 9794753) B9794753
theorem B5743439 : Blo 1528461 5743439 := bstep (se 1 (by rfl) ⟨4307579, by rfl⟩ : syracuseStep 5743439 = 8615159) B8615159
theorem B7742303 : Blo 1528461 7742303 := bstep (se 1 (by rfl) ⟨5806727, by rfl⟩ : syracuseStep 7742303 = 11613455) B11613455
theorem B3441563 : Blo 1528461 3441563 := bstep (se 1 (by rfl) ⟨2581172, by rfl⟩ : syracuseStep 3441563 = 5162345) B5162345
theorem B5809097 : Blo 1528461 5809097 := bstep (se 2 (by rfl) ⟨2178411, by rfl⟩ : syracuseStep 5809097 = 4356823) B4356823
theorem B2294759 : Blo 1528461 2294759 := bstep (se 1 (by rfl) ⟨1721069, by rfl⟩ : syracuseStep 2294759 = 3442139) B3442139
theorem B3441761 : Blo 1528461 3441761 := bstep (se 2 (by rfl) ⟨1290660, by rfl⟩ : syracuseStep 3441761 = 2581321) B2581321
theorem B5162183 : Blo 1528461 5162183 := bstep (se 1 (by rfl) ⟨3871637, by rfl⟩ : syracuseStep 5162183 = 7743275) B7743275
theorem B2295017 : Blo 1528461 2295017 := bstep (se 2 (by rfl) ⟨860631, by rfl⟩ : syracuseStep 2295017 = 1721263) B1721263
theorem B2295071 : Blo 1528461 2295071 := bstep (se 1 (by rfl) ⟨1721303, by rfl⟩ : syracuseStep 2295071 = 3442607) B3442607
theorem B3441959 : Blo 1528461 3441959 := bstep (se 1 (by rfl) ⟨2581469, by rfl⟩ : syracuseStep 3441959 = 5162939) B5162939
theorem B1721767 : Blo 1528461 1721767 := bstep (se 1 (by rfl) ⟨1291325, by rfl⟩ : syracuseStep 1721767 = 2582651) B2582651
theorem B16541101 : Blo 1528461 16541101 := bstep (se 3 (by rfl) ⟨3101456, by rfl⟩ : syracuseStep 16541101 = 6202913) B6202913
theorem B2295239 : Blo 1528461 2295239 := bstep (se 1 (by rfl) ⟨1721429, by rfl⟩ : syracuseStep 2295239 = 3442859) B3442859
theorem B2582111 : Blo 1528461 2582111 := bstep (se 1 (by rfl) ⟨1936583, by rfl⟩ : syracuseStep 2582111 = 3873167) B3873167
theorem B10462877 : Blo 1528461 10462877 := bstep (se 3 (by rfl) ⟨1961789, by rfl⟩ : syracuseStep 10462877 = 3923579) B3923579
theorem B3442337 : Blo 1528461 3442337 := bstep (se 2 (by rfl) ⟨1290876, by rfl⟩ : syracuseStep 3442337 = 2581753) B2581753
theorem B2901739 : Blo 1528461 2901739 := bstep (se 1 (by rfl) ⟨2176304, by rfl⟩ : syracuseStep 2901739 = 4352609) B4352609
theorem B2295593 : Blo 1528461 2295593 := bstep (se 2 (by rfl) ⟨860847, by rfl⟩ : syracuseStep 2295593 = 1721695) B1721695
theorem B2295599 : Blo 1528461 2295599 := bstep (se 1 (by rfl) ⟨1721699, by rfl⟩ : syracuseStep 2295599 = 3443399) B3443399
theorem B2901815 : Blo 1528461 2901815 := bstep (se 1 (by rfl) ⟨2176361, by rfl⟩ : syracuseStep 2901815 = 4352723) B4352723
theorem B2582327 : Blo 1528461 2582327 := bstep (se 1 (by rfl) ⟨1936745, by rfl⟩ : syracuseStep 2582327 = 3873491) B3873491
theorem B18605971 : Blo 1528461 18605971 := bstep (se 1 (by rfl) ⟨13954478, by rfl⟩ : syracuseStep 18605971 = 27908957) B27908957
theorem B13068215 : Blo 1528461 13068215 := bstep (se 1 (by rfl) ⟨9801161, by rfl⟩ : syracuseStep 13068215 = 19602323) B19602323
theorem B62801891 : Blo 1528461 62801891 := bstep (se 1 (by rfl) ⟨47101418, by rfl⟩ : syracuseStep 62801891 = 94202837) B94202837
theorem B14690285 : Blo 1528461 14690285 := bstep (se 3 (by rfl) ⟨2754428, by rfl⟩ : syracuseStep 14690285 = 5508857) B5508857
theorem B3442697 : Blo 1528461 3442697 := bstep (se 2 (by rfl) ⟨1291011, by rfl⟩ : syracuseStep 3442697 = 2582023) B2582023
theorem B44124365 : Blo 1528461 44124365 := bstep (se 3 (by rfl) ⟨8273318, by rfl⟩ : syracuseStep 44124365 = 16546637) B16546637
theorem B40298789 : Blo 1528461 40298789 := bstep (se 4 (by rfl) ⟨3778011, by rfl⟩ : syracuseStep 40298789 = 7556023) B7556023
theorem B29395331 : Blo 1528461 29395331 := bstep (se 1 (by rfl) ⟨22046498, by rfl⟩ : syracuseStep 29395331 = 44092997) B44092997
theorem B22956431 : Blo 1528461 22956431 := bstep (se 1 (by rfl) ⟨17217323, by rfl⟩ : syracuseStep 22956431 = 34434647) B34434647
theorem B3443111 : Blo 1528461 3443111 := bstep (se 1 (by rfl) ⟨2582333, by rfl⟩ : syracuseStep 3443111 = 5164667) B5164667
theorem B2902483 : Blo 1528461 2902483 := bstep (se 1 (by rfl) ⟨2176862, by rfl⟩ : syracuseStep 2902483 = 4353725) B4353725
theorem B17418725 : Blo 1528461 17418725 := bstep (se 4 (by rfl) ⟨1633005, by rfl⟩ : syracuseStep 17418725 = 3266011) B3266011
theorem B3443219 : Blo 1528461 3443219 := bstep (se 1 (by rfl) ⟨2582414, by rfl⟩ : syracuseStep 3443219 = 5164829) B5164829
theorem B4352575 : Blo 1528461 4352575 := bstep (se 1 (by rfl) ⟨3264431, by rfl⟩ : syracuseStep 4352575 = 6528863) B6528863
theorem B3443273 : Blo 1528461 3443273 := bstep (se 2 (by rfl) ⟨1291227, by rfl⟩ : syracuseStep 3443273 = 2582455) B2582455
theorem B2755193 : Blo 1528461 2755193 := bstep (se 2 (by rfl) ⟨1033197, by rfl⟩ : syracuseStep 2755193 = 2066395) B2066395
theorem B5163695 : Blo 1528461 5163695 := bstep (se 1 (by rfl) ⟨3872771, by rfl⟩ : syracuseStep 5163695 = 7745543) B7745543
theorem B2902711 : Blo 1528461 2902711 := bstep (se 1 (by rfl) ⟨2177033, by rfl⟩ : syracuseStep 2902711 = 4354067) B4354067
theorem B7744247 : Blo 1528461 7744247 := bstep (se 1 (by rfl) ⟨5808185, by rfl⟩ : syracuseStep 7744247 = 11616371) B11616371
theorem B6286099 : Blo 1528461 6286099 := bstep (se 1 (by rfl) ⟨4714574, by rfl⟩ : syracuseStep 6286099 = 9429149) B9429149
theorem B2903015 : Blo 1528461 2903015 := bstep (se 1 (by rfl) ⟨2177261, by rfl⟩ : syracuseStep 2903015 = 4354523) B4354523
theorem B5164019 : Blo 1528461 5164019 := bstep (se 1 (by rfl) ⟨3873014, by rfl⟩ : syracuseStep 5164019 = 7746029) B7746029
theorem B8825971 : Blo 1528461 8825971 := bstep (se 1 (by rfl) ⟨6619478, by rfl⟩ : syracuseStep 8825971 = 13238957) B13238957
theorem B23547019 : Blo 1528461 23547019 := bstep (se 1 (by rfl) ⟨17660264, by rfl⟩ : syracuseStep 23547019 = 35320529) B35320529
theorem B22056137 : Blo 1528461 22056137 := bstep (se 2 (by rfl) ⟨8271051, by rfl⟩ : syracuseStep 22056137 = 16542103) B16542103
theorem B7744733 : Blo 1528461 7744733 := bstep (se 3 (by rfl) ⟨1452137, by rfl⟩ : syracuseStep 7744733 = 2904275) B2904275
theorem B2903273 : Blo 1528461 2903273 := bstep (se 2 (by rfl) ⟨1088727, by rfl⟩ : syracuseStep 2903273 = 2177455) B2177455
theorem B2755871 : Blo 1528461 2755871 := bstep (se 1 (by rfl) ⟨2066903, by rfl⟩ : syracuseStep 2755871 = 4133807) B4133807
theorem B11611511 : Blo 1528461 11611511 := bstep (se 1 (by rfl) ⟨8708633, by rfl⟩ : syracuseStep 11611511 = 17417267) B17417267
theorem B3870089 : Blo 1528461 3870089 := bstep (se 2 (by rfl) ⟨1451283, by rfl⟩ : syracuseStep 3870089 = 2902567) B2902567
theorem B3870139 : Blo 1528461 3870139 := bstep (se 1 (by rfl) ⟨2902604, by rfl⟩ : syracuseStep 3870139 = 5805209) B5805209
theorem B5164559 : Blo 1528461 5164559 := bstep (se 1 (by rfl) ⟨3873419, by rfl⟩ : syracuseStep 5164559 = 7746839) B7746839
theorem B14691901 : Blo 1528461 14691901 := bstep (se 3 (by rfl) ⟨2754731, by rfl⟩ : syracuseStep 14691901 = 5509463) B5509463
theorem B3870443 : Blo 1528461 3870443 := bstep (se 1 (by rfl) ⟨2902832, by rfl⟩ : syracuseStep 3870443 = 5805665) B5805665
theorem B106000109 : Blo 1528461 106000109 := bstep (se 3 (by rfl) ⟨19875020, by rfl⟩ : syracuseStep 106000109 = 39750041) B39750041
theorem B5803933 : Blo 1528461 5803933 := bstep (se 3 (by rfl) ⟨1088237, by rfl⟩ : syracuseStep 5803933 = 2176475) B2176475
theorem B2904169 : Blo 1528461 2904169 := bstep (se 2 (by rfl) ⟨1089063, by rfl⟩ : syracuseStep 2904169 = 2178127) B2178127
theorem B2904329 : Blo 1528461 2904329 := bstep (se 2 (by rfl) ⟨1089123, by rfl⟩ : syracuseStep 2904329 = 2178247) B2178247
theorem B55816877 : Blo 1528461 55816877 := bstep (se 3 (by rfl) ⟨10465664, by rfl⟩ : syracuseStep 55816877 = 20931329) B20931329
theorem B3871415 : Blo 1528461 3871415 := bstep (se 1 (by rfl) ⟨2903561, by rfl⟩ : syracuseStep 3871415 = 5807123) B5807123
theorem B1528543 : Blo 1528461 1528543 := bstep (se 1 (by rfl) ⟨1146407, by rfl⟩ : syracuseStep 1528543 = 2292815) B2292815
theorem B12407519 : Blo 1528461 12407519 := bstep (se 1 (by rfl) ⟨9305639, by rfl⟩ : syracuseStep 12407519 = 18611279) B18611279
theorem B1528623 : Blo 1528461 1528623 := bstep (se 1 (by rfl) ⟨1146467, by rfl⟩ : syracuseStep 1528623 = 2292935) B2292935
theorem B1528731 : Blo 1528461 1528731 := bstep (se 1 (by rfl) ⟨1146548, by rfl⟩ : syracuseStep 1528731 = 2293097) B2293097
theorem B1528783 : Blo 1528461 1528783 := bstep (se 1 (by rfl) ⟨1146587, by rfl⟩ : syracuseStep 1528783 = 2293175) B2293175
theorem B1528807 : Blo 1528461 1528807 := bstep (se 1 (by rfl) ⟨1146605, by rfl⟩ : syracuseStep 1528807 = 2293211) B2293211
theorem B62772317 : Blo 1528461 62772317 := bstep (se 3 (by rfl) ⟨11769809, by rfl⟩ : syracuseStep 62772317 = 23539619) B23539619
theorem B8705171 : Blo 1528461 8705171 := bstep (se 1 (by rfl) ⟨6528878, by rfl⟩ : syracuseStep 8705171 = 13057757) B13057757
theorem B14693633 : Blo 1528461 14693633 := bstep (se 2 (by rfl) ⟨5510112, by rfl⟩ : syracuseStep 14693633 = 11020225) B11020225
theorem B1529119 : Blo 1528461 1529119 := bstep (se 1 (by rfl) ⟨1146839, by rfl⟩ : syracuseStep 1529119 = 2293679) B2293679
theorem B1529179 : Blo 1528461 1529179 := bstep (se 1 (by rfl) ⟨1146884, by rfl⟩ : syracuseStep 1529179 = 2293769) B2293769
theorem B1529199 : Blo 1528461 1529199 := bstep (se 1 (by rfl) ⟨1146899, by rfl⟩ : syracuseStep 1529199 = 2293799) B2293799
theorem B57365923 : Blo 1528461 57365923 := bstep (se 1 (by rfl) ⟨43024442, by rfl⟩ : syracuseStep 57365923 = 86048885) B86048885
theorem B1529255 : Blo 1528461 1529255 := bstep (se 1 (by rfl) ⟨1146941, by rfl⟩ : syracuseStep 1529255 = 2293883) B2293883
theorem B4781501 : Blo 1528461 4781501 := bstep (se 3 (by rfl) ⟨896531, by rfl⟩ : syracuseStep 4781501 = 1793063) B1793063
theorem B1529339 : Blo 1528461 1529339 := bstep (se 1 (by rfl) ⟨1147004, by rfl⟩ : syracuseStep 1529339 = 2294009) B2294009
theorem B1529407 : Blo 1528461 1529407 := bstep (se 1 (by rfl) ⟨1147055, by rfl⟩ : syracuseStep 1529407 = 2294111) B2294111
theorem B1529415 : Blo 1528461 1529415 := bstep (se 1 (by rfl) ⟨1147061, by rfl⟩ : syracuseStep 1529415 = 2294123) B2294123
theorem B7345799 : Blo 1528461 7345799 := bstep (se 1 (by rfl) ⟨5509349, by rfl⟩ : syracuseStep 7345799 = 11018699) B11018699
theorem B11024059 : Blo 1528461 11024059 := bstep (se 1 (by rfl) ⟨8268044, by rfl⟩ : syracuseStep 11024059 = 16536089) B16536089
theorem B1529567 : Blo 1528461 1529567 := bstep (se 1 (by rfl) ⟨1147175, by rfl⟩ : syracuseStep 1529567 = 2294351) B2294351
theorem B3872519 : Blo 1528461 3872519 := bstep (se 1 (by rfl) ⟨2904389, by rfl⟩ : syracuseStep 3872519 = 5808779) B5808779
theorem B3266345 : Blo 1528461 3266345 := bstep (se 2 (by rfl) ⟨1224879, by rfl⟩ : syracuseStep 3266345 = 2449759) B2449759
theorem B1529647 : Blo 1528461 1529647 := bstep (se 1 (by rfl) ⟨1147235, by rfl⟩ : syracuseStep 1529647 = 2294471) B2294471
theorem B3872569 : Blo 1528461 3872569 := bstep (se 2 (by rfl) ⟨1452213, by rfl⟩ : syracuseStep 3872569 = 2904427) B2904427
theorem B8705879 : Blo 1528461 8705879 := bstep (se 1 (by rfl) ⟨6529409, by rfl⟩ : syracuseStep 8705879 = 13058819) B13058819
theorem B1529755 : Blo 1528461 1529755 := bstep (se 1 (by rfl) ⟨1147316, by rfl⟩ : syracuseStep 1529755 = 2294633) B2294633
theorem B16529339 : Blo 1528461 16529339 := bstep (se 1 (by rfl) ⟨12397004, by rfl⟩ : syracuseStep 16529339 = 24794009) B24794009
theorem B8263631 : Blo 1528461 8263631 := bstep (se 1 (by rfl) ⟨6197723, by rfl⟩ : syracuseStep 8263631 = 12395447) B12395447
theorem B1529807 : Blo 1528461 1529807 := bstep (se 1 (by rfl) ⟨1147355, by rfl⟩ : syracuseStep 1529807 = 2294711) B2294711
theorem B1529831 : Blo 1528461 1529831 := bstep (se 1 (by rfl) ⟨1147373, by rfl⟩ : syracuseStep 1529831 = 2294747) B2294747
theorem B33069059 : Blo 1528461 33069059 := bstep (se 1 (by rfl) ⟨24801794, by rfl⟩ : syracuseStep 33069059 = 49603589) B49603589
theorem B6535201 : Blo 1528461 6535201 := bstep (se 2 (by rfl) ⟨2450700, by rfl⟩ : syracuseStep 6535201 = 4901401) B4901401
theorem B2324585 : Blo 1528461 2324585 := bstep (se 2 (by rfl) ⟨871719, by rfl⟩ : syracuseStep 2324585 = 1743439) B1743439
theorem B3872873 : Blo 1528461 3872873 := bstep (se 2 (by rfl) ⟨1452327, by rfl⟩ : syracuseStep 3872873 = 2904655) B2904655
theorem B8714375 : Blo 1528461 8714375 := bstep (se 1 (by rfl) ⟨6535781, by rfl⟩ : syracuseStep 8714375 = 13071563) B13071563
theorem B1530143 : Blo 1528461 1530143 := bstep (se 1 (by rfl) ⟨1147607, by rfl⟩ : syracuseStep 1530143 = 2295215) B2295215
theorem B1530203 : Blo 1528461 1530203 := bstep (se 1 (by rfl) ⟨1147652, by rfl⟩ : syracuseStep 1530203 = 2295305) B2295305
theorem B1530223 : Blo 1528461 1530223 := bstep (se 1 (by rfl) ⟨1147667, by rfl⟩ : syracuseStep 1530223 = 2295335) B2295335
theorem B13236605 : Blo 1528461 13236605 := bstep (se 3 (by rfl) ⟨2481863, by rfl⟩ : syracuseStep 13236605 = 4963727) B4963727
theorem B1530279 : Blo 1528461 1530279 := bstep (se 1 (by rfl) ⟨1147709, by rfl⟩ : syracuseStep 1530279 = 2295419) B2295419
theorem B1530363 : Blo 1528461 1530363 := bstep (se 1 (by rfl) ⟨1147772, by rfl⟩ : syracuseStep 1530363 = 2295545) B2295545
theorem B1530431 : Blo 1528461 1530431 := bstep (se 1 (by rfl) ⟨1147823, by rfl⟩ : syracuseStep 1530431 = 2295647) B2295647
theorem B1530439 : Blo 1528461 1530439 := bstep (se 1 (by rfl) ⟨1147829, by rfl⟩ : syracuseStep 1530439 = 2295659) B2295659
theorem B3873359 : Blo 1528461 3873359 := bstep (se 1 (by rfl) ⟨2905019, by rfl⟩ : syracuseStep 3873359 = 5810039) B5810039
theorem B6199915 : Blo 1528461 6199915 := bstep (se 1 (by rfl) ⟨4649936, by rfl⟩ : syracuseStep 6199915 = 9299873) B9299873
theorem B5159699 : Blo 1528461 5159699 := bstep (se 1 (by rfl) ⟨3869774, by rfl⟩ : syracuseStep 5159699 = 7739549) B7739549
theorem B3439439 : Blo 1528461 3439439 := bstep (se 1 (by rfl) ⟨2579579, by rfl⟩ : syracuseStep 3439439 = 5159159) B5159159
theorem B6536123 : Blo 1528461 6536123 := bstep (se 1 (by rfl) ⟨4902092, by rfl⟩ : syracuseStep 6536123 = 9804185) B9804185
theorem B13073339 : Blo 1528461 13073339 := bstep (se 1 (by rfl) ⟨9805004, by rfl⟩ : syracuseStep 13073339 = 19610009) B19610009
theorem B3677147 : Blo 1528461 3677147 := bstep (se 1 (by rfl) ⟨2757860, by rfl⟩ : syracuseStep 3677147 = 5515721) B5515721
theorem B2579431 : Blo 1528461 2579431 := bstep (se 1 (by rfl) ⟨1934573, by rfl⟩ : syracuseStep 2579431 = 3869147) B3869147
theorem B3439655 : Blo 1528461 3439655 := bstep (se 1 (by rfl) ⟨2579741, by rfl⟩ : syracuseStep 3439655 = 5159483) B5159483
theorem B3439835 : Blo 1528461 3439835 := bstep (se 1 (by rfl) ⟨2579876, by rfl⟩ : syracuseStep 3439835 = 5159753) B5159753
theorem B7740683 : Blo 1528461 7740683 := bstep (se 1 (by rfl) ⟨5805512, by rfl⟩ : syracuseStep 7740683 = 11611025) B11611025
theorem B2293031 : Blo 1528461 2293031 := bstep (se 1 (by rfl) ⟨1719773, by rfl⟩ : syracuseStep 2293031 = 3439547) B3439547
theorem B2178343 : Blo 1528461 2178343 := bstep (se 1 (by rfl) ⟨1633757, by rfl⟩ : syracuseStep 2178343 = 3267515) B3267515
theorem B1719643 : Blo 1528461 1719643 := bstep (se 1 (by rfl) ⟨1289732, by rfl⟩ : syracuseStep 1719643 = 2579465) B2579465
theorem B2293115 : Blo 1528461 2293115 := bstep (se 1 (by rfl) ⟨1719836, by rfl⟩ : syracuseStep 2293115 = 3439673) B3439673
theorem B3440033 : Blo 1528461 3440033 := bstep (se 2 (by rfl) ⟨1290012, by rfl⟩ : syracuseStep 3440033 = 2580025) B2580025
theorem B1719751 : Blo 1528461 1719751 := bstep (se 1 (by rfl) ⟨1289813, by rfl⟩ : syracuseStep 1719751 = 2579627) B2579627
theorem B2293241 : Blo 1528461 2293241 := bstep (se 2 (by rfl) ⟨859965, by rfl⟩ : syracuseStep 2293241 = 1719931) B1719931
theorem B5807609 : Blo 1528461 5807609 := bstep (se 2 (by rfl) ⟨2177853, by rfl⟩ : syracuseStep 5807609 = 4355707) B4355707
theorem B2293343 : Blo 1528461 2293343 := bstep (se 1 (by rfl) ⟨1720007, by rfl⟩ : syracuseStep 2293343 = 3440015) B3440015
theorem B5160563 : Blo 1528461 5160563 := bstep (se 1 (by rfl) ⟨3870422, by rfl⟩ : syracuseStep 5160563 = 7740845) B7740845
theorem B1720111 : Blo 1528461 1720111 := bstep (se 1 (by rfl) ⟨1290083, by rfl⟩ : syracuseStep 1720111 = 2580167) B2580167
theorem B2293559 : Blo 1528461 2293559 := bstep (se 1 (by rfl) ⟨1720169, by rfl⟩ : syracuseStep 2293559 = 3440339) B3440339
theorem B5160833 : Blo 1528461 5160833 := bstep (se 2 (by rfl) ⟨1935312, by rfl⟩ : syracuseStep 5160833 = 3870625) B3870625
theorem B1720219 : Blo 1528461 1720219 := bstep (se 1 (by rfl) ⟨1290164, by rfl⟩ : syracuseStep 1720219 = 2580329) B2580329
theorem B3440591 : Blo 1528461 3440591 := bstep (se 1 (by rfl) ⟨2580443, by rfl⟩ : syracuseStep 3440591 = 5160887) B5160887
theorem B2293979 : Blo 1528461 2293979 := bstep (se 1 (by rfl) ⟨1720484, by rfl⟩ : syracuseStep 2293979 = 3440969) B3440969
theorem B2293991 : Blo 1528461 2293991 := bstep (se 1 (by rfl) ⟨1720493, by rfl⟩ : syracuseStep 2293991 = 3440987) B3440987
theorem B35324219 : Blo 1528461 35324219 := bstep (se 1 (by rfl) ⟨26493164, by rfl⟩ : syracuseStep 35324219 = 52986329) B52986329
theorem B2294153 : Blo 1528461 2294153 := bstep (se 2 (by rfl) ⟨860307, by rfl⟩ : syracuseStep 2294153 = 1720615) B1720615
theorem B3441095 : Blo 1528461 3441095 := bstep (se 1 (by rfl) ⟨2580821, by rfl⟩ : syracuseStep 3441095 = 5161643) B5161643
theorem B2580943 : Blo 1528461 2580943 := bstep (se 1 (by rfl) ⟨1935707, by rfl⟩ : syracuseStep 2580943 = 3871415) B3871415
theorem B2294249 : Blo 1528461 2294249 := bstep (se 2 (by rfl) ⟨860343, by rfl⟩ : syracuseStep 2294249 = 1720687) B1720687
theorem B5161535 : Blo 1528461 5161535 := bstep (se 1 (by rfl) ⟨3871151, by rfl⟩ : syracuseStep 5161535 = 7742303) B7742303
theorem B2294375 : Blo 1528461 2294375 := bstep (se 1 (by rfl) ⟨1720781, by rfl⟩ : syracuseStep 2294375 = 3441563) B3441563
theorem B2294507 : Blo 1528461 2294507 := bstep (se 1 (by rfl) ⟨1720880, by rfl⟩ : syracuseStep 2294507 = 3441761) B3441761
theorem B2294537 : Blo 1528461 2294537 := bstep (se 2 (by rfl) ⟨860451, by rfl⟩ : syracuseStep 2294537 = 1720903) B1720903
theorem B3441455 : Blo 1528461 3441455 := bstep (se 1 (by rfl) ⟨2581091, by rfl⟩ : syracuseStep 3441455 = 5162183) B5162183
theorem B8266553 : Blo 1528461 8266553 := bstep (se 2 (by rfl) ⟨3099957, by rfl⟩ : syracuseStep 8266553 = 6199915) B6199915
theorem B2294639 : Blo 1528461 2294639 := bstep (se 1 (by rfl) ⟨1720979, by rfl⟩ : syracuseStep 2294639 = 3441959) B3441959
theorem B3187667 : Blo 1528461 3187667 := bstep (se 1 (by rfl) ⟨2390750, by rfl⟩ : syracuseStep 3187667 = 4781501) B4781501
theorem B8381465 : Blo 1528461 8381465 := bstep (se 2 (by rfl) ⟨3143049, by rfl⟩ : syracuseStep 8381465 = 6286099) B6286099
theorem B1721407 : Blo 1528461 1721407 := bstep (se 1 (by rfl) ⟨1291055, by rfl⟩ : syracuseStep 1721407 = 2582111) B2582111
theorem B2294891 : Blo 1528461 2294891 := bstep (se 1 (by rfl) ⟨1721168, by rfl⟩ : syracuseStep 2294891 = 3442337) B3442337
theorem B2581679 : Blo 1528461 2581679 := bstep (se 1 (by rfl) ⟨1936259, by rfl⟩ : syracuseStep 2581679 = 3872519) B3872519
theorem B1934543 : Blo 1528461 1934543 := bstep (se 1 (by rfl) ⟨1450907, by rfl⟩ : syracuseStep 1934543 = 2901815) B2901815
theorem B1721551 : Blo 1528461 1721551 := bstep (se 1 (by rfl) ⟨1291163, by rfl⟩ : syracuseStep 1721551 = 2582327) B2582327
theorem B11019559 : Blo 1528461 11019559 := bstep (se 1 (by rfl) ⟨8264669, by rfl⟩ : syracuseStep 11019559 = 16529339) B16529339
theorem B22046039 : Blo 1528461 22046039 := bstep (se 1 (by rfl) ⟨16534529, by rfl⟩ : syracuseStep 22046039 = 33069059) B33069059
theorem B2295131 : Blo 1528461 2295131 := bstep (se 1 (by rfl) ⟨1721348, by rfl⟩ : syracuseStep 2295131 = 3442697) B3442697
theorem B2581915 : Blo 1528461 2581915 := bstep (se 1 (by rfl) ⟨1936436, by rfl⟩ : syracuseStep 2581915 = 3872873) B3872873
theorem B5809583 : Blo 1528461 5809583 := bstep (se 1 (by rfl) ⟨4357187, by rfl⟩ : syracuseStep 5809583 = 8714375) B8714375
theorem B11617829 : Blo 1528461 11617829 := bstep (se 4 (by rfl) ⟨1089171, by rfl⟩ : syracuseStep 11617829 = 2178343) B2178343
theorem B8824403 : Blo 1528461 8824403 := bstep (se 1 (by rfl) ⟨6618302, by rfl⟩ : syracuseStep 8824403 = 13236605) B13236605
theorem B19596887 : Blo 1528461 19596887 := bstep (se 1 (by rfl) ⟨14697665, by rfl⟩ : syracuseStep 19596887 = 29395331) B29395331
theorem B2295407 : Blo 1528461 2295407 := bstep (se 1 (by rfl) ⟨1721555, by rfl⟩ : syracuseStep 2295407 = 3443111) B3443111
theorem B2295479 : Blo 1528461 2295479 := bstep (se 1 (by rfl) ⟨1721609, by rfl⟩ : syracuseStep 2295479 = 3443219) B3443219
theorem B2295515 : Blo 1528461 2295515 := bstep (se 1 (by rfl) ⟨1721636, by rfl⟩ : syracuseStep 2295515 = 3443273) B3443273
theorem B2582239 : Blo 1528461 2582239 := bstep (se 1 (by rfl) ⟨1936679, by rfl⟩ : syracuseStep 2582239 = 3873359) B3873359
theorem B3442463 : Blo 1528461 3442463 := bstep (se 1 (by rfl) ⟨2581847, by rfl⟩ : syracuseStep 3442463 = 5163695) B5163695
theorem B5162831 : Blo 1528461 5162831 := bstep (se 1 (by rfl) ⟨3872123, by rfl⟩ : syracuseStep 5162831 = 7744247) B7744247
theorem B2295689 : Blo 1528461 2295689 := bstep (se 2 (by rfl) ⟨860883, by rfl⟩ : syracuseStep 2295689 = 1721767) B1721767
theorem B2451431 : Blo 1528461 2451431 := bstep (se 1 (by rfl) ⟨1838573, by rfl⟩ : syracuseStep 2451431 = 3677147) B3677147
theorem B1935343 : Blo 1528461 1935343 := bstep (se 1 (by rfl) ⟨1451507, by rfl⟩ : syracuseStep 1935343 = 2903015) B2903015
theorem B3442679 : Blo 1528461 3442679 := bstep (se 1 (by rfl) ⟨2582009, by rfl⟩ : syracuseStep 3442679 = 5164019) B5164019
theorem B19589201 : Blo 1528461 19589201 := bstep (se 2 (by rfl) ⟨7345950, by rfl⟩ : syracuseStep 19589201 = 14691901) B14691901
theorem B8710253 : Blo 1528461 8710253 := bstep (se 3 (by rfl) ⟨1633172, by rfl⟩ : syracuseStep 8710253 = 3266345) B3266345
theorem B5163155 : Blo 1528461 5163155 := bstep (se 1 (by rfl) ⟨3872366, by rfl⟩ : syracuseStep 5163155 = 7744733) B7744733
theorem B1935515 : Blo 1528461 1935515 := bstep (se 1 (by rfl) ⟨1451636, by rfl⟩ : syracuseStep 1935515 = 2903273) B2903273
theorem B1837247 : Blo 1528461 1837247 := bstep (se 1 (by rfl) ⟨1377935, by rfl⟩ : syracuseStep 1837247 = 2755871) B2755871
theorem B14698745 : Blo 1528461 14698745 := bstep (se 2 (by rfl) ⟨5512029, by rfl⟩ : syracuseStep 14698745 = 11024059) B11024059
theorem B3868985 : Blo 1528461 3868985 := bstep (se 2 (by rfl) ⟨1450869, by rfl⟩ : syracuseStep 3868985 = 2901739) B2901739
theorem B3443039 : Blo 1528461 3443039 := bstep (se 1 (by rfl) ⟨2582279, by rfl⟩ : syracuseStep 3443039 = 5164559) B5164559
theorem B5163425 : Blo 1528461 5163425 := bstep (se 2 (by rfl) ⟨1936284, by rfl⟩ : syracuseStep 5163425 = 3872569) B3872569
theorem B70666739 : Blo 1528461 70666739 := bstep (se 1 (by rfl) ⟨53000054, by rfl⟩ : syracuseStep 70666739 = 106000109) B106000109
theorem B24807961 : Blo 1528461 24807961 := bstep (se 2 (by rfl) ⟨9302985, by rfl⟩ : syracuseStep 24807961 = 18605971) B18605971
theorem B1936219 : Blo 1528461 1936219 := bstep (se 1 (by rfl) ⟨1452164, by rfl⟩ : syracuseStep 1936219 = 2904329) B2904329
theorem B37211251 : Blo 1528461 37211251 := bstep (se 1 (by rfl) ⟨27908438, by rfl⟩ : syracuseStep 37211251 = 55816877) B55816877
theorem B3828959 : Blo 1528461 3828959 := bstep (se 1 (by rfl) ⟨2871719, by rfl⟩ : syracuseStep 3828959 = 5743439) B5743439
theorem B3869977 : Blo 1528461 3869977 := bstep (se 2 (by rfl) ⟨1451241, by rfl⟩ : syracuseStep 3869977 = 2902483) B2902483
theorem B41848211 : Blo 1528461 41848211 := bstep (se 1 (by rfl) ⟨31386158, by rfl⟩ : syracuseStep 41848211 = 62772317) B62772317
theorem B5803433 : Blo 1528461 5803433 := bstep (se 2 (by rfl) ⟨2176287, by rfl⟩ : syracuseStep 5803433 = 4352575) B4352575
theorem B5803447 : Blo 1528461 5803447 := bstep (se 1 (by rfl) ⟨4352585, by rfl⟩ : syracuseStep 5803447 = 8705171) B8705171
theorem B7745057 : Blo 1528461 7745057 := bstep (se 2 (by rfl) ⟨2904396, by rfl⟩ : syracuseStep 7745057 = 5808793) B5808793
theorem B3870281 : Blo 1528461 3870281 := bstep (se 2 (by rfl) ⟨1451355, by rfl⟩ : syracuseStep 3870281 = 2902711) B2902711
theorem B6975251 : Blo 1528461 6975251 := bstep (se 1 (by rfl) ⟨5231438, by rfl⟩ : syracuseStep 6975251 = 10462877) B10462877
theorem B5803919 : Blo 1528461 5803919 := bstep (se 1 (by rfl) ⟨4352939, by rfl⟩ : syracuseStep 5803919 = 8705879) B8705879
theorem B8712143 : Blo 1528461 8712143 := bstep (se 1 (by rfl) ⟨6534107, by rfl⟩ : syracuseStep 8712143 = 13068215) B13068215
theorem B9793523 : Blo 1528461 9793523 := bstep (se 1 (by rfl) ⟨7345142, by rfl⟩ : syracuseStep 9793523 = 14690285) B14690285
theorem B11767961 : Blo 1528461 11767961 := bstep (se 2 (by rfl) ⟨4412985, by rfl⟩ : syracuseStep 11767961 = 8825971) B8825971
theorem B31396025 : Blo 1528461 31396025 := bstep (se 2 (by rfl) ⟨11773509, by rfl⟩ : syracuseStep 31396025 = 23547019) B23547019
theorem B26865859 : Blo 1528461 26865859 := bstep (se 1 (by rfl) ⟨20149394, by rfl⟩ : syracuseStep 26865859 = 40298789) B40298789
theorem B11612483 : Blo 1528461 11612483 := bstep (se 1 (by rfl) ⟨8709362, by rfl⟩ : syracuseStep 11612483 = 17418725) B17418725
theorem B17412893 : Blo 1528461 17412893 := bstep (se 3 (by rfl) ⟨3264917, by rfl⟩ : syracuseStep 17412893 = 6529835) B6529835
theorem B1528687 : Blo 1528461 1528687 := bstep (se 1 (by rfl) ⟨1146515, by rfl⟩ : syracuseStep 1528687 = 2293031) B2293031
theorem B1528743 : Blo 1528461 1528743 := bstep (se 1 (by rfl) ⟨1146557, by rfl⟩ : syracuseStep 1528743 = 2293115) B2293115
theorem B1528827 : Blo 1528461 1528827 := bstep (se 1 (by rfl) ⟨1146620, by rfl⟩ : syracuseStep 1528827 = 2293241) B2293241
theorem B3871739 : Blo 1528461 3871739 := bstep (se 1 (by rfl) ⟨2903804, by rfl⟩ : syracuseStep 3871739 = 5807609) B5807609
theorem B1528895 : Blo 1528461 1528895 := bstep (se 1 (by rfl) ⟨1146671, by rfl⟩ : syracuseStep 1528895 = 2293343) B2293343
theorem B1529039 : Blo 1528461 1529039 := bstep (se 1 (by rfl) ⟨1146779, by rfl⟩ : syracuseStep 1529039 = 2293559) B2293559
theorem B7738577 : Blo 1528461 7738577 := bstep (se 2 (by rfl) ⟨2901966, by rfl⟩ : syracuseStep 7738577 = 5803933) B5803933
theorem B8713601 : Blo 1528461 8713601 := bstep (se 2 (by rfl) ⟨3267600, by rfl⟩ : syracuseStep 8713601 = 6535201) B6535201
theorem B1529243 : Blo 1528461 1529243 := bstep (se 1 (by rfl) ⟨1146932, by rfl⟩ : syracuseStep 1529243 = 2293865) B2293865
theorem B5510587 : Blo 1528461 5510587 := bstep (se 1 (by rfl) ⟨4132940, by rfl⟩ : syracuseStep 5510587 = 8265881) B8265881
theorem B3872225 : Blo 1528461 3872225 := bstep (se 2 (by rfl) ⟨1452084, by rfl⟩ : syracuseStep 3872225 = 2904169) B2904169
theorem B6198893 : Blo 1528461 6198893 := bstep (se 3 (by rfl) ⟨1162292, by rfl⟩ : syracuseStep 6198893 = 2324585) B2324585
theorem B1529455 : Blo 1528461 1529455 := bstep (se 1 (by rfl) ⟨1147091, by rfl⟩ : syracuseStep 1529455 = 2294183) B2294183
theorem B1529511 : Blo 1528461 1529511 := bstep (se 1 (by rfl) ⟨1147133, by rfl⟩ : syracuseStep 1529511 = 2294267) B2294267
theorem B12408491 : Blo 1528461 12408491 := bstep (se 1 (by rfl) ⟨9306368, by rfl⟩ : syracuseStep 12408491 = 18612737) B18612737
theorem B1529595 : Blo 1528461 1529595 := bstep (se 1 (by rfl) ⟨1147196, by rfl⟩ : syracuseStep 1529595 = 2294393) B2294393
theorem B5232395 : Blo 1528461 5232395 := bstep (se 1 (by rfl) ⟨3924296, by rfl⟩ : syracuseStep 5232395 = 7848593) B7848593
theorem B1529631 : Blo 1528461 1529631 := bstep (se 1 (by rfl) ⟨1147223, by rfl⟩ : syracuseStep 1529631 = 2294447) B2294447
theorem B1529663 : Blo 1528461 1529663 := bstep (se 1 (by rfl) ⟨1147247, by rfl⟩ : syracuseStep 1529663 = 2294495) B2294495
theorem B8271679 : Blo 1528461 8271679 := bstep (se 1 (by rfl) ⟨6203759, by rfl⟩ : syracuseStep 8271679 = 12407519) B12407519
theorem B3872731 : Blo 1528461 3872731 := bstep (se 1 (by rfl) ⟨2904548, by rfl⟩ : syracuseStep 3872731 = 5809097) B5809097
theorem B1529839 : Blo 1528461 1529839 := bstep (se 1 (by rfl) ⟨1147379, by rfl⟩ : syracuseStep 1529839 = 2294759) B2294759
theorem B1530011 : Blo 1528461 1530011 := bstep (se 1 (by rfl) ⟨1147508, by rfl⟩ : syracuseStep 1530011 = 2295017) B2295017
theorem B9795755 : Blo 1528461 9795755 := bstep (se 1 (by rfl) ⟨7346816, by rfl⟩ : syracuseStep 9795755 = 14693633) B14693633
theorem B1530047 : Blo 1528461 1530047 := bstep (se 1 (by rfl) ⟨1147535, by rfl⟩ : syracuseStep 1530047 = 2295071) B2295071
theorem B1530159 : Blo 1528461 1530159 := bstep (se 1 (by rfl) ⟨1147619, by rfl⟩ : syracuseStep 1530159 = 2295239) B2295239
theorem B61217149 : Blo 1528461 61217149 := bstep (se 3 (by rfl) ⟨11478215, by rfl⟩ : syracuseStep 61217149 = 22956431) B22956431
theorem B4897199 : Blo 1528461 4897199 := bstep (se 1 (by rfl) ⟨3672899, by rfl⟩ : syracuseStep 4897199 = 7345799) B7345799
theorem B1530395 : Blo 1528461 1530395 := bstep (se 1 (by rfl) ⟨1147796, by rfl⟩ : syracuseStep 1530395 = 2295593) B2295593
theorem B1530399 : Blo 1528461 1530399 := bstep (se 1 (by rfl) ⟨1147799, by rfl⟩ : syracuseStep 1530399 = 2295599) B2295599
theorem B3439241 : Blo 1528461 3439241 := bstep (se 2 (by rfl) ⟨1289715, by rfl⟩ : syracuseStep 3439241 = 2579431) B2579431
theorem B41867927 : Blo 1528461 41867927 := bstep (se 1 (by rfl) ⟨31400945, by rfl⟩ : syracuseStep 41867927 = 62801891) B62801891
theorem B29416243 : Blo 1528461 29416243 := bstep (se 1 (by rfl) ⟨22062182, by rfl⟩ : syracuseStep 29416243 = 44124365) B44124365
theorem B7347181 : Blo 1528461 7347181 := bstep (se 3 (by rfl) ⟨1377596, by rfl⟩ : syracuseStep 7347181 = 2755193) B2755193
theorem B2292857 : Blo 1528461 2292857 := bstep (se 2 (by rfl) ⟨859821, by rfl⟩ : syracuseStep 2292857 = 1719643) B1719643
theorem B3439799 : Blo 1528461 3439799 := bstep (se 1 (by rfl) ⟨2579849, by rfl⟩ : syracuseStep 3439799 = 5159699) B5159699
theorem B76487897 : Blo 1528461 76487897 := bstep (se 2 (by rfl) ⟨28682961, by rfl⟩ : syracuseStep 76487897 = 57365923) B57365923
theorem B2292959 : Blo 1528461 2292959 := bstep (se 1 (by rfl) ⟨1719719, by rfl⟩ : syracuseStep 2292959 = 3439439) B3439439
theorem B5160185 : Blo 1528461 5160185 := bstep (se 2 (by rfl) ⟨1935069, by rfl⟩ : syracuseStep 5160185 = 3870139) B3870139
theorem B2293001 : Blo 1528461 2293001 := bstep (se 2 (by rfl) ⟨859875, by rfl⟩ : syracuseStep 2293001 = 1719751) B1719751
theorem B4357415 : Blo 1528461 4357415 := bstep (se 1 (by rfl) ⟨3268061, by rfl⟩ : syracuseStep 4357415 = 6536123) B6536123
theorem B8715559 : Blo 1528461 8715559 := bstep (se 1 (by rfl) ⟨6536669, by rfl⟩ : syracuseStep 8715559 = 13073339) B13073339
theorem B2293103 : Blo 1528461 2293103 := bstep (se 1 (by rfl) ⟨1719827, by rfl⟩ : syracuseStep 2293103 = 3439655) B3439655
theorem B14704091 : Blo 1528461 14704091 := bstep (se 1 (by rfl) ⟨11028068, by rfl⟩ : syracuseStep 14704091 = 22056137) B22056137
theorem B2293223 : Blo 1528461 2293223 := bstep (se 1 (by rfl) ⟨1719917, by rfl⟩ : syracuseStep 2293223 = 3439835) B3439835
theorem B5160455 : Blo 1528461 5160455 := bstep (se 1 (by rfl) ⟨3870341, by rfl⟩ : syracuseStep 5160455 = 7740683) B7740683
theorem B88219205 : Blo 1528461 88219205 := bstep (se 4 (by rfl) ⟨8270550, by rfl⟩ : syracuseStep 88219205 = 16541101) B16541101
theorem B7741007 : Blo 1528461 7741007 := bstep (se 1 (by rfl) ⟨5805755, by rfl⟩ : syracuseStep 7741007 = 11611511) B11611511
theorem B2580059 : Blo 1528461 2580059 := bstep (se 1 (by rfl) ⟨1935044, by rfl⟩ : syracuseStep 2580059 = 3870089) B3870089
theorem B2293355 : Blo 1528461 2293355 := bstep (se 1 (by rfl) ⟨1720016, by rfl⟩ : syracuseStep 2293355 = 3440033) B3440033
theorem B2293481 : Blo 1528461 2293481 := bstep (se 2 (by rfl) ⟨860055, by rfl⟩ : syracuseStep 2293481 = 1720111) B1720111
theorem B3440375 : Blo 1528461 3440375 := bstep (se 1 (by rfl) ⟨2580281, by rfl⟩ : syracuseStep 3440375 = 5160563) B5160563
theorem B2580295 : Blo 1528461 2580295 := bstep (se 1 (by rfl) ⟨1935221, by rfl⟩ : syracuseStep 2580295 = 3870443) B3870443
theorem B2293625 : Blo 1528461 2293625 := bstep (se 2 (by rfl) ⟨860109, by rfl⟩ : syracuseStep 2293625 = 1720219) B1720219
theorem B22036349 : Blo 1528461 22036349 := bstep (se 3 (by rfl) ⟨4131815, by rfl⟩ : syracuseStep 22036349 = 8263631) B8263631
theorem B3440555 : Blo 1528461 3440555 := bstep (se 1 (by rfl) ⟨2580416, by rfl⟩ : syracuseStep 3440555 = 5160833) B5160833
theorem B2293727 : Blo 1528461 2293727 := bstep (se 1 (by rfl) ⟨1720295, by rfl⟩ : syracuseStep 2293727 = 3440591) B3440591
theorem B20930683 : Blo 1528461 20930683 := bstep (se 1 (by rfl) ⟨15698012, by rfl⟩ : syracuseStep 20930683 = 31396025) B31396025
theorem B7741655 : Blo 1528461 7741655 := bstep (se 1 (by rfl) ⟨5806241, by rfl⟩ : syracuseStep 7741655 = 11612483) B11612483
theorem B2294063 : Blo 1528461 2294063 := bstep (se 1 (by rfl) ⟨1720547, by rfl⟩ : syracuseStep 2294063 = 3441095) B3441095
theorem B3441023 : Blo 1528461 3441023 := bstep (se 1 (by rfl) ⟨2580767, by rfl⟩ : syracuseStep 3441023 = 5161535) B5161535
theorem B5161373 : Blo 1528461 5161373 := bstep (se 3 (by rfl) ⟨967757, by rfl⟩ : syracuseStep 5161373 = 1935515) B1935515
theorem B4899325 : Blo 1528461 4899325 := bstep (se 3 (by rfl) ⟨918623, by rfl⟩ : syracuseStep 4899325 = 1837247) B1837247
theorem B11608595 : Blo 1528461 11608595 := bstep (se 1 (by rfl) ⟨8706446, by rfl⟩ : syracuseStep 11608595 = 17412893) B17412893
theorem B2294303 : Blo 1528461 2294303 := bstep (se 1 (by rfl) ⟨1720727, by rfl⟩ : syracuseStep 2294303 = 3441455) B3441455
theorem B3441257 : Blo 1528461 3441257 := bstep (se 2 (by rfl) ⟨1290471, by rfl⟩ : syracuseStep 3441257 = 2580943) B2580943
theorem B2581159 : Blo 1528461 2581159 := bstep (se 1 (by rfl) ⟨1935869, by rfl⟩ : syracuseStep 2581159 = 3871739) B3871739
theorem B5587643 : Blo 1528461 5587643 := bstep (se 1 (by rfl) ⟨4190732, by rfl⟩ : syracuseStep 5587643 = 8381465) B8381465
theorem B1721119 : Blo 1528461 1721119 := bstep (se 1 (by rfl) ⟨1290839, by rfl⟩ : syracuseStep 1721119 = 2581679) B2581679
theorem B14697359 : Blo 1528461 14697359 := bstep (se 1 (by rfl) ⟨11023019, by rfl⟩ : syracuseStep 14697359 = 22046039) B22046039
theorem B5809067 : Blo 1528461 5809067 := bstep (se 1 (by rfl) ⟨4356800, by rfl⟩ : syracuseStep 5809067 = 8713601) B8713601
theorem B2581483 : Blo 1528461 2581483 := bstep (se 1 (by rfl) ⟨1936112, by rfl⟩ : syracuseStep 2581483 = 3872225) B3872225
theorem B2581625 : Blo 1528461 2581625 := bstep (se 2 (by rfl) ⟨968109, by rfl⟩ : syracuseStep 2581625 = 1936219) B1936219
theorem B2294975 : Blo 1528461 2294975 := bstep (se 1 (by rfl) ⟨1721231, by rfl⟩ : syracuseStep 2294975 = 3442463) B3442463
theorem B3441887 : Blo 1528461 3441887 := bstep (se 1 (by rfl) ⟨2581415, by rfl⟩ : syracuseStep 3441887 = 5162831) B5162831
theorem B2295119 : Blo 1528461 2295119 := bstep (se 1 (by rfl) ⟨1721339, by rfl⟩ : syracuseStep 2295119 = 3442679) B3442679
theorem B13059467 : Blo 1528461 13059467 := bstep (se 1 (by rfl) ⟨9794600, by rfl⟩ : syracuseStep 13059467 = 19589201) B19589201
theorem B2295209 : Blo 1528461 2295209 := bstep (se 2 (by rfl) ⟨860703, by rfl⟩ : syracuseStep 2295209 = 1721407) B1721407
theorem B3442103 : Blo 1528461 3442103 := bstep (se 1 (by rfl) ⟨2581577, by rfl⟩ : syracuseStep 3442103 = 5163155) B5163155
theorem B6530503 : Blo 1528461 6530503 := bstep (se 1 (by rfl) ⟨4897877, by rfl⟩ : syracuseStep 6530503 = 9795755) B9795755
theorem B9799163 : Blo 1528461 9799163 := bstep (se 1 (by rfl) ⟨7349372, by rfl⟩ : syracuseStep 9799163 = 14698745) B14698745
theorem B2295359 : Blo 1528461 2295359 := bstep (se 1 (by rfl) ⟨1721519, by rfl⟩ : syracuseStep 2295359 = 3443039) B3443039
theorem B2295401 : Blo 1528461 2295401 := bstep (se 2 (by rfl) ⟨860775, by rfl⟩ : syracuseStep 2295401 = 1721551) B1721551
theorem B3442283 : Blo 1528461 3442283 := bstep (se 1 (by rfl) ⟨2581712, by rfl⟩ : syracuseStep 3442283 = 5163425) B5163425
theorem B27911951 : Blo 1528461 27911951 := bstep (se 1 (by rfl) ⟨20933963, by rfl⟩ : syracuseStep 27911951 = 41867927) B41867927
theorem B33089309 : Blo 1528461 33089309 := bstep (se 3 (by rfl) ⟨6204245, by rfl⟩ : syracuseStep 33089309 = 12408491) B12408491
theorem B3442553 : Blo 1528461 3442553 := bstep (se 2 (by rfl) ⟨1290957, by rfl⟩ : syracuseStep 3442553 = 2581915) B2581915
theorem B13953053 : Blo 1528461 13953053 := bstep (se 3 (by rfl) ⟨2616197, by rfl⟩ : syracuseStep 13953053 = 5232395) B5232395
theorem B3868955 : Blo 1528461 3868955 := bstep (se 1 (by rfl) ⟨2901716, by rfl⟩ : syracuseStep 3868955 = 5803433) B5803433
theorem B3442985 : Blo 1528461 3442985 := bstep (se 2 (by rfl) ⟨1291119, by rfl⟩ : syracuseStep 3442985 = 2582239) B2582239
theorem B5163371 : Blo 1528461 5163371 := bstep (se 1 (by rfl) ⟨3872528, by rfl⟩ : syracuseStep 5163371 = 7745057) B7745057
theorem B58812803 : Blo 1528461 58812803 := bstep (se 1 (by rfl) ⟨44109602, by rfl⟩ : syracuseStep 58812803 = 88219205) B88219205
theorem B11028905 : Blo 1528461 11028905 := bstep (se 2 (by rfl) ⟨4135839, by rfl⟩ : syracuseStep 11028905 = 8271679) B8271679
theorem B14690899 : Blo 1528461 14690899 := bstep (se 1 (by rfl) ⟨11018174, by rfl⟩ : syracuseStep 14690899 = 22036349) B22036349
theorem B3869279 : Blo 1528461 3869279 := bstep (se 1 (by rfl) ⟨2901959, by rfl⟩ : syracuseStep 3869279 = 5803919) B5803919
theorem B5163641 : Blo 1528461 5163641 := bstep (se 2 (by rfl) ⟨1936365, by rfl⟩ : syracuseStep 5163641 = 3872731) B3872731
theorem B2125111 : Blo 1528461 2125111 := bstep (se 1 (by rfl) ⟨1593833, by rfl⟩ : syracuseStep 2125111 = 3187667) B3187667
theorem B11619773 : Blo 1528461 11619773 := bstep (se 3 (by rfl) ⟨2178707, by rfl⟩ : syracuseStep 11619773 = 4357415) B4357415
theorem B7745219 : Blo 1528461 7745219 := bstep (se 1 (by rfl) ⟨5808914, by rfl⟩ : syracuseStep 7745219 = 11617829) B11617829
theorem B111595229 : Blo 1528461 111595229 := bstep (se 3 (by rfl) ⟨20924105, by rfl⟩ : syracuseStep 111595229 = 41848211) B41848211
theorem B4132595 : Blo 1528461 4132595 := bstep (se 1 (by rfl) ⟨3099446, by rfl⟩ : syracuseStep 4132595 = 6198893) B6198893
theorem B49615001 : Blo 1528461 49615001 := bstep (se 2 (by rfl) ⟨18605625, by rfl⟩ : syracuseStep 49615001 = 37211251) B37211251
theorem B23531741 : Blo 1528461 23531741 := bstep (se 3 (by rfl) ⟨4412201, by rfl⟩ : syracuseStep 23531741 = 8824403) B8824403
theorem B3264799 : Blo 1528461 3264799 := bstep (se 1 (by rfl) ⟨2448599, by rfl⟩ : syracuseStep 3264799 = 4897199) B4897199
theorem B14692745 : Blo 1528461 14692745 := bstep (se 2 (by rfl) ⟨5509779, by rfl⟩ : syracuseStep 14692745 = 11019559) B11019559
theorem B11620745 : Blo 1528461 11620745 := bstep (se 2 (by rfl) ⟨4357779, by rfl⟩ : syracuseStep 11620745 = 8715559) B8715559
theorem B7737929 : Blo 1528461 7737929 := bstep (se 2 (by rfl) ⟨2901723, by rfl⟩ : syracuseStep 7737929 = 5803447) B5803447
theorem B1528571 : Blo 1528461 1528571 := bstep (se 1 (by rfl) ⟨1146428, by rfl⟩ : syracuseStep 1528571 = 2292857) B2292857
theorem B50991931 : Blo 1528461 50991931 := bstep (se 1 (by rfl) ⟨38243948, by rfl⟩ : syracuseStep 50991931 = 76487897) B76487897
theorem B1528639 : Blo 1528461 1528639 := bstep (se 1 (by rfl) ⟨1146479, by rfl⟩ : syracuseStep 1528639 = 2292959) B2292959
theorem B2552639 : Blo 1528461 2552639 := bstep (se 1 (by rfl) ⟨1914479, by rfl⟩ : syracuseStep 2552639 = 3828959) B3828959
theorem B1528667 : Blo 1528461 1528667 := bstep (se 1 (by rfl) ⟨1146500, by rfl⟩ : syracuseStep 1528667 = 2293001) B2293001
theorem B1528735 : Blo 1528461 1528735 := bstep (se 1 (by rfl) ⟨1146551, by rfl⟩ : syracuseStep 1528735 = 2293103) B2293103
theorem B9802727 : Blo 1528461 9802727 := bstep (se 1 (by rfl) ⟨7352045, by rfl⟩ : syracuseStep 9802727 = 14704091) B14704091
theorem B1528815 : Blo 1528461 1528815 := bstep (se 1 (by rfl) ⟨1146611, by rfl⟩ : syracuseStep 1528815 = 2293223) B2293223
theorem B1528903 : Blo 1528461 1528903 := bstep (se 1 (by rfl) ⟨1146677, by rfl⟩ : syracuseStep 1528903 = 2293355) B2293355
theorem B1528987 : Blo 1528461 1528987 := bstep (se 1 (by rfl) ⟨1146740, by rfl⟩ : syracuseStep 1528987 = 2293481) B2293481
theorem B4650167 : Blo 1528461 4650167 := bstep (se 1 (by rfl) ⟨3487625, by rfl⟩ : syracuseStep 4650167 = 6975251) B6975251
theorem B1529083 : Blo 1528461 1529083 := bstep (se 1 (by rfl) ⟨1146812, by rfl⟩ : syracuseStep 1529083 = 2293625) B2293625
theorem B1529151 : Blo 1528461 1529151 := bstep (se 1 (by rfl) ⟨1146863, by rfl⟩ : syracuseStep 1529151 = 2293727) B2293727
theorem B1529319 : Blo 1528461 1529319 := bstep (se 1 (by rfl) ⟨1146989, by rfl⟩ : syracuseStep 1529319 = 2293979) B2293979
theorem B1529327 : Blo 1528461 1529327 := bstep (se 1 (by rfl) ⟨1146995, by rfl⟩ : syracuseStep 1529327 = 2293991) B2293991
theorem B35821145 : Blo 1528461 35821145 := bstep (se 2 (by rfl) ⟨13432929, by rfl⟩ : syracuseStep 35821145 = 26865859) B26865859
theorem B1529435 : Blo 1528461 1529435 := bstep (se 1 (by rfl) ⟨1147076, by rfl⟩ : syracuseStep 1529435 = 2294153) B2294153
theorem B1529499 : Blo 1528461 1529499 := bstep (se 1 (by rfl) ⟨1147124, by rfl⟩ : syracuseStep 1529499 = 2294249) B2294249
theorem B31381229 : Blo 1528461 31381229 := bstep (se 3 (by rfl) ⟨5883980, by rfl⟩ : syracuseStep 31381229 = 11767961) B11767961
theorem B1529583 : Blo 1528461 1529583 := bstep (se 1 (by rfl) ⟨1147187, by rfl⟩ : syracuseStep 1529583 = 2294375) B2294375
theorem B1529671 : Blo 1528461 1529671 := bstep (se 1 (by rfl) ⟨1147253, by rfl⟩ : syracuseStep 1529671 = 2294507) B2294507
theorem B81622865 : Blo 1528461 81622865 := bstep (se 2 (by rfl) ⟨30608574, by rfl⟩ : syracuseStep 81622865 = 61217149) B61217149
theorem B1529691 : Blo 1528461 1529691 := bstep (se 1 (by rfl) ⟨1147268, by rfl⟩ : syracuseStep 1529691 = 2294537) B2294537
theorem B5511035 : Blo 1528461 5511035 := bstep (se 1 (by rfl) ⟨4133276, by rfl⟩ : syracuseStep 5511035 = 8266553) B8266553
theorem B5158781 : Blo 1528461 5158781 := bstep (se 3 (by rfl) ⟨967271, by rfl⟩ : syracuseStep 5158781 = 1934543) B1934543
theorem B1529759 : Blo 1528461 1529759 := bstep (se 1 (by rfl) ⟨1147319, by rfl⟩ : syracuseStep 1529759 = 2294639) B2294639
theorem B33077281 : Blo 1528461 33077281 := bstep (se 2 (by rfl) ⟨12403980, by rfl⟩ : syracuseStep 33077281 = 24807961) B24807961
theorem B1529927 : Blo 1528461 1529927 := bstep (se 1 (by rfl) ⟨1147445, by rfl⟩ : syracuseStep 1529927 = 2294891) B2294891
theorem B5159051 : Blo 1528461 5159051 := bstep (se 1 (by rfl) ⟨3869288, by rfl⟩ : syracuseStep 5159051 = 7738577) B7738577
theorem B94197917 : Blo 1528461 94197917 := bstep (se 3 (by rfl) ⟨17662109, by rfl⟩ : syracuseStep 94197917 = 35324219) B35324219
theorem B1530087 : Blo 1528461 1530087 := bstep (se 1 (by rfl) ⟨1147565, by rfl⟩ : syracuseStep 1530087 = 2295131) B2295131
theorem B3873055 : Blo 1528461 3873055 := bstep (se 1 (by rfl) ⟨2904791, by rfl⟩ : syracuseStep 3873055 = 5809583) B5809583
theorem B13064591 : Blo 1528461 13064591 := bstep (se 1 (by rfl) ⟨9798443, by rfl⟩ : syracuseStep 13064591 = 19596887) B19596887
theorem B39221657 : Blo 1528461 39221657 := bstep (se 2 (by rfl) ⟨14708121, by rfl⟩ : syracuseStep 39221657 = 29416243) B29416243
theorem B1530271 : Blo 1528461 1530271 := bstep (se 1 (by rfl) ⟨1147703, by rfl⟩ : syracuseStep 1530271 = 2295407) B2295407
theorem B1530319 : Blo 1528461 1530319 := bstep (se 1 (by rfl) ⟨1147739, by rfl⟩ : syracuseStep 1530319 = 2295479) B2295479
theorem B1530343 : Blo 1528461 1530343 := bstep (se 1 (by rfl) ⟨1147757, by rfl⟩ : syracuseStep 1530343 = 2295515) B2295515
theorem B1530459 : Blo 1528461 1530459 := bstep (se 1 (by rfl) ⟨1147844, by rfl⟩ : syracuseStep 1530459 = 2295689) B2295689
theorem B9796241 : Blo 1528461 9796241 := bstep (se 2 (by rfl) ⟨3673590, by rfl⟩ : syracuseStep 9796241 = 7347181) B7347181
theorem B5806835 : Blo 1528461 5806835 := bstep (se 1 (by rfl) ⟨4355126, by rfl⟩ : syracuseStep 5806835 = 8710253) B8710253
theorem B2579323 : Blo 1528461 2579323 := bstep (se 1 (by rfl) ⟨1934492, by rfl⟩ : syracuseStep 2579323 = 3868985) B3868985
theorem B47111159 : Blo 1528461 47111159 := bstep (se 1 (by rfl) ⟨35333369, by rfl⟩ : syracuseStep 47111159 = 70666739) B70666739
theorem B5159969 : Blo 1528461 5159969 := bstep (se 2 (by rfl) ⟨1934988, by rfl⟩ : syracuseStep 5159969 = 3869977) B3869977
theorem B2292827 : Blo 1528461 2292827 := bstep (se 1 (by rfl) ⟨1719620, by rfl⟩ : syracuseStep 2292827 = 3439241) B3439241
theorem B6529015 : Blo 1528461 6529015 := bstep (se 1 (by rfl) ⟨4896761, by rfl⟩ : syracuseStep 6529015 = 9793523) B9793523
theorem B7347449 : Blo 1528461 7347449 := bstep (se 2 (by rfl) ⟨2755293, by rfl⟩ : syracuseStep 7347449 = 5510587) B5510587
theorem B2293199 : Blo 1528461 2293199 := bstep (se 1 (by rfl) ⟨1719899, by rfl⟩ : syracuseStep 2293199 = 3439799) B3439799
theorem B3440123 : Blo 1528461 3440123 := bstep (se 1 (by rfl) ⟨2580092, by rfl⟩ : syracuseStep 3440123 = 5160185) B5160185
theorem B3440303 : Blo 1528461 3440303 := bstep (se 1 (by rfl) ⟨2580227, by rfl⟩ : syracuseStep 3440303 = 5160455) B5160455
theorem B2580187 : Blo 1528461 2580187 := bstep (se 1 (by rfl) ⟨1935140, by rfl⟩ : syracuseStep 2580187 = 3870281) B3870281
theorem B5160671 : Blo 1528461 5160671 := bstep (se 1 (by rfl) ⟨3870503, by rfl⟩ : syracuseStep 5160671 = 7741007) B7741007
theorem B1720039 : Blo 1528461 1720039 := bstep (se 1 (by rfl) ⟨1290029, by rfl⟩ : syracuseStep 1720039 = 2580059) B2580059
theorem B3440393 : Blo 1528461 3440393 := bstep (se 2 (by rfl) ⟨1290147, by rfl⟩ : syracuseStep 3440393 = 2580295) B2580295
theorem B2293583 : Blo 1528461 2293583 := bstep (se 1 (by rfl) ⟨1720187, by rfl⟩ : syracuseStep 2293583 = 3440375) B3440375
theorem B6537149 : Blo 1528461 6537149 := bstep (se 3 (by rfl) ⟨1225715, by rfl⟩ : syracuseStep 6537149 = 2451431) B2451431
theorem B2293703 : Blo 1528461 2293703 := bstep (se 1 (by rfl) ⟨1720277, by rfl⟩ : syracuseStep 2293703 = 3440555) B3440555
theorem B5808095 : Blo 1528461 5808095 := bstep (se 1 (by rfl) ⟨4356071, by rfl⟩ : syracuseStep 5808095 = 8712143) B8712143
theorem B2580457 : Blo 1528461 2580457 := bstep (se 2 (by rfl) ⟨967671, by rfl⟩ : syracuseStep 2580457 = 1935343) B1935343
theorem B5161103 : Blo 1528461 5161103 := bstep (se 1 (by rfl) ⟨3870827, by rfl⟩ : syracuseStep 5161103 = 7741655) B7741655
theorem B15687827 : Blo 1528461 15687827 := bstep (se 1 (by rfl) ⟨11765870, by rfl⟩ : syracuseStep 15687827 = 23531741) B23531741
theorem B2294015 : Blo 1528461 2294015 := bstep (se 1 (by rfl) ⟨1720511, by rfl⟩ : syracuseStep 2294015 = 3441023) B3441023
theorem B3440915 : Blo 1528461 3440915 := bstep (se 1 (by rfl) ⟨2580686, by rfl⟩ : syracuseStep 3440915 = 5161373) B5161373
theorem B2294171 : Blo 1528461 2294171 := bstep (se 1 (by rfl) ⟨1720628, by rfl⟩ : syracuseStep 2294171 = 3441257) B3441257
theorem B9798239 : Blo 1528461 9798239 := bstep (se 1 (by rfl) ⟨7348679, by rfl⟩ : syracuseStep 9798239 = 14697359) B14697359
theorem B1721083 : Blo 1528461 1721083 := bstep (se 1 (by rfl) ⟨1290812, by rfl⟩ : syracuseStep 1721083 = 2581625) B2581625
theorem B19587865 : Blo 1528461 19587865 := bstep (se 2 (by rfl) ⟨7345449, by rfl⟩ : syracuseStep 19587865 = 14690899) B14690899
theorem B2294591 : Blo 1528461 2294591 := bstep (se 1 (by rfl) ⟨1720943, by rfl⟩ : syracuseStep 2294591 = 3441887) B3441887
theorem B3441545 : Blo 1528461 3441545 := bstep (se 2 (by rfl) ⟨1290579, by rfl⟩ : syracuseStep 3441545 = 2581159) B2581159
theorem B2294735 : Blo 1528461 2294735 := bstep (se 1 (by rfl) ⟨1721051, by rfl⟩ : syracuseStep 2294735 = 3442103) B3442103
theorem B2294825 : Blo 1528461 2294825 := bstep (se 2 (by rfl) ⟨860559, by rfl⟩ : syracuseStep 2294825 = 1721119) B1721119
theorem B23880763 : Blo 1528461 23880763 := bstep (se 1 (by rfl) ⟨17910572, by rfl⟩ : syracuseStep 23880763 = 35821145) B35821145
theorem B2294855 : Blo 1528461 2294855 := bstep (se 1 (by rfl) ⟨1721141, by rfl⟩ : syracuseStep 2294855 = 3442283) B3442283
theorem B2295035 : Blo 1528461 2295035 := bstep (se 1 (by rfl) ⟨1721276, by rfl⟩ : syracuseStep 2295035 = 3442553) B3442553
theorem B3441977 : Blo 1528461 3441977 := bstep (se 2 (by rfl) ⟨1290741, by rfl⟩ : syracuseStep 3441977 = 2581483) B2581483
theorem B2295323 : Blo 1528461 2295323 := bstep (se 1 (by rfl) ⟨1721492, by rfl⟩ : syracuseStep 2295323 = 3442985) B3442985
theorem B3442247 : Blo 1528461 3442247 := bstep (se 1 (by rfl) ⟨2581685, by rfl⟩ : syracuseStep 3442247 = 5163371) B5163371
theorem B39208535 : Blo 1528461 39208535 := bstep (se 1 (by rfl) ⟨29406401, by rfl⟩ : syracuseStep 39208535 = 58812803) B58812803
theorem B8709727 : Blo 1528461 8709727 := bstep (se 1 (by rfl) ⟨6532295, by rfl⟩ : syracuseStep 8709727 = 13064591) B13064591
theorem B3442427 : Blo 1528461 3442427 := bstep (se 1 (by rfl) ⟨2581820, by rfl⟩ : syracuseStep 3442427 = 5163641) B5163641
theorem B6530827 : Blo 1528461 6530827 := bstep (se 1 (by rfl) ⟨4898120, by rfl⟩ : syracuseStep 6530827 = 9796241) B9796241
theorem B83683277 : Blo 1528461 83683277 := bstep (se 3 (by rfl) ⟨15690614, by rfl⟩ : syracuseStep 83683277 = 31381229) B31381229
theorem B5163479 : Blo 1528461 5163479 := bstep (se 1 (by rfl) ⟨3872609, by rfl⟩ : syracuseStep 5163479 = 7745219) B7745219
theorem B2755063 : Blo 1528461 2755063 := bstep (se 1 (by rfl) ⟨2066297, by rfl⟩ : syracuseStep 2755063 = 4132595) B4132595
theorem B4353065 : Blo 1528461 4353065 := bstep (se 2 (by rfl) ⟨1632399, by rfl⟩ : syracuseStep 4353065 = 3264799) B3264799
theorem B5164073 : Blo 1528461 5164073 := bstep (se 2 (by rfl) ⟨1936527, by rfl⟩ : syracuseStep 5164073 = 3873055) B3873055
theorem B6532433 : Blo 1528461 6532433 := bstep (se 2 (by rfl) ⟨2449662, by rfl⟩ : syracuseStep 6532433 = 4899325) B4899325
theorem B6532775 : Blo 1528461 6532775 := bstep (se 1 (by rfl) ⟨4899581, by rfl⟩ : syracuseStep 6532775 = 9799163) B9799163
theorem B67989241 : Blo 1528461 67989241 := bstep (se 2 (by rfl) ⟨25495965, by rfl⟩ : syracuseStep 67989241 = 50991931) B50991931
theorem B18607967 : Blo 1528461 18607967 := bstep (se 1 (by rfl) ⟨13955975, by rfl⟩ : syracuseStep 18607967 = 27911951) B27911951
theorem B54415243 : Blo 1528461 54415243 := bstep (se 1 (by rfl) ⟨40811432, by rfl⟩ : syracuseStep 54415243 = 81622865) B81622865
theorem B9302035 : Blo 1528461 9302035 := bstep (se 1 (by rfl) ⟨6976526, by rfl⟩ : syracuseStep 9302035 = 13953053) B13953053
theorem B7352603 : Blo 1528461 7352603 := bstep (se 1 (by rfl) ⟨5514452, by rfl⟩ : syracuseStep 7352603 = 11028905) B11028905
theorem B3871223 : Blo 1528461 3871223 := bstep (se 1 (by rfl) ⟨2903417, by rfl⟩ : syracuseStep 3871223 = 5806835) B5806835
theorem B1528551 : Blo 1528461 1528551 := bstep (se 1 (by rfl) ⟨1146413, by rfl⟩ : syracuseStep 1528551 = 2292827) B2292827
theorem B7746515 : Blo 1528461 7746515 := bstep (se 1 (by rfl) ⟨5809886, by rfl⟩ : syracuseStep 7746515 = 11619773) B11619773
theorem B1528799 : Blo 1528461 1528799 := bstep (se 1 (by rfl) ⟨1146599, by rfl⟩ : syracuseStep 1528799 = 2293199) B2293199
theorem B74396819 : Blo 1528461 74396819 := bstep (se 1 (by rfl) ⟨55797614, by rfl⟩ : syracuseStep 74396819 = 111595229) B111595229
theorem B1529055 : Blo 1528461 1529055 := bstep (se 1 (by rfl) ⟨1146791, by rfl⟩ : syracuseStep 1529055 = 2293583) B2293583
theorem B1529135 : Blo 1528461 1529135 := bstep (se 1 (by rfl) ⟨1146851, by rfl⟩ : syracuseStep 1529135 = 2293703) B2293703
theorem B3872063 : Blo 1528461 3872063 := bstep (se 1 (by rfl) ⟨2904047, by rfl⟩ : syracuseStep 3872063 = 5808095) B5808095
theorem B8705353 : Blo 1528461 8705353 := bstep (se 2 (by rfl) ⟨3264507, by rfl⟩ : syracuseStep 8705353 = 6529015) B6529015
theorem B44103041 : Blo 1528461 44103041 := bstep (se 2 (by rfl) ⟨16538640, by rfl⟩ : syracuseStep 44103041 = 33077281) B33077281
theorem B33076667 : Blo 1528461 33076667 := bstep (se 1 (by rfl) ⟨24807500, by rfl⟩ : syracuseStep 33076667 = 49615001) B49615001
theorem B27907577 : Blo 1528461 27907577 := bstep (se 2 (by rfl) ⟨10465341, by rfl⟩ : syracuseStep 27907577 = 20930683) B20930683
theorem B1529375 : Blo 1528461 1529375 := bstep (se 1 (by rfl) ⟨1147031, by rfl⟩ : syracuseStep 1529375 = 2294063) B2294063
theorem B9795163 : Blo 1528461 9795163 := bstep (se 1 (by rfl) ⟨7346372, by rfl⟩ : syracuseStep 9795163 = 14692745) B14692745
theorem B7747163 : Blo 1528461 7747163 := bstep (se 1 (by rfl) ⟨5810372, by rfl⟩ : syracuseStep 7747163 = 11620745) B11620745
theorem B7739063 : Blo 1528461 7739063 := bstep (se 1 (by rfl) ⟨5804297, by rfl⟩ : syracuseStep 7739063 = 11608595) B11608595
theorem B1529535 : Blo 1528461 1529535 := bstep (se 1 (by rfl) ⟨1147151, by rfl⟩ : syracuseStep 1529535 = 2294303) B2294303
theorem B5158619 : Blo 1528461 5158619 := bstep (se 1 (by rfl) ⟨3868964, by rfl⟩ : syracuseStep 5158619 = 7737929) B7737929
theorem B12400445 : Blo 1528461 12400445 := bstep (se 3 (by rfl) ⟨2325083, by rfl⟩ : syracuseStep 12400445 = 4650167) B4650167
theorem B3872711 : Blo 1528461 3872711 := bstep (se 1 (by rfl) ⟨2904533, by rfl⟩ : syracuseStep 3872711 = 5809067) B5809067
theorem B19593197 : Blo 1528461 19593197 := bstep (se 3 (by rfl) ⟨3673724, by rfl⟩ : syracuseStep 19593197 = 7347449) B7347449
theorem B6535151 : Blo 1528461 6535151 := bstep (se 1 (by rfl) ⟨4901363, by rfl⟩ : syracuseStep 6535151 = 9802727) B9802727
theorem B27228149 : Blo 1528461 27228149 := bstep (se 5 (by rfl) ⟨1276319, by rfl⟩ : syracuseStep 27228149 = 2552639) B2552639
theorem B1529983 : Blo 1528461 1529983 := bstep (se 1 (by rfl) ⟨1147487, by rfl⟩ : syracuseStep 1529983 = 2294975) B2294975
theorem B1530079 : Blo 1528461 1530079 := bstep (se 1 (by rfl) ⟨1147559, by rfl⟩ : syracuseStep 1530079 = 2295119) B2295119
theorem B8706311 : Blo 1528461 8706311 := bstep (se 1 (by rfl) ⟨6529733, by rfl⟩ : syracuseStep 8706311 = 13059467) B13059467
theorem B1530139 : Blo 1528461 1530139 := bstep (se 1 (by rfl) ⟨1147604, by rfl⟩ : syracuseStep 1530139 = 2295209) B2295209
theorem B1530239 : Blo 1528461 1530239 := bstep (se 1 (by rfl) ⟨1147679, by rfl⟩ : syracuseStep 1530239 = 2295359) B2295359
theorem B1530267 : Blo 1528461 1530267 := bstep (se 1 (by rfl) ⟨1147700, by rfl⟩ : syracuseStep 1530267 = 2295401) B2295401
theorem B3439097 : Blo 1528461 3439097 := bstep (se 2 (by rfl) ⟨1289661, by rfl⟩ : syracuseStep 3439097 = 2579323) B2579323
theorem B22059539 : Blo 1528461 22059539 := bstep (se 1 (by rfl) ⟨16544654, by rfl⟩ : syracuseStep 22059539 = 33089309) B33089309
theorem B3439187 : Blo 1528461 3439187 := bstep (se 1 (by rfl) ⟨2579390, by rfl⟩ : syracuseStep 3439187 = 5158781) B5158781
theorem B3439367 : Blo 1528461 3439367 := bstep (se 1 (by rfl) ⟨2579525, by rfl⟩ : syracuseStep 3439367 = 5159051) B5159051
theorem B62798611 : Blo 1528461 62798611 := bstep (se 1 (by rfl) ⟨47098958, by rfl⟩ : syracuseStep 62798611 = 94197917) B94197917
theorem B2579303 : Blo 1528461 2579303 := bstep (se 1 (by rfl) ⟨1934477, by rfl⟩ : syracuseStep 2579303 = 3868955) B3868955
theorem B26147771 : Blo 1528461 26147771 := bstep (se 1 (by rfl) ⟨19610828, by rfl⟩ : syracuseStep 26147771 = 39221657) B39221657
theorem B2579519 : Blo 1528461 2579519 := bstep (se 1 (by rfl) ⟨1934639, by rfl⟩ : syracuseStep 2579519 = 3869279) B3869279
theorem B2833481 : Blo 1528461 2833481 := bstep (se 2 (by rfl) ⟨1062555, by rfl⟩ : syracuseStep 2833481 = 2125111) B2125111
theorem B14900381 : Blo 1528461 14900381 := bstep (se 3 (by rfl) ⟨2793821, by rfl⟩ : syracuseStep 14900381 = 5587643) B5587643
theorem B8707337 : Blo 1528461 8707337 := bstep (se 2 (by rfl) ⟨3265251, by rfl⟩ : syracuseStep 8707337 = 6530503) B6530503
theorem B31407439 : Blo 1528461 31407439 := bstep (se 1 (by rfl) ⟨23555579, by rfl⟩ : syracuseStep 31407439 = 47111159) B47111159
theorem B3439979 : Blo 1528461 3439979 := bstep (se 1 (by rfl) ⟨2579984, by rfl⟩ : syracuseStep 3439979 = 5159969) B5159969
theorem B3440249 : Blo 1528461 3440249 := bstep (se 2 (by rfl) ⟨1290093, by rfl⟩ : syracuseStep 3440249 = 2580187) B2580187
theorem B2293385 : Blo 1528461 2293385 := bstep (se 2 (by rfl) ⟨860019, by rfl⟩ : syracuseStep 2293385 = 1720039) B1720039
theorem B14696093 : Blo 1528461 14696093 := bstep (se 3 (by rfl) ⟨2755517, by rfl⟩ : syracuseStep 14696093 = 5511035) B5511035
theorem B2293415 : Blo 1528461 2293415 := bstep (se 1 (by rfl) ⟨1720061, by rfl⟩ : syracuseStep 2293415 = 3440123) B3440123
theorem B2293535 : Blo 1528461 2293535 := bstep (se 1 (by rfl) ⟨1720151, by rfl⟩ : syracuseStep 2293535 = 3440303) B3440303
theorem B3440447 : Blo 1528461 3440447 := bstep (se 1 (by rfl) ⟨2580335, by rfl⟩ : syracuseStep 3440447 = 5160671) B5160671
theorem B2293595 : Blo 1528461 2293595 := bstep (se 1 (by rfl) ⟨1720196, by rfl⟩ : syracuseStep 2293595 = 3440393) B3440393
theorem B4358099 : Blo 1528461 4358099 := bstep (se 1 (by rfl) ⟨3268574, by rfl⟩ : syracuseStep 4358099 = 6537149) B6537149
theorem B3440609 : Blo 1528461 3440609 := bstep (se 2 (by rfl) ⟨1290228, by rfl⟩ : syracuseStep 3440609 = 2580457) B2580457
theorem B12402713 : Blo 1528461 12402713 := bstep (se 2 (by rfl) ⟨4651017, by rfl⟩ : syracuseStep 12402713 = 9302035) B9302035
theorem B3440735 : Blo 1528461 3440735 := bstep (se 1 (by rfl) ⟨2580551, by rfl⟩ : syracuseStep 3440735 = 5161103) B5161103
theorem B2293943 : Blo 1528461 2293943 := bstep (se 1 (by rfl) ⟨1720457, by rfl⟩ : syracuseStep 2293943 = 3440915) B3440915
theorem B2580815 : Blo 1528461 2580815 := bstep (se 1 (by rfl) ⟨1935611, by rfl⟩ : syracuseStep 2580815 = 3871223) B3871223
theorem B2294363 : Blo 1528461 2294363 := bstep (se 1 (by rfl) ⟨1720772, by rfl⟩ : syracuseStep 2294363 = 3441545) B3441545
theorem B2294651 : Blo 1528461 2294651 := bstep (se 1 (by rfl) ⟨1720988, by rfl⟩ : syracuseStep 2294651 = 3441977) B3441977
theorem B2581375 : Blo 1528461 2581375 := bstep (se 1 (by rfl) ⟨1936031, by rfl⟩ : syracuseStep 2581375 = 3872063) B3872063
theorem B29402027 : Blo 1528461 29402027 := bstep (se 1 (by rfl) ⟨22051520, by rfl⟩ : syracuseStep 29402027 = 44103041) B44103041
theorem B2294777 : Blo 1528461 2294777 := bstep (se 2 (by rfl) ⟨860541, by rfl⟩ : syracuseStep 2294777 = 1721083) B1721083
theorem B18605051 : Blo 1528461 18605051 := bstep (se 1 (by rfl) ⟨13953788, by rfl⟩ : syracuseStep 18605051 = 27907577) B27907577
theorem B83731481 : Blo 1528461 83731481 := bstep (se 2 (by rfl) ⟨31399305, by rfl⟩ : syracuseStep 83731481 = 62798611) B62798611
theorem B26117153 : Blo 1528461 26117153 := bstep (se 2 (by rfl) ⟨9793932, by rfl⟩ : syracuseStep 26117153 = 19587865) B19587865
theorem B2294831 : Blo 1528461 2294831 := bstep (se 1 (by rfl) ⟨1721123, by rfl⟩ : syracuseStep 2294831 = 3442247) B3442247
theorem B2294951 : Blo 1528461 2294951 := bstep (se 1 (by rfl) ⟨1721213, by rfl⟩ : syracuseStep 2294951 = 3442427) B3442427
theorem B8266963 : Blo 1528461 8266963 := bstep (se 1 (by rfl) ⟨6200222, by rfl⟩ : syracuseStep 8266963 = 12400445) B12400445
theorem B2581807 : Blo 1528461 2581807 := bstep (se 1 (by rfl) ⟨1936355, by rfl⟩ : syracuseStep 2581807 = 3872711) B3872711
theorem B55788851 : Blo 1528461 55788851 := bstep (se 1 (by rfl) ⟨41841638, by rfl⟩ : syracuseStep 55788851 = 83683277) B83683277
theorem B3442319 : Blo 1528461 3442319 := bstep (se 1 (by rfl) ⟨2581739, by rfl⟩ : syracuseStep 3442319 = 5163479) B5163479
theorem B14706359 : Blo 1528461 14706359 := bstep (se 1 (by rfl) ⟨11029769, by rfl⟩ : syracuseStep 14706359 = 22059539) B22059539
theorem B2902043 : Blo 1528461 2902043 := bstep (se 1 (by rfl) ⟨2176532, by rfl⟩ : syracuseStep 2902043 = 4353065) B4353065
theorem B3442715 : Blo 1528461 3442715 := bstep (se 1 (by rfl) ⟨2582036, by rfl⟩ : syracuseStep 3442715 = 5164073) B5164073
theorem B13060217 : Blo 1528461 13060217 := bstep (se 2 (by rfl) ⟨4897581, by rfl⟩ : syracuseStep 13060217 = 9795163) B9795163
theorem B12405311 : Blo 1528461 12405311 := bstep (se 1 (by rfl) ⟨9303983, by rfl⟩ : syracuseStep 12405311 = 18607967) B18607967
theorem B4901735 : Blo 1528461 4901735 := bstep (se 1 (by rfl) ⟨3676301, by rfl⟩ : syracuseStep 4901735 = 7352603) B7352603
theorem B7555949 : Blo 1528461 7555949 := bstep (se 3 (by rfl) ⟨1416740, by rfl⟩ : syracuseStep 7555949 = 2833481) B2833481
theorem B127364069 : Blo 1528461 127364069 := bstep (se 4 (by rfl) ⟨11940381, by rfl⟩ : syracuseStep 127364069 = 23880763) B23880763
theorem B6532159 : Blo 1528461 6532159 := bstep (se 1 (by rfl) ⟨4899119, by rfl⟩ : syracuseStep 6532159 = 9798239) B9798239
theorem B5164343 : Blo 1528461 5164343 := bstep (se 1 (by rfl) ⟨3873257, by rfl⟩ : syracuseStep 5164343 = 7746515) B7746515
theorem B49597879 : Blo 1528461 49597879 := bstep (se 1 (by rfl) ⟨37198409, by rfl⟩ : syracuseStep 49597879 = 74396819) B74396819
theorem B5164775 : Blo 1528461 5164775 := bstep (se 1 (by rfl) ⟨3873581, by rfl⟩ : syracuseStep 5164775 = 7747163) B7747163
theorem B13062131 : Blo 1528461 13062131 := bstep (se 1 (by rfl) ⟨9796598, by rfl⟩ : syracuseStep 13062131 = 19593197) B19593197
theorem B5804207 : Blo 1528461 5804207 := bstep (se 1 (by rfl) ⟨4353155, by rfl⟩ : syracuseStep 5804207 = 8706311) B8706311
theorem B9933587 : Blo 1528461 9933587 := bstep (se 1 (by rfl) ⟨7450190, by rfl⟩ : syracuseStep 9933587 = 14900381) B14900381
theorem B11612969 : Blo 1528461 11612969 := bstep (se 2 (by rfl) ⟨4354863, by rfl⟩ : syracuseStep 11612969 = 8709727) B8709727
theorem B5804891 : Blo 1528461 5804891 := bstep (se 1 (by rfl) ⟨4353668, by rfl⟩ : syracuseStep 5804891 = 8707337) B8707337
theorem B4354955 : Blo 1528461 4354955 := bstep (se 1 (by rfl) ⟨3266216, by rfl⟩ : syracuseStep 4354955 = 6532433) B6532433
theorem B1528923 : Blo 1528461 1528923 := bstep (se 1 (by rfl) ⟨1146692, by rfl⟩ : syracuseStep 1528923 = 2293385) B2293385
theorem B1528943 : Blo 1528461 1528943 := bstep (se 1 (by rfl) ⟨1146707, by rfl⟩ : syracuseStep 1528943 = 2293415) B2293415
theorem B4355183 : Blo 1528461 4355183 := bstep (se 1 (by rfl) ⟨3266387, by rfl⟩ : syracuseStep 4355183 = 6532775) B6532775
theorem B72553657 : Blo 1528461 72553657 := bstep (se 2 (by rfl) ⟨27207621, by rfl⟩ : syracuseStep 72553657 = 54415243) B54415243
theorem B1529023 : Blo 1528461 1529023 := bstep (se 1 (by rfl) ⟨1146767, by rfl⟩ : syracuseStep 1529023 = 2293535) B2293535
theorem B1529063 : Blo 1528461 1529063 := bstep (se 1 (by rfl) ⟨1146797, by rfl⟩ : syracuseStep 1529063 = 2293595) B2293595
theorem B14693669 : Blo 1528461 14693669 := bstep (se 4 (by rfl) ⟨1377531, by rfl⟩ : syracuseStep 14693669 = 2755063) B2755063
theorem B2905399 : Blo 1528461 2905399 := bstep (se 1 (by rfl) ⟨2179049, by rfl⟩ : syracuseStep 2905399 = 4358099) B4358099
theorem B10458551 : Blo 1528461 10458551 := bstep (se 1 (by rfl) ⟨7843913, by rfl⟩ : syracuseStep 10458551 = 15687827) B15687827
theorem B1529343 : Blo 1528461 1529343 := bstep (se 1 (by rfl) ⟨1147007, by rfl⟩ : syracuseStep 1529343 = 2294015) B2294015
theorem B1529447 : Blo 1528461 1529447 := bstep (se 1 (by rfl) ⟨1147085, by rfl⟩ : syracuseStep 1529447 = 2294171) B2294171
theorem B1529727 : Blo 1528461 1529727 := bstep (se 1 (by rfl) ⟨1147295, by rfl⟩ : syracuseStep 1529727 = 2294591) B2294591
theorem B1529823 : Blo 1528461 1529823 := bstep (se 1 (by rfl) ⟨1147367, by rfl⟩ : syracuseStep 1529823 = 2294735) B2294735
theorem B1529883 : Blo 1528461 1529883 := bstep (se 1 (by rfl) ⟨1147412, by rfl⟩ : syracuseStep 1529883 = 2294825) B2294825
theorem B1529903 : Blo 1528461 1529903 := bstep (se 1 (by rfl) ⟨1147427, by rfl⟩ : syracuseStep 1529903 = 2294855) B2294855
theorem B1530023 : Blo 1528461 1530023 := bstep (se 1 (by rfl) ⟨1147517, by rfl⟩ : syracuseStep 1530023 = 2295035) B2295035
theorem B22051111 : Blo 1528461 22051111 := bstep (se 1 (by rfl) ⟨16538333, by rfl⟩ : syracuseStep 22051111 = 33076667) B33076667
theorem B1530215 : Blo 1528461 1530215 := bstep (se 1 (by rfl) ⟨1147661, by rfl⟩ : syracuseStep 1530215 = 2295323) B2295323
theorem B26139023 : Blo 1528461 26139023 := bstep (se 1 (by rfl) ⟨19604267, by rfl⟩ : syracuseStep 26139023 = 39208535) B39208535
theorem B5159375 : Blo 1528461 5159375 := bstep (se 1 (by rfl) ⟨3869531, by rfl⟩ : syracuseStep 5159375 = 7739063) B7739063
theorem B3439079 : Blo 1528461 3439079 := bstep (se 1 (by rfl) ⟨2579309, by rfl⟩ : syracuseStep 3439079 = 5158619) B5158619
theorem B4356767 : Blo 1528461 4356767 := bstep (se 1 (by rfl) ⟨3267575, by rfl⟩ : syracuseStep 4356767 = 6535151) B6535151
theorem B18152099 : Blo 1528461 18152099 := bstep (se 1 (by rfl) ⟨13614074, by rfl⟩ : syracuseStep 18152099 = 27228149) B27228149
theorem B2292731 : Blo 1528461 2292731 := bstep (se 1 (by rfl) ⟨1719548, by rfl⟩ : syracuseStep 2292731 = 3439097) B3439097
theorem B2292791 : Blo 1528461 2292791 := bstep (se 1 (by rfl) ⟨1719593, by rfl⟩ : syracuseStep 2292791 = 3439187) B3439187
theorem B11607137 : Blo 1528461 11607137 := bstep (se 2 (by rfl) ⟨4352676, by rfl⟩ : syracuseStep 11607137 = 8705353) B8705353
theorem B41876585 : Blo 1528461 41876585 := bstep (se 2 (by rfl) ⟨15703719, by rfl⟩ : syracuseStep 41876585 = 31407439) B31407439
theorem B2292911 : Blo 1528461 2292911 := bstep (se 1 (by rfl) ⟨1719683, by rfl⟩ : syracuseStep 2292911 = 3439367) B3439367
theorem B1719535 : Blo 1528461 1719535 := bstep (se 1 (by rfl) ⟨1289651, by rfl⟩ : syracuseStep 1719535 = 2579303) B2579303
theorem B17431847 : Blo 1528461 17431847 := bstep (se 1 (by rfl) ⟨13073885, by rfl⟩ : syracuseStep 17431847 = 26147771) B26147771
theorem B1719679 : Blo 1528461 1719679 := bstep (se 1 (by rfl) ⟨1289759, by rfl⟩ : syracuseStep 1719679 = 2579519) B2579519
theorem B2293319 : Blo 1528461 2293319 := bstep (se 1 (by rfl) ⟨1719989, by rfl⟩ : syracuseStep 2293319 = 3439979) B3439979
theorem B90652321 : Blo 1528461 90652321 := bstep (se 2 (by rfl) ⟨33994620, by rfl⟩ : syracuseStep 90652321 = 67989241) B67989241
theorem B8707769 : Blo 1528461 8707769 := bstep (se 2 (by rfl) ⟨3265413, by rfl⟩ : syracuseStep 8707769 = 6530827) B6530827
theorem B2293499 : Blo 1528461 2293499 := bstep (se 1 (by rfl) ⟨1720124, by rfl⟩ : syracuseStep 2293499 = 3440249) B3440249
theorem B9797395 : Blo 1528461 9797395 := bstep (se 1 (by rfl) ⟨7348046, by rfl⟩ : syracuseStep 9797395 = 14696093) B14696093
theorem B2293631 : Blo 1528461 2293631 := bstep (se 1 (by rfl) ⟨1720223, by rfl⟩ : syracuseStep 2293631 = 3440447) B3440447
theorem B2293739 : Blo 1528461 2293739 := bstep (se 1 (by rfl) ⟨1720304, by rfl⟩ : syracuseStep 2293739 = 3440609) B3440609
theorem B2293823 : Blo 1528461 2293823 := bstep (se 1 (by rfl) ⟨1720367, by rfl⟩ : syracuseStep 2293823 = 3440735) B3440735
theorem B1720543 : Blo 1528461 1720543 := bstep (se 1 (by rfl) ⟨1290407, by rfl⟩ : syracuseStep 1720543 = 2580815) B2580815
theorem B29401481 : Blo 1528461 29401481 := bstep (se 2 (by rfl) ⟨11025555, by rfl⟩ : syracuseStep 29401481 = 22051111) B22051111
theorem B7741979 : Blo 1528461 7741979 := bstep (se 1 (by rfl) ⟨5806484, by rfl⟩ : syracuseStep 7741979 = 11612969) B11612969
theorem B12403367 : Blo 1528461 12403367 := bstep (se 1 (by rfl) ⟨9302525, by rfl⟩ : syracuseStep 12403367 = 18605051) B18605051
theorem B55820987 : Blo 1528461 55820987 := bstep (se 1 (by rfl) ⟨41865740, by rfl⟩ : syracuseStep 55820987 = 83731481) B83731481
theorem B37192567 : Blo 1528461 37192567 := bstep (se 1 (by rfl) ⟨27894425, by rfl⟩ : syracuseStep 37192567 = 55788851) B55788851
theorem B6972367 : Blo 1528461 6972367 := bstep (se 1 (by rfl) ⟨5229275, by rfl⟩ : syracuseStep 6972367 = 10458551) B10458551
theorem B2294879 : Blo 1528461 2294879 := bstep (se 1 (by rfl) ⟨1721159, by rfl⟩ : syracuseStep 2294879 = 3442319) B3442319
theorem B3441833 : Blo 1528461 3441833 := bstep (se 2 (by rfl) ⟨1290687, by rfl⟩ : syracuseStep 3441833 = 2581375) B2581375
theorem B1934695 : Blo 1528461 1934695 := bstep (se 1 (by rfl) ⟨1451021, by rfl⟩ : syracuseStep 1934695 = 2902043) B2902043
theorem B2295143 : Blo 1528461 2295143 := bstep (se 1 (by rfl) ⟨1721357, by rfl⟩ : syracuseStep 2295143 = 3442715) B3442715
theorem B8709545 : Blo 1528461 8709545 := bstep (se 2 (by rfl) ⟨3266079, by rfl⟩ : syracuseStep 8709545 = 6532159) B6532159
theorem B17426015 : Blo 1528461 17426015 := bstep (se 1 (by rfl) ⟨13069511, by rfl⟩ : syracuseStep 17426015 = 26139023) B26139023
theorem B3442409 : Blo 1528461 3442409 := bstep (se 2 (by rfl) ⟨1290903, by rfl⟩ : syracuseStep 3442409 = 2581807) B2581807
theorem B12101399 : Blo 1528461 12101399 := bstep (se 1 (by rfl) ⟨9076049, by rfl⟩ : syracuseStep 12101399 = 18152099) B18152099
theorem B3442895 : Blo 1528461 3442895 := bstep (se 1 (by rfl) ⟨2582171, by rfl⟩ : syracuseStep 3442895 = 5164343) B5164343
theorem B3443183 : Blo 1528461 3443183 := bstep (se 1 (by rfl) ⟨2582387, by rfl⟩ : syracuseStep 3443183 = 5164775) B5164775
theorem B8268475 : Blo 1528461 8268475 := bstep (se 1 (by rfl) ⟨6201356, by rfl⟩ : syracuseStep 8268475 = 12402713) B12402713
theorem B3869471 : Blo 1528461 3869471 := bstep (se 1 (by rfl) ⟨2902103, by rfl⟩ : syracuseStep 3869471 = 5804207) B5804207
theorem B6622391 : Blo 1528461 6622391 := bstep (se 1 (by rfl) ⟨4966793, by rfl⟩ : syracuseStep 6622391 = 9933587) B9933587
theorem B3869927 : Blo 1528461 3869927 := bstep (se 1 (by rfl) ⟨2902445, by rfl⟩ : syracuseStep 3869927 = 5804891) B5804891
theorem B2903303 : Blo 1528461 2903303 := bstep (se 1 (by rfl) ⟨2177477, by rfl⟩ : syracuseStep 2903303 = 4354955) B4354955
theorem B17411435 : Blo 1528461 17411435 := bstep (se 1 (by rfl) ⟨13058576, by rfl⟩ : syracuseStep 17411435 = 26117153) B26117153
theorem B2903455 : Blo 1528461 2903455 := bstep (se 1 (by rfl) ⟨2177591, by rfl⟩ : syracuseStep 2903455 = 4355183) B4355183
theorem B11022617 : Blo 1528461 11022617 := bstep (se 2 (by rfl) ⟨4133481, by rfl⟩ : syracuseStep 11022617 = 8266963) B8266963
theorem B8270207 : Blo 1528461 8270207 := bstep (se 1 (by rfl) ⟨6202655, by rfl⟩ : syracuseStep 8270207 = 12405311) B12405311
theorem B2904511 : Blo 1528461 2904511 := bstep (se 1 (by rfl) ⟨2178383, by rfl⟩ : syracuseStep 2904511 = 4356767) B4356767
theorem B66130505 : Blo 1528461 66130505 := bstep (se 2 (by rfl) ⟨24798939, by rfl⟩ : syracuseStep 66130505 = 49597879) B49597879
theorem B1528487 : Blo 1528461 1528487 := bstep (se 1 (by rfl) ⟨1146365, by rfl⟩ : syracuseStep 1528487 = 2292731) B2292731
theorem B1528527 : Blo 1528461 1528527 := bstep (se 1 (by rfl) ⟨1146395, by rfl⟩ : syracuseStep 1528527 = 2292791) B2292791
theorem B7738091 : Blo 1528461 7738091 := bstep (se 1 (by rfl) ⟨5803568, by rfl⟩ : syracuseStep 7738091 = 11607137) B11607137
theorem B1528607 : Blo 1528461 1528607 := bstep (se 1 (by rfl) ⟨1146455, by rfl⟩ : syracuseStep 1528607 = 2292911) B2292911
theorem B11621231 : Blo 1528461 11621231 := bstep (se 1 (by rfl) ⟨8715923, by rfl⟩ : syracuseStep 11621231 = 17431847) B17431847
theorem B120869761 : Blo 1528461 120869761 := bstep (se 2 (by rfl) ⟨45326160, by rfl⟩ : syracuseStep 120869761 = 90652321) B90652321
theorem B13063193 : Blo 1528461 13063193 := bstep (se 2 (by rfl) ⟨4898697, by rfl⟩ : syracuseStep 13063193 = 9797395) B9797395
theorem B1528879 : Blo 1528461 1528879 := bstep (se 1 (by rfl) ⟨1146659, by rfl⟩ : syracuseStep 1528879 = 2293319) B2293319
theorem B5805179 : Blo 1528461 5805179 := bstep (se 1 (by rfl) ⟨4353884, by rfl⟩ : syracuseStep 5805179 = 8707769) B8707769
theorem B1528999 : Blo 1528461 1528999 := bstep (se 1 (by rfl) ⟨1146749, by rfl⟩ : syracuseStep 1528999 = 2293499) B2293499
theorem B1529087 : Blo 1528461 1529087 := bstep (se 1 (by rfl) ⟨1146815, by rfl⟩ : syracuseStep 1529087 = 2293631) B2293631
theorem B1529159 : Blo 1528461 1529159 := bstep (se 1 (by rfl) ⟨1146869, by rfl⟩ : syracuseStep 1529159 = 2293739) B2293739
theorem B1529295 : Blo 1528461 1529295 := bstep (se 1 (by rfl) ⟨1146971, by rfl⟩ : syracuseStep 1529295 = 2293943) B2293943
theorem B1529575 : Blo 1528461 1529575 := bstep (se 1 (by rfl) ⟨1147181, by rfl⟩ : syracuseStep 1529575 = 2294363) B2294363
theorem B1529767 : Blo 1528461 1529767 := bstep (se 1 (by rfl) ⟨1147325, by rfl⟩ : syracuseStep 1529767 = 2294651) B2294651
theorem B19601351 : Blo 1528461 19601351 := bstep (se 1 (by rfl) ⟨14701013, by rfl⟩ : syracuseStep 19601351 = 29402027) B29402027
theorem B1529851 : Blo 1528461 1529851 := bstep (se 1 (by rfl) ⟨1147388, by rfl⟩ : syracuseStep 1529851 = 2294777) B2294777
theorem B1529887 : Blo 1528461 1529887 := bstep (se 1 (by rfl) ⟨1147415, by rfl⟩ : syracuseStep 1529887 = 2294831) B2294831
theorem B1529967 : Blo 1528461 1529967 := bstep (se 1 (by rfl) ⟨1147475, by rfl⟩ : syracuseStep 1529967 = 2294951) B2294951
theorem B9795779 : Blo 1528461 9795779 := bstep (se 1 (by rfl) ⟨7346834, by rfl⟩ : syracuseStep 9795779 = 14693669) B14693669
theorem B9804239 : Blo 1528461 9804239 := bstep (se 1 (by rfl) ⟨7353179, by rfl⟩ : syracuseStep 9804239 = 14706359) B14706359
theorem B8706811 : Blo 1528461 8706811 := bstep (se 1 (by rfl) ⟨6530108, by rfl⟩ : syracuseStep 8706811 = 13060217) B13060217
theorem B96738209 : Blo 1528461 96738209 := bstep (se 2 (by rfl) ⟨36276828, by rfl⟩ : syracuseStep 96738209 = 72553657) B72553657
theorem B3439583 : Blo 1528461 3439583 := bstep (se 1 (by rfl) ⟨2579687, by rfl⟩ : syracuseStep 3439583 = 5159375) B5159375
theorem B2292713 : Blo 1528461 2292713 := bstep (se 2 (by rfl) ⟨859767, by rfl⟩ : syracuseStep 2292713 = 1719535) B1719535
theorem B2292719 : Blo 1528461 2292719 := bstep (se 1 (by rfl) ⟨1719539, by rfl⟩ : syracuseStep 2292719 = 3439079) B3439079
theorem B3873865 : Blo 1528461 3873865 := bstep (se 2 (by rfl) ⟨1452699, by rfl⟩ : syracuseStep 3873865 = 2905399) B2905399
theorem B2292905 : Blo 1528461 2292905 := bstep (se 2 (by rfl) ⟨859839, by rfl⟩ : syracuseStep 2292905 = 1719679) B1719679
theorem B3267823 : Blo 1528461 3267823 := bstep (se 1 (by rfl) ⟨2450867, by rfl⟩ : syracuseStep 3267823 = 4901735) B4901735
theorem B5037299 : Blo 1528461 5037299 := bstep (se 1 (by rfl) ⟨3777974, by rfl⟩ : syracuseStep 5037299 = 7555949) B7555949
theorem B84909379 : Blo 1528461 84909379 := bstep (se 1 (by rfl) ⟨63682034, by rfl⟩ : syracuseStep 84909379 = 127364069) B127364069
theorem B27917723 : Blo 1528461 27917723 := bstep (se 1 (by rfl) ⟨20938292, by rfl⟩ : syracuseStep 27917723 = 41876585) B41876585
theorem B8708087 : Blo 1528461 8708087 := bstep (se 1 (by rfl) ⟨6531065, by rfl⟩ : syracuseStep 8708087 = 13062131) B13062131
theorem B7348411 : Blo 1528461 7348411 := bstep (se 1 (by rfl) ⟨5511308, by rfl⟩ : syracuseStep 7348411 = 11022617) B11022617
theorem B5513471 : Blo 1528461 5513471 := bstep (se 1 (by rfl) ⟨4135103, by rfl⟩ : syracuseStep 5513471 = 8270207) B8270207
theorem B2294057 : Blo 1528461 2294057 := bstep (se 2 (by rfl) ⟨860271, by rfl⟩ : syracuseStep 2294057 = 1720543) B1720543
theorem B5161319 : Blo 1528461 5161319 := bstep (se 1 (by rfl) ⟨3870989, by rfl⟩ : syracuseStep 5161319 = 7741979) B7741979
theorem B8708795 : Blo 1528461 8708795 := bstep (se 1 (by rfl) ⟨6531596, by rfl⟩ : syracuseStep 8708795 = 13063193) B13063193
theorem B7742141 : Blo 1528461 7742141 := bstep (se 3 (by rfl) ⟨1451651, by rfl⟩ : syracuseStep 7742141 = 2903303) B2903303
theorem B2294555 : Blo 1528461 2294555 := bstep (se 1 (by rfl) ⟨1720916, by rfl⟩ : syracuseStep 2294555 = 3441833) B3441833
theorem B11609081 : Blo 1528461 11609081 := bstep (se 2 (by rfl) ⟨4353405, by rfl⟩ : syracuseStep 11609081 = 8706811) B8706811
theorem B11617343 : Blo 1528461 11617343 := bstep (se 1 (by rfl) ⟨8713007, by rfl⟩ : syracuseStep 11617343 = 17426015) B17426015
theorem B2294939 : Blo 1528461 2294939 := bstep (se 1 (by rfl) ⟨1721204, by rfl⟩ : syracuseStep 2294939 = 3442409) B3442409
theorem B13067567 : Blo 1528461 13067567 := bstep (se 1 (by rfl) ⟨9800675, by rfl⟩ : syracuseStep 13067567 = 19601351) B19601351
theorem B6530519 : Blo 1528461 6530519 := bstep (se 1 (by rfl) ⟨4897889, by rfl⟩ : syracuseStep 6530519 = 9795779) B9795779
theorem B2295263 : Blo 1528461 2295263 := bstep (se 1 (by rfl) ⟨1721447, by rfl⟩ : syracuseStep 2295263 = 3442895) B3442895
theorem B2295455 : Blo 1528461 2295455 := bstep (se 1 (by rfl) ⟨1721591, by rfl⟩ : syracuseStep 2295455 = 3443183) B3443183
theorem B8268911 : Blo 1528461 8268911 := bstep (se 1 (by rfl) ⟨6201683, by rfl⟩ : syracuseStep 8268911 = 12403367) B12403367
theorem B3870119 : Blo 1528461 3870119 := bstep (se 1 (by rfl) ⟨2902589, by rfl⟩ : syracuseStep 3870119 = 5805179) B5805179
theorem B49590089 : Blo 1528461 49590089 := bstep (se 2 (by rfl) ⟨18596283, by rfl⟩ : syracuseStep 49590089 = 37192567) B37192567
theorem B5165153 : Blo 1528461 5165153 := bstep (se 2 (by rfl) ⟨1936932, by rfl⟩ : syracuseStep 5165153 = 3873865) B3873865
theorem B3871273 : Blo 1528461 3871273 := bstep (se 2 (by rfl) ⟨1451727, by rfl⟩ : syracuseStep 3871273 = 2903455) B2903455
theorem B64492139 : Blo 1528461 64492139 := bstep (se 1 (by rfl) ⟨48369104, by rfl⟩ : syracuseStep 64492139 = 96738209) B96738209
theorem B1528475 : Blo 1528461 1528475 := bstep (se 1 (by rfl) ⟨1146356, by rfl⟩ : syracuseStep 1528475 = 2292713) B2292713
theorem B1528479 : Blo 1528461 1528479 := bstep (se 1 (by rfl) ⟨1146359, by rfl⟩ : syracuseStep 1528479 = 2292719) B2292719
theorem B1528603 : Blo 1528461 1528603 := bstep (se 1 (by rfl) ⟨1146452, by rfl⟩ : syracuseStep 1528603 = 2292905) B2292905
theorem B5805391 : Blo 1528461 5805391 := bstep (se 1 (by rfl) ⟨4354043, by rfl⟩ : syracuseStep 5805391 = 8708087) B8708087
theorem B1529215 : Blo 1528461 1529215 := bstep (se 1 (by rfl) ⟨1146911, by rfl⟩ : syracuseStep 1529215 = 2293823) B2293823
theorem B19600987 : Blo 1528461 19600987 := bstep (se 1 (by rfl) ⟨14700740, by rfl⟩ : syracuseStep 19600987 = 29401481) B29401481
theorem B44087003 : Blo 1528461 44087003 := bstep (se 1 (by rfl) ⟨33065252, by rfl⟩ : syracuseStep 44087003 = 66130505) B66130505
theorem B37213991 : Blo 1528461 37213991 := bstep (se 1 (by rfl) ⟨27910493, by rfl⟩ : syracuseStep 37213991 = 55820987) B55820987
theorem B5158727 : Blo 1528461 5158727 := bstep (se 1 (by rfl) ⟨3869045, by rfl⟩ : syracuseStep 5158727 = 7738091) B7738091
theorem B7747487 : Blo 1528461 7747487 := bstep (se 1 (by rfl) ⟨5810615, by rfl⟩ : syracuseStep 7747487 = 11621231) B11621231
theorem B3872681 : Blo 1528461 3872681 := bstep (se 2 (by rfl) ⟨1452255, by rfl⟩ : syracuseStep 3872681 = 2904511) B2904511
theorem B1529919 : Blo 1528461 1529919 := bstep (se 1 (by rfl) ⟨1147439, by rfl⟩ : syracuseStep 1529919 = 2294879) B2294879
theorem B1530095 : Blo 1528461 1530095 := bstep (se 1 (by rfl) ⟨1147571, by rfl⟩ : syracuseStep 1530095 = 2295143) B2295143
theorem B11024633 : Blo 1528461 11024633 := bstep (se 2 (by rfl) ⟨4134237, by rfl⟩ : syracuseStep 11024633 = 8268475) B8268475
theorem B5806363 : Blo 1528461 5806363 := bstep (se 1 (by rfl) ⟨4354772, by rfl⟩ : syracuseStep 5806363 = 8709545) B8709545
theorem B161159681 : Blo 1528461 161159681 := bstep (se 2 (by rfl) ⟨60434880, by rfl⟩ : syracuseStep 161159681 = 120869761) B120869761
theorem B8067599 : Blo 1528461 8067599 := bstep (se 1 (by rfl) ⟨6050699, by rfl⟩ : syracuseStep 8067599 = 12101399) B12101399
theorem B9296489 : Blo 1528461 9296489 := bstep (se 2 (by rfl) ⟨3486183, by rfl⟩ : syracuseStep 9296489 = 6972367) B6972367
theorem B6536159 : Blo 1528461 6536159 := bstep (se 1 (by rfl) ⟨4902119, by rfl⟩ : syracuseStep 6536159 = 9804239) B9804239
theorem B4357097 : Blo 1528461 4357097 := bstep (se 2 (by rfl) ⟨1633911, by rfl⟩ : syracuseStep 4357097 = 3267823) B3267823
theorem B113212505 : Blo 1528461 113212505 := bstep (se 2 (by rfl) ⟨42454689, by rfl⟩ : syracuseStep 113212505 = 84909379) B84909379
theorem B2579593 : Blo 1528461 2579593 := bstep (se 2 (by rfl) ⟨967347, by rfl⟩ : syracuseStep 2579593 = 1934695) B1934695
theorem B2579647 : Blo 1528461 2579647 := bstep (se 1 (by rfl) ⟨1934735, by rfl⟩ : syracuseStep 2579647 = 3869471) B3869471
theorem B2293055 : Blo 1528461 2293055 := bstep (se 1 (by rfl) ⟨1719791, by rfl⟩ : syracuseStep 2293055 = 3439583) B3439583
theorem B4414927 : Blo 1528461 4414927 := bstep (se 1 (by rfl) ⟨3311195, by rfl⟩ : syracuseStep 4414927 = 6622391) B6622391
theorem B2579951 : Blo 1528461 2579951 := bstep (se 1 (by rfl) ⟨1934963, by rfl⟩ : syracuseStep 2579951 = 3869927) B3869927
theorem B3358199 : Blo 1528461 3358199 := bstep (se 1 (by rfl) ⟨2518649, by rfl⟩ : syracuseStep 3358199 = 5037299) B5037299
theorem B11607623 : Blo 1528461 11607623 := bstep (se 1 (by rfl) ⟨8705717, by rfl⟩ : syracuseStep 11607623 = 17411435) B17411435
theorem B18611815 : Blo 1528461 18611815 := bstep (se 1 (by rfl) ⟨13958861, by rfl⟩ : syracuseStep 18611815 = 27917723) B27917723
theorem B3440879 : Blo 1528461 3440879 := bstep (se 1 (by rfl) ⟨2580659, by rfl⟩ : syracuseStep 3440879 = 5161319) B5161319
theorem B9797881 : Blo 1528461 9797881 := bstep (se 2 (by rfl) ⟨3674205, by rfl⟩ : syracuseStep 9797881 = 7348411) B7348411
theorem B7741817 : Blo 1528461 7741817 := bstep (se 2 (by rfl) ⟨2903181, by rfl⟩ : syracuseStep 7741817 = 5806363) B5806363
theorem B5161427 : Blo 1528461 5161427 := bstep (se 1 (by rfl) ⟨3871070, by rfl⟩ : syracuseStep 5161427 = 7742141) B7742141
theorem B5161697 : Blo 1528461 5161697 := bstep (se 2 (by rfl) ⟨1935636, by rfl⟩ : syracuseStep 5161697 = 3871273) B3871273
theorem B2581787 : Blo 1528461 2581787 := bstep (se 1 (by rfl) ⟨1936340, by rfl⟩ : syracuseStep 2581787 = 3872681) B3872681
theorem B8955197 : Blo 1528461 8955197 := bstep (se 3 (by rfl) ⟨1679099, by rfl⟩ : syracuseStep 8955197 = 3358199) B3358199
theorem B24790637 : Blo 1528461 24790637 := bstep (se 3 (by rfl) ⟨4648244, by rfl⟩ : syracuseStep 24790637 = 9296489) B9296489
theorem B107439787 : Blo 1528461 107439787 := bstep (se 1 (by rfl) ⟨80579840, by rfl⟩ : syracuseStep 107439787 = 161159681) B161159681
theorem B75475003 : Blo 1528461 75475003 := bstep (se 1 (by rfl) ⟨56606252, by rfl⟩ : syracuseStep 75475003 = 113212505) B113212505
theorem B26134649 : Blo 1528461 26134649 := bstep (se 2 (by rfl) ⟨9800493, by rfl⟩ : syracuseStep 26134649 = 19600987) B19600987
theorem B24815753 : Blo 1528461 24815753 := bstep (se 2 (by rfl) ⟨9305907, by rfl⟩ : syracuseStep 24815753 = 18611815) B18611815
theorem B3443435 : Blo 1528461 3443435 := bstep (se 1 (by rfl) ⟨2582576, by rfl⟩ : syracuseStep 3443435 = 5165153) B5165153
theorem B7744895 : Blo 1528461 7744895 := bstep (se 1 (by rfl) ⟨5808671, by rfl⟩ : syracuseStep 7744895 = 11617343) B11617343
theorem B8711711 : Blo 1528461 8711711 := bstep (se 1 (by rfl) ⟨6533783, by rfl⟩ : syracuseStep 8711711 = 13067567) B13067567
theorem B4353679 : Blo 1528461 4353679 := bstep (se 1 (by rfl) ⟨3265259, by rfl⟩ : syracuseStep 4353679 = 6530519) B6530519
theorem B24809327 : Blo 1528461 24809327 := bstep (se 1 (by rfl) ⟨18606995, by rfl⟩ : syracuseStep 24809327 = 37213991) B37213991
theorem B5164991 : Blo 1528461 5164991 := bstep (se 1 (by rfl) ⟨3873743, by rfl⟩ : syracuseStep 5164991 = 7747487) B7747487
theorem B171979037 : Blo 1528461 171979037 := bstep (se 3 (by rfl) ⟨32246069, by rfl⟩ : syracuseStep 171979037 = 64492139) B64492139
theorem B5378399 : Blo 1528461 5378399 := bstep (se 1 (by rfl) ⟨4033799, by rfl⟩ : syracuseStep 5378399 = 8067599) B8067599
theorem B5886569 : Blo 1528461 5886569 := bstep (se 2 (by rfl) ⟨2207463, by rfl⟩ : syracuseStep 5886569 = 4414927) B4414927
theorem B2904731 : Blo 1528461 2904731 := bstep (se 1 (by rfl) ⟨2178548, by rfl⟩ : syracuseStep 2904731 = 4357097) B4357097
theorem B1528703 : Blo 1528461 1528703 := bstep (se 1 (by rfl) ⟨1146527, by rfl⟩ : syracuseStep 1528703 = 2293055) B2293055
theorem B7738415 : Blo 1528461 7738415 := bstep (se 1 (by rfl) ⟨5803811, by rfl⟩ : syracuseStep 7738415 = 11607623) B11607623
theorem B33060059 : Blo 1528461 33060059 := bstep (se 1 (by rfl) ⟨24795044, by rfl⟩ : syracuseStep 33060059 = 49590089) B49590089
theorem B3675647 : Blo 1528461 3675647 := bstep (se 1 (by rfl) ⟨2756735, by rfl⟩ : syracuseStep 3675647 = 5513471) B5513471
theorem B1529371 : Blo 1528461 1529371 := bstep (se 1 (by rfl) ⟨1147028, by rfl⟩ : syracuseStep 1529371 = 2294057) B2294057
theorem B5805863 : Blo 1528461 5805863 := bstep (se 1 (by rfl) ⟨4354397, by rfl⟩ : syracuseStep 5805863 = 8708795) B8708795
theorem B1529703 : Blo 1528461 1529703 := bstep (se 1 (by rfl) ⟨1147277, by rfl⟩ : syracuseStep 1529703 = 2294555) B2294555
theorem B29399021 : Blo 1528461 29399021 := bstep (se 3 (by rfl) ⟨5512316, by rfl⟩ : syracuseStep 29399021 = 11024633) B11024633
theorem B7739387 : Blo 1528461 7739387 := bstep (se 1 (by rfl) ⟨5804540, by rfl⟩ : syracuseStep 7739387 = 11609081) B11609081
theorem B1529959 : Blo 1528461 1529959 := bstep (se 1 (by rfl) ⟨1147469, by rfl⟩ : syracuseStep 1529959 = 2294939) B2294939
theorem B1530175 : Blo 1528461 1530175 := bstep (se 1 (by rfl) ⟨1147631, by rfl⟩ : syracuseStep 1530175 = 2295263) B2295263
theorem B1530303 : Blo 1528461 1530303 := bstep (se 1 (by rfl) ⟨1147727, by rfl⟩ : syracuseStep 1530303 = 2295455) B2295455
theorem B29391335 : Blo 1528461 29391335 := bstep (se 1 (by rfl) ⟨22043501, by rfl⟩ : syracuseStep 29391335 = 44087003) B44087003
theorem B3439151 : Blo 1528461 3439151 := bstep (se 1 (by rfl) ⟨2579363, by rfl⟩ : syracuseStep 3439151 = 5158727) B5158727
theorem B3439457 : Blo 1528461 3439457 := bstep (se 2 (by rfl) ⟨1289796, by rfl⟩ : syracuseStep 3439457 = 2579593) B2579593
theorem B3439529 : Blo 1528461 3439529 := bstep (se 2 (by rfl) ⟨1289823, by rfl⟩ : syracuseStep 3439529 = 2579647) B2579647
theorem B7740521 : Blo 1528461 7740521 := bstep (se 2 (by rfl) ⟨2902695, by rfl⟩ : syracuseStep 7740521 = 5805391) B5805391
theorem B4357439 : Blo 1528461 4357439 := bstep (se 1 (by rfl) ⟨3268079, by rfl⟩ : syracuseStep 4357439 = 6536159) B6536159
theorem B5512607 : Blo 1528461 5512607 := bstep (se 1 (by rfl) ⟨4134455, by rfl⟩ : syracuseStep 5512607 = 8268911) B8268911
theorem B2580079 : Blo 1528461 2580079 := bstep (se 1 (by rfl) ⟨1935059, by rfl⟩ : syracuseStep 2580079 = 3870119) B3870119
theorem B1719967 : Blo 1528461 1719967 := bstep (se 1 (by rfl) ⟨1289975, by rfl⟩ : syracuseStep 1719967 = 2579951) B2579951
theorem B2293919 : Blo 1528461 2293919 := bstep (se 1 (by rfl) ⟨1720439, by rfl⟩ : syracuseStep 2293919 = 3440879) B3440879
theorem B5161211 : Blo 1528461 5161211 := bstep (se 1 (by rfl) ⟨3870908, by rfl⟩ : syracuseStep 5161211 = 7741817) B7741817
theorem B3440951 : Blo 1528461 3440951 := bstep (se 1 (by rfl) ⟨2580713, by rfl⟩ : syracuseStep 3440951 = 5161427) B5161427
theorem B3924379 : Blo 1528461 3924379 := bstep (se 1 (by rfl) ⟨2943284, by rfl⟩ : syracuseStep 3924379 = 5886569) B5886569
theorem B3441131 : Blo 1528461 3441131 := bstep (se 1 (by rfl) ⟨2580848, by rfl⟩ : syracuseStep 3441131 = 5161697) B5161697
theorem B1721191 : Blo 1528461 1721191 := bstep (se 1 (by rfl) ⟨1290893, by rfl⟩ : syracuseStep 1721191 = 2581787) B2581787
theorem B2450431 : Blo 1528461 2450431 := bstep (se 1 (by rfl) ⟨1837823, by rfl⟩ : syracuseStep 2450431 = 3675647) B3675647
theorem B2295623 : Blo 1528461 2295623 := bstep (se 1 (by rfl) ⟨1721717, by rfl⟩ : syracuseStep 2295623 = 3443435) B3443435
theorem B5163263 : Blo 1528461 5163263 := bstep (se 1 (by rfl) ⟨3872447, by rfl⟩ : syracuseStep 5163263 = 7744895) B7744895
theorem B3443327 : Blo 1528461 3443327 := bstep (se 1 (by rfl) ⟨2582495, by rfl⟩ : syracuseStep 3443327 = 5164991) B5164991
theorem B100633337 : Blo 1528461 100633337 := bstep (se 2 (by rfl) ⟨37737501, by rfl⟩ : syracuseStep 100633337 = 75475003) B75475003
theorem B1936487 : Blo 1528461 1936487 := bstep (se 1 (by rfl) ⟨1452365, by rfl⟩ : syracuseStep 1936487 = 2904731) B2904731
theorem B22040039 : Blo 1528461 22040039 := bstep (se 1 (by rfl) ⟨16530029, by rfl⟩ : syracuseStep 22040039 = 33060059) B33060059
theorem B16527091 : Blo 1528461 16527091 := bstep (se 1 (by rfl) ⟨12395318, by rfl⟩ : syracuseStep 16527091 = 24790637) B24790637
theorem B3870575 : Blo 1528461 3870575 := bstep (se 1 (by rfl) ⟨2902931, by rfl⟩ : syracuseStep 3870575 = 5805863) B5805863
theorem B19599347 : Blo 1528461 19599347 := bstep (se 1 (by rfl) ⟨14699510, by rfl⟩ : syracuseStep 19599347 = 29399021) B29399021
theorem B16543835 : Blo 1528461 16543835 := bstep (se 1 (by rfl) ⟨12407876, by rfl⟩ : syracuseStep 16543835 = 24815753) B24815753
theorem B5804905 : Blo 1528461 5804905 := bstep (se 2 (by rfl) ⟨2176839, by rfl⟩ : syracuseStep 5804905 = 4353679) B4353679
theorem B2904959 : Blo 1528461 2904959 := bstep (se 1 (by rfl) ⟨2178719, by rfl⟩ : syracuseStep 2904959 = 4357439) B4357439
theorem B3675071 : Blo 1528461 3675071 := bstep (se 1 (by rfl) ⟨2756303, by rfl⟩ : syracuseStep 3675071 = 5512607) B5512607
theorem B114652691 : Blo 1528461 114652691 := bstep (se 1 (by rfl) ⟨85989518, by rfl⟩ : syracuseStep 114652691 = 171979037) B171979037
theorem B3585599 : Blo 1528461 3585599 := bstep (se 1 (by rfl) ⟨2689199, by rfl⟩ : syracuseStep 3585599 = 5378399) B5378399
theorem B13063841 : Blo 1528461 13063841 := bstep (se 2 (by rfl) ⟨4898940, by rfl⟩ : syracuseStep 13063841 = 9797881) B9797881
theorem B5158943 : Blo 1528461 5158943 := bstep (se 1 (by rfl) ⟨3869207, by rfl⟩ : syracuseStep 5158943 = 7738415) B7738415
theorem B5970131 : Blo 1528461 5970131 := bstep (se 1 (by rfl) ⟨4477598, by rfl⟩ : syracuseStep 5970131 = 8955197) B8955197
theorem B5159591 : Blo 1528461 5159591 := bstep (se 1 (by rfl) ⟨3869693, by rfl⟩ : syracuseStep 5159591 = 7739387) B7739387
theorem B17423099 : Blo 1528461 17423099 := bstep (se 1 (by rfl) ⟨13067324, by rfl⟩ : syracuseStep 17423099 = 26134649) B26134649
theorem B19594223 : Blo 1528461 19594223 := bstep (se 1 (by rfl) ⟨14695667, by rfl⟩ : syracuseStep 19594223 = 29391335) B29391335
theorem B2292767 : Blo 1528461 2292767 := bstep (se 1 (by rfl) ⟨1719575, by rfl⟩ : syracuseStep 2292767 = 3439151) B3439151
theorem B2292971 : Blo 1528461 2292971 := bstep (se 1 (by rfl) ⟨1719728, by rfl⟩ : syracuseStep 2292971 = 3439457) B3439457
theorem B2293019 : Blo 1528461 2293019 := bstep (se 1 (by rfl) ⟨1719764, by rfl⟩ : syracuseStep 2293019 = 3439529) B3439529
theorem B5160347 : Blo 1528461 5160347 := bstep (se 1 (by rfl) ⟨3870260, by rfl⟩ : syracuseStep 5160347 = 7740521) B7740521
theorem B3440105 : Blo 1528461 3440105 := bstep (se 2 (by rfl) ⟨1290039, by rfl⟩ : syracuseStep 3440105 = 2580079) B2580079
theorem B2293289 : Blo 1528461 2293289 := bstep (se 2 (by rfl) ⟨859983, by rfl⟩ : syracuseStep 2293289 = 1719967) B1719967
theorem B143253049 : Blo 1528461 143253049 := bstep (se 2 (by rfl) ⟨53719893, by rfl⟩ : syracuseStep 143253049 = 107439787) B107439787
theorem B5807807 : Blo 1528461 5807807 := bstep (se 1 (by rfl) ⟨4355855, by rfl⟩ : syracuseStep 5807807 = 8711711) B8711711
theorem B16539551 : Blo 1528461 16539551 := bstep (se 1 (by rfl) ⟨12404663, by rfl⟩ : syracuseStep 16539551 = 24809327) B24809327
theorem B3440807 : Blo 1528461 3440807 := bstep (se 1 (by rfl) ⟨2580605, by rfl⟩ : syracuseStep 3440807 = 5161211) B5161211
theorem B2293967 : Blo 1528461 2293967 := bstep (se 1 (by rfl) ⟨1720475, by rfl⟩ : syracuseStep 2293967 = 3440951) B3440951
theorem B2294087 : Blo 1528461 2294087 := bstep (se 1 (by rfl) ⟨1720565, by rfl⟩ : syracuseStep 2294087 = 3441131) B3441131
theorem B8709227 : Blo 1528461 8709227 := bstep (se 1 (by rfl) ⟨6531920, by rfl⟩ : syracuseStep 8709227 = 13063841) B13063841
theorem B2294921 : Blo 1528461 2294921 := bstep (se 2 (by rfl) ⟨860595, by rfl⟩ : syracuseStep 2294921 = 1721191) B1721191
theorem B3442175 : Blo 1528461 3442175 := bstep (se 1 (by rfl) ⟨2581631, by rfl⟩ : syracuseStep 3442175 = 5163263) B5163263
theorem B2295551 : Blo 1528461 2295551 := bstep (se 1 (by rfl) ⟨1721663, by rfl⟩ : syracuseStep 2295551 = 3443327) B3443327
theorem B9800189 : Blo 1528461 9800189 := bstep (se 3 (by rfl) ⟨1837535, by rfl⟩ : syracuseStep 9800189 = 3675071) B3675071
theorem B13068965 : Blo 1528461 13068965 := bstep (se 4 (by rfl) ⟨1225215, by rfl⟩ : syracuseStep 13068965 = 2450431) B2450431
theorem B11029223 : Blo 1528461 11029223 := bstep (se 1 (by rfl) ⟨8271917, by rfl⟩ : syracuseStep 11029223 = 16543835) B16543835
theorem B5163965 : Blo 1528461 5163965 := bstep (se 3 (by rfl) ⟨968243, by rfl⟩ : syracuseStep 5163965 = 1936487) B1936487
theorem B1936639 : Blo 1528461 1936639 := bstep (se 1 (by rfl) ⟨1452479, by rfl⟩ : syracuseStep 1936639 = 2904959) B2904959
theorem B76435127 : Blo 1528461 76435127 := bstep (se 1 (by rfl) ⟨57326345, by rfl⟩ : syracuseStep 76435127 = 114652691) B114652691
theorem B58773437 : Blo 1528461 58773437 := bstep (se 3 (by rfl) ⟨11020019, by rfl⟩ : syracuseStep 58773437 = 22040039) B22040039
theorem B67088891 : Blo 1528461 67088891 := bstep (se 1 (by rfl) ⟨50316668, by rfl⟩ : syracuseStep 67088891 = 100633337) B100633337
theorem B13062815 : Blo 1528461 13062815 := bstep (se 1 (by rfl) ⟨9797111, by rfl⟩ : syracuseStep 13062815 = 19594223) B19594223
theorem B1528511 : Blo 1528461 1528511 := bstep (se 1 (by rfl) ⟨1146383, by rfl⟩ : syracuseStep 1528511 = 2292767) B2292767
theorem B1528647 : Blo 1528461 1528647 := bstep (se 1 (by rfl) ⟨1146485, by rfl⟩ : syracuseStep 1528647 = 2292971) B2292971
theorem B1528679 : Blo 1528461 1528679 := bstep (se 1 (by rfl) ⟨1146509, by rfl⟩ : syracuseStep 1528679 = 2293019) B2293019
theorem B1528859 : Blo 1528461 1528859 := bstep (se 1 (by rfl) ⟨1146644, by rfl⟩ : syracuseStep 1528859 = 2293289) B2293289
theorem B3871871 : Blo 1528461 3871871 := bstep (se 1 (by rfl) ⟨2903903, by rfl⟩ : syracuseStep 3871871 = 5807807) B5807807
theorem B1529279 : Blo 1528461 1529279 := bstep (se 1 (by rfl) ⟨1146959, by rfl⟩ : syracuseStep 1529279 = 2293919) B2293919
theorem B5232505 : Blo 1528461 5232505 := bstep (se 2 (by rfl) ⟨1962189, by rfl⟩ : syracuseStep 5232505 = 3924379) B3924379
theorem B2390399 : Blo 1528461 2390399 := bstep (se 1 (by rfl) ⟨1792799, by rfl⟩ : syracuseStep 2390399 = 3585599) B3585599
theorem B7739873 : Blo 1528461 7739873 := bstep (se 2 (by rfl) ⟨2902452, by rfl⟩ : syracuseStep 7739873 = 5804905) B5804905
theorem B1530415 : Blo 1528461 1530415 := bstep (se 1 (by rfl) ⟨1147811, by rfl⟩ : syracuseStep 1530415 = 2295623) B2295623
theorem B3439295 : Blo 1528461 3439295 := bstep (se 1 (by rfl) ⟨2579471, by rfl⟩ : syracuseStep 3439295 = 5158943) B5158943
theorem B13066231 : Blo 1528461 13066231 := bstep (se 1 (by rfl) ⟨9799673, by rfl⟩ : syracuseStep 13066231 = 19599347) B19599347
theorem B3980087 : Blo 1528461 3980087 := bstep (se 1 (by rfl) ⟨2985065, by rfl⟩ : syracuseStep 3980087 = 5970131) B5970131
theorem B3439727 : Blo 1528461 3439727 := bstep (se 1 (by rfl) ⟨2579795, by rfl⟩ : syracuseStep 3439727 = 5159591) B5159591
theorem B11615399 : Blo 1528461 11615399 := bstep (se 1 (by rfl) ⟨8711549, by rfl⟩ : syracuseStep 11615399 = 17423099) B17423099
theorem B191004065 : Blo 1528461 191004065 := bstep (se 2 (by rfl) ⟨71626524, by rfl⟩ : syracuseStep 191004065 = 143253049) B143253049
theorem B3440231 : Blo 1528461 3440231 := bstep (se 1 (by rfl) ⟨2580173, by rfl⟩ : syracuseStep 3440231 = 5160347) B5160347
theorem B22036121 : Blo 1528461 22036121 := bstep (se 2 (by rfl) ⟨8263545, by rfl⟩ : syracuseStep 22036121 = 16527091) B16527091
theorem B2293403 : Blo 1528461 2293403 := bstep (se 1 (by rfl) ⟨1720052, by rfl⟩ : syracuseStep 2293403 = 3440105) B3440105
theorem B2580383 : Blo 1528461 2580383 := bstep (se 1 (by rfl) ⟨1935287, by rfl⟩ : syracuseStep 2580383 = 3870575) B3870575
theorem B11026367 : Blo 1528461 11026367 := bstep (se 1 (by rfl) ⟨8269775, by rfl⟩ : syracuseStep 11026367 = 16539551) B16539551
theorem B2293871 : Blo 1528461 2293871 := bstep (se 1 (by rfl) ⟨1720403, by rfl⟩ : syracuseStep 2293871 = 3440807) B3440807
theorem B8708543 : Blo 1528461 8708543 := bstep (se 1 (by rfl) ⟨6531407, by rfl⟩ : syracuseStep 8708543 = 13062815) B13062815
theorem B2581247 : Blo 1528461 2581247 := bstep (se 1 (by rfl) ⟨1935935, by rfl⟩ : syracuseStep 2581247 = 3871871) B3871871
theorem B2294783 : Blo 1528461 2294783 := bstep (se 1 (by rfl) ⟨1721087, by rfl⟩ : syracuseStep 2294783 = 3442175) B3442175
theorem B2582185 : Blo 1528461 2582185 := bstep (se 2 (by rfl) ⟨968319, by rfl⟩ : syracuseStep 2582185 = 1936639) B1936639
theorem B3442643 : Blo 1528461 3442643 := bstep (se 1 (by rfl) ⟨2581982, by rfl⟩ : syracuseStep 3442643 = 5163965) B5163965
theorem B7743599 : Blo 1528461 7743599 := bstep (se 1 (by rfl) ⟨5807699, by rfl⟩ : syracuseStep 7743599 = 11615399) B11615399
theorem B14690747 : Blo 1528461 14690747 := bstep (se 1 (by rfl) ⟨11018060, by rfl⟩ : syracuseStep 14690747 = 22036121) B22036121
theorem B50956751 : Blo 1528461 50956751 := bstep (se 1 (by rfl) ⟨38217563, by rfl⟩ : syracuseStep 50956751 = 76435127) B76435127
theorem B7350911 : Blo 1528461 7350911 := bstep (se 1 (by rfl) ⟨5513183, by rfl⟩ : syracuseStep 7350911 = 11026367) B11026367
theorem B1593599 : Blo 1528461 1593599 := bstep (se 1 (by rfl) ⟨1195199, by rfl⟩ : syracuseStep 1593599 = 2390399) B2390399
theorem B6533459 : Blo 1528461 6533459 := bstep (se 1 (by rfl) ⟨4900094, by rfl⟩ : syracuseStep 6533459 = 9800189) B9800189
theorem B8712643 : Blo 1528461 8712643 := bstep (se 1 (by rfl) ⟨6534482, by rfl⟩ : syracuseStep 8712643 = 13068965) B13068965
theorem B7352815 : Blo 1528461 7352815 := bstep (se 1 (by rfl) ⟨5514611, by rfl⟩ : syracuseStep 7352815 = 11029223) B11029223
theorem B1528935 : Blo 1528461 1528935 := bstep (se 1 (by rfl) ⟨1146701, by rfl⟩ : syracuseStep 1528935 = 2293403) B2293403
theorem B6976673 : Blo 1528461 6976673 := bstep (se 2 (by rfl) ⟨2616252, by rfl⟩ : syracuseStep 6976673 = 5232505) B5232505
theorem B17421641 : Blo 1528461 17421641 := bstep (se 2 (by rfl) ⟨6533115, by rfl⟩ : syracuseStep 17421641 = 13066231) B13066231
theorem B1529311 : Blo 1528461 1529311 := bstep (se 1 (by rfl) ⟨1146983, by rfl⟩ : syracuseStep 1529311 = 2293967) B2293967
theorem B1529391 : Blo 1528461 1529391 := bstep (se 1 (by rfl) ⟨1147043, by rfl⟩ : syracuseStep 1529391 = 2294087) B2294087
theorem B44725927 : Blo 1528461 44725927 := bstep (se 1 (by rfl) ⟨33544445, by rfl⟩ : syracuseStep 44725927 = 67088891) B67088891
theorem B5806151 : Blo 1528461 5806151 := bstep (se 1 (by rfl) ⟨4354613, by rfl⟩ : syracuseStep 5806151 = 8709227) B8709227
theorem B1529947 : Blo 1528461 1529947 := bstep (se 1 (by rfl) ⟨1147460, by rfl⟩ : syracuseStep 1529947 = 2294921) B2294921
theorem B1530367 : Blo 1528461 1530367 := bstep (se 1 (by rfl) ⟨1147775, by rfl⟩ : syracuseStep 1530367 = 2295551) B2295551
theorem B5159915 : Blo 1528461 5159915 := bstep (se 1 (by rfl) ⟨3869936, by rfl⟩ : syracuseStep 5159915 = 7739873) B7739873
theorem B2292863 : Blo 1528461 2292863 := bstep (se 1 (by rfl) ⟨1719647, by rfl⟩ : syracuseStep 2292863 = 3439295) B3439295
theorem B2653391 : Blo 1528461 2653391 := bstep (se 1 (by rfl) ⟨1990043, by rfl⟩ : syracuseStep 2653391 = 3980087) B3980087
theorem B2293151 : Blo 1528461 2293151 := bstep (se 1 (by rfl) ⟨1719863, by rfl⟩ : syracuseStep 2293151 = 3439727) B3439727
theorem B127336043 : Blo 1528461 127336043 := bstep (se 1 (by rfl) ⟨95502032, by rfl⟩ : syracuseStep 127336043 = 191004065) B191004065
theorem B2293487 : Blo 1528461 2293487 := bstep (se 1 (by rfl) ⟨1720115, by rfl⟩ : syracuseStep 2293487 = 3440231) B3440231
theorem B1720255 : Blo 1528461 1720255 := bstep (se 1 (by rfl) ⟨1290191, by rfl⟩ : syracuseStep 1720255 = 2580383) B2580383
theorem B39182291 : Blo 1528461 39182291 := bstep (se 1 (by rfl) ⟨29386718, by rfl⟩ : syracuseStep 39182291 = 58773437) B58773437
theorem B1720831 : Blo 1528461 1720831 := bstep (se 1 (by rfl) ⟨1290623, by rfl⟩ : syracuseStep 1720831 = 2581247) B2581247
theorem B11616857 : Blo 1528461 11616857 := bstep (se 2 (by rfl) ⟨4356321, by rfl⟩ : syracuseStep 11616857 = 8712643) B8712643
theorem B2295095 : Blo 1528461 2295095 := bstep (se 1 (by rfl) ⟨1721321, by rfl⟩ : syracuseStep 2295095 = 3442643) B3442643
theorem B5162399 : Blo 1528461 5162399 := bstep (se 1 (by rfl) ⟨3871799, by rfl⟩ : syracuseStep 5162399 = 7743599) B7743599
theorem B4900607 : Blo 1528461 4900607 := bstep (se 1 (by rfl) ⟨3675455, by rfl⟩ : syracuseStep 4900607 = 7350911) B7350911
theorem B3442913 : Blo 1528461 3442913 := bstep (se 2 (by rfl) ⟨1291092, by rfl⟩ : syracuseStep 3442913 = 2582185) B2582185
theorem B3870767 : Blo 1528461 3870767 := bstep (se 1 (by rfl) ⟨2903075, by rfl⟩ : syracuseStep 3870767 = 5806151) B5806151
theorem B9793831 : Blo 1528461 9793831 := bstep (se 1 (by rfl) ⟨7345373, by rfl⟩ : syracuseStep 9793831 = 14690747) B14690747
theorem B1528575 : Blo 1528461 1528575 := bstep (se 1 (by rfl) ⟨1146431, by rfl⟩ : syracuseStep 1528575 = 2292863) B2292863
theorem B59634569 : Blo 1528461 59634569 := bstep (se 2 (by rfl) ⟨22362963, by rfl⟩ : syracuseStep 59634569 = 44725927) B44725927
theorem B1528767 : Blo 1528461 1528767 := bstep (se 1 (by rfl) ⟨1146575, by rfl⟩ : syracuseStep 1528767 = 2293151) B2293151
theorem B84890695 : Blo 1528461 84890695 := bstep (se 1 (by rfl) ⟨63668021, by rfl⟩ : syracuseStep 84890695 = 127336043) B127336043
theorem B1528991 : Blo 1528461 1528991 := bstep (se 1 (by rfl) ⟨1146743, by rfl⟩ : syracuseStep 1528991 = 2293487) B2293487
theorem B26121527 : Blo 1528461 26121527 := bstep (se 1 (by rfl) ⟨19591145, by rfl⟩ : syracuseStep 26121527 = 39182291) B39182291
theorem B1529247 : Blo 1528461 1529247 := bstep (se 1 (by rfl) ⟨1146935, by rfl⟩ : syracuseStep 1529247 = 2293871) B2293871
theorem B4355639 : Blo 1528461 4355639 := bstep (se 1 (by rfl) ⟨3266729, by rfl⟩ : syracuseStep 4355639 = 6533459) B6533459
theorem B5805695 : Blo 1528461 5805695 := bstep (se 1 (by rfl) ⟨4354271, by rfl⟩ : syracuseStep 5805695 = 8708543) B8708543
theorem B9803753 : Blo 1528461 9803753 := bstep (se 2 (by rfl) ⟨3676407, by rfl⟩ : syracuseStep 9803753 = 7352815) B7352815
theorem B4249597 : Blo 1528461 4249597 := bstep (se 3 (by rfl) ⟨796799, by rfl⟩ : syracuseStep 4249597 = 1593599) B1593599
theorem B1529855 : Blo 1528461 1529855 := bstep (se 1 (by rfl) ⟨1147391, by rfl⟩ : syracuseStep 1529855 = 2294783) B2294783
theorem B4651115 : Blo 1528461 4651115 := bstep (se 1 (by rfl) ⟨3488336, by rfl⟩ : syracuseStep 4651115 = 6976673) B6976673
theorem B11614427 : Blo 1528461 11614427 := bstep (se 1 (by rfl) ⟨8710820, by rfl⟩ : syracuseStep 11614427 = 17421641) B17421641
theorem B33971167 : Blo 1528461 33971167 := bstep (se 1 (by rfl) ⟨25478375, by rfl⟩ : syracuseStep 33971167 = 50956751) B50956751
theorem B3439943 : Blo 1528461 3439943 := bstep (se 1 (by rfl) ⟨2579957, by rfl⟩ : syracuseStep 3439943 = 5159915) B5159915
theorem B1768927 : Blo 1528461 1768927 := bstep (se 1 (by rfl) ⟨1326695, by rfl⟩ : syracuseStep 1768927 = 2653391) B2653391
theorem B2293673 : Blo 1528461 2293673 := bstep (se 2 (by rfl) ⟨860127, by rfl⟩ : syracuseStep 2293673 = 1720255) B1720255
theorem B2580511 : Blo 1528461 2580511 := bstep (se 1 (by rfl) ⟨1935383, by rfl⟩ : syracuseStep 2580511 = 3870767) B3870767
theorem B12402973 : Blo 1528461 12402973 := bstep (se 3 (by rfl) ⟨2325557, by rfl⟩ : syracuseStep 12402973 = 4651115) B4651115
theorem B13058441 : Blo 1528461 13058441 := bstep (se 2 (by rfl) ⟨4896915, by rfl⟩ : syracuseStep 13058441 = 9793831) B9793831
theorem B39756379 : Blo 1528461 39756379 := bstep (se 1 (by rfl) ⟨29817284, by rfl⟩ : syracuseStep 39756379 = 59634569) B59634569
theorem B2294441 : Blo 1528461 2294441 := bstep (se 2 (by rfl) ⟨860415, by rfl⟩ : syracuseStep 2294441 = 1720831) B1720831
theorem B3441599 : Blo 1528461 3441599 := bstep (se 1 (by rfl) ⟨2581199, by rfl⟩ : syracuseStep 3441599 = 5162399) B5162399
theorem B45294889 : Blo 1528461 45294889 := bstep (se 2 (by rfl) ⟨16985583, by rfl⟩ : syracuseStep 45294889 = 33971167) B33971167
theorem B7742951 : Blo 1528461 7742951 := bstep (se 1 (by rfl) ⟨5807213, by rfl⟩ : syracuseStep 7742951 = 11614427) B11614427
theorem B2295275 : Blo 1528461 2295275 := bstep (se 1 (by rfl) ⟨1721456, by rfl⟩ : syracuseStep 2295275 = 3442913) B3442913
theorem B7744571 : Blo 1528461 7744571 := bstep (se 1 (by rfl) ⟨5808428, by rfl⟩ : syracuseStep 7744571 = 11616857) B11616857
theorem B2903759 : Blo 1528461 2903759 := bstep (se 1 (by rfl) ⟨2177819, by rfl⟩ : syracuseStep 2903759 = 4355639) B4355639
theorem B3870463 : Blo 1528461 3870463 := bstep (se 1 (by rfl) ⟨2902847, by rfl⟩ : syracuseStep 3870463 = 5805695) B5805695
theorem B1529115 : Blo 1528461 1529115 := bstep (se 1 (by rfl) ⟨1146836, by rfl⟩ : syracuseStep 1529115 = 2293673) B2293673
theorem B5666129 : Blo 1528461 5666129 := bstep (se 2 (by rfl) ⟨2124798, by rfl⟩ : syracuseStep 5666129 = 4249597) B4249597
theorem B17414351 : Blo 1528461 17414351 := bstep (se 1 (by rfl) ⟨13060763, by rfl⟩ : syracuseStep 17414351 = 26121527) B26121527
theorem B1530063 : Blo 1528461 1530063 := bstep (se 1 (by rfl) ⟨1147547, by rfl⟩ : syracuseStep 1530063 = 2295095) B2295095
theorem B3267071 : Blo 1528461 3267071 := bstep (se 1 (by rfl) ⟨2450303, by rfl⟩ : syracuseStep 3267071 = 4900607) B4900607
theorem B6535835 : Blo 1528461 6535835 := bstep (se 1 (by rfl) ⟨4901876, by rfl⟩ : syracuseStep 6535835 = 9803753) B9803753
theorem B113187593 : Blo 1528461 113187593 := bstep (se 2 (by rfl) ⟨42445347, by rfl⟩ : syracuseStep 113187593 = 84890695) B84890695
theorem B2358569 : Blo 1528461 2358569 := bstep (se 2 (by rfl) ⟨884463, by rfl⟩ : syracuseStep 2358569 = 1768927) B1768927
theorem B2293295 : Blo 1528461 2293295 := bstep (se 1 (by rfl) ⟨1719971, by rfl⟩ : syracuseStep 2293295 = 3439943) B3439943
theorem B3440681 : Blo 1528461 3440681 := bstep (se 2 (by rfl) ⟨1290255, by rfl⟩ : syracuseStep 3440681 = 2580511) B2580511
theorem B2294399 : Blo 1528461 2294399 := bstep (se 1 (by rfl) ⟨1720799, by rfl⟩ : syracuseStep 2294399 = 3441599) B3441599
theorem B3777419 : Blo 1528461 3777419 := bstep (se 1 (by rfl) ⟨2833064, by rfl⟩ : syracuseStep 3777419 = 5666129) B5666129
theorem B5161967 : Blo 1528461 5161967 := bstep (se 1 (by rfl) ⟨3871475, by rfl⟩ : syracuseStep 5161967 = 7742951) B7742951
theorem B11609567 : Blo 1528461 11609567 := bstep (se 1 (by rfl) ⟨8707175, by rfl⟩ : syracuseStep 11609567 = 17414351) B17414351
theorem B60393185 : Blo 1528461 60393185 := bstep (se 2 (by rfl) ⟨22647444, by rfl⟩ : syracuseStep 60393185 = 45294889) B45294889
theorem B75458395 : Blo 1528461 75458395 := bstep (se 1 (by rfl) ⟨56593796, by rfl⟩ : syracuseStep 75458395 = 113187593) B113187593
theorem B5163047 : Blo 1528461 5163047 := bstep (se 1 (by rfl) ⟨3872285, by rfl⟩ : syracuseStep 5163047 = 7744571) B7744571
theorem B1935839 : Blo 1528461 1935839 := bstep (se 1 (by rfl) ⟨1451879, by rfl⟩ : syracuseStep 1935839 = 2903759) B2903759
theorem B1528863 : Blo 1528461 1528863 := bstep (se 1 (by rfl) ⟨1146647, by rfl⟩ : syracuseStep 1528863 = 2293295) B2293295
theorem B8705627 : Blo 1528461 8705627 := bstep (se 1 (by rfl) ⟨6529220, by rfl⟩ : syracuseStep 8705627 = 13058441) B13058441
theorem B16537297 : Blo 1528461 16537297 := bstep (se 2 (by rfl) ⟨6201486, by rfl⟩ : syracuseStep 16537297 = 12402973) B12402973
theorem B1529627 : Blo 1528461 1529627 := bstep (se 1 (by rfl) ⟨1147220, by rfl⟩ : syracuseStep 1529627 = 2294441) B2294441
theorem B6289517 : Blo 1528461 6289517 := bstep (se 3 (by rfl) ⟨1179284, by rfl⟩ : syracuseStep 6289517 = 2358569) B2358569
theorem B53008505 : Blo 1528461 53008505 := bstep (se 2 (by rfl) ⟨19878189, by rfl⟩ : syracuseStep 53008505 = 39756379) B39756379
theorem B1530183 : Blo 1528461 1530183 := bstep (se 1 (by rfl) ⟨1147637, by rfl⟩ : syracuseStep 1530183 = 2295275) B2295275
theorem B2178047 : Blo 1528461 2178047 := bstep (se 1 (by rfl) ⟨1633535, by rfl⟩ : syracuseStep 2178047 = 3267071) B3267071
theorem B4357223 : Blo 1528461 4357223 := bstep (se 1 (by rfl) ⟨3267917, by rfl⟩ : syracuseStep 4357223 = 6535835) B6535835
theorem B5160617 : Blo 1528461 5160617 := bstep (se 2 (by rfl) ⟨1935231, by rfl⟩ : syracuseStep 5160617 = 3870463) B3870463
theorem B2293787 : Blo 1528461 2293787 := bstep (se 1 (by rfl) ⟨1720340, by rfl⟩ : syracuseStep 2293787 = 3440681) B3440681
theorem B3441311 : Blo 1528461 3441311 := bstep (se 1 (by rfl) ⟨2580983, by rfl⟩ : syracuseStep 3441311 = 5161967) B5161967
theorem B5808125 : Blo 1528461 5808125 := bstep (se 3 (by rfl) ⟨1089023, by rfl⟩ : syracuseStep 5808125 = 2178047) B2178047
theorem B5162237 : Blo 1528461 5162237 := bstep (se 3 (by rfl) ⟨967919, by rfl⟩ : syracuseStep 5162237 = 1935839) B1935839
theorem B3442031 : Blo 1528461 3442031 := bstep (se 1 (by rfl) ⟨2581523, by rfl⟩ : syracuseStep 3442031 = 5163047) B5163047
theorem B5803751 : Blo 1528461 5803751 := bstep (se 1 (by rfl) ⟨4352813, by rfl⟩ : syracuseStep 5803751 = 8705627) B8705627
theorem B2904815 : Blo 1528461 2904815 := bstep (se 1 (by rfl) ⟨2178611, by rfl⟩ : syracuseStep 2904815 = 4357223) B4357223
theorem B22049729 : Blo 1528461 22049729 := bstep (se 2 (by rfl) ⟨8268648, by rfl⟩ : syracuseStep 22049729 = 16537297) B16537297
theorem B10073117 : Blo 1528461 10073117 := bstep (se 3 (by rfl) ⟨1888709, by rfl⟩ : syracuseStep 10073117 = 3777419) B3777419
theorem B100611193 : Blo 1528461 100611193 := bstep (se 2 (by rfl) ⟨37729197, by rfl⟩ : syracuseStep 100611193 = 75458395) B75458395
theorem B1529599 : Blo 1528461 1529599 := bstep (se 1 (by rfl) ⟨1147199, by rfl⟩ : syracuseStep 1529599 = 2294399) B2294399
theorem B7739711 : Blo 1528461 7739711 := bstep (se 1 (by rfl) ⟨5804783, by rfl⟩ : syracuseStep 7739711 = 11609567) B11609567
theorem B40262123 : Blo 1528461 40262123 := bstep (se 1 (by rfl) ⟨30196592, by rfl⟩ : syracuseStep 40262123 = 60393185) B60393185
theorem B4193011 : Blo 1528461 4193011 := bstep (se 1 (by rfl) ⟨3144758, by rfl⟩ : syracuseStep 4193011 = 6289517) B6289517
theorem B35339003 : Blo 1528461 35339003 := bstep (se 1 (by rfl) ⟨26504252, by rfl⟩ : syracuseStep 35339003 = 53008505) B53008505
theorem B3440411 : Blo 1528461 3440411 := bstep (se 1 (by rfl) ⟨2580308, by rfl⟩ : syracuseStep 3440411 = 5160617) B5160617
theorem B26861645 : Blo 1528461 26861645 := bstep (se 3 (by rfl) ⟨5036558, by rfl⟩ : syracuseStep 26861645 = 10073117) B10073117
theorem B2294207 : Blo 1528461 2294207 := bstep (se 1 (by rfl) ⟨1720655, by rfl⟩ : syracuseStep 2294207 = 3441311) B3441311
theorem B3441491 : Blo 1528461 3441491 := bstep (se 1 (by rfl) ⟨2581118, by rfl⟩ : syracuseStep 3441491 = 5162237) B5162237
theorem B2294687 : Blo 1528461 2294687 := bstep (se 1 (by rfl) ⟨1721015, by rfl⟩ : syracuseStep 2294687 = 3442031) B3442031
theorem B107365661 : Blo 1528461 107365661 := bstep (se 3 (by rfl) ⟨20131061, by rfl⟩ : syracuseStep 107365661 = 40262123) B40262123
theorem B3869167 : Blo 1528461 3869167 := bstep (se 1 (by rfl) ⟨2901875, by rfl⟩ : syracuseStep 3869167 = 5803751) B5803751
theorem B1936543 : Blo 1528461 1936543 := bstep (se 1 (by rfl) ⟨1452407, by rfl⟩ : syracuseStep 1936543 = 2904815) B2904815
theorem B14699819 : Blo 1528461 14699819 := bstep (se 1 (by rfl) ⟨11024864, by rfl⟩ : syracuseStep 14699819 = 22049729) B22049729
theorem B134148257 : Blo 1528461 134148257 := bstep (se 2 (by rfl) ⟨50305596, by rfl⟩ : syracuseStep 134148257 = 100611193) B100611193
theorem B3872083 : Blo 1528461 3872083 := bstep (se 1 (by rfl) ⟨2904062, by rfl⟩ : syracuseStep 3872083 = 5808125) B5808125
theorem B1529191 : Blo 1528461 1529191 := bstep (se 1 (by rfl) ⟨1146893, by rfl⟩ : syracuseStep 1529191 = 2293787) B2293787
theorem B22362725 : Blo 1528461 22362725 := bstep (se 4 (by rfl) ⟨2096505, by rfl⟩ : syracuseStep 22362725 = 4193011) B4193011
theorem B5159807 : Blo 1528461 5159807 := bstep (se 1 (by rfl) ⟨3869855, by rfl⟩ : syracuseStep 5159807 = 7739711) B7739711
theorem B23559335 : Blo 1528461 23559335 := bstep (se 1 (by rfl) ⟨17669501, by rfl⟩ : syracuseStep 23559335 = 35339003) B35339003
theorem B2293607 : Blo 1528461 2293607 := bstep (se 1 (by rfl) ⟨1720205, by rfl⟩ : syracuseStep 2293607 = 3440411) B3440411
theorem B89432171 : Blo 1528461 89432171 := bstep (se 1 (by rfl) ⟨67074128, by rfl⟩ : syracuseStep 89432171 = 134148257) B134148257
theorem B71631053 : Blo 1528461 71631053 := bstep (se 3 (by rfl) ⟨13430822, by rfl⟩ : syracuseStep 71631053 = 26861645) B26861645
theorem B2294327 : Blo 1528461 2294327 := bstep (se 1 (by rfl) ⟨1720745, by rfl⟩ : syracuseStep 2294327 = 3441491) B3441491
theorem B2582057 : Blo 1528461 2582057 := bstep (se 2 (by rfl) ⟨968271, by rfl⟩ : syracuseStep 2582057 = 1936543) B1936543
theorem B5162777 : Blo 1528461 5162777 := bstep (se 2 (by rfl) ⟨1936041, by rfl⟩ : syracuseStep 5162777 = 3872083) B3872083
theorem B15706223 : Blo 1528461 15706223 := bstep (se 1 (by rfl) ⟨11779667, by rfl⟩ : syracuseStep 15706223 = 23559335) B23559335
theorem B9799879 : Blo 1528461 9799879 := bstep (se 1 (by rfl) ⟨7349909, by rfl⟩ : syracuseStep 9799879 = 14699819) B14699819
theorem B71577107 : Blo 1528461 71577107 := bstep (se 1 (by rfl) ⟨53682830, by rfl⟩ : syracuseStep 71577107 = 107365661) B107365661
theorem B1529071 : Blo 1528461 1529071 := bstep (se 1 (by rfl) ⟨1146803, by rfl⟩ : syracuseStep 1529071 = 2293607) B2293607
theorem B1529471 : Blo 1528461 1529471 := bstep (se 1 (by rfl) ⟨1147103, by rfl⟩ : syracuseStep 1529471 = 2294207) B2294207
theorem B1529791 : Blo 1528461 1529791 := bstep (se 1 (by rfl) ⟨1147343, by rfl⟩ : syracuseStep 1529791 = 2294687) B2294687
theorem B5158889 : Blo 1528461 5158889 := bstep (se 2 (by rfl) ⟨1934583, by rfl⟩ : syracuseStep 5158889 = 3869167) B3869167
theorem B14908483 : Blo 1528461 14908483 := bstep (se 1 (by rfl) ⟨11181362, by rfl⟩ : syracuseStep 14908483 = 22362725) B22362725
theorem B3439871 : Blo 1528461 3439871 := bstep (se 1 (by rfl) ⟨2579903, by rfl⟩ : syracuseStep 3439871 = 5159807) B5159807
theorem B59621447 : Blo 1528461 59621447 := bstep (se 1 (by rfl) ⟨44716085, by rfl⟩ : syracuseStep 59621447 = 89432171) B89432171
theorem B13066505 : Blo 1528461 13066505 := bstep (se 2 (by rfl) ⟨4899939, by rfl⟩ : syracuseStep 13066505 = 9799879) B9799879
theorem B1721371 : Blo 1528461 1721371 := bstep (se 1 (by rfl) ⟨1291028, by rfl⟩ : syracuseStep 1721371 = 2582057) B2582057
theorem B3441851 : Blo 1528461 3441851 := bstep (se 1 (by rfl) ⟨2581388, by rfl⟩ : syracuseStep 3441851 = 5162777) B5162777
theorem B10470815 : Blo 1528461 10470815 := bstep (se 1 (by rfl) ⟨7853111, by rfl⟩ : syracuseStep 10470815 = 15706223) B15706223
theorem B47754035 : Blo 1528461 47754035 := bstep (se 1 (by rfl) ⟨35815526, by rfl⟩ : syracuseStep 47754035 = 71631053) B71631053
theorem B19877977 : Blo 1528461 19877977 := bstep (se 2 (by rfl) ⟨7454241, by rfl⟩ : syracuseStep 19877977 = 14908483) B14908483
theorem B1529551 : Blo 1528461 1529551 := bstep (se 1 (by rfl) ⟨1147163, by rfl⟩ : syracuseStep 1529551 = 2294327) B2294327
theorem B3439259 : Blo 1528461 3439259 := bstep (se 1 (by rfl) ⟨2579444, by rfl⟩ : syracuseStep 3439259 = 5158889) B5158889
theorem B2293247 : Blo 1528461 2293247 := bstep (se 1 (by rfl) ⟨1719935, by rfl⟩ : syracuseStep 2293247 = 3439871) B3439871
theorem B47718071 : Blo 1528461 47718071 := bstep (se 1 (by rfl) ⟨35788553, by rfl⟩ : syracuseStep 47718071 = 71577107) B71577107
theorem B158990525 : Blo 1528461 158990525 := bstep (se 3 (by rfl) ⟨29810723, by rfl⟩ : syracuseStep 158990525 = 59621447) B59621447
theorem B2294567 : Blo 1528461 2294567 := bstep (se 1 (by rfl) ⟨1720925, by rfl⟩ : syracuseStep 2294567 = 3441851) B3441851
theorem B6980543 : Blo 1528461 6980543 := bstep (se 1 (by rfl) ⟨5235407, by rfl⟩ : syracuseStep 6980543 = 10470815) B10470815
theorem B2295161 : Blo 1528461 2295161 := bstep (se 2 (by rfl) ⟨860685, by rfl⟩ : syracuseStep 2295161 = 1721371) B1721371
theorem B31836023 : Blo 1528461 31836023 := bstep (se 1 (by rfl) ⟨23877017, by rfl⟩ : syracuseStep 31836023 = 47754035) B47754035
theorem B31812047 : Blo 1528461 31812047 := bstep (se 1 (by rfl) ⟨23859035, by rfl⟩ : syracuseStep 31812047 = 47718071) B47718071
theorem B26503969 : Blo 1528461 26503969 := bstep (se 2 (by rfl) ⟨9938988, by rfl⟩ : syracuseStep 26503969 = 19877977) B19877977
theorem B8711003 : Blo 1528461 8711003 := bstep (se 1 (by rfl) ⟨6533252, by rfl⟩ : syracuseStep 8711003 = 13066505) B13066505
theorem B1528831 : Blo 1528461 1528831 := bstep (se 1 (by rfl) ⟨1146623, by rfl⟩ : syracuseStep 1528831 = 2293247) B2293247
theorem B2292839 : Blo 1528461 2292839 := bstep (se 1 (by rfl) ⟨1719629, by rfl⟩ : syracuseStep 2292839 = 3439259) B3439259
theorem B4653695 : Blo 1528461 4653695 := bstep (se 1 (by rfl) ⟨3490271, by rfl⟩ : syracuseStep 4653695 = 6980543) B6980543
theorem B1528559 : Blo 1528461 1528559 := bstep (se 1 (by rfl) ⟨1146419, by rfl⟩ : syracuseStep 1528559 = 2292839) B2292839
theorem B105993683 : Blo 1528461 105993683 := bstep (se 1 (by rfl) ⟨79495262, by rfl⟩ : syracuseStep 105993683 = 158990525) B158990525
theorem B1529711 : Blo 1528461 1529711 := bstep (se 1 (by rfl) ⟨1147283, by rfl⟩ : syracuseStep 1529711 = 2294567) B2294567
theorem B1530107 : Blo 1528461 1530107 := bstep (se 1 (by rfl) ⟨1147580, by rfl⟩ : syracuseStep 1530107 = 2295161) B2295161
theorem B35338625 : Blo 1528461 35338625 := bstep (se 2 (by rfl) ⟨13251984, by rfl⟩ : syracuseStep 35338625 = 26503969) B26503969
theorem B21224015 : Blo 1528461 21224015 := bstep (se 1 (by rfl) ⟨15918011, by rfl⟩ : syracuseStep 21224015 = 31836023) B31836023
theorem B21208031 : Blo 1528461 21208031 := bstep (se 1 (by rfl) ⟨15906023, by rfl⟩ : syracuseStep 21208031 = 31812047) B31812047
theorem B5807335 : Blo 1528461 5807335 := bstep (se 1 (by rfl) ⟨4355501, by rfl⟩ : syracuseStep 5807335 = 8711003) B8711003
theorem B7743113 : Blo 1528461 7743113 := bstep (se 2 (by rfl) ⟨2903667, by rfl⟩ : syracuseStep 7743113 = 5807335) B5807335
theorem B14149343 : Blo 1528461 14149343 := bstep (se 1 (by rfl) ⟨10612007, by rfl⟩ : syracuseStep 14149343 = 21224015) B21224015
theorem B3102463 : Blo 1528461 3102463 := bstep (se 1 (by rfl) ⟨2326847, by rfl⟩ : syracuseStep 3102463 = 4653695) B4653695
theorem B70662455 : Blo 1528461 70662455 := bstep (se 1 (by rfl) ⟨52996841, by rfl⟩ : syracuseStep 70662455 = 105993683) B105993683
theorem B23559083 : Blo 1528461 23559083 := bstep (se 1 (by rfl) ⟨17669312, by rfl⟩ : syracuseStep 23559083 = 35338625) B35338625
theorem B14138687 : Blo 1528461 14138687 := bstep (se 1 (by rfl) ⟨10604015, by rfl⟩ : syracuseStep 14138687 = 21208031) B21208031
theorem B5162075 : Blo 1528461 5162075 := bstep (se 1 (by rfl) ⟨3871556, by rfl⟩ : syracuseStep 5162075 = 7743113) B7743113
theorem B15706055 : Blo 1528461 15706055 := bstep (se 1 (by rfl) ⟨11779541, by rfl⟩ : syracuseStep 15706055 = 23559083) B23559083
theorem B9432895 : Blo 1528461 9432895 := bstep (se 1 (by rfl) ⟨7074671, by rfl⟩ : syracuseStep 9432895 = 14149343) B14149343
theorem B47108303 : Blo 1528461 47108303 := bstep (se 1 (by rfl) ⟨35331227, by rfl⟩ : syracuseStep 47108303 = 70662455) B70662455
theorem B9425791 : Blo 1528461 9425791 := bstep (se 1 (by rfl) ⟨7069343, by rfl⟩ : syracuseStep 9425791 = 14138687) B14138687
theorem B4136617 : Blo 1528461 4136617 := bstep (se 2 (by rfl) ⟨1551231, by rfl⟩ : syracuseStep 4136617 = 3102463) B3102463
theorem B3441383 : Blo 1528461 3441383 := bstep (se 1 (by rfl) ⟨2581037, by rfl⟩ : syracuseStep 3441383 = 5162075) B5162075
theorem B12567721 : Blo 1528461 12567721 := bstep (se 2 (by rfl) ⟨4712895, by rfl⟩ : syracuseStep 12567721 = 9425791) B9425791
theorem B10470703 : Blo 1528461 10470703 := bstep (se 1 (by rfl) ⟨7853027, by rfl⟩ : syracuseStep 10470703 = 15706055) B15706055
theorem B5515489 : Blo 1528461 5515489 := bstep (se 2 (by rfl) ⟨2068308, by rfl⟩ : syracuseStep 5515489 = 4136617) B4136617
theorem B12577193 : Blo 1528461 12577193 := bstep (se 2 (by rfl) ⟨4716447, by rfl⟩ : syracuseStep 12577193 = 9432895) B9432895
theorem B31405535 : Blo 1528461 31405535 := bstep (se 1 (by rfl) ⟨23554151, by rfl⟩ : syracuseStep 31405535 = 47108303) B47108303
theorem B2294255 : Blo 1528461 2294255 := bstep (se 1 (by rfl) ⟨1720691, by rfl⟩ : syracuseStep 2294255 = 3441383) B3441383
theorem B13960937 : Blo 1528461 13960937 := bstep (se 2 (by rfl) ⟨5235351, by rfl⟩ : syracuseStep 13960937 = 10470703) B10470703
theorem B16756961 : Blo 1528461 16756961 := bstep (se 2 (by rfl) ⟨6283860, by rfl⟩ : syracuseStep 16756961 = 12567721) B12567721
theorem B8384795 : Blo 1528461 8384795 := bstep (se 1 (by rfl) ⟨6288596, by rfl⟩ : syracuseStep 8384795 = 12577193) B12577193
theorem B7353985 : Blo 1528461 7353985 := bstep (se 2 (by rfl) ⟨2757744, by rfl⟩ : syracuseStep 7353985 = 5515489) B5515489
theorem B20937023 : Blo 1528461 20937023 := bstep (se 1 (by rfl) ⟨15702767, by rfl⟩ : syracuseStep 20937023 = 31405535) B31405535
theorem B5589863 : Blo 1528461 5589863 := bstep (se 1 (by rfl) ⟨4192397, by rfl⟩ : syracuseStep 5589863 = 8384795) B8384795
theorem B37229165 : Blo 1528461 37229165 := bstep (se 3 (by rfl) ⟨6980468, by rfl⟩ : syracuseStep 37229165 = 13960937) B13960937
theorem B1529503 : Blo 1528461 1529503 := bstep (se 1 (by rfl) ⟨1147127, by rfl⟩ : syracuseStep 1529503 = 2294255) B2294255
theorem B44685229 : Blo 1528461 44685229 := bstep (se 3 (by rfl) ⟨8378480, by rfl⟩ : syracuseStep 44685229 = 16756961) B16756961
theorem B13958015 : Blo 1528461 13958015 := bstep (se 1 (by rfl) ⟨10468511, by rfl⟩ : syracuseStep 13958015 = 20937023) B20937023
theorem B9805313 : Blo 1528461 9805313 := bstep (se 2 (by rfl) ⟨3676992, by rfl⟩ : syracuseStep 9805313 = 7353985) B7353985
theorem B37221373 : Blo 1528461 37221373 := bstep (se 3 (by rfl) ⟨6979007, by rfl⟩ : syracuseStep 37221373 = 13958015) B13958015
theorem B24819443 : Blo 1528461 24819443 := bstep (se 1 (by rfl) ⟨18614582, by rfl⟩ : syracuseStep 24819443 = 37229165) B37229165
theorem B3726575 : Blo 1528461 3726575 := bstep (se 1 (by rfl) ⟨2794931, by rfl⟩ : syracuseStep 3726575 = 5589863) B5589863
theorem B6536875 : Blo 1528461 6536875 := bstep (se 1 (by rfl) ⟨4902656, by rfl⟩ : syracuseStep 6536875 = 9805313) B9805313
theorem B59580305 : Blo 1528461 59580305 := bstep (se 2 (by rfl) ⟨22342614, by rfl⟩ : syracuseStep 59580305 = 44685229) B44685229
theorem B49628497 : Blo 1528461 49628497 := bstep (se 2 (by rfl) ⟨18610686, by rfl⟩ : syracuseStep 49628497 = 37221373) B37221373
theorem B2484383 : Blo 1528461 2484383 := bstep (se 1 (by rfl) ⟨1863287, by rfl⟩ : syracuseStep 2484383 = 3726575) B3726575
theorem B39720203 : Blo 1528461 39720203 := bstep (se 1 (by rfl) ⟨29790152, by rfl⟩ : syracuseStep 39720203 = 59580305) B59580305
theorem B16546295 : Blo 1528461 16546295 := bstep (se 1 (by rfl) ⟨12409721, by rfl⟩ : syracuseStep 16546295 = 24819443) B24819443
theorem B8715833 : Blo 1528461 8715833 := bstep (se 2 (by rfl) ⟨3268437, by rfl⟩ : syracuseStep 8715833 = 6536875) B6536875
theorem B5810555 : Blo 1528461 5810555 := bstep (se 1 (by rfl) ⟨4357916, by rfl⟩ : syracuseStep 5810555 = 8715833) B8715833
theorem B26480135 : Blo 1528461 26480135 := bstep (se 1 (by rfl) ⟨19860101, by rfl⟩ : syracuseStep 26480135 = 39720203) B39720203
theorem B11030863 : Blo 1528461 11030863 := bstep (se 1 (by rfl) ⟨8273147, by rfl⟩ : syracuseStep 11030863 = 16546295) B16546295
theorem B66171329 : Blo 1528461 66171329 := bstep (se 2 (by rfl) ⟨24814248, by rfl⟩ : syracuseStep 66171329 = 49628497) B49628497
theorem B6625021 : Blo 1528461 6625021 := bstep (se 3 (by rfl) ⟨1242191, by rfl⟩ : syracuseStep 6625021 = 2484383) B2484383
theorem B44114219 : Blo 1528461 44114219 := bstep (se 1 (by rfl) ⟨33085664, by rfl⟩ : syracuseStep 44114219 = 66171329) B66171329
theorem B14707817 : Blo 1528461 14707817 := bstep (se 2 (by rfl) ⟨5515431, by rfl⟩ : syracuseStep 14707817 = 11030863) B11030863
theorem B141333781 : Blo 1528461 141333781 := bstep (se 6 (by rfl) ⟨3312510, by rfl⟩ : syracuseStep 141333781 = 6625021) B6625021
theorem B3873703 : Blo 1528461 3873703 := bstep (se 1 (by rfl) ⟨2905277, by rfl⟩ : syracuseStep 3873703 = 5810555) B5810555
theorem B17653423 : Blo 1528461 17653423 := bstep (se 1 (by rfl) ⟨13240067, by rfl⟩ : syracuseStep 17653423 = 26480135) B26480135
theorem B29409479 : Blo 1528461 29409479 := bstep (se 1 (by rfl) ⟨22057109, by rfl⟩ : syracuseStep 29409479 = 44114219) B44114219
theorem B23537897 : Blo 1528461 23537897 := bstep (se 2 (by rfl) ⟨8826711, by rfl⟩ : syracuseStep 23537897 = 17653423) B17653423
theorem B5164937 : Blo 1528461 5164937 := bstep (se 2 (by rfl) ⟨1936851, by rfl⟩ : syracuseStep 5164937 = 3873703) B3873703
theorem B188445041 : Blo 1528461 188445041 := bstep (se 2 (by rfl) ⟨70666890, by rfl⟩ : syracuseStep 188445041 = 141333781) B141333781
theorem B9805211 : Blo 1528461 9805211 := bstep (se 1 (by rfl) ⟨7353908, by rfl⟩ : syracuseStep 9805211 = 14707817) B14707817
theorem B3443291 : Blo 1528461 3443291 := bstep (se 1 (by rfl) ⟨2582468, by rfl⟩ : syracuseStep 3443291 = 5164937) B5164937
theorem B19606319 : Blo 1528461 19606319 := bstep (se 1 (by rfl) ⟨14704739, by rfl⟩ : syracuseStep 19606319 = 29409479) B29409479
theorem B15691931 : Blo 1528461 15691931 := bstep (se 1 (by rfl) ⟨11768948, by rfl⟩ : syracuseStep 15691931 = 23537897) B23537897
theorem B125630027 : Blo 1528461 125630027 := bstep (se 1 (by rfl) ⟨94222520, by rfl⟩ : syracuseStep 125630027 = 188445041) B188445041
theorem B6536807 : Blo 1528461 6536807 := bstep (se 1 (by rfl) ⟨4902605, by rfl⟩ : syracuseStep 6536807 = 9805211) B9805211
theorem B10461287 : Blo 1528461 10461287 := bstep (se 1 (by rfl) ⟨7845965, by rfl⟩ : syracuseStep 10461287 = 15691931) B15691931
theorem B2295527 : Blo 1528461 2295527 := bstep (se 1 (by rfl) ⟨1721645, by rfl⟩ : syracuseStep 2295527 = 3443291) B3443291
theorem B13070879 : Blo 1528461 13070879 := bstep (se 1 (by rfl) ⟨9803159, by rfl⟩ : syracuseStep 13070879 = 19606319) B19606319
theorem B83753351 : Blo 1528461 83753351 := bstep (se 1 (by rfl) ⟨62815013, by rfl⟩ : syracuseStep 83753351 = 125630027) B125630027
theorem B4357871 : Blo 1528461 4357871 := bstep (se 1 (by rfl) ⟨3268403, by rfl⟩ : syracuseStep 4357871 = 6536807) B6536807
theorem B6974191 : Blo 1528461 6974191 := bstep (se 1 (by rfl) ⟨5230643, by rfl⟩ : syracuseStep 6974191 = 10461287) B10461287
theorem B2905247 : Blo 1528461 2905247 := bstep (se 1 (by rfl) ⟨2178935, by rfl⟩ : syracuseStep 2905247 = 4357871) B4357871
theorem B8713919 : Blo 1528461 8713919 := bstep (se 1 (by rfl) ⟨6535439, by rfl⟩ : syracuseStep 8713919 = 13070879) B13070879
theorem B1530351 : Blo 1528461 1530351 := bstep (se 1 (by rfl) ⟨1147763, by rfl⟩ : syracuseStep 1530351 = 2295527) B2295527
theorem B55835567 : Blo 1528461 55835567 := bstep (se 1 (by rfl) ⟨41876675, by rfl⟩ : syracuseStep 55835567 = 83753351) B83753351
theorem B5809279 : Blo 1528461 5809279 := bstep (se 1 (by rfl) ⟨4356959, by rfl⟩ : syracuseStep 5809279 = 8713919) B8713919
theorem B37195685 : Blo 1528461 37195685 := bstep (se 4 (by rfl) ⟨3487095, by rfl⟩ : syracuseStep 37195685 = 6974191) B6974191
theorem B7747325 : Blo 1528461 7747325 := bstep (se 3 (by rfl) ⟨1452623, by rfl⟩ : syracuseStep 7747325 = 2905247) B2905247
theorem B37223711 : Blo 1528461 37223711 := bstep (se 1 (by rfl) ⟨27917783, by rfl⟩ : syracuseStep 37223711 = 55835567) B55835567
theorem B24815807 : Blo 1528461 24815807 := bstep (se 1 (by rfl) ⟨18611855, by rfl⟩ : syracuseStep 24815807 = 37223711) B37223711
theorem B5164883 : Blo 1528461 5164883 := bstep (se 1 (by rfl) ⟨3873662, by rfl⟩ : syracuseStep 5164883 = 7747325) B7747325
theorem B7745705 : Blo 1528461 7745705 := bstep (se 2 (by rfl) ⟨2904639, by rfl⟩ : syracuseStep 7745705 = 5809279) B5809279
theorem B24797123 : Blo 1528461 24797123 := bstep (se 1 (by rfl) ⟨18597842, by rfl⟩ : syracuseStep 24797123 = 37195685) B37195685
theorem B3443255 : Blo 1528461 3443255 := bstep (se 1 (by rfl) ⟨2582441, by rfl⟩ : syracuseStep 3443255 = 5164883) B5164883
theorem B5163803 : Blo 1528461 5163803 := bstep (se 1 (by rfl) ⟨3872852, by rfl⟩ : syracuseStep 5163803 = 7745705) B7745705
theorem B16543871 : Blo 1528461 16543871 := bstep (se 1 (by rfl) ⟨12407903, by rfl⟩ : syracuseStep 16543871 = 24815807) B24815807
theorem B16531415 : Blo 1528461 16531415 := bstep (se 1 (by rfl) ⟨12398561, by rfl⟩ : syracuseStep 16531415 = 24797123) B24797123
theorem B2295503 : Blo 1528461 2295503 := bstep (se 1 (by rfl) ⟨1721627, by rfl⟩ : syracuseStep 2295503 = 3443255) B3443255
theorem B3442535 : Blo 1528461 3442535 := bstep (se 1 (by rfl) ⟨2581901, by rfl⟩ : syracuseStep 3442535 = 5163803) B5163803
theorem B11020943 : Blo 1528461 11020943 := bstep (se 1 (by rfl) ⟨8265707, by rfl⟩ : syracuseStep 11020943 = 16531415) B16531415
theorem B11029247 : Blo 1528461 11029247 := bstep (se 1 (by rfl) ⟨8271935, by rfl⟩ : syracuseStep 11029247 = 16543871) B16543871
theorem B2295023 : Blo 1528461 2295023 := bstep (se 1 (by rfl) ⟨1721267, by rfl⟩ : syracuseStep 2295023 = 3442535) B3442535
theorem B7352831 : Blo 1528461 7352831 := bstep (se 1 (by rfl) ⟨5514623, by rfl⟩ : syracuseStep 7352831 = 11029247) B11029247
theorem B1530335 : Blo 1528461 1530335 := bstep (se 1 (by rfl) ⟨1147751, by rfl⟩ : syracuseStep 1530335 = 2295503) B2295503
theorem B7347295 : Blo 1528461 7347295 := bstep (se 1 (by rfl) ⟨5510471, by rfl⟩ : syracuseStep 7347295 = 11020943) B11020943
theorem B4901887 : Blo 1528461 4901887 := bstep (se 1 (by rfl) ⟨3676415, by rfl⟩ : syracuseStep 4901887 = 7352831) B7352831
theorem B1530015 : Blo 1528461 1530015 := bstep (se 1 (by rfl) ⟨1147511, by rfl⟩ : syracuseStep 1530015 = 2295023) B2295023
theorem B9796393 : Blo 1528461 9796393 := bstep (se 2 (by rfl) ⟨3673647, by rfl⟩ : syracuseStep 9796393 = 7347295) B7347295
theorem B26143397 : Blo 1528461 26143397 := bstep (se 4 (by rfl) ⟨2450943, by rfl⟩ : syracuseStep 26143397 = 4901887) B4901887
theorem B13061857 : Blo 1528461 13061857 := bstep (se 2 (by rfl) ⟨4898196, by rfl⟩ : syracuseStep 13061857 = 9796393) B9796393
theorem B17428931 : Blo 1528461 17428931 := bstep (se 1 (by rfl) ⟨13071698, by rfl⟩ : syracuseStep 17428931 = 26143397) B26143397
theorem B17415809 : Blo 1528461 17415809 := bstep (se 2 (by rfl) ⟨6530928, by rfl⟩ : syracuseStep 17415809 = 13061857) B13061857
theorem B11610539 : Blo 1528461 11610539 := bstep (se 1 (by rfl) ⟨8707904, by rfl⟩ : syracuseStep 11610539 = 17415809) B17415809
theorem B11619287 : Blo 1528461 11619287 := bstep (se 1 (by rfl) ⟨8714465, by rfl⟩ : syracuseStep 11619287 = 17428931) B17428931
theorem B7746191 : Blo 1528461 7746191 := bstep (se 1 (by rfl) ⟨5809643, by rfl⟩ : syracuseStep 7746191 = 11619287) B11619287
theorem B7740359 : Blo 1528461 7740359 := bstep (se 1 (by rfl) ⟨5805269, by rfl⟩ : syracuseStep 7740359 = 11610539) B11610539
theorem B5164127 : Blo 1528461 5164127 := bstep (se 1 (by rfl) ⟨3873095, by rfl⟩ : syracuseStep 5164127 = 7746191) B7746191
theorem B5160239 : Blo 1528461 5160239 := bstep (se 1 (by rfl) ⟨3870179, by rfl⟩ : syracuseStep 5160239 = 7740359) B7740359
theorem B3442751 : Blo 1528461 3442751 := bstep (se 1 (by rfl) ⟨2582063, by rfl⟩ : syracuseStep 3442751 = 5164127) B5164127
theorem B3440159 : Blo 1528461 3440159 := bstep (se 1 (by rfl) ⟨2580119, by rfl⟩ : syracuseStep 3440159 = 5160239) B5160239
theorem B2295167 : Blo 1528461 2295167 := bstep (se 1 (by rfl) ⟨1721375, by rfl⟩ : syracuseStep 2295167 = 3442751) B3442751
theorem B2293439 : Blo 1528461 2293439 := bstep (se 1 (by rfl) ⟨1720079, by rfl⟩ : syracuseStep 2293439 = 3440159) B3440159
theorem B1528959 : Blo 1528461 1528959 := bstep (se 1 (by rfl) ⟨1146719, by rfl⟩ : syracuseStep 1528959 = 2293439) B2293439
theorem B1530111 : Blo 1528461 1530111 := bstep (se 1 (by rfl) ⟨1147583, by rfl⟩ : syracuseStep 1530111 = 2295167) B2295167

theorem C0 (j : ℕ) (h1 : 382115 ≤ j) (h2 : j ≤ 382614) : Blo 1528461 (4 * j + 3) := by
  interval_cases j
  · exact B1528463
  · exact B1528467
  · exact B1528471
  · exact B1528475
  · exact B1528479
  · exact B1528483
  · exact B1528487
  · exact B1528491
  · exact B1528495
  · exact B1528499
  · exact B1528503
  · exact B1528507
  · exact B1528511
  · exact B1528515
  · exact B1528519
  · exact B1528523
  · exact B1528527
  · exact B1528531
  · exact B1528535
  · exact B1528539
  · exact B1528543
  · exact B1528547
  · exact B1528551
  · exact B1528555
  · exact B1528559
  · exact B1528563
  · exact B1528567
  · exact B1528571
  · exact B1528575
  · exact B1528579
  · exact B1528583
  · exact B1528587
  · exact B1528591
  · exact B1528595
  · exact B1528599
  · exact B1528603
  · exact B1528607
  · exact B1528611
  · exact B1528615
  · exact B1528619
  · exact B1528623
  · exact B1528627
  · exact B1528631
  · exact B1528635
  · exact B1528639
  · exact B1528643
  · exact B1528647
  · exact B1528651
  · exact B1528655
  · exact B1528659
  · exact B1528663
  · exact B1528667
  · exact B1528671
  · exact B1528675
  · exact B1528679
  · exact B1528683
  · exact B1528687
  · exact B1528691
  · exact B1528695
  · exact B1528699
  · exact B1528703
  · exact B1528707
  · exact B1528711
  · exact B1528715
  · exact B1528719
  · exact B1528723
  · exact B1528727
  · exact B1528731
  · exact B1528735
  · exact B1528739
  · exact B1528743
  · exact B1528747
  · exact B1528751
  · exact B1528755
  · exact B1528759
  · exact B1528763
  · exact B1528767
  · exact B1528771
  · exact B1528775
  · exact B1528779
  · exact B1528783
  · exact B1528787
  · exact B1528791
  · exact B1528795
  · exact B1528799
  · exact B1528803
  · exact B1528807
  · exact B1528811
  · exact B1528815
  · exact B1528819
  · exact B1528823
  · exact B1528827
  · exact B1528831
  · exact B1528835
  · exact B1528839
  · exact B1528843
  · exact B1528847
  · exact B1528851
  · exact B1528855
  · exact B1528859
  · exact B1528863
  · exact B1528867
  · exact B1528871
  · exact B1528875
  · exact B1528879
  · exact B1528883
  · exact B1528887
  · exact B1528891
  · exact B1528895
  · exact B1528899
  · exact B1528903
  · exact B1528907
  · exact B1528911
  · exact B1528915
  · exact B1528919
  · exact B1528923
  · exact B1528927
  · exact B1528931
  · exact B1528935
  · exact B1528939
  · exact B1528943
  · exact B1528947
  · exact B1528951
  · exact B1528955
  · exact B1528959
  · exact B1528963
  · exact B1528967
  · exact B1528971
  · exact B1528975
  · exact B1528979
  · exact B1528983
  · exact B1528987
  · exact B1528991
  · exact B1528995
  · exact B1528999
  · exact B1529003
  · exact B1529007
  · exact B1529011
  · exact B1529015
  · exact B1529019
  · exact B1529023
  · exact B1529027
  · exact B1529031
  · exact B1529035
  · exact B1529039
  · exact B1529043
  · exact B1529047
  · exact B1529051
  · exact B1529055
  · exact B1529059
  · exact B1529063
  · exact B1529067
  · exact B1529071
  · exact B1529075
  · exact B1529079
  · exact B1529083
  · exact B1529087
  · exact B1529091
  · exact B1529095
  · exact B1529099
  · exact B1529103
  · exact B1529107
  · exact B1529111
  · exact B1529115
  · exact B1529119
  · exact B1529123
  · exact B1529127
  · exact B1529131
  · exact B1529135
  · exact B1529139
  · exact B1529143
  · exact B1529147
  · exact B1529151
  · exact B1529155
  · exact B1529159
  · exact B1529163
  · exact B1529167
  · exact B1529171
  · exact B1529175
  · exact B1529179
  · exact B1529183
  · exact B1529187
  · exact B1529191
  · exact B1529195
  · exact B1529199
  · exact B1529203
  · exact B1529207
  · exact B1529211
  · exact B1529215
  · exact B1529219
  · exact B1529223
  · exact B1529227
  · exact B1529231
  · exact B1529235
  · exact B1529239
  · exact B1529243
  · exact B1529247
  · exact B1529251
  · exact B1529255
  · exact B1529259
  · exact B1529263
  · exact B1529267
  · exact B1529271
  · exact B1529275
  · exact B1529279
  · exact B1529283
  · exact B1529287
  · exact B1529291
  · exact B1529295
  · exact B1529299
  · exact B1529303
  · exact B1529307
  · exact B1529311
  · exact B1529315
  · exact B1529319
  · exact B1529323
  · exact B1529327
  · exact B1529331
  · exact B1529335
  · exact B1529339
  · exact B1529343
  · exact B1529347
  · exact B1529351
  · exact B1529355
  · exact B1529359
  · exact B1529363
  · exact B1529367
  · exact B1529371
  · exact B1529375
  · exact B1529379
  · exact B1529383
  · exact B1529387
  · exact B1529391
  · exact B1529395
  · exact B1529399
  · exact B1529403
  · exact B1529407
  · exact B1529411
  · exact B1529415
  · exact B1529419
  · exact B1529423
  · exact B1529427
  · exact B1529431
  · exact B1529435
  · exact B1529439
  · exact B1529443
  · exact B1529447
  · exact B1529451
  · exact B1529455
  · exact B1529459
  · exact B1529463
  · exact B1529467
  · exact B1529471
  · exact B1529475
  · exact B1529479
  · exact B1529483
  · exact B1529487
  · exact B1529491
  · exact B1529495
  · exact B1529499
  · exact B1529503
  · exact B1529507
  · exact B1529511
  · exact B1529515
  · exact B1529519
  · exact B1529523
  · exact B1529527
  · exact B1529531
  · exact B1529535
  · exact B1529539
  · exact B1529543
  · exact B1529547
  · exact B1529551
  · exact B1529555
  · exact B1529559
  · exact B1529563
  · exact B1529567
  · exact B1529571
  · exact B1529575
  · exact B1529579
  · exact B1529583
  · exact B1529587
  · exact B1529591
  · exact B1529595
  · exact B1529599
  · exact B1529603
  · exact B1529607
  · exact B1529611
  · exact B1529615
  · exact B1529619
  · exact B1529623
  · exact B1529627
  · exact B1529631
  · exact B1529635
  · exact B1529639
  · exact B1529643
  · exact B1529647
  · exact B1529651
  · exact B1529655
  · exact B1529659
  · exact B1529663
  · exact B1529667
  · exact B1529671
  · exact B1529675
  · exact B1529679
  · exact B1529683
  · exact B1529687
  · exact B1529691
  · exact B1529695
  · exact B1529699
  · exact B1529703
  · exact B1529707
  · exact B1529711
  · exact B1529715
  · exact B1529719
  · exact B1529723
  · exact B1529727
  · exact B1529731
  · exact B1529735
  · exact B1529739
  · exact B1529743
  · exact B1529747
  · exact B1529751
  · exact B1529755
  · exact B1529759
  · exact B1529763
  · exact B1529767
  · exact B1529771
  · exact B1529775
  · exact B1529779
  · exact B1529783
  · exact B1529787
  · exact B1529791
  · exact B1529795
  · exact B1529799
  · exact B1529803
  · exact B1529807
  · exact B1529811
  · exact B1529815
  · exact B1529819
  · exact B1529823
  · exact B1529827
  · exact B1529831
  · exact B1529835
  · exact B1529839
  · exact B1529843
  · exact B1529847
  · exact B1529851
  · exact B1529855
  · exact B1529859
  · exact B1529863
  · exact B1529867
  · exact B1529871
  · exact B1529875
  · exact B1529879
  · exact B1529883
  · exact B1529887
  · exact B1529891
  · exact B1529895
  · exact B1529899
  · exact B1529903
  · exact B1529907
  · exact B1529911
  · exact B1529915
  · exact B1529919
  · exact B1529923
  · exact B1529927
  · exact B1529931
  · exact B1529935
  · exact B1529939
  · exact B1529943
  · exact B1529947
  · exact B1529951
  · exact B1529955
  · exact B1529959
  · exact B1529963
  · exact B1529967
  · exact B1529971
  · exact B1529975
  · exact B1529979
  · exact B1529983
  · exact B1529987
  · exact B1529991
  · exact B1529995
  · exact B1529999
  · exact B1530003
  · exact B1530007
  · exact B1530011
  · exact B1530015
  · exact B1530019
  · exact B1530023
  · exact B1530027
  · exact B1530031
  · exact B1530035
  · exact B1530039
  · exact B1530043
  · exact B1530047
  · exact B1530051
  · exact B1530055
  · exact B1530059
  · exact B1530063
  · exact B1530067
  · exact B1530071
  · exact B1530075
  · exact B1530079
  · exact B1530083
  · exact B1530087
  · exact B1530091
  · exact B1530095
  · exact B1530099
  · exact B1530103
  · exact B1530107
  · exact B1530111
  · exact B1530115
  · exact B1530119
  · exact B1530123
  · exact B1530127
  · exact B1530131
  · exact B1530135
  · exact B1530139
  · exact B1530143
  · exact B1530147
  · exact B1530151
  · exact B1530155
  · exact B1530159
  · exact B1530163
  · exact B1530167
  · exact B1530171
  · exact B1530175
  · exact B1530179
  · exact B1530183
  · exact B1530187
  · exact B1530191
  · exact B1530195
  · exact B1530199
  · exact B1530203
  · exact B1530207
  · exact B1530211
  · exact B1530215
  · exact B1530219
  · exact B1530223
  · exact B1530227
  · exact B1530231
  · exact B1530235
  · exact B1530239
  · exact B1530243
  · exact B1530247
  · exact B1530251
  · exact B1530255
  · exact B1530259
  · exact B1530263
  · exact B1530267
  · exact B1530271
  · exact B1530275
  · exact B1530279
  · exact B1530283
  · exact B1530287
  · exact B1530291
  · exact B1530295
  · exact B1530299
  · exact B1530303
  · exact B1530307
  · exact B1530311
  · exact B1530315
  · exact B1530319
  · exact B1530323
  · exact B1530327
  · exact B1530331
  · exact B1530335
  · exact B1530339
  · exact B1530343
  · exact B1530347
  · exact B1530351
  · exact B1530355
  · exact B1530359
  · exact B1530363
  · exact B1530367
  · exact B1530371
  · exact B1530375
  · exact B1530379
  · exact B1530383
  · exact B1530387
  · exact B1530391
  · exact B1530395
  · exact B1530399
  · exact B1530403
  · exact B1530407
  · exact B1530411
  · exact B1530415
  · exact B1530419
  · exact B1530423
  · exact B1530427
  · exact B1530431
  · exact B1530435
  · exact B1530439
  · exact B1530443
  · exact B1530447
  · exact B1530451
  · exact B1530455
  · exact B1530459

theorem solution (m : ℕ) (hlo : 1528461 ≤ m) (hhi : m ≤ 1530461) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 382115 ≤ j := by omega
    have hj2 : j ≤ 382614 := by omega
    have hb : Blo 1528461 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
