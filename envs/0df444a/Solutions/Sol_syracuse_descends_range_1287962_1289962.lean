-- Prove2me | solution 1 for syracuse_descends_range_1287962_1289962
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T22:12:22.033013+00:00
-- url     : https://prove2.me/submissions/8eb4c40a-baa4-487f-b125-b8d45538948a

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


theorem B1449985 : Blo 1287962 1449985 := bbase (se 2 (by rfl) ⟨543744, by rfl⟩ : syracuseStep 1449985 = 1087489) (by norm_num)
theorem B1933325 : Blo 1287962 1933325 := bbase (se 3 (by rfl) ⟨362498, by rfl⟩ : syracuseStep 1933325 = 724997) (by norm_num)
theorem B15687701 : Blo 1287962 15687701 := bbase (se 6 (by rfl) ⟨367680, by rfl⟩ : syracuseStep 15687701 = 735361) (by norm_num)
theorem B2981909 : Blo 1287962 2981909 := bbase (se 6 (by rfl) ⟨69888, by rfl⟩ : syracuseStep 2981909 = 139777) (by norm_num)
theorem B1376281 : Blo 1287962 1376281 := bbase (se 2 (by rfl) ⟨516105, by rfl⟩ : syracuseStep 1376281 = 1032211) (by norm_num)
theorem B3096605 : Blo 1287962 3096605 := bbase (se 3 (by rfl) ⟨580613, by rfl⟩ : syracuseStep 3096605 = 1161227) (by norm_num)
theorem B2899997 : Blo 1287962 2899997 := bbase (se 3 (by rfl) ⟨543749, by rfl⟩ : syracuseStep 2899997 = 1087499) (by norm_num)
theorem B1933349 : Blo 1287962 1933349 := bbase (se 4 (by rfl) ⟨181251, by rfl⟩ : syracuseStep 1933349 = 362503) (by norm_num)
theorem B1450021 : Blo 1287962 1450021 := bbase (se 4 (by rfl) ⟨135939, by rfl⟩ : syracuseStep 1450021 = 271879) (by norm_num)
theorem B1933373 : Blo 1287962 1933373 := bbase (se 3 (by rfl) ⟨362507, by rfl⟩ : syracuseStep 1933373 = 725015) (by norm_num)
theorem B1450057 : Blo 1287962 1450057 := bbase (se 2 (by rfl) ⟨543771, by rfl⟩ : syracuseStep 1450057 = 1087543) (by norm_num)
theorem B1933397 : Blo 1287962 1933397 := bbase (se 8 (by rfl) ⟨11328, by rfl⟩ : syracuseStep 1933397 = 22657) (by norm_num)
theorem B1630297 : Blo 1287962 1630297 := bbase (se 2 (by rfl) ⟨611361, by rfl⟩ : syracuseStep 1630297 = 1222723) (by norm_num)
theorem B4890725 : Blo 1287962 4890725 := bbase (se 4 (by rfl) ⟨458505, by rfl⟩ : syracuseStep 4890725 = 917011) (by norm_num)
theorem B4128869 : Blo 1287962 4128869 := bbase (se 4 (by rfl) ⟨387081, by rfl⟩ : syracuseStep 4128869 = 774163) (by norm_num)
theorem B2900069 : Blo 1287962 2900069 := bbase (se 4 (by rfl) ⟨271881, by rfl⟩ : syracuseStep 2900069 = 543763) (by norm_num)
theorem B2515045 : Blo 1287962 2515045 := bbase (se 4 (by rfl) ⟨235785, by rfl⟩ : syracuseStep 2515045 = 471571) (by norm_num)
theorem B2203757 : Blo 1287962 2203757 := bbase (se 3 (by rfl) ⟨413204, by rfl⟩ : syracuseStep 2203757 = 826409) (by norm_num)
theorem B1933421 : Blo 1287962 1933421 := bbase (se 3 (by rfl) ⟨362516, by rfl⟩ : syracuseStep 1933421 = 725033) (by norm_num)
theorem B1450093 : Blo 1287962 1450093 := bbase (se 3 (by rfl) ⟨271892, by rfl⟩ : syracuseStep 1450093 = 543785) (by norm_num)
theorem B6963317 : Blo 1287962 6963317 := bbase (se 5 (by rfl) ⟨326405, by rfl⟩ : syracuseStep 6963317 = 652811) (by norm_num)
theorem B3260533 : Blo 1287962 3260533 := bbase (se 5 (by rfl) ⟨152837, by rfl⟩ : syracuseStep 3260533 = 305675) (by norm_num)
theorem B1933445 : Blo 1287962 1933445 := bbase (se 4 (by rfl) ⟨181260, by rfl⟩ : syracuseStep 1933445 = 362521) (by norm_num)
theorem B1450129 : Blo 1287962 1450129 := bbase (se 2 (by rfl) ⟨543798, by rfl⟩ : syracuseStep 1450129 = 1087597) (by norm_num)
theorem B1933469 : Blo 1287962 1933469 := bbase (se 3 (by rfl) ⟨362525, by rfl⟩ : syracuseStep 1933469 = 725051) (by norm_num)
theorem B2900141 : Blo 1287962 2900141 := bbase (se 3 (by rfl) ⟨543776, by rfl⟩ : syracuseStep 2900141 = 1087553) (by norm_num)
theorem B1933493 : Blo 1287962 1933493 := bbase (se 5 (by rfl) ⟨90632, by rfl⟩ : syracuseStep 1933493 = 181265) (by norm_num)
theorem B1450165 : Blo 1287962 1450165 := bbase (se 5 (by rfl) ⟨67976, by rfl⟩ : syracuseStep 1450165 = 135953) (by norm_num)
theorem B1933517 : Blo 1287962 1933517 := bbase (se 3 (by rfl) ⟨362534, by rfl⟩ : syracuseStep 1933517 = 725069) (by norm_num)
theorem B17629397 : Blo 1287962 17629397 := bbase (se 7 (by rfl) ⟨206594, by rfl⟩ : syracuseStep 17629397 = 413189) (by norm_num)
theorem B1450201 : Blo 1287962 1450201 := bbase (se 2 (by rfl) ⟨543825, by rfl⟩ : syracuseStep 1450201 = 1087651) (by norm_num)
theorem B3260645 : Blo 1287962 3260645 := bbase (se 4 (by rfl) ⟨305685, by rfl⟩ : syracuseStep 3260645 = 611371) (by norm_num)
theorem B1933541 : Blo 1287962 1933541 := bbase (se 4 (by rfl) ⟨181269, by rfl⟩ : syracuseStep 1933541 = 362539) (by norm_num)
theorem B2900213 : Blo 1287962 2900213 := bbase (se 5 (by rfl) ⟨135947, by rfl⟩ : syracuseStep 2900213 = 271895) (by norm_num)
theorem B1933565 : Blo 1287962 1933565 := bbase (se 3 (by rfl) ⟨362543, by rfl⟩ : syracuseStep 1933565 = 725087) (by norm_num)
theorem B1450237 : Blo 1287962 1450237 := bbase (se 3 (by rfl) ⟨271919, by rfl⟩ : syracuseStep 1450237 = 543839) (by norm_num)
theorem B1630469 : Blo 1287962 1630469 := bbase (se 4 (by rfl) ⟨152856, by rfl⟩ : syracuseStep 1630469 = 305713) (by norm_num)
theorem B1933589 : Blo 1287962 1933589 := bbase (se 6 (by rfl) ⟨45318, by rfl⟩ : syracuseStep 1933589 = 90637) (by norm_num)
theorem B1450273 : Blo 1287962 1450273 := bbase (se 2 (by rfl) ⟨543852, by rfl⟩ : syracuseStep 1450273 = 1087705) (by norm_num)
theorem B4964645 : Blo 1287962 4964645 := bbase (se 4 (by rfl) ⟨465435, by rfl⟩ : syracuseStep 4964645 = 930871) (by norm_num)
theorem B1933613 : Blo 1287962 1933613 := bbase (se 3 (by rfl) ⟨362552, by rfl⟩ : syracuseStep 1933613 = 725105) (by norm_num)
theorem B1630525 : Blo 1287962 1630525 := bbase (se 3 (by rfl) ⟨305723, by rfl⟩ : syracuseStep 1630525 = 611447) (by norm_num)
theorem B2900285 : Blo 1287962 2900285 := bbase (se 3 (by rfl) ⟨543803, by rfl⟩ : syracuseStep 2900285 = 1087607) (by norm_num)
theorem B1933637 : Blo 1287962 1933637 := bbase (se 4 (by rfl) ⟨181278, by rfl⟩ : syracuseStep 1933637 = 362557) (by norm_num)
theorem B1450309 : Blo 1287962 1450309 := bbase (se 4 (by rfl) ⟨135966, by rfl⟩ : syracuseStep 1450309 = 271933) (by norm_num)
theorem B9290069 : Blo 1287962 9290069 := bbase (se 10 (by rfl) ⟨13608, by rfl⟩ : syracuseStep 9290069 = 27217) (by norm_num)
theorem B4350293 : Blo 1287962 4350293 := bbase (se 10 (by rfl) ⟨6372, by rfl⟩ : syracuseStep 4350293 = 12745) (by norm_num)
theorem B1933661 : Blo 1287962 1933661 := bbase (se 3 (by rfl) ⟨362561, by rfl⟩ : syracuseStep 1933661 = 725123) (by norm_num)
theorem B1450345 : Blo 1287962 1450345 := bbase (se 2 (by rfl) ⟨543879, by rfl⟩ : syracuseStep 1450345 = 1087759) (by norm_num)
theorem B1933685 : Blo 1287962 1933685 := bbase (se 5 (by rfl) ⟨90641, by rfl⟩ : syracuseStep 1933685 = 181283) (by norm_num)
theorem B5226869 : Blo 1287962 5226869 := bbase (se 5 (by rfl) ⟨245009, by rfl⟩ : syracuseStep 5226869 = 490019) (by norm_num)
theorem B1835389 : Blo 1287962 1835389 := bbase (se 3 (by rfl) ⟨344135, by rfl⟩ : syracuseStep 1835389 = 688271) (by norm_num)
theorem B4891013 : Blo 1287962 4891013 := bbase (se 4 (by rfl) ⟨458532, by rfl⟩ : syracuseStep 4891013 = 917065) (by norm_num)
theorem B2900357 : Blo 1287962 2900357 := bbase (se 4 (by rfl) ⟨271908, by rfl⟩ : syracuseStep 2900357 = 543817) (by norm_num)
theorem B2064781 : Blo 1287962 2064781 := bbase (se 3 (by rfl) ⟨387146, by rfl⟩ : syracuseStep 2064781 = 774293) (by norm_num)
theorem B1933709 : Blo 1287962 1933709 := bbase (se 3 (by rfl) ⟨362570, by rfl⟩ : syracuseStep 1933709 = 725141) (by norm_num)
theorem B1450381 : Blo 1287962 1450381 := bbase (se 3 (by rfl) ⟨271946, by rfl⟩ : syracuseStep 1450381 = 543893) (by norm_num)
theorem B1630621 : Blo 1287962 1630621 := bbase (se 3 (by rfl) ⟨305741, by rfl⟩ : syracuseStep 1630621 = 611483) (by norm_num)
theorem B3260837 : Blo 1287962 3260837 := bbase (se 4 (by rfl) ⟨305703, by rfl⟩ : syracuseStep 3260837 = 611407) (by norm_num)
theorem B3096997 : Blo 1287962 3096997 := bbase (se 4 (by rfl) ⟨290343, by rfl⟩ : syracuseStep 3096997 = 580687) (by norm_num)
theorem B1933733 : Blo 1287962 1933733 := bbase (se 4 (by rfl) ⟨181287, by rfl⟩ : syracuseStep 1933733 = 362575) (by norm_num)
theorem B1450417 : Blo 1287962 1450417 := bbase (se 2 (by rfl) ⟨543906, by rfl⟩ : syracuseStep 1450417 = 1087813) (by norm_num)
theorem B1933757 : Blo 1287962 1933757 := bbase (se 3 (by rfl) ⟨362579, by rfl⟩ : syracuseStep 1933757 = 725159) (by norm_num)
theorem B2941373 : Blo 1287962 2941373 := bbase (se 3 (by rfl) ⟨551507, by rfl⟩ : syracuseStep 2941373 = 1103015) (by norm_num)
theorem B1376713 : Blo 1287962 1376713 := bbase (se 2 (by rfl) ⟨516267, by rfl⟩ : syracuseStep 1376713 = 1032535) (by norm_num)
theorem B2064845 : Blo 1287962 2064845 := bbase (se 3 (by rfl) ⟨387158, by rfl⟩ : syracuseStep 2064845 = 774317) (by norm_num)
theorem B2900429 : Blo 1287962 2900429 := bbase (se 3 (by rfl) ⟨543830, by rfl⟩ : syracuseStep 2900429 = 1087661) (by norm_num)
theorem B1933781 : Blo 1287962 1933781 := bbase (se 7 (by rfl) ⟨22661, by rfl⟩ : syracuseStep 1933781 = 45323) (by norm_num)
theorem B1450453 : Blo 1287962 1450453 := bbase (se 7 (by rfl) ⟨16997, by rfl⟩ : syracuseStep 1450453 = 33995) (by norm_num)
theorem B1933805 : Blo 1287962 1933805 := bbase (se 3 (by rfl) ⟨362588, by rfl⟩ : syracuseStep 1933805 = 725177) (by norm_num)
theorem B1450489 : Blo 1287962 1450489 := bbase (se 2 (by rfl) ⟨543933, by rfl⟩ : syracuseStep 1450489 = 1087867) (by norm_num)
theorem B1933829 : Blo 1287962 1933829 := bbase (se 4 (by rfl) ⟨181296, by rfl⟩ : syracuseStep 1933829 = 362593) (by norm_num)
theorem B1376785 : Blo 1287962 1376785 := bbase (se 2 (by rfl) ⟨516294, by rfl⟩ : syracuseStep 1376785 = 1032589) (by norm_num)
theorem B2900501 : Blo 1287962 2900501 := bbase (se 6 (by rfl) ⟨67980, by rfl⟩ : syracuseStep 2900501 = 135961) (by norm_num)
theorem B1933853 : Blo 1287962 1933853 := bbase (se 3 (by rfl) ⟨362597, by rfl⟩ : syracuseStep 1933853 = 725195) (by norm_num)
theorem B1450525 : Blo 1287962 1450525 := bbase (se 3 (by rfl) ⟨271973, by rfl⟩ : syracuseStep 1450525 = 543947) (by norm_num)
theorem B1933877 : Blo 1287962 1933877 := bbase (se 5 (by rfl) ⟨90650, by rfl⟩ : syracuseStep 1933877 = 181301) (by norm_num)
theorem B1450561 : Blo 1287962 1450561 := bbase (se 2 (by rfl) ⟨543960, by rfl⟩ : syracuseStep 1450561 = 1087921) (by norm_num)
theorem B1630793 : Blo 1287962 1630793 := bbase (se 2 (by rfl) ⟨611547, by rfl⟩ : syracuseStep 1630793 = 1223095) (by norm_num)
theorem B1933901 : Blo 1287962 1933901 := bbase (se 3 (by rfl) ⟨362606, by rfl⟩ : syracuseStep 1933901 = 725213) (by norm_num)
theorem B2900573 : Blo 1287962 2900573 := bbase (se 3 (by rfl) ⟨543857, by rfl⟩ : syracuseStep 2900573 = 1087715) (by norm_num)
theorem B1933925 : Blo 1287962 1933925 := bbase (se 4 (by rfl) ⟨181305, by rfl⟩ : syracuseStep 1933925 = 362611) (by norm_num)
theorem B1450597 : Blo 1287962 1450597 := bbase (se 4 (by rfl) ⟨135993, by rfl⟩ : syracuseStep 1450597 = 271987) (by norm_num)
theorem B1933949 : Blo 1287962 1933949 := bbase (se 3 (by rfl) ⟨362615, by rfl⟩ : syracuseStep 1933949 = 725231) (by norm_num)
theorem B1630849 : Blo 1287962 1630849 := bbase (se 2 (by rfl) ⟨611568, by rfl⟩ : syracuseStep 1630849 = 1223137) (by norm_num)
theorem B1450633 : Blo 1287962 1450633 := bbase (se 2 (by rfl) ⟨543987, by rfl⟩ : syracuseStep 1450633 = 1087975) (by norm_num)
theorem B1548941 : Blo 1287962 1548941 := bbase (se 3 (by rfl) ⟨290426, by rfl⟩ : syracuseStep 1548941 = 580853) (by norm_num)
theorem B1933973 : Blo 1287962 1933973 := bbase (se 6 (by rfl) ⟨45327, by rfl⟩ : syracuseStep 1933973 = 90655) (by norm_num)
theorem B2900645 : Blo 1287962 2900645 := bbase (se 4 (by rfl) ⟨271935, by rfl⟩ : syracuseStep 2900645 = 543871) (by norm_num)
theorem B1933997 : Blo 1287962 1933997 := bbase (se 3 (by rfl) ⟨362624, by rfl⟩ : syracuseStep 1933997 = 725249) (by norm_num)
theorem B1450669 : Blo 1287962 1450669 := bbase (se 3 (by rfl) ⟨272000, by rfl⟩ : syracuseStep 1450669 = 544001) (by norm_num)
theorem B1934021 : Blo 1287962 1934021 := bbase (se 4 (by rfl) ⟨181314, by rfl⟩ : syracuseStep 1934021 = 362629) (by norm_num)
theorem B6529733 : Blo 1287962 6529733 := bbase (se 4 (by rfl) ⟨612162, by rfl⟩ : syracuseStep 6529733 = 1224325) (by norm_num)
theorem B1835725 : Blo 1287962 1835725 := bbase (se 3 (by rfl) ⟨344198, by rfl⟩ : syracuseStep 1835725 = 688397) (by norm_num)
theorem B1450705 : Blo 1287962 1450705 := bbase (se 2 (by rfl) ⟨544014, by rfl⟩ : syracuseStep 1450705 = 1088029) (by norm_num)
theorem B1934045 : Blo 1287962 1934045 := bbase (se 3 (by rfl) ⟨362633, by rfl⟩ : syracuseStep 1934045 = 725267) (by norm_num)
theorem B1630945 : Blo 1287962 1630945 := bbase (se 2 (by rfl) ⟨611604, by rfl⟩ : syracuseStep 1630945 = 1223209) (by norm_num)
theorem B2900717 : Blo 1287962 2900717 := bbase (se 3 (by rfl) ⟨543884, by rfl⟩ : syracuseStep 2900717 = 1087769) (by norm_num)
theorem B1549037 : Blo 1287962 1549037 := bbase (se 3 (by rfl) ⟨290444, by rfl⟩ : syracuseStep 1549037 = 580889) (by norm_num)
theorem B1934069 : Blo 1287962 1934069 := bbase (se 5 (by rfl) ⟨90659, by rfl⟩ : syracuseStep 1934069 = 181319) (by norm_num)
theorem B1450741 : Blo 1287962 1450741 := bbase (se 5 (by rfl) ⟨68003, by rfl⟩ : syracuseStep 1450741 = 136007) (by norm_num)
theorem B3261181 : Blo 1287962 3261181 := bbase (se 3 (by rfl) ⟨611471, by rfl⟩ : syracuseStep 3261181 = 1222943) (by norm_num)
theorem B1549057 : Blo 1287962 1549057 := bbase (se 2 (by rfl) ⟨580896, by rfl⟩ : syracuseStep 1549057 = 1161793) (by norm_num)
theorem B4350725 : Blo 1287962 4350725 := bbase (se 4 (by rfl) ⟨407880, by rfl⟩ : syracuseStep 4350725 = 815761) (by norm_num)
theorem B1934093 : Blo 1287962 1934093 := bbase (se 3 (by rfl) ⟨362642, by rfl⟩ : syracuseStep 1934093 = 725285) (by norm_num)
theorem B1450777 : Blo 1287962 1450777 := bbase (se 2 (by rfl) ⟨544041, by rfl⟩ : syracuseStep 1450777 = 1088083) (by norm_num)
theorem B1934117 : Blo 1287962 1934117 := bbase (se 4 (by rfl) ⟨181323, by rfl⟩ : syracuseStep 1934117 = 362647) (by norm_num)
theorem B2900789 : Blo 1287962 2900789 := bbase (se 5 (by rfl) ⟨135974, by rfl⟩ : syracuseStep 2900789 = 271949) (by norm_num)
theorem B1934141 : Blo 1287962 1934141 := bbase (se 3 (by rfl) ⟨362651, by rfl⟩ : syracuseStep 1934141 = 725303) (by norm_num)
theorem B1450813 : Blo 1287962 1450813 := bbase (se 3 (by rfl) ⟨272027, by rfl⟩ : syracuseStep 1450813 = 544055) (by norm_num)
theorem B2753365 : Blo 1287962 2753365 := bbase (se 9 (by rfl) ⟨8066, by rfl⟩ : syracuseStep 2753365 = 16133) (by norm_num)
theorem B1934165 : Blo 1287962 1934165 := bbase (se 9 (by rfl) ⟨5666, by rfl⟩ : syracuseStep 1934165 = 11333) (by norm_num)
theorem B1450849 : Blo 1287962 1450849 := bbase (se 2 (by rfl) ⟨544068, by rfl⟩ : syracuseStep 1450849 = 1088137) (by norm_num)
theorem B3261293 : Blo 1287962 3261293 := bbase (se 3 (by rfl) ⟨611492, by rfl⟩ : syracuseStep 3261293 = 1222985) (by norm_num)
theorem B1934189 : Blo 1287962 1934189 := bbase (se 3 (by rfl) ⟨362660, by rfl⟩ : syracuseStep 1934189 = 725321) (by norm_num)
theorem B2900861 : Blo 1287962 2900861 := bbase (se 3 (by rfl) ⟨543911, by rfl⟩ : syracuseStep 2900861 = 1087823) (by norm_num)
theorem B1934213 : Blo 1287962 1934213 := bbase (se 4 (by rfl) ⟨181332, by rfl⟩ : syracuseStep 1934213 = 362665) (by norm_num)
theorem B1377157 : Blo 1287962 1377157 := bbase (se 4 (by rfl) ⟨129108, by rfl⟩ : syracuseStep 1377157 = 258217) (by norm_num)
theorem B1450885 : Blo 1287962 1450885 := bbase (se 4 (by rfl) ⟨136020, by rfl⟩ : syracuseStep 1450885 = 272041) (by norm_num)
theorem B1631117 : Blo 1287962 1631117 := bbase (se 3 (by rfl) ⟨305834, by rfl⟩ : syracuseStep 1631117 = 611669) (by norm_num)
theorem B1549201 : Blo 1287962 1549201 := bbase (se 2 (by rfl) ⟨580950, by rfl⟩ : syracuseStep 1549201 = 1161901) (by norm_num)
theorem B1934237 : Blo 1287962 1934237 := bbase (se 3 (by rfl) ⟨362669, by rfl⟩ : syracuseStep 1934237 = 725339) (by norm_num)
theorem B1835941 : Blo 1287962 1835941 := bbase (se 4 (by rfl) ⟨172119, by rfl⟩ : syracuseStep 1835941 = 344239) (by norm_num)
theorem B1450921 : Blo 1287962 1450921 := bbase (se 2 (by rfl) ⟨544095, by rfl⟩ : syracuseStep 1450921 = 1088191) (by norm_num)
theorem B1934261 : Blo 1287962 1934261 := bbase (se 5 (by rfl) ⟨90668, by rfl⟩ : syracuseStep 1934261 = 181337) (by norm_num)
theorem B1631173 : Blo 1287962 1631173 := bbase (se 4 (by rfl) ⟨152922, by rfl⟩ : syracuseStep 1631173 = 305845) (by norm_num)
theorem B2900933 : Blo 1287962 2900933 := bbase (se 4 (by rfl) ⟨271962, by rfl⟩ : syracuseStep 2900933 = 543925) (by norm_num)
theorem B1934285 : Blo 1287962 1934285 := bbase (se 3 (by rfl) ⟨362678, by rfl⟩ : syracuseStep 1934285 = 725357) (by norm_num)
theorem B1450957 : Blo 1287962 1450957 := bbase (se 3 (by rfl) ⟨272054, by rfl⟩ : syracuseStep 1450957 = 544109) (by norm_num)
theorem B1934309 : Blo 1287962 1934309 := bbase (se 4 (by rfl) ⟨181341, by rfl⟩ : syracuseStep 1934309 = 362683) (by norm_num)
theorem B1450993 : Blo 1287962 1450993 := bbase (se 2 (by rfl) ⟨544122, by rfl⟩ : syracuseStep 1450993 = 1088245) (by norm_num)
theorem B1934333 : Blo 1287962 1934333 := bbase (se 3 (by rfl) ⟨362687, by rfl⟩ : syracuseStep 1934333 = 725375) (by norm_num)
theorem B2901005 : Blo 1287962 2901005 := bbase (se 3 (by rfl) ⟨543938, by rfl⟩ : syracuseStep 2901005 = 1087877) (by norm_num)
theorem B1934357 : Blo 1287962 1934357 := bbase (se 6 (by rfl) ⟨45336, by rfl⟩ : syracuseStep 1934357 = 90673) (by norm_num)
theorem B1451029 : Blo 1287962 1451029 := bbase (se 6 (by rfl) ⟨34008, by rfl⟩ : syracuseStep 1451029 = 68017) (by norm_num)
theorem B1631269 : Blo 1287962 1631269 := bbase (se 4 (by rfl) ⟨152931, by rfl⟩ : syracuseStep 1631269 = 305863) (by norm_num)
theorem B3261485 : Blo 1287962 3261485 := bbase (se 3 (by rfl) ⟨611528, by rfl⟩ : syracuseStep 3261485 = 1223057) (by norm_num)
theorem B1934381 : Blo 1287962 1934381 := bbase (se 3 (by rfl) ⟨362696, by rfl⟩ : syracuseStep 1934381 = 725393) (by norm_num)
theorem B1451065 : Blo 1287962 1451065 := bbase (se 2 (by rfl) ⟨544149, by rfl⟩ : syracuseStep 1451065 = 1088299) (by norm_num)
theorem B1934405 : Blo 1287962 1934405 := bbase (se 4 (by rfl) ⟨181350, by rfl⟩ : syracuseStep 1934405 = 362701) (by norm_num)
theorem B2901077 : Blo 1287962 2901077 := bbase (se 8 (by rfl) ⟨16998, by rfl⟩ : syracuseStep 2901077 = 33997) (by norm_num)
theorem B1934429 : Blo 1287962 1934429 := bbase (se 3 (by rfl) ⟨362705, by rfl⟩ : syracuseStep 1934429 = 725411) (by norm_num)
theorem B1451101 : Blo 1287962 1451101 := bbase (se 3 (by rfl) ⟨272081, by rfl⟩ : syracuseStep 1451101 = 544163) (by norm_num)
theorem B6521957 : Blo 1287962 6521957 := bbase (se 4 (by rfl) ⟨611433, by rfl⟩ : syracuseStep 6521957 = 1222867) (by norm_num)
theorem B1934453 : Blo 1287962 1934453 := bbase (se 5 (by rfl) ⟨90677, by rfl⟩ : syracuseStep 1934453 = 181355) (by norm_num)
theorem B1451137 : Blo 1287962 1451137 := bbase (se 2 (by rfl) ⟨544176, by rfl⟩ : syracuseStep 1451137 = 1088353) (by norm_num)
theorem B1934477 : Blo 1287962 1934477 := bbase (se 3 (by rfl) ⟨362714, by rfl⟩ : syracuseStep 1934477 = 725429) (by norm_num)
theorem B2901149 : Blo 1287962 2901149 := bbase (se 3 (by rfl) ⟨543965, by rfl⟩ : syracuseStep 2901149 = 1087931) (by norm_num)
theorem B1934501 : Blo 1287962 1934501 := bbase (se 4 (by rfl) ⟨181359, by rfl⟩ : syracuseStep 1934501 = 362719) (by norm_num)
theorem B1451173 : Blo 1287962 1451173 := bbase (se 4 (by rfl) ⟨136047, by rfl⟩ : syracuseStep 1451173 = 272095) (by norm_num)
theorem B4351157 : Blo 1287962 4351157 := bbase (se 5 (by rfl) ⟨203960, by rfl⟩ : syracuseStep 4351157 = 407921) (by norm_num)
theorem B1934525 : Blo 1287962 1934525 := bbase (se 3 (by rfl) ⟨362723, by rfl⟩ : syracuseStep 1934525 = 725447) (by norm_num)
theorem B1631441 : Blo 1287962 1631441 := bbase (se 2 (by rfl) ⟨611790, by rfl⟩ : syracuseStep 1631441 = 1223581) (by norm_num)
theorem B1934549 : Blo 1287962 1934549 := bbase (se 7 (by rfl) ⟨22670, by rfl⟩ : syracuseStep 1934549 = 45341) (by norm_num)
theorem B2901221 : Blo 1287962 2901221 := bbase (se 4 (by rfl) ⟨271989, by rfl⟩ : syracuseStep 2901221 = 543979) (by norm_num)
theorem B1934573 : Blo 1287962 1934573 := bbase (se 3 (by rfl) ⟨362732, by rfl⟩ : syracuseStep 1934573 = 725465) (by norm_num)
theorem B1934597 : Blo 1287962 1934597 := bbase (se 4 (by rfl) ⟨181368, by rfl⟩ : syracuseStep 1934597 = 362737) (by norm_num)
theorem B1631497 : Blo 1287962 1631497 := bbase (se 2 (by rfl) ⟨611811, by rfl⟩ : syracuseStep 1631497 = 1223623) (by norm_num)
theorem B1836317 : Blo 1287962 1836317 := bbase (se 3 (by rfl) ⟨344309, by rfl⟩ : syracuseStep 1836317 = 688619) (by norm_num)
theorem B1934621 : Blo 1287962 1934621 := bbase (se 3 (by rfl) ⟨362741, by rfl⟩ : syracuseStep 1934621 = 725483) (by norm_num)
theorem B2901293 : Blo 1287962 2901293 := bbase (se 3 (by rfl) ⟨543992, by rfl⟩ : syracuseStep 2901293 = 1087985) (by norm_num)
theorem B1934645 : Blo 1287962 1934645 := bbase (se 5 (by rfl) ⟨90686, by rfl⟩ : syracuseStep 1934645 = 181373) (by norm_num)
theorem B1934669 : Blo 1287962 1934669 := bbase (se 3 (by rfl) ⟨362750, by rfl⟩ : syracuseStep 1934669 = 725501) (by norm_num)
theorem B3671381 : Blo 1287962 3671381 := bbase (se 12 (by rfl) ⟨1344, by rfl⟩ : syracuseStep 3671381 = 2689) (by norm_num)
theorem B1934693 : Blo 1287962 1934693 := bbase (se 4 (by rfl) ⟨181377, by rfl⟩ : syracuseStep 1934693 = 362755) (by norm_num)
theorem B1631593 : Blo 1287962 1631593 := bbase (se 2 (by rfl) ⟨611847, by rfl⟩ : syracuseStep 1631593 = 1223695) (by norm_num)
theorem B2901365 : Blo 1287962 2901365 := bbase (se 5 (by rfl) ⟨136001, by rfl⟩ : syracuseStep 2901365 = 272003) (by norm_num)
theorem B1934717 : Blo 1287962 1934717 := bbase (se 3 (by rfl) ⟨362759, by rfl⟩ : syracuseStep 1934717 = 725519) (by norm_num)
theorem B3261829 : Blo 1287962 3261829 := bbase (se 4 (by rfl) ⟨305796, by rfl⟩ : syracuseStep 3261829 = 611593) (by norm_num)
theorem B1934741 : Blo 1287962 1934741 := bbase (se 6 (by rfl) ⟨45345, by rfl⟩ : syracuseStep 1934741 = 90691) (by norm_num)
theorem B1934765 : Blo 1287962 1934765 := bbase (se 3 (by rfl) ⟨362768, by rfl⟩ : syracuseStep 1934765 = 725537) (by norm_num)
theorem B2901437 : Blo 1287962 2901437 := bbase (se 3 (by rfl) ⟨544019, by rfl⟩ : syracuseStep 2901437 = 1088039) (by norm_num)
theorem B1934789 : Blo 1287962 1934789 := bbase (se 4 (by rfl) ⟨181386, by rfl⟩ : syracuseStep 1934789 = 362773) (by norm_num)
theorem B35743189 : Blo 1287962 35743189 := bbase (se 7 (by rfl) ⟨418865, by rfl⟩ : syracuseStep 35743189 = 837731) (by norm_num)
theorem B1934813 : Blo 1287962 1934813 := bbase (se 3 (by rfl) ⟨362777, by rfl⟩ : syracuseStep 1934813 = 725555) (by norm_num)
theorem B3261941 : Blo 1287962 3261941 := bbase (se 5 (by rfl) ⟨152903, by rfl⟩ : syracuseStep 3261941 = 305807) (by norm_num)
theorem B3974645 : Blo 1287962 3974645 := bbase (se 5 (by rfl) ⟨186311, by rfl⟩ : syracuseStep 3974645 = 372623) (by norm_num)
theorem B1934837 : Blo 1287962 1934837 := bbase (se 5 (by rfl) ⟨90695, by rfl⟩ : syracuseStep 1934837 = 181391) (by norm_num)
theorem B2901509 : Blo 1287962 2901509 := bbase (se 4 (by rfl) ⟨272016, by rfl⟩ : syracuseStep 2901509 = 544033) (by norm_num)
theorem B1934861 : Blo 1287962 1934861 := bbase (se 3 (by rfl) ⟨362786, by rfl⟩ : syracuseStep 1934861 = 725573) (by norm_num)
theorem B1631765 : Blo 1287962 1631765 := bbase (se 6 (by rfl) ⟨38244, by rfl⟩ : syracuseStep 1631765 = 76489) (by norm_num)
theorem B4892197 : Blo 1287962 4892197 := bbase (se 4 (by rfl) ⟨458643, by rfl⟩ : syracuseStep 4892197 = 917287) (by norm_num)
theorem B1934885 : Blo 1287962 1934885 := bbase (se 4 (by rfl) ⟨181395, by rfl⟩ : syracuseStep 1934885 = 362791) (by norm_num)
theorem B1934909 : Blo 1287962 1934909 := bbase (se 3 (by rfl) ⟨362795, by rfl⟩ : syracuseStep 1934909 = 725591) (by norm_num)
theorem B1631821 : Blo 1287962 1631821 := bbase (se 3 (by rfl) ⟨305966, by rfl⟩ : syracuseStep 1631821 = 611933) (by norm_num)
theorem B2901581 : Blo 1287962 2901581 := bbase (se 3 (by rfl) ⟨544046, by rfl⟩ : syracuseStep 2901581 = 1088093) (by norm_num)
theorem B1934933 : Blo 1287962 1934933 := bbase (se 8 (by rfl) ⟨11337, by rfl⟩ : syracuseStep 1934933 = 22675) (by norm_num)
theorem B4351589 : Blo 1287962 4351589 := bbase (se 4 (by rfl) ⟨407961, by rfl⟩ : syracuseStep 4351589 = 815923) (by norm_num)
theorem B5228165 : Blo 1287962 5228165 := bbase (se 4 (by rfl) ⟨490140, by rfl⟩ : syracuseStep 5228165 = 980281) (by norm_num)
theorem B2901653 : Blo 1287962 2901653 := bbase (se 6 (by rfl) ⟨68007, by rfl⟩ : syracuseStep 2901653 = 136015) (by norm_num)
theorem B1631917 : Blo 1287962 1631917 := bbase (se 3 (by rfl) ⟨305984, by rfl⟩ : syracuseStep 1631917 = 611969) (by norm_num)
theorem B3262133 : Blo 1287962 3262133 := bbase (se 5 (by rfl) ⟨152912, by rfl⟩ : syracuseStep 3262133 = 305825) (by norm_num)
theorem B2754253 : Blo 1287962 2754253 := bbase (se 3 (by rfl) ⟨516422, by rfl⟩ : syracuseStep 2754253 = 1032845) (by norm_num)
theorem B2901725 : Blo 1287962 2901725 := bbase (se 3 (by rfl) ⟨544073, by rfl⟩ : syracuseStep 2901725 = 1088147) (by norm_num)
theorem B6194917 : Blo 1287962 6194917 := bbase (se 4 (by rfl) ⟨580773, by rfl⟩ : syracuseStep 6194917 = 1161547) (by norm_num)
theorem B2066165 : Blo 1287962 2066165 := bbase (se 5 (by rfl) ⟨96851, by rfl⟩ : syracuseStep 2066165 = 193703) (by norm_num)
theorem B2901797 : Blo 1287962 2901797 := bbase (se 4 (by rfl) ⟨272043, by rfl⟩ : syracuseStep 2901797 = 544087) (by norm_num)
theorem B4892501 : Blo 1287962 4892501 := bbase (se 9 (by rfl) ⟨14333, by rfl⟩ : syracuseStep 4892501 = 28667) (by norm_num)
theorem B1632089 : Blo 1287962 1632089 := bbase (se 2 (by rfl) ⟨612033, by rfl⟩ : syracuseStep 1632089 = 1224067) (by norm_num)
theorem B2901869 : Blo 1287962 2901869 := bbase (se 3 (by rfl) ⟨544100, by rfl⟩ : syracuseStep 2901869 = 1088201) (by norm_num)
theorem B10594165 : Blo 1287962 10594165 := bbase (se 5 (by rfl) ⟨496601, by rfl⟩ : syracuseStep 10594165 = 993203) (by norm_num)
theorem B7341941 : Blo 1287962 7341941 := bbase (se 5 (by rfl) ⟨344153, by rfl⟩ : syracuseStep 7341941 = 688307) (by norm_num)
theorem B1632145 : Blo 1287962 1632145 := bbase (se 2 (by rfl) ⟨612054, by rfl⟩ : syracuseStep 1632145 = 1224109) (by norm_num)
theorem B2901941 : Blo 1287962 2901941 := bbase (se 5 (by rfl) ⟨136028, by rfl⟩ : syracuseStep 2901941 = 272057) (by norm_num)
theorem B1959869 : Blo 1287962 1959869 := bbase (se 3 (by rfl) ⟨367475, by rfl⟩ : syracuseStep 1959869 = 734951) (by norm_num)
theorem B1632241 : Blo 1287962 1632241 := bbase (se 2 (by rfl) ⟨612090, by rfl⟩ : syracuseStep 1632241 = 1224181) (by norm_num)
theorem B2902013 : Blo 1287962 2902013 := bbase (se 3 (by rfl) ⟨544127, by rfl⟩ : syracuseStep 2902013 = 1088255) (by norm_num)
theorem B1861637 : Blo 1287962 1861637 := bbase (se 4 (by rfl) ⟨174528, by rfl⟩ : syracuseStep 1861637 = 349057) (by norm_num)
theorem B3262477 : Blo 1287962 3262477 := bbase (se 3 (by rfl) ⟨611714, by rfl⟩ : syracuseStep 3262477 = 1223429) (by norm_num)
theorem B4352021 : Blo 1287962 4352021 := bbase (se 6 (by rfl) ⟨102000, by rfl⟩ : syracuseStep 4352021 = 204001) (by norm_num)
theorem B2902085 : Blo 1287962 2902085 := bbase (se 4 (by rfl) ⟨272070, by rfl⟩ : syracuseStep 2902085 = 544141) (by norm_num)
theorem B3262589 : Blo 1287962 3262589 := bbase (se 3 (by rfl) ⟨611735, by rfl⟩ : syracuseStep 3262589 = 1223471) (by norm_num)
theorem B2902157 : Blo 1287962 2902157 := bbase (se 3 (by rfl) ⟨544154, by rfl⟩ : syracuseStep 2902157 = 1088309) (by norm_num)
theorem B1632413 : Blo 1287962 1632413 := bbase (se 3 (by rfl) ⟨306077, by rfl⟩ : syracuseStep 1632413 = 612155) (by norm_num)
theorem B2754749 : Blo 1287962 2754749 := bbase (se 3 (by rfl) ⟨516515, by rfl⟩ : syracuseStep 2754749 = 1033031) (by norm_num)
theorem B1632469 : Blo 1287962 1632469 := bbase (se 7 (by rfl) ⟨19130, by rfl⟩ : syracuseStep 1632469 = 38261) (by norm_num)
theorem B2902229 : Blo 1287962 2902229 := bbase (se 7 (by rfl) ⟨34010, by rfl⟩ : syracuseStep 2902229 = 68021) (by norm_num)
theorem B2902301 : Blo 1287962 2902301 := bbase (se 3 (by rfl) ⟨544181, by rfl⟩ : syracuseStep 2902301 = 1088363) (by norm_num)
theorem B4131125 : Blo 1287962 4131125 := bbase (se 5 (by rfl) ⟨193646, by rfl⟩ : syracuseStep 4131125 = 387293) (by norm_num)
theorem B1632565 : Blo 1287962 1632565 := bbase (se 5 (by rfl) ⟨76526, by rfl⟩ : syracuseStep 1632565 = 153053) (by norm_num)
theorem B3262781 : Blo 1287962 3262781 := bbase (se 3 (by rfl) ⟨611771, by rfl⟩ : syracuseStep 3262781 = 1223543) (by norm_num)
theorem B2902373 : Blo 1287962 2902373 := bbase (se 4 (by rfl) ⟨272097, by rfl⟩ : syracuseStep 2902373 = 544195) (by norm_num)
theorem B6523253 : Blo 1287962 6523253 := bbase (se 5 (by rfl) ⟨305777, by rfl⟩ : syracuseStep 6523253 = 611555) (by norm_num)
theorem B5441941 : Blo 1287962 5441941 := bbase (se 6 (by rfl) ⟨127545, by rfl⟩ : syracuseStep 5441941 = 255091) (by norm_num)
theorem B4352453 : Blo 1287962 4352453 := bbase (se 4 (by rfl) ⟨408042, by rfl⟩ : syracuseStep 4352453 = 816085) (by norm_num)
theorem B9415157 : Blo 1287962 9415157 := bbase (se 5 (by rfl) ⟨441335, by rfl⟩ : syracuseStep 9415157 = 882671) (by norm_num)
theorem B11004437 : Blo 1287962 11004437 := bbase (se 6 (by rfl) ⟨257916, by rfl⟩ : syracuseStep 11004437 = 515833) (by norm_num)
theorem B2173493 : Blo 1287962 2173493 := bbase (se 5 (by rfl) ⟨101882, by rfl⟩ : syracuseStep 2173493 = 203765) (by norm_num)
theorem B1985141 : Blo 1287962 1985141 := bbase (se 5 (by rfl) ⟨93053, by rfl⟩ : syracuseStep 1985141 = 186107) (by norm_num)
theorem B3263125 : Blo 1287962 3263125 := bbase (se 6 (by rfl) ⟨76479, by rfl⟩ : syracuseStep 3263125 = 152959) (by norm_num)
theorem B2173621 : Blo 1287962 2173621 := bbase (se 5 (by rfl) ⟨101888, by rfl⟩ : syracuseStep 2173621 = 203777) (by norm_num)
theorem B4467413 : Blo 1287962 4467413 := bbase (se 7 (by rfl) ⟨52352, by rfl⟩ : syracuseStep 4467413 = 104705) (by norm_num)
theorem B3263237 : Blo 1287962 3263237 := bbase (se 4 (by rfl) ⟨305928, by rfl⟩ : syracuseStep 3263237 = 611857) (by norm_num)
theorem B2173709 : Blo 1287962 2173709 := bbase (se 3 (by rfl) ⟨407570, by rfl⟩ : syracuseStep 2173709 = 815141) (by norm_num)
theorem B1469281 : Blo 1287962 1469281 := bbase (se 2 (by rfl) ⟨550980, by rfl⟩ : syracuseStep 1469281 = 1101961) (by norm_num)
theorem B4352885 : Blo 1287962 4352885 := bbase (se 5 (by rfl) ⟨204041, by rfl⟩ : syracuseStep 4352885 = 408083) (by norm_num)
theorem B3672965 : Blo 1287962 3672965 := bbase (se 4 (by rfl) ⟨344340, by rfl⟩ : syracuseStep 3672965 = 688681) (by norm_num)
theorem B2173837 : Blo 1287962 2173837 := bbase (se 3 (by rfl) ⟨407594, by rfl⟩ : syracuseStep 2173837 = 815189) (by norm_num)
theorem B3263429 : Blo 1287962 3263429 := bbase (se 4 (by rfl) ⟨305946, by rfl⟩ : syracuseStep 3263429 = 611893) (by norm_num)
theorem B2173925 : Blo 1287962 2173925 := bbase (se 4 (by rfl) ⟨203805, by rfl⟩ : syracuseStep 2173925 = 407611) (by norm_num)
theorem B4131893 : Blo 1287962 4131893 := bbase (se 5 (by rfl) ⟨193682, by rfl⟩ : syracuseStep 4131893 = 387365) (by norm_num)
theorem B2174053 : Blo 1287962 2174053 := bbase (se 4 (by rfl) ⟨203817, by rfl⟩ : syracuseStep 2174053 = 407635) (by norm_num)
theorem B2174141 : Blo 1287962 2174141 := bbase (se 3 (by rfl) ⟨407651, by rfl⟩ : syracuseStep 2174141 = 815303) (by norm_num)
theorem B3484901 : Blo 1287962 3484901 := bbase (se 4 (by rfl) ⟨326709, by rfl⟩ : syracuseStep 3484901 = 653419) (by norm_num)
theorem B3263773 : Blo 1287962 3263773 := bbase (se 3 (by rfl) ⟨611957, by rfl⟩ : syracuseStep 3263773 = 1223915) (by norm_num)
theorem B4353317 : Blo 1287962 4353317 := bbase (se 4 (by rfl) ⟨408123, by rfl⟩ : syracuseStep 4353317 = 816247) (by norm_num)
theorem B2174269 : Blo 1287962 2174269 := bbase (se 3 (by rfl) ⟨407675, by rfl⟩ : syracuseStep 2174269 = 815351) (by norm_num)
theorem B1469765 : Blo 1287962 1469765 := bbase (se 4 (by rfl) ⟨137790, by rfl⟩ : syracuseStep 1469765 = 275581) (by norm_num)
theorem B11750741 : Blo 1287962 11750741 := bbase (se 11 (by rfl) ⟨8606, by rfl⟩ : syracuseStep 11750741 = 17213) (by norm_num)
theorem B3263885 : Blo 1287962 3263885 := bbase (se 3 (by rfl) ⟨611978, by rfl⟩ : syracuseStep 3263885 = 1223957) (by norm_num)
theorem B2174357 : Blo 1287962 2174357 := bbase (se 6 (by rfl) ⟨50961, by rfl⟩ : syracuseStep 2174357 = 101923) (by norm_num)
theorem B2321941 : Blo 1287962 2321941 := bbase (se 6 (by rfl) ⟨54420, by rfl⟩ : syracuseStep 2321941 = 108841) (by norm_num)
theorem B2174485 : Blo 1287962 2174485 := bbase (se 6 (by rfl) ⟨50964, by rfl⟩ : syracuseStep 2174485 = 101929) (by norm_num)
theorem B4132405 : Blo 1287962 4132405 := bbase (se 5 (by rfl) ⟨193706, by rfl⟩ : syracuseStep 4132405 = 387413) (by norm_num)
theorem B3264077 : Blo 1287962 3264077 := bbase (se 3 (by rfl) ⟨612014, by rfl⟩ : syracuseStep 3264077 = 1224029) (by norm_num)
theorem B2174573 : Blo 1287962 2174573 := bbase (se 3 (by rfl) ⟨407732, by rfl⟩ : syracuseStep 2174573 = 815465) (by norm_num)
theorem B6524549 : Blo 1287962 6524549 := bbase (se 4 (by rfl) ⟨611676, by rfl⟩ : syracuseStep 6524549 = 1223353) (by norm_num)
theorem B2174701 : Blo 1287962 2174701 := bbase (se 3 (by rfl) ⟨407756, by rfl⟩ : syracuseStep 2174701 = 815513) (by norm_num)
theorem B2789149 : Blo 1287962 2789149 := bbase (se 3 (by rfl) ⟨522965, by rfl⟩ : syracuseStep 2789149 = 1045931) (by norm_num)
theorem B5508917 : Blo 1287962 5508917 := bbase (se 5 (by rfl) ⟨258230, by rfl⟩ : syracuseStep 5508917 = 516461) (by norm_num)
theorem B2322245 : Blo 1287962 2322245 := bbase (se 4 (by rfl) ⟨217710, by rfl⟩ : syracuseStep 2322245 = 435421) (by norm_num)
theorem B2174789 : Blo 1287962 2174789 := bbase (se 4 (by rfl) ⟨203886, by rfl⟩ : syracuseStep 2174789 = 407773) (by norm_num)
theorem B2445157 : Blo 1287962 2445157 := bbase (se 4 (by rfl) ⟨229233, by rfl⟩ : syracuseStep 2445157 = 458467) (by norm_num)
theorem B1306481 : Blo 1287962 1306481 := bbase (se 2 (by rfl) ⟨489930, by rfl⟩ : syracuseStep 1306481 = 979861) (by norm_num)
theorem B1470349 : Blo 1287962 1470349 := bbase (se 3 (by rfl) ⟨275690, by rfl⟩ : syracuseStep 1470349 = 551381) (by norm_num)
theorem B4894613 : Blo 1287962 4894613 := bbase (se 6 (by rfl) ⟨114717, by rfl⟩ : syracuseStep 4894613 = 229435) (by norm_num)
theorem B3264421 : Blo 1287962 3264421 := bbase (se 4 (by rfl) ⟨306039, by rfl⟩ : syracuseStep 3264421 = 612079) (by norm_num)
theorem B2174917 : Blo 1287962 2174917 := bbase (se 4 (by rfl) ⟨203898, by rfl⟩ : syracuseStep 2174917 = 407797) (by norm_num)
theorem B3264533 : Blo 1287962 3264533 := bbase (se 6 (by rfl) ⟨76512, by rfl⟩ : syracuseStep 3264533 = 153025) (by norm_num)
theorem B2175005 : Blo 1287962 2175005 := bbase (se 3 (by rfl) ⟨407813, by rfl⟩ : syracuseStep 2175005 = 815627) (by norm_num)
theorem B2445461 : Blo 1287962 2445461 := bbase (se 6 (by rfl) ⟨57315, by rfl⟩ : syracuseStep 2445461 = 114631) (by norm_num)
theorem B3723413 : Blo 1287962 3723413 := bbase (se 6 (by rfl) ⟨87267, by rfl⟩ : syracuseStep 3723413 = 174535) (by norm_num)
theorem B2175133 : Blo 1287962 2175133 := bbase (se 3 (by rfl) ⟨407837, by rfl⟩ : syracuseStep 2175133 = 815675) (by norm_num)
theorem B4894901 : Blo 1287962 4894901 := bbase (se 5 (by rfl) ⟨229448, by rfl⟩ : syracuseStep 4894901 = 458897) (by norm_num)
theorem B3264725 : Blo 1287962 3264725 := bbase (se 7 (by rfl) ⟨38258, by rfl⟩ : syracuseStep 3264725 = 76517) (by norm_num)
theorem B4903157 : Blo 1287962 4903157 := bbase (se 5 (by rfl) ⟨229835, by rfl⟩ : syracuseStep 4903157 = 459671) (by norm_num)
theorem B2175221 : Blo 1287962 2175221 := bbase (se 5 (by rfl) ⟨101963, by rfl⟩ : syracuseStep 2175221 = 203927) (by norm_num)
theorem B18583829 : Blo 1287962 18583829 := bbase (se 6 (by rfl) ⟨435558, by rfl⟩ : syracuseStep 18583829 = 871117) (by norm_num)
theorem B2175349 : Blo 1287962 2175349 := bbase (se 5 (by rfl) ⟨101969, by rfl⟩ : syracuseStep 2175349 = 203939) (by norm_num)
theorem B1307065 : Blo 1287962 1307065 := bbase (se 2 (by rfl) ⟨490149, by rfl⟩ : syracuseStep 1307065 = 980299) (by norm_num)
theorem B2175437 : Blo 1287962 2175437 := bbase (se 3 (by rfl) ⟨407894, by rfl⟩ : syracuseStep 2175437 = 815789) (by norm_num)
theorem B16732693 : Blo 1287962 16732693 := bbase (se 6 (by rfl) ⟨392172, by rfl⟩ : syracuseStep 16732693 = 784345) (by norm_num)
theorem B3265069 : Blo 1287962 3265069 := bbase (se 3 (by rfl) ⟨612200, by rfl⟩ : syracuseStep 3265069 = 1224401) (by norm_num)
theorem B6279749 : Blo 1287962 6279749 := bbase (se 4 (by rfl) ⟨588726, by rfl⟩ : syracuseStep 6279749 = 1177453) (by norm_num)
theorem B2175565 : Blo 1287962 2175565 := bbase (se 3 (by rfl) ⟨407918, by rfl⟩ : syracuseStep 2175565 = 815837) (by norm_num)
theorem B7336565 : Blo 1287962 7336565 := bbase (se 5 (by rfl) ⟨343901, by rfl⟩ : syracuseStep 7336565 = 687803) (by norm_num)
theorem B3265181 : Blo 1287962 3265181 := bbase (se 3 (by rfl) ⟨612221, by rfl⟩ : syracuseStep 3265181 = 1224443) (by norm_num)
theorem B2175653 : Blo 1287962 2175653 := bbase (se 4 (by rfl) ⟨203967, by rfl⟩ : syracuseStep 2175653 = 407935) (by norm_num)
theorem B8819381 : Blo 1287962 8819381 := bbase (se 5 (by rfl) ⟨413408, by rfl⟩ : syracuseStep 8819381 = 826817) (by norm_num)
theorem B2323181 : Blo 1287962 2323181 := bbase (se 3 (by rfl) ⟨435596, by rfl⟩ : syracuseStep 2323181 = 871193) (by norm_num)
theorem B2175781 : Blo 1287962 2175781 := bbase (se 4 (by rfl) ⟨203979, by rfl⟩ : syracuseStep 2175781 = 407959) (by norm_num)
theorem B9794357 : Blo 1287962 9794357 := bbase (se 5 (by rfl) ⟨459110, by rfl⟩ : syracuseStep 9794357 = 918221) (by norm_num)
theorem B2175869 : Blo 1287962 2175869 := bbase (se 3 (by rfl) ⟨407975, by rfl⟩ : syracuseStep 2175869 = 815951) (by norm_num)
theorem B2446213 : Blo 1287962 2446213 := bbase (se 4 (by rfl) ⟨229332, by rfl⟩ : syracuseStep 2446213 = 458665) (by norm_num)
theorem B6525845 : Blo 1287962 6525845 := bbase (se 6 (by rfl) ⟨152949, by rfl⟩ : syracuseStep 6525845 = 305899) (by norm_num)
theorem B2175997 : Blo 1287962 2175997 := bbase (se 3 (by rfl) ⟨407999, by rfl⟩ : syracuseStep 2175997 = 815999) (by norm_num)
theorem B2446357 : Blo 1287962 2446357 := bbase (se 6 (by rfl) ⟨57336, by rfl⟩ : syracuseStep 2446357 = 114673) (by norm_num)
theorem B2176085 : Blo 1287962 2176085 := bbase (se 8 (by rfl) ⟨12750, by rfl⟩ : syracuseStep 2176085 = 25501) (by norm_num)
theorem B6616181 : Blo 1287962 6616181 := bbase (se 5 (by rfl) ⟨310133, by rfl⟩ : syracuseStep 6616181 = 620267) (by norm_num)
theorem B6198437 : Blo 1287962 6198437 := bbase (se 4 (by rfl) ⟨581103, by rfl⟩ : syracuseStep 6198437 = 1162207) (by norm_num)
theorem B1741997 : Blo 1287962 1741997 := bbase (se 3 (by rfl) ⟨326624, by rfl⟩ : syracuseStep 1741997 = 653249) (by norm_num)
theorem B2446517 : Blo 1287962 2446517 := bbase (se 5 (by rfl) ⟨114680, by rfl⟩ : syracuseStep 2446517 = 229361) (by norm_num)
theorem B1742029 : Blo 1287962 1742029 := bbase (se 3 (by rfl) ⟨326630, by rfl⟩ : syracuseStep 1742029 = 653261) (by norm_num)
theorem B9786581 : Blo 1287962 9786581 := bbase (se 7 (by rfl) ⟨114686, by rfl⟩ : syracuseStep 9786581 = 229373) (by norm_num)
theorem B2176213 : Blo 1287962 2176213 := bbase (se 7 (by rfl) ⟨25502, by rfl⟩ : syracuseStep 2176213 = 51005) (by norm_num)
theorem B2479405 : Blo 1287962 2479405 := bbase (se 3 (by rfl) ⟨464888, by rfl⟩ : syracuseStep 2479405 = 929777) (by norm_num)
theorem B1570093 : Blo 1287962 1570093 := bbase (se 3 (by rfl) ⟨294392, by rfl⟩ : syracuseStep 1570093 = 588785) (by norm_num)
theorem B2176301 : Blo 1287962 2176301 := bbase (se 3 (by rfl) ⟨408056, by rfl⟩ : syracuseStep 2176301 = 816113) (by norm_num)
theorem B8262965 : Blo 1287962 8262965 := bbase (se 5 (by rfl) ⟨387326, by rfl⟩ : syracuseStep 8262965 = 774653) (by norm_num)
theorem B2446661 : Blo 1287962 2446661 := bbase (se 4 (by rfl) ⟨229374, by rfl⟩ : syracuseStep 2446661 = 458749) (by norm_num)
theorem B4896085 : Blo 1287962 4896085 := bbase (se 13 (by rfl) ⟨896, by rfl⟩ : syracuseStep 4896085 = 1793) (by norm_num)
theorem B4347269 : Blo 1287962 4347269 := bbase (se 4 (by rfl) ⟨407556, by rfl⟩ : syracuseStep 4347269 = 815113) (by norm_num)
theorem B21755285 : Blo 1287962 21755285 := bbase (se 6 (by rfl) ⟨509889, by rfl⟩ : syracuseStep 21755285 = 1019779) (by norm_num)
theorem B2176429 : Blo 1287962 2176429 := bbase (se 3 (by rfl) ⟨408080, by rfl⟩ : syracuseStep 2176429 = 816161) (by norm_num)
theorem B11007413 : Blo 1287962 11007413 := bbase (se 5 (by rfl) ⟨515972, by rfl⟩ : syracuseStep 11007413 = 1031945) (by norm_num)
theorem B3306949 : Blo 1287962 3306949 := bbase (se 4 (by rfl) ⟨310026, by rfl⟩ : syracuseStep 3306949 = 620053) (by norm_num)
theorem B2176517 : Blo 1287962 2176517 := bbase (se 4 (by rfl) ⟨204048, by rfl⟩ : syracuseStep 2176517 = 408097) (by norm_num)
theorem B6190613 : Blo 1287962 6190613 := bbase (se 6 (by rfl) ⟨145092, by rfl⟩ : syracuseStep 6190613 = 290185) (by norm_num)
theorem B10589717 : Blo 1287962 10589717 := bbase (se 6 (by rfl) ⟨248196, by rfl⟩ : syracuseStep 10589717 = 496393) (by norm_num)
theorem B12383765 : Blo 1287962 12383765 := bbase (se 6 (by rfl) ⟨290244, by rfl⟩ : syracuseStep 12383765 = 580489) (by norm_num)
theorem B2446949 : Blo 1287962 2446949 := bbase (se 4 (by rfl) ⟨229401, by rfl⟩ : syracuseStep 2446949 = 458803) (by norm_num)
theorem B1767037 : Blo 1287962 1767037 := bbase (se 3 (by rfl) ⟨331319, by rfl⟩ : syracuseStep 1767037 = 662639) (by norm_num)
theorem B4896389 : Blo 1287962 4896389 := bbase (se 4 (by rfl) ⟨459036, by rfl⟩ : syracuseStep 4896389 = 918073) (by norm_num)
theorem B2176645 : Blo 1287962 2176645 := bbase (se 4 (by rfl) ⟨204060, by rfl⟩ : syracuseStep 2176645 = 408121) (by norm_num)
theorem B5502613 : Blo 1287962 5502613 := bbase (se 6 (by rfl) ⟨128967, by rfl⟩ : syracuseStep 5502613 = 257935) (by norm_num)
theorem B5502629 : Blo 1287962 5502629 := bbase (se 4 (by rfl) ⟨515871, by rfl⟩ : syracuseStep 5502629 = 1031743) (by norm_num)
theorem B2479781 : Blo 1287962 2479781 := bbase (se 4 (by rfl) ⟨232479, by rfl⟩ : syracuseStep 2479781 = 464959) (by norm_num)
theorem B6190805 : Blo 1287962 6190805 := bbase (se 7 (by rfl) ⟨72548, by rfl⟩ : syracuseStep 6190805 = 145097) (by norm_num)
theorem B2176733 : Blo 1287962 2176733 := bbase (se 3 (by rfl) ⟨408137, by rfl⟩ : syracuseStep 2176733 = 816275) (by norm_num)
theorem B2447101 : Blo 1287962 2447101 := bbase (se 3 (by rfl) ⟨458831, by rfl⟩ : syracuseStep 2447101 = 917663) (by norm_num)
theorem B1652501 : Blo 1287962 1652501 := bbase (se 6 (by rfl) ⟨38730, by rfl⟩ : syracuseStep 1652501 = 77461) (by norm_num)
theorem B7337749 : Blo 1287962 7337749 := bbase (se 6 (by rfl) ⟨171978, by rfl⟩ : syracuseStep 7337749 = 343957) (by norm_num)
theorem B9418517 : Blo 1287962 9418517 := bbase (se 6 (by rfl) ⟨220746, by rfl⟩ : syracuseStep 9418517 = 441493) (by norm_num)
theorem B4347701 : Blo 1287962 4347701 := bbase (se 5 (by rfl) ⟨203798, by rfl⟩ : syracuseStep 4347701 = 407597) (by norm_num)
theorem B3667781 : Blo 1287962 3667781 := bbase (se 4 (by rfl) ⟨343854, by rfl⟩ : syracuseStep 3667781 = 687709) (by norm_num)
theorem B1652609 : Blo 1287962 1652609 := bbase (se 2 (by rfl) ⟨619728, by rfl⟩ : syracuseStep 1652609 = 1239457) (by norm_num)
theorem B1325005 : Blo 1287962 1325005 := bbase (se 3 (by rfl) ⟨248438, by rfl⟩ : syracuseStep 1325005 = 496877) (by norm_num)
theorem B2447405 : Blo 1287962 2447405 := bbase (se 3 (by rfl) ⟨458888, by rfl⟩ : syracuseStep 2447405 = 917777) (by norm_num)
theorem B2897981 : Blo 1287962 2897981 := bbase (se 3 (by rfl) ⟨543371, by rfl⟩ : syracuseStep 2897981 = 1086743) (by norm_num)
theorem B2898053 : Blo 1287962 2898053 := bbase (se 4 (by rfl) ⟨271692, by rfl⟩ : syracuseStep 2898053 = 543385) (by norm_num)
theorem B6527141 : Blo 1287962 6527141 := bbase (se 4 (by rfl) ⟨611919, by rfl⟩ : syracuseStep 6527141 = 1223839) (by norm_num)
theorem B2898125 : Blo 1287962 2898125 := bbase (se 3 (by rfl) ⟨543398, by rfl⟩ : syracuseStep 2898125 = 1086797) (by norm_num)
theorem B4348133 : Blo 1287962 4348133 := bbase (se 4 (by rfl) ⟨407637, by rfl⟩ : syracuseStep 4348133 = 815275) (by norm_num)
theorem B2791693 : Blo 1287962 2791693 := bbase (se 3 (by rfl) ⟨523442, by rfl⟩ : syracuseStep 2791693 = 1046885) (by norm_num)
theorem B2898197 : Blo 1287962 2898197 := bbase (se 6 (by rfl) ⟨67926, by rfl⟩ : syracuseStep 2898197 = 135853) (by norm_num)
theorem B11155765 : Blo 1287962 11155765 := bbase (se 5 (by rfl) ⟨522926, by rfl⟩ : syracuseStep 11155765 = 1045853) (by norm_num)
theorem B2898269 : Blo 1287962 2898269 := bbase (se 3 (by rfl) ⟨543425, by rfl⟩ : syracuseStep 2898269 = 1086851) (by norm_num)
theorem B9288053 : Blo 1287962 9288053 := bbase (se 5 (by rfl) ⟨435377, by rfl⟩ : syracuseStep 9288053 = 870755) (by norm_num)
theorem B3307925 : Blo 1287962 3307925 := bbase (se 6 (by rfl) ⟨77529, by rfl⟩ : syracuseStep 3307925 = 155059) (by norm_num)
theorem B2898341 : Blo 1287962 2898341 := bbase (se 4 (by rfl) ⟨271719, by rfl⟩ : syracuseStep 2898341 = 543439) (by norm_num)
theorem B1341893 : Blo 1287962 1341893 := bbase (se 4 (by rfl) ⟨125802, by rfl⟩ : syracuseStep 1341893 = 251605) (by norm_num)
theorem B2898413 : Blo 1287962 2898413 := bbase (se 3 (by rfl) ⟨543452, by rfl⟩ : syracuseStep 2898413 = 1086905) (by norm_num)
theorem B2898485 : Blo 1287962 2898485 := bbase (se 5 (by rfl) ⟨135866, by rfl⟩ : syracuseStep 2898485 = 271733) (by norm_num)
theorem B2898557 : Blo 1287962 2898557 := bbase (se 3 (by rfl) ⟨543479, by rfl⟩ : syracuseStep 2898557 = 1086959) (by norm_num)
theorem B4348565 : Blo 1287962 4348565 := bbase (se 6 (by rfl) ⟨101919, by rfl⟩ : syracuseStep 4348565 = 203839) (by norm_num)
theorem B1931957 : Blo 1287962 1931957 := bbase (se 5 (by rfl) ⟨90560, by rfl⟩ : syracuseStep 1931957 = 181121) (by norm_num)
theorem B2898629 : Blo 1287962 2898629 := bbase (se 4 (by rfl) ⟨271746, by rfl⟩ : syracuseStep 2898629 = 543493) (by norm_num)
theorem B1931981 : Blo 1287962 1931981 := bbase (se 3 (by rfl) ⟨362246, by rfl⟩ : syracuseStep 1931981 = 724493) (by norm_num)
theorem B1932005 : Blo 1287962 1932005 := bbase (se 4 (by rfl) ⟨181125, by rfl⟩ : syracuseStep 1932005 = 362251) (by norm_num)
theorem B1932029 : Blo 1287962 1932029 := bbase (se 3 (by rfl) ⟨362255, by rfl⟩ : syracuseStep 1932029 = 724511) (by norm_num)
theorem B2898701 : Blo 1287962 2898701 := bbase (se 3 (by rfl) ⟨543506, by rfl⟩ : syracuseStep 2898701 = 1087013) (by norm_num)
theorem B1932053 : Blo 1287962 1932053 := bbase (se 6 (by rfl) ⟨45282, by rfl⟩ : syracuseStep 1932053 = 90565) (by norm_num)
theorem B2448157 : Blo 1287962 2448157 := bbase (se 3 (by rfl) ⟨459029, by rfl⟩ : syracuseStep 2448157 = 918059) (by norm_num)
theorem B2063141 : Blo 1287962 2063141 := bbase (se 4 (by rfl) ⟨193419, by rfl⟩ : syracuseStep 2063141 = 386839) (by norm_num)
theorem B3668773 : Blo 1287962 3668773 := bbase (se 4 (by rfl) ⟨343947, by rfl⟩ : syracuseStep 3668773 = 687895) (by norm_num)
theorem B1932077 : Blo 1287962 1932077 := bbase (se 3 (by rfl) ⟨362264, by rfl⟩ : syracuseStep 1932077 = 724529) (by norm_num)
theorem B2063173 : Blo 1287962 2063173 := bbase (se 4 (by rfl) ⟨193422, by rfl⟩ : syracuseStep 2063173 = 386845) (by norm_num)
theorem B1932101 : Blo 1287962 1932101 := bbase (se 4 (by rfl) ⟨181134, by rfl⟩ : syracuseStep 1932101 = 362269) (by norm_num)
theorem B1653577 : Blo 1287962 1653577 := bbase (se 2 (by rfl) ⟨620091, by rfl⟩ : syracuseStep 1653577 = 1240183) (by norm_num)
theorem B2898773 : Blo 1287962 2898773 := bbase (se 9 (by rfl) ⟨8492, by rfl⟩ : syracuseStep 2898773 = 16985) (by norm_num)
theorem B1932125 : Blo 1287962 1932125 := bbase (se 3 (by rfl) ⟨362273, by rfl⟩ : syracuseStep 1932125 = 724547) (by norm_num)
theorem B1833845 : Blo 1287962 1833845 := bbase (se 5 (by rfl) ⟨85961, by rfl⟩ : syracuseStep 1833845 = 171923) (by norm_num)
theorem B1932149 : Blo 1287962 1932149 := bbase (se 5 (by rfl) ⟨90569, by rfl⟩ : syracuseStep 1932149 = 181139) (by norm_num)
theorem B2751349 : Blo 1287962 2751349 := bbase (se 5 (by rfl) ⟨128969, by rfl⟩ : syracuseStep 2751349 = 257939) (by norm_num)
theorem B1932173 : Blo 1287962 1932173 := bbase (se 3 (by rfl) ⟨362282, by rfl⟩ : syracuseStep 1932173 = 724565) (by norm_num)
theorem B2898845 : Blo 1287962 2898845 := bbase (se 3 (by rfl) ⟨543533, by rfl⟩ : syracuseStep 2898845 = 1087067) (by norm_num)
theorem B1932197 : Blo 1287962 1932197 := bbase (se 4 (by rfl) ⟨181143, by rfl⟩ : syracuseStep 1932197 = 362287) (by norm_num)
theorem B2448301 : Blo 1287962 2448301 := bbase (se 3 (by rfl) ⟨459056, by rfl⟩ : syracuseStep 2448301 = 918113) (by norm_num)
theorem B1932221 : Blo 1287962 1932221 := bbase (se 3 (by rfl) ⟨362291, by rfl⟩ : syracuseStep 1932221 = 724583) (by norm_num)
theorem B1932245 : Blo 1287962 1932245 := bbase (se 7 (by rfl) ⟨22643, by rfl⟩ : syracuseStep 1932245 = 45287) (by norm_num)
theorem B3308501 : Blo 1287962 3308501 := bbase (se 7 (by rfl) ⟨38771, by rfl⟩ : syracuseStep 3308501 = 77543) (by norm_num)
theorem B2898917 : Blo 1287962 2898917 := bbase (se 4 (by rfl) ⟨271773, by rfl⟩ : syracuseStep 2898917 = 543547) (by norm_num)
theorem B1932269 : Blo 1287962 1932269 := bbase (se 3 (by rfl) ⟨362300, by rfl⟩ : syracuseStep 1932269 = 724601) (by norm_num)
theorem B1932293 : Blo 1287962 1932293 := bbase (se 4 (by rfl) ⟨181152, by rfl⟩ : syracuseStep 1932293 = 362305) (by norm_num)
theorem B1448977 : Blo 1287962 1448977 := bbase (se 2 (by rfl) ⟨543366, by rfl⟩ : syracuseStep 1448977 = 1086733) (by norm_num)
theorem B1932317 : Blo 1287962 1932317 := bbase (se 3 (by rfl) ⟨362309, by rfl⟩ : syracuseStep 1932317 = 724619) (by norm_num)
theorem B3308581 : Blo 1287962 3308581 := bbase (se 4 (by rfl) ⟨310179, by rfl⟩ : syracuseStep 3308581 = 620359) (by norm_num)
theorem B2898989 : Blo 1287962 2898989 := bbase (se 3 (by rfl) ⟨543560, by rfl⟩ : syracuseStep 2898989 = 1087121) (by norm_num)
theorem B2481197 : Blo 1287962 2481197 := bbase (se 3 (by rfl) ⟨465224, by rfl⟩ : syracuseStep 2481197 = 930449) (by norm_num)
theorem B1449013 : Blo 1287962 1449013 := bbase (se 5 (by rfl) ⟨67922, by rfl⟩ : syracuseStep 1449013 = 135845) (by norm_num)
theorem B1932341 : Blo 1287962 1932341 := bbase (se 5 (by rfl) ⟨90578, by rfl⟩ : syracuseStep 1932341 = 181157) (by norm_num)
theorem B4348997 : Blo 1287962 4348997 := bbase (se 4 (by rfl) ⟨407718, by rfl⟩ : syracuseStep 4348997 = 815437) (by norm_num)
theorem B1932365 : Blo 1287962 1932365 := bbase (se 3 (by rfl) ⟨362318, by rfl⟩ : syracuseStep 1932365 = 724637) (by norm_num)
theorem B2448461 : Blo 1287962 2448461 := bbase (se 3 (by rfl) ⟨459086, by rfl⟩ : syracuseStep 2448461 = 918173) (by norm_num)
theorem B1449049 : Blo 1287962 1449049 := bbase (se 2 (by rfl) ⟨543393, by rfl⟩ : syracuseStep 1449049 = 1086787) (by norm_num)
theorem B1932389 : Blo 1287962 1932389 := bbase (se 4 (by rfl) ⟨181161, by rfl⟩ : syracuseStep 1932389 = 362323) (by norm_num)
theorem B3095653 : Blo 1287962 3095653 := bbase (se 4 (by rfl) ⟨290217, by rfl⟩ : syracuseStep 3095653 = 580435) (by norm_num)
theorem B2899061 : Blo 1287962 2899061 := bbase (se 5 (by rfl) ⟨135893, by rfl⟩ : syracuseStep 2899061 = 271787) (by norm_num)
theorem B7445621 : Blo 1287962 7445621 := bbase (se 5 (by rfl) ⟨349013, by rfl⟩ : syracuseStep 7445621 = 698027) (by norm_num)
theorem B1449085 : Blo 1287962 1449085 := bbase (se 3 (by rfl) ⟨271703, by rfl⟩ : syracuseStep 1449085 = 543407) (by norm_num)
theorem B1932413 : Blo 1287962 1932413 := bbase (se 3 (by rfl) ⟨362327, by rfl⟩ : syracuseStep 1932413 = 724655) (by norm_num)
theorem B1932437 : Blo 1287962 1932437 := bbase (se 6 (by rfl) ⟨45291, by rfl⟩ : syracuseStep 1932437 = 90583) (by norm_num)
theorem B1449121 : Blo 1287962 1449121 := bbase (se 2 (by rfl) ⟨543420, by rfl⟩ : syracuseStep 1449121 = 1086841) (by norm_num)
theorem B1932461 : Blo 1287962 1932461 := bbase (se 3 (by rfl) ⟨362336, by rfl⟩ : syracuseStep 1932461 = 724673) (by norm_num)
theorem B2899133 : Blo 1287962 2899133 := bbase (se 3 (by rfl) ⟨543587, by rfl⟩ : syracuseStep 2899133 = 1087175) (by norm_num)
theorem B1547461 : Blo 1287962 1547461 := bbase (se 4 (by rfl) ⟨145074, by rfl⟩ : syracuseStep 1547461 = 290149) (by norm_num)
theorem B1449157 : Blo 1287962 1449157 := bbase (se 4 (by rfl) ⟨135858, by rfl⟩ : syracuseStep 1449157 = 271717) (by norm_num)
theorem B1932485 : Blo 1287962 1932485 := bbase (se 4 (by rfl) ⟨181170, by rfl⟩ : syracuseStep 1932485 = 362341) (by norm_num)
theorem B1932509 : Blo 1287962 1932509 := bbase (se 3 (by rfl) ⟨362345, by rfl⟩ : syracuseStep 1932509 = 724691) (by norm_num)
theorem B2448605 : Blo 1287962 2448605 := bbase (se 3 (by rfl) ⟨459113, by rfl⟩ : syracuseStep 2448605 = 918227) (by norm_num)
theorem B1449193 : Blo 1287962 1449193 := bbase (se 2 (by rfl) ⟨543447, by rfl⟩ : syracuseStep 1449193 = 1086895) (by norm_num)
theorem B2751725 : Blo 1287962 2751725 := bbase (se 3 (by rfl) ⟨515948, by rfl⟩ : syracuseStep 2751725 = 1031897) (by norm_num)
theorem B1932533 : Blo 1287962 1932533 := bbase (se 5 (by rfl) ⟨90587, by rfl⟩ : syracuseStep 1932533 = 181175) (by norm_num)
theorem B2899205 : Blo 1287962 2899205 := bbase (se 4 (by rfl) ⟨271800, by rfl⟩ : syracuseStep 2899205 = 543601) (by norm_num)
theorem B1449229 : Blo 1287962 1449229 := bbase (se 3 (by rfl) ⟨271730, by rfl⟩ : syracuseStep 1449229 = 543461) (by norm_num)
theorem B1932557 : Blo 1287962 1932557 := bbase (se 3 (by rfl) ⟨362354, by rfl⟩ : syracuseStep 1932557 = 724709) (by norm_num)
theorem B1932581 : Blo 1287962 1932581 := bbase (se 4 (by rfl) ⟨181179, by rfl⟩ : syracuseStep 1932581 = 362359) (by norm_num)
theorem B1449265 : Blo 1287962 1449265 := bbase (se 2 (by rfl) ⟨543474, by rfl⟩ : syracuseStep 1449265 = 1086949) (by norm_num)
theorem B1932605 : Blo 1287962 1932605 := bbase (se 3 (by rfl) ⟨362363, by rfl⟩ : syracuseStep 1932605 = 724727) (by norm_num)
theorem B2899277 : Blo 1287962 2899277 := bbase (se 3 (by rfl) ⟨543614, by rfl⟩ : syracuseStep 2899277 = 1087229) (by norm_num)
theorem B1449301 : Blo 1287962 1449301 := bbase (se 11 (by rfl) ⟨1061, by rfl⟩ : syracuseStep 1449301 = 2123) (by norm_num)
theorem B1932629 : Blo 1287962 1932629 := bbase (se 11 (by rfl) ⟨1415, by rfl⟩ : syracuseStep 1932629 = 2831) (by norm_num)
theorem B3399005 : Blo 1287962 3399005 := bbase (se 3 (by rfl) ⟨637313, by rfl⟩ : syracuseStep 3399005 = 1274627) (by norm_num)
theorem B1375589 : Blo 1287962 1375589 := bbase (se 4 (by rfl) ⟨128961, by rfl⟩ : syracuseStep 1375589 = 257923) (by norm_num)
theorem B1932653 : Blo 1287962 1932653 := bbase (se 3 (by rfl) ⟨362372, by rfl⟩ : syracuseStep 1932653 = 724745) (by norm_num)
theorem B10452341 : Blo 1287962 10452341 := bbase (se 5 (by rfl) ⟨489953, by rfl⟩ : syracuseStep 10452341 = 979907) (by norm_num)
theorem B1449337 : Blo 1287962 1449337 := bbase (se 2 (by rfl) ⟨543501, by rfl⟩ : syracuseStep 1449337 = 1087003) (by norm_num)
theorem B1932677 : Blo 1287962 1932677 := bbase (se 4 (by rfl) ⟨181188, by rfl⟩ : syracuseStep 1932677 = 362377) (by norm_num)
theorem B2899349 : Blo 1287962 2899349 := bbase (se 6 (by rfl) ⟨67953, by rfl⟩ : syracuseStep 2899349 = 135907) (by norm_num)
theorem B8256917 : Blo 1287962 8256917 := bbase (se 6 (by rfl) ⟨193521, by rfl⟩ : syracuseStep 8256917 = 387043) (by norm_num)
theorem B1449373 : Blo 1287962 1449373 := bbase (se 3 (by rfl) ⟨271757, by rfl⟩ : syracuseStep 1449373 = 543515) (by norm_num)
theorem B1932701 : Blo 1287962 1932701 := bbase (se 3 (by rfl) ⟨362381, by rfl⟩ : syracuseStep 1932701 = 724763) (by norm_num)
theorem B1932725 : Blo 1287962 1932725 := bbase (se 5 (by rfl) ⟨90596, by rfl⟩ : syracuseStep 1932725 = 181193) (by norm_num)
theorem B6528437 : Blo 1287962 6528437 := bbase (se 5 (by rfl) ⟨306020, by rfl⟩ : syracuseStep 6528437 = 612041) (by norm_num)
theorem B1449409 : Blo 1287962 1449409 := bbase (se 2 (by rfl) ⟨543528, by rfl⟩ : syracuseStep 1449409 = 1087057) (by norm_num)
theorem B1932749 : Blo 1287962 1932749 := bbase (se 3 (by rfl) ⟨362390, by rfl⟩ : syracuseStep 1932749 = 724781) (by norm_num)
theorem B6618581 : Blo 1287962 6618581 := bbase (se 7 (by rfl) ⟨77561, by rfl⟩ : syracuseStep 6618581 = 155123) (by norm_num)
theorem B2899421 : Blo 1287962 2899421 := bbase (se 3 (by rfl) ⟨543641, by rfl⟩ : syracuseStep 2899421 = 1087283) (by norm_num)
theorem B1449445 : Blo 1287962 1449445 := bbase (se 4 (by rfl) ⟨135885, by rfl⟩ : syracuseStep 1449445 = 271771) (by norm_num)
theorem B1932773 : Blo 1287962 1932773 := bbase (se 4 (by rfl) ⟨181197, by rfl⟩ : syracuseStep 1932773 = 362395) (by norm_num)
theorem B4349429 : Blo 1287962 4349429 := bbase (se 5 (by rfl) ⟨203879, by rfl⟩ : syracuseStep 4349429 = 407759) (by norm_num)
theorem B1932797 : Blo 1287962 1932797 := bbase (se 3 (by rfl) ⟨362399, by rfl⟩ : syracuseStep 1932797 = 724799) (by norm_num)
theorem B2448893 : Blo 1287962 2448893 := bbase (se 3 (by rfl) ⟨459167, by rfl⟩ : syracuseStep 2448893 = 918335) (by norm_num)
theorem B1449481 : Blo 1287962 1449481 := bbase (se 2 (by rfl) ⟨543555, by rfl⟩ : syracuseStep 1449481 = 1087111) (by norm_num)
theorem B1932821 : Blo 1287962 1932821 := bbase (se 6 (by rfl) ⟨45300, by rfl⟩ : syracuseStep 1932821 = 90601) (by norm_num)
theorem B2899493 : Blo 1287962 2899493 := bbase (se 4 (by rfl) ⟨271827, by rfl⟩ : syracuseStep 2899493 = 543655) (by norm_num)
theorem B1449517 : Blo 1287962 1449517 := bbase (se 3 (by rfl) ⟨271784, by rfl⟩ : syracuseStep 1449517 = 543569) (by norm_num)
theorem B1932845 : Blo 1287962 1932845 := bbase (se 3 (by rfl) ⟨362408, by rfl⟩ : syracuseStep 1932845 = 724817) (by norm_num)
theorem B1932869 : Blo 1287962 1932869 := bbase (se 4 (by rfl) ⟨181206, by rfl⟩ : syracuseStep 1932869 = 362413) (by norm_num)
theorem B1449553 : Blo 1287962 1449553 := bbase (se 2 (by rfl) ⟨543582, by rfl⟩ : syracuseStep 1449553 = 1087165) (by norm_num)
theorem B1932893 : Blo 1287962 1932893 := bbase (se 3 (by rfl) ⟨362417, by rfl⟩ : syracuseStep 1932893 = 724835) (by norm_num)
theorem B1834597 : Blo 1287962 1834597 := bbase (se 4 (by rfl) ⟨171993, by rfl⟩ : syracuseStep 1834597 = 343987) (by norm_num)
theorem B2899565 : Blo 1287962 2899565 := bbase (se 3 (by rfl) ⟨543668, by rfl⟩ : syracuseStep 2899565 = 1087337) (by norm_num)
theorem B1449589 : Blo 1287962 1449589 := bbase (se 5 (by rfl) ⟨67949, by rfl⟩ : syracuseStep 1449589 = 135899) (by norm_num)
theorem B1932917 : Blo 1287962 1932917 := bbase (se 5 (by rfl) ⟨90605, by rfl⟩ : syracuseStep 1932917 = 181211) (by norm_num)
theorem B1932941 : Blo 1287962 1932941 := bbase (se 3 (by rfl) ⟨362426, by rfl⟩ : syracuseStep 1932941 = 724853) (by norm_num)
theorem B1449625 : Blo 1287962 1449625 := bbase (se 2 (by rfl) ⟨543609, by rfl⟩ : syracuseStep 1449625 = 1087219) (by norm_num)
theorem B1932965 : Blo 1287962 1932965 := bbase (se 4 (by rfl) ⟨181215, by rfl⟩ : syracuseStep 1932965 = 362431) (by norm_num)
theorem B2899637 : Blo 1287962 2899637 := bbase (se 5 (by rfl) ⟨135920, by rfl⟩ : syracuseStep 2899637 = 271841) (by norm_num)
theorem B1449661 : Blo 1287962 1449661 := bbase (se 3 (by rfl) ⟨271811, by rfl⟩ : syracuseStep 1449661 = 543623) (by norm_num)
theorem B1932989 : Blo 1287962 1932989 := bbase (se 3 (by rfl) ⟨362435, by rfl⟩ : syracuseStep 1932989 = 724871) (by norm_num)
theorem B3096269 : Blo 1287962 3096269 := bbase (se 3 (by rfl) ⟨580550, by rfl⟩ : syracuseStep 3096269 = 1161101) (by norm_num)
theorem B1933013 : Blo 1287962 1933013 := bbase (se 7 (by rfl) ⟨22652, by rfl⟩ : syracuseStep 1933013 = 45305) (by norm_num)
theorem B7339733 : Blo 1287962 7339733 := bbase (se 7 (by rfl) ⟨86012, by rfl⟩ : syracuseStep 7339733 = 172025) (by norm_num)
theorem B1449697 : Blo 1287962 1449697 := bbase (se 2 (by rfl) ⟨543636, by rfl⟩ : syracuseStep 1449697 = 1087273) (by norm_num)
theorem B2064101 : Blo 1287962 2064101 := bbase (se 4 (by rfl) ⟨193509, by rfl⟩ : syracuseStep 2064101 = 387019) (by norm_num)
theorem B1654501 : Blo 1287962 1654501 := bbase (se 4 (by rfl) ⟨155109, by rfl⟩ : syracuseStep 1654501 = 310219) (by norm_num)
theorem B1933037 : Blo 1287962 1933037 := bbase (se 3 (by rfl) ⟨362444, by rfl⟩ : syracuseStep 1933037 = 724889) (by norm_num)
theorem B2899709 : Blo 1287962 2899709 := bbase (se 3 (by rfl) ⟨543695, by rfl⟩ : syracuseStep 2899709 = 1087391) (by norm_num)
theorem B1449733 : Blo 1287962 1449733 := bbase (se 4 (by rfl) ⟨135912, by rfl⟩ : syracuseStep 1449733 = 271825) (by norm_num)
theorem B1933061 : Blo 1287962 1933061 := bbase (se 4 (by rfl) ⟨181224, by rfl⟩ : syracuseStep 1933061 = 362449) (by norm_num)
theorem B4185877 : Blo 1287962 4185877 := bbase (se 6 (by rfl) ⟨98106, by rfl⟩ : syracuseStep 4185877 = 196213) (by norm_num)
theorem B3260189 : Blo 1287962 3260189 := bbase (se 3 (by rfl) ⟨611285, by rfl⟩ : syracuseStep 3260189 = 1222571) (by norm_num)
theorem B1933085 : Blo 1287962 1933085 := bbase (se 3 (by rfl) ⟨362453, by rfl⟩ : syracuseStep 1933085 = 724907) (by norm_num)
theorem B1376033 : Blo 1287962 1376033 := bbase (se 2 (by rfl) ⟨516012, by rfl⟩ : syracuseStep 1376033 = 1032025) (by norm_num)
theorem B1449769 : Blo 1287962 1449769 := bbase (se 2 (by rfl) ⟨543663, by rfl⟩ : syracuseStep 1449769 = 1087327) (by norm_num)
theorem B1933109 : Blo 1287962 1933109 := bbase (se 5 (by rfl) ⟨90614, by rfl⟩ : syracuseStep 1933109 = 181229) (by norm_num)
theorem B2899781 : Blo 1287962 2899781 := bbase (se 4 (by rfl) ⟨271854, by rfl⟩ : syracuseStep 2899781 = 543709) (by norm_num)
theorem B1449805 : Blo 1287962 1449805 := bbase (se 3 (by rfl) ⟨271838, by rfl⟩ : syracuseStep 1449805 = 543677) (by norm_num)
theorem B1933133 : Blo 1287962 1933133 := bbase (se 3 (by rfl) ⟨362462, by rfl⟩ : syracuseStep 1933133 = 724925) (by norm_num)
theorem B6520661 : Blo 1287962 6520661 := bbase (se 9 (by rfl) ⟨19103, by rfl⟩ : syracuseStep 6520661 = 38207) (by norm_num)
theorem B1933157 : Blo 1287962 1933157 := bbase (se 4 (by rfl) ⟨181233, by rfl⟩ : syracuseStep 1933157 = 362467) (by norm_num)
theorem B2236261 : Blo 1287962 2236261 := bbase (se 4 (by rfl) ⟨209649, by rfl⟩ : syracuseStep 2236261 = 419299) (by norm_num)
theorem B1449841 : Blo 1287962 1449841 := bbase (se 2 (by rfl) ⟨543690, by rfl⟩ : syracuseStep 1449841 = 1087381) (by norm_num)
theorem B3669877 : Blo 1287962 3669877 := bbase (se 5 (by rfl) ⟨172025, by rfl⟩ : syracuseStep 3669877 = 344051) (by norm_num)
theorem B5504885 : Blo 1287962 5504885 := bbase (se 5 (by rfl) ⟨258041, by rfl⟩ : syracuseStep 5504885 = 516083) (by norm_num)
theorem B1933181 : Blo 1287962 1933181 := bbase (se 3 (by rfl) ⟨362471, by rfl⟩ : syracuseStep 1933181 = 724943) (by norm_num)
theorem B2899853 : Blo 1287962 2899853 := bbase (se 3 (by rfl) ⟨543722, by rfl⟩ : syracuseStep 2899853 = 1087445) (by norm_num)
theorem B1449877 : Blo 1287962 1449877 := bbase (se 6 (by rfl) ⟨33981, by rfl⟩ : syracuseStep 1449877 = 67963) (by norm_num)
theorem B1933205 : Blo 1287962 1933205 := bbase (se 6 (by rfl) ⟨45309, by rfl⟩ : syracuseStep 1933205 = 90619) (by norm_num)
theorem B4349861 : Blo 1287962 4349861 := bbase (se 4 (by rfl) ⟨407799, by rfl⟩ : syracuseStep 4349861 = 815599) (by norm_num)
theorem B1933229 : Blo 1287962 1933229 := bbase (se 3 (by rfl) ⟨362480, by rfl⟩ : syracuseStep 1933229 = 724961) (by norm_num)
theorem B1449913 : Blo 1287962 1449913 := bbase (se 2 (by rfl) ⟨543717, by rfl⟩ : syracuseStep 1449913 = 1087435) (by norm_num)
theorem B1630145 : Blo 1287962 1630145 := bbase (se 2 (by rfl) ⟨611304, by rfl⟩ : syracuseStep 1630145 = 1222609) (by norm_num)
theorem B1933253 : Blo 1287962 1933253 := bbase (se 4 (by rfl) ⟨181242, by rfl⟩ : syracuseStep 1933253 = 362485) (by norm_num)
theorem B2899925 : Blo 1287962 2899925 := bbase (se 7 (by rfl) ⟨33983, by rfl⟩ : syracuseStep 2899925 = 67967) (by norm_num)
theorem B1449949 : Blo 1287962 1449949 := bbase (se 3 (by rfl) ⟨271865, by rfl⟩ : syracuseStep 1449949 = 543731) (by norm_num)
theorem B1933277 : Blo 1287962 1933277 := bbase (se 3 (by rfl) ⟨362489, by rfl⟩ : syracuseStep 1933277 = 724979) (by norm_num)
theorem B1933301 : Blo 1287962 1933301 := bbase (se 5 (by rfl) ⟨90623, by rfl⟩ : syracuseStep 1933301 = 181247) (by norm_num)
theorem B1630201 : Blo 1287962 1630201 := bbase (se 2 (by rfl) ⟨611325, by rfl⟩ : syracuseStep 1630201 = 1222651) (by norm_num)
theorem B1933313 : Blo 1287962 1933313 := bstep (se 2 (by rfl) ⟨724992, by rfl⟩ : syracuseStep 1933313 = 1449985) B1449985
theorem B4964365 : Blo 1287962 4964365 := bstep (se 3 (by rfl) ⟨930818, by rfl⟩ : syracuseStep 4964365 = 1861637) B1861637
theorem B4349969 : Blo 1287962 4349969 := bstep (se 2 (by rfl) ⟨1631238, by rfl⟩ : syracuseStep 4349969 = 3262477) B3262477
theorem B2064403 : Blo 1287962 2064403 := bstep (se 1 (by rfl) ⟨1548302, by rfl⟩ : syracuseStep 2064403 = 3096605) B3096605
theorem B1933331 : Blo 1287962 1933331 := bstep (se 1 (by rfl) ⟨1449998, by rfl⟩ : syracuseStep 1933331 = 2899997) B2899997
theorem B1450003 : Blo 1287962 1450003 := bstep (se 1 (by rfl) ⟨1087502, by rfl⟩ : syracuseStep 1450003 = 2175005) B2175005
theorem B1933361 : Blo 1287962 1933361 := bstep (se 2 (by rfl) ⟨725010, by rfl⟩ : syracuseStep 1933361 = 1450021) B1450021
theorem B3260483 : Blo 1287962 3260483 := bstep (se 1 (by rfl) ⟨2445362, by rfl⟩ : syracuseStep 3260483 = 4890725) B4890725
theorem B2752579 : Blo 1287962 2752579 := bstep (se 1 (by rfl) ⟨2064434, by rfl⟩ : syracuseStep 2752579 = 4128869) B4128869
theorem B1933379 : Blo 1287962 1933379 := bstep (se 1 (by rfl) ⟨1450034, by rfl⟩ : syracuseStep 1933379 = 2900069) B2900069
theorem B1933409 : Blo 1287962 1933409 := bstep (se 2 (by rfl) ⟨725028, by rfl⟩ : syracuseStep 1933409 = 1450057) B1450057
theorem B1630307 : Blo 1287962 1630307 := bstep (se 1 (by rfl) ⟨1222730, by rfl⟩ : syracuseStep 1630307 = 2445461) B2445461
theorem B1933427 : Blo 1287962 1933427 := bstep (se 1 (by rfl) ⟨1450070, by rfl⟩ : syracuseStep 1933427 = 2900141) B2900141
theorem B7340165 : Blo 1287962 7340165 := bstep (se 4 (by rfl) ⟨688140, by rfl⟩ : syracuseStep 7340165 = 1376281) B1376281
theorem B1933457 : Blo 1287962 1933457 := bstep (se 2 (by rfl) ⟨725046, by rfl⟩ : syracuseStep 1933457 = 1450093) B1450093
theorem B1933475 : Blo 1287962 1933475 := bstep (se 1 (by rfl) ⟨1450106, by rfl⟩ : syracuseStep 1933475 = 2900213) B2900213
theorem B1450147 : Blo 1287962 1450147 := bstep (se 1 (by rfl) ⟨1087610, by rfl⟩ : syracuseStep 1450147 = 2175221) B2175221
theorem B1933505 : Blo 1287962 1933505 := bstep (se 2 (by rfl) ⟨725064, by rfl⟩ : syracuseStep 1933505 = 1450129) B1450129
theorem B3309763 : Blo 1287962 3309763 := bstep (se 1 (by rfl) ⟨2482322, by rfl⟩ : syracuseStep 3309763 = 4964645) B4964645
theorem B2900177 : Blo 1287962 2900177 := bstep (se 2 (by rfl) ⟨1087566, by rfl⟩ : syracuseStep 2900177 = 2175133) B2175133
theorem B1933523 : Blo 1287962 1933523 := bstep (se 1 (by rfl) ⟨1450142, by rfl⟩ : syracuseStep 1933523 = 2900285) B2900285
theorem B6193379 : Blo 1287962 6193379 := bstep (se 1 (by rfl) ⟨4645034, by rfl⟩ : syracuseStep 6193379 = 9290069) B9290069
theorem B2900195 : Blo 1287962 2900195 := bstep (se 1 (by rfl) ⟨2175146, by rfl⟩ : syracuseStep 2900195 = 4350293) B4350293
theorem B1933553 : Blo 1287962 1933553 := bstep (se 2 (by rfl) ⟨725082, by rfl⟩ : syracuseStep 1933553 = 1450165) B1450165
theorem B3260675 : Blo 1287962 3260675 := bstep (se 1 (by rfl) ⟨2445506, by rfl⟩ : syracuseStep 3260675 = 4891013) B4891013
theorem B1933571 : Blo 1287962 1933571 := bstep (se 1 (by rfl) ⟨1450178, by rfl⟩ : syracuseStep 1933571 = 2900357) B2900357
theorem B1933601 : Blo 1287962 1933601 := bstep (se 2 (by rfl) ⟨725100, by rfl⟩ : syracuseStep 1933601 = 1450201) B1450201
theorem B1376563 : Blo 1287962 1376563 := bstep (se 1 (by rfl) ⟨1032422, by rfl⟩ : syracuseStep 1376563 = 2064845) B2064845
theorem B1933619 : Blo 1287962 1933619 := bstep (se 1 (by rfl) ⟨1450214, by rfl⟩ : syracuseStep 1933619 = 2900429) B2900429
theorem B1450291 : Blo 1287962 1450291 := bstep (se 1 (by rfl) ⟨1087718, by rfl⟩ : syracuseStep 1450291 = 2175437) B2175437
theorem B1933649 : Blo 1287962 1933649 := bstep (se 2 (by rfl) ⟨725118, by rfl⟩ : syracuseStep 1933649 = 1450237) B1450237
theorem B1933667 : Blo 1287962 1933667 := bstep (se 1 (by rfl) ⟨1450250, by rfl⟩ : syracuseStep 1933667 = 2900501) B2900501
theorem B1933697 : Blo 1287962 1933697 := bstep (se 2 (by rfl) ⟨725136, by rfl⟩ : syracuseStep 1933697 = 1450273) B1450273
theorem B4186499 : Blo 1287962 4186499 := bstep (se 1 (by rfl) ⟨3139874, by rfl⟩ : syracuseStep 4186499 = 6279749) B6279749
theorem B9929101 : Blo 1287962 9929101 := bstep (se 3 (by rfl) ⟨1861706, by rfl⟩ : syracuseStep 9929101 = 3723413) B3723413
theorem B1933715 : Blo 1287962 1933715 := bstep (se 1 (by rfl) ⟨1450286, by rfl⟩ : syracuseStep 1933715 = 2900573) B2900573
theorem B4891043 : Blo 1287962 4891043 := bstep (se 1 (by rfl) ⟨3668282, by rfl⟩ : syracuseStep 4891043 = 7336565) B7336565
theorem B1933745 : Blo 1287962 1933745 := bstep (se 2 (by rfl) ⟨725154, by rfl⟩ : syracuseStep 1933745 = 1450309) B1450309
theorem B1933763 : Blo 1287962 1933763 := bstep (se 1 (by rfl) ⟨1450322, by rfl⟩ : syracuseStep 1933763 = 2900645) B2900645
theorem B1450435 : Blo 1287962 1450435 := bstep (se 1 (by rfl) ⟨1087826, by rfl⟩ : syracuseStep 1450435 = 2175653) B2175653
theorem B4645325 : Blo 1287962 4645325 := bstep (se 3 (by rfl) ⟨870998, by rfl⟩ : syracuseStep 4645325 = 1741997) B1741997
theorem B1933793 : Blo 1287962 1933793 := bstep (se 2 (by rfl) ⟨725172, by rfl⟩ : syracuseStep 1933793 = 1450345) B1450345
theorem B2900465 : Blo 1287962 2900465 := bstep (se 2 (by rfl) ⟨1087674, by rfl⟩ : syracuseStep 2900465 = 2175349) B2175349
theorem B1933811 : Blo 1287962 1933811 := bstep (se 1 (by rfl) ⟨1450358, by rfl⟩ : syracuseStep 1933811 = 2900717) B2900717
theorem B2900483 : Blo 1287962 2900483 := bstep (se 1 (by rfl) ⟨2175362, by rfl⟩ : syracuseStep 2900483 = 4350725) B4350725
theorem B2753041 : Blo 1287962 2753041 := bstep (se 2 (by rfl) ⟨1032390, by rfl⟩ : syracuseStep 2753041 = 2064781) B2064781
theorem B1933841 : Blo 1287962 1933841 := bstep (se 2 (by rfl) ⟨725190, by rfl⟩ : syracuseStep 1933841 = 1450381) B1450381
theorem B1933859 : Blo 1287962 1933859 := bstep (se 1 (by rfl) ⟨1450394, by rfl⟩ : syracuseStep 1933859 = 2900789) B2900789
theorem B6529571 : Blo 1287962 6529571 := bstep (se 1 (by rfl) ⟨4897178, by rfl⟩ : syracuseStep 6529571 = 9794357) B9794357
theorem B4350509 : Blo 1287962 4350509 := bstep (se 3 (by rfl) ⟨815720, by rfl⟩ : syracuseStep 4350509 = 1631441) B1631441
theorem B1933889 : Blo 1287962 1933889 := bstep (se 2 (by rfl) ⟨725208, by rfl⟩ : syracuseStep 1933889 = 1450417) B1450417
theorem B1933907 : Blo 1287962 1933907 := bstep (se 1 (by rfl) ⟨1450430, by rfl⟩ : syracuseStep 1933907 = 2900861) B2900861
theorem B1450579 : Blo 1287962 1450579 := bstep (se 1 (by rfl) ⟨1087934, by rfl⟩ : syracuseStep 1450579 = 2175869) B2175869
theorem B1835617 : Blo 1287962 1835617 := bstep (se 2 (by rfl) ⟨688356, by rfl⟩ : syracuseStep 1835617 = 1376713) B1376713
theorem B4350563 : Blo 1287962 4350563 := bstep (se 1 (by rfl) ⟨3262922, by rfl⟩ : syracuseStep 4350563 = 6525845) B6525845
theorem B1933937 : Blo 1287962 1933937 := bstep (se 2 (by rfl) ⟨725226, by rfl⟩ : syracuseStep 1933937 = 1450453) B1450453
theorem B1933955 : Blo 1287962 1933955 := bstep (se 1 (by rfl) ⟨1450466, by rfl⟩ : syracuseStep 1933955 = 2900933) B2900933
theorem B13075085 : Blo 1287962 13075085 := bstep (se 3 (by rfl) ⟨2451578, by rfl⟩ : syracuseStep 13075085 = 4903157) B4903157
theorem B1933985 : Blo 1287962 1933985 := bstep (se 2 (by rfl) ⟨725244, by rfl⟩ : syracuseStep 1933985 = 1450489) B1450489
theorem B1934003 : Blo 1287962 1934003 := bstep (se 1 (by rfl) ⟨1450502, by rfl⟩ : syracuseStep 1934003 = 2901005) B2901005
theorem B1835713 : Blo 1287962 1835713 := bstep (se 2 (by rfl) ⟨688392, by rfl⟩ : syracuseStep 1835713 = 1376785) B1376785
theorem B1934033 : Blo 1287962 1934033 := bstep (se 2 (by rfl) ⟨725262, by rfl⟩ : syracuseStep 1934033 = 1450525) B1450525
theorem B1934051 : Blo 1287962 1934051 := bstep (se 1 (by rfl) ⟨1450538, by rfl⟩ : syracuseStep 1934051 = 2901077) B2901077
theorem B1450723 : Blo 1287962 1450723 := bstep (se 1 (by rfl) ⟨1088042, by rfl⟩ : syracuseStep 1450723 = 2176085) B2176085
theorem B1934081 : Blo 1287962 1934081 := bstep (se 2 (by rfl) ⟨725280, by rfl⟩ : syracuseStep 1934081 = 1450561) B1450561
theorem B2900753 : Blo 1287962 2900753 := bstep (se 2 (by rfl) ⟨1087782, by rfl⟩ : syracuseStep 2900753 = 2175565) B2175565
theorem B1934099 : Blo 1287962 1934099 := bstep (se 1 (by rfl) ⟨1450574, by rfl⟩ : syracuseStep 1934099 = 2901149) B2901149
theorem B1631011 : Blo 1287962 1631011 := bstep (se 1 (by rfl) ⟨1223258, by rfl⟩ : syracuseStep 1631011 = 2446517) B2446517
theorem B2900771 : Blo 1287962 2900771 := bstep (se 1 (by rfl) ⟨2175578, by rfl⟩ : syracuseStep 2900771 = 4351157) B4351157
theorem B1934129 : Blo 1287962 1934129 := bstep (se 2 (by rfl) ⟨725298, by rfl⟩ : syracuseStep 1934129 = 1450597) B1450597
theorem B1934147 : Blo 1287962 1934147 := bstep (se 1 (by rfl) ⟨1450610, by rfl⟩ : syracuseStep 1934147 = 2901221) B2901221
theorem B1934177 : Blo 1287962 1934177 := bstep (se 2 (by rfl) ⟨725316, by rfl⟩ : syracuseStep 1934177 = 1450633) B1450633
theorem B4350833 : Blo 1287962 4350833 := bstep (se 2 (by rfl) ⟨1631562, by rfl⟩ : syracuseStep 4350833 = 3263125) B3263125
theorem B1934195 : Blo 1287962 1934195 := bstep (se 1 (by rfl) ⟨1450646, by rfl⟩ : syracuseStep 1934195 = 2901293) B2901293
theorem B1450867 : Blo 1287962 1450867 := bstep (se 1 (by rfl) ⟨1088150, by rfl⟩ : syracuseStep 1450867 = 2176301) B2176301
theorem B1631107 : Blo 1287962 1631107 := bstep (se 1 (by rfl) ⟨1223330, by rfl⟩ : syracuseStep 1631107 = 2446661) B2446661
theorem B1934225 : Blo 1287962 1934225 := bstep (se 2 (by rfl) ⟨725334, by rfl⟩ : syracuseStep 1934225 = 1450669) B1450669
theorem B1934243 : Blo 1287962 1934243 := bstep (se 1 (by rfl) ⟨1450682, by rfl⟩ : syracuseStep 1934243 = 2901365) B2901365
theorem B1934273 : Blo 1287962 1934273 := bstep (se 2 (by rfl) ⟨725352, by rfl⟩ : syracuseStep 1934273 = 1450705) B1450705
theorem B1934291 : Blo 1287962 1934291 := bstep (se 1 (by rfl) ⟨1450718, by rfl⟩ : syracuseStep 1934291 = 2901437) B2901437
theorem B1934321 : Blo 1287962 1934321 := bstep (se 2 (by rfl) ⟨725370, by rfl⟩ : syracuseStep 1934321 = 1450741) B1450741
theorem B2065409 : Blo 1287962 2065409 := bstep (se 2 (by rfl) ⟨774528, by rfl⟩ : syracuseStep 2065409 = 1549057) B1549057
theorem B1934339 : Blo 1287962 1934339 := bstep (se 1 (by rfl) ⟨1450754, by rfl⟩ : syracuseStep 1934339 = 2901509) B2901509
theorem B1451011 : Blo 1287962 1451011 := bstep (se 1 (by rfl) ⟨1088258, by rfl⟩ : syracuseStep 1451011 = 2176517) B2176517
theorem B1934369 : Blo 1287962 1934369 := bstep (se 2 (by rfl) ⟨725388, by rfl⟩ : syracuseStep 1934369 = 1450777) B1450777
theorem B4891697 : Blo 1287962 4891697 := bstep (se 2 (by rfl) ⟨1834386, by rfl⟩ : syracuseStep 4891697 = 3668773) B3668773
theorem B2901041 : Blo 1287962 2901041 := bstep (se 2 (by rfl) ⟨1087890, by rfl⟩ : syracuseStep 2901041 = 2175781) B2175781
theorem B1934387 : Blo 1287962 1934387 := bstep (se 1 (by rfl) ⟨1450790, by rfl⟩ : syracuseStep 1934387 = 2901581) B2901581
theorem B2901059 : Blo 1287962 2901059 := bstep (se 1 (by rfl) ⟨2175794, by rfl⟩ : syracuseStep 2901059 = 4351589) B4351589
theorem B9290821 : Blo 1287962 9290821 := bstep (se 4 (by rfl) ⟨871014, by rfl⟩ : syracuseStep 9290821 = 1742029) B1742029
theorem B14689349 : Blo 1287962 14689349 := bstep (se 4 (by rfl) ⟨1377126, by rfl⟩ : syracuseStep 14689349 = 2754253) B2754253
theorem B1934417 : Blo 1287962 1934417 := bstep (se 2 (by rfl) ⟨725406, by rfl⟩ : syracuseStep 1934417 = 1450813) B1450813
theorem B1934435 : Blo 1287962 1934435 := bstep (se 1 (by rfl) ⟨1450826, by rfl⟩ : syracuseStep 1934435 = 2901653) B2901653
theorem B3671153 : Blo 1287962 3671153 := bstep (se 2 (by rfl) ⟨1376682, by rfl⟩ : syracuseStep 3671153 = 2753365) B2753365
theorem B1959041 : Blo 1287962 1959041 := bstep (se 2 (by rfl) ⟨734640, by rfl⟩ : syracuseStep 1959041 = 1469281) B1469281
theorem B1934465 : Blo 1287962 1934465 := bstep (se 2 (by rfl) ⟨725424, by rfl⟩ : syracuseStep 1934465 = 1450849) B1450849
theorem B1934483 : Blo 1287962 1934483 := bstep (se 1 (by rfl) ⟨1450862, by rfl⟩ : syracuseStep 1934483 = 2901725) B2901725
theorem B1451155 : Blo 1287962 1451155 := bstep (se 1 (by rfl) ⟨1088366, by rfl⟩ : syracuseStep 1451155 = 2176733) B2176733
theorem B1377443 : Blo 1287962 1377443 := bstep (se 1 (by rfl) ⟨1033082, by rfl⟩ : syracuseStep 1377443 = 2066165) B2066165
theorem B3261617 : Blo 1287962 3261617 := bstep (se 2 (by rfl) ⟨1223106, by rfl⟩ : syracuseStep 3261617 = 2446213) B2446213
theorem B1836209 : Blo 1287962 1836209 := bstep (se 2 (by rfl) ⟨688578, by rfl⟩ : syracuseStep 1836209 = 1377157) B1377157
theorem B1934513 : Blo 1287962 1934513 := bstep (se 2 (by rfl) ⟨725442, by rfl⟩ : syracuseStep 1934513 = 1450885) B1450885
theorem B13935797 : Blo 1287962 13935797 := bstep (se 5 (by rfl) ⟨653240, by rfl⟩ : syracuseStep 13935797 = 1306481) B1306481
theorem B2065601 : Blo 1287962 2065601 := bstep (se 2 (by rfl) ⟨774600, by rfl⟩ : syracuseStep 2065601 = 1549201) B1549201
theorem B1934531 : Blo 1287962 1934531 := bstep (se 1 (by rfl) ⟨1450898, by rfl⟩ : syracuseStep 1934531 = 2901797) B2901797
theorem B1934561 : Blo 1287962 1934561 := bstep (se 2 (by rfl) ⟨725460, by rfl⟩ : syracuseStep 1934561 = 1450921) B1450921
theorem B3261667 : Blo 1287962 3261667 := bstep (se 1 (by rfl) ⟨2446250, by rfl⟩ : syracuseStep 3261667 = 4892501) B4892501
theorem B1934579 : Blo 1287962 1934579 := bstep (se 1 (by rfl) ⟨1450934, by rfl⟩ : syracuseStep 1934579 = 2901869) B2901869
theorem B1934609 : Blo 1287962 1934609 := bstep (se 2 (by rfl) ⟨725478, by rfl⟩ : syracuseStep 1934609 = 1450957) B1450957
theorem B1934627 : Blo 1287962 1934627 := bstep (se 1 (by rfl) ⟨1450970, by rfl⟩ : syracuseStep 1934627 = 2901941) B2901941
theorem B1934657 : Blo 1287962 1934657 := bstep (se 2 (by rfl) ⟨725496, by rfl⟩ : syracuseStep 1934657 = 1450993) B1450993
theorem B6530381 : Blo 1287962 6530381 := bstep (se 3 (by rfl) ⟨1224446, by rfl⟩ : syracuseStep 6530381 = 2448893) B2448893
theorem B2901329 : Blo 1287962 2901329 := bstep (se 2 (by rfl) ⟨1087998, by rfl⟩ : syracuseStep 2901329 = 2175997) B2175997
theorem B1934675 : Blo 1287962 1934675 := bstep (se 1 (by rfl) ⟨1451006, by rfl⟩ : syracuseStep 1934675 = 2902013) B2902013
theorem B2901347 : Blo 1287962 2901347 := bstep (se 1 (by rfl) ⟨2176010, by rfl⟩ : syracuseStep 2901347 = 4352021) B4352021
theorem B3261809 : Blo 1287962 3261809 := bstep (se 2 (by rfl) ⟨1223178, by rfl⟩ : syracuseStep 3261809 = 2446357) B2446357
theorem B1934705 : Blo 1287962 1934705 := bstep (se 2 (by rfl) ⟨725514, by rfl⟩ : syracuseStep 1934705 = 1451029) B1451029
theorem B1631603 : Blo 1287962 1631603 := bstep (se 1 (by rfl) ⟨1223702, by rfl⟩ : syracuseStep 1631603 = 2447405) B2447405
theorem B1934723 : Blo 1287962 1934723 := bstep (se 1 (by rfl) ⟨1451042, by rfl⟩ : syracuseStep 1934723 = 2902085) B2902085
theorem B4351373 : Blo 1287962 4351373 := bstep (se 3 (by rfl) ⟨815882, by rfl⟩ : syracuseStep 4351373 = 1631765) B1631765
theorem B1934753 : Blo 1287962 1934753 := bstep (se 2 (by rfl) ⟨725532, by rfl⟩ : syracuseStep 1934753 = 1451065) B1451065
theorem B1934771 : Blo 1287962 1934771 := bstep (se 1 (by rfl) ⟨1451078, by rfl⟩ : syracuseStep 1934771 = 2902157) B2902157
theorem B4351427 : Blo 1287962 4351427 := bstep (se 1 (by rfl) ⟨3263570, by rfl⟩ : syracuseStep 4351427 = 6527141) B6527141
theorem B1934801 : Blo 1287962 1934801 := bstep (se 2 (by rfl) ⟨725550, by rfl⟩ : syracuseStep 1934801 = 1451101) B1451101
theorem B1934819 : Blo 1287962 1934819 := bstep (se 1 (by rfl) ⟨1451114, by rfl⟩ : syracuseStep 1934819 = 2902229) B2902229
theorem B1934849 : Blo 1287962 1934849 := bstep (se 2 (by rfl) ⟨725568, by rfl⟩ : syracuseStep 1934849 = 1451137) B1451137
theorem B1934867 : Blo 1287962 1934867 := bstep (se 1 (by rfl) ⟨1451150, by rfl⟩ : syracuseStep 1934867 = 2902301) B2902301
theorem B35276309 : Blo 1287962 35276309 := bstep (se 6 (by rfl) ⟨826788, by rfl⟩ : syracuseStep 35276309 = 1653577) B1653577
theorem B2754083 : Blo 1287962 2754083 := bstep (se 1 (by rfl) ⟨2065562, by rfl⟩ : syracuseStep 2754083 = 4131125) B4131125
theorem B1934897 : Blo 1287962 1934897 := bstep (se 2 (by rfl) ⟨725586, by rfl⟩ : syracuseStep 1934897 = 1451173) B1451173
theorem B1934915 : Blo 1287962 1934915 := bstep (se 1 (by rfl) ⟨1451186, by rfl⟩ : syracuseStep 1934915 = 2902373) B2902373
theorem B8373829 : Blo 1287962 8373829 := bstep (se 4 (by rfl) ⟨785046, by rfl⟩ : syracuseStep 8373829 = 1570093) B1570093
theorem B2901617 : Blo 1287962 2901617 := bstep (se 2 (by rfl) ⟨1088106, by rfl⟩ : syracuseStep 2901617 = 2176213) B2176213
theorem B2901635 : Blo 1287962 2901635 := bstep (se 1 (by rfl) ⟨2176226, by rfl⟩ : syracuseStep 2901635 = 4352453) B4352453
theorem B4130509 : Blo 1287962 4130509 := bstep (se 3 (by rfl) ⟨774470, by rfl⟩ : syracuseStep 4130509 = 1548941) B1548941
theorem B4351697 : Blo 1287962 4351697 := bstep (se 2 (by rfl) ⟨1631886, by rfl⟩ : syracuseStep 4351697 = 3263773) B3263773
theorem B6612749 : Blo 1287962 6612749 := bstep (se 3 (by rfl) ⟨1239890, by rfl⟩ : syracuseStep 6612749 = 2479781) B2479781
theorem B1287971 : Blo 1287962 1287971 := bstep (se 1 (by rfl) ⟨965978, by rfl⟩ : syracuseStep 1287971 = 1931957) B1931957
theorem B1287987 : Blo 1287962 1287987 := bstep (se 1 (by rfl) ⟨965990, by rfl⟩ : syracuseStep 1287987 = 1931981) B1931981
theorem B1288003 : Blo 1287962 1288003 := bstep (se 1 (by rfl) ⟨966002, by rfl⟩ : syracuseStep 1288003 = 1932005) B1932005
theorem B1288019 : Blo 1287962 1288019 := bstep (se 1 (by rfl) ⟨966014, by rfl⟩ : syracuseStep 1288019 = 1932029) B1932029
theorem B1288035 : Blo 1287962 1288035 := bstep (se 1 (by rfl) ⟨966026, by rfl⟩ : syracuseStep 1288035 = 1932053) B1932053
theorem B1288051 : Blo 1287962 1288051 := bstep (se 1 (by rfl) ⟨966038, by rfl⟩ : syracuseStep 1288051 = 1932077) B1932077
theorem B1288067 : Blo 1287962 1288067 := bstep (se 1 (by rfl) ⟨966050, by rfl⟩ : syracuseStep 1288067 = 1932101) B1932101
theorem B11913101 : Blo 1287962 11913101 := bstep (se 3 (by rfl) ⟨2233706, by rfl⟩ : syracuseStep 11913101 = 4467413) B4467413
theorem B2901905 : Blo 1287962 2901905 := bstep (se 2 (by rfl) ⟨1088214, by rfl⟩ : syracuseStep 2901905 = 2176429) B2176429
theorem B1288083 : Blo 1287962 1288083 := bstep (se 1 (by rfl) ⟨966062, by rfl⟩ : syracuseStep 1288083 = 1932125) B1932125
theorem B1288099 : Blo 1287962 1288099 := bstep (se 1 (by rfl) ⟨966074, by rfl⟩ : syracuseStep 1288099 = 1932149) B1932149
theorem B2901923 : Blo 1287962 2901923 := bstep (se 1 (by rfl) ⟨2176442, by rfl⟩ : syracuseStep 2901923 = 4352885) B4352885
theorem B1288115 : Blo 1287962 1288115 := bstep (se 1 (by rfl) ⟨966086, by rfl⟩ : syracuseStep 1288115 = 1932173) B1932173
theorem B1288131 : Blo 1287962 1288131 := bstep (se 1 (by rfl) ⟨966098, by rfl⟩ : syracuseStep 1288131 = 1932197) B1932197
theorem B6195149 : Blo 1287962 6195149 := bstep (se 3 (by rfl) ⟨1161590, by rfl⟩ : syracuseStep 6195149 = 2323181) B2323181
theorem B4130765 : Blo 1287962 4130765 := bstep (se 3 (by rfl) ⟨774518, by rfl⟩ : syracuseStep 4130765 = 1549037) B1549037
theorem B1288147 : Blo 1287962 1288147 := bstep (se 1 (by rfl) ⟨966110, by rfl⟩ : syracuseStep 1288147 = 1932221) B1932221
theorem B1288163 : Blo 1287962 1288163 := bstep (se 1 (by rfl) ⟨966122, by rfl⟩ : syracuseStep 1288163 = 1932245) B1932245
theorem B2205667 : Blo 1287962 2205667 := bstep (se 1 (by rfl) ⟨1654250, by rfl⟩ : syracuseStep 2205667 = 3308501) B3308501
theorem B1288179 : Blo 1287962 1288179 := bstep (se 1 (by rfl) ⟨966134, by rfl⟩ : syracuseStep 1288179 = 1932269) B1932269
theorem B1288195 : Blo 1287962 1288195 := bstep (se 1 (by rfl) ⟨966146, by rfl⟩ : syracuseStep 1288195 = 1932293) B1932293
theorem B1288211 : Blo 1287962 1288211 := bstep (se 1 (by rfl) ⟨966158, by rfl⟩ : syracuseStep 1288211 = 1932317) B1932317
theorem B1288227 : Blo 1287962 1288227 := bstep (se 1 (by rfl) ⟨966170, by rfl⟩ : syracuseStep 1288227 = 1932341) B1932341
theorem B2754595 : Blo 1287962 2754595 := bstep (se 1 (by rfl) ⟨2065946, by rfl⟩ : syracuseStep 2754595 = 4131893) B4131893
theorem B6522929 : Blo 1287962 6522929 := bstep (se 2 (by rfl) ⟨2446098, by rfl⟩ : syracuseStep 6522929 = 4892197) B4892197
theorem B1288243 : Blo 1287962 1288243 := bstep (se 1 (by rfl) ⟨966182, by rfl⟩ : syracuseStep 1288243 = 1932365) B1932365
theorem B1632307 : Blo 1287962 1632307 := bstep (se 1 (by rfl) ⟨1224230, by rfl⟩ : syracuseStep 1632307 = 2448461) B2448461
theorem B1288259 : Blo 1287962 1288259 := bstep (se 1 (by rfl) ⟨966194, by rfl⟩ : syracuseStep 1288259 = 1932389) B1932389
theorem B1288275 : Blo 1287962 1288275 := bstep (se 1 (by rfl) ⟨966206, by rfl⟩ : syracuseStep 1288275 = 1932413) B1932413
theorem B1288291 : Blo 1287962 1288291 := bstep (se 1 (by rfl) ⟨966218, by rfl⟩ : syracuseStep 1288291 = 1932437) B1932437
theorem B1288307 : Blo 1287962 1288307 := bstep (se 1 (by rfl) ⟨966230, by rfl⟩ : syracuseStep 1288307 = 1932461) B1932461
theorem B1288323 : Blo 1287962 1288323 := bstep (se 1 (by rfl) ⟨966242, by rfl⟩ : syracuseStep 1288323 = 1932485) B1932485
theorem B1288339 : Blo 1287962 1288339 := bstep (se 1 (by rfl) ⟨966254, by rfl⟩ : syracuseStep 1288339 = 1932509) B1932509
theorem B1632403 : Blo 1287962 1632403 := bstep (se 1 (by rfl) ⟨1224302, by rfl⟩ : syracuseStep 1632403 = 2448605) B2448605
theorem B1288355 : Blo 1287962 1288355 := bstep (se 1 (by rfl) ⟨966266, by rfl⟩ : syracuseStep 1288355 = 1932533) B1932533
theorem B2902193 : Blo 1287962 2902193 := bstep (se 2 (by rfl) ⟨1088322, by rfl⟩ : syracuseStep 2902193 = 2176645) B2176645
theorem B1288371 : Blo 1287962 1288371 := bstep (se 1 (by rfl) ⟨966278, by rfl⟩ : syracuseStep 1288371 = 1932557) B1932557
theorem B1288387 : Blo 1287962 1288387 := bstep (se 1 (by rfl) ⟨966290, by rfl⟩ : syracuseStep 1288387 = 1932581) B1932581
theorem B2902211 : Blo 1287962 2902211 := bstep (se 1 (by rfl) ⟨2176658, by rfl⟩ : syracuseStep 2902211 = 4353317) B4353317
theorem B16517317 : Blo 1287962 16517317 := bstep (se 4 (by rfl) ⟨1548498, by rfl⟩ : syracuseStep 16517317 = 3096997) B3096997
theorem B1288403 : Blo 1287962 1288403 := bstep (se 1 (by rfl) ⟨966302, by rfl⟩ : syracuseStep 1288403 = 1932605) B1932605
theorem B7833827 : Blo 1287962 7833827 := bstep (se 1 (by rfl) ⟨5875370, by rfl⟩ : syracuseStep 7833827 = 11750741) B11750741
theorem B1288419 : Blo 1287962 1288419 := bstep (se 1 (by rfl) ⟨966314, by rfl⟩ : syracuseStep 1288419 = 1932629) B1932629
theorem B4352237 : Blo 1287962 4352237 := bstep (se 3 (by rfl) ⟨816044, by rfl⟩ : syracuseStep 4352237 = 1632089) B1632089
theorem B1288435 : Blo 1287962 1288435 := bstep (se 1 (by rfl) ⟨966326, by rfl⟩ : syracuseStep 1288435 = 1932653) B1932653
theorem B1288451 : Blo 1287962 1288451 := bstep (se 1 (by rfl) ⟨966338, by rfl⟩ : syracuseStep 1288451 = 1932677) B1932677
theorem B1288467 : Blo 1287962 1288467 := bstep (se 1 (by rfl) ⟨966350, by rfl⟩ : syracuseStep 1288467 = 1932701) B1932701
theorem B1288483 : Blo 1287962 1288483 := bstep (se 1 (by rfl) ⟨966362, by rfl⟩ : syracuseStep 1288483 = 1932725) B1932725
theorem B4352291 : Blo 1287962 4352291 := bstep (se 1 (by rfl) ⟨3264218, by rfl⟩ : syracuseStep 4352291 = 6528437) B6528437
theorem B8259889 : Blo 1287962 8259889 := bstep (se 2 (by rfl) ⟨3097458, by rfl⟩ : syracuseStep 8259889 = 6194917) B6194917
theorem B2206001 : Blo 1287962 2206001 := bstep (se 2 (by rfl) ⟨827250, by rfl⟩ : syracuseStep 2206001 = 1654501) B1654501
theorem B1288499 : Blo 1287962 1288499 := bstep (se 1 (by rfl) ⟨966374, by rfl⟩ : syracuseStep 1288499 = 1932749) B1932749
theorem B1288515 : Blo 1287962 1288515 := bstep (se 1 (by rfl) ⟨966386, by rfl⟩ : syracuseStep 1288515 = 1932773) B1932773
theorem B3262801 : Blo 1287962 3262801 := bstep (se 2 (by rfl) ⟨1223550, by rfl⟩ : syracuseStep 3262801 = 2447101) B2447101
theorem B1288531 : Blo 1287962 1288531 := bstep (se 1 (by rfl) ⟨966398, by rfl⟩ : syracuseStep 1288531 = 1932797) B1932797
theorem B1288547 : Blo 1287962 1288547 := bstep (se 1 (by rfl) ⟨966410, by rfl⟩ : syracuseStep 1288547 = 1932821) B1932821
theorem B9783665 : Blo 1287962 9783665 := bstep (se 2 (by rfl) ⟨3668874, by rfl⟩ : syracuseStep 9783665 = 7337749) B7337749
theorem B5581169 : Blo 1287962 5581169 := bstep (se 2 (by rfl) ⟨2092938, by rfl⟩ : syracuseStep 5581169 = 4185877) B4185877
theorem B1288563 : Blo 1287962 1288563 := bstep (se 1 (by rfl) ⟨966422, by rfl⟩ : syracuseStep 1288563 = 1932845) B1932845
theorem B1288579 : Blo 1287962 1288579 := bstep (se 1 (by rfl) ⟨966434, by rfl⟩ : syracuseStep 1288579 = 1932869) B1932869
theorem B1288595 : Blo 1287962 1288595 := bstep (se 1 (by rfl) ⟨966446, by rfl⟩ : syracuseStep 1288595 = 1932893) B1932893
theorem B1288611 : Blo 1287962 1288611 := bstep (se 1 (by rfl) ⟨966458, by rfl⟩ : syracuseStep 1288611 = 1932917) B1932917
theorem B1288627 : Blo 1287962 1288627 := bstep (se 1 (by rfl) ⟨966470, by rfl⟩ : syracuseStep 1288627 = 1932941) B1932941
theorem B1288643 : Blo 1287962 1288643 := bstep (se 1 (by rfl) ⟨966482, by rfl⟩ : syracuseStep 1288643 = 1932965) B1932965
theorem B1288659 : Blo 1287962 1288659 := bstep (se 1 (by rfl) ⟨966494, by rfl⟩ : syracuseStep 1288659 = 1932989) B1932989
theorem B1288675 : Blo 1287962 1288675 := bstep (se 1 (by rfl) ⟨966506, by rfl⟩ : syracuseStep 1288675 = 1933013) B1933013
theorem B4893155 : Blo 1287962 4893155 := bstep (se 1 (by rfl) ⟨3669866, by rfl⟩ : syracuseStep 4893155 = 7339733) B7339733
theorem B4893169 : Blo 1287962 4893169 := bstep (se 2 (by rfl) ⟨1834938, by rfl⟩ : syracuseStep 4893169 = 3669877) B3669877
theorem B14125553 : Blo 1287962 14125553 := bstep (se 2 (by rfl) ⟨5297082, by rfl⟩ : syracuseStep 14125553 = 10594165) B10594165
theorem B1288691 : Blo 1287962 1288691 := bstep (se 1 (by rfl) ⟨966518, by rfl⟩ : syracuseStep 1288691 = 1933037) B1933037
theorem B1288707 : Blo 1287962 1288707 := bstep (se 1 (by rfl) ⟨966530, by rfl⟩ : syracuseStep 1288707 = 1933061) B1933061
theorem B1960465 : Blo 1287962 1960465 := bstep (se 2 (by rfl) ⟨735174, by rfl⟩ : syracuseStep 1960465 = 1470349) B1470349
theorem B2173459 : Blo 1287962 2173459 := bstep (se 1 (by rfl) ⟨1630094, by rfl⟩ : syracuseStep 2173459 = 3260189) B3260189
theorem B1288723 : Blo 1287962 1288723 := bstep (se 1 (by rfl) ⟨966542, by rfl⟩ : syracuseStep 1288723 = 1933085) B1933085
theorem B1288739 : Blo 1287962 1288739 := bstep (se 1 (by rfl) ⟨966554, by rfl⟩ : syracuseStep 1288739 = 1933109) B1933109
theorem B3672611 : Blo 1287962 3672611 := bstep (se 1 (by rfl) ⟨2754458, by rfl⟩ : syracuseStep 3672611 = 5508917) B5508917
theorem B4352561 : Blo 1287962 4352561 := bstep (se 2 (by rfl) ⟨1632210, by rfl⟩ : syracuseStep 4352561 = 3264421) B3264421
theorem B1288755 : Blo 1287962 1288755 := bstep (se 1 (by rfl) ⟨966566, by rfl⟩ : syracuseStep 1288755 = 1933133) B1933133
theorem B1288771 : Blo 1287962 1288771 := bstep (se 1 (by rfl) ⟨966578, by rfl⟩ : syracuseStep 1288771 = 1933157) B1933157
theorem B1288787 : Blo 1287962 1288787 := bstep (se 1 (by rfl) ⟨966590, by rfl⟩ : syracuseStep 1288787 = 1933181) B1933181
theorem B1288803 : Blo 1287962 1288803 := bstep (se 1 (by rfl) ⟨966602, by rfl⟩ : syracuseStep 1288803 = 1933205) B1933205
theorem B3263075 : Blo 1287962 3263075 := bstep (se 1 (by rfl) ⟨2447306, by rfl⟩ : syracuseStep 3263075 = 4894613) B4894613
theorem B1288819 : Blo 1287962 1288819 := bstep (se 1 (by rfl) ⟨966614, by rfl⟩ : syracuseStep 1288819 = 1933229) B1933229
theorem B1288835 : Blo 1287962 1288835 := bstep (se 1 (by rfl) ⟨966626, by rfl⟩ : syracuseStep 1288835 = 1933253) B1933253
theorem B1288851 : Blo 1287962 1288851 := bstep (se 1 (by rfl) ⟨966638, by rfl⟩ : syracuseStep 1288851 = 1933277) B1933277
theorem B2173601 : Blo 1287962 2173601 := bstep (se 2 (by rfl) ⟨815100, by rfl⟩ : syracuseStep 2173601 = 1630201) B1630201
theorem B1288867 : Blo 1287962 1288867 := bstep (se 1 (by rfl) ⟨966650, by rfl⟩ : syracuseStep 1288867 = 1933301) B1933301
theorem B1288883 : Blo 1287962 1288883 := bstep (se 1 (by rfl) ⟨966662, by rfl⟩ : syracuseStep 1288883 = 1933325) B1933325
theorem B1288899 : Blo 1287962 1288899 := bstep (se 1 (by rfl) ⟨966674, by rfl⟩ : syracuseStep 1288899 = 1933349) B1933349
theorem B1288915 : Blo 1287962 1288915 := bstep (se 1 (by rfl) ⟨966686, by rfl⟩ : syracuseStep 1288915 = 1933373) B1933373
theorem B1288931 : Blo 1287962 1288931 := bstep (se 1 (by rfl) ⟨966698, by rfl⟩ : syracuseStep 1288931 = 1933397) B1933397
theorem B1469171 : Blo 1287962 1469171 := bstep (se 1 (by rfl) ⟨1101878, by rfl⟩ : syracuseStep 1469171 = 2203757) B2203757
theorem B1288947 : Blo 1287962 1288947 := bstep (se 1 (by rfl) ⟨966710, by rfl⟩ : syracuseStep 1288947 = 1933421) B1933421
theorem B1288963 : Blo 1287962 1288963 := bstep (se 1 (by rfl) ⟨966722, by rfl⟩ : syracuseStep 1288963 = 1933445) B1933445
theorem B1288979 : Blo 1287962 1288979 := bstep (se 1 (by rfl) ⟨966734, by rfl⟩ : syracuseStep 1288979 = 1933469) B1933469
theorem B2173729 : Blo 1287962 2173729 := bstep (se 2 (by rfl) ⟨815148, by rfl⟩ : syracuseStep 2173729 = 1630297) B1630297
theorem B1288995 : Blo 1287962 1288995 := bstep (se 1 (by rfl) ⟨966746, by rfl⟩ : syracuseStep 1288995 = 1933493) B1933493
theorem B3263267 : Blo 1287962 3263267 := bstep (se 1 (by rfl) ⟨2447450, by rfl⟩ : syracuseStep 3263267 = 4894901) B4894901
theorem B3353393 : Blo 1287962 3353393 := bstep (se 2 (by rfl) ⟨1257522, by rfl⟩ : syracuseStep 3353393 = 2515045) B2515045
theorem B1289011 : Blo 1287962 1289011 := bstep (se 1 (by rfl) ⟨966758, by rfl⟩ : syracuseStep 1289011 = 1933517) B1933517
theorem B2173763 : Blo 1287962 2173763 := bstep (se 1 (by rfl) ⟨1630322, by rfl⟩ : syracuseStep 2173763 = 3260645) B3260645
theorem B1289027 : Blo 1287962 1289027 := bstep (se 1 (by rfl) ⟨966770, by rfl⟩ : syracuseStep 1289027 = 1933541) B1933541
theorem B1289043 : Blo 1287962 1289043 := bstep (se 1 (by rfl) ⟨966782, by rfl⟩ : syracuseStep 1289043 = 1933565) B1933565
theorem B1289059 : Blo 1287962 1289059 := bstep (se 1 (by rfl) ⟨966794, by rfl⟩ : syracuseStep 1289059 = 1933589) B1933589
theorem B12389219 : Blo 1287962 12389219 := bstep (se 1 (by rfl) ⟨9291914, by rfl⟩ : syracuseStep 12389219 = 18583829) B18583829
theorem B1289075 : Blo 1287962 1289075 := bstep (se 1 (by rfl) ⟨966806, by rfl⟩ : syracuseStep 1289075 = 1933613) B1933613
theorem B1289091 : Blo 1287962 1289091 := bstep (se 1 (by rfl) ⟨966818, by rfl⟩ : syracuseStep 1289091 = 1933637) B1933637
theorem B1289107 : Blo 1287962 1289107 := bstep (se 1 (by rfl) ⟨966830, by rfl⟩ : syracuseStep 1289107 = 1933661) B1933661
theorem B1289123 : Blo 1287962 1289123 := bstep (se 1 (by rfl) ⟨966842, by rfl⟩ : syracuseStep 1289123 = 1933685) B1933685
theorem B3484579 : Blo 1287962 3484579 := bstep (se 1 (by rfl) ⟨2613434, by rfl⟩ : syracuseStep 3484579 = 5226869) B5226869
theorem B1289139 : Blo 1287962 1289139 := bstep (se 1 (by rfl) ⟨966854, by rfl⟩ : syracuseStep 1289139 = 1933709) B1933709
theorem B2173891 : Blo 1287962 2173891 := bstep (se 1 (by rfl) ⟨1630418, by rfl⟩ : syracuseStep 2173891 = 3260837) B3260837
theorem B1289155 : Blo 1287962 1289155 := bstep (se 1 (by rfl) ⟨966866, by rfl⟩ : syracuseStep 1289155 = 1933733) B1933733
theorem B1289171 : Blo 1287962 1289171 := bstep (se 1 (by rfl) ⟨966878, by rfl⟩ : syracuseStep 1289171 = 1933757) B1933757
theorem B1289187 : Blo 1287962 1289187 := bstep (se 1 (by rfl) ⟨966890, by rfl⟩ : syracuseStep 1289187 = 1933781) B1933781
theorem B1289203 : Blo 1287962 1289203 := bstep (se 1 (by rfl) ⟨966902, by rfl⟩ : syracuseStep 1289203 = 1933805) B1933805
theorem B1289219 : Blo 1287962 1289219 := bstep (se 1 (by rfl) ⟨966914, by rfl⟩ : syracuseStep 1289219 = 1933829) B1933829
theorem B3722257 : Blo 1287962 3722257 := bstep (se 2 (by rfl) ⟨1395846, by rfl⟩ : syracuseStep 3722257 = 2791693) B2791693
theorem B1289235 : Blo 1287962 1289235 := bstep (se 1 (by rfl) ⟨966926, by rfl⟩ : syracuseStep 1289235 = 1933853) B1933853
theorem B1289251 : Blo 1287962 1289251 := bstep (se 1 (by rfl) ⟨966938, by rfl⟩ : syracuseStep 1289251 = 1933877) B1933877
theorem B1289267 : Blo 1287962 1289267 := bstep (se 1 (by rfl) ⟨966950, by rfl⟩ : syracuseStep 1289267 = 1933901) B1933901
theorem B1289283 : Blo 1287962 1289283 := bstep (se 1 (by rfl) ⟨966962, by rfl⟩ : syracuseStep 1289283 = 1933925) B1933925
theorem B4353101 : Blo 1287962 4353101 := bstep (se 3 (by rfl) ⟨816206, by rfl⟩ : syracuseStep 4353101 = 1632413) B1632413
theorem B2174033 : Blo 1287962 2174033 := bstep (se 2 (by rfl) ⟨815262, by rfl⟩ : syracuseStep 2174033 = 1630525) B1630525
theorem B1289299 : Blo 1287962 1289299 := bstep (se 1 (by rfl) ⟨966974, by rfl⟩ : syracuseStep 1289299 = 1933949) B1933949
theorem B1289315 : Blo 1287962 1289315 := bstep (se 1 (by rfl) ⟨966986, by rfl⟩ : syracuseStep 1289315 = 1933973) B1933973
theorem B1289331 : Blo 1287962 1289331 := bstep (se 1 (by rfl) ⟨966998, by rfl⟩ : syracuseStep 1289331 = 1933997) B1933997
theorem B1289347 : Blo 1287962 1289347 := bstep (se 1 (by rfl) ⟨967010, by rfl⟩ : syracuseStep 1289347 = 1934021) B1934021
theorem B4353155 : Blo 1287962 4353155 := bstep (se 1 (by rfl) ⟨3264866, by rfl⟩ : syracuseStep 4353155 = 6529733) B6529733
theorem B1289363 : Blo 1287962 1289363 := bstep (se 1 (by rfl) ⟨967022, by rfl⟩ : syracuseStep 1289363 = 1934045) B1934045
theorem B1289379 : Blo 1287962 1289379 := bstep (se 1 (by rfl) ⟨967034, by rfl⟩ : syracuseStep 1289379 = 1934069) B1934069
theorem B1289395 : Blo 1287962 1289395 := bstep (se 1 (by rfl) ⟨967046, by rfl⟩ : syracuseStep 1289395 = 1934093) B1934093
theorem B1289411 : Blo 1287962 1289411 := bstep (se 1 (by rfl) ⟨967058, by rfl⟩ : syracuseStep 1289411 = 1934117) B1934117
theorem B2174161 : Blo 1287962 2174161 := bstep (se 2 (by rfl) ⟨815310, by rfl⟩ : syracuseStep 2174161 = 1630621) B1630621
theorem B1289427 : Blo 1287962 1289427 := bstep (se 1 (by rfl) ⟨967070, by rfl⟩ : syracuseStep 1289427 = 1934141) B1934141
theorem B1289443 : Blo 1287962 1289443 := bstep (se 1 (by rfl) ⟨967082, by rfl⟩ : syracuseStep 1289443 = 1934165) B1934165
theorem B2174195 : Blo 1287962 2174195 := bstep (se 1 (by rfl) ⟨1630646, by rfl⟩ : syracuseStep 2174195 = 3261293) B3261293
theorem B1289459 : Blo 1287962 1289459 := bstep (se 1 (by rfl) ⟨967094, by rfl⟩ : syracuseStep 1289459 = 1934189) B1934189
theorem B1289475 : Blo 1287962 1289475 := bstep (se 1 (by rfl) ⟨967106, by rfl⟩ : syracuseStep 1289475 = 1934213) B1934213
theorem B9293069 : Blo 1287962 9293069 := bstep (se 3 (by rfl) ⟨1742450, by rfl⟩ : syracuseStep 9293069 = 3484901) B3484901
theorem B1289491 : Blo 1287962 1289491 := bstep (se 1 (by rfl) ⟨967118, by rfl⟩ : syracuseStep 1289491 = 1934237) B1934237
theorem B1289507 : Blo 1287962 1289507 := bstep (se 1 (by rfl) ⟨967130, by rfl⟩ : syracuseStep 1289507 = 1934261) B1934261
theorem B1289523 : Blo 1287962 1289523 := bstep (se 1 (by rfl) ⟨967142, by rfl⟩ : syracuseStep 1289523 = 1934285) B1934285
theorem B1289539 : Blo 1287962 1289539 := bstep (se 1 (by rfl) ⟨967154, by rfl⟩ : syracuseStep 1289539 = 1934309) B1934309
theorem B1289555 : Blo 1287962 1289555 := bstep (se 1 (by rfl) ⟨967166, by rfl⟩ : syracuseStep 1289555 = 1934333) B1934333
theorem B1289571 : Blo 1287962 1289571 := bstep (se 1 (by rfl) ⟨967178, by rfl⟩ : syracuseStep 1289571 = 1934357) B1934357
theorem B22310257 : Blo 1287962 22310257 := bstep (se 2 (by rfl) ⟨8366346, by rfl⟩ : syracuseStep 22310257 = 16732693) B16732693
theorem B2174323 : Blo 1287962 2174323 := bstep (se 1 (by rfl) ⟨1630742, by rfl⟩ : syracuseStep 2174323 = 3261485) B3261485
theorem B1289587 : Blo 1287962 1289587 := bstep (se 1 (by rfl) ⟨967190, by rfl⟩ : syracuseStep 1289587 = 1934381) B1934381
theorem B1289603 : Blo 1287962 1289603 := bstep (se 1 (by rfl) ⟨967202, by rfl⟩ : syracuseStep 1289603 = 1934405) B1934405
theorem B4353425 : Blo 1287962 4353425 := bstep (se 2 (by rfl) ⟨1632534, by rfl⟩ : syracuseStep 4353425 = 3265069) B3265069
theorem B1289619 : Blo 1287962 1289619 := bstep (se 1 (by rfl) ⟨967214, by rfl⟩ : syracuseStep 1289619 = 1934429) B1934429
theorem B4410787 : Blo 1287962 4410787 := bstep (se 1 (by rfl) ⟨3308090, by rfl⟩ : syracuseStep 4410787 = 6616181) B6616181
theorem B1289635 : Blo 1287962 1289635 := bstep (se 1 (by rfl) ⟨967226, by rfl⟩ : syracuseStep 1289635 = 1934453) B1934453
theorem B1289651 : Blo 1287962 1289651 := bstep (se 1 (by rfl) ⟨967238, by rfl⟩ : syracuseStep 1289651 = 1934477) B1934477
theorem B1289667 : Blo 1287962 1289667 := bstep (se 1 (by rfl) ⟨967250, by rfl⟩ : syracuseStep 1289667 = 1934501) B1934501
theorem B4132291 : Blo 1287962 4132291 := bstep (se 1 (by rfl) ⟨3099218, by rfl⟩ : syracuseStep 4132291 = 6198437) B6198437
theorem B1289683 : Blo 1287962 1289683 := bstep (se 1 (by rfl) ⟨967262, by rfl⟩ : syracuseStep 1289683 = 1934525) B1934525
theorem B6524387 : Blo 1287962 6524387 := bstep (se 1 (by rfl) ⟨4893290, by rfl⟩ : syracuseStep 6524387 = 9786581) B9786581
theorem B1289699 : Blo 1287962 1289699 := bstep (se 1 (by rfl) ⟨967274, by rfl⟩ : syracuseStep 1289699 = 1934549) B1934549
theorem B1289715 : Blo 1287962 1289715 := bstep (se 1 (by rfl) ⟨967286, by rfl⟩ : syracuseStep 1289715 = 1934573) B1934573
theorem B2174465 : Blo 1287962 2174465 := bstep (se 2 (by rfl) ⟨815424, by rfl⟩ : syracuseStep 2174465 = 1630849) B1630849
theorem B1289731 : Blo 1287962 1289731 := bstep (se 1 (by rfl) ⟨967298, by rfl⟩ : syracuseStep 1289731 = 1934597) B1934597
theorem B3919373 : Blo 1287962 3919373 := bstep (se 3 (by rfl) ⟨734882, by rfl⟩ : syracuseStep 3919373 = 1469765) B1469765
theorem B1289747 : Blo 1287962 1289747 := bstep (se 1 (by rfl) ⟨967310, by rfl⟩ : syracuseStep 1289747 = 1934621) B1934621
theorem B5508643 : Blo 1287962 5508643 := bstep (se 1 (by rfl) ⟨4131482, by rfl⟩ : syracuseStep 5508643 = 8262965) B8262965
theorem B1289763 : Blo 1287962 1289763 := bstep (se 1 (by rfl) ⟨967322, by rfl⟩ : syracuseStep 1289763 = 1934645) B1934645
theorem B1289779 : Blo 1287962 1289779 := bstep (se 1 (by rfl) ⟨967334, by rfl⟩ : syracuseStep 1289779 = 1934669) B1934669
theorem B1289795 : Blo 1287962 1289795 := bstep (se 1 (by rfl) ⟨967346, by rfl⟩ : syracuseStep 1289795 = 1934693) B1934693
theorem B1289811 : Blo 1287962 1289811 := bstep (se 1 (by rfl) ⟨967358, by rfl⟩ : syracuseStep 1289811 = 1934717) B1934717
theorem B1289827 : Blo 1287962 1289827 := bstep (se 1 (by rfl) ⟨967370, by rfl⟩ : syracuseStep 1289827 = 1934741) B1934741
theorem B1289843 : Blo 1287962 1289843 := bstep (se 1 (by rfl) ⟨967382, by rfl⟩ : syracuseStep 1289843 = 1934765) B1934765
theorem B2174593 : Blo 1287962 2174593 := bstep (se 2 (by rfl) ⟨815472, by rfl⟩ : syracuseStep 2174593 = 1630945) B1630945
theorem B1289859 : Blo 1287962 1289859 := bstep (se 1 (by rfl) ⟨967394, by rfl⟩ : syracuseStep 1289859 = 1934789) B1934789
theorem B1289875 : Blo 1287962 1289875 := bstep (se 1 (by rfl) ⟨967406, by rfl⟩ : syracuseStep 1289875 = 1934813) B1934813
theorem B2174627 : Blo 1287962 2174627 := bstep (se 1 (by rfl) ⟨1630970, by rfl⟩ : syracuseStep 2174627 = 3261941) B3261941
theorem B2649763 : Blo 1287962 2649763 := bstep (se 1 (by rfl) ⟨1987322, by rfl⟩ : syracuseStep 2649763 = 3974645) B3974645
theorem B1289891 : Blo 1287962 1289891 := bstep (se 1 (by rfl) ⟨967418, by rfl⟩ : syracuseStep 1289891 = 1934837) B1934837
theorem B1289907 : Blo 1287962 1289907 := bstep (se 1 (by rfl) ⟨967430, by rfl⟩ : syracuseStep 1289907 = 1934861) B1934861
theorem B1289923 : Blo 1287962 1289923 := bstep (se 1 (by rfl) ⟨967442, by rfl⟩ : syracuseStep 1289923 = 1934885) B1934885
theorem B3264209 : Blo 1287962 3264209 := bstep (se 2 (by rfl) ⟨1224078, by rfl⟩ : syracuseStep 3264209 = 2448157) B2448157
theorem B1289939 : Blo 1287962 1289939 := bstep (se 1 (by rfl) ⟨967454, by rfl⟩ : syracuseStep 1289939 = 1934909) B1934909
theorem B1289955 : Blo 1287962 1289955 := bstep (se 1 (by rfl) ⟨967466, by rfl⟩ : syracuseStep 1289955 = 1934933) B1934933
theorem B3485443 : Blo 1287962 3485443 := bstep (se 1 (by rfl) ⟨2614082, by rfl⟩ : syracuseStep 3485443 = 5228165) B5228165
theorem B3264259 : Blo 1287962 3264259 := bstep (se 1 (by rfl) ⟨2448194, by rfl⟩ : syracuseStep 3264259 = 4896389) B4896389
theorem B2174755 : Blo 1287962 2174755 := bstep (se 1 (by rfl) ⟨1631066, by rfl⟩ : syracuseStep 2174755 = 3262133) B3262133
theorem B7843661 : Blo 1287962 7843661 := bstep (se 3 (by rfl) ⟨1470686, by rfl⟩ : syracuseStep 7843661 = 2941373) B2941373
theorem B6279011 : Blo 1287962 6279011 := bstep (se 1 (by rfl) ⟨4709258, by rfl⟩ : syracuseStep 6279011 = 9418517) B9418517
theorem B3264401 : Blo 1287962 3264401 := bstep (se 2 (by rfl) ⟨1224150, by rfl⟩ : syracuseStep 3264401 = 2448301) B2448301
theorem B4894627 : Blo 1287962 4894627 := bstep (se 1 (by rfl) ⟨3670970, by rfl⟩ : syracuseStep 4894627 = 7341941) B7341941
theorem B2174897 : Blo 1287962 2174897 := bstep (se 2 (by rfl) ⟨815586, by rfl⟩ : syracuseStep 2174897 = 1631173) B1631173
theorem B1306579 : Blo 1287962 1306579 := bstep (se 1 (by rfl) ⟨979934, by rfl⟩ : syracuseStep 1306579 = 1959869) B1959869
theorem B2175025 : Blo 1287962 2175025 := bstep (se 2 (by rfl) ⟨815634, by rfl⟩ : syracuseStep 2175025 = 1631269) B1631269
theorem B4411441 : Blo 1287962 4411441 := bstep (se 2 (by rfl) ⟨1654290, by rfl⟩ : syracuseStep 4411441 = 3308581) B3308581
theorem B2175059 : Blo 1287962 2175059 := bstep (se 1 (by rfl) ⟨1631294, by rfl⟩ : syracuseStep 2175059 = 3262589) B3262589
theorem B2175187 : Blo 1287962 2175187 := bstep (se 1 (by rfl) ⟨1631390, by rfl⟩ : syracuseStep 2175187 = 3262781) B3262781
theorem B6525197 : Blo 1287962 6525197 := bstep (se 3 (by rfl) ⟨1223474, by rfl⟩ : syracuseStep 6525197 = 2446949) B2446949
theorem B2175329 : Blo 1287962 2175329 := bstep (se 2 (by rfl) ⟨815748, by rfl⟩ : syracuseStep 2175329 = 1631497) B1631497
theorem B7336291 : Blo 1287962 7336291 := bstep (se 1 (by rfl) ⟨5502218, by rfl⟩ : syracuseStep 7336291 = 11004437) B11004437
theorem B3305873 : Blo 1287962 3305873 := bstep (se 2 (by rfl) ⟨1239702, by rfl⟩ : syracuseStep 3305873 = 2479405) B2479405
theorem B1323427 : Blo 1287962 1323427 := bstep (se 1 (by rfl) ⟨992570, by rfl⟩ : syracuseStep 1323427 = 1985141) B1985141
theorem B2175457 : Blo 1287962 2175457 := bstep (se 2 (by rfl) ⟨815796, by rfl⟩ : syracuseStep 2175457 = 1631593) B1631593
theorem B2175491 : Blo 1287962 2175491 := bstep (se 1 (by rfl) ⟨1631618, by rfl⟩ : syracuseStep 2175491 = 3263237) B3263237
theorem B47657585 : Blo 1287962 47657585 := bstep (se 2 (by rfl) ⟨17871594, by rfl⟩ : syracuseStep 47657585 = 35743189) B35743189
theorem B2175619 : Blo 1287962 2175619 := bstep (se 1 (by rfl) ⟨1631714, by rfl⟩ : syracuseStep 2175619 = 3263429) B3263429
theorem B5509873 : Blo 1287962 5509873 := bstep (se 2 (by rfl) ⟨2066202, by rfl⟩ : syracuseStep 5509873 = 4132405) B4132405
theorem B2175761 : Blo 1287962 2175761 := bstep (se 2 (by rfl) ⟨815910, by rfl⟩ : syracuseStep 2175761 = 1631821) B1631821
theorem B2446129 : Blo 1287962 2446129 := bstep (se 2 (by rfl) ⟨917298, by rfl⟩ : syracuseStep 2446129 = 1834597) B1834597
theorem B2356049 : Blo 1287962 2356049 := bstep (se 2 (by rfl) ⟨883518, by rfl⟩ : syracuseStep 2356049 = 1767037) B1767037
theorem B7336817 : Blo 1287962 7336817 := bstep (se 2 (by rfl) ⟨2751306, by rfl⟩ : syracuseStep 7336817 = 5502613) B5502613
theorem B2175889 : Blo 1287962 2175889 := bstep (se 2 (by rfl) ⟨815958, by rfl⟩ : syracuseStep 2175889 = 1631917) B1631917
theorem B2266003 : Blo 1287962 2266003 := bstep (se 1 (by rfl) ⟨1699502, by rfl⟩ : syracuseStep 2266003 = 3399005) B3399005
theorem B6968227 : Blo 1287962 6968227 := bstep (se 1 (by rfl) ⟨5226170, by rfl⟩ : syracuseStep 6968227 = 10452341) B10452341
theorem B2175923 : Blo 1287962 2175923 := bstep (se 1 (by rfl) ⟨1631942, by rfl⟩ : syracuseStep 2175923 = 3263885) B3263885
theorem B4412387 : Blo 1287962 4412387 := bstep (se 1 (by rfl) ⟨3309290, by rfl⟩ : syracuseStep 4412387 = 6618581) B6618581
theorem B2176051 : Blo 1287962 2176051 := bstep (se 1 (by rfl) ⟨1632038, by rfl⟩ : syracuseStep 2176051 = 3264077) B3264077
theorem B7066693 : Blo 1287962 7066693 := bstep (se 4 (by rfl) ⟨662502, by rfl⟩ : syracuseStep 7066693 = 1325005) B1325005
theorem B4347053 : Blo 1287962 4347053 := bstep (se 3 (by rfl) ⟨815072, by rfl⟩ : syracuseStep 4347053 = 1630145) B1630145
theorem B2176193 : Blo 1287962 2176193 := bstep (se 2 (by rfl) ⟨816072, by rfl⟩ : syracuseStep 2176193 = 1632145) B1632145
theorem B4347107 : Blo 1287962 4347107 := bstep (se 1 (by rfl) ⟨3260330, by rfl⟩ : syracuseStep 4347107 = 6520661) B6520661
theorem B2176321 : Blo 1287962 2176321 := bstep (se 2 (by rfl) ⟨816120, by rfl⟩ : syracuseStep 2176321 = 1632241) B1632241
theorem B2176355 : Blo 1287962 2176355 := bstep (se 1 (by rfl) ⟨1632266, by rfl⟩ : syracuseStep 2176355 = 3264533) B3264533
theorem B10458467 : Blo 1287962 10458467 := bstep (se 1 (by rfl) ⟨7843850, by rfl⟩ : syracuseStep 10458467 = 15687701) B15687701
theorem B1987939 : Blo 1287962 1987939 := bstep (se 1 (by rfl) ⟨1490954, by rfl⟩ : syracuseStep 1987939 = 2981909) B2981909
theorem B4642211 : Blo 1287962 4642211 := bstep (se 1 (by rfl) ⟨3481658, by rfl⟩ : syracuseStep 4642211 = 6963317) B6963317
theorem B6616525 : Blo 1287962 6616525 := bstep (se 3 (by rfl) ⟨1240598, by rfl⟩ : syracuseStep 6616525 = 2481197) B2481197
theorem B11752931 : Blo 1287962 11752931 := bstep (se 1 (by rfl) ⟨8814698, by rfl⟩ : syracuseStep 11752931 = 17629397) B17629397
theorem B2176483 : Blo 1287962 2176483 := bstep (se 1 (by rfl) ⟨1632362, by rfl⟩ : syracuseStep 2176483 = 3264725) B3264725
theorem B4347377 : Blo 1287962 4347377 := bstep (se 2 (by rfl) ⟨1630266, by rfl⟩ : syracuseStep 4347377 = 3260533) B3260533
theorem B2176625 : Blo 1287962 2176625 := bstep (se 2 (by rfl) ⟨816234, by rfl⟩ : syracuseStep 2176625 = 1632469) B1632469
theorem B19854989 : Blo 1287962 19854989 := bstep (se 3 (by rfl) ⟨3722810, by rfl⟩ : syracuseStep 19854989 = 7445621) B7445621
theorem B14677685 : Blo 1287962 14677685 := bstep (se 5 (by rfl) ⟨688016, by rfl⟩ : syracuseStep 14677685 = 1376033) B1376033
theorem B14874353 : Blo 1287962 14874353 := bstep (se 2 (by rfl) ⟨5577882, by rfl⟩ : syracuseStep 14874353 = 11155765) B11155765
theorem B2176753 : Blo 1287962 2176753 := bstep (se 2 (by rfl) ⟨816282, by rfl⟩ : syracuseStep 2176753 = 1632565) B1632565
theorem B2176787 : Blo 1287962 2176787 := bstep (se 1 (by rfl) ⟨1632590, by rfl⟩ : syracuseStep 2176787 = 3265181) B3265181
theorem B5879587 : Blo 1287962 5879587 := bstep (se 1 (by rfl) ⟨4409690, by rfl⟩ : syracuseStep 5879587 = 8819381) B8819381
theorem B7345997 : Blo 1287962 7345997 := bstep (se 3 (by rfl) ⟨1377374, by rfl⟩ : syracuseStep 7345997 = 2754749) B2754749
theorem B2447185 : Blo 1287962 2447185 := bstep (se 2 (by rfl) ⟨917694, by rfl⟩ : syracuseStep 2447185 = 1835389) B1835389
theorem B7255921 : Blo 1287962 7255921 := bstep (se 2 (by rfl) ⟨2720970, by rfl⟩ : syracuseStep 7255921 = 5441941) B5441941
theorem B1742753 : Blo 1287962 1742753 := bstep (se 2 (by rfl) ⟨653532, by rfl⟩ : syracuseStep 1742753 = 1307065) B1307065
theorem B4347917 : Blo 1287962 4347917 := bstep (se 3 (by rfl) ⟨815234, by rfl⟩ : syracuseStep 4347917 = 1630469) B1630469
theorem B4347971 : Blo 1287962 4347971 := bstep (se 1 (by rfl) ⟨3260978, by rfl⟩ : syracuseStep 4347971 = 6521957) B6521957
theorem B4896845 : Blo 1287962 4896845 := bstep (se 3 (by rfl) ⟨918158, by rfl⟩ : syracuseStep 4896845 = 1836317) B1836317
theorem B928225493 : Blo 1287962 928225493 := bstep (se 7 (by rfl) ⟨10877642, by rfl⟩ : syracuseStep 928225493 = 21755285) B21755285
theorem B2447587 : Blo 1287962 2447587 := bstep (se 1 (by rfl) ⟨1835690, by rfl⟩ : syracuseStep 2447587 = 3671381) B3671381
theorem B2898161 : Blo 1287962 2898161 := bstep (se 2 (by rfl) ⟨1086810, by rfl⟩ : syracuseStep 2898161 = 2173621) B2173621
theorem B2898179 : Blo 1287962 2898179 := bstep (se 1 (by rfl) ⟨2173634, by rfl⟩ : syracuseStep 2898179 = 4347269) B4347269
theorem B3668237 : Blo 1287962 3668237 := bstep (se 3 (by rfl) ⟨687794, by rfl⟩ : syracuseStep 3668237 = 1375589) B1375589
theorem B2447633 : Blo 1287962 2447633 := bstep (se 2 (by rfl) ⟨917862, by rfl⟩ : syracuseStep 2447633 = 1835725) B1835725
theorem B7338275 : Blo 1287962 7338275 := bstep (se 1 (by rfl) ⟨5503706, by rfl⟩ : syracuseStep 7338275 = 11007413) B11007413
theorem B4348241 : Blo 1287962 4348241 := bstep (se 2 (by rfl) ⟨1630590, by rfl⟩ : syracuseStep 4348241 = 3261181) B3261181
theorem B4127075 : Blo 1287962 4127075 := bstep (se 1 (by rfl) ⟨3095306, by rfl⟩ : syracuseStep 4127075 = 6190613) B6190613
theorem B7059811 : Blo 1287962 7059811 := bstep (se 1 (by rfl) ⟨5294858, by rfl⟩ : syracuseStep 7059811 = 10589717) B10589717
theorem B8255843 : Blo 1287962 8255843 := bstep (se 1 (by rfl) ⟨6191882, by rfl⟩ : syracuseStep 8255843 = 12383765) B12383765
theorem B8821133 : Blo 1287962 8821133 := bstep (se 3 (by rfl) ⟨1653962, by rfl⟩ : syracuseStep 8821133 = 3307925) B3307925
theorem B2750897 : Blo 1287962 2750897 := bstep (se 2 (by rfl) ⟨1031586, by rfl⟩ : syracuseStep 2750897 = 2063173) B2063173
theorem B3668419 : Blo 1287962 3668419 := bstep (se 1 (by rfl) ⟨2751314, by rfl⟩ : syracuseStep 3668419 = 5502629) B5502629
theorem B4127203 : Blo 1287962 4127203 := bstep (se 1 (by rfl) ⟨3095402, by rfl⟩ : syracuseStep 4127203 = 6190805) B6190805
theorem B3668465 : Blo 1287962 3668465 := bstep (se 2 (by rfl) ⟨1375674, by rfl⟩ : syracuseStep 3668465 = 2751349) B2751349
theorem B3578381 : Blo 1287962 3578381 := bstep (se 3 (by rfl) ⟨670946, by rfl⟩ : syracuseStep 3578381 = 1341893) B1341893
theorem B2898449 : Blo 1287962 2898449 := bstep (se 2 (by rfl) ⟨1086918, by rfl⟩ : syracuseStep 2898449 = 2173837) B2173837
theorem B2898467 : Blo 1287962 2898467 := bstep (se 1 (by rfl) ⟨2173850, by rfl⟩ : syracuseStep 2898467 = 4347701) B4347701
theorem B2447921 : Blo 1287962 2447921 := bstep (se 2 (by rfl) ⟨917970, by rfl⟩ : syracuseStep 2447921 = 1835941) B1835941
theorem B25107085 : Blo 1287962 25107085 := bstep (se 3 (by rfl) ⟨4707578, by rfl⟩ : syracuseStep 25107085 = 9415157) B9415157
theorem B1931969 : Blo 1287962 1931969 := bstep (se 2 (by rfl) ⟨724488, by rfl⟩ : syracuseStep 1931969 = 1448977) B1448977
theorem B1931987 : Blo 1287962 1931987 := bstep (se 1 (by rfl) ⟨1448990, by rfl⟩ : syracuseStep 1931987 = 2897981) B2897981
theorem B1932017 : Blo 1287962 1932017 := bstep (se 2 (by rfl) ⟨724506, by rfl⟩ : syracuseStep 1932017 = 1449013) B1449013
theorem B1932035 : Blo 1287962 1932035 := bstep (se 1 (by rfl) ⟨1449026, by rfl⟩ : syracuseStep 1932035 = 2898053) B2898053
theorem B1932065 : Blo 1287962 1932065 := bstep (se 2 (by rfl) ⟨724524, by rfl⟩ : syracuseStep 1932065 = 1449049) B1449049
theorem B2898737 : Blo 1287962 2898737 := bstep (se 2 (by rfl) ⟨1087026, by rfl⟩ : syracuseStep 2898737 = 2174053) B2174053
theorem B4127537 : Blo 1287962 4127537 := bstep (se 2 (by rfl) ⟨1547826, by rfl⟩ : syracuseStep 4127537 = 3095653) B3095653
theorem B1932083 : Blo 1287962 1932083 := bstep (se 1 (by rfl) ⟨1449062, by rfl⟩ : syracuseStep 1932083 = 2898125) B2898125
theorem B2898755 : Blo 1287962 2898755 := bstep (se 1 (by rfl) ⟨2174066, by rfl⟩ : syracuseStep 2898755 = 4348133) B4348133
theorem B1932113 : Blo 1287962 1932113 := bstep (se 2 (by rfl) ⟨724542, by rfl⟩ : syracuseStep 1932113 = 1449085) B1449085
theorem B1932131 : Blo 1287962 1932131 := bstep (se 1 (by rfl) ⟨1449098, by rfl⟩ : syracuseStep 1932131 = 2898197) B2898197
theorem B4348781 : Blo 1287962 4348781 := bstep (se 3 (by rfl) ⟨815396, by rfl⟩ : syracuseStep 4348781 = 1630793) B1630793
theorem B1932161 : Blo 1287962 1932161 := bstep (se 2 (by rfl) ⟨724560, by rfl⟩ : syracuseStep 1932161 = 1449121) B1449121
theorem B1932179 : Blo 1287962 1932179 := bstep (se 1 (by rfl) ⟨1449134, by rfl⟩ : syracuseStep 1932179 = 2898269) B2898269
theorem B4348835 : Blo 1287962 4348835 := bstep (se 1 (by rfl) ⟨3261626, by rfl⟩ : syracuseStep 4348835 = 6523253) B6523253
theorem B6192035 : Blo 1287962 6192035 := bstep (se 1 (by rfl) ⟨4644026, by rfl⟩ : syracuseStep 6192035 = 9288053) B9288053
theorem B2063281 : Blo 1287962 2063281 := bstep (se 2 (by rfl) ⟨773730, by rfl⟩ : syracuseStep 2063281 = 1547461) B1547461
theorem B1932209 : Blo 1287962 1932209 := bstep (se 2 (by rfl) ⟨724578, by rfl⟩ : syracuseStep 1932209 = 1449157) B1449157
theorem B1932227 : Blo 1287962 1932227 := bstep (se 1 (by rfl) ⟨1449170, by rfl⟩ : syracuseStep 1932227 = 2898341) B2898341
theorem B1932257 : Blo 1287962 1932257 := bstep (se 2 (by rfl) ⟨724596, by rfl⟩ : syracuseStep 1932257 = 1449193) B1449193
theorem B1932275 : Blo 1287962 1932275 := bstep (se 1 (by rfl) ⟨1449206, by rfl⟩ : syracuseStep 1932275 = 2898413) B2898413
theorem B1932305 : Blo 1287962 1932305 := bstep (se 2 (by rfl) ⟨724614, by rfl⟩ : syracuseStep 1932305 = 1449229) B1449229
theorem B1448995 : Blo 1287962 1448995 := bstep (se 1 (by rfl) ⟨1086746, by rfl⟩ : syracuseStep 1448995 = 2173493) B2173493
theorem B1932323 : Blo 1287962 1932323 := bstep (se 1 (by rfl) ⟨1449242, by rfl⟩ : syracuseStep 1932323 = 2898485) B2898485
theorem B1932353 : Blo 1287962 1932353 := bstep (se 2 (by rfl) ⟨724632, by rfl⟩ : syracuseStep 1932353 = 1449265) B1449265
theorem B2899025 : Blo 1287962 2899025 := bstep (se 2 (by rfl) ⟨1087134, by rfl⟩ : syracuseStep 2899025 = 2174269) B2174269
theorem B1932371 : Blo 1287962 1932371 := bstep (se 1 (by rfl) ⟨1449278, by rfl⟩ : syracuseStep 1932371 = 2898557) B2898557
theorem B2899043 : Blo 1287962 2899043 := bstep (se 1 (by rfl) ⟨2174282, by rfl⟩ : syracuseStep 2899043 = 4348565) B4348565
theorem B1932401 : Blo 1287962 1932401 := bstep (se 2 (by rfl) ⟨724650, by rfl⟩ : syracuseStep 1932401 = 1449301) B1449301
theorem B6528113 : Blo 1287962 6528113 := bstep (se 2 (by rfl) ⟨2448042, by rfl⟩ : syracuseStep 6528113 = 4896085) B4896085
theorem B1932419 : Blo 1287962 1932419 := bstep (se 1 (by rfl) ⟨1449314, by rfl⟩ : syracuseStep 1932419 = 2898629) B2898629
theorem B1932449 : Blo 1287962 1932449 := bstep (se 2 (by rfl) ⟨724668, by rfl⟩ : syracuseStep 1932449 = 1449337) B1449337
theorem B4349105 : Blo 1287962 4349105 := bstep (se 2 (by rfl) ⟨1630914, by rfl⟩ : syracuseStep 4349105 = 3261829) B3261829
theorem B1449139 : Blo 1287962 1449139 := bstep (se 1 (by rfl) ⟨1086854, by rfl⟩ : syracuseStep 1449139 = 2173709) B2173709
theorem B1932467 : Blo 1287962 1932467 := bstep (se 1 (by rfl) ⟨1449350, by rfl⟩ : syracuseStep 1932467 = 2898701) B2898701
theorem B1375427 : Blo 1287962 1375427 := bstep (se 1 (by rfl) ⟨1031570, by rfl⟩ : syracuseStep 1375427 = 2063141) B2063141
theorem B1932497 : Blo 1287962 1932497 := bstep (se 2 (by rfl) ⟨724686, by rfl⟩ : syracuseStep 1932497 = 1449373) B1449373
theorem B1932515 : Blo 1287962 1932515 := bstep (se 1 (by rfl) ⟨1449386, by rfl⟩ : syracuseStep 1932515 = 2898773) B2898773
theorem B1932545 : Blo 1287962 1932545 := bstep (se 2 (by rfl) ⟨724704, by rfl⟩ : syracuseStep 1932545 = 1449409) B1449409
theorem B2448643 : Blo 1287962 2448643 := bstep (se 1 (by rfl) ⟨1836482, by rfl⟩ : syracuseStep 2448643 = 3672965) B3672965
theorem B5504269 : Blo 1287962 5504269 := bstep (se 3 (by rfl) ⟨1032050, by rfl⟩ : syracuseStep 5504269 = 2064101) B2064101
theorem B1932563 : Blo 1287962 1932563 := bstep (se 1 (by rfl) ⟨1449422, by rfl⟩ : syracuseStep 1932563 = 2898845) B2898845
theorem B1932593 : Blo 1287962 1932593 := bstep (se 2 (by rfl) ⟨724722, by rfl⟩ : syracuseStep 1932593 = 1449445) B1449445
theorem B1449283 : Blo 1287962 1449283 := bstep (se 1 (by rfl) ⟨1086962, by rfl⟩ : syracuseStep 1449283 = 2173925) B2173925
theorem B1932611 : Blo 1287962 1932611 := bstep (se 1 (by rfl) ⟨1449458, by rfl⟩ : syracuseStep 1932611 = 2898917) B2898917
theorem B1932641 : Blo 1287962 1932641 := bstep (se 2 (by rfl) ⟨724740, by rfl⟩ : syracuseStep 1932641 = 1449481) B1449481
theorem B3095921 : Blo 1287962 3095921 := bstep (se 2 (by rfl) ⟨1160970, by rfl⟩ : syracuseStep 3095921 = 2321941) B2321941
theorem B2899313 : Blo 1287962 2899313 := bstep (se 2 (by rfl) ⟨1087242, by rfl⟩ : syracuseStep 2899313 = 2174485) B2174485
theorem B1932659 : Blo 1287962 1932659 := bstep (se 1 (by rfl) ⟨1449494, by rfl⟩ : syracuseStep 1932659 = 2898989) B2898989
theorem B2899331 : Blo 1287962 2899331 := bstep (se 1 (by rfl) ⟨2174498, by rfl⟩ : syracuseStep 2899331 = 4348997) B4348997
theorem B4406669 : Blo 1287962 4406669 := bstep (se 3 (by rfl) ⟨826250, by rfl⟩ : syracuseStep 4406669 = 1652501) B1652501
theorem B1932689 : Blo 1287962 1932689 := bstep (se 2 (by rfl) ⟨724758, by rfl⟩ : syracuseStep 1932689 = 1449517) B1449517
theorem B1932707 : Blo 1287962 1932707 := bstep (se 1 (by rfl) ⟨1449530, by rfl⟩ : syracuseStep 1932707 = 2899061) B2899061
theorem B1932737 : Blo 1287962 1932737 := bstep (se 2 (by rfl) ⟨724776, by rfl⟩ : syracuseStep 1932737 = 1449553) B1449553
theorem B1449427 : Blo 1287962 1449427 := bstep (se 1 (by rfl) ⟨1087070, by rfl⟩ : syracuseStep 1449427 = 2174141) B2174141
theorem B1932755 : Blo 1287962 1932755 := bstep (se 1 (by rfl) ⟨1449566, by rfl⟩ : syracuseStep 1932755 = 2899133) B2899133
theorem B1932785 : Blo 1287962 1932785 := bstep (se 2 (by rfl) ⟨724794, by rfl⟩ : syracuseStep 1932785 = 1449589) B1449589
theorem B1834483 : Blo 1287962 1834483 := bstep (se 1 (by rfl) ⟨1375862, by rfl⟩ : syracuseStep 1834483 = 2751725) B2751725
theorem B1932803 : Blo 1287962 1932803 := bstep (se 1 (by rfl) ⟨1449602, by rfl⟩ : syracuseStep 1932803 = 2899205) B2899205
theorem B9780749 : Blo 1287962 9780749 := bstep (se 3 (by rfl) ⟨1833890, by rfl⟩ : syracuseStep 9780749 = 3667781) B3667781
theorem B1932833 : Blo 1287962 1932833 := bstep (se 2 (by rfl) ⟨724812, by rfl⟩ : syracuseStep 1932833 = 1449625) B1449625
theorem B1932851 : Blo 1287962 1932851 := bstep (se 1 (by rfl) ⟨1449638, by rfl⟩ : syracuseStep 1932851 = 2899277) B2899277
theorem B1932881 : Blo 1287962 1932881 := bstep (se 2 (by rfl) ⟨724830, by rfl⟩ : syracuseStep 1932881 = 1449661) B1449661
theorem B1449571 : Blo 1287962 1449571 := bstep (se 1 (by rfl) ⟨1087178, by rfl⟩ : syracuseStep 1449571 = 2174357) B2174357
theorem B1932899 : Blo 1287962 1932899 := bstep (se 1 (by rfl) ⟨1449674, by rfl⟩ : syracuseStep 1932899 = 2899349) B2899349
theorem B5504611 : Blo 1287962 5504611 := bstep (se 1 (by rfl) ⟨4128458, by rfl⟩ : syracuseStep 5504611 = 8256917) B8256917
theorem B1932929 : Blo 1287962 1932929 := bstep (se 2 (by rfl) ⟨724848, by rfl⟩ : syracuseStep 1932929 = 1449697) B1449697
theorem B4890253 : Blo 1287962 4890253 := bstep (se 3 (by rfl) ⟨916922, by rfl⟩ : syracuseStep 4890253 = 1833845) B1833845
theorem B2899601 : Blo 1287962 2899601 := bstep (se 2 (by rfl) ⟨1087350, by rfl⟩ : syracuseStep 2899601 = 2174701) B2174701
theorem B1932947 : Blo 1287962 1932947 := bstep (se 1 (by rfl) ⟨1449710, by rfl⟩ : syracuseStep 1932947 = 2899421) B2899421
theorem B2899619 : Blo 1287962 2899619 := bstep (se 1 (by rfl) ⟨2174714, by rfl⟩ : syracuseStep 2899619 = 4349429) B4349429
theorem B4406957 : Blo 1287962 4406957 := bstep (se 3 (by rfl) ⟨826304, by rfl⟩ : syracuseStep 4406957 = 1652609) B1652609
theorem B1932977 : Blo 1287962 1932977 := bstep (se 2 (by rfl) ⟨724866, by rfl⟩ : syracuseStep 1932977 = 1449733) B1449733
theorem B1932995 : Blo 1287962 1932995 := bstep (se 1 (by rfl) ⟨1449746, by rfl⟩ : syracuseStep 1932995 = 2899493) B2899493
theorem B17637061 : Blo 1287962 17637061 := bstep (se 4 (by rfl) ⟨1653474, by rfl⟩ : syracuseStep 17637061 = 3306949) B3306949
theorem B4349645 : Blo 1287962 4349645 := bstep (se 3 (by rfl) ⟨815558, by rfl⟩ : syracuseStep 4349645 = 1631117) B1631117
theorem B3718865 : Blo 1287962 3718865 := bstep (se 2 (by rfl) ⟨1394574, by rfl⟩ : syracuseStep 3718865 = 2789149) B2789149
theorem B1933025 : Blo 1287962 1933025 := bstep (se 2 (by rfl) ⟨724884, by rfl⟩ : syracuseStep 1933025 = 1449769) B1449769
theorem B1449715 : Blo 1287962 1449715 := bstep (se 1 (by rfl) ⟨1087286, by rfl⟩ : syracuseStep 1449715 = 2174573) B2174573
theorem B1933043 : Blo 1287962 1933043 := bstep (se 1 (by rfl) ⟨1449782, by rfl⟩ : syracuseStep 1933043 = 2899565) B2899565
theorem B4349699 : Blo 1287962 4349699 := bstep (se 1 (by rfl) ⟨3262274, by rfl⟩ : syracuseStep 4349699 = 6524549) B6524549
theorem B1933073 : Blo 1287962 1933073 := bstep (se 2 (by rfl) ⟨724902, by rfl⟩ : syracuseStep 1933073 = 1449805) B1449805
theorem B1933091 : Blo 1287962 1933091 := bstep (se 1 (by rfl) ⟨1449818, by rfl⟩ : syracuseStep 1933091 = 2899637) B2899637
theorem B3260209 : Blo 1287962 3260209 := bstep (se 2 (by rfl) ⟨1222578, by rfl⟩ : syracuseStep 3260209 = 2445157) B2445157
theorem B2981681 : Blo 1287962 2981681 := bstep (se 2 (by rfl) ⟨1118130, by rfl⟩ : syracuseStep 2981681 = 2236261) B2236261
theorem B2064179 : Blo 1287962 2064179 := bstep (se 1 (by rfl) ⟨1548134, by rfl⟩ : syracuseStep 2064179 = 3096269) B3096269
theorem B1933121 : Blo 1287962 1933121 := bstep (se 2 (by rfl) ⟨724920, by rfl⟩ : syracuseStep 1933121 = 1449841) B1449841
theorem B1933139 : Blo 1287962 1933139 := bstep (se 1 (by rfl) ⟨1449854, by rfl⟩ : syracuseStep 1933139 = 2899709) B2899709
theorem B1933169 : Blo 1287962 1933169 := bstep (se 2 (by rfl) ⟨724938, by rfl⟩ : syracuseStep 1933169 = 1449877) B1449877
theorem B1548163 : Blo 1287962 1548163 := bstep (se 1 (by rfl) ⟨1161122, by rfl⟩ : syracuseStep 1548163 = 2322245) B2322245
theorem B1449859 : Blo 1287962 1449859 := bstep (se 1 (by rfl) ⟨1087394, by rfl⟩ : syracuseStep 1449859 = 2174789) B2174789
theorem B1933187 : Blo 1287962 1933187 := bstep (se 1 (by rfl) ⟨1449890, by rfl⟩ : syracuseStep 1933187 = 2899781) B2899781
theorem B1933217 : Blo 1287962 1933217 := bstep (se 2 (by rfl) ⟨724956, by rfl⟩ : syracuseStep 1933217 = 1449913) B1449913
theorem B3669923 : Blo 1287962 3669923 := bstep (se 1 (by rfl) ⟨2752442, by rfl⟩ : syracuseStep 3669923 = 5504885) B5504885
theorem B2899889 : Blo 1287962 2899889 := bstep (se 2 (by rfl) ⟨1087458, by rfl⟩ : syracuseStep 2899889 = 2174917) B2174917
theorem B1933235 : Blo 1287962 1933235 := bstep (se 1 (by rfl) ⟨1449926, by rfl⟩ : syracuseStep 1933235 = 2899853) B2899853
theorem B2899907 : Blo 1287962 2899907 := bstep (se 1 (by rfl) ⟨2174930, by rfl⟩ : syracuseStep 2899907 = 4349861) B4349861
theorem B1933265 : Blo 1287962 1933265 := bstep (se 2 (by rfl) ⟨724974, by rfl⟩ : syracuseStep 1933265 = 1449949) B1449949
theorem B1933283 : Blo 1287962 1933283 := bstep (se 1 (by rfl) ⟨1449962, by rfl⟩ : syracuseStep 1933283 = 2899925) B2899925
theorem B2899979 : Blo 1287962 2899979 := bstep (se 1 (by rfl) ⟨2174984, by rfl⟩ : syracuseStep 2899979 = 4349969) B4349969
theorem B6619153 : Blo 1287962 6619153 := bstep (se 2 (by rfl) ⟨2482182, by rfl⟩ : syracuseStep 6619153 = 4964365) B4964365
theorem B2752537 : Blo 1287962 2752537 := bstep (se 2 (by rfl) ⟨1032201, by rfl⟩ : syracuseStep 2752537 = 2064403) B2064403
theorem B1933337 : Blo 1287962 1933337 := bstep (se 2 (by rfl) ⟨725001, by rfl⟩ : syracuseStep 1933337 = 1450003) B1450003
theorem B1450039 : Blo 1287962 1450039 := bstep (se 1 (by rfl) ⟨1087529, by rfl⟩ : syracuseStep 1450039 = 2175059) B2175059
theorem B2900033 : Blo 1287962 2900033 := bstep (se 2 (by rfl) ⟨1087512, by rfl⟩ : syracuseStep 2900033 = 2175025) B2175025
theorem B3670105 : Blo 1287962 3670105 := bstep (se 2 (by rfl) ⟨1376289, by rfl⟩ : syracuseStep 3670105 = 2752579) B2752579
theorem B1933451 : Blo 1287962 1933451 := bstep (se 1 (by rfl) ⟨1450088, by rfl⟩ : syracuseStep 1933451 = 2900177) B2900177
theorem B1933463 : Blo 1287962 1933463 := bstep (se 1 (by rfl) ⟨1450097, by rfl⟩ : syracuseStep 1933463 = 2900195) B2900195
theorem B4350131 : Blo 1287962 4350131 := bstep (se 1 (by rfl) ⟨3262598, by rfl⟩ : syracuseStep 4350131 = 6525197) B6525197
theorem B1933529 : Blo 1287962 1933529 := bstep (se 2 (by rfl) ⟨725073, by rfl⟩ : syracuseStep 1933529 = 1450147) B1450147
theorem B1450219 : Blo 1287962 1450219 := bstep (se 1 (by rfl) ⟨1087664, by rfl⟩ : syracuseStep 1450219 = 2175329) B2175329
theorem B23527685 : Blo 1287962 23527685 := bstep (se 4 (by rfl) ⟨2205720, by rfl⟩ : syracuseStep 23527685 = 4411441) B4411441
theorem B3260695 : Blo 1287962 3260695 := bstep (se 1 (by rfl) ⟨2445521, by rfl⟩ : syracuseStep 3260695 = 4891043) B4891043
theorem B2900249 : Blo 1287962 2900249 := bstep (se 2 (by rfl) ⟨1087593, by rfl⟩ : syracuseStep 2900249 = 2175187) B2175187
theorem B3096883 : Blo 1287962 3096883 := bstep (se 1 (by rfl) ⟨2322662, by rfl⟩ : syracuseStep 3096883 = 4645325) B4645325
theorem B1933643 : Blo 1287962 1933643 := bstep (se 1 (by rfl) ⟨1450232, by rfl⟩ : syracuseStep 1933643 = 2900465) B2900465
theorem B1933655 : Blo 1287962 1933655 := bstep (se 1 (by rfl) ⟨1450241, by rfl⟩ : syracuseStep 1933655 = 2900483) B2900483
theorem B1450327 : Blo 1287962 1450327 := bstep (se 1 (by rfl) ⟨1087745, by rfl⟩ : syracuseStep 1450327 = 2175491) B2175491
theorem B2900339 : Blo 1287962 2900339 := bstep (se 1 (by rfl) ⟨2175254, by rfl⟩ : syracuseStep 2900339 = 4350509) B4350509
theorem B2900375 : Blo 1287962 2900375 := bstep (se 1 (by rfl) ⟨2175281, by rfl⟩ : syracuseStep 2900375 = 4350563) B4350563
theorem B1835417 : Blo 1287962 1835417 := bstep (se 2 (by rfl) ⟨688281, by rfl⟩ : syracuseStep 1835417 = 1376563) B1376563
theorem B1933721 : Blo 1287962 1933721 := bstep (se 2 (by rfl) ⟨725145, by rfl⟩ : syracuseStep 1933721 = 1450291) B1450291
theorem B4350401 : Blo 1287962 4350401 := bstep (se 2 (by rfl) ⟨1631400, by rfl⟩ : syracuseStep 4350401 = 3262801) B3262801
theorem B9781721 : Blo 1287962 9781721 := bstep (se 2 (by rfl) ⟨3668145, by rfl⟩ : syracuseStep 9781721 = 7336291) B7336291
theorem B9413081 : Blo 1287962 9413081 := bstep (se 2 (by rfl) ⟨3529905, by rfl⟩ : syracuseStep 9413081 = 7059811) B7059811
theorem B1933835 : Blo 1287962 1933835 := bstep (se 1 (by rfl) ⟨1450376, by rfl⟩ : syracuseStep 1933835 = 2900753) B2900753
theorem B1450507 : Blo 1287962 1450507 := bstep (se 1 (by rfl) ⟨1087880, by rfl⟩ : syracuseStep 1450507 = 2175761) B2175761
theorem B13238801 : Blo 1287962 13238801 := bstep (se 2 (by rfl) ⟨4964550, by rfl⟩ : syracuseStep 13238801 = 9929101) B9929101
theorem B1933847 : Blo 1287962 1933847 := bstep (se 1 (by rfl) ⟨1450385, by rfl⟩ : syracuseStep 1933847 = 2900771) B2900771
theorem B4891211 : Blo 1287962 4891211 := bstep (se 1 (by rfl) ⟨3668408, by rfl⟩ : syracuseStep 4891211 = 7336817) B7336817
theorem B2900555 : Blo 1287962 2900555 := bstep (se 1 (by rfl) ⟨2175416, by rfl⟩ : syracuseStep 2900555 = 4350833) B4350833
theorem B4891225 : Blo 1287962 4891225 := bstep (se 2 (by rfl) ⟨1834209, by rfl⟩ : syracuseStep 4891225 = 3668419) B3668419
theorem B1933913 : Blo 1287962 1933913 := bstep (se 2 (by rfl) ⟨725217, by rfl⟩ : syracuseStep 1933913 = 1450435) B1450435
theorem B16515677 : Blo 1287962 16515677 := bstep (se 3 (by rfl) ⟨3096689, by rfl⟩ : syracuseStep 16515677 = 6193379) B6193379
theorem B1450615 : Blo 1287962 1450615 := bstep (se 1 (by rfl) ⟨1087961, by rfl⟩ : syracuseStep 1450615 = 2175923) B2175923
theorem B2900609 : Blo 1287962 2900609 := bstep (se 2 (by rfl) ⟨1087728, by rfl⟩ : syracuseStep 2900609 = 2175457) B2175457
theorem B2941591 : Blo 1287962 2941591 := bstep (se 1 (by rfl) ⟨2206193, by rfl⟩ : syracuseStep 2941591 = 4412387) B4412387
theorem B1376939 : Blo 1287962 1376939 := bstep (se 1 (by rfl) ⟨1032704, by rfl⟩ : syracuseStep 1376939 = 2065409) B2065409
theorem B3670721 : Blo 1287962 3670721 := bstep (se 2 (by rfl) ⟨1376520, by rfl⟩ : syracuseStep 3670721 = 2753041) B2753041
theorem B2613953 : Blo 1287962 2613953 := bstep (se 2 (by rfl) ⟨980232, by rfl⟩ : syracuseStep 2613953 = 1960465) B1960465
theorem B3261131 : Blo 1287962 3261131 := bstep (se 1 (by rfl) ⟨2445848, by rfl⟩ : syracuseStep 3261131 = 4891697) B4891697
theorem B1934027 : Blo 1287962 1934027 := bstep (se 1 (by rfl) ⟨1450520, by rfl⟩ : syracuseStep 1934027 = 2901041) B2901041
theorem B1934039 : Blo 1287962 1934039 := bstep (se 1 (by rfl) ⟨1450529, by rfl⟩ : syracuseStep 1934039 = 2901059) B2901059
theorem B1934105 : Blo 1287962 1934105 := bstep (se 2 (by rfl) ⟨725289, by rfl⟩ : syracuseStep 1934105 = 1450579) B1450579
theorem B9290531 : Blo 1287962 9290531 := bstep (se 1 (by rfl) ⟨6967898, by rfl⟩ : syracuseStep 9290531 = 13935797) B13935797
theorem B1450795 : Blo 1287962 1450795 := bstep (se 1 (by rfl) ⟨1088096, by rfl⟩ : syracuseStep 1450795 = 2176193) B2176193
theorem B5882669 : Blo 1287962 5882669 := bstep (se 3 (by rfl) ⟨1103000, by rfl⟩ : syracuseStep 5882669 = 2206001) B2206001
theorem B2900825 : Blo 1287962 2900825 := bstep (se 2 (by rfl) ⟨1087809, by rfl⟩ : syracuseStep 2900825 = 2175619) B2175619
theorem B14132069 : Blo 1287962 14132069 := bstep (se 4 (by rfl) ⟨1324881, by rfl⟩ : syracuseStep 14132069 = 2649763) B2649763
theorem B1934219 : Blo 1287962 1934219 := bstep (se 1 (by rfl) ⟨1450664, by rfl⟩ : syracuseStep 1934219 = 2901329) B2901329
theorem B1934231 : Blo 1287962 1934231 := bstep (se 1 (by rfl) ⟨1450673, by rfl⟩ : syracuseStep 1934231 = 2901347) B2901347
theorem B1450903 : Blo 1287962 1450903 := bstep (se 1 (by rfl) ⟨1088177, by rfl⟩ : syracuseStep 1450903 = 2176355) B2176355
theorem B6972311 : Blo 1287962 6972311 := bstep (se 1 (by rfl) ⟨5229233, by rfl⟩ : syracuseStep 6972311 = 10458467) B10458467
theorem B2900915 : Blo 1287962 2900915 := bstep (se 1 (by rfl) ⟨2175686, by rfl⟩ : syracuseStep 2900915 = 4351373) B4351373
theorem B2900951 : Blo 1287962 2900951 := bstep (se 1 (by rfl) ⟨2175713, by rfl⟩ : syracuseStep 2900951 = 4351427) B4351427
theorem B1934297 : Blo 1287962 1934297 := bstep (se 2 (by rfl) ⟨725361, by rfl⟩ : syracuseStep 1934297 = 1450723) B1450723
theorem B4350941 : Blo 1287962 4350941 := bstep (se 3 (by rfl) ⟨815801, by rfl⟩ : syracuseStep 4350941 = 1631603) B1631603
theorem B9790469 : Blo 1287962 9790469 := bstep (se 4 (by rfl) ⟨917856, by rfl⟩ : syracuseStep 9790469 = 1835713) B1835713
theorem B1836055 : Blo 1287962 1836055 := bstep (se 1 (by rfl) ⟨1377041, by rfl⟩ : syracuseStep 1836055 = 2754083) B2754083
theorem B8815661 : Blo 1287962 8815661 := bstep (se 3 (by rfl) ⟨1652936, by rfl⟩ : syracuseStep 8815661 = 3305873) B3305873
theorem B3261505 : Blo 1287962 3261505 := bstep (se 2 (by rfl) ⟨1223064, by rfl⟩ : syracuseStep 3261505 = 2446129) B2446129
theorem B1934411 : Blo 1287962 1934411 := bstep (se 1 (by rfl) ⟨1450808, by rfl⟩ : syracuseStep 1934411 = 2901617) B2901617
theorem B1451083 : Blo 1287962 1451083 := bstep (se 1 (by rfl) ⟨1088312, by rfl⟩ : syracuseStep 1451083 = 2176625) B2176625
theorem B1934423 : Blo 1287962 1934423 := bstep (se 1 (by rfl) ⟨1450817, by rfl⟩ : syracuseStep 1934423 = 2901635) B2901635
theorem B2901131 : Blo 1287962 2901131 := bstep (se 1 (by rfl) ⟨2175848, by rfl⟩ : syracuseStep 2901131 = 4351697) B4351697
theorem B1934489 : Blo 1287962 1934489 := bstep (se 2 (by rfl) ⟨725433, by rfl⟩ : syracuseStep 1934489 = 1450867) B1450867
theorem B4408499 : Blo 1287962 4408499 := bstep (se 1 (by rfl) ⟨3306374, by rfl⟩ : syracuseStep 4408499 = 6612749) B6612749
theorem B1451191 : Blo 1287962 1451191 := bstep (se 1 (by rfl) ⟨1088393, by rfl⟩ : syracuseStep 1451191 = 2176787) B2176787
theorem B2901185 : Blo 1287962 2901185 := bstep (se 2 (by rfl) ⟨1087944, by rfl⟩ : syracuseStep 2901185 = 2175889) B2175889
theorem B9290969 : Blo 1287962 9290969 := bstep (se 2 (by rfl) ⟨3484113, by rfl⟩ : syracuseStep 9290969 = 6968227) B6968227
theorem B4646105 : Blo 1287962 4646105 := bstep (se 2 (by rfl) ⟨1742289, by rfl⟩ : syracuseStep 4646105 = 3484579) B3484579
theorem B1934603 : Blo 1287962 1934603 := bstep (se 1 (by rfl) ⟨1450952, by rfl⟩ : syracuseStep 1934603 = 2901905) B2901905
theorem B1934615 : Blo 1287962 1934615 := bstep (se 1 (by rfl) ⟨1450961, by rfl⟩ : syracuseStep 1934615 = 2901923) B2901923
theorem B4130099 : Blo 1287962 4130099 := bstep (se 1 (by rfl) ⟨3097574, by rfl⟩ : syracuseStep 4130099 = 6195149) B6195149
theorem B2753843 : Blo 1287962 2753843 := bstep (se 1 (by rfl) ⟨2065382, by rfl⟩ : syracuseStep 2753843 = 4130765) B4130765
theorem B1934681 : Blo 1287962 1934681 := bstep (se 2 (by rfl) ⟨725505, by rfl⟩ : syracuseStep 1934681 = 1451011) B1451011
theorem B2901401 : Blo 1287962 2901401 := bstep (se 2 (by rfl) ⟨1088025, by rfl⟩ : syracuseStep 2901401 = 2176051) B2176051
theorem B12387761 : Blo 1287962 12387761 := bstep (se 2 (by rfl) ⟨4645410, by rfl⟩ : syracuseStep 12387761 = 9290821) B9290821
theorem B9422257 : Blo 1287962 9422257 := bstep (se 2 (by rfl) ⟨3533346, by rfl⟩ : syracuseStep 9422257 = 7066693) B7066693
theorem B1934795 : Blo 1287962 1934795 := bstep (se 1 (by rfl) ⟨1451096, by rfl⟩ : syracuseStep 1934795 = 2902193) B2902193
theorem B1934807 : Blo 1287962 1934807 := bstep (se 1 (by rfl) ⟨1451105, by rfl⟩ : syracuseStep 1934807 = 2902211) B2902211
theorem B618816995 : Blo 1287962 618816995 := bstep (se 1 (by rfl) ⟨464112746, by rfl⟩ : syracuseStep 618816995 = 928225493) B928225493
theorem B2901491 : Blo 1287962 2901491 := bstep (se 1 (by rfl) ⟨2176118, by rfl⟩ : syracuseStep 2901491 = 4352237) B4352237
theorem B1631755 : Blo 1287962 1631755 := bstep (se 1 (by rfl) ⟨1223816, by rfl⟩ : syracuseStep 1631755 = 2447633) B2447633
theorem B4892183 : Blo 1287962 4892183 := bstep (se 1 (by rfl) ⟨3669137, by rfl⟩ : syracuseStep 4892183 = 7338275) B7338275
theorem B2901527 : Blo 1287962 2901527 := bstep (se 1 (by rfl) ⟨2176145, by rfl⟩ : syracuseStep 2901527 = 4352291) B4352291
theorem B1934873 : Blo 1287962 1934873 := bstep (se 2 (by rfl) ⟨725577, by rfl⟩ : syracuseStep 1934873 = 1451155) B1451155
theorem B6522443 : Blo 1287962 6522443 := bstep (se 1 (by rfl) ⟨4891832, by rfl⟩ : syracuseStep 6522443 = 9783665) B9783665
theorem B3720779 : Blo 1287962 3720779 := bstep (se 1 (by rfl) ⟨2790584, by rfl⟩ : syracuseStep 3720779 = 5581169) B5581169
theorem B3262103 : Blo 1287962 3262103 := bstep (se 1 (by rfl) ⟨2446577, by rfl⟩ : syracuseStep 3262103 = 4893155) B4893155
theorem B2385587 : Blo 1287962 2385587 := bstep (se 1 (by rfl) ⟨1789190, by rfl⟩ : syracuseStep 2385587 = 3578381) B3578381
theorem B2901707 : Blo 1287962 2901707 := bstep (se 1 (by rfl) ⟨2176280, by rfl⟩ : syracuseStep 2901707 = 4352561) B4352561
theorem B34866893 : Blo 1287962 34866893 := bstep (se 3 (by rfl) ⟨6537542, by rfl⟩ : syracuseStep 34866893 = 13075085) B13075085
theorem B2901761 : Blo 1287962 2901761 := bstep (se 2 (by rfl) ⟨1088160, by rfl⟩ : syracuseStep 2901761 = 2176321) B2176321
theorem B1287979 : Blo 1287962 1287979 := bstep (se 1 (by rfl) ⟨965984, by rfl⟩ : syracuseStep 1287979 = 1931969) B1931969
theorem B1287991 : Blo 1287962 1287991 := bstep (se 1 (by rfl) ⟨965993, by rfl⟩ : syracuseStep 1287991 = 1931987) B1931987
theorem B29747009 : Blo 1287962 29747009 := bstep (se 2 (by rfl) ⟨11155128, by rfl⟩ : syracuseStep 29747009 = 22310257) B22310257
theorem B1288011 : Blo 1287962 1288011 := bstep (se 1 (by rfl) ⟨966008, by rfl⟩ : syracuseStep 1288011 = 1932017) B1932017
theorem B1288023 : Blo 1287962 1288023 := bstep (se 1 (by rfl) ⟨966017, by rfl⟩ : syracuseStep 1288023 = 1932035) B1932035
theorem B1288043 : Blo 1287962 1288043 := bstep (se 1 (by rfl) ⟨966032, by rfl⟩ : syracuseStep 1288043 = 1932065) B1932065
theorem B1288055 : Blo 1287962 1288055 := bstep (se 1 (by rfl) ⟨966041, by rfl⟩ : syracuseStep 1288055 = 1932083) B1932083
theorem B1288075 : Blo 1287962 1288075 := bstep (se 1 (by rfl) ⟨966056, by rfl⟩ : syracuseStep 1288075 = 1932113) B1932113
theorem B1288087 : Blo 1287962 1288087 := bstep (se 1 (by rfl) ⟨966065, by rfl⟩ : syracuseStep 1288087 = 1932131) B1932131
theorem B8259479 : Blo 1287962 8259479 := bstep (se 1 (by rfl) ⟨6194609, by rfl⟩ : syracuseStep 8259479 = 12389219) B12389219
theorem B1288107 : Blo 1287962 1288107 := bstep (se 1 (by rfl) ⟨966080, by rfl⟩ : syracuseStep 1288107 = 1932161) B1932161
theorem B1288119 : Blo 1287962 1288119 := bstep (se 1 (by rfl) ⟨966089, by rfl⟩ : syracuseStep 1288119 = 1932179) B1932179
theorem B1288139 : Blo 1287962 1288139 := bstep (se 1 (by rfl) ⟨966104, by rfl⟩ : syracuseStep 1288139 = 1932209) B1932209
theorem B1288151 : Blo 1287962 1288151 := bstep (se 1 (by rfl) ⟨966113, by rfl⟩ : syracuseStep 1288151 = 1932227) B1932227
theorem B2901977 : Blo 1287962 2901977 := bstep (se 2 (by rfl) ⟨1088241, by rfl⟩ : syracuseStep 2901977 = 2176483) B2176483
theorem B3917789 : Blo 1287962 3917789 := bstep (se 3 (by rfl) ⟨734585, by rfl⟩ : syracuseStep 3917789 = 1469171) B1469171
theorem B1288171 : Blo 1287962 1288171 := bstep (se 1 (by rfl) ⟨966128, by rfl⟩ : syracuseStep 1288171 = 1932257) B1932257
theorem B1288183 : Blo 1287962 1288183 := bstep (se 1 (by rfl) ⟨966137, by rfl⟩ : syracuseStep 1288183 = 1932275) B1932275
theorem B1288203 : Blo 1287962 1288203 := bstep (se 1 (by rfl) ⟨966152, by rfl⟩ : syracuseStep 1288203 = 1932305) B1932305
theorem B1288215 : Blo 1287962 1288215 := bstep (se 1 (by rfl) ⟨966161, by rfl⟩ : syracuseStep 1288215 = 1932323) B1932323
theorem B1288235 : Blo 1287962 1288235 := bstep (se 1 (by rfl) ⟨966176, by rfl⟩ : syracuseStep 1288235 = 1932353) B1932353
theorem B2902067 : Blo 1287962 2902067 := bstep (se 1 (by rfl) ⟨2176550, by rfl⟩ : syracuseStep 2902067 = 4353101) B4353101
theorem B1288247 : Blo 1287962 1288247 := bstep (se 1 (by rfl) ⟨966185, by rfl⟩ : syracuseStep 1288247 = 1932371) B1932371
theorem B1288267 : Blo 1287962 1288267 := bstep (se 1 (by rfl) ⟨966200, by rfl⟩ : syracuseStep 1288267 = 1932401) B1932401
theorem B4352075 : Blo 1287962 4352075 := bstep (se 1 (by rfl) ⟨3264056, by rfl⟩ : syracuseStep 4352075 = 6528113) B6528113
theorem B1288279 : Blo 1287962 1288279 := bstep (se 1 (by rfl) ⟨966209, by rfl⟩ : syracuseStep 1288279 = 1932419) B1932419
theorem B2902103 : Blo 1287962 2902103 := bstep (se 1 (by rfl) ⟨2176577, by rfl⟩ : syracuseStep 2902103 = 4353155) B4353155
theorem B1288299 : Blo 1287962 1288299 := bstep (se 1 (by rfl) ⟨966224, by rfl⟩ : syracuseStep 1288299 = 1932449) B1932449
theorem B1288311 : Blo 1287962 1288311 := bstep (se 1 (by rfl) ⟨966233, by rfl⟩ : syracuseStep 1288311 = 1932467) B1932467
theorem B1288331 : Blo 1287962 1288331 := bstep (se 1 (by rfl) ⟨966248, by rfl⟩ : syracuseStep 1288331 = 1932497) B1932497
theorem B1288343 : Blo 1287962 1288343 := bstep (se 1 (by rfl) ⟨966257, by rfl⟩ : syracuseStep 1288343 = 1932515) B1932515
theorem B1288363 : Blo 1287962 1288363 := bstep (se 1 (by rfl) ⟨966272, by rfl⟩ : syracuseStep 1288363 = 1932545) B1932545
theorem B6195379 : Blo 1287962 6195379 := bstep (se 1 (by rfl) ⟨4646534, by rfl⟩ : syracuseStep 6195379 = 9293069) B9293069
theorem B1288375 : Blo 1287962 1288375 := bstep (se 1 (by rfl) ⟨966281, by rfl⟩ : syracuseStep 1288375 = 1932563) B1932563
theorem B1288395 : Blo 1287962 1288395 := bstep (se 1 (by rfl) ⟨966296, by rfl⟩ : syracuseStep 1288395 = 1932593) B1932593
theorem B1288407 : Blo 1287962 1288407 := bstep (se 1 (by rfl) ⟨966305, by rfl⟩ : syracuseStep 1288407 = 1932611) B1932611
theorem B1288427 : Blo 1287962 1288427 := bstep (se 1 (by rfl) ⟨966320, by rfl⟩ : syracuseStep 1288427 = 1932641) B1932641
theorem B1288439 : Blo 1287962 1288439 := bstep (se 1 (by rfl) ⟨966329, by rfl⟩ : syracuseStep 1288439 = 1932659) B1932659
theorem B1288459 : Blo 1287962 1288459 := bstep (se 1 (by rfl) ⟨966344, by rfl⟩ : syracuseStep 1288459 = 1932689) B1932689
theorem B2902283 : Blo 1287962 2902283 := bstep (se 1 (by rfl) ⟨2176712, by rfl⟩ : syracuseStep 2902283 = 4353425) B4353425
theorem B5507345 : Blo 1287962 5507345 := bstep (se 2 (by rfl) ⟨2065254, by rfl⟩ : syracuseStep 5507345 = 4130509) B4130509
theorem B1288471 : Blo 1287962 1288471 := bstep (se 1 (by rfl) ⟨966353, by rfl⟩ : syracuseStep 1288471 = 1932707) B1932707
theorem B1288491 : Blo 1287962 1288491 := bstep (se 1 (by rfl) ⟨966368, by rfl⟩ : syracuseStep 1288491 = 1932737) B1932737
theorem B1288503 : Blo 1287962 1288503 := bstep (se 1 (by rfl) ⟨966377, by rfl⟩ : syracuseStep 1288503 = 1932755) B1932755
theorem B2902337 : Blo 1287962 2902337 := bstep (se 2 (by rfl) ⟨1088376, by rfl⟩ : syracuseStep 2902337 = 2176753) B2176753
theorem B1288523 : Blo 1287962 1288523 := bstep (se 1 (by rfl) ⟨966392, by rfl⟩ : syracuseStep 1288523 = 1932785) B1932785
theorem B1288535 : Blo 1287962 1288535 := bstep (se 1 (by rfl) ⟨966401, by rfl⟩ : syracuseStep 1288535 = 1932803) B1932803
theorem B4647257 : Blo 1287962 4647257 := bstep (se 2 (by rfl) ⟨1742721, by rfl⟩ : syracuseStep 4647257 = 3485443) B3485443
theorem B4352345 : Blo 1287962 4352345 := bstep (se 2 (by rfl) ⟨1632129, by rfl⟩ : syracuseStep 4352345 = 3264259) B3264259
theorem B1288555 : Blo 1287962 1288555 := bstep (se 1 (by rfl) ⟨966416, by rfl⟩ : syracuseStep 1288555 = 1932833) B1932833
theorem B1288567 : Blo 1287962 1288567 := bstep (se 1 (by rfl) ⟨966425, by rfl⟩ : syracuseStep 1288567 = 1932851) B1932851
theorem B1288587 : Blo 1287962 1288587 := bstep (se 1 (by rfl) ⟨966440, by rfl⟩ : syracuseStep 1288587 = 1932881) B1932881
theorem B1288599 : Blo 1287962 1288599 := bstep (se 1 (by rfl) ⟨966449, by rfl⟩ : syracuseStep 1288599 = 1932899) B1932899
theorem B1288619 : Blo 1287962 1288619 := bstep (se 1 (by rfl) ⟨966464, by rfl⟩ : syracuseStep 1288619 = 1932929) B1932929
theorem B4647341 : Blo 1287962 4647341 := bstep (se 3 (by rfl) ⟨871376, by rfl⟩ : syracuseStep 4647341 = 1742753) B1742753
theorem B1288631 : Blo 1287962 1288631 := bstep (se 1 (by rfl) ⟨966473, by rfl⟩ : syracuseStep 1288631 = 1932947) B1932947
theorem B3262913 : Blo 1287962 3262913 := bstep (se 2 (by rfl) ⟨1223592, by rfl⟩ : syracuseStep 3262913 = 2447185) B2447185
theorem B1288651 : Blo 1287962 1288651 := bstep (se 1 (by rfl) ⟨966488, by rfl⟩ : syracuseStep 1288651 = 1932977) B1932977
theorem B1288663 : Blo 1287962 1288663 := bstep (se 1 (by rfl) ⟨966497, by rfl⟩ : syracuseStep 1288663 = 1932995) B1932995
theorem B1288683 : Blo 1287962 1288683 := bstep (se 1 (by rfl) ⟨966512, by rfl⟩ : syracuseStep 1288683 = 1933025) B1933025
theorem B1288695 : Blo 1287962 1288695 := bstep (se 1 (by rfl) ⟨966521, by rfl⟩ : syracuseStep 1288695 = 1933043) B1933043
theorem B1288715 : Blo 1287962 1288715 := bstep (se 1 (by rfl) ⟨966536, by rfl⟩ : syracuseStep 1288715 = 1933073) B1933073
theorem B1288727 : Blo 1287962 1288727 := bstep (se 1 (by rfl) ⟨966545, by rfl⟩ : syracuseStep 1288727 = 1933091) B1933091
theorem B1288747 : Blo 1287962 1288747 := bstep (se 1 (by rfl) ⟨966560, by rfl⟩ : syracuseStep 1288747 = 1933121) B1933121
theorem B5229107 : Blo 1287962 5229107 := bstep (se 1 (by rfl) ⟨3921830, by rfl⟩ : syracuseStep 5229107 = 7843661) B7843661
theorem B1288759 : Blo 1287962 1288759 := bstep (se 1 (by rfl) ⟨966569, by rfl⟩ : syracuseStep 1288759 = 1933139) B1933139
theorem B1288779 : Blo 1287962 1288779 := bstep (se 1 (by rfl) ⟨966584, by rfl⟩ : syracuseStep 1288779 = 1933169) B1933169
theorem B1288791 : Blo 1287962 1288791 := bstep (se 1 (by rfl) ⟨966593, by rfl⟩ : syracuseStep 1288791 = 1933187) B1933187
theorem B1288811 : Blo 1287962 1288811 := bstep (se 1 (by rfl) ⟨966608, by rfl⟩ : syracuseStep 1288811 = 1933217) B1933217
theorem B1288823 : Blo 1287962 1288823 := bstep (se 1 (by rfl) ⟨966617, by rfl⟩ : syracuseStep 1288823 = 1933235) B1933235
theorem B1288843 : Blo 1287962 1288843 := bstep (se 1 (by rfl) ⟨966632, by rfl⟩ : syracuseStep 1288843 = 1933265) B1933265
theorem B1288855 : Blo 1287962 1288855 := bstep (se 1 (by rfl) ⟨966641, by rfl⟩ : syracuseStep 1288855 = 1933283) B1933283
theorem B1288875 : Blo 1287962 1288875 := bstep (se 1 (by rfl) ⟨966656, by rfl⟩ : syracuseStep 1288875 = 1933313) B1933313
theorem B1288887 : Blo 1287962 1288887 := bstep (se 1 (by rfl) ⟨966665, by rfl⟩ : syracuseStep 1288887 = 1933331) B1933331
theorem B1288907 : Blo 1287962 1288907 := bstep (se 1 (by rfl) ⟨966680, by rfl⟩ : syracuseStep 1288907 = 1933361) B1933361
theorem B2173655 : Blo 1287962 2173655 := bstep (se 1 (by rfl) ⟨1630241, by rfl⟩ : syracuseStep 2173655 = 3260483) B3260483
theorem B1288919 : Blo 1287962 1288919 := bstep (se 1 (by rfl) ⟨966689, by rfl⟩ : syracuseStep 1288919 = 1933379) B1933379
theorem B3672793 : Blo 1287962 3672793 := bstep (se 2 (by rfl) ⟨1377297, by rfl⟩ : syracuseStep 3672793 = 2754595) B2754595
theorem B1288939 : Blo 1287962 1288939 := bstep (se 1 (by rfl) ⟨966704, by rfl⟩ : syracuseStep 1288939 = 1933409) B1933409
theorem B1288951 : Blo 1287962 1288951 := bstep (se 1 (by rfl) ⟨966713, by rfl⟩ : syracuseStep 1288951 = 1933427) B1933427
theorem B4893443 : Blo 1287962 4893443 := bstep (se 1 (by rfl) ⟨3670082, by rfl⟩ : syracuseStep 4893443 = 7340165) B7340165
theorem B19852037 : Blo 1287962 19852037 := bstep (se 4 (by rfl) ⟨1861128, by rfl⟩ : syracuseStep 19852037 = 3722257) B3722257
theorem B1288971 : Blo 1287962 1288971 := bstep (se 1 (by rfl) ⟨966728, by rfl⟩ : syracuseStep 1288971 = 1933457) B1933457
theorem B1288983 : Blo 1287962 1288983 := bstep (se 1 (by rfl) ⟨966737, by rfl⟩ : syracuseStep 1288983 = 1933475) B1933475
theorem B1289003 : Blo 1287962 1289003 := bstep (se 1 (by rfl) ⟨966752, by rfl⟩ : syracuseStep 1289003 = 1933505) B1933505
theorem B1289015 : Blo 1287962 1289015 := bstep (se 1 (by rfl) ⟨966761, by rfl⟩ : syracuseStep 1289015 = 1933523) B1933523
theorem B1289035 : Blo 1287962 1289035 := bstep (se 1 (by rfl) ⟨966776, by rfl⟩ : syracuseStep 1289035 = 1933553) B1933553
theorem B2173783 : Blo 1287962 2173783 := bstep (se 1 (by rfl) ⟨1630337, by rfl⟩ : syracuseStep 2173783 = 3260675) B3260675
theorem B1289047 : Blo 1287962 1289047 := bstep (se 1 (by rfl) ⟨966785, by rfl⟩ : syracuseStep 1289047 = 1933571) B1933571
theorem B1289067 : Blo 1287962 1289067 := bstep (se 1 (by rfl) ⟨966800, by rfl⟩ : syracuseStep 1289067 = 1933601) B1933601
theorem B1289079 : Blo 1287962 1289079 := bstep (se 1 (by rfl) ⟨966809, by rfl⟩ : syracuseStep 1289079 = 1933619) B1933619
theorem B1289099 : Blo 1287962 1289099 := bstep (se 1 (by rfl) ⟨966824, by rfl⟩ : syracuseStep 1289099 = 1933649) B1933649
theorem B1289111 : Blo 1287962 1289111 := bstep (se 1 (by rfl) ⟨966833, by rfl⟩ : syracuseStep 1289111 = 1933667) B1933667
theorem B1289131 : Blo 1287962 1289131 := bstep (se 1 (by rfl) ⟨966848, by rfl⟩ : syracuseStep 1289131 = 1933697) B1933697
theorem B22023089 : Blo 1287962 22023089 := bstep (se 2 (by rfl) ⟨8258658, by rfl⟩ : syracuseStep 22023089 = 16517317) B16517317
theorem B1289143 : Blo 1287962 1289143 := bstep (se 1 (by rfl) ⟨966857, by rfl⟩ : syracuseStep 1289143 = 1933715) B1933715
theorem B1289163 : Blo 1287962 1289163 := bstep (se 1 (by rfl) ⟨966872, by rfl⟩ : syracuseStep 1289163 = 1933745) B1933745
theorem B1289175 : Blo 1287962 1289175 := bstep (se 1 (by rfl) ⟨966881, by rfl⟩ : syracuseStep 1289175 = 1933763) B1933763
theorem B3263449 : Blo 1287962 3263449 := bstep (se 2 (by rfl) ⟨1223793, by rfl⟩ : syracuseStep 3263449 = 2447587) B2447587
theorem B1289195 : Blo 1287962 1289195 := bstep (se 1 (by rfl) ⟨966896, by rfl⟩ : syracuseStep 1289195 = 1933793) B1933793
theorem B1289207 : Blo 1287962 1289207 := bstep (se 1 (by rfl) ⟨966905, by rfl⟩ : syracuseStep 1289207 = 1933811) B1933811
theorem B1289227 : Blo 1287962 1289227 := bstep (se 1 (by rfl) ⟨966920, by rfl⟩ : syracuseStep 1289227 = 1933841) B1933841
theorem B1289239 : Blo 1287962 1289239 := bstep (se 1 (by rfl) ⟨966929, by rfl⟩ : syracuseStep 1289239 = 1933859) B1933859
theorem B4353047 : Blo 1287962 4353047 := bstep (se 1 (by rfl) ⟨3264785, by rfl⟩ : syracuseStep 4353047 = 6529571) B6529571
theorem B1289259 : Blo 1287962 1289259 := bstep (se 1 (by rfl) ⟨966944, by rfl⟩ : syracuseStep 1289259 = 1933889) B1933889
theorem B1289271 : Blo 1287962 1289271 := bstep (se 1 (by rfl) ⟨966953, by rfl⟩ : syracuseStep 1289271 = 1933907) B1933907
theorem B11013185 : Blo 1287962 11013185 := bstep (se 2 (by rfl) ⟨4129944, by rfl⟩ : syracuseStep 11013185 = 8259889) B8259889
theorem B31771723 : Blo 1287962 31771723 := bstep (se 1 (by rfl) ⟨23828792, by rfl⟩ : syracuseStep 31771723 = 47657585) B47657585
theorem B1289291 : Blo 1287962 1289291 := bstep (se 1 (by rfl) ⟨966968, by rfl⟩ : syracuseStep 1289291 = 1933937) B1933937
theorem B1289303 : Blo 1287962 1289303 := bstep (se 1 (by rfl) ⟨966977, by rfl⟩ : syracuseStep 1289303 = 1933955) B1933955
theorem B3673181 : Blo 1287962 3673181 := bstep (se 3 (by rfl) ⟨688721, by rfl⟩ : syracuseStep 3673181 = 1377443) B1377443
theorem B1289323 : Blo 1287962 1289323 := bstep (se 1 (by rfl) ⟨966992, by rfl⟩ : syracuseStep 1289323 = 1933985) B1933985
theorem B1289335 : Blo 1287962 1289335 := bstep (se 1 (by rfl) ⟨967001, by rfl⟩ : syracuseStep 1289335 = 1934003) B1934003
theorem B1289355 : Blo 1287962 1289355 := bstep (se 1 (by rfl) ⟨967016, by rfl⟩ : syracuseStep 1289355 = 1934033) B1934033
theorem B1289367 : Blo 1287962 1289367 := bstep (se 1 (by rfl) ⟨967025, by rfl⟩ : syracuseStep 1289367 = 1934051) B1934051
theorem B1289387 : Blo 1287962 1289387 := bstep (se 1 (by rfl) ⟨967040, by rfl⟩ : syracuseStep 1289387 = 1934081) B1934081
theorem B5508269 : Blo 1287962 5508269 := bstep (se 3 (by rfl) ⟨1032800, by rfl⟩ : syracuseStep 5508269 = 2065601) B2065601
theorem B1289399 : Blo 1287962 1289399 := bstep (se 1 (by rfl) ⟨967049, by rfl⟩ : syracuseStep 1289399 = 1934099) B1934099
theorem B1289419 : Blo 1287962 1289419 := bstep (se 1 (by rfl) ⟨967064, by rfl⟩ : syracuseStep 1289419 = 1934129) B1934129
theorem B1289431 : Blo 1287962 1289431 := bstep (se 1 (by rfl) ⟨967073, by rfl⟩ : syracuseStep 1289431 = 1934147) B1934147
theorem B1764569 : Blo 1287962 1764569 := bstep (se 2 (by rfl) ⟨661713, by rfl⟩ : syracuseStep 1764569 = 1323427) B1323427
theorem B1289451 : Blo 1287962 1289451 := bstep (se 1 (by rfl) ⟨967088, by rfl⟩ : syracuseStep 1289451 = 1934177) B1934177
theorem B1289463 : Blo 1287962 1289463 := bstep (se 1 (by rfl) ⟨967097, by rfl⟩ : syracuseStep 1289463 = 1934195) B1934195
theorem B1289483 : Blo 1287962 1289483 := bstep (se 1 (by rfl) ⟨967112, by rfl⟩ : syracuseStep 1289483 = 1934225) B1934225
theorem B1289495 : Blo 1287962 1289495 := bstep (se 1 (by rfl) ⟨967121, by rfl⟩ : syracuseStep 1289495 = 1934243) B1934243
theorem B1289515 : Blo 1287962 1289515 := bstep (se 1 (by rfl) ⟨967136, by rfl⟩ : syracuseStep 1289515 = 1934273) B1934273
theorem B1289527 : Blo 1287962 1289527 := bstep (se 1 (by rfl) ⟨967145, by rfl⟩ : syracuseStep 1289527 = 1934291) B1934291
theorem B6524225 : Blo 1287962 6524225 := bstep (se 2 (by rfl) ⟨2446584, by rfl⟩ : syracuseStep 6524225 = 4893169) B4893169
theorem B1289547 : Blo 1287962 1289547 := bstep (se 1 (by rfl) ⟨967160, by rfl⟩ : syracuseStep 1289547 = 1934321) B1934321
theorem B1289559 : Blo 1287962 1289559 := bstep (se 1 (by rfl) ⟨967169, by rfl⟩ : syracuseStep 1289559 = 1934339) B1934339
theorem B1289579 : Blo 1287962 1289579 := bstep (se 1 (by rfl) ⟨967184, by rfl⟩ : syracuseStep 1289579 = 1934369) B1934369
theorem B1289591 : Blo 1287962 1289591 := bstep (se 1 (by rfl) ⟨967193, by rfl⟩ : syracuseStep 1289591 = 1934387) B1934387
theorem B9792899 : Blo 1287962 9792899 := bstep (se 1 (by rfl) ⟨7344674, by rfl⟩ : syracuseStep 9792899 = 14689349) B14689349
theorem B1289611 : Blo 1287962 1289611 := bstep (se 1 (by rfl) ⟨967208, by rfl⟩ : syracuseStep 1289611 = 1934417) B1934417
theorem B1289623 : Blo 1287962 1289623 := bstep (se 1 (by rfl) ⟨967217, by rfl⟩ : syracuseStep 1289623 = 1934435) B1934435
theorem B1306027 : Blo 1287962 1306027 := bstep (se 1 (by rfl) ⟨979520, by rfl⟩ : syracuseStep 1306027 = 1959041) B1959041
theorem B1289643 : Blo 1287962 1289643 := bstep (se 1 (by rfl) ⟨967232, by rfl⟩ : syracuseStep 1289643 = 1934465) B1934465
theorem B1289655 : Blo 1287962 1289655 := bstep (se 1 (by rfl) ⟨967241, by rfl⟩ : syracuseStep 1289655 = 1934483) B1934483
theorem B2174411 : Blo 1287962 2174411 := bstep (se 1 (by rfl) ⟨1630808, by rfl⟩ : syracuseStep 2174411 = 3261617) B3261617
theorem B1289675 : Blo 1287962 1289675 := bstep (se 1 (by rfl) ⟨967256, by rfl⟩ : syracuseStep 1289675 = 1934513) B1934513
theorem B1289687 : Blo 1287962 1289687 := bstep (se 1 (by rfl) ⟨967265, by rfl⟩ : syracuseStep 1289687 = 1934531) B1934531
theorem B1289707 : Blo 1287962 1289707 := bstep (se 1 (by rfl) ⟨967280, by rfl⟩ : syracuseStep 1289707 = 1934561) B1934561
theorem B1289719 : Blo 1287962 1289719 := bstep (se 1 (by rfl) ⟨967289, by rfl⟩ : syracuseStep 1289719 = 1934579) B1934579
theorem B1289739 : Blo 1287962 1289739 := bstep (se 1 (by rfl) ⟨967304, by rfl⟩ : syracuseStep 1289739 = 1934609) B1934609
theorem B33476113 : Blo 1287962 33476113 := bstep (se 2 (by rfl) ⟨12553542, by rfl⟩ : syracuseStep 33476113 = 25107085) B25107085
theorem B1289751 : Blo 1287962 1289751 := bstep (se 1 (by rfl) ⟨967313, by rfl⟩ : syracuseStep 1289751 = 1934627) B1934627
theorem B1289771 : Blo 1287962 1289771 := bstep (se 1 (by rfl) ⟨967328, by rfl⟩ : syracuseStep 1289771 = 1934657) B1934657
theorem B4353587 : Blo 1287962 4353587 := bstep (se 1 (by rfl) ⟨3265190, by rfl⟩ : syracuseStep 4353587 = 6530381) B6530381
theorem B1289783 : Blo 1287962 1289783 := bstep (se 1 (by rfl) ⟨967337, by rfl⟩ : syracuseStep 1289783 = 1934675) B1934675
theorem B2174539 : Blo 1287962 2174539 := bstep (se 1 (by rfl) ⟨1630904, by rfl⟩ : syracuseStep 2174539 = 3261809) B3261809
theorem B1289803 : Blo 1287962 1289803 := bstep (se 1 (by rfl) ⟨967352, by rfl⟩ : syracuseStep 1289803 = 1934705) B1934705
theorem B1289815 : Blo 1287962 1289815 := bstep (se 1 (by rfl) ⟨967361, by rfl⟩ : syracuseStep 1289815 = 1934723) B1934723
theorem B1289835 : Blo 1287962 1289835 := bstep (se 1 (by rfl) ⟨967376, by rfl⟩ : syracuseStep 1289835 = 1934753) B1934753
theorem B1289847 : Blo 1287962 1289847 := bstep (se 1 (by rfl) ⟨967385, by rfl⟩ : syracuseStep 1289847 = 1934771) B1934771
theorem B1289867 : Blo 1287962 1289867 := bstep (se 1 (by rfl) ⟨967400, by rfl⟩ : syracuseStep 1289867 = 1934801) B1934801
theorem B7835287 : Blo 1287962 7835287 := bstep (se 1 (by rfl) ⟨5876465, by rfl⟩ : syracuseStep 7835287 = 11752931) B11752931
theorem B1289879 : Blo 1287962 1289879 := bstep (se 1 (by rfl) ⟨967409, by rfl⟩ : syracuseStep 1289879 = 1934819) B1934819
theorem B1289899 : Blo 1287962 1289899 := bstep (se 1 (by rfl) ⟨967424, by rfl⟩ : syracuseStep 1289899 = 1934849) B1934849
theorem B1289911 : Blo 1287962 1289911 := bstep (se 1 (by rfl) ⟨967433, by rfl⟩ : syracuseStep 1289911 = 1934867) B1934867
theorem B1289931 : Blo 1287962 1289931 := bstep (se 1 (by rfl) ⟨967448, by rfl⟩ : syracuseStep 1289931 = 1934897) B1934897
theorem B1289943 : Blo 1287962 1289943 := bstep (se 1 (by rfl) ⟨967457, by rfl⟩ : syracuseStep 1289943 = 1934915) B1934915
theorem B2174681 : Blo 1287962 2174681 := bstep (se 2 (by rfl) ⟨815505, by rfl⟩ : syracuseStep 2174681 = 1631011) B1631011
theorem B9785123 : Blo 1287962 9785123 := bstep (se 1 (by rfl) ⟨7338842, by rfl⟩ : syracuseStep 9785123 = 14677685) B14677685
theorem B9916235 : Blo 1287962 9916235 := bstep (se 1 (by rfl) ⟨7437176, by rfl⟩ : syracuseStep 9916235 = 14874353) B14874353
theorem B2174809 : Blo 1287962 2174809 := bstep (se 2 (by rfl) ⟨815553, by rfl⟩ : syracuseStep 2174809 = 1631107) B1631107
theorem B7942067 : Blo 1287962 7942067 := bstep (se 1 (by rfl) ⟨5956550, by rfl⟩ : syracuseStep 7942067 = 11913101) B11913101
theorem B3264563 : Blo 1287962 3264563 := bstep (se 1 (by rfl) ⟨2448422, by rfl⟩ : syracuseStep 3264563 = 4896845) B4896845
theorem B5222551 : Blo 1287962 5222551 := bstep (se 1 (by rfl) ⟨3916913, by rfl⟩ : syracuseStep 5222551 = 7833827) B7833827
theorem B2445491 : Blo 1287962 2445491 := bstep (se 1 (by rfl) ⟨1834118, by rfl⟩ : syracuseStep 2445491 = 3668237) B3668237
theorem B2445643 : Blo 1287962 2445643 := bstep (se 1 (by rfl) ⟨1834232, by rfl⟩ : syracuseStep 2445643 = 3668465) B3668465
theorem B9417035 : Blo 1287962 9417035 := bstep (se 1 (by rfl) ⟨7062776, by rfl⟩ : syracuseStep 9417035 = 14125553) B14125553
theorem B3264857 : Blo 1287962 3264857 := bstep (se 2 (by rfl) ⟨1224321, by rfl⟩ : syracuseStep 3264857 = 2448643) B2448643
theorem B2175383 : Blo 1287962 2175383 := bstep (se 1 (by rfl) ⟨1631537, by rfl⟩ : syracuseStep 2175383 = 3263075) B3263075
theorem B2650585 : Blo 1287962 2650585 := bstep (se 2 (by rfl) ⟨993969, by rfl⟩ : syracuseStep 2650585 = 1987939) B1987939
theorem B2175511 : Blo 1287962 2175511 := bstep (se 1 (by rfl) ⟨1631633, by rfl⟩ : syracuseStep 2175511 = 3263267) B3263267
theorem B5509721 : Blo 1287962 5509721 := bstep (se 2 (by rfl) ⟨2066145, by rfl⟩ : syracuseStep 5509721 = 4132291) B4132291
theorem B2445977 : Blo 1287962 2445977 := bstep (se 2 (by rfl) ⟨917241, by rfl⟩ : syracuseStep 2445977 = 1834483) B1834483
theorem B7344857 : Blo 1287962 7344857 := bstep (se 2 (by rfl) ⟨2754321, by rfl⟩ : syracuseStep 7344857 = 5508643) B5508643
theorem B23516081 : Blo 1287962 23516081 := bstep (se 2 (by rfl) ⟨8818530, by rfl⟩ : syracuseStep 23516081 = 17637061) B17637061
theorem B2937779 : Blo 1287962 2937779 := bstep (se 1 (by rfl) ⟨2203334, by rfl⟩ : syracuseStep 2937779 = 4406669) B4406669
theorem B4346945 : Blo 1287962 4346945 := bstep (se 2 (by rfl) ⟨1630104, by rfl⟩ : syracuseStep 4346945 = 3260209) B3260209
theorem B2937971 : Blo 1287962 2937971 := bstep (se 1 (by rfl) ⟨2203478, by rfl⟩ : syracuseStep 2937971 = 4406957) B4406957
theorem B2479243 : Blo 1287962 2479243 := bstep (se 1 (by rfl) ⟨1859432, by rfl⟩ : syracuseStep 2479243 = 3718865) B3718865
theorem B2176139 : Blo 1287962 2176139 := bstep (se 1 (by rfl) ⟨1632104, by rfl⟩ : syracuseStep 2176139 = 3264209) B3264209
theorem B1987787 : Blo 1287962 1987787 := bstep (se 1 (by rfl) ⟨1490840, by rfl⟩ : syracuseStep 1987787 = 2981681) B2981681
theorem B6526169 : Blo 1287962 6526169 := bstep (se 2 (by rfl) ⟨2447313, by rfl⟩ : syracuseStep 6526169 = 4894627) B4894627
theorem B2176267 : Blo 1287962 2176267 := bstep (se 1 (by rfl) ⟨1632200, by rfl⟩ : syracuseStep 2176267 = 3264401) B3264401
theorem B2446615 : Blo 1287962 2446615 := bstep (se 1 (by rfl) ⟨1834961, by rfl⟩ : syracuseStep 2446615 = 3669923) B3669923
theorem B1742105 : Blo 1287962 1742105 := bstep (se 2 (by rfl) ⟨653289, by rfl⟩ : syracuseStep 1742105 = 1306579) B1306579
theorem B2176409 : Blo 1287962 2176409 := bstep (se 2 (by rfl) ⟨816153, by rfl⟩ : syracuseStep 2176409 = 1632307) B1632307
theorem B2176537 : Blo 1287962 2176537 := bstep (se 2 (by rfl) ⟨816201, by rfl⟩ : syracuseStep 2176537 = 1632403) B1632403
theorem B4413017 : Blo 1287962 4413017 := bstep (se 2 (by rfl) ⟨1654881, by rfl⟩ : syracuseStep 4413017 = 3309763) B3309763
theorem B4347485 : Blo 1287962 4347485 := bstep (se 3 (by rfl) ⟨815153, by rfl⟩ : syracuseStep 4347485 = 1630307) B1630307
theorem B4896557 : Blo 1287962 4896557 := bstep (se 3 (by rfl) ⟨918104, by rfl⟩ : syracuseStep 4896557 = 1836209) B1836209
theorem B3667805 : Blo 1287962 3667805 := bstep (se 3 (by rfl) ⟨687713, by rfl⟩ : syracuseStep 3667805 = 1375427) B1375427
theorem B1570699 : Blo 1287962 1570699 := bstep (se 1 (by rfl) ⟨1178024, by rfl⟩ : syracuseStep 1570699 = 2356049) B2356049
theorem B5502937 : Blo 1287962 5502937 := bstep (se 2 (by rfl) ⟨2063601, by rfl⟩ : syracuseStep 5502937 = 4127203) B4127203
theorem B2897945 : Blo 1287962 2897945 := bstep (se 2 (by rfl) ⟨1086729, by rfl⟩ : syracuseStep 2897945 = 2173459) B2173459
theorem B2447435 : Blo 1287962 2447435 := bstep (se 1 (by rfl) ⟨1835576, by rfl⟩ : syracuseStep 2447435 = 3671153) B3671153
theorem B2898035 : Blo 1287962 2898035 := bstep (se 1 (by rfl) ⟨2173526, by rfl⟩ : syracuseStep 2898035 = 4347053) B4347053
theorem B2447489 : Blo 1287962 2447489 := bstep (se 2 (by rfl) ⟨917808, by rfl⟩ : syracuseStep 2447489 = 1835617) B1835617
theorem B2898071 : Blo 1287962 2898071 := bstep (se 1 (by rfl) ⟨2173553, by rfl⟩ : syracuseStep 2898071 = 4347107) B4347107
theorem B3094807 : Blo 1287962 3094807 := bstep (se 1 (by rfl) ⟨2321105, by rfl⟩ : syracuseStep 3094807 = 4642211) B4642211
theorem B8255789 : Blo 1287962 8255789 := bstep (se 3 (by rfl) ⟨1547960, by rfl⟩ : syracuseStep 8255789 = 3095921) B3095921
theorem B7346497 : Blo 1287962 7346497 := bstep (se 2 (by rfl) ⟨2754936, by rfl⟩ : syracuseStep 7346497 = 5509873) B5509873
theorem B2898251 : Blo 1287962 2898251 := bstep (se 1 (by rfl) ⟨2173688, by rfl⟩ : syracuseStep 2898251 = 4347377) B4347377
theorem B11163997 : Blo 1287962 11163997 := bstep (se 3 (by rfl) ⟨2093249, by rfl⟩ : syracuseStep 11163997 = 4186499) B4186499
theorem B23517539 : Blo 1287962 23517539 := bstep (se 1 (by rfl) ⟨17638154, by rfl⟩ : syracuseStep 23517539 = 35276309) B35276309
theorem B2898305 : Blo 1287962 2898305 := bstep (se 2 (by rfl) ⟨1086864, by rfl⟩ : syracuseStep 2898305 = 2173729) B2173729
theorem B13236659 : Blo 1287962 13236659 := bstep (se 1 (by rfl) ⟨9927494, by rfl⟩ : syracuseStep 13236659 = 19854989) B19854989
theorem B3021337 : Blo 1287962 3021337 := bstep (se 2 (by rfl) ⟨1133001, by rfl⟩ : syracuseStep 3021337 = 2266003) B2266003
theorem B4897331 : Blo 1287962 4897331 := bstep (se 1 (by rfl) ⟨3672998, by rfl⟩ : syracuseStep 4897331 = 7345997) B7345997
theorem B2751041 : Blo 1287962 2751041 := bstep (se 2 (by rfl) ⟨1031640, by rfl⟩ : syracuseStep 2751041 = 2063281) B2063281
theorem B2898521 : Blo 1287962 2898521 := bstep (se 2 (by rfl) ⟨1086945, by rfl⟩ : syracuseStep 2898521 = 2173891) B2173891
theorem B2898611 : Blo 1287962 2898611 := bstep (se 1 (by rfl) ⟨2173958, by rfl⟩ : syracuseStep 2898611 = 4347917) B4347917
theorem B4348619 : Blo 1287962 4348619 := bstep (se 1 (by rfl) ⟨3261464, by rfl⟩ : syracuseStep 4348619 = 6522929) B6522929
theorem B2898647 : Blo 1287962 2898647 := bstep (se 1 (by rfl) ⟨2173985, by rfl⟩ : syracuseStep 2898647 = 4347971) B4347971
theorem B1931993 : Blo 1287962 1931993 := bstep (se 2 (by rfl) ⟨724497, by rfl⟩ : syracuseStep 1931993 = 1448995) B1448995
theorem B6527789 : Blo 1287962 6527789 := bstep (se 3 (by rfl) ⟨1223960, by rfl⟩ : syracuseStep 6527789 = 2447921) B2447921
theorem B1932107 : Blo 1287962 1932107 := bstep (se 1 (by rfl) ⟨1449080, by rfl⟩ : syracuseStep 1932107 = 2898161) B2898161
theorem B1932119 : Blo 1287962 1932119 := bstep (se 1 (by rfl) ⟨1449089, by rfl⟩ : syracuseStep 1932119 = 2898179) B2898179
theorem B2898827 : Blo 1287962 2898827 := bstep (se 1 (by rfl) ⟨2174120, by rfl⟩ : syracuseStep 2898827 = 4348241) B4348241
theorem B2751383 : Blo 1287962 2751383 := bstep (se 1 (by rfl) ⟨2063537, by rfl⟩ : syracuseStep 2751383 = 4127075) B4127075
theorem B5503895 : Blo 1287962 5503895 := bstep (se 1 (by rfl) ⟨4127921, by rfl⟩ : syracuseStep 5503895 = 8255843) B8255843
theorem B1932185 : Blo 1287962 1932185 := bstep (se 2 (by rfl) ⟨724569, by rfl⟩ : syracuseStep 1932185 = 1449139) B1449139
theorem B5880755 : Blo 1287962 5880755 := bstep (se 1 (by rfl) ⟨4410566, by rfl⟩ : syracuseStep 5880755 = 8821133) B8821133
theorem B2898881 : Blo 1287962 2898881 := bstep (se 2 (by rfl) ⟨1087080, by rfl⟩ : syracuseStep 2898881 = 2174161) B2174161
theorem B1833931 : Blo 1287962 1833931 := bstep (se 1 (by rfl) ⟨1375448, by rfl⟩ : syracuseStep 1833931 = 2750897) B2750897
theorem B4348889 : Blo 1287962 4348889 := bstep (se 2 (by rfl) ⟨1630833, by rfl⟩ : syracuseStep 4348889 = 3261667) B3261667
theorem B1932299 : Blo 1287962 1932299 := bstep (se 1 (by rfl) ⟨1449224, by rfl⟩ : syracuseStep 1932299 = 2898449) B2898449
theorem B7339025 : Blo 1287962 7339025 := bstep (se 2 (by rfl) ⟨2752134, by rfl⟩ : syracuseStep 7339025 = 5504269) B5504269
theorem B1932311 : Blo 1287962 1932311 := bstep (se 1 (by rfl) ⟨1449233, by rfl⟩ : syracuseStep 1932311 = 2898467) B2898467
theorem B2448407 : Blo 1287962 2448407 := bstep (se 1 (by rfl) ⟨1836305, by rfl⟩ : syracuseStep 2448407 = 3672611) B3672611
theorem B1932377 : Blo 1287962 1932377 := bstep (se 2 (by rfl) ⟨724641, by rfl⟩ : syracuseStep 1932377 = 1449283) B1449283
theorem B1449067 : Blo 1287962 1449067 := bstep (se 1 (by rfl) ⟨1086800, by rfl⟩ : syracuseStep 1449067 = 2173601) B2173601
theorem B2899097 : Blo 1287962 2899097 := bstep (se 2 (by rfl) ⟨1087161, by rfl⟩ : syracuseStep 2899097 = 2174323) B2174323
theorem B1932491 : Blo 1287962 1932491 := bstep (se 1 (by rfl) ⟨1449368, by rfl⟩ : syracuseStep 1932491 = 2898737) B2898737
theorem B2751691 : Blo 1287962 2751691 := bstep (se 1 (by rfl) ⟨2063768, by rfl⟩ : syracuseStep 2751691 = 4127537) B4127537
theorem B2235595 : Blo 1287962 2235595 := bstep (se 1 (by rfl) ⟨1676696, by rfl⟩ : syracuseStep 2235595 = 3353393) B3353393
theorem B1449175 : Blo 1287962 1449175 := bstep (se 1 (by rfl) ⟨1086881, by rfl⟩ : syracuseStep 1449175 = 2173763) B2173763
theorem B1932503 : Blo 1287962 1932503 := bstep (se 1 (by rfl) ⟨1449377, by rfl⟩ : syracuseStep 1932503 = 2898755) B2898755
theorem B5881049 : Blo 1287962 5881049 := bstep (se 2 (by rfl) ⟨2205393, by rfl⟩ : syracuseStep 5881049 = 4410787) B4410787
theorem B2899187 : Blo 1287962 2899187 := bstep (se 1 (by rfl) ⟨2174390, by rfl⟩ : syracuseStep 2899187 = 4348781) B4348781
theorem B8822033 : Blo 1287962 8822033 := bstep (se 2 (by rfl) ⟨3308262, by rfl⟩ : syracuseStep 8822033 = 6616525) B6616525
theorem B2899223 : Blo 1287962 2899223 := bstep (se 1 (by rfl) ⟨2174417, by rfl⟩ : syracuseStep 2899223 = 4348835) B4348835
theorem B4128023 : Blo 1287962 4128023 := bstep (se 1 (by rfl) ⟨3096017, by rfl⟩ : syracuseStep 4128023 = 6192035) B6192035
theorem B1932569 : Blo 1287962 1932569 := bstep (se 2 (by rfl) ⟨724713, by rfl⟩ : syracuseStep 1932569 = 1449427) B1449427
theorem B1449355 : Blo 1287962 1449355 := bstep (se 1 (by rfl) ⟨1087016, by rfl⟩ : syracuseStep 1449355 = 2174033) B2174033
theorem B1932683 : Blo 1287962 1932683 := bstep (se 1 (by rfl) ⟨1449512, by rfl⟩ : syracuseStep 1932683 = 2899025) B2899025
theorem B1932695 : Blo 1287962 1932695 := bstep (se 1 (by rfl) ⟨1449521, by rfl⟩ : syracuseStep 1932695 = 2899043) B2899043
theorem B11165105 : Blo 1287962 11165105 := bstep (se 2 (by rfl) ⟨4186914, by rfl⟩ : syracuseStep 11165105 = 8373829) B8373829
theorem B2899403 : Blo 1287962 2899403 := bstep (se 1 (by rfl) ⟨2174552, by rfl⟩ : syracuseStep 2899403 = 4349105) B4349105
theorem B1932761 : Blo 1287962 1932761 := bstep (se 2 (by rfl) ⟨724785, by rfl⟩ : syracuseStep 1932761 = 1449571) B1449571
theorem B7339481 : Blo 1287962 7339481 := bstep (se 2 (by rfl) ⟨2752305, by rfl⟩ : syracuseStep 7339481 = 5504611) B5504611
theorem B1449463 : Blo 1287962 1449463 := bstep (se 1 (by rfl) ⟨1087097, by rfl⟩ : syracuseStep 1449463 = 2174195) B2174195
theorem B2899457 : Blo 1287962 2899457 := bstep (se 2 (by rfl) ⟨1087296, by rfl⟩ : syracuseStep 2899457 = 2174593) B2174593
theorem B6520337 : Blo 1287962 6520337 := bstep (se 2 (by rfl) ⟨2445126, by rfl⟩ : syracuseStep 6520337 = 4890253) B4890253
theorem B1932875 : Blo 1287962 1932875 := bstep (se 1 (by rfl) ⟨1449656, by rfl⟩ : syracuseStep 1932875 = 2899313) B2899313
theorem B1932887 : Blo 1287962 1932887 := bstep (se 1 (by rfl) ⟨1449665, by rfl⟩ : syracuseStep 1932887 = 2899331) B2899331
theorem B4349591 : Blo 1287962 4349591 := bstep (se 1 (by rfl) ⟨3262193, by rfl⟩ : syracuseStep 4349591 = 6524387) B6524387
theorem B1932953 : Blo 1287962 1932953 := bstep (se 2 (by rfl) ⟨724857, by rfl⟩ : syracuseStep 1932953 = 1449715) B1449715
theorem B1449643 : Blo 1287962 1449643 := bstep (se 1 (by rfl) ⟨1087232, by rfl⟩ : syracuseStep 1449643 = 2174465) B2174465
theorem B6520499 : Blo 1287962 6520499 := bstep (se 1 (by rfl) ⟨4890374, by rfl⟩ : syracuseStep 6520499 = 9780749) B9780749
theorem B2612915 : Blo 1287962 2612915 := bstep (se 1 (by rfl) ⟨1959686, by rfl⟩ : syracuseStep 2612915 = 3919373) B3919373
theorem B2899673 : Blo 1287962 2899673 := bstep (se 2 (by rfl) ⟨1087377, by rfl⟩ : syracuseStep 2899673 = 2174755) B2174755
theorem B7839449 : Blo 1287962 7839449 := bstep (se 2 (by rfl) ⟨2939793, by rfl⟩ : syracuseStep 7839449 = 5879587) B5879587
theorem B1933067 : Blo 1287962 1933067 := bstep (se 1 (by rfl) ⟨1449800, by rfl⟩ : syracuseStep 1933067 = 2899601) B2899601
theorem B1449751 : Blo 1287962 1449751 := bstep (se 1 (by rfl) ⟨1087313, by rfl⟩ : syracuseStep 1449751 = 2174627) B2174627
theorem B1933079 : Blo 1287962 1933079 := bstep (se 1 (by rfl) ⟨1449809, by rfl⟩ : syracuseStep 1933079 = 2899619) B2899619
theorem B2899763 : Blo 1287962 2899763 := bstep (se 1 (by rfl) ⟨2174822, by rfl⟩ : syracuseStep 2899763 = 4349645) B4349645
theorem B9674561 : Blo 1287962 9674561 := bstep (se 2 (by rfl) ⟨3627960, by rfl⟩ : syracuseStep 9674561 = 7255921) B7255921
theorem B2899799 : Blo 1287962 2899799 := bstep (se 1 (by rfl) ⟨2174849, by rfl⟩ : syracuseStep 2899799 = 4349699) B4349699
theorem B2064217 : Blo 1287962 2064217 := bstep (se 2 (by rfl) ⟨774081, by rfl⟩ : syracuseStep 2064217 = 1548163) B1548163
theorem B1933145 : Blo 1287962 1933145 := bstep (se 2 (by rfl) ⟨724929, by rfl⟩ : syracuseStep 1933145 = 1449859) B1449859
theorem B1376119 : Blo 1287962 1376119 := bstep (se 1 (by rfl) ⟨1032089, by rfl⟩ : syracuseStep 1376119 = 2064179) B2064179
theorem B4186007 : Blo 1287962 4186007 := bstep (se 1 (by rfl) ⟨3139505, by rfl⟩ : syracuseStep 4186007 = 6279011) B6279011
theorem B1449931 : Blo 1287962 1449931 := bstep (se 1 (by rfl) ⟨1087448, by rfl⟩ : syracuseStep 1449931 = 2174897) B2174897
theorem B1933259 : Blo 1287962 1933259 := bstep (se 1 (by rfl) ⟨1449944, by rfl⟩ : syracuseStep 1933259 = 2899889) B2899889
theorem B1933271 : Blo 1287962 1933271 := bstep (se 1 (by rfl) ⟨1449953, by rfl⟩ : syracuseStep 1933271 = 2899907) B2899907
theorem B2940889 : Blo 1287962 2940889 := bstep (se 2 (by rfl) ⟨1102833, by rfl⟩ : syracuseStep 2940889 = 2205667) B2205667
theorem B1933319 : Blo 1287962 1933319 := bstep (se 1 (by rfl) ⟨1449989, by rfl⟩ : syracuseStep 1933319 = 2899979) B2899979
theorem B3670049 : Blo 1287962 3670049 := bstep (se 2 (by rfl) ⟨1376268, by rfl⟩ : syracuseStep 3670049 = 2752537) B2752537
theorem B1933355 : Blo 1287962 1933355 := bstep (se 1 (by rfl) ⟨1450016, by rfl⟩ : syracuseStep 1933355 = 2900033) B2900033
theorem B6529085 : Blo 1287962 6529085 := bstep (se 3 (by rfl) ⟨1224203, by rfl⟩ : syracuseStep 6529085 = 2448407) B2448407
theorem B1933385 : Blo 1287962 1933385 := bstep (se 2 (by rfl) ⟨725019, by rfl⟩ : syracuseStep 1933385 = 1450039) B1450039
theorem B2900087 : Blo 1287962 2900087 := bstep (se 1 (by rfl) ⟨2175065, by rfl⟩ : syracuseStep 2900087 = 4350131) B4350131
theorem B1933499 : Blo 1287962 1933499 := bstep (se 1 (by rfl) ⟨1450124, by rfl⟩ : syracuseStep 1933499 = 2900249) B2900249
theorem B6963401 : Blo 1287962 6963401 := bstep (se 2 (by rfl) ⟨2611275, by rfl⟩ : syracuseStep 6963401 = 5222551) B5222551
theorem B1933559 : Blo 1287962 1933559 := bstep (se 1 (by rfl) ⟨1450169, by rfl⟩ : syracuseStep 1933559 = 2900339) B2900339
theorem B1933583 : Blo 1287962 1933583 := bstep (se 1 (by rfl) ⟨1450187, by rfl⟩ : syracuseStep 1933583 = 2900375) B2900375
theorem B1450255 : Blo 1287962 1450255 := bstep (se 1 (by rfl) ⟨1087691, by rfl⟩ : syracuseStep 1450255 = 2175383) B2175383
theorem B2900267 : Blo 1287962 2900267 := bstep (se 1 (by rfl) ⟨2175200, by rfl⟩ : syracuseStep 2900267 = 4350401) B4350401
theorem B1933625 : Blo 1287962 1933625 := bstep (se 2 (by rfl) ⟨725109, by rfl⟩ : syracuseStep 1933625 = 1450219) B1450219
theorem B6521147 : Blo 1287962 6521147 := bstep (se 1 (by rfl) ⟨4890860, by rfl⟩ : syracuseStep 6521147 = 9781721) B9781721
theorem B6275387 : Blo 1287962 6275387 := bstep (se 1 (by rfl) ⟨4706540, by rfl⟩ : syracuseStep 6275387 = 9413081) B9413081
theorem B3260807 : Blo 1287962 3260807 := bstep (se 1 (by rfl) ⟨2445605, by rfl⟩ : syracuseStep 3260807 = 4891211) B4891211
theorem B1933703 : Blo 1287962 1933703 := bstep (se 1 (by rfl) ⟨1450277, by rfl⟩ : syracuseStep 1933703 = 2900555) B2900555
theorem B11010451 : Blo 1287962 11010451 := bstep (se 1 (by rfl) ⟨8257838, by rfl⟩ : syracuseStep 11010451 = 16515677) B16515677
theorem B4129177 : Blo 1287962 4129177 := bstep (se 2 (by rfl) ⟨1548441, by rfl⟩ : syracuseStep 4129177 = 3096883) B3096883
theorem B1933739 : Blo 1287962 1933739 := bstep (se 1 (by rfl) ⟨1450304, by rfl⟩ : syracuseStep 1933739 = 2900609) B2900609
theorem B3260857 : Blo 1287962 3260857 := bstep (se 2 (by rfl) ⟨1222821, by rfl⟩ : syracuseStep 3260857 = 2445643) B2445643
theorem B1933769 : Blo 1287962 1933769 := bstep (se 2 (by rfl) ⟨725163, by rfl⟩ : syracuseStep 1933769 = 1450327) B1450327
theorem B6521309 : Blo 1287962 6521309 := bstep (se 3 (by rfl) ⟨1222745, by rfl⟩ : syracuseStep 6521309 = 2445491) B2445491
theorem B6193687 : Blo 1287962 6193687 := bstep (se 1 (by rfl) ⟨4645265, by rfl⟩ : syracuseStep 6193687 = 9290531) B9290531
theorem B5300765 : Blo 1287962 5300765 := bstep (se 3 (by rfl) ⟨993893, by rfl⟩ : syracuseStep 5300765 = 1987787) B1987787
theorem B1933883 : Blo 1287962 1933883 := bstep (se 1 (by rfl) ⟨1450412, by rfl⟩ : syracuseStep 1933883 = 2900825) B2900825
theorem B9421379 : Blo 1287962 9421379 := bstep (se 1 (by rfl) ⟨7066034, by rfl⟩ : syracuseStep 9421379 = 14132069) B14132069
theorem B1958519 : Blo 1287962 1958519 := bstep (se 1 (by rfl) ⟨1468889, by rfl⟩ : syracuseStep 1958519 = 2937779) B2937779
theorem B1933943 : Blo 1287962 1933943 := bstep (se 1 (by rfl) ⟨1450457, by rfl⟩ : syracuseStep 1933943 = 2900915) B2900915
theorem B1933967 : Blo 1287962 1933967 := bstep (se 1 (by rfl) ⟨1450475, by rfl⟩ : syracuseStep 1933967 = 2900951) B2900951
theorem B2900627 : Blo 1287962 2900627 := bstep (se 1 (by rfl) ⟨2175470, by rfl⟩ : syracuseStep 2900627 = 4350941) B4350941
theorem B1934009 : Blo 1287962 1934009 := bstep (se 2 (by rfl) ⟨725253, by rfl⟩ : syracuseStep 1934009 = 1450507) B1450507
theorem B2900681 : Blo 1287962 2900681 := bstep (se 2 (by rfl) ⟨1087755, by rfl⟩ : syracuseStep 2900681 = 2175511) B2175511
theorem B4645613 : Blo 1287962 4645613 := bstep (se 3 (by rfl) ⟨871052, by rfl⟩ : syracuseStep 4645613 = 1742105) B1742105
theorem B1958647 : Blo 1287962 1958647 := bstep (se 1 (by rfl) ⟨1468985, by rfl⟩ : syracuseStep 1958647 = 2937971) B2937971
theorem B1934087 : Blo 1287962 1934087 := bstep (se 1 (by rfl) ⟨1450565, by rfl⟩ : syracuseStep 1934087 = 2901131) B2901131
theorem B1450759 : Blo 1287962 1450759 := bstep (se 1 (by rfl) ⟨1088069, by rfl⟩ : syracuseStep 1450759 = 2176139) B2176139
theorem B6521633 : Blo 1287962 6521633 := bstep (se 2 (by rfl) ⟨2445612, by rfl⟩ : syracuseStep 6521633 = 4891225) B4891225
theorem B1934123 : Blo 1287962 1934123 := bstep (se 1 (by rfl) ⟨1450592, by rfl⟩ : syracuseStep 1934123 = 2901185) B2901185
theorem B6193979 : Blo 1287962 6193979 := bstep (se 1 (by rfl) ⟨4645484, by rfl⟩ : syracuseStep 6193979 = 9290969) B9290969
theorem B4350779 : Blo 1287962 4350779 := bstep (se 1 (by rfl) ⟨3263084, by rfl⟩ : syracuseStep 4350779 = 6526169) B6526169
theorem B3097403 : Blo 1287962 3097403 := bstep (se 1 (by rfl) ⟨2323052, by rfl⟩ : syracuseStep 3097403 = 4646105) B4646105
theorem B1934153 : Blo 1287962 1934153 := bstep (se 2 (by rfl) ⟨725307, by rfl⟩ : syracuseStep 1934153 = 1450615) B1450615
theorem B2753399 : Blo 1287962 2753399 := bstep (se 1 (by rfl) ⟨2065049, by rfl⟩ : syracuseStep 2753399 = 4130099) B4130099
theorem B1934267 : Blo 1287962 1934267 := bstep (se 1 (by rfl) ⟨1450700, by rfl⟩ : syracuseStep 1934267 = 2901401) B2901401
theorem B1450939 : Blo 1287962 1450939 := bstep (se 1 (by rfl) ⟨1088204, by rfl⟩ : syracuseStep 1450939 = 2176409) B2176409
theorem B8258507 : Blo 1287962 8258507 := bstep (se 1 (by rfl) ⟨6193880, by rfl⟩ : syracuseStep 8258507 = 12387761) B12387761
theorem B1934327 : Blo 1287962 1934327 := bstep (se 1 (by rfl) ⟨1450745, by rfl⟩ : syracuseStep 1934327 = 2901491) B2901491
theorem B3261455 : Blo 1287962 3261455 := bstep (se 1 (by rfl) ⟨2446091, by rfl⟩ : syracuseStep 3261455 = 4892183) B4892183
theorem B1934351 : Blo 1287962 1934351 := bstep (se 1 (by rfl) ⟨1450763, by rfl⟩ : syracuseStep 1934351 = 2901527) B2901527
theorem B1934393 : Blo 1287962 1934393 := bstep (se 2 (by rfl) ⟨725397, by rfl⟩ : syracuseStep 1934393 = 1450795) B1450795
theorem B2942011 : Blo 1287962 2942011 := bstep (se 1 (by rfl) ⟨2206508, by rfl⟩ : syracuseStep 2942011 = 4413017) B4413017
theorem B1590391 : Blo 1287962 1590391 := bstep (se 1 (by rfl) ⟨1192793, by rfl⟩ : syracuseStep 1590391 = 2385587) B2385587
theorem B1934471 : Blo 1287962 1934471 := bstep (se 1 (by rfl) ⟨1450853, by rfl⟩ : syracuseStep 1934471 = 2901707) B2901707
theorem B1934507 : Blo 1287962 1934507 := bstep (se 1 (by rfl) ⟨1450880, by rfl⟩ : syracuseStep 1934507 = 2901761) B2901761
theorem B1934537 : Blo 1287962 1934537 := bstep (se 2 (by rfl) ⟨725451, by rfl⟩ : syracuseStep 1934537 = 1450903) B1450903
theorem B5506319 : Blo 1287962 5506319 := bstep (se 1 (by rfl) ⟨4129739, by rfl⟩ : syracuseStep 5506319 = 8259479) B8259479
theorem B4351265 : Blo 1287962 4351265 := bstep (se 2 (by rfl) ⟨1631724, by rfl⟩ : syracuseStep 4351265 = 3263449) B3263449
theorem B1934651 : Blo 1287962 1934651 := bstep (se 1 (by rfl) ⟨1450988, by rfl⟩ : syracuseStep 1934651 = 2901977) B2901977
theorem B1934711 : Blo 1287962 1934711 := bstep (se 1 (by rfl) ⟨1451033, by rfl⟩ : syracuseStep 1934711 = 2902067) B2902067
theorem B2901383 : Blo 1287962 2901383 := bstep (se 1 (by rfl) ⟨2176037, by rfl⟩ : syracuseStep 2901383 = 4352075) B4352075
theorem B1934735 : Blo 1287962 1934735 := bstep (se 1 (by rfl) ⟨1451051, by rfl⟩ : syracuseStep 1934735 = 2902103) B2902103
theorem B1631659 : Blo 1287962 1631659 := bstep (se 1 (by rfl) ⟨1223744, by rfl⟩ : syracuseStep 1631659 = 2447489) B2447489
theorem B42362297 : Blo 1287962 42362297 := bstep (se 2 (by rfl) ⟨15885861, by rfl⟩ : syracuseStep 42362297 = 31771723) B31771723
theorem B1934777 : Blo 1287962 1934777 := bstep (se 2 (by rfl) ⟨725541, by rfl⟩ : syracuseStep 1934777 = 1451083) B1451083
theorem B1934855 : Blo 1287962 1934855 := bstep (se 1 (by rfl) ⟨1451141, by rfl⟩ : syracuseStep 1934855 = 2902283) B2902283
theorem B3671563 : Blo 1287962 3671563 := bstep (se 1 (by rfl) ⟨2753672, by rfl⟩ : syracuseStep 3671563 = 5507345) B5507345
theorem B1934891 : Blo 1287962 1934891 := bstep (se 1 (by rfl) ⟨1451168, by rfl⟩ : syracuseStep 1934891 = 2902337) B2902337
theorem B3098171 : Blo 1287962 3098171 := bstep (se 1 (by rfl) ⟨2323628, by rfl⟩ : syracuseStep 3098171 = 4647257) B4647257
theorem B2901563 : Blo 1287962 2901563 := bstep (se 1 (by rfl) ⟨2176172, by rfl⟩ : syracuseStep 2901563 = 4352345) B4352345
theorem B1934921 : Blo 1287962 1934921 := bstep (se 2 (by rfl) ⟨725595, by rfl⟩ : syracuseStep 1934921 = 1451191) B1451191
theorem B8824439 : Blo 1287962 8824439 := bstep (se 1 (by rfl) ⟨6618329, by rfl⟩ : syracuseStep 8824439 = 13236659) B13236659
theorem B2901689 : Blo 1287962 2901689 := bstep (se 2 (by rfl) ⟨1088133, by rfl⟩ : syracuseStep 2901689 = 2176267) B2176267
theorem B3262153 : Blo 1287962 3262153 := bstep (se 2 (by rfl) ⟨1223307, by rfl⟩ : syracuseStep 3262153 = 2446615) B2446615
theorem B6522605 : Blo 1287962 6522605 := bstep (se 3 (by rfl) ⟨1222988, by rfl⟩ : syracuseStep 6522605 = 2445977) B2445977
theorem B3671837 : Blo 1287962 3671837 := bstep (se 3 (by rfl) ⟨688469, by rfl⟩ : syracuseStep 3671837 = 1376939) B1376939
theorem B1287995 : Blo 1287962 1287995 := bstep (se 1 (by rfl) ⟨965996, by rfl⟩ : syracuseStep 1287995 = 1931993) B1931993
theorem B59541317 : Blo 1287962 59541317 := bstep (se 4 (by rfl) ⟨5581998, by rfl⟩ : syracuseStep 59541317 = 11163997) B11163997
theorem B3262295 : Blo 1287962 3262295 := bstep (se 1 (by rfl) ⟨2446721, by rfl⟩ : syracuseStep 3262295 = 4893443) B4893443
theorem B4351859 : Blo 1287962 4351859 := bstep (se 1 (by rfl) ⟨3263894, by rfl⟩ : syracuseStep 4351859 = 6527789) B6527789
theorem B1288071 : Blo 1287962 1288071 := bstep (se 1 (by rfl) ⟨966053, by rfl⟩ : syracuseStep 1288071 = 1932107) B1932107
theorem B1288079 : Blo 1287962 1288079 := bstep (se 1 (by rfl) ⟨966059, by rfl⟩ : syracuseStep 1288079 = 1932119) B1932119
theorem B1288123 : Blo 1287962 1288123 := bstep (se 1 (by rfl) ⟨966092, by rfl⟩ : syracuseStep 1288123 = 1932185) B1932185
theorem B14682059 : Blo 1287962 14682059 := bstep (se 1 (by rfl) ⟨11011544, by rfl⟩ : syracuseStep 14682059 = 22023089) B22023089
theorem B1288199 : Blo 1287962 1288199 := bstep (se 1 (by rfl) ⟨966149, by rfl⟩ : syracuseStep 1288199 = 1932299) B1932299
theorem B4892683 : Blo 1287962 4892683 := bstep (se 1 (by rfl) ⟨3669512, by rfl⟩ : syracuseStep 4892683 = 7339025) B7339025
theorem B1288207 : Blo 1287962 1288207 := bstep (se 1 (by rfl) ⟨966155, by rfl⟩ : syracuseStep 1288207 = 1932311) B1932311
theorem B2902031 : Blo 1287962 2902031 := bstep (se 1 (by rfl) ⟨2176523, by rfl⟩ : syracuseStep 2902031 = 4353047) B4353047
theorem B2902049 : Blo 1287962 2902049 := bstep (se 2 (by rfl) ⟨1088268, by rfl⟩ : syracuseStep 2902049 = 2176537) B2176537
theorem B7342123 : Blo 1287962 7342123 := bstep (se 1 (by rfl) ⟨5506592, by rfl⟩ : syracuseStep 7342123 = 11013185) B11013185
theorem B1288251 : Blo 1287962 1288251 := bstep (se 1 (by rfl) ⟨966188, by rfl⟩ : syracuseStep 1288251 = 1932377) B1932377
theorem B3672179 : Blo 1287962 3672179 := bstep (se 1 (by rfl) ⟨2754134, by rfl⟩ : syracuseStep 3672179 = 5508269) B5508269
theorem B1288327 : Blo 1287962 1288327 := bstep (se 1 (by rfl) ⟨966245, by rfl⟩ : syracuseStep 1288327 = 1932491) B1932491
theorem B1288335 : Blo 1287962 1288335 := bstep (se 1 (by rfl) ⟨966251, by rfl⟩ : syracuseStep 1288335 = 1932503) B1932503
theorem B1288379 : Blo 1287962 1288379 := bstep (se 1 (by rfl) ⟨966284, by rfl⟩ : syracuseStep 1288379 = 1932569) B1932569
theorem B10447049 : Blo 1287962 10447049 := bstep (se 2 (by rfl) ⟨3917643, by rfl⟩ : syracuseStep 10447049 = 7835287) B7835287
theorem B6965477 : Blo 1287962 6965477 := bstep (se 4 (by rfl) ⟨653013, by rfl⟩ : syracuseStep 6965477 = 1306027) B1306027
theorem B1288455 : Blo 1287962 1288455 := bstep (se 1 (by rfl) ⟨966341, by rfl⟩ : syracuseStep 1288455 = 1932683) B1932683
theorem B1288463 : Blo 1287962 1288463 := bstep (se 1 (by rfl) ⟨966347, by rfl⟩ : syracuseStep 1288463 = 1932695) B1932695
theorem B1288507 : Blo 1287962 1288507 := bstep (se 1 (by rfl) ⟨966380, by rfl⟩ : syracuseStep 1288507 = 1932761) B1932761
theorem B4892987 : Blo 1287962 4892987 := bstep (se 1 (by rfl) ⟨3669740, by rfl⟩ : syracuseStep 4892987 = 7339481) B7339481
theorem B2902391 : Blo 1287962 2902391 := bstep (se 1 (by rfl) ⟨2176793, by rfl⟩ : syracuseStep 2902391 = 4353587) B4353587
theorem B1288583 : Blo 1287962 1288583 := bstep (se 1 (by rfl) ⟨966437, by rfl⟩ : syracuseStep 1288583 = 1932875) B1932875
theorem B1288591 : Blo 1287962 1288591 := bstep (se 1 (by rfl) ⟨966443, by rfl⟩ : syracuseStep 1288591 = 1932887) B1932887
theorem B1288635 : Blo 1287962 1288635 := bstep (se 1 (by rfl) ⟨966476, by rfl⟩ : syracuseStep 1288635 = 1932953) B1932953
theorem B1288711 : Blo 1287962 1288711 := bstep (se 1 (by rfl) ⟨966533, by rfl⟩ : syracuseStep 1288711 = 1933067) B1933067
theorem B1288719 : Blo 1287962 1288719 := bstep (se 1 (by rfl) ⟨966539, by rfl⟩ : syracuseStep 1288719 = 1933079) B1933079
theorem B6523415 : Blo 1287962 6523415 := bstep (se 1 (by rfl) ⟨4892561, by rfl⟩ : syracuseStep 6523415 = 9785123) B9785123
theorem B6449707 : Blo 1287962 6449707 := bstep (se 1 (by rfl) ⟨4837280, by rfl⟩ : syracuseStep 6449707 = 9674561) B9674561
theorem B1288763 : Blo 1287962 1288763 := bstep (se 1 (by rfl) ⟨966572, by rfl⟩ : syracuseStep 1288763 = 1933145) B1933145
theorem B5294711 : Blo 1287962 5294711 := bstep (se 1 (by rfl) ⟨3971033, by rfl⟩ : syracuseStep 5294711 = 7942067) B7942067
theorem B1288839 : Blo 1287962 1288839 := bstep (se 1 (by rfl) ⟨966629, by rfl⟩ : syracuseStep 1288839 = 1933259) B1933259
theorem B1288847 : Blo 1287962 1288847 := bstep (se 1 (by rfl) ⟨966635, by rfl⟩ : syracuseStep 1288847 = 1933271) B1933271
theorem B1288891 : Blo 1287962 1288891 := bstep (se 1 (by rfl) ⟨966668, by rfl⟩ : syracuseStep 1288891 = 1933337) B1933337
theorem B8825537 : Blo 1287962 8825537 := bstep (se 2 (by rfl) ⟨3309576, by rfl⟩ : syracuseStep 8825537 = 6619153) B6619153
theorem B1288967 : Blo 1287962 1288967 := bstep (se 1 (by rfl) ⟨966725, by rfl⟩ : syracuseStep 1288967 = 1933451) B1933451
theorem B1288975 : Blo 1287962 1288975 := bstep (se 1 (by rfl) ⟨966731, by rfl⟩ : syracuseStep 1288975 = 1933463) B1933463
theorem B4893473 : Blo 1287962 4893473 := bstep (se 2 (by rfl) ⟨1835052, by rfl⟩ : syracuseStep 4893473 = 3670105) B3670105
theorem B1289019 : Blo 1287962 1289019 := bstep (se 1 (by rfl) ⟨966764, by rfl⟩ : syracuseStep 1289019 = 1933529) B1933529
theorem B6278023 : Blo 1287962 6278023 := bstep (se 1 (by rfl) ⟨4708517, by rfl⟩ : syracuseStep 6278023 = 9417035) B9417035
theorem B1289095 : Blo 1287962 1289095 := bstep (se 1 (by rfl) ⟨966821, by rfl⟩ : syracuseStep 1289095 = 1933643) B1933643
theorem B1289103 : Blo 1287962 1289103 := bstep (se 1 (by rfl) ⟨966827, by rfl⟩ : syracuseStep 1289103 = 1933655) B1933655
theorem B8260505 : Blo 1287962 8260505 := bstep (se 2 (by rfl) ⟨3097689, by rfl⟩ : syracuseStep 8260505 = 6195379) B6195379
theorem B1289147 : Blo 1287962 1289147 := bstep (se 1 (by rfl) ⟨966860, by rfl⟩ : syracuseStep 1289147 = 1933721) B1933721
theorem B1289223 : Blo 1287962 1289223 := bstep (se 1 (by rfl) ⟨966917, by rfl⟩ : syracuseStep 1289223 = 1933835) B1933835
theorem B8825867 : Blo 1287962 8825867 := bstep (se 1 (by rfl) ⟨6619400, by rfl⟩ : syracuseStep 8825867 = 13238801) B13238801
theorem B1289231 : Blo 1287962 1289231 := bstep (se 1 (by rfl) ⟨966923, by rfl⟩ : syracuseStep 1289231 = 1933847) B1933847
theorem B1289275 : Blo 1287962 1289275 := bstep (se 1 (by rfl) ⟨966956, by rfl⟩ : syracuseStep 1289275 = 1933913) B1933913
theorem B3673147 : Blo 1287962 3673147 := bstep (se 1 (by rfl) ⟨2754860, by rfl⟩ : syracuseStep 3673147 = 5509721) B5509721
theorem B2174087 : Blo 1287962 2174087 := bstep (se 1 (by rfl) ⟨1630565, by rfl⟩ : syracuseStep 2174087 = 3261131) B3261131
theorem B1289351 : Blo 1287962 1289351 := bstep (se 1 (by rfl) ⟨967013, by rfl⟩ : syracuseStep 1289351 = 1934027) B1934027
theorem B1289359 : Blo 1287962 1289359 := bstep (se 1 (by rfl) ⟨967019, by rfl⟩ : syracuseStep 1289359 = 1934039) B1934039
theorem B1289403 : Blo 1287962 1289403 := bstep (se 1 (by rfl) ⟨967052, by rfl⟩ : syracuseStep 1289403 = 1934105) B1934105
theorem B4705517 : Blo 1287962 4705517 := bstep (se 3 (by rfl) ⟨882284, by rfl⟩ : syracuseStep 4705517 = 1764569) B1764569
theorem B1289479 : Blo 1287962 1289479 := bstep (se 1 (by rfl) ⟨967109, by rfl⟩ : syracuseStep 1289479 = 1934219) B1934219
theorem B1289487 : Blo 1287962 1289487 := bstep (se 1 (by rfl) ⟨967115, by rfl⟩ : syracuseStep 1289487 = 1934231) B1934231
theorem B4648207 : Blo 1287962 4648207 := bstep (se 1 (by rfl) ⟨3486155, by rfl⟩ : syracuseStep 4648207 = 6972311) B6972311
theorem B3534113 : Blo 1287962 3534113 := bstep (se 2 (by rfl) ⟨1325292, by rfl⟩ : syracuseStep 3534113 = 2650585) B2650585
theorem B1289531 : Blo 1287962 1289531 := bstep (se 1 (by rfl) ⟨967148, by rfl⟩ : syracuseStep 1289531 = 1934297) B1934297
theorem B5877107 : Blo 1287962 5877107 := bstep (se 1 (by rfl) ⟨4407830, by rfl⟩ : syracuseStep 5877107 = 8815661) B8815661
theorem B1289607 : Blo 1287962 1289607 := bstep (se 1 (by rfl) ⟨967205, by rfl⟩ : syracuseStep 1289607 = 1934411) B1934411
theorem B1289615 : Blo 1287962 1289615 := bstep (se 1 (by rfl) ⟨967211, by rfl⟩ : syracuseStep 1289615 = 1934423) B1934423
theorem B1289659 : Blo 1287962 1289659 := bstep (se 1 (by rfl) ⟨967244, by rfl⟩ : syracuseStep 1289659 = 1934489) B1934489
theorem B7343581 : Blo 1287962 7343581 := bstep (se 3 (by rfl) ⟨1376921, by rfl⟩ : syracuseStep 7343581 = 2753843) B2753843
theorem B1289735 : Blo 1287962 1289735 := bstep (se 1 (by rfl) ⟨967301, by rfl⟩ : syracuseStep 1289735 = 1934603) B1934603
theorem B1289743 : Blo 1287962 1289743 := bstep (se 1 (by rfl) ⟨967307, by rfl⟩ : syracuseStep 1289743 = 1934615) B1934615
theorem B1289787 : Blo 1287962 1289787 := bstep (se 1 (by rfl) ⟨967340, by rfl⟩ : syracuseStep 1289787 = 1934681) B1934681
theorem B1289863 : Blo 1287962 1289863 := bstep (se 1 (by rfl) ⟨967397, by rfl⟩ : syracuseStep 1289863 = 1934795) B1934795
theorem B1289871 : Blo 1287962 1289871 := bstep (se 1 (by rfl) ⟨967403, by rfl⟩ : syracuseStep 1289871 = 1934807) B1934807
theorem B412544663 : Blo 1287962 412544663 := bstep (se 1 (by rfl) ⟨309408497, by rfl⟩ : syracuseStep 412544663 = 618816995) B618816995
theorem B1289915 : Blo 1287962 1289915 := bstep (se 1 (by rfl) ⟨967436, by rfl⟩ : syracuseStep 1289915 = 1934873) B1934873
theorem B4894445 : Blo 1287962 4894445 := bstep (se 3 (by rfl) ⟨917708, by rfl⟩ : syracuseStep 4894445 = 1835417) B1835417
theorem B2174735 : Blo 1287962 2174735 := bstep (se 1 (by rfl) ⟨1631051, by rfl⟩ : syracuseStep 2174735 = 3262103) B3262103
theorem B29773613 : Blo 1287962 29773613 := bstep (se 3 (by rfl) ⟨5582552, by rfl⟩ : syracuseStep 29773613 = 11165105) B11165105
theorem B3264371 : Blo 1287962 3264371 := bstep (se 1 (by rfl) ⟨2448278, by rfl⟩ : syracuseStep 3264371 = 4896557) B4896557
theorem B2445203 : Blo 1287962 2445203 := bstep (se 1 (by rfl) ⟨1833902, by rfl⟩ : syracuseStep 2445203 = 3667805) B3667805
theorem B2445241 : Blo 1287962 2445241 := bstep (se 2 (by rfl) ⟨916965, by rfl⟩ : syracuseStep 2445241 = 1833931) B1833931
theorem B7336109 : Blo 1287962 7336109 := bstep (se 3 (by rfl) ⟨1375520, by rfl⟩ : syracuseStep 7336109 = 2751041) B2751041
theorem B3305657 : Blo 1287962 3305657 := bstep (se 2 (by rfl) ⟨1239621, by rfl⟩ : syracuseStep 3305657 = 2479243) B2479243
theorem B2175275 : Blo 1287962 2175275 := bstep (se 1 (by rfl) ⟨1631456, by rfl⟩ : syracuseStep 2175275 = 3262913) B3262913
theorem B3486071 : Blo 1287962 3486071 := bstep (se 1 (by rfl) ⟨2614553, by rfl⟩ : syracuseStep 3486071 = 5229107) B5229107
theorem B3264887 : Blo 1287962 3264887 := bstep (se 1 (by rfl) ⟨2448665, by rfl⟩ : syracuseStep 3264887 = 4897331) B4897331
theorem B13234691 : Blo 1287962 13234691 := bstep (se 1 (by rfl) ⟨9926018, by rfl⟩ : syracuseStep 13234691 = 19852037) B19852037
theorem B12563009 : Blo 1287962 12563009 := bstep (se 2 (by rfl) ⟨4711128, by rfl⟩ : syracuseStep 12563009 = 9422257) B9422257
theorem B3920503 : Blo 1287962 3920503 := bstep (se 1 (by rfl) ⟨2940377, by rfl⟩ : syracuseStep 3920503 = 5880755) B5880755
theorem B2175673 : Blo 1287962 2175673 := bstep (se 2 (by rfl) ⟨815877, by rfl⟩ : syracuseStep 2175673 = 1631755) B1631755
theorem B44634817 : Blo 1287962 44634817 := bstep (se 2 (by rfl) ⟨16738056, by rfl⟩ : syracuseStep 44634817 = 33476113) B33476113
theorem B3920699 : Blo 1287962 3920699 := bstep (se 1 (by rfl) ⟨2940524, by rfl⟩ : syracuseStep 3920699 = 5881049) B5881049
theorem B4346891 : Blo 1287962 4346891 := bstep (se 1 (by rfl) ⟨3260168, by rfl⟩ : syracuseStep 4346891 = 6520337) B6520337
theorem B4346999 : Blo 1287962 4346999 := bstep (se 1 (by rfl) ⟨3260249, by rfl⟩ : syracuseStep 4346999 = 6520499) B6520499
theorem B1741943 : Blo 1287962 1741943 := bstep (se 1 (by rfl) ⟨1306457, by rfl⟩ : syracuseStep 1741943 = 2612915) B2612915
theorem B2094265 : Blo 1287962 2094265 := bstep (se 2 (by rfl) ⟨785349, by rfl⟩ : syracuseStep 2094265 = 1570699) B1570699
theorem B2790671 : Blo 1287962 2790671 := bstep (se 1 (by rfl) ⟨2093003, by rfl⟩ : syracuseStep 2790671 = 4186007) B4186007
theorem B7337249 : Blo 1287962 7337249 := bstep (se 2 (by rfl) ⟨2751468, by rfl⟩ : syracuseStep 7337249 = 5502937) B5502937
theorem B3921185 : Blo 1287962 3921185 := bstep (se 2 (by rfl) ⟨1470444, by rfl⟩ : syracuseStep 3921185 = 2940889) B2940889
theorem B2176375 : Blo 1287962 2176375 := bstep (se 1 (by rfl) ⟨1632281, by rfl⟩ : syracuseStep 2176375 = 3264563) B3264563
theorem B15685123 : Blo 1287962 15685123 := bstep (se 1 (by rfl) ⟨11763842, by rfl⟩ : syracuseStep 15685123 = 23527685) B23527685
theorem B6526493 : Blo 1287962 6526493 := bstep (se 3 (by rfl) ⟨1223717, by rfl⟩ : syracuseStep 6526493 = 2447435) B2447435
theorem B2176571 : Blo 1287962 2176571 := bstep (se 1 (by rfl) ⟨1632428, by rfl⟩ : syracuseStep 2176571 = 3264857) B3264857
theorem B4126409 : Blo 1287962 4126409 := bstep (se 2 (by rfl) ⟨1547403, by rfl⟩ : syracuseStep 4126409 = 3094807) B3094807
theorem B4347593 : Blo 1287962 4347593 := bstep (se 2 (by rfl) ⟨1630347, by rfl⟩ : syracuseStep 4347593 = 3260695) B3260695
theorem B9795329 : Blo 1287962 9795329 := bstep (se 2 (by rfl) ⟨3673248, by rfl⟩ : syracuseStep 9795329 = 7346497) B7346497
theorem B2447147 : Blo 1287962 2447147 := bstep (se 1 (by rfl) ⟨1835360, by rfl⟩ : syracuseStep 2447147 = 3670721) B3670721
theorem B1742635 : Blo 1287962 1742635 := bstep (se 1 (by rfl) ⟨1306976, by rfl⟩ : syracuseStep 1742635 = 2613953) B2613953
theorem B4896571 : Blo 1287962 4896571 := bstep (se 1 (by rfl) ⟨3672428, by rfl⟩ : syracuseStep 4896571 = 7344857) B7344857
theorem B3921779 : Blo 1287962 3921779 := bstep (se 1 (by rfl) ⟨2941334, by rfl⟩ : syracuseStep 3921779 = 5882669) B5882669
theorem B15677387 : Blo 1287962 15677387 := bstep (se 1 (by rfl) ⟨11758040, by rfl⟩ : syracuseStep 15677387 = 23516081) B23516081
theorem B6526979 : Blo 1287962 6526979 := bstep (se 1 (by rfl) ⟨4895234, by rfl⟩ : syracuseStep 6526979 = 9790469) B9790469
theorem B4028449 : Blo 1287962 4028449 := bstep (se 2 (by rfl) ⟨1510668, by rfl⟩ : syracuseStep 4028449 = 3021337) B3021337
theorem B2897963 : Blo 1287962 2897963 := bstep (se 1 (by rfl) ⟨2173472, by rfl⟩ : syracuseStep 2897963 = 4346945) B4346945
theorem B11008061 : Blo 1287962 11008061 := bstep (se 3 (by rfl) ⟨2064011, by rfl⟩ : syracuseStep 11008061 = 4128023) B4128023
theorem B39688309 : Blo 1287962 39688309 := bstep (se 5 (by rfl) ⟨1860389, by rfl⟩ : syracuseStep 39688309 = 3720779) B3720779
theorem B2938999 : Blo 1287962 2938999 := bstep (se 1 (by rfl) ⟨2204249, by rfl⟩ : syracuseStep 2938999 = 4408499) B4408499
theorem B3922121 : Blo 1287962 3922121 := bstep (se 2 (by rfl) ⟨1470795, by rfl⟩ : syracuseStep 3922121 = 2941591) B2941591
theorem B4897057 : Blo 1287962 4897057 := bstep (se 2 (by rfl) ⟨1836396, by rfl⟩ : syracuseStep 4897057 = 3672793) B3672793
theorem B4348295 : Blo 1287962 4348295 := bstep (se 1 (by rfl) ⟨3261221, by rfl⟩ : syracuseStep 4348295 = 6522443) B6522443
theorem B2898323 : Blo 1287962 2898323 := bstep (se 1 (by rfl) ⟨2173742, by rfl⟩ : syracuseStep 2898323 = 4347485) B4347485
theorem B2898377 : Blo 1287962 2898377 := bstep (se 2 (by rfl) ⟨1086891, by rfl⟩ : syracuseStep 2898377 = 2173783) B2173783
theorem B12392909 : Blo 1287962 12392909 := bstep (se 3 (by rfl) ⟨2323670, by rfl⟩ : syracuseStep 12392909 = 4647341) B4647341
theorem B19831339 : Blo 1287962 19831339 := bstep (se 1 (by rfl) ⟨14873504, by rfl⟩ : syracuseStep 19831339 = 29747009) B29747009
theorem B2611859 : Blo 1287962 2611859 := bstep (se 1 (by rfl) ⟨1958894, by rfl⟩ : syracuseStep 2611859 = 3917789) B3917789
theorem B1931963 : Blo 1287962 1931963 := bstep (se 1 (by rfl) ⟨1448972, by rfl⟩ : syracuseStep 1931963 = 2897945) B2897945
theorem B2448073 : Blo 1287962 2448073 := bstep (se 2 (by rfl) ⟨918027, by rfl⟩ : syracuseStep 2448073 = 1836055) B1836055
theorem B1932023 : Blo 1287962 1932023 := bstep (se 1 (by rfl) ⟨1449017, by rfl⟩ : syracuseStep 1932023 = 2898035) B2898035
theorem B4348673 : Blo 1287962 4348673 := bstep (se 2 (by rfl) ⟨1630752, by rfl⟩ : syracuseStep 4348673 = 3261505) B3261505
theorem B1932047 : Blo 1287962 1932047 := bstep (se 1 (by rfl) ⟨1449035, by rfl⟩ : syracuseStep 1932047 = 2898071) B2898071
theorem B1932089 : Blo 1287962 1932089 := bstep (se 2 (by rfl) ⟨724533, by rfl⟩ : syracuseStep 1932089 = 1449067) B1449067
theorem B5503859 : Blo 1287962 5503859 := bstep (se 1 (by rfl) ⟨4127894, by rfl⟩ : syracuseStep 5503859 = 8255789) B8255789
theorem B1932167 : Blo 1287962 1932167 := bstep (se 1 (by rfl) ⟨1449125, by rfl⟩ : syracuseStep 1932167 = 2898251) B2898251
theorem B15678359 : Blo 1287962 15678359 := bstep (se 1 (by rfl) ⟨11758769, by rfl⟩ : syracuseStep 15678359 = 23517539) B23517539
theorem B1932203 : Blo 1287962 1932203 := bstep (se 1 (by rfl) ⟨1449152, by rfl⟩ : syracuseStep 1932203 = 2898305) B2898305
theorem B3668921 : Blo 1287962 3668921 := bstep (se 2 (by rfl) ⟨1375845, by rfl⟩ : syracuseStep 3668921 = 2751691) B2751691
theorem B2980793 : Blo 1287962 2980793 := bstep (se 2 (by rfl) ⟨1117797, by rfl⟩ : syracuseStep 2980793 = 2235595) B2235595
theorem B1932233 : Blo 1287962 1932233 := bstep (se 2 (by rfl) ⟨724587, by rfl⟩ : syracuseStep 1932233 = 1449175) B1449175
theorem B1932347 : Blo 1287962 1932347 := bstep (se 1 (by rfl) ⟨1449260, by rfl⟩ : syracuseStep 1932347 = 2898521) B2898521
theorem B1932407 : Blo 1287962 1932407 := bstep (se 1 (by rfl) ⟨1449305, by rfl⟩ : syracuseStep 1932407 = 2898611) B2898611
theorem B2899079 : Blo 1287962 2899079 := bstep (se 1 (by rfl) ⟨2174309, by rfl⟩ : syracuseStep 2899079 = 4348619) B4348619
theorem B1449103 : Blo 1287962 1449103 := bstep (se 1 (by rfl) ⟨1086827, by rfl⟩ : syracuseStep 1449103 = 2173655) B2173655
theorem B1932431 : Blo 1287962 1932431 := bstep (se 1 (by rfl) ⟨1449323, by rfl⟩ : syracuseStep 1932431 = 2898647) B2898647
theorem B1932473 : Blo 1287962 1932473 := bstep (se 2 (by rfl) ⟨724677, by rfl⟩ : syracuseStep 1932473 = 1449355) B1449355
theorem B92978381 : Blo 1287962 92978381 := bstep (se 3 (by rfl) ⟨17433446, by rfl⟩ : syracuseStep 92978381 = 34866893) B34866893
theorem B1932551 : Blo 1287962 1932551 := bstep (se 1 (by rfl) ⟨1449413, by rfl⟩ : syracuseStep 1932551 = 2898827) B2898827
theorem B1834255 : Blo 1287962 1834255 := bstep (se 1 (by rfl) ⟨1375691, by rfl⟩ : syracuseStep 1834255 = 2751383) B2751383
theorem B3669263 : Blo 1287962 3669263 := bstep (se 1 (by rfl) ⟨2751947, by rfl⟩ : syracuseStep 3669263 = 5503895) B5503895
theorem B1932587 : Blo 1287962 1932587 := bstep (se 1 (by rfl) ⟨1449440, by rfl⟩ : syracuseStep 1932587 = 2898881) B2898881
theorem B2899259 : Blo 1287962 2899259 := bstep (se 1 (by rfl) ⟨2174444, by rfl⟩ : syracuseStep 2899259 = 4348889) B4348889
theorem B1932617 : Blo 1287962 1932617 := bstep (se 2 (by rfl) ⟨724731, by rfl⟩ : syracuseStep 1932617 = 1449463) B1449463
theorem B2448787 : Blo 1287962 2448787 := bstep (se 1 (by rfl) ⟨1836590, by rfl⟩ : syracuseStep 2448787 = 3673181) B3673181
theorem B2899385 : Blo 1287962 2899385 := bstep (se 2 (by rfl) ⟨1087269, by rfl⟩ : syracuseStep 2899385 = 2174539) B2174539
theorem B1932731 : Blo 1287962 1932731 := bstep (se 1 (by rfl) ⟨1449548, by rfl⟩ : syracuseStep 1932731 = 2899097) B2899097
theorem B1932791 : Blo 1287962 1932791 := bstep (se 1 (by rfl) ⟨1449593, by rfl⟩ : syracuseStep 1932791 = 2899187) B2899187
theorem B5881355 : Blo 1287962 5881355 := bstep (se 1 (by rfl) ⟨4411016, by rfl⟩ : syracuseStep 5881355 = 8822033) B8822033
theorem B1932815 : Blo 1287962 1932815 := bstep (se 1 (by rfl) ⟨1449611, by rfl⟩ : syracuseStep 1932815 = 2899223) B2899223
theorem B4349483 : Blo 1287962 4349483 := bstep (se 1 (by rfl) ⟨3262112, by rfl⟩ : syracuseStep 4349483 = 6524225) B6524225
theorem B1932857 : Blo 1287962 1932857 := bstep (se 2 (by rfl) ⟨724821, by rfl⟩ : syracuseStep 1932857 = 1449643) B1449643
theorem B6528599 : Blo 1287962 6528599 := bstep (se 1 (by rfl) ⟨4896449, by rfl⟩ : syracuseStep 6528599 = 9792899) B9792899
theorem B1449607 : Blo 1287962 1449607 := bstep (se 1 (by rfl) ⟨1087205, by rfl⟩ : syracuseStep 1449607 = 2174411) B2174411
theorem B1932935 : Blo 1287962 1932935 := bstep (se 1 (by rfl) ⟨1449701, by rfl⟩ : syracuseStep 1932935 = 2899403) B2899403
theorem B1932971 : Blo 1287962 1932971 := bstep (se 1 (by rfl) ⟨1449728, by rfl⟩ : syracuseStep 1932971 = 2899457) B2899457
theorem B1933001 : Blo 1287962 1933001 := bstep (se 2 (by rfl) ⟨724875, by rfl⟩ : syracuseStep 1933001 = 1449751) B1449751
theorem B2899727 : Blo 1287962 2899727 := bstep (se 1 (by rfl) ⟨2174795, by rfl⟩ : syracuseStep 2899727 = 4349591) B4349591
theorem B2752289 : Blo 1287962 2752289 := bstep (se 2 (by rfl) ⟨1032108, by rfl⟩ : syracuseStep 2752289 = 2064217) B2064217
theorem B2899745 : Blo 1287962 2899745 := bstep (se 2 (by rfl) ⟨1087404, by rfl⟩ : syracuseStep 2899745 = 2174809) B2174809
theorem B1449787 : Blo 1287962 1449787 := bstep (se 1 (by rfl) ⟨1087340, by rfl⟩ : syracuseStep 1449787 = 2174681) B2174681
theorem B1933115 : Blo 1287962 1933115 := bstep (se 1 (by rfl) ⟨1449836, by rfl⟩ : syracuseStep 1933115 = 2899673) B2899673
theorem B5226299 : Blo 1287962 5226299 := bstep (se 1 (by rfl) ⟨3919724, by rfl⟩ : syracuseStep 5226299 = 7839449) B7839449
theorem B1834825 : Blo 1287962 1834825 := bstep (se 2 (by rfl) ⟨688059, by rfl⟩ : syracuseStep 1834825 = 1376119) B1376119
theorem B1933175 : Blo 1287962 1933175 := bstep (se 1 (by rfl) ⟨1449881, by rfl⟩ : syracuseStep 1933175 = 2899763) B2899763
theorem B6610823 : Blo 1287962 6610823 := bstep (se 1 (by rfl) ⟨4958117, by rfl⟩ : syracuseStep 6610823 = 9916235) B9916235
theorem B1933199 : Blo 1287962 1933199 := bstep (se 1 (by rfl) ⟨1449899, by rfl⟩ : syracuseStep 1933199 = 2899799) B2899799
theorem B1933241 : Blo 1287962 1933241 := bstep (se 2 (by rfl) ⟨724965, by rfl⟩ : syracuseStep 1933241 = 1449931) B1449931
theorem B9789497 : Blo 1287962 9789497 := bstep (se 2 (by rfl) ⟨3671061, by rfl⟩ : syracuseStep 9789497 = 7342123) B7342123
theorem B1933391 : Blo 1287962 1933391 := bstep (se 1 (by rfl) ⟨1450043, by rfl⟩ : syracuseStep 1933391 = 2900087) B2900087
theorem B4890739 : Blo 1287962 4890739 := bstep (se 1 (by rfl) ⟨3668054, by rfl⟩ : syracuseStep 4890739 = 7336109) B7336109
theorem B2203771 : Blo 1287962 2203771 := bstep (se 1 (by rfl) ⟨1652828, by rfl⟩ : syracuseStep 2203771 = 3305657) B3305657
theorem B1933511 : Blo 1287962 1933511 := bstep (se 1 (by rfl) ⟨1450133, by rfl⟩ : syracuseStep 1933511 = 2900267) B2900267
theorem B1450183 : Blo 1287962 1450183 := bstep (se 1 (by rfl) ⟨1087637, by rfl⟩ : syracuseStep 1450183 = 2175275) B2175275
theorem B4645181 : Blo 1287962 4645181 := bstep (se 3 (by rfl) ⟨870971, by rfl⟩ : syracuseStep 4645181 = 1741943) B1741943
theorem B1933673 : Blo 1287962 1933673 := bstep (se 2 (by rfl) ⟨725127, by rfl⟩ : syracuseStep 1933673 = 1450255) B1450255
theorem B6529409 : Blo 1287962 6529409 := bstep (se 2 (by rfl) ⟨2448528, by rfl⟩ : syracuseStep 6529409 = 4897057) B4897057
theorem B1933751 : Blo 1287962 1933751 := bstep (se 1 (by rfl) ⟨1450313, by rfl⟩ : syracuseStep 1933751 = 2900627) B2900627
theorem B1933787 : Blo 1287962 1933787 := bstep (se 1 (by rfl) ⟨1450340, by rfl⟩ : syracuseStep 1933787 = 2900681) B2900681
theorem B3097075 : Blo 1287962 3097075 := bstep (se 1 (by rfl) ⟨2322806, by rfl⟩ : syracuseStep 3097075 = 4645613) B4645613
theorem B14680601 : Blo 1287962 14680601 := bstep (se 2 (by rfl) ⟨5505225, by rfl⟩ : syracuseStep 14680601 = 11010451) B11010451
theorem B5505569 : Blo 1287962 5505569 := bstep (se 2 (by rfl) ⟨2064588, by rfl⟩ : syracuseStep 5505569 = 4129177) B4129177
theorem B4129319 : Blo 1287962 4129319 := bstep (se 1 (by rfl) ⟨3096989, by rfl⟩ : syracuseStep 4129319 = 6193979) B6193979
theorem B2900519 : Blo 1287962 2900519 := bstep (se 1 (by rfl) ⟨2175389, by rfl⟩ : syracuseStep 2900519 = 4350779) B4350779
theorem B2064935 : Blo 1287962 2064935 := bstep (se 1 (by rfl) ⟨1548701, by rfl⟩ : syracuseStep 2064935 = 3097403) B3097403
theorem B2613799 : Blo 1287962 2613799 := bstep (se 1 (by rfl) ⟨1960349, by rfl⟩ : syracuseStep 2613799 = 3920699) B3920699
theorem B5505671 : Blo 1287962 5505671 := bstep (se 1 (by rfl) ⟨4129253, by rfl⟩ : syracuseStep 5505671 = 8258507) B8258507
theorem B8258249 : Blo 1287962 8258249 := bstep (se 2 (by rfl) ⟨3096843, by rfl⟩ : syracuseStep 8258249 = 6193687) B6193687
theorem B5227337 : Blo 1287962 5227337 := bstep (se 2 (by rfl) ⟨1960251, by rfl⟩ : syracuseStep 5227337 = 3920503) B3920503
theorem B4891499 : Blo 1287962 4891499 := bstep (se 1 (by rfl) ⟨3668624, by rfl⟩ : syracuseStep 4891499 = 7337249) B7337249
theorem B2900843 : Blo 1287962 2900843 := bstep (se 1 (by rfl) ⟨2175632, by rfl⟩ : syracuseStep 2900843 = 4351265) B4351265
theorem B2614123 : Blo 1287962 2614123 := bstep (se 1 (by rfl) ⟨1960592, by rfl⟩ : syracuseStep 2614123 = 3921185) B3921185
theorem B2900897 : Blo 1287962 2900897 := bstep (se 2 (by rfl) ⟨1087836, by rfl⟩ : syracuseStep 2900897 = 2175673) B2175673
theorem B1934255 : Blo 1287962 1934255 := bstep (se 1 (by rfl) ⟨1450691, by rfl⟩ : syracuseStep 1934255 = 2901383) B2901383
theorem B1934345 : Blo 1287962 1934345 := bstep (se 2 (by rfl) ⟨725379, by rfl⟩ : syracuseStep 1934345 = 1450759) B1450759
theorem B4350995 : Blo 1287962 4350995 := bstep (se 1 (by rfl) ⟨3263246, by rfl⟩ : syracuseStep 4350995 = 6526493) B6526493
theorem B2065447 : Blo 1287962 2065447 := bstep (se 1 (by rfl) ⟨1549085, by rfl⟩ : syracuseStep 2065447 = 3098171) B3098171
theorem B1934375 : Blo 1287962 1934375 := bstep (se 1 (by rfl) ⟨1450781, by rfl⟩ : syracuseStep 1934375 = 2901563) B2901563
theorem B1451047 : Blo 1287962 1451047 := bstep (se 1 (by rfl) ⟨1088285, by rfl⟩ : syracuseStep 1451047 = 2176571) B2176571
theorem B5882959 : Blo 1287962 5882959 := bstep (se 1 (by rfl) ⟨4412219, by rfl⟩ : syracuseStep 5882959 = 8824439) B8824439
theorem B1934459 : Blo 1287962 1934459 := bstep (se 1 (by rfl) ⟨1450844, by rfl⟩ : syracuseStep 1934459 = 2901689) B2901689
theorem B6530219 : Blo 1287962 6530219 := bstep (se 1 (by rfl) ⟨4897664, by rfl⟩ : syracuseStep 6530219 = 9795329) B9795329
theorem B1631431 : Blo 1287962 1631431 := bstep (se 1 (by rfl) ⟨1223573, by rfl⟩ : syracuseStep 1631431 = 2447147) B2447147
theorem B2901239 : Blo 1287962 2901239 := bstep (se 1 (by rfl) ⟨2175929, by rfl⟩ : syracuseStep 2901239 = 4351859) B4351859
theorem B2614519 : Blo 1287962 2614519 := bstep (se 1 (by rfl) ⟨1960889, by rfl⟩ : syracuseStep 2614519 = 3921779) B3921779
theorem B1934585 : Blo 1287962 1934585 := bstep (se 2 (by rfl) ⟨725469, by rfl⟩ : syracuseStep 1934585 = 1450939) B1450939
theorem B4351319 : Blo 1287962 4351319 := bstep (se 1 (by rfl) ⟨3263489, by rfl⟩ : syracuseStep 4351319 = 6526979) B6526979
theorem B35292509 : Blo 1287962 35292509 := bstep (se 3 (by rfl) ⟨6617345, by rfl⟩ : syracuseStep 35292509 = 13234691) B13234691
theorem B1934687 : Blo 1287962 1934687 := bstep (se 1 (by rfl) ⟨1451015, by rfl⟩ : syracuseStep 1934687 = 2902031) B2902031
theorem B1934699 : Blo 1287962 1934699 := bstep (se 1 (by rfl) ⟨1451024, by rfl⟩ : syracuseStep 1934699 = 2902049) B2902049
theorem B9782693 : Blo 1287962 9782693 := bstep (se 4 (by rfl) ⟨917127, by rfl⟩ : syracuseStep 9782693 = 1834255) B1834255
theorem B6964699 : Blo 1287962 6964699 := bstep (se 1 (by rfl) ⟨5223524, by rfl⟩ : syracuseStep 6964699 = 10447049) B10447049
theorem B2614747 : Blo 1287962 2614747 := bstep (se 1 (by rfl) ⟨1961060, by rfl⟩ : syracuseStep 2614747 = 3922121) B3922121
theorem B3261991 : Blo 1287962 3261991 := bstep (se 1 (by rfl) ⟨2446493, by rfl⟩ : syracuseStep 3261991 = 4892987) B4892987
theorem B1934927 : Blo 1287962 1934927 := bstep (se 1 (by rfl) ⟨1451195, by rfl⟩ : syracuseStep 1934927 = 2902391) B2902391
theorem B6964957 : Blo 1287962 6964957 := bstep (se 3 (by rfl) ⟨1305929, by rfl⟩ : syracuseStep 6964957 = 2611859) B2611859
theorem B1287975 : Blo 1287962 1287975 := bstep (se 1 (by rfl) ⟨965981, by rfl⟩ : syracuseStep 1287975 = 1931963) B1931963
theorem B5883691 : Blo 1287962 5883691 := bstep (se 1 (by rfl) ⟨4412768, by rfl⟩ : syracuseStep 5883691 = 8825537) B8825537
theorem B2901833 : Blo 1287962 2901833 := bstep (se 2 (by rfl) ⟨1088187, by rfl⟩ : syracuseStep 2901833 = 2176375) B2176375
theorem B1288015 : Blo 1287962 1288015 := bstep (se 1 (by rfl) ⟨966011, by rfl⟩ : syracuseStep 1288015 = 1932023) B1932023
theorem B1288031 : Blo 1287962 1288031 := bstep (se 1 (by rfl) ⟨966023, by rfl⟩ : syracuseStep 1288031 = 1932047) B1932047
theorem B3262315 : Blo 1287962 3262315 := bstep (se 1 (by rfl) ⟨2446736, by rfl⟩ : syracuseStep 3262315 = 4893473) B4893473
theorem B1288059 : Blo 1287962 1288059 := bstep (se 1 (by rfl) ⟨966044, by rfl⟩ : syracuseStep 1288059 = 1932089) B1932089
theorem B1288111 : Blo 1287962 1288111 := bstep (se 1 (by rfl) ⟨966083, by rfl⟩ : syracuseStep 1288111 = 1932167) B1932167
theorem B5507003 : Blo 1287962 5507003 := bstep (se 1 (by rfl) ⟨4130252, by rfl⟩ : syracuseStep 5507003 = 8260505) B8260505
theorem B1288135 : Blo 1287962 1288135 := bstep (se 1 (by rfl) ⟨966101, by rfl⟩ : syracuseStep 1288135 = 1932203) B1932203
theorem B9791441 : Blo 1287962 9791441 := bstep (se 2 (by rfl) ⟨3671790, by rfl⟩ : syracuseStep 9791441 = 7343581) B7343581
theorem B1288155 : Blo 1287962 1288155 := bstep (se 1 (by rfl) ⟨966116, by rfl⟩ : syracuseStep 1288155 = 1932233) B1932233
theorem B5883911 : Blo 1287962 5883911 := bstep (se 1 (by rfl) ⟨4412933, by rfl⟩ : syracuseStep 5883911 = 8825867) B8825867
theorem B1288231 : Blo 1287962 1288231 := bstep (se 1 (by rfl) ⟨966173, by rfl⟩ : syracuseStep 1288231 = 1932347) B1932347
theorem B1288271 : Blo 1287962 1288271 := bstep (se 1 (by rfl) ⟨966203, by rfl⟩ : syracuseStep 1288271 = 1932407) B1932407
theorem B1288287 : Blo 1287962 1288287 := bstep (se 1 (by rfl) ⟨966215, by rfl⟩ : syracuseStep 1288287 = 1932431) B1932431
theorem B1288315 : Blo 1287962 1288315 := bstep (se 1 (by rfl) ⟨966236, by rfl⟩ : syracuseStep 1288315 = 1932473) B1932473
theorem B1288367 : Blo 1287962 1288367 := bstep (se 1 (by rfl) ⟨966275, by rfl⟩ : syracuseStep 1288367 = 1932551) B1932551
theorem B1288391 : Blo 1287962 1288391 := bstep (se 1 (by rfl) ⟨966293, by rfl⟩ : syracuseStep 1288391 = 1932587) B1932587
theorem B1288411 : Blo 1287962 1288411 := bstep (se 1 (by rfl) ⟨966308, by rfl⟩ : syracuseStep 1288411 = 1932617) B1932617
theorem B3918071 : Blo 1287962 3918071 := bstep (se 1 (by rfl) ⟨2938553, by rfl⟩ : syracuseStep 3918071 = 5877107) B5877107
theorem B1288487 : Blo 1287962 1288487 := bstep (se 1 (by rfl) ⟨966365, by rfl⟩ : syracuseStep 1288487 = 1932731) B1932731
theorem B7342397 : Blo 1287962 7342397 := bstep (se 3 (by rfl) ⟨1376699, by rfl⟩ : syracuseStep 7342397 = 2753399) B2753399
theorem B1288527 : Blo 1287962 1288527 := bstep (se 1 (by rfl) ⟨966395, by rfl⟩ : syracuseStep 1288527 = 1932791) B1932791
theorem B1288543 : Blo 1287962 1288543 := bstep (se 1 (by rfl) ⟨966407, by rfl⟩ : syracuseStep 1288543 = 1932815) B1932815
theorem B1288571 : Blo 1287962 1288571 := bstep (se 1 (by rfl) ⟨966428, by rfl⟩ : syracuseStep 1288571 = 1932857) B1932857
theorem B4352399 : Blo 1287962 4352399 := bstep (se 1 (by rfl) ⟨3264299, by rfl⟩ : syracuseStep 4352399 = 6528599) B6528599
theorem B1288623 : Blo 1287962 1288623 := bstep (se 1 (by rfl) ⟨966467, by rfl⟩ : syracuseStep 1288623 = 1932935) B1932935
theorem B1288647 : Blo 1287962 1288647 := bstep (se 1 (by rfl) ⟨966485, by rfl⟩ : syracuseStep 1288647 = 1932971) B1932971
theorem B1288667 : Blo 1287962 1288667 := bstep (se 1 (by rfl) ⟨966500, by rfl⟩ : syracuseStep 1288667 = 1933001) B1933001
theorem B3262963 : Blo 1287962 3262963 := bstep (se 1 (by rfl) ⟨2447222, by rfl⟩ : syracuseStep 3262963 = 4894445) B4894445
theorem B1288743 : Blo 1287962 1288743 := bstep (se 1 (by rfl) ⟨966557, by rfl⟩ : syracuseStep 1288743 = 1933115) B1933115
theorem B3484199 : Blo 1287962 3484199 := bstep (se 1 (by rfl) ⟨2613149, by rfl⟩ : syracuseStep 3484199 = 5226299) B5226299
theorem B1288783 : Blo 1287962 1288783 := bstep (se 1 (by rfl) ⟨966587, by rfl⟩ : syracuseStep 1288783 = 1933175) B1933175
theorem B1288799 : Blo 1287962 1288799 := bstep (se 1 (by rfl) ⟨966599, by rfl⟩ : syracuseStep 1288799 = 1933199) B1933199
theorem B1288827 : Blo 1287962 1288827 := bstep (se 1 (by rfl) ⟨966620, by rfl⟩ : syracuseStep 1288827 = 1933241) B1933241
theorem B1288879 : Blo 1287962 1288879 := bstep (se 1 (by rfl) ⟨966659, by rfl⟩ : syracuseStep 1288879 = 1933319) B1933319
theorem B6523577 : Blo 1287962 6523577 := bstep (se 2 (by rfl) ⟨2446341, by rfl⟩ : syracuseStep 6523577 = 4892683) B4892683
theorem B1288903 : Blo 1287962 1288903 := bstep (se 1 (by rfl) ⟨966677, by rfl⟩ : syracuseStep 1288903 = 1933355) B1933355
theorem B4352723 : Blo 1287962 4352723 := bstep (se 1 (by rfl) ⟨3264542, by rfl⟩ : syracuseStep 4352723 = 6529085) B6529085
theorem B1288923 : Blo 1287962 1288923 := bstep (se 1 (by rfl) ⟨966692, by rfl⟩ : syracuseStep 1288923 = 1933385) B1933385
theorem B1288999 : Blo 1287962 1288999 := bstep (se 1 (by rfl) ⟨966749, by rfl⟩ : syracuseStep 1288999 = 1933499) B1933499
theorem B3918665 : Blo 1287962 3918665 := bstep (se 2 (by rfl) ⟨1469499, by rfl⟩ : syracuseStep 3918665 = 2938999) B2938999
theorem B1289039 : Blo 1287962 1289039 := bstep (se 1 (by rfl) ⟨966779, by rfl⟩ : syracuseStep 1289039 = 1933559) B1933559
theorem B1289055 : Blo 1287962 1289055 := bstep (se 1 (by rfl) ⟨966791, by rfl⟩ : syracuseStep 1289055 = 1933583) B1933583
theorem B1289083 : Blo 1287962 1289083 := bstep (se 1 (by rfl) ⟨966812, by rfl⟩ : syracuseStep 1289083 = 1933625) B1933625
theorem B2173871 : Blo 1287962 2173871 := bstep (se 1 (by rfl) ⟨1630403, by rfl⟩ : syracuseStep 2173871 = 3260807) B3260807
theorem B1289135 : Blo 1287962 1289135 := bstep (se 1 (by rfl) ⟨966851, by rfl⟩ : syracuseStep 1289135 = 1933703) B1933703
theorem B1289159 : Blo 1287962 1289159 := bstep (se 1 (by rfl) ⟨966869, by rfl⟩ : syracuseStep 1289159 = 1933739) B1933739
theorem B1289179 : Blo 1287962 1289179 := bstep (se 1 (by rfl) ⟨966884, by rfl⟩ : syracuseStep 1289179 = 1933769) B1933769
theorem B3533843 : Blo 1287962 3533843 := bstep (se 1 (by rfl) ⟨2650382, by rfl⟩ : syracuseStep 3533843 = 5300765) B5300765
theorem B1289255 : Blo 1287962 1289255 := bstep (se 1 (by rfl) ⟨966941, by rfl⟩ : syracuseStep 1289255 = 1933883) B1933883
theorem B8375339 : Blo 1287962 8375339 := bstep (se 1 (by rfl) ⟨6281504, by rfl⟩ : syracuseStep 8375339 = 12563009) B12563009
theorem B1289295 : Blo 1287962 1289295 := bstep (se 1 (by rfl) ⟨966971, by rfl⟩ : syracuseStep 1289295 = 1933943) B1933943
theorem B1289311 : Blo 1287962 1289311 := bstep (se 1 (by rfl) ⟨966983, by rfl⟩ : syracuseStep 1289311 = 1933967) B1933967
theorem B1289339 : Blo 1287962 1289339 := bstep (se 1 (by rfl) ⟨967004, by rfl⟩ : syracuseStep 1289339 = 1934009) B1934009
theorem B1289391 : Blo 1287962 1289391 := bstep (se 1 (by rfl) ⟨967043, by rfl⟩ : syracuseStep 1289391 = 1934087) B1934087
theorem B1289415 : Blo 1287962 1289415 := bstep (se 1 (by rfl) ⟨967061, by rfl⟩ : syracuseStep 1289415 = 1934123) B1934123
theorem B1289435 : Blo 1287962 1289435 := bstep (se 1 (by rfl) ⟨967076, by rfl⟩ : syracuseStep 1289435 = 1934153) B1934153
theorem B1289511 : Blo 1287962 1289511 := bstep (se 1 (by rfl) ⟨967133, by rfl⟩ : syracuseStep 1289511 = 1934267) B1934267
theorem B1289551 : Blo 1287962 1289551 := bstep (se 1 (by rfl) ⟨967163, by rfl⟩ : syracuseStep 1289551 = 1934327) B1934327
theorem B2174303 : Blo 1287962 2174303 := bstep (se 1 (by rfl) ⟨1630727, by rfl⟩ : syracuseStep 2174303 = 3261455) B3261455
theorem B1289567 : Blo 1287962 1289567 := bstep (se 1 (by rfl) ⟨967175, by rfl⟩ : syracuseStep 1289567 = 1934351) B1934351
theorem B1289595 : Blo 1287962 1289595 := bstep (se 1 (by rfl) ⟨967196, by rfl⟩ : syracuseStep 1289595 = 1934393) B1934393
theorem B7441789 : Blo 1287962 7441789 := bstep (se 3 (by rfl) ⟨1395335, by rfl⟩ : syracuseStep 7441789 = 2790671) B2790671
theorem B14683517 : Blo 1287962 14683517 := bstep (se 3 (by rfl) ⟨2753159, by rfl⟩ : syracuseStep 14683517 = 5506319) B5506319
theorem B1289647 : Blo 1287962 1289647 := bstep (se 1 (by rfl) ⟨967235, by rfl⟩ : syracuseStep 1289647 = 1934471) B1934471
theorem B1289671 : Blo 1287962 1289671 := bstep (se 1 (by rfl) ⟨967253, by rfl⟩ : syracuseStep 1289671 = 1934507) B1934507
theorem B1289691 : Blo 1287962 1289691 := bstep (se 1 (by rfl) ⟨967268, by rfl⟩ : syracuseStep 1289691 = 1934537) B1934537
theorem B1289767 : Blo 1287962 1289767 := bstep (se 1 (by rfl) ⟨967325, by rfl⟩ : syracuseStep 1289767 = 1934651) B1934651
theorem B1289807 : Blo 1287962 1289807 := bstep (se 1 (by rfl) ⟨967355, by rfl⟩ : syracuseStep 1289807 = 1934711) B1934711
theorem B1289823 : Blo 1287962 1289823 := bstep (se 1 (by rfl) ⟨967367, by rfl⟩ : syracuseStep 1289823 = 1934735) B1934735
theorem B3264097 : Blo 1287962 3264097 := bstep (se 2 (by rfl) ⟨1224036, by rfl⟩ : syracuseStep 3264097 = 2448073) B2448073
theorem B28241531 : Blo 1287962 28241531 := bstep (se 1 (by rfl) ⟨21181148, by rfl⟩ : syracuseStep 28241531 = 42362297) B42362297
theorem B1289851 : Blo 1287962 1289851 := bstep (se 1 (by rfl) ⟨967388, by rfl⟩ : syracuseStep 1289851 = 1934777) B1934777
theorem B11169413 : Blo 1287962 11169413 := bstep (se 4 (by rfl) ⟨1047132, by rfl⟩ : syracuseStep 11169413 = 2094265) B2094265
theorem B1289903 : Blo 1287962 1289903 := bstep (se 1 (by rfl) ⟨967427, by rfl⟩ : syracuseStep 1289903 = 1934855) B1934855
theorem B1289927 : Blo 1287962 1289927 := bstep (se 1 (by rfl) ⟨967445, by rfl⟩ : syracuseStep 1289927 = 1934891) B1934891
theorem B1289947 : Blo 1287962 1289947 := bstep (se 1 (by rfl) ⟨967460, by rfl⟩ : syracuseStep 1289947 = 1934921) B1934921
theorem B39694211 : Blo 1287962 39694211 := bstep (se 1 (by rfl) ⟨29770658, by rfl⟩ : syracuseStep 39694211 = 59541317) B59541317
theorem B2174863 : Blo 1287962 2174863 := bstep (se 1 (by rfl) ⟨1631147, by rfl⟩ : syracuseStep 2174863 = 3262295) B3262295
theorem B8261939 : Blo 1287962 8261939 := bstep (se 1 (by rfl) ⟨6196454, by rfl⟩ : syracuseStep 8261939 = 12392909) B12392909
theorem B5222717 : Blo 1287962 5222717 := bstep (se 3 (by rfl) ⟨979259, by rfl⟩ : syracuseStep 5222717 = 1958519) B1958519
theorem B6197609 : Blo 1287962 6197609 := bstep (se 2 (by rfl) ⟨2324103, by rfl⟩ : syracuseStep 6197609 = 4648207) B4648207
theorem B3265049 : Blo 1287962 3265049 := bstep (se 2 (by rfl) ⟨1224393, by rfl⟩ : syracuseStep 3265049 = 2448787) B2448787
theorem B2175545 : Blo 1287962 2175545 := bstep (se 2 (by rfl) ⟨815829, by rfl⟩ : syracuseStep 2175545 = 1631659) B1631659
theorem B2445947 : Blo 1287962 2445947 := bstep (se 1 (by rfl) ⟨1834460, by rfl⟩ : syracuseStep 2445947 = 3668921) B3668921
theorem B1987195 : Blo 1287962 1987195 := bstep (se 1 (by rfl) ⟨1490396, by rfl⟩ : syracuseStep 1987195 = 2980793) B2980793
theorem B4895417 : Blo 1287962 4895417 := bstep (se 2 (by rfl) ⟨1835781, by rfl⟩ : syracuseStep 4895417 = 3671563) B3671563
theorem B61985587 : Blo 1287962 61985587 := bstep (se 1 (by rfl) ⟨46489190, by rfl⟩ : syracuseStep 61985587 = 92978381) B92978381
theorem B2446175 : Blo 1287962 2446175 := bstep (se 1 (by rfl) ⟨1834631, by rfl⟩ : syracuseStep 2446175 = 3669263) B3669263
theorem B2356075 : Blo 1287962 2356075 := bstep (se 1 (by rfl) ⟨1767056, by rfl⟩ : syracuseStep 2356075 = 3534113) B3534113
theorem B3920903 : Blo 1287962 3920903 := bstep (se 1 (by rfl) ⟨2940677, by rfl⟩ : syracuseStep 3920903 = 5881355) B5881355
theorem B2323513 : Blo 1287962 2323513 := bstep (se 2 (by rfl) ⟨871317, by rfl⟩ : syracuseStep 2323513 = 1742635) B1742635
theorem B2446433 : Blo 1287962 2446433 := bstep (se 2 (by rfl) ⟨917412, by rfl⟩ : syracuseStep 2446433 = 1834825) B1834825
theorem B2176247 : Blo 1287962 2176247 := bstep (se 1 (by rfl) ⟨1632185, by rfl⟩ : syracuseStep 2176247 = 3264371) B3264371
theorem B2446699 : Blo 1287962 2446699 := bstep (se 1 (by rfl) ⟨1835024, by rfl⟩ : syracuseStep 2446699 = 3670049) B3670049
theorem B5371265 : Blo 1287962 5371265 := bstep (se 2 (by rfl) ⟨2014224, by rfl⟩ : syracuseStep 5371265 = 4028449) B4028449
theorem B4642267 : Blo 1287962 4642267 := bstep (se 1 (by rfl) ⟨3481700, by rfl⟩ : syracuseStep 4642267 = 6963401) B6963401
theorem B52917745 : Blo 1287962 52917745 := bstep (se 2 (by rfl) ⟨19844154, by rfl⟩ : syracuseStep 52917745 = 39688309) B39688309
theorem B4347431 : Blo 1287962 4347431 := bstep (se 1 (by rfl) ⟨3260573, by rfl⟩ : syracuseStep 4347431 = 6521147) B6521147
theorem B4183591 : Blo 1287962 4183591 := bstep (se 1 (by rfl) ⟨3137693, by rfl⟩ : syracuseStep 4183591 = 6275387) B6275387
theorem B2324047 : Blo 1287962 2324047 := bstep (se 1 (by rfl) ⟨1743035, by rfl⟩ : syracuseStep 2324047 = 3486071) B3486071
theorem B2176591 : Blo 1287962 2176591 := bstep (se 1 (by rfl) ⟨1632443, by rfl⟩ : syracuseStep 2176591 = 3264887) B3264887
theorem B4347539 : Blo 1287962 4347539 := bstep (se 1 (by rfl) ⟨3260654, by rfl⟩ : syracuseStep 4347539 = 6521309) B6521309
theorem B6280919 : Blo 1287962 6280919 := bstep (se 1 (by rfl) ⟨4710689, by rfl⟩ : syracuseStep 6280919 = 9421379) B9421379
theorem B4347755 : Blo 1287962 4347755 := bstep (se 1 (by rfl) ⟨3260816, by rfl⟩ : syracuseStep 4347755 = 6521633) B6521633
theorem B4347809 : Blo 1287962 4347809 := bstep (se 2 (by rfl) ⟨1630428, by rfl⟩ : syracuseStep 4347809 = 3260857) B3260857
theorem B2897927 : Blo 1287962 2897927 := bstep (se 1 (by rfl) ⟨2173445, by rfl⟩ : syracuseStep 2897927 = 4346891) B4346891
theorem B26441785 : Blo 1287962 26441785 := bstep (se 2 (by rfl) ⟨9915669, by rfl⟩ : syracuseStep 26441785 = 19831339) B19831339
theorem B8599609 : Blo 1287962 8599609 := bstep (se 2 (by rfl) ⟨3224853, by rfl⟩ : syracuseStep 8599609 = 6449707) B6449707
theorem B2897999 : Blo 1287962 2897999 := bstep (se 1 (by rfl) ⟨2173499, by rfl⟩ : syracuseStep 2897999 = 4346999) B4346999
theorem B59513089 : Blo 1287962 59513089 := bstep (se 2 (by rfl) ⟨22317408, by rfl⟩ : syracuseStep 59513089 = 44634817) B44634817
theorem B2611529 : Blo 1287962 2611529 := bstep (se 2 (by rfl) ⟨979323, by rfl⟩ : syracuseStep 2611529 = 1958647) B1958647
theorem B2750939 : Blo 1287962 2750939 := bstep (se 1 (by rfl) ⟨2063204, by rfl⟩ : syracuseStep 2750939 = 4126409) B4126409
theorem B2898395 : Blo 1287962 2898395 := bstep (se 1 (by rfl) ⟨2173796, by rfl⟩ : syracuseStep 2898395 = 4347593) B4347593
theorem B4348403 : Blo 1287962 4348403 := bstep (se 1 (by rfl) ⟨3261302, by rfl⟩ : syracuseStep 4348403 = 6522605) B6522605
theorem B8370697 : Blo 1287962 8370697 := bstep (se 2 (by rfl) ⟨3139011, by rfl⟩ : syracuseStep 8370697 = 6278023) B6278023
theorem B2447891 : Blo 1287962 2447891 := bstep (se 1 (by rfl) ⟨1835918, by rfl⟩ : syracuseStep 2447891 = 3671837) B3671837
theorem B10451591 : Blo 1287962 10451591 := bstep (se 1 (by rfl) ⟨7838693, by rfl⟩ : syracuseStep 10451591 = 15677387) B15677387
theorem B9788039 : Blo 1287962 9788039 := bstep (se 1 (by rfl) ⟨7341029, by rfl⟩ : syracuseStep 9788039 = 14682059) B14682059
theorem B1931975 : Blo 1287962 1931975 := bstep (se 1 (by rfl) ⟨1448981, by rfl⟩ : syracuseStep 1931975 = 2897963) B2897963
theorem B7338707 : Blo 1287962 7338707 := bstep (se 1 (by rfl) ⟨5504030, by rfl⟩ : syracuseStep 7338707 = 11008061) B11008061
theorem B2448119 : Blo 1287962 2448119 := bstep (se 1 (by rfl) ⟨1836089, by rfl⟩ : syracuseStep 2448119 = 3672179) B3672179
theorem B4897529 : Blo 1287962 4897529 := bstep (se 2 (by rfl) ⟨1836573, by rfl⟩ : syracuseStep 4897529 = 3673147) B3673147
theorem B3922681 : Blo 1287962 3922681 := bstep (se 2 (by rfl) ⟨1471005, by rfl⟩ : syracuseStep 3922681 = 2942011) B2942011
theorem B4643651 : Blo 1287962 4643651 := bstep (se 1 (by rfl) ⟨3482738, by rfl⟩ : syracuseStep 4643651 = 6965477) B6965477
theorem B2120521 : Blo 1287962 2120521 := bstep (se 2 (by rfl) ⟨795195, by rfl⟩ : syracuseStep 2120521 = 1590391) B1590391
theorem B1932137 : Blo 1287962 1932137 := bstep (se 2 (by rfl) ⟨724551, by rfl⟩ : syracuseStep 1932137 = 1449103) B1449103
theorem B2898863 : Blo 1287962 2898863 := bstep (se 1 (by rfl) ⟨2174147, by rfl⟩ : syracuseStep 2898863 = 4348295) B4348295
theorem B1932215 : Blo 1287962 1932215 := bstep (se 1 (by rfl) ⟨1449161, by rfl⟩ : syracuseStep 1932215 = 2898323) B2898323
theorem B1932251 : Blo 1287962 1932251 := bstep (se 1 (by rfl) ⟨1449188, by rfl⟩ : syracuseStep 1932251 = 2898377) B2898377
theorem B4348943 : Blo 1287962 4348943 := bstep (se 1 (by rfl) ⟨3261707, by rfl⟩ : syracuseStep 4348943 = 6523415) B6523415
theorem B3529807 : Blo 1287962 3529807 := bstep (se 1 (by rfl) ⟨2647355, by rfl⟩ : syracuseStep 3529807 = 5294711) B5294711
theorem B2899115 : Blo 1287962 2899115 := bstep (se 1 (by rfl) ⟨2174336, by rfl⟩ : syracuseStep 2899115 = 4348673) B4348673
theorem B3669239 : Blo 1287962 3669239 := bstep (se 1 (by rfl) ⟨2751929, by rfl⟩ : syracuseStep 3669239 = 5503859) B5503859
theorem B10452239 : Blo 1287962 10452239 := bstep (se 1 (by rfl) ⟨7839179, by rfl⟩ : syracuseStep 10452239 = 15678359) B15678359
theorem B20913497 : Blo 1287962 20913497 := bstep (se 2 (by rfl) ⟨7842561, by rfl⟩ : syracuseStep 20913497 = 15685123) B15685123
theorem B1449391 : Blo 1287962 1449391 := bstep (se 1 (by rfl) ⟨1087043, by rfl⟩ : syracuseStep 1449391 = 2174087) B2174087
theorem B1932719 : Blo 1287962 1932719 := bstep (se 1 (by rfl) ⟨1449539, by rfl⟩ : syracuseStep 1932719 = 2899079) B2899079
theorem B79396301 : Blo 1287962 79396301 := bstep (se 3 (by rfl) ⟨14886806, by rfl⟩ : syracuseStep 79396301 = 29773613) B29773613
theorem B3137011 : Blo 1287962 3137011 := bstep (se 1 (by rfl) ⟨2352758, by rfl⟩ : syracuseStep 3137011 = 4705517) B4705517
theorem B1932809 : Blo 1287962 1932809 := bstep (se 2 (by rfl) ⟨724803, by rfl⟩ : syracuseStep 1932809 = 1449607) B1449607
theorem B1932839 : Blo 1287962 1932839 := bstep (se 1 (by rfl) ⟨1449629, by rfl⟩ : syracuseStep 1932839 = 2899259) B2899259
theorem B4349537 : Blo 1287962 4349537 := bstep (se 2 (by rfl) ⟨1631076, by rfl⟩ : syracuseStep 4349537 = 3262153) B3262153
theorem B1932923 : Blo 1287962 1932923 := bstep (se 1 (by rfl) ⟨1449692, by rfl⟩ : syracuseStep 1932923 = 2899385) B2899385
theorem B2899655 : Blo 1287962 2899655 := bstep (se 1 (by rfl) ⟨2174741, by rfl⟩ : syracuseStep 2899655 = 4349483) B4349483
theorem B1933049 : Blo 1287962 1933049 := bstep (se 2 (by rfl) ⟨724893, by rfl⟩ : syracuseStep 1933049 = 1449787) B1449787
theorem B6528761 : Blo 1287962 6528761 := bstep (se 2 (by rfl) ⟨2448285, by rfl⟩ : syracuseStep 6528761 = 4896571) B4896571
theorem B275029775 : Blo 1287962 275029775 := bstep (se 1 (by rfl) ⟨206272331, by rfl⟩ : syracuseStep 275029775 = 412544663) B412544663
theorem B1449823 : Blo 1287962 1449823 := bstep (se 1 (by rfl) ⟨1087367, by rfl⟩ : syracuseStep 1449823 = 2174735) B2174735
theorem B1933151 : Blo 1287962 1933151 := bstep (se 1 (by rfl) ⟨1449863, by rfl⟩ : syracuseStep 1933151 = 2899727) B2899727
theorem B1834859 : Blo 1287962 1834859 := bstep (se 1 (by rfl) ⟨1376144, by rfl⟩ : syracuseStep 1834859 = 2752289) B2752289
theorem B1933163 : Blo 1287962 1933163 := bstep (se 1 (by rfl) ⟨1449872, by rfl⟩ : syracuseStep 1933163 = 2899745) B2899745
theorem B3260321 : Blo 1287962 3260321 := bstep (se 2 (by rfl) ⟨1222620, by rfl⟩ : syracuseStep 3260321 = 2445241) B2445241
theorem B4407215 : Blo 1287962 4407215 := bstep (se 1 (by rfl) ⟨3305411, by rfl⟩ : syracuseStep 4407215 = 6610823) B6610823
theorem B1630135 : Blo 1287962 1630135 := bstep (se 1 (by rfl) ⟨1222601, by rfl⟩ : syracuseStep 1630135 = 2445203) B2445203
theorem B6520985 : Blo 1287962 6520985 := bstep (se 2 (by rfl) ⟨2445369, by rfl⟩ : syracuseStep 6520985 = 4890739) B4890739
theorem B3481811 : Blo 1287962 3481811 := bstep (se 1 (by rfl) ⟨2611358, by rfl⟩ : syracuseStep 3481811 = 5222717) B5222717
theorem B3096787 : Blo 1287962 3096787 := bstep (se 1 (by rfl) ⟨2322590, by rfl⟩ : syracuseStep 3096787 = 4645181) B4645181
theorem B1933577 : Blo 1287962 1933577 := bstep (se 2 (by rfl) ⟨725091, by rfl⟩ : syracuseStep 1933577 = 1450183) B1450183
theorem B3670379 : Blo 1287962 3670379 := bstep (se 1 (by rfl) ⟨2752784, by rfl⟩ : syracuseStep 3670379 = 5505569) B5505569
theorem B2752879 : Blo 1287962 2752879 := bstep (se 1 (by rfl) ⟨2064659, by rfl⟩ : syracuseStep 2752879 = 4129319) B4129319
theorem B1933679 : Blo 1287962 1933679 := bstep (se 1 (by rfl) ⟨1450259, by rfl⟩ : syracuseStep 1933679 = 2900519) B2900519
theorem B1376623 : Blo 1287962 1376623 := bstep (se 1 (by rfl) ⟨1032467, by rfl⟩ : syracuseStep 1376623 = 2064935) B2064935
theorem B1450363 : Blo 1287962 1450363 := bstep (se 1 (by rfl) ⟨1087772, by rfl⟩ : syracuseStep 1450363 = 2175545) B2175545
theorem B18825637 : Blo 1287962 18825637 := bstep (se 4 (by rfl) ⟨1764903, by rfl⟩ : syracuseStep 18825637 = 3529807) B3529807
theorem B1630631 : Blo 1287962 1630631 := bstep (se 1 (by rfl) ⟨1222973, by rfl⟩ : syracuseStep 1630631 = 2445947) B2445947
theorem B31375781 : Blo 1287962 31375781 := bstep (se 4 (by rfl) ⟨2941479, by rfl⟩ : syracuseStep 31375781 = 5882959) B5882959
theorem B3670447 : Blo 1287962 3670447 := bstep (se 1 (by rfl) ⟨2752835, by rfl⟩ : syracuseStep 3670447 = 5505671) B5505671
theorem B5505499 : Blo 1287962 5505499 := bstep (se 1 (by rfl) ⟨4129124, by rfl⟩ : syracuseStep 5505499 = 8258249) B8258249
theorem B1630783 : Blo 1287962 1630783 := bstep (se 1 (by rfl) ⟨1223087, by rfl⟩ : syracuseStep 1630783 = 2446175) B2446175
theorem B3260999 : Blo 1287962 3260999 := bstep (se 1 (by rfl) ⟨2445749, by rfl⟩ : syracuseStep 3260999 = 4891499) B4891499
theorem B1933895 : Blo 1287962 1933895 := bstep (se 1 (by rfl) ⟨1450421, by rfl⟩ : syracuseStep 1933895 = 2900843) B2900843
theorem B1933931 : Blo 1287962 1933931 := bstep (se 1 (by rfl) ⟨1450448, by rfl⟩ : syracuseStep 1933931 = 2900897) B2900897
theorem B4129433 : Blo 1287962 4129433 := bstep (se 2 (by rfl) ⟨1548537, by rfl⟩ : syracuseStep 4129433 = 3097075) B3097075
theorem B4350617 : Blo 1287962 4350617 := bstep (se 2 (by rfl) ⟨1631481, by rfl⟩ : syracuseStep 4350617 = 3262963) B3262963
theorem B2613935 : Blo 1287962 2613935 := bstep (se 1 (by rfl) ⟨1960451, by rfl⟩ : syracuseStep 2613935 = 3920903) B3920903
theorem B2900663 : Blo 1287962 2900663 := bstep (se 1 (by rfl) ⟨2175497, by rfl⟩ : syracuseStep 2900663 = 4350995) B4350995
theorem B1630955 : Blo 1287962 1630955 := bstep (se 1 (by rfl) ⟨1223216, by rfl⟩ : syracuseStep 1630955 = 2446433) B2446433
theorem B1934159 : Blo 1287962 1934159 := bstep (se 1 (by rfl) ⟨1450619, by rfl⟩ : syracuseStep 1934159 = 2901239) B2901239
theorem B1450831 : Blo 1287962 1450831 := bstep (se 1 (by rfl) ⟨1088123, by rfl⟩ : syracuseStep 1450831 = 2176247) B2176247
theorem B2900879 : Blo 1287962 2900879 := bstep (se 1 (by rfl) ⟨2175659, by rfl⟩ : syracuseStep 2900879 = 4351319) B4351319
theorem B23528339 : Blo 1287962 23528339 := bstep (se 1 (by rfl) ⟨17646254, by rfl⟩ : syracuseStep 23528339 = 35292509) B35292509
theorem B3580843 : Blo 1287962 3580843 := bstep (se 1 (by rfl) ⟨2685632, by rfl⟩ : syracuseStep 3580843 = 5371265) B5371265
theorem B6521795 : Blo 1287962 6521795 := bstep (se 1 (by rfl) ⟨4891346, by rfl⟩ : syracuseStep 6521795 = 9782693) B9782693
theorem B2827361 : Blo 1287962 2827361 := bstep (se 2 (by rfl) ⟨1060260, by rfl⟩ : syracuseStep 2827361 = 2120521) B2120521
theorem B4187279 : Blo 1287962 4187279 := bstep (se 1 (by rfl) ⟨3140459, by rfl⟩ : syracuseStep 4187279 = 6280919) B6280919
theorem B211723469 : Blo 1287962 211723469 := bstep (se 3 (by rfl) ⟨39698150, by rfl⟩ : syracuseStep 211723469 = 79396301) B79396301
theorem B1934555 : Blo 1287962 1934555 := bstep (se 1 (by rfl) ⟨1450916, by rfl⟩ : syracuseStep 1934555 = 2901833) B2901833
theorem B3671335 : Blo 1287962 3671335 := bstep (se 1 (by rfl) ⟨2753501, by rfl⟩ : syracuseStep 3671335 = 5507003) B5507003
theorem B2753929 : Blo 1287962 2753929 := bstep (se 2 (by rfl) ⟨1032723, by rfl⟩ : syracuseStep 2753929 = 2065447) B2065447
theorem B1934729 : Blo 1287962 1934729 := bstep (se 2 (by rfl) ⟨725523, by rfl⟩ : syracuseStep 1934729 = 1451047) B1451047
theorem B3098017 : Blo 1287962 3098017 := bstep (se 2 (by rfl) ⟨1161756, by rfl⟩ : syracuseStep 3098017 = 2323513) B2323513
theorem B2901599 : Blo 1287962 2901599 := bstep (se 1 (by rfl) ⟨2176199, by rfl⟩ : syracuseStep 2901599 = 4352399) B4352399
theorem B1631927 : Blo 1287962 1631927 := bstep (se 1 (by rfl) ⟨1223945, by rfl⟩ : syracuseStep 1631927 = 2447891) B2447891
theorem B1287983 : Blo 1287962 1287983 := bstep (se 1 (by rfl) ⟨965987, by rfl⟩ : syracuseStep 1287983 = 1931975) B1931975
theorem B4892471 : Blo 1287962 4892471 := bstep (se 1 (by rfl) ⟨3669353, by rfl⟩ : syracuseStep 4892471 = 7338707) B7338707
theorem B3262265 : Blo 1287962 3262265 := bstep (se 2 (by rfl) ⟨1223349, by rfl⟩ : syracuseStep 3262265 = 2446699) B2446699
theorem B2901815 : Blo 1287962 2901815 := bstep (se 1 (by rfl) ⟨2176361, by rfl⟩ : syracuseStep 2901815 = 4352723) B4352723
theorem B1632079 : Blo 1287962 1632079 := bstep (se 1 (by rfl) ⟨1224059, by rfl⟩ : syracuseStep 1632079 = 2448119) B2448119
theorem B9922385 : Blo 1287962 9922385 := bstep (se 2 (by rfl) ⟨3720894, by rfl⟩ : syracuseStep 9922385 = 7441789) B7441789
theorem B1288091 : Blo 1287962 1288091 := bstep (se 1 (by rfl) ⟨966068, by rfl⟩ : syracuseStep 1288091 = 1932137) B1932137
theorem B1288143 : Blo 1287962 1288143 := bstep (se 1 (by rfl) ⟨966107, by rfl⟩ : syracuseStep 1288143 = 1932215) B1932215
theorem B1288167 : Blo 1287962 1288167 := bstep (se 1 (by rfl) ⟨966125, by rfl⟩ : syracuseStep 1288167 = 1932251) B1932251
theorem B3098729 : Blo 1287962 3098729 := bstep (se 2 (by rfl) ⟨1162023, by rfl⟩ : syracuseStep 3098729 = 2324047) B2324047
theorem B2902121 : Blo 1287962 2902121 := bstep (se 2 (by rfl) ⟨1088295, by rfl⟩ : syracuseStep 2902121 = 2176591) B2176591
theorem B4352129 : Blo 1287962 4352129 := bstep (se 2 (by rfl) ⟨1632048, by rfl⟩ : syracuseStep 4352129 = 3264097) B3264097
theorem B4892957 : Blo 1287962 4892957 := bstep (se 3 (by rfl) ⟨917429, by rfl⟩ : syracuseStep 4892957 = 1834859) B1834859
theorem B1288479 : Blo 1287962 1288479 := bstep (se 1 (by rfl) ⟨966359, by rfl⟩ : syracuseStep 1288479 = 1932719) B1932719
theorem B1288539 : Blo 1287962 1288539 := bstep (se 1 (by rfl) ⟨966404, by rfl⟩ : syracuseStep 1288539 = 1932809) B1932809
theorem B1288559 : Blo 1287962 1288559 := bstep (se 1 (by rfl) ⟨966419, by rfl⟩ : syracuseStep 1288559 = 1932839) B1932839
theorem B18827687 : Blo 1287962 18827687 := bstep (se 1 (by rfl) ⟨14120765, by rfl⟩ : syracuseStep 18827687 = 28241531) B28241531
theorem B1288615 : Blo 1287962 1288615 := bstep (se 1 (by rfl) ⟨966461, by rfl⟩ : syracuseStep 1288615 = 1932923) B1932923
theorem B1288699 : Blo 1287962 1288699 := bstep (se 1 (by rfl) ⟨966524, by rfl⟩ : syracuseStep 1288699 = 1933049) B1933049
theorem B4352507 : Blo 1287962 4352507 := bstep (se 1 (by rfl) ⟨3264380, by rfl⟩ : syracuseStep 4352507 = 6528761) B6528761
theorem B1288767 : Blo 1287962 1288767 := bstep (se 1 (by rfl) ⟨966575, by rfl⟩ : syracuseStep 1288767 = 1933151) B1933151
theorem B1288775 : Blo 1287962 1288775 := bstep (se 1 (by rfl) ⟨966581, by rfl⟩ : syracuseStep 1288775 = 1933163) B1933163
theorem B2173513 : Blo 1287962 2173513 := bstep (se 2 (by rfl) ⟨815067, by rfl⟩ : syracuseStep 2173513 = 1630135) B1630135
theorem B26462807 : Blo 1287962 26462807 := bstep (se 1 (by rfl) ⟨19847105, by rfl⟩ : syracuseStep 26462807 = 39694211) B39694211
theorem B16730725 : Blo 1287962 16730725 := bstep (se 4 (by rfl) ⟨1568505, by rfl⟩ : syracuseStep 16730725 = 3137011) B3137011
theorem B2173547 : Blo 1287962 2173547 := bstep (se 1 (by rfl) ⟨1630160, by rfl⟩ : syracuseStep 2173547 = 3260321) B3260321
theorem B1288927 : Blo 1287962 1288927 := bstep (se 1 (by rfl) ⟨966695, by rfl⟩ : syracuseStep 1288927 = 1933391) B1933391
theorem B22334237 : Blo 1287962 22334237 := bstep (se 3 (by rfl) ⟨4187669, by rfl⟩ : syracuseStep 22334237 = 8375339) B8375339
theorem B1289007 : Blo 1287962 1289007 := bstep (se 1 (by rfl) ⟨966755, by rfl⟩ : syracuseStep 1289007 = 1933511) B1933511
theorem B1289115 : Blo 1287962 1289115 := bstep (se 1 (by rfl) ⟨966836, by rfl⟩ : syracuseStep 1289115 = 1933673) B1933673
theorem B4131739 : Blo 1287962 4131739 := bstep (se 1 (by rfl) ⟨3098804, by rfl⟩ : syracuseStep 4131739 = 6197609) B6197609
theorem B4352939 : Blo 1287962 4352939 := bstep (se 1 (by rfl) ⟨3264704, by rfl⟩ : syracuseStep 4352939 = 6529409) B6529409
theorem B1289167 : Blo 1287962 1289167 := bstep (se 1 (by rfl) ⟨966875, by rfl⟩ : syracuseStep 1289167 = 1933751) B1933751
theorem B1289191 : Blo 1287962 1289191 := bstep (se 1 (by rfl) ⟨966893, by rfl⟩ : syracuseStep 1289191 = 1933787) B1933787
theorem B79350785 : Blo 1287962 79350785 := bstep (se 2 (by rfl) ⟨29756544, by rfl⟩ : syracuseStep 79350785 = 59513089) B59513089
theorem B3263611 : Blo 1287962 3263611 := bstep (se 1 (by rfl) ⟨2447708, by rfl⟩ : syracuseStep 3263611 = 4895417) B4895417
theorem B3484891 : Blo 1287962 3484891 := bstep (se 1 (by rfl) ⟨2613668, by rfl⟩ : syracuseStep 3484891 = 5227337) B5227337
theorem B1289503 : Blo 1287962 1289503 := bstep (se 1 (by rfl) ⟨967127, by rfl⟩ : syracuseStep 1289503 = 1934255) B1934255
theorem B10448189 : Blo 1287962 10448189 := bstep (se 3 (by rfl) ⟨1959035, by rfl⟩ : syracuseStep 10448189 = 3918071) B3918071
theorem B9784637 : Blo 1287962 9784637 := bstep (se 3 (by rfl) ⟨1834619, by rfl⟩ : syracuseStep 9784637 = 3669239) B3669239
theorem B1289563 : Blo 1287962 1289563 := bstep (se 1 (by rfl) ⟨967172, by rfl⟩ : syracuseStep 1289563 = 1934345) B1934345
theorem B11160929 : Blo 1287962 11160929 := bstep (se 2 (by rfl) ⟨4185348, by rfl⟩ : syracuseStep 11160929 = 8370697) B8370697
theorem B1289583 : Blo 1287962 1289583 := bstep (se 1 (by rfl) ⟨967187, by rfl⟩ : syracuseStep 1289583 = 1934375) B1934375
theorem B3485065 : Blo 1287962 3485065 := bstep (se 2 (by rfl) ⟨1306899, by rfl⟩ : syracuseStep 3485065 = 2613799) B2613799
theorem B1289639 : Blo 1287962 1289639 := bstep (se 1 (by rfl) ⟨967229, by rfl⟩ : syracuseStep 1289639 = 1934459) B1934459
theorem B4353479 : Blo 1287962 4353479 := bstep (se 1 (by rfl) ⟨3265109, by rfl⟩ : syracuseStep 4353479 = 6530219) B6530219
theorem B22031837 : Blo 1287962 22031837 := bstep (se 3 (by rfl) ⟨4130969, by rfl⟩ : syracuseStep 22031837 = 8261939) B8261939
theorem B2649593 : Blo 1287962 2649593 := bstep (se 2 (by rfl) ⟨993597, by rfl⟩ : syracuseStep 2649593 = 1987195) B1987195
theorem B1289723 : Blo 1287962 1289723 := bstep (se 1 (by rfl) ⟨967292, by rfl⟩ : syracuseStep 1289723 = 1934585) B1934585
theorem B1289791 : Blo 1287962 1289791 := bstep (se 1 (by rfl) ⟨967343, by rfl⟩ : syracuseStep 1289791 = 1934687) B1934687
theorem B1289799 : Blo 1287962 1289799 := bstep (se 1 (by rfl) ⟨967349, by rfl⟩ : syracuseStep 1289799 = 1934699) B1934699
theorem B5230241 : Blo 1287962 5230241 := bstep (se 2 (by rfl) ⟨1961340, by rfl⟩ : syracuseStep 5230241 = 3922681) B3922681
theorem B1289951 : Blo 1287962 1289951 := bstep (se 1 (by rfl) ⟨967463, by rfl⟩ : syracuseStep 1289951 = 1934927) B1934927
theorem B3141433 : Blo 1287962 3141433 := bstep (se 2 (by rfl) ⟨1178037, by rfl⟩ : syracuseStep 3141433 = 2356075) B2356075
theorem B37146437 : Blo 1287962 37146437 := bstep (se 4 (by rfl) ⟨3482478, by rfl⟩ : syracuseStep 37146437 = 6964957) B6964957
theorem B4894931 : Blo 1287962 4894931 := bstep (se 1 (by rfl) ⟨3671198, by rfl⟩ : syracuseStep 4894931 = 7342397) B7342397
theorem B1741019 : Blo 1287962 1741019 := bstep (se 1 (by rfl) ⟨1305764, by rfl⟩ : syracuseStep 1741019 = 2611529) B2611529
theorem B2175241 : Blo 1287962 2175241 := bstep (se 2 (by rfl) ⟨815715, by rfl⟩ : syracuseStep 2175241 = 1631431) B1631431
theorem B3486025 : Blo 1287962 3486025 := bstep (se 2 (by rfl) ⟨1307259, by rfl⟩ : syracuseStep 3486025 = 2614519) B2614519
theorem B2322799 : Blo 1287962 2322799 := bstep (se 1 (by rfl) ⟨1742099, by rfl⟩ : syracuseStep 2322799 = 3484199) B3484199
theorem B6967727 : Blo 1287962 6967727 := bstep (se 1 (by rfl) ⟨5225795, by rfl⟩ : syracuseStep 6967727 = 10451591) B10451591
theorem B6525359 : Blo 1287962 6525359 := bstep (se 1 (by rfl) ⟨4894019, by rfl⟩ : syracuseStep 6525359 = 9788039) B9788039
theorem B3265019 : Blo 1287962 3265019 := bstep (se 1 (by rfl) ⟨2448764, by rfl⟩ : syracuseStep 3265019 = 4897529) B4897529
theorem B6189689 : Blo 1287962 6189689 := bstep (se 2 (by rfl) ⟨2321133, by rfl⟩ : syracuseStep 6189689 = 4642267) B4642267
theorem B9286265 : Blo 1287962 9286265 := bstep (se 2 (by rfl) ⟨3482349, by rfl⟩ : syracuseStep 9286265 = 6964699) B6964699
theorem B3486329 : Blo 1287962 3486329 := bstep (se 2 (by rfl) ⟨1307373, by rfl⟩ : syracuseStep 3486329 = 2614747) B2614747
theorem B2355895 : Blo 1287962 2355895 := bstep (se 1 (by rfl) ⟨1766921, by rfl⟩ : syracuseStep 2355895 = 3533843) B3533843
theorem B6968159 : Blo 1287962 6968159 := bstep (se 1 (by rfl) ⟨5226119, by rfl⟩ : syracuseStep 6968159 = 10452239) B10452239
theorem B7844921 : Blo 1287962 7844921 := bstep (se 2 (by rfl) ⟨2941845, by rfl⟩ : syracuseStep 7844921 = 5883691) B5883691
theorem B11752573 : Blo 1287962 11752573 := bstep (se 3 (by rfl) ⟨2203607, by rfl⟩ : syracuseStep 11752573 = 4407215) B4407215
theorem B6526331 : Blo 1287962 6526331 := bstep (se 1 (by rfl) ⟨4894748, by rfl⟩ : syracuseStep 6526331 = 9789497) B9789497
theorem B2938361 : Blo 1287962 2938361 := bstep (se 2 (by rfl) ⟨1101885, by rfl⟩ : syracuseStep 2938361 = 2203771) B2203771
theorem B141022853 : Blo 1287962 141022853 := bstep (se 4 (by rfl) ⟨13220892, by rfl⟩ : syracuseStep 141022853 = 26441785) B26441785
theorem B45864581 : Blo 1287962 45864581 := bstep (se 4 (by rfl) ⟨4299804, by rfl⟩ : syracuseStep 45864581 = 8599609) B8599609
theorem B9787067 : Blo 1287962 9787067 := bstep (se 1 (by rfl) ⟨7340300, by rfl⟩ : syracuseStep 9787067 = 14680601) B14680601
theorem B2176699 : Blo 1287962 2176699 := bstep (se 1 (by rfl) ⟨1632524, by rfl⟩ : syracuseStep 2176699 = 3265049) B3265049
theorem B2898287 : Blo 1287962 2898287 := bstep (se 1 (by rfl) ⟨2173715, by rfl⟩ : syracuseStep 2898287 = 4347431) B4347431
theorem B82647449 : Blo 1287962 82647449 := bstep (se 2 (by rfl) ⟨30992793, by rfl⟩ : syracuseStep 82647449 = 61985587) B61985587
theorem B2898359 : Blo 1287962 2898359 := bstep (se 1 (by rfl) ⟨2173769, by rfl⟩ : syracuseStep 2898359 = 4347539) B4347539
theorem B2898503 : Blo 1287962 2898503 := bstep (se 1 (by rfl) ⟨2173877, by rfl⟩ : syracuseStep 2898503 = 4347755) B4347755
theorem B2898539 : Blo 1287962 2898539 := bstep (se 1 (by rfl) ⟨2173904, by rfl⟩ : syracuseStep 2898539 = 4347809) B4347809
theorem B6527627 : Blo 1287962 6527627 := bstep (se 1 (by rfl) ⟨4895720, by rfl⟩ : syracuseStep 6527627 = 9791441) B9791441
theorem B1931951 : Blo 1287962 1931951 := bstep (se 1 (by rfl) ⟨1448963, by rfl⟩ : syracuseStep 1931951 = 2897927) B2897927
theorem B3922607 : Blo 1287962 3922607 := bstep (se 1 (by rfl) ⟨2941955, by rfl⟩ : syracuseStep 3922607 = 5883911) B5883911
theorem B1931999 : Blo 1287962 1931999 := bstep (se 1 (by rfl) ⟨1448999, by rfl⟩ : syracuseStep 1931999 = 2897999) B2897999
theorem B1833959 : Blo 1287962 1833959 := bstep (se 1 (by rfl) ⟨1375469, by rfl⟩ : syracuseStep 1833959 = 2750939) B2750939
theorem B1932263 : Blo 1287962 1932263 := bstep (se 1 (by rfl) ⟨1449197, by rfl⟩ : syracuseStep 1932263 = 2898395) B2898395
theorem B2898935 : Blo 1287962 2898935 := bstep (se 1 (by rfl) ⟨2174201, by rfl⟩ : syracuseStep 2898935 = 4348403) B4348403
theorem B4349051 : Blo 1287962 4349051 := bstep (se 1 (by rfl) ⟨3261788, by rfl⟩ : syracuseStep 4349051 = 6523577) B6523577
theorem B3095767 : Blo 1287962 3095767 := bstep (se 1 (by rfl) ⟨2321825, by rfl⟩ : syracuseStep 3095767 = 4643651) B4643651
theorem B2612443 : Blo 1287962 2612443 := bstep (se 1 (by rfl) ⟨1959332, by rfl⟩ : syracuseStep 2612443 = 3918665) B3918665
theorem B13941989 : Blo 1287962 13941989 := bstep (se 4 (by rfl) ⟨1307061, by rfl⟩ : syracuseStep 13941989 = 2614123) B2614123
theorem B1932521 : Blo 1287962 1932521 := bstep (se 2 (by rfl) ⟨724695, by rfl⟩ : syracuseStep 1932521 = 1449391) B1449391
theorem B1449247 : Blo 1287962 1449247 := bstep (se 1 (by rfl) ⟨1086935, by rfl⟩ : syracuseStep 1449247 = 2173871) B2173871
theorem B1932575 : Blo 1287962 1932575 := bstep (se 1 (by rfl) ⟨1449431, by rfl⟩ : syracuseStep 1932575 = 2898863) B2898863
theorem B70556993 : Blo 1287962 70556993 := bstep (se 2 (by rfl) ⟨26458872, by rfl⟩ : syracuseStep 70556993 = 52917745) B52917745
theorem B2899295 : Blo 1287962 2899295 := bstep (se 1 (by rfl) ⟨2174471, by rfl⟩ : syracuseStep 2899295 = 4348943) B4348943
theorem B5578121 : Blo 1287962 5578121 := bstep (se 2 (by rfl) ⟨2091795, by rfl⟩ : syracuseStep 5578121 = 4183591) B4183591
theorem B4349321 : Blo 1287962 4349321 := bstep (se 2 (by rfl) ⟨1630995, by rfl⟩ : syracuseStep 4349321 = 3261991) B3261991
theorem B1932743 : Blo 1287962 1932743 := bstep (se 1 (by rfl) ⟨1449557, by rfl⟩ : syracuseStep 1932743 = 2899115) B2899115
theorem B13942331 : Blo 1287962 13942331 := bstep (se 1 (by rfl) ⟨10456748, by rfl⟩ : syracuseStep 13942331 = 20913497) B20913497
theorem B1449535 : Blo 1287962 1449535 := bstep (se 1 (by rfl) ⟨1087151, by rfl⟩ : syracuseStep 1449535 = 2174303) B2174303
theorem B9789011 : Blo 1287962 9789011 := bstep (se 1 (by rfl) ⟨7341758, by rfl⟩ : syracuseStep 9789011 = 14683517) B14683517
theorem B2899691 : Blo 1287962 2899691 := bstep (se 1 (by rfl) ⟨2174768, by rfl⟩ : syracuseStep 2899691 = 4349537) B4349537
theorem B7446275 : Blo 1287962 7446275 := bstep (se 1 (by rfl) ⟨5584706, by rfl⟩ : syracuseStep 7446275 = 11169413) B11169413
theorem B1933097 : Blo 1287962 1933097 := bstep (se 2 (by rfl) ⟨724911, by rfl⟩ : syracuseStep 1933097 = 1449823) B1449823
theorem B1933103 : Blo 1287962 1933103 := bstep (se 1 (by rfl) ⟨1449827, by rfl⟩ : syracuseStep 1933103 = 2899655) B2899655
theorem B4349753 : Blo 1287962 4349753 := bstep (se 2 (by rfl) ⟨1631157, by rfl⟩ : syracuseStep 4349753 = 3262315) B3262315
theorem B183353183 : Blo 1287962 183353183 := bstep (se 1 (by rfl) ⟨137514887, by rfl⟩ : syracuseStep 183353183 = 275029775) B275029775
theorem B2899817 : Blo 1287962 2899817 := bstep (se 2 (by rfl) ⟨1087431, by rfl⟩ : syracuseStep 2899817 = 2174863) B2174863
theorem B4129049 : Blo 1287962 4129049 := bstep (se 2 (by rfl) ⟨1548393, by rfl⟩ : syracuseStep 4129049 = 3096787) B3096787
theorem B4645151 : Blo 1287962 4645151 := bstep (se 1 (by rfl) ⟨3483863, by rfl⟩ : syracuseStep 4645151 = 6967727) B6967727
theorem B4350239 : Blo 1287962 4350239 := bstep (se 1 (by rfl) ⟨3262679, by rfl⟩ : syracuseStep 4350239 = 6525359) B6525359
theorem B2900321 : Blo 1287962 2900321 := bstep (se 2 (by rfl) ⟨1087620, by rfl⟩ : syracuseStep 2900321 = 2175241) B2175241
theorem B2752955 : Blo 1287962 2752955 := bstep (se 1 (by rfl) ⟨2064716, by rfl⟩ : syracuseStep 2752955 = 4129433) B4129433
theorem B2900411 : Blo 1287962 2900411 := bstep (se 1 (by rfl) ⟨2175308, by rfl⟩ : syracuseStep 2900411 = 4350617) B4350617
theorem B1933775 : Blo 1287962 1933775 := bstep (se 1 (by rfl) ⟨1450331, by rfl⟩ : syracuseStep 1933775 = 2900663) B2900663
theorem B3670505 : Blo 1287962 3670505 := bstep (se 2 (by rfl) ⟨1376439, by rfl⟩ : syracuseStep 3670505 = 2752879) B2752879
theorem B1835497 : Blo 1287962 1835497 := bstep (se 2 (by rfl) ⟨688311, by rfl⟩ : syracuseStep 1835497 = 1376623) B1376623
theorem B1933817 : Blo 1287962 1933817 := bstep (se 2 (by rfl) ⟨725181, by rfl⟩ : syracuseStep 1933817 = 1450363) B1450363
theorem B25100849 : Blo 1287962 25100849 := bstep (se 2 (by rfl) ⟨9412818, by rfl⟩ : syracuseStep 25100849 = 18825637) B18825637
theorem B4645439 : Blo 1287962 4645439 := bstep (se 1 (by rfl) ⟨3484079, by rfl⟩ : syracuseStep 4645439 = 6968159) B6968159
theorem B1933919 : Blo 1287962 1933919 := bstep (se 1 (by rfl) ⟨1450439, by rfl⟩ : syracuseStep 1933919 = 2900879) B2900879
theorem B7340665 : Blo 1287962 7340665 := bstep (se 2 (by rfl) ⟨2752749, by rfl⟩ : syracuseStep 7340665 = 5505499) B5505499
theorem B1884907 : Blo 1287962 1884907 := bstep (se 1 (by rfl) ⟨1413680, by rfl⟩ : syracuseStep 1884907 = 2827361) B2827361
theorem B22307633 : Blo 1287962 22307633 := bstep (se 2 (by rfl) ⟨8365362, by rfl⟩ : syracuseStep 22307633 = 16730725) B16730725
theorem B141148979 : Blo 1287962 141148979 := bstep (se 1 (by rfl) ⟨105861734, by rfl⟩ : syracuseStep 141148979 = 211723469) B211723469
theorem B4350887 : Blo 1287962 4350887 := bstep (se 1 (by rfl) ⟨3263165, by rfl⟩ : syracuseStep 4350887 = 6526331) B6526331
theorem B1934399 : Blo 1287962 1934399 := bstep (se 1 (by rfl) ⟨1450799, by rfl⟩ : syracuseStep 1934399 = 2901599) B2901599
theorem B1934441 : Blo 1287962 1934441 := bstep (se 2 (by rfl) ⟨725415, by rfl⟩ : syracuseStep 1934441 = 1450831) B1450831
theorem B3261647 : Blo 1287962 3261647 := bstep (se 1 (by rfl) ⟨2446235, by rfl⟩ : syracuseStep 3261647 = 4892471) B4892471
theorem B1934543 : Blo 1287962 1934543 := bstep (se 1 (by rfl) ⟨1450907, by rfl⟩ : syracuseStep 1934543 = 2901815) B2901815
theorem B2065819 : Blo 1287962 2065819 := bstep (se 1 (by rfl) ⟨1549364, by rfl⟩ : syracuseStep 2065819 = 3098729) B3098729
theorem B1934747 : Blo 1287962 1934747 := bstep (se 1 (by rfl) ⟨1451060, by rfl⟩ : syracuseStep 1934747 = 2902121) B2902121
theorem B2901419 : Blo 1287962 2901419 := bstep (se 1 (by rfl) ⟨2176064, by rfl⟩ : syracuseStep 2901419 = 4352129) B4352129
theorem B4351481 : Blo 1287962 4351481 := bstep (se 2 (by rfl) ⟨1631805, by rfl⟩ : syracuseStep 4351481 = 3263611) B3263611
theorem B3261971 : Blo 1287962 3261971 := bstep (se 1 (by rfl) ⟨2446478, by rfl⟩ : syracuseStep 3261971 = 4892957) B4892957
theorem B3483257 : Blo 1287962 3483257 := bstep (se 2 (by rfl) ⟨1306221, by rfl⟩ : syracuseStep 3483257 = 2612443) B2612443
theorem B4646521 : Blo 1287962 4646521 := bstep (se 2 (by rfl) ⟨1742445, by rfl⟩ : syracuseStep 4646521 = 3484891) B3484891
theorem B2901671 : Blo 1287962 2901671 := bstep (se 1 (by rfl) ⟨2176253, by rfl⟩ : syracuseStep 2901671 = 4352507) B4352507
theorem B4351751 : Blo 1287962 4351751 := bstep (se 1 (by rfl) ⟨3263813, by rfl⟩ : syracuseStep 4351751 = 6527627) B6527627
theorem B1287967 : Blo 1287962 1287967 := bstep (se 1 (by rfl) ⟨965975, by rfl⟩ : syracuseStep 1287967 = 1931951) B1931951
theorem B4351805 : Blo 1287962 4351805 := bstep (se 3 (by rfl) ⟨815963, by rfl⟩ : syracuseStep 4351805 = 1631927) B1631927
theorem B1287999 : Blo 1287962 1287999 := bstep (se 1 (by rfl) ⟨965999, by rfl⟩ : syracuseStep 1287999 = 1931999) B1931999
theorem B4646753 : Blo 1287962 4646753 := bstep (se 2 (by rfl) ⟨1742532, by rfl⟩ : syracuseStep 4646753 = 3485065) B3485065
theorem B3671905 : Blo 1287962 3671905 := bstep (se 2 (by rfl) ⟨1376964, by rfl⟩ : syracuseStep 3671905 = 2753929) B2753929
theorem B4130689 : Blo 1287962 4130689 := bstep (se 2 (by rfl) ⟨1549008, by rfl⟩ : syracuseStep 4130689 = 3098017) B3098017
theorem B12388261 : Blo 1287962 12388261 := bstep (se 4 (by rfl) ⟨1161399, by rfl⟩ : syracuseStep 12388261 = 2322799) B2322799
theorem B2901959 : Blo 1287962 2901959 := bstep (se 1 (by rfl) ⟨2176469, by rfl⟩ : syracuseStep 2901959 = 4352939) B4352939
theorem B1288175 : Blo 1287962 1288175 := bstep (se 1 (by rfl) ⟨966131, by rfl⟩ : syracuseStep 1288175 = 1932263) B1932263
theorem B1288347 : Blo 1287962 1288347 := bstep (se 1 (by rfl) ⟨966260, by rfl⟩ : syracuseStep 1288347 = 1932521) B1932521
theorem B1288383 : Blo 1287962 1288383 := bstep (se 1 (by rfl) ⟨966287, by rfl⟩ : syracuseStep 1288383 = 1932575) B1932575
theorem B6965459 : Blo 1287962 6965459 := bstep (se 1 (by rfl) ⟨5224094, by rfl⟩ : syracuseStep 6965459 = 10448189) B10448189
theorem B6523091 : Blo 1287962 6523091 := bstep (se 1 (by rfl) ⟨4892318, by rfl⟩ : syracuseStep 6523091 = 9784637) B9784637
theorem B7440619 : Blo 1287962 7440619 := bstep (se 1 (by rfl) ⟨5580464, by rfl⟩ : syracuseStep 7440619 = 11160929) B11160929
theorem B2902265 : Blo 1287962 2902265 := bstep (se 2 (by rfl) ⟨1088349, by rfl⟩ : syracuseStep 2902265 = 2176699) B2176699
theorem B1288495 : Blo 1287962 1288495 := bstep (se 1 (by rfl) ⟨966371, by rfl⟩ : syracuseStep 1288495 = 1932743) B1932743
theorem B2902319 : Blo 1287962 2902319 := bstep (se 1 (by rfl) ⟨2176739, by rfl⟩ : syracuseStep 2902319 = 4353479) B4353479
theorem B4188577 : Blo 1287962 4188577 := bstep (se 2 (by rfl) ⟨1570716, by rfl⟩ : syracuseStep 4188577 = 3141433) B3141433
theorem B1288731 : Blo 1287962 1288731 := bstep (se 1 (by rfl) ⟨966548, by rfl⟩ : syracuseStep 1288731 = 1933097) B1933097
theorem B1288735 : Blo 1287962 1288735 := bstep (se 1 (by rfl) ⟨966551, by rfl⟩ : syracuseStep 1288735 = 1933103) B1933103
theorem B122235455 : Blo 1287962 122235455 := bstep (se 1 (by rfl) ⟨91676591, by rfl⟩ : syracuseStep 122235455 = 183353183) B183353183
theorem B2321207 : Blo 1287962 2321207 := bstep (se 1 (by rfl) ⟨1740905, by rfl⟩ : syracuseStep 2321207 = 3481811) B3481811
theorem B3263287 : Blo 1287962 3263287 := bstep (se 1 (by rfl) ⟨2447465, by rfl⟩ : syracuseStep 3263287 = 4894931) B4894931
theorem B1289051 : Blo 1287962 1289051 := bstep (se 1 (by rfl) ⟨966788, by rfl⟩ : syracuseStep 1289051 = 1933577) B1933577
theorem B1289119 : Blo 1287962 1289119 := bstep (se 1 (by rfl) ⟨966839, by rfl⟩ : syracuseStep 1289119 = 1933679) B1933679
theorem B20917187 : Blo 1287962 20917187 := bstep (se 1 (by rfl) ⟨15687890, by rfl⟩ : syracuseStep 20917187 = 31375781) B31375781
theorem B2173999 : Blo 1287962 2173999 := bstep (se 1 (by rfl) ⟨1630499, by rfl⟩ : syracuseStep 2173999 = 3260999) B3260999
theorem B1289263 : Blo 1287962 1289263 := bstep (se 1 (by rfl) ⟨966947, by rfl⟩ : syracuseStep 1289263 = 1933895) B1933895
theorem B1289287 : Blo 1287962 1289287 := bstep (se 1 (by rfl) ⟨966965, by rfl⟩ : syracuseStep 1289287 = 1933931) B1933931
theorem B4648033 : Blo 1287962 4648033 := bstep (se 2 (by rfl) ⟨1743012, by rfl⟩ : syracuseStep 4648033 = 3486025) B3486025
theorem B1289439 : Blo 1287962 1289439 := bstep (se 1 (by rfl) ⟨967079, by rfl⟩ : syracuseStep 1289439 = 1934159) B1934159
theorem B4893929 : Blo 1287962 4893929 := bstep (se 2 (by rfl) ⟨1835223, by rfl⟩ : syracuseStep 4893929 = 3670447) B3670447
theorem B5229947 : Blo 1287962 5229947 := bstep (se 1 (by rfl) ⟨3922460, by rfl⟩ : syracuseStep 5229947 = 7844921) B7844921
theorem B2174377 : Blo 1287962 2174377 := bstep (se 2 (by rfl) ⟨815391, by rfl⟩ : syracuseStep 2174377 = 1630783) B1630783
theorem B1289703 : Blo 1287962 1289703 := bstep (se 1 (by rfl) ⟨967277, by rfl⟩ : syracuseStep 1289703 = 1934555) B1934555
theorem B3141193 : Blo 1287962 3141193 := bstep (se 2 (by rfl) ⟨1177947, by rfl⟩ : syracuseStep 3141193 = 2355895) B2355895
theorem B1289819 : Blo 1287962 1289819 := bstep (se 1 (by rfl) ⟨967364, by rfl⟩ : syracuseStep 1289819 = 1934729) B1934729
theorem B94015235 : Blo 1287962 94015235 := bstep (se 1 (by rfl) ⟨70511426, by rfl⟩ : syracuseStep 94015235 = 141022853) B141022853
theorem B6524711 : Blo 1287962 6524711 := bstep (se 1 (by rfl) ⟨4893533, by rfl⟩ : syracuseStep 6524711 = 9787067) B9787067
theorem B5508985 : Blo 1287962 5508985 := bstep (se 2 (by rfl) ⟨2065869, by rfl⟩ : syracuseStep 5508985 = 4131739) B4131739
theorem B2174843 : Blo 1287962 2174843 := bstep (se 1 (by rfl) ⟨1631132, by rfl⟩ : syracuseStep 2174843 = 3262265) B3262265
theorem B7835629 : Blo 1287962 7835629 := bstep (se 3 (by rfl) ⟨1469180, by rfl⟩ : syracuseStep 7835629 = 2938361) B2938361
theorem B4895113 : Blo 1287962 4895113 := bstep (se 2 (by rfl) ⟨1835667, by rfl⟩ : syracuseStep 4895113 = 3671335) B3671335
theorem B17641871 : Blo 1287962 17641871 := bstep (se 1 (by rfl) ⟨13231403, by rfl⟩ : syracuseStep 17641871 = 26462807) B26462807
theorem B14889491 : Blo 1287962 14889491 := bstep (se 1 (by rfl) ⟨11167118, by rfl⟩ : syracuseStep 14889491 = 22334237) B22334237
theorem B52900523 : Blo 1287962 52900523 := bstep (se 1 (by rfl) ⟨39675392, by rfl⟩ : syracuseStep 52900523 = 79350785) B79350785
theorem B9294659 : Blo 1287962 9294659 := bstep (se 1 (by rfl) ⟨6970994, by rfl⟩ : syracuseStep 9294659 = 13941989) B13941989
theorem B1766395 : Blo 1287962 1766395 := bstep (se 1 (by rfl) ⟨1324796, by rfl⟩ : syracuseStep 1766395 = 2649593) B2649593
theorem B9294887 : Blo 1287962 9294887 := bstep (se 1 (by rfl) ⟨6971165, by rfl⟩ : syracuseStep 9294887 = 13942331) B13942331
theorem B6526007 : Blo 1287962 6526007 := bstep (se 1 (by rfl) ⟨4894505, by rfl⟩ : syracuseStep 6526007 = 9789011) B9789011
theorem B2176105 : Blo 1287962 2176105 := bstep (se 2 (by rfl) ⟨816039, by rfl⟩ : syracuseStep 2176105 = 1632079) B1632079
theorem B3486827 : Blo 1287962 3486827 := bstep (se 1 (by rfl) ⟨2615120, by rfl⟩ : syracuseStep 3486827 = 5230241) B5230241
theorem B4347323 : Blo 1287962 4347323 := bstep (se 1 (by rfl) ⟨3260492, by rfl⟩ : syracuseStep 4347323 = 6520985) B6520985
theorem B2446919 : Blo 1287962 2446919 := bstep (se 1 (by rfl) ⟨1835189, by rfl⟩ : syracuseStep 2446919 = 3670379) B3670379
theorem B2176679 : Blo 1287962 2176679 := bstep (se 1 (by rfl) ⟨1632509, by rfl⟩ : syracuseStep 2176679 = 3265019) B3265019
theorem B4126459 : Blo 1287962 4126459 := bstep (se 1 (by rfl) ⟨3094844, by rfl⟩ : syracuseStep 4126459 = 6189689) B6189689
theorem B6190843 : Blo 1287962 6190843 := bstep (se 1 (by rfl) ⟨4643132, by rfl⟩ : syracuseStep 6190843 = 9286265) B9286265
theorem B2324219 : Blo 1287962 2324219 := bstep (se 1 (by rfl) ⟨1743164, by rfl⟩ : syracuseStep 2324219 = 3486329) B3486329
theorem B4642717 : Blo 1287962 4642717 := bstep (se 3 (by rfl) ⟨870509, by rfl⟩ : syracuseStep 4642717 = 1741019) B1741019
theorem B15685559 : Blo 1287962 15685559 := bstep (se 1 (by rfl) ⟨11764169, by rfl⟩ : syracuseStep 15685559 = 23528339) B23528339
theorem B4347863 : Blo 1287962 4347863 := bstep (se 1 (by rfl) ⟨3260897, by rfl⟩ : syracuseStep 4347863 = 6521795) B6521795
theorem B2791519 : Blo 1287962 2791519 := bstep (se 1 (by rfl) ⟨2093639, by rfl⟩ : syracuseStep 2791519 = 4187279) B4187279
theorem B2898017 : Blo 1287962 2898017 := bstep (se 2 (by rfl) ⟨1086756, by rfl⟩ : syracuseStep 2898017 = 2173513) B2173513
theorem B4348349 : Blo 1287962 4348349 := bstep (se 3 (by rfl) ⟨815315, by rfl⟩ : syracuseStep 4348349 = 1630631) B1630631
theorem B50207165 : Blo 1287962 50207165 := bstep (se 3 (by rfl) ⟨9413843, by rfl⟩ : syracuseStep 50207165 = 18827687) B18827687
theorem B4774457 : Blo 1287962 4774457 := bstep (se 2 (by rfl) ⟨1790421, by rfl⟩ : syracuseStep 4774457 = 3580843) B3580843
theorem B15670097 : Blo 1287962 15670097 := bstep (se 2 (by rfl) ⟨5876286, by rfl⟩ : syracuseStep 15670097 = 11752573) B11752573
theorem B1932191 : Blo 1287962 1932191 := bstep (se 1 (by rfl) ⟨1449143, by rfl⟩ : syracuseStep 1932191 = 2898287) B2898287
theorem B55098299 : Blo 1287962 55098299 := bstep (se 1 (by rfl) ⟨41323724, by rfl⟩ : syracuseStep 55098299 = 82647449) B82647449
theorem B4127689 : Blo 1287962 4127689 := bstep (se 2 (by rfl) ⟨1547883, by rfl⟩ : syracuseStep 4127689 = 3095767) B3095767
theorem B1932239 : Blo 1287962 1932239 := bstep (se 1 (by rfl) ⟨1449179, by rfl⟩ : syracuseStep 1932239 = 2898359) B2898359
theorem B122305549 : Blo 1287962 122305549 := bstep (se 3 (by rfl) ⟨22932290, by rfl⟩ : syracuseStep 122305549 = 45864581) B45864581
theorem B1932329 : Blo 1287962 1932329 := bstep (se 2 (by rfl) ⟨724623, by rfl⟩ : syracuseStep 1932329 = 1449247) B1449247
theorem B1932335 : Blo 1287962 1932335 := bstep (se 1 (by rfl) ⟨1449251, by rfl⟩ : syracuseStep 1932335 = 2898503) B2898503
theorem B1449031 : Blo 1287962 1449031 := bstep (se 1 (by rfl) ⟨1086773, by rfl⟩ : syracuseStep 1449031 = 2173547) B2173547
theorem B1932359 : Blo 1287962 1932359 := bstep (se 1 (by rfl) ⟨1449269, by rfl⟩ : syracuseStep 1932359 = 2898539) B2898539
theorem B6970493 : Blo 1287962 6970493 := bstep (se 3 (by rfl) ⟨1306967, by rfl⟩ : syracuseStep 6970493 = 2613935) B2613935
theorem B10460285 : Blo 1287962 10460285 := bstep (se 3 (by rfl) ⟨1961303, by rfl⟩ : syracuseStep 10460285 = 3922607) B3922607
theorem B4349213 : Blo 1287962 4349213 := bstep (se 3 (by rfl) ⟨815477, by rfl⟩ : syracuseStep 4349213 = 1630955) B1630955
theorem B1932623 : Blo 1287962 1932623 := bstep (se 1 (by rfl) ⟨1449467, by rfl⟩ : syracuseStep 1932623 = 2898935) B2898935
theorem B2899367 : Blo 1287962 2899367 := bstep (se 1 (by rfl) ⟨2174525, by rfl⟩ : syracuseStep 2899367 = 4349051) B4349051
theorem B1932713 : Blo 1287962 1932713 := bstep (se 2 (by rfl) ⟨724767, by rfl⟩ : syracuseStep 1932713 = 1449535) B1449535
theorem B47037995 : Blo 1287962 47037995 := bstep (se 1 (by rfl) ⟨35278496, by rfl⟩ : syracuseStep 47037995 = 70556993) B70556993
theorem B26459693 : Blo 1287962 26459693 := bstep (se 3 (by rfl) ⟨4961192, by rfl⟩ : syracuseStep 26459693 = 9922385) B9922385
theorem B1932863 : Blo 1287962 1932863 := bstep (se 1 (by rfl) ⟨1449647, by rfl⟩ : syracuseStep 1932863 = 2899295) B2899295
theorem B3718747 : Blo 1287962 3718747 := bstep (se 1 (by rfl) ⟨2789060, by rfl⟩ : syracuseStep 3718747 = 5578121) B5578121
theorem B2899547 : Blo 1287962 2899547 := bstep (se 1 (by rfl) ⟨2174660, by rfl⟩ : syracuseStep 2899547 = 4349321) B4349321
theorem B14687891 : Blo 1287962 14687891 := bstep (se 1 (by rfl) ⟨11015918, by rfl⟩ : syracuseStep 14687891 = 22031837) B22031837
theorem B1933127 : Blo 1287962 1933127 := bstep (se 1 (by rfl) ⟨1449845, by rfl⟩ : syracuseStep 1933127 = 2899691) B2899691
theorem B4964183 : Blo 1287962 4964183 := bstep (se 1 (by rfl) ⟨3723137, by rfl⟩ : syracuseStep 4964183 = 7446275) B7446275
theorem B2899835 : Blo 1287962 2899835 := bstep (se 1 (by rfl) ⟨2174876, by rfl⟩ : syracuseStep 2899835 = 4349753) B4349753
theorem B24764291 : Blo 1287962 24764291 := bstep (se 1 (by rfl) ⟨18573218, by rfl⟩ : syracuseStep 24764291 = 37146437) B37146437
theorem B1933211 : Blo 1287962 1933211 := bstep (se 1 (by rfl) ⟨1449908, by rfl⟩ : syracuseStep 1933211 = 2899817) B2899817
theorem B4890557 : Blo 1287962 4890557 := bstep (se 3 (by rfl) ⟨916979, by rfl⟩ : syracuseStep 4890557 = 1833959) B1833959
theorem B2752699 : Blo 1287962 2752699 := bstep (se 1 (by rfl) ⟨2064524, by rfl⟩ : syracuseStep 2752699 = 4129049) B4129049
theorem B3096767 : Blo 1287962 3096767 := bstep (se 1 (by rfl) ⟨2322575, by rfl⟩ : syracuseStep 3096767 = 4645151) B4645151
theorem B2900159 : Blo 1287962 2900159 := bstep (se 1 (by rfl) ⟨2175119, by rfl⟩ : syracuseStep 2900159 = 4350239) B4350239
theorem B1933547 : Blo 1287962 1933547 := bstep (se 1 (by rfl) ⟨1450160, by rfl⟩ : syracuseStep 1933547 = 2900321) B2900321
theorem B1835303 : Blo 1287962 1835303 := bstep (se 1 (by rfl) ⟨1376477, by rfl⟩ : syracuseStep 1835303 = 2752955) B2752955
theorem B1933607 : Blo 1287962 1933607 := bstep (se 1 (by rfl) ⟨1450205, by rfl⟩ : syracuseStep 1933607 = 2900411) B2900411
theorem B9920825 : Blo 1287962 9920825 := bstep (se 2 (by rfl) ⟨3720309, by rfl⟩ : syracuseStep 9920825 = 7440619) B7440619
theorem B18587981 : Blo 1287962 18587981 := bstep (se 3 (by rfl) ⟨3485246, by rfl⟩ : syracuseStep 18587981 = 6970493) B6970493
theorem B3096959 : Blo 1287962 3096959 := bstep (se 1 (by rfl) ⟨2322719, by rfl⟩ : syracuseStep 3096959 = 4645439) B4645439
theorem B35267015 : Blo 1287962 35267015 := bstep (se 1 (by rfl) ⟨26450261, by rfl⟩ : syracuseStep 35267015 = 52900523) B52900523
theorem B24789509 : Blo 1287962 24789509 := bstep (se 4 (by rfl) ⟨2324016, by rfl⟩ : syracuseStep 24789509 = 4648033) B4648033
theorem B2900591 : Blo 1287962 2900591 := bstep (se 1 (by rfl) ⟨2175443, by rfl⟩ : syracuseStep 2900591 = 4350887) B4350887
theorem B4350671 : Blo 1287962 4350671 := bstep (se 1 (by rfl) ⟨3263003, by rfl⟩ : syracuseStep 4350671 = 6526007) B6526007
theorem B1934279 : Blo 1287962 1934279 := bstep (se 1 (by rfl) ⟨1450709, by rfl⟩ : syracuseStep 1934279 = 2901419) B2901419
theorem B2900987 : Blo 1287962 2900987 := bstep (se 1 (by rfl) ⟨2175740, by rfl⟩ : syracuseStep 2900987 = 4351481) B4351481
theorem B1631279 : Blo 1287962 1631279 := bstep (se 1 (by rfl) ⟨1223459, by rfl⟩ : syracuseStep 1631279 = 2446919) B2446919
theorem B4351049 : Blo 1287962 4351049 := bstep (se 2 (by rfl) ⟨1631643, by rfl⟩ : syracuseStep 4351049 = 3263287) B3263287
theorem B1934447 : Blo 1287962 1934447 := bstep (se 1 (by rfl) ⟨1450835, by rfl⟩ : syracuseStep 1934447 = 2901671) B2901671
theorem B1451119 : Blo 1287962 1451119 := bstep (se 1 (by rfl) ⟨1088339, by rfl⟩ : syracuseStep 1451119 = 2176679) B2176679
theorem B2901167 : Blo 1287962 2901167 := bstep (se 1 (by rfl) ⟨2175875, by rfl⟩ : syracuseStep 2901167 = 4351751) B4351751
theorem B2901203 : Blo 1287962 2901203 := bstep (se 1 (by rfl) ⟨2175902, by rfl⟩ : syracuseStep 2901203 = 4351805) B4351805
theorem B3097835 : Blo 1287962 3097835 := bstep (se 1 (by rfl) ⟨2323376, by rfl⟩ : syracuseStep 3097835 = 4646753) B4646753
theorem B1934639 : Blo 1287962 1934639 := bstep (se 1 (by rfl) ⟨1450979, by rfl⟩ : syracuseStep 1934639 = 2901959) B2901959
theorem B2901473 : Blo 1287962 2901473 := bstep (se 2 (by rfl) ⟨1088052, by rfl⟩ : syracuseStep 2901473 = 2176105) B2176105
theorem B1934843 : Blo 1287962 1934843 := bstep (se 1 (by rfl) ⟨1451132, by rfl⟩ : syracuseStep 1934843 = 2902265) B2902265
theorem B1934879 : Blo 1287962 1934879 := bstep (se 1 (by rfl) ⟨1451159, by rfl⟩ : syracuseStep 1934879 = 2902319) B2902319
theorem B2754425 : Blo 1287962 2754425 := bstep (se 2 (by rfl) ⟨1032909, by rfl⟩ : syracuseStep 2754425 = 2065819) B2065819
theorem B10446731 : Blo 1287962 10446731 := bstep (se 1 (by rfl) ⟨7835048, by rfl⟩ : syracuseStep 10446731 = 15670097) B15670097
theorem B1288127 : Blo 1287962 1288127 := bstep (se 1 (by rfl) ⟨966095, by rfl⟩ : syracuseStep 1288127 = 1932191) B1932191
theorem B13944791 : Blo 1287962 13944791 := bstep (se 1 (by rfl) ⟨10458593, by rfl⟩ : syracuseStep 13944791 = 20917187) B20917187
theorem B1288159 : Blo 1287962 1288159 := bstep (se 1 (by rfl) ⟨966119, by rfl⟩ : syracuseStep 1288159 = 1932239) B1932239
theorem B1288219 : Blo 1287962 1288219 := bstep (se 1 (by rfl) ⟨966164, by rfl⟩ : syracuseStep 1288219 = 1932329) B1932329
theorem B1288223 : Blo 1287962 1288223 := bstep (se 1 (by rfl) ⟨966167, by rfl⟩ : syracuseStep 1288223 = 1932335) B1932335
theorem B1288239 : Blo 1287962 1288239 := bstep (se 1 (by rfl) ⟨966179, by rfl⟩ : syracuseStep 1288239 = 1932359) B1932359
theorem B6973523 : Blo 1287962 6973523 := bstep (se 1 (by rfl) ⟨5230142, by rfl⟩ : syracuseStep 6973523 = 10460285) B10460285
theorem B4188257 : Blo 1287962 4188257 := bstep (se 2 (by rfl) ⟨1570596, by rfl⟩ : syracuseStep 4188257 = 3141193) B3141193
theorem B4958329 : Blo 1287962 4958329 := bstep (se 2 (by rfl) ⟨1859373, by rfl⟩ : syracuseStep 4958329 = 3718747) B3718747
theorem B3262619 : Blo 1287962 3262619 := bstep (se 1 (by rfl) ⟨2446964, by rfl⟩ : syracuseStep 3262619 = 4893929) B4893929
theorem B6195361 : Blo 1287962 6195361 := bstep (se 2 (by rfl) ⟨2323260, by rfl⟩ : syracuseStep 6195361 = 4646521) B4646521
theorem B1288415 : Blo 1287962 1288415 := bstep (se 1 (by rfl) ⟨966311, by rfl⟩ : syracuseStep 1288415 = 1932623) B1932623
theorem B1288475 : Blo 1287962 1288475 := bstep (se 1 (by rfl) ⟨966356, by rfl⟩ : syracuseStep 1288475 = 1932713) B1932713
theorem B17639795 : Blo 1287962 17639795 := bstep (se 1 (by rfl) ⟨13229846, by rfl⟩ : syracuseStep 17639795 = 26459693) B26459693
theorem B1288575 : Blo 1287962 1288575 := bstep (se 1 (by rfl) ⟨966431, by rfl⟩ : syracuseStep 1288575 = 1932863) B1932863
theorem B22014341 : Blo 1287962 22014341 := bstep (se 4 (by rfl) ⟨2063844, by rfl⟩ : syracuseStep 22014341 = 4127689) B4127689
theorem B9791927 : Blo 1287962 9791927 := bstep (se 1 (by rfl) ⟨7343945, by rfl⟩ : syracuseStep 9791927 = 14687891) B14687891
theorem B5507585 : Blo 1287962 5507585 := bstep (se 2 (by rfl) ⟨2065344, by rfl⟩ : syracuseStep 5507585 = 4130689) B4130689
theorem B1288751 : Blo 1287962 1288751 := bstep (se 1 (by rfl) ⟨966563, by rfl⟩ : syracuseStep 1288751 = 1933127) B1933127
theorem B16517681 : Blo 1287962 16517681 := bstep (se 2 (by rfl) ⟨6194130, by rfl⟩ : syracuseStep 16517681 = 12388261) B12388261
theorem B16509527 : Blo 1287962 16509527 := bstep (se 1 (by rfl) ⟨12382145, by rfl⟩ : syracuseStep 16509527 = 24764291) B24764291
theorem B1288807 : Blo 1287962 1288807 := bstep (se 1 (by rfl) ⟨966605, by rfl⟩ : syracuseStep 1288807 = 1933211) B1933211
theorem B10447505 : Blo 1287962 10447505 := bstep (se 2 (by rfl) ⟨3917814, by rfl⟩ : syracuseStep 10447505 = 7835629) B7835629
theorem B1289183 : Blo 1287962 1289183 := bstep (se 1 (by rfl) ⟨966887, by rfl⟩ : syracuseStep 1289183 = 1933775) B1933775
theorem B1289211 : Blo 1287962 1289211 := bstep (se 1 (by rfl) ⟨966908, by rfl⟩ : syracuseStep 1289211 = 1933817) B1933817
theorem B1289279 : Blo 1287962 1289279 := bstep (se 1 (by rfl) ⟨966959, by rfl⟩ : syracuseStep 1289279 = 1933919) B1933919
theorem B14871755 : Blo 1287962 14871755 := bstep (se 1 (by rfl) ⟨11153816, by rfl⟩ : syracuseStep 14871755 = 22307633) B22307633
theorem B6196439 : Blo 1287962 6196439 := bstep (se 1 (by rfl) ⟨4647329, by rfl⟩ : syracuseStep 6196439 = 9294659) B9294659
theorem B6196591 : Blo 1287962 6196591 := bstep (se 1 (by rfl) ⟨4647443, by rfl⟩ : syracuseStep 6196591 = 9294887) B9294887
theorem B1289599 : Blo 1287962 1289599 := bstep (se 1 (by rfl) ⟨967199, by rfl⟩ : syracuseStep 1289599 = 1934399) B1934399
theorem B1289627 : Blo 1287962 1289627 := bstep (se 1 (by rfl) ⟨967220, by rfl⟩ : syracuseStep 1289627 = 1934441) B1934441
theorem B2174431 : Blo 1287962 2174431 := bstep (se 1 (by rfl) ⟨1630823, by rfl⟩ : syracuseStep 2174431 = 3261647) B3261647
theorem B1289695 : Blo 1287962 1289695 := bstep (se 1 (by rfl) ⟨967271, by rfl⟩ : syracuseStep 1289695 = 1934543) B1934543
theorem B1289831 : Blo 1287962 1289831 := bstep (se 1 (by rfl) ⟨967373, by rfl⟩ : syracuseStep 1289831 = 1934747) B1934747
theorem B2174647 : Blo 1287962 2174647 := bstep (se 1 (by rfl) ⟨1630985, by rfl⟩ : syracuseStep 2174647 = 3261971) B3261971
theorem B10457039 : Blo 1287962 10457039 := bstep (se 1 (by rfl) ⟨7842779, by rfl⟩ : syracuseStep 10457039 = 15685559) B15685559
theorem B2355193 : Blo 1287962 2355193 := bstep (se 2 (by rfl) ⟨883197, by rfl⟩ : syracuseStep 2355193 = 1766395) B1766395
theorem B163074065 : Blo 1287962 163074065 := bstep (se 2 (by rfl) ⟨61152774, by rfl⟩ : syracuseStep 163074065 = 122305549) B122305549
theorem B3182971 : Blo 1287962 3182971 := bstep (se 1 (by rfl) ⟨2387228, by rfl⟩ : syracuseStep 3182971 = 4774457) B4774457
theorem B81490303 : Blo 1287962 81490303 := bstep (se 1 (by rfl) ⟨61117727, by rfl⟩ : syracuseStep 81490303 = 122235455) B122235455
theorem B59552405 : Blo 1287962 59552405 := bstep (se 6 (by rfl) ⟨1395759, by rfl⟩ : syracuseStep 59552405 = 2791519) B2791519
theorem B6197917 : Blo 1287962 6197917 := bstep (se 3 (by rfl) ⟨1162109, by rfl⟩ : syracuseStep 6197917 = 2324219) B2324219
theorem B3486631 : Blo 1287962 3486631 := bstep (se 1 (by rfl) ⟨2614973, by rfl⟩ : syracuseStep 3486631 = 5229947) B5229947
theorem B5501945 : Blo 1287962 5501945 := bstep (se 2 (by rfl) ⟨2063229, by rfl⟩ : syracuseStep 5501945 = 4126459) B4126459
theorem B8254457 : Blo 1287962 8254457 := bstep (se 2 (by rfl) ⟨3095421, by rfl⟩ : syracuseStep 8254457 = 6190843) B6190843
theorem B4895873 : Blo 1287962 4895873 := bstep (se 2 (by rfl) ⟨1835952, by rfl⟩ : syracuseStep 4895873 = 3671905) B3671905
theorem B7345313 : Blo 1287962 7345313 := bstep (se 2 (by rfl) ⟨2754492, by rfl⟩ : syracuseStep 7345313 = 5508985) B5508985
theorem B6190289 : Blo 1287962 6190289 := bstep (se 2 (by rfl) ⟨2321358, by rfl⟩ : syracuseStep 6190289 = 4642717) B4642717
theorem B11761247 : Blo 1287962 11761247 := bstep (se 1 (by rfl) ⟨8820935, by rfl⟩ : syracuseStep 11761247 = 17641871) B17641871
theorem B2447003 : Blo 1287962 2447003 := bstep (se 1 (by rfl) ⟨1835252, by rfl⟩ : syracuseStep 2447003 = 3670505) B3670505
theorem B9926327 : Blo 1287962 9926327 := bstep (se 1 (by rfl) ⟨7444745, by rfl⟩ : syracuseStep 9926327 = 14889491) B14889491
theorem B16733899 : Blo 1287962 16733899 := bstep (se 1 (by rfl) ⟨12550424, by rfl⟩ : syracuseStep 16733899 = 25100849) B25100849
theorem B6526817 : Blo 1287962 6526817 := bstep (se 2 (by rfl) ⟨2447556, by rfl⟩ : syracuseStep 6526817 = 4895113) B4895113
theorem B94099319 : Blo 1287962 94099319 := bstep (se 1 (by rfl) ⟨70574489, by rfl⟩ : syracuseStep 94099319 = 141148979) B141148979
theorem B5584769 : Blo 1287962 5584769 := bstep (se 2 (by rfl) ⟨2094288, by rfl⟩ : syracuseStep 5584769 = 4188577) B4188577
theorem B2447329 : Blo 1287962 2447329 := bstep (se 2 (by rfl) ⟨917748, by rfl⟩ : syracuseStep 2447329 = 1835497) B1835497
theorem B2324551 : Blo 1287962 2324551 := bstep (se 1 (by rfl) ⟨1743413, by rfl⟩ : syracuseStep 2324551 = 3486827) B3486827
theorem B9787553 : Blo 1287962 9787553 := bstep (se 2 (by rfl) ⟨3670332, by rfl⟩ : syracuseStep 9787553 = 7340665) B7340665
theorem B2898215 : Blo 1287962 2898215 := bstep (se 1 (by rfl) ⟨2173661, by rfl⟩ : syracuseStep 2898215 = 4347323) B4347323
theorem B2513209 : Blo 1287962 2513209 := bstep (se 2 (by rfl) ⟨942453, by rfl⟩ : syracuseStep 2513209 = 1884907) B1884907
theorem B2898575 : Blo 1287962 2898575 := bstep (se 1 (by rfl) ⟨2173931, by rfl⟩ : syracuseStep 2898575 = 4347863) B4347863
theorem B2898665 : Blo 1287962 2898665 := bstep (se 2 (by rfl) ⟨1086999, by rfl⟩ : syracuseStep 2898665 = 2173999) B2173999
theorem B1932011 : Blo 1287962 1932011 := bstep (se 1 (by rfl) ⟨1449008, by rfl⟩ : syracuseStep 1932011 = 2898017) B2898017
theorem B1932041 : Blo 1287962 1932041 := bstep (se 2 (by rfl) ⟨724515, by rfl⟩ : syracuseStep 1932041 = 1449031) B1449031
theorem B4643639 : Blo 1287962 4643639 := bstep (se 1 (by rfl) ⟨3482729, by rfl⟩ : syracuseStep 4643639 = 6965459) B6965459
theorem B4348727 : Blo 1287962 4348727 := bstep (se 1 (by rfl) ⟨3261545, by rfl⟩ : syracuseStep 4348727 = 6523091) B6523091
theorem B2898899 : Blo 1287962 2898899 := bstep (se 1 (by rfl) ⟨2174174, by rfl⟩ : syracuseStep 2898899 = 4348349) B4348349
theorem B33471443 : Blo 1287962 33471443 := bstep (se 1 (by rfl) ⟨25103582, by rfl⟩ : syracuseStep 33471443 = 50207165) B50207165
theorem B9288685 : Blo 1287962 9288685 := bstep (se 3 (by rfl) ⟨1741628, by rfl⟩ : syracuseStep 9288685 = 3483257) B3483257
theorem B1547471 : Blo 1287962 1547471 := bstep (se 1 (by rfl) ⟨1160603, by rfl⟩ : syracuseStep 1547471 = 2321207) B2321207
theorem B2899169 : Blo 1287962 2899169 := bstep (se 2 (by rfl) ⟨1087188, by rfl⟩ : syracuseStep 2899169 = 2174377) B2174377
theorem B36732199 : Blo 1287962 36732199 := bstep (se 1 (by rfl) ⟨27549149, by rfl⟩ : syracuseStep 36732199 = 55098299) B55098299
theorem B2899475 : Blo 1287962 2899475 := bstep (se 1 (by rfl) ⟨2174606, by rfl⟩ : syracuseStep 2899475 = 4349213) B4349213
theorem B1932911 : Blo 1287962 1932911 := bstep (se 1 (by rfl) ⟨1449683, by rfl⟩ : syracuseStep 1932911 = 2899367) B2899367
theorem B31358663 : Blo 1287962 31358663 := bstep (se 1 (by rfl) ⟨23518997, by rfl⟩ : syracuseStep 31358663 = 47037995) B47037995
theorem B1933031 : Blo 1287962 1933031 := bstep (se 1 (by rfl) ⟨1449773, by rfl⟩ : syracuseStep 1933031 = 2899547) B2899547
theorem B62676823 : Blo 1287962 62676823 := bstep (se 1 (by rfl) ⟨47007617, by rfl⟩ : syracuseStep 62676823 = 94015235) B94015235
theorem B4349807 : Blo 1287962 4349807 := bstep (se 1 (by rfl) ⟨3262355, by rfl⟩ : syracuseStep 4349807 = 6524711) B6524711
theorem B3309455 : Blo 1287962 3309455 := bstep (se 1 (by rfl) ⟨2482091, by rfl⟩ : syracuseStep 3309455 = 4964183) B4964183
theorem B1449895 : Blo 1287962 1449895 := bstep (se 1 (by rfl) ⟨1087421, by rfl⟩ : syracuseStep 1449895 = 2174843) B2174843
theorem B1933223 : Blo 1287962 1933223 := bstep (se 1 (by rfl) ⟨1449917, by rfl⟩ : syracuseStep 1933223 = 2899835) B2899835
theorem B3260371 : Blo 1287962 3260371 := bstep (se 1 (by rfl) ⟨2445278, by rfl⟩ : syracuseStep 3260371 = 4890557) B4890557
theorem B434864173 : Blo 1287962 434864173 := bstep (se 3 (by rfl) ⟨81537032, by rfl⟩ : syracuseStep 434864173 = 163074065) B163074065
theorem B4350077 : Blo 1287962 4350077 := bstep (se 3 (by rfl) ⟨815639, by rfl⟩ : syracuseStep 4350077 = 1631279) B1631279
theorem B2064511 : Blo 1287962 2064511 := bstep (se 1 (by rfl) ⟨1548383, by rfl⟩ : syracuseStep 2064511 = 3096767) B3096767
theorem B1933439 : Blo 1287962 1933439 := bstep (se 1 (by rfl) ⟨1450079, by rfl⟩ : syracuseStep 1933439 = 2900159) B2900159
theorem B6611105 : Blo 1287962 6611105 := bstep (se 2 (by rfl) ⟨2479164, by rfl⟩ : syracuseStep 6611105 = 4958329) B4958329
theorem B3670265 : Blo 1287962 3670265 := bstep (se 2 (by rfl) ⟨1376349, by rfl⟩ : syracuseStep 3670265 = 2752699) B2752699
theorem B23511343 : Blo 1287962 23511343 := bstep (se 1 (by rfl) ⟨17633507, by rfl⟩ : syracuseStep 23511343 = 35267015) B35267015
theorem B1933727 : Blo 1287962 1933727 := bstep (se 1 (by rfl) ⟨1450295, by rfl⟩ : syracuseStep 1933727 = 2900591) B2900591
theorem B3350945 : Blo 1287962 3350945 := bstep (se 2 (by rfl) ⟨1256604, by rfl⟩ : syracuseStep 3350945 = 2513209) B2513209
theorem B2900447 : Blo 1287962 2900447 := bstep (se 1 (by rfl) ⟨2175335, by rfl⟩ : syracuseStep 2900447 = 4350671) B4350671
theorem B4243961 : Blo 1287962 4243961 := bstep (se 2 (by rfl) ⟨1591485, by rfl⟩ : syracuseStep 4243961 = 3182971) B3182971
theorem B1933991 : Blo 1287962 1933991 := bstep (se 1 (by rfl) ⟨1450493, by rfl⟩ : syracuseStep 1933991 = 2900987) B2900987
theorem B2900699 : Blo 1287962 2900699 := bstep (se 1 (by rfl) ⟨2175524, by rfl⟩ : syracuseStep 2900699 = 4351049) B4351049
theorem B1934111 : Blo 1287962 1934111 := bstep (se 1 (by rfl) ⟨1450583, by rfl⟩ : syracuseStep 1934111 = 2901167) B2901167
theorem B1934135 : Blo 1287962 1934135 := bstep (se 1 (by rfl) ⟨1450601, by rfl⟩ : syracuseStep 1934135 = 2901203) B2901203
theorem B2065223 : Blo 1287962 2065223 := bstep (se 1 (by rfl) ⟨1548917, by rfl⟩ : syracuseStep 2065223 = 3097835) B3097835
theorem B47039453 : Blo 1287962 47039453 := bstep (se 3 (by rfl) ⟨8819897, by rfl⟩ : syracuseStep 47039453 = 17639795) B17639795
theorem B1934315 : Blo 1287962 1934315 := bstep (se 1 (by rfl) ⟨1450736, by rfl⟩ : syracuseStep 1934315 = 2901473) B2901473
theorem B8258557 : Blo 1287962 8258557 := bstep (se 3 (by rfl) ⟨1548479, by rfl⟩ : syracuseStep 8258557 = 3096959) B3096959
theorem B7840831 : Blo 1287962 7840831 := bstep (se 1 (by rfl) ⟨5880623, by rfl⟩ : syracuseStep 7840831 = 11761247) B11761247
theorem B1631335 : Blo 1287962 1631335 := bstep (se 1 (by rfl) ⟨1223501, by rfl⟩ : syracuseStep 1631335 = 2447003) B2447003
theorem B4351211 : Blo 1287962 4351211 := bstep (se 1 (by rfl) ⟨3263408, by rfl⟩ : syracuseStep 4351211 = 6526817) B6526817
theorem B1836283 : Blo 1287962 1836283 := bstep (se 1 (by rfl) ⟨1377212, by rfl⟩ : syracuseStep 1836283 = 2754425) B2754425
theorem B6964487 : Blo 1287962 6964487 := bstep (se 1 (by rfl) ⟨5223365, by rfl⟩ : syracuseStep 6964487 = 10446731) B10446731
theorem B1934825 : Blo 1287962 1934825 := bstep (se 2 (by rfl) ⟨725559, by rfl⟩ : syracuseStep 1934825 = 1451119) B1451119
theorem B3671723 : Blo 1287962 3671723 := bstep (se 1 (by rfl) ⟨2753792, by rfl⟩ : syracuseStep 3671723 = 5507585) B5507585
theorem B11011787 : Blo 1287962 11011787 := bstep (se 1 (by rfl) ⟨8258840, by rfl⟩ : syracuseStep 11011787 = 16517681) B16517681
theorem B6965003 : Blo 1287962 6965003 := bstep (se 1 (by rfl) ⟨5223752, by rfl⟩ : syracuseStep 6965003 = 10447505) B10447505
theorem B1288007 : Blo 1287962 1288007 := bstep (se 1 (by rfl) ⟨966005, by rfl⟩ : syracuseStep 1288007 = 1932011) B1932011
theorem B1288027 : Blo 1287962 1288027 := bstep (se 1 (by rfl) ⟨966020, by rfl⟩ : syracuseStep 1288027 = 1932041) B1932041
theorem B9914503 : Blo 1287962 9914503 := bstep (se 1 (by rfl) ⟨7435877, by rfl⟩ : syracuseStep 9914503 = 14871755) B14871755
theorem B4130959 : Blo 1287962 4130959 := bstep (se 1 (by rfl) ⟨3098219, by rfl⟩ : syracuseStep 4130959 = 6196439) B6196439
theorem B8825213 : Blo 1287962 8825213 := bstep (se 3 (by rfl) ⟨1654727, by rfl⟩ : syracuseStep 8825213 = 3309455) B3309455
theorem B1288607 : Blo 1287962 1288607 := bstep (se 1 (by rfl) ⟨966455, by rfl⟩ : syracuseStep 1288607 = 1932911) B1932911
theorem B83569097 : Blo 1287962 83569097 := bstep (se 2 (by rfl) ⟨31338411, by rfl⟩ : syracuseStep 83569097 = 62676823) B62676823
theorem B1288687 : Blo 1287962 1288687 := bstep (se 1 (by rfl) ⟨966515, by rfl⟩ : syracuseStep 1288687 = 1933031) B1933031
theorem B1288815 : Blo 1287962 1288815 := bstep (se 1 (by rfl) ⟨966611, by rfl⟩ : syracuseStep 1288815 = 1933223) B1933223
theorem B3263105 : Blo 1287962 3263105 := bstep (se 2 (by rfl) ⟨1223664, by rfl⟩ : syracuseStep 3263105 = 2447329) B2447329
theorem B3140257 : Blo 1287962 3140257 := bstep (se 2 (by rfl) ⟨1177596, by rfl⟩ : syracuseStep 3140257 = 2355193) B2355193
theorem B238283477 : Blo 1287962 238283477 := bstep (se 7 (by rfl) ⟨2792384, by rfl⟩ : syracuseStep 238283477 = 5584769) B5584769
theorem B3099401 : Blo 1287962 3099401 := bstep (se 2 (by rfl) ⟨1162275, by rfl⟩ : syracuseStep 3099401 = 2324551) B2324551
theorem B1289031 : Blo 1287962 1289031 := bstep (se 1 (by rfl) ⟨966773, by rfl⟩ : syracuseStep 1289031 = 1933547) B1933547
theorem B1289071 : Blo 1287962 1289071 := bstep (se 1 (by rfl) ⟨966803, by rfl⟩ : syracuseStep 1289071 = 1933607) B1933607
theorem B6613883 : Blo 1287962 6613883 := bstep (se 1 (by rfl) ⟨4960412, by rfl⟩ : syracuseStep 6613883 = 9920825) B9920825
theorem B8260481 : Blo 1287962 8260481 := bstep (se 2 (by rfl) ⟨3097680, by rfl⟩ : syracuseStep 8260481 = 6195361) B6195361
theorem B16526339 : Blo 1287962 16526339 := bstep (se 1 (by rfl) ⟨12394754, by rfl⟩ : syracuseStep 16526339 = 24789509) B24789509
theorem B39701603 : Blo 1287962 39701603 := bstep (se 1 (by rfl) ⟨29776202, by rfl⟩ : syracuseStep 39701603 = 59552405) B59552405
theorem B108653737 : Blo 1287962 108653737 := bstep (se 2 (by rfl) ⟨40745151, by rfl⟩ : syracuseStep 108653737 = 81490303) B81490303
theorem B1289519 : Blo 1287962 1289519 := bstep (se 1 (by rfl) ⟨967139, by rfl⟩ : syracuseStep 1289519 = 1934279) B1934279
theorem B1289631 : Blo 1287962 1289631 := bstep (se 1 (by rfl) ⟨967223, by rfl⟩ : syracuseStep 1289631 = 1934447) B1934447
theorem B3263915 : Blo 1287962 3263915 := bstep (se 1 (by rfl) ⟨2447936, by rfl⟩ : syracuseStep 3263915 = 4895873) B4895873
theorem B4894141 : Blo 1287962 4894141 := bstep (se 3 (by rfl) ⟨917651, by rfl⟩ : syracuseStep 4894141 = 1835303) B1835303
theorem B1289759 : Blo 1287962 1289759 := bstep (se 1 (by rfl) ⟨967319, by rfl⟩ : syracuseStep 1289759 = 1934639) B1934639
theorem B1289895 : Blo 1287962 1289895 := bstep (se 1 (by rfl) ⟨967421, by rfl⟩ : syracuseStep 1289895 = 1934843) B1934843
theorem B1289919 : Blo 1287962 1289919 := bstep (se 1 (by rfl) ⟨967439, by rfl⟩ : syracuseStep 1289919 = 1934879) B1934879
theorem B4648841 : Blo 1287962 4648841 := bstep (se 2 (by rfl) ⟨1743315, by rfl⟩ : syracuseStep 4648841 = 3486631) B3486631
theorem B4649015 : Blo 1287962 4649015 := bstep (se 1 (by rfl) ⟨3486761, by rfl⟩ : syracuseStep 4649015 = 6973523) B6973523
theorem B2175079 : Blo 1287962 2175079 := bstep (se 1 (by rfl) ⟨1631309, by rfl⟩ : syracuseStep 2175079 = 3262619) B3262619
theorem B6525035 : Blo 1287962 6525035 := bstep (se 1 (by rfl) ⟨4893776, by rfl⟩ : syracuseStep 6525035 = 9787553) B9787553
theorem B14676227 : Blo 1287962 14676227 := bstep (se 1 (by rfl) ⟨11007170, by rfl⟩ : syracuseStep 14676227 = 22014341) B22014341
theorem B48976265 : Blo 1287962 48976265 := bstep (se 2 (by rfl) ⟨18366099, by rfl⟩ : syracuseStep 48976265 = 36732199) B36732199
theorem B11006351 : Blo 1287962 11006351 := bstep (se 1 (by rfl) ⟨8254763, by rfl⟩ : syracuseStep 11006351 = 16509527) B16509527
theorem B8262121 : Blo 1287962 8262121 := bstep (se 2 (by rfl) ⟨3098295, by rfl⟩ : syracuseStep 8262121 = 6196591) B6196591
theorem B22311865 : Blo 1287962 22311865 := bstep (se 2 (by rfl) ⟨8366949, by rfl⟩ : syracuseStep 22311865 = 16733899) B16733899
theorem B4347161 : Blo 1287962 4347161 := bstep (se 2 (by rfl) ⟨1630185, by rfl⟩ : syracuseStep 4347161 = 3260371) B3260371
theorem B12391987 : Blo 1287962 12391987 := bstep (se 1 (by rfl) ⟨9293990, by rfl⟩ : syracuseStep 12391987 = 18587981) B18587981
theorem B4126589 : Blo 1287962 4126589 := bstep (se 3 (by rfl) ⟨773735, by rfl⟩ : syracuseStep 4126589 = 1547471) B1547471
theorem B5502971 : Blo 1287962 5502971 := bstep (se 1 (by rfl) ⟨4127228, by rfl⟩ : syracuseStep 5502971 = 8254457) B8254457
theorem B4896875 : Blo 1287962 4896875 := bstep (se 1 (by rfl) ⟨3672656, by rfl⟩ : syracuseStep 4896875 = 7345313) B7345313
theorem B4126859 : Blo 1287962 4126859 := bstep (se 1 (by rfl) ⟨3095144, by rfl⟩ : syracuseStep 4126859 = 6190289) B6190289
theorem B8263889 : Blo 1287962 8263889 := bstep (se 2 (by rfl) ⟨3098958, by rfl⟩ : syracuseStep 8263889 = 6197917) B6197917
theorem B6617551 : Blo 1287962 6617551 := bstep (se 1 (by rfl) ⟨4963163, by rfl⟩ : syracuseStep 6617551 = 9926327) B9926327
theorem B62732879 : Blo 1287962 62732879 := bstep (se 1 (by rfl) ⟨47049659, by rfl⟩ : syracuseStep 62732879 = 94099319) B94099319
theorem B9296527 : Blo 1287962 9296527 := bstep (se 1 (by rfl) ⟨6972395, by rfl⟩ : syracuseStep 9296527 = 13944791) B13944791
theorem B12384913 : Blo 1287962 12384913 := bstep (se 2 (by rfl) ⟨4644342, by rfl⟩ : syracuseStep 12384913 = 9288685) B9288685
theorem B2792171 : Blo 1287962 2792171 := bstep (se 1 (by rfl) ⟨2094128, by rfl⟩ : syracuseStep 2792171 = 4188257) B4188257
theorem B1932143 : Blo 1287962 1932143 := bstep (se 1 (by rfl) ⟨1449107, by rfl⟩ : syracuseStep 1932143 = 2898215) B2898215
theorem B6527951 : Blo 1287962 6527951 := bstep (se 1 (by rfl) ⟨4895963, by rfl⟩ : syracuseStep 6527951 = 9791927) B9791927
theorem B1932383 : Blo 1287962 1932383 := bstep (se 1 (by rfl) ⟨1449287, by rfl⟩ : syracuseStep 1932383 = 2898575) B2898575
theorem B1932443 : Blo 1287962 1932443 := bstep (se 1 (by rfl) ⟨1449332, by rfl⟩ : syracuseStep 1932443 = 2898665) B2898665
theorem B3095759 : Blo 1287962 3095759 := bstep (se 1 (by rfl) ⟨2321819, by rfl⟩ : syracuseStep 3095759 = 4643639) B4643639
theorem B2899151 : Blo 1287962 2899151 := bstep (se 1 (by rfl) ⟨2174363, by rfl⟩ : syracuseStep 2899151 = 4348727) B4348727
theorem B2899241 : Blo 1287962 2899241 := bstep (se 2 (by rfl) ⟨1087215, by rfl⟩ : syracuseStep 2899241 = 2174431) B2174431
theorem B1932599 : Blo 1287962 1932599 := bstep (se 1 (by rfl) ⟨1449449, by rfl⟩ : syracuseStep 1932599 = 2898899) B2898899
theorem B22314295 : Blo 1287962 22314295 := bstep (se 1 (by rfl) ⟨16735721, by rfl⟩ : syracuseStep 22314295 = 33471443) B33471443
theorem B1932779 : Blo 1287962 1932779 := bstep (se 1 (by rfl) ⟨1449584, by rfl⟩ : syracuseStep 1932779 = 2899169) B2899169
theorem B2899529 : Blo 1287962 2899529 := bstep (se 2 (by rfl) ⟨1087323, by rfl⟩ : syracuseStep 2899529 = 2174647) B2174647
theorem B1932983 : Blo 1287962 1932983 := bstep (se 1 (by rfl) ⟨1449737, by rfl⟩ : syracuseStep 1932983 = 2899475) B2899475
theorem B20905775 : Blo 1287962 20905775 := bstep (se 1 (by rfl) ⟨15679331, by rfl⟩ : syracuseStep 20905775 = 31358663) B31358663
theorem B1933193 : Blo 1287962 1933193 := bstep (se 2 (by rfl) ⟨724947, by rfl⟩ : syracuseStep 1933193 = 1449895) B1449895
theorem B2899871 : Blo 1287962 2899871 := bstep (se 1 (by rfl) ⟨2174903, by rfl⟩ : syracuseStep 2899871 = 4349807) B4349807
theorem B6971359 : Blo 1287962 6971359 := bstep (se 1 (by rfl) ⟨5228519, by rfl⟩ : syracuseStep 6971359 = 10457039) B10457039
theorem B14671853 : Blo 1287962 14671853 := bstep (se 3 (by rfl) ⟨2750972, by rfl⟩ : syracuseStep 14671853 = 5501945) B5501945
theorem B4350023 : Blo 1287962 4350023 := bstep (se 1 (by rfl) ⟨3262517, by rfl⟩ : syracuseStep 4350023 = 6525035) B6525035
theorem B2900051 : Blo 1287962 2900051 := bstep (se 1 (by rfl) ⟨2175038, by rfl⟩ : syracuseStep 2900051 = 4350077) B4350077
theorem B2900105 : Blo 1287962 2900105 := bstep (se 2 (by rfl) ⟨1087539, by rfl⟩ : syracuseStep 2900105 = 2175079) B2175079
theorem B1933631 : Blo 1287962 1933631 := bstep (se 1 (by rfl) ⟨1450223, by rfl⟩ : syracuseStep 1933631 = 2900447) B2900447
theorem B17629613 : Blo 1287962 17629613 := bstep (se 3 (by rfl) ⟨3305552, by rfl⟩ : syracuseStep 17629613 = 6611105) B6611105
theorem B1933799 : Blo 1287962 1933799 := bstep (se 1 (by rfl) ⟨1450349, by rfl⟩ : syracuseStep 1933799 = 2900699) B2900699
theorem B8823401 : Blo 1287962 8823401 := bstep (se 2 (by rfl) ⟨3308775, by rfl⟩ : syracuseStep 8823401 = 6617551) B6617551
theorem B31359635 : Blo 1287962 31359635 := bstep (se 1 (by rfl) ⟨23519726, by rfl⟩ : syracuseStep 31359635 = 47039453) B47039453
theorem B11010725 : Blo 1287962 11010725 := bstep (se 4 (by rfl) ⟨1032255, by rfl⟩ : syracuseStep 11010725 = 2064511) B2064511
theorem B2900807 : Blo 1287962 2900807 := bstep (se 1 (by rfl) ⟨2175605, by rfl⟩ : syracuseStep 2900807 = 4351211) B4351211
theorem B12395369 : Blo 1287962 12395369 := bstep (se 2 (by rfl) ⟨4648263, by rfl⟩ : syracuseStep 12395369 = 9296527) B9296527
theorem B4187009 : Blo 1287962 4187009 := bstep (se 2 (by rfl) ⟨1570128, by rfl⟩ : syracuseStep 4187009 = 3140257) B3140257
theorem B7341191 : Blo 1287962 7341191 := bstep (se 1 (by rfl) ⟨5505893, by rfl⟩ : syracuseStep 7341191 = 11011787) B11011787
theorem B11011409 : Blo 1287962 11011409 := bstep (se 2 (by rfl) ⟨4129278, by rfl⟩ : syracuseStep 11011409 = 8258557) B8258557
theorem B10454441 : Blo 1287962 10454441 := bstep (se 2 (by rfl) ⟨3920415, by rfl⟩ : syracuseStep 10454441 = 7840831) B7840831
theorem B5883475 : Blo 1287962 5883475 := bstep (se 1 (by rfl) ⟨4412606, by rfl⟩ : syracuseStep 5883475 = 8825213) B8825213
theorem B41821919 : Blo 1287962 41821919 := bstep (se 1 (by rfl) ⟨31366439, by rfl⟩ : syracuseStep 41821919 = 62732879) B62732879
theorem B2066267 : Blo 1287962 2066267 := bstep (se 1 (by rfl) ⟨1549700, by rfl⟩ : syracuseStep 2066267 = 3099401) B3099401
theorem B1288095 : Blo 1287962 1288095 := bstep (se 1 (by rfl) ⟨966071, by rfl⟩ : syracuseStep 1288095 = 1932143) B1932143
theorem B4409255 : Blo 1287962 4409255 := bstep (se 1 (by rfl) ⟨3306941, by rfl⟩ : syracuseStep 4409255 = 6613883) B6613883
theorem B5506987 : Blo 1287962 5506987 := bstep (se 1 (by rfl) ⟨4130240, by rfl⟩ : syracuseStep 5506987 = 8260481) B8260481
theorem B4351967 : Blo 1287962 4351967 := bstep (se 1 (by rfl) ⟨3263975, by rfl⟩ : syracuseStep 4351967 = 6527951) B6527951
theorem B1288255 : Blo 1287962 1288255 := bstep (se 1 (by rfl) ⟨966191, by rfl⟩ : syracuseStep 1288255 = 1932383) B1932383
theorem B1288295 : Blo 1287962 1288295 := bstep (se 1 (by rfl) ⟨966221, by rfl⟩ : syracuseStep 1288295 = 1932443) B1932443
theorem B5507261 : Blo 1287962 5507261 := bstep (se 3 (by rfl) ⟨1032611, by rfl⟩ : syracuseStep 5507261 = 2065223) B2065223
theorem B1288399 : Blo 1287962 1288399 := bstep (se 1 (by rfl) ⟨966299, by rfl⟩ : syracuseStep 1288399 = 1932599) B1932599
theorem B1288519 : Blo 1287962 1288519 := bstep (se 1 (by rfl) ⟨966389, by rfl⟩ : syracuseStep 1288519 = 1932779) B1932779
theorem B1288655 : Blo 1287962 1288655 := bstep (se 1 (by rfl) ⟨966491, by rfl⟩ : syracuseStep 1288655 = 1932983) B1932983
theorem B13937183 : Blo 1287962 13937183 := bstep (se 1 (by rfl) ⟨10452887, by rfl⟩ : syracuseStep 13937183 = 20905775) B20905775
theorem B1288795 : Blo 1287962 1288795 := bstep (se 1 (by rfl) ⟨966596, by rfl⟩ : syracuseStep 1288795 = 1933193) B1933193
theorem B3099227 : Blo 1287962 3099227 := bstep (se 1 (by rfl) ⟨2324420, by rfl⟩ : syracuseStep 3099227 = 4648841) B4648841
theorem B1288959 : Blo 1287962 1288959 := bstep (se 1 (by rfl) ⟨966719, by rfl⟩ : syracuseStep 1288959 = 1933439) B1933439
theorem B12397373 : Blo 1287962 12397373 := bstep (se 3 (by rfl) ⟨2324507, by rfl⟩ : syracuseStep 12397373 = 4649015) B4649015
theorem B9784151 : Blo 1287962 9784151 := bstep (se 1 (by rfl) ⟨7338113, by rfl⟩ : syracuseStep 9784151 = 14676227) B14676227
theorem B5507945 : Blo 1287962 5507945 := bstep (se 2 (by rfl) ⟨2065479, by rfl⟩ : syracuseStep 5507945 = 4130959) B4130959
theorem B1289151 : Blo 1287962 1289151 := bstep (se 1 (by rfl) ⟨966863, by rfl⟩ : syracuseStep 1289151 = 1933727) B1933727
theorem B1289327 : Blo 1287962 1289327 := bstep (se 1 (by rfl) ⟨966995, by rfl⟩ : syracuseStep 1289327 = 1933991) B1933991
theorem B1289407 : Blo 1287962 1289407 := bstep (se 1 (by rfl) ⟨967055, by rfl⟩ : syracuseStep 1289407 = 1934111) B1934111
theorem B1289423 : Blo 1287962 1289423 := bstep (se 1 (by rfl) ⟨967067, by rfl⟩ : syracuseStep 1289423 = 1934135) B1934135
theorem B1289543 : Blo 1287962 1289543 := bstep (se 1 (by rfl) ⟨967157, by rfl⟩ : syracuseStep 1289543 = 1934315) B1934315
theorem B1289883 : Blo 1287962 1289883 := bstep (se 1 (by rfl) ⟨967412, by rfl⟩ : syracuseStep 1289883 = 1934825) B1934825
theorem B29749153 : Blo 1287962 29749153 := bstep (se 2 (by rfl) ⟨11155932, by rfl⟩ : syracuseStep 29749153 = 22311865) B22311865
theorem B11317229 : Blo 1287962 11317229 := bstep (se 3 (by rfl) ⟨2121980, by rfl⟩ : syracuseStep 11317229 = 4243961) B4243961
theorem B3264583 : Blo 1287962 3264583 := bstep (se 1 (by rfl) ⟨2448437, by rfl⟩ : syracuseStep 3264583 = 4896875) B4896875
theorem B2175113 : Blo 1287962 2175113 := bstep (se 2 (by rfl) ⟨815667, by rfl⟩ : syracuseStep 2175113 = 1631335) B1631335
theorem B5509259 : Blo 1287962 5509259 := bstep (se 1 (by rfl) ⟨4131944, by rfl⟩ : syracuseStep 5509259 = 8263889) B8263889
theorem B144871649 : Blo 1287962 144871649 := bstep (se 2 (by rfl) ⟨54326868, by rfl⟩ : syracuseStep 144871649 = 108653737) B108653737
theorem B2175403 : Blo 1287962 2175403 := bstep (se 1 (by rfl) ⟨1631552, by rfl⟩ : syracuseStep 2175403 = 3263105) B3263105
theorem B158855651 : Blo 1287962 158855651 := bstep (se 1 (by rfl) ⟨119141738, by rfl⟩ : syracuseStep 158855651 = 238283477) B238283477
theorem B6525521 : Blo 1287962 6525521 := bstep (se 2 (by rfl) ⟨2447070, by rfl⟩ : syracuseStep 6525521 = 4894141) B4894141
theorem B2175943 : Blo 1287962 2175943 := bstep (se 1 (by rfl) ⟨1631957, by rfl⟩ : syracuseStep 2175943 = 3263915) B3263915
theorem B9295145 : Blo 1287962 9295145 := bstep (se 2 (by rfl) ⟨3485679, by rfl⟩ : syracuseStep 9295145 = 6971359) B6971359
theorem B579818897 : Blo 1287962 579818897 := bstep (se 2 (by rfl) ⟨217432086, by rfl⟩ : syracuseStep 579818897 = 434864173) B434864173
theorem B2446843 : Blo 1287962 2446843 := bstep (se 1 (by rfl) ⟨1835132, by rfl⟩ : syracuseStep 2446843 = 3670265) B3670265
theorem B13219337 : Blo 1287962 13219337 := bstep (se 2 (by rfl) ⟨4957251, by rfl⟩ : syracuseStep 13219337 = 9914503) B9914503
theorem B7337567 : Blo 1287962 7337567 := bstep (se 1 (by rfl) ⟨5503175, by rfl⟩ : syracuseStep 7337567 = 11006351) B11006351
theorem B2233963 : Blo 1287962 2233963 := bstep (se 1 (by rfl) ⟨1675472, by rfl⟩ : syracuseStep 2233963 = 3350945) B3350945
theorem B31348457 : Blo 1287962 31348457 := bstep (se 2 (by rfl) ⟨11755671, by rfl⟩ : syracuseStep 31348457 = 23511343) B23511343
theorem B8255357 : Blo 1287962 8255357 := bstep (se 3 (by rfl) ⟨1547879, by rfl⟩ : syracuseStep 8255357 = 3095759) B3095759
theorem B11016161 : Blo 1287962 11016161 := bstep (se 2 (by rfl) ⟨4131060, by rfl⟩ : syracuseStep 11016161 = 8262121) B8262121
theorem B4642991 : Blo 1287962 4642991 := bstep (se 1 (by rfl) ⟨3482243, by rfl⟩ : syracuseStep 4642991 = 6964487) B6964487
theorem B2898107 : Blo 1287962 2898107 := bstep (se 1 (by rfl) ⟨2173580, by rfl⟩ : syracuseStep 2898107 = 4347161) B4347161
theorem B16513217 : Blo 1287962 16513217 := bstep (se 2 (by rfl) ⟨6192456, by rfl⟩ : syracuseStep 16513217 = 12384913) B12384913
theorem B130603373 : Blo 1287962 130603373 := bstep (se 3 (by rfl) ⟨24488132, by rfl⟩ : syracuseStep 130603373 = 48976265) B48976265
theorem B2447815 : Blo 1287962 2447815 := bstep (se 1 (by rfl) ⟨1835861, by rfl⟩ : syracuseStep 2447815 = 3671723) B3671723
theorem B4643335 : Blo 1287962 4643335 := bstep (se 1 (by rfl) ⟨3482501, by rfl⟩ : syracuseStep 4643335 = 6965003) B6965003
theorem B2751059 : Blo 1287962 2751059 := bstep (se 1 (by rfl) ⟨2063294, by rfl⟩ : syracuseStep 2751059 = 4126589) B4126589
theorem B3668647 : Blo 1287962 3668647 := bstep (se 1 (by rfl) ⟨2751485, by rfl⟩ : syracuseStep 3668647 = 5502971) B5502971
theorem B2751239 : Blo 1287962 2751239 := bstep (se 1 (by rfl) ⟨2063429, by rfl⟩ : syracuseStep 2751239 = 4126859) B4126859
theorem B55712731 : Blo 1287962 55712731 := bstep (se 1 (by rfl) ⟨41784548, by rfl⟩ : syracuseStep 55712731 = 83569097) B83569097
theorem B2448377 : Blo 1287962 2448377 := bstep (se 2 (by rfl) ⟨918141, by rfl⟩ : syracuseStep 2448377 = 1836283) B1836283
theorem B29752393 : Blo 1287962 29752393 := bstep (se 2 (by rfl) ⟨11157147, by rfl⟩ : syracuseStep 29752393 = 22314295) B22314295
theorem B7445789 : Blo 1287962 7445789 := bstep (se 3 (by rfl) ⟨1396085, by rfl⟩ : syracuseStep 7445789 = 2792171) B2792171
theorem B11017559 : Blo 1287962 11017559 := bstep (se 1 (by rfl) ⟨8263169, by rfl⟩ : syracuseStep 11017559 = 16526339) B16526339
theorem B26467735 : Blo 1287962 26467735 := bstep (se 1 (by rfl) ⟨19850801, by rfl⟩ : syracuseStep 26467735 = 39701603) B39701603
theorem B16522649 : Blo 1287962 16522649 := bstep (se 2 (by rfl) ⟨6195993, by rfl⟩ : syracuseStep 16522649 = 12391987) B12391987
theorem B1932767 : Blo 1287962 1932767 := bstep (se 1 (by rfl) ⟨1449575, by rfl⟩ : syracuseStep 1932767 = 2899151) B2899151
theorem B1932827 : Blo 1287962 1932827 := bstep (se 1 (by rfl) ⟨1449620, by rfl⟩ : syracuseStep 1932827 = 2899241) B2899241
theorem B1933019 : Blo 1287962 1933019 := bstep (se 1 (by rfl) ⟨1449764, by rfl⟩ : syracuseStep 1933019 = 2899529) B2899529
theorem B1933247 : Blo 1287962 1933247 := bstep (se 1 (by rfl) ⟨1449935, by rfl⟩ : syracuseStep 1933247 = 2899871) B2899871
theorem B9781235 : Blo 1287962 9781235 := bstep (se 1 (by rfl) ⟨7335926, by rfl⟩ : syracuseStep 9781235 = 14671853) B14671853
theorem B2900015 : Blo 1287962 2900015 := bstep (se 1 (by rfl) ⟨2175011, by rfl⟩ : syracuseStep 2900015 = 4350023) B4350023
theorem B1933367 : Blo 1287962 1933367 := bstep (se 1 (by rfl) ⟨1450025, by rfl⟩ : syracuseStep 1933367 = 2900051) B2900051
theorem B1933403 : Blo 1287962 1933403 := bstep (se 1 (by rfl) ⟨1450052, by rfl⟩ : syracuseStep 1933403 = 2900105) B2900105
theorem B1450075 : Blo 1287962 1450075 := bstep (se 1 (by rfl) ⟨1087556, by rfl⟩ : syracuseStep 1450075 = 2175113) B2175113
theorem B4350347 : Blo 1287962 4350347 := bstep (se 1 (by rfl) ⟨3262760, by rfl⟩ : syracuseStep 4350347 = 6525521) B6525521
theorem B5882267 : Blo 1287962 5882267 := bstep (se 1 (by rfl) ⟨4411700, by rfl⟩ : syracuseStep 5882267 = 8823401) B8823401
theorem B20906423 : Blo 1287962 20906423 := bstep (se 1 (by rfl) ⟨15679817, by rfl⟩ : syracuseStep 20906423 = 31359635) B31359635
theorem B7340483 : Blo 1287962 7340483 := bstep (se 1 (by rfl) ⟨5505362, by rfl⟩ : syracuseStep 7340483 = 11010725) B11010725
theorem B1933871 : Blo 1287962 1933871 := bstep (se 1 (by rfl) ⟨1450403, by rfl⟩ : syracuseStep 1933871 = 2900807) B2900807
theorem B2900537 : Blo 1287962 2900537 := bstep (se 2 (by rfl) ⟨1087701, by rfl⟩ : syracuseStep 2900537 = 2175403) B2175403
theorem B4891529 : Blo 1287962 4891529 := bstep (se 2 (by rfl) ⟨1834323, by rfl⟩ : syracuseStep 4891529 = 3668647) B3668647
theorem B7340939 : Blo 1287962 7340939 := bstep (se 1 (by rfl) ⟨5505704, by rfl⟩ : syracuseStep 7340939 = 11011409) B11011409
theorem B4891711 : Blo 1287962 4891711 := bstep (se 1 (by rfl) ⟨3668783, by rfl⟩ : syracuseStep 4891711 = 7337567) B7337567
theorem B27878509 : Blo 1287962 27878509 := bstep (se 3 (by rfl) ⟨5227220, by rfl⟩ : syracuseStep 27878509 = 10454441) B10454441
theorem B20898971 : Blo 1287962 20898971 := bstep (se 1 (by rfl) ⟨15674228, by rfl⟩ : syracuseStep 20898971 = 31348457) B31348457
theorem B2901257 : Blo 1287962 2901257 := bstep (se 2 (by rfl) ⟨1087971, by rfl⟩ : syracuseStep 2901257 = 2175943) B2175943
theorem B2901311 : Blo 1287962 2901311 := bstep (se 1 (by rfl) ⟨2175983, by rfl⟩ : syracuseStep 2901311 = 4351967) B4351967
theorem B3671507 : Blo 1287962 3671507 := bstep (se 1 (by rfl) ⟨2753630, by rfl⟩ : syracuseStep 3671507 = 5507261) B5507261
theorem B9291455 : Blo 1287962 9291455 := bstep (se 1 (by rfl) ⟨6968591, by rfl⟩ : syracuseStep 9291455 = 13937183) B13937183
theorem B6522767 : Blo 1287962 6522767 := bstep (se 1 (by rfl) ⟨4892075, by rfl⟩ : syracuseStep 6522767 = 9784151) B9784151
theorem B3671963 : Blo 1287962 3671963 := bstep (se 1 (by rfl) ⟨2753972, by rfl⟩ : syracuseStep 3671963 = 5507945) B5507945
theorem B3262457 : Blo 1287962 3262457 := bstep (se 2 (by rfl) ⟨1223421, by rfl⟩ : syracuseStep 3262457 = 2446843) B2446843
theorem B1632251 : Blo 1287962 1632251 := bstep (se 1 (by rfl) ⟨1224188, by rfl⟩ : syracuseStep 1632251 = 2448377) B2448377
theorem B1288511 : Blo 1287962 1288511 := bstep (se 1 (by rfl) ⟨966383, by rfl⟩ : syracuseStep 1288511 = 1932767) B1932767
theorem B1288551 : Blo 1287962 1288551 := bstep (se 1 (by rfl) ⟨966413, by rfl⟩ : syracuseStep 1288551 = 1932827) B1932827
theorem B1288679 : Blo 1287962 1288679 := bstep (se 1 (by rfl) ⟨966509, by rfl⟩ : syracuseStep 1288679 = 1933019) B1933019
theorem B7342649 : Blo 1287962 7342649 := bstep (se 2 (by rfl) ⟨2753493, by rfl⟩ : syracuseStep 7342649 = 5506987) B5506987
theorem B1288831 : Blo 1287962 1288831 := bstep (se 1 (by rfl) ⟨966623, by rfl⟩ : syracuseStep 1288831 = 1933247) B1933247
theorem B3672839 : Blo 1287962 3672839 := bstep (se 1 (by rfl) ⟨2754629, by rfl⟩ : syracuseStep 3672839 = 5509259) B5509259
theorem B4352777 : Blo 1287962 4352777 := bstep (se 2 (by rfl) ⟨1632291, by rfl⟩ : syracuseStep 4352777 = 3264583) B3264583
theorem B1289087 : Blo 1287962 1289087 := bstep (se 1 (by rfl) ⟨966815, by rfl⟩ : syracuseStep 1289087 = 1933631) B1933631
theorem B1289199 : Blo 1287962 1289199 := bstep (se 1 (by rfl) ⟨966899, by rfl⟩ : syracuseStep 1289199 = 1933799) B1933799
theorem B11914469 : Blo 1287962 11914469 := bstep (se 4 (by rfl) ⟨1116981, by rfl⟩ : syracuseStep 11914469 = 2233963) B2233963
theorem B3263753 : Blo 1287962 3263753 := bstep (se 2 (by rfl) ⟨1223907, by rfl⟩ : syracuseStep 3263753 = 2447815) B2447815
theorem B4894127 : Blo 1287962 4894127 := bstep (se 1 (by rfl) ⟨3670595, by rfl⟩ : syracuseStep 4894127 = 7341191) B7341191
theorem B6196763 : Blo 1287962 6196763 := bstep (se 1 (by rfl) ⟨4647572, by rfl⟩ : syracuseStep 6196763 = 9295145) B9295145
theorem B27881279 : Blo 1287962 27881279 := bstep (se 1 (by rfl) ⟨20910959, by rfl⟩ : syracuseStep 27881279 = 41821919) B41821919
theorem B7344107 : Blo 1287962 7344107 := bstep (se 1 (by rfl) ⟨5508080, by rfl⟩ : syracuseStep 7344107 = 11016161) B11016161
theorem B39669857 : Blo 1287962 39669857 := bstep (se 2 (by rfl) ⟨14876196, by rfl⟩ : syracuseStep 39669857 = 29752393) B29752393
theorem B87068915 : Blo 1287962 87068915 := bstep (se 1 (by rfl) ⟨65301686, by rfl⟩ : syracuseStep 87068915 = 130603373) B130603373
theorem B7844633 : Blo 1287962 7844633 := bstep (se 2 (by rfl) ⟨2941737, by rfl⟩ : syracuseStep 7844633 = 5883475) B5883475
theorem B7345039 : Blo 1287962 7345039 := bstep (se 1 (by rfl) ⟨5508779, by rfl⟩ : syracuseStep 7345039 = 11017559) B11017559
theorem B5510045 : Blo 1287962 5510045 := bstep (se 3 (by rfl) ⟨1033133, by rfl⟩ : syracuseStep 5510045 = 2066267) B2066267
theorem B11015099 : Blo 1287962 11015099 := bstep (se 1 (by rfl) ⟨8261324, by rfl⟩ : syracuseStep 11015099 = 16522649) B16522649
theorem B96581099 : Blo 1287962 96581099 := bstep (se 1 (by rfl) ⟨72435824, by rfl⟩ : syracuseStep 96581099 = 144871649) B144871649
theorem B11753075 : Blo 1287962 11753075 := bstep (se 1 (by rfl) ⟨8814806, by rfl⟩ : syracuseStep 11753075 = 17629613) B17629613
theorem B105903767 : Blo 1287962 105903767 := bstep (se 1 (by rfl) ⟨79427825, by rfl⟩ : syracuseStep 105903767 = 158855651) B158855651
theorem B6191113 : Blo 1287962 6191113 := bstep (se 2 (by rfl) ⟨2321667, by rfl⟩ : syracuseStep 6191113 = 4643335) B4643335
theorem B386545931 : Blo 1287962 386545931 := bstep (se 1 (by rfl) ⟨289909448, by rfl⟩ : syracuseStep 386545931 = 579818897) B579818897
theorem B8812891 : Blo 1287962 8812891 := bstep (se 1 (by rfl) ⟨6609668, by rfl⟩ : syracuseStep 8812891 = 13219337) B13219337
theorem B5503571 : Blo 1287962 5503571 := bstep (se 1 (by rfl) ⟨4127678, by rfl⟩ : syracuseStep 5503571 = 8255357) B8255357
theorem B2939503 : Blo 1287962 2939503 := bstep (se 1 (by rfl) ⟨2204627, by rfl⟩ : syracuseStep 2939503 = 4409255) B4409255
theorem B74283641 : Blo 1287962 74283641 := bstep (se 2 (by rfl) ⟨27856365, by rfl⟩ : syracuseStep 74283641 = 55712731) B55712731
theorem B3095327 : Blo 1287962 3095327 := bstep (se 1 (by rfl) ⟨2321495, by rfl⟩ : syracuseStep 3095327 = 4642991) B4642991
theorem B1932071 : Blo 1287962 1932071 := bstep (se 1 (by rfl) ⟨1449053, by rfl⟩ : syracuseStep 1932071 = 2898107) B2898107
theorem B11008811 : Blo 1287962 11008811 := bstep (se 1 (by rfl) ⟨8256608, by rfl⟩ : syracuseStep 11008811 = 16513217) B16513217
theorem B8264605 : Blo 1287962 8264605 := bstep (se 3 (by rfl) ⟨1549613, by rfl⟩ : syracuseStep 8264605 = 3099227) B3099227
theorem B1834039 : Blo 1287962 1834039 := bstep (se 1 (by rfl) ⟨1375529, by rfl⟩ : syracuseStep 1834039 = 2751059) B2751059
theorem B1834159 : Blo 1287962 1834159 := bstep (se 1 (by rfl) ⟨1375619, by rfl⟩ : syracuseStep 1834159 = 2751239) B2751239
theorem B35290313 : Blo 1287962 35290313 := bstep (se 2 (by rfl) ⟨13233867, by rfl⟩ : syracuseStep 35290313 = 26467735) B26467735
theorem B8264915 : Blo 1287962 8264915 := bstep (se 1 (by rfl) ⟨6198686, by rfl⟩ : syracuseStep 8264915 = 12397373) B12397373
theorem B4963859 : Blo 1287962 4963859 := bstep (se 1 (by rfl) ⟨3722894, by rfl⟩ : syracuseStep 4963859 = 7445789) B7445789
theorem B33054317 : Blo 1287962 33054317 := bstep (se 3 (by rfl) ⟨6197684, by rfl⟩ : syracuseStep 33054317 = 12395369) B12395369
theorem B11165357 : Blo 1287962 11165357 := bstep (se 3 (by rfl) ⟨2093504, by rfl⟩ : syracuseStep 11165357 = 4187009) B4187009
theorem B39665537 : Blo 1287962 39665537 := bstep (se 2 (by rfl) ⟨14874576, by rfl⟩ : syracuseStep 39665537 = 29749153) B29749153
theorem B7544819 : Blo 1287962 7544819 := bstep (se 1 (by rfl) ⟨5658614, by rfl⟩ : syracuseStep 7544819 = 11317229) B11317229
theorem B6520823 : Blo 1287962 6520823 := bstep (se 1 (by rfl) ⟨4890617, by rfl⟩ : syracuseStep 6520823 = 9781235) B9781235
theorem B1933343 : Blo 1287962 1933343 := bstep (se 1 (by rfl) ⟨1450007, by rfl⟩ : syracuseStep 1933343 = 2900015) B2900015
theorem B1933433 : Blo 1287962 1933433 := bstep (se 2 (by rfl) ⟨725037, by rfl⟩ : syracuseStep 1933433 = 1450075) B1450075
theorem B2900231 : Blo 1287962 2900231 := bstep (se 1 (by rfl) ⟨2175173, by rfl⟩ : syracuseStep 2900231 = 4350347) B4350347
theorem B1933691 : Blo 1287962 1933691 := bstep (se 1 (by rfl) ⟨1450268, by rfl⟩ : syracuseStep 1933691 = 2900537) B2900537
theorem B3261019 : Blo 1287962 3261019 := bstep (se 1 (by rfl) ⟨2445764, by rfl⟩ : syracuseStep 3261019 = 4891529) B4891529
theorem B1934171 : Blo 1287962 1934171 := bstep (se 1 (by rfl) ⟨1450628, by rfl⟩ : syracuseStep 1934171 = 2901257) B2901257
theorem B1934207 : Blo 1287962 1934207 := bstep (se 1 (by rfl) ⟨1450655, by rfl⟩ : syracuseStep 1934207 = 2901311) B2901311
theorem B6194303 : Blo 1287962 6194303 := bstep (se 1 (by rfl) ⟨4645727, by rfl⟩ : syracuseStep 6194303 = 9291455) B9291455
theorem B11019473 : Blo 1287962 11019473 := bstep (se 2 (by rfl) ⟨4132302, by rfl⟩ : syracuseStep 11019473 = 8264605) B8264605
theorem B6522281 : Blo 1287962 6522281 := bstep (se 2 (by rfl) ⟨2445855, by rfl⟩ : syracuseStep 6522281 = 4891711) B4891711
theorem B5029879 : Blo 1287962 5029879 := bstep (se 1 (by rfl) ⟨3772409, by rfl⟩ : syracuseStep 5029879 = 7544819) B7544819
theorem B257697287 : Blo 1287962 257697287 := bstep (se 1 (by rfl) ⟨193272965, by rfl⟩ : syracuseStep 257697287 = 386545931) B386545931
theorem B49522427 : Blo 1287962 49522427 := bstep (se 1 (by rfl) ⟨37141820, by rfl⟩ : syracuseStep 49522427 = 74283641) B74283641
theorem B2901851 : Blo 1287962 2901851 := bstep (se 1 (by rfl) ⟨2176388, by rfl⟩ : syracuseStep 2901851 = 4352777) B4352777
theorem B1288047 : Blo 1287962 1288047 := bstep (se 1 (by rfl) ⟨966035, by rfl⟩ : syracuseStep 1288047 = 1932071) B1932071
theorem B3262751 : Blo 1287962 3262751 := bstep (se 1 (by rfl) ⟨2447063, by rfl⟩ : syracuseStep 3262751 = 4894127) B4894127
theorem B4131175 : Blo 1287962 4131175 := bstep (se 1 (by rfl) ⟨3098381, by rfl⟩ : syracuseStep 4131175 = 6196763) B6196763
theorem B4352669 : Blo 1287962 4352669 := bstep (se 3 (by rfl) ⟨816125, by rfl⟩ : syracuseStep 4352669 = 1632251) B1632251
theorem B1288911 : Blo 1287962 1288911 := bstep (se 1 (by rfl) ⟨966683, by rfl⟩ : syracuseStep 1288911 = 1933367) B1933367
theorem B1288935 : Blo 1287962 1288935 := bstep (se 1 (by rfl) ⟨966701, by rfl⟩ : syracuseStep 1288935 = 1933403) B1933403
theorem B26446571 : Blo 1287962 26446571 := bstep (se 1 (by rfl) ⟨19834928, by rfl⟩ : syracuseStep 26446571 = 39669857) B39669857
theorem B13937615 : Blo 1287962 13937615 := bstep (se 1 (by rfl) ⟨10453211, by rfl⟩ : syracuseStep 13937615 = 20906423) B20906423
theorem B4893655 : Blo 1287962 4893655 := bstep (se 1 (by rfl) ⟨3670241, by rfl⟩ : syracuseStep 4893655 = 7340483) B7340483
theorem B1289247 : Blo 1287962 1289247 := bstep (se 1 (by rfl) ⟨966935, by rfl⟩ : syracuseStep 1289247 = 1933871) B1933871
theorem B11750521 : Blo 1287962 11750521 := bstep (se 2 (by rfl) ⟨4406445, by rfl⟩ : syracuseStep 11750521 = 8812891) B8812891
theorem B5229755 : Blo 1287962 5229755 := bstep (se 1 (by rfl) ⟨3922316, by rfl⟩ : syracuseStep 5229755 = 7844633) B7844633
theorem B4893959 : Blo 1287962 4893959 := bstep (se 1 (by rfl) ⟨3670469, by rfl⟩ : syracuseStep 4893959 = 7340939) B7340939
theorem B3673363 : Blo 1287962 3673363 := bstep (se 1 (by rfl) ⟨2755022, by rfl⟩ : syracuseStep 3673363 = 5510045) B5510045
theorem B7343399 : Blo 1287962 7343399 := bstep (se 1 (by rfl) ⟨5507549, by rfl⟩ : syracuseStep 7343399 = 11015099) B11015099
theorem B3919337 : Blo 1287962 3919337 := bstep (se 2 (by rfl) ⟨1469751, by rfl⟩ : syracuseStep 3919337 = 2939503) B2939503
theorem B7835383 : Blo 1287962 7835383 := bstep (se 1 (by rfl) ⟨5876537, by rfl⟩ : syracuseStep 7835383 = 11753075) B11753075
theorem B70602511 : Blo 1287962 70602511 := bstep (se 1 (by rfl) ⟨52951883, by rfl⟩ : syracuseStep 70602511 = 105903767) B105903767
theorem B9793385 : Blo 1287962 9793385 := bstep (se 2 (by rfl) ⟨3672519, by rfl⟩ : syracuseStep 9793385 = 7345039) B7345039
theorem B2174971 : Blo 1287962 2174971 := bstep (se 1 (by rfl) ⟨1631228, by rfl⟩ : syracuseStep 2174971 = 3262457) B3262457
theorem B2445385 : Blo 1287962 2445385 := bstep (se 2 (by rfl) ⟨917019, by rfl⟩ : syracuseStep 2445385 = 1834039) B1834039
theorem B37171345 : Blo 1287962 37171345 := bstep (se 2 (by rfl) ⟨13939254, by rfl⟩ : syracuseStep 37171345 = 27878509) B27878509
theorem B2445545 : Blo 1287962 2445545 := bstep (se 2 (by rfl) ⟨917079, by rfl⟩ : syracuseStep 2445545 = 1834159) B1834159
theorem B4895099 : Blo 1287962 4895099 := bstep (se 1 (by rfl) ⟨3671324, by rfl⟩ : syracuseStep 4895099 = 7342649) B7342649
theorem B5509943 : Blo 1287962 5509943 := bstep (se 1 (by rfl) ⟨4132457, by rfl⟩ : syracuseStep 5509943 = 8264915) B8264915
theorem B7942979 : Blo 1287962 7942979 := bstep (se 1 (by rfl) ⟨5957234, by rfl⟩ : syracuseStep 7942979 = 11914469) B11914469
theorem B2175835 : Blo 1287962 2175835 := bstep (se 1 (by rfl) ⟨1631876, by rfl⟩ : syracuseStep 2175835 = 3263753) B3263753
theorem B7443571 : Blo 1287962 7443571 := bstep (se 1 (by rfl) ⟨5582678, by rfl⟩ : syracuseStep 7443571 = 11165357) B11165357
theorem B4896071 : Blo 1287962 4896071 := bstep (se 1 (by rfl) ⟨3672053, by rfl⟩ : syracuseStep 4896071 = 7344107) B7344107
theorem B4347215 : Blo 1287962 4347215 := bstep (se 1 (by rfl) ⟨3260411, by rfl⟩ : syracuseStep 4347215 = 6520823) B6520823
theorem B8254817 : Blo 1287962 8254817 := bstep (se 2 (by rfl) ⟨3095556, by rfl⟩ : syracuseStep 8254817 = 6191113) B6191113
theorem B58045943 : Blo 1287962 58045943 := bstep (se 1 (by rfl) ⟨43534457, by rfl⟩ : syracuseStep 58045943 = 87068915) B87068915
theorem B13932647 : Blo 1287962 13932647 := bstep (se 1 (by rfl) ⟨10449485, by rfl⟩ : syracuseStep 13932647 = 20898971) B20898971
theorem B2447671 : Blo 1287962 2447671 := bstep (se 1 (by rfl) ⟨1835753, by rfl⟩ : syracuseStep 2447671 = 3671507) B3671507
theorem B64387399 : Blo 1287962 64387399 := bstep (se 1 (by rfl) ⟨48290549, by rfl⟩ : syracuseStep 64387399 = 96581099) B96581099
theorem B15686045 : Blo 1287962 15686045 := bstep (se 3 (by rfl) ⟨2941133, by rfl⟩ : syracuseStep 15686045 = 5882267) B5882267
theorem B4348511 : Blo 1287962 4348511 := bstep (se 1 (by rfl) ⟨3261383, by rfl⟩ : syracuseStep 4348511 = 6522767) B6522767
theorem B2447975 : Blo 1287962 2447975 := bstep (se 1 (by rfl) ⟨1835981, by rfl⟩ : syracuseStep 2447975 = 3671963) B3671963
theorem B3669047 : Blo 1287962 3669047 := bstep (se 1 (by rfl) ⟨2751785, by rfl⟩ : syracuseStep 3669047 = 5503571) B5503571
theorem B2448559 : Blo 1287962 2448559 := bstep (se 1 (by rfl) ⟨1836419, by rfl⟩ : syracuseStep 2448559 = 3672839) B3672839
theorem B2063551 : Blo 1287962 2063551 := bstep (se 1 (by rfl) ⟨1547663, by rfl⟩ : syracuseStep 2063551 = 3095327) B3095327
theorem B7339207 : Blo 1287962 7339207 := bstep (se 1 (by rfl) ⟨5504405, by rfl⟩ : syracuseStep 7339207 = 11008811) B11008811
theorem B23526875 : Blo 1287962 23526875 := bstep (se 1 (by rfl) ⟨17645156, by rfl⟩ : syracuseStep 23526875 = 35290313) B35290313
theorem B3309239 : Blo 1287962 3309239 := bstep (se 1 (by rfl) ⟨2481929, by rfl⟩ : syracuseStep 3309239 = 4963859) B4963859
theorem B22036211 : Blo 1287962 22036211 := bstep (se 1 (by rfl) ⟨16527158, by rfl⟩ : syracuseStep 22036211 = 33054317) B33054317
theorem B18587519 : Blo 1287962 18587519 := bstep (se 1 (by rfl) ⟨13940639, by rfl⟩ : syracuseStep 18587519 = 27881279) B27881279
theorem B26443691 : Blo 1287962 26443691 := bstep (se 1 (by rfl) ⟨19832768, by rfl⟩ : syracuseStep 26443691 = 39665537) B39665537
theorem B3260513 : Blo 1287962 3260513 := bstep (se 2 (by rfl) ⟨1222692, by rfl⟩ : syracuseStep 3260513 = 2445385) B2445385
theorem B1630363 : Blo 1287962 1630363 := bstep (se 1 (by rfl) ⟨1222772, by rfl⟩ : syracuseStep 1630363 = 2445545) B2445545
theorem B1933487 : Blo 1287962 1933487 := bstep (se 1 (by rfl) ⟨1450115, by rfl⟩ : syracuseStep 1933487 = 2900231) B2900231
theorem B49561793 : Blo 1287962 49561793 := bstep (se 2 (by rfl) ⟨18585672, by rfl⟩ : syracuseStep 49561793 = 37171345) B37171345
theorem B2899961 : Blo 1287962 2899961 := bstep (se 2 (by rfl) ⟨1087485, by rfl⟩ : syracuseStep 2899961 = 2174971) B2174971
theorem B4129535 : Blo 1287962 4129535 := bstep (se 1 (by rfl) ⟨3097151, by rfl⟩ : syracuseStep 4129535 = 6194303) B6194303
theorem B2901113 : Blo 1287962 2901113 := bstep (se 2 (by rfl) ⟨1087917, by rfl⟩ : syracuseStep 2901113 = 2175835) B2175835
theorem B33014951 : Blo 1287962 33014951 := bstep (se 1 (by rfl) ⟨24761213, by rfl⟩ : syracuseStep 33014951 = 49522427) B49522427
theorem B1934567 : Blo 1287962 1934567 := bstep (se 1 (by rfl) ⟨1450925, by rfl⟩ : syracuseStep 1934567 = 2901851) B2901851
theorem B154789181 : Blo 1287962 154789181 := bstep (se 3 (by rfl) ⟨29022971, by rfl⟩ : syracuseStep 154789181 = 58045943) B58045943
theorem B1631983 : Blo 1287962 1631983 := bstep (se 1 (by rfl) ⟨1223987, by rfl⟩ : syracuseStep 1631983 = 2447975) B2447975
theorem B2901779 : Blo 1287962 2901779 := bstep (se 1 (by rfl) ⟨2176334, by rfl⟩ : syracuseStep 2901779 = 4352669) B4352669
theorem B17631047 : Blo 1287962 17631047 := bstep (se 1 (by rfl) ⟨13223285, by rfl⟩ : syracuseStep 17631047 = 26446571) B26446571
theorem B9291743 : Blo 1287962 9291743 := bstep (se 1 (by rfl) ⟨6968807, by rfl⟩ : syracuseStep 9291743 = 13937615) B13937615
theorem B3262639 : Blo 1287962 3262639 := bstep (se 1 (by rfl) ⟨2446979, by rfl⟩ : syracuseStep 3262639 = 4893959) B4893959
theorem B10447177 : Blo 1287962 10447177 := bstep (se 2 (by rfl) ⟨3917691, by rfl⟩ : syracuseStep 10447177 = 7835383) B7835383
theorem B94136681 : Blo 1287962 94136681 := bstep (se 2 (by rfl) ⟨35301255, by rfl⟩ : syracuseStep 94136681 = 70602511) B70602511
theorem B2206159 : Blo 1287962 2206159 := bstep (se 1 (by rfl) ⟨1654619, by rfl⟩ : syracuseStep 2206159 = 3309239) B3309239
theorem B14690807 : Blo 1287962 14690807 := bstep (se 1 (by rfl) ⟨11018105, by rfl⟩ : syracuseStep 14690807 = 22036211) B22036211
theorem B1288895 : Blo 1287962 1288895 := bstep (se 1 (by rfl) ⟨966671, by rfl⟩ : syracuseStep 1288895 = 1933343) B1933343
theorem B1288955 : Blo 1287962 1288955 := bstep (se 1 (by rfl) ⟨966716, by rfl⟩ : syracuseStep 1288955 = 1933433) B1933433
theorem B1289127 : Blo 1287962 1289127 := bstep (se 1 (by rfl) ⟨966845, by rfl⟩ : syracuseStep 1289127 = 1933691) B1933691
theorem B3263399 : Blo 1287962 3263399 := bstep (se 1 (by rfl) ⟨2447549, by rfl⟩ : syracuseStep 3263399 = 4895099) B4895099
theorem B3263561 : Blo 1287962 3263561 := bstep (se 2 (by rfl) ⟨1223835, by rfl⟩ : syracuseStep 3263561 = 2447671) B2447671
theorem B5508233 : Blo 1287962 5508233 := bstep (se 2 (by rfl) ⟨2065587, by rfl⟩ : syracuseStep 5508233 = 4131175) B4131175
theorem B3673295 : Blo 1287962 3673295 := bstep (se 1 (by rfl) ⟨2754971, by rfl⟩ : syracuseStep 3673295 = 5509943) B5509943
theorem B1289447 : Blo 1287962 1289447 := bstep (se 1 (by rfl) ⟨967085, by rfl⟩ : syracuseStep 1289447 = 1934171) B1934171
theorem B1289471 : Blo 1287962 1289471 := bstep (se 1 (by rfl) ⟨967103, by rfl⟩ : syracuseStep 1289471 = 1934207) B1934207
theorem B3264047 : Blo 1287962 3264047 := bstep (se 1 (by rfl) ⟨2448035, by rfl⟩ : syracuseStep 3264047 = 4896071) B4896071
theorem B171798191 : Blo 1287962 171798191 := bstep (se 1 (by rfl) ⟨128848643, by rfl⟩ : syracuseStep 171798191 = 257697287) B257697287
theorem B62738333 : Blo 1287962 62738333 := bstep (se 3 (by rfl) ⟨11763437, by rfl⟩ : syracuseStep 62738333 = 23526875) B23526875
theorem B6524873 : Blo 1287962 6524873 := bstep (se 2 (by rfl) ⟨2446827, by rfl⟩ : syracuseStep 6524873 = 4893655) B4893655
theorem B9924761 : Blo 1287962 9924761 := bstep (se 2 (by rfl) ⟨3721785, by rfl⟩ : syracuseStep 9924761 = 7443571) B7443571
theorem B15667361 : Blo 1287962 15667361 := bstep (se 2 (by rfl) ⟨5875260, by rfl⟩ : syracuseStep 15667361 = 11750521) B11750521
theorem B2175167 : Blo 1287962 2175167 := bstep (se 1 (by rfl) ⟨1631375, by rfl⟩ : syracuseStep 2175167 = 3262751) B3262751
theorem B3264745 : Blo 1287962 3264745 := bstep (se 2 (by rfl) ⟨1224279, by rfl⟩ : syracuseStep 3264745 = 2448559) B2448559
theorem B9785609 : Blo 1287962 9785609 := bstep (se 2 (by rfl) ⟨3669603, by rfl⟩ : syracuseStep 9785609 = 7339207) B7339207
theorem B10457363 : Blo 1287962 10457363 := bstep (se 1 (by rfl) ⟨7843022, by rfl⟩ : syracuseStep 10457363 = 15686045) B15686045
theorem B2446031 : Blo 1287962 2446031 := bstep (se 1 (by rfl) ⟨1834523, by rfl⟩ : syracuseStep 2446031 = 3669047) B3669047
theorem B3486503 : Blo 1287962 3486503 := bstep (se 1 (by rfl) ⟨2614877, by rfl⟩ : syracuseStep 3486503 = 5229755) B5229755
theorem B21181277 : Blo 1287962 21181277 := bstep (se 3 (by rfl) ⟨3971489, by rfl⟩ : syracuseStep 21181277 = 7942979) B7942979
theorem B4895599 : Blo 1287962 4895599 := bstep (se 1 (by rfl) ⟨3671699, by rfl⟩ : syracuseStep 4895599 = 7343399) B7343399
theorem B12391679 : Blo 1287962 12391679 := bstep (se 1 (by rfl) ⟨9293759, by rfl⟩ : syracuseStep 12391679 = 18587519) B18587519
theorem B6706505 : Blo 1287962 6706505 := bstep (se 2 (by rfl) ⟨2514939, by rfl⟩ : syracuseStep 6706505 = 5029879) B5029879
theorem B85849865 : Blo 1287962 85849865 := bstep (se 2 (by rfl) ⟨32193699, by rfl⟩ : syracuseStep 85849865 = 64387399) B64387399
theorem B4348025 : Blo 1287962 4348025 := bstep (se 2 (by rfl) ⟨1630509, by rfl⟩ : syracuseStep 4348025 = 3261019) B3261019
theorem B7346315 : Blo 1287962 7346315 := bstep (se 1 (by rfl) ⟨5509736, by rfl⟩ : syracuseStep 7346315 = 11019473) B11019473
theorem B2898143 : Blo 1287962 2898143 := bstep (se 1 (by rfl) ⟨2173607, by rfl⟩ : syracuseStep 2898143 = 4347215) B4347215
theorem B5503211 : Blo 1287962 5503211 := bstep (se 1 (by rfl) ⟨4127408, by rfl⟩ : syracuseStep 5503211 = 8254817) B8254817
theorem B4348187 : Blo 1287962 4348187 := bstep (se 1 (by rfl) ⟨3261140, by rfl⟩ : syracuseStep 4348187 = 6522281) B6522281
theorem B9288431 : Blo 1287962 9288431 := bstep (se 1 (by rfl) ⟨6966323, by rfl⟩ : syracuseStep 9288431 = 13932647) B13932647
theorem B2751401 : Blo 1287962 2751401 := bstep (se 2 (by rfl) ⟨1031775, by rfl⟩ : syracuseStep 2751401 = 2063551) B2063551
theorem B4897817 : Blo 1287962 4897817 := bstep (se 2 (by rfl) ⟨1836681, by rfl⟩ : syracuseStep 4897817 = 3673363) B3673363
theorem B2899007 : Blo 1287962 2899007 := bstep (se 1 (by rfl) ⟨2174255, by rfl⟩ : syracuseStep 2899007 = 4348511) B4348511
theorem B2612891 : Blo 1287962 2612891 := bstep (se 1 (by rfl) ⟨1959668, by rfl⟩ : syracuseStep 2612891 = 3919337) B3919337
theorem B6528923 : Blo 1287962 6528923 := bstep (se 1 (by rfl) ⟨4896692, by rfl⟩ : syracuseStep 6528923 = 9793385) B9793385
theorem B17629127 : Blo 1287962 17629127 := bstep (se 1 (by rfl) ⟨13221845, by rfl⟩ : syracuseStep 17629127 = 26443691) B26443691
theorem B10444907 : Blo 1287962 10444907 := bstep (se 1 (by rfl) ⟨7833680, by rfl⟩ : syracuseStep 10444907 = 15667361) B15667361
theorem B1450111 : Blo 1287962 1450111 := bstep (se 1 (by rfl) ⟨1087583, by rfl⟩ : syracuseStep 1450111 = 2175167) B2175167
theorem B4350185 : Blo 1287962 4350185 := bstep (se 2 (by rfl) ⟨1631319, by rfl⟩ : syracuseStep 4350185 = 3262639) B3262639
theorem B1630687 : Blo 1287962 1630687 := bstep (se 1 (by rfl) ⟨1223015, by rfl⟩ : syracuseStep 1630687 = 2446031) B2446031
theorem B2753023 : Blo 1287962 2753023 := bstep (se 1 (by rfl) ⟨2064767, by rfl⟩ : syracuseStep 2753023 = 4129535) B4129535
theorem B27886301 : Blo 1287962 27886301 := bstep (se 3 (by rfl) ⟨5228681, by rfl⟩ : syracuseStep 27886301 = 10457363) B10457363
theorem B1934075 : Blo 1287962 1934075 := bstep (se 1 (by rfl) ⟨1450556, by rfl⟩ : syracuseStep 1934075 = 2901113) B2901113
theorem B1934519 : Blo 1287962 1934519 := bstep (se 1 (by rfl) ⟨1450889, by rfl⟩ : syracuseStep 1934519 = 2901779) B2901779
theorem B6194495 : Blo 1287962 6194495 := bstep (se 1 (by rfl) ⟨4645871, by rfl⟩ : syracuseStep 6194495 = 9291743) B9291743
theorem B3672155 : Blo 1287962 3672155 := bstep (se 1 (by rfl) ⟨2754116, by rfl⟩ : syracuseStep 3672155 = 5508233) B5508233
theorem B11766181 : Blo 1287962 11766181 := bstep (se 4 (by rfl) ⟨1103079, by rfl⟩ : syracuseStep 11766181 = 2206159) B2206159
theorem B4352615 : Blo 1287962 4352615 := bstep (se 1 (by rfl) ⟨3264461, by rfl⟩ : syracuseStep 4352615 = 6528923) B6528923
theorem B2173675 : Blo 1287962 2173675 := bstep (se 1 (by rfl) ⟨1630256, by rfl⟩ : syracuseStep 2173675 = 3260513) B3260513
theorem B1288991 : Blo 1287962 1288991 := bstep (se 1 (by rfl) ⟨966743, by rfl⟩ : syracuseStep 1288991 = 1933487) B1933487
theorem B33041195 : Blo 1287962 33041195 := bstep (se 1 (by rfl) ⟨24780896, by rfl⟩ : syracuseStep 33041195 = 49561793) B49561793
theorem B6523739 : Blo 1287962 6523739 := bstep (se 1 (by rfl) ⟨4892804, by rfl⟩ : syracuseStep 6523739 = 9785609) B9785609
theorem B2173817 : Blo 1287962 2173817 := bstep (se 2 (by rfl) ⟨815181, by rfl⟩ : syracuseStep 2173817 = 1630363) B1630363
theorem B4352993 : Blo 1287962 4352993 := bstep (se 2 (by rfl) ⟨1632372, by rfl⟩ : syracuseStep 4352993 = 3264745) B3264745
theorem B13929569 : Blo 1287962 13929569 := bstep (se 2 (by rfl) ⟨5223588, by rfl⟩ : syracuseStep 13929569 = 10447177) B10447177
theorem B1289711 : Blo 1287962 1289711 := bstep (se 1 (by rfl) ⟨967283, by rfl⟩ : syracuseStep 1289711 = 1934567) B1934567
theorem B8261119 : Blo 1287962 8261119 := bstep (se 1 (by rfl) ⟨6195839, by rfl⟩ : syracuseStep 8261119 = 12391679) B12391679
theorem B57233243 : Blo 1287962 57233243 := bstep (se 1 (by rfl) ⟨42924932, by rfl⟩ : syracuseStep 57233243 = 85849865) B85849865
theorem B9793871 : Blo 1287962 9793871 := bstep (se 1 (by rfl) ⟨7345403, by rfl⟩ : syracuseStep 9793871 = 14690807) B14690807
theorem B2175599 : Blo 1287962 2175599 := bstep (se 1 (by rfl) ⟨1631699, by rfl⟩ : syracuseStep 2175599 = 3263399) B3263399
theorem B3265211 : Blo 1287962 3265211 := bstep (se 1 (by rfl) ⟨2448908, by rfl⟩ : syracuseStep 3265211 = 4897817) B4897817
theorem B2175707 : Blo 1287962 2175707 := bstep (se 1 (by rfl) ⟨1631780, by rfl⟩ : syracuseStep 2175707 = 3263561) B3263561
theorem B2175977 : Blo 1287962 2175977 := bstep (se 2 (by rfl) ⟨815991, by rfl⟩ : syracuseStep 2175977 = 1631983) B1631983
theorem B2176031 : Blo 1287962 2176031 := bstep (se 1 (by rfl) ⟨1632023, by rfl⟩ : syracuseStep 2176031 = 3264047) B3264047
theorem B1741927 : Blo 1287962 1741927 := bstep (se 1 (by rfl) ⟨1306445, by rfl⟩ : syracuseStep 1741927 = 2612891) B2612891
theorem B41825555 : Blo 1287962 41825555 := bstep (se 1 (by rfl) ⟨31369166, by rfl⟩ : syracuseStep 41825555 = 62738333) B62738333
theorem B11752751 : Blo 1287962 11752751 := bstep (se 1 (by rfl) ⟨8814563, by rfl⟩ : syracuseStep 11752751 = 17629127) B17629127
theorem B6616507 : Blo 1287962 6616507 := bstep (se 1 (by rfl) ⟨4962380, by rfl⟩ : syracuseStep 6616507 = 9924761) B9924761
theorem B2324335 : Blo 1287962 2324335 := bstep (se 1 (by rfl) ⟨1743251, by rfl⟩ : syracuseStep 2324335 = 3486503) B3486503
theorem B14120851 : Blo 1287962 14120851 := bstep (se 1 (by rfl) ⟨10590638, by rfl⟩ : syracuseStep 14120851 = 21181277) B21181277
theorem B22009967 : Blo 1287962 22009967 := bstep (se 1 (by rfl) ⟨16507475, by rfl⟩ : syracuseStep 22009967 = 33014951) B33014951
theorem B103192787 : Blo 1287962 103192787 := bstep (se 1 (by rfl) ⟨77394590, by rfl⟩ : syracuseStep 103192787 = 154789181) B154789181
theorem B4471003 : Blo 1287962 4471003 := bstep (se 1 (by rfl) ⟨3353252, by rfl⟩ : syracuseStep 4471003 = 6706505) B6706505
theorem B6527465 : Blo 1287962 6527465 := bstep (se 2 (by rfl) ⟨2447799, by rfl⟩ : syracuseStep 6527465 = 4895599) B4895599
theorem B11754031 : Blo 1287962 11754031 := bstep (se 1 (by rfl) ⟨8815523, by rfl⟩ : syracuseStep 11754031 = 17631047) B17631047
theorem B2898683 : Blo 1287962 2898683 := bstep (se 1 (by rfl) ⟨2174012, by rfl⟩ : syracuseStep 2898683 = 4348025) B4348025
theorem B4897543 : Blo 1287962 4897543 := bstep (se 1 (by rfl) ⟨3673157, by rfl⟩ : syracuseStep 4897543 = 7346315) B7346315
theorem B1932095 : Blo 1287962 1932095 := bstep (se 1 (by rfl) ⟨1449071, by rfl⟩ : syracuseStep 1932095 = 2898143) B2898143
theorem B3668807 : Blo 1287962 3668807 := bstep (se 1 (by rfl) ⟨2751605, by rfl⟩ : syracuseStep 3668807 = 5503211) B5503211
theorem B2898791 : Blo 1287962 2898791 := bstep (se 1 (by rfl) ⟨2174093, by rfl⟩ : syracuseStep 2898791 = 4348187) B4348187
theorem B62757787 : Blo 1287962 62757787 := bstep (se 1 (by rfl) ⟨47068340, by rfl⟩ : syracuseStep 62757787 = 94136681) B94136681
theorem B6192287 : Blo 1287962 6192287 := bstep (se 1 (by rfl) ⟨4644215, by rfl⟩ : syracuseStep 6192287 = 9288431) B9288431
theorem B1834267 : Blo 1287962 1834267 := bstep (se 1 (by rfl) ⟨1375700, by rfl⟩ : syracuseStep 1834267 = 2751401) B2751401
theorem B1932671 : Blo 1287962 1932671 := bstep (se 1 (by rfl) ⟨1449503, by rfl⟩ : syracuseStep 1932671 = 2899007) B2899007
theorem B2448863 : Blo 1287962 2448863 := bstep (se 1 (by rfl) ⟨1836647, by rfl⟩ : syracuseStep 2448863 = 3673295) B3673295
theorem B114532127 : Blo 1287962 114532127 := bstep (se 1 (by rfl) ⟨85899095, by rfl⟩ : syracuseStep 114532127 = 171798191) B171798191
theorem B4349915 : Blo 1287962 4349915 := bstep (se 1 (by rfl) ⟨3262436, by rfl⟩ : syracuseStep 4349915 = 6524873) B6524873
theorem B1933307 : Blo 1287962 1933307 := bstep (se 1 (by rfl) ⟨1449980, by rfl⟩ : syracuseStep 1933307 = 2899961) B2899961
theorem B2900123 : Blo 1287962 2900123 := bstep (se 1 (by rfl) ⟨2175092, by rfl⟩ : syracuseStep 2900123 = 4350185) B4350185
theorem B1933481 : Blo 1287962 1933481 := bstep (se 2 (by rfl) ⟨725055, by rfl⟩ : syracuseStep 1933481 = 1450111) B1450111
theorem B6529247 : Blo 1287962 6529247 := bstep (se 1 (by rfl) ⟨4896935, by rfl⟩ : syracuseStep 6529247 = 9793871) B9793871
theorem B27853085 : Blo 1287962 27853085 := bstep (se 3 (by rfl) ⟨5222453, by rfl⟩ : syracuseStep 27853085 = 10444907) B10444907
theorem B1450399 : Blo 1287962 1450399 := bstep (se 1 (by rfl) ⟨1087799, by rfl⟩ : syracuseStep 1450399 = 2175599) B2175599
theorem B1450471 : Blo 1287962 1450471 := bstep (se 1 (by rfl) ⟨1087853, by rfl⟩ : syracuseStep 1450471 = 2175707) B2175707
theorem B15688241 : Blo 1287962 15688241 := bstep (se 2 (by rfl) ⟨5883090, by rfl⟩ : syracuseStep 15688241 = 11766181) B11766181
theorem B1450651 : Blo 1287962 1450651 := bstep (se 1 (by rfl) ⟨1087988, by rfl⟩ : syracuseStep 1450651 = 2175977) B2175977
theorem B3670697 : Blo 1287962 3670697 := bstep (se 2 (by rfl) ⟨1376511, by rfl⟩ : syracuseStep 3670697 = 2753023) B2753023
theorem B1450687 : Blo 1287962 1450687 := bstep (se 1 (by rfl) ⟨1088015, by rfl⟩ : syracuseStep 1450687 = 2176031) B2176031
theorem B15672041 : Blo 1287962 15672041 := bstep (se 2 (by rfl) ⟨5877015, by rfl⟩ : syracuseStep 15672041 = 11754031) B11754031
theorem B6530057 : Blo 1287962 6530057 := bstep (se 2 (by rfl) ⟨2448771, by rfl⟩ : syracuseStep 6530057 = 4897543) B4897543
theorem B14673311 : Blo 1287962 14673311 := bstep (se 1 (by rfl) ⟨11004983, by rfl⟩ : syracuseStep 14673311 = 22009967) B22009967
theorem B4351643 : Blo 1287962 4351643 := bstep (se 1 (by rfl) ⟨3263732, by rfl⟩ : syracuseStep 4351643 = 6527465) B6527465
theorem B2901743 : Blo 1287962 2901743 := bstep (se 1 (by rfl) ⟨2176307, by rfl⟩ : syracuseStep 2901743 = 4352615) B4352615
theorem B1288063 : Blo 1287962 1288063 := bstep (se 1 (by rfl) ⟨966047, by rfl⟩ : syracuseStep 1288063 = 1932095) B1932095
theorem B2901995 : Blo 1287962 2901995 := bstep (se 1 (by rfl) ⟨2176496, by rfl⟩ : syracuseStep 2901995 = 4352993) B4352993
theorem B1288447 : Blo 1287962 1288447 := bstep (se 1 (by rfl) ⟨966335, by rfl⟩ : syracuseStep 1288447 = 1932671) B1932671
theorem B1632575 : Blo 1287962 1632575 := bstep (se 1 (by rfl) ⟨1224431, by rfl⟩ : syracuseStep 1632575 = 2448863) B2448863
theorem B3099113 : Blo 1287962 3099113 := bstep (se 2 (by rfl) ⟨1162167, by rfl⟩ : syracuseStep 3099113 = 2324335) B2324335
theorem B18827801 : Blo 1287962 18827801 := bstep (se 2 (by rfl) ⟨7060425, by rfl⟩ : syracuseStep 18827801 = 14120851) B14120851
theorem B1288871 : Blo 1287962 1288871 := bstep (se 1 (by rfl) ⟨966653, by rfl⟩ : syracuseStep 1288871 = 1933307) B1933307
theorem B9792413 : Blo 1287962 9792413 := bstep (se 3 (by rfl) ⟨1836077, by rfl⟩ : syracuseStep 9792413 = 3672155) B3672155
theorem B18590867 : Blo 1287962 18590867 := bstep (se 1 (by rfl) ⟨13943150, by rfl⟩ : syracuseStep 18590867 = 27886301) B27886301
theorem B1289383 : Blo 1287962 1289383 := bstep (se 1 (by rfl) ⟨967037, by rfl⟩ : syracuseStep 1289383 = 1934075) B1934075
theorem B2174249 : Blo 1287962 2174249 := bstep (se 2 (by rfl) ⟨815343, by rfl⟩ : syracuseStep 2174249 = 1630687) B1630687
theorem B1289679 : Blo 1287962 1289679 := bstep (se 1 (by rfl) ⟨967259, by rfl⟩ : syracuseStep 1289679 = 1934519) B1934519
theorem B16518653 : Blo 1287962 16518653 := bstep (se 3 (by rfl) ⟨3097247, by rfl⟩ : syracuseStep 16518653 = 6194495) B6194495
theorem B7835167 : Blo 1287962 7835167 := bstep (se 1 (by rfl) ⟨5876375, by rfl⟩ : syracuseStep 7835167 = 11752751) B11752751
theorem B83677049 : Blo 1287962 83677049 := bstep (se 2 (by rfl) ⟨31378893, by rfl⟩ : syracuseStep 83677049 = 62757787) B62757787
theorem B2322569 : Blo 1287962 2322569 := bstep (se 2 (by rfl) ⟨870963, by rfl⟩ : syracuseStep 2322569 = 1741927) B1741927
theorem B2445689 : Blo 1287962 2445689 := bstep (se 2 (by rfl) ⟨917133, by rfl⟩ : syracuseStep 2445689 = 1834267) B1834267
theorem B2445871 : Blo 1287962 2445871 := bstep (se 1 (by rfl) ⟨1834403, by rfl⟩ : syracuseStep 2445871 = 3668807) B3668807
theorem B11014825 : Blo 1287962 11014825 := bstep (se 2 (by rfl) ⟨4130559, by rfl⟩ : syracuseStep 11014825 = 8261119) B8261119
theorem B9286379 : Blo 1287962 9286379 := bstep (se 1 (by rfl) ⟨6964784, by rfl⟩ : syracuseStep 9286379 = 13929569) B13929569
theorem B76354751 : Blo 1287962 76354751 := bstep (se 1 (by rfl) ⟨57266063, by rfl⟩ : syracuseStep 76354751 = 114532127) B114532127
theorem B38155495 : Blo 1287962 38155495 := bstep (se 1 (by rfl) ⟨28616621, by rfl⟩ : syracuseStep 38155495 = 57233243) B57233243
theorem B5961337 : Blo 1287962 5961337 := bstep (se 2 (by rfl) ⟨2235501, by rfl⟩ : syracuseStep 5961337 = 4471003) B4471003
theorem B2176807 : Blo 1287962 2176807 := bstep (se 1 (by rfl) ⟨1632605, by rfl⟩ : syracuseStep 2176807 = 3265211) B3265211
theorem B27883703 : Blo 1287962 27883703 := bstep (se 1 (by rfl) ⟨20912777, by rfl⟩ : syracuseStep 27883703 = 41825555) B41825555
theorem B2898233 : Blo 1287962 2898233 := bstep (se 2 (by rfl) ⟨1086837, by rfl⟩ : syracuseStep 2898233 = 2173675) B2173675
theorem B68795191 : Blo 1287962 68795191 := bstep (se 1 (by rfl) ⟨51596393, by rfl⟩ : syracuseStep 68795191 = 103192787) B103192787
theorem B1932455 : Blo 1287962 1932455 := bstep (se 1 (by rfl) ⟨1449341, by rfl⟩ : syracuseStep 1932455 = 2898683) B2898683
theorem B22027463 : Blo 1287962 22027463 := bstep (se 1 (by rfl) ⟨16520597, by rfl⟩ : syracuseStep 22027463 = 33041195) B33041195
theorem B4349159 : Blo 1287962 4349159 := bstep (se 1 (by rfl) ⟨3261869, by rfl⟩ : syracuseStep 4349159 = 6523739) B6523739
theorem B1932527 : Blo 1287962 1932527 := bstep (se 1 (by rfl) ⟨1449395, by rfl⟩ : syracuseStep 1932527 = 2898791) B2898791
theorem B8822009 : Blo 1287962 8822009 := bstep (se 2 (by rfl) ⟨3308253, by rfl⟩ : syracuseStep 8822009 = 6616507) B6616507
theorem B1449211 : Blo 1287962 1449211 := bstep (se 1 (by rfl) ⟨1086908, by rfl⟩ : syracuseStep 1449211 = 2173817) B2173817
theorem B4128191 : Blo 1287962 4128191 := bstep (se 1 (by rfl) ⟨3096143, by rfl⟩ : syracuseStep 4128191 = 6192287) B6192287
theorem B2899943 : Blo 1287962 2899943 := bstep (se 1 (by rfl) ⟨2174957, by rfl⟩ : syracuseStep 2899943 = 4349915) B4349915
theorem B1548379 : Blo 1287962 1548379 := bstep (se 1 (by rfl) ⟨1161284, by rfl⟩ : syracuseStep 1548379 = 2322569) B2322569
theorem B1933415 : Blo 1287962 1933415 := bstep (se 1 (by rfl) ⟨1450061, by rfl⟩ : syracuseStep 1933415 = 2900123) B2900123
theorem B1630459 : Blo 1287962 1630459 := bstep (se 1 (by rfl) ⟨1222844, by rfl⟩ : syracuseStep 1630459 = 2445689) B2445689
theorem B203612669 : Blo 1287962 203612669 := bstep (se 3 (by rfl) ⟨38177375, by rfl⟩ : syracuseStep 203612669 = 76354751) B76354751
theorem B1933865 : Blo 1287962 1933865 := bstep (se 2 (by rfl) ⟨725199, by rfl⟩ : syracuseStep 1933865 = 1450399) B1450399
theorem B1933961 : Blo 1287962 1933961 := bstep (se 2 (by rfl) ⟨725235, by rfl⟩ : syracuseStep 1933961 = 1450471) B1450471
theorem B3261161 : Blo 1287962 3261161 := bstep (se 2 (by rfl) ⟨1222935, by rfl⟩ : syracuseStep 3261161 = 2445871) B2445871
theorem B1934201 : Blo 1287962 1934201 := bstep (se 2 (by rfl) ⟨725325, by rfl⟩ : syracuseStep 1934201 = 1450651) B1450651
theorem B1934249 : Blo 1287962 1934249 := bstep (se 2 (by rfl) ⟨725343, by rfl⟩ : syracuseStep 1934249 = 1450687) B1450687
theorem B9782207 : Blo 1287962 9782207 := bstep (se 1 (by rfl) ⟨7336655, by rfl⟩ : syracuseStep 9782207 = 14673311) B14673311
theorem B91726921 : Blo 1287962 91726921 := bstep (se 2 (by rfl) ⟨34397595, by rfl⟩ : syracuseStep 91726921 = 68795191) B68795191
theorem B2901095 : Blo 1287962 2901095 := bstep (se 1 (by rfl) ⟨2175821, by rfl⟩ : syracuseStep 2901095 = 4351643) B4351643
theorem B1934495 : Blo 1287962 1934495 := bstep (se 1 (by rfl) ⟨1450871, by rfl⟩ : syracuseStep 1934495 = 2901743) B2901743
theorem B1934663 : Blo 1287962 1934663 := bstep (se 1 (by rfl) ⟨1450997, by rfl⟩ : syracuseStep 1934663 = 2901995) B2901995
theorem B18589135 : Blo 1287962 18589135 := bstep (se 1 (by rfl) ⟨13941851, by rfl⟩ : syracuseStep 18589135 = 27883703) B27883703
theorem B50873993 : Blo 1287962 50873993 := bstep (se 2 (by rfl) ⟨19077747, by rfl⟩ : syracuseStep 50873993 = 38155495) B38155495
theorem B2066075 : Blo 1287962 2066075 := bstep (se 1 (by rfl) ⟨1549556, by rfl⟩ : syracuseStep 2066075 = 3099113) B3099113
theorem B12551867 : Blo 1287962 12551867 := bstep (se 1 (by rfl) ⟨9413900, by rfl⟩ : syracuseStep 12551867 = 18827801) B18827801
theorem B10446889 : Blo 1287962 10446889 := bstep (se 2 (by rfl) ⟨3917583, by rfl⟩ : syracuseStep 10446889 = 7835167) B7835167
theorem B1288303 : Blo 1287962 1288303 := bstep (se 1 (by rfl) ⟨966227, by rfl⟩ : syracuseStep 1288303 = 1932455) B1932455
theorem B1288351 : Blo 1287962 1288351 := bstep (se 1 (by rfl) ⟨966263, by rfl⟩ : syracuseStep 1288351 = 1932527) B1932527
theorem B11012435 : Blo 1287962 11012435 := bstep (se 1 (by rfl) ⟨8259326, by rfl⟩ : syracuseStep 11012435 = 16518653) B16518653
theorem B2902409 : Blo 1287962 2902409 := bstep (se 2 (by rfl) ⟨1088403, by rfl⟩ : syracuseStep 2902409 = 2176807) B2176807
theorem B127175189 : Blo 1287962 127175189 := bstep (se 6 (by rfl) ⟨2980668, by rfl⟩ : syracuseStep 127175189 = 5961337) B5961337
theorem B1288987 : Blo 1287962 1288987 := bstep (se 1 (by rfl) ⟨966740, by rfl⟩ : syracuseStep 1288987 = 1933481) B1933481
theorem B4352831 : Blo 1287962 4352831 := bstep (se 1 (by rfl) ⟨3264623, by rfl⟩ : syracuseStep 4352831 = 6529247) B6529247
theorem B10448027 : Blo 1287962 10448027 := bstep (se 1 (by rfl) ⟨7836020, by rfl⟩ : syracuseStep 10448027 = 15672041) B15672041
theorem B4353371 : Blo 1287962 4353371 := bstep (se 1 (by rfl) ⟨3265028, by rfl⟩ : syracuseStep 4353371 = 6530057) B6530057
theorem B4353533 : Blo 1287962 4353533 := bstep (se 3 (by rfl) ⟨816287, by rfl⟩ : syracuseStep 4353533 = 1632575) B1632575
theorem B14684975 : Blo 1287962 14684975 := bstep (se 1 (by rfl) ⟨11013731, by rfl⟩ : syracuseStep 14684975 = 22027463) B22027463
theorem B55784699 : Blo 1287962 55784699 := bstep (se 1 (by rfl) ⟨41838524, by rfl⟩ : syracuseStep 55784699 = 83677049) B83677049
theorem B18568723 : Blo 1287962 18568723 := bstep (se 1 (by rfl) ⟨13926542, by rfl⟩ : syracuseStep 18568723 = 27853085) B27853085
theorem B10458827 : Blo 1287962 10458827 := bstep (se 1 (by rfl) ⟨7844120, by rfl⟩ : syracuseStep 10458827 = 15688241) B15688241
theorem B6190919 : Blo 1287962 6190919 := bstep (se 1 (by rfl) ⟨4643189, by rfl⟩ : syracuseStep 6190919 = 9286379) B9286379
theorem B14686433 : Blo 1287962 14686433 := bstep (se 2 (by rfl) ⟨5507412, by rfl⟩ : syracuseStep 14686433 = 11014825) B11014825
theorem B1932155 : Blo 1287962 1932155 := bstep (se 1 (by rfl) ⟨1449116, by rfl⟩ : syracuseStep 1932155 = 2898233) B2898233
theorem B1932281 : Blo 1287962 1932281 := bstep (se 2 (by rfl) ⟨724605, by rfl⟩ : syracuseStep 1932281 = 1449211) B1449211
theorem B9788525 : Blo 1287962 9788525 := bstep (se 3 (by rfl) ⟨1835348, by rfl⟩ : syracuseStep 9788525 = 3670697) B3670697
theorem B6528275 : Blo 1287962 6528275 := bstep (se 1 (by rfl) ⟨4896206, by rfl⟩ : syracuseStep 6528275 = 9792413) B9792413
theorem B12393911 : Blo 1287962 12393911 := bstep (se 1 (by rfl) ⟨9295433, by rfl⟩ : syracuseStep 12393911 = 18590867) B18590867
theorem B2899439 : Blo 1287962 2899439 := bstep (se 1 (by rfl) ⟨2174579, by rfl⟩ : syracuseStep 2899439 = 4349159) B4349159
theorem B5881339 : Blo 1287962 5881339 := bstep (se 1 (by rfl) ⟨4411004, by rfl⟩ : syracuseStep 5881339 = 8822009) B8822009
theorem B1449499 : Blo 1287962 1449499 := bstep (se 1 (by rfl) ⟨1087124, by rfl⟩ : syracuseStep 1449499 = 2174249) B2174249
theorem B2752127 : Blo 1287962 2752127 := bstep (se 1 (by rfl) ⟨2064095, by rfl⟩ : syracuseStep 2752127 = 4128191) B4128191
theorem B1933295 : Blo 1287962 1933295 := bstep (se 1 (by rfl) ⟨1449971, by rfl⟩ : syracuseStep 1933295 = 2899943) B2899943
theorem B135741779 : Blo 1287962 135741779 := bstep (se 1 (by rfl) ⟨101806334, by rfl⟩ : syracuseStep 135741779 = 203612669) B203612669
theorem B8258021 : Blo 1287962 8258021 := bstep (se 4 (by rfl) ⟨774189, by rfl⟩ : syracuseStep 8258021 = 1548379) B1548379
theorem B9789983 : Blo 1287962 9789983 := bstep (se 1 (by rfl) ⟨7342487, by rfl⟩ : syracuseStep 9789983 = 14684975) B14684975
theorem B6521471 : Blo 1287962 6521471 := bstep (se 1 (by rfl) ⟨4891103, by rfl⟩ : syracuseStep 6521471 = 9782207) B9782207
theorem B1934063 : Blo 1287962 1934063 := bstep (se 1 (by rfl) ⟨1450547, by rfl⟩ : syracuseStep 1934063 = 2901095) B2901095
theorem B33915995 : Blo 1287962 33915995 := bstep (se 1 (by rfl) ⟨25436996, by rfl⟩ : syracuseStep 33915995 = 50873993) B50873993
theorem B1377383 : Blo 1287962 1377383 := bstep (se 1 (by rfl) ⟨1033037, by rfl⟩ : syracuseStep 1377383 = 2066075) B2066075
theorem B6972551 : Blo 1287962 6972551 := bstep (se 1 (by rfl) ⟨5229413, by rfl⟩ : syracuseStep 6972551 = 10458827) B10458827
theorem B339133837 : Blo 1287962 339133837 := bstep (se 3 (by rfl) ⟨63587594, by rfl⟩ : syracuseStep 339133837 = 127175189) B127175189
theorem B9790955 : Blo 1287962 9790955 := bstep (se 1 (by rfl) ⟨7343216, by rfl⟩ : syracuseStep 9790955 = 14686433) B14686433
theorem B7341623 : Blo 1287962 7341623 := bstep (se 1 (by rfl) ⟨5506217, by rfl⟩ : syracuseStep 7341623 = 11012435) B11012435
theorem B1934939 : Blo 1287962 1934939 := bstep (se 1 (by rfl) ⟨1451204, by rfl⟩ : syracuseStep 1934939 = 2902409) B2902409
theorem B2901887 : Blo 1287962 2901887 := bstep (se 1 (by rfl) ⟨2176415, by rfl⟩ : syracuseStep 2901887 = 4352831) B4352831
theorem B1288103 : Blo 1287962 1288103 := bstep (se 1 (by rfl) ⟨966077, by rfl⟩ : syracuseStep 1288103 = 1932155) B1932155
theorem B7841785 : Blo 1287962 7841785 := bstep (se 2 (by rfl) ⟨2940669, by rfl⟩ : syracuseStep 7841785 = 5881339) B5881339
theorem B1288187 : Blo 1287962 1288187 := bstep (se 1 (by rfl) ⟨966140, by rfl⟩ : syracuseStep 1288187 = 1932281) B1932281
theorem B24758297 : Blo 1287962 24758297 := bstep (se 2 (by rfl) ⟨9284361, by rfl⟩ : syracuseStep 24758297 = 18568723) B18568723
theorem B6965351 : Blo 1287962 6965351 := bstep (se 1 (by rfl) ⟨5224013, by rfl⟩ : syracuseStep 6965351 = 10448027) B10448027
theorem B4352183 : Blo 1287962 4352183 := bstep (se 1 (by rfl) ⟨3264137, by rfl⟩ : syracuseStep 4352183 = 6528275) B6528275
theorem B2902247 : Blo 1287962 2902247 := bstep (se 1 (by rfl) ⟨2176685, by rfl⟩ : syracuseStep 2902247 = 4353371) B4353371
theorem B2902355 : Blo 1287962 2902355 := bstep (se 1 (by rfl) ⟨2176766, by rfl⟩ : syracuseStep 2902355 = 4353533) B4353533
theorem B1288863 : Blo 1287962 1288863 := bstep (se 1 (by rfl) ⟨966647, by rfl⟩ : syracuseStep 1288863 = 1933295) B1933295
theorem B13929185 : Blo 1287962 13929185 := bstep (se 2 (by rfl) ⟨5223444, by rfl⟩ : syracuseStep 13929185 = 10446889) B10446889
theorem B1288943 : Blo 1287962 1288943 := bstep (se 1 (by rfl) ⟨966707, by rfl⟩ : syracuseStep 1288943 = 1933415) B1933415
theorem B2173945 : Blo 1287962 2173945 := bstep (se 2 (by rfl) ⟨815229, by rfl⟩ : syracuseStep 2173945 = 1630459) B1630459
theorem B1289243 : Blo 1287962 1289243 := bstep (se 1 (by rfl) ⟨966932, by rfl⟩ : syracuseStep 1289243 = 1933865) B1933865
theorem B1289307 : Blo 1287962 1289307 := bstep (se 1 (by rfl) ⟨966980, by rfl⟩ : syracuseStep 1289307 = 1933961) B1933961
theorem B2174107 : Blo 1287962 2174107 := bstep (se 1 (by rfl) ⟨1630580, by rfl⟩ : syracuseStep 2174107 = 3261161) B3261161
theorem B1289467 : Blo 1287962 1289467 := bstep (se 1 (by rfl) ⟨967100, by rfl⟩ : syracuseStep 1289467 = 1934201) B1934201
theorem B1289499 : Blo 1287962 1289499 := bstep (se 1 (by rfl) ⟨967124, by rfl⟩ : syracuseStep 1289499 = 1934249) B1934249
theorem B1289663 : Blo 1287962 1289663 := bstep (se 1 (by rfl) ⟨967247, by rfl⟩ : syracuseStep 1289663 = 1934495) B1934495
theorem B1289775 : Blo 1287962 1289775 := bstep (se 1 (by rfl) ⟨967331, by rfl⟩ : syracuseStep 1289775 = 1934663) B1934663
theorem B8367911 : Blo 1287962 8367911 := bstep (se 1 (by rfl) ⟨6275933, by rfl⟩ : syracuseStep 8367911 = 12551867) B12551867
theorem B122302561 : Blo 1287962 122302561 := bstep (se 2 (by rfl) ⟨45863460, by rfl⟩ : syracuseStep 122302561 = 91726921) B91726921
theorem B24785513 : Blo 1287962 24785513 := bstep (se 2 (by rfl) ⟨9294567, by rfl⟩ : syracuseStep 24785513 = 18589135) B18589135
theorem B6525683 : Blo 1287962 6525683 := bstep (se 1 (by rfl) ⟨4894262, by rfl⟩ : syracuseStep 6525683 = 9788525) B9788525
theorem B8262607 : Blo 1287962 8262607 := bstep (se 1 (by rfl) ⟨6196955, by rfl⟩ : syracuseStep 8262607 = 12393911) B12393911
theorem B37189799 : Blo 1287962 37189799 := bstep (se 1 (by rfl) ⟨27892349, by rfl⟩ : syracuseStep 37189799 = 55784699) B55784699
theorem B4127279 : Blo 1287962 4127279 := bstep (se 1 (by rfl) ⟨3095459, by rfl⟩ : syracuseStep 4127279 = 6190919) B6190919
theorem B1932665 : Blo 1287962 1932665 := bstep (se 2 (by rfl) ⟨724749, by rfl⟩ : syracuseStep 1932665 = 1449499) B1449499
theorem B1932959 : Blo 1287962 1932959 := bstep (se 1 (by rfl) ⟨1449719, by rfl⟩ : syracuseStep 1932959 = 2899439) B2899439
theorem B1834751 : Blo 1287962 1834751 := bstep (se 1 (by rfl) ⟨1376063, by rfl⟩ : syracuseStep 1834751 = 2752127) B2752127
theorem B163070081 : Blo 1287962 163070081 := bstep (se 2 (by rfl) ⟨61151280, by rfl⟩ : syracuseStep 163070081 = 122302561) B122302561
theorem B5505347 : Blo 1287962 5505347 := bstep (se 1 (by rfl) ⟨4129010, by rfl⟩ : syracuseStep 5505347 = 8258021) B8258021
theorem B16523675 : Blo 1287962 16523675 := bstep (se 1 (by rfl) ⟨12392756, by rfl⟩ : syracuseStep 16523675 = 24785513) B24785513
theorem B4350455 : Blo 1287962 4350455 := bstep (se 1 (by rfl) ⟨3262841, by rfl⟩ : syracuseStep 4350455 = 6525683) B6525683
theorem B22610663 : Blo 1287962 22610663 := bstep (se 1 (by rfl) ⟨16957997, by rfl⟩ : syracuseStep 22610663 = 33915995) B33915995
theorem B1934591 : Blo 1287962 1934591 := bstep (se 1 (by rfl) ⟨1450943, by rfl⟩ : syracuseStep 1934591 = 2901887) B2901887
theorem B2901455 : Blo 1287962 2901455 := bstep (se 1 (by rfl) ⟨2176091, by rfl⟩ : syracuseStep 2901455 = 4352183) B4352183
theorem B1934831 : Blo 1287962 1934831 := bstep (se 1 (by rfl) ⟨1451123, by rfl⟩ : syracuseStep 1934831 = 2902247) B2902247
theorem B1934903 : Blo 1287962 1934903 := bstep (se 1 (by rfl) ⟨1451177, by rfl⟩ : syracuseStep 1934903 = 2902355) B2902355
theorem B4892669 : Blo 1287962 4892669 := bstep (se 3 (by rfl) ⟨917375, by rfl⟩ : syracuseStep 4892669 = 1834751) B1834751
theorem B1288443 : Blo 1287962 1288443 := bstep (se 1 (by rfl) ⟨966332, by rfl⟩ : syracuseStep 1288443 = 1932665) B1932665
theorem B1288639 : Blo 1287962 1288639 := bstep (se 1 (by rfl) ⟨966479, by rfl⟩ : syracuseStep 1288639 = 1932959) B1932959
theorem B10455713 : Blo 1287962 10455713 := bstep (se 2 (by rfl) ⟨3920892, by rfl⟩ : syracuseStep 10455713 = 7841785) B7841785
theorem B3673021 : Blo 1287962 3673021 := bstep (se 3 (by rfl) ⟨688691, by rfl⟩ : syracuseStep 3673021 = 1377383) B1377383
theorem B1289375 : Blo 1287962 1289375 := bstep (se 1 (by rfl) ⟨967031, by rfl⟩ : syracuseStep 1289375 = 1934063) B1934063
theorem B4648367 : Blo 1287962 4648367 := bstep (se 1 (by rfl) ⟨3486275, by rfl⟩ : syracuseStep 4648367 = 6972551) B6972551
theorem B4894415 : Blo 1287962 4894415 := bstep (se 1 (by rfl) ⟨3670811, by rfl⟩ : syracuseStep 4894415 = 7341623) B7341623
theorem B1289959 : Blo 1287962 1289959 := bstep (se 1 (by rfl) ⟨967469, by rfl⟩ : syracuseStep 1289959 = 1934939) B1934939
theorem B24793199 : Blo 1287962 24793199 := bstep (se 1 (by rfl) ⟨18594899, by rfl⟩ : syracuseStep 24793199 = 37189799) B37189799
theorem B11006077 : Blo 1287962 11006077 := bstep (se 3 (by rfl) ⟨2063639, by rfl⟩ : syracuseStep 11006077 = 4127279) B4127279
theorem B9286123 : Blo 1287962 9286123 := bstep (se 1 (by rfl) ⟨6964592, by rfl⟩ : syracuseStep 9286123 = 13929185) B13929185
theorem B452178449 : Blo 1287962 452178449 := bstep (se 2 (by rfl) ⟨169566918, by rfl⟩ : syracuseStep 452178449 = 339133837) B339133837
theorem B90494519 : Blo 1287962 90494519 := bstep (se 1 (by rfl) ⟨67870889, by rfl⟩ : syracuseStep 90494519 = 135741779) B135741779
theorem B6526655 : Blo 1287962 6526655 := bstep (se 1 (by rfl) ⟨4894991, by rfl⟩ : syracuseStep 6526655 = 9789983) B9789983
theorem B4347647 : Blo 1287962 4347647 := bstep (se 1 (by rfl) ⟨3260735, by rfl⟩ : syracuseStep 4347647 = 6521471) B6521471
theorem B6527303 : Blo 1287962 6527303 := bstep (se 1 (by rfl) ⟨4895477, by rfl⟩ : syracuseStep 6527303 = 9790955) B9790955
theorem B11016809 : Blo 1287962 11016809 := bstep (se 2 (by rfl) ⟨4131303, by rfl⟩ : syracuseStep 11016809 = 8262607) B8262607
theorem B2898593 : Blo 1287962 2898593 := bstep (se 2 (by rfl) ⟨1086972, by rfl⟩ : syracuseStep 2898593 = 2173945) B2173945
theorem B16505531 : Blo 1287962 16505531 := bstep (se 1 (by rfl) ⟨12379148, by rfl⟩ : syracuseStep 16505531 = 24758297) B24758297
theorem B4643567 : Blo 1287962 4643567 := bstep (se 1 (by rfl) ⟨3482675, by rfl⟩ : syracuseStep 4643567 = 6965351) B6965351
theorem B2898809 : Blo 1287962 2898809 := bstep (se 2 (by rfl) ⟨1087053, by rfl⟩ : syracuseStep 2898809 = 2174107) B2174107
theorem B5578607 : Blo 1287962 5578607 := bstep (se 1 (by rfl) ⟨4183955, by rfl⟩ : syracuseStep 5578607 = 8367911) B8367911
theorem B3670231 : Blo 1287962 3670231 := bstep (se 1 (by rfl) ⟨2752673, by rfl⟩ : syracuseStep 3670231 = 5505347) B5505347
theorem B2900303 : Blo 1287962 2900303 := bstep (se 1 (by rfl) ⟨2175227, by rfl⟩ : syracuseStep 2900303 = 4350455) B4350455
theorem B15073775 : Blo 1287962 15073775 := bstep (se 1 (by rfl) ⟨11305331, by rfl⟩ : syracuseStep 15073775 = 22610663) B22610663
theorem B1934303 : Blo 1287962 1934303 := bstep (se 1 (by rfl) ⟨1450727, by rfl⟩ : syracuseStep 1934303 = 2901455) B2901455
theorem B4351103 : Blo 1287962 4351103 := bstep (se 1 (by rfl) ⟨3263327, by rfl⟩ : syracuseStep 4351103 = 6526655) B6526655
theorem B3261779 : Blo 1287962 3261779 := bstep (se 1 (by rfl) ⟨2446334, by rfl⟩ : syracuseStep 3261779 = 4892669) B4892669
theorem B4351535 : Blo 1287962 4351535 := bstep (se 1 (by rfl) ⟨3263651, by rfl⟩ : syracuseStep 4351535 = 6527303) B6527303
theorem B11003687 : Blo 1287962 11003687 := bstep (se 1 (by rfl) ⟨8252765, by rfl⟩ : syracuseStep 11003687 = 16505531) B16505531
theorem B3098911 : Blo 1287962 3098911 := bstep (se 1 (by rfl) ⟨2324183, by rfl⟩ : syracuseStep 3098911 = 4648367) B4648367
theorem B3262943 : Blo 1287962 3262943 := bstep (se 1 (by rfl) ⟨2447207, by rfl⟩ : syracuseStep 3262943 = 4894415) B4894415
theorem B14674769 : Blo 1287962 14674769 := bstep (se 2 (by rfl) ⟨5503038, by rfl⟩ : syracuseStep 14674769 = 11006077) B11006077
theorem B301452299 : Blo 1287962 301452299 := bstep (se 1 (by rfl) ⟨226089224, by rfl⟩ : syracuseStep 301452299 = 452178449) B452178449
theorem B965274869 : Blo 1287962 965274869 := bstep (se 5 (by rfl) ⟨45247259, by rfl⟩ : syracuseStep 965274869 = 90494519) B90494519
theorem B12381497 : Blo 1287962 12381497 := bstep (se 2 (by rfl) ⟨4643061, by rfl⟩ : syracuseStep 12381497 = 9286123) B9286123
theorem B1289727 : Blo 1287962 1289727 := bstep (se 1 (by rfl) ⟨967295, by rfl⟩ : syracuseStep 1289727 = 1934591) B1934591
theorem B1289887 : Blo 1287962 1289887 := bstep (se 1 (by rfl) ⟨967415, by rfl⟩ : syracuseStep 1289887 = 1934831) B1934831
theorem B1289935 : Blo 1287962 1289935 := bstep (se 1 (by rfl) ⟨967451, by rfl⟩ : syracuseStep 1289935 = 1934903) B1934903
theorem B7344539 : Blo 1287962 7344539 := bstep (se 1 (by rfl) ⟨5508404, by rfl⟩ : syracuseStep 7344539 = 11016809) B11016809
theorem B16528799 : Blo 1287962 16528799 := bstep (se 1 (by rfl) ⟨12396599, by rfl⟩ : syracuseStep 16528799 = 24793199) B24793199
theorem B108713387 : Blo 1287962 108713387 := bstep (se 1 (by rfl) ⟨81535040, by rfl⟩ : syracuseStep 108713387 = 163070081) B163070081
theorem B11015783 : Blo 1287962 11015783 := bstep (se 1 (by rfl) ⟨8261837, by rfl⟩ : syracuseStep 11015783 = 16523675) B16523675
theorem B2898431 : Blo 1287962 2898431 := bstep (se 1 (by rfl) ⟨2173823, by rfl⟩ : syracuseStep 2898431 = 4347647) B4347647
theorem B4897361 : Blo 1287962 4897361 := bstep (se 2 (by rfl) ⟨1836510, by rfl⟩ : syracuseStep 4897361 = 3673021) B3673021
theorem B1932395 : Blo 1287962 1932395 := bstep (se 1 (by rfl) ⟨1449296, by rfl⟩ : syracuseStep 1932395 = 2898593) B2898593
theorem B6970475 : Blo 1287962 6970475 := bstep (se 1 (by rfl) ⟨5227856, by rfl⟩ : syracuseStep 6970475 = 10455713) B10455713
theorem B3095711 : Blo 1287962 3095711 := bstep (se 1 (by rfl) ⟨2321783, by rfl⟩ : syracuseStep 3095711 = 4643567) B4643567
theorem B1932539 : Blo 1287962 1932539 := bstep (se 1 (by rfl) ⟨1449404, by rfl⟩ : syracuseStep 1932539 = 2898809) B2898809
theorem B3719071 : Blo 1287962 3719071 := bstep (se 1 (by rfl) ⟨2789303, by rfl⟩ : syracuseStep 3719071 = 5578607) B5578607
theorem B1933535 : Blo 1287962 1933535 := bstep (se 1 (by rfl) ⟨1450151, by rfl⟩ : syracuseStep 1933535 = 2900303) B2900303
theorem B2900735 : Blo 1287962 2900735 := bstep (se 1 (by rfl) ⟨2175551, by rfl⟩ : syracuseStep 2900735 = 4351103) B4351103
theorem B11019199 : Blo 1287962 11019199 := bstep (se 1 (by rfl) ⟨8264399, by rfl⟩ : syracuseStep 11019199 = 16528799) B16528799
theorem B2901023 : Blo 1287962 2901023 := bstep (se 1 (by rfl) ⟨2175767, by rfl⟩ : syracuseStep 2901023 = 4351535) B4351535
theorem B9783179 : Blo 1287962 9783179 := bstep (se 1 (by rfl) ⟨7337384, by rfl⟩ : syracuseStep 9783179 = 14674769) B14674769
theorem B200968199 : Blo 1287962 200968199 := bstep (se 1 (by rfl) ⟨150726149, by rfl⟩ : syracuseStep 200968199 = 301452299) B301452299
theorem B1288263 : Blo 1287962 1288263 := bstep (se 1 (by rfl) ⟨966197, by rfl⟩ : syracuseStep 1288263 = 1932395) B1932395
theorem B4646983 : Blo 1287962 4646983 := bstep (se 1 (by rfl) ⟨3485237, by rfl⟩ : syracuseStep 4646983 = 6970475) B6970475
theorem B643516579 : Blo 1287962 643516579 := bstep (se 1 (by rfl) ⟨482637434, by rfl⟩ : syracuseStep 643516579 = 965274869) B965274869
theorem B1288359 : Blo 1287962 1288359 := bstep (se 1 (by rfl) ⟨966269, by rfl⟩ : syracuseStep 1288359 = 1932539) B1932539
theorem B4958761 : Blo 1287962 4958761 := bstep (se 2 (by rfl) ⟨1859535, by rfl⟩ : syracuseStep 4958761 = 3719071) B3719071
theorem B4893641 : Blo 1287962 4893641 := bstep (se 2 (by rfl) ⟨1835115, by rfl⟩ : syracuseStep 4893641 = 3670231) B3670231
theorem B4131881 : Blo 1287962 4131881 := bstep (se 2 (by rfl) ⟨1549455, by rfl⟩ : syracuseStep 4131881 = 3098911) B3098911
theorem B1289535 : Blo 1287962 1289535 := bstep (se 1 (by rfl) ⟨967151, by rfl⟩ : syracuseStep 1289535 = 1934303) B1934303
theorem B2174519 : Blo 1287962 2174519 := bstep (se 1 (by rfl) ⟨1630889, by rfl⟩ : syracuseStep 2174519 = 3261779) B3261779
theorem B7343855 : Blo 1287962 7343855 := bstep (se 1 (by rfl) ⟨5507891, by rfl⟩ : syracuseStep 7343855 = 11015783) B11015783
theorem B289902365 : Blo 1287962 289902365 := bstep (se 3 (by rfl) ⟨54356693, by rfl⟩ : syracuseStep 289902365 = 108713387) B108713387
theorem B7335791 : Blo 1287962 7335791 := bstep (se 1 (by rfl) ⟨5501843, by rfl⟩ : syracuseStep 7335791 = 11003687) B11003687
theorem B2175295 : Blo 1287962 2175295 := bstep (se 1 (by rfl) ⟨1631471, by rfl⟩ : syracuseStep 2175295 = 3262943) B3262943
theorem B3264907 : Blo 1287962 3264907 := bstep (se 1 (by rfl) ⟨2448680, by rfl⟩ : syracuseStep 3264907 = 4897361) B4897361
theorem B8254331 : Blo 1287962 8254331 := bstep (se 1 (by rfl) ⟨6190748, by rfl⟩ : syracuseStep 8254331 = 12381497) B12381497
theorem B4896359 : Blo 1287962 4896359 := bstep (se 1 (by rfl) ⟨3672269, by rfl⟩ : syracuseStep 4896359 = 7344539) B7344539
theorem B10049183 : Blo 1287962 10049183 := bstep (se 1 (by rfl) ⟨7536887, by rfl⟩ : syracuseStep 10049183 = 15073775) B15073775
theorem B1932287 : Blo 1287962 1932287 := bstep (se 1 (by rfl) ⟨1449215, by rfl⟩ : syracuseStep 1932287 = 2898431) B2898431
theorem B2063807 : Blo 1287962 2063807 := bstep (se 1 (by rfl) ⟨1547855, by rfl⟩ : syracuseStep 2063807 = 3095711) B3095711
theorem B2900393 : Blo 1287962 2900393 := bstep (se 2 (by rfl) ⟨1087647, by rfl⟩ : syracuseStep 2900393 = 2175295) B2175295
theorem B1933823 : Blo 1287962 1933823 := bstep (se 1 (by rfl) ⟨1450367, by rfl⟩ : syracuseStep 1933823 = 2900735) B2900735
theorem B1934015 : Blo 1287962 1934015 := bstep (se 1 (by rfl) ⟨1450511, by rfl⟩ : syracuseStep 1934015 = 2901023) B2901023
theorem B6611681 : Blo 1287962 6611681 := bstep (se 2 (by rfl) ⟨2479380, by rfl⟩ : syracuseStep 6611681 = 4958761) B4958761
theorem B3432088421 : Blo 1287962 3432088421 := bstep (se 4 (by rfl) ⟨321758289, by rfl⟩ : syracuseStep 3432088421 = 643516579) B643516579
theorem B6522119 : Blo 1287962 6522119 := bstep (se 1 (by rfl) ⟨4891589, by rfl⟩ : syracuseStep 6522119 = 9783179) B9783179
theorem B3262427 : Blo 1287962 3262427 := bstep (se 1 (by rfl) ⟨2446820, by rfl⟩ : syracuseStep 3262427 = 4893641) B4893641
theorem B1288191 : Blo 1287962 1288191 := bstep (se 1 (by rfl) ⟨966143, by rfl⟩ : syracuseStep 1288191 = 1932287) B1932287
theorem B2754587 : Blo 1287962 2754587 := bstep (se 1 (by rfl) ⟨2065940, by rfl⟩ : syracuseStep 2754587 = 4131881) B4131881
theorem B193268243 : Blo 1287962 193268243 := bstep (se 1 (by rfl) ⟨144951182, by rfl⟩ : syracuseStep 193268243 = 289902365) B289902365
theorem B6195977 : Blo 1287962 6195977 := bstep (se 2 (by rfl) ⟨2323491, by rfl⟩ : syracuseStep 6195977 = 4646983) B4646983
theorem B1289023 : Blo 1287962 1289023 := bstep (se 1 (by rfl) ⟨966767, by rfl⟩ : syracuseStep 1289023 = 1933535) B1933535
theorem B4353209 : Blo 1287962 4353209 := bstep (se 2 (by rfl) ⟨1632453, by rfl⟩ : syracuseStep 4353209 = 3264907) B3264907
theorem B3264239 : Blo 1287962 3264239 := bstep (se 1 (by rfl) ⟨2448179, by rfl⟩ : syracuseStep 3264239 = 4896359) B4896359
theorem B14692265 : Blo 1287962 14692265 := bstep (se 2 (by rfl) ⟨5509599, by rfl⟩ : syracuseStep 14692265 = 11019199) B11019199
theorem B4895903 : Blo 1287962 4895903 := bstep (se 1 (by rfl) ⟨3671927, by rfl⟩ : syracuseStep 4895903 = 7343855) B7343855
theorem B5502887 : Blo 1287962 5502887 := bstep (se 1 (by rfl) ⟨4127165, by rfl⟩ : syracuseStep 5502887 = 8254331) B8254331
theorem B6699455 : Blo 1287962 6699455 := bstep (se 1 (by rfl) ⟨5024591, by rfl⟩ : syracuseStep 6699455 = 10049183) B10049183
theorem B133978799 : Blo 1287962 133978799 := bstep (se 1 (by rfl) ⟨100484099, by rfl⟩ : syracuseStep 133978799 = 200968199) B200968199
theorem B1375871 : Blo 1287962 1375871 := bstep (se 1 (by rfl) ⟨1031903, by rfl⟩ : syracuseStep 1375871 = 2063807) B2063807
theorem B1449679 : Blo 1287962 1449679 := bstep (se 1 (by rfl) ⟨1087259, by rfl⟩ : syracuseStep 1449679 = 2174519) B2174519
theorem B4890527 : Blo 1287962 4890527 := bstep (se 1 (by rfl) ⟨3667895, by rfl⟩ : syracuseStep 4890527 = 7335791) B7335791
theorem B1933595 : Blo 1287962 1933595 := bstep (se 1 (by rfl) ⟨1450196, by rfl⟩ : syracuseStep 1933595 = 2900393) B2900393
theorem B4407787 : Blo 1287962 4407787 := bstep (se 1 (by rfl) ⟨3305840, by rfl⟩ : syracuseStep 4407787 = 6611681) B6611681
theorem B2288058947 : Blo 1287962 2288058947 := bstep (se 1 (by rfl) ⟨1716044210, by rfl⟩ : syracuseStep 2288058947 = 3432088421) B3432088421
theorem B4466303 : Blo 1287962 4466303 := bstep (se 1 (by rfl) ⟨3349727, by rfl⟩ : syracuseStep 4466303 = 6699455) B6699455
theorem B128845495 : Blo 1287962 128845495 := bstep (se 1 (by rfl) ⟨96634121, by rfl⟩ : syracuseStep 128845495 = 193268243) B193268243
theorem B89319199 : Blo 1287962 89319199 := bstep (se 1 (by rfl) ⟨66989399, by rfl⟩ : syracuseStep 89319199 = 133978799) B133978799
theorem B4130651 : Blo 1287962 4130651 := bstep (se 1 (by rfl) ⟨3097988, by rfl⟩ : syracuseStep 4130651 = 6195977) B6195977
theorem B2902139 : Blo 1287962 2902139 := bstep (se 1 (by rfl) ⟨2176604, by rfl⟩ : syracuseStep 2902139 = 4353209) B4353209
theorem B1289215 : Blo 1287962 1289215 := bstep (se 1 (by rfl) ⟨966911, by rfl⟩ : syracuseStep 1289215 = 1933823) B1933823
theorem B1289343 : Blo 1287962 1289343 := bstep (se 1 (by rfl) ⟨967007, by rfl⟩ : syracuseStep 1289343 = 1934015) B1934015
theorem B3263935 : Blo 1287962 3263935 := bstep (se 1 (by rfl) ⟨2447951, by rfl⟩ : syracuseStep 3263935 = 4895903) B4895903
theorem B2174951 : Blo 1287962 2174951 := bstep (se 1 (by rfl) ⟨1631213, by rfl⟩ : syracuseStep 2174951 = 3262427) B3262427
theorem B2176159 : Blo 1287962 2176159 := bstep (se 1 (by rfl) ⟨1632119, by rfl⟩ : syracuseStep 2176159 = 3264239) B3264239
theorem B9794843 : Blo 1287962 9794843 := bstep (se 1 (by rfl) ⟨7346132, by rfl⟩ : syracuseStep 9794843 = 14692265) B14692265
theorem B7345565 : Blo 1287962 7345565 := bstep (se 3 (by rfl) ⟨1377293, by rfl⟩ : syracuseStep 7345565 = 2754587) B2754587
theorem B4348079 : Blo 1287962 4348079 := bstep (se 1 (by rfl) ⟨3261059, by rfl⟩ : syracuseStep 4348079 = 6522119) B6522119
theorem B3668591 : Blo 1287962 3668591 := bstep (se 1 (by rfl) ⟨2751443, by rfl⟩ : syracuseStep 3668591 = 5502887) B5502887
theorem B3668989 : Blo 1287962 3668989 := bstep (se 3 (by rfl) ⟨687935, by rfl⟩ : syracuseStep 3668989 = 1375871) B1375871
theorem B1932905 : Blo 1287962 1932905 := bstep (se 2 (by rfl) ⟨724839, by rfl⟩ : syracuseStep 1932905 = 1449679) B1449679
theorem B3260351 : Blo 1287962 3260351 := bstep (se 1 (by rfl) ⟨2445263, by rfl⟩ : syracuseStep 3260351 = 4890527) B4890527
theorem B6529895 : Blo 1287962 6529895 := bstep (se 1 (by rfl) ⟨4897421, by rfl⟩ : syracuseStep 6529895 = 9794843) B9794843
theorem B2753767 : Blo 1287962 2753767 := bstep (se 1 (by rfl) ⟨2065325, by rfl⟩ : syracuseStep 2753767 = 4130651) B4130651
theorem B4891985 : Blo 1287962 4891985 := bstep (se 2 (by rfl) ⟨1834494, by rfl⟩ : syracuseStep 4891985 = 3668989) B3668989
theorem B1934759 : Blo 1287962 1934759 := bstep (se 1 (by rfl) ⟨1451069, by rfl⟩ : syracuseStep 1934759 = 2902139) B2902139
theorem B2901545 : Blo 1287962 2901545 := bstep (se 2 (by rfl) ⟨1088079, by rfl⟩ : syracuseStep 2901545 = 2176159) B2176159
theorem B4351913 : Blo 1287962 4351913 := bstep (se 2 (by rfl) ⟨1631967, by rfl⟩ : syracuseStep 4351913 = 3263935) B3263935
theorem B1288603 : Blo 1287962 1288603 := bstep (se 1 (by rfl) ⟨966452, by rfl⟩ : syracuseStep 1288603 = 1932905) B1932905
theorem B2173567 : Blo 1287962 2173567 := bstep (se 1 (by rfl) ⟨1630175, by rfl⟩ : syracuseStep 2173567 = 3260351) B3260351
theorem B1289063 : Blo 1287962 1289063 := bstep (se 1 (by rfl) ⟨966797, by rfl⟩ : syracuseStep 1289063 = 1933595) B1933595
theorem B5877049 : Blo 1287962 5877049 := bstep (se 2 (by rfl) ⟨2203893, by rfl⟩ : syracuseStep 5877049 = 4407787) B4407787
theorem B2977535 : Blo 1287962 2977535 := bstep (se 1 (by rfl) ⟨2233151, by rfl⟩ : syracuseStep 2977535 = 4466303) B4466303
theorem B2445727 : Blo 1287962 2445727 := bstep (se 1 (by rfl) ⟨1834295, by rfl⟩ : syracuseStep 2445727 = 3668591) B3668591
theorem B119092265 : Blo 1287962 119092265 := bstep (se 2 (by rfl) ⟨44659599, by rfl⟩ : syracuseStep 119092265 = 89319199) B89319199
theorem B1525372631 : Blo 1287962 1525372631 := bstep (se 1 (by rfl) ⟨1144029473, by rfl⟩ : syracuseStep 1525372631 = 2288058947) B2288058947
theorem B4897043 : Blo 1287962 4897043 := bstep (se 1 (by rfl) ⟨3672782, by rfl⟩ : syracuseStep 4897043 = 7345565) B7345565
theorem B687175973 : Blo 1287962 687175973 := bstep (se 4 (by rfl) ⟨64422747, by rfl⟩ : syracuseStep 687175973 = 128845495) B128845495
theorem B2898719 : Blo 1287962 2898719 := bstep (se 1 (by rfl) ⟨2174039, by rfl⟩ : syracuseStep 2898719 = 4348079) B4348079
theorem B1449967 : Blo 1287962 1449967 := bstep (se 1 (by rfl) ⟨1087475, by rfl⟩ : syracuseStep 1449967 = 2174951) B2174951
theorem B3260969 : Blo 1287962 3260969 := bstep (se 2 (by rfl) ⟨1222863, by rfl⟩ : syracuseStep 3260969 = 2445727) B2445727
theorem B3261323 : Blo 1287962 3261323 := bstep (se 1 (by rfl) ⟨2445992, by rfl⟩ : syracuseStep 3261323 = 4891985) B4891985
theorem B1934363 : Blo 1287962 1934363 := bstep (se 1 (by rfl) ⟨1450772, by rfl⟩ : syracuseStep 1934363 = 2901545) B2901545
theorem B1016915087 : Blo 1287962 1016915087 := bstep (se 1 (by rfl) ⟨762686315, by rfl⟩ : syracuseStep 1016915087 = 1525372631) B1525372631
theorem B2901275 : Blo 1287962 2901275 := bstep (se 1 (by rfl) ⟨2175956, by rfl⟩ : syracuseStep 2901275 = 4351913) B4351913
theorem B3671689 : Blo 1287962 3671689 := bstep (se 2 (by rfl) ⟨1376883, by rfl⟩ : syracuseStep 3671689 = 2753767) B2753767
theorem B1985023 : Blo 1287962 1985023 := bstep (se 1 (by rfl) ⟨1488767, by rfl⟩ : syracuseStep 1985023 = 2977535) B2977535
theorem B4353263 : Blo 1287962 4353263 := bstep (se 1 (by rfl) ⟨3264947, by rfl⟩ : syracuseStep 4353263 = 6529895) B6529895
theorem B1289839 : Blo 1287962 1289839 := bstep (se 1 (by rfl) ⟨967379, by rfl⟩ : syracuseStep 1289839 = 1934759) B1934759
theorem B3264695 : Blo 1287962 3264695 := bstep (se 1 (by rfl) ⟨2448521, by rfl⟩ : syracuseStep 3264695 = 4897043) B4897043
theorem B458117315 : Blo 1287962 458117315 := bstep (se 1 (by rfl) ⟨343587986, by rfl⟩ : syracuseStep 458117315 = 687175973) B687175973
theorem B7836065 : Blo 1287962 7836065 := bstep (se 2 (by rfl) ⟨2938524, by rfl⟩ : syracuseStep 7836065 = 5877049) B5877049
theorem B79394843 : Blo 1287962 79394843 := bstep (se 1 (by rfl) ⟨59546132, by rfl⟩ : syracuseStep 79394843 = 119092265) B119092265
theorem B2898089 : Blo 1287962 2898089 := bstep (se 2 (by rfl) ⟨1086783, by rfl⟩ : syracuseStep 2898089 = 2173567) B2173567
theorem B1932479 : Blo 1287962 1932479 := bstep (se 1 (by rfl) ⟨1449359, by rfl⟩ : syracuseStep 1932479 = 2898719) B2898719
theorem B1933289 : Blo 1287962 1933289 := bstep (se 2 (by rfl) ⟨724983, by rfl⟩ : syracuseStep 1933289 = 1449967) B1449967
theorem B1934183 : Blo 1287962 1934183 := bstep (se 1 (by rfl) ⟨1450637, by rfl⟩ : syracuseStep 1934183 = 2901275) B2901275
theorem B52929895 : Blo 1287962 52929895 := bstep (se 1 (by rfl) ⟨39697421, by rfl⟩ : syracuseStep 52929895 = 79394843) B79394843
theorem B1288319 : Blo 1287962 1288319 := bstep (se 1 (by rfl) ⟨966239, by rfl⟩ : syracuseStep 1288319 = 1932479) B1932479
theorem B2902175 : Blo 1287962 2902175 := bstep (se 1 (by rfl) ⟨2176631, by rfl⟩ : syracuseStep 2902175 = 4353263) B4353263
theorem B1288859 : Blo 1287962 1288859 := bstep (se 1 (by rfl) ⟨966644, by rfl⟩ : syracuseStep 1288859 = 1933289) B1933289
theorem B10586789 : Blo 1287962 10586789 := bstep (se 4 (by rfl) ⟨992511, by rfl⟩ : syracuseStep 10586789 = 1985023) B1985023
theorem B2173979 : Blo 1287962 2173979 := bstep (se 1 (by rfl) ⟨1630484, by rfl⟩ : syracuseStep 2173979 = 3260969) B3260969
theorem B2174215 : Blo 1287962 2174215 := bstep (se 1 (by rfl) ⟨1630661, by rfl⟩ : syracuseStep 2174215 = 3261323) B3261323
theorem B1289575 : Blo 1287962 1289575 := bstep (se 1 (by rfl) ⟨967181, by rfl⟩ : syracuseStep 1289575 = 1934363) B1934363
theorem B4895585 : Blo 1287962 4895585 := bstep (se 2 (by rfl) ⟨1835844, by rfl⟩ : syracuseStep 4895585 = 3671689) B3671689
theorem B2176463 : Blo 1287962 2176463 := bstep (se 1 (by rfl) ⟨1632347, by rfl⟩ : syracuseStep 2176463 = 3264695) B3264695
theorem B305411543 : Blo 1287962 305411543 := bstep (se 1 (by rfl) ⟨229058657, by rfl⟩ : syracuseStep 305411543 = 458117315) B458117315
theorem B5224043 : Blo 1287962 5224043 := bstep (se 1 (by rfl) ⟨3918032, by rfl⟩ : syracuseStep 5224043 = 7836065) B7836065
theorem B677943391 : Blo 1287962 677943391 := bstep (se 1 (by rfl) ⟨508457543, by rfl⟩ : syracuseStep 677943391 = 1016915087) B1016915087
theorem B1932059 : Blo 1287962 1932059 := bstep (se 1 (by rfl) ⟨1449044, by rfl⟩ : syracuseStep 1932059 = 2898089) B2898089
theorem B1450975 : Blo 1287962 1450975 := bstep (se 1 (by rfl) ⟨1088231, by rfl⟩ : syracuseStep 1450975 = 2176463) B2176463
theorem B3482695 : Blo 1287962 3482695 := bstep (se 1 (by rfl) ⟨2612021, by rfl⟩ : syracuseStep 3482695 = 5224043) B5224043
theorem B1934783 : Blo 1287962 1934783 := bstep (se 1 (by rfl) ⟨1451087, by rfl⟩ : syracuseStep 1934783 = 2902175) B2902175
theorem B1288039 : Blo 1287962 1288039 := bstep (se 1 (by rfl) ⟨966029, by rfl⟩ : syracuseStep 1288039 = 1932059) B1932059
theorem B903924521 : Blo 1287962 903924521 := bstep (se 2 (by rfl) ⟨338971695, by rfl⟩ : syracuseStep 903924521 = 677943391) B677943391
theorem B3263723 : Blo 1287962 3263723 := bstep (se 1 (by rfl) ⟨2447792, by rfl⟩ : syracuseStep 3263723 = 4895585) B4895585
theorem B1289455 : Blo 1287962 1289455 := bstep (se 1 (by rfl) ⟨967091, by rfl⟩ : syracuseStep 1289455 = 1934183) B1934183
theorem B203607695 : Blo 1287962 203607695 := bstep (se 1 (by rfl) ⟨152705771, by rfl⟩ : syracuseStep 203607695 = 305411543) B305411543
theorem B7057859 : Blo 1287962 7057859 := bstep (se 1 (by rfl) ⟨5293394, by rfl⟩ : syracuseStep 7057859 = 10586789) B10586789
theorem B2898953 : Blo 1287962 2898953 := bstep (se 2 (by rfl) ⟨1087107, by rfl⟩ : syracuseStep 2898953 = 2174215) B2174215
theorem B70573193 : Blo 1287962 70573193 := bstep (se 2 (by rfl) ⟨26464947, by rfl⟩ : syracuseStep 70573193 = 52929895) B52929895
theorem B1449319 : Blo 1287962 1449319 := bstep (se 1 (by rfl) ⟨1086989, by rfl⟩ : syracuseStep 1449319 = 2173979) B2173979
theorem B1934633 : Blo 1287962 1934633 := bstep (se 2 (by rfl) ⟨725487, by rfl⟩ : syracuseStep 1934633 = 1450975) B1450975
theorem B47048795 : Blo 1287962 47048795 := bstep (se 1 (by rfl) ⟨35286596, by rfl⟩ : syracuseStep 47048795 = 70573193) B70573193
theorem B18574373 : Blo 1287962 18574373 := bstep (se 4 (by rfl) ⟨1741347, by rfl⟩ : syracuseStep 18574373 = 3482695) B3482695
theorem B1289855 : Blo 1287962 1289855 := bstep (se 1 (by rfl) ⟨967391, by rfl⟩ : syracuseStep 1289855 = 1934783) B1934783
theorem B18820957 : Blo 1287962 18820957 := bstep (se 3 (by rfl) ⟨3528929, by rfl⟩ : syracuseStep 18820957 = 7057859) B7057859
theorem B602616347 : Blo 1287962 602616347 := bstep (se 1 (by rfl) ⟨451962260, by rfl⟩ : syracuseStep 602616347 = 903924521) B903924521
theorem B2175815 : Blo 1287962 2175815 := bstep (se 1 (by rfl) ⟨1631861, by rfl⟩ : syracuseStep 2175815 = 3263723) B3263723
theorem B135738463 : Blo 1287962 135738463 := bstep (se 1 (by rfl) ⟨101803847, by rfl⟩ : syracuseStep 135738463 = 203607695) B203607695
theorem B1932425 : Blo 1287962 1932425 := bstep (se 2 (by rfl) ⟨724659, by rfl⟩ : syracuseStep 1932425 = 1449319) B1449319
theorem B1932635 : Blo 1287962 1932635 := bstep (se 1 (by rfl) ⟨1449476, by rfl⟩ : syracuseStep 1932635 = 2898953) B2898953
theorem B401744231 : Blo 1287962 401744231 := bstep (se 1 (by rfl) ⟨301308173, by rfl⟩ : syracuseStep 401744231 = 602616347) B602616347
theorem B1450543 : Blo 1287962 1450543 := bstep (se 1 (by rfl) ⟨1087907, by rfl⟩ : syracuseStep 1450543 = 2175815) B2175815
theorem B1288283 : Blo 1287962 1288283 := bstep (se 1 (by rfl) ⟨966212, by rfl⟩ : syracuseStep 1288283 = 1932425) B1932425
theorem B1288423 : Blo 1287962 1288423 := bstep (se 1 (by rfl) ⟨966317, by rfl⟩ : syracuseStep 1288423 = 1932635) B1932635
theorem B25094609 : Blo 1287962 25094609 := bstep (se 2 (by rfl) ⟨9410478, by rfl⟩ : syracuseStep 25094609 = 18820957) B18820957
theorem B1289755 : Blo 1287962 1289755 := bstep (se 1 (by rfl) ⟨967316, by rfl⟩ : syracuseStep 1289755 = 1934633) B1934633
theorem B12382915 : Blo 1287962 12382915 := bstep (se 1 (by rfl) ⟨9287186, by rfl⟩ : syracuseStep 12382915 = 18574373) B18574373
theorem B31365863 : Blo 1287962 31365863 := bstep (se 1 (by rfl) ⟨23524397, by rfl⟩ : syracuseStep 31365863 = 47048795) B47048795
theorem B180984617 : Blo 1287962 180984617 := bstep (se 2 (by rfl) ⟨67869231, by rfl⟩ : syracuseStep 180984617 = 135738463) B135738463
theorem B267829487 : Blo 1287962 267829487 := bstep (se 1 (by rfl) ⟨200872115, by rfl⟩ : syracuseStep 267829487 = 401744231) B401744231
theorem B1934057 : Blo 1287962 1934057 := bstep (se 2 (by rfl) ⟨725271, by rfl⟩ : syracuseStep 1934057 = 1450543) B1450543
theorem B16729739 : Blo 1287962 16729739 := bstep (se 1 (by rfl) ⟨12547304, by rfl⟩ : syracuseStep 16729739 = 25094609) B25094609
theorem B16510553 : Blo 1287962 16510553 := bstep (se 2 (by rfl) ⟨6191457, by rfl⟩ : syracuseStep 16510553 = 12382915) B12382915
theorem B20910575 : Blo 1287962 20910575 := bstep (se 1 (by rfl) ⟨15682931, by rfl⟩ : syracuseStep 20910575 = 31365863) B31365863
theorem B120656411 : Blo 1287962 120656411 := bstep (se 1 (by rfl) ⟨90492308, by rfl⟩ : syracuseStep 120656411 = 180984617) B180984617
theorem B178552991 : Blo 1287962 178552991 := bstep (se 1 (by rfl) ⟨133914743, by rfl⟩ : syracuseStep 178552991 = 267829487) B267829487
theorem B80437607 : Blo 1287962 80437607 := bstep (se 1 (by rfl) ⟨60328205, by rfl⟩ : syracuseStep 80437607 = 120656411) B120656411
theorem B1289371 : Blo 1287962 1289371 := bstep (se 1 (by rfl) ⟨967028, by rfl⟩ : syracuseStep 1289371 = 1934057) B1934057
theorem B11153159 : Blo 1287962 11153159 := bstep (se 1 (by rfl) ⟨8364869, by rfl⟩ : syracuseStep 11153159 = 16729739) B16729739
theorem B11007035 : Blo 1287962 11007035 := bstep (se 1 (by rfl) ⟨8255276, by rfl⟩ : syracuseStep 11007035 = 16510553) B16510553
theorem B13940383 : Blo 1287962 13940383 := bstep (se 1 (by rfl) ⟨10455287, by rfl⟩ : syracuseStep 13940383 = 20910575) B20910575
theorem B53625071 : Blo 1287962 53625071 := bstep (se 1 (by rfl) ⟨40218803, by rfl⟩ : syracuseStep 53625071 = 80437607) B80437607
theorem B7435439 : Blo 1287962 7435439 := bstep (se 1 (by rfl) ⟨5576579, by rfl⟩ : syracuseStep 7435439 = 11153159) B11153159
theorem B119035327 : Blo 1287962 119035327 := bstep (se 1 (by rfl) ⟨89276495, by rfl⟩ : syracuseStep 119035327 = 178552991) B178552991
theorem B7338023 : Blo 1287962 7338023 := bstep (se 1 (by rfl) ⟨5503517, by rfl⟩ : syracuseStep 7338023 = 11007035) B11007035
theorem B18587177 : Blo 1287962 18587177 := bstep (se 2 (by rfl) ⟨6970191, by rfl⟩ : syracuseStep 18587177 = 13940383) B13940383
theorem B35750047 : Blo 1287962 35750047 := bstep (se 1 (by rfl) ⟨26812535, by rfl⟩ : syracuseStep 35750047 = 53625071) B53625071
theorem B4956959 : Blo 1287962 4956959 := bstep (se 1 (by rfl) ⟨3717719, by rfl⟩ : syracuseStep 4956959 = 7435439) B7435439
theorem B4892015 : Blo 1287962 4892015 := bstep (se 1 (by rfl) ⟨3669011, by rfl⟩ : syracuseStep 4892015 = 7338023) B7338023
theorem B158713769 : Blo 1287962 158713769 := bstep (se 2 (by rfl) ⟨59517663, by rfl⟩ : syracuseStep 158713769 = 119035327) B119035327
theorem B12391451 : Blo 1287962 12391451 := bstep (se 1 (by rfl) ⟨9293588, by rfl⟩ : syracuseStep 12391451 = 18587177) B18587177
theorem B3261343 : Blo 1287962 3261343 := bstep (se 1 (by rfl) ⟨2446007, by rfl⟩ : syracuseStep 3261343 = 4892015) B4892015
theorem B105809179 : Blo 1287962 105809179 := bstep (se 1 (by rfl) ⟨79356884, by rfl⟩ : syracuseStep 105809179 = 158713769) B158713769
theorem B8260967 : Blo 1287962 8260967 := bstep (se 1 (by rfl) ⟨6195725, by rfl⟩ : syracuseStep 8260967 = 12391451) B12391451
theorem B13218557 : Blo 1287962 13218557 := bstep (se 3 (by rfl) ⟨2478479, by rfl⟩ : syracuseStep 13218557 = 4956959) B4956959
theorem B47666729 : Blo 1287962 47666729 := bstep (se 2 (by rfl) ⟨17875023, by rfl⟩ : syracuseStep 47666729 = 35750047) B35750047
theorem B5507311 : Blo 1287962 5507311 := bstep (se 1 (by rfl) ⟨4130483, by rfl⟩ : syracuseStep 5507311 = 8260967) B8260967
theorem B127111277 : Blo 1287962 127111277 := bstep (se 3 (by rfl) ⟨23833364, by rfl⟩ : syracuseStep 127111277 = 47666729) B47666729
theorem B141078905 : Blo 1287962 141078905 := bstep (se 2 (by rfl) ⟨52904589, by rfl⟩ : syracuseStep 141078905 = 105809179) B105809179
theorem B140997941 : Blo 1287962 140997941 := bstep (se 5 (by rfl) ⟨6609278, by rfl⟩ : syracuseStep 140997941 = 13218557) B13218557
theorem B4348457 : Blo 1287962 4348457 := bstep (se 2 (by rfl) ⟨1630671, by rfl⟩ : syracuseStep 4348457 = 3261343) B3261343
theorem B94052603 : Blo 1287962 94052603 := bstep (se 1 (by rfl) ⟨70539452, by rfl⟩ : syracuseStep 94052603 = 141078905) B141078905
theorem B84740851 : Blo 1287962 84740851 := bstep (se 1 (by rfl) ⟨63555638, by rfl⟩ : syracuseStep 84740851 = 127111277) B127111277
theorem B7343081 : Blo 1287962 7343081 := bstep (se 2 (by rfl) ⟨2753655, by rfl⟩ : syracuseStep 7343081 = 5507311) B5507311
theorem B93998627 : Blo 1287962 93998627 := bstep (se 1 (by rfl) ⟨70498970, by rfl⟩ : syracuseStep 93998627 = 140997941) B140997941
theorem B2898971 : Blo 1287962 2898971 := bstep (se 1 (by rfl) ⟨2174228, by rfl⟩ : syracuseStep 2898971 = 4348457) B4348457
theorem B62701735 : Blo 1287962 62701735 := bstep (se 1 (by rfl) ⟨47026301, by rfl⟩ : syracuseStep 62701735 = 94052603) B94052603
theorem B112987801 : Blo 1287962 112987801 := bstep (se 2 (by rfl) ⟨42370425, by rfl⟩ : syracuseStep 112987801 = 84740851) B84740851
theorem B4895387 : Blo 1287962 4895387 := bstep (se 1 (by rfl) ⟨3671540, by rfl⟩ : syracuseStep 4895387 = 7343081) B7343081
theorem B62665751 : Blo 1287962 62665751 := bstep (se 1 (by rfl) ⟨46999313, by rfl⟩ : syracuseStep 62665751 = 93998627) B93998627
theorem B1932647 : Blo 1287962 1932647 := bstep (se 1 (by rfl) ⟨1449485, by rfl⟩ : syracuseStep 1932647 = 2898971) B2898971
theorem B1288431 : Blo 1287962 1288431 := bstep (se 1 (by rfl) ⟨966323, by rfl⟩ : syracuseStep 1288431 = 1932647) B1932647
theorem B83602313 : Blo 1287962 83602313 := bstep (se 2 (by rfl) ⟨31350867, by rfl⟩ : syracuseStep 83602313 = 62701735) B62701735
theorem B3263591 : Blo 1287962 3263591 := bstep (se 1 (by rfl) ⟨2447693, by rfl⟩ : syracuseStep 3263591 = 4895387) B4895387
theorem B41777167 : Blo 1287962 41777167 := bstep (se 1 (by rfl) ⟨31332875, by rfl⟩ : syracuseStep 41777167 = 62665751) B62665751
theorem B150650401 : Blo 1287962 150650401 := bstep (se 2 (by rfl) ⟨56493900, by rfl⟩ : syracuseStep 150650401 = 112987801) B112987801
theorem B55734875 : Blo 1287962 55734875 := bstep (se 1 (by rfl) ⟨41801156, by rfl⟩ : syracuseStep 55734875 = 83602313) B83602313
theorem B2175727 : Blo 1287962 2175727 := bstep (se 1 (by rfl) ⟨1631795, by rfl⟩ : syracuseStep 2175727 = 3263591) B3263591
theorem B55702889 : Blo 1287962 55702889 := bstep (se 2 (by rfl) ⟨20888583, by rfl⟩ : syracuseStep 55702889 = 41777167) B41777167
theorem B200867201 : Blo 1287962 200867201 := bstep (se 2 (by rfl) ⟨75325200, by rfl⟩ : syracuseStep 200867201 = 150650401) B150650401
theorem B37135259 : Blo 1287962 37135259 := bstep (se 1 (by rfl) ⟨27851444, by rfl⟩ : syracuseStep 37135259 = 55702889) B55702889
theorem B2900969 : Blo 1287962 2900969 := bstep (se 2 (by rfl) ⟨1087863, by rfl⟩ : syracuseStep 2900969 = 2175727) B2175727
theorem B133911467 : Blo 1287962 133911467 := bstep (se 1 (by rfl) ⟨100433600, by rfl⟩ : syracuseStep 133911467 = 200867201) B200867201
theorem B37156583 : Blo 1287962 37156583 := bstep (se 1 (by rfl) ⟨27867437, by rfl⟩ : syracuseStep 37156583 = 55734875) B55734875
theorem B24756839 : Blo 1287962 24756839 := bstep (se 1 (by rfl) ⟨18567629, by rfl⟩ : syracuseStep 24756839 = 37135259) B37135259
theorem B1933979 : Blo 1287962 1933979 := bstep (se 1 (by rfl) ⟨1450484, by rfl⟩ : syracuseStep 1933979 = 2900969) B2900969
theorem B89274311 : Blo 1287962 89274311 := bstep (se 1 (by rfl) ⟨66955733, by rfl⟩ : syracuseStep 89274311 = 133911467) B133911467
theorem B24771055 : Blo 1287962 24771055 := bstep (se 1 (by rfl) ⟨18578291, by rfl⟩ : syracuseStep 24771055 = 37156583) B37156583
theorem B59516207 : Blo 1287962 59516207 := bstep (se 1 (by rfl) ⟨44637155, by rfl⟩ : syracuseStep 59516207 = 89274311) B89274311
theorem B1289319 : Blo 1287962 1289319 := bstep (se 1 (by rfl) ⟨966989, by rfl⟩ : syracuseStep 1289319 = 1933979) B1933979
theorem B16504559 : Blo 1287962 16504559 := bstep (se 1 (by rfl) ⟨12378419, by rfl⟩ : syracuseStep 16504559 = 24756839) B24756839
theorem B33028073 : Blo 1287962 33028073 := bstep (se 2 (by rfl) ⟨12385527, by rfl⟩ : syracuseStep 33028073 = 24771055) B24771055
theorem B11003039 : Blo 1287962 11003039 := bstep (se 1 (by rfl) ⟨8252279, by rfl⟩ : syracuseStep 11003039 = 16504559) B16504559
theorem B39677471 : Blo 1287962 39677471 := bstep (se 1 (by rfl) ⟨29758103, by rfl⟩ : syracuseStep 39677471 = 59516207) B59516207
theorem B22018715 : Blo 1287962 22018715 := bstep (se 1 (by rfl) ⟨16514036, by rfl⟩ : syracuseStep 22018715 = 33028073) B33028073
theorem B7335359 : Blo 1287962 7335359 := bstep (se 1 (by rfl) ⟨5501519, by rfl⟩ : syracuseStep 7335359 = 11003039) B11003039
theorem B14679143 : Blo 1287962 14679143 := bstep (se 1 (by rfl) ⟨11009357, by rfl⟩ : syracuseStep 14679143 = 22018715) B22018715
theorem B26451647 : Blo 1287962 26451647 := bstep (se 1 (by rfl) ⟨19838735, by rfl⟩ : syracuseStep 26451647 = 39677471) B39677471
theorem B9786095 : Blo 1287962 9786095 := bstep (se 1 (by rfl) ⟨7339571, by rfl⟩ : syracuseStep 9786095 = 14679143) B14679143
theorem B17634431 : Blo 1287962 17634431 := bstep (se 1 (by rfl) ⟨13225823, by rfl⟩ : syracuseStep 17634431 = 26451647) B26451647
theorem B4890239 : Blo 1287962 4890239 := bstep (se 1 (by rfl) ⟨3667679, by rfl⟩ : syracuseStep 4890239 = 7335359) B7335359
theorem B11756287 : Blo 1287962 11756287 := bstep (se 1 (by rfl) ⟨8817215, by rfl⟩ : syracuseStep 11756287 = 17634431) B17634431
theorem B6524063 : Blo 1287962 6524063 := bstep (se 1 (by rfl) ⟨4893047, by rfl⟩ : syracuseStep 6524063 = 9786095) B9786095
theorem B3260159 : Blo 1287962 3260159 := bstep (se 1 (by rfl) ⟨2445119, by rfl⟩ : syracuseStep 3260159 = 4890239) B4890239
theorem B2173439 : Blo 1287962 2173439 := bstep (se 1 (by rfl) ⟨1630079, by rfl⟩ : syracuseStep 2173439 = 3260159) B3260159
theorem B15675049 : Blo 1287962 15675049 := bstep (se 2 (by rfl) ⟨5878143, by rfl⟩ : syracuseStep 15675049 = 11756287) B11756287
theorem B4349375 : Blo 1287962 4349375 := bstep (se 1 (by rfl) ⟨3262031, by rfl⟩ : syracuseStep 4349375 = 6524063) B6524063
theorem B20900065 : Blo 1287962 20900065 := bstep (se 2 (by rfl) ⟨7837524, by rfl⟩ : syracuseStep 20900065 = 15675049) B15675049
theorem B1448959 : Blo 1287962 1448959 := bstep (se 1 (by rfl) ⟨1086719, by rfl⟩ : syracuseStep 1448959 = 2173439) B2173439
theorem B2899583 : Blo 1287962 2899583 := bstep (se 1 (by rfl) ⟨2174687, by rfl⟩ : syracuseStep 2899583 = 4349375) B4349375
theorem B27866753 : Blo 1287962 27866753 := bstep (se 2 (by rfl) ⟨10450032, by rfl⟩ : syracuseStep 27866753 = 20900065) B20900065
theorem B1931945 : Blo 1287962 1931945 := bstep (se 2 (by rfl) ⟨724479, by rfl⟩ : syracuseStep 1931945 = 1448959) B1448959
theorem B1933055 : Blo 1287962 1933055 := bstep (se 1 (by rfl) ⟨1449791, by rfl⟩ : syracuseStep 1933055 = 2899583) B2899583
theorem B1287963 : Blo 1287962 1287963 := bstep (se 1 (by rfl) ⟨965972, by rfl⟩ : syracuseStep 1287963 = 1931945) B1931945
theorem B1288703 : Blo 1287962 1288703 := bstep (se 1 (by rfl) ⟨966527, by rfl⟩ : syracuseStep 1288703 = 1933055) B1933055
theorem B18577835 : Blo 1287962 18577835 := bstep (se 1 (by rfl) ⟨13933376, by rfl⟩ : syracuseStep 18577835 = 27866753) B27866753
theorem B12385223 : Blo 1287962 12385223 := bstep (se 1 (by rfl) ⟨9288917, by rfl⟩ : syracuseStep 12385223 = 18577835) B18577835
theorem B8256815 : Blo 1287962 8256815 := bstep (se 1 (by rfl) ⟨6192611, by rfl⟩ : syracuseStep 8256815 = 12385223) B12385223
theorem B5504543 : Blo 1287962 5504543 := bstep (se 1 (by rfl) ⟨4128407, by rfl⟩ : syracuseStep 5504543 = 8256815) B8256815
theorem B3669695 : Blo 1287962 3669695 := bstep (se 1 (by rfl) ⟨2752271, by rfl⟩ : syracuseStep 3669695 = 5504543) B5504543
theorem B2446463 : Blo 1287962 2446463 := bstep (se 1 (by rfl) ⟨1834847, by rfl⟩ : syracuseStep 2446463 = 3669695) B3669695
theorem B6523901 : Blo 1287962 6523901 := bstep (se 3 (by rfl) ⟨1223231, by rfl⟩ : syracuseStep 6523901 = 2446463) B2446463
theorem B4349267 : Blo 1287962 4349267 := bstep (se 1 (by rfl) ⟨3261950, by rfl⟩ : syracuseStep 4349267 = 6523901) B6523901
theorem B2899511 : Blo 1287962 2899511 := bstep (se 1 (by rfl) ⟨2174633, by rfl⟩ : syracuseStep 2899511 = 4349267) B4349267
theorem B1933007 : Blo 1287962 1933007 := bstep (se 1 (by rfl) ⟨1449755, by rfl⟩ : syracuseStep 1933007 = 2899511) B2899511
theorem B1288671 : Blo 1287962 1288671 := bstep (se 1 (by rfl) ⟨966503, by rfl⟩ : syracuseStep 1288671 = 1933007) B1933007

theorem C0 (j : ℕ) (h1 : 321990 ≤ j) (h2 : j ≤ 322489) : Blo 1287962 (4 * j + 3) := by
  interval_cases j
  · exact B1287963
  · exact B1287967
  · exact B1287971
  · exact B1287975
  · exact B1287979
  · exact B1287983
  · exact B1287987
  · exact B1287991
  · exact B1287995
  · exact B1287999
  · exact B1288003
  · exact B1288007
  · exact B1288011
  · exact B1288015
  · exact B1288019
  · exact B1288023
  · exact B1288027
  · exact B1288031
  · exact B1288035
  · exact B1288039
  · exact B1288043
  · exact B1288047
  · exact B1288051
  · exact B1288055
  · exact B1288059
  · exact B1288063
  · exact B1288067
  · exact B1288071
  · exact B1288075
  · exact B1288079
  · exact B1288083
  · exact B1288087
  · exact B1288091
  · exact B1288095
  · exact B1288099
  · exact B1288103
  · exact B1288107
  · exact B1288111
  · exact B1288115
  · exact B1288119
  · exact B1288123
  · exact B1288127
  · exact B1288131
  · exact B1288135
  · exact B1288139
  · exact B1288143
  · exact B1288147
  · exact B1288151
  · exact B1288155
  · exact B1288159
  · exact B1288163
  · exact B1288167
  · exact B1288171
  · exact B1288175
  · exact B1288179
  · exact B1288183
  · exact B1288187
  · exact B1288191
  · exact B1288195
  · exact B1288199
  · exact B1288203
  · exact B1288207
  · exact B1288211
  · exact B1288215
  · exact B1288219
  · exact B1288223
  · exact B1288227
  · exact B1288231
  · exact B1288235
  · exact B1288239
  · exact B1288243
  · exact B1288247
  · exact B1288251
  · exact B1288255
  · exact B1288259
  · exact B1288263
  · exact B1288267
  · exact B1288271
  · exact B1288275
  · exact B1288279
  · exact B1288283
  · exact B1288287
  · exact B1288291
  · exact B1288295
  · exact B1288299
  · exact B1288303
  · exact B1288307
  · exact B1288311
  · exact B1288315
  · exact B1288319
  · exact B1288323
  · exact B1288327
  · exact B1288331
  · exact B1288335
  · exact B1288339
  · exact B1288343
  · exact B1288347
  · exact B1288351
  · exact B1288355
  · exact B1288359
  · exact B1288363
  · exact B1288367
  · exact B1288371
  · exact B1288375
  · exact B1288379
  · exact B1288383
  · exact B1288387
  · exact B1288391
  · exact B1288395
  · exact B1288399
  · exact B1288403
  · exact B1288407
  · exact B1288411
  · exact B1288415
  · exact B1288419
  · exact B1288423
  · exact B1288427
  · exact B1288431
  · exact B1288435
  · exact B1288439
  · exact B1288443
  · exact B1288447
  · exact B1288451
  · exact B1288455
  · exact B1288459
  · exact B1288463
  · exact B1288467
  · exact B1288471
  · exact B1288475
  · exact B1288479
  · exact B1288483
  · exact B1288487
  · exact B1288491
  · exact B1288495
  · exact B1288499
  · exact B1288503
  · exact B1288507
  · exact B1288511
  · exact B1288515
  · exact B1288519
  · exact B1288523
  · exact B1288527
  · exact B1288531
  · exact B1288535
  · exact B1288539
  · exact B1288543
  · exact B1288547
  · exact B1288551
  · exact B1288555
  · exact B1288559
  · exact B1288563
  · exact B1288567
  · exact B1288571
  · exact B1288575
  · exact B1288579
  · exact B1288583
  · exact B1288587
  · exact B1288591
  · exact B1288595
  · exact B1288599
  · exact B1288603
  · exact B1288607
  · exact B1288611
  · exact B1288615
  · exact B1288619
  · exact B1288623
  · exact B1288627
  · exact B1288631
  · exact B1288635
  · exact B1288639
  · exact B1288643
  · exact B1288647
  · exact B1288651
  · exact B1288655
  · exact B1288659
  · exact B1288663
  · exact B1288667
  · exact B1288671
  · exact B1288675
  · exact B1288679
  · exact B1288683
  · exact B1288687
  · exact B1288691
  · exact B1288695
  · exact B1288699
  · exact B1288703
  · exact B1288707
  · exact B1288711
  · exact B1288715
  · exact B1288719
  · exact B1288723
  · exact B1288727
  · exact B1288731
  · exact B1288735
  · exact B1288739
  · exact B1288743
  · exact B1288747
  · exact B1288751
  · exact B1288755
  · exact B1288759
  · exact B1288763
  · exact B1288767
  · exact B1288771
  · exact B1288775
  · exact B1288779
  · exact B1288783
  · exact B1288787
  · exact B1288791
  · exact B1288795
  · exact B1288799
  · exact B1288803
  · exact B1288807
  · exact B1288811
  · exact B1288815
  · exact B1288819
  · exact B1288823
  · exact B1288827
  · exact B1288831
  · exact B1288835
  · exact B1288839
  · exact B1288843
  · exact B1288847
  · exact B1288851
  · exact B1288855
  · exact B1288859
  · exact B1288863
  · exact B1288867
  · exact B1288871
  · exact B1288875
  · exact B1288879
  · exact B1288883
  · exact B1288887
  · exact B1288891
  · exact B1288895
  · exact B1288899
  · exact B1288903
  · exact B1288907
  · exact B1288911
  · exact B1288915
  · exact B1288919
  · exact B1288923
  · exact B1288927
  · exact B1288931
  · exact B1288935
  · exact B1288939
  · exact B1288943
  · exact B1288947
  · exact B1288951
  · exact B1288955
  · exact B1288959
  · exact B1288963
  · exact B1288967
  · exact B1288971
  · exact B1288975
  · exact B1288979
  · exact B1288983
  · exact B1288987
  · exact B1288991
  · exact B1288995
  · exact B1288999
  · exact B1289003
  · exact B1289007
  · exact B1289011
  · exact B1289015
  · exact B1289019
  · exact B1289023
  · exact B1289027
  · exact B1289031
  · exact B1289035
  · exact B1289039
  · exact B1289043
  · exact B1289047
  · exact B1289051
  · exact B1289055
  · exact B1289059
  · exact B1289063
  · exact B1289067
  · exact B1289071
  · exact B1289075
  · exact B1289079
  · exact B1289083
  · exact B1289087
  · exact B1289091
  · exact B1289095
  · exact B1289099
  · exact B1289103
  · exact B1289107
  · exact B1289111
  · exact B1289115
  · exact B1289119
  · exact B1289123
  · exact B1289127
  · exact B1289131
  · exact B1289135
  · exact B1289139
  · exact B1289143
  · exact B1289147
  · exact B1289151
  · exact B1289155
  · exact B1289159
  · exact B1289163
  · exact B1289167
  · exact B1289171
  · exact B1289175
  · exact B1289179
  · exact B1289183
  · exact B1289187
  · exact B1289191
  · exact B1289195
  · exact B1289199
  · exact B1289203
  · exact B1289207
  · exact B1289211
  · exact B1289215
  · exact B1289219
  · exact B1289223
  · exact B1289227
  · exact B1289231
  · exact B1289235
  · exact B1289239
  · exact B1289243
  · exact B1289247
  · exact B1289251
  · exact B1289255
  · exact B1289259
  · exact B1289263
  · exact B1289267
  · exact B1289271
  · exact B1289275
  · exact B1289279
  · exact B1289283
  · exact B1289287
  · exact B1289291
  · exact B1289295
  · exact B1289299
  · exact B1289303
  · exact B1289307
  · exact B1289311
  · exact B1289315
  · exact B1289319
  · exact B1289323
  · exact B1289327
  · exact B1289331
  · exact B1289335
  · exact B1289339
  · exact B1289343
  · exact B1289347
  · exact B1289351
  · exact B1289355
  · exact B1289359
  · exact B1289363
  · exact B1289367
  · exact B1289371
  · exact B1289375
  · exact B1289379
  · exact B1289383
  · exact B1289387
  · exact B1289391
  · exact B1289395
  · exact B1289399
  · exact B1289403
  · exact B1289407
  · exact B1289411
  · exact B1289415
  · exact B1289419
  · exact B1289423
  · exact B1289427
  · exact B1289431
  · exact B1289435
  · exact B1289439
  · exact B1289443
  · exact B1289447
  · exact B1289451
  · exact B1289455
  · exact B1289459
  · exact B1289463
  · exact B1289467
  · exact B1289471
  · exact B1289475
  · exact B1289479
  · exact B1289483
  · exact B1289487
  · exact B1289491
  · exact B1289495
  · exact B1289499
  · exact B1289503
  · exact B1289507
  · exact B1289511
  · exact B1289515
  · exact B1289519
  · exact B1289523
  · exact B1289527
  · exact B1289531
  · exact B1289535
  · exact B1289539
  · exact B1289543
  · exact B1289547
  · exact B1289551
  · exact B1289555
  · exact B1289559
  · exact B1289563
  · exact B1289567
  · exact B1289571
  · exact B1289575
  · exact B1289579
  · exact B1289583
  · exact B1289587
  · exact B1289591
  · exact B1289595
  · exact B1289599
  · exact B1289603
  · exact B1289607
  · exact B1289611
  · exact B1289615
  · exact B1289619
  · exact B1289623
  · exact B1289627
  · exact B1289631
  · exact B1289635
  · exact B1289639
  · exact B1289643
  · exact B1289647
  · exact B1289651
  · exact B1289655
  · exact B1289659
  · exact B1289663
  · exact B1289667
  · exact B1289671
  · exact B1289675
  · exact B1289679
  · exact B1289683
  · exact B1289687
  · exact B1289691
  · exact B1289695
  · exact B1289699
  · exact B1289703
  · exact B1289707
  · exact B1289711
  · exact B1289715
  · exact B1289719
  · exact B1289723
  · exact B1289727
  · exact B1289731
  · exact B1289735
  · exact B1289739
  · exact B1289743
  · exact B1289747
  · exact B1289751
  · exact B1289755
  · exact B1289759
  · exact B1289763
  · exact B1289767
  · exact B1289771
  · exact B1289775
  · exact B1289779
  · exact B1289783
  · exact B1289787
  · exact B1289791
  · exact B1289795
  · exact B1289799
  · exact B1289803
  · exact B1289807
  · exact B1289811
  · exact B1289815
  · exact B1289819
  · exact B1289823
  · exact B1289827
  · exact B1289831
  · exact B1289835
  · exact B1289839
  · exact B1289843
  · exact B1289847
  · exact B1289851
  · exact B1289855
  · exact B1289859
  · exact B1289863
  · exact B1289867
  · exact B1289871
  · exact B1289875
  · exact B1289879
  · exact B1289883
  · exact B1289887
  · exact B1289891
  · exact B1289895
  · exact B1289899
  · exact B1289903
  · exact B1289907
  · exact B1289911
  · exact B1289915
  · exact B1289919
  · exact B1289923
  · exact B1289927
  · exact B1289931
  · exact B1289935
  · exact B1289939
  · exact B1289943
  · exact B1289947
  · exact B1289951
  · exact B1289955
  · exact B1289959

theorem solution (m : ℕ) (hlo : 1287962 ≤ m) (hhi : m ≤ 1289962) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 321990 ≤ j := by omega
    have hj2 : j ≤ 322489 := by omega
    have hb : Blo 1287962 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
